use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::iter;
use std::num::NonZeroU32;
use std::rc::Rc;

use aluvm::data::{MaybeNumber, Number};
use aluvm::isa::{ExecStep, InstructionSet};
use aluvm::library::LibSite;
use aluvm::reg::{CoreRegs, Reg, Reg16, Reg32, RegA, RegS};
use amplify::confinement::{NonEmptyOrdSet, NonEmptyVec, SmallBlob};
use amplify::num::u24;
use bp::{Outpoint, Txid};
use commit_verify::StrictHash;
use strict_encoding::StrictDumb;

use super::*;
use crate::operation::assignments::AssignVec;
use crate::operation::Operation;
use crate::vm::{
    ContractOp, ContractStateAccess, GlobalContractState, GlobalOrd, GlobalStateIter, OpInfo,
    OrdOpRef, UnknownGlobalStateType, VmContext, WitnessOrd, WitnessPos,
};
use crate::{
    schema, Assign, AssignmentType, Assignments, BundleId, ChainNet, ContractId, Ffv,
    FungibleState, Genesis, GenesisSeal, GlobalState, GlobalStateType, GraphSeal, Identity, Inputs,
    MetaType, Metadata, OpId, Opout, RevealedData, RevealedValue, SchemaId, SealClosingStrategy,
    Signature, Transition, TypedAssigns,
};

const DUMMY_ASSIGN_TYPE_FUNGIBLE: AssignmentType = AssignmentType::with(1000);
const DUMMY_ASSIGN_TYPE_DATA: AssignmentType = AssignmentType::with(1001);
const DUMMY_ASSIGN_TYPE_RIGHTS: AssignmentType = AssignmentType::with(1002);

const DUMMY_GLOBAL_TYPE_A: GlobalStateType = GlobalStateType::with(2000);
const DUMMY_GLOBAL_TYPE_B: GlobalStateType = GlobalStateType::with(2001);

const DUMMY_META_TYPE_A: MetaType = MetaType::with(3000);

#[derive(Debug, Default, Clone)]
struct MockContractState {
    global_data: BTreeMap<GlobalStateType, Vec<(GlobalOrd, RevealedData)>>,
    fungible_data: BTreeMap<(Outpoint, AssignmentType), Vec<FungibleState>>,
    structured_data: BTreeMap<(Outpoint, AssignmentType), Vec<RevealedData>>,
    rights_data: BTreeMap<(Outpoint, AssignmentType), u32>,
    fail_global_access: bool,
}

#[derive(Debug)]
struct MockGlobalStateIter {
    data: Vec<(GlobalOrd, RevealedData)>,
    current_idx_for_prev: usize, /* For prev(): index of the *next* element to be returned
                                  * by prev() */
    current_idx_for_last: usize, /* For last() after reset: index of the *exact* element to
                                  * be returned */
    original_size: u24,
    initial_depth_reset: bool,
}

impl GlobalStateIter for MockGlobalStateIter {
    type Data = RevealedData;

    fn size(&mut self) -> u24 { self.original_size }

    fn prev(&mut self) -> Option<(GlobalOrd, Self::Data)> {
        if self.initial_depth_reset {
            self.current_idx_for_prev = self.data.len();
            self.initial_depth_reset = false;
        }
        if self.current_idx_for_prev > 0 {
            self.current_idx_for_prev -= 1;
            Some(self.data[self.current_idx_for_prev].clone())
        } else {
            None
        }
    }

    fn last(&mut self) -> Option<(GlobalOrd, Self::Data)> {
        if self.initial_depth_reset {
            if self.current_idx_for_last < self.data.len() {
                Some(self.data[self.current_idx_for_last].clone())
            } else {
                None
            }
        } else if !self.data.is_empty() {
            Some(self.data[self.data.len() - 1].clone())
        } else {
            None
        }
    }

    fn reset(&mut self, depth: u24) {
        self.initial_depth_reset = true;
        let depth_u32 = depth.to_u32();
        if self.data.is_empty() || depth_u32 >= self.original_size.to_u32() {
            self.current_idx_for_last = self.data.len();
        } else {
            self.current_idx_for_last = self.data.len() - 1 - (depth_u32 as usize);
        }
    }
}

impl ContractStateAccess for MockContractState {
    fn global(
        &self,
        ty: GlobalStateType,
    ) -> Result<GlobalContractState<impl GlobalStateIter>, UnknownGlobalStateType> {
        if self.fail_global_access {
            return Err(UnknownGlobalStateType(ty));
        }
        let data_for_type = self.global_data.get(&ty).cloned().unwrap_or_default();
        let size = u24::try_from(data_for_type.len() as u32).unwrap_or(u24::MAX);
        let iter = MockGlobalStateIter {
            data: data_for_type,
            current_idx_for_prev: size.to_usize(),
            current_idx_for_last: 0,
            original_size: size,
            initial_depth_reset: false,
        };
        Ok(GlobalContractState::new(iter))
    }

    fn rights(&self, outpoint: Outpoint, ty: AssignmentType) -> u32 {
        self.rights_data.get(&(outpoint, ty)).cloned().unwrap_or(0)
    }

    fn fungible(
        &self,
        outpoint: Outpoint,
        ty: AssignmentType,
    ) -> impl DoubleEndedIterator<Item = FungibleState> {
        self.fungible_data
            .get(&(outpoint, ty))
            .cloned()
            .unwrap_or_default()
            .into_iter()
    }

    fn data(
        &self,
        outpoint: Outpoint,
        ty: AssignmentType,
    ) -> impl DoubleEndedIterator<Item = impl Borrow<RevealedData>> {
        self.structured_data
            .get(&(outpoint, ty))
            .cloned()
            .unwrap_or_default()
            .into_iter()
    }
}

fn create_dummy_genesis() -> Genesis {
    Genesis {
        ffv: Ffv::default(),
        schema_id: SchemaId::strict_dumb(),
        timestamp: 0,
        issuer: Identity::strict_dumb(),
        chain_net: ChainNet::BitcoinRegtest,
        seal_closing_strategy: SealClosingStrategy::default(),
        metadata: Metadata::default(),
        globals: GlobalState::default(),
        assignments: Assignments::<GenesisSeal>::default(),
    }
}

fn dummy_witness_pos() -> WitnessPos {
    WitnessPos::bitcoin(NonZeroU32::new(1).unwrap(), 1231006505).unwrap()
}

fn dummy_witness_ord_mined() -> WitnessOrd { WitnessOrd::Mined(dummy_witness_pos()) }

fn create_dummy_transition(contract_id: ContractId, signature: Option<Signature>) -> Transition {
    let dummy_opout = Opout::strict_dumb();
    let mut opout_set = BTreeSet::new();
    opout_set.insert(dummy_opout);
    let nonempty_opout_set = NonEmptyOrdSet::try_from(opout_set).expect("Should not be empty");
    let inputs = Inputs::from(nonempty_opout_set);

    Transition {
        ffv: Ffv::default(),
        contract_id,
        nonce: 0,
        transition_type: schema::TransitionType::strict_dumb(),
        metadata: Metadata::default(),
        globals: GlobalState::default(),
        inputs,
        assignments: Assignments::<GraphSeal>::default(),
        signature,
    }
}

fn exec_op_and_assert_st0<S: ContractStateAccess + Clone>(
    op: ContractOp<S>,
    regs: &mut CoreRegs,
    context: &VmContext<S>,
    expected_st0_ok: bool,
) {
    let step = op.exec(regs, LibSite::default(), context);
    assert_eq!(regs.status(), expected_st0_ok, "ST0 flag (is_ok) mismatch for op {:?}", op);
    if !expected_st0_ok {
        assert_eq!(step, ExecStep::Stop, "ExecStep should be Stop on failure for op {:?}", op);
    } else {
        assert_eq!(step, ExecStep::Next, "ExecStep should be Next on success for op {:?}", op);
    }
}

fn create_vm_context<'op, S: ContractStateAccess>(
    contract_id: ContractId,
    op_info: OpInfo<'op>,
    contract_state: Rc<RefCell<S>>,
) -> VmContext<'op, S> {
    VmContext {
        contract_id,
        op_info,
        contract_state,
    }
}

fn create_default_op_info_genesis<'genesis>(
    genesis_op_ref: &'genesis Genesis,
    ord_op_ref: &'genesis OrdOpRef<'genesis>,
    empty_assignments: &'genesis Assignments<GraphSeal>,
) -> OpInfo<'genesis> {
    OpInfo {
        id: genesis_op_ref.id(),
        prev_state: empty_assignments,
        op: ord_op_ref,
    }
}

fn create_default_op_info_transition<'transition>(
    transition_op_ref: &'transition Transition,
    prev_state_ref: &'transition Assignments<GraphSeal>,
    ord_op_ref: &'transition OrdOpRef<'transition>,
) -> OpInfo<'transition> {
    OpInfo {
        id: transition_op_ref.id(),
        prev_state: prev_state_ref,
        op: ord_op_ref,
    }
}

#[test]
fn test_cng_success_single_global() {
    let mut regs = CoreRegs::default();
    let mock_contract_state_rc = Rc::new(RefCell::new(MockContractState::default()));

    let mut genesis_op_val = create_dummy_genesis();
    let contract_id = genesis_op_val.contract_id();

    genesis_op_val
        .globals
        .add_state(DUMMY_GLOBAL_TYPE_A, RevealedData::new(SmallBlob::try_from(vec![1u8]).unwrap()))
        .unwrap();

    let empty_assignments_for_genesis = Assignments::<GraphSeal>::default();
    let ord_op_ref_val = OrdOpRef::Genesis(&genesis_op_val);

    let op_info = create_default_op_info_genesis(
        &genesis_op_val,
        &ord_op_ref_val,
        &empty_assignments_for_genesis,
    );
    let context = create_vm_context(contract_id, op_info, mock_contract_state_rc.clone());

    let op = ContractOp::CnG(DUMMY_GLOBAL_TYPE_A, Reg32::Reg0);
    exec_op_and_assert_st0(op, &mut regs, &context, true);
    assert_eq!(regs.get_n(RegA::A8, Reg32::Reg0), MaybeNumber::from(Number::from(1u8)));
}
