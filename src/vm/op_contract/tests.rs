use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::iter;
use std::num::NonZeroU32;
use std::rc::Rc;

use aluvm::data::{ByteStr, MaybeNumber, Number};
use aluvm::isa::ExecStep;
use aluvm::library::LibSite;
use aluvm::reg::{CoreRegs, Reg, Reg16, Reg32, RegA, RegF, RegR, RegS};
use amplify::confinement::{NonEmptyOrdSet, NonEmptyVec, SmallBlob, SmallOrdMap};
use amplify::num::u24;
use amplify::{Bytes64, Wrapper};
use bp::{Outpoint, Txid};
use commit_verify::StrictHash;
use secp256k1::{generate_keypair, rand, Secp256k1};
use strict_encoding::StrictDumb;

use super::*;
use crate::operation::assignments::AssignVec;
use crate::operation::Operation;
use crate::vm::{
    ContractOp, ContractStateAccess, GlobalContractState, GlobalOrd, GlobalStateIter, OpInfo,
    OrdOpRef, UnknownGlobalStateType, VmContext, WitnessOrd, WitnessPos,
};
use crate::{
    schema, seal, Assign, AssignmentType, Assignments, BundleId, ChainNet, ContractId, Ffv,
    FungibleState, Genesis, GenesisSeal, GlobalState, GlobalStateType, GraphSeal, Identity, Inputs,
    MetaType, MetaValue, Metadata, OpId, Opout, RevealedData, RevealedValue, SchemaId,
    SealClosingStrategy, Signature, Transition, TypedAssigns,
};

const DUMMY_ASSIGN_TYPE_FUNGIBLE: AssignmentType = AssignmentType::with(1000);
const DUMMY_ASSIGN_TYPE_DATA: AssignmentType = AssignmentType::with(1001);
const DUMMY_ASSIGN_TYPE_RIGHTS: AssignmentType = AssignmentType::with(1002);
const DUMMY_ASSIGN_TYPE_UNUSED: AssignmentType = AssignmentType::with(1003);

const DUMMY_GLOBAL_TYPE_A: GlobalStateType = GlobalStateType::with(2000);
const DUMMY_GLOBAL_TYPE_B: GlobalStateType = GlobalStateType::with(2001);
const DUMMY_GLOBAL_TYPE_UNUSED: GlobalStateType = GlobalStateType::with(2002);

const DUMMY_META_TYPE_A: MetaType = MetaType::with(3000);

#[derive(Debug, Default, Clone, PartialEq)]
struct MockContractState {
    global_data: BTreeMap<GlobalStateType, Vec<(GlobalOrd, RevealedData)>>,
    rights_data: BTreeMap<(Outpoint, AssignmentType), u32>,
    fungible_data: BTreeMap<(Outpoint, AssignmentType), Vec<FungibleState>>,
    structured_data: BTreeMap<(Outpoint, AssignmentType), Vec<RevealedData>>,
    fail_global_access: bool,
}

#[derive(Debug)]
struct MockGlobalStateIter {
    data: Vec<(GlobalOrd, RevealedData)>,
    current_idx_for_prev: usize,
    current_idx_for_last: usize,
    original_size: u24,
    has_been_reset: bool,
}

impl GlobalStateIter for MockGlobalStateIter {
    type Data = RevealedData;
    fn size(&mut self) -> u24 { self.original_size }
    fn prev(&mut self) -> Option<(GlobalOrd, Self::Data)> {
        if self.has_been_reset {
            self.current_idx_for_prev = self.data.len();
            self.has_been_reset = false;
        }
        if self.current_idx_for_prev > 0 {
            self.current_idx_for_prev -= 1;
            Some(self.data[self.current_idx_for_prev].clone())
        } else {
            None
        }
    }
    fn last(&mut self) -> Option<(GlobalOrd, Self::Data)> {
        if self.has_been_reset {
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
        self.has_been_reset = true;
        let depth_u32 = depth.to_u32();
        if self.data.is_empty() || depth_u32 >= self.original_size.to_u32() {
            self.current_idx_for_last = 0;
                                           // default.
                                           // The original implementation had `self.data.len()`
                                           // which could lead to out-of-bounds on next `last()`
                                           // call. Let's
                                           // adjust to be safe for `last()`.
        } else {
            self.current_idx_for_last = (self.data.len() - 1).saturating_sub(depth_u32 as usize);
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
            has_been_reset: false,
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

fn dummy_genesis() -> Genesis {
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

fn dummy_transition(contract_id: ContractId, signature: Option<Signature>) -> Transition {
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
    assert_eq!(
        regs.status(),
        expected_st0_ok,
        "ST0 flag mismatch for op {:?}. Expected {}, got {}",
        op,
        expected_st0_ok,
        regs.status()
    );
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

fn assignments_from_typed<Seal: Copy + StrictDumb + seal::ExposedSeal>(
    map: BTreeMap<AssignmentType, TypedAssigns<Seal>>,
) -> Assignments<Seal> {
    let mut confined_map = SmallOrdMap::new();
    for (k, v) in map {
        confined_map.insert(k, v).unwrap();
    }
    Assignments::from_inner(confined_map)
}

fn create_fungible_assign_vec(
    seal: GraphSeal,
    values: Vec<u64>,
) -> AssignVec<Assign<RevealedValue, GraphSeal>> {
    let assigns = values
        .into_iter()
        .map(|v| Assign::Revealed {
            seal,
            state: RevealedValue::from(v),
        })
        .collect::<Vec<_>>();
    if assigns.is_empty() {
        panic!("create_fungible_assignments called with empty values");
    }
    AssignVec::with(NonEmptyVec::try_from(assigns).unwrap())
}

fn create_structured_assign_vec(
    seal: GraphSeal,
    data_items: Vec<Vec<u8>>,
) -> AssignVec<Assign<RevealedData, GraphSeal>> {
    let assigns = data_items
        .into_iter()
        .map(|d| Assign::Revealed {
            seal,
            state: RevealedData::new(SmallBlob::try_from(d).unwrap()),
        })
        .collect::<Vec<_>>();
    if assigns.is_empty() {
        panic!("create_structured_assignments called with empty data");
    }
    AssignVec::with(NonEmptyVec::try_from(assigns).unwrap())
}

struct TestEnv {
    contract_id: ContractId,
    genesis_val: Option<Genesis>,
    transition_val: Option<Transition>,
    prev_assignments_val: Assignments<GraphSeal>,
    owned_assignments_val: Assignments<GraphSeal>,
    globals_val: GlobalState,
    metadata_val: Metadata,
    mock_contract_state_rc: Rc<RefCell<MockContractState>>,
    regs: CoreRegs,
}

impl TestEnv {
    fn for_genesis() -> Self {
        let genesis = dummy_genesis();
        let contract_id = genesis.contract_id();
        Self {
            contract_id,
            genesis_val: Some(genesis),
            transition_val: None,
            prev_assignments_val: Assignments::default(),
            owned_assignments_val: Assignments::default(),
            globals_val: GlobalState::default(),
            metadata_val: Metadata::default(),
            mock_contract_state_rc: Rc::new(RefCell::new(MockContractState::default())),
            regs: CoreRegs::default(),
        }
    }

    fn for_transition() -> Self {
        let contract_id = ContractId::strict_dumb();
        let transition = dummy_transition(contract_id, None);
        Self {
            contract_id,
            genesis_val: None,
            transition_val: Some(transition),
            prev_assignments_val: Assignments::default(),
            owned_assignments_val: Assignments::default(),
            globals_val: GlobalState::default(),
            metadata_val: Metadata::default(),
            mock_contract_state_rc: Rc::new(RefCell::new(MockContractState::default())),
            regs: CoreRegs::default(),
        }
    }

    fn set_contract_id(mut self, contract_id: ContractId) -> Self {
        self.contract_id = contract_id;
        if let Some(t) = self.transition_val.as_mut() {
            t.contract_id = contract_id;
        }
        self
    }

    fn add_global_current_op(mut self, global_type: GlobalStateType, data: Vec<u8>) -> Self {
        let revealed_data = RevealedData::new(SmallBlob::try_from(data).unwrap());
        if let Some(g) = self.genesis_val.as_mut() {
            g.globals.add_state(global_type, revealed_data).unwrap();
        } else if let Some(t) = self.transition_val.as_mut() {
            t.globals.add_state(global_type, revealed_data).unwrap();
        }
        self.globals_val = if self.genesis_val.is_some() {
            self.genesis_val.as_ref().unwrap().globals.clone()
        } else {
            self.transition_val.as_ref().unwrap().globals.clone()
        };
        self
    }

    fn add_metadata_current_op(mut self, meta_type: MetaType, data: Vec<u8>) -> Self {
        let meta_value = MetaValue::from(SmallBlob::try_from(data).unwrap());
        if let Some(g) = self.genesis_val.as_mut() {
            g.metadata.insert(meta_type, meta_value).unwrap();
        } else if let Some(t) = self.transition_val.as_mut() {
            t.metadata.insert(meta_type, meta_value).unwrap();
        }
        self.metadata_val = if self.genesis_val.is_some() {
            self.genesis_val.as_ref().unwrap().metadata.clone()
        } else {
            self.transition_val.as_ref().unwrap().metadata.clone()
        };
        self
    }

    fn add_prev_assign_fungible(mut self, assign_type: AssignmentType, values: Vec<u64>) -> Self {
        let typed_assigns =
            TypedAssigns::Fungible(create_fungible_assign_vec(GraphSeal::strict_dumb(), values));
        self.prev_assignments_val
            .insert(assign_type, typed_assigns)
            .unwrap();
        self
    }

    fn add_prev_assign_structured(
        mut self,
        assign_type: AssignmentType,
        data_items: Vec<Vec<u8>>,
    ) -> Self {
        let typed_assigns = TypedAssigns::Structured(create_structured_assign_vec(
            GraphSeal::strict_dumb(),
            data_items,
        ));
        self.prev_assignments_val
            .insert(assign_type, typed_assigns)
            .unwrap();
        self
    }

    fn add_owned_assign_fungible(mut self, assign_type: AssignmentType, values: Vec<u64>) -> Self {
        let typed_assigns =
            TypedAssigns::Fungible(create_fungible_assign_vec(GraphSeal::strict_dumb(), values));
        if let Some(g) = self.genesis_val.as_mut() {
            panic!(
                "add_owned_assign_fungible for Genesis not fully implemented in TestEnv due to \
                 Seal type mismatch"
            );
        } else if let Some(t) = self.transition_val.as_mut() {
            t.assignments.insert(assign_type, typed_assigns).unwrap();
        }
        self.owned_assignments_val = self.transition_val.as_ref().unwrap().assignments.clone();
        self
    }

    fn add_owned_assign_structured(
        mut self,
        assign_type: AssignmentType,
        data_items: Vec<Vec<u8>>,
    ) -> Self {
        let typed_assigns = TypedAssigns::Structured(create_structured_assign_vec(
            GraphSeal::strict_dumb(),
            data_items,
        ));
        if let Some(g) = self.genesis_val.as_mut() {
            panic!(
                "add_owned_assign_structured for Genesis not fully implemented in TestEnv due to \
                 Seal type mismatch"
            );
        } else if let Some(t) = self.transition_val.as_mut() {
            t.assignments.insert(assign_type, typed_assigns).unwrap();
        }
        self.owned_assignments_val = self.transition_val.as_ref().unwrap().assignments.clone();
        self
    }

    fn set_mock_global_state_history(
        mut self,
        global_type: GlobalStateType,
        history: Vec<(GlobalOrd, RevealedData)>,
    ) -> Self {
        self.mock_contract_state_rc
            .borrow_mut()
            .global_data
            .insert(global_type, history);
        self
    }

    fn set_mock_fail_global_access(mut self, fail: bool) -> Self {
        self.mock_contract_state_rc.borrow_mut().fail_global_access = fail;
        self
    }

    fn execute<'this_env>(
        &'this_env mut self,
        op_code: ContractOp<MockContractState>,
        expected_st0_ok: bool,
    ) where
        MockContractState: 'this_env,
    {
        let op_info: OpInfo;
        let ord_op_ref_val_owned: OrdOpRef;

        if let Some(genesis) = &self.genesis_val {
            ord_op_ref_val_owned = OrdOpRef::Genesis(genesis);
            op_info = OpInfo {
                id: genesis.id(),
                prev_state: &self.prev_assignments_val,
                op: &ord_op_ref_val_owned,
            };
        } else if let Some(transition) = &self.transition_val {
            let txid = Txid::strict_dumb();
            let bundle_id = BundleId::strict_dumb();
            ord_op_ref_val_owned =
                OrdOpRef::Transition(transition, txid, dummy_witness_ord_mined(), bundle_id);
            op_info = OpInfo {
                id: transition.id(),
                prev_state: &self.prev_assignments_val,
                op: &ord_op_ref_val_owned,
            };
        } else {
            panic!("TestEnv not initialized with an operation");
        }

        let context =
            create_vm_context(self.contract_id, op_info, self.mock_contract_state_rc.clone());
        exec_op_and_assert_st0(op_code, &mut self.regs, &context, expected_st0_ok);
    }
}

mod count_ops {
    use aluvm::data::{MaybeNumber, Number};
    use aluvm::reg::{Reg32, RegA};

    use super::*;

    // CnP Tests (Count Previous state)
    #[test]
    fn test_cnp_found_multiple() {
        let mut env = TestEnv::for_transition().add_prev_assign_fungible(
            DUMMY_ASSIGN_TYPE_FUNGIBLE,
            vec![10, 20, 30], // 3 items
        );
        let op_code = ContractOp::CnP(DUMMY_ASSIGN_TYPE_FUNGIBLE, Reg32::Reg0);
        env.execute(op_code, true);
        assert_eq!(env.regs.get_n(RegA::A16, Reg32::Reg0), MaybeNumber::from(Number::from(3u16)));
    }

    #[test]
    fn test_cnp_found_single() {
        let mut env = TestEnv::for_transition()
            .add_prev_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![10]);
        let op_code = ContractOp::CnP(DUMMY_ASSIGN_TYPE_FUNGIBLE, Reg32::Reg0);
        env.execute(op_code, true);
        assert_eq!(env.regs.get_n(RegA::A16, Reg32::Reg0), MaybeNumber::from(Number::from(1u16)));
    }

    #[test]
    fn test_cnp_type_not_found_in_prev_state() {
        let mut env = TestEnv::for_transition();
        let op_code = ContractOp::CnP(DUMMY_ASSIGN_TYPE_UNUSED, Reg32::Reg0);
        env.execute(op_code, true);
        // CnP sets target register to None if the type is not found in prev_state
        assert_eq!(env.regs.get_n(RegA::A16, Reg32::Reg0), MaybeNumber::none());
    }

    // CnS Tests (Count Same [owned] state)
    #[test]
    fn test_cns_found_multiple_transition() {
        let mut env = TestEnv::for_transition().add_owned_assign_structured(
            DUMMY_ASSIGN_TYPE_DATA,
            vec![vec![1], vec![2]], // 2 items
        );
        let op_code = ContractOp::CnS(DUMMY_ASSIGN_TYPE_DATA, Reg32::Reg0);
        env.execute(op_code, true);
        assert_eq!(env.regs.get_n(RegA::A16, Reg32::Reg0), MaybeNumber::from(Number::from(2u16)));
    }

    #[test]
    fn test_cns_found_single_transition() {
        let mut env = TestEnv::for_transition()
            .add_owned_assign_structured(DUMMY_ASSIGN_TYPE_DATA, vec![vec![1]]);
        let op_code = ContractOp::CnS(DUMMY_ASSIGN_TYPE_DATA, Reg32::Reg0);
        env.execute(op_code, true);
        assert_eq!(env.regs.get_n(RegA::A16, Reg32::Reg0), MaybeNumber::from(Number::from(1u16)));
    }

    #[test]
    fn test_cns_type_not_found_in_owned_state_transition() {
        let mut env = TestEnv::for_transition();
        let op_code = ContractOp::CnS(DUMMY_ASSIGN_TYPE_UNUSED, Reg32::Reg0);
        env.execute(op_code, true);
        assert_eq!(env.regs.get_n(RegA::A16, Reg32::Reg0), MaybeNumber::none());
    }

    // CnS for Genesis (needs specific handling for GenesisSeal if we strictly test owned
    // assignments) For simplicity, if `add_owned_assign_...` for genesis is too complex due to
    // seal types, we can test with an empty owned assignment for genesis, which is a valid
    // case.
    #[test]
    fn test_cns_genesis_type_not_found() {
        let mut env = TestEnv::for_genesis();
        let op_code = ContractOp::CnS(DUMMY_ASSIGN_TYPE_UNUSED, Reg32::Reg0);
        env.execute(op_code, true);
        assert_eq!(env.regs.get_n(RegA::A16, Reg32::Reg0), MaybeNumber::none());
    }

    // CnG Tests (Count Next [current op's] Global state)
    #[test]
    fn test_cng_found_multiple() {
        let mut env = TestEnv::for_genesis()
            .add_global_current_op(DUMMY_GLOBAL_TYPE_A, vec![1])
            .add_global_current_op(DUMMY_GLOBAL_TYPE_A, vec![2]);
        let op_code = ContractOp::CnG(DUMMY_GLOBAL_TYPE_A, Reg32::Reg0);
        env.execute(op_code, true);
        assert_eq!(env.regs.get_n(RegA::A8, Reg32::Reg0), MaybeNumber::from(Number::from(2u8)));
    }

    #[test]
    fn test_cng_found_single() {
        let mut env = TestEnv::for_genesis().add_global_current_op(DUMMY_GLOBAL_TYPE_A, vec![1]);
        let op_code = ContractOp::CnG(DUMMY_GLOBAL_TYPE_A, Reg32::Reg0);
        env.execute(op_code, true);
        assert_eq!(env.regs.get_n(RegA::A8, Reg32::Reg0), MaybeNumber::from(Number::from(1u8)));
    }

    #[test]
    fn test_cng_type_not_found_in_globals() {
        let mut env = TestEnv::for_genesis();
        let op_code = ContractOp::CnG(DUMMY_GLOBAL_TYPE_UNUSED, Reg32::Reg0);
        env.execute(op_code, true);
        assert_eq!(env.regs.get_n(RegA::A8, Reg32::Reg0), MaybeNumber::none());
    }

    // CnC Tests (Count Contract's [historical] Global state)
    #[test]
    fn test_cnc_found_multiple() {
        let history = vec![
            (GlobalOrd::genesis(0), RevealedData::new(SmallBlob::try_from(vec![1]).unwrap())),
            (GlobalOrd::genesis(1), RevealedData::new(SmallBlob::try_from(vec![2]).unwrap())),
        ];
        let mut env =
            TestEnv::for_genesis().set_mock_global_state_history(DUMMY_GLOBAL_TYPE_A, history);
        let op_code = ContractOp::CnC(DUMMY_GLOBAL_TYPE_A, Reg32::Reg0);
        env.execute(op_code, true);
        assert_eq!(env.regs.get_n(RegA::A32, Reg32::Reg0), MaybeNumber::from(Number::from(2u32)));
    }

    #[test]
    fn test_cnc_found_single() {
        let history =
            vec![(GlobalOrd::genesis(0), RevealedData::new(SmallBlob::try_from(vec![1]).unwrap()))];
        let mut env =
            TestEnv::for_genesis().set_mock_global_state_history(DUMMY_GLOBAL_TYPE_A, history);
        let op_code = ContractOp::CnC(DUMMY_GLOBAL_TYPE_A, Reg32::Reg0);
        env.execute(op_code, true);
        assert_eq!(env.regs.get_n(RegA::A32, Reg32::Reg0), MaybeNumber::from(Number::from(1u32)));
    }

    #[test]
    fn test_cnc_type_not_found_in_history() {
        let mut env = TestEnv::for_genesis();
        let op_code = ContractOp::CnC(DUMMY_GLOBAL_TYPE_UNUSED, Reg32::Reg0);
        env.execute(op_code, true);
        // If type not found in BTreeMap, unwrap_or_default gives empty vec, size 0.
        assert_eq!(env.regs.get_n(RegA::A32, Reg32::Reg0), MaybeNumber::from(Number::from(0u32)));
    }

    #[test]
    fn test_cnc_fail_on_global_access_error() {
        let mut env = TestEnv::for_genesis().set_mock_fail_global_access(true);
        let op_code = ContractOp::CnC(DUMMY_GLOBAL_TYPE_A, Reg32::Reg0);
        env.execute(op_code, true);
        assert_eq!(env.regs.get_n(RegA::A32, Reg32::Reg0), MaybeNumber::none());
    }
}
