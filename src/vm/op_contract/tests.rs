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

/// A mock implementation of `GlobalStateIter` initialized from a `Vec`.
pub struct MockGlobalStateIter<'a> {
    data: &'a Vec<(GlobalOrd, RevealedData)>,
    current_pos: usize,
    last_item_cache: Option<(GlobalOrd, &'a RevealedData)>,
    total_size: usize,
}

impl<'a> MockGlobalStateIter<'a> {
    pub fn new(initial_data: &'a Vec<(GlobalOrd, RevealedData)>) -> Self {
        MockGlobalStateIter {
            data: initial_data,
            current_pos: 0,
            last_item_cache: None,
            total_size: initial_data.len(),
        }
    }
}

impl<'a> GlobalStateIter for MockGlobalStateIter<'a> {
    type Data = &'a RevealedData;

    fn size(&mut self) -> u24 {
        u24::try_from(self.total_size as u32).expect("MockGlobalStateIter data size must fit u24")
    }

    fn prev(&mut self) -> Option<(GlobalOrd, Self::Data)> {
        if self.current_pos < self.total_size {
            let (ord_ref, data_ref) = &self.data[self.current_pos];
            let item_to_return = (*ord_ref, data_ref);

            self.last_item_cache = Some(item_to_return);
            self.current_pos += 1;
            Some(item_to_return)
        } else {
            self.last_item_cache = None;
            None
        }
    }

    fn last(&mut self) -> Option<(GlobalOrd, Self::Data)> { self.last_item_cache }

    fn reset(&mut self, depth_1based: u24) {
        if depth_1based == u24::ZERO {
            panic!("MockGlobalStateIter cannot be reset to depth 0");
        }

        let target_idx_for_last_0based = depth_1based.to_usize() - 1; // Convert 1-based to 0-indexed

        if target_idx_for_last_0based < self.total_size {
            // The item at target_idx_for_last_0based should become the "last" item.
            let (ord_ref, data_ref) = &self.data[target_idx_for_last_0based];
            self.last_item_cache = Some((*ord_ref, data_ref));
            // The next call to prev() should yield the item *after* this one.
            self.current_pos = target_idx_for_last_0based + 1;
        } else {
            // Requested 1-based depth is out of bounds.
            // e.g., total_size=1. reset(depth_1based=2). target_idx_for_last_0based=1.
            // 1 < 1 is false. Comes here.
            self.last_item_cache = None;
            self.current_pos = self.total_size; // Exhausted
        }
    }
}

static EMPTY_GLOBAL_VEC: Vec<(GlobalOrd, RevealedData)> = Vec::new();

impl ContractStateAccess for MockContractState {
    fn global(
        &self,
        ty: GlobalStateType,
    ) -> Result<GlobalContractState<impl GlobalStateIter>, UnknownGlobalStateType> {
        if self.fail_global_access {
            return Err(UnknownGlobalStateType(ty));
        }

        let data_ref: &Vec<(GlobalOrd, RevealedData)> = self
            .global_data
            .get(&ty)
            .map_or(&EMPTY_GLOBAL_VEC, |vec| vec);

        let iter = MockGlobalStateIter::new(data_ref);

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
        self,
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

mod load_ops {
    use aluvm::data::Number;
    use amplify::confinement::SmallBlob;
    use bp::seals::SecretSeal;

    use super::*;

    // LdP (Load Previous structured state) Tests
    #[test]
    fn test_ldp_success_revealed() {
        let data_vec = vec![0xAB, 0xCD, 0xEF];
        let mut env = TestEnv::for_transition()
            .add_prev_assign_structured(DUMMY_ASSIGN_TYPE_DATA, vec![data_vec.clone()]);
        env.regs.set_n(RegA::A16, Reg32::Reg0, Number::from(0u16)); // index = 0

        let op_code = ContractOp::LdP(DUMMY_ASSIGN_TYPE_DATA, Reg16::Reg0, RegS::from(0));
        env.execute(op_code, true);

        assert_eq!(env.regs.s16(RegS::from(0)).unwrap().as_ref(), data_vec.as_slice());
    }

    #[test]
    fn test_ldp_success_concealed_seal_loads_state() {
        let data_vec = vec![0xAA, 0xBB];
        let revealed_data = RevealedData::new(SmallBlob::try_from(data_vec.clone()).unwrap());
        let concealed_assign = Assign::ConfidentialSeal {
            seal: SecretSeal::strict_dumb(),
            state: revealed_data,
        };

        let mut prev_map = BTreeMap::new();
        prev_map.insert(
            DUMMY_ASSIGN_TYPE_DATA,
            TypedAssigns::Structured(AssignVec::with(NonEmptyVec::with(concealed_assign))),
        );
        let mut env = TestEnv::for_transition();
        env.prev_assignments_val = assignments_from_typed(prev_map);
        env.regs.set_n(RegA::A16, Reg32::Reg0, Number::from(0u16));

        let op_code = ContractOp::LdP(DUMMY_ASSIGN_TYPE_DATA, Reg16::Reg0, RegS::from(0));
        env.execute(op_code, true);
        assert_eq!(env.regs.s16(RegS::from(0)).unwrap().as_ref(), data_vec.as_slice());
    }

    #[test]
    fn test_ldp_fail_index_reg_none() {
        let mut env = TestEnv::for_transition(); // a16[0] (index_reg) is None
        let op_code = ContractOp::LdP(DUMMY_ASSIGN_TYPE_DATA, Reg16::Reg0, RegS::from(0));
        env.execute(op_code, false);
        assert!(env.regs.s16(RegS::from(0)).is_none());
    }

    #[test]
    fn test_ldp_fail_state_type_missing_in_prev() {
        let mut env = TestEnv::for_transition(); // prev_assignments is empty
        env.regs.set_n(RegA::A16, Reg32::Reg0, Number::from(0u16));
        let op_code = ContractOp::LdP(DUMMY_ASSIGN_TYPE_DATA, Reg16::Reg0, RegS::from(0));
        env.execute(op_code, false);
        assert!(env.regs.s16(RegS::from(0)).is_none());
    }

    #[test]
    fn test_ldp_fail_index_oob() {
        // 1 item at index 0
        let mut env = TestEnv::for_transition()
            .add_prev_assign_structured(DUMMY_ASSIGN_TYPE_DATA, vec![vec![1]]);
        // Request index 1
        env.regs.set_n(RegA::A16, Reg32::Reg0, Number::from(1u16));

        let op_code = ContractOp::LdP(DUMMY_ASSIGN_TYPE_DATA, Reg16::Reg0, RegS::from(0));
        env.execute(op_code, false);
        assert!(env.regs.s16(RegS::from(0)).is_none());
    }

    #[test]
    fn test_ldp_fail_wrong_state_type_in_prev() {
        // prev_state has DUMMY_ASSIGN_TYPE_DATA, but it's Fungible, not Structured for LdP
        let mut env =
            TestEnv::for_transition().add_prev_assign_fungible(DUMMY_ASSIGN_TYPE_DATA, vec![100]);
        env.regs.set_n(RegA::A16, Reg32::Reg0, Number::from(0u16));

        let op_code = ContractOp::LdP(DUMMY_ASSIGN_TYPE_DATA, Reg16::Reg0, RegS::from(0));
        env.execute(op_code, false);
        assert!(env.regs.s16(RegS::from(0)).is_none());
    }

    // LdS (Load Same/owned structured state) Tests
    #[test]
    fn test_lds_success_revealed() {
        let data_vec = vec![0xBE, 0xEF];
        let mut env = TestEnv::for_transition()
            .add_owned_assign_structured(DUMMY_ASSIGN_TYPE_DATA, vec![data_vec.clone()]);
        env.regs.set_n(RegA::A16, Reg32::Reg0, Number::from(0u16));

        let op_code = ContractOp::LdS(DUMMY_ASSIGN_TYPE_DATA, Reg16::Reg0, RegS::from(1));
        env.execute(op_code, true);
        assert_eq!(env.regs.s16(RegS::from(1)).unwrap().as_ref(), data_vec.as_slice());
    }

    #[test]
    fn test_lds_fail_index_reg_none() {
        let mut env = TestEnv::for_transition(); // a16[0] is None
        let op_code = ContractOp::LdS(DUMMY_ASSIGN_TYPE_DATA, Reg16::Reg0, RegS::from(1));
        env.execute(op_code, false);
        assert!(env.regs.s16(RegS::from(1)).is_none());
    }

    #[test]
    fn test_lds_fail_state_type_missing_in_owned() {
        let mut env = TestEnv::for_transition();
        env.regs.set_n(RegA::A16, Reg32::Reg0, Number::from(0u16));
        let op_code = ContractOp::LdS(DUMMY_ASSIGN_TYPE_DATA, Reg16::Reg0, RegS::from(1));
        env.execute(op_code, false);
        assert!(env.regs.s16(RegS::from(1)).is_none());
    }

    #[test]
    fn test_lds_fail_index_oob() {
        let mut env = TestEnv::for_transition()
            .add_owned_assign_structured(DUMMY_ASSIGN_TYPE_DATA, vec![vec![1]]);
        env.regs.set_n(RegA::A16, Reg32::Reg0, Number::from(1u16)); // Request index 1
        let op_code = ContractOp::LdS(DUMMY_ASSIGN_TYPE_DATA, Reg16::Reg0, RegS::from(1));
        env.execute(op_code, false);
        assert!(env.regs.s16(RegS::from(1)).is_none());
    }

    #[test]
    fn test_lds_fail_wrong_state_type_in_owned() {
        // Data is fungible
        let mut env =
            TestEnv::for_transition().add_owned_assign_fungible(DUMMY_ASSIGN_TYPE_DATA, vec![100]);
        env.regs.set_n(RegA::A16, Reg32::Reg0, Number::from(0u16));
        let op_code = ContractOp::LdS(DUMMY_ASSIGN_TYPE_DATA, Reg16::Reg0, RegS::from(1));
        env.execute(op_code, false);
        assert!(env.regs.s16(RegS::from(1)).is_none());
    }

    // LdF (Load Same/owned Fungible state) Tests
    #[test]
    fn test_ldf_success_revealed() {
        let fungible_val = 777u64;
        let mut env = TestEnv::for_transition()
            .add_owned_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![fungible_val]);
        // index_reg for source; destination is a64[Reg16::Reg0]
        env.regs.set_n(RegA::A16, Reg32::Reg0, Number::from(0u16));

        let op_code = ContractOp::LdF(DUMMY_ASSIGN_TYPE_FUNGIBLE, Reg16::Reg0, Reg16::Reg0);
        env.execute(op_code, true);
        assert_eq!(
            env.regs.get_n(RegA::A64, Reg32::Reg0),
            MaybeNumber::from(Number::from(fungible_val))
        );
    }

    #[test]
    fn test_ldf_fail_index_reg_none() {
        let mut env = TestEnv::for_transition();
        let op_code = ContractOp::LdF(DUMMY_ASSIGN_TYPE_FUNGIBLE, Reg16::Reg0, Reg16::Reg0);
        env.execute(op_code, false);
        assert!(env.regs.get_n(RegA::A64, Reg32::Reg0).is_none());
    }

    #[test]
    fn test_ldf_fail_state_type_missing_in_owned() {
        let mut env = TestEnv::for_transition();
        env.regs.set_n(RegA::A16, Reg32::Reg0, Number::from(0u16));
        let op_code = ContractOp::LdF(DUMMY_ASSIGN_TYPE_FUNGIBLE, Reg16::Reg0, Reg16::Reg0);
        env.execute(op_code, false);
        assert!(env.regs.get_n(RegA::A64, Reg32::Reg0).is_none());
    }

    #[test]
    fn test_ldf_fail_index_oob() {
        let mut env = TestEnv::for_transition()
            .add_owned_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![100]);
        // Request index 1
        env.regs.set_n(RegA::A16, Reg32::Reg0, Number::from(1u16));
        let op_code = ContractOp::LdF(DUMMY_ASSIGN_TYPE_FUNGIBLE, Reg16::Reg0, Reg16::Reg0);
        env.execute(op_code, false);
        assert!(env.regs.get_n(RegA::A64, Reg32::Reg0).is_none());
    }

    #[test]
    fn test_ldf_fail_wrong_state_type_in_owned() {
        // Data is structured
        let mut env = TestEnv::for_transition()
            .add_owned_assign_structured(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![vec![1]]);
        env.regs.set_n(RegA::A16, Reg32::Reg0, Number::from(0u16));
        let op_code = ContractOp::LdF(DUMMY_ASSIGN_TYPE_FUNGIBLE, Reg16::Reg0, Reg16::Reg0);
        env.execute(op_code, false);
        assert!(env.regs.get_n(RegA::A64, Reg32::Reg0).is_none());
    }

    // LdG (Load Global state from current op) Tests
    #[test]
    fn test_ldg_success() {
        let data_vec = vec![0xC0, 0xDE];
        let mut env =
            TestEnv::for_genesis().add_global_current_op(DUMMY_GLOBAL_TYPE_A, data_vec.clone());
        // index_reg for source (a8)
        env.regs.set_n(RegA::A8, Reg32::Reg0, Number::from(0u8));

        let op_code = ContractOp::LdG(DUMMY_GLOBAL_TYPE_A, Reg16::Reg0, RegS::from(2));
        env.execute(op_code, true);
        assert_eq!(env.regs.s16(RegS::from(2)).unwrap().as_ref(), data_vec.as_slice());
    }

    #[test]
    fn test_ldg_success_multiple_items_correct_index() {
        let data_vec1 = vec![0xC0];
        let data_vec2 = vec![0xDE];
        let mut env = TestEnv::for_genesis()
            .add_global_current_op(DUMMY_GLOBAL_TYPE_A, data_vec1.clone())
            .add_global_current_op(DUMMY_GLOBAL_TYPE_A, data_vec2.clone());
        // index = 1 (for the second item)
        env.regs.set_n(RegA::A8, Reg32::Reg0, Number::from(1u8));

        let op_code = ContractOp::LdG(DUMMY_GLOBAL_TYPE_A, Reg16::Reg0, RegS::from(2));
        env.execute(op_code, true);
        assert_eq!(env.regs.s16(RegS::from(2)).unwrap().as_ref(), data_vec2.as_slice());
    }

    #[test]
    fn test_ldg_fail_index_reg_none() {
        let mut env = TestEnv::for_genesis().add_global_current_op(DUMMY_GLOBAL_TYPE_A, vec![1, 2]);
        // Index register a8[0] is deliberately not set (i.e., None)
        let op_code = ContractOp::LdG(DUMMY_GLOBAL_TYPE_A, Reg16::Reg0, RegS::from(2));
        env.execute(op_code, false);
        assert!(env.regs.s16(RegS::from(2)).is_none());
    }

    #[test]
    fn test_ldg_fail_state_type_missing_in_globals() {
        // Globals are empty for DUMMY_GLOBAL_TYPE_A
        let mut env = TestEnv::for_genesis();
        env.regs.set_n(RegA::A8, Reg32::Reg0, Number::from(0u8));
        let op_code = ContractOp::LdG(DUMMY_GLOBAL_TYPE_A, Reg16::Reg0, RegS::from(2));
        env.execute(op_code, false);
        assert!(env.regs.s16(RegS::from(2)).is_none());
    }

    #[test]
    fn test_ldg_fail_index_oob() {
        // 1 item
        let mut env = TestEnv::for_genesis().add_global_current_op(DUMMY_GLOBAL_TYPE_A, vec![1, 2]);
        // Request index 1 (OOB for 1 item)
        env.regs.set_n(RegA::A8, Reg32::Reg0, Number::from(1u8));

        let op_code = ContractOp::LdG(DUMMY_GLOBAL_TYPE_A, Reg16::Reg0, RegS::from(2));
        env.execute(op_code, false);
        assert!(env.regs.s16(RegS::from(2)).is_none());
    }

    // LdC (Load Global state from Contract history) Tests
    #[test]
    fn test_ldc_success() {
        let data_vec_hist = vec![0x12, 0x34];
        let history = vec![(
            GlobalOrd::genesis(0), // Dummy GlobalOrd
            RevealedData::new(SmallBlob::try_from(data_vec_hist.clone()).unwrap()),
        )];
        // LdC uses contract_state, not current op's state
        let mut env =
            TestEnv::for_genesis().set_mock_global_state_history(DUMMY_GLOBAL_TYPE_A, history);
        // let the depth eq 0
        env.regs.set_n(RegA::A32, Reg32::Reg0, Number::from(1u32));

        let op_code = ContractOp::LdC(DUMMY_GLOBAL_TYPE_A, Reg16::Reg0, RegS::from(3));
        env.execute(op_code, true);
        assert_eq!(env.regs.s16(RegS::from(3)).unwrap().as_ref(), data_vec_hist.as_slice());
    }

    #[test]
    fn test_ldc_success_at_depth_one() {
        let data_vec_hist1 = vec![0x01, 0x02];
        let data_vec_hist2 = vec![0x03, 0x04];
        let history = vec![
            (
                GlobalOrd::genesis(1), // d = 1
                RevealedData::new(SmallBlob::try_from(data_vec_hist1.clone()).unwrap()),
            ),
            (
                GlobalOrd::genesis(2), // d = 2
                RevealedData::new(SmallBlob::try_from(data_vec_hist2.clone()).unwrap()),
            ),
        ];
        let mut env =
            TestEnv::for_genesis().set_mock_global_state_history(DUMMY_GLOBAL_TYPE_A, history);
        env.regs.set_n(RegA::A32, Reg32::Reg0, Number::from(1u32)); // depth = 1

        let op_code = ContractOp::LdC(DUMMY_GLOBAL_TYPE_A, Reg16::Reg0, RegS::from(3));
        env.execute(op_code, true);
        assert_eq!(env.regs.s16(RegS::from(3)).unwrap().as_ref(), data_vec_hist1.as_slice());

        env.regs.set_n(RegA::A32, Reg32::Reg0, Number::from(2u32)); // depth = 2
        let op_code = ContractOp::LdC(DUMMY_GLOBAL_TYPE_A, Reg16::Reg0, RegS::from(4));
        env.execute(op_code, true);
        assert_eq!(env.regs.s16(RegS::from(4)).unwrap().as_ref(), data_vec_hist2.as_slice());
    }

    #[test]
    fn test_ldc_fail_mock_global_access_error() {
        let mut env = TestEnv::for_genesis().set_mock_fail_global_access(true);
        env.regs.set_n(RegA::A32, Reg32::Reg0, Number::from(0u32));
        let op_code = ContractOp::LdC(DUMMY_GLOBAL_TYPE_A, Reg16::Reg0, RegS::from(3));
        // fail!() is called if contract_state.global() errors
        env.execute(op_code, false);
        assert!(env.regs.s16(RegS::from(3)).is_none());
    }

    #[test]
    fn test_ldc_fail_depth_reg_none() {
        let mut env = TestEnv::for_genesis(); // a32[0] (depth_reg) is None
        let op_code = ContractOp::LdC(DUMMY_GLOBAL_TYPE_A, Reg16::Reg0, RegS::from(3));
        env.execute(op_code, false);
        assert!(env.regs.s16(RegS::from(3)).is_none());
    }

    #[test]
    fn test_ldc_fail_depth_oob_in_history() {
        let history =
            vec![(GlobalOrd::genesis(0), RevealedData::new(SmallBlob::try_from(vec![1]).unwrap()))]; // Only 1 item
        let mut env =
            TestEnv::for_genesis().set_mock_global_state_history(DUMMY_GLOBAL_TYPE_A, history);
        env.regs.set_n(RegA::A32, Reg32::Reg0, Number::from(2u32)); // Request depth 2 (OOB)

        let op_code = ContractOp::LdC(DUMMY_GLOBAL_TYPE_A, Reg16::Reg0, RegS::from(3));
        env.execute(op_code, false);
        assert!(env.regs.s16(RegS::from(3)).is_none());
    }

    #[test]
    fn test_ldc_fail_depth_too_large_for_u24() {
        let mut env = TestEnv::for_genesis();
        // Set depth register to a value greater than u24::MAX to test saturation/error handling
        env.regs
            .set_n(RegA::A32, Reg32::Reg0, Number::from(u24::MAX.to_u32() + 1));

        let op_code = ContractOp::LdC(DUMMY_GLOBAL_TYPE_A, Reg16::Reg0, RegS::from(3));
        env.execute(op_code, false);
        assert!(env.regs.s16(RegS::from(3)).is_none());
    }

    // LdM (Load Metadata from current op) Tests
    #[test]
    fn test_ldm_success() {
        let meta_bytes = vec![0xDA, 0x7A];
        let mut env =
            TestEnv::for_genesis().add_metadata_current_op(DUMMY_META_TYPE_A, meta_bytes.clone());

        let op_code = ContractOp::LdM(DUMMY_META_TYPE_A, RegS::from(4));
        env.execute(op_code, true);
        assert_eq!(env.regs.s16(RegS::from(4)).unwrap().as_ref(), meta_bytes.as_slice());
    }

    #[test]
    fn test_ldm_fail_meta_type_missing() {
        let mut env = TestEnv::for_genesis(); // metadata is empty by default
        let op_code = ContractOp::LdM(DUMMY_META_TYPE_A, RegS::from(4));
        env.execute(op_code, false);
        assert!(env.regs.s16(RegS::from(4)).is_none());
    }
}


mod sum_verification_ops {
    use aluvm::data::{MaybeNumber, Number};
    use aluvm::reg::{Reg32, RegA};

    use super::*;

    // Svs (Sum Verify Same state) Tests
    #[test]
    fn test_svs_success_equal_sum() {
        let mut env = TestEnv::for_transition()
            .add_prev_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![10, 20]) // Prev sum = 30
            .add_owned_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![5, 25]); // Owned sum = 30
        let op_code = ContractOp::Svs(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, true);
    }

    #[test]
    fn test_svs_success_zero_sum_both_empty() {
        let mut env = TestEnv::for_transition(); // No prev, no owned of this type
        let op_code = ContractOp::Svs(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, true); // 0 == 0
    }

    #[test]
    fn test_svs_success_zero_sum_with_zero_values() {
        let mut env = TestEnv::for_transition()
            .add_prev_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![0, 0])
            .add_owned_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![0]);
        let op_code = ContractOp::Svs(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, true); // 0 == 0
    }

    #[test]
    fn test_svs_fail_unequal_sum() {
        let mut env = TestEnv::for_transition()
            .add_prev_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![10, 20]) // Prev sum = 30
            .add_owned_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![5, 20]); // Owned sum = 25
        let op_code = ContractOp::Svs(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, false);
    }

    #[test]
    fn test_svs_fail_only_inputs_present() {
        let mut env = TestEnv::for_transition()
            .add_prev_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![10, 20]); // No owned of this type
        let op_code = ContractOp::Svs(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, false); // 30 != 0
    }

    #[test]
    fn test_svs_fail_only_outputs_present() {
        let mut env = TestEnv::for_transition()
            .add_owned_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![5, 25]); // No prev of this type
        let op_code = ContractOp::Svs(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, false); // 0 != 30
    }

    #[test]
    fn test_svs_fail_input_not_fungible() {
        let mut env = TestEnv::for_transition()
            .add_prev_assign_structured(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![vec![1]]) // Wrong type for prev
            .add_owned_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![10]);
        let op_code = ContractOp::Svs(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, false);
    }

    #[test]
    fn test_svs_fail_output_not_fungible() {
        let mut env = TestEnv::for_transition()
            .add_prev_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![10])
            .add_owned_assign_structured(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![vec![1]]); // Wrong type for owned
        let op_code = ContractOp::Svs(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, false);
    }

    #[test]
    fn test_svs_fail_input_sum_overflow() {
        let mut env = TestEnv::for_transition()
            .add_prev_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![u64::MAX, 1]) // Overflow
            .add_owned_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![10]);
        let op_code = ContractOp::Svs(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, false);
    }

    #[test]
    fn test_svs_fail_output_sum_overflow() {
        let mut env = TestEnv::for_transition()
            .add_prev_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![10])
            .add_owned_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![u64::MAX, 1]); // Overflow
        let op_code = ContractOp::Svs(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, false);
    }

    // SaS (Sum verify Assigned state) Tests
    #[test]
    fn test_sas_success() {
        let mut env = TestEnv::for_transition()
            .add_owned_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![10, 20]); // Owned sum = 30
        env.regs.set_n(RegA::A64, Reg32::Reg0, Number::from(30u64)); // Expected sum

        let op_code = ContractOp::Sas(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, true);
    }

    #[test]
    fn test_sas_fail_sum_reg_none() {
        let mut env = TestEnv::for_transition()
            .add_owned_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![10, 20]);
        // a64[0] is None
        let op_code = ContractOp::Sas(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, false);
    }

    #[test]
    fn test_sas_fail_sum_mismatch() {
        let mut env = TestEnv::for_transition()
            .add_owned_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![10, 20]); // Owned sum = 30
        env.regs.set_n(RegA::A64, Reg32::Reg0, Number::from(31u64)); // Expected sum mismatch

        let op_code = ContractOp::Sas(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, false);
    }

    #[test]
    fn test_sas_fail_owned_state_type_missing() {
        let mut env = TestEnv::for_transition(); // No owned state of this type
        env.regs.set_n(RegA::A64, Reg32::Reg0, Number::from(1u64)); // Expect non-zero sum
        let op_code = ContractOp::Sas(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        // owned sum is 0, a64[0] is 1 -> fail
        env.execute(op_code, false);
    }

    #[test]
    fn test_sas_success_owned_state_type_missing_and_sum_reg_zero() {
        let mut env = TestEnv::for_transition();
        env.regs.set_n(RegA::A64, Reg32::Reg0, Number::from(0u64)); // Expect zero sum

        let op_code = ContractOp::Sas(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        // owned sum is 0, a64[0] is 0 -> success
        env.execute(op_code, true);
    }

    #[test]
    fn test_sas_fail_owned_state_not_fungible() {
        let mut env = TestEnv::for_transition()
            .add_owned_assign_structured(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![vec![1]]); // Wrong type
        env.regs.set_n(RegA::A64, Reg32::Reg0, Number::from(0u64));

        let op_code = ContractOp::Sas(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, false);
    }

    #[test]
    fn test_sas_fail_owned_state_contains_zero_value() {
        // SaS specifically fails if any of the outputted fungible values are zero
        let mut env = TestEnv::for_transition()
            .add_owned_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![10, 0, 20]); // Contains 0
        env.regs.set_n(RegA::A64, Reg32::Reg0, Number::from(30u64));

        let op_code = ContractOp::Sas(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, false);
    }

    #[test]
    fn test_sas_fail_owned_sum_overflow() {
        let mut env = TestEnv::for_transition()
            .add_owned_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![u64::MAX, 1]); // Overflow
        env.regs.set_n(RegA::A64, Reg32::Reg0, Number::from(10u64)); // Doesn't matter due to overflow

        let op_code = ContractOp::Sas(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, false);
    }

    // SpS (Sum verify Previous state) Tests
    #[test]
    fn test_sps_success() {
        let mut env = TestEnv::for_transition()
            .add_prev_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![15, 25]); // Prev sum = 40
        env.regs.set_n(RegA::A64, Reg32::Reg0, Number::from(40u64)); // Expected sum

        let op_code = ContractOp::Sps(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, true);
    }

    #[test]
    fn test_sps_fail_sum_reg_none() {
        let mut env = TestEnv::for_transition()
            .add_prev_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![15, 25]);
        // a64[0] is None
        let op_code = ContractOp::Sps(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, false);
    }

    #[test]
    fn test_sps_fail_sum_mismatch() {
        let mut env = TestEnv::for_transition()
            .add_prev_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![15, 25]); // Prev sum = 40
        env.regs.set_n(RegA::A64, Reg32::Reg0, Number::from(41u64)); // Expected different

        let op_code = ContractOp::Sps(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, false);
    }

    #[test]
    fn test_sps_fail_prev_state_type_missing() {
        let mut env = TestEnv::for_transition(); // No prev state of this type
        env.regs.set_n(RegA::A64, Reg32::Reg0, Number::from(1u64)); // Expect non-zero sum

        let op_code = ContractOp::Sps(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        // prev sum is 0, a64[0] is 1 -> fail
        env.execute(op_code, false);
    }

    #[test]
    fn test_sps_success_prev_state_type_missing_and_sum_reg_zero() {
        let mut env = TestEnv::for_transition();
        env.regs.set_n(RegA::A64, Reg32::Reg0, Number::from(0u64)); // Expect zero sum

        let op_code = ContractOp::Sps(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        // prev sum is 0, a64[0] is 0 -> success
        env.execute(op_code, true);
    }

    #[test]
    fn test_sps_fail_prev_state_not_fungible() {
        let mut env = TestEnv::for_transition()
            .add_prev_assign_structured(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![vec![1]]); // Wrong type
        env.regs.set_n(RegA::A64, Reg32::Reg0, Number::from(0u64));

        let op_code = ContractOp::Sps(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, false);
    }

    #[test]
    fn test_sps_fail_prev_sum_overflow() {
        let mut env = TestEnv::for_transition()
            .add_prev_assign_fungible(DUMMY_ASSIGN_TYPE_FUNGIBLE, vec![u64::MAX, 1]); // Overflow
        env.regs.set_n(RegA::A64, Reg32::Reg0, Number::from(10u64));

        let op_code = ContractOp::Sps(DUMMY_ASSIGN_TYPE_FUNGIBLE);
        env.execute(op_code, false);
    }
}
