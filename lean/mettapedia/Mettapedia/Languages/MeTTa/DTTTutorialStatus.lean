/-!
# DTT Tutorial Status Map

Compiled status table for the current he-prime DTT tutorial ladder. This is a
small audit artifact: it records which substrate currently carries each case,
without turning runtime golden tests into proof evidence.
-/

namespace Mettapedia.Languages.MeTTa.DTTTutorialStatus

inductive AxisStatus where
  | proved
  | surface
  | represented
  | partialSupport
  | openIssue
deriving DecidableEq, Repr

structure LadderCaseStatus where
  caseName : String
  pureKernel : AxisStatus
  mettail : AxisStatus
  mm2 : AxisStatus
  hePrime : AxisStatus
  nextObligation : String
deriving Repr

inductive SpecRelation where
  | conservative
  | capacityGap
  | openQuestion
  | intentionalDivergence
deriving BEq, DecidableEq, Repr

structure CapacitySpecLedgerCase where
  caseName : String
  relation : SpecRelation
  note : String
deriving Repr

def boolNatStatus : LadderCaseStatus :=
  { caseName := "Bool/Nat foundations"
    pureKernel := .proved
    mettail := .represented
    mm2 := .represented
    hePrime := .surface
    nextObligation := "keep constants aligned across declaration specs and surface annotations" }

def finVecStatus : LadderCaseStatus :=
  { caseName := "Fin-indexed Vec safe indexing"
    pureKernel := .openIssue
    mettail := .represented
    mm2 := .openIssue
    hePrime := .surface
    nextObligation := "add indexed-family declaration/elaboration proof path" }

def equalityCongStatus : LadderCaseStatus :=
  { caseName := "Equality refl/congruence"
    pureKernel := .proved
    mettail := .represented
    mm2 := .openIssue
    hePrime := .surface
    nextObligation := "connect surface equality proofs to PureKernel Id terms" }

def dependentPairStatus : LadderCaseStatus :=
  { caseName := "Dependent pair/proof packaging"
    pureKernel := .proved
    mettail := .represented
    mm2 := .openIssue
    hePrime := .surface
    nextObligation := "expose Sigma packaging through the surface elaborator" }

def capabilityStatus : LadderCaseStatus :=
  { caseName := "Capability-indexed proof objects"
    pureKernel := .proved
    mettail := .represented
    mm2 := .openIssue
    hePrime := .surface
    nextObligation := "connect capability proof objects to runtime authority checks" }

def unitRecOracleStatus : LadderCaseStatus :=
  { caseName := "UnitRec runtime/oracle bridge"
    pureKernel := .proved
    mettail := .represented
    mm2 := .openIssue
    hePrime := .surface
    nextObligation := "generalize the one-example bridge only when NatRec or Vec forces it" }

def natRecStatus : LadderCaseStatus :=
  { caseName := "NatRec / eliminators"
    pureKernel := .partialSupport
    mettail := .represented
    mm2 := .openIssue
    hePrime := .surface
    nextObligation := "derive Nat iota rules from inductive declarations and cross-check runtime reduction" }

def tutorialLadderStatus : List LadderCaseStatus :=
  [ boolNatStatus
  , finVecStatus
  , equalityCongStatus
  , dependentPairStatus
  , capabilityStatus
  , unitRecOracleStatus
  , natRecStatus
  ]

theorem tutorialLadderStatus_count :
    tutorialLadderStatus.length = 7 := rfl

theorem natRec_is_the_partial_case :
    natRecStatus.pureKernel = .partialSupport ∧ natRecStatus.mm2 = .openIssue :=
  ⟨rfl, rfl⟩

theorem unitRec_has_runtime_oracle_bridge :
    unitRecOracleStatus.pureKernel = .proved ∧ unitRecOracleStatus.hePrime = .surface :=
  ⟨rfl, rfl⟩

theorem capability_has_pureKernel_seed :
    capabilityStatus.pureKernel = .proved :=
  rfl

theorem finVec_needs_indexed_family_oracle :
    finVecStatus.pureKernel = .openIssue :=
  rfl

def capacitySpecLedger : List CapacitySpecLedgerCase :=
  [ { caseName := "UnitRec surface/oracle seed"
      relation := .capacityGap
      note := "he-prime emits the UnitRec certificate atom; PureKernel checks the exact shape; general trace bridge is still narrow" }
  , { caseName := "Capability forged read"
      relation := .conservative
      note := "he-prime rejects the attack; PureKernel seed now has a closed certificate rejection" }
  , { caseName := "NatRec eliminator"
      relation := .capacityGap
      note := "NatRec type, generated obligations, and generated zero iota rule exist; succ rule and reduction semantics are still absent" }
  , { caseName := "Grounded Number-indexed VecN"
      relation := .openQuestion
      note := "negative numeric indices are an index-refinement question, not an intentional language fork" }
  ]

def hasIntentionalDivergence (c : CapacitySpecLedgerCase) : Bool :=
  c.relation == .intentionalDivergence

theorem capacitySpecLedger_has_no_intentional_divergence :
    capacitySpecLedger.any hasIntentionalDivergence = false :=
  rfl

end Mettapedia.Languages.MeTTa.DTTTutorialStatus
