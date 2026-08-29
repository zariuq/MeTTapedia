import Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
import Mettapedia.GSLT.LanguageDef.TptpOfficialPrincipalSymbols
import Mettapedia.GSLT.LanguageDef.TptpOfficialRoleSemantics
import Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo

/-!
# Status-indexed semantic services for official TSTP derivations

TSTP inference metadata has two independent jobs.  The status names the
semantic relation between the parent formulae and the inferred formula, while
assumption and introduced-symbol records update derivation-wide structural
state.  This module keeps those jobs separate and then checks both in one
single-pass transition.

The calculus is a parameter with an explicit soundness theorem for every
accepted status-indexed edge.  The fixed structural transition propagates and
discharges assumptions, checks exact introduced-symbol deltas, and maintains a
global signature ledger.  It contains no inference-rule implementation and no
proof search.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedService

open Mettapedia.GSLT.LanguageDef.TptpOfficialRoleSemantics
open Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.TptpOfficialPrincipalSymbols
open Mettapedia.Languages.TPTP.StatusSemantics

universe uFormula uRule uEvidence uProvenance uObligation

variable {Formula : Type uFormula} {Rule : Type uRule}
  {Evidence : Type uEvidence} {Provenance : Type uProvenance}
  {Obligation : Type uObligation}

/-! ## Semantic carriers and normalized official metadata -/

/-- Source-derived provenance for one formula occurrence.  This records how
the occurrence entered the derivation; it is not itself a claim that the
formula is true. -/
inductive NodeOrigin where
  | input
  | inferred (status : Status)
  deriving DecidableEq, Repr

/-- A formula occurrence retains its official name, role, and currently open
assumption dependencies.  Its principal symbols are extracted from the
official formula AST; the guest calculus cannot replace that vocabulary. -/
structure SemanticNode (Formula : Type uFormula) where
  name : String
  role : FormulaRole
  origin : NodeOrigin
  body : Formula
  principalSymbols : Finset PrincipalSymbolId
  openAssumptions : Finset String
  deriving DecidableEq

/-- Persistent state of the structural verifier.  It is deliberately small:
formula occurrences and proof edges remain in the derivation machine. -/
structure MetadataState where
  knownSymbols : Finset PrincipalSymbolId
  deriving DecidableEq

/-- Calculus-specific evidence is paired with the exact official metadata.
The metadata is not reconstructed from a private opcode or checker result. -/
structure OfficialEvidence (Evidence : Type uEvidence) where
  metadata : RuleMetadata
  calculus : Evidence
  deriving DecidableEq

/-- Set-valued semantic view of the list-valued official records.  The
original lists remain available in `OfficialEvidence.metadata` for calculi
whose rule-specific evidence is order-sensitive. -/
structure NormalizedMetadata where
  status : Status
  declaredAssumptions : Finset String
  dischargedAssumptions : Finset String
  introducedSymbols : List PrincipalSymbolId
  deriving DecidableEq

def assumptionNames (records : List AssumptionsRecord) : List String :=
  records.flatMap AssumptionsRecord.names

def introducedSymbolIds (records : List NewSymbolsRecord) :
    List PrincipalSymbolId :=
  records.flatMap fun record => record.symbols.map PrincipalSymbol.id

/-- Decode every rule-indexed `discharge` detail as an official formula name.
Malformed discharge details fail closed; other rule-specific information is
left for the supplied calculus. -/
def dischargedNames? : List RuleInfoRecord -> Option (List String)
  | [] => some []
  | record :: records => do
      let rest <- dischargedNames? records
      if record.informationKind = "discharge" then
        let names <- record.details.mapM decodeReferenceNameGeneralTerm?
        some (names ++ rest)
      else
        some rest

def normalizeMetadata? (metadata : RuleMetadata) : Option NormalizedMetadata := do
  let discharged <- dischargedNames? metadata.ruleInfo
  some {
    status := metadata.status
    declaredAssumptions := (assumptionNames metadata.assumptions).toFinset
    dischargedAssumptions := discharged.toFinset
    introducedSymbols := introducedSymbolIds metadata.newSymbols
  }

/-! ## One-pass assumption and signature transition -/

def parentAssumptions (parents : List (SemanticNode Formula)) : Finset String :=
  parents.foldl (fun accumulated parent =>
    accumulated ∪ parent.openAssumptions) ∅

def parentSymbols (parents : List (SemanticNode Formula)) : Finset PrincipalSymbolId :=
  parents.foldl (fun symbols parent => symbols ∪ parent.principalSymbols) ∅

def nextMetadataState (state : MetadataState)
    (conclusion : SemanticNode Formula) : MetadataState :=
  { knownSymbols := state.knownSymbols ∪ conclusion.principalSymbols }

def finsetSubsetB {alpha : Type} [DecidableEq alpha]
    (left right : Finset alpha) : Bool :=
  decide (left ⊆ right)

def finsetEqualB {alpha : Type} [DecidableEq alpha]
    (left right : Finset alpha) : Bool :=
  decide (left = right)

def listNodupB {alpha : Type} [DecidableEq alpha] (items : List alpha) : Bool :=
  decide (items.dedup = items)

/-- Exact structural obligations for one inference edge.  Assumptions behave
as a set semantically while their original order and multiplicity remain in
the raw metadata.  Introduced symbols are stricter: their official list must
be duplicate-free, globally fresh, and exactly the formula's signature delta.
-/
def metadataAcceptedB (state : MetadataState) (parents : List (SemanticNode Formula))
    (conclusion : SemanticNode Formula) (metadata : NormalizedMetadata) : Bool :=
  let openParents := parentAssumptions parents
  let expectedOpen := openParents \ metadata.dischargedAssumptions
  let introduced := metadata.introducedSymbols.toFinset
  decide (conclusion.origin = .inferred metadata.status) &&
    conclusion.role.semanticSupported &&
    finsetSubsetB (parentSymbols parents) state.knownSymbols &&
    finsetSubsetB metadata.dischargedAssumptions openParents &&
    finsetEqualB metadata.declaredAssumptions expectedOpen &&
    finsetEqualB conclusion.openAssumptions expectedOpen &&
    listNodupB metadata.introducedSymbols &&
    finsetEqualB (introduced ∩ state.knownSymbols) ∅ &&
    finsetEqualB
      (conclusion.principalSymbols \ state.knownSymbols) introduced

def MetadataAccepted (state : MetadataState) (parents : List (SemanticNode Formula))
    (conclusion : SemanticNode Formula) (metadata : NormalizedMetadata) : Prop :=
  metadataAcceptedB state parents conclusion metadata = true

def MetadataConditions (state : MetadataState) (parents : List (SemanticNode Formula))
    (conclusion : SemanticNode Formula) (metadata : NormalizedMetadata) : Prop :=
  let openParents := parentAssumptions parents
  let expectedOpen := openParents \ metadata.dischargedAssumptions
  let introduced := metadata.introducedSymbols.toFinset
  conclusion.origin = .inferred metadata.status /\
    conclusion.role.semanticSupported = true /\
    parentSymbols parents ⊆ state.knownSymbols /\
    metadata.dischargedAssumptions ⊆ openParents /\
    metadata.declaredAssumptions = expectedOpen /\
    conclusion.openAssumptions = expectedOpen /\
    metadata.introducedSymbols.Nodup /\
    introduced ∩ state.knownSymbols = ∅ /\
    conclusion.principalSymbols \ state.knownSymbols = introduced

theorem metadataAccepted_iff_conditions (state : MetadataState)
    (parents : List (SemanticNode Formula))
    (conclusion : SemanticNode Formula) (metadata : NormalizedMetadata) :
    MetadataAccepted state parents conclusion metadata <->
      MetadataConditions state parents conclusion metadata := by
  simp [MetadataAccepted, metadataAcceptedB, MetadataConditions,
    finsetSubsetB, finsetEqualB, listNodupB, List.dedup_eq_self, and_assoc]

def metadataTransition? (state : MetadataState) (parents : List (SemanticNode Formula))
    (conclusion : SemanticNode Formula) (metadata : NormalizedMetadata) :
    Option MetadataState :=
  if metadataAcceptedB state parents conclusion metadata then
    some (nextMetadataState state conclusion)
  else
    none

theorem metadataTransition?_sound (state next : MetadataState)
    (parents : List (SemanticNode Formula))
    (conclusion : SemanticNode Formula) (metadata : NormalizedMetadata)
    (accepted : metadataTransition? state parents conclusion metadata =
      some next) :
    MetadataAccepted state parents conclusion metadata /\
      next = nextMetadataState state conclusion := by
  unfold metadataTransition? at accepted
  split at accepted <;> rename_i condition
  · simp at accepted
    subst next
    exact ⟨condition, rfl⟩
  · simp at accepted

/-! ## Status-indexed calculus boundary -/

/-- A calculus service checks one local edge and proves exactly the semantic
relation named by its TSTP status.  Unsupported statuses return `false`; they
must not be silently reinterpreted as theoremhood. -/
structure Calculus (Formula : Type uFormula) (Rule : Type uRule)
    (Evidence : Type uEvidence) where
  meaning : StatusMeaning Formula
  /-- Which derivational origins may be consumed as premises of this rule.
  This is distinct from `check`: origin admission protects composition, while
  `check` establishes the local status-indexed semantic relation. -/
  parentOriginsAccepted : Rule -> Status -> List NodeOrigin -> Bool
  /-- Rule-specific use of normalized official metadata.  This is distinct
  from the generic assumption/signature transition: a signature-extending
  rule, for example, must require the exact `new_symbols` list it realizes. -/
  ruleMetadataAccepted : Rule -> NormalizedMetadata -> Evidence -> Bool
  check : Rule -> Status -> List Formula -> Evidence -> Formula -> Bool
  check_sound : forall rule status parents evidence conclusion,
    check rule status parents evidence conclusion = true ->
      meaning.Meaning status { parents, inferred := conclusion }

/-- The calculus host must be able to recover the exact official principal
symbol set from its semantic formula carrier.  Returning `none` rejects a
carrier outside the declared semantic fragment.  This prevents a guest
projection from pairing one formula with unrelated signature metadata. -/
structure FormulaSignatureAuthority (Formula : Type uFormula) where
  principalSymbols? : Formula -> Option (Finset PrincipalSymbolId)

structure Service (Formula : Type uFormula) (Rule : Type uRule)
    (Evidence : Type uEvidence) where
  formulaSignature : FormulaSignatureAuthority Formula
  calculus : Calculus Formula Rule Evidence

def nodeSignatureAcceptedB (service : Service Formula Rule Evidence)
    (node : SemanticNode Formula) : Bool :=
  decide (service.formulaSignature.principalSymbols? node.body =
    some node.principalSymbols)

def nodesSignatureAcceptedB (service : Service Formula Rule Evidence)
    (nodes : List (SemanticNode Formula)) : Bool :=
  nodes.all (nodeSignatureAcceptedB service)

def NodeSignatureExact (service : Service Formula Rule Evidence)
    (node : SemanticNode Formula) : Prop :=
  service.formulaSignature.principalSymbols? node.body =
    some node.principalSymbols

theorem nodeSignatureAcceptedB_iff_exact
    (service : Service Formula Rule Evidence)
    (node : SemanticNode Formula) :
    nodeSignatureAcceptedB service node = true <->
      NodeSignatureExact service node := by
  simp [nodeSignatureAcceptedB, NodeSignatureExact]

theorem nodesSignatureAcceptedB_iff_exact
    (service : Service Formula Rule Evidence)
    (nodes : List (SemanticNode Formula)) :
    nodesSignatureAcceptedB service nodes = true <->
      forall node, node ∈ nodes -> NodeSignatureExact service node := by
  simp [nodesSignatureAcceptedB, nodeSignatureAcceptedB_iff_exact]

def checkStep? (service : Service Formula Rule Evidence)
    (state : MetadataState) (rule : Rule)
    (parents : List (SemanticNode Formula))
    (evidence : OfficialEvidence Evidence)
    (conclusion : SemanticNode Formula) : Option MetadataState :=
  match normalizeMetadata? evidence.metadata with
  | none => none
  | some metadata =>
      if nodesSignatureAcceptedB service parents &&
          nodeSignatureAcceptedB service conclusion then
        match metadataTransition? state parents conclusion metadata with
        | none => none
        | some next =>
            if service.calculus.parentOriginsAccepted rule metadata.status
                  (parents.map SemanticNode.origin) &&
                service.calculus.ruleMetadataAccepted rule metadata
                  evidence.calculus &&
                service.calculus.check rule metadata.status
                  (parents.map SemanticNode.body) evidence.calculus conclusion.body then
              some next
            else
              none
      else
        none

def StepSound (service : Service Formula Rule Evidence)
    (state next : MetadataState) (rule : Rule)
    (parents : List (SemanticNode Formula))
    (evidence : OfficialEvidence Evidence)
    (conclusion : SemanticNode Formula) : Prop :=
  exists normalized : NormalizedMetadata,
    normalizeMetadata? evidence.metadata = some normalized /\
    (forall parent, parent ∈ parents -> NodeSignatureExact service parent) /\
    NodeSignatureExact service conclusion /\
    MetadataAccepted state parents conclusion normalized /\
    next = nextMetadataState state conclusion /\
    service.calculus.parentOriginsAccepted rule normalized.status
      (parents.map SemanticNode.origin) = true /\
    service.calculus.ruleMetadataAccepted rule normalized
      evidence.calculus = true /\
    service.calculus.check rule normalized.status
      (parents.map SemanticNode.body) evidence.calculus conclusion.body = true /\
    service.calculus.meaning.Meaning normalized.status {
      parents := parents.map SemanticNode.body
      inferred := conclusion.body
    }

theorem checkStep?_sound (service : Service Formula Rule Evidence)
    (state next : MetadataState) (rule : Rule)
    (parents : List (SemanticNode Formula))
    (evidence : OfficialEvidence Evidence)
    (conclusion : SemanticNode Formula)
    (accepted : checkStep? service state rule parents evidence conclusion = some next) :
    StepSound service state next rule parents evidence conclusion := by
  unfold checkStep? at accepted
  cases normalizedEq : normalizeMetadata? evidence.metadata with
  | none => simp [normalizedEq] at accepted
  | some metadata =>
      simp only [normalizedEq] at accepted
      split at accepted
      next signaturesAccepted =>
        have signatureParts :
            nodesSignatureAcceptedB service parents = true /\
              nodeSignatureAcceptedB service conclusion = true := by
          simpa only [Bool.and_eq_true] using signaturesAccepted
        cases transitionEq : metadataTransition? state parents
            conclusion metadata with
        | none => simp [transitionEq] at accepted
        | some actualNext =>
            simp only [transitionEq] at accepted
            split at accepted
            next calculusAccepted =>
              have nextEqual : next = actualNext := Option.some.inj accepted |>.symm
              have metadataSound := metadataTransition?_sound
                state actualNext parents conclusion metadata transitionEq
              have acceptedParts :
                  service.calculus.parentOriginsAccepted rule metadata.status
                      (parents.map SemanticNode.origin) = true /\
                    service.calculus.ruleMetadataAccepted rule metadata
                      evidence.calculus = true /\
                    service.calculus.check rule metadata.status
                      (parents.map SemanticNode.body) evidence.calculus
                        conclusion.body = true := by
                simpa only [Bool.and_eq_true, and_assoc] using calculusAccepted
              refine ⟨metadata, normalizedEq,
                (nodesSignatureAcceptedB_iff_exact service parents).mp
                  signatureParts.1,
                (nodeSignatureAcceptedB_iff_exact service conclusion).mp
                  signatureParts.2,
                metadataSound.1, nextEqual.trans metadataSound.2,
                acceptedParts.1, acceptedParts.2.1, acceptedParts.2.2, ?_⟩
              exact service.calculus.check_sound rule metadata.status
                (parents.map SemanticNode.body) evidence.calculus conclusion.body
                acceptedParts.2.2
            next calculusRejected => simp at accepted
      next signaturesRejected => simp at accepted

/-! ## Adapter to the generic derivation-check machine -/

/-- Problem-specific leaf and root authorization.  These decisions contain no
calculus rule: inference remains entirely in `Service.calculus`. -/
structure MachineBoundary (MachineFormula MachineProvenance MachineObligation : Type) where
  initialMetadata : MetadataState
  inputAuthorized : MachineProvenance -> SemanticNode MachineFormula -> Bool
  rootAuthorized : MetadataState -> SemanticNode MachineFormula -> MachineObligation -> Bool

def expectedInputAssumptions {MachineFormula : Type}
    (formula : SemanticNode MachineFormula) : Finset String :=
  if formula.role.requiresDischarge then [formula.name].toFinset else ∅

def inputAcceptedB {MachineFormula MachineRule MachineEvidence
    MachineProvenance MachineObligation : Type}
    (service : Service MachineFormula MachineRule MachineEvidence)
    (boundary : MachineBoundary MachineFormula MachineProvenance MachineObligation)
    (state : MetadataState) (provenance : MachineProvenance)
    (formula : SemanticNode MachineFormula) : Bool :=
  decide (formula.origin = .input) &&
    nodeSignatureAcceptedB service formula &&
    boundary.inputAuthorized provenance formula &&
    formula.role.semanticSupported &&
    finsetSubsetB formula.principalSymbols state.knownSymbols &&
    finsetEqualB formula.openAssumptions (expectedInputAssumptions formula)

def rootAcceptedB {MachineFormula MachineProvenance MachineObligation : Type}
    (boundary : MachineBoundary MachineFormula MachineProvenance MachineObligation)
    (state : MetadataState) (formula : SemanticNode MachineFormula)
    (obligation : MachineObligation) : Bool :=
  finsetEqualB formula.openAssumptions ∅ &&
    boundary.rootAuthorized state formula obligation

def machineServices {MachineFormula MachineRule MachineEvidence
    MachineProvenance MachineObligation : Type}
    (service : Service MachineFormula MachineRule MachineEvidence)
    (boundary : MachineBoundary MachineFormula MachineProvenance MachineObligation) :
    Services (SemanticNode MachineFormula) MachineRule (OfficialEvidence MachineEvidence)
      MachineProvenance MachineObligation MetadataState where
  initial := boundary.initialMetadata
  input := fun state provenance formula =>
    if inputAcceptedB service boundary state provenance formula then
      some state
    else
      none
  infer := fun state rule parents evidence conclusion =>
    checkStep? service state rule parents evidence conclusion
  root := fun state formula obligation =>
    rootAcceptedB boundary state formula obligation

def InputConditions {MachineFormula MachineRule MachineEvidence
    MachineProvenance MachineObligation : Type}
    (service : Service MachineFormula MachineRule MachineEvidence)
    (boundary : MachineBoundary MachineFormula MachineProvenance MachineObligation)
    (state : MetadataState) (provenance : MachineProvenance)
    (formula : SemanticNode MachineFormula) : Prop :=
  formula.origin = .input /\
    NodeSignatureExact service formula /\
    boundary.inputAuthorized provenance formula = true /\
    formula.role.semanticSupported = true /\
    formula.principalSymbols ⊆ state.knownSymbols /\
    formula.openAssumptions = expectedInputAssumptions formula

theorem inputAcceptedB_iff_conditions
    {MachineFormula MachineRule MachineEvidence MachineProvenance
      MachineObligation : Type}
    (service : Service MachineFormula MachineRule MachineEvidence)
    (boundary : MachineBoundary MachineFormula MachineProvenance MachineObligation)
    (state : MetadataState) (provenance : MachineProvenance)
    (formula : SemanticNode MachineFormula) :
    inputAcceptedB service boundary state provenance formula = true <->
      InputConditions service boundary state provenance formula := by
  simp [inputAcceptedB, InputConditions, nodeSignatureAcceptedB_iff_exact,
    finsetSubsetB, finsetEqualB, and_assoc]

theorem machineServices_input_exact
    {MachineFormula MachineRule MachineEvidence MachineProvenance
      MachineObligation : Type}
    (service : Service MachineFormula MachineRule MachineEvidence)
    (boundary : MachineBoundary MachineFormula MachineProvenance MachineObligation)
    (state next : MetadataState) (provenance : MachineProvenance)
    (formula : SemanticNode MachineFormula)
    (accepted : (machineServices service boundary).input state provenance formula =
      some next) :
      InputConditions service boundary state provenance formula /\ next = state := by
  simp only [machineServices] at accepted
  split at accepted <;> rename_i condition
  · simp at accepted
    subst next
    exact ⟨(inputAcceptedB_iff_conditions service boundary state provenance formula).mp
      condition, rfl⟩
  · simp at accepted

theorem machineServices_infer_sound
    {MachineFormula MachineRule MachineEvidence MachineProvenance
      MachineObligation : Type}
    (service : Service MachineFormula MachineRule MachineEvidence)
    (boundary : MachineBoundary MachineFormula MachineProvenance MachineObligation)
    (state next : MetadataState) (rule : MachineRule)
    (parents : List (SemanticNode MachineFormula))
    (evidence : OfficialEvidence MachineEvidence)
    (conclusion : SemanticNode MachineFormula)
    (accepted : (machineServices service boundary).infer state rule parents
      evidence conclusion = some next) :
    StepSound service state next rule parents evidence conclusion := by
  exact checkStep?_sound service state next rule parents evidence conclusion accepted

theorem machineServices_root_exact
    {MachineFormula MachineRule MachineEvidence MachineProvenance
      MachineObligation : Type}
    (service : Service MachineFormula MachineRule MachineEvidence)
    (boundary : MachineBoundary MachineFormula MachineProvenance MachineObligation)
    (state : MetadataState) (formula : SemanticNode MachineFormula)
    (obligation : MachineObligation)
    (accepted : (machineServices service boundary).root state formula obligation = true) :
    formula.openAssumptions = ∅ /\
      boundary.rootAuthorized state formula obligation = true := by
  simpa [machineServices, rootAcceptedB, finsetEqualB] using accepted

/-! ## Proof-relevant status ledger -/

/-- A checked formula occurrence together with the exact local reason it was
accepted.  This is intentionally status-polymorphic: an inference constructor
stores its `StepSound` relation instead of pretending that every TSTP status
is theorem-preserving.  Parent derivations make the object a proof-relevant
tree view of the machine's checked DAG. -/
inductive StatusDerivation
    {MachineFormula MachineRule MachineEvidence MachineProvenance
      MachineObligation : Type}
    (service : Service MachineFormula MachineRule MachineEvidence)
    (boundary : MachineBoundary MachineFormula MachineProvenance MachineObligation) :
    SemanticNode MachineFormula -> Prop where
  | input (state : MetadataState) (provenance : MachineProvenance)
      (formula : SemanticNode MachineFormula)
      (conditions : InputConditions service boundary state provenance formula) :
      StatusDerivation service boundary formula
  | infer (state next : MetadataState) (rule : MachineRule)
      (parents : List (SemanticNode MachineFormula))
      (evidence : OfficialEvidence MachineEvidence)
      (conclusion : SemanticNode MachineFormula)
      (parentsChecked : forall parent, parent ∈ parents ->
        StatusDerivation service boundary parent)
      (stepSound : StepSound service state next rule parents evidence conclusion) :
      StatusDerivation service boundary conclusion

/-- What the status-generic layer may honestly conclude about an accepted
root.  It records a fully checked derivation, closed assumptions, and the
problem-specific root authorization.  Turning this into theoremhood,
countertheoremhood, or equisatisfiability is a separate calculus theorem. -/
inductive StatusCheckedObjective
    {MachineFormula MachineRule MachineEvidence MachineProvenance
      MachineObligation : Type}
    (service : Service MachineFormula MachineRule MachineEvidence)
    (boundary : MachineBoundary MachineFormula MachineProvenance MachineObligation)
    (obligation : MachineObligation) : Prop where
  | verified (state : MetadataState) (formula : SemanticNode MachineFormula)
      (derivation : StatusDerivation service boundary formula)
      (assumptionsClosed : formula.openAssumptions = ∅)
      (rootAuthorized :
        boundary.rootAuthorized state formula obligation = true) :
      StatusCheckedObjective service boundary obligation

/-- One continuous invariant for every status-indexed machine branch.  It
proves structural and local-semantic acceptance without collapsing unlike
TSTP statuses into a single global consequence relation. -/
def structuralSoundServices
    {MachineFormula MachineRule MachineEvidence MachineProvenance
      MachineObligation : Type}
    (service : Service MachineFormula MachineRule MachineEvidence)
    (boundary : MachineBoundary MachineFormula MachineProvenance MachineObligation) :
    SoundServices (machineServices service boundary) where
  Valid := StatusDerivation service boundary
  Objective := StatusCheckedObjective service boundary
  StateValid := fun _ => True
  initial_sound := trivial
  input_sound := by
    intro state provenance formula next accepted _stateValid
    have exactInput := machineServices_input_exact
      service boundary state next provenance formula accepted
    exact ⟨.input state provenance formula exactInput.1, trivial⟩
  infer_sound := by
    intro state rule parents evidence conclusion next accepted
      _stateValid parentsChecked
    have soundStep := machineServices_infer_sound
      service boundary state next rule parents evidence conclusion accepted
    exact ⟨.infer state next rule parents evidence conclusion
      parentsChecked soundStep, trivial⟩
  root_sound := by
    intro state formula obligation accepted _stateValid derivation
    have exactRoot := machineServices_root_exact
      service boundary state formula obligation accepted
    exact .verified state formula derivation exactRoot.1 exactRoot.2

/-! ## Structural positive and negative canaries -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo.Canary

def functorId (name : String) : PrincipalSymbolId :=
  { kind := .functor, name }

def parent : SemanticNode (Finset PrincipalSymbolId) := {
  name := "h"
  role := .assumption
  origin := .input
  body := [functorId "p"].toFinset
  principalSymbols := [functorId "p"].toFinset
  openAssumptions := ["h"].toFinset
}

def conclusion : SemanticNode (Finset PrincipalSymbolId) := {
  name := "derived"
  role := .plain
  origin := .inferred .thm
  body := [functorId "p", functorId "sk"].toFinset
  principalSymbols := [functorId "p", functorId "sk"].toFinset
  openAssumptions := ∅
}

def state : MetadataState := {
  knownSymbols := [functorId "p"].toFinset
}

def dischargedAndFresh : NormalizedMetadata := {
  status := .thm
  declaredAssumptions := ∅
  dischargedAssumptions := ["h"].toFinset
  introducedSymbols := [functorId "sk"]
}

theorem discharge_and_fresh_symbol_are_accepted :
    metadataTransition? state [parent] conclusion dischargedAndFresh =
      some { knownSymbols := [functorId "p", functorId "sk"].toFinset } := by
  rfl

def wrongStatusOriginConclusion : SemanticNode (Finset PrincipalSymbolId) := {
  conclusion with origin := .inferred .cth
}

theorem conclusion_origin_must_match_metadata_status :
    metadataTransition? state [parent] wrongStatusOriginConclusion
      dischargedAndFresh = none := by
  rfl

def permissiveBoundary :
    MachineBoundary (Finset PrincipalSymbolId) Unit Unit where
  initialMetadata := state
  inputAuthorized := fun _ _ => true
  rootAuthorized := fun _ _ _ => false

def canaryService : Service (Finset PrincipalSymbolId) Unit Unit where
  formulaSignature := {
    principalSymbols? := some
  }
  calculus := {
    meaning := { Meaning := fun _ _ => False }
    parentOriginsAccepted := fun _ _ _ => false
    ruleMetadataAccepted := fun _ _ _ => false
    check := fun _ _ _ _ _ => false
    check_sound := by simp
  }

def inferredOccurrenceMasqueradingAsInput :
    SemanticNode (Finset PrincipalSymbolId) := {
  parent with origin := .inferred .thm
}

def mismatchedInputSignature : SemanticNode (Finset PrincipalSymbolId) := {
  parent with principalSymbols := [functorId "sk"].toFinset
}

theorem only_source_input_origin_enters_input_branch :
    inputAcceptedB canaryService permissiveBoundary state () parent = true /\
    inputAcceptedB canaryService permissiveBoundary state ()
      inferredOccurrenceMasqueradingAsInput = false := by
  decide +kernel

theorem formula_signature_cannot_be_replaced_by_metadata :
    nodeSignatureAcceptedB canaryService parent = true /\
    nodeSignatureAcceptedB canaryService mismatchedInputSignature = false /\
    inputAcceptedB canaryService permissiveBoundary state ()
      mismatchedInputSignature = false := by
  decide +kernel

def missingDischarge : NormalizedMetadata := {
  dischargedAndFresh with
  dischargedAssumptions := ∅
}

theorem missing_discharge_is_rejected :
    metadataTransition? state [parent] conclusion missingDischarge = none := by
  rfl

def staleIntroduction : NormalizedMetadata := {
  dischargedAndFresh with
  introducedSymbols := [functorId "p"]
}

theorem stale_introduced_symbol_is_rejected :
    metadataTransition? state [parent] conclusion staleIntroduction = none := by
  rfl

def duplicateIntroduction : NormalizedMetadata := {
  dischargedAndFresh with
  introducedSymbols := [functorId "sk", functorId "sk"]
}

theorem duplicate_introduced_symbol_is_rejected :
    metadataTransition? state [parent] conclusion duplicateIntroduction = none := by
  rfl

theorem official_assumption_and_discharge_metadata_normalizes_exactly :
    (decodeRuleMetadata? "contra" assumptionsAndDischarge).bind normalizeMetadata? =
      some {
        status := .thm
        declaredAssumptions := ["h"].toFinset
        dischargedAssumptions := ["h"].toFinset
        introducedSymbols := []
      } := by
  rfl

def malformedDischargeDetail : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern :=
  usefulInfo [
    functionTerm "status" [atomicTerm "thm"],
    functionTerm "contra" [atomicTerm "discharge",
      listTerm [functionTerm "not-a-name" [atomicTerm "x"]]]]

theorem malformed_discharge_name_is_rejected_semantically :
    (decodeRuleMetadata? "contra" malformedDischargeDetail).bind normalizeMetadata? =
      none := by
  rfl

end Canary

#print axioms metadataTransition?_sound
#print axioms metadataAccepted_iff_conditions
#print axioms nodeSignatureAcceptedB_iff_exact
#print axioms nodesSignatureAcceptedB_iff_exact
#print axioms checkStep?_sound
#print axioms machineServices_input_exact
#print axioms machineServices_infer_sound
#print axioms machineServices_root_exact
#print axioms structuralSoundServices
#print axioms Canary.discharge_and_fresh_symbol_are_accepted
#print axioms Canary.conclusion_origin_must_match_metadata_status
#print axioms Canary.only_source_input_origin_enters_input_branch
#print axioms Canary.formula_signature_cannot_be_replaced_by_metadata
#print axioms Canary.missing_discharge_is_rejected
#print axioms Canary.stale_introduced_symbol_is_rejected
#print axioms Canary.duplicate_introduced_symbol_is_rejected
#print axioms Canary.official_assumption_and_discharge_metadata_normalizes_exactly
#print axioms Canary.malformed_discharge_name_is_rejected_semantically

end Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedService
