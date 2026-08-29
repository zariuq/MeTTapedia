import Mettapedia.GSLT.LanguageDef.TptpOfficialTheoryStateComposition

/-!
# Signature-extending theory transformations for official TSTP

Same-signature contextual replacement is not sufficient for Skolemization or
definitional naming: those transformations extend the formula vocabulary.
This module makes the source and target model signatures explicit, requires a
target model extending each satisfying source model, and requires every
satisfying target model to restrict back to a satisfying source model.

The generic model theory is connected to the exact `new_symbols` delta already
checked by the official status-indexed derivation service.  It contains no
Skolemization algorithm and no inference-rule implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialSignatureExtensionComposition

open Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedService
open Mettapedia.GSLT.LanguageDef.TptpOfficialTheoryStateComposition
open Mettapedia.GSLT.LanguageDef.TptpOfficialPrincipalSymbols
open Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo
open Mettapedia.Languages.TPTP.StatusSemantics

universe uSymbol uFormula uModel

/-! ## Signature-indexed model semantics -/

/-- Model semantics indexed by the exact finite vocabulary available at one
theory state.  Restriction must preserve every formula whose principal symbols
already lie in the source signature. -/
structure SignatureIndexedModelSemantics
    (Symbol : Type uSymbol) [DecidableEq Symbol]
    (Formula : Type uFormula) where
  symbols : Formula -> Finset Symbol
  Model : Finset Symbol -> Type uModel
  satisfies : forall signature, Model signature -> Formula -> Prop
  restrict : forall {source target : Finset Symbol},
    source ⊆ target -> Model target -> Model source
  restrict_satisfies : forall {source target : Finset Symbol}
    (included : source ⊆ target) (model : Model target) (formula : Formula),
    symbols formula ⊆ source ->
      (satisfies source (restrict included model) formula <->
        satisfies target model formula)

namespace SignatureIndexedModelSemantics

variable {Symbol : Type uSymbol} [DecidableEq Symbol]
  {Formula : Type uFormula}
  (semantics : SignatureIndexedModelSemantics Symbol Formula)

def TheoryWellFormed (signature : Finset Symbol)
    (theory : List Formula) : Prop :=
  forall formula, formula ∈ theory -> semantics.symbols formula ⊆ signature

def SatisfiesAll (signature : Finset Symbol)
    (model : semantics.Model signature) (theory : List Formula) : Prop :=
  forall formula, formula ∈ theory -> semantics.satisfies signature model formula

def Satisfiable (signature : Finset Symbol) (theory : List Formula) : Prop :=
  exists model, semantics.SatisfiesAll signature model theory

end SignatureIndexedModelSemantics

structure IndexedTheoryState
    (Symbol : Type uSymbol) [DecidableEq Symbol]
    (Formula : Type uFormula) where
  signature : Finset Symbol
  theory : List Formula

variable {Symbol : Type uSymbol} [DecidableEq Symbol]
  {Formula : Type uFormula}

/-- Exact syntactic signature growth, including the source-ordered introduced
symbol list retained by official TSTP metadata. -/
structure ExactSignatureDelta (source target : Finset Symbol) : Type uSymbol where
  introduced : List Symbol
  introduced_nodup : introduced.Nodup
  introduced_fresh : introduced.toFinset ∩ source = ∅
  target_eq : target = source ∪ introduced.toFinset

theorem ExactSignatureDelta.source_subset
    {source target : Finset Symbol}
    (delta : ExactSignatureDelta source target) : source ⊆ target := by
  rw [delta.target_eq]
  exact Finset.subset_union_left

/-- A signature-changing transformation carries both directions of the model
correspondence.  The forward witness extends the particular source model, not
merely some unrelated model of the target theory. -/
structure SignatureChangingTransformation
    (semantics : SignatureIndexedModelSemantics Symbol Formula)
    (source target : IndexedTheoryState Symbol Formula) where
  delta : ExactSignatureDelta source.signature target.signature
  source_well_formed : semantics.TheoryWellFormed
    source.signature source.theory
  target_well_formed : semantics.TheoryWellFormed
    target.signature target.theory
  forward : forall sourceModel,
    semantics.SatisfiesAll source.signature sourceModel source.theory ->
      exists targetModel,
        semantics.restrict delta.source_subset targetModel = sourceModel /\
        semantics.SatisfiesAll target.signature targetModel target.theory
  backward : forall targetModel,
    semantics.SatisfiesAll target.signature targetModel target.theory ->
      semantics.SatisfiesAll source.signature
        (semantics.restrict delta.source_subset targetModel) source.theory

theorem SignatureChangingTransformation.satisfiable_iff
    {semantics : SignatureIndexedModelSemantics Symbol Formula}
    {source target : IndexedTheoryState Symbol Formula}
    (transformation : SignatureChangingTransformation semantics source target) :
    semantics.Satisfiable source.signature source.theory <->
      semantics.Satisfiable target.signature target.theory := by
  constructor
  · rintro ⟨sourceModel, sourceSatisfied⟩
    rcases transformation.forward sourceModel sourceSatisfied with
      ⟨targetModel, _extends, targetSatisfied⟩
    exact ⟨targetModel, targetSatisfied⟩
  · rintro ⟨targetModel, targetSatisfied⟩
    exact ⟨semantics.restrict transformation.delta.source_subset targetModel,
      transformation.backward targetModel targetSatisfied⟩

/-- Finite chain of signature-changing theory transformations. -/
inductive SignatureChangingTrace
    (semantics : SignatureIndexedModelSemantics Symbol Formula) :
    IndexedTheoryState Symbol Formula -> IndexedTheoryState Symbol Formula -> Prop where
  | refl (state : IndexedTheoryState Symbol Formula) :
      SignatureChangingTrace semantics state state
  | step {source middle target : IndexedTheoryState Symbol Formula}
      (transformation : SignatureChangingTransformation semantics source middle)
      (rest : SignatureChangingTrace semantics middle target) :
      SignatureChangingTrace semantics source target

theorem SignatureChangingTrace.satisfiable_iff
    {semantics : SignatureIndexedModelSemantics Symbol Formula}
    {source target : IndexedTheoryState Symbol Formula}
    (trace : SignatureChangingTrace semantics source target) :
    semantics.Satisfiable source.signature source.theory <->
      semantics.Satisfiable target.signature target.theory := by
  induction trace with
  | refl => exact Iff.rfl
  | step transformation rest inductionHypothesis =>
      exact transformation.satisfiable_iff.trans inductionHypothesis

/-! ## Exact official introduced-symbol delta -/

variable {Rule Evidence : Type}

/-- Every accepted official edge determines one exact signature extension.
This theorem uses the ordered, duplicate-free, fresh `new_symbols` list and
the source-derived conclusion-symbol delta; it does not infer freshness from a
calculus name. -/
theorem stepSound_hasExactSignatureDelta
    {service : Service Formula Rule Evidence}
    {state next : MetadataState} {rule : Rule}
    {parents : List (SemanticNode Formula)}
    {evidence : OfficialEvidence Evidence}
    {conclusion : SemanticNode Formula}
    (stepSound : StepSound service state next rule parents evidence conclusion) :
    Nonempty (ExactSignatureDelta state.knownSymbols next.knownSymbols) := by
  rcases stepSound with
    ⟨normalized, _normalizedEq, _parentSignatures, _conclusionSignature,
      metadataAccepted, nextEq,
      _parentOriginsAccepted, _ruleMetadataAccepted,
      _calculusAccepted, _semanticMeaning⟩
  rcases (metadataAccepted_iff_conditions state parents conclusion normalized).mp
      metadataAccepted with
    ⟨_originEq, _roleAccepted, _parentSymbols, _discharged, _declared,
      _open, introducedNodup, introducedFresh, conclusionDelta⟩
  refine ⟨{
    introduced := normalized.introducedSymbols
    introduced_nodup := introducedNodup
    introduced_fresh := introducedFresh
    target_eq := ?_
  }⟩
  rw [nextEq]
  change state.knownSymbols ∪ conclusion.principalSymbols =
    state.knownSymbols ∪ normalized.introducedSymbols.toFinset
  rw [← conclusionDelta]
  exact (Finset.union_sdiff_self_eq_union
    (s := state.knownSymbols) (t := conclusion.principalSymbols)).symm

/-! ## Signature-extending `.esa` calculus profile -/

def sourceTheoryState (state : MetadataState)
    (parents : List (SemanticNode Formula)) :
    IndexedTheoryState PrincipalSymbolId Formula := {
  signature := state.knownSymbols
  theory := parents.map SemanticNode.body
}

def targetTheoryState (next : MetadataState)
    (conclusion : SemanticNode Formula) :
    IndexedTheoryState PrincipalSymbolId Formula := {
  signature := next.knownSymbols
  theory := [conclusion.body]
}

/-- Additional obligations for an `.esa` calculus whose accepted step extends
the vocabulary.  Local TSTP equisatisfiability and indexed model extension are
both retained.  The indexed theorem must use the exact normalized official
introduced-symbol list. -/
structure SignatureExtendingEsaProfile
    (localSemantics : ClassicalModelSemantics Formula)
    (indexedSemantics :
      SignatureIndexedModelSemantics PrincipalSymbolId Formula)
    (service : Service Formula Rule Evidence) where
  local_meaning_eq :
    service.calculus.meaning = localSemantics.commonStatusMeaning
  accepted_status : forall rule status parents evidence conclusion,
    service.calculus.check rule status parents evidence conclusion = true ->
      status = .esa
  parents_are_theory_entries : forall rule status origins,
    service.calculus.parentOriginsAccepted rule status origins = true ->
      forall origin, origin ∈ origins -> TheoryEntryOrigin origin
  indexed_sound : forall (state next : MetadataState) (rule : Rule)
    (parents : List (SemanticNode Formula))
    (evidence : OfficialEvidence Evidence)
    (conclusion : SemanticNode Formula) (normalized : NormalizedMetadata),
    normalizeMetadata? evidence.metadata = some normalized ->
    (forall parent, parent ∈ parents -> NodeSignatureExact service parent) ->
    NodeSignatureExact service conclusion ->
    MetadataAccepted state parents conclusion normalized ->
    next = nextMetadataState state conclusion ->
    service.calculus.ruleMetadataAccepted rule normalized
      evidence.calculus = true ->
    service.calculus.check rule .esa (parents.map SemanticNode.body)
      evidence.calculus conclusion.body = true ->
      exists transformation : SignatureChangingTransformation indexedSemantics
        (sourceTheoryState state parents) (targetTheoryState next conclusion),
        transformation.delta.introduced = normalized.introducedSymbols

/-- Complete semantic object supplied by one accepted signature-extending
`.esa` edge.  This is proposition-valued because `StepSound` is proof data;
the executable normalized metadata remains available directly from the input
evidence. -/
def CheckedSignatureExtendingEdge
    (localSemantics : ClassicalModelSemantics Formula)
    (indexedSemantics :
      SignatureIndexedModelSemantics PrincipalSymbolId Formula)
    (state next : MetadataState)
    (parents : List (SemanticNode Formula))
    (evidence : OfficialEvidence Evidence)
    (conclusion : SemanticNode Formula) : Prop :=
  exists normalized : NormalizedMetadata,
    exists transformation : SignatureChangingTransformation indexedSemantics
      (sourceTheoryState state parents) (targetTheoryState next conclusion),
      normalizeMetadata? evidence.metadata = some normalized /\
      conclusion.origin = .inferred .esa /\
      (forall parent, parent ∈ parents -> TheoryEntryOrigin parent.origin) /\
      localSemantics.EquiSatisfiableRelation {
        parents := parents.map SemanticNode.body
        inferred := conclusion.body
      } /\
      transformation.delta.introduced = normalized.introducedSymbols

theorem SignatureExtendingEsaProfile.checkedEdge
    {localSemantics : ClassicalModelSemantics Formula}
    {indexedSemantics :
      SignatureIndexedModelSemantics PrincipalSymbolId Formula}
    {service : Service Formula Rule Evidence}
    (profile : SignatureExtendingEsaProfile localSemantics indexedSemantics service)
    {state next : MetadataState} {rule : Rule}
    {parents : List (SemanticNode Formula)}
    {evidence : OfficialEvidence Evidence}
    {conclusion : SemanticNode Formula}
    (stepSound : StepSound service state next rule parents evidence conclusion) :
    CheckedSignatureExtendingEdge localSemantics indexedSemantics
      state next parents evidence conclusion := by
  rcases stepSound with
    ⟨normalized, normalizedEq, parentSignatures, conclusionSignature,
      metadataAccepted, nextEq,
      parentOriginsAccepted, ruleMetadataAccepted,
      calculusAccepted, semanticMeaning⟩
  have statusEq : normalized.status = .esa :=
    profile.accepted_status rule normalized.status
      (parents.map SemanticNode.body) evidence.calculus conclusion.body
      calculusAccepted
  have originEq : conclusion.origin = .inferred normalized.status :=
    (metadataAccepted_iff_conditions state parents conclusion normalized).mp
      metadataAccepted |>.1
  have parentEntries : forall parent, parent ∈ parents ->
      TheoryEntryOrigin parent.origin := by
    intro parent parentMember
    apply profile.parents_are_theory_entries rule normalized.status
      (parents.map SemanticNode.origin) parentOriginsAccepted parent.origin
    exact List.mem_map.mpr ⟨parent, parentMember, rfl⟩
  have localRelation : localSemantics.EquiSatisfiableRelation {
      parents := parents.map SemanticNode.body
      inferred := conclusion.body
    } := by
    rw [profile.local_meaning_eq] at semanticMeaning
    rw [statusEq] at semanticMeaning
    simpa [ClassicalModelSemantics.commonStatusMeaning] using semanticMeaning
  rw [statusEq] at calculusAccepted
  rcases profile.indexed_sound state next rule parents evidence conclusion
      normalized normalizedEq parentSignatures conclusionSignature
      metadataAccepted nextEq ruleMetadataAccepted calculusAccepted with
    ⟨transformation, introducedExact⟩
  exact ⟨normalized, transformation, normalizedEq,
    originEq.trans (congrArg NodeOrigin.inferred statusEq), parentEntries,
    localRelation, introducedExact⟩

/-! ## Nontrivial indexed-model canary -/

namespace Canary

inductive DemoSymbol where
  | base
  | fresh
  deriving DecidableEq, Repr

def sourceSignature : Finset DemoSymbol := [.base].toFinset
def targetSignature : Finset DemoSymbol := [.base, .fresh].toFinset

theorem fresh_symbol_absent_from_source :
    .fresh ∉ sourceSignature := by
  decide

theorem existing_symbol_cannot_be_the_introduced_delta :
    Not (exists delta : ExactSignatureDelta sourceSignature targetSignature,
      delta.introduced = [.base]) := by
  rintro ⟨delta, introducedEq⟩
  have freshness := delta.introduced_fresh
  rw [introducedEq] at freshness
  simp [sourceSignature] at freshness

/-- A model interprets exactly the symbols admitted by its signature. -/
def DemoModel (signature : Finset DemoSymbol) : Type :=
  forall symbol : DemoSymbol, symbol ∈ signature -> Bool

def demoSemantics : SignatureIndexedModelSemantics DemoSymbol DemoSymbol where
  symbols := fun formula => [formula].toFinset
  Model := DemoModel
  satisfies := fun signature model formula =>
    exists membership : formula ∈ signature, model formula membership = true
  restrict := fun included model symbol membership =>
    model symbol (included membership)
  restrict_satisfies := by
    intro source target included model formula formulaInSource
    have sourceMembership : formula ∈ source :=
      formulaInSource (by simp)
    constructor
    · rintro ⟨membership, valueTrue⟩
      exact ⟨included membership, valueTrue⟩
    · rintro ⟨membership, valueTrue⟩
      refine ⟨sourceMembership, ?_⟩
      simpa only using valueTrue

def sourceState : IndexedTheoryState DemoSymbol DemoSymbol := {
  signature := sourceSignature
  theory := [.base]
}

def targetState : IndexedTheoryState DemoSymbol DemoSymbol := {
  signature := targetSignature
  theory := [.base, .fresh]
}

def extendModel (sourceModel : DemoModel sourceSignature) :
    DemoModel targetSignature :=
  fun symbol _membership =>
    match symbol with
    | .base => sourceModel .base (by simp [sourceSignature])
    | .fresh => true

theorem restrict_extendModel (sourceModel : DemoModel sourceSignature) :
    demoSemantics.restrict (by
      intro symbol membership
      have symbolEq : symbol = .base := by
        simpa [sourceSignature] using membership
      subst symbol
      simp [targetSignature])
      (extendModel sourceModel) = sourceModel := by
  funext symbol membership
  cases symbol with
  | base => rfl
  | fresh => simp [sourceSignature] at membership

/-- Adding the genuinely fresh symbol is satisfiability-preserving because
each source model is extended with a concrete interpretation of that symbol,
and every target model restricts to the original signature. -/
def freshSymbolTransformation :
    SignatureChangingTransformation demoSemantics sourceState targetState where
  delta := {
    introduced := [.fresh]
    introduced_nodup := by simp
    introduced_fresh := by decide
    target_eq := by decide
  }
  source_well_formed := by
    intro formula member
    simp only [sourceState, List.mem_singleton] at member
    subst formula
    change [.base].toFinset ⊆ sourceState.signature
    simp [sourceState, sourceSignature]
  target_well_formed := by
    intro formula member
    simp only [targetState, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change [.base].toFinset ⊆ targetState.signature
      simp [targetState, targetSignature]
    · change [.fresh].toFinset ⊆ targetState.signature
      simp [targetState, targetSignature]
  forward := by
    intro sourceModel sourceSatisfied
    refine ⟨extendModel sourceModel, restrict_extendModel sourceModel, ?_⟩
    intro formula member
    simp only [targetState, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · rcases sourceSatisfied .base (by simp [sourceState]) with
        ⟨sourceMembership, sourceTrue⟩
      refine ⟨by simp [targetState, targetSignature], ?_⟩
      simpa [extendModel] using sourceTrue
    · exact ⟨by simp [targetState, targetSignature], rfl⟩
  backward := by
    intro targetModel targetSatisfied formula member
    simp only [sourceState, List.mem_singleton] at member
    subst formula
    rcases targetSatisfied .base (by simp [targetState]) with
      ⟨targetMembership, targetTrue⟩
    refine ⟨by simp [sourceState, sourceSignature], ?_⟩
    change targetModel .base _ = true
    simpa only using targetTrue

theorem source_and_target_satisfiable_iff :
    demoSemantics.Satisfiable sourceSignature [.base] <->
      demoSemantics.Satisfiable targetSignature [.base, .fresh] := by
  simpa [sourceState, targetState] using
    freshSymbolTransformation.satisfiable_iff

def oneStepTrace : SignatureChangingTrace demoSemantics
    sourceState targetState :=
  .step freshSymbolTransformation (.refl targetState)

theorem trace_preserves_satisfiability :
    demoSemantics.Satisfiable sourceSignature [.base] <->
      demoSemantics.Satisfiable targetSignature [.base, .fresh] := by
  simpa [sourceState, targetState] using oneStepTrace.satisfiable_iff

/-! ### A status-indexed `.esa` service with a genuinely fresh symbol -/

def basePrincipal : PrincipalSymbolId := { kind := .functor, name := "p" }
def freshPrincipal : PrincipalSymbolId := { kind := .functor, name := "sk" }

inductive ExtensionFormula where
  | source
  | target
  | notSource
  | notTarget
  deriving DecidableEq, Repr

def ExtensionFormula.principalSymbols : ExtensionFormula -> Finset PrincipalSymbolId
  | .source | .notSource => [basePrincipal].toFinset
  | .target | .notTarget => [basePrincipal, freshPrincipal].toFinset

def LocalModel := PrincipalSymbolId -> Bool

def localSatisfies (model : LocalModel) : ExtensionFormula -> Prop
  | .source => model basePrincipal = true
  | .target => model basePrincipal = true /\ model freshPrincipal = true
  | .notSource => Not (model basePrincipal = true)
  | .notTarget => Not (model basePrincipal = true /\ model freshPrincipal = true)

def extensionLocalSemantics : ClassicalModelSemantics ExtensionFormula where
  Model := LocalModel
  satisfies := localSatisfies
  negate
    | .source => .notSource
    | .target => .notTarget
    | .notSource => .source
    | .notTarget => .target
  satisfies_negate := by
    intro model formula
    classical
    cases formula <;> simp [localSatisfies]

theorem source_target_local_equisatisfiable :
    extensionLocalSemantics.EquiSatisfiableRelation {
      parents := [.source]
      inferred := .target
    } := by
  constructor
  · intro _sourceSatisfiable
    refine ⟨fun _ => true, ?_⟩
    intro formula member
    simp only [List.mem_singleton] at member
    subst formula
    exact ⟨rfl, rfl⟩
  · intro _targetSatisfiable
    refine ⟨fun _ => true, ?_⟩
    intro formula member
    simp only [List.mem_singleton] at member
    subst formula
    rfl

def ExtensionModel (signature : Finset PrincipalSymbolId) : Type :=
  forall symbol : PrincipalSymbolId, symbol ∈ signature -> Bool

def indexedAtomTrue (signature : Finset PrincipalSymbolId)
    (model : ExtensionModel signature) (symbol : PrincipalSymbolId) : Prop :=
  exists membership : symbol ∈ signature, model symbol membership = true

def indexedSatisfies (signature : Finset PrincipalSymbolId)
    (model : ExtensionModel signature) : ExtensionFormula -> Prop
  | .source => indexedAtomTrue signature model basePrincipal
  | .target => indexedAtomTrue signature model basePrincipal /\
      indexedAtomTrue signature model freshPrincipal
  | .notSource => Not (indexedAtomTrue signature model basePrincipal)
  | .notTarget => Not (indexedAtomTrue signature model basePrincipal /\
      indexedAtomTrue signature model freshPrincipal)

def restrictExtensionModel {source target : Finset PrincipalSymbolId}
    (included : source ⊆ target) (model : ExtensionModel target) :
    ExtensionModel source :=
  fun symbol membership => model symbol (included membership)

theorem indexedAtomTrue_restrict
    {source target : Finset PrincipalSymbolId}
    (included : source ⊆ target) (model : ExtensionModel target)
    (symbol : PrincipalSymbolId) (membership : symbol ∈ source) :
    indexedAtomTrue source (restrictExtensionModel included model) symbol <->
      indexedAtomTrue target model symbol := by
  constructor
  · rintro ⟨sourceMembership, valueTrue⟩
    exact ⟨included sourceMembership, valueTrue⟩
  · rintro ⟨_targetMembership, valueTrue⟩
    refine ⟨membership, ?_⟩
    simpa [restrictExtensionModel] using valueTrue

def extensionIndexedSemantics :
    SignatureIndexedModelSemantics PrincipalSymbolId ExtensionFormula where
  symbols := ExtensionFormula.principalSymbols
  Model := ExtensionModel
  satisfies := indexedSatisfies
  restrict := restrictExtensionModel
  restrict_satisfies := by
    intro source target included model formula formulaInSource
    cases formula with
    | source =>
        apply indexedAtomTrue_restrict included model
        exact formulaInSource (by simp [ExtensionFormula.principalSymbols])
    | target =>
        apply and_congr
        · apply indexedAtomTrue_restrict included model
          exact formulaInSource (by simp [ExtensionFormula.principalSymbols])
        · apply indexedAtomTrue_restrict included model
          exact formulaInSource (by simp [ExtensionFormula.principalSymbols])
    | notSource =>
        apply not_congr
        apply indexedAtomTrue_restrict included model
        exact formulaInSource (by simp [ExtensionFormula.principalSymbols])
    | notTarget =>
        apply not_congr
        apply and_congr
        · apply indexedAtomTrue_restrict included model
          exact formulaInSource (by simp [ExtensionFormula.principalSymbols])
        · apply indexedAtomTrue_restrict included model
          exact formulaInSource (by simp [ExtensionFormula.principalSymbols])

inductive ExtensionRule where
  | introduceFresh
  deriving DecidableEq, Repr

def extensionTheoryEntryOriginB : NodeOrigin -> Bool
  | .input => true
  | .inferred .thm => true
  | .inferred .esa => true
  | _ => false

def extensionCalculus : Calculus ExtensionFormula ExtensionRule Unit where
  meaning := extensionLocalSemantics.commonStatusMeaning
  parentOriginsAccepted := fun _ _ origins =>
    origins.all extensionTheoryEntryOriginB
  ruleMetadataAccepted := fun _ metadata _ =>
    decide (metadata.status = .esa /\
      metadata.declaredAssumptions = ∅ /\
      metadata.dischargedAssumptions = ∅ /\
      metadata.introducedSymbols = [freshPrincipal])
  check := fun _ status parents _ conclusion =>
    decide (status = .esa /\ parents = [.source] /\ conclusion = .target)
  check_sound := by
    intro rule status parents evidence conclusion accepted
    have conditions := of_decide_eq_true accepted
    rcases conditions with ⟨rfl, rfl, rfl⟩
    exact source_target_local_equisatisfiable

def extensionService : Service ExtensionFormula ExtensionRule Unit where
  formulaSignature := {
    principalSymbols? := fun formula =>
      some formula.principalSymbols
  }
  calculus := extensionCalculus

def extensionSourceNode : SemanticNode ExtensionFormula := {
  name := "source-theory"
  role := .axiom
  origin := .input
  body := .source
  principalSymbols := [basePrincipal].toFinset
  openAssumptions := ∅
}

def extensionTargetNode : SemanticNode ExtensionFormula := {
  name := "fresh-theory"
  role := .plain
  origin := .inferred .esa
  body := .target
  principalSymbols := [basePrincipal, freshPrincipal].toFinset
  openAssumptions := ∅
}

def extensionSourceMetadata : MetadataState := {
  knownSymbols := [basePrincipal].toFinset
}

def extensionTargetMetadata : MetadataState := {
  knownSymbols := [basePrincipal, freshPrincipal].toFinset
}

def freshPrincipalRaw : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern :=
  .apply "sk" []

def extensionMetadata : RuleMetadata := {
  status := .esa
  assumptions := []
  newSymbols := [{
    introductionKind := "skolem"
    symbols := [{
      kind := .functor
      name := "sk"
      raw := freshPrincipalRaw
    }]
    rawSymbols := [freshPrincipalRaw]
    raw := freshPrincipalRaw
  }]
  rawItems := []
  ruleInfo := []
}

def extensionEvidence : OfficialEvidence Unit := {
  metadata := extensionMetadata
  calculus := ()
}

theorem extension_step_executes_exactly :
    checkStep? extensionService extensionSourceMetadata
      .introduceFresh [extensionSourceNode] extensionEvidence
      extensionTargetNode = some extensionTargetMetadata := by
  decide +kernel

theorem extension_step_is_sound :
    StepSound extensionService extensionSourceMetadata
      extensionTargetMetadata .introduceFresh [extensionSourceNode]
      extensionEvidence extensionTargetNode :=
  checkStep?_sound extensionService extensionSourceMetadata
    extensionTargetMetadata .introduceFresh [extensionSourceNode]
    extensionEvidence extensionTargetNode extension_step_executes_exactly

def extendFreshPrincipalModel
    {source target : Finset PrincipalSymbolId}
    (sourceModel : ExtensionModel source) : ExtensionModel target :=
  fun symbol _targetMembership =>
    if membership : symbol ∈ source then sourceModel symbol membership else true

theorem restrict_extendFreshPrincipalModel
    {source target : Finset PrincipalSymbolId}
    (included : source ⊆ target) (sourceModel : ExtensionModel source) :
    restrictExtensionModel included
      (extendFreshPrincipalModel (target := target) sourceModel) = sourceModel := by
  funext symbol membership
  simp [restrictExtensionModel, extendFreshPrincipalModel, membership]

def extensionTransformation
    (source target : Finset PrincipalSymbolId)
    (baseInSource : basePrincipal ∈ source)
    (freshNotInSource : freshPrincipal ∉ source)
    (targetExact :
      target = source ∪ [basePrincipal, freshPrincipal].toFinset) :
    SignatureChangingTransformation extensionIndexedSemantics
      { signature := source, theory := [.source] }
      { signature := target, theory := [.target] } where
  delta := {
    introduced := [freshPrincipal]
    introduced_nodup := by simp
    introduced_fresh := by
      simp [freshNotInSource]
    target_eq := by
      rw [targetExact]
      ext symbol
      simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons]
      constructor
      · intro member
        rcases member with inSource | isBase | isFresh
        · exact Or.inl inSource
        · subst symbol
          exact Or.inl baseInSource
        · exact Or.inr isFresh
      · intro member
        rcases member with inSource | isFresh
        · exact Or.inl inSource
        · exact Or.inr (Or.inr isFresh)
  }
  source_well_formed := by
    intro formula member
    simp only [List.mem_singleton] at member
    subst formula
    change [basePrincipal].toFinset ⊆ source
    simp [baseInSource]
  target_well_formed := by
    intro formula member
    simp only [List.mem_singleton] at member
    subst formula
    change [basePrincipal, freshPrincipal].toFinset ⊆ target
    rw [targetExact]
    exact Finset.subset_union_right
  forward := by
    intro sourceModel sourceSatisfied
    have sourceSubsetTarget : source ⊆ target := by
      rw [targetExact]
      exact Finset.subset_union_left
    refine ⟨extendFreshPrincipalModel (source := source)
        (target := target) sourceModel,
      restrict_extendFreshPrincipalModel sourceSubsetTarget sourceModel, ?_⟩
    · intro formula member
      simp only [List.mem_singleton] at member
      subst formula
      constructor
      · rcases sourceSatisfied .source (by simp) with
          ⟨_sourceMembership, sourceTrue⟩
        refine ⟨?_, ?_⟩
        · rw [targetExact]
          simp [baseInSource]
        · simpa [extendFreshPrincipalModel, baseInSource] using sourceTrue
      · refine ⟨?_, ?_⟩
        · rw [targetExact]
          simp
        · simp [extendFreshPrincipalModel, freshNotInSource]
  backward := by
    intro targetModel targetSatisfied formula member
    simp only [List.mem_singleton] at member
    subst formula
    rcases targetSatisfied .target (by simp) with
      ⟨targetBaseTrue, _freshTrue⟩
    apply (indexedAtomTrue_restrict
      (by rw [targetExact]; exact Finset.subset_union_left)
      targetModel basePrincipal baseInSource).mpr
    exact targetBaseTrue

def extensionProfile : SignatureExtendingEsaProfile
    extensionLocalSemantics extensionIndexedSemantics extensionService where
  local_meaning_eq := rfl
  accepted_status := by
    intro rule status parents evidence conclusion accepted
    exact (of_decide_eq_true accepted).1
  parents_are_theory_entries := by
    intro rule status origins accepted origin member
    have acceptedOrigin := List.all_eq_true.mp accepted origin member
    cases origin with
    | input => trivial
    | inferred originStatus =>
        cases originStatus <;>
          simp [extensionTheoryEntryOriginB, TheoryEntryOrigin] at acceptedOrigin ⊢
  indexed_sound := by
    intro state next rule parents evidence conclusion normalized
      _normalizedEq parentSignatures conclusionSignature metadataAccepted
      nextEq ruleMetadataAccepted calculusAccepted
    have ruleMetadataConditions := of_decide_eq_true ruleMetadataAccepted
    have introducedExact :
        normalized.introducedSymbols = [freshPrincipal] :=
      ruleMetadataConditions.2.2.2
    have calculusConditions := of_decide_eq_true calculusAccepted
    have parentBodies :
        parents.map SemanticNode.body = [.source] :=
      calculusConditions.2.1
    have conclusionBody : conclusion.body = .target :=
      calculusConditions.2.2
    rcases (metadataAccepted_iff_conditions state parents conclusion normalized).mp
        metadataAccepted with
      ⟨_originExact, _roleAccepted, parentSymbolsSubset, _discharged,
        _declared, _open, _introducedNodup, introducedFresh,
        _conclusionDelta⟩
    cases parents with
    | nil => simp at parentBodies
    | cons parent rest =>
        cases rest with
        | cons other tail => simp at parentBodies
        | nil =>
            have parentBody : parent.body = .source := by
              simpa using parentBodies
            have parentSignature := parentSignatures parent (by simp)
            have parentSymbolsExact :
                parent.principalSymbols = [basePrincipal].toFinset := by
              simpa [NodeSignatureExact, extensionService,
                ExtensionFormula.principalSymbols, parentBody] using
                  parentSignature.symm
            have baseInState : basePrincipal ∈ state.knownSymbols := by
              have parentSubset :
                  parent.principalSymbols ⊆ state.knownSymbols := by
                simpa [parentSymbols] using parentSymbolsSubset
              apply parentSubset
              rw [parentSymbolsExact]
              simp
            have freshNotInState : freshPrincipal ∉ state.knownSymbols := by
              intro freshInState
              have freshInIntersection : freshPrincipal ∈
                  [freshPrincipal].toFinset ∩ state.knownSymbols := by
                simp [freshInState]
              rw [introducedExact] at introducedFresh
              have freshInEmpty : freshPrincipal ∈ (∅ : Finset PrincipalSymbolId) := by
                rw [← introducedFresh]
                exact freshInIntersection
              simp at freshInEmpty
            have conclusionSymbolsExact :
                conclusion.principalSymbols =
                  [basePrincipal, freshPrincipal].toFinset := by
              simpa [NodeSignatureExact, extensionService,
                ExtensionFormula.principalSymbols, conclusionBody] using
                  conclusionSignature.symm
            have targetExact : next.knownSymbols = state.knownSymbols ∪
                [basePrincipal, freshPrincipal].toFinset := by
              rw [nextEq]
              simp [nextMetadataState, conclusionSymbolsExact]
            have sourceTheoryExact : sourceTheoryState state [parent] = {
                signature := state.knownSymbols
                theory := [.source]
              } := by
              simp [sourceTheoryState, parentBody]
            have targetTheoryExact : targetTheoryState next conclusion = {
                signature := next.knownSymbols
                theory := [.target]
              } := by
              simp [targetTheoryState, conclusionBody]
            rw [sourceTheoryExact, targetTheoryExact]
            refine ⟨extensionTransformation state.knownSymbols next.knownSymbols
              baseInState freshNotInState targetExact, ?_⟩
            simpa [extensionTransformation] using introducedExact.symm

theorem accepted_extension_retains_indexed_model_transformation :
    CheckedSignatureExtendingEdge extensionLocalSemantics
      extensionIndexedSemantics extensionSourceMetadata extensionTargetMetadata
      [extensionSourceNode] extensionEvidence extensionTargetNode :=
  extensionProfile.checkedEdge extension_step_is_sound

def extensionMetadataWithoutFresh : RuleMetadata := {
  extensionMetadata with newSymbols := []
}

def extensionEvidenceWithoutFresh : OfficialEvidence Unit := {
  metadata := extensionMetadataWithoutFresh
  calculus := ()
}

theorem missing_new_symbols_record_is_rejected :
    checkStep? extensionService extensionSourceMetadata
      .introduceFresh [extensionSourceNode] extensionEvidenceWithoutFresh
      extensionTargetNode = none := by
  decide +kernel

theorem already_known_symbol_cannot_be_reintroduced :
    checkStep? extensionService extensionTargetMetadata
      .introduceFresh [extensionSourceNode] extensionEvidence
      extensionTargetNode = none := by
  decide +kernel

end Canary

#print axioms ExactSignatureDelta.source_subset
#print axioms SignatureChangingTransformation.satisfiable_iff
#print axioms SignatureChangingTrace.satisfiable_iff
#print axioms stepSound_hasExactSignatureDelta
#print axioms SignatureExtendingEsaProfile.checkedEdge
#print axioms Canary.existing_symbol_cannot_be_the_introduced_delta
#print axioms Canary.restrict_extendModel
#print axioms Canary.source_and_target_satisfiable_iff
#print axioms Canary.trace_preserves_satisfiability
#print axioms Canary.source_target_local_equisatisfiable
#print axioms Canary.indexedAtomTrue_restrict
#print axioms Canary.extension_step_executes_exactly
#print axioms Canary.extension_step_is_sound
#print axioms Canary.restrict_extendFreshPrincipalModel
#print axioms Canary.extensionTransformation
#print axioms Canary.extensionProfile
#print axioms Canary.accepted_extension_retains_indexed_model_transformation
#print axioms Canary.missing_new_symbols_record_is_rejected
#print axioms Canary.already_known_symbol_cannot_be_reintroduced

end Mettapedia.GSLT.LanguageDef.TptpOfficialSignatureExtensionComposition
