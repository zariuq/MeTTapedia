import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance4

/-!
# Closure of the cumulative round, layer by layer: the views and the lower layers

Every layer of the cumulative round has a **view** (`roundView`, `…_view`): the base layer's move, or else the moves of
its new rule, read through the update that prepared the store. So a class of stores is kept by a layer as soon as it is
kept by the base layer, by the preparation, and by the new rule (`ViewKeeps.or`, `ViewKeeps.prepared`,
`ViewKeeps.identity`, `ViewKeeps.found`). Refutations offer no update and keep every class (`ViewKeeps.refuted`).

This file proves that for an arbitrary class `holds` and the lower layers, which rank by size: R99's fragment round
(`fragmentRound_keeps`), the identity and Π decompositions, R86's in-place round, the rigid formers, η-expansion, the
occurs checks, the spine and deep decompositions, R107's recognition and the full occurs round
(`occursFullRound_keeps`). Each lemma states exactly which rule must keep the class.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCumulativeClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)

/-! ## Views that keep a class -/

/-- **Every update a view offers lands in the class.** -/
def ViewKeeps {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (view : Option (Option (Update S.levels problem))) : Prop :=
  ∀ update, view = some (some update) → holds update.remaining

/-- **A rule's outcome keeps the class**: every update it solves with lands in the class. -/
def FoundKeeps {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (found : Option (Found problem)) : Prop :=
  ∀ update smaller, found = some (.solved update smaller) → holds update.remaining

/-- **A layer keeps the class**: its view on every store of the class keeps it. -/
def LayerKeeps {rank : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Nat × Nat}
    (round : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)), Round S.levels rank problem) : Prop :=
  ∀ ⦃Θ : Context S.R⦄ (problem : EquationStore (TotalTerm Θ)), holds problem → ViewKeeps holds (roundView (round problem))

/-- **A rule keeps the class** on every store of it. -/
def RuleKeeps (rule : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)), Option (Found problem)) : Prop :=
  ∀ ⦃Θ : Context S.R⦄ (problem : EquationStore (TotalTerm Θ)), holds problem → FoundKeeps holds (rule problem)

/-- **An update of every store keeps the class.** -/
def UpdateKeeps (update : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)), Update S.levels problem) :
    Prop :=
  ∀ ⦃Θ : Context S.R⦄ (problem : EquationStore (TotalTerm Θ)), holds problem → holds (update problem).remaining

variable {holds}

theorem ViewKeeps.or {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {first second : Option (Option (Update S.levels problem))} (keepsFirst : ViewKeeps holds first)
    (keepsSecond : ViewKeeps holds second) : ViewKeeps holds (first.or second) := by
  intro update offered
  cases first with
  | some inner => exact keepsFirst update offered
  | none => exact keepsSecond update offered

theorem ViewKeeps.none {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} :
    ViewKeeps holds (Option.none : Option (Option (Update S.levels problem))) := fun _ offered => by cases offered

/-- **A refutation keeps every class.** -/
theorem ViewKeeps.refuted {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (decided : Bool) :
    ViewKeeps holds (if decided then some Option.none else Option.none :
      Option (Option (Update S.levels problem))) := by
  intro update offered
  cases decided <;> cases offered

/-- **A move on the prepared store, carried back through the preparation.** -/
theorem ViewKeeps.prepared {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {prepared : Update S.levels problem}
    {view : Option (Option (Update S.levels prepared.remaining))} (keeps : ViewKeeps holds view) :
    ViewKeeps holds (view.map (Option.map fun update => prepared.then update)) := by
  intro update offered
  cases view with
  | none => cases offered
  | some inner =>
      cases inner with
      | none => cases offered
      | some moved =>
          cases offered
          exact keeps moved rfl

theorem ViewKeeps.found {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {found : Option (Found problem)}
    (keeps : FoundKeeps holds found) : ViewKeeps holds (ContextualDependentFragment.foundView found) := by
  intro update offered
  cases found with
  | none => cases offered
  | some inner =>
      cases inner with
      | solved moved smaller =>
          have same : moved = update := Option.some.inj (Option.some.inj offered)
          subst same
          exact keeps moved smaller rfl
      | refuted absent => cases offered

theorem ViewKeeps.foundFiring {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {found : Option (Found problem)} (keeps : FoundKeeps holds found) :
    ViewKeeps holds (ContextualDependentPatternFiring.foundView found) := by
  intro update offered
  cases found with
  | none => cases offered
  | some inner =>
      cases inner with
      | solved moved smaller =>
          have same : moved = update := Option.some.inj (Option.some.inj offered)
          subst same
          exact keeps moved smaller rfl
      | refuted absent => cases offered

/-- **A committed rule on the prepared store, or else the rest.** -/
theorem ViewKeeps.identity {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {prepared : Update S.levels problem}
    {found : Option (Found prepared.remaining)} {otherwise : Option (Option (Update S.levels problem))}
    (keepsFound : FoundKeeps holds found) (keepsOtherwise : ViewKeeps holds otherwise) :
    ViewKeeps holds (identityView prepared found otherwise) := by
  intro update offered
  unfold identityView at offered
  split at offered
  · rename_i committed computed
    have inner : ViewKeeps holds (some committed : Option (Option (Update S.levels prepared.remaining))) :=
      fun update' same => ViewKeeps.found keepsFound update' (computed.trans same)
    rcases committed with _ | committed
    · cases offered
    · cases offered
      exact inner committed rfl
  · exact keepsOtherwise update offered

/-- **A layer that keeps the class keeps it at every move of its round.** -/
theorem roundKeeps_of_layer {rank : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Nat × Nat}
    {round : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)), Round S.levels rank problem}
    (keeps : LayerKeeps holds round) : ContextualDependentOpenedNormal.RoundKeeps holds round := by
  intro Θ problem update smaller held fired
  exact keeps problem held update (by rw [fired]; rfl)

/-! ## The lower layers -/

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- **Preparation keeps the class** at a budget. -/
def PrepareKeeps (fuel : Nat) : Prop :=
  UpdateKeeps holds fun problem => ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- **A round extended by one rule on the prepared store keeps the class**, when the base round, the preparation and
the rule do. -/
theorem extendRound_keeps
    (base : Nat → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) → Round S.levels size problem)
    (rule : Nat → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) → Option (Found problem)) (fuel : Nat)
    (prepared : PrepareKeeps (holds := holds) facts roots heads root rootComplete fuel)
    (keepsBase : LayerKeeps holds fun problem => base fuel problem)
    (keepsRule : RuleKeeps holds fun problem => rule fuel problem) :
    LayerKeeps holds fun problem =>
      ContextualDependentEtaExpansion.extendRound root rootComplete facts roots heads base rule fuel problem := by
  intro Θ problem held
  rw [ContextualDependentEtaExpansion.extendRound_view]
  exact (keepsBase problem held).or (ViewKeeps.prepared (ViewKeeps.found (keepsRule _ (prepared problem held))))

/-- **R99's fragment round keeps the class** where the decomposition round and the rotation keep it. -/
theorem fragmentRound_keeps (fuel : Nat) (prepared : PrepareKeeps (holds := holds) facts roots heads root rootComplete fuel)
    (decompose : LayerKeeps holds fun problem =>
      ContextualDependentRigidDecomposition.decomposeRound rigid facts complete roots heads algebra declared choices
        reducer root normalizes certifyNormal headTypingUnique fuel problem)
    (rotate : RuleKeeps holds fun problem =>
      ContextualDependentPermutation.rotateRule rigid complete facts roots heads algebra declared choices reducer root
        normalizes certifyNormal fuel problem) :
    LayerKeeps holds fun problem =>
      fragmentRound rigid facts complete roots heads algebra declared choices reducer root rootComplete normalizes
        certifyNormal headTypingUnique fuel problem := by
  intro Θ problem held
  rw [fragmentRound_view]
  exact ViewKeeps.prepared ((decompose _ (prepared problem held)).or (ViewKeeps.found (rotate _ (prepared problem held))))

/-- **The identity round keeps the class.** -/
theorem identityRound_keeps (fuel : Nat) (prepared : PrepareKeeps (holds := holds) facts roots heads root rootComplete fuel)
    (base : LayerKeeps holds fun problem =>
      fragmentRound rigid facts complete roots heads algebra declared choices reducer root rootComplete normalizes
        certifyNormal headTypingUnique fuel problem)
    (identity : RuleKeeps holds fun problem =>
      idDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        fuel problem) :
    LayerKeeps holds fun problem =>
      identityRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [identityRound_view]
  exact ViewKeeps.identity (identity _ (prepared problem held)) (base problem held)

/-- **The Π round keeps the class.** -/
theorem piRound_keeps (fuel : Nat) (prepared : PrepareKeeps (holds := holds) facts roots heads root rootComplete fuel)
    (base : LayerKeeps holds fun problem =>
      identityRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem)
    (pi : RuleKeeps holds fun problem =>
      piDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        fuel problem) :
    LayerKeeps holds fun problem =>
      piRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [piRound_view]
  exact ViewKeeps.identity (pi _ (prepared problem held)) (base problem held)

/-- **R86's in-place round keeps the class.** -/
theorem inPlaceRound_keeps (fuel : Nat) (prepared : PrepareKeeps (holds := holds) facts roots heads root rootComplete fuel)
    (base : LayerKeeps holds fun problem =>
      piRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem)
    (inPlace : RuleKeeps holds fun problem =>
      ContextualDependentInPlace.inPlaceRule facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal headTypingUnique fuel problem) :
    LayerKeeps holds fun problem =>
      ContextualDependentInPlace.inPlaceRound facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [ContextualDependentInPlace.inPlaceRound_view]
  exact (base problem held).or (ViewKeeps.prepared (ViewKeeps.found (inPlace _ (prepared problem held))))

/-- **The rigid-formers round keeps the class.** -/
theorem formersRound_keeps (fuel : Nat) (prepared : PrepareKeeps (holds := holds) facts roots heads root rootComplete fuel)
    (base : LayerKeeps holds fun problem =>
      ContextualDependentInPlace.inPlaceRound facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal headTypingUnique rootComplete fuel problem)
    (formers : RuleKeeps holds fun problem =>
      ContextualDependentRigidFormers.formerSearch facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal headTypingUnique fuel problem) :
    LayerKeeps holds fun problem =>
      ContextualDependentRigidFormers.formersRound facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [ContextualDependentRigidFormers.formersRound_view]
  exact (base problem held).or (ViewKeeps.prepared (ViewKeeps.found (formers _ (prepared problem held))))

/-- **The obligations of the lower layers**, rule by rule, at one budget: preparation, R99's decomposition round and
rotation, the identity and Π decompositions, R86's in-place rule, the rigid formers, η-expansion, the occurs check, the
spine and deep decompositions, R107's conversion pattern rule, and the full occurs check. -/
structure LowerObligations (fuel : Nat) : Prop where
  prepare : PrepareKeeps (holds := holds) facts roots heads root rootComplete fuel
  decompose : LayerKeeps holds fun problem =>
    ContextualDependentRigidDecomposition.decomposeRound rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique fuel problem
  rotate : RuleKeeps holds fun problem =>
    ContextualDependentPermutation.rotateRule rigid complete facts roots heads algebra declared choices reducer root
      normalizes certifyNormal fuel problem
  identity : RuleKeeps holds fun problem =>
    idDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
      fuel problem
  pi : RuleKeeps holds fun problem =>
    piDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
      fuel problem
  inPlace : RuleKeeps holds fun problem =>
    ContextualDependentInPlace.inPlaceRule facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique fuel problem
  formers : RuleKeeps holds fun problem =>
    ContextualDependentRigidFormers.formerSearch facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique fuel problem
  eta : RuleKeeps holds fun problem =>
    ContextualDependentEtaExpansion.etaSearch facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique fuel problem
  occurs : RuleKeeps holds fun problem =>
    ContextualDependentOccursCheck.occursSearch facts roots heads algebra rigid complete problem
  two : RuleKeeps holds fun problem =>
    ContextualDependentRigidFormers.twoSearch facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique fuel problem
  deep : RuleKeeps holds fun problem =>
    ContextualDependentRigidFormers.deepSearch facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique fuel problem
  pattern : RuleKeeps holds fun problem =>
    ContextualDependentRecognitionConversion.patternRuleConv facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal fuel problem
  occursFull : RuleKeeps holds fun problem =>
    ContextualDependentOccursFull.occursFullSearch facts roots heads algebra rigid complete problem

/-- **The full occurs round keeps the class** wherever its rules do. -/
theorem occursFullRound_keeps (fuel : Nat)
    (obligations : LowerObligations (holds := holds) facts roots heads algebra rigid complete declared choices reducer
      root normalizes certifyNormal headTypingUnique rootComplete fuel) :
    LayerKeeps holds fun problem =>
      ContextualDependentOccursFull.occursFullRound facts roots heads algebra rigid complete declared choices reducer
        root normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  have fragment := fragmentRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations.prepare obligations.decompose obligations.rotate
  have identity := identityRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations.prepare fragment obligations.identity
  have pi := piRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations.prepare identity obligations.pi
  have inPlace := inPlaceRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations.prepare pi obligations.inPlace
  have formers := formersRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations.prepare inPlace obligations.formers
  have eta := extendRound_keeps facts roots heads root rootComplete
    (fun fuel => ContextualDependentRigidFormers.formersRound facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal headTypingUnique rootComplete fuel)
    (fun fuel => ContextualDependentEtaExpansion.etaSearch facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal headTypingUnique fuel) fuel obligations.prepare formers obligations.eta
  have occurs := extendRound_keeps facts roots heads root rootComplete
    (fun fuel => ContextualDependentEtaExpansion.etaRound facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal headTypingUnique rootComplete fuel)
    (fun _ => ContextualDependentOccursCheck.occursSearch facts roots heads algebra rigid complete) fuel
    obligations.prepare eta obligations.occurs
  have two := extendRound_keeps facts roots heads root rootComplete
    (fun fuel => ContextualDependentOccursCheck.occursRound facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete fuel)
    (fun fuel => ContextualDependentRigidFormers.twoSearch facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal headTypingUnique fuel) fuel obligations.prepare occurs obligations.two
  have deep := extendRound_keeps facts roots heads root rootComplete
    (fun fuel => ContextualDependentRigidFormers.spineRound facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal headTypingUnique rootComplete fuel)
    (fun fuel => ContextualDependentRigidFormers.deepSearch facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal headTypingUnique fuel) fuel obligations.prepare two obligations.deep
  have recognition := extendRound_keeps facts roots heads root rootComplete
    (fun fuel => ContextualDependentRigidFormers.deepRound facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal headTypingUnique rootComplete fuel)
    (fun fuel => ContextualDependentRecognitionConversion.patternRuleConv facts roots heads algebra declared choices
      reducer rigid complete root normalizes certifyNormal fuel) fuel obligations.prepare deep obligations.pattern
  exact extendRound_keeps facts roots heads root rootComplete
    (fun fuel => ContextualDependentRecognitionConversion.recognitionRound facts roots heads algebra declared choices
      reducer rigid complete root normalizes certifyNormal headTypingUnique rootComplete fuel)
    (fun _ => ContextualDependentOccursFull.occursFullSearch facts roots heads algebra rigid complete) fuel
    obligations.prepare recognition obligations.occursFull

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
