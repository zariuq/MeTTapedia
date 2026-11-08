import Mathlib.Data.List.Rotate
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralInPlaceRound

/-!
# Intersection anywhere in the store

The intersection rules read the **first** equation of the store. R86's in-place step reorders a store, and can put a
twin before the intersection it depends on (`ContextualDependentMillerClosure.ReorderControls`); then the first
equation is the twin, whose annotations differ, and no intersection rule fires.

The rule here tries in-place intersection, at every depth, on each rotation of the store in turn
(`anywhereRule`). A rotation is a permutation, so it keeps the solutions (`equivalent_perm`) and the weight
(`storeWeight_perm`), and a progress of the rotated store is a progress of the store, with the same answer and the same
site (`unrotate`).

* **The anywhere round** is the in-place round, then this rule when that round is stuck (`anywhereRound`), with the
  **anywhere family** at the weight rank. It makes the in-place round's move wherever that round moves
  (`anywhereRound_eq_of_inPlace`, `anywhere_run_of_inPlace`).
* It is eventually constant on every store (`anywhereRound_const`), and acceptance reduces to settling on a class as for
  the other families (`anywhereSettledOfConst`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersectionGeneral

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget
open ContextualDependentIntersection ContextualDependentDynamicFragment ContextualDependentInPlace

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Permutations of a store -/

section Permutations

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **A permutation keeps the weight of a store.** -/
theorem storeWeight_perm {Θ : Context S.R} {problem problem' : EquationStore (TotalTerm Θ)}
    (perm : problem.Perm problem') :
    storeWeight facts roots heads algebra rigid complete problem =
      storeWeight facts roots heads algebra rigid complete problem' := by
  induction perm with
  | nil => rfl
  | cons equation _ ih => simp only [storeWeight, ih]
  | swap first second rest => simp only [storeWeight]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **A permutation keeps the solutions of a store.** -/
theorem equivalent_perm {Θ : Context S.R} {problem problem' : EquationStore (TotalTerm Θ)}
    (perm : problem.Perm problem') : (frames S.levels).Equivalent problem problem' :=
  fun _ _ => ⟨fun solved equation member => solved equation (perm.symm.subset member),
    fun solved equation member => solved equation (perm.subset member)⟩

/-- **A sited progress of a rotation of the store is a sited progress of the store**, with the same answer and
residual store. -/
def unrotate {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (k : Nat)
    (found : SitedProgress facts roots heads algebra rigid complete (problem.rotate k)) :
    SitedProgress facts roots heads algebra rigid complete problem :=
  ⟨found.val.rephrase (equivalent_perm (List.rotate_perm problem k).symm), by
    have lower : ContextualDependentWorklist.Below
        (weightRank facts roots heads algebra rigid complete found.val.remaining)
        (Θ.arity, storeWeight facts roots heads algebra rigid complete (problem.rotate k)) := found.property.1
    rw [storeWeight_perm facts roots heads algebra rigid complete (List.rotate_perm problem k)] at lower
    exact lower,
    found.property.2⟩

theorem unrotate_val {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (k : Nat)
    (found : SitedProgress facts roots heads algebra rigid complete (problem.rotate k)) :
    (unrotate facts roots heads algebra rigid complete k found).val =
      found.val.rephrase (equivalent_perm (List.rotate_perm problem k).symm) := rfl

end Permutations

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

/-! ## The rule, the round, the family -/

/-- In-place intersection at every depth, on the rotations of the store in turn. -/
def anywhereSearch (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    List Nat → Option (SitedProgress facts roots heads algebra rigid complete problem)
  | [] => none
  | k :: rest =>
      match inPlaceIntersectSearch facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique fuel (problem.rotate k) (List.range Θ.arity) with
      | some found => some (unrotate facts roots heads algebra rigid complete k found)
      | none => anywhereSearch fuel problem rest

/-- **Intersection anywhere in the store**: every rotation after the first, every depth. -/
def anywhereRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (SitedProgress facts roots heads algebra rigid complete problem) :=
  anywhereSearch facts roots heads algebra rigid complete declared choices reducer root normalizes headTypingUnique
    fuel problem (List.range' 1 (problem.length - 1))

/-- **One anywhere round**: the in-place round; when it is stuck, intersection anywhere in the store. -/
def anywhereRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck =>
      match anywhereRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique fuel problem with
      | some found => .progress found.val found.property.1
      | none => .stuck
  | other => other

/-- **The anywhere family**, at the weight rank. -/
noncomputable def anywhereFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-! ## Conservativity over the in-place family -/

/-- **The anywhere round makes the in-place round's move wherever that round moves.** -/
theorem anywhereRound_eq_of_inPlace (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem =
      inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  unfold anywhereRound
  cases computed : inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the in-place family decides, the anywhere family decides with the same outcome.** -/
theorem anywhere_run_of_inPlace (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((inPlaceFamily facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds).Decided) :
    run ((anywhereFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds =
      run ((inPlaceFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun problem => anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun _ moving => anywhereRound_eq_of_inPlace facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete fuel moving)
    rounds _ decided

/-- **The anywhere round is not stuck where the anywhere rule fires.** -/
theorem anywhereRound_not_stuck_of_rule (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (anywhereRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem).isSome) :
    anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold anywhereRound
  cases inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp read
      rw [computed]
      exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem anywhereSearch_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    ∀ rotations : List Nat, EventuallyConst fun fuel =>
      anywhereSearch facts roots heads algebra rigid complete declared choices reducer root normalizes
        headTypingUnique fuel problem rotations
  | [] => EventuallyConst.const _
  | k :: rest => by
      obtain ⟨t₁, first⟩ := (inPlaceIntersectSearch_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes headTypingUnique stable (problem.rotate k) (List.range Θ.arity)).spec
      obtain ⟨t₂, later⟩ := (anywhereSearch_const problem rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [anywhereSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

theorem anywhereRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (sitedView facts roots heads algebra rigid complete (anywhereRule facts roots heads algebra rigid
          complete declared choices reducer root normalizes headTypingUnique fuel problem)) := by
  unfold anywhereRound
  cases inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      cases anywhereRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique fuel problem with
      | some found => rfl
      | none => rfl
  | progress update smaller => rfl
  | refuted absent => rfl

include stable in
/-- **The anywhere round is eventually constant on every store.** -/
theorem anywhereRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => anywhereRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => anywhereRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (inPlaceRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (EventuallyConst.comp (sitedView facts roots heads algebra rigid complete)
        (anywhereSearch_const facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique stable problem _)))

include stable in
/-- **The anywhere family settles** on every class of stores on which, at each nonempty store and from some budget on,
its round is not stuck and keeps every residual store in the class. -/
noncomputable def anywhereSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (anywhereFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => anywhereRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentIntersectionGeneral
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
