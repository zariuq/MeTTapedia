import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUniverseInjective
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursBoundFamily

/-!
# The least annotation of an equation

An equation of the store compares its two sides at its left annotation. When the annotation is a telescope of Π
types ending in a universe, and both sides are terms of the same telescope ending in a smaller universe, the
equation at the smaller telescope has exactly the solutions of the equation (`Lowered.solves`): equality at the
larger type of two terms of the smaller type holds at the smaller
(`ContextualDependentUniverseInjective.Lowers.reflects`), and the converse is subsumption.

So the universe at the end of an annotation is presentation, as the form of the sides is. This module normalizes it:

* `Lowered`: a reading of an equation at a smaller annotation; `Lowered.equation`, `Lowered.solves`,
  `Lowered.weight` (the normal weight is kept, since an η-long normal form at the smaller type is one at the larger);
* `lowerCode`, `lowerAt`, `lowerFirst`, `lowerOne`: the executable search. For each candidate universe, least
  first, the annotation's telescope with that universe at its end is formed and both sides are checked against it;
  the first that succeeds is taken. Only homogeneous equations are read;
* `lowerUpdate`: the store with every equation at its least annotation among the candidates, as an update with
  exactly the store's solutions. It keeps the weight rank (`lowerUpdate_rank`) and the permuted Miller class
  (`lowerUpdate_keeps`), and it is eventually constant in the budget (`lowerUpdate_const`).

The update is a reading of the store, as the preparation is. It is not a step: it changes neither component of the
rank.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentDynamicFragment
open ContextualDependentMillerClosure ContextualDependentOpenedNormal
open ContextualDependentAcceptance4 ContextualDependentTwinsUnder
open ContextualDependentConstantHeads ContextualDependentCumulativeClosure ContextualDependentShortClosure
open ContextualDependentIntersectionGeneral ContextualDependentCoverageReadersHalf
open ContextualDependentRigidFormers ContextualDependentClosure ContextualDependentEtaLong
open ContextualDependentUniverseInjective
open ContextualDependentCumulative (checkAt checkAt_const)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## An equation read at a smaller annotation -/

/-- **A reading of an equation at a smaller annotation**: a formed type that lowers the left annotation, and both
sides as terms of it. -/
structure Lowered {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) where
  small : TypeOver Θ
  lowers : Lowers S.R small.code equation.1.1.code
  left : Term Θ small
  right : Term Θ small
  leftCode : left.code = equation.1.2.code
  rightCode : right.code = equation.2.2.code

/-- The equation at the smaller annotation. -/
def Lowered.equation {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (lowered : Lowered equation) :
    Equation (TotalTerm Θ) :=
  (⟨lowered.small, lowered.left⟩, ⟨lowered.small, lowered.right⟩)

section Semantics

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **The equation at the smaller annotation has exactly the solutions of the equation**, when the equation is
homogeneous. -/
theorem Lowered.solves {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) {equation : Equation (TotalTerm Θ)}
    (lowered : Lowered equation) (homogeneous : equation.2.1.code = equation.1.1.code) :
    (frames S.levels).Solves σ lowered.equation ↔ (frames S.levels).Solves σ equation := by
  have isSmall : IsType S.R Δ.raw (subst σ.substitution lowered.small.code) := (lowered.small.reindex σ).isType
  have isLarge : IsType S.R Δ.raw (subst σ.substitution equation.1.1.code) := (equation.1.1.reindex σ).isType
  have lowers := lowered.lowers.subst σ.substitution
  have typedLeft : Typed S.R Δ.raw (subst σ.substitution equation.1.2.code)
      (subst σ.substitution lowered.small.code) := by
    rw [← lowered.leftCode]
    exact lowered.left.typed.substitute σ.typed
  have typedRight : Typed S.R Δ.raw (subst σ.substitution equation.2.2.code)
      (subst σ.substitution lowered.small.code) := by
    rw [← lowered.rightCode]
    exact lowered.right.typed.substitute σ.typed
  rw [solves_raw, solves_raw]
  change (TypeEq S.R Δ.raw (subst σ.substitution lowered.small.code) (subst σ.substitution lowered.small.code) ∧
      Equal S.R Δ.raw (subst σ.substitution lowered.left.code) (subst σ.substitution lowered.right.code)
        (subst σ.substitution lowered.small.code)) ↔ _
  rw [lowered.leftCode, lowered.rightCode]
  constructor
  · rintro ⟨_, held⟩
    refine ⟨?_, .subEq held (lowers.usable isSmall isLarge)⟩
    rw [homogeneous]
    exact IsType.refl isLarge
  · rintro ⟨_, held⟩
    exact ⟨IsType.refl isSmall,
      lowers.reflects facts roots heads algebra rigid complete Δ.formed typedLeft typedRight held⟩

include facts roots heads algebra rigid complete in
/-- **A term has the same normal weight at the smaller type and at the larger.** -/
theorem sideWeight_lower {Θ : Context S.R} (small large : TypeOver Θ) (lowers : Lowers S.R small.code large.code)
    (lower : Term Θ small) (upper : Term Θ large) (same : lower.code = upper.code) :
    sideWeight facts roots heads algebra rigid complete ⟨small, lower⟩ =
      sideWeight facts roots heads algebra rigid complete ⟨large, upper⟩ := by
  have chosen := Classical.choose_spec (long_exists facts roots heads algebra rigid complete Θ.formed lower.typed)
  have normal : NormalForm S.R S.roles Θ.raw upper.code
      (Classical.choose (long_exists facts roots heads algebra rigid complete Θ.formed lower.typed)) large.code := by
    rw [← same]
    exact lowers.normalForm facts Θ.formed small.isType large.isType chosen
  rw [sideWeight_eq facts roots heads algebra rigid complete ⟨large, upper⟩ normal]
  rfl

include facts roots heads algebra rigid complete in
/-- **The equation at the smaller annotation has the normal weight of the equation.** -/
theorem Lowered.weight {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (lowered : Lowered equation)
    (homogeneous : equation.2.1.code = equation.1.1.code) :
    equationWeight facts roots heads algebra rigid complete lowered.equation =
      equationWeight facts roots heads algebra rigid complete equation := by
  have right : Lowers S.R lowered.small.code equation.2.1.code := by
    rw [homogeneous]
    exact lowered.lowers
  unfold equationWeight
  congr 1
  · exact sideWeight_lower facts roots heads algebra rigid complete lowered.small equation.1.1 lowered.lowers
      lowered.left equation.1.2 lowered.leftCode
  · exact sideWeight_lower facts roots heads algebra rigid complete lowered.small equation.2.1 right
      lowered.right equation.2.2 lowered.rightCode

/-- The equation at a found reading, or the equation itself. -/
def lowerOr {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (Lowered equation) → Equation (TotalTerm Θ)
  | some lowered => lowered.equation
  | none => equation

include facts roots heads algebra rigid complete in
theorem lowerOr_solves {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) {equation : Equation (TotalTerm Θ)}
    (homogeneous : equation.2.1.code = equation.1.1.code) (found : Option (Lowered equation)) :
    (frames S.levels).Solves σ (lowerOr equation found) ↔ (frames S.levels).Solves σ equation := by
  cases found with
  | none => exact Iff.rfl
  | some lowered => exact lowered.solves facts roots heads algebra rigid complete σ homogeneous

include facts roots heads algebra rigid complete in
theorem lowerOr_weight {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    (homogeneous : equation.2.1.code = equation.1.1.code) (found : Option (Lowered equation)) :
    equationWeight facts roots heads algebra rigid complete (lowerOr equation found) =
      equationWeight facts roots heads algebra rigid complete equation := by
  cases found with
  | none => rfl
  | some lowered => exact lowered.weight facts roots heads algebra rigid complete homogeneous

/-- A reading at a smaller annotation keeps the codes of the sides, hence Miller sides. -/
theorem lowerOr_sides {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (found : Option (Lowered equation))
    (sides : FragmentSidesMiller equation) : FragmentSidesMiller (lowerOr equation found) := by
  cases found with
  | none => exact sides
  | some lowered =>
      have left : (lowerOr equation (some lowered)).1.2.code = equation.1.2.code := lowered.leftCode
      have right : (lowerOr equation (some lowered)).2.2.code = equation.2.2.code := lowered.rightCode
      unfold FragmentSidesMiller
      rw [left, right]
      exact sides

/-- A reading at a smaller annotation is homogeneous, hence stratified. -/
theorem lowerOr_stratified {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (found : Option (Lowered equation))
    (before : EquationStore (TotalTerm Θ)) (stratified : StratifiedAt S.levels before equation) :
    StratifiedAt S.levels before (lowerOr equation found) := by
  cases found with
  | none => exact stratified
  | some lowered =>
      intro Δ σ _
      exact IsType.refl (lowered.small.reindex σ).isType

end Semantics

/-! ## The executable search -/

section Search

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]

/-- **The telescope with the universe at its end replaced by another universe below it.** -/
def lowerCode (u : Head) :
    {n : Nat} → (large : Tm Head n) → Option {small : Tm Head n // Lowers S.R small large}
  | _, .head v =>
      if allowed : S.R.isUniverse u ∧ S.R.isUniverse v ∧ S.R.cumulative u v ∧ u ≠ v then
        some ⟨.head u, .sort allowed.1 allowed.2.1 allowed.2.2.1⟩
      else none
  | _, .pi A B =>
      match lowerCode u B with
      | some small => some ⟨.pi A small.1, .pi small.2⟩
      | none => none
  | _, _ => none

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- **An equation read with the universe `u` at the end of its annotation**, when that lowers the annotation, the
lowered telescope is formed, and both sides check against it. -/
def lowerAt (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (u : Head) :
    Option (Lowered equation) :=
  match lowerCode (S := S) u equation.1.1.code with
  | none => none
  | some small =>
      match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ small.1 with
      | none => none
      | some type =>
          match checkAt facts roots heads algebra declared choices reducer fuel type.1 equation.1.2.code,
              checkAt facts roots heads algebra declared choices reducer fuel type.1 equation.2.2.code with
          | some left, some right =>
              some ⟨type.1, by rw [type.2]; exact small.2, left.1, right.1, left.2, right.2⟩
          | _, _ => none

/-- The first candidate universe at which the equation can be read. -/
def lowerFirst (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    List Head → Option (Lowered equation)
  | [] => none
  | u :: rest =>
      (lowerAt facts roots heads algebra declared choices reducer fuel equation u).orElse fun _ =>
        lowerFirst fuel equation rest

/-- **One equation at its least annotation among the candidates**, least first; an equation that is not
homogeneous, or that no candidate lowers, is left as it is. -/
def lowerOne (candidates : List Head) (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Equation (TotalTerm Θ) :=
  if equation.2.1.code = equation.1.1.code then
    lowerOr equation (lowerFirst facts roots heads algebra declared choices reducer fuel equation candidates)
  else equation

include rigid complete in
theorem lowerOne_solves (candidates : List Head) (fuel : Nat) {Θ Δ : Context S.R} (σ : Δ ⟶ Θ)
    (equation : Equation (TotalTerm Θ)) :
    (frames S.levels).Solves σ (lowerOne facts roots heads algebra declared choices reducer candidates fuel equation) ↔
      (frames S.levels).Solves σ equation := by
  unfold lowerOne
  split
  · rename_i homogeneous
    exact lowerOr_solves facts roots heads algebra rigid complete σ homogeneous _
  · exact Iff.rfl

include rigid complete in
theorem lowerOne_weight (candidates : List Head) (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    equationWeight facts roots heads algebra rigid complete
        (lowerOne facts roots heads algebra declared choices reducer candidates fuel equation) =
      equationWeight facts roots heads algebra rigid complete equation := by
  unfold lowerOne
  split
  · rename_i homogeneous
    exact lowerOr_weight facts roots heads algebra rigid complete homogeneous _
  · rfl

theorem lowerOne_sides (candidates : List Head) (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (sides : FragmentSidesMiller equation) :
    FragmentSidesMiller (lowerOne facts roots heads algebra declared choices reducer candidates fuel equation) := by
  unfold lowerOne
  split
  · exact lowerOr_sides _ sides
  · exact sides

theorem lowerOne_stratified (candidates : List Head) (fuel : Nat) {Θ : Context S.R}
    (equation : Equation (TotalTerm Θ)) (before : EquationStore (TotalTerm Θ))
    (stratified : StratifiedAt S.levels before equation) :
    StratifiedAt S.levels before
      (lowerOne facts roots heads algebra declared choices reducer candidates fuel equation) := by
  unfold lowerOne
  split
  · exact lowerOr_stratified _ before stratified
  · exact stratified

/-! ## The store at its least annotations -/

/-- The store with every equation at its least annotation among the candidates, with its solutions. -/
def lowered (candidates : List Head) (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    {store : EquationStore (TotalTerm Θ) // (frames S.levels).Equivalent problem store} :=
  ⟨problem.map (lowerOne facts roots heads algebra declared choices reducer candidates fuel), fun _ σ => by
    simp only [Frames.Models, List.forall_mem_map]
    exact forall₂_congr fun equation _ =>
      (lowerOne_solves facts roots heads algebra rigid complete declared choices reducer candidates fuel σ
        equation).symm⟩

/-- **The store at its least annotations**, as an update with exactly the store's solutions. -/
def lowerUpdate (candidates : List Head) (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Update S.levels problem :=
  collapseOf (lowered facts roots heads algebra rigid complete declared choices reducer candidates fuel problem)

theorem lowerUpdate_remaining (candidates : List Head) (fuel : Nat) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) :
    (lowerUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel problem).remaining =
      problem.map (lowerOne facts roots heads algebra declared choices reducer candidates fuel) := rfl

include rigid complete in
/-- **The store at its least annotations has the normal weight of the store.** -/
theorem lower_weight (candidates : List Head) (fuel : Nat) {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ),
      storeWeight facts roots heads algebra rigid complete
          (problem.map (lowerOne facts roots heads algebra declared choices reducer candidates fuel)) =
        storeWeight facts roots heads algebra rigid complete problem
  | [] => rfl
  | equation :: rest => by
      simp only [List.map_cons, storeWeight]
      rw [lowerOne_weight facts roots heads algebra rigid complete declared choices reducer candidates fuel equation,
        lower_weight candidates fuel rest]

/-- **The update keeps the weight rank**: it is a reading of the store, not a step. -/
theorem lowerUpdate_rank (candidates : List Head) (fuel : Nat) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) :
    weightRank facts roots heads algebra rigid complete
        (lowerUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel
          problem).remaining =
      weightRank facts roots heads algebra rigid complete problem := by
  change (Θ.arity, storeWeight facts roots heads algebra rigid complete
    (problem.map (lowerOne facts roots heads algebra declared choices reducer candidates fuel))) = (Θ.arity, _)
  rw [lower_weight facts roots heads algebra rigid complete declared choices reducer candidates fuel problem]

/-- **The store at its least annotations stays in the permuted Miller class.** -/
theorem lowerUpdate_keeps (candidates : List Head) (fuel : Nat) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (permuted : PermutedMiller S.levels problem) :
    PermutedMiller S.levels
      (lowerUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel
        problem).remaining :=
  permuted.map _
    (fun equation _ σ =>
      lowerOne_solves facts roots heads algebra rigid complete declared choices reducer candidates fuel σ equation)
    (fun equation _ sides =>
      lowerOne_sides facts roots heads algebra declared choices reducer candidates fuel equation sides)
    (fun equation _ before stratified =>
      lowerOne_stratified facts roots heads algebra declared choices reducer candidates fuel equation before
        stratified)

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- Reading at one candidate universe is eventually constant: type formation and checking keep their results. -/
theorem lowerAt_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (u : Head) :
    EventuallyConst fun fuel => lowerAt facts roots heads algebra declared choices reducer fuel equation u := by
  have forming : ∀ (Γ : Context S.R) (code : Tm Head Γ.arity), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ code =
        ContextualDependentPruning.formType facts roots heads algebra declared choices reducer threshold Γ code :=
    fun _ code => (formType_const facts roots heads algebra declared choices reducer stable code).spec
  have checking : ∀ (C : Context S.R) (type : TypeOver C) (code : Tm Head C.arity), ∃ threshold, ∀ fuel,
      threshold ≤ fuel →
        checkAt facts roots heads algebra declared choices reducer fuel type code =
          checkAt facts roots heads algebra declared choices reducer threshold type code :=
    fun _ type code => (checkAt_const facts roots heads algebra declared choices reducer stable type code).spec
  choose formAt formSame using forming
  choose checkThreshold checkSame using checking
  unfold lowerAt
  split <;> try exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [formSame _ _ fuel enough]) ?_
  split <;> try exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq (max (checkThreshold _ _ _) (checkThreshold _ _ _)) (fun fuel enough => by
    rw [checkSame _ _ _ fuel (le_of_max_le_left enough), checkSame _ _ _ fuel (le_of_max_le_right enough)]) ?_
  exact EventuallyConst.const _

include stable in
theorem lowerFirst_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    ∀ candidates : List Head, EventuallyConst fun fuel =>
      lowerFirst facts roots heads algebra declared choices reducer fuel equation candidates
  | [] => EventuallyConst.const _
  | u :: rest =>
      EventuallyConst.of_eq (fun _ => rfl)
        (EventuallyConst.comp (fun pair : Option (Lowered equation) × Option (Lowered equation) =>
            pair.1.orElse fun _ => pair.2)
          (EventuallyConst.pair
            (lowerAt_const facts roots heads algebra declared choices reducer stable equation u)
            (lowerFirst_const equation rest)))

include stable in
theorem lowerOne_const (candidates : List Head) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel => lowerOne facts roots heads algebra declared choices reducer candidates fuel equation := by
  by_cases homogeneous : equation.2.1.code = equation.1.1.code
  · refine EventuallyConst.of_eq (fun fuel => ?_)
      (EventuallyConst.comp (lowerOr equation)
        (lowerFirst_const facts roots heads algebra declared choices reducer stable equation candidates))
    unfold lowerOne
    rw [if_pos homogeneous]
  · refine EventuallyConst.of_eq (fun fuel => ?_) (EventuallyConst.const equation)
    unfold lowerOne
    rw [if_neg homogeneous]

include stable in
theorem lowerStore_const (candidates : List Head) {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      problem.map (lowerOne facts roots heads algebra declared choices reducer candidates fuel)
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.of_eq (fun _ => rfl)
        (EventuallyConst.comp (fun pair : Equation (TotalTerm Θ) × EquationStore (TotalTerm Θ) => pair.1 :: pair.2)
          (EventuallyConst.pair
            (lowerOne_const facts roots heads algebra declared choices reducer stable candidates equation)
            (lowerStore_const candidates rest)))

include stable in
theorem lowered_const (candidates : List Head) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      lowered facts roots heads algebra rigid complete declared choices reducer candidates fuel problem := by
  obtain ⟨threshold, same⟩ :=
    lowerStore_const facts roots heads algebra declared choices reducer stable candidates problem
  exact ⟨threshold, fun fuel enough => Subtype.ext (same fuel enough)⟩

include stable in
/-- **The update is eventually constant** in the budget. -/
theorem lowerUpdate_const (candidates : List Head) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      lowerUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel problem :=
  EventuallyConst.comp collapseOf
    (lowered_const facts roots heads algebra rigid complete declared choices reducer stable candidates problem)

end Search

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
