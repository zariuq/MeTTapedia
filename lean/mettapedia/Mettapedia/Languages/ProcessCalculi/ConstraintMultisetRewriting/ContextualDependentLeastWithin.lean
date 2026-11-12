import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentLeastAnnotation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUniverseInjectiveSigma

/-!
# The least annotation of an equation, through the components of Σ types

`ContextualDependentEtaDepth.lowerUpdate` lowers the universe at the end of a telescope of Π types. An annotation
can also be written above a declaration at a component of a Σ type. This module reads an equation at a smaller
annotation along `ContextualDependentUniverseInjective.LowersWithin`, which reaches those positions.

* `LoweredWithin`: a reading of an equation at a smaller annotation; `LoweredWithin.solves` (the equation at the
  smaller annotation has exactly the solutions of the equation), `LoweredWithin.weight` (and its normal weight);
* `lowerCodes`: **every** lowering of one universe position of an annotation to a candidate universe, through
  codomains of Π types and both components of Σ types; `lowerAtWithin` takes the first that is formed and against
  which both sides check; `lowerFirstWithin` tries the candidate universes, least first;
* `lowerMany`: the reading repeated, one position at a time, until no candidate lowers or as many times as the
  annotation has universe positions (`sortPositions`). Different positions can need different universes, so one
  position is lowered at a time;
* `lowerWithinUpdate`: the store with every equation read this way, as an update with exactly the store's
  solutions. It keeps the weight rank (`lowerWithinUpdate_rank`) and the permuted Miller class
  (`lowerWithinUpdate_keeps`), and it is eventually constant in the budget (`lowerWithinUpdate_const`).

That the repetition reaches an annotation no candidate lowers further is not proved; the statements above hold for
every number of repetitions.
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

/-- **A reading of an equation at a smaller annotation**: a formed type that lowers one universe position of the
left annotation, and both sides as terms of it. -/
structure LoweredWithin {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) where
  small : TypeOver Θ
  lowers : LowersWithin S.R small.code equation.1.1.code
  left : Term Θ small
  right : Term Θ small
  leftCode : left.code = equation.1.2.code
  rightCode : right.code = equation.2.2.code

/-- The equation at the smaller annotation. -/
def LoweredWithin.equation {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    (lowered : LoweredWithin equation) : Equation (TotalTerm Θ) :=
  (⟨lowered.small, lowered.left⟩, ⟨lowered.small, lowered.right⟩)

section Semantics

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **The equation at the smaller annotation has exactly the solutions of the equation**, when the equation is
homogeneous. -/
theorem LoweredWithin.solves {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) {equation : Equation (TotalTerm Θ)}
    (lowered : LoweredWithin equation) (homogeneous : equation.2.1.code = equation.1.1.code) :
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
      lowered.lowers.reflects facts roots heads algebra rigid complete σ.substitution Δ.formed typedLeft typedRight
        held⟩

include facts roots heads algebra rigid complete in
/-- **A term has the same normal weight at the smaller type and at the larger.** -/
theorem sideWeight_lowerWithin {Θ : Context S.R} (small large : TypeOver Θ)
    (lowers : LowersWithin S.R small.code large.code)
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
theorem LoweredWithin.weight {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    (lowered : LoweredWithin equation) (homogeneous : equation.2.1.code = equation.1.1.code) :
    equationWeight facts roots heads algebra rigid complete lowered.equation =
      equationWeight facts roots heads algebra rigid complete equation := by
  have right : LowersWithin S.R lowered.small.code equation.2.1.code := by
    rw [homogeneous]
    exact lowered.lowers
  unfold equationWeight
  congr 1
  · exact sideWeight_lowerWithin facts roots heads algebra rigid complete lowered.small equation.1.1 lowered.lowers
      lowered.left equation.1.2 lowered.leftCode
  · exact sideWeight_lowerWithin facts roots heads algebra rigid complete lowered.small equation.2.1 right
      lowered.right equation.2.2 lowered.rightCode

/-- A reading at a smaller annotation keeps the codes of the sides, hence Miller sides. -/
theorem LoweredWithin.sides {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (lowered : LoweredWithin equation)
    (sides : FragmentSidesMiller equation) : FragmentSidesMiller lowered.equation := by
  have left : lowered.equation.1.2.code = equation.1.2.code := lowered.leftCode
  have right : lowered.equation.2.2.code = equation.2.2.code := lowered.rightCode
  unfold FragmentSidesMiller
  rw [left, right]
  exact sides

/-- A reading at a smaller annotation is homogeneous, hence stratified. -/
theorem LoweredWithin.stratified {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    (lowered : LoweredWithin equation) (before : EquationStore (TotalTerm Θ)) :
    StratifiedAt S.levels before lowered.equation := by
  intro Δ σ _
  exact IsType.refl (lowered.small.reindex σ).isType

end Semantics

/-! ## The executable search -/

/-- The number of universe positions of an annotation that the reading can lower. -/
def sortPositions : {n : Nat} → Tm Head n → Nat
  | _, .head _ => 1
  | _, .pi _ B => sortPositions B
  | _, .sigma A B => sortPositions A + sortPositions B
  | _, _ => 0

section Search

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]

/-- **Every lowering of one universe position to the universe `u`**, through codomains of Π types and both
components of Σ types. -/
def lowerCodes (u : Head) :
    {n : Nat} → (large : Tm Head n) → List {small : Tm Head n // LowersWithin S.R small large}
  | _, .head v =>
      if allowed : S.R.isUniverse u ∧ S.R.isUniverse v ∧ S.R.cumulative u v ∧ u ≠ v then
        [⟨.head u, .sort allowed.1 allowed.2.1 allowed.2.2.1⟩]
      else []
  | _, .pi A B => (lowerCodes u B).map fun small => ⟨.pi A small.1, .pi small.2⟩
  | _, .sigma A B =>
      ((lowerCodes u A).map fun small => ⟨.sigma small.1 B, .sigmaFirst small.2⟩) ++
        ((lowerCodes u B).map fun small => ⟨.sigma A small.1, .sigmaSecond small.2⟩)
  | _, _ => []

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- **An equation read at one lowered annotation**, when the annotation is formed and both sides check against
it. -/
def lowerWith (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (small : {small : Tm Head Θ.arity // LowersWithin S.R small equation.1.1.code}) :
    Option (LoweredWithin equation) :=
  match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ small.1 with
  | none => none
  | some type =>
      match checkAt facts roots heads algebra declared choices reducer fuel type.1 equation.1.2.code,
          checkAt facts roots heads algebra declared choices reducer fuel type.1 equation.2.2.code with
      | some left, some right =>
          some ⟨type.1, by rw [type.2]; exact small.2, left.1, right.1, left.2, right.2⟩
      | _, _ => none

/-- The first of a list of lowered annotations at which the equation can be read. -/
def lowerAmong (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    List {small : Tm Head Θ.arity // LowersWithin S.R small equation.1.1.code} → Option (LoweredWithin equation)
  | [] => none
  | small :: rest =>
      (lowerWith facts roots heads algebra declared choices reducer fuel equation small).orElse fun _ =>
        lowerAmong fuel equation rest

/-- **An equation read with one universe position lowered to `u`**: the first position at which that is formed
and both sides check. -/
def lowerAtWithin (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (u : Head) :
    Option (LoweredWithin equation) :=
  lowerAmong facts roots heads algebra declared choices reducer fuel equation
    (lowerCodes (S := S) u equation.1.1.code)

/-- The first candidate universe to which a universe position of the equation's annotation can be lowered. -/
def lowerFirstWithin (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    List Head → Option (LoweredWithin equation)
  | [] => none
  | u :: rest =>
      (lowerAtWithin facts roots heads algebra declared choices reducer fuel equation u).orElse fun _ =>
        lowerFirstWithin fuel equation rest

/-- **The reading repeated**: one universe position lowered at a time, candidates least first, until no candidate
lowers or `steps` times. -/
def lowerMany (candidates : List Head) (fuel : Nat) :
    Nat → {Θ : Context S.R} → Equation (TotalTerm Θ) → Equation (TotalTerm Θ)
  | 0, _, equation => equation
  | steps + 1, _, equation =>
      match lowerFirstWithin facts roots heads algebra declared choices reducer fuel equation candidates with
      | none => equation
      | some lowered => lowerMany candidates fuel steps lowered.equation

theorem lowerMany_succ (candidates : List Head) (fuel steps : Nat) {Θ : Context S.R}
    (equation : Equation (TotalTerm Θ)) :
    lowerMany facts roots heads algebra declared choices reducer candidates fuel (steps + 1) equation =
      match lowerFirstWithin facts roots heads algebra declared choices reducer fuel equation candidates with
      | none => equation
      | some lowered =>
          lowerMany facts roots heads algebra declared choices reducer candidates fuel steps lowered.equation :=
  rfl

include rigid complete in
theorem lowerMany_solves (candidates : List Head) (fuel : Nat) {Δ : Context S.R} :
    ∀ (steps : Nat) {Θ : Context S.R} (σ : Δ ⟶ Θ) (equation : Equation (TotalTerm Θ)),
      equation.2.1.code = equation.1.1.code →
      ((frames S.levels).Solves σ
          (lowerMany facts roots heads algebra declared choices reducer candidates fuel steps equation) ↔
        (frames S.levels).Solves σ equation)
  | 0, _, _, _, _ => Iff.rfl
  | steps + 1, _, σ, equation, homogeneous => by
      rw [lowerMany_succ]
      split
      · exact Iff.rfl
      · rename_i lowered _
        exact (lowerMany_solves candidates fuel steps σ lowered.equation rfl).trans
          (lowered.solves facts roots heads algebra rigid complete σ homogeneous)

include rigid complete in
theorem lowerMany_weight (candidates : List Head) (fuel : Nat) :
    ∀ (steps : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)),
      equation.2.1.code = equation.1.1.code →
      equationWeight facts roots heads algebra rigid complete
          (lowerMany facts roots heads algebra declared choices reducer candidates fuel steps equation) =
        equationWeight facts roots heads algebra rigid complete equation
  | 0, _, _, _ => rfl
  | steps + 1, _, equation, homogeneous => by
      rw [lowerMany_succ]
      split
      · rfl
      · rename_i lowered _
        exact (lowerMany_weight candidates fuel steps lowered.equation rfl).trans
          (lowered.weight facts roots heads algebra rigid complete homogeneous)

theorem lowerMany_sides (candidates : List Head) (fuel : Nat) :
    ∀ (steps : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)), FragmentSidesMiller equation →
      FragmentSidesMiller
        (lowerMany facts roots heads algebra declared choices reducer candidates fuel steps equation)
  | 0, _, _, sides => sides
  | steps + 1, _, equation, sides => by
      rw [lowerMany_succ]
      split
      · exact sides
      · rename_i lowered _
        exact lowerMany_sides candidates fuel steps lowered.equation (lowered.sides sides)

theorem lowerMany_stratified (candidates : List Head) (fuel : Nat) :
    ∀ (steps : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (before : EquationStore (TotalTerm Θ)),
      StratifiedAt S.levels before equation →
      StratifiedAt S.levels before
        (lowerMany facts roots heads algebra declared choices reducer candidates fuel steps equation)
  | 0, _, _, _, stratified => stratified
  | steps + 1, _, equation, before, stratified => by
      rw [lowerMany_succ]
      split
      · exact stratified
      · rename_i lowered _
        exact lowerMany_stratified candidates fuel steps lowered.equation before (lowered.stratified before)

/-- **One equation with every universe position of its annotation at its least candidate**; an equation that is
not homogeneous is left as it is. -/
def lowerOneWithin (candidates : List Head) (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Equation (TotalTerm Θ) :=
  if equation.2.1.code = equation.1.1.code then
    lowerMany facts roots heads algebra declared choices reducer candidates fuel
      (sortPositions equation.1.1.code) equation
  else equation

include rigid complete in
theorem lowerOneWithin_solves (candidates : List Head) (fuel : Nat) {Θ Δ : Context S.R} (σ : Δ ⟶ Θ)
    (equation : Equation (TotalTerm Θ)) :
    (frames S.levels).Solves σ
        (lowerOneWithin facts roots heads algebra declared choices reducer candidates fuel equation) ↔
      (frames S.levels).Solves σ equation := by
  unfold lowerOneWithin
  split
  · rename_i homogeneous
    exact lowerMany_solves facts roots heads algebra rigid complete declared choices reducer candidates fuel _ σ
      equation homogeneous
  · exact Iff.rfl

include rigid complete in
theorem lowerOneWithin_weight (candidates : List Head) (fuel : Nat) {Θ : Context S.R}
    (equation : Equation (TotalTerm Θ)) :
    equationWeight facts roots heads algebra rigid complete
        (lowerOneWithin facts roots heads algebra declared choices reducer candidates fuel equation) =
      equationWeight facts roots heads algebra rigid complete equation := by
  unfold lowerOneWithin
  split
  · rename_i homogeneous
    exact lowerMany_weight facts roots heads algebra rigid complete declared choices reducer candidates fuel _
      equation homogeneous
  · rfl

theorem lowerOneWithin_sides (candidates : List Head) (fuel : Nat) {Θ : Context S.R}
    (equation : Equation (TotalTerm Θ)) (sides : FragmentSidesMiller equation) :
    FragmentSidesMiller
      (lowerOneWithin facts roots heads algebra declared choices reducer candidates fuel equation) := by
  unfold lowerOneWithin
  split
  · exact lowerMany_sides facts roots heads algebra declared choices reducer candidates fuel _ equation sides
  · exact sides

theorem lowerOneWithin_stratified (candidates : List Head) (fuel : Nat) {Θ : Context S.R}
    (equation : Equation (TotalTerm Θ)) (before : EquationStore (TotalTerm Θ))
    (stratified : StratifiedAt S.levels before equation) :
    StratifiedAt S.levels before
      (lowerOneWithin facts roots heads algebra declared choices reducer candidates fuel equation) := by
  unfold lowerOneWithin
  split
  · exact lowerMany_stratified facts roots heads algebra declared choices reducer candidates fuel _ equation before
      stratified
  · exact stratified

/-! ## The store read this way -/

/-- The store with every equation read at its least annotation through components, with its solutions. -/
def loweredWithin (candidates : List Head) (fuel : Nat) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) :
    {store : EquationStore (TotalTerm Θ) // (frames S.levels).Equivalent problem store} :=
  ⟨problem.map (lowerOneWithin facts roots heads algebra declared choices reducer candidates fuel), fun _ σ => by
    simp only [Frames.Models, List.forall_mem_map]
    exact forall₂_congr fun equation _ =>
      (lowerOneWithin_solves facts roots heads algebra rigid complete declared choices reducer candidates fuel σ
        equation).symm⟩

/-- **The store at its least annotations through components**, as an update with exactly the store's
solutions. -/
def lowerWithinUpdate (candidates : List Head) (fuel : Nat) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) : Update S.levels problem :=
  collapseOf
    (loweredWithin facts roots heads algebra rigid complete declared choices reducer candidates fuel problem)

theorem lowerWithinUpdate_remaining (candidates : List Head) (fuel : Nat) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) :
    (lowerWithinUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel
        problem).remaining =
      problem.map (lowerOneWithin facts roots heads algebra declared choices reducer candidates fuel) := rfl

include rigid complete in
/-- The store read this way has the normal weight of the store. -/
theorem lowerWithin_weight (candidates : List Head) (fuel : Nat) {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ),
      storeWeight facts roots heads algebra rigid complete
          (problem.map (lowerOneWithin facts roots heads algebra declared choices reducer candidates fuel)) =
        storeWeight facts roots heads algebra rigid complete problem
  | [] => rfl
  | equation :: rest => by
      simp only [List.map_cons, storeWeight]
      rw [lowerOneWithin_weight facts roots heads algebra rigid complete declared choices reducer candidates fuel
          equation,
        lowerWithin_weight candidates fuel rest]

/-- **The update keeps the weight rank**: it is a reading of the store, not a step. -/
theorem lowerWithinUpdate_rank (candidates : List Head) (fuel : Nat) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) :
    weightRank facts roots heads algebra rigid complete
        (lowerWithinUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel
          problem).remaining =
      weightRank facts roots heads algebra rigid complete problem := by
  change (Θ.arity, storeWeight facts roots heads algebra rigid complete
    (problem.map (lowerOneWithin facts roots heads algebra declared choices reducer candidates fuel))) =
      (Θ.arity, _)
  rw [lowerWithin_weight facts roots heads algebra rigid complete declared choices reducer candidates fuel problem]

/-- **The store read this way stays in the permuted Miller class.** -/
theorem lowerWithinUpdate_keeps (candidates : List Head) (fuel : Nat) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (permuted : PermutedMiller S.levels problem) :
    PermutedMiller S.levels
      (lowerWithinUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel
        problem).remaining :=
  permuted.map _
    (fun equation _ σ =>
      lowerOneWithin_solves facts roots heads algebra rigid complete declared choices reducer candidates fuel σ
        equation)
    (fun equation _ sides =>
      lowerOneWithin_sides facts roots heads algebra declared choices reducer candidates fuel equation sides)
    (fun equation _ before stratified =>
      lowerOneWithin_stratified facts roots heads algebra declared choices reducer candidates fuel equation before
        stratified)

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- Reading at one lowered annotation is eventually constant: type formation and checking keep their results. -/
theorem lowerWith_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (small : {small : Tm Head Θ.arity // LowersWithin S.R small equation.1.1.code}) :
    EventuallyConst fun fuel => lowerWith facts roots heads algebra declared choices reducer fuel equation small := by
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
  unfold lowerWith
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [formSame _ _ fuel enough]) ?_
  split <;> try exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq (max (checkThreshold _ _ _) (checkThreshold _ _ _)) (fun fuel enough => by
    rw [checkSame _ _ _ fuel (le_of_max_le_left enough), checkSame _ _ _ fuel (le_of_max_le_right enough)]) ?_
  exact EventuallyConst.const _

include stable in
theorem lowerAmong_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    ∀ smalls : List {small : Tm Head Θ.arity // LowersWithin S.R small equation.1.1.code},
      EventuallyConst fun fuel =>
        lowerAmong facts roots heads algebra declared choices reducer fuel equation smalls
  | [] => EventuallyConst.const _
  | small :: rest =>
      EventuallyConst.of_eq (fun _ => rfl)
        (EventuallyConst.comp (fun pair : Option (LoweredWithin equation) × Option (LoweredWithin equation) =>
            pair.1.orElse fun _ => pair.2)
          (EventuallyConst.pair
            (lowerWith_const facts roots heads algebra declared choices reducer stable equation small)
            (lowerAmong_const equation rest)))

include stable in
theorem lowerFirstWithin_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    ∀ candidates : List Head, EventuallyConst fun fuel =>
      lowerFirstWithin facts roots heads algebra declared choices reducer fuel equation candidates
  | [] => EventuallyConst.const _
  | u :: rest =>
      EventuallyConst.of_eq (fun _ => rfl)
        (EventuallyConst.comp (fun pair : Option (LoweredWithin equation) × Option (LoweredWithin equation) =>
            pair.1.orElse fun _ => pair.2)
          (EventuallyConst.pair
            (lowerAmong_const facts roots heads algebra declared choices reducer stable equation
              (lowerCodes (S := S) u equation.1.1.code))
            (lowerFirstWithin_const equation rest)))

include stable in
theorem lowerMany_const (candidates : List Head) :
    ∀ (steps : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)), EventuallyConst fun fuel =>
      lowerMany facts roots heads algebra declared choices reducer candidates fuel steps equation
  | 0, _, _ => EventuallyConst.const _
  | steps + 1, Θ, equation =>
      EventuallyConst.of_eq (fun _ => rfl)
        (EventuallyConst.dep
          (h := fun fuel =>
            lowerFirstWithin facts roots heads algebra declared choices reducer fuel equation candidates)
          (k := fun fuel (found : Option (LoweredWithin equation)) =>
            match found with
            | none => equation
            | some lowered =>
                lowerMany facts roots heads algebra declared choices reducer candidates fuel steps lowered.equation)
          (lowerFirstWithin_const facts roots heads algebra declared choices reducer stable equation candidates)
          (fun found => by
            cases found with
            | none => exact EventuallyConst.const _
            | some lowered => exact lowerMany_const candidates steps lowered.equation))

include stable in
theorem lowerOneWithin_const (candidates : List Head) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      lowerOneWithin facts roots heads algebra declared choices reducer candidates fuel equation := by
  by_cases homogeneous : equation.2.1.code = equation.1.1.code
  · refine EventuallyConst.of_eq (fun fuel => ?_)
      (lowerMany_const facts roots heads algebra declared choices reducer stable candidates
        (sortPositions equation.1.1.code) equation)
    unfold lowerOneWithin
    rw [if_pos homogeneous]
  · refine EventuallyConst.of_eq (fun fuel => ?_) (EventuallyConst.const equation)
    unfold lowerOneWithin
    rw [if_neg homogeneous]

include stable in
theorem lowerWithinStore_const (candidates : List Head) {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      problem.map (lowerOneWithin facts roots heads algebra declared choices reducer candidates fuel)
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.of_eq (fun _ => rfl)
        (EventuallyConst.comp (fun pair : Equation (TotalTerm Θ) × EquationStore (TotalTerm Θ) => pair.1 :: pair.2)
          (EventuallyConst.pair
            (lowerOneWithin_const facts roots heads algebra declared choices reducer stable candidates equation)
            (lowerWithinStore_const candidates rest)))

include stable in
theorem loweredWithin_const (candidates : List Head) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      loweredWithin facts roots heads algebra rigid complete declared choices reducer candidates fuel problem := by
  obtain ⟨threshold, same⟩ :=
    lowerWithinStore_const facts roots heads algebra declared choices reducer stable candidates problem
  exact ⟨threshold, fun fuel enough => Subtype.ext (same fuel enough)⟩

include stable in
/-- **The update is eventually constant** in the budget. -/
theorem lowerWithinUpdate_const (candidates : List Head) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      lowerWithinUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel problem :=
  EventuallyConst.comp collapseOf
    (loweredWithin_const facts roots heads algebra rigid complete declared choices reducer stable candidates
      problem)

end Search

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
