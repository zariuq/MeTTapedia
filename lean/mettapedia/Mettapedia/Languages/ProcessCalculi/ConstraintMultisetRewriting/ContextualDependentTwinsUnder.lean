import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpinesManyFormersRound

/-!
# Twins with convertible annotations

Decomposition produces **heterogeneous equations**: the two sides of a piece sit at annotations that
are equal only once earlier pieces are solved (Gundry and McBride's twins). When the two annotations
of an equation are already equal types but are different codes, for instance because they differ by
an η-expansion of a local, no instantiation makes them the same code, and every reading that compares
annotation codes leaves the equation alone.

Such an equation has exactly the solutions of its **homogeneous form**, the right side retyped at the
left annotation: a store equation compares its sides at its left annotation, and an equality of
types is kept by every substitution. Both forms have the same normal weight, since equal judged terms
have equal η-long normal forms.

The **twin round** is the ranked abstraction round, and when that round is stuck, the ranked
abstraction round again on the store whose convertible twins are made homogeneous (`collapse`).
Making twins homogeneous keeps the weight rank, so every committed step of the second round lowers
the rank of the original store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentTwinsUnder

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentRigidFormers ContextualDependentRank ContextualDependentSpinesMany
open ContextualDependentFragment ContextualDependentDecisiveFragment ContextualDependentConversionBudget

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The homogeneous form of an equation -/

/-- **The homogeneous form**: the right side retyped at the left annotation. -/
def retype {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (same : TypeEq S.R Θ.raw equation.1.1.code equation.2.1.code) : Equation (TotalTerm Θ) :=
  (equation.1, ⟨equation.1.1, ⟨equation.2.2.code, Typed.convType equation.2.2.typed same.symm⟩⟩)

/-- **The homogeneous form has exactly the solutions of the equation.** -/
theorem retype_solves {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (equation : Equation (TotalTerm Θ))
    (same : TypeEq S.R Θ.raw equation.1.1.code equation.2.1.code) :
    (frames S.levels).Solves σ (retype equation same) ↔ (frames S.levels).Solves σ equation := by
  rw [solves_raw, solves_raw]
  constructor
  · rintro ⟨_, held⟩
    exact ⟨reindex_typeEquality same σ, held⟩
  · rintro ⟨_, held⟩
    exact ⟨IsType.refl (equation.1.1.reindex σ).isType, held⟩

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra complete in
/-- **The homogeneous form has the normal weight of the equation.** -/
theorem retype_weight {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (same : TypeEq S.R Θ.raw equation.1.1.code equation.2.1.code) :
    equationWeight facts roots heads algebra rigid complete (retype equation same) =
      equationWeight facts roots heads algebra rigid complete equation := by
  unfold equationWeight
  congr 1
  exact sideWeight_of_equivalent facts roots heads algebra rigid complete
    ⟨same, .refl (Typed.convType equation.2.2.typed same.symm)⟩

/-! ## Making the twins of a store homogeneous -/

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
variable (reducer : ExecutableReduction.Reducer S.R)

/-- One equation: when its annotations are different codes that the bounded comparison of types finds
equal, its homogeneous form; otherwise the equation itself. -/
def collapseOne (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Equation (TotalTerm Θ) :=
  if equation.2.1.code = equation.1.1.code then equation
  else
    match Conversion.compareTypes facts roots heads algebra reducer fuel equation.1.1 equation.2.1 with
    | some same => retype equation same.down
    | none => equation

theorem collapseOne_solves (fuel : Nat) {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (equation : Equation (TotalTerm Θ)) :
    (frames S.levels).Solves σ (collapseOne facts roots heads algebra reducer fuel equation) ↔
      (frames S.levels).Solves σ equation := by
  unfold collapseOne
  split
  · exact Iff.rfl
  · split
    · exact retype_solves σ equation _
    · exact Iff.rfl

include rigid complete in
theorem collapseOne_weight (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    equationWeight facts roots heads algebra rigid complete (collapseOne facts roots heads algebra reducer fuel equation) =
      equationWeight facts roots heads algebra rigid complete equation := by
  unfold collapseOne
  split
  · rfl
  · split
    · exact retype_weight facts roots heads algebra rigid complete equation _
    · rfl

/-- The store with its convertible twins made homogeneous, with its solutions. -/
def collapsed (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    {store : EquationStore (TotalTerm Θ) // (frames S.levels).Equivalent problem store} :=
  ⟨problem.map (collapseOne facts roots heads algebra reducer fuel), fun _ σ => by
    simp only [Frames.Models, List.forall_mem_map]
    exact forall₂_congr fun equation _ => (collapseOne_solves facts roots heads algebra reducer fuel σ equation).symm⟩

/-- **Making the twins homogeneous**, as an update with exactly the store's solutions. -/
def collapse (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Update S.levels problem :=
  (Update.pending S.levels (collapsed facts roots heads algebra reducer fuel problem).val).rephrase
    (collapsed facts roots heads algebra reducer fuel problem).property

theorem collapse_remaining (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    (collapse facts roots heads algebra reducer fuel problem).remaining =
      problem.map (collapseOne facts roots heads algebra reducer fuel) := rfl

include rigid complete in
/-- **Making the twins homogeneous keeps the normal weight.** -/
theorem collapse_weight (fuel : Nat) {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ),
      storeWeight facts roots heads algebra rigid complete
          (problem.map (collapseOne facts roots heads algebra reducer fuel)) =
        storeWeight facts roots heads algebra rigid complete problem
  | [] => rfl
  | equation :: rest => by
      simp only [List.map_cons, storeWeight]
      rw [collapseOne_weight facts roots heads algebra rigid complete reducer fuel equation,
        collapse_weight fuel rest]

include rigid complete in
theorem collapse_rank (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    weightRank facts roots heads algebra rigid complete (collapse facts roots heads algebra reducer fuel problem).remaining =
      weightRank facts roots heads algebra rigid complete problem := by
  change (Θ.arity, storeWeight facts roots heads algebra rigid complete
    (problem.map (collapseOne facts roots heads algebra reducer fuel))) = (Θ.arity, _)
  rw [collapse_weight facts roots heads algebra rigid complete reducer fuel problem]

/-! ## The twin round -/

variable [DecidableRel S.R.cumulative]
variable (declared : DeclaredTypesFormed S.R) (choices : ExecutableChecking.HeadChoices S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- A round of the store with homogeneous twins, read as a round of the original store. -/
def liftCollapsed {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (collapsedUpdate : Update S.levels problem)
    (keeps : weightRank facts roots heads algebra rigid complete collapsedUpdate.remaining =
      weightRank facts roots heads algebra rigid complete problem)
    (round : Round S.levels (weightRank facts roots heads algebra rigid complete) collapsedUpdate.remaining) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match round with
  | .progress update smaller => .progress (collapsedUpdate.then update) (keeps ▸ smaller)
  | .refuted absent => .refuted fun solvable => absent (collapsedUpdate.solvable_iff.mp solvable)
  | .stuck => .stuck

/-- The ranked abstraction round on the store with homogeneous twins. -/
def twinRest (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  liftCollapsed facts roots heads algebra rigid complete (collapse facts roots heads algebra reducer fuel problem)
    (collapse_rank facts roots heads algebra rigid complete reducer fuel problem)
    (anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel (collapse facts roots heads algebra reducer fuel problem).remaining)

/-- **One twin round**: the ranked abstraction round; when it is stuck, the same round on the store whose
convertible twins are homogeneous. -/
def twinRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck => twinRest facts roots heads algebra rigid complete reducer declared choices root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem
  | other => other

/-- **The twin family**, at the weight rank. -/
noncomputable def twinFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := twinRound facts roots heads algebra rigid complete reducer declared choices root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

omit [DecidableRel S.R.cumulative] in
include stable in
theorem collapseOne_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel => collapseOne facts roots heads algebra reducer fuel equation := by
  unfold collapseOne
  by_cases same : equation.2.1.code = equation.1.1.code
  · simp only [same, if_true]
    exact EventuallyConst.const _
  · simp only [same, if_false]
    exact EventuallyConst.comp
      (fun found : Option (PLift (TypeEq S.R Θ.raw equation.1.1.code equation.2.1.code)) =>
        match found with
        | some same => retype equation same.down
        | none => equation)
      (compareTypes_const facts roots heads algebra reducer stable equation.1.1 equation.2.1)

omit [DecidableRel S.R.cumulative] in
include stable in
theorem map_collapseOne_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ),
      EventuallyConst fun fuel => problem.map (collapseOne facts roots heads algebra reducer fuel)
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.comp (fun pair : Equation (TotalTerm Θ) × EquationStore (TotalTerm Θ) => pair.1 :: pair.2)
        (EventuallyConst.pair (collapseOne_const facts roots heads algebra reducer stable equation)
          (map_collapseOne_const rest))

omit [DecidableRel S.R.cumulative] in
include stable in
theorem collapsed_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => collapsed facts roots heads algebra reducer fuel problem :=
  EventuallyConst.of_injective (g := Subtype.val) Subtype.val_injective
    (map_collapseOne_const facts roots heads algebra reducer stable problem)

/-- The view of a lifted round. -/
def liftView {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (collapsedUpdate : Update S.levels problem) :
    Option (Option (Update S.levels collapsedUpdate.remaining)) → Option (Option (Update S.levels problem))
  | some (some update) => some (some (collapsedUpdate.then update))
  | some none => some none
  | none => none

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
theorem liftCollapsed_view {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (collapsedUpdate : Update S.levels problem)
    (keeps : weightRank facts roots heads algebra rigid complete collapsedUpdate.remaining =
      weightRank facts roots heads algebra rigid complete problem)
    (round : Round S.levels (weightRank facts roots heads algebra rigid complete) collapsedUpdate.remaining) :
    roundView (liftCollapsed facts roots heads algebra rigid complete collapsedUpdate keeps round) =
      liftView collapsedUpdate (roundView round) := by
  cases round <;> rfl

/-- The update of a collapsed store, read from its store and solutions. -/
def collapseOf {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (store : {store : EquationStore (TotalTerm Θ) // (frames S.levels).Equivalent problem store}) :
    Update S.levels problem :=
  (Update.pending S.levels store.val).rephrase store.property

include stable in
theorem twinRest_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => twinRest facts roots heads algebra rigid complete reducer declared choices root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (g := fun fuel =>
      liftView (collapseOf (collapsed facts roots heads algebra reducer fuel problem))
        (roundView (anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel
          (collapseOf (collapsed facts roots heads algebra reducer fuel problem)).remaining)))
    (fun fuel => liftCollapsed_view facts roots heads algebra rigid complete _ _ _) ?_
  exact EventuallyConst.dep (h := fun fuel => collapsed facts roots heads algebra reducer fuel problem)
    (k := fun fuel store => liftView (collapseOf store)
      (roundView (anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete fuel (collapseOf store).remaining)))
    (collapsed_const facts roots heads algebra reducer stable problem)
    (fun store => EventuallyConst.comp (fun round => liftView (collapseOf store) (roundView round))
      (anyRound_const facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete stable (collapseOf store).remaining))

theorem twinRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (twinRound facts roots heads algebra rigid complete reducer declared choices root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem) =
      (roundView (anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (roundView (twinRest facts roots heads algebra rigid complete reducer declared choices root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)) := by
  unfold twinRound
  cases anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem <;> rfl

include stable in
/-- **The twin round is eventually constant on every store.** -/
theorem twinRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => twinRound facts roots heads algebra rigid complete reducer declared choices root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => twinRound_view facts roots heads algebra rigid complete reducer declared
    choices root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (anyRound_const facts roots heads algebra rigid complete declared choices reducer
        root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (EventuallyConst.comp roundView (twinRest_const facts roots heads algebra rigid complete reducer declared choices
        root normalizes certifyNormal headTypingUnique rootComplete stable problem)))

include stable in
/-- **The twin family settles** on every class of stores on which, at each nonempty store and from some
budget on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def twinSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        twinRound facts roots heads algebra rigid complete reducer declared choices root normalizes certifyNormal
            headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          twinRound facts roots heads algebra rigid complete reducer declared choices root normalizes certifyNormal
              headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (twinFamily facts roots heads algebra rigid complete reducer declared choices root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => twinRound_const facts roots heads algebra rigid complete reducer declared choices
    root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentTwinsUnder
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
