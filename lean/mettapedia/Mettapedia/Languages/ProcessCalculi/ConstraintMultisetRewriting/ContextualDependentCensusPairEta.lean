import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantHeads

/-!
# A pair against a neutral term: η for Σ, by a certified re-expression

The census finds one shape that no rule of the heads round reads: under its abstractions, at a Σ
annotation, **a pair against a rigid neutral term**, a spine whose head is a bound local or a constant.
Every term of a Σ type equals the pair of its projections (η for Σ), so `(a, b) ≐ n` has exactly the
solutions of `(a, b) ≐ (fst n, snd n)`, which the pair decomposition reads. A spine of a metavariable is
not expanded: its projections are not Miller occurrences, and the pattern rule reads it.

The expansion is a **re-expression** of one side: a new code for it, accepted when the executable
checker types it at the side's annotation and the executable conversion finds it equal to the old
side. An accepted re-expression keeps the solutions of the equation exactly, since equality of judged
terms is kept by every substitution, and keeps its normal weight, since equal judged terms have equal
η-long normal forms. No step of the expansion is trusted: the checker and the converter certify it.

The **pairs round** is the heads round, and when that round is stuck, the heads round again on the
prepared store whose pair-against-neutral equations are expanded.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCensusPairEta

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentRigidFormers ContextualDependentRank ContextualDependentSpinesMany
open ContextualDependentFragment ContextualDependentDecisiveFragment ContextualDependentConversionBudget
open ContextualDependentTwinsUnder ContextualDependentConstantHeads

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The candidate code -/

/-- **The η-expansion of a side against a pair**, under the common abstractions: at a Σ annotation, a rigid
neutral side, a spine whose head is a bound local or a constant, becomes the pair of its projections. A
spine of a metavariable is left to the pattern rule: its projections are not Miller occurrences. -/
def pairEtaCode : {n : Nat} → Nat → Tm Head n → Tm Head n → Tm Head n → Option (Tm Head n)
  | _, depth, .pi _ T, .lam pairSide, .lam other => (pairEtaCode (depth + 1) T pairSide other).map .lam
  | _, depth, .sigma _ _, .pair _ _, other =>
      (fixedSkeleton depth other).map fun _ => .pair (.fst other) (.snd other)
  | _, _, _, _, _ => none

/-! ## Re-expressing one side -/

/-- A re-expression of the right side keeps the solutions of an equation. -/
theorem solves_right {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (left right right' : TotalTerm Θ)
    (same : (frames S.levels).E right right') :
    (frames S.levels).Solves σ (left, right') ↔ (frames S.levels).Solves σ (left, right) := by
  have moved := (frames S.levels).preserves σ same
  have equivalence := (frames S.levels).equivalence Δ
  constructor
  · intro solved
    exact equivalence.trans solved (equivalence.symm moved)
  · intro solved
    exact equivalence.trans solved moved

/-- A re-expression of the left side keeps the solutions of an equation. -/
theorem solves_left {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (left left' right : TotalTerm Θ)
    (same : (frames S.levels).E left left') :
    (frames S.levels).Solves σ (left', right) ↔ (frames S.levels).Solves σ (left, right) := by
  have moved := (frames S.levels).preserves σ same
  have equivalence := (frames S.levels).equivalence Δ
  constructor
  · intro solved
    exact equivalence.trans moved solved
  · intro solved
    exact equivalence.trans (equivalence.symm moved) solved

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- The comparison of a candidate code with a judged term, once the candidate is typed. -/
def reexpressWith (fuel : Nat) {Θ : Context S.R} (term : TotalTerm Θ) (code : Tm Head Θ.arity) :
    Option (ExecutableChecking.CheckResult S.R Θ.raw code term.1.code) →
      Option {other : TotalTerm Θ // (frames S.levels).E term other}
  | some checked =>
      (Conversion.compare facts roots heads algebra reducer fuel term ⟨term.1, ⟨code, CheckingAlgorithm.sound (S := S)
        facts roots heads algebra declared checked.down Θ.formed term.1.isType⟩⟩).map fun same => ⟨_, same.down⟩
  | none => none

/-- **A certified re-expression of a judged term**: the candidate code, typed by the executable checker
at the term's annotation, and found equal to the term by the executable conversion. -/
def reexpress (fuel : Nat) {Θ : Context S.R} (term : TotalTerm Θ) (code : Tm Head Θ.arity) :
    Option {other : TotalTerm Θ // (frames S.levels).E term other} :=
  reexpressWith facts roots heads algebra declared reducer fuel term code
    (ExecutableChecking.check S.R choices reducer fuel Θ.raw code term.1.code)

/-- **One equation, with a pair against a neutral side expanded**: the right side first, else the left. -/
def expandOne (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Equation (TotalTerm Θ) :=
  match (pairEtaCode 0 equation.1.1.code equation.1.2.code equation.2.2.code).bind
      (reexpress facts roots heads algebra declared choices reducer fuel equation.2) with
  | some right => (equation.1, right.val)
  | none =>
      match (pairEtaCode 0 equation.1.1.code equation.2.2.code equation.1.2.code).bind
          (reexpress facts roots heads algebra declared choices reducer fuel equation.1) with
      | some left => (left.val, equation.2)
      | none => equation

theorem expandOne_solves (fuel : Nat) {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (equation : Equation (TotalTerm Θ)) :
    (frames S.levels).Solves σ (expandOne facts roots heads algebra declared choices reducer fuel equation) ↔
      (frames S.levels).Solves σ equation := by
  unfold expandOne
  split
  · rename_i right _
    exact solves_right σ equation.1 equation.2 right.val right.property
  · split
    · rename_i left _
      exact solves_left σ equation.1 left.val equation.2 left.property
    · exact Iff.rfl

include rigid complete in
theorem expandOne_weight (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    equationWeight facts roots heads algebra rigid complete
        (expandOne facts roots heads algebra declared choices reducer fuel equation) =
      equationWeight facts roots heads algebra rigid complete equation := by
  unfold expandOne equationWeight
  split
  · rename_i right _
    rw [sideWeight_of_equivalent facts roots heads algebra rigid complete right.property]
  · split
    · rename_i left _
      rw [sideWeight_of_equivalent facts roots heads algebra rigid complete left.property]
    · rfl

/-- The store with its pair-against-neutral equations expanded, with its solutions. -/
def expanded (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    {store : EquationStore (TotalTerm Θ) // (frames S.levels).Equivalent problem store} :=
  ⟨problem.map (expandOne facts roots heads algebra declared choices reducer fuel), fun _ σ => by
    simp only [Frames.Models, List.forall_mem_map]
    exact forall₂_congr fun equation _ =>
      (expandOne_solves facts roots heads algebra declared choices reducer fuel σ equation).symm⟩

include rigid complete in
theorem expanded_weight (fuel : Nat) {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ),
      storeWeight facts roots heads algebra rigid complete (expanded facts roots heads algebra declared choices reducer
          fuel problem).val =
        storeWeight facts roots heads algebra rigid complete problem
  | [] => rfl
  | equation :: rest => by
      change storeWeight facts roots heads algebra rigid complete
          (expandOne facts roots heads algebra declared choices reducer fuel equation ::
            (expanded facts roots heads algebra declared choices reducer fuel rest).val) = _
      simp only [storeWeight]
      rw [expandOne_weight facts roots heads algebra rigid complete declared choices reducer fuel equation,
        expanded_weight fuel rest]

/-! ## The pairs round -/

variable (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- The prepared store with its pair-against-neutral equations expanded, as an update of the store. -/
def preparedExpanded (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Update S.levels problem :=
  (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).then
    (collapseOf (expanded facts roots heads algebra declared choices reducer fuel
      (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining))

include rigid complete in
theorem preparedExpanded_rank (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    weightRank facts roots heads algebra rigid complete
        (preparedExpanded facts roots heads algebra declared choices reducer root rootComplete fuel problem).remaining =
      weightRank facts roots heads algebra rigid complete problem := by
  change ((ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).target.arity,
      storeWeight facts roots heads algebra rigid complete (expanded facts roots heads algebra declared choices reducer
        fuel (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining).val) =
    (Θ.arity, storeWeight facts roots heads algebra rigid complete problem)
  rw [expanded_weight facts roots heads algebra rigid complete declared choices reducer fuel,
    prepare_weight facts roots heads algebra rigid complete root rootComplete fuel problem,
    prepare_arity facts roots heads root rootComplete fuel problem]

/-- The heads round on the prepared store with expanded pairs. -/
def pairsRest (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  liftCollapsed facts roots heads algebra rigid complete
    (preparedExpanded facts roots heads algebra declared choices reducer root rootComplete fuel problem)
    (preparedExpanded_rank facts roots heads algebra rigid complete declared choices reducer root rootComplete fuel
      problem)
    (headsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel
      (preparedExpanded facts roots heads algebra declared choices reducer root rootComplete fuel problem).remaining)

/-- **One pairs round**: the heads round; when it is stuck, the heads round on the prepared store with
expanded pairs. -/
def pairsRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match headsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck => pairsRest facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem
  | other => other

/-- **The pairs family**, at the weight rank. -/
noncomputable def pairsFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := pairsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem reexpress_const {Θ : Context S.R} (term : TotalTerm Θ) (code : Tm Head Θ.arity) :
    EventuallyConst fun fuel => reexpress facts roots heads algebra declared choices reducer fuel term code := by
  unfold reexpress
  exact EventuallyConst.dep (h := fun fuel => ExecutableChecking.check S.R choices reducer fuel Θ.raw code term.1.code)
    (k := fun fuel checked => reexpressWith facts roots heads algebra declared reducer fuel term code checked)
    (EventuallyConst.of_mono fun computed enough =>
      ContextualDependentCheckingBudget.check_success_mono S.R choices reducer stable computed enough)
    (fun checked => by
      cases checked with
      | none => exact EventuallyConst.const _
      | some checked =>
          unfold reexpressWith
          exact EventuallyConst.comp _ (compare_const facts roots heads algebra reducer stable term _))

include stable in
theorem expandOne_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel => expandOne facts roots heads algebra declared choices reducer fuel equation := by
  unfold expandOne
  refine EventuallyConst.comp (fun pair : Option {other : TotalTerm Θ // (frames S.levels).E equation.2 other} ×
      Option {other : TotalTerm Θ // (frames S.levels).E equation.1 other} =>
        match pair.1 with
        | some right => (equation.1, right.val)
        | none =>
            match pair.2 with
            | some left => (left.val, equation.2)
            | none => equation) (EventuallyConst.pair ?_ ?_)
  · cases (pairEtaCode 0 equation.1.1.code equation.1.2.code equation.2.2.code) with
    | none => exact EventuallyConst.const _
    | some code => exact reexpress_const facts roots heads algebra declared choices reducer stable equation.2 code
  · cases (pairEtaCode 0 equation.1.1.code equation.2.2.code equation.1.2.code) with
    | none => exact EventuallyConst.const _
    | some code => exact reexpress_const facts roots heads algebra declared choices reducer stable equation.1 code

include stable in
theorem expandedStore_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ),
      EventuallyConst fun fuel => problem.map (expandOne facts roots heads algebra declared choices reducer fuel)
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.comp (fun pair : Equation (TotalTerm Θ) × EquationStore (TotalTerm Θ) => pair.1 :: pair.2)
        (EventuallyConst.pair (expandOne_const facts roots heads algebra declared choices reducer stable equation)
          (expandedStore_const rest))

include stable in
theorem expanded_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => expanded facts roots heads algebra declared choices reducer fuel problem :=
  EventuallyConst.of_injective (g := Subtype.val) Subtype.val_injective
    (expandedStore_const facts roots heads algebra declared choices reducer stable problem)

include stable in
theorem pairsRest_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => pairsRest facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => liftCollapsed_view facts roots heads algebra rigid complete _ _ _) ?_
  refine EventuallyConst.dep (h := fun fuel => ContextualDependentNormalizing.prepare root rootComplete facts roots heads
      fuel problem)
    (k := fun fuel prepared => liftView (prepared.then (collapseOf (expanded facts roots heads algebra declared choices
        reducer fuel prepared.remaining)))
      (roundView (headsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete fuel
        (prepared.then (collapseOf (expanded facts roots heads algebra declared choices reducer fuel
          prepared.remaining))).remaining)))
    (prepare_const root rootComplete facts roots heads problem) (fun prepared => ?_)
  exact EventuallyConst.dep (h := fun fuel => expanded facts roots heads algebra declared choices reducer fuel
      prepared.remaining)
    (k := fun fuel store => liftView (prepared.then (collapseOf store))
      (roundView (headsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete fuel (prepared.then (collapseOf store)).remaining)))
    (expanded_const facts roots heads algebra declared choices reducer stable prepared.remaining)
    (fun store => EventuallyConst.comp (fun round => liftView (prepared.then (collapseOf store)) (roundView round))
      (headsRound_const facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete stable (prepared.then (collapseOf store)).remaining))

theorem pairsRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (pairsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (headsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (roundView (pairsRest facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)) := by
  unfold pairsRound
  cases headsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem <;> rfl

include stable in
/-- **The pairs round is eventually constant on every store.** -/
theorem pairsRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => pairsRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => pairsRound_view facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (headsRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (EventuallyConst.comp roundView (pairsRest_const facts roots heads algebra rigid complete declared choices reducer
        root normalizes certifyNormal headTypingUnique rootComplete stable problem)))

include stable in
/-- **The pairs family settles** on every class of stores on which, at each nonempty store and from some
budget on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def pairsSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        pairsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
            headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          pairsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
              headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (pairsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => pairsRound_const facts roots heads algebra rigid complete declared choices reducer
    root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentCensusPairEta
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
