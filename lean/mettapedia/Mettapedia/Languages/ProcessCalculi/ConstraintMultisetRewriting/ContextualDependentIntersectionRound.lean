import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentPrune

/-!
# The intersection round: conservativity, eventual constancy, settling

The intersection rule reads isolation from the codes (no budget), the scoped reading, `G`'s spine and the recognized
pattern, the right side's arguments, the agreeing binders, the pruned type and its spine, and the conversion test of the
instantiated equation. Type formation, spine discovery, the scoped reading and the conversion test keep their results at
larger budgets, and every other step reads no budget, so the rule is **eventually constant on every store**
(`intersectRule_const`), and so is the round (`intersectRound_const`). The round makes the reorder round's move wherever
that round moves (`intersectRound_eq_of_reorder`, `intersect_decided_of_reorder`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersection

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentScope
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentFlexReorder

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
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

/-! ## Conservativity over the reorder family -/

/-- **The intersection round makes the move of the reorder round wherever that round moves.** -/
theorem intersectRound_eq_of_reorder (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : reorderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    intersectRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem =
      reorderRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  unfold intersectRound
  cases computed : reorderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the reorder family decides, the intersection family decides with the same outcome.** -/
theorem intersect_run_of_reorder (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((reorderFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds).Decided) :
    run ((intersectFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds =
      run ((reorderFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => reorderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun problem => intersectRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun _ moving => intersectRound_eq_of_reorder facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete fuel moving)
    rounds _ decided

/-- **Every store that the reorder family decides at a joint budget, the intersection family decides at that
budget**, with the same outcome at every larger joint budget. -/
theorem intersect_decided_of_reorder {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {budget : Nat}
    (decided : ∀ larger, budget ≤ larger →
      (run ((reorderFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided) :
    ∀ larger, budget ≤ larger →
      run ((intersectFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((reorderFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger :=
  fun larger enough => intersect_run_of_reorder facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete larger larger problem (decided larger enough)

/-- **The intersection round is not stuck where the intersection rule fires.** -/
theorem intersectRound_not_stuck_of_rule (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (intersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem).isSome) :
    intersectRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold intersectRound
  cases reorderRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
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
/-- **The intersection rule on one recognized pattern is eventually constant.** -/
theorem tryIntersect_const {Γ₀ : Context S.R} (newer : TypeOver Γ₀)
    {scopeType : TypeOver (extend Γ₀ newer)} (scope : Spine scopeType) (active : Active scope.target)
    (equation : Equation (TotalTerm (extend Γ₀ newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ₀ newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ₀ newer))) (isolated : ∀ other ∈ rest, Weakened other)
    (spine : Spine newer) (recognized : Recognized spine scope active) :
    EventuallyConst fun fuel =>
      tryIntersect facts roots heads algebra rigid complete declared choices reducer normalizes headTypingUnique fuel
        newer scope active equation view rest isolated spine recognized := by
  have discovering : ∀ (Γ : Context S.R) (count : Nat) (whole : TypeOver Γ), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel count whole =
        ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer threshold count
          whole :=
    fun _ count whole => (discover_const facts roots heads algebra declared choices reducer stable count whole).spec
  have forming : ∀ (Γ : Context S.R) (code : Tm Head Γ.arity), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ code =
        ContextualDependentPruning.formType facts roots heads algebra declared choices reducer threshold Γ code :=
    fun _ code => (formType_const facts roots heads algebra declared choices reducer stable code).spec
  have comparing : ∀ (Γ : Context S.R) (first second : TotalTerm Γ), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      Conversion.compare facts roots heads algebra reducer fuel first second =
        Conversion.compare facts roots heads algebra reducer threshold first second :=
    fun _ first second => (compare_const facts roots heads algebra reducer stable first second).spec
  choose discoverAt discoverSame using discovering
  choose formAt formSame using forming
  choose compareAt compareSame using comparing
  unfold tryIntersect
  try dsimp only
  -- the right side's application
  split
  · exact EventuallyConst.const _
  -- its arguments as locals, and their positions
  split
  · exact EventuallyConst.const _
  split
  · exact EventuallyConst.const _
  -- distinct arguments, compatible binders, the same type, the same side
  split
  swap
  · exact EventuallyConst.const _
  split
  swap
  · exact EventuallyConst.const _
  try dsimp only
  split
  swap
  · exact EventuallyConst.const _
  split
  swap
  · exact EventuallyConst.const _
  try dsimp only
  -- the deleted binders
  split
  · exact EventuallyConst.const _
  -- the pruned type
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [formSame _ _ fuel enough]) ?_
  split
  · exact EventuallyConst.const _
  -- its spine, and the kept positions
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [discoverSame _ _ _ fuel enough]) ?_
  split
  · exact EventuallyConst.const _
  split
  · exact EventuallyConst.const _
  -- distinct kept positions, compatible binders, the same result, covering
  split
  swap
  · exact EventuallyConst.const _
  split
  swap
  · exact EventuallyConst.const _
  split
  swap
  · exact EventuallyConst.const _
  try dsimp only
  split
  swap
  · exact EventuallyConst.const _
  try dsimp only
  -- the conversion test of the instantiated equation
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by erw [compareSame _ _ _ fuel enough]) ?_
  split <;> exact EventuallyConst.const _

include stable in
/-- **The intersection rule on one store equation is eventually constant.** -/
theorem intersectEquation_const {Γ₀ : Context S.R} (newer : TypeOver Γ₀)
    (equation : Equation (TotalTerm (extend Γ₀ newer))) (rest : EquationStore (TotalTerm (extend Γ₀ newer))) :
    EventuallyConst fun fuel =>
      intersectEquation facts roots heads algebra rigid complete declared choices reducer root normalizes
        headTypingUnique fuel newer equation rest := by
  have viewing : ∀ {Θ : Context S.R} (equation : Equation (TotalTerm Θ)), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      viewEquation facts roots heads algebra declared choices reducer root fuel equation =
        viewEquation facts roots heads algebra declared choices reducer root threshold equation :=
    fun equation => (viewEquation_const facts roots heads algebra declared choices reducer root stable equation).spec
  have discovering : ∀ (Γ : Context S.R) (count : Nat) (whole : TypeOver Γ), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel count whole =
        ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer threshold count
          whole :=
    fun _ count whole => (discover_const facts roots heads algebra declared choices reducer stable count whole).spec
  obtain ⟨t₁, viewSame⟩ := viewing equation
  choose discoverAt discoverSame using discovering
  unfold intersectEquation
  split
  · exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by erw [viewSame fuel enough]) ?_
  split
  · exact EventuallyConst.const _
  split
  · exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [discoverSame _ _ _ fuel enough]) ?_
  split
  · exact EventuallyConst.const _
  split
  · exact EventuallyConst.const _
  exact tryIntersect_const facts roots heads algebra rigid complete declared choices reducer normalizes headTypingUnique
    stable _ _ _ _ _ _ _ _ _

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
theorem throughNewestProgress_const {Θ : Context S.R} (view : Newest Θ) (problem : EquationStore (TotalTerm Θ))
    (solve : Nat → {Γ₀ : Context S.R} → (type : TypeOver Γ₀) → (stored : EquationStore (TotalTerm (extend Γ₀ type))) →
      Option (Progress facts roots heads algebra rigid complete stored))
    (constant : ∀ {Γ₀ : Context S.R} (type : TypeOver Γ₀) stored, EventuallyConst fun fuel => solve fuel type stored) :
    EventuallyConst fun fuel =>
      throughNewestProgress facts roots heads algebra rigid complete view problem (solve fuel) := by
  rcases view with ⟨base, type, same⟩
  subst same
  exact constant type problem

include stable in
/-- **The intersection rule is eventually constant on every store.** -/
theorem intersectRule_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      intersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes headTypingUnique
        fuel problem := by
  obtain ⟨t₁, viewSame⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable Θ).spec
  cases viewed : newestOf facts roots heads algebra declared choices reducer t₁ Θ with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold intersectRule
      erw [viewSame fuel enough, viewed]
  | some view =>
      have constant : ∀ {Γ₀ : Context S.R} (newer : TypeOver Γ₀) (stored : EquationStore (TotalTerm (extend Γ₀ newer))),
          EventuallyConst fun fuel => (match stored with
            | [] => none
            | equation :: rest => intersectEquation facts roots heads algebra rigid complete declared choices reducer
                root normalizes headTypingUnique fuel newer equation rest :
              Option (Progress facts roots heads algebra rigid complete stored)) := by
        intro Γ₀ newer stored
        cases stored with
        | nil => exact EventuallyConst.const _
        | cons equation rest =>
            exact intersectEquation_const facts roots heads algebra rigid complete declared choices reducer root
              normalizes headTypingUnique stable newer equation rest
      obtain ⟨t₂, solved⟩ := (throughNewestProgress_const facts roots heads algebra rigid complete view problem
        (fun fuel {_} newer stored => match stored with
          | [] => none
          | equation :: rest => intersectEquation facts roots heads algebra rigid complete declared choices reducer root
              normalizes headTypingUnique fuel newer equation rest)
        constant).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      unfold intersectRule
      erw [viewSame fuel (le_of_max_le_left enough), viewed, viewSame _ (le_max_left _ _), viewed]
      exact (solved fuel (le_of_max_le_right enough)).trans (solved _ (le_max_right _ _)).symm

/-- The view of a progress. -/
def progressView {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} :
    Option (Progress facts roots heads algebra rigid complete problem) → Option (Option (Update S.levels problem))
  | some found => some (some found.val)
  | none => none

theorem intersectRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (intersectRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (reorderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (progressView facts roots heads algebra rigid complete (intersectRule facts roots heads algebra rigid complete
          declared choices reducer root normalizes headTypingUnique fuel problem)) := by
  unfold intersectRound
  cases reorderRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      cases intersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique fuel problem with
      | some found => rfl
      | none => rfl
  | progress update smaller => rfl
  | refuted absent => rfl

include stable in
/-- **The intersection round is eventually constant on every store.** -/
theorem intersectRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => intersectRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => intersectRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (reorderRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (EventuallyConst.comp (progressView facts roots heads algebra rigid complete) (intersectRule_const facts roots
        heads algebra rigid complete declared choices reducer root normalizes headTypingUnique stable problem)))

include stable in
/-- **The intersection family settles** on every class of stores on which, at each nonempty store and from some
budget on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def intersectSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        intersectRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          intersectRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (intersectFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => intersectRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentIntersection
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
