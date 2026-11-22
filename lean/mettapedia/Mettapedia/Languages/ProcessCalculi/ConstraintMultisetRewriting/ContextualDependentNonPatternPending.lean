import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentFiringControls

/-!
# The non-pattern store `F x x ≐ Id T y x` is unsolvable, and no solver ever solves it

Over `T : U0, F : (a b : T) → U0`, R77's store `λ x y. F x x ≐ λ x y. Id T y x` repeats the local
`x`, so it lies outside the dynamic pattern fragment (`repeated_store_not_in_fragment`).

**It has no solution in any future context.** At a solution `σ`, the opened equation reads
`f x x ≐ Id A y x` over `Δ, x y : A`, where neither `f` nor `A` mentions the locals. Instantiating
`y` by `x` and weakening again turns it into `f x x ≐ Id A x x`, with the same left side. So
`Id A y x ≐ Id A x x`, and equal identity types have equal endpoints: `y ≐ x`, two distinct rigid
locals, which no future context makes equal.

Hence no run of any solver ever solves it: a solved run carries a solution. And no run of the
rigid solver or of the fragment solver ever refutes it: the left side `F x x` is a spine with a
repeated argument, which recognition never reads; the right side is an identity type; there is no
clash; the conversion scan cannot discharge an unsolvable equation; neither side is equal to `F`, so
the dispatcher never fires; `F` mentions `T`, so exchange never applies; and two declarations are
too few to rotate. **The store is pending (suspended) at every budget** (`repeated_pending`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFragment.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentWorklist
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls
open ContextualDependentPatternSolver ContextualDependentPatternSolver.Controls
open ContextualDependentDynamicFragment ContextualDependentDecisiveFragment

/-! ## Unsolvable -/

/-- `y ≐ x` at `T`, under `T, F, x, y`. -/
def crossedLocals : Active scope.target :=
  ⟨ContextualDependentRigidDecomposition.Controls.carrier, ContextualDependentRigidDecomposition.Controls.secondLocal,
    ContextualDependentRigidDecomposition.Controls.firstLocal⟩

theorem repeatedStore_closes :
    ∃ active, (scope.toScoped RecognitionControls.repeatedEquation).closeWith setting.levels
      ExecutableTowerChoices.choices = some active :=
  Option.isSome_iff_exists.mp (by decide +kernel)

/-- **`λ x y. F x x ≐ λ x y. Id T y x` has no solution in any future context.** -/
theorem repeated_unsolvable : ¬ (frames setting.levels).Solvable repeatedStore := by
  rintro ⟨Δ, solution, solved⟩
  have held := (closeStore_models (scope.toScoped RecognitionControls.repeatedEquation) solution
    repeatedStore_closes).mp solved
  replace held := (Spine.toScoped_holds_iff scope RecognitionControls.repeatedEquation solution).mp held
  change Equal setting.R
      (.snoc (.snoc Δ.raw (solution.substitution 1)) (Presentation.rename wk (solution.substitution 1)))
      (.app (.app (Presentation.rename wk (Presentation.rename wk (solution.substitution 0))) (.var 1)) (.var 1))
      (.id (Presentation.rename wk (Presentation.rename wk (solution.substitution 1))) (.var 0) (.var 1))
      (.head (.sort Tower.zero)) at held
  have local_typed : Typed setting.R (.snoc Δ.raw (solution.substitution 1)) (.var 0)
      (Presentation.rename wk (solution.substitution 1)) := .var 0
  have collapsed := (held.substitute (SubstMor.single local_typed)).weaken
    (extension := Presentation.rename wk (solution.substitution 1))
  change Equal setting.R
      (.snoc (.snoc Δ.raw (solution.substitution 1)) (Presentation.rename wk (solution.substitution 1)))
      (Presentation.rename wk (.app (.app (inst0 (.var 0)
        (Presentation.rename wk (Presentation.rename wk (solution.substitution 0)))) (.var 0)) (.var 0)))
      (Presentation.rename wk (.id (inst0 (.var 0)
        (Presentation.rename wk (Presentation.rename wk (solution.substitution 1)))) (.var 0) (.var 0)))
      (.head (.sort Tower.zero)) at collapsed
  rw [inst0_rename_wk, inst0_rename_wk] at collapsed
  change Equal setting.R
      (.snoc (.snoc Δ.raw (solution.substitution 1)) (Presentation.rename wk (solution.substitution 1)))
      (.app (.app (Presentation.rename wk (Presentation.rename wk (solution.substitution 0))) (.var 1)) (.var 1))
      (.id (Presentation.rename wk (Presentation.rename wk (solution.substitution 1))) (.var 1) (.var 1))
      (.head (.sort Tower.zero)) at collapsed
  have types : TypeEq setting.R
      (.snoc (.snoc Δ.raw (solution.substitution 1)) (Presentation.rename wk (solution.substitution 1)))
      (.id (Presentation.rename wk (Presentation.rename wk (solution.substitution 1))) (.var 0) (.var 1))
      (.id (Presentation.rename wk (Presentation.rename wk (solution.substitution 1))) (.var 1) (.var 1)) :=
    ⟨_, .sort _, held.symm.trans collapsed⟩
  obtain ⟨_, ends, _⟩ := (ContextualDependentRigid.typeEq_id_iff TowerModel.facts
    (scope.reindex solution).target.formed).mp types
  apply ContextualDependentRigidDecomposition.distinct_locals_refuted ContextualDependentPiSpine.Controls.rigid
    TowerModel.complete scope crossedLocals (.inr (.inl ())) (.inl ()) (by intro same; cases same)
    (by rfl') (by rfl') solution ((Spine.toScoped_holds_iff scope crossedLocals solution).mpr ends)

/-! ## Never solved -/

/-- **No run of any solver solves it**: a solved run carries a solution. -/
theorem repeated_never_solved (solver : Solver setting.levels) (rounds : Nat) :
    ∀ state finished, run solver repeatedStore rounds ≠ .solved state finished := by
  intro state finished solved
  exact repeated_unsolvable ⟨_, state.answer, (drive_solved_principal solver solved).1⟩

/-! ## Neither side is the newest variable -/

/-- `F := λ a b. Id T a b`, used to separate terms. -/
abbrev separating : ContextualDependentGeneralPattern.Controls.types ⟶ extend ContextualDependentGeneralPattern.Controls.types outerWhole :=
  Elimination.instantiate ContextualDependentGeneralPattern.Controls.types (spine.abstractBody orderedBody)

/-- The repeated equation as the store's only equation. -/
def repeatedOnly : Equation (TotalTerm (extend ContextualDependentGeneralPattern.Controls.types outerWhole)) :=
  repeatedStore.head (List.ne_nil_of_length_pos (by
    rw [ContextualDependentDynamicFragment.Controls.repeated_store_length]; decide))

theorem repeatedStore_eq : repeatedStore = [repeatedOnly] :=
  ContextualDependentDynamicFragment.Controls.singleton_of_length repeatedStore
    ContextualDependentDynamicFragment.Controls.repeated_store_length

/-- **Two functions of `(a b : T) → U0` over `T` whose opened bodies normalize to identity types
with differently supported endpoints are not equal.** -/
theorem not_equal_of_opened {first second : Term ContextualDependentGeneralPattern.Controls.types outerWhole}
    {A a b A' a' b' : Tower.Tm 3}
    (firstRun : (ExecutableReduction.normalize setting.R (fun _ => none) 16 (spine.openFunction first).code).isSome)
    (firstValue : ((ExecutableReduction.normalize setting.R (fun _ => none) 16
      (spine.openFunction first).code).get firstRun).val = .id A a b)
    (secondRun : (ExecutableReduction.normalize setting.R (fun _ => none) 16 (spine.openFunction second).code).isSome)
    (secondValue : ((ExecutableReduction.normalize setting.R (fun _ => none) 16
      (spine.openFunction second).code).get secondRun).val = .id A' a' b')
    (normalA : ContextualDependentNormalChecking.Normal (S := setting) a)
    (normalA' : ContextualDependentNormalChecking.Normal (S := setting) a')
    (normalB : ContextualDependentNormalChecking.Normal (S := setting) b)
    (normalB' : ContextualDependentNormalChecking.Normal (S := setting) b')
    (apart : ¬ (a.support = a'.support ∧ b.support = b'.support)) :
    ¬ Equal setting.R ContextualDependentGeneralPattern.Controls.types.raw first.code second.code outerWhole.code := by
  intro same
  have opened := (spine.openFunction_equal_iff first second).mp same
  have toFirst := (Reduces.preserve (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads spine.target.formed
    ((ExecutableReduction.normalize setting.R (fun _ => none) 16 (spine.openFunction first).code).get firstRun).property
    (spine.openFunction first).typed).2
  have toSecond := (Reduces.preserve (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads spine.target.formed
    ((ExecutableReduction.normalize setting.R (fun _ => none) 16 (spine.openFunction second).code).get secondRun).property
    (spine.openFunction second).typed).2
  rw [firstValue] at toFirst
  rw [secondValue] at toSecond
  have normals := toFirst.symm.trans (opened.trans toSecond)
  have identities : TypeEq setting.R spine.target.raw (.id A a b) (.id A' a' b') := ⟨_, .sort _, normals⟩
  obtain ⟨_, lefts, rights⟩ := (ContextualDependentRigid.typeEq_id_iff TowerModel.facts spine.target.formed).mp identities
  exact apart ⟨ContextualDependentNormalSupport.equal_support ContextualDependentPiSpine.Controls.rigid
      TowerModel.complete spine.target.formed lefts normalA normalA',
    ContextualDependentNormalSupport.equal_support ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      spine.target.formed rights normalB normalB'⟩

/-- The annotation of the equation, moved to `T` by the separating instantiation, is `(a b : T) → U0`. -/
theorem separated_annotation :
    subst separating.substitution repeatedOnly.1.1.code = outerWhole.code := by decide +kernel

theorem separated_right_annotation :
    subst separating.substitution repeatedOnly.2.1.code = outerWhole.code := by decide +kernel

/-- A side of the equation, moved to `T` by the separating instantiation, as a term. -/
def separatedLeft : Term ContextualDependentGeneralPattern.Controls.types outerWhole :=
  ⟨subst separating.substitution repeatedOnly.1.2.code, by
    have moved := repeatedOnly.1.2.typed.substitute separating.typed
    rw [separated_annotation] at moved
    exact moved⟩

def separatedRight : Term ContextualDependentGeneralPattern.Controls.types outerWhole :=
  ⟨subst separating.substitution repeatedOnly.2.2.code, by
    have moved := repeatedOnly.2.2.typed.substitute separating.typed
    rw [separated_right_annotation] at moved
    exact moved⟩

theorem separated_newest :
    subst separating.substitution (.var 0 : Tower.Tm 2) = (spine.abstractBody orderedBody).code := by decide +kernel

theorem separated_type :
    subst separating.substitution (Presentation.rename wk outerWhole.code) = outerWhole.code := by decide +kernel

/-- **The left side `λ x y. F x x` is not the newest variable `F`.** -/
theorem repeated_left_not_newest :
    ¬ Equal setting.R (extend ContextualDependentGeneralPattern.Controls.types outerWhole).raw repeatedOnly.1.2.code
      (.var 0) (Presentation.rename wk outerWhole.code) := by
  intro same
  have moved := same.substitute separating.typed
  erw [separated_newest, separated_type] at moved
  exact not_equal_of_opened (first := separatedLeft) (second := spine.abstractBody orderedBody)
    (A := .var 2) (a := .var 1) (b := .var 1) (A' := .var 2) (a' := .var 1) (b' := .var 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ContextualDependentNormalObservations.normal_var ContextualDependentPiSpine.Controls.rigid _) (ContextualDependentNormalObservations.normal_var ContextualDependentPiSpine.Controls.rigid _)
    (ContextualDependentNormalObservations.normal_var ContextualDependentPiSpine.Controls.rigid _) (ContextualDependentNormalObservations.normal_var ContextualDependentPiSpine.Controls.rigid _)
    (by decide +kernel) moved

/-- **The right side `λ x y. Id T y x` is not the newest variable `F`.** -/
theorem repeated_right_not_newest :
    ¬ Equal setting.R (extend ContextualDependentGeneralPattern.Controls.types outerWhole).raw repeatedOnly.2.2.code
      (.var 0) (Presentation.rename wk outerWhole.code) := by
  intro same
  have moved := same.substitute separating.typed
  erw [separated_newest, separated_type] at moved
  exact not_equal_of_opened (first := separatedRight) (second := spine.abstractBody orderedBody)
    (A := .var 2) (a := .var 0) (b := .var 1) (A' := .var 2) (a' := .var 1) (b' := .var 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ContextualDependentNormalObservations.normal_var ContextualDependentPiSpine.Controls.rigid _) (ContextualDependentNormalObservations.normal_var ContextualDependentPiSpine.Controls.rigid _)
    (ContextualDependentNormalObservations.normal_var ContextualDependentPiSpine.Controls.rigid _) (ContextualDependentNormalObservations.normal_var ContextualDependentPiSpine.Controls.rigid _)
    (by decide +kernel) moved

/-! ## No rule reads it -/

/-- Every result of the executable normalizer on a code is unreadable when the one at a budget
where it finishes is. -/
theorem normalize_results_unreadable (bound : Nat) {n : Nat} (code : Tower.Tm n)
    (finishes : (ExecutableReduction.normalize setting.R (fun _ => none) bound code).isSome = true)
    (unreadableResult : ((ExecutableReduction.normalize setting.R (fun _ => none) bound code).map Subtype.val).all
      unreadableB = true) :
    ∀ fuel result, ExecutableReduction.normalize setting.R (fun _ => none) fuel code = some result →
      Unreadable result.val := by
  intro fuel result run
  obtain ⟨found, foundRun⟩ := Option.isSome_iff_exists.mp finishes
  have mono : ∀ {first second : Nat} {value : ExecutableReduction.Result setting.R code},
      ExecutableReduction.normalize setting.R (fun _ => none) first code = some value → first ≤ second →
        ExecutableReduction.normalize setting.R (fun _ => none) second code = some value := by
    intro first second value computed enough
    induction enough with
    | refl => exact computed
    | step _ ih => exact ContextualDependentReductionBudget.success_succ setting.R (fun _ => none) ih
  have same : result = found := by
    have atResult := mono run (le_max_left fuel bound)
    rw [mono foundRun (le_max_right fuel bound)] at atResult
    exact (Option.some.inj atResult).symm
  subst same
  rw [foundRun] at unreadableResult
  exact unreadable_of_unreadableB (by simpa using unreadableResult)

/-- **Both opened sides are unreadable at every budget**: the left side is `F x x`, a spine with a
repeated argument, or the β-redex it comes from; the right side is an identity type. -/
theorem repeated_unreadable : UnreadableEquation (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) repeatedOnly := by
  intro fuel reading read
  obtain ⟨found, leftCode, right, rightSame, rightCode⟩ := viewEquation_codes (S := setting) TowerModel.facts
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none) fuel repeatedOnly read
  have depth : lamDepth repeatedOnly.1.2.code = 2 := by decide +kernel
  rw [depth] at found
  have opened : ∀ term : Term (extend ContextualDependentGeneralPattern.Controls.types outerWhole) repeatedOnly.1.1,
      (Unreadable (Tm.app (Presentation.rename wk (Tm.app (Presentation.rename wk term.code) (.var 0))) (.var 0)) ∧
        ∀ fuel' result, ExecutableReduction.normalize setting.R (fun _ => none) fuel'
          (Tm.app (Presentation.rename wk (Tm.app (Presentation.rename wk term.code) (.var 0))) (.var 0)) =
            some result → Unreadable result.val) →
      Unreadable (normalizeAt (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads (fun _ => none) fuel
        (reading.1.openFunction term)).1.code := by
    intro term holds
    have both := discover_two_code (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer fuel _ reading.1 found term
      (fun code => Unreadable code ∧ ∀ fuel' result,
        ExecutableReduction.normalize setting.R (fun _ => none) fuel' code = some result → Unreadable result.val) holds
    rcases normalizeAt_code (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads (fun _ => none) fuel
      (reading.1.openFunction term) with same | ⟨result, run, same⟩
    · rw [same]; exact both.1
    · rw [same]; exact both.2 fuel result run
  refine ⟨?_, ?_⟩
  · rw [leftCode]
    exact opened repeatedOnly.1.2 ⟨unreadable_of_unreadableB (by decide +kernel),
      normalize_results_unreadable 8 _ (by decide +kernel) (by decide +kernel)⟩
  · rw [rightCode]
    apply opened
    rw [rightSame]
    exact ⟨unreadable_of_unreadableB (by decide +kernel),
      normalize_results_unreadable 8 _ (by decide +kernel) (by decide +kernel)⟩

/-- **The newest declaration `F` mentions the one below it, `T`**, so the exchange rule never
applies. -/
theorem repeated_dependent : ∀ (Γ₀ : Context setting.R) (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older)),
    extend ContextualDependentGeneralPattern.Controls.types outerWhole = extend (extend Γ₀ older) newer →
      ContextualDependentInversion.invert (ContextualDependentPatternSolver.withoutNewest Γ₀.arity) newer.code = none := by
  intro Γ₀ older newer same
  obtain ⟨arity, raw, formed⟩ := Γ₀
  obtain ⟨olderCode, olderLevel, olderUniverse, olderFormed⟩ := older
  obtain ⟨newerCode, newerLevel, newerUniverse, newerFormed⟩ := newer
  cases same
  exact (by decide +kernel :
    ContextualDependentInversion.invert (ContextualDependentPatternSolver.withoutNewest 0) outerWhole.code = none)

theorem repeated_context_stopped :
    StoppedContext (S := setting) (fun _ => none) (extend ContextualDependentGeneralPattern.Controls.types outerWhole).raw :=
  ⟨⟨trivial, rfl⟩, rfl⟩

theorem repeated_codes_stopped : ∀ equation ∈ repeatedStore,
    StoppedTerm (S := setting) (fun _ => none) equation.1 ∧ StoppedTerm (S := setting) (fun _ => none) equation.2 := by
  rw [repeatedStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  exact ⟨⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel⟩⟩

theorem repeatedOnly_unsolvable : ¬ (frames setting.levels).Solvable [repeatedOnly] := by
  intro solvable
  apply repeated_unsolvable
  rw [repeatedStore_eq]
  exact solvable

/-- The dispatcher never solves `F` from it. -/
theorem repeated_noSearch (fuel : Nat) :
    ∀ view : Newest (extend ContextualDependentGeneralPattern.Controls.types outerWhole),
      ∀ moved : Equation (TotalTerm (extend view.base view.type)), HEq moved repeatedOnly →
        ContextualDependentDispatch.search (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
          TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
          ContextualDependentInversion.Controls.reducer fuel view.type [moved] = none := by
  intro view moved same
  obtain ⟨⟨arity, raw, formed⟩, ⟨code, level, universeWitness, typeFormed⟩, contexts⟩ := view
  cases contexts
  cases same
  exact search_of_not_newest (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer fuel ⟨_, level, universeWitness, typeFormed⟩ repeatedOnly
    repeated_left_not_newest repeated_right_not_newest

/-! ## Pending at every budget -/

/-- **The rigid round is stuck on it at every budget.** -/
theorem repeated_rigidRound_stuck (fuel : Nat) :
    ContextualDependentRigidDecomposition.rigidRound (S := setting) ContextualDependentPiSpine.Controls.rigid
      TowerModel.complete TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique fuel [repeatedOnly] =
        .stuck := by
  unfold ContextualDependentRigidDecomposition.rigidRound
  rw [localsRule_unreadable (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts
    TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) fuel repeatedOnly repeated_unreadable]
  dsimp only
  erw [fullRound_eq]
  have first : firstRule (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
      TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
      DispatchControls.tower_normalizes DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique fuel [repeatedOnly] = none := by
    unfold firstRule
    rw [patternRule_unreadable (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts
      TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal fuel repeatedOnly repeated_unreadable]
    dsimp only
    rw [pruneRule_unreadable (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts
      TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique fuel repeatedOnly
      repeated_unreadable]
    exact exchangeRule_dependent (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts
      TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal fuel _ repeated_dependent
  rw [first]
  dsimp only
  exact worklistRound_stuck_of_search (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts
    TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer fuel repeatedOnly (by decide +kernel) repeatedOnly_unsolvable
    (repeated_noSearch fuel)

/-- **The decomposition round is stuck on it at every budget.** -/
theorem repeated_decomposeRound_stuck (fuel : Nat) :
    ContextualDependentRigidDecomposition.decomposeRound (S := setting) ContextualDependentPiSpine.Controls.rigid
      TowerModel.facts TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique fuel [repeatedOnly] =
        .stuck := by
  unfold ContextualDependentRigidDecomposition.decomposeRound
  rw [decomposeSearch_unreadable (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts
    TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal fuel repeatedOnly repeated_unreadable]
  exact repeated_rigidRound_stuck fuel

/-- **The fragment round is stuck on it at every budget.** -/
theorem repeated_fragmentRound_stuck (fuel : Nat) :
    fragmentRound (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
      TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique fuel repeatedStore =
        .stuck := by
  apply fragmentRound_stuck_of_stopped (S := setting) (fun _ => none)
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
    TowerModel.heads ContextualDependentPiSpine.Controls.rigid TowerModel.complete TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique fuel repeatedStore repeated_context_stopped
    repeated_codes_stopped
  · rw [repeatedStore_eq]
    exact repeated_decomposeRound_stuck fuel
  · exact rotateRule_short (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
      TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
      DispatchControls.tower_normalizes DispatchControls.certifyNormal fuel (by decide) repeatedStore

theorem repeatedStore_nonempty : repeatedStore ≠ [] := by
  rw [repeatedStore_eq]
  exact List.cons_ne_nil _ _

/-- A run that is not decided is suspended. -/
theorem suspended_of_not_decided {Γ : Context setting.R} {original : EquationStore (TotalTerm Γ)}
    {outcome : Outcome setting.levels original} (undecided : ¬ outcome.Decided) : outcome.readout = .suspended := by
  cases outcome with
  | solved state finished => exact absurd trivial undecided
  | refuted absent => exact absurd trivial undecided
  | stuck state => rfl
  | cutoff state => rfl

/-- **`F x x ≐ Id T y x` is pending at every budget**: for the fragment solver and the rigid solver,
at every budget and every number of rounds, the run is suspended. It is never solved, because it
has no solution, and never refuted, because no rule reads it. -/
theorem repeated_pending (fuel rounds : Nat) :
    (run (fragmentTower.solver fuel) repeatedStore rounds).readout = .suspended ∧
      (run (rigidTower.solver fuel) repeatedStore rounds).readout = .suspended := by
  refine ⟨suspended_of_not_decided (never_decided_of_stuck _ repeatedStore_nonempty
      (repeated_fragmentRound_stuck fuel) rounds),
    suspended_of_not_decided (never_decided_of_stuck _ repeatedStore_nonempty ?_ rounds)⟩
  rw [repeatedStore_eq]
  exact repeated_rigidRound_stuck fuel

end ContextualDependentFragment.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
