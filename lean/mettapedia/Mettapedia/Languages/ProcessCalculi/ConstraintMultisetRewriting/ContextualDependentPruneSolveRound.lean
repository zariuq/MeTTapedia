import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruneSolveRule
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentPrune

/-!
# The prune-and-solve round: conservativity, eventual constancy, settling

Spine discovery, type formation and R76's pattern search keep their results at larger budgets, and every other step of
the rule reads no budget, so the rule is eventually constant on every store (`pruneSolveRule_const`), and so is the round
(`pruneSolveRound_const`). The round makes the intersection round's move wherever that round moves
(`pruneSolveRound_eq_of_intersect`, `pruneSolve_decided_of_intersect`), and it is not stuck where the rule fires.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPruneSolve

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentScope
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentFlexReorder
open ContextualDependentIntersection
open ContextualDependentParameterExchange (second)

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

/-! ## Conservativity over the intersection family -/

/-- **The prune-and-solve round makes the move of the intersection round wherever that round moves.** -/
theorem pruneSolveRound_eq_of_intersect (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : intersectRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    pruneSolveRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem =
      intersectRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  unfold pruneSolveRound
  cases computed : intersectRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the intersection family decides, the prune-and-solve family decides with the same outcome.** -/
theorem pruneSolve_run_of_intersect (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((intersectFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds).Decided) :
    run ((pruneSolveFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds =
      run ((intersectFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => intersectRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun problem => pruneSolveRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun _ moving => pruneSolveRound_eq_of_intersect facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete fuel moving)
    rounds _ decided

/-- **Every store that the intersection family decides at a joint budget, the prune-and-solve family decides at that
budget**, with the same outcome at every larger joint budget. -/
theorem pruneSolve_decided_of_intersect {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {budget : Nat}
    (decided : ∀ larger, budget ≤ larger →
      (run ((intersectFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided) :
    ∀ larger, budget ≤ larger →
      run ((pruneSolveFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((intersectFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger :=
  fun larger enough => pruneSolve_run_of_intersect facts roots heads algebra rigid complete declared choices reducer
    root normalizes certifyNormal headTypingUnique rootComplete larger larger problem (decided larger enough)

/-- **The prune-and-solve round is not stuck where the rule fires.** -/
theorem pruneSolveRound_not_stuck_of_rule (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (pruneSolveRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel problem).isSome) :
    pruneSolveRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold pruneSolveRound
  cases intersectRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp read
      rw [computed]
      cases found with
      | solved update smaller => exact fun impossible => by cases impossible
      | refuted absent => exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-! ## Eventual constancy -/

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- A decided branch whose two sides are eventually constant is eventually constant. -/
theorem eventually_dite {α : Sort _} {c : Prop} {decision : Decidable c} {t : Nat → c → α} {e : Nat → ¬ c → α}
    (pos : ∀ h : c, EventuallyConst fun fuel => t fuel h) (neg : ∀ h : ¬ c, EventuallyConst fun fuel => e fuel h) :
    EventuallyConst fun fuel => @dite α c decision (fun h => t fuel h) (fun h => e fuel h) := by
  cases decision with
  | isTrue h => exact EventuallyConst.of_eq (fun _ => rfl) (pos h)
  | isFalse h => exact EventuallyConst.of_eq (fun _ => rfl) (neg h)

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **The rule under a rigid binder context is eventually constant.** -/
theorem tryContext_const {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) {u : Head}
    (hu : S.R.isUniverse u) (annotation : active.type.code = .head u) :
    EventuallyConst fun fuel =>
      tryContext facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel older newer scope active equation view rest hu annotation := by
  have discovering : ∀ (Γ : Context S.R) (count : Nat) (whole : TypeOver Γ), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel count whole =
        ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer threshold count
          whole :=
    fun _ count whole => (discover_const facts roots heads algebra declared choices reducer stable count whole).spec
  have forming : ∀ (Γ : Context S.R) (code : Tm Head Γ.arity), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ code =
        ContextualDependentPruning.formType facts roots heads algebra declared choices reducer threshold Γ code :=
    fun _ code => (formType_const facts roots heads algebra declared choices reducer stable code).spec
  have searching : ∀ (Γ : Context S.R) (type : TypeOver Γ) (store : EquationStore (TotalTerm (extend Γ type))),
      ∃ threshold, ∀ fuel, threshold ≤ fuel →
        searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal fuel
            type store =
          searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
            threshold type store :=
    fun _ type store => (searchStore_const rigid facts complete roots heads algebra declared choices reducer root
      normalizes certifyNormal stable type store).spec
  choose discoverAt discoverSame using discovering
  choose formAt formSame using forming
  choose searchAt searchSame using searching
  unfold tryContext
  try dsimp only
  -- the pattern candidate in the binder context, read as an application
  split <;> try exact EventuallyConst.const _
  split <;> try exact EventuallyConst.const _
  -- `G`'s spine
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [discoverSame _ _ _ fuel enough]) ?_
  split <;> try exact EventuallyConst.const _
  try dsimp only
  -- `G`'s arguments, distinct and compatible, the same side, a universe
  split <;> try exact EventuallyConst.const _
  split <;> try exact EventuallyConst.const _
  refine eventually_dite (fun _ => ?_) (fun _ => EventuallyConst.const _)
  refine eventually_dite (fun _ => ?_) (fun _ => EventuallyConst.const _)
  try dsimp only
  refine eventually_dite (fun _ => ?_) (fun _ => EventuallyConst.const _)
  split <;> try exact EventuallyConst.const _
  refine eventually_dite (fun _ => ?_) (fun _ => EventuallyConst.const _)
  -- the other side's application and `F`'s spine
  split <;> try exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [discoverSame _ _ _ fuel enough]) ?_
  split <;> try exact EventuallyConst.const _
  split <;> try exact EventuallyConst.const _
  split <;> try exact EventuallyConst.const _
  refine eventually_dite (fun _ => ?_) (fun _ => EventuallyConst.const _)
  refine eventually_dite (fun _ => ?_) (fun _ => EventuallyConst.const _)
  try dsimp only
  refine eventually_dite (fun _ => ?_) (fun _ => EventuallyConst.const _)
  refine eventually_dite (fun _ => ?_) (fun _ => EventuallyConst.const _)
  try dsimp only
  -- the deleted binders, the pruned type and its spine
  split <;> try exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [formSame _ _ fuel enough]) ?_
  split <;> try exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [discoverSame _ _ _ fuel enough]) ?_
  split <;> try exact EventuallyConst.const _
  split <;> try exact EventuallyConst.const _
  -- distinct kept positions, compatible binders, the same result, covering
  refine eventually_dite (fun _ => ?_) (fun _ => EventuallyConst.const _)
  refine eventually_dite (fun _ => ?_) (fun _ => EventuallyConst.const _)
  refine eventually_dite (fun _ => ?_) (fun _ => EventuallyConst.const _)
  try dsimp only
  refine eventually_dite (fun _ => ?_) (fun _ => EventuallyConst.const _)
  try dsimp only
  -- the pattern search after exchanging
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by erw [searchSame _ _ _ fuel enough]) ?_
  split <;> exact EventuallyConst.const _

include stable in
/-- **The rule on one scoped reading is eventually constant.** -/
theorem tryCodomain_const {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) :
    EventuallyConst fun fuel =>
      tryCodomain facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel older newer scope active equation view rest := by
  unfold tryCodomain
  split <;> try exact EventuallyConst.const _
  refine eventually_dite (fun _ => ?_) (fun _ => EventuallyConst.const _)
  exact tryContext_const facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique stable _ _ _ _ _ _ _ _ _

include stable in
/-- **The rule on one store equation, in both orientations, is eventually constant.** -/
theorem codomainEquation_const {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) :
    EventuallyConst fun fuel =>
      codomainEquation facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel older newer equation rest := by
  obtain ⟨t₁, viewed⟩ := (viewEquation_const facts roots heads algebra declared choices reducer root stable
    equation).spec
  cases reading : viewEquation facts roots heads algebra declared choices reducer root t₁ equation with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold codomainEquation
      erw [viewed fuel enough, reading]
  | some found =>
      obtain ⟨scope, active, view⟩ := found
      obtain ⟨t₂, first⟩ := (tryCodomain_const facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique stable older newer scope active equation view rest).spec
      obtain ⟨t₃, second⟩ := (tryCodomain_const facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique stable older newer scope ⟨active.type, active.right, active.left⟩
        equation (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest).spec
      refine ⟨max t₁ (max t₂ t₃), fun fuel enough => ?_⟩
      have e₁ : t₁ ≤ fuel := by omega
      have e₂ : t₂ ≤ fuel := by omega
      have e₃ : t₃ ≤ fuel := by omega
      have f₁ : t₁ ≤ max t₁ (max t₂ t₃) := by omega
      have f₂ : t₂ ≤ max t₁ (max t₂ t₃) := by omega
      have f₃ : t₃ ≤ max t₁ (max t₂ t₃) := by omega
      dsimp only
      unfold codomainEquation
      erw [viewed fuel e₁, reading, viewed _ f₁, reading]
      dsimp only
      erw [first fuel e₂, first _ f₂, second fuel e₃, second _ f₃]

include stable in
/-- **The rule through the store is eventually constant.** -/
theorem codomainSearch_const {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older)) :
    ∀ problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)), EventuallyConst fun fuel =>
      codomainSearch facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel older newer problem
  | [] => ⟨0, fun _ _ => rfl⟩
  | equation :: rest => by
      obtain ⟨t₁, first⟩ := (codomainEquation_const facts roots heads algebra rigid complete declared choices reducer
        root normalizes certifyNormal headTypingUnique stable older newer equation rest).spec
      obtain ⟨t₂, later⟩ := (codomainSearch_const older newer rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      simp only [codomainSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

include stable in
/-- **The rule at the two newest declarations is eventually constant on every store.** -/
theorem codomainRule_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      codomainRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel problem := by
  obtain ⟨t₁, outerSame⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable Θ).spec
  cases outer : newestOf facts roots heads algebra declared choices reducer t₁ Θ with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold codomainRule
      erw [outerSame fuel enough, outer]
  | some outerView =>
      obtain ⟨t₂, innerSame⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable
        outerView.base).spec
      cases inner : newestOf facts roots heads algebra declared choices reducer t₂ outerView.base with
      | none =>
          refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
          dsimp only
          unfold codomainRule
          erw [outerSame fuel (le_of_max_le_left enough), outer, outerSame _ (le_max_left _ _), outer]
          dsimp only
          erw [innerSame fuel (le_of_max_le_right enough), inner, innerSame _ (le_max_right _ _), inner]
      | some innerView =>
          obtain ⟨t₃, through⟩ := (throughTwo_const outerView innerView problem
            (fun fuel {_} older newer stored => codomainSearch facts roots heads algebra rigid complete declared
              choices reducer root normalizes certifyNormal headTypingUnique fuel older newer stored)
            (fun older newer stored => codomainSearch_const facts roots heads algebra rigid complete declared choices
              reducer root normalizes certifyNormal headTypingUnique stable older newer stored)).spec
          refine ⟨max t₁ (max t₂ t₃), fun fuel enough => ?_⟩
          have e₁ : t₁ ≤ fuel := by omega
          have e₂ : t₂ ≤ fuel := by omega
          have e₃ : t₃ ≤ fuel := by omega
          dsimp only
          unfold codomainRule
          erw [outerSame fuel e₁, outer, outerSame _ (by omega), outer]
          dsimp only
          erw [innerSame fuel e₂, inner, innerSame _ (by omega), inner]
          dsimp only
          exact (through fuel e₃).trans (through _ (by omega)).symm

include stable in
/-- **Exchanging first is eventually constant** when the solver after it is. -/
theorem exchangeSolve_const
    (solve : Nat → {Γ : Context S.R} → (stored : EquationStore (TotalTerm Γ)) → Option (Found stored))
    (constant : ∀ {Γ : Context S.R} (stored : EquationStore (TotalTerm Γ)), EventuallyConst fun fuel => solve fuel stored)
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) :
    EventuallyConst fun fuel =>
      exchangeSolve facts roots heads algebra declared choices reducer fuel (solve fuel) older newer problem := by
  cases inverted : ContextualDependentInversion.invert (withoutNewest Γ₀.arity) newer.code with
  | none =>
      refine ⟨0, fun fuel _ => ?_⟩
      dsimp only
      unfold exchangeSolve
      simp only [inverted]
  | some code =>
      obtain ⟨t₁, formed⟩ := (formType_const facts roots heads algebra declared choices reducer stable
        (Γ := Γ₀) code).spec
      cases next : ContextualDependentPruning.formType facts roots heads algebra declared choices reducer t₁ Γ₀ code with
      | none =>
          refine ⟨t₁, fun fuel enough => ?_⟩
          dsimp only
          unfold exchangeSolve
          simp only [inverted]
          erw [formed fuel enough, next]
      | some formedType =>
          by_cases same : newer.code = (second older formedType.val).code ∧
              newer.level = (second older formedType.val).level
          · have independent : newer = second older formedType.val := TypeOver.ext same.1 same.2
            subst independent
            obtain ⟨t₂, solved⟩ := (EventuallyConst.comp
              (afterExchange (ContextualDependentPrune.exchange S.levels older formedType.val problem) rfl)
              (constant (ContextualDependentPrune.exchange S.levels older formedType.val problem).remaining)).spec
            refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
            dsimp only
            unfold exchangeSolve
            simp only [inverted]
            erw [formed fuel (le_of_max_le_left enough), next, formed _ (le_max_left _ _), next]
            dsimp only
            rw [dif_pos same, dif_pos same]
            exact (solved fuel (le_of_max_le_right enough)).trans (solved _ (le_max_right _ _)).symm
          · refine ⟨t₁, fun fuel enough => ?_⟩
            dsimp only
            unfold exchangeSolve
            simp only [inverted]
            erw [formed fuel enough, next]
            dsimp only
            rw [dif_neg same, dif_neg same]

include stable in
/-- **The rule after exchanging is eventually constant on every store.** -/
theorem exchangedRule_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      exchangedRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel problem := by
  obtain ⟨t₁, outerSame⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable Θ).spec
  cases outer : newestOf facts roots heads algebra declared choices reducer t₁ Θ with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold exchangedRule
      erw [outerSame fuel enough, outer]
  | some outerView =>
      obtain ⟨t₂, innerSame⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable
        outerView.base).spec
      cases inner : newestOf facts roots heads algebra declared choices reducer t₂ outerView.base with
      | none =>
          refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
          dsimp only
          unfold exchangedRule
          erw [outerSame fuel (le_of_max_le_left enough), outer, outerSame _ (le_max_left _ _), outer]
          dsimp only
          erw [innerSame fuel (le_of_max_le_right enough), inner, innerSame _ (le_max_right _ _), inner]
      | some innerView =>
          obtain ⟨t₃, through⟩ := (throughTwo_const outerView innerView problem
            (fun fuel {_} older newer stored => exchangeSolve facts roots heads algebra declared choices reducer fuel
              (fun exchanged => codomainRule facts roots heads algebra rigid complete declared choices reducer root
                normalizes certifyNormal headTypingUnique fuel exchanged) older newer stored)
            (fun older newer stored => exchangeSolve_const facts roots heads algebra declared choices reducer stable
              (fun fuel {_} exchanged => codomainRule facts roots heads algebra rigid complete declared choices reducer
                root normalizes certifyNormal headTypingUnique fuel exchanged)
              (fun stored => codomainRule_const facts roots heads algebra rigid complete declared choices reducer root
                normalizes certifyNormal headTypingUnique stable stored) older newer stored)).spec
          refine ⟨max t₁ (max t₂ t₃), fun fuel enough => ?_⟩
          have e₁ : t₁ ≤ fuel := by omega
          have e₂ : t₂ ≤ fuel := by omega
          have e₃ : t₃ ≤ fuel := by omega
          dsimp only
          unfold exchangedRule
          erw [outerSame fuel e₁, outer, outerSame _ (by omega), outer]
          dsimp only
          erw [innerSame fuel e₂, inner, innerSame _ (by omega), inner]
          dsimp only
          exact (through fuel e₃).trans (through _ (by omega)).symm

include stable in
/-- **The prune-and-solve rule is eventually constant on every store.** -/
theorem pruneSolveRule_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      pruneSolveRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel problem := by
  obtain ⟨t₁, first⟩ := (codomainRule_const facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique stable problem).spec
  obtain ⟨t₂, later⟩ := (exchangedRule_const facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique stable problem).spec
  refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
  dsimp only
  unfold pruneSolveRule
  erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
    later _ (le_max_right _ _)]

theorem pruneSolveRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (pruneSolveRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (intersectRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (ContextualDependentPatternFiring.foundView (pruneSolveRule facts roots heads algebra rigid complete declared
          choices reducer root normalizes certifyNormal headTypingUnique fuel problem)) := by
  unfold pruneSolveRound
  cases intersectRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      cases pruneSolveRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique fuel problem with
      | some found =>
          cases found with
          | solved update smaller => rfl
          | refuted absent => rfl
      | none => rfl
  | progress update smaller => rfl
  | refuted absent => rfl

include stable in
/-- **The prune-and-solve round is eventually constant on every store.** -/
theorem pruneSolveRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => pruneSolveRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => pruneSolveRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (intersectRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (EventuallyConst.comp ContextualDependentPatternFiring.foundView (pruneSolveRule_const facts roots heads algebra
        rigid complete declared choices reducer root normalizes certifyNormal headTypingUnique stable problem)))

include stable in
/-- **The prune-and-solve family settles** on every class of stores on which, at each nonempty store and from some
budget on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def pruneSolveSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        pruneSolveRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          pruneSolveRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (pruneSolveFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => pruneSolveRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentPruneSolve
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
