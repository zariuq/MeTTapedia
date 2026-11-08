import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInPlaceRounds

/-!
# An in-place answer found at one budget is kept

When, at one budget, every equation of a store strengthens past the newest declaration, the
separation is the same at every larger budget. When moreover the newest declaration is read and the
rule on the strengthened store keeps its result, the in-place rule at the next depth keeps its
result too (`inPlaceAt_succ_kept`). At depth `0` the rule is the pattern rule whenever that fires
(`inPlaceAt_zero_kept`).

The in-place round keeps its result once the Π round is stuck at every larger budget, preparation
is fixed, and the in-place rule keeps its result (`inPlaceRound_kept`). The firmness test
`strengthenFirm` is a boolean the kernel evaluates.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentInPlace

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentConversionBudget

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

/-- **Every equation of the store strengthens at this budget**, on both sides. -/
def strengthenFirm (budget : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ type))) : Bool :=
  problem.all fun equation =>
    (strengthen facts roots heads algebra declared choices reducer budget type equation.1).isSome &&
      (strengthen facts roots heads algebra declared choices reducer budget type equation.2).isSome

include stable in
/-- **A separation in which every equation strengthened is kept.** -/
theorem separate_kept {Γ : Context S.R} (type : TypeOver Γ) :
    ∀ (problem : EquationStore (TotalTerm (extend Γ type))) {budget : Nat},
      strengthenFirm facts roots heads algebra declared choices reducer budget type problem = true →
      ∀ larger, budget ≤ larger →
        separate facts roots heads algebra declared choices reducer larger type problem =
          separate facts roots heads algebra declared choices reducer budget type problem
  | [], _, _ => fun _ _ => rfl
  | equation :: rest, budget, firm => by
      intro larger enough
      simp only [strengthenFirm, List.all_cons, Bool.and_eq_true] at firm
      obtain ⟨⟨leftSome, rightSome⟩, restFirm⟩ := firm
      obtain ⟨left, leftRun⟩ := Option.isSome_iff_exists.mp leftSome
      obtain ⟨right, rightRun⟩ := Option.isSome_iff_exists.mp rightSome
      have restKept := separate_kept type rest (budget := budget) restFirm larger enough
      simp only [separate]
      rw [strengthen_mono facts roots heads algebra declared choices reducer stable leftRun enough,
        strengthen_mono facts roots heads algebra declared choices reducer stable rightRun enough, leftRun, rightRun,
        restKept]

include stable in
theorem separation_kept {Γ : Context S.R} (type : TypeOver Γ) (problem : EquationStore (TotalTerm (extend Γ type)))
    {budget : Nat} (firm : strengthenFirm facts roots heads algebra declared choices reducer budget type problem = true) :
    ∀ larger, budget ≤ larger →
      separation facts roots heads algebra declared choices reducer larger type problem =
        separation facts roots heads algebra declared choices reducer budget type problem :=
  fun larger enough => Subtype.ext
    (separate_kept facts roots heads algebra declared choices reducer stable type problem firm larger enough)

include stable in
/-- **The in-place rule at the next depth is kept** once the newest declaration is read, the
separation is kept, and the rule on the strengthened store is kept. -/
theorem inPlaceAt_succ_kept {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (depth : Nat) {budget : Nat}
    {view : Newest Θ}
    (read : newestOf facts roots heads algebra declared choices reducer budget Θ = some view)
    (separated : ∀ larger, budget ≤ larger →
      separation facts roots heads algebra declared choices reducer larger view.type (view.same ▸ problem) =
        separation facts roots heads algebra declared choices reducer budget view.type (view.same ▸ problem))
    (inner : ∀ larger, budget ≤ larger →
      inPlaceAt facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique larger depth
          (separation facts roots heads algebra declared choices reducer budget view.type (view.same ▸ problem)).val.1 =
        inPlaceAt facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique budget depth
          (separation facts roots heads algebra declared choices reducer budget view.type (view.same ▸ problem)).val.1) :
    ∀ larger, budget ≤ larger →
      inPlaceAt facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique larger (depth + 1) problem =
        inPlaceAt facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique budget (depth + 1) problem := by
  intro larger enough
  simp only [inPlaceAt]
  rw [newestOf_kept facts roots heads algebra declared choices reducer stable read larger enough, read]
  dsimp only
  apply throughNewest_eq
  have carried : ∀ first second : {pair : EquationStore (TotalTerm view.base) ×
        EquationStore (TotalTerm (extend view.base view.type)) //
        (frames S.levels).Equivalent (view.same ▸ problem)
          (pair.2 ++ (frames S.levels).applyStore (projectionHom view.base view.type) pair.1)},
      first = second →
        (inPlaceAt facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique larger depth first.val.1).map (carry view.type first.property) =
        (inPlaceAt facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique larger depth second.val.1).map (carry view.type second.property) := by
    rintro _ _ rfl
    rfl
  exact (carried _ _ (separated larger enough)).trans (congrArg (Option.map _) (inner larger enough))

/-- **At depth `0` the in-place rule is the pattern rule** whenever that fires and is kept. -/
theorem inPlaceAt_zero_kept {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) {budget : Nat}
    {found : Found problem}
    (patternKept : ∀ larger, budget ≤ larger →
      patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal larger
          problem =
        patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal budget
          problem)
    (fires : patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      budget problem = some found) :
    ∀ larger, budget ≤ larger →
      inPlaceAt facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique larger 0 problem = some found := by
  intro larger enough
  simp only [inPlaceAt]
  unfold firstRule
  rw [patternKept larger enough, fires]

/-- The search through the depths returns what the first depth keeps. -/
theorem inPlaceSearch_head_kept {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (depth : Nat)
    (rest : List Nat) {budget : Nat} {found : Found problem}
    (kept : ∀ larger, budget ≤ larger →
      inPlaceAt facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique larger depth problem = some found) :
    ∀ larger, budget ≤ larger →
      inPlaceSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique larger problem (depth :: rest) = some found := by
  intro larger enough
  simp only [inPlaceSearch]
  rw [kept larger enough]

/-- **The in-place round is kept** once the Π round is stuck at every larger budget, preparation is
fixed and the in-place rule on the prepared store keeps its result. -/
theorem inPlaceRound_kept {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) {budget : Nat}
    (piStuck : ∀ larger, budget ≤ larger →
      piRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete larger problem = .stuck)
    (prepared : ∀ larger, budget ≤ larger →
      ContextualDependentNormalizing.prepare root rootComplete facts roots heads larger problem =
        ContextualDependentNormalizing.prepare root rootComplete facts roots heads budget problem)
    (ruleKept : ∀ larger, budget ≤ larger →
      inPlaceRule facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique larger
          (ContextualDependentNormalizing.prepare root rootComplete facts roots heads budget problem).remaining =
        inPlaceRule facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique budget
          (ContextualDependentNormalizing.prepare root rootComplete facts roots heads budget problem).remaining) :
    ∀ larger, budget ≤ larger →
      inPlaceRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique rootComplete larger problem =
        inPlaceRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique rootComplete budget problem := by
  intro larger enough
  apply roundView_injective
  rw [inPlaceRound_view, inPlaceRound_view, piStuck larger enough, piStuck budget le_rfl, prepared larger enough,
    ruleKept larger enough]

end ContextualDependentInPlace
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
