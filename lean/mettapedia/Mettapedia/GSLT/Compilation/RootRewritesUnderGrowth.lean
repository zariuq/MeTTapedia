import Mettapedia.GSLT.Compilation.RootRewritesOnTheStep
import Mettapedia.GSLT.Core.OperationalColimitRuns
import Mettapedia.GSLT.Core.OperationalColimitStageEquality
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Growing root languages on the transform step

A language that grows by rules is a diagram of operational theories, the identity
on terms. If each stage compiles, the colimit reaches a term exactly when the
transform program of some stage reaches a state that reads as it
(`reaches_iff_transform_stage`). Appending rules appends schemas
(`lowerRules_append`).

Growth is by rules alone. Equations, removed rules and observations of absence
need maps and observations of their own.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.RootRewritesUnderGrowth

open _root_.CategoryTheory
open scoped _root_.CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.IndexedOperational.OperationalColimits (inject inject_along run_from_stage_iff
  inject_eq_iff_eventually_equal)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax
open RuleSyntax.Presentation.Schematic
open RuleSyntax.Machines
open RootRewritesOnTheStep

/-- A language that grows by rules, as a diagram. -/
def growing (relEnv : RelationEnv) (stage : ℕ → LanguageDef)
    (grows : ∀ {first later}, first ≤ later → ∀ rule, rule ∈ (stage first).rewrites → rule ∈ (stage later).rewrites) :
    ℕ ⥤ OperationalTheory.{0} where
  obj index := ⟨sourceSystem relEnv (stage index)⟩
  map route :=
    { mapTerm := _root_.id
      mapEquiv := fun same => same
      mapStep := fun stepped => Step.mono_rules (grows (leOfHom route)) stepped }
  map_id _ := by
    apply OperationalTranslation.ext
    rfl
  map_comp _ _ := by
    apply OperationalTranslation.ext
    rfl

variable {relEnv : RelationEnv} {stage : ℕ → LanguageDef}
  {grows : ∀ {first later}, first ≤ later → ∀ rule, rule ∈ (stage first).rewrites → rule ∈ (stage later).rewrites}

/-- Transport is the identity, so equal images are equal terms. -/
theorem inject_eq_iff (index : ℕ) (term target : Pattern) :
    inject (growing relEnv stage grows) index term = inject (growing relEnv stage grows) 0 target ↔ term = target := by
  constructor
  · intro same
    obtain ⟨_, _, _, equal⟩ := (inject_eq_iff_eventually_equal _ _ _).mp same
    exact equal
  · rintro rfl
    exact (inject_along (growing relEnv stage grows) (homOfLE (Nat.zero_le index)) term).symm

/-- A state reads as one row only. -/
theorem readsRow_unique {O : Type} [DecidableEq O] [Infinite O] {state : SState O} {first second : Expr}
    (left : ReadsBag state {first}) (right : ReadsBag state {second}) : first = second := by
  obtain ⟨⟨solution, solved⟩, leftAs⟩ := left.readsAs
  have mapped := (leftAs solution solved).symm.trans (right.readsAs.2 solution solved)
  simp only [Multiset.map_singleton, Multiset.singleton_inj] at mapped
  exact toTerm_injective mapped

/-- **The growing language and the transform step of its compiled stages.** -/
theorem reaches_iff_transform_stage {O : Type} [DecidableEq O] [Infinite O] {schemas : ℕ → List (Tm × Tm)}
    (compiles : ∀ index, compile (stage index) = .ok (schemas index)) {source : Pattern} (target : Pattern)
    {start : SState O} (reads : ReadsBag start {encode source}) :
    (OperationalColimits.theory (growing relEnv stage grows)).MultiStep
        (inject (growing relEnv stage grows) 0 source) (inject (growing relEnv stage grows) 0 target) ↔
      ∃ index final, (stepSystem O (rootRules (schemas index))).MultiStep start final ∧
        ReadsBag final {encode target} := by
  have lifted := run_from_stage_iff (growing relEnv stage grows)
    (fun index => stepSystem O (rootRules (schemas index)))
    (fun index => RootRewritesOnTheStep.stepCorrespondence relEnv (compiles index))
    (fun finish => finish = inject (growing relEnv stage grows) 0 target)
    (fun _ state => ReadsBag state {encode target})
    (by
      rintro index origin current ⟨row, rfl, bag, rfl, originReads⟩
      refine (inject_eq_iff index origin target).trans ⟨?_, fun targetReads => ?_⟩
      · rintro rfl
        exact originReads
      · exact encode_injective (readsRow_unique originReads targetReads))
    (site := (0 : ℕ)) source (fun _ _ => start)
    (fun _ _ => ⟨_, rfl, _, rfl, reads⟩)
  constructor
  · intro path
    obtain ⟨index, _, final, run, finalReads⟩ := lifted.mp ⟨_, path, rfl⟩
    exact ⟨index, final, run, finalReads⟩
  · rintro ⟨index, final, run, finalReads⟩
    obtain ⟨finish, path, same⟩ := lifted.mpr ⟨index, homOfLE (Nat.zero_le index), final, run, finalReads⟩
    cases same
    exact path

/-- Appending rules appends schemas. -/
theorem lowerRules_append {first second : List RewriteRule} {left right : List (Tm × Tm)}
    (firstLowered : lowerRules first = .ok left) (secondLowered : lowerRules second = .ok right) :
    lowerRules (first ++ second) = .ok (left ++ right) := by
  induction first generalizing left with
  | nil =>
    simp only [lowerRules, Except.ok.injEq] at firstLowered
    subst firstLowered
    simpa using secondLowered
  | cons rule rest ih =>
    cases one : lowerRule rule with
    | error reason => simp [lowerRules, one] at firstLowered
    | ok schema =>
      cases more : lowerRules rest with
      | error reason => simp [lowerRules, one, more] at firstLowered
      | ok schemas =>
        simp only [lowerRules, one, more, Except.ok.injEq] at firstLowered
        subst firstLowered
        simp [lowerRules, one, ih more]

/-! ## Controls -/

namespace Controls

open RootRewritesOnTheStep.Controls (choice choice_compiles choice_step_iff)

/-- A property kept by every step is kept by every finite run. -/
theorem multiStep_kept {S : GSLT} {kept_ : S.Term → Prop}
    (kept : ∀ first next, kept_ first → S.Step first next → kept_ next) :
    ∀ {first last : S.Term}, S.MultiStep first last → kept_ first → kept_ last
  | _, _, .refl _, holds => holds
  | _, _, .step stepped rest, holds => multiStep_kept kept rest (kept _ _ holds stepped)

/-- No rule at stage 0, both rules of `Choice` from stage 1 on. -/
def learning : ℕ → LanguageDef
  | 0 => { choice with rewrites := [] }
  | _ + 1 => choice

theorem learning_grows {first later : ℕ} (le : first ≤ later) :
    ∀ rule, rule ∈ (learning first).rewrites → rule ∈ (learning later).rewrites := by
  cases first with
  | zero =>
    intro rule member
    simp [learning] at member
  | succ first =>
    cases later with
    | zero => omega
    | succ later => exact fun _ member => member

theorem learning_compiles : ∃ schemas : ℕ → List (Tm × Tm),
    ∀ index, compile (learning index) = .ok (schemas index) := by
  obtain ⟨schemas, compiled⟩ := choice_compiles
  refine ⟨fun | 0 => [] | _ + 1 => schemas, fun index => ?_⟩
  cases index with
  | zero => rfl
  | succ index => exact compiled

def left : Pattern := .apply "Left" []
def right : Pattern := .apply "Right" []
def other : Pattern := .apply "Other" []
def question : Pattern := .apply "Choose" [left, right]

/-- **Negative at the stage**: stage 0 has no step. -/
theorem initial_stuck (source target : Pattern) :
    ¬ Step (engineBasePremises relEnv) (learning 0) source target := by
  intro stepped
  obtain ⟨_, member, _⟩ := rootStep_of_step (schemas := []) rfl stepped
  cases member

/-- **Positive under growth**: the same query is answered in the colimit. -/
theorem later_answers :
    (OperationalColimits.theory (growing relEnv learning learning_grows)).MultiStep
      (inject (growing relEnv learning learning_grows) 0 question)
      (inject (growing relEnv learning learning_grows) 0 left) := by
  apply (OperationalColimits.multiStep_from_stage_iff _ _ _).mpr
  exact ⟨1, homOfLE (Nat.zero_le 1), left,
    .step ((choice_step_iff left right left).mpr (Or.inl rfl)) (.refl _),
    (inject_eq_iff 1 left left).mpr rfl⟩

/-- **Negative in the colimit**: growth adds no third answer. -/
theorem never_other :
    ¬ (OperationalColimits.theory (growing relEnv learning learning_grows)).MultiStep
      (inject (growing relEnv learning learning_grows) 0 question)
      (inject (growing relEnv learning learning_grows) 0 other) := by
  intro path
  obtain ⟨index, _, after, run, same⟩ := (OperationalColimits.multiStep_from_stage_iff _ _ _).mp path
  obtain rfl := (inject_eq_iff index after other).mp same
  have kept : ∀ {first next : Pattern}, first ∈ [question, left, right] →
      Step (engineBasePremises relEnv) (learning index) first next → next ∈ [question, left, right] := by
    intro first next member stepped
    cases index with
    | zero => exact (initial_stuck first next stepped).elim
    | succ index =>
      obtain ⟨schemas, compiled⟩ := choice_compiles
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · rcases (choice_step_iff left right next).mp stepped with rfl | rfl <;> simp
      all_goals
        obtain ⟨rule, declared, bindings, matched, _⟩ :=
          (Mettapedia.OSLF.MeTTaIL.ContextualStep.step_iff_exists_match (compile_plain compiled)).mp stepped
        simp only [choice, List.mem_cons, List.not_mem_nil, or_false] at declared
        rcases declared with rfl | rfl <;>
          simp [RootRewritesOnTheStep.Controls.chooseFirst, RootRewritesOnTheStep.Controls.chooseSecond,
            Mettapedia.OSLF.MeTTaIL.Match.matchPattern, left, right] at matched
  have member := multiStep_kept (S := sourceSystem relEnv (learning index))
    (kept := fun first next => kept (first := first) (next := next)) run (List.mem_cons_self ..)
  simp [question, left, right, other] at member

end Controls

end Mettapedia.GSLT.Compilation.RootRewritesUnderGrowth

#print axioms Mettapedia.GSLT.Compilation.RootRewritesUnderGrowth.reaches_iff_transform_stage
#print axioms Mettapedia.GSLT.Compilation.RootRewritesUnderGrowth.lowerRules_append
#print axioms Mettapedia.GSLT.Compilation.RootRewritesUnderGrowth.Controls.initial_stuck
#print axioms Mettapedia.GSLT.Compilation.RootRewritesUnderGrowth.Controls.later_answers
#print axioms Mettapedia.GSLT.Compilation.RootRewritesUnderGrowth.Controls.never_other
