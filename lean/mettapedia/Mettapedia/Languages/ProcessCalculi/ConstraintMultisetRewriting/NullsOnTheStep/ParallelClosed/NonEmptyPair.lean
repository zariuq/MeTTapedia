import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Separation

/-!
# The separation without the empty store

The separating pair of `StepSource` has the empty store as one part, so homomorphism there forces
the image of the empty store to act as a unit beside the image of the store holding `U`. A second
absence-guarded program separates on a pair of non-empty stores: it replaces `spawn` by a rule that
needs a trigger. The statements below are about that program, not about `spawn` and `tick`.

The program `program'`: `fire` (take the trigger `V`, make `T` where `U` is absent) and `tick` (read
`U`, make `W`). `source'` composes only **composable pairs of non-empty stores**
(`NonEmptyComposable`).

* `trigger_succeeds`: the store holding `V` succeeds; `trigger_blocked`: beside the store holding
  `U` no run ever makes `T`.
* `source'_switchable`, hence `no_uniformTranslation_presentation'` and
  `no_uniformTranslation_rho'`: no translation homomorphic on parallel composition **for pairs of
  non-empty stores**, preserving and reflecting reachable success, goes into any presentation with a
  parallel context rule or into the reduction of any rho rule set.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed

open NamesOnTheStep NamesOnTheStep.IssuingControls
open MeTTaCalculus.OccurrenceCommits (fire mem_fire)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Composition
  (unionOf)

/-- The trigger row `V`. -/
def trigger : Expr := .sym 16

/-- `fire`: take `V`, make `T` where `U` is absent. -/
def fireRule : RuleInstance Expr := rule [trigger] [] [factT] [.predicate .none factU]

/-- **The program with a trigger**: `fire` and `tick`. -/
def program' (r : RuleInstance Expr) : Prop := r = fireRule ∨ r = tick

/-- Composable pairs of non-empty stores. -/
def NonEmptyComposable (C D : Conf) : Prop :=
  Composable ground C D ∧ C.present.Nonempty ∧ D.present.Nonempty

/-- The step under the program with a trigger, composing only non-empty stores. -/
def source' : ParallelCalculus :=
  { stepCalculus ground (Prod.fst : Occ → Expr) program' (· = factT) with
    composable := NonEmptyComposable }

/-- The store holding `V`. -/
def triggerStore : Conf := ⟨[], {(trigger, 0)}⟩

/-- `fire`, taking the trigger and making `T` with copy number `0`. -/
def fireAt : Fir := ⟨fireRule, [], ⟨[(trigger, 0)], [], [(factT, 0)]⟩⟩

theorem program'_keeps : ∀ r, program' r → factU ∉ r.take := by
  rintro r (rfl | rfl) <;> simp [fireRule, tick, rule, trigger, factU]

theorem program'_guards :
    ∀ r, program' r → factT ∈ r.produce → Check.predicate .none factU ∈ r.checks := by
  rintro r (rfl | rfl) made
  · simp [fireRule, rule]
  · simp [tick, rule, factT, factW] at made

/-- **The store holding the trigger succeeds.** -/
theorem trigger_succeeds : source'.Succeeds triggerStore := by
  have admitted : base.Admits (s := triggerStore) fireAt := by
    refine (admits_of (D := fun _ _ _ _ => True) (σ := (triggerStore, ∅)) (fresh := [])
      (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl ?_ trivial).1
    intro c member
    simp only [fireRule, rule, List.mem_singleton] at member
    subst member
    exact absent_holds (by decide)
  refine ⟨_, .single ⟨fireAt, Or.inl rfl, admitted, rfl⟩, (factT, 0), ?_, rfl⟩
  change (factT, 0) ∈ fire triggerStore.present (fireAt.selection.commit (T := Expr))
  rw [mem_fire]
  exact Or.inr (by simp [fireAt, Selection.commit])

/-- **Beside the store holding `U`, no run ever makes `T`.** -/
theorem trigger_blocked : ¬ source'.Succeeds (unionOf triggerStore blocker) :=
  never_succeeds_of_blocker program'_keeps program'_guards ⟨(factU, 0), by decide, rfl⟩
    (by decide)

/-- The two stores are non-empty and composable. -/
theorem trigger_blocker_composable : source'.composable triggerStore blocker :=
  ⟨⟨by decide, ⟨(), fun _ member => absurd member List.not_mem_nil⟩⟩, ⟨(trigger, 0), by decide⟩,
    ⟨(factU, 0), by decide⟩⟩

/-- **Switchable on a pair of non-empty stores.** -/
theorem source'_switchable : source'.Switchable :=
  ⟨triggerStore, blocker, trigger_blocker_composable, trigger_succeeds, trigger_blocked⟩

/-- **No translation homomorphic on pairs of non-empty stores** into any presentation with a parallel
context rule, modulo its equations. -/
theorem no_uniformTranslation_presentation' {base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator}
    {language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    {kind : Mettapedia.OSLF.MeTTaIL.Syntax.CollType} (has : HasParallelContextRule kind language)
    (ω : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    IsEmpty (UniformTranslation source' (presentationCalculus base language kind ω)) :=
  isEmpty_uniformTranslation source'_switchable (presentationCalculus_persistent has ω)

section Rho

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres

/-- **No translation homomorphic on pairs of non-empty stores** into the reduction of any rho rule
set. -/
theorem no_uniformTranslation_rho' {Index : Type*} (rules : Index → RhoScopedParallelEvents.ProcessRule)
    (admitted : Index → Prop) (context : Ctx sig) (c : Process context) :
    IsEmpty (UniformTranslation source' (rhoCalculus rules admitted context c)) :=
  isEmpty_uniformTranslation source'_switchable (rhoCalculus_persistent rules admitted context c)

end Rho

#print axioms trigger_succeeds
#print axioms trigger_blocked
#print axioms trigger_blocker_composable
#print axioms source'_switchable
#print axioms no_uniformTranslation_presentation'
#print axioms no_uniformTranslation_rho'

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
