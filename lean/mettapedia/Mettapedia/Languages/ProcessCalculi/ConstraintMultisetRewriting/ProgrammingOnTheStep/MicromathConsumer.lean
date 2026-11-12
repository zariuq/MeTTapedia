import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.MicromathSoundness

/-!
# The Micromath consumer: a run, its theorem, and a model

Micromath's six rules run on the first-order step with a ledger of issued names
(`NamesOnTheStep.MicromathSoundness.mm`), and every theorem a run stores that mentions no issued
name is true in every model whose codes `X` and `Y` denote the projections (`mm_valid`). This module
exercises that consumer at both ends.

* **A run** (`reflRun`): from the empty store, the rule `refl` fires with `a := X` and stores the
  theorem `X = X(X, Y)`; it issues nothing.
* **Its theorem** (`refl_run_valid`): `mm_valid` applies to that run, so the stored theorem holds in
  every model of the codes.
* **A model** (`boolModel_projections`): the class of models is inhabited, on a two-element domain;
  in it the theorem `X = Y(X, Y)` is false (`boolModel_refutes`). So the theory hosted by the rules
  has a model, and does not prove every theorem; this is a semantic fact about the declared rules,
  established by a model, not by agreement of an executable checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ProgrammingOnTheStep.MicromathConsumer

open NamesOnTheStep NamesOnTheStep.IssuingControls NamesOnTheStep.CodeOnlyLoading
open NamesOnTheStep.MicromathSoundness

/-- Every hole of the rule is `X`. -/
def allX : ℕ → Expr := fun _ => projX

/-- The stored theorem `X = X(X, Y)`. -/
def reflTheorem : Expr := thmTerm projX projX projX projY

/-- **The firing**: `refl` at `a := X`, making the theorem as occurrence `0`, issuing nothing. -/
def reflFiring : Fir × List ℕ := (⟨refl.inst allX, [], ⟨[], [], [(reflTheorem, 0)]⟩⟩, [])

theorem refl_writes_nothing (n : ℕ)
    (written : n ∈ firingNames Expr.names (⟨refl.inst allX, [], ⟨[], [], [(reflTheorem, 0)]⟩⟩ : Fir)) :
    False := by
  obtain ⟨_, _, _, _, held⟩ :=
    codeOnly_writes (micromath_codeOnly refl (by simp [micromath])) allX [] _ written
  change n ∈ (Expr.sym 0).support at held
  simp at held

/-- **The firing is admitted by Micromath on the step.** -/
theorem refl_admitted : mm.Admits (s := emptyStart) reflFiring := by
  refine admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
    ⟨⟨List.nodup_nil, fun _ member => absurd member List.not_mem_nil, fun n written => ?_⟩,
      Or.inr (Or.inr (Or.inl ⟨allX, rfl, rfl⟩))⟩
  exact (refl_writes_nothing n written).elim

/-- **The run** of the one firing. -/
def reflRun : mm.Run emptyStart := .cons reflFiring refl_admitted (.nil _)

/-- The run stores the theorem. -/
theorem reflRun_stores : (reflTheorem, 0) ∈ reflRun.last.1.present := by
  show (reflTheorem, 0) ∈ (mm.result (s := emptyStart) reflFiring refl_admitted).1.present
  decide

/-- The run issues no name. -/
theorem reflRun_issues_nothing : issuedAlong reflRun = [] := rfl

/-- **The consumer's soundness theorem applies to the run**: the stored theorem holds in every model
of the codes. -/
theorem refl_run_valid {D : Type} (ι : Expr → D → D → D) (projections : Projections ι) :
    ∀ a b, ι projX a b = ι projX (ι projX a b) (ι projY a b) :=
  mm_valid reflRun ι projections reflRun_stores rfl
    (fun n member => by rw [reflRun_issues_nothing] at member; exact absurd member List.not_mem_nil)

/-! ## A model -/

/-- The model on `Bool`: `X` and `Y` the projections, every other symbol the first projection. -/
def boolModel : Expr → Bool → Bool → Bool :=
  fun e a b => if e = projY then b else a

theorem boolModel_projections : Projections boolModel := by
  refine ⟨?_, ?_⟩
  · funext a b
    have : projX ≠ projY := by decide
    simp [boolModel, this]
  · funext a b
    simp [boolModel]

/-- **The model refutes `X = Y(X, Y)`**: the theory has a model and does not prove every theorem. -/
theorem boolModel_refutes :
    ¬ ∀ a b, boolModel projX a b = boolModel projY (boolModel projX a b) (boolModel projY a b) := by
  intro all
  have := all true false
  have distinct : projX ≠ projY := by decide
  simp [boolModel, distinct] at this

end ProgrammingOnTheStep.MicromathConsumer

#print axioms ProgrammingOnTheStep.MicromathConsumer.refl_admitted
#print axioms ProgrammingOnTheStep.MicromathConsumer.reflRun_stores
#print axioms ProgrammingOnTheStep.MicromathConsumer.refl_run_valid
#print axioms ProgrammingOnTheStep.MicromathConsumer.boolModel_projections
#print axioms ProgrammingOnTheStep.MicromathConsumer.boolModel_refutes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
