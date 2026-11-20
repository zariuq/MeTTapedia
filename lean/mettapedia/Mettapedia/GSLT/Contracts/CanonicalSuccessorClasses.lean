import Mettapedia.GSLT.Dynamics.ProtocolModuloEquations

/-!
# Canonical representatives of a one-step quotient

Static equations act before and after a raw transition. A canonical
representative can be used directly exactly when each raw transition
has an equivalent successor from the canonical source. Merely having
unique representatives of the equations is not that hypothesis.

This is an endpoint observation: membership in the set of successor
classes. The underlying modulo-equations occurrences still retain
raw receipts. Neither their multiplicity nor the order of a selection
policy is inferred from endpoint equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.CanonicalSuccessorClasses

open Mettapedia.GSLT.Dynamics.ProtocolModuloEquations (Occurrence)

universe u v

variable {State : Type u}

/-- One canonical representative per independently specified equation
class. The static equations are not generated from raw transitions. -/
structure NormalForms (equations : Setoid State) where
  normal : State → State
  sound : ∀ state, equations.r (normal state) state
  same : ∀ {first second : State}, equations.r first second → normal first = normal second

namespace NormalForms

variable {equations : Setoid State} (forms : NormalForms equations)

theorem idempotent (state : State) : forms.normal (forms.normal state) = forms.normal state :=
  forms.same (forms.sound state)

abbrev Key := {state : State // forms.normal state = state}

def key (state : State) : forms.Key :=
  ⟨forms.normal state, forms.idempotent state⟩

theorem key_eq_iff {first second : State} :
    forms.key first = forms.key second ↔ equations.r first second := by
  constructor
  · intro equal
    have values := congrArg Subtype.val equal
    change forms.normal first = forms.normal second at values
    exact equations.iseqv.trans (equations.iseqv.symm (forms.sound first))
      (values ▸ forms.sound second)
  · intro same
    exact Subtype.ext (forms.same same)

/-- Semantic equation classes and their chosen keys have the same
elements. Any additional operational requirement belongs to the
transition relation, not to this equivalence. -/
def classEquiv : Quotient equations ≃ forms.Key where
  toFun := Quotient.lift forms.key (fun _ _ eq => forms.key_eq_iff.mpr eq)
  invFun k := Quotient.mk _ k.val
  left_inv c := Quotient.inductionOn c (fun state =>
    Quotient.sound (s := equations) (forms.sound state))
  right_inv k := Subtype.ext k.property

end NormalForms

variable {equations : Setoid State} (forms : NormalForms equations)
  (Raw : State → State → Type v)

/-- The already-defined modulo-equations occurrence, observed at its endpoints. -/
abbrev Modulo (source target : State) : Prop := Nonempty (Occurrence equations Raw source target)

/-- Run a raw transition *at the canonical source*, then normalize its
destination. No search over pre-representatives is hidden here. -/
def CanonicalStep (source target : forms.Key) : Prop :=
  ∃ result, Nonempty (Raw source.val result) ∧ forms.key result = target

/-- The required one-step coherence diamond, not a many-step joinability
condition and not merely equality of normal forms after saturation. -/
def Coherent : Prop :=
  ∀ source target, Nonempty (Raw source target) →
    ∃ result, Nonempty (Raw (forms.normal source) result) ∧ equations.r result target

theorem sound {source target : State}
    (step : CanonicalStep forms Raw (forms.key source) (forms.key target)) :
    Modulo (equations := equations) Raw source target := by
  obtain ⟨result, ⟨receipt⟩, observed⟩ := step
  exact ⟨⟨forms.normal source, result, equations.iseqv.symm (forms.sound source), receipt,
    (forms.key_eq_iff).mp observed⟩⟩

theorem complete (coherent : Coherent forms Raw) {source target : State}
    (step : Modulo (equations := equations) Raw source target) :
    CanonicalStep forms Raw (forms.key source) (forms.key target) := by
  obtain ⟨receipt⟩ := step
  obtain ⟨result, raw, agrees⟩ := coherent receipt.redex receipt.contractum ⟨receipt.receipt⟩
  have sameSource := forms.same receipt.sourceEquation
  refine ⟨result, ?_, (forms.key_eq_iff).mpr (equations.iseqv.trans agrees receipt.targetEquation)⟩
  change Nonempty (Raw (forms.normal source) result)
  rw [sameSource]
  exact raw

/-- An exact criterion for stepping only the chosen representatives. -/
theorem exact_iff_coherent :
    (∀ source target, CanonicalStep forms Raw (forms.key source) (forms.key target) ↔
      Modulo (equations := equations) Raw source target) ↔ Coherent forms Raw := by
  constructor
  · intro exactSteps source target ⟨raw⟩
    obtain ⟨result, after, observed⟩ :=
      (exactSteps source target).mpr ⟨Occurrence.ofRaw raw⟩
    exact ⟨result, after, (forms.key_eq_iff).mp observed⟩
  · exact fun coherent _ _ => ⟨sound forms Raw, complete forms Raw coherent⟩

/-- If a finite enumeration is exact at the raw canonical source, its
normalized answers contain precisely all quotient successor classes.
No assumption is made about how the raw enumeration performs matching. -/
theorem enumerate_iff_modulo (coherent : Coherent forms Raw)
    (enumerate : forms.Key → List State)
    (exactRaw : ∀ source target, target ∈ enumerate source ↔ Nonempty (Raw source.val target))
    (source target : State) :
    forms.key target ∈ (enumerate (forms.key source)).map forms.key ↔
      Modulo (equations := equations) Raw source target := by
  rw [← ((exact_iff_coherent forms Raw).mpr coherent) source target]
  simp only [CanonicalStep, List.mem_map, exactRaw]

/-- Equating the endpoints of all directed steps identifies the two arms
of every fork, whether or not the arms admit any further steps. -/
theorem merge_identifies_fork (stateEquations : Setoid State)
    (merge : ∀ source target, Nonempty (Raw source target) → stateEquations.r source target)
    {source left right : State} (first : Raw source left) (second : Raw source right) :
    stateEquations.r left right :=
  stateEquations.iseqv.trans (stateEquations.iseqv.symm (merge _ _ ⟨first⟩))
    (merge _ _ ⟨second⟩)

namespace Controls

private inductive StateCase where
  | normal | alternate | done

private def normalize : StateCase → StateCase
  | .alternate => .normal
  | state => state

private def equationsCase : Setoid StateCase := Setoid.ker normalize

private def formsCase : NormalForms equationsCase where
  normal := normalize
  sound state := by cases state <;> rfl
  same := id

private inductive OnlyAlternate : StateCase → StateCase → Type
  | step : OnlyAlternate .alternate .done

/-- Correct static representatives do not ensure an exact transition rule. -/
theorem omitted_redex_loses_a_successor :
    Modulo (equations := equationsCase) OnlyAlternate .normal .done ∧
      ¬ CanonicalStep formsCase OnlyAlternate (formsCase.key .normal) (formsCase.key .done) := by
  constructor
  · exact ⟨⟨.alternate, .done, rfl, .step, rfl⟩⟩
  · rintro ⟨result, ⟨impossible⟩, _⟩
    cases impossible

private inductive BothRepresentatives : StateCase → StateCase → Type
  | fromNormal : BothRepresentatives .normal .done
  | fromAlternate : BothRepresentatives .alternate .done

theorem completed_representatives_have_exact_successors :
    ∀ source target, CanonicalStep formsCase BothRepresentatives
      (formsCase.key source) (formsCase.key target) ↔
      Modulo (equations := equationsCase) BothRepresentatives source target :=
  (exact_iff_coherent formsCase BothRepresentatives).mpr (by
    rintro _ _ ⟨raw⟩
    cases raw <;> exact ⟨.done, ⟨.fromNormal⟩, rfl⟩)

private inductive Fork where
  | start | left | right

private inductive ForkStep : Fork → Fork → Type
  | left : ForkStep .start .left
  | right : ForkStep .start .right

theorem merging_a_terminal_fork_erases_a_distinction :
    Fork.left ≠ Fork.right ∧
      (∀ target, ¬ Nonempty (ForkStep .left target)) ∧
      (∀ target, ¬ Nonempty (ForkStep .right target)) ∧
      ∀ relation : Setoid Fork,
        (∀ source target, Nonempty (ForkStep source target) → relation.r source target) →
          relation.r .left .right := by
  have different : Fork.left ≠ Fork.right := by intro same; cases same
  refine ⟨different, ?_, ?_, ?_⟩
  · rintro target ⟨step⟩
    cases step
  · rintro target ⟨step⟩
    cases step
  · intro relation merges
    exact merge_identifies_fork ForkStep relation merges .left .right

end Controls

#print axioms exact_iff_coherent
#print axioms enumerate_iff_modulo
#print axioms Controls.omitted_redex_loses_a_successor
#print axioms Controls.completed_representatives_have_exact_successors
#print axioms Controls.merging_a_terminal_fork_erases_a_distinction

end Mettapedia.GSLT.Contracts.CanonicalSuccessorClasses
