import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Restriction to finite Turing-machine control support

A closed finite support becomes the actual label type. Restriction and
inclusion commute with each native transition and preserve and reflect
termination. The initial inhabitant is the source's start label. No tape,
symbol, or command is changed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine.FiniteControl

open Turing

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
variable (source : TM0.Machine Γ Λ) (support : Finset Λ)
variable (supported : TM0.Supports source (support : Set Λ))

/-- The native initial label belongs to the finite control space. -/
@[instance_reducible] def controlInhabited : Inhabited {label : Λ // label ∈ support} :=
  ⟨⟨default, supported.1⟩⟩

/-- Restrict a finitely supported machine to the labels it can actually visit. -/
def restrict [Inhabited {label : Λ // label ∈ support}] :
    TM0.Machine Γ {label : Λ // label ∈ support} :=
  fun label symbol =>
    match found : source label.val symbol with
    | none => none
    | some (next, command) =>
        some (⟨next, supported.2 (by rw [found]; rfl) label.property⟩, command)

def forget (configuration : TM0.Cfg Γ {label : Λ // label ∈ support}) : TM0.Cfg Γ Λ :=
  ⟨configuration.q.val, configuration.Tape⟩

section

variable [Inhabited {label : Λ // label ∈ support}]

theorem forget_step (configuration : TM0.Cfg Γ {label : Λ // label ∈ support}) :
    (TM0.step (restrict source support supported) configuration).map (forget support) =
      TM0.step source (forget support configuration) := by
  simp only [TM0.step, restrict, forget]
  split <;> simp_all [forget]

theorem respects : StateTransition.Respects
    (TM0.step (restrict source support supported)) (TM0.step source)
    (fun restricted native => forget support restricted = native) := by
  intro restricted native same
  subst native
  have commuting := forget_step source support supported restricted
  cases found : TM0.step (restrict source support supported) restricted with
  | none => simpa only [found, Option.map_none] using commuting.symm
  | some next =>
      refine ⟨forget support next, rfl, .single ?_⟩
      exact show TM0.step source (forget support restricted) = some (forget support next) from
        by simpa only [found, Option.map_some] using commuting.symm

/-- Each source transition lifts back to the finite control space. -/
theorem reflects : StateTransition.Respects
    (TM0.step source) (TM0.step (restrict source support supported))
    (fun native restricted => forget support restricted = native) := by
  intro native restricted same
  subst native
  have commuting := forget_step source support supported restricted
  cases nativeStep : TM0.step source (forget support restricted) with
  | none =>
      rw [nativeStep] at commuting
      exact Option.map_eq_none_iff.mp commuting
  | some nativeNext =>
      cases restrictedStep : TM0.step (restrict source support supported) restricted with
      | none => simp only [restrictedStep, Option.map_none] at commuting; rw [nativeStep] at commuting; contradiction
      | some restrictedNext =>
          refine ⟨restrictedNext, ?_, .single restrictedStep⟩
          rw [restrictedStep, Option.map_some, nativeStep] at commuting
          exact Option.some.inj commuting

theorem eval_dom_iff (configuration : TM0.Cfg Γ {label : Λ // label ∈ support}) :
    (StateTransition.eval (TM0.step (restrict source support supported)) configuration).Dom ↔
      (StateTransition.eval (TM0.step source) (forget support configuration)).Dom :=
  (StateTransition.tr_eval_dom (respects source support supported) rfl).symm

end

/-- Choose the native start label, rather than an arbitrary inhabitant of the support. -/
theorem input_eval_dom_iff (input : List Γ) :
    letI := controlInhabited source support supported
    (TM0.eval (restrict source support supported) input).Dom ↔
      (TM0.eval source input).Dom := by
  let := controlInhabited source support supported
  change (StateTransition.eval (TM0.step (restrict source support supported)) (TM0.init input)).Dom ↔
    (StateTransition.eval (TM0.step source) (TM0.init input)).Dom
  exact eval_dom_iff source support supported (TM0.init input)

end Mettapedia.Languages.TuringMachine.FiniteControl
