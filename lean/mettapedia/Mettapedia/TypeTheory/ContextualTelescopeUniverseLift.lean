import Mettapedia.TypeTheory.ContextualCwfUniverseLift
import Mettapedia.TypeTheory.ContextualModelTelescopes

/-!
# Dependent telescope checking through carrier lifts

The lift retains every supplied telescope family and section. Variable
lookup, component readout and dependent argument checking agree with the
original model, including unsuccessful checks. This changes external carrier
sizes and does not introduce a universe operation in the modeled language.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCwfUniverseLift

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes

universe u v w w' uc vs wt ms

variable {K : Cwf.{u, v, w, w'}} {C : CwfWithTerminal.{u, v, w, w'}}

def liftValue {Γ : K.Ctx} (value : Value K Γ) :
    Value (lift.{u, v, w, w', uc, vs, wt, ms} K) (ULift.up Γ) :=
  ⟨ULift.up value.1, ULift.up value.2⟩

def lowerValue {Γ : (lift.{u, v, w, w', uc, vs, wt, ms} K).Ctx}
    (value : Value (lift.{u, v, w, w', uc, vs, wt, ms} K) Γ) : Value K Γ.down := ⟨value.1.down, value.2.down⟩

@[simp] theorem lower_liftValue {Γ : K.Ctx} (value : Value K Γ) :
    lowerValue.{u, v, w, w', uc, vs, wt, ms} (liftValue.{u, v, w, w', uc, vs, wt, ms} value) = value := by
  cases value
  rfl

@[simp] theorem lift_lowerValue {Γ : (lift.{u, v, w, w', uc, vs, wt, ms} K).Ctx}
    (value : Value (lift.{u, v, w, w', uc, vs, wt, ms} K) Γ) : liftValue.{u, v, w, w', uc, vs, wt, ms} (lowerValue.{u, v, w, w', uc, vs, wt, ms} value) = value := by
  cases Γ
  rcases value with ⟨⟨type⟩, ⟨term⟩⟩
  rfl

theorem liftedValue_eq {Γ : K.Ctx}
    (original : Value K Γ)
    (raised : Value (lift.{u, v, w, w', uc, vs, wt, ms} K) (ULift.up Γ))
    (types : raised.1.down = original.1) (terms : HEq raised.2.down original.2) :
    raised = liftValue.{u, v, w, w', uc, vs, wt, ms} original := by
  have lowered : lowerValue.{u, v, w, w', uc, vs, wt, ms} raised = original := Sigma.ext types terms
  exact (lift_lowerValue raised).symm.trans (congrArg liftValue.{u, v, w, w', uc, vs, wt, ms} lowered)

theorem liftedValue_at_type {Γ : K.Ctx} (A : K.Ty Γ) (term : K.Tm Γ A)
    (A' : (lift.{u, v, w, w', uc, vs, wt, ms} K).Ty (ULift.up Γ))
    (types : A'.down = A) :
    ∃ term' : (lift.{u, v, w, w', uc, vs, wt, ms} K).Tm (ULift.up Γ) A',
      liftValue.{u, v, w, w', uc, vs, wt, ms} (⟨A, term⟩ : Value K Γ) = ⟨A', term'⟩ ∧ HEq term'.down term := by
  have same : A' = ULift.up A := congrArg ULift.up types
  cases same
  exact ⟨ULift.up term, rfl, HEq.rfl⟩

theorem liftValue_injective {Γ : K.Ctx} :
    Function.Injective (liftValue.{u, v, w, w', uc, vs, wt, ms} (K := K) (Γ := Γ)) := fun _ _ same => congrArg lowerValue.{u, v, w, w', uc, vs, wt, ms} same

theorem liftValue_atType {Γ : K.Ctx} (value : Value K Γ) (A : K.Ty Γ) :
    Value.atType? (liftValue.{u, v, w, w', uc, vs, wt, ms} value) (ULift.up A) =
      (value.atType? A).map ULift.up := by
  classical
  by_cases same : value.1 = A
  · cases value with
    | mk actual term =>
        change actual = A at same
        cases same
        rw [Value.atType?_supplied A term]
        exact Value.atType?_supplied (K := lift.{u, v, w, w', uc, vs, wt, ms} K)
          (ULift.up A) (ULift.up term)
  · have raisedDifferent : (liftValue.{u, v, w, w', uc, vs, wt, ms} value).1 ≠ ULift.up A :=
      fun equation => same (congrArg ULift.down equation)
    rw [Value.atType?_none _ _ raisedDifferent, Value.atType?_none _ _ same]
    rfl

@[simp] theorem liftValue_substitute {Γ Δ : K.Ctx}
    (value : Value K Γ) (σ : K.Sub Δ Γ) :
    (liftValue.{u, v, w, w', uc, vs, wt, ms} value).substitute (ULift.up σ) =
      liftValue.{u, v, w, w', uc, vs, wt, ms} (value.substitute σ) := rfl

/-- Each successive family is lifted at its actual preceding context. -/
def liftTelescope : {n : Nat} → {Γ : C.toCwf.Ctx} → Telescope C n Γ →
    Telescope (liftWithTerminal.{u, v, w, w', uc, vs, wt, ms} C) n (ULift.up Γ)
  | _, _, .nil => .nil
  | _, _, .snoc previous type => .snoc (liftTelescope previous) (ULift.up type)

def liftContext {n : Nat} (Γ : Context C n) :
    Context (liftWithTerminal.{u, v, w, w', uc, vs, wt, ms} C) n :=
  ⟨ULift.up Γ.1, liftTelescope.{u, v, w, w', uc, vs, wt, ms} Γ.2⟩

@[simp] theorem liftContext_nil :
    liftContext.{u, v, w, w', uc, vs, wt, ms} (Context.nil C) =
      Context.nil (liftWithTerminal.{u, v, w, w', uc, vs, wt, ms} C) := rfl

@[simp] theorem liftContext_snoc {n : Nat} (Γ : Context C n) (A : C.toCwf.Ty Γ.1) :
    liftContext.{u, v, w, w', uc, vs, wt, ms} (Context.snoc Γ A) =
      Context.snoc (liftContext.{u, v, w, w', uc, vs, wt, ms} Γ) (ULift.up A) := rfl

theorem liftTelescope_lookup : {n : Nat} → {Γ : C.toCwf.Ctx} →
    (telescope : Telescope C n Γ) → (index : Fin n) →
    (liftTelescope.{u, v, w, w', uc, vs, wt, ms} telescope).lookup index =
      liftValue.{u, v, w, w', uc, vs, wt, ms} (telescope.lookup index)
  | _, _, .nil, index => Fin.elim0 index
  | _, _, .snoc previous type, index => by
      cases index using Fin.cases with
      | zero => rfl
      | succ preceding =>
          change Value.substitute ((liftTelescope.{u, v, w, w', uc, vs, wt, ms} previous).lookup preceding)
            (ULift.up (C.toCwf.wk type)) = _
          rw [liftTelescope_lookup]
          rfl

theorem liftTelescope_components {n : Nat} {Γ Δ : C.toCwf.Ctx}
    (telescope : Telescope C n Γ) (σ : C.toCwf.Sub Δ Γ) (index : Fin n) :
    (liftTelescope.{u, v, w, w', uc, vs, wt, ms} telescope).components
      (ULift.up σ) index = liftValue.{u, v, w, w', uc, vs, wt, ms} (telescope.components σ index) := by
  change Value.substitute ((liftTelescope.{u, v, w, w', uc, vs, wt, ms} telescope).lookup index) (ULift.up σ) = _
  rw [liftTelescope_lookup]
  rfl

theorem liftValue_option_injective {Γ : K.Ctx} {first second : Option (Value K Γ)}
    (same : first.map (liftValue.{u, v, w, w', uc, vs, wt, ms}) =
      second.map liftValue.{u, v, w, w', uc, vs, wt, ms}) : first = second := by
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some second => cases same
  | some first =>
      cases second with
      | none => cases same
      | some second =>
          exact congrArg some (liftValue_injective (Option.some.inj same))

/-- Successful dependent checking is preserved and reflected. -/
theorem liftTelescope_assemble_eq_some_iff {n : Nat} {Γ Δ : C.toCwf.Ctx}
    (telescope : Telescope C n Γ) (supplied : Fin n → Option (Value C.toCwf Δ))
    (σ : C.toCwf.Sub Δ Γ) :
    (liftTelescope.{u, v, w, w', uc, vs, wt, ms} telescope).assemble?
      (fun index => (supplied index).map liftValue.{u, v, w, w', uc, vs, wt, ms}) = some (ULift.up σ) ↔
      telescope.assemble? supplied = some σ := by
  constructor
  · intro checked
    apply (Telescope.assemble?_eq_some_iff telescope supplied σ).mpr
    intro index
    have read := (Telescope.assemble?_eq_some_iff
      (C := liftWithTerminal.{u, v, w, w', uc, vs, wt, ms} C)
      (liftTelescope.{u, v, w, w', uc, vs, wt, ms} telescope) _ (ULift.up σ)).mp checked index
    rw [liftTelescope_components] at read
    apply liftValue_option_injective
    exact read
  · intro checked
    apply (Telescope.assemble?_eq_some_iff
      (C := liftWithTerminal.{u, v, w, w', uc, vs, wt, ms} C)
      (liftTelescope.{u, v, w, w', uc, vs, wt, ms} telescope) _ (ULift.up σ)).mpr
    intro index
    rw [(Telescope.assemble?_eq_some_iff telescope supplied σ).mp checked index]
    exact congrArg some (liftTelescope_components telescope σ index).symm

/-- The entire checker result retains its original arrow, including failure. -/
theorem liftTelescope_assemble {n : Nat} {Γ Δ : C.toCwf.Ctx}
    (telescope : Telescope C n Γ) (supplied : Fin n → Option (Value C.toCwf Δ)) :
    (liftTelescope.{u, v, w, w', uc, vs, wt, ms} telescope).assemble?
      (fun index => (supplied index).map liftValue.{u, v, w, w', uc, vs, wt, ms}) =
      (telescope.assemble? supplied).map ULift.up := by
  cases original : telescope.assemble? supplied with
  | some σ =>
      exact (liftTelescope_assemble_eq_some_iff telescope supplied σ).mpr original
  | none =>
      cases raised : (liftTelescope.{u, v, w, w', uc, vs, wt, ms} telescope).assemble?
          (fun index => (supplied index).map liftValue.{u, v, w, w', uc, vs, wt, ms}) with
      | none => rfl
      | some σ =>
          cases σ with
          | up σ =>
              have impossible := (liftTelescope_assemble_eq_some_iff telescope supplied σ).mp raised
              rw [original] at impossible
              cases impossible

end Mettapedia.TypeTheory.ContextualCwfUniverseLift
