import Mettapedia.Computability.FramedFieldSelection

/-!
# Physical grouped assembly of framed fields

Each fixed group concatenates selected input fields into one output field.
Groups may reorder, omit or repeat input occurrences. The existing alphabet
lift, indexed template machine and physical handoff perform all work.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.FramedFieldAssembly

open Turing WordTemplateMachine

variable {Γ : Type} {arity : Nat}

def template (groups : List (List (Fin arity))) : Indexed.Template (Option Γ) arity :=
  groups.flatMap fun group => group.map Sum.inr ++ [Sum.inl none]

theorem template_cons (group : List (Fin arity)) (rest : List (List (Fin arity))) :
    template (Γ := Γ) (group :: rest) = (group.map Sum.inr ++ [.inl none]) ++ template rest := by
  simp [template]

theorem template_length (groups : List (List (Fin arity))) :
    (template (Γ := Γ) groups).length = (groups.map fun group => group.length + 1).sum := by
  simp [template, List.length_flatMap]

theorem instantiate_holes (indices : List (Fin arity)) (fields : Fin arity → List Γ) :
    Indexed.instantiate (indices.map Sum.inr) (FramedFieldSelection.liftedFields fields) =
      (indices.flatMap fields).map some := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      change (fields index).map some ++ Indexed.instantiate (rest.map Sum.inr)
        (FramedFieldSelection.liftedFields fields) = _
      rw [ih]
      simp only [List.flatMap_cons, List.map_append]

theorem instantiate_exact (groups : List (List (Fin arity))) (fields : Fin arity → List Γ) :
    Indexed.instantiate (template groups) (FramedFieldSelection.liftedFields fields) =
      Indexed.frame (groups.map fun group => group.flatMap fields) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      rw [template_cons, Indexed.instantiate_append, Indexed.instantiate_append, instantiate_holes, ih]
      simp only [Indexed.instantiate_literal, Indexed.instantiate_nil, List.map_cons, Indexed.frame,
        List.flatMap_cons, List.append_assoc]

variable [Fintype Γ] [Inhabited Γ]

local instance : Fintype ((WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ := Γ))).Γ
    (WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ := Γ))).k₁) :=
  inferInstanceAs (Fintype (Option (Option Γ)))
local instance : Inhabited ((WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ := Γ))).Γ
    (WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ := Γ))).k₁) :=
  inferInstanceAs (Inhabited (Option (Option Γ)))

def machine (groups : List (List (Fin arity))) : FinTM2 := StackMachineComposition.machine
  (WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ := Γ)))
  (Indexed.machine (template groups)) (Equiv.refl (Option (Option Γ)))

/-- The group list and its instruction count are fixed before all field
contents. Every selected occurrence and output delimiter is physically emitted. -/
noncomputable def outputs (groups : List (List (Fin arity))) (fields : Fin arity → List Γ) :
    TM2OutputsInTime (machine groups) (Indexed.argumentWire fields)
      (some (Indexed.frame (groups.map fun group => group.flatMap fields)))
      ((4 * (groups.map fun group => group.length + 1).sum + 12) * ((Indexed.argumentWire fields).length + 1)) := by
  have lifted := WordHomomorphismMachine.outputs (FramedFieldSelection.liftSymbol (Γ := Γ)) (Indexed.argumentWire fields)
  have length := FramedFieldSelection.lifted_length (Indexed.argumentWire fields)
  rw [FramedFieldSelection.lift_exact] at lifted length
  have assembled := Indexed.outputs (template groups) (FramedFieldSelection.liftedFields fields)
  rw [instantiate_exact] at assembled
  have joined := StackMachineComposition.outputs
    (WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ := Γ))) (Indexed.machine (template groups))
    (Equiv.refl (Option (Option Γ))) (Indexed.argumentWire fields)
    (Indexed.argumentWire (FramedFieldSelection.liftedFields fields))
    (Indexed.frame (groups.map fun group => group.flatMap fields)) _ _ lifted (by
      change TM2OutputsInTime (Indexed.machine (template groups))
        ((Indexed.argumentWire (FramedFieldSelection.liftedFields fields)).map id) _ _
      simpa only [List.map_id] using assembled)
  refine ⟨joined.toEvalsTo, joined.steps_le_m.trans ?_⟩
  simp only [template_length]
  change 2 * (Indexed.argumentWire fields).length +
    2 * (Indexed.argumentWire (FramedFieldSelection.liftedFields fields)).length + 2 +
    2 * (Indexed.argumentWire (FramedFieldSelection.liftedFields fields)).length + 2 +
    4 * ((groups.map fun group => group.length + 1).sum + 1) *
      ((Indexed.argumentWire (FramedFieldSelection.liftedFields fields)).length + 1) ≤ _
  rw [length]
  nlinarith

end Mettapedia.Computability.FramedFieldAssembly
