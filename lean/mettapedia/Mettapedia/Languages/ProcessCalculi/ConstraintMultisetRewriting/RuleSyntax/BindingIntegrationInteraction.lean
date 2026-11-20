import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegrationRows

/-!
# Actual contextual activation checks joint captured information

The reader and the stored row each have a solvable local equation store. A
canonical activation opens the stored row at fresh declarations and then
identifies its captured parameter with the reader's actual unknown. The full
firing is refused when those two otherwise compatible stores disagree on that
capture. Changing the reader's value to zero makes the same operation admissible.

All shape, presence, freshness and physical-allocation conditions are supplied;
the refused case fails at actual knowledge solvability, not at malformed syntax
or an unavailable rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration.Interaction

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface (Frames)
open Interface.Frames (Frame)
open RuleOccurrences SchematicRows
open Rows.Example (signature ambient target)

def constant (frame : Frame signature) (value : Nat) :
    Term (ContextualFamily.signature signature frame.arity) [] () :=
  .op (.inl (.atom value)) .nil

def captured : Contextual.Terms signature ambient :=
  observe (generator ambient.arity ())

def reader (value : Nat) : RuleSyntax.State (Contextual.Terms signature) Nat :=
  ⟨ambient, [(captured, observe (constant ambient value))], ∅, fun _ => captured⟩

def schema : Schema (Contextual.Terms signature) :=
  ⟨ambient, [(captured, observe (constant ambient 0))], [captured], captured⟩

def stored (value : Nat) (_ : Unit) : Closure (Contextual.Terms signature) (reader value).frame :=
  ⟨schema, [captured]⟩

def activation (value : Nat) :=
  Rows.activation (reader value) ({()} : Finset Unit) (stored value) () 0

def point (value : Nat) : Assignment ambient.arity target.arity := fun _ => constant target value

theorem reader_model (value : Nat) :
    (Frames.contextual signature).Models (point value) (reader value).knowledge := by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem reader_separately_solvable (value : Nat) :
    (Frames.contextual signature).Solvable (reader value).knowledge :=
  ⟨target, point value, reader_model value⟩

theorem schema_separately_solvable :
    (Frames.contextual signature).Solvable schema.knowledge :=
  ⟨target, point 0, reader_model 0⟩

theorem activation_fresh (value : Nat) :
    (activation value).Fresh (Frames.contextual signature) :=
  Rows.activation_fresh (reader value) {()} (stored value) () 0

theorem activation_shapes (value : Nat) :
    (activation value).Shapes (Frames.contextual signature) ∅ :=
  HeldReadGenericFirings.datum_shapes (E := Contextual.declarations signature)
    (Frames.contextual signature) (reader value) {()} (stored value) () ambient
    (Contextual.canonicalOpening signature ambient ambient) 0 ∅ (Finset.mem_singleton_self _)
    (activation_fresh value) rfl

theorem activation_enabled (value : Nat) :
    MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : Nat => ()) (reader value).present
      ((activation value).selection.commit (T := Unit)) :=
  HeldReadGenericFirings.datum_enabled (E := Contextual.declarations signature)
    (reader value) {()} (stored value) () ambient
    (Contextual.canonicalOpening signature ambient ambient) 0 (by simp [reader])

abbrev opened : Frame signature := Contextual.extend signature ambient ambient

def readerName : Contextual.Terms signature opened :=
  observe (generator opened.arity (.inl ()))

def localName : Contextual.Terms signature opened :=
  observe (generator opened.arity (.inr ()))

/-- The capture equation is part of this real RFiring's full information. -/
theorem activation_information (value : Nat) :
    (activation value).information (Frames.contextual signature) =
      [(readerName, observe (constant opened value)),
        (localName, observe (constant opened 0)), (localName, readerName)] := rfl

theorem incompatible_information_unsolvable :
    ¬ (Frames.contextual signature).Solvable
      ((activation 1).information (Frames.contextual signature)) := by
  rintro ⟨future, assignment, model⟩
  have readerEquation := model (readerName, observe (constant opened 1)) (by
    rw [activation_information]
    exact List.mem_cons_self)
  have localEquation := model (localName, observe (constant opened 0)) (by
    rw [activation_information]
    exact List.mem_cons_of_mem _ List.mem_cons_self)
  have captureEquation := model (localName, readerName) (by
    rw [activation_information]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have unequal : constant future 0 = constant future 1 :=
    observe_injective (localEquation.symm.trans (captureEquation.trans readerEquation))
  cases unequal

/-- Both local stores, freshness and physical allocation pass. Actual
admission still refuses their incompatible shared capture. -/
theorem incompatible_activation_refused :
    ¬ (activation 1).Admits (Frames.contextual signature) ∅ := by
  rintro ⟨_, _, solved, _⟩
  exact incompatible_information_unsolvable solved

theorem compatible_reading :
    (stored 0 ()).ReadsAt (Frames.contextual signature) (point 0) (observe (constant target 0)) := by
  refine ⟨point 0, reader_model 0, .cons rfl .nil, ?_⟩
  rfl

theorem compatible_activation_admitted :
    (activation 0).Admits (Frames.contextual signature) ∅ :=
  Rows.activation_admitted_of_reading (reader 0) {()} (stored 0) () 0
    (Finset.mem_singleton_self _) (by simp [reader]) rfl
    (point 0) (reader_model 0) (observe (constant target 0)) compatible_reading

/-- Compatibility is tested precisely at the operation combining information:
the unrelated local consistency checks cannot replace it. -/
theorem actual_compatibility_boundary :
    (Frames.contextual signature).Solvable (reader 1).knowledge ∧
      (Frames.contextual signature).Solvable schema.knowledge ∧
      (activation 1).Fresh (Frames.contextual signature) ∧
      (activation 1).Shapes (Frames.contextual signature) ∅ ∧
      MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : Nat => ()) (reader 1).present
        ((activation 1).selection.commit (T := Unit)) ∧
      ¬ (activation 1).Admits (Frames.contextual signature) ∅ ∧
      (activation 0).Admits (Frames.contextual signature) ∅ :=
  ⟨reader_separately_solvable 1, schema_separately_solvable, activation_fresh 1,
    activation_shapes 1, activation_enabled 1, incompatible_activation_refused,
    compatible_activation_admitted⟩

#print axioms activation_fresh
#print axioms activation_shapes
#print axioms activation_enabled
#print axioms activation_information
#print axioms incompatible_information_unsolvable
#print axioms incompatible_activation_refused
#print axioms compatible_activation_admitted
#print axioms actual_compatibility_boundary

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration.Interaction
