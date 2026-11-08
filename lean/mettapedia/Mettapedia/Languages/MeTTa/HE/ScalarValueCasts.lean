import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-!
# Scalar source casts from their reached type query

A literal's value cast consumes the actual query at that occurrence. It
does not prescribe a storage-only or inferred reader, and is independent of
the operand-admission service chosen by the surrounding environment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type Spec.Match.Merge

theorem same_symbol_type_match (name : String) (bindings : Bindings)
    (notUndefined : name ≠ "%Undefined%") (notAtom : name ≠ "Atom") :
    TypeMatchRel (.symbol name) (.symbol name) bindings bindings :=
  .structural (by simpa [Atom.undefinedType] using notUndefined)
    (by simpa [Atom.atomType] using notAtom)
    (by simpa [Atom.undefinedType] using notUndefined)
    (by simpa [Atom.atomType] using notAtom)
    (.symSym name semanticLoopFree_empty)
    (.mk (by simp [constraints, Bindings.empty]) .nil)

theorem Stateful.scalar_from_query {Context World : Type}
    (environment : WorldEnvironment Context World) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (frame : Frame) (value : GroundedValue) (name : String)
    (notUndefined : name ≠ "%Undefined%") (notAtom : name ≠ "Atom")
    (notGrounded : name ≠ "Grounded")
    (queried : environment.lookup
      (invocationTypeScope scope live (.grounded value) (.symbol name) frame.bindings)
      (environment.view world label) frame.bindings (.grounded value) (.symbol name) [.symbol name]) :
    Stateful.AtomRel environment label world live scope (.grounded value) (.symbol name) frame
      [(.grounded value, frame)] world (policy := policy) := by
  have readValue : frame.read policy (.grounded value) = .grounded value := by
    simp [Frame.read, Entry.Value.substitute]
  apply Stateful.AtomRel.cast (raw := [(.grounded value, frame.bindings)])
  · rw [readValue]
    apply Entry.Rel.cast (metaType := Atom.groundedType)
    · simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · simpa only [Entry.Value.erase] using MetaTypeRel.grounded value
    · simp [Atom.atomType, Atom.groundedType, Atom.variableType, notAtom, notGrounded]
    · exact Or.inr (Or.inl ⟨value, by simp [Entry.Value.erase]⟩)
    · simp [Entry.Value.erase, Atom.unit]
  · rw [readValue]
    simp only [Entry.Value.erase]
    exact TypeCastBatchRel.success (earlierTypes := []) (laterTypes := []) queried rfl (by simp)
      (frame.preserved_type_match policy (same_symbol_type_match name frame.bindings notUndefined notAtom))
  · rw [readValue]
    exact .cons ⟨by simp [rawResult, Entry.Value.erase], .same frame, by simp [Entry.Value.erase]⟩ .nil

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
