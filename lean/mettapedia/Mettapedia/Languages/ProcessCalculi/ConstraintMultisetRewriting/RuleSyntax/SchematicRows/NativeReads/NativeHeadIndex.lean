import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.HeadRanges
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.SchematicIndex

/-!
# Schematic readings survive the concrete two-range native index

The descriptor is a numeric head and expression length; variable-headed
values use the unknown bucket. Symbol-code collisions can over-select but
cannot omit a reading. The captured view must satisfy its sorted-key
invariant. Retrieval and exact admission remain separate operations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.NativeHeadIndex

open Mettapedia.Logic.LP

variable {signature : LPSignature}
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

def descriptor (constantCode : signature.constants → Nat) (functionCode : signature.functionSymbols → Nat)
    (term : Term signature) : HeadRanges.HeadKey :=
  match RigidIndex.head term with
  | none => toLex (0, 0)
  | some (.inl constant) => toLex (constantCode constant, 0)
  | some (.inr symbol) => toLex (functionCode symbol, signature.functionArity symbol + 1)

theorem compatible_descriptor (constantCode : signature.constants → Nat)
    (functionCode : signature.functionSymbols → Nat) (pattern row : Term signature)
    (permitted : RigidIndex.permits pattern row = true) :
    (ofLex (descriptor constantCode functionCode pattern)).1 = 0 ∨
      (ofLex (descriptor constantCode functionCode row)).1 = 0 ∨
        descriptor constantCode functionCode pattern = descriptor constantCode functionCode row := by
  cases hp : RigidIndex.head pattern with
  | none =>
      left
      simp only [descriptor, hp, ofLex_toLex]
  | some first =>
      cases hr : RigidIndex.head row with
      | none =>
          right
          left
          simp only [descriptor, hr, ofLex_toLex]
      | some second =>
          have equal : first = second := by
            simpa only [RigidIndex.permits, hp, hr, decide_eq_true_eq] using permitted
          right
          right
          simp only [descriptor, hp, hr, equal]

variable {Occurrence : Type}

private theorem permitted_enumeration
    (constantCode : signature.constants → Nat) (functionCode : signature.functionSymbols → Nat)
    (pattern : Term signature) (label : Occurrence → SchematicIndex.Datum signature)
    (rowAt : Nat → Occurrence) (size : Nat)
    (sorted : HeadRanges.Sorted
      (fun i => descriptor constantCode functionCode (SchematicIndex.skeleton (label (rowAt i)))) size)
    (i : Nat) (inside : i < size)
    (permitted : RigidIndex.permits pattern (SchematicIndex.skeleton (label (rowAt i))) = true) :
    i ∈ (if (ofLex (descriptor constantCode functionCode pattern)).1 = 0 then List.range size else
      HeadRanges.twoRuns (fun j => descriptor constantCode functionCode (SchematicIndex.skeleton (label (rowAt j))))
        size (ofLex (descriptor constantCode functionCode pattern)).1
          (ofLex (descriptor constantCode functionCode pattern)).2) := by
  have candidates := compatible_descriptor constantCode functionCode pattern
    (SchematicIndex.skeleton (label (rowAt i))) permitted
  apply (HeadRanges.selected_range_is_complete _ size sorted _ _ i inside).mpr
  rcases candidates with unknown | unknown | same
  · exact Or.inl unknown
  · exact Or.inr (Or.inl unknown)
  · right
    right
    change descriptor constantCode functionCode (SchematicIndex.skeleton (label (rowAt i))) =
      toLex (ofLex (descriptor constantCode functionCode pattern))
    rw [toLex_ofLex]
    exact same.symm

theorem independent_reading_is_enumerated
    (constantCode : signature.constants → Nat) (functionCode : signature.functionSymbols → Nat)
    (pattern : Term signature) (label : Occurrence → SchematicIndex.Datum signature)
    (rowAt : Nat → Occurrence) (size : Nat)
    (sorted : HeadRanges.Sorted
      (fun i => descriptor constantCode functionCode (SchematicIndex.skeleton (label (rowAt i)))) size)
    (i : Nat) (inside : i < size) (caller ambient : Subst signature)
    (reading : Row.ReadsAt SchematicIndex.X (b := PUnit.unit) ambient (caller.applyTerm pattern) (label (rowAt i))) :
    i ∈ (if (ofLex (descriptor constantCode functionCode pattern)).1 = 0 then List.range size else
      HeadRanges.twoRuns (fun j => descriptor constantCode functionCode (SchematicIndex.skeleton (label (rowAt j))))
        size (ofLex (descriptor constantCode functionCode pattern)).1
          (ofLex (descriptor constantCode functionCode pattern)).2) :=
  permitted_enumeration constantCode functionCode pattern label rowAt size sorted i inside
    (SchematicIndex.permits_of_independent_reading pattern (label (rowAt i)) caller ambient reading)

theorem actual_reading_is_enumerated
    (constantCode : signature.constants → Nat) (functionCode : signature.functionSymbols → Nat)
    (pattern : Term signature) (label : Occurrence → SchematicIndex.Datum signature)
    (rowAt : Nat → Occurrence) (size : Nat)
    (sorted : HeadRanges.Sorted
      (fun i => descriptor constantCode functionCode (SchematicIndex.skeleton (label (rowAt i)))) size)
    (i : Nat) (inside : i < size) (point : Subst signature)
    (reading : Row.ReadsAt SchematicIndex.X (b := PUnit.unit) point (point.applyTerm pattern) (label (rowAt i))) :
    i ∈ (if (ofLex (descriptor constantCode functionCode pattern)).1 = 0 then List.range size else
      HeadRanges.twoRuns (fun j => descriptor constantCode functionCode (SchematicIndex.skeleton (label (rowAt j))))
        size (ofLex (descriptor constantCode functionCode pattern)).1
          (ofLex (descriptor constantCode functionCode pattern)).2) :=
  independent_reading_is_enumerated constantCode functionCode pattern label rowAt size sorted i inside point point reading

#print axioms compatible_descriptor
#print axioms actual_reading_is_enumerated
#print axioms independent_reading_is_enumerated

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.NativeHeadIndex
