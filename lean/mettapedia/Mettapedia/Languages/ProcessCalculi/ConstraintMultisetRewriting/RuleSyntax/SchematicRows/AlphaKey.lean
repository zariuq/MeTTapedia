import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Schema
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricSemantics

/-!
# Schematic-row keys from the existing consistent-renaming classes

At the first-order frame, encode a closure by a premiseless rule whose ordered
outputs are its value followed by its parameters. Captured arguments remain a
separate, rigid part of the key. The existing symmetric-match class then renames
the value, local equations and entire parameter vector consistently.

The encoding is for row identity, not an additional runtime inference. Its
realization theorem identifies the exposed parameter vector with the caller's
arguments. Thus equality of keys preserves every closure reading without
quotienting by arbitrary behavioural equivalence or by solving caller knowledge.
Physical occurrence identities and rule-origin profiles are not erased.
This is a payload key: zone, location, access mode, authority and origin must
remain in the surrounding representation when its observer distinguishes them.
The result is not a licence to merge whole held occurrences across those fields.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.AlphaKey

open Mettapedia.Logic.LP
open OneFrame (Terms frames)
open JointFirings

variable {signature : LPSignature}

abbrev RowClosure (signature : LPSignature) := Closure (Terms (Term signature)) PUnit.unit
abbrev X := frames (FirstOrder.action signature)

def presentation (row : RowClosure signature) : SymmetricMatches.Presentation signature Nat :=
  ⟨⟨PUnit.unit, ⟨[], [], row.schema.knowledge, [], row.schema.value :: row.schema.params⟩, []⟩, 0, 0⟩

abbrev Key (signature : LPSignature) := List (Term signature) × SymmetricMatches.Class signature Nat

def key (row : RowClosure signature) : Key signature := ⟨row.args, (presentation row).key⟩

def renamed (names : signature.vars → signature.vars) (row : RowClosure signature) : RowClosure signature :=
  row.instantiate X (b := row.schema.locals) (fun name => Term.var (names name))

theorem presentation_renamed (names : signature.vars → signature.vars) (row : RowClosure signature) :
    presentation (renamed names row) = (presentation row).rename names := rfl

theorem key_renamed (names : SymmetricMatches.Names signature.vars) (row : RowClosure signature) :
    key (renamed names.forward row) = key row := by
  change (row.args, (presentation (renamed names.forward row)).key) =
    (row.args, (presentation row).key)
  rw [presentation_renamed, SymmetricMatches.rename_key]

theorem key_eq_iff (first second : RowClosure signature) :
    key first = key second ↔ first.args = second.args ∧
      SymmetricMatches.Same (presentation first) (presentation second) := by
  rw [key, key, Prod.mk.injEq, SymmetricMatches.key_eq_iff]

theorem readsAt_iff_realizes (row : RowClosure signature) (source : Subst signature)
    (value : Term signature) (label : Nat → Term signature) :
    row.ReadsAt X (b := PUnit.unit) source value ↔
      (presentation row).Realizes label source (value :: row.args.map source.applyTerm) := by
  constructor
  · rintro ⟨locals, known, captures, output⟩
    refine ⟨locals, ?_, known, ?_⟩
    · intro pair missing
      simp [SymmetricMatches.Presentation.uses, presentation] at missing
    · change value :: row.args.map source.applyTerm =
        (row.schema.value :: row.schema.params).map locals.applyTerm
      rw [List.map_cons]
      apply congrArg₂ List.cons output.symm
      have parameters : row.schema.params.map locals.applyTerm = row.args.map source.applyTerm := by
        rw [← List.forall₂_eq_eq_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact captures
      exact parameters.symm
  · rintro ⟨locals, _, known, output⟩
    change value :: row.args.map source.applyTerm =
      (row.schema.value :: row.schema.params).map locals.applyTerm at output
    rw [List.map_cons] at output
    have pieces := List.cons.inj output
    refine ⟨locals, known, ?_, pieces.1.symm⟩
    have parameters : List.Forall₂ Eq (row.schema.params.map locals.applyTerm) (row.args.map source.applyTerm) := by
      rw [List.forall₂_eq_eq_eq]
      exact pieces.2.symm
    exact List.forall₂_map_right_iff.mp (List.forall₂_map_left_iff.mp parameters)

theorem key_eq_readings {first second : RowClosure signature} (same : key first = key second)
    (source : Subst signature) (value : Term signature) :
    first.ReadsAt X (b := PUnit.unit) source value ↔ second.ReadsAt X (b := PUnit.unit) source value := by
  obtain ⟨arguments, classes⟩ := (key_eq_iff first second).mp same
  calc
    first.ReadsAt X (b := PUnit.unit) source value ↔
        (presentation first).Realizes (fun _ => value) source (value :: first.args.map source.applyTerm) :=
      readsAt_iff_realizes first source value _
    _ ↔ (presentation second).Realizes (fun _ => value) source (value :: first.args.map source.applyTerm) :=
      classes.realizes_iff _ _ _
    _ ↔ second.ReadsAt X (b := PUnit.unit) source value := by
      rw [arguments]
      exact (readsAt_iff_realizes second source value _).symm

#print axioms key_renamed
#print axioms key_eq_iff
#print axioms readsAt_iff_realizes
#print axioms key_eq_readings

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.AlphaKey
