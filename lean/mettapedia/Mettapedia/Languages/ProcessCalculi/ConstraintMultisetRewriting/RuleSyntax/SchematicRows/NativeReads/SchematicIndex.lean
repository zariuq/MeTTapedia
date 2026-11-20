import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.RigidIndex
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Schema
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.FrameFilter

/-!
# Schematic candidate completeness without sharing local unknowns

The immutable schema skeleton supplies a negative head certificate. Its
private equations and captured arguments are still checked by the original
read relation. Successful local substitutions are never cached or shared.
Both shared and schematic rows use the existing term and frame instance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.SchematicIndex

open Mettapedia.Logic.LP
open OneFrame (Terms frames)

variable {signature : LPSignature}
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

abbrev X := frames (FirstOrder.action signature)
abbrev Datum (signature : LPSignature) := Row (Terms (Term signature)) PUnit.unit

def skeleton : Datum signature → Term signature
  | .shared value => value
  | .schematic closure => closure.schema.value

def permits (pattern : Term signature) (row : Datum signature) : Bool :=
  RigidIndex.permits pattern (skeleton row)

theorem permits_of_independent_reading {future : PUnit} (pattern : Term signature) (row : Datum signature)
    (caller ambient : Subst signature)
    (reading : Row.ReadsAt X (b := future) ambient (caller.applyTerm pattern) row) :
    permits pattern row = true := by
  cases row with
  | shared value =>
      change ambient.applyTerm value = caller.applyTerm pattern at reading
      exact RigidIndex.permits_of_equal_instances pattern value caller ambient reading.symm
  | schematic closure =>
      obtain ⟨locals, _, _, output⟩ := reading
      exact RigidIndex.permits_of_equal_instances pattern closure.schema.value caller locals output.symm

theorem complete (pattern : Term signature) :
    FrameFilter.Complete X (caller := PUnit.unit) pattern (permits pattern) := by
  intro row denied future caller ambient reading
  have accepted := permits_of_independent_reading pattern row caller ambient reading
  rw [denied] at accepted
  cases accepted

theorem reading_is_candidate (pattern : Term signature) (row : Datum signature)
    (point : Subst signature)
    (reading : Row.ReadsAt X (b := PUnit.unit) point (point.applyTerm pattern) row) :
    permits pattern row = true := by
  cases row with
  | shared value =>
      change point.applyTerm value = point.applyTerm pattern at reading
      exact RigidIndex.permits_of_equal_instances pattern value point point reading.symm
  | schematic closure =>
      obtain ⟨locals, _, _, output⟩ := reading
      exact RigidIndex.permits_of_equal_instances pattern closure.schema.value point locals output.symm

theorem rejected_has_no_reading (pattern : Term signature) (row : Datum signature)
    (rejected : permits pattern row = false) :
    ¬ ∃ point : Subst signature,
      Row.ReadsAt X (b := PUnit.unit) point (point.applyTerm pattern) row := by
  rintro ⟨point, reading⟩
  have accepted := reading_is_candidate pattern row point reading
  rw [rejected] at accepted
  cases accepted

variable {Occurrence Answer : Type}

theorem resolver_word (pattern : Term signature) (label : Occurrence → Datum signature)
    (rows : List Occurrence) (resolve : Occurrence → List Answer)
    (sound : ∀ occurrence answer, answer ∈ resolve occurrence →
      ∃ point : Subst signature,
        Row.ReadsAt X (b := PUnit.unit) point (point.applyTerm pattern) (label occurrence)) :
    (NativeReads.enumerate (fun occurrence => permits pattern (label occurrence)) rows).flatMap resolve =
      rows.flatMap resolve := by
  apply NativeReads.enumerate_resolver_word
  intro occurrence _ nonempty
  obtain ⟨answer, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨point, reading⟩ := sound occurrence answer member
  exact reading_is_candidate pattern (label occurrence) point reading

def localNames (names : signature.vars → signature.vars) : Subst signature :=
  fun name => .var (names name)

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem local_names_preserve_head (names : signature.vars → signature.vars) (term : Term signature) :
    RigidIndex.head ((localNames names).applyTerm term) = RigidIndex.head term := by
  cases term <;> rfl

theorem fresh_schema_has_same_filter (names : signature.vars → signature.vars)
    (pattern : Term signature) (closure : Closure (Terms (Term signature)) PUnit.unit) :
    permits pattern (.schematic (closure.instantiate X (b := PUnit.unit) (localNames names))) =
      permits pattern (.schematic closure) := by
  change RigidIndex.permits pattern ((localNames names).applyTerm closure.schema.value) =
    RigidIndex.permits pattern closure.schema.value
  unfold RigidIndex.permits
  rw [local_names_preserve_head]

#print axioms reading_is_candidate
#print axioms complete
#print axioms rejected_has_no_reading
#print axioms resolver_word
#print axioms fresh_schema_has_same_filter

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.SchematicIndex
