import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.SchematicIndex
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.QueryProjection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.NativeHeadIndex
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.QuantifierControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.NativeMatchControls

/-! # Candidate controls: unknowns, captures, binders and duplicate occurrences -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.IndexControls

open Mettapedia.Logic.LP
open RuleSyntax.Controls (atoms)

def five : Term atoms := .const 5
def six : Term atoms := .const 6

theorem mismatched_rigid_heads_refuse : RigidIndex.permits five six = false := by decide

theorem descriptor_collision_is_only_overselection :
    NativeHeadIndex.descriptor (fun _ : atoms.constants => 7) (fun _ : atoms.functionSymbols => 7) five =
      NativeHeadIndex.descriptor (fun _ : atoms.constants => 7) (fun _ : atoms.functionSymbols => 7) six ∧
      RigidIndex.permits five six = false := ⟨rfl, by decide⟩

theorem unknown_query_is_kept : RigidIndex.permits (.var 0 : Term atoms) six = true := by decide

theorem unknown_stored_row_is_kept : RigidIndex.permits five (.var 0 : Term atoms) = true := by decide

def labels (occurrence : Nat) : Term atoms := if occurrence = 1 then six else five
def resolve (occurrence : Nat) : List Nat := if occurrence = 1 then [] else [occurrence]

theorem complete_index_keeps_distinct_equal_rows :
    (enumerate (fun occurrence => RigidIndex.permits five (labels occurrence)) [0, 1, 2]).flatMap resolve = [0, 2] := by
  decide

theorem duplicate_encounters_are_not_deduplicated :
    (enumerate (fun occurrence => RigidIndex.permits five (labels occurrence)) [0, 0, 2]).flatMap resolve = [0, 0, 2] := by
  decide

def captured : Closure (OneFrame.Terms (Term atoms)) PUnit.unit := Closure.captured (.var 0)

theorem passing_the_index_does_not_admit_a_capture :
    SchematicIndex.permits six (.schematic captured) = true ∧
      ¬ captured.ReadsAt QuantifierControls.X (b := PUnit.unit) (QuantifierControls.point 5) six := by
  refine ⟨by decide, ?_⟩
  unfold captured
  rw [Closure.readsAt_captured_iff]
  intro impossible
  cases impossible

theorem one_schematic_origin_does_not_share_its_instances :
    Row.ReadsAt QuantifierControls.X (b := PUnit.unit) (QuantifierControls.point 0)
        (QuantifierControls.c 5) QuantifierControls.schematic ∧
      Row.ReadsAt QuantifierControls.X (b := PUnit.unit) (QuantifierControls.point 0)
        (QuantifierControls.c 6) QuantifierControls.schematic ∧
      QuantifierControls.c 5 ≠ QuantifierControls.c 6 :=
  ⟨QuantifierControls.schematic_reads _ _, QuantifierControls.schematic_reads _ _, QuantifierControls.distinct_payloads⟩

theorem one_settled_instance_is_not_a_schema_certificate :
    RigidIndex.permits six ((QuantifierControls.point 5).applyTerm (.var 0)) = false ∧
      SchematicIndex.permits six QuantifierControls.schematic = true ∧
      Row.ReadsAt QuantifierControls.X (b := PUnit.unit) (QuantifierControls.point 0)
        (QuantifierControls.c 6) QuantifierControls.schematic :=
  ⟨by decide, by decide, QuantifierControls.schematic_reads _ _⟩

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open SourceLanguage.Elaboration SourceLanguage.Toolkit
open SourceLanguage.NativeQuery

theorem binder_query_survives :
    ContextualIndex.permits MatchControls.pattern MatchControls.row.atom = true :=
  ContextualIndex.row_problem_survives 0 [] MatchControls.pattern MatchControls.row MatchControls.binding_match_live

theorem wrong_constructor_rejected_before_opening :
    ContextualIndex.permits (num 1) MatchControls.row.atom = false := by decide

theorem duplicate_native_query_has_no_discarded_rows :
    QueryProjection.discarded (D := MatchControls.D) MatchControls.duplicateWorld [] (csym "space") (num 1)
      (.ret (num 7) : SourceLanguage.Comp mkeys [] () MTy) [] [] = 0 := by
  simp [QueryProjection.discarded, MatchControls.duplicateWorld, MatchControls.duplicateRow,
    ContextualIndex.permits,
    ContextualIndex.head, num]

#print axioms complete_index_keeps_distinct_equal_rows
#print axioms passing_the_index_does_not_admit_a_capture
#print axioms binder_query_survives
#print axioms duplicate_native_query_has_no_discarded_rows

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.IndexControls
