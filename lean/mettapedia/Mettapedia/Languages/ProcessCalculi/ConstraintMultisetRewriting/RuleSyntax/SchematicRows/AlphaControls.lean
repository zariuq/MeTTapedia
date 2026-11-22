import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.AlphaKey
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.QuantifierControls

/-!
# Controls for local keys, rigid captures and variable sharing

A fresh local coordinate change keeps the key. Specializing a local unknown,
changing only the value's variable while leaving its parameter unchanged, or
renaming an ambient capture does not. These controls concern label identity;
they do not deduplicate physical occurrence or derivation origins.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.AlphaControls

open Mettapedia.Logic.LP
open OneFrame (Terms)
open JointFirings AlphaKey QuantifierControls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms)

def freshNames : SymmetricMatches.Names Nat :=
  ⟨fun name => name + 10, fun name => name - 10, fun name => Nat.add_sub_cancel name 10⟩

theorem fresh_local_names_keep_key : key (renamed freshNames.forward freeClosure) = key freeClosure :=
  key_renamed freshNames freeClosure

def specialized : RowClosure atoms := freeClosure.instantiate QuantifierControls.X (b := PUnit.unit) (point 5)

theorem specialization_is_not_alpha_renaming : key freeClosure ≠ key specialized := by
  intro same
  have reading := (key_eq_readings same (point 5) (c 6)).mp (schematic_reads (point 5) 6)
  exact arbitrary_local_instantiation_is_not_reversible.2.1 reading

def captured : RowClosure atoms := Closure.captured (.var 0)

def brokenSharing : RowClosure atoms :=
  ⟨⟨PUnit.unit, [], [.var 0], .var 1⟩, [.var 0]⟩

theorem broken_sharing_reads_another_value :
    brokenSharing.ReadsAt QuantifierControls.X (b := PUnit.unit) (point 5) (c 6) := by
  refine ⟨fun name => if name = 0 then c 5 else c 6, ?_, .cons rfl .nil, rfl⟩
  intro equation absent
  cases absent

theorem renaming_only_the_value_is_not_alpha : key captured ≠ key brokenSharing := by
  intro same
  have reading := (key_eq_readings same (point 5) (c 6)).mpr broken_sharing_reads_another_value
  have impossible : c 5 = c 6 :=
    (Closure.readsAt_captured_iff QuantifierControls.X (.var 0) (point 5) (c 6)).mp reading
  exact distinct_payloads impossible

def changedCapture : RowClosure atoms := ⟨captured.schema, [.var 1]⟩

theorem ambient_capture_names_are_rigid : key captured ≠ key changedCapture := by
  intro same
  have arguments := congrArg Prod.fst same
  have variableSame : (Term.var 0 : Term atoms) = .var 1 := (List.cons.inj arguments).1
  have impossible : (0 : Nat) = 1 := Term.var.inj variableSame
  omega

#print axioms fresh_local_names_keep_key
#print axioms specialization_is_not_alpha_renaming
#print axioms renaming_only_the_value_is_not_alpha
#print axioms ambient_capture_names_are_rigid

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.AlphaControls
