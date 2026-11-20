import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSupport

/-!
# Realizing a reading through an independently opened datum

The witness chooses only the datum's local assignment. A global assignment
then realizes that witness when it retains the ambient arguments and agrees
on the datum's private namespace. Both requirements are discharged by the
paired-namespace construction, rather than by solving caller unknowns anew.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)

def privateOpening (bound index : Nat) : Subst rowSig :=
  FreshNamespaces.opening (Equiv.refl Nat) bound index

def privateUse {a : PUnit} (bound index : Nat) (row : Row RowTerms a) :
    RowUse RowTerms (fun _ _ : PUnit => Subst rowSig) a row :=
  match row with
  | .shared value => .shared value
  | .schematic closure => .schematic closure (privateOpening bound index)

theorem reading_wellFormed {a : PUnit} (row : Row RowTerms a) (caller : Subst rowSig)
    (value : Tm) (reading : row.ReadsAt X (b := PUnit.unit) caller value) : row.WellFormed := by
  cases row with
  | shared _ => rfl
  | schematic closure => exact Closure.wellFormed_of_readsAt X closure caller reading

theorem privateUse_realizes {a : PUnit} (bound index : Nat) (row : Row RowTerms a)
    (caller : Subst rowSig) (value : Tm)
    (reading : row.ReadsAt X (b := PUnit.unit) caller value) :
    ∃ locals : Subst rowSig, ∀ assignment : Subst rowSig,
      (∀ term ∈ row.ambientTerms, assignment.applyTerm term = caller.applyTerm term) →
      (∀ term : Tm, assignment.applyTerm ((privateOpening bound index).applyTerm term) =
        locals.applyTerm term) →
      X.Models (a := PUnit.unit) (b := PUnit.unit) assignment
          (RowUse.information (Tm := RowTerms) X (Subst.id rowSig) (privateUse bound index row)) ∧
        assignment.applyTerm (RowUse.value (Tm := RowTerms) X (Subst.id rowSig) (privateUse bound index row)) = value := by
  cases row with
  | shared term =>
    refine ⟨Subst.id rowSig, fun assignment ambient _ => ⟨?_, ?_⟩⟩
    · exact Interface.Frames.models_nil (X := X) (a := PUnit.unit) (b := PUnit.unit) assignment
    · change caller.applyTerm term = value at reading
      change assignment.applyTerm ((Subst.id rowSig).applyTerm term) = value
      rw [Subst.applyTerm_id]
      exact (ambient term (List.mem_singleton_self term)).trans reading
  | schematic closure =>
    obtain ⟨locals, solved, captures, output⟩ := reading
    refine ⟨locals, fun assignment ambient opened => ⟨?_, ?_⟩⟩
    · change Unifies assignment
        ((closure.schema.knowledge.map fun equation =>
          ((privateOpening bound index).applyTerm equation.1,
            (privateOpening bound index).applyTerm equation.2)) ++
          (closure.schema.params.map (privateOpening bound index).applyTerm).zip
            (closure.args.map (Subst.id rowSig).applyTerm))
      intro equation inside
      rcases List.mem_append.mp inside with known | captured
      · obtain ⟨original, member, rfl⟩ := List.mem_map.mp known
        change assignment.applyTerm ((privateOpening bound index).applyTerm original.1) =
          assignment.applyTerm ((privateOpening bound index).applyTerm original.2)
        rw [opened, opened]
        exact solved original member
      · rw [List.zip_map] at captured
        obtain ⟨⟨parameter, argument⟩, paired, rfl⟩ := List.mem_map.mp captured
        change assignment.applyTerm ((privateOpening bound index).applyTerm parameter) =
          assignment.applyTerm ((Subst.id rowSig).applyTerm argument)
        rw [opened, Subst.applyTerm_id, ambient argument (List.of_mem_zip paired).2]
        exact List.forall₂_zip captures paired
    · change assignment.applyTerm ((privateOpening bound index).applyTerm closure.schema.value) = value
      rw [opened]
      exact output

def applicationAssignment (function argument domain codomain : Tm) : Subst rowSig :=
  fun name => if name = 0 then function else if name = 1 then domain else
    if name = 2 then codomain else if name = 3 then argument else .var name

theorem applicationAssignment_read (judgmentTag arrowTag : Nat)
    (function argument domain codomain : Tm) :
    (ApplicationSyntax.interpreter judgmentTag arrowTag).body.read.map
      (applicationAssignment function argument domain codomain).applyTerm =
      [ApplicationSyntax.judgment judgmentTag function (ApplicationSyntax.arrow arrowTag domain codomain),
        ApplicationSyntax.judgment judgmentTag argument domain] := by
  rw [ApplicationSyntax.interpreter_read_instance]
  rfl

theorem applicationAssignment_produce (judgmentTag arrowTag : Nat)
    (function argument domain codomain : Tm) :
    (ApplicationSyntax.interpreter judgmentTag arrowTag).body.produce.map
      (applicationAssignment function argument domain codomain).applyTerm =
      [ApplicationSyntax.judgment judgmentTag (ApplicationSyntax.app function argument) codomain] := by
  rw [ApplicationSyntax.interpreter_produce_instance]
  rfl

#print axioms privateUse_realizes
#print axioms applicationAssignment_read
#print axioms applicationAssignment_produce

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
