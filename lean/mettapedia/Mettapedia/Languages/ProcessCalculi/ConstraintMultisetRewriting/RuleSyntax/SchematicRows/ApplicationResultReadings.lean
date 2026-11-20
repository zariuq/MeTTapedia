import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationReadings

/-!
# Every reading of the actual application result is derivable

The argument follows the result's real occurrence commit and labelling function.
Retained occurrences are transported hypotheses. Made occurrences carry the
principal schemes whose readings have uniform derivations. Equal payloads at
different occurrence identities are not collapsed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSemantics (Derives)
open MeTTaCalculus.OccurrenceCommits (mem_fire)

universe uOcc
variable {judgmentTag arrowTag : Nat} {O : Type uOcc} [DecidableEq O] {s : Store O}

private theorem zip_covers_left {A B : Type*} : ∀ (first : List A) (second : List B),
    first.length = second.length → ∀ value ∈ first, ∃ other, (value, other) ∈ first.zip second := by
  intro first
  induction first with
  | nil => intro second lengths value member; cases member
  | cons head rest ih =>
    intro second lengths value member
    cases second with
    | nil => cases lengths
    | cons other later =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨other, List.mem_cons_self⟩
      · obtain ⟨found, inside⟩ := ih later (Nat.succ.inj lengths) value member
        exact ⟨found, List.mem_cons_of_mem _ inside⟩

theorem made_length (f : Attempt judgmentTag arrowTag O s)
    (admitted : (machine judgmentTag arrowTag O).Admits f) :
    f.raw.selection.made.length = f.outputs.length := by
  have noSchematic : f.raw.rule.schematic.length = 0 := congrArg
    (fun rule : Rule RowTerms => rule.schematic.length)
    (show f.raw.rule = Rule.ofShared (ApplicationSyntax.interpreter judgmentTag arrowTag) from f.raw.member)
  have length := admitted.1.2.2.2.2.2.1
  rw [noSchematic, Nat.add_zero] at length
  simpa only [Attempt.outputs, List.length_map] using length.symm

theorem result_reading_derivable (f : Attempt judgmentTag arrowTag O s)
    (admitted : (machine judgmentTag arrowTag O).Admits f) (source : Subst rowSig)
    (o : O) (present : o ∈ f.result.present) (observed : Tm)
    (reading : (f.result.label o).ReadsAt X (b := PUnit.unit) source observed) :
    Derives judgmentTag arrowTag (s.dataAt X (b := PUnit.unit) f.answer) source observed := by
  by_cases made : o ∈ f.raw.selection.made
  · obtain ⟨row, pair⟩ := zip_covers_left f.raw.selection.made f.outputs (made_length f admitted) o made
    have labelled : f.result.label o = row :=
      RuleSyntax.Firing.relabel_zip f.retained f.raw.selection.made f.outputs
        admitted.1.2.2.1 (made_length f admitted) (o, row) pair
    rw [labelled] at reading
    have outputMember := (List.of_mem_zip pair).2
    change row ∈ f.raw.rule.basic.body.produce.map (fun value =>
      Row.schematic (PrincipalOutputs.scheme X (a := PUnit.unit) (m := PUnit.unit)
        f.answer (context s) (f.raw.opening.applyTerm value))) at outputMember
    obtain ⟨value, member, rfl⟩ := List.mem_map.mp outputMember
    exact output_reading_derivable f admitted value member source observed reading
  · have labelled : f.result.label o = f.retained o :=
      RuleSyntax.Firing.relabel_of_not_mem f.retained f.raw.selection.made f.outputs made
    rw [labelled] at reading
    have old : o ∈ s.present := by
      rcases mem_fire.mp present with retained | new
      · exact retained.1
      · exact False.elim (made (List.mem_toFinset.mp new))
    exact .hypothesis ⟨f.retained o, (State.mem_dataAt X s f.answer _).mpr ⟨o, old, rfl⟩, reading⟩

#print axioms made_length
#print axioms result_reading_derivable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
