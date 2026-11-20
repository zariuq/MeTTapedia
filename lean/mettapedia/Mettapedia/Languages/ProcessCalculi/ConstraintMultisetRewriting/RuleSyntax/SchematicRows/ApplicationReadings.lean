import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSubstitution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.SelectedPatterns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.DataViews

/-!
# Actual application results have uniform derivations

The premises below come from the actual selected occurrences and matching
equations. They are not supplied as an adequacy assumption. After principal
settlement, every reading of the made scheme is derivable from the transported
source data at the same caller point. The full run and saturation laws are
separate from this one-inference invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSyntax
open ApplicationSemantics (Derives)

universe uOcc
variable {judgmentTag arrowTag : Nat} {O : Type uOcc} [DecidableEq O] {s : Store O}

private theorem related_right {A B : Type*} {R : A → B → Prop} {first : List A} {second : List B}
    (paired : List.Forall₂ R first second) : ∀ value ∈ first, ∃ other ∈ second, R value other := by
  induction paired with
  | nil => intro value member; cases member
  | @cons left right first second relation _ ih =>
    intro value member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨right, List.mem_cons_self, relation⟩
    · obtain ⟨other, member, same⟩ := ih value later
      exact ⟨other, List.mem_cons_of_mem _ member, same⟩

theorem read_derivation (raw : Firing O E (program judgmentTag arrowTag) s)
    (assignment : Subst rowSig) (solved : X.Models (b := PUnit.unit) assignment (raw.information X))
    (admitted : raw.Admits X) (pattern : Tm) (member : pattern ∈ raw.rule.basic.body.read) :
    Derives judgmentTag arrowTag (s.dataAt X (b := PUnit.unit) assignment) (Subst.id rowSig)
      (assignment.applyTerm (raw.opening.applyTerm pattern)) := by
  obtain ⟨selected, inside, reading⟩ := related_right
    (raw.read_pattern_readings X assignment solved admitted.1) pattern member
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp inside
  have present : raw.selection.read.get i ∈ s.present :=
    admitted.2.1.kept_subset (List.mem_toFinset.mpr (List.get_mem _ _))
  apply Derives.hypothesis
  apply (State.dataAt_reading_iff X s (b := PUnit.unit) assignment _).mpr
  refine ⟨raw.selection.read.get i, present, ?_⟩
  have point : X.comp (a := s.frame) (b := E.target raw.ext) (c := PUnit.unit)
      assignment (E.weaken raw.ext) = assignment := Subst.comp_id_right assignment
  rw [point] at reading
  change (s.label (raw.selection.read.get i)).ReadsAt X (b := PUnit.unit) assignment
    (assignment.applyTerm (raw.opening.applyTerm pattern)) at reading
  exact reading

theorem produced_derivation (raw : Firing O E (program judgmentTag arrowTag) s)
    (assignment : Subst rowSig) (solved : X.Models (b := PUnit.unit) assignment (raw.information X))
    (admitted : raw.Admits X) (value : Tm) (member : value ∈ raw.rule.basic.body.produce) :
    Derives judgmentTag arrowTag (s.dataAt X (b := PUnit.unit) assignment) (Subst.id rowSig)
      (assignment.applyTerm (raw.opening.applyTerm value)) := by
  have canonical : raw.rule.basic = interpreter judgmentTag arrowTag :=
    congrArg Rule.basic (show raw.rule = Rule.ofShared (interpreter judgmentTag arrowTag) from raw.member)
  have majorMember : judgment judgmentTag (.var 0) (arrow arrowTag (.var 1) (.var 2)) ∈
      raw.rule.basic.body.read := by
    rw [canonical]
    exact List.mem_cons_self
  have minorMember : judgment judgmentTag (.var 3) (.var 1) ∈ raw.rule.basic.body.read := by
    rw [canonical]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have major := read_derivation raw assignment solved admitted _ majorMember
  have minor := read_derivation raw assignment solved admitted _ minorMember
  simp only [apply_judgment, apply_arrow, Subst.applyTerm] at major minor
  have derived := Derives.apply (domain := assignment.applyTerm (raw.opening 1)) major minor
  have output : raw.rule.basic.body.produce =
      [judgment judgmentTag (app (.var 0) (.var 3)) (.var 2)] := by
    rw [canonical]
    rfl
  rw [output] at member
  rw [List.mem_singleton.mp member]
  simpa only [apply_judgment, apply_app, Subst.applyTerm] using derived

omit [DecidableEq O] in
theorem context_covers_data (assignment : Subst rowSig) :
    ∀ row ∈ s.dataAt X (b := PUnit.unit) assignment, ∀ term ∈ row.ambientTerms,
      term ∈ (context s).map assignment.applyTerm := by
  intro row member term inside
  have mapped := State.dataAt_term X s assignment row member term inside
  obtain ⟨original, argument, rfl⟩ := List.mem_map.mp mapped
  exact List.mem_map_of_mem (List.mem_append_right _ argument)

theorem output_reading_derivable (f : Attempt judgmentTag arrowTag O s)
    (admitted : (machine judgmentTag arrowTag O).Admits f)
    (value : Tm) (member : value ∈ f.raw.rule.basic.body.produce)
    (source : Subst rowSig) (observed : Tm)
    (reading : (PrincipalOutputs.scheme X (a := PUnit.unit) (m := PUnit.unit)
      f.answer (context s) (f.raw.opening.applyTerm value)).ReadsAt X (b := PUnit.unit) source observed) :
    Derives judgmentTag arrowTag (s.dataAt X (b := PUnit.unit) f.answer) source observed := by
  have derived := produced_derivation f.raw f.answer f.principal.sound admitted value member
  exact ApplicationSemantics.generalized_reading_derivable judgmentTag arrowTag
    (s.dataAt X (b := PUnit.unit) f.answer) ((context s).map f.answer.applyTerm)
    (context_covers_data f.answer) derived source observed reading

#print axioms read_derivation
#print axioms produced_derivation
#print axioms context_covers_data
#print axioms output_reading_derivable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
