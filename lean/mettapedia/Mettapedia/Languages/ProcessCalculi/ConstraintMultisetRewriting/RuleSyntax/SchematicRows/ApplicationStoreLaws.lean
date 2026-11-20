import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationRunSound

/-!
# Retention and source-interface coverage of actual application results

Application consumes no occurrence. Retained labels are acted on by its
settlement, and the made scheme captures the entire normalized source context.
These properties concern the actual result store and hold independently of a
particular candidate enumerator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSyntax
open MeTTaCalculus.OccurrenceCommits (mem_fire)

universe uOcc
variable {judgmentTag arrowTag : Nat} {O : Type uOcc} {s : Store O}

namespace Attempt

variable (f : Attempt judgmentTag arrowTag O s)

theorem rule_eq : f.raw.rule = Rule.ofShared (interpreter judgmentTag arrowTag) := f.raw.member

theorem outputs_singleton : f.outputs =
    [Row.schematic (PrincipalOutputs.scheme X (a := PUnit.unit) (m := PUnit.unit)
      f.answer (context s) (f.raw.opening.applyTerm
        (judgment judgmentTag (app (.var 0) (.var 3)) (.var 2))))] := by
  have transport : ∀ first second : Rule RowTerms, first = second →
      HEq first.basic.body.produce second.basic.body.produce := by
    intro first second same
    cases same
    rfl
  have production : f.raw.rule.basic.body.produce =
      [judgment judgmentTag (app (.var 0) (.var 3)) (.var 2)] :=
    eq_of_heq (transport _ _ f.rule_eq)
  change List.map (fun value => Row.schematic
    (PrincipalOutputs.scheme X (a := PUnit.unit) (m := PUnit.unit) f.answer (context s)
      (f.raw.opening.applyTerm value))) f.raw.rule.basic.body.produce = _
  rw [production]
  rfl

variable [DecidableEq O]

theorem no_takes (admitted : (machine judgmentTag arrowTag O).Admits f) :
    f.raw.selection.taken = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [← admitted.1.2.2.2.1, f.rule_eq]
  rfl

theorem made_one (admitted : (machine judgmentTag arrowTag O).Admits f) :
    f.raw.selection.made.length = 1 := by
  rw [made_length f admitted, f.outputs_singleton]
  rfl

theorem old_not_made (admitted : (machine judgmentTag arrowTag O).Admits f)
    (o : O) (present : o ∈ s.present) : o ∉ f.raw.selection.made := by
  intro made
  exact Finset.disjoint_left.mp admitted.2.1.fresh (List.mem_toFinset.mpr made) present

theorem present_mono (admitted : (machine judgmentTag arrowTag O).Admits f) :
    s.present ⊆ f.result.present := by
  intro o present
  apply mem_fire.mpr
  refine Or.inl ⟨present, ?_⟩
  simpa only [Selection.commit, f.no_takes admitted, List.toFinset_nil] using (Finset.notMem_empty o)

theorem retained_label (admitted : (machine judgmentTag arrowTag O).Admits f)
    (o : O) (present : o ∈ s.present) : f.result.label o = f.retained o :=
  RuleSyntax.Firing.relabel_of_not_mem f.retained f.raw.selection.made f.outputs
    (f.old_not_made admitted o present)

theorem retained_reading_iff (admitted : (machine judgmentTag arrowTag O).Admits f)
    (o : O) (present : o ∈ s.present) (source : Subst rowSig) (value : Tm) :
    (f.result.label o).ReadsAt X (b := PUnit.unit) source value ↔
      (s.label o).ReadsAt X (b := PUnit.unit) (source.comp f.answer) value := by
  rw [f.retained_label admitted o present]
  exact Row.readsAt_act_iff X (a := s.frame) (b := PUnit.unit) (c := PUnit.unit)
    f.answer source value (s.label o)

theorem context_transport (admitted : (machine judgmentTag arrowTag O).Admits f)
    (term : Tm) (inside : term ∈ context s) : f.answer.applyTerm term ∈ context f.result := by
  obtain ⟨made, madeEq⟩ := List.length_eq_one_iff.mp (f.made_one admitted)
  have present : made ∈ f.result.present :=
    mem_fire.mpr (Or.inr (List.mem_toFinset.mpr (madeEq.symm ▸ List.mem_singleton_self made)))
  have labelled : f.result.label made = Row.schematic
      (PrincipalOutputs.scheme X (a := PUnit.unit) (m := PUnit.unit) f.answer (context s)
        (f.raw.opening.applyTerm (judgment judgmentTag (app (.var 0) (.var 3)) (.var 2)))) := by
    change RuleSyntax.relabel (Tm := fun a => Row RowTerms a) f.retained f.raw.selection.made f.outputs made = _
    rw [madeEq, f.outputs_singleton]
    simp [RuleSyntax.relabel]
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨made, Finset.mem_toList.mpr present, ?_⟩
  rw [labelled]
  exact List.mem_map_of_mem (f := f.answer.applyTerm) inside

end Attempt

#print axioms Attempt.no_takes
#print axioms Attempt.present_mono
#print axioms Attempt.retained_reading_iff
#print axioms Attempt.context_transport

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
