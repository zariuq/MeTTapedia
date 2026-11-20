import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Materialization

/-!
# The actual materialized state has a two-image term span

All mentioned terms after a premiseless activation come from the old source
along weakening or from the activated spec along its opening. Knowledge,
ordinary labels and retained held arguments are inspected separately. The
span is derived from the real `RFiring.result`; it is not a new freshness
assumption or a replacement state definition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadDatumSpan

open Interface (Frames)
open RuleOccurrences

universe uO uT uH uE uOcc uR uC uZ
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}
  {E : Extensions.{uO, uH, uE} Hom} {codes : Codes Tm C Z} {source : RState Tm O R C Z}
  (firing : RFiring O R E codes source)

def sourceImages : Set (Tm (E.target firing.ext)) :=
  {term | ∃ old, source.Mentions old ∧ term = X.act (E.weaken firing.ext) old}

def datumImages : Set (Tm (E.target firing.ext)) :=
  {term | ∃ datumTerm ∈ firing.spec.terms, term = X.act firing.opening datumTerm}

theorem information_images (ambient : Set C) (available : source.Available ambient firing.use)
    (noTake : firing.spec.body.take = []) (noRead : firing.spec.body.read = [])
    (equation : Equation (Tm (E.target firing.ext))) (member : equation ∈ firing.information X) :
    equation.1 ∈ sourceImages X firing ∪ datumImages X firing ∧
      equation.2 ∈ sourceImages X firing ∪ datumImages X firing := by
  rw [Opening.information_no_inputs X firing noTake noRead] at member
  rcases List.mem_append.mp member with base | capture
  · rcases List.mem_append.mp base with old | localKnowledge
    · change equation ∈ source.knowledge.map
        (fun pair => (X.act (E.weaken firing.ext) pair.1, X.act (E.weaken firing.ext) pair.2)) at old
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp old
      exact ⟨Or.inl ⟨original.1, Or.inl (Or.inl (List.mem_map_of_mem (f := Prod.fst) inside)), rfl⟩,
        Or.inl ⟨original.2, Or.inl (Or.inr (Or.inl (List.mem_map_of_mem (f := Prod.snd) inside))), rfl⟩⟩
    · change equation ∈ firing.spec.body.tell.map
        (fun pair => (X.act firing.opening pair.1, X.act firing.opening pair.2)) at localKnowledge
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp localKnowledge
      exact ⟨Or.inr ⟨original.1, Opening.tell_left_in_terms firing original inside, rfl⟩,
        Or.inr ⟨original.2, Opening.tell_right_in_terms firing original inside, rfl⟩⟩
  · change equation ∈ (firing.spec.params.map (X.act firing.opening)).zip
      ((source.argsOf firing.use).map (X.act (E.weaken firing.ext))) at capture
    rw [List.zip_map] at capture
    obtain ⟨⟨parameter, argument⟩, paired, rfl⟩ := List.mem_map.mp capture
    exact ⟨Or.inr ⟨parameter, Opening.parameter_in_terms firing parameter (List.of_mem_zip paired).1, rfl⟩,
      Or.inl ⟨argument,
        Opening.args_mentioned firing ambient available argument (List.of_mem_zip paired).2, rfl⟩⟩

variable [DecidableEq O] [DecidableEq R]

theorem label_other (out : O) (value : Tm firing.spec.locals)
    (made : firing.selection.made = [out]) (produced : firing.spec.body.produce = [value])
    (occurrence : O) (different : occurrence ≠ out) :
    (firing.result X).label occurrence = X.act (E.weaken firing.ext) (source.label occurrence) := by
  have opened : (firing.base.opened X).produce = [X.act firing.opening value] := by
    simp [RuleSyntax.Firing.opened, RuleInstance.map, produced]
  change RuleSyntax.relabel (firing.base.row X source.toState) firing.selection.made
    (firing.base.opened X).produce occurrence = _
  rw [made, opened]
  simp only [RuleSyntax.relabel, if_neg different]
  rfl

theorem result_mentions_span (ambient : Set C) (available : source.Available ambient firing.use)
    (noTake : firing.spec.body.take = []) (noRead : firing.spec.body.read = [])
    (noTaken : firing.selection.taken = []) (out : O) (value : Tm firing.spec.locals)
    (made : firing.selection.made = [out]) (produced : firing.spec.body.produce = [value])
    (noMadeRules : firing.madeRules = []) (term : Tm (E.target firing.ext))
    (mentioned : (firing.result X).Mentions term) :
    term ∈ sourceImages X firing ∪ datumImages X firing := by
  rcases mentioned with (left | right | ⟨occurrence, present, labelled⟩) |
      ⟨occurrence, present, argument⟩
  · obtain ⟨equation, member, rfl⟩ := List.mem_map.mp left
    exact (information_images X firing ambient available noTake noRead equation member).1
  · obtain ⟨equation, member, rfl⟩ := List.mem_map.mp right
    exact (information_images X firing ambient available noTake noRead equation member).2
  · by_cases same : occurrence = out
    · subst occurrence
      rw [Materialization.result_label_single X firing out value made produced] at labelled
      exact Or.inr ⟨value, Opening.produced_in_terms firing value
        (by rw [produced]; exact List.mem_singleton_self value), labelled.symm⟩
    · have sourcePresent : occurrence ∈ source.present := by
        rw [Materialization.result_present_single X firing out noTaken made] at present
        rcases Finset.mem_union.mp present with old | fresh
        · exact old
        · exact False.elim (same (Finset.mem_singleton.mp fresh))
      exact Or.inl ⟨source.label occurrence,
        Or.inl (Or.inr (Or.inr ⟨occurrence, sourcePresent, rfl⟩)),
        labelled.symm.trans (label_other X firing out value made produced occurrence same)⟩
  · have sourcePresent : occurrence ∈ source.rules := by
      rcases firing.mem_result_rules.mp present with kept | created
      · exact firing.kept_subset kept
      · rw [noMadeRules] at created
        cases created
    rw [firing.result_held_other (by rw [noMadeRules]; exact List.not_mem_nil)] at argument
    change term ∈ (source.held occurrence).args.map (X.act (E.weaken firing.ext)) at argument
    obtain ⟨original, inside, equality⟩ := List.mem_map.mp argument
    exact Or.inl ⟨original, Or.inr ⟨occurrence, sourcePresent, inside⟩, equality.symm⟩

#print axioms information_images
#print axioms label_other
#print axioms result_mentions_span

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadDatumSpan
