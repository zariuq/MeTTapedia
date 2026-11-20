import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Step

/-!
# The finite term scope of a state holding rules, over arbitrary Frames

Only knowledge, present ordinary labels and held captured arguments constrain
the caller interface. The identity-labelled term probe has exactly those
mentions. It is a freshness view, not an extra executed store or a source of
runtime occurrences; no padding term or free-variable generator is required.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadStateScope

open RuleOccurrences

universe uO uT uOcc uR uC uZ
variable {Obj : Type uO} {Tm : Obj → Type uT} {O : Type uOcc}
  {R : Type uR} {C : Type uC} {Z : Type uZ}

noncomputable def terms (state : RState Tm O R C Z) : List (Tm state.frame) :=
  state.knowledge.map Prod.fst ++ state.knowledge.map Prod.snd ++
    state.present.toList.map state.label ++
    state.rules.toList.flatMap (fun rule => (state.held rule).args)

theorem mentioned_in_terms (state : RState Tm O R C Z) (term : Tm state.frame)
    (mentioned : state.Mentions term) : term ∈ terms state := by
  rcases mentioned with (left | right | ⟨o, present, labelled⟩) |
      ⟨rule, present, argument⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ left))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ right))
  · exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨o, Finset.mem_toList.mpr present, labelled⟩))
  · exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨rule, Finset.mem_toList.mpr present, argument⟩)

theorem mentions_of_mem_terms (state : RState Tm O R C Z) (term : Tm state.frame)
    (member : term ∈ terms state) : state.Mentions term := by
  rcases List.mem_append.mp member with old | held
  · rcases List.mem_append.mp old with known | ordinary
    · rcases List.mem_append.mp known with left | right
      · exact Or.inl (Or.inl left)
      · exact Or.inl (Or.inr (Or.inl right))
    · obtain ⟨o, present, labelled⟩ := List.mem_map.mp ordinary
      exact Or.inl (Or.inr (Or.inr ⟨o, Finset.mem_toList.mp present, labelled⟩))
  · obtain ⟨rule, present, argument⟩ := List.mem_flatMap.mp held
    exact Or.inr ⟨rule, Finset.mem_toList.mp present, argument⟩

noncomputable def scope (state : RState Tm O R C Z) : RuleSyntax.State Tm (Tm state.frame) := by
  classical
  exact ⟨state.frame, state.knowledge, (terms state).toFinset, id⟩

theorem mentions_iff (state : RState Tm O R C Z) (term : Tm state.frame) :
    (scope state).Mentions term ↔ state.Mentions term := by
  classical
  constructor
  · rintro (left | right | ⟨value, present, labelled⟩)
    · exact Or.inl (Or.inl left)
    · exact Or.inl (Or.inr (Or.inl right))
    · change value = term at labelled
      subst value
      exact mentions_of_mem_terms state term (List.mem_toFinset.mp present)
  · intro mentioned
    refine Or.inr (Or.inr ⟨term, ?_, rfl⟩)
    exact List.mem_toFinset.mpr (mentioned_in_terms state term mentioned)

#print axioms mentioned_in_terms
#print axioms mentions_of_mem_terms
#print axioms mentions_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadStateScope
