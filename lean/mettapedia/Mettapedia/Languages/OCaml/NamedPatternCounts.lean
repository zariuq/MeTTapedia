import Mettapedia.Languages.OCaml.NamedPattern

/-! Erasing names preserves the exact number and source order of slots.
This includes nested pattern fields and constructor argument grouping. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.NamedPattern

theorem erase_binders (pattern : NamedPattern) : pattern.erase.binders = pattern.names.length := by
  refine NamedPattern.rec
    (motive_1 := fun pattern => pattern.erase.binders = pattern.names.length)
    (motive_2 := fun patterns => ((patterns.map erase).map MatchPattern.binders).sum = (patterns.flatMap names).length)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ pattern
  · intro name; simp [erase, names, MatchPattern.binders]
  · simp [erase, names, MatchPattern.binders]
  · intro value; simp [erase, names, MatchPattern.binders]
  · intro fields ih; simpa only [erase, names, MatchPattern.binders] using ih
  · intro head tail headIH tailIH; simp only [erase, names, MatchPattern.binders, headIH, tailIH, List.length_append]
  · intro typeId constructor fields ih; simpa only [erase, names, MatchPattern.binders] using ih
  · rfl
  · intro pattern rest headIH tailIH
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, headIH, tailIH]

#print axioms erase_binders

end Mettapedia.Languages.OCaml.NamedPattern
