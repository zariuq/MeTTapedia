import Mettapedia.OSLF.MeTTaIL.GeneralInferredContext

/-! The inference lookups recover uniquely declared constructor and
collection sorts. Stable duplicate removal permits repeated evidence for
one collection element sort without introducing an arbitrary choice.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

open Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem unique?_of_members {α : Type} [DecidableEq α] (items : List α) (actual : α)
    (member : actual ∈ items) (same : ∀ item ∈ items, item = actual) : unique? items = some actual := by
  have normalized : items.eraseDups = [actual] := by
    cases erased : items.eraseDups with
    | nil =>
        have present := List.mem_eraseDups.mpr member
        rw [erased] at present
        cases present
    | cons first rest =>
        have firstSame := same first (List.mem_eraseDups.mp (erased ▸ List.mem_cons_self))
        subst first
        cases rest with
        | nil => rfl
        | cons second tail =>
            have secondSame := same second (List.mem_eraseDups.mp (erased ▸ List.mem_cons_of_mem actual List.mem_cons_self))
            have distinct := Mettapedia.Util.LinearHash.eraseDups_nodup items
            rw [erased] at distinct
            exact False.elim ((List.nodup_cons.mp distinct).1 (secondSame ▸ List.mem_cons_self))
  simp only [unique?, normalized]

theorem constructor?_complete (language : LanguageDef) (declaration : GrammarRule)
    (labels : (language.terms.map GrammarRule.label).Nodup) (declared : declaration ∈ language.terms) :
    constructor? language declaration.label = some declaration := by
  simp only [constructor?, LanguageDef.filter_terms_by_label_eq_singleton language.terms declaration labels declared]

theorem collectionElement?_complete (language : LanguageDef) (choices : CollectionChoiceDeterministic language)
    (kind : CollType) (expected elementType : TypeExpr)
    (origin : expected = .collection kind elementType ∨ ∃ declaration ∈ language.terms,
      bareCollectionElementType? declaration kind expected = some elementType) :
    collectionElement? language kind expected = some elementType := by
  apply unique?_of_members
  · rcases origin with direct | ⟨declaration, declared, selected⟩
    · simp [direct]
    · apply List.mem_append_right
      exact List.mem_filterMap.mpr ⟨declaration, declared, selected⟩
  · intro other member
    rcases List.mem_append.mp member with direct | authored
    · cases expected <;> simp_all
    · obtain ⟨declaration, declared, selected⟩ := List.mem_filterMap.mp authored
      rcases origin with direct | ⟨original, present, chosen⟩
      · obtain ⟨impossible, _, _⟩ := (bareCollectionElementType?_eq_some_iff _ _ _ _).mp selected
        rw [direct] at impossible
        cases impossible
      · obtain ⟨typeFirst, nameFirst, shapeFirst⟩ := (bareCollectionElementType?_eq_some_iff _ _ _ _).mp selected
        obtain ⟨typeSecond, nameSecond, shapeSecond⟩ := (bareCollectionElementType?_eq_some_iff _ _ _ _).mp chosen
        exact choices declared present shapeFirst shapeSecond (TypeExpr.base.inj (typeFirst.symm.trans typeSecond))

#print axioms unique?_of_members
#print axioms constructor?_complete
#print axioms collectionElement?_complete

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar
