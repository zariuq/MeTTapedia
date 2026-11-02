import Mettapedia.Logic.DerivationGraph

/-! # Exact source addresses of selected premise values -/

set_option autoImplicit false

namespace Mettapedia.Logic.DerivationGraph

universe u
variable {J : Type u}

/-- Membership in a successful premise lookup has an actual cited address.
Unused cache rows need no semantic authority to justify this lookup. -/
theorem lookupPremises_selected (cache : Array J) {indices : List Nat} {premises : List J}
    (accepted : lookupPremises cache indices = some premises) :
    ∀ premise ∈ premises, ∃ index ∈ indices, cache[index]? = some premise := by
  induction indices generalizing premises with
  | nil =>
      cases Option.some.inj accepted
      intro premise member
      cases member
  | cons index rest ih =>
      cases head : cache[index]? with
      | none => simp [lookupPremises, head] at accepted
      | some premise =>
          cases tail : lookupPremises cache rest with
          | none => simp [lookupPremises, head, tail] at accepted
          | some earlier =>
              have equal : premise :: earlier = premises := by
                simpa [lookupPremises, head, tail] using accepted
              subst premises
              intro judgment member
              rcases List.mem_cons.mp member with rfl | member
              · exact ⟨index, List.mem_cons_self .., head⟩
              · obtain ⟨address, selected, found⟩ := ih tail judgment member
                exact ⟨address, List.mem_cons_of_mem _ selected, found⟩

theorem lookupPremises_cited (cache : Array J) {indices : List Nat} {premises : List J}
    (accepted : lookupPremises cache indices = some premises) :
    ∀ index ∈ indices, ∀ premise, cache[index]? = some premise → premise ∈ premises := by
  induction indices generalizing premises with
  | nil => intro index member; cases member
  | cons first rest ih =>
      cases head : cache[first]? with
      | none => simp [lookupPremises, head] at accepted
      | some value =>
          cases tail : lookupPremises cache rest with
          | none => simp [lookupPremises, head, tail] at accepted
          | some earlier =>
              have equal : value :: earlier = premises := by
                simpa [lookupPremises, head, tail] using accepted
              subst premises
              intro index member premise found
              rcases List.mem_cons.mp member with rfl | member
              · have same := Option.some.inj (head.symm.trans found)
                exact List.mem_cons.mpr (Or.inl same.symm)
              · exact List.mem_cons_of_mem _ (ih tail index member premise found)

end Mettapedia.Logic.DerivationGraph
