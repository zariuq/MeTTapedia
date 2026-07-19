/-
Bind decomposition for the finite type-substitution solution theory.

`TypeSubstSatisfied.bind_iff`: a valuation satisfies `substitution.bind name
value` (for an unassigned `name`) exactly when it satisfies `substitution`
and equates `name` with the valuation-image of `value`.  Both directions are
assembled from the existing absorption lemma: the composed head assignment
is absorbed by satisfaction of the old substitution, and the single new
assignment is absorbed through the singleton instance of the same lemma.
-/
import Mettapedia.Languages.MeTTa.HE.HumanTypePresentationTheory

namespace Mettapedia.Languages.MeTTa.HE.HumanTypePresentationTheory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.HumanTypePresentation
open Mettapedia.Languages.MeTTa.HE.HumanTypeRuntimeRefinement

private theorem lookup_none_not_mem :
    ∀ {substitution : TypeSubst} {name : String} {value : Atom},
      substitution.lookup name = none →
      (name, value) ∉ substitution
  | [], _, _, _ => List.not_mem_nil
  | entry :: rest, name, value, hlookup => by
    simp only [TypeSubst.lookup] at hlookup
    by_cases hname : name = entry.1
    · rw [if_pos hname] at hlookup
      cases hlookup
    · rw [if_neg hname] at hlookup
      intro hmem
      rcases List.mem_cons.mp hmem with heq | hmem'
      · exact hname (congrArg Prod.fst heq)
      · exact lookup_none_not_mem hlookup hmem'

private theorem erase_eq_self_of_lookup_none
    {substitution : TypeSubst} {name : String}
    (unassigned : substitution.lookup name = none) :
    substitution.erase name = substitution := by
  unfold TypeSubst.erase
  apply List.filter_eq_self.mpr
  intro entry hentry
  obtain ⟨k, v⟩ := entry
  simp only [bne_iff_ne, ne_eq]
  intro hk
  subst hk
  exact lookup_none_not_mem unassigned hentry

private theorem singleton_satisfied
    {valuation : String → Atom} {name : String} {resolved : Atom}
    (hname : valuation name = applyTypeValuation valuation resolved) :
    TypeSubstSatisfied valuation [(name, resolved)] := by
  intro k v hkv
  rcases List.mem_cons.mp hkv with heq | hmem
  · cases heq
    exact hname
  · exact absurd hmem (List.not_mem_nil)

private theorem applyAssignment_absorb
    {valuation : String → Atom} {name : String} {resolved : Atom}
    (hname : valuation name = applyTypeValuation valuation resolved)
    (atom : Atom) :
    applyTypeValuation valuation (TypeSubst.applyAssignment name resolved atom) =
      applyTypeValuation valuation atom := by
  have habsorb := TypeSubstSatisfied.absorbs
    (singleton_satisfied hname) atom
  simpa [TypeSubst.applyAssignment] using habsorb

/-- **Bind decomposition.**  Satisfying an extension by one fresh assignment
is exactly satisfying the old substitution plus the new equation. -/
theorem TypeSubstSatisfied.bind_iff
    {substitution : TypeSubst} {name : String} {value : Atom}
    (unassigned : substitution.lookup name = none)
    (valuation : String → Atom) :
    TypeSubstSatisfied valuation (substitution.bind name value) ↔
      TypeSubstSatisfied valuation substitution ∧
        valuation name = applyTypeValuation valuation value := by
  have herase := erase_eq_self_of_lookup_none unassigned
  constructor
  · intro hbind
    have hhead : valuation name =
        applyTypeValuation valuation (substitution.apply value) := by
      apply hbind name (substitution.apply value)
      simp [TypeSubst.bind]
    have hold : TypeSubstSatisfied valuation substitution := by
      intro k v hkv
      have hmapped : (k, TypeSubst.applyAssignment name (substitution.apply value) v) ∈
          substitution.bind name value := by
        simp only [TypeSubst.bind]
        apply List.mem_cons_of_mem
        rw [herase]
        exact List.mem_map.mpr ⟨(k, v), hkv, rfl⟩
      have := hbind _ _ hmapped
      rwa [applyAssignment_absorb hhead] at this
    refine ⟨hold, ?_⟩
    rw [hhead]
    exact hold.absorbs value
  · rintro ⟨hold, hname⟩
    have hhead : valuation name =
        applyTypeValuation valuation (substitution.apply value) := by
      rw [hname]
      exact (hold.absorbs value).symm
    intro k v hkv
    simp only [TypeSubst.bind] at hkv
    rcases List.mem_cons.mp hkv with heq | hmem
    · cases heq
      exact hhead
    · rw [herase] at hmem
      obtain ⟨⟨k₀, v₀⟩, hkv₀, hpair⟩ := List.mem_map.mp hmem
      cases hpair
      rw [applyAssignment_absorb hhead]
      exact hold k₀ v₀ hkv₀

end Mettapedia.Languages.MeTTa.HE.HumanTypePresentationTheory
