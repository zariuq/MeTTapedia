import Mettapedia.OSLF.PathMap.PathPrefixRestrictDesiderata

/-!
# Prefix Selector Normalization

This file settles the canonical rhs representation for path-prefix `restrict`.

Different finite selector sets can induce the same admissibility cone.  The most
important redundancy is when a selector contains both a prefix and one of its
extensions: the longer path contributes no additional filtering power.

We define a normalization that keeps exactly the prefix-minimal selector paths
and prove:

* normalization preserves `Allows`
* the normalized selector is prefix-antichain
* any prefix-antichain selector is already normalized
* normalized selectors are canonical among cone-equivalent selectors

This is the theorem slice that can guide how Rust should represent selector rhs
operands once `restrict` is settled as prefix-selector action.
-/

namespace Mettapedia.PathMap

attribute [local instance] Classical.propDecidable

/-- A selector is prefix-antichain when no distinct member is a prefix of
another member. -/
def PrefixAntichain (s : PrefixSelector) : Prop :=
  ∀ p ∈ s, ∀ q ∈ s, p ≠ q → ¬ PathPrefix p q

/-- Keep exactly the prefix-minimal selector paths. -/
noncomputable def selectorNormalize (s : PrefixSelector) : PrefixSelector := by
  classical
  exact s.filter fun q => ∀ r ∈ s, PathPrefix r q → PathPrefix q r

theorem selectorNormalize_mem_iff {s : PrefixSelector} {q : BytePath} :
    q ∈ selectorNormalize s ↔ q ∈ s ∧ ∀ r ∈ s, PathPrefix r q → PathPrefix q r := by
  classical
  simp [selectorNormalize]

theorem prefix_eq_of_mutual {p q : BytePath}
    (hpq : PathPrefix p q) (hqp : PathPrefix q p) : p = q := by
  exact List.IsPrefix.eq_of_length hpq (hpq.length_le.antisymm hqp.length_le)

theorem pathPrefix_refl (p : BytePath) : PathPrefix p p := by
  change p <+: p
  rw [List.prefix_iff_eq_take]
  simp

theorem shorter_of_strict_prefix {p q : BytePath}
    (hpq : PathPrefix p q) (hnqp : ¬ PathPrefix q p) :
    p.length < q.length := by
  have hp_le : p.length ≤ q.length := hpq.length_le
  by_contra hnot
  have hq_le : q.length ≤ p.length := Nat.le_of_not_gt hnot
  have hpqeq : p = q := List.IsPrefix.eq_of_length hpq (hp_le.antisymm hq_le)
  exact hnqp (hpqeq ▸ pathPrefix_refl q)

theorem exists_normalized_prefix_of_mem {s : PrefixSelector} {q : BytePath}
    (hq : q ∈ s) :
    ∃ r ∈ selectorNormalize s, PathPrefix r q := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ q : BytePath, q.length = n → q ∈ s → ∃ r ∈ selectorNormalize s, PathPrefix r q
  have hStrong : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih q hlen hq
    by_cases hmin : ∀ r ∈ s, PathPrefix r q → PathPrefix q r
    · exact ⟨q, (selectorNormalize_mem_iff).2 ⟨hq, hmin⟩, pathPrefix_refl q⟩
    · push_neg at hmin
      rcases hmin with ⟨r, hrS, hrq, hnqr⟩
      have hrlt : r.length < n := by
        simpa [hlen] using shorter_of_strict_prefix hrq hnqr
      rcases ih r.length hrlt r rfl hrS with ⟨t, htNorm, htr⟩
      exact ⟨t, htNorm, htr.trans hrq⟩
  exact hStrong q.length q rfl hq

theorem selectorNormalize_allows_iff (s : PrefixSelector) (p : BytePath) :
    Allows (selectorNormalize s) p ↔ Allows s p := by
  constructor
  · intro h
    rcases h with ⟨q, hq, hqp⟩
    exact ⟨q, (selectorNormalize_mem_iff.mp hq).1, hqp⟩
  · intro h
    rcases h with ⟨q, hq, hqp⟩
    rcases exists_normalized_prefix_of_mem hq with ⟨r, hr, hrq⟩
    exact ⟨r, hr, hrq.trans hqp⟩

theorem selectorNormalize_antichain (s : PrefixSelector) :
    PrefixAntichain (selectorNormalize s) := by
  intro p hp q hq hpq hpre
  have hp' := selectorNormalize_mem_iff.mp hp
  have hq' := selectorNormalize_mem_iff.mp hq
  have hqp : PathPrefix q p := hq'.2 p hp'.1 hpre
  have : p = q := prefix_eq_of_mutual hpre hqp
  exact hpq this

theorem selectorNormalize_self_of_antichain {s : PrefixSelector}
    (hs : PrefixAntichain s) :
    selectorNormalize s = s := by
  classical
  apply Finset.ext
  intro q
  constructor
  · intro hq
    exact (selectorNormalize_mem_iff.mp hq).1
  · intro hq
    refine (selectorNormalize_mem_iff).2 ?_
    refine ⟨hq, ?_⟩
    intro r hr hrq
    by_cases hEq : r = q
    · simp [hEq]
    · exact False.elim ((hs r hr q hq hEq) hrq)

theorem prefixAntichain_eq_of_allows_iff
    {s t : PrefixSelector}
    (hs : PrefixAntichain s) (ht : PrefixAntichain t)
    (hCone : ∀ p, Allows s p ↔ Allows t p) :
    s = t := by
  classical
  apply Finset.ext
  intro q
  constructor
  · intro hq
    have hqt : Allows t q := (hCone q).mp ⟨q, hq, pathPrefix_refl q⟩
    rcases hqt with ⟨r, hr, hrq⟩
    have hrs : Allows s r := (hCone r).mpr ⟨r, hr, pathPrefix_refl r⟩
    rcases hrs with ⟨u, hu, hur⟩
    have huq : PathPrefix u q := hur.trans hrq
    have huqEq : u = q := by
      by_contra hneq
      exact (hs u hu q hq hneq) huq
    have hqr : PathPrefix q r := by simpa [huqEq] using hur
    have hrEq : r = q := prefix_eq_of_mutual hrq hqr
    simp [hrEq] at hr
    exact hr
  · intro hq
    have hqs : Allows s q := (hCone q).mpr ⟨q, hq, pathPrefix_refl q⟩
    rcases hqs with ⟨r, hr, hrq⟩
    have hrt : Allows t r := (hCone r).mp ⟨r, hr, pathPrefix_refl r⟩
    rcases hrt with ⟨u, hu, hur⟩
    have huq : PathPrefix u q := hur.trans hrq
    have huqEq : u = q := by
      by_contra hneq
      exact (ht u hu q hq hneq) huq
    have hqr : PathPrefix q r := by simpa [huqEq] using hur
    have hrEq : r = q := prefix_eq_of_mutual hrq hqr
    simpa [hrEq] using hr

theorem selectorNormalize_idempotent (s : PrefixSelector) :
    selectorNormalize (selectorNormalize s) = selectorNormalize s := by
  exact selectorNormalize_self_of_antichain (selectorNormalize_antichain s)

theorem selectorNormalize_canonical {s t : PrefixSelector}
    (hCone : ∀ p, Allows s p ↔ Allows t p) :
    selectorNormalize s = selectorNormalize t := by
  apply prefixAntichain_eq_of_allows_iff
  · exact selectorNormalize_antichain s
  · exact selectorNormalize_antichain t
  · intro p
    rw [selectorNormalize_allows_iff, selectorNormalize_allows_iff, hCone]

theorem selectorNormalize_root_collapse {s : PrefixSelector}
    (hroot : ([] : BytePath) ∈ s) :
    selectorNormalize s = {([] : BytePath)} := by
  have hCone : ∀ p, Allows s p ↔ Allows {([] : BytePath)} p := by
    intro p
    constructor
    · intro _
      exact ⟨[], by simp, by simp⟩
    · intro _
      exact allows_root s hroot p
  calc
    selectorNormalize s = selectorNormalize {([] : BytePath)} :=
      selectorNormalize_canonical hCone
    _ = {([] : BytePath)} := by
      apply selectorNormalize_self_of_antichain
      intro p hp q hq hpq hpre
      simp at hp hq
      subst hp
      subst hq
      exact hpq rfl

end Mettapedia.PathMap
