import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mathlib.Data.List.Enum

/-!
# Declarative Reduction with Premises for Generic LanguageDef

Defines a declarative one-step reduction relation that mirrors
`rewriteWithContextWithPremises`, i.e. premise-aware rule application.

This sits alongside `DeclReduces.lean` (which intentionally models the legacy
no-premise engine path for backward compatibility).
-/

namespace Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises

set_option linter.dupNamespace false

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine

/-! ## Declarative Reduction -/

/-- Declarative one-step reduction aligned with the premise-aware engine.
    Parameterized by a relation environment used for `relationQuery`. -/
inductive DeclReducesWithPremises (relEnv : RelationEnv) (lang : LanguageDef) :
    Pattern → Pattern → Prop where
  | topRule :
      {p q : Pattern} →
      (r : RewriteRule) →
      r ∈ lang.rewrites →
      (bs0 : Bindings) →
      bs0 ∈ matchPattern r.left p →
      (bs : Bindings) →
      bs ∈ applyPremisesWithEnv relEnv lang r.premises bs0 →
      applyBindings bs r.right = q →
      DeclReducesWithPremises relEnv lang p q
  | congElem :
      {elems : List Pattern} →
      {ct : CollType} →
      {rest : Option String} →
      (i : Nat) →
      (hi : i < elems.length) →
      (r : RewriteRule) →
      r ∈ lang.rewrites →
      (bs0 : Bindings) →
      bs0 ∈ matchPattern r.left elems[i] →
      (bs : Bindings) →
      bs ∈ applyPremisesWithEnv relEnv lang r.premises bs0 →
      {q' : Pattern} →
      applyBindings bs r.right = q' →
      DeclReducesWithPremises relEnv lang (.collection ct elems rest)
        (.collection ct (elems.set i q') rest)

/-! ## Helpers -/

private theorem mem_zipIdx_of_lt {α : Type*} (l : List α) (i : Nat) (hi : i < l.length) :
    (l[i], i) ∈ l.zipIdx := by
  have hlen : i < l.zipIdx.length := by rw [List.length_zipIdx]; exact hi
  have hget : l.zipIdx[i] = (l[i], i) := by simp [List.getElem_zipIdx]
  rw [← hget]
  exact List.getElem_mem hlen

/-- From `(a, i) ∈ l.zipIdx`, extract `i < l.length`. -/
private theorem lt_length_of_mem_zipIdx {α : Type*} {l : List α} {a : α} {i : Nat}
    (h : (a, i) ∈ l.zipIdx) : i < l.length := by
  have key := List.exists_mem_zipIdx'.mp
    (show ∃ x ∈ l.zipIdx, x = (a, i) from ⟨_, h, rfl⟩)
  obtain ⟨k, hk, hpair⟩ := key
  have : k = i := (Prod.ext_iff.mp hpair).2
  subst this; exact hk

/-- From `(a, i) ∈ l.zipIdx` and `i < l.length`, extract `a = l[i]`. -/
private theorem eq_getElem_of_mem_zipIdx {α : Type*} {l : List α} {a : α} {i : Nat}
    (h : (a, i) ∈ l.zipIdx) (hi : i < l.length) : a = l[i] := by
  have key := List.exists_mem_zipIdx'.mp
    (show ∃ x ∈ l.zipIdx, x = (a, i) from ⟨_, h, rfl⟩)
  obtain ⟨k, _, hpair⟩ := key
  have hki : k = i := (Prod.ext_iff.mp hpair).2
  subst hki
  exact (Prod.ext_iff.mp hpair).1.symm

/-! ## Soundness: Engine → Declarative -/

private theorem applyRuleWithPremisesUsing_sound {relEnv : RelationEnv}
    {lang : LanguageDef} {rule : RewriteRule}
    {p q : Pattern}
    (hrule : rule ∈ lang.rewrites)
    (hq : q ∈ applyRuleWithPremisesUsing relEnv lang rule p) :
    DeclReducesWithPremises relEnv lang p q := by
  unfold applyRuleWithPremisesUsing at hq
  rw [List.mem_flatMap] at hq
  obtain ⟨bs0, hbs0, hq_map⟩ := hq
  rw [List.mem_map] at hq_map
  obtain ⟨bs, hprem, hq_eq⟩ := hq_map
  exact .topRule rule hrule bs0 hbs0 bs hprem hq_eq

private theorem rewriteStepWithPremisesUsing_sound {relEnv : RelationEnv}
    {lang : LanguageDef} {p q : Pattern}
    (hq : q ∈ rewriteStepWithPremisesUsing relEnv lang p) :
    DeclReducesWithPremises relEnv lang p q := by
  unfold rewriteStepWithPremisesUsing at hq
  rw [List.mem_flatMap] at hq
  obtain ⟨rule, hrule, hq_rule⟩ := hq
  exact applyRuleWithPremisesUsing_sound hrule hq_rule

private theorem rewriteInCollectionWithPremisesUsing_sound {relEnv : RelationEnv}
    {lang : LanguageDef}
    {ct : CollType} {elems : List Pattern} {rest : Option String} {q : Pattern}
    (hq : q ∈ rewriteInCollectionWithPremisesUsing relEnv lang ct elems rest) :
    DeclReducesWithPremises relEnv lang (.collection ct elems rest) q := by
  unfold rewriteInCollectionWithPremisesUsing at hq
  rw [List.mem_flatMap] at hq
  obtain ⟨⟨elem, j⟩, hmem_zip, hq_map⟩ := hq
  rw [List.mem_map] at hq_map
  obtain ⟨elem', hstep, rfl⟩ := hq_map
  have hj := lt_length_of_mem_zipIdx hmem_zip
  have helem_eq := eq_getElem_of_mem_zipIdx hmem_zip hj
  subst helem_eq
  unfold rewriteStepWithPremisesUsing at hstep
  rw [List.mem_flatMap] at hstep
  obtain ⟨rule, hrule, hq_rule⟩ := hstep
  unfold applyRuleWithPremisesUsing at hq_rule
  rw [List.mem_flatMap] at hq_rule
  obtain ⟨bs0, hbs0, hq_map_rule⟩ := hq_rule
  rw [List.mem_map] at hq_map_rule
  obtain ⟨bs, hprem, rfl⟩ := hq_map_rule
  exact .congElem j hj rule hrule bs0 hbs0 bs hprem rfl

/-- **Soundness**: every result of the premise-aware engine with environment is
    a declarative reduction. -/
theorem engineWithPremisesUsing_sound {relEnv : RelationEnv}
    {lang : LanguageDef} {p q : Pattern}
    (h : q ∈ rewriteWithContextWithPremisesUsing relEnv lang p) :
    DeclReducesWithPremises relEnv lang p q := by
  unfold rewriteWithContextWithPremisesUsing at h
  rw [List.mem_append] at h
  cases h with
  | inl h_top => exact rewriteStepWithPremisesUsing_sound h_top
  | inr h_cong =>
    match p with
    | .collection ct elems rest =>
      exact rewriteInCollectionWithPremisesUsing_sound h_cong
    | .bvar _ | .fvar _ | .apply _ _ | .lambda _ | .multiLambda _ _ | .subst _ _ =>
      simp at h_cong

/-- **Soundness (default env)**: every result of `rewriteWithContextWithPremises`
    is a declarative reduction with `RelationEnv.empty`. -/
theorem engineWithPremises_sound {lang : LanguageDef} {p q : Pattern}
    (h : q ∈ rewriteWithContextWithPremises lang p) :
    DeclReducesWithPremises RelationEnv.empty lang p q := by
  simpa [rewriteWithContextWithPremises] using
    (engineWithPremisesUsing_sound (relEnv := RelationEnv.empty) h)

/-! ## Completeness: Declarative → Engine -/

private theorem applyRuleWithPremisesUsing_of_topRule {relEnv : RelationEnv}
    {lang : LanguageDef} {r : RewriteRule}
    {p q : Pattern}
    (bs0 : Bindings) (hbs0 : bs0 ∈ matchPattern r.left p)
    (bs : Bindings) (hprem : bs ∈ applyPremisesWithEnv relEnv lang r.premises bs0)
    (hq : applyBindings bs r.right = q) :
    q ∈ applyRuleWithPremisesUsing relEnv lang r p := by
  unfold applyRuleWithPremisesUsing
  rw [List.mem_flatMap]
  refine ⟨bs0, hbs0, ?_⟩
  rw [List.mem_map]
  exact ⟨bs, hprem, hq⟩

private theorem rewriteStepWithPremisesUsing_of_topRule' {relEnv : RelationEnv}
    {lang : LanguageDef} {p q : Pattern}
    (r : RewriteRule) (hr : r ∈ lang.rewrites)
    (bs0 : Bindings) (hbs0 : bs0 ∈ matchPattern r.left p)
    (bs : Bindings) (hprem : bs ∈ applyPremisesWithEnv relEnv lang r.premises bs0)
    (hq : applyBindings bs r.right = q) :
    q ∈ rewriteStepWithPremisesUsing relEnv lang p := by
  unfold rewriteStepWithPremisesUsing
  rw [List.mem_flatMap]
  exact ⟨r, hr, applyRuleWithPremisesUsing_of_topRule bs0 hbs0 bs hprem hq⟩

/-- **Completeness**: every premise-aware declarative reduction is produced
    by the premise-aware engine. -/
theorem engineWithPremisesUsing_complete {relEnv : RelationEnv}
    {lang : LanguageDef} {p q : Pattern}
    (h : DeclReducesWithPremises relEnv lang p q) :
    q ∈ rewriteWithContextWithPremisesUsing relEnv lang p := by
  cases h with
  | topRule r hr bs0 hbs0 bs hprem hq =>
    unfold rewriteWithContextWithPremisesUsing
    rw [List.mem_append]
    exact .inl (rewriteStepWithPremisesUsing_of_topRule' r hr bs0 hbs0 bs hprem hq)
  | @congElem elems ct rest i hi r hr bs0 hbs0 bs hprem q' hq =>
    unfold rewriteWithContextWithPremisesUsing
    rw [List.mem_append]
    right
    unfold rewriteInCollectionWithPremisesUsing
    rw [List.mem_flatMap]
    refine ⟨(elems[i], i), mem_zipIdx_of_lt elems i hi, ?_⟩
    rw [List.mem_map]
    exact ⟨q', rewriteStepWithPremisesUsing_of_topRule' r hr bs0 hbs0 bs hprem hq, rfl⟩

/-- **Completeness (default env)**: every declarative reduction with
    `RelationEnv.empty` is produced by `rewriteWithContextWithPremises`. -/
theorem engineWithPremises_complete {lang : LanguageDef} {p q : Pattern}
    (h : DeclReducesWithPremises RelationEnv.empty lang p q) :
    q ∈ rewriteWithContextWithPremises lang p := by
  simpa [rewriteWithContextWithPremises] using
    (engineWithPremisesUsing_complete (relEnv := RelationEnv.empty) h)

/-! ## Equivalence -/

/-- `DeclReducesWithPremises` and environment-aware engine membership are equivalent. -/
theorem declReducesWithPremises_iff_langReducesWithPremisesUsing
    {relEnv : RelationEnv} {lang : LanguageDef} {p q : Pattern} :
    DeclReducesWithPremises relEnv lang p q ↔
      q ∈ rewriteWithContextWithPremisesUsing relEnv lang p :=
  ⟨engineWithPremisesUsing_complete, engineWithPremisesUsing_sound⟩

/-- Backward-compatible default equivalence at `RelationEnv.empty`. -/
theorem declReducesWithPremises_iff_langReducesWithPremises
    {lang : LanguageDef} {p q : Pattern} :
    DeclReducesWithPremises RelationEnv.empty lang p q ↔
      q ∈ rewriteWithContextWithPremises lang p :=
  ⟨engineWithPremises_complete, engineWithPremises_sound⟩

end Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises
