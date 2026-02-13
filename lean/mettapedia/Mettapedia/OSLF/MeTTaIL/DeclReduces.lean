import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mathlib.Data.List.Enum

/-!
# Declarative Reduction for Generic LanguageDef

Defines a declarative (inductive) reduction relation for any `LanguageDef`,
then proves the executable engine is both sound and complete w.r.t. it.

## References

- Meredith & Stay, "Operational Semantics in Logical Form"
-/

namespace Mettapedia.OSLF.MeTTaIL.DeclReduces

set_option linter.dupNamespace false

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine

/-! ## Declarative Reduction -/

/-- Declarative one-step reduction for a `LanguageDef`.

    - `topRule`: a rewrite rule matches at the top level
    - `congElem`: apply a rule to one element of a collection -/
inductive DeclReduces (lang : LanguageDef) : Pattern → Pattern → Prop where
  | topRule :
      {p q : Pattern} →
      (r : RewriteRule) →
      r ∈ lang.rewrites →
      r.premises = [] →
      (bs : Bindings) →
      bs ∈ matchPattern r.left p →
      applyBindings bs r.right = q →
      DeclReduces lang p q
  | congElem :
      {elems : List Pattern} →
      {ct : CollType} →
      {rest : Option String} →
      (hct : LanguageDef.allowsCongruenceIn lang ct) →
      (i : Nat) →
      (hi : i < elems.length) →
      (r : RewriteRule) →
      r ∈ lang.rewrites →
      r.premises = [] →
      (bs : Bindings) →
      bs ∈ matchPattern r.left elems[i] →
      {q' : Pattern} →
      applyBindings bs r.right = q' →
      DeclReduces lang (.collection ct elems rest)
                       (.collection ct (elems.set i q') rest)

/-! ## Helpers -/

private theorem premises_nil_of_isEmpty {r : RewriteRule}
    (h : r.premises.isEmpty = true) : r.premises = [] := by
  match h_eq : r.premises with
  | [] => rfl
  | _ :: _ => simp [h_eq, List.isEmpty] at h

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

private theorem applyRule_sound {lang : LanguageDef} {rule : RewriteRule} {p q : Pattern}
    (hrule : rule ∈ lang.rewrites)
    (hq : q ∈ applyRule rule p) :
    DeclReduces lang p q := by
  unfold applyRule at hq
  split at hq
  case isTrue hprem =>
    rw [List.mem_map] at hq
    obtain ⟨bs, hbs_mem, hbs_eq⟩ := hq
    exact .topRule rule hrule (premises_nil_of_isEmpty hprem) bs hbs_mem hbs_eq
  case isFalse => simp at hq

private theorem rewriteStep_sound {lang : LanguageDef} {p q : Pattern}
    (hq : q ∈ rewriteStep lang p) :
    DeclReduces lang p q := by
  unfold rewriteStep at hq
  rw [List.mem_flatMap] at hq
  obtain ⟨rule, hrule, hq_rule⟩ := hq
  exact applyRule_sound hrule hq_rule

private theorem rewriteInCollection_sound {lang : LanguageDef}
    {ct : CollType} {elems : List Pattern} {rest : Option String} {q : Pattern}
    (hq : q ∈ rewriteInCollectionNoPremises lang ct elems rest) :
    DeclReduces lang (.collection ct elems rest) q := by
  unfold rewriteInCollectionNoPremises at hq
  split at hq
  · rename_i hct
    rw [List.mem_flatMap] at hq
    obtain ⟨⟨elem, j⟩, hmem_zip, hq_map⟩ := hq
    rw [List.mem_map] at hq_map
    obtain ⟨elem', hstep, rfl⟩ := hq_map
    have hj := lt_length_of_mem_zipIdx hmem_zip
    have helem_eq := eq_getElem_of_mem_zipIdx hmem_zip hj
    subst helem_eq
    -- Decompose rewriteStep to get rule and bindings
    unfold rewriteStepNoPremises rewriteStep at hstep
    rw [List.mem_flatMap] at hstep
    obtain ⟨rule, hrule, hq_rule⟩ := hstep
    unfold applyRule at hq_rule
    split at hq_rule
    case isTrue hprem =>
      rw [List.mem_map] at hq_rule
      obtain ⟨bs, hbs, rfl⟩ := hq_rule
      exact .congElem hct j hj rule hrule (premises_nil_of_isEmpty hprem) bs hbs rfl
    case isFalse => simp at hq_rule
  · simp at hq

/-- **Soundness**: every result of the engine is a declarative reduction. -/
theorem engine_sound {lang : LanguageDef} {p q : Pattern}
    (h : q ∈ rewriteWithContext lang p) :
    DeclReduces lang p q := by
  unfold rewriteWithContext rewriteWithContextNoPremises at h
  rw [List.mem_append] at h
  cases h with
  | inl h_top => exact rewriteStep_sound h_top
  | inr h_cong =>
    match p with
    | .collection ct elems rest =>
      exact rewriteInCollection_sound h_cong
    | .bvar _ | .fvar _ | .apply _ _ | .lambda _ | .multiLambda _ _ | .subst _ _ =>
      simp at h_cong

/-! ## Completeness: Declarative → Engine -/

private theorem applyRule_of_topRule {r : RewriteRule} {p q : Pattern}
    (hprem : r.premises = [])
    (bs : Bindings) (hbs : bs ∈ matchPattern r.left p)
    (hq : applyBindings bs r.right = q) :
    q ∈ applyRule r p := by
  unfold applyRule
  have : r.premises.isEmpty = true := by rw [hprem]; rfl
  simp only [this, ↓reduceIte]
  rw [List.mem_map]
  exact ⟨bs, hbs, hq⟩

private theorem rewriteStep_of_topRule' {lang : LanguageDef} {p q : Pattern}
    (r : RewriteRule) (hr : r ∈ lang.rewrites) (hprem : r.premises = [])
    (bs : Bindings) (hbs : bs ∈ matchPattern r.left p)
    (hq : applyBindings bs r.right = q) :
    q ∈ rewriteStep lang p := by
  unfold rewriteStep
  rw [List.mem_flatMap]
  exact ⟨r, hr, applyRule_of_topRule hprem bs hbs hq⟩

/-- **Completeness**: every declarative reduction is produced by the engine. -/
theorem engine_complete {lang : LanguageDef} {p q : Pattern}
    (h : DeclReduces lang p q) :
    q ∈ rewriteWithContext lang p := by
  cases h with
  | topRule r hr hprem bs hbs hq =>
    unfold rewriteWithContext rewriteWithContextNoPremises
    rw [List.mem_append]
    exact .inl (rewriteStep_of_topRule' r hr hprem bs hbs hq)
  | @congElem elems ct rest hct i hi r hr hprem bs hbs q' hq =>
    unfold rewriteWithContext rewriteWithContextNoPremises
    rw [List.mem_append]
    right
    unfold rewriteInCollectionNoPremises
    simp [hct, List.mem_flatMap, List.mem_map]
    refine ⟨elems[i], i, mem_zipIdx_of_lt elems i hi, q', ?_, rfl⟩
    exact rewriteStep_of_topRule' r hr hprem bs hbs hq

/-! ## Equivalence -/

/-- `DeclReduces` and `langReduces` (engine membership) are equivalent. -/
theorem declReduces_iff_langReduces {lang : LanguageDef} {p q : Pattern} :
    DeclReduces lang p q ↔ q ∈ rewriteWithContext lang p :=
  ⟨engine_complete, engine_sound⟩

/-! ## Summary

**0 sorries. 0 axioms.**

- `engine_sound`: `q ∈ rewriteWithContext lang p → DeclReduces lang p q`
- `engine_complete`: `DeclReduces lang p q → q ∈ rewriteWithContext lang p`
- `declReduces_iff_langReduces`: full equivalence
-/

end Mettapedia.OSLF.MeTTaIL.DeclReduces
