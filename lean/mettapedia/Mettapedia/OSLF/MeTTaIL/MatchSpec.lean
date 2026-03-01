import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.DeclReduces
import Mathlib.Data.List.Enum

/-!
# Relational Matching Specification for MeTTaIL

Defines `MatchRel`, `MatchArgsRel`, `MatchBagRel` as mutual inductive relations
that specify pattern matching independently of the executable algorithm
(`matchPattern`, `matchArgs`, `matchBag`). Proves soundness and completeness
bridges between the two, breaking the circularity in `DeclReduces`.

## Architecture

```
  matchPattern  ──sound──►  MatchRel  ◄──complete──  matchPattern
  matchArgs     ──sound──►  MatchArgsRel
  matchBag      ──sound──►  MatchBagRel
```

`DeclReducesRel` uses `MatchRel` instead of `matchPattern`, making it
truly independent of the executable algorithm. The equivalence
`DeclReducesRel ↔ DeclReduces` follows from soundness + completeness.

## LLM Notes

- sizeOf bounds: use named helper lemmas (sizeOf_body_lt_lambda, etc.) then omega.
- matchBag unfolding: use `cases rest` then `simp [matchBag]` to fully reduce.
- Catch-all matchPattern cases: `simp [matchPattern] at hmem` unfolds AND closes.
- After `subst hceq` where `hceq : c1 = c2`: c2 is eliminated (RHS), use c1 after.
  After `subst hnn` where `hnn : npat = nconc`: nconc is eliminated (RHS), use npat after.
- Completeness uses same strong Nat induction as soundness (on sizeOf of pattern),
  since `induction` tactic does not support mutual inductives.
-/

namespace Mettapedia.OSLF.MeTTaIL.MatchSpec

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.DeclReductions

/-! ## Relational Matching Specification -/

mutual
/-- Relational specification of `matchPattern`. -/
inductive MatchRel : Pattern → Pattern → Bindings → Prop where
  | fvar : MatchRel (.fvar x) t [(x, t)]
  | bvar : MatchRel (.bvar n) (.bvar n) []
  | apply :
      MatchArgsRel pargs targs bs →
      pargs.length = targs.length →
      MatchRel (.apply c pargs) (.apply c targs) bs
  | lambda :
      MatchRel bodyPat bodyConcrete bs →
      MatchRel (.lambda bodyPat) (.lambda bodyConcrete) bs
  | multiLambda :
      MatchRel bodyPat bodyConcrete bs →
      MatchRel (.multiLambda n bodyPat) (.multiLambda n bodyConcrete) bs
  | collection :
      MatchBagRel pelems rest ct telems bs →
      MatchRel (.collection ct pelems rest) (.collection ct telems rest₂) bs
  | subst :
      MatchRel pbody tbody b1 →
      MatchRel prepl trepl b2 →
      mergeBindings b1 b2 = some bs →
      MatchRel (.subst pbody prepl) (.subst tbody trepl) bs

/-- Relational specification of `matchArgs`. -/
inductive MatchArgsRel : List Pattern → List Pattern → Bindings → Prop where
  | nil : MatchArgsRel [] [] []
  | cons :
      MatchRel p t hb →
      MatchArgsRel ps ts tb →
      mergeBindings hb tb = some bs →
      MatchArgsRel (p :: ps) (t :: ts) bs

/-- Relational specification of `matchBag`. -/
inductive MatchBagRel : List Pattern → Option String → CollType →
    List Pattern → Bindings → Prop where
  | nilNoRest :
      MatchBagRel [] none ct [] []
  | nilRest :
      MatchBagRel [] (some rv) ct telems [(rv, Pattern.collection ct telems none)]
  | cons :
      (i : Nat) → (hi : i < telems.length) →
      MatchRel ppat telems[i] hb →
      MatchBagRel prest rest ct (telems.eraseIdx i) restB →
      mergeBindings hb restB = some bs →
      MatchBagRel (ppat :: prest) rest ct telems bs
end

/-! ## Helper Lemmas -/

private theorem lt_length_of_mem_zipIdx {α : Type*} {l : List α} {a : α} {i : Nat}
    (h : (a, i) ∈ l.zipIdx) : i < l.length := by
  have key := List.exists_mem_zipIdx'.mp
    (show ∃ x ∈ l.zipIdx, x = (a, i) from ⟨_, h, rfl⟩)
  obtain ⟨k, hk, hpair⟩ := key
  have : k = i := (Prod.ext_iff.mp hpair).2
  subst this; exact hk

private theorem eq_getElem_of_mem_zipIdx {α : Type*} {l : List α} {a : α} {i : Nat}
    (h : (a, i) ∈ l.zipIdx) (hi : i < l.length) : a = l[i] := by
  have key := List.exists_mem_zipIdx'.mp
    (show ∃ x ∈ l.zipIdx, x = (a, i) from ⟨_, h, rfl⟩)
  obtain ⟨k, _, hpair⟩ := key
  have hki : k = i := (Prod.ext_iff.mp hpair).2
  subst hki
  exact (Prod.ext_iff.mp hpair).1.symm

private theorem mem_zipIdx_of_lt {α : Type*} (l : List α) (i : Nat) (hi : i < l.length) :
    (l[i], i) ∈ l.zipIdx := by
  have hlen : i < l.zipIdx.length := by rw [List.length_zipIdx]; exact hi
  have hget : l.zipIdx[i] = (l[i], i) := by simp [List.getElem_zipIdx]
  rw [← hget]
  exact List.getElem_mem hlen

private theorem eq_nil_of_isEmpty {α : Type} {l : List α}
    (h : l.isEmpty = true) : l = [] := by
  cases l with
  | nil => rfl
  | cons _ _ => simp [List.isEmpty] at h

/-! ## sizeOf helpers

These lemmas establish the strict subterm ordering. `simp_wf` handles
single-field constructors; multi-field ones need `; omega`. -/

private theorem sizeOf_body_lt_lambda (body : Pattern) :
    sizeOf body < sizeOf (Pattern.lambda body) := by simp_wf

private theorem sizeOf_body_lt_multiLambda (n : Nat) (body : Pattern) :
    sizeOf body < sizeOf (Pattern.multiLambda n body) := by simp_wf

private theorem sizeOf_args_lt_apply (c : String) (args : List Pattern) :
    sizeOf args < sizeOf (Pattern.apply c args) := by simp_wf

private theorem sizeOf_elems_lt_collection (ct : CollType) (elems : List Pattern)
    (rest : Option String) :
    sizeOf elems < sizeOf (Pattern.collection ct elems rest) := by simp_wf; omega

private theorem sizeOf_pbody_lt_subst (pbody prepl : Pattern) :
    sizeOf pbody < sizeOf (Pattern.subst pbody prepl) := by simp_wf; omega

private theorem sizeOf_prepl_lt_subst (pbody prepl : Pattern) :
    sizeOf prepl < sizeOf (Pattern.subst pbody prepl) := by simp_wf

private theorem sizeOf_head_lt_cons (p : Pattern) (ps : List Pattern) :
    sizeOf p < sizeOf (p :: ps) := by simp_wf; omega

private theorem sizeOf_tail_lt_cons (p : Pattern) (ps : List Pattern) :
    sizeOf ps < sizeOf (p :: ps) := by simp_wf

private theorem sizeOf_pattern_pos (pat : Pattern) : 0 < sizeOf pat := by
  cases pat <;> simp [sizeOf, Pattern._sizeOf_1]

private theorem sizeOf_list_pattern_pos (p : Pattern) (ps : List Pattern) :
    0 < sizeOf (p :: ps) := by
  have := sizeOf_head_lt_cons p ps; omega

/-! ## Soundness: executable → relational

All three proofs simultaneously by strong induction on `n` bounding `sizeOf`
of the pattern-side argument. -/

private theorem sound_all (n : Nat) :
    (∀ pat t bs, sizeOf pat ≤ n → bs ∈ matchPattern pat t → MatchRel pat t bs) ∧
    (∀ pargs targs bs, sizeOf pargs ≤ n →
      bs ∈ matchArgs pargs targs → MatchArgsRel pargs targs bs) ∧
    (∀ ppats rest ct telems bs, sizeOf ppats ≤ n →
      bs ∈ matchBag ppats rest ct telems → MatchBagRel ppats rest ct telems bs) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro pat _ _ hle _
      exact absurd hle (by have := sizeOf_pattern_pos pat; omega)
    · intro pargs targs bs hle hmem
      match pargs, targs with
      | [], [] =>
        simp only [matchArgs, List.mem_singleton] at hmem; subst hmem; exact .nil
      | [], _ :: _ => simp [matchArgs] at hmem
      | _ :: _, [] => simp [matchArgs] at hmem
      | p :: _, _ :: _ => exact absurd hle (by simp [sizeOf, List._sizeOf_1]; try omega)
    · intro ppats rest ct telems bs hle hmem
      match ppats with
      | [] =>
        unfold matchBag at hmem
        match rest with
        | none =>
          dsimp only at hmem
          split at hmem
          next hemp =>
            simp only [List.mem_singleton] at hmem; subst hmem
            have := eq_nil_of_isEmpty hemp; subst this; exact .nilNoRest
          next => simp at hmem
        | some rv =>
          simp only [List.mem_singleton] at hmem; subst hmem
          exact .nilRest
      | p :: _ => exact absurd hle (by simp [sizeOf, List._sizeOf_1]; try omega)
  | succ m ih =>
    obtain ⟨ih_pat, ih_args, ih_bag⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    -- matchPattern soundness
    · intro pat t bs hle hmem
      match pat, t with
      | .fvar x, t =>
        simp only [matchPattern, List.mem_singleton] at hmem
        subst hmem; exact .fvar
      | .bvar n₁, .bvar n₂ =>
        unfold matchPattern at hmem
        split at hmem
        next heq =>
          have := beq_iff_eq.mp heq; subst this
          simp only [List.mem_singleton] at hmem; subst hmem; exact .bvar
        next => simp at hmem
      | .bvar _, .fvar _ | .bvar _, .apply _ _ | .bvar _, .lambda _
      | .bvar _, .multiLambda _ _ | .bvar _, .subst _ _ | .bvar _, .collection _ _ _ =>
        simp [matchPattern] at hmem
      | .apply c1 pargs, .apply c2 targs =>
        unfold matchPattern at hmem
        split at hmem
        next hcond =>
          have ⟨hc, hl⟩ := Bool.and_eq_true_iff.mp hcond
          have hceq : c1 = c2 := beq_iff_eq.mp hc
          have hlen : pargs.length = targs.length := beq_iff_eq.mp hl
          subst hceq
          exact .apply (ih_args pargs targs bs
            (by have := sizeOf_args_lt_apply c1 pargs; omega) hmem) hlen
        next => simp at hmem
      | .apply _ _, .bvar _ | .apply _ _, .fvar _ | .apply _ _, .lambda _
      | .apply _ _, .multiLambda _ _ | .apply _ _, .subst _ _
      | .apply _ _, .collection _ _ _ =>
        simp [matchPattern] at hmem
      | .lambda bodyPat, .lambda bodyConcrete =>
        unfold matchPattern at hmem
        exact .lambda (ih_pat bodyPat bodyConcrete bs
          (by have := sizeOf_body_lt_lambda bodyPat; omega) hmem)
      | .lambda _, .bvar _ | .lambda _, .fvar _ | .lambda _, .apply _ _
      | .lambda _, .multiLambda _ _ | .lambda _, .subst _ _
      | .lambda _, .collection _ _ _ =>
        simp [matchPattern] at hmem
      | .multiLambda npat bodyPat, .multiLambda nconc bodyConcrete =>
        unfold matchPattern at hmem
        split at hmem
        next heq =>
          have hnn := beq_iff_eq.mp heq; subst hnn
          -- After subst, nconc is gone (subst eliminates the RHS). Use npat.
          exact .multiLambda (ih_pat bodyPat bodyConcrete bs
            (by have := sizeOf_body_lt_multiLambda npat bodyPat; omega) hmem)
        next => simp at hmem
      | .multiLambda _ _, .bvar _ | .multiLambda _ _, .fvar _
      | .multiLambda _ _, .apply _ _ | .multiLambda _ _, .lambda _
      | .multiLambda _ _, .subst _ _ | .multiLambda _ _, .collection _ _ _ =>
        simp [matchPattern] at hmem
      | .collection ct1 pelems rest1, .collection ct2 telems _rest2 =>
        unfold matchPattern at hmem
        split at hmem
        next heq =>
          have hcteq := beq_iff_eq.mp heq; subst hcteq
          exact .collection (ih_bag pelems rest1 ct1 telems bs
            (by have := sizeOf_elems_lt_collection ct1 pelems rest1; omega) hmem)
        next => simp at hmem
      | .collection _ _ _, .bvar _ | .collection _ _ _, .fvar _
      | .collection _ _ _, .apply _ _ | .collection _ _ _, .lambda _
      | .collection _ _ _, .multiLambda _ _ | .collection _ _ _, .subst _ _ =>
        simp [matchPattern] at hmem
      | .subst pbody prepl, .subst tbody trepl =>
        unfold matchPattern at hmem
        rw [List.mem_flatMap] at hmem
        obtain ⟨b1, hb1_mem, hmem2⟩ := hmem
        rw [List.mem_filterMap] at hmem2
        obtain ⟨b2, hb2_mem, hmerge⟩ := hmem2
        exact .subst
          (ih_pat pbody tbody b1
            (by have := sizeOf_pbody_lt_subst pbody prepl; omega) hb1_mem)
          (ih_pat prepl trepl b2
            (by have := sizeOf_prepl_lt_subst pbody prepl; omega) hb2_mem)
          hmerge
      | .subst _ _, .bvar _ | .subst _ _, .fvar _ | .subst _ _, .apply _ _
      | .subst _ _, .lambda _ | .subst _ _, .multiLambda _ _
      | .subst _ _, .collection _ _ _ =>
        simp [matchPattern] at hmem
    -- matchArgs soundness
    · intro pargs targs bs hle hmem
      match pargs, targs with
      | [], [] =>
        simp only [matchArgs, List.mem_singleton] at hmem; subst hmem; exact .nil
      | [], _ :: _ => simp [matchArgs] at hmem
      | _ :: _, [] => simp [matchArgs] at hmem
      | p :: ps, t :: ts =>
        unfold matchArgs at hmem
        rw [List.mem_flatMap] at hmem
        obtain ⟨hb, hb_mem, hmem2⟩ := hmem
        rw [List.mem_filterMap] at hmem2
        obtain ⟨tb, htb_mem, hmerge⟩ := hmem2
        exact .cons
          (ih_pat p t hb (by have := sizeOf_head_lt_cons p ps; omega) hb_mem)
          (ih_args ps ts tb (by have := sizeOf_tail_lt_cons p ps; omega) htb_mem)
          hmerge
    -- matchBag soundness
    · intro ppats rest ct telems bs hle hmem
      match ppats with
      | [] =>
        unfold matchBag at hmem
        match rest with
        | none =>
          dsimp only at hmem
          split at hmem
          next hemp =>
            simp only [List.mem_singleton] at hmem; subst hmem
            have := eq_nil_of_isEmpty hemp; subst this; exact .nilNoRest
          next => simp at hmem
        | some rv =>
          simp only [List.mem_singleton] at hmem; subst hmem
          exact .nilRest
      | ppat :: prest =>
        unfold matchBag at hmem
        rw [List.mem_flatMap] at hmem
        obtain ⟨⟨telem, i⟩, hmem_zip, hmem2⟩ := hmem
        rw [List.mem_flatMap] at hmem2
        obtain ⟨hb, hb_mem, hmem3⟩ := hmem2
        rw [List.mem_filterMap] at hmem3
        obtain ⟨restB, hrestB_mem, hmerge⟩ := hmem3
        have hi := lt_length_of_mem_zipIdx hmem_zip
        have htelem_eq := eq_getElem_of_mem_zipIdx hmem_zip hi
        subst htelem_eq
        exact .cons i hi
          (ih_pat ppat telems[i] hb
            (by have := sizeOf_head_lt_cons ppat prest; omega) hb_mem)
          (ih_bag prest rest ct (telems.eraseIdx i) restB
            (by have := sizeOf_tail_lt_cons ppat prest; omega) hrestB_mem)
          hmerge

theorem matchPattern_sound {pat t : Pattern} {bs : Bindings}
    (h : bs ∈ matchPattern pat t) : MatchRel pat t bs :=
  (sound_all (sizeOf pat)).1 pat t bs (Nat.le_refl _) h

theorem matchArgs_sound {pargs targs : List Pattern} {bs : Bindings}
    (h : bs ∈ matchArgs pargs targs) : MatchArgsRel pargs targs bs :=
  (sound_all (sizeOf pargs)).2.1 pargs targs bs (Nat.le_refl _) h

theorem matchBag_sound {ppats : List Pattern} {rest : Option String}
    {ct : CollType} {telems : List Pattern} {bs : Bindings}
    (h : bs ∈ matchBag ppats rest ct telems) : MatchBagRel ppats rest ct telems bs :=
  (sound_all (sizeOf ppats)).2.2 ppats rest ct telems bs (Nat.le_refl _) h

/-! ## Completeness: relational → executable

Also by strong Nat induction on `sizeOf` of the pattern, since `induction`
does not support mutual inductives. After `cases h`, each constructor gives
sub-derivations on strictly smaller patterns. -/

private theorem complete_all (n : Nat) :
    (∀ pat t bs, sizeOf pat ≤ n → MatchRel pat t bs → bs ∈ matchPattern pat t) ∧
    (∀ pargs targs bs, sizeOf pargs ≤ n →
      MatchArgsRel pargs targs bs → bs ∈ matchArgs pargs targs) ∧
    (∀ ppats rest ct telems bs, sizeOf ppats ≤ n →
      MatchBagRel ppats rest ct telems bs → bs ∈ matchBag ppats rest ct telems) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro pat _ _ hle _
      exact absurd hle (by have := sizeOf_pattern_pos pat; omega)
    · intro pargs targs bs hle h
      cases h with
      | nil => simp [matchArgs]
      | cons => exact absurd hle (by simp [sizeOf, List._sizeOf_1]; try omega)
    · intro ppats rest ct telems bs hle h
      cases h with
      | nilNoRest => simp [matchBag, List.isEmpty]
      | nilRest => simp [matchBag]
      | cons => exact absurd hle (by simp [sizeOf, List._sizeOf_1]; try omega)
  | succ m ih =>
    obtain ⟨ih_pat, ih_args, ih_bag⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    -- MatchRel → matchPattern
    · intro pat t bs hle h
      cases h with
      | fvar => simp [matchPattern]
      | bvar => simp [matchPattern]
      | apply hargs hlen =>
        rename_i pargs targs c
        unfold matchPattern
        simp only [beq_self_eq_true, beq_iff_eq.mpr hlen, Bool.true_and, ↓reduceIte]
        exact ih_args pargs targs _ (by have := sizeOf_args_lt_apply c pargs; omega) hargs
      | lambda hmatch =>
        rename_i bodyPat bodyConcrete
        unfold matchPattern
        exact ih_pat bodyPat bodyConcrete _ (by have := sizeOf_body_lt_lambda bodyPat; omega) hmatch
      | multiLambda hmatch =>
        rename_i bodyPat bodyConcrete n'
        unfold matchPattern
        simp only [beq_self_eq_true, ↓reduceIte]
        exact ih_pat bodyPat bodyConcrete _ (by have := sizeOf_body_lt_multiLambda n' bodyPat; omega) hmatch
      | collection hbag =>
        rename_i pelems rest ct telems rest₂
        unfold matchPattern
        simp only [beq_self_eq_true, ↓reduceIte]
        exact ih_bag pelems rest ct telems _ (by have := sizeOf_elems_lt_collection ct pelems rest; omega) hbag
      | subst hm1 hm2 hmerge =>
        rename_i pbody tbody b1 prepl trepl b2
        unfold matchPattern
        rw [List.mem_flatMap]
        exact ⟨b1, ih_pat pbody tbody b1
            (by have := sizeOf_pbody_lt_subst pbody prepl; omega) hm1,
          List.mem_filterMap.mpr
            ⟨b2, ih_pat prepl trepl b2
              (by have := sizeOf_prepl_lt_subst pbody prepl; omega) hm2, hmerge⟩⟩
    -- MatchArgsRel → matchArgs
    · intro pargs targs bs hle h
      cases h with
      | nil => simp [matchArgs]
      | cons hmatch hargs hmerge =>
        rename_i p t hb ps ts tb
        unfold matchArgs
        rw [List.mem_flatMap]
        exact ⟨hb, ih_pat p t hb (by have := sizeOf_head_lt_cons p ps; omega) hmatch,
          List.mem_filterMap.mpr
            ⟨tb, ih_args ps ts tb (by have := sizeOf_tail_lt_cons p ps; omega) hargs, hmerge⟩⟩
    -- MatchBagRel → matchBag
    · intro ppats rest ct telems bs hle h
      cases h with
      | nilNoRest => simp [matchBag, List.isEmpty]
      | nilRest => simp [matchBag]
      | cons i hi hmatch hbag hmerge =>
        rename_i ppat hb prest restB
        unfold matchBag
        rw [List.mem_flatMap]
        refine ⟨(telems[i], i), mem_zipIdx_of_lt telems i hi, ?_⟩
        rw [List.mem_flatMap]
        exact ⟨hb, ih_pat ppat telems[i] hb
            (by have := sizeOf_head_lt_cons ppat prest; omega) hmatch,
          List.mem_filterMap.mpr
            ⟨restB, ih_bag prest rest ct (telems.eraseIdx i) restB
              (by have := sizeOf_tail_lt_cons ppat prest; omega) hbag, hmerge⟩⟩

theorem matchRel_complete {pat t : Pattern} {bs : Bindings}
    (h : MatchRel pat t bs) : bs ∈ matchPattern pat t :=
  (complete_all (sizeOf pat)).1 pat t bs (Nat.le_refl _) h

theorem matchArgsRel_complete {pargs targs : List Pattern} {bs : Bindings}
    (h : MatchArgsRel pargs targs bs) : bs ∈ matchArgs pargs targs :=
  (complete_all (sizeOf pargs)).2.1 pargs targs bs (Nat.le_refl _) h

theorem matchBagRel_complete {ppats : List Pattern} {rest : Option String}
    {ct : CollType} {telems : List Pattern} {bs : Bindings}
    (h : MatchBagRel ppats rest ct telems bs) : bs ∈ matchBag ppats rest ct telems :=
  (complete_all (sizeOf ppats)).2.2 ppats rest ct telems bs (Nat.le_refl _) h

/-! ## Equivalences -/

theorem matchPattern_iff_matchRel {pat t : Pattern} {bs : Bindings} :
    bs ∈ matchPattern pat t ↔ MatchRel pat t bs :=
  ⟨matchPattern_sound, matchRel_complete⟩

theorem matchArgs_iff_matchArgsRel {pargs targs : List Pattern} {bs : Bindings} :
    bs ∈ matchArgs pargs targs ↔ MatchArgsRel pargs targs bs :=
  ⟨matchArgs_sound, matchArgsRel_complete⟩

theorem matchBag_iff_matchBagRel {ppats : List Pattern} {rest : Option String}
    {ct : CollType} {telems : List Pattern} {bs : Bindings} :
    bs ∈ matchBag ppats rest ct telems ↔ MatchBagRel ppats rest ct telems bs :=
  ⟨matchBag_sound, matchBagRel_complete⟩

/-! ## DeclReducesRel: Reduction using MatchRel -/

/-- Declarative one-step reduction using `MatchRel` instead of `matchPattern`.
    This is independent of the executable matching algorithm. -/
inductive DeclReducesRel (lang : LanguageDef) : Pattern → Pattern → Prop where
  | topRule :
      (r : RewriteRule) →
      r ∈ lang.rewrites →
      r.premises = [] →
      (bs : Bindings) →
      MatchRel r.left p bs →
      applyBindings bs r.right = q →
      DeclReducesRel lang p q
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
      MatchRel r.left elems[i] bs →
      {q' : Pattern} →
      applyBindings bs r.right = q' →
      DeclReducesRel lang (.collection ct elems rest)
                          (.collection ct (elems.set i q') rest)

/-! ## Equivalence: DeclReducesRel ↔ DeclReduces -/

theorem declReducesRel_of_declReduces {lang : LanguageDef} {p q : Pattern}
    (h : DeclReduces lang p q) : DeclReducesRel lang p q := by
  cases h with
  | topRule r hr hprem bs hbs hq =>
    exact .topRule r hr hprem bs (matchPattern_sound hbs) hq
  | @congElem elems ct rest hct i hi r hr hprem bs hbs q' hq =>
    exact .congElem hct i hi r hr hprem bs (matchPattern_sound hbs) hq

theorem declReduces_of_declReducesRel {lang : LanguageDef} {p q : Pattern}
    (h : DeclReducesRel lang p q) : DeclReduces lang p q := by
  cases h with
  | topRule r hr hprem bs hbs hq =>
    exact .topRule r hr hprem bs (matchRel_complete hbs) hq
  | @congElem elems ct rest hct i hi r hr hprem bs hbs q' hq =>
    exact .congElem hct i hi r hr hprem bs (matchRel_complete hbs) hq

theorem declReducesRel_iff_declReduces {lang : LanguageDef} {p q : Pattern} :
    DeclReducesRel lang p q ↔ DeclReduces lang p q :=
  ⟨declReduces_of_declReducesRel, declReducesRel_of_declReduces⟩

/-! ## Independence Triangle -/

theorem engine_sound_rel {lang : LanguageDef} {p q : Pattern}
    (h : q ∈ rewriteWithContext lang p) : DeclReducesRel lang p q :=
  declReducesRel_of_declReduces (engine_sound h)

theorem engine_complete_rel {lang : LanguageDef} {p q : Pattern}
    (h : DeclReducesRel lang p q) : q ∈ rewriteWithContext lang p :=
  engine_complete (declReduces_of_declReducesRel h)

/-! ## mergeBindings Subsumption

Fold invariants for `mergeBindings b1 b2 = some bs`:
- Left: every binding in `b1` is preserved in `bs`.
- Right: every binding in `b2` is present in `bs`. -/

/-- Fold invariant (left): if `(x, v)` is findable in the accumulator before the fold,
    it remains findable (with the same value) in the final result. -/
private theorem foldlM_merge_preserves_left (b2 : Bindings) (acc bs : Bindings)
    (hfold : List.foldlM (fun acc' pair =>
      match acc'.find? (·.1 == pair.1) with
      | none => some (pair :: acc')
      | some (_, existing) => if existing == pair.2 then some acc' else none) acc b2 = some bs)
    {x : String} {v : Pattern}
    (hx : acc.find? (·.1 == x) = some (x, v)) :
    bs.find? (·.1 == x) = some (x, v) := by
  induction b2 generalizing acc with
  | nil =>
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hfold
    subst hfold; exact hx
  | cons pair tl ih =>
    obtain ⟨name, val⟩ := pair
    simp only [List.foldlM_cons] at hfold
    dsimp only [Bind.bind, Option.bind] at hfold
    cases hn : acc.find? (fun p => p.1 == (name, val).1) with
    | none =>
      simp only [hn] at hfold
      apply ih _ hfold
      simp only [List.find?_cons]
      by_cases hname : (name, val).1 == x
      · simp only [hname]
        have : (fun (p : String × Pattern) => p.1 == name) = (·.1 == x) := by
          ext p; simp [show name = x from beq_iff_eq.mp hname]
        rw [this] at hn; rw [hn] at hx; exact absurd hx (by simp)
      · simp only [hname]; exact hx
    | some p =>
      obtain ⟨s, e⟩ := p
      simp only [hn] at hfold
      cases heq : (e == (name, val).2)
      · simp only [heq] at hfold; simp at hfold
      · simp only [heq] at hfold; exact ih _ hfold hx

/-- If `(x, v)` is in `b1` and `mergeBindings b1 b2 = some bs`, then `bs` finds `x → v`. -/
theorem mergeBindings_subsumed_left {b1 b2 bs : Bindings}
    (hm : mergeBindings b1 b2 = some bs)
    {x : String} {v : Pattern}
    (hx : b1.find? (·.1 == x) = some (x, v)) :
    bs.find? (·.1 == x) = some (x, v) := by
  apply foldlM_merge_preserves_left b2 b1 bs _ hx
  simpa [mergeBindings] using hm

/-- Helper: extract the first component from a successful `find?` on `Bindings`. -/
private theorem find?_fst_eq {bs : Bindings} {x : String} {p : String × Pattern}
    (hf : bs.find? (·.1 == x) = some p) : p.1 = x := by
  have := List.find?_some hf
  exact beq_iff_eq.mp this

/-- If `(x, v)` is in `b2` and `mergeBindings b1 b2 = some bs`, then `bs` finds `x → v`. -/
theorem mergeBindings_subsumed_right {b1 b2 bs : Bindings}
    (hm : mergeBindings b1 b2 = some bs)
    {x : String} {v : Pattern}
    (hx : b2.find? (·.1 == x) = some (x, v)) :
    bs.find? (·.1 == x) = some (x, v) := by
  induction b2 generalizing b1 with
  | nil => simp at hx
  | cons pair tl ih =>
    obtain ⟨name, val⟩ := pair
    simp only [List.find?_cons] at hx
    simp only [mergeBindings, List.foldlM_cons] at hm
    dsimp only [Bind.bind, Option.bind] at hm
    by_cases hname : name == x
    · -- head matches x: hx says (name, val) = (x, v)
      simp only [hname, Option.some.injEq] at hx
      have hneq : name = x := (Prod.ext_iff.mp hx).1
      have hveq : val = v := (Prod.ext_iff.mp hx).2
      rw [hneq, hveq] at hm
      cases hn : b1.find? (fun p => p.1 == x) with
      | none =>
        rw [show (fun (p : String × Pattern) => p.1 == (x, v).1) = (fun p => p.1 == x) from rfl,
            hn] at hm
        apply foldlM_merge_preserves_left tl ((x, v) :: b1) bs
        · exact hm
        · simp
      | some p =>
        obtain ⟨s, e⟩ := p
        rw [show (fun (p : String × Pattern) => p.1 == (x, v).1) = (fun p => p.1 == x) from rfl,
            hn] at hm
        cases heq : (e == v)
        · simp only [heq] at hm; simp at hm
        · simp only [heq] at hm
          have hs : s = x := by
            have := List.find?_some hn; exact beq_iff_eq.mp this
          have he : e = v := beq_iff_eq.mp heq
          subst hs he
          apply foldlM_merge_preserves_left tl b1 bs
          · exact hm
          · exact hn
    · -- head doesn't match x → recurse into tail
      simp only [hname] at hx
      cases hn : b1.find? (fun p => p.1 == (name, val).1) with
      | none =>
        simp only [hn] at hm
        exact ih hm hx
      | some p =>
        obtain ⟨s, e⟩ := p
        simp only [hn] at hm
        cases heq : (e == (name, val).2)
        · simp only [heq] at hm; simp at hm
        · simp only [heq] at hm
          exact ih hm hx

/-! ## Bindings Extension -/

/-- Bindings `bs'` extends `bs`: every variable value in `bs` is preserved in `bs'`. -/
def BindingsExtends (bs bs' : Bindings) : Prop :=
  ∀ x v, bs.find? (·.1 == x) = some (x, v) → bs'.find? (·.1 == x) = some (x, v)

private theorem extends_trans {b1 b2 b3 : Bindings}
    (h12 : BindingsExtends b1 b2) (h23 : BindingsExtends b2 b3) : BindingsExtends b1 b3 :=
  fun x v hx => h23 x v (h12 x v hx)

private theorem extends_of_mergeBindings_left {b1 b2 bs : Bindings}
    (hm : mergeBindings b1 b2 = some bs) : BindingsExtends b1 bs :=
  fun _ _ hx => mergeBindings_subsumed_left hm hx

private theorem extends_of_mergeBindings_right {b1 b2 bs : Bindings}
    (hm : mergeBindings b1 b2 = some bs) : BindingsExtends b2 bs :=
  fun _ _ hx => mergeBindings_subsumed_right hm hx

/-! ## isMatchCorrectListAux ↔ forall -/

private theorem isMatchCorrectListAux_iff_forall (l : List Pattern) :
    isMatchCorrectListAux l = true ↔ ∀ p ∈ l, Pattern.isMatchCorrect p = true := by
  induction l with
  | nil => simp [isMatchCorrectListAux]
  | cons p ps ih =>
    simp only [isMatchCorrectListAux, Bool.and_eq_true,
               List.mem_cons, forall_eq_or_imp]
    exact ⟨fun ⟨hp, hps⟩ => ⟨hp, ih.mp hps⟩, fun ⟨hp, hps⟩ => ⟨hp, ih.mpr hps⟩⟩

/-! ## matchRel_correct: Correctness for isMatchCorrect patterns

The stronger `correct_all_strong` proves: for `isMatchCorrect` patterns,
`applyBindings bs' pat = t` for **any** extension `bs' ⊇ bs`. This handles
the `MatchArgsRel.cons` case where child bindings `hb` and `tb` are merged
into `bs`, but the IH is over `hb` (resp. `tb`), not `bs`.
-/

private theorem correct_all_strong (n : Nat) :
    (∀ pat t bs, sizeOf pat ≤ n →
      Pattern.isMatchCorrect pat = true →
      MatchRel pat t bs →
      ∀ bs', BindingsExtends bs bs' → applyBindings bs' pat = t) ∧
    (∀ pargs targs bs, sizeOf pargs ≤ n →
      (∀ p ∈ pargs, Pattern.isMatchCorrect p = true) →
      MatchArgsRel pargs targs bs →
      ∀ bs', BindingsExtends bs bs' → pargs.map (applyBindings bs') = targs) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro pat _ _ hle; exact absurd hle (by have := sizeOf_pattern_pos pat; omega)
    · intro pargs _ _ hle _ h
      cases h with
      | nil => intro _ _; rfl
      | cons => exact absurd hle (by simp [sizeOf, List._sizeOf_1]; try omega)
  | succ m ih =>
    obtain ⟨ih_pat, ih_args⟩ := ih
    refine ⟨?_, ?_⟩
    -- MatchRel case
    · intro pat t bs hle hmc h bs' hext
      cases h with
      | fvar =>
        rename_i x
        simp only [applyBindings]
        have : bs'.find? (·.1 == x) = some (x, t) :=
          hext x t (by simp [List.find?])
        simp [this]
      | bvar => simp [applyBindings]
      | apply hargs hlen =>
        rename_i pargs targs c
        simp only [Pattern.isMatchCorrect, isMatchCorrectAux] at hmc
        simp only [applyBindings]; congr 1
        exact ih_args pargs targs bs
          (by have := sizeOf_args_lt_apply c pargs; omega)
          ((isMatchCorrectListAux_iff_forall pargs).mp hmc) hargs bs' hext
      | lambda hmatch =>
        rename_i bodyPat bodyConcrete
        simp only [Pattern.isMatchCorrect, isMatchCorrectAux] at hmc
        simp only [applyBindings]; congr 1
        exact ih_pat bodyPat bodyConcrete bs
          (by have := sizeOf_body_lt_lambda bodyPat; omega) hmc hmatch bs' hext
      | multiLambda hmatch =>
        rename_i bodyPat bodyConcrete n'
        simp only [Pattern.isMatchCorrect, isMatchCorrectAux] at hmc
        simp only [applyBindings]; congr 1
        exact ih_pat bodyPat bodyConcrete bs
          (by have := sizeOf_body_lt_multiLambda n' bodyPat; omega) hmc hmatch bs' hext
      | collection _ => simp [Pattern.isMatchCorrect, isMatchCorrectAux] at hmc
      | subst _ _ _ => simp [Pattern.isMatchCorrect, isMatchCorrectAux] at hmc
    -- MatchArgsRel case
    · intro pargs targs bs hle hmc h bs' hext
      cases h with
      | nil => simp [List.map]
      | cons hmatch hargs hmerge =>
        rename_i p t hb ps ts tb
        simp only [List.map, List.cons.injEq]
        constructor
        · exact ih_pat p t hb
            (by have := sizeOf_head_lt_cons p ps; omega)
            (hmc p (List.mem_cons_self))
            hmatch bs'
            (extends_trans (extends_of_mergeBindings_left hmerge) hext)
        · exact ih_args ps ts tb
            (by have := sizeOf_tail_lt_cons p ps; omega)
            (fun q hq => hmc q (List.mem_cons_of_mem p hq))
            hargs bs'
            (extends_trans (extends_of_mergeBindings_right hmerge) hext)

/-! ## Public API -/

/-- For `isMatchCorrect` patterns, `MatchRel pat t bs` implies `applyBindings bs pat = t`. -/
theorem matchRel_correct {pat t : Pattern} {bs : Bindings}
    (h : MatchRel pat t bs)
    (hmc : Pattern.isMatchCorrect pat = true) :
    applyBindings bs pat = t :=
  (correct_all_strong (sizeOf pat)).1 pat t bs (Nat.le_refl _) hmc h bs (fun _ _ hx => hx)

/-- For `isMatchCorrect` arg lists, correctness of `applyBindings` over the list. -/
theorem matchArgsRel_correct {pargs targs : List Pattern} {bs : Bindings}
    (h : MatchArgsRel pargs targs bs)
    (hmc : ∀ p ∈ pargs, Pattern.isMatchCorrect p = true) :
    pargs.map (applyBindings bs) = targs :=
  (correct_all_strong (sizeOf pargs)).2 pargs targs bs (Nat.le_refl _) hmc h bs
    (fun _ _ hx => hx)

/-- If `bs ∈ matchPattern pat t` and `pat.isMatchCorrect`, then `applyBindings bs pat = t`. -/
theorem matchPattern_correct {pat t : Pattern} {bs : Bindings}
    (h : bs ∈ matchPattern pat t)
    (hmc : Pattern.isMatchCorrect pat = true) :
    applyBindings bs pat = t :=
  matchRel_correct (matchPattern_sound h) hmc

/-! ## Falsity: matchPattern_correct is FALSE without isMatchCorrect

Bag matching can pick elements out of order, producing bindings where
`applyBindings bs pat` reorders elements vs. the target `t`. -/

/-- Explicit counterexample: bag matching can produce incorrect bindings.
    Pattern `[fvar x, fvar y]` matched against `[b, a]` can yield `bs = [x→a, y→b]`
    via `matchBag` picking `i=1` first, so `applyBindings bs pat = [a, b] ≠ [b, a]`. -/
theorem matchPattern_correct_false :
    ∃ (pat t : Pattern) (bs : Bindings),
        bs ∈ matchPattern pat t ∧ applyBindings bs pat ≠ t := by
  refine ⟨.collection .vec [.fvar "x", .fvar "y"] none,
           .collection .vec [.apply "b" [], .apply "a" []] none,
           [("y", .apply "b" []), ("x", .apply "a" [])], ?_, ?_⟩
  · -- membership: matchBag picks i=1 first, giving x→a, y→b (swapped order)
    simp only [matchPattern, matchBag, List.flatMap, List.zipIdx,
               mergeBindings, BEq.beq]
    decide
  · -- applyBindings gives [a, b] ≠ [b, a]
    simp [applyBindings, List.find?, List.map, List.append_nil]

/-! ## Summary

**0 sorries. 0 axioms.**

### Relational Specification
- `MatchRel`, `MatchArgsRel`, `MatchBagRel`

### Soundness / Completeness / Equivalence
- `matchPattern_sound` / `matchRel_complete` / `matchPattern_iff_matchRel`
- `matchArgs_sound` / `matchArgsRel_complete` / `matchArgs_iff_matchArgsRel`
- `matchBag_sound` / `matchBagRel_complete` / `matchBag_iff_matchBagRel`

### mergeBindings Subsumption
- `mergeBindings_subsumed_left` / `mergeBindings_subsumed_right`

### Correctness (isMatchCorrect fragment)
- `matchRel_correct`: `MatchRel pat t bs → pat.isMatchCorrect → applyBindings bs pat = t`
- `matchArgsRel_correct`: same for argument lists
- `matchPattern_correct`: `bs ∈ matchPattern pat t → pat.isMatchCorrect → applyBindings bs pat = t`

### Falsity (outside isMatchCorrect)
- `matchPattern_correct_false`: explicit bag-collection counterexample

### Independent Reduction
- `DeclReducesRel`, `declReducesRel_iff_declReduces`
- `engine_sound_rel`, `engine_complete_rel`
-/

end Mettapedia.OSLF.MeTTaIL.MatchSpec

