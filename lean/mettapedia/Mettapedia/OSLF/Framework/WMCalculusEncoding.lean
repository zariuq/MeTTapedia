import Mettapedia.OSLF.Framework.WMCalculusOSLFBridge

/-!
# WM Calculus — Encoding Faithfulness on Image

This module establishes the bidirectional relationship between the abstract
`WMTerm` type (from `WMCalculusOSLFBridge`, indexed by `WMSort`) and the
concrete `Pattern` representation via the `wmCoreLanguageDef`.

## Architecture

1. **`encodeWM`**: computable encoder `WMTerm s → Pattern`
2. **Constructor injectivity**: `pRevise`, `pExtract`, etc. are injective;
   `encodeWM` is injective within each sort.
3. **`WMStep`**: abstract one-step reduction relation on `WMTerm` (5 core rules).
   Sort-preservation is enforced by the type indices (subject reduction is definitional).
4. **Soundness**: `WMStep t₁ t₂ → langReduces wmCoreLanguageDef (encodeWM t₁) (encodeWM t₂)`
5. **Completeness**: `langReduces wmCoreLanguageDef (encodeWM t₁) q →
   ∃ t₂, WMStep t₁ t₂ ∧ encodeWM t₂ = q`
6. **Star adequacy**: `WMStepStar t₁ t₂ ↔ LangReducesStar ...`
7. **Backward completeness**: lifting box properties to the WMTerm level.

## References

- `WMCalculusOSLFBridge.lean` — `WMSort`, `WMTerm`, `WMTermEncodes`
- `WMCalculusLanguageDef.lean` — `wmCoreLanguageDef`, pattern vocabulary, step lemmas
- `TypeSynthesis.lean` — `langReduces`
-/

namespace Mettapedia.OSLF.Framework.WMCalculusEncoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge

/-! ## Section 1: Computable Encoder -/

/-- Encode a `WMTerm s` as a `Pattern`. -/
def encodeWM : WMTerm s → Pattern
  | .state name => .fvar name
  | .query name => .fvar name
  | .revise t₁ t₂ => pRevise (encodeWM t₁) (encodeWM t₂)
  | .extract tw tq => pExtract (encodeWM tw) (encodeWM tq)
  | .combine t₁ t₂ => pCombine (encodeWM t₁) (encodeWM t₂)
  | .zero => pEvidenceZero

/-! ## Section 2: Constructor Injectivity -/

theorem pRevise_injective {w₁ w₂ w₁' w₂' : Pattern} :
    pRevise w₁ w₂ = pRevise w₁' w₂' → w₁ = w₁' ∧ w₂ = w₂' := by
  intro h; simp [pRevise] at h; exact h

theorem pExtract_injective {w q w' q' : Pattern} :
    pExtract w q = pExtract w' q' → w = w' ∧ q = q' := by
  intro h; simp [pExtract] at h; exact h

theorem pCombine_injective {e₁ e₂ e₁' e₂' : Pattern} :
    pCombine e₁ e₂ = pCombine e₁' e₂' → e₁ = e₁' ∧ e₂ = e₂' := by
  intro h; simp [pCombine] at h; exact h

/-! ## Section 3: Encoding Injectivity -/

/-- Encoding is injective within each sort. -/
theorem encodeWM_injective {s : WMSort} {t₁ t₂ : WMTerm s}
    (h : encodeWM t₁ = encodeWM t₂) : t₁ = t₂ := by
  induction t₁ with
  | state name₁ =>
    cases t₂ with
    | state name₂ => simp [encodeWM] at h; subst h; rfl
    | revise _ _ => simp [encodeWM, pRevise] at h
  | query name₁ =>
    cases t₂ with
    | query name₂ => simp [encodeWM] at h; subst h; rfl
  | revise s₁ s₂ ih₁ ih₂ =>
    cases t₂ with
    | revise s₃ s₄ =>
      simp [encodeWM, pRevise] at h
      obtain ⟨h₁, h₂⟩ := h
      rw [ih₁ h₁, ih₂ h₂]
    | state _ => simp [encodeWM, pRevise] at h
  | extract tw tq ihw ihq =>
    cases t₂ with
    | extract tw' tq' =>
      simp [encodeWM, pExtract] at h
      obtain ⟨h₁, h₂⟩ := h
      rw [ihw h₁, ihq h₂]
    | combine _ _ => simp [encodeWM, pExtract, pCombine] at h
    | zero => simp [encodeWM, pExtract, pEvidenceZero] at h
  | combine e₁ e₂ ih₁ ih₂ =>
    cases t₂ with
    | combine e₃ e₄ =>
      simp [encodeWM, pCombine] at h
      obtain ⟨h₁, h₂⟩ := h
      rw [ih₁ h₁, ih₂ h₂]
    | extract _ _ => simp [encodeWM, pCombine, pExtract] at h
    | zero => simp [encodeWM, pCombine, pEvidenceZero] at h
  | zero =>
    cases t₂ with
    | zero => rfl
    | extract _ _ => simp [encodeWM, pEvidenceZero, pExtract] at h
    | combine _ _ => simp [encodeWM, pEvidenceZero, pCombine] at h

/-! ## Section 4: WMTermEncodes ↔ encodeWM -/

/-- `WMTermEncodes p t` holds iff `p = encodeWM t`. -/
theorem wmTermEncodes_iff_encodeWM {s : WMSort} (p : Pattern) (t : WMTerm s) :
    WMTermEncodes p t ↔ p = encodeWM t := by
  constructor
  · intro h; induction h with
    | state => simp [encodeWM]
    | query => simp [encodeWM]
    | revise _ _ ih₁ ih₂ => simp [encodeWM, pRevise, ih₁, ih₂]
    | extract _ _ ih₁ ih₂ => simp [encodeWM, pExtract, ih₁, ih₂]
    | combine _ _ ih₁ ih₂ => simp [encodeWM, pCombine, ih₁, ih₂]
    | zero => simp [encodeWM, pEvidenceZero]
  · intro h; subst h; induction t with
    | state name => exact .state name
    | query name => exact .query name
    | revise t₁ t₂ ih₁ ih₂ =>
      simp [encodeWM]; exact .revise ih₁ ih₂
    | extract tw tq ihw ihq =>
      simp [encodeWM]; exact .extract ihw ihq
    | combine t₁ t₂ ih₁ ih₂ =>
      simp [encodeWM]; exact .combine ih₁ ih₂
    | zero => simp [encodeWM]; exact .zero

/-! ## Section 5: Abstract WM Step Relation

Sort-preservation is enforced by the type indices: each constructor maps
`WMTerm s → WMTerm s` for the same sort `s`. Subject reduction is definitional. -/

/-- One-step reduction on `WMTerm`, corresponding to the 5 core WM rules.
    Sort preservation is enforced by the type indices. -/
inductive WMStep : WMTerm s → WMTerm s → Prop where
  /-- BinaryEvidence extraction distributes over revision. -/
  | evidence_add (t₁ t₂ : WMTerm .state) (q : WMTerm .query) :
      WMStep (.extract (.revise t₁ t₂) q)
             (.combine (.extract t₁ q) (.extract t₂ q))
  /-- Revision is commutative. -/
  | revision_comm (t₁ t₂ : WMTerm .state) :
      WMStep (.revise t₁ t₂) (.revise t₂ t₁)
  /-- Revision is associative. -/
  | revision_assoc (t₁ t₂ t₃ : WMTerm .state) :
      WMStep (.revise (.revise t₁ t₂) t₃)
             (.revise t₁ (.revise t₂ t₃))
  /-- BinaryEvidence combination is commutative. -/
  | combine_comm (e₁ e₂ : WMTerm .evidence) :
      WMStep (.combine e₁ e₂) (.combine e₂ e₁)
  /-- EvidenceZero is the identity for combination. -/
  | combine_zero (e : WMTerm .evidence) :
      WMStep (.combine e .zero) e

/-! ## Section 6: Soundness -/

/-- Core step lemma: evidence-add via wmCoreLanguageDef. -/
private theorem wmCoreLangReduces_evidenceAdd (pw₁ pw₂ pq : Pattern) :
    langReduces wmCoreLanguageDef
      (pExtract (pRevise pw₁ pw₂) pq)
      (pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)) := by
  unfold langReduces langReducesUsing
  let bs : Bindings := [("q", pq), ("W2", pw₂), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmCoreLanguageDef)
    (r := ruleEvidenceAdd)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp [wmCoreLanguageDef, coreRules]
  · simp [bs, ruleEvidenceAdd, pExtract, pRevise, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleEvidenceAdd, applyPremisesWithEnv]
  · simp [bs, ruleEvidenceAdd, pExtract, pCombine, applyBindings]

private theorem wmCoreLangReduces_revisionComm (pw₁ pw₂ : Pattern) :
    langReduces wmCoreLanguageDef
      (pRevise pw₁ pw₂)
      (pRevise pw₂ pw₁) := by
  unfold langReduces langReducesUsing
  let bs : Bindings := [("W2", pw₂), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmCoreLanguageDef)
    (r := ruleRevisionComm)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp [wmCoreLanguageDef, coreRules]
  · simp [bs, ruleRevisionComm, pRevise, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleRevisionComm, applyPremisesWithEnv]
  · simp [bs, ruleRevisionComm, pRevise, applyBindings]

private theorem wmCoreLangReduces_revisionAssoc (pw₁ pw₂ pw₃ : Pattern) :
    langReduces wmCoreLanguageDef
      (pRevise (pRevise pw₁ pw₂) pw₃)
      (pRevise pw₁ (pRevise pw₂ pw₃)) := by
  unfold langReduces langReducesUsing
  let bs : Bindings := [("W3", pw₃), ("W2", pw₂), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmCoreLanguageDef)
    (r := ruleRevisionAssoc)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp [wmCoreLanguageDef, coreRules]
  · simp [bs, ruleRevisionAssoc, pRevise, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleRevisionAssoc, applyPremisesWithEnv]
  · simp [bs, ruleRevisionAssoc, pRevise, applyBindings]

private theorem wmCoreLangReduces_combineComm (pe₁ pe₂ : Pattern) :
    langReduces wmCoreLanguageDef
      (pCombine pe₁ pe₂)
      (pCombine pe₂ pe₁) := by
  unfold langReduces langReducesUsing
  let bs : Bindings := [("e2", pe₂), ("e1", pe₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmCoreLanguageDef)
    (r := ruleCombineComm)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp [wmCoreLanguageDef, coreRules]
  · simp [bs, ruleCombineComm, pCombine, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleCombineComm, applyPremisesWithEnv]
  · simp [bs, ruleCombineComm, pCombine, applyBindings]

private theorem wmCoreLangReduces_combineZero (pe : Pattern) :
    langReduces wmCoreLanguageDef
      (pCombine pe pEvidenceZero)
      pe := by
  unfold langReduces langReducesUsing
  let bs : Bindings := [("e", pe)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmCoreLanguageDef)
    (r := ruleCombineZero)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp [wmCoreLanguageDef, coreRules]
  · simp [bs, ruleCombineZero, pCombine, pEvidenceZero, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleCombineZero, applyPremisesWithEnv]
  · simp [bs, ruleCombineZero, applyBindings]

/-- Soundness: every `WMStep` lifts to a `langReduces wmCoreLanguageDef` step. -/
theorem wmStep_sound {s : WMSort} (t₁ t₂ : WMTerm s) :
    WMStep t₁ t₂ → langReduces wmCoreLanguageDef (encodeWM t₁) (encodeWM t₂) := by
  intro h
  cases h with
  | evidence_add s₁ s₂ q =>
    simp only [encodeWM]
    exact wmCoreLangReduces_evidenceAdd (encodeWM s₁) (encodeWM s₂) (encodeWM q)
  | revision_comm s₁ s₂ =>
    simp only [encodeWM]
    exact wmCoreLangReduces_revisionComm (encodeWM s₁) (encodeWM s₂)
  | revision_assoc s₁ s₂ s₃ =>
    simp only [encodeWM]
    exact wmCoreLangReduces_revisionAssoc (encodeWM s₁) (encodeWM s₂) (encodeWM s₃)
  | combine_comm e₁ e₂ =>
    simp only [encodeWM]
    exact wmCoreLangReduces_combineComm (encodeWM e₁) (encodeWM e₂)
  | combine_zero e =>
    simp only [encodeWM]
    exact wmCoreLangReduces_combineZero (encodeWM e)

/-! ## Section 7: Completeness

Completeness on image: if `langReduces wmCoreLanguageDef (encodeWM t₁) q` then
there exists `t₂` with `q = encodeWM t₂` and `WMStep t₁ t₂`.

The proof works by:
1. `congElem` is impossible (WM patterns use `.apply`, not `.collection`)
2. Case on which of 5 core rules matched in `topRule`
3. Inversion on `matchPattern r.left (encodeWM t₁)` to reconstruct `t₁` shape
4. Show `applyBindings bs r.right = encodeWM t₂` for the corresponding `WMStep` -/

/-- No WM-encoded term is a `.collection`. This rules out `congElem`. -/
theorem encodeWM_not_collection {s : WMSort} (t : WMTerm s) :
    ∀ ct elems rest, encodeWM t ≠ .collection ct elems rest := by
  intro ct elems rest
  cases t <;> simp [encodeWM, pRevise, pExtract, pCombine, pEvidenceZero]

/-- When the source pattern is not a `.collection`, `DeclReducesWithPremises`
    can only hold via `topRule` (not `congElem`). -/
private theorem topRule_of_apply
    {relEnv : RelationEnv} {lang : LanguageDef} {name : String}
    {args : List Pattern} {q : Pattern}
    (h : DeclReducesWithPremises relEnv lang (.apply name args) q) :
    ∃ (r : RewriteRule), r ∈ lang.rewrites ∧
      ∃ bs, bs ∈ matchPattern r.left (.apply name args) ∧
      ∃ bs', bs' ∈ applyPremisesWithEnv relEnv lang r.premises bs ∧
        applyBindings bs' r.right = q := by
  cases h with
  | topRule r hr bs hmatch bs' hprem happly =>
    exact ⟨r, hr, bs, hmatch, bs', hprem, happly⟩

private theorem topRule_of_fvar
    {relEnv : RelationEnv} {lang : LanguageDef} {name : String} {q : Pattern}
    (h : DeclReducesWithPremises relEnv lang (.fvar name) q) :
    ∃ (r : RewriteRule), r ∈ lang.rewrites ∧
      ∃ bs, bs ∈ matchPattern r.left (.fvar name) ∧
      ∃ bs', bs' ∈ applyPremisesWithEnv relEnv lang r.premises bs ∧
        applyBindings bs' r.right = q := by
  cases h with
  | topRule r hr bs hmatch bs' hprem happly =>
    exact ⟨r, hr, bs, hmatch, bs', hprem, happly⟩

/-- Extract topRule data from any DeclReducesWithPremises on an encoded WM term. -/
private theorem topRule_of_encodeWM {s : WMSort} (t₁ : WMTerm s) (q : Pattern)
    (h : DeclReducesWithPremises RelationEnv.empty wmCoreLanguageDef (encodeWM t₁) q) :
    ∃ (r : RewriteRule), r ∈ wmCoreLanguageDef.rewrites ∧
      ∃ bs, bs ∈ matchPattern r.left (encodeWM t₁) ∧
      ∃ bs', bs' ∈ applyPremisesWithEnv RelationEnv.empty wmCoreLanguageDef r.premises bs ∧
        applyBindings bs' r.right = q := by
  cases t₁ with
  | state name => exact topRule_of_fvar (by simp [encodeWM] at h ⊢; exact h)
  | query name => exact topRule_of_fvar (by simp [encodeWM] at h ⊢; exact h)
  | revise t₁ t₂ => exact topRule_of_apply (by simp [encodeWM, pRevise] at h ⊢; exact h)
  | extract tw tq => exact topRule_of_apply (by simp [encodeWM, pExtract] at h ⊢; exact h)
  | combine t₁ t₂ => exact topRule_of_apply (by simp [encodeWM, pCombine] at h ⊢; exact h)
  | zero => exact topRule_of_apply (by simp [encodeWM, pEvidenceZero] at h ⊢; exact h)

set_option linter.unusedSimpArgs false in
/-- Completeness on image: any core reduction from an encoded term yields an
    encoded result that is a `WMStep` image.

    Note: This theorem establishes that the encoding is *faithful* — no
    spurious reductions exist on the image of `encodeWM`. -/
theorem wmStep_complete {s : WMSort} (t₁ : WMTerm s) (q : Pattern) :
    langReduces wmCoreLanguageDef (encodeWM t₁) q →
    ∃ t₂ : WMTerm s, WMStep t₁ t₂ ∧ encodeWM t₂ = q := by
  intro h
  unfold langReduces langReducesUsing at h
  obtain ⟨r, hr, bs, hmatch, bs', hprem, happly⟩ := topRule_of_encodeWM t₁ q h
  -- r must be one of the 5 core rules
  simp [wmCoreLanguageDef, coreRules] at hr
  -- Case split on which rule matched, then simplify premises (all are [])
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp [ruleEvidenceAdd, ruleRevisionComm, ruleRevisionAssoc, ruleCombineComm,
          ruleCombineZero, applyPremisesWithEnv] at hprem <;>
    subst hprem
  -- Case: ruleEvidenceAdd
  · cases t₁ with
    | extract tw tq =>
      cases tw with
      | revise s₁ s₂ =>
        simp [encodeWM, pExtract, pRevise, ruleEvidenceAdd, matchPattern,
              matchArgs, mergeBindings] at hmatch
        subst hmatch
        simp [ruleEvidenceAdd, applyBindings, pCombine, pExtract] at happly
        subst happly
        exact ⟨.combine (.extract s₁ tq) (.extract s₂ tq),
               .evidence_add s₁ s₂ tq, by simp [encodeWM, pCombine, pExtract, pRevise, pEvidenceZero]⟩
      | _ =>
        simp [encodeWM, pExtract, pRevise, pCombine, pEvidenceZero, ruleEvidenceAdd,
              matchPattern, matchArgs, mergeBindings] at hmatch
    | _ =>
      simp [encodeWM, pExtract, pRevise, pCombine, pEvidenceZero, ruleEvidenceAdd,
            matchPattern, matchArgs, mergeBindings] at hmatch
  -- Case: ruleRevisionComm
  · cases t₁ with
    | revise s₁ s₂ =>
      simp [encodeWM, pRevise, ruleRevisionComm, matchPattern,
            matchArgs, mergeBindings] at hmatch
      subst hmatch
      simp [ruleRevisionComm, applyBindings, pRevise] at happly
      subst happly
      exact ⟨.revise s₂ s₁, .revision_comm s₁ s₂,
             by simp [encodeWM, pCombine, pExtract, pRevise, pEvidenceZero]⟩
    | _ =>
      simp [encodeWM, pRevise, pExtract, pCombine, pEvidenceZero, ruleRevisionComm,
            matchPattern, matchArgs, mergeBindings] at hmatch
  -- Case: ruleRevisionAssoc
  · cases t₁ with
    | revise tw t₃ =>
      cases tw with
      | revise s₁ s₂ =>
        simp [encodeWM, pRevise, ruleRevisionAssoc, matchPattern,
              matchArgs, mergeBindings] at hmatch
        subst hmatch
        simp [ruleRevisionAssoc, applyBindings, pRevise] at happly
        subst happly
        exact ⟨.revise s₁ (.revise s₂ t₃), .revision_assoc s₁ s₂ t₃,
               by simp [encodeWM, pCombine, pExtract, pRevise, pEvidenceZero]⟩
      | _ =>
        simp [encodeWM, pRevise, pExtract, pCombine, pEvidenceZero, ruleRevisionAssoc,
              matchPattern, matchArgs, mergeBindings] at hmatch
    | _ =>
      simp [encodeWM, pRevise, pExtract, pCombine, pEvidenceZero, ruleRevisionAssoc,
            matchPattern, matchArgs, mergeBindings] at hmatch
  -- Case: ruleCombineComm
  · cases t₁ with
    | combine e₁ e₂ =>
      simp [encodeWM, pCombine, ruleCombineComm, matchPattern,
            matchArgs, mergeBindings] at hmatch
      subst hmatch
      simp [ruleCombineComm, applyBindings, pCombine] at happly
      subst happly
      exact ⟨.combine e₂ e₁, .combine_comm e₁ e₂,
             by simp [encodeWM, pCombine, pExtract, pRevise, pEvidenceZero]⟩
    | _ =>
      simp [encodeWM, pCombine, pRevise, pExtract, pEvidenceZero, ruleCombineComm,
            matchPattern, matchArgs, mergeBindings] at hmatch
  -- Case: ruleCombineZero
  · cases t₁ with
    | combine e₁ e₂ =>
      cases e₂ with
      | zero =>
        simp [encodeWM, pCombine, pEvidenceZero, ruleCombineZero, matchPattern,
              matchArgs, mergeBindings] at hmatch
        subst hmatch
        simp [ruleCombineZero, applyBindings] at happly
        subst happly
        exact ⟨e₁, .combine_zero e₁, by simp [encodeWM, pCombine, pExtract, pRevise, pEvidenceZero]⟩
      | _ =>
        simp [encodeWM, pCombine, pRevise, pExtract, pEvidenceZero, ruleCombineZero,
              matchPattern, matchArgs, mergeBindings] at hmatch
    | _ =>
      simp [encodeWM, pCombine, pRevise, pExtract, pEvidenceZero, ruleCombineZero,
            matchPattern, matchArgs, mergeBindings] at hmatch

/-! ## Section 8: Star Adequacy

Multi-step reduction correspondence: `WMStepStar t₁ t₂` iff
`LangReducesStar wmCoreLanguageDef (encodeWM t₁) (encodeWM t₂)`. -/

open Mettapedia.OSLF.Framework.LangMorphism

/-- Multi-step WMTerm reduction: reflexive-transitive closure of WMStep. -/
def WMStepStar {s : WMSort} (t₁ t₂ : WMTerm s) : Prop :=
  Relation.ReflTransGen (fun a b => WMStep a b) t₁ t₂

/-- Forward: `WMStepStar → LangReducesStar`. -/
theorem wmStepStar_sound {s : WMSort} {t₁ t₂ : WMTerm s}
    (h : WMStepStar t₁ t₂) :
    LangReducesStar wmCoreLanguageDef (encodeWM t₁) (encodeWM t₂) := by
  unfold WMStepStar at h
  induction h with
  | refl => exact .refl _
  | tail _ hab ih => exact ih.trans (LangReducesStar.single (wmStep_sound _ _ hab))

/-- Backward: `LangReducesStar` from an encoded term yields an encoded result. -/
theorem wmStepStar_complete {s : WMSort} (t₁ : WMTerm s) (q : Pattern)
    (h : LangReducesStar wmCoreLanguageDef (encodeWM t₁) q) :
    ∃ t₂ : WMTerm s, WMStepStar t₁ t₂ ∧ encodeWM t₂ = q := by
  -- Induction on LangReducesStar after generalizing the start pattern
  generalize hp : encodeWM t₁ = p at h
  induction h generalizing t₁ with
  | refl _ => exact ⟨t₁, .refl, hp⟩
  | step hstep _hstar ih =>
    subst hp
    obtain ⟨t_mid, hstep_wm, hencode_mid⟩ := wmStep_complete _ _ hstep
    obtain ⟨t₂, hstar_wm, hencode₂⟩ := ih t_mid hencode_mid
    exact ⟨t₂, Relation.ReflTransGen.head hstep_wm hstar_wm, hencode₂⟩

/-- Star adequacy biconditional. -/
theorem wmStepStar_adequate {s : WMSort} (t₁ t₂ : WMTerm s) :
    WMStepStar t₁ t₂ ↔
    LangReducesStar wmCoreLanguageDef (encodeWM t₁) (encodeWM t₂) := by
  constructor
  · exact wmStepStar_sound
  · intro h
    obtain ⟨t₂', hstar, hencode⟩ := wmStepStar_complete t₁ _ h
    have := encodeWM_injective hencode
    subst this
    exact hstar

/-! ## Section 9: Biconditional and Box Lifting

The single-step biconditional on the image of `encodeWM`, combining soundness
and completeness with injectivity. Box soundness lifts langBox to WMStep
predecessors.

Note: full backward completeness (`langReduces q (encodeWM t) → ∃ t', ...`)
does NOT hold because `ruleCombineZero` can produce Pattern-level predecessors
(e.g. `Combine(.fvar "x", EvidenceZero)`) that are outside the image of
`encodeWM` for leaf-sorted terms. The biconditional on image is the correct
formulation. -/

/-- Single-step biconditional: `WMStep t₁ t₂ ↔ langReduces ... (encodeWM t₁) (encodeWM t₂)`. -/
theorem wmStep_iff {s : WMSort} (t₁ t₂ : WMTerm s) :
    WMStep t₁ t₂ ↔ langReduces wmCoreLanguageDef (encodeWM t₁) (encodeWM t₂) := by
  constructor
  · exact wmStep_sound t₁ t₂
  · intro h
    obtain ⟨t₂', hstep, hencode⟩ := wmStep_complete t₁ _ h
    have := encodeWM_injective hencode
    subst this
    exact hstep

/-- Box soundness: `langBox` implies all WMStep predecessors satisfy φ. -/
theorem wmBox_sound {s : WMSort} (t : WMTerm s) (φ : Pattern → Prop)
    (h : langBox wmCoreLanguageDef φ (encodeWM t)) :
    ∀ t' : WMTerm s, WMStep t' t → φ (encodeWM t') := by
  intro t' hstep
  rw [langBox_spec] at h
  exact h (encodeWM t') (wmStep_sound t' t hstep)

/-- Diamond completeness: if `WMStep t t'` then `langDiamond φ (encodeWM t)`,
    for any `φ` satisfied by `encodeWM t'`. -/
theorem wmDiamond_complete {s : WMSort} (t t' : WMTerm s) (φ : Pattern → Prop)
    (hstep : WMStep t t') (hφ : φ (encodeWM t')) :
    langDiamond wmCoreLanguageDef φ (encodeWM t) := by
  rw [langDiamond_spec]
  exact ⟨encodeWM t', wmStep_sound t t' hstep, hφ⟩

end Mettapedia.OSLF.Framework.WMCalculusEncoding
