import Mettapedia.OSLF.Framework.PLNSelectorGSLT
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Formula

/-!
# PLN Selector LanguageDef Bridge (GSLT ↔ OSLF LanguageDef)

This module provides a `LanguageDef` view of the core PLN selector rewrites and
connects it to the existing `PLNSelectorExpr.Reduces` relation.

We encode selector expressions as `Pattern`s, define rewrite rules that mirror:

1. `extBayes2`
2. `extBayesFamily` (via symbolic `FMapUpdate`)
3. `normalizeStrength` (finite nonzero regime abstraction)

and prove one-way soundness:

- every `PLNSelectorExpr.Reduces` step is realized by a `langReducesUsing` step
  on encoded patterns (with a decoding relation that interprets `FMapUpdate`).

We also add checker-facing `sat -> sem` plumbing plus concrete `.sat` / `.unsat`
examples for the selector language.
-/

namespace Mettapedia.OSLF.Framework.PLNSelectorLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.PLNSelectorGSLT
open Mettapedia.OSLF.Framework.PLNSelectorGSLT.PLNSelectorExpr
open Mettapedia.OSLF.Formula
open Mettapedia.Logic.PremiseSelection

universe u v

/-! ## Pattern Vocabulary -/

def pAtom : Pattern := .apply "Atom" []
def pFuse (a b : Pattern) : Pattern := .apply "Fuse" [a, b]
def pUpdate (p l : Pattern) : Pattern := .apply "Update" [p, l]
def pNormalizeNZ (p : Pattern) : Pattern := .apply "NormalizeNZ" [p]
def pFuseFamily (xs : Pattern) : Pattern := .apply "FuseFamily" [xs]
def pFNil : Pattern := .apply "FNil" []
def pFCons (x xs : Pattern) : Pattern := .apply "FCons" [x, xs]
def pFMapUpdate (xs l : Pattern) : Pattern := .apply "FMapUpdate" [xs, l]

/-! ## LanguageDef Rules -/

def ruleExtBayes2 : RewriteRule := {
  name := "PLN_ExtBayes2"
  typeContext := [("p", .base "Proc"), ("q", .base "Proc"), ("l", .base "Proc")]
  premises := []
  left := pUpdate (pFuse (.fvar "p") (.fvar "q")) (.fvar "l")
  right := pFuse (pUpdate (.fvar "p") (.fvar "l")) (pUpdate (.fvar "q") (.fvar "l"))
}

def ruleExtBayesFamily : RewriteRule := {
  name := "PLN_ExtBayesFamily"
  typeContext := [("xs", .base "Family"), ("l", .base "Proc")]
  premises := []
  left := pUpdate (pFuseFamily (.fvar "xs")) (.fvar "l")
  right := pFuseFamily (pFMapUpdate (.fvar "xs") (.fvar "l"))
}

def ruleNormalizeStrength : RewriteRule := {
  name := "PLN_NormalizeStrength"
  typeContext := [("e", .base "Proc")]
  premises := []
  left := pNormalizeNZ (.fvar "e")
  right := .fvar "e"
}

/-- LanguageDef parity path for PLN selector rewrites. -/
def plnSelectorLanguageDef : LanguageDef := {
  name := "PLNSelectorGSLT_LanguageDef"
  types := ["Proc", "Family"]
  terms := []
  equations := []
  rewrites := [ruleExtBayes2, ruleExtBayesFamily, ruleNormalizeStrength]
}

/-! ## Encoding / Decoding Relation -/

variable {Goal : Type u} {Fact : Type v}

mutual

  /-- Canonical encoding of selector expressions into `Pattern`. -/
  def encodeExpr : PLNSelectorExpr Goal Fact → Pattern
    | .atom _ => pAtom
    | .fuse a b => pFuse (encodeExpr a) (encodeExpr b)
    | .update p l => pUpdate (encodeExpr p) (encodeExpr l)
    | .normalize _ e => pNormalizeNZ (encodeExpr e)
    | .fuseFamily xs => pFuseFamily (encodeFamily xs)

  /-- Canonical encoding of selector families into `Pattern`. -/
  def encodeFamily : List (PLNSelectorExpr Goal Fact) → Pattern
    | [] => pFNil
    | x :: xs => pFCons (encodeExpr x) (encodeFamily xs)

end

mutual

  /-- Relational decoding from selector patterns to DSL expressions.
  `pAtom` can represent any underlying scorer atom. -/
  inductive ExprEncodes : Pattern → PLNSelectorExpr Goal Fact → Prop where
    | atom (s : Mettapedia.Logic.PremiseSelection.Scorer Goal Fact) :
        ExprEncodes pAtom (.atom s)
    | fuse {pa pb ea eb} :
        ExprEncodes pa ea →
        ExprEncodes pb eb →
        ExprEncodes (pFuse pa pb) (.fuse ea eb)
    | update {pp pl ep el} :
        ExprEncodes pp ep →
        ExprEncodes pl el →
        ExprEncodes (pUpdate pp pl) (.update ep el)
    | normalize {pe e t} :
        ExprEncodes pe e →
        ExprEncodes (pNormalizeNZ pe) (.normalize t e)
    | fuseFamily {pxs xs} :
        FamilyEncodes pxs xs →
        ExprEncodes (pFuseFamily pxs) (.fuseFamily xs)

  /-- Relational decoding of family patterns.
  `FMapUpdate` is interpreted as list-map by `update · l`. -/
  inductive FamilyEncodes : Pattern → List (PLNSelectorExpr Goal Fact) → Prop where
    | nil :
        FamilyEncodes pFNil []
    | cons {px pxs ex xs} :
        ExprEncodes px ex →
        FamilyEncodes pxs xs →
        FamilyEncodes (pFCons px pxs) (ex :: xs)
    | mapUpdate {pxs pl xs l} :
        FamilyEncodes pxs xs →
        ExprEncodes pl l →
        FamilyEncodes (pFMapUpdate pxs pl) (xs.map (fun e => .update e l))

end

mutual

  theorem encodeExpr_encodes :
      ∀ e : PLNSelectorExpr Goal Fact, ExprEncodes (encodeExpr e) e
    | .atom s => ExprEncodes.atom s
    | .fuse a b => ExprEncodes.fuse (encodeExpr_encodes a) (encodeExpr_encodes b)
    | .update p l => ExprEncodes.update (encodeExpr_encodes p) (encodeExpr_encodes l)
    | .normalize _t e => ExprEncodes.normalize (encodeExpr_encodes e)
    | .fuseFamily xs => ExprEncodes.fuseFamily (encodeFamily_encodes xs)

  theorem encodeFamily_encodes :
      ∀ xs : List (PLNSelectorExpr Goal Fact), FamilyEncodes (encodeFamily xs) xs
    | [] => FamilyEncodes.nil
    | x :: xs => FamilyEncodes.cons (encodeExpr_encodes x) (encodeFamily_encodes xs)

end

/-! ## LanguageDef Step Lemmas -/

abbrev plnSelectorLangReduces (p q : Pattern) : Prop :=
  langReducesUsing RelationEnv.empty plnSelectorLanguageDef p q

theorem plnSelector_lang_extBayes2 (pp qq ll : Pattern) :
    plnSelectorLangReduces
      (pUpdate (pFuse pp qq) ll)
      (pFuse (pUpdate pp ll) (pUpdate qq ll)) := by
  unfold plnSelectorLangReduces langReducesUsing
  let bs0 : Bindings := [("l", ll), ("q", qq), ("p", pp)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := plnSelectorLanguageDef)
    (r := ruleExtBayes2)
    ?hr bs0 ?hmatch bs0 ?hprem ?happly
  · simp [plnSelectorLanguageDef]
  · simp [bs0, ruleExtBayes2, pUpdate, pFuse, matchPattern, matchArgs, mergeBindings]
  · simp [bs0, ruleExtBayes2, applyPremisesWithEnv]
  · simp [bs0, ruleExtBayes2, pUpdate, pFuse, applyBindings]

theorem plnSelector_lang_extBayesFamily (xsp ll : Pattern) :
    plnSelectorLangReduces
      (pUpdate (pFuseFamily xsp) ll)
      (pFuseFamily (pFMapUpdate xsp ll)) := by
  unfold plnSelectorLangReduces langReducesUsing
  let bs0 : Bindings := [("l", ll), ("xs", xsp)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := plnSelectorLanguageDef)
    (r := ruleExtBayesFamily)
    ?hr bs0 ?hmatch bs0 ?hprem ?happly
  · simp [plnSelectorLanguageDef]
  · simp [bs0, ruleExtBayesFamily, pUpdate, pFuseFamily, matchPattern, matchArgs, mergeBindings]
  · simp [bs0, ruleExtBayesFamily, applyPremisesWithEnv]
  · simp [bs0, ruleExtBayesFamily, pFuseFamily, pFMapUpdate, applyBindings]

theorem plnSelector_lang_normalize (ep : Pattern) :
    plnSelectorLangReduces (pNormalizeNZ ep) ep := by
  unfold plnSelectorLangReduces langReducesUsing
  let bs0 : Bindings := [("e", ep)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := plnSelectorLanguageDef)
    (r := ruleNormalizeStrength)
    ?hr bs0 ?hmatch bs0 ?hprem ?happly
  · simp [plnSelectorLanguageDef]
  · simp [bs0, ruleNormalizeStrength, pNormalizeNZ, matchPattern, matchArgs, mergeBindings]
  · simp [bs0, ruleNormalizeStrength, applyPremisesWithEnv]
  · simp [bs0, ruleNormalizeStrength, pNormalizeNZ, applyBindings]

/-! ## One-Way Soundness: DSL Rewrite ⇒ LanguageDef Rewrite -/

theorem reduces_to_langReduces_exists
    {e e' : PLNSelectorExpr Goal Fact}
    (h : PLNSelectorExpr.Reduces e e') :
    ∃ q, plnSelectorLangReduces (encodeExpr e) q ∧ ExprEncodes q e' := by
  cases h with
  | extBayes2 p q l =>
      refine ⟨pFuse (pUpdate (encodeExpr p) (encodeExpr l))
        (pUpdate (encodeExpr q) (encodeExpr l)), ?_, ?_⟩
      · simpa [encodeExpr] using
          plnSelector_lang_extBayes2 (pp := encodeExpr p) (qq := encodeExpr q) (ll := encodeExpr l)
      · exact ExprEncodes.fuse
          (ExprEncodes.update (encodeExpr_encodes p) (encodeExpr_encodes l))
          (ExprEncodes.update (encodeExpr_encodes q) (encodeExpr_encodes l))
  | extBayesFamily xs l =>
      refine ⟨pFuseFamily (pFMapUpdate (encodeFamily xs) (encodeExpr l)), ?_, ?_⟩
      · simpa [encodeExpr] using
          plnSelector_lang_extBayesFamily (xsp := encodeFamily xs) (ll := encodeExpr l)
      · exact ExprEncodes.fuseFamily
          (FamilyEncodes.mapUpdate (encodeFamily_encodes xs) (encodeExpr_encodes l))
  | normalizeStrength t ht htop =>
      refine ⟨encodeExpr e', ?_, ?_⟩
      · simpa [encodeExpr] using plnSelector_lang_normalize (ep := encodeExpr e')
      · exact encodeExpr_encodes e'

/-! ## Reverse Bridge: LanguageDef Rewrite ⇒ DSL Rewrite (decoded) -/

/-- Regime needed to reflect `NormalizeNZ` language-steps back into the
typed selector rewrite relation, which requires `t ≠ 0` and `t ≠ ⊤`. -/
def NormalizeFiniteNonzero : PLNSelectorExpr Goal Fact → Prop
  | .normalize t _ => t ≠ 0 ∧ t ≠ ⊤
  | _ => True

/-- Expressions on which `encodeExpr` is injective through `ExprEncodes`.
This excludes atom payloads and normalize nodes (the normalize scale is
abstracted by `pNormalizeNZ`). -/
inductive EncodeInjective : PLNSelectorExpr Goal Fact → Prop where
  | fuse {a b} : EncodeInjective a → EncodeInjective b → EncodeInjective (.fuse a b)
  | update {p l} : EncodeInjective p → EncodeInjective l → EncodeInjective (.update p l)
  | fuseFamily_nil : EncodeInjective (.fuseFamily [])
  | fuseFamily_cons {x xs} :
      EncodeInjective x → EncodeInjective (.fuseFamily xs) → EncodeInjective (.fuseFamily (x :: xs))

mutual

  private theorem exprEncodes_fuse_inv_aux
      {p pa pb : Pattern} {e : PLNSelectorExpr Goal Fact}
      (h : ExprEncodes p e)
      (hp : p = pFuse pa pb) :
      ∃ ea eb, e = .fuse ea eb ∧ ExprEncodes pa ea ∧ ExprEncodes pb eb := by
    cases h with
    | atom _ =>
        simp [pAtom, pFuse] at hp
    | fuse hEa hEb =>
        cases hp
        exact ⟨_, _, rfl, hEa, hEb⟩
    | update _ _ =>
        simp [pUpdate, pFuse] at hp
    | normalize _ =>
        simp [pNormalizeNZ, pFuse] at hp
    | fuseFamily _ =>
        simp [pFuseFamily, pFuse] at hp

  private theorem exprEncodes_update_inv_aux
      {p pp pl : Pattern} {e : PLNSelectorExpr Goal Fact}
      (h : ExprEncodes p e)
      (hp : p = pUpdate pp pl) :
      ∃ ep el, e = .update ep el ∧ ExprEncodes pp ep ∧ ExprEncodes pl el := by
    cases h with
    | atom _ =>
        simp [pAtom, pUpdate] at hp
    | fuse _ _ =>
        simp [pFuse, pUpdate] at hp
    | update hEp hEl =>
        cases hp
        exact ⟨_, _, rfl, hEp, hEl⟩
    | normalize _ =>
        simp [pNormalizeNZ, pUpdate] at hp
    | fuseFamily _ =>
        simp [pFuseFamily, pUpdate] at hp

  private theorem exprEncodes_fuseFamily_inv_aux
      {p pxs : Pattern} {e : PLNSelectorExpr Goal Fact}
      (h : ExprEncodes p e)
      (hp : p = pFuseFamily pxs) :
      ∃ xs, e = .fuseFamily xs ∧ FamilyEncodes pxs xs := by
    cases h with
    | atom _ =>
        simp [pAtom, pFuseFamily] at hp
    | fuse _ _ =>
        simp [pFuse, pFuseFamily] at hp
    | update _ _ =>
        simp [pUpdate, pFuseFamily] at hp
    | normalize _ =>
        simp [pNormalizeNZ, pFuseFamily] at hp
    | fuseFamily hXs =>
        cases hp
        exact ⟨_, rfl, hXs⟩

  private theorem familyEncodes_nil_inv_aux
      {p : Pattern} {ys : List (PLNSelectorExpr Goal Fact)}
      (h : FamilyEncodes p ys)
      (hp : p = pFNil) :
      ys = [] := by
    cases h with
    | nil =>
        rfl
    | cons _ _ =>
        simp [pFCons, pFNil] at hp
    | mapUpdate _ _ =>
        simp [pFMapUpdate, pFNil] at hp

  private theorem familyEncodes_cons_inv_aux
      {p px pxs : Pattern} {ys : List (PLNSelectorExpr Goal Fact)}
      (h : FamilyEncodes p ys)
      (hp : p = pFCons px pxs) :
      ∃ y ys', ys = y :: ys' ∧ ExprEncodes px y ∧ FamilyEncodes pxs ys' := by
    cases h with
    | nil =>
        simp [pFNil, pFCons] at hp
    | cons hY hYs =>
        cases hp
        exact ⟨_, _, rfl, hY, hYs⟩
    | mapUpdate _ _ =>
        simp [pFMapUpdate, pFCons] at hp

  private theorem exprEncodes_fuse_inv
      {pa pb : Pattern} {e : PLNSelectorExpr Goal Fact}
      (h : ExprEncodes (pFuse pa pb) e) :
      ∃ ea eb, e = .fuse ea eb ∧ ExprEncodes pa ea ∧ ExprEncodes pb eb :=
    exprEncodes_fuse_inv_aux (h := h) (hp := rfl)

  private theorem exprEncodes_update_inv
      {pp pl : Pattern} {e : PLNSelectorExpr Goal Fact}
      (h : ExprEncodes (pUpdate pp pl) e) :
      ∃ ep el, e = .update ep el ∧ ExprEncodes pp ep ∧ ExprEncodes pl el :=
    exprEncodes_update_inv_aux (h := h) (hp := rfl)

  private theorem exprEncodes_fuseFamily_inv
      {pxs : Pattern} {e : PLNSelectorExpr Goal Fact}
      (h : ExprEncodes (pFuseFamily pxs) e) :
      ∃ xs, e = .fuseFamily xs ∧ FamilyEncodes pxs xs :=
    exprEncodes_fuseFamily_inv_aux (h := h) (hp := rfl)

  private theorem familyEncodes_nil_inv
      {ys : List (PLNSelectorExpr Goal Fact)}
      (h : FamilyEncodes pFNil ys) :
      ys = [] :=
    familyEncodes_nil_inv_aux (h := h) (hp := rfl)

  private theorem familyEncodes_cons_inv
      {px pxs : Pattern} {ys : List (PLNSelectorExpr Goal Fact)}
      (h : FamilyEncodes (pFCons px pxs) ys) :
      ∃ y ys', ys = y :: ys' ∧ ExprEncodes px y ∧ FamilyEncodes pxs ys' :=
    familyEncodes_cons_inv_aux (h := h) (hp := rfl)

  theorem exprEncodes_encode_unique_of_encodeInjective :
      ∀ {e e' : PLNSelectorExpr Goal Fact},
        EncodeInjective e → ExprEncodes (encodeExpr e) e' → e' = e
    | _, _, hFree, hEnc => by
        cases hFree with
        | @fuse a b ha hb =>
            rcases exprEncodes_fuse_inv (pa := encodeExpr a) (pb := encodeExpr b) hEnc
              with ⟨ea, eb, heq, hEa, hEb⟩
            subst heq
            rcases exprEncodes_encode_unique_of_encodeInjective (e := a) (e' := ea) ha hEa with rfl
            rcases exprEncodes_encode_unique_of_encodeInjective (e := b) (e' := eb) hb hEb with rfl
            rfl
        | @update p l hp hl =>
            rcases exprEncodes_update_inv (pp := encodeExpr p) (pl := encodeExpr l) hEnc
              with ⟨ep, el, heq, hEp, hEl⟩
            subst heq
            rcases exprEncodes_encode_unique_of_encodeInjective (e := p) (e' := ep) hp hEp with rfl
            rcases exprEncodes_encode_unique_of_encodeInjective (e := l) (e' := el) hl hEl with rfl
            rfl
        | fuseFamily_nil =>
            rcases exprEncodes_fuseFamily_inv (pxs := pFNil) hEnc with ⟨ys, heq, hYs⟩
            subst heq
            simpa using familyEncodes_nil_inv hYs
        | @fuseFamily_cons x xs hx hxs =>
            rcases exprEncodes_fuseFamily_inv
              (pxs := pFCons (encodeExpr x) (encodeFamily xs)) hEnc with ⟨ys, heq, hYs⟩
            subst heq
            rcases familyEncodes_cons_inv
              (px := encodeExpr x) (pxs := encodeFamily xs) hYs with
              ⟨y, ys', hys, hY, hYs'⟩
            subst hys
            rcases exprEncodes_encode_unique_of_encodeInjective (e := x) (e' := y) hx hY with rfl
            rcases familyEncodes_encode_unique_of_encodeInjective (xs := xs) (ys := ys') hxs hYs' with rfl
            rfl

  theorem familyEncodes_encode_unique_of_encodeInjective :
      ∀ {xs ys : List (PLNSelectorExpr Goal Fact)},
        EncodeInjective (.fuseFamily xs) → FamilyEncodes (encodeFamily xs) ys → ys = xs
    | [], _, hFree, hEnc => by
        cases hFree with
        | fuseFamily_nil =>
            simpa using familyEncodes_nil_inv hEnc
    | x :: xs, _, hFree, hEnc => by
        cases hFree with
        | fuseFamily_cons hx hxs =>
            rcases familyEncodes_cons_inv
              (px := encodeExpr x) (pxs := encodeFamily xs) hEnc with
              ⟨y, ys', hys, hY, hYs'⟩
            subst hys
            rcases exprEncodes_encode_unique_of_encodeInjective (e := x) (e' := y) hx hY with rfl
            rcases familyEncodes_encode_unique_of_encodeInjective (xs := xs) (ys := ys') hxs hYs' with rfl
            rfl

end

/-- Reverse bridge (decoded form): if an encoded selector expression performs one
`LanguageDef` rewrite step, then it corresponds to one typed
`PLNSelectorExpr.Reduces` step to some decoded target.

This is the strongest generally valid reverse direction for the current encoding:
atom payloads are intentionally abstracted by `pAtom`, so reverse reconstruction is
existential over the decoded target expression. -/
theorem langReduces_to_reduces_exists_of_normalizeFinite
    {e : PLNSelectorExpr Goal Fact} {q : Pattern}
    (hNorm : NormalizeFiniteNonzero e)
    (h : plnSelectorLangReduces (encodeExpr e) q) :
    ∃ e', PLNSelectorExpr.Reduces e e' ∧ ExprEncodes q e' := by
  have hExec :
      langReducesExecUsing RelationEnv.empty plnSelectorLanguageDef (encodeExpr e) q := by
    exact langReducesUsing_to_exec
      (relEnv := RelationEnv.empty) (lang := plnSelectorLanguageDef) h
  unfold langReducesExecUsing at hExec
  unfold rewriteWithContextWithPremisesUsing at hExec
  have hTop : q ∈ rewriteStepWithPremisesUsing RelationEnv.empty plnSelectorLanguageDef (encodeExpr e) := by
    rcases List.mem_append.mp hExec with hTop | hSub
    · exact hTop
    · cases e <;> simp [encodeExpr, pAtom, pFuse, pUpdate, pNormalizeNZ, pFuseFamily] at hSub
  unfold rewriteStepWithPremisesUsing at hTop
  rw [List.mem_flatMap] at hTop
  rcases hTop with ⟨r, hr, hRule⟩
  have hrCases :
      r = ruleExtBayes2 ∨ r = ruleExtBayesFamily ∨ r = ruleNormalizeStrength := by
    simpa [plnSelectorLanguageDef] using hr
  unfold applyRuleWithPremisesUsing at hRule
  rw [List.mem_flatMap] at hRule
  rcases hRule with ⟨bs0, hbs0, hqMap⟩
  rw [List.mem_map] at hqMap
  rcases hqMap with ⟨bs, hprem, hq⟩
  rcases hrCases with rfl | rfl | rfl
  · -- extBayes2
    have hbs : bs = bs0 := by
      simpa [ruleExtBayes2, applyPremisesWithEnv] using hprem
    subst bs
    cases e with
    | update p l =>
        cases p with
        | fuse p q0 =>
            have hbs0Eq :
                bs0 =
                  [("l", encodeExpr l), ("q", encodeExpr q0), ("p", encodeExpr p)] := by
              simpa [ruleExtBayes2, encodeExpr, pAtom, pUpdate, pFuse,
                pNormalizeNZ, pFuseFamily, matchPattern, matchArgs, mergeBindings] using hbs0
            subst bs0
            have hq' :
                q = pFuse (pUpdate (encodeExpr p) (encodeExpr l))
                  (pUpdate (encodeExpr q0) (encodeExpr l)) := by
              simpa [ruleExtBayes2, pFuse, pUpdate, applyBindings] using hq.symm
            refine ⟨.fuse (.update p l) (.update q0 l), ?_, ?_⟩
            · exact PLNSelectorExpr.Reduces.extBayes2 p q0 l
            · simpa [hq'] using
                (ExprEncodes.fuse
                  (ExprEncodes.update (encodeExpr_encodes p) (encodeExpr_encodes l))
                  (ExprEncodes.update (encodeExpr_encodes q0) (encodeExpr_encodes l)))
        | atom _ =>
            exfalso
            simp [ruleExtBayes2, encodeExpr, pAtom, pUpdate, pFuse, matchPattern, matchArgs, mergeBindings] at hbs0
        | update _ _ =>
            exfalso
            simp [ruleExtBayes2, encodeExpr, pUpdate, pFuse, matchPattern, matchArgs, mergeBindings] at hbs0
        | normalize _ _ =>
            exfalso
            simp [ruleExtBayes2, encodeExpr, pUpdate, pFuse, pNormalizeNZ, matchPattern, matchArgs, mergeBindings] at hbs0
        | fuseFamily _ =>
            exfalso
            simp [ruleExtBayes2, encodeExpr, pUpdate, pFuse, pFuseFamily, matchPattern, matchArgs, mergeBindings] at hbs0
    | atom _ =>
        exfalso
        simp [ruleExtBayes2, encodeExpr, pAtom, pUpdate, pFuse, matchPattern] at hbs0
    | fuse _ _ =>
        exfalso
        simp [ruleExtBayes2, encodeExpr, pUpdate, pFuse, matchPattern] at hbs0
    | normalize _ _ =>
        exfalso
        simp [ruleExtBayes2, encodeExpr, pUpdate, pFuse, pNormalizeNZ, matchPattern] at hbs0
    | fuseFamily _ =>
        exfalso
        simp [ruleExtBayes2, encodeExpr, pUpdate, pFuse, pFuseFamily, matchPattern] at hbs0
  · -- extBayesFamily
    have hbs : bs = bs0 := by
      simpa [ruleExtBayesFamily, applyPremisesWithEnv] using hprem
    subst bs
    cases e with
    | update p l =>
        cases p with
        | fuseFamily xs =>
            have hbs0Eq :
                bs0 = [("l", encodeExpr l), ("xs", encodeFamily xs)] := by
              simpa [ruleExtBayesFamily, encodeExpr, pAtom, pUpdate, pFuse,
                pNormalizeNZ, pFuseFamily, matchPattern, matchArgs, mergeBindings] using hbs0
            subst bs0
            have hq' :
                q = pFuseFamily (pFMapUpdate (encodeFamily xs) (encodeExpr l)) := by
              simpa [ruleExtBayesFamily, pFuseFamily, pFMapUpdate, applyBindings] using hq.symm
            refine ⟨.fuseFamily (xs.map (fun e => .update e l)), ?_, ?_⟩
            · exact PLNSelectorExpr.Reduces.extBayesFamily xs l
            · simpa [hq'] using
                (ExprEncodes.fuseFamily
                  (FamilyEncodes.mapUpdate (encodeFamily_encodes xs) (encodeExpr_encodes l)))
        | atom _ =>
            exfalso
            simp [ruleExtBayesFamily, encodeExpr, pAtom, pUpdate, pFuseFamily, matchPattern, matchArgs, mergeBindings] at hbs0
        | fuse _ _ =>
            exfalso
            simp [ruleExtBayesFamily, encodeExpr, pUpdate, pFuse, pFuseFamily, matchPattern, matchArgs, mergeBindings] at hbs0
        | update _ _ =>
            exfalso
            simp [ruleExtBayesFamily, encodeExpr, pUpdate, pFuseFamily, matchPattern, matchArgs, mergeBindings] at hbs0
        | normalize _ _ =>
            exfalso
            simp [ruleExtBayesFamily, encodeExpr, pUpdate, pNormalizeNZ, pFuseFamily, matchPattern, matchArgs, mergeBindings] at hbs0
    | atom _ =>
        exfalso
        simp [ruleExtBayesFamily, encodeExpr, pAtom, pUpdate, pFuseFamily, matchPattern] at hbs0
    | fuse _ _ =>
        exfalso
        simp [ruleExtBayesFamily, encodeExpr, pUpdate, pFuse, pFuseFamily, matchPattern] at hbs0
    | normalize _ _ =>
        exfalso
        simp [ruleExtBayesFamily, encodeExpr, pUpdate, pNormalizeNZ, pFuseFamily, matchPattern] at hbs0
    | fuseFamily _ =>
        exfalso
        simp [ruleExtBayesFamily, encodeExpr, pUpdate, pFuseFamily, matchPattern] at hbs0
  · -- normalize
    have hbs : bs = bs0 := by
      simpa [ruleNormalizeStrength, applyPremisesWithEnv] using hprem
    subst bs
    cases e with
    | normalize t e0 =>
        rcases hNorm with ⟨ht, htop⟩
        have hbs0Eq : bs0 = [("e", encodeExpr e0)] := by
          simpa [ruleNormalizeStrength, encodeExpr, pAtom, pUpdate, pFuse,
            pNormalizeNZ, pFuseFamily, matchPattern, matchArgs, mergeBindings] using hbs0
        subst bs0
        have hq' : q = encodeExpr e0 := by
          simpa [ruleNormalizeStrength, pNormalizeNZ, applyBindings] using hq.symm
        refine ⟨e0, PLNSelectorExpr.Reduces.normalizeStrength t ht htop e0, ?_⟩
        simpa [hq'] using encodeExpr_encodes e0
    | atom _ =>
        exfalso
        simp [ruleNormalizeStrength, encodeExpr, pAtom, pNormalizeNZ, matchPattern] at hbs0
    | fuse _ _ =>
        exfalso
        simp [ruleNormalizeStrength, encodeExpr, pFuse, pNormalizeNZ, matchPattern] at hbs0
    | update _ _ =>
        exfalso
        simp [ruleNormalizeStrength, encodeExpr, pUpdate, pNormalizeNZ, matchPattern] at hbs0
    | fuseFamily _ =>
        exfalso
        simp [ruleNormalizeStrength, encodeExpr, pFuseFamily, pNormalizeNZ, matchPattern] at hbs0

/-- Existence-level equivalence for one-step behavior at encoded sources:
language reduction exists iff typed selector reduction exists (finite nonzero
regime for normalize nodes). -/
theorem langReduces_exists_iff_reduces_exists_of_normalizeFinite
    {e : PLNSelectorExpr Goal Fact}
    (hNorm : NormalizeFiniteNonzero e) :
    (∃ q, plnSelectorLangReduces (encodeExpr e) q) ↔
      (∃ e', PLNSelectorExpr.Reduces e e') := by
  constructor
  · intro hq
    rcases hq with ⟨q, hq⟩
    rcases langReduces_to_reduces_exists_of_normalizeFinite
      (e := e) (q := q) hNorm hq with ⟨e', hr, _⟩
    exact ⟨e', hr⟩
  · intro hr
    rcases hr with ⟨e', hr⟩
    rcases reduces_to_langReduces_exists (e := e) (e' := e') hr with ⟨q, hq, _⟩
    exact ⟨q, hq⟩

/-- Exact reverse direction at encoded targets on the encode-injective
fragment (no atoms, no normalize nodes). -/
theorem langReduces_encode_to_encode_reduces_of_encodeInjective
    {e e' : PLNSelectorExpr Goal Fact}
    (hNorm : NormalizeFiniteNonzero e)
    (hFree : EncodeInjective e')
    (h : plnSelectorLangReduces (encodeExpr e) (encodeExpr e')) :
    PLNSelectorExpr.Reduces e e' := by
  rcases langReduces_to_reduces_exists_of_normalizeFinite
      (e := e) (q := encodeExpr e') hNorm h with ⟨e'', hRed, hEnc⟩
  have hEq : e'' = e' := by
    simpa using
      (exprEncodes_encode_unique_of_encodeInjective (e := e') (e' := e'') hFree hEnc)
  subst hEq
  exact hRed

/-- Backward-compatible alias. -/
theorem langReduces_encode_to_encode_reduces_of_atomFree
    {e e' : PLNSelectorExpr Goal Fact}
    (hNorm : NormalizeFiniteNonzero e)
    (hFree : EncodeInjective e')
    (h : plnSelectorLangReduces (encodeExpr e) (encodeExpr e')) :
    PLNSelectorExpr.Reduces e e' :=
  langReduces_encode_to_encode_reduces_of_encodeInjective
    (e := e) (e' := e') hNorm hFree h

/-! ### Boundary lemmas for excluded constructors -/

/-- Atom nodes are excluded from the encode-injective fragment. -/
theorem not_encodeInjective_atom
    (s : Mettapedia.Logic.PremiseSelection.Scorer Goal Fact) :
    ¬ EncodeInjective (.atom s) := by
  intro h
  cases h

/-- Normalize nodes are excluded from the encode-injective fragment. -/
theorem not_encodeInjective_normalize
    (t : ENNReal) (e : PLNSelectorExpr Goal Fact) :
    ¬ EncodeInjective (.normalize t e) := by
  intro h
  cases h

/-- Atom payload is abstracted by encoding: all atoms map to the same pattern. -/
@[simp] theorem encodeExpr_atom_const
    (s₁ s₂ : Mettapedia.Logic.PremiseSelection.Scorer Goal Fact) :
    encodeExpr (.atom s₁) = encodeExpr (.atom s₂) := by
  rfl

/-- Normalize scale is abstracted by encoding: only the body is retained. -/
@[simp] theorem encodeExpr_normalize_scale_ignored
    (t1 t2 : ENNReal) (e : PLNSelectorExpr Goal Fact) :
    encodeExpr (.normalize t1 e) = encodeExpr (.normalize t2 e) := by
  rfl

/-! ## Checker-Facing Soundness + Examples -/

def extBayes2Target : Pattern :=
  pFuse (pUpdate pAtom pAtom) (pUpdate pAtom pAtom)

def selectorAtomCheck : AtomCheck := fun a p =>
  if a = "isExtBayes2RHS" then decide (p = extBayes2Target) else false

def selectorAtomSem : AtomSem := fun a p =>
  if a = "isExtBayes2RHS" then p = extBayes2Target else False

theorem selectorAtom_sound :
    ∀ a p, selectorAtomCheck a p = true → selectorAtomSem a p := by
  intro a p h
  unfold selectorAtomCheck at h
  by_cases ha : a = "isExtBayes2RHS"
  · have hdec : decide (p = extBayes2Target) = true := by
      simpa [ha] using h
    have hp : p = extBayes2Target := decide_eq_true_eq.mp hdec
    simpa [selectorAtomSem, ha] using hp
  · simp [ha] at h

theorem plnSelector_checkLangUsing_sat_sound
    {relEnv : RelationEnv} {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (hSat : checkLangUsing relEnv plnSelectorLanguageDef selectorAtomCheck fuel p φ = .sat) :
    sem (langReducesUsing relEnv plnSelectorLanguageDef) selectorAtomSem φ p := by
  exact checkLangUsing_sat_sound
    (relEnv := relEnv) (lang := plnSelectorLanguageDef)
    (I_check := selectorAtomCheck) (I_sem := selectorAtomSem)
    (h_atoms := selectorAtom_sound) hSat

/-- Graph-level checker soundness corollary specialized to the PLN selector
LanguageDef. -/
theorem plnSelector_checkLangUsing_sat_sound_graph
    (C : Type _) [CategoryTheory.Category C]
    {relEnv : RelationEnv} {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    {X : Opposite C}
    (hSat : checkLangUsing relEnv plnSelectorLanguageDef selectorAtomCheck
      fuel p (.dia φ) = .sat) :
    ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
      (C := C) relEnv plnSelectorLanguageDef).Edge.obj X,
      ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := C) relEnv plnSelectorLanguageDef).source.app X e).down = p ∧
      sem (langReducesUsing relEnv plnSelectorLanguageDef) selectorAtomSem φ
        (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := C) relEnv plnSelectorLanguageDef).target.app X e).down) := by
  exact checkLangUsing_sat_sound_graph
    (C := C) (relEnv := relEnv) (lang := plnSelectorLanguageDef)
    (I_check := selectorAtomCheck) (I_sem := selectorAtomSem)
    (h_atoms := selectorAtom_sound) hSat

def demoExtBayes2Src : Pattern := pUpdate (pFuse pAtom pAtom) pAtom
def demoIrreducible : Pattern := pAtom

example :
    checkLangUsing RelationEnv.empty plnSelectorLanguageDef selectorAtomCheck
      3 demoExtBayes2Src (.dia (.atom "isExtBayes2RHS")) = .sat := by
  native_decide

example :
    checkLangUsing RelationEnv.empty plnSelectorLanguageDef selectorAtomCheck
      3 demoIrreducible (.dia .top) = .unsat := by
  native_decide

theorem demoExtBayes2_sat_sem :
    sem (langReducesUsing RelationEnv.empty plnSelectorLanguageDef)
      selectorAtomSem (.dia (.atom "isExtBayes2RHS")) demoExtBayes2Src := by
  have hSat :
      checkLangUsing RelationEnv.empty plnSelectorLanguageDef selectorAtomCheck
        3 demoExtBayes2Src (.dia (.atom "isExtBayes2RHS")) = .sat := by
    native_decide
  exact plnSelector_checkLangUsing_sat_sound hSat

end Mettapedia.OSLF.Framework.PLNSelectorLanguageDef
