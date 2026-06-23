import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MultiStep
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitution

/-!
# Derived Operational Layer for Replication/Restriction Wrappers

This module keeps canonical one-step semantics in
`RhoCalculus/Reduction.lean` and adds a separate derived layer with explicit
administrative operational rules used by higher-level encodings.

Core policy:
- `Reduction.Reduces` remains canonical.
- `ReducesDerived` extends it (currently with `rep_unfold`).
- Bridge lemmas provide adequacy (`core -> derived`) and transport back to
  core for core-compatible derived traces.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-- Derived one-step operational relation.

`core` embeds canonical reduction steps.
`rep_unfold` adds the administrative replication unfolding step.
-/
inductive ReducesDerived : Pattern → Pattern → Type where
  | core {p q : Pattern} : p ⇝ q → ReducesDerived p q
  | rep_unfold {p : Pattern} :
      ReducesDerived (.apply "PReplicate" [p])
                     (.collection .hashBag [p, .apply "PReplicate" [p]] none)
  | par {p q : Pattern} {rest : List Pattern} :
      ReducesDerived p q →
      ReducesDerived (.collection .hashBag (p :: rest) none)
                     (.collection .hashBag (q :: rest) none)
  | par_any {p q : Pattern} {before after : List Pattern} :
      ReducesDerived p q →
      ReducesDerived (.collection .hashBag (before ++ [p] ++ after) none)
                     (.collection .hashBag (before ++ [q] ++ after) none)
  | par_set {p q : Pattern} {rest : List Pattern} :
      ReducesDerived p q →
      ReducesDerived (.collection .hashSet (p :: rest) none)
                     (.collection .hashSet (q :: rest) none)
  | par_set_any {p q : Pattern} {before after : List Pattern} :
      ReducesDerived p q →
      ReducesDerived (.collection .hashSet (before ++ [p] ++ after) none)
                     (.collection .hashSet (before ++ [q] ++ after) none)

infix:50 " ⇝ᵈ " => ReducesDerived

/-- Derived reflexive-transitive closure. -/
inductive ReducesDerivedStar : Pattern → Pattern → Type where
  | refl (p : Pattern) : ReducesDerivedStar p p
  | step {p q r : Pattern} : p ⇝ᵈ q → ReducesDerivedStar q r → ReducesDerivedStar p r

notation:20 p " ⇝ᵈ* " q => ReducesDerivedStar p q

namespace ReducesDerivedStar

/-- Single derived step as a derived star trace. -/
def single {p q : Pattern} (h : p ⇝ᵈ q) : p ⇝ᵈ* q :=
  .step h (.refl q)

/-- Transitivity of derived star closure. -/
noncomputable def trans {p q r : Pattern} (h₁ : p ⇝ᵈ* q) (h₂ : q ⇝ᵈ* r) : p ⇝ᵈ* r := by
  induction h₁ with
  | refl => exact h₂
  | step h hs ih => exact .step h (ih h₂)

/-- Lift a derived-star trace through head-position parallel bag context. -/
noncomputable def par {p q : Pattern} {rest : List Pattern}
    (h : p ⇝ᵈ* q) :
    (.collection .hashBag (p :: rest) none) ⇝ᵈ*
      (.collection .hashBag (q :: rest) none) := by
  induction h with
  | refl p =>
      exact .refl (.collection .hashBag (p :: rest) none)
  | step h₁ hs ih =>
      exact .step (.par h₁) ih

/-- Lift a derived-star trace through arbitrary-position parallel bag context. -/
noncomputable def par_any {p q : Pattern} {before after : List Pattern}
    (h : p ⇝ᵈ* q) :
    (.collection .hashBag (before ++ [p] ++ after) none) ⇝ᵈ*
      (.collection .hashBag (before ++ [q] ++ after) none) := by
  induction h with
  | refl p =>
      exact .refl (.collection .hashBag (before ++ [p] ++ after) none)
  | step h₁ hs ih =>
      exact .step (.par_any h₁) ih

/-- Lift a derived-star trace through head-position set context. -/
noncomputable def par_set {p q : Pattern} {rest : List Pattern}
    (h : p ⇝ᵈ* q) :
    (.collection .hashSet (p :: rest) none) ⇝ᵈ*
      (.collection .hashSet (q :: rest) none) := by
  induction h with
  | refl p =>
      exact .refl (.collection .hashSet (p :: rest) none)
  | step h₁ hs ih =>
      exact .step (.par_set h₁) ih

/-- Lift a derived-star trace through arbitrary-position set context. -/
noncomputable def par_set_any {p q : Pattern} {before after : List Pattern}
    (h : p ⇝ᵈ* q) :
    (.collection .hashSet (before ++ [p] ++ after) none) ⇝ᵈ*
      (.collection .hashSet (before ++ [q] ++ after) none) := by
  induction h with
  | refl p =>
      exact .refl (.collection .hashSet (before ++ [p] ++ after) none)
  | step h₁ hs ih =>
      exact .step (.par_set_any h₁) ih

end ReducesDerivedStar

/-! ## Administrative Trace Helpers -/

/-- One-step replication unfolding as a derived-star trace. -/
def rep_unfold_single (p : Pattern) :
    (.apply "PReplicate" [p]) ⇝ᵈ*
      (.collection .hashBag [p, .apply "PReplicate" [p]] none) :=
  ReducesDerivedStar.single ReducesDerived.rep_unfold

/-- Replication unfolding lifted into arbitrary bag context. -/
noncomputable def rep_unfold_par_any {before after : List Pattern} (p : Pattern) :
    (.collection .hashBag (before ++ [.apply "PReplicate" [p]] ++ after) none) ⇝ᵈ*
      (.collection .hashBag
        (before ++ [.collection .hashBag [p, .apply "PReplicate" [p]] none] ++ after) none) :=
  ReducesDerivedStar.par_any (h := rep_unfold_single p)

/-! ## Core/Derived Bridge -/

/-- Core one-step reduction embeds into derived one-step reduction. -/
def Reduces.toDerived {p q : Pattern} (h : p ⇝ q) : p ⇝ᵈ q :=
  .core h

/-- Core star trace embeds into derived star trace. -/
noncomputable def ReducesStar.toDerived {p q : Pattern} (h : p ⇝* q) : p ⇝ᵈ* q := by
  induction h with
  | refl p => exact .refl p
  | step h hs ih => exact .step (.core h) ih

/-- A derived trace is core-compatible when every step came from `core`. -/
inductive CoreCompatible : {p q : Pattern} → (p ⇝ᵈ* q) → Type where
  | refl (p : Pattern) : CoreCompatible (.refl p)
  | step {p q r : Pattern} (h : p ⇝ q) (hs : q ⇝ᵈ* r) :
      CoreCompatible hs →
      CoreCompatible (.step (.core h) hs)

/-- The derived trace produced from a core star trace is core-compatible. -/
noncomputable def ReducesStar.toDerivedCoreCompatible {p q : Pattern} (h : p ⇝* q) :
    CoreCompatible (ReducesStar.toDerived h) := by
  induction h with
  | refl p =>
      simpa [ReducesStar.toDerived] using (CoreCompatible.refl p)
  | step h hs ih =>
      simpa [ReducesStar.toDerived] using (CoreCompatible.step h _ ih)

/-- Transport a core-compatible derived trace back to canonical core star. -/
noncomputable def CoreCompatible.toCore {p q : Pattern} {hs : p ⇝ᵈ* q}
    (hcc : CoreCompatible hs) : p ⇝* q := by
  induction hcc with
  | refl p => exact .refl p
  | step h hs hcc ih => exact .step h ih

/-! ## One-Step Conservativity on Core-Canonical Sources -/

/-- Detect whether a pattern uses derived administrative heads (`PReplicate`/`PNu`). -/
def hasDerivedHead : Pattern → Bool
  | .bvar _ => false
  | .fvar _ => false
  | .apply "PReplicate" _ => true
  | .apply "PNu" _ => true
  | .apply _ args => (args.map hasDerivedHead).any (fun b => b)
  | .lambda _nm body => hasDerivedHead body
  | .multiLambda _ _nms body => hasDerivedHead body
  | .subst body repl => hasDerivedHead body || hasDerivedHead repl
  | .collection _ elems _ => (elems.map hasDerivedHead).any (fun b => b)

/-- Core-canonical terms have no derived administrative heads. -/
def CoreCanonical (p : Pattern) : Prop := hasDerivedHead p = false

/-- Core-canonical collections have only core-canonical elements. -/
theorem coreCanonical_elem_of_collection {ct : CollType} {elems : List Pattern} {e : Pattern}
    (hc : CoreCanonical (.collection ct elems none)) (he : e ∈ elems) :
    CoreCanonical e := by
  unfold CoreCanonical at hc ⊢
  cases hbe : hasDerivedHead e with
  | false =>
      simp
  | true =>
      have hmemMap : hasDerivedHead e ∈ elems.map hasDerivedHead :=
        List.mem_map_of_mem he
      have hmemTrue : true ∈ elems.map hasDerivedHead := by
        simpa [hbe] using hmemMap
      have hanyTrue : (elems.map hasDerivedHead).any (fun b => b) = true := by
        exact List.any_eq_true.mpr ⟨true, hmemTrue, rfl⟩
      have hanyFalse : (elems.map hasDerivedHead).any (fun b => b) = false := by
        simpa [hasDerivedHead] using hc
      have : False := by
        simp [hanyFalse] at hanyTrue
      exact False.elim this

/-- If every element has no derived head, mapped-any is false. -/
theorem hasDerivedHead_any_false_of_forall_false {elems : List Pattern}
    (hall : ∀ e ∈ elems, hasDerivedHead e = false) :
    (elems.map hasDerivedHead).any (fun b => b) = false := by
  induction elems with
  | nil =>
      rfl
  | cons a as ih =>
      have ha : hasDerivedHead a = false := hall a (by simp)
      have htail : ∀ e ∈ as, hasDerivedHead e = false := by
        intro e he
        exact hall e (by simp [he])
      simp [ha, ih htail]

private theorem hasDerivedHead_any_of_pointwise_eq {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (hEq : ∀ i h₁ h₂, hasDerivedHead (ps.get ⟨i, h₁⟩) = hasDerivedHead (qs.get ⟨i, h₂⟩)) :
    (ps.map hasDerivedHead).any (fun b => b) = (qs.map hasDerivedHead).any (fun b => b) := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil => rfl
      | cons _ _ => cases hlen
  | cons p ps ih =>
      cases qs with
      | nil => cases hlen
      | cons q qs =>
          have hpq : hasDerivedHead p = hasDerivedHead q := by
            exact hEq 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have hlen' : ps.length = qs.length := Nat.succ.inj hlen
          have hEq' : ∀ i h₁ h₂,
              hasDerivedHead (ps.get ⟨i, h₁⟩) = hasDerivedHead (qs.get ⟨i, h₂⟩) := by
            intro i h₁ h₂
            simpa using hEq (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          simp [hpq, ih hlen' hEq']

/-- Structural congruence preserves derived-head detection. -/
theorem hasDerivedHead_SC {p q : Pattern}
    (hsc : Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence p q) :
    hasDerivedHead p = hasDerivedHead q := by
  induction hsc with
  | alpha _ _ h =>
      subst h
      rfl
  | refl _ =>
      rfl
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | par_singleton p =>
      simp [hasDerivedHead]
  | par_nil_left p =>
      simp [hasDerivedHead]
  | par_nil_right p =>
      simp [hasDerivedHead]
  | par_empty =>
      simp [hasDerivedHead]
  | par_comm p q =>
      simp [hasDerivedHead, Bool.or_comm]
  | par_assoc p q r =>
      simp [hasDerivedHead, Bool.or_assoc]
  | par_cong ps qs hlen _ ih =>
      simpa [hasDerivedHead] using hasDerivedHead_any_of_pointwise_eq hlen ih
  | par_flatten ps qs =>
      simp [hasDerivedHead, List.any_append]
  | par_perm elems₁ elems₂ hperm =>
      have hpermMap :
          (elems₁.map hasDerivedHead).Perm (elems₂.map hasDerivedHead) := hperm.map hasDerivedHead
      simpa [hasDerivedHead] using hpermMap.any_eq
  | set_perm elems₁ elems₂ hperm =>
      have hpermMap :
          (elems₁.map hasDerivedHead).Perm (elems₂.map hasDerivedHead) := hperm.map hasDerivedHead
      simpa [hasDerivedHead] using hpermMap.any_eq
  | set_cong elems₁ elems₂ hlen _ ih =>
      simpa [hasDerivedHead] using hasDerivedHead_any_of_pointwise_eq hlen ih
  | lambda_cong _ _ _ _ ih =>
      simpa [hasDerivedHead] using ih
  | apply_cong f args₁ args₂ hlen _ ih =>
      by_cases hrep : f = "PReplicate"
      · simp [hasDerivedHead, hrep]
      by_cases hnu : f = "PNu"
      · simp [hasDerivedHead, hnu]
      · have hargs := hasDerivedHead_any_of_pointwise_eq hlen ih
        simpa [hasDerivedHead, hrep, hnu] using hargs
  | collection_general_cong _ elems₁ elems₂ _ hlen _ ih =>
      simpa [hasDerivedHead] using hasDerivedHead_any_of_pointwise_eq hlen ih
  | multiLambda_cong _ _ _ _ _ ih =>
      simpa [hasDerivedHead] using ih
  | subst_cong _ _ _ _ _ _ ih₁ ih₂ =>
      simp [hasDerivedHead, ih₁, ih₂]
  | quote_drop n =>
      simp [hasDerivedHead]

/-- Structural congruence preserves core-canonical shape. -/
theorem coreCanonical_of_SC {p q : Pattern}
    (hc : CoreCanonical p)
    (hsc : Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence p q) :
    CoreCanonical q := by
  unfold CoreCanonical at hc ⊢
  simpa [hasDerivedHead_SC hsc] using hc

private theorem hasDerivedHead_map_openBVar_any_false {k : Nat} {u : Pattern} {ps : List Pattern}
    (hall : (ps.map hasDerivedHead).any (fun b => b) = false)
    (ih : ∀ q ∈ ps, ∀ k, hasDerivedHead q = false →
      hasDerivedHead (Mettapedia.OSLF.MeTTaIL.Substitution.openBVar k u q) = false) :
    ((ps.map (Mettapedia.OSLF.MeTTaIL.Substitution.openBVar k u)).map hasDerivedHead).any
      (fun b => b) = false := by
  apply hasDerivedHead_any_false_of_forall_false
  intro p hp
  rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  exact ih q hq k (coreCanonical_elem_of_collection (ct := .hashBag)
    (elems := ps) (by simpa [CoreCanonical, hasDerivedHead] using hall) hq)

/-- Opening with a core-canonical replacement preserves no-derived-head shape. -/
theorem hasDerivedHead_openBVar_false {k : Nat} {u p : Pattern}
    (hp : hasDerivedHead p = false) (hu : hasDerivedHead u = false) :
    hasDerivedHead (Mettapedia.OSLF.MeTTaIL.Substitution.openBVar k u p) = false := by
  suffices h : ∀ (p : Pattern) (k : Nat), hasDerivedHead p = false →
      hasDerivedHead (Mettapedia.OSLF.MeTTaIL.Substitution.openBVar k u p) = false from h p k hp
  intro p
  induction p using Pattern.inductionOn with
  | hbvar n =>
      intro k hp'
      unfold Mettapedia.OSLF.MeTTaIL.Substitution.openBVar
      split
      · exact hu
      · simp [hasDerivedHead]
  | hfvar x =>
      intro _ hp'
      simp [Mettapedia.OSLF.MeTTaIL.Substitution.openBVar, hasDerivedHead]
  | happly c args ih =>
      intro k hp'
      by_cases hrep : c = "PReplicate"
      · subst hrep
        simp [hasDerivedHead] at hp'
      by_cases hnu : c = "PNu"
      · subst hnu
        simp [hasDerivedHead] at hp'
      · have hargs :
            (args.map hasDerivedHead).any (fun b => b) = false := by
          simpa [hasDerivedHead, hrep, hnu] using hp'
        have hargsOpen :
            ((args.map (Mettapedia.OSLF.MeTTaIL.Substitution.openBVar k u)).map hasDerivedHead).any
              (fun b => b) = false :=
          hasDerivedHead_map_openBVar_any_false hargs ih
        simpa [Mettapedia.OSLF.MeTTaIL.Substitution.openBVar, hasDerivedHead, hrep, hnu] using
          hargsOpen
  | hlambda _ body ih =>
      intro k hp'
      have hbody : hasDerivedHead body = false := by
        simpa [hasDerivedHead] using hp'
      have hopen :
          hasDerivedHead (Mettapedia.OSLF.MeTTaIL.Substitution.openBVar (k + 1) u body) = false :=
        ih (k + 1) hbody
      simpa [Mettapedia.OSLF.MeTTaIL.Substitution.openBVar, hasDerivedHead] using hopen
  | hmultiLambda n _ body ih =>
      intro k hp'
      have hbody : hasDerivedHead body = false := by
        simpa [hasDerivedHead] using hp'
      have hopen :
          hasDerivedHead (Mettapedia.OSLF.MeTTaIL.Substitution.openBVar (k + n) u body) = false :=
        ih (k + n) hbody
      simpa [Mettapedia.OSLF.MeTTaIL.Substitution.openBVar, hasDerivedHead] using hopen
  | hsubst body repl ihBody ihRepl =>
      intro k hp'
      have hbodyRepl :
          hasDerivedHead body = false ∧ hasDerivedHead repl = false :=
        by
          simpa [hasDerivedHead, Bool.or_eq_false_iff] using hp'
      have hbody :
          hasDerivedHead (Mettapedia.OSLF.MeTTaIL.Substitution.openBVar (k + 1) u body) = false :=
        ihBody (k + 1) hbodyRepl.1
      have hrepl :
          hasDerivedHead (Mettapedia.OSLF.MeTTaIL.Substitution.openBVar k u repl) = false :=
        ihRepl k hbodyRepl.2
      simp [Mettapedia.OSLF.MeTTaIL.Substitution.openBVar, hasDerivedHead, hbody, hrepl]
  | hcollection ct elems rest ih =>
      intro k hp'
      have helems :
          (elems.map hasDerivedHead).any (fun b => b) = false := by
        simpa [hasDerivedHead] using hp'
      have hopenElems :
          ((elems.map (Mettapedia.OSLF.MeTTaIL.Substitution.openBVar k u)).map hasDerivedHead).any
            (fun b => b) = false :=
        hasDerivedHead_map_openBVar_any_false helems ih
      simpa [Mettapedia.OSLF.MeTTaIL.Substitution.openBVar, hasDerivedHead] using hopenElems

/-- COMM substitution preserves no-derived-head shape on canonical inputs. -/
theorem hasDerivedHead_commSubst_false {p q : Pattern}
    (hp : hasDerivedHead p = false) (hq : hasDerivedHead q = false) :
    hasDerivedHead (Mettapedia.OSLF.MeTTaIL.Substitution.commSubst p q) = false := by
  rw [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst_def]
  have hquote : hasDerivedHead (.apply "NQuote" [q]) = false := by
    simp [hasDerivedHead, hq]
  exact hasDerivedHead_openBVar_false hp hquote

mutual
  private theorem hasDerivedHead_semanticNormalizeName_false :
      ∀ {p : Pattern}, hasDerivedHead p = false →
        hasDerivedHead (semanticNormalizeName p) = false
    | .bvar _, hp => by
        simp [semanticNormalizeName, hasDerivedHead]
    | .fvar _, hp => by
        simp [semanticNormalizeName, hasDerivedHead]
    | .apply "NQuote" [.apply "PDrop" [n]], hp => by
        have hn : hasDerivedHead n = false := by
          simpa [hasDerivedHead, Bool.or_eq_false_iff] using hp
        simpa [semanticNormalizeName] using hasDerivedHead_semanticNormalizeName_false hn
    | .apply "NQuote" [p], hp => by
        by_cases hdropq : ∃ n, p = .apply "PDrop" [n]
        · rcases hdropq with ⟨n, rfl⟩
          have hn : hasDerivedHead n = false := by
            simpa [hasDerivedHead, Bool.or_eq_false_iff] using hp
          simpa [semanticNormalizeName.eq_3] using hasDerivedHead_semanticNormalizeName_false hn
        · have hp' : hasDerivedHead p = false := by
            simpa [hasDerivedHead] using hp
          have hnorm : hasDerivedHead (semanticNormalizeProc p) = false :=
            hasDerivedHead_semanticNormalizeProc_false hp'
          have hpnot : ∀ n, p = .apply "PDrop" [n] → False := by
            intro n hpdrop
            exact hdropq ⟨n, hpdrop⟩
          rw [semanticNormalizeName.eq_4 p hpnot]
          simpa [hasDerivedHead] using hnorm
    | .apply c args, hp => by
        by_cases hqd : c = "NQuote" ∧ ∃ n, args = [.apply "PDrop" [n]]
        · rcases hqd with ⟨rfl, n, rfl⟩
          have hn : hasDerivedHead n = false := by
            simpa [hasDerivedHead, Bool.or_eq_false_iff] using hp
          simpa [semanticNormalizeName] using hasDerivedHead_semanticNormalizeName_false hn
        · by_cases hq : c = "NQuote" ∧ ∃ p', args = [p']
          · rcases hq with ⟨rfl, p', rfl⟩
            have hp' : hasDerivedHead p' = false := by
              simpa [hasDerivedHead] using hp
            have hnorm : hasDerivedHead (semanticNormalizeProc p') = false :=
              hasDerivedHead_semanticNormalizeProc_false hp'
            have hpnot : ∀ n, p' = .apply "PDrop" [n] → False := by
              intro n hpdrop
              exact hqd ⟨rfl, ⟨n, by simp [hpdrop]⟩⟩
            rw [semanticNormalizeName.eq_4 p' hpnot]
            simpa [hasDerivedHead] using hnorm
          · rw [semanticNormalizeName.eq_5 (.apply c args)
                (by intro n h; cases h)
                (by intro x h; cases h)
                (by
                  intro n hEq
                  injection hEq with hc hargs
                  exact hqd ⟨hc, ⟨n, hargs⟩⟩)
                (by
                  intro p' hEq
                  injection hEq with hc hargs
                  exact hq ⟨hc, ⟨p', hargs⟩⟩)]
            exact hp
    | .lambda _ body, hp => by
        simpa [semanticNormalizeName] using hp
    | .multiLambda _ _ body, hp => by
        simpa [semanticNormalizeName] using hp
    | .subst body repl, hp => by
        simpa [semanticNormalizeName] using hp
    | .collection ct elems rest, hp => by
        simpa [semanticNormalizeName] using hp

  private theorem hasDerivedHead_semanticNormalizeProc_false :
      ∀ {p : Pattern}, hasDerivedHead p = false →
        hasDerivedHead (semanticNormalizeProc p) = false
    | .bvar _, hp => by
        simp [semanticNormalizeProc, hasDerivedHead]
    | .fvar _, hp => by
        simp [semanticNormalizeProc, hasDerivedHead]
    | .apply "POutput" [n, q], hp => by
        have hparts : hasDerivedHead n = false ∧ hasDerivedHead q = false := by
          simpa [hasDerivedHead, Bool.or_eq_false_iff] using hp
        simp [semanticNormalizeProc, hasDerivedHead,
          hasDerivedHead_semanticNormalizeName_false hparts.1,
          hasDerivedHead_semanticNormalizeProc_false hparts.2]
    | .apply "PInput" [n, .lambda none body], hp => by
        have hparts : hasDerivedHead n = false ∧ hasDerivedHead (.lambda none body) = false := by
          simpa [hasDerivedHead, Bool.or_eq_false_iff] using hp
        have hbody : hasDerivedHead body = false := by
          simpa [hasDerivedHead] using hparts.2
        simp [semanticNormalizeProc, hasDerivedHead,
          hasDerivedHead_semanticNormalizeName_false hparts.1,
          hasDerivedHead_semanticNormalizeProc_false hbody]
    | .apply "PDrop" [n], hp => by
        have hn : hasDerivedHead n = false := by
          simpa [hasDerivedHead] using hp
        simp [semanticNormalizeProc, hasDerivedHead,
          hasDerivedHead_semanticNormalizeName_false hn]
    | .apply "NQuote" [p], hp => by
        have hp' : hasDerivedHead p = false := by
          simpa [hasDerivedHead] using hp
        simp [semanticNormalizeProc, hasDerivedHead,
          hasDerivedHead_semanticNormalizeProc_false hp']
    | .apply c args, hp => by
        by_cases hout : c = "POutput" ∧ ∃ n q, args = [n, q]
        · rcases hout with ⟨rfl, n, q, rfl⟩
          have hparts : hasDerivedHead n = false ∧ hasDerivedHead q = false := by
            simpa [hasDerivedHead, Bool.or_eq_false_iff] using hp
          simp [semanticNormalizeProc, hasDerivedHead,
            hasDerivedHead_semanticNormalizeName_false hparts.1,
            hasDerivedHead_semanticNormalizeProc_false hparts.2]
        · by_cases hin : c = "PInput" ∧ ∃ n body, args = [n, .lambda none body]
          · rcases hin with ⟨rfl, n, body, rfl⟩
            have hparts : hasDerivedHead n = false ∧ hasDerivedHead (.lambda none body) = false := by
              simpa [hasDerivedHead, Bool.or_eq_false_iff] using hp
            have hbody : hasDerivedHead body = false := by
              simpa [hasDerivedHead] using hparts.2
            simp [semanticNormalizeProc, hasDerivedHead,
              hasDerivedHead_semanticNormalizeName_false hparts.1,
              hasDerivedHead_semanticNormalizeProc_false hbody]
          · by_cases hdrop : c = "PDrop" ∧ ∃ n, args = [n]
            · rcases hdrop with ⟨rfl, n, rfl⟩
              have hn : hasDerivedHead n = false := by
                simpa [hasDerivedHead] using hp
              simp [semanticNormalizeProc, hasDerivedHead,
                hasDerivedHead_semanticNormalizeName_false hn]
            · by_cases hquote : c = "NQuote" ∧ ∃ p', args = [p']
              · rcases hquote with ⟨rfl, p', rfl⟩
                have hp' : hasDerivedHead p' = false := by
                  simpa [hasDerivedHead] using hp
                have hnorm : hasDerivedHead (semanticNormalizeProc p') = false :=
                  hasDerivedHead_semanticNormalizeProc_false hp'
                rw [semanticNormalizeProc.eq_6]
                simpa [hasDerivedHead] using hnorm
              · rw [semanticNormalizeProc.eq_11 (.apply c args)
                    (by intro n h; cases h)
                    (by intro x h; cases h)
                    (by
                      intro n q hEq
                      injection hEq with hc hargs
                      exact hout ⟨hc, ⟨n, q, hargs⟩⟩)
                    (by
                      intro n body hEq
                      injection hEq with hc hargs
                      exact hin ⟨hc, ⟨n, body, hargs⟩⟩)
                    (by
                      intro n hEq
                      injection hEq with hc hargs
                      exact hdrop ⟨hc, ⟨n, hargs⟩⟩)
                    (by
                      intro p' hEq
                      injection hEq with hc hargs
                      exact hquote ⟨hc, ⟨p', hargs⟩⟩)
                    (by intro nm body h; cases h)
                    (by intro n nms body h; cases h)
                    (by intro body repl h; cases h)
                    (by intro ct elems rest h; cases h)]
                exact hp
    | .lambda _ body, hp => by
        have hbody : hasDerivedHead body = false := by
          simpa [hasDerivedHead] using hp
        simpa [semanticNormalizeProc, hasDerivedHead] using
          hasDerivedHead_semanticNormalizeProc_false hbody
    | .multiLambda _ _ body, hp => by
        have hbody : hasDerivedHead body = false := by
          simpa [hasDerivedHead] using hp
        simpa [semanticNormalizeProc, hasDerivedHead] using
          hasDerivedHead_semanticNormalizeProc_false hbody
    | .subst body repl, hp => by
        have hparts : hasDerivedHead body = false ∧ hasDerivedHead repl = false := by
          simpa [hasDerivedHead, Bool.or_eq_false_iff] using hp
        simp [semanticNormalizeProc, hasDerivedHead,
          hasDerivedHead_semanticNormalizeProc_false hparts.1,
          hasDerivedHead_semanticNormalizeProc_false hparts.2]
    | .collection ct elems rest, hp => by
        have hall : ∀ e ∈ elems, hasDerivedHead e = false := by
          intro e he
          exact coreCanonical_elem_of_collection (ct := ct) (elems := elems)
            (by simpa [CoreCanonical, hasDerivedHead] using hp) he
        simpa [semanticNormalizeProc, hasDerivedHead] using
          hasDerivedHead_semanticNormalizeProcList_false hall

  private theorem hasDerivedHead_semanticNormalizeProcList_false :
      ∀ {elems : List Pattern},
        (∀ e ∈ elems, hasDerivedHead e = false) →
          ((semanticNormalizeProcList elems).map hasDerivedHead).any (fun b => b) = false
    | [], _ => by
        simp [semanticNormalizeProcList]
    | e :: es, hall => by
        have he : hasDerivedHead e = false := hall e (by simp)
        have htail : ∀ e' ∈ es, hasDerivedHead e' = false := by
          intro e' he'
          exact hall e' (by simp [he'])
        simp [semanticNormalizeProcList,
          hasDerivedHead_semanticNormalizeProc_false he,
          hasDerivedHead_semanticNormalizeProcList_false htail]
end

private theorem hasDerivedHead_semanticSubstName_false
    {k : Nat} {replacementName name : Pattern}
    (hrepl : hasDerivedHead replacementName = false)
    (hname : hasDerivedHead name = false) :
    hasDerivedHead (semanticSubstName k replacementName name) = false := by
  unfold semanticSubstName semanticSubstNameMark
  have hnorm : hasDerivedHead (semanticNormalizeName name) = false :=
    hasDerivedHead_semanticNormalizeName_false hname
  cases hnm : semanticNormalizeName name with
  | bvar n =>
      by_cases hnk : n = k
      · simp [hnk, hrepl]
      · simp [hnk, hasDerivedHead]
  | fvar x =>
      simpa [hnm] using hnorm
  | apply c args =>
      simpa [hnm] using hnorm
  | lambda nm body =>
      simpa [hnm] using hnorm
  | multiLambda n nms body =>
      simpa [hnm] using hnorm
  | subst body repl =>
      simpa [hnm] using hnorm
  | collection ct elems rest =>
      simpa [hnm] using hnorm

mutual
  private theorem hasDerivedHead_semanticSubstProc_false
      {replacementName : Pattern}
      (hrepl : hasDerivedHead replacementName = false) :
      ∀ {p : Pattern} {k : Nat}, hasDerivedHead p = false →
        hasDerivedHead (semanticSubstProc k replacementName p) = false
    | .bvar n, k, hp => by
        by_cases hnk : n = k
        · simp [semanticSubstProc, hnk, hrepl]
        · simp [semanticSubstProc, hnk, hasDerivedHead]
    | .fvar _, _, hp => by
        simp [semanticSubstProc, hasDerivedHead]
    | .apply "NQuote" [p], _, hp => by
        have hp' : hasDerivedHead p = false := by
          simpa [hasDerivedHead] using hp
        simp [semanticSubstProc, hasDerivedHead, hp']
    | .apply "PDrop" [name], k, hp => by
        have hname : hasDerivedHead name = false := by
          simpa [hasDerivedHead] using hp
        have hsubstName :
            hasDerivedHead (semanticSubstName k replacementName name) = false :=
          hasDerivedHead_semanticSubstName_false hrepl hname
        unfold semanticSubstProc
        cases hnm : semanticSubstNameMark k replacementName name with
        | mk name' matched =>
            have hname' : hasDerivedHead name' = false := by
              simpa [semanticSubstName, hnm] using hsubstName
            cases matched with
            | false =>
                simp [hnm, hasDerivedHead, hname']
            | true =>
                cases name' with
                | apply c args =>
                    by_cases hquote : c = "NQuote" ∧ ∃ p', args = [p']
                    · rcases hquote with ⟨rfl, p', rfl⟩
                      have hp' : hasDerivedHead p' = false := by
                        simpa [hasDerivedHead] using hname'
                      simp [hnm, hp']
                    · have hdrop' : hasDerivedHead (.apply "PDrop" [Pattern.apply c args]) = false := by
                        simpa [hasDerivedHead] using hname'
                      have hne : ∀ p', Pattern.apply c args ≠ Pattern.apply "NQuote" [p'] := by
                        intro p' hEq
                        injection hEq with hc hargs
                        exact hquote ⟨hc, ⟨p', hargs⟩⟩
                      have hmatch :
                          (match Pattern.apply c args, true with
                           | Pattern.apply "NQuote" [p], true => p
                           | x, x_1 => Pattern.apply "PDrop" [Pattern.apply c args]) =
                            .apply "PDrop" [Pattern.apply c args] := by
                        simp [hne]
                      have hgoal :
                          hasDerivedHead
                              (match Pattern.apply c args, true with
                               | Pattern.apply "NQuote" [p], true => p
                               | x, x_1 => Pattern.apply "PDrop" [Pattern.apply c args]) = false := by
                        rw [hmatch]
                        exact hdrop'
                      simpa [hnm] using! hgoal
                | _ =>
                    simp [hnm, hasDerivedHead, hname']
    | .apply "POutput" [n, q], k, hp => by
        have hparts : hasDerivedHead n = false ∧ hasDerivedHead q = false := by
          simpa [hasDerivedHead, Bool.or_eq_false_iff] using hp
        simp [semanticSubstProc, hasDerivedHead,
          hasDerivedHead_semanticSubstName_false (k := k) hrepl hparts.1,
          hasDerivedHead_semanticSubstProc_false hrepl hparts.2]
    | .apply "PInput" [n, .lambda none body], k, hp => by
        have hparts : hasDerivedHead n = false ∧ hasDerivedHead (.lambda none body) = false := by
          simpa [hasDerivedHead, Bool.or_eq_false_iff] using hp
        have hbody : hasDerivedHead body = false := by
          simpa [hasDerivedHead] using hparts.2
        simp [semanticSubstProc, hasDerivedHead,
          hasDerivedHead_semanticSubstName_false (k := k) hrepl hparts.1,
          hasDerivedHead_semanticSubstProc_false hrepl (k := k + 1) hbody]
    | .apply c args, k, hp => by
        by_cases hquote : c = "NQuote" ∧ ∃ p', args = [p']
        · rcases hquote with ⟨rfl, p', rfl⟩
          have hp' : hasDerivedHead p' = false := by
            simpa [hasDerivedHead] using hp
          simp [semanticSubstProc, hasDerivedHead, hp']
        · by_cases hdrop : c = "PDrop" ∧ ∃ name, args = [name]
          · rcases hdrop with ⟨rfl, name, rfl⟩
            have hname : hasDerivedHead name = false := by
              simpa [hasDerivedHead] using hp
            have hsubstName :
                hasDerivedHead (semanticSubstName k replacementName name) = false :=
              hasDerivedHead_semanticSubstName_false (k := k) hrepl hname
            unfold semanticSubstProc
            cases hnm : semanticSubstNameMark k replacementName name with
            | mk name' matched =>
                have hname' : hasDerivedHead name' = false := by
                  simpa [semanticSubstName, hnm] using hsubstName
                cases matched with
                | false =>
                    simp [hnm, hasDerivedHead, hname']
                | true =>
                    cases name' with
                    | apply c' args' =>
                        by_cases hq' : c' = "NQuote" ∧ ∃ p', args' = [p']
                        · rcases hq' with ⟨rfl, p', rfl⟩
                          have hp'' : hasDerivedHead p' = false := by
                            simpa [hasDerivedHead] using hname'
                          simp [hnm, hp'']
                        · have hdrop' : hasDerivedHead (.apply "PDrop" [Pattern.apply c' args']) = false := by
                            simpa [hasDerivedHead] using hname'
                          have hne : ∀ p', Pattern.apply c' args' ≠ Pattern.apply "NQuote" [p'] := by
                            intro p' hEq
                            injection hEq with hc hargs
                            exact hq' ⟨hc, ⟨p', hargs⟩⟩
                          have hmatch :
                              (match Pattern.apply c' args', true with
                               | Pattern.apply "NQuote" [p], true => p
                               | x, x_1 => Pattern.apply "PDrop" [Pattern.apply c' args']) =
                                .apply "PDrop" [Pattern.apply c' args'] := by
                            simp [hne]
                          have hgoal :
                              hasDerivedHead
                                  (match Pattern.apply c' args', true with
                                   | Pattern.apply "NQuote" [p], true => p
                                   | x, x_1 => Pattern.apply "PDrop" [Pattern.apply c' args']) = false := by
                            rw [hmatch]
                            exact hdrop'
                          simpa [hnm] using! hgoal
                    | _ =>
                        simp [hnm, hasDerivedHead, hname']
          · by_cases hout : c = "POutput" ∧ ∃ n q', args = [n, q']
            · rcases hout with ⟨rfl, n, q', rfl⟩
              have hparts : hasDerivedHead n = false ∧ hasDerivedHead q' = false := by
                simpa [hasDerivedHead, Bool.or_eq_false_iff] using hp
              simp [semanticSubstProc, hasDerivedHead,
                hasDerivedHead_semanticSubstName_false (k := k) hrepl hparts.1,
                hasDerivedHead_semanticSubstProc_false hrepl (k := k) hparts.2]
            · by_cases hin : c = "PInput" ∧ ∃ n body, args = [n, .lambda none body]
              · rcases hin with ⟨rfl, n, body, rfl⟩
                have hparts : hasDerivedHead n = false ∧ hasDerivedHead (.lambda none body) = false := by
                  simpa [hasDerivedHead, Bool.or_eq_false_iff] using hp
                have hbody : hasDerivedHead body = false := by
                  simpa [hasDerivedHead] using hparts.2
                simp [semanticSubstProc, hasDerivedHead,
                  hasDerivedHead_semanticSubstName_false (k := k) hrepl hparts.1,
                  hasDerivedHead_semanticSubstProc_false hrepl (k := k + 1) hbody]
              · rw [semanticSubstProc.eq_11 (k := k) (replacementName := replacementName) (.apply c args)
                    (by intro n h; cases h)
                    (by intro x h; cases h)
                    (by
                      intro p' hEq
                      injection hEq with hc hargs
                      exact hquote ⟨hc, ⟨p', hargs⟩⟩)
                    (by
                      intro name hEq
                      injection hEq with hc hargs
                      exact hdrop ⟨hc, ⟨name, hargs⟩⟩)
                    (by
                      intro n q' hEq
                      injection hEq with hc hargs
                      exact hout ⟨hc, ⟨n, q', hargs⟩⟩)
                    (by
                      intro n body hEq
                      injection hEq with hc hargs
                      exact hin ⟨hc, ⟨n, body, hargs⟩⟩)
                    (by intro nm body h; cases h)
                    (by intro n nms body h; cases h)
                    (by intro body repl h; cases h)
                    (by intro ct elems rest h; cases h)]
                exact hp
    | .lambda _ body, k, hp => by
        have hbody : hasDerivedHead body = false := by
          simpa [hasDerivedHead] using hp
        simpa [semanticSubstProc, hasDerivedHead] using
          hasDerivedHead_semanticSubstProc_false hrepl (k := k + 1) hbody
    | .multiLambda n nms body, k, hp => by
        have hbody : hasDerivedHead body = false := by
          simpa [hasDerivedHead] using hp
        simpa [semanticSubstProc, hasDerivedHead] using
          hasDerivedHead_semanticSubstProc_false hrepl (k := k + n) hbody
    | .subst body repl, k, hp => by
        have hparts : hasDerivedHead body = false ∧ hasDerivedHead repl = false := by
          simpa [hasDerivedHead, Bool.or_eq_false_iff] using hp
        simp [semanticSubstProc, hasDerivedHead,
          hasDerivedHead_semanticSubstProc_false hrepl (k := k + 1) hparts.1,
          hasDerivedHead_semanticSubstProc_false hrepl (k := k) hparts.2]
    | .collection ct elems rest, k, hp => by
        have hall : ∀ e ∈ elems, hasDerivedHead e = false := by
          intro e he
          exact coreCanonical_elem_of_collection (ct := ct) (elems := elems)
            (by simpa [CoreCanonical, hasDerivedHead] using hp) he
        simpa [semanticSubstProc, hasDerivedHead] using
          hasDerivedHead_semanticSubstProcList_false hrepl (k := k) hall

  private theorem hasDerivedHead_semanticSubstProcList_false
      {replacementName : Pattern}
      (hrepl : hasDerivedHead replacementName = false) :
      ∀ {elems : List Pattern} {k : Nat},
        (∀ e ∈ elems, hasDerivedHead e = false) →
          ((semanticSubstProcList k replacementName elems).map hasDerivedHead).any (fun b => b) = false
    | [], _, _ => by
        simp [semanticSubstProcList]
    | e :: es, k, hall => by
        have he : hasDerivedHead e = false := hall e (by simp)
        have htail : ∀ e' ∈ es, hasDerivedHead e' = false := by
          intro e' he'
          exact hall e' (by simp [he'])
        simp [semanticSubstProcList,
          hasDerivedHead_semanticSubstProc_false hrepl (k := k) he,
          hasDerivedHead_semanticSubstProcList_false hrepl (k := k) htail]
end

/-- Semantic COMM substitution preserves no-derived-head shape on canonical inputs. -/
theorem hasDerivedHead_semanticCommSubst_false {p q : Pattern}
    (hp : hasDerivedHead p = false) (hq : hasDerivedHead q = false) :
    hasDerivedHead (semanticCommSubst p q) = false := by
  have hnormQ : hasDerivedHead (semanticNormalizeProc q) = false :=
    hasDerivedHead_semanticNormalizeProc_false hq
  have hrepl : hasDerivedHead (.apply "NQuote" [semanticNormalizeProc q]) = false := by
    simp [hasDerivedHead, hnormQ]
  simpa [semanticCommSubst] using
    hasDerivedHead_semanticSubstProc_false hrepl (k := 0) hp

/-- Conservativity (one-step): derived steps from core-canonical sources are core steps. -/
noncomputable def ReducesDerived.toCore_of_coreCanonical {p q : Pattern}
    (hc : CoreCanonical p) (h : p ⇝ᵈ q) : p ⇝ q := by
  revert hc
  induction h with
  | core hcore =>
      intro _
      exact hcore
  | rep_unfold =>
      intro hc
      simp [CoreCanonical, hasDerivedHead] at hc
  | @par p q rest hstep ih =>
      intro hc
      have hp : CoreCanonical p :=
        coreCanonical_elem_of_collection (ct := .hashBag) (elems := p :: rest) hc (by simp)
      exact Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.par (ih hp)
  | @par_any p q before after hstep ih =>
      intro hc
      have hp : CoreCanonical p :=
        coreCanonical_elem_of_collection
          (ct := .hashBag) (elems := before ++ [p] ++ after) hc (by simp)
      exact
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.par_any
          (before := before) (after := after) (ih hp)
  | @par_set p q rest hstep ih =>
      intro hc
      have hp : CoreCanonical p :=
        coreCanonical_elem_of_collection (ct := .hashSet) (elems := p :: rest) hc (by simp)
      exact Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.par_set (ih hp)
  | @par_set_any p q before after hstep ih =>
      intro hc
      have hp : CoreCanonical p :=
        coreCanonical_elem_of_collection
          (ct := .hashSet) (elems := before ++ [p] ++ after) hc (by simp)
      exact
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.par_set_any
          (before := before) (after := after) (ih hp)

/-- Core one-step reduction preserves core-canonical shape. -/
theorem coreCanonical_of_core_step {p q : Pattern}
    (hc : CoreCanonical p) (h : p ⇝ q) : CoreCanonical q := by
  induction h with
  | @comm n q p rest =>
      have hOut : CoreCanonical (.apply "POutput" [n, q]) :=
        coreCanonical_elem_of_collection
          (ct := .hashBag)
          (elems := [.apply "POutput" [n, q], .apply "PInput" [n, .lambda none p]] ++ rest)
          hc (by simp)
      have hIn : CoreCanonical (.apply "PInput" [n, .lambda none p]) :=
        coreCanonical_elem_of_collection
          (ct := .hashBag)
          (elems := [.apply "POutput" [n, q], .apply "PInput" [n, .lambda none p]] ++ rest)
          hc (by simp)
      have hq : hasDerivedHead q = false := by
        have hOut' : hasDerivedHead (.apply "POutput" [n, q]) = false := hOut
        have hParts : hasDerivedHead n = false ∧ hasDerivedHead q = false := by
          simpa [hasDerivedHead, Bool.or_eq_false_iff] using hOut'
        exact hParts.2
      have hpBody : hasDerivedHead p = false := by
        have hIn' : hasDerivedHead (.apply "PInput" [n, .lambda none p]) = false := hIn
        have hParts : hasDerivedHead n = false ∧ hasDerivedHead (.lambda none p) = false := by
          simpa [hasDerivedHead, Bool.or_eq_false_iff] using hIn'
        simpa [hasDerivedHead] using hParts.2
      have hrestAll : ∀ e ∈ rest, hasDerivedHead e = false := by
        intro e he
        exact coreCanonical_elem_of_collection
          (ct := .hashBag)
          (elems := [.apply "POutput" [n, q], .apply "PInput" [n, .lambda none p]] ++ rest)
          hc (by simp [he])
      have hrestAny : (rest.map hasDerivedHead).any (fun b => b) = false :=
        hasDerivedHead_any_false_of_forall_false hrestAll
      have hComm : hasDerivedHead (semanticCommSubst p q) = false :=
        hasDerivedHead_semanticCommSubst_false hpBody hq
      unfold CoreCanonical
      simp [hasDerivedHead, hComm, hrestAny]
  | @equiv p p' q q' hsc hmid hsc' ih =>
      have hc' : CoreCanonical p' := coreCanonical_of_SC hc hsc
      have hq' : CoreCanonical q' := ih hc'
      exact coreCanonical_of_SC hq' hsc'
  | @par p q rest hstep ih =>
      have hp : CoreCanonical p :=
        coreCanonical_elem_of_collection (ct := .hashBag) (elems := p :: rest) hc (by simp)
      have hq : CoreCanonical q := ih hp
      have hrestAll : ∀ e ∈ rest, hasDerivedHead e = false := by
        intro e he
        exact coreCanonical_elem_of_collection
          (ct := .hashBag) (elems := p :: rest) hc (by simp [he])
      have hrestAny : (rest.map hasDerivedHead).any (fun b => b) = false :=
        hasDerivedHead_any_false_of_forall_false hrestAll
      unfold CoreCanonical at hq ⊢
      simp [hasDerivedHead, hq, hrestAny]
  | @par_any p q before after hstep ih =>
      have hp : CoreCanonical p :=
        coreCanonical_elem_of_collection
          (ct := .hashBag) (elems := before ++ [p] ++ after) hc (by simp)
      have hq : CoreCanonical q := ih hp
      have hsrcAll : ∀ e ∈ before ++ ([p] ++ after), hasDerivedHead e = false := by
        intro e he
        exact coreCanonical_elem_of_collection
          (ct := .hashBag) (elems := before ++ [p] ++ after) hc (by simpa [List.append_assoc] using he)
      have hdstAllAssoc : ∀ e ∈ before ++ ([q] ++ after), hasDerivedHead e = false := by
        intro e he
        rcases List.mem_append.mp he with hBefore | hTail
        · exact hsrcAll e (List.mem_append.mpr (Or.inl hBefore))
        · rcases List.mem_append.mp hTail with hMid | hAfter
          · have heq : e = q := by simpa using hMid
            subst heq; exact hq
          · exact hsrcAll e (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hAfter))))
      have hdstAll : ∀ e ∈ before ++ [q] ++ after, hasDerivedHead e = false := by
        intro e he
        exact hdstAllAssoc e (by simpa [List.append_assoc] using he)
      unfold CoreCanonical
      simpa [hasDerivedHead] using hasDerivedHead_any_false_of_forall_false hdstAll
  | @par_set p q rest hstep ih =>
      have hp : CoreCanonical p :=
        coreCanonical_elem_of_collection (ct := .hashSet) (elems := p :: rest) hc (by simp)
      have hq : CoreCanonical q := ih hp
      have hrestAll : ∀ e ∈ rest, hasDerivedHead e = false := by
        intro e he
        exact coreCanonical_elem_of_collection
          (ct := .hashSet) (elems := p :: rest) hc (by simp [he])
      have hrestAny : (rest.map hasDerivedHead).any (fun b => b) = false :=
        hasDerivedHead_any_false_of_forall_false hrestAll
      unfold CoreCanonical at hq ⊢
      simp [hasDerivedHead, hq, hrestAny]
  | @par_set_any p q before after hstep ih =>
      have hp : CoreCanonical p :=
        coreCanonical_elem_of_collection
          (ct := .hashSet) (elems := before ++ [p] ++ after) hc (by simp)
      have hq : CoreCanonical q := ih hp
      have hsrcAll : ∀ e ∈ before ++ ([p] ++ after), hasDerivedHead e = false := by
        intro e he
        exact coreCanonical_elem_of_collection
          (ct := .hashSet) (elems := before ++ [p] ++ after) hc (by simpa [List.append_assoc] using he)
      have hdstAllAssoc : ∀ e ∈ before ++ ([q] ++ after), hasDerivedHead e = false := by
        intro e he
        rcases List.mem_append.mp he with hBefore | hTail
        · exact hsrcAll e (List.mem_append.mpr (Or.inl hBefore))
        · rcases List.mem_append.mp hTail with hMid | hAfter
          · have heq : e = q := by simpa using hMid
            subst heq; exact hq
          · exact hsrcAll e (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hAfter))))
      have hdstAll : ∀ e ∈ before ++ [q] ++ after, hasDerivedHead e = false := by
        intro e he
        exact hdstAllAssoc e (by simpa [List.append_assoc] using he)
      unfold CoreCanonical
      simpa [hasDerivedHead] using hasDerivedHead_any_false_of_forall_false hdstAll

/-- Derived one-step reduction preserves core-canonical shape. -/
theorem coreCanonical_of_derived_step {p q : Pattern}
    (hc : CoreCanonical p) (h : p ⇝ᵈ q) : CoreCanonical q := by
  exact coreCanonical_of_core_step hc (ReducesDerived.toCore_of_coreCanonical hc h)

/-- Conservativity (star): derived traces from core-canonical sources reduce in core. -/
noncomputable def ReducesDerivedStar.toCore_of_coreCanonical {p q : Pattern}
    (hc : CoreCanonical p) (hs : p ⇝ᵈ* q) : p ⇝* q := by
  induction hs with
  | refl p =>
      exact .refl p
  | @step p r q hstep htail ih =>
      have hcore : p ⇝ r := ReducesDerived.toCore_of_coreCanonical hc hstep
      have hc' : CoreCanonical r := coreCanonical_of_derived_step hc hstep
      exact .step hcore (ih hc')

/-- Witness-free conservativity transport (star):
from core-canonical sources, any inhabited derived trace yields an inhabited core trace. -/
theorem ReducesDerivedStar.toCore_of_coreCanonical_nonempty {p q : Pattern}
    (hc : CoreCanonical p) :
    Nonempty (p ⇝ᵈ* q) → Nonempty (p ⇝* q) := by
  intro hs
  exact ⟨ReducesDerivedStar.toCore_of_coreCanonical hc (Classical.choice hs)⟩

/-- Witness-free embedding (star): any inhabited core trace yields an inhabited derived trace. -/
theorem ReducesStar.toDerived_nonempty {p q : Pattern} :
    Nonempty (p ⇝* q) → Nonempty (p ⇝ᵈ* q) := by
  intro hs
  exact ⟨ReducesStar.toDerived (Classical.choice hs)⟩

/-- Core-canonical star equivalence between core and derived relations. -/
theorem coreCanonical_star_nonempty_iff {p q : Pattern}
    (hc : CoreCanonical p) :
    Nonempty (p ⇝ᵈ* q) ↔ Nonempty (p ⇝* q) := by
  constructor
  · exact ReducesDerivedStar.toCore_of_coreCanonical_nonempty hc
  · exact ReducesStar.toDerived_nonempty

/-- Conservativity (star, core-compatible traces):
transport a derived star trace to core when a `CoreCompatible` witness is available. -/
noncomputable def ReducesDerivedStar.toCore_of_coreCanonical_of_coreCompatible {p q : Pattern}
    (_hc : CoreCanonical p) {hs : p ⇝ᵈ* q} (hcc : CoreCompatible hs) : p ⇝* q :=
  CoreCompatible.toCore hcc

/-- Witness that a core reduction proof used a non-`equiv` constructor. -/
inductive IsDirectCore : {p q : Pattern} → (p ⇝ q) → Prop where
  | comm {n q p : Pattern} {rest : List Pattern} :
      IsDirectCore (@Reduces.comm n q p rest)
  | par {p q : Pattern} {rest : List Pattern} (h : p ⇝ q) :
      IsDirectCore (@Reduces.par p q rest h)
  | par_any {p q : Pattern} {before after : List Pattern} (h : p ⇝ q) :
      IsDirectCore (@Reduces.par_any p q before after h)
  | par_set {p q : Pattern} {rest : List Pattern} (h : p ⇝ q) :
      IsDirectCore (@Reduces.par_set p q rest h)
  | par_set_any {p q : Pattern} {before after : List Pattern} (h : p ⇝ q) :
      IsDirectCore (@Reduces.par_set_any p q before after h)

/-- Design boundary: `PReplicate` cannot reduce via any direct core constructor.
    If it reduces at all in core semantics, that proof necessarily uses `equiv`.
-/
theorem no_direct_core_step_from_PReplicate {p q : Pattern}
    (h : (.apply "PReplicate" [p]) ⇝ q) : ¬ IsDirectCore h := by
  intro hdir
  let aux (p0 : Pattern) :
      ∀ s q0, s = (.apply "PReplicate" [p0]) → (hred : s ⇝ q0) → IsDirectCore hred → False := by
    intro s q0 hs hred hdirect
    cases hdirect with
    | comm => simp at hs
    | par _ => simp at hs
    | par_any _ => simp at hs
    | par_set _ => simp at hs
    | par_set_any _ => simp at hs
  exact aux p _ _ rfl h hdir

/-- Design boundary: `PNu` also cannot reduce via any direct core constructor.
    Any core reduction proof from `PNu` must pass through `equiv`.
-/
theorem no_direct_core_step_from_PNu {p q : Pattern}
    (h : (.apply "PNu" [p]) ⇝ q) : ¬ IsDirectCore h := by
  intro hdir
  let aux (p0 : Pattern) :
      ∀ s q0, s = (.apply "PNu" [p0]) → (hred : s ⇝ q0) → IsDirectCore hred → False := by
    intro s q0 hs hred hdirect
    cases hdirect with
    | comm => simp at hs
    | par _ => simp at hs
    | par_any _ => simp at hs
    | par_set _ => simp at hs
    | par_set_any _ => simp at hs
  exact aux p _ _ rfl h hdir

/-- Any core step from `PReplicate` has an explicit `equiv` shell.
    This is the strongest fully-proved boundary theorem currently available. -/
theorem core_step_from_PReplicate_has_equiv_shell {p q : Pattern}
    (h : (.apply "PReplicate" [p]) ⇝ q) :
    ∃ p' q', ∃ _ : p' ⇝ q',
      StructuralCongruence (.apply "PReplicate" [p]) p' ∧ StructuralCongruence q' q := by
  let aux (p0 : Pattern) :
      ∀ s q0, s = (.apply "PReplicate" [p0]) → (hred : s ⇝ q0) →
        ∃ p' q', ∃ _ : p' ⇝ q',
          StructuralCongruence (.apply "PReplicate" [p0]) p' ∧ StructuralCongruence q' q0 := by
    intro s q0 hs hred
    induction hred generalizing p0 with
    | comm => simp at hs
    | par h ih => simp at hs
    | par_any h ih => simp at hs
    | par_set h ih => simp at hs
    | par_set_any h ih => simp at hs
    | equiv hsc hmid hsc2 ih =>
      exact ⟨_, _, hmid, ⟨hs ▸ hsc, hsc2⟩⟩
  exact aux p _ _ rfl h

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu
