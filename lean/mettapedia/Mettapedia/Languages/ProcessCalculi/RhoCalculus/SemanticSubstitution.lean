import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhoOpening
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubjectEquiv

/-!
# ρ-Calculus Semantic COMM Substitution

Paper-faithful COMM substitution for the strict-core ρ-calculus.

This module keeps the generic locally nameless `openBVar` machinery intact for
syntactic substitution, while providing the operational substitution used by the
ρ-calculus COMM rule:

- quoted process bodies are opaque to substitution;
- names are normalized through quote-drop before matching;
- drop-of-quote collapses only when the COMM substitution itself revealed the
  quoted process under the drop.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax

private theorem struct_apply_cong_single {f : String} {p q : Pattern}
    (hpq : StructuralCongruence p q) :
    StructuralCongruence (.apply f [p]) (.apply f [q]) := by
  refine StructuralCongruence.apply_cong f [p] [q] rfl ?_
  intro i h₁ h₂
  have hi : i = 0 := by
    have hlt : i < 1 := by simpa using h₁
    simpa using hlt
  subst hi
  simpa using hpq

private theorem struct_apply_cong_two {f : String} {p₁ p₂ q₁ q₂ : Pattern}
    (h₁ : StructuralCongruence p₁ q₁) (h₂ : StructuralCongruence p₂ q₂) :
    StructuralCongruence (.apply f [p₁, p₂]) (.apply f [q₁, q₂]) := by
  refine StructuralCongruence.apply_cong f [p₁, p₂] [q₁, q₂] rfl ?_
  intro i h₁i h₂i
  have hlt : i < 2 := by simpa using h₁i
  have hi : i = 0 ∨ i = 1 := by omega
  cases hi with
  | inl hi0 =>
      subst hi0
      simpa using h₁
  | inr hi1 =>
      subst hi1
      simpa using h₂

mutual
  /-- Name normalization with quote-drop cancellation. -/
  def semanticNormalizeName : Pattern → Pattern
    | .bvar n => .bvar n
    | .fvar x => .fvar x
    | .apply "NQuote" [.apply "PDrop" [n]] =>
        semanticNormalizeName n
    | .apply "NQuote" [p] =>
        .apply "NQuote" [semanticNormalizeProc p]
    | n => n

  /-- Process normalization needed by semantic substitution on names. -/
  def semanticNormalizeProc : Pattern → Pattern
    | .bvar n => .bvar n
    | .fvar x => .fvar x
    | .apply "POutput" [n, q] =>
        .apply "POutput" [semanticNormalizeName n, semanticNormalizeProc q]
    | .apply "PInput" [n, .lambda none body] =>
        .apply "PInput" [semanticNormalizeName n, .lambda none (semanticNormalizeProc body)]
    | .apply "PDrop" [n] =>
        .apply "PDrop" [semanticNormalizeName n]
    | .apply "NQuote" [p] =>
        .apply "NQuote" [semanticNormalizeProc p]
    | .lambda nm body =>
        .lambda nm (semanticNormalizeProc body)
    | .multiLambda n nms body =>
        .multiLambda n nms (semanticNormalizeProc body)
    | .subst body repl =>
        .subst (semanticNormalizeProc body) (semanticNormalizeProc repl)
    | .collection ct elems rest =>
        .collection ct (semanticNormalizeProcList elems) rest
    | p => p

  /-- List recursion for process normalization. -/
  def semanticNormalizeProcList : List Pattern → List Pattern
    | [] => []
    | p :: ps => semanticNormalizeProc p :: semanticNormalizeProcList ps
end

/-- Name substitution for COMM: normalize the name, then replace the bound name
    only when the normalized name is exactly the target bound variable. The
    boolean records whether such a match occurred. -/
def semanticSubstNameMark (k : Nat) (replacementName : Pattern) (name : Pattern) :
    Pattern × Bool :=
  let norm := semanticNormalizeName name
  match norm with
  | .bvar n =>
      if n == k then (replacementName, true) else (.bvar n, false)
  | _ => (norm, false)

/-- The name-only projection of `semanticSubstNameMark`. -/
def semanticSubstName (k : Nat) (replacementName : Pattern) (name : Pattern) : Pattern :=
  (semanticSubstNameMark k replacementName name).1

mutual
  /-- Paper-faithful COMM substitution on process bodies.

  This mirrors the operational shape of CeTTa's strict-core reducer:
  - descend through process constructors;
  - substitute in names only via `semanticSubstName`;
  - do not descend under literal `NQuote`;
  - collapse `PDrop n` only when COMM substitution matched the dropped name and
    exposed a quoted process. -/
  def semanticSubstProc (k : Nat) (replacementName : Pattern) : Pattern → Pattern
    | .bvar n => if n == k then replacementName else .bvar n
    | .fvar x => .fvar x
    | .apply "NQuote" [p] => .apply "NQuote" [p]
    | .apply "PDrop" [name] =>
        let (name', matched) := semanticSubstNameMark k replacementName name
        match name', matched with
        | .apply "NQuote" [p], true => p
        | _, _ => .apply "PDrop" [name']
    | .apply "POutput" [n, q] =>
        .apply "POutput"
          [semanticSubstName k replacementName n, semanticSubstProc k replacementName q]
    | .apply "PInput" [n, .lambda none body] =>
        .apply "PInput"
          [semanticSubstName k replacementName n,
           .lambda none (semanticSubstProc (k + 1) replacementName body)]
    | .lambda nm body =>
        .lambda nm (semanticSubstProc (k + 1) replacementName body)
    | .multiLambda n nms body =>
        .multiLambda n nms (semanticSubstProc (k + n) replacementName body)
    | .subst body repl =>
        .subst (semanticSubstProc (k + 1) replacementName body)
               (semanticSubstProc k replacementName repl)
    | .collection ct elems rest =>
        .collection ct (semanticSubstProcList k replacementName elems) rest
    | p => p

  /-- List recursion for semantic process substitution. -/
  def semanticSubstProcList (k : Nat) (replacementName : Pattern) : List Pattern → List Pattern
    | [] => []
    | p :: ps => semanticSubstProc k replacementName p :: semanticSubstProcList k replacementName ps
end

mutual
  /-- A no-collapse semantic representative for COMM substitution.

  This keeps the same quote-opacity and name-normalization behavior as
  `semanticSubstProc`, but leaves matched `drop` sites as explicit
  `PDrop (NQuote ...)` nodes instead of collapsing them immediately. -/
  def semanticSubstProcNoCollapse (k : Nat) (replacementName : Pattern) : Pattern → Pattern
    | .bvar n => if n == k then replacementName else .bvar n
    | .fvar x => .fvar x
    | .apply "NQuote" [p] => .apply "NQuote" [p]
    | .apply "PDrop" [name] =>
        .apply "PDrop" [semanticSubstName k replacementName name]
    | .apply "POutput" [n, q] =>
        .apply "POutput"
          [semanticSubstName k replacementName n,
           semanticSubstProcNoCollapse k replacementName q]
    | .apply "PInput" [n, .lambda none body] =>
        .apply "PInput"
          [semanticSubstName k replacementName n,
           .lambda none (semanticSubstProcNoCollapse (k + 1) replacementName body)]
    | .lambda nm body =>
        .lambda nm (semanticSubstProcNoCollapse (k + 1) replacementName body)
    | .multiLambda n nms body =>
        .multiLambda n nms (semanticSubstProcNoCollapse (k + n) replacementName body)
    | .subst body repl =>
        .subst (semanticSubstProcNoCollapse (k + 1) replacementName body)
               (semanticSubstProcNoCollapse k replacementName repl)
    | .collection ct elems rest =>
        .collection ct (semanticSubstProcNoCollapseList k replacementName elems) rest
    | p => p

  /-- List recursion for the no-collapse semantic representative. -/
  def semanticSubstProcNoCollapseList (k : Nat) (replacementName : Pattern) : List Pattern → List Pattern
    | [] => []
    | p :: ps =>
        semanticSubstProcNoCollapse k replacementName p ::
          semanticSubstProcNoCollapseList k replacementName ps
end

/-- Explicit no-collapse representative for the live semantic COMM result. -/
def semanticCommRepresentative (pBody q : Pattern) : Pattern :=
  semanticSubstProcNoCollapse 0 (.apply "NQuote" [q]) pBody

/-- Strict-core ρ-calculus COMM substitution: substitute the quoted, normalized
    payload for bound variable 0. -/
def semanticCommSubst (pBody q : Pattern) : Pattern :=
  semanticSubstProc 0 (.apply "NQuote" [semanticNormalizeProc q]) pBody

theorem semanticCommSubst_collapses_bound_drop (q : Pattern) :
    semanticCommSubst (.apply "PDrop" [.bvar 0]) q = semanticNormalizeProc q := by
  simp [semanticCommSubst, semanticSubstProc, semanticSubstNameMark, semanticNormalizeName]

theorem semanticCommSubst_preserves_output_literal_drop
    (chan payload q : Pattern) :
    semanticCommSubst (.apply "PDrop" [.apply "NQuote" [.apply "POutput" [chan, payload]]]) q =
      .apply "PDrop"
        [.apply "NQuote" [.apply "POutput" [semanticNormalizeName chan, semanticNormalizeProc payload]]] := by
  simp [semanticCommSubst, semanticSubstProc, semanticSubstNameMark,
    semanticNormalizeName, semanticNormalizeProc]

theorem semanticCommSubst_preserves_quoted_code (p q : Pattern) :
    semanticCommSubst (.apply "NQuote" [p]) q = .apply "NQuote" [p] := by
  simp [semanticCommSubst, semanticSubstProc]

theorem semanticCommSubst_normalizes_free_quote_drop_output_channel_empty_payload
    (x : String) (q : Pattern) :
    semanticCommSubst
      (.apply "POutput"
        [.apply "NQuote" [.apply "PDrop" [.fvar x]],
         .collection .hashBag [] none])
  q
      =
      (.apply "POutput" [.fvar x, .collection .hashBag [] none]) := by
  simp [semanticCommSubst, semanticSubstProc, semanticSubstProcList,
    semanticSubstName, semanticSubstNameMark,
    semanticNormalizeName]

theorem semanticCommSubst_bare_bound_becomes_normalized_quote (q : Pattern) :
    semanticCommSubst (.bvar 0) q = .apply "NQuote" [semanticNormalizeProc q] := by
  simp [semanticCommSubst, semanticSubstProc]

/-- Concrete quoted-code opacity witness: semantic COMM does not descend under
literal quote, even when the quoted process contains the bound name. -/
theorem semanticCommSubst_preserves_quote_opacity_output_emptyBag
    (q : Pattern) :
    semanticCommSubst
      (.apply "POutput"
        [.apply "NQuote"
          [.apply "POutput" [.bvar 0, .collection .hashBag [] none]],
         .collection .hashBag [] none])
      q
      =
      (.apply "POutput"
        [.apply "NQuote"
          [.apply "POutput" [.bvar 0, .collection .hashBag [] none]],
         .collection .hashBag [] none]) := by
  rfl

/-- Concrete quoted-code opacity witness against syntactic opening: semantic
COMM respects literal quote opacity, while the old syntactic opener descends
under the quote. -/
theorem semanticCommSubst_diverges_from_syntactic_open_on_quote_opacity_emptyBag :
    semanticCommSubst
      (.apply "POutput"
        [.apply "NQuote"
          [.apply "POutput" [.bvar 0, .collection .hashBag [] none]],
         .collection .hashBag [] none])
      (.collection .hashBag [] none)
      ≠
      Mettapedia.OSLF.MeTTaIL.Substitution.commSubst
        (.apply "POutput"
          [.apply "NQuote"
            [.apply "POutput" [.bvar 0, .collection .hashBag [] none]],
           .collection .hashBag [] none])
        (.collection .hashBag [] none) := by
  native_decide

private theorem procResidual_apply_cong_single {f : String} {p q : Pattern}
    (hpq : ProcResidualEquiv p q) :
    ProcResidualEquiv (.apply f [p]) (.apply f [q]) := by
  refine ProcResidualEquiv.apply_cong f [p] [q] rfl ?_
  intro i h₁ h₂
  have hi : i = 0 := by
    have hlt : i < 1 := by simpa using h₁
    simpa using hlt
  subst hi
  simpa using hpq

private theorem procResidual_apply_cong_two {f : String} {p₁ p₂ q₁ q₂ : Pattern}
    (h₁ : ProcResidualEquiv p₁ q₁) (h₂ : ProcResidualEquiv p₂ q₂) :
    ProcResidualEquiv (.apply f [p₁, p₂]) (.apply f [q₁, q₂]) := by
  refine ProcResidualEquiv.apply_cong f [p₁, p₂] [q₁, q₂] rfl ?_
  intro i h₁i h₂i
  have hlt : i < 2 := by simpa using h₁i
  have hi : i = 0 ∨ i = 1 := by omega
  cases hi with
  | inl hi0 =>
      subst hi0
      simpa using h₁
  | inr hi1 =>
      subst hi1
      simpa using h₂

theorem semanticCommSubst_bound_drop_differs_from_syntactic_open_on_emptyBag :
    semanticCommSubst (.apply "PDrop" [.bvar 0]) (.collection .hashBag [] none) ≠
      Mettapedia.OSLF.MeTTaIL.Substitution.openBVar 0
        (.apply "NQuote" [.collection .hashBag [] none])
        (.apply "PDrop" [.bvar 0]) := by
  native_decide

theorem semanticNormalizeName_free_quote_drop_var (x : String) :
    semanticNormalizeName (.apply "NQuote" [.apply "PDrop" [.fvar x]]) = .fvar x := by
  simp [semanticNormalizeName]

mutual
  theorem semanticNormalizeName_sound :
      ∀ n : Pattern, NameEquiv (semanticNormalizeName n) n
    | .bvar n => NameEquiv.refl (.bvar n)
    | .fvar x => NameEquiv.refl (.fvar x)
    | .apply "NQuote" [.apply "PDrop" [n]] =>
        NameEquiv.trans _ _ _
          (semanticNormalizeName_sound n)
          (NameEquiv.symm _ _ (NameEquiv.quote_drop n))
    | .apply "NQuote" [p] => by
        by_cases hdropq : ∃ n, p = .apply "PDrop" [n]
        · rcases hdropq with ⟨n, rfl⟩
          simpa [semanticNormalizeName.eq_3] using
            (NameEquiv.trans _ _ _
              (semanticNormalizeName_sound n)
              (NameEquiv.symm _ _ (NameEquiv.quote_drop n)))
        · have hpnot : ∀ n, p = .apply "PDrop" [n] → False := by
            intro n hpdrop
            exact hdropq ⟨n, hpdrop⟩
          rw [semanticNormalizeName.eq_4 p hpnot]
          exact NameEquiv.struct_equiv (semanticNormalizeProc p) p
            (semanticNormalizeProc_sound p)
    | .apply c args => by
        by_cases hqd : c = "NQuote" ∧ ∃ n, args = [.apply "PDrop" [n]]
        · rcases hqd with ⟨rfl, n, rfl⟩
          simpa [semanticNormalizeName] using
            (NameEquiv.trans _ _ _
              (semanticNormalizeName_sound n)
              (NameEquiv.symm _ _ (NameEquiv.quote_drop n)))
        · by_cases hq : c = "NQuote" ∧ ∃ p', args = [p']
          · rcases hq with ⟨rfl, p', rfl⟩
            have hpnot : ∀ n, p' = .apply "PDrop" [n] → False := by
              intro n hpdrop
              exact hqd ⟨rfl, ⟨n, by simp [hpdrop]⟩⟩
            rw [semanticNormalizeName.eq_4 p' hpnot]
            exact NameEquiv.struct_equiv (semanticNormalizeProc p') p'
              (semanticNormalizeProc_sound p')
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
            exact NameEquiv.refl (.apply c args)
    | .lambda nm body => by
        simpa [semanticNormalizeName] using (NameEquiv.refl (.lambda nm body))
    | .multiLambda n nms body => by
        simpa [semanticNormalizeName] using
          (NameEquiv.refl (.multiLambda n nms body))
    | .subst body repl => by
        simpa [semanticNormalizeName] using
          (NameEquiv.refl (.subst body repl))
    | .collection ct elems rest => by
        simpa [semanticNormalizeName] using
          (NameEquiv.refl (.collection ct elems rest))

  theorem semanticNormalizeProc_sound :
      ∀ p : Pattern, StructuralCongruence (semanticNormalizeProc p) p
    | .bvar n => StructuralCongruence.refl (.bvar n)
    | .fvar x => StructuralCongruence.refl (.fvar x)
    | .apply "POutput" [n, q] =>
        struct_apply_cong_two
          (nameEquiv_implies_struct (semanticNormalizeName_sound n))
          (semanticNormalizeProc_sound q)
    | .apply "PInput" [n, .lambda none body] =>
        struct_apply_cong_two
          (nameEquiv_implies_struct (semanticNormalizeName_sound n))
          (StructuralCongruence.lambda_cong none (semanticNormalizeProc body) body
            (semanticNormalizeProc_sound body))
    | .apply "PDrop" [n] =>
        struct_apply_cong_single
          (nameEquiv_implies_struct (semanticNormalizeName_sound n))
    | .apply "NQuote" [p] =>
        struct_apply_cong_single
          (semanticNormalizeProc_sound p)
    | .lambda nm body =>
        StructuralCongruence.lambda_cong nm (semanticNormalizeProc body) body
          (semanticNormalizeProc_sound body)
    | .multiLambda n nms body =>
        StructuralCongruence.multiLambda_cong n nms (semanticNormalizeProc body) body
          (semanticNormalizeProc_sound body)
    | .subst body repl =>
        StructuralCongruence.subst_cong (semanticNormalizeProc body) body
          (semanticNormalizeProc repl) repl
          (semanticNormalizeProc_sound body)
          (semanticNormalizeProc_sound repl)
    | .collection ct elems rest =>
        StructuralCongruence.collection_general_cong ct (semanticNormalizeProcList elems) elems rest
          (by simp [semanticNormalizeProcList_length elems])
          (semanticNormalizeProcList_sound elems)
    | .apply c args => by
        by_cases hout : c = "POutput" ∧ ∃ n q, args = [n, q]
        · rcases hout with ⟨rfl, n, q, rfl⟩
          exact struct_apply_cong_two
            (nameEquiv_implies_struct (semanticNormalizeName_sound n))
            (semanticNormalizeProc_sound q)
        · by_cases hin : c = "PInput" ∧ ∃ n body, args = [n, .lambda none body]
          · rcases hin with ⟨rfl, n, body, rfl⟩
            exact struct_apply_cong_two
              (nameEquiv_implies_struct (semanticNormalizeName_sound n))
              (StructuralCongruence.lambda_cong none (semanticNormalizeProc body) body
                (semanticNormalizeProc_sound body))
          · by_cases hdrop : c = "PDrop" ∧ ∃ n, args = [n]
            · rcases hdrop with ⟨rfl, n, rfl⟩
              exact struct_apply_cong_single
                (nameEquiv_implies_struct (semanticNormalizeName_sound n))
            · by_cases hquote : c = "NQuote" ∧ ∃ p', args = [p']
              · rcases hquote with ⟨rfl, p', rfl⟩
                exact struct_apply_cong_single
                  (semanticNormalizeProc_sound p')
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
                exact StructuralCongruence.refl (.apply c args)

  theorem semanticNormalizeProcList_length :
      ∀ elems : List Pattern, (semanticNormalizeProcList elems).length = elems.length
    | [] => rfl
    | _ :: ps => by
        simp [semanticNormalizeProcList, semanticNormalizeProcList_length ps]

  theorem semanticNormalizeProcList_sound :
      ∀ elems : List Pattern,
        ∀ i h₁ h₂,
          StructuralCongruence ((semanticNormalizeProcList elems).get ⟨i, h₁⟩) (elems.get ⟨i, h₂⟩)
    | [], i, h₁, _ => by
        cases h₁
    | p :: ps, 0, h₁, h₂ => by
        simpa [semanticNormalizeProcList] using semanticNormalizeProc_sound p
    | p :: ps, i + 1, h₁, h₂ => by
        have h₁' : i < (semanticNormalizeProcList ps).length := by
          simpa [semanticNormalizeProcList, semanticNormalizeProcList_length ps] using h₁
        have h₂' : i < ps.length := by
          simpa using h₂
        simpa [semanticNormalizeProcList] using semanticNormalizeProcList_sound ps i h₁' h₂'
end

theorem semanticNormalizeName_sound_struct {n : Pattern} :
    StructuralCongruence (semanticNormalizeName n) n :=
  nameEquiv_implies_struct (semanticNormalizeName_sound n)

private theorem semanticSubstNameMark_true_eq_replacement
    (k : Nat) (replacementName name name' : Pattern)
    (hmark : semanticSubstNameMark k replacementName name = (name', true)) :
    name' = replacementName := by
  unfold semanticSubstNameMark at hmark
  cases hnorm : semanticNormalizeName name with
  | bvar n =>
      by_cases hnk : n = k
      · subst hnk
        simpa [hnorm, beq_self_eq_true] using hmark.symm
      · have hbeq : (n == k) = false := beq_eq_false_iff_ne.mpr hnk
        simp [hnorm, hbeq] at hmark
  | fvar x =>
      simp [hnorm] at hmark
  | apply c args =>
      simp [hnorm] at hmark
  | lambda nm body =>
      simp [hnorm] at hmark
  | multiLambda n nms body =>
      simp [hnorm] at hmark
  | subst body repl =>
      simp [hnorm] at hmark
  | collection ct elems rest =>
      simp [hnorm] at hmark

theorem semanticSubstName_transport_to_representative (k : Nat) (q name : Pattern) :
    NameEquiv
      (semanticSubstName k (.apply "NQuote" [semanticNormalizeProc q]) name)
      (semanticSubstName k (.apply "NQuote" [q]) name) := by
  cases hnorm : semanticNormalizeName name with
  | bvar n =>
      by_cases hnk : n = k
      · subst hnk
        simpa [semanticSubstName, semanticSubstNameMark, hnorm, beq_self_eq_true] using
          (quote_respects_structural (semanticNormalizeProc_sound q))
      · have hbeq : (n == k) = false := beq_eq_false_iff_ne.mpr hnk
        simpa [semanticSubstName, semanticSubstNameMark, hnorm, hbeq] using
          (NameEquiv.refl (.bvar n))
  | fvar x =>
      simpa [semanticSubstName, semanticSubstNameMark, hnorm] using
        (NameEquiv.refl (.fvar x))
  | apply c args =>
      simpa [semanticSubstName, semanticSubstNameMark, hnorm] using
        (NameEquiv.refl (.apply c args))
  | lambda nm body =>
      simpa [semanticSubstName, semanticSubstNameMark, hnorm] using
        (NameEquiv.refl (.lambda nm body))
  | multiLambda n nms body =>
      simpa [semanticSubstName, semanticSubstNameMark, hnorm] using
        (NameEquiv.refl (.multiLambda n nms body))
  | subst body repl =>
      simpa [semanticSubstName, semanticSubstNameMark, hnorm] using
        (NameEquiv.refl (.subst body repl))
  | collection ct elems rest =>
      simpa [semanticSubstName, semanticSubstNameMark, hnorm] using
        (NameEquiv.refl (.collection ct elems rest))

theorem semanticSubstProcList_length (k : Nat) (replacementName : Pattern) :
    ∀ elems : List Pattern,
      (semanticSubstProcList k replacementName elems).length = elems.length
  | [] => rfl
  | _ :: elems => by
      simp [semanticSubstProcList, semanticSubstProcList_length k replacementName elems]

theorem semanticSubstProcNoCollapseList_length (k : Nat) (replacementName : Pattern) :
    ∀ elems : List Pattern,
      (semanticSubstProcNoCollapseList k replacementName elems).length = elems.length
  | [] => rfl
  | _ :: elems => by
      simp [semanticSubstProcNoCollapseList,
        semanticSubstProcNoCollapseList_length k replacementName elems]

private theorem rhoOpenNameBVarList_length (k : Nat) (u : Pattern) :
    ∀ elems : List Pattern,
      (rhoOpenNameBVarList k u elems).length = elems.length
  | [] => rfl
  | _ :: elems => by
      simp [rhoOpenNameBVarList, rhoOpenNameBVarList_length k u elems]

private theorem rhoNameCoreShape_apply_nil (c : String) :
    rhoNameCoreShape (.apply c []) = false := by
  refine rhoNameCoreShape.eq_4 (.apply c []) ?_ ?_ ?_
  · intro a h
    cases h
  · intro a h
    cases h
  · intro p h
    cases h

private theorem rhoNameCoreShape_apply_single (c : String) (a : Pattern) :
    rhoNameCoreShape (.apply c [a]) =
      (if c = "NQuote" then rhoProcCoreShape a else false) := by
  by_cases hc : c = "NQuote"
  · subst hc
    simp [rhoNameCoreShape]
  · have hfalse : rhoNameCoreShape (.apply c [a]) = false := by
      refine rhoNameCoreShape.eq_4 (.apply c [a]) ?_ ?_ ?_
      · intro n h
        cases h
      · intro x h
        cases h
      · intro p h
        injection h with hc' hargs
        exact hc hc'
    simp [hc, hfalse]

private theorem rhoNameCoreShape_apply_many (c : String) (a b : Pattern) (bs : List Pattern) :
    rhoNameCoreShape (.apply c (a :: b :: bs)) = false := by
  refine rhoNameCoreShape.eq_4 (.apply c (a :: b :: bs)) ?_ ?_ ?_
  · intro n h
    cases h
  · intro x h
    cases h
  · intro p h
    injection h with hc hargs
    cases hargs

private theorem rhoNameCoreShape_apply_inv {c : String} {args : List Pattern}
    (hshape : rhoNameCoreShape (.apply c args) = true) :
    ∃ p, c = "NQuote" ∧ args = [p] ∧ rhoProcCoreShape p = true := by
  cases args with
  | nil =>
      rw [rhoNameCoreShape_apply_nil c] at hshape
      cases hshape
  | cons a as =>
      cases as with
      | nil =>
          rw [rhoNameCoreShape_apply_single c a] at hshape
          by_cases hc : c = "NQuote"
          · exact ⟨a, hc, rfl, by simpa [hc] using hshape⟩
          · simp [hc] at hshape
      | cons b bs =>
          rw [rhoNameCoreShape_apply_many c a b bs] at hshape
          cases hshape

private theorem rhoProcCoreShape_apply_cases {c : String} {args : List Pattern}
    (hshape : rhoProcCoreShape (.apply c args) = true) :
    (c = "PZero" ∧ args = []) ∨
    (∃ n, c = "PDrop" ∧ args = [n] ∧ rhoNameCoreShape n = true) ∨
    (∃ n payload, c = "POutput" ∧ args = [n, payload] ∧
      rhoNameCoreShape n = true ∧ rhoProcCoreShape payload = true) ∨
    (∃ n body, c = "PInput" ∧ args = [n, .lambda none body] ∧
      rhoNameCoreShape n = true ∧ rhoProcCoreShape body = true) := by
  cases args with
  | nil =>
      by_cases hzero : c = "PZero"
      · exact Or.inl ⟨hzero, rfl⟩
      · simp [rhoProcCoreShape, hzero] at hshape
  | cons a as =>
      cases as with
      | nil =>
          by_cases hdrop : c = "PDrop"
          · exact Or.inr <| Or.inl ⟨a, hdrop, rfl, by simpa [rhoProcCoreShape, hdrop] using hshape⟩
          · simp [rhoProcCoreShape, hdrop] at hshape
      | cons b bs =>
          cases bs with
          | nil =>
              by_cases hout : c = "POutput"
              · exact Or.inr <| Or.inr <| Or.inl
                  ⟨a, b, hout, rfl, by simpa [rhoProcCoreShape, hout] using hshape⟩
              · match b with
                | .lambda none body =>
                    by_cases hin : c = "PInput"
                    · exact Or.inr <| Or.inr <| Or.inr
                        ⟨a, body, hin, rfl, by simpa [rhoProcCoreShape, hout, hin] using hshape⟩
                    · simp [rhoProcCoreShape, hout, hin] at hshape
                | .lambda (.some nm) body =>
                    simp [rhoProcCoreShape, hout] at hshape
                | .bvar n =>
                    simp [rhoProcCoreShape, hout] at hshape
                | .fvar x =>
                    simp [rhoProcCoreShape, hout] at hshape
                | .apply f xs =>
                    simp [rhoProcCoreShape, hout] at hshape
                | .multiLambda n nms body =>
                    simp [rhoProcCoreShape, hout] at hshape
                | .subst body repl =>
                    simp [rhoProcCoreShape, hout] at hshape
                | .collection ct elems rest =>
                    simp [rhoProcCoreShape, hout] at hshape
          | cons b' bs' =>
              simp [rhoProcCoreShape] at hshape

private theorem rhoProcCoreShape_collection_inv {ct : CollType} {elems : List Pattern}
    {rest : Option String}
    (hshape : rhoProcCoreShape (.collection ct elems rest) = true) :
    ct = .hashBag ∧ rest = none ∧ rhoProcCoreShapeList elems = true := by
  cases ct <;> cases rest <;> simp [rhoProcCoreShape] at hshape
  exact ⟨rfl, rfl, hshape⟩

private theorem rhoNameCoreShape_noBoundUnderQuote_of_noBVar (k : Nat)
    {n : Pattern}
    (hshape : rhoNameCoreShape n = true)
    (hnoB : noBVar k n = true) :
    noBoundUnderQuote k n = true := by
  match n with
  | .bvar _ =>
      simp [noBoundUnderQuote]
  | .fvar _ =>
      simp [noBoundUnderQuote]
  | .apply "NQuote" [p] =>
      simpa [rhoNameCoreShape, noBoundUnderQuote, noBVar, noBVarList] using hnoB
  | .apply c args =>
      rcases rhoNameCoreShape_apply_inv hshape with ⟨p, hc, hargs, hp⟩
      subst hc
      subst hargs
      simpa [rhoNameCoreShape, noBoundUnderQuote, noBVar, noBVarList] using hnoB
  | .lambda nm body =>
      simp [rhoNameCoreShape] at hshape
  | .multiLambda n nms body =>
      simp [rhoNameCoreShape] at hshape
  | .subst body repl =>
      simp [rhoNameCoreShape] at hshape
  | .collection ct elems rest =>
      simp [rhoNameCoreShape] at hshape

private theorem rhoOpenNameBVar_eq_self_of_rhoNameCoreShape_noBVar (k : Nat) (u : Pattern)
    {n : Pattern}
    (hshape : rhoNameCoreShape n = true)
    (hnoB : noBVar k n = true) :
    rhoOpenNameBVar k u n = n := by
  match n with
  | .bvar n =>
      by_cases hEq : n = k
      · subst hEq
        simp [noBVar] at hnoB
      · have hbeq : (n == k) = false := by
          exact beq_eq_false_iff_ne.mpr hEq
        simp [rhoOpenNameBVar, hbeq]
  | .fvar _ =>
      simp [rhoOpenNameBVar]
  | .apply "NQuote" [_] =>
      simp [rhoOpenNameBVar]
  | .apply c args =>
      rcases rhoNameCoreShape_apply_inv hshape with ⟨p, hc, hargs, hp⟩
      subst hc
      subst hargs
      simp [rhoOpenNameBVar]
  | .lambda nm body =>
      simp [rhoNameCoreShape] at hshape
  | .multiLambda n nms body =>
      simp [rhoNameCoreShape] at hshape
  | .subst body repl =>
      simp [rhoNameCoreShape] at hshape
  | .collection ct elems rest =>
      simp [rhoNameCoreShape] at hshape

mutual
  theorem semanticSubstQuotedName_equiv_rhoOpenNameBVar_of_rhoProcCoreShape
      (k : Nat) (q : Pattern) (n : Pattern)
      (hshapeN : rhoProcCoreShape n = true)
      (hnoB : noBVar k n = true) :
      NameEquiv
        (semanticSubstName k (.apply "NQuote" [q]) (.apply "NQuote" [n]))
        (.apply "NQuote" [n]) := by
    by_cases hdrop : ∃ m, n = .apply "PDrop" [m]
    · rcases hdrop with ⟨m, rfl⟩
      have hshapeM : rhoNameCoreShape m = true := by
        simpa [rhoProcCoreShape] using hshapeN
      have hnoBM : noBVar k m = true := by
        simpa [noBVar, noBVarList] using hnoB
      have hopaqueM : noBoundUnderQuote k m = true :=
        rhoNameCoreShape_noBoundUnderQuote_of_noBVar k hshapeM hnoBM
      have hrec :
          NameEquiv
            (semanticSubstName k (.apply "NQuote" [q]) m)
            (rhoOpenNameBVar k (.apply "NQuote" [q]) m) :=
        semanticSubstName_equiv_rhoOpenNameBVar_of_rhoNameCoreShape k q hshapeM hopaqueM
      have hself :
          rhoOpenNameBVar k (.apply "NQuote" [q]) m = m :=
        rhoOpenNameBVar_eq_self_of_rhoNameCoreShape_noBVar k (.apply "NQuote" [q]) hshapeM hnoBM
      have hrec' :
          NameEquiv
            (semanticSubstName k (.apply "NQuote" [q]) m)
            m := by
        simpa [hself] using hrec
      have hsubst :
          semanticSubstName k (.apply "NQuote" [q]) (.apply "NQuote" [.apply "PDrop" [m]]) =
            semanticSubstName k (.apply "NQuote" [q]) m := by
        simp [semanticSubstName, semanticSubstNameMark, semanticNormalizeName]
      rw [hsubst]
      exact NameEquiv.trans _ _ _ hrec' (NameEquiv.symm _ _ (NameEquiv.quote_drop m))
    · have hsubst :
          semanticSubstName k (.apply "NQuote" [q]) (.apply "NQuote" [n]) =
            .apply "NQuote" [semanticNormalizeProc n] := by
        simp [semanticSubstName, semanticSubstNameMark,
          semanticNormalizeName.eq_4 n (by
            intro m hpdrop
            exact hdrop ⟨m, hpdrop⟩)]
      rw [hsubst]
      exact NameEquiv.struct_equiv
        (semanticNormalizeProc n)
        n
        (semanticNormalizeProc_sound n)
  termination_by 2 * sizeOf n

  theorem semanticSubstName_equiv_rhoOpenNameBVar_of_rhoNameCoreShape (k : Nat) (q : Pattern)
      {n : Pattern}
      (hshape : rhoNameCoreShape n = true)
      (hopaque : noBoundUnderQuote k n = true) :
      NameEquiv
        (semanticSubstName k (.apply "NQuote" [q]) n)
        (rhoOpenNameBVar k (.apply "NQuote" [q]) n) := by
    match n with
    | .bvar n =>
        by_cases hEq : n = k
        · subst hEq
          simpa [semanticSubstName, semanticSubstNameMark, semanticNormalizeName,
            rhoOpenNameBVar, beq_self_eq_true] using
            (NameEquiv.refl (.apply "NQuote" [q]))
        · have hbeq : (n == k) = false := by
            exact beq_eq_false_iff_ne.mpr hEq
          simpa [semanticSubstName, semanticSubstNameMark, semanticNormalizeName, rhoOpenNameBVar, hbeq] using
            (NameEquiv.refl (.bvar n))
    | .fvar x =>
        simpa [semanticSubstName, semanticSubstNameMark, semanticNormalizeName, rhoOpenNameBVar] using
          (NameEquiv.refl (.fvar x))
    | .apply "NQuote" [p] =>
        have hshapeP : rhoProcCoreShape p = true := by
          simpa [rhoNameCoreShape] using hshape
        have hnoB : noBVar k p = true := by
          simpa [noBoundUnderQuote] using hopaque
        simpa [rhoOpenNameBVar] using
          semanticSubstQuotedName_equiv_rhoOpenNameBVar_of_rhoProcCoreShape k q p hshapeP hnoB
    | .apply c args =>
        rcases rhoNameCoreShape_apply_inv hshape with ⟨p, hc, hargs, hshapeP⟩
        subst hc
        subst hargs
        have hnoB : noBVar k p = true := by
          simpa [noBoundUnderQuote] using hopaque
        simpa [rhoOpenNameBVar] using
          semanticSubstQuotedName_equiv_rhoOpenNameBVar_of_rhoProcCoreShape k q p hshapeP hnoB
    | .lambda nm body =>
        simp [rhoNameCoreShape] at hshape
    | .multiLambda n nms body =>
        simp [rhoNameCoreShape] at hshape
    | .subst body repl =>
        simp [rhoNameCoreShape] at hshape
    | .collection ct elems rest =>
        simp [rhoNameCoreShape] at hshape
  termination_by 2 * sizeOf n + 1
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      omega
end

mutual
  theorem semanticSubstProcNoCollapse_residual_equiv_rhoOpenNameBVar_of_rhoProcCoreShape
      (k : Nat) (q : Pattern)
      {p : Pattern}
      (hshape : rhoProcCoreShape p = true)
      (hopaque : noBoundUnderQuote k p = true) :
      ProcResidualEquiv
        (semanticSubstProcNoCollapse k (.apply "NQuote" [q]) p)
        (rhoOpenNameBVar k (.apply "NQuote" [q]) p) := by
    match p with
    | .bvar n =>
        by_cases hEq : n = k
        · subst hEq
          simpa [semanticSubstProcNoCollapse, rhoOpenNameBVar, beq_self_eq_true] using
            (ProcResidualEquiv.refl (.apply "NQuote" [q]))
        · have hbeq : (n == k) = false := by
            exact beq_eq_false_iff_ne.mpr hEq
          simpa [semanticSubstProcNoCollapse, rhoOpenNameBVar, hbeq] using
            (ProcResidualEquiv.refl (.bvar n))
    | .fvar x =>
        exact ProcResidualEquiv.refl (.fvar x)
    | .apply "PZero" [] =>
        exact ProcResidualEquiv.refl (.apply "PZero" [])
    | .apply "PDrop" [n] =>
        have hshapeN : rhoNameCoreShape n = true := by
          simpa [rhoProcCoreShape] using hshape
        have hopaqueN : noBoundUnderQuote k n = true := by
          simpa [noBoundUnderQuote, noBoundUnderQuoteList] using hopaque
        have hname :
            NameEquiv
              (semanticSubstName k (.apply "NQuote" [q]) n)
              (rhoOpenNameBVar k (.apply "NQuote" [q]) n) :=
          semanticSubstName_equiv_rhoOpenNameBVar_of_rhoNameCoreShape k q hshapeN hopaqueN
        simpa [semanticSubstProcNoCollapse, rhoOpenNameBVar, rhoOpenNameBVarList] using
          (procResidual_apply_cong_single (ProcResidualEquiv.of_nameEquiv hname))
    | .apply "POutput" [n, payload] =>
        have hshapeSplit : rhoNameCoreShape n = true ∧ rhoProcCoreShape payload = true := by
          simpa [rhoProcCoreShape] using hshape
        have hopaqueSplit :
            noBoundUnderQuote k n = true ∧ noBoundUnderQuote k payload = true := by
          simpa [noBoundUnderQuote, noBoundUnderQuoteList] using hopaque
        have hname :=
          semanticSubstName_equiv_rhoOpenNameBVar_of_rhoNameCoreShape k q hshapeSplit.1 hopaqueSplit.1
        have hpayload :=
          semanticSubstProcNoCollapse_residual_equiv_rhoOpenNameBVar_of_rhoProcCoreShape
            k q hshapeSplit.2 hopaqueSplit.2
        simpa [semanticSubstProcNoCollapse, rhoOpenNameBVar, rhoOpenNameBVarList] using
          (procResidual_apply_cong_two
            (ProcResidualEquiv.of_nameEquiv hname)
            hpayload)
    | .apply "PInput" [n, .lambda none body] =>
        have hshapeSplit : rhoNameCoreShape n = true ∧ rhoProcCoreShape body = true := by
          simpa [rhoProcCoreShape] using hshape
        have hopaqueSplit :
            noBoundUnderQuote k n = true ∧ noBoundUnderQuote (k + 1) body = true := by
          simpa [noBoundUnderQuote, noBoundUnderQuoteList] using hopaque
        have hname :=
          semanticSubstName_equiv_rhoOpenNameBVar_of_rhoNameCoreShape k q hshapeSplit.1 hopaqueSplit.1
        have hbody :=
          semanticSubstProcNoCollapse_residual_equiv_rhoOpenNameBVar_of_rhoProcCoreShape
            (k + 1) q hshapeSplit.2 hopaqueSplit.2
        simpa [semanticSubstProcNoCollapse, rhoOpenNameBVar, rhoOpenNameBVarList] using
          (procResidual_apply_cong_two
            (ProcResidualEquiv.of_nameEquiv hname)
            (ProcResidualEquiv.lambda_cong none hbody))
    | .collection .hashBag elems none =>
        have hshapeList : rhoProcCoreShapeList elems = true := by
          simpa [rhoProcCoreShape] using hshape
        have hopaqueList : noBoundUnderQuoteList k elems = true := by
          simpa [noBoundUnderQuote] using hopaque
        have hlenLeft :
            (semanticSubstProcNoCollapseList k (.apply "NQuote" [q]) elems).length =
              elems.length := semanticSubstProcNoCollapseList_length k (.apply "NQuote" [q]) elems
        have hlenRight :
            (rhoOpenNameBVarList k (.apply "NQuote" [q]) elems).length =
              elems.length := rhoOpenNameBVarList_length k (.apply "NQuote" [q]) elems
        have hlen :
            (semanticSubstProcNoCollapseList k (.apply "NQuote" [q]) elems).length =
              (rhoOpenNameBVarList k (.apply "NQuote" [q]) elems).length := by
          rw [hlenLeft, hlenRight]
        refine ProcResidualEquiv.collection_cong .hashBag
          (semanticSubstProcNoCollapseList k (.apply "NQuote" [q]) elems)
          (rhoOpenNameBVarList k (.apply "NQuote" [q]) elems)
          none hlen ?_
        intro i h₁ h₂
        simpa [semanticSubstProcNoCollapseList, rhoOpenNameBVarList] using
          semanticSubstProcNoCollapseList_residual_equiv_rhoOpenNameBVarList_of_rhoProcCoreShape
            k q elems hshapeList hopaqueList i h₁ h₂
    | .apply c args =>
        rcases rhoProcCoreShape_apply_cases hshape with
          hzero | hdrop | houtput | hinput
        · rcases hzero with ⟨hc, hargs⟩
          subst hc
          subst hargs
          exact ProcResidualEquiv.refl (.apply "PZero" [])
        · rcases hdrop with ⟨n, hc, hargs, hshapeN⟩
          subst hc
          subst hargs
          have hopaqueN : noBoundUnderQuote k n = true := by
            simpa [noBoundUnderQuote, noBoundUnderQuoteList] using hopaque
          have hname :
              NameEquiv
                (semanticSubstName k (.apply "NQuote" [q]) n)
                (rhoOpenNameBVar k (.apply "NQuote" [q]) n) :=
            semanticSubstName_equiv_rhoOpenNameBVar_of_rhoNameCoreShape k q hshapeN hopaqueN
          simpa [semanticSubstProcNoCollapse, rhoOpenNameBVar, rhoOpenNameBVarList] using
            (procResidual_apply_cong_single (ProcResidualEquiv.of_nameEquiv hname))
        · rcases houtput with ⟨n, payload, hc, hargs, hshapeN, hshapePayload⟩
          subst hc
          subst hargs
          have hopaqueSplit :
              noBoundUnderQuote k n = true ∧ noBoundUnderQuote k payload = true := by
            simpa [noBoundUnderQuote, noBoundUnderQuoteList] using hopaque
          have hname :=
            semanticSubstName_equiv_rhoOpenNameBVar_of_rhoNameCoreShape k q hshapeN hopaqueSplit.1
          have hpayload :=
            semanticSubstProcNoCollapse_residual_equiv_rhoOpenNameBVar_of_rhoProcCoreShape
              k q hshapePayload hopaqueSplit.2
          simpa [semanticSubstProcNoCollapse, rhoOpenNameBVar, rhoOpenNameBVarList] using
            (procResidual_apply_cong_two
              (ProcResidualEquiv.of_nameEquiv hname)
              hpayload)
        · rcases hinput with ⟨n, body, hc, hargs, hshapeN, hshapeBody⟩
          subst hc
          subst hargs
          have hopaqueSplit :
              noBoundUnderQuote k n = true ∧ noBoundUnderQuote (k + 1) body = true := by
            simpa [noBoundUnderQuote, noBoundUnderQuoteList] using hopaque
          have hname :=
            semanticSubstName_equiv_rhoOpenNameBVar_of_rhoNameCoreShape k q hshapeN hopaqueSplit.1
          have hbody :=
            semanticSubstProcNoCollapse_residual_equiv_rhoOpenNameBVar_of_rhoProcCoreShape
              (k + 1) q hshapeBody hopaqueSplit.2
          simpa [semanticSubstProcNoCollapse, rhoOpenNameBVar, rhoOpenNameBVarList] using
            (procResidual_apply_cong_two
              (ProcResidualEquiv.of_nameEquiv hname)
              (ProcResidualEquiv.lambda_cong none hbody))
    | .lambda nm body =>
        simp [rhoProcCoreShape] at hshape
    | .multiLambda n nms body =>
        simp [rhoProcCoreShape] at hshape
    | .subst body repl =>
        simp [rhoProcCoreShape] at hshape
    | .collection ct elems rest =>
        rcases rhoProcCoreShape_collection_inv hshape with ⟨hct, hrest, hshapeList⟩
        subst hct
        subst hrest
        have hopaqueList : noBoundUnderQuoteList k elems = true := by
          simpa [noBoundUnderQuote] using hopaque
        have hlenLeft :
            (semanticSubstProcNoCollapseList k (.apply "NQuote" [q]) elems).length =
              elems.length := semanticSubstProcNoCollapseList_length k (.apply "NQuote" [q]) elems
        have hlenRight :
            (rhoOpenNameBVarList k (.apply "NQuote" [q]) elems).length =
              elems.length := rhoOpenNameBVarList_length k (.apply "NQuote" [q]) elems
        have hlen :
            (semanticSubstProcNoCollapseList k (.apply "NQuote" [q]) elems).length =
              (rhoOpenNameBVarList k (.apply "NQuote" [q]) elems).length := by
          rw [hlenLeft, hlenRight]
        refine ProcResidualEquiv.collection_cong .hashBag
          (semanticSubstProcNoCollapseList k (.apply "NQuote" [q]) elems)
          (rhoOpenNameBVarList k (.apply "NQuote" [q]) elems)
          none hlen ?_
        intro i h₁ h₂
        simpa [semanticSubstProcNoCollapseList, rhoOpenNameBVarList] using
          semanticSubstProcNoCollapseList_residual_equiv_rhoOpenNameBVarList_of_rhoProcCoreShape
            k q elems hshapeList hopaqueList i h₁ h₂
  termination_by sizeOf p

  theorem semanticSubstProcNoCollapseList_residual_equiv_rhoOpenNameBVarList_of_rhoProcCoreShape
      (k : Nat) (q : Pattern) :
      ∀ elems : List Pattern,
        rhoProcCoreShapeList elems = true →
        noBoundUnderQuoteList k elems = true →
        ∀ i h₁ h₂,
          ProcResidualEquiv
            ((semanticSubstProcNoCollapseList k (.apply "NQuote" [q]) elems).get ⟨i, h₁⟩)
            ((rhoOpenNameBVarList k (.apply "NQuote" [q]) elems).get ⟨i, h₂⟩)
    | [], _, _, i, h₁, _ => by
        cases h₁
    | p :: ps, hshape, hopaque, 0, h₁, h₂ => by
        have hshapeSplit : rhoProcCoreShape p = true ∧ rhoProcCoreShapeList ps = true := by
          simpa [rhoProcCoreShapeList, Bool.and_eq_true] using hshape
        have hopaqueSplit : noBoundUnderQuote k p = true ∧ noBoundUnderQuoteList k ps = true := by
          simpa [noBoundUnderQuoteList, Bool.and_eq_true] using hopaque
        simpa [semanticSubstProcNoCollapseList, rhoOpenNameBVarList] using
          semanticSubstProcNoCollapse_residual_equiv_rhoOpenNameBVar_of_rhoProcCoreShape
            k q hshapeSplit.1 hopaqueSplit.1
    | p :: ps, hshape, hopaque, i + 1, h₁, h₂ => by
        have hshapeSplit : rhoProcCoreShape p = true ∧ rhoProcCoreShapeList ps = true := by
          simpa [rhoProcCoreShapeList, Bool.and_eq_true] using hshape
        have hopaqueSplit : noBoundUnderQuote k p = true ∧ noBoundUnderQuoteList k ps = true := by
          simpa [noBoundUnderQuoteList, Bool.and_eq_true] using hopaque
        have h₁' : i < (semanticSubstProcNoCollapseList k (.apply "NQuote" [q]) ps).length := by
          simpa [semanticSubstProcNoCollapseList] using h₁
        have h₂' : i < (rhoOpenNameBVarList k (.apply "NQuote" [q]) ps).length := by
          simpa [rhoOpenNameBVarList, rhoOpenNameBVarList_length k (.apply "NQuote" [q]) ps] using h₂
        simpa [semanticSubstProcNoCollapseList, rhoOpenNameBVarList] using
          semanticSubstProcNoCollapseList_residual_equiv_rhoOpenNameBVarList_of_rhoProcCoreShape
            k q ps hshapeSplit.2 hopaqueSplit.2 i h₁' h₂'
  termination_by elems => sizeOf elems
end

theorem semanticCommRepresentative_residual_equiv_rhoOpenNameBVar_of_rhoProcCoreShape
    {pBody q : Pattern}
    (hshape : rhoProcCoreShape pBody = true)
    (hopaque : noBoundUnderQuote 0 pBody = true) :
    ProcResidualEquiv
      (semanticCommRepresentative pBody q)
      (rhoOpenNameBVar 0 (.apply "NQuote" [q]) pBody) := by
  simpa [semanticCommRepresentative] using
    semanticSubstProcNoCollapse_residual_equiv_rhoOpenNameBVar_of_rhoProcCoreShape
      0 q hshape hopaque

mutual
  theorem semanticSubstProc_transport_to_representative (k : Nat) (q : Pattern) :
      ∀ p : Pattern,
        ProcResidualEquiv
          (semanticSubstProc k (.apply "NQuote" [semanticNormalizeProc q]) p)
          (semanticSubstProcNoCollapse k (.apply "NQuote" [q]) p)
      := by
    intro p
    match p with
    | .bvar n =>
        by_cases hnk : n = k
        · subst hnk
          simpa [semanticSubstProc, semanticSubstProcNoCollapse, beq_self_eq_true] using
            (ProcResidualEquiv.of_nameEquiv
              (quote_respects_structural (semanticNormalizeProc_sound q)))
        · have hbeq : (n == k) = false := beq_eq_false_iff_ne.mpr hnk
          simpa [semanticSubstProc, semanticSubstProcNoCollapse, hbeq] using
            (ProcResidualEquiv.refl (.bvar n))
    | .fvar x =>
        exact ProcResidualEquiv.refl (.fvar x)
    | .apply "NQuote" [p] =>
        exact ProcResidualEquiv.refl (.apply "NQuote" [p])
    | .apply "PDrop" [name] =>
        unfold semanticSubstProc semanticSubstProcNoCollapse
        cases hmark : semanticSubstNameMark k (.apply "NQuote" [semanticNormalizeProc q]) name with
        | mk name' matched =>
            cases matched with
            | false =>
                have hname :
                    NameEquiv name'
                      (semanticSubstName k (.apply "NQuote" [q]) name) := by
                  simpa [semanticSubstName, hmark] using
                    semanticSubstName_transport_to_representative k q name
                simpa [semanticSubstProc, semanticSubstProcNoCollapse, hmark] using
                  (procResidual_apply_cong_single (ProcResidualEquiv.of_nameEquiv hname))
            | true =>
                have hname' :
                    name' = .apply "NQuote" [semanticNormalizeProc q] := by
                  exact semanticSubstNameMark_true_eq_replacement
                    k (.apply "NQuote" [semanticNormalizeProc q]) name name' hmark
                have hname :
                    NameEquiv
                      (.apply "NQuote" [semanticNormalizeProc q])
                      (semanticSubstName k (.apply "NQuote" [q]) name) := by
                  simpa [semanticSubstName, hmark, hname'] using
                    semanticSubstName_transport_to_representative k q name
                have hleft :
                    ProcResidualEquiv
                      (semanticSubstProc k (.apply "NQuote" [semanticNormalizeProc q]) (.apply "PDrop" [name]))
                      (.apply "PDrop" [.apply "NQuote" [semanticNormalizeProc q]]) := by
                  simpa [semanticSubstProc, hmark, hname'] using
                    (ProcResidualEquiv.symm (ProcResidualEquiv.unquote (semanticNormalizeProc q)))
                have hdrop :
                    ProcResidualEquiv
                      (.apply "PDrop" [.apply "NQuote" [semanticNormalizeProc q]])
                      (.apply "PDrop" [semanticSubstName k (.apply "NQuote" [q]) name]) := by
                  exact procResidual_apply_cong_single (ProcResidualEquiv.of_nameEquiv hname)
                exact ProcResidualEquiv.trans
                  hleft
                  hdrop
    | .apply "POutput" [n, payload] =>
        simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
          (procResidual_apply_cong_two
            (ProcResidualEquiv.of_nameEquiv
              (semanticSubstName_transport_to_representative k q n))
            (semanticSubstProc_transport_to_representative k q payload))
    | .apply "PInput" [n, .lambda none body] =>
        simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
          (procResidual_apply_cong_two
            (ProcResidualEquiv.of_nameEquiv
              (semanticSubstName_transport_to_representative k q n))
            (ProcResidualEquiv.lambda_cong none
              (semanticSubstProc_transport_to_representative (k + 1) q body)))
    | .apply c args =>
        by_cases hQuote : c = "NQuote"
        · subst hQuote
          cases args with
          | nil =>
              simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                (ProcResidualEquiv.refl (.apply "NQuote" []))
          | cons a as =>
              cases as with
              | nil =>
                  simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                    (ProcResidualEquiv.refl (.apply "NQuote" [a]))
              | cons b bs =>
                  simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                    (ProcResidualEquiv.refl (.apply "NQuote" (a :: b :: bs)))
        · by_cases hDrop : c = "PDrop"
          · subst hDrop
            cases args with
            | nil =>
                simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                  (ProcResidualEquiv.refl (.apply "PDrop" []))
            | cons a as =>
                cases as with
                | nil =>
                    unfold semanticSubstProc semanticSubstProcNoCollapse
                    cases hmark : semanticSubstNameMark k (.apply "NQuote" [semanticNormalizeProc q]) a with
                    | mk name' matched =>
                        cases matched with
                        | false =>
                            have hname :
                                NameEquiv name'
                                  (semanticSubstName k (.apply "NQuote" [q]) a) := by
                              simpa [semanticSubstName, hmark] using
                                semanticSubstName_transport_to_representative k q a
                            simpa [semanticSubstProc, semanticSubstProcNoCollapse, hmark] using
                              (procResidual_apply_cong_single
                                (ProcResidualEquiv.of_nameEquiv hname))
                        | true =>
                            have hname' :
                                name' = .apply "NQuote" [semanticNormalizeProc q] := by
                              exact semanticSubstNameMark_true_eq_replacement
                                k (.apply "NQuote" [semanticNormalizeProc q]) a name' hmark
                            have hname :
                                NameEquiv
                                  (.apply "NQuote" [semanticNormalizeProc q])
                                  (semanticSubstName k (.apply "NQuote" [q]) a) := by
                              simpa [semanticSubstName, hmark, hname'] using
                                semanticSubstName_transport_to_representative k q a
                            have hleft :
                                ProcResidualEquiv
                                  (semanticSubstProc k (.apply "NQuote" [semanticNormalizeProc q]) (.apply "PDrop" [a]))
                                  (.apply "PDrop" [.apply "NQuote" [semanticNormalizeProc q]]) := by
                              simpa [semanticSubstProc, hmark, hname'] using
                                (ProcResidualEquiv.symm (ProcResidualEquiv.unquote (semanticNormalizeProc q)))
                            have hdrop :
                                ProcResidualEquiv
                                  (.apply "PDrop" [.apply "NQuote" [semanticNormalizeProc q]])
                                  (.apply "PDrop" [semanticSubstName k (.apply "NQuote" [q]) a]) := by
                              exact procResidual_apply_cong_single
                                (ProcResidualEquiv.of_nameEquiv hname)
                            exact ProcResidualEquiv.trans hleft hdrop
                | cons b bs =>
                    simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                      (ProcResidualEquiv.refl (.apply "PDrop" (a :: b :: bs)))
          · by_cases hOutput : c = "POutput"
            · subst hOutput
              cases args with
              | nil =>
                  simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                    (ProcResidualEquiv.refl (.apply "POutput" []))
              | cons a as =>
                  cases as with
                  | nil =>
                      simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                        (ProcResidualEquiv.refl (.apply "POutput" [a]))
                  | cons b bs =>
                      cases bs with
                      | nil =>
                          simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                            (procResidual_apply_cong_two
                              (ProcResidualEquiv.of_nameEquiv
                                (semanticSubstName_transport_to_representative k q a))
                              (semanticSubstProc_transport_to_representative k q b))
                      | cons c cs =>
                          simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                            (ProcResidualEquiv.refl (.apply "POutput" (a :: b :: c :: cs)))
            · by_cases hInput : c = "PInput"
              · subst hInput
                cases args with
                | nil =>
                    simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                      (ProcResidualEquiv.refl (.apply "PInput" []))
                | cons a as =>
                    cases as with
                    | nil =>
                        simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                          (ProcResidualEquiv.refl (.apply "PInput" [a]))
                    | cons b bs =>
                        cases bs with
                        | nil =>
                            cases b with
                            | bvar n =>
                                simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                                  (ProcResidualEquiv.refl (.apply "PInput" [a, .bvar n]))
                            | fvar x =>
                                simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                                  (ProcResidualEquiv.refl (.apply "PInput" [a, .fvar x]))
                            | apply c' args' =>
                                simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                                  (ProcResidualEquiv.refl (.apply "PInput" [a, .apply c' args']))
                            | lambda nm body =>
                                cases nm with
                                | none =>
                                    simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                                      (procResidual_apply_cong_two
                                        (ProcResidualEquiv.of_nameEquiv
                                          (semanticSubstName_transport_to_representative k q a))
                                        (ProcResidualEquiv.lambda_cong none
                                          (semanticSubstProc_transport_to_representative (k + 1) q body)))
                                | some nm' =>
                                    simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                                      (ProcResidualEquiv.refl (.apply "PInput" [a, .lambda (some nm') body]))
                            | multiLambda n nms body =>
                                simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                                  (ProcResidualEquiv.refl (.apply "PInput" [a, .multiLambda n nms body]))
                            | subst body repl =>
                                simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                                  (ProcResidualEquiv.refl (.apply "PInput" [a, .subst body repl]))
                            | collection ct elems rest =>
                                simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                                  (ProcResidualEquiv.refl (.apply "PInput" [a, .collection ct elems rest]))
                        | cons c cs =>
                            simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
                              (ProcResidualEquiv.refl (.apply "PInput" (a :: b :: c :: cs)))
              · simpa [semanticSubstProc, semanticSubstProcNoCollapse, hQuote, hDrop, hOutput, hInput] using
                  (ProcResidualEquiv.refl (.apply c args))
    | .lambda nm body =>
        simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
          (ProcResidualEquiv.lambda_cong nm
            (semanticSubstProc_transport_to_representative (k + 1) q body))
    | .multiLambda n nms body =>
        simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
          (ProcResidualEquiv.multiLambda_cong n nms
            (semanticSubstProc_transport_to_representative (k + n) q body))
    | .subst body repl =>
        simpa [semanticSubstProc, semanticSubstProcNoCollapse] using
          (ProcResidualEquiv.subst_cong
            (semanticSubstProc_transport_to_representative (k + 1) q body)
            (semanticSubstProc_transport_to_representative k q repl))
    | .collection ct elems rest =>
        have hlenLeft :
            (semanticSubstProcList k (.apply "NQuote" [semanticNormalizeProc q]) elems).length =
              elems.length := semanticSubstProcList_length k (.apply "NQuote" [semanticNormalizeProc q]) elems
        have hlenRight :
            (semanticSubstProcNoCollapseList k (.apply "NQuote" [q]) elems).length =
              elems.length := semanticSubstProcNoCollapseList_length k (.apply "NQuote" [q]) elems
        have hlen :
            (semanticSubstProcList k (.apply "NQuote" [semanticNormalizeProc q]) elems).length =
              (semanticSubstProcNoCollapseList k (.apply "NQuote" [q]) elems).length := by
          rw [hlenLeft, hlenRight]
        refine ProcResidualEquiv.collection_cong ct
          (semanticSubstProcList k (.apply "NQuote" [semanticNormalizeProc q]) elems)
          (semanticSubstProcNoCollapseList k (.apply "NQuote" [q]) elems)
          rest hlen ?_
        intro i h₁ h₂
        simpa [semanticSubstProcList, semanticSubstProcNoCollapseList] using
          semanticSubstProcList_transport_to_representative k q elems i h₁ h₂
  termination_by p => sizeOf p

  theorem semanticSubstProcList_transport_to_representative
      (k : Nat) (q : Pattern) :
      ∀ elems : List Pattern,
        ∀ i h₁ h₂,
          ProcResidualEquiv
            ((semanticSubstProcList k (.apply "NQuote" [semanticNormalizeProc q]) elems).get ⟨i, h₁⟩)
            ((semanticSubstProcNoCollapseList k (.apply "NQuote" [q]) elems).get ⟨i, h₂⟩)
      := by
    intro elems i h₁ h₂
    match elems with
    | [] =>
        cases h₁
    | p :: ps =>
        cases i with
        | zero =>
            simpa [semanticSubstProcList, semanticSubstProcNoCollapseList] using
              semanticSubstProc_transport_to_representative k q p
        | succ i =>
            have h₁' : i < (semanticSubstProcList k (.apply "NQuote" [semanticNormalizeProc q]) ps).length := by
              simpa [semanticSubstProcList] using h₁
            have h₂' : i < (semanticSubstProcNoCollapseList k (.apply "NQuote" [q]) ps).length := by
              simpa [semanticSubstProcNoCollapseList] using h₂
            simpa [semanticSubstProcList, semanticSubstProcNoCollapseList] using
              semanticSubstProcList_transport_to_representative k q ps i h₁' h₂'
  termination_by elems => sizeOf elems
end

theorem semanticCommSubst_transport_to_representative (pBody q : Pattern) :
    ProcResidualEquiv (semanticCommSubst pBody q) (semanticCommRepresentative pBody q) := by
  simpa [semanticCommSubst, semanticCommRepresentative] using
    semanticSubstProc_transport_to_representative 0 q pBody

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
