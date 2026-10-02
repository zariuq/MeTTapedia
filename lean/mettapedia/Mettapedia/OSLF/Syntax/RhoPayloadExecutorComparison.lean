import Mettapedia.OSLF.Syntax.RhoPayloadTranslation
import Mettapedia.OSLF.Syntax.EquationalQuotient
import Mettapedia.OSLF.Syntax.RhoAuthoredDropProfile
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
import Mettapedia.OSLF.Syntax.RhoCombinedInterpretedStep

/-!
# The authored rho executor against the payload presentation

The executor matches communication partners whose channels have the same
canonical form, and it steps inside parallel bags selected in any order.
Translated into the payload presentation, canonical forms are equal up to
the equations: the monoid laws of parallel composition and quote/drop
cancellation. Each executor step is therefore one step of the presented
calculus between equation classes, in the strict core and in the book's
profile with Drop.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoPayloadPresentation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern CollType)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
  (canonicalize canonicalizeList normalizeQuote bagSplice normalizeBagElements
    sortPatterns collapseBag bagSplice_eq_singleton_of_not_bag
    collapseBag_eq_bag_of_length_ge_two sortPatterns_perm
    normalizeQuote_eq_quote_of_not_drop)

/-! ## Canonical forms translate to equal classes -/

section Canonical

variable {Γ : Ctx sig} (ρ : Env Γ)

theorem canonicalize_quoteDrop (name : Pattern) :
    canonicalize (.apply "NQuote" [.apply "PDrop" [name]]) = canonicalize name := by
  simp [canonicalize, canonicalizeList, normalizeQuote]

theorem nameHead_canonicalize_of_some {name : Pattern} {k : Nat}
    (h : nameHead name = some k) : nameHead (canonicalize name) = some k := by
  induction name using nameHead.induct with
  | case1 j => simpa [canonicalize] using h
  | case2 m ih =>
      rw [canonicalize_quoteDrop]
      rw [nameHead.eq_2] at h
      exact ih h
  | case3 x hbvar hquoteDrop =>
      rw [nameHead.eq_3 x hbvar hquoteDrop] at h
      cases h

theorem tProcs_bagSplice {x : Pattern} {x₀ : Term sig Γ Srt.pr}
    (hx : tProc ρ x = some x₀) :
    ∃ b, tProcs ρ (bagSplice x) = some b ∧ EqClosure equations b x₀ := by
  by_cases hbag : ∃ elements, x = .collection .hashBag elements none
  · obtain ⟨elements, rfl⟩ := hbag
    rw [tProc.eq_5] at hx
    exact ⟨x₀, hx, .refl _⟩
  · rw [bagSplice_eq_singleton_of_not_bag (fun elements e => hbag ⟨elements, e⟩)]
    refine ⟨parT x₀ nilT, ?_, parT_nil x₀⟩
    rw [tProcs.eq_2, hx, Option.bind_some, tProcs.eq_1, Option.map_some]

theorem tProcs_flatMap_bagSplice {xs : List Pattern} {a : Term sig Γ Srt.pr}
    (h : tProcs ρ xs = some a) :
    ∃ b, tProcs ρ (xs.flatMap bagSplice) = some b ∧ EqClosure equations b a := by
  induction xs generalizing a with
  | nil =>
      cases h
      exact ⟨nilT, rfl, .refl _⟩
  | cons x xs ih =>
      rw [tProcs.eq_2] at h
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨head, hhead, tail, htail, rfl⟩ := h
      obtain ⟨spliced, hspliced, equivSpliced⟩ := tProcs_bagSplice ρ hhead
      obtain ⟨rest, hrest, equivRest⟩ := ih htail
      obtain ⟨c, hc, equivC⟩ := tProcs_append_of ρ hspliced hrest
      rw [List.flatMap_cons]
      exact ⟨c, hc, equivC.trans (equiv_parT equivSpliced equivRest)⟩

theorem tProcs_filter_zero {xs : List Pattern} {a : Term sig Γ Srt.pr}
    (h : tProcs ρ xs = some a) :
    ∃ b, tProcs ρ (xs.filter (fun pattern => decide (pattern ≠ .apply "PZero" []))) =
      some b ∧ EqClosure equations b a := by
  induction xs generalizing a with
  | nil =>
      cases h
      exact ⟨nilT, rfl, .refl _⟩
  | cons x xs ih =>
      rw [tProcs.eq_2] at h
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨head, hhead, tail, htail, rfl⟩ := h
      obtain ⟨b, hb, equiv⟩ := ih htail
      by_cases hzero : x = .apply "PZero" []
      · subst hzero
        rw [tProc.eq_1] at hhead
        cases hhead
        rw [List.filter_cons_of_neg (by simp)]
        exact ⟨b, hb, equiv.trans (nil_parT tail).symm⟩
      · rw [List.filter_cons_of_pos (by simpa using hzero), tProcs.eq_2, hhead,
          Option.bind_some, hb, Option.map_some]
        exact ⟨parT head b, rfl, equiv_parT (.refl head) equiv⟩

theorem tProc_collapseBag {xs : List Pattern} {a : Term sig Γ Srt.pr}
    (h : tProcs ρ xs = some a) :
    ∃ b, tProc ρ (collapseBag xs) = some b ∧ EqClosure equations b a := by
  match xs, h with
  | [], h =>
      cases h
      exact ⟨nilT, rfl, .refl _⟩
  | [x], h =>
      rw [tProcs.eq_2] at h
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨head, hhead, tail, htail, rfl⟩ := h
      cases htail
      exact ⟨head, hhead, (parT_nil head).symm⟩
  | x :: y :: rest, h =>
      refine ⟨a, ?_, .refl _⟩
      rw [collapseBag_eq_bag_of_length_ge_two (by simp), tProc.eq_5]
      exact h

/-- Normalizing a bag keeps its translation up to the monoid equations. -/
theorem tProc_collapse_normalize {xs : List Pattern} {a : Term sig Γ Srt.pr}
    (h : tProcs ρ xs = some a) :
    ∃ b, tProc ρ (collapseBag (normalizeBagElements xs)) = some b ∧
      EqClosure equations b a := by
  obtain ⟨spliced, hspliced, e₁⟩ := tProcs_flatMap_bagSplice ρ h
  obtain ⟨filtered, hfiltered, e₂⟩ := tProcs_filter_zero ρ hspliced
  obtain ⟨sorted, hsorted, e₃⟩ :=
    tProcs_perm ρ (sortPatterns_perm _) hfiltered
  obtain ⟨b, hb, e₄⟩ := tProc_collapseBag ρ hsorted
  exact ⟨b, hb, e₄.trans (e₃.symm.trans (e₂.trans e₁))⟩

/-- **Canonical forms translate to equal classes.** A translatable name keeps
the bound index it denotes, and every translatable name or process has a
translatable canonical form with an equal class. -/
theorem translate_canonicalize :
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (n : Pattern) (c : Term sig Γ Srt.nm),
      tName ρ n = some c →
        nameHead (canonicalize n) = nameHead n ∧
        ∃ c', tName ρ (canonicalize n) = some c' ∧ EqClosure equations c' c) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (p : Pattern) (t : Term sig Γ Srt.pr),
      tProc ρ p = some t →
        ∃ t', tProc ρ (canonicalize p) = some t' ∧ EqClosure equations t' t) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (ps : List Pattern) (t : Term sig Γ Srt.pr),
      tProcs ρ ps = some t →
        ∃ t', tProcs ρ (canonicalizeList ps) = some t' ∧ EqClosure equations t' t) := by
  refine tName.mutual_induct
    (fun {Γ} ρ n => ∀ c : Term sig Γ Srt.nm, tName ρ n = some c →
        nameHead (canonicalize n) = nameHead n ∧
        ∃ c', tName ρ (canonicalize n) = some c' ∧ EqClosure equations c' c)
    (fun {Γ} ρ p => ∀ t : Term sig Γ Srt.pr, tProc ρ p = some t →
        ∃ t', tProc ρ (canonicalize p) = some t' ∧ EqClosure equations t' t)
    (fun {Γ} ρ ps => ∀ t : Term sig Γ Srt.pr, tProcs ρ ps = some t →
        ∃ t', tProcs ρ (canonicalizeList ps) = some t' ∧ EqClosure equations t' t)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Γ ρ k c h
    have hcanon : canonicalize (.bvar k) = .bvar k := by simp [canonicalize]
    rw [hcanon]
    exact ⟨rfl, c, h, .refl c⟩
  · intro Γ ρ label c h
    have hcanon : canonicalize (.fvar label) = .fvar label := by simp [canonicalize]
    rw [hcanon]
    exact ⟨rfl, c, h, .refl c⟩
  · intro Γ ρ name ih c h
    rw [tName.eq_3] at h
    rw [canonicalize_quoteDrop, nameHead.eq_2]
    exact ih c h
  · intro Γ ρ code hcode ih c h
    rw [tName.eq_4 _ _ hcode] at h
    obtain ⟨code₀, hcode₀, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨code', hcode', equiv⟩ := ih code₀ hcode₀
    have hcanon : canonicalize (.apply "NQuote" [code]) =
        normalizeQuote (canonicalize code) := by
      simp [canonicalize]
    have hhead : nameHead (.apply "NQuote" [code]) = none :=
      nameHead.eq_3 _ (by simp) (fun m e => hcode m (by simpa using e))
    rw [hcanon, hhead]
    have hlift : EqClosure equations (quoT (lift0 (Γ := Γ) code'))
        (nameOf (lift0 code₀)) :=
      (equiv_quoT (eqClosure_rename (emptyRen Γ) equiv)).trans
        (nameOf_equiv (lift0 code₀)).symm
    by_cases hdrop : ∃ x, canonicalize code = .apply "PDrop" [x]
    · obtain ⟨x, hx⟩ := hdrop
      rw [hx] at hcode' ⊢
      simp only [normalizeQuote]
      rw [tProc.eq_2] at hcode'
      cases hxh : nameHead x with
      | some k => simp [hxh, Env.empty] at hcode'
      | none =>
          simp only [hxh] at hcode'
          obtain ⟨x₀, hx₀, rfl⟩ := Option.map_eq_some_iff.mp hcode'
          exact ⟨rfl, lift0 x₀, tName_closed hx₀ ρ,
            (quoteDrop_equiv (lift0 x₀)).symm.trans hlift⟩
    · have hnd : ∀ x, canonicalize code ≠ .apply "PDrop" [x] := fun x e => hdrop ⟨x, e⟩
      rw [normalizeQuote_eq_quote_of_not_drop hnd]
      refine ⟨nameHead.eq_3 _ (by simp) (fun m e => hnd m (by simpa using e)), ?_⟩
      rw [tName.eq_4 _ _ (fun m e => hnd m e), hcode', Option.map_some]
      exact ⟨_, rfl, (nameOf_equiv _).trans hlift⟩
  · intro x Γ ρ hbvar hfvar hquoteDrop hquote c h
    rw [tName.eq_5 _ _ hbvar hfvar hquoteDrop hquote] at h
    cases h
  · intro Γ ρ t h
    have hcanon : canonicalize (.apply "PZero" []) = .apply "PZero" [] := by
      simp [canonicalize, canonicalizeList]
    rw [hcanon]
    exact ⟨t, h, .refl t⟩
  · intro Γ ρ name k hk t h
    have hcanon : canonicalize (.apply "PDrop" [name]) =
        .apply "PDrop" [canonicalize name] := by
      simp [canonicalize, canonicalizeList]
    rw [hcanon, tProc.eq_2, nameHead_canonicalize_of_some hk]
    simp only [tProc.eq_2, hk] at h
    exact ⟨t, h, .refl t⟩
  · intro Γ ρ name hk ih t h
    have hcanon : canonicalize (.apply "PDrop" [name]) =
        .apply "PDrop" [canonicalize name] := by
      simp [canonicalize, canonicalizeList]
    simp only [tProc.eq_2, hk] at h
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hhead, m', hm', equiv⟩ := ih m hm
    rw [hcanon, tProc.eq_2, hhead, hk]
    simp only [hm', Option.map_some]
    exact ⟨_, rfl, equiv_drpT equiv⟩
  · intro Γ ρ name payload ihn ihp t h
    have hcanon : canonicalize (.apply "POutput" [name, payload]) =
        .apply "POutput" [canonicalize name, canonicalize payload] := by
      simp [canonicalize, canonicalizeList]
    rw [tProc.eq_3] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, process, hprocess, rfl⟩ := h
    obtain ⟨-, c', hc', equivc⟩ := ihn c hc
    obtain ⟨process', hprocess', equivp⟩ := ihp process hprocess
    rw [hcanon, tProc.eq_3, hc', Option.bind_some, hprocess', Option.map_some]
    exact ⟨_, rfl, equiv_outT equivc equivp⟩
  · intro Γ ρ name body ihn ihb t h
    have hcanon : canonicalize (.apply "PInput" [name, .lambda none body]) =
        .apply "PInput" [canonicalize name, .lambda none (canonicalize body)] := by
      simp [canonicalize, canonicalizeList]
    rw [tProc.eq_4] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, continuation, hcontinuation, rfl⟩ := h
    obtain ⟨-, c', hc', equivc⟩ := ihn c hc
    obtain ⟨continuation', hcontinuation', equivK⟩ := ihb continuation hcontinuation
    rw [hcanon, tProc.eq_4, hc', Option.bind_some, hcontinuation', Option.map_some]
    exact ⟨_, rfl, equiv_inpT equivc equivK⟩
  · intro Γ ρ elements ih t h
    have hcanon : canonicalize (.collection .hashBag elements none) =
        collapseBag (normalizeBagElements (canonicalizeList elements)) := by
      simp [canonicalize]
    rw [tProc.eq_5] at h
    obtain ⟨t', ht', equiv⟩ := ih t h
    rw [hcanon]
    obtain ⟨u, hu, equ⟩ := tProc_collapse_normalize ρ ht'
    exact ⟨u, hu, equ.trans equiv⟩
  · intro x Γ ρ hzero hdrop hout hinp hbag t h
    rw [tProc.eq_6 _ _ hzero hdrop hout hinp hbag] at h
    cases h
  · intro Γ ρ t h
    exact ⟨t, h, .refl t⟩
  · intro Γ ρ process rest ihp ihr t h
    rw [tProcs.eq_2] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    obtain ⟨head', hhead', equivh⟩ := ihp head hhead
    obtain ⟨tail', htail', equivt⟩ := ihr tail htail
    refine ⟨parT head' tail', ?_, equiv_parT equivh equivt⟩
    simp only [canonicalizeList, tProcs.eq_2, hhead', Option.bind_some, htail',
      Option.map_some]

/-- Names with one canonical form translate to one class. -/
theorem tName_equiv_of_canonicalize_eq {n m : Pattern} {c d : Term sig Γ Srt.nm}
    (hn : tName ρ n = some c) (hm : tName ρ m = some d)
    (same : canonicalize n = canonicalize m) : EqClosure equations c d := by
  obtain ⟨-, c', hc', ec⟩ := translate_canonicalize.1 ρ n c hn
  obtain ⟨-, d', hd', ed⟩ := translate_canonicalize.1 ρ m d hm
  rw [same, hd'] at hc'
  cases hc'
  exact ec.symm.trans ed

end Canonical

/-! ## Inverting the authored executor -/

section Executor

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
open Mettapedia.OSLF.Binding.RhoSchema.Authored
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial (Rule)

/-- An executed COMM selects an input and an output on channels with one
canonical form, and continues with the executor's semantic substitution. -/
theorem commApplication {free : FreeSortContext} {bound : List String}
    {source target : Pattern} {initial : Bindings}
    (sourceTyped : ProcWellSorted rhoReflectivePresentation free bound source)
    (matched : initial ∈ matchPatternForRuleUsing rhoReflectionProfile rhoCommRewrite source)
    (targetEq : applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite initial = target) :
    ∃ (elements : List Pattern) (inputIndex : Nat) (inputBound : inputIndex < elements.length)
      (outputIndex : Nat) (outputBound : outputIndex < (elements.eraseIdx inputIndex).length)
      (inputChannel outputChannel body payload : Pattern),
      source = .collection .hashBag elements none ∧
      elements[inputIndex] = .apply "PInput" [inputChannel, .lambda none body] ∧
      (elements.eraseIdx inputIndex)[outputIndex] = .apply "POutput" [outputChannel, payload] ∧
      canonicalize inputChannel = canonicalize outputChannel ∧
      target = .collection .hashBag (semanticCommSubst body payload ::
        (elements.eraseIdx inputIndex).eraseIdx outputIndex) none := by
  obtain ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound,
    inputChannel, body, inputBinder, outputChannel, payload, sourceEq,
    inputEq, outputEq, channelsEquivalent, bindingsEq⟩ :=
      rhoComm_match_shape matched
  subst source
  subst initial
  cases sourceTyped
  rename_i elementsTyped
  have inputTyped := elementsTyped.getElem inputIndex inputBound
  rw [inputEq] at inputTyped
  obtain ⟨rfl, _, bodyTyped⟩ := rho_input_wellSorted_inv inputTyped
  have outputTyped :=
    (elementsTyped.eraseIdx inputIndex).getElem outputIndex outputBound
  rw [outputEq] at outputTyped
  obtain ⟨_, payloadTyped⟩ := rho_output_wellSorted_inv outputTyped
  rw [rhoCanonicalEquivalent, canonicalEquivalent_eq_true_iff,
    derivedCanonicalize_eq, derivedCanonicalize_eq] at channelsEquivalent
  refine ⟨elements, inputIndex, inputBound, outputIndex, outputBound, inputChannel,
    outputChannel, body, payload, rfl, inputEq, outputEq, channelsEquivalent, ?_⟩
  let residue := (elements.eraseIdx inputIndex).eraseIdx outputIndex
  have compiledAgreement :=
    LanguageDefAdequacy.applyBindingsForRule_rhoComm_agrees_derived
      bodyTyped payloadTyped inputChannel residue
  rw [← targetEq]
  have reordered :
      applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
          [("q", payload),
           ("rest", .collection .hashBag
             ((elements.eraseIdx inputIndex).eraseIdx outputIndex) none),
           ("p", body), ("n", inputChannel)] =
        applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
          (LanguageDefAdequacy.rhoCommBindings inputChannel body payload residue) := by
    simp only [applyBindingsForRuleUsing,
      LanguageDefAdequacy.rhoComm_substitutionPresentation_selected]
    simp [LanguageDefAdequacy.rhoCommBindings, residue,
      applyBindingsReflective, applyBindingsReflectiveList, rhoCommRewrite]
  rw [reordered]
  exact compiledAgreement

private theorem drop_no_matchingPresentation :
    matchingPresentationForRule? rhoReflectionProfile rhoDropRewrite = none := by
  decide +kernel

private theorem drop_no_substitutionPresentation :
    substitutionPresentationForRule? rhoReflectionProfile rhoDropRewrite = none := by
  decide +kernel

/-- An executed Drop consumes a dropped quotation and returns its code. -/
theorem dropApplication {source target : Pattern} {initial : Bindings}
    (matched : initial ∈ matchPatternForRuleUsing rhoReflectionProfile rhoDropRewrite source)
    (targetEq : applyBindingsForRuleUsing rhoReflectionProfile rhoDropRewrite initial = target) :
    ∃ code, source = .apply "PDrop" [.apply "NQuote" [code]] ∧ target = code := by
  rw [matchPatternForRuleUsing_iff_matchRel_of_no_presentation
    drop_no_matchingPresentation] at matched
  change MatchRel (.apply "PDrop" [.apply "NQuote" [.fvar "P"]]) source initial at matched
  cases matched
  rename_i arguments argumentsLength argumentsMatch
  clear argumentsLength
  cases argumentsMatch
  rename_i quoted quotedBindings rest restBindings quotedMatch restMatch merged
  cases restMatch
  cases quotedMatch
  rename_i codes codesLength codesMatch
  clear codesLength
  cases codesMatch
  rename_i code codeBindings codeRest codeRestBindings codeMatch codeRestMatch codeMerged
  cases codeRestMatch
  cases codeMatch
  simp [mergeBindings] at codeMerged merged
  subst codeMerged
  subst merged
  refine ⟨code, rfl, ?_⟩
  rw [← targetEq, applyBindingsForRuleUsing, drop_no_substitutionPresentation]
  simp [rhoDropRewrite, applyRuleBindings, applyBindings]

variable {Γ : Ctx sig} {ρ : Env Γ}

theorem tProc_input_inv {name body : Pattern} {t : Term sig Γ Srt.pr}
    (h : tProc ρ (.apply "PInput" [name, .lambda none body]) = some t) :
    ∃ c K, tName ρ name = some c ∧ tProc ρ.up body = some K ∧ t = inpT c K := by
  rw [tProc.eq_4] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨c, hc, K, hK, rfl⟩ := h
  exact ⟨c, K, hc, hK, rfl⟩

theorem tProc_output_inv {name payload : Pattern} {t : Term sig Γ Srt.pr}
    (h : tProc ρ (.apply "POutput" [name, payload]) = some t) :
    ∃ c q, tName ρ name = some c ∧ tProc ρ payload = some q ∧ t = outT c q := by
  rw [tProc.eq_3] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨c, hc, q, hq, rfl⟩ := h
  exact ⟨c, q, hc, hq, rfl⟩

/-- A closed drop of a quotation is, up to the name equation, the drop of
the quoted code. -/
theorem tProc_dropQuote {code : Pattern} {s : Term sig [] Srt.pr}
    (h : tProc (Env.empty []) (.apply "PDrop" [.apply "NQuote" [code]]) = some s) :
    ∃ code₀, tProc (Env.empty []) code = some code₀ ∧
      EqClosure equations s (drpT (quoT code₀)) := by
  rw [tProc.eq_2] at h
  by_cases hdrop : ∃ n, code = .apply "PDrop" [n]
  · obtain ⟨n, rfl⟩ := hdrop
    rw [nameHead.eq_2] at h
    cases hn : nameHead n with
    | some k => simp [hn, Env.empty] at h
    | none =>
        simp only [hn, tName.eq_3] at h
        obtain ⟨n₀, hn₀, rfl⟩ := Option.map_eq_some_iff.mp h
        refine ⟨drpT n₀, ?_, equiv_drpT (quoteDrop_equiv n₀).symm⟩
        rw [tProc.eq_2, hn]
        simp only [hn₀, Option.map_some]
  · have hnot : ∀ n, code = .apply "PDrop" [n] → False := fun n e => hdrop ⟨n, e⟩
    have hhead : nameHead (.apply "NQuote" [code]) = none :=
      nameHead.eq_3 _ (by simp) (fun m e => hnot m (by simpa using e))
    simp only [hhead, tName.eq_4 _ _ hnot] at h
    obtain ⟨name, hname, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨code₀, hcode₀, rfl⟩ := Option.map_eq_some_iff.mp hname
    refine ⟨code₀, hcode₀, ?_⟩
    rw [lift0_nil]
    exact equiv_drpT (nameOf_equiv code₀)

/-- **One executor step is one step of the presented calculus.** A step of
the authored executor for a rule list of COMM, ParCong and possibly Drop,
from a well-sorted closed process in the translated fragment, reaches a
translated process, and the two translations are related by one firing
tree of the presented calculus between their equation classes. -/
theorem simulation (language : LanguageDef) (rest : List (Rule sig metas))
    (hrules : ∀ rule ∈ language.rewrites,
      rule = rhoCommRewrite ∨ rule = rhoParCongRewrite ∨ rule = rhoDropRewrite)
    (hdrop : rhoDropRewrite ∈ language.rewrites →
      ∀ code : Term sig [] Srt.pr, Steps (comm :: parCong :: rest) (drpT (quoT code)) code)
    {free : FreeSortContext} {bound : List String} :
    ∀ (fuel : Nat) {source target : Pattern},
      ProcWellSorted rhoReflectivePresentation free bound source →
      StepAt rhoRuleInterpretation rhoBasePremises language fuel source target →
      ∀ s₀, tProc (Env.empty []) source = some s₀ →
        ∃ t₀, tProc (Env.empty []) target = some t₀ ∧
          Steps (comm :: parCong :: rest) s₀ t₀ := by
  intro fuel
  induction fuel with
  | zero =>
      intro source target _ step
      cases step
  | succ fuel ih =>
      intro source target sourceTyped step s₀ hs
      cases step
      rename_i rule initial final ruleMember premises matched targetEq
      rcases hrules rule ruleMember with rfl | rfl | rfl
      · change PremisesAt rhoRuleInterpretation rhoBasePremises language fuel initial []
          final at premises
        cases premises
        obtain ⟨elements, i, hi, j, hj, inputChannel, outputChannel, body, payload,
          rfl, hinput, houtput, hsame, rfl⟩ := commApplication sourceTyped matched targetEq
        rw [tProc.eq_5] at hs
        obtain ⟨I, R₁, hI, hR₁, e₁⟩ := tProcs_select _ hs i hi
        obtain ⟨O, R₂, hO, hR₂, e₂⟩ := tProcs_select _ hR₁ j hj
        rw [hinput] at hI
        rw [houtput] at hO
        obtain ⟨cI, K, hcI, hK, rfl⟩ := tProc_input_inv hI
        obtain ⟨cO, q₀, hcO, hq₀, rfl⟩ := tProc_output_inv hO
        have channels : EqClosure equations cO cI :=
          tName_equiv_of_canonicalize_eq _ hcO hcI hsame.symm
        obtain ⟨T, hT, eT⟩ := translate_semanticCommSubst hK hq₀
        refine ⟨parT T R₂, ?_, ?_⟩
        · rw [tProc.eq_5, tProcs.eq_2, hT, Option.bind_some, hR₂, Option.map_some]
        · refine steps_of_equiv ?_ (equiv_parT eT.symm (.refl R₂))
            (steps_parCong rest R₂ (steps_comm rest cI q₀ K))
          refine e₁.trans ((equiv_parT (.refl _) e₂).trans ?_)
          refine (equiv_parT (.refl _) (equiv_parT (equiv_outT channels (.refl q₀))
            (.refl R₂))).trans ?_
          exact (parT_assoc _ _ _).symm.trans
            (equiv_parT (parT_comm _ _) (.refl R₂))
      · obtain ⟨elements, termRest, index, hindex, selected, rfl, hselected, rfl⟩ :=
          rhoParCong_match_shape matched
        cases sourceTyped
        rename_i elementsTyped
        have selectedTyped := elementsTyped.getElem index hindex
        rw [hselected] at selectedTyped
        change PremisesAt rhoRuleInterpretation rhoBasePremises language fuel
          [("rest", .collection .hashBag (elements.eraseIdx index) none),
           ("S", selected)]
          [.congruence (.fvar "S") (.fvar "T")] final at premises
        cases premises
        rename_i middle firstPremise remainingPremises
        cases remainingPremises
        cases firstPremise
        rename_i premiseBindings candidate recursiveStep targetMatch merged
        simp [matchPattern] at targetMatch
        subst premiseBindings
        simp [mergeBindings] at merged
        subst final
        have innerStep : StepAt rhoRuleInterpretation rhoBasePremises language fuel
            selected candidate := by
          simpa [applyBindings, Bindings.lookup] using recursiveStep
        have targetShape :
            target = .collection .hashBag (candidate :: elements.eraseIdx index) none := by
          rw [← targetEq]
          change applyBindingsForRuleUsing rhoReflectionProfile rhoParCongRewrite _ = _
          simp only [applyBindingsForRuleUsing, rhoParCong_no_substitutionPresentation,
            applyRuleBindings, applyBindingsScoped_zero_of_binderFree _ _ _
              (by decide : binderFree rhoParCongRewrite.right = true)]
          simp [rhoParCongRewrite, applyBindings]
        subst targetShape
        rw [tProc.eq_5] at hs
        obtain ⟨S, R, hS, hR, e⟩ := tProcs_select _ hs index hindex
        rw [hselected] at hS
        obtain ⟨C, hC, stepC⟩ := ih selectedTyped innerStep S hS
        refine ⟨parT C R, ?_, steps_of_equiv e (.refl _) (steps_parCong rest R stepC)⟩
        rw [tProc.eq_5, tProcs.eq_2, hC, Option.bind_some, hR, Option.map_some]
      · change PremisesAt rhoRuleInterpretation rhoBasePremises language fuel initial []
          final at premises
        cases premises
        obtain ⟨code, rfl, rfl⟩ := dropApplication matched targetEq
        obtain ⟨code₀, hcode₀, e⟩ := tProc_dropQuote hs
        exact ⟨code₀, hcode₀, steps_of_equiv e (.refl _) (hdrop ruleMember code₀)⟩

/-- The strict core: every authored COMM/ParCong step is one presented step. -/
theorem rhoStep_simulation {free : FreeSortContext} {bound : List String}
    {source target : Pattern}
    (sourceTyped : ProcWellSorted rhoReflectivePresentation free bound source)
    (step : RhoStep source target) {s₀ : Term sig [] Srt.pr}
    (hs : tProc (Env.empty []) source = some s₀) :
    ∃ t₀, tProc (Env.empty []) target = some t₀ ∧ Steps strictRules s₀ t₀ := by
  obtain ⟨fuel, step⟩ := step
  refine simulation rhoCalc [] ?_ ?_ fuel sourceTyped step s₀ hs
  · intro rule member
    simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
  · intro member
    simp [rhoCalc, rhoDropRewrite, rhoCommRewrite, rhoParCongRewrite] at member

/-- The book's profile: every authored COMM/ParCong/Drop step is one
presented step. -/
theorem rhoStepWithDrop_simulation {free : FreeSortContext} {bound : List String}
    {source target : Pattern}
    (sourceTyped : ProcWellSorted rhoReflectivePresentation free bound source)
    (step : RhoCombinedInterpretedStep.RhoStepWithDrop source target)
    {s₀ : Term sig [] Srt.pr} (hs : tProc (Env.empty []) source = some s₀) :
    ∃ t₀, tProc (Env.empty []) target = some t₀ ∧ Steps bookRules s₀ t₀ := by
  obtain ⟨fuel, step⟩ := step
  refine simulation rhoCalcWithDrop [drop] ?_ (fun _ code => steps_drop code)
    fuel sourceTyped step s₀ hs
  intro rule member
  simp only [rhoCalcWithDrop, rhoCalc, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

end Executor

/-! ## Coverage of the admitted source

The executor admits a process when it is well sorted and its literal quotes
mention no enclosing bound index. Every such process without free process
variables translates. The translation also accepts `@*x` for a bound `x`, a
whole name the admission check rejects and the executor treats as the bound
name. -/

section Coverage

open Mettapedia.OSLF.MeTTaIL.Syntax (rhoReflectivePresentation)
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern

private theorem safe_quote {d : Nat} {code : Pattern}
    (safe : binderSafeAt "NQuote" d (.apply "NQuote" [code]) = true) :
    binderSafeAt "NQuote" 0 code = true := by
  simpa [binderSafeAt] using safe

private theorem safe_drop {d : Nat} {name : Pattern}
    (safe : binderSafeAt "NQuote" d (.apply "PDrop" [name]) = true) :
    binderSafeAt "NQuote" d name = true := by
  simpa [binderSafeAt, binderSafeListAt] using safe

private theorem safe_output {d : Nat} {name payload : Pattern}
    (safe : binderSafeAt "NQuote" d (.apply "POutput" [name, payload]) = true) :
    binderSafeAt "NQuote" d name = true ∧ binderSafeAt "NQuote" d payload = true := by
  simpa [binderSafeAt, binderSafeListAt] using safe

private theorem safe_input {d : Nat} {name body : Pattern}
    (safe : binderSafeAt "NQuote" d (.apply "PInput" [name, .lambda none body]) = true) :
    binderSafeAt "NQuote" d name = true ∧ binderSafeAt "NQuote" (d + 1) body = true := by
  simpa [binderSafeAt, binderSafeListAt] using safe

/-- The bound index a safe name denotes is within the safe depth; a quoted
drop cannot reach an enclosing binder. -/
theorem nameHead_lt_of_safe {name : Pattern} {k : Nat} (h : nameHead name = some k) :
    ∀ {d : Nat}, binderSafeAt "NQuote" d name = true → k < d := by
  induction name using nameHead.induct with
  | case1 j =>
      intro d safe
      simp only [nameHead, Option.some.injEq] at h
      subst h
      simpa [binderSafeAt] using safe
  | case2 m ih =>
      intro d safe
      rw [nameHead.eq_2] at h
      have inner : binderSafeAt "NQuote" 0 m = true := safe_drop (safe_quote safe)
      exact absurd (ih h inner) (Nat.not_lt_zero _)
  | case3 x hbvar hquoteDrop =>
      rw [nameHead.eq_3 x hbvar hquoteDrop] at h
      cases h

/-- **Coverage.** A well-sorted process whose literal quotes are closed, with
no process variables, translates in every environment that supplies the
bound indices below its safe depth. -/
theorem translate_covers {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {bound : List String} {p : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free bound p) :
    (∀ i : Nat, bound[i]? ≠ some rhoReflectivePresentation.processSort) →
      ∀ (d : Nat) {Γ : Ctx sig} (ρ : Env Γ), (∀ k, k < d → ∃ t, ρ k = some t) →
        binderSafeAt "NQuote" d p = true → ∃ t, tProc ρ p = some t := by
  refine ProcWellSorted.rec
    (motive_1 := fun bound n _ =>
      (∀ i : Nat, bound[i]? ≠ some rhoReflectivePresentation.processSort) →
      ∀ (d : Nat) {Γ : Ctx sig} (ρ : Env Γ), (∀ k, k < d → ∃ t, ρ k = some t) →
        binderSafeAt "NQuote" d n = true → ∃ c, tName ρ n = some c)
    (motive_2 := fun bound p _ =>
      (∀ i : Nat, bound[i]? ≠ some rhoReflectivePresentation.processSort) →
      ∀ (d : Nat) {Γ : Ctx sig} (ρ : Env Γ), (∀ k, k < d → ∃ t, ρ k = some t) →
        binderSafeAt "NQuote" d p = true → ∃ t, tProc ρ p = some t)
    (motive_3 := fun bound ps _ =>
      (∀ i : Nat, bound[i]? ≠ some rhoReflectivePresentation.processSort) →
      ∀ (d : Nat) {Γ : Ctx sig} (ρ : Env Γ), (∀ k, k < d → ∃ t, ρ k = some t) →
        binderSafeListAt "NQuote" d ps = true → ∃ t, tProcs ρ ps = some t)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · intro bound index _ _ d Γ ρ hρ safe
    have hlt : index < d := by simpa [binderSafeAt] using safe
    obtain ⟨t, ht⟩ := hρ index hlt
    exact ⟨nameOf t, by rw [tName.eq_1, ht, Option.map_some]⟩
  · intro bound name _ _ d Γ ρ _ _
    exact ⟨freeT name, tName.eq_2 ρ name⟩
  · intro bound process _ ih hb d Γ ρ _ safe
    change binderSafeAt "NQuote" d (.apply "NQuote" [process]) = true at safe
    show ∃ c, tName ρ (.apply "NQuote" [process]) = some c
    have safe0 := safe_quote safe
    obtain ⟨code₀, hcode₀⟩ := ih hb 0 (Env.empty []) (fun k hk => absurd hk (Nat.not_lt_zero k))
      safe0
    by_cases hdrop : ∃ m, process = .apply "PDrop" [m]
    · obtain ⟨m, rfl⟩ := hdrop
      rw [tName.eq_3]
      rw [tProc.eq_2] at hcode₀
      cases hm : nameHead m with
      | some k => simp [hm, Env.empty] at hcode₀
      | none =>
          simp only [hm] at hcode₀
          obtain ⟨m₀, hm₀, _⟩ := Option.map_eq_some_iff.mp hcode₀
          exact ⟨lift0 m₀, tName_closed hm₀ ρ⟩
    · have hnot : ∀ m, process = .apply "PDrop" [m] → False := fun m e => hdrop ⟨m, e⟩
      exact ⟨nameOf (lift0 code₀), by rw [tName.eq_4 _ _ hnot, hcode₀, Option.map_some]⟩
  · intro bound index lookup hb
    exact absurd lookup (hb index)
  · intro bound name lookup _
    exact absurd lookup (hfree name)
  · intro bound _ d Γ ρ _ _
    exact ⟨nilT, tProc.eq_1 ρ⟩
  · intro bound name _ ih hb d Γ ρ hρ safe
    change binderSafeAt "NQuote" d (.apply "PDrop" [name]) = true at safe
    show ∃ t, tProc ρ (.apply "PDrop" [name]) = some t
    rw [tProc.eq_2]
    cases hk : nameHead name with
    | some k =>
        exact hρ k (nameHead_lt_of_safe hk (safe_drop safe))
    | none =>
        obtain ⟨c, hc⟩ := ih hb d ρ hρ (safe_drop safe)
        exact ⟨drpT c, by simp only [hc, Option.map_some]⟩
  · intro bound channel payload _ _ ihc ihp hb d Γ ρ hρ safe
    change binderSafeAt "NQuote" d (.apply "POutput" [channel, payload]) = true at safe
    show ∃ t, tProc ρ (.apply "POutput" [channel, payload]) = some t
    obtain ⟨safec, safep⟩ := safe_output safe
    obtain ⟨c, hc⟩ := ihc hb d ρ hρ safec
    obtain ⟨q, hq⟩ := ihp hb d ρ hρ safep
    exact ⟨outT c q, by rw [tProc.eq_3, hc, Option.bind_some, hq, Option.map_some]⟩
  · intro bound channel body _ _ ihc ihb hb d Γ ρ hρ safe
    change binderSafeAt "NQuote" d (.apply "PInput" [channel, .lambda none body]) = true at safe
    show ∃ t, tProc ρ (.apply "PInput" [channel, .lambda none body]) = some t
    obtain ⟨safec, safeb⟩ := safe_input safe
    obtain ⟨c, hc⟩ := ihc hb d ρ hρ safec
    have hb' : ∀ i : Nat, (rhoReflectivePresentation.nameSort :: bound)[i]? ≠
        some rhoReflectivePresentation.processSort := by
      intro i
      cases i with
      | zero => simp [rhoReflectivePresentation]
      | succ i => simpa using hb i
    have hρ' : ∀ k, k < d + 1 → ∃ t, ρ.up k = some t := by
      intro k hk
      cases k with
      | zero => exact ⟨.var .zero, rfl⟩
      | succ k =>
          obtain ⟨t, ht⟩ := hρ k (by omega)
          exact ⟨weaken t, by simp [Env.up, ht]⟩
    obtain ⟨K, hK⟩ := ihb hb' (d + 1) ρ.up hρ' safeb
    exact ⟨inpT c K, by rw [tProc.eq_4, hc, Option.bind_some, hK, Option.map_some]⟩
  · intro bound processes _ ih hb d Γ ρ hρ safe
    have safeList : binderSafeListAt "NQuote" d processes = true := by
      simpa [binderSafeAt] using safe
    obtain ⟨t, ht⟩ := ih hb d ρ hρ safeList
    exact ⟨t, by rw [show rhoReflectivePresentation.parallelCollection = .hashBag from rfl,
      tProc.eq_5]; exact ht⟩
  · intro bound _ d Γ ρ _ _
    exact ⟨nilT, rfl⟩
  · intro bound process processes _ _ ihp ihs hb d Γ ρ hρ safe
    simp only [binderSafeListAt, Bool.and_eq_true] at safe
    obtain ⟨head, hhead⟩ := ihp hb d ρ hρ safe.1
    obtain ⟨tail, htail⟩ := ihs hb d ρ hρ safe.2
    exact ⟨parT head tail, by rw [tProcs.eq_2, hhead, Option.bind_some, htail,
      Option.map_some]⟩

/-- Every closed admitted process translates. -/
theorem closed_admitted_translates {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort) {p : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] p)
    (safe : binderSafe "NQuote" p = true) :
    ∃ t, tProc (Env.empty []) p = some t :=
  translate_covers hfree typed (fun i => by simp) 0 (Env.empty [])
    (fun k hk => absurd hk (Nat.not_lt_zero k)) safe

/-- The whole name `@*x` of a bound `x` is outside admission but inside the
translation, where it is the received name. -/
theorem bound_quoteDrop_translated_not_admitted :
    binderSafeAt "NQuote" 1 (.apply "NQuote" [.apply "PDrop" [.bvar 0]]) = false ∧
      tName (Env.empty []).up (.apply "NQuote" [.apply "PDrop" [.bvar 0]]) =
        some (quoT (.var .zero)) := by
  refine ⟨by decide, rfl⟩

end Coverage

/-! ## Reading target terms back as source patterns

A target term reads back as an authored pattern: a process variable is the
drop of its bound name, a name variable is its bound name. Equal classes read
back to structurally congruent patterns, and a translated pattern reads back
to itself up to structural congruence. -/

section Readback

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence

/-- The de Bruijn index of a variable. -/
def varIndex {Γ : Ctx sig} {s : Srt} : Var Γ s → Nat
  | .zero => 0
  | .succ v => varIndex v + 1

/-- The authored pattern of a target term. -/
def readback {Γ : Ctx sig} : {s : Srt} → Term sig Γ s → Pattern
  | Srt.pr, .var v => .apply "PDrop" [.bvar (varIndex v)]
  | Srt.nm, .var v => .bvar (varIndex v)
  | _, .op Op.nil _ => .apply "PZero" []
  | _, .op Op.par (.cons a (.cons b .nil)) =>
      .collection .hashBag [readback a, readback b] none
  | _, .op Op.out (.cons c (.cons x .nil)) => .apply "POutput" [readback c, readback x]
  | _, .op Op.inp (.cons c (.cons K .nil)) =>
      .apply "PInput" [readback c, .lambda none (readback K)]
  | _, .op Op.drp (.cons n .nil) => .apply "PDrop" [readback n]
  | _, .op Op.quo (.cons p .nil) => .apply "NQuote" [readback p]
  | _, .op (Op.free label) _ => .fvar label

theorem sc_apply1 (f : String) {a b : Pattern} (h : StructuralCongruence a b) :
    StructuralCongruence (.apply f [a]) (.apply f [b]) := by
  refine StructuralCongruence.apply_cong f [a] [b] rfl ?_
  intro i h₁ _
  have : i = 0 := by simpa using h₁
  subst this
  simpa using h

theorem sc_apply2 (f : String) {a b c d : Pattern} (h₁ : StructuralCongruence a c)
    (h₂ : StructuralCongruence b d) :
    StructuralCongruence (.apply f [a, b]) (.apply f [c, d]) := by
  refine StructuralCongruence.apply_cong f [a, b] [c, d] rfl ?_
  intro i hi _
  have : i = 0 ∨ i = 1 := by simp at hi; omega
  rcases this with rfl | rfl
  · simpa using h₁
  · simpa using h₂

theorem sc_bag2 {a b c d : Pattern} (h₁ : StructuralCongruence a c)
    (h₂ : StructuralCongruence b d) :
    StructuralCongruence (.collection .hashBag [a, b] none)
      (.collection .hashBag [c, d] none) := by
  refine StructuralCongruence.par_cong [a, b] [c, d] rfl ?_
  intro i hi _
  have : i = 0 ∨ i = 1 := by simp at hi; omega
  rcases this with rfl | rfl
  · simpa using h₁
  · simpa using h₂

/-- Pointwise structural congruence of read-back arguments. -/
def ArgsSC {Γ : Ctx sig} :
    {ars : List (List Srt × Srt)} → Args sig ars Γ → Args sig ars Γ → Prop
  | _, .nil, .nil => True
  | _, .cons h t, .cons h' t' =>
      StructuralCongruence (readback h) (readback h') ∧ ArgsSC t t'

/-- **Equal classes read back to structurally congruent patterns.** -/
theorem readback_sc {Γ : Ctx sig} {s : Srt} {t u : Term sig Γ s}
    (h : EqClosure equations t u) : StructuralCongruence (readback t) (readback u) := by
  refine EqClosure.rec
    (motive_1 := fun t u _ => StructuralCongruence (readback t) (readback u))
    (motive_2 := fun as as' _ => ArgsSC as as')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro i Θ Γ body ambient close
    fin_cases i
    · exact StructuralCongruence.par_comm _ _
    · exact StructuralCongruence.par_assoc _ _ _
    · exact StructuralCongruence.par_nil_right _
    · exact StructuralCongruence.quote_drop _
  · intro Γ s t
    exact .refl _
  · intro Γ s t u _ ih
    exact .symm _ _ ih
  · intro Γ s t u v _ _ ih₁ ih₂
    exact .trans _ _ _ ih₁ ih₂
  · intro Γ s o as as' _ ih
    cases o with
    | nil => exact .refl _
    | free label => exact .refl _
    | par =>
        match as, as', ih with
        | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
            exact sc_bag2 ha hb
    | out =>
        match as, as', ih with
        | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
            exact sc_apply2 _ ha hb
    | inp =>
        match as, as', ih with
        | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
            exact sc_apply2 _ ha (StructuralCongruence.lambda_cong _ _ _ hb)
    | drp =>
        match as, as', ih with
        | .cons a .nil, .cons a' .nil, ⟨ha, _⟩ => exact sc_apply1 _ ha
    | quo =>
        match as, as', ih with
        | .cons a .nil, .cons a' .nil, ⟨ha, _⟩ => exact sc_apply1 _ ha
  · intro Γ
    trivial
  · intro bs s ars Γ h h' t t' _ _ ihh iht
    exact ⟨ihh, iht⟩

/-- Renaming that keeps indices keeps the read-back pattern. -/
theorem readback_rename {Δ Δ' : Ctx sig} (r : Ren sig Δ Δ')
    (hr : ∀ s (v : Var Δ s), varIndex (r s v) = varIndex v) :
    ∀ {s : Srt} (t : Term sig Δ s), readback (rename r t) = readback t
  | Srt.pr, .var v => by
      change Pattern.apply "PDrop" [.bvar (varIndex (r _ v))] = _
      rw [hr]
      rfl
  | Srt.nm, .var v => by
      change Pattern.bvar (varIndex (r _ v)) = _
      rw [hr]
      rfl
  | _, .op Op.nil _ => rfl
  | _, .op (Op.free _) _ => rfl
  | _, .op Op.par (.cons a (.cons b .nil)) => by
      change Pattern.collection .hashBag [readback (rename r a), readback (rename r b)] none = _
      rw [readback_rename r hr a, readback_rename r hr b]
      rfl
  | _, .op Op.out (.cons c (.cons x .nil)) => by
      change Pattern.apply "POutput" [readback (rename r c), readback (rename r x)] = _
      rw [readback_rename r hr c, readback_rename r hr x]
      rfl
  | _, .op Op.inp (.cons c (.cons K .nil)) => by
      change Pattern.apply "PInput"
        [readback (rename r c), .lambda none (readback (rename (liftRen r [Srt.pr]) K))] = _
      have hr' : ∀ s (v : Var (Srt.pr :: Δ) s),
          varIndex (liftRen r [Srt.pr] s v) = varIndex v := by
        intro s v
        cases v with
        | zero => rfl
        | succ w =>
            change varIndex (liftRen r [] s w) + 1 = varIndex w + 1
            rw [show liftRen r [] s w = r s w from rfl, hr]
      rw [readback_rename r hr c, readback_rename (liftRen r [Srt.pr]) hr' K]
      rfl
  | _, .op Op.drp (.cons n .nil) => by
      change Pattern.apply "PDrop" [readback (rename r n)] = _
      rw [readback_rename r hr n]
      rfl
  | _, .op Op.quo (.cons q .nil) => by
      change Pattern.apply "NQuote" [readback (rename r q)] = _
      rw [readback_rename r hr q]
      rfl
termination_by _ t => termSize t
decreasing_by all_goals (simp_wf; simp only [termSize, argsSize]; omega)

theorem readback_lift0 {Γ : Ctx sig} {s : Srt} (t : Term sig [] s) :
    readback (lift0 (Γ := Γ) t) = readback t :=
  readback_rename (emptyRen Γ) (fun _ v => by cases v) t

theorem readback_nameOf {Γ : Ctx sig} (t : Term sig Γ Srt.pr) :
    StructuralCongruence (readback (nameOf t)) (.apply "NQuote" [readback t]) :=
  readback_sc (nameOf_equiv t)

/-- An environment whose entries are the variables at their own index. -/
def VarEnv {Γ : Ctx sig} (ρ : Env Γ) : Prop :=
  ∀ k t, ρ k = some t → ∃ v, t = .var v ∧ varIndex v = k

theorem VarEnv.up {Γ : Ctx sig} {ρ : Env Γ} (h : VarEnv ρ) : VarEnv ρ.up := by
  intro k t ht
  cases k with
  | zero =>
      cases ht
      exact ⟨.zero, rfl, rfl⟩
  | succ k =>
      simp only [Env.up, Option.map_eq_some_iff] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      obtain ⟨v, rfl, hv⟩ := h k u hu
      exact ⟨.succ v, rfl, by simp [varIndex, hv]⟩

theorem VarEnv.empty : VarEnv (Env.empty ([] : Ctx sig)) := by
  intro k t h
  cases h

/-- A name that denotes a bound index is congruent to that index. -/
theorem sc_of_nameHead {name : Pattern} {k : Nat} (h : nameHead name = some k) :
    StructuralCongruence name (.bvar k) := by
  induction name using nameHead.induct with
  | case1 j =>
      simp only [nameHead, Option.some.injEq] at h
      subst h
      exact .refl _
  | case2 m ih =>
      rw [nameHead.eq_2] at h
      exact .trans _ _ _ (StructuralCongruence.quote_drop m) (ih h)
  | case3 x hbvar hquoteDrop =>
      rw [nameHead.eq_3 x hbvar hquoteDrop] at h
      cases h

/-- **A translated pattern reads back to itself**, up to structural
congruence, in every environment of variables. -/
theorem readback_translate :
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (n : Pattern) (c : Term sig Γ Srt.nm),
      VarEnv ρ → tName ρ n = some c → StructuralCongruence (readback c) n) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (p : Pattern) (t : Term sig Γ Srt.pr),
      VarEnv ρ → tProc ρ p = some t → StructuralCongruence (readback t) p) ∧
    (∀ {Γ : Ctx sig} (ρ : Env Γ) (ps : List Pattern) (t : Term sig Γ Srt.pr),
      VarEnv ρ → tProcs ρ ps = some t →
        StructuralCongruence (readback t) (.collection .hashBag ps none)) := by
  refine tName.mutual_induct
    (fun {Γ} ρ n => ∀ c : Term sig Γ Srt.nm,
      VarEnv ρ → tName ρ n = some c → StructuralCongruence (readback c) n)
    (fun {Γ} ρ p => ∀ t : Term sig Γ Srt.pr,
      VarEnv ρ → tProc ρ p = some t → StructuralCongruence (readback t) p)
    (fun {Γ} ρ ps => ∀ t : Term sig Γ Srt.pr, VarEnv ρ → tProcs ρ ps = some t →
      StructuralCongruence (readback t) (.collection .hashBag ps none))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Γ ρ k c hρ h
    rw [tName.eq_1] at h
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨v, rfl, hv⟩ := hρ k u hu
    change StructuralCongruence (.apply "NQuote" [.apply "PDrop" [.bvar (varIndex v)]]) _
    rw [hv]
    exact StructuralCongruence.quote_drop _
  · intro Γ ρ label c _ h
    rw [tName.eq_2] at h
    cases h
    exact .refl _
  · intro Γ ρ name ih c hρ h
    rw [tName.eq_3] at h
    exact .trans _ _ _ (ih c hρ h) (.symm _ _ (StructuralCongruence.quote_drop name))
  · intro Γ ρ code hcode ih c _ h
    rw [tName.eq_4 _ _ hcode] at h
    obtain ⟨code₀, hcode₀, rfl⟩ := Option.map_eq_some_iff.mp h
    refine .trans _ _ _ (readback_nameOf _) ?_
    rw [readback_lift0]
    exact sc_apply1 _ (ih code₀ VarEnv.empty hcode₀)
  · intro x Γ ρ hbvar hfvar hquoteDrop hquote c _ h
    rw [tName.eq_5 _ _ hbvar hfvar hquoteDrop hquote] at h
    cases h
  · intro Γ ρ t _ h
    rw [tProc.eq_1] at h
    cases h
    exact .refl _
  · intro Γ ρ name k hk t hρ h
    simp only [tProc.eq_2, hk] at h
    obtain ⟨v, rfl, hv⟩ := hρ k t h
    change StructuralCongruence (.apply "PDrop" [.bvar (varIndex v)]) _
    rw [hv]
    exact sc_apply1 _ (.symm _ _ (sc_of_nameHead hk))
  · intro Γ ρ name hk ih t hρ h
    simp only [tProc.eq_2, hk] at h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    exact sc_apply1 _ (ih c hρ hc)
  · intro Γ ρ name payload ihn ihp t hρ h
    rw [tProc.eq_3] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, q, hq, rfl⟩ := h
    exact sc_apply2 _ (ihn c hρ hc) (ihp q hρ hq)
  · intro Γ ρ name body ihn ihb t hρ h
    rw [tProc.eq_4] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, K, hK, rfl⟩ := h
    exact sc_apply2 _ (ihn c hρ hc)
      (StructuralCongruence.lambda_cong _ _ _ (ihb K hρ.up hK))
  · intro Γ ρ elements ih t hρ h
    rw [tProc.eq_5] at h
    exact ih t hρ h
  · intro x Γ ρ hzero hdrop hout hinp hbag t _ h
    rw [tProc.eq_6 _ _ hzero hdrop hout hinp hbag] at h
    cases h
  · intro Γ ρ t _ h
    cases h
    exact .symm _ _ StructuralCongruence.par_empty
  · intro Γ ρ process rest ihp ihr t hρ h
    rw [tProcs.eq_2] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    exact .trans _ _ _ (sc_bag2 (ihp head hρ hhead) (ihr tail hρ htail))
      (StructuralCongruence.par_flatten [process] rest)

/-- Translated names with equal classes are structurally congruent. -/
theorem sc_of_tName_cls {Γ : Ctx sig} {ρ : Env Γ} (hρ : VarEnv ρ) {n m : Pattern}
    {c d : Term sig Γ Srt.nm} (hn : tName ρ n = some c) (hm : tName ρ m = some d)
    (same : cls c = cls d) : StructuralCongruence n m :=
  .trans _ _ _ (.symm _ _ (readback_translate.1 ρ n c hρ hn))
    (.trans _ _ _ (readback_sc (cls_eq_iff.mp same)) (readback_translate.1 ρ m d hρ hm))

end Readback

/-! ## Parallel atoms of a source process -/

section Flatten

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence

mutual
/-- The parallel atoms of an authored process: nested bags are spliced and
null processes removed. -/
def flatAtoms : Pattern → List Pattern
  | .collection .hashBag elements none => flatAtomsList elements
  | .apply "PZero" [] => []
  | p => [p]

def flatAtomsList : List Pattern → List Pattern
  | [] => []
  | p :: ps => flatAtoms p ++ flatAtomsList ps
end

/-- An atom is neither a bag nor the null process. -/
def IsAtom (e : Pattern) : Prop :=
  (∀ elements, e ≠ .collection .hashBag elements none) ∧ e ≠ .apply "PZero" []

theorem sc_bag_append (A B : List Pattern) :
    StructuralCongruence
      (.collection .hashBag [.collection .hashBag A none, .collection .hashBag B none] none)
      (.collection .hashBag (A ++ B) none) :=
  (StructuralCongruence.par_flatten [.collection .hashBag A none] B).trans _ _ _
    ((StructuralCongruence.par_perm _ _ (List.perm_append_comm)).trans _ _ _
      ((StructuralCongruence.par_flatten B A).trans _ _ _
        (StructuralCongruence.par_perm _ _ List.perm_append_comm)))

/-- A process is its bag of parallel atoms, up to structural congruence. -/
theorem sc_flatAtoms :
    (∀ p : Pattern, StructuralCongruence p (.collection .hashBag (flatAtoms p) none)) ∧
    (∀ ps : List Pattern, StructuralCongruence (.collection .hashBag ps none)
      (.collection .hashBag (flatAtomsList ps) none)) := by
  refine flatAtoms.mutual_induct (fun p => StructuralCongruence p
      (.collection .hashBag (flatAtoms p) none))
    (fun ps => StructuralCongruence (.collection .hashBag ps none)
      (.collection .hashBag (flatAtomsList ps) none)) ?_ ?_ ?_ ?_ ?_
  · intro elements ih
    rw [flatAtoms.eq_1]
    exact ih
  · rw [flatAtoms.eq_2]
    exact .symm _ _ StructuralCongruence.par_empty
  · intro p hbag hzero
    rw [flatAtoms.eq_3 p hbag hzero]
    exact .symm _ _ (StructuralCongruence.par_singleton p)
  · rw [flatAtomsList.eq_1]
    exact .refl _
  · intro p ps ihp ihps
    rw [flatAtomsList.eq_2]
    have split : StructuralCongruence (.collection .hashBag (p :: ps) none)
        (.collection .hashBag [p, .collection .hashBag ps none] none) :=
      .symm _ _ (StructuralCongruence.par_flatten [p] ps)
    exact split.trans _ _ _ ((sc_bag2 ihp ihps).trans _ _ _ (sc_bag_append _ _))

theorem isAtom_of_mem_flatAtoms :
    (∀ p : Pattern, ∀ e ∈ flatAtoms p, IsAtom e) ∧
    (∀ ps : List Pattern, ∀ e ∈ flatAtomsList ps, IsAtom e) := by
  refine flatAtoms.mutual_induct (fun p => ∀ e ∈ flatAtoms p, IsAtom e)
    (fun ps => ∀ e ∈ flatAtomsList ps, IsAtom e) ?_ ?_ ?_ ?_ ?_
  · intro elements ih e he
    rw [flatAtoms.eq_1] at he
    exact ih e he
  · intro e he
    rw [flatAtoms.eq_2] at he
    cases he
  · intro p hbag hzero e he
    rw [flatAtoms.eq_3 p hbag hzero] at he
    rw [List.mem_singleton.mp he]
    exact ⟨fun elements h => hbag elements h, fun h => hzero h⟩
  · intro e he
    cases he
  · intro p ps ihp ihps e he
    rw [flatAtomsList.eq_2] at he
    rcases List.mem_append.mp he with he | he
    · exact ihp e he
    · exact ihps e he

open Mettapedia.OSLF.MeTTaIL.Syntax (rhoReflectivePresentation)
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax

theorem typed_of_mem_flatAtoms {free : FreeSortContext} {bound : List String} :
    (∀ p : Pattern, ProcWellSorted rhoReflectivePresentation free bound p →
      ∀ e ∈ flatAtoms p, ProcWellSorted rhoReflectivePresentation free bound e) ∧
    (∀ ps : List Pattern, ProcListWellSorted rhoReflectivePresentation free bound ps →
      ∀ e ∈ flatAtomsList ps, ProcWellSorted rhoReflectivePresentation free bound e) := by
  refine flatAtoms.mutual_induct
    (fun p => ProcWellSorted rhoReflectivePresentation free bound p →
      ∀ e ∈ flatAtoms p, ProcWellSorted rhoReflectivePresentation free bound e)
    (fun ps => ProcListWellSorted rhoReflectivePresentation free bound ps →
      ∀ e ∈ flatAtomsList ps, ProcWellSorted rhoReflectivePresentation free bound e)
    ?_ ?_ ?_ ?_ ?_
  · intro elements ih typed e he
    rw [flatAtoms.eq_1] at he
    cases typed
    rename_i listTyped
    exact ih listTyped e he
  · intro _ e he
    rw [flatAtoms.eq_2] at he
    cases he
  · intro p hbag hzero typed e he
    rw [flatAtoms.eq_3 p hbag hzero] at he
    rw [List.mem_singleton.mp he]
    exact typed
  · intro _ e he
    cases he
  · intro p ps ihp ihps typed e he
    rw [flatAtomsList.eq_2] at he
    cases typed
    rename_i headTyped tailTyped
    rcases List.mem_append.mp he with he | he
    · exact ihp headTyped e he
    · exact ihps tailTyped e he

/-- The shapes a translated process can have. -/
theorem tProc_shape {Γ : Ctx sig} {ρ : Env Γ} {e : Pattern} {t : Term sig Γ Srt.pr}
    (h : tProc ρ e = some t) :
    (e = .apply "PZero" [] ∧ t = nilT) ∨
    (∃ name k, e = .apply "PDrop" [name] ∧ nameHead name = some k ∧ ρ k = some t) ∨
    (∃ name c, e = .apply "PDrop" [name] ∧ nameHead name = none ∧ tName ρ name = some c ∧
      t = drpT c) ∨
    (∃ channel payload c q, e = .apply "POutput" [channel, payload] ∧
      tName ρ channel = some c ∧ tProc ρ payload = some q ∧ t = outT c q) ∨
    (∃ channel body c K, e = .apply "PInput" [channel, .lambda none body] ∧
      tName ρ channel = some c ∧ tProc ρ.up body = some K ∧ t = inpT c K) ∨
    (∃ elements, e = .collection .hashBag elements none ∧ tProcs ρ elements = some t) := by
  by_cases hzero : e = .apply "PZero" []
  · subst hzero
    rw [tProc.eq_1] at h
    cases h
    exact .inl ⟨rfl, rfl⟩
  by_cases hdrop : ∃ name, e = .apply "PDrop" [name]
  · obtain ⟨name, rfl⟩ := hdrop
    rw [tProc.eq_2] at h
    cases hk : nameHead name with
    | some k =>
        simp only [hk] at h
        exact .inr (.inl ⟨name, k, rfl, hk, h⟩)
    | none =>
        simp only [hk] at h
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
        exact .inr (.inr (.inl ⟨name, c, rfl, hk, hc, rfl⟩))
  by_cases hout : ∃ channel payload, e = .apply "POutput" [channel, payload]
  · obtain ⟨channel, payload, rfl⟩ := hout
    rw [tProc.eq_3] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, q, hq, rfl⟩ := h
    exact .inr (.inr (.inr (.inl ⟨channel, payload, c, q, rfl, hc, hq, rfl⟩)))
  by_cases hinp : ∃ channel body, e = .apply "PInput" [channel, .lambda none body]
  · obtain ⟨channel, body, rfl⟩ := hinp
    rw [tProc.eq_4] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, K, hK, rfl⟩ := h
    exact .inr (.inr (.inr (.inr (.inl ⟨channel, body, c, K, rfl, hc, hK, rfl⟩))))
  by_cases hbag : ∃ elements, e = .collection .hashBag elements none
  · obtain ⟨elements, rfl⟩ := hbag
    rw [tProc.eq_5] at h
    exact .inr (.inr (.inr (.inr (.inr ⟨elements, rfl, h⟩))))
  rw [tProc.eq_6 ρ e hzero (fun name he => hdrop ⟨name, he⟩)
    (fun channel payload he => hout ⟨channel, payload, he⟩)
    (fun channel body he => hinp ⟨channel, body, he⟩)
    (fun elements he => hbag ⟨elements, he⟩)] at h
  cases h

/-- An atom in an environment of variables translates to a single class. -/
theorem atoms_of_atom {Γ : Ctx sig} {ρ : Env Γ} (hρ : VarEnv ρ) {e : Pattern}
    {t : Term sig Γ Srt.pr} (he : IsAtom e) (h : tProc ρ e = some t) :
    atoms t = {cls t} := by
  rcases tProc_shape h with ⟨hz, _⟩ | ⟨name, k, _, _, hk⟩ | ⟨name, c, _, _, _, rfl⟩ |
      ⟨channel, payload, c, q, _, _, _, rfl⟩ | ⟨channel, body, c, K, _, _, _, rfl⟩ |
      ⟨elements, rfl, _⟩
  · exact absurd hz he.2
  · obtain ⟨v, rfl, _⟩ := hρ k t hk
    rfl
  · rfl
  · rfl
  · rfl
  · exact absurd rfl (he.1 elements)

/-- The translation of a process is the parallel composition of the
translations of its atoms. -/
theorem translate_flatAtoms {Γ : Ctx sig} {ρ : Env Γ} (hρ : VarEnv ρ) :
    (∀ p : Pattern, ∀ t, tProc ρ p = some t →
      ∃ L : List (Pattern × Term sig Γ Srt.pr), L.map Prod.fst = flatAtoms p ∧
        (∀ x ∈ L, tProc ρ x.1 = some x.2) ∧ atoms t = (L.map (fun x => cls x.2) : List _)) ∧
    (∀ ps : List Pattern, ∀ t, tProcs ρ ps = some t →
      ∃ L : List (Pattern × Term sig Γ Srt.pr), L.map Prod.fst = flatAtomsList ps ∧
        (∀ x ∈ L, tProc ρ x.1 = some x.2) ∧ atoms t = (L.map (fun x => cls x.2) : List _)) := by
  refine flatAtoms.mutual_induct
    (fun p => ∀ t, tProc ρ p = some t →
      ∃ L : List (Pattern × Term sig Γ Srt.pr), L.map Prod.fst = flatAtoms p ∧
        (∀ x ∈ L, tProc ρ x.1 = some x.2) ∧ atoms t = (L.map (fun x => cls x.2) : List _))
    (fun ps => ∀ t, tProcs ρ ps = some t →
      ∃ L : List (Pattern × Term sig Γ Srt.pr), L.map Prod.fst = flatAtomsList ps ∧
        (∀ x ∈ L, tProc ρ x.1 = some x.2) ∧ atoms t = (L.map (fun x => cls x.2) : List _))
    ?_ ?_ ?_ ?_ ?_
  · intro elements ih t h
    rw [tProc.eq_5] at h
    rw [flatAtoms.eq_1]
    exact ih t h
  · intro t h
    rw [tProc.eq_1] at h
    cases h
    exact ⟨[], by rw [flatAtoms.eq_2]; rfl, by simp, rfl⟩
  · intro p hbag hzero t h
    refine ⟨[(p, t)], by rw [flatAtoms.eq_3 p hbag hzero]; rfl, by simpa using h, ?_⟩
    rw [atoms_of_atom hρ ⟨fun elements e => hbag elements e, fun e => hzero e⟩ h]
    rfl
  · intro t h
    cases h
    exact ⟨[], rfl, by simp, rfl⟩
  · intro p ps ihp ihps t h
    rw [tProcs.eq_2] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    obtain ⟨Lp, hLp, htp, hap⟩ := ihp head hhead
    obtain ⟨Ls, hLs, hts, has⟩ := ihps tail htail
    refine ⟨Lp ++ Ls, by rw [List.map_append, hLp, hLs, flatAtomsList.eq_2], ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact htp x hx
      · exact hts x hx
    · change atoms head + atoms tail = _
      rw [hap, has, List.map_append]
      rfl

/-- A list of translated atoms translates to the composition of their classes. -/
theorem tProcs_atoms {Γ : Ctx sig} {ρ : Env Γ} (hρ : VarEnv ρ)
    (L : List (Pattern × Term sig Γ Srt.pr)) (hL : ∀ x ∈ L, tProc ρ x.1 = some x.2)
    (hatom : ∀ x ∈ L, IsAtom x.1) :
    ∃ T, tProcs ρ (L.map Prod.fst) = some T ∧ atoms T = (L.map (fun x => cls x.2) : List _) := by
  induction L with
  | nil => exact ⟨nilT, rfl, rfl⟩
  | cons x L ih =>
      obtain ⟨T, hT, hatoms⟩ := ih (fun y hy => hL y (List.mem_cons_of_mem x hy))
        (fun y hy => hatom y (List.mem_cons_of_mem x hy))
      refine ⟨parT x.2 T, ?_, ?_⟩
      · rw [List.map_cons, tProcs.eq_2, hL x (List.mem_cons_self), Option.bind_some, hT,
          Option.map_some]
      · change atoms x.2 + atoms T = _
        rw [atoms_of_atom hρ (hatom x (List.mem_cons_self)) (hL x (List.mem_cons_self)),
          hatoms]
        rfl

/-- Two named members of a multiset image come from two distinct list
positions. -/
theorem extract_two {α β : Type*} (L : List α) (f : α → β) {a b : β} {m : Multiset β}
    (h : ((L.map f : List β) : Multiset β) = a ::ₘ b ::ₘ m) :
    ∃ x y L', L.Perm (x :: y :: L') ∧ f x = a ∧ f y = b ∧
      ((L'.map f : List β) : Multiset β) = m := by
  classical
  have ha : a ∈ L.map f := by
    have : a ∈ ((L.map f : List β) : Multiset β) := by rw [h]; simp
    exact Multiset.mem_coe.mp this
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  have perm₁ := List.perm_cons_erase hx
  have h₁ : (((L.erase x).map f : List β) : Multiset β) = b ::ₘ m := by
    have := h
    rw [(Multiset.coe_eq_coe.mpr (perm₁.map f)), List.map_cons, ← Multiset.cons_coe] at this
    exact (Multiset.cons_inj_right _).mp this
  have hb : b ∈ (L.erase x).map f := by
    have : b ∈ (((L.erase x).map f : List β) : Multiset β) := by rw [h₁]; simp
    exact Multiset.mem_coe.mp this
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
  have perm₂ := List.perm_cons_erase hy
  refine ⟨x, y, (L.erase x).erase y, perm₁.trans (perm₂.cons x), rfl, rfl, ?_⟩
  have := h₁
  rw [(Multiset.coe_eq_coe.mpr (perm₂.map f)), List.map_cons, ← Multiset.cons_coe] at this
  exact (Multiset.cons_inj_right _).mp this

/-- An atom whose class is an output is an output with those component
classes. -/
theorem output_of_cls {Γ : Ctx sig} {ρ : Env Γ} (hρ : VarEnv ρ) {e : Pattern}
    {t : Term sig Γ Srt.pr} (he : IsAtom e) (h : tProc ρ e = some t)
    {c : Term sig Γ Srt.nm} {q : Term sig Γ Srt.pr} (hcls : cls t = cls (outT c q)) :
    ∃ channel payload c' q', e = .apply "POutput" [channel, payload] ∧
      tName ρ channel = some c' ∧ tProc ρ payload = some q' ∧
      cls c' = cls c ∧ cls q' = cls q := by
  have hparts : outParts t = {(cls c, cls q)} := outParts_invariant (cls_eq_iff.mp hcls)
  rcases tProc_shape h with ⟨hz, _⟩ | ⟨name, k, _, _, hk⟩ | ⟨name, c₁, _, _, _, rfl⟩ |
      ⟨channel, payload, c₁, q₁, rfl, hc, hq, rfl⟩ | ⟨channel, body, c₁, K, _, _, _, rfl⟩ |
      ⟨elements, rfl, _⟩
  · exact absurd hz he.2
  · obtain ⟨v, rfl, _⟩ := hρ k t hk
    exact absurd hparts.symm (Multiset.singleton_ne_zero _)
  · exact absurd hparts.symm (Multiset.singleton_ne_zero _)
  · have := Multiset.singleton_inj.mp hparts
    simp only [Prod.mk.injEq] at this
    exact ⟨channel, payload, c₁, q₁, rfl, hc, hq, this.1, this.2⟩
  · exact absurd hparts.symm (Multiset.singleton_ne_zero _)
  · exact absurd rfl (he.1 elements)

/-- An atom whose class is an input is an input with those component
classes. -/
theorem input_of_cls {Γ : Ctx sig} {ρ : Env Γ} (hρ : VarEnv ρ) {e : Pattern}
    {t : Term sig Γ Srt.pr} (he : IsAtom e) (h : tProc ρ e = some t)
    {c : Term sig Γ Srt.nm} {K : Term sig (Srt.pr :: Γ) Srt.pr}
    (hcls : cls t = cls (inpT c K)) :
    ∃ channel body c' K', e = .apply "PInput" [channel, .lambda none body] ∧
      tName ρ channel = some c' ∧ tProc ρ.up body = some K' ∧
      cls c' = cls c ∧ cls K' = cls K := by
  have hparts : inpParts t = {(cls c, cls K)} := inpParts_invariant (cls_eq_iff.mp hcls)
  rcases tProc_shape h with ⟨hz, _⟩ | ⟨name, k, _, _, hk⟩ | ⟨name, c₁, _, _, _, rfl⟩ |
      ⟨channel, payload, c₁, q₁, _, _, _, rfl⟩ | ⟨channel, body, c₁, K₁, rfl, hc, hK, rfl⟩ |
      ⟨elements, rfl, _⟩
  · exact absurd hz he.2
  · obtain ⟨v, rfl, _⟩ := hρ k t hk
    exact absurd hparts.symm (Multiset.singleton_ne_zero _)
  · exact absurd hparts.symm (Multiset.singleton_ne_zero _)
  · exact absurd hparts.symm (Multiset.singleton_ne_zero _)
  · have := Multiset.singleton_inj.mp hparts
    simp only [Prod.mk.injEq] at this
    exact ⟨channel, body, c₁, K₁, rfl, hc, hK, this.1, this.2⟩
  · exact absurd rfl (he.1 elements)

/-- Instantiation respects the equations in both arguments. -/
theorem inst_equiv {Γ : Ctx sig} {K K' : Term sig (Srt.pr :: Γ) Srt.pr}
    {q q' : Term sig Γ Srt.pr} (hK : EqClosure equations K K') (hq : EqClosure equations q q') :
    EqClosure equations (inst K q) (inst K' q') :=
  (eqClosure_bind (extend q) hK).trans
    (eqClosure_bind_pointwise (extend q) (extend q') (fun _ x => by
      cases x with
      | zero => exact hq
      | succ _ => exact .refl _) K')

theorem sc_second {a b b' : Pattern} (rest : List Pattern) (h : StructuralCongruence b b') :
    StructuralCongruence (.collection .hashBag (a :: b :: rest) none)
      (.collection .hashBag (a :: b' :: rest) none) := by
  refine StructuralCongruence.par_cong _ _ (by simp) ?_
  intro i h₁ _
  match i with
  | 0 => exact .refl _
  | 1 => simpa using h
  | n + 2 => exact .refl _

end Flatten

/-! ## Reflection of the strict core

Every step of the presented strict core from the translation of an admitted
closed process is taken by the authored executor from a structurally
congruent rearrangement of that process, and its reduct translates into the
target class. With the forward simulation this makes the image of the
admitted processes closed under the strict core's steps. -/

section Reflection

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
  (RhoStep rho_input_wellSorted_inv rho_output_wellSorted_inv)
open Mettapedia.OSLF.MeTTaIL.Syntax (rhoReflectivePresentation)
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax

/-- A COMM-shaped step between classes, from the translation of an admitted
closed process, is an executor COMM step from a rearrangement. -/
theorem comm_reflection {free : FreeSortContext} {P : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] P)
    {s₀ : Term sig [] Srt.pr} (hs : tProc (Env.empty []) P = some s₀)
    {u : Term sig [] Srt.pr} (c : Term sig [] Srt.nm) (q : Term sig [] Srt.pr)
    (K : Term sig [Srt.pr] Srt.pr) (others : Multiset (Cls [] Srt.pr))
    (hsrc : atoms s₀ = cls (outT c q) ::ₘ cls (inpT c K) ::ₘ others)
    (htgt : atoms u = atoms (inst K q) + others) :
    ∃ P₁ P', StructuralCongruence P P₁ ∧ RhoStep P₁ P' ∧
      ∃ t, tProc (Env.empty []) P' = some t ∧ cls t = cls u := by
  have hρ : VarEnv (Env.empty ([] : Ctx sig)) := VarEnv.empty
  obtain ⟨L, hLfst, hLtr, hLatoms⟩ := (translate_flatAtoms hρ).1 P s₀ hs
  rw [hLatoms] at hsrc
  obtain ⟨xo, xi, L', hperm, hxo, hxi, hL'⟩ := extract_two L (fun x => cls x.2) hsrc
  have memo : xo ∈ L := hperm.symm.subset (List.mem_cons_self)
  have memi : xi ∈ L := hperm.symm.subset (List.mem_cons_of_mem _ List.mem_cons_self)
  have memL' : ∀ x ∈ L', x ∈ L := fun x hx =>
    hperm.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
  have inFlat : ∀ x ∈ L, x.1 ∈ flatAtoms P := fun x hx => by
    rw [← hLfst]
    exact List.mem_map_of_mem hx
  have atomAt : ∀ x ∈ L, IsAtom x.1 := fun x hx =>
    isAtom_of_mem_flatAtoms.1 P x.1 (inFlat x hx)
  have typedAt : ∀ x ∈ L, ProcWellSorted rhoReflectivePresentation free [] x.1 := fun x hx =>
    typed_of_mem_flatAtoms.1 P typed x.1 (inFlat x hx)
  obtain ⟨chO, pl, cO, q', hxo1, hcO, hq', ecO, eq'⟩ :=
    output_of_cls hρ (atomAt xo memo) (hLtr xo memo) hxo
  obtain ⟨chI, body, cI, K', hxi1, hcI, hK', ecI, eK'⟩ :=
    input_of_cls hρ (atomAt xi memi) (hLtr xi memi) hxi
  have channels : StructuralCongruence chO chI :=
    sc_of_tName_cls hρ hcO hcI (ecO.trans ecI.symm)
  have outTyped := typedAt xo memo
  rw [hxo1] at outTyped
  obtain ⟨_, payloadTyped⟩ := rho_output_wellSorted_inv outTyped
  have inTyped := typedAt xi memi
  rw [hxi1] at inTyped
  obtain ⟨_, _, bodyTyped⟩ := rho_input_wellSorted_inv inTyped
  let rest := L'.map Prod.fst
  refine ⟨.collection .hashBag
      ([.apply "PInput" [chI, .lambda none body], .apply "POutput" [chI, pl]] ++ rest) none,
    .collection .hashBag (semanticCommSubst body pl :: rest) none, ?_,
    RhoStep.comm chI body pl rest bodyTyped payloadTyped, ?_⟩
  · have flat := sc_flatAtoms.1 P
    rw [← hLfst] at flat
    refine flat.trans _ _ _ ?_
    refine (StructuralCongruence.par_perm _ _ (hperm.map Prod.fst)).trans _ _ _ ?_
    refine (StructuralCongruence.par_perm _ _ (List.Perm.swap _ _ _)).trans _ _ _ ?_
    change StructuralCongruence (.collection .hashBag (xi.1 :: xo.1 :: rest) none) _
    rw [hxo1, hxi1]
    exact sc_second rest (sc_apply2 _ channels (.refl pl))
  · obtain ⟨T, hT, eT⟩ := translate_semanticCommSubst hK' hq'
    obtain ⟨R, hR, hRatoms⟩ := tProcs_atoms hρ L' (fun x hx => hLtr x (memL' x hx))
      (fun x hx => atomAt x (memL' x hx))
    refine ⟨parT T R, ?_, ?_⟩
    · rw [tProc.eq_5, tProcs.eq_2, hT, Option.bind_some, hR, Option.map_some]
    · apply cls_eq_of_atoms_eq
      change atoms T + atoms R = atoms u
      rw [atoms_invariant (eT.trans (inst_equiv (cls_eq_iff.mp eK') (cls_eq_iff.mp eq'))),
        hRatoms, hL', htgt]

/-- **Reflection of strict steps.** Every step of the presented strict core
from the translation of an admitted closed process is an executor step from a
structurally congruent rearrangement, and its reduct translates into the
target class. -/
theorem strict_reflection {free : FreeSortContext} {P : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] P)
    {s₀ : Term sig [] Srt.pr} (hs : tProc (Env.empty []) P = some s₀)
    {u : Term sig [] Srt.pr} (step : Steps strictRules s₀ u) :
    ∃ P₁ P', StructuralCongruence P P₁ ∧ RhoStep P₁ P' ∧
      ∃ t, tProc (Env.empty []) P' = some t ∧ cls t = cls u := by
  rcases steps_inversion (rest := []) (.inl rfl) step with
    ⟨c, q, K, others, hsrc, htgt⟩ | ⟨hne, _⟩
  · exact comm_reflection typed hs c q K others hsrc htgt
  · exact absurd hne (by simp)

/-- One named member of a multiset image comes from a list position. -/
theorem extract_one {α β : Type*} (L : List α) (f : α → β) {a : β} {m : Multiset β}
    (h : ((L.map f : List β) : Multiset β) = a ::ₘ m) :
    ∃ x L', L.Perm (x :: L') ∧ f x = a ∧ ((L'.map f : List β) : Multiset β) = m := by
  classical
  have ha : a ∈ L.map f := by
    have : a ∈ ((L.map f : List β) : Multiset β) := by rw [h]; simp
    exact Multiset.mem_coe.mp this
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  have perm := List.perm_cons_erase hx
  refine ⟨x, L.erase x, perm, rfl, ?_⟩
  have := h
  rw [(Multiset.coe_eq_coe.mpr (perm.map f)), List.map_cons, ← Multiset.cons_coe] at this
  exact (Multiset.cons_inj_right _).mp this

/-- An atom whose class is a drop is a drop of a name of that class. -/
theorem drop_of_cls {Γ : Ctx sig} {ρ : Env Γ} (hρ : VarEnv ρ) {e : Pattern}
    {t : Term sig Γ Srt.pr} (he : IsAtom e) (h : tProc ρ e = some t)
    {n : Term sig Γ Srt.nm} (hcls : cls t = cls (drpT n)) :
    ∃ name n', e = .apply "PDrop" [name] ∧ nameHead name = none ∧
      tName ρ name = some n' ∧ cls n' = cls n := by
  have hparts : dropParts t = {cls n} := dropParts_invariant (cls_eq_iff.mp hcls)
  rcases tProc_shape h with ⟨hz, _⟩ | ⟨name, k, _, _, hk⟩ | ⟨name, c₁, rfl, hn, hc, rfl⟩ |
      ⟨channel, payload, c₁, q₁, _, _, _, rfl⟩ | ⟨channel, body, c₁, K₁, _, _, _, rfl⟩ |
      ⟨elements, rfl, _⟩
  · exact absurd hz he.2
  · obtain ⟨v, rfl, _⟩ := hρ k t hk
    exact absurd hparts.symm (Multiset.singleton_ne_zero _)
  · exact ⟨name, c₁, rfl, hn, hc, Multiset.singleton_inj.mp hparts⟩
  · exact absurd hparts.symm (Multiset.singleton_ne_zero _)
  · exact absurd hparts.symm (Multiset.singleton_ne_zero _)
  · exact absurd rfl (he.1 elements)

theorem sizeOf_le_of_mem_flatAtoms :
    (∀ p : Pattern, ∀ e ∈ flatAtoms p, sizeOf e ≤ sizeOf p) ∧
    (∀ ps : List Pattern, ∀ e ∈ flatAtomsList ps, sizeOf e ≤ sizeOf ps) := by
  refine flatAtoms.mutual_induct (fun p => ∀ e ∈ flatAtoms p, sizeOf e ≤ sizeOf p)
    (fun ps => ∀ e ∈ flatAtomsList ps, sizeOf e ≤ sizeOf ps) ?_ ?_ ?_ ?_ ?_
  · intro elements ih e he
    rw [flatAtoms.eq_1] at he
    have := ih e he
    simp only [Pattern.collection.sizeOf_spec]
    omega
  · intro e he
    rw [flatAtoms.eq_2] at he
    cases he
  · intro p hbag hzero e he
    rw [flatAtoms.eq_3 p hbag hzero] at he
    rw [List.mem_singleton.mp he]
  · intro e he
    cases he
  · intro p ps ihp ihps e he
    rw [flatAtomsList.eq_2] at he
    simp only [List.cons.sizeOf_spec]
    rcases List.mem_append.mp he with he | he
    · have := ihp e he
      omega
    · have := ihps e he
      omega

/-- The translation of a process that is not a drop is not a drop, so its
name is its quotation. -/
theorem nameOf_translate_of_not_drop {Γ : Ctx sig} {ρ : Env Γ} {P : Pattern}
    {X : Term sig Γ Srt.pr} (h : tProc ρ P = some X)
    (hnot : ∀ m, P = .apply "PDrop" [m] → False) : nameOf X = quoT X := by
  rcases tProc_shape h with ⟨_, rfl⟩ | ⟨name, k, hP, _, _⟩ | ⟨name, c, hP, _, _, _⟩ |
      ⟨channel, payload, c, q, _, _, _, rfl⟩ | ⟨channel, body, c, K, _, _, _, rfl⟩ |
      ⟨elements, _, hX⟩
  · rfl
  · exact absurd hP (hnot name)
  · exact absurd hP (hnot name)
  · rfl
  · rfl
  · cases elements with
    | nil =>
        cases hX
        rfl
    | cons head tail =>
        rw [tProcs.eq_2] at hX
        simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hX
        obtain ⟨_, _, _, _, rfl⟩ := hX
        rfl

/-- **The source side of a Drop.** A closed dropped name whose translation is
the class of the quotation of some code can be rearranged into the quotation
of a source process translating to the class of that code. -/
theorem drop_source (name : Pattern) {n₀ : Term sig [] Srt.nm} {code : Term sig [] Srt.pr}
    (hn : nameHead name = none) (h : tName (Env.empty []) name = some n₀)
    (hc : cls n₀ = cls (quoT code)) :
    ∃ P', StructuralCongruence name (.apply "NQuote" [P']) ∧
      ∃ t, tProc (Env.empty []) P' = some t ∧ cls t = cls code := by
  cases hk : key code with
  | some k =>
      obtain ⟨m, hm, hmk, _⟩ := drop_of_key code k hk
      have hq : qcore (quoT code) = k := by rw [qcore_quo, hk]
      have hn0 : qcore n₀ = k := (qcore_invariant (cls_eq_iff.mp hc)).trans hq
      have hmn : EqClosure equations m n₀ := cls_eq_of_qcore_eq (hmk.trans hn0.symm)
      refine ⟨.apply "PDrop" [name], .symm _ _ (StructuralCongruence.quote_drop name),
        drpT n₀, ?_, cls_eq ((equiv_drpT hmn).symm.trans hm.symm)⟩
      rw [tProc.eq_2, hn]
      simp only [h, Option.map_some]
  | none =>
      have hq : qcore (quoT code) = .quo (cls code) := by rw [qcore_quo, hk]
      have hn0 : qcore n₀ = .quo (cls code) := (qcore_invariant (cls_eq_iff.mp hc)).trans hq
      by_cases hqd : ∃ name', name = .apply "NQuote" [.apply "PDrop" [name']]
      · obtain ⟨name', rfl⟩ := hqd
        rw [tName.eq_3] at h
        rw [nameHead.eq_2] at hn
        have hsize : sizeOf name' < sizeOf (Pattern.apply "NQuote" [.apply "PDrop" [name']]) := by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec]
          omega
        obtain ⟨P', hsc, rest⟩ := drop_source name' hn h hc
        exact ⟨P', (StructuralCongruence.quote_drop name').trans _ _ _ hsc, rest⟩
      by_cases hlit : ∃ P0, name = .apply "NQuote" [P0]
      · obtain ⟨P0, rfl⟩ := hlit
        have hnot : ∀ m, P0 = .apply "PDrop" [m] → False := fun m e => hqd ⟨m, by rw [e]⟩
        rw [tName.eq_4 _ _ hnot] at h
        obtain ⟨X, hX, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [lift0_nil, nameOf_translate_of_not_drop hX hnot, qcore_quo] at hn0
        cases hX' : key X with
        | none =>
            rw [hX'] at hn0
            refine ⟨P0, .refl _, X, hX, ?_⟩
            injection hn0
        | some k =>
            rw [hX'] at hn0
            obtain ⟨m, hXm, hmk, _⟩ := drop_of_key X k hX'
            have hmq : EqClosure equations m (quoT code) :=
              cls_eq_of_qcore_eq (hmk.trans (hn0.trans hq.symm))
            obtain ⟨L, hLfst, hLtr, hLatoms⟩ :=
              (translate_flatAtoms VarEnv.empty).1 P0 X hX
            have hatomsX : atoms X = {cls (drpT m)} := atoms_invariant hXm
            rw [hLatoms] at hatomsX
            obtain ⟨x, L', hperm, hx, hL'⟩ :=
              extract_one L (fun x => cls x.2) (hatomsX.trans (Multiset.cons_zero _).symm)
            have hL'nil : L' = [] := by
              have := congrArg Multiset.card hL'
              simpa using this
            subst hL'nil
            have hLx : L = [x] := List.perm_singleton.mp hperm
            subst hLx
            have hflat : flatAtoms P0 = [x.1] := hLfst.symm
            have hatom : IsAtom x.1 :=
              isAtom_of_mem_flatAtoms.1 P0 x.1 (by rw [hflat]; exact List.mem_singleton_self _)
            obtain ⟨name'', n'', hx1, hn'', htr'', hcls''⟩ :=
              drop_of_cls VarEnv.empty hatom (hLtr x (List.mem_singleton_self x)) hx
            have hsize : sizeOf name'' < sizeOf (Pattern.apply "NQuote" [P0]) := by
              have hle := sizeOf_le_of_mem_flatAtoms.1 P0 x.1
                (by rw [hflat]; exact List.mem_singleton_self _)
              rw [hx1] at hle
              simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec] at hle ⊢
              omega
            obtain ⟨P', hsc, rest⟩ := drop_source name'' hn'' htr'' (hcls''.trans (cls_eq hmq))
            refine ⟨P', ?_, rest⟩
            have hP0 : StructuralCongruence P0 (.apply "PDrop" [name'']) := by
              have := sc_flatAtoms.1 P0
              rw [hflat, hx1] at this
              exact this.trans _ _ _ (StructuralCongruence.par_singleton _)
            exact (sc_apply1 _ hP0).trans _ _ _
              ((StructuralCongruence.quote_drop name'').trans _ _ _ hsc)
      · exfalso
        by_cases hfree : ∃ label, name = .fvar label
        · obtain ⟨label, rfl⟩ := hfree
          rw [tName.eq_2] at h
          cases h
          cases hn0
        · have hbvar : ∀ k, name = .bvar k → False := fun k e => by
            subst e
            simp [nameHead] at hn
          rw [tName.eq_5 _ _ hbvar (fun label e => hfree ⟨label, e⟩)
            (fun name' e => hqd ⟨name', e⟩) (fun P0 e => hlit ⟨P0, e⟩)] at h
          cases h
termination_by sizeOf name

theorem sc_first {a a' : Pattern} (rest : List Pattern) (h : StructuralCongruence a a') :
    StructuralCongruence (.collection .hashBag (a :: rest) none)
      (.collection .hashBag (a' :: rest) none) := by
  refine StructuralCongruence.par_cong _ _ (by simp) ?_
  intro i h₁ _
  match i with
  | 0 => simpa using h
  | n + 1 => exact .refl _

/-- **Reflection of the book's steps.** Every step of the presented book
profile from the translation of an admitted closed process is a step of the
authored COMM/ParCong/Drop executor from a structurally congruent
rearrangement, and its reduct translates into the target class. -/
theorem book_reflection {free : FreeSortContext} {P : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] P)
    {s₀ : Term sig [] Srt.pr} (hs : tProc (Env.empty []) P = some s₀)
    {u : Term sig [] Srt.pr} (step : Steps bookRules s₀ u) :
    ∃ P₁ P', StructuralCongruence P P₁ ∧ RhoCombinedInterpretedStep.RhoStepWithDrop P₁ P' ∧
      ∃ t, tProc (Env.empty []) P' = some t ∧ cls t = cls u := by
  rcases steps_inversion (rest := [drop]) (.inr rfl) step with
    ⟨c, q, K, others, hsrc, htgt⟩ | ⟨_, code, others, hsrc, htgt⟩
  · obtain ⟨P₁, P', hsc, hstep, rest⟩ := comm_reflection typed hs c q K others hsrc htgt
    exact ⟨P₁, P', hsc, RhoCombinedInterpretedStep.core_in_combined hstep, rest⟩
  · have hρ : VarEnv (Env.empty ([] : Ctx sig)) := VarEnv.empty
    change atoms s₀ = _ at hsrc
    change atoms u = _ at htgt
    obtain ⟨L, hLfst, hLtr, hLatoms⟩ := (translate_flatAtoms hρ).1 P s₀ hs
    rw [hLatoms] at hsrc
    obtain ⟨x, L', hperm, hx, hL'⟩ := extract_one L (fun x => cls x.2) hsrc
    have memx : x ∈ L := hperm.symm.subset List.mem_cons_self
    have memL' : ∀ y ∈ L', y ∈ L := fun y hy => hperm.symm.subset (List.mem_cons_of_mem _ hy)
    have inFlat : ∀ y ∈ L, y.1 ∈ flatAtoms P := fun y hy => by
      rw [← hLfst]
      exact List.mem_map_of_mem hy
    have atomAt : ∀ y ∈ L, IsAtom y.1 := fun y hy =>
      isAtom_of_mem_flatAtoms.1 P y.1 (inFlat y hy)
    obtain ⟨name, n₀, hx1, hn, hname, hcls⟩ :=
      drop_of_cls hρ (atomAt x memx) (hLtr x memx) hx
    obtain ⟨P', hsc, t, ht, htc⟩ := drop_source name hn hname hcls
    let rest := L'.map Prod.fst
    refine ⟨.collection .hashBag (.apply "PDrop" [.apply "NQuote" [P']] :: rest) none,
      .collection .hashBag (P' :: rest) none, ?_,
      RhoCombinedInterpretedStep.par rest (RhoCombinedInterpretedStep.drop P'), ?_⟩
    · have flat := sc_flatAtoms.1 P
      rw [← hLfst] at flat
      refine flat.trans _ _ _ ?_
      refine (StructuralCongruence.par_perm _ _ (hperm.map Prod.fst)).trans _ _ _ ?_
      change StructuralCongruence (.collection .hashBag (x.1 :: rest) none) _
      rw [hx1]
      exact sc_first rest (sc_apply1 _ hsc)
    · obtain ⟨R, hR, hRatoms⟩ := tProcs_atoms hρ L' (fun y hy => hLtr y (memL' y hy))
        (fun y hy => atomAt y (memL' y hy))
      refine ⟨parT t R, ?_, ?_⟩
      · rw [tProc.eq_5, tProcs.eq_2, ht, Option.bind_some, hR, Option.map_some]
      · apply cls_eq_of_atoms_eq
        change atoms t + atoms R = atoms u
        rw [atoms_invariant (cls_eq_iff.mp htc), hRatoms, hL', htgt]
        rfl

end Reflection


/-! ## Controls -/

section Controls

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
  (RhoStep freeDrop no_freeDrop_step)

private def zeroP : Pattern := .apply "PZero" []
private def quoteZero : Pattern := .apply "NQuote" [zeroP]
private def outP (name process : Pattern) : Pattern := .apply "POutput" [name, process]
private def dropP (name : Pattern) : Pattern := .apply "PDrop" [name]
private def inpP (name body : Pattern) : Pattern := .apply "PInput" [name, .lambda none body]

/-- The payload `@0!(0)`. -/
private def payload : Pattern := outP quoteZero zeroP

private def payload₀ : Term sig [] Srt.pr := outT (quoT nilT) nilT

theorem control_payload : tProc (Env.empty []) payload = some payload₀ := rfl

/-- `for(x <- @0){x!(0)}` receiving `@0!(0)` sends on `@{@0!(0)}`, as the
pinned runtime does, and this is the instantiated continuation. -/
theorem control_received_name :
    semanticCommSubst (outP (.bvar 0) zeroP) payload =
        outP (.apply "NQuote" [payload]) zeroP ∧
      tProc (Env.empty []) (outP (.apply "NQuote" [payload]) zeroP) =
        some (inst (outT (quoT (.var .zero)) nilT) payload₀) :=
  ⟨rfl, rfl⟩

/-- `@*x` for the bound `x` is the bound name: the executor normalizes it
before comparing names, and the translation resolves it as a whole name. -/
theorem control_bound_quoteDrop :
    semanticCommSubst (outP (.apply "NQuote" [dropP (.bvar 0)]) zeroP) payload =
        semanticCommSubst (outP (.bvar 0) zeroP) payload ∧
      tProc (Env.empty []).up (outP (.apply "NQuote" [dropP (.bvar 0)]) zeroP) =
        tProc (Env.empty []).up (outP (.bvar 0) zeroP) :=
  ⟨rfl, rfl⟩

/-- `@*x` for a free `x` is the free name `x`, untouched by communication;
this is the pinned runtime's `@{*$x}`, whose quote seals the receive scope. -/
theorem control_free_quoteDrop :
    semanticCommSubst (outP (.apply "NQuote" [dropP (.fvar "x")]) zeroP) payload =
        outP (.fvar "x") zeroP ∧
      tProc (Env.empty []) (outP (.apply "NQuote" [dropP (.fvar "x")]) zeroP) =
        some (outT (freeT "x") nilT) ∧
      tProc (Env.empty []) (outP (.fvar "x") zeroP) = some (outT (freeT "x") nilT) :=
  ⟨rfl, rfl, rfl⟩

/-- A drop of the received name runs the payload; its translation is the
received process variable. -/
theorem control_received_drop :
    semanticCommSubst (dropP (.bvar 0)) payload = payload ∧
      tProc (Env.empty []).up (dropP (.bvar 0)) = some (.var .zero) :=
  ⟨rfl, rfl⟩

/-- A literal quote cannot mention an enclosing bound name: such code is
outside the translated fragment. -/
theorem control_literal_closed :
    tProc (Env.empty []).up (outP (.apply "NQuote" [outP (.bvar 0) zeroP]) zeroP) = none :=
  rfl

/-- A nested input shadows index zero, and the outer received drop is found
at index one. -/
theorem control_nested :
    semanticCommSubst (inpP quoteZero (outP (.bvar 0) (dropP (.bvar 1)))) payload =
        inpP quoteZero (outP (.bvar 0) payload) ∧
      tProc (Env.empty []) (inpP quoteZero (outP (.bvar 0) payload)) =
        some (inst (inpT (quoT nilT) (outT (quoT (.var .zero)) (.var (.succ .zero))))
          payload₀) :=
  ⟨rfl, rfl⟩

/-- A literal free drop is inert in the strict core, for the executor and
for the presented calculus, and runs in the book's profile. -/
theorem control_free_drop :
    freeDrop = dropP quoteZero ∧
      tProc (Env.empty []) freeDrop = some (drpT (quoT nilT)) ∧
      (∀ target, ¬ RhoStep freeDrop target) ∧
      (∀ target, ¬ Steps strictRules (drpT (quoT (nilT : Term sig [] Srt.pr))) target) ∧
      Steps bookRules (drpT (quoT (nilT : Term sig [] Srt.pr))) nilT :=
  ⟨rfl, rfl, no_freeDrop_step, fun target => drop_inert_strict nilT target,
    drop_runs_book nilT⟩

end Controls

#print axioms translate_semanticCommSubst
#print axioms rhoStep_simulation
#print axioms rhoStepWithDrop_simulation
#print axioms control_nested
#print axioms control_free_drop
#print axioms closed_admitted_translates
#print axioms strict_reflection
#print axioms book_reflection

end Mettapedia.OSLF.Binding.RhoPayloadPresentation
