import Mettapedia.OSLF.Syntax.RhoAuthoredCommRuleCover
import Mettapedia.OSLF.MeTTaIL.ScopedSubstitutionAgreement
import Mettapedia.OSLF.MeTTaIL.QuoteSafeOpening

/-!
# Quote-safe intrinsic communication and authored residual semantics

The intrinsic continuation lives in a sorted one-name context. Its encoding
commutes with capture-free substitution and with ordinary binder opening when
the payload and continuation respect the authored quotation boundary. This
connects the actual authored COMM firing to the intrinsic rule generator:
sources agree up to structural congruence, while immediate targets agree up to
process residual equivalence. The latter relation is necessary even for safe
terms, because authored substitution may contract a quoted Drop.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoQuoteSafeCommComparison

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
open Mettapedia.OSLF.Binding.RhoSemanticRulePolynomial
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

/-- A literal rho quote admitted at its sealed boundary is opaque to every
surrounding context-variable assignment. Its code may contain free names and
its own binders; it simply cannot depend on the surrounding binder context. -/
theorem literal_quote_substitute_opaque
    (assignment : Assignment) (code : Pattern)
    (safe : binderSafeAt "NQuote" 0 code = true) :
    substitute assignment (.apply "NQuote" [code]) =
      .apply "NQuote" [code] := by
  have closed := isWellScopedAt_of_binderSafeAt "NQuote" safe
  simp only [substitute, substituteList,
    substitute_closed_eq_self assignment code closed]

/-- An index above the available context cannot occur freely. -/
theorem noBVar_of_scope {p : Pattern} {depth index : Nat}
    (hscope : p.isWellScopedAt depth = true)
    (outside : depth ≤ index) : noBVar index p = true := by
  induction p using Pattern.inductionOn generalizing depth index with
  | hbvar n =>
      have hn : n < depth := by
        simpa only [Pattern.isWellScopedAt, decide_eq_true_eq] using hscope
      simp [noBVar, Nat.ne_of_lt (lt_of_lt_of_le hn outside)]
  | hfvar x => simp [noBVar]
  | happly constructor args ih =>
      have each := (isWellScopedListAt_eq_true_iff depth args).mp hscope
      induction args with
      | nil => rfl
      | cons head tail tailIH =>
          have hhead : noBVar index head = true :=
            ih head (by simp) (each head (by simp)) outside
          have htail : ∀ p ∈ tail, p.isWellScopedAt depth = true := by
            intro p hp
            exact each p (by simp [hp])
          have ihTail : ∀ p ∈ tail,
              ∀ {depth index : Nat},
                p.isWellScopedAt depth = true →
                depth ≤ index → noBVar index p = true := by
            intro p hp depth index hscope outside
            exact ih p (by simp [hp]) hscope outside
          simp [noBVar, noBVarList, hhead]
          have tailScope : (Pattern.apply constructor tail).isWellScopedAt depth = true :=
            (isWellScopedListAt_eq_true_iff depth tail).mpr htail
          exact tailIH ihTail tailScope htail
  | hlambda name body ih =>
      exact ih hscope (by omega)
  | hmultiLambda arity names body ih =>
      exact ih hscope (by omega)
  | hsubst body replacement ihBody ihReplacement =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at hscope
      simp only [noBVar, Bool.and_eq_true]
      exact ⟨ihBody hscope.1 (by omega), ihReplacement hscope.2 outside⟩
  | hcollection kind elems rest ih =>
      have each := (isWellScopedListAt_eq_true_iff depth elems).mp hscope
      induction elems with
      | nil => rfl
      | cons head tail tailIH =>
          have hhead : noBVar index head = true :=
            ih head (by simp) (each head (by simp)) outside
          have htail : ∀ p ∈ tail, p.isWellScopedAt depth = true := by
            intro p hp
            exact each p (by simp [hp])
          have ihTail : ∀ p ∈ tail,
              ∀ {depth index : Nat},
                p.isWellScopedAt depth = true →
                depth ≤ index → noBVar index p = true := by
            intro p hp depth index hscope outside
            exact ih p (by simp [hp]) hscope outside
          simp [noBVar, noBVarList, hhead]
          have tailScope :
              (Pattern.collection kind tail rest).isWellScopedAt depth = true :=
            (isWellScopedListAt_eq_true_iff depth tail).mpr htail
          exact tailIH ihTail tailScope htail

private theorem noBoundUnderQuoteList_of_each
    {index : Nat} {patterns : List Pattern}
    (each : ∀ p ∈ patterns, noBoundUnderQuote index p = true) :
    noBoundUnderQuoteList index patterns = true := by
  induction patterns with
  | nil => rfl
  | cons head tail ih =>
      simp only [noBoundUnderQuoteList, Bool.and_eq_true]
      exact ⟨each head (by simp),
        ih (fun p member => each p (by simp [member]))⟩

/-- A quote-safe pattern cannot mention an ambient binder from inside a
literal quotation. The statement tracks the ambient binder through nested
ordinary binders and collections. -/
theorem noBoundUnderQuote_of_binderSafeAt :
    ∀ (p : Pattern) (index : Nat),
      binderSafeAt "NQuote" (index + 1) p = true →
      noBoundUnderQuote index p = true := by
  intro p
  induction p using Pattern.inductionOn with
  | hbvar n =>
      intro index hsafe
      rfl
  | hfvar x =>
      intro index hsafe
      rfl
  | happly constructor args ih =>
      intro index hsafe
      cases args with
      | nil => simp [noBoundUnderQuote, noBoundUnderQuoteList]
      | cons first rest =>
          cases rest with
          | nil =>
              by_cases quoted : constructor = "NQuote"
              · subst constructor
                have bodySafe : binderSafeAt "NQuote" 0 first = true := by
                  simpa only [binderSafeAt, beq_self_eq_true, if_true] using hsafe
                have bodyScope := isWellScopedAt_of_binderSafeAt
                  "NQuote" bodySafe
                simpa only [noBoundUnderQuote] using
                  noBVar_of_scope bodyScope (Nat.zero_le index)
              · have firstSafe :
                    binderSafeAt "NQuote" (index + 1) first = true := by
                  simpa [binderSafeAt, quoted, binderSafeListAt] using hsafe
                have firstNoBound := ih first (by simp) index firstSafe
                simpa [noBoundUnderQuote, quoted, noBoundUnderQuoteList]
                  using firstNoBound
          | cons second more =>
              have hlist :
                  binderSafeListAt "NQuote" (index + 1)
                    (first :: second :: more) = true := by
                simpa [binderSafeAt] using hsafe
              have each :=
                (binderSafeListAt_eq_true_iff "NQuote" (index + 1)
                  (first :: second :: more)).mp hlist
              have noBoundEach : ∀ p ∈ first :: second :: more,
                  noBoundUnderQuote index p = true := by
                intro p hp
                exact ih p hp index (each p hp)
              simpa [noBoundUnderQuote] using
                noBoundUnderQuoteList_of_each noBoundEach
  | hlambda name body ih =>
      intro index hsafe
      simpa [noBoundUnderQuote, binderSafeAt, Nat.add_assoc] using
        ih (index + 1) hsafe
  | hmultiLambda arity names body ih =>
      intro index hsafe
      have bodySafe :
          binderSafeAt "NQuote" (index + arity + 1) body = true := by
        simpa [binderSafeAt, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hsafe
      simpa [noBoundUnderQuote] using ih (index + arity) bodySafe
  | hsubst body replacement ihBody ihReplacement =>
      intro index hsafe
      simp only [binderSafeAt, Bool.and_eq_true] at hsafe
      simp only [noBoundUnderQuote, Bool.and_eq_true]
      exact ⟨ihBody (index + 1) (by simpa [Nat.add_assoc] using hsafe.1),
        ihReplacement index hsafe.2⟩
  | hcollection kind elems rest ih =>
      intro index hsafe
      have each :=
        (binderSafeListAt_eq_true_iff "NQuote" (index + 1) elems).mp hsafe
      have noBoundEach : ∀ p ∈ elems,
          noBoundUnderQuote index p = true := by
        intro p hp
        exact ih p hp index (each p hp)
      simpa [noBoundUnderQuote] using
        noBoundUnderQuoteList_of_each noBoundEach

private abbrev raw := BindingCloneAlgebra.terms sig

/-- The encoded intrinsic rho constructors inhabit the strict authored name
or process shape, independently of the later cost syntax. -/
def EncodedCoreShape {Γ : Ctx sig} {s : Srt}
    (term : Term sig Γ s) : Prop :=
  match s with
  | .nm => rhoNameCoreShape (encodeTerm term) = true
  | .pr => rhoProcCoreShape (encodeTerm term) = true

mutual

theorem encodedTerm_coreShape : ∀ {Γ : Ctx sig} {s : Srt}
    (term : Term sig Γ s), EncodedCoreShape term
  | _, _, .var (s := s) v => by cases s <;> rfl
  | _, _, .op .nil .nil => rfl
  | _, _, .op .par (.cons left (.cons right .nil)) => by
      simpa [EncodedCoreShape, encodeTerm, encodeArgs, wrapBinders,
        rhoProcCoreShape, rhoProcCoreShapeList] using
        And.intro (encodedTerm_coreShape left) (encodedTerm_coreShape right)
  | _, _, .op .out (.cons channel (.cons payload .nil)) => by
      simpa [EncodedCoreShape, encodeTerm, encodeArgs, wrapBinders,
        rhoProcCoreShape, rhoNameCoreShape] using
        And.intro (encodedTerm_coreShape channel)
          (encodedTerm_coreShape payload)
  | _, _, .op .inp (.cons channel (.cons body .nil)) => by
      simpa [EncodedCoreShape, encodeTerm, encodeArgs, wrapBinders,
        rhoProcCoreShape, rhoNameCoreShape] using
        And.intro (encodedTerm_coreShape channel)
          (encodedTerm_coreShape body)
  | _, _, .op .quo (.cons process .nil) => by
      simpa [EncodedCoreShape, encodeTerm, encodeArgs, wrapBinders,
        rhoNameCoreShape] using encodedTerm_coreShape process
  | _, _, .op .drp (.cons name .nil) => by
      simpa [EncodedCoreShape, encodeTerm, encodeArgs, wrapBinders,
        rhoProcCoreShape] using encodedTerm_coreShape name

end

/-- At every ambient sorted context, intrinsic COMM substitution agrees with
binder-eliminating substitution of the encoded quoted payload. This is an
equality of generated raw terms; it does not assert that an open payload is a
literal quote admitted by the authored source grammar. -/
theorem encode_comm_target_eq_instantiate {Γ : Ctx sig}
    (payload : Term sig Γ Srt.pr)
    (body : Term sig (Srt.nm :: Γ) Srt.pr)
    (bodyScope : (encodeTerm body).isWellScopedAt (Γ.length + 1) = true) :
    encodeTerm (commTarget raw payload body) =
      instantiateBVar (.apply "NQuote" [encodeTerm payload])
        (encodeTerm body) := by
  let sigma := newestNameEnvironment raw (quote raw payload)
  let quoted : Pattern := .apply "NQuote" [encodeTerm payload]
  have agree : ∀ index, index < Γ.length + 1 →
      encodeSub sigma index = single quoted index := by
    intro index inside
    cases index with
    | zero =>
        have head := encodeSub_at_var sigma
          (Var.zero : Var (Srt.nm :: Γ) Srt.nm)
        change encodeSub sigma 0 =
          encodeTerm (Term.op Op.quo (.cons payload .nil)) at head
        simpa [quoted, single, encodeTerm, encodeArgs, wrapBinders] using head
    | succ older =>
        have olderInside : older < Γ.length := by omega
        let v := varOfIdx Γ ⟨older, olderInside⟩
        have position : (varIdx v).val = older := by
          exact congrArg Fin.val (varIdx_varOfIdx Γ ⟨older, olderInside⟩)
        have tail := encodeSub_at_var sigma (Var.succ v)
        change encodeSub sigma ((varIdx v).val + 1) =
          encodeTerm (Term.var v) at tail
        simpa [quoted, single, encodeTerm, position] using tail
  calc
    encodeTerm (commTarget raw payload body) =
        substitute (encodeSub sigma) (encodeTerm body) := by
      change encodeTerm (bind sigma body) = _
      exact encodeTerm_bind sigma body
    _ = substitute (single quoted) (encodeTerm body) :=
      substitute_eq_of_agree_on_scope _ _ _ _ bodyScope agree
    _ = instantiateBVar quoted (encodeTerm body) :=
      substitute_single_eq_instantiateBVar quoted (encodeTerm body)

/-- Source admission supplies the continuation scope needed by the general
context-indexed substitution comparison. The result lives in the generated
carrier even if its quoted payload was not a literal source quote. -/
theorem encode_comm_target_of_source_safe {Γ : Ctx sig}
    (channel : Term sig Γ Srt.nm)
    (payload : Term sig Γ Srt.pr)
    (body : Term sig (Srt.nm :: Γ) Srt.pr)
    (sourceSafe : intrinsicQuoteSafe Γ.length
      (commSource raw channel payload body) = true) :
    encodeTerm (commTarget raw payload body) =
      instantiateBVar (.apply "NQuote" [encodeTerm payload])
        (encodeTerm body) := by
  have bodySafe : intrinsicQuoteSafe (Γ.length + 1) body = true :=
    ((terms_commSource_quoteSafe channel payload body).mp sourceSafe).2.2
  have encodedBodySafe : binderSafeAt "NQuote" (Γ.length + 1)
      (encodeTerm body) = true := by
    rw [encodeTerm_quoteSafe]
    exact bodySafe
  exact encode_comm_target_eq_instantiate payload body
    (isWellScopedAt_of_binderSafeAt "NQuote" encodedBodySafe)

/-- The open COMM witness uses the same binder-eliminating substitution.
Its quoted payload is generated from the ambient context, rather than being
an authored literal quote. -/
theorem open_comm_target_eq_instantiate :
    encodeTerm openCommTarget =
      instantiateBVar (.apply "NQuote" [encodeTerm openCommPayload])
        (encodeTerm openCommContinuation) := by
  rw [← terms_openCommTarget]
  exact encode_comm_target_of_source_safe openCommAmbientName
    openCommPayload openCommContinuation (by
      rw [terms_openCommSource]
      exact openCommSource_quoteSafe)

/-- A quoted payload that is itself literal-safe at the sealed boundary
keeps the generated COMM target inside the literal source fragment. The
continuation may depend on any variable in its binder-extended context. -/
theorem comm_target_literal_safe_of_payload_safe {Γ : Ctx sig}
    (payload : Term sig Γ Srt.pr)
    (body : Term sig (Srt.nm :: Γ) Srt.pr)
    (payloadSafe : intrinsicQuoteSafe 0 payload = true)
    (bodySafe : intrinsicQuoteSafe (Γ.length + 1) body = true) :
    binderSafeAt "NQuote" Γ.length
      (encodeTerm (commTarget raw payload body)) = true := by
  have encodedBodySafe : binderSafeAt "NQuote" (Γ.length + 1)
      (encodeTerm body) = true := by
    rw [encodeTerm_quoteSafe]
    exact bodySafe
  have bodyScope : (encodeTerm body).isWellScopedAt (Γ.length + 1) = true :=
    isWellScopedAt_of_binderSafeAt "NQuote" encodedBodySafe
  have encodedPayloadSafe : binderSafeAt "NQuote" 0
      (encodeTerm payload) = true := by
    rw [encodeTerm_quoteSafe]
    exact payloadSafe
  have quotedSafe : binderSafeAt "NQuote" Γ.length
      (.apply "NQuote" [encodeTerm payload]) = true := by
    simpa [binderSafeAt] using encodedPayloadSafe
  rw [encode_comm_target_eq_instantiate payload body bodyScope]
  exact binderSafeAt_instantiateBVar "NQuote"
    (.apply "NQuote" [encodeTerm payload]) Γ.length
    quotedSafe (encodeTerm body) encodedBodySafe

/-- Encoded intrinsic communication substitution is ordinary locally
nameless opening on the quote-safe one-name continuation. -/
theorem encode_comm_target_eq_open
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr)
    (payloadSafe : intrinsicQuoteSafe 0 payload = true)
    (bodySafe : intrinsicQuoteSafe 1 body = true) :
    encodeTerm (commTarget raw payload body) =
      openBVar 0 (.apply "NQuote" [encodeTerm payload])
        (encodeTerm body) := by
  let quoted : Pattern := .apply "NQuote" [encodeTerm payload]
  have bodyScope : (encodeTerm body).isWellScopedAt 1 = true := by
    apply isWellScopedAt_of_binderSafeAt "NQuote"
    rw [encodeTerm_quoteSafe]
    exact bodySafe
  have payloadScope : (encodeTerm payload).isWellScopedAt 0 = true := by
    apply isWellScopedAt_of_binderSafeAt "NQuote"
    rw [encodeTerm_quoteSafe]
    exact payloadSafe
  have quoteScope : quoted.isWellScoped = true := by
    simpa [quoted, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt] using payloadScope
  calc
    encodeTerm (commTarget raw payload body) =
        instantiateBVar quoted (encodeTerm body) :=
      encode_comm_target_eq_instantiate payload body bodyScope
    _ = openBVar 0 quoted (encodeTerm body) := by
      exact instantiateBVarAt_eq_openBVar_of_isWellScoped bodyScope quoteScope

/-- The intrinsic COMM reduct also inhabits the declaration-derived closed
process carrier. Quote-safe opening is the missing preservation law: admission
of the authored reduct alone would not establish admission of this distinct
intrinsic representative. -/
theorem intrinsic_comm_target_admitted_of_safe
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr)
    (payloadSafe : intrinsicQuoteSafe 0 payload = true)
    (bodySafe : intrinsicQuoteSafe 1 body = true) :
    RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (encodeTerm (commTarget raw payload body)) := by
  have encodedPayloadSafe :
      binderSafeAt "NQuote" 0 (encodeTerm payload) = true := by
    rw [encodeTerm_quoteSafe]
    exact payloadSafe
  have quotedSafe :
      binderSafeAt "NQuote" 0
        (.apply "NQuote" [encodeTerm payload]) = true := by
    simpa [binderSafeAt] using encodedPayloadSafe
  have encodedBodySafe :
      binderSafeAt "NQuote" 1 (encodeTerm body) = true := by
    rw [encodeTerm_quoteSafe]
    exact bodySafe
  have openedSafe := binderSafeAt_openBVar "NQuote"
    (.apply "NQuote" [encodeTerm payload]) quotedSafe
    (encodeTerm body) 0 encodedBodySafe
  rw [← encode_comm_target_eq_open payload body payloadSafe bodySafe] at openedSafe
  let target : Term sig [] Srt.pr := commTarget raw payload body
  have safetyEq := encodeTerm_quoteSafe target 0
  have targetSafe :
      intrinsicQuoteSafe 0 (commTarget raw payload body) = true := by
    exact safetyEq ▸ openedSafe
  exact (encoded_process_admitted_iff_quoteSafe _).mpr targetSafe

/-- The authored COMM evaluator and intrinsic clone substitution agree up to
the established residual equivalence on every quote-safe closed-context
continuation. The quotient is substantive: direct structural congruence is
false even on this domain. -/
theorem semantic_comm_target_residual_equiv
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr)
    (payloadSafe : intrinsicQuoteSafe 0 payload = true)
    (bodySafe : intrinsicQuoteSafe 1 body = true) :
    ProcResidualEquiv
      (semanticCommSubst (encodeTerm body) (encodeTerm payload))
      (encodeTerm (commTarget raw payload body)) := by
  have shape : rhoProcCoreShape (encodeTerm body) = true :=
    encodedTerm_coreShape body
  have bodySafePattern : binderSafeAt "NQuote" 1 (encodeTerm body) = true := by
    rw [encodeTerm_quoteSafe]
    exact bodySafe
  have hOpaque : noBoundUnderQuote 0 (encodeTerm body) = true :=
    noBoundUnderQuote_of_binderSafeAt (encodeTerm body) 0 bodySafePattern
  have direct := semanticCommSubst_transport_to_representative
    (encodeTerm body) (encodeTerm payload)
  have representative :=
    semanticCommRepresentative_residual_equiv_rhoOpenNameBVar_of_rhoProcCoreShape
      shape hOpaque (q := encodeTerm payload)
  have opening := rhoOpenNameBVar_eq_openBVar_of_noBoundUnderQuote
    (u := .apply "NQuote" [encodeTerm payload]) hOpaque
  rw [opening] at representative
  rw [← encode_comm_target_eq_open payload body payloadSafe bodySafe]
    at representative
  exact ProcResidualEquiv.trans direct representative

/-- The authored hash-bag wrapper can be removed up to structural
congruence after transporting the one selected COMM target. -/
theorem authored_comm_target_residual_equiv
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr)
    (payloadSafe : intrinsicQuoteSafe 0 payload = true)
    (bodySafe : intrinsicQuoteSafe 1 body = true) :
    ProcResidualEquiv
      (Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.authoredResult
        payload body)
      (encodeTerm (commTarget raw payload body)) := by
  have pointwise := semantic_comm_target_residual_equiv
    payload body payloadSafe bodySafe
  have whole : ProcResidualEquiv
      (.collection .hashBag
        [semanticCommSubst (encodeTerm body) (encodeTerm payload)] none)
      (.collection .hashBag
        [encodeTerm (commTarget raw payload body)] none) := by
    apply ProcResidualEquiv.collection_cong .hashBag
      [semanticCommSubst (encodeTerm body) (encodeTerm payload)]
      [encodeTerm (commTarget raw payload body)] none rfl
    intro index leftBound rightBound
    have zero : index = 0 := by
      have small : index < 1 := by simpa using leftBound
      omega
    subst zero
    simpa using pointwise
  exact ProcResidualEquiv.trans whole
    (ProcResidualEquiv.struct
      (StructuralCongruence.par_singleton
        (encodeTerm (commTarget raw payload body))))

/-- Every quote-safe intrinsic COMM generator has an actual authored
closed-process firing at a structurally congruent source, and the two
immediate targets agree for every observation saturated under residual
equivalence. -/
theorem authored_comm_residual_simulation
    (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr)
    (channelSafe : intrinsicQuoteSafe 0 channel = true)
    (payloadSafe : intrinsicQuoteSafe 0 payload = true)
    (bodySafe : intrinsicQuoteSafe 1 body = true) :
    RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.authoredInputFirst
        channel payload body) ∧
    RhoStep
      (Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.authoredInputFirst
        channel payload body)
      (Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.authoredResult
        payload body) ∧
    StructuralCongruence
      (encodeTerm (Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.intrinsicSource
        channel payload body))
      (Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.authoredInputFirst
        channel payload body) ∧
    ProcResidualEquiv
      (Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.authoredResult
        payload body)
      (encodeTerm (commTarget raw payload body)) := by
  have cover :=
    Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.comm_closed_source_and_rule_cover
      channel payload body channelSafe payloadSafe bodySafe
  exact ⟨cover.2.1, cover.2.2.2.2.1, cover.2.2.2.1,
    authored_comm_target_residual_equiv payload body payloadSafe bodySafe⟩

/-- The two compared COMM reducts are both admitted closed processes. This
retains the authored firing and the precise residual comparison without
identifying their separate histories. -/
theorem authored_comm_both_targets_admitted
    (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr)
    (channelSafe : intrinsicQuoteSafe 0 channel = true)
    (payloadSafe : intrinsicQuoteSafe 0 payload = true)
    (bodySafe : intrinsicQuoteSafe 1 body = true) :
    RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.authoredResult
        payload body) ∧
    RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (encodeTerm (commTarget raw payload body)) ∧
    RhoStep
      (Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.authoredInputFirst
        channel payload body)
      (Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.authoredResult
        payload body) ∧
    ProcResidualEquiv
      (Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.authoredResult
        payload body)
      (encodeTerm (commTarget raw payload body)) := by
  have cover :=
    Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.comm_closed_source_and_rule_cover
      channel payload body channelSafe payloadSafe bodySafe
  exact ⟨cover.2.2.1,
    intrinsic_comm_target_admitted_of_safe payload body payloadSafe bodySafe,
    cover.2.2.2.2.1,
    authored_comm_target_residual_equiv payload body payloadSafe bodySafe⟩

/-- Every residual-saturated process observation agrees on the authored and
intrinsic immediate COMM results on the admitted quote-safe domain. -/
theorem residualObservation_agrees_of_safe
    (φ : ProcPred) (respects : ProcPredRespectsResidualEquiv φ)
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr)
    (payloadSafe : intrinsicQuoteSafe 0 payload = true)
    (bodySafe : intrinsicQuoteSafe 1 body = true) :
    φ (Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.authoredResult
        payload body) ↔
      φ (encodeTerm (commTarget raw payload body)) := by
  have comparison := authored_comm_target_residual_equiv
    payload body payloadSafe bodySafe
  constructor
  · exact respects comparison
  · exact respects (ProcResidualEquiv.symm comparison)

/-- The selected unquote continuation witnesses both sides of the boundary:
the general comparison applies to it, while structural congruence still
distinguishes the immediate results. -/
theorem unquote_result_residual_but_not_structural :
    ProcResidualEquiv
      Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding.authoredCommReduct
      (encodeTerm RhoSchema.commTarget) ∧
    ¬ StructuralCongruence
      Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding.authoredCommReduct
      (encodeTerm RhoSchema.commTarget) := by
  let body : Term sig [Srt.nm] Srt.pr :=
    Term.op Op.drp (.cons (.var .zero) .nil)
  have comparison := authored_comm_target_residual_equiv nilP body
    (by decide +kernel) (by decide +kernel)
  constructor
  · change ProcResidualEquiv
      Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding.authoredCommReduct
      (encodeTerm RhoSchema.commTarget) at comparison
    exact comparison
  · exact fun congruence =>
      Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding.notStructurallyCongruent
        (StructuralCongruence.symm _ _ congruence)

#print axioms noBVar_of_scope
#print axioms noBoundUnderQuote_of_binderSafeAt
#print axioms encodedTerm_coreShape
#print axioms encode_comm_target_eq_open
#print axioms intrinsic_comm_target_admitted_of_safe
#print axioms semantic_comm_target_residual_equiv
#print axioms authored_comm_target_residual_equiv
#print axioms authored_comm_residual_simulation
#print axioms authored_comm_both_targets_admitted
#print axioms residualObservation_agrees_of_safe
#print axioms unquote_result_residual_but_not_structural

end Mettapedia.OSLF.Binding.RhoQuoteSafeCommComparison
