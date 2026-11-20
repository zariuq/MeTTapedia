import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedImage
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedNormalization
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ScopedErasure

/-!
# Generated reflective substitution on admitted receiver code

The actual wrapped substitution and binder-eliminating cost substitution
agree through apparatus erasure on the parser's closed receiver domain.
Literal target syntax and authority keys are not identified by this observer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

def generatedReplacement (payload : Pattern) : Pattern :=
  .apply "$cost:wrapped-constructor:NQuote" [normalizeReflective wrappedRhoDeclaration payload]

theorem substituteReflective_collection (depth : Nat) (replacement : Pattern)
    (kind : CollType) (elements : List Pattern) (rest : Option String) :
    substituteReflective wrappedRhoDeclaration depth replacement (.collection kind elements rest) =
      .collection kind (substituteReflectiveList wrappedRhoDeclaration depth replacement elements) rest := by
  simp [substituteReflective, substituteReflectiveList, resolveQuotes, resolveQuotesList_eq_map,
    substituteResolved, substituteResolvedList_eq_map, List.map_map, Function.comp_def]

theorem NameImage.quote_source_closed {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : NameImage depth source (.quote term)) :
    source.isWellScopedAt 0 = true := by
  cases image with
  | baseZeroQuote => rfl
  | quote code => simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using code.scoped

private theorem resolved_source_readout {depth : Nat} {source : Pattern}
    {name : CostName LiteralAuthority} (image : NameImage depth source name)
    (encoding : SignatureNameEncoding LiteralAuthority) :
    StructuralCongruence (eraseGenerated (resolveQuotes wrappedRhoDeclaration source))
      (name.erase encoding) :=
  .trans _ _ _ (eraseGenerated_resolveQuotes source)
    (.symm _ _ (image.erase_structural encoding))

/-- A closed name misses every binder, and substitution resolves it. -/
theorem closed_miss {depth : Nat} {replacement source : Pattern}
    (closed : source.isWellScopedAt 0 = true) :
    matchesBinder wrappedRhoDeclaration depth (resolveQuotes wrappedRhoDeclaration source) = false ∧
      substituteReflective wrappedRhoDeclaration depth replacement source =
        resolveQuotes wrappedRhoDeclaration source := by
  have mark := substituteNameMark_closed wrappedRhoDeclaration depth replacement closed
  unfold substituteNameMark at mark
  by_cases hit : matchesBinder wrappedRhoDeclaration depth (resolveQuotes wrappedRhoDeclaration source) = true
  · rw [if_pos hit] at mark
    simp at mark
  · rw [if_neg hit] at mark
    exact ⟨by simpa using hit, (Prod.mk.inj mark).1⟩

theorem NameImage.substitute_erasure {depth : Nat} {source payloadSource : Pattern}
    {name : CostName LiteralAuthority} {payload : CostTerm LiteralAuthority}
    (image : NameImage (depth + 1) source name)
    (payloadImage : CodeImage 0 payloadSource payload) (payloadSafe : payload.BinderSafe)
    (encoding : SignatureNameEncoding LiteralAuthority) :
    StructuralCongruence
      (eraseGenerated (substituteNameMark wrappedRhoDeclaration depth
        (generatedReplacement payloadSource) source).1)
      ((CostName.substitute payload depth name).erase encoding) := by
  cases image with
  | @bvar _ index bound =>
    by_cases matched : index = depth
    · subst index
      simp only [substituteNameMark, resolveQuotes, matchesBinder_bvar, beq_self_eq_true, ite_true,
        CostName.substitute, CostName.erase]
      rw [payloadSafe.erase_liftAbove_eq (signatureName := encoding)
        (scope := 0) (cutoff := 0) (amount := depth) (le_refl 0)]
      exact applyCongruence_of_forall₂ "NQuote"
        (.cons (.trans _ _ _ (eraseGenerated_normalizeReflective payloadSource)
          (.symm _ _ (payloadImage.erase_structural encoding))) .nil)
    · have notHigher : ¬depth < index := by omega
      simp [substituteNameMark, substituteReflective, resolveQuotes, substituteResolved,
        CostName.substitute, CostName.erase, matched, notHigher]
      exact .refl _
  | baseZeroQuote =>
    rw [substituteNameMark_closed wrappedRhoDeclaration depth _ (by rfl)]
    exact resolved_source_readout (NameImage.baseZeroQuote (depth := depth + 1)) encoding
  | quote code =>
    rw [substituteNameMark_closed wrappedRhoDeclaration depth _
      (NameImage.quote_source_closed (NameImage.quote (depth := depth + 1) code))]
    exact resolved_source_readout (NameImage.quote (depth := depth + 1) code) encoding

private theorem substitute_drop_quote_erasure {depth : Nat} {source payloadSource : Pattern}
    {quoted payload : CostTerm LiteralAuthority}
    (image : NameImage (depth + 1) source (.quote quoted))
    (encoding : SignatureNameEncoding LiteralAuthority) :
    StructuralCongruence
      (eraseGenerated (substituteReflective wrappedRhoDeclaration depth
        (generatedReplacement payloadSource) (.apply "$cost:wrapped-constructor:PDrop" [source])))
      ((CostTerm.substitute payload depth (.drop (.quote quoted))).erase encoding) := by
  obtain ⟨miss, substituted⟩ := closed_miss (depth := depth)
    (replacement := generatedReplacement payloadSource) image.quote_source_closed
  have notQuote : "$cost:wrapped-constructor:PDrop" ≠ wrappedRhoDeclaration.quoteConstructor := by
    decide +kernel
  have distinct : wrappedRhoDeclaration.dropConstructor ≠ wrappedRhoDeclaration.quoteConstructor := by
    decide +kernel
  have actual : substituteReflective wrappedRhoDeclaration depth
      (generatedReplacement payloadSource) (.apply "$cost:wrapped-constructor:PDrop" [source]) =
      .apply "$cost:wrapped-constructor:PDrop" [resolveQuotes wrappedRhoDeclaration source] := by
    unfold substituteReflective at substituted ⊢
    simp only [resolveQuotes, resolveQuotesList, finishResolveApply, notQuote, if_false]
    rw [show ("$cost:wrapped-constructor:PDrop" : String) = wrappedRhoDeclaration.dropConstructor from rfl,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.substituteResolved_drop distinct, if_neg (by simpa using miss), substituted]
  rw [actual]
  exact applyCongruence_of_forall₂ "PDrop"
    (.cons (resolved_source_readout image encoding) .nil)

theorem NameImage.substituteReflective_eq_mark {scope depth : Nat} {source : Pattern}
    {name : CostName LiteralAuthority} (image : NameImage scope source name)
    (replacement : Pattern) :
    substituteReflective wrappedRhoDeclaration depth replacement source =
      (substituteNameMark wrappedRhoDeclaration depth replacement source).1 := by
  cases image with
  | @bvar _ index bound =>
    by_cases matched : index = depth <;>
      simp [substituteReflective, substituteNameMark, resolveQuotes, substituteResolved, matched]
  | baseZeroQuote =>
    rw [substituteNameMark_closed wrappedRhoDeclaration depth _ (by rfl)]
    exact (closed_miss (by rfl)).2
  | quote code =>
    have closed := NameImage.quote_source_closed (NameImage.quote (depth := scope) code)
    rw [substituteNameMark_closed wrappedRhoDeclaration depth _ closed]
    exact (closed_miss closed).2

theorem NameImage.substituteReflective_erasure {depth : Nat} {source payloadSource : Pattern}
    {name : CostName LiteralAuthority} {payload : CostTerm LiteralAuthority}
    (image : NameImage (depth + 1) source name)
    (payloadImage : CodeImage 0 payloadSource payload) (payloadSafe : payload.BinderSafe)
    (encoding : SignatureNameEncoding LiteralAuthority) :
    StructuralCongruence
      (eraseGenerated (substituteReflective wrappedRhoDeclaration depth
        (generatedReplacement payloadSource) source))
      ((CostName.substitute payload depth name).erase encoding) := by
  rw [image.substituteReflective_eq_mark]
  exact image.substitute_erasure payloadImage payloadSafe encoding

mutual
  theorem CodeImage.substitute_erasure {depth : Nat} {source payloadSource : Pattern}
      {term payload : CostTerm LiteralAuthority} (image : CodeImage (depth + 1) source term)
      (payloadImage : CodeImage 0 payloadSource payload) (payloadSafe : payload.BinderSafe)
      (encoding : SignatureNameEncoding LiteralAuthority) :
      StructuralCongruence
        (eraseGenerated (substituteReflective wrappedRhoDeclaration depth
          (generatedReplacement payloadSource) source))
        ((CostTerm.substitute payload depth term).erase encoding) := by
    have quoteName : wrappedRhoDeclaration.quoteConstructor = "$cost:wrapped-constructor:NQuote" := rfl
    have dropName : wrappedRhoDeclaration.dropConstructor = "$cost:wrapped-constructor:PDrop" := rfl
    cases image with
    | zero => exact .symm _ _ .par_empty
    | drop name =>
      cases name with
      | @bvar _ index bound =>
        by_cases matched : index = depth
        · subst index
          simp only [substituteReflective, resolveQuotes, resolveQuotesList, finishResolveApply,
            substituteResolved, matchesBinder_bvar, receive, generatedReplacement, quoteName, dropName,
            CostTerm.substitute, beq_self_eq_true, ite_true, String.reduceEq, ite_false]
          rw [payloadSafe.erase_liftAbove_eq (signatureName := encoding)
            (scope := 0) (cutoff := 0) (amount := depth) (le_refl 0)]
          exact .trans _ _ _ (eraseGenerated_normalizeReflective payloadSource)
            (.symm _ _ (payloadImage.erase_structural encoding))
        · have notHigher : ¬depth < index := by omega
          simp [substituteReflective, resolveQuotes, resolveQuotesList, finishResolveApply,
            substituteResolved, quoteName, dropName,
            CostTerm.substitute, CostTerm.erase, CostName.erase, matched, notHigher]
          exact .refl _
      | baseZeroQuote => exact substitute_drop_quote_erasure .baseZeroQuote encoding
      | quote code => exact substitute_drop_quote_erasure (.quote code) encoding
    | signed _ _ process => exact process.substitute_erasure payloadImage payloadSafe encoding
    | collection codes =>
      rw [substituteReflective_collection]
      exact codes.substitute_erasure payloadImage payloadSafe encoding

  theorem ProcImage.substitute_erasure {depth : Nat} {source payloadSource : Pattern}
      {process : CostProc LiteralAuthority} {payload : CostTerm LiteralAuthority}
      (image : ProcImage (depth + 1) source process)
      (payloadImage : CodeImage 0 payloadSource payload) (payloadSafe : payload.BinderSafe)
      (encoding : SignatureNameEncoding LiteralAuthority) :
      StructuralCongruence
        (eraseGenerated (substituteReflective wrappedRhoDeclaration depth
          (generatedReplacement payloadSource) source))
        ((CostProc.substitute payload depth process).erase encoding) := by
    cases image with
    | zero => exact .symm _ _ .par_empty
    | send name code =>
      exact applyCongruence_of_forall₂ "POutput"
        (.cons (name.substituteReflective_erasure payloadImage payloadSafe encoding)
          (.cons (code.substitute_erasure payloadImage payloadSafe encoding) .nil))
    | recv name code =>
      exact applyCongruence_of_forall₂ "PInput"
        (.cons (name.substituteReflective_erasure payloadImage payloadSafe encoding)
          (.cons (.lambda_cong none _ _ (code.substitute_erasure payloadImage payloadSafe encoding)) .nil))
    | pair left right =>
      exact collectionCongruence_of_forall₂ .hashBag none
        (.cons (left.substitute_erasure payloadImage payloadSafe encoding)
          (.cons (right.substitute_erasure payloadImage payloadSafe encoding) .nil))

  theorem CodeListImage.substitute_erasure {depth : Nat} {sources : List Pattern}
      {payloadSource : Pattern} {term payload : CostTerm LiteralAuthority}
      (image : CodeListImage (depth + 1) sources term)
      (payloadImage : CodeImage 0 payloadSource payload) (payloadSafe : payload.BinderSafe)
      (encoding : SignatureNameEncoding LiteralAuthority) :
      StructuralCongruence
        (.collection .hashBag
          (eraseGeneratedList (substituteReflectiveList wrappedRhoDeclaration depth
            (generatedReplacement payloadSource) sources)) none)
        ((CostTerm.substitute payload depth term).erase encoding) := by
    cases image with
    | nil => exact .refl _
    | @cons _ source sources head tail headImage tailImage =>
      exact .trans _ _ _
        (.symm _ _ (.par_flatten
          [eraseGenerated (substituteReflective wrappedRhoDeclaration depth
            (generatedReplacement payloadSource) source)]
          (eraseGeneratedList (substituteReflectiveList wrappedRhoDeclaration depth
            (generatedReplacement payloadSource) sources))))
        (collectionCongruence_of_forall₂ .hashBag none
          (.cons (headImage.substitute_erasure payloadImage payloadSafe encoding)
            (.cons (tailImage.substitute_erasure payloadImage payloadSafe encoding) .nil)))
end

theorem GeneratedCodeImage.commSubst_erasure {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority}
    (bodyImage : GeneratedCodeImage 1 bodySource body)
    (payloadImage : GeneratedCodeImage 0 payloadSource payload)
    (encoding : SignatureNameEncoding LiteralAuthority) :
    StructuralCongruence
      (eraseGenerated (substituteReflective wrappedRhoDeclaration 0
        (generatedReplacement payloadSource) bodySource))
      ((body.commSubst payload).erase encoding) :=
  bodyImage.structural_image.substitute_erasure payloadImage.structural_image
    payloadImage.binderSafe encoding

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
