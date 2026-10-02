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

theorem substituteNameMark_closed (depth : Nat) (replacement : Pattern) {name : Pattern}
    (closed : name.isWellScopedAt 0 = true) :
    substituteNameMark wrappedRhoDeclaration depth replacement name =
      (normalizeReflective wrappedRhoDeclaration name, false) := by
  have normalizedSafe := normalizeReflective_scoped wrappedRhoDeclaration closed
  unfold substituteNameMark
  cases normalized : normalizeReflective wrappedRhoDeclaration name <;> try rfl
  case bvar index =>
    rw [normalized] at normalizedSafe
    simp [Pattern.isWellScopedAt] at normalizedSafe

theorem NameImage.quote_source_closed {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : NameImage depth source (.quote term)) :
    source.isWellScopedAt 0 = true := by
  cases image with
  | baseZeroQuote => rfl
  | quote code => simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using code.scoped

private theorem normalized_source_readout {depth : Nat} {source : Pattern}
    {name : CostName LiteralAuthority} (image : NameImage depth source name)
    (encoding : SignatureNameEncoding LiteralAuthority) :
    StructuralCongruence (eraseGenerated (normalizeReflective wrappedRhoDeclaration source))
      (name.erase encoding) :=
  .trans _ _ _ (eraseGenerated_normalizeReflective source)
    (.symm _ _ (image.erase_structural encoding))

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
      simp only [substituteNameMark, normalizeReflective, beq_self_eq_true, ite_true,
        CostName.substitute, CostName.erase]
      rw [payloadSafe.erase_liftAbove_eq (signatureName := encoding)
        (scope := 0) (cutoff := 0) (amount := depth) (le_refl 0)]
      exact applyCongruence_of_forall₂ "NQuote"
        (.cons (.trans _ _ _ (eraseGenerated_normalizeReflective payloadSource)
          (.symm _ _ (payloadImage.erase_structural encoding))) .nil)
    · have notHigher : ¬depth < index := by omega
      simp [substituteNameMark, normalizeReflective, CostName.substitute,
        CostName.erase, matched, notHigher]
      exact .refl _
  | baseZeroQuote =>
    rw [substituteNameMark_closed depth _ (by rfl)]
    exact normalized_source_readout (NameImage.baseZeroQuote (depth := depth + 1)) encoding
  | quote code =>
    rw [substituteNameMark_closed depth _ (NameImage.quote_source_closed (NameImage.quote (depth := depth + 1) code))]
    exact normalized_source_readout (NameImage.quote (depth := depth + 1) code) encoding

private theorem substitute_drop_quote_erasure {depth : Nat} {source payloadSource : Pattern}
    {quoted payload : CostTerm LiteralAuthority}
    (image : NameImage (depth + 1) source (.quote quoted))
    (encoding : SignatureNameEncoding LiteralAuthority) :
    StructuralCongruence
      (eraseGenerated (substituteReflective wrappedRhoDeclaration depth
        (generatedReplacement payloadSource) (.apply "$cost:wrapped-constructor:PDrop" [source])))
      ((CostTerm.substitute payload depth (.drop (.quote quoted))).erase encoding) := by
  have closedMark := substituteNameMark_closed depth (generatedReplacement payloadSource)
    image.quote_source_closed
  have actual : substituteReflective wrappedRhoDeclaration depth
      (generatedReplacement payloadSource) (.apply "$cost:wrapped-constructor:PDrop" [source]) =
      .apply "$cost:wrapped-constructor:PDrop" [normalizeReflective wrappedRhoDeclaration source] := by
    change (let (name, matched) := substituteNameMark wrappedRhoDeclaration depth (generatedReplacement payloadSource) source;
      match name, matched with
      | .apply quote [process], true =>
        if quote == wrappedRhoDeclaration.quoteConstructor then process
        else .apply "$cost:wrapped-constructor:PDrop" [name]
      | _, _ => .apply "$cost:wrapped-constructor:PDrop" [name]) = _
    rw [closedMark]
    generalize normalizeReflective wrappedRhoDeclaration source = normalized
    cases normalized <;> try rfl
    case apply constructor arguments =>
      cases arguments with
      | nil => rfl
      | cons argument arguments => cases arguments <;> rfl
  rw [actual]
  exact applyCongruence_of_forall₂ "PDrop"
    (.cons (normalized_source_readout image encoding) .nil)

theorem NameImage.substituteReflective_eq_mark {scope depth : Nat} {source : Pattern}
    {name : CostName LiteralAuthority} (image : NameImage scope source name)
    (replacement : Pattern) :
    substituteReflective wrappedRhoDeclaration depth replacement source =
      (substituteNameMark wrappedRhoDeclaration depth replacement source).1 := by
  cases image with
  | @bvar _ index bound =>
    by_cases matched : index = depth <;>
      simp [substituteReflective, substituteNameMark, normalizeReflective, matched]
  | baseZeroQuote => rfl
  | quote code => rfl

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
    cases image with
    | zero => exact .symm _ _ .par_empty
    | drop name =>
      cases name with
      | @bvar _ index bound =>
        by_cases matched : index = depth
        · subst index
          simp only [substituteReflective, substituteNameMark, normalizeReflective,
            generatedReplacement, CostTerm.substitute, beq_self_eq_true, ite_true]
          rw [payloadSafe.erase_liftAbove_eq (signatureName := encoding)
            (scope := 0) (cutoff := 0) (amount := depth) (le_refl 0)]
          exact .trans _ _ _ (eraseGenerated_normalizeReflective payloadSource)
            (.symm _ _ (payloadImage.erase_structural encoding))
        · have notHigher : ¬depth < index := by omega
          simp [substituteReflective, substituteNameMark, normalizeReflective,
            CostTerm.substitute, CostTerm.erase, CostName.erase, matched, notHigher]
          exact .refl _
      | baseZeroQuote => exact substitute_drop_quote_erasure .baseZeroQuote encoding
      | quote code => exact substitute_drop_quote_erasure (.quote code) encoding
    | signed _ _ process => exact process.substitute_erasure payloadImage payloadSafe encoding
    | collection codes => exact codes.substitute_erasure payloadImage payloadSafe encoding

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
