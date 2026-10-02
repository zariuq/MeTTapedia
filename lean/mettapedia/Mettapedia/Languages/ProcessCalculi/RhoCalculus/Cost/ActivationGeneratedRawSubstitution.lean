import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedRawNormalization
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedSubstitutionClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationRawEncoding

/-!
# Exact raw normal comparison for arbitrary admitted receiver substitution

The actual wrapped reflective operation is decoded structurally. Its readout
has the same raw normal form as the existing binder-eliminating communication
operation. Closed payloads and the anonymous receiver domain remain explicit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

mutual
  theorem NameImage.liftAbove_eq {scope cutoff : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage scope source name)
      (larger : scope ≤ cutoff) (amount : Nat) : name.lift amount cutoff = name := by
    cases image with
    | @bvar _ index bound => simp [CostName.lift, show ¬cutoff ≤ index from by omega]
    | baseZeroQuote => rfl
    | quote code => rfl

  theorem CodeImage.liftAbove_eq {scope cutoff : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeImage scope source term)
      (larger : scope ≤ cutoff) (amount : Nat) : term.lift amount cutoff = term := by
    cases image with
    | zero => rfl
    | drop name => simp only [CostTerm.lift, name.liftAbove_eq larger amount]
    | signed signature accepted process => simp only [CostTerm.lift, process.liftAbove_eq larger amount]
    | collection codes => exact codes.liftAbove_eq larger amount

  theorem ProcImage.liftAbove_eq {scope cutoff : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage scope source process)
      (larger : scope ≤ cutoff) (amount : Nat) : process.lift amount cutoff = process := by
    cases image with
    | zero => rfl
    | send name code => simp only [CostProc.lift, name.liftAbove_eq larger amount, code.liftAbove_eq larger amount]
    | recv name code =>
      simp only [CostProc.lift, name.liftAbove_eq larger amount,
        code.liftAbove_eq (Nat.add_le_add_right larger 1) amount]
    | pair left right => simp only [CostProc.lift, left.liftAbove_eq larger amount, right.liftAbove_eq larger amount]

  theorem CodeListImage.liftAbove_eq {scope cutoff : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage scope sources term)
      (larger : scope ≤ cutoff) (amount : Nat) : term.lift amount cutoff = term := by
    cases image with
    | nil => rfl
    | cons head tail => simp only [CostTerm.lift, head.liftAbove_eq larger amount, tail.liftAbove_eq larger amount]
end

theorem NameImage.literal_substitute_raw_readout {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : NameImage (depth + 1) source (.quote term))
    (replacement : Pattern) :
    ∃ normalized, NameImage depth
      (substituteReflective wrappedRhoDeclaration depth replacement source) normalized ∧
      (literalEncodeName (.quote term)).normalize = (literalEncodeName normalized).normalize := by
  obtain ⟨normalized, normalizedImage, same⟩ := image.quote_closed_image.normalize_raw_readout
  rw [image.substituteReflective_eq_mark,
    substituteNameMark_closed depth replacement image.quote_source_closed]
  exact ⟨normalized, normalizedImage.weaken (Nat.zero_le depth), same⟩

theorem NameImage.substitute_raw_readout {depth : Nat} {source payloadSource : Pattern}
    {name : CostName LiteralAuthority} {payload : CostTerm LiteralAuthority}
    (image : NameImage (depth + 1) source name) (payloadImage : CodeImage 0 payloadSource payload) :
    ∃ result, NameImage depth
      (substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource) source) result ∧
      (literalEncodeName (CostName.substitute payload depth name)).normalize =
        (literalEncodeName result).normalize := by
  cases image with
  | @bvar _ index bound =>
    by_cases matched : index = depth
    · subst index
      obtain ⟨normalized, normalizedImage, same⟩ := payloadImage.normalize_raw_readout
      simp only [substituteReflective, beq_self_eq_true, ite_true, generatedReplacement]
      refine ⟨_, .quote normalizedImage, ?_⟩
      rw [CostName.substitute, if_pos rfl, payloadImage.liftAbove_eq (le_refl 0) depth]
      exact raw_quote_normalize_congr same
    · simp only [substituteReflective, beq_iff_eq, matched, ite_false]
      refine ⟨_, .bvar (by omega), ?_⟩
      simp [CostName.substitute, matched, show ¬depth < index from by omega]
  | baseZeroQuote => exact NameImage.literal_substitute_raw_readout .baseZeroQuote _
  | quote code => exact NameImage.literal_substitute_raw_readout (.quote code) _

private theorem drop_literal_substitute_raw_readout {depth : Nat} {source payloadSource : Pattern}
    {quoted payload : CostTerm LiteralAuthority} (image : NameImage (depth + 1) source (.quote quoted)) :
    ∃ result, CodeImage depth
      (substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource)
        (.apply "$cost:wrapped-constructor:PDrop" [source])) result ∧
      (literalEncodeTerm (CostTerm.substitute payload depth (.drop (.quote quoted)))).normalize =
        (literalEncodeTerm result).normalize := by
  rw [substituteReflective_drop_closed depth _ image.quote_source_closed]
  obtain ⟨normalized, normalizedImage, same⟩ := image.quote_closed_image.normalize_raw_readout
  refine ⟨_, .drop (normalizedImage.weaken (Nat.zero_le depth)), ?_⟩
  change RawCostTerm.drop (literalEncodeName (.quote quoted)).normalize =
    RawCostTerm.drop (literalEncodeName normalized).normalize
  rw [same]

mutual
  theorem CodeImage.substitute_raw_readout {depth : Nat} {source payloadSource : Pattern}
      {term payload : CostTerm LiteralAuthority} (image : CodeImage (depth + 1) source term)
      (payloadImage : CodeImage 0 payloadSource payload) :
      ∃ result, CodeImage depth
        (substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource) source) result ∧
        (literalEncodeTerm (CostTerm.substitute payload depth term)).normalize =
          (literalEncodeTerm result).normalize := by
    cases image with
    | zero => exact ⟨_, .zero, rfl⟩
    | drop name =>
      cases name with
      | @bvar _ index bound =>
        by_cases matched : index = depth
        · subst index
          obtain ⟨normalized, normalizedImage, same⟩ := payloadImage.normalize_raw_readout
          simp only [substituteReflective, substituteNameMark, normalizeReflective,
            generatedReplacement, beq_self_eq_true, ite_true]
          refine ⟨_, normalizedImage.weaken (Nat.zero_le depth), ?_⟩
          rw [CostTerm.substitute, if_pos rfl, payloadImage.liftAbove_eq (le_refl 0) depth]
          exact same
        · simp only [substituteReflective, substituteNameMark, normalizeReflective,
            beq_iff_eq, matched, ite_false]
          refine ⟨_, .drop (.bvar (by omega)), ?_⟩
          simp [CostTerm.substitute, matched, show ¬depth < index from by omega]
      | baseZeroQuote => exact drop_literal_substitute_raw_readout .baseZeroQuote
      | quote code => exact drop_literal_substitute_raw_readout (.quote code)
    | signed signature accepted process =>
      obtain ⟨result, resultImage, same⟩ := process.substitute_raw_readout payloadImage
      change ∃ result, CodeImage depth (.apply "$cost:apparatus-constructor:signed"
        [substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource) _,
         substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource) _]) result ∧ _
      rw [signature?_accepted_substitution_identity accepted]
      refine ⟨_, .signed signature accepted resultImage, ?_⟩
      change RawCostTerm.signed (literalEncodeProc (CostProc.substitute payload depth _)).normalize _ =
        RawCostTerm.signed (literalEncodeProc result).normalize _
      rw [same]
    | collection codes =>
      obtain ⟨result, resultImage, same⟩ := codes.substitute_raw_readout payloadImage
      exact ⟨_, .collection resultImage, same⟩

  theorem ProcImage.substitute_raw_readout {depth : Nat} {source payloadSource : Pattern}
      {process : CostProc LiteralAuthority} {payload : CostTerm LiteralAuthority}
      (image : ProcImage (depth + 1) source process) (payloadImage : CodeImage 0 payloadSource payload) :
      ∃ result, ProcImage depth
        (substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource) source) result ∧
        (literalEncodeProc (CostProc.substitute payload depth process)).normalize =
          (literalEncodeProc result).normalize := by
    cases image with
    | zero => exact ⟨_, .zero, rfl⟩
    | send name code =>
      obtain ⟨resultName, nameImage, nameSame⟩ := name.substitute_raw_readout payloadImage
      obtain ⟨resultCode, codeImage, codeSame⟩ := code.substitute_raw_readout payloadImage
      refine ⟨_, .send nameImage codeImage, ?_⟩
      change RawCostProc.send (literalEncodeName (CostName.substitute payload depth _)).normalize
        (literalEncodeTerm (CostTerm.substitute payload depth _)).normalize =
        RawCostProc.send (literalEncodeName resultName).normalize (literalEncodeTerm resultCode).normalize
      rw [nameSame, codeSame]
    | recv name code =>
      obtain ⟨resultName, nameImage, nameSame⟩ := name.substitute_raw_readout payloadImage
      obtain ⟨resultCode, codeImage, codeSame⟩ := code.substitute_raw_readout payloadImage
      refine ⟨_, .recv nameImage codeImage, ?_⟩
      change RawCostProc.recv (literalEncodeName (CostName.substitute payload depth _)).normalize
        (literalEncodeTerm (CostTerm.substitute payload (depth + 1) _)).normalize =
        RawCostProc.recv (literalEncodeName resultName).normalize (literalEncodeTerm resultCode).normalize
      rw [nameSame, codeSame]
    | pair left right =>
      obtain ⟨resultLeft, leftImage, leftSame⟩ := left.substitute_raw_readout payloadImage
      obtain ⟨resultRight, rightImage, rightSame⟩ := right.substitute_raw_readout payloadImage
      exact ⟨_, .pair leftImage rightImage, raw_proc_par_normalize_congr leftSame rightSame⟩

  theorem CodeListImage.substitute_raw_readout {depth : Nat} {sources : List Pattern}
      {payloadSource : Pattern} {term payload : CostTerm LiteralAuthority}
      (image : CodeListImage (depth + 1) sources term) (payloadImage : CodeImage 0 payloadSource payload) :
      ∃ result, CodeListImage depth
        (substituteReflectiveList wrappedRhoDeclaration depth (generatedReplacement payloadSource) sources) result ∧
        (literalEncodeTerm (CostTerm.substitute payload depth term)).normalize =
          (literalEncodeTerm result).normalize := by
    cases image with
    | nil => exact ⟨_, .nil, rfl⟩
    | cons head tail =>
      obtain ⟨resultHead, headImage, headSame⟩ := head.substitute_raw_readout payloadImage
      obtain ⟨resultTail, tailImage, tailSame⟩ := tail.substitute_raw_readout payloadImage
      exact ⟨_, .cons headImage tailImage, raw_term_par_normalize_congr headSame tailSame⟩
end

theorem code_parser_commSubst_raw_readout {bodyFuel payloadFuel : Nat}
    {bodySource payloadSource : Pattern} {body payload : CostTerm LiteralAuthority}
    (bodyParsed : (code? bodyFuel 1 bodySource).map Subtype.val = some body)
    (payloadParsed : (code? payloadFuel 0 payloadSource).map Subtype.val = some payload) :
    ∃ result fuel, (code? fuel 0
      (substituteReflective wrappedRhoDeclaration 0 (generatedReplacement payloadSource) bodySource)).map
        Subtype.val = some result ∧
      ((literalEncodeTerm body).commSubst (literalEncodeTerm payload)).normalize =
        (literalEncodeTerm result).normalize := by
  obtain ⟨result, image, same⟩ := (code_parser_image bodyParsed).substitute_raw_readout
    (code_parser_image payloadParsed)
  obtain ⟨fuel, readback⟩ := image.parser_eventually
  refine ⟨result, fuel, readback fuel (le_refl fuel), ?_⟩
  rw [← literalEncodeTerm_commSubst]
  exact same

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
