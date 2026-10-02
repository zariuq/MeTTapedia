import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedReadout
import Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation

/-!
# Structural image of the generated decoder

These inductive graphs expose the constructors returned by the existing
certifying parser. They introduce neither a process carrier nor a reduction.
Quotation resets scope, and signature admission remains the actual checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

mutual
  inductive NameImage : Nat → Pattern → CostName LiteralAuthority → Prop where
    | bvar {depth index} (bound : index < depth) :
        NameImage depth (.bvar index) (.bvar index)
    | baseZeroQuote {depth} : NameImage depth
        (.apply "$cost:base-constructor:NQuote" [.apply "$cost:base-constructor:PZero" []])
        (.quote .nil)
    | quote {depth source term} (code : CodeImage 0 source term) :
        NameImage depth (.apply "$cost:wrapped-constructor:NQuote" [source]) (.quote term)

  inductive CodeImage : Nat → Pattern → CostTerm LiteralAuthority → Prop where
    | zero {depth} : CodeImage depth (.apply "$cost:wrapped-constructor:PZero" []) .nil
    | drop {depth source name} (parsed : NameImage depth source name) :
        CodeImage depth (.apply "$cost:wrapped-constructor:PDrop" [source]) (.drop name)
    | signed {depth core source process} (signature : TypedSignature source) (accepted : signature? source = some signature)
        (parsed : ProcImage depth core process) :
        CodeImage depth (.apply "$cost:apparatus-constructor:signed" [core, source])
          (.signed process signature.val)
    | collection {depth sources term} (parsed : CodeListImage depth sources term) :
        CodeImage depth (.collection .hashBag sources none) term

  inductive ProcImage : Nat → Pattern → CostProc LiteralAuthority → Prop where
    | zero {depth} : ProcImage depth (.apply "$cost:base-constructor:PZero" []) .nil
    | send {depth channel payload name term}
        (channelImage : NameImage depth channel name) (payloadImage : CodeImage depth payload term) :
        ProcImage depth (.apply "$cost:base-constructor:POutput" [channel, payload]) (.send name term)
    | recv {depth channel body name term}
        (channelImage : NameImage depth channel name) (bodyImage : CodeImage (depth + 1) body term) :
        ProcImage depth (.apply "$cost:base-constructor:PInput" [channel, .lambda none body])
          (.recv name term)
    | pair {depth left right first second}
        (leftImage : ProcImage depth left first) (rightImage : ProcImage depth right second) :
        ProcImage depth (.collection .hashBag [left, right] none) (.par first second)

  inductive CodeListImage : Nat → List Pattern → CostTerm LiteralAuthority → Prop where
    | nil {depth} : CodeListImage depth [] .nil
    | cons {depth source sources head tail}
        (headImage : CodeImage depth source head) (tailImage : CodeListImage depth sources tail) :
        CodeListImage depth (source :: sources) (.par head tail)
end

private theorem parser_image :
    (∀ fuel depth source (decoded : DecodedName depth source),
      name? fuel depth source = some decoded → NameImage depth source decoded.val) ∧
    (∀ fuel depth source (decoded : DecodedCode depth source),
      code? fuel depth source = some decoded → CodeImage depth source decoded.val) ∧
    (∀ fuel depth sources (decoded : DecodedCode depth (.collection .hashBag sources none)),
      codeList? fuel depth sources = some decoded → CodeListImage depth sources decoded.val) ∧
    (∀ fuel depth source (decoded : DecodedProc depth source),
      proc? fuel depth source = some decoded → ProcImage depth source decoded.val) := by
  apply name?.mutual_induct
    (motive_1 := fun fuel depth source => ∀ decoded : DecodedName depth source,
      name? fuel depth source = some decoded → NameImage depth source decoded.val)
    (motive_2 := fun fuel depth source => ∀ decoded : DecodedCode depth source,
      code? fuel depth source = some decoded → CodeImage depth source decoded.val)
    (motive_3 := fun fuel depth sources =>
      ∀ decoded : DecodedCode depth (.collection .hashBag sources none),
        codeList? fuel depth sources = some decoded → CodeListImage depth sources decoded.val)
    (motive_4 := fun fuel depth source => ∀ decoded : DecodedProc depth source,
      proc? fuel depth source = some decoded → ProcImage depth source decoded.val)
  · intro source depth decoded parsed
    simp [name?] at parsed
  · intro fuel depth index bound decoded parsed
    simp only [name?, dif_pos bound, Option.some.injEq] at parsed
    cases parsed
    exact .bvar bound
  · intro fuel depth index bound decoded parsed
    simp [name?, bound] at parsed
  · intro fuel depth decoded parsed
    simp only [name?, Option.some.injEq] at parsed
    cases parsed
    exact .baseZeroQuote
  · intro fuel depth source childIH decoded parsed
    cases childParsed : code? fuel 0 source with
    | none => simp [name?, childParsed] at parsed
    | some child =>
      simp only [name?, childParsed] at parsed
      cases parsed
      exact .quote (childIH child childParsed)
  · intro source fuel depth notBvar notBase notWrapped decoded parsed
    simp_all [name?]
  · intro source depth decoded parsed
    simp [code?] at parsed
  · intro fuel depth decoded parsed
    simp only [code?, Option.some.injEq] at parsed
    cases parsed
    exact .zero
  · intro fuel depth source childIH decoded parsed
    cases childParsed : name? fuel depth source with
    | none => simp [code?, childParsed] at parsed
    | some child =>
      simp only [code?, childParsed] at parsed
      cases parsed
      exact .drop (childIH child childParsed)
  · intro fuel depth core authority childIH decoded parsed
    cases signatureParsed : signature? authority with
    | none => simp [code?, signatureParsed] at parsed
    | some signature =>
      cases childParsed : proc? fuel depth core with
      | none => simp [code?, signatureParsed, childParsed] at parsed
      | some child =>
        simp only [code?, signatureParsed, childParsed] at parsed
        cases parsed
        exact .signed signature signatureParsed (childIH child childParsed)
  · intro fuel depth sources childIH decoded parsed
    exact .collection (childIH decoded parsed)
  · intro source fuel depth notZero notDrop notSigned notCollection decoded parsed
    simp_all [code?]
  · intro source depth decoded parsed
    simp [proc?] at parsed
  · intro fuel depth decoded parsed
    simp only [proc?, Option.some.injEq] at parsed
    cases parsed
    exact .zero
  · intro fuel depth channel payload channelIH childIH decoded parsed
    cases channelParsed : name? fuel depth channel with
    | none => simp [proc?, channelParsed] at parsed
    | some name =>
      cases childParsed : code? fuel depth payload with
      | none => simp [proc?, channelParsed, childParsed] at parsed
      | some child =>
        simp only [proc?, channelParsed, childParsed] at parsed
        cases parsed
        exact .send (channelIH name channelParsed) (childIH child childParsed)
  · intro fuel depth channel body channelIH childIH decoded parsed
    cases channelParsed : name? fuel depth channel with
    | none => simp [proc?, channelParsed] at parsed
    | some name =>
      cases childParsed : code? fuel (depth + 1) body with
      | none => simp [proc?, channelParsed, childParsed] at parsed
      | some child =>
        simp only [proc?, channelParsed, childParsed] at parsed
        cases parsed
        exact .recv (channelIH name channelParsed) (childIH child childParsed)
  · intro fuel depth left right leftIH rightIH decoded parsed
    cases leftParsed : proc? fuel depth left with
    | none => simp [proc?, leftParsed] at parsed
    | some first =>
      cases rightParsed : proc? fuel depth right with
      | none => simp [proc?, leftParsed, rightParsed] at parsed
      | some second =>
        simp only [proc?, leftParsed, rightParsed] at parsed
        cases parsed
        exact .pair (leftIH first leftParsed) (rightIH second rightParsed)
  · intro source fuel depth notZero notSend notRecv notPair decoded parsed
    simp_all [proc?]
  · intro sources depth decoded parsed
    simp [codeList?] at parsed
  · intro fuel depth decoded parsed
    simp only [codeList?, Option.some.injEq] at parsed
    cases parsed
    exact .nil
  · intro fuel depth source sources headIH tailIH decoded parsed
    cases headParsed : code? fuel depth source with
    | none => simp [codeList?, headParsed] at parsed
    | some head =>
      cases tailParsed : codeList? fuel depth sources with
      | none => simp [codeList?, headParsed, tailParsed] at parsed
      | some tail =>
        simp only [codeList?, headParsed, tailParsed] at parsed
        cases parsed
        exact .cons (headIH head headParsed) (tailIH tail tailParsed)

theorem name_parser_image {fuel depth : Nat} {source : Pattern}
    {name : CostName LiteralAuthority}
    (parsed : (name? fuel depth source).map Subtype.val = some name) :
    NameImage depth source name := by
  obtain ⟨decoded, found, same⟩ := Option.map_eq_some_iff.mp parsed
  subst name
  exact parser_image.1 fuel _ _ decoded found

theorem code_parser_image {fuel depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority}
    (parsed : (code? fuel depth source).map Subtype.val = some term) :
    CodeImage depth source term := by
  obtain ⟨decoded, found, same⟩ := Option.map_eq_some_iff.mp parsed
  subst term
  exact parser_image.2.1 fuel _ _ decoded found

theorem GeneratedCodeImage.structural_image {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : GeneratedCodeImage depth source term) :
    CodeImage depth source term := by
  obtain ⟨fuel, parsed⟩ := image.2
  exact code_parser_image parsed

mutual
  theorem NameImage.scoped {depth : Nat} {source : Pattern} {name : CostName LiteralAuthority}
      (image : NameImage depth source name) : source.isWellScopedAt depth = true := by
    cases image with
    | bvar bound => simpa [Pattern.isWellScopedAt] using bound
    | baseZeroQuote => rfl
    | quote code =>
      simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using
        isWellScopedAt_mono code.scoped (Nat.zero_le depth)

  theorem CodeImage.scoped {depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority}
      (image : CodeImage depth source term) : source.isWellScopedAt depth = true := by
    cases image with
    | zero => rfl
    | drop name => simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using name.scoped
    | @signed depth core source processTerm signature _ process =>
      have signatureSafe : source.isWellScopedAt depth = true :=
        isWellScopedAt_mono signature.property.2.isWellScopedAt (Nat.zero_le depth)
      simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, process.scoped, signatureSafe]
    | collection codes => exact codes.scoped

  theorem ProcImage.scoped {depth : Nat} {source : Pattern} {process : CostProc LiteralAuthority}
      (image : ProcImage depth source process) : source.isWellScopedAt depth = true := by
    cases image with
    | zero => rfl
    | send name code =>
      simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, name.scoped, code.scoped]
    | recv name code =>
      simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, name.scoped, code.scoped]
    | pair left right =>
      simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, left.scoped, right.scoped]

  theorem CodeListImage.scoped {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term) :
      Pattern.isWellScopedListAt depth sources = true := by
    cases image with
    | nil => rfl
    | cons head tail => simp [Pattern.isWellScopedListAt, head.scoped, tail.scoped]
end

mutual
  theorem NameImage.erase_structural {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage depth source name)
      (encoding : SignatureNameEncoding LiteralAuthority) :
      StructuralCongruence (name.erase encoding) (eraseGenerated source) := by
    cases image with
    | bvar => exact .refl _
    | baseZeroQuote => exact applyCongruence_of_forall₂ "NQuote" (.cons .par_empty .nil)
    | quote code =>
      exact applyCongruence_of_forall₂ "NQuote" (.cons (code.erase_structural encoding) .nil)

  theorem CodeImage.erase_structural {depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeImage depth source term)
      (encoding : SignatureNameEncoding LiteralAuthority) :
      StructuralCongruence (term.erase encoding) (eraseGenerated source) := by
    cases image with
    | zero => exact .par_empty
    | drop name =>
      exact applyCongruence_of_forall₂ "PDrop" (.cons (name.erase_structural encoding) .nil)
    | signed _ _ process => exact process.erase_structural encoding
    | collection codes => exact codes.erase_structural encoding

  theorem ProcImage.erase_structural {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage depth source process)
      (encoding : SignatureNameEncoding LiteralAuthority) :
      StructuralCongruence (process.erase encoding) (eraseGenerated source) := by
    cases image with
    | zero => exact .par_empty
    | send name code =>
      exact applyCongruence_of_forall₂ "POutput"
        (.cons (name.erase_structural encoding) (.cons (code.erase_structural encoding) .nil))
    | recv name code =>
      exact applyCongruence_of_forall₂ "PInput"
        (.cons (name.erase_structural encoding)
          (.cons (.lambda_cong none _ _ (code.erase_structural encoding)) .nil))
    | pair left right =>
      exact collectionCongruence_of_forall₂ .hashBag none
        (.cons (left.erase_structural encoding) (.cons (right.erase_structural encoding) .nil))

  theorem CodeListImage.erase_structural {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term)
      (encoding : SignatureNameEncoding LiteralAuthority) :
      StructuralCongruence (term.erase encoding)
        (.collection .hashBag (eraseGeneratedList sources) none) := by
    cases image with
    | nil => exact .refl _
    | @cons depth source sources head tail headImage tailImage =>
      exact .trans _ _ _
        (collectionCongruence_of_forall₂ .hashBag none
          (.cons (headImage.erase_structural encoding) (.cons (tailImage.erase_structural encoding) .nil)))
        (.par_flatten [eraseGenerated source] (eraseGeneratedList sources))
end

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
