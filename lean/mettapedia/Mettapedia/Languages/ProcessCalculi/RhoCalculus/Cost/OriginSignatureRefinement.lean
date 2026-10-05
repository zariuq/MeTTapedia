import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ClosedOriginAccountInterpretation

/-!
# Origin-refined signatures in the actual generated grammar

The refinement is indexed by the unchanged literal signature. Each commitment
retains an admitted closed source origin whose computed canonical key supplies
the actual Key tree. Unit and product preserve the authored signature structure.
Ordered origin words give the account observation, independently of the
singleton authority containing the whole literal signature.

This is an admitted origin image, not a choice of source meaning for every
arbitrary Key tree. No monoid equation is added to the generated syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.OriginSignatureRefinement

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.GSLT.LanguageDef.Cost.SignatureSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ActivationGenerated
open AccountedGeneratedReadout
open ClosedOriginAccountInterpretation

/-- Source-origin evidence refines an existing literal, without replacing it. -/
inductive Image : Pattern → Type where
  | unit : Image (.apply costSignatureUnitConstructorName [])
  | product {left right : Pattern} (first : Image left) (second : Image right) :
      Image (.apply costSignatureProductConstructorName [left, right])
  | commit (origin : Origin) :
      Image (AtomicSignatureInterpretation.canonical rhoCIGSLT (admitted origin))

def Image.word {literal : Pattern} : Image literal → OriginWord
  | .unit => 1
  | .product first second => first.word * second.word
  | .commit origin => FreeMonoid.of origin

theorem Image.word_transport {first second : Pattern} (same : first = second)
    (image : Image first) : (same ▸ image).word = image.word := by
  cases same
  rfl

theorem Image.syntax {literal : Pattern} (image : Image literal) :
    LiteralSignatureSyntax literal := by
  induction image with
  | unit => exact .unit
  | product first second firstIH secondIH => exact .product firstIH secondIH
  | commit origin => exact Commitments.canonical_syntax _

theorem Image.typed {literal : Pattern} (image : Image literal) :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] literal
      (.base costSignatureSortName) := by
  induction image with
  | unit =>
      apply HasType.constructor (rule := costSignatureUnitConstructor)
        (List.mem_append_right _ (by simp [costCoreConstructors]))
      · simp [UsesBareCollection, costSignatureUnitConstructor]
      · exact .nil
  | product first second firstIH secondIH =>
      apply HasType.constructor (rule := costSignatureProductConstructor)
        (List.mem_append_right _ (by simp [costCoreConstructors]))
      · simp [UsesBareCollection, costSignatureProductConstructor]
      · exact .cons trivial rfl firstIH (.cons trivial rfl secondIH .nil)
  | commit origin => exact Commitments.canonical_typed _

theorem Image.object {literal : Pattern} (image : Image literal) :
    isObjectPattern literal = true := by
  induction image with
  | unit => rfl
  | product first second firstIH secondIH =>
      simp [isObjectPattern, isObjectPatternList, firstIH, secondIH]
  | commit origin => exact AtomicSignatureInterpretation.canonical_object _ _

def Image.authority {literal : Pattern} (image : Image literal) : TypedSignature literal :=
  ⟨{literal}, rfl, image.typed⟩

theorem Image.accepted {literal : Pattern} (image : Image literal) :
    signature? literal = some image.authority := by
  have checked := checkHasType_complete_of_object image.typed image.object
  simp only [signature?, checked, ↓reduceDIte]
  rfl

theorem Image.authority_positive {literal : Pattern} (image : Image literal) :
    image.authority.val.RuntimeValid := image.authority.positive

theorem Image.annotation {literal : Pattern} (image : Image literal) :
    AtomicSignatureInterpretation.readSignature? literal = some (literalWord image.word) := by
  induction image with
  | unit => simpa only [Image.word, map_one] using AtomicSignatureInterpretation.readSignature_unit
  | product first second firstIH secondIH =>
      simp only [Image.word, map_mul, AtomicSignatureInterpretation.readSignature_product,
        firstIH, secondIH]
  | commit origin => exact authority_annotation origin

theorem Image.normalization_fixed {literal : Pattern} (image : Image literal) :
    normalizeReflective wrappedRhoDeclaration literal = literal := image.syntax.normalize_identity

theorem Image.substitution_fixed {literal : Pattern} (image : Image literal)
    (depth : Nat) (replacement : Pattern) :
    substituteReflective wrappedRhoDeclaration depth replacement literal = literal :=
  image.syntax.substitute_identity depth replacement

noncomputable def Image.sourceAccount {literal : Pattern} (image : Image literal) (Γ : Ctx sig) :
    SourceAccountSubstitution.Account source Srt.pr Γ := sourceWord Γ image.word

theorem Image.sourceAccount_substitute {literal : Pattern} (image : Image literal)
    {Γ Δ : Ctx sig} (env : BindingSubstitutionAlgebra.Environment sig
      source.substitution.Carrier Γ Δ) :
    SourceAccountSubstitution.substitute source Srt.pr env (image.sourceAccount Γ) =
      image.sourceAccount Δ := by
  exact congrArg (fun hom => hom image.word) (sourceWord_substitute env)

theorem Image.sourceAccount_length {literal : Pattern} (image : Image literal) (Γ : Ctx sig) :
    (image.sourceAccount Γ).length = image.word.length := sourceWord_length Γ image.word

/-- An actual product contains two semantic atoms but remains one authority cell. -/
theorem repeated_commitment_control (origin : Origin) :
    let image := Image.product (.commit origin) (.commit origin)
    (literalWord image.word).length = 2 ∧ image.authority.val.card = 1 := by
  dsimp
  constructor
  · rw [literalWord_length]
    rfl
  · rfl

/-- Literal product boundaries are finer than the lawful monoid observation. -/
theorem unit_boundary_control :
    let plain := Image.unit
    let factored := Image.product Image.unit Image.unit
    literalWord plain.word = literalWord factored.word ∧
      plain.authority.val ≠ factored.authority.val := by
  dsimp
  constructor
  · simp [Image.word]
  · intro same
    have literalSame := Multiset.singleton_inj.mp same
    cases literalSame

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.OriginSignatureRefinement
