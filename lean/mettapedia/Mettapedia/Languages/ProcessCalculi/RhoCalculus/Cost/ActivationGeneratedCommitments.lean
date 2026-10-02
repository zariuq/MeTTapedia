import Mettapedia.GSLT.LanguageDef.Cost.AtomicSignatureInterpretation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedSignatureStability

/-!
# Decoder-admitted commitments to authored rho canonical classes

The existing canonical section supplies the committed source representative.
The actual generated signature decoder accepts its exact binary encoding as
one positive authority atom. Reflection normalization and receiver substitution
preserve that literal key. These statements do not assert that every signing
constructor uses the commitment of its own body, or identify the authority atom
with a numerical account valuation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Cost.SignatureSyntax
open Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace Commitments

private theorem source_reflection_safe (source : Pattern)
    (safe : Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt "NQuote" 0 source = true) :
    ReflectiveWellSorted.ReflectiveScopeSafeAt rhoCIGSLT.reflection.val 0 source := by
  intro declaration member
  have presentations : rhoCIGSLT.reflection.val.presentations =
      [rhoReflectivePresentation.toReflectivePresentationDecl] := rfl
  rw [presentations] at member
  obtain rfl := List.mem_singleton.mp member
  exact safe

/-- A concrete inhabitant of the original closed, reflection-admitted
source domain; the authority statements are not over an empty fibre. -/
def zeroOrigin : rhoCIGSLT.CanonicalCarrier :=
  ⟨.apply "PZero" [],
    ⟨⟨checkHasType_sound (by decide +kernel), by decide +kernel,
      by decide +kernel, by rfl⟩,
      source_reflection_safe _ (by decide +kernel)⟩⟩

def parallelZeroOrigin : rhoCIGSLT.CanonicalCarrier :=
  ⟨.collection .hashBag [.apply "PZero" [], .apply "PZero" []] none,
    ⟨⟨checkHasType_sound (by decide +kernel), by decide +kernel,
      by decide +kernel, by rfl⟩,
      source_reflection_safe _ (by decide +kernel)⟩⟩

def sendOrigin : rhoCIGSLT.CanonicalCarrier :=
  ⟨.apply "POutput" [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []],
    ⟨⟨checkHasType_sound (by decide +kernel), by decide +kernel,
      by decide +kernel, by rfl⟩,
      source_reflection_safe _ (by decide +kernel)⟩⟩

private theorem leaf_declared : costKeyLeafConstructor ∈ rhoCIGSLT.costWholeLanguage.terms :=
  List.mem_append_right _ (by simp [costCoreConstructors])

private theorem branch_declared : costKeyBranchConstructor ∈ rhoCIGSLT.costWholeLanguage.terms :=
  List.mem_append_right _ (by simp [costCoreConstructors])

private theorem commit_declared : costSignatureCommitConstructor ∈ rhoCIGSLT.costWholeLanguage.terms :=
  List.mem_append_right _ (by simp [costCoreConstructors])

theorem positive_syntax (number : PosNum) : LiteralSignatureSyntax (LiteralSignatureCommitment.encodePositive number) := by
  induction number with
  | one => exact .product .unit .unit
  | bit0 number ih => exact .product .unit ih
  | bit1 number ih => exact .product (.product .unit .unit) ih

theorem number_syntax (number : Nat) : LiteralSignatureSyntax (LiteralSignatureCommitment.encodeNat number) := by
  unfold LiteralSignatureCommitment.encodeNat
  cases (number : Num) with
  | zero => exact .unit
  | pos value => exact positive_syntax value

theorem canonical_syntax (source : rhoCIGSLT.CanonicalCarrier) :
    LiteralSignatureSyntax (AtomicSignatureInterpretation.canonical rhoCIGSLT source) :=
  AtomicSignatureInterpretation.canonical_syntax _ _

theorem canonical_typed (source : rhoCIGSLT.CanonicalCarrier) :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (AtomicSignatureInterpretation.canonical rhoCIGSLT source) (.base costSignatureSortName) :=
  AtomicSignatureInterpretation.canonical_typed _ _ leaf_declared branch_declared commit_declared

/-- This authority value is independently constructed from the canonical
representative and its generated grammar derivation. -/
def authority (source : rhoCIGSLT.CanonicalCarrier) :
    TypedSignature (AtomicSignatureInterpretation.canonical rhoCIGSLT source) :=
  ⟨{AtomicSignatureInterpretation.canonical rhoCIGSLT source}, rfl, canonical_typed source⟩

theorem canonical_decoded (source : rhoCIGSLT.CanonicalCarrier) :
    signature? (AtomicSignatureInterpretation.canonical rhoCIGSLT source) = some (authority source) := by
  have checked := checkHasType_complete_of_object (canonical_typed source)
    (AtomicSignatureInterpretation.canonical_object _ _)
  simp only [signature?, checked, ↓reduceDIte]
  rfl

/-- Authority equality classifies the actual admitted source equation
classes; syntactically different products cannot collide in the decoder. -/
theorem authority_eq_iff (left right : rhoCIGSLT.CanonicalCarrier) :
    (authority left).val = (authority right).val ↔ rhoCIGSLT.canonicalEquationSetoid.r left right := by
  change ({AtomicSignatureInterpretation.canonical rhoCIGSLT left} : CostSig Pattern) =
    {AtomicSignatureInterpretation.canonical rhoCIGSLT right} ↔ _
  rw [Multiset.singleton_inj, AtomicSignatureInterpretation.canonical_eq_iff]

theorem positive_authority (source : rhoCIGSLT.CanonicalCarrier) :
    (authority source).val.RuntimeValid := (authority source).positive

/-- Canonical commitments identify the source parallel unit law even
though the two authored spellings are different. -/
theorem congruent_origins_same_authority :
    zeroOrigin.val ≠ parallelZeroOrigin.val ∧
    (authority zeroOrigin).val = (authority parallelZeroOrigin).val := by
  constructor
  · decide +kernel
  · apply (authority_eq_iff _ _).mpr
    apply (rhoCIGSLT.canonicalKey_eq_iff _ _).mp
    apply Subtype.ext
    apply Subtype.ext
    change Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize
      zeroOrigin.val =
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize parallelZeroOrigin.val
    decide +kernel

/-- A real output process and zero remain distinct canonical authorities;
both authorities are positive in the actual funding domain. -/
theorem distinct_origins_distinct_authority :
    (authority zeroOrigin).val ≠ (authority sendOrigin).val ∧
    (authority zeroOrigin).val.RuntimeValid ∧ (authority sendOrigin).val.RuntimeValid := by
  refine ⟨?_, positive_authority _, positive_authority _⟩
  intro same
  have equivalent := (authority_eq_iff _ _).mp same
  have sameKey := (rhoCIGSLT.canonicalKey_eq_iff _ _).mpr equivalent
  have samePattern := congrArg (fun key : rhoCIGSLT.CanonicalKey => key.val.val) sameKey
  have separate :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize zeroOrigin.val ≠
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize sendOrigin.val := by
    decide +kernel
  exact separate samePattern

/-- Literal source keys survive both operations actually used by the
generated reflective receiver, without an assumed opacity axiom. -/
theorem canonical_key_stable (source : rhoCIGSLT.CanonicalCarrier)
    (depth : Nat) (replacement : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.normalizeReflective wrappedRhoDeclaration
      (AtomicSignatureInterpretation.canonical rhoCIGSLT source) = AtomicSignatureInterpretation.canonical rhoCIGSLT source ∧
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.substituteReflective wrappedRhoDeclaration
      depth replacement (AtomicSignatureInterpretation.canonical rhoCIGSLT source) =
      AtomicSignatureInterpretation.canonical rhoCIGSLT source :=
  ⟨(canonical_syntax source).normalize_identity,
    (canonical_syntax source).substitute_identity depth replacement⟩

/-- Substitution changes a literal open receiver body while its retained origin
commitment stays fixed. Recomputing the literal key of the current body is
therefore a different operation from transporting the original commitment. -/
theorem retained_origin_is_not_recomputed :
    let body := Pattern.apply (costWrappedConstructorName "PDrop") [.bvar 0]
    let replacement := Pattern.apply (costWrappedConstructorName "NQuote")
      [.apply (costWrappedConstructorName "PZero") []]
    substituteReflective wrappedRhoDeclaration 0 replacement
      (AtomicSignatureInterpretation.commitLiteral body) = AtomicSignatureInterpretation.commitLiteral body ∧
    AtomicSignatureInterpretation.commitLiteral
      (substituteReflective wrappedRhoDeclaration 0 replacement body) ≠
      AtomicSignatureInterpretation.commitLiteral body := by
  dsimp only
  constructor
  · exact (AtomicSignatureInterpretation.commitLiteral_syntax _).substitute_identity _ _
  · intro same
    have changed := AtomicSignatureInterpretation.commitLiteral_injective same
    have different :
        substituteReflective wrappedRhoDeclaration 0
          (.apply (costWrappedConstructorName "NQuote")
            [.apply (costWrappedConstructorName "PZero") []])
          (.apply (costWrappedConstructorName "PDrop") [.bvar 0]) ≠
        .apply (costWrappedConstructorName "PDrop") [.bvar 0] := by decide +kernel
    exact different changed

end Commitments
end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
