import Mettapedia.Languages.MeTTa.Prime.LanguageOperationSyntax

/-!
# Exact factorization of Prime language-operation syntax

Finite language-operation signatures already provide an independent Prime
grammar, a syntax-directed decoder, dependent typing, and free-path semantics.
This module identifies the strongest true reflection principle for that
grammar.

Raw syntax is not isomorphic to free paths: explicit identities and differently
parenthesized compositions give distinct terms with the same decoded program.
Instead, recognized terms are quotiented by equality of their recovered
endpoint-indexed path.  That quotient is exactly equivalent to decoded free
programs, and every interpretation insensitive to the choice of surface
spelling factors uniquely through it.

This is a selected-fragment initial-factorization theorem.  It does not claim
that every authored GSLT-IL relation is functional or that every future
language operation belongs to a finite signature.
-/

namespace Mettapedia.Languages.MeTTa.Prime.LanguageOperationFactorization

open CategoryTheory
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.Prime.FiniteLanguageOperationSignature

universe u

namespace Signature

variable (signature : Signature)

/-! ## The exact syntax quotient -/

/-- Two recognized Prime terms present the same operation exactly when their
decoder outputs the same endpoint-indexed free path. -/
def SameProgram (first second : signature.RecognizedOperation) : Prop :=
  first.decoded = second.decoded

theorem sameProgram_refl (operation : signature.RecognizedOperation) :
    SameProgram signature operation operation :=
  rfl

theorem sameProgram_symm {first second : signature.RecognizedOperation}
    (same : SameProgram signature first second) :
    SameProgram signature second first :=
  same.symm

theorem sameProgram_trans {first second third : signature.RecognizedOperation}
    (firstSecond : SameProgram signature first second)
    (secondThird : SameProgram signature second third) :
    SameProgram signature first third :=
  firstSecond.trans secondThird

/-- The spelling quotient induced by exact decoded-program equality. -/
def recognizedSetoid : Setoid signature.RecognizedOperation where
  r := SameProgram signature
  iseqv :=
    { refl := sameProgram_refl signature
      symm := sameProgram_symm signature
      trans := sameProgram_trans signature }

abbrev OperationQuotient := Quotient (recognizedSetoid signature)

/-- The canonical spelling of one decoded free program is itself recognized. -/
def canonical (decoded : signature.DecodedProgram) :
    signature.RecognizedOperation := by
  rcases decoded with ⟨source, target, program⟩
  exact
    { term := signature.encodeProgram program
      decoded := ⟨source, target, program⟩
      recognized := signature.decodeProgram_encodeProgram program }

@[simp] theorem canonical_term (decoded : signature.DecodedProgram) :
    (canonical signature decoded).term =
      signature.encodeProgram decoded.program := by
  cases decoded
  rfl

@[simp] theorem canonical_decoded (decoded : signature.DecodedProgram) :
    (canonical signature decoded).decoded = decoded := by
  cases decoded
  rfl

/-- Forget only the surface spelling of a recognized term. -/
def quotientToDecoded :
    OperationQuotient signature → signature.DecodedProgram :=
  Quotient.lift (fun operation => operation.decoded) (by
    intro first second same
    exact same)

/-- Select the canonical surface spelling of a decoded program. -/
def decodedToQuotient (decoded : signature.DecodedProgram) :
    OperationQuotient signature :=
  Quotient.mk (recognizedSetoid signature) (canonical signature decoded)

/-- Recognized Prime operation syntax, modulo exact decoded-program equality,
is precisely the endpoint-indexed free path language. -/
def operationQuotientEquiv :
    OperationQuotient signature ≃ signature.DecodedProgram where
  toFun := quotientToDecoded signature
  invFun := decodedToQuotient signature
  left_inv quotient := by
    refine Quotient.inductionOn quotient ?_
    intro operation
    apply Quotient.sound
    exact canonical_decoded signature operation.decoded
  right_inv decoded := canonical_decoded signature decoded

/-! ## Canonicalization and strongest true reflection -/

/-- Normalize a recognized raw term to the canonical spelling of the exact
free path recovered by the independent decoder. -/
def normalize? (term : PureTm 0) : Option (PureTm 0) :=
  (signature.decodeProgram? term).map fun decoded =>
    signature.encodeProgram decoded.program

@[simp] theorem normalize_encode {source target : signature.Language}
    (program : signature.Program source target) :
    normalize? signature (signature.encodeProgram program) =
      some (signature.encodeProgram program) := by
  simp [normalize?]

theorem normalize_of_decode (term : PureTm 0)
    (decoded : signature.DecodedProgram)
    (accepted : signature.decodeProgram? term = some decoded) :
    normalize? signature term =
      some (signature.encodeProgram decoded.program) := by
  simp [normalize?, accepted]

/-- Normalization preserves the exact endpoint-indexed path recovered by the
independent decoder. -/
theorem normalize_preserves_decode (term : PureTm 0)
    (decoded : signature.DecodedProgram)
    (accepted : signature.decodeProgram? term = some decoded) :
    signature.decodeProgram? (signature.encodeProgram decoded.program) =
      some decoded := by
  rcases decoded with ⟨source, target, program⟩
  exact signature.decodeProgram_encodeProgram program

/-- The canonical result of normalization is independently well typed at the
same recovered endpoints as the authored spelling. -/
theorem normalize_preserves_typing (term : PureTm 0)
    (decoded : signature.DecodedProgram)
    (_accepted : signature.decodeProgram? term = some decoded) :
    Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.HasTypeDecl
      signature.operationDeclEnv .nil
      (signature.encodeProgram decoded.program)
      (signature.routeType
        (signature.languageTerm decoded.source)
        (signature.languageTerm decoded.target)) := by
  rcases decoded with ⟨source, target, program⟩
  exact signature.encodeProgram_typed program

/-- Once a term has been normalized, applying normalization again is inert. -/
theorem normalize_idempotent_of_decode (term : PureTm 0)
    (decoded : signature.DecodedProgram)
    (accepted : signature.decodeProgram? term = some decoded) :
    normalize? signature (signature.encodeProgram decoded.program) =
      normalize? signature term := by
  rw [normalize_of_decode signature term decoded accepted]
  exact normalize_encode signature decoded.program

/-- Canonical encoding is injective at fixed intrinsic endpoints. -/
theorem encodeProgram_injective {source target : signature.Language} :
    Function.Injective
      (@Signature.encodeProgram signature source target) := by
  intro first second equal
  have decodedEqual := congrArg signature.decodeProgram? equal
  simp only [signature.decodeProgram_encodeProgram] at decodedEqual
  have structuresEqual := Option.some.inj decodedEqual
  cases structuresEqual
  rfl

/-- The independent decoder recognizes an explicitly written composition of
two canonical route programs.  Unlike `decodeProgram_encodeProgram`, this
lemma deliberately retains the authored composition node. -/
theorem decodeProgram_compose_encode
    {first middle last : signature.Language}
    (earlier : signature.Program first middle)
    (later : signature.Program middle last) :
    signature.decodeProgram?
        (signature.composeTerm first middle last
          (signature.encodeProgram earlier)
          (signature.encodeProgram later)) =
      some
        { source := first
          target := last
          program := Quiver.Path.comp earlier later } := by
  simp only [
    Mettapedia.Languages.MeTTa.Prime.FiniteLanguageOperationSignature.Signature.composeTerm,
    Mettapedia.Languages.MeTTa.Prime.FiniteLanguageOperationSignature.Signature.decodeProgram?]
  simp [signature.decodeProgram_encodeProgram,
    signature.composeDecoded_programs]

/-! ## Universal factorization -/

/-- An interpretation of surface operations is admissible at the categorical
waist exactly when it is insensitive to surface spellings with the same
decoded endpoint-indexed path. -/
structure InvariantInterpretation (Target : Type u) where
  apply : signature.RecognizedOperation → Target
  respects : ∀ first second,
    SameProgram signature first second → apply first = apply second

namespace InvariantInterpretation

variable {signature : Signature} {Target : Type u}

/-- The induced interpretation of decoded free programs. -/
def factor (interpretation : InvariantInterpretation signature Target) :
    signature.DecodedProgram → Target :=
  fun decoded => interpretation.apply (canonical signature decoded)

/-- The factor agrees with the original interpretation on every recognized
surface spelling. -/
theorem factor_agrees
    (interpretation : InvariantInterpretation signature Target)
    (operation : signature.RecognizedOperation) :
    interpretation.factor operation.decoded = interpretation.apply operation :=
  interpretation.respects _ _
    (canonical_decoded signature operation.decoded)

/-- No other map from decoded free programs can have the same action on all
recognized spellings. -/
theorem factor_unique
    (interpretation : InvariantInterpretation signature Target)
    (candidate : signature.DecodedProgram → Target)
    (agrees : ∀ operation : signature.RecognizedOperation,
      candidate operation.decoded = interpretation.apply operation) :
    candidate = interpretation.factor := by
  funext decoded
  have canonicalAgreement := agrees (canonical signature decoded)
  simpa [factor] using canonicalAgreement

/-- Every spelling-invariant interpretation factors uniquely through the
endpoint-indexed free program language. -/
theorem existsUnique_factor
    (interpretation : InvariantInterpretation signature Target) :
    ∃! factor : signature.DecodedProgram → Target,
      ∀ operation : signature.RecognizedOperation,
        factor operation.decoded = interpretation.apply operation := by
  exact ⟨interpretation.factor, interpretation.factor_agrees,
    fun candidate agrees => interpretation.factor_unique candidate agrees⟩

end InvariantInterpretation

end Signature

/-! ## The represented operational and structural action -/

namespace CurrentExecution

open Mettapedia.Languages.MeTTa.Prime.DataFibration
open Mettapedia.Languages.MeTTa.Prime.DataFibration.FibreTranslation
open Mettapedia.Languages.MeTTa.Prime.DataFibration.ValidatedLanguageData
open Mettapedia.Languages.MeTTa.Prime.InternalDataTransport
open Mettapedia.Languages.MeTTa.NativeTypeTheory
open Mettapedia.Languages.MeTTa.Prime.LanguageOperationSyntax

/-- The two semantic readings and executable Data action determined by one
represented Prime route.  The source and target remain intrinsic indices. -/
structure CompiledAction where
  source : Language
  target : Language
  program : Program source target
  operationalRoute : operationStage source ⟶ operationStage target
  structuralRoute :
    currentLanguagePresentation source ⟶ currentLanguagePresentation target
  run : AllData (fibre (currentLanguagePresentation source)) →
    AllData (fibre (currentLanguagePresentation target))
  operational_eq : operationalRoute = gsltInterpretation.map program
  structural_eq : structuralRoute = structuralInterpretation.map program
  run_eq : run = runProgram program

/-- Interpret one decoded free program simultaneously in the operational
diagram, the structural language category, and the internal Data action. -/
def actionOfDecoded (decoded : currentOperationSignature.DecodedProgram) :
    CompiledAction :=
  { source := decoded.source
    target := decoded.target
    program := decoded.program
    operationalRoute := gsltInterpretation.map decoded.program
    structuralRoute := structuralInterpretation.map decoded.program
    run := runProgram decoded.program
    operational_eq := rfl
    structural_eq := rfl
    run_eq := rfl }

/-- A recognized authored spelling acts only through its independently
decoded endpoint-indexed program. -/
def actionOfRecognized (operation : RecognizedOperation) : CompiledAction :=
  actionOfDecoded operation.decoded

/-- Exact program equality implies equality of operational transport,
structural transport, and executable Data action together. -/
theorem action_respects (first second : RecognizedOperation)
    (same : LanguageOperationFactorization.Signature.SameProgram
      currentOperationSignature first second) :
    actionOfRecognized first = actionOfRecognized second := by
  exact congrArg actionOfDecoded same

/-- Compiled execution descends to the exact spelling quotient. -/
def quotientAction :
    LanguageOperationFactorization.Signature.OperationQuotient
        currentOperationSignature →
      CompiledAction :=
  Quotient.lift actionOfRecognized action_respects

@[simp] theorem quotientAction_mk (operation : RecognizedOperation) :
    quotientAction
        (Quotient.mk
          (LanguageOperationFactorization.Signature.recognizedSetoid
            currentOperationSignature)
          operation) =
      actionOfRecognized operation :=
  rfl

/-- Canonicalization does not change either interpretation or execution. -/
theorem canonical_action_agrees (operation : RecognizedOperation) :
    actionOfRecognized
        (LanguageOperationFactorization.Signature.canonical
          currentOperationSignature operation.decoded) =
      actionOfRecognized operation := by
  unfold actionOfRecognized
  rw [LanguageOperationFactorization.Signature.canonical_decoded]

end CurrentExecution

/-! ## A concrete many-spellings/one-program control -/

namespace CurrentCanary

open Mettapedia.Languages.MeTTa.Prime.LanguageOperationSyntax

/-- The canonical spelling of the Zero identity. -/
def canonicalIdentityTerm : PureTm 0 :=
  identityTerm .zero

/-- A distinct spelling which explicitly composes the Zero identity with
itself. -/
def expandedIdentityTerm : PureTm 0 :=
  composeTerm .zero .zero .zero canonicalIdentityTerm canonicalIdentityTerm

def identityDecoded : currentOperationSignature.DecodedProgram :=
  { source := .zero
    target := .zero
    program := identityProgram .zero }

theorem canonicalIdentity_decodes :
    decodeProgram? canonicalIdentityTerm = some identityDecoded := by
  exact decodeProgram_encodeProgram (identityProgram .zero)

theorem expandedIdentity_decodes :
    decodeProgram? expandedIdentityTerm = some identityDecoded := by
  change currentOperationSignature.decodeProgram?
      (currentOperationSignature.composeTerm .zero .zero .zero
        (currentOperationSignature.encodeProgram
          (currentOperationSignature.identityProgram .zero))
        (currentOperationSignature.encodeProgram
          (currentOperationSignature.identityProgram .zero))) =
    some
      { source := .zero
        target := .zero
        program := Quiver.Path.comp
          (currentOperationSignature.identityProgram .zero)
          (currentOperationSignature.identityProgram .zero) }
  exact LanguageOperationFactorization.Signature.decodeProgram_compose_encode
    currentOperationSignature
    (currentOperationSignature.identityProgram .zero)
    (currentOperationSignature.identityProgram .zero)

/-- The two accepted terms are syntactically distinct. -/
theorem identity_spellings_distinct :
    canonicalIdentityTerm ≠ expandedIdentityTerm := by
  decide

/-- A non-operation is rejected by normalization rather than assigned a
synthetic route. -/
theorem routeType_is_not_normalized :
    LanguageOperationFactorization.Signature.normalize?
      currentOperationSignature (.const routeTypeName) = none := by
  simp [LanguageOperationFactorization.Signature.normalize?,
    Mettapedia.Languages.MeTTa.Prime.FiniteLanguageOperationSignature.Signature.decodeProgram?,
    Mettapedia.Languages.MeTTa.Prime.FiniteLanguageOperationSignature.Signature.decodeRouteName?,
    Mettapedia.Languages.MeTTa.Prime.FiniteLanguageOperationSignature.Signature.decodeIndex?,
    routeNameEmbedding, routeTypeName, promoteName]

def canonicalIdentityOperation : RecognizedOperation where
  term := canonicalIdentityTerm
  decoded := identityDecoded
  recognized := canonicalIdentity_decodes

def expandedIdentityOperation : RecognizedOperation where
  term := expandedIdentityTerm
  decoded := identityDecoded
  recognized := expandedIdentity_decodes

/-- Distinct surface terms become equal exactly at the categorical quotient,
not by pretending their raw syntax was identical. -/
theorem distinct_spellings_same_quotient :
    canonicalIdentityOperation.term ≠ expandedIdentityOperation.term ∧
      Quotient.mk
          (LanguageOperationFactorization.Signature.recognizedSetoid
            currentOperationSignature)
          canonicalIdentityOperation =
        Quotient.mk
          (LanguageOperationFactorization.Signature.recognizedSetoid
            currentOperationSignature)
          expandedIdentityOperation := by
  exact ⟨identity_spellings_distinct, Quotient.sound rfl⟩

end CurrentCanary

#print axioms Signature.operationQuotientEquiv
#print axioms Signature.encodeProgram_injective
#print axioms Signature.InvariantInterpretation.existsUnique_factor
#print axioms CurrentExecution.action_respects
#print axioms CurrentExecution.canonical_action_agrees
#print axioms CurrentCanary.distinct_spellings_same_quotient
#print axioms CurrentCanary.routeType_is_not_normalized

end Mettapedia.Languages.MeTTa.Prime.LanguageOperationFactorization
