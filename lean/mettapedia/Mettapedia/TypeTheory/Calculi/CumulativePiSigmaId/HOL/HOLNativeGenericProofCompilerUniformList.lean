import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerTyping
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizNativeRecursiveExtensionalCompiler

/-!
# Uniform-List instance of the signature-generic HOL proof compiler

The generic compiler and correctness interface are independent of this
specimen.  This module supplies the complete extensional List operation
algebra and retains the old compiler only as an extensional regression
comparison.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler

open Presentation Mettapedia.Logic
open FormationSensitiveHOLInterface

namespace UniformList

open HOL.UniformListInduction

def proofName : DeclName :=
  FormationSensitiveHOLProofFamily.proofName

@[simp] theorem proof_eq_legacy {n : Nat} (proposition : Tower.Tm n) :
    FormationSensitiveHOLGenericProofFamily.proof
        FormationSensitiveHOLProofFamily.proofName proposition =
      FormationSensitiveHOLProofFamily.proof proposition := rfl

@[simp] theorem universalProposition_eq_legacy {n : Nat}
    (type : HOL.Ty BaseSort) (predicate : Tower.Tm n) :
    FormationSensitiveHOLGenericProofFamily.universalProposition
        FormationSensitiveHOLLeibnizInterface.signature type predicate =
      FormationSensitiveHOLProofFamily.universalProposition
        (FormationSensitiveHOLInterface.typeAt
          FormationSensitiveHOLUniformList.types n type) predicate := by
  simp [FormationSensitiveHOLGenericProofFamily.universalProposition,
    FormationSensitiveHOLProofFamily.universalProposition,
    FormationSensitiveHOLLeibnizInterface.signature,
    FormationSensitiveHOLUniformList.signature,
    FormationSensitiveHOLUniformList.universal, liftClosed,
    Presentation.rename, typeAt_rename]

@[simp] theorem universalFamily_eq_legacy {n : Nat}
    (type : HOL.Ty BaseSort) (predicate : Tower.Tm n) :
    FormationSensitiveHOLGenericProofFamily.universalFamily
        FormationSensitiveHOLLeibnizInterface.signature
        FormationSensitiveHOLProofFamily.proofName type predicate =
      FormationSensitiveHOLProofFamily.universalFamily
        (FormationSensitiveHOLInterface.typeAt
          FormationSensitiveHOLUniformList.types n type) predicate := by
  rfl

/-- The List source reaches the extensional host by composing the existing
source-to-proof and proof-to-extensional presentation morphisms. -/
theorem sourceMorphism : FormationSensitiveHOLLeibnizInterface.signature.rules.Morphism
    FormationSensitiveHOLExtensionalProfile.rules (fun head => head) := by
  have composed := FormationSensitiveHOLProofFamily.sourceMorphism.comp
    FormationSensitiveHOLExtensionalProfile.baseMorphism
  exact {
    headTyping := composed.headTyping
    isUniverse := composed.isUniverse
    join := composed.join
    cumulative := composed.cumulative
    headEq := composed.headEq
    constantType := by
      intro name type known
      simpa only [Function.comp_apply, Function.comp_def, Tm.mapHead_id] using
        composed.constantType known
    computation := by
      intro n left right step
      simpa only [Function.comp_apply, Function.comp_def, Tm.mapHead_id] using
        composed.computation step
  }

/-- Both generic decoder equations are the already implemented List decoder
equations, transported once into the richer extensional host. -/
theorem decoder_step {n : Nat} {left right : Tower.Tm n}
    (step : FormationSensitiveHOLGenericProofFamily.DecoderStep
      FormationSensitiveHOLLeibnizInterface.signature proofName left right) :
    FormationSensitiveHOLExtensionalProfile.rules.computation.step left right := by
  cases step with
  | implication p q =>
      have prior : FormationSensitiveHOLProofFamily.rules.computation.step
          (FormationSensitiveHOLGenericProofFamily.proof proofName
            (FormationSensitiveHOLGenericProofFamily.rawImp
              FormationSensitiveHOLLeibnizInterface.signature p q))
          (FormationSensitiveHOLGenericProofFamily.implicationFamily proofName p q) := by
        change Presentation.Declaration.RootStep Tower.rules
          FormationSensitiveHOLProofFamily.declarations n
          (FormationSensitiveHOLProofFamily.proof
            (FormationSensitiveHOLProofFamily.Source.rawImp p q))
          (FormationSensitiveHOLProofFamily.implicationFamily p q)
        exact Presentation.Declaration.RootStep.declared
          (FormationSensitiveHOLProofFamily.DecoderStep.implication p q)
      simpa only [Tm.mapHead_id] using
        FormationSensitiveHOLExtensionalProfile.baseMorphism.computation prior
  | universal type predicate =>
      have prior : FormationSensitiveHOLProofFamily.rules.computation.step
          (FormationSensitiveHOLProofFamily.proof
            (FormationSensitiveHOLProofFamily.universalProposition
              (FormationSensitiveHOLInterface.typeAt
                FormationSensitiveHOLUniformList.types n type) predicate))
          (FormationSensitiveHOLProofFamily.universalFamily
            (FormationSensitiveHOLInterface.typeAt
              FormationSensitiveHOLUniformList.types n type) predicate) := by
        exact Presentation.Declaration.RootStep.declared
          (FormationSensitiveHOLProofFamily.DecoderStep.universal
            (FormationSensitiveHOLInterface.typeAt
              FormationSensitiveHOLUniformList.types n type) predicate)
      simpa only [proofName, proof_eq_legacy,
        universalProposition_eq_legacy, universalFamily_eq_legacy,
        Tm.mapHead_id] using
        FormationSensitiveHOLExtensionalProfile.baseMorphism.computation prior

/-- The complete generic proof-family presentation maps into the existing
extensional List host; no declaration or computation table is recopied. -/
theorem proofMorphism :
    (FormationSensitiveHOLGenericProofFamily.rules
      FormationSensitiveHOLLeibnizInterface.signature proofName).Morphism
      FormationSensitiveHOLExtensionalProfile.rules (fun head => head) :=
  FormationSensitiveHOLGenericProofFamily.morphismTo
    FormationSensitiveHOLLeibnizInterface.signature proofName
    FormationSensitiveHOLExtensionalProfile.rules sourceMorphism (by decide)
    decoder_step

/-- Every operation used by the former List-specific compiler, supplied as
one explicit instance. -/
def rawOperations : RawOperations BaseSort where
  reflexivity := some FormationSensitiveHOLLeibnizDerived.reflTerm
  symmetry := fun type left proof =>
    some (FormationSensitiveHOLLeibnizDerived.symmetry type left proof)
  transitivity := fun type left first second =>
    some (FormationSensitiveHOLLeibnizDerived.transitivity type left first second)
  propositionExtensionality := fun left right forward backward =>
    some (FormationSensitiveHOLExtensionalApplications.propositionExtensionalityApp
      left right forward backward)
  propositionForward := fun proof =>
    some (FormationSensitiveHOLLeibnizDerived.propForward proof)
  functionCongruence := fun result function argument proof =>
    some (FormationSensitiveHOLLeibnizDerived.functionCongruence
      result function argument proof)
  argumentCongruence := fun result function argument proof =>
    some (FormationSensitiveHOLLeibnizDerived.congruence
      result function argument proof)
  functionExtensionality := fun domain codomain function other pointwise =>
    some (FormationSensitiveHOLExtensionalApplications.functionExtensionalityApp
      domain codomain function other pointwise)

@[simp] theorem signature_rules_eq_legacy :
    FormationSensitiveHOLLeibnizInterface.signature.rules =
      FormationSensitiveHOLUniformList.rules := rfl

@[simp] theorem signature_types_eq_legacy :
    FormationSensitiveHOLLeibnizInterface.signature.types =
      FormationSensitiveHOLUniformList.types := rfl

@[simp] theorem rawEquality_eq_legacy {n : Nat} (type : HOL.Ty BaseSort)
    (left right : Tower.Tm n) :
    rawEquality FormationSensitiveHOLLeibnizInterface.signature type left right =
      HOLLeibnizNativeProofTranslation.rawEquality type left right := rfl

@[simp] theorem rawImp_eq_legacy {n : Nat} (left right : Tower.Tm n) :
    FormationSensitiveHOLGenericProofFamily.rawImp
        FormationSensitiveHOLLeibnizInterface.signature left right =
      FormationSensitiveHOLUniformList.rawImp left right := rfl

/-- Source object typing enters the inherited List proof presentation through
its declaration-extension morphism; no target proof principle is used. -/
theorem includeSourceTyping {n : Nat} {context : Tower.Ctx n}
    {term type : Tower.Tm n}
    (typed : Presentation.FormationSensitive.Typing
      FormationSensitiveHOLLeibnizInterface.signature.rules context term type) :
    Presentation.FormationSensitive.Typing FormationSensitiveHOLProofFamily.rules
      context term type := by
  apply FormationSensitiveHOLProofFamily.include_typed
  simpa only [signature_rules_eq_legacy] using typed

/-- The extensional List host supplies every advertised compiler operation,
with the operation terms and their typing laws packaged together. -/
def operations : Operations FormationSensitiveHOLLeibnizInterface.signature proofName where
  fresh := by decide
  target := FormationSensitiveHOLExtensionalProfile.rules
  proofMorphism := proofMorphism
  raw := rawOperations
  reflexivity_typed := by
    intro n context type left right out emitted leftTyped rightTyped conversion
    simp only [rawOperations, Option.some.injEq] at emitted
    subst out
    simpa only [proofName, proof_eq_legacy, rawEquality_eq_legacy] using
      HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.equality_of_conversion
        (includeSourceTyping leftTyped)
        (includeSourceTyping rightTyped)
        conversion
  symmetry_typed := by
    intro n context type left right comparison out emitted leftTyped rightTyped
      comparisonTyped
    simp only [rawOperations, Option.some.injEq] at emitted
    subst out
    simpa only [proofName, proof_eq_legacy, rawEquality_eq_legacy] using
      HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.equality_from_predicate
        (includeSourceTyping rightTyped)
        (includeSourceTyping leftTyped)
        (FormationSensitiveHOLExtensionalDerived.symmetry_typed
          (includeSourceTyping leftTyped)
          (includeSourceTyping rightTyped)
          (HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.equality_to_predicate
            (includeSourceTyping leftTyped)
            (includeSourceTyping rightTyped)
            (by simpa only [proofName, proof_eq_legacy, rawEquality_eq_legacy] using
              comparisonTyped)))
  transitivity_typed := by
    intro n context type left middle right first second out emitted leftTyped
      middleTyped rightTyped firstTyped secondTyped
    simp only [rawOperations, Option.some.injEq] at emitted
    subst out
    simpa only [proofName, proof_eq_legacy, rawEquality_eq_legacy] using
      HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.equality_from_predicate
        (includeSourceTyping leftTyped)
        (includeSourceTyping rightTyped)
        (FormationSensitiveHOLExtensionalDerived.transitivity_typed
          (includeSourceTyping leftTyped)
          (includeSourceTyping middleTyped)
          (includeSourceTyping rightTyped)
          (HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.equality_to_predicate
            (includeSourceTyping leftTyped)
            (includeSourceTyping middleTyped)
            (by simpa only [proofName, proof_eq_legacy, rawEquality_eq_legacy] using firstTyped))
          (HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.equality_to_predicate
            (includeSourceTyping middleTyped)
            (includeSourceTyping rightTyped)
            (by simpa only [proofName, proof_eq_legacy, rawEquality_eq_legacy] using secondTyped)))
  propositionExtensionality_typed := by
    intro n context left right forward backward out emitted leftTyped rightTyped
      forwardTyped backwardTyped
    simp only [rawOperations, Option.some.injEq] at emitted
    subst out
    simpa only [proofName, proof_eq_legacy, rawEquality_eq_legacy] using
      HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.proposition_extensionality_typed
        (includeSourceTyping leftTyped)
        (includeSourceTyping rightTyped)
        (by simpa only [proofName, proof_eq_legacy, rawImp_eq_legacy] using forwardTyped)
        (by simpa only [proofName, proof_eq_legacy, rawImp_eq_legacy] using backwardTyped)
  propositionForward_typed := by
    intro n context left right comparison out emitted leftTyped rightTyped comparisonTyped
    simp only [rawOperations, Option.some.injEq] at emitted
    subst out
    simpa only [proofName, proof_eq_legacy, rawImp_eq_legacy] using
      FormationSensitiveHOLExtensionalDerived.propForward_typed
      (includeSourceTyping leftTyped)
      (includeSourceTyping rightTyped)
      (HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.equality_to_predicate
        (includeSourceTyping leftTyped)
        (includeSourceTyping rightTyped)
        (by simpa only [proofName, proof_eq_legacy, rawEquality_eq_legacy] using
          comparisonTyped))
  functionCongruence_typed := by
    intro n context domain result function other argument comparison out emitted
      functionTyped otherTyped argumentTyped comparisonTyped
    simp only [rawOperations, Option.some.injEq] at emitted
    subst out
    have functionTyped' := includeSourceTyping functionTyped
    have otherTyped' := includeSourceTyping otherTyped
    have argumentTyped' := includeSourceTyping argumentTyped
    have functionApplication := FormationSensitiveHOLLeibnizRules.application_typed
      functionTyped' argumentTyped'
    have otherApplication := FormationSensitiveHOLLeibnizRules.application_typed
      otherTyped' argumentTyped'
    simpa only [proofName, proof_eq_legacy, rawEquality_eq_legacy] using
      HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.equality_from_predicate
        functionApplication otherApplication
        (FormationSensitiveHOLExtensionalDerived.functionCongruence_typed
          functionTyped' otherTyped' argumentTyped'
          (HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.equality_to_predicate
            functionTyped' otherTyped'
            (by simpa only [proofName, proof_eq_legacy, rawEquality_eq_legacy] using
              comparisonTyped)))
  argumentCongruence_typed := by
    intro n context domain result function left right comparison out emitted
      functionTyped leftTyped rightTyped comparisonTyped
    simp only [rawOperations, Option.some.injEq] at emitted
    subst out
    have functionTyped' := includeSourceTyping functionTyped
    have leftTyped' := includeSourceTyping leftTyped
    have rightTyped' := includeSourceTyping rightTyped
    have leftApplication := FormationSensitiveHOLLeibnizRules.application_typed
      functionTyped' leftTyped'
    have rightApplication := FormationSensitiveHOLLeibnizRules.application_typed
      functionTyped' rightTyped'
    simpa only [proofName, proof_eq_legacy, rawEquality_eq_legacy] using
      HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.equality_from_predicate
        leftApplication rightApplication
        (FormationSensitiveHOLExtensionalDerived.congruence_typed
          functionTyped' leftTyped' rightTyped'
          (HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.equality_to_predicate
            leftTyped' rightTyped'
            (by simpa only [proofName, proof_eq_legacy, rawEquality_eq_legacy] using
              comparisonTyped)))
  functionExtensionality_typed := by
    intro n context domain codomain function other pointwise out emitted
      functionTyped otherTyped pointwiseTyped
    simp only [rawOperations, Option.some.injEq] at emitted
    subst out
    simpa only [proofName, proof_eq_legacy, rawEquality_eq_legacy,
      signature_types_eq_legacy,
      HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.rules] using
      HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.function_extensionality_typed
        (includeSourceTyping functionTyped)
        (includeSourceTyping otherTyped)
        (by simpa only [proofName, proof_eq_legacy, rawEquality_eq_legacy,
          universalProposition_eq_legacy,
          FormationSensitiveHOLUniformList.rawAll,
          FormationSensitiveHOLProofFamily.universalProposition,
          FormationSensitiveHOLUniformList.universal, liftClosed,
          Presentation.rename, typeAt_rename] using pointwiseTyped)

@[simp] theorem operations_raw : operations.raw = rawOperations := rfl

@[simp] theorem represent_eq_legacy {gamma : HOL.Ctx BaseSort}
    {type : HOL.Ty BaseSort} (term : HOL.Term Symbol gamma type) :
    represent FormationSensitiveHOLLeibnizInterface.signature term =
      HOLLeibnizNativeProofTranslation.represent term := rfl

/-- The generic fold with the full List algebra is extensionally the former
List-specific recursive compiler on every proof and every environment. -/
theorem compile_eq_legacy
    {gamma : HOL.Ctx BaseSort}
    {delta : List (HOL.Formula Symbol gamma)} {phi : HOL.Formula Symbol gamma}
    (source : HOL.ProofSyntax Symbol delta phi) {n : Nat}
    (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) :
    compile FormationSensitiveHOLLeibnizInterface.signature proofName operations
        source objects hypotheses =
      HOLLeibnizNativeRecursiveExtensionalCompiler.compile
        source objects hypotheses := by
  induction source generalizing n <;>
    simp only [compile, operations_raw,
      HOLLeibnizNativeRecursiveExtensionalCompiler.compile] <;>
    simp_all only [rawOperations, represent_eq_legacy, signature_types_eq_legacy] <;>
    rfl

/-- The former nested extensional canary is now checked by the generic
correctness induction instantiated with the List operation algebra. -/
theorem nested_extensional_compiles_typed :
    ∃ native code,
      compile FormationSensitiveHOLLeibnizInterface.signature proofName operations
          HOLLeibnizNativeRecursiveExtensionalCompiler.Controls.symmetricFunctionExtensionality
          (n := 0) Fin.elim0 Fin.elim0 = some native ∧
      represent FormationSensitiveHOLLeibnizInterface.signature
          (.eq
            HOLLeibnizNativeExtensionalProofTranslation.Controls.propositionIdentityFunction
            HOLLeibnizNativeExtensionalProofTranslation.Controls.propositionIdentityFunction) =
        some code ∧
      Presentation.FormationSensitive.Typing operations.target .nil native
        (FormationSensitiveHOLGenericProofFamily.proof proofName code) := by
  let source :=
    HOLLeibnizNativeRecursiveExtensionalCompiler.Controls.symmetricFunctionExtensionality
  obtain ⟨native, compiled⟩ : ∃ native,
      compile FormationSensitiveHOLLeibnizInterface.signature
        proofName operations source (n := 0) Fin.elim0 Fin.elim0 = some native := by
    refine ⟨_, rfl⟩
  obtain ⟨code, represented, typed⟩ :=
    GenericTyping.compile_closed FormationSensitiveHOLLeibnizInterface.signature
      proofName operations source compiled
  exact ⟨native, code, compiled, represented, typed⟩

end UniformList

#print axioms UniformList.compile_eq_legacy
#print axioms UniformList.nested_extensional_compiles_typed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
