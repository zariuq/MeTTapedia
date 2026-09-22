import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerUniformListSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerNaturalityControls

/-!
# Retained compiler outputs under state-qualified substitution

Source proof syntax and the original successful compilation identify the
actual retained native term. Primitive target object and hypothesis meanings
then qualify its substitution using the existing compiler naturality and
semantic fusion theorems. No compiler is reimplemented, and no closure law for
arbitrary raw extensional denotations is assumed.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler.UniformListStateSubstitution

open Presentation Mettapedia.Logic HOL.UniformListInduction
open FormationSensitiveHOLInterface
open Mettapedia.Logic.HOL.Embedding
open NativeTraceLambdaSemantics (Context)
open NativeTraceContextMorphisms (Morphism)
open UniformListSemantics

universe u

/-- Reuse the existing state. Each source HOL object variable must have its
actual substituted native meaning; a generic mixed component does not imply
this stronger source-indexed object condition. -/
def reindexState {a : ZFSet.{u}} {gamma : SourceContext} {n m : Nat}
    {objects : Sub Tower.Head gamma.length n} (state : State a objects)
    (target : Context.{u} m) (morphism : Morphism state.context target)
    (sigma : Sub Tower.Head n m)
    (objectComponents : NativeHOLTraceLeibnizCompilerSemantics.ObjectsDenote target
      (fun index => subst sigma (objects index))
      (fun point => state.valuation (morphism.environment point))) :
    State a (fun index => subst sigma (objects index)) where
  context := target
  valuation := fun point => state.valuation (morphism.environment point)
  objectsDenote := objectComponents

/-- Naturality identifies the exact substituted retained output. -/
theorem retained_compile_substitution {gamma : SourceContext}
    {delta : List (Formula gamma)} {conclusion : Formula gamma}
    (source : HOL.ProofSyntax Symbol delta conclusion)
    {n m : Nat} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (success : compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations source objects hypotheses = some native)
    (sigma : Sub Tower.Head n m) :
    compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations source (fun index => subst sigma (objects index))
        (fun index => subst sigma (hypotheses index)) = some (subst sigma native) := by
  rw [compile_substitute _ _ _ UniformList.rawOperations_natural, success]
  rfl

/-- Per-input meanings suffice for the actual substituted compiler output;
the conclusion is not supplied as a preservation field. -/
theorem retained_substitution {a : ZFSet.{u}} {gamma : SourceContext}
    {delta : List (Formula gamma)} {conclusion : Formula gamma}
    (source : HOL.ProofSyntax Symbol delta conclusion)
    {n m : Nat} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (success : compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations source objects hypotheses = some native)
    (sigma : Sub Tower.Head n m)
    (targetState : State a (fun index => subst sigma (objects index)))
    (hypothesisComponents : ∀ index,
      Denotes a targetState (subst sigma (hypotheses index)) (delta.get index)) :
    Denotes a targetState (subst sigma native) conclusion :=
  UniformListSemantics.compile_denotes a source
    (retained_compile_substitution source success sigma) targetState hypothesisComponents

theorem retained_reindexed_substitution {a : ZFSet.{u}} {gamma : SourceContext}
    {delta : List (Formula gamma)} {conclusion : Formula gamma}
    (source : HOL.ProofSyntax Symbol delta conclusion)
    {n m : Nat} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (success : compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations source objects hypotheses = some native)
    (state : State a objects) (target : Context.{u} m)
    (morphism : Morphism state.context target) (sigma : Sub Tower.Head n m)
    (objectComponents : NativeHOLTraceLeibnizCompilerSemantics.ObjectsDenote target
      (fun index => subst sigma (objects index))
      (fun point => state.valuation (morphism.environment point)))
    (hypothesisComponents : ∀ index,
      Denotes a (reindexState state target morphism sigma objectComponents)
        (subst sigma (hypotheses index)) (delta.get index)) :
    NativeHOLTraceQualifiedExtensionalSemantics.ProofDenotes a target (subst sigma native)
      (fun point => NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning conclusion
        state.context state.valuation (morphism.environment point)) :=
  retained_substitution source success sigma
    (reindexState state target morphism sigma objectComponents) hypothesisComponents

/-- Instantiating an actual compiled proof binder keeps all older hypothesis
occurrences. The source object telescope is unchanged by a proof binder. -/
theorem proof_binder_instantiation {a : ZFSet.{u}} {gamma : SourceContext}
    {delta : List (Formula gamma)} {premise conclusion : Formula gamma}
    (source : HOL.ProofSyntax Symbol (premise :: delta) conclusion)
    {n : Nat} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm (n + 1)}
    (success : compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations source (fun index => rename wk (objects index))
        (Fin.cases (.var 0) (fun index => rename wk (hypotheses index))) = some native)
    (state : State a objects) {argument : Tower.Tm n}
    (argumentMeaning : Denotes a state argument premise)
    (hypothesesMeaning : ∀ index, Denotes a state (hypotheses index) (delta.get index)) :
    Denotes a state (inst0 argument native) conclusion := by
  have moved := retained_compile_substitution source success (subst0 argument)
  have objectEquality : (fun index => subst (subst0 argument) (rename wk (objects index))) =
      objects := funext (fun index => inst0_rename_wk argument (objects index))
  have hypothesisEquality :
      (fun index => subst (subst0 argument)
        (Fin.cases (.var 0) (fun prior => rename wk (hypotheses prior)) index)) =
      Fin.cases argument hypotheses := by
    funext index
    refine Fin.cases ?_ (fun prior => ?_) index
    · rfl
    · exact inst0_rename_wk argument (hypotheses prior)
  rw [objectEquality] at moved
  have emitted := (congrArg (fun inputs : Fin (premise :: delta).length → Tower.Tm n =>
    compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations source objects inputs) hypothesisEquality).symm.trans moved
  apply UniformListSemantics.compile_denotes a source emitted state
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · exact argumentMeaning
  · exact hypothesesMeaning prior

/-- An object binder changes the source HOL telescope as well as the native
scope. Its instance retains a genuinely object-denoted argument. -/
def instantiateObjectState {a : ZFSet.{u}} {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} (state : State a objects)
    {type : HOL.Ty BaseSort} {argument : Tower.Tm n}
    {value : state.context.Environment → ZFSetUniformListTraceTypeInterpretation.Value a type}
    (argumentMeaning : NativeHOLTraceDisplayedTerms.Denotes a state.context argument value) :
    State a (gamma := type :: gamma) (consSub argument objects) where
  context := state.context
  valuation := fun point => ZFSetUniformListTraceTermInterpretation.extend
    (state.valuation point) (value point)
  objectsDenote := by
    intro objectType index
    cases index with
    | vz => exact argumentMeaning
    | vs prior => exact state.objectsDenote prior

/-- Older proofs keep their meanings when the source telescope is extended
by the instantiated object; this is source weakening, not a family guess. -/
theorem object_instance_old_proof {a : ZFSet.{u}} {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} (state : State a objects)
    {type : HOL.Ty BaseSort} {argument proof : Tower.Tm n}
    {value : state.context.Environment → ZFSetUniformListTraceTypeInterpretation.Value a type}
    (argumentMeaning : NativeHOLTraceDisplayedTerms.Denotes a state.context argument value)
    {formula : Formula gamma} (meaning : Denotes a state proof formula) :
    Denotes a (instantiateObjectState state argumentMeaning) proof (HOL.weaken formula) := by
  apply meaning.cast_proposition
  funext point
  unfold NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning
  exact (congrArg ZFSetHOLTypeInterpretation.holds
    (NativeHOLTraceLeibnizCompilerSemantics.interpret_weaken formula
      (state.valuation point) (value point))).symm

theorem object_binder_instantiation {a : ZFSet.{u}} {gamma : SourceContext}
    {type : HOL.Ty BaseSort} {delta : List (Formula (type :: gamma))}
    {conclusion : Formula (type :: gamma)}
    (source : HOL.ProofSyntax Symbol delta conclusion)
    {n : Nat} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm (n + 1)} {native : Tower.Tm (n + 1)}
    (success : compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations source (liftSub objects) hypotheses = some native)
    (state : State a objects) {argument : Tower.Tm n}
    {value : state.context.Environment → ZFSetUniformListTraceTypeInterpretation.Value a type}
    (argumentMeaning : NativeHOLTraceDisplayedTerms.Denotes a state.context argument value)
    (hypothesisComponents : ∀ index,
      Denotes a (instantiateObjectState state argumentMeaning)
        (inst0 argument (hypotheses index)) (delta.get index)) :
    Denotes a (instantiateObjectState state argumentMeaning)
      (inst0 argument native) conclusion := by
  have moved := retained_compile_substitution source success (subst0 argument)
  have objectEquality : (fun index => subst (subst0 argument) (liftSub objects index)) =
      consSub argument objects := by
    funext index
    refine Fin.cases ?_ (fun prior => ?_) index
    · rfl
    · exact inst0_rename_wk argument (objects prior)
  have emitted := (congrArg (fun inputs : Sub Tower.Head (type :: gamma).length n =>
    compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations source inputs
      (fun index => subst (subst0 argument) (hypotheses index))) objectEquality).symm.trans moved
  exact UniformListSemantics.compile_denotes a source emitted
    (instantiateObjectState state argumentMeaning) hypothesisComponents

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler.UniformListStateSubstitution
