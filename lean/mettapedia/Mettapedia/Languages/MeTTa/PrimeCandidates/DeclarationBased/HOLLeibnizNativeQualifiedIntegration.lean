import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceRecursiveExtensionalCompilerSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLExtensionalConservativity
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveSimpleFragment
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TwoSortConservativity

/-!
# Qualified HOL inside the native dependent tower

This module assembles the exact positive and negative boundaries of the
current HOL-to-native bridge.

For the recursively supported source fragment, one and the same emitted term
is both a formation-sensitive native proof and a section of the canonical
Aczel-trace truth family of its source conclusion.  The compiler output is
retained in the statement; no replacement proof is constructed.

The reflection results are deliberately narrower.  Conversion is conservative
when the two endpoints lie in the intrinsic simple fragment, and adding the
two opaque extensional proof constants changes no conversion.  Neither fact
implies that every inhabitant of a represented proposition came from a source
proof.  The new constants refute typing reflection to the constructive base,
the unrestricted tower refutes raw legacy-typing reflection, and erasure of
intrinsic annotations is not injective.

The source fragment here has simply typed object terms, implication,
universal quantification, Leibniz equality, beta and eta, and proposition and
function extensionality.  It does not include the remaining `ProofSyntax`
constructors, a choice principle, source-level type polymorphism, or the HOTG
universe tower.  The trace result is parameterized by one set carrier and does
not require inaccessible-cardinal closure; the latter enters only when this
package is composed with the actual HOTG universe interpretation.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLLeibnizNativeQualifiedIntegration

open Presentation Presentation.FormationSensitive Mettapedia.Logic
open HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open NativeTraceLambdaSemantics (Context)

universe u

namespace Compiler

abbrev SourceContext := HOLLeibnizNativeProofTranslation.SourceContext
abbrev Formula := HOLLeibnizNativeProofTranslation.Formula
abbrev represent {gamma : SourceContext} {type : HOL.Ty BaseSort}
    (term : HOL.Term Symbol gamma type) : Option (Tower.Tm gamma.length) :=
  HOLLeibnizNativeProofTranslation.represent term

/-- A structural and environment-independent description of exactly the
source proof trees accepted by the recursive extensional compiler. -/
def supported {gamma : SourceContext} {delta : List (Formula gamma)}
    {phi : Formula gamma} : HOL.ProofSyntax Symbol delta phi → Bool
  | .hyp _ => true
  | @HOL.ProofSyntax.impI _ _ _ _ premise _ body =>
      (represent premise).isSome && supported body
  | .impE function argument => supported function && supported argument
  | .allI body => supported body
  | .allE term function => (represent term).isSome && supported function
  | .eqRefl term => (represent term).isSome
  | @HOL.ProofSyntax.eqSymm _ _ _ _ _ left right comparison =>
      (represent left).isSome && (represent right).isSome && supported comparison
  | @HOL.ProofSyntax.eqTrans _ _ _ _ _ left middle right first second =>
      (represent left).isSome && (represent middle).isSome &&
        (represent right).isSome && supported first && supported second
  | @HOL.ProofSyntax.eqPropI _ _ _ _ left right forward backward =>
      (represent left).isSome && (represent right).isSome &&
        supported forward && supported backward
  | @HOL.ProofSyntax.eqPropEL _ _ _ _ left right comparison =>
      (represent left).isSome && (represent right).isSome && supported comparison
  | @HOL.ProofSyntax.eqPropER _ _ _ _ left right comparison =>
      (represent left).isSome && (represent right).isSome && supported comparison
  | @HOL.ProofSyntax.eqApp _ _ _ _ _ _ left right argument comparison =>
      (represent left).isSome && (represent right).isSome &&
        (represent argument).isSome && supported comparison
  | @HOL.ProofSyntax.eqAppArg _ _ _ _ _ _ function left right comparison =>
      (represent function).isSome && (represent left).isSome &&
        (represent right).isSome && supported comparison
  | @HOL.ProofSyntax.eqLam _ _ _ _ _ _ left right comparison =>
      (represent left).isSome && (represent right).isSome && supported comparison
  | @HOL.ProofSyntax.funExt _ _ _ _ _ _ function other pointwise =>
      (represent function).isSome && (represent other).isSome && supported pointwise
  | .beta argument body => (represent argument).isSome && (represent body).isSome
  | .eta function => (represent function).isSome
  | _ => false

/-- The structural classifier is exact for every native object and proof
environment. -/
theorem compile_some_iff_supported {gamma : SourceContext}
    {delta : List (Formula gamma)} {phi : Formula gamma}
    (source : HOL.ProofSyntax Symbol delta phi) {n : Nat}
    (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) :
    (∃ native, HOLLeibnizNativeRecursiveExtensionalCompiler.compile
      source objects hypotheses = some native) ↔
      supported source = true := by
  induction source generalizing n <;>
    simp [HOLLeibnizNativeRecursiveExtensionalCompiler.compile, supported,
      represent, Option.bind_eq_some_iff, Option.isSome_iff_exists,
      and_assoc, *]

/-- Successful compilation is independent of the chosen target environment;
only the emitted syntax changes with that environment. -/
theorem support_environment_invariant {gamma : SourceContext}
    {delta : List (Formula gamma)} {phi : Formula gamma}
    (source : HOL.ProofSyntax Symbol delta phi)
    {n m : Nat} (objects₁ : Sub Tower.Head gamma.length n)
    (hypotheses₁ : Fin delta.length → Tower.Tm n)
    (objects₂ : Sub Tower.Head gamma.length m)
    (hypotheses₂ : Fin delta.length → Tower.Tm m) :
    (∃ native, HOLLeibnizNativeRecursiveExtensionalCompiler.compile
      source objects₁ hypotheses₁ = some native) ↔
      ∃ native, HOLLeibnizNativeRecursiveExtensionalCompiler.compile
        source objects₂ hypotheses₂ = some native := by
  rw [compile_some_iff_supported, compile_some_iff_supported]

end Compiler

namespace Connected

open NativeHOLTraceRecursiveExtensionalCompilerSemantics

/-- The connected theorem: the actual compiler result simultaneously carries
its native dependent typing judgment and the canonical trace denotation of
the exact source conclusion.  The shared `native` witness is the point of the
statement. -/
theorem compile_preserves_typing_and_trace
    {a : ZFSet.{u}} {gamma : Compiler.SourceContext}
    {delta : List (Compiler.Formula gamma)} {phi : Compiler.Formula gamma}
    (source : HOL.ProofSyntax Symbol delta phi)
    {n : Nat} {target : Tower.Ctx n} {context : Context.{u} n}
    {objects : Sub Tower.Head gamma.length n}
    {valuation : context.Environment → Valuation a gamma}
    {hypotheses : Fin delta.length → Tower.Tm n}
    (sourceSupported : Compiler.supported source = true)
    (targetFormed : ContextFormation
      FormationSensitiveHOLExtensionalProfile.rules target)
    (objectsTyped : HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.Objects
      target objects)
    (hypothesesTyped :
      HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.Hypotheses
        target objects hypotheses)
    (objectsDenote : ObjectsDenote context objects valuation)
    (hypothesesDenote : HypothesesDenote context valuation hypotheses) :
    ∃ native code,
      HOLLeibnizNativeRecursiveExtensionalCompiler.compile
        source objects hypotheses = some native ∧
      Compiler.represent phi = some code ∧
      Judgment FormationSensitiveHOLExtensionalProfile.rules target native
        (FormationSensitiveHOLProofFamily.proof (subst objects code)) ∧
      ProofDenotes a context native (formulaMeaning phi context valuation) := by
  obtain ⟨native, compiled⟩ :=
    (Compiler.compile_some_iff_supported source objects hypotheses).mpr sourceSupported
  obtain ⟨code, represented, typed⟩ :=
    HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.compile_judgment
      source targetFormed objectsTyped hypothesesTyped compiled
  exact ⟨native, code, compiled, represented, typed,
    compile_denotes source objectsDenote hypothesesDenote compiled⟩

/-- Closed source proofs need no supplied object, proof, or semantic
environment. -/
theorem compile_closed_preserves_typing_and_trace
    {a : ZFSet.{u}} {phi : Compiler.Formula []}
    (source : HOL.ProofSyntax Symbol [] phi)
    (sourceSupported : Compiler.supported source = true) :
    ∃ native code,
      HOLLeibnizNativeRecursiveExtensionalCompiler.compile
        source Fin.elim0 Fin.elim0 = some native ∧
      Compiler.represent phi = some code ∧
      Judgment FormationSensitiveHOLExtensionalProfile.rules .nil native
        (FormationSensitiveHOLProofFamily.proof code) ∧
      ProofDenotes a NativeHOLTraceDisplayedTerms.Controls.emptyContext native
        (formulaMeaning (a := a) phi
          NativeHOLTraceDisplayedTerms.Controls.emptyContext
          (fun _ => ZFSetUniformListTraceTermInterpretation.emptyValuation
            (a := a))) := by
  obtain ⟨native, compiled⟩ :=
    (Compiler.compile_some_iff_supported source Fin.elim0 Fin.elim0).mpr
      sourceSupported
  obtain ⟨code, represented, typed⟩ :=
    HOLLeibnizNativeRecursiveExtensionalCompiler.NativeTyping.compile_closed
      source compiled
  exact ⟨native, code, compiled, represented, typed,
    compile_closed_denotes source compiled⟩

end Connected

namespace Boundary

/-- Adding the opaque extensional proof constants preserves exactly the
constructive profile's conversion relation. -/
theorem extensional_conversion_iff {n : Nat} (left right : Tower.Tm n) :
    Conv FormationSensitiveHOLProofFamily.rules.headEq left right
        FormationSensitiveHOLProofFamily.rules.computation ↔
      Conv FormationSensitiveHOLExtensionalProfile.rules.headEq left right
        FormationSensitiveHOLExtensionalProfile.rules.computation :=
  FormationSensitiveHOLExtensionalConservativity.conversion_iff left right

/-- Conversion both preserves and reflects beta conversion for endpoints in
the intrinsic simple fragment. -/
theorem simple_conversion_on_image
    {gamma : List Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT.Ty}
    {type : Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT.Ty}
    (left right : Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT.Term gamma type) :
    Conv Tower.HeadEq
        (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT.eraseTerm left)
        (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT.eraseTerm right) ↔
      Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT.BetaConv left right :=
  (FormationSensitiveSimpleFragment.conversion_on_image left right).2.2

/-- Typing reflection from the extensional profile to the constructive base
is false: proposition extensionality is an intentional new inhabitant. -/
theorem extensional_typing_reflection_is_false :
    ¬ (∀ (term type : Tower.Tm 0),
      Typing FormationSensitiveHOLExtensionalProfile.rules .nil term type →
        Typing FormationSensitiveHOLProofFamily.rules .nil term type) := by
  intro reflects
  obtain ⟨typed, absent⟩ :=
    FormationSensitiveHOLExtensionalConservativity.proposition_extensionality_is_new
      (.nil : Tower.Ctx 0)
  exact absent ⟨_, reflects _ _ typed⟩

/-- Even before extensionality, unrestricted raw Tower typing does not reflect
to the legacy calculus because native universe formation leaks through the
shared raw syntax. -/
theorem unrestricted_raw_typing_reflection_is_false :
    ¬ (∀ (Γ : Presentation.Legacy.Ctx 0)
      (term type : Presentation.Legacy.Tm 0),
      Presentation.Tower.HasType (Presentation.Legacy.embedCtx Γ)
          (Presentation.Legacy.embed term) (Presentation.Legacy.embed type) →
        Presentation.Legacy.HasType Γ term type) :=
  Presentation.Legacy.unrestricted_raw_reflection_is_false

/-- The simple embedding preserves typing and conversion, but it cannot
recover a unique intrinsically typed source term after domain annotations
have been erased. -/
theorem source_syntax_reflection_is_false :
    Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ErasureBoundary.discardAtomicIdentity ≠
      Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ErasureBoundary.discardFunctionIdentity ∧
    Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT.eraseTerm
        Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ErasureBoundary.discardAtomicIdentity =
      Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT.eraseTerm
        Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ErasureBoundary.discardFunctionIdentity ∧
    Judgment Tower.rules .nil
        (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT.eraseTerm
          Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ErasureBoundary.discardAtomicIdentity)
        (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT.eraseTypeAt 0
          FormationSensitiveSimpleFragment.Examples.endomorphism) ∧
    Judgment Tower.rules .nil
        (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT.eraseTerm
          Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ErasureBoundary.discardFunctionIdentity)
        (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT.eraseTypeAt 0
          FormationSensitiveSimpleFragment.Examples.endomorphism) :=
  FormationSensitiveSimpleFragment.Examples.refinement_does_not_restore_intrinsic_syntax

end Boundary

namespace Controls

open HOLLeibnizNativeRecursiveExtensionalCompiler.Controls
open HOLLeibnizNativeExtensionalProofTranslation.Controls

theorem nested_extensional_source_supported :
    Compiler.supported symmetricFunctionExtensionality = true := by
  exact (Compiler.compile_some_iff_supported symmetricFunctionExtensionality
    Fin.elim0 Fin.elim0).mp nested_function_extensionality_succeeds

theorem nested_extensional_connected (a : ZFSet.{u}) :
    ∃ native code,
      HOLLeibnizNativeRecursiveExtensionalCompiler.compile
        symmetricFunctionExtensionality Fin.elim0 Fin.elim0 = some native ∧
      Compiler.represent (.eq propositionIdentityFunction propositionIdentityFunction) =
        some code ∧
      Judgment FormationSensitiveHOLExtensionalProfile.rules .nil native
        (FormationSensitiveHOLProofFamily.proof code) ∧
      NativeHOLTraceRecursiveExtensionalCompilerSemantics.ProofDenotes a
        NativeHOLTraceDisplayedTerms.Controls.emptyContext native
        (NativeHOLTraceRecursiveExtensionalCompilerSemantics.formulaMeaning
          (a := a) (.eq propositionIdentityFunction propositionIdentityFunction)
          NativeHOLTraceDisplayedTerms.Controls.emptyContext
          (fun _ => ZFSetUniformListTraceTermInterpretation.emptyValuation
            (a := a))) :=
  Connected.compile_closed_preserves_typing_and_trace
    symmetricFunctionExtensionality nested_extensional_source_supported

/-- A source proof using conjunction is valid syntax but lies outside the
advertised compiler fragment. -/
def unsupportedConjunction (p : Compiler.Formula []) :
    HOL.ProofSyntax Symbol [p] (.and p p) :=
  .andI (.hyp 0) (.hyp 0)

theorem conjunction_is_not_supported (p : Compiler.Formula []) :
    Compiler.supported (unsupportedConjunction p) = false := by
  rfl

theorem conjunction_is_not_compiled (p : Compiler.Formula []) :
    HOLLeibnizNativeRecursiveExtensionalCompiler.compile
      (unsupportedConjunction p) (n := 0) Fin.elim0
      (fun _ => .const `unsupportedHypothesis) = none := by
  rfl

end Controls

#print axioms Compiler.compile_some_iff_supported
#print axioms Compiler.support_environment_invariant
#print axioms Connected.compile_preserves_typing_and_trace
#print axioms Connected.compile_closed_preserves_typing_and_trace
#print axioms Boundary.extensional_conversion_iff
#print axioms Boundary.simple_conversion_on_image
#print axioms Boundary.extensional_typing_reflection_is_false
#print axioms Boundary.unrestricted_raw_typing_reflection_is_false
#print axioms Boundary.source_syntax_reflection_is_false
#print axioms Controls.nested_extensional_connected
#print axioms Controls.conjunction_is_not_supported
#print axioms Controls.conjunction_is_not_compiled

end HOLLeibnizNativeQualifiedIntegration
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
