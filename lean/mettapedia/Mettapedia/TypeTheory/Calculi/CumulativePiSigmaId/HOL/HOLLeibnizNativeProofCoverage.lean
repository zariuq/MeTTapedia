import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizNativeProofTranslation

/-!
# Exact coverage of the native HOL proof compiler

The native Leibniz compiler is intentionally partial.  This module gives an
independent, structural Boolean description of its present proof-rule and
term-representation boundary, then proves that the description is exact for
every object and hypothesis environment.

The positive fragment contains hypotheses, implication and universal rules,
constructive Leibniz equality rules, and beta.  The remaining source rules are
reported as unsupported rather than silently assigned a native inhabitant.
This theorem qualifies the compiler; it does not add extensionality principles
or choose encodings for the other logical connectives.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizNativeProofCoverage

open Presentation Mettapedia.Logic
open HOL.UniformListInduction
open HOLLeibnizNativeProofTranslation

/-- A structural account of precisely the proof and object syntax accepted by
the current compiler.  Unlike running `compile`, this does not inspect or
construct a native environment or output term. -/
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
  | @HOL.ProofSyntax.eqApp _ _ _ _ _ _ left right argument comparison =>
      (represent left).isSome && (represent right).isSome &&
        (represent argument).isSome && supported comparison
  | @HOL.ProofSyntax.eqAppArg _ _ _ _ _ _ function left right comparison =>
      (represent function).isSome && (represent left).isSome &&
        (represent right).isSome && supported comparison
  | @HOL.ProofSyntax.eqPropEL _ _ _ _ left right comparison =>
      (represent left).isSome && (represent right).isSome && supported comparison
  | @HOL.ProofSyntax.eqPropER _ _ _ _ left right comparison =>
      (represent left).isSome && (represent right).isSome && supported comparison
  | .beta argument body => (represent argument).isSome && (represent body).isSome
  | _ => false

theorem compile_some_iff_supported {gamma : SourceContext}
    {delta : List (Formula gamma)} {phi : Formula gamma}
    (source : HOL.ProofSyntax Symbol delta phi) {n : Nat}
    (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) :
    (∃ native, compile source objects hypotheses = some native) ↔ supported source = true := by
  induction source generalizing n <;>
    simp [compile, supported, Option.bind_eq_some_iff,
      Option.isSome_iff_exists, and_assoc, *]

/-- The structural classifier is exact and independent of the supplied native
environment: a compiler result exists exactly when `supported` says it does. -/
theorem compile_isSome {gamma : SourceContext} {delta : List (Formula gamma)}
    {phi : Formula gamma} (source : HOL.ProofSyntax Symbol delta phi)
    {n : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) :
    (compile source objects hypotheses).isSome = supported source := by
  rw [Bool.eq_iff_iff, Option.isSome_iff_exists]
  exact compile_some_iff_supported source objects hypotheses

/-- Successful compilation is invariant under changing the native object and
hypothesis environment.  The emitted term may change, but support cannot. -/
theorem support_environment_invariant {gamma : SourceContext}
    {delta : List (Formula gamma)} {phi : Formula gamma}
    (source : HOL.ProofSyntax Symbol delta phi)
    {n m : Nat} (objects₁ : Sub Tower.Head gamma.length n)
    (hypotheses₁ : Fin delta.length → Tower.Tm n)
    (objects₂ : Sub Tower.Head gamma.length m)
    (hypotheses₂ : Fin delta.length → Tower.Tm m) :
    (∃ native, compile source objects₁ hypotheses₁ = some native) ↔
      ∃ native, compile source objects₂ hypotheses₂ = some native := by
  rw [compile_some_iff_supported, compile_some_iff_supported]

namespace Controls

def implicationIdentity (p : Formula []) : HOL.ProofSyntax Symbol [] (.imp p p) :=
  .impI (.hyp 0)

theorem implication_identity_supported (p : Formula [])
    (represented : (represent p).isSome = true) :
    supported (implicationIdentity p) = true := by
  simp [implicationIdentity, supported, represented]

/-- A valid function-extensionality proof remains outside the constructive
Leibniz fragment; support is not confused with source validity. -/
theorem function_extensionality_unsupported :
    supported (HOL.ProofSyntax.funExt (Const := Symbol) (Δ := [])
      (f := HOL.Term.lam (Γ := []) (σ := .prop) (.var .vz))
      (g := HOL.Term.lam (Γ := []) (σ := .prop) (.var .vz))
      (.allI (.eqRefl (.app (HOL.weaken (.lam (.var .vz))) (.var .vz))))) = false := rfl

theorem lambda_equality_unsupported :
    supported (HOL.ProofSyntax.eqLam (Const := Symbol) (Δ := [])
      (.eqRefl (HOL.Term.var (Γ := [.prop]) .vz))) = false := rfl

theorem propositional_extensionality_unsupported :
    supported (HOL.ProofSyntax.eqPropI (Const := Symbol) (Δ := [])
      (p := HOL.Term.var (Γ := [.prop]) .vz) (q := .var .vz)
      (.impI (.hyp 0)) (.impI (.hyp 0))) = false := rfl

end Controls

#print axioms compile_isSome
#print axioms compile_some_iff_supported
#print axioms support_environment_invariant
#print axioms Controls.implication_identity_supported
#print axioms Controls.function_extensionality_unsupported
#print axioms Controls.lambda_equality_unsupported
#print axioms Controls.propositional_extensionality_unsupported

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizNativeProofCoverage
