import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerTyping
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLGenericProofInstances

/-!
# Call-guard instance of the signature-generic HOL proof compiler

The compiler and its typing theorem do not depend on this operational
specimen.  This module supplies the dependency in the other direction: the
actual call-guard proof and signature instantiate the generic construction.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
namespace CallGuard

open Presentation Mettapedia.Logic
open FormationSensitiveHOLInterface
open FormationSensitiveHOLGenericProofInstances.CallGuard
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant

/-- The two source assumptions are represented by the two native variables in
the same order as the source assumption list. -/
def hypotheses (index : Fin assumptions.length) : Tower.Tm 2 :=
  .var (Fin.rev (index.cast (by decide)))

/-- The actual call-guard proof compiles through the signature-generic fold,
using no equality or extensional capabilities. -/
theorem preservation_compiles :
    ∃ native, compile FormationSensitiveHOLInvariant.signature proofName
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName
        proofName_fresh) preservationSyntax
      (n := 2) Fin.elim0 hypotheses = some native := by
  refine ⟨_, rfl⟩

/-- Compilation of the retained proof succeeds for every native realization
of its two hypotheses; the traversal does not depend on the specimen context
chosen above. -/
theorem preservation_compiles_any {n : Nat}
    (nativeHypotheses : Fin assumptions.length → Tower.Tm n) :
    ∃ native, compile FormationSensitiveHOLInvariant.signature proofName
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName
        proofName_fresh) preservationSyntax
      (n := n) Fin.elim0 nativeHypotheses = some native := by
  refine ⟨_, rfl⟩

/-- In every native context containing typed realizations of the two actual
call-guard assumptions, the same retained proof compiles to a term inhabiting
the proof family of its exact represented conclusion. -/
theorem preservation_compiles_typed {n : Nat} {target : Tower.Ctx n}
    {nativeHypotheses : Fin assumptions.length → Tower.Tm n}
    (hypothesisTyped : GenericTyping.Hypotheses
      FormationSensitiveHOLInvariant.signature
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature
        FormationSensitiveHOLGenericProofInstances.CallGuard.proofName
        FormationSensitiveHOLGenericProofInstances.CallGuard.proofName_fresh)
      target Fin.elim0 nativeHypotheses) :
    ∃ native code,
      compile FormationSensitiveHOLInvariant.signature proofName
        (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName
          proofName_fresh) preservationSyntax
        Fin.elim0 nativeHypotheses = some native ∧
      represent FormationSensitiveHOLInvariant.signature conclusion = some code ∧
      Presentation.FormationSensitive.Typing
        FormationSensitiveHOLGenericProofInstances.CallGuard.rules target native
        (FormationSensitiveHOLGenericProofFamily.proof
          FormationSensitiveHOLGenericProofInstances.CallGuard.proofName
          (subst Fin.elim0 code)) := by
  obtain ⟨native, compiled⟩ := preservation_compiles_any nativeHypotheses
  have objectTyped : GenericTyping.Objects
      FormationSensitiveHOLInvariant.signature
      (gamma := []) target Fin.elim0 := by
    intro index
    nomatch index
  obtain ⟨code, represented, typed⟩ :=
    GenericTyping.compile_typed FormationSensitiveHOLInvariant.signature
      FormationSensitiveHOLGenericProofInstances.CallGuard.proofName
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature
        FormationSensitiveHOLGenericProofInstances.CallGuard.proofName
        FormationSensitiveHOLGenericProofInstances.CallGuard.proofName_fresh)
      preservationSyntax objectTyped hypothesisTyped compiled
  exact ⟨native, code, compiled, represented, typed⟩

/-- The sparse call-guard algebra does not silently acquire equality
reflexivity merely because the source equality formula is representable. -/
theorem equality_rejected :
    compile FormationSensitiveHOLInvariant.signature
      proofName
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName
        proofName_fresh)
      (HOL.ProofSyntax.eqRefl (HOL.Term.const Constant.property) :
        HOL.ProofSyntax Constant []
          (((HOL.Term.const Constant.property).eq
            (HOL.Term.const Constant.property)) : HOL.ClosedFormula Constant))
      (n := 0) Fin.elim0 Fin.elim0 = none := rfl

end CallGuard

#print axioms CallGuard.preservation_compiles
#print axioms CallGuard.preservation_compiles_any
#print axioms CallGuard.preservation_compiles_typed
#print axioms CallGuard.equality_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
