import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeProofConsumption
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerSubstitution

/-!
# Context substitution through actual proof consumption

The provider and consumer use the one generic recursive compiler. The same
native substitution acts on their environment and the returned proof. The
result preserves acceptance and rejection, not merely the type of a separately
constructed proof.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeProofConsumption

open Presentation Mettapedia.Logic FormationSensitiveHOLInterface HOLNativeGenericProofCompiler

universe u v

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

theorem compile_substitute (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (natural : operations.raw.Natural)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {premise conclusion : HOL.Formula Const gamma}
    (provider : HOL.ProofSyntax Const delta premise)
    (consumer : HOL.ProofSyntax Const [premise] conclusion)
    {n m : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) (sigma : Sub Tower.Head n m) :
    compile? signature proofName operations provider consumer
        (fun i => subst sigma (objects i)) (fun i => subst sigma (hypotheses i)) =
      (compile? signature proofName operations provider consumer objects hypotheses).map (subst sigma) := by
  simp only [compile?, HOLNativeGenericProofCompiler.compile_substitute
    signature proofName operations natural provider objects hypotheses sigma]
  cases compile signature proofName operations provider objects hypotheses with
  | none => rfl
  | some provided =>
      simpa using HOLNativeGenericProofCompiler.compile_substitute signature proofName operations
        natural consumer objects (fun _ => provided) sigma

#print axioms compile_substitute

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeProofConsumption
