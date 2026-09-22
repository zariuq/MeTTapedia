import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLImpredicativeProofCompilation

/-!
# Dependent execution with a computed retained HOL proof

The actual total proof compiler supplies the argument of an arbitrary native
dependent body. Opening that body computes its beta result and its dependent
result type, using the existing capture-avoiding substitution. No replacement
proof is chosen, and the body need not itself be an encoded HOL proof.

The execution and substitution laws cover this beta boundary for every source
proof constructor and every law-bearing host with the required equality
operations. They do not claim termination of arbitrary declared computation
rules or formal verification of a runtime normalizer.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLDependentProofExecution

open Presentation Presentation.FormationSensitive FormationSensitiveHOLInterface
open Mettapedia.Logic HOL.ImpredicativeConnectives HOLNativeGenericProofCompiler
open HOLImpredicativeProofCompilation

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- The beta result is computed from the retained source proof and native body. -/
def execute (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (total : operations.raw.Total)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (source : HOL.ProofSyntax Const Δ φ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map expand).length → Tower.Tm n)
    (body : Tower.Tm (n + 1)) : Tower.Tm n :=
  inst0 (translateProof signature proofName operations total source objects hypotheses) body

/-- Every computed source proof can be used in a genuinely dependent native
body, not just as an assumption in another encoded HOL proof tree. -/
theorem execute_typed (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (total : operations.raw.Total)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (source : HOL.ProofSyntax Const Δ φ)
    {n : Nat} {target : Tower.Ctx n} {objects : Sub Tower.Head Γ.length n}
    {hypotheses : Fin (Δ.map expand).length → Tower.Tm n}
    (objectTyped : GenericTyping.Objects signature target objects)
    (hypothesisTyped : GenericTyping.Hypotheses signature operations target objects hypotheses)
    {body family : Tower.Tm (n + 1)}
    (bodyTyped : Typing operations.target
      (.snoc target (FormationSensitiveHOLGenericProofFamily.proof proofName
        (subst objects (HOLImpredicativeRepresentation.translate signature φ)))) body family) :
    Typing operations.target target
      (execute signature proofName operations total source objects hypotheses body)
      (execute signature proofName operations total source objects hypotheses family) :=
  bodyTyped.instantiate (translateProof_typed signature proofName operations total
    source objectTyped hypothesisTyped)

theorem execute_beta (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (total : operations.raw.Total)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (source : HOL.ProofSyntax Const Δ φ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map expand).length → Tower.Tm n) (body : Tower.Tm (n + 1)) :
    Step operations.target.headEq
      (.app (.lam body) (translateProof signature proofName operations total source objects hypotheses))
      (execute signature proofName operations total source objects hypotheses body)
      operations.target.computation := .betaPi _ _

/-- Executing then substituting agrees on the actual returned term with
substituting the object environment, hypotheses and dependent body first. -/
theorem execute_substitute (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (total : operations.raw.Total)
    (natural : operations.raw.Natural)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (source : HOL.ProofSyntax Const Δ φ)
    {n m : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map expand).length → Tower.Tm n)
    (body : Tower.Tm (n + 1)) (sigma : Sub Tower.Head n m) :
    execute signature proofName operations total source
        (fun i => subst sigma (objects i)) (fun i => subst sigma (hypotheses i))
        (subst (liftSub sigma) body) =
      subst sigma (execute signature proofName operations total source objects hypotheses body) := by
  simp only [execute, subst_inst0,
    translateProof_substitute signature proofName operations total natural]

namespace Controls

open HOL.UniformListInduction HOLNativeGenericProofCompiler.UniformList

private def compiled : Tower.Tm 0 :=
  translateProof FormationSensitiveHOLLeibnizInterface.signature proofName operations
    uniformList_total HOLImpredicativeProofCompilation.Controls.split Fin.elim0 Fin.elim0

private def proofType : Tower.Tm 0 :=
  FormationSensitiveHOLGenericProofFamily.proof proofName
    (HOLImpredicativeRepresentation.translate FormationSensitiveHOLLeibnizInterface.signature
      HOLImpredicativeProofCompilation.Controls.splitConclusion)

/-- The returned identity proof concerns the exact compiled witness, not an
independently supplied term with the same observable conclusion. -/
theorem reflexive_consumer_checked :
    Typing operations.target .nil
      (execute FormationSensitiveHOLLeibnizInterface.signature proofName operations
        uniformList_total HOLImpredicativeProofCompilation.Controls.split Fin.elim0 Fin.elim0
        (.refl (.var 0)))
      (.id proofType compiled compiled) := by
  simpa only [execute, inst0, subst, subst0, Fin.cases_zero, proofType, compiled] using
    (Typing.reflIntro HOLImpredicativeProofCompilation.Controls.split_compiles_typed)

end Controls

#print axioms execute_typed
#print axioms execute_beta
#print axioms execute_substitute
#print axioms Controls.reflexive_consumer_checked

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLDependentProofExecution
