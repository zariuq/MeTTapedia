import Mettapedia.Logic.ProofSearch.Planning
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerSemantics

/-! # HOL goal planning and compilation into dependent declarations -/
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
set_option autoImplicit false
namespace Mettapedia.Logic.ProofSearch
universe u v w x y z
namespace HOLAdapter

open Mettapedia.Logic

/-- A HOL goal retains its object context, hypotheses, and conclusion in one
dependent package. -/
structure Goal (Base : Type u) (Const : HOL.Ty Base → Type v) where
  context : HOL.Ctx Base
  hypotheses : List (HOL.Formula Const context)
  conclusion : HOL.Formula Const context

abbrev Solution {Base : Type u} {Const : HOL.Ty Base → Type v}
    (goal : Goal Base Const) : Type (max u v) :=
  HOL.ProofSyntax Const goal.hypotheses goal.conclusion

/-- There are no accepted counter-certificates in a proof-only workload. -/
def noCounter {Base : Type u} {Const : HOL.Ty Base → Type v} :
    CounterSystem (Goal Base Const) Solution where
  Certificate := fun _ => ULift.{max u v} Empty
  check := fun {_goal} certificate => nomatch certificate.down
  sound := by
    intro goal certificate accepted proof
    exact nomatch certificate.down

open Presentation FormationSensitiveHOLInterface
open HOLNativeGenericProofCompiler

/-- Compile only a solved outcome.  Other search outcomes produce no native
term and therefore cannot be mistaken for successful proof compilation. -/
def compileOutcome? {Base : Type u} {Const : HOL.Ty Base → Type v}
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    {counter : CounterSystem (Goal Base Const) Solution}
    {Constraint : Goal Base Const → Type (max u v)} {goal : Goal Base Const}
    (outcome : Outcome Solution counter Constraint goal)
    {n : Nat} (objects : Sub Tower.Head goal.context.length n)
    (hypotheses : Fin goal.hypotheses.length → Tower.Tm n) : Option (Tower.Tm n) :=
  match outcome with
  | .solved proof => compile signature proofName operations proof objects hypotheses
  | .refuted _ _ | .constrained _ | .exhausted _ => none

/-- Semantic correctness of a solved plan result is inherited from the one
generic proof compiler.  There is no second semantic compiler for plans. -/
theorem compileOutcome_denotes {Base : Type u} {Const : HOL.Ty Base → Type v}
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    (semantics : GenericSemantics.Algebra signature proofName operations)
    {counter : CounterSystem (Goal Base Const) Solution}
    {Constraint : Goal Base Const → Type (max u v)} {goal : Goal Base Const}
    (outcome : Outcome Solution counter Constraint goal)
    {n : Nat} {objects : Sub Tower.Head goal.context.length n}
    {hypotheses : Fin goal.hypotheses.length → Tower.Tm n}
    {native : Tower.Tm n}
    (success : compileOutcome? signature proofName operations outcome objects hypotheses =
      some native) (state : semantics.State objects)
    (hypothesesMeaning : GenericSemantics.Hypotheses semantics state hypotheses) :
    semantics.Denotes state native goal.conclusion := by
  cases outcome with
  | solved proof =>
      exact GenericSemantics.compile_denotes signature proofName operations semantics
        proof success state hypothesesMeaning
  | refuted certificate accepted => simp [compileOutcome?] at success
  | constrained residual => simp [compileOutcome?] at success
  | exhausted failure => simp [compileOutcome?] at success

/-- Compilation is an evidence-bearing stage whose witness is the successful
equation returned by the one generic compiler. -/
def compilationStage {Base : Type u} {Const : HOL.Ty Base → Type v}
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    {counter : CounterSystem (Goal Base Const) Solution}
    {Constraint : Goal Base Const → Type (max u v)} {goal : Goal Base Const}
    (n : Nat) (objects : Sub Tower.Head goal.context.length n)
    (hypotheses : Fin goal.hypotheses.length → Tower.Tm n) :
    Stage (Outcome Solution counter Constraint goal) (Tower.Tm n) where
  Evidence outcome native :=
    PLift
      (compileOutcome? signature proofName operations outcome objects hypotheses =
        some native)

end HOLAdapter

end Mettapedia.Logic.ProofSearch
