import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.ProofPlanning
import Mettapedia.Logic.ProofSearch.Refinement
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerTyping

/-!
# Scoped HOL backward inferences through the native proof compiler

Each refinement below is implemented by an existing retained HOL proof
constructor. Introduction changes the child context or hypotheses explicitly;
elimination retains its actual scoped term argument. Reconstruction is not a
new proof authority. The one native compiler consumes its returned tree and
may still reject a constructor omitted by its selected operation algebra.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Logic.ProofSearch
namespace ProofObligations.HOL

open Mettapedia.Logic
open Presentation FormationSensitiveHOLInterface HOLNativeGenericProofCompiler

universe u v

variable {Base : Type u} {Const : Logic.HOL.Ty Base → Type v}
variable {context : Logic.HOL.Ctx Base}
variable {hypotheses : List (Logic.HOL.Formula Const context)}

/-- One child query with its actual syntax constructor. -/
def unary {goal : HOLAdapter.Goal Base Const} (child : HOLAdapter.Goal Base Const)
    (build : HOLAdapter.Solution child → HOLAdapter.Solution goal) :
    Refinement HOLAdapter.Solution goal where
  Premise := ULift.{max u v} (Fin 1)
  query _ := child
  rebuild answers := build (answers ⟨0⟩)

/-- Two separately indexed premises, even if their queries coincide. -/
def binary {goal : HOLAdapter.Goal Base Const} (first second : HOLAdapter.Goal Base Const)
    (build : HOLAdapter.Solution first → HOLAdapter.Solution second → HOLAdapter.Solution goal) :
    Refinement HOLAdapter.Solution goal where
  Premise := ULift.{max u v} (Fin 2)
  query occurrence := Fin.cases (motive := fun _ : Fin 2 => HOLAdapter.Goal Base Const)
    first (fun _ => second) occurrence.down
  rebuild answers := build (answers ⟨0⟩) (answers ⟨1⟩)

def impI (antecedent conclusion : Logic.HOL.Formula Const context) :
    Refinement HOLAdapter.Solution ⟨context, hypotheses, .imp antecedent conclusion⟩ :=
  unary ⟨context, antecedent :: hypotheses, conclusion⟩ Logic.HOL.ProofSyntax.impI

def impE (antecedent conclusion : Logic.HOL.Formula Const context) :
    Refinement HOLAdapter.Solution ⟨context, hypotheses, conclusion⟩ :=
  binary ⟨context, hypotheses, .imp antecedent conclusion⟩
    ⟨context, hypotheses, antecedent⟩ Logic.HOL.ProofSyntax.impE

def allI {type : Logic.HOL.Ty Base} (body : Logic.HOL.Formula Const (type :: context)) :
    Refinement HOLAdapter.Solution ⟨context, hypotheses, .all body⟩ :=
  unary ⟨type :: context, Logic.HOL.weakenHyps hypotheses, body⟩ Logic.HOL.ProofSyntax.allI

def allE {type : Logic.HOL.Ty Base} (body : Logic.HOL.Formula Const (type :: context))
    (argument : Logic.HOL.Term Const context type) :
    Refinement HOLAdapter.Solution
      ⟨context, hypotheses, Logic.HOL.instantiate argument body⟩ :=
  unary ⟨context, hypotheses, .all body⟩ (Logic.HOL.ProofSyntax.allE argument)

def andI (first second : Logic.HOL.Formula Const context) :
    Refinement HOLAdapter.Solution ⟨context, hypotheses, .and first second⟩ :=
  binary ⟨context, hypotheses, first⟩ ⟨context, hypotheses, second⟩ Logic.HOL.ProofSyntax.andI

def andEL (first second : Logic.HOL.Formula Const context) :
    Refinement HOLAdapter.Solution ⟨context, hypotheses, first⟩ :=
  unary ⟨context, hypotheses, .and first second⟩ Logic.HOL.ProofSyntax.andEL

def andER (first second : Logic.HOL.Formula Const context) :
    Refinement HOLAdapter.Solution ⟨context, hypotheses, second⟩ :=
  unary ⟨context, hypotheses, .and first second⟩ Logic.HOL.ProofSyntax.andER

def orIL (first second : Logic.HOL.Formula Const context) :
    Refinement HOLAdapter.Solution ⟨context, hypotheses, .or first second⟩ :=
  unary ⟨context, hypotheses, first⟩ Logic.HOL.ProofSyntax.orIL

def orIR (first second : Logic.HOL.Formula Const context) :
    Refinement HOLAdapter.Solution ⟨context, hypotheses, .or first second⟩ :=
  unary ⟨context, hypotheses, second⟩ Logic.HOL.ProofSyntax.orIR

def exI {type : Logic.HOL.Ty Base} (body : Logic.HOL.Formula Const (type :: context))
    (argument : Logic.HOL.Term Const context type) :
    Refinement HOLAdapter.Solution ⟨context, hypotheses, .ex body⟩ :=
  unary ⟨context, hypotheses, Logic.HOL.instantiate argument body⟩
    (Logic.HOL.ProofSyntax.exI argument)

/-- An explicit existing assumption occurrence discharges its own query. -/
def hyp (occurrence : Fin hypotheses.length) :
    Refinement HOLAdapter.Solution ⟨context, hypotheses, hypotheses.get occurrence⟩ :=
  Refinement.discharged (Logic.HOL.ProofSyntax.hyp occurrence)

/-- This calls reconstruction once and sends that returned tree to the one
generic compiler. A missing child does not produce a native proof. -/
def compile? {goal : HOLAdapter.Goal Base Const}
    (route : Refinement HOLAdapter.Solution goal)
    (candidate : ∀ index, Option (HOLAdapter.Solution (route.query index)))
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    {n : Nat} (objects : Sub Tower.Head goal.context.length n)
    (hypotheses : Fin goal.hypotheses.length → Tower.Tm n) : Option (Tower.Tm n) :=
  (route.tryRebuild candidate).bind (fun proof =>
    HOLNativeGenericProofCompiler.compile signature proofName operations proof objects hypotheses)

/-- Success retains every supplied child tree and the exact reconstructed
parent sent to compilation. -/
theorem compiled_from_answers {goal : HOLAdapter.Goal Base Const}
    (route : Refinement HOLAdapter.Solution goal)
    (candidate : ∀ index, Option (HOLAdapter.Solution (route.query index)))
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    {n : Nat} {objects : Sub Tower.Head goal.context.length n}
    {hypotheses : Fin goal.hypotheses.length → Tower.Tm n} {native : Tower.Tm n}
    (success : compile? route candidate signature proofName operations objects hypotheses = some native) :
    ∃ answers, (∀ index, candidate index = some (answers index)) ∧
      HOLNativeGenericProofCompiler.compile signature proofName operations
        (route.rebuild answers) objects hypotheses = some native := by
  cases reconstructed : route.tryRebuild candidate with
  | none => simp [compile?, reconstructed] at success
  | some proof =>
      obtain ⟨answers, actual, rebuilt⟩ :=
        (Refinement.tryRebuild_eq_some_iff route candidate proof).1 reconstructed
      refine ⟨answers, actual, ?_⟩
      simpa only [compile?, reconstructed, Option.bind_some, rebuilt] using success

theorem compiled_typed {goal : HOLAdapter.Goal Base Const}
    (route : Refinement HOLAdapter.Solution goal)
    (candidate : ∀ index, Option (HOLAdapter.Solution (route.query index)))
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    {n : Nat} {target : Tower.Ctx n} {objects : Sub Tower.Head goal.context.length n}
    {hypotheses : Fin goal.hypotheses.length → Tower.Tm n} {native : Tower.Tm n}
    (objectTyped : GenericTyping.Objects signature target objects)
    (hypothesisTyped : GenericTyping.Hypotheses signature operations target objects hypotheses)
    (success : compile? route candidate signature proofName operations objects hypotheses = some native) :
    ∃ code, represent signature goal.conclusion = some code ∧
      FormationSensitive.Typing operations.target target native
        (FormationSensitiveHOLGenericProofFamily.proof proofName (subst objects code)) := by
  obtain ⟨answers, _actual, compiled⟩ :=
    compiled_from_answers route candidate signature proofName operations success
  exact GenericTyping.compile_typed signature proofName operations
    (route.rebuild answers) objectTyped hypothesisTyped compiled

theorem compiled_denotes {goal : HOLAdapter.Goal Base Const}
    (route : Refinement HOLAdapter.Solution goal)
    (candidate : ∀ index, Option (HOLAdapter.Solution (route.query index)))
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    (semantics : GenericSemantics.Algebra signature proofName operations)
    {n : Nat} {objects : Sub Tower.Head goal.context.length n}
    {hypotheses : Fin goal.hypotheses.length → Tower.Tm n} {native : Tower.Tm n}
    (success : compile? route candidate signature proofName operations objects hypotheses = some native)
    (state : semantics.State objects)
    (hypothesesMeaning : GenericSemantics.Hypotheses semantics state hypotheses) :
    semantics.Denotes state native goal.conclusion := by
  obtain ⟨answers, _actual, compiled⟩ :=
    compiled_from_answers route candidate signature proofName operations success
  exact GenericSemantics.compile_denotes signature proofName operations semantics
    (route.rebuild answers) compiled state hypothesesMeaning

theorem missing_not_compiled {goal : HOLAdapter.Goal Base Const}
    (route : Refinement HOLAdapter.Solution goal)
    (candidate : ∀ index, Option (HOLAdapter.Solution (route.query index)))
    (missing : ∃ index, candidate index = none)
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    {n : Nat} (objects : Sub Tower.Head goal.context.length n)
    (hypotheses : Fin goal.hypotheses.length → Tower.Tm n) :
    compile? route candidate signature proofName operations objects hypotheses = none := by
  rw [compile?, (Refinement.tryRebuild_eq_none_iff route candidate).2 missing]
  rfl

#print axioms compiled_from_answers
#print axioms compiled_typed
#print axioms compiled_denotes
#print axioms missing_not_compiled

end ProofObligations.HOL
end Mettapedia.Logic.ProofSearch
