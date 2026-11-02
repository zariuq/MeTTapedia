import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateRealizability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Reduction
import Mettapedia.Logic.HOL.ContextualTrinity

/-!
# Guarded dependent beta reduction and its HOL computation

Source typing and reduction are defined by the annotated calculus. Target
computation is the independently defined contextual HOL beta relation. A
represented function body and argument supply a typed source equality, an
actual target step and membership proofs at both endpoints. The codomain
guard is instantiated at the argument, rather than discarded.

This covers function beta at represented roots. It does not assert reflection
of arbitrary HOL reductions, nor a strict simulation of annotation steps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
open Mettapedia.Logic
open Presentation TypedEquality.Annotated
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
  {R : Rules Head} {P : ChurchRules R} {lex : LexicalReading Head Base Const}
  {Γ Ξ : HOL.Ctx Base} {roots : List (HOL.ClosedFormula Const)}

namespace GuardedBeta
variable [DecidableEq Base] {L : Type} [UniverseLevel.LevelOrder L]
  (levels : TypedEquality.Normalization.LevelModel R L)
  {context : GuardedContext P lex Γ} {domain codomain : HOL.Ty Base}
  {A argument : CTm Head Γ.length} {body B : CTm Head (Γ.length + 1)}
  (predicate : HOL.Term Const Γ (domain ⇒ .prop))
  (domainRead : Reads lex A predicate) (domainFormed : CIsType P context.source A)
  (familyFormed : CIsType P (.snoc context.source A) B)
  (bodyValue : GuardedRealizer roots (context.snoc predicate domainRead domainFormed) body B codomain)
  (argumentValue : GuardedRealizer roots context argument A domain)

def redex : GuardedRealizer roots context (.app (.lam A body) argument)
    (CTm.inst0 argument B) codomain :=
  (GuardedRealizer.abstraction levels predicate domainRead domainFormed familyFormed bodyValue).application
    argumentValue

omit [DecidableEq Base] in
include levels predicate domainRead domainFormed familyFormed bodyValue argumentValue in
theorem sourceEquality : CEqual P context.source (.app (.lam A body) argument)
    (CTm.inst0 argument body) (CTm.inst0 argument B) := by
  obtain ⟨_, allowed, typedPi⟩ := CIsType.pi levels domainFormed familyFormed
  exact .betaPi typedPi allowed bodyValue.typed argumentValue.typed

def reduct : GuardedRealizer roots context (CTm.inst0 argument body)
    (CTm.inst0 argument B) codomain :=
  (redex levels predicate domainRead domainFormed familyFormed bodyValue argumentValue).rewrite levels
    (sourceEquality levels predicate domainRead domainFormed familyFormed bodyValue argumentValue)
    (EqualityAt.beta domainRead bodyValue.termRead argumentValue.termRead)

theorem redex_code :
    (redex levels predicate domainRead domainFormed familyFormed bodyValue argumentValue).term =
      .app (.lam bodyValue.term) argumentValue.term := rfl

theorem reduct_code :
    (reduct levels predicate domainRead domainFormed familyFormed bodyValue argumentValue).term =
      HOL.instantiate argumentValue.term bodyValue.term := rfl

theorem guard :
    (redex levels predicate domainRead domainFormed familyFormed bodyValue argumentValue).predicate =
      HOL.instantiate argumentValue.term bodyValue.predicate := by
  apply Reader.term_unique
    (redex levels predicate domainRead domainFormed familyFormed bodyValue argumentValue).typeRead
  exact bodyValue.typeRead.instantiate argumentValue.termRead

theorem reduct_guard :
    (reduct levels predicate domainRead domainFormed familyFormed bodyValue argumentValue).predicate =
      HOL.instantiate argumentValue.term bodyValue.predicate :=
  guard levels predicate domainRead domainFormed familyFormed bodyValue argumentValue

omit [DecidableEq Base] in
/-- The source contraction exists independently of its predicate reading. -/
theorem sourceStep (root : CRootComputation Head) (headEq : Head → Head → Prop) :
    CStepCore root headEq (.app (.lam A body) argument) (CTm.inst0 argument body) :=
  .betaPi A body argument

/-- One source function contraction corresponds to one actual HOL beta step. -/
def targetStep : HOL.ContextualTrinity.BetaStep
    (redex levels predicate domainRead domainFormed familyFormed bodyValue argumentValue).term
    (reduct levels predicate domainRead domainFormed familyFormed bodyValue argumentValue).term :=
  .beta bodyValue.term argumentValue.term

def targetExecution : HOL.ContextualTrinity.Execution
    (redex levels predicate domainRead domainFormed familyFormed bodyValue argumentValue).term
    (reduct levels predicate domainRead domainFormed familyFormed bodyValue argumentValue).term :=
  .step (targetStep levels predicate domainRead domainFormed familyFormed bodyValue argumentValue) (.done _)

theorem redex_free (bodyFree : bodyValue.Free) (argumentFree : argumentValue.Free) :
    (redex levels predicate domainRead domainFormed familyFormed bodyValue argumentValue).Free :=
  GuardedRealizer.application_free _ _
    (GuardedRealizer.abstraction_free levels predicate domainRead domainFormed familyFormed bodyValue bodyFree)
    argumentFree

theorem reduct_free (bodyFree : bodyValue.Free) (argumentFree : argumentValue.Free) :
    (reduct levels predicate domainRead domainFormed familyFormed bodyValue argumentValue).Free := by
  apply GuardedRealizer.rewrite_free
  · exact redex_free levels predicate domainRead domainFormed familyFormed bodyValue argumentValue bodyFree argumentFree
  · trivial

/-- The target step survives any represented substitution, and both resulting
terms retain their independently transported source typing and guard proofs. -/
def substitutedTargetStep {target : GuardedContext P lex Ξ}
    {raw : CSub Head Γ.length Ξ.length} {code : HOL.Subst Const Γ Ξ}
    (substitution : GuardedSubstitution roots context target raw code) :
    HOL.ContextualTrinity.BetaStep
      ((redex levels predicate domainRead domainFormed familyFormed bodyValue argumentValue).substitute substitution).term
      ((reduct levels predicate domainRead domainFormed familyFormed bodyValue argumentValue).substitute substitution).term :=
  (targetStep levels predicate domainRead domainFormed familyFormed bodyValue argumentValue).subst code

end GuardedBeta

#print axioms GuardedBeta.sourceEquality
#print axioms GuardedBeta.reduct
#print axioms GuardedBeta.guard
#print axioms GuardedBeta.targetStep
#print axioms GuardedBeta.redex_free
#print axioms GuardedBeta.reduct_free
#print axioms GuardedBeta.substitutedTargetStep
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
