import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.GuardedEnvironmentBindings

/-!
# Logical closure of guarded source continuations

An actual value supplies an existential witness. Conversely, an existential
input opens its original guarded source binder for a retained continuation.
The continuation's result is independent of that input witness. Closed roots
remain explicit, and no witness-selection operation is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading

open Mettapedia.Logic
open Presentation TypedEquality.Annotated HOL.PredicateContexts
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
    {R : Rules Head} {P : ChurchRules R} {lex : LexicalReading Head Base Const}
    {Γ : HOL.Ctx Base} {carrier : HOL.Ty Base} {roots : List (HOL.ClosedFormula Const)}

namespace GuardedContext

def previous (context : GuardedContext P lex (carrier :: Γ)) : GuardedContext P lex Γ where
  source := match context.source with | .snoc prior _ => prior
  telescope := match context.telescope with | .snoc prior _ => prior
  formed := by
    rcases context with ⟨source, telescope, formed, reading⟩
    cases source
    cases telescope
    cases formed
    assumption
  reading := by
    rcases context with ⟨source, telescope, formed, reading⟩
    cases source
    cases telescope
    cases reading
    assumption

def lastType (context : GuardedContext P lex (carrier :: Γ)) : CTm Head Γ.length :=
  match context.source with | .snoc _ A => A

def lastPredicate (context : GuardedContext P lex (carrier :: Γ)) : HOL.Term Const Γ (carrier ⇒ .prop) :=
  match context.telescope with | .snoc _ predicate => predicate

theorem last_formed (context : GuardedContext P lex (carrier :: Γ)) :
    CIsType P context.previous.source context.lastType := by
  rcases context with ⟨source, telescope, formed, reading⟩
  cases source with
  | snoc prior A => cases telescope; cases formed; assumption

theorem last_read (context : GuardedContext P lex (carrier :: Γ)) :
    Reads lex context.lastType context.lastPredicate := by
  rcases context with ⟨source, telescope, formed, reading⟩
  cases source with
  | snoc prior A => cases telescope; cases reading; assumption

theorem rebuild (context : GuardedContext P lex (carrier :: Γ)) :
    context.previous.snoc context.lastPredicate context.last_read context.last_formed = context := by
  rcases context with ⟨source, telescope, formed, reading⟩
  cases source
  cases telescope
  rfl

private def exposeGuard (front : List (HOL.Formula Const Γ))
    (guard : HOL.Formula Const Γ) (tail : List (HOL.Formula Const Γ)) :
    HOL.ProofSyntax.HypothesisSubstitution (front ++ guard :: tail) (guard :: (front ++ tail)) :=
  HOL.ProofSyntax.HypothesisSubstitution.append front (guard :: tail) (guard :: (front ++ tail))
    (fun index => ((HOL.ProofSyntax.hyp (Δ := front) index).mono
      (HOL.ProofSyntax.OccurrenceMap.appendRight front tail)).prepend guard)
    (Fin.cases (.hyp 0) (fun index => ((HOL.ProofSyntax.hyp (Δ := tail) index).mono
      (HOL.ProofSyntax.OccurrenceMap.appendLeft front tail)).prepend guard))

private theorem exposeGuard_free (front : List (HOL.Formula Const Γ))
    (guard : HOL.Formula Const Γ) (tail : List (HOL.Formula Const Γ)) :
    ∀ occurrence, (exposeGuard front guard tail occurrence).FunctionExtensionalityFree := by
  apply HOL.ProofSyntax.HypothesisSubstitution.append_free
  · intro index
    simp only [HOL.ProofSyntax.prepend, HOL.ProofSyntax.functionExtensionalityFree_mono,
      HOL.ProofSyntax.FunctionExtensionalityFree]
  · intro occurrence
    refine Fin.cases ?_ (fun index => ?_) occurrence
    · trivial
    · simp only [Fin.cases_succ, HOL.ProofSyntax.prepend, HOL.ProofSyntax.functionExtensionalityFree_mono,
        HOL.ProofSyntax.FunctionExtensionalityFree]

def openGuard (context : GuardedContext P lex Γ)
    {sourceType : CTm Head Γ.length} (predicate : HOL.Term Const Γ (carrier ⇒ .prop))
    (reading : Reads lex sourceType predicate) (formed : CIsType P context.source sourceType)
    (goal : HOL.Formula Const (carrier :: Γ))
    (continuation : HOL.ProofSyntax Const ((context.snoc predicate reading formed).hypotheses roots) goal) :
    HOL.ProofSyntax Const
      (.app (HOL.weaken predicate) (.var .vz) :: HOL.weakenHyps (context.hypotheses roots)) goal := by
  let guard := HOL.Term.app (HOL.weaken predicate) (.var .vz)
  have exposed := HOL.ProofSyntax.substituteHypothesesCached
    (exposeGuard (assumptions roots (carrier :: Γ)) guard (HOL.weakenHyps context.telescope.hypotheses)) continuation
  apply HOL.ProofSyntax.castIndices ?_ rfl exposed
  simp only [hypotheses, HOL.weakenHyps, List.map_append]
  exact congrArg (fun front => guard :: (front ++ context.telescope.hypotheses.map HOL.weaken))
    (assumptions_weaken roots Γ carrier).symm

theorem openGuard_free (context : GuardedContext P lex Γ)
    {sourceType : CTm Head Γ.length} (predicate : HOL.Term Const Γ (carrier ⇒ .prop))
    (reading : Reads lex sourceType predicate) (formed : CIsType P context.source sourceType)
    (goal : HOL.Formula Const (carrier :: Γ))
    (continuation : HOL.ProofSyntax Const ((context.snoc predicate reading formed).hypotheses roots) goal)
    (free : continuation.FunctionExtensionalityFree) :
    (context.openGuard predicate reading formed goal continuation).FunctionExtensionalityFree := by
  unfold openGuard
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  rw [HOL.ProofSyntax.substituteHypothesesCached_eq]
  exact HOL.ProofSyntax.substituteHypotheses_free _ continuation free (exposeGuard_free _ _ _)

def closeWitness (context : GuardedContext P lex Γ)
    {sourceType : CTm Head Γ.length} (predicate : HOL.Term Const Γ (carrier ⇒ .prop))
    (reading : Reads lex sourceType predicate) (formed : CIsType P context.source sourceType)
    (goal : HOL.Formula Const Γ)
    (continuation : HOL.ProofSyntax Const ((context.snoc predicate reading formed).hypotheses roots) (HOL.weaken goal)) :
    HOL.ProofSyntax Const (context.hypotheses roots)
      (.imp (.ex (.app (HOL.weaken predicate) (.var .vz))) goal) :=
  let present := HOL.Term.ex (.app (HOL.weaken predicate) (.var .vz))
  let guard := HOL.Term.app (HOL.weaken predicate) (.var .vz)
  let opened := context.openGuard predicate reading formed (HOL.weaken goal) continuation
  .impI (.exE (.hyp 0) (opened.mono
    ((HOL.ProofSyntax.OccurrenceMap.prepend (HOL.weaken present)).lift guard)))

theorem closeWitness_free (context : GuardedContext P lex Γ)
    {sourceType : CTm Head Γ.length} (predicate : HOL.Term Const Γ (carrier ⇒ .prop))
    (reading : Reads lex sourceType predicate) (formed : CIsType P context.source sourceType)
    (goal : HOL.Formula Const Γ)
    (continuation : HOL.ProofSyntax Const ((context.snoc predicate reading formed).hypotheses roots) (HOL.weaken goal))
    (free : continuation.FunctionExtensionalityFree) :
    (context.closeWitness predicate reading formed goal continuation).FunctionExtensionalityFree := by
  unfold closeWitness
  constructor
  · trivial
  · apply (HOL.ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    exact context.openGuard_free predicate reading formed (HOL.weaken goal) continuation free

def closeLastWitness (context : GuardedContext P lex (carrier :: Γ)) (goal : HOL.Formula Const Γ)
    (continuation : HOL.ProofSyntax Const (context.hypotheses roots) (HOL.weaken goal)) :
    HOL.ProofSyntax Const (context.previous.hypotheses roots)
      (.imp (.ex (.app (HOL.weaken context.lastPredicate) (.var .vz))) goal) :=
  context.previous.closeWitness context.lastPredicate context.last_read context.last_formed goal
    (context.rebuild.symm ▸ continuation)

theorem closeLastWitness_free (context : GuardedContext P lex (carrier :: Γ)) (goal : HOL.Formula Const Γ)
    (continuation : HOL.ProofSyntax Const (context.hypotheses roots) (HOL.weaken goal))
    (free : continuation.FunctionExtensionalityFree) :
    (context.closeLastWitness goal continuation).FunctionExtensionalityFree := by
  rcases context with ⟨source, telescope, formed, reading⟩
  cases source
  cases telescope
  apply closeWitness_free
  exact free

def closeGuard (context : GuardedContext P lex Γ)
    {sourceType : CTm Head Γ.length} (predicate : HOL.Term Const Γ (carrier ⇒ .prop))
    (reading : Reads lex sourceType predicate) (formed : CIsType P context.source sourceType)
    (goal : HOL.Formula Const (carrier :: Γ))
    (continuation : HOL.ProofSyntax Const ((context.snoc predicate reading formed).hypotheses roots) goal) :
    HOL.ProofSyntax Const (context.hypotheses roots)
      (.all (.imp (.app (HOL.weaken predicate) (.var .vz)) goal)) :=
  .allI (.impI (context.openGuard predicate reading formed goal continuation))

theorem closeGuard_free (context : GuardedContext P lex Γ)
    {sourceType : CTm Head Γ.length} (predicate : HOL.Term Const Γ (carrier ⇒ .prop))
    (reading : Reads lex sourceType predicate) (formed : CIsType P context.source sourceType)
    (goal : HOL.Formula Const (carrier :: Γ))
    (continuation : HOL.ProofSyntax Const ((context.snoc predicate reading formed).hypotheses roots) goal)
    (free : continuation.FunctionExtensionalityFree) :
    (context.closeGuard predicate reading formed goal continuation).FunctionExtensionalityFree :=
  context.openGuard_free predicate reading formed goal continuation free

def closeLastGuard (context : GuardedContext P lex (carrier :: Γ)) (goal : HOL.Formula Const (carrier :: Γ))
    (continuation : HOL.ProofSyntax Const (context.hypotheses roots) goal) :
    HOL.ProofSyntax Const (context.previous.hypotheses roots)
      (.all (.imp (.app (HOL.weaken context.lastPredicate) (.var .vz)) goal)) :=
  context.previous.closeGuard context.lastPredicate context.last_read context.last_formed goal
    (context.rebuild.symm ▸ continuation)

theorem closeLastGuard_free (context : GuardedContext P lex (carrier :: Γ)) (goal : HOL.Formula Const (carrier :: Γ))
    (continuation : HOL.ProofSyntax Const (context.hypotheses roots) goal)
    (free : continuation.FunctionExtensionalityFree) :
    (context.closeLastGuard goal continuation).FunctionExtensionalityFree := by
  rcases context with ⟨source, telescope, formed, reading⟩
  cases source
  cases telescope
  apply closeGuard_free
  exact free

end GuardedContext

namespace GuardedRealizer

def witness {context : GuardedContext P lex Γ} {source type : CTm Head Γ.length}
    (realizer : GuardedRealizer roots context source type carrier) :
    HOL.ProofSyntax Const (context.hypotheses roots)
      (.ex (.app (HOL.weaken realizer.predicate) (.var .vz))) := by
  apply HOL.ProofSyntax.exI realizer.term
  apply HOL.ProofSyntax.castIndices rfl ?_ realizer.member
  simp only [HOL.instantiate, HOL.subst, HOL.Subst.single, HOL.PredicateFixedPoint.subst_single_weaken]

theorem witness_free {context : GuardedContext P lex Γ} {source type : CTm Head Γ.length}
    (realizer : GuardedRealizer roots context source type carrier) (free : realizer.Free) :
    realizer.witness.FunctionExtensionalityFree := by
  simpa only [witness, Free, HOL.ProofSyntax.FunctionExtensionalityFree,
    HOL.ProofSyntax.functionExtensionalityFree_castIndices] using free

end GuardedRealizer

#print axioms GuardedContext.closeLastWitness_free
#print axioms GuardedRealizer.witness_free

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
