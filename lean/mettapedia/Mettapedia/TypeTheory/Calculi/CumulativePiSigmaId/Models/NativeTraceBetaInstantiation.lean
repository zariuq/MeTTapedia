import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeTraceDisplayedSubstitution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeTraceFamilyRealization

/-!
# Native beta retains the actual trace section through substitution

Instantiation is the existing displayed substitution along comprehension by
the interpreted argument. The redex and the actual substituted native body
therefore have the same retained section. Erasure exposes a directed beta
step in the existing native reduction relation.

This theorem concerns supplied body and argument meanings. It does not claim
uniqueness of every possible denotation of unannotated syntax, soundness of
arbitrary conversion, or implementation correspondence.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeTraceBetaInstantiation

open Presentation
open Mettapedia.Logic.HOL.Embedding
open ZFSetContextualInterpretation (SetFamily Section Extension)
open NativeTraceLambdaSemantics
open NativeTraceContextMorphisms
open NativeTraceDisplayedSubstitution

universe u

/-- Extend an environment by the actual interpreted argument. -/
def argumentMorphism {n : Nat} (context : Context.{u} n)
    {domain : SetFamily context.Environment} (argumentValue : Section domain) :
    Morphism (context.snoc domain) context where
  environment point := ⟨point, argumentValue point⟩

/-- The newest component is the supplied term; old components retain their
original variable projections. -/
def argumentSubstitution {n : Nat} {context : Context.{u} n}
    {domain : SetFamily context.Environment} {argument : NativeTraceLambdaSemantics.Tm n}
    {argumentValue : Section domain}
    (argumentMeaning : Denotes context argument domain argumentValue) :
    Substitution (context.snoc domain) context (argumentMorphism context argumentValue) where
  term := Fin.cases argument NativeTraceLambdaSemantics.Tm.var
  component index := by
    refine Fin.cases ?_ (fun prior => ?_) index
    · exact argumentMeaning
    · exact Denotes.var context prior

@[simp] theorem argumentSubstitution_erase {n : Nat} {context : Context.{u} n}
    {domain : SetFamily context.Environment} {argument : NativeTraceLambdaSemantics.Tm n}
    {argumentValue : Section domain}
    (argumentMeaning : Denotes context argument domain argumentValue)
    (index : Fin (n + 1)) :
    ((argumentSubstitution argumentMeaning).term index).erase = subst0 argument.erase index := by
  refine Fin.cases ?_ (fun prior => ?_) index <;> rfl

/-- Simultaneous native substitution computes the supplied body's retained
section at the environment extended by the supplied argument. -/
theorem instantiate_denotes {n : Nat} {context : Context.{u} n}
    {domain : SetFamily context.Environment} {codomain : SetFamily (Extension domain)}
    {body : NativeTraceLambdaSemantics.Tm (n + 1)}
    {argument : NativeTraceLambdaSemantics.Tm n}
    {bodyValue : Section codomain} {argumentValue : Section domain}
    (bodyMeaning : Denotes (context.snoc domain) body codomain bodyValue)
    (argumentMeaning : Denotes context argument domain argumentValue) :
    Denotes context
      (body.subst (argumentSubstitution argumentMeaning).term)
      (fun point => codomain ⟨point, argumentValue point⟩)
      (fun point => bodyValue ⟨point, argumentValue point⟩) :=
  substitute_denotes (argumentSubstitution argumentMeaning) bodyMeaning

theorem instantiation_erase {n : Nat} {context : Context.{u} n}
    {domain : SetFamily context.Environment} {argument : NativeTraceLambdaSemantics.Tm n}
    {argumentValue : Section domain}
    (argumentMeaning : Denotes context argument domain argumentValue)
    (body : NativeTraceLambdaSemantics.Tm (n + 1)) :
    (body.subst (argumentSubstitution argumentMeaning).term).erase =
      inst0 argument.erase body.erase := by
  rw [NativeTraceLambdaSemantics.Tm.erase_subst]
  unfold inst0
  exact congrArg (fun sigma => Presentation.subst sigma body.erase)
    (funext (argumentSubstitution_erase argumentMeaning))

/-- The actual beta redex, its actual substituted body, and the directed
native beta step share the same supplied section, for any native rule package. -/
theorem beta_square {n : Nat} {context : Context.{u} n}
    {domain : SetFamily context.Environment} {codomain : SetFamily (Extension domain)}
    {body : NativeTraceLambdaSemantics.Tm (n + 1)}
    {argument : NativeTraceLambdaSemantics.Tm n}
    {bodyValue : Section codomain} {argumentValue : Section domain}
    (bodyMeaning : Denotes (context.snoc domain) body codomain bodyValue)
    (argumentMeaning : Denotes context argument domain argumentValue)
    (headEquality : Tower.Head → Tower.Head → Prop)
    (root : RootComputation Tower.Head) :
    Step headEquality (.app (.lam body.erase) argument.erase)
        (body.subst (argumentSubstitution argumentMeaning).term).erase root ∧
      Denotes context (.app (.lam body) argument)
        (fun point => codomain ⟨point, argumentValue point⟩)
        (fun point => bodyValue ⟨point, argumentValue point⟩) ∧
      Denotes context (body.subst (argumentSubstitution argumentMeaning).term)
        (fun point => codomain ⟨point, argumentValue point⟩)
        (fun point => bodyValue ⟨point, argumentValue point⟩) := by
  refine ⟨?_, NativeTraceLambdaSemantics.beta bodyMeaning argumentMeaning,
    instantiate_denotes bodyMeaning argumentMeaning⟩
  rw [instantiation_erase argumentMeaning]
  exact .betaPi body.erase argument.erase

/-- Instantiating a binder does not replace an older contextual projection
by the newest argument. This uses the actual lifted variable index. -/
theorem older_projection_square {n : Nat} {context : Context.{u} n}
    {domain : SetFamily context.Environment} {argument : NativeTraceLambdaSemantics.Tm n}
    {argumentValue : Section domain}
    (argumentMeaning : Denotes context argument domain argumentValue) (index : Fin n)
    (headEquality : Tower.Head → Tower.Head → Prop)
    (root : RootComputation Tower.Head) :
    Step headEquality (.app (.lam (.var index.succ)) argument.erase) (.var index) root ∧
      Denotes context (.app (.lam (.var index.succ)) argument)
        (context.family index) (context.projection index) ∧
      Denotes context (.var index) (context.family index) (context.projection index) :=
  beta_square (Denotes.var (context.snoc domain) index.succ)
    argumentMeaning headEquality root

namespace Controls

open ZFSetContextualInterpretation.Controls (domain codomain body zeroArgument oneArgument)
open NativeTraceFamilyRealization.Controls (functionContext applicationProgram application_denotes)

/-- A beta-redex consumes the existing input-dependent program as its
argument, retaining the real dependent result fibre and section. -/
theorem dependent_application_square
    (headEquality : Tower.Head → Tower.Head → Prop)
    (root : RootComputation Tower.Head) :
    Step headEquality
        (.app (.lam (.var 0)) applicationProgram.erase)
        applicationProgram.erase root ∧
      Denotes (functionContext.{u}.snoc domain)
        (.app (.lam (.var 0)) applicationProgram) codomain body ∧
      Denotes (functionContext.{u}.snoc domain) applicationProgram codomain body := by
  have identityBody := Denotes.var
    ((functionContext.{u}.snoc domain).snoc codomain) 0
  exact beta_square identityBody application_denotes headEquality root

theorem dependent_result_changes :
    (body.{u} ⟨PUnit.unit, zeroArgument PUnit.unit⟩).1 ≠
      (body ⟨PUnit.unit, oneArgument PUnit.unit⟩).1 := by
  exact Ne.symm NativeTraceFamilyRealization.Controls.wrong_constant_application

/-- The preserved section cannot be replaced by a constant-empty return. -/
theorem wrong_constant_return :
    ¬ ∀ point : Extension domain.{u}, (body point).1 = ∅ := by
  intro constantReturn
  exact NativeTraceFamilyRealization.Controls.wrong_constant_application
    (constantReturn ⟨PUnit.unit, oneArgument PUnit.unit⟩)

end Controls

#print axioms argumentSubstitution
#print axioms argumentSubstitution_erase
#print axioms instantiate_denotes
#print axioms instantiation_erase
#print axioms beta_square
#print axioms older_projection_square
#print axioms Controls.dependent_application_square
#print axioms Controls.dependent_result_changes
#print axioms Controls.wrong_constant_return

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeTraceBetaInstantiation
