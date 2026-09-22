import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeTraceBetaInstantiation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedSubstitution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeTraceReductionBoundary

/-!
# Retained beta computation commutes with displayed substitution

Substituting a caller's environment before or after applying a supplied native
continuation gives the same actual native reduct and reindexed section.
The construction uses the existing context morphisms, component substitution,
and native opening law. Body and argument meanings retain their shared domain;
no preservation theorem for arbitrary raw denotations is asserted.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeTraceBetaNaturality

open Presentation
open Mettapedia.Logic.HOL.Embedding
open ZFSetContextualInterpretation (SetFamily Section Extension)
open NativeTraceLambdaSemantics NativeTraceContextMorphisms
open NativeTraceDisplayedSubstitution NativeTraceBetaInstantiation

universe u

/-- The environment square uses the actual supplied argument, not a fresh
projection standing in for it. -/
theorem argument_morphism_square {n m : Nat} {source : Context.{u} n}
    {target : Context.{u} m} (morphism : Morphism source target)
    {domain : SetFamily source.Environment} (argumentValue : Section domain) :
    (morphism.lift domain).comp
        (argumentMorphism target (morphism.reindexSection argumentValue)) =
      (argumentMorphism source argumentValue).comp morphism := rfl

/-- Native opening and caller substitution commute on the actual syntax,
including the lifted substitution beneath the continuation's binder. -/
theorem instantiation_substitute_erase {n m : Nat} {source : Context.{u} n}
    {target : Context.{u} m} {morphism : Morphism source target}
    (sigma : Substitution source target morphism)
    {domain : SetFamily source.Environment}
    {argument : NativeTraceLambdaSemantics.Tm n} {argumentValue : Section domain}
    (argumentMeaning : Denotes source argument domain argumentValue)
    (body : NativeTraceLambdaSemantics.Tm (n + 1)) :
    ((body.subst (argumentSubstitution argumentMeaning).term).subst sigma.term).erase =
      ((body.subst (sigma.lift domain).term).subst
        (argumentSubstitution (substitute_denotes sigma argumentMeaning)).term).erase := by
  calc
    _ = Presentation.subst (fun index => (sigma.term index).erase)
        (inst0 argument.erase body.erase) := by
      rw [NativeTraceLambdaSemantics.Tm.erase_subst, instantiation_erase]
    _ = inst0 (argument.subst sigma.term).erase
        (body.subst (sigma.lift domain).term).erase := by
      rw [subst_inst0, NativeTraceLambdaSemantics.Tm.erase_subst,
        NativeTraceLambdaSemantics.Tm.erase_subst]
      congr 1
      apply congrArg (fun substitution => Presentation.subst substitution body.erase)
      funext index
      exact (erase_liftSubTm sigma.term index).symm
    _ = _ := (instantiation_erase (substitute_denotes sigma argumentMeaning)
      (body.subst (sigma.lift domain).term)).symm

/-- The displayed substitution of an aligned beta square retains its exact
directed computation and section in the caller's context. No root-rule
semantic law is required because the actual step is built-in beta. -/
theorem beta_substitution_square {n m : Nat} {source : Context.{u} n}
    {target : Context.{u} m} {morphism : Morphism source target}
    (sigma : Substitution source target morphism)
    {domain : SetFamily source.Environment} {codomain : SetFamily (Extension domain)}
    {body : NativeTraceLambdaSemantics.Tm (n + 1)}
    {argument : NativeTraceLambdaSemantics.Tm n}
    {bodyValue : Section codomain} {argumentValue : Section domain}
    (bodyMeaning : Denotes (source.snoc domain) body codomain bodyValue)
    (argumentMeaning : Denotes source argument domain argumentValue)
    (headEquality : Tower.Head → Tower.Head → Prop)
    (root : RootComputation Tower.Head) :
    Step headEquality
        ((NativeTraceLambdaSemantics.Tm.app (.lam body) argument).subst sigma.term).erase
        ((body.subst (argumentSubstitution argumentMeaning).term).subst sigma.term).erase root ∧
      Denotes target
        ((NativeTraceLambdaSemantics.Tm.app (.lam body) argument).subst sigma.term)
        (fun point => codomain ⟨morphism.environment point,
          argumentValue (morphism.environment point)⟩)
        (fun point => bodyValue ⟨morphism.environment point,
          argumentValue (morphism.environment point)⟩) ∧
      Denotes target
        ((body.subst (argumentSubstitution argumentMeaning).term).subst sigma.term)
        (fun point => codomain ⟨morphism.environment point,
          argumentValue (morphism.environment point)⟩)
        (fun point => bodyValue ⟨morphism.environment point,
          argumentValue (morphism.environment point)⟩) := by
  refine ⟨?_, substitute_denotes sigma
    (NativeTraceLambdaSemantics.beta bodyMeaning argumentMeaning),
    substitute_denotes sigma (instantiate_denotes bodyMeaning argumentMeaning)⟩
  rw [instantiation_substitute_erase sigma argumentMeaning body]
  exact (beta_square (substitute_denotes (sigma.lift domain) bodyMeaning)
    (substitute_denotes sigma argumentMeaning) headEquality root).1

namespace Controls

open NativeTraceReductionBoundary (context unitFamily nonemptyValue nonemptyValue_ne_empty)

def targetContext : Context.{u} 2 := context.snoc unitFamily

/-- A genuine nonidentity caller substitution adds a fresh variable while
retaining the old variable at index one. -/
def weakening : Substitution context.{u} targetContext
    (Morphism.weaken context unitFamily) where
  term index := .var index.succ
  component index := Denotes.var targetContext index.succ

theorem old_continuation_survives_new_binder
    (headEquality : Tower.Head → Tower.Head → Prop)
    (root : RootComputation Tower.Head) :
    Step headEquality (.app (.lam (.var (2 : Fin 3))) (.var (1 : Fin 2)))
        (.var (1 : Fin 2)) root ∧
      Denotes targetContext.{u} (.app (.lam (.var 2)) (.var 1))
        (fun point => context.family 0 point.1)
        (fun point => context.projection 0 point.1) ∧
      Denotes targetContext.{u} (.var 1)
        (fun point => context.family 0 point.1)
        (fun point => context.projection 0 point.1) := by
  have oldIndex : (0 : Fin 1).succ = (1 : Fin 2) := by decide
  have bodyIndex : (1 : Fin 2).succ = (2 : Fin 3) := by decide
  have square := beta_substitution_square weakening.{u}
    (Denotes.var (context.snoc (context.family 0)) (0 : Fin 1).succ)
    (Denotes.var context 0) headEquality root
  simp only [NativeTraceLambdaSemantics.Tm.subst, liftSubTm, weakening,
    argumentSubstitution, Fin.cases_succ, Fin.cases_zero,
    NativeTraceLambdaSemantics.Tm.rename, NativeTraceLambdaSemantics.Tm.erase, wk,
    Context.snoc_family_succ, Context.snoc_projection_succ] at square
  simpa only [oldIndex, bodyIndex, Morphism.weaken] using square

theorem old_and_new_terms_differ :
    (NativeTraceLambdaSemantics.Tm.var (1 : Fin 2)) ≠ .var 0 := by decide

/-- Replacing the retained old result by the fresh empty-valued projection
cannot satisfy the same semantic evidence. -/
theorem fresh_projection_not_old_result :
    ¬ Denotes targetContext.{u} (.var 0)
      (fun point => context.family 0 point.1)
      (fun point => context.projection 0 point.1) := by
  intro meaning
  have familyEquality := NativeTraceReductionBoundary.variable_family meaning
  let point : targetContext.{u}.Environment :=
    ⟨PUnit.unit, ⟨∅, ZFSet.mem_singleton.mpr rfl⟩⟩
  have atPoint : ({nonemptyValue} : ZFSet.{u}) = {∅} := congrFun familyEquality point
  have member : nonemptyValue.{u} ∈ ({∅} : ZFSet.{u}) :=
    atPoint ▸ ZFSet.mem_singleton.mpr rfl
  exact nonemptyValue_ne_empty (ZFSet.mem_singleton.mp member)

end Controls
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeTraceBetaNaturality
