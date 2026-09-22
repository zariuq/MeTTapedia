import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeTraceContextMorphisms

/-!
# Displayed substitution for native trace terms

A displayed renaming pairs the native de Bruijn action with a semantic context
morphism and proves that every selected variable family and projection commute.
A displayed substitution replaces those selected variables by actual native
trace terms with the corresponding meanings.

Both structures lift through context comprehension.  The main theorems state
that native renaming and capture-avoiding simultaneous substitution commute
with trace denotation.  No equality of whole dependent context records is
used; the required fibre transports are explicit in `castSection`.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeTraceDisplayedSubstitution

open Presentation
open Mettapedia.Logic.HOL.Embedding
open ZFSetContextualInterpretation (SetFamily Section Extension)
open NativeTraceLambdaSemantics
open NativeTraceContextMorphisms

universe u

def castSection {Gamma : Type (u + 1)} {a b : SetFamily Gamma}
    (equal : a = b) (termSection : Section a) : Section b :=
  equal ▸ termSection

@[simp] theorem castSection_rfl {Gamma : Type (u + 1)}
    {a : SetFamily Gamma} (termSection : Section a) :
    castSection rfl termSection = termSection := rfl

theorem castSection_precompose {Gamma Delta : Type (u + 1)}
    {a b : SetFamily Gamma} (equal : a = b) (termSection : Section a)
    (theta : Delta → Gamma) :
    castSection (congrArg (fun family => family ∘ theta) equal)
        (fun point => termSection (theta point)) =
      fun point => castSection equal termSection (theta point) := by
  cases equal
  rfl

/-- A de Bruijn renaming displayed over its semantic context morphism. -/
structure Renaming {n m : Nat} (source : Context.{u} n) (target : Context.{u} m)
    (rho : Ren n m) (morphism : Morphism source target) where
  familyEq : ∀ index, target.family (rho index) =
    morphism.reindexFamily (source.family index)
  projectionEq : ∀ index,
    castSection (familyEq index) (target.projection (rho index)) =
      morphism.reindexSection (source.projection index)

theorem Renaming.identity {n : Nat} (context : Context.{u} n) :
    Renaming context context id (Morphism.identity context) where
  familyEq _ := rfl
  projectionEq _ := rfl

theorem Renaming.weaken {n : Nat} (context : Context.{u} n)
    (family : SetFamily context.Environment) :
    Renaming context (context.snoc family) wk (Morphism.weaken context family) where
  familyEq _ := rfl
  projectionEq _ := rfl

/-- Lift both the syntactic renaming and its semantic map under one binder. -/
theorem Renaming.lift {n m : Nat} {source : Context.{u} n} {target : Context.{u} m}
    {rho : Ren n m} {morphism : Morphism source target}
    (displayed : Renaming source target rho morphism)
    (family : SetFamily source.Environment) :
    Renaming (source.snoc family)
      (target.snoc (morphism.reindexFamily family))
      (liftRen rho) (morphism.lift family) where
  familyEq index := by
    refine Fin.cases ?_ (fun prior => ?_) index
    · rfl
    · apply funext
      intro point
      exact congrFun (displayed.familyEq prior) point.1
  projectionEq index := by
    refine Fin.cases ?_ (fun prior => ?_) index
    · rfl
    · change castSection
          (congrArg (fun displayedFamily => displayedFamily ∘ Sigma.fst)
            (displayed.familyEq prior))
          (fun point => target.projection (rho prior) point.1) =
        fun point : Extension (morphism.reindexFamily family) =>
          source.projection prior (morphism.environment point.1)
      rw [castSection_precompose]
      exact congrArg
        (fun termSection : Section (morphism.reindexFamily (source.family prior)) =>
          fun point : Extension (morphism.reindexFamily family) => termSection point.1)
        (displayed.projectionEq prior)

theorem change_denoted_section {n : Nat} {context : Context.{u} n}
    {term : NativeTraceLambdaSemantics.Tm n}
    {family : SetFamily context.Environment} {first second : Section family}
    (meaning : Denotes context term family first) (equal : first = second) :
    Denotes context term family second := by
  cases equal
  exact meaning

/-- Native renaming is reindexing along the displayed context morphism. -/
theorem rename_denotes {n m : Nat} {source : Context.{u} n}
    {target : Context.{u} m} {rho : Ren n m}
    {morphism : Morphism source target}
    (displayed : Renaming source target rho morphism)
    {term : NativeTraceLambdaSemantics.Tm n}
    {family : SetFamily source.Environment} {value : Section family}
    (meaning : Denotes source term family value) :
    Denotes target (term.rename rho) (morphism.reindexFamily family)
      (morphism.reindexSection value) := by
  induction meaning generalizing m with
  | var context index =>
      have selected := Denotes.var target (rho index)
      have transported := selected.cast (displayed.familyEq index)
      exact change_denoted_section transported (displayed.projectionEq index)
  | @lam n context domain codomain body bodyValue bodyMeaning inductionHypothesis =>
      have bodyRenamed := inductionHypothesis (displayed.lift domain)
      have abstraction := Denotes.lam bodyRenamed
      exact abstraction
  | @app n context domain codomain function argument functionValue argumentValue
      functionMeaning argumentMeaning functionInduction argumentInduction =>
      have functionRenamed := functionInduction displayed
      have argumentRenamed := argumentInduction displayed
      have functionForApplication :
          Denotes target (function.rename rho)
            (ZFSetTraceContextual.piFamily (morphism.reindexFamily domain)
              (codomain ∘ (morphism.lift domain).environment))
            (morphism.reindexSection functionValue) :=
        functionRenamed.cast (by rfl)
      have application := Denotes.app
        (a := morphism.reindexFamily domain)
        (b := codomain ∘ (morphism.lift domain).environment)
        functionForApplication argumentRenamed
      exact application

/-- A native substitution displayed over the semantic map it denotes. -/
structure Substitution {n m : Nat} (source : Context.{u} n) (target : Context.{u} m)
    (morphism : Morphism source target) where
  term : Fin n → NativeTraceLambdaSemantics.Tm m
  component : ∀ index, Denotes target (term index)
    (morphism.reindexFamily (source.family index))
    (morphism.reindexSection (source.projection index))

def Substitution.identity {n : Nat} (context : Context.{u} n) :
    Substitution context context (Morphism.identity context) where
  term := .var
  component index := .var context index

/-- Lift a displayed substitution beneath context comprehension. -/
def Substitution.lift {n m : Nat} {source : Context.{u} n}
    {target : Context.{u} m} {morphism : Morphism source target}
    (substitution : Substitution source target morphism)
    (family : SetFamily source.Environment) :
    Substitution (source.snoc family)
      (target.snoc (morphism.reindexFamily family)) (morphism.lift family) where
  term := liftSubTm substitution.term
  component index := by
    refine Fin.cases ?_ (fun prior => ?_) index
    · exact .var _ 0
    · exact rename_denotes (Renaming.weaken target (morphism.reindexFamily family))
        (substitution.component prior)

/-- Capture-avoiding native substitution commutes with the represented
contextual substitution. -/
theorem substitute_denotes {n m : Nat} {source : Context.{u} n}
    {target : Context.{u} m} {morphism : Morphism source target}
    (substitution : Substitution source target morphism)
    {term : NativeTraceLambdaSemantics.Tm n}
    {family : SetFamily source.Environment} {value : Section family}
    (meaning : Denotes source term family value) :
    Denotes target (term.subst substitution.term)
      (morphism.reindexFamily family) (morphism.reindexSection value) := by
  induction meaning generalizing m with
  | var context index => exact substitution.component index
  | @lam n context domain codomain body bodyValue bodyMeaning inductionHypothesis =>
      have bodySubstituted := inductionHypothesis (substitution.lift domain)
      have abstraction := Denotes.lam bodySubstituted
      exact abstraction
  | @app n context domain codomain function argument functionValue argumentValue
      functionMeaning argumentMeaning functionInduction argumentInduction =>
      have functionSubstituted := functionInduction substitution
      have argumentSubstituted := argumentInduction substitution
      have functionForApplication :
          Denotes target (function.subst substitution.term)
            (ZFSetTraceContextual.piFamily (morphism.reindexFamily domain)
              (codomain ∘ (morphism.lift domain).environment))
            (morphism.reindexSection functionValue) :=
        functionSubstituted.cast (by rfl)
      have application := Denotes.app
        (a := morphism.reindexFamily domain)
        (b := codomain ∘ (morphism.lift domain).environment)
        functionForApplication argumentSubstituted
      exact application

@[simp] theorem Substitution.identity_term {n : Nat} (context : Context.{u} n) :
    (Substitution.identity context).term = NativeTraceLambdaSemantics.Tm.var := rfl

#print axioms castSection_precompose
#print axioms Renaming.lift
#print axioms rename_denotes
#print axioms Substitution.lift
#print axioms substitute_denotes

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeTraceDisplayedSubstitution
