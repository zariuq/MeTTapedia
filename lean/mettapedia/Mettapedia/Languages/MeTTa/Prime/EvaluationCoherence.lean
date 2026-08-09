import Mettapedia.GSLT.Core.Ultrainfinite
import Mettapedia.Languages.MeTTa.Prime.Language

/-!
# A two-dimensional coherence witness for Prime evaluation

Prime exposes two routes from an evaluation request to the same occurrence:

* the one-step extensional route supplied by the query-derived evaluator;
* the three-step lazy route that enters a revision-keyed Need cell and returns.

`Prime.Language` proves both paths in the interacting semantic GSLT.  This
module retains the corresponding steps as type-valued route data and supplies
one authored 2-generator comparing them.  Its free closure under vertical
composition and whiskering is the existing `GeneratedTwoCell` construction.

This is deliberately a finite two-dimensional nucleus.  It is not a claim
that all bicategorical coherence laws, much less an `(infinity,2)`-completion,
have already been constructed.
-/

namespace Mettapedia.Languages.MeTTa.Prime.EvaluationCoherence

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Languages.MeTTa.Prime.Language
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Prime steps retained as data rather than propositionally truncated. -/
abbrev CarriedStep (model : Model) (source target : (kernelGSLT model).Term) :=
  PLift ((kernelGSLT model).Step source target)

/-- The direct extensional route for one result occurrence. -/
def directRoute (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.toModel space subject)) :
    Route (CarriedStep model)
      ((evaluationKernelEmbedding model).toFun (.request space subject))
      ((evaluationKernelEmbedding model).toFun
        (.answer space subject occurrence result)) :=
  .cons ⟨((evaluationKernelEmbedding model).step_iff _ _).2
    (MeTTaZero.EvaluationStep.found copy)⟩ (.refl _)

/-- The lazy route through Need for the same result occurrence. -/
def lazyRoute (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.toModel space subject)) :
    Route (CarriedStep model)
      ((evaluationKernelEmbedding model).toFun (.request space subject))
      ((evaluationKernelEmbedding model).toFun
        (.answer space subject occurrence result)) :=
  .cons ⟨evaluation_enters_need model space subject⟩
    (.cons ⟨((needEmbedding model).step_iff _ _).2 (NeedStep.found copy)⟩
      (.cons ⟨need_returns_evaluation model space subject occurrence result⟩
        (.refl _)))

/-- Every proof-relevant Prime route conserves the common occurrence-bag
interpretation.  The theorem is route-generic: direct interpretation, lazy
Need execution, and later certified routes all use the same step law. -/
theorem route_preserves_meaning (model : Model)
    {source target : (kernelGSLT model).Term}
    (route : Route (CarriedStep model) source target) :
    (kernelElaboration model).elaborate source =
      (kernelElaboration model).elaborate target :=
  Route.observe_eq_of_route (kernelElaboration model).elaborate
    (fun step => kernel_step_preserves_meaning model step.down) route

/-- The one-step extensional route preserves the complete answer bag. -/
theorem directRoute_preserves_meaning (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.toModel space subject)) :
    (kernelElaboration model).elaborate
        ((evaluationKernelEmbedding model).toFun (.request space subject)) =
      (kernelElaboration model).elaborate
        ((evaluationKernelEmbedding model).toFun
          (.answer space subject occurrence result)) :=
  route_preserves_meaning model
    (directRoute model space subject result occurrence copy)

/-- The three-step lazy route preserves exactly the same complete answer bag,
including across both component boundaries. -/
theorem lazyRoute_preserves_meaning (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.toModel space subject)) :
    (kernelElaboration model).elaborate
        ((evaluationKernelEmbedding model).toFun (.request space subject)) =
      (kernelElaboration model).elaborate
        ((evaluationKernelEmbedding model).toFun
          (.answer space subject occurrence result)) :=
  route_preserves_meaning model
    (lazyRoute model space subject result occurrence copy)

@[simp] theorem directRoute_length (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.toModel space subject)) :
    (directRoute model space subject result occurrence copy).length = 1 :=
  rfl

@[simp] theorem lazyRoute_length (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.toModel space subject)) :
    (lazyRoute model space subject result occurrence copy).length = 3 :=
  rfl

/-- The comparison is non-vacuous: its two routes are not definitionally or
propositionally equal, since their retained lengths differ. -/
theorem directRoute_ne_lazyRoute (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.toModel space subject)) :
    directRoute model space subject result occurrence copy ≠
      lazyRoute model space subject result occurrence copy := by
  intro equal
  have lengths := congrArg Route.length equal
  simp at lengths

/-- The authored 2-generator says that direct interpretation and lazy
realization implement the same admitted occurrence.  The shared `copy`
evidence is load-bearing: unrelated routes receive no constructor. -/
inductive EvaluationCell (model : Model) :
    {source target : (kernelGSLT model).Term} →
      Route (CarriedStep model) source target →
      Route (CarriedStep model) source target → Type where
  | directLazy (space : model.Space) (subject result : Pattern)
      (occurrence : Nat)
      (copy : occurrence < Multiset.count result
        (MeTTaZero.evaluateOne model.toModel space subject)) :
      EvaluationCell model
        (directRoute model space subject result occurrence copy)
        (lazyRoute model space subject result occurrence copy)

/-- The generated 2-cell comparing the direct and lazy routes. -/
def directLazyTwoCell (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.toModel space subject)) :
    GeneratedTwoCell (EvaluationCell model)
      (directRoute model space subject result occurrence copy)
      (lazyRoute model space subject result occurrence copy) :=
  .generator (.directLazy space subject result occurrence copy)

/-- The direct/lazy comparison as a filled globular diamond.  Both branches
already reach the common answer, so their closing routes are identities. -/
def evaluationDiamond (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.toModel space subject)) :
    FilledDiamond (CarriedStep model)
      (GeneratedTwoCell (EvaluationCell model))
      ((evaluationKernelEmbedding model).toFun (.request space subject))
      ((evaluationKernelEmbedding model).toFun
        (.answer space subject occurrence result))
      ((evaluationKernelEmbedding model).toFun
        (.answer space subject occurrence result)) where
  leftBranch := directRoute model space subject result occurrence copy
  rightBranch := lazyRoute model space subject result occurrence copy
  join := (evaluationKernelEmbedding model).toFun
    (.answer space subject occurrence result)
  closeLeft := .refl _
  closeRight := .refl _
  filler := by
    simpa using directLazyTwoCell model space subject result occurrence copy

end Mettapedia.Languages.MeTTa.Prime.EvaluationCoherence
