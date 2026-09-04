import Mettapedia.GSLT.Meredith.RhoExample
import Mettapedia.GSLT.Logic.MinimalContext
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-!
# Rho evaluation contexts are candidate labels, not proved minimal contexts

The rho syntax supplies a useful grammar of one-hole evaluation contexts and a
labeled transition relation.  It does **not** by itself prove that those
contexts are least enablers in the Milner--Sewell--Leifer sense.  Least
enabling contexts require the factorization universal property formalized by
`MinimalEnablingContext.ContextualRules.IsLeastEnabler`, normally obtained
from a redex-relative pushout construction.

This module therefore records only the facts the syntax actually establishes:

* plugging is `fillEvalContext`,
* a labeled transition is exactly a reduction after plugging, and
* the two communication partners give concrete positive examples.

No `HasMinimalContexts rhoGSLT` instance is manufactured here.  Consequently
these candidates cannot silently enter a context-HML adequacy theorem as if
the missing universal property had been proved.
-/

namespace Mettapedia.GSLT.Meredith.RhoExample

open Mettapedia.GSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The raw GSLT context shape induced by a rho evaluation context. -/
def ofEvalContext (K : EvalContext) : GSLTContext rhoGSLT where
  plug := fillEvalContext K

/-- A raw GSLT context is rho-generated when it is extensionally induced by an
evaluation context from the rho syntax. -/
def IsEvalGenerated (K : GSLTContext rhoGSLT) : Prop :=
  ∃ Kρ : EvalContext, ∀ p : Pattern, K.plug p = fillEvalContext Kρ p

theorem isEvalGenerated_ofEvalContext (K : EvalContext) :
    IsEvalGenerated (ofEvalContext K) :=
  ⟨K, fun _ => rfl⟩

/-- Candidate-context action: plug the source into an evaluation context and
take one equation-respecting rho step.  This is a valid labeled transition
family, but it carries no least-enabler claim. -/
def evalContextStep (K : EvalContext) (p q : Pattern) : Prop :=
  rhoGSLT.Step (fillEvalContext K p) q

theorem evalContextStep_iff_reduces (K : EvalContext) (p q : Pattern) :
    evalContextStep K p q ↔ Nonempty (Reduces (fillEvalContext K p) q) :=
  Iff.rfl

/-- Every rho labeled transition yields the corresponding candidate-context
step. -/
theorem evalContextStep_of_labeledTransition {K : EvalContext} {p q : Pattern}
    (h : Nonempty (p ⇝[K] q)) :
    evalContextStep K p q :=
  labeled_implies_reduces h

/-- Every candidate-context step gives a rho labeled transition through the
generic `from_reduction` constructor. -/
theorem labeledTransition_of_evalContextStep {K : EvalContext} {p q : Pattern}
    (h : evalContextStep K p q) :
    Nonempty (p ⇝[K] q) :=
  ⟨LabeledTransition.from_reduction h⟩

/-- The syntax-level labeled transition and candidate-context action coincide.
This theorem deliberately says nothing about minimality. -/
theorem evalContextStep_iff_labeledTransition {K : EvalContext} {p q : Pattern} :
    evalContextStep K p q ↔ Nonempty (p ⇝[K] q) := by
  constructor
  · exact labeledTransition_of_evalContextStep
  · exact evalContextStep_of_labeledTransition

/-- The COMM interaction appears under the matching output candidate. -/
theorem comm_input_evalContextStep (x q p : Pattern) :
    evalContextStep
      (.par (.apply "POutput" [x, q]) .hole)
      (.apply "PInput" [x, .lambda none p])
      (semanticCommSubst p q) := by
  exact evalContextStep_of_labeledTransition ⟨LabeledTransition.comm_input⟩

/-- Dually, the output process steps under the matching input candidate. -/
theorem comm_output_evalContextStep (x q p : Pattern) :
    evalContextStep
      (.par (.apply "PInput" [x, .lambda none p]) .hole)
      (.apply "POutput" [x, q])
      (semanticCommSubst p q) := by
  exact evalContextStep_of_labeledTransition ⟨LabeledTransition.comm_output⟩

#print axioms evalContextStep_iff_labeledTransition
#print axioms comm_input_evalContextStep
#print axioms comm_output_evalContextStep

end Mettapedia.GSLT.Meredith.RhoExample
