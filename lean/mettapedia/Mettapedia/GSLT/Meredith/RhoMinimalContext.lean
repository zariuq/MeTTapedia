import Mettapedia.GSLT.Meredith.RhoExample
import Mettapedia.GSLT.Logic.MinimalContext
import Mettapedia.GSLT.Logic.ContextHML
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-!
# Concrete Minimal Contexts for the ρ-Calculus

This file instantiates the abstract `HasMinimalContexts` interface for the
concrete rho-calculus GSLT from `RhoExample.lean`.

The key choice is simple and explicit:

* the certified one-hole/reactive/minimal contexts are exactly the evaluation
  contexts already formalized in `RhoCalculus/Context.lean`,
* plugging is `fillEvalContext`,
* GSLT context steps coincide with rho labeled transitions.

This gives the first concrete bridge from the abstract HML layer back to an
actual process calculus. It is intentionally modest: we certify the current
rho context grammar, not the full universal minimality theorem of the
Milner-Sewell-Leifer construction.
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

/-- The rho-calculus context grammar supplies the concrete minimal-context
interface for `rhoGSLT`. -/
instance : HasMinimalContexts rhoGSLT where
  IsOneHole := IsEvalGenerated
  IsReactive := IsEvalGenerated
  IsMinimal := IsEvalGenerated
  id_oneHole := ⟨EvalContext.hole, fun p => by simp [GSLTContext.id, fillEvalContext]⟩
  id_reactive := ⟨EvalContext.hole, fun p => by simp [GSLTContext.id, fillEvalContext]⟩
  id_minimal := ⟨EvalContext.hole, fun p => by simp [GSLTContext.id, fillEvalContext]⟩
  minimal_reactive := id
  minimal_oneHole := id

/-- The concrete minimal context packaged from a rho evaluation context. -/
def minimalOfEvalContext (K : EvalContext) : MinimalContext rhoGSLT :=
  ⟨ofEvalContext K, isEvalGenerated_ofEvalContext K⟩

@[simp] theorem minimalOfEvalContext_plug (K : EvalContext) (p : Pattern) :
    (minimalOfEvalContext K).plug p = fillEvalContext K p := rfl

/-- On rho-generated contexts, GSLT context steps are exactly filled rho
reductions. -/
theorem contextStep_iff_reduces (K : EvalContext) (p q : Pattern) :
    GSLT.contextStep rhoGSLT p (minimalOfEvalContext K) q ↔ Nonempty (Reduces (fillEvalContext K p) q) := by
  rfl

/-- Every rho labeled transition yields a GSLT context step through the concrete
minimal-context instance. -/
theorem contextStep_of_labeledTransition {K : EvalContext} {p q : Pattern}
    (h : Nonempty (p ⇝[K] q)) :
    GSLT.contextStep rhoGSLT p (minimalOfEvalContext K) q :=
  labeled_implies_reduces h

/-- Every rho GSLT context step gives a rho labeled transition, via the generic
`from_reduction` constructor. -/
theorem labeledTransition_of_contextStep {K : EvalContext} {p q : Pattern}
    (h : GSLT.contextStep rhoGSLT p (minimalOfEvalContext K) q) :
    Nonempty (p ⇝[K] q) :=
  ⟨LabeledTransition.from_reduction h⟩

/-- Hence the concrete rho minimal-context steps are equivalent to rho labeled
transitions. -/
theorem contextStep_iff_labeledTransition {K : EvalContext} {p q : Pattern} :
    GSLT.contextStep rhoGSLT p (minimalOfEvalContext K) q ↔ Nonempty (p ⇝[K] q) := by
  constructor
  · exact labeledTransition_of_contextStep
  · exact contextStep_of_labeledTransition

/-- The COMM interaction appears as a concrete GSLT context step for an input
process placed in its matching output context. -/
theorem comm_input_contextStep (x q p : Pattern) :
    GSLT.contextStep rhoGSLT
      (.apply "PInput" [x, .lambda none p])
      (minimalOfEvalContext (.par (.apply "POutput" [x, q]) .hole))
      (commSubst p q) := by
  exact contextStep_of_labeledTransition ⟨LabeledTransition.comm_input⟩

/-- Dually, the output process steps in the matching input context. -/
theorem comm_output_contextStep (x q p : Pattern) :
    GSLT.contextStep rhoGSLT
      (.apply "POutput" [x, q])
      (minimalOfEvalContext (.par (.apply "PInput" [x, .lambda none p]) .hole))
      (commSubst p q) := by
  exact contextStep_of_labeledTransition ⟨LabeledTransition.comm_output⟩

/-- The rho input process satisfies the corresponding HML diamond formula for a
matching output environment. -/
theorem comm_input_satisfies_diamond (x q p : Pattern) :
    HMLFormula.satisfies rhoGSLT
      (.apply "PInput" [x, .lambda none p])
      (.diamond (minimalOfEvalContext (.par (.apply "POutput" [x, q]) .hole)) .top) := by
  refine ⟨commSubst p q, comm_input_contextStep x q p, ?_⟩
  simp [HMLFormula.satisfies]

/-- Dually, the rho output process satisfies the corresponding HML diamond
formula for a matching input environment. -/
theorem comm_output_satisfies_diamond (x q p : Pattern) :
    HMLFormula.satisfies rhoGSLT
      (.apply "POutput" [x, q])
      (.diamond (minimalOfEvalContext (.par (.apply "PInput" [x, .lambda none p]) .hole)) .top) := by
  refine ⟨commSubst p q, comm_output_contextStep x q p, ?_⟩
  simp [HMLFormula.satisfies]

end Mettapedia.GSLT.Meredith.RhoExample
