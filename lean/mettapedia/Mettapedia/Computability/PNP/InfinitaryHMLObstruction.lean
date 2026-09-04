import Mettapedia.GSLT.Logic.LogicalMetric
import Mettapedia.GSLT.Meredith.RhoMinimalContext

/-!
# Conditional infinitary HML obstruction and the rho candidate-context boundary

If a genuinely certified minimal-context type is infinite, then the
depth-bounded observable data domain need not be finite at all.  Abstractly,
this file proves that an infinite `MinimalContext S` makes `HMLFormula S` and
even its depth-`1` fragment infinite.

For rho, the syntactic evaluation-context grammar is infinite.  That is only a
family of *candidate* labels: it does not establish that infinitely many of
them satisfy the redex-relative-pushout least-enabler property.  The old
inference from "evaluation context" to "minimal context" has therefore been
removed.  A concrete rho HML obstruction requires an RPO construction first.

The separation matters: grammar cardinality cannot mint the universal property
required by the Meredith--Stay--Wells logic.
-/

namespace Mettapedia.Computability.PNP

open Mettapedia.GSLT
open Mettapedia.GSLT.HMLFormula
open Mettapedia.GSLT.Meredith.RhoExample
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context
open Mettapedia.OSLF.MeTTaIL.Syntax

section Abstract

variable {S : GSLT} [HasMinimalContexts S]

/-- Encode a minimal context as the corresponding depth-`1` diamond formula. -/
def depthOneFormulaOfContext (K : MinimalContext S) : HMLFormula S :=
  .diamond K .top

theorem depthOneFormulaOfContext_injective :
    Function.Injective (depthOneFormulaOfContext (S := S)) := by
  intro K L h
  cases h
  rfl

/-- The corresponding element of the depth-`1` fragment. -/
def depthOneFragmentOfContext (K : MinimalContext S) : DepthFragment (S := S) 1 :=
  ⟨depthOneFormulaOfContext (S := S) K, by
    simp [depthOneFormulaOfContext, modalDepth]⟩

theorem depthOneFragmentOfContext_injective :
    Function.Injective (depthOneFragmentOfContext (S := S)) := by
  intro K L h
  apply depthOneFormulaOfContext_injective (S := S)
  exact congrArg Subtype.val h

theorem infinite_hmlFormula_of_infinite_minimalContext
    [Infinite (MinimalContext S)] :
    Infinite (HMLFormula S) :=
  Infinite.of_injective (depthOneFormulaOfContext (S := S))
    (depthOneFormulaOfContext_injective (S := S))

theorem infinite_depthFragment_one_of_infinite_minimalContext
    [Infinite (MinimalContext S)] :
    Infinite (DepthFragment (S := S) 1) :=
  Infinite.of_injective (depthOneFragmentOfContext (S := S))
    (depthOneFragmentOfContext_injective (S := S))

theorem not_surjective_depthFragment_one_of_finite_code
    [Infinite (MinimalContext S)]
    {Code : Type*} [Fintype Code]
    (decode : Code → DepthFragment (S := S) 1) :
    ¬ Function.Surjective decode := by
  intro hsurj
  letI : Infinite (DepthFragment (S := S) 1) :=
    infinite_depthFragment_one_of_infinite_minimalContext (S := S)
  letI : Finite (DepthFragment (S := S) 1) := Finite.of_surjective decode hsurj
  exact not_finite (DepthFragment (S := S) 1)

theorem not_surjective_hmlFormula_of_finite_code
    [Infinite (MinimalContext S)]
    {Code : Type*} [Fintype Code]
    (decode : Code → HMLFormula S) :
    ¬ Function.Surjective decode := by
  intro hsurj
  letI : Infinite (HMLFormula S) :=
    infinite_hmlFormula_of_infinite_minimalContext (S := S)
  letI : Finite (HMLFormula S) := Finite.of_surjective decode hsurj
  exact not_finite (HMLFormula S)

end Abstract

section Rho

/-- A fixed environment probe used to build an infinite ladder of rho contexts. -/
def rhoEnvPattern : Pattern := .fvar "__rho_env__"

/-- A fixed hole probe used to read back the ladder depth from filled contexts. -/
def rhoProbePattern : Pattern := .fvar "__rho_probe__"

/-- Parallel-only ladder of rho evaluation contexts. -/
def rhoParLadder : Nat → EvalContext
  | 0 => .hole
  | n + 1 => .par rhoEnvPattern (rhoParLadder n)

/-- Count the left-nested rho environment frames in the probe image. -/
def rhoParDepth : Pattern → Nat
  | .collection .hashBag [q, rest] none =>
      if q = rhoEnvPattern then rhoParDepth rest + 1 else 0
  | _ => 0

theorem rhoParDepth_fill_rhoParLadder :
    ∀ n : Nat, rhoParDepth (fillEvalContext (rhoParLadder n) rhoProbePattern) = n
  | 0 => by
      rfl
  | n + 1 => by
      simp [rhoParLadder, fillEvalContext, rhoParDepth, rhoParDepth_fill_rhoParLadder]

theorem rhoParLadder_evalContext_injective :
    Function.Injective rhoParLadder := by
  intro m n h
  have hplug :
      fillEvalContext (rhoParLadder m) rhoProbePattern =
      fillEvalContext (rhoParLadder n) rhoProbePattern :=
    congrArg (fun K : EvalContext => fillEvalContext K rhoProbePattern) h
  have hdepth := congrArg rhoParDepth hplug
  simpa [rhoParDepth_fill_rhoParLadder] using hdepth

/-- Rho has infinitely many syntactically distinct evaluation contexts. -/
theorem infinite_rhoEvalContexts : Infinite EvalContext :=
  Infinite.of_injective rhoParLadder rhoParLadder_evalContext_injective

/-- The same ladder remains injective after forgetting the syntax down to its
extensional plug operation. -/
theorem rhoParLadder_contextShape_injective :
    Function.Injective (fun n : Nat => ofEvalContext (rhoParLadder n)) := by
  intro m n h
  have hplug :
      (ofEvalContext (rhoParLadder m)).plug rhoProbePattern =
      (ofEvalContext (rhoParLadder n)).plug rhoProbePattern :=
    congrArg (fun K : GSLTContext rhoGSLT => K.plug rhoProbePattern) h
  have hdepth := congrArg rhoParDepth hplug
  simpa [ofEvalContext, rhoParDepth_fill_rhoParLadder] using hdepth

/-- Thus even the candidate plug operations are infinite.  No conclusion about
least-enabling contexts follows without an RPO/minimality proof. -/
theorem infinite_rhoEvaluationContextShapes : Infinite (GSLTContext rhoGSLT) :=
  Infinite.of_injective (fun n : Nat => ofEvalContext (rhoParLadder n))
    rhoParLadder_contextShape_injective

#print axioms rhoParLadder_evalContext_injective
#print axioms infinite_rhoEvalContexts
#print axioms rhoParLadder_contextShape_injective
#print axioms infinite_rhoEvaluationContextShapes

end Rho

end Mettapedia.Computability.PNP
