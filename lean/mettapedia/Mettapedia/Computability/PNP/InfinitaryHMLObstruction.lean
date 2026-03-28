import Mettapedia.GSLT.Logic.LogicalMetric
import Mettapedia.GSLT.Meredith.RhoMinimalContext

/-!
# P vs NP crux: the current Meredith observable surface is already infinitary

The current HML layer quantifies over all certified minimal contexts.  Without a
separate finiteness theorem on that context type, the depth-bounded observable
surface need not be finite at all.  In fact:

* abstractly, if `MinimalContext S` is infinite, then `HMLFormula S` and even the
  depth-`1` fragment are infinite;
* concretely, the rho-calculus minimal-context instance already has infinitely
  many certified contexts, so its depth-`1` HML fragment is infinite.

This does not refute a repaired Meredith route.  It does show that the current
semantic layer is not yet close to the finite encoded-family interface required
by the switching/ERM route.
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

theorem rhoParLadder_minimalContext_injective :
    Function.Injective (fun n : Nat => minimalOfEvalContext (rhoParLadder n)) := by
  intro m n h
  have hplug :
      (minimalOfEvalContext (rhoParLadder m)).plug rhoProbePattern =
      (minimalOfEvalContext (rhoParLadder n)).plug rhoProbePattern :=
    congrArg (fun K : MinimalContext rhoGSLT => K.plug rhoProbePattern) h
  have hdepth := congrArg rhoParDepth hplug
  simpa [rhoParDepth_fill_rhoParLadder] using hdepth

theorem infinite_rhoMinimalContexts : Infinite (MinimalContext rhoGSLT) :=
  Infinite.of_injective (fun n : Nat => minimalOfEvalContext (rhoParLadder n))
    rhoParLadder_minimalContext_injective

theorem infinite_rhoHMLFormula : Infinite (HMLFormula rhoGSLT) := by
  letI := infinite_rhoMinimalContexts
  exact infinite_hmlFormula_of_infinite_minimalContext (S := rhoGSLT)

theorem infinite_rhoDepthFragment_one : Infinite (DepthFragment (S := rhoGSLT) 1) := by
  letI := infinite_rhoMinimalContexts
  exact infinite_depthFragment_one_of_infinite_minimalContext (S := rhoGSLT)

theorem not_surjective_rhoDepthFragment_one_of_finite_code
    {Code : Type*} [Fintype Code]
    (decode : Code → DepthFragment (S := rhoGSLT) 1) :
    ¬ Function.Surjective decode := by
  letI := infinite_rhoMinimalContexts
  exact not_surjective_depthFragment_one_of_finite_code (S := rhoGSLT) decode

theorem not_surjective_rhoHMLFormula_of_finite_code
    {Code : Type*} [Fintype Code]
    (decode : Code → HMLFormula rhoGSLT) :
    ¬ Function.Surjective decode := by
  letI := infinite_rhoMinimalContexts
  exact not_surjective_hmlFormula_of_finite_code (S := rhoGSLT) decode

end Rho

end Mettapedia.Computability.PNP
