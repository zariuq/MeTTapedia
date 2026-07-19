import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-!
# Explicit Set-Context Extension of the Rho Calculus

The paper-faithful rho calculus reduces by COMM, modulo structural
congruence and parallel-bag context.  This module records the optional
set-context extension as a separate least relation.  A `hashSet` is therefore
never executable merely because it is represented as a collection.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ExtendedReduction

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Rho reduction with the explicitly named set-context extension.

`core` embeds the pure calculus.  The remaining constructors are the least
closure needed to transport either a pure or an extended step through the
same EQUIV/PAR structure, plus the additional `ParSetCong` context. -/
inductive Reduces : Pattern → Pattern → Type where
  | core {p q : Pattern} : Reduction.Reduces p q → Reduces p q
  | equiv {p p' q q' : Pattern} :
      StructuralCongruence p p' →
      Reduces p' q' →
      StructuralCongruence q' q →
      Reduces p q
  | par {p q : Pattern} {rest : List Pattern} :
      Reduces p q →
      Reduces (.collection .hashBag (p :: rest) none)
              (.collection .hashBag (q :: rest) none)
  | parAny {p q : Pattern} {before after : List Pattern} :
      Reduces p q →
      Reduces (.collection .hashBag (before ++ [p] ++ after) none)
              (.collection .hashBag (before ++ [q] ++ after) none)
  | parSet {p q : Pattern} {rest : List Pattern} :
      Reduces p q →
      Reduces (.collection .hashSet (p :: rest) none)
              (.collection .hashSet (q :: rest) none)
  | parSetAny {p q : Pattern} {before after : List Pattern} :
      Reduces p q →
      Reduces (.collection .hashSet (before ++ [p] ++ after) none)
              (.collection .hashSet (before ++ [q] ++ after) none)

infix:50 " ⇝ˣ " => Reduces

/-- Every pure rho step is a step of the explicit set-context extension. -/
def Reduction.Reduces.toExtended {p q : Pattern} (step : p ⇝ q) : p ⇝ˣ q :=
  .core step

/-- The extension provides set-context descent for a concrete pure step. -/
def parSetOfCore {p q : Pattern} {rest : List Pattern} (step : p ⇝ q) :
    (.collection .hashSet (p :: rest) none) ⇝ˣ
      (.collection .hashSet (q :: rest) none) :=
  .parSet (.core step)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ExtendedReduction
