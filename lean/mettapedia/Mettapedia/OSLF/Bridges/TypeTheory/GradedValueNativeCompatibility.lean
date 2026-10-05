import Mettapedia.OSLF.Bridges.TypeTheory.GradedValueNativeDescent

/-!
# Legacy bundled native-satisfaction endpoint

The direct formula and native-predicate comparisons in
`GradedValueNativeDescent` do not use choice. The endpoint below states the
same result through the existing bundled `gsltOSLF` satisfaction interface.
Its type inherits the classical dependency of that interface's categorical
frame construction; the underlying formula comparison remains constructive.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Bridges.TypeTheory.GradedValueNativeDescent

open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Distinction.Constructive Mettapedia.GSLT.GradedValueObserver
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes

universe uS uAtom uLabel uObs uV

variable {V : Type uV} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]
variable {S : GSLT.{uS}} {K : Scale V}
variable (Q : PresentedSystem.{uS, uAtom, uLabel, uObs} S K)
variable (vocabulary : Q.Vocabulary) (stage : Nat)
variable (positive : K.Positive) (stable : Q.Stabilizes vocabulary stage)

include vocabulary positive stable in
theorem native_satisfaction_stage_iff
    (formula : Formula (valueSystem Q).Atom Q.dynamics.Label) (source : S.Term) :
    (gsltOSLF (stageTheory Q stage)).satisfies (S := ()) (stateOf Q stage source)
        (formulaNativeType (stageSystem Q stage) formula).pred ↔
      (gsltOSLF S).satisfies (S := ()) source
        (formulaNativeType (valueSystem Q) formula).pred :=
  formula_stage_iff Q vocabulary stage positive stable formula source

end Mettapedia.OSLF.Bridges.TypeTheory.GradedValueNativeDescent
