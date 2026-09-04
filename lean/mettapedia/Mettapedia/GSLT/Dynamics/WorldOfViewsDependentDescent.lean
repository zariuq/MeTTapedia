import Mettapedia.GSLT.Dynamics.WorldOfViews
import Mettapedia.TypeTheory.JointObservationDependentDescent

/-!
# Dependent families over a jointly faithful world of views

A modular view carries several local observers.  Its defining faithfulness
law says that those observers jointly separate global states, even when no
individual module does.  The general joint-observation theorem therefore
transports every dependent family on global states to the compatible family
of local views.

This bridge does not assert that arbitrary tuples of local states are
globally compatible, manufacture functional translations between different
views, or choose one local module as foundational.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.WorldOfViewsDependentDescent

open Mettapedia.GSLT.WorldOfViews
open Mettapedia.TypeTheory.JointObservationDependentDescent
open Mettapedia.TypeTheory.UniversalDependentFamilyDescent

universe uState uFibre

/-- The local observers of a modular world-of-views object, regarded as an
indexed observation family. -/
def modularObservationFamily {State : Type uState}
    (view : ModularView State) :
    ObservationFamily.{uState, uState, uState} State where
  Index := view.Module
  Target := view.LocalState
  observe module := (view.observer module).observe

/-- The defining joint-faithfulness law of a modular view is exactly joint
separation of its observation family. -/
theorem modularObservationFamily_jointlySeparating
    {State : Type uState} (view : ModularView State) :
    (modularObservationFamily view).JointlySeparating :=
  view.jointlyFaithful

/-- Every dependent family on a modular state descends to the compatible
joint local view.  No individual module is claimed faithful. -/
theorem modularView_allFamiliesDescend
    {State : Type uState} (view : ModularView State) :
    AllFamiliesDescend.{uState, uState, uFibre}
      (modularObservationFamily view).compatibleReadout := by
  exact
    (ObservationFamily.allFamiliesDescend_iff_jointlySeparating
      (modularObservationFamily view)).2
        (modularObservationFamily_jointlySeparating view)

/-! ## Concrete plural-view control -/

/-- The existing response view has two individually partial coordinate
modules whose joint observation carries every dependent response family. -/
theorem responseModules_allFamiliesDescend :
    AllFamiliesDescend.{0, 0, uFibre}
      (modularObservationFamily
        Mettapedia.GSLT.WorldOfViews.Canary.responseModules).compatibleReadout :=
  modularView_allFamiliesDescend
    Mettapedia.GSLT.WorldOfViews.Canary.responseModules

#print axioms modularObservationFamily_jointlySeparating
#print axioms modularView_allFamiliesDescend
#print axioms responseModules_allFamiliesDescend

end Mettapedia.GSLT.WorldOfViewsDependentDescent
