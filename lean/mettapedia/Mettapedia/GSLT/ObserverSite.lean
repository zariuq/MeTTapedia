import Mettapedia.GSLT.Logic.ObserverPresheaf
import Mettapedia.GSLT.Logic.ObserverPresheafControls
import Mettapedia.GSLT.Logic.ObserverPresheafLimits
import Mettapedia.OSLF.Framework.ObserverNativeTypes

/-!
# The observer site

* `ObserverPresheaf`: admissible classes of contexts as a thin category, and the
  observer presheaf sending a class to the behavioural classes of its saturated
  system, with forgetting as restriction; its factorisation through the category
  of observers; stage predicates with existential and universal image adjoint to
  reindexing, Frobenius reciprocity, the Galois insertion and coinsertion given by
  surjective forgetting; Beck–Chevalley along forgetting characterised as
  amalgamation, and injectivity into the pullback as separation; restriction
  along chains and sub-sites; stage predicates as the observable predicates of the
  theory–model framework.
* `ObserverPresheafControls`: an oracle tower whose every restriction forgets;
  determination as a non-functorial assignment while the stages stay functorial;
  three squares of inert observers where amalgamation fails, where separation
  fails, and where both hold.
* `ObserverPresheafLimits`: the supremum of a directed family of classes admits
  exactly the contexts of its members; under image-finiteness its relative
  equivalence is the intersection of the family's, so the limit stage is
  determined by the finite stages; the oracle tower is continuous at its limit,
  and a branching tower with infinitely many reducts is not.
* `ObserverNativeTypes`: the GSLT seen by an observer class and its generated OSLF;
  its native predicates are the stage predicates, OSLF change of base along
  forgetting is the hyperdoctrine of the observer presheaf, the step-future is
  natural along forgetting and the step-past only lax; subfunctors of the observer
  presheaf are the forgetting-closed families; carving to a sub-site is
  restriction with both adjoint extensions; the Williams–Stay adjoints and
  Beck–Chevalley condition over the observer site.

The identity carve (`Logic.TheoryModel.IdentityCarve`) belongs to the theory–model
modules and is imported from their aggregate.
-/
