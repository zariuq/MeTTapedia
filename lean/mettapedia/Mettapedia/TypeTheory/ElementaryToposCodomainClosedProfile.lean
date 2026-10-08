import Mettapedia.CategoryTheory.ElementaryTopos
import Mettapedia.CategoryTheory.ElementaryToposObjectUniverseLift
import Mettapedia.CategoryTheory.ElementaryToposDependentProducts
import Mettapedia.CategoryTheory.SliceClassifier
import Mettapedia.TypeTheory.CodomainFibrationComprehensionProfile

/-!
# Closed codomain comprehension of an arbitrary elementary topos

The dependent products and adjunctions are constructed from finite limits,
base exponentials and the supplied classifier. They instantiate the actual
codomain fibration, whose full comprehension, Cartesian lifts and strong
sums use the same chosen slice pullbacks. Each actual slice is equipped
with its earned elementary-topos structure.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.TypeTheory.ElementaryToposCodomainClosedProfile

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory
open Mettapedia.CategoryTheory.FibrationTwoCategory
namespace Size
abbrev raised := ElementaryToposObjectUniverseLift.raised
end Size

universe u v
variable (topos : ElementaryTopos.{u,v})

def closedComprehension : CodomainClosedComprehension topos where
  dependentProduct := ElementaryToposDependentProducts.dependentProduct topos.classifier
  dependentAdjunction := ElementaryToposDependentProducts.pullbackAdjunction topos.classifier

/-- The complete profile uses the explicitly equivalent object-raised
base. Its hom universe remains the original one. -/
def profile :
    @FibrationComprehensionProfile.Closed.{max u v,v,max u v,v}
      (codomain (Size.raised topos)) CodomainComprehension.sliceFibres :=
  CodomainFibrationComprehensionProfile.closed (closedComprehension (Size.raised topos))

local instance fibres : HasFibers.{v,max u v} (codomain (Size.raised topos)).functor :=
  CodomainComprehension.sliceFibres

attribute [local instance] Over.cartesianMonoidalCategory

def sliceTopos (base : topos) : ElementaryTopos.{max u v,v} :=
  letI : MonoidalClosed (Over base) :=
    ElementaryToposSliceExponentials.monoidalClosed topos.classifier base
  ElementaryTopos.ofCategory (Over base) (SliceClassifier.overClassifier topos.classifier base)

theorem original_abstraction {source target : topos} (route : source ⟶ target)
    {argument : Over target} {result : Over source}
    (body : (Over.pullback route).obj argument ⟶ result) :
    (closedComprehension topos).abstraction route body =
      ElementaryToposDependentProducts.dependentCurry topos.classifier route body := rfl

theorem original_evaluation {source target : topos} (route : source ⟶ target)
    (result : Over source) :
    (closedComprehension topos).evaluation route result =
      (ElementaryToposDependentProducts.pullbackAdjunction topos.classifier route).counit.app result :=
  rfl

theorem profile_abstraction {source target : Size.raised topos} (route : source ⟶ target)
    {argument : Over target} {result : Over source}
    (body : (Over.pullback route).obj argument ⟶ result) :
    (profile topos).abstraction route body =
      ElementaryToposDependentProducts.dependentCurry (Size.raised topos).classifier route body := rfl

theorem profile_evaluation {source target : Size.raised topos} (route : source ⟶ target)
    (result : Over source) :
    (profile topos).evaluation route result =
      (ElementaryToposDependentProducts.pullbackAdjunction (Size.raised topos).classifier route).counit.app result :=
  rfl

theorem strong_sum_retains_complete_domain {source target : Size.raised topos}
    (route : source ⟶ target) (result : Over source) :
    ((profile topos).strongSumComparison route result).hom = 𝟙 result.left :=
  CodomainFibrationComprehensionProfile.strongSum_domain
    (closedComprehension (Size.raised topos)) route result

/-- Complete application of the independently constructed profile returns
the supplied body, including its actual dependent slice value. -/
theorem profile_beta {source target : Size.raised topos} (route : source ⟶ target)
    {argument : Over target} {result : Over source}
    (body : (Over.pullback route).obj argument ⟶ result) :
    (Over.pullback route).map ((profile topos).abstraction route body) ≫
      (profile topos).evaluation route result = body :=
  (profile topos).beta route body

end Mettapedia.TypeTheory.ElementaryToposCodomainClosedProfile
