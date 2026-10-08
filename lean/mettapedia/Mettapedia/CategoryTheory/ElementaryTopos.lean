import Mettapedia.CategoryTheory.ElementaryToposImages
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Supplied elementary topoi

The object bundle contains finite limits, cartesian closed structure, and
an actual subobject classifier. Images and strong epimorphisms are derived
from these data. No completeness, cocompleteness, or extra logical fibration
is included in the definition.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

set_option linter.checkUnivs false in
structure ElementaryTopos where
  Carrier : Type u
  category : Category.{v} Carrier
  finite : HasFiniteLimits Carrier
  cartesian : CartesianMonoidalCategory Carrier
  closed : MonoidalClosed Carrier
  classifier : Subobject.Classifier Carrier

namespace ElementaryTopos

attribute [instance] category finite cartesian closed

instance : CoeSort ElementaryTopos.{u, v} (Type u) := ⟨Carrier⟩

def ofCategory (C : Type u) [Category.{v} C] [HasFiniteLimits C]
    [CartesianMonoidalCategory C] [MonoidalClosed C]
    (classifier : Subobject.Classifier C) : ElementaryTopos.{u, v} where
  Carrier := C
  category := inferInstance
  finite := inferInstance
  cartesian := inferInstance
  closed := inferInstance
  classifier := classifier

instance hasImages (topos : ElementaryTopos.{u, v}) : HasImages topos :=
  ElementaryToposImages.hasImages topos.classifier

instance strongEpiCategory (topos : ElementaryTopos.{u, v}) : StrongEpiCategory topos :=
  ElementaryToposImages.strongEpiCategory topos.classifier

instance hasImageMaps (topos : ElementaryTopos.{u, v}) : HasImageMaps topos := inferInstance

/-- The supplied classifier also gives the ordinary classifier existence class. -/
instance hasSubobjectClassifier (topos : ElementaryTopos.{u, v}) :
    HasSubobjectClassifier topos := ⟨⟨topos.classifier⟩⟩

end ElementaryTopos
end Mettapedia.CategoryTheory
