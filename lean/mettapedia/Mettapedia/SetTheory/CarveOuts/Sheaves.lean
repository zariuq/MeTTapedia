import Mettapedia.SetTheory.CarveOuts.Sheaves.LocalIsos
import Mettapedia.SetTheory.CarveOuts.Sheaves.Families
import Mettapedia.SetTheory.CarveOuts.Sheaves.Forcing
import Mettapedia.SetTheory.CarveOuts.Sheaves.SmallMaps
import Mettapedia.SetTheory.CarveOuts.Sheaves.FamilySmallMaps
import Mettapedia.SetTheory.CarveOuts.Sheaves.Collection
import Mettapedia.SetTheory.CarveOuts.Sheaves.Cantor

/-!
# Families over the contexts, valued in sheaves on a space

* `LocalIsos`: forcing on the product site is invariant under locally injective and locally
  surjective maps of value families, for every formula.
* `Families`: families `D ⥤ Sheaf (Opens X)`, the passage from value families on the product site
  by sheafification pointwise in the contexts, and the unit, which commutes with context arrows
  and is locally injective and locally surjective.
* `Forcing`: sheaf models, Kripke–Joyal sheaf forcing, closed extensions, and the agreement of
  forcing on a presheaf model with sheaf forcing on its sheafification.
* `SmallMaps`: pointwise small maps of sheaves with epimorphisms the local surjections; (S1)–(S5)
  and (M).
* `FamilySmallMaps`: the same for families over the contexts.
* `Collection`: collection for sheaves from collection in the base, and the base from host
  choice.
* `Cantor`: the test case — covers needed for agreement, non-classical logic, small maps.
-/
