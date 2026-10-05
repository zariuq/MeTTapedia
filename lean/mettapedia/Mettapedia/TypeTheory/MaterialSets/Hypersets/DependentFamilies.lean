import Mettapedia.TypeTheory.DependentFamilySectionDescent
import Mettapedia.TypeTheory.MaterialSets.DependentProduct
import Mettapedia.TypeTheory.MaterialSets.Hypersets.DependentProduct
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ProductsFromSmallSections
import Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyDescent
import Mettapedia.TypeTheory.MaterialSets.Hypersets.SmallMembers
import Mettapedia.TypeTheory.MaterialSets.Hypersets.WellFoundedFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyCwf
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresheafFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresheafProducts
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CodedFamilies

/-!
# Hypersets and dependent families

This collection relates graph presentations, material membership, and
contextual dependent families through proved comparisons of actual values.

* `DependentFamilySectionDescent` characterizes which terms of a descending
  family descend, and identifies the observed total space with its kernel
  quotient. `FamilyDescent` specializes this to pictured graph members.
* `DependentProduct` constructs material dependent function graphs and proves
  their equivalence with dependent sections. `ProductsFromSmallSections`
  constructs the same graph set from a supplied small carrier of sections,
  separating this route from powerset-based product existence. `FamilyCwf` uses material sets
  for contexts and comprehension, with sums, products, and substitution laws.
* `WellFoundedFamilies` preserves member values and the material sum and
  product constructions through the well-founded part and its `ZFSet` model.
* `PresheafFamilies` supplies the existing displayed-family machinery with
  actual hyperset members. `PresheafProducts` compares compatible contextual
  sections with its right-Kan product, including evaluation. The discrete
  comparison and a growing-domain counterexample delimit when a material
  product in one context suffices.
* `SmallMembers` gives small carriers for fixed member types under supplied
  recovery data, while proving that the whole hyperset carrier cannot be
  small at that level. `CodedFamilies` uses next-level codes and an explicit
  closed-universe bound to decode non-well-founded families and their material
  sums and products.

Presentation and recovery data remain explicit. The classical next-level
coding model and the host's selected categorical constructions retain their
classical dependencies. Model equality here is ordinary extensional equality;
no native higher identity rules or set-theory axiom package are selected.
-/
