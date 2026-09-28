import Mettapedia.TypeTheory.MaterialSets.MembershipEvidence
import Mettapedia.TypeTheory.MaterialSets.DependentReplacement
import Mettapedia.TypeTheory.MaterialSets.DependentSum
import Mettapedia.TypeTheory.MaterialSets.Instances.ZFSet
import Mettapedia.TypeTheory.MaterialSets.Instances.SetCodedProofs
import Mettapedia.TypeTheory.MaterialSets.Instances.TwoWitness

/-!
# Material sets with membership evidence

The well-founded `set` profile: membership evidence, `El`, dependent
replacement `Image`, equality read as identity, and the comparison of the set of
dependent pairs with the dependent sum of member types. The generic interface
and its consequences under propositional membership; the `ZFSet` model; the
set-coded proof model with its identity type and `J`; and the two-witness model
in which every consequence fails.
-/
