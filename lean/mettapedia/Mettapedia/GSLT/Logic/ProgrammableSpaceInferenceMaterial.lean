import Mettapedia.GSLT.Core.ProgrammableSpaceInference
import Mettapedia.GSLT.Logic.ProgrammableSpaceReadings

/-!
# Persistent inference has a policy-independent material support

The actual predicate subtype of a faithfully coded carrier supplies the
collecting graph. No witness is selected from existence and no finite support
bound is imposed. A fair run's eventual graph is exactly the graph of finite
derivability. A finite prefix has that value precisely when it is rule-closed.
This theorem concerns support; receipts, work and convergence time are other
readings.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceInferenceMaterial

open Mettapedia.GSLT.Core.ProgrammableSpaceInference
open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u v
variable {Atom : Type u} (coding : ArgumentCoding Atom)

def graph (predicate : Atom → Prop) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.sup fun atom : {atom : Atom // predicate atom} => coding.graph atom.val

def value (predicate : Atom → Prop) : HSet.{u} := HSet.mk (graph coding predicate)

theorem member_value_iff (predicate : Atom → Prop) (reading : HSet.{u}) :
    reading ∈ value coding predicate ↔ ∃ atom, predicate atom ∧ coding.reading atom = reading := by
  change reading ∈ HSet.range (fun atom : {atom : Atom // predicate atom} => coding.graph atom.val) ↔ _
  rw [HSet.mem_range]
  exact ⟨fun ⟨atom, same⟩ => ⟨atom.val, atom.property, same⟩,
    fun ⟨atom, present, same⟩ => ⟨⟨atom, present⟩, same⟩⟩

theorem fact_member_iff (predicate : Atom → Prop) (atom : Atom) :
    coding.reading atom ∈ value coding predicate ↔ predicate atom := by
  rw [member_value_iff]
  constructor
  · rintro ⟨other, present, same⟩
    exact coding.injective same ▸ present
  · exact fun present => ⟨atom, present, rfl⟩

theorem value_eq_iff (first second : Atom → Prop) :
    value coding first = value coding second ↔ ∀ atom, first atom ↔ second atom := by
  constructor
  · intro same atom
    rw [← fact_member_iff coding first atom, ← fact_member_iff coding second atom, same]
  · intro same
    have predicates : first = second := funext fun atom => propext (same atom)
    exact congrArg (value coding) predicates

theorem list_support_comparison (atoms : List Atom) :
    value coding (fun atom => atom ∈ atoms) = ProgrammableSpaceReadings.support coding atoms := by
  apply HSet.ext
  intro reading
  rw [member_value_iff, ProgrammableSpaceReadings.member_support_iff]

variable {Instance : Type v} {theory : Theory Atom Instance}

def eventual (run : Run theory) : HSet.{u} := value coding run.support
def closure (theory : Theory Atom Instance) : HSet.{u} := value coding theory.closure
def prefixValue (run : Run theory) (tick : Nat) : HSet.{u} := value coding (run.facts tick)

theorem fair_eventual_exact (run : Run theory) (fair : run.RuleInstanceFair) :
    eventual coding run = closure coding theory :=
  congrArg (value coding) (run.support_eq_closure fair)

theorem fair_material_policies_agree (first second : Run theory)
    (firstFair : first.RuleInstanceFair) (secondFair : second.RuleInstanceFair) :
    eventual coding first = eventual coding second :=
  (fair_eventual_exact coding first firstFair).trans (fair_eventual_exact coding second secondFair).symm

theorem finite_prefix_exact_iff (run : Run theory) (tick : Nat) :
    prefixValue coding run tick = closure coding theory ↔ theory.Closed (run.facts tick) := by
  have predicates : (∀ atom, atom ∈ run.facts tick ↔ atom ∈ theory.closure) ↔
      run.facts tick = theory.closure := ⟨fun same => Set.ext same, fun same => same ▸ fun _ => Iff.rfl⟩
  exact (value_eq_iff coding (fun atom => atom ∈ run.facts tick)
    (fun atom => atom ∈ theory.closure)).trans
      (predicates.trans (run.finite_prefix_exact_iff_closed tick))

theorem eventual_membership (run : Run theory) (fair : run.RuleInstanceFair) (atom : Atom) :
    coding.reading atom ∈ eventual coding run ↔ theory.Derivable atom :=
  (fact_member_iff coding run.support atom).trans (run.eventually_iff_derivable fair atom)

end Mettapedia.GSLT.ProgrammableSpaceInferenceMaterial
