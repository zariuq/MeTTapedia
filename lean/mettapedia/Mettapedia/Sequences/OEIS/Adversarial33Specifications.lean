import Mettapedia.Sequences.OEIS.AdversarialElementary
import Mettapedia.Sequences.OEIS.AdversarialStructural
import Mettapedia.Sequences.OEIS.PredicateDefined

/-!
# Candidate-blind specifications for the adversarial 33-entry cohort

This registry fixes the mathematical specifications selected from the
weakest-evidence discoveries before their synthesized candidates are exposed.
It combines predicate-defined, elementary, and structural entries without
asserting that any candidate realizes them.
-/

namespace Mettapedia.Sequences.OEIS.Adversarial33Specifications

open Mettapedia.Sequences.OEIS.Elementary49

noncomputable def registry : List (String × SequenceSpec) :=
  Mettapedia.Sequences.OEIS.PredicateDefined.registry ++
    Mettapedia.Sequences.OEIS.AdversarialElementary.registry ++
    Mettapedia.Sequences.OEIS.AdversarialStructural.registry

theorem registry_length : registry.length = 33 := by rfl

theorem registry_names_nodup : (registry.map Prod.fst).Nodup := by
  simp [registry, Mettapedia.Sequences.OEIS.PredicateDefined.registry,
    Mettapedia.Sequences.OEIS.AdversarialElementary.registry,
    Mettapedia.Sequences.OEIS.AdversarialStructural.registry]

theorem registry_contains_A260981 :
    ("A260981", Mettapedia.Sequences.OEIS.PredicateDefined.A260981.spec) ∈ registry := by
  simp [registry, Mettapedia.Sequences.OEIS.PredicateDefined.registry]

theorem registry_contains_A265286 :
    ("A265286", Mettapedia.Sequences.OEIS.AdversarialStructural.A265286.spec) ∈ registry := by
  simp [registry, Mettapedia.Sequences.OEIS.AdversarialStructural.registry]

#print axioms registry_length
#print axioms registry_names_nodup
#print axioms registry_contains_A260981
#print axioms registry_contains_A265286

end Mettapedia.Sequences.OEIS.Adversarial33Specifications
