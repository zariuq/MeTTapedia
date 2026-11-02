import Mettapedia.Logic.RandomClosure
import Mettapedia.Logic.FiniteImplicationPresentation

/-! The random-closure response interface has a finite operational
presentation exactly when its deterministic response satisfies the closure
laws. The response is not itself taken as the derivation relation. -/

set_option autoImplicit false

namespace Mettapedia.Logic.RandomClosure

open FiniteHornClosureCharacterization

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem closure_has_finite_rule_table (response : ClosureOperator (Set A)) :
    ∃ table : Finset (Finset A × A), ∀ seed atom,
      atom ∈ response seed ↔ FinitaryClosure.close (tableRules table) (· ∈ seed) atom := by
  apply (finite_table_characterization response).mp
  exact ⟨response.le_closure, response.monotone, response.idempotent⟩

theorem component_has_finite_rule_table (component : Component A) :
    ∃ table : Finset (Finset A × A), ∀ seed atom,
      atom ∈ component.closure seed ↔ FinitaryClosure.close (tableRules table) (· ∈ seed) atom :=
  closure_has_finite_rule_table component.closure

end Mettapedia.Logic.RandomClosure
