import Mettapedia.GSLT.Contracts.ScopedTheoryImports
import Mettapedia.Logic.LP.FiniteDependencyClosure

/-!
# Protecting transitive definition imports

A declared use is an edge from a resolved binding to another slot it
can consult. A protection check follows the *pinned* manifest and
checks the full reply of every reached slot, including missing slots.
If it passes, the incoming manifest has exactly the same reachable
closure. Unrelated child declarations need not agree.

The manifest must be sound for the operations allowed by the module.
Untyped reflective code cannot certify its own complete dependency
list merely by advertising one. Module programs over a restricted
slot interface enforce the restriction for every branch.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.SealedDefinitionGraph

open Mettapedia.GSLT.Contracts.ScopedTheoryImports (Environment Protects compatible compatible_iff)
open Mettapedia.Logic.LP.FiniteDependencyClosure (closure least closed roots_subset)

universe u v
variable {Name : Type u} {Payload : Type v}

structure Export (Name : Type u) (Payload : Type v) where
  meaning : Payload
  dependencies : Finset Name
  deriving DecidableEq

abbrev Catalog (Name : Type u) (Payload : Type v) := Environment Name (Export Name Payload)

def requires (catalog : Catalog Name Payload) (name : Name) : Finset Name :=
  (catalog name).elim ∅ Export.dependencies

variable [DecidableEq Name] [Fintype Name]

def footprint (catalog : Catalog Name Payload) (roots : Finset Name) : Finset Name :=
  closure (requires catalog) roots

theorem protected_closure {pinned incoming : Catalog Name Payload} (roots : Finset Name)
    (same : Protects (footprint pinned roots) pinned incoming) :
    footprint incoming roots = footprint pinned roots := by
  have forward : footprint incoming roots ⊆ footprint pinned roots := by
    apply least
    · exact roots_subset _ _
    · intro name reachable
      have localBinding := same name reachable
      rw [requires, localBinding]
      exact closed (requires pinned) roots reachable
  refine Finset.Subset.antisymm forward ?_
  apply least
  · exact roots_subset _ _
  · intro name reachable
    have localBinding := same name (forward reachable)
    rw [requires, ← localBinding]
    exact closed (requires incoming) roots reachable

/-- The full-reply check, not just equality of the root definition,
licenses re-use of a sealed module with a known dependency manifest. -/
theorem protected_import [DecidableEq Payload] {pinned incoming : Catalog Name Payload}
    (roots : Finset Name) (accepted : compatible (footprint pinned roots) pinned incoming = true) :
    footprint incoming roots = footprint pinned roots ∧
      ∀ reached ∈ footprint incoming roots, incoming reached = pinned reached := by
  have same := (compatible_iff (footprint pinned roots) pinned incoming).mp accepted
  have exactFootprint := protected_closure roots same
  exact ⟨exactFootprint, fun reached present => same reached (exactFootprint ▸ present)⟩

namespace Controls

private def testCatalog : Catalog (Fin 3) Nat :=
  fun name => if name = 0 then some ⟨4, {1}⟩ else if name = 1 then some ⟨5, ∅⟩ else none

private def changesUnused : Catalog (Fin 3) Nat :=
  fun name => if name = 2 then some ⟨6, ∅⟩ else testCatalog name

private def changesHelper : Catalog (Fin 3) Nat :=
  fun name => if name = 1 then some ⟨6, ∅⟩ else testCatalog name

theorem unrelated_definition_is_admitted :
    compatible (footprint testCatalog {0}) testCatalog changesUnused = true := by
  decide +kernel

theorem unchanged_entry_cannot_hide_redefined_helper :
    changesHelper 0 = testCatalog 0 ∧
      compatible (footprint testCatalog {0}) testCatalog changesHelper = false := by
  decide +kernel

end Controls

#print axioms protected_closure
#print axioms protected_import
#print axioms Controls.unrelated_definition_is_admitted
#print axioms Controls.unchanged_entry_cannot_hide_redefined_helper

end Mettapedia.GSLT.Contracts.SealedDefinitionGraph
