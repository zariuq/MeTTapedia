import Mettapedia.Languages.Micromath.Checking
import Mettapedia.Logic.DerivationGraph

/-!
# Micromath on the existing shared certificate graph

The common graph checker resolves earlier premise addresses and invokes the
static Micromath rule validator. This reuses the existing shared proof layer;
it introduces neither a new graph representation nor another replay engine.
The correspondence concerns static derivability, not mutable C slots or the
upstream binary proof format.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.Micromath.SharedChecking
open Mettapedia.Logic
universe u v

abbrev Node (Origin : Type v) := DerivationGraph.Node Claim Checking.RuleTag Origin

def replay {Origin : Type v} (axioms : List Claim) (nodes : List (Node Origin)) : Option (Array Claim) :=
  DerivationGraph.replay (Checking.interface axioms) nodes

theorem root_derives {Origin : Type v} (axioms : List Claim) {nodes : List (Node Origin)}
    {cache : Array Claim} {root : Nat} {claim : Claim}
    (accepted : replay axioms nodes = some cache) (found : cache[root]? = some claim) :
    Micromath.Derives (Checking.basis axioms) claim :=
  Checking.generic_derives_source axioms (DerivationGraph.root_sound (Checking.interface axioms) accepted found)

theorem derives_iff_graph {Origin : Type v} (origin : Origin) (axioms : List Claim) (claim : Claim) :
    Micromath.Derives (Checking.basis axioms) claim ↔
      ∃ (nodes : List (Node Origin)) (cache : Array Claim) (root : Nat),
        replay axioms nodes = some cache ∧ cache[root]? = some claim :=
  (Checking.generic_derives_iff_source axioms claim).symm.trans
    (DerivationGraph.derives_iff_checked_graph (Checking.interface axioms) origin claim)

theorem root_holds {D : Type u} {Origin : Type v} (interpret : Assignment D) (projections : Projects interpret)
    (axioms : List Claim) (axiomsValid : ∀ claim ∈ axioms, Holds interpret claim)
    {nodes : List (Node Origin)} {cache : Array Claim} {root : Nat} {claim : Claim}
    (accepted : replay axioms nodes = some cache) (found : cache[root]? = some claim) : Holds interpret claim :=
  derives_sound interpret projections axiomsValid (root_derives axioms accepted found)

#print axioms root_derives
#print axioms derives_iff_graph
#print axioms root_holds
end Mettapedia.Languages.Micromath.SharedChecking
