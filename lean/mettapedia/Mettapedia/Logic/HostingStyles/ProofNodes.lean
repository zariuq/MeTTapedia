import Mettapedia.Logic.HostingStyles.ProofTheory

/-!
# The root of a derivation

Every derivation of a rule signature is one rule applied to derivations
(`RuleSignature.Proof.exists_node`), and two derivations with different rules
at the root are different (`RuleSignature.node_ne_of_shape_ne`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

namespace RuleSignature

variable {J : Type} (P : RuleSignature J)

/-- Every derivation is a rule applied to derivations. -/
theorem Proof.exists_node {j : J} (proof : P.Proof j) :
    ∃ shape children, proof = P.node shape children := by
  induction proof using RuleSignature.Proof.induction with
  | node shape children _ => exact ⟨shape, children, rfl⟩

/-- The rule at the root of a derivation. -/
def rootShape {j : J} (proof : P.Proof j) : P.Shape PUnit.unit j :=
  (Fix.out P proof).1

@[simp] theorem rootShape_node {j : J} (shape : P.Shape PUnit.unit j)
    (children : (position : P.Position shape) → P.Proof (P.next shape position)) :
    P.rootShape (P.node shape children) = shape := rfl

/-- Derivations with different rules at the root are different. -/
theorem node_ne_of_shape_ne {j : J} {first second : P.Shape PUnit.unit j}
    (distinct : first ≠ second)
    (firstChildren : (position : P.Position first) → P.Proof (P.next first position))
    (secondChildren : (position : P.Position second) → P.Proof (P.next second position)) :
    P.node first firstChildren ≠ P.node second secondChildren :=
  fun same => distinct (congrArg P.rootShape same)

end RuleSignature

#print axioms RuleSignature.Proof.exists_node
#print axioms RuleSignature.node_ne_of_shape_ne

end Mettapedia.Logic.HostingStyles
