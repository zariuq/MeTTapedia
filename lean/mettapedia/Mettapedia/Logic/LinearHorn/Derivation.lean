import Mathlib.Data.Multiset.AddSub
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Order.Group.Multiset

/-!
# Multiplicative Horn derivations with declared rules

Sequents have multisets of atoms on both sides. A declared Horn rule has a
tensor of input atoms and a tensor of output atoms. Proofs use identity,
one declared rule, tensor and cut. Multisets provide exchange; there is no
weakening or contraction of the linear contexts. The rule family is reusable,
so a proof records a separate use every time it invokes a declaration.

These are independent logical proof objects, with no reference to a resource
transition relation, search algorithm or interaction interpreter. An empty
multiset is the tensor unit. A residual resource is carried by identity.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearHorn

universe uAtom uRule

inductive Derivation {Atom : Type uAtom} {Rule : Type uRule}
    (premises conclusions : Rule → Multiset Atom) : Multiset Atom → Multiset Atom → Type (max uAtom uRule) where
  | identity (context : Multiset Atom) : Derivation premises conclusions context context
  | rule (declaration : Rule) : Derivation premises conclusions (premises declaration) (conclusions declaration)
  | tensor {left right left' right' : Multiset Atom} :
      Derivation premises conclusions left right → Derivation premises conclusions left' right' →
        Derivation premises conclusions (left + left') (right + right')
  | cut {before middle after : Multiset Atom} :
      Derivation premises conclusions before middle → Derivation premises conclusions middle after →
        Derivation premises conclusions before after

namespace Derivation

variable {Atom : Type uAtom} {Rule : Type uRule} {premises conclusions : Rule → Multiset Atom}

/-- Tensor is sequentialized left then right; independent alternative
sequentializations are not identified by this readout. -/
def uses : {before after : Multiset Atom} → Derivation premises conclusions before after → List Rule
  | _, _, .identity _ => []
  | _, _, .rule declaration => [declaration]
  | _, _, .tensor first second => first.uses ++ second.uses
  | _, _, .cut first second => first.uses ++ second.uses

/-- Every additive invariant of the declared rules is an invariant of the
independent proof calculus. In particular, context resources cannot be
invented merely by identity, tensor or cut. -/
theorem preserves_valuation {Value : Type*} [AddMonoid Value]
    (value : Multiset Atom →+ Value)
    (balanced : ∀ declaration, value (premises declaration) = value (conclusions declaration))
    {before after : Multiset Atom} (proof : Derivation premises conclusions before after) :
    value before = value after := by
  induction proof with
  | identity => rfl
  | rule declaration => exact balanced declaration
  | tensor first second left right => simp only [map_add, left, right]
  | cut first second left right => exact left.trans right

end Derivation

end Mettapedia.Logic.LinearHorn
