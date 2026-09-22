import Mettapedia.TypeTheory.IndexedPolynomialFree
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
# Coalgebraic realization of indexed method trees

An indexed polynomial acts on the category of indexed families by retaining
shapes and mapping their children. A coalgebra for `Holes + P` exposes either
an indexed leaf or a method together with successor states at all its typed
obligations. This is the existing categorical coalgebra interface, not another
method or agent record.

Bounded unfolding produces the existing free tree. Its leaves distinguish
retained provider states from returned hole values. Resumption fills only the
former, and successive depth budgets compose by the proved free substitution
law. Depth bounds are not work receipts, refutations, or completeness claims.
Neither finite branching nor a scheduling convention is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial

open CategoryTheory

universe u

variable {Base : Type u} {Index : Base → Type u}
variable (P : IndexedPolynomial.{u, u, u, u} Base Index)

/-- The pointwise category of families over the original base and indices. -/
abbrev Family (baseType : Type u) (indexType : baseType → Type u) : Type (u + 1) :=
  (base : baseType) → indexType base → Type u

/-- The actual polynomial extension is an endofunctor of indexed families. -/
def endofunctor : Family Base Index ⥤ Family Base Index where
  obj := P.Extension
  map mapping := fun base index =>
    ↾(Extension.map P (fun b i => mapping b i))
  map_id family := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro layer
    exact Extension.map_id P layer
  map_comp earlier later := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro layer
    exact (Extension.map_comp P (fun b i => earlier b i)
      (fun b i => later b i) layer).symm

namespace CoalgebraicPlans

variable {P}
variable {H : (base : Base) → Index base → Type u}

/-- The existing endofunctor coalgebra, for methods with returned leaves. -/
abbrev Realizer := Endofunctor.Coalgebra ((P.withHoles H).endofunctor)

/-- An unfinished provider state and a returned leaf remain distinguishable. -/
abbrev Residual (realizer : Realizer (P := P) (H := H))
    (base : Base) (index : Index base) := realizer.V base index ⊕ H base index

/-- Unfold the provider to a depth, retaining every frontier state as a hole.
This bounds method depth; arbitrary position families are not enumerated. -/
def unfoldPrefix (realizer : Realizer (P := P) (H := H)) :
    Nat → ∀ base index, realizer.V base index → P.Free (Residual realizer) base index
  | 0, _, _, state => Free.pure P (.inl state)
  | depth + 1, base, index, state =>
      match realizer.str base index state with
      | ⟨.inl value, _⟩ => Free.pure P (.inr value)
      | ⟨.inr shape, children⟩ =>
          Free.node P shape (fun position =>
            unfoldPrefix realizer depth base (P.next shape position) (children position))

/-- Continue actual frontier states; a returned leaf is never requested again. -/
def resume (realizer : Realizer (P := P) (H := H)) (depth : Nat) :
    ∀ base index, Residual realizer base index → P.Free (Residual realizer) base index
  | base, index, .inl state => unfoldPrefix realizer depth base index state
  | _, _, .inr value => Free.pure P (.inr value)

@[simp] theorem prefix_zero (realizer : Realizer (P := P) (H := H))
    {base : Base} {index : Index base} (state : realizer.V base index) :
    unfoldPrefix realizer 0 base index state = Free.pure P (.inl state) := rfl

@[simp] theorem resume_returned (realizer : Realizer (P := P) (H := H))
    (depth : Nat) {base : Base} {index : Index base} (value : H base index) :
    resume realizer depth base index (.inr value) = Free.pure P (.inr value) := rfl

/-- A resumed prefix is exactly the larger depth prefix, including all leaves
and method occurrences, not merely its reconstructed endpoint. -/
theorem prefix_add (realizer : Realizer (P := P) (H := H))
    (earlier later : Nat) {base : Base} {index : Index base}
    (state : realizer.V base index) :
    unfoldPrefix realizer (earlier + later) base index state =
      Free.bind P (resume realizer later) base index
        (unfoldPrefix realizer earlier base index state) := by
  induction earlier generalizing index with
  | zero => simp only [Nat.zero_add, prefix_zero, Free.bind_pure, resume]
  | succ earlier ih =>
      rw [Nat.succ_add]
      unfold unfoldPrefix
      cases realizer.str base index state with
      | mk shape children =>
          cases shape with
          | inl value => rfl
          | inr shape =>
              change Free.node P shape (fun position =>
                  unfoldPrefix realizer (earlier + later) base _ (children position)) = _
              rw [Free.bind_node]
              congr 1
              funext position
              exact ih (children position)

/-- The state-free leaf map induced by a coalgebra morphism. -/
def residualMap {first second : Realizer (P := P) (H := H)}
    (hom : first ⟶ second) : ∀ base index,
      Residual first base index → Residual second base index
  | base, index, .inl state => .inl (hom.f base index state)
  | _, _, .inr value => .inr value

/-- A coalgebra morphism preserves every bounded method tree and returned
leaf, while mapping the still-unfinished provider states. -/
theorem prefix_hom {first second : Realizer (P := P) (H := H)}
    (hom : first ⟶ second) (depth : Nat)
    {base : Base} {index : Index base} (state : first.V base index) :
    Free.map P (residualMap hom) base index (unfoldPrefix first depth base index state) =
      unfoldPrefix second depth base index (hom.f base index state) := by
  induction depth generalizing index with
  | zero => rfl
  | succ depth ih =>
      have step := congrArg
        (fun mapping => mapping base index state) hom.h
      change Extension.map (P.withHoles H) (fun b i => hom.f b i)
          (first.str base index state) =
        second.str base index (hom.f base index state) at step
      unfold unfoldPrefix
      rw [← step]
      cases first.str base index state with
      | mk shape children =>
          cases shape with
          | inl value => rfl
          | inr shape =>
              rw [Free.map_node]
              congr 1
              funext position
              exact ih (children position)

/-- Existing free plans expose their own layer as a genuine coalgebra. -/
def retainedPlanRealizer : Realizer (P := P) (H := H) where
  V := P.Free H
  str := fun _ _ => ↾(Fix.out (P.withHoles H))

end CoalgebraicPlans

#print axioms endofunctor
#print axioms CoalgebraicPlans.prefix_add
#print axioms CoalgebraicPlans.prefix_hom

end Mettapedia.TypeTheory.IndexedPolynomial
