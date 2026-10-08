import Mettapedia.TypeTheory.IndexedGSOSCoalgebraMonad

/-!
# Cross-base operational lifting controls

The behavior functor reads a successor at another base and a second
successor at the current base. Its natural law adds different constructor
depths to these two readings. Actual lifted maps and multiplication retain
the complete resulting terms. A base-dependent variable map fails the
coalgebra square, showing why a local covariance argument at one base
cannot replace compatibility with the whole behavior functor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.IndexedGSOSControls

open _root_.CategoryTheory IndexedPolynomial IndexedGSOS IndexedGSOS.Operational

abbrev Families := Family Bool (fun _ => Unit)

def polynomial : IndexedPolynomial.{0, 0, 0, 0} Bool (fun _ => Unit) where
  Shape _ _ := Unit
  Position _ := Unit
  next _ _ := ()

/-- This functor genuinely mixes bases and retains two complete successors. -/
def behavior : Families ⥤ Families where
  obj X := fun base index => X (!base) index × X base index
  map mapping := fun base index => ↾(fun pair =>
    (mapping (!base) index pair.1, mapping base index pair.2))
  map_id _ := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro pair
    rfl
  map_comp _ _ := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro pair
    rfl

/-- The supplied law is natural for arbitrary families and maps, with
nontrivial constructor terms in both coordinates of its conclusion. -/
noncomputable def law : Law polynomial behavior where
  app X := fun base index => ↾(fun layer =>
    (Free.node polynomial () (fun _ => Free.pure polynomial (layer.2 ()).2.1),
      Free.node polynomial () (fun _ =>
        Free.node polynomial () (fun _ => Free.pure polynomial (layer.2 ()).2.2))))
  naturality {_ _} mapping := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro layer
    cases layer with
    | mk shape children =>
      cases shape
      apply Prod.ext <;> rfl

abbrev values : Families := fun _ _ => Nat
def otherIncrement (base : Bool) : Nat := if base then 13 else 7
def ownIncrement (base : Bool) : Nat := if base then 17 else 9

abbrev inputs : Endofunctor.Coalgebra behavior where
  V := values
  str := fun base _ => ↾(fun value =>
    (value + otherIncrement base, value + ownIncrement base))

noncomputable def unary {X : Families} (base : Bool) (term : polynomial.Free X base ()) :
    polynomial.Free X base () := Free.node polynomial () (fun _ => term)

noncomputable def single (base : Bool) (value : Nat) : polynomial.Free values base () :=
  unary base (Free.pure polynomial value)

noncomputable def twice {X : Families} (base : Bool) (term : polynomial.Free X base ()) :
    polynomial.Free X base () := unary base (unary base term)

theorem complete_source_retained (base : Bool) (value : Nat) :
    (evaluate law inputs.str base () (single base value)).1 = single base value :=
  evaluate_source law inputs.str base () _

/-- The readout uses the actual lifted object, not a separately chosen behavior. -/
theorem actual_node_behavior (base : Bool) (value : Nat) :
    ((liftedMonad law).obj inputs).str base () (single base value) =
      (single (!base) (value + otherIncrement base),
        twice base (Free.pure polynomial (value + ownIncrement base))) := rfl

theorem both_worlds_change :
    ((liftedMonad law).obj inputs).str false () (single false 0) =
      (single true 7, twice false (Free.pure polynomial 9)) ∧
    ((liftedMonad law).obj inputs).str true () (single true 0) =
      (single false 13, twice true (Free.pure polynomial 17)) := ⟨rfl, rfl⟩

def shift : inputs ⟶ inputs where
  f := fun _ _ => ↾(fun value => value + 3)
  h := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro value
    change (value + otherIncrement base + 3, value + ownIncrement base + 3) =
      (value + 3 + otherIncrement base, value + 3 + ownIncrement base)
    exact Prod.ext (Nat.add_right_comm value (otherIncrement base) 3)
      (Nat.add_right_comm value (ownIncrement base) 3)

theorem actual_map_retains_constructor (base : Bool) (value : Nat) :
    ((liftedMonad law).map shift).f base () (single base value) =
      single base (value + 3) := rfl

theorem actual_mapped_behavior (base : Bool) (value : Nat) :
    ((liftedMonad law).obj inputs).str base ()
        (((liftedMonad law).map shift).f base () (single base value)) =
      (single (!base) (value + 3 + otherIncrement base),
        twice base (Free.pure polynomial (value + 3 + ownIncrement base))) := rfl

theorem actual_complete_map_square (base : Bool) (term : polynomial.Free values base ()) :
    behavior.map ((liftedMonad law).map shift).f base ()
        (((liftedMonad law).obj inputs).str base () term) =
      ((liftedMonad law).obj inputs).str base ()
        (((liftedMonad law).map shift).f base () term) :=
  congrArg (fun arrow => arrow base () term) ((liftedMonad law).map shift).h

noncomputable def nested (base : Bool) (value : Nat) :
    polynomial.Free (polynomial.Free values) base () :=
  unary base (Free.pure polynomial (single base value))

theorem actual_multiplication_retains_both_nodes (base : Bool) (value : Nat) :
    ((liftedMonad law).μ.app inputs).f base () (nested base value) =
      unary base (single base value) := rfl

theorem actual_flattened_behavior (base : Bool) (value : Nat) :
    ((liftedMonad law).obj inputs).str base ()
        (((liftedMonad law).μ.app inputs).f base () (nested base value)) =
      (twice (!base) (Free.pure polynomial (value + otherIncrement base)),
        twice base (twice base (Free.pure polynomial (value + ownIncrement base)))) := rfl

theorem actual_complete_multiplication_square
    (base : Bool) (term : polynomial.Free (polynomial.Free values) base ()) :
    behavior.map ((liftedMonad law).μ.app inputs).f base ()
        (((liftedMonad law).obj ((liftedMonad law).obj inputs)).str base () term) =
      ((liftedMonad law).obj inputs).str base ()
        (((liftedMonad law).μ.app inputs).f base () term) :=
  congrArg (fun arrow => arrow base () term) ((liftedMonad law).μ.app inputs).h

def conflicting : values ⟶ values :=
  fun base _ => ↾(fun value => value + if base then 5 else 3)

/-- Both coordinates are actual supplied variable maps, but the first
successor is observed at another base, where the incompatible offset differs. -/
theorem conflicting_has_no_coalgebra_map :
    ¬ ∃ mapping : inputs ⟶ inputs, mapping.f = conflicting := by
  rintro ⟨mapping, same⟩
  have square := mapping.h
  rw [same] at square
  have reading := congrArg (fun arrow => (arrow false () 0).1) square
  change (12 : Nat) = 10 at reading
  omega

noncomputable def valueReadout (base : Bool) : polynomial.Free values base () → Nat :=
  Free.fold polynomial (fun _ _ value => value)
    ⟨fun _ _ layer => layer.2 ()⟩ base ()

/-- Arbitrary variable relabeling need not preserve the operational coalgebra,
already at a pure leaf. The input-compatibility premise is substantive. -/
theorem incompatible_operational_rename :
    coalgebra law inputs.str false ()
        ((FreeAdjunction.monad polynomial).map conflicting false () (Free.pure polynomial 0)) ≠
      behavior.map ((FreeAdjunction.monad polynomial).map conflicting) false ()
        (coalgebra law inputs.str false () (Free.pure polynomial 0)) := by
  intro same
  have reading := congrArg (fun pair => valueReadout true pair.1) same
  change (10 : Nat) = 12 at reading
  omega

end Mettapedia.TypeTheory.IndexedGSOSControls
