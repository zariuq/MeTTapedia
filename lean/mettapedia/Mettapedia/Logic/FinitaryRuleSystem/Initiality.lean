import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mettapedia.Logic.FinitaryRuleSystem.Tree

/-!
# Initial algebra of finite derivation trees

For fixed judgment and witness types, a derivation-node algebra interprets a
conclusion, a rule witness, a finite arity, and the interpretations of the
children.  Finite `Derivation` trees form the initial such algebra.  Replay,
conclusion extraction, and node counting are therefore folds from one common
finite construction, rather than unrelated recursive functions.

This is a structural initiality result.  It does not compare the
proof-theoretic strength of object theories capable of reasoning about these
finite trees.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u v w

/-- An interpretation of one layer of a finite derivation tree. -/
structure NodeAlgebra (J : Type u) (W : Type v) where
  Carrier : Type w
  node : J → W → (n : Nat) → (Fin n → Carrier) → Carrier

namespace NodeAlgebra

variable {J : Type u} {W : Type v}

/-- A function preserving derivation-node formation. -/
@[ext]
structure Hom (A B : NodeAlgebra.{u, v, w} J W) where
  toFun : A.Carrier → B.Carrier
  map_node : ∀ conclusion witness n children,
    toFun (A.node conclusion witness n children) =
      B.node conclusion witness n (fun i => toFun (children i))

instance {A B : NodeAlgebra.{u, v, w} J W} :
    CoeFun (Hom A B) (fun _ => A.Carrier → B.Carrier) :=
  ⟨Hom.toFun⟩

@[ext]
theorem Hom.ext' {A B : NodeAlgebra.{u, v, w} J W} (f g : Hom A B)
    (pointwise : ∀ value, f value = g value) : f = g := by
  cases f with
  | mk f preservesF =>
      cases g with
      | mk g preservesG =>
          change ∀ value, f value = g value at pointwise
          have functionsEqual : f = g := funext pointwise
          subst g
          rfl

/-- Identity node-algebra homomorphism. -/
def Hom.id (A : NodeAlgebra.{u, v, w} J W) : Hom A A where
  toFun := fun value => value
  map_node := by intros; rfl

/-- Composition of node-algebra homomorphisms. -/
def Hom.comp {A B C : NodeAlgebra.{u, v, w} J W}
    (f : Hom A B) (g : Hom B C) : Hom A C where
  toFun := fun value => g (f value)
  map_node := by
    intro conclusion witness n children
    rw [f.map_node, g.map_node]

instance : Category (NodeAlgebra.{u, v, w} J W) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by intros; ext; simp [Hom.comp, Hom.id]
  comp_id := by intros; ext; simp [Hom.comp, Hom.id]
  assoc := by intros; ext; simp [Hom.comp]

/-- The node algebra whose carrier is the finite derivation syntax itself. -/
def derivationAlgebra : NodeAlgebra.{u, v, max u v} J W where
  Carrier := Derivation J W
  node := Derivation.node

/-- Structural recursion from derivation syntax into any node algebra. -/
def fold (A : NodeAlgebra.{u, v, max u v} J W) :
    Derivation J W → A.Carrier
  | .node conclusion witness n children =>
      A.node conclusion witness n (fun i => fold A (children i))

@[simp]
theorem fold_node (A : NodeAlgebra.{u, v, max u v} J W)
    (conclusion : J) (witness : W) (n : Nat)
    (children : Fin n → Derivation J W) :
    fold A (.node conclusion witness n children) =
      A.node conclusion witness n (fun i => fold A (children i)) := rfl

/-- The fold as a node-algebra homomorphism. -/
def foldHom (A : NodeAlgebra.{u, v, max u v} J W) :
    derivationAlgebra ⟶ A where
  toFun := fold A
  map_node := by intros; rfl

/-- Any node-preserving map out of finite derivation syntax is the fold. -/
theorem hom_eq_fold (A : NodeAlgebra.{u, v, max u v} J W)
    (f : derivationAlgebra ⟶ A) : f = foldHom A := by
  apply Hom.ext'
  intro tree
  induction tree with
  | node conclusion witness n children ih =>
      calc
        f.toFun (.node conclusion witness n children) =
            A.node conclusion witness n (fun i => f.toFun (children i)) := by
              simpa [derivationAlgebra] using
                f.map_node conclusion witness n children
        _ = A.node conclusion witness n
            (fun i => fold A (children i)) := by
              congr 1
              funext i
              exact ih i
        _ = fold A (.node conclusion witness n children) := rfl

/-- Finite derivation syntax is initial in the category of node algebras. -/
def derivationAlgebra_isInitial : IsInitial (derivationAlgebra (J := J) (W := W)) :=
  IsInitial.ofUniqueHom foldHom (fun A f => hom_eq_fold A f)

/-- Node interpretation that retains only the conclusion. -/
def conclusionAlgebra : NodeAlgebra.{u, v, max u v} J W where
  Carrier := ULift.{max u v, u} J
  node := fun conclusion _witness _n _children => ULift.up conclusion

theorem fold_conclusion (tree : Derivation J W) :
    (fold conclusionAlgebra tree).down = tree.concl := by
  cases tree
  rfl

/-- Node interpretation that counts physical rule nodes. -/
def nodeCountAlgebra : NodeAlgebra.{u, v, max u v} J W where
  Carrier := ULift.{max u v, 0} Nat
  node := fun _conclusion _witness n children =>
    ULift.up (1 + ∑ i : Fin n, (children i).down)

theorem fold_nodeCount (tree : Derivation J W) :
    (fold nodeCountAlgebra tree).down = tree.nodeCount := by
  induction tree with
  | node conclusion witness n children ih =>
      simp only [fold_node, nodeCountAlgebra, Derivation.nodeCount_node]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => ih i)

/-- One fold computes both the root conclusion and replay result. -/
def replayAlgebra {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) :
    NodeAlgebra.{u, v, max u v} J interface.W where
  Carrier := ULift.{max u v, max u 0} (J × Bool)
  node := fun conclusion witness n children =>
    ULift.up (conclusion,
      interface.isInstance witness
          (List.ofFn fun i : Fin n => (children i).down.1) conclusion &&
        (List.ofFn fun i : Fin n => (children i).down.2).all id)

theorem fold_replay {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules)
    (tree : Derivation J interface.W) :
    (fold (replayAlgebra interface) tree).down =
      (tree.concl, tree.valid interface) := by
  induction tree with
  | node conclusion witness n children ih =>
      simp only [fold_node, replayAlgebra, Derivation.concl,
        Derivation.valid, Prod.mk.injEq, true_and]
      change
        (interface.isInstance witness
            (List.ofFn fun i : Fin n =>
              (fold (replayAlgebra interface) (children i)).down.1)
            conclusion &&
          (List.ofFn fun i : Fin n =>
            (fold (replayAlgebra interface) (children i)).down.2).all id) =
        (interface.isInstance witness
            (List.ofFn fun i : Fin n => (children i).concl) conclusion &&
          (List.ofFn fun i : Fin n =>
            (children i).valid interface).all id)
      have conclusionsEqual :
          (List.ofFn fun i : Fin n =>
              (fold (replayAlgebra interface) (children i)).down.1) =
            List.ofFn fun i : Fin n => (children i).concl := by
        apply congrArg List.ofFn
        funext i
        exact congrArg Prod.fst (ih i)
      have validityEqual :
          (List.ofFn fun i : Fin n =>
              (fold (replayAlgebra interface) (children i)).down.2) =
            List.ofFn fun i : Fin n => (children i).valid interface := by
        apply congrArg List.ofFn
        funext i
        exact congrArg Prod.snd (ih i)
      rw [conclusionsEqual, validityEqual]

/-- Root witness projection, used to state the non-faithfulness control. -/
def rootWitness (tree : Derivation J W) : W :=
  match tree with
  | .node _conclusion witness _n _children => witness

def falseWitnessTree : Derivation Unit Bool :=
  .node () false 0 (fun i => Fin.elim0 i)

def trueWitnessTree : Derivation Unit Bool :=
  .node () true 0 (fun i => Fin.elim0 i)

/-- Negative control: conclusion extraction forgets genuine certificate data. -/
theorem witnessTrees_same_conclusion :
    falseWitnessTree.concl = trueWitnessTree.concl := rfl

theorem witnessTrees_distinct : falseWitnessTree ≠ trueWitnessTree := by
  intro treesEqual
  have witnessesEqual := congrArg rootWitness treesEqual
  simp [falseWitnessTree, trueWitnessTree, rootWitness] at witnessesEqual

end NodeAlgebra

end Mettapedia.Logic.FinitaryRuleSystem
