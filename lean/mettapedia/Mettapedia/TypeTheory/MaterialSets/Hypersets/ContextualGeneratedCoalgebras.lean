import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFunctor
import Mettapedia.TypeTheory.MaterialSets.Hypersets.LocallyPresentedCoalgebras
import Mettapedia.TypeTheory.ContextualWitnessCover

/-!
# Small generated contextual coalgebras

An authored enumeration of each stable future successor predicate supplies
small branch receipts. Finite paths retain both actual context moves and
enumerated successors. A fibre consists of a path together with an actual
arrow from its endpoint context, so context restriction is postcomposition.

The possibly larger state is computed from the small path; it is never
stored in its carrier. The natural endpoint map covers every future
successor of the original coalgebra. Enumeration data are inputs; their
mere propositional existence does not provide a selected enumeration.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedCoalgebras

open CategoryTheory
open PowerClassPresheafBaseChange
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u v
variable {D : Type u} [Category.{u} D] (A : D ⥤ Type v)

abbrev State := Σ point : D, A.obj point

variable (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable (enumeration : ∀ point value, CoveredFuturePowerFamilies.Enumeration (coalgebra.app point value).val)

/-- Both kinds of receipts live at the small context bound. -/
def pathSystem : LocallyPresentedCoalgebras.Coalgebra.{u, max u v} (State A) where
  Branch state := (Σ target : D, state.1 ⟶ target) ⊕
    (Σ future : Future.Objects state.1, (enumeration state.1 state.2).Carrier future)
  next state branch := match branch with
    | .inl move => ⟨move.1, A.map move.2 state.2⟩
    | .inr child => ⟨child.1.1, (enumeration state.1 state.2).value child.1 child.2⟩

variable (root : State A)

abbrev PathNode : Type u := LocallyPresentedCoalgebras.Node (pathSystem A coalgebra enumeration) root

def endState (node : PathNode A coalgebra enumeration root) : State A :=
  LocallyPresentedCoalgebras.endpoint (pathSystem A coalgebra enumeration) node

/-- The terminal arrow makes the generated carrier strictly context closed. -/
def family : D ⥤ Type u where
  obj point := Σ node : PathNode A coalgebra enumeration root,
    (endState A coalgebra enumeration root node).1 ⟶ point
  map step := TypeCat.ofHom (fun receipt => ⟨receipt.1, receipt.2 ≫ step⟩)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact congrArg (Sigma.mk receipt.1) (Category.comp_id receipt.2)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact congrArg (Sigma.mk receipt.1) (Category.assoc receipt.2 first second).symm

def endpoint : NaturalHom (family A coalgebra enumeration root) A where
  app _ receipt := A.map receipt.2 (endState A coalgebra enumeration root receipt.1).2
  naturality step receipt :=
    (congrArg (fun operation => operation (endState A coalgebra enumeration root receipt.1).2)
      (A.map_comp receipt.2 step)).symm

def rootMember : (family A coalgebra enumeration root).obj root.1 :=
  ⟨LocallyPresentedCoalgebras.rootNode (pathSystem A coalgebra enumeration) root, 𝟙 root.1⟩

theorem endpoint_root :
    (endpoint A coalgebra enumeration root).app root.1 (rootMember A coalgebra enumeration root) = root.2 :=
  congrArg (fun operation => operation root.2) (A.map_id root.1)

def contextNode (node : PathNode A coalgebra enumeration root) (target : D)
    (move : (endState A coalgebra enumeration root node).1 ⟶ target) :
    PathNode A coalgebra enumeration root :=
  LocallyPresentedCoalgebras.append (pathSystem A coalgebra enumeration) node (.inl ⟨target, move⟩)

theorem endState_contextNode (node : PathNode A coalgebra enumeration root) (target : D)
    (move : (endState A coalgebra enumeration root node).1 ⟶ target) :
    endState A coalgebra enumeration root (contextNode A coalgebra enumeration root node target move) =
      ⟨target, A.map move (endState A coalgebra enumeration root node).2⟩ := rfl

def childNode (node : PathNode A coalgebra enumeration root)
    (future : Future.Objects (endState A coalgebra enumeration root node).1)
    (code : (enumeration (endState A coalgebra enumeration root node).1
      (endState A coalgebra enumeration root node).2).Carrier future) :
    PathNode A coalgebra enumeration root :=
  LocallyPresentedCoalgebras.append (pathSystem A coalgebra enumeration) node (.inr ⟨future, code⟩)

theorem endState_childNode (node : PathNode A coalgebra enumeration root)
    (future : Future.Objects (endState A coalgebra enumeration root node).1)
    (code : (enumeration (endState A coalgebra enumeration root node).1
      (endState A coalgebra enumeration root node).2).Carrier future) :
    endState A coalgebra enumeration root (childNode A coalgebra enumeration root node future code) =
      ⟨future.1, (enumeration (endState A coalgebra enumeration root node).1
        (endState A coalgebra enumeration root node).2).value future code⟩ := rfl

def childReceipt (node : PathNode A coalgebra enumeration root)
    (future : Future.Objects (endState A coalgebra enumeration root node).1)
    (code : (enumeration (endState A coalgebra enumeration root node).1
      (endState A coalgebra enumeration root node).2).Carrier future) :
    (family A coalgebra enumeration root).obj future.1 :=
  ⟨childNode A coalgebra enumeration root node future code, 𝟙 future.1⟩

theorem endpoint_childReceipt (node : PathNode A coalgebra enumeration root)
    (future : Future.Objects (endState A coalgebra enumeration root node).1)
    (code : (enumeration (endState A coalgebra enumeration root node).1
      (endState A coalgebra enumeration root node).2).Carrier future) :
    (endpoint A coalgebra enumeration root).app future.1
      (childReceipt A coalgebra enumeration root node future code) =
        (enumeration (endState A coalgebra enumeration root node).1
          (endState A coalgebra enumeration root node).2).value future code :=
  congrArg (fun operation => operation ((enumeration (endState A coalgebra enumeration root node).1
    (endState A coalgebra enumeration root node).2).value future code)) (A.map_id future.1)

abbrev endpointArguments (point : D) :=
  CoveredFuturePowerFunctor.futureArguments (endpoint A coalgebra enumeration root) point

def generatedPredicate (point : D) (receipt : (family A coalgebra enumeration root).obj point) :
    CoveredFuturePowerFamilies.Predicate (family A coalgebra enumeration root) point where
  holds argument := (coalgebra.app point ((endpoint A coalgebra enumeration root).app point receipt)).val.holds
    ((endpointArguments A coalgebra enumeration root point).obj argument)
  closed move available :=
    (coalgebra.app point ((endpoint A coalgebra enumeration root).app point receipt)).val.closed
      ((endpointArguments A coalgebra enumeration root point).map move) available

/-- Context naturality of the original coalgebra supplies exactly the
future substitution used by the generated carrier. -/
theorem coalgebra_transport {first second : D} (step : first ⟶ second)
    (receipt : (family A coalgebra enumeration root).obj first)
    (future : Future.Objects second) (argument : A.obj future.1) :
    (coalgebra.app second ((endpoint A coalgebra enumeration root).app second
      ((family A coalgebra enumeration root).map step receipt))).val.holds ⟨future, argument⟩ ↔
    (coalgebra.app first ((endpoint A coalgebra enumeration root).app first receipt)).val.holds
      ⟨⟨future.1, step ≫ future.2⟩, argument⟩ := by
  have same := (coalgebra.naturality step ((endpoint A coalgebra enumeration root).app first receipt)).trans
    (congrArg (coalgebra.app second) ((endpoint A coalgebra enumeration root).naturality step receipt))
  exact Iff.of_eq (congrArg (fun power : CoveredFuturePowerFamilies.Power A second => power.val.holds ⟨future, argument⟩) same).symm

/-- The generated coalgebra uses the actual small truth subtype as its
enumeration. No original enumeration is selected by this definition. -/
def generatedCoalgebra : NaturalHom (family A coalgebra enumeration root)
    (CoveredFuturePowerFamilies.family (family A coalgebra enumeration root)) where
  app point receipt :=
    ⟨generatedPredicate A coalgebra enumeration root point receipt,
      ⟨CoveredFuturePowerFamilies.smallEnumeration (generatedPredicate A coalgebra enumeration root point receipt)⟩⟩
  naturality step receipt := by
    apply Subtype.ext
    apply CoveredFuturePowerFamilies.Predicate.ext
    intro argument
    exact (coalgebra_transport A coalgebra enumeration root step receipt argument.1
      ((endpoint A coalgebra enumeration root).app argument.1.1 argument.2)).symm

theorem generated_truth (point : D) (receipt : (family A coalgebra enumeration root).obj point)
    (future : CoveredFuturePowerFamilies.Arguments (family A coalgebra enumeration root) point) :
    ((generatedCoalgebra A coalgebra enumeration root).app point receipt).val.holds future ↔
    (coalgebra.app point ((endpoint A coalgebra enumeration root).app point receipt)).val.holds
      ⟨future.1, (endpoint A coalgebra enumeration root).app future.1.1 future.2⟩ := Iff.rfl

/-- Every original future successor has an actual generated receipt at that
same future context, with its complete endpoint value preserved. -/
theorem forward_cover (point : D) (receipt : (family A coalgebra enumeration root).obj point)
    (future : Future.Objects point) (argument : A.obj future.1) :
    (coalgebra.app point ((endpoint A coalgebra enumeration root).app point receipt)).val.holds
      ⟨future, argument⟩ ↔
    ∃ child : (family A coalgebra enumeration root).obj future.1,
      ((generatedCoalgebra A coalgebra enumeration root).app point receipt).val.holds ⟨future, child⟩ ∧
        (endpoint A coalgebra enumeration root).app future.1 child = argument := by
  constructor
  · intro available
    let oldState := endState A coalgebra enumeration root receipt.1
    let oldFuture : Future.Objects oldState.1 := ⟨future.1, receipt.2 ≫ future.2⟩
    have same := coalgebra.naturality receipt.2 oldState.2
    have oldTruth : (coalgebra.app oldState.1 oldState.2).val.holds ⟨oldFuture, argument⟩ :=
      Eq.mpr (congrArg (fun power : CoveredFuturePowerFamilies.Power A point => power.val.holds ⟨future, argument⟩) same) available
    obtain ⟨code, codeValue⟩ := ((enumeration oldState.1 oldState.2).covered oldFuture argument).mp oldTruth
    let child := childReceipt A coalgebra enumeration root receipt.1 oldFuture code
    have childValue : (endpoint A coalgebra enumeration root).app future.1 child = argument :=
      (endpoint_childReceipt A coalgebra enumeration root receipt.1 oldFuture code).trans codeValue
    refine ⟨child, ?_, childValue⟩
    change (coalgebra.app point ((endpoint A coalgebra enumeration root).app point receipt)).val.holds
      ⟨future, (endpoint A coalgebra enumeration root).app future.1 child⟩
    rw [childValue]
    exact available
  · rintro ⟨child, available, same⟩
    change (coalgebra.app point ((endpoint A coalgebra enumeration root).app point receipt)).val.holds
      ⟨future, (endpoint A coalgebra enumeration root).app future.1 child⟩ at available
    rw [same] at available
    exact available

/-- The endpoint is a coalgebra morphism for the actual small-covered power
functor. Both sides are whole natural maps, not only present observations. -/
theorem coalgebra_square :
    (generatedCoalgebra A coalgebra enumeration root).comp
      (CoveredFuturePowerFunctor.imageHom (endpoint A coalgebra enumeration root)) =
    (endpoint A coalgebra enumeration root).comp coalgebra := by
  apply NaturalHom.ext
  intro point receipt
  apply Subtype.ext
  apply CoveredFuturePowerFamilies.Predicate.ext
  intro argument
  constructor
  · rintro ⟨child, same, available⟩
    exact (forward_cover A coalgebra enumeration root point receipt argument.1 argument.2).mpr
      ⟨child, available, same⟩
  · intro available
    obtain ⟨child, available, same⟩ :=
      (forward_cover A coalgebra enumeration root point receipt argument.1 argument.2).mp available
    exact ⟨child, same, available⟩

/-- Reachability allows actual context moves and admitted future children. -/
def Step (source target : State A) : Prop :=
  (∃ move : source.1 ⟶ target.1, A.map move source.2 = target.2) ∨
  (∃ move : source.1 ⟶ target.1,
    (coalgebra.app source.1 source.2).val.holds ⟨⟨target.1, move⟩, target.2⟩)

theorem path_next_step (state : State A)
    (branch : (pathSystem A coalgebra enumeration).Branch state) :
    Step A coalgebra state ((pathSystem A coalgebra enumeration).next state branch) := by
  cases branch with
  | inl move => exact .inl ⟨move.2, rfl⟩
  | inr child => exact .inr ⟨child.1.2,
      ((enumeration state.1 state.2).covered child.1 _).mpr ⟨child.2, rfl⟩⟩

theorem path_endpoint_reachable (node : PathNode A coalgebra enumeration root) :
    Relation.ReflTransGen (Step A coalgebra) root (endState A coalgebra enumeration root node) := by
  have reachable := LocallyPresentedCoalgebras.path_reachable
    (pathSystem A coalgebra enumeration) root node.1 node.2
  exact Relation.ReflTransGen.lift
    (r := LocallyPresentedCoalgebras.edge (pathSystem A coalgebra enumeration))
    (p := Step A coalgebra) (endState A coalgebra enumeration root)
    (fun _ _ available => by
      obtain ⟨branch, rfl⟩ := available
      exact path_next_step A coalgebra enumeration _ branch) _ _ reachable

/-- Every generated member is actually reachable, including its retained
terminal context transport. -/
theorem generated_reachable (point : D) (receipt : (family A coalgebra enumeration root).obj point) :
    Relation.ReflTransGen (Step A coalgebra) root
      ⟨point, (endpoint A coalgebra enumeration root).app point receipt⟩ :=
  (path_endpoint_reachable A coalgebra enumeration root receipt.1).tail
    (.inl ⟨receipt.2, rfl⟩)

/-- Conversely, every reachable original value has a small generated
receipt. The proof supplies an existential cover, not a selected inverse. -/
theorem reachable_covered (target : State A)
    (reachable : Relation.ReflTransGen (Step A coalgebra) root target) :
    ∃ receipt : (family A coalgebra enumeration root).obj target.1,
      (endpoint A coalgebra enumeration root).app target.1 receipt = target.2 := by
  induction reachable with
  | refl => exact ⟨rootMember A coalgebra enumeration root, endpoint_root A coalgebra enumeration root⟩
  | @tail middle target earlier move covered =>
    obtain ⟨receipt, decoded⟩ := covered
    cases move with
    | inl transported =>
      obtain ⟨step, same⟩ := transported
      refine ⟨(family A coalgebra enumeration root).map step receipt, ?_⟩
      exact ((endpoint A coalgebra enumeration root).naturality step receipt).symm.trans
        ((congrArg (A.map step) decoded).trans same)
    | inr admitted =>
      obtain ⟨step, truth⟩ := admitted
      have generatedTruth :
          (coalgebra.app middle.1 ((endpoint A coalgebra enumeration root).app middle.1 receipt)).val.holds
            ⟨⟨target.1, step⟩, target.2⟩ := by
        rw [decoded]
        exact truth
      obtain ⟨child, _available, same⟩ :=
        (forward_cover A coalgebra enumeration root middle.1 receipt ⟨target.1, step⟩ target.2).mp generatedTruth
      exact ⟨child, same⟩

theorem reachable_iff_covered (point : D) (argument : A.obj point) :
    Relation.ReflTransGen (Step A coalgebra) root ⟨point, argument⟩ ↔
    ∃ receipt : (family A coalgebra enumeration root).obj point,
      (endpoint A coalgebra enumeration root).app point receipt = argument := by
  constructor
  · exact reachable_covered A coalgebra enumeration root ⟨point, argument⟩
  · rintro ⟨receipt, same⟩
    have reachable := generated_reachable A coalgebra enumeration root point receipt
    rw [same] at reachable
    exact reachable

/-- The reachable subfamily remains in the original argument universe.
Its constructed small cover is separate from any chosen inverse. -/
def reachableFamily : D ⥤ Type v where
  obj point := {argument : A.obj point //
    Relation.ReflTransGen (Step A coalgebra) root ⟨point, argument⟩}
  map step := TypeCat.ofHom (fun argument => ⟨A.map step argument.val,
    argument.property.tail (.inl ⟨step, rfl⟩)⟩)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro argument
    exact Subtype.ext (congrArg (fun operation => operation argument.val) (A.map_id point))
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro argument
    exact Subtype.ext (congrArg (fun operation => operation argument.val) (A.map_comp first second))

def reachabilityCover : NaturalHom (family A coalgebra enumeration root)
    (reachableFamily A coalgebra root) where
  app point receipt := ⟨(endpoint A coalgebra enumeration root).app point receipt,
    generated_reachable A coalgebra enumeration root point receipt⟩
  naturality step receipt := Subtype.ext ((endpoint A coalgebra enumeration root).naturality step receipt)

theorem reachabilityCover_surjective (point : D) :
    Function.Surjective ((reachabilityCover A coalgebra enumeration root).app point) := by
  intro argument
  obtain ⟨receipt, same⟩ := reachable_covered A coalgebra enumeration root ⟨point, argument.val⟩ argument.property
  exact ⟨receipt, Subtype.ext same⟩

/-- Actual branch receipts remain distinct even when their endpoint values
coincide. No branch is recovered by choosing a relational witness. -/
theorem append_injective (node : PathNode A coalgebra enumeration root) :
    Function.Injective (LocallyPresentedCoalgebras.append (pathSystem A coalgebra enumeration) node) := by
  intro first second same
  have pathSame := eq_of_heq (Sigma.mk.inj same).2
  exact eq_of_heq (Sigma.mk.inj pathSame).2

theorem contextNode_injective (node : PathNode A coalgebra enumeration root) (target : D) :
    Function.Injective (contextNode A coalgebra enumeration root node target) := by
  intro first second same
  have receipts := Sum.inl.inj (append_injective A coalgebra enumeration root node same)
  exact eq_of_heq (Sigma.mk.inj receipts).2

theorem childNode_injective (node : PathNode A coalgebra enumeration root)
    (future : Future.Objects (endState A coalgebra enumeration root node).1) :
    Function.Injective (childNode A coalgebra enumeration root node future) := by
  intro first second same
  have receipts := Sum.inr.inj (append_injective A coalgebra enumeration root node same)
  exact eq_of_heq (Sigma.mk.inj receipts).2

theorem contextNode_ne_childNode (node : PathNode A coalgebra enumeration root)
    (future : Future.Objects (endState A coalgebra enumeration root node).1)
    (code : (enumeration (endState A coalgebra enumeration root node).1
      (endState A coalgebra enumeration root node).2).Carrier future) :
    contextNode A coalgebra enumeration root node future.1 future.2 ≠
      childNode A coalgebra enumeration root node future code := by
  intro same
  have impossible := append_injective A coalgebra enumeration root node same
  cases impossible

theorem restriction_node {first second : D} (step : first ⟶ second)
    (receipt : (family A coalgebra enumeration root).obj first) :
    ((family A coalgebra enumeration root).map step receipt).1 = receipt.1 := rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedCoalgebras
