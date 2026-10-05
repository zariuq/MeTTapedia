import Mettapedia.TypeTheory.MaterialSets.Hypersets.LabelledDependentProducts
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafBaseChange
import Mathlib.Logic.Encodable.Basic

/-!
# Faithful labels for contexts, arrows and dependent arguments

A full contextual function receives a future world, its actual restriction
arrow and a dependent argument. Their graph labels can be constructed from
faithful codings of these three pieces. This construction works in categories
with parallel arrows and does not require an inverse decoder for any index.

An authored `Encodable` dictionary supplies such labels without selecting an
enumeration from a propositional countability claim. The concrete category of
labelled context paths has infinitely many worlds and parallel arrows. Its
argument family grows with context length; path labels and their order remain
observable even when their endpoints and transported arguments agree.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

open CategoryTheory
open PowerClassPresheafBaseChange

universe u

namespace ArgumentCoding

/-- The encoder is supplied as authored data. Only its proved injectivity is
used; material argument membership does not select a host value. -/
def ofEncodable (A : Type u) [Encodable A] : ArgumentCoding A where
  graph argument := OutcomeLabels.chainGraph (Encodable.encode argument)
  injective := by
    intro first second same
    dsimp only at same
    rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at same
    exact Encodable.encode_injective (OutcomeLabels.chainValue_injective same)

private theorem pair_not_empty (first second : HSet.{u}) :
    HSet.kpair first second ≠ ∅ := by
  intro same
  have member : ({first} : HSet.{u}) ∈ HSet.kpair first second :=
    HSet.mem_pair.mpr (Or.inl rfl)
  rw [same] at member
  exact HSet.notMem_empty _ member

/-- Lists retain both order and multiplicity by recursively labelled pairs. -/
def listGraph {A : Type u} (coding : ArgumentCoding A) : List A → AccessiblePointedGraph.{u}
  | [] => AccessiblePointedGraph.empty
  | first :: rest => AccessiblePointedGraph.kpairGraph (coding.graph first) (listGraph coding rest)

theorem listGraph_injective {A : Type u} (coding : ArgumentCoding A) :
    Function.Injective (fun path => HSet.mk (listGraph coding path)) := by
  intro first
  induction first with
  | nil =>
    intro second same
    cases second with
    | nil => rfl
    | cons head tail =>
      change HSet.mk AccessiblePointedGraph.empty =
        HSet.mk (AccessiblePointedGraph.kpairGraph (coding.graph head) (listGraph coding tail)) at same
      rw [HSet.mk_empty, AccessiblePointedGraph.mk_kpairGraph] at same
      exact (pair_not_empty _ _ same.symm).elim
  | cons head tail inductionHypothesis =>
    intro second same
    cases second with
    | nil =>
      change HSet.mk (AccessiblePointedGraph.kpairGraph (coding.graph head) (listGraph coding tail)) =
        HSet.mk AccessiblePointedGraph.empty at same
      rw [AccessiblePointedGraph.mk_kpairGraph, HSet.mk_empty] at same
      exact (pair_not_empty _ _ same).elim
    | cons next rest =>
      change HSet.mk (AccessiblePointedGraph.kpairGraph (coding.graph head) (listGraph coding tail)) =
        HSet.mk (AccessiblePointedGraph.kpairGraph (coding.graph next) (listGraph coding rest)) at same
      rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph] at same
      exact congrArg₂ List.cons (coding.injective (HSet.kpair_inj.mp same).1)
        (inductionHypothesis (HSet.kpair_inj.mp same).2)

def lists {A : Type u} (coding : ArgumentCoding A) : ArgumentCoding (List A) where
  graph := listGraph coding
  injective := listGraph_injective coding

variable {D : Type u} [Category.{u} D]

/-- All three components of a future index are retained. In particular the
arrow labels are not replaced by labels for their endpoints. -/
def contextual (worlds : ArgumentCoding D)
    (arrows : (source target : D) → ArgumentCoding (source ⟶ target))
    (family : D ⥤ Type u) (arguments : (world : D) → ArgumentCoding (family.obj world))
    (point : D) : ArgumentCoding (Future.domain family point).Elements where
  graph index := AccessiblePointedGraph.kpairGraph (worlds.graph index.1.1)
    (AccessiblePointedGraph.kpairGraph ((arrows point index.1.1).graph index.1.2)
      ((arguments index.1.1).graph index.2))
  injective := by
    rintro ⟨⟨firstWorld, firstArrow⟩, firstArgument⟩
      ⟨⟨secondWorld, secondArrow⟩, secondArgument⟩ same
    dsimp only at same
    rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph,
      AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph] at same
    have worldsEq := worlds.injective (HSet.kpair_inj.mp same).1
    cases worldsEq
    have components := HSet.kpair_inj.mp (HSet.kpair_inj.mp same).2
    have arrowsEq := (arrows point firstWorld).injective components.1
    cases arrowsEq
    have argumentsEq := (arguments firstWorld).injective components.2
    cases argumentsEq
    rfl

theorem contextual_reading (worlds : ArgumentCoding D)
    (arrows : (source target : D) → ArgumentCoding (source ⟶ target))
    (family : D ⥤ Type u) (arguments : (world : D) → ArgumentCoding (family.obj world))
    (point : D) (index : (Future.domain family point).Elements) :
    (contextual worlds arrows family arguments point).reading index =
      HSet.kpair (worlds.reading index.1.1)
        (HSet.kpair ((arrows point index.1.1).reading index.1.2)
          ((arguments index.1.1).reading index.2)) := by
  simp only [reading, contextual, AccessiblePointedGraph.mk_kpairGraph]

theorem parallel_arrows_distinguished (worlds : ArgumentCoding D)
    (arrows : (source target : D) → ArgumentCoding (source ⟶ target))
    (family : D ⥤ Type u) (arguments : (world : D) → ArgumentCoding (family.obj world))
    {point target : D} (first second : point ⟶ target) (different : first ≠ second)
    (argument : family.obj target) :
    (contextual worlds arrows family arguments point).reading ⟨⟨target, first⟩, argument⟩ ≠
      (contextual worlds arrows family arguments point).reading ⟨⟨target, second⟩, argument⟩ := by
  intro same
  have pairs := (contextual_reading worlds arrows family arguments point
      (⟨⟨target, first⟩, argument⟩ : (Future.domain family point).Elements)).symm.trans
    (same.trans (contextual_reading worlds arrows family arguments point
      (⟨⟨target, second⟩, argument⟩ : (Future.domain family point).Elements)))
  exact different ((arrows point target).injective (HSet.kpair_inj.mp (HSet.kpair_inj.mp pairs).2).1)

end ArgumentCoding

namespace LabelledContextPaths

/-- Context length is separate from the labelled history of an extension. -/
structure World where
  length : Nat
  deriving DecidableEq

instance category : Category World where
  Hom first second := {path : List Nat // first.length + path.length = second.length}
  id _ := ⟨[], Nat.add_zero _⟩
  comp first second := ⟨first.1 ++ second.1, by
    rw [List.length_append, ← Nat.add_assoc, first.2, second.2]⟩
  id_comp _ := Subtype.ext (List.nil_append _)
  comp_id _ := Subtype.ext (List.append_nil _)
  assoc _ _ _ := Subtype.ext (List.append_assoc _ _ _)

def worlds : ArgumentCoding World where
  graph world := OutcomeLabels.chainGraph world.length
  injective := by
    rintro ⟨first⟩ ⟨second⟩ same
    dsimp only at same
    rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at same
    exact congrArg World.mk (OutcomeLabels.chainValue_injective same)

def arrows (first second : World) : ArgumentCoding (first ⟶ second) :=
  ((ArgumentCoding.ofEncodable Nat).lists).subtype _

def arguments : World ⥤ Type where
  obj world := Fin (world.length + 1)
  map {first second} step := TypeCat.ofHom fun argument =>
    ⟨argument.val, by
      have grows : first.length ≤ second.length :=
        (Nat.le_add_right first.length step.val.length).trans_eq step.property
      exact Nat.lt_of_lt_of_le argument.isLt (Nat.add_le_add_right grows 1)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def argumentCoding (world : World) : ArgumentCoding (arguments.obj world) where
  graph argument := OutcomeLabels.chainGraph argument.val
  injective := by
    intro first second same
    dsimp only at same
    rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at same
    exact Fin.ext (OutcomeLabels.chainValue_injective same)

def coding (point : World) : ArgumentCoding (Future.domain arguments point).Elements :=
  ArgumentCoding.contextual worlds arrows arguments argumentCoding point

def initial : World := ⟨0⟩
def next : World := ⟨1⟩
def two : World := ⟨2⟩

def extension (label : Nat) : initial ⟶ next := ⟨[label], rfl⟩
def laterExtension (label : Nat) : next ⟶ two := ⟨[label], rfl⟩

def index (label : Nat) : (Future.domain arguments initial).Elements :=
  ⟨⟨next, extension label⟩, ⟨0, Nat.zero_lt_succ 1⟩⟩

/-- Infinitely many parallel context arrows have distinct material readings. -/
theorem reading_injective : Function.Injective (fun label => (coding initial).reading (index label)) := by
  intro first second same
  have indices := (coding initial).injective same
  have futures := congrArg (fun value : (Future.domain arguments initial).Elements => value.1) indices
  have paths : [first] = [second] := congrArg (fun value : Future.Objects initial => value.2.val) futures
  exact List.singleton_injective paths

theorem endpoint_argument_erasure_not_injective :
    ¬ Function.Injective (fun value : (Future.domain arguments initial).Elements =>
      (⟨value.1.1, value.2⟩ : arguments.Elements)) := by
  intro injective
  have same := injective (a₁ := index 0) (a₂ := index 1) rfl
  have impossible : (0 : Nat) = 1 := reading_injective (congrArg (coding initial).reading same)
  exact Nat.zero_ne_one impossible

theorem composition_retains_order (first second : Nat) :
    (extension first ≫ laterExtension second).val = [first, second] := rfl

theorem reversed_histories_distinguished {first second : Nat} (different : first ≠ second) :
    (arrows initial two).reading (extension first ≫ laterExtension second) ≠
      (arrows initial two).reading (extension second ≫ laterExtension first) := by
  intro same
  have paths := congrArg Subtype.val ((arrows initial two).injective same)
  change [first, second] = [second, first] at paths
  exact different (List.cons.inj paths).1

def newlyAvailable : arguments.obj next := ⟨1, by decide⟩

theorem newlyAvailable_not_from_initial (label : Nat) :
    ¬ ∃ argument : arguments.obj initial, arguments.map (extension label) argument = newlyAvailable := by
  rintro ⟨argument, same⟩
  have value : argument.val = 1 := congrArg Fin.val same
  have bound := argument.isLt
  change argument.val < 1 at bound
  rw [value] at bound
  exact Nat.lt_irrefl 1 bound

end LabelledContextPaths

end Mettapedia.TypeTheory.MaterialSets.Hypersets
