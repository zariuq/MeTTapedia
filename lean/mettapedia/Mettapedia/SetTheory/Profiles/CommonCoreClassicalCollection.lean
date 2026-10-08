import Mettapedia.SetTheory.Profiles.CommonCoreClassical
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ClassicalHypersetCollection

/-!
# Semantic Collection extensions of the two concrete classical models

Strong Collection is constructed in `ZFSet` by selecting witnesses over the
small member carrier, and in `HSet` by the existing small-graph construction.
Those two endpoints use host `Classical.choice`. The object-language proof
calculus gains no choice rule or choice operator.

Subset Collection uses each target's actual power set and Separation. Its
outer collecting family is chosen before the arbitrary formula parameter.
These are validations of the explicit extension calculus, not derivations
of its axioms from the common core or from a native HOTG seed presentation.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.CommonCoreClassicalCollection

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic (Formula substitute)
open ContextualMaterialSetTheory
open ContextualMaterialFormulaSemantics
open GraphRealizedSetTheory (subsetCollectionAxiom subsetPremiseIndices subsetForwardIndices subsetBackwardIndices)
open Mettapedia.SetTheory.CarveOuts.Sites (Tarski)
open CommonCoreClassicalLogic (substitute_iff proof_sound)
open CommonCoreClassical

universe u

variable {S : Type u} {member : S → S → Prop}

def StrongCollection (member : S → S → Prop) : Prop :=
  ∀ parent (relation : S → S → Prop),
    (∀ child, member child parent → ∃ witness, relation child witness) →
    ∃ collected,
      (∀ child, member child parent → ∃ witness, member witness collected ∧ relation child witness) ∧
      (∀ witness, member witness collected → ∃ child, member child parent ∧ relation child witness)

structure PowerOperation (S : Type u) (member : S → S → Prop) where
  power : S → S
  specification : ∀ parent child, member child (power parent) ↔
    ∀ value, member value child → member value parent

def prepend {count : Nat} (value : S) (environment : Fin count → S) : Fin (count+1) → S :=
  Fin.cases value environment

theorem read_discardOne {count : Nat} (body : Formula (count+2)) (environment : Fin count → S)
    (parent child witness : S) :
    Tarski member (substitute behindTwoOne body)
      (prepend witness (prepend child (prepend parent environment))) ↔
    Tarski member body (prepend witness (prepend child environment)) := by
  apply (substitute_iff member behindTwoOne body _).trans
  apply Iff.of_eq
  apply congrArg (Tarski member body)
  funext index
  exact Fin.cases rfl (fun next => Fin.cases rfl (fun _ => rfl) next) index

theorem read_discardTwo {count : Nat} (body : Formula (count+2)) (environment : Fin count → S)
    (parent collected child witness : S) :
    Tarski member (substitute behindTwoTwo body)
      (prepend witness (prepend child (prepend collected (prepend parent environment)))) ↔
    Tarski member body (prepend witness (prepend child environment)) := by
  apply (substitute_iff member behindTwoTwo body _).trans
  apply Iff.of_eq
  apply congrArg (Tarski member body)
  funext index
  exact Fin.cases rfl (fun next => Fin.cases rfl (fun _ => rfl) next) index

theorem read_swapDiscardTwo {count : Nat} (body : Formula (count+2)) (environment : Fin count → S)
    (parent collected witness child : S) :
    Tarski member (substitute swappedBehindTwoTwo body)
      (prepend child (prepend witness (prepend collected (prepend parent environment)))) ↔
    Tarski member body (prepend witness (prepend child environment)) := by
  apply (substitute_iff member swappedBehindTwoTwo body _).trans
  apply Iff.of_eq
  apply congrArg (Tarski member body)
  funext index
  exact Fin.cases rfl (fun next => Fin.cases rfl (fun _ => rfl) next) index

theorem strongCollection_valid (collection : StrongCollection member) {count : Nat}
    (body : Formula (count+2)) (environment : Fin count → S) :
    Tarski member (strongCollectionAxiom body) environment := by
  intro parent premise
  let relation := fun child witness => Tarski member body (prepend witness (prepend child environment))
  have total : ∀ child, member child parent → ∃ witness, relation child witness := by
    intro child belongs
    obtain ⟨witness, related⟩ := premise child belongs
    exact ⟨witness, (read_discardOne body environment parent child witness).mp related⟩
  obtain ⟨collected, forward, backward⟩ := collection parent relation total
  refine ⟨collected, ?_, ?_⟩
  · intro child belongs
    obtain ⟨witness, included, related⟩ := forward child belongs
    exact ⟨witness, included, (read_discardTwo body environment parent collected child witness).mpr related⟩
  · intro witness included
    obtain ⟨child, belongs, related⟩ := backward witness included
    exact ⟨child, belongs, (read_swapDiscardTwo body environment parent collected witness child).mpr related⟩

theorem read_subsetPremise {count : Nat} (body : Formula (count+3)) (environment : Fin count → S)
    (source target family parameter child witness : S) :
    Tarski member (substitute subsetPremiseIndices body)
      (prepend witness (prepend child (prepend parameter (prepend family (prepend target (prepend source environment)))))) ↔
    Tarski member body (prepend witness (prepend child (prepend parameter environment))) := by
  apply (substitute_iff member subsetPremiseIndices body _).trans
  apply Iff.of_eq
  apply congrArg (Tarski member body)
  funext index
  exact Fin.cases rfl (fun next => Fin.cases rfl (fun last => Fin.cases rfl (fun _ => rfl) last) next) index

theorem read_subsetForward {count : Nat} (body : Formula (count+3)) (environment : Fin count → S)
    (source target family parameter collected child witness : S) :
    Tarski member (substitute subsetForwardIndices body)
      (prepend witness (prepend child (prepend collected (prepend parameter (prepend family (prepend target (prepend source environment))))))) ↔
    Tarski member body (prepend witness (prepend child (prepend parameter environment))) := by
  apply (substitute_iff member subsetForwardIndices body _).trans
  apply Iff.of_eq
  apply congrArg (Tarski member body)
  funext index
  exact Fin.cases rfl (fun next => Fin.cases rfl (fun last => Fin.cases rfl (fun _ => rfl) last) next) index

theorem read_subsetBackward {count : Nat} (body : Formula (count+3)) (environment : Fin count → S)
    (source target family parameter collected witness child : S) :
    Tarski member (substitute subsetBackwardIndices body)
      (prepend child (prepend witness (prepend collected (prepend parameter (prepend family (prepend target (prepend source environment))))))) ↔
    Tarski member body (prepend witness (prepend child (prepend parameter environment))) := by
  apply (substitute_iff member subsetBackwardIndices body _).trans
  apply Iff.of_eq
  apply congrArg (Tarski member body)
  funext index
  exact Fin.cases rfl (fun next => Fin.cases rfl (fun last => Fin.cases rfl (fun _ => rfl) last) next) index

/-- The power set of the target is fixed before the relation's parameter.
The selected relation image is then formed by actual Separation. -/
theorem subsetCollection_valid (operations : Operations S member) (powers : PowerOperation S member)
    {count : Nat} (body : Formula (count+3)) (environment : Fin count → S) :
    Tarski member (subsetCollectionAxiom body) environment := by
  intro source target
  refine ⟨powers.power target, ?_⟩
  intro parameter premise
  let relation := fun child witness =>
    Tarski member body (prepend witness (prepend child (prepend parameter environment)))
  let selected := fun witness => ∃ child, member child source ∧ relation child witness
  let collected := operations.separate selected target
  have collected_spec : ∀ witness, member witness collected ↔ member witness target ∧ selected witness :=
    operations.separate_spec selected target
  refine ⟨collected, (powers.specification target collected).mpr
    (fun witness included => ((collected_spec witness).mp included).1), ?_, ?_⟩
  · intro child belongs
    obtain ⟨witness, inTarget, related⟩ := premise child belongs
    have actual : relation child witness :=
      (read_subsetPremise body environment source target (powers.power target) parameter child witness).mp related
    refine ⟨witness, (collected_spec witness).mpr ⟨inTarget, child, belongs, actual⟩, ?_⟩
    exact (read_subsetForward body environment source target (powers.power target) parameter collected child witness).mpr actual
  · intro witness included
    obtain ⟨child, belongs, related⟩ := ((collected_spec witness).mp included).2
    exact ⟨child, belongs,
      (read_subsetBackward body environment source target (powers.power target) parameter collected witness child).mpr related⟩

/-- This host-level construction selects over the genuinely small member
carrier of one set. It asserts no object-language choice function. -/
theorem wellFounded_strongCollection : StrongCollection (fun (child parent : ZFSet.{u}) => child ∈ parent) := by
  classical
  intro parent relation total
  let chosen : parent → ZFSet.{u} := fun child => Classical.choose (total child.val child.property)
  have related : ∀ child : parent, relation child.val (chosen child) := fun child =>
    Classical.choose_spec (total child.val child.property)
  refine ⟨ZFSet.range chosen, ?_, ?_⟩
  · intro child belongs
    exact ⟨chosen ⟨child, belongs⟩,
      ZFSet.mem_range_self (f := chosen) (⟨child, belongs⟩ : parent), related ⟨child, belongs⟩⟩
  · intro witness included
    obtain ⟨child, rfl⟩ := ZFSet.mem_range.mp included
    exact ⟨child.val, child.property, related child⟩

theorem hyperset_strongCollection : StrongCollection (fun (child parent : HSet.{u}) => child ∈ parent) :=
  ClassicalHypersetCollection.strongCollection

def wellFoundedPower : PowerOperation ZFSet.{u} (· ∈ ·) where
  power := ZFSet.powerset
  specification _ _ := ZFSet.mem_powerset

def hypersetPower : PowerOperation HSet.{u} (· ∈ ·) where
  power := HSet.powerset
  specification _ _ := HSet.mem_powerset

theorem wellFounded_subsetCollection_valid {count : Nat} (body : Formula (count+3))
    (environment : Fin count → ZFSet.{u}) :
    Tarski (· ∈ ·) (subsetCollectionAxiom body) environment :=
  subsetCollection_valid wellFoundedOperations wellFoundedPower body environment

theorem hyperset_subsetCollection_valid {count : Nat} (body : Formula (count+3))
    (environment : Fin count → HSet.{u}) :
    Tarski (· ∈ ·) (subsetCollectionAxiom body) environment :=
  subsetCollection_valid hypersetOperations hypersetPower body environment

theorem wellFounded_strongCollection_valid {count : Nat} (body : Formula (count+2))
    (environment : Fin count → ZFSet.{u}) :
    Tarski (· ∈ ·) (strongCollectionAxiom body) environment :=
  strongCollection_valid wellFounded_strongCollection body environment

theorem hyperset_strongCollection_valid {count : Nat} (body : Formula (count+2))
    (environment : Fin count → HSet.{u}) :
    Tarski (· ∈ ·) (strongCollectionAxiom body) environment :=
  strongCollection_valid hyperset_strongCollection body environment

theorem validateExtension (operations : Operations S member) (powers : PowerOperation S member)
    (collection : StrongCollection member) {count : Nat} {body : Formula count}
    (adopted : CommonCore.Extension body) (environment : Fin count → S) :
    Tarski member body environment := by
  induction adopted with
  | core adopted => exact validate operations adopted environment
  | strongCollection body => exact strongCollection_valid collection body environment
  | subsetCollection body => exact subsetCollection_valid operations powers body environment
  | substitution indices _ inductionHypothesis =>
      exact (substitute_iff member indices _ environment).mpr (inductionHypothesis _)

theorem interpretExtension (operations : Operations S member) (powers : PowerOperation S member)
    (collection : StrongCollection member) {count : Nat} {body : Formula count}
    (derivation : CommonCore.ExtensionDerivation body) (environment : Fin count → S) :
    Tarski member body environment :=
  proof_sound member derivation.proof environment
    (fun index => validateExtension operations powers collection (derivation.adopted index) environment)

theorem wellFounded_extension {count : Nat} {body : Formula count}
    (derivation : CommonCore.ExtensionDerivation body) (environment : Fin count → ZFSet.{u}) :
    Tarski (· ∈ ·) body environment :=
  interpretExtension wellFoundedOperations wellFoundedPower wellFounded_strongCollection derivation environment

theorem hyperset_extension {count : Nat} {body : Formula count}
    (derivation : CommonCore.ExtensionDerivation body) (environment : Fin count → HSet.{u}) :
    Tarski (· ∈ ·) body environment :=
  interpretExtension hypersetOperations hypersetPower hyperset_strongCollection derivation environment

end Mettapedia.SetTheory.Profiles.CommonCoreClassicalCollection
