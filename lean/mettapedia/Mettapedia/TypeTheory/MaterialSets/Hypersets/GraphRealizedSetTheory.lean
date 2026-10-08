import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedSetConstructors
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphBoundedFormulaRealization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedFullness
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedDeduction
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSetTheory

/-!
# A realized constructive material theory at the original graph bound

The adopted first-order sentences are stated separately from their
interpretation. Empty set, pairing, union, infinity and extensionality
have explicit realizers. Separation is bounded; Strong Collection allows
arbitrary first-order bodies. Subset Collection uses a small carrier of
receipt functions and one collecting set independent of the relation's
parameter. Powerset, set induction, Choice and equality reflection are
not adopted. Graph anti-foundation has its separate constructive theorem.

Logical derivations retain hypothesis occurrences and compute witnesses.
This is Type-valued realization; it is not a selector from erased Prop
existence and does not imply a global choice function on material sets.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedSetTheory

open GraphSetRealization GraphFormulaRealization GraphRealizedSetConstructors
open GraphRealizedDeduction
open ContextualMaterialLogic (substitute)
open ContextualMaterialFormulaSemantics
open ContextualMaterialSetTheory (equivalent emptyAxiom pairingAxiom unionAxiom infinityAxiom
  extensionalityAxiom separationAxiom strongCollectionAxiom)

universe u

def subsetPremiseIndices {count : Nat} : Fin (count+3) → Fin (count+6) :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (fun index => index.succ.succ.succ.succ.succ.succ)))

def subsetForwardIndices {count : Nat} : Fin (count+3) → Fin (count+7) :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 3 (fun index => index.succ.succ.succ.succ.succ.succ.succ)))

def subsetBackwardIndices {count : Nat} : Fin (count+3) → Fin (count+7) :=
  Fin.cases 1 (Fin.cases 0 (Fin.cases 3 (fun index => index.succ.succ.succ.succ.succ.succ.succ)))

/-- The outer collecting set is chosen before the parameter. -/
def subsetCollectionAxiom {count : Nat} (body : Formula (count+3)) : Formula count :=
  .all (.all (.exist (.all
    (.imply
      (.all (.imply (.member 0 4)
        (.exist (.both (.member 0 4) (substitute subsetPremiseIndices body)))))
      (.exist (.both (.member 0 2)
        (.both
          (.all (.imply (.member 0 5)
            (.exist (.both (.member 0 2) (substitute subsetForwardIndices body)))))
          (.all (.imply (.member 0 1)
            (.exist (.both (.member 0 6) (substitute subsetBackwardIndices body))))))))))))

/-- Adoption records are syntax data, not host axioms. -/
inductive Axiom : {count : Nat} → Formula count → Type where
  | empty : Axiom emptyAxiom
  | pairing : Axiom pairingAxiom
  | union : Axiom unionAxiom
  | infinity : Axiom infinityAxiom
  | extensionality : Axiom extensionalityAxiom
  | boundedSeparation {count : Nat} (body : GraphBoundedFormulaRealization.BoundedFormula (count+1)) :
      Axiom (separationAxiom (GraphBoundedFormulaRealization.toFormula body))
  | strongCollection {count : Nat} (body : Formula (count+2)) : Axiom (strongCollectionAxiom body)
  | subsetCollection {count : Nat} (body : Formula (count+3)) : Axiom (subsetCollectionAxiom body)
  | substitution {count other : Nat} {body : Formula count} (indices : Fin count → Fin other)
      (adopted : Axiom body) : Axiom (substitute indices body)

theorem discardTwo {count : Nat} (environment : Environment.{u} count)
    (first second head : Graph.{u}) :
    extend head (extend second (extend first environment)) ∘ behindHeadTwo = extend head environment := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

theorem discardOneAfterTwo {count : Nat} (environment : Environment.{u} count)
    (inserted child witness : Graph.{u}) :
    extend witness (extend child (extend inserted environment)) ∘ behindTwoOne =
      extend witness (extend child environment) := by
  funext index
  exact Fin.cases rfl (fun remaining => Fin.cases rfl (fun _ => rfl) remaining) index

theorem discardTwoAfterTwo {count : Nat} (environment : Environment.{u} count)
    (first second child witness : Graph.{u}) :
    extend witness (extend child (extend second (extend first environment))) ∘ behindTwoTwo =
      extend witness (extend child environment) := by
  funext index
  exact Fin.cases rfl (fun remaining => Fin.cases rfl (fun _ => rfl) remaining) index

theorem swapDiscardTwoAfterTwo {count : Nat} (environment : Environment.{u} count)
    (first second witness child : Graph.{u}) :
    extend child (extend witness (extend second (extend first environment))) ∘ swappedBehindTwoTwo =
      extend witness (extend child environment) := by
  funext index
  exact Fin.cases rfl (fun remaining => Fin.cases rfl (fun _ => rfl) remaining) index

def emptyLaw (environment : Environment.{u} 0) : realize emptyAxiom environment :=
  ⟨AccessiblePointedGraph.empty, fun _ member => PEmpty.elim (emptyEliminate member.down)⟩

def pairingLaw (environment : Environment.{u} 0) : realize pairingAxiom environment :=
  fun first second => ⟨GraphSetOperations.pair first second, fun _value =>
    ⟨fun member => match GraphSetOperations.pairEliminate member.down with
      | .inl same => .inl ⟨same⟩
      | .inr same => .inr ⟨same⟩,
     fun proof => match proof with
      | .inl same => ⟨Member.transportChild same.down.symm (GraphSetOperations.pairFirst first second)⟩
      | .inr same => ⟨Member.transportChild same.down.symm (GraphSetOperations.pairSecond first second)⟩⟩⟩

def unionLaw (environment : Environment.{u} 0) : realize unionAxiom environment :=
  fun parent => ⟨GraphSetOperations.union parent, fun _ =>
    ⟨fun member => let decoded := GraphSetOperations.unionEliminate member.down
       ⟨decoded.1, ⟨⟨decoded.2.1⟩, ⟨decoded.2.2⟩⟩⟩,
     fun proof => ⟨GraphSetOperations.unionIntro proof.2.1.down proof.2.2.down⟩⟩⟩

def infinityLaw (environment : Environment.{u} 0) : realize infinityAxiom environment :=
  ⟨infinity,
    ⟨⟨AccessiblePointedGraph.empty, ⟨fun _ proof => PEmpty.elim (emptyEliminate proof.down), ⟨infinityEmpty⟩⟩⟩,
      fun value member => ⟨successor value,
        ⟨fun _ =>
          ⟨fun proof => match successorEliminate proof.down with
            | .inl old => .inl ⟨old⟩
            | .inr self => .inr ⟨self⟩,
           fun proof => match proof with
            | .inl old => ⟨successorOld old.down⟩
            | .inr self => ⟨successorSelf self.down⟩⟩,
         ⟨infinitySuccessor member.down⟩⟩⟩⟩⟩

def extensionalityLaw (environment : Environment.{u} 2) : realize extensionalityAxiom environment :=
  fun agreement => ⟨extensionality (fun value member => (agreement value).1 ⟨member⟩ |>.down)
    (fun value member => (agreement value).2 ⟨member⟩ |>.down)⟩

def separationLaw {count : Nat} (body : GraphBoundedFormulaRealization.BoundedFormula (count+1))
    (environment : Environment.{u} count) : realize (separationAxiom (GraphBoundedFormulaRealization.toFormula body)) environment := by
  intro parent
  let separated := GraphBoundedFormulaRealization.separation body environment parent
  refine ⟨separated, ?_⟩
  intro value
  have bodySame :
      realize (substitute behindHeadTwo (GraphBoundedFormulaRealization.toFormula body)) (extend value (extend separated (extend parent environment))) =
        realize (GraphBoundedFormulaRealization.toFormula body) (extend value environment) := by
    rw [realize_substitution, discardTwo]
  constructor
  · intro member
    let decoded := GraphBoundedFormulaRealization.separationEliminate body environment member.down
    exact ⟨⟨decoded.1⟩, bodySame.symm ▸ GraphBoundedFormulaRealization.toFull body (extend value environment) decoded.2⟩
  · intro proof
    exact ⟨GraphBoundedFormulaRealization.separationIntro body environment proof.1.down
      (GraphBoundedFormulaRealization.toFull.fromFull body (extend value environment) (bodySame ▸ proof.2))⟩

def strongCollectionLaw {count : Nat} (body : Formula (count+2)) (environment : Environment.{u} count) :
    realize (strongCollectionAxiom body) environment := by
  intro parent premise
  let input : ∀ value : Graph.{u}, Member value parent → GraphRealizedCollection.Witness body environment value :=
    fun value member =>
      let witness := premise value ⟨member⟩
      ⟨witness.1, (by
        have same : realize (substitute behindTwoOne body)
            (extend witness.1 (extend value (extend parent environment))) =
              realize body (extend witness.1 (extend value environment)) := by
          rw [realize_substitution, discardOneAfterTwo]
        exact same ▸ witness.2)⟩
  let packet := GraphRealizedCollection.strongCollection body environment parent input
  refine ⟨packet.1, ?_, ?_⟩
  · intro value member
    let witness := packet.2.1 value member.down
    refine ⟨witness.1, ⟨⟨witness.2.1⟩, ?_⟩⟩
    have same : realize (substitute behindTwoTwo body)
        (extend witness.1 (extend value (extend packet.1 (extend parent environment)))) =
          realize body (extend witness.1 (extend value environment)) := by
      rw [realize_substitution, discardTwoAfterTwo]
    exact same.symm ▸ witness.2.2
  · intro result member
    let witness := packet.2.2 result member.down
    refine ⟨witness.1, ⟨⟨witness.2.1⟩, ?_⟩⟩
    have same : realize (substitute swappedBehindTwoTwo body)
        (extend witness.1 (extend result (extend packet.1 (extend parent environment)))) =
          realize body (extend result (extend witness.1 environment)) := by
      rw [realize_substitution, swapDiscardTwoAfterTwo]
    exact same.symm ▸ witness.2.2

theorem subsetPremiseEnvironment {count : Nat} (environment : Environment.{u} count)
    (source target family parameter value result : Graph.{u}) :
    extend result (extend value (extend parameter (extend family (extend target (extend source environment))))) ∘
        subsetPremiseIndices = extend result (extend value (extend parameter environment)) := by
  funext index
  exact Fin.cases rfl (fun second => Fin.cases rfl (fun third => Fin.cases rfl (fun _ => rfl) third) second) index

theorem subsetForwardEnvironment {count : Nat} (environment : Environment.{u} count)
    (source target family parameter collector value result : Graph.{u}) :
    extend result (extend value (extend collector (extend parameter (extend family (extend target (extend source environment)))))) ∘
        subsetForwardIndices = extend result (extend value (extend parameter environment)) := by
  funext index
  exact Fin.cases rfl (fun second => Fin.cases rfl (fun third => Fin.cases rfl (fun _ => rfl) third) second) index

theorem subsetBackwardEnvironment {count : Nat} (environment : Environment.{u} count)
    (source target family parameter collector result value : Graph.{u}) :
    extend value (extend result (extend collector (extend parameter (extend family (extend target (extend source environment)))))) ∘
        subsetBackwardIndices = extend result (extend value (extend parameter environment)) := by
  funext index
  exact Fin.cases rfl (fun second => Fin.cases rfl (fun third => Fin.cases rfl (fun _ => rfl) third) second) index

def subsetCollectionLaw {count : Nat} (body : Formula (count+3)) (environment : Environment.{u} count) :
    realize (subsetCollectionAxiom body) environment := by
  intro source target
  let family := GraphRealizedFullness.fullness source target
  refine ⟨family, ?_⟩
  intro parameter premise
  let input : GraphRealizedFullness.Premise body (extend parameter environment) source target :=
    fun value member =>
      let witness := premise value ⟨member⟩
      ⟨witness.1, witness.2.1.down, (by
        have same : realize (substitute subsetPremiseIndices body)
            (extend witness.1 (extend value (extend parameter (extend family (extend target (extend source environment)))))) =
              realize body (extend witness.1 (extend value (extend parameter environment))) := by
          rw [realize_substitution, subsetPremiseEnvironment]
        exact same ▸ witness.2.2)⟩
  let packet := GraphRealizedFullness.subsetCollection body (extend parameter environment) source target input
  refine ⟨packet.1, ⟨⟨packet.2.1⟩, ?_, ?_⟩⟩
  · intro value member
    let witness := packet.2.2.1 value member.down
    refine ⟨witness.1, ⟨⟨witness.2.1⟩, ?_⟩⟩
    have same : realize (substitute subsetForwardIndices body)
        (extend witness.1 (extend value (extend packet.1 (extend parameter (extend family (extend target (extend source environment))))))) =
          realize body (extend witness.1 (extend value (extend parameter environment))) := by
      rw [realize_substitution, subsetForwardEnvironment]
    exact same.symm ▸ witness.2.2
  · intro result member
    let witness := packet.2.2.2.1 result member.down
    refine ⟨witness.1, ⟨⟨witness.2.1⟩, ?_⟩⟩
    have same : realize (substitute subsetBackwardIndices body)
        (extend witness.1 (extend result (extend packet.1 (extend parameter (extend family (extend target (extend source environment))))))) =
          realize body (extend result (extend witness.1 (extend parameter environment))) := by
      rw [realize_substitution, subsetBackwardEnvironment]
    exact same.symm ▸ witness.2.2

/-- Each independently adopted law has a computed realizer at every
assignment, including substituted schema instances. -/
def validate : {count : Nat} → {formula : Formula count} → Axiom formula →
    (environment : Environment.{u} count) → realize formula environment
  | _, _, .empty, environment => emptyLaw environment
  | _, _, .pairing, environment => pairingLaw environment
  | _, _, .union, environment => unionLaw environment
  | _, _, .infinity, environment => infinityLaw environment
  | _, _, .extensionality, environment => extensionalityLaw environment
  | _, _, .boundedSeparation body, environment => separationLaw body environment
  | _, _, .strongCollection body, environment => strongCollectionLaw body environment
  | _, _, .subsetCollection body, environment => subsetCollectionLaw body environment
  | _, _, .substitution indices previous, environment =>
      (realize_substitution indices _ environment).symm ▸ validate previous (environment ∘ indices)

/-- An actual deduction from adopted instances computes its conclusion. -/
def derivationRealizer {count : Nat} {assumptions : List (Formula count)} {conclusion : Formula count}
    (proof : Proof assumptions conclusion) (adopted : (index : Fin assumptions.length) → Axiom assumptions[index.val])
    (environment : Environment.{u} count) : realize conclusion environment :=
  interpret proof environment (fun index => validate (adopted index) environment)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedSetTheory
