import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphSetOperations

/-!
# Finite ordinals and infinity with matching receipts

All constructors have original-small node carriers. The infinite graph
is the disjoint union of the finite ordinal graphs. Its empty member and
successor closure are constructed from actual membership receipts.
No erased witness is selected.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedSetConstructors

open GraphBisimulationRealizers GraphSetRealization GraphSetOperations

universe u

def singleton (value : Graph.{u}) : Graph.{u} :=
  AccessiblePointedGraph.sup (fun _ : PUnit.{u+1} => value)

def singletonIntro {value child : Graph.{u}} (same : Equal child value) :
    Member child (singleton value) := Sup.intro _ PUnit.unit same

def singletonEliminate {value child : Graph.{u}} (proof : Member child (singleton value)) :
    Equal child value := (Sup.eliminate _ proof).2

def successor (value : Graph.{u}) : Graph.{u} :=
  AccessiblePointedGraph.sup (fun index : Child value.edge value.point ⊕ PUnit.{u+1} =>
    match index with
    | .inl child => value.repoint child.val
    | .inr _ => value)

def successorOld {child value : Graph.{u}} (proof : Member child value) :
    Member child (successor value) := Sup.intro _ (.inl proof.1) proof.2

def successorSelf {child value : Graph.{u}} (same : Equal child value) :
    Member child (successor value) := Sup.intro _ (.inr PUnit.unit) same

def successorEliminate {child value : Graph.{u}} (proof : Member child (successor value)) :
    Member child value ⊕ Equal child value :=
  match Sup.eliminate _ proof with
  | ⟨.inl receipt, same⟩ => .inl ⟨receipt, same⟩
  | ⟨.inr _, same⟩ => .inr same

def successorCongruence {first second : Graph.{u}} (same : Equal first second) :
    Equal (successor first) (successor second) :=
  extensionality
    (fun _ proof => match successorEliminate proof with
      | .inl old => successorOld (Member.transportParent same old)
      | .inr self => successorSelf (self.trans same))
    (fun _ proof => match successorEliminate proof with
      | .inl old => successorOld (Member.transportParent same.symm old)
      | .inr self => successorSelf (self.trans same.symm))

/-- The index `i : Fin n` supplies the strictly smaller recursive call. -/
def ordinal (bound : Nat) : Graph.{u} :=
  AccessiblePointedGraph.sup (fun index : ULift.{u} (Fin bound) => ordinal index.down.val)
termination_by bound

def ordinalIntro {value : Graph.{u}} {index bound : Nat} (small : index < bound)
    (same : Equal value (ordinal index)) : Member value (ordinal bound) := by
  unfold ordinal
  exact Sup.intro _ ⟨⟨index, small⟩⟩ same

def ordinalEliminate {value : Graph.{u}} (bound : Nat) (proof : Member value (ordinal bound)) :
    Σ index : Fin bound, Equal value (ordinal index.val) := by
  unfold ordinal at proof
  exact let decoded := Sup.eliminate _ proof; ⟨decoded.1.down, decoded.2⟩

def ordinalZero : Equal (ordinal 0) AccessiblePointedGraph.empty :=
  extensionality
    (fun _ proof => False.elim (Nat.not_lt_zero _ (ordinalEliminate 0 proof).1.isLt))
    (fun _ proof => PEmpty.elim (emptyEliminate proof))

def ordinalSuccessor (bound : Nat) : Equal (ordinal (bound+1)) (successor (ordinal bound)) :=
  extensionality
    (fun _ proof =>
      let decoded := ordinalEliminate (bound+1) proof
      if smaller : decoded.1.val < bound then
        successorOld (ordinalIntro smaller decoded.2)
      else
        let same : decoded.1.val = bound := by omega
        successorSelf (same ▸ decoded.2))
    (fun _ proof => match successorEliminate proof with
      | .inl old =>
          let decoded := ordinalEliminate bound old
          ordinalIntro (Nat.lt_trans decoded.1.isLt (Nat.lt_succ_self bound)) decoded.2
      | .inr self => ordinalIntro (Nat.lt_succ_self bound) self)

def infinity : Graph.{u} :=
  AccessiblePointedGraph.sup (fun index : ULift.{u} Nat => ordinal index.down)

def infinityIntro {value : Graph.{u}} (index : Nat) (same : Equal value (ordinal index)) :
    Member value infinity := Sup.intro _ ⟨index⟩ same

def infinityEliminate {value : Graph.{u}} (proof : Member value infinity) :
    Σ index : Nat, Equal value (ordinal index) :=
  let decoded := Sup.eliminate _ proof
  ⟨decoded.1.down, decoded.2⟩

def infinityEmpty : Member AccessiblePointedGraph.empty infinity :=
  infinityIntro 0 ordinalZero.symm

def infinitySuccessor {value : Graph.{u}} (proof : Member value infinity) :
    Member (successor value) infinity :=
  let decoded := infinityEliminate proof
  infinityIntro (decoded.1+1)
    ((successorCongruence decoded.2).trans (ordinalSuccessor decoded.1).symm)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedSetConstructors
