import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedMemberGraphs

/-!
# Same-bound operations on actual presented material types

A presented material type has an actual graph and a constructed comparison
between its material members and its small semantic carrier. Its term graphs
are constructed from all occurrences below that graph. Products collect
authored function graphs over the small semantic domain; their decoder uses
bounded fibre separation and union, rather than selecting a section witness.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

structure PresentedType (T : Type u) : Type (u + 1) where
  graph : AccessiblePointedGraph.{u}
  decode : {value : HSet.{u} // value ∈ HSet.mk graph} ≃ T

namespace PresentedType

variable {A : Type u}

def carrier (model : PresentedType A) : HSet.{u} := HSet.mk model.graph

def value (model : PresentedType A) (term : A) : HSet.{u} := (model.decode.symm term).1

theorem value_mem (model : PresentedType A) (term : A) : model.value term ∈ model.carrier :=
  (model.decode.symm term).2

theorem value_injective (model : PresentedType A) : Function.Injective model.value := by
  intro first second same
  exact model.decode.symm.injective (Subtype.ext same)

def termGraph (model : PresentedType A) (term : A) : AccessiblePointedGraph.{u} :=
  model.graph.memberGraph ⟨model.value term, by
    rw [AccessiblePointedGraph.picture_eq_mk]
    exact model.value_mem term⟩

theorem mk_termGraph (model : PresentedType A) (term : A) :
    HSet.mk (model.termGraph term) = model.value term :=
  AccessiblePointedGraph.mk_memberGraph _ _

theorem decode_value (model : PresentedType A) (term : A) :
    model.decode ⟨model.value term, model.value_mem term⟩ = term := model.decode.apply_symm_apply term

theorem value_decode (model : PresentedType A) (member : {value : HSet.{u} // value ∈ model.carrier}) :
    model.value (model.decode member) = member.1 :=
  congrArg Subtype.val (model.decode.symm_apply_apply member)

def transportMember {first second : PresentedType A} (same : first = second)
    (member : {value : HSet.{u} // value ∈ first.carrier}) :
    {value : HSet.{u} // value ∈ second.carrier} :=
  ⟨member.1, congrArg carrier same ▸ member.2⟩

theorem decode_transportMember {first second : PresentedType A} (same : first = second)
    (member : {value : HSet.{u} // value ∈ first.carrier}) :
    second.decode (transportMember same member) = first.decode member := by
  cases same
  rfl

section Products

variable {B : A → Type u} (domain : PresentedType A) (fibres : (a : A) → PresentedType (B a))

def functionGraph (sectionValue : (a : A) → B a) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.sup fun a : A =>
    AccessiblePointedGraph.kpairGraph (domain.termGraph a) ((fibres a).termGraph (sectionValue a))

theorem mem_functionGraph_iff (sectionValue : (a : A) → B a) (row : HSet.{u}) :
    row ∈ HSet.mk (functionGraph domain fibres sectionValue) ↔
      ∃ a, HSet.kpair (domain.value a) ((fibres a).value (sectionValue a)) = row := by
  change row ∈ HSet.range (fun a : A => AccessiblePointedGraph.kpairGraph
    (domain.termGraph a) ((fibres a).termGraph (sectionValue a))) ↔ _
  rw [HSet.mem_range]
  constructor <;> rintro ⟨a, same⟩ <;> refine ⟨a, ?_⟩
  · rw [AccessiblePointedGraph.mk_kpairGraph, mk_termGraph, mk_termGraph] at same
    exact same
  · rw [AccessiblePointedGraph.mk_kpairGraph, mk_termGraph, mk_termGraph]
    exact same

def productGraph : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.sup (functionGraph domain fibres)

theorem mem_productGraph_iff {graphValue : HSet.{u}} :
    graphValue ∈ HSet.mk (productGraph domain fibres) ↔
      ∃ sectionValue : (a : A) → B a, HSet.mk (functionGraph domain fibres sectionValue) = graphValue :=
  HSet.mem_range

def functionMember (sectionValue : (a : A) → B a) :
    {graphValue : HSet.{u} // graphValue ∈ HSet.mk (productGraph domain fibres)} :=
  ⟨HSet.mk (functionGraph domain fibres sectionValue),
    (mem_productGraph_iff domain fibres).mpr ⟨sectionValue, rfl⟩⟩

def evalValue (graphValue : HSet.{u}) (a : A) : HSet.{u} :=
  HSet.sUnion (HSet.sep (fun b => HSet.kpair (domain.value a) b ∈ graphValue) (fibres a).carrier)

theorem evalValue_functionGraph (sectionValue : (a : A) → B a) (a : A) :
    evalValue domain fibres (HSet.mk (functionGraph domain fibres sectionValue)) a =
      (fibres a).value (sectionValue a) := by
  have row : HSet.sep (fun b => HSet.kpair (domain.value a) b ∈
      HSet.mk (functionGraph domain fibres sectionValue)) (fibres a).carrier =
      {(fibres a).value (sectionValue a)} := by
    apply HSet.ext
    intro b
    rw [HSet.mem_sep, mem_functionGraph_iff, HSet.mem_singleton]
    constructor
    · rintro ⟨_, a', same⟩
      have index : a' = a := domain.value_injective (HSet.kpair_inj.mp same).1
      cases index
      exact (HSet.kpair_inj.mp same).2.symm
    · intro same
      exact ⟨same ▸ (fibres a).value_mem (sectionValue a), a, congrArg (HSet.kpair _) same.symm⟩
  exact (congrArg HSet.sUnion row).trans (HSet.sUnion_singleton _)

def evaluate (graphValue : {graphValue : HSet.{u} // graphValue ∈ HSet.mk (productGraph domain fibres)})
    (a : A) : B a :=
  (fibres a).decode ⟨evalValue domain fibres graphValue.1 a, by
    obtain ⟨sectionValue, same⟩ := (mem_productGraph_iff domain fibres).mp graphValue.2
    rw [← same, evalValue_functionGraph]
    exact (fibres a).value_mem (sectionValue a)⟩

theorem evaluate_functionMember (sectionValue : (a : A) → B a) (a : A) :
    evaluate domain fibres (functionMember domain fibres sectionValue) a = sectionValue a := by
  apply (fibres a).decode.symm.injective
  apply Subtype.ext
  exact (value_decode _ _).trans (evalValue_functionGraph domain fibres sectionValue a)

theorem functionMember_evaluate
    (graphValue : {graphValue : HSet.{u} // graphValue ∈ HSet.mk (productGraph domain fibres)}) :
    functionMember domain fibres (evaluate domain fibres graphValue) = graphValue := by
  obtain ⟨sectionValue, same⟩ := (mem_productGraph_iff domain fibres).mp graphValue.2
  have memberSame : graphValue = functionMember domain fibres sectionValue := Subtype.ext same.symm
  rw [memberSame]
  exact congrArg (functionMember domain fibres) (funext (evaluate_functionMember domain fibres sectionValue))

def product : PresentedType ((a : A) → B a) where
  graph := productGraph domain fibres
  decode := {
    toFun := evaluate domain fibres
    invFun := functionMember domain fibres
    left_inv := functionMember_evaluate domain fibres
    right_inv := fun sectionValue => funext (evaluate_functionMember domain fibres sectionValue) }

theorem product_value (sectionValue : (a : A) → B a) :
    (product domain fibres).value sectionValue = HSet.mk (functionGraph domain fibres sectionValue) := rfl

theorem product_application (sectionValue : (a : A) → B a) (a : A) :
    (product domain fibres).decode ((product domain fibres).decode.symm sectionValue) a =
      sectionValue a := evaluate_functionMember domain fibres sectionValue a

theorem product_entry (sectionValue : (a : A) → B a) (a : A) :
    HSet.kpair (domain.value a) ((fibres a).value (sectionValue a)) ∈
      (product domain fibres).value sectionValue :=
  (mem_functionGraph_iff domain fibres sectionValue _).mpr ⟨a, rfl⟩

end Products

theorem value_cast {B : A → Type u} (fibres : (a : A) → PresentedType (B a))
    {first second : A} (same : first = second) (term : B first) :
    (fibres first).value term = (fibres second).value (cast (congrArg B same) term) := by
  cases same
  rfl

section Sums

variable {B : A → Type u} (domain : PresentedType A) (fibres : (a : A) → PresentedType (B a))

def pairTermGraph (term : Sigma B) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.kpairGraph (domain.termGraph term.1) ((fibres term.1).termGraph term.2)

theorem mk_pairTermGraph (term : Sigma B) :
    HSet.mk (pairTermGraph domain fibres term) =
      HSet.kpair (domain.value term.1) ((fibres term.1).value term.2) := by
  rw [pairTermGraph, AccessiblePointedGraph.mk_kpairGraph, mk_termGraph, mk_termGraph]

def sumGraph : AccessiblePointedGraph.{u} := AccessiblePointedGraph.sup (pairTermGraph domain fibres)

theorem mem_sumGraph_iff {pairValue : HSet.{u}} :
    pairValue ∈ HSet.mk (sumGraph domain fibres) ↔
      ∃ term : Sigma B, HSet.kpair (domain.value term.1) ((fibres term.1).value term.2) = pairValue := by
  constructor
  · intro member
    obtain ⟨term, same⟩ := HSet.mem_range.mp member
    exact ⟨term, (mk_pairTermGraph domain fibres term).symm.trans same⟩
  · rintro ⟨term, same⟩
    exact HSet.mem_range.mpr ⟨term, (mk_pairTermGraph domain fibres term).trans same⟩

def pairMember (term : Sigma B) : {pairValue : HSet.{u} // pairValue ∈ HSet.mk (sumGraph domain fibres)} :=
  ⟨HSet.mk (pairTermGraph domain fibres term), HSet.mem_range.mpr ⟨term, rfl⟩⟩

def first (pairValue : {pairValue : HSet.{u} // pairValue ∈ HSet.mk (sumGraph domain fibres)}) : A :=
  domain.decode ⟨HSet.fst pairValue.1, by
    obtain ⟨term, same⟩ := (mem_sumGraph_iff domain fibres).mp pairValue.2
    rw [← same, HSet.fst_kpair]
    exact domain.value_mem term.1⟩

theorem first_pairMember (term : Sigma B) : first domain fibres (pairMember domain fibres term) = term.1 := by
  apply domain.decode.symm.injective
  apply Subtype.ext
  exact (value_decode _ _).trans ((congrArg HSet.fst (mk_pairTermGraph domain fibres term)).trans
    (HSet.fst_kpair _ _))

def second (pairValue : {pairValue : HSet.{u} // pairValue ∈ HSet.mk (sumGraph domain fibres)}) :
    B (first domain fibres pairValue) :=
  (fibres (first domain fibres pairValue)).decode ⟨HSet.snd pairValue.1, by
    obtain ⟨term, same⟩ := HSet.mem_range.mp pairValue.2
    have memberSame : pairValue = pairMember domain fibres term := Subtype.ext same.symm
    cases memberSame
    change HSet.snd (HSet.mk (pairTermGraph domain fibres term)) ∈
      (fibres (first domain fibres (pairMember domain fibres term))).carrier
    rw [mk_pairTermGraph, HSet.snd_kpair, first_pairMember]
    exact (fibres term.1).value_mem term.2⟩

theorem second_pairMember (term : Sigma B) :
    cast (congrArg B (first_pairMember domain fibres term))
      (second domain fibres (pairMember domain fibres term)) = term.2 := by
  apply (fibres term.1).value_injective
  exact (value_cast fibres (first_pairMember domain fibres term) _).symm.trans
    ((value_decode _ _).trans ((congrArg HSet.snd (mk_pairTermGraph domain fibres term)).trans
      (HSet.snd_kpair _ _)))

def projections (pairValue : {pairValue : HSet.{u} // pairValue ∈ HSet.mk (sumGraph domain fibres)}) : Sigma B :=
  ⟨first domain fibres pairValue, second domain fibres pairValue⟩

theorem projections_pairMember (term : Sigma B) :
    projections domain fibres (pairMember domain fibres term) = term :=
  Sigma.ext (first_pairMember domain fibres term)
    ((cast_heq _ _).symm.trans (heq_of_eq (second_pairMember domain fibres term)))

theorem pairMember_projections
    (pairValue : {pairValue : HSet.{u} // pairValue ∈ HSet.mk (sumGraph domain fibres)}) :
    pairMember domain fibres (projections domain fibres pairValue) = pairValue := by
  obtain ⟨term, same⟩ := HSet.mem_range.mp pairValue.2
  have memberSame : pairValue = pairMember domain fibres term := Subtype.ext same.symm
  rw [memberSame, projections_pairMember]

def sum : PresentedType (Sigma B) where
  graph := sumGraph domain fibres
  decode := {
    toFun := projections domain fibres
    invFun := pairMember domain fibres
    left_inv := pairMember_projections domain fibres
    right_inv := projections_pairMember domain fibres }

theorem sum_value (term : Sigma B) :
    (sum domain fibres).value term = HSet.kpair (domain.value term.1) ((fibres term.1).value term.2) :=
  mk_pairTermGraph domain fibres term

end Sums

/-- The empty semantic carrier is represented by the genuinely empty graph. -/
def empty : PresentedType (ULift.{u, 0} Empty) where
  graph := AccessiblePointedGraph.empty
  decode := {
    toFun := fun member => (HSet.notMem_empty member.1 (HSet.mk_empty ▸ member.2)).elim
    invFun := fun term => term.down.elim
    left_inv := fun member => (HSet.notMem_empty member.1 (HSet.mk_empty ▸ member.2)).elim
    right_inv := fun term => term.down.elim }

def unit : PresentedType (ULift.{u, 0} PUnit) where
  graph := AccessiblePointedGraph.singletonGraph AccessiblePointedGraph.empty
  decode := {
    toFun := fun _ => ⟨PUnit.unit⟩
    invFun := fun _ => ⟨∅, by
      rw [AccessiblePointedGraph.mk_singletonGraph, HSet.mk_empty]
      exact HSet.mem_singleton_self _⟩
    left_inv := fun member => Subtype.ext (by
      have bound : member.val = ∅ := by
        simpa only [AccessiblePointedGraph.mk_singletonGraph, HSet.mk_empty, HSet.mem_singleton]
          using member.2
      exact bound.symm)
    right_inv := fun _ => Subsingleton.elim _ _ }

section Identities

variable (domain : PresentedType A) (left right : A)

def identityGraph : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.separationGraph
    (AccessiblePointedGraph.singletonGraph AccessiblePointedGraph.empty)
    (fun _ => domain.value left = domain.value right)

theorem mem_identityGraph_iff {witness : HSet.{u}} :
    witness ∈ HSet.mk (identityGraph domain left right) ↔ witness = ∅ ∧ left = right := by
  rw [identityGraph, AccessiblePointedGraph.mk_separationGraph,
    AccessiblePointedGraph.mk_singletonGraph, HSet.mk_empty, HSet.mem_sep, HSet.mem_singleton]
  exact ⟨fun ⟨value, same⟩ => ⟨value, domain.value_injective same⟩,
    fun ⟨value, same⟩ => ⟨value, congrArg domain.value same⟩⟩

def identityEncode (same : left = right) :
    {witness : HSet.{u} // witness ∈ HSet.mk (identityGraph domain left right)} :=
  ⟨∅, (mem_identityGraph_iff domain left right).mpr ⟨rfl, same⟩⟩

def identity : PresentedType (ULift.{u, 0} (PLift (left = right))) where
  graph := identityGraph domain left right
  decode := {
    toFun := fun member => ⟨⟨((mem_identityGraph_iff domain left right).mp member.2).2⟩⟩
    invFun := fun witness => identityEncode domain left right witness.down.down
    left_inv := fun member => Subtype.ext ((mem_identityGraph_iff domain left right).mp member.2).1.symm
    right_inv := fun _ => Subsingleton.elim _ _ }

theorem identity_value (witness : ULift.{u, 0} (PLift (left = right))) :
    (identity domain left right).value witness = ∅ := rfl

theorem identity_empty_of_distinct (different : left ≠ right) :
    (identity domain left right).carrier = ∅ :=
  HSet.eq_empty_iff.mpr fun _ member =>
    different ((mem_identityGraph_iff domain left right).mp member).2

end Identities

end PresentedType

end Mettapedia.TypeTheory.MaterialSets.Hypersets
