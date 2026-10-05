import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedSubtypes
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedLabelledBisimulation

/-!
# Material dependent products with externally retained arguments

Function evaluation receives its actual argument from the consumer. It
therefore needs faithful authored argument labels, not a material decoder
for the entire argument carrier. The collecting graph of all functions and
its bounded output decoder are constructed explicitly. The same construction
represents predicate-compatible functions by separation.

Concrete natural argument codings and bare material output families discharge
these data at one raised graph bound. They do not select natural numbers from
an existential membership proposition or assume a host Boolean decoder.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

/-- Faithful labels preserve the externally retained argument identity.
There is deliberately no decoder for arbitrary material argument values. -/
structure ArgumentCoding (A : Type u) : Type (u + 1) where
  graph : A → AccessiblePointedGraph.{u}
  injective : Function.Injective (fun argument => HSet.mk (graph argument))

namespace ArgumentCoding

variable {A : Type u} (coding : ArgumentCoding A)

def reading (argument : A) : HSet.{u} := HSet.mk (coding.graph argument)

theorem mk_graph (argument : A) : HSet.mk (coding.graph argument) = coding.reading argument := rfl

def subtype (predicate : A → Prop) : ArgumentCoding {argument : A // predicate argument} where
  graph argument := coding.graph argument.val
  injective := fun _ _ same => Subtype.ext (coding.injective same)

def sigma {B : A → Type u} (fibres : (a : A) → ArgumentCoding (B a)) : ArgumentCoding (Sigma B) where
  graph argument := AccessiblePointedGraph.kpairGraph (coding.graph argument.1)
    ((fibres argument.1).graph argument.2)
  injective := by
    intro first second same
    dsimp only at same
    rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph] at same
    have firstSame := coding.injective (HSet.kpair_inj.mp same).1
    rcases first with ⟨a, b⟩
    rcases second with ⟨a', b'⟩
    cases firstSame
    have secondSame := (fibres a).injective (HSet.kpair_inj.mp same).2
    exact Sigma.ext rfl (heq_of_eq secondSame)

/-- Every natural label graph is recursively authored and injective. -/
def naturals : ArgumentCoding (ULift.{u, 0} Nat) where
  graph number := OutcomeLabels.chainGraph number.down
  injective := by
    intro first second same
    dsimp only at same
    rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at same
    exact ULift.ext _ _ (OutcomeLabels.chainValue_injective same)

/-- A smaller authored argument remains faithful at a raised material bound. -/
def lift : ArgumentCoding (ULift.{u + 1, u} A) where
  graph argument := (coding.graph argument.down).lift
  injective := by
    intro first second same
    have original : HSet.mk (coding.graph first.down) = HSet.mk (coding.graph second.down) :=
      HSet.lift_injective same
    exact ULift.ext _ _ (coding.injective original)

end ArgumentCoding

namespace PresentedType

/-- A proved semantic equivalence changes only the decoded type of an
actual representation. The material carrier and term encodings remain known. -/
def relabel {A B : Type u} (model : PresentedType A) (equivalence : A ≃ B) : PresentedType B where
  graph := model.graph
  decode := model.decode.trans equivalence

theorem relabel_value {A B : Type u} (model : PresentedType A) (equivalence : A ≃ B) (term : B) :
    (relabel model equivalence).value term = model.value (equivalence.symm term) := rfl

end PresentedType

namespace LabelledDependentProducts

open AccessiblePointedGraph

variable {A : Type u} {B : A → Type u} (coding : ArgumentCoding A)
variable (fibres : (a : A) → PresentedType (B a))

def functionGraph (sectionValue : (a : A) → B a) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.sup fun a : A =>
    AccessiblePointedGraph.kpairGraph (coding.graph a) ((fibres a).termGraph (sectionValue a))

theorem mem_functionGraph_iff (sectionValue : (a : A) → B a) (row : HSet.{u}) :
    row ∈ HSet.mk (functionGraph coding fibres sectionValue) ↔
      ∃ a, HSet.kpair (coding.reading a) ((fibres a).value (sectionValue a)) = row := by
  change row ∈ HSet.range (fun a : A => AccessiblePointedGraph.kpairGraph
    (coding.graph a) ((fibres a).termGraph (sectionValue a))) ↔ _
  rw [HSet.mem_range]
  constructor <;> rintro ⟨a, same⟩ <;> refine ⟨a, ?_⟩
  · rw [AccessiblePointedGraph.mk_kpairGraph, ArgumentCoding.mk_graph, PresentedType.mk_termGraph] at same
    exact same
  · rw [AccessiblePointedGraph.mk_kpairGraph, ArgumentCoding.mk_graph, PresentedType.mk_termGraph]
    exact same

def productGraph : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.sup (functionGraph coding fibres)

theorem mem_productGraph_iff {graphValue : HSet.{u}} :
    graphValue ∈ HSet.mk (productGraph coding fibres) ↔
      ∃ sectionValue : (a : A) → B a, HSet.mk (functionGraph coding fibres sectionValue) = graphValue :=
  HSet.mem_range

def functionMember (sectionValue : (a : A) → B a) :
    {graphValue : HSet.{u} // graphValue ∈ HSet.mk (productGraph coding fibres)} :=
  ⟨HSet.mk (functionGraph coding fibres sectionValue),
    (mem_productGraph_iff coding fibres).mpr ⟨sectionValue, rfl⟩⟩

def evalValue (graphValue : HSet.{u}) (a : A) : HSet.{u} :=
  HSet.sUnion (HSet.sep (fun b => HSet.kpair (coding.reading a) b ∈ graphValue) (fibres a).carrier)

theorem evalValue_functionGraph (sectionValue : (a : A) → B a) (a : A) :
    evalValue coding fibres (HSet.mk (functionGraph coding fibres sectionValue)) a =
      (fibres a).value (sectionValue a) := by
  have row : HSet.sep (fun b => HSet.kpair (coding.reading a) b ∈
      HSet.mk (functionGraph coding fibres sectionValue)) (fibres a).carrier =
      {(fibres a).value (sectionValue a)} := by
    apply HSet.ext
    intro b
    rw [HSet.mem_sep, mem_functionGraph_iff, HSet.mem_singleton]
    constructor
    · rintro ⟨_, a', same⟩
      have index : a' = a := coding.injective (HSet.kpair_inj.mp same).1
      cases index
      exact (HSet.kpair_inj.mp same).2.symm
    · intro same
      exact ⟨same ▸ (fibres a).value_mem (sectionValue a), a, congrArg (HSet.kpair _) same.symm⟩
  exact (congrArg HSet.sUnion row).trans (HSet.sUnion_singleton _)

def evaluate (graphValue : {graphValue : HSet.{u} // graphValue ∈ HSet.mk (productGraph coding fibres)})
    (a : A) : B a :=
  (fibres a).decode ⟨evalValue coding fibres graphValue.1 a, by
    obtain ⟨sectionValue, same⟩ := (mem_productGraph_iff coding fibres).mp graphValue.2
    rw [← same, evalValue_functionGraph]
    exact (fibres a).value_mem (sectionValue a)⟩

theorem evaluate_functionMember (sectionValue : (a : A) → B a) (a : A) :
    evaluate coding fibres (functionMember coding fibres sectionValue) a = sectionValue a := by
  apply (fibres a).decode.symm.injective
  apply Subtype.ext
  exact (PresentedType.value_decode _ _).trans (evalValue_functionGraph coding fibres sectionValue a)

theorem functionMember_evaluate
    (graphValue : {graphValue : HSet.{u} // graphValue ∈ HSet.mk (productGraph coding fibres)}) :
    functionMember coding fibres (evaluate coding fibres graphValue) = graphValue := by
  obtain ⟨sectionValue, same⟩ := (mem_productGraph_iff coding fibres).mp graphValue.2
  have memberSame : graphValue = functionMember coding fibres sectionValue := Subtype.ext same.symm
  rw [memberSame]
  exact congrArg (functionMember coding fibres) (funext (evaluate_functionMember coding fibres sectionValue))

def product : PresentedType ((a : A) → B a) where
  graph := productGraph coding fibres
  decode := {
    toFun := evaluate coding fibres
    invFun := functionMember coding fibres
    left_inv := functionMember_evaluate coding fibres
    right_inv := fun sectionValue => funext (evaluate_functionMember coding fibres sectionValue) }

theorem product_value (sectionValue : (a : A) → B a) :
    (product coding fibres).value sectionValue = HSet.mk (functionGraph coding fibres sectionValue) := rfl

theorem product_application (sectionValue : (a : A) → B a) (a : A) :
    (product coding fibres).decode ((product coding fibres).decode.symm sectionValue) a =
      sectionValue a := evaluate_functionMember coding fibres sectionValue a

theorem product_entry (sectionValue : (a : A) → B a) (a : A) :
    HSet.kpair (coding.reading a) ((fibres a).value (sectionValue a)) ∈
      (product coding fibres).value sectionValue :=
  (mem_functionGraph_iff coding fibres sectionValue _).mpr ⟨a, rfl⟩

/-- Compatibility is implemented in the actual material function carrier,
with both the unrestricted output decoder and its predicate evidence. -/
def compatibleProduct (compatible : ((a : A) → B a) → Prop) :
    PresentedType {sectionValue : (a : A) → B a // compatible sectionValue} :=
  PresentedType.restrict (product coding fibres) compatible

theorem compatibleProduct_value (compatible : ((a : A) → B a) → Prop)
    (sectionValue : {sectionValue : (a : A) → B a // compatible sectionValue}) :
    (compatibleProduct coding fibres compatible).value sectionValue =
      HSet.mk (functionGraph coding fibres sectionValue.val) := rfl

section LargerOutputs

variable {Input : Type u} {Output : Input → Type (u + 1)}

def liftedArgumentFunctionEquiv :
    ((argument : ULift.{u + 1, u} Input) → Output argument.down) ≃
      ((argument : Input) → Output argument) where
  toFun function argument := function (ULift.up argument)
  invFun function argument := function argument.down
  left_inv function := by
    funext argument
    cases argument
    rfl
  right_inv _ := rfl

/-- Larger result fibres keep the original external argument type. Only
the graph construction lifts its argument indices to the collecting bound. -/
def raisedArgumentProduct (arguments : ArgumentCoding Input)
    (outputs : (argument : Input) → PresentedType (Output argument)) :
    PresentedType ((argument : Input) → Output argument) :=
  PresentedType.relabel
    (product arguments.lift (fun argument => outputs argument.down)) liftedArgumentFunctionEquiv

theorem raisedArgumentProduct_entry (arguments : ArgumentCoding Input)
    (outputs : (argument : Input) → PresentedType (Output argument))
    (function : (argument : Input) → Output argument) (argument : Input) :
    HSet.kpair (HSet.lift (arguments.reading argument)) ((outputs argument).value (function argument)) ∈
      (raisedArgumentProduct arguments outputs).value function := by
  exact product_entry arguments.lift (fun argument => outputs argument.down)
    (fun argument => function argument.down) (ULift.up argument)

end LargerOutputs

section ConcreteFamilies

open GeneratedMaterialDecoder LiftedFamilyModel

/-- An arbitrary bare natural-indexed material family supplies all output
representations at the raised level, without a global graph selector. -/
def naturalFamilyProduct (family : ULift.{u + 1, 0} Nat → HSet.{u}) :
    PresentedType ((number : ULift.{u + 1, 0} Nat) → Elements (family number)) :=
  product ArgumentCoding.naturals (fun number => liftedModel (family number))

theorem naturalFamilyProduct_entry (family : ULift.{u + 1, 0} Nat → HSet.{u})
    (sectionValue : (number : ULift.{u + 1, 0} Nat) → Elements (family number))
    (number : ULift.{u + 1, 0} Nat) :
    HSet.kpair (OutcomeLabels.chainValue number.down) (HSet.lift (sectionValue number).1) ∈
      (naturalFamilyProduct family).value sectionValue := by
  have entry := product_entry ArgumentCoding.naturals (fun number => liftedModel (family number))
    sectionValue number
  simpa only [ArgumentCoding.reading, ArgumentCoding.naturals, OutcomeLabels.mk_chainGraph,
    liftedModel_value, naturalFamilyProduct] using entry

/-- The varying singleton family ranges over all finite material chains. -/
def chainFamily (number : ULift.{u + 1, 0} Nat) : HSet.{u} := {OutcomeLabels.chainValue number.down}

def chainSection (number : ULift.{u + 1, 0} Nat) : Elements (chainFamily number) :=
  ⟨OutcomeLabels.chainValue number.down, HSet.mem_singleton.mpr rfl⟩

theorem chainProduct_beta (number : ULift.{u + 1, 0} Nat) :
    (naturalFamilyProduct chainFamily).decode
      ((naturalFamilyProduct chainFamily).decode.symm chainSection) number = chainSection number :=
  product_application _ _ _ _

theorem chain_family_varies {first second : ULift.{u + 1, 0} Nat}
    (different : first ≠ second) : chainFamily first ≠ chainFamily second := by
  intro same
  have sameNumbers := OutcomeLabels.chainValue_injective (HSet.singleton_inj.mp same)
  exact different (ULift.ext _ _ sameNumbers)

theorem empty_fibre_blocks_product
    (family : ULift.{u + 1, 0} Nat → HSet.{u}) (number : ULift.{u + 1, 0} Nat)
    (empty : family number = ∅) :
    (naturalFamilyProduct family).carrier = (∅ : HSet.{u + 1}) := by
  apply HSet.eq_empty_iff.mpr
  intro value member
  let sectionValue := (naturalFamilyProduct family).decode ⟨value, member⟩
  have impossible := (sectionValue number).2
  exact HSet.notMem_empty _
    (Eq.mp (congrArg (fun bound : HSet.{u} => (sectionValue number).1 ∈ bound) empty) impossible)

end ConcreteFamilies

#print axioms product
#print axioms compatibleProduct
#print axioms naturalFamilyProduct_entry
#print axioms chainProduct_beta

end LabelledDependentProducts

end Mettapedia.TypeTheory.MaterialSets.Hypersets
