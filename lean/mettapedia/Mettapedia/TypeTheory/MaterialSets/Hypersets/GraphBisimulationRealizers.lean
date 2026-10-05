import Mettapedia.TypeTheory.MaterialSets.Hypersets.AccessiblePointedGraph
import Mathlib.Logic.Equiv.Defs

/-!
# Small proof-relevant graph bisimulations

A matching realizer contains compatible finite matching trees. Each tree
retains an actual response to every child in both directions. Coherence
identifies the responses at successive depths. The resulting limit stays
in the universe of the two node carriers.

Coiteration constructs these realizers from actual matching data. Their
forgetful interpretation is ordinary propositional bisimilarity; no
conversion of a propositional existence statement into matching data is
used. The construction is the indexed finite-approximation limit of
Ahrens, Capriotti and Spadotti, *Non-Wellfounded Trees in Homotopy Type
Theory*, TLCA 2015, specialized to two-sided graph matching.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphBisimulationRealizers

universe u v w z

variable {A : Type u} {B : Type v}
variable (left : A → A → Prop) (right : B → B → Prop)

abbrev Child (relation : A → A → Prop) (node : A) :=
  {child : A // relation node child}

/-- One layer retains the matching child and the continuation realizer. -/
def Layer (family : A → B → Type w) (first : A) (second : B) : Type (max u v w) :=
  ((child : Child left first) → Σ matched : Child right second,
    family child.val matched.val) ×
  ((child : Child right second) → Σ matched : Child left first,
    family matched.val child.val)

namespace Layer

def map {source : A → B → Type w} {target : A → B → Type z}
    (operation : ∀ first second, source first second → target first second)
    {first : A} {second : B} (layer : Layer left right source first second) :
    Layer left right target first second :=
  ⟨fun child => ⟨(layer.1 child).1, operation _ _ (layer.1 child).2⟩,
    fun child => ⟨(layer.2 child).1, operation _ _ (layer.2 child).2⟩⟩

theorem map_id {source : A → B → Type w} {first : A} {second : B}
    (layer : Layer left right source first second) :
    map left right (fun _ _ value => value) layer = layer := by
  cases layer
  rfl

theorem map_comp {source : A → B → Type w} {middle : A → B → Type z}
    {target : A → B → Type*}
    (firstMap : ∀ first second, source first second → middle first second)
    (secondMap : ∀ first second, middle first second → target first second)
    {first : A} {second : B} (layer : Layer left right source first second) :
    map left right secondMap (map left right firstMap layer) =
      map left right (fun first second value => secondMap first second (firstMap first second value))
        layer := rfl

theorem map_congr {source : A → B → Type w} {target : A → B → Type z}
    {firstMap secondMap : ∀ first second, source first second → target first second}
    (same : ∀ first second value, firstMap first second value = secondMap first second value)
    {first : A} {second : B} (layer : Layer left right source first second) :
    map left right firstMap layer = map left right secondMap layer := by
  apply Prod.ext
  · funext child
    exact congrArg (Sigma.mk (layer.1 child).1) (same _ _ (layer.1 child).2)
  · funext child
    exact congrArg (Sigma.mk (layer.2 child).1) (same _ _ (layer.2 child).2)

end Layer

/-- A finite matching tree. The depth-zero tree makes no observation. -/
def Approx : Nat → A → B → Type (max u v)
  | 0, _, _ => PUnit
  | depth + 1, first, second => Layer left right (Approx depth) first second

/-- Truncation preserves all responses before the last depth. -/
def truncate : (depth : Nat) → ∀ first second,
    Approx left right (depth + 1) first second → Approx left right depth first second
  | 0, _, _, _ => PUnit.unit
  | depth + 1, _, _, layer => Layer.map left right (truncate depth) layer

/-- Compatible matching trees at every depth form a small realizer. -/
structure Realizer (first : A) (second : B) : Type (max u v) where
  approx : ∀ depth, Approx left right depth first second
  coherent : ∀ depth, truncate left right depth first second (approx (depth + 1)) = approx depth

namespace Realizer

theorem ext {first : A} {second : B} {firstProof secondProof : Realizer left right first second}
    (same : ∀ depth, firstProof.approx depth = secondProof.approx depth) :
    firstProof = secondProof := by
  cases firstProof
  cases secondProof
  congr
  funext depth
  exact same depth

end Realizer

section Coiteration

variable {witness : A → B → Type w}
variable (step : ∀ first second, witness first second → Layer left right witness first second)

def iterate : (depth : Nat) → ∀ first second,
    witness first second → Approx left right depth first second
  | 0, _, _, _ => PUnit.unit
  | depth + 1, first, second, proof =>
      Layer.map left right (iterate depth) (step first second proof)

theorem iterate_coherent (depth : Nat) (first : A) (second : B) (proof : witness first second) :
    truncate left right depth first second (iterate left right step (depth + 1) first second proof) =
      iterate left right step depth first second proof := by
  induction depth generalizing first second with
  | zero => rfl
  | succ depth induction =>
    change Layer.map left right (truncate left right depth)
        (Layer.map left right (iterate left right step (depth + 1)) (step first second proof)) =
      Layer.map left right (iterate left right step depth) (step first second proof)
    rw [Layer.map_comp]
    exact Layer.map_congr left right (fun first second proof => induction first second proof) _

/-- The supplied coalgebra gives finite matching data, from which the
whole coherent realizer is constructed. -/
def corec {first : A} {second : B} (proof : witness first second) :
    Realizer left right first second where
  approx depth := iterate left right step depth first second proof
  coherent depth := iterate_coherent left right step depth first second proof

end Coiteration

namespace FixedIndexLimit

variable {Index : Type u} (family : Nat → Index → Type v)
variable (step : ∀ depth index, family (depth + 1) index → family depth index)
variable (values : ∀ depth, Σ index, family depth index)
variable (compatible : ∀ depth,
  (⟨(values (depth + 1)).1, step depth _ (values (depth + 1)).2⟩ : Σ index, family depth index) =
    values depth)

include compatible in
/-- The index retained by a coherent dependent sum never changes. -/
theorem indexEq : (depth : Nat) → (values depth).1 = (values 0).1
  | 0 => rfl
  | depth + 1 => (congrArg Sigma.fst (compatible depth)).trans (indexEq depth)

def transport {Index : Type u} {fibre : Index → Type v} {first second : Index}
    (same : first = second) (value : fibre first) : fibre second := same ▸ value

theorem transport_comp {Index : Type u} {fibre : Index → Type v} {first middle last : Index}
    (firstSame : first = middle) (secondSame : middle = last) (value : fibre first) :
    transport secondSame (transport firstSame value) = transport (firstSame.trans secondSame) value := by
  cases firstSame
  cases secondSame
  rfl

theorem map_transport {Index : Type u} {source : Index → Type v} {target : Index → Type w}
    (operation : ∀ index, source index → target index) {first second : Index}
    (same : first = second) (value : source first) :
    operation second (transport same value) = transport same (operation first value) := by
  cases same
  rfl

theorem sigma_transport {Index : Type u} {fibre : Index → Type v}
    {first second : Σ index, fibre index} (same : first = second) :
    transport (congrArg Sigma.fst same) first.2 = second.2 := by
  cases same
  rfl

theorem sigma_mk_transport {Index : Type u} {fibre : Index → Type v}
    {first second : Index} (same : first = second) (value : fibre first) :
    (⟨second, transport same value⟩ : Σ index, fibre index) = ⟨first, value⟩ := by
  cases same
  rfl

def value (depth : Nat) : family depth (values 0).1 :=
  transport (indexEq family step values compatible depth) (values depth).2

theorem reconstruct (depth : Nat) :
    (⟨(values 0).1, value family step values compatible depth⟩ : Σ index, family depth index) =
      values depth :=
  sigma_mk_transport (indexEq family step values compatible depth) (values depth).2

theorem value_coherent (depth : Nat) :
    step depth (values 0).1 (value family step values compatible (depth + 1)) =
      value family step values compatible depth := by
  change step depth (values 0).1
      (transport (indexEq family step values compatible (depth + 1)) (values (depth + 1)).2) =
    transport (indexEq family step values compatible depth) (values depth).2
  rw [map_transport (step depth)]
  change transport
      ((congrArg Sigma.fst (compatible depth)).trans (indexEq family step values compatible depth))
      (step depth (values (depth + 1)).1 (values (depth + 1)).2) = _
  rw [← transport_comp (congrArg Sigma.fst (compatible depth))
    (indexEq family step values compatible depth)]
  exact congrArg (transport (indexEq family step values compatible depth)) (sigma_transport (compatible depth))

end FixedIndexLimit

namespace Realizer

variable {left right} {first : A} {second : B}

def leftValues (proof : Realizer left right first second) (child : Child left first)
    (depth : Nat) : Σ matched : Child right second, Approx left right depth child.val matched.val :=
  (proof.approx (depth + 1)).1 child

theorem leftValues_coherent (proof : Realizer left right first second) (child : Child left first)
    (depth : Nat) :
    (⟨(proof.leftValues child (depth + 1)).1,
      truncate left right depth _ _ (proof.leftValues child (depth + 1)).2⟩ :
        Σ matched : Child right second, Approx left right depth child.val matched.val) =
      proof.leftValues child depth :=
  congrArg (fun layer : Approx left right (depth + 1) first second => layer.1 child)
    (proof.coherent (depth + 1))

def rightValues (proof : Realizer left right first second) (child : Child right second)
    (depth : Nat) : Σ matched : Child left first, Approx left right depth matched.val child.val :=
  (proof.approx (depth + 1)).2 child

theorem rightValues_coherent (proof : Realizer left right first second) (child : Child right second)
    (depth : Nat) :
    (⟨(proof.rightValues child (depth + 1)).1,
      truncate left right depth _ _ (proof.rightValues child (depth + 1)).2⟩ :
        Σ matched : Child left first, Approx left right depth matched.val child.val) =
      proof.rightValues child depth :=
  congrArg (fun layer : Approx left right (depth + 1) first second => layer.2 child)
    (proof.coherent (depth + 1))

/-- Reading a realizer returns an actual matching child and a coherent
continuation at that child. All transports eliminate proven index equalities. -/
def out (proof : Realizer left right first second) :
    Layer left right (Realizer left right) first second :=
  ⟨fun child =>
    ⟨(proof.leftValues child 0).1,
      { approx := FixedIndexLimit.value (fun depth (matched : Child right second) =>
            Approx left right depth child.val matched.val)
          (fun depth (matched : Child right second) => truncate left right depth child.val matched.val)
          (proof.leftValues child) (proof.leftValues_coherent child)
        coherent := FixedIndexLimit.value_coherent
          (fun depth (matched : Child right second) => Approx left right depth child.val matched.val)
          (fun depth (matched : Child right second) => truncate left right depth child.val matched.val)
          (proof.leftValues child) (proof.leftValues_coherent child) }⟩,
    fun child =>
    ⟨(proof.rightValues child 0).1,
      { approx := FixedIndexLimit.value (fun depth (matched : Child left first) =>
            Approx left right depth matched.val child.val)
          (fun depth (matched : Child left first) => truncate left right depth matched.val child.val)
          (proof.rightValues child) (proof.rightValues_coherent child)
        coherent := FixedIndexLimit.value_coherent
          (fun depth (matched : Child left first) => Approx left right depth matched.val child.val)
          (fun depth (matched : Child left first) => truncate left right depth matched.val child.val)
          (proof.rightValues child) (proof.rightValues_coherent child) }⟩⟩

def rollApprox (layer : Layer left right (Realizer left right) first second) :
    (depth : Nat) → Approx left right depth first second
  | 0 => PUnit.unit
  | depth + 1 => Layer.map left right (fun _ _ proof => proof.approx depth) layer

theorem rollApprox_coherent (layer : Layer left right (Realizer left right) first second)
    (depth : Nat) :
    truncate left right depth first second (rollApprox layer (depth + 1)) = rollApprox layer depth := by
  cases depth with
  | zero => rfl
  | succ depth =>
    change Layer.map left right (truncate left right depth)
        (Layer.map left right (fun _ _ proof => proof.approx (depth + 1)) layer) =
      Layer.map left right (fun _ _ proof => proof.approx depth) layer
    rw [Layer.map_comp]
    exact Layer.map_congr left right (fun _ _ proof => proof.coherent depth) layer

/-- Any actual two-sided layer of realizers constructs a whole realizer. -/
def roll (layer : Layer left right (Realizer left right) first second) :
    Realizer left right first second where
  approx := rollApprox layer
  coherent := rollApprox_coherent layer

theorem out_roll (layer : Layer left right (Realizer left right) first second) :
    (roll layer).out = layer := by
  apply Prod.ext
  · funext child
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Realizer.ext
    intro depth
    rfl
  · funext child
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Realizer.ext
    intro depth
    rfl

theorem roll_out (proof : Realizer left right first second) : roll proof.out = proof := by
  apply Realizer.ext
  intro depth
  cases depth with
  | zero => exact proof.coherent 0
  | succ depth =>
    apply Prod.ext
    · funext child
      exact FixedIndexLimit.reconstruct
        (fun depth (matched : Child right second) => Approx left right depth child.val matched.val)
        (fun depth (matched : Child right second) => truncate left right depth child.val matched.val)
        (proof.leftValues child) (proof.leftValues_coherent child) depth
    · funext child
      exact FixedIndexLimit.reconstruct
        (fun depth (matched : Child left first) => Approx left right depth matched.val child.val)
        (fun depth (matched : Child left first) => truncate left right depth matched.val child.val)
        (proof.rightValues child) (proof.rightValues_coherent child) depth

def unfolding : Realizer left right first second ≃
    Layer left right (Realizer left right) first second where
  toFun := out
  invFun := roll
  left_inv := roll_out
  right_inv := out_roll

theorem out_corec {witness : A → B → Type w}
    (step : ∀ first second, witness first second → Layer left right witness first second)
    (proof : witness first second) :
    (corec left right step proof).out =
      Layer.map left right (fun _ _ proof => corec left right step proof) (step first second proof) := by
  apply Prod.ext
  · funext child
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Realizer.ext
    intro depth
    rfl
  · funext child
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Realizer.ext
    intro depth
    rfl

end Realizer

section Equivalence

variable {left right}

def reflexiveStep (first second : A) (same : ULift.{u} (PLift (first = second))) :
    Layer left left (fun first second => ULift.{u} (PLift (first = second))) first second := by
  cases same.down.down
  exact ⟨fun child => ⟨child, ⟨⟨rfl⟩⟩⟩, fun child => ⟨child, ⟨⟨rfl⟩⟩⟩⟩

def Realizer.refl (first : A) : Realizer left left first first :=
  corec left left (reflexiveStep (left := left)) ⟨⟨rfl⟩⟩

def symmetricStep (first : B) (second : A) (proof : Realizer left right second first) :
    Layer right left (fun first second => Realizer left right second first) first second :=
  ⟨proof.out.2, proof.out.1⟩

def Realizer.symm {first : A} {second : B} (proof : Realizer left right first second) :
    Realizer right left second first :=
  corec right left (symmetricStep (left := left) (right := right)) proof

variable {C : Type w} {last : C → C → Prop}

def compositeStep (first : A) (third : C)
    (proof : Σ second : B, Realizer left right first second × Realizer right last second third) :
    Layer left last
      (fun first third => Σ second : B, Realizer left right first second × Realizer right last second third)
      first third :=
  ⟨fun child =>
      let middle := proof.2.1.out.1 child
      let target := proof.2.2.out.1 middle.1
      ⟨target.1, middle.1.val, middle.2, target.2⟩,
    fun child =>
      let middle := proof.2.2.out.2 child
      let source := proof.2.1.out.2 middle.1
      ⟨source.1, middle.1.val, source.2, middle.2⟩⟩

def Realizer.trans {first : A} {second : B} {third : C}
    (firstProof : Realizer left right first second) (secondProof : Realizer right last second third) :
    Realizer left last first third :=
  corec left last (compositeStep (left := left) (right := right) (last := last))
    ⟨second, firstProof, secondProof⟩

end Equivalence

section ActualLifting

variable {left right} (operation : A → B)
variable (preserves : ∀ first child, left first child → right (operation first) (operation child))
variable (liftChild : ∀ first (child : Child right (operation first)),
  {source : Child left first // operation source.val = child.val})

/-- A map with computed child lifts supplies matching data, not only
propositional surjectivity on the child fibres. -/
def mapStep (first : A) (second : B) (same : ULift.{max u v} (PLift (operation first = second))) :
    Layer left right (fun first second => ULift.{max u v} (PLift (operation first = second)))
      first second := by
  cases same.down.down
  refine ⟨fun child => ⟨⟨operation child.val, preserves _ _ child.property⟩, ⟨⟨rfl⟩⟩⟩, ?_⟩
  intro child
  exact ⟨(liftChild first child).val, ⟨⟨(liftChild first child).property⟩⟩⟩

def Realizer.ofMap (first : A) : Realizer left right first (operation first) :=
  corec left right (mapStep operation preserves liftChild) ⟨⟨rfl⟩⟩

end ActualLifting

section Generated

variable {left}

/-- The generated-subgraph inclusion has an explicit lift of each child. -/
def generated (first : A) (node : (AccessiblePointedGraph.generated left first).Node) :
    Realizer (AccessiblePointedGraph.generated left first).edge left node node.val :=
  Realizer.ofMap Subtype.val (fun _ _ edge => edge)
    (fun source child => ⟨⟨⟨child.val, source.property.tail child.property⟩, child.property⟩, rfl⟩) node

end Generated

section Forgetting

variable {left right}

theorem isBisimulation_realizers :
    IsBisimulation left right (fun first second => Nonempty (Realizer left right first second)) := by
  intro first second inhabited
  obtain ⟨proof⟩ := inhabited
  constructor
  · intro child edge
    let matched := proof.out.1 ⟨child, edge⟩
    exact ⟨matched.1.val, matched.1.property, ⟨matched.2⟩⟩
  · intro child edge
    let matched := proof.out.2 ⟨child, edge⟩
    exact ⟨matched.1.val, matched.1.property, ⟨matched.2⟩⟩

/-- Forgetting actual matching data gives ordinary bisimilarity. -/
theorem Realizer.forget {first : A} {second : B} (proof : Realizer left right first second) :
    Bisimilar left right first second :=
  (isBisimulation_realizers (left := left) (right := right)).bisimilar ⟨proof⟩

end Forgetting

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphBisimulationRealizers
