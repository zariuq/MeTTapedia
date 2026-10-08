import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphDiagrams

/-!
# Constructed small future-indexed matching limits

The indexed polynomial limit is built from coherent finite trees. Its
one-step observation retains a shape and every continuation, and
coiteration computes the entire limit. Contextual graph matching uses
this construction with actual future arrows and two-sided child replies.
Every continuation retains all its own futures as well.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizers

open CategoryTheory ContextualGraphDiagrams
open Mettapedia.TypeTheory.ContextualWitnessCover
universe u v w

namespace IndexedLimit

variable {Index : Type u} (Shape : Index → Type u)
variable (Position : (index : Index) → Shape index → Type u)
variable (next : (index : Index) → (shape : Shape index) → Position index shape → Index)

abbrev Layer (family : Index → Type v) (index : Index) :=
  Σ shape : Shape index, (position : Position index shape) → family (next index shape position)

def map {source : Index → Type v} {target : Index → Type w}
    (operation : ∀ index, source index → target index) {index : Index}
    (layer : Layer Shape Position next source index) : Layer Shape Position next target index :=
  ⟨layer.1, fun position => operation _ (layer.2 position)⟩

theorem map_composition {source : Index → Type v} {middle : Index → Type w}
    {target : Index → Type*} (earlier : ∀ index, source index → middle index)
    (later : ∀ index, middle index → target index) {index : Index}
    (layer : Layer Shape Position next source index) :
    map Shape Position next later (map Shape Position next earlier layer) =
      map Shape Position next (fun index value => later index (earlier index value)) layer := rfl

theorem map_congr {source : Index → Type v} {target : Index → Type w}
    {first second : ∀ index, source index → target index}
    (same : ∀ index value, first index value = second index value) {index : Index}
    (layer : Layer Shape Position next source index) :
    map Shape Position next first layer = map Shape Position next second layer := by
  unfold map
  exact congrArg (Sigma.mk layer.1) (funext (fun position => same _ _))

def Approx : Nat → Index → Type u
  | 0, _ => PUnit
  | depth+1, index => Layer Shape Position next (Approx depth) index

def truncate : (depth : Nat) → ∀ index,
    Approx Shape Position next (depth+1) index → Approx Shape Position next depth index
  | 0, _, _ => PUnit.unit
  | depth+1, _, layer => map Shape Position next (truncate depth) layer

structure Realizer (index : Index) : Type u where
  approx : ∀ depth, Approx Shape Position next depth index
  coherent : ∀ depth, truncate Shape Position next depth index (approx (depth+1)) = approx depth

section Coiteration

variable {witness : Index → Type v}
variable (step : ∀ index, witness index → Layer Shape Position next witness index)

def iterate : (depth : Nat) → ∀ index, witness index → Approx Shape Position next depth index
  | 0, _, _ => PUnit.unit
  | depth+1, index, proof => map Shape Position next (iterate depth) (step index proof)

theorem iterate_coherent (depth : Nat) (index : Index) (proof : witness index) :
    truncate Shape Position next depth index
      (iterate Shape Position next step (depth+1) index proof) =
      iterate Shape Position next step depth index proof := by
  induction depth generalizing index with
  | zero => rfl
  | succ depth induction =>
    change map Shape Position next (truncate Shape Position next depth)
      (map Shape Position next (iterate Shape Position next step (depth+1)) (step index proof)) = _
    rw [map_composition]
    exact map_congr Shape Position next (fun index proof => induction index proof) _

def corec {index : Index} (proof : witness index) : Realizer Shape Position next index where
  approx depth := iterate Shape Position next step depth index proof
  coherent depth := iterate_coherent Shape Position next step depth index proof

end Coiteration

namespace Realizer

variable {Shape Position next} {index : Index}

def values (proof : Realizer Shape Position next index) (depth : Nat) :
    Σ shape : Shape index,
      (position : Position index shape) → Approx Shape Position next depth (next index shape position) :=
  proof.approx (depth+1)

theorem values_coherent (proof : Realizer Shape Position next index) (depth : Nat) :
    (⟨(proof.values (depth+1)).1, fun position =>
      truncate Shape Position next depth _ ((proof.values (depth+1)).2 position)⟩ :
      Σ shape : Shape index,
        (position : Position index shape) → Approx Shape Position next depth (next index shape position)) =
      proof.values depth := proof.coherent (depth+1)

def out (proof : Realizer Shape Position next index) :
    Layer Shape Position next (Realizer Shape Position next) index :=
  let family := fun depth (shape : Shape index) =>
    (position : Position index shape) → Approx Shape Position next depth (next index shape position)
  let dropping := fun depth (shape : Shape index) (value : family (depth+1) shape) =>
    fun position => truncate Shape Position next depth _ (value position)
  ⟨(proof.values 0).1, fun position => {
    approx depth := GraphBisimulationRealizers.FixedIndexLimit.value family dropping
      proof.values proof.values_coherent depth position
    coherent depth := congrFun
      (GraphBisimulationRealizers.FixedIndexLimit.value_coherent family dropping
        proof.values proof.values_coherent depth) position }⟩

def rollApprox (layer : Layer Shape Position next (Realizer Shape Position next) index) :
    (depth : Nat) → Approx Shape Position next depth index
  | 0 => PUnit.unit
  | depth+1 => map Shape Position next (fun _ proof => proof.approx depth) layer

theorem rollApprox_coherent (layer : Layer Shape Position next (Realizer Shape Position next) index)
    (depth : Nat) : truncate Shape Position next depth index (rollApprox layer (depth+1)) =
      rollApprox layer depth := by
  cases depth with
  | zero => rfl
  | succ depth =>
    change map Shape Position next (truncate Shape Position next depth)
      (map Shape Position next (fun _ proof => proof.approx (depth+1)) layer) =
        map Shape Position next (fun _ proof => proof.approx depth) layer
    rw [map_composition]
    exact map_congr Shape Position next (fun _ proof => proof.coherent depth) _

def roll (layer : Layer Shape Position next (Realizer Shape Position next) index) :
    Realizer Shape Position next index where
  approx := rollApprox layer
  coherent := rollApprox_coherent layer

end Realizer
end IndexedLimit

variable {D : Type u} [Category.{u} D]
variable (left right : Diagram D)

abbrev Future (point : D) : Type u := Σ target : D, point ⟶ target

abbrev Index : Type u := Σ point : D, left.nodes.obj point × right.nodes.obj point
abbrev Child (graph : Diagram D) (point : D) (node : graph.nodes.obj point) :=
  {child : graph.nodes.obj point // graph.edge point node child}

abbrev LeftChildren (index : Index left right) (future : Future index.1) :=
  Child left future.1 (left.nodes.map future.2 index.2.1)
abbrev RightChildren (index : Index left right) (future : Future index.1) :=
  Child right future.1 (right.nodes.map future.2 index.2.2)

def Shape (index : Index left right) : Type u :=
  (future : Future index.1) →
    (LeftChildren left right index future → RightChildren left right index future) ×
    (RightChildren left right index future → LeftChildren left right index future)

def Position (index : Index left right) (_shape : Shape left right index) : Type u :=
  Σ future : Future index.1,
    LeftChildren left right index future ⊕ RightChildren left right index future

def next (index : Index left right) (shape : Shape left right index)
    (position : Position left right index shape) : Index left right :=
  match position.2 with
  | .inl child => ⟨position.1.1, child.val, ((shape position.1).1 child).val⟩
  | .inr child => ⟨position.1.1, ((shape position.1).2 child).val, child.val⟩

abbrev Realizer (point : D) (first : left.nodes.obj point) (second : right.nodes.obj point) : Type u :=
  IndexedLimit.Realizer (Shape left right) (Position left right) (next left right) ⟨point, first, second⟩

abbrev Layer (family : Index left right → Type v) (point : D)
    (first : left.nodes.obj point) (second : right.nodes.obj point) :=
  IndexedLimit.Layer (Shape left right) (Position left right) (next left right) family ⟨point, first, second⟩

namespace Realizer

variable {left right} {point : D} {first : left.nodes.obj point} {second : right.nodes.obj point}

def forth (proof : Realizer left right point first second) (future : Future point)
    (child : Child left future.1 (left.nodes.map future.2 first)) :
    Σ matched : Child right future.1 (right.nodes.map future.2 second),
      Realizer left right future.1 child.val matched.val :=
  let reading := IndexedLimit.Realizer.out proof
  ⟨(reading.1 future).1 child, reading.2 ⟨future, .inl child⟩⟩

def back (proof : Realizer left right point first second) (future : Future point)
    (child : Child right future.1 (right.nodes.map future.2 second)) :
    Σ matched : Child left future.1 (left.nodes.map future.2 first),
      Realizer left right future.1 matched.val child.val :=
  let reading := IndexedLimit.Realizer.out proof
  ⟨(reading.1 future).2 child, reading.2 ⟨future, .inr child⟩⟩

end Realizer

def roll {point : D} {first : left.nodes.obj point} {second : right.nodes.obj point}
    (forth : (future : Future point) →
      (child : Child left future.1 (left.nodes.map future.2 first)) →
        Σ matched : Child right future.1 (right.nodes.map future.2 second),
          Realizer left right future.1 child.val matched.val)
    (back : (future : Future point) →
      (child : Child right future.1 (right.nodes.map future.2 second)) →
        Σ matched : Child left future.1 (left.nodes.map future.2 first),
          Realizer left right future.1 matched.val child.val) :
    Realizer left right point first second :=
  IndexedLimit.Realizer.roll ⟨fun future =>
    ⟨fun child => (forth future child).1, fun child => (back future child).1⟩,
    fun ⟨future, position⟩ => match position with
      | .inl child => (forth future child).2
      | .inr child => (back future child).2⟩

def castChild (graph : Diagram D) {point : D} {first second : graph.nodes.obj point}
    (same : first = second) (child : Child graph point first) : Child graph point second :=
  ⟨child.val, same ▸ child.property⟩

namespace Realizer

variable {left right}

def reflexiveStep (graph : Diagram D) (index : Index graph graph)
    (same : PLift (index.2.1 = index.2.2)) :
    IndexedLimit.Layer (Shape graph graph) (Position graph graph) (next graph graph)
      (fun index => PLift (index.2.1 = index.2.2)) index := by
  rcases index with ⟨point, first, second⟩
  cases same.down
  exact ⟨fun _ => ⟨id, id⟩, fun ⟨future, position⟩ => by
    cases position <;> exact ⟨rfl⟩⟩

def refl (graph : Diagram D) (point : D) (node : graph.nodes.obj point) :
    Realizer graph graph point node node :=
  IndexedLimit.corec (Shape graph graph) (Position graph graph) (next graph graph)
    (reflexiveStep graph) ⟨rfl⟩

def symmetricStep (index : Index right left)
    (proof : Realizer left right index.1 index.2.2 index.2.1) :
    IndexedLimit.Layer (Shape right left) (Position right left) (next right left)
      (fun index => Realizer left right index.1 index.2.2 index.2.1) index :=
  let reading := IndexedLimit.Realizer.out proof
  ⟨fun future => ⟨(reading.1 future).2, (reading.1 future).1⟩,
    fun ⟨future, position⟩ => match position with
      | .inl child => reading.2 ⟨future, .inr child⟩
      | .inr child => reading.2 ⟨future, .inl child⟩⟩

def symm {point : D} {first : left.nodes.obj point} {second : right.nodes.obj point}
    (proof : Realizer left right point first second) : Realizer right left point second first :=
  IndexedLimit.corec (Shape right left) (Position right left) (next right left)
    symmetricStep proof

variable (middle : Diagram D)

abbrev TransitiveWitness (index : Index left right) : Type u :=
  Σ node : middle.nodes.obj index.1,
    Realizer left middle index.1 index.2.1 node ×
      Realizer middle right index.1 node index.2.2

def transitiveStep (index : Index left right) (proof : TransitiveWitness middle index) :
    IndexedLimit.Layer (Shape left right) (Position left right) (next left right)
      (TransitiveWitness middle) index :=
  let forward := fun future child =>
    let earlier := proof.2.1.forth future child
    let later := proof.2.2.forth future earlier.1
    (⟨later.1, earlier.1.val, earlier.2, later.2⟩ :
      Σ target : RightChildren left right index future,
        TransitiveWitness middle ⟨future.1, child.val, target.val⟩)
  let backward := fun future child =>
    let later := proof.2.2.back future child
    let earlier := proof.2.1.back future later.1
    (⟨earlier.1, later.1.val, earlier.2, later.2⟩ :
      Σ target : LeftChildren left right index future,
        TransitiveWitness middle ⟨future.1, target.val, child.val⟩)
  ⟨fun future => ⟨fun child => (forward future child).1, fun child => (backward future child).1⟩,
    fun ⟨future, position⟩ => match position with
      | .inl child => (forward future child).2
      | .inr child => (backward future child).2⟩

def trans {point : D} {first : left.nodes.obj point} {between : middle.nodes.obj point}
    {second : right.nodes.obj point} (earlier : Realizer left middle point first between)
    (later : Realizer middle right point between second) : Realizer left right point first second :=
  IndexedLimit.corec (Shape left right) (Position left right) (next left right)
    (transitiveStep middle) ⟨between, earlier, later⟩

end Realizer

section Coiteration

variable {witness : (point : D) → left.nodes.obj point → right.nodes.obj point → Type v}
variable (forth : ∀ point first second, witness point first second →
  (future : Future point) → (child : Child left future.1 (left.nodes.map future.2 first)) →
    Σ matched : Child right future.1 (right.nodes.map future.2 second),
      witness future.1 child.val matched.val)
variable (back : ∀ point first second, witness point first second →
  (future : Future point) → (child : Child right future.1 (right.nodes.map future.2 second)) →
    Σ matched : Child left future.1 (left.nodes.map future.2 first),
      witness future.1 matched.val child.val)

def coiterationStep (index : Index left right)
    (proof : witness index.1 index.2.1 index.2.2) :
    IndexedLimit.Layer (Shape left right) (Position left right) (next left right)
      (fun index => witness index.1 index.2.1 index.2.2) index :=
  ⟨fun future =>
    ⟨fun child => (forth _ _ _ proof future child).1,
      fun child => (back _ _ _ proof future child).1⟩,
    fun ⟨future, position⟩ => match position with
      | .inl child => (forth _ _ _ proof future child).2
      | .inr child => (back _ _ _ proof future child).2⟩

def corec {point : D} {first : left.nodes.obj point} {second : right.nodes.obj point}
    (proof : witness point first second) : Realizer left right point first second :=
  IndexedLimit.corec (Shape left right) (Position left right) (next left right)
    (coiterationStep left right forth back) proof

end Coiteration

namespace Realizer

variable {left right}

def futureForth {origin point : D} {first : left.nodes.obj origin}
    {second : right.nodes.obj origin} (arrival : origin ⟶ point)
    (proof : Realizer left right origin first second) (future : Future point)
    (child : Child left future.1 (left.nodes.map future.2 (left.nodes.map arrival first))) :
    Σ matched : Child right future.1 (right.nodes.map future.2 (right.nodes.map arrival second)),
      Realizer left right future.1 child.val matched.val :=
  let answer := proof.forth ⟨future.1, arrival ≫ future.2⟩
    (castChild left (left.nodes.map_comp_apply arrival future.2 first).symm child)
  ⟨castChild right (right.nodes.map_comp_apply arrival future.2 second) answer.1, answer.2⟩

def futureBack {origin point : D} {first : left.nodes.obj origin}
    {second : right.nodes.obj origin} (arrival : origin ⟶ point)
    (proof : Realizer left right origin first second) (future : Future point)
    (child : Child right future.1 (right.nodes.map future.2 (right.nodes.map arrival second))) :
    Σ matched : Child left future.1 (left.nodes.map future.2 (left.nodes.map arrival first)),
      Realizer left right future.1 matched.val child.val :=
  let answer := proof.back ⟨future.1, arrival ≫ future.2⟩
    (castChild right (right.nodes.map_comp_apply arrival future.2 second).symm child)
  ⟨castChild left (left.nodes.map_comp_apply arrival future.2 first) answer.1, answer.2⟩

abbrev RestrictionWitness (index : Index left right) : Type u :=
  Σ origin : Index left right,
    Σ arrival : origin.1 ⟶ index.1,
      Realizer left right origin.1 origin.2.1 origin.2.2 ×
        PLift (left.nodes.map arrival origin.2.1 = index.2.1) ×
        PLift (right.nodes.map arrival origin.2.2 = index.2.2)

def restrictionStep (index : Index left right) (retained : RestrictionWitness index) :
    IndexedLimit.Layer (Shape left right) (Position left right) (next left right)
      RestrictionWitness index := by
  rcases index with ⟨point, first, second⟩
  rcases retained with ⟨⟨origin, earlierFirst, earlierSecond⟩, arrival, proof, ⟨firstSame⟩, ⟨secondSame⟩⟩
  change origin ⟶ point at arrival
  change Realizer left right origin earlierFirst earlierSecond at proof
  change left.nodes.map arrival earlierFirst = first at firstSame
  change right.nodes.map arrival earlierSecond = second at secondSame
  subst first second
  let forward := fun future child => futureForth arrival proof future child
  let backward := fun future child => futureBack arrival proof future child
  exact ⟨fun future => ⟨fun child => (forward future child).1, fun child => (backward future child).1⟩,
    fun ⟨future, position⟩ => match position with
      | .inl child => ⟨⟨future.1, child.val, (forward future child).1.val⟩,
          𝟙 future.1, (forward future child).2,
          ⟨left.nodes.map_id_apply _ _⟩, ⟨right.nodes.map_id_apply _ _⟩⟩
      | .inr child => ⟨⟨future.1, (backward future child).1.val, child.val⟩,
          𝟙 future.1, (backward future child).2,
          ⟨left.nodes.map_id_apply _ _⟩, ⟨right.nodes.map_id_apply _ _⟩⟩⟩

def restrict {origin point : D} {first : left.nodes.obj origin}
    {second : right.nodes.obj origin} (arrival : origin ⟶ point)
    (proof : Realizer left right origin first second) :
    Realizer left right point (left.nodes.map arrival first) (right.nodes.map arrival second) :=
  IndexedLimit.corec (Shape left right) (Position left right) (next left right)
    restrictionStep ⟨⟨origin, first, second⟩, arrival, proof, ⟨rfl⟩, ⟨rfl⟩⟩

def currentForth {point : D} {first : left.nodes.obj point} {second : right.nodes.obj point}
    (proof : Realizer left right point first second) (child : Child left point first) :
    Σ matched : Child right point second, Realizer left right point child.val matched.val :=
  let answer := proof.forth ⟨point, 𝟙 point⟩
    (castChild left (left.nodes.map_id_apply point first).symm child)
  ⟨castChild right (right.nodes.map_id_apply point second) answer.1, answer.2⟩

def currentBack {point : D} {first : left.nodes.obj point} {second : right.nodes.obj point}
    (proof : Realizer left right point first second) (child : Child right point second) :
    Σ matched : Child left point first, Realizer left right point matched.val child.val :=
  let answer := proof.back ⟨point, 𝟙 point⟩
    (castChild right (right.nodes.map_id_apply point second).symm child)
  ⟨castChild left (left.nodes.map_id_apply point first) answer.1, answer.2⟩

end Realizer

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizers
