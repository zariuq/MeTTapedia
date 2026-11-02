import Mettapedia.TypeTheory.IndexedPolynomialGeneratedRepresentation
import Mettapedia.TypeTheory.IndexedPolynomialRecursiveSpaceRepresentation

/-!
# Generated constructor families without ambient induction

A natural-slot presentation acts on arbitrary target carriers through primitive
payload and constructor operations. Injective payloads and separation on encoded source shapes
derive faithfulness of complete source layers, including every active child.
The generated subfamily therefore has a structured initial representation.
Neither ambient induction nor an ambient recursive-space equivalence is used.

The root guard permits arbitrary child functions. Payload faithfulness still
makes its result index unique, which lets a shared family predicate retain
the indices of recursive children. Canonical padding remains explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.IndexedPolynomial.RecursiveSpaceRepresentation

universe uB uI uS uP uD uR
variable {Base : Type uB} {Index : Base → Type uI}
  (presentation : Presentation.{uB,uI,uS,uP} (Base := Base) (Index := Index))
  {Payload : Base → Type uD} {Target : Base → Type uR}
  (pack : ∀ base, (Σ index, presentation.polynomial.Shape base index) → Payload base)
  (empty : ∀ base, Target base)
  (construct : ∀ base, Nat → Payload base → (Nat → Target base) → Target base)

def constructorAlgebra : Algebra presentation.polynomial (fun base _ => Target base) where
  act base index layer := construct base (presentation.tag layer.1) (pack base ⟨index, layer.1⟩)
    ((presentation.coding layer.1).extend (empty base) layer.2)

def ConstructorRoot (base : Base) (index : Index base) (value : Target base) : Prop :=
  ∃ (shape : presentation.polynomial.Shape base index) (children : Nat → Target base),
    value = construct base (presentation.tag shape) (pack base ⟨index, shape⟩) children

def EncodedShapeSeparation : Prop :=
  ∀ base (first second : Σ index, presentation.polynomial.Shape base index)
    (children otherChildren : Nat → Target base),
    construct base (presentation.tag first.2) (pack base first) children =
      construct base (presentation.tag second.2) (pack base second) otherChildren →
        pack base first = pack base second ∧ children = otherChildren

theorem EncodedShapeSeparation.of_raw
    (raw : ∀ base tag payload children otherTag otherPayload otherChildren,
      construct base tag payload children = construct base otherTag otherPayload otherChildren →
        payload = otherPayload ∧ children = otherChildren) :
    EncodedShapeSeparation presentation pack construct := by
  intro base first second children otherChildren same
  exact raw base _ _ _ _ _ _ same

variable (pack_injective : ∀ base, Function.Injective (pack base))
  (fields_injective : EncodedShapeSeparation presentation pack construct)

include pack_injective fields_injective

theorem constructorLayer_injective (base : Base) :
    Function.Injective (fun layer : Σ index, presentation.polynomial.Extension (fun base _ => Target base) base index =>
      (constructorAlgebra presentation pack empty construct).act base layer.1 layer.2) := by
  rintro ⟨firstIndex, firstShape, children⟩ ⟨secondIndex, secondShape, other⟩ same
  obtain ⟨payloads, branches⟩ := fields_injective base ⟨firstIndex, firstShape⟩ ⟨secondIndex, secondShape⟩ _ _ same
  have points := pack_injective base payloads
  have indices := congrArg Sigma.fst points
  cases indices
  have shapes : firstShape = secondShape := eq_of_heq (Sigma.mk.inj points).2
  cases shapes
  apply congrArg (Sigma.mk firstIndex)
  apply congrArg (Sigma.mk firstShape)
  funext position
  have observed := congrFun branches ((presentation.coding firstShape).encode position)
  simpa only [SlotEncoding.extend_at] using observed

theorem constructorAlgebra_injective (base : Base) (index : Index base) :
    Function.Injective ((constructorAlgebra presentation pack empty construct).act base index) := by
  rintro ⟨first, children⟩ ⟨second, other⟩ same
  obtain ⟨payloads, branches⟩ := fields_injective base ⟨index, first⟩ ⟨index, second⟩ _ _ same
  have points := pack_injective base payloads
  have shapes : first = second := eq_of_heq (Sigma.mk.inj points).2
  cases shapes
  apply congrArg (Sigma.mk first)
  funext position
  have observed := congrFun branches ((presentation.coding first).encode position)
  simpa only [SlotEncoding.extend_at] using observed

theorem constructorRoot_unique (base : Base) (value : Target base)
    (first second : Index base)
    (firstRoot : ConstructorRoot presentation pack construct base first value)
    (secondRoot : ConstructorRoot presentation pack construct base second value) : first = second := by
  obtain ⟨firstShape, firstChildren, firstEquation⟩ := firstRoot
  obtain ⟨secondShape, secondChildren, secondEquation⟩ := secondRoot
  have payloads := (fields_injective base ⟨first, firstShape⟩ ⟨second, secondShape⟩ _ _
    (firstEquation.symm.trans secondEquation)).1
  exact congrArg Sigma.fst (pack_injective base payloads)

omit pack_injective fields_injective in
theorem generated_constructorRoot (base : Base) (index : Index base) (value : Target base)
    (generated : Algebra.Generated (constructorAlgebra presentation pack empty construct) base index value) :
    ConstructorRoot presentation pack construct base index value := by
  apply Algebra.generated_least (constructorAlgebra presentation pack empty construct)
    (fun base index value => ConstructorRoot presentation pack construct base index value) ?_ base index value generated
  intro base index shape children _
  exact ⟨shape, (presentation.coding shape).extend (empty base) children, rfl⟩

noncomputable def constructorRepresentation :
    Algebra.Representation presentation.polynomial
      (Algebra.generatedAlgebra (constructorAlgebra presentation pack empty construct)) :=
  Algebra.generatedRepresentation (constructorAlgebra presentation pack empty construct)
    (Algebra.generatedAlgebra_injective _
      (constructorAlgebra_injective presentation pack empty construct pack_injective fields_injective))

def ConstructorFamily (base : Base) (value : Target base) : Prop :=
  ∃ index, Algebra.Generated (constructorAlgebra presentation pack empty construct) base index value

omit pack_injective fields_injective in
theorem constructorFamily_refuses_empty
    (separated : ∀ base tag payload children, construct base tag payload children ≠ empty base)
    (base : Base) : ¬ ConstructorFamily presentation pack empty construct base (empty base) := by
  rintro ⟨index, generated⟩
  obtain ⟨shape, children, equation⟩ := generated_constructorRoot presentation pack empty construct base index (empty base) generated
  exact separated base (presentation.tag shape) (pack base ⟨index, shape⟩) children equation.symm

def GuardedConstructorStep (base : Base) (property : Target base → Prop) (value : Target base) : Prop :=
  ∃ (index : Index base) (shape : presentation.polynomial.Shape base index)
    (children : Nat → Target base),
    value = construct base (presentation.tag shape) (pack base ⟨index, shape⟩) children ∧
    (∀ slot position, (presentation.coding shape).decode slot = some position →
      ConstructorRoot presentation pack construct base (presentation.polynomial.next shape position) (children slot) ∧
        property (children slot)) ∧
    (presentation.coding shape).Canonical (empty base) children

theorem generated_iff_constructorFamily_root (base : Base) (index : Index base) (value : Target base) :
    Algebra.Generated (constructorAlgebra presentation pack empty construct) base index value ↔
      ConstructorFamily presentation pack empty construct base value ∧
        ConstructorRoot presentation pack construct base index value := by
  constructor
  · intro generated
    exact ⟨⟨index, generated⟩, generated_constructorRoot presentation pack empty construct base index value generated⟩
  · rintro ⟨⟨other, generated⟩, root⟩
    have indices := constructorRoot_unique presentation pack construct pack_injective fields_injective base value other index
      (generated_constructorRoot presentation pack empty construct base other value generated) root
    exact indices ▸ generated

theorem indexedFold_injective (base : Base) :
    Function.Injective (fun tree : Σ index, Fix presentation.polynomial base index =>
      Fix.fold presentation.polynomial (constructorAlgebra presentation pack empty construct).act base tree.1 tree.2) := by
  rintro ⟨firstIndex, first⟩ ⟨secondIndex, second⟩ same
  change Fix.fold presentation.polynomial (constructorAlgebra presentation pack empty construct).act base firstIndex first =
    Fix.fold presentation.polynomial (constructorAlgebra presentation pack empty construct).act base secondIndex second at same
  have firstRoot := generated_constructorRoot presentation pack empty construct base firstIndex _
    (Algebra.generated_fold (constructorAlgebra presentation pack empty construct) base firstIndex first)
  have secondRoot := generated_constructorRoot presentation pack empty construct base secondIndex _
    (Algebra.generated_fold (constructorAlgebra presentation pack empty construct) base secondIndex second)
  have indices := constructorRoot_unique presentation pack construct pack_injective fields_injective base _
    firstIndex secondIndex firstRoot (same.symm ▸ secondRoot)
  cases indices
  apply congrArg (Sigma.mk firstIndex)
  exact Algebra.fold_injective (constructorAlgebra presentation pack empty construct)
    (constructorAlgebra_injective presentation pack empty construct pack_injective fields_injective) base firstIndex same

theorem generated_constructor_iff (base : Base) (index : Index base)
    (shape : presentation.polynomial.Shape base index)
    (children : presentation.polynomial.Position shape → Target base) :
    Algebra.Generated (constructorAlgebra presentation pack empty construct) base index
      ((constructorAlgebra presentation pack empty construct).act base index ⟨shape, children⟩) ↔
      ∀ position, Algebra.Generated (constructorAlgebra presentation pack empty construct)
        base (presentation.polynomial.next shape position) (children position) := by
  constructor
  · intro generated
    obtain ⟨tree, same⟩ := (Algebra.generated_iff_fold (constructorAlgebra presentation pack empty construct)
      base index _).mp generated
    cases tree with
    | roll otherShape otherChildren =>
      have layers := constructorAlgebra_injective presentation pack empty construct pack_injective fields_injective base index same
      have shapes := congrArg Sigma.fst layers
      cases shapes
      have branches := eq_of_heq (Sigma.mk.inj layers).2
      intro position
      rw [← congrFun branches position]
      exact Algebra.generated_fold (constructorAlgebra presentation pack empty construct) base _ (otherChildren position)
  · exact Algebra.generated_closed (constructorAlgebra presentation pack empty construct) base index shape children

theorem constructorFamily_fixed (base : Base) (value : Target base) :
    ConstructorFamily presentation pack empty construct base value ↔
      GuardedConstructorStep presentation pack empty construct base
        (ConstructorFamily presentation pack empty construct base) value := by
  constructor
  · rintro ⟨index, generated⟩
    obtain ⟨tree, rfl⟩ := (Algebra.generated_iff_fold
      (constructorAlgebra presentation pack empty construct) base index value).mp generated
    cases tree with
    | roll shape children =>
      let folded := fun position => Fix.fold presentation.polynomial
        (constructorAlgebra presentation pack empty construct).act base _ (children position)
      refine ⟨_, shape, (presentation.coding shape).extend (empty base) folded, rfl, ?_,
        (presentation.coding shape).extend_canonical _ _⟩
      intro slot position decoded
      have atSlot : (presentation.coding shape).extend (empty base) folded slot = folded position := by
        simp only [SlotEncoding.extend, decoded]
      rw [atSlot]
      have child := Algebra.generated_fold (constructorAlgebra presentation pack empty construct) base _ (children position)
      exact ⟨generated_constructorRoot presentation pack empty construct base _ _ child, ⟨_, child⟩⟩
  · rintro ⟨index, shape, children, equation, conditions, canonical⟩
    refine ⟨index, ?_⟩
    have generated : ∀ position, Algebra.Generated (constructorAlgebra presentation pack empty construct)
        base (presentation.polynomial.next shape position) (children ((presentation.coding shape).encode position)) := by
      intro position
      obtain ⟨root, childIndex, child⟩ := conditions _ position ((presentation.coding shape).decode_encode position)
      have indices := constructorRoot_unique presentation pack construct pack_injective fields_injective
        base _ childIndex _ (generated_constructorRoot presentation pack empty construct base _ _ child) root
      exact indices ▸ child
    have result := Algebra.generated_closed (constructorAlgebra presentation pack empty construct)
      base index shape ((presentation.coding shape).restrict children) generated
    change Algebra.Generated (constructorAlgebra presentation pack empty construct) base index
      (construct base (presentation.tag shape) (pack base ⟨index, shape⟩)
        ((presentation.coding shape).extend (empty base) ((presentation.coding shape).restrict children))) at result
    rw [SlotEncoding.extend_restrict _ _ _ canonical] at result
    exact equation.symm ▸ result

omit pack_injective fields_injective in
theorem constructorFamily_least (base : Base) (property : Target base → Prop)
    (closed : ∀ value, GuardedConstructorStep presentation pack empty construct base property value → property value)
    (value : Target base) (generated : ConstructorFamily presentation pack empty construct base value) : property value := by
  obtain ⟨index, member⟩ := generated
  obtain ⟨tree, rfl⟩ := (Algebra.generated_iff_fold
    (constructorAlgebra presentation pack empty construct) base index value).mp member
  clear member
  induction tree with
  | roll shape children hypotheses =>
    apply closed
    let folded := fun position => Fix.fold presentation.polynomial
      (constructorAlgebra presentation pack empty construct).act base _ (children position)
    refine ⟨_, shape, (presentation.coding shape).extend (empty base) folded, rfl, ?_,
      (presentation.coding shape).extend_canonical _ _⟩
    intro slot position decoded
    have atSlot : (presentation.coding shape).extend (empty base) folded slot = folded position := by
      simp only [SlotEncoding.extend, decoded]
    rw [atSlot]
    exact ⟨generated_constructorRoot presentation pack empty construct base _ _
      (Algebra.generated_fold (constructorAlgebra presentation pack empty construct) base _ (children position)),
      hypotheses position⟩

theorem constructorFamily_iff_closed_predicates (base : Base) (value : Target base) :
    ConstructorFamily presentation pack empty construct base value ↔
      ∀ property : Target base → Prop,
        (∀ point, GuardedConstructorStep presentation pack empty construct base property point → property point) →
          property value := by
  constructor
  · intro generated property closed
    exact constructorFamily_least presentation pack empty construct base property closed value generated
  · intro least
    apply least (ConstructorFamily presentation pack empty construct base)
    intro point step
    exact (constructorFamily_fixed presentation pack empty construct pack_injective fields_injective base point).mpr step

#print axioms constructorAlgebra_injective
#print axioms constructorLayer_injective
#print axioms constructorRoot_unique
#print axioms constructorRepresentation
#print axioms constructorFamily_refuses_empty
#print axioms indexedFold_injective
#print axioms generated_constructor_iff
#print axioms generated_iff_constructorFamily_root
#print axioms constructorFamily_fixed
#print axioms constructorFamily_least
#print axioms constructorFamily_iff_closed_predicates

end Mettapedia.TypeTheory.IndexedPolynomial.RecursiveSpaceRepresentation
