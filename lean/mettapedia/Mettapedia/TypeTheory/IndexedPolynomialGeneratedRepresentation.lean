import Mettapedia.TypeTheory.IndexedPolynomialRepresentation
import Mettapedia.TypeTheory.IndexedPolynomialEquivalence

/-!
# Logical generation and structured inductive representations

The intersection of all constructor-closed predicates is exactly the image
of the initial-algebra fold. If the constructor operation is injective on
complete layers with generated children, its generated subfamily is a
structured representation of the original inductive family. No assumption
that every ambient value is generated is needed for this guarded result.

The inverse equivalences are semantic and noncomputable. Executable decoding,
universe bounds for a material-set model and judgmental computation remain
separate obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.IndexedPolynomial.Algebra
universe uB uI uS uP uX uY uZ
variable {Base : Type uB} {Index : Base → Type uI}
  {P : IndexedPolynomial.{uB,uI,uS,uP} Base Index}
  {X : ∀ b, Index b → Type uX} {Y : ∀ b, Index b → Type uY}

def ClosedUnder (algebra : Algebra P X) (predicate : ∀ b i, X b i → Prop) : Prop :=
  ∀ b i (shape : P.Shape b i) (children : ∀ position, X b (P.next shape position)),
    (∀ position, predicate b (P.next shape position) (children position)) →
      predicate b i (algebra.act b i ⟨shape, children⟩)

def Generated (algebra : Algebra P X) (base : Base) (index : Index base) (value : X base index) : Prop :=
  ∀ predicate : ∀ b i, X b i → Prop, ClosedUnder algebra predicate → predicate base index value

theorem generated_closed (algebra : Algebra P X) : ClosedUnder algebra (Generated algebra) := by
  intro base index shape children generated predicate closed
  exact closed base index shape children (fun position => generated position predicate closed)

theorem generated_least (algebra : Algebra P X) (predicate : ∀ b i, X b i → Prop)
    (closed : ClosedUnder algebra predicate) (base : Base) (index : Index base) (value : X base index)
    (generated : Generated algebra base index value) : predicate base index value :=
  generated predicate closed

theorem generated_fold (algebra : Algebra P X) (base : Base) (index : Index base) (tree : Fix P base index) :
    Generated algebra base index (Fix.fold P algebra.act base index tree) := by
  intro predicate closed
  exact Fix.eliminate P (fun b i t => predicate b i (Fix.fold P algebra.act b i t))
    (fun b i shape children hypotheses => closed b i shape _ hypotheses) base index tree

theorem generated_iff_fold (algebra : Algebra P X) (base : Base) (index : Index base) (value : X base index) :
    Generated algebra base index value ↔ ∃ tree : Fix P base index, Fix.fold P algebra.act base index tree = value := by
  constructor
  · intro generated
    apply generated (fun b i x => ∃ tree : Fix P b i, Fix.fold P algebra.act b i tree = x)
    intro b i shape children hypotheses
    let witnesses := fun position => Classical.choose (hypotheses position)
    have agrees : (fun position => Fix.fold P algebra.act b _ (witnesses position)) = children :=
      funext fun position => Classical.choose_spec (hypotheses position)
    refine ⟨Fix.roll shape witnesses, ?_⟩
    rw [Fix.fold_roll]
    exact congrArg (fun branch => algebra.act b i ⟨shape, branch⟩) agrees
  · rintro ⟨tree, rfl⟩
    exact generated_fold algebra base index tree

def GeneratedCarrier (algebra : Algebra P X) (base : Base) (index : Index base) :=
  { value : X base index // Generated algebra base index value }

def generatedAlgebra (algebra : Algebra P X) : Algebra P (GeneratedCarrier algebra) where
  act base index layer :=
    ⟨algebra.act base index ⟨layer.1, fun position => (layer.2 position).val⟩,
      generated_closed algebra base index layer.1 _ (fun position => (layer.2 position).property)⟩

noncomputable def generatedHom (algebra : Algebra P X) : Hom (initial P) (generatedAlgebra algebra) where
  toFun base index tree := ⟨Fix.fold P algebra.act base index tree, generated_fold algebra base index tree⟩
  commutes := by
    intro base index layer
    cases layer
    apply Subtype.ext
    rfl

theorem fold_injective_on_generated (algebra : Algebra P X)
    (constructors : ∀ base index, Function.Injective ((generatedAlgebra algebra).act base index))
    (base : Base) (index : Index base) : Function.Injective (Fix.fold P algebra.act base index) := by
  intro first
  refine Fix.eliminate P
    (fun b i first => ∀ second : Fix P b i,
      Fix.fold P algebra.act b i first = Fix.fold P algebra.act b i second → first = second)
    ?_ base index first
  intro b i shape children hypotheses second same
  cases second with
  | roll otherShape otherChildren =>
      let firstLayer : P.Extension (GeneratedCarrier algebra) b i :=
        ⟨shape, fun position => ⟨Fix.fold P algebra.act b _ (children position),
          generated_fold algebra b _ (children position)⟩⟩
      let secondLayer : P.Extension (GeneratedCarrier algebra) b i :=
        ⟨otherShape, fun position => ⟨Fix.fold P algebra.act b _ (otherChildren position),
          generated_fold algebra b _ (otherChildren position)⟩⟩
      have restricted : firstLayer = secondLayer := constructors b i (Subtype.ext same)
      have layers := congrArg
        (Extension.map P (fun base index (value : GeneratedCarrier algebra base index) => value.val)) restricted
      have shapes := congrArg Sigma.fst layers
      cases shapes
      have branches : (fun position => Fix.fold P algebra.act b _ (children position)) =
          (fun position => Fix.fold P algebra.act b _ (otherChildren position)) :=
        eq_of_heq (Sigma.mk.inj layers).2
      exact congrArg (Fix.roll shape) (funext fun position =>
        hypotheses position (otherChildren position) (congrFun branches position))

private theorem forget_layer_injective (algebra : Algebra P X) (base : Base) (index : Index base) :
    Function.Injective (Extension.map P (fun base index (value : GeneratedCarrier algebra base index) => value.val)
      (base := base) (index := index)) := by
  intro ⟨first, children⟩ ⟨second, other⟩ same
  have shapes := congrArg Sigma.fst same
  cases shapes
  apply congrArg (Sigma.mk first)
  funext position
  apply Subtype.ext
  exact congrFun (eq_of_heq (Sigma.mk.inj same).2) position

theorem generatedAlgebra_injective (algebra : Algebra P X)
    (constructors : ∀ base index, Function.Injective (algebra.act base index)) :
    ∀ base index, Function.Injective ((generatedAlgebra algebra).act base index) := by
  intro base index ⟨first, children⟩ ⟨second, other⟩ same
  apply forget_layer_injective algebra base index
  exact constructors base index (congrArg Subtype.val same)

theorem fold_injective (algebra : Algebra P X)
    (constructors : ∀ base index, Function.Injective (algebra.act base index))
    (base : Base) (index : Index base) : Function.Injective (Fix.fold P algebra.act base index) :=
  fold_injective_on_generated algebra (generatedAlgebra_injective algebra constructors) base index

noncomputable def generatedRepresentation (algebra : Algebra P X)
    (constructors : ∀ base index, Function.Injective ((generatedAlgebra algebra).act base index)) :
    Representation P (generatedAlgebra algebra) where
  toEquiv base index := Equiv.ofBijective ((generatedHom algebra).toFun base index) (by
    constructor
    · intro first second same
      exact fold_injective_on_generated algebra constructors base index (congrArg Subtype.val same)
    · intro value
      obtain ⟨tree, agrees⟩ := (generated_iff_fold algebra base index value.val).mp value.property
      exact ⟨tree, Subtype.ext agrees⟩)
  commutes := (generatedHom algebra).commutes

@[simp] theorem generatedRepresentation_value (algebra : Algebra P X)
    (constructors : ∀ base index, Function.Injective ((generatedAlgebra algebra).act base index))
    (base : Base) (index : Index base) (tree : Fix P base index) :
    ((generatedRepresentation algebra constructors).toEquiv base index tree).val =
      Fix.fold P algebra.act base index tree := rfl

noncomputable def representationOfGeneration (algebra : Algebra P X)
    (constructors : ∀ base index, Function.Injective ((generatedAlgebra algebra).act base index))
    (generated : ∀ base index value, Generated algebra base index value) : Representation P algebra where
  toEquiv base index := Equiv.ofBijective (Fix.fold P algebra.act base index)
    ⟨fold_injective_on_generated algebra constructors base index,
      fun value => (generated_iff_fold algebra base index value).mp (generated base index value)⟩
  commutes := (foldHom algebra).commutes

@[instance_reducible] noncomputable def uniqueHomFromGenerated (algebra : Algebra P X)
    (constructors : ∀ base index, Function.Injective ((generatedAlgebra algebra).act base index)) (target : Algebra P Y) :
    Unique (Hom (generatedAlgebra algebra) target) := by
  let representation := generatedRepresentation algebra constructors
  refine { default := Hom.compose (foldHom target) representation.symm.toHom, uniq := ?_ }
  intro mapping
  apply Hom.ext
  intro base index value
  obtain ⟨tree, rfl⟩ := (representation.toEquiv base index).surjective value
  change mapping.toFun base index (representation.toEquiv base index tree) =
    Fix.fold P target.act base index
      ((representation.toEquiv base index).symm (representation.toEquiv base index tree))
  rw [Equiv.symm_apply_apply]
  exact hom_eq_fold target (Hom.compose mapping representation.toHom) base index tree

theorem Hom.maps_generated {source : Algebra P X} {target : Algebra P Y} (mapping : Hom source target)
    (base : Base) (index : Index base) (value : X base index)
    (generated : Generated source base index value) : Generated target base index (mapping.toFun base index value) := by
  intro predicate closed
  apply generated (fun b i x => predicate b i (mapping.toFun b i x))
  intro b i shape children hypotheses
  have step := closed b i shape (fun position => mapping.toFun b _ (children position)) hypotheses
  exact (mapping.commutes b i ⟨shape, children⟩).symm ▸ step

def Hom.onGenerated {source : Algebra P X} {target : Algebra P Y} (mapping : Hom source target) :
    Hom (generatedAlgebra source) (generatedAlgebra target) where
  toFun base index value := ⟨mapping.toFun base index value.val,
    mapping.maps_generated base index value.val value.property⟩
  commutes := by
    intro base index layer
    apply Subtype.ext
    exact mapping.commutes base index ⟨layer.1, fun position => (layer.2 position).val⟩

theorem Hom.onGenerated_identity (algebra : Algebra P X)
    (base : Base) (index : Index base) (value : GeneratedCarrier algebra base index) :
    (Hom.identity algebra).onGenerated.toFun base index value = value := by
  apply Subtype.ext
  rfl

theorem Hom.onGenerated_compose {Z : ∀ b, Index b → Type uZ}
    {source : Algebra P X} {middle : Algebra P Y} {target : Algebra P Z}
    (later : Hom middle target) (earlier : Hom source middle)
    (base : Base) (index : Index base) (value : GeneratedCarrier source base index) :
    (Hom.compose later earlier).onGenerated.toFun base index value =
      later.onGenerated.toFun base index (earlier.onGenerated.toFun base index value) := by
  apply Subtype.ext
  rfl

#print axioms generated_iff_fold
#print axioms fold_injective_on_generated
#print axioms fold_injective
#print axioms generatedRepresentation
#print axioms representationOfGeneration
#print axioms uniqueHomFromGenerated
#print axioms Hom.onGenerated
end Mettapedia.TypeTheory.IndexedPolynomial.Algebra

namespace Mettapedia.TypeTheory.IndexedPolynomial.SignatureEquiv
universe uB uI uS uP uT uQ uX
variable {Base : Type uB} {Index : Base → Type uI}
  {P : IndexedPolynomial.{uB,uI,uS,uP} Base Index}
  {Q : IndexedPolynomial.{uB,uI,uT,uQ} Base Index}
  {X : ∀ base, Index base → Type uX}

/-- Changing a complete constructor signature preserves logical generation
under the transported constructor algebra, at the original value and index. -/
theorem generated_pull_iff (comparison : SignatureEquiv P Q) (algebra : Algebra Q X)
    (base : Base) (index : Index base) (value : X base index) :
    Algebra.Generated (comparison.pullAlgebra algebra) base index value ↔
      Algebra.Generated algebra base index value := by
  rw [Algebra.generated_iff_fold, Algebra.generated_iff_fold]
  constructor
  · rintro ⟨tree, same⟩
    exact ⟨comparison.toFix base index tree,
      (comparison.fold_toFix algebra base index tree).trans same⟩
  · rintro ⟨tree, same⟩
    refine ⟨comparison.fromFix base index tree, ?_⟩
    have preserved := comparison.fold_toFix algebra base index (comparison.fromFix base index tree)
    rw [comparison.toFix_fromFix] at preserved
    exact preserved.symm.trans same

#print axioms generated_pull_iff
end Mettapedia.TypeTheory.IndexedPolynomial.SignatureEquiv
