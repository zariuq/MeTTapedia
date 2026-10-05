import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualUniverseCodes

/-!
# Natural equivalences of material dependent families

An equivalence compares actual fibre carriers, restriction maps and complete
material values. Its comprehension maps retain the original parent point
and act on the decoded dependent coordinate. Their explicit inverses,
projection squares and material label squares support transport of
dependent formation contexts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialEquivalence

open CategoryTheory ContextualGeneratedUniverse
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C : Type u} [Category.{u} C]
variable {context : LabelledContext C}

structure Equivalence (first second : MaterialFamily context) where
  fibre : (point : context.base.Elements) → first.family.obj point ≃ second.family.obj point
  naturality : ∀ {point next : context.base.Elements} (step : point ⟶ next) (term : first.family.obj point),
    fibre next (first.family.map step term) = second.family.map step (fibre point term)
  value : ∀ (point : context.base.Elements) (term : first.family.obj point),
    (second.model point).value (fibre point term) = (first.model point).value term

namespace Equivalence

variable {first second third : MaterialFamily context}

def refl (family : MaterialFamily context) : Equivalence family family where
  fibre _ := Equiv.refl _
  naturality _ _ := rfl
  value _ _ := rfl

def symm (equivalence : Equivalence first second) : Equivalence second first where
  fibre point := (equivalence.fibre point).symm
  naturality {point next} step term := by
    apply (equivalence.fibre next).injective
    exact ((equivalence.naturality step _).trans
      ((congrArg (second.family.map step) ((equivalence.fibre point).apply_symm_apply term)).trans
        ((equivalence.fibre next).apply_symm_apply _).symm)).symm
  value point term :=
    (equivalence.value point ((equivalence.fibre point).symm term)).symm.trans
      (congrArg (second.model point).value ((equivalence.fibre point).apply_symm_apply term))

def trans (earlier : Equivalence first second) (later : Equivalence second third) : Equivalence first third where
  fibre point := (earlier.fibre point).trans (later.fibre point)
  naturality step term :=
    (congrArg (later.fibre _) (earlier.naturality step term)).trans (later.naturality step _)
  value point term := (later.value point _).trans (earlier.value point term)

def hom (equivalence : Equivalence first second) : NatTrans first.family second.family where
  app point := TypeCat.ofHom (equivalence.fibre point)
  naturality _ _ step := by
    apply ConcreteCategory.hom_ext
    exact equivalence.naturality step

def inverse (equivalence : Equivalence first second) : NatTrans second.family first.family :=
  equivalence.symm.hom

theorem hom_inverse (equivalence : Equivalence first second) :
    compose equivalence.hom equivalence.inverse = identity first.family := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact (equivalence.fibre point).symm_apply_apply

theorem inverse_hom (equivalence : Equivalence first second) :
    compose equivalence.inverse equivalence.hom = identity second.family := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact (equivalence.fibre point).apply_symm_apply

def sections (equivalence : Equivalence first second) : first.family.sections ≃ second.family.sections where
  toFun term := ⟨fun point => equivalence.fibre point (term.val point), by
    intro point next step
    exact (equivalence.naturality step (term.val point)).symm.trans
      (congrArg (equivalence.fibre next) (term.property step))⟩
  invFun term := ⟨fun point => (equivalence.fibre point).symm (term.val point), by
    intro point next step
    exact (equivalence.symm.naturality step (term.val point)).symm.trans
      (congrArg (equivalence.fibre next).symm (term.property step))⟩
  left_inv term := Subtype.ext (funext fun point => (equivalence.fibre point).symm_apply_apply (term.val point))
  right_inv term := Subtype.ext (funext fun point => (equivalence.fibre point).apply_symm_apply (term.val point))

theorem sections_value (equivalence : Equivalence first second) (term : first.family.sections)
    (point : context.base.Elements) :
    (second.model point).value ((equivalence.sections term).val point) = (first.model point).value (term.val point) :=
  equivalence.value point (term.val point)

/-- Carrier equality follows from the two constructed fibre decoders and
the full value law. It is not a substitute for restriction naturality. -/
theorem carrier (equivalence : Equivalence first second) (point : context.base.Elements) :
    (first.model point).carrier = (second.model point).carrier := by
  apply HSet.ext
  intro value
  constructor
  · intro belongs
    have reading := (equivalence.value point ((first.model point).decode ⟨value, belongs⟩)).trans
      ((first.model point).value_decode ⟨value, belongs⟩)
    exact Eq.mp (congrArg (fun output : HSet.{u} => output ∈ (second.model point).carrier) reading)
      ((second.model point).value_mem _)
  · intro belongs
    have reading := (equivalence.symm.value point ((second.model point).decode ⟨value, belongs⟩)).trans
      ((second.model point).value_decode ⟨value, belongs⟩)
    exact Eq.mp (congrArg (fun output : HSet.{u} => output ∈ (first.model point).carrier) reading)
      ((first.model point).value_mem _)

def comprehension (equivalence : Equivalence first second) : NatTrans first.extension.base second.extension.base where
  app world := TypeCat.ofHom fun receipt => ⟨receipt.1, equivalence.fibre ⟨world, receipt.1⟩ receipt.2⟩
  naturality {world later} step := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact Sigma.ext rfl (heq_of_eq (equivalence.naturality
      (CategoryOfElements.homMk ⟨world, receipt.1⟩
        ⟨later, context.base.map step receipt.1⟩ step rfl) receipt.2))

def comprehensionInverse (equivalence : Equivalence first second) : NatTrans second.extension.base first.extension.base :=
  equivalence.symm.comprehension

theorem comprehension_inverse (equivalence : Equivalence first second) :
    compose equivalence.comprehension equivalence.comprehensionInverse = identity first.extension.base := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  exact Sigma.ext rfl (heq_of_eq ((equivalence.fibre ⟨world, receipt.1⟩).symm_apply_apply receipt.2))

theorem inverse_comprehension (equivalence : Equivalence first second) :
    compose equivalence.comprehensionInverse equivalence.comprehension = identity second.extension.base := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  exact Sigma.ext rfl (heq_of_eq ((equivalence.fibre ⟨world, receipt.1⟩).apply_symm_apply receipt.2))

theorem comprehension_projection (equivalence : Equivalence first second) :
    compose equivalence.comprehension (PowerClassPresheafProducts.projection second.family) =
      PowerClassPresheafProducts.projection first.family := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

theorem comprehension_label (equivalence : Equivalence first second) (point : first.extension.base.Elements) :
    second.extension.labels.reading ((PowerClassPresheafProducts.elementMap equivalence.comprehension).obj point) =
      first.extension.labels.reading point := by
  change HSet.mk (AccessiblePointedGraph.kpairGraph _ _) = HSet.mk (AccessiblePointedGraph.kpairGraph _ _)
  rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph,
    PresentedType.mk_termGraph, PresentedType.mk_termGraph]
  change (context.labels.reading ⟨point.1, point.2.1⟩).kpair
    ((second.model ⟨point.1, point.2.1⟩).value (equivalence.fibre ⟨point.1, point.2.1⟩ point.2.2)) = _
  exact congrArg (HSet.kpair (context.labels.reading ⟨point.1, point.2.1⟩))
    (equivalence.value ⟨point.1, point.2.1⟩ point.2.2)

theorem comprehension_section (equivalence : Equivalence first second) (term : first.family.sections) :
    compose (PowerClassPresheafProducts.sectionMap first.family term) equivalence.comprehension =
      PowerClassPresheafProducts.sectionMap second.family (equivalence.sections term) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro point
  rfl

def reindex (equivalence : Equivalence first second) {other : LabelledContext C}
    (change : NatTrans other.base context.base) : Equivalence (first.reindex change) (second.reindex change) where
  fibre point := equivalence.fibre ((PowerClassPresheafProducts.elementMap change).obj point)
  naturality step term := equivalence.naturality ((PowerClassPresheafProducts.elementMap change).map step) term
  value point term := equivalence.value ((PowerClassPresheafProducts.elementMap change).obj point) term

/-- A dependent body is moved through the actual inverse comprehension
map. Its native restrictions and fibre dictionaries are both retained. -/
def transportBody (equivalence : Equivalence first second) (body : MaterialFamily first.extension) :
    MaterialFamily second.extension :=
  body.reindex (other := second.extension) equivalence.comprehensionInverse

theorem transportBody_roundtrip (equivalence : Equivalence first second) (body : MaterialFamily first.extension) :
    (equivalence.transportBody body).reindex (other := first.extension) equivalence.comprehension = body :=
  (ContextualUniverseCodes.MaterialFamily.reindex_comp body equivalence.comprehension equivalence.comprehensionInverse).trans
    ((congrArg (fun change : NatTrans first.extension.base first.extension.base => body.reindex change)
      equivalence.comprehension_inverse).trans
      (ContextualUniverseCodes.MaterialFamily.reindex_identity body))

end Equivalence

def ofEquality {first second : MaterialFamily context} (same : first = second) : Equivalence first second := by
  cases same
  exact Equivalence.refl first

namespace Controls

theorem unit_empty_obstruction (point : context.base.Elements) :
    ¬ Nonempty (Equivalence (MaterialFamily.unit context) (MaterialFamily.empty context)) := by
  rintro ⟨equivalence⟩
  have same := equivalence.carrier point
  have unitValue : ((MaterialFamily.unit context).model point).carrier = {∅} :=
    (AccessiblePointedGraph.mk_singletonGraph AccessiblePointedGraph.empty).trans
      (congrArg (fun value : HSet.{u} => ({value} : HSet.{u})) HSet.mk_empty)
  have emptyValue : ((MaterialFamily.empty context).model point).carrier = ∅ := HSet.mk_empty
  exact HSet.empty_ne_singleton_empty (emptyValue.symm.trans (same.symm.trans unitValue))

theorem growing_unit_empty_obstruction :
    ¬ Nonempty (Equivalence (MaterialFamily.unit Growing.context) (MaterialFamily.empty Growing.context)) :=
  unit_empty_obstruction Growing.old

abbrev pairFamily := Growing.input.sigma Growing.body

def swap (point : Growing.context.base.Elements) : pairFamily.family.obj point ≃ pairFamily.family.obj point where
  toFun pair := ⟨pair.2, pair.1⟩
  invFun pair := ⟨pair.2, pair.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

def reversedDictionary : MaterialFamily Growing.context where
  family := pairFamily.family
  model point := (pairFamily.model point).relabel (swap point)

def coordinateEquivalence : Equivalence pairFamily reversedDictionary where
  fibre := swap
  naturality _ _ := rfl
  value point pair := (PresentedType.relabel_value _ _ _).trans
    (congrArg (pairFamily.model point).value ((swap point).symm_apply_apply pair))

def mixedPair : pairFamily.family.obj Growing.newPoint :=
  ⟨Growing.emptySection.val Growing.newPoint, Growing.positiveSection.val Growing.newPoint⟩

theorem coordinate_swap_changes_pair : swap Growing.newPoint mixedPair ≠ mixedPair := by
  intro same
  have values := congrArg (fun pair : pairFamily.family.obj Growing.newPoint =>
    (Growing.input.model Growing.newPoint).value pair.1) same
  have positive : (Growing.input.model Growing.newPoint).value (Growing.positiveSection.val Growing.newPoint) = HSet.quineAtom :=
    Growing.positiveSection_value Growing.newRaw
  have empty : (Growing.input.model Growing.newPoint).value (Growing.emptySection.val Growing.newPoint) = ∅ :=
    Growing.emptySection_value Growing.newRaw
  exact HSet.empty_ne_quineAtom (empty.symm.trans (values.symm.trans positive))

theorem coordinate_swap_value :
    (reversedDictionary.model Growing.newPoint).value (swap Growing.newPoint mixedPair) =
      (pairFamily.model Growing.newPoint).value mixedPair :=
  coordinateEquivalence.value Growing.newPoint mixedPair

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialEquivalence
