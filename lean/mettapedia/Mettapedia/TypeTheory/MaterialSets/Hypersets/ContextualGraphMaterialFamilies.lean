import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphOrderedPairs
import Mettapedia.TypeTheory.ContextualSmallFamilyComprehension

/-!
# Native contextual families with actual material element denotations

A material family retains its native dependent functor and a natural
reading of its actual terms into the varying graph universe. Dependent
sums pair the actual two readings. Material equality may identify native
receipts; the induced small quotient family has an exact natural-consumer
factorization criterion. No inverse to an extensional readout is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFamilies

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualGraphDiagrams ContextualRealizedGraphs
universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}

structure Family (base : D ⥤ Type u) where
  native : base.Elements ⥤ Type u
  reading : NaturalHom (total native) (values D)

variable (family : Family base)

def termValue (point : base.Elements) (term : family.native.obj point) : Value D point.1 :=
  family.reading.app point.1 ⟨point.2, term⟩

def substitute {other : D ⥤ Type u} (change : NaturalHom other base) : Family other where
  native := substitutedFamily family.native change
  reading := (substitutedTotalMap family.native change).comp family.reading

theorem substitute_value {other : D ⥤ Type u} (change : NaturalHom other base)
    (point : other.Elements) (term : (substitute family change).native.obj point) :
    termValue (substitute family change) point term =
      termValue family ((elementMap change).obj point) term := rfl

theorem substitute_native_identity :
    (substitute family (ContextualSmallMapConstructions.identity base)).native = family.native :=
  substitutedFamily_id family.native

theorem substitute_native_composition {other third : D ⥤ Type u}
    (earlier : NaturalHom other base) (later : NaturalHom third other) :
    (substitute (substitute family earlier) later).native =
      (substitute family (later.comp earlier)).native :=
  substitutedFamily_comp family.native earlier later

theorem substitute_value_composition {other third : D ⥤ Type u}
    (earlier : NaturalHom other base) (later : NaturalHom third other)
    (point : third.Elements) (term : (substitute (substitute family earlier) later).native.obj point) :
    termValue (substitute (substitute family earlier) later) point term =
      termValue (substitute family (later.comp earlier)) point term := rfl

theorem termValue_move {first second : base.Elements} (step : first ⟶ second)
    (term : family.native.obj first) :
    move D step.1 (termValue family first term) =
      termValue family second (family.native.map step term) := by
  rcases first with ⟨first, parameter⟩
  rcases second with ⟨second, other⟩
  rcases step with ⟨arrival, follows⟩
  change first ⟶ second at arrival
  change base.map arrival parameter = other at follows
  subst other
  exact family.reading.naturality arrival ⟨parameter, term⟩

def kernel (point : base.Elements) : Setoid (family.native.obj point) where
  r first second := Nonempty (Equal (termValue family point first) (termValue family point second))
  iseqv := {
    refl := fun term => ⟨Equal.refl (termValue family point term)⟩
    symm := fun ⟨same⟩ => ⟨same.symm⟩
    trans := fun ⟨earlier⟩ ⟨later⟩ => ⟨earlier.trans later⟩ }

theorem kernel_move {first second : base.Elements} (step : first ⟶ second)
    {left right : family.native.obj first} (same : (kernel family first).r left right) :
    (kernel family second).r (family.native.map step left) (family.native.map step right) := by
  rcases same with ⟨same⟩
  exact ⟨(Equal.ofEq (termValue_move family step left)).symm.trans
    ((Equal.restrict step.1 same).trans (Equal.ofEq (termValue_move family step right)))⟩

/-- The quotient carrier is constructed from the original-small native
terms. It does not enumerate the larger material universe. -/
def observed : base.Elements ⥤ Type u where
  obj point := Quotient (kernel family point)
  map step := TypeCat.ofHom (Quotient.map (family.native.map step) (fun _ _ same => kernel_move family step same))
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro term
    refine Quotient.inductionOn term (fun receipt => ?_)
    exact congrArg (Quotient.mk (kernel family point)) (family.native.map_id_apply point receipt)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro term
    refine Quotient.inductionOn term (fun receipt => ?_)
    exact congrArg (Quotient.mk (kernel family _)) (family.native.map_comp_apply earlier later receipt)

def observe : NaturalHom family.native (observed family) where
  app point term := Quotient.mk (kernel family point) term
  naturality _ _ := rfl

theorem observed_kernel (point : base.Elements) (first second : family.native.obj point) :
    (observe family).app point first = (observe family).app point second ↔
      Nonempty (Equal (termValue family point first) (termValue family point second)) :=
  Quotient.eq_iff_equiv

variable {output : base.Elements ⥤ Type u}

def Compatible (consumer : NaturalHom family.native output) : Prop :=
  ∀ (point : base.Elements) (first second : family.native.obj point),
    Nonempty (Equal (termValue family point first) (termValue family point second)) →
      consumer.app point first = consumer.app point second

def descend (consumer : NaturalHom family.native output) (compatible : Compatible family consumer) :
    NaturalHom (observed family) output where
  app point := Quotient.lift (consumer.app point) (compatible point)
  naturality {first second} step term := by
    refine Quotient.inductionOn term (fun receipt => ?_)
    exact consumer.naturality step receipt

theorem descend_square (consumer : NaturalHom family.native output) (compatible : Compatible family consumer) :
    (observe family).comp (descend family consumer compatible) = consumer := by
  apply NaturalHom.ext
  intro _ _
  rfl

/-- Compatibility is necessary as well as sufficient for actual natural
factorization through the material observation kernel. -/
theorem descends_iff (consumer : NaturalHom family.native output) :
    (∃ descended : NaturalHom (observed family) output,
      (observe family).comp descended = consumer) ↔ Compatible family consumer := by
  constructor
  · rintro ⟨descended, square⟩ point first second same
    have firstSame := congrArg (fun operation => operation.app point first) square
    have secondSame := congrArg (fun operation => operation.app point second) square
    exact firstSame.symm.trans ((congrArg (descended.app point)
      ((observed_kernel family point first second).mpr same)).trans secondSame)
  · intro compatible
    exact ⟨descend family consumer compatible, descend_square family consumer compatible⟩

def descendedConsumerEquiv :
    {consumer : NaturalHom family.native output // Compatible family consumer} ≃
      NaturalHom (observed family) output where
  toFun consumer := descend family consumer.val consumer.property
  invFun consumer := ⟨(observe family).comp consumer,
    fun point first second same => congrArg (consumer.app point)
      ((observed_kernel family point first second).mpr same)⟩
  left_inv consumer := by
    apply Subtype.ext
    exact descend_square family consumer.val consumer.property
  right_inv consumer := by
    apply NaturalHom.ext
    intro point term
    exact Quotient.inductionOn term (fun _ => rfl)

variable (domain : Family base) (body : Family (total domain.native))

def sumFirst : NaturalHom (total (sigmaDisplayed domain.native body.native)) (total domain.native) where
  app _ receipt := ⟨receipt.1, receipt.2.1⟩
  naturality _ _ := rfl

def sumSecond : NaturalHom (total (sigmaDisplayed domain.native body.native)) (total body.native) where
  app _ receipt := ⟨⟨receipt.1, receipt.2.1⟩, receipt.2.2⟩
  naturality _ _ := rfl

/-- The native dependent sum and both actual element denotations are
constructed together; its terms are genuine ordered pairs. -/
def sigma : Family base where
  native := sigmaDisplayed domain.native body.native
  reading := ContextualGraphOrderedPairs.orderedReading
    ((sumFirst domain body).comp domain.reading) ((sumSecond domain body).comp body.reading)

theorem sum_value (point : base.Elements) (term : (sigma domain body).native.obj point) :
    termValue (sigma domain body) point term = ContextualGraphOrderedPairs.orderedPair
      (termValue domain point term.1)
      (termValue body ((flatten domain.native).obj ⟨point, term.1⟩) term.2) := rfl

/-- The ordered-pair observation identifies precisely its two component
readings. Native body fibres are not transported across this equality. -/
theorem sum_kernel (point : base.Elements) (first second : (sigma domain body).native.obj point) :
    Nonempty (Equal (termValue (sigma domain body) point first) (termValue (sigma domain body) point second)) ↔
      Nonempty (Equal (termValue domain point first.1) (termValue domain point second.1)) ∧
        Nonempty (Equal
          (termValue body ((flatten domain.native).obj ⟨point, first.1⟩) first.2)
          (termValue body ((flatten domain.native).obj ⟨point, second.1⟩) second.2)) :=
  ContextualGraphOrderedPairs.orderedPair_kernel

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFamilies
