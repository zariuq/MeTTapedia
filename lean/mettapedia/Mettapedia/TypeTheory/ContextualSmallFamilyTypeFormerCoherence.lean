import Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers

/-!
# Substitution of constructed small dependent families

Arbitrary parameter maps retain their actual values, including coordinates
forgotten by a noninjective map. Dependent sums commute with reindexing as
whole functors. Independently formed dependent products have constructed
inverse comparisons of complete compatible future sections. Their actual
future arguments, evaluation and universe decoder are preserved.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormerCoherence

open CategoryTheory ContextualWitnessCover ContextualSmallFamilyTypeFormers
open MaterialSets.Hypersets.PowerClassPresheafBaseChange

universe u v w z
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v} {other : D ⥤ Type w}
variable (change : NaturalHom other base) (domain : base.Elements ⥤ Type u)
variable (body : domain.Elements ⥤ Type u)

abbrev domainUnder := ContextualSmallFamilyUniverse.substitutedFamily domain change

def argumentsUnder : (domainUnder change domain).Elements ⥤ domain.Elements where
  obj argument := ⟨(ContextualSmallFamilyUniverse.elementMap change).obj argument.1, argument.2⟩
  map step := CategoryOfElements.homMk (F := domain) _ _
    ((ContextualSmallFamilyUniverse.elementMap change).map step.1) step.2
  map_id _ := rfl
  map_comp _ _ := rfl

def bodyUnder : (domainUnder change domain).Elements ⥤ Type u :=
  ContextualSmallFamilyUniverse.restrict (argumentsUnder change domain) body

theorem sigma_substitution :
    sigma (domainUnder change domain) (bodyUnder change domain body) =
      ContextualSmallFamilyUniverse.substitutedFamily (sigma domain body) change := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem futureDomain_change (point : other.Elements) :
    futureDomain (domainUnder change domain) point =
      futureDomain domain ((ContextualSmallFamilyUniverse.elementMap change).obj point) :=
  ContextualSmallFamilyUniverse.familyCode_substitution domain change point.1 point.2

def futureArgumentChange (point : other.Elements) :
    (futureDomain (domainUnder change domain) point).Elements ⥤
      (futureDomain domain ((ContextualSmallFamilyUniverse.elementMap change).obj point)).Elements :=
  Cat.elementsTransport (futureDomain_change change domain point)

theorem futureArgumentChange_context (point : other.Elements)
    (argument : (futureDomain (domainUnder change domain) point).Elements) :
    ((futureArgumentChange change domain point).obj argument).1 = argument.1 :=
  Cat.elementsTransport_context (futureDomain_change change domain point) argument

theorem futureArgumentChange_value (point : other.Elements)
    (argument : (futureDomain (domainUnder change domain) point).Elements) :
    HEq ((futureArgumentChange change domain point).obj argument).2 argument.2 :=
  Cat.elementsTransport_value (futureDomain_change change domain point) argument

theorem changeFuturePoint_eq (point : other.Elements) (future : Future.Objects point.1) :
    (ContextualSmallFamilyUniverse.futureElement point.1 (change.app point.1 point.2)).obj future =
      (ContextualSmallFamilyUniverse.elementMap change).obj
        ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).obj future) :=
  congrArg (fun value : base.obj future.1 => (⟨future.1, value⟩ : base.Elements))
    (change.naturality future.2 point.2)

theorem futureArgumentChange_embedding (point : other.Elements)
    (argument : (futureDomain (domainUnder change domain) point).Elements) :
    (futureArguments domain ((ContextualSmallFamilyUniverse.elementMap change).obj point)).obj
        ((futureArgumentChange change domain point).obj argument) =
      (argumentsUnder change domain).obj ((futureArguments (domainUnder change domain) point).obj argument) := by
  apply Sigma.ext
    ((congrArg (ContextualSmallFamilyUniverse.futureElement point.1 (change.app point.1 point.2)).obj
      (futureArgumentChange_context change domain point argument)).trans (changeFuturePoint_eq change point argument.1))
  exact futureArgumentChange_value change domain point argument

theorem futureArgumentChange_arrow (point : other.Elements)
    {first second : (futureDomain (domainUnder change domain) point).Elements} (step : first ⟶ second) :
    HEq (((futureArgumentChange change domain point).map step).1.1) step.1.1 :=
  futureArrow_value_heq (futureArgumentChange_context change domain point first)
    (futureArgumentChange_context change domain point second) _ _
    (Cat.elementsTransport_arrow (futureDomain_change change domain point) step)

theorem futureArgumentChange_embedding_arrow (point : other.Elements)
    {first second : (futureDomain (domainUnder change domain) point).Elements} (step : first ⟶ second) :
    HEq ((futureArguments domain ((ContextualSmallFamilyUniverse.elementMap change).obj point)).map
        ((futureArgumentChange change domain point).map step))
      ((argumentsUnder change domain).map ((futureArguments (domainUnder change domain) point).map step)) := by
  apply elementArrow_heq (futureArgumentChange_embedding change domain point first)
    (futureArgumentChange_embedding change domain point second)
  exact ContextualSmallFamilyUniverse.elementsArrow_heq
    (congrArg Sigma.fst (futureArgumentChange_embedding change domain point first))
    (congrArg Sigma.fst (futureArgumentChange_embedding change domain point second)) _ _
    (futureArgumentChange_arrow change domain point step)

theorem futureBody_change (point : other.Elements) :
    ContextualSmallFamilyUniverse.restrict (futureArgumentChange change domain point)
        (futureBody domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point)) =
      futureBody (domainUnder change domain) (bodyUnder change domain body) point := by
  refine Functor.hext (fun argument => congrArg body.obj (futureArgumentChange_embedding change domain point argument)) ?_
  intro first second step
  exact ContextualSmallFamilyUniverse.familyArrow_heq body
    (futureArgumentChange_embedding change domain point first) (futureArgumentChange_embedding change domain point second)
    _ _ (futureArgumentChange_embedding_arrow change domain point step)

theorem elementsTransport_left {E : Type u} [Category.{u} E] {first second : E ⥤ Type u}
    (same : first = second) :
    Cat.compose (Cat.elementsTransport same) (Cat.elementsTransport same.symm) = Cat.identity first.Elements := by
  cases same
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem elementsTransport_right {E : Type u} [Category.{u} E] {first second : E ⥤ Type u}
    (same : first = second) :
    Cat.compose (Cat.elementsTransport same.symm) (Cat.elementsTransport same) = Cat.identity second.Elements :=
  elementsTransport_left same.symm

def sectionCastEquiv {E : Type u} [Category.{u} E] {first second : E ⥤ Type u} (same : first = second) :
    first.sections ≃ second.sections where
  toFun := MaterialSets.Hypersets.PowerClassPresheafProducts.CP.castSection same
  invFun := MaterialSets.Hypersets.PowerClassPresheafProducts.CP.castSection same.symm
  left_inv := MaterialSets.Hypersets.PowerClassPresheafProducts.CP.castSection_reverse same
  right_inv := MaterialSets.Hypersets.PowerClassPresheafProducts.CP.castSection_reverse same.symm

def productComparison (point : other.Elements) :
    ProductAt domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point) ≃
      ProductAt (domainUnder change domain) (bodyUnder change domain body) point :=
  (Cat.sectionEquivOfInverse (futureArgumentChange change domain point)
    (Cat.elementsTransport (futureDomain_change change domain point).symm)
    (elementsTransport_left (futureDomain_change change domain point))
    (elementsTransport_right (futureDomain_change change domain point))
    (futureBody domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point))).trans
      (sectionCastEquiv (futureBody_change change domain body point))

theorem productComparison_value (point : other.Elements)
    (term : ProductAt domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point))
    (argument : (futureDomain (domainUnder change domain) point).Elements) :
    HEq ((productComparison change domain body point term).val argument)
      (term.val ((futureArgumentChange change domain point).obj argument)) :=
  MaterialSets.Hypersets.PowerClassPresheafProducts.CP.castSection_value
    (futureBody_change change domain body point)
    (MaterialSets.Hypersets.PowerClassPresheafProducts.CP.restrictSection
      (futureArgumentChange change domain point)
      (futureBody domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point)) term) argument

theorem futureArgumentChange_prefix {first second : other.Elements} (step : first ⟶ second)
    (argument : (futureDomain (domainUnder change domain) second).Elements) :
    (prefixArguments domain ((ContextualSmallFamilyUniverse.elementMap change).map step)).obj
        ((futureArgumentChange change domain second).obj argument) =
      (futureArgumentChange change domain first).obj
        ((prefixArguments (domainUnder change domain) step).obj argument) := by
  have context :
      ((prefixArguments domain ((ContextualSmallFamilyUniverse.elementMap change).map step)).obj
        ((futureArgumentChange change domain second).obj argument)).1 =
      ((futureArgumentChange change domain first).obj
        ((prefixArguments (domainUnder change domain) step).obj argument)).1 :=
    (prefixArguments_context domain ((ContextualSmallFamilyUniverse.elementMap change).map step) _).trans
      ((congrArg (ContextualSmallFamilyUniverse.futurePrefix step.1).obj
        (futureArgumentChange_context change domain second argument)).trans
        ((prefixArguments_context (domainUnder change domain) step argument).symm.trans
          (futureArgumentChange_context change domain first _).symm))
  exact Sigma.ext context
    (((prefixArguments_value domain ((ContextualSmallFamilyUniverse.elementMap change).map step) _).trans
      (futureArgumentChange_value change domain second argument)).trans
        ((futureArgumentChange_value change domain first _).trans
          (prefixArguments_value (domainUnder change domain) step argument)).symm)

def piSubstitution :
    NatTrans (ContextualSmallFamilyUniverse.substitutedFamily (pi domain body) change)
      (pi (domainUnder change domain) (bodyUnder change domain body)) where
  app point := TypeCat.ofHom (productComparison change domain body point)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro term
    apply Subtype.ext
    funext argument
    exact eq_of_heq ((productComparison_value change domain body second
        (productMap domain body ((ContextualSmallFamilyUniverse.elementMap change).map step) term) argument).trans
      ((productMap_value domain body ((ContextualSmallFamilyUniverse.elementMap change).map step) term
          ((futureArgumentChange change domain second).obj argument)).trans
        ((Cat.dependentValue_heq term.val (futureArgumentChange_prefix change domain step argument)).trans
          ((productComparison_value change domain body first term
              ((prefixArguments (domainUnder change domain) step).obj argument)).symm.trans
            (productMap_value (domainUnder change domain) (bodyUnder change domain body) step
              (productComparison change domain body first term) argument).symm))))

def piSubstitutionInverse :
    NatTrans (pi (domainUnder change domain) (bodyUnder change domain body))
      (ContextualSmallFamilyUniverse.substitutedFamily (pi domain body) change) where
  app point := TypeCat.ofHom (productComparison change domain body point).symm
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro term
    change (productComparison change domain body second).symm
        (productMap (domainUnder change domain) (bodyUnder change domain body) step term) =
      productMap domain body ((ContextualSmallFamilyUniverse.elementMap change).map step)
        ((productComparison change domain body first).symm term)
    apply (productComparison change domain body second).injective
    have natural := congrArg (fun map => map ((productComparison change domain body first).symm term))
      ((piSubstitution change domain body).naturality step)
    exact ((productComparison change domain body second).apply_symm_apply _).trans
      (natural.trans (congrArg
        (productMap (domainUnder change domain) (bodyUnder change domain body) step)
        ((productComparison change domain body first).apply_symm_apply term))).symm

theorem piSubstitution_left :
    composeNat (piSubstitution change domain body) (piSubstitutionInverse change domain body) =
      identityNat (ContextualSmallFamilyUniverse.substitutedFamily (pi domain body) change) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact (productComparison change domain body point).symm_apply_apply

theorem piSubstitution_right :
    composeNat (piSubstitutionInverse change domain body) (piSubstitution change domain body) =
      identityNat (pi (domainUnder change domain) (bodyUnder change domain body)) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact (productComparison change domain body point).apply_symm_apply

theorem futureArgumentChange_current (point : other.Elements)
    (argument : (domainUnder change domain).obj point) :
    (futureArgumentChange change domain point).obj (currentArgument (domainUnder change domain) point argument) =
      currentArgument domain ((ContextualSmallFamilyUniverse.elementMap change).obj point) argument := by
  apply Sigma.ext (futureArgumentChange_context change domain point _)
  exact ((futureArgumentChange_value change domain point _).trans
    (currentArgument_value (domainUnder change domain) point argument)).trans
      (currentArgument_value domain ((ContextualSmallFamilyUniverse.elementMap change).obj point) argument).symm

theorem evaluate_substitution (point : other.Elements)
    (term : ProductAt domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point))
    (argument : (domainUnder change domain).obj point) :
    evaluateValue (domainUnder change domain) (bodyUnder change domain body) point
        (productComparison change domain body point term) argument =
      evaluateValue domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point) term argument :=
  eq_of_heq ((evaluateValue_heq (domainUnder change domain) (bodyUnder change domain body) point
      (productComparison change domain body point term) argument).trans
    ((productComparison_value change domain body point term (currentArgument (domainUnder change domain) point argument)).trans
      ((Cat.dependentValue_heq term.val (futureArgumentChange_current change domain point argument)).trans
        (evaluateValue_heq domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point) term argument).symm)))

def mapSectionNat {E : Type w} [Category.{u} E] {first second : E ⥤ Type z}
    (operation : NatTrans first second) (term : first.sections) : second.sections :=
  ⟨fun point => operation.app point (term.val point), by
    intro firstPoint secondPoint step
    exact (congrArg (fun map => map (term.val firstPoint)) (operation.naturality step)).symm.trans
      (congrArg (operation.app secondPoint) (term.property step))⟩

def productSectionComparison :
    (ContextualSmallFamilyUniverse.substitutedFamily (pi domain body) change).sections ≃
      (pi (domainUnder change domain) (bodyUnder change domain body)).sections where
  toFun := mapSectionNat (piSubstitution change domain body)
  invFun := mapSectionNat (piSubstitutionInverse change domain body)
  left_inv term := by
    apply Subtype.ext
    funext point
    exact (productComparison change domain body point).symm_apply_apply (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact (productComparison change domain body point).apply_symm_apply (term.val point)

/-! ## The constructed universe classifies the formed families -/

theorem sigma_decoder :
    ContextualSmallFamilyUniverse.decodedFamily (ContextualSmallFamilyUniverse.classifier (sigma domain body)) =
      sigma domain body := ContextualSmallFamilyUniverse.decoded_classifier_eq (sigma domain body)

theorem pi_decoder :
    ContextualSmallFamilyUniverse.decodedFamily (ContextualSmallFamilyUniverse.classifier (pi domain body)) =
      pi domain body := ContextualSmallFamilyUniverse.decoded_classifier_eq (pi domain body)

def restrictNat {E : Type v} {K : Type w} [Category.{u} E] [Category.{u} K]
    (contextMap : E ⥤ K) {first second : K ⥤ Type z} (operation : NatTrans first second) :
    NatTrans (ContextualSmallFamilyUniverse.restrict contextMap first)
      (ContextualSmallFamilyUniverse.restrict contextMap second) where
  app point := operation.app (contextMap.obj point)
  naturality _ _ step := operation.naturality (contextMap.map step)

def productCodeComparison (point : other.Elements) :
    NatTrans
      (ContextualSmallFamilyUniverse.familyCode
        (ContextualSmallFamilyUniverse.substitutedFamily (pi domain body) change) point.1 point.2)
      (ContextualSmallFamilyUniverse.familyCode
        (pi (domainUnder change domain) (bodyUnder change domain body)) point.1 point.2) :=
  restrictNat (ContextualSmallFamilyUniverse.futureElement point.1 point.2) (piSubstitution change domain body)

def productCodeComparisonInverse (point : other.Elements) :
    NatTrans
      (ContextualSmallFamilyUniverse.familyCode
        (pi (domainUnder change domain) (bodyUnder change domain body)) point.1 point.2)
      (ContextualSmallFamilyUniverse.familyCode
        (ContextualSmallFamilyUniverse.substitutedFamily (pi domain body) change) point.1 point.2) :=
  restrictNat (ContextualSmallFamilyUniverse.futureElement point.1 point.2) (piSubstitutionInverse change domain body)

theorem productCodeComparison_left (point : other.Elements) :
    composeNat (productCodeComparison change domain body point) (productCodeComparisonInverse change domain body point) =
      identityNat (ContextualSmallFamilyUniverse.familyCode
        (ContextualSmallFamilyUniverse.substitutedFamily (pi domain body) change) point.1 point.2) := by
  apply NatTrans.ext
  funext future
  apply ConcreteCategory.hom_ext
  exact (productComparison change domain body
    ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).obj future)).symm_apply_apply

theorem productCodeComparison_right (point : other.Elements) :
    composeNat (productCodeComparisonInverse change domain body point) (productCodeComparison change domain body point) =
      identityNat (ContextualSmallFamilyUniverse.familyCode
        (pi (domainUnder change domain) (bodyUnder change domain body)) point.1 point.2) := by
  apply NatTrans.ext
  funext future
  apply ConcreteCategory.hom_ext
  exact (productComparison change domain body
    ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).obj future)).apply_symm_apply

theorem productCode_source (point : other.Elements) :
    ContextualSmallFamilyUniverse.familyCode
        (ContextualSmallFamilyUniverse.substitutedFamily (pi domain body) change) point.1 point.2 =
      ContextualSmallFamilyUniverse.familyCode (pi domain body) point.1 (change.app point.1 point.2) :=
  ContextualSmallFamilyUniverse.familyCode_substitution (pi domain body) change point.1 point.2

theorem evaluationEquiv_natural {first second : base.Elements ⥤ Type u}
    (operation : NatTrans first second) (point : base.Elements)
    (term : ContextualSmallFamilyUniverse.decode (ContextualSmallFamilyUniverse.familyCode first point.1 point.2)) :
    ContextualSmallFamilyUniverse.evaluationEquiv second point.1 point.2
        (operation.app ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).obj
          (ContextualSmallFamilyUniverse.root point.1)) term) =
      operation.app point (ContextualSmallFamilyUniverse.evaluationEquiv first point.1 point.2 term) := by
  exact eq_of_heq ((ContextualSmallFamilyUniverse.cast_heq _ _).trans
    (naturalApplication_heq operation (ContextualSmallFamilyUniverse.evaluationPoint_eq point.1 point.2)
      term (ContextualSmallFamilyUniverse.evaluationEquiv first point.1 point.2 term)
      (ContextualSmallFamilyUniverse.cast_heq _ _).symm))

theorem productCode_decoding (point : other.Elements)
    (term : ContextualSmallFamilyUniverse.decode
      (ContextualSmallFamilyUniverse.familyCode
        (ContextualSmallFamilyUniverse.substitutedFamily (pi domain body) change) point.1 point.2)) :
    ContextualSmallFamilyUniverse.evaluationEquiv
        (pi (domainUnder change domain) (bodyUnder change domain body)) point.1 point.2
        ((productCodeComparison change domain body point).app (ContextualSmallFamilyUniverse.root point.1) term) =
      productComparison change domain body point
        (ContextualSmallFamilyUniverse.evaluationEquiv
          (ContextualSmallFamilyUniverse.substitutedFamily (pi domain body) change) point.1 point.2 term) :=
  evaluationEquiv_natural (piSubstitution change domain body) point term

theorem productCode_evaluation (point : other.Elements)
    (term : ContextualSmallFamilyUniverse.decode
      (ContextualSmallFamilyUniverse.familyCode
        (ContextualSmallFamilyUniverse.substitutedFamily (pi domain body) change) point.1 point.2))
    (argument : (domainUnder change domain).obj point) :
    evaluateValue (domainUnder change domain) (bodyUnder change domain body) point
        (ContextualSmallFamilyUniverse.evaluationEquiv
          (pi (domainUnder change domain) (bodyUnder change domain body)) point.1 point.2
          ((productCodeComparison change domain body point).app (ContextualSmallFamilyUniverse.root point.1) term)) argument =
      evaluateValue domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point)
        (ContextualSmallFamilyUniverse.evaluationEquiv
          (ContextualSmallFamilyUniverse.substitutedFamily (pi domain body) change) point.1 point.2 term) argument := by
  rw [productCode_decoding]
  exact evaluate_substitution change domain body point _ argument

theorem domainUnder_id :
    domainUnder (ContextualSmallMapConstructions.identity base) domain = domain := by
  rfl

theorem bodyUnder_id :
    bodyUnder (ContextualSmallMapConstructions.identity base) domain body = body := by
  rfl

theorem domainUnder_comp {third : D ⥤ Type z} (earlier : NaturalHom third other) :
    domainUnder (earlier.comp change) domain = domainUnder earlier (domainUnder change domain) := by
  rfl

theorem bodyUnder_comp {third : D ⥤ Type z} (earlier : NaturalHom third other) :
    bodyUnder (earlier.comp change) domain body =
      bodyUnder earlier (domainUnder change domain) (bodyUnder change domain body) := by
  rfl

theorem elementsTransport_comp {E : Type u} [Category.{u} E] {first middle last : E ⥤ Type u}
    (earlier : first = middle) (later : middle = last) (argument : first.Elements) :
    (Cat.elementsTransport (earlier.trans later)).obj argument =
      (Cat.elementsTransport later).obj ((Cat.elementsTransport earlier).obj argument) := by
  cases earlier
  cases later
  rfl

theorem productComparison_id (point : base.Elements) (term : ProductAt domain body point) :
    productComparison (ContextualSmallMapConstructions.identity base) domain body point term = term := by
  apply Subtype.ext
  funext argument
  exact eq_of_heq ((productComparison_value (ContextualSmallMapConstructions.identity base) domain body point term argument).trans
    (Cat.dependentValue_heq term.val rfl))

theorem futureArgumentChange_comp {third : D ⥤ Type z} (earlier : NaturalHom third other)
    (point : third.Elements)
    (argument : (futureDomain (domainUnder (earlier.comp change) domain) point).Elements) :
    (futureArgumentChange (earlier.comp change) domain point).obj argument =
      (futureArgumentChange change domain ((ContextualSmallFamilyUniverse.elementMap earlier).obj point)).obj
        ((futureArgumentChange earlier (domainUnder change domain) point).obj argument) :=
  elementsTransport_comp (futureDomain_change earlier (domainUnder change domain) point)
    (futureDomain_change change domain ((ContextualSmallFamilyUniverse.elementMap earlier).obj point)) argument

theorem productComparison_comp {third : D ⥤ Type z} (earlier : NaturalHom third other)
    (point : third.Elements)
    (term : ProductAt domain body ((ContextualSmallFamilyUniverse.elementMap (earlier.comp change)).obj point)) :
    productComparison (earlier.comp change) domain body point term =
      productComparison earlier (domainUnder change domain) (bodyUnder change domain body) point
        (productComparison change domain body ((ContextualSmallFamilyUniverse.elementMap earlier).obj point) term) := by
  apply Subtype.ext
  funext argument
  exact eq_of_heq ((productComparison_value (earlier.comp change) domain body point term argument).trans
    ((Cat.dependentValue_heq term.val (futureArgumentChange_comp change domain earlier point argument)).trans
      ((productComparison_value change domain body ((ContextualSmallFamilyUniverse.elementMap earlier).obj point) term
          ((futureArgumentChange earlier (domainUnder change domain) point).obj argument)).symm.trans
        (productComparison_value earlier (domainUnder change domain) (bodyUnder change domain body) point
          (productComparison change domain body ((ContextualSmallFamilyUniverse.elementMap earlier).obj point) term) argument).symm)))

end Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormerCoherence
