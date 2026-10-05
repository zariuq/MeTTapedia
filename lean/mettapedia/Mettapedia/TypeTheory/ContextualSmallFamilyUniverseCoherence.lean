import Mettapedia.TypeTheory.ContextualSmallFamilyUniverse

/-!
# Classification pullbacks and substitution for coherent small families

The identity decoder's total family is compared with the literal pullback
of its universal projection. Both directions, their naturality, and their
whole inverse laws are constructed. Combining this with the complete
displayed-family decoding theorem classifies actual small displayed
families over arbitrarily larger parameter presheaves.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyUniverse

open CategoryTheory ContextualWitnessCover ContextualImageFactorization

universe u v w z
variable {D : Type u} [Category.{u} D]
variable {base : D ⥤ Type v}

abbrev GenericPullback (operation : NaturalHom base universeFamily) :=
  pullback universalProjection operation

def genericForward (operation : NaturalHom base universeFamily) :
    NaturalHom (total (decodedFamily operation)) (GenericPullback operation) where
  app point receipt := ⟨(⟨operation.app point receipt.1, receipt.2⟩, receipt.1), rfl⟩
  naturality {first second} step receipt := by
    apply Subtype.ext
    refine Prod.ext (Sigma.ext (operation.naturality step receipt.1) ?_) rfl
    let original := CategoryOfElements.homMk (F := universeFamily)
      ⟨first, operation.app first receipt.1⟩
      ⟨second, codeMap step (operation.app first receipt.1)⟩ step rfl
    let changed := (elementMap operation).map
      (CategoryOfElements.homMk (F := base)
        ⟨first, receipt.1⟩ ⟨second, base.map step receipt.1⟩ step rfl)
    exact (decoder_map_heq original receipt.2).trans (decoder_map_heq changed receipt.2).symm

def genericBackwardValue (operation : NaturalHom base universeFamily) (point : D)
    (receipt : (GenericPullback operation).obj point) : TotalAt (decodedFamily operation) point :=
  ⟨receipt.val.2,
    cast (congrArg (fun code : Code point => decode code) receipt.property) receipt.val.1.2⟩

theorem generic_left (operation : NaturalHom base universeFamily) (point : D)
    (receipt : TotalAt (decodedFamily operation) point) :
    genericBackwardValue operation point ((genericForward operation).app point receipt) = receipt := rfl

theorem generic_right (operation : NaturalHom base universeFamily) (point : D)
    (receipt : (GenericPullback operation).obj point) :
    (genericForward operation).app point (genericBackwardValue operation point receipt) = receipt := by
  rcases receipt with ⟨⟨⟨code, term⟩, value⟩, same⟩
  change code = operation.app point value at same
  subst code
  rfl

theorem genericForward_injective (operation : NaturalHom base universeFamily) (point : D) :
    Function.Injective ((genericForward operation).app point) := by
  intro first second same
  exact (generic_left operation point first).symm.trans
    ((congrArg (genericBackwardValue operation point) same).trans (generic_left operation point second))

def genericBackward (operation : NaturalHom base universeFamily) :
    NaturalHom (GenericPullback operation) (total (decodedFamily operation)) where
  app := genericBackwardValue operation
  naturality {first second} step receipt := by
    apply genericForward_injective operation second
    exact ((genericForward operation).naturality step
      (genericBackwardValue operation first receipt)).symm.trans
      ((congrArg ((GenericPullback operation).map step) (generic_right operation first receipt)).trans
        (generic_right operation second ((GenericPullback operation).map step receipt)).symm)

def genericEquiv (operation : NaturalHom base universeFamily) (point : D) :
    TotalAt (decodedFamily operation) point ≃ (GenericPullback operation).obj point where
  toFun := (genericForward operation).app point
  invFun := (genericBackward operation).app point
  left_inv := generic_left operation point
  right_inv := generic_right operation point

def genericSectionEquiv (operation : NaturalHom base universeFamily) :
    (total (decodedFamily operation)).sections ≃ (GenericPullback operation).sections where
  toFun := (genericForward operation).mapSection
  invFun := (genericBackward operation).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact generic_left operation point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact generic_right operation point (term.val point)

theorem genericForward_parameter (operation : NaturalHom base universeFamily) :
    (genericForward operation).comp (pullbackSecond universalProjection operation) =
      projection (decodedFamily operation) := by
  apply NaturalHom.ext
  intro _ _
  rfl

def totalCast {first second : base.Elements ⥤ Type u} (same : first = second) :
    NaturalHom (total first) (total second) where
  app point receipt := ⟨receipt.1,
    cast (congrArg (fun family : base.Elements ⥤ Type u => family.obj ⟨point, receipt.1⟩) same) receipt.2⟩
  naturality := by
    cases same
    intro _ _ _ _
    rfl

theorem totalCast_reverse {first second : base.Elements ⥤ Type u} (same : first = second)
    (point : D) (receipt : TotalAt first point) :
    (totalCast same.symm).app point ((totalCast same).app point receipt) = receipt := by
  cases same
  rfl

theorem totalCast_value_heq {first second : base.Elements ⥤ Type u} (same : first = second)
    (point : D) (receipt : TotalAt first point) :
    HEq ((totalCast same).app point receipt).2 receipt.2 := cast_heq _ _

variable (family : base.Elements ⥤ Type u)

abbrev ClassificationPullback := GenericPullback (classifier family)

def classificationForward : NaturalHom (total family) (ClassificationPullback family) :=
  (totalCast (decoded_classifier_eq family).symm).comp (genericForward (classifier family))

def classificationBackward : NaturalHom (ClassificationPullback family) (total family) :=
  (genericBackward (classifier family)).comp (totalCast (decoded_classifier_eq family))

theorem classification_left (point : D) (receipt : TotalAt family point) :
    (classificationBackward family).app point ((classificationForward family).app point receipt) = receipt := by
  exact (congrArg ((totalCast (decoded_classifier_eq family)).app point)
    (generic_left (classifier family) point
      ((totalCast (decoded_classifier_eq family).symm).app point receipt))).trans
        (totalCast_reverse (decoded_classifier_eq family).symm point receipt)

theorem classification_right (point : D) (receipt : (ClassificationPullback family).obj point) :
    (classificationForward family).app point ((classificationBackward family).app point receipt) = receipt := by
  exact (congrArg ((genericForward (classifier family)).app point)
    (totalCast_reverse (decoded_classifier_eq family) point
      (genericBackwardValue (classifier family) point receipt))).trans
        (generic_right (classifier family) point receipt)

def classificationEquiv (point : D) : TotalAt family point ≃ (ClassificationPullback family).obj point where
  toFun := (classificationForward family).app point
  invFun := (classificationBackward family).app point
  left_inv := classification_left family point
  right_inv := classification_right family point

def classificationSectionEquiv : (total family).sections ≃ (ClassificationPullback family).sections where
  toFun := (classificationForward family).mapSection
  invFun := (classificationBackward family).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact classification_left family point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact classification_right family point (term.val point)

def classified : NaturalHom (total family) universalTotal :=
  (classificationForward family).comp (pullbackFirst universalProjection (classifier family))

theorem classified_parameter_square :
    (classified family).comp universalProjection = (projection family).comp (classifier family) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem classified_code (point : D) (receipt : TotalAt family point) :
    ((classified family).app point receipt).1 = (classifier family).app point receipt.1 := rfl

theorem classified_value_heq (point : D) (receipt : TotalAt family point) :
    HEq ((classified family).app point receipt).2 receipt.2 :=
  totalCast_value_heq (decoded_classifier_eq family).symm point receipt

theorem classificationForward_parameter :
    (classificationForward family).comp (pullbackSecond universalProjection (classifier family)) =
      projection family := by
  apply NaturalHom.ext
  intro _ _
  rfl

section ParameterSubstitution

variable {other : D ⥤ Type w} {third : D ⥤ Type z}
variable (change : NaturalHom other base)

def substitutedFamily : other.Elements ⥤ Type u := restrict (elementMap change) family

theorem substitutedFamily_id :
    substitutedFamily family (ContextualSmallMapConstructions.identity base) = family := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem substitutedFamily_comp (earlier : NaturalHom third other) :
    substitutedFamily (substitutedFamily family change) earlier =
      substitutedFamily family (earlier.comp change) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem familyCode_substitution (point : D) (value : other.obj point) :
    familyCode (substitutedFamily family change) point value =
      familyCode family point (change.app point value) := by
  have objects : ∀ future : MaterialSets.Hypersets.PowerClassPresheafBaseChange.Future.Objects point,
      (elementMap change).obj ((futureElement point value).obj future) =
        (futureElement point (change.app point value)).obj future :=
    fun future => congrArg (fun member : base.obj future.1 => (⟨future.1, member⟩ : base.Elements))
      (change.naturality future.2 value).symm
  refine Functor.hext (fun future => congrArg family.obj (objects future)) ?_
  intro first second step
  exact familyArrow_heq (E := base.Elements) family (objects first) (objects second) _ _
    (elementsArrow_heq (base := base) (objects first) (objects second) _ _ (heq_of_eq rfl))

theorem classifier_parameter_substitution :
    classifier (substitutedFamily family change) = change.comp (classifier family) := by
  apply NaturalHom.ext
  exact familyCode_substitution family change

def substitutedTotalMap : NaturalHom (total (substitutedFamily family change)) (total family) where
  app point receipt := ⟨change.app point receipt.1, receipt.2⟩
  naturality {first second} step receipt := by
    apply Sigma.ext (change.naturality step receipt.1)
    have target : (⟨second, base.map step (change.app first receipt.1)⟩ : base.Elements) =
        ⟨second, change.app second (other.map step receipt.1)⟩ :=
      congrArg (fun member : base.obj second => (⟨second, member⟩ : base.Elements))
        (change.naturality step receipt.1)
    exact familyMap_heq (E := base.Elements) family rfl target _ _
      (elementsArrow_heq (base := base) rfl target _ _ (heq_of_eq rfl)) receipt.2 receipt.2 (heq_of_eq rfl)

theorem substituted_parameter_square :
    (substitutedTotalMap family change).comp (projection family) =
      (projection (substitutedFamily family change)).comp change := by
  apply NaturalHom.ext
  intro _ _
  rfl

/-- Parameter substitution preserves the complete interpreted code and
selected decoded term, including noninjective parameter maps. -/
theorem classified_substitution :
    (substitutedTotalMap family change).comp (classified family) =
      classified (substitutedFamily family change) := by
  apply NaturalHom.ext
  intro point receipt
  apply Sigma.ext (familyCode_substitution family change point receipt.1).symm
  exact (classified_value_heq family point ((substitutedTotalMap family change).app point receipt)).trans
    (classified_value_heq (substitutedFamily family change) point receipt).symm

abbrev SubstitutionPullback := pullback (projection family) change

def substitutionForward :
    NaturalHom (total (substitutedFamily family change)) (SubstitutionPullback family change) :=
  pullbackPair (projection family) change (substitutedTotalMap family change)
    (projection (substitutedFamily family change)) (substituted_parameter_square family change)

def substitutionBackwardValue (point : D) (receipt : (SubstitutionPullback family change).obj point) :
    TotalAt (substitutedFamily family change) point :=
  ⟨receipt.val.2,
    cast (congrArg family.obj (congrArg (fun member : base.obj point =>
      (⟨point, member⟩ : base.Elements)) receipt.property)) receipt.val.1.2⟩

theorem substitution_left (point : D) (receipt : TotalAt (substitutedFamily family change) point) :
    substitutionBackwardValue family change point ((substitutionForward family change).app point receipt) = receipt :=
  rfl

theorem substitution_right (point : D) (receipt : (SubstitutionPullback family change).obj point) :
    (substitutionForward family change).app point (substitutionBackwardValue family change point receipt) = receipt := by
  rcases receipt with ⟨⟨⟨parameter, term⟩, value⟩, same⟩
  change parameter = change.app point value at same
  subst parameter
  rfl

theorem substitutionForward_injective (point : D) :
    Function.Injective ((substitutionForward family change).app point) := by
  intro first second same
  exact (substitution_left family change point first).symm.trans
    ((congrArg (substitutionBackwardValue family change point) same).trans
      (substitution_left family change point second))

def substitutionBackward :
    NaturalHom (SubstitutionPullback family change) (total (substitutedFamily family change)) where
  app := substitutionBackwardValue family change
  naturality {first second} step receipt := by
    apply substitutionForward_injective family change second
    exact ((substitutionForward family change).naturality step
      (substitutionBackwardValue family change first receipt)).symm.trans
      ((congrArg ((SubstitutionPullback family change).map step)
        (substitution_right family change first receipt)).trans
          (substitution_right family change second ((SubstitutionPullback family change).map step receipt)).symm)

def substitutionEquiv (point : D) :
    TotalAt (substitutedFamily family change) point ≃ (SubstitutionPullback family change).obj point where
  toFun := (substitutionForward family change).app point
  invFun := (substitutionBackward family change).app point
  left_inv := substitution_left family change point
  right_inv := substitution_right family change point

def substitutionSectionEquiv :
    (total (substitutedFamily family change)).sections ≃ (SubstitutionPullback family change).sections where
  toFun := (substitutionForward family change).mapSection
  invFun := (substitutionBackward family change).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact substitution_left family change point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact substitution_right family change point (term.val point)

end ParameterSubstitution

end Mettapedia.TypeTheory.ContextualSmallFamilyUniverse
