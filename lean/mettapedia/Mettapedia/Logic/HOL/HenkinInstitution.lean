import Mettapedia.Logic.Institution
import Mettapedia.Logic.HOL.Syntax.ConstMap
import Mettapedia.Logic.HOL.Semantics.Extensionality
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# The fixed-base Henkin institution for Church-style simple type theory

This module assembles the existing typed syntax and Henkin semantics into a
model-valued institution.  Objects vary the typed constant signature while
retaining one fixed alphabet of base types.  Signature morphisms translate
constants covariantly; Henkin models reduce contravariantly by precomposing
their constant interpretation.

The construction deliberately does not package choice, infinity, excluded
middle, or definitions into the logic.  Those remain independently named
theories and model properties.  The separate `TypeDerivedSignature` category
allows base sorts to denote compound types, with derivation transport and a
full-domain satisfaction theorem.  It does not change the fixed-base category
or the arbitrary-Henkin model reducts constructed here.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.HenkinInstitution

open CategoryTheory
open scoped CategoryTheory

universe u

/-- A typed constant signature over a fixed alphabet of HOL base types. -/
structure Signature (Base : Type u) where
  Const : Ty Base → Type u

namespace Signature

/-- A signature morphism maps constants without changing their simple type. -/
structure Hom {Base : Type u} (source target : Signature Base) where
  map : ∀ {type : Ty Base}, source.Const type → target.Const type

@[ext]
theorem Hom.ext {Base : Type u} {source target : Signature Base}
    {left right : Hom source target}
    (equal : ∀ {type : Ty Base} (constant : source.Const type),
      left.map constant = right.map constant) :
    left = right := by
  cases left with
  | mk leftMap =>
      cases right with
      | mk rightMap =>
          congr
          funext type constant
          exact equal constant

/-- Identity translation of typed constants. -/
def Hom.identity {Base : Type u} (signature : Signature Base) :
    Hom signature signature where
  map := fun constant => constant

/-- Composition of typed-constant translations. -/
def Hom.comp {Base : Type u} {first middle last : Signature Base}
    (earlier : Hom first middle) (later : Hom middle last) :
    Hom first last where
  map := fun constant => later.map (earlier.map constant)

instance category (Base : Type u) : Category (Signature Base) where
  Hom := Hom
  id := Hom.identity
  comp := Hom.comp
  id_comp := by
    intro source target translation
    ext type constant
    rfl
  comp_id := by
    intro source target translation
    ext type constant
    rfl
  assoc := by
    intro first second third fourth one two three
    ext type constant
    rfl

@[simp]
theorem id_map {Base : Type u} {signature : Signature Base}
    {type : Ty Base} (constant : signature.Const type) :
    (𝟙 signature : signature ⟶ signature).map constant = constant :=
  rfl

@[simp]
theorem comp_map {Base : Type u}
    {first middle last : Signature Base}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    {type : Ty Base} (constant : first.Const type) :
    (earlier ≫ later).map constant = later.map (earlier.map constant) :=
  rfl

end Signature

section Syntax

variable {Base : Type u}

/-- Closed HOL formulas vary functorially with the typed constant signature. -/
def sentence : Signature Base ⥤ Type u where
  obj signature := ClosedFormula signature.Const
  map translation := TypeCat.ofHom fun formula =>
    mapConst translation.map formula
  map_id signature := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext formula
    exact mapConst_id formula
  map_comp earlier later := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext formula
    exact (mapConst_comp later.map earlier.map formula).symm

end Syntax

/-! ## Contravariant Henkin-model reduct -/

namespace PreModel

variable {Base : Type u} {source target : Signature Base}

/-- Forget target constants by precomposing their interpretation with a
typed-constant translation. -/
def reduct (translation : source ⟶ target)
    (model : HOL.PreModel.{u, u, u} Base target.Const) :
    HOL.PreModel.{u, u, u} Base source.Const where
  Carrier := model.Carrier
  adm := model.adm
  base_mem := model.base_mem
  prop_mem := model.prop_mem
  app_mem := model.app_mem
  constDen constant := model.constDen (translation.map constant)
  const_mem constant := model.const_mem (translation.map constant)

/-- The extensional equality relation is unchanged by forgetting constants. -/
theorem eqv_reduct (translation : source ⟶ target)
    (model : HOL.PreModel.{u, u, u} Base target.Const) :
    ∀ {type : Ty Base}
      (left right : Ty.denote model.Carrier type),
      HOL.PreModel.Eqv (reduct translation model) type left right ↔
        HOL.PreModel.Eqv model type left right := by
  intro type
  induction type with
  | prop =>
      intro left right
      rfl
  | base base =>
      intro left right
      rfl
  | arr sourceType targetType sourceIH targetIH =>
      intro left right
      constructor
      · intro related value admissible
        exact (targetIH (left value) (right value)).mp
          (related value admissible)
      · intro related value admissible
        exact (targetIH (left value) (right value)).mpr
          (related value admissible)

/-- Extending a valuation is independent of the forgotten constant
signature. -/
theorem extend_reduct (translation : source ⟶ target)
    (model : HOL.PreModel.{u, u, u} Base target.Const)
    {context : Ctx Base} {type : Ty Base}
    (valuation : HOL.PreModel.Valuation (reduct translation model) context)
    (value : Ty.denote model.Carrier type) :
    (fun {resultType} (v : Var (type :: context) resultType) =>
      HOL.PreModel.extend (reduct translation model) valuation value v) =
    (fun {resultType} (v : Var (type :: context) resultType) =>
      HOL.PreModel.extend model valuation value v) := by
  funext resultType v
  cases v <;> rfl

/-- Term denotation commutes with reduct and constant translation. -/
theorem denote_reduct (translation : source ⟶ target)
    (model : HOL.PreModel.{u, u, u} Base target.Const) :
    ∀ {context : Ctx Base} {type : Ty Base}
      (term : Term source.Const context type)
      (valuation : HOL.PreModel.Valuation (reduct translation model) context),
      HOL.PreModel.denote (reduct translation model) term valuation =
        HOL.PreModel.denote model (mapConst translation.map term) valuation := by
  intro context type term
  induction term with
  | var v => intro valuation; rfl
  | const constant => intro valuation; rfl
  | app function argument functionIH argumentIH =>
      intro valuation
      simp only [HOL.PreModel.denote, mapConst]
      rw [functionIH valuation, argumentIH valuation]
  | lam body bodyIH =>
      intro valuation
      simp only [HOL.PreModel.denote, mapConst]
      funext value
      exact bodyIH (HOL.PreModel.extend model valuation value)
  | top => intro valuation; rfl
  | bot => intro valuation; rfl
  | and left right leftIH rightIH =>
      intro valuation
      simp only [HOL.PreModel.denote, mapConst]
      rw [leftIH valuation, rightIH valuation]
  | or left right leftIH rightIH =>
      intro valuation
      simp only [HOL.PreModel.denote, mapConst]
      rw [leftIH valuation, rightIH valuation]
  | imp left right leftIH rightIH =>
      intro valuation
      simp only [HOL.PreModel.denote, mapConst]
      rw [leftIH valuation, rightIH valuation]
  | not formula formulaIH =>
      intro valuation
      simp only [HOL.PreModel.denote, mapConst]
      rw [formulaIH valuation]
  | eq left right leftIH rightIH =>
      intro valuation
      simp only [HOL.PreModel.denote, mapConst]
      rw [leftIH valuation, rightIH valuation]
      congr 1
      apply propext
      exact eqv_reduct translation model _ _
  | all body bodyIH =>
      intro valuation
      simp only [HOL.PreModel.denote, mapConst]
      apply congrArg ULift.up
      apply propext
      constructor
      · intro holds value admissible
        have bodyTruth := holds value admissible
        rw [extend_reduct translation model valuation value] at bodyTruth
        rw [bodyIH (HOL.PreModel.extend model valuation value)] at bodyTruth
        exact bodyTruth
      · intro holds value admissible
        rw [extend_reduct translation model valuation value]
        rw [bodyIH (HOL.PreModel.extend model valuation value)]
        exact holds value admissible
  | ex body bodyIH =>
      intro valuation
      simp only [HOL.PreModel.denote, mapConst]
      apply congrArg ULift.up
      apply propext
      constructor
      · rintro ⟨value, admissible, holds⟩
        refine ⟨value, admissible, ?_⟩
        rw [extend_reduct translation model valuation value] at holds
        rw [bodyIH (HOL.PreModel.extend model valuation value)] at holds
        exact holds
      · rintro ⟨value, admissible, holds⟩
        refine ⟨value, admissible, ?_⟩
        rw [extend_reduct translation model valuation value]
        rw [bodyIH (HOL.PreModel.extend model valuation value)]
        exact holds

@[simp]
theorem models_reduct (translation : source ⟶ target)
    (model : HOL.PreModel.{u, u, u} Base target.Const)
    (formula : ClosedFormula source.Const) :
    HOL.PreModel.models (reduct translation model) formula ↔
      HOL.PreModel.models model (mapConst translation.map formula) := by
  change
    (HOL.PreModel.denote (reduct translation model) formula
      (fun v => nomatch v)).down ↔
    (HOL.PreModel.denote model (mapConst translation.map formula)
      (fun v => nomatch v)).down
  rw [denote_reduct]
  rfl

end PreModel

namespace HenkinModel

variable {Base : Type u} {source target : Signature Base}

/-- Henkin closure is retained by constant-signature reduct. -/
def reduct (translation : source ⟶ target)
    (model : HOL.HenkinModel.{u, u, u} Base target.Const) :
    HOL.HenkinModel.{u, u, u} Base source.Const where
  toPreModel := PreModel.reduct translation model.toPreModel
  term_closed := by
    intro context type term valuation admissible
    rw [PreModel.denote_reduct]
    exact model.term_closed (mapConst translation.map term) valuation admissible

@[simp]
theorem models_reduct (translation : source ⟶ target)
    (model : HOL.HenkinModel.{u, u, u} Base target.Const)
    (formula : ClosedFormula source.Const) :
    (reduct translation model).models formula ↔
      model.models (mapConst translation.map formula) :=
  PreModel.models_reduct translation model.toPreModel formula

@[simp]
theorem reduct_id {signature : Signature Base}
    (model : HOL.HenkinModel.{u, u, u} Base signature.Const) :
    reduct (𝟙 signature) model = model := by
  cases model with
  | mk preModel closed =>
      cases preModel
      rfl

@[simp]
theorem reduct_comp {first middle last : Signature Base}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (model : HOL.HenkinModel.{u, u, u} Base last.Const) :
    reduct earlier (reduct later model) = reduct (earlier ≫ later) model := by
  cases model with
  | mk preModel closed =>
      cases preModel
      rfl

end HenkinModel

/-! ## Models of the extensional derivation calculus -/

/-- A Henkin model equipped with the application-congruence law consumed by
the extensional HOL derivation.  The property is bundled because arbitrary
Henkin models do not validate that stronger equality rule. -/
structure Model {Base : Type u} (signature : Signature Base) where
  henkin : HOL.HenkinModel.{u, u, u} Base signature.Const
  functionsRespectEqv : henkin.FunctionsRespectEqv

namespace Model

variable {Base : Type u} {source target : Signature Base}

@[ext]
theorem ext {signature : Signature Base} {left right : Model signature}
    (equal : left.henkin = right.henkin) : left = right := by
  cases left
  cases right
  cases equal
  rfl

/-- Extensional Henkin models are stable under constant-signature reduct. -/
def reduct (translation : source ⟶ target) (model : Model target) :
    Model source where
  henkin := HenkinModel.reduct translation model.henkin
  functionsRespectEqv := by
    intro sourceType targetType function left right
      functionAdmissible leftAdmissible rightAdmissible related
    apply (PreModel.eqv_reduct translation model.henkin.toPreModel _ _).mpr
    exact model.functionsRespectEqv functionAdmissible leftAdmissible
      rightAdmissible
      ((PreModel.eqv_reduct translation model.henkin.toPreModel _ _).mp
        related)

@[simp]
theorem reduct_id {signature : Signature Base} (model : Model signature) :
    reduct (𝟙 signature) model = model := by
  apply ext
  exact HenkinModel.reduct_id model.henkin

@[simp]
theorem reduct_comp {first middle last : Signature Base}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (model : Model last) :
    reduct earlier (reduct later model) = reduct (earlier ≫ later) model := by
  apply ext
  exact HenkinModel.reduct_comp earlier later model.henkin

end Model

section Institution

variable (Base : Type u)

/-- Henkin models form a contravariant discrete model functor.  Discreteness
is sufficient for satisfaction and consequence; model homomorphisms are a
separate enrichment not claimed here. -/
def model : (Signature Base)ᵒᵖ ⥤ CategoryTheory.Cat where
  obj signature := CategoryTheory.Cat.of
    (CategoryTheory.Discrete
      (Model signature.unop))
  map := fun {source target} translation =>
    (CategoryTheory.Discrete.functor fun henkinModel :
        Model source.unop =>
      CategoryTheory.Discrete.mk
        (Model.reduct translation.unop henkinModel)).toCatHom
  map_id signature := by
    apply CategoryTheory.Cat.Hom.ext
    apply CategoryTheory.Discrete.functor_ext
    intro henkinModel
    apply CategoryTheory.Discrete.ext
    exact Model.reduct_id henkinModel
  map_comp earlier later := by
    apply CategoryTheory.Cat.Hom.ext
    apply CategoryTheory.Discrete.functor_ext
    intro henkinModel
    apply CategoryTheory.Discrete.ext
    exact Model.reduct_comp later.unop earlier.unop henkinModel

/-- Satisfaction is ordinary closed-formula truth in the selected Henkin
model. -/
def satisfies (signature : Signature Base)
    (model : (model Base).obj (Opposite.op signature))
    (formula : ClosedFormula signature.Const) : Prop :=
  (show CategoryTheory.Discrete
      (Model signature) from model).as.henkin.models formula

/-- The model-valued institution of Church-style HOL over a fixed base-type
alphabet and varying typed constants. -/
def institution : Logic.Institution (Signature Base) where
  sentence := sentence
  model := model Base
  satisfies := satisfies Base
  satisfaction_condition := by
    intro source target translation targetModel sourceFormula
    change
      (show CategoryTheory.Discrete
          (Model target) from targetModel).as.henkin.models
            (mapConst translation.map sourceFormula) ↔
      (HenkinModel.reduct translation
        (show CategoryTheory.Discrete
          (Model target) from targetModel).as.henkin).models sourceFormula
    exact (HenkinModel.models_reduct translation
      (show CategoryTheory.Discrete
        (Model target) from targetModel).as.henkin sourceFormula).symm

@[simp]
theorem satisfaction_condition
    {source target : Signature Base} (translation : source ⟶ target)
    (targetModel : Model target)
    (sourceFormula : ClosedFormula source.Const) :
    (institution Base).satisfies target
        (CategoryTheory.Discrete.mk targetModel)
        (mapConst translation.map sourceFormula) ↔
      (institution Base).satisfies source
        ((institution Base).reduct translation
          (CategoryTheory.Discrete.mk targetModel))
        sourceFormula :=
  (institution Base).satisfaction_condition translation
    (CategoryTheory.Discrete.mk targetModel) sourceFormula

end Institution

#print axioms PreModel.denote_reduct
#print axioms HenkinModel.models_reduct
#print axioms HenkinModel.reduct_id
#print axioms HenkinModel.reduct_comp
#print axioms model
#print axioms institution
#print axioms satisfaction_condition

end Mettapedia.Logic.HOL.HenkinInstitution
