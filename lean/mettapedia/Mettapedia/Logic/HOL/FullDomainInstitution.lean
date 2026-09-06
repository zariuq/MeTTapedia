import Mettapedia.Logic.HOL.TypeDerivedSignature
import Mettapedia.Logic.HOL.TypeSubstitutionModelCoherence

/-!
# The full-domain institution of type-derived HOL signatures

Full Henkin models are closed under type-derived reducts. Structural carrier
equalities make these reducts strictly contravariantly functorial. The model
categories are discrete, as in the existing fixed-base Henkin institution;
this construction does not add general model homomorphisms.

The fixed-base Henkin institution has a comorphism into this institution:
sentences are unchanged, and target full models are forgotten to Henkin
models. This supplies satisfaction invariance, not model coverage or
reflection of semantic consequence.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.FullDomainInstitution

open CategoryTheory
open scoped CategoryTheory

universe u

/-- A full-domain Henkin model at one type-derived signature. -/
abbrev Model (signature : TypeDerivedSignature.{u}) :=
  { M : HenkinModel.{u, u, u} signature.1 signature.2.Const // M.FullDomains }

namespace Model

variable {first middle last : TypeDerivedSignature.{u}}

/-- Interpret the source types and constants in a full target model. -/
def reduct (translation : first ⟶ middle) (M : Model middle) : Model first :=
  ⟨HenkinModel.standardTypeReduct translation.base translation.constants M.1,
    HenkinModel.standardTypeReduct_fullDomains _ _ _⟩

@[simp]
theorem reduct_id (M : Model first) : reduct (𝟙 first) M = M := by
  apply Subtype.ext
  exact (HenkinModel.standardTypeReduct_id M.1).trans
    (HenkinModel.standard_eq_of_fullDomains M.1 M.2)

@[simp]
theorem reduct_comp (earlier : first ⟶ middle) (later : middle ⟶ last)
    (M : Model last) : reduct earlier (reduct later M) = reduct (earlier ≫ later) M := by
  apply Subtype.ext
  exact HenkinModel.standardTypeReduct_comp earlier.base later.base
    earlier.constants later.constants M.1

end Model

/-- Full models form a strict contravariant discrete model functor. -/
def model : TypeDerivedSignature.{u}ᵒᵖ ⥤ Cat where
  obj signature := Cat.of (Discrete (Model signature.unop))
  map := fun {source target} translation =>
    (Discrete.functor fun M : Model source.unop =>
      Discrete.mk (Model.reduct translation.unop M)).toCatHom
  map_id signature := by
    apply Cat.Hom.ext
    apply Discrete.functor_ext
    intro M
    apply Discrete.ext
    exact Model.reduct_id M
  map_comp earlier later := by
    apply Cat.Hom.ext
    apply Discrete.functor_ext
    intro M
    apply Discrete.ext
    exact (Model.reduct_comp later.unop earlier.unop M).symm

/-- Satisfaction uses the underlying model's independently defined denotation. -/
def satisfies (signature : TypeDerivedSignature.{u})
    (M : model.obj (Opposite.op signature))
    (formula : ClosedFormula signature.2.Const) : Prop :=
  (show Discrete (Model signature) from M).as.1.models formula

/-- Full-domain HOL with base symbols interpreted by arbitrary simple types. -/
def institution : Logic.Institution TypeDerivedSignature.{u} where
  sentence := TypeDerivedSignature.sentence
  model := model
  satisfies := satisfies
  satisfaction_condition := by
    intro source target translation targetModel sourceFormula
    exact (HenkinModel.models_mapTypes translation.base translation.constants
      targetModel.as.1 targetModel.as.2 sourceFormula).symm

/-- The institution satisfaction law includes type-derived translations. -/
theorem satisfaction_iff {source target : TypeDerivedSignature.{u}}
    (translation : source ⟶ target) (M : Model target)
    (formula : ClosedFormula source.2.Const) :
    M.1.models (mapTypes translation.base translation.constants formula) ↔
      (Model.reduct translation M).1.models formula :=
  (HenkinModel.models_mapTypes translation.base translation.constants
    M.1 M.2 formula).symm

section FixedBase

variable {Base : Type u}

/-- Constant-only translation agrees with the existing Henkin reduct on
full models; no equation between general model representations is assumed. -/
theorem reduct_fixedBase {source target : HenkinInstitution.Signature Base}
    (translation : source ⟶ target)
    (M : HenkinModel.{u, u, u} Base target.Const) (full : M.FullDomains) :
    HenkinModel.standardTypeReduct
        ((TypeDerivedSignature.fixedBase Base).map translation).base
        ((TypeDerivedSignature.fixedBase Base).map translation).constants M =
      HenkinInstitution.HenkinModel.reduct translation M := by
  calc
    _ = HenkinModel.standard
        (HenkinInstitution.HenkinModel.reduct translation M).Carrier
        (HenkinInstitution.HenkinModel.reduct translation M).constDen := by
      apply HenkinModel.standard_ext rfl
      intro a c
      refine (Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).trans ?_
      change HEq (M.constDen ((Ty.substitute_id a).symm ▸ translation.map c))
        (M.constDen (translation.map c))
      congr 1 <;> simp
    _ = _ := HenkinModel.standard_eq_of_fullDomains _ full

/-- A full model is in particular an extensional Henkin model. -/
def forgetFull {signature : HenkinInstitution.Signature Base}
    (M : Model ((TypeDerivedSignature.fixedBase Base).obj signature)) :
    HenkinInstitution.Model signature where
  henkin := M.1
  functionsRespectEqv := HenkinModel.functionsRespectEqv_of_fullDomains M.1 M.2

/-- Forgetting fullness covers exactly the full source models. This image
criterion does not assert that all Henkin models are full. -/
theorem forgetFull_image_iff {signature : HenkinInstitution.Signature Base}
    (M : HenkinInstitution.Model signature) :
    (∃ N : Model ((TypeDerivedSignature.fixedBase Base).obj signature),
      forgetFull N = M) ↔ M.henkin.FullDomains := by
  constructor
  · rintro ⟨N, rfl⟩
    exact N.2
  · intro full
    refine ⟨⟨M.henkin, full⟩, ?_⟩
    exact HenkinInstitution.Model.ext rfl

/-- Sentences are unchanged by the fixed-base comparison. -/
def fixedBaseSentence : HenkinInstitution.sentence (Base := Base) ⟶
    TypeDerivedSignature.fixedBase Base ⋙ TypeDerivedSignature.sentence where
  app _ := TypeCat.ofHom id
  naturality := by
    intro source target translation
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext formula
    exact (TypeDerivedSignature.sentence_fixedBase translation formula).symm

/-- Target full models reduce to source Henkin models; naturality is the
agreement between the two already defined constant-signature reducts. -/
def fixedBaseModel : (TypeDerivedSignature.fixedBase Base).op ⋙ model ⟶
    HenkinInstitution.model Base where
  app signature :=
    (Discrete.functor fun M : Model
        ((TypeDerivedSignature.fixedBase Base).obj signature.unop) =>
      Discrete.mk (forgetFull M)).toCatHom
  naturality := by
    intro source target translation
    apply Cat.Hom.ext
    apply Discrete.functor_ext
    intro M
    apply Discrete.ext
    apply HenkinInstitution.Model.ext
    exact reduct_fixedBase translation.unop M.1 M.2

/-- General fixed-base Henkin semantics maps into full-domain semantics.
The model component forgets fullness in the opposite direction. -/
def fixedBaseComorphism (Base : Type u) :
    Logic.Institution.Comorphism (HenkinInstitution.institution Base) institution where
  mapSignature := TypeDerivedSignature.fixedBase Base
  mapSentence := fixedBaseSentence
  mapModel := fixedBaseModel
  satisfaction_condition := by
    intro signature targetModel formula
    rfl

end FixedBase

namespace BaseCollapse

open TypeSubstitutionExample

/-- The source has two independently interpreted base types. -/
def source : TypeDerivedSignature := ⟨Bool, ⟨NoConstants Bool⟩⟩

/-- The target has one base type and the same empty constant family. -/
def target : TypeDerivedSignature := ⟨Unit, ⟨NoConstants Unit⟩⟩

/-- Both source base types are interpreted by the single target base type. -/
def collapse : source ⟶ target where
  base := collapseTypes
  constants := fun {a} c => noConstantsMap collapseTypes (A := a) c

/-- The source model interprets one base as a singleton and the other by Bool. -/
def separated : Model source :=
  ⟨separatingModel, HenkinModel.fullDomains_standard _ _⟩

/-- The collapsed reduct necessarily validates the implication from
subsingletonhood of one source base type to the other. -/
theorem reduct_satisfies_sourceClaim (M : Model target) :
    (Model.reduct collapse M).1.models sourceClaim := by
  apply (satisfaction_iff collapse M sourceClaim).mp
  change M.1.models (mapTypes collapseTypes (noConstantsMap collapseTypes) sourceClaim)
  rw [mapTypes_sourceClaim]
  exact targetClaim_valid M.1

/-- The independent source model refutes that implication. -/
theorem separated_refutes_sourceClaim : ¬ separated.1.models sourceClaim :=
  separatingModel_refutes_sourceClaim

/-- A genuine type-derived signature arrow need not cover source models,
even when both institutions use only full domains. -/
theorem no_expansion : ¬ ∃ M : Model target, Model.reduct collapse M = separated := by
  rintro ⟨M, equal⟩
  have satisfies := reduct_satisfies_sourceClaim M
  rw [equal] at satisfies
  exact separated_refutes_sourceClaim satisfies

end BaseCollapse

#print axioms Model.reduct_comp
#print axioms institution
#print axioms forgetFull_image_iff
#print axioms fixedBaseComorphism
#print axioms BaseCollapse.no_expansion

end Mettapedia.Logic.HOL.FullDomainInstitution
