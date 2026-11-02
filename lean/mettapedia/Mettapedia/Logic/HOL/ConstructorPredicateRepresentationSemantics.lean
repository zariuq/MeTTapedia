import Mettapedia.Logic.HOL.ConstructorPredicateRepresentation
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-! # Exact interpretation of transported field predicates -/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.ConstructorPredicateRepresentation
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  {source target : Ty Base}

theorem lift_denote (model : HenkinModel.{u,v,w} Base Const)
    (encode : Term Const Γ (source ⇒ target)) (predicate : Term Const Γ (source ⇒ .prop))
    (values : model.Valuation Γ) (stored : Ty.denote model.Carrier target) :
    (model.denote (lift encode predicate) values stored).down ↔
      ∃ field, model.adm source field ∧ (model.denote predicate values field).down ∧
        model.Eqv target (model.denote encode values field) stored := by
  simp only [lift,body,witness,HenkinModel.denote,PreModel.denote,Soundness.denote_weaken,PreModel.extend]

theorem lift_denote_full (model : HenkinModel.{u,v,w} Base Const) (full : model.FullDomains)
    (encode : Term Const Γ (source ⇒ target)) (predicate : Term Const Γ (source ⇒ .prop))
    (values : model.Valuation Γ) (stored : Ty.denote model.Carrier target) :
    (model.denote (lift encode predicate) values stored).down ↔
      ∃ field, (model.denote predicate values field).down ∧ model.denote encode values field = stored := by
  rw [lift_denote]
  simp only [model.eqv_iff_eq_of_fullDomains full]
  constructor
  · rintro ⟨field,_,valid,same⟩
    exact ⟨field,valid,same⟩
  · rintro ⟨field,valid,same⟩
    exact ⟨field,full _ _,valid,same⟩

/-- The transported guard recognizes exactly the represented source subtype.
No inverse or injectivity is needed for this image characterization. -/
theorem value_image (model : HenkinModel.{u,v,w} Base Const) (full : model.FullDomains)
    (encode : Term Const Γ (source ⇒ target)) (predicate : Term Const Γ (source ⇒ .prop))
    (values : model.Valuation Γ) (stored : Ty.denote model.Carrier target) :
    (model.denote (lift encode predicate) values stored).down ↔
      ∃ field : {value : Ty.denote model.Carrier source // (model.denote predicate values value).down},
        model.denote encode values field.val = stored := by
  rw [lift_denote_full model full]
  constructor
  · rintro ⟨field,valid,same⟩
    exact ⟨⟨field,valid⟩,same⟩
  · rintro ⟨field,same⟩
    exact ⟨field.val,field.property,same⟩

/-- Empty source guards stay empty, including on inhabited target carriers. -/
theorem empty_guard (model : HenkinModel.{u,v,w} Base Const)
    (encode : Term Const Γ (source ⇒ target)) (predicate : Term Const Γ (source ⇒ .prop))
    (values : model.Valuation Γ) (empty : ∀ field, ¬ (model.denote predicate values field).down)
    (stored : Ty.denote model.Carrier target) :
    ¬ (model.denote (lift encode predicate) values stored).down := by
  intro present
  obtain ⟨field,_,valid,_⟩ := (lift_denote model encode predicate values stored).mp present
  exact empty field valid

/-- Both directions are the supplied HOL programs. Existential witnesses are
used only to prove their guards and inverse laws, never to choose a decoder. -/
noncomputable def subtypeEquiv (model : HenkinModel.{u,v,w} Base Const) (full : model.FullDomains)
    (encode : Term Const Γ (source ⇒ target)) (decode : Term Const Γ (target ⇒ source))
    (predicate : Term Const Γ (source ⇒ .prop)) (values : model.Valuation Γ)
    (roundtrip : ∀ field, model.denote decode values (model.denote encode values field) = field) :
    {field : Ty.denote model.Carrier source // (model.denote predicate values field).down} ≃
      {stored : Ty.denote model.Carrier target // (model.denote (lift encode predicate) values stored).down} where
  toFun field := ⟨model.denote encode values field.val,
    (lift_denote_full model full encode predicate values _).mpr ⟨field.val,field.property,rfl⟩⟩
  invFun stored := ⟨model.denote decode values stored.val,by
    obtain ⟨field,valid,same⟩ := (lift_denote_full model full encode predicate values stored.val).mp stored.property
    have decoded : model.denote decode values stored.val = field :=
      (congrArg (model.denote decode values) same).symm.trans (roundtrip field)
    rw [decoded]
    exact valid⟩
  left_inv field := Subtype.ext (roundtrip field.val)
  right_inv stored := by
    apply Subtype.ext
    obtain ⟨field,_,same⟩ := (lift_denote_full model full encode predicate values stored.val).mp stored.property
    change model.denote encode values (model.denote decode values stored.val) = stored.val
    rw [← same,roundtrip]

/-- A retained field roundtrip, interpreted under its actual hypotheses,
supplies the inverse law of the represented subtype equivalence. -/
noncomputable def subtypeEquivOfProof (model : HenkinModel.{u,v,w} Base Const) (full : model.FullDomains)
    (encode : Term Const Γ (source ⇒ target)) (decode : Term Const Γ (target ⇒ source))
    (predicate : Term Const Γ (source ⇒ .prop)) (values : model.Valuation Γ)
    {assumptions : List (Formula Const Γ)}
    (law : ProofSyntax Const assumptions (ConstructorFieldRepresentation.leftInverse encode decode))
    (holds : Soundness.SatisfiesHyps model values assumptions) :
    {field : Ty.denote model.Carrier source // (model.denote predicate values field).down} ≃
      {stored : Ty.denote model.Carrier target // (model.denote (lift encode predicate) values stored).down} := by
  apply subtypeEquiv model full encode decode predicate values
  have sound := Soundness.extDerivation_sound law.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => full _ _) holds
  have pointwise : ∀ field, model.adm source field →
      model.Eqv source (model.denote decode values (model.denote encode values field)) field := by
    simpa only [ConstructorFieldRepresentation.leftInverse,HenkinModel.denote,PreModel.denote,
      Soundness.denote_weaken,PreModel.extend] using sound
  intro field
  exact model.eq_of_eqv_of_fullDomains full (pointwise field (full _ _))

#print axioms lift_denote
#print axioms value_image
#print axioms empty_guard
#print axioms subtypeEquiv
#print axioms subtypeEquivOfProof
end Mettapedia.Logic.HOL.ConstructorPredicateRepresentation
