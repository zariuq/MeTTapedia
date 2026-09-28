import Mettapedia.Languages.Agda.Adequacy.AdministrativeCanonizationCore

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Canonization

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Structural
open Structural.Statics (RawTm RawTy RawContext)
open Structural.AdministrativeStatics

noncomputable def rule {j : Judgment} (shape : RuleShape j)
    (children : Evidence Derivation (premises shape))
    (ih : Evidence Motive (premises shape)) : Motive j := by
  cases shape with
  | prior shape =>
      have children := priorPremiseEvidence children
      have ih := priorPremiseEvidence ih
      cases shape with
      | core shape =>
          exact coreRule shape (SpineStatics.corePremiseEvidence children)
            (SpineStatics.corePremiseEvidence ih)
      | nil Γ A =>
          refine ⟨[], rfl, ?_⟩
          intro f g heads
          exact termTransitivity (Derivation.emptyElimination heads.termEndpoints.left) heads
      | cons Γ A B u es C =>
          simp only [SpineStatics.premises] at children ih
          let argument := ih 0
          let tail := ih 1
          refine ⟨.apply argument.value :: tail.value,
            Observation.cons_of_some (Observation.apply_of_some argument.observed) tail.observed, ?_⟩
          intro f g heads
          exact termTransitivity
            (CanonizationPreparation.consToNested heads.termEndpoints.left (children 0) (children 1))
            (tail.transform (applicationCongruence (A := A) (B := B) heads argument.equality))
      | append Γ A es B fs C =>
          simp only [SpineStatics.premises] at children ih
          let first := ih 0
          let second := ih 1
          refine ⟨first.value ++ second.value, Observation.append_of_some first.observed second.observed, ?_⟩
          intro f g heads
          have nested := Derivation.nestedElimination heads.termEndpoints.left (children 0) (children 1)
          have result := termTransitivity (termSymmetry nested) (second.transform (first.transform heads))
          simp only [applyReadback_append]
          exact result
      | inputConversion Γ A' A es B =>
          simp only [SpineStatics.premises] at children ih
          let tail := ih 1
          exact ⟨tail.value, tail.observed, fun heads => tail.transform (termConversion heads (children 0))⟩
      | outputConversion Γ A es B B' =>
          simp only [SpineStatics.premises] at children ih
          let tail := ih 0
          exact ⟨tail.value, tail.observed, fun heads => termConversion (tail.transform heads) (children 1)⟩
      | elimination Γ f A es B =>
          simp only [SpineStatics.premises] at children ih
          let head := ih 0
          let action := ih 1
          refine ⟨head.value.applySpine action.value, Observation.eliminate_of_some head.observed action.observed, ?_⟩
          have result := action.transform head.equality
          simpa only [applyReadback_embed] using result
  | spineRefl | spineSymm | spineTrans | spineCons | spineAppend | spineInputConversion
    | spineOutputConversion | appendEmpty | appendCons | eliminationCongruence
    | emptyElimination | nestedElimination => exact ⟨⟩

noncomputable def canonize {j : Judgment} (tree : Derivation j) : Motive j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial (fun _ j _ => Motive j)
    (fun _ _ shape children ih => rule shape children ih) () j tree

noncomputable def context {n : Nat} {Γ : RawContext n}
    (tree : CoreDerivation (Statics.context Γ)) : ContextResult Γ := canonize tree

noncomputable def formation {n : Nat} {Γ : RawContext n} {A : RawTy n}
    (tree : CoreDerivation (Statics.formed Γ A)) : TypeResult Γ A := canonize tree

noncomputable def typing {n : Nat} {Γ : RawContext n} {t : RawTm n} {A : RawTy n}
    (tree : CoreDerivation (Statics.typed Γ t A)) : TermResult Γ t A := canonize tree

noncomputable def action {n : Nat} {Γ : RawContext n} {A B : RawTy n} {es : Spine (scope n)}
    (tree : Action Γ A es B) : ActionResult Γ A es B := canonize tree

noncomputable def ContextResult.returnSubstitution {n : Nat} {Γ : RawContext n} (result : ContextResult Γ) :
    Statics.TypedSubstitution CoreDerivation (embedContext result.value) Γ
      (Telescope.identity (S := sig) .term n) :=
  Statics.ContextConversion.identitySubstitution administrativeOperations CoreDerivation.typeEndpoints
    (Statics.ContextConversion.symmetry administrativeOperations CoreDerivation.typeEndpoints result.equality)

noncomputable def ContextResult.returnAt {n : Nat} {Γ : RawContext n} (result : ContextResult Γ)
    {Δ : StaticSpecification.RawContext n} (observed : Observation.context Γ = some Δ) :
    Statics.TypedSubstitution CoreDerivation (embedContext Δ) Γ (Telescope.identity (S := sig) .term n) :=
  (congrArg (fun Δ => Statics.TypedSubstitution CoreDerivation (embedContext Δ) Γ
      (Telescope.identity (S := sig) .term n))
    (Option.some.inj (result.observed.symm.trans observed))).mp result.returnSubstitution

end Mettapedia.Languages.Agda.StaticAdequacy.Canonization
