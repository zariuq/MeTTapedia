import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.ValidityPiEquality
import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PiInstantiationEquality

/-!
Validity of dependent application and its congruence rule. Result type
validity uses semantic comparison at both the changed function code and the
changed argument. No syntactic matching of a converted lambda is used.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.StaticMetatheory

theorem ValidTerm.applicationType {Γ : RawContext n} {A : Ty n} {B : TyAbs n} {f a : Term n}
    (function : ValidTerm Γ f (Ty.pi A B)) (argument : ValidTerm Γ a A) :
    ValidType Γ (B.instantiate a) := by
  obtain ⟨functionSource⟩ := function.source
  obtain ⟨argumentSource⟩ := argument.source
  refine ⟨⟨typingFormation (.app functionSource argumentSource)⟩, ?_, ?_⟩
  · intro m Δ σ substitution
    have functionType := function.type.reducible substitution
    simp only [Ty.pi_subst] at functionType
    simpa only [TyAbs.instantiate_subst] using
      (functionType.application (by simpa only [Ty.pi_subst] using function.member substitution)
        (argument.type.reducible substitution) (argument.member substitution)).1
  · intro m Δ σ τ substitution
    have functionType := function.type.reducible substitution.left
    have compared := function.type.extension substitution
    simp only [Ty.pi_subst] at functionType compared
    simpa only [TyAbs.instantiate_subst] using
      (functionType.piInstantiationEquality compared (argument.type.reducible substitution.left)
        (argument.extension substitution)).2

theorem ValidTerm.app {Γ : RawContext n} {A : Ty n} {B : TyAbs n} {f a : Term n}
    (function : ValidTerm Γ f (Ty.pi A B)) (argument : ValidTerm Γ a A) :
    ValidTerm Γ (f.app a) (B.instantiate a) := by
  obtain ⟨functionSource⟩ := function.source
  obtain ⟨argumentSource⟩ := argument.source
  refine ⟨⟨.app functionSource argumentSource⟩, function.applicationType argument, ?_, ?_⟩
  · intro m Δ σ substitution
    have functionType := function.type.reducible substitution
    simp only [Ty.pi_subst] at functionType
    simpa only [TyAbs.instantiate_subst, Term.app_subst] using
      (functionType.application (by simpa only [Ty.pi_subst] using function.member substitution)
        (argument.type.reducible substitution) (argument.member substitution)).2
  · intro m Δ σ τ substitution
    have functionType := function.type.reducible substitution.left
    simp only [Ty.pi_subst] at functionType
    simpa only [TyAbs.instantiate_subst, Term.app_subst] using
      (functionType.applicationCongruence (by simpa only [Ty.pi_subst] using function.extension substitution)
        (argument.type.reducible substitution.left) (argument.extension substitution)).2

theorem ValidTermEq.appCong {Γ : RawContext n} {A : Ty n} {B : TyAbs n} {f g a b : Term n}
    (functions : ValidTermEq Γ f g (Ty.pi A B)) (arguments : ValidTermEq Γ a b A) :
    ValidTermEq Γ (f.app a) (g.app b) (B.instantiate a) := by
  obtain ⟨functionSource⟩ := functions.source
  obtain ⟨argumentSource⟩ := arguments.source
  apply ValidTermEq.ofLeft (.appCong functionSource argumentSource) (functions.left.app arguments.left)
  intro m Δ σ substitution
  have functionType := functions.left.type.reducible substitution
  simp only [Ty.pi_subst] at functionType
  simpa only [TyAbs.instantiate_subst, Term.app_subst] using
    (functionType.applicationCongruence (by simpa only [Ty.pi_subst] using functions.equal substitution)
      (arguments.left.type.reducible substitution) (arguments.equal substitution)).2

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
