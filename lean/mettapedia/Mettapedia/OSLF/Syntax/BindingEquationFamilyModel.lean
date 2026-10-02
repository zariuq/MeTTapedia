import Mettapedia.OSLF.Syntax.BindingEquationFamilyCongruence
import Mettapedia.OSLF.Syntax.BindingTermCongruenceQuotient
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafProgramModel

/-!
# Full binding models for small equation families

The checked finite-fragment relation instantiates the reusable term-congruence
quotient. Arbitrary quotient-valued contextual bodies, captured environments
and ordinary environments satisfy every family axiom. The descended fold into
each independently specified satisfying clone is unique. Every finite
supported fragment also receives the existing presheaf interpretation.

No collection law or generated Cost equation is invented by this construction;
the caller must supply its actual equation family.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingEquationFamilyModel

open BindingSubstitutionAlgebra BindingEquationFamilyCongruence

universe u

variable {S : Signature} {M : List (MetaArity S)}

theorem argumentRelation_to_relatedArgs {family : EqAxiom S M → Prop} :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      {first second : Args S arity Γ},
      BindingTermCongruenceQuotient.ArgumentRelation (Related family) first second →
        RelatedArgs family first second
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons head tail => .cons head (argumentRelation_to_relatedArgs tail)

/-- All generic quotient obligations are discharged by the constructed
finitary family relation. -/
def congruence (family : EqAxiom S M → Prop) : BindingTermCongruenceQuotient.Congruence S where
  relation := Related family
  reflexive := Related.refl
  symmetric := Related.symm
  transitive := Related.trans
  bind_relation := by
    intro Γ Δ sort env first second relation
    exact Related.bind env relation
  bind_pointwise := Related.bind_pointwise
  operation_relation := by
    intro Γ sort operator first second arguments
    exact Related.operation operator (argumentRelation_to_relatedArgs arguments)

abbrev Carrier (family : EqAxiom S M → Prop) :=
  BindingTermCongruenceQuotient.Carrier (congruence family)

noncomputable abbrev algebra (family : EqAxiom S M → Prop) :=
  BindingTermCongruenceQuotient.algebra (congruence family)

def project (family : EqAxiom S M → Prop) {Γ : Ctx S} {sort : S.Srt}
    (value : Term S Γ sort) : Carrier family Γ sort :=
  BindingTermCongruenceQuotient.project (congruence family) value

noncomputable def projection (family : EqAxiom S M → Prop) :
    FreeBindingClone.Hom (BindingCloneAlgebra.terms S) (algebra family) :=
  BindingTermCongruenceQuotient.projection (congruence family)

theorem interpret_eq_project (family : EqAxiom S M → Prop)
    {Γ : Ctx S} {sort : S.Srt} (value : Term S Γ sort) :
    BindingCloneFoldSubstitution.interpret (algebra family) value = project family value :=
  BindingTermCongruenceQuotient.interpret_eq_project (congruence family) value

/-- Every actual family axiom must hold on arbitrary contextual semantic
bodies and both independent environments. -/
def Satisfies (target : BindingCloneAlgebra.Algebra.{u} S)
    (family : EqAxiom S M → Prop) : Prop :=
  ∀ equation, family equation → ∀ {Θ Γ : Ctx S}
    (valuation : SemanticContextualMetavariables.Valuation (M := M) target Θ)
    (ambient : Environment S target.substitution.Carrier Θ Γ)
    (ordinary : Environment S target.substitution.Carrier equation.ctx Γ),
    SemanticContextualMetavariables.interpretSchema target valuation ambient ordinary equation.lhs =
      SemanticContextualMetavariables.interpretSchema target valuation ambient ordinary equation.rhs

noncomputable def contextualValuationBodies (family : EqAxiom S M → Prop)
    {Θ : Ctx S}
    (valuation : SemanticContextualMetavariables.Valuation (M := M) (algebra family) Θ) :
    ContextualAssignment S M Θ := fun position => Quotient.out (valuation position)

/-- Representatives of arbitrary semantic inputs supply the actual syntactic
contextual instance. The quotient projection is independently constructed. -/
theorem interpretContextualSchema_eq_project (family : EqAxiom S M → Prop)
    {Θ Ξ Γ : Ctx S}
    (valuation : SemanticContextualMetavariables.Valuation (M := M) (algebra family) Θ)
    (ambient : Environment S (Carrier family) Θ Γ)
    (ordinary : Environment S (Carrier family) Ξ Γ)
    {sort : S.Srt} (value : Term (withMetas S M) Ξ sort) :
    SemanticContextualMetavariables.interpretSchema (algebra family) valuation ambient ordinary value =
      project family
        (ContextualAssignment.instantiate (contextualValuationBodies family valuation)
          (BindingTermCongruenceQuotient.representativeEnv (congruence family) ambient)
          (BindingTermCongruenceQuotient.representativeEnv (congruence family) ordinary) value) := by
  have bodies : BindingContextualEquationInterpretation.interpretAssignment (algebra family)
      (contextualValuationBodies family valuation) = valuation := by
    funext position
    change BindingCloneFoldSubstitution.interpret (algebra family)
      (Quotient.out (valuation position)) = valuation position
    rw [interpret_eq_project]
    exact Quotient.out_eq _
  have ambientValues : BindingContextualEquationInterpretation.interpretEnvironment (algebra family)
      (BindingTermCongruenceQuotient.representativeEnv (congruence family) ambient) = ambient := by
    funext sort position
    change BindingCloneFoldSubstitution.interpret (algebra family) _ = ambient sort position
    rw [interpret_eq_project]
    exact BindingTermCongruenceQuotient.project_representativeEnv _ _ _ _
  have ordinaryValues : BindingContextualEquationInterpretation.interpretEnvironment (algebra family)
      (BindingTermCongruenceQuotient.representativeEnv (congruence family) ordinary) = ordinary := by
    funext sort position
    change BindingCloneFoldSubstitution.interpret (algebra family) _ = ordinary sort position
    rw [interpret_eq_project]
    exact BindingTermCongruenceQuotient.project_representativeEnv _ _ _ _
  have comparison := BindingContextualEquationInterpretation.interpret_instantiate (algebra family)
    (contextualValuationBodies family valuation)
    (BindingTermCongruenceQuotient.representativeEnv (congruence family) ambient)
    (BindingTermCongruenceQuotient.representativeEnv (congruence family) ordinary) value
  rw [bodies, ambientValues, ordinaryValues, interpret_eq_project] at comparison
  exact comparison.symm

/-- The actual quotient satisfies every family axiom in full environments. -/
theorem algebra_satisfies (family : EqAxiom S M → Prop) : Satisfies (algebra family) family := by
  intro equation admitted Θ Γ valuation ambient ordinary
  rw [interpretContextualSchema_eq_project, interpretContextualSchema_eq_project]
  apply Quotient.sound
  refine ⟨[equation], ?_, ?_⟩
  · intro candidate member
    obtain rfl := List.mem_singleton.mp member
    exact admitted
  · exact EqClosure.ax (E := [equation]) ⟨0, by simp⟩
      (contextualValuationBodies family valuation)
      (BindingTermCongruenceQuotient.representativeEnv (congruence family) ambient)
      (BindingTermCongruenceQuotient.representativeEnv (congruence family) ordinary)

theorem satisfies_fragment (target : BindingCloneAlgebra.Algebra.{u} S)
    {family : EqAxiom S M → Prop} (satisfaction : Satisfies target family)
    {fragment : List (EqAxiom S M)} (supported : Supported family fragment) :
    BindingEquationInterpretation.Satisfies target fragment := by
  intro position Θ Γ valuation ambient ordinary
  exact satisfaction (fragment.get position) (supported _ (List.get_mem fragment position))
    valuation ambient ordinary

/-- Family satisfaction proves the exact descent condition into the target. -/
theorem satisfaction_sound (target : BindingCloneAlgebra.Algebra.{u} S)
    {family : EqAxiom S M → Prop} (satisfaction : Satisfies target family) :
    BindingTermCongruenceQuotient.Sound (congruence family) target := by
  rintro Γ sort first second ⟨fragment, supported, proof⟩
  exact BindingEquationInterpretation.interpret_eqClosure target
    (satisfies_fragment target satisfaction supported) proof

/-- The unique universal interpretation into an independently specified
family-satisfying binding clone retains all bound and free values. -/
noncomputable def interpretHom (family : EqAxiom S M → Prop)
    (target : BindingCloneAlgebra.Algebra.{u} S) (satisfaction : Satisfies target family) :
    FreeBindingClone.Hom (algebra family) target :=
  BindingTermCongruenceQuotient.quotientHom (congruence family) target
    (satisfaction_sound target satisfaction)

theorem hom_unique (family : EqAxiom S M → Prop)
    (target : BindingCloneAlgebra.Algebra.{u} S) (satisfaction : Satisfies target family)
    (hom : FreeBindingClone.Hom (algebra family) target) :
    hom = interpretHom family target satisfaction :=
  BindingTermCongruenceQuotient.hom_unique (congruence family) target
    (satisfaction_sound target satisfaction) hom

/-- The existing categorical presheaf model satisfies every finite supported
fragment of the same whole family, over the whole family's quotient carrier. -/
noncomputable def presheafInterpretation (family : EqAxiom S M → Prop)
    (fragment : List (EqAxiom S M)) (supported : Supported family fragment) :=
  IntrinsicScopedOperationalPresheafProgramModel.satisfyingInterpretation
    (algebra family) fragment (satisfies_fragment _ (algebra_satisfies family) supported)

end Mettapedia.OSLF.Binding.BindingEquationFamilyModel
