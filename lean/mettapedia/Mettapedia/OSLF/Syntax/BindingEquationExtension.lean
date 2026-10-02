import Mettapedia.OSLF.Syntax.FreeBindingEquationModel

/-!
# Extending an authored binding-equation presentation

An inclusion of axiom lists induces restriction of equation models and a
canonical map between their initial models. The map preserves every binding
operator and quotient-valued simultaneous substitution. It is surjective on
each context-and-sort fibre; it need not be injective when the new equations
identify previously distinct terms.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingEquationExtension

open CategoryTheory
open Mettapedia.OSLF.Binding.FreeBindingEquationModel
open Mettapedia.OSLF.Binding.BindingEquationInterpretation
open Mettapedia.OSLF.Binding.BindingEquationQuotientModel

universe u

variable {S : Signature} {M : List (MetaArity S)}

/-- Every earlier axiom occurs literally in the extended presentation. -/
def AxiomInclusion (E F : List (EqAxiom S M)) : Prop :=
  ∀ i : Fin E.length, ∃ j : Fin F.length, F.get j = E.get i

theorem axiomInclusion_refl (E : List (EqAxiom S M)) :
    AxiomInclusion E E := by
  intro i
  exact ⟨i, rfl⟩

theorem axiomInclusion_trans {E F G : List (EqAxiom S M)}
    (first : AxiomInclusion E F) (later : AxiomInclusion F G) :
    AxiomInclusion E G := by
  intro i
  obtain ⟨j, hj⟩ := first i
  obtain ⟨k, hk⟩ := later j
  exact ⟨k, hk.trans hj⟩

/-- Contextual satisfaction is monotone when equations are forgotten;
the bodies and both semantic environments are retained. -/
theorem satisfies_of_inclusion {E F : List (EqAxiom S M)}
    (includeAxiom : AxiomInclusion E F)
    (A : Mettapedia.OSLF.Binding.BindingCloneAlgebra.Algebra.{u} S)
    (satisfies : Satisfies A F) : Satisfies A E := by
  intro i Θ Γ valuation ambient ordinary
  obtain ⟨j, equalAxiom⟩ := includeAxiom i
  let P : EqAxiom S M → Prop := fun a =>
    ∀ (assignment : Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra.Environment S
        A.substitution.Carrier a.ctx Γ),
      SemanticContextualMetavariables.interpretSchema A valuation ambient assignment a.lhs =
        SemanticContextualMetavariables.interpretSchema A valuation ambient assignment a.rhs
  have hF : P (F.get j) := by
    intro assignment
    exact satisfies j valuation ambient assignment
  exact (Eq.mp (congrArg P equalAxiom) hF) ordinary

/-- The model of the larger equation set, viewed as a model of the smaller
one, has exactly the same carrier and algebraic operations. -/
def restrictModel {E F : List (EqAxiom S M)}
    (includeAxiom : AxiomInclusion E F) (A : Model.{u} F) : Model.{u} E where
  algebra := A.algebra
  satisfies := satisfies_of_inclusion includeAxiom A.algebra A.satisfies

/-- Forgetting equation obligations acts on morphisms without changing their
underlying binding-clone maps. -/
def restrictFunctor {E F : List (EqAxiom S M)}
    (includeAxiom : AxiomInclusion E F) : Model.{u} F ⥤ Model.{u} E where
  obj := restrictModel includeAxiom
  map := fun f => f
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- Adding equation obligations selects a full subcategory of the weaker
models: an algebra morphism between models of both presentations needs no
extra equation-specific fields. -/
def restrictFullyFaithful {E F : List (EqAxiom S M)}
    (includeAxiom : AxiomInclusion E F) :
    (restrictFunctor.{u} includeAxiom).FullyFaithful where
  preimage f := f

/-- Initiality produces the canonical comparison from the weaker quotient to
the stronger quotient. Its codomain is restricted along the axiom inclusion. -/
noncomputable def comparisonHom {E F : List (EqAxiom S M)}
    (includeAxiom : AxiomInclusion E F) :
    (presented E) ⟶
      restrictModel includeAxiom (presented F) :=
  interpretHom (restrictModel includeAxiom (presented F))

/-- On a representative the comparison is the obvious quotient projection. -/
theorem comparisonHom_mk {E F : List (EqAxiom S M)}
    (includeAxiom : AxiomInclusion E F)
    {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) :
    (comparisonHom includeAxiom).raw.map
        (Quotient.mk _ term : TermQ E Γ sort) =
      (Quotient.mk _ term : TermQ F Γ sort) := by
  change interpretQuotient
      (BindingEquationQuotientModel.algebra F)
      (satisfies_of_inclusion includeAxiom
        (BindingEquationQuotientModel.algebra F)
        (BindingEquationQuotientModel.algebra_satisfies F)).congruenceSound
      (Quotient.mk _ term : TermQ E Γ sort) =
    (Quotient.mk _ term : TermQ F Γ sort)
  rw [interpretQuotient_mk]
  exact interpret_eq_mk F term

/-- Every equation class of the stronger presentation has a precursor in the
weaker presentation, at its original context and sort. -/
theorem comparisonHom_surjective {E F : List (EqAxiom S M)}
    (includeAxiom : AxiomInclusion E F)
    {Γ : Ctx S} {sort : S.Srt} :
    Function.Surjective
      (fun q : TermQ E Γ sort => (comparisonHom includeAxiom).raw.map q) := by
  intro target
  induction target using Quotient.inductionOn with
  | _ term =>
      exact ⟨Quotient.mk _ term, comparisonHom_mk includeAxiom term⟩

/-- The canonical quotient comparison composes when axiom lists are enlarged
in two stages. Both sides preserve the full binding-clone structure. -/
theorem comparisonHom_comp {E F G : List (EqAxiom S M)}
    (first : AxiomInclusion E F) (later : AxiomInclusion F G)
    {Γ : Ctx S} {sort : S.Srt} (q : TermQ E Γ sort) :
    (comparisonHom (axiomInclusion_trans first later)).raw.map q =
      (comparisonHom later).raw.map ((comparisonHom first).raw.map q) := by
  induction q using Quotient.inductionOn with
  | _ term =>
      rw [comparisonHom_mk, comparisonHom_mk, comparisonHom_mk]

end Mettapedia.OSLF.Binding.BindingEquationExtension
