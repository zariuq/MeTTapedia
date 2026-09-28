import Mettapedia.OSLF.Syntax.CategoricalBindingFunctor
import Mettapedia.OSLF.Syntax.SecondOrderEquationUniversal

/-!
# Models of the equations interpret the equation-class classifier

A model satisfies a list of equation axioms when every instance of every
axiom has equal interpretations. The generated equational theory is then
identified by the interpretation, by induction on derivations: axiom instances
by satisfaction, substitution instances by the substitution lemma, and
congruence steps by the algebra operations.

Hence a model of an equation presentation gives a lawful interpretation in
the sense of the equation-context universal property, and so a functor on the
equation-class classifier whose restriction to raw contexts is the classifying
functor of the model.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

namespace Model

variable {S : Signature} (M : Model S D)

/-- Every instance of every axiom holds in the model. -/
def SatisfiesAxioms (N : List (MetaArity S)) {schema : List (MetaArity S)}
    (E : List (EqAxiom (withMetas S N) schema)) : Prop :=
  ∀ (i : Fin E.length)
    (body : (k : Fin schema.length) → Term (withMetas S N) (schema.get k).1 (schema.get k).2),
    M.interp N (instantiate body (E.get i).lhs) = M.interp N (instantiate body (E.get i).rhs)

section Closure

variable {N : List (MetaArity S)} {schema : List (MetaArity S)}
  {E : List (EqAxiom (withMetas S N) schema)}

mutual

/-- **Soundness.** A model of the axioms identifies the generated equational
theory. -/
theorem interp_eqClosure (sat : M.SatisfiesAxioms N E) :
    ∀ {Γ : Ctx S} {s : S.Srt} {t u : Term (withMetas S N) Γ s},
      EqClosure E t u → M.interp N t = M.interp N u
  | _, _, _, _, .ax i body close => by
      unfold interp
      rw [BindingCloneFoldSubstitution.interpret_bind, BindingCloneFoldSubstitution.interpret_bind]
      exact congrArg _ (sat i body)
  | _, _, _, _, .refl _ => rfl
  | _, _, _, _, .symm h => (interp_eqClosure sat h).symm
  | _, _, _, _, .trans h₁ h₂ => (interp_eqClosure sat h₁).trans (interp_eqClosure sat h₂)
  | _, _, _, _, .cong o h =>
      congrArg (fun a => (M.kripke N).toRaw.operation o a) (interpArgs_eqArgs sat h)

theorem interpArgs_eqArgs (sat : M.SatisfiesAxioms N E) :
    ∀ {ars : List (List S.Srt × S.Srt)} {Γ : Ctx S} {as as' : Args (withMetas S N) ars Γ},
      EqArgs E as as' →
        FreeBindingTerms.foldArgs (M.kripke N).toRaw as =
          FreeBindingTerms.foldArgs (M.kripke N).toRaw as'
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons h hs =>
      congrArg₂ FreeBindingTerms.FamilyArgs.cons (interp_eqClosure sat h) (interpArgs_eqArgs sat hs)

end

end Closure

/-- A model satisfies an equation presentation when it satisfies its axioms at
every metavariable context. -/
def Satisfies {schema : List (MetaArity S)} (P : EquationPresentation S schema) : Prop :=
  ∀ X : Object S, M.SatisfiesAxioms X.arities (P.axioms X)

variable {schema : List (MetaArity S)} (P : EquationPresentation S schema)

/-- Equation-related assignments interpret alike. -/
theorem assignHom_congr (sat : M.Satisfies P) {X Y : Object S} {σ τ : X ⟶ Y}
    (related : P.homRel σ τ) : M.assignHom σ = M.assignHom τ := by
  unfold assignHom
  congr 1
  funext j
  unfold generic
  rw [M.interp_eqClosure (sat X) (related j)]

/-- The lawful interpretation carried by a model of the presentation. -/
def lawfulInterpretation (sat : M.Satisfies P) : LawfulEquationInterpretation P D where
  functor := M.classifyingFunctor
  respects := fun related => M.assignHom_congr P sat related

/-- **The functor on the equation-class classifier** determined by a model of
the presentation. -/
noncomputable def equationClassifyingFunctor (sat : M.Satisfies P) : EquationContexts P ⥤ D :=
  SecondOrderContext.extend P D (M.lawfulInterpretation P sat)

/-- Its restriction along the quotient is the classifying functor of the model. -/
theorem quotient_comp_equationClassifyingFunctor (sat : M.Satisfies P) :
    P.quotientFunctor ⋙ M.equationClassifyingFunctor P sat = M.classifyingFunctor :=
  congrArg LawfulEquationInterpretation.functor
    (SecondOrderContext.restrict_extend P D (M.lawfulInterpretation P sat))

end Model

end Mettapedia.OSLF.Binding.CategoricalBindingModel

#print axioms Mettapedia.OSLF.Binding.CategoricalBindingModel.Model.interp_eqClosure
#print axioms Mettapedia.OSLF.Binding.CategoricalBindingModel.Model.quotient_comp_equationClassifyingFunctor
