import Mettapedia.OSLF.Syntax.BindingEquationQuotientModel

/-!
# The free binding-clone model of an authored equation presentation

An equation model is a binding clone satisfying every authored axiom under
arbitrary contextual semantic bodies and independent ambient and ordinary
environments. The existing
syntactic equation quotient is such a model. Its interpretation into any
other model is the unique binding-clone morphism, including preservation of
full quotient-valued simultaneous substitution and every binder-aware
operator. This is the equation rung's categorical initiality theorem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FreeBindingEquationModel

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.BindingEquationalModels
open Mettapedia.OSLF.Binding.BindingEquationInterpretation
open Mettapedia.OSLF.Binding.BindingEquationQuotientSubstitution
open Mettapedia.OSLF.Binding.BindingEquationQuotientModel

universe u

variable {S : Signature} {M : List (MetaArity S)}

/-- A binding-clone algebra satisfying an authored equation presentation
under all contextual semantic bodies and both semantic environments. -/
structure Model (E : List (EqAxiom S M)) where
  algebra : BindingCloneAlgebra.Algebra.{u} S
  satisfies : BindingEquationInterpretation.Satisfies algebra E

instance modelCategory (E : List (EqAxiom S M)) :
    CategoryTheory.Category (Model.{u} E) where
  Hom A B := FreeBindingClone.Hom A.algebra B.algebra
  id A := FreeBindingClone.Hom.id A.algebra
  comp f g := FreeBindingClone.Hom.comp f g
  id_comp := by
    intro A B f
    apply FreeBindingClone.Hom.ext
    exact FreeBindingTerms.Hom.ext (fun _ => rfl)
  comp_id := by
    intro A B f
    apply FreeBindingClone.Hom.ext
    exact FreeBindingTerms.Hom.ext (fun _ => rfl)
  assoc := by
    intro A B C D f g h
    apply FreeBindingClone.Hom.ext
    exact FreeBindingTerms.Hom.ext (fun _ => rfl)

/-- The existing equation quotient, now carrying the complete binder-aware
algebra and the proof of semantic equation satisfaction. -/
noncomputable abbrev presented (E : List (EqAxiom S M)) : Model E where
  algebra := BindingEquationQuotientModel.algebra E
  satisfies := BindingEquationQuotientModel.algebra_satisfies E

variable {E : List (EqAxiom S M)}

section Sound

open BindingEquationInterpretation (CongruenceSound)

variable (A : BindingCloneAlgebra.Algebra.{u} S) (sound : CongruenceSound A E)

/-- The quotient interpretation of an arbitrary equation class can be read
from any representative. -/
theorem interpretQuotient_out {Γ : Ctx S} {sort : S.Srt} (q : TermQ E Γ sort) :
    interpretQuotient A sound q =
      BindingCloneFoldSubstitution.interpret A (Quotient.out q) := by
  have h := interpretQuotient_mk A sound (Quotient.out q)
  rw [Quotient.out_eq] at h
  exact h

theorem interpretArgs_representativeArgs :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S (TermQ E) arity Γ),
      BindingCloneFoldSubstitution.interpretArgs A
        (BindingEquationQuotientModel.representativeArgs E args) =
      FamilyArgs.map (interpretQuotient A sound) args
  | _, _, .nil => rfl
  | _, _, .cons head tail =>
      congrArg₂ FamilyArgs.cons
        (interpretQuotient_out A sound head).symm
        (interpretArgs_representativeArgs tail)

/-- An algebra in which the generated congruence is sound receives a
binding-clone morphism from the presented quotient. -/
noncomputable def quotientHom :
    FreeBindingClone.Hom (presented E).algebra A where
  raw :=
    { map := interpretQuotient A sound
      map_variable := by intro Γ sort v; rfl
      map_operation := by
        intro Γ sort op args
        change interpretQuotient A sound
            (Quotient.mk _
              (Term.op op
                (BindingEquationQuotientModel.representativeArgs E args))) =
          A.operation op (FamilyArgs.map (interpretQuotient A sound) args)
        rw [interpretQuotient_mk]
        change A.operation op
            (BindingCloneFoldSubstitution.interpretArgs A
              (BindingEquationQuotientModel.representativeArgs E args)) = _
        exact congrArg (A.operation op) (interpretArgs_representativeArgs A sound args) }
  map_substitute := by
    intro Γ Δ sort env q
    change interpretQuotient A sound (substitute E env q) =
      A.substitution.substitute (fun s v => interpretQuotient A sound (env s v))
        (interpretQuotient A sound q)
    rw [substitute_eq_bindQ E env (representativeEnv E env) (mk_representativeEnv E env) q]
    rw [interpretQuotient_bindQ]
    congr 1
    funext s v
    exact (interpretQuotient_out A sound (env s v)).symm

end Sound

/-- The quotient interpretation is a full binding-clone morphism. -/
noncomputable def interpretHom (A : Model.{u} E) :
    FreeBindingClone.Hom (presented E).algebra A.algebra :=
  quotientHom A.algebra A.satisfies.congruenceSound

/-- Any binding-clone morphism from the presented quotient agrees on every
representative with the unique raw-term fold, hence with `interpretHom`. -/
theorem hom_unique (A : Model.{u} E)
    (h : FreeBindingClone.Hom (presented E).algebra A.algebra) :
    h = interpretHom A := by
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intro Γ sort q
  induction q using Quotient.inductionOn with
  | _ term =>
      have fromTerms := FreeBindingClone.hom_unique A.algebra
        (FreeBindingClone.Hom.comp
          (BindingEquationQuotientModel.projection E) h)
      have onTerm := congrArg
        (fun f : FreeBindingClone.Hom (BindingCloneAlgebra.terms S)
          A.algebra => f.raw.map term) fromTerms
      change h.raw.map (Quotient.mk _ term) =
        BindingCloneFoldSubstitution.interpret A.algebra term at onTerm
      exact onTerm.trans (interpretQuotient_mk A.algebra A.satisfies.congruenceSound term).symm

/-- The presented quotient is initial among binding-clone models satisfying
the authored equations. -/
noncomputable def presentedIsInitial (E : List (EqAxiom S M)) :
    IsInitial (presented E) :=
  IsInitial.ofUniqueHom interpretHom (fun A h => hom_unique A h)

end Mettapedia.OSLF.Binding.FreeBindingEquationModel
