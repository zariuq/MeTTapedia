import Mettapedia.OSLF.Syntax.SemanticSchemaNaturality
import Mettapedia.OSLF.Syntax.BindingContextualEquationInterpretation
import Mettapedia.OSLF.Syntax.EquationalQuotient

/-!
# Interpreting authored binding equation schemas

Equation satisfaction uses the existing contextual semantic fold, with
separate declared dependencies, captured ambient values and ordinary schema
variables. The argument fold retains every operator's binder context.
Dependency-only satisfaction remains a separately named condition.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingEquationInterpretation

open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.BindingCloneFoldSubstitution
open Mettapedia.OSLF.Binding.BindingEquationalModels

universe u v

variable {S : Signature} {M : List (MetaArity S)}

/-- The dependency-only equation condition does not quantify contextual
metavariable bodies. It is separate from contextual satisfaction. -/
def DependencySatisfies (A : BindingCloneAlgebra.Algebra.{u} S)
    (E : List (EqAxiom S M)) : Prop :=
  ∀ (i : Fin E.length) (valuation : MetaValuation A M)
    {Γ : Ctx S}
    (env : BindingSubstitutionAlgebra.Environment S
      A.substitution.Carrier (E.get i).ctx Γ),
    A.substitution.substitute env
      (interpretSchema A valuation (E.get i).lhs) =
    A.substitution.substitute env
      (interpretSchema A valuation (E.get i).rhs)

/-- Every contextual semantic instance holds, with arbitrary captured
bodies and independent ambient and ordinary environments. -/
def Satisfies (A : BindingCloneAlgebra.Algebra.{u} S)
    (E : List (EqAxiom S M)) : Prop :=
  BindingContextualEquationInterpretation.Satisfies A E

/-- Each authored equation instance remains valid after transporting all its
semantic metavariables and ordinary variables along a model morphism. This
is an image statement; it does not assert that an arbitrary target
valuation factors through the morphism. -/
theorem mapped_dependency_equation_instance
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    {E : List (EqAxiom S M)} (satisfies : DependencySatisfies A E)
    (i : Fin E.length) (valuation : MetaValuation A M)
    {Δ : Ctx S}
    (env : BindingSubstitutionAlgebra.Environment S
      A.substitution.Carrier (E.get i).ctx Δ) :
    B.substitution.substitute (fun s x => h.raw.map (env s x))
      (interpretSchema B (mapMetaValuation h valuation) (E.get i).lhs) =
    B.substitution.substitute (fun s x => h.raw.map (env s x))
      (interpretSchema B (mapMetaValuation h valuation) (E.get i).rhs) := by
  exact (interpretSchema_closed_map h valuation env (E.get i).lhs).symm.trans
    ((congrArg h.raw.map (satisfies i valuation env)).trans
      (interpretSchema_closed_map h valuation env (E.get i).rhs))

/-- A contextual equation instance transports along a full binding-clone
map, preserving both supplied environments. Only image values are claimed. -/
theorem mapped_equation_instance
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    {E : List (EqAxiom S M)} (satisfies : Satisfies A E)
    (i : Fin E.length) {Θ Γ : Ctx S}
    (body : SemanticContextualMetavariables.Valuation (M := M) A Θ)
    (ambient : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier Θ Γ)
    (ordinary : BindingSubstitutionAlgebra.Environment S
      A.substitution.Carrier (E.get i).ctx Γ) :
    SemanticContextualMetavariables.interpretSchema B
        (SemanticContextualMetavariables.mapValuation h body)
        (fun s v => h.raw.map (ambient s v))
        (fun s v => h.raw.map (ordinary s v)) (E.get i).lhs =
      SemanticContextualMetavariables.interpretSchema B
        (SemanticContextualMetavariables.mapValuation h body)
        (fun s v => h.raw.map (ambient s v))
        (fun s v => h.raw.map (ordinary s v)) (E.get i).rhs :=
  (SemanticContextualMetavariables.interpretSchema_map h body ambient ordinary (E.get i).lhs).symm.trans
    ((congrArg h.raw.map (satisfies i body ambient ordinary)).trans
      (SemanticContextualMetavariables.interpretSchema_map h body ambient ordinary (E.get i).rhs))

/-- The shared semantic comparison identifies the interpretations of
every actual syntactic contextual equation instance. -/
theorem Satisfies.interpret_instance {A : BindingCloneAlgebra.Algebra.{u} S}
    {E : List (EqAxiom S M)} (satisfies : Satisfies A E)
    (i : Fin E.length) {Θ Γ : Ctx S} (body : ContextualAssignment S M Θ)
    (ambient : Sub S Θ Γ) (ordinary : Sub S (E.get i).ctx Γ) :
    interpret A (ContextualAssignment.instantiate body ambient ordinary (E.get i).lhs) =
      interpret A (ContextualAssignment.instantiate body ambient ordinary (E.get i).rhs) :=
  BindingContextualEquationInterpretation.Satisfies.interpret_instance
    satisfies i body ambient ordinary


mutual

/-- Every semantic equation model identifies all pairs in the generated
syntactic congruence, including instances beneath binders. -/
theorem interpret_eqClosure
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {E : List (EqAxiom S M)} (satisfies : Satisfies A E) :
    ∀ {Γ : Ctx S} {sort : S.Srt}
      {left right : Term S Γ sort}, EqClosure E left right →
      interpret A left = interpret A right
  | _, _, _, _, .ax i body ambient ordinary =>
      satisfies.interpret_instance i body ambient ordinary
  | _, _, _, _, .refl _ => rfl
  | _, _, _, _, .symm h => (interpret_eqClosure A satisfies h).symm
  | _, _, _, _, .trans h h' =>
      (interpret_eqClosure A satisfies h).trans
        (interpret_eqClosure A satisfies h')
  | _, _, _, _, .cong op argsEq => by
      change A.operation op (interpretArgs A _) =
        A.operation op (interpretArgs A _)
      exact congrArg (A.operation op)
        (interpretArgs_eqArgs A satisfies argsEq)

/-- The congruence induction follows every argument into the binder context
declared for that argument. -/
theorem interpretArgs_eqArgs
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {E : List (EqAxiom S M)} (satisfies : Satisfies A E) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      {left right : Args S arity Γ}, EqArgs E left right →
      interpretArgs A left = interpretArgs A right
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons headEq tailEq =>
      congrArg₂ FamilyArgs.cons
        (interpret_eqClosure A satisfies headEq)
        (interpretArgs_eqArgs A satisfies tailEq)

end

/-- The congruence generated by the equations holds in the algebra's
interpretation of terms. Semantic satisfaction implies it; it is exactly what
an interpretation of the equation quotient needs. -/
def CongruenceSound (A : BindingCloneAlgebra.Algebra.{u} S) (E : List (EqAxiom S M)) : Prop :=
  ∀ {Γ : Ctx S} {sort : S.Srt} {left right : Term S Γ sort},
    EqClosure E left right → interpret A left = interpret A right

theorem Satisfies.congruenceSound {A : BindingCloneAlgebra.Algebra.{u} S}
    {E : List (EqAxiom S M)} (satisfies : Satisfies A E) : CongruenceSound A E :=
  fun h => interpret_eqClosure A satisfies h

/-- An algebra in which the generated congruence is sound receives a
well-defined interpretation from every context-and-sort fibre of the
syntactic equation quotient. -/
def interpretQuotient
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {E : List (EqAxiom S M)} (sound : CongruenceSound A E)
    {Γ : Ctx S} {sort : S.Srt} :
    TermQ E Γ sort → A.substitution.Carrier Γ sort :=
  Quotient.lift (interpret A) (fun _ _ h => sound h)

theorem interpretQuotient_mk
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {E : List (EqAxiom S M)} (sound : CongruenceSound A E)
    {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) :
    interpretQuotient A sound (Quotient.mk _ term) =
      interpret A term := rfl

/-- The quotient interpretation commutes with the repository's quotient
substitution by a syntactic environment. -/
theorem interpretQuotient_bindQ
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {E : List (EqAxiom S M)} (sound : CongruenceSound A E)
    {Γ Δ : Ctx S} {sort : S.Srt}
    (sigma : Sub S Γ Δ) (q : TermQ E Γ sort) :
    interpretQuotient A sound (bindQ (E := E) sigma q) =
      A.substitution.substitute
        (fun s v => interpret A (sigma s v))
        (interpretQuotient A sound q) := by
  induction q using Quotient.inductionOn with
  | _ term => exact interpret_bind A sigma term

/-- Any family of maps out of the quotient that agrees with the term fold on
representatives agrees with this factorization everywhere. -/
theorem interpretQuotient_unique
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {E : List (EqAxiom S M)} (sound : CongruenceSound A E)
    {Γ : Ctx S} {sort : S.Srt}
    (map : TermQ E Γ sort → A.substitution.Carrier Γ sort)
    (onTerms : ∀ term : Term S Γ sort,
      map (Quotient.mk _ term) = interpret A term) :
    map = interpretQuotient A sound := by
  funext q
  induction q using Quotient.inductionOn with
  | _ term => exact onTerms term

end Mettapedia.OSLF.Binding.BindingEquationInterpretation
