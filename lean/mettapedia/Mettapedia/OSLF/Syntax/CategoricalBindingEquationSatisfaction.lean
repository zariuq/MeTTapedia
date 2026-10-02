import Mettapedia.OSLF.Syntax.CategoricalBindingFunctor
import Mettapedia.OSLF.Syntax.SecondOrderEquationContext
import Mettapedia.OSLF.Syntax.ContextualMetavariableAssignment

/-!
# Satisfaction of authored equation presentations

The model contract is stated independently of quotient soundness and
interpretation functors.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

namespace Model

variable {S : Signature} (M : Model S D)

/-- The original axiom law uses bodies in their declared dependency contexts. -/
def DependencySatisfiesAxioms (N : List (MetaArity S)) {schema : List (MetaArity S)}
    (E : List (EqAxiom (withMetas S N) schema)) : Prop :=
  ∀ (i : Fin E.length)
    (body : (k : Fin schema.length) → Term (withMetas S N) (schema.get k).1 (schema.get k).2),
    M.interp N (instantiate body (E.get i).lhs) = M.interp N (instantiate body (E.get i).rhs)

/-- The original dependency-only law at every metavariable context. -/
def DependencySatisfies {schema : List (MetaArity S)} (P : EquationPresentation S schema) : Prop :=
  ∀ X : Object S, M.DependencySatisfiesAxioms X.arities (P.axioms X)

/-- Equation instances may capture a separate ambient context as well as
receive their declared dependency arguments. Both environments are explicit. -/
def SatisfiesAxioms (N : List (MetaArity S)) {schema : List (MetaArity S)}
    (E : List (EqAxiom (withMetas S N) schema)) : Prop :=
  ∀ (i : Fin E.length) {Θ Δ : Ctx S}
    (body : ContextualAssignment (withMetas S N) schema Θ)
    (ambient : Sub (withMetas S N) Θ Δ)
    (ordinary : Sub (withMetas S N) (E.get i).ctx Δ),
    M.interp N (ContextualAssignment.instantiate body ambient ordinary (E.get i).lhs) =
      M.interp N (ContextualAssignment.instantiate body ambient ordinary (E.get i).rhs)

/-- Contextual satisfaction at every second-order stage is independent of
the generated quotient and its interpretation. -/
def Satisfies {schema : List (MetaArity S)}
    (P : EquationPresentation S schema) : Prop :=
  ∀ X : Object S, M.SatisfiesAxioms X.arities (P.axioms X)

/-- Contextual instances include every dependency-only instance, with no
restriction on the equation presentation. -/
theorem SatisfiesAxioms.toDependencySatisfiesAxioms
    {N : List (MetaArity S)} {schema : List (MetaArity S)}
    {E : List (EqAxiom (withMetas S N) schema)}
    (sat : M.SatisfiesAxioms N E) : M.DependencySatisfiesAxioms N E := by
  intro i body
  have equality := sat i (ContextualAssignment.ofClosed body [])
    (fun _ v => nomatch v) (fun _ v => Term.var v)
  simpa only [ContextualAssignment.instantiate_ofClosed, bind_id] using equality

/-- Forgetting the additional instances preserves global satisfaction. -/
theorem Satisfies.toDependencySatisfies {schema : List (MetaArity S)}
    {P : EquationPresentation S schema} (sat : M.Satisfies P) :
    M.DependencySatisfies P :=
  fun X => SatisfiesAxioms.toDependencySatisfiesAxioms M (sat X)


/-- The contextual name denotes the canonical full instance contract. -/
abbrev ContextualSatisfiesAxioms (N : List (MetaArity S)) {schema : List (MetaArity S)}
    (E : List (EqAxiom (withMetas S N) schema)) : Prop := M.SatisfiesAxioms N E

/-- The contextual name denotes canonical satisfaction at all stages. -/
abbrev ContextualSatisfies {schema : List (MetaArity S)}
    (P : EquationPresentation S schema) : Prop := M.Satisfies P

end Model

end Mettapedia.OSLF.Binding.CategoricalBindingModel
