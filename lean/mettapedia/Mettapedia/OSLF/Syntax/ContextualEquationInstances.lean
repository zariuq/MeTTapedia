import Mettapedia.OSLF.Syntax.ContextualMetavariableAssignment
import Mettapedia.OSLF.Syntax.SecondOrderVariableAbstractionControls

/-!
# Authored equation instances with an explicit ambient context

The existing contextual assignment supplies each schema metavariable in its
declared dependency context followed by the ambient context. The same
instantiator used for scoped templates gives the two sides of an equation
instance. These sides commute with substitution, and recover every old
closed-body instance exactly. The generated equation closure admits these
contextual instances through its single axiom constructor.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualEquationInstances

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualAssignment

variable {S : Signature} {M : List (MetaArity S)}

/-- Instantiate the two authored sides in one ambient context, with each
metavariable's dependencies kept separate from that context. -/
def instantiateAt (equation : EqAxiom S M) {Γ : Ctx S}
    (body : ContextualAssignment S M Γ) (env : Sub S equation.ctx Γ) :
    Term S Γ equation.sort × Term S Γ equation.sort :=
  (ContextualAssignment.instantiate body (fun _ v => .var v) env equation.lhs,
    ContextualAssignment.instantiate body (fun _ v => .var v) env equation.rhs)

/-- Contextual instantiation includes the entire old closed-body domain. -/
theorem instantiateAt_ofClosed (equation : EqAxiom S M) {Γ : Ctx S}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (env : Sub S equation.ctx Γ) :
    instantiateAt equation (ofClosed body Γ) env =
      (bind env (Mettapedia.OSLF.Binding.instantiate body equation.lhs),
        bind env (Mettapedia.OSLF.Binding.instantiate body equation.rhs)) :=
  Prod.ext (instantiate_ofClosed body _ env equation.lhs)
    (instantiate_ofClosed body _ env equation.rhs)

/-- Transporting an equation instance substitutes into both its ambient
metavariable values and its ordinary-variable environment. -/
theorem instantiateAt_substitution (equation : EqAxiom S M) {Γ Δ : Ctx S}
    (body : ContextualAssignment S M Γ) (env : Sub S equation.ctx Γ)
    (sigma : Sub S Γ Δ) :
    Prod.map (bind sigma) (bind sigma) (instantiateAt equation body env) =
      instantiateAt equation (mapSub sigma body)
        (fun s v => bind sigma (env s v)) := by
  apply Prod.ext
  · dsimp only [instantiateAt, Prod.map]
    rw [bind_instantiate, instantiate_mapSub]
    simp only [bind, bind_id]
  · dsimp only [instantiateAt, Prod.map]
    rw [bind_instantiate, instantiate_mapSub]
    simp only [bind, bind_id]

/-- The renaming law is the variable-valued substitution instance. -/
theorem instantiateAt_renaming (equation : EqAxiom S M) {Γ Δ : Ctx S}
    (body : ContextualAssignment S M Γ) (env : Sub S equation.ctx Γ)
    (rho : Ren S Γ Δ) :
    Prod.map (rename rho) (rename rho) (instantiateAt equation body env) =
      instantiateAt equation (mapRen rho body)
        (fun s v => rename rho (env s v)) := by
  have convert : (bind (fun s v => Term.var (rho s v)) :
      Term S Γ equation.sort → Term S Δ equation.sort) = rename rho := by
    funext term
    exact bind_var_eq_rename rho term
  simpa only [convert, bind_var_eq_rename, mapSub_var] using
    instantiateAt_substitution equation body env (fun s v => .var (rho s v))

namespace Controls

open SecondOrderVariableAbstraction.Controls

/-- The schema's nullary metavariable may refer to the separately supplied
ambient variable. It acquires no declared dependency arguments. -/
def variableBody : ContextualAssignment signature schemaMetas [()] :=
  fun i => Fin.cases (.var .zero) (fun i => Fin.elim0 i) i

def noVariables : Sub signature [] [()] := fun _ v => nomatch v

def constantBody : (i : Fin schemaMetas.length) →
    Term signature (schemaMetas.get i).1 (schemaMetas.get i).2 :=
  fun i => Fin.cases constant (fun i => Fin.elim0 i) i

/-- The contextual instance computes the variable/constant pair with the
ambient variable distinct from declared dependency arguments. -/
theorem contextual_instance_is_variable_constant :
    instantiateAt closedEquation variableBody noVariables =
      ((Term.var Var.zero : Term signature [()] ()), constant) := rfl

/-- A closed value remains the original closed instance. -/
theorem closed_instance_is_constant_constant :
    instantiateAt closedEquation
      (ofClosed constantBody [()]) noVariables =
      (constant, constant) := rfl

/-- The actual equation closure admits the supplied ambient variable. -/
theorem contextual_instance_in_closure :
    EqClosure equations (Term.var Var.zero : Term signature [()] ()) constant := by
  simpa [equations, closedEquation, variableBody, noVariables, metaVar,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    ContextualAssignment.apply, ContextualAssignment.joinSub, bind, bindArgs,
    embed, embedArgs, constant] using
      (EqClosure.ax (E := equations) ⟨0, by decide⟩ variableBody
        (fun _ v => .var v) noVariables)

end Controls

end Mettapedia.OSLF.Binding.ContextualEquationInstances
