import Mettapedia.OSLF.Syntax.ContextualEquationInstances
import Mettapedia.OSLF.Syntax.MonoidEquationRung
import Mettapedia.OSLF.Syntax.EquationTransport

/-!
# The unit law as an ordinary equation and as a metavariable schema

Both presentations express the same intended monoid law. The existing
ordinary-variable presentation proves the unit law for every open term.
The metavariable schema generates it on both template parameters and
ordinary free variables through the shared contextual instantiator.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.MonoidContextualEquationControl

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.MonoidEquationRung (sig Srt Op unitT mulT monoidE)
open Mettapedia.OSLF.Binding.SecondOrderContext

abbrev parameter : List (MetaArity sig) := [([], Srt.element)]

def schemaParameter : Term (withMetas sig parameter) [] Srt.element :=
  metaVar (S := sig) (M := parameter) ⟨0, by decide⟩

/-- The same unit law written with a nullary schema parameter. -/
def schemaLeftUnit : EqAxiom sig parameter where
  ctx := []
  sort := Srt.element
  lhs := .op (Sum.inl Op.mul)
    (.cons (.op (Sum.inl Op.unit) .nil) (.cons schemaParameter .nil))
  rhs := schemaParameter

abbrev schemaAxioms : List (EqAxiom sig parameter) := [schemaLeftUnit]

def x : Term sig [Srt.element] Srt.element := .var .zero

/-- The existing ordinary-variable monoid presentation already handles x. -/
theorem ordinary_presentation_unit_law : EqClosure monoidE (mulT unitT x) x :=
  MonoidEquationRung.raw_left_unit x

/-- A schema parameter can be supplied by an actual closed template
parameter in an extended second-order signature. -/
theorem schema_template_parameter_unit_law :
    EqClosure (schemaAxioms.map (liftEquation (⟨parameter⟩ : Object sig)))
      (Term.op (Sum.inl Op.mul)
        (.cons (.op (Sum.inl Op.unit) .nil) (.cons schemaParameter .nil)))
      schemaParameter := by
  let body : (i : Fin parameter.length) →
      Term (withMetas sig parameter) (parameter.get i).1 (parameter.get i).2 :=
    fun i => Fin.cases schemaParameter (fun i => Fin.elim0 i) i
  let env : Sub (withMetas sig parameter) [] [] := fun _ v => .var v
  exact EqClosure.ax_closed (schemaAxioms.map (liftEquation (⟨parameter⟩ : Object sig)))
    ⟨0, by decide⟩ body env

def variableBody : ContextualAssignment sig parameter [Srt.element] :=
  fun i => Fin.cases x (fun i => Fin.elim0 i) i

def noVariables : Sub sig [] [Srt.element] := fun _ v => nomatch v

/-- The common instantiator computes the ordinary open unit law.
Its ambient variable has not been added to the parameter's declared arity. -/
theorem contextual_instance_recovers_open_unit_law :
    ContextualEquationInstances.instantiateAt schemaLeftUnit variableBody noVariables =
      (mulT unitT x, x) := rfl

/-- The authored schema now proves the ordinary open unit law. -/
theorem schema_open_unit_law : EqClosure schemaAxioms (mulT unitT x) x := by
  simpa [schemaAxioms, schemaLeftUnit, schemaParameter, metaVar, idArgs,
    variableBody, noVariables, ContextualAssignment.instantiate,
    ContextualAssignment.instantiateArgs, ContextualAssignment.apply,
    ContextualAssignment.joinSub, ContextualAssignment.weakenSub,
    bind, bindArgs, liftSub, rename, renameArgs, weakenVar, unitT, mulT, x] using
      (EqClosure.ax (E := schemaAxioms) ⟨0, by decide⟩ variableBody
        (fun _ v => .var v) noVariables)

/-- The program quotient identifies the open unit expression with x. -/
theorem schema_program_classes_equal :
    (Quotient.mk _ (mulT unitT x) : TermQ schemaAxioms [Srt.element] Srt.element) =
      Quotient.mk _ x := Quotient.sound schema_open_unit_law

/-- Every contextual instance of the schema is an ordinary monoid unit law.
The captured context and the ordinary environment remain independent. -/
theorem schema_instance_is_unit_law {Θ Γ : Ctx sig}
    (body : ContextualAssignment sig parameter Θ)
    (ambient : Sub sig Θ Γ) (ordinary : Sub sig [] Γ) :
    ContextualAssignment.instantiate body ambient ordinary schemaLeftUnit.lhs =
      mulT unitT
        (ContextualAssignment.instantiate body ambient ordinary schemaLeftUnit.rhs) := by
  change mulT unitT (bind (ContextualAssignment.weakenSub [] ambient) (body ⟨0, by decide⟩)) =
    mulT unitT (bind ambient (body ⟨0, by decide⟩))
  exact congrArg (fun env => mulT unitT (bind env (body ⟨0, by decide⟩)))
    (ContextualAssignment.weakenSub_nil (S := sig) ambient)

/-- The schema's generators are justified by the independently authored
monoid presentation, through the existing signature-transport interface. -/
theorem schema_interpreted_in_monoid :
    (SigMor.ident sig).RespectsEquations schemaAxioms monoidE := by
  intro index Θ Γ body ambient ordinary
  obtain rfl : index = ⟨0, by decide⟩ := Fin.eq_zero index
  change EqClosure monoidE
    ((SigMor.ident sig).onTerm
      (ContextualAssignment.instantiate body ambient ordinary schemaLeftUnit.lhs))
    ((SigMor.ident sig).onTerm
      (ContextualAssignment.instantiate body ambient ordinary schemaLeftUnit.rhs))
  have instanceEq := schema_instance_is_unit_law body ambient ordinary
  have mapped := congrArg (fun term : Term sig Γ Srt.element => (SigMor.ident sig).onTerm term)
    instanceEq
  refine Eq.mp (congrArg (fun lhs => EqClosure monoidE lhs
    ((SigMor.ident sig).onTerm
      (ContextualAssignment.instantiate body ambient ordinary schemaLeftUnit.rhs))) mapped.symm) ?_
  exact MonoidEquationRung.raw_left_unit
    ((SigMor.ident sig).onTerm
      (ContextualAssignment.instantiate body ambient ordinary schemaLeftUnit.rhs))

/-- The template law holds for every program body in every ordinary context. -/
theorem schema_left_unit {Γ : Ctx sig} (term : Term sig Γ Srt.element) :
    EqClosure schemaAxioms (mulT unitT term) term := by
  let body : ContextualAssignment sig parameter Γ :=
    fun i => Fin.cases term (fun j => Fin.elim0 j) i
  let ordinary : Sub sig [] Γ := fun _ v => nomatch v
  have generated := EqClosure.ax (E := schemaAxioms) ⟨0, by decide⟩
    body (fun _ v => Term.var v) ordinary
  change EqClosure schemaAxioms
    (ContextualAssignment.instantiate body (fun _ v => Term.var v) ordinary schemaLeftUnit.lhs)
    (ContextualAssignment.instantiate body (fun _ v => Term.var v) ordinary schemaLeftUnit.rhs)
      at generated
  have rhs : ContextualAssignment.instantiate body (fun _ v => Term.var v)
      ordinary schemaLeftUnit.rhs = term := by
    change bind (fun _ v => Term.var v) term = term
    exact bind_id term
  have lhs := (schema_instance_is_unit_law body (fun _ v => Term.var v) ordinary).trans
    (congrArg (mulT unitT) rhs)
  exact Eq.mp (congrArg₂ (fun left right => EqClosure schemaAxioms left right) lhs rhs) generated

/-- Contextual parameters do not make the unit schema identify the two
orders of distinct program inputs. -/
theorem schema_does_not_impose_commutativity :
    ¬ EqClosure schemaAxioms
      (mulT (Term.var (Var.zero : Var [Srt.element, Srt.element] Srt.element))
        (Term.var (Var.succ Var.zero)))
      (mulT (Term.var (Var.succ Var.zero)) (Term.var Var.zero)) := by
  intro related
  have transported := (SigMor.ident sig).eqClosure_map schema_interpreted_in_monoid
    (fun _ v => v) related
  change EqClosure monoidE
    (mapTerm (SigMor.ident sig) (fun _ v => v)
      (mulT (Term.var (Var.zero : Var [Srt.element, Srt.element] Srt.element))
        (Term.var (Var.succ Var.zero))))
    (mapTerm (SigMor.ident sig) (fun _ v => v)
      (mulT (Term.var (Var.succ Var.zero)) (Term.var Var.zero))) at transported
  have left : mapTerm (SigMor.ident sig) (fun _ v => v)
      (mulT (Term.var (Var.zero : Var [Srt.element, Srt.element] Srt.element))
        (Term.var (Var.succ Var.zero))) =
      mulT (Term.var Var.zero) (Term.var (Var.succ Var.zero)) :=
    (mapTerm_ident (S := sig) (fun _ v => v) _).trans (rename_id _)
  have right : mapTerm (SigMor.ident sig) (fun _ v => v)
      (mulT (Term.var (Var.succ Var.zero))
        (Term.var (Var.zero : Var [Srt.element, Srt.element] Srt.element))) =
      mulT (Term.var (Var.succ Var.zero)) (Term.var Var.zero) :=
    (mapTerm_ident (S := sig) (fun _ v => v) _).trans (rename_id _)
  exact MonoidEquationRung.mul_variables_not_commutative
    (Eq.mp (congrArg₂ (fun lhs rhs => EqClosure monoidE lhs rhs) left right) transported)

/-- The two input orders also remain distinct in the actual schema quotient. -/
theorem schema_program_classes_not_commutative :
    (Quotient.mk _
      (mulT (Term.var (Var.zero : Var [Srt.element, Srt.element] Srt.element))
        (Term.var (Var.succ Var.zero))) :
      TermQ schemaAxioms [Srt.element, Srt.element] Srt.element) ≠
    Quotient.mk _ (mulT (Term.var (Var.succ Var.zero)) (Term.var Var.zero)) := by
  intro same
  exact schema_does_not_impose_commutativity (Quotient.exact same)

end Mettapedia.OSLF.Binding.MonoidContextualEquationControl
