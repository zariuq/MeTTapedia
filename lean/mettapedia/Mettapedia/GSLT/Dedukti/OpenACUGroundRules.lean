import Mettapedia.GSLT.Dedukti.GroundACU
import Mettapedia.GSLT.Dedukti.PureTypeSystem
import Mettapedia.GSLT.Contracts.ACGroundMatching

/-!
# Open homogeneous LF rules at ground ACU subjects

The metavariables of one homogeneous rule are distinct LF context
slots. Instantiating a printed rule has the same meaning as printing
its instantiated template. The finite search computes all one-step
successor classes, with a real contextual LF contraction between
the two equation endpoints.

This extends ground rule declarations to open patterns, not the
calculus of dependent conversion or higher-order matching.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.GroundACU

open Mettapedia.GSLT.LanguageDef.LF (Term)
open Mettapedia.GSLT.LanguageDef.LFTyping (Ctx ctxLookup lift)
open Mettapedia.GSLT.Contracts
open ACUReplacement.GroundMatching (Template Schema)

namespace Declaration

variable (d : Declaration) {n : Nat}

def renderTemplate : Template (Fin n) d.Atom → Term
  | .hole index => .var index.val
  | .atom name => .con name.val
  | .unit => .con d.identity
  | .op a b => d.binary (renderTemplate a) (renderTemplate b)

/-- Slots outside the declared context do not occur in the code. -/
def assignment (values : Fin n → d.Expr) (slot : Nat) : Term :=
  if inside : slot < n then d.render (values ⟨slot, inside⟩) else .con d.identity

theorem inst_renderTemplate (p : Template (Fin n) d.Atom) (values : Fin n → d.Expr) :
    inst (d.assignment values) (d.renderTemplate p) = d.render (p.instantiate values) := by
  induction p with
  | hole v => simp [renderTemplate, assignment, v.isLt, Template.instantiate]
  | atom _ | unit => rfl
  | op _ _ first second =>
      simp only [renderTemplate, Template.instantiate, render, binary, inst_app, inst_con, first, second]

def renderSchema (r : Schema (Fin n) d.Atom) : RewriteRule :=
  ⟨d.renderTemplate r.lhs, d.renderTemplate r.rhs⟩

/-- An ambient LF signature with one declared rule schema, before
adding the ACU equivalence around its contextual contractions. -/
def schemaTheory (r : Schema (Fin n) d.Atom) : Theory :=
  { d.theory [] with rule := (· = d.renderSchema r) }

theorem lookup_homogeneous (v : Fin n) :
    ctxLookup (List.replicate n d.carrierType) v.val = some d.carrierType := by
  rw [ctxLookup_eq_getElem?, List.getElem?_replicate, if_pos v.isLt]
  rfl

theorem renderTemplate_typed (rule : Schema (Fin n) d.Atom)
    (p : Template (Fin n) d.Atom) :
    LambdaPiModulo (d.schemaTheory rule) (List.replicate n d.carrierType)
      (d.renderTemplate p) d.carrierType := by
  induction p with
  | hole index => exact .var (d.lookup_homogeneous index)
  | atom name => exact .con (by
      simp [schemaTheory, theory, name.property.1, name.property.2.1])
  | unit => exact .con (by
      simp [schemaTheory, theory, d.carrier_ne_identity.symm, d.operator_ne_identity.symm])
  | op a b ihA ihB =>
      have opTyped : LambdaPiModulo (d.schemaTheory rule) (List.replicate n d.carrierType)
          (.con d.operator) d.operationType :=
        .con (by simp [schemaTheory, theory, d.carrier_ne_operator.symm])
      have partialTyped : LambdaPiModulo (d.schemaTheory rule) (List.replicate n d.carrierType)
          (.app (.con d.operator) (d.renderTemplate a)) (.pi d.carrierType d.carrierType) :=
        .app opTyped ihA
      exact .app partialTyped ihB

theorem instance_at_context (rule : Schema (Fin n) d.Atom)
    (values : Fin n → d.Expr) (context : ACUReplacement.Context d.Atom) :
    Step (d.schemaTheory rule)
      (d.render (context.plug (rule.lhs.instantiate values)))
      (d.render (context.plug (rule.rhs.instantiate values))) := by
  rw [← d.render_plug, ← d.render_plug]
  apply Step.inContext
  have root := RootStep.rule (theory := d.schemaTheory rule)
    (rule := d.renderSchema rule) (d.assignment values) rfl
  simpa only [renderSchema, inst_renderTemplate] using root

/-- This uses the same LF substitution action on both sides of the
root step. No conversion of a rewrite arrow into an equation is used. -/
theorem canonical_open_rule_iff (rule : Schema (Fin n) d.Atom) (a b : d.Expr) :
    ACUReplacement.operands b ∈ ACUReplacement.GroundMatching.successorKeys rule
      (ACUReplacement.operands a) ↔
      ∃ (values : Fin n → d.Expr) (context : ACUReplacement.Context d.Atom),
        ACUReplacement.Equation a (context.plug (rule.lhs.instantiate values)) ∧
        Step (d.schemaTheory rule)
          (d.render (context.plug (rule.lhs.instantiate values)))
          (d.render (context.plug (rule.rhs.instantiate values))) ∧
        ACUReplacement.Equation (context.plug (rule.rhs.instantiate values)) b := by
  rw [ACUReplacement.GroundMatching.canonical_successors_exact, ACUReplacement.reduces_iff_context]
  constructor
  · rintro ⟨ground, ⟨values, rfl⟩, context, first, last⟩
    exact ⟨values, context, first, d.instance_at_context rule values context, last⟩
  · rintro ⟨values, context, first, _, last⟩
    exact ⟨rule.instanceAt values, ⟨values, rfl⟩, context, first, last⟩

theorem canonical_open_ac_rule_iff (rule : Schema (Fin n) d.Atom) {a b : d.Expr}
    (lhs : rule.lhs.UnitFree) (rhs : rule.rhs.UnitFree)
    (aFree : ACUReplacement.AC.UnitFree a) (bFree : ACUReplacement.AC.UnitFree b) :
    ACUReplacement.operands b ∈ ACUReplacement.GroundMatching.successorKeysAC rule
      (ACUReplacement.operands a) ↔
      ∃ (values : Fin n → d.Expr) (context : ACUReplacement.Context d.Atom),
        (∀ v, ACUReplacement.AC.UnitFree (values v)) ∧ ACUReplacement.AC.UnitFreeContext context ∧
        ACUReplacement.AC.Equation a (context.plug (rule.lhs.instantiate values)) ∧
        Step (d.schemaTheory rule)
          (d.render (context.plug (rule.lhs.instantiate values)))
          (d.render (context.plug (rule.rhs.instantiate values))) ∧
        ACUReplacement.AC.Equation (context.plug (rule.rhs.instantiate values)) b := by
  rw [ACUReplacement.GroundMatching.canonical_AC_successors_exact rule lhs rhs aFree bFree]
  constructor
  · rintro ⟨terms, context, free, contextFree, first, last⟩
    exact ⟨terms, context, free, contextFree, first, d.instance_at_context rule terms context, last⟩
  · rintro ⟨terms, context, free, contextFree, first, _, last⟩
    exact ⟨terms, context, free, contextFree, first, last⟩

end Declaration

#print axioms Declaration.inst_renderTemplate
#print axioms Declaration.renderTemplate_typed
#print axioms Declaration.instance_at_context
#print axioms Declaration.canonical_open_rule_iff
#print axioms Declaration.canonical_open_ac_rule_iff

end Mettapedia.GSLT.Dedukti.GroundACU
