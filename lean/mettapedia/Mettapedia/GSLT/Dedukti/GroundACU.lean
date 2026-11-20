import Mettapedia.GSLT.Dedukti.Typing
import Mettapedia.GSLT.Contracts.ACReplacement

/-!
# A typed ground ACU fragment of the λΠ rule language

A declaration introduces a carrier, a homogeneous binary operator, and
its unit. Terms print injectively into the existing LF syntax. Each
printed term has the declared carrier type, and each selected context
really contains an ordinary one-position Dedukti rule contraction.

The quotient puts ACU equations only at the endpoints of that step.
This fragment does not add ACU conversion to general dependent typing:
it has ground operands and no binders or matching variables.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.GroundACU

open Mettapedia.GSLT.LanguageDef.LF (Term WellScoped)
open Mettapedia.GSLT.LanguageDef.LFTyping (Ctx)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)

open Mettapedia.GSLT.Contracts

structure Declaration where
  carrier : String
  operator : String
  identity : String
  carrier_ne_operator : carrier ≠ operator
  carrier_ne_identity : carrier ≠ identity
  operator_ne_identity : operator ≠ identity

namespace Declaration

variable (d : Declaration)

abbrev Atom := {name : String // name ≠ d.carrier ∧ name ≠ d.operator ∧ name ≠ d.identity}
abbrev Expr := ACUReplacement.Term d.Atom
abbrev GroundRule := ACUReplacement.Rule d.Atom

def carrierType : Term := .con d.carrier

def operationType : Term := .pi d.carrierType (.pi d.carrierType d.carrierType)

def binary (a b : Term) : Term := .app (.app (.con d.operator) a) b

def render : d.Expr → Term
  | .atom name => .con name.val
  | .unit => .con d.identity
  | .op a b => d.binary (render a) (render b)

theorem render_injective : Function.Injective d.render := by
  intro a
  induction a with
  | atom name =>
      intro b eq
      cases b with
      | atom other =>
          exact congrArg ACUReplacement.Term.atom (Subtype.ext (Term.con.inj eq))
      | unit => exact (name.property.2.2 (Term.con.inj eq)).elim
      | op _ _ => cases eq
  | unit =>
      intro b eq
      cases b with
      | atom other => exact (other.property.2.2 (Term.con.inj eq).symm).elim
      | unit => rfl
      | op _ _ => cases eq
  | op a b ihA ihB =>
      intro target eq
      cases target with
      | atom _ => cases eq
      | unit => cases eq
      | op c e =>
          obtain ⟨function, argument⟩ := Term.app.inj eq
          exact congrArg₂ ACUReplacement.Term.op (ihA (Term.app.inj function).2) (ihB argument)

theorem render_closed (a : d.Expr) : Closed (d.render a) := by
  induction a with
  | atom _ | unit => exact .con
  | op _ _ first second => exact .app (.app .con first) second

def renderRule (r : d.GroundRule) : RewriteRule := ⟨d.render r.lhs, d.render r.rhs⟩

/-- The ordinary, directed rewrite declarations. ACU is not put into
this rule list or used to equate a rule's two sides. -/
def theory (rules : List d.GroundRule) : Theory where
  constType name := some (
    if name = d.carrier then .srt .type
    else if name = d.operator then d.operationType
    else d.carrierType)
  body := fun _ => none
  rule := fun r => ∃ ground ∈ rules, d.renderRule ground = r

theorem render_typed (rules : List d.GroundRule) (context : Ctx) (a : d.Expr) :
    LambdaPiModulo (d.theory rules) context (d.render a) d.carrierType := by
  induction a with
  | atom name =>
      exact .con (by simp [theory, name.property.1, name.property.2.1])
  | unit =>
      exact .con (by
        simp [theory, d.carrier_ne_identity.symm, d.operator_ne_identity.symm])
  | op a b ihA ihB =>
      have opTyped : LambdaPiModulo (d.theory rules) context (.con d.operator) d.operationType :=
        .con (by simp [theory, d.carrier_ne_operator.symm])
      have partialTyped :
          LambdaPiModulo (d.theory rules) context (.app (.con d.operator) (d.render a))
            (.pi d.carrierType d.carrierType) :=
        .app opTyped ihA
      exact .app partialTyped ihB

def renderContext (c : ACUReplacement.Context d.Atom) : Context :=
  match c with
  | .hole => .hole
  | .left inner kept =>
      .appFunction (.appArgument (.con d.operator) (renderContext inner)) (d.render kept)
  | .right kept inner =>
      .appArgument (.app (.con d.operator) (d.render kept)) (renderContext inner)

theorem render_plug (c : ACUReplacement.Context d.Atom) (a : d.Expr) :
    (d.renderContext c).plug (d.render a) = d.render (c.plug a) := by
  induction c with
  | hole => rfl
  | left _ _ ih | right _ _ ih =>
      simp [renderContext, Context.plug, ACUReplacement.Context.plug, render, binary, ih]

theorem raw_root {rules : List d.GroundRule} {r : d.GroundRule} (declared : r ∈ rules) :
    RootStep (d.theory rules) (d.render r.lhs) (d.render r.rhs) := by
  have instantiated := RootStep.rule (theory := d.theory rules)
    (rule := d.renderRule r) Term.var ⟨r, declared, rfl⟩
  simpa only [renderRule, (d.render_closed r.lhs).inst, (d.render_closed r.rhs).inst]
    using instantiated

theorem raw_at {rules : List d.GroundRule} {r : d.GroundRule} (declared : r ∈ rules)
    (context : ACUReplacement.Context d.Atom) :
    Step (d.theory rules) (d.render (context.plug r.lhs)) (d.render (context.plug r.rhs)) := by
  rw [← d.render_plug, ← d.render_plug]
  exact .inContext (d.renderContext context) (d.raw_root declared)

/-- The canonical bag enumerator agrees with independently declared
ACU equations around an ordinary LF rule contraction, restricted to
this ground grammar. Both directions use the same one-hole context. -/
theorem canonical_step_iff_context (rules : List d.GroundRule) (a b : d.Expr) :
    ACUReplacement.operands b ∈ ACUReplacement.successors rules (ACUReplacement.operands a) ↔
      ∃ rule ∈ rules, ∃ context : ACUReplacement.Context d.Atom,
        ACUReplacement.Equation a (context.plug rule.lhs) ∧
        Step (d.theory rules) (d.render (context.plug rule.lhs)) (d.render (context.plug rule.rhs)) ∧
        ACUReplacement.Equation (context.plug rule.rhs) b := by
  rw [ACUReplacement.mem_successors_iff, ACUReplacement.reduces_iff_context]
  constructor
  · rintro ⟨rule, declared, context, first, last⟩
    exact ⟨rule, declared, context, first, d.raw_at declared context, last⟩
  · rintro ⟨rule, declared, context, first, _, last⟩
    exact ⟨rule, declared, context, first, last⟩

/-- With the explicit unit excluded from the grammar, the same
enumerator computes the ground AC profile. Its contextual certificate
uses only AC axioms and a unit-free context. -/
theorem canonical_ac_step_iff_context (rules : List d.GroundRule)
    (rulesFree : ∀ rule ∈ rules, ACUReplacement.AC.UnitFree rule.lhs ∧
      ACUReplacement.AC.UnitFree rule.rhs)
    {a b : d.Expr} (aFree : ACUReplacement.AC.UnitFree a) (bFree : ACUReplacement.AC.UnitFree b) :
    ACUReplacement.operands b ∈ ACUReplacement.successors rules (ACUReplacement.operands a) ↔
      ∃ rule ∈ rules, ∃ context : ACUReplacement.Context d.Atom,
        ACUReplacement.AC.UnitFreeContext context ∧
        ACUReplacement.AC.Equation a (context.plug rule.lhs) ∧
        Step (d.theory rules) (d.render (context.plug rule.lhs)) (d.render (context.plug rule.rhs)) ∧
        ACUReplacement.AC.Equation (context.plug rule.rhs) b := by
  rw [ACUReplacement.AC.mem_successors_iff_ac_context rules rulesFree aFree bFree]
  constructor
  · rintro ⟨rule, declared, context, free, first, last⟩
    exact ⟨rule, declared, context, free, first, d.raw_at declared context, last⟩
  · rintro ⟨rule, declared, context, free, first, _, last⟩
    exact ⟨rule, declared, context, free, first, last⟩

end Declaration

namespace Controls

def declaration : Declaration := ⟨"D", "join", "e", by decide, by decide, by decide⟩
private def a : declaration.Expr := .atom ⟨"a", by decide⟩
private def b : declaration.Expr := .atom ⟨"b", by decide⟩
private def c : declaration.Expr := .atom ⟨"c", by decide⟩
private def r : declaration.GroundRule := ⟨.op a b, .unit⟩

theorem typed_replacement_under_acu :
    ACUReplacement.operands c ∈ ACUReplacement.successors [r]
      (ACUReplacement.operands (.op b (.op c a))) ∧
      LambdaPiModulo (declaration.theory [r]) [] (declaration.render c) declaration.carrierType := by
  exact ⟨by decide, declaration.render_typed [r] [] c⟩

theorem unit_is_not_an_idempotence_law :
    ¬ ACUReplacement.Equation (.op a a) a := by
  rw [ACUReplacement.equation_iff_operands]
  decide

end Controls

#print axioms Declaration.render_injective
#print axioms Declaration.render_typed
#print axioms Declaration.raw_at
#print axioms Declaration.canonical_step_iff_context
#print axioms Declaration.canonical_ac_step_iff_context
#print axioms Controls.typed_replacement_under_acu
#print axioms Controls.unit_is_not_an_idempotence_law

end Mettapedia.GSLT.Dedukti.GroundACU
