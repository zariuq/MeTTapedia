import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.State

/-!
# Shared and schematic outputs of a rule

The ordinary rule body makes shared terms. Additional outputs are explicit
schematic closures whose arguments use the rule's frame. Their private code
frames remain separate. This introduces a binder as data; it is not an implicit
generalization of arbitrary unknowns in a matched shared hypothesis.

The scope rule exposes all captured output arguments to the existing freshness
predicate, in addition to the original checks and collect patterns. Its output
vector is a scope view, not an extra set of runtime outputs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows

open Interface (Frames)

universe uO uT uH
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

structure Rule (Tm : Obj → Type uT) where
  basic : RuleSyntax.Rule Tm
  schematic : List (Closure Tm basic.locals)

namespace Rule

def ofShared (rule : RuleSyntax.Rule Tm) : Rule Tm := ⟨rule, []⟩

def scope (rule : Rule Tm) : RuleSyntax.Rule Tm :=
  { rule.basic with body :=
      { rule.basic.body with produce := rule.basic.body.produce ++ rule.schematic.flatMap Closure.args } }

theorem scope_ofShared (rule : RuleSyntax.Rule Tm) : (ofShared rule).scope = rule := by
  cases rule with
  | mk locals body collect =>
    cases body with
    | mk take read tell checks produce =>
      simp [scope, ofShared]
      exact List.append_nil produce

def outputs (X : Frames Tm Hom) (rule : Rule Tm) {a : Obj} (opening : Hom rule.basic.locals a) : List (Row Tm a) :=
  rule.basic.body.produce.map (fun term => Row.shared (X.act opening term)) ++
    rule.schematic.map (fun row => Row.schematic (row.act X opening))

theorem outputs_ofShared (X : Frames Tm Hom) (rule : RuleSyntax.Rule Tm) {a : Obj}
    (opening : Hom rule.locals a) :
    (ofShared rule).outputs X opening = rule.body.produce.map (fun term => Row.shared (X.act opening term)) := by
  simp [outputs, ofShared]

theorem outputs_length (X : Frames Tm Hom) (rule : Rule Tm) {a : Obj} (opening : Hom rule.basic.locals a) :
    (rule.outputs X opening).length = rule.basic.body.produce.length + rule.schematic.length := by
  simp [outputs]

end Rule

#print axioms Rule.scope_ofShared
#print axioms Rule.outputs_ofShared
#print axioms Rule.outputs_length

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows
