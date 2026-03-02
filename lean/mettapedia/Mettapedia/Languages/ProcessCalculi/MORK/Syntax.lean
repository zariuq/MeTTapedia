import Mettapedia.Languages.MeTTa.Core.Atom

/-!
# MORK: MM2 Syntax

Minimal Model 2 (MM2) is the execution language of the MORK kernel.
MORK runs a set of prioritised exec rules over a PathMap-backed space of atoms.

## MM2 Grammar (from mork_backend.rs)

```
ExecRule  ::= (exec (priority n name) Pattern Template)
Pattern   ::= (, Atom₁ ... Atomₙ)          -- simultaneous match
Template  ::= (O Sink₁ ... Sinkₙ)          -- output
Sink      ::= (+ Atom)                      -- add atom to space
            | (- Atom)                      -- remove atom from space
```

## Reuse

`Atom` is imported from `Mettapedia.Languages.MeTTa.Core.Atom` — same S-expression type
used throughout MeTTaCore. MORK S-expressions are a subset of MeTTa atoms.

## Connection to MQ-Calculus

An MM2 exec rule fires like a quantum measurement branch:
- Pattern match = the output wire fires (`MQOut i`)
- Sinks apply    = the input collapses to a branch (`MQIn i {P, Q}`)
- Non-determinism (two possible assembled results) = `CommReduction.outcome_zero` / `outcome_one`
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.Core (Atom)

/-! ## MORK-specific Syntax -/

/-- A simultaneous-match pattern `(, a₁ a₂ ... aₙ)`.
    All atoms must be present in the space for the rule to fire. -/
structure Pattern where
  atoms : List Atom
  deriving Repr, DecidableEq

/-- A space-mutation sink.
    `(+ a)` inserts atom `a`; `(- a)` removes atom `a`. -/
inductive Sink where
  | add    : Atom → Sink   -- (+ a)
  | remove : Atom → Sink   -- (- a)
  deriving Repr, DecidableEq

/-- An output template `(O sink₁ sink₂ ... sinkₙ)`:
    a list of sinks applied simultaneously when the pattern fires. -/
structure Template where
  sinks : List Sink
  deriving Repr, DecidableEq

/-- A MORK exec rule with priority, name, pattern, and template. -/
structure ExecRule where
  priority : ℕ
  name     : String
  pat      : Pattern
  tmpl     : Template
  deriving Repr, DecidableEq

/-! ## Smart constructors -/

/-- Build an add-sink atom: `(+ a)`. -/
def mkAdd (a : Atom) : Sink := .add a

/-- Build a remove-sink atom: `(- a)`. -/
def mkRemove (a : Atom) : Sink := .remove a

/-- Build a pattern from a list of atoms. -/
def mkPattern (atoms : List Atom) : Pattern := ⟨atoms⟩

/-- Build a template from a list of sinks. -/
def mkTemplate (sinks : List Sink) : Template := ⟨sinks⟩

/-- Build an exec rule. -/
def mkExecRule (priority : ℕ) (name : String)
    (pat : Pattern) (tmpl : Template) : ExecRule :=
  ⟨priority, name, pat, tmpl⟩

/-! ## Predicates -/

/-- A sink is an add operation. -/
def Sink.isAdd : Sink → Bool
  | .add _    => true
  | .remove _ => false

/-- A sink is a remove operation. -/
def Sink.isRemove : Sink → Bool
  | .add _    => false
  | .remove _ => true

/-- Extract the atom from a sink. -/
def Sink.atom : Sink → Atom
  | .add a    => a
  | .remove a => a

/-- All atoms added by a template (before variable substitution). -/
def Template.addAtoms (t : Template) : List Atom :=
  t.sinks.filterMap fun s => if s.isAdd then some s.atom else none

/-- All atoms removed by a template (before variable substitution). -/
def Template.removeAtoms (t : Template) : List Atom :=
  t.sinks.filterMap fun s => if s.isRemove then some s.atom else none

/-! ## Canary tests -/

section CanaryTests

-- Build a simple exec rule and check fields
def exampleRule : ExecRule :=
  mkExecRule 10 "test-rule"
    (mkPattern [.symbol "metta-query", .var "qid", .symbol "lhs"])
    (mkTemplate [mkAdd (.symbol "metta-result"), mkRemove (.symbol "metta-query")])

example : exampleRule.priority = 10 := rfl
example : exampleRule.name = "test-rule" := rfl
example : exampleRule.pat.atoms.length = 3 := rfl
example : exampleRule.tmpl.sinks.length = 2 := rfl

-- Sink predicates
example : (mkAdd (.symbol "x")).isAdd = true := rfl
example : (mkRemove (.symbol "x")).isAdd = false := rfl
example : (mkRemove (.symbol "x")).isRemove = true := rfl

-- Template atom lists
def tmpl1 : Template := mkTemplate
  [mkAdd (.symbol "a"), mkRemove (.symbol "b"), mkAdd (.symbol "c")]
example : tmpl1.addAtoms = [.symbol "a", .symbol "c"] := rfl
example : tmpl1.removeAtoms = [.symbol "b"] := rfl

end CanaryTests

end Mettapedia.Languages.ProcessCalculi.MORK
