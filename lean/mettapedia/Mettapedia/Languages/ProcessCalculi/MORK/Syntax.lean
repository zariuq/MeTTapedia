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
            | (head Atom)                   -- idempotent add (first-wins)
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
    `(+ a)` inserts atom `a`; `(- a)` removes atom `a`;
    `(head a)` inserts atom `a` idempotently (no-op if already present). -/
inductive Sink where
  | add    : Atom → Sink   -- (+ a)
  | remove : Atom → Sink   -- (- a)
  | head   : Atom → Sink   -- (head a) — idempotent add (first-wins)
  deriving Repr, DecidableEq

/-- An output template `(O sink₁ sink₂ ... sinkₙ)`:
    a list of sinks applied simultaneously when the pattern fires. -/
structure Template where
  sinks : List Sink
  deriving Repr, DecidableEq

/-! ## Oracle/resource-side syntax -/

/-- External resources requested by the runtime.

These are resource descriptors at the MORK runtime boundary, not workspace
atoms. They cover the currently active external mechanisms:
- `act name`: external ACT/file-backed data source
- `z3 name`: solver instance / oracle resource
-/
inductive ResourceRequest where
  | act : String → ResourceRequest
  | z3 : String → ResourceRequest
  deriving Repr, DecidableEq

/-- Oracle-side queries supported by the current runtime architecture.

These live on the oracle seam, not the generic source-factor/query seam. -/
inductive OracleQuery where
  | actMatch : String → Atom → OracleQuery
  | z3CheckSat : String → List Atom → OracleQuery
  | z3GetModel : String → List Atom → OracleQuery
  deriving Repr, DecidableEq

/-- Responses returned by an oracle resource.

`model` and `factSet` carry atom payloads that can later be interpreted as a
space for matching; `sat` and `unsat` carry no payload. -/
inductive OracleResponse where
  | sat : OracleResponse
  | unsat : OracleResponse
  | model : List Atom → OracleResponse
  | factSet : List Atom → OracleResponse
  deriving Repr, DecidableEq

/-- Route an oracle query to the underlying resource it needs. -/
def OracleQuery.resourceRequest : OracleQuery → ResourceRequest
  | .actMatch name _ => .act name
  | .z3CheckSat name _ => .z3 name
  | .z3GetModel name _ => .z3 name

/-- Extract the atom payload carried by an oracle response. -/
def OracleResponse.payloadAtoms : OracleResponse → List Atom
  | .sat => []
  | .unsat => []
  | .model atoms => atoms
  | .factSet atoms => atoms

/-- Whether an oracle response carries a nonempty payload channel. -/
def OracleResponse.hasPayload : OracleResponse → Bool
  | .sat => false
  | .unsat => false
  | .model _ => true
  | .factSet _ => true

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

/-- Build a head-sink atom: `(head a)`. -/
def mkHead (a : Atom) : Sink := .head a

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
  | .head _   => false

/-- A sink is a remove operation. -/
def Sink.isRemove : Sink → Bool
  | .add _    => false
  | .remove _ => true
  | .head _   => false

/-- A sink is a head (idempotent add) operation. -/
def Sink.isHead : Sink → Bool
  | .add _    => false
  | .remove _ => false
  | .head _   => true

/-- Extract the atom from a sink. -/
def Sink.atom : Sink → Atom
  | .add a    => a
  | .remove a => a
  | .head a   => a

/-- All atoms added by a template (before variable substitution). -/
def Template.addAtoms (t : Template) : List Atom :=
  t.sinks.filterMap fun s => if s.isAdd then some s.atom else none

/-- All atoms removed by a template (before variable substitution). -/
def Template.removeAtoms (t : Template) : List Atom :=
  t.sinks.filterMap fun s => if s.isRemove then some s.atom else none

/-! ## Source-side input specification -/

/-- A source factor specifies WHERE a pattern atom is matched.
    In compat mode `(, pat₁ pat₂ ...)`, each atom implicitly uses `btm`.
    In explicit mode `(I (BTM pat₁) (== pat₂ pat₃) ...)`, each factor
    names its source explicitly.

    Current coverage:
    - `btm`: match against the workspace (current space / PathMap trie)
    - `eqConstraint`: `(== pat witness)` — substitute pat, check it exists in space,
      bind witness to the found atom
    - `neqConstraint`: `(!= pat witness)` — substitute pat, REMOVE it from the space,
      match witness against the remaining atoms

    NOT yet formalized: `ACT` (external file), `z3`. -/
inductive SourceFactor where
  /-- `(BTM pat)`: match `pat` against the current workspace. -/
  | btm : Atom → SourceFactor
  /-- `(== pat witness)`: substitute `pat` using current bindings, then check
      if the result exists in the space. If yes, bind `witness` to the found atom.
      This is a lookup/equality constraint. -/
  | eqConstraint : Atom → Atom → SourceFactor
  /-- `(!= pat witness)`: substitute `pat` using current bindings, REMOVE the
      result from the space, then match `witness` against remaining atoms.
      This is an inequality/exclusion constraint. -/
  | neqConstraint : Atom → Atom → SourceFactor
  deriving Repr, DecidableEq

/-- Guards are substitution-level conditions that don't interact with the workspace.
    They filter matched substitutions but never produce new bindings.
    Unlike `SourceFactor`s which query/constrain the space, guards only inspect
    the current substitution and accept or reject it.

    Design rationale (Council directive): keep workspace-facing operations
    (`SourceFactor`) separate from substitution-level conditions (`SourceGuard`). -/
inductive SourceGuard where
  /-- Freshness guard: resolve variable `v` through the substitution,
      then check that the resolved name does not occur free in `applySubst σ pat`.
      Mirrors MeTTaIL's `premiseStepWithEnv (.freshness ...)` semantics. -/
  | freshness : String → Atom → SourceGuard
  deriving Repr, DecidableEq

/-- An input specification is either compat-mode `(, ...)` or
    explicit-source `(I ...)`.

    - `compat`: `Pattern` — all atoms matched against the workspace
    - `explicit`: list of `SourceFactor`s — each factor has its own source -/
inductive InputSpec where
  /-- `(, pat₁ pat₂ ...)` — compat mode, all atoms against workspace. -/
  | compat : Pattern → InputSpec
  /-- `(I src₁ src₂ ...)` — explicit source factors. -/
  | explicit : List SourceFactor → InputSpec
  deriving Repr, DecidableEq

/-- An exec rule with source-aware input. This extends `ExecRule` with
    the ability to specify explicit source factors.

    For backward compatibility, `ExecRule` remains the compat-mode rule type;
    `SourceExecRule` supports both modes. -/
structure SourceExecRule where
  priority : ℕ
  name     : String
  input    : InputSpec
  guards   : List SourceGuard := []
  tmpl     : Template
  deriving Repr, DecidableEq

/-- Convert a compat-mode `ExecRule` to a `SourceExecRule`. -/
def ExecRule.toSourceRule (r : ExecRule) : SourceExecRule :=
  { priority := r.priority, name := r.name, input := .compat r.pat, tmpl := r.tmpl }

/-- Extract the `Pattern` from an `InputSpec` in compat mode (for backward compat). -/
def InputSpec.toPattern? : InputSpec → Option Pattern
  | .compat p => some p
  | .explicit _ => none

/-! ## Fold-level aggregation -/

/-- Fold-level aggregation strategy for assembling sub-results.

    During the fold phase, a query's sub-results are combined into a single
    assembled result. The aggregator determines HOW:

    - `selectAll`: Non-deterministic (any sub-result is a valid outcome).
      This is the current/default behavior modeled by `NaryFoldPicksSubResult`.
    - `selectFirst`: Deterministic: take the first sub-result only (head).
    - `count`: Assembled result = `(.grounded (.int N))` where N = number of sub-results.
    - `sum`: Assembled result = `(.grounded (.int (Σ values)))` where values are
      extracted from sub-results that are `.grounded (.int _)`. -/
inductive FoldAggregator where
  | selectAll   : FoldAggregator
  | selectFirst : FoldAggregator
  | count       : FoldAggregator
  | sum         : FoldAggregator
  deriving Repr, DecidableEq

/-- Extract an integer from a grounded atom, if present. -/
def extractInt : Atom → Option Int
  | .grounded (.int n) => some n
  | _ => none

/-- Apply a fold aggregator to a list of sub-results, producing the assembled atom.
    Returns `none` if the sub-results list is empty (no valid aggregation). -/
def applyAggregator (agg : FoldAggregator) (subResults : List Atom) : Option Atom :=
  match agg with
  | .selectAll   => subResults.head?
  | .selectFirst => subResults.head?
  | .count       => some (.grounded (.int subResults.length))
  | .sum         =>
    let vals := subResults.filterMap extractInt
    some (.grounded (.int (vals.foldl (· + ·) 0)))

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
