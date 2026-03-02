import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Premise Datalog IR

A backend-agnostic intermediate representation for premise-driven semantics.
Languages with premise-driven rules (MeTTa, PeTTa, etc.) express their premise
relations as first-order datalog programs, which can then be compiled to:
- Ascent (Rust datalog, current backend)
- MORK/ZAM (term-rewriting / WAM-style backends, future)

## Design Rationale

`RelationEnv` in `Engine.lean` is `String → List Pattern → List (List Pattern)` —
an opaque Lean function that cannot be compiled to backends. This IR captures the
same semantics as inspectable first-order data.

The key types:
- `PExpr`: expressions (variables, constructors, literals, builtin calls)
- `PGuard`: conditions in rule bodies (equality, deconstruction, negation, joins)
- `PRule`: a single datalog rule `head(...) :- guard₁, guard₂, ...`
- `PremiseProgram`: a complete set of rules + required builtins

## Connection to Engine.lean

`evalPremiseProgram : PremiseProgram → RelationEnv` (in PremiseDatalogEval.lean)
interprets this IR as a RelationEnv. All optimization contracts from
`OptimizationTheorems.lean` / `ZamContracts.lean` apply to the result
since they work on arbitrary RelationEnv.

## LLM Primer
- `PExpr` is NOT `Pattern` from Syntax.lean. PExpr is for the datalog body;
  Pattern is the MeTTaIL term language. `PExpr.literal` embeds a Pattern.
- `PGuard.deconstruct` binds new variables — the bound names appear in the
  guard, not in `PRule.boundVars` (which is computed, not stored).
- Rules are ordered: body guards are evaluated left-to-right (matters for
  variable binding order).
-/

namespace Mettapedia.OSLF.MeTTaIL.PremiseDatalog

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern CollType)

/-! ## Expressions -/

/-- An expression in the premise datalog.

Unlike `Pattern` (which represents MeTTaIL terms), `PExpr` represents
computations within datalog rule bodies. -/
inductive PExpr where
  /-- Reference to a bound variable by name. -/
  | var : String → PExpr
  /-- Constructor application: `ctor "ACons" [head, tail]`. -/
  | ctor : String → List PExpr → PExpr
  /-- Embed a constant Pattern (ground term). -/
  | literal : Pattern → PExpr
  /-- Call a named builtin function: `call "int_add" [lhs, rhs]`. -/
  | call : String → List PExpr → PExpr
  /-- Wildcard — matches anything, binds nothing. -/
  | wild : PExpr
deriving Repr, Inhabited

/-! ## Guards (Rule Body Conditions) -/

/-- A condition/guard in a datalog rule body.

Guards are evaluated left-to-right. Variable-binding guards (deconstruct,
compute, computeMany, relQuery) introduce new variables available to
subsequent guards. -/
inductive PGuard where
  /-- Structural equality: `eq(lhs, rhs)`. -/
  | eq : PExpr → PExpr → PGuard
  /-- Structural inequality: `neq(lhs, rhs)`. -/
  | neq : PExpr → PExpr → PGuard
  /-- Pattern deconstruction with variable binding.
      `deconstruct(expr, "ACons", ["head", "tail"])` succeeds if `expr`
      matches the constructor `ACons` and binds its fields to the given names. -/
  | deconstruct : PExpr → String → List String → PGuard
  /-- Call a builtin function and bind the result.
      `compute("int_add", [lhs, rhs], "result")` calls the builtin and
      binds the output to "result". -/
  | compute : String → List PExpr → String → PGuard
  /-- Call a builtin function that may return multiple outputs.
      `computeMany("queryEq", [space, atom], "rhs")` iterates all returned
      values, binding each to "rhs". -/
  | computeMany : String → List PExpr → String → PGuard
  /-- Negation-as-failure: succeeds when the relation has no matching tuples.
      `notIn("eqnLookup", [sp, src, wild])` — true if no equation maps src. -/
  | notIn : String → List PExpr → PGuard
  /-- Join against another relation.
      `relQuery("eqListContains", [list, src, dst])` — joins with the named
      relation, binding any free variables in the argument list. -/
  | relQuery : String → List PExpr → PGuard
  /-- Collection membership iteration.
      `collIter(expr, collType, "elem")` iterates over elements of a
      collection (Vec/HashBag/HashSet), binding each to "elem". -/
  | collIter : PExpr → CollType → String → PGuard
  /-- Guard that always succeeds — used for unconditional facts. -/
  | trueGuard : PGuard
deriving Repr, Inhabited

/-! ## Rules -/

/-- A single datalog rule defining one clause of a relation.

Multiple rules with the same `headRel` form a union (disjunction).
The body is a conjunction of guards evaluated left-to-right. -/
structure PRule where
  /-- The relation being defined (e.g., "eqnLookup"). -/
  headRel : String
  /-- Output tuple expressions. May reference variables bound in the body. -/
  headArgs : List PExpr
  /-- Conjunction of guards (left-to-right evaluation). -/
  body : List PGuard
  /-- Optional human-readable name for this clause. -/
  clauseName : Option String := none
deriving Repr, Inhabited

/-! ## Builtin Functions -/

/-- A builtin function that the backend must implement natively.

These are the computational primitives that cannot be expressed as pure
datalog (arithmetic, string operations, etc.). Each backend renders them
differently:
- Ascent: inline Rust expressions
- MORK: MM2 term operations
- ZAM: WAM instructions -/
structure BuiltinFn where
  /-- Function name (e.g., "int_add", "string_concat"). -/
  name : String
  /-- Number of input arguments. -/
  arity : Nat
deriving Repr, Inhabited, DecidableEq

/-- Backend-specific implementation hints for a builtin function.
    Kept separate from BuiltinFn so the core IR stays backend-agnostic. -/
structure BackendHint where
  /-- The builtin function name this hint applies to. -/
  builtinName : String
  /-- Backend identifier (e.g., "ascent", "mork", "zam"). -/
  backend : String
  /-- Implementation template (e.g., Rust expression for Ascent,
      MM2 rule name for MORK). Format is backend-specific. -/
  template : String
deriving Repr, Inhabited

/-! ## Relation Declarations -/

/-- Declaration of a relation with its name and parameter type names. -/
structure RelDecl where
  /-- Relation name (e.g., "eqnLookup"). -/
  name : String
  /-- Parameter type names from the LanguageDef (e.g., ["Space", "Atom", "Atom"]).
      Used by backends for type annotations. -/
  paramTypes : List String
  /-- Whether this relation participates in stratified negation.
      If true, a negative counterpart (e.g., "noEqnLookup") may be generated. -/
  hasNegation : Bool := false
deriving Repr, Inhabited

/-! ## Complete Premise Program -/

/-- A complete premise program: datalog rules + required builtins.

This is the backend-agnostic specification of all premise-driven semantics
for a language. Combined with a `LanguageDef` (which provides types, terms,
and rewrite rules), it fully specifies the runtime behavior. -/
structure PremiseProgram where
  /-- Relation declarations with type information. -/
  relations : List RelDecl
  /-- Datalog rules defining the relations. -/
  rules : List PRule
  /-- Builtin functions required by `compute` guards. -/
  builtins : List BuiltinFn
  /-- Backend-specific implementation hints. Kept separate so the core
      IR is backend-agnostic; the Ascent renderer consults these for
      Rust expression templates, MORK for MM2 rule names, etc. -/
  backendHints : List BackendHint := []
  /-- Which relation to use for the fast-path recursive evaluator (if any).
      Some languages (MeTTa) have a core ground-evaluation loop that benefits
      from a trusted runtime primitive rather than pure datalog. -/
  coreGroundEvalRelation : Option String := none
  /-- State constructor name (e.g., "State" for MeTTa).
      Backends use this to generate domain extraction rules. -/
  stateConstructor : Option String := none
deriving Repr, Inhabited

/-! ## Utilities -/

namespace PremiseProgram

/-- All relation names declared in the program. -/
def relationNames (prog : PremiseProgram) : List String :=
  prog.relations.map (·.name)

/-- All rules for a given relation. -/
def rulesFor (prog : PremiseProgram) (rel : String) : List PRule :=
  prog.rules.filter (·.headRel == rel)

/-- All builtin names used in the program. -/
def builtinNames (prog : PremiseProgram) : List String :=
  prog.builtins.map (·.name)

/-- Relations that have negation counterparts. -/
def negatedRelations (prog : PremiseProgram) : List RelDecl :=
  prog.relations.filter (·.hasNegation)

/-- Check that every relation referenced in rules is declared. -/
def wellFormed (prog : PremiseProgram) : Bool :=
  let declaredRels := prog.relationNames
  let referencedRels := prog.rules.map (·.headRel)
  let guardRels := prog.rules.flatMap fun r => r.body.filterMap fun
    | .relQuery rel _ => some rel
    | .notIn rel _ => some rel
    | _ => none
  (referencedRels ++ guardRels).all (· ∈ declaredRels)

/-- Get backend hints for a specific builtin and backend. -/
def hintFor (prog : PremiseProgram) (builtinName backend : String) : Option String :=
  (prog.backendHints.find? fun h => h.builtinName == builtinName && h.backend == backend)
    |>.map (·.template)

/-! ### Stratification

Stratified negation requires that if relation R uses `notIn S`, then S must
be fully computed before R. We check this by building a dependency graph and
verifying no negation edge creates a cycle.

A program is stratified if we can assign each relation a stratum number such that:
- If R has a `relQuery S` guard, then stratum(S) ≤ stratum(R)
- If R has a `notIn S` guard, then stratum(S) < stratum(R)
-/

/-- Relations that a given relation positively depends on (via relQuery). -/
def positiveDeps (prog : PremiseProgram) (rel : String) : List String :=
  (prog.rulesFor rel).flatMap fun r => r.body.filterMap fun
    | .relQuery dep _ => some dep
    | _ => none

/-- Relations that a given relation negatively depends on (via notIn). -/
def negativeDeps (prog : PremiseProgram) (rel : String) : List String :=
  (prog.rulesFor rel).flatMap fun r => r.body.filterMap fun
    | .notIn dep _ => some dep
    | _ => none

/-- Compute a stratification by iterative fixed-point.
    Returns `none` if the program is not stratifiable (negation cycle). -/
partial def stratify (prog : PremiseProgram) : Option (List (String × Nat)) :=
  let rels := prog.relationNames
  let init := rels.map (·, 0)
  go rels init (rels.length + 1)
where
  go (rels : List String) (strata : List (String × Nat)) (fuel : Nat) :
      Option (List (String × Nat)) :=
    match fuel with
    | 0 => none  -- did not converge → not stratifiable
    | fuel' + 1 =>
      let strataMap := strata
      let getStratum (r : String) : Nat :=
        (strataMap.find? (·.1 == r)).map (·.2) |>.getD 0
      let newStrata := rels.map fun r =>
        let posMax := (prog.positiveDeps r).foldl (fun acc d => max acc (getStratum d)) 0
        let negMax := (prog.negativeDeps r).foldl (fun acc d => max acc (getStratum d + 1)) 0
        (r, max posMax negMax)
      if newStrata == strata then some strata
      else go rels newStrata fuel'

/-- Check that the program has a valid stratification (no negation cycles). -/
def isStratified (prog : PremiseProgram) : Bool :=
  prog.stratify.isSome

end PremiseProgram

/-! ## Free Variables -/

/-- Collect free variable names from a PExpr. -/
partial def PExpr.freeVars : PExpr → List String
  | .var x => [x]
  | .ctor _ args => args.flatMap PExpr.freeVars
  | .literal _ => []
  | .call _ args => args.flatMap PExpr.freeVars
  | .wild => []

/-- Variables bound by a guard. -/
def PGuard.bindsVars : PGuard → List String
  | .deconstruct _ _ names => names.filter (· ≠ "_")
  | .compute _ _ result => [result]
  | .computeMany _ _ result => [result]
  | .collIter _ _ elem => [elem]
  | .relQuery _ args => args.flatMap fun
    | .var x => [x]  -- variables in relQuery args get bound if not already
    | _ => []
  | _ => []

end Mettapedia.OSLF.MeTTaIL.PremiseDatalog
