import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveSyntax

/-!
# The `.module` format, as data

A `.module` file imports other module files under aliases and defines one module: a list of
theories and an optional entry `theory T(args)`. A theory has parameters, each naming the theory
its argument must be an instance of, and a body: a theory expression.

A theory expression is a reference to a parameter or a `let`-bound value, an application
`T(args)`, a join `e \/ e`, an extension of a base by declaration blocks, or `let x = e in e`.
Declaration blocks hold the rows of a `LanguageDef` exactly as they are written in
`languageDef!`: sorts, constructors, equations and rewrites. `Exports` lists visible sorts and
may rename one (`Elem => Proc`); `Replacements` replace a constructor while keeping its identity
(`One => Zero . |- "0" : Elem`).

Both readers produce this data: the Lean commands of `ModuleSource.Commands` and the
grammar-driven reader. Elaboration (`ModuleSource.Elaborate`) gives it its meaning.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A qualified theory name: `Monoid`, or `u.CommutativeMonoid` through an import alias. -/
abbrev Path := List String

/-- An exported sort, possibly renamed on export. -/
structure Export where
  sort : String
  renamed : Option String := none
  deriving DecidableEq, Repr

/-- A replaced constructor: the old label and the new constructor. -/
structure Replacement where
  old : String
  rule : GrammarRule
  deriving DecidableEq, Repr

/-- One block of a theory body. -/
inductive Block where
  | types (declarations : List TypeDecl)
  | exports (rows : List Export)
  /-- Constructors, and those of them declared bare (`![bare]`): a declared-bare constructor keeps its bare
  collections where it shares its collection kind with another constructor, which would otherwise keep its label. -/
  | terms (rules : List GrammarRule) (bare : List String := [])
  | replacements (rows : List Replacement)
  | equations (rows : List Equation)
  | rewrites (rows : List RewriteRule)
  | inductives (families : List InductiveSyntax.Family)
  deriving Repr

/-- A theory expression. -/
inductive Expr where
  /-- A parameter or a `let`-bound value. -/
  | ref (name : String)
  /-- `T(args)`: a fresh instance of the theory `T`. -/
  | apply (theory : Path) (args : List Expr)
  /-- `e \/ e`: the join over shared origins. -/
  | join (left right : Expr)
  /-- A base extended by blocks; the base `none` is the empty theory. -/
  | extend (base : Option Expr) (blocks : List Block)
  /-- `let x = e in body`: `x` names one shared value. -/
  | letIn (name : String) (value body : Expr)
  deriving Repr

/-- A parameter: its name and the theory its argument must be an instance of. -/
structure Param where
  name : String
  theory : Path
  deriving DecidableEq, Repr

structure Theory where
  name : String
  params : List Param
  body : Expr
  deriving Repr

/-- An import: the module file and the qualifier its theories are named with. -/
structure Import where
  file : String
  qualifier : String
  deriving DecidableEq, Repr

structure Module where
  imports : List Import
  name : String
  theories : List Theory
  /-- `theory T(args)`: the theory the module elaborates to. -/
  entry : Option (Path × List Expr) := none
  deriving Repr

end Mettapedia.GSLT.LanguageDef.ModuleSource
