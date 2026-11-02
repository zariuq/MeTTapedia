import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInstructionInstantiation

/-! Source-machine transitions at the actual instruction compiler boundary.
The emitted instruction body is instantiated by its runtime environment and
continuation, then compared with the encoded source-machine successor.
Matcher coverage and the intermediate application/service states are separate
parts of the complete operational correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem literal_source_agreement (pool : List OCaml.MatchPattern) (reference : Nat) (datum : OCaml.Literal)
    (captured : OCaml.Environment) (continuation : OCaml.Continuation)
    (encoded : Pattern) (resolved : continuation? pool continuation = some encoded) :
    instructionResult? pool reference (.literal datum) (environment captured) encoded =
      state? pool (.returned (.literal datum) continuation) := by
  rw [literal_instruction]
  simp only [state?, resolved, value, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem lambda_source_agreement (pool : List OCaml.MatchPattern) (reference body : Nat) (pattern : OCaml.MatchPattern)
    (captured : OCaml.Environment) (continuation : OCaml.Continuation)
    (encoded : Pattern) (resolved : continuation? pool continuation = some encoded) :
    instructionResult? pool reference (.lambda pattern body) (environment captured) encoded =
      state? pool (.returned (.closure (.lambda reference) captured) continuation) := by
  rw [lambda_instruction]
  simp only [state?, resolved, value, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem application_source_agreement (pool : List OCaml.MatchPattern)
    (reference function argument : Nat) (captured : OCaml.Environment) (continuation : OCaml.Continuation)
    (encoded : Pattern) (resolved : continuation? pool continuation = some encoded) :
    instructionResult? pool reference (.apply function argument) (environment captured) encoded =
      state? pool (.evaluate argument captured (.argument function captured :: continuation)) := by
  rw [application_instruction]
  simp only [state?, continuation?, resolved, frame?, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem recursive_source_agreement (pool : List OCaml.MatchPattern)
    (reference body : Nat) (definitions : List OCaml.Code) (captured : OCaml.Environment)
    (continuation : OCaml.Continuation) (encoded : Pattern)
    (resolved : continuation? pool continuation = some encoded) :
    instructionResult? pool reference (.letRecursive definitions body) (environment captured) encoded =
      state? pool (.evaluate body (OCaml.recursiveEnvironment reference definitions captured) continuation) := by
  rw [recursive_instruction]
  simp only [state?, resolved, recursive_environment, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem branch_source_agreement (pool : List OCaml.MatchPattern)
    (reference condition yes no : Nat) (captured : OCaml.Environment) (continuation : OCaml.Continuation)
    (encoded : Pattern) (resolved : continuation? pool continuation = some encoded) :
    instructionResult? pool reference (.branch condition yes no) (environment captured) encoded =
      state? pool (.evaluate condition captured (.branch yes no captured :: continuation)) := by
  rw [branch_instruction]
  simp only [state?, continuation?, resolved, frame?, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem and_source_agreement (pool : List OCaml.MatchPattern)
    (reference left right : Nat) (captured : OCaml.Environment) (continuation : OCaml.Continuation)
    (encoded : Pattern) (resolved : continuation? pool continuation = some encoded) :
    instructionResult? pool reference (.andThen left right) (environment captured) encoded =
      state? pool (.evaluate left captured (.andThen right captured :: continuation)) := by
  rw [and_instruction]
  simp only [state?, continuation?, resolved, frame?, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem or_source_agreement (pool : List OCaml.MatchPattern)
    (reference left right : Nat) (captured : OCaml.Environment) (continuation : OCaml.Continuation)
    (encoded : Pattern) (resolved : continuation? pool continuation = some encoded) :
    instructionResult? pool reference (.orElse left right) (environment captured) encoded =
      state? pool (.evaluate left captured (.orElse right captured :: continuation)) := by
  rw [or_instruction]
  simp only [state?, continuation?, resolved, frame?, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem cons_source_agreement (pool : List OCaml.MatchPattern)
    (reference head tail : Nat) (captured : OCaml.Environment) (continuation : OCaml.Continuation)
    (encoded : Pattern) (resolved : continuation? pool continuation = some encoded) :
    instructionResult? pool reference (.cons head tail) (environment captured) encoded =
      state? pool (.evaluate tail captured (.consTail head captured :: continuation)) := by
  rw [cons_instruction]
  simp only [state?, continuation?, resolved, frame?, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem let_source_agreement {pool : List OCaml.MatchPattern}
    (reference argument body : Nat) {pattern : OCaml.MatchPattern} {patternCode : Pattern}
    (found : patternReference? pool pattern = some patternCode)
    (captured : OCaml.Environment) (continuation : OCaml.Continuation)
    (encoded : Pattern) (resolved : continuation? pool continuation = some encoded) :
    instructionResult? pool reference (.letValue pattern argument body) (environment captured) encoded =
      state? pool (.evaluate argument captured (.letValue pattern body captured :: continuation)) := by
  rw [let_instruction _ _ _ found]
  simp only [state?, continuation?, resolved, frame?, found, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem match_source_agreement {pool : List OCaml.MatchPattern}
    (reference scrutinee : Nat) {clauses : List OCaml.Clause} {clauseCode : Pattern}
    (found : clauseList? pool clauses = some clauseCode)
    (captured : OCaml.Environment) (continuation : OCaml.Continuation)
    (encoded : Pattern) (resolved : continuation? pool continuation = some encoded) :
    instructionResult? pool reference (.matchValue scrutinee clauses) (environment captured) encoded =
      state? pool (.evaluate scrutinee captured (.matchValue clauses captured :: continuation)) := by
  rw [match_instruction _ _ found]
  simp only [state?, continuation?, resolved, frame?, found, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

#print axioms application_source_agreement
#print axioms recursive_source_agreement
#print axioms let_source_agreement

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
