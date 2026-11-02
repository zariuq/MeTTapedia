import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlValueTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveReturn

/-! Encoded continuations and machine states inhabit the authored runtime
sorts whenever their pattern and clause references resolve. This applies
to all source states, and therefore to every reachable source state.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem patternId_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (index : Nat) :
    HasType language free bound (patternId index) (.base "MlPattern") :=
  nonbare_constructor_typed terms [("digits", .collection .vec (.base "R16Nibble"))] _ (by decide +kernel)
    (.cons (digits_typed language terms free bound index) .nil)

theorem patternReference?_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) {pool : List OCaml.MatchPattern}
    {parameter : OCaml.MatchPattern} {encoded : Pattern} (found : patternReference? pool parameter = some encoded) :
    HasType language free bound encoded (.base "MlPattern") := by
  unfold patternReference? at found
  obtain ⟨index, _, same⟩ := Option.map_eq_some_iff.mp found
  cases same
  exact patternId_typed language terms free bound index

theorem primitive_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (operator : OCaml.Primitive) :
    HasType language free bound (primitive operator) (.base "MlPrimitive") := by
  cases operator <;> exact nonbare_constructor_typed terms [] [] (by decide +kernel) .nil

theorem fault_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (error : OCaml.Fault) :
    HasType language free bound (fault error) (.base "MlFaultData") := by
  cases error <;> exact nonbare_constructor_typed terms [] [] (by decide +kernel) .nil

theorem codes_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (references : List OCaml.Code) :
    HasType language free bound (codes (references.map code)) (.base "MlCodes") := by
  induction references with
  | nil => exact nonbare_constructor_typed terms [] [] (by decide +kernel) .nil
  | cons head tail ih =>
      exact nonbare_constructor_typed terms [("head", .base "MlCode"), ("tail", .base "MlCodes")] _ (by decide +kernel)
        (.cons (code_typed language terms free bound head) (.cons ih .nil))

theorem build_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (kind : OCaml.Build) :
    HasType language free bound (build kind) (.base "MlBuild") := by
  cases kind with
  | tuple => exact nonbare_constructor_typed terms [] [] (by decide +kernel) .nil
  | variant typeId constructor =>
      exact nonbare_constructor_typed terms [("tag", .base "MlTag")] _ (by decide +kernel)
        (.cons (tag_typed language terms free bound typeId constructor) .nil)
  | primitive operator =>
      exact nonbare_constructor_typed terms [("operator", .base "MlPrimitive")] _ (by decide +kernel)
        (.cons (primitive_typed language terms free bound operator) .nil)

theorem clauseList?_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (pool : List OCaml.MatchPattern)
    (clauses : List OCaml.Clause) (encoded : Pattern) (found : clauseList? pool clauses = some encoded) :
    HasType language free bound encoded (.base "MlClauses") := by
  induction clauses generalizing encoded with
  | nil =>
      rw [clauseList?_nil] at found
      cases Option.some.inj found
      exact nonbare_constructor_typed terms [] [] (by decide +kernel) .nil
  | cons first rest ih =>
      rw [clauseList?_cons] at found
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
      obtain ⟨parameter, referenced, later, remaining, rfl⟩ := found
      exact nonbare_constructor_typed terms
        [("pattern", .base "MlPattern"), ("body", .base "MlCode"), ("tail", .base "MlClauses")] _ (by decide +kernel)
        (.cons (patternReference?_typed language terms free bound referenced)
          (.cons (code_typed language terms free bound first.body) (.cons (ih later remaining) .nil)))

theorem frame?_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (pool : List OCaml.MatchPattern)
    (frame : OCaml.Frame) (rest encoded : Pattern)
    (tailTyped : HasType language free bound rest (.base "MlContinuation"))
    (found : frame? pool frame rest = some encoded) :
    HasType language free bound encoded (.base "MlContinuation") := by
  cases frame with
  | argument function captured =>
      cases Option.some.inj found
      exact nonbare_constructor_typed terms
        [("function", .base "MlCode"), ("environment", .base "MlEnvironment"), ("rest", .base "MlContinuation")] _
        (by decide +kernel) (.cons (code_typed language terms free bound function)
          (.cons (environment_typed language terms free bound captured) (.cons tailTyped .nil)))
  | function argument =>
      cases Option.some.inj found
      exact nonbare_constructor_typed terms [("argument", .base "MlValue"), ("rest", .base "MlContinuation")] _
        (by decide +kernel) (.cons (value_typed language terms free bound argument) (.cons tailTyped .nil))
  | letValue parameter body captured =>
      simp only [frame?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
      obtain ⟨patternCode, referenced, rfl⟩ := found
      exact nonbare_constructor_typed terms
        [("pattern", .base "MlPattern"), ("body", .base "MlCode"), ("environment", .base "MlEnvironment"), ("rest", .base "MlContinuation")] _
        (by decide +kernel) (.cons (patternReference?_typed language terms free bound referenced)
          (.cons (code_typed language terms free bound body) (.cons (environment_typed language terms free bound captured)
            (.cons tailTyped .nil))))
  | branch yes no captured =>
      cases Option.some.inj found
      exact nonbare_constructor_typed terms
        [("yes", .base "MlCode"), ("no", .base "MlCode"), ("environment", .base "MlEnvironment"), ("rest", .base "MlContinuation")] _
        (by decide +kernel) (.cons (code_typed language terms free bound yes) (.cons (code_typed language terms free bound no)
          (.cons (environment_typed language terms free bound captured) (.cons tailTyped .nil))))
  | andThen right captured =>
      cases Option.some.inj found
      exact nonbare_constructor_typed terms
        [("right", .base "MlCode"), ("environment", .base "MlEnvironment"), ("rest", .base "MlContinuation")] _
        (by decide +kernel) (.cons (code_typed language terms free bound right)
          (.cons (environment_typed language terms free bound captured) (.cons tailTyped .nil)))
  | orElse right captured =>
      cases Option.some.inj found
      exact nonbare_constructor_typed terms
        [("right", .base "MlCode"), ("environment", .base "MlEnvironment"), ("rest", .base "MlContinuation")] _
        (by decide +kernel) (.cons (code_typed language terms free bound right)
          (.cons (environment_typed language terms free bound captured) (.cons tailTyped .nil)))
  | booleanResult =>
      cases Option.some.inj found
      exact nonbare_constructor_typed terms [("rest", .base "MlContinuation")] _ (by decide +kernel) (.cons tailTyped .nil)
  | consTail head captured =>
      cases Option.some.inj found
      exact nonbare_constructor_typed terms
        [("head", .base "MlCode"), ("environment", .base "MlEnvironment"), ("rest", .base "MlContinuation")] _
        (by decide +kernel) (.cons (code_typed language terms free bound head)
          (.cons (environment_typed language terms free bound captured) (.cons tailTyped .nil)))
  | consHead tail =>
      cases Option.some.inj found
      exact nonbare_constructor_typed terms [("tail", .base "MlValue"), ("rest", .base "MlContinuation")] _
        (by decide +kernel) (.cons (value_typed language terms free bound tail) (.cons tailTyped .nil))
  | gather kind reversed captured suffix =>
      cases Option.some.inj found
      exact nonbare_constructor_typed terms
        [("kind", .base "MlBuild"), ("remaining", .base "MlCodes"), ("environment", .base "MlEnvironment"),
          ("suffix", .base "MlValues"), ("rest", .base "MlContinuation")] _ (by decide +kernel)
        (.cons (build_typed language terms free bound kind) (.cons (codes_typed language terms free bound reversed)
          (.cons (environment_typed language terms free bound captured) (.cons (valueList_typed language terms free bound suffix)
            (.cons tailTyped .nil)))))
  | matchValue clauses captured =>
      simp only [frame?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
      obtain ⟨clauseCode, referenced, rfl⟩ := found
      exact nonbare_constructor_typed terms
        [("clauses", .base "MlClauses"), ("environment", .base "MlEnvironment"), ("rest", .base "MlContinuation")] _
        (by decide +kernel) (.cons (clauseList?_typed language terms free bound pool clauses clauseCode referenced)
          (.cons (environment_typed language terms free bound captured) (.cons tailTyped .nil)))

theorem continuation?_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (pool : List OCaml.MatchPattern)
    (rest : OCaml.Continuation) (encoded : Pattern) (found : continuation? pool rest = some encoded) :
    HasType language free bound encoded (.base "MlContinuation") := by
  induction rest generalizing encoded with
  | nil =>
      cases Option.some.inj found
      exact nonbare_constructor_typed terms [] [] (by decide +kernel) .nil
  | cons frame rest ih =>
      simp only [continuation?, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨tail, resolved, result⟩ := found
      exact frame?_typed language terms free bound pool frame tail encoded (ih tail resolved) result

theorem state?_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (pool : List OCaml.MatchPattern)
    (state : OCaml.MachineState) (encoded : Pattern) (found : state? pool state = some encoded) :
    HasType language free bound encoded (.base "MlConfig") := by
  cases state with
  | evaluate reference captured rest =>
      simp only [state?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
      obtain ⟨tail, resolved, rfl⟩ := found
      exact nonbare_constructor_typed terms
        [("code", .base "MlCode"), ("environment", .base "MlEnvironment"), ("continuation", .base "MlContinuation")] _
        (by decide +kernel) (.cons (code_typed language terms free bound reference)
          (.cons (environment_typed language terms free bound captured) (.cons (continuation?_typed language terms free bound pool rest tail resolved) .nil)))
  | returned actual rest =>
      simp only [state?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
      obtain ⟨tail, resolved, rfl⟩ := found
      exact nonbare_constructor_typed terms [("value", .base "MlValue"), ("continuation", .base "MlContinuation")] _
        (by decide +kernel) (.cons (value_typed language terms free bound actual)
          (.cons (continuation?_typed language terms free bound pool rest tail resolved) .nil))
  | halted result =>
      cases result with
      | ok actual =>
          cases Option.some.inj found
          exact nonbare_constructor_typed terms [("value", .base "MlValue")] _ (by decide +kernel)
            (.cons (value_typed language terms free bound actual) .nil)
      | error error =>
          cases Option.some.inj found
          exact nonbare_constructor_typed terms [("fault", .base "MlFaultData")] _ (by decide +kernel)
            (.cons (fault_typed language terms free bound error) .nil)

#print axioms clauseList?_typed
#print axioms frame?_typed
#print axioms continuation?_typed
#print axioms state?_typed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
