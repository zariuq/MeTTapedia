import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlDoubleDispatchAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlClosureAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionBindingProperties

/-! Admission follows the actual indexed source instruction compiler.
These families require no supplied plan-completeness certificate.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralFirstOrderProjection GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem literal_dispatch_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (pool : List OCaml.MatchPattern)
    (index reference : Nat) (datum : OCaml.Literal) (row : RewriteRule)
    (formed : compileInstruction? pool reference (.literal datum) = some row) : ruleObligations snapshot index row = [] := by
  simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
  subst row
  exact (literal_rule_ready snapshot terms types index _ reference datum).2

theorem lambda_dispatch_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (pool : List OCaml.MatchPattern)
    (index reference : Nat) (parameter : OCaml.MatchPattern) (body : Nat) (row : RewriteRule)
    (formed : compileInstruction? pool reference (.lambda parameter body) = some row) : ruleObligations snapshot index row = [] := by
  simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
  subst row
  exact (closure_rule_ready snapshot terms types index _ reference).2

theorem application_dispatch_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (pool : List OCaml.MatchPattern)
    (index reference function argument : Nat) (row : RewriteRule)
    (formed : compileInstruction? pool reference (.apply function argument) = some row) : ruleObligations snapshot index row = [] := by
  simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
  subst row
  exact (continuation_rule_ready snapshot terms types index _ "MlKArgument" (Or.inl rfl) reference argument
    (code function) (code_vector function) (code_freeNames function)).2

theorem cons_dispatch_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (pool : List OCaml.MatchPattern)
    (index reference head tail : Nat) (row : RewriteRule)
    (formed : compileInstruction? pool reference (.cons head tail) = some row) : ruleObligations snapshot index row = [] := by
  simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
  subst row
  exact (continuation_rule_ready snapshot terms types index _ "MlKConsTail" (Or.inr (Or.inl rfl)) reference tail
    (code head) (code_vector head) (code_freeNames head)).2

theorem and_dispatch_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (pool : List OCaml.MatchPattern)
    (index reference first second : Nat) (row : RewriteRule)
    (formed : compileInstruction? pool reference (.andThen first second) = some row) : ruleObligations snapshot index row = [] := by
  simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
  subst row
  exact (continuation_rule_ready snapshot terms types index _ "MlKAnd" (Or.inr (Or.inr (Or.inl rfl))) reference first
    (code second) (code_vector second) (code_freeNames second)).2

theorem or_dispatch_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (pool : List OCaml.MatchPattern)
    (index reference first second : Nat) (row : RewriteRule)
    (formed : compileInstruction? pool reference (.orElse first second) = some row) : ruleObligations snapshot index row = [] := by
  simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
  subst row
  exact (continuation_rule_ready snapshot terms types index _ "MlKOr" (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) reference first
    (code second) (code_vector second) (code_freeNames second)).2

theorem branch_dispatch_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (pool : List OCaml.MatchPattern)
    (index reference condition yes no : Nat) (row : RewriteRule)
    (formed : compileInstruction? pool reference (.branch condition yes no) = some row) : ruleObligations snapshot index row = [] := by
  simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
  subst row
  exact (double_continuation_rule_ready snapshot terms types index _ "MlKBranch" (Or.inl rfl) reference condition
    (code yes) (code no) (code_vector yes) (code_vector no) (code_freeNames yes) (code_freeNames no)).2

theorem let_dispatch_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (pool : List OCaml.MatchPattern)
    (index reference : Nat) (parameter : OCaml.MatchPattern) (argument body : Nat) (row : RewriteRule)
    (formed : compileInstruction? pool reference (.letValue parameter argument body) = some row) : ruleObligations snapshot index row = [] := by
  cases referenced : patternReference? pool parameter with
  | none => simp [compileInstruction?, referenced] at formed
  | some patternCode =>
    simp only [compileInstruction?, referenced, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
    subst row
    exact (double_continuation_rule_ready snapshot terms types index _ "MlKLet" (Or.inr rfl) reference argument
      patternCode (code body) (pattern_reference_vector referenced) (code_vector body)
      (pattern_reference_freeNames referenced) (code_freeNames body)).2

theorem clause_list_closed (pool : List OCaml.MatchPattern) (clauses : List OCaml.Clause) (encoded : Pattern)
    (resolved : clauseList? pool clauses = some encoded) : encoded.freeFvarNames = [] :=
  vector_typed_closed (clauseList?_vector pool clauses encoded resolved)
    (clauseList?_typed baseLanguage rfl FreeTypeContext.empty [] pool clauses encoded resolved)

theorem match_dispatch_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (pool : List OCaml.MatchPattern)
    (index reference scrutinee : Nat) (clauses : List OCaml.Clause) (row : RewriteRule)
    (formed : compileInstruction? pool reference (.matchValue scrutinee clauses) = some row) : ruleObligations snapshot index row = [] := by
  cases resolved : clauseList? pool clauses with
  | none => simp [compileInstruction?, resolved] at formed
  | some clauseCode =>
    simp only [compileInstruction?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
    subst row
    exact (continuation_rule_ready snapshot terms types index _ "MlKMatch" (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) reference scrutinee
      clauseCode (clauseList?_vector pool clauses clauseCode resolved) (clause_list_closed pool clauses clauseCode resolved)).2

#print axioms literal_dispatch_admitted
#print axioms lambda_dispatch_admitted
#print axioms application_dispatch_admitted
#print axioms cons_dispatch_admitted
#print axioms and_dispatch_admitted
#print axioms or_dispatch_admitted
#print axioms branch_dispatch_admitted
#print axioms let_dispatch_admitted
#print axioms match_dispatch_admitted

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
