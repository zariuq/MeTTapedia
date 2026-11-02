import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation

/-! Successful preparation retains the actual authored equation and rule
tables. The source positions are those used by the compiler, before algebra
equations and context rules are appended. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL.Syntax

private theorem tables {theory : Maude.Theory} {prepared : Prepared}
    (accepted : prepare theory = .ok prepared) :
    ∃ equations algebra rules,
      theory.equations.zipIdx.mapM (fun (row, index) => equation? theory.signature index row) = some equations ∧
      theory.rules.zipIdx.mapM (fun (row, index) => rewrite? theory.signature index row) = some rules ∧
      prepared.source = theory ∧ prepared.language.equations = equations ++ algebra ∧
      prepared.language.rewrites = rules ++ theory.signature.operators.flatMap congruences ∧
      theory.check = true ∧ prepared.language.validate = [] := by
  cases checked : theory.check with
  | false =>
    simp [prepare, checked] at accepted
    change Except.error _ = Except.ok prepared at accepted
    cases accepted
  | true =>
    cases equations : theory.equations.zipIdx.mapM (fun (row, index) => equation? theory.signature index row) with
    | none => simp [prepare, checked, equations] at accepted
    | some sourceEquations =>
      let generated := theory.signature.operators.zipIdx.flatMap fun (declaration, index) =>
        (algebraRows declaration).map fun (law, row) => (index, law, row)
      cases algebra : generated.zipIdx.mapM (fun (entry, index) =>
          equation? theory.signature (theory.equations.length + index) entry.2.2) with
      | none =>
        simp only [generated] at algebra
        simp [prepare, checked, equations, algebra] at accepted
      | some algebraEquations =>
        simp only [generated] at algebra
        cases rules : theory.rules.zipIdx.mapM (fun (row, index) => rewrite? theory.signature index row) with
        | none => simp [prepare, checked, equations, algebra, rules] at accepted
        | some sourceRules =>
          simp [prepare, checked, equations, algebra, rules] at accepted
          split at accepted
          · rename_i valid
            cases Except.ok.inj accepted
            exact ⟨sourceEquations, algebraEquations, sourceRules, rfl, rfl, rfl, rfl, rfl, rfl, valid⟩
          · change Except.error _ = Except.ok prepared at accepted
            cases accepted

theorem prepare_source {theory : Maude.Theory} {prepared : Prepared}
    (accepted : prepare theory = .ok prepared) : prepared.source = theory := by
  obtain ⟨_, _, _, _, _, source, _, _⟩ := tables accepted
  exact source

theorem prepare_checked {theory : Maude.Theory} {prepared : Prepared}
    (accepted : prepare theory = .ok prepared) : theory.check = true := by
  obtain ⟨_, _, _, _, _, _, _, _, checked, _⟩ := tables accepted
  exact checked

theorem prepare_valid {theory : Maude.Theory} {prepared : Prepared}
    (accepted : prepare theory = .ok prepared) : prepared.language.validate = [] := by
  obtain ⟨_, _, _, _, _, _, _, _, _, valid⟩ := tables accepted
  exact valid

private theorem mapM_member {α β : Type} (f : α → Option β) {source : List α} {target : List β}
    (mapped : source.mapM f = some target) {entry : α} (member : entry ∈ source) :
    ∃ result, f entry = some result ∧ result ∈ target := by
  induction source generalizing target with
  | nil => cases member
  | cons head rest ih =>
      cases first : f head with
      | none => simp [List.mapM_cons, first] at mapped
      | some value =>
        cases remaining : rest.mapM f with
        | none => simp [List.mapM_cons, first, remaining] at mapped
        | some values =>
          have same : value :: values = target := by simpa [List.mapM_cons, first, remaining] using mapped
          subst target
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨value, first, List.mem_cons_self⟩
          · obtain ⟨result, produced, present⟩ := ih remaining member
            exact ⟨result, produced, List.mem_cons_of_mem _ present⟩

theorem authored_equation_member {theory : Maude.Theory} {prepared : Prepared}
    (accepted : prepare theory = .ok prepared) {row : Maude.Row} {index : Nat}
    (source : (row, index) ∈ theory.equations.zipIdx) :
    ∃ equation, equation? theory.signature index row = some equation ∧ equation ∈ prepared.language.equations := by
  obtain ⟨equations, _, _, compiled, _, _, retained, _⟩ := tables accepted
  obtain ⟨equation, produced, member⟩ := mapM_member _ compiled source
  refine ⟨equation, produced, ?_⟩
  rw [retained]
  exact List.mem_append_left _ member

private theorem mapM_layout {α β : Type} (f : α → Option β) {source : List α} {target : List β}
    (mapped : source.mapM f = some target) :
    target.length = source.length ∧ ∀ value ∈ target, ∃ entry ∈ source, f entry = some value := by
  induction source generalizing target with
  | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at mapped
      subst target
      exact ⟨rfl, fun _ member => by cases member⟩
  | cons head rest ih =>
      cases first : f head with
      | none => simp [List.mapM_cons, first] at mapped
      | some value =>
          cases remaining : rest.mapM f with
          | none => simp [List.mapM_cons, first, remaining] at mapped
          | some values =>
              have same : value :: values = target := by simpa [List.mapM_cons, first, remaining] using mapped
              subst target
              obtain ⟨length, inverse⟩ := ih remaining
              refine ⟨by simp only [List.length_cons, length], ?_⟩
              intro result member
              rcases List.mem_cons.mp member with rfl | member
              · exact ⟨head, List.mem_cons_self, first⟩
              · obtain ⟨entry, present, produced⟩ := inverse result member
                exact ⟨entry, List.mem_cons_of_mem _ present, produced⟩

/-- Every row in the authored prefix comes from an actual source equation,
with its original statement index. Algebra-generated rows are outside it. -/
theorem authored_equation_source {theory : Maude.Theory} {prepared : Prepared}
    (accepted : prepare theory = .ok prepared) {equation : Equation}
    (member : equation ∈ prepared.language.equations.take prepared.source.equations.length) :
    ∃ row index, (row, index) ∈ theory.equations.zipIdx ∧
      equation? theory.signature index row = some equation := by
  obtain ⟨equations, algebra, _, compiled, _, sourceExact, retained, _⟩ := tables accepted
  obtain ⟨length, inverse⟩ := mapM_layout _ compiled
  have sourceLength : equations.length = theory.equations.length := by
    simpa only [List.length_zipIdx] using length
  rw [sourceExact, retained, ← sourceLength] at member
  have inEquations : equation ∈ equations := by
    simpa only [List.take_append, List.take_length, Nat.sub_self, List.take_zero, List.append_nil] using member
  obtain ⟨⟨row, index⟩, present, produced⟩ := inverse equation inEquations
  exact ⟨row, index, present, produced⟩

theorem authored_rule_member {theory : Maude.Theory} {prepared : Prepared}
    (accepted : prepare theory = .ok prepared) {row : Maude.Row} {index : Nat}
    (source : (row, index) ∈ theory.rules.zipIdx) :
    ∃ rule, rewrite? theory.signature index row = some rule ∧ rule ∈ prepared.language.rewrites := by
  obtain ⟨_, _, rules, _, compiled, _, _, retained, _, _⟩ := tables accepted
  obtain ⟨rule, produced, member⟩ := mapM_member _ compiled source
  refine ⟨rule, produced, ?_⟩
  rw [retained]
  exact List.mem_append_left _ member

theorem authored_equation_checked {theory : Maude.Theory} {prepared : Prepared}
    (accepted : prepare theory = .ok prepared) {row : Maude.Row} {index : Nat}
    (source : (row, index) ∈ theory.equations.zipIdx) : row.check theory.signature = true := by
  have checked := prepare_checked accepted
  simp only [Maude.Theory.check, Bool.and_eq_true, List.all_eq_true] at checked
  exact checked.1.2 row (List.fst_mem_of_mem_zipIdx source)

theorem authored_rule_checked {theory : Maude.Theory} {prepared : Prepared}
    (accepted : prepare theory = .ok prepared) {row : Maude.Row} {index : Nat}
    (source : (row, index) ∈ theory.rules.zipIdx) : row.check theory.signature = true := by
  have checked := prepare_checked accepted
  simp only [Maude.Theory.check, Bool.and_eq_true, List.all_eq_true] at checked
  exact checked.2 row (List.fst_mem_of_mem_zipIdx source)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
