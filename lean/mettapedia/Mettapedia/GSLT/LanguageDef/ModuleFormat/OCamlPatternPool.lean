import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInstructionInstantiation

/-! Pattern references resolve exactly to declared entries. The whole
program pool covers every pattern used by its instructions, including all
first-match clauses in source order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem patternReference?_exists {pool : List OCaml.MatchPattern} {pattern : OCaml.MatchPattern}
    (member : pattern ∈ pool) : ∃ encoded, patternReference? pool pattern = some encoded := by
  obtain ⟨index, found⟩ := OCaml.patternIndex?_complete pattern pool member
  exact ⟨patternId index, by simp only [patternReference?, found, Option.map_some]⟩

theorem patternReference?_none_iff (pool : List OCaml.MatchPattern) (pattern : OCaml.MatchPattern) :
    patternReference? pool pattern = none ↔ pattern ∉ pool := by
  simp only [patternReference?, Option.map_eq_none_iff, OCaml.patternIndex?_none_iff]

theorem lambda_pattern_member {program : OCaml.Program} {reference : Nat} {pattern : OCaml.MatchPattern} {body : Nat}
    (found : program.instruction? reference = some (.lambda pattern body)) : pattern ∈ patterns program := by
  unfold patterns
  apply List.mem_flatMap.mpr
  refine ⟨.lambda pattern body, ?_, ?_⟩
  · exact List.mem_toArray.mp (Array.mem_of_getElem? found)
  · simp

theorem let_pattern_member {program : OCaml.Program} {reference : Nat} {pattern : OCaml.MatchPattern}
    {argument body : Nat} (found : program.instruction? reference = some (.letValue pattern argument body)) :
    pattern ∈ patterns program := by
  unfold patterns
  apply List.mem_flatMap.mpr
  refine ⟨.letValue pattern argument body, ?_, ?_⟩
  · exact List.mem_toArray.mp (Array.mem_of_getElem? found)
  · simp

theorem clause_pattern_member {program : OCaml.Program} {reference scrutinee : Nat} {clauses : List OCaml.Clause}
    (found : program.instruction? reference = some (.matchValue scrutinee clauses))
    (clause : OCaml.Clause) (member : clause ∈ clauses) : clause.pattern ∈ patterns program := by
  unfold patterns
  apply List.mem_flatMap.mpr
  refine ⟨.matchValue scrutinee clauses, ?_, ?_⟩
  · exact List.mem_toArray.mp (Array.mem_of_getElem? found)
  · exact List.mem_map.mpr ⟨clause, member, rfl⟩

theorem clauseList?_exists {pool : List OCaml.MatchPattern} (clauses : List OCaml.Clause)
    (covered : ∀ clause ∈ clauses, clause.pattern ∈ pool) : ∃ encoded, clauseList? pool clauses = some encoded := by
  induction clauses with
  | nil => exact ⟨_, rfl⟩
  | cons first rest ih =>
    obtain ⟨head, referenced⟩ := patternReference?_exists (covered first List.mem_cons_self)
    obtain ⟨tail, remaining⟩ := ih (fun clause member => covered clause (List.mem_cons_of_mem first member))
    exact ⟨node "MlClauseCons" [head, code first.body, tail], by rw [clauseList?_cons]; simp only [referenced, remaining, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]⟩

theorem program_clauses_resolve {program : OCaml.Program} {reference scrutinee : Nat} {clauses : List OCaml.Clause}
    (found : program.instruction? reference = some (.matchValue scrutinee clauses)) :
    ∃ encoded, clauseList? (patterns program) clauses = some encoded :=
  clauseList?_exists clauses (clause_pattern_member found)

#print axioms lambda_pattern_member
#print axioms program_clauses_resolve

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
