import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.WellFormedRuns

/-!
# The clauses of well-formedness the run theorems do not use: the weaker hypothesis says more

The headline run theorems (`arrow_runs_forward_of_scoped`, `arrow_answers_of_scoped`,
`arrow_runs_reflected_of_scoped`) ask that each equation be scoped, with its own site and its binder
sites distinct, and that the query be scoped from its site, with distinct sites. The forms stated with
`WellFormed` and `QueryWellFormed` are their corollaries, and they ask more: the patterns clause, and
distinctness of sites across equations and between the query and the program.

A program that breaks both of those clauses (two equations share a site, and a left-hand side applies
an unknown to a constant, outside the pattern class) is not well formed (`not_wellFormed`,
`shared_site`, `lhs_not_pattern`), but satisfies the clauses of the `_of_scoped` forms
(`scoped_clauses`), so the run theorems apply to every run of it (`runs_forward_applies`,
`runs_reflected_applies`): the `_of_scoped` forms say strictly more than the `WellFormed` forms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Controls.UnusedClauses

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting

/-- The trivial discipline, with its type language on the nose. -/
abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩
abbrev N := mettaNodes

def supply : ℕ → MClosed := fun _ => csym "space"
abbrev sp : MClosed → Multiset (Row mkeys [] ()) := fun _ => 0

/-- `(= (f $x) $x)` at site `[250]`. -/
def e1 : SourceLanguage.Equation mkeys [] () MTy := ⟨[250], tuple [sym "f", foD [] [250] 0], .ret (foD [] [250] 0)⟩

/-- `(= (g ($G k)) one)`, also at site `[250]`: `$G` applied to a constant is outside the pattern class. -/
def e2 : SourceLanguage.Equation mkeys [] () MTy :=
  ⟨[250], tuple [sym "g", hoD [] [250] 1 (sym "k")], .ret (sym "one")⟩

def program : SourceLanguage.Program mkeys [] () MTy := ⟨[e1, e2], fun t => .apply t⟩

/-- The query `(g k)`. -/
def query : Comp mkeys [] () MTy := .apply (tuple [sym "g", sym "k"])

theorem not_wellFormed : ¬ WellFormed program := by decide

theorem shared_site : ¬ program.sites.Nodup := by decide

theorem lhs_not_pattern : ¬ IsPattern e2.lhs := by decide

/-- **The clauses the run theorems use hold.** -/
theorem scoped_clauses :
    ∀ e ∈ program.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs := by
  intro e member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨by decide, by decide, trivial⟩
  · exact ⟨by decide, by decide, trivial⟩

theorem query_scoped : query.Scoped [[3]] := by decide

theorem query_distinct : ([3] :: query.sites).Nodup := by decide

/-- **The run theorems apply to every run of this program, which is not well formed.** -/
theorem runs_forward_applies {C : Config mkeys [] () MTy}
    (runs : Runs D program supply (Config.initial sp query) C) :
    ∃ L, ArrowFrontier (D := D) N program C L ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires N program) (Hosting.start N program query) x.2.1 :=
  arrow_runs_forward_of_scoped N (D := D) (P := program) (supply := supply) sp query scoped_clauses
    query_scoped query_distinct trivial runs

/-- **And every run of the translated program is a source run.** -/
theorem runs_reflected_applies {s : HostState MSig}
    (run : Relation.ReflTransGen (Fires N program) (Hosting.start N program query) s) :
    ∃ (C : Config mkeys [] () MTy) (b : Branch mkeys [] () MTy) (a : ℕ),
      Runs D program supply (Config.initial sp query) C ∧ b ∈ C.branches ∧
        Represents N program C.world.scope b s a ∧ ArrowBranch b :=
  arrow_runs_reflected_of_scoped N (D := D) (P := program) (supply := supply) sp query scoped_clauses
    query_scoped query_distinct trivial run

#print axioms not_wellFormed
#print axioms shared_site
#print axioms lhs_not_pattern
#print axioms scoped_clauses
#print axioms runs_forward_applies
#print axioms runs_reflected_applies

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Controls.UnusedClauses
