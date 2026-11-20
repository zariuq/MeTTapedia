import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.OpenRow

/-!
# A value that still holds a variable

A condition "does this value still hold a variable" asks about the store as it is now. On the step it is:
**the knowledge does not determine the term** (`Undetermined`: two solutions of the knowledge read it
differently). This module states it and answers three questions about it. Nothing is added to the step.

**Is it kept when a neighbour tells?** No. More knowledge can only determine
(`undetermined_of_more`), and one tell loses it (`lost_by_a_tell`: with no knowledge the unknown `0` is
undetermined, after `0 ≐ 5` it is determined). What every solution satisfies goes the other way: an ask, a
none query or a count that holds at every solution still holds under more knowledge (`entailed_more`). So the
condition is of the kind of none queries (lost by what a neighbour adds), with tells in place of made rows.

**Is it one of the step's conditions?** A firing reads the knowledge in two ways: its information (the
knowledge with the firing's own equations) must be solvable, and its checks and collect patterns must hold at
every solution of the information. `holds_where_determined`: whatever the firing's own equations `T` and
whatever is asked at every solution, if the two hold at a knowledge `K` they hold at `K` with one more
equation that determines the term. So no choice of tells, asks, none checks, counts and collect patterns holds
exactly at the knowledges that leave a term undetermined. (Stated for these two readings of the knowledge;
`Firing.Admits` also asks that the opening be fresh for the terms the state mentions, which is not treated
here.)

**What is it on a store that reads as rows?** Constantly false: at a state that reads as rows
(`Machines.Reads`) every solution reads each present label as the same ground row (`reads_determined`). At a
row that holds an unknown it is true (`openRow_undetermined`), and there the evaluation of a condition on that
row is refused while the point reading fires and tells the unknown (`OpenRow.probe_eval_refused`,
`OpenRow.probe_point_admitted`).

**What this says about a rule that uses it.** On stores that read as rows, the stores of a machine whose rules
make determined rows, a test of "still holds a variable" in this sense never fires. A library test that does
fire on such stores is about variables of the hosted language written as data in ground rows: a function of
the row, and so a computed condition like the others, with an interpretation that answers `open` at some
ground arguments (the hypothesis of `TestRules.primOpen_never_fires` excludes exactly these). On stores with
rows that hold unknowns, the test in this sense is not a table read, not an ask, and not kept by a
neighbour's tell; a rule that uses it needs what a rule that uses the none query needs, an argument that no
neighbour can tell the unknown between the test and the use of its answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.OpenValues

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open Presentation.Schematic (Tm SState A rowSig toTerm applyTerm_toTerm inst mem_vars_var vars_toTerm)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (Reads)

/-- **The knowledge does not determine a term**: two of its solutions read the term differently. -/
def Undetermined (K : EquationStore Tm) (t : Tm) : Prop :=
  ∃ σ τ : Subst rowSig, A.Models σ K ∧ A.Models τ K ∧ σ.applyTerm t ≠ τ.applyTerm t

/-- **More knowledge keeps what every solution satisfies.** -/
theorem entailed_more {K more : EquationStore Tm} {holds : Subst rowSig → Prop}
    (entailed : ∀ σ, A.Models σ K → holds σ) : ∀ σ, A.Models σ (K ++ more) → holds σ :=
  fun σ solved => entailed σ ((A.models_append σ K more).mp solved).1

/-- **More knowledge can only determine**: a term that the stronger knowledge leaves undetermined is left
undetermined by the weaker. -/
theorem undetermined_of_more {K more : EquationStore Tm} {t : Tm} (stillOpen : Undetermined (K ++ more) t) :
    Undetermined K t := by
  obtain ⟨σ, τ, solvedσ, solvedτ, differ⟩ := stillOpen
  exact ⟨σ, τ, ((A.models_append σ K more).mp solvedσ).1, ((A.models_append τ K more).mp solvedτ).1, differ⟩

/-- A knowledge that equates a term with a ground row determines it. -/
theorem determined_of_told {K : EquationStore Tm} (t : Tm) (value : Expr) :
    ¬ Undetermined ((t, toTerm value) :: K) t := by
  rintro ⟨σ, τ, solvedσ, solvedτ, differ⟩
  have atσ : σ.applyTerm t = σ.applyTerm (toTerm value) := solvedσ _ List.mem_cons_self
  have atτ : τ.applyTerm t = τ.applyTerm (toTerm value) := solvedτ _ List.mem_cons_self
  rw [applyTerm_toTerm] at atσ atτ
  exact differ (atσ.trans atτ.symm)

/-- **Lost by one tell**: with no knowledge the unknown `0` is undetermined; after the tell `0 ≐ 5` it is
determined. -/
theorem lost_by_a_tell :
    Undetermined [] (.var 0) ∧ ¬ Undetermined [((.var 0 : Tm), toTerm (.sym 5))] (.var 0) := by
  refine ⟨⟨Subst.id rowSig, fun _ => toTerm (.sym 5), fun _ inside => absurd inside List.not_mem_nil,
    fun _ inside => absurd inside List.not_mem_nil, fun same => ?_⟩, determined_of_told _ _⟩
  have same' : (.var 0 : Tm) = toTerm (.sym 5) := by
    rw [Subst.applyTerm_id] at same
    exact same
  have inside : 0 ∈ (.var 0 : Tm).freeVars := mem_vars_var.mpr rfl
  rw [same'] at inside
  exact vars_toTerm _ _ inside

/-- **No condition of the step's two readings of the knowledge holds exactly where a term is
undetermined.** If the knowledge with a firing's own equations `T` is solvable, and `holds` at every solution
of it, then both are so at the knowledge with one more equation, which determines the term. -/
theorem holds_where_determined {K T : EquationStore Tm} {holds : Subst rowSig → Prop} (t : Tm)
    (solvable : A.Consistent (K ++ T)) (entailed : ∀ σ, A.Models σ (K ++ T) → holds σ) :
    ∃ value : Expr, A.Consistent (((t, toTerm value) :: K) ++ T) ∧
      (∀ σ, A.Models σ (((t, toTerm value) :: K) ++ T) → holds σ) ∧
      ¬ Undetermined ((t, toTerm value) :: K) t := by
  obtain ⟨σ₀, solved⟩ := solvable
  refine ⟨inst (fun _ => .sym 0) (σ₀.applyTerm t), ⟨grounded σ₀, fun e inside => ?_⟩,
    fun σ solvedσ => entailed σ fun e inside => solvedσ e (List.mem_cons_of_mem _ inside),
    determined_of_told _ _⟩
  rcases List.mem_cons.mp inside with rfl | old
  · show (grounded σ₀).applyTerm t = (grounded σ₀).applyTerm (toTerm _)
    rw [applyTerm_toTerm, grounded_applyTerm]
  · exact grounded_models solved e old

/-- **At a state that reads as rows no present row holds a variable**: every solution of the knowledge reads
its label as the same ground row. -/
theorem reads_determined {O : Type} {s : SState O} {rowsOf : O → Expr} (reads : Reads s rowsOf) {o : O}
    (present : o ∈ s.present) : ¬ Undetermined s.knowledge (s.label o) := by
  rintro ⟨σ, τ, solvedσ, solvedτ, differ⟩
  exact differ ((reads.reads σ solvedσ o present).trans (reads.reads τ solvedτ o present).symm)

/-- **At the open row the row's label is undetermined.** -/
theorem openRow_undetermined : Undetermined OpenRow.openRow.knowledge (OpenRow.openRow.label 0) := by
  refine ⟨Subst.id rowSig, OpenRow.allFive, fun _ inside => absurd inside List.not_mem_nil,
    fun _ inside => absurd inside List.not_mem_nil, fun same => ?_⟩
  have same' : (Subst.id rowSig).applyTerm (OpenRow.box (.var 100)) =
      OpenRow.allFive.applyTerm (OpenRow.box (.var 100)) := same
  rw [Subst.applyTerm_id, OpenRow.applyTerm_box] at same'
  have inside : 100 ∈ (OpenRow.box (.var 100)).freeVars := OpenRow.mem_vars_box.mpr (mem_vars_var.mpr rfl)
  rw [same'] at inside
  have ground : 100 ∈ (toTerm (.sym 5) : Tm).freeVars := OpenRow.mem_vars_box.mp inside
  exact vars_toTerm _ _ ground

#print axioms undetermined_of_more
#print axioms lost_by_a_tell
#print axioms holds_where_determined
#print axioms reads_determined
#print axioms openRow_undetermined

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.OpenValues
