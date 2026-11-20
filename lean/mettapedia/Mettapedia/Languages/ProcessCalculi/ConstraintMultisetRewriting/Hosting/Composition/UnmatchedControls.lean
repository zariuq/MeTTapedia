import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Controls

/-!
# The unmatched call beside a row, when the call holds an unknown

`Composition.unmatched_beside_iff` says when the rule of the unmatched call fires beside other rows that
never read as alternatives' rows: exactly when no other row matches the call at a solution
(`NoMatchingRow`), a condition asked at **every** solution of the knowledge. Three controls, for the
program with no equation and the query `(g $x b)`, with `$x` the query's own name:

* `partial_match_stuck`: beside the closed row `eqn((g a b))` the call has **no** firing. The row matches
  the call at the solution `$x := a` (`matches_at_a`) and not at `$x := c` (`no_match_at_c`).
* One row text, `eqn((g a $x))`, with its unknown shared or private:
  `shared_row_fires`: when its `$x` is **the call's own** name, the call has its firing: no solution reads
  `(g a $x)` as `(g $x b)`;
  `private_row_stuck`: when its `$x` is the row's **private** name, the call has no firing.

So a row `eqn($y)` switches a call off when `$y` is the row's private unknown, and not, in general,
when it is the call's.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.UnmatchedControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Controls
open Classical

/-- The frame with no names. -/
abbrev B₀ : Interface.Frames.Frame MSig := ⟨Empty, noNames⟩

/-- The instantiation of the start's names that sends the query's first-order names to `first` and
every private copy to `second`. -/
def close (first second : String) : Assignment (startArity mkeys) B₀.arity
  | .inl x => closeNames [] (csym first) x
  | .inr p => closeNames [] (csym second) p.2

/-- The datum `(g $x b)`, with the query's own name. -/
def gxT : MData := tuple [sym "g", xName, sym "b"]

/-- The datum `(g a $x)`. -/
def gaxT : MData := tuple [sym "g", sym "a", xName]

/-- The datum `(g a b)`. -/
def gabT : MData := tuple [sym "g", sym "a", sym "b"]

/-- The query `(g $x b)`, called. -/
def qgx : Comp mkeys [] () MTy := .apply gxT

theorem qgx_unopened : ∀ t ∈ qgx.data, ∀ x ∈ support t, x.scopes = [] := by decide

theorem label_alt (row : Observation MSig (startArity mkeys)) :
    (startWith N P0 qgx row).label 0 =
      observe (altN N (evalN N (applyN N (instantiate queryNames gxT))) (emptyN N)) := by
  have ne : (0 : ℕ) ≠ P0.equations.length + 1 := by decide
  show Function.update (startLabel N P0 qgx) (P0.equations.length + 1) row 0 = _
  rw [Function.update_of_ne ne]
  rfl

theorem label_row (row : Observation MSig (startArity mkeys)) :
    (startWith N P0 qgx row).label (P0.equations.length + 1) = row := by
  show Function.update (startLabel N P0 qgx) (P0.equations.length + 1) row (P0.equations.length + 1) = _
  rw [Function.update_self]

/-- The alternative's row, read by an instantiation of the start's names. -/
theorem reads_alt {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity)
    (row : Observation MSig (startArity mkeys)) :
    instantiateObservation σ ((startWith N P0 qgx row).label 0) =
      observe (altN N (evalN N (applyN N (instantiate σ (instantiate queryNames gxT))))
        (instantiate σ (emptyN N))) := by
  rw [label_alt]
  show observe (instantiate σ (altN N (evalN N (applyN N (instantiate queryNames gxT))) (emptyN N))) = _
  rw [instantiate_altN, instantiate_evalN, instantiate_applyN]

/-- A row `eqn(t)` never reads as an alternative's row. -/
theorem eqn_row_quiet (t : Term (signature MSig (startArity mkeys)) [] ()) :
    NeverReads (IsAlternative N) (startWith N P0 qgx (observe (eqnN N t))) {P0.equations.length + 1} := by
  intro o inside B σ _ reads
  obtain ⟨x, y, same⟩ := reads
  rw [Finset.mem_singleton.mp inside, label_row] at same
  change observe (instantiate σ (eqnN N t)) = _ at same
  rw [instantiate_eqnN] at same
  exact absurd (N.tag_eq (observe_injective same)) (by decide)

/-- **A row that matches the call at one solution switches the call off**: if some instantiation of the
start's names reads the row `eqn(t)` as `eqn` of its reading of the call, the call has no firing. -/
theorem stuck_of_match (t : Term (signature MSig (startArity mkeys)) [] ())
    (σ : Assignment (startArity mkeys) B₀.arity)
    (matched : instantiate σ t = instantiate σ (instantiate queryNames gxT)) (w' : HostState MSig) :
    ¬ Fires N P0 (startWith N P0 qgx (observe (eqnN N t))) w' := by
  intro fires
  have beside := startWith_beside N (P := P0) qgx (observe (eqnN N t)) qgx_unopened
  have noRow := (unmatched_beside_iff N beside (eqn_row_quiet t) (fun e member => by cases member)
    live_nil).mp ⟨w', fires⟩
  refine noRow (P0.equations.length + 1) (Finset.mem_singleton_self _) B₀ σ
    (fun e member => absurd member List.not_mem_nil) _ _ (reads_alt σ _) ?_
  rw [label_row]
  show observe (instantiate σ (eqnN N t)) = _
  rw [instantiate_eqnN, matched]

/-- The closed row `eqn((g a b))` matches the call at `$x := a`. -/
theorem matches_at_a :
    instantiate (close "a" "a") (instantiate (rowNames 7) gabT) =
      instantiate (close "a" "a") (instantiate queryNames gxT) := rfl

/-- It does not match at `$x := c`: there the call reads `(g c b)`. -/
theorem no_match_at_c :
    instantiate (close "c" "c") (instantiate (rowNames 7) gabT) ≠
      instantiate (close "c" "c") (instantiate queryNames gxT) := by
  intro same
  have args := Args.cons.inj (op_inj same)
  have second : (symAt "a" : Term (signature MSig B₀.arity) [] ()) = symAt "c" := (Args.cons.inj args.2).1
  simp [symAt] at second

/-- **Beside the closed row `eqn((g a b))`, the call `(g $x b)` of the program with no equation has no
firing**: the row matches it at one solution. -/
theorem partial_match_stuck (w' : HostState MSig) :
    ¬ Fires N P0 (startWith N P0 qgx (observe (eqnN N (instantiate (rowNames 7) gabT)))) w' :=
  stuck_of_match _ (close "a" "a") matches_at_a w'

/-- **The row `eqn((g a $x))` with a private unknown switches the call off**: at `$x := a` for the call
and `$x := b` for the row, the row matches. -/
theorem private_row_stuck (w' : HostState MSig) :
    ¬ Fires N P0 (startWith N P0 qgx (observe (eqnN N (instantiate (rowNames 7) gaxT)))) w' :=
  stuck_of_match (instantiate (rowNames 7) gaxT) (close "a" "b") rfl w'

/-- **The same row with the call's own unknown does not**: beside the row `eqn((g a $x))`, with `$x`
the query's name, the call `(g $x b)` has its firing. No solution reads `(g a $x)` as `(g $x b)`. -/
theorem shared_row_fires :
    ∃ w', Fires N P0 (startWith N P0 qgx (observe (eqnN N (instantiate queryNames gaxT)))) w' := by
  have beside := startWith_beside N (P := P0) qgx (observe (eqnN N (instantiate queryNames gaxT))) qgx_unopened
  refine (unmatched_beside_iff N beside (eqn_row_quiet _) (fun e member => by cases member) live_nil).mpr ?_
  intro o inside B σ known x y readsA sameRow
  have readsA' : instantiateObservation σ
      ((startWith N P0 qgx (observe (eqnN N (instantiate queryNames gaxT)))).label 0) =
      observe (altN N (evalN N (applyN N x)) y) := readsA
  rw [reads_alt] at readsA'
  obtain ⟨onFocus, _⟩ := vec2_inj (N.args_eq (observe_injective readsA'))
  have onCall := vec1_inj (N.args_eq (vec1_inj (N.args_eq onFocus)))
  rw [Finset.mem_singleton.mp inside, label_row] at sameRow
  change observe (instantiate σ (eqnN N (instantiate queryNames gaxT))) = _ at sameRow
  rw [instantiate_eqnN] at sameRow
  have onRow := vec1_inj (N.args_eq (observe_injective sameRow))
  have same : instantiate σ (instantiate queryNames gaxT) = instantiate σ (instantiate queryNames gxT) :=
    onRow.trans onCall.symm
  rw [read_queryNames, read_queryNames] at same
  have unfolded : tupleAt [symAt "g", symAt "a", instantiate (fun x => σ (.inl x)) xName] =
      tupleAt [symAt "g", instantiate (fun x => σ (.inl x)) xName, symAt "b"] := same
  obtain ⟨_, first, second⟩ := tuple3_inj unfolded
  have clash : (symAt "a" : Term (signature MSig B.arity) [] ()) = symAt "b" := first.trans second
  simp [symAt] at clash

#print axioms stuck_of_match
#print axioms matches_at_a
#print axioms no_match_at_c
#print axioms partial_match_stuck
#print axioms private_row_stuck
#print axioms shared_row_fires

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.UnmatchedControls
