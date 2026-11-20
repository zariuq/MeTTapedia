import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreOutcomes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreOpenControls

/-!
# A finite ground instance of transitive closure through the actual disciplines

Rows 0--2 are the edges of a three-edge chain. Rows 3--5 are their paths;
6 and 7 join adjacent paths to an edge, and 8 joins the length-two path
to the final edge. The ground rule instances retain their read conjunctions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStorePathControls

open Mettapedia.Logic.LP
open OneFrame (Terms)
open SetStoreSyntax
open SetStoreOpenControls (c)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms)

def ports : Fin 6 → List ℕ × List ℕ
  | ⟨0, _⟩ => ([0], [3])
  | ⟨1, _⟩ => ([1], [4])
  | ⟨2, _⟩ => ([2], [5])
  | ⟨3, _⟩ => ([3, 1], [6])
  | ⟨4, _⟩ => ([4, 2], [7])
  | ⟨5, _⟩ => ([6, 2], [8])

def ruleAt (i : Fin 6) : Rule (Terms (Term atoms)) :=
  ⟨PUnit.unit, ⟨[], (ports i).1.map c, [], [], (ports i).2.map c⟩, []⟩
def program : Program (Terms (Term atoms)) := Set.range ruleAt

theorem constants_have_no_variables (numbers : List ℕ) : varsIn (numbers.map c) = ∅ := by
  induction numbers with
  | nil => rfl
  | cons n rest ih => simp [varsIn, c, Term.freeVars, ih]

theorem rule_propagates (i : Fin 6) : Propagates (ruleAt i) := by
  refine ⟨rfl, rfl, ⟨?_, rfl⟩, ?_, ?_⟩
  · intro check inside
    cases inside
  · simp only [ruleAt, constants_have_no_variables]
    exact Finset.Subset.refl _
  · simp [ruleAt, varsIn]

theorem program_pure : ∀ rule ∈ program, Propagates rule := by
  rintro rule ⟨i, rfl⟩
  exact rule_propagates i

def matchAt (i : Fin 6) : GroundMatch program where
  rule := ruleAt i
  member := ⟨i, rfl⟩
  propagates := rule_propagates i
  assignment := Subst.id atoms
  groundReads term inside := by
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp inside
    trivial
  checked _ _ inside := by cases inside

def rows (numbers : Finset ℕ) : Finset (Term atoms) := numbers.image c
def seed : Finset (Term atoms) := rows {0, 1, 2}
def paths : Finset (Term atoms) := rows {0, 1, 2, 3, 4, 5, 6, 7, 8}

theorem rows_ground (numbers : Finset ℕ) : GroundRows (rows numbers) := by
  intro term inside
  obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp inside
  trivial

theorem paths_closed : SetStoreClosure.Closed (consequence (P := program)) paths := by
  intro match_ _
  obtain ⟨i, isRule⟩ := match_.member
  change (match_.rule.body.produce.map match_.assignment.applyTerm).toFinset ⊆ paths
  rw [← isRule]
  fin_cases i <;> simp [ruleAt, ports, paths, rows, c, Subst.applyTerm]

theorem paths_reached (timing : SetStore.AskTiming) :
    Relation.ReflTransGen (SetStore.Step timing program) seed paths := by
  have first : SetStore.Step timing program seed (rows {0, 1, 2, 3}) :=
    lift_step timing (rows_ground _) ⟨matchAt 0, by decide +kernel, by decide +kernel, by decide +kernel⟩
  have second : SetStore.Step timing program (rows {0, 1, 2, 3}) (rows {0, 1, 2, 3, 4}) :=
    lift_step timing (rows_ground _) ⟨matchAt 1, by decide +kernel, by decide +kernel, by decide +kernel⟩
  have third : SetStore.Step timing program (rows {0, 1, 2, 3, 4}) (rows {0, 1, 2, 3, 4, 5}) :=
    lift_step timing (rows_ground _) ⟨matchAt 2, by decide +kernel, by decide +kernel, by decide +kernel⟩
  have fourth : SetStore.Step timing program (rows {0, 1, 2, 3, 4, 5}) (rows {0, 1, 2, 3, 4, 5, 6}) :=
    lift_step timing (rows_ground _) ⟨matchAt 3, by decide +kernel, by decide +kernel, by decide +kernel⟩
  have fifth : SetStore.Step timing program (rows {0, 1, 2, 3, 4, 5, 6}) (rows {0, 1, 2, 3, 4, 5, 6, 7}) :=
    lift_step timing (rows_ground _) ⟨matchAt 4, by decide +kernel, by decide +kernel, by decide +kernel⟩
  have sixth : SetStore.Step timing program (rows {0, 1, 2, 3, 4, 5, 6, 7}) paths :=
    lift_step timing (rows_ground _) ⟨matchAt 5, by decide +kernel, by decide +kernel, by decide +kernel⟩
  exact .tail (.tail (.tail (.tail (.tail (.single first) second) third) fourth) fifth) sixth

theorem paths_least : (paths : Set (Term atoms)) = SetStoreClosure.closure (consequence (P := program)) seed :=
  actual_terminal_eq_closure .afterTells program_pure (rows_ground _) (paths_reached .afterTells)
    (closed_ground_terminal program_pure paths (rows_ground _) paths_closed)

theorem all_six_profiles_finish_at_paths (discipline : Discipline) (notUnique : discipline ≠ .unique)
    (timing : SetStore.AskTiming) :
    ∃ after, Relation.ReflTransGen (DisciplinedStep discipline timing program) seed after ∧
      TerminalWith discipline timing program after ∧ after = paths := by
  have covers : ∀ rule ∈ program, rule ∈ List.ofFn ruleAt := by
    rintro rule ⟨i, rfl⟩
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  obtain ⟨after, run, terminal, least, _⟩ := discipline_has_least_outcome (Equiv.refl ℕ)
    discipline timing program_pure (List.ofFn ruleAt) covers paths seed paths_closed (by decide +kernel) (rows_ground _)
    (fun impossible => False.elim (notUnique impossible))
  exact ⟨after, run, terminal, Finset.coe_injective (least.trans paths_least.symm)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStorePathControls
