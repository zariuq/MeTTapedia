import Mettapedia.Machines.ObserverLicence.Table
import Mettapedia.Machines.PortfolioReach.Embedding
import Mathlib.Data.Multiset.AddSub

/-!
# Actual portfolio batches satisfy the unordered observer contract

Increasing a depth bound inserts occurrences without duplicating old ones.
An uncut finite bound fixes the complete occurrence bag. Every lawful batch
of the existing portfolio then satisfies the bag-select relation, including
short complete batches and repeated equal payloads. Ordered selection is
strictly stronger: a shallow witness can precede an earlier deep witness.

The operational publication/existence results are imported from PortfolioReach.
Native classification of quiet regions and source continuation boundaries
remains an adapter obligation; class names alone are not evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ObserverLicence.PortfolioBridge

open Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness

universe u v
variable {S : Type u} {A : Type v}

theorem flatMap_sublist {X Y : Type*} (first second : X → List Y) (rows : List X)
    (inside : ∀ row ∈ rows, (first row).Sublist (second row)) :
    (rows.flatMap first).Sublist (rows.flatMap second) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [List.flatMap_cons]
      exact (inside row List.mem_cons_self).append
        (ih (fun value member => inside value (List.mem_cons_of_mem _ member)))

theorem bounded_sublist (space : Space S A) (small large : Nat) (below : small ≤ large)
    (root : S) : ((bounded space small root).1).Sublist (bounded space large root).1 := by
  induction small generalizing large root with
  | zero =>
      cases expansion : space.expand root with
      | answer value => simp [bounded_answer space expansion]
      | branch children => simp [bounded_zero_branch space expansion]
  | succ small ih =>
      cases large with
      | zero => omega
      | succ large =>
          cases expansion : space.expand root with
          | answer value => simp [bounded_answer space expansion]
          | branch children =>
              simp only [bounded_succ_branch space expansion, List.flatMap_map]
              exact flatMap_sublist _ _ children (fun child _ => ih large (by omega) child)

theorem uncut_stable (space : Space S A) (small large : Nat) (below : small ≤ large)
    (root : S) (uncut : (bounded space small root).2 = false) :
    bounded space large root = bounded space small root := by
  induction small generalizing large root with
  | zero =>
      cases expansion : space.expand root with
      | answer value => simp [bounded_answer space expansion]
      | branch children =>
          have empty : children = [] := by simpa [bounded_zero_branch space expansion] using uncut
          cases large <;> simp [bounded, expansion, empty]
  | succ small ih =>
      cases large with
      | zero => omega
      | succ large =>
          cases expansion : space.expand root with
          | answer value => simp [bounded_answer space expansion]
          | branch children =>
              have each : ∀ child ∈ children, (bounded space small child).2 = false := by
                simpa [bounded_succ_branch space expansion, List.any_map] using uncut
              have same : children.map (bounded space large) = children.map (bounded space small) := by
                apply List.map_congr_left
                intro child member
                exact ih large (by omega) child (each child member)
              simp only [bounded_succ_branch space expansion, same]

theorem uncut_bounds_agree (space : Space S A) (first second : Nat) (root : S)
    (firstDone : (bounded space first root).2 = false)
    (secondDone : (bounded space second root).2 = false) :
    bounded space first root = bounded space second root := by
  rcases le_total first second with below | below
  · exact (uncut_stable space first second below root firstDone).symm
  · exact uncut_stable space second first below root secondDone

theorem any_bound_subbag_of_complete (space : Space S A) (depth complete : Nat) (root : S)
    (uncut : (bounded space complete root).2 = false) :
    ((bounded space depth root).1 : Multiset A) ≤ (bounded space complete root).1 := by
  rcases le_total depth complete with below | below
  · exact (bounded_sublist space depth complete below root).subperm
  · rw [uncut_stable space complete depth below root uncut]

theorem lawful_batch_is_bag_select (space : Space S A) (root : S) (demand complete : Nat)
    (uncut : (bounded space complete root).2 = false) (answers : List A)
    (lawful : BoundedSearchPortfolio.BatchMeaning space root demand answers) :
    Observes (.bag ((bounded space complete root).1 : Multiset A)) (select demand) answers := by
  obtain ⟨depth, suffix, assembled, limited, finishes⟩ := lawful
  have included : (answers : Multiset A) ≤ (bounded space depth root).1 := by
    rw [← assembled, ← Multiset.coe_add]
    exact Multiset.le_add_right _ _
  have contained := included.trans (any_bound_subbag_of_complete space depth complete root uncut)
  have size : answers.length = min demand (bounded space complete root).1.length := by
    rcases finishes with full | ⟨whole, depthDone⟩
    · have count := Multiset.card_le_card contained
      simp only [Multiset.coe_card] at count
      omega
    · have same := congrArg Prod.fst (uncut_bounds_agree space depth complete root depthDone uncut)
      rw [whole] at limited ⊢
      rw [same] at limited ⊢
      omega
  obtain ⟨remaining, all⟩ := Multiset.le_iff_exists_add.mp contained
  obtain ⟨rest, represented⟩ := Quot.exists_rep remaining
  change (rest : Multiset A) = remaining at represented
  apply (bag_select_iff _ demand answers).mpr
  refine ⟨rest, ?_, size⟩
  rw [← Multiset.coe_add, represented]
  exact all.symm

theorem published_batch_is_bag_select (space : Space S A) (root : S) (demand complete : Nat)
    (uncut : (bounded space complete root).2 = false) (E : Type)
    (schedule : List BoundedSearchPortfolio.Origin)
    (portfolio : BoundedSearchPortfolio.Portfolio
      {iteration : BoundedSearchPortfolio.Iteration S A // iteration.Valid space root demand} A E)
    (uncommitted : portfolio.published = none) :
    ∀ origin answers,
      (BoundedSearchPortfolio.execute (BoundedSearchPortfolio.boundedEngine space root demand E)
        (BoundedSearchPortfolio.boundedEngine space root demand E) schedule portfolio).published = some (origin, answers) →
      Observes (.bag ((bounded space complete root).1 : Multiset A)) (select demand) answers := by
  intro origin answers published
  exact lawful_batch_is_bag_select space root demand complete uncut answers
    (BoundedSearchPortfolio.boundedPortfolio_law space root demand E schedule portfolio uncommitted origin answers published)

theorem quiet_region_publication_exists {Store Event : Type} (sys : PortfolioReach.System Store S A Event)
    (store : Store) (root : S) (quiet : PortfolioReach.Quiet sys store root)
    (demand complete : Nat) (uncut : (bounded (sys.space store) complete root).2 = false)
    (log : List Event) :
    ∃ rounds answers,
      PortfolioReach.batch (PortfolioReach.portfolio sys root demand
        (PortfolioReach.rounds (PortfolioReach.doubling 1) rounds) store log) = some answers ∧
      Observes (.bag ((bounded (sys.space store) complete root).1 : Multiset A)) (select demand) answers ∧
      (PortfolioReach.portfolio sys root demand
        (PortfolioReach.rounds (PortfolioReach.doubling 1) rounds) store log).world = ⟨store, log, none⟩ := by
  obtain ⟨rounds, answers, published, lawful, world⟩ := PortfolioReach.portfolio_publishes sys quiet
    demand complete (Or.inr uncut) log
  exact ⟨rounds, answers, published,
    lawful_batch_is_bag_select (sys.space store) root demand complete uncut answers lawful, world⟩

namespace Controls

def depthSensitive : Space Nat Nat where
  expand
    | 0 => .branch [1, 2]
    | 1 => .branch [3]
    | 2 => .answer 9
    | 3 => .answer 7
    | _ => .branch []

theorem a_shallow_witness_is_not_the_declared_first :
    (BoundedSearchPortfolio.run depthSensitive 1 10 1 0).answers = [9] ∧
      (bounded depthSensitive 2 0).1 = [7, 9] ∧
      Observes (.bag (([7, 9] : List Nat) : Multiset Nat)) once (some 9) ∧
      ¬ Observes (.ordered [7, 9]) once (some 9) := by
  refine ⟨by decide, by decide, (bag_once_some _ _).mpr (by simp), ?_⟩
  rw [ordered_once]
  decide

end Controls

end Mettapedia.Machines.ObserverLicence.PortfolioBridge
