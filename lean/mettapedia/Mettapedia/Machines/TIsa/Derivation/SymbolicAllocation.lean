import Mettapedia.Machines.TIsa.Derivation.SymbolicSelectionSearch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.FreshNamespaces

/-!
# Opening rules and reserving occurrence identities

Variable namespaces and physical occurrence identities are independent.
Fresh rule variables are placed above the variables visible in the
incoming knowledge and labels. New occurrence identities use a
monotone counter; removing an occurrence does not free its identity
for the next firing. A schedule may reserve disjoint blocks for
several members, without making those occurrences visible to a guard.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicFiring

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax (Program)
open RuleSyntax.OneFrame (Terms ext)
open RuleSyntax.SchematicRows.FreshNamespaces (opening combine source_agrees combine_opening)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (fire)

private abbrev ResourceSelection := Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Selection ℕ

variable {signature : LPSignature}

structure LiveWorld (signature : LPSignature) where
  state : World signature ℕ
  live : List ℕ
  next : ℕ
  visible : live.toFinset = state.present
  distinct : live.Nodup
  allocated : ∀ i ∈ live, i < next

namespace LiveWorld

variable (world : LiveWorld signature)

def initial (state : World signature ℕ) (live : List ℕ)
    (visible : live.toFinset = state.present) (distinct : live.Nodup) : LiveWorld signature where
  state := state
  live := live
  next := state.present.sup id + 1
  visible := visible
  distinct := distinct
  allocated _ inside := Nat.lt_succ_of_le (Finset.le_sup (f := id) (visible ▸ List.mem_toFinset.mpr inside))

theorem below_next {i : ℕ} (live : i ∈ world.state.present) : i < world.next :=
  world.allocated i (List.mem_toFinset.mp (world.visible.symm ▸ live))

def reserve (offset count : ℕ) : List ℕ := List.range' (world.next + offset) count

theorem reserve_length (offset count : ℕ) : (world.reserve offset count).length = count :=
  List.length_range'

theorem reserve_distinct (offset count : ℕ) : (world.reserve offset count).Nodup :=
  List.nodup_range'

theorem mem_reserve {offset count i : ℕ} :
    i ∈ world.reserve offset count ↔ world.next + offset ≤ i ∧ i < world.next + offset + count :=
  List.mem_range'_1

theorem reserve_fresh (offset count : ℕ) :
    Disjoint (world.reserve offset count).toFinset world.state.present := by
  apply Finset.disjoint_left.mpr
  intro i new old
  have lower := (world.mem_reserve.mp (List.mem_toFinset.mp new)).1
  have upper := world.below_next old
  omega

theorem reserve_apart {left leftCount right : ℕ} (separated : left + leftCount ≤ right)
    (rightCount : ℕ) :
    Disjoint (world.reserve left leftCount).toFinset (world.reserve right rightCount).toFinset := by
  apply Finset.disjoint_left.mpr
  intro i inLeft inRight
  have upper := (world.mem_reserve.mp (List.mem_toFinset.mp inLeft)).2
  have lower := (world.mem_reserve.mp (List.mem_toFinset.mp inRight)).1
  omega

/-- Only the completed step becomes visible. The enumeration of surviving
occurrences keeps its order, and the outputs are appended once. -/
def commitDelta (selection : ResourceSelection) (after : World signature ℕ)
    (selectionResult : after.present = fire world.state.present (selection.commit (T := Unit)))
    (allocated : selection.made = world.reserve 0 selection.made.length) :
    LiveWorld signature where
  state := after
  live := (world.live.filter fun i => !selection.taken.contains i) ++ selection.made
  next := world.next + selection.made.length
  visible := by
    rw [selectionResult]
    ext i
    simp only [fire, Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Selection.commit,
      Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset, List.mem_append, List.mem_filter,
      Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem]
    rw [← world.visible, List.mem_toFinset]
  distinct := by
    apply List.nodup_append.mpr
    refine ⟨world.distinct.filter _, ?_, ?_⟩
    · rw [allocated]
      exact world.reserve_distinct _ _
    · intro i kept j made equal
      subst j
      have upper := world.allocated i (List.mem_filter.mp kept).1
      have held : i ∈ world.reserve 0 selection.made.length := allocated ▸ made
      have lower := (world.mem_reserve.mp held).1
      omega
  allocated := by
    intro i present
    rcases List.mem_append.mp present with old | new
    · exact (world.allocated i (List.mem_filter.mp old).1).trans_le (Nat.le_add_right _ _)
    · have held : i ∈ world.reserve 0 selection.made.length := allocated ▸ new
      have bound := (world.mem_reserve.mp held).2
      simpa using bound

def commit {program : Program (Terms (Term signature))}
    (firing : RuleSyntax.Firing ℕ (ext (FirstOrder.action signature)) program world.state.frame)
    (allocated : firing.selection.made = world.reserve 0 firing.selection.made.length) :
    LiveWorld signature :=
  world.commitDelta firing.selection (firing.result (act signature) world.state) rfl allocated

@[simp] theorem commit_next {program : Program (Terms (Term signature))}
    (firing : RuleSyntax.Firing ℕ (ext (FirstOrder.action signature)) program world.state.frame)
    (allocated : firing.selection.made = world.reserve 0 firing.selection.made.length) :
    (world.commit firing allocated).next = world.next + firing.selection.made.length := rfl

def visibleTerms : List (Term signature) :=
  world.state.knowledge.map Prod.fst ++ world.state.knowledge.map Prod.snd ++ world.live.map world.state.label

theorem mentions_mem {term : Term signature} (observed : world.state.Mentions term) :
    term ∈ world.visibleTerms := by
  rcases observed with first | second | ⟨i, live, rfl⟩
  · exact List.mem_append_left _ (List.mem_append_left _ first)
  · exact List.mem_append_left _ (List.mem_append_right _ second)
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_toFinset.mp (world.visible.symm ▸ live), rfl⟩)

variable [DecidableEq signature.vars]

def variableBound (slots : signature.vars ≃ ℕ) : ℕ :=
  (world.visibleTerms.map fun term => term.freeVars.sup slots + 1).foldr max 0

private theorem le_fold_max {i : ℕ} {xs : List ℕ} (inside : i ∈ xs) : i ≤ xs.foldr max 0 := by
  induction xs with
  | nil => cases inside
  | cons head tail ih =>
    rcases List.mem_cons.mp inside with rfl | later
    · exact Nat.le_max_left _ _
    · exact (ih later).trans (Nat.le_max_right _ _)

theorem below_variableBound (slots : signature.vars ≃ ℕ)
    {term : Term signature} (observed : world.state.Mentions term)
    {name : signature.vars} (used : name ∈ term.freeVars) : slots name < world.variableBound slots := by
  have localBound := Finset.le_sup (f := slots) used
  have globalBound : term.freeVars.sup slots + 1 ≤ world.variableBound slots :=
    le_fold_max (List.mem_map.mpr ⟨term, world.mentions_mem observed, rfl⟩)
  exact (Nat.lt_succ_of_le localBound).trans_le globalBound

variable {program : Program (Terms (Term signature))}

def template (slots : signature.vars ≃ ℕ) (rule : RuleSyntax.Rule (Terms (Term signature)))
    (authored : rule ∈ program) (space offset : ℕ) :
    RuleSyntax.Firing ℕ (ext (FirstOrder.action signature)) program world.state.frame :=
  ⟨rule, authored, PUnit.unit, opening slots (world.variableBound slots) space,
    ⟨[], [], world.reserve offset rule.body.produce.length⟩, List.replicate rule.collect.length ∅⟩

theorem template_fresh (slots : signature.vars ≃ ℕ) (rule : RuleSyntax.Rule (Terms (Term signature)))
    (authored : rule ∈ program) (space offset : ℕ) :
    (world.template slots rule authored space offset).Fresh (act signature) world.state := by
  intro frame caller locals
  cases frame
  let bound := world.variableBound slots
  let witness := combine slots bound caller (fun _ => locals)
  refine ⟨witness, ?_, ?_⟩
  · intro term observed
    change witness.applyTerm ((Subst.id signature).applyTerm term) = caller.applyTerm term
    rw [Subst.applyTerm_id]
    exact source_agrees slots bound caller (fun _ => locals) term (fun _ used =>
      world.below_variableBound slots observed used)
  · intro term _
    exact combine_opening slots bound caller (fun _ => locals) space term

def prepare (slots : signature.vars ≃ ℕ) (rule : RuleSyntax.Rule (Terms (Term signature)))
    (authored : rule ∈ program) (space offset : ℕ) :
    PreparedOpening (program := program) world.state where
  template := world.template slots rule authored space offset
  fresh := world.template_fresh slots rule authored space offset
  madeDistinct := world.reserve_distinct _ _
  madeFresh := world.reserve_fresh _ _
  makes := (world.reserve_length _ _).symm
  collects := List.length_replicate.symm

end LiveWorld

end Mettapedia.Machines.TIsa.Derivation.SymbolicFiring
