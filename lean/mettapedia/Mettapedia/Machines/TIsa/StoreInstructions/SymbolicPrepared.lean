import Mettapedia.Machines.TIsa.StoreInstructions.SymbolicPortCode
import Mettapedia.Machines.TIsa.Derivation.SymbolicSearch

/-!
# A prepared symbolic firing on p1

Preparing a rule chooses its opening and occurrence ports, not
an answer to the equations. The p1 prefix reconstructs the selected
ports and their equations from the current occurrence store.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.SymbolicPrepared

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Derivation (Match)
open Derivation.SymbolicFiring (Rules LiveWorld Attempt act problem)
open SymbolicExecution (Code Frame Work Equations initial enter storeOf)
open SymbolicPortCode (Port extendAll Ready execute_matches)

universe u p
variable {σ : LPSignature.{u,u,p,u}} {rules : Rules σ} {before : LiveWorld σ}

abbrev Prepared := Attempt rules before

abbrev body (a : Prepared (rules := rules) (before := before)) : RuleInstance (Term σ) :=
  a.seed.firing.opened (act σ)

def takes (a : Prepared (rules := rules) (before := before)) : List (Port σ) :=
  (body a).take.zip a.seed.firing.selection.taken

def reads (a : Prepared (rules := rules) (before := before)) : List (Port σ) :=
  (body a).read.zip a.seed.firing.selection.read

def afterTakes (a : Prepared (rules := rules) (before := before)) : Match (Term σ) (Work σ) :=
  extendAll before.state.label .take (takes a) (initial σ)

def entered (a : Prepared (rules := rules) (before := before)) : Match (Term σ) (Work σ) :=
  extendAll before.state.label .read (reads a) (afterTakes a)

def level (a : Prepared (rules := rules) (before := before)) : ℕ := (takes a).length + (reads a).length

theorem taken_ports (a : Prepared (rules := rules) (before := before)) :
    (takes a).map Prod.snd = a.seed.firing.selection.taken := by
  unfold takes
  apply List.map_snd_zip
  change a.seed.firing.selection.taken.length ≤ (a.seed.firing.rule.body.take.map _).length
  rw [List.length_map, a.seed.shaped.2.2.2.1]

theorem read_ports (a : Prepared (rules := rules) (before := before)) :
    (reads a).map Prod.snd = a.seed.firing.selection.read := by
  unfold reads
  apply List.map_snd_zip
  change a.seed.firing.selection.read.length ≤ (a.seed.firing.rule.body.read.map _).length
  rw [List.length_map, a.seed.shaped.2.2.2.2.1]

theorem taken_exact (a : Prepared (rules := rules) (before := before)) :
    (entered a).taken = a.seed.firing.selection.taken := by
  rw [entered, (SymbolicPortCode.extendAll_read before.state.label _ _).2, afterTakes,
    (SymbolicPortCode.extendAll_take before.state.label _ _).1, taken_ports]
  rfl

theorem read_exact (a : Prepared (rules := rules) (before := before)) :
    (entered a).read = a.seed.firing.selection.read := by
  rw [entered, (SymbolicPortCode.extendAll_read before.state.label _ _).1, afterTakes,
    (SymbolicPortCode.extendAll_take before.state.label _ _).2, read_ports]
  rfl

theorem entered_empty_outputs (a : Prepared (rules := rules) (before := before)) :
    (entered a).seen = [] ∧ (entered a).made = [] := by
  obtain ⟨readsSeen, readsMade⟩ := SymbolicPortCode.extendAll_no_outputs before.state.label .read (reads a) (afterTakes a)
  obtain ⟨takesSeen, takesMade⟩ := SymbolicPortCode.extendAll_no_outputs before.state.label .take (takes a) (initial σ)
  exact ⟨readsSeen.trans takesSeen, readsMade.trans takesMade⟩

theorem row_exact (a : Prepared (rules := rules) (before := before)) :
    a.seed.firing.row (act σ) before.state = before.state.label := by
  funext i
  exact Subst.applyTerm_id (before.state.label i)

theorem old_information (a : Prepared (rules := rules) (before := before)) :
    (act σ).applyStore ((RuleSyntax.OneFrame.ext (FirstOrder.action σ)).weaken a.seed.firing.ext)
      before.state.knowledge = before.state.knowledge := by
  unfold Interface.Frames.applyStore
  conv_rhs => rw [← List.map_id before.state.knowledge]
  apply List.map_congr_left
  intro entry _
  cases entry with
  | mk left right =>
    change ((Subst.id σ).applyTerm left, (Subst.id σ).applyTerm right) = (left, right)
    rw [Subst.applyTerm_id, Subst.applyTerm_id]

theorem information (a : Prepared (rules := rules) (before := before)) :
    (entered a).bindings.problem before.state.knowledge ++ (body a).tell = problem a.seed := by
  rw [entered, SymbolicPortCode.extendAll_problem, afterTakes, SymbolicPortCode.extendAll_problem]
  unfold problem RuleSyntax.Firing.information RuleSyntax.Firing.matching
  rw [old_information a, row_exact a]
  simp only [initial, Work.problem, List.reverse_nil, List.append_nil, takes, reads, List.zip, List.map_zipWith,
    List.append_assoc]

private theorem takes_ready (a : Prepared (rules := rules) (before := before)) : Ready before .take (initial σ) (takes a) := by
  apply Ready.takes
  · intro port listed
    have inTakes : port.2 ∈ (takes a).map Prod.snd := List.mem_map.mpr ⟨port, listed, rfl⟩
    rw [taken_ports a] at inTakes
    exact List.mem_toFinset.mp (before.visible.symm ▸ a.seed.enabled.taken_subset (List.mem_toFinset.mpr inTakes))
  · simpa only [initial, List.nil_append, taken_ports] using a.seed.shaped.2.1
  · intro port _
    exact List.not_mem_nil

private theorem reads_ready (a : Prepared (rules := rules) (before := before)) :
    Ready before .read (afterTakes a) (reads a) := by
  have already : (afterTakes a).taken = a.seed.firing.selection.taken := by
    rw [afterTakes, (SymbolicPortCode.extendAll_take before.state.label _ _).1, taken_ports]
    rfl
  have inReads (port : Port σ) (listed : port ∈ reads a) : port.2 ∈ a.seed.firing.selection.read := by
    have member : port.2 ∈ (reads a).map Prod.snd := List.mem_map.mpr ⟨port, listed, rfl⟩
    rwa [read_ports a] at member
  apply Ready.reads
  · intro port listed
    exact List.mem_toFinset.mp (before.visible.symm ▸ a.seed.enabled.kept_subset (List.mem_toFinset.mpr (inReads port listed)))
  · intro port listed consumed
    rw [already] at consumed
    exact Finset.disjoint_left.mp a.seed.enabled.apart (List.mem_toFinset.mpr consumed)
      (List.mem_toFinset.mpr (inReads port listed))

def emitPorts (a : Prepared (rules := rules) (before := before)) (next : Code σ) : Code σ :=
  .seq (.instruction (.transform (.open 0)))
    (SymbolicPortCode.emit before.live .take 0 (takes a)
      (SymbolicPortCode.emit before.live .read (takes a).length (reads a) next))

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

theorem execute_prefix (a : Prepared (rules := rules) (before := before))
    (machine : P1WordExecution.State) (fits : before.live.length < 2 ^ 64) (next : Code σ) :
    ∃ st : Frame σ, st.store = storeOf before ∧ SameFuel (enter machine before) st ∧ st.levels (level a) = entered a ∧
      SymbolicExecution.execute before.state.knowledge (enter machine before) (emitPorts a next) =
        SymbolicExecution.execute before.state.knowledge st next := by
  let opened := (enter machine before).setLevel 0 (initial σ)
  have ranOpen : SymbolicExecution.execute before.state.knowledge (enter machine before)
      (.instruction (.transform (.open 0))) = .continuing opened := rfl
  have initialLevel : opened.levels 0 = initial σ := by simp [opened, StoreInstructions.State.setLevel]
  obtain ⟨taken, storeAtTakes, fuelAtTakes, takeLevel, ranTakes⟩ :=
    execute_matches before.state.knowledge before .take fits
      (SymbolicPortCode.emit before.live .read (takes a).length (reads a) next)
      0 (state := opened) rfl (initialLevel.symm ▸ takes_ready a)
  have atRead : taken.levels (takes a).length = afterTakes a := by
    simpa only [Nat.zero_add, initialLevel, afterTakes] using takeLevel
  obtain ⟨st, storeAtReads, fuelAtReads, readLevel, ranReads⟩ :=
    execute_matches before.state.knowledge before .read fits next (takes a).length
      (state := taken) storeAtTakes (atRead.symm ▸ reads_ready a)
  have freeOpen : SameFuel (enter machine before) opened := ⟨rfl, rfl⟩
  refine ⟨st, storeAtReads.trans storeAtTakes, (freeOpen.trans fuelAtTakes).trans fuelAtReads, ?_, ?_⟩
  · simpa only [level, atRead, entered] using readLevel
  · change (SymbolicExecution.execute before.state.knowledge (enter machine before)
      (.instruction (.transform (.open 0)))).thenContinue (fun entry =>
        SymbolicExecution.execute before.state.knowledge entry
          (SymbolicPortCode.emit before.live .take 0 (takes a)
            (SymbolicPortCode.emit before.live .read (takes a).length (reads a) next))) = _
    rw [ranOpen, Flow.thenContinue, ranTakes, ranReads]

end Mettapedia.Machines.TIsa.StoreInstructions.SymbolicPrepared
