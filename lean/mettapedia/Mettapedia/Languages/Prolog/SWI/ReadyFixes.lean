import Mathlib.Data.List.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Protocol obligations for the November 2026 SWI-Prolog fix set

These small models pin the safety or semantic obligation of each ready C branch.
They complement the detailed call-port, supervisor, retract-constraint and
grace-period models in this directory.  They are not a refinement proof of C,
its allocator or its platform atomics.  Each namespace states the source fact
that the corresponding C review must establish.
-/

namespace Mettapedia.Languages.Prolog.SWI.ReadyFixes

/-! ## Cyclic module qualification (`b61d9f7`) -/

namespace MetaQualification

structure St where
  top : Nat
  argumentEnd : Nat
  errorAllocated : Bool := false
  invalidStackAccess : Bool := false
deriving DecidableEq, Repr

/-- Reporting a cyclic qualification may allocate on the local stack.  The
fixed path first exposes every argument cell through `lTop`. -/
def reportCyclic (raiseTop : Bool) (s : St) : St :=
  let top := if raiseTop then s.argumentEnd else s.top
  { s with top, errorAllocated := true,
           invalidStackAccess := decide (top < s.argumentEnd) }

def Safe (s : St) : Prop := s.invalidStackAccess = false

theorem fixed_safe (s : St) : Safe (reportCyclic true s) := by
  simp [Safe, reportCyclic]

theorem old_path_unsafe :
    ¬ Safe (reportCyclic false { top := 0, argumentEnd := 3 }) := by
  simp [Safe, reportCyclic]

theorem fixed_preserves_required_top (s : St) :
    (reportCyclic true s).top = s.argumentEnd := by
  simp [reportCyclic]

end MetaQualification

/-! ## Assertion result ownership (`36f53d5`) -/

namespace AssertionReference

structure Plan where
  referenceBeforePublish : Bool
  usesNewClauseAfterPublish : Bool
  usesWhereNodeAfterUnlock : Bool
  keepsOriginalClause : Bool
deriving DecidableEq, Repr

structure AfterGC where
  newClauseLive : Bool
  whereNodeLive : Bool
  originalClauseLive : Bool
deriving DecidableEq, Repr

/-- Clause GC may run after publication and predicate unlock. -/
def collect (p : Plan) : AfterGC :=
  { newClauseLive := p.referenceBeforePublish
    whereNodeLive := false
    originalClauseLive := p.keepsOriginalClause }

def Safe (p : Plan) : Prop :=
  let g := collect p
  (p.usesNewClauseAfterPublish = true → g.newClauseLive = true) ∧
  (p.usesWhereNodeAfterUnlock = true → g.whereNodeLive = true) ∧
  g.originalClauseLive = true

/-- The patch creates the returned clause reference before publication, keeps
`orig`, and never dereferences the borrowed `where` node after unlock. -/
def fixed : Plan := ⟨true, true, false, true⟩

def noResultReference : Plan := { fixed with referenceBeforePublish := false }
def borrowedWhere : Plan := { fixed with usesWhereNodeAfterUnlock := true }
def noOriginalHold : Plan := { fixed with keepsOriginalClause := false }

theorem fixed_safe : Safe fixed := by simp [Safe, fixed, collect]
theorem missing_result_reference_unsafe : ¬ Safe noResultReference := by
  simp [Safe, noResultReference, fixed, collect]
theorem borrowed_where_unsafe : ¬ Safe borrowedWhere := by
  simp [Safe, borrowedWhere, fixed, collect]
theorem missing_original_hold_unsafe : ¬ Safe noOriginalHold := by
  simp [Safe, noOriginalHold, fixed, collect]

end AssertionReference

/-! ## Concurrent index filling (`18ad39f`) -/

namespace IndexFill

/-- Whether the mutation wins the predicate lock before the filler starts, or
waits until an already started fill is complete. -/
inductive Order where
  | mutationFirst
  | fillFirst
deriving DecidableEq, Repr

/-- Contribution of one newly asserted clause to a freshly built index. -/
def fixedCount : Order → Nat
  | .mutationFirst => 1  -- linked before the scan; the scan inserts it once
  | .fillFirst => 1      -- the scan finishes first; the mutator inserts once

/-- Without the `filling` exclusion, the scan and mutator can both insert. -/
def oldDoubleInsert : Nat := 2

/-- Without the exclusion, an erasure can precede the scan, so neither side
inserts an index entry for the still-relevant historical view. -/
def oldMissedHistoricalEntry : Nat := 0

theorem fixed_exactly_once (o : Order) : fixedCount o = 1 := by
  cases o <;> rfl

theorem old_double_insert_wrong : oldDoubleInsert ≠ 1 := by decide
theorem old_missed_entry_wrong : oldMissedHistoricalEntry ≠ 1 := by decide

inductive Phase where
  | idle
  | scanning
  | done
deriving DecidableEq, Repr

structure FillSt where
  phase : Phase := .idle
  linked : Bool := false
  indexed : Nat := 0
  mutationDone : Bool := false
deriving DecidableEq, Repr

/-- The predicate lock makes the mutation finish before filling starts, or
makes it wait until an already started fill is complete. There is deliberately
no mutation transition from the scanning phase. -/
inductive FillStep : FillSt → FillSt → Prop where
  | mutateBefore (s : FillSt) (hp : s.phase = .idle)
      (hm : s.mutationDone = false) :
      FillStep s { s with linked := true, mutationDone := true }
  | start (s : FillSt) (hp : s.phase = .idle) :
      FillStep s { s with phase := .scanning }
  | scan (s : FillSt) (hp : s.phase = .scanning) :
      FillStep s { s with phase := .done, indexed := if s.linked then 1 else 0 }
  | mutateAfter (s : FillSt) (hp : s.phase = .done)
      (hm : s.mutationDone = false) :
      FillStep s { s with linked := true, indexed := 1, mutationDone := true }

inductive FillReach : FillSt → FillSt → Prop where
  | refl (s : FillSt) : FillReach s s
  | tail {s t u : FillSt} : FillReach s t → FillStep t u → FillReach s u

structure FillInv (s : FillSt) : Prop where
  mutation_linked : s.mutationDone = true → s.linked = true
  done_indexed : s.phase = .done → s.indexed = if s.linked then 1 else 0

theorem fill_initial_inv : FillInv {} := by
  constructor <;> simp

theorem FillInv.step {s t : FillSt} (h : FillInv s) (hst : FillStep s t) : FillInv t := by
  rcases h with ⟨hmut, hdone⟩
  cases hst <;> constructor <;> simp_all

theorem fill_reach_inv {s : FillSt} (h : FillReach {} s) : FillInv s := by
  induction h with
  | refl => exact fill_initial_inv
  | tail hr hs ih => exact ih.step hs

theorem fixed_terminal_exactly_once {s : FillSt} (h : FillReach {} s)
    (hd : s.phase = .done) (hm : s.mutationDone = true) :
    s.linked = true ∧ s.indexed = 1 := by
  have hi := fill_reach_inv h
  have hl := hi.mutation_linked hm
  exact ⟨hl, by simpa [hl] using hi.done_indexed hd⟩

structure Completion where
  entriesVisible : Bool
  invalidVisible : Bool
  fillingVisible : Nat
deriving DecidableEq, Repr

/-- Release completion followed by an acquire observation. -/
def releaseComplete (invalid : Bool) : Completion :=
  { entriesVisible := true, invalidVisible := invalid, fillingVisible := 0 }

theorem acquire_after_completion (invalid : Bool) :
    let s := releaseComplete invalid
    s.entriesVisible = true ∧ s.invalidVisible = invalid ∧ s.fillingVisible = 0 := by
  simp [releaseComplete]

end IndexFill

/-! ## Index and clause publication (`96a0875`, `fb1a108`) -/

namespace Publication

structure St where
  payloadVisible : Bool := false
  stampVisible : Bool := false
  linkVisible : Bool := false
  generationVisible : Bool := false
deriving DecidableEq, Repr

def Safe (s : St) : Prop :=
  (s.linkVisible = true → s.payloadVisible = true) ∧
  (s.generationVisible = true → s.stampVisible = true)

def initializePayload (s : St) : St := { s with payloadVisible := true }
def stamp (s : St) : St := { s with stampVisible := true }

/-- A release publication exposes the initialized node. -/
def releaseLink (s : St) : St :=
  { s with payloadVisible := true, linkVisible := true }

/-- Publishing the global generation with release semantics exposes the birth
and erase stamp written before it. -/
def releaseGeneration (s : St) : St :=
  { s with stampVisible := true, generationVisible := true }

def plainLink (s : St) : St := { s with linkVisible := true }
def plainGeneration (s : St) : St := { s with generationVisible := true }

theorem release_link_safe (s : St) (h : Safe s) : Safe (releaseLink s) := by
  exact ⟨by simp [releaseLink], h.2⟩

theorem release_generation_safe (s : St) (h : Safe s) : Safe (releaseGeneration s) := by
  exact ⟨h.1, by simp [releaseGeneration]⟩

theorem fixed_publication_safe (s : St) :
    Safe (releaseGeneration (stamp (releaseLink (initializePayload s)))) := by
  simp [Safe, releaseGeneration, stamp, releaseLink, initializePayload]

theorem plain_link_can_expose_uninitialized :
    ¬ Safe (plainLink {}) := by simp [Safe, plainLink]

theorem generation_before_stamp_can_expose_wrong_birth :
    ¬ Safe (plainGeneration {}) := by simp [Safe, plainGeneration]

/-! `good_from` is the release/acquire flag for a completed index.  The logical
contract is the same implication.  The x86 assembly branch of `96a0875` must be
checked against the compiler and machine memory models because it is not a C11
acquire load. -/

structure IndexView where
  entriesVisible : Bool
  goodFromVisible : Bool
deriving DecidableEq, Repr

def IndexView.Safe (s : IndexView) : Prop :=
  s.goodFromVisible = true → s.entriesVisible = true

def releaseGoodFrom : IndexView := ⟨true, true⟩
def reorderedGoodFrom : IndexView := ⟨false, true⟩
def x86Path (machineOrdersEntries : Bool) : IndexView :=
  ⟨machineOrdersEntries, true⟩

theorem acquire_good_from_safe : releaseGoodFrom.Safe := by
  simp [IndexView.Safe, releaseGoodFrom]
theorem reordered_good_from_unsafe : ¬ reorderedGoodFrom.Safe := by
  simp [IndexView.Safe, reorderedGoodFrom]

theorem x86_path_safe_of_ordered {machineOrdersEntries : Bool}
    (h : machineOrdersEntries = true) :
    (x86Path machineOrdersEntries).Safe := by
  simp [IndexView.Safe, x86Path, h]

theorem x86_path_unsafe_without_order : ¬ (x86Path false).Safe := by
  simp [IndexView.Safe, x86Path]

end Publication

/-! ## Transaction/snapshot start generation (`ec7d838`) -/

namespace TransactionStart

structure Announcement where
  sampled : Nat
  visible : Nat
  current : Nat
deriving DecidableEq, Repr

def Stable (a : Announcement) : Prop :=
  a.sampled = a.current ∧ a.visible = a.sampled

/-- The loop stores the sample, executes the generation barrier, and accepts it
only when the following global-generation read agrees. -/
def fixed (g : Nat) : Announcement := ⟨g, g, g⟩

def oldBuffered : Announcement := ⟨0, 0, 1⟩
def oldStaleVisible : Announcement := ⟨0, 0, 1⟩

theorem fixed_stable (g : Nat) : Stable (fixed g) := by
  simp [Stable, fixed]

theorem buffered_old_start_unsafe : ¬ Stable oldBuffered := by
  simp [Stable, oldBuffered]

/-- A collector that marks the published start protects every clause visible at
that start, by the defining retention rule. -/
def visibleAt (born erased g : Nat) : Prop := born ≤ g ∧ g < erased

def retainedBy (announced born erased : Nat) : Prop := visibleAt born erased announced

theorem announced_view_retained {g born erased : Nat}
    (h : visibleAt born erased g) : retainedBy g born erased := h

theorem old_start_can_miss_refreshed_view :
    ¬ visibleAt 1 2 oldStaleVisible.visible ∧
      visibleAt 1 2 oldStaleVisible.current := by
  simp [visibleAt, oldStaleVisible]

end TransactionStart

/-! ## Static reload and dirty registration (`0f7a274`) -/

namespace StaticReload

structure St where
  registered : Bool
  lastModified : Nat
  oldestGoal : Nat
deriving DecidableEq, Repr

/-- Reload publishes generation `u`, then under the predicate lock records
`last_modified = u` and registers the definition. -/
def reload (s : St) (u : Nat) : St :=
  { s with registered := true, lastModified := u }

/-- Clause GC repeats this test under the same predicate lock. -/
def mayUnregister (s : St) : Bool :=
  s.registered && decide (s.lastModified < s.oldestGoal)

def unregister (s : St) : St :=
  if mayUnregister s then { s with registered := false } else s

theorem older_goal_keeps_reload_registered (s : St) (u : Nat)
    (h : s.oldestGoal ≤ u) :
    (unregister (reload s u)).registered = true := by
  simp [unregister, mayUnregister, reload, show ¬u < s.oldestGoal by omega]

/-! The old split precheck can decide using the old stamp and unregister after
the reload has completed. -/
def oldInitial : St := ⟨true, 0, 1⟩
def staleDecision : Bool := mayUnregister oldInitial
def oldSplitRace : St :=
  let reloaded := reload oldInitial 2
  if staleDecision then { reloaded with registered := false } else reloaded

theorem stale_precheck_accepts : staleDecision = true := by decide
theorem old_split_race_loses_registration : oldSplitRace.registered = false := by decide
theorem old_split_race_has_older_goal : oldSplitRace.oldestGoal ≤ oldSplitRace.lastModified := by decide

end StaticReload

/-! ## Retract lost-candidate continuation (`64db76f`) -/

namespace RetractContinuation

variable {α : Type} [DecidableEq α]

def after (lost : α) : List α → List α
  | [] => []
  | x :: xs => if x = lost then xs else after lost xs

def candidates (visible accepts : α → Bool) (lost : α) (xs : List α) : List α :=
  (after lost xs).filter fun x => visible x && accepts x

/-- Rewalk a current index.  If it cannot locate the lost clause, continue in
the complete clause list. -/
def resume (visible accepts : α → Bool) (lost : α)
    (currentIndex fullList : List α) : List α :=
  if lost ∈ currentIndex
  then candidates visible accepts lost currentIndex
  else candidates visible accepts lost fullList

theorem fallback_complete (visible accepts : α → Bool) (lost : α)
    (currentIndex fullList : List α) (h : lost ∉ currentIndex) :
    resume visible accepts lost currentIndex fullList =
      candidates visible accepts lost fullList := by
  simp [resume, h]

theorem indexed_complete (visible accepts : α → Bool) (lost : α)
    (currentIndex fullList : List α) (hmem : lost ∈ currentIndex)
    (hcoverage : candidates visible accepts lost currentIndex =
                 candidates visible accepts lost fullList) :
    resume visible accepts lost currentIndex fullList =
      candidates visible accepts lost fullList := by
  simp [resume, hmem, hcoverage]

inductive C where | lost | oldTail | added
deriving DecidableEq, Repr

def visible : C → Bool := fun _ => true
def accepts : C → Bool := fun _ => true

theorem saved_old_cursor_misses_added :
    ([] : List C) ≠ candidates visible accepts .lost [.lost, .added] := by decide

theorem fixed_rewalk_finds_added :
    resume visible accepts .lost [.lost, .added] [.lost, .added] = [.added] := by decide

theorem fallback_finds_added_when_current_index_lacks_lost :
    resume visible accepts .lost [.added] [.lost, .added] = [.added] := by decide

end RetractContinuation

/-! ## Remaining source designs: wrapper ownership, post-unlock access and
split frame generations

These sections specify the obligations for C2, C8.2 and C7a. Their positive
plans are design targets for the C work, rather than claims that stock or the
current integration implements them. -/

namespace WrapperOwnership

structure Plan where
  atomicSlotUpdate : Bool
  retiresReplacedSupervisor : Bool
  drainsClosureLingering : Bool
  ownsEmbeddedClauses : Bool
deriving DecidableEq, Repr

def Safe (p : Plan) : Prop :=
  p.atomicSlotUpdate = true ∧
  p.retiresReplacedSupervisor = true ∧
  p.drainsClosureLingering = true ∧
  p.ownsEmbeddedClauses = true

def requiredDesign : Plan := ⟨true, true, true, true⟩
def plainSwap : Plan := { requiredDesign with atomicSlotUpdate := false }
def leakedReplacement : Plan := { requiredDesign with retiresReplacedSupervisor := false }
def undrainedClosure : Plan := { requiredDesign with drainsClosureLingering := false }
def borrowedClauses : Plan := { requiredDesign with ownsEmbeddedClauses := false }

theorem required_design_safe : Safe requiredDesign := by simp [Safe, requiredDesign]
theorem plain_swap_unsafe : ¬ Safe plainSwap := by
  simp [Safe, plainSwap, requiredDesign]
theorem leaked_replacement_unsafe : ¬ Safe leakedReplacement := by
  simp [Safe, leakedReplacement, requiredDesign]
theorem undrained_closure_unsafe : ¬ Safe undrainedClosure := by
  simp [Safe, undrainedClosure, requiredDesign]
theorem borrowed_clauses_unsafe : ¬ Safe borrowedClauses := by
  simp [Safe, borrowedClauses, requiredDesign]

end WrapperOwnership

namespace PostUnlock

structure Plan where
  holdsClause : Bool
  readsClauseAfterUnlock : Bool
  readsBorrowedNodeAfterUnlock : Bool
deriving DecidableEq, Repr

def Safe (p : Plan) : Prop :=
  (p.readsClauseAfterUnlock = true → p.holdsClause = true) ∧
  p.readsBorrowedNodeAfterUnlock = false

def requiredDesign : Plan := ⟨true, true, false⟩
def unheldClause : Plan := { requiredDesign with holdsClause := false }
def borrowedNode : Plan := { requiredDesign with readsBorrowedNodeAfterUnlock := true }

theorem required_design_safe : Safe requiredDesign := by simp [Safe, requiredDesign]
theorem unheld_clause_unsafe : ¬ Safe unheldClause := by
  simp [Safe, unheldClause, requiredDesign]
theorem borrowed_node_unsafe : ¬ Safe borrowedNode := by
  simp [Safe, borrowedNode, requiredDesign]

end PostUnlock

namespace SplitGeneration

inductive Domain where
  | global
  | transaction
deriving DecidableEq, Repr

structure Gen where
  domain : Domain
  sequence : Nat
deriving DecidableEq, Repr

def Coherent (read old new : Gen) : Prop := read = old ∨ read = new

def atomicOld (old _new : Gen) : Gen := old
def atomicNew (_old new : Gen) : Gen := new
/-- A representative split-field read: the domain half is new and the sequence
half is old. -/
def torn (old new : Gen) : Gen := ⟨new.domain, old.sequence⟩

theorem atomic_old_coherent (old new : Gen) : Coherent (atomicOld old new) old new :=
  Or.inl rfl

theorem atomic_new_coherent (old new : Gen) : Coherent (atomicNew old new) old new :=
  Or.inr rfl

def oldGlobal : Gen := ⟨.global, 7⟩
def newTransaction : Gen := ⟨.transaction, 9⟩

theorem torn_generation_incoherent :
    ¬ Coherent (torn oldGlobal newTransaction) oldGlobal newTransaction := by
  simp [Coherent, torn, oldGlobal, newTransaction]

end SplitGeneration

end Mettapedia.Languages.Prolog.SWI.ReadyFixes
