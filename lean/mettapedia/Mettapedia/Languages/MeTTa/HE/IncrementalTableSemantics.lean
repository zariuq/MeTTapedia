import Mettapedia.Languages.MeTTa.HE.SnapshotPreservation
import Mettapedia.Languages.MeTTa.HE.BindingCacheSoundness
import Mettapedia.Languages.MeTTa.HE.VariantQueryCorrectness

/-!
# Incremental Table Semantics

Specifies correctness conditions for **incremental tabling**: accumulating
answers incrementally while consumers read partial results. Bridges CeTTa's
current full-result caching to future XSB-style tabled evaluation.

## Key Results (0 sorry)

- `TableEntry.Sound` — every answer is a genuine query result
- `addAnswer_sound` — adding genuine answers preserves soundness
- `addAnswer_extends` — monotonicity (no retraction)
- `markComplete_sound` — completion preserves soundness
- `exact_is_sound` — exact tables are sound
- `tableEntry_addAtom_invalidates` — revision invalidation
- `tableEntry_variant_rhs_agree` — variant queries share RHS atoms
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## §1: Table entry states -/

/-- Completion state of a table entry. -/
inductive TableStatus where
  | inProgress
  | completed
  deriving DecidableEq, Repr

/-- A table entry: accumulated answers + completion status. -/
structure TableEntry where
  query : Atom
  spaceRevision : Nat
  answers : List (Atom × Bindings)
  status : TableStatus

namespace TableEntry

def init (q : Atom) (rev : Nat) : TableEntry :=
  { query := q, spaceRevision := rev, answers := [], status := .inProgress }

def addAnswer (te : TableEntry) (ans : Atom × Bindings) : TableEntry :=
  match te.status with
  | .inProgress => { te with answers := ans :: te.answers }
  | .completed => te

def markComplete (te : TableEntry) : TableEntry :=
  { te with status := .completed }

theorem addAnswer_query (te : TableEntry) (ans : Atom × Bindings)
    (h : te.status = .inProgress) :
    (te.addAnswer ans).query = te.query := by simp [addAnswer, h]

theorem markComplete_query (te : TableEntry) :
    te.markComplete.query = te.query := rfl

end TableEntry

/-! ## §2: Soundness -/

def isGenuineAnswer (space : Space) (q : Atom) (fuel : Nat)
    (ans : Atom × Bindings) : Prop :=
  ans ∈ queryEquations space q fuel

def TableEntry.Sound (te : TableEntry) (space : Space) (fuel : Nat) : Prop :=
  ∀ ans, ans ∈ te.answers → isGenuineAnswer space te.query fuel ans

theorem TableEntry.init_sound (q : Atom) (rev : Nat) (space : Space) (fuel : Nat) :
    (TableEntry.init q rev).Sound space fuel :=
  fun _ h => by simp [TableEntry.init] at h

theorem TableEntry.addAnswer_sound (te : TableEntry) (space : Space) (fuel : Nat)
    (hpartial : te.status = .inProgress)
    (hsound : te.Sound space fuel)
    (ans : Atom × Bindings) (hgenuine : isGenuineAnswer space te.query fuel ans) :
    (te.addAnswer ans).Sound space fuel := by
  intro a hmem
  have hq := te.addAnswer_query ans hpartial
  rw [TableEntry.Sound, hq] at *
  simp [TableEntry.addAnswer, hpartial] at hmem
  rcases hmem with rfl | hmem
  · exact hgenuine
  · exact hsound a hmem

theorem TableEntry.addAnswer_complete_noop (te : TableEntry)
    (hcomplete : te.status = .completed) (ans : Atom × Bindings) :
    te.addAnswer ans = te := by simp [TableEntry.addAnswer, hcomplete]

theorem TableEntry.markComplete_sound (te : TableEntry) (space : Space) (fuel : Nat)
    (hsound : te.Sound space fuel) :
    te.markComplete.Sound space fuel := hsound

/-! ## §3: Monotonicity -/

theorem TableEntry.addAnswer_extends (te : TableEntry) (ans : Atom × Bindings)
    (hpartial : te.status = .inProgress) :
    ∀ a, a ∈ te.answers → a ∈ (te.addAnswer ans).answers := by
  intro a ha; simp [TableEntry.addAnswer, hpartial]; exact Or.inr ha

theorem TableEntry.addAnswer_mem_new (te : TableEntry) (ans : Atom × Bindings)
    (hpartial : te.status = .inProgress) :
    ans ∈ (te.addAnswer ans).answers := by
  simp [TableEntry.addAnswer, hpartial]

theorem TableEntry.markComplete_answers (te : TableEntry) :
    te.markComplete.answers = te.answers := rfl

/-! ## §4: Completeness -/

def TableEntry.Exact (te : TableEntry) (space : Space) (fuel : Nat) : Prop :=
  te.answers.Perm (queryEquations space te.query fuel)

theorem TableEntry.exact_is_sound (te : TableEntry) (space : Space) (fuel : Nat)
    (hexact : te.Exact space fuel) :
    te.Sound space fuel :=
  fun _ hmem => hexact.mem_iff.mp hmem

def TableEntry.populateExact (rs : RevisionedSpace) (q : Atom) (fuel : Nat) :
    TableEntry :=
  { query := q, spaceRevision := rs.revision,
    answers := queryEquations rs.space q fuel, status := .completed }

theorem TableEntry.populateExact_exact (rs : RevisionedSpace) (q : Atom)
    (fuel : Nat) :
    (TableEntry.populateExact rs q fuel).Exact rs.space fuel :=
  List.Perm.refl _

theorem TableEntry.populateExact_valid (rs : RevisionedSpace) (q : Atom)
    (fuel : Nat) :
    (TableEntry.populateExact rs q fuel).spaceRevision = rs.revision := rfl

/-! ## §5: Revision invalidation -/

theorem tableEntry_addAtom_invalidates (rs : RevisionedSpace) (a : Atom)
    (te : TableEntry) (hvalid : te.spaceRevision = rs.revision) :
    te.spaceRevision ≠ (rs.addAtom a).revision := by
  simp [RevisionedSpace.addAtom] at *; omega

theorem tableEntry_snapshot_permanent (rs : RevisionedSpace) (q : Atom)
    (fuel : Nat) :
    let snap := rs.snapshot
    let te := TableEntry.populateExact ⟨⟨snap.atoms⟩, snap.frozenRevision⟩ q fuel
    te.spaceRevision = snap.frozenRevision := rfl

/-! ## §6: Variant-key compatibility -/

theorem tableEntry_variant_rhs_agree
    (rs : RevisionedSpace) (q₁ q₂ : Atom) (hvar : VariantEquiv q₁ q₂) (fuel : Nat) :
    (TableEntry.populateExact rs q₁ fuel).answers.map Prod.fst =
    (TableEntry.populateExact rs q₂ fuel).answers.map Prod.fst :=
  variant_queries_same_rhs rs.space q₁ q₂ hvar fuel

/-! ## §7: Table store -/

structure TableStore where
  entries : List (Atom × TableEntry)

namespace TableStore

def empty : TableStore := ⟨[]⟩

def lookup (ts : TableStore) (q : Atom) : Option TableEntry :=
  ts.entries.find? (fun (k, _) => k == q) |>.map Prod.snd

def upsert (ts : TableStore) (q : Atom) (te : TableEntry) : TableStore :=
  ⟨(q, te) :: ts.entries.filter (fun (k, _) => !(k == q))⟩

end TableStore

end Mettapedia.Languages.MeTTa.HE
