import Mettapedia.Machines.VersionedValidation.Versions
import Mettapedia.Algorithms.Collections.StableKeyEncoding

/-! Ordered occurrences of a space are the source. A declaration catalogue is a
projection, not ownership of the corresponding rows. An import search also reads
its resolution path. The classifications below are parameters of the language. -/
set_option autoImplicit false
namespace Mettapedia.GSLT.Contracts.LiveTheoryProjections

open Mettapedia.Machines
open Mettapedia.Machines.VersionedValidation
open ReadWindowCuts (Cut)
open Mettapedia.Algorithms.Collections

inductive Role where
  | rewrite | typing | equation
  deriving DecidableEq

structure World (Space Row : Type*) where
  resolution : Space → List Space
  occurrences : Space → List Row

inductive Field (Space : Type*) where
  | path (root : Space)
  | raw (space : Space)
  | catalog (space : Space) (role : Role)
  deriving DecidableEq

inductive Port (Space Name : Type*) where
  | whole (field : Field Space)
  | named (space : Space) (role : Role) (name : Name)
  deriving DecidableEq

inductive Reply (Space Row : Type*) where
  | path (spaces : List Space)
  | rows (occurrences : List Row)
  deriving DecidableEq

variable {S N R : Type*}

/-- Outer none: not a declaration of this role. Inner none: a wildcard head. -/
abbrev Classifier (N R : Type*) := Role → R → Option (Option N)

def catalog (classify : Classifier N R) (role : Role) (rows : List R) : List R :=
  rows.filter fun r => (classify role r).isSome

/-- Removing only data need not remove quotations of declarations; what
counts as a declaration is the chosen profile's interpretation of a row. -/
def declarations (c : Classifier N R) (rows : List R) : List R :=
  rows.filter fun r => (c .rewrite r).isSome || (c .typing r).isSome || (c .equation r).isSome

theorem catalog_of_declarations (c : Classifier N R) (k : Role) (rows : List R) :
    catalog c k (declarations c rows) = catalog c k rows := by
  simp only [catalog, declarations, List.filter_filter]
  apply List.filter_congr
  intro r _
  cases k <;> cases c .rewrite r <;> cases c .typing r <;> cases c .equation r <;> rfl

def fieldRead (classify : Classifier N R) (w : World S R) : Field S → Reply S R
  | .path s => .path (w.resolution s)
  | .raw s => .rows (w.occurrences s)
  | .catalog s k => .rows (catalog classify k (w.occurrences s))

def protects : Port S N → Field S
  | .whole f => f
  | .named s k _ => .catalog s k

def selects [DecidableEq N] (classify : Classifier N R) (k : Role) (name : N) (r : R) : Bool :=
  match classify k r with
  | none => false
  | some none => true
  | some (some h) => decide (h = name)

def project [DecidableEq N] (c : Classifier N R) : Port S N → Reply S R → Reply S R
  | .named _ k n, .rows rs => .rows (rs.filter (selects c k n))
  | _, answer => answer

def read [DecidableEq N] (c : Classifier N R) (w : World S R) (p : Port S N) : Reply S R :=
  project c p (fieldRead c w (protects p))

@[simp] theorem read_whole [DecidableEq N] (c : Classifier N R) (w : World S R) (f : Field S) :
    read c w (.whole f) = fieldRead c w f := rfl

private def atName (space : S) (k : Role) (n : N) :
    ReadOnlyQuery.Program (Port S N) (Reply S R) (List R) :=
  .read (.named space k n) fun
    | .rows rs => .pure rs
    | .path _ => .pure []

/-- The root supplies its own ordered resolution path. Repeated imports are
observable here; a dialect with import deduplication supplies its resolved path. -/
def resolve (root : S) (k : Role) (n : N) :
    ReadOnlyQuery.Program (Port S N) (Reply S R) (List R) :=
  .read (.whole (.path root)) fun
    | .path spaces => ReadOnlyQuery.flatTraverse spaces (fun s => atName s k n)
    | .rows _ => .pure []

theorem resolve_answer [DecidableEq N] (c : Classifier N R) (w : World S R)
    (root : S) (k : Role) (n : N) :
    (ReadOnlyQuery.run (read c w) (resolve root k n)).answer =
      (w.resolution root).flatMap (fun s => (catalog c k (w.occurrences s)).filter (selects c k n)) := by
  change (ReadOnlyQuery.run _ (ReadOnlyQuery.flatTraverse _ _)).answer = _
  rw [ReadOnlyQuery.run_flatTraverse]
  rfl

theorem resolve_receipt [DecidableEq N] (c : Classifier N R) (w : World S R)
    (root : S) (k : Role) (n : N) :
    (ReadOnlyQuery.run (read c w) (resolve root k n)).reads =
      (.whole (.path root), .path (w.resolution root)) ::
        (w.resolution root).map (fun s => (.named s k n, read c w (.named s k n))) := by
  change _ :: (ReadOnlyQuery.run _ (ReadOnlyQuery.flatTraverse _ _)).reads = _ :: _
  rw [ReadOnlyQuery.run_flatTraverse_reads]
  simp [atName, ReadOnlyQuery.run, read, project, protects, fieldRead]
  induction w.resolution root with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- The converse matters: the unfiltered port witnesses any change of field.
This works even for infinitely many names, including never-mentioned names. -/
theorem classChanged_iff [DecidableEq N] {m : ℕ} (c : Classifier N R)
    (history : Cut m → World S R) (f : Field S) (i : Fin m) :
    ClassChangedAt (fun t => read c (history t)) protects f i ↔
      fieldRead c (history i.succ) f ≠ fieldRead c (history i.castSucc) f := by
  constructor
  · rintro ⟨port, rfl, changed⟩ eq
    exact changed (congrArg (project c port) eq)
  · intro changed
    exact ⟨.whole f, rfl, changed⟩

instance changesDecidable [DecidableEq S] [DecidableEq N] [DecidableEq R] {m : ℕ}
    (c : Classifier N R) (history : Cut m → World S R) (f : Field S) :
    DecidablePred (ClassChangedAt (fun t => read c (history t)) protects f) :=
  fun i => decidable_of_iff _ (classChanged_iff c history f i).symm

section History
variable [DecidableEq S] [DecidableEq N] [DecidableEq R] {m : ℕ}
    (c : Classifier N R) (history : Cut m → World S R)

/-- A semantic change counter; not an assertion about machine-word epochs. -/
def revision : Cut m → Field S → ℕ :=
  countingVersion (fun t => read c (history t)) protects

theorem revision_step (i : Fin m) (f : Field S) :
    revision c history i.succ f = revision c history i.castSucc f +
      if fieldRead c (history i.succ) f ≠ fieldRead c (history i.castSucc) f then 1 else 0 := by
  simp only [revision, countingVersion_succ, classChanged_iff]

/-- Arbitrary edits to data (not only append) require no catalogue bump
if the ordered declaration subsequence is unchanged. The raw field is
deliberately not covered by this law. -/
theorem data_edit_keeps_catalogues (i : Fin m) (s : S)
    (same : declarations c ((history i.succ).occurrences s) =
      declarations c ((history i.castSucc).occurrences s)) (k : Role) :
    revision c history i.succ (.catalog s k) = revision c history i.castSucc (.catalog s k) := by
  have preserved := congrArg (catalog c k) same
  simp only [catalog_of_declarations] at preserved
  rw [revision_step, if_neg (fun h => h (congrArg (Reply.rows (Space := S)) preserved)),
    Nat.add_zero]

/-- Includes the read discovering which spaces to visit, if the program makes
that choice adaptively. Preserves its ordered reads as well as its answer. -/
theorem replay {A : Type*} {t₀ t : Cut m} (later : t₀ ≤ t)
    (q : ReadOnlyQuery.Program (Port S N) (Reply S R) A)
    (valid : StampAgrees (revision c history) t
      (takeStamp protects (revision c history) t₀ (ReadOnlyQuery.run (read c (history t₀)) q).reads)) :
    ReadOnlyQuery.run (read c (history t)) q = ReadOnlyQuery.run (read c (history t₀)) q :=
  reuse_sound countingVersion_isVersioning later q valid
end History

theorem append_catalog_iff (c : Classifier N R) (k : Role) (old extra : List R) :
    catalog c k (old ++ extra) = catalog c k old ↔ ∀ r ∈ extra, c k r = none := by
  simp [catalog, List.filter_eq_nil_iff]

/-- A data-only append is visible to raw match, but not to any catalogue.
Neither ordering nor duplicate multiplicity is quotiented away. -/
theorem data_append (c : Classifier N R) (old : List R) (r : R) (data : ∀ k, c k r = none) :
    old ++ [r] ≠ old ∧ ∀ k, catalog c k (old ++ [r]) = catalog c k old := by
  exact ⟨by simp, fun k => (append_catalog_iff c k old [r]).2 (by simpa using data k)⟩

/-- Number before selecting: inserting a row with a different head does not
renumber existing occurrences. The offset counts raw rows, not just matches. -/
def namedSuffix [DecidableEq N] (c : Classifier N R) (k : Role) (n : N) (start : Nat)
    (rs : List R) : List (R × Nat) :=
  (rs.zipIdx start).filter fun p => selects c k n p.1

theorem append_namedSuffix [DecidableEq N] (c : Classifier N R) (k : Role) (n : N)
    (start : Nat) (old extra : List R) :
    namedSuffix c k n start (old ++ extra) =
      namedSuffix c k n start old ++ namedSuffix c k n (start + old.length) extra := by
  simp only [namedSuffix, List.zipIdx_append, List.filter_append]

/-- The length of the old name table is not a code for an unknown name. -/
def knownCode [DecidableEq N] (keys : List N) (name : N) : Option Nat :=
  if name ∈ keys then some (keys.idxOf name) else none

theorem knownCode_grow [DecidableEq N] (keys input : List N) (n : N) (known : n ∈ keys) :
    knownCode (StableKeyEncoding.encode keys input).1 n = knownCode keys n := by
  have member := (StableKeyEncoding.encode_prefix keys input).subset known
  simp [knownCode, known, member, StableKeyEncoding.earlier_code_unchanged keys input n known]

theorem unrelated_growth_preserves_miss [DecidableEq N] (keys input : List N) (n : N)
    (old : n ∉ keys) (fresh : n ∉ input) :
    knownCode (StableKeyEncoding.encode keys input).1 n = none := by
  simp [knownCode, StableKeyEncoding.encode_membership, old, fresh]

theorem default_slot_collision :
    ([] : List Nat).idxOf 7 = ([9] : List Nat).idxOf 9 ∧
    knownCode ([] : List Nat) 7 ≠ knownCode [9] 9 := by decide

private def oneAlias : Classifier Unit Nat := fun k _ =>
  if k = .equation then some (some ()) else none

private def edited : Cut 2 → World Unit Nat := fun t =>
  ⟨fun _ => [()], fun _ => if t.val = 1 then [7] else []⟩

/-- An install followed by removal restores empty content, not revision zero. -/
theorem empty_after_edit :
    fieldRead oneAlias (edited 0) (.catalog () .equation) =
      fieldRead oneAlias (edited 2) (.catalog () .equation) ∧
    revision oneAlias edited 0 (.catalog () .equation) = 0 ∧
    revision oneAlias edited 2 (.catalog () .equation) = 2 := by decide +kernel

private def route (selected : Bool) : World Bool Nat :=
  ⟨fun _ => [selected], fun s => if s then [2, 2] else [1]⟩

/-- Every leaf read is unchanged. Omitting the read that *selected* the
leaves would nevertheless reuse the wrong answer, even its wrong count. -/
theorem changed_import_path :
    (∀ s, read oneAlias (route false) (.named s .equation ()) =
      read oneAlias (route true) (.named s .equation ())) ∧
    (ReadOnlyQuery.run (read oneAlias (route false)) (resolve false .equation ())).answer = [1] ∧
    (ReadOnlyQuery.run (read oneAlias (route true)) (resolve false .equation ())).answer = [2, 2] := by
  exact ⟨fun _ => rfl, rfl, rfl⟩

private def heads : Classifier Nat (Option Nat) := fun k head =>
  if k = .rewrite then some head else none

theorem wildcard_reaches_previously_missing :
    namedSuffix heads .rewrite 7 0 [some 9] = [] ∧
    namedSuffix heads .rewrite 7 0 [some 9, none] = [(none, 1)] := by decide

end Mettapedia.GSLT.Contracts.LiveTheoryProjections
