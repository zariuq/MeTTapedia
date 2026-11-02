import Mathlib.Tactic

/-!
# One scope stamp and head-partitioned updates

The source writes every index's scope and updates its selected occurrence.
The target stores the common scope once and updates only the indexes which
can admit the old or new row head. A missing slot has no row; an unknown
head can affect every index. Extra column tests remain the same in both
representations. Occurrence coordinates remain distinct from row payloads.

The laws concern one coordinate replacement. Appending, removing a final
coordinate and swap removal are compositions of these replacements with a
new shared scope. A general contraction can affect every coordinate and
therefore still requires transporting all retained postings.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PartitionedIndexUpdates

inductive Head (H : Type) where
  | unknown
  | closed
  | named (head : H)
  deriving DecidableEq

structure Row (H V : Type) where
  head : Head H
  value : V
  deriving DecidableEq

variable {H V K M : Type} [DecidableEq H]

def admits (owner : Option H) : Option (Row H V) → Bool
  | none => false
  | some row => match owner, row.head with
    | none, _ => true
    | some _, .unknown => true
    | some _, .closed => false
    | some h, .named r => decide (h = r)

def project (owner : K → Option H) (column : K → V → Bool)
    (key : K) (row : Option (Row H V)) : Option (Row H V) :=
  if admits (owner key) row then row.filter (fun r => column key r.value) else none

def affected (owner : K → Option H) (key : K)
    (old new : Option (Row H V)) : Bool :=
  admits (owner key) old || admits (owner key) new

abbrev Payload (H V : Type) := ℕ → Option (Row H V)
abbrev Source (K M H V : Type) := K → M × Payload H V

structure Grouped (K M H V : Type) where
  scope : M
  payload : K → Payload H V

def expand (group : Grouped K M H V) : Source K M H V :=
  fun key => (group.scope, group.payload key)

def Coherent (owner : K → Option H) (column : K → V → Bool)
    (facts : Payload H V) (group : Grouped K M H V) : Prop :=
  ∀ key pos, group.payload key pos = project owner column key (facts pos)

def sourceWrite (owner : K → Option H) (column : K → V → Bool)
    (source : Source K M H V) (scope : M) (pos : ℕ) (row : Option (Row H V)) :
    Source K M H V :=
  fun key => (scope, Function.update (source key).2 pos (project owner column key row))

def groupedWrite (owner : K → Option H) (column : K → V → Bool)
    (facts : Payload H V) (group : Grouped K M H V)
    (scope : M) (pos : ℕ) (row : Option (Row H V)) : Grouped K M H V :=
  ⟨scope, fun key => if affected owner key (facts pos) row then
      Function.update (group.payload key) pos (project owner column key row)
    else group.payload key⟩

theorem write_refines (owner : K → Option H) (column : K → V → Bool)
    (facts : Payload H V) (group : Grouped K M H V)
    (coherent : Coherent owner column facts group)
    (scope : M) (pos : ℕ) (row : Option (Row H V)) :
    expand (groupedWrite owner column facts group scope pos row) =
      sourceWrite owner column (expand group) scope pos row := by
  funext key
  apply Prod.ext
  · rfl
  · funext at_
    by_cases touches : affected owner key (facts pos) row = true
    · simp [expand, groupedWrite, sourceWrite, touches]
    · have none : admits (owner key) (facts pos) = false ∧
          admits (owner key) row = false := by
        simpa [affected, Bool.or_eq_true] using touches
      obtain ⟨noOld, noNew⟩ := none
      by_cases same : at_ = pos
      · subst at_
        simpa [expand, groupedWrite, sourceWrite, touches, project, noOld, noNew]
          using coherent key pos
      · simp [expand, groupedWrite, sourceWrite, touches, same]

theorem write_coherent (owner : K → Option H) (column : K → V → Bool)
    (facts : Payload H V) (group : Grouped K M H V)
    (coherent : Coherent owner column facts group)
    (scope : M) (pos : ℕ) (row : Option (Row H V)) :
    Coherent owner column (Function.update facts pos row)
      (groupedWrite owner column facts group scope pos row) := by
  intro key at_
  have refine := congrArg (fun s : Source K M H V => (s key).2 at_)
    (write_refines owner column facts group coherent scope pos row)
  by_cases same : at_ = pos
  · subst at_
    simpa [expand, sourceWrite] using refine
  · simp [expand, sourceWrite, same] at refine
    simpa [same] using refine.trans (coherent key at_)

theorem other_head_untouched (owner : K → Option H) (key : K) (h r : H)
    (owned : owner key = some h) (different : h ≠ r) (value : V) :
    affected owner key none (some ⟨.named r, value⟩) = false := by
  simp [affected, admits, owned, different]

example : admits (some (2 : ℕ)) (some (Row.mk .unknown 7)) = true := by decide
example : admits (some (2 : ℕ)) (some (Row.mk (.named 3) 7)) = false := by decide
example : admits (none : Option ℕ) (some (Row.mk .closed 7)) = true := by decide

end Mettapedia.Machines.PartitionedIndexUpdates
