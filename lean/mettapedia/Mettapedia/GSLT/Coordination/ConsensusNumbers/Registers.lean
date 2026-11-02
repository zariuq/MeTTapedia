import Mettapedia.GSLT.Coordination.ConsensusNumbers.Valence

/-!
# Read/write registers have consensus number one

A family of registers indexed by `ι`, each holding a value of `V`
(Herlihy 1991, Theorem 2; Loui and Abu-Amara 1987).

Every pair of operations hides its order from one of the two processes
(`registers_pairCannotOrder`):

* a read changes nothing (`noChange`);
* two writes to one register: the second erases the first (`overwritten`);
* two writes to different registers commute, and a write answers nothing (`commutes`).

So no wait-free protocol solves consensus for two processes from registers
(`registers_not_solvable_two`), and their consensus number is one
(`registers_hasConsensusNumber_one`).

## Controls

* `Controls.read_hidden`: a read is hidden from the writer of the same register.
* `Controls.write_write_overwritten`: a second write to one register hides the first.
* `Controls.reader_sees_write`: a reader is not blind to a write; the order of a write and a read
  is hidden from the writer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ConsensusNumbers

/-- Operations on a family of registers. -/
inductive RegOp (ι V : Type) where
  | read (i : ι)
  | write (i : ι) (v : V)

/-- A family of read/write registers: a read answers the value, a write answers nothing. -/
abbrev registers (ι V : Type) [DecidableEq ι] : DetObject where
  State := ι → V
  Op := RegOp ι V
  Res := Option V
  apply s
    | .read i => (s, some (s i))
    | .write i v => (Function.update s i v, none)

variable {ι V : Type} [DecidableEq ι]

/-- **Every pair of register operations hides its order from one of the two processes.** -/
theorem registers_pairCannotOrder : ∀ s a b, PairCannotOrder (registers ι V) s a b := by
  rintro s (i | ⟨i, v⟩) b
  · exact Or.inl (.noChange rfl)
  · cases b with
    | read j => exact Or.inr (.noChange rfl)
    | write j w =>
        by_cases same : i = j
        · subst same
          exact Or.inl (.overwritten (by simp [Function.update_idem]))
        · exact Or.inl (.commutes (by simp [Function.update_comm same]) rfl)

/-- **No two-process consensus from registers.** -/
theorem registers_not_solvable_two {n : ℕ} (two : 2 ≤ n) :
    ¬ Solvable (registers ι V).toObject n Bool :=
  not_solvable_of_pairCannotOrder two registers_pairCannotOrder

/-- **Registers have consensus number one.** -/
theorem registers_hasConsensusNumber_one [Inhabited V] :
    HasConsensusNumber (registers ι V).toObject 1 :=
  hasConsensusNumber_one (T := registers ι V) (fun _ => default) registers_pairCannotOrder

namespace Controls

/-- **Positive control**: a read of a register is hidden from a writer of it. -/
theorem read_hidden (s : Unit → Bool) :
    OrderHidden (registers Unit Bool) s (.read ()) (.write () true) := .noChange rfl

/-- **Positive control**: a second write to one register hides the first from the second writer. -/
theorem write_write_overwritten (s : Unit → Bool) :
    OrderHidden (registers Unit Bool) s (.write () false) (.write () true) :=
  .overwritten (by simp [Function.update_idem])

/-- **Negative control**: the reader is not blind to a write before its read: it answers `true`
after the write and `false` without it. The order of a write and a read is hidden from the writer
only (`commutes`: the writer gets no answer). -/
theorem reader_sees_write :
    ((registers Unit Bool).apply ((registers Unit Bool).apply (fun _ => false) (.write () true)).1
      (.read ())).2 ≠ ((registers Unit Bool).apply (fun _ => false) (.read ())).2 := by
  simp

end Controls

end Mettapedia.GSLT.Coordination.ConsensusNumbers
