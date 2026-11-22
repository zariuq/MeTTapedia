import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.OwnedReads

/-!
# The verdict region: the LCF rule as a capability, and what readers still have to do

A **verdict region** is a region at one name where judgments are kept. The LCF discipline says that
only the kernel can produce a theorem. As a capability discipline:

* **Minting.** Only the kernel holds `send` at the verdict name, the kernel hands out no `send`
  there, and it makes there only judgments it has checked. Then every occurrence at the verdict
  name, after any run of the whole system, carries a derivable judgment
  (`board_verdicts_derivable`). This is Morris's induction rule in the commit semantics; the seal
  calculus proves the same law for sealed boxes (`Seal.lcf_sound`).
* **Keeping.** When nobody holds or receives `receive` at the verdict name, no verdict ever
  leaves (`board_verdicts_permanent`): a user's existential read "this theorem is proved" stays
  true. The board profile gives its holder `send`, `peek` and `observe`, and others `peek`.
* **Users hold `peek`, not `receive`.** With `receive`, one user takes away a verdict another
  relies on (`Controls.receive_deletes_verdict`); a grant of `(peek receive)` to users is wrong,
  and `(peek)` is right (`Controls.peek_keeps_verdict`).

## What the capability does not give: which region a reader is reading

The minting law holds per region. A reader that finds "the verdict region" through data that
someone else can write may be reading another region, where another holder minted what it liked
(`Controls.forger_board_mints`). So a reader's acceptance has two parts: the identity of the region
it reads (a reference it obtained from the kernel, or an identity it can compare), and its policy
over what it accepts from that kernel (`Logic.EvidenceKinds`: a verdict is a reader's policy over
granted atoms, and "this kernel is sound" is one such atom). Minting is one discipline; use is two.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes

universe u v w x

variable {O : Type u} [DecidableEq O] {R : Type v} {N : Type w} {I : Type x} [DecidableEq I]

section Board

variable {label : O → R} {loc : R → N} {carries : R → Rights N}

/-- Every occurrence at the verdict name carries a derivable judgment. -/
def AllDerivable (label : O → R) (loc : R → N) (Derivable : R → Prop) (verdicts : N)
    (S : Finset O) : Prop :=
  ∀ o ∈ S, loc (label o) = verdicts → Derivable (label o)

/-- **The kernel's minting discipline** along a run: at the verdict name it makes only derivable
judgments, and nothing it makes carries `send` at the verdict name. -/
def KernelDiscipline (label : O → R) (loc : R → N) (carries : R → Rights N) (kernel : I)
    (verdicts : N) (Derivable : R → Prop) (run : List (I × Commit O R)) : Prop :=
  ∀ x ∈ run, x.1 = kernel → ∀ o ∈ x.2.made,
    (loc (label o) = verdicts → Derivable (label o)) ∧ carries (label o) verdicts .send = false

/-- **Only checked verdicts are ever on the board.** If no process but the kernel holds or
receives `send` at the verdict name, and the kernel follows its discipline, then after any run of
the whole system every occurrence at the verdict name is derivable. -/
theorem board_verdicts_derivable {Derivable : R → Prop} {verdicts : N} {kernel : I}
    {Γ Γ' : I → Rights N} {S S' : Finset O} {run : List (I × Commit O R)}
    (h : AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S run Γ' S')
    (sole : ¬ OthersAuthority label carries Γ S kernel verdicts .send)
    (discipline : KernelDiscipline label loc carries kernel verdicts Derivable run)
    (initially : AllDerivable label loc Derivable verdicts S) :
    AllDerivable label loc Derivable verdicts S' := by
  induction h with
  | nil => exact initially
  | @cons Γ₀ Γ₁ Γ₂ S₀ S₁ S₂ i c rest step after ih =>
      have head := discipline (i, c) List.mem_cons_self
      have keeps : i = kernel → ∀ o ∈ c.made, carries (label o) verdicts .send = false :=
        fun isKernel o made => (head isKernel o made).2
      apply ih (fun later => sole (step_othersAuthority_mono step keeps later))
        (fun y member => discipline y (List.mem_cons_of_mem _ member))
      intro o member atV
      rw [step.store] at member
      rcases mem_fire.mp member with ⟨inS, -⟩ | made
      · exact initially o inS atV
      · by_cases isKernel : i = kernel
        · exact (head isKernel o made).1 atV
        · have held := step.formed.made o made
          rw [atV] at held
          exact absurd (Or.inl ⟨i, isKernel, held⟩) sole

/-- **No verdict ever leaves** when nobody holds or receives `receive` at the verdict name. -/
theorem board_verdicts_permanent [DecidableEq N] {verdicts : N} {Γ Γ' : I → Rights N}
    {S S' : Finset O} {run : List (I × Commit O R)}
    (h : AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S run Γ' S')
    (noReceive : ¬ Authority label carries Γ S verdicts .receive) :
    restrict label loc (fun n => decide (n = verdicts)) S ⊆
      restrict label loc (fun n => decide (n = verdicts)) S' := by
  rw [run_store_eq h]
  apply restrict_subset_fireList_of_takesOutside
  intro e member o taken
  obtain ⟨y, inRun, rfl⟩ := List.mem_map.mp member
  have := h.never_receives noReceive y inRun o taken
  simpa using this

end Board

/-! ## Controls -/

namespace Controls

/-- Every occurrence is a verdict at name `0`; its label is itself. -/
def verdictLoc : ℕ → ℕ := fun _ => 0

/-- Nothing carries a facet. -/
def inertCarries : ℕ → Rights ℕ := fun _ _ _ => false

/-- The proposed user grant: `peek` and `receive` at the verdict name. -/
def peekReceiveUser : Rights ℕ := fun n f => n == 0 && (f == .peek || f == .receive)

/-- The board holder's facets: `send`, `peek`, `observe`. -/
def boardHolder : Rights ℕ := fun n f => n == 0 && (f == .send || f == .peek || f == .observe)

/-- The users' facets on a board: `peek`. -/
def peekUser : Rights ℕ := fun n f => n == 0 && f == .peek

/-- Kernel `true` holds the board; user `false` has the proposed `(peek receive)` grant. -/
def receiveGrant : Bool → Rights ℕ := fun i => if i then boardHolder else peekReceiveUser

/-- Kernel `true` holds the board; user `false` has `(peek)`. -/
def peekGrant : Bool → Rights ℕ := fun i => if i then boardHolder else peekUser

/-- **With `receive`, a user deletes a verdict another relies on**: the verdict `7` is the only
one at the verdict name, and one step of the user leaves none. -/
theorem receive_deletes_verdict :
    ∃ Γ' S', AuthorityRun (label := id) (loc := verdictLoc) (carries := inertCarries)
        receiveGrant {7} [(false, Commit.takeOne 7)] Γ' S' ∧
      restrict id verdictLoc (fun n => n == 0) S' = ∅ := by
  obtain ⟨h, -, gone⟩ := witness_taken_of_other_receive (label := id) (loc := verdictLoc)
    (carries := inertCarries) (Γ := receiveGrant) (S := {7}) (owner := true) (i := false) (by decide)
    (A := fun n => n == 0) (o := 7) (by decide) (by decide) (by decide)
  exact ⟨_, _, h, gone⟩

/-- **With `peek`, no verdict can leave**: nobody holds or receives `receive` at the verdict name
under the board profile, so `board_verdicts_permanent` keeps every verdict along every run. -/
theorem peek_keeps_verdict {run : List (Bool × Commit ℕ ℕ)} {Γ' : Bool → Rights ℕ}
    {S' : Finset ℕ}
    (h : AuthorityRun (label := id) (loc := verdictLoc) (carries := inertCarries) peekGrant {7}
      run Γ' S') :
    (7 : ℕ) ∈ S' := by
  have noReceive : ¬ Authority id inertCarries peekGrant ({7} : Finset ℕ) 0 .receive := by
    rintro (⟨i, held⟩ | ⟨o, -, carried⟩)
    · cases i <;> simp [peekGrant, boardHolder, peekUser] at held
    · simp [inertCarries] at carried
  have kept := board_verdicts_permanent h noReceive
  have : (7 : ℕ) ∈ restrict id verdictLoc (fun n => decide (n = 0)) ({7} : Finset ℕ) := by decide
  exact (mem_restrict.mp (kept this)).1

/-- A judgment is derivable when it is even. -/
def EvenDerivable : ℕ → Prop := fun j => j % 2 = 0

/-- **Another holder's board mints what it likes.** A forger holding `send` at its own name makes
the underivable judgment `7` there in one step: a reader that resolves "the verdict board" through
data the forger can write reads a board where the minting law does not hold. -/
theorem forger_board_mints :
    ∃ Γ' S', AuthorityRun (label := id) (loc := verdictLoc) (carries := inertCarries)
        (fun _ : Bool => boardHolder) ∅ [(false, Commit.makeOne 7)] Γ' S' ∧
      ¬ AllDerivable id verdictLoc EvenDerivable 0 S' := by
  obtain ⟨h, -, made⟩ := absence_falsified_of_other_send (label := id) (loc := verdictLoc)
    (carries := inertCarries) (Γ := fun _ : Bool => boardHolder) (S := ∅) (owner := true) (i := false)
    (by decide) (A := fun n => n == 0) (o := 7) (by simp) (by decide) (by decide)
    (fun _ _ => rfl)
  refine ⟨_, _, h, fun all => ?_⟩
  have := all 7 (mem_restrict.mp made).1 rfl
  simp [EvenDerivable] at this

/-- **Others' authority, present and absent**: under the `(peek receive)` grant the user holds
`receive` at the verdict name; under the board profile nobody but the holder does, and nothing
carries it. -/
theorem othersAuthority_controls :
    OthersAuthority id inertCarries receiveGrant ({7} : Finset ℕ) true 0 .receive ∧
      ¬ OthersAuthority id inertCarries peekGrant ({7} : Finset ℕ) true 0 .receive := by
  refine ⟨Or.inl ⟨false, by decide, by decide⟩, ?_⟩
  rintro (⟨i, notOwner, held⟩ | ⟨o, -, carried⟩)
  · cases i
    · revert held; decide
    · exact notOwner rfl
  · simp [inertCarries] at carried

/-- A board of even verdicts is derivable; a board holding `7` is not. -/
theorem allDerivable_controls :
    AllDerivable id verdictLoc EvenDerivable 0 {4} ∧ ¬ AllDerivable id verdictLoc EvenDerivable 0 {4, 7} := by
  refine ⟨fun o member _ => ?_, fun all => ?_⟩
  · rw [Finset.mem_singleton.mp member]
    simp [EvenDerivable]
  · have := all 7 (by decide) rfl
    simp [EvenDerivable] at this

/-- A kernel that makes only the even verdict `4` follows the minting discipline; one that makes
`7` does not. -/
theorem kernelDiscipline_controls :
    KernelDiscipline id verdictLoc inertCarries true 0 EvenDerivable [(true, Commit.makeOne 4)] ∧
      ¬ KernelDiscipline id verdictLoc inertCarries true 0 EvenDerivable [(true, Commit.makeOne 7)] := by
  refine ⟨?_, fun discipline => ?_⟩
  · intro x member _ o made
    simp only [List.mem_singleton] at member
    subst member
    simp only [Commit.makeOne_made, Finset.mem_singleton] at made
    subst made
    exact ⟨fun _ => by simp [EvenDerivable], rfl⟩
  · have := (discipline (true, Commit.makeOne 7) (by simp) rfl 7 (by simp)).1 rfl
    simp [EvenDerivable] at this

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions
