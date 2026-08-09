import Mathlib.Data.List.Basic

/-!
# Space-mediated reflection is guarded: the revision logic of self-inspection

A MeTTa program never inspects a live computation: it `match`es atoms already
*stored* in a space, and every self-modification is an `add-atom` at a later
revision.  This module makes that discipline a formal object and proves the
four facts the pattern silently relies on:

1. `snapshot_stable` — a reflective read at revision `r` is unaffected by any
   later additions: program B, asked about program A, answers about A's
   *snapshot*, never A's live state.
2. `lob` — the temporal logic this induces has "later" = *strictly earlier
   revision*, and its Löb rule `(▷P → P) → P` is exactly strong induction on
   revisions.  Guarded self-reference through the space is therefore sound,
   with no further axiom.
3. `GuardedImprover.tower_meaning_const` — a program that repeatedly rewrites
   itself from snapshots, each step meaning-preserving, has one extensional
   meaning at every revision.  This is the license behind
   "inspect own source → derive faster version → install".
4. `no_fixed_point_of_progress` — the negative witness: *unguarded*
   self-reference demands a simultaneous fixed point `p = improve p`, which
   need not exist.  Guarding through revisions is what made the tower total.

Intensionality is real but *gated* (`observe_sem_eq_of_meaning_eq` vs
`observe_src_distinguishes`): without the source capability, extensionally
equal programs are indistinguishable; with it, they are distinguishable.
Observational equivalence is thus relative to a declared capability, not
destroyed by reflection — the finite-model kernel of the Wand-collapse repair.

These are finite-model statements about the discipline itself, not about a
full calculus: congruence for a real term language, the transfinite tower,
and ultraproduct transfer are the successor obligations.
-/

namespace Mettapedia.GSLT.Dynamics.SpaceGuardedReflection

/-! ## Snapshots of an append-only history -/

variable {Atom : Type}

/-- The space history is the append-only log of stored atoms; revision `r`
denotes its first `r` entries.  (`add-atom` appends; removal would be a
separate, coarser event and is not needed for the guarding theorems.) -/
def snapshot (h : List Atom) (r : ℕ) : List Atom := h.take r

/-- **The veil.**  A reflective read at revision `r` is stable under every
later extension of the history: B's answer about A cannot depend on what A
does after being asked. -/
theorem snapshot_stable (h ext : List Atom) (r : ℕ) (hr : r ≤ h.length) :
    snapshot (h ++ ext) r = snapshot h r := by
  induction h generalizing r with
  | nil => simp [snapshot, Nat.le_zero.mp hr]
  | cons a t ih =>
      cases r with
      | zero => simp [snapshot]
      | succ r =>
          simpa [snapshot, List.take_succ_cons] using
            ih r (Nat.le_of_succ_le_succ hr)

/-- Snapshots grow monotonically: an earlier snapshot is a prefix of a later
one, so nothing observed at revision `r` is ever retracted at `s ≥ r`. -/
theorem snapshot_prefix (h : List Atom) {r s : ℕ} (hrs : r ≤ s) :
    snapshot h r <+: snapshot h s := by
  simpa [snapshot] using List.take_prefix_take_left (l := h) hrs

/-! ## The revision logic and its Löb rule -/

/-- The later modality of the space logic: `later P r` holds when `P` holds
at every strictly earlier revision.  This is what a stored snapshot gives a
self-inspecting program: knowledge of its *past* states only. -/
def later (P : ℕ → Prop) (r : ℕ) : Prop := ∀ s < r, P s

/-- **Löb's rule is strong induction on revisions.**  If establishing `P` at
revision `r` may assume `P` at all earlier revisions, then `P` holds at every
revision.  Sound self-reference through the space needs no new axiom: the
guard `▷` is the revision order, and the revision order is well-founded. -/
theorem lob (P : ℕ → Prop) (step : ∀ r, later P r → P r) : ∀ r, P r := by
  intro r
  induction r using Nat.strongRecOn with
  | ind n ih => exact step n ih

/-! ## Guarded self-improvement -/

variable {Prog Sem : Type}

/-- A self-improvement discipline: `improve` derives the next version of a
program from a *snapshot* of the current one, and each step preserves
extensional meaning.  `improve` never receives the live program — only the
stored value — which is why `tower` below is a total function. -/
structure GuardedImprover (Prog Sem : Type) where
  /-- Extensional meaning (the declared observation of answers). -/
  meaning : Prog → Sem
  /-- Derivation of the next revision from the current snapshot. -/
  improve : Prog → Prog
  /-- Each installed revision is extensionally faithful to its snapshot. -/
  sound : ∀ p, meaning (improve p) = meaning p

/-- The revision tower: version at revision `r` of a self-improving program. -/
def GuardedImprover.tower (si : GuardedImprover Prog Sem) (p₀ : Prog) :
    ℕ → Prog
  | 0 => p₀
  | r + 1 => si.improve (si.tower p₀ r)

/-- **License for self-optimization.**  Every revision of the tower has the
same extensional meaning as the original: a program may inspect its stored
source, derive a faster version, and install it, indefinitely, without
semantic drift — provided each step reads only snapshots. -/
theorem GuardedImprover.tower_meaning_const (si : GuardedImprover Prog Sem)
    (p₀ : Prog) : ∀ r, si.meaning (si.tower p₀ r) = si.meaning p₀
  | 0 => rfl
  | r + 1 => by
      rw [GuardedImprover.tower, si.sound,
        si.tower_meaning_const p₀ r]

/-- **Negative witness: unguarded self-reference can be unsatisfiable.**
Demanding the improved program *be* the current program — the simultaneous
fixed point that live (unguarded) self-reference requires — has no solution
for as simple an `improve` as successor.  The revision tower exists for every
`improve`; the fixed point does not. -/
theorem no_fixed_point_of_progress : ¬ ∃ n : ℕ, n = n + 1 := by
  rintro ⟨n, h⟩
  exact absurd h.symm (Nat.succ_ne_self n)

/-! ## Capability-gated intensionality -/

/-- What an observer may see of a stored program: its meaning always; its
source only through the reflective capability. -/
inductive Observation (Prog Sem : Type) where
  | sem : Sem → Observation Prog Sem
  | src : Prog → Observation Prog Sem
  deriving DecidableEq

/-- Observation relative to a capability: without `reflective` access the
observer sees only the meaning; with it, the stored source. -/
def observe (meaning : Prog → Sem) : Bool → Prog → Observation Prog Sem
  | false, p => .sem (meaning p)
  | true, p => .src p

/-- Without the source capability, extensionally equal programs are
indistinguishable: the pure fragment's equational theory survives reflection
because reflection is not ambient. -/
theorem observe_sem_eq_of_meaning_eq (meaning : Prog → Sem) {p q : Prog}
    (h : meaning p = meaning q) :
    observe meaning false p = observe meaning false q := by
  simp [observe, h]

/-- With the source capability, extensionally equal programs may be
distinguished: intensionality is real, and it is exactly as large as the
granted capability.  (Witness: two distinct programs with one meaning.) -/
theorem observe_src_distinguishes :
    ∃ (meaning : Bool → Unit) (p q : Bool),
      meaning p = meaning q ∧
        observe meaning true p ≠ observe meaning true q := by
  refine ⟨fun _ => (), true, false, rfl, ?_⟩
  simp [observe]

end Mettapedia.GSLT.Dynamics.SpaceGuardedReflection
