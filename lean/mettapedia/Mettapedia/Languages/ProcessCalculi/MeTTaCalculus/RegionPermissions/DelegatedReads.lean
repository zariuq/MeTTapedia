import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.OwnedReads
import Mettapedia.Machines.Kernel.Delegation

/-!
# Reads under delegated authority: exactly when a universal read is safe without validation

`Machines.Kernel.Delegation` gives authority that moves only by passing capabilities from a
declared genesis, its exact reach (`canHold_iff`), and revocation of everything derived from a
capability (`revoke_removes_derived`). Here its objects are **facets at names**: a capability to
`(send, n)` is the right to make at name `n`. Commits are formed under the capabilities their actor
holds at the moment (`CapFormed`), and a **system run** interleaves delegation steps with commits
(`SysRun`).

## The three cases of a universal read

Fix a process, the **owner**, and a universal read at the names `A` (absence, "every row here is
like this").

1. **Owned.** No other subject can ever hold `send` at `A` from the genesis:
   `∀ b ≠ owner, ¬ CanHold st₀ b (send, n)`. Then the read stays true across every run of the
   others, whatever they delegate among themselves or receive from the owner
   (`delegated_antitone_stable`). This is exact: if some other subject can reach `send` at a name
   of `A`, a run of delegations and one commit falsifies absence there
   (`delegated_absence_falsified`), so the absence read is preserved by every run of the others
   exactly when the owned condition holds (`absence_preserved_iff`). `canHold_iff` makes the
   condition a property of the genesis alone.
2. **Sealed.** Every `send` at `A` held by another subject was derived from one capability `i` of
   the owner (the authority is stratified below `i`). Revoking `i` removes all of them
   (`revoke_seals`); from then on, as long as the owner passes no `send` at `A` again, the seal
   persists (`sealed_run`) and the read is stable (`stable_after_seal`). Sealing is revocation.
3. **Shared.** Otherwise the read must be validated when its commit fires: a full re-read or an
   epoch of the region. `Enabled.queries_hold` is that validation in the commit semantics; on the
   runtime's revision protocol it is `SharedReads.shared_absence_stale_under_revision`.

An existential read needs none of this for correctness: its witnesses validate it
(`ReadPolarity.monotone_of_witnesses_present`). Its *stability* has the dual condition, with
`receive` in place of `send` (`delegated_monotone_stable`).

## Controls

`Controls.granted_other_falsifies` and `Controls.unreachable_other_cannot` are a genesis in which
another subject can reach `send` (the owner may grant to it) and one in which it cannot.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
open Mettapedia.Machines.Kernel

variable {O : Type} [DecidableEq O] {R : Type} {N : Type} [DecidableEq N]
  {Sub : Type} [DecidableEq Sub]

/-- The capability to use facet `f` at name `n`. -/
abbrev facetAt (f : Facet) (n : N) : Delegation.Target Sub (Facet × N) := .obj (f, n)

section System

variable (label : O → R) (loc : R → N)

/-- **A commit formed under held capabilities**: its actor holds the facet of every part at the
name where the part lies. -/
structure CapFormed (caps : Delegation.State Sub (Facet × N)) (a : Sub) (c : Commit O R) : Prop where
  taken : ∀ o ∈ c.taken, Delegation.Holds caps a (facetAt .receive (loc (label o))) false
  kept : ∀ o ∈ c.kept, Delegation.Holds caps a (facetAt .peek (loc (label o))) false
  made : ∀ o ∈ c.made, Delegation.Holds caps a (facetAt .send (loc (label o))) false
  queries : ∀ read ∈ c.queries, ∀ r, read.region r = true →
    Delegation.Holds caps a (facetAt .observe (loc r)) false

/-- One act of the system: a delegation step, or a commit by a subject. -/
inductive Act (Sub O R N : Type) where
  | deleg (op : Delegation.Op Sub (Facet × N))
  | commit (a : Sub) (c : Commit O R)

/-- **A run of the system.** Delegation steps change the capabilities; commits, enabled at the
store and formed under their actor's current capabilities, change the store. -/
inductive SysRun : Delegation.State Sub (Facet × N) → Finset O → List (Act Sub O R N) →
    Delegation.State Sub (Facet × N) → Finset O → Prop
  | nil (caps : Delegation.State Sub (Facet × N)) (store : Finset O) : SysRun caps store [] caps store
  | deleg {caps caps' : Delegation.State Sub (Facet × N)} {store store' : Finset O} {op : Delegation.Op Sub (Facet × N)}
      {rest : List (Act Sub O R N)} (after : SysRun (Delegation.step caps op) store rest caps' store') :
      SysRun caps store (.deleg op :: rest) caps' store'
  | commit {caps caps' : Delegation.State Sub (Facet × N)} {store store' : Finset O} {a : Sub}
      {c : Commit O R} {rest : List (Act Sub O R N)} (enabled : Enabled label store c)
      (formed : CapFormed label loc caps a c) (after : SysRun caps (fire store c) rest caps' store') :
      SysRun caps store (.commit a c :: rest) caps' store'

/-- Every commit of the run is by a subject other than the owner. -/
def OthersActs (owner : Sub) (acts : List (Act Sub O R N)) : Prop :=
  ∀ a c, Act.commit a c ∈ acts → a ≠ owner

end System

section Owned

variable {label : O → R} {loc : R → N}

omit [DecidableEq O] [DecidableEq N] [DecidableEq Sub] in
theorem OthersActs.tail {owner : Sub} {act : Act Sub O R N} {rest : List (Act Sub O R N)}
    (others : OthersActs owner (act :: rest)) : OthersActs owner rest :=
  fun a c member => others a c (List.mem_cons_of_mem _ member)

/-- **Owned universal reads, under delegation.** If no subject other than the owner can ever
hold `send` at the read's names, a universal read stays true across every run in which only the
others commit, whatever anyone delegates. -/
theorem delegated_antitone_stable {st₀ : Delegation.State Sub (Facet × N)} {owner : Sub} {A : N → Bool}
    (owned : ∀ b, b ≠ owner → ∀ n, A n = true → ¬ Delegation.CanHold st₀ b (facetAt .send n) false)
    {P : Finset O → Prop} (antitone : DownwardClosed P) :
    ∀ {ops : List (Delegation.Op Sub (Facet × N))} {store : Finset O} {acts : List (Act Sub O R N)}
      {caps' : Delegation.State Sub (Facet × N)} {store' : Finset O},
      SysRun label loc (Delegation.run st₀ ops) store acts caps' store' → OthersActs owner acts →
      P (restrict label loc A store) → P (restrict label loc A store') := by
  intro ops store acts caps' store' h
  generalize hcaps : Delegation.run st₀ ops = caps at h
  induction h generalizing ops with
  | nil => intro _ holds; exact holds
  | @deleg caps caps' store store' op rest after ih =>
      intro others holds
      have : Delegation.run st₀ (ops ++ [op]) = Delegation.step caps op := by
        rw [Delegation.run_append, hcaps]; rfl
      exact ih (ops := ops ++ [op]) this others.tail holds
  | @commit caps caps' store store' a c rest enabled formed after ih =>
      intro others holds
      have notOwner : a ≠ owner := others a c List.mem_cons_self
      apply ih (ops := ops) hcaps others.tail
      refine antitone (restrict_fire_subset_of_makesOutside ?_ store) holds
      intro o made
      by_contra atA
      have atA' : A (loc (label o)) = true := by simpa using atA
      have held := formed.made o made
      rw [← hcaps] at held
      exact owned a notOwner _ atA' (Delegation.holds_confined st₀ ops held)

/-- **Owned existential reads are stable under delegation** when no other subject can ever hold
`receive` at the read's names. -/
theorem delegated_monotone_stable {st₀ : Delegation.State Sub (Facet × N)} {owner : Sub} {A : N → Bool}
    (owned : ∀ b, b ≠ owner → ∀ n, A n = true → ¬ Delegation.CanHold st₀ b (facetAt .receive n) false)
    {P : Finset O → Prop} (monotone : UpwardClosed P) :
    ∀ {ops : List (Delegation.Op Sub (Facet × N))} {store : Finset O} {acts : List (Act Sub O R N)}
      {caps' : Delegation.State Sub (Facet × N)} {store' : Finset O},
      SysRun label loc (Delegation.run st₀ ops) store acts caps' store' → OthersActs owner acts →
      P (restrict label loc A store) → P (restrict label loc A store') := by
  intro ops store acts caps' store' h
  generalize hcaps : Delegation.run st₀ ops = caps at h
  induction h generalizing ops with
  | nil => intro _ holds; exact holds
  | @deleg caps caps' store store' op rest after ih =>
      intro others holds
      have : Delegation.run st₀ (ops ++ [op]) = Delegation.step caps op := by
        rw [Delegation.run_append, hcaps]; rfl
      exact ih (ops := ops ++ [op]) this others.tail holds
  | @commit caps caps' store store' a c rest enabled formed after ih =>
      intro others holds
      have notOwner : a ≠ owner := others a c List.mem_cons_self
      apply ih (ops := ops) hcaps others.tail
      refine monotone (restrict_subset_fire_of_takesOutside ?_ store) holds
      intro o taken
      by_contra atA
      have atA' : A (loc (label o)) = true := by simpa using atA
      have held := formed.taken o taken
      rw [← hcaps] at held
      exact owned a notOwner _ atA' (Delegation.holds_confined st₀ ops held)

end Owned

/-! ## The owned condition is exact -/

section Exact

variable {label : O → R} {loc : R → N}

/-- A run of delegation operations, followed by any system run. -/
theorem SysRun.of_ops (label : O → R) (loc : R → N) :
    ∀ (ops : List (Delegation.Op Sub (Facet × N))) {caps caps' : Delegation.State Sub (Facet × N)}
      {store store' : Finset O} {rest : List (Act Sub O R N)},
      SysRun label loc (Delegation.run caps ops) store rest caps' store' →
        SysRun label loc caps store (ops.map Act.deleg ++ rest) caps' store'
  | [], _, _, _, _, _, h => h
  | op :: ops, caps, _, _, _, _, h => .deleg (SysRun.of_ops label loc ops (caps := Delegation.step caps op) h)

/-- **Reachable `send` falsifies absence.** If another subject can reach `send` at a name `n` of
the read, and an occurrence can be made fresh at `n`, some run of the others ends with an
occurrence at the read's names. -/
theorem delegated_absence_falsified {st₀ : Delegation.State Sub (Facet × N)} {owner b : Sub}
    (notOwner : b ≠ owner) {A : N → Bool} {n : N} (atA : A n = true)
    (reach : Delegation.CanHold st₀ b (facetAt .send n) false) {store : Finset O} {o : O}
    (fresh : o ∉ store) (atN : loc (label o) = n) :
    ∃ acts caps' store', SysRun label loc st₀ store acts caps' store' ∧ OthersActs owner acts ∧
      o ∈ restrict label loc A store' := by
  obtain ⟨ops, passes, held⟩ := Delegation.canHold_realized reach
  refine ⟨ops.map Act.deleg ++ [.commit b (Commit.makeOne o)], Delegation.run st₀ ops, fire store (Commit.makeOne o),
    SysRun.of_ops label loc ops (.commit ?_ ?_ (.nil _ _)), ?_, ?_⟩
  · exact ⟨by simp [Commit.makeOne], by simp [Commit.makeOne], by simp [Commit.makeOne],
      by simpa [Commit.makeOne] using fresh, by simp [Commit.makeOne]⟩
  · refine ⟨by simp [Commit.makeOne], by simp [Commit.makeOne], ?_, by simp [Commit.makeOne]⟩
    intro p made
    simp only [Commit.makeOne, Finset.mem_singleton] at made
    subst made
    rw [atN]
    exact held
  · intro a c member
    rcases List.mem_append.mp member with inOps | last
    · obtain ⟨op, -, impossible⟩ := List.mem_map.mp inOps
      cases impossible
    · simp only [List.mem_singleton, Act.commit.injEq] at last
      rw [last.1]
      exact notOwner
  · exact mem_restrict.mpr ⟨mem_fire.mpr (Or.inr (by simp [Commit.makeOne])), by rw [atN]; exact atA⟩

/-- **Exactly when absence needs no validation.** For a read at names where an occurrence can
always be made fresh, absence is preserved by every run of the others exactly when no other subject
can reach `send` at those names from the genesis. -/
theorem absence_preserved_iff {st₀ : Delegation.State Sub (Facet × N)} {owner : Sub} {A : N → Bool}
    {store : Finset O} (initially : restrict label loc A store = ∅)
    (freshAt : ∀ n, A n = true → ∃ o, o ∉ store ∧ loc (label o) = n) :
    (∀ acts caps' store', SysRun label loc st₀ store acts caps' store' → OthersActs owner acts →
        restrict label loc A store' = ∅) ↔
      ∀ b, b ≠ owner → ∀ n, A n = true → ¬ Delegation.CanHold st₀ b (facetAt .send n) false := by
  constructor
  · intro preserved b notOwner n atA reach
    obtain ⟨o, fresh, atN⟩ := freshAt n atA
    obtain ⟨acts, caps', store', h, others, inRegion⟩ :=
      delegated_absence_falsified (label := label) (loc := loc) notOwner atA reach fresh atN
    rw [preserved acts caps' store' h others] at inRegion
    simp at inRegion
  · intro owned acts caps' store' h others
    have antitone : DownwardClosed (fun B : Finset O => B = ∅) := by
      intro small large sub empty
      subst empty
      exact Finset.subset_empty.mp sub
    have h' : SysRun label loc (Delegation.run st₀ []) store acts caps' store' := h
    exact delegated_antitone_stable (label := label) (loc := loc) owned antitone h' others initially

end Exact

/-! ## Sealing is revocation -/

section Seal

variable {label : O → R} {loc : R → N}

/-- **Sealed**: no subject other than the owner holds `send` at the names of `A`. -/
def Sealed (caps : Delegation.State Sub (Facet × N)) (owner : Sub) (A : N → Bool) : Prop :=
  ∀ b, b ≠ owner → ∀ n, A n = true → ¬ Delegation.Holds caps b (facetAt .send n) false

/-- **Revoking the root of stratified authority seals the region.** If the owner holds capability
`i` and every other subject's `send` at `A` was derived from `i`, revoking `i` leaves no such
capability. -/
theorem revoke_seals {caps : Delegation.State Sub (Facet × N)} {owner : Sub} {A : N → Bool} {i : Nat}
    (heldI : caps.caps.any (fun c => c.id == i && c.holder == owner) = true)
    (stratified : ∀ c ∈ caps.caps, c.holder ≠ owner → ∀ n, A n = true →
      c.target = facetAt .send n → i ∈ c.ancestry) :
    Sealed (Delegation.step caps (.revoke owner i)) owner A := by
  intro b notOwner n atA held
  obtain ⟨c, member, holder, target, -⟩ := held
  have notDerived := Delegation.revoke_removes_derived caps owner i c member heldI
  have kept : c ∈ caps.caps := by
    simp only [Delegation.step, heldI, if_true] at member
    exact (List.mem_filter.mp member).1
  exact notDerived (stratified c kept (by rw [holder]; exact notOwner) n atA target)

/-- A delegation step **respects the seal** when it is not the owner passing `send` at `A`. -/
def RespectsSeal (owner : Sub) (A : N → Bool) (op : Delegation.Op Sub (Facet × N)) : Prop :=
  ∀ x g b n, op = .pass owner x g b → A n = true → x ≠ facetAt .send n

/-- **The seal persists** across every delegation step that respects it. -/
theorem sealed_step {caps : Delegation.State Sub (Facet × N)} {owner : Sub} {A : N → Bool}
    (sealed : Sealed caps owner A) {op : Delegation.Op Sub (Facet × N)} (respects : RespectsSeal owner A op) :
    Sealed (Delegation.step caps op) owner A := by
  intro b notOwner n atA held
  cases op with
  | pass a x g b' =>
      simp only [Delegation.step] at held
      split at held
      · rename_i c hsrc
        split at held
        · obtain ⟨c', member, holder, target, -⟩ := held
          rcases List.mem_cons.mp member with rfl | old
          · simp only at holder target
            subst target
            by_cases fromOwner : a = owner
            · subst fromOwner
              exact respects (facetAt .send n) g b' n rfl atA rfl
            · obtain ⟨cm, sourceHolder, sourceTarget, -⟩ := Delegation.source_spec hsrc
              exact sealed a fromOwner n atA
                ⟨c, cm, sourceHolder, sourceTarget, fun h => absurd h (by decide)⟩
          · exact sealed b notOwner n atA ⟨c', old, holder, target, fun h => absurd h (by decide)⟩
        · exact sealed b notOwner n atA held
      · exact sealed b notOwner n atA held
  | revoke a i =>
      simp only [Delegation.step] at held
      split at held
      · obtain ⟨c, member, holder, target, -⟩ := held
        exact sealed b notOwner n atA
          ⟨c, (List.mem_filter.mp member).1, holder, target, fun h => absurd h (by decide)⟩
      · exact sealed b notOwner n atA held

/-- Every delegation step of the run respects the seal. -/
def RespectsSealActs (owner : Sub) (A : N → Bool) (acts : List (Act Sub O R N)) : Prop :=
  ∀ op, Act.deleg op ∈ acts → RespectsSeal owner A op

/-- **A sealed region stays sealed, and its universal reads stay true**, across every run in which
only the others commit and the owner passes no `send` at its names again. -/
theorem stable_after_seal {owner : Sub} {A : N → Bool} {P : Finset O → Prop}
    (antitone : DownwardClosed P) :
    ∀ {caps caps' : Delegation.State Sub (Facet × N)} {store store' : Finset O}
      {acts : List (Act Sub O R N)},
      SysRun label loc caps store acts caps' store' → Sealed caps owner A →
      OthersActs owner acts → RespectsSealActs owner A acts →
      P (restrict label loc A store) → P (restrict label loc A store') ∧ Sealed caps' owner A := by
  intro caps caps' store store' acts h
  induction h with
  | nil => intro sealed _ _ holds; exact ⟨holds, sealed⟩
  | @deleg caps caps' store store' op rest after ih =>
      intro sealed others respects holds
      exact ih (sealed_step sealed (respects op List.mem_cons_self)) others.tail
        (fun op' member => respects op' (List.mem_cons_of_mem _ member)) holds
  | @commit caps caps' store store' a c rest enabled formed after ih =>
      intro sealed others respects holds
      have notOwner : a ≠ owner := others a c List.mem_cons_self
      refine ih sealed others.tail (fun op' member => respects op' (List.mem_cons_of_mem _ member)) ?_
      refine antitone (restrict_fire_subset_of_makesOutside ?_ store) holds
      intro o made
      by_contra atA
      have atA' : A (loc (label o)) = true := by simpa using atA
      exact sealed a notOwner _ atA' (formed.made o made)

end Seal

/-! ## Controls -/

namespace Controls

/-- The owner is `true`; the other subject is `false`. Objects are facets at name `0`. -/
def ownerSend : Delegation.Cap Bool (Facet × ℕ) := ⟨0, true, .obj (.send, 0), true, []⟩

/-- The owner may grant to the other subject. -/
def ownerGrantsOther : Delegation.Cap Bool (Facet × ℕ) := ⟨1, true, .subj false, true, []⟩

/-- A genesis where the owner holds `send` at name `0` and may grant to the other subject. -/
def grantingGenesis : Delegation.State Bool (Facet × ℕ) := ⟨[ownerSend, ownerGrantsOther], 2⟩

/-- A genesis where the owner holds `send` at name `0` and may grant to nobody. -/
def closedGenesis : Delegation.State Bool (Facet × ℕ) := ⟨[ownerSend], 1⟩

/-- In the granting genesis the other subject can reach `send` at `0`. -/
theorem other_reaches_send : Delegation.CanHold grantingGenesis false (facetAt .send 0) false :=
  .pass (a := true) (.base ⟨ownerSend, by simp [grantingGenesis], rfl, rfl, by simp⟩)
    (.base ⟨ownerGrantsOther, by simp [grantingGenesis], rfl, rfl, fun _ => rfl⟩)

/-- **Granted, the other falsifies absence**: an instance of `delegated_absence_falsified`, with
occurrence `5` made at name `0` from the empty store. -/
theorem granted_other_falsifies :
    ∃ acts caps' store', SysRun (Sub := Bool) (fun o : ℕ => o) (fun _ : ℕ => (0 : ℕ))
        grantingGenesis ∅ acts caps' store' ∧ OthersActs true acts ∧
      (5 : ℕ) ∈ restrict (fun o : ℕ => o) (fun _ : ℕ => (0 : ℕ)) (fun n => n == 0) store' :=
  delegated_absence_falsified (b := false) (by decide) (n := 0) (by decide) other_reaches_send
    (by simp) rfl

/-- What the closed genesis can reach: nothing at the other subject's name, and `send` only by
the owner. -/
def ClosedInv (a : Bool) (x : Delegation.Target Bool (Facet × ℕ)) : Prop :=
  x ≠ .subj false ∧ x ≠ .subj true ∧ (x = facetAt .send 0 → a = true)

theorem closedInv_of_canHold {a : Bool} {x : Delegation.Target Bool (Facet × ℕ)} {g : Bool}
    (h : Delegation.CanHold closedGenesis a x g) : ClosedInv a x := by
  induction h with
  | base held =>
      obtain ⟨c, member, holder, target, -⟩ := held
      simp only [closedGenesis, List.mem_singleton] at member
      subst member
      simp only [ownerSend] at holder target
      subst holder
      subst target
      exact ⟨by simp, by simp, fun _ => rfl⟩
  | @pass a b x g _ _ _ ihb =>
      exfalso
      cases b with
      | false => exact ihb.1 rfl
      | true => exact ihb.2.1 rfl

/-- **Closed, the other cannot**: in the closed genesis the other subject never reaches `send` at
`0`, so by `delegated_antitone_stable` every universal read there is stable against it. -/
theorem unreachable_other_cannot : ¬ Delegation.CanHold closedGenesis false (facetAt .send 0) false :=
  fun h => absurd ((closedInv_of_canHold h).2.2 rfl) (by decide)

/-- The other subject holds `send` at name `0` directly. -/
def otherHoldsSend : Delegation.State Bool (Facet × ℕ) := ⟨[⟨0, false, .obj (.send, 0), false, []⟩], 1⟩

/-- **Sealed and not sealed**: in the closed genesis only the owner holds `send` at name `0`;
where the other subject holds it, the region is not sealed. -/
theorem sealed_controls :
    Sealed closedGenesis true (fun n => n == 0) ∧ ¬ Sealed otherHoldsSend true (fun n => n == 0) := by
  refine ⟨?_, fun sealed => sealed false (by decide) 0 rfl
    ⟨_, List.mem_singleton_self _, rfl, rfl, fun h => absurd h (by decide)⟩⟩
  rintro b notOwner n - ⟨c, member, holder, -, -⟩
  simp only [closedGenesis, List.mem_singleton] at member
  subst member
  exact notOwner holder.symm

/-- **Formed and not formed under held capabilities**: in the closed genesis the owner may make at
name `0`, the other subject may not. -/
theorem capFormed_controls :
    CapFormed (fun o : ℕ => o) (fun _ : ℕ => (0 : ℕ)) closedGenesis true (Commit.makeOne 5) ∧
      ¬ CapFormed (fun o : ℕ => o) (fun _ : ℕ => (0 : ℕ)) closedGenesis false (Commit.makeOne 5) := by
  refine ⟨⟨by simp, by simp,
    fun _ _ => ⟨ownerSend, List.mem_singleton_self _, rfl, rfl, fun h => absurd h (by decide)⟩, by simp⟩,
    fun formed => ?_⟩
  obtain ⟨c, member, holder, -, -⟩ := formed.made 5 (by simp)
  simp only [closedGenesis, List.mem_singleton] at member
  subst member
  exact absurd holder (by decide)

/-- A revocation respects the seal; the owner passing `send` at a sealed name does not. -/
theorem respectsSeal_controls :
    RespectsSeal true (fun n : ℕ => n == 0) (.revoke true 0) ∧
      ¬ RespectsSeal true (fun n : ℕ => n == 0) (.pass true (facetAt .send 0) false false) := by
  refine ⟨fun x g b n h _ => (by cases h), fun respects => ?_⟩
  exact respects (facetAt .send 0) false false 0 rfl rfl rfl

/-- A run of the others, and one in which the owner commits. -/
theorem othersActs_controls :
    OthersActs (O := ℕ) (R := ℕ) (N := ℕ) true [Act.commit false (Commit.makeOne 5)] ∧
      ¬ OthersActs (O := ℕ) (R := ℕ) (N := ℕ) true [Act.commit true (Commit.makeOne 5)] := by
  refine ⟨fun a c member => ?_, fun others => others true _ List.mem_cons_self rfl⟩
  simp only [List.mem_singleton, Act.commit.injEq] at member
  rw [member.1]
  decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions
