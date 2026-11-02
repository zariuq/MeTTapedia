import Mettapedia.GSLT.Coordination.ConsensusNumbers.Framework

/-!
# Which objects have a consensus number

`HasConsensusNumber T k` says that binary consensus is solvable over `T` for exactly the numbers of
processes up to `k`. Herlihy defines the consensus number as "the largest `n` for which `X` solves
`n`-process consensus", which presumes that solvability is closed downwards. Here that is a theorem:

* **Fewer processes are easier** (`Solvable.mono`): a protocol for `n` processes gives one for any
  `m ≤ n`. The first `m` processes run as before, and the others never move; a process never sees
  the local state of another, so no one can tell (`Protocol.restrict`). The absent processes'
  inputs are set to process `0`'s, so a decided value is still someone's input.
* **Every object with at least one state has a consensus number** (`hasConsensusNumber_of_nonempty`):
  `∞` if consensus is solvable for every number of processes, otherwise one less than the first
  number for which it is not.
* **An object with no state has none** (`not_hasConsensusNumber_of_isEmpty`): no protocol can even
  start, so consensus is not solvable even for no processes, while every `k` admits `0 ≤ k`.
* So an object has a consensus number exactly when it has a state (`hasConsensusNumber_iff`).

This is about the definition used here, which counts the object alone. Whether the consensus
number of several objects used together can exceed the largest of theirs (the robustness question
studied by Jayanti, and answered negatively for some nondeterministic objects by Lo and Hadzilacos)
is a different question, not settled here.

## Controls

* `Controls.stateless_has_none`: an object with no state has no consensus number (positive control
  for the exception).
* `Controls.restrict_keeps_agreement`: the first process of a two-process protocol, run alone, is a
  one-process protocol (positive control for `restrict`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ConsensusNumbers

namespace Protocol

variable {T : ObjectType} {n m : ℕ} {V : Type}

/-- **The first `m` processes** of a protocol for `n`, the others never moving. -/
abbrev restrict (P : Protocol T n V) (le : m ≤ n) : Protocol T m V where
  Local := P.Local
  start i v := P.start (Fin.castLE le i) v
  init := P.init
  action i := P.action (Fin.castLE le i)
  next i := P.next (Fin.castLE le i)

variable {P : Protocol T n V} {le : m ≤ n}

/-- A configuration of the first `m` processes, with the others at their start. -/
def embed (fill : Fin n → V) (C : (P.restrict le).Config) : P.Config :=
  ⟨C.obj, fun j => if hj : j.val < m then C.loc ⟨j.val, hj⟩ else P.start j (fill j)⟩

theorem embed_loc_castLE (fill : Fin n → V) (C : (P.restrict le).Config) (i : Fin m) :
    (embed fill C).loc (Fin.castLE le i) = C.loc i := by
  show (if hj : (Fin.castLE le i).val < m then C.loc ⟨(Fin.castLE le i).val, hj⟩
    else P.start _ (fill _)) = C.loc i
  rw [dif_pos (by simp [i.isLt])]
  rfl

theorem restrict_decision (fill : Fin n → V) (C : (P.restrict le).Config) (i : Fin m) :
    (P.restrict le).decision C i = P.decision (embed fill C) (Fin.castLE le i) := by
  unfold Protocol.decision
  rw [embed_loc_castLE]

theorem embed_update (fill : Fin n → V) (C : (P.restrict le).Config) (s : T.State) (i : Fin m)
    (l : P.Local) :
    embed fill (⟨s, Function.update C.loc i l⟩ : (P.restrict le).Config) =
      ⟨s, Function.update (embed fill C).loc (Fin.castLE le i) l⟩ := by
  refine Config.ext rfl (funext fun j => ?_)
  show (if hj : j.val < m then Function.update C.loc i l ⟨j.val, hj⟩ else P.start j (fill j)) =
    Function.update (embed fill C).loc (Fin.castLE le i) l j
  by_cases hj : j = Fin.castLE le i
  · subst hj
    rw [Function.update_self, dif_pos (by simp [i.isLt])]
    have e : (⟨(Fin.castLE le i).val, by simp [i.isLt]⟩ : Fin m) = i := Fin.ext rfl
    rw [e, Function.update_self]
  · rw [Function.update_of_ne hj]
    by_cases hm : j.val < m
    · rw [dif_pos hm]
      have ne : (⟨j.val, hm⟩ : Fin m) ≠ i := by
        intro h; apply hj; ext; simp [← h]
      rw [Function.update_of_ne ne]
      show C.loc ⟨j.val, hm⟩ = (if hj : j.val < m then C.loc ⟨j.val, hj⟩ else P.start j (fill j))
      rw [dif_pos hm]
    · rw [dif_neg hm]
      show P.start j (fill j) = (if hj : j.val < m then C.loc ⟨j.val, hj⟩ else P.start j (fill j))
      rw [dif_neg hm]

/-- **A step of one of the first `m` processes is a step of the whole protocol.** -/
theorem embed_step (fill : Fin n → V) {C D : (P.restrict le).Config} {i : Fin m}
    (step : (P.restrict le).Step C i D) : P.Step (embed fill C) (Fin.castLE le i) (embed fill D) := by
  cases step with
  | decided h => exact Step.decided (by rw [embed_loc_castLE]; exact h)
  | fires h hf =>
      rw [embed_update]
      have := Step.fires (P := P) (C := embed fill C) (i := Fin.castLE le i)
        (by rw [embed_loc_castLE]; exact h) hf
      rw [embed_loc_castLE] at this
      exact this
  | waits h never => exact Step.waits (by rw [embed_loc_castLE]; exact h) never

theorem embed_run (fill : Fin n → V) {C D : (P.restrict le).Config} {σ : List (Fin m)}
    (run : (P.restrict le).Run C σ D) :
    P.Run (embed fill C) (σ.map (Fin.castLE le)) (embed fill D) := by
  induction σ generalizing C with
  | nil => rw [run]; rfl
  | cons i σ ih =>
      obtain ⟨E, step, rest⟩ := run
      exact ⟨_, embed_step fill step, ih rest⟩

/-- The inputs of the whole protocol: the given ones, and process `0`'s for the others. -/
def fillInputs (pos : 0 < m) (x : Fin m → V) : Fin n → V :=
  fun j => if hj : j.val < m then x ⟨j.val, hj⟩ else x ⟨0, pos⟩

theorem embed_initial (pos : 0 < m) (x : Fin m → V) :
    embed (fillInputs pos x) ((P.restrict le).initial x) = P.initial (fillInputs pos x) := by
  refine Config.ext rfl (funext fun j => ?_)
  by_cases hj : j.val < m
  · simp [embed, Protocol.initial, restrict, fillInputs, hj]
  · simp [embed, Protocol.initial, fillInputs, hj]

/-- **The first `m` processes of a consensus protocol solve consensus among themselves.** -/
theorem Solves.restrict (S : P.Solves) (pos : 0 < m) : (P.restrict le).Solves := by
  have reachEmbed : ∀ x C, (P.restrict le).Reach x C → P.Reach (fillInputs pos x)
      (embed (fillInputs pos x) C) := by
    rintro x C ⟨σ, run⟩
    exact ⟨σ.map (Fin.castLE le), by rw [← embed_initial pos x]; exact embed_run _ run⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x C reach i j v w hv hw
    rw [restrict_decision (fillInputs pos x)] at hv hw
    exact S.agreement _ _ (reachEmbed x C reach) _ _ v w hv hw
  · intro x C reach i v hv
    rw [restrict_decision (fillInputs pos x)] at hv
    obtain ⟨k, hk⟩ := S.validity _ _ (reachEmbed x C reach) _ v hv
    by_cases hkm : k.val < m
    · exact ⟨⟨k.val, hkm⟩, by simp [fillInputs, hkm] at hk; exact hk⟩
    · exact ⟨⟨0, pos⟩, by simp [fillInputs, hkm] at hk; exact hk⟩
  · intro x σ c start exec i often
    have exec' : P.Execution (fun t => Fin.castLE le (σ t)) (fun t => embed (fillInputs pos x) (c t)) :=
      fun t => embed_step _ (exec t)
    have often' : InfinitelyOften (fun t => Fin.castLE le (σ t)) (Fin.castLE le i) := by
      intro N
      obtain ⟨t, ht, hσ⟩ := often N
      exact ⟨t, ht, by simp [hσ]⟩
    obtain ⟨t, ht⟩ := S.waitFree (fillInputs pos x) _ _ (by rw [start, embed_initial]) exec' _ often'
    exact ⟨t, by rw [restrict_decision (fillInputs pos x)]; exact ht⟩

end Protocol

/-- **Fewer processes are easier**: consensus solvable for `n` processes is solvable for any
`m ≤ n`. -/
theorem Solvable.mono {T : ObjectType} {n m : ℕ} {V : Type} (solvable : Solvable T n V)
    (le : m ≤ n) : Solvable T m V := by
  obtain ⟨P, S⟩ := solvable
  rcases Nat.eq_zero_or_pos m with rfl | pos
  · exact solvable_of_le_one T P.init (by omega) V
  · exact ⟨P.restrict le, S.restrict pos⟩

/-- **Every object with at least one state has a consensus number.** -/
theorem hasConsensusNumber_of_nonempty (T : ObjectType) [inst : Nonempty T.State] :
    ∃ k, HasConsensusNumber T k := by
  classical
  by_cases all : ∀ n, Solvable T n Bool
  · exact ⟨⊤, fun n => ⟨fun _ => le_top, fun _ => all n⟩⟩
  · push Not at all
    have hN : ¬ Solvable T (Nat.find all) Bool := Nat.find_spec all
    have below : ∀ n, n < Nat.find all → Solvable T n Bool := fun n hn => by
      have := Nat.find_min all hn
      push Not at this
      exact this
    have pos : 0 < Nat.find all := by
      by_contra zero
      have : Nat.find all = 0 := by omega
      rw [this] at hN
      exact hN (solvable_of_le_one T (Classical.choice inst) (by omega) Bool)
    refine ⟨((Nat.find all - 1 : ℕ) : ℕ∞), fun n => ⟨fun hs => ?_, fun hn => ?_⟩⟩
    · have lt : n < Nat.find all := by
        by_contra ge
        exact hN (hs.mono (by omega))
      exact_mod_cast (show n ≤ Nat.find all - 1 by omega)
    · have : n ≤ Nat.find all - 1 := by exact_mod_cast hn
      exact below n (by omega)

/-- **An object with no state has no consensus number**: no protocol can start. -/
theorem not_hasConsensusNumber_of_isEmpty (T : ObjectType) [IsEmpty T.State] (k : ℕ∞) :
    ¬ HasConsensusNumber T k := by
  intro h
  unfold HasConsensusNumber at h
  obtain ⟨P, -⟩ := (h 0).mpr (by simp)
  exact IsEmpty.false P.init

/-- **An object has a consensus number exactly when it has a state.** -/
theorem hasConsensusNumber_iff (T : ObjectType) : (∃ k, HasConsensusNumber T k) ↔ Nonempty T.State := by
  constructor
  · rintro ⟨k, h⟩
    unfold HasConsensusNumber at h
    obtain ⟨P, -⟩ := (h 0).mpr (by simp)
    exact ⟨P.init⟩
  · intro inst
    exact hasConsensusNumber_of_nonempty T

namespace Controls

/-- An object with no state. -/
def stateless : ObjectType := ⟨Empty, Unit, Unit, fun _ _ _ _ => True⟩

/-- **Control**: an object with no state has no consensus number. -/
theorem stateless_has_none : ¬ ∃ k, HasConsensusNumber stateless k := by
  rw [hasConsensusNumber_iff]
  rintro ⟨s⟩
  exact s.elim

/-- **Positive control**: deciding one's own input, restricted to the first of two processes, is a
one-process consensus protocol. -/
theorem restrict_keeps_agreement :
    ((ownInput unitObject () 2 Bool).restrict (m := 1) (by omega)).Solves := by
  have := ownInput_solves_one
  refine ⟨?_, ?_, ?_⟩
  · intro x C reach i j v w hv hw
    obtain rfl : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
    exact Option.some.inj (hv.symm.trans hw)
  · rintro x C ⟨σ, run⟩ i v hv
    refine ⟨i, ?_⟩
    have stays : ∀ (σ : List (Fin 1)) (C D : ((ownInput unitObject () 2 Bool).restrict
        (m := 1) (by omega)).Config), Protocol.Run _ C σ D → D = C := by
      intro σ
      induction σ with
      | nil => intro C D run; exact run
      | cons k σ ih =>
          intro C D run
          obtain ⟨E, step, rest⟩ := run
          rw [ih E D rest]
          exact step.eq_of_decide rfl
    rw [stays σ _ _ run] at hv
    exact Option.some.inj hv
  · intro x σ c start _ i _
    exact ⟨0, by rw [start]; rfl⟩

end Controls

end Mettapedia.GSLT.Coordination.ConsensusNumbers
