import Mettapedia.Machines.OccurrenceMachine
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Reconvergent frontiers: merging equal configurations keeps the answer bag

A depth-first search visits one root-to-leaf path at a time, so its work is at
least the number of paths. A frontier is a bag of configurations; advancing it
replaces every non-final configuration by its successor occurrences. Since the
observation is a bag, a frontier may hold one configuration with weight `w` in
place of `w` equal copies: the weight is the multiplicity.

* `frontierAnswers_eq_bind`: advancing a frontier round by round answers
  exactly the answer bags (`answerBag`) of its configurations, multiplicity
  included.
* `KeySimulation`, `answerBag_eq_keyBag`: a key that forgets only what no later
  step reads gives equal answer bags to configurations with equal keys.
* `merged_answers`: the answers of a frontier are a sum over its distinct keys,
  each key's bag taken once and scaled by the number of configurations with
  that key.

Controls: merging as a set loses answer occurrences (`dedup_loses_occurrences`),
and a key that forgets a value a later step reads admits no key simulation
(`no_simulation_forgetting_live`).

The counting family (`Fanout`): `w` choices at each of `k` levels with an
accumulator kept modulo `m`. After `t ≤ k` rounds the unmerged frontier holds
`w ^ t` configurations (`card_round`), while their keys take at most `m`
values (`card_keys_round_le`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ReconvergentFrontier

open Mettapedia.Machines
open Mettapedia.Machines.OccurrenceMachineCore

variable {Term State Answer Key : Type}

/-! ## Round-synchronous evaluation -/

/-- Answer occurrences a frontier exposes now. -/
def emitted (M : OccurrenceMachineCore Term State Answer) (F : Multiset State) :
    Multiset Answer :=
  F.bind fun s => ((M.answer s).toList : Multiset Answer)

/-- Every non-final configuration is replaced by its successor occurrences. -/
def advance (M : OccurrenceMachineCore Term State Answer) (F : Multiset State) :
    Multiset State :=
  F.bind fun s => if (M.answer s).isSome then 0 else (M.next s : Multiset State)

/-- Round-synchronous evaluation of a frontier with `fuel` rounds. -/
def frontierAnswers (M : OccurrenceMachineCore Term State Answer) :
    Nat → Multiset State → Multiset Answer
  | 0, F => emitted M F
  | fuel + 1, F => emitted M F + frontierAnswers M fuel (advance M F)

theorem answerBag_zero (M : OccurrenceMachineCore Term State Answer) (s : State) :
    M.answerBag 0 s = ((M.answer s).toList : Multiset Answer) := rfl

theorem answerBag_succ_of_answer (M : OccurrenceMachineCore Term State Answer)
    (fuel : Nat) (s : State) (a : Answer) (h : M.answer s = some a) :
    M.answerBag (fuel + 1) s = {a} := by
  simp [answerBag, answerOccurrences, h]

theorem answerBag_succ_of_none (M : OccurrenceMachineCore Term State Answer)
    (fuel : Nat) (s : State) (h : M.answer s = none) :
    M.answerBag (fuel + 1) s =
      (M.next s : Multiset State).bind (M.answerBag fuel) := by
  simp only [answerBag, answerOccurrences, h]
  exact (Multiset.coe_bind _ _).symm

/-- Advancing a frontier round by round is exact: it answers the bag of every
configuration in it, with multiplicity. -/
theorem frontierAnswers_eq_bind (M : OccurrenceMachineCore Term State Answer) :
    ∀ (fuel : Nat) (F : Multiset State),
      frontierAnswers M fuel F = F.bind (M.answerBag fuel)
  | 0, F => rfl
  | fuel + 1, F => by
      rw [frontierAnswers, frontierAnswers_eq_bind M fuel, emitted, advance,
        Multiset.bind_assoc, ← Multiset.bind_add]
      apply Multiset.bind_congr
      intro s _
      cases h : M.answer s with
      | none =>
          rw [answerBag_succ_of_none M fuel s h]
          simp
      | some a =>
          rw [answerBag_succ_of_answer M fuel s a h]
          simp

/-! ## Merging by a key -/

/-- A key forgets only what no later step reads: configurations with equal keys
have equal answers, and their successors have equal keys, occurrence for
occurrence. -/
structure KeySimulation (M : OccurrenceMachineCore Term State Answer)
    (key : State → Key) where
  answerOf : Key → Option Answer
  nextOf : Key → Multiset Key
  answer_eq : ∀ s, M.answer s = answerOf (key s)
  next_eq : ∀ s, (M.next s : Multiset State).map key = nextOf (key s)

namespace KeySimulation

variable {M : OccurrenceMachineCore Term State Answer} {key : State → Key}

/-- The answer bag of a key. -/
def keyBag (S : KeySimulation M key) : Nat → Key → Multiset Answer
  | 0, k => ((S.answerOf k).toList : Multiset Answer)
  | fuel + 1, k =>
      match S.answerOf k with
      | some a => {a}
      | none => (S.nextOf k).bind (S.keyBag fuel)

/-- Configurations with equal keys have equal answer bags. -/
theorem answerBag_eq_keyBag (S : KeySimulation M key) :
    ∀ (fuel : Nat) (s : State), M.answerBag fuel s = S.keyBag fuel (key s)
  | 0, s => by
      rw [answerBag_zero, S.answer_eq s]
      rfl
  | fuel + 1, s => by
      cases h : M.answer s with
      | none =>
          have hk : S.answerOf (key s) = none := (S.answer_eq s).symm.trans h
          rw [answerBag_succ_of_none M fuel s h, keyBag, hk]
          simp only []
          rw [← S.next_eq s, Multiset.bind_map]
          exact Multiset.bind_congr (fun s' _ => answerBag_eq_keyBag S fuel s')
      | some a =>
          have hk : S.answerOf (key s) = some a := (S.answer_eq s).symm.trans h
          rw [answerBag_succ_of_answer M fuel s a h, keyBag, hk]

/-- A frontier may be replaced by its keys. -/
theorem bind_answerBag_eq_bind_keyBag (S : KeySimulation M key) (fuel : Nat)
    (F : Multiset State) :
    F.bind (M.answerBag fuel) = (F.map key).bind (S.keyBag fuel) := by
  rw [Multiset.bind_map]
  exact Multiset.bind_congr (fun s _ => S.answerBag_eq_keyBag fuel s)

end KeySimulation

/-- Binding a fixed continuation is additive in the frontier. -/
def bindHom (g : Key → Multiset Answer) : Multiset Key →+ Multiset Answer where
  toFun m := m.bind g
  map_zero' := Multiset.zero_bind g
  map_add' s t := Multiset.add_bind s t g

/-- A bag of keys is its distinct keys with their counts as weights. -/
theorem bind_eq_sum_count_nsmul [DecidableEq Key] (m : Multiset Key)
    (g : Key → Multiset Answer) :
    m.bind g = ∑ k ∈ m.toFinset, m.count k • g k := by
  conv_lhs => rw [← Multiset.toFinset_sum_count_nsmul_eq m]
  change bindHom g (∑ k ∈ m.toFinset, m.count k • ({k} : Multiset Key)) = _
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_nsmul]
  simp [bindHom]

/-- The merged frontier: each distinct key's answer bag is computed once and
scaled by its weight, the number of configurations with that key. -/
theorem merged_answers [DecidableEq Key] {M : OccurrenceMachineCore Term State Answer}
    {key : State → Key} (S : KeySimulation M key) (fuel : Nat) (F : Multiset State) :
    F.bind (M.answerBag fuel) =
      ∑ k ∈ (F.map key).toFinset, (F.map key).count k • S.keyBag fuel k := by
  rw [S.bind_answerBag_eq_bind_keyBag, bind_eq_sum_count_nsmul]

/-! ## Controls -/

/-- A root with two equal successor occurrences, each answering `0`. -/
def twinMachine : OccurrenceMachineCore Unit Bool Nat where
  load _ := false
  next s := if s then [] else [true, true]
  answer s := if s then some 0 else none
  answer_final := by
    intro s a h
    cases s <;> simp_all

theorem twinMachine_answers : twinMachine.answerBag 1 false = {0, 0} := by
  simp [answerBag, answerOccurrences, twinMachine]
  rfl

/-- Merging a frontier as a set drops an answer occurrence. -/
theorem dedup_loses_occurrences :
    (({true, true} : Multiset Bool).dedup).bind (twinMachine.answerBag 0) ≠
      ({true, true} : Multiset Bool).bind (twinMachine.answerBag 0) := by
  intro h
  have hc := congrArg Multiset.card h
  simp [twinMachine, answerBag, answerOccurrences] at hc

/-- A value chosen at step `0` and answered at step `1`. -/
def choiceMachine : OccurrenceMachineCore Unit (Nat × Nat) Nat where
  load _ := (0, 0)
  next s := if s.1 = 0 then [(1, 0), (1, 1)] else []
  answer s := if s.1 = 1 then some s.2 else none
  answer_final := by
    intro s a h
    by_cases h1 : s.1 = 1
    · simp [h1]
    · simp [h1] at h

/-- Forgetting the chosen value, which step `1` reads, admits no key simulation. -/
theorem no_simulation_forgetting_live :
    IsEmpty (KeySimulation choiceMachine (fun s : Nat × Nat => s.1)) := by
  constructor
  intro S
  have h0 := S.answer_eq (1, 0)
  have h1 := S.answer_eq (1, 1)
  simp only [choiceMachine] at h0 h1
  rw [← h0] at h1
  simp at h1

/-! ## The counting family -/

namespace Fanout

/-- The accumulator `7 * a + c` modulo `m`, over the choices made so far. -/
def acc (m : Nat) (s : List Nat) : Nat :=
  s.foldl (fun a c => (7 * a + c) % m) 0

/-- Choose one of `w` values at each of `k` levels; answer the accumulator. -/
def machine (w k m : Nat) : OccurrenceMachineCore Unit (List Nat) Nat where
  load _ := []
  next s := if s.length < k then (List.range w).map (fun c => s ++ [c]) else []
  answer s := if s.length = k then some (acc m s) else none
  answer_final := by
    intro s a h
    by_cases hk : s.length = k
    · simp [hk]
    · simp [hk] at h

/-- The key keeps the level and the accumulator, and forgets the path. -/
def key (m : Nat) (s : List Nat) : Nat × Nat := (s.length, acc m s)

theorem acc_snoc (m : Nat) (s : List Nat) (c : Nat) :
    acc m (s ++ [c]) = (7 * acc m s + c) % m := by
  simp [acc, List.foldl_append]

/-- The key is a simulation: the path does not matter to the future. -/
def simulation (w k m : Nat) : KeySimulation (machine w k m) (key m) where
  answerOf p := if p.1 = k then some p.2 else none
  nextOf p := if p.1 < k then
      (((List.range w).map (fun c => (p.1 + 1, (7 * p.2 + c) % m)) : List (Nat × Nat)) :
        Multiset (Nat × Nat))
    else 0
  answer_eq _ := rfl
  next_eq s := by
    by_cases hk : s.length < k
    · have hl : (key m s).1 < k := hk
      simp only [machine, hk, hl, if_true, Multiset.map_coe, List.map_map]
      congr 1
      apply List.map_congr_left
      intro c _
      simp [key, acc_snoc]
    · have hl : ¬ (key m s).1 < k := hk
      simp only [machine, hk, hl, if_false]
      simp

/-- The frontier after `t` rounds from the empty path. -/
def round (w k m : Nat) (t : Nat) : Multiset (List Nat) :=
  (advance (machine w k m))^[t] {[]}

theorem length_of_mem_round (w k m : Nat) :
    ∀ (t : Nat), t ≤ k → ∀ s ∈ round w k m t, s.length = t
  | 0, _, s, hs => by
      simp [round] at hs
      simp [hs]
  | t + 1, ht, s, hs => by
      have hprev := length_of_mem_round w k m t (Nat.le_of_succ_le ht)
      simp only [round, Function.iterate_succ_apply'] at hs
      simp only [advance, Multiset.mem_bind] at hs
      obtain ⟨p, hp, hs⟩ := hs
      have hpl : p.length = t := hprev p hp
      have hlt : p.length < k := by omega
      have hne : p.length ≠ k := by omega
      simp [machine, hne, hlt] at hs
      obtain ⟨c, _, rfl⟩ := hs
      simp [hpl]

/-- The unmerged frontier holds `w ^ t` configurations after `t ≤ k` rounds. -/
theorem card_round (w k m : Nat) :
    ∀ (t : Nat), t ≤ k → Multiset.card (round w k m t) = w ^ t
  | 0, _ => by simp [round]
  | t + 1, ht => by
      have hprev := card_round w k m t (Nat.le_of_succ_le ht)
      have hlen := length_of_mem_round w k m t (Nat.le_of_succ_le ht)
      have hround : round w k m (t + 1) = advance (machine w k m) (round w k m t) := by
        simp only [round, Function.iterate_succ_apply']
      rw [hround, advance, Multiset.card_bind]
      have hconst : ∀ s ∈ round w k m t,
          (Multiset.card ∘ fun s => if ((machine w k m).answer s).isSome then 0
            else (((machine w k m).next s : List (List Nat)) : Multiset (List Nat))) s = w := by
        intro s hs
        have hl : s.length = t := hlen s hs
        have hlt : s.length < k := by omega
        have hne : s.length ≠ k := by omega
        simp [machine, hne, hlt]
      rw [Multiset.map_congr rfl hconst, Multiset.map_const', Multiset.sum_replicate, hprev]
      simp [pow_succ]

/-- The merged frontier after `t` rounds has at most `m` keys. -/
theorem card_keys_round_le (w k m : Nat) (hm : 0 < m) (t : Nat) (ht : t ≤ k) :
    ((round w k m t).map (key m)).toFinset.card ≤ m := by
  have hsub : ((round w k m t).map (key m)).toFinset ⊆
      (Finset.range m).image (fun a => (t, a)) := by
    intro p hp
    simp only [Multiset.mem_toFinset, Multiset.mem_map] at hp
    obtain ⟨s, hs, rfl⟩ := hp
    have hl := length_of_mem_round w k m t ht s hs
    simp only [Finset.mem_image, Finset.mem_range]
    refine ⟨acc m s, ?_, ?_⟩
    · cases s using List.reverseRecOn with
      | nil => simp [acc, hm]
      | append_singleton s c _ =>
          rw [acc_snoc]
          exact Nat.mod_lt _ hm
    · simp [key, hl]
  calc ((round w k m t).map (key m)).toFinset.card
      ≤ ((Finset.range m).image (fun a => (t, a))).card := Finset.card_le_card hsub
    _ ≤ (Finset.range m).card := Finset.card_image_le
    _ = m := Finset.card_range m

end Fanout

end Mettapedia.Machines.ReconvergentFrontier
