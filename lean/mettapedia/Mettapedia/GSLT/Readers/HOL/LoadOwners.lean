import Mettapedia.GSLT.Readers.HOL.Load

/-!
# The HOL loader's cut by owner

`Load.owners` assigns every record of HOL Light's ProofTrace record to the claim it is checked in.
This file proves, for every input record sequence:

* `owners_inference`: every inference record (not an axiom, definition or type definition) has an
  owner, and `owners_only_inference`: nothing else has one;
* `owners_root`: an owner is the record itself or a later record, and is its own owner: a claim's
  root. So every inference record is a node of the claim of its owner's root, and an owner is never a
  record that belongs to another claim.

Not proved here: that the builders then make one node per record (they are partial definitions,
run on the corpora; the node census of the report counts it).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.HOL.Load

/-- The cut's invariant once the records `m, m+1, …` have been visited (from the last). -/
structure OwnInv (steps : Array (Option PTStep)) (m : Nat) (st : OwnSt) : Prop where
  own_size : st.own.size = steps.size
  first_size : st.first.size = steps.size
  /-- an owner is set only for a visited record, is that record or a later one, and is a root -/
  own_ok : ∀ (j o : Nat), st.own[j]? = some (some o) → m ≤ j ∧ j ≤ o ∧ st.own[o]? = some (some o)
  /-- the claim of a premise's first user is a later record and a root -/
  first_ok : ∀ (p f : Nat), st.first[p]? = some (some f) → p < f ∧ st.own[f]? = some (some f)
  /-- every visited inference record has an owner -/
  visited : ∀ (j : Nat) (s : PTStep), m ≤ j → steps[j]? = some (some s) → isExtension s = false →
    ∃ o, st.own[j]? = some (some o)
  /-- owners only for inference records -/
  inference : ∀ (j o : Nat), st.own[j]? = some (some o) → ∃ s, steps[j]? = some (some s) ∧ isExtension s = false

theorem notePremise_own (o : Nat) (st : OwnSt) (p : Nat) : (notePremise o st p).own = st.own := by
  unfold notePremise
  split
  · rfl
  · split <;> rfl
  · rfl

theorem notePremise_first_size (o : Nat) (st : OwnSt) (p : Nat) :
    (notePremise o st p).first.size = st.first.size := by
  unfold notePremise
  split
  · simp
  · split <;> rfl
  · rfl

/-- Noting a premise below a root keeps every first user's claim a later record and a root. -/
theorem notePremise_firstOk (o : Nat) (st : OwnSt) (p : Nat) (hpo : p < o)
    (hroot : st.own[o]? = some (some o))
    (h : ∀ (q f : Nat), st.first[q]? = some (some f) → q < f ∧ st.own[f]? = some (some f)) :
    ∀ (q f : Nat), (notePremise o st p).first[q]? = some (some f) →
      q < f ∧ (notePremise o st p).own[f]? = some (some f) := by
  rw [notePremise_own]
  unfold notePremise
  split
  · intro q f hq
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hq
    by_cases hpq : p = q
    · subst hpq
      simp only [if_true] at hq
      split at hq
      · simp only [Option.some.injEq] at hq
        subst hq
        exact ⟨hpo, hroot⟩
      · simp at hq
    · simp only [hpq, if_false] at hq
      exact h q f hq
  · split
    · exact h
    · exact h
  · exact h

theorem foldl_notePremise (o : Nat) : ∀ (ps : List Nat) (st : OwnSt), (∀ p ∈ ps, p < o) →
    st.own[o]? = some (some o) →
    (∀ (q f : Nat), st.first[q]? = some (some f) → q < f ∧ st.own[f]? = some (some f)) →
    (ps.foldl (notePremise o) st).own = st.own ∧
      (ps.foldl (notePremise o) st).first.size = st.first.size ∧
      (∀ (q f : Nat), (ps.foldl (notePremise o) st).first[q]? = some (some f) →
        q < f ∧ (ps.foldl (notePremise o) st).own[f]? = some (some f))
  | [], _, _, _, h => ⟨rfl, rfl, h⟩
  | p :: ps, st, hlt, hroot, h => by
    have h1 := notePremise_firstOk o st p (hlt p (by simp)) hroot h
    have hown := notePremise_own o st p
    obtain ⟨e1, e2, e3⟩ := foldl_notePremise o ps (notePremise o st p)
      (fun q hq => hlt q (by simp [hq])) (by rw [hown]; exact hroot) h1
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.foldl_cons]; rw [e1, hown]
    · simp only [List.foldl_cons]; rw [e2, notePremise_first_size]
    · simpa only [List.foldl_cons] using e3

theorem earlierPremises_lt (s : PTStep) (i : Nat) : ∀ p ∈ earlierPremises s i, p < i := by
  intro p hp
  simpa [earlierPremises] using (List.mem_filter.mp hp).2

/-- Visiting record `i` keeps the invariant. -/
theorem ownStep_inv (steps : Array (Option PTStep)) (named : Nat → Bool) (forced : Array Bool)
    (i : Nat) (st : OwnSt) (h : OwnInv steps (i + 1) st) :
    OwnInv steps i (ownStep steps named forced st i) := by
  -- the record `i` itself has no owner yet
  have hnone : ∀ o, st.own[i]? ≠ some (some o) := by
    intro o ho
    have := (h.own_ok i o ho).1
    omega
  unfold ownStep
  split
  · next s hs =>
    by_cases hx : isExtension s = true
    · simp only [hx, if_true]
      refine ⟨h.own_size, h.first_size, fun j o hj => ?_, h.first_ok, fun j s' hj hs' hx' => ?_, h.inference⟩
      · obtain ⟨a, b, c⟩ := h.own_ok j o hj
        exact ⟨by omega, b, c⟩
      · rcases Nat.lt_or_ge j (i + 1) with hlt | hge
        · have hji : j = i := by omega
          subst hji
          rw [hs] at hs'
          cases hs'
          simp [hx] at hx'
        · exact h.visited j s' hge hs' hx'
    · have hx' : isExtension s = false := by simpa using hx
      simp only [hx', Bool.false_eq_true, if_false]
      -- the owner o of record i
      generalize ho : (if named i || (forced[i]?).getD false || (st.multi[i]?).getD false then i
        else ((st.first[i]?).join).getD i) = o
      have hio : i = o ∨ (i < o ∧ st.own[o]? = some (some o)) := by
        rw [← ho]
        split
        · exact Or.inl rfl
        · cases hf : st.first[i]? with
          | none => exact Or.inl rfl
          | some x =>
            cases x with
            | none => exact Or.inl rfl
            | some f =>
              have := h.first_ok i f hf
              simp only [Option.join]
              exact Or.inr ⟨this.1, this.2⟩
      have hisize : i < steps.size := by
        have : steps[i]?.isSome := by rw [hs]; rfl
        simpa using this
      -- after setting the owner of i
      let st1 : OwnSt := { st with own := st.own.set! i (some o) }
      have st1own : ∀ (j : Nat), j ≠ i → st1.own[j]? = st.own[j]? := by
        intro j hj
        simp [st1, Array.set!_eq_setIfInBounds, Ne.symm hj]
      have st1i : st1.own[i]? = some (some o) := by
        simp [st1, Array.set!_eq_setIfInBounds, h.own_size, hisize]
      have hroot1 : st1.own[o]? = some (some o) := by
        rcases hio with rfl | ⟨hlt, hr⟩
        · exact st1i
        · rw [st1own o (by omega)]; exact hr
      have hfirst1 : ∀ (q f : Nat), st1.first[q]? = some (some f) → q < f ∧ st1.own[f]? = some (some f) := by
        intro q f hq
        obtain ⟨a, b⟩ := h.first_ok q f hq
        have hfi : f ≠ i := by
          intro hfi
          subst hfi
          exact hnone _ b
        exact ⟨a, by rw [st1own f hfi]; exact b⟩
      have hle : i ≤ o := by rcases hio with rfl | ⟨hlt, _⟩ <;> omega
      obtain ⟨e1, e2, e3⟩ := foldl_notePremise o (earlierPremises s i) st1
        (fun p hp => by have := earlierPremises_lt s i p hp; omega) hroot1 hfirst1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [e1]; simp [st1, Array.set!_eq_setIfInBounds, h.own_size]
      · rw [e2]; exact h.first_size
      · intro j o' hj
        rw [e1] at hj ⊢
        by_cases hji : j = i
        · subst hji
          rw [st1i] at hj
          cases hj
          exact ⟨le_refl _, hle, hroot1⟩
        · rw [st1own j hji] at hj
          obtain ⟨a, b, c⟩ := h.own_ok j o' hj
          have : o' ≠ i := by omega
          exact ⟨by omega, b, by rw [st1own o' this]; exact c⟩
      · exact e3
      · intro j s' hj hs' hx''
        rw [e1]
        by_cases hji : j = i
        · subst hji; exact ⟨o, st1i⟩
        · obtain ⟨o', ho'⟩ := h.visited j s' (by omega) hs' hx''
          exact ⟨o', by rw [st1own j hji]; exact ho'⟩
      · intro j o' hj
        rw [e1] at hj
        by_cases hji : j = i
        · subst hji; exact ⟨s, hs, hx'⟩
        · rw [st1own j hji] at hj
          exact h.inference j o' hj
  · next hs =>
    refine ⟨h.own_size, h.first_size, fun j o hj => ?_, h.first_ok, fun j s' hj hs' hx' => ?_, h.inference⟩
    · obtain ⟨a, b, c⟩ := h.own_ok j o hj
      exact ⟨by omega, b, c⟩
    · rcases Nat.lt_or_ge j (i + 1) with hlt | hge
      · have hji : j = i := by omega
        subst hji
        exact absurd hs' (hs s')
      · exact h.visited j s' hge hs' hx'

theorem ownInv_init (steps : Array (Option PTStep)) :
    OwnInv steps steps.size
      ⟨Array.replicate steps.size none, Array.replicate steps.size false, Array.replicate steps.size none⟩ := by
  refine ⟨by simp, by simp, fun j o hj => ?_, fun p f hp => ?_, fun j s hj hs hx => ?_, fun j o hj => ?_⟩
  · simp [Array.getElem?_replicate] at hj
  · simp [Array.getElem?_replicate] at hp
  · have : steps[j]? = none := Array.getElem?_eq_none hj
    rw [this] at hs; cases hs
  · simp [Array.getElem?_replicate] at hj

theorem fold_ownInv (steps : Array (Option PTStep)) (named : Nat → Bool) (forced : Array Bool) :
    ∀ (k : Nat) (st : OwnSt), OwnInv steps k st →
      OwnInv steps 0 ((List.range k).reverse.foldl (ownStep steps named forced) st)
  | 0, st, h => by simpa using h
  | k + 1, st, h => by
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.foldl_cons]
    exact fold_ownInv steps named forced k _ (ownStep_inv steps named forced k st h)

theorem owners_inv (steps : Array (Option PTStep)) (named : Nat → Bool) :
    ∃ st : OwnSt, OwnInv steps 0 st ∧ owners steps named = st.own :=
  ⟨_, fold_ownInv steps named (forcedOf steps) steps.size _ (ownInv_init steps), rfl⟩

/-- **Every inference record has an owner.** -/
theorem owners_inference {steps : Array (Option PTStep)} {named : Nat → Bool} {i : Nat} {s : PTStep}
    (hs : steps[i]? = some (some s)) (hx : isExtension s = false) :
    ∃ o, (owners steps named)[i]? = some (some o) := by
  obtain ⟨st, hinv, heq⟩ := owners_inv steps named
  rw [heq]; exact hinv.visited i s (Nat.zero_le _) hs hx

/-- **Only inference records have owners** (axioms, definitions and type definitions are admissions). -/
theorem owners_only_inference {steps : Array (Option PTStep)} {named : Nat → Bool} {i o : Nat}
    (h : (owners steps named)[i]? = some (some o)) :
    ∃ s, steps[i]? = some (some s) ∧ isExtension s = false := by
  obtain ⟨st, hinv, heq⟩ := owners_inv steps named
  rw [heq] at h; exact hinv.inference i o h

/-- **An owner is the record itself or a later record, and a claim's root** (its own owner). -/
theorem owners_root {steps : Array (Option PTStep)} {named : Nat → Bool} {i o : Nat}
    (h : (owners steps named)[i]? = some (some o)) :
    i ≤ o ∧ (owners steps named)[o]? = some (some o) := by
  obtain ⟨st, hinv, heq⟩ := owners_inv steps named
  rw [heq] at h ⊢
  obtain ⟨_, b, c⟩ := hinv.own_ok i o h
  exact ⟨b, c⟩

/-! ## Each root's group -/

theorem groupsOf_fold (own : Array (Option Nat)) (o : Nat) : ∀ (k : Nat) (i : Nat),
    i ∈ (((List.range k).foldl (groupStep own) ({} : Std.HashMap Nat (Array Nat))).getD o #[]).toList ↔
      i < k ∧ own[i]? = some (some o)
  | 0, i => by simp
  | k + 1, i => by
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, groupStep]
    have ih := groupsOf_fold own o k i
    split
    · next o' heq =>
      rw [Std.HashMap.getD_insert]
      by_cases ho : o' = o
      · subst ho
        simp only [beq_self_eq_true, if_true, Array.toList_push, List.mem_append, List.mem_singleton]
        rw [ih]
        constructor
        · rintro (⟨hk, h⟩ | rfl)
          · exact ⟨by omega, h⟩
          · exact ⟨by omega, heq⟩
        · rintro ⟨hk, h⟩
          rcases Nat.lt_or_ge i k with hlt | hge
          · exact Or.inl ⟨hlt, h⟩
          · exact Or.inr (by omega)
      · have hne : (o' == o) = false := by simpa using ho
        simp only [hne, Bool.false_eq_true, if_false]
        rw [ih]
        constructor
        · rintro ⟨hk, h⟩; exact ⟨by omega, h⟩
        · rintro ⟨hk, h⟩
          rcases Nat.lt_or_ge i k with hlt | hge
          · exact ⟨hlt, h⟩
          · have hik : i = k := by omega
            subst hik
            rw [heq] at h
            simp only [Option.some.injEq] at h
            exact absurd h ho
    · next hnot =>
      rw [ih]
      constructor
      · rintro ⟨hk, h⟩; exact ⟨by omega, h⟩
      · rintro ⟨hk, h⟩
        rcases Nat.lt_or_ge i k with hlt | hge
        · exact ⟨hlt, h⟩
        · have hik : i = k := by omega
          subst hik
          exact absurd h (hnot o)

/-- **Each root's group holds exactly the records it owns**: the claim of `o` is built over these
records (`claimStep` takes `groups.getD o #[]`). -/
theorem mem_groupsOf (own : Array (Option Nat)) (o i : Nat) :
    i ∈ ((groupsOf own).getD o #[]).toList ↔ own[i]? = some (some o) := by
  unfold groupsOf
  rw [groupsOf_fold own o own.size i]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have : own[i]?.isSome := by rw [h]; rfl
    simpa using this

end Mettapedia.GSLT.Readers.HOL.Load
