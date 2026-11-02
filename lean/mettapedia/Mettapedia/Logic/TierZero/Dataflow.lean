import Mettapedia.Logic.TierZero.Kernel

/-!
# The dataflow kernel: any schedule, one verdict

The MeTTa kernel `tier0.metta` fires a proof's nodes in any order: a node fires as soon as the
theorems its children name exist. This file proves that the order does not matter and that the
dataflow kernel accepts exactly what the sequential kernel accepts.

* A node is **fireable** at a set `S` of fired nodes when its rule instance exists and its premises
  discharge against the hypotheses and the conclusions of `S` (`Fireable`). A **dataflow step**
  fires one fireable node (`DStep`).
* A node is **valid** when it belongs to every set closed under firing (`Valid`): the least such set.
* `reach_valid`: everything a dataflow run fires is valid. `quiescent_contains_valid`: a state where
  nothing more can fire contains every valid node. So every run that stops ends at the same state,
  the valid nodes (`final_eq_valid`): the verdict is a function of the proof (INV-006 of the spec),
  whatever the schedule.
* The dataflow acceptance reads the claim in full: every node fired, and the root names the goal
  (`DAccepts`). `daccepts_iff_derivable`: some proof is accepted exactly for the derivable
  judgments, the same set as the sequential kernel's (`check_iff_derivable`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero

universe u

variable {P : Presentation.{u}} [DecidableEq P.J]

section Dataflow

variable (hyps : List P.J) (nodes : List (Node P))

/-- The conclusion a node would have. -/
def concl (n : ℕ) : Option P.J :=
  match nodes[n]? with
  | none => none
  | some (r, a, _) => (P.inst r a).map Prod.snd

/-- Children name hypotheses, and fired nodes by their conclusions. -/
def lookupAt (S : Finset ℕ) : Kid → Option P.J
  | .hyp i => hyps[i]?
  | .node m => if m ∈ S then concl nodes m else none

/-- A node can fire at `S`. -/
def Fireable (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ r a kids ps c, nodes[n]? = some (r, a, kids) ∧ P.inst r a = some (ps, c) ∧
    discharge (lookupAt hyps nodes S) ps kids = true

/-- One dataflow step: a fireable node that has not fired fires. -/
def DStep (S T : Finset ℕ) : Prop := ∃ n ∉ S, Fireable hyps nodes S n ∧ T = insert n S

/-- A set closed under firing. -/
def ClosedSet (S : Finset ℕ) : Prop := ∀ n, Fireable hyps nodes S n → n ∈ S

/-- A valid node: in every set closed under firing. -/
def Valid (n : ℕ) : Prop := ∀ S, ClosedSet hyps nodes S → n ∈ S

/-- The dataflow acceptance: every node fired (nothing of the claim is left: the full read), and
the root names the goal. By `final_eq_valid` this does not depend on the schedule. -/
def DAccepts (root : Kid) (goal : P.J) : Prop :=
  (∀ n < nodes.length, Valid hyps nodes n) ∧
    match root with
    | .hyp i => hyps[i]? = some goal
    | .node m => m < nodes.length ∧ concl nodes m = some goal

variable {hyps nodes}

/-- Discharging with a lookup that agrees wherever the first one answers. -/
theorem discharge_mono {look look' : Kid → Option P.J}
    (agree : ∀ k p, look k = some p → look' k = some p) :
    ∀ (ps : List P.J) (kids : List Kid), discharge look ps kids = true → discharge look' ps kids = true
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [discharge] at h
  | p :: ps, kids, h => by
      by_cases sp : P.side p = true
      · simp only [discharge, sp, ↓reduceIte] at h ⊢
        exact discharge_mono agree ps kids h
      · have sp' : P.side p = false := by simpa using sp
        cases kids with
        | nil => simp [discharge, sp'] at h
        | cons k ks =>
            simp only [discharge, sp', Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
              decide_eq_true_eq] at h ⊢
            exact ⟨agree k p h.1, discharge_mono agree ps ks h.2⟩

omit [DecidableEq P.J] in
theorem lookupAt_mono {S T : Finset ℕ} (sub : S ⊆ T) :
    ∀ k p, lookupAt hyps nodes S k = some p → lookupAt hyps nodes T k = some p := by
  intro k p h
  cases k with
  | hyp i => exact h
  | node m =>
      simp only [lookupAt] at h ⊢
      by_cases hm : m ∈ S
      · simp only [hm, ↓reduceIte] at h
        simp [sub hm, h]
      · simp [hm] at h

theorem fireable_mono {S T : Finset ℕ} (sub : S ⊆ T) {n : ℕ} (h : Fireable hyps nodes S n) :
    Fireable hyps nodes T n := by
  obtain ⟨r, a, kids, ps, c, hn, hi, hd⟩ := h
  exact ⟨r, a, kids, ps, c, hn, hi, discharge_mono (lookupAt_mono sub) ps kids hd⟩

/-- A node fireable at a set of valid nodes is valid. -/
theorem valid_of_fireable {S : Finset ℕ} (allValid : ∀ m ∈ S, Valid hyps nodes m) {n : ℕ}
    (h : Fireable hyps nodes S n) : Valid hyps nodes n := by
  intro T closed
  exact closed n (fireable_mono (fun m hm => allValid m hm T closed) h)

/-- **Everything a dataflow run fires is valid.** -/
theorem reach_valid {S : Finset ℕ} (reach : Relation.ReflTransGen (DStep hyps nodes) ∅ S) :
    ∀ m ∈ S, Valid hyps nodes m := by
  induction reach with
  | refl => simp
  | tail _ step ih =>
      obtain ⟨n, -, fire, rfl⟩ := step
      intro m hm
      rcases Finset.mem_insert.mp hm with rfl | hm'
      · exact valid_of_fireable ih fire
      · exact ih m hm'

/-- A quiescent state, where nothing more can fire, is closed, so it contains every valid node. -/
theorem quiescent_contains_valid {S : Finset ℕ}
    (quiet : ∀ n, Fireable hyps nodes S n → n ∈ S) {n : ℕ} (h : Valid hyps nodes n) : n ∈ S :=
  h S quiet

/-- **One verdict for every schedule**: a dataflow run that stops has fired exactly the valid
nodes. -/
theorem final_eq_valid {S : Finset ℕ} (reach : Relation.ReflTransGen (DStep hyps nodes) ∅ S)
    (quiet : ∀ n, Fireable hyps nodes S n → n ∈ S) (n : ℕ) : n ∈ S ↔ Valid hyps nodes n :=
  ⟨reach_valid reach n, quiescent_contains_valid quiet⟩

/-- Valid nodes conclude derivable judgments. -/
theorem valid_derivable {n : ℕ} (h : Valid hyps nodes n) :
    ∃ c, concl nodes n = some c ∧ Derivable P hyps c := by
  classical
  -- the set of nodes (among those listed) whose conclusion is derivable is closed under firing
  let good : Finset ℕ := (Finset.range nodes.length).filter fun m =>
    ∃ c, concl nodes m = some c ∧ Derivable P hyps c
  have closed : ClosedSet hyps nodes good := by
    intro m ⟨r, a, kids, ps, c, hm, hi, hd⟩
    have inRange : m < nodes.length := by
      by_contra hge
      simp [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hm
    have premises : ∀ p ∈ ps, P.side p = false → Derivable P hyps p := by
      have doneOk : ∀ k q, lookupAt hyps nodes good k = some q → Derivable P hyps q := by
        intro k q hk
        cases k with
        | hyp i => exact Derivable.hyp (List.mem_of_getElem? hk)
        | node m' =>
            simp only [lookupAt] at hk
            by_cases hm' : m' ∈ good
            · simp only [hm', ↓reduceIte] at hk
              obtain ⟨-, c', hc', hd'⟩ := Finset.mem_filter.mp hm'
              rw [hc'] at hk; cases hk; exact hd'
            · simp [hm'] at hk
      -- discharge soundness against an arbitrary lookup of derivable judgments
      have gen : ∀ (ps : List P.J) (kids : List Kid),
          discharge (lookupAt hyps nodes good) ps kids = true →
            ∀ p ∈ ps, P.side p = false → Derivable P hyps p := by
        intro ps
        induction ps with
        | nil => intro kids _ p mem; simp at mem
        | cons p ps ih =>
            intro kids hdis q mem notSide
            by_cases sp : P.side p = true
            · have rest : discharge (lookupAt hyps nodes good) ps kids = true := by
                simpa [discharge, sp] using hdis
              rcases List.mem_cons.mp mem with rfl | mem'
              · rw [sp] at notSide; cases notSide
              · exact ih kids rest q mem' notSide
            · have sp' : P.side p = false := by simpa using sp
              cases kids with
              | nil => simp [discharge, sp'] at hdis
              | cons k ks =>
                  simp only [discharge, sp', Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
                    decide_eq_true_eq] at hdis
                  rcases List.mem_cons.mp mem with rfl | mem'
                  · exact doneOk k _ hdis.1
                  · exact ih ks hdis.2 q mem' notSide
      exact gen ps kids hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr inRange, c, ?_, Derivable.rule hi premises⟩
    simp [concl, hm, hi]
  obtain ⟨-, rest⟩ := Finset.mem_filter.mp (h good closed)
  exact rest

/-- A dataflow-accepted claim is derivable. -/
theorem daccepts_sound {root : Kid} {goal : P.J} (h : DAccepts hyps nodes root goal) :
    Derivable P hyps goal := by
  obtain ⟨allValid, hroot⟩ := h
  cases root with
  | hyp i => exact Derivable.hyp (List.mem_of_getElem? hroot)
  | node m =>
      obtain ⟨hm, hc⟩ := hroot
      obtain ⟨c, hc', hd⟩ := valid_derivable (allValid m hm)
      rw [hc] at hc'; cases hc'; exact hd

/-- A successful sequential walk fires every node validly, in order. -/
theorem run_valid :
    ∀ (k : ℕ) (done : List P.J) (out : List P.J),
      done.length = k → (∀ i < k, done[i]? = concl nodes i) → (∀ i < k, Valid hyps nodes i) →
      run hyps done (nodes.drop k) = some out →
        (∀ i < nodes.length, Valid hyps nodes i) ∧ (∀ i < nodes.length, out[i]? = concl nodes i)
  := by
  intro k
  induction h : nodes.length - k generalizing k with
  | zero =>
      intro done out hlen hdone hvalid hrun
      have hk : nodes.length ≤ k := by omega
      rw [List.drop_eq_nil_of_le hk] at hrun
      simp only [run, Option.some.injEq] at hrun
      subst hrun
      exact ⟨fun i hi => hvalid i (by omega), fun i hi => hdone i (by omega)⟩
  | succ d ih =>
      intro done out hlen hdone hvalid hrun
      have hk : k < nodes.length := by omega
      rw [List.drop_eq_getElem_cons hk] at hrun
      rcases hnk : nodes[k] with ⟨r, a, kids⟩
      rw [hnk] at hrun
      simp only [run] at hrun
      cases hi : P.inst r a with
      | none => simp [hi] at hrun
      | some pc =>
          obtain ⟨ps, c⟩ := pc
          simp only [hi] at hrun
          by_cases hd : discharge (lookup hyps done) ps kids = true
          · simp only [hd, ↓reduceIte] at hrun
            have hnode : nodes[k]? = some (r, a, kids) := by
              rw [List.getElem?_eq_getElem hk, hnk]
            -- the walk's lookup agrees with the dataflow lookup at the earlier nodes
            have agree : ∀ kid p, lookup hyps done kid = some p →
                lookupAt hyps nodes (Finset.range k) kid = some p := by
              intro kid p hl
              cases kid with
              | hyp i => exact hl
              | node m =>
                  simp only [lookup] at hl
                  have hm : m < k := by
                    by_contra hge
                    rw [List.getElem?_eq_none (by omega)] at hl; cases hl
                  simp only [lookupAt, Finset.mem_range, hm, ↓reduceIte]
                  rw [← hdone m hm]; exact hl
            have fire : Fireable hyps nodes (Finset.range k) k :=
              ⟨r, a, kids, ps, c, hnode, hi, discharge_mono agree ps kids hd⟩
            have validK : Valid hyps nodes k :=
              valid_of_fireable (fun m hm => hvalid m (Finset.mem_range.mp hm)) fire
            have hconcl : concl nodes k = some c := by simp [concl, hnode, hi]
            refine ih (k + 1) (by omega) (done ++ [c]) out (by simp [hlen]) ?_ ?_ hrun
            · intro i hi'
              rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt | rfl
              · rw [List.getElem?_append_left (by omega)]; exact hdone i hlt
              · rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]; simp [hconcl]
            · intro i hi'
              rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt | rfl
              · exact hvalid i hlt
              · exact validK
          · simp [hd] at hrun

/-- The walk adds one conclusion per node. -/
theorem run_length :
    ∀ (done : List P.J) (proof : List (Node P)) (out : List P.J),
      run hyps done proof = some out → out.length = done.length + proof.length
  | done, [], out, h => by simp only [run, Option.some.injEq] at h; subst h; simp
  | done, (r, a, kids) :: rest, out, h => by
      simp only [run] at h
      cases hi : P.inst r a with
      | none => simp [hi] at h
      | some pc =>
          obtain ⟨ps, c⟩ := pc
          simp only [hi] at h
          by_cases hd : discharge (lookup hyps done) ps kids = true
          · simp only [hd, ↓reduceIte] at h
            have := run_length (done ++ [c]) rest out h
            simp at this; simp; omega
          · simp [hd] at h

/-- **The dataflow kernel accepts the same judgments as the sequential kernel**: some proof is
accepted exactly for the derivable judgments. -/
theorem daccepts_iff_derivable (goal : P.J) :
    (∃ (proof : List (Node P)) (root : Kid), DAccepts hyps proof root goal) ↔
      Derivable P hyps goal := by
  constructor
  · rintro ⟨proof, root, h⟩
    exact daccepts_sound h
  · intro h
    obtain ⟨proof, root, out, hrun, hlook⟩ := derivable_proves h
    have both := run_valid (nodes := proof) (hyps := hyps) 0 [] out rfl (by simp) (by simp)
      (by simpa using hrun)
    refine ⟨proof, root, both.1, ?_⟩
    cases root with
    | hyp i => exact hlook
    | node m =>
        simp only [lookup] at hlook
        have hm : m < proof.length := by
          have hlen := run_length (hyps := hyps) [] proof out hrun
          by_contra hge
          rw [List.getElem?_eq_none (by simp at hlen; omega)] at hlook
          cases hlook
        exact ⟨hm, (both.2 m hm).symm.trans hlook⟩

end Dataflow

end Mettapedia.Logic.TierZero
