import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchSpace
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Search policies and the library verbs

A **frontier machine** (`Space.step`) keeps the answers found so far, in discovery order, and the
pending entries: addressed items not yet looked at. A step looks at the first pending entry: an
answer is recorded, a state is replaced by its alternatives. A **policy** (`Policy`) only decides
where the alternatives go; it must place exactly them (`Policy.perm`). Depth-first puts them in
front (a stack), breadth-first behind (a queue). These are the only places an order is promised.

## Every policy is sound (`Covers`)

The machine keeps one invariant for every policy: every address of the tree is accounted for
exactly once, by a recorded answer, an expanded state, or a pending entry above it
(`covers_search`). Hence, for every policy and budget:

* the recorded answers are answers of the unbounded semantics, each once (`found_sound`,
  `found_nodup`); the outcome lies below a budgeted run in the information order
  (`outcome_le_run`);
* when nothing is pending, the recorded answers are all of them (`found_complete`), the tree has
  fewer states than the budget, and the outcome is the budgeted run itself
  (`outcome_eq_run_of_finished`).

## The verbs

* `within P k x`: the outcome after `k` steps, with its status (`within_le_approx`,
  `within_eq_approx_of_finished`).
* `take P n k x`: stop as soon as `n` answers are recorded. It is the machine stopped at an
  earlier budget (`take_eq_search`); it is **finished for its own contract** when it has `n`
  answers or nothing is pending, and in the first case that says nothing about the rest of the
  search (`take_finished_contract`, controls in `SearchControls`).
* `first P k x` is `take` with `n = 1`: a found answer is an answer (`first_sound`); no answer with
  nothing pending is a refutation (`first_refuted`).
* `all P x`: defined when some budget leaves nothing pending, and then it is the unbounded
  semantics (`mem_all`); its value does not depend on the policy (`all_eq_all`).
* **Policies.** Breadth-first is **fair**: every answer at finite depth is recorded at some budget
  (`bfs_complete`). Iterative deepening (`deepen`) runs the depth-bounded rounds `run d` and stops at
  the first finished one; that is the last round (`deepen_eq_run`), so it records every answer at
  depth at most its budget, in any order of alternatives (`mem_deepen`). Depth-first is not fair:
  on a left-recursive alternative it never records an answer that both other policies find
  (`SearchControls`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search

universe u v w

/-- **A policy**: where the alternatives of an expanded state go among the pending entries. It must
place exactly them. -/
structure Policy (E : Type w) where
  insert : List E → List E → List E
  perm : ∀ alternatives rest : List E, (insert alternatives rest).Perm (alternatives ++ rest)

namespace Policy

variable {E : Type w}

/-- **Depth-first**: the pending entries are a stack. -/
def dfs : Policy E := ⟨fun alternatives rest => alternatives ++ rest, fun _ _ => .refl _⟩

/-- **Breadth-first**: the pending entries are a queue. -/
def bfs : Policy E := ⟨fun alternatives rest => rest ++ alternatives, fun _ _ => List.perm_append_comm⟩

end Policy

/-- A configuration of the frontier machine. -/
structure Config (σ : Type u) (α : Type v) where
  found : List (List ℕ × α)
  pending : List (List ℕ × (α ⊕ σ))

namespace Config

variable {σ : Type u} {α : Type v}

/-- The status of a configuration: finished when nothing is pending. -/
def status (c : Config σ α) : Status :=
  match c.pending with
  | [] => .finished
  | _ :: _ => .cutOff

/-- The outcome of a configuration, with addresses. -/
def outcome (c : Config σ α) : Outcome (List ℕ × α) := ⟨c.found, c.status⟩

/-- The machine before any step. -/
def start (x : α ⊕ σ) : Config σ α := ⟨[], [([], x)]⟩

theorem status_eq_finished_iff (c : Config σ α) : c.status = .finished ↔ c.pending = [] := by
  unfold status
  split <;> simp_all

/-- Finished for the contract of `take n`: `n` answers recorded, or nothing pending. -/
def takeStatus (c : Config σ α) (n : ℕ) : Status :=
  if n ≤ c.found.length then .finished else c.status

end Config

namespace Space

variable {σ : Type u} {α : Type v} (S : Space σ α)

/-- The alternatives of the state at address `w`, addressed. -/
def children (w : List ℕ) (s : σ) : List (List ℕ × (α ⊕ σ)) :=
  (List.finRange (S.unfold s).length).map fun i => (w ++ [i.val], (S.unfold s)[i])

/-- **One step of the frontier machine.** -/
def step (P : Policy (List ℕ × (α ⊕ σ))) : Config σ α → Config σ α
  | ⟨found, []⟩ => ⟨found, []⟩
  | ⟨found, (w, .inl a) :: rest⟩ => ⟨found ++ [(w, a)], rest⟩
  | ⟨found, (w, .inr s) :: rest⟩ => ⟨found, P.insert (S.children w s) rest⟩

/-- The machine after `k` steps. -/
def search (P : Policy (List ℕ × (α ⊕ σ))) (k : ℕ) (x : α ⊕ σ) : Config σ α :=
  (S.step P)^[k] (Config.start x)

theorem search_succ (P : Policy (List ℕ × (α ⊕ σ))) (k : ℕ) (x : α ⊕ σ) :
    S.search P (k + 1) x = S.step P (S.search P k x) :=
  Function.iterate_succ_apply' _ _ _

/-! ## Facts about addresses -/

theorem mem_children {w : List ℕ} {s : σ} {e : List ℕ × (α ⊕ σ)} :
    e ∈ S.children w s ↔ ∃ i : Fin (S.unfold s).length, e = (w ++ [i.val], (S.unfold s)[i]) := by
  simp only [children, List.mem_map]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, List.mem_finRange i, rfl⟩

theorem children_valid {x : α ⊕ σ} {w : List ℕ} {s : σ} (state : S.item x w = some (.inr s)) :
    ∀ e ∈ S.children w s, S.item x e.1 = some e.2 := by
  intro e member
  obtain ⟨i, rfl⟩ := (S.mem_children).mp member
  rw [item_append, state]
  simp [item_inr_cons]

/-- An answer has no extension. -/
theorem eq_of_answer_prefix {x : α ⊕ σ} {w v : List ℕ} {a : α} {y : α ⊕ σ}
    (answer : S.item x w = some (.inl a)) (valid : S.item x v = some y) (pre : w <+: v) : v = w := by
  obtain ⟨r, rfl⟩ := pre
  rw [item_append, answer] at valid
  cases r with
  | nil => simp
  | cons i r => simp at valid

theorem get_of_state_prefix {x : α ⊕ σ} {w : List ℕ} {s : σ} {i : ℕ} {r : List ℕ} {y : α ⊕ σ}
    (state : S.item x w = some (.inr s)) (valid : S.item x (w ++ i :: r) = some y) :
    i < (S.unfold s).length := by
  rw [item_append, state] at valid
  simp only [Option.bind_some, item_inr_cons, Option.bind_eq_some_iff] at valid
  obtain ⟨y₀, get, _⟩ := valid
  exact (List.getElem?_eq_some_iff.mp get).1

/-- The number of pending entries at or above an address. -/
def cover (pending : List (List ℕ × (α ⊕ σ))) (v : List ℕ) : ℕ :=
  pending.countP fun e => decide (e.1 <+: v)

theorem cover_cons (e : List ℕ × (α ⊕ σ)) (rest : List (List ℕ × (α ⊕ σ))) (v : List ℕ) :
    cover (e :: rest) v = cover rest v + if e.1 <+: v then 1 else 0 := by
  simp [cover, List.countP_cons]

theorem cover_perm {l l' : List (List ℕ × (α ⊕ σ))} (h : l.Perm l') (v : List ℕ) :
    cover l v = cover l' v :=
  h.countP_eq _

theorem cover_append (l l' : List (List ℕ × (α ⊕ σ))) (v : List ℕ) :
    cover (l ++ l') v = cover l v + cover l' v := List.countP_append

theorem cover_children_of_not_prefix {w v : List ℕ} {s : σ} (h : ¬ w <+: v) :
    cover (S.children w s) v = 0 := by
  rw [cover, List.countP_eq_zero]
  intro e member
  obtain ⟨i, rfl⟩ := (S.mem_children).mp member
  simp only [decide_eq_true_eq]
  exact fun pre => h ((List.prefix_append w [i.val]).trans pre)

theorem cover_children_self (w : List ℕ) (s : σ) : cover (S.children w s) w = 0 := by
  rw [cover, List.countP_eq_zero]
  intro e member
  obtain ⟨i, rfl⟩ := (S.mem_children).mp member
  simp only [decide_eq_true_eq]
  intro pre
  have := pre.length_le
  simp at this

theorem cover_children_below {w : List ℕ} {s : σ} {i : ℕ} (r : List ℕ)
    (h : i < (S.unfold s).length) : cover (S.children w s) (w ++ i :: r) = 1 := by
  rw [cover, children, List.countP_map]
  have same : ∀ j ∈ List.finRange (S.unfold s).length,
      ((fun e : List ℕ × (α ⊕ σ) => decide (e.1 <+: w ++ i :: r)) ∘
        fun j : Fin (S.unfold s).length => (w ++ [j.val], (S.unfold s)[j])) j = true ↔
        (j == ⟨i, h⟩) = true := by
    intro j _
    simp [Fin.ext_iff]
  rw [List.countP_congr same]
  exact List.count_eq_one_of_mem (List.nodup_finRange _) (List.mem_finRange _)

/-! ## The invariant -/

/-- **Every address is accounted for exactly once**: by a recorded answer, an expanded state in
`done`, or a pending entry above it; and everything recorded is where it says. -/
structure Covers (x : α ⊕ σ) (c : Config σ α) (done : List (List ℕ)) : Prop where
  pending_valid : ∀ e ∈ c.pending, S.item x e.1 = some e.2
  found_valid : ∀ p ∈ c.found, S.item x p.1 = some (.inl p.2)
  done_valid : ∀ w ∈ done, ∃ t, S.item x w = some (.inr t)
  once : ∀ v y, S.item x v = some y →
    (c.found.map Prod.fst).count v + done.count v + cover c.pending v = 1

theorem covers_start (x : α ⊕ σ) : S.Covers x (Config.start x) [] where
  pending_valid e member := by
    simp only [Config.start, List.mem_singleton] at member
    subst member
    simp
  found_valid p member := by simp [Config.start] at member
  done_valid w member := by simp at member
  once v y _ := by simp [Config.start, cover]

theorem covers_step (P : Policy (List ℕ × (α ⊕ σ))) {x : α ⊕ σ} {c : Config σ α}
    {done : List (List ℕ)} (h : S.Covers x c done) :
    ∃ done' : List (List ℕ), done'.length ≤ done.length + 1 ∧ S.Covers x (S.step P c) done' := by
  obtain ⟨found, pending⟩ := c
  match pending, h with
  | [], h => exact ⟨done, Nat.le_succ _, h⟩
  | (w₀, .inl a) :: rest, h =>
      refine ⟨done, Nat.le_succ _, ⟨?_, ?_, h.done_valid, ?_⟩⟩
      · intro e member
        exact h.pending_valid e (List.mem_cons_of_mem _ member)
      · intro p member
        rcases List.mem_append.mp member with old | new
        · exact h.found_valid p old
        · simp only [List.mem_singleton] at new
          subst new
          exact h.pending_valid _ (List.mem_cons_self ..)
      · intro v y valid
        have before := h.once v y valid
        have answer := h.pending_valid _ (List.mem_cons_self ..)
        simp only [cover_cons] at before
        show ((found ++ [(w₀, a)]).map Prod.fst).count v + done.count v + cover rest v = 1
        rw [List.map_append, List.count_append]
        by_cases pre : w₀ <+: v
        · have same := S.eq_of_answer_prefix answer valid pre
          rw [if_pos pre] at before
          have : ([(w₀, a)].map Prod.fst).count v = 1 := by
            rw [same]
            exact List.count_singleton_self
          omega
        · rw [if_neg pre] at before
          have : ([(w₀, a)].map Prod.fst).count v = 0 := by
            rw [List.map_singleton, List.count_singleton, if_neg]
            rw [beq_iff_eq]
            rintro rfl
            exact pre (List.prefix_refl _)
          omega
  | (w₀, .inr s) :: rest, h =>
      have state := h.pending_valid _ (List.mem_cons_self ..)
      refine ⟨w₀ :: done, by simp, ⟨?_, h.found_valid, ?_, ?_⟩⟩
      · intro e member
        rcases List.mem_append.mp ((P.perm _ _).mem_iff.mp member) with new | old
        · exact S.children_valid state e new
        · exact h.pending_valid e (List.mem_cons_of_mem _ old)
      · intro w member
        rcases List.mem_cons.mp member with rfl | old
        · exact ⟨s, state⟩
        · exact h.done_valid w old
      · intro v y valid
        have before := h.once v y valid
        simp only [cover_cons] at before
        show (found.map Prod.fst).count v + (w₀ :: done).count v +
          cover (P.insert (S.children w₀ s) rest) v = 1
        rw [cover_perm (P.perm _ _), cover_append, List.count_cons]
        by_cases pre : w₀ <+: v
        · obtain ⟨r, rfl⟩ := pre
          cases r with
          | nil =>
              rw [List.append_nil] at before valid ⊢
              rw [if_pos (List.prefix_refl w₀)] at before
              rw [if_pos (beq_self_eq_true w₀), S.cover_children_self]
              omega
          | cons i r =>
              have bound := S.get_of_state_prefix state valid
              have differ : ¬ (w₀ == w₀ ++ i :: r) = true := by
                rw [beq_iff_eq]
                intro same
                have := congrArg List.length same
                simp at this
              rw [if_pos (List.prefix_append w₀ (i :: r))] at before
              rw [if_neg differ, S.cover_children_below r bound]
              omega
        · have differ : ¬ (w₀ == v) = true := by
            rw [beq_iff_eq]
            rintro rfl
            exact pre (List.prefix_refl _)
          rw [if_neg pre] at before
          rw [if_neg differ, S.cover_children_of_not_prefix pre]
          omega

/-- **The invariant holds after every number of steps, for every policy.** -/
theorem covers_search (P : Policy (List ℕ × (α ⊕ σ))) (x : α ⊕ σ) :
    ∀ k : ℕ, ∃ done : List (List ℕ), done.length ≤ k ∧ S.Covers x (S.search P k x) done
  | 0 => ⟨[], le_rfl, S.covers_start x⟩
  | k + 1 => by
      obtain ⟨done, short, h⟩ := covers_search P x k
      obtain ⟨done', short', h'⟩ := S.covers_step P h
      rw [search_succ]
      exact ⟨done', by omega, h'⟩

/-! ## Soundness and completeness of every policy -/

variable (P : Policy (List ℕ × (α ⊕ σ)))

/-- **Recorded answers are answers.** -/
theorem found_sound {k : ℕ} {x : α ⊕ σ} {p : List ℕ × α} (h : p ∈ (S.search P k x).found) :
    p ∈ S.Answers x := by
  obtain ⟨_, _, covers⟩ := S.covers_search P x k
  exact covers.found_valid p h

/-- **Each answer is recorded once.** -/
theorem found_nodup (k : ℕ) (x : α ⊕ σ) : ((S.search P k x).found.map Prod.fst).Nodup := by
  obtain ⟨done, _, covers⟩ := S.covers_search P x k
  rw [List.nodup_iff_count_le_one]
  intro v
  by_cases present : v ∈ (S.search P k x).found.map Prod.fst
  · obtain ⟨p, member, rfl⟩ := List.mem_map.mp present
    have := covers.once p.1 _ (covers.found_valid p member)
    omega
  · rw [List.count_eq_zero_of_not_mem present]
    exact Nat.zero_le 1

theorem found_nodup' (k : ℕ) (x : α ⊕ σ) : (S.search P k x).found.Nodup :=
  (S.found_nodup P k x).of_map _

/-- **Nothing pending means every answer is recorded.** -/
theorem found_complete {k : ℕ} {x : α ⊕ σ} (finished : (S.search P k x).pending = [])
    {p : List ℕ × α} (h : p ∈ S.Answers x) : p ∈ (S.search P k x).found := by
  obtain ⟨done, _, covers⟩ := S.covers_search P x k
  have once := covers.once p.1 _ h
  have notDone : done.count p.1 = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro member
    obtain ⟨t, state⟩ := covers.done_valid _ member
    have := (S.mem_Answers.mp h).symm.trans state
    simp at this
  rw [finished, notDone] at once
  simp only [cover, List.countP_nil, add_zero] at once
  have pos : 0 < ((S.search P k x).found.map Prod.fst).count p.1 := by omega
  obtain ⟨q, member, address⟩ := List.mem_map.mp (List.count_pos_iff.mp pos)
  have : q.2 = p.2 := by
    have valid := covers.found_valid q member
    rw [address] at valid
    have := valid.symm.trans (S.mem_Answers.mp h)
    simpa using this
  rwa [Prod.ext address this] at member

/-- Every state of a finished machine is shallower than its budget. -/
theorem length_lt_of_finished {k : ℕ} {x : α ⊕ σ} (finished : (S.search P k x).pending = [])
    {w : List ℕ} {t : σ} (state : S.item x w = some (.inr t)) : w.length < k := by
  obtain ⟨done, short, covers⟩ := S.covers_search P x k
  classical
  have inDone : ∀ j ≤ w.length, w.take j ∈ done := by
    intro j _
    have valid : ∃ y, S.item x (w.take j) = some y := by
      have := S.item_append x (w.take j) (w.drop j)
      rw [List.take_append_drop, state] at this
      cases hj : S.item x (w.take j) with
      | none => rw [hj] at this; simp at this
      | some y => exact ⟨y, rfl⟩
    obtain ⟨y, valid⟩ := valid
    have once := covers.once _ y valid
    rw [finished] at once
    simp only [cover, List.countP_nil, add_zero] at once
    have notFound : ((S.search P k x).found.map Prod.fst).count (w.take j) = 0 := by
      apply List.count_eq_zero_of_not_mem
      intro member
      obtain ⟨p, member, address⟩ := List.mem_map.mp member
      have answer := covers.found_valid p member
      rw [address] at answer
      have := S.eq_of_answer_prefix answer state (List.take_prefix j w)
      rw [← this] at answer
      have := answer.symm.trans state
      simp at this
    rw [notFound, zero_add] at once
    have pos : 0 < done.count (w.take j) := by omega
    exact List.count_pos_iff.mp pos
  have card : (Finset.range (w.length + 1)).card ≤ done.toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun j => w.take j)
    · intro j member
      simp only [Finset.coe_range, Set.mem_Iio] at member
      exact List.mem_toFinset.mpr (inDone j (by omega))
    · intro i member j member' same
      simp only [Finset.coe_range, Set.mem_Iio] at member member'
      have := congrArg List.length same
      simp only [List.length_take] at this
      omega
  have := done.toFinset_card_le
  simp only [Finset.card_range] at card
  omega

/-- **Every policy computes an approximant**: below the budgeted run at a large enough depth. -/
theorem outcome_le_run (k : ℕ) (x : α ⊕ σ) :
    ∃ N, (S.search P k x).outcome ≤ S.run N x := by
  by_cases finished : (S.search P k x).pending = []
  · refine ⟨k, le_of_eq ?_⟩
    have runFinished : (S.run k x).status = .finished :=
      (S.status_run_eq_finished_iff k x).mpr fun w t state =>
        S.length_lt_of_finished P finished state
    apply Outcome.ext
    · apply (Multiset.Nodup.ext (Multiset.coe_nodup.mpr (S.found_nodup' P k x))
        (S.nodup_run k x)).mpr
      intro p
      constructor
      · intro member
        exact S.mem_run_of_finished runFinished (S.found_sound P member)
      · intro member
        exact S.found_complete P finished (S.run_sound member)
    · show (S.search P k x).status = (S.run k x).status
      rw [runFinished]
      exact (Config.status_eq_finished_iff _).mpr finished
  · let N := ((S.search P k x).found.map fun p => p.1.length).sum
    refine ⟨N, .inr ⟨?_, ?_⟩⟩
    · show (S.search P k x).status = .cutOff
      apply Status.eq_cutOff_of_ne_finished
      rwa [Ne, Config.status_eq_finished_iff]
    · show ((S.search P k x).found : Multiset (List ℕ × α)) ≤ (S.run N x).answers
      rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (S.found_nodup' P k x))]
      intro p member
      apply (S.mem_run N x p.1 p.2).mpr
      refine ⟨S.found_sound P member, ?_⟩
      exact List.le_sum_of_mem (List.mem_map.mpr ⟨p, member, rfl⟩)

/-- **A finished machine computes the budgeted run itself**, for every policy. -/
theorem outcome_eq_run_of_finished {k : ℕ} {x : α ⊕ σ} (finished : (S.search P k x).pending = []) :
    (S.search P k x).outcome = S.run k x := by
  have runFinished : (S.run k x).status = .finished :=
    (S.status_run_eq_finished_iff k x).mpr fun w t state => S.length_lt_of_finished P finished state
  obtain ⟨N, below⟩ := S.outcome_le_run P k x
  have status : (S.search P k x).outcome.status = .finished :=
    (Config.status_eq_finished_iff _).mpr finished
  have same := Outcome.eq_of_finished_le status below
  rcases le_total k N with h | h
  · rw [← same, S.run_eq_of_finished h runFinished]
  · have runN : (S.run N x).status = .finished := by rw [same]; exact status
    rw [← same, S.run_eq_of_finished h runN]

/-- The recorded answers only grow, in order. -/
theorem found_prefix_step (c : Config σ α) : c.found <+: (S.step P c).found := by
  obtain ⟨found, pending⟩ := c
  match pending with
  | [] => exact List.prefix_refl _
  | (w, .inl a) :: rest => exact List.prefix_append _ _
  | (w, .inr s) :: rest => exact List.prefix_refl _

theorem found_prefix_of_le (x : α ⊕ σ) {k k' : ℕ} (h : k ≤ k') :
    (S.search P k x).found <+: (S.search P k' x).found := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => rw [search_succ]; exact ih.trans (S.found_prefix_step P _)

theorem step_of_finished {c : Config σ α} (finished : c.pending = []) : S.step P c = c := by
  obtain ⟨found, pending⟩ := c
  simp only at finished
  subst finished
  rfl

/-! ## The verbs -/

/-- **`within`**: the answers after `k` steps, with whether the search finished. -/
def within (k : ℕ) (x : α ⊕ σ) : Outcome α := (S.search P k x).outcome.map Prod.snd

/-- **`within` is sound**: below the approximant at some depth, in the information order. -/
theorem within_le_approx (k : ℕ) (x : α ⊕ σ) : ∃ N, S.within P k x ≤ S.approx N x := by
  obtain ⟨N, h⟩ := S.outcome_le_run P k x
  exact ⟨N, Outcome.map_mono _ h⟩

theorem within_eq_approx_of_finished {k : ℕ} {x : α ⊕ σ}
    (finished : (S.within P k x).status = .finished) : S.within P k x = S.approx k x := by
  have : (S.search P k x).pending = [] := (Config.status_eq_finished_iff _).mp finished
  rw [within, S.outcome_eq_run_of_finished P this]
  rfl

/-- **`within` never reads refuted while cut off, and a refutation is sound.** -/
theorem within_refuted_sound {k : ℕ} {x : α ⊕ σ} (h : (S.within P k x).verdict = .refuted) :
    ∀ w a, S.item x w ≠ some (.inl a) := by
  have finished : (S.within P k x).status = .finished := by
    rw [Outcome.verdict_eq_refuted_iff] at h
    rw [h]
    rfl
  rw [within_eq_approx_of_finished S P finished] at h
  exact S.refuted_sound h

/-- One step that refuses once `n` answers are recorded. -/
def stepUntil (n : ℕ) (c : Config σ α) : Config σ α :=
  if n ≤ c.found.length then c else S.step P c

/-- **`take n`**: the machine, stopped as soon as `n` answers are recorded. -/
def take (n k : ℕ) (x : α ⊕ σ) : Config σ α := (S.stepUntil P n)^[k] (Config.start x)

/-- **`take n` is the machine stopped at an earlier budget.** -/
theorem take_eq_search (n : ℕ) (x : α ⊕ σ) :
    ∀ k : ℕ, ∃ j ≤ k, S.take P n k x = S.search P j x
  | 0 => ⟨0, le_rfl, rfl⟩
  | k + 1 => by
      obtain ⟨j, short, same⟩ := take_eq_search n x k
      have unfold : S.take P n (k + 1) x = S.stepUntil P n (S.take P n k x) :=
        Function.iterate_succ_apply' _ _ _
      rw [unfold, same, stepUntil]
      split_ifs
      · exact ⟨j, by omega, rfl⟩
      · exact ⟨j + 1, by omega, (S.search_succ P j x).symm⟩

theorem take_found_sound {n k : ℕ} {x : α ⊕ σ} {p : List ℕ × α}
    (h : p ∈ (S.take P n k x).found) : p ∈ S.Answers x := by
  obtain ⟨j, _, same⟩ := S.take_eq_search P n x k
  rw [same] at h
  exact S.found_sound P h

theorem take_found_length_le (n : ℕ) (x : α ⊕ σ) :
    ∀ k : ℕ, (S.take P n k x).found.length ≤ n
  | 0 => Nat.zero_le n
  | k + 1 => by
      have ih := take_found_length_le n x k
      have unfold : S.take P n (k + 1) x = S.stepUntil P n (S.take P n k x) :=
        Function.iterate_succ_apply' _ _ _
      rw [unfold, stepUntil]
      split_ifs with full
      · exact ih
      · generalize S.take P n k x = c at ih full ⊢
        obtain ⟨found, pending⟩ := c
        change found.length ≤ n at ih
        cases pending with
        | nil => exact ih
        | cons e rest =>
            obtain ⟨w, y⟩ := e
            cases y with
            | inl a =>
                show (found ++ [(w, a)]).length ≤ n
                change ¬ n ≤ found.length at full
                rw [List.length_append, List.length_singleton]
                omega
            | inr s => exact ih

/-- **The contract of `take n`**: when finished for it, either `n` answers were recorded, or the
whole search finished and every answer was recorded. -/
theorem take_finished_contract {n k : ℕ} {x : α ⊕ σ}
    (finished : (S.take P n k x).takeStatus n = .finished) :
    (S.take P n k x).found.length = n ∨
      ((S.take P n k x).pending = [] ∧ ∀ p ∈ S.Answers x, p ∈ (S.take P n k x).found) := by
  unfold Config.takeStatus at finished
  split_ifs at finished with full
  · exact .inl (le_antisymm (S.take_found_length_le P n x k) full)
  · rw [Config.status_eq_finished_iff] at finished
    obtain ⟨j, _, same⟩ := S.take_eq_search P n x k
    rw [same] at finished ⊢
    exact .inr ⟨finished, fun p h => S.found_complete P finished h⟩

/-- **`first`**: the first answer recorded, stopping there. -/
def first (k : ℕ) (x : α ⊕ σ) : Option (List ℕ × α) := (S.take P 1 k x).found.head?

theorem first_sound {k : ℕ} {x : α ⊕ σ} {p : List ℕ × α} (h : S.first P k x = some p) :
    p ∈ S.Answers x :=
  S.take_found_sound P (List.mem_of_mem_head? h)

/-- **No first answer with nothing pending is a refutation** of the unbounded semantics. -/
theorem first_refuted {k : ℕ} {x : α ⊕ σ} (none : S.first P k x = none)
    (finished : (S.take P 1 k x).pending = []) : ∀ p, p ∉ S.Answers x := by
  intro p h
  obtain ⟨j, _, same⟩ := S.take_eq_search P 1 x k
  rw [same] at finished
  have := S.found_complete P finished h
  rw [← same] at this
  rw [first, List.head?_eq_none_iff] at none
  rw [none] at this
  exact List.not_mem_nil this

/-- **`all`**: defined when some budget leaves nothing pending; then the recorded answers. -/
def all (x : α ⊕ σ) : Part (Multiset (List ℕ × α)) :=
  ⟨∃ k, (S.search P k x).pending.isEmpty = true, fun h => (S.search P (Nat.find h) x).found⟩

/-- **`all` is the unbounded semantics.** -/
theorem mem_all {x : α ⊕ σ} (defined : (S.all P x).Dom) (p : List ℕ × α) :
    p ∈ (S.all P x).get defined ↔ p ∈ S.Answers x := by
  have finished : (S.search P (Nat.find defined) x).pending = [] :=
    List.isEmpty_iff.mp (Nat.find_spec defined)
  change p ∈ ((S.search P (Nat.find defined) x).found : Multiset (List ℕ × α)) ↔ _
  rw [Multiset.mem_coe]
  exact ⟨S.found_sound P, S.found_complete P finished⟩

theorem nodup_all {x : α ⊕ σ} (defined : (S.all P x).Dom) : ((S.all P x).get defined).Nodup :=
  Multiset.coe_nodup.mpr (S.found_nodup' P _ x)

/-- **`all` does not depend on the policy.** -/
theorem all_eq_all (P' : Policy (List ℕ × (α ⊕ σ))) {x : α ⊕ σ} (defined : (S.all P x).Dom)
    (defined' : (S.all P' x).Dom) : (S.all P x).get defined = (S.all P' x).get defined' :=
  (Multiset.Nodup.ext (S.nodup_all P defined) (S.nodup_all P' defined')).mpr fun p =>
    (S.mem_all P defined p).trans (S.mem_all P' defined' p).symm

/-! ## Breadth-first is fair -/

/-- An entry of a queue reaches its front after as many steps as there are entries before it. -/
theorem bfs_front (x : α ⊕ σ) :
    ∀ (pre : List (List ℕ × (α ⊕ σ))) (e : List ℕ × (α ⊕ σ)) (post : List (List ℕ × (α ⊕ σ)))
      (k : ℕ), (S.search .bfs k x).pending = pre ++ e :: post →
      ∃ post', (S.search .bfs (k + pre.length) x).pending = e :: post'
  | [], e, post, k, h => ⟨post, h⟩
  | head :: pre, e, post, k, h => by
      have next : ∃ post', (S.search .bfs (k + 1) x).pending = pre ++ e :: post' := by
        rw [search_succ]
        generalize S.search .bfs k x = c at h ⊢
        obtain ⟨found, pending⟩ := c
        change pending = _ at h
        subst h
        obtain ⟨w, y⟩ := head
        cases y with
        | inl a => exact ⟨post, rfl⟩
        | inr s => exact ⟨post ++ S.children w s, by simp [step, Policy.bfs]⟩
      obtain ⟨post', h'⟩ := next
      obtain ⟨post'', h''⟩ := bfs_front x pre e post' (k + 1) h'
      exact ⟨post'', by rw [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm]; exact h''⟩

/-- **Breadth-first reaches every address**: every item of the tree is at the front at some
budget. -/
theorem bfs_reaches (x : α ⊕ σ) :
    ∀ (w : List ℕ) (y : α ⊕ σ), S.item x w = some y →
      ∃ k post, (S.search .bfs k x).pending = (w, y) :: post := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      intro y h
      simp only [item_nil, Option.some.injEq] at h
      subst h
      exact ⟨0, [], rfl⟩
  | append_singleton w i ih =>
      intro y h
      have parent : ∃ t, S.item x w = some (.inr t) := by
        rw [item_append] at h
        cases hw : S.item x w with
        | none => rw [hw] at h; simp at h
        | some z =>
            rw [hw] at h
            cases z with
            | inl a => simp at h
            | inr t => exact ⟨t, rfl⟩
      obtain ⟨t, state⟩ := parent
      obtain ⟨k, post, front⟩ := ih _ state
      have bound : i < (S.unfold t).length := by
        exact S.get_of_state_prefix (r := []) state h
      have value : (S.unfold t)[i] = y := by
        rw [item_append, state] at h
        simp only [Option.bind_some, item_inr_cons, Option.bind_eq_some_iff, item_nil,
          Option.some.injEq] at h
        obtain ⟨y₀, get, rfl⟩ := h
        exact (List.getElem?_eq_some_iff.mp get).2
      have member : (w ++ [i], y) ∈ S.children w t :=
        (S.mem_children).mpr ⟨⟨i, bound⟩, by rw [← value]; rfl⟩
      have next : (S.search .bfs (k + 1) x).pending = post ++ S.children w t := by
        rw [search_succ]
        generalize S.search .bfs k x = c at front ⊢
        obtain ⟨found, pending⟩ := c
        change pending = _ at front
        subst front
        rfl
      obtain ⟨pre', post', split⟩ := List.append_of_mem (List.mem_append_right post member)
      rw [split] at next
      obtain ⟨post'', h''⟩ := S.bfs_front x pre' _ post' (k + 1) next
      exact ⟨_, _, h''⟩

/-- **Breadth-first is complete on answers at finite depth.** -/
theorem bfs_complete {x : α ⊕ σ} {p : List ℕ × α} (h : p ∈ S.Answers x) :
    ∃ k, p ∈ (S.search .bfs k x).found := by
  obtain ⟨k, post, front⟩ := S.bfs_reaches x p.1 _ h
  refine ⟨k + 1, ?_⟩
  rw [search_succ]
  generalize S.search .bfs k x = c at front ⊢
  obtain ⟨found, pending⟩ := c
  change pending = _ at front
  subst front
  simp [step]

/-! ## Iterative deepening -/

/-- **Iterative deepening** with at most `D` rounds: round `d` is the depth-bounded search `run d`;
it stops at the first finished round. -/
def deepen (D : ℕ) (x : α ⊕ σ) : Outcome (List ℕ × α) :=
  match (List.range (D + 1)).find? fun d => (S.run d x).status == .finished with
  | some d => S.run d x
  | none => S.run D x

/-- **Stopping at the first finished round is sound**: it is the last round. -/
theorem deepen_eq_run (D : ℕ) (x : α ⊕ σ) : S.deepen D x = S.run D x := by
  unfold deepen
  split
  · rename_i d found
    have member := List.mem_of_find?_eq_some found
    have finished := List.find?_some found
    simp only [beq_iff_eq] at finished
    rw [List.mem_range] at member
    exact (S.run_eq_of_finished (by omega) finished).symm
  · rfl

/-- **Iterative deepening is complete on finite depth**: every answer at depth at most its budget
is recorded, whatever the order of alternatives. -/
theorem mem_deepen {D : ℕ} {x : α ⊕ σ} {p : List ℕ × α} (h : p ∈ S.Answers x)
    (shallow : p.1.length ≤ D) : p ∈ (S.deepen D x).answers := by
  rw [deepen_eq_run]
  exact (S.mem_run D x p.1 p.2).mpr ⟨h, shallow⟩

theorem deepen_complete {x : α ⊕ σ} {p : List ℕ × α} (h : p ∈ S.Answers x) :
    ∃ D, p ∈ (S.deepen D x).answers :=
  ⟨p.1.length, S.mem_deepen h le_rfl⟩

end Space

#print axioms Space.covers_search
#print axioms Space.found_sound
#print axioms Space.found_nodup
#print axioms Space.found_complete
#print axioms Space.length_lt_of_finished
#print axioms Space.outcome_le_run
#print axioms Space.outcome_eq_run_of_finished
#print axioms Space.found_prefix_of_le
#print axioms Space.within_le_approx
#print axioms Space.within_eq_approx_of_finished
#print axioms Space.within_refuted_sound
#print axioms Space.take_eq_search
#print axioms Space.take_found_length_le
#print axioms Space.take_finished_contract
#print axioms Space.first_sound
#print axioms Space.first_refuted
#print axioms Space.mem_all
#print axioms Space.all_eq_all
#print axioms Space.bfs_front
#print axioms Space.bfs_reaches
#print axioms Space.bfs_complete
#print axioms Space.deepen_eq_run
#print axioms Space.mem_deepen
#print axioms Space.deepen_complete

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search
