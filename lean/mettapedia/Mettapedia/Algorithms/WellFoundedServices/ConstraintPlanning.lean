import Mettapedia.Algorithms.WellFoundedServices.MeasuredLoop
import Mathlib.Data.List.Forall2

/-!
# Finite constraint planning by backtracking

A problem has finitely many variables, a finite domain for each, and
constraints over scopes of variables. Backtracking search assigns one pending
variable at a time, chosen by a strategy, and tries its values in order.

* **Sound with a witness**: a returned assignment is a solution
  (`solve_inl`).
* **Complete with a refutation certificate**: otherwise the search returns a
  decision tree whose leaves name violated constraints; an independent checker
  (`Problem.check`) accepts it (`solve_inr`), and an accepted certificate
  excludes every solution (`check_sound`).
* **Termination** by the number of pending variables. A strategy may pick any
  pending variable, so the recursion is not structural on the variable list.

`backtrack` is measure-based: recursion on the exact number of pending
variables. `solveAcc` runs the same step (`backtrackStep`) through the
accessibility route, and `solveAcc_eq` says the two agree for every inert
recursor. Two strategies are provided: the first pending variable, and the
variable with the fewest values that survive the constraints (`fewestValues`).
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.WellFoundedServices

open Mettapedia.Order

universe u v w

/-- A constraint: a scope of variables and the value lists it allows. -/
structure Constraint (V : Type u) (D : Type v) where
  scope : List V
  allows : List D → Bool

/-- A finite constraint problem. -/
structure Problem (V : Type u) (D : Type v) where
  vars : List V
  dom : V → List D
  constraints : List (Constraint V D)

/-- A partial assignment; the first binding of a variable counts. -/
abbrev Assignment (V : Type u) (D : Type v) := List (V × D)

/-- A refutation certificate: a decision tree whose leaves name violated
constraints by index. A `split` node has one branch per domain value, in
order. -/
inductive Refutation (V : Type u) where
  | conflict (index : ℕ)
  | split (var : V) (branches : List (Refutation V))
  deriving Repr

/-- The first success of `k` along a list, or the list of all failures. -/
def firstSuccess {S : Type u} {R : Type v} {X : Type w} (k : X → S ⊕ R) : List X → S ⊕ List R
  | [] => .inr []
  | x :: xs =>
      match k x with
      | .inl s => .inl s
      | .inr r =>
          match firstSuccess k xs with
          | .inl s => .inl s
          | .inr rs => .inr (r :: rs)

section FirstSuccess

variable {S : Type u} {R : Type v} {X : Type w}

theorem firstSuccess_inl {k : X → S ⊕ R} {s : S} :
    ∀ {xs : List X}, firstSuccess k xs = .inl s → ∃ x ∈ xs, k x = .inl s
  | [], h => by cases h
  | x :: xs, h => by
      simp only [firstSuccess] at h
      split at h
      · rename_i s' e
        cases h
        exact ⟨x, List.mem_cons_self, e⟩
      · split at h
        · cases h
          obtain ⟨y, hy, e⟩ := firstSuccess_inl ‹_›
          exact ⟨y, List.mem_cons_of_mem _ hy, e⟩
        · cases h

theorem firstSuccess_inr {k : X → S ⊕ R} :
    ∀ {xs : List X} {rs : List R}, firstSuccess k xs = .inr rs →
      List.Forall₂ (fun x r => k x = .inr r) xs rs
  | [], rs, h => by
      simp only [firstSuccess, Sum.inr.injEq] at h
      subst h
      exact .nil
  | x :: xs, rs, h => by
      simp only [firstSuccess] at h
      split at h
      · cases h
      · rename_i r e
        split at h
        · cases h
        · rename_i rs' e'
          simp only [Sum.inr.injEq] at h
          subst h
          exact .cons e (firstSuccess_inr e')

theorem firstSuccess_congr {k k' : X → S ⊕ R} :
    ∀ {xs : List X}, (∀ x ∈ xs, k x = k' x) → firstSuccess k xs = firstSuccess k' xs
  | [], _ => rfl
  | x :: xs, h => by
      simp only [firstSuccess, h x List.mem_cons_self,
        firstSuccess_congr fun y hy => h y (List.mem_cons_of_mem _ hy)]

end FirstSuccess

section ListFacts

variable {α : Type u} [DecidableEq α]

theorem length_erase_add_one {a : α} : ∀ {l : List α}, a ∈ l → (l.erase a).length + 1 = l.length
  | [], h => absurd h List.not_mem_nil
  | b :: l, h => by
      by_cases hb : b = a
      · subst hb
        rw [List.erase_cons_head]
        rfl
      · rw [List.erase_cons_tail (fun e => hb (beq_iff_eq.1 e)), List.length_cons, List.length_cons,
          length_erase_add_one ((List.mem_cons.1 h).resolve_left (Ne.symm hb))]

theorem mem_erase_of_ne {a b : α} (hba : b ≠ a) : ∀ {l : List α}, b ∈ l.erase a ↔ b ∈ l
  | [] => Iff.rfl
  | c :: l => by
      by_cases hc : c = a
      · subst hc
        rw [List.erase_cons_head, List.mem_cons]
        exact ⟨.inr, fun h => h.resolve_left hba⟩
      · rw [List.erase_cons_tail (fun e => hc (beq_iff_eq.1 e)), List.mem_cons, List.mem_cons,
          mem_erase_of_ne hba]

theorem ne_of_mem_erase {a b : α} : ∀ {l : List α}, l.Nodup → b ∈ l.erase a → b ≠ a
  | [], _, h => absurd h List.not_mem_nil
  | c :: l, hn, h => by
      obtain ⟨hcl, hl⟩ := List.nodup_cons.1 hn
      by_cases hc : c = a
      · subst hc
        rw [List.erase_cons_head] at h
        exact fun e => hcl (e ▸ h)
      · rw [List.erase_cons_tail (fun e => hc (beq_iff_eq.1 e)), List.mem_cons] at h
        rcases h with rfl | h
        · exact hc
        · exact ne_of_mem_erase hl h

omit [DecidableEq α] in
theorem findIdx?_some {p : α → Bool} :
    ∀ {l : List α} {i : ℕ}, l.findIdx? p = some i → ∃ h : i < l.length, p l[i] = true
  | [], _, h => by cases h
  | a :: l, i, h => by
      rw [List.findIdx?_cons] at h
      by_cases ha : p a = true
      · rw [if_pos ha] at h
        cases h
        exact ⟨Nat.zero_lt_succ _, ha⟩
      · rw [if_neg ha] at h
        cases e : l.findIdx? p with
        | none => rw [e] at h; cases h
        | some j =>
            rw [e] at h
            cases h
            obtain ⟨hj, hp⟩ := findIdx?_some e
            exact ⟨Nat.succ_lt_succ hj, hp⟩

end ListFacts

section Values

variable {V : Type u} {D : Type v} [DecidableEq V]

/-- The values of a list of variables, when all of them are assigned. -/
def values (a : Assignment V D) : List V → Option (List D)
  | [] => some []
  | v :: vs =>
      match a.lookup v, values a vs with
      | some d, some ds => some (d :: ds)
      | _, _ => none

/-- `f` extends `a`: every binding of `a` is a binding of `f`. -/
def Extends (f a : Assignment V D) : Prop := ∀ v d, a.lookup v = some d → f.lookup v = some d

theorem lookup_cons_ne {a : Assignment V D} {v w : V} {d : D} (h : w ≠ v) :
    List.lookup w ((v, d) :: a) = a.lookup w := by
  rw [List.lookup_cons, beq_false_of_ne h]

theorem extends_nil (f : Assignment V D) : Extends f [] := fun _ _ h => by cases h

theorem extends_cons {f a : Assignment V D} {v : V} {d : D} (he : Extends f a)
    (hv : f.lookup v = some d) : Extends f ((v, d) :: a) := by
  intro w d' h
  by_cases hw : w = v
  · subst hw
    rw [List.lookup_cons_self] at h
    cases h
    exact hv
  · rw [lookup_cons_ne hw] at h
    exact he w d' h

theorem values_extends {f a : Assignment V D} (he : Extends f a) :
    ∀ {vs : List V} {ds : List D}, values a vs = some ds → values f vs = some ds
  | [], _, h => h
  | v :: vs, ds, h => by
      simp only [values] at h ⊢
      split at h
      · rename_i d ds' hv hvs
        cases h
        rw [he v d hv, values_extends he hvs]
      · cases h

theorem values_of_assigned {a : Assignment V D} :
    ∀ {vs : List V}, (∀ v ∈ vs, ∃ d, a.lookup v = some d) → ∃ ds, values a vs = some ds
  | [], _ => ⟨[], rfl⟩
  | v :: vs, h => by
      obtain ⟨d, hd⟩ := h v List.mem_cons_self
      obtain ⟨ds, hds⟩ := values_of_assigned fun w hw => h w (List.mem_cons_of_mem _ hw)
      exact ⟨d :: ds, by simp only [values, hd, hds]⟩

end Values

namespace Constraint

variable {V : Type u} {D : Type v} [DecidableEq V] (c : Constraint V D)

/-- The constraint is violated: its scope is assigned and the values are not
allowed. -/
def violatedBy (a : Assignment V D) : Bool :=
  match values a c.scope with
  | some ds => !c.allows ds
  | none => false

/-- The constraint holds under an assignment. -/
def Satisfies (f : Assignment V D) : Prop :=
  ∃ ds, values f c.scope = some ds ∧ c.allows ds = true

theorem not_satisfies {a f : Assignment V D} (h : c.violatedBy a = true) (he : Extends f a) :
    ¬ c.Satisfies f := by
  rintro ⟨ds, hds, hallow⟩
  unfold violatedBy at h
  split at h
  · rename_i ds' e
    rw [values_extends he e] at hds
    cases hds
    simp [hallow] at h
  · cases h

end Constraint

namespace Problem

variable {V : Type u} {D : Type v} [DecidableEq V] (P : Problem V D)

/-- A solution: every variable has a value from its domain, and every
constraint holds. -/
def Solution (f : Assignment V D) : Prop :=
  (∀ v ∈ P.vars, ∃ d ∈ P.dom v, f.lookup v = some d) ∧ ∀ c ∈ P.constraints, c.Satisfies f

/-- Distinct variables, and constraints only over the problem's variables. -/
structure WellFormed : Prop where
  nodup : P.vars.Nodup
  scopes : ∀ c ∈ P.constraints, ∀ v ∈ c.scope, v ∈ P.vars

/-- The index of the first violated constraint. -/
def firstViolation (a : Assignment V D) : Option ℕ :=
  P.constraints.findIdx? fun c => c.violatedBy a

theorem firstViolation_some {a : Assignment V D} {i : ℕ} (h : P.firstViolation a = some i) :
    ∃ c, P.constraints[i]? = some c ∧ c.violatedBy a = true := by
  obtain ⟨hi, hv⟩ := findIdx?_some h
  exact ⟨_, List.getElem?_eq_getElem hi, hv⟩

theorem firstViolation_none {a : Assignment V D} (h : P.firstViolation a = none) :
    ∀ c ∈ P.constraints, c.violatedBy a = false :=
  List.findIdx?_eq_none_iff.1 h

/-! ## Checking refutations -/

mutual

/-- **The refutation checker.** -/
def check : Assignment V D → Refutation V → Bool
  | a, .conflict i =>
      match P.constraints[i]? with
      | some c => c.violatedBy a
      | none => false
  | a, .split v bs => decide (v ∈ P.vars) && checkBranches a v (P.dom v) bs

/-- One branch per domain value, in order. -/
def checkBranches (a : Assignment V D) (v : V) : List D → List (Refutation V) → Bool
  | [], [] => true
  | d :: ds, b :: bs => check ((v, d) :: a) b && checkBranches a v ds bs
  | _, _ => false

end

mutual

/-- **Soundness of the checker**: an accepted certificate excludes every
solution extending the assignment. -/
theorem check_sound : ∀ (a : Assignment V D) (r : Refutation V), P.check a r = true →
    ∀ f, P.Solution f → ¬ Extends f a
  | a, .conflict i, h, f, hf, he => by
      simp only [check] at h
      split at h
      · rename_i c hc
        exact c.not_satisfies h he (hf.2 c (List.mem_of_getElem? hc))
      · cases h
  | a, .split v bs, h, f, hf, he => by
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨d, hd, hfv⟩ := hf.1 v h.1
      exact checkBranches_sound a v _ bs h.2 d hd f hf (extends_cons he hfv)

theorem checkBranches_sound (a : Assignment V D) (v : V) :
    ∀ (ds : List D) (bs : List (Refutation V)), P.checkBranches a v ds bs = true →
      ∀ d ∈ ds, ∀ f, P.Solution f → ¬ Extends f ((v, d) :: a)
  | [], [], _, d, hd, _, _, _ => absurd hd List.not_mem_nil
  | d' :: ds, b :: bs, h, d, hd, f, hf, he => by
      simp only [checkBranches, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hd with rfl | hd
      · exact check_sound _ b h.1 f hf he
      · exact checkBranches_sound a v ds bs h.2 d hd f hf he
  | [], _ :: _, h, _, _, _, _, _ => by simp [checkBranches] at h
  | _ :: _, [], h, _, _, _, _, _ => by simp [checkBranches] at h

end

/-- An accepted certificate at the empty assignment refutes the problem. -/
theorem no_solution {r : Refutation V} (h : P.check [] r = true) (f : Assignment V D) :
    ¬ P.Solution f :=
  fun hf => P.check_sound [] r h f hf (extends_nil f)

theorem checkBranches_of_forall₂ {a : Assignment V D} {v : V} :
    ∀ {ds : List D} {bs : List (Refutation V)},
      List.Forall₂ (fun d b => P.check ((v, d) :: a) b = true) ds bs →
        P.checkBranches a v ds bs = true
  | [], [], _ => by simp [checkBranches]
  | _ :: _, _ :: _, .cons h hs => by
      simp only [checkBranches, Bool.and_eq_true]
      exact ⟨h, checkBranches_of_forall₂ hs⟩

end Problem

/-! ## Strategies -/

/-- A variable-selection strategy: some pending variable. -/
def Strategy (V : Type u) (D : Type v) : Type (max u v) :=
  Assignment V D → (pending : List V) → pending ≠ [] → {v : V // v ∈ pending}

namespace Strategy

variable {V : Type u} {D : Type v} [DecidableEq V]

/-- The first pending variable. -/
def first : Strategy V D := fun _ pending h => ⟨pending.head h, List.head_mem h⟩

/-- The first member of a nonempty list with the least score. -/
def leastBy (score : V → ℕ) : (x : V) → (xs : List V) → {v : V // v ∈ x :: xs}
  | x, [] => ⟨x, List.mem_cons_self⟩
  | x, y :: ys =>
      let best := leastBy score y ys
      if score x ≤ score best.1 then ⟨x, List.mem_cons_self⟩
      else ⟨best.1, List.mem_cons_of_mem _ best.2⟩

/-- The pending variable with the fewest values that violate no constraint
when assigned. -/
def fewestValues (P : Problem V D) : Strategy V D := fun a pending h =>
  match pending, h with
  | x :: xs, _ =>
      leastBy (fun v => ((P.dom v).filter fun d => (P.firstViolation ((v, d) :: a)).isNone).length)
        x xs

end Strategy

namespace Problem

variable {V : Type u} {D : Type v} [DecidableEq V] (P : Problem V D) (σ : Strategy V D)

theorem length_erase_lt {pending : List V} {v : V} (hv : v ∈ pending) :
    (pending.erase v).length < pending.length := by
  rw [← length_erase_add_one hv]
  exact Nat.lt_succ_self _

/-! ## Backtracking, measure-based -/

/-- **Backtracking search**, by recursion on the exact number of pending
variables. -/
def backtrack : (n : ℕ) → (a : Assignment V D) → (pending : List V) → pending.length = n →
    Assignment V D ⊕ Refutation V
  | 0, a, _, _ =>
      match P.firstViolation a with
      | some i => .inr (.conflict i)
      | none => .inl a
  | n + 1, a, pending, h =>
      match P.firstViolation a with
      | some i => .inr (.conflict i)
      | none =>
          let v := σ a pending (List.ne_nil_of_length_eq_add_one h)
          match firstSuccess (fun d => backtrack n ((v.1, d) :: a) (pending.erase v.1)
              (Nat.succ.inj ((length_erase_add_one v.2).trans h))) (P.dom v.1) with
          | .inl f => .inl f
          | .inr rs => .inr (.split v.1 rs)

/-- **Solve** a problem: search from the empty assignment. -/
def solve : Assignment V D ⊕ Refutation V := P.backtrack σ P.vars.length [] P.vars rfl

theorem backtrack_count {n m : ℕ} {a : Assignment V D} {pending : List V}
    (hn : pending.length = n) (hm : pending.length = m) :
    P.backtrack σ n a pending hn = P.backtrack σ m a pending hm := by
  subst hn; subst hm; rfl

/-! ## Backtracking through the accessibility route -/

/-- The search state: the current assignment and the pending variables. -/
abbrev State (V : Type u) (D : Type v) := Assignment V D × List V

/-- One step of backtracking: report a violated constraint, accept a complete
assignment, or branch on the selected variable; `k` solves the subproblems. -/
def backtrackStep (s : State V D)
    (k : ∀ s' : State V D, s'.2.length < s.2.length → Assignment V D ⊕ Refutation V) :
    Assignment V D ⊕ Refutation V :=
  match P.firstViolation s.1 with
  | some i => .inr (.conflict i)
  | none =>
      if h : s.2 = [] then .inl s.1
      else
        let v := σ s.1 s.2 h
        match firstSuccess (fun d => k ((v.1, d) :: s.1, s.2.erase v.1) (length_erase_lt v.2))
            (P.dom v.1) with
        | .inl f => .inl f
        | .inr rs => .inr (.split v.1 rs)

/-- **Solve through the accessibility route.** -/
def solveAcc (I : InertRecursor.{max (u + 1) (v + 1), max (u + 1) (v + 1)}
      fun (y x : State V D) => y.2.length < x.2.length) : Assignment V D ⊕ Refutation V :=
  I.recursor (C := fun _ => Assignment V D ⊕ Refutation V) (P.backtrackStep σ) ([], P.vars)
    (accCode_measure (fun s : State V D => s.2.length) _)

/-- The measure-based search satisfies the step equation. -/
theorem backtrack_eq_step (n : ℕ) (a : Assignment V D) (pending : List V)
    (h : pending.length = n) :
    P.backtrack σ n a pending h =
      P.backtrackStep σ (a, pending) fun s' _ => P.backtrack σ s'.2.length s'.1 s'.2 rfl := by
  cases n with
  | zero =>
      have hp : pending = [] := List.eq_nil_of_length_eq_zero h
      subst hp
      simp only [backtrack, backtrackStep]
      cases P.firstViolation a <;> rfl
  | succ n =>
      have hp : pending ≠ [] := List.ne_nil_of_length_eq_add_one h
      simp only [backtrack, backtrackStep, dif_neg hp]
      cases P.firstViolation a with
      | some i => rfl
      | none =>
          simp only
          rw [firstSuccess_congr fun d _ => P.backtrack_count σ _ rfl]

/-- **Agreement** of the two searches, for every inert recursor. -/
theorem solveAcc_eq (I : InertRecursor.{max (u + 1) (v + 1), max (u + 1) (v + 1)}
      fun (y x : State V D) => y.2.length < x.2.length) : P.solveAcc σ I = P.solve σ :=
  I.rec_eq_of_fix (C := fun _ => Assignment V D ⊕ Refutation V) (P.backtrackStep σ)
    (fun s => P.backtrack σ s.2.length s.1 s.2 rfl)
    (fun s => P.backtrack_eq_step σ s.2.length s.1 s.2 rfl) _

/-! ## Correctness -/

/-- The invariant of the search. -/
structure SearchInv (a : Assignment V D) (pending : List V) : Prop where
  sub : ∀ v ∈ pending, v ∈ P.vars
  nodup : pending.Nodup
  fresh : ∀ v ∈ pending, a.lookup v = none
  assigned : ∀ v ∈ P.vars, v ∉ pending → ∃ d ∈ P.dom v, a.lookup v = some d

theorem searchInv_start (hW : P.WellFormed) : P.SearchInv [] P.vars where
  sub _ h := h
  nodup := hW.nodup
  fresh _ _ := rfl
  assigned _ h h' := absurd h h'

theorem searchInv_step {a : Assignment V D} {pending : List V} (inv : P.SearchInv a pending)
    {v : V} (hv : v ∈ pending) {d : D} (hd : d ∈ P.dom v) :
    P.SearchInv ((v, d) :: a) (pending.erase v) where
  sub w hw := inv.sub w (List.erase_subset hw)
  nodup := inv.nodup.erase v
  fresh w hw := by
    have hwv : w ≠ v := ne_of_mem_erase inv.nodup hw
    rw [lookup_cons_ne hwv]
    exact inv.fresh w (List.erase_subset hw)
  assigned w hw hw' := by
    by_cases hwv : w = v
    · subst hwv
      exact ⟨d, hd, List.lookup_cons_self⟩
    · rw [lookup_cons_ne hwv]
      exact inv.assigned w hw fun h => hw' ((mem_erase_of_ne hwv).2 h)

theorem solution_of_complete (hW : P.WellFormed) {a : Assignment V D}
    (inv : P.SearchInv a []) (hv : P.firstViolation a = none) : P.Solution a := by
  have assigned : ∀ v ∈ P.vars, ∃ d ∈ P.dom v, a.lookup v = some d :=
    fun v hv' => inv.assigned v hv' List.not_mem_nil
  refine ⟨assigned, fun c hc => ?_⟩
  obtain ⟨ds, hds⟩ := values_of_assigned (a := a) (vs := c.scope) fun v hv' => by
    obtain ⟨d, -, hd⟩ := assigned v (hW.scopes c hc v hv')
    exact ⟨d, hd⟩
  have hviol := P.firstViolation_none hv c hc
  unfold Constraint.violatedBy at hviol
  rw [hds] at hviol
  exact ⟨ds, hds, by simpa using hviol⟩

/-- **Soundness** of the measure-based search. -/
theorem backtrack_inl (hW : P.WellFormed) :
    ∀ (n : ℕ) (a : Assignment V D) (pending : List V) (h : pending.length = n) (f : Assignment V D),
      P.SearchInv a pending → P.backtrack σ n a pending h = .inl f → P.Solution f
  | 0, a, pending, h, f, inv, e => by
      have hp : pending = [] := List.eq_nil_of_length_eq_zero h
      subst hp
      simp only [backtrack] at e
      split at e
      · cases e
      · rename_i hv
        cases e
        exact P.solution_of_complete hW inv hv
  | n + 1, a, pending, h, f, inv, e => by
      simp only [backtrack] at e
      split at e
      · cases e
      · split at e
        · rename_i f' hs
          cases e
          obtain ⟨d, hd, e'⟩ := firstSuccess_inl hs
          exact backtrack_inl hW n _ _ _ f
            (P.searchInv_step inv (σ a pending (List.ne_nil_of_length_eq_add_one h)).2 hd) e'
        · cases e

/-- **Completeness** of the measure-based search: its refutations are
accepted by the checker. -/
theorem backtrack_inr :
    ∀ (n : ℕ) (a : Assignment V D) (pending : List V) (h : pending.length = n) (r : Refutation V),
      (∀ v ∈ pending, v ∈ P.vars) → P.backtrack σ n a pending h = .inr r → P.check a r = true
  | 0, a, pending, h, r, _, e => by
      simp only [backtrack] at e
      split at e
      · rename_i i hi
        cases e
        obtain ⟨c, hc, hv⟩ := P.firstViolation_some hi
        simp only [check, hc, hv]
      · cases e
  | n + 1, a, pending, h, r, hsub, e => by
      simp only [backtrack] at e
      split at e
      · rename_i i hi
        cases e
        obtain ⟨c, hc, hv⟩ := P.firstViolation_some hi
        simp only [check, hc, hv]
      · split at e
        · cases e
        · rename_i rs hs
          cases e
          have hvar := (σ a pending (List.ne_nil_of_length_eq_add_one h)).2
          simp only [check, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨hsub _ hvar, P.checkBranches_of_forall₂ ?_⟩
          refine (firstSuccess_inr hs).imp fun d r' e' => ?_
          exact backtrack_inr n _ _ _ r' (fun w hw => hsub w (List.erase_subset hw)) e'

/-- **The search is sound**: a returned assignment is a solution. -/
theorem solve_inl (hW : P.WellFormed) {f : Assignment V D} (h : P.solve σ = .inl f) :
    P.Solution f :=
  P.backtrack_inl σ hW _ _ _ _ f (P.searchInv_start hW) h

/-- **The search is complete**: a returned refutation is accepted by the
checker, so the problem has no solution. -/
theorem solve_inr {r : Refutation V} (h : P.solve σ = .inr r) :
    P.check [] r = true ∧ ∀ f, ¬ P.Solution f := by
  have hc := P.backtrack_inr σ _ _ _ _ r (fun _ h => h) h
  exact ⟨hc, P.no_solution hc⟩

/-- **The search decides solvability**, for every strategy. -/
theorem solvable_iff (hW : P.WellFormed) : (∃ f, P.Solution f) ↔ (P.solve σ).isLeft := by
  constructor
  · rintro ⟨f, hf⟩
    cases e : P.solve σ with
    | inl f' => rfl
    | inr r => exact absurd hf ((P.solve_inr σ e).2 f)
  · intro h
    cases e : P.solve σ with
    | inl f => exact ⟨f, P.solve_inl σ hW e⟩
    | inr r => rw [e] at h; cases h

/-- The same guarantees through the accessibility route. -/
theorem solveAcc_inl (hW : P.WellFormed) (I : InertRecursor.{max (u + 1) (v + 1), max (u + 1) (v + 1)}
      fun (y x : State V D) => y.2.length < x.2.length) {f : Assignment V D}
    (h : P.solveAcc σ I = .inl f) : P.Solution f :=
  P.solve_inl σ hW (P.solveAcc_eq σ I ▸ h)

theorem solveAcc_inr (I : InertRecursor.{max (u + 1) (v + 1), max (u + 1) (v + 1)}
      fun (y x : State V D) => y.2.length < x.2.length) {r : Refutation V}
    (h : P.solveAcc σ I = .inr r) : P.check [] r = true ∧ ∀ f, ¬ P.Solution f :=
  P.solve_inr σ (P.solveAcc_eq σ I ▸ h)

end Problem

end Mettapedia.Algorithms.WellFoundedServices
