import Mettapedia.Languages.MeTTa.EvaluationControl.ParameterReadings

/-!
# One-way matching is unification against a ground target

The evaluator of `ParameterReadings` binds by two-way unification (`unifyM`). One-way matching
(`matchTm`), which binds only the pattern's variables and treats the target's variables as
constants, is the special case of a target without variables, and substitution of arguments for
parameters is the special case of a head made of distinct variables:

* `unify_ground_eq_match`: for a pattern `p` (no cells, no role markers) and a ground target `t`,
  with ground bindings and enough fuel, unification has exactly the outcome of matching: one
  success with the matching bindings when `matchTm p t` succeeds, no outcome when it fails.
* `unify_ground_eq_match_in_role`: the same with the target read in any role; each binding
  carries the role (`wrapBinds`).
* `match_ground_rows`: on a space of ground rows, from a store without bindings,
  `(match &self p template)` runs the template once for each row that `p` matches one-way, in
  row order, with the matching bindings in the reading's role.
* `unify_ground_ground`: two ground terms unify exactly when they are equal.
* `unify_var_cell`, `unify_var_held`, `unify_var_received`: a variable parameter takes a running
  argument's need cell without running it, and a held argument as syntax.
* `unify_head_vars`: a head of distinct unbound variables binds each parameter to what it
  received, in order, running nothing: on such heads, unification is substitution.
* `match_reads_values`, `match_runs_reads`: on ground rows, `(match &self p $x)` answers each
  matched part as a value under the readings that keep values, and runs it as code under
  `substitute`.

Positive and negative examples (`matching_examples`): `(fact 1 $v)` against `(fact 1 2)` binds
`$v` to `2`; `(pair $a $a)` against `(pair 3 4)` has no outcome, against `(pair 3 3)` it binds `$a`
once. Against a target with a variable the two differ: matching `(fact 1 $v)` against
`(fact $y 2)` fails, and unification binds `$v` to `2` and `$y` to `1`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.EvaluationControl.ParameterReadings

mutual
/-- A term without variables, cells or role markers. -/
def isGround : Tm → Bool
  | .sym _ => true
  | .num _ => true
  | .str _ => true
  | .expr items => isGroundList items
  | _ => false

def isGroundList : List Tm → Bool
  | [] => true
  | t :: ts => isGround t && isGroundList ts
end

mutual
/-- A pattern: a term without cells or role markers. -/
def isPattern : Tm → Bool
  | .var _ => true
  | .sym _ => true
  | .num _ => true
  | .str _ => true
  | .expr items => isPatternList items
  | _ => false

def isPatternList : List Tm → Bool
  | [] => true
  | t :: ts => isPattern t && isPatternList ts
end

mutual
/-- The nesting depth of a term. -/
def depth : Tm → Nat
  | .expr items => depthList items + 1
  | .held t => depth t + 1
  | .val t => depth t + 1
  | _ => 0

def depthList : List Tm → Nat
  | [] => 0
  | t :: ts => max (depth t) (depthList ts)
end

/-- Bindings whose terms are all ground. -/
def GroundBinds (θ : List (String × Tm)) : Prop := ∀ q ∈ θ, isGround q.2 = true

theorem groundBinds_nil : GroundBinds [] := fun _ h => absurd h List.not_mem_nil

theorem groundBinds_cons {x : String} {t : Tm} {θ : List (String × Tm)} (ht : isGround t = true)
    (hθ : GroundBinds θ) : GroundBinds ((x, t) :: θ) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ht
  · exact hθ q hq

mutual
theorem inst_ground (θ : List (String × Tm)) : ∀ t, isGround t = true → inst θ t = t
  | .sym _, _ => rfl
  | .num _, _ => rfl
  | .str _, _ => rfl
  | .expr items, h => by
      simp only [isGround] at h
      simp only [inst]
      rw [instList_ground θ items h]
  | .var _, h => by simp [isGround] at h
  | .held _, h => by simp [isGround] at h
  | .val _, h => by simp [isGround] at h
  | .cell _, h => by simp [isGround] at h

theorem instList_ground (θ : List (String × Tm)) :
    ∀ ts, isGroundList ts = true → instList θ ts = ts
  | [], _ => rfl
  | t :: ts, h => by
      simp only [isGroundList, Bool.and_eq_true] at h
      simp only [instList]
      rw [inst_ground θ t h.1, instList_ground θ ts h.2]
end

mutual
theorem occurs_ground (x : String) : ∀ t, isGround t = true → occurs x t = false
  | .sym _, _ => rfl
  | .num _, _ => rfl
  | .str _, _ => rfl
  | .expr items, h => by
      simp only [isGround] at h
      simp only [occurs]
      exact occursList_ground x items h
  | .var _, h => by simp [isGround] at h
  | .held _, h => by simp [isGround] at h
  | .val _, h => by simp [isGround] at h
  | .cell _, h => by simp [isGround] at h

theorem occursList_ground (x : String) :
    ∀ ts, isGroundList ts = true → occursList x ts = false
  | [], _ => rfl
  | t :: ts, h => by
      simp only [isGroundList, Bool.and_eq_true] at h
      simp only [occursList, occurs_ground x t h.1, occursList_ground x ts h.2, Bool.or_self]
end

/-- Binding a variable to a ground term, over ground bindings, only adds the binding. -/
theorem bindVar_ground (st : Store) (x : String) {u : Tm} (hθ : GroundBinds st.binds) :
    st.bindVar x u = { st with binds := (x, u) :: st.binds } := by
  unfold Store.bindVar
  congr 2
  conv => rhs; rw [← List.map_id st.binds]
  apply List.map_congr_left
  intro q hq
  rw [inst_ground _ _ (hθ q hq)]
  rfl

theorem depth_le_of_mem {t : Tm} : ∀ {ts : List Tm}, t ∈ ts → depth t ≤ depthList ts
  | _ :: _, .head _ => by simp only [depthList]; exact Nat.le_max_left _ _
  | _ :: _, .tail _ h => by
      simp only [depthList]
      exact Nat.le_trans (depth_le_of_mem h) (Nat.le_max_right _ _)

theorem depthList_tail_le (t : Tm) (ts : List Tm) : depthList ts ≤ depthList (t :: ts) := by
  simp only [depthList]; exact Nat.le_max_right _ _

theorem depth_head_le (t : Tm) (ts : List Tm) : depth t ≤ depthList (t :: ts) := by
  simp only [depthList]; exact Nat.le_max_left _ _

theorem matchList_length : ∀ (ps ts : List Tm) (σ σ' : List (String × Tm)),
    matchList ps ts σ = some σ' → ps.length = ts.length
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp [matchList] at h
  | _ :: _, [], _, _, h => by simp [matchList] at h
  | p :: ps, t :: ts, σ, σ', h => by
      simp only [matchList] at h
      cases hm : matchTm p t σ with
      | none => rw [hm] at h; simp at h
      | some σ₁ =>
          rw [hm] at h
          simp only [List.length_cons, matchList_length ps ts σ₁ σ' h]

mutual
/-- Matching against a ground term binds only ground terms. -/
theorem matchTm_groundBinds : ∀ (p t : Tm) (σ σ' : List (String × Tm)), isGround t = true →
    GroundBinds σ → matchTm p t σ = some σ' → GroundBinds σ'
  | .var x, t, σ, σ', ht, hσ, h => by
      simp only [matchTm] at h
      cases hl : lookupVar σ x with
      | some u =>
          rw [hl] at h
          simp only at h
          split at h
          · simp only [Option.some.injEq] at h; subst h; exact hσ
          · simp at h
      | none =>
          rw [hl] at h
          simp only [Option.some.injEq] at h
          subst h
          exact groundBinds_cons ht hσ
  | .expr ps, .expr ts, σ, σ', ht, hσ, h => by
      simp only [matchTm] at h
      simp only [isGround] at ht
      exact matchList_groundBinds ps ts σ σ' ht hσ h
  | .expr _, .sym _, σ, σ', _, hσ, h | .expr _, .num _, σ, σ', _, hσ, h
  | .expr _, .str _, σ, σ', _, hσ, h | .expr _, .var _, σ, σ', _, hσ, h
  | .expr _, .held _, σ, σ', _, hσ, h | .expr _, .val _, σ, σ', _, hσ, h
  | .expr _, .cell _, σ, σ', _, hσ, h | .sym _, _, σ, σ', _, hσ, h | .num _, _, σ, σ', _, hσ, h
  | .str _, _, σ, σ', _, hσ, h | .held _, _, σ, σ', _, hσ, h | .val _, _, σ, σ', _, hσ, h
  | .cell _, _, σ, σ', _, hσ, h => by
      simp only [matchTm] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; exact hσ
      · simp at h

theorem matchList_groundBinds : ∀ (ps ts : List Tm) (σ σ' : List (String × Tm)),
    isGroundList ts = true → GroundBinds σ → matchList ps ts σ = some σ' → GroundBinds σ'
  | [], [], σ, σ', _, hσ, h => by
      simp only [matchList, Option.some.injEq] at h; subst h; exact hσ
  | [], _ :: _, _, _, _, _, h => by simp [matchList] at h
  | _ :: _, [], _, _, _, _, h => by simp [matchList] at h
  | p :: ps, t :: ts, σ, σ', ht, hσ, h => by
      simp only [isGroundList, Bool.and_eq_true] at ht
      simp only [matchList] at h
      cases hm : matchTm p t σ with
      | none => rw [hm] at h; simp at h
      | some σ₁ =>
          rw [hm] at h
          exact matchList_groundBinds ps ts σ₁ σ' ht.2
            (matchTm_groundBinds p t σ σ₁ ht.1 hσ hm) h
end

section Unification

variable (force : Nat → M Tm)

theorem unifyM_succ (n : Nat) (ra : Role) (a : Tm) (rb : Role) (b : Tm) (st : Store) :
    unifyM force (n + 1) ra a rb b st =
      runUStep force (unifyM force n) (ustep st.binds ra a rb b) st := rfl

theorem unifyPairs_cons (u : Tm → Tm → M Unit) (a b : Tm) (rest : List (Tm × Tm)) (st : Store) :
    unifyPairs u ((a, b) :: rest) st = (u a b st).flatMap (Out.next fun _ => unifyPairs u rest) :=
  rfl

theorem groundBinds_lookup {θ : List (String × Tm)} {x : String} {u : Tm} (hθ : GroundBinds θ)
    (h : lookupVar θ x = some u) : isGround u = true := by
  unfold lookupVar at h
  cases hf : θ.find? (fun p => p.1 == x) with
  | none => rw [hf] at h; simp at h
  | some q =>
      rw [hf] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact hθ q (List.mem_of_find?_eq_some hf)

/-- **Two ground terms unify exactly when they are equal**, and unifying them binds nothing. -/
theorem unify_ground_ground (m : Nat) (ra rb : Role) : ∀ (u t : Tm) (st : Store), isGround u = true →
    isGround t = true → depth t < m →
    unifyM force m ra u rb t st = if u = t then [.ok () st] else [] := by
  induction m with
  | zero => intro u t st _ _ hd; exact absurd hd (Nat.not_lt_zero _)
  | succ m ih =>
    have hl : ∀ (us ts : List Tm) (st : Store), isGroundList us = true →
        isGroundList ts = true → depthList ts < m → us.length = ts.length →
        unifyPairs (fun x y => unifyM force m ra x rb y) (us.zip ts) st =
          if us = ts then [.ok () st] else [] := by
      intro us
      induction us with
      | nil =>
          intro ts st _ _ _ hlen
          cases ts with
          | nil => simp [unifyPairs, M.pure]
          | cons => simp at hlen
      | cons u us ihl =>
          intro ts st hu ht hd hlen
          cases ts with
          | nil => simp at hlen
          | cons t ts =>
              simp only [isGroundList, Bool.and_eq_true] at hu ht
              simp only [List.zip_cons_cons]
              rw [unifyPairs_cons, ih u t st hu.1 ht.1
                (Nat.lt_of_le_of_lt (depth_head_le t ts) hd)]
              by_cases e : u = t
              · subst e
                simp only [if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil,
                  Out.next]
                rw [ihl ts st hu.2 ht.2 (Nat.lt_of_le_of_lt (depthList_tail_le u ts) hd)
                  (by simpa using hlen)]
                simp
              · simp [e]
    intro u t st hu ht hd
    rw [unifyM_succ]
    cases u <;> cases t <;> simp only [isGround, Bool.false_eq_true] at hu ht
    all_goals (simp only [ustep]; split <;> simp_all [runUStep, M.pure])
    · exact hl _ _ st hu ht (by simp only [depth] at hd; omega) (by assumption)
    · intro e; simp_all

theorem ustep_var_ground (θ : List (String × Tm)) (ra rb : Role) (x : String) {t : Tm}
    (ht : isGround t = true) :
    ustep θ ra (.var x) rb t =
      match lookupVar θ x with
      | some u => .again ra u rb t
      | none => .bind x rb t := by
  cases t <;> simp only [isGround, Bool.false_eq_true] at ht <;> simp only [ustep] <;>
    cases lookupVar θ x <;> rfl

theorem ustep_expr_ground (θ : List (String × Tm)) (ra rb : Role) (ps : List Tm) {t : Tm}
    (ht : isGround t = true) :
    ustep θ ra (.expr ps) rb t =
      match t with
      | .expr ts => if ps.length = ts.length then .items ra rb (ps.zip ts) else .fail
      | _ => .fail := by
  cases t <;> simp only [isGround, Bool.false_eq_true] at ht <;> simp [ustep]

/-- **One-way matching is unification against a ground target.** For a pattern `p` and a ground
term `t`, over ground bindings and with fuel deeper than `t`, unification has exactly the outcome
of matching `p` against `t`: one success with the bindings matching gives, or no outcome. -/
theorem unify_ground_eq_match (n : Nat) : ∀ (p t : Tm) (st : Store), isPattern p = true →
    isGround t = true → GroundBinds st.binds → depth t + 1 < n →
    unifyM force n .plain p .plain t st =
      match matchTm p t st.binds with
      | some σ => [.ok () { st with binds := σ }]
      | none => [] := by
  induction n with
  | zero => intro p t st _ _ _ hd; exact absurd hd (Nat.not_lt_zero _)
  | succ n ih =>
    have hl : ∀ (ps ts : List Tm) (st : Store), isPatternList ps = true →
        isGroundList ts = true → GroundBinds st.binds → depthList ts + 1 < n →
        ps.length = ts.length →
        unifyPairs (fun x y => unifyM force n .plain x .plain y) (ps.zip ts) st =
          match matchList ps ts st.binds with
          | some σ => [.ok () { st with binds := σ }]
          | none => [] := by
      intro ps
      induction ps with
      | nil =>
          intro ts st _ _ _ _ hlen
          cases ts with
          | nil => rfl
          | cons => simp at hlen
      | cons p ps ihl =>
          intro ts st hp ht hθ hd hlen
          cases ts with
          | nil => simp at hlen
          | cons t ts =>
              simp only [isPatternList, isGroundList, Bool.and_eq_true] at hp ht
              simp only [List.zip_cons_cons]
              rw [unifyPairs_cons, ih p t st hp.1 ht.1 hθ
                (by have := depth_head_le t ts; omega)]
              simp only [matchList]
              cases hm : matchTm p t st.binds with
              | none => rfl
              | some σ₁ =>
                  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Out.next]
                  rw [ihl ts { st with binds := σ₁ } hp.2 ht.2
                    (matchTm_groundBinds p t st.binds σ₁ ht.1 hθ hm)
                    (by have := depthList_tail_le t ts; omega) (by simpa using hlen)]
    intro p t st hp ht hθ hd
    rw [unifyM_succ]
    cases p with
    | var x =>
        rw [ustep_var_ground _ _ _ x ht]
        cases hx : lookupVar st.binds x with
        | some u =>
            simp only [runUStep]
            rw [unify_ground_ground force n .plain .plain u t st (groundBinds_lookup hθ hx) ht (by omega)]
            simp only [matchTm, hx]
            by_cases e : u = t
            · subst e; simp
            · simp [e]
        | none =>
            simp only [runUStep, bindTo, inst_ground _ _ ht, occurs_ground _ _ ht, Role.wrap,
              bindVar_ground _ _ hθ, matchTm, hx]
            simp
    | expr ps =>
        rw [ustep_expr_ground _ _ _ ps ht]
        cases t with
        | expr ts =>
            simp only [isPattern] at hp
            simp only [isGround] at ht
            simp only [depth] at hd
            simp only [matchTm]
            by_cases hlen : ps.length = ts.length
            · rw [if_pos hlen]
              exact hl ps ts st hp ht hθ (by omega) hlen
            · rw [if_neg hlen]
              cases hm : matchList ps ts st.binds with
              | none => rfl
              | some σ => exact absurd (matchList_length ps ts _ σ hm) hlen
        | sym _ => simp [runUStep, matchTm]
        | num _ => simp [runUStep, matchTm]
        | str _ => simp [runUStep, matchTm]
        | var _ => simp [isGround] at ht
        | held _ => simp [isGround] at ht
        | val _ => simp [isGround] at ht
        | cell _ => simp [isGround] at ht
    | sym _ | num _ | str _ =>
        cases t <;> simp only [isGround, Bool.false_eq_true] at ht <;>
          simp only [ustep, runUStep, matchTm] <;> split <;>
          simp_all [M.pure]
    | held _ => simp [isPattern] at hp
    | val _ => simp [isPattern] at hp
    | cell _ => simp [isPattern] at hp

/-- **A variable parameter takes a running argument without running it**: unifying an unbound
variable with a need cell binds the variable to the cell and forces nothing. -/
theorem unify_var_cell (n : Nat) (x : String) (i : Nat) (st : Store)
    (hx : lookupVar st.binds x = none) :
    unifyM force (n + 1) .plain (.var x) .plain (.cell i) st = [.ok () (st.bindVar x (.cell i))] := by
  simp [unifyM_succ, ustep, hx, runUStep, bindTo, inst, occurs, Role.wrap]

/-- **A variable parameter takes held syntax as it is**: unifying an unbound variable with held
code `t` (no variables, cells or roles) binds the variable to the held code. -/
theorem unify_var_held (n : Nat) (x : String) (t : Tm) (st : Store)
    (hx : lookupVar st.binds x = none) (ht : isGround t = true) :
    unifyM force (n + 2) .plain (.var x) .plain (.held t) st =
      [.ok () (st.bindVar x (asHeld t))] := by
  rw [unifyM_succ]
  simp only [ustep, runUStep]
  rw [unifyM_succ, ustep_var_ground _ _ _ x ht, hx]
  simp only [runUStep, bindTo, inst_ground _ _ ht, occurs_ground _ _ ht, Role.wrap]
  simp


/-- Bindings `σ` with every term put in role `r`. -/
def wrapBinds (r : Role) (σ : List (String × Tm)) : List (String × Tm) :=
  σ.map fun q => (q.1, r.wrap q.2)

theorem lookupVar_wrapBinds (r : Role) (σ : List (String × Tm)) (x : String) :
    lookupVar (wrapBinds r σ) x = (lookupVar σ x).map r.wrap := by
  simp [wrapBinds, lookupVar, List.find?_map, Function.comp_def, Option.map_map]

/-- A ground term in a role: plain, held or a value. -/
theorem wrap_ground (r : Role) {u : Tm} (hu : isGround u = true) :
    r.wrap u = match r with
      | .plain => u
      | .held => .held u
      | .val => .val u := by
  cases r <;> cases u <;> simp_all [isGround, Role.wrap, asHeld, asVal]

theorem inst_wrap_ground (θ : List (String × Tm)) (r : Role) {u : Tm} (hu : isGround u = true) :
    inst θ (r.wrap u) = r.wrap u := by
  rw [wrap_ground r hu]
  cases r <;> simp only [inst, inst_ground θ u hu]

/-- Binding a variable over bindings that it leaves as they are only adds the binding. -/
theorem bindVar_of_fixed (st : Store) (x : String) (u : Tm)
    (h : ∀ q ∈ st.binds, inst [(x, u)] q.2 = q.2) :
    st.bindVar x u = { st with binds := (x, u) :: st.binds } := by
  unfold Store.bindVar
  congr 2
  conv => rhs; rw [← List.map_id st.binds]
  apply List.map_congr_left
  intro q hq
  rw [h q hq]
  rfl

theorem wrapBinds_fixed (r : Role) {σ : List (String × Tm)} (hσ : GroundBinds σ) (x : String)
    (u : Tm) : ∀ q ∈ wrapBinds r σ, inst [(x, u)] q.2 = q.2 := by
  intro q hq
  simp only [wrapBinds, List.mem_map] at hq
  obtain ⟨q', hq', rfl⟩ := hq
  exact inst_wrap_ground _ r (hσ q' hq')

/-- **A ground term in a role unifies with a ground term exactly when they are equal.** Entering
the role costs one step of fuel. -/
theorem unify_wrap_ground (m : Nat) (r ra rb : Role) (u t : Tm) (st : Store)
    (hu : isGround u = true) (ht : isGround t = true) (hd : depth t + 1 < m) :
    unifyM force m ra (r.wrap u) rb t st = if u = t then [.ok () st] else [] := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [wrap_ground r hu]
  cases r with
  | plain => exact unify_ground_ground force (k + 1) ra rb u t st hu ht (by omega)
  | held =>
      rw [unifyM_succ]
      simp only [ustep, runUStep]
      exact unify_ground_ground force k .held rb u t st hu ht (by omega)
  | val =>
      rw [unifyM_succ]
      simp only [ustep, runUStep]
      exact unify_ground_ground force k .val rb u t st hu ht (by omega)

/-- **One-way matching is unification against a ground target, in any role.** With the target
read in role `r`, as `match` reads a row in the reading's role, unification has exactly the
outcome of matching, each binding carrying the role. -/
theorem unify_ground_eq_match_in_role (r : Role) (n : Nat) : ∀ (p t : Tm)
    (σ : List (String × Tm)) (st : Store), isPattern p = true → isGround t = true →
    GroundBinds σ → st.binds = wrapBinds r σ → depth t + 2 < n →
    unifyM force n .plain p r t st =
      match matchTm p t σ with
      | some σ' => [.ok () { st with binds := wrapBinds r σ' }]
      | none => [] := by
  induction n with
  | zero => intro p t σ st _ _ _ _ hd; exact absurd hd (Nat.not_lt_zero _)
  | succ n ih =>
    have hl : ∀ (ps ts : List Tm) (σ : List (String × Tm)) (st : Store),
        isPatternList ps = true → isGroundList ts = true → GroundBinds σ →
        st.binds = wrapBinds r σ → depthList ts + 2 < n → ps.length = ts.length →
        unifyPairs (fun x y => unifyM force n .plain x r y) (ps.zip ts) st =
          match matchList ps ts σ with
          | some σ' => [.ok () { st with binds := wrapBinds r σ' }]
          | none => [] := by
      intro ps
      induction ps with
      | nil =>
          intro ts σ st _ _ _ hst _ hlen
          cases ts with
          | nil =>
              simp only [List.zip_nil_left, unifyPairs, M.pure, matchList, ← hst]
          | cons => simp at hlen
      | cons p ps ihl =>
          intro ts σ st hp ht hσ hst hd hlen
          cases ts with
          | nil => simp at hlen
          | cons t ts =>
              simp only [isPatternList, isGroundList, Bool.and_eq_true] at hp ht
              simp only [List.zip_cons_cons]
              rw [unifyPairs_cons, ih p t σ st hp.1 ht.1 hσ hst
                (by have := depth_head_le t ts; omega)]
              simp only [matchList]
              cases hm : matchTm p t σ with
              | none => rfl
              | some σ₁ =>
                  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Out.next]
                  rw [ihl ts σ₁ { st with binds := wrapBinds r σ₁ } hp.2 ht.2
                    (matchTm_groundBinds p t σ σ₁ ht.1 hσ hm) rfl
                    (by have := depthList_tail_le t ts; omega) (by simpa using hlen)]
    intro p t σ st hp ht hσ hst hd
    rw [unifyM_succ]
    cases p with
    | var x =>
        rw [ustep_var_ground _ _ _ x ht, hst, lookupVar_wrapBinds]
        cases hx : lookupVar σ x with
        | some u =>
            simp only [Option.map_some, runUStep]
            rw [unify_wrap_ground force n r .plain r u t st (groundBinds_lookup hσ hx) ht
              (by omega)]
            simp only [matchTm, hx]
            by_cases e : u = t
            · subst e; simp [← hst]
            · simp [e]
        | none =>
            simp only [Option.map_none, runUStep, bindTo, inst_ground _ _ ht,
              occurs_ground _ _ ht, matchTm, hx]
            rw [bindVar_of_fixed st x _ (hst ▸ wrapBinds_fixed r hσ x _), hst]
            simp [wrapBinds]
    | expr ps =>
        rw [ustep_expr_ground _ _ _ ps ht]
        cases t with
        | expr ts =>
            simp only [isPattern] at hp
            simp only [isGround] at ht
            simp only [depth] at hd
            simp only [matchTm]
            by_cases hlen : ps.length = ts.length
            · rw [if_pos hlen]
              exact hl ps ts σ st hp ht hσ hst (by omega) hlen
            · rw [if_neg hlen]
              cases hm : matchList ps ts σ with
              | none => rfl
              | some σ' => exact absurd (matchList_length ps ts _ σ' hm) hlen
        | sym _ => simp [runUStep, matchTm]
        | num _ => simp [runUStep, matchTm]
        | str _ => simp [runUStep, matchTm]
        | var _ => simp [isGround] at ht
        | held _ => simp [isGround] at ht
        | val _ => simp [isGround] at ht
        | cell _ => simp [isGround] at ht
    | sym _ | num _ | str _ =>
        obtain ⟨sp, ce, bi, fr⟩ := st
        simp only at hst
        subst hst
        cases t <;> simp only [isGround, Bool.false_eq_true] at ht <;>
          simp only [ustep, runUStep, matchTm] <;> split <;>
          simp_all [M.pure]
    | held _ => simp [isPattern] at hp
    | val _ => simp [isPattern] at hp
    | cell _ => simp [isPattern] at hp


/-- What a parameter receives from `bindOne` when the argument runs or is held: a need cell, or
held syntax. -/
def Received (a : Tm) : Prop := (∃ i, a = .cell i) ∨ (∃ t, a = .held t ∧ isGround t = true)

theorem lookupVar_cons_ne {x y : String} {u : Tm} {θ : List (String × Tm)} (h : y ≠ x) :
    lookupVar ((x, u) :: θ) y = lookupVar θ y := by
  simp [lookupVar, Ne.symm h]

theorem lookupVar_mapSnd (θ : List (String × Tm)) (f : Tm → Tm) (y : String) :
    lookupVar (θ.map fun q => (q.1, f q.2)) y = (lookupVar θ y).map f := by
  simp [lookupVar, List.find?_map, Function.comp_def, Option.map_map]

/-- A variable parameter takes what it received, a cell or held syntax, without running it. -/
theorem unify_var_received (n : Nat) (x : String) (a : Tm) (st : Store)
    (hx : lookupVar st.binds x = none) (ha : Received a) :
    unifyM force (n + 2) .plain (.var x) .plain a st = [.ok () (st.bindVar x a)] := by
  rcases ha with ⟨i, rfl⟩ | ⟨t, rfl, ht⟩
  · exact unify_var_cell force (n + 1) x i st hx
  · rw [unify_var_held force n x t st hx ht]
    cases t <;> simp_all [isGround, asHeld]

/-- **A head of distinct variables binds each parameter to what it received**, cell or held
syntax, in order, running nothing: on such heads unification is the substitution of the received
terms for the parameters. -/
theorem unify_head_vars (n : Nat) : ∀ (xs : List String) (as : List Tm) (st : Store),
    xs.Nodup → xs.length = as.length → (∀ x ∈ xs, lookupVar st.binds x = none) →
    (∀ a ∈ as, Received a) →
    unifyPairs (fun p a => unifyM force (n + 2) .plain p .plain a) ((xs.map Tm.var).zip as) st =
      [.ok () ((xs.zip as).foldl (fun s q => s.bindVar q.1 q.2) st)]
  | [], [], st, _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _ => by simp at h
  | x :: xs, a :: as, st, hnd, hlen, hun, hrec => by
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [unifyPairs_cons, unify_var_received force n x a st (hun x List.mem_cons_self)
        (hrec a List.mem_cons_self)]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Out.next]
      have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
      refine unify_head_vars n xs as (st.bindVar x a) (List.nodup_cons.mp hnd).2
        (by simpa using hlen) ?_ (fun b m => hrec b (List.mem_cons_of_mem _ m))
      intro y hy
      have hyx : y ≠ x := fun e => hx (e ▸ hy)
      simp only [Store.bindVar]
      rw [lookupVar_cons_ne hyx, lookupVar_mapSnd, hun y (List.mem_cons_of_mem _ hy)]
      rfl

/-- The examples of the module header, computed: `(fact 1 $v)` against `(fact 1 2)` binds `$v`
to `2`; `(pair $a $a)` has no outcome against `(pair 3 4)` and binds `$a` once against
`(pair 3 3)`; against a target with a variable, `(fact $y 2)`, one-way matching fails while
unification binds both sides. -/
theorem matching_examples :
    unifyM force 4 .plain (.expr [.sym "fact", .num 1, .var "v"]) .plain
        (.expr [.sym "fact", .num 1, .num 2]) (Store.init []) =
      [.ok () { Store.init [] with binds := [("v", .num 2)] }] ∧
    matchTm (.expr [.sym "fact", .num 1, .var "v"]) (.expr [.sym "fact", .num 1, .num 2]) [] =
      some [("v", .num 2)] ∧
    unifyM force 4 .plain (.expr [.sym "pair", .var "a", .var "a"]) .plain
        (.expr [.sym "pair", .num 3, .num 4]) (Store.init []) = [] ∧
    unifyM force 4 .plain (.expr [.sym "pair", .var "a", .var "a"]) .plain
        (.expr [.sym "pair", .num 3, .num 3]) (Store.init []) =
      [.ok () { Store.init [] with binds := [("a", .num 3)] }] ∧
    matchTm (.expr [.sym "fact", .num 1, .var "v"]) (.expr [.sym "fact", .var "y", .num 2]) [] =
      none ∧
    unifyM force 4 .plain (.expr [.sym "fact", .num 1, .var "v"]) .plain
        (.expr [.sym "fact", .var "y", .num 2]) (Store.init []) =
      [.ok () { Store.init [] with binds := [("v", .num 2), ("y", .num 1)] }] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

mutual
theorem inst_nil : ∀ t : Tm, inst [] t = t
  | .var _ => rfl
  | .expr items => by simp only [inst]; rw [instList_nil items]
  | .held t => by simp only [inst]; rw [inst_nil t]
  | .val t => by simp only [inst]; rw [inst_nil t]
  | .sym _ => rfl
  | .num _ => rfl
  | .str _ => rfl
  | .cell _ => rfl

theorem instList_nil : ∀ ts : List Tm, instList [] ts = ts
  | [] => rfl
  | t :: ts => by simp only [instList]; rw [inst_nil t, instList_nil ts]
end

mutual
theorem rename_ground (k : Nat) : ∀ t : Tm, isGround t = true → rename k t = t
  | .sym _, _ => rfl
  | .num _, _ => rfl
  | .str _, _ => rfl
  | .expr items, h => by
      simp only [isGround] at h
      simp only [rename]
      rw [renameList_ground k items h]
  | .var _, h => by simp [isGround] at h
  | .held _, h => by simp [isGround] at h
  | .val _, h => by simp [isGround] at h
  | .cell _, h => by simp [isGround] at h

theorem renameList_ground (k : Nat) : ∀ ts : List Tm, isGroundList ts = true → renameList k ts = ts
  | [], _ => rfl
  | t :: ts, h => by
      simp only [isGroundList, Bool.and_eq_true] at h
      simp only [renameList]
      rw [rename_ground k t h.1, renameList_ground k ts h.2]
end

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.flatMap_cons]
      rw [h a List.mem_cons_self, ih fun b m => h b (List.mem_cons_of_mem _ m)]

end Unification

/-- **On ground rows, `match` is one-way matching.** From a store without bindings, over a space
whose rows are ground, `(match &self p template)` runs the template once for each row that `p`
matches one-way, in row order, with the matching bindings in the reading's role (`bindRole`). -/
theorem match_ground_rows (R : Reading) (check : Verdicts) (n : Nat) (p template : Tm)
    (st : Store) (hp : isPattern p = true) (hb : st.binds = [])
    (hrows : ∀ row ∈ st.space, isGround row = true ∧ depth row + 2 < n) :
    eval R check (n + 1) (.expr [.sym "match", .sym "&self", p, template]) st =
      st.space.flatMap fun row =>
        match matchTm p row [] with
        | some σ => eval R check n template
            { st with binds := wrapBinds R.bindRole σ, fresh := st.fresh + 1 }
        | none => [] := by
  have hstep : eval R check (n + 1) (.expr [.sym "match", .sym "&self", p, template]) st =
      st.space.flatMap fun row =>
        M.bind (unifyM (forceWith R check (eval R check n)) n .plain (inst st.binds p)
            R.bindRole (rename st.fresh row))
          (fun _ => eval R check n (inst st.binds template)) { st with fresh := st.fresh + 1 } :=
    rfl
  rw [hstep, hb, inst_nil, inst_nil]
  apply flatMap_congr_mem
  intro row hrow
  obtain ⟨hg, hd⟩ := hrows row hrow
  rw [rename_ground _ _ hg]
  simp only [M.bind]
  rw [unify_ground_eq_match_in_role _ R.bindRole n p row []
    { space := st.space, cells := st.cells, binds := [], fresh := st.fresh + 1 } hp hg
    groundBinds_nil (by simp [wrapBinds]) hd]
  cases matchTm p row [] with
  | none => rfl
  | some σ => simp [Out.next]



/-! ## Reading rows: law 3 on ground rows -/

/-- **Reading a ground row runs nothing, under `stay` and `forward`**: the answers of
`(match &self p $x)` are, for each row that `p` matches one-way, the part bound to `$x` in the
value role (or `$x` itself when `p` does not bind it), in row order. -/
theorem match_reads_values (R : Reading) (hR : R.bindRole = .val) (check : Verdicts) (n : Nat)
    (p : Tm) (x : String) (st : Store) (hp : isPattern p = true) (hb : st.binds = [])
    (hrows : ∀ row ∈ st.space, isGround row = true ∧ depth row + 2 < n + 1) :
    eval R check (n + 2) (.expr [.sym "match", .sym "&self", p, .var x]) st =
      st.space.flatMap fun row =>
        match matchTm p row [] with
        | some σ => [.ok (((lookupVar σ x).map asVal).getD (.var x))
            { st with binds := wrapBinds .val σ, fresh := st.fresh + 1 }]
        | none => [] := by
  rw [match_ground_rows R check (n + 1) p (.var x) st hp hb hrows]
  apply flatMap_congr_mem
  intro row hrow
  cases hm : matchTm p row [] with
  | none => rfl
  | some σ =>
      have hσ : GroundBinds σ :=
        matchTm_groundBinds p row [] σ (hrows row hrow).1 groundBinds_nil hm
      simp only [hR]
      show stepForm R check (eval R check n) n
          (classify (inst (wrapBinds .val σ) (.var x))) _ = _
      simp only [inst, lookupVar_wrapBinds]
      cases hx : lookupVar σ x with
      | none => rfl
      | some u =>
          have hu : isGround u = true := groundBinds_lookup hσ hx
          simp only [Option.map_some, Option.getD_some]
          rw [wrap_ground .val hu]
          have hv : asVal u = .val u := by cases u <;> simp_all [isGround, asVal]
          rw [hv]
          rfl

/-- **Under `substitute`, reading a ground row runs it**: for each row that `p` matches, the part
bound to `$x` is evaluated as code. -/
theorem match_runs_reads (R : Reading) (hR : R.bindRole = .plain) (check : Verdicts) (n : Nat)
    (p : Tm) (x : String) (st : Store) (hp : isPattern p = true) (hb : st.binds = [])
    (hrows : ∀ row ∈ st.space, isGround row = true ∧ depth row + 2 < n + 1) :
    eval R check (n + 2) (.expr [.sym "match", .sym "&self", p, .var x]) st =
      st.space.flatMap fun row =>
        match matchTm p row [] with
        | some σ => eval R check (n + 1) ((lookupVar σ x).getD (.var x))
            { st with binds := σ, fresh := st.fresh + 1 }
        | none => [] := by
  rw [match_ground_rows R check (n + 1) p (.var x) st hp hb hrows]
  apply flatMap_congr_mem
  intro row hrow
  cases hm : matchTm p row [] with
  | none => rfl
  | some σ =>
      have hσ : GroundBinds σ :=
        matchTm_groundBinds p row [] σ (hrows row hrow).1 groundBinds_nil hm
      have hw : wrapBinds .plain σ = σ := by
        simp only [wrapBinds, Role.wrap]
        exact List.map_id' σ
      simp only [hR, hw]
      show stepForm R check (eval R check n) n (classify (inst σ (.var x))) _ =
        stepForm R check (eval R check n) n (classify (inst σ ((lookupVar σ x).getD (.var x)))) _
      cases hx : lookupVar σ x with
      | none => simp only [inst, hx, Option.getD_none]
      | some u =>
          have hu : isGround u = true := groundBinds_lookup hσ hx
          simp only [inst, hx, Option.getD_some, inst_ground σ u hu]

end Mettapedia.Languages.MeTTa.EvaluationControl.ParameterReadings
