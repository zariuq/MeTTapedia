import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramSource

/-!
# Adequacy of the program core on the step, determinism, and administrative termination

* **Adequacy** (`program_execution_iff`): from the rows of a program, the reference semantics reaches
  `W` exactly when a run of translated firings of the ordinary step reaches a configuration
  representing `W`. Each firing is one source step: there are no administrative firings on the step.
* **One thread** (`step_singleton`): a configuration of one row steps only by a rule with one take
  pattern and no read pattern.
* **Determinism up to choice** (`singleton_deterministic`): two steps of one row agree, unless the
  row evaluates a choice `amb`. The take patterns of different rules do not overlap
  (`overlap_free`), checked by a structural compatibility test on patterns (`compatible`,
  `compatible_of_inst`).
* **Administrative steps terminate** (`administrative_decreases`): the machine's administrative
  rules (lookup, pushing frames, forming values) strictly decrease a measure; only β, let binding,
  activation, choice, effects, suspension and definitions are not administrative.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program

open ProgramRows ProgramTranslation

/-! ## Adequacy -/

/-- **Adequacy of the program core.** -/
theorem program_execution_iff (l : List Sx) (W : Multiset Sx) :
    Relation.ReflTransGen Step (l : Multiset Sx) W ↔
      ∃ q : Config × ℕ, Relation.ReflTransGen (Translated schema) (initial l, 1) q ∧
        Represents q.1 W q.2 := by
  rw [step_eq_rewrites]
  exact execution_iff schema_wellFormed l W

/-- **Soundness for one step from any represented configuration.** -/
theorem step_sound {C : Config} {n : ℕ} {W W' : Multiset Sx} (rep : Represents C W n) (step : Step W W') :
    ∃ q : Config × ℕ, Translated schema (C, n) q ∧ Represents q.1 W' q.2 := by
  obtain ⟨i, fires⟩ := (step_iff_rewrites W W').mp step
  obtain ⟨taken, read, valid, rep'⟩ := sound (schema_wellFormed i) rep fires
  exact ⟨_, .fire i taken read valid, rep'⟩

/-- **Completeness for one firing from any represented configuration.** -/
theorem firing_complete {C : Config} {n : ℕ} {W : Multiset Sx} (rep : Represents C W n)
    {q : Config × ℕ} (firing : Translated schema (C, n) q) :
    ∃ W', Step W W' ∧ Represents q.1 W' q.2 := by
  cases firing with
  | fire i taken read valid =>
      obtain ⟨W', fires, rep'⟩ := complete (schema_wellFormed i) rep valid
      exact ⟨W', (step_iff_rewrites W W').mpr ⟨i, fires⟩, rep'⟩

/-- **A source state without steps has no translated firing.** -/
theorem stuck_of_source {C : Config} {n : ℕ} {W : Multiset Sx} (rep : Represents C W n)
    (stuck : ∀ W', ¬ Step W W') (q : Config × ℕ) : ¬ Translated schema (C, n) q := fun firing => by
  obtain ⟨W', step, -⟩ := firing_complete rep firing
  exact stuck W' step

/-! ## One thread -/

theorem card_push (l : List Sx) (F : Multiset Sx) : (push l F).card = l.length + F.card := by
  rw [push_eq, Multiset.card_add, Multiset.coe_card]

/-- Every rule takes a row. -/
theorem take_ne_nil (i : RuleName) : (schema i).take ≠ [] := by
  cases i <;> simp [schema]

/-- **A schema fires on one row only through one take pattern and no read pattern.** -/
theorem fires_singleton {r : Schema} (taking : r.take ≠ []) {s : Sx} {W' : Multiset Sx} :
    r.Fires {s} W' ↔
      ∃ (p : Pat) (θ : ℕ → Sx), r.take = [p] ∧ r.read = [] ∧ p.inst θ = s ∧
        W' = push (r.make.map (Pat.inst θ)) 0 := by
  constructor
  · rintro ⟨θ, F, hW, rfl⟩
    have card := congrArg Multiset.card hW
    rw [card_push, card_push, Multiset.card_singleton, List.length_map, List.length_map] at card
    obtain ⟨p, rest, hp⟩ := List.exists_cons_of_ne_nil taking
    rw [hp, List.length_cons] at card
    have restNil : rest = [] := List.length_eq_zero_iff.mp (by omega)
    have readNil : r.read = [] := List.length_eq_zero_iff.mp (by omega)
    have emptyF : F = 0 := Multiset.card_eq_zero.mp (by omega)
    subst restNil emptyF
    rw [hp, readNil] at hW
    refine ⟨p, θ, hp, readNil, ?_, by rw [readNil]; rfl⟩
    exact (Multiset.singleton_inj.mp hW).symm
  · rintro ⟨p, θ, hp, hr, rfl, rfl⟩
    refine ⟨θ, 0, ?_, ?_⟩
    · rw [hp, hr]; rfl
    · rw [hr]; rfl

/-- **One row steps only by a rule with one take pattern and no read pattern.** -/
theorem step_singleton {s : Sx} {W' : Multiset Sx} :
    Step {s} W' ↔ ∃ (i : RuleName) (p : Pat) (θ : ℕ → Sx), (schema i).take = [p] ∧ (schema i).read = [] ∧
      p.inst θ = s ∧ W' = push ((schema i).make.map (Pat.inst θ)) 0 := by
  rw [step_iff_rewrites]
  constructor
  · rintro ⟨i, fires⟩
    obtain ⟨p, θ, h⟩ := (fires_singleton (take_ne_nil i)).mp fires
    exact ⟨i, p, θ, h⟩
  · rintro ⟨i, p, θ, h⟩
    exact ⟨i, (fires_singleton (take_ne_nil i)).mpr ⟨p, θ, h⟩⟩

/-! ## Overlap of take patterns -/

/-- Two patterns can have a common instance only if they agree wherever both are rigid. -/
def compatible : Pat → Pat → Bool
  | .var _, _ => true
  | _, .var _ => true
  | .sym k, .sym k' => k == k'
  | .cell a b, .cell c d => compatible a c && compatible b d
  | .sym _, .cell _ _ => false
  | .cell _ _, .sym _ => false

/-- **Patterns with a common instance are compatible.** -/
theorem compatible_of_inst {θ θ' : ℕ → Sx} : ∀ (p q : Pat), p.inst θ = q.inst θ' → compatible p q = true
  | .var _, _, _ => by simp [compatible]
  | .sym _, .var _, _ => by simp [compatible]
  | .cell _ _, .var _, _ => by simp [compatible]
  | .sym k, .sym k', h => by
      simp only [Pat.inst, Sx.sym.injEq] at h
      simp [compatible, h]
  | .cell a b, .cell c d, h => by
      simp only [Pat.inst, Sx.cell.injEq] at h
      simp [compatible, compatible_of_inst a c h.1, compatible_of_inst b d h.2]
  | .sym _, .cell _ _, h => by simp [Pat.inst] at h
  | .cell _ _, .sym _, h => by simp [Pat.inst] at h

/-- Every rule name. -/
def allRules : List RuleName :=
  [.varZero, .varSucc, .lam, .app, .appL, .beta, .let_, .letK, .quote, .activate, .activateK, .atom,
    .ambL, .ambR, .add, .addK, .remove, .removeK, .await, .demand, .demandK, .resume, .call, .redefine]

theorem mem_allRules (i : RuleName) : i ∈ allRules := by
  cases i <;> simp [allRules]

/-- The two choice rules. -/
def choicePair (i j : RuleName) : Bool :=
  (i == .ambL && j == .ambR) || (i == .ambR && j == .ambL)

/-- The single take patterns of distinct rules are incompatible, except for the two choice rules. -/
def overlapCheck : Bool :=
  allRules.all fun i => allRules.all fun j =>
    match (schema i).take, (schema j).take with
    | [p], [q] => !(compatible p q) || i == j || choicePair i j
    | _, _ => true

theorem overlapCheck_true : overlapCheck = true := by decide

/-- **The take patterns do not overlap, except for choice.** -/
theorem overlap_free {i j : RuleName} {p q : Pat} (hi : (schema i).take = [p]) (hj : (schema j).take = [q])
    (compat : compatible p q = true) : i = j ∨ choicePair i j = true := by
  have all := overlapCheck_true
  simp only [overlapCheck, List.all_eq_true] at all
  have check := all i (mem_allRules i) j (mem_allRules j)
  rw [hi, hj] at check
  simp only [compat, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at check
  exact check

/-- **Two steps of one row agree, unless the row evaluates a choice.** -/
theorem singleton_deterministic {s : Sx} {W₁ W₂ : Multiset Sx} (one : Step {s} W₁) (two : Step {s} W₂) :
    W₁ = W₂ ∨ ∃ l r ρ κ, s = ev (amb l r) ρ κ := by
  obtain ⟨i, p, θ, hi, hri, hp, rfl⟩ := step_singleton.mp one
  obtain ⟨j, q, θ', hj, hrj, hq, rfl⟩ := step_singleton.mp two
  rcases overlap_free hi hj (compatible_of_inst p q (hp.trans hq.symm)) with same | choice
  · subst same
    rw [hi, List.cons.injEq] at hj
    obtain ⟨rfl, -⟩ := hj
    left
    have agree := Pat.inst_agree p (hp.trans hq.symm)
    congr 1
    refine List.map_congr_left fun m hm => Pat.inst_congr m fun x hx => ?_
    obtain ⟨p', hp', hx'⟩ := (schema_wellFormed i).covered m hm x hx
    rw [hi, hri, List.append_nil, List.mem_singleton] at hp'
    exact agree x (hp' ▸ hx')
  · right
    simp only [choicePair, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at choice
    rcases choice with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp only [schema, List.cons.injEq, and_true] at hi
      subst hi
      exact ⟨θ 0, θ 1, θ 2, θ 3, hp.symm⟩
    · simp only [schema, List.cons.injEq, and_true] at hi
      subst hi
      exact ⟨θ 0, θ 1, θ 2, θ 3, hp.symm⟩

/-- **The successors of a choice**: exactly its two branches. -/
theorem amb_successors {l r ρ κ : Sx} {W : Multiset Sx} (step : Step {ev (amb l r) ρ κ} W) :
    W = {ev l ρ κ} ∨ W = {ev r ρ κ} := by
  obtain ⟨i, p, θ, hi, -, hp, rfl⟩ := step_singleton.mp step
  have left : (schema .ambL).take = [p3 29 (p2 11 (.var 0) (.var 1)) (.var 2) (.var 3)] := rfl
  have compat := compatible_of_inst p (p3 29 (p2 11 (.var 0) (.var 1)) (.var 2) (.var 3))
    (θ' := args [l, r, ρ, κ]) (hp.trans rfl)
  rcases overlap_free hi left compat with same | choice
  · subst same
    simp only [schema, List.cons.injEq, and_true] at hi
    subst hi
    simp only [Pat.inst, p3, p2, ev, amb, t3, t2, Sx.cell.injEq] at hp
    obtain ⟨-, ⟨-, rfl, rfl⟩, rfl, rfl⟩ := hp
    left; rfl
  · simp only [choicePair, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at choice
    rcases choice with ⟨-, h⟩ | ⟨rfl, -⟩
    · cases h
    · simp only [schema, List.cons.injEq, and_true] at hi
      subst hi
      simp only [Pat.inst, p3, p2, ev, amb, t3, t2, Sx.cell.injEq] at hp
      obtain ⟨-, ⟨-, rfl, rfl⟩, rfl, rfl⟩ := hp
      right; rfl

/-! ## Administrative steps terminate -/

/-- The size of a row. -/
def size : Sx → ℕ
  | .sym _ => 1
  | .cell a b => size a + size b + 1

/-- The pending argument evaluations at the top of a continuation. -/
def frames : Sx → ℕ
  | .cell (.sym k) (.cell (.cell (.sym k') (.cell a _)) κ) =>
      if k = 21 ∧ k' = 22 then 3 * size a + 2 + frames κ else 0
  | _ => 0

/-- The administrative measure of a row: threads only. -/
def threadMeasure : Sx → ℕ
  | .cell (.sym k) (.cell a b) =>
      if k = 29 then (match b with | .cell _ κ => 3 * size a + frames κ + 1 | .sym _ => 0)
      else if k = 30 then frames b else 0
  | _ => 0

/-- The administrative measure of a configuration. -/
def measure (W : Multiset Sx) : ℕ := (W.map threadMeasure).sum

/-- The administrative rules: lookup, pushing frames and forming values. -/
inductive Administrative : Multiset Sx → Multiset Sx → Prop
  | varZero (v ρ κ : Sx) (W : Multiset Sx) :
      Administrative (ev (var zero) (cons v ρ) κ ::ₘ W) (ret v κ ::ₘ W)
  | varSucc (i v ρ κ : Sx) (W : Multiset Sx) :
      Administrative (ev (var (succ i)) (cons v ρ) κ ::ₘ W) (ev (var i) ρ κ ::ₘ W)
  | lam (b ρ κ : Sx) (W : Multiset Sx) : Administrative (ev (lam b) ρ κ ::ₘ W) (ret (clo b ρ) κ ::ₘ W)
  | app (f a ρ κ : Sx) (W : Multiset Sx) :
      Administrative (ev (app f a) ρ κ ::ₘ W) (ev f ρ (cons (appL a ρ) κ) ::ₘ W)
  | appL (v a ρ κ : Sx) (W : Multiset Sx) :
      Administrative (ret v (cons (appL a ρ) κ) ::ₘ W) (ev a ρ (cons (appR v) κ) ::ₘ W)
  | let_ (s b ρ κ : Sx) (W : Multiset Sx) :
      Administrative (ev (let_ s b) ρ κ ::ₘ W) (ev s ρ (cons (letK b ρ) κ) ::ₘ W)
  | quote (c ρ κ : Sx) (W : Multiset Sx) : Administrative (ev (quote c) ρ κ ::ₘ W) (ret (code c ρ) κ ::ₘ W)
  | activate (e ρ κ : Sx) (W : Multiset Sx) :
      Administrative (ev (activate e) ρ κ ::ₘ W) (ev e ρ (cons actK κ) ::ₘ W)
  | atom (d ρ κ : Sx) (W : Multiset Sx) : Administrative (ev (atom d) ρ κ ::ₘ W) (ret (atom d) κ ::ₘ W)
  | add (e ρ κ : Sx) (W : Multiset Sx) :
      Administrative (ev (add e) ρ κ ::ₘ W) (ev e ρ (cons addK κ) ::ₘ W)
  | remove (e ρ κ : Sx) (W : Multiset Sx) :
      Administrative (ev (remove e) ρ κ ::ₘ W) (ev e ρ (cons removeK κ) ::ₘ W)
  | demand (k e ρ κ : Sx) (W : Multiset Sx) :
      Administrative (ev (demandE k e) ρ κ ::ₘ W) (ev e ρ (cons (demandK k) κ) ::ₘ W)

/-- Administrative steps are steps. -/
theorem Administrative.step {W W' : Multiset Sx} : Administrative W W' → Step W W'
  | .varZero v ρ κ W => .varZero v ρ κ W
  | .varSucc i v ρ κ W => .varSucc i v ρ κ W
  | .lam b ρ κ W => .lam b ρ κ W
  | .app f a ρ κ W => .app f a ρ κ W
  | .appL v a ρ κ W => .appL v a ρ κ W
  | .let_ s b ρ κ W => .let_ s b ρ κ W
  | .quote c ρ κ W => .quote c ρ κ W
  | .activate e ρ κ W => .activate e ρ κ W
  | .atom d ρ κ W => .atom d ρ κ W
  | .add e ρ κ W => .add e ρ κ W
  | .remove e ρ κ W => .remove e ρ κ W
  | .demand k e ρ κ W => .demand k e ρ κ W

theorem measure_cons (s : Sx) (W : Multiset Sx) : measure (s ::ₘ W) = threadMeasure s + measure W := by
  simp [measure]

theorem threadMeasure_ev (e ρ κ : Sx) : threadMeasure (ev e ρ κ) = 3 * size e + frames κ + 1 := by
  simp [threadMeasure, ev, t3]

theorem threadMeasure_ret (v κ : Sx) : threadMeasure (ret v κ) = frames κ := by
  simp [threadMeasure, ret, t2]

theorem frames_appL (a ρ κ : Sx) : frames (cons (appL a ρ) κ) = 3 * size a + 2 + frames κ := by
  simp [frames, cons, appL, t2]

theorem frames_other {k : ℕ} (other : k ≠ 22) (f : Sx) (κ : Sx) :
    frames (cons (.cell (.sym k) f) κ) = 0 := by
  cases f with
  | sym _ => simp [frames, cons, t2]
  | cell a b => simp [frames, cons, t2, other]

/-- **Administrative steps strictly decrease the measure**, so every administrative sequence is
finite: only β, let binding, activation, choice, effects, suspension and definitions remain. -/
theorem administrative_decreases {W W' : Multiset Sx} (step : Administrative W W') : measure W' < measure W := by
  cases step with
  | varZero v ρ κ W =>
      rw [measure_cons, measure_cons, threadMeasure_ev, threadMeasure_ret]; omega
  | varSucc i v ρ κ W =>
      rw [measure_cons, measure_cons, threadMeasure_ev, threadMeasure_ev]
      simp only [var, succ, t1, size]; omega
  | lam b ρ κ W => rw [measure_cons, measure_cons, threadMeasure_ev, threadMeasure_ret]; omega
  | app f a ρ κ W =>
      rw [measure_cons, measure_cons, threadMeasure_ev, threadMeasure_ev, frames_appL]
      simp only [app, t2, size]; omega
  | appL v a ρ κ W =>
      rw [measure_cons, measure_cons, threadMeasure_ret, threadMeasure_ev, frames_appL,
        show appR v = .cell (.sym 23) v from rfl, frames_other (by decide)]
      omega
  | let_ s b ρ κ W =>
      rw [measure_cons, measure_cons, threadMeasure_ev, threadMeasure_ev,
        show letK b ρ = .cell (.sym 24) (.cell b ρ) from rfl, frames_other (by decide)]
      simp only [let_, t2, size]; omega
  | quote c ρ κ W => rw [measure_cons, measure_cons, threadMeasure_ev, threadMeasure_ret]; omega
  | activate e ρ κ W =>
      rw [measure_cons, measure_cons, threadMeasure_ev, threadMeasure_ev,
        show actK = .sym 25 from rfl]
      have : frames (cons (.sym 25) κ) = 0 := by simp [frames, cons, t2]
      rw [this]
      simp only [activate, t1, size]; omega
  | atom d ρ κ W => rw [measure_cons, measure_cons, threadMeasure_ev, threadMeasure_ret]; omega
  | add e ρ κ W =>
      rw [measure_cons, measure_cons, threadMeasure_ev, threadMeasure_ev, show addK = .sym 26 from rfl]
      have : frames (cons (.sym 26) κ) = 0 := by simp [frames, cons, t2]
      rw [this]
      simp only [add, t1, size]; omega
  | remove e ρ κ W =>
      rw [measure_cons, measure_cons, threadMeasure_ev, threadMeasure_ev, show removeK = .sym 27 from rfl]
      have : frames (cons (.sym 27) κ) = 0 := by simp [frames, cons, t2]
      rw [this]
      simp only [remove, t1, size]; omega
  | demand k e ρ κ W =>
      rw [measure_cons, measure_cons, threadMeasure_ev, threadMeasure_ev,
        show demandK k = .cell (.sym 28) k from rfl, frames_other (by decide)]
      simp only [demandE, t2, size]; omega

/-- **No infinite administrative sequence.** -/
theorem administrative_wellFounded : WellFounded (flip Administrative) :=
  Subrelation.wf (fun {_ _} step => administrative_decreases step) (InvImage.wf measure Nat.lt_wfRel.wf)

#print axioms program_execution_iff
#print axioms step_sound
#print axioms firing_complete
#print axioms stuck_of_source
#print axioms fires_singleton
#print axioms step_singleton
#print axioms compatible_of_inst
#print axioms overlapCheck_true
#print axioms overlap_free
#print axioms singleton_deterministic
#print axioms amb_successors
#print axioms administrative_decreases
#print axioms administrative_wellFounded

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program
