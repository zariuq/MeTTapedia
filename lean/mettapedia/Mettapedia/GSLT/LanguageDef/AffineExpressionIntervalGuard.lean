import Mettapedia.GSLT.LanguageDef.AffineExpressionNativeTypes

/-!
# Prepared interval guards for every source intermediate

Bottom-up compilation retains an affine form for each source occurrence,
including literals and inputs. Instantiation evaluates coefficient expressions
once for a fixed input environment. The resulting guard contains only integer
pairs: its interval check neither traverses source syntax nor evaluates the
source expression.

Checking the two endpoints of every retained form is equivalent to successful
checked source evaluation for every accumulator in an ordered interval. The
result is exact for the syntactically admitted affine fragment, including
negative slopes and intermediate overflow. It does not identify every
semantically affine expression, license changing the input environment, or
prove that coefficient preparation itself fits a machine word. Preparation and
guard arithmetic use exact integers; a fixed-width implementation needs its own
arithmetic realization. The number of checks is proportional to source
occurrences; coefficient-expression size and integer bit complexity remain
separate costs.
-/

namespace Mettapedia.GSLT.AffineExpression.IntervalGuard

open Mettapedia.Algebra
open NativeTypes

/-- Source values in left-to-right postorder, including all leaves. -/
def intermediates (e : Expr n) (env : Fin n → Int) (state : Int) : List Int :=
  match e with
  | .lit k => [k]
  | .input i => [env i]
  | .acc => [state]
  | .bin op l r =>
      intermediates l env state ++ intermediates r env state ++
        [op.eval (l.eval env state) (r.eval env state)]

/-- Each list entry records a source occurrence, not a distinct value. -/
def occurrenceCount : Expr n → Nat
  | .lit _ | .input _ | .acc => 1
  | .bin _ l r => occurrenceCount l + occurrenceCount r + 1

theorem intermediates_length (e : Expr n) (env : Fin n → Int) (state : Int) :
    (intermediates e env state).length = occurrenceCount e := by
  induction e with
  | lit | input | acc => rfl
  | bin op l r ihl ihr => simp [intermediates, occurrenceCount, ihl, ihr, Nat.add_assoc]

theorem checked_isSome_iff (lower upper value : Int) :
    (checked lower upper value).isSome = true ↔ InRange lower upper value := by
  simp [checked, InRange]

/-- The checked evaluator succeeds precisely when every independently listed
source intermediate fits, including unused-looking operands such as `0 * x`. -/
theorem intermediates_safe_iff (e : Expr n) (lower upper : Int)
    (env : Fin n → Int) (state : Int) :
    (∀ value ∈ intermediates e env state, InRange lower upper value) ↔
      (e.evalChecked lower upper env state).isSome = true := by
  induction e with
  | lit k => simpa [intermediates, Expr.evalChecked] using
      (checked_isSome_iff lower upper k).symm
  | input i => simpa [intermediates, Expr.evalChecked] using
      (checked_isSome_iff lower upper (env i)).symm
  | acc => simpa [intermediates, Expr.evalChecked] using
      (checked_isSome_iff lower upper state).symm
  | bin op l r ihl ihr =>
      simp only [intermediates, List.forall_mem_append, List.forall_mem_singleton,
        ihl, ihr]
      cases hl : l.evalChecked lower upper env state with
      | none => simp [Expr.evalChecked, hl]
      | some x =>
          cases hr : r.evalChecked lower upper env state with
          | none => simp [Expr.evalChecked, hl, hr]
          | some y =>
              have hx := (checked_eval_sound l lower upper env state x hl).1
              have hy := (checked_eval_sound r lower upper env state y hr).1
              simp [Expr.evalChecked, hl, hr, checked_isSome_iff, hx, hy]

/-- Reusable syntax-level plan, compiled without observing input values. -/
structure Plan (n : Nat) where
  result : Form n
  checks : List (Form n)
  deriving Repr

def leaf (f : Form n) : Plan n := ⟨f, [f]⟩

def combinePlans (op : Op) (left right : Plan n) : Option (Plan n) := do
  let out ← combine op left.result right.result
  pure ⟨out, left.checks ++ right.checks ++ [out]⟩

/-- One bottom-up compilation obtains the root form and every guard form. -/
def compilePlan : Expr n → Option (Plan n)
  | .lit k => some (leaf (.constant (.lit k)))
  | .input i => some (leaf (.constant (.input i)))
  | .acc => some (leaf (.affine (.lit 1) (.lit 0)))
  | .bin op l r => do combinePlans op (← compilePlan l) (← compilePlan r)

theorem compilePlan_result (e : Expr n) :
    (compilePlan e).map Plan.result = compile e := by
  induction e with
  | lit | input | acc => rfl
  | bin op l r ihl ihr =>
      cases hl : compilePlan l with
      | none => simp [hl] at ihl; simp [compilePlan, hl, compile, ← ihl]
      | some lp =>
          cases hr : compilePlan r with
          | none => simp [hr] at ihr; simp [compilePlan, hl, hr, compile, ← ihr]
          | some rp =>
              simp only [hl, Option.map_some] at ihl
              simp only [hr, Option.map_some] at ihr
              simp [compilePlan, compile, hl, hr, ← ihl, ← ihr, combinePlans]

theorem compilePlan_sound (e : Expr n) (p : Plan n)
    (accepted : compilePlan e = some p) : compile e = some p.result := by
  rw [← compilePlan_result, accepted]
  rfl

/-- Adding intermediate guards does not shrink the existing affine grammar. -/
theorem compilePlan_exists_iff (e : Expr n) :
    (∃ p, compilePlan e = some p) ↔ e.degree ≤ 1 := by
  rw [← compile_exists_iff, ← compilePlan_result]
  cases compilePlan e <;> simp

theorem compilePlan_intermediates (e : Expr n) (p : Plan n)
    (accepted : compilePlan e = some p) (env : Fin n → Int) (state : Int) :
    p.checks.map (Form.apply env state) = intermediates e env state := by
  induction e generalizing p with
  | lit k =>
      simp [compilePlan] at accepted
      subst p
      simp [leaf, Form.apply, Form.summary, Form.scale, Form.offset,
        Coeff.eval, AffineSummary.act, intermediates]
  | input i =>
      simp [compilePlan] at accepted
      subst p
      simp [leaf, Form.apply, Form.summary, Form.scale, Form.offset,
        Coeff.eval, AffineSummary.act, intermediates]
  | acc =>
      simp [compilePlan] at accepted
      subst p
      simp [leaf, Form.apply, Form.summary, Form.scale, Form.offset,
        Coeff.eval, AffineSummary.act, intermediates]
  | bin op l r ihl ihr =>
      cases hl : compilePlan l with
      | none => simp [compilePlan, hl] at accepted
      | some lp =>
          cases hr : compilePlan r with
          | none => simp [compilePlan, hl, hr] at accepted
          | some rp =>
              cases hc : combine op lp.result rp.result with
              | none => simp [compilePlan, hl, hr, combinePlans, hc] at accepted
              | some out =>
                  simp [compilePlan, hl, hr, combinePlans, hc] at accepted
                  subst p
                  have hroot : compile (.bin op l r) = some out := by
                    simp [compile, compilePlan_sound l lp hl, compilePlan_sound r rp hr, hc]
                  simpa [List.map_append, ihl lp hl, ihr rp hr, intermediates, Expr.eval]
                    using congrArg (fun value =>
                      intermediates l env state ++ intermediates r env state ++ [value])
                        (compile_sound (.bin op l r) out hroot env state)

/-- Instantiated guards have no source syntax or input-variable references. -/
structure Prepared where
  result : AffineSummary Int
  checks : List (AffineSummary Int)
  deriving DecidableEq, Repr

def Plan.prepare (p : Plan n) (env : Fin n → Int) : Prepared :=
  ⟨p.result.summary env, p.checks.map (Form.summary env)⟩

/-- The number of endpoint obligations before short-circuiting is independent
of how many accumulators an interval contains. This does not model
bit-operation or coefficient-preparation costs. -/
def Prepared.endpointCount (p : Prepared) : Nat := 2 * p.checks.length

def Prepared.checkInterval (p : Prepared) (lo hi lower upper : Int) : Bool :=
  p.checks.all fun f => decide
    (InRange lower upper (f.act lo) ∧ InRange lower upper (f.act hi))

theorem prepared_intermediates (e : Expr n) (p : Plan n)
    (accepted : compilePlan e = some p) (env : Fin n → Int) (state : Int) :
    (p.prepare env).checks.map (fun f => f.act state) = intermediates e env state := by
  change (p.checks.map (Form.summary env)).map (fun f => f.act state) = _
  rw [List.map_map]
  exact compilePlan_intermediates e p accepted env state

theorem prepared_endpointCount (e : Expr n) (p : Plan n)
    (accepted : compilePlan e = some p) (env : Fin n → Int) :
    (p.prepare env).endpointCount = 2 * occurrenceCount e := by
  have h := congrArg List.length (prepared_intermediates e p accepted env 0)
  simp only [List.length_map, intermediates_length] at h
  simp [Prepared.endpointCount, h]

theorem Prepared.checkInterval_iff (p : Prepared) (lo hi lower upper : Int)
    (ordered : lo ≤ hi) :
    p.checkInterval lo hi lower upper = true ↔
      ∀ state, lo ≤ state → state ≤ hi →
        ∀ f ∈ p.checks, InRange lower upper (f.act state) := by
  simp only [Prepared.checkInterval, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h state hslo hshi f hf
    exact (affine_interval_endpoints f.scale f.offset lo hi lower upper ordered).mpr
      (h f hf) state hslo hshi
  · intro h f hf
    exact ⟨h lo le_rfl ordered f hf, h hi ordered le_rfl f hf⟩

/-- An interval certificate remains valid under restriction of its input
interval. No new source or coefficient evaluation is required. -/
theorem Prepared.checkInterval_mono (p : Prepared) (lo hi lo' hi' lower upper : Int)
    (ordered : lo ≤ hi) (ordered' : lo' ≤ hi')
    (hlo : lo ≤ lo') (hhi : hi' ≤ hi)
    (guard : p.checkInterval lo hi lower upper = true) :
    p.checkInterval lo' hi' lower upper = true := by
  apply (p.checkInterval_iff lo' hi' lower upper ordered').mpr
  intro state hslo hshi
  exact (p.checkInterval_iff lo hi lower upper ordered).mp guard state
    (hlo.trans hslo) (hshi.trans hhi)

/-- Exact universal safety, not merely a sufficient endpoint heuristic. -/
theorem prepared_guard_exact (e : Expr n) (p : Plan n)
    (accepted : compilePlan e = some p) (env : Fin n → Int)
    (lo hi lower upper : Int) (ordered : lo ≤ hi) :
    (p.prepare env).checkInterval lo hi lower upper = true ↔
      ∀ state, lo ≤ state → state ≤ hi →
        (e.evalChecked lower upper env state).isSome = true := by
  rw [Prepared.checkInterval_iff _ _ _ _ _ ordered]
  apply forall_congr'
  intro state
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  rw [← intermediates_safe_iff, ← prepared_intermediates e p accepted env state]
  simp

/-- The prepared executable check decides universal membership in the actual
generated source word-safety refinement. -/
theorem prepared_guard_native_exact (e : Expr n) (p : Plan n)
    (accepted : compilePlan e = some p) (env : Fin n → Int)
    (lo hi lower upper : Int) (ordered : lo ≤ hi) :
    (p.prepare env).checkInterval lo hi lower upper = true ↔
      ∀ state, lo ≤ state → state ≤ hi →
        Holds env state e (wordSafeType env state lower upper) :=
  prepared_guard_exact e p accepted env lo hi lower upper ordered

/-- A successful interval can be reused for any contained singleton without
re-evaluating source or coefficient syntax. -/
theorem prepared_guard_sound_at (e : Expr n) (p : Plan n)
    (accepted : compilePlan e = some p) (env : Fin n → Int)
    (lo hi lower upper state : Int) (ordered : lo ≤ hi)
    (guard : (p.prepare env).checkInterval lo hi lower upper = true)
    (hlo : lo ≤ state) (hhi : state ≤ hi) :
    e.evalChecked lower upper env state = some ((p.prepare env).result.act state) := by
  have safe := (prepared_guard_exact e p accepted env lo hi lower upper ordered).mp
    guard state hlo hhi
  cases h : e.evalChecked lower upper env state with
  | none => simp [h] at safe
  | some out =>
      have hout := (checked_eval_sound e lower upper env state out h).1
      have hresult := compile_sound e p.result (compilePlan_sound e p accepted) env state
      simp only [Plan.prepare]
      change some out = some (p.result.apply env state)
      rw [hout, hresult]

/-- After discharging the endpoint obligations, only the valid accumulator
interval and final exact summary are needed by this executable guard. The
owner must still retain the source and input-environment dependencies. -/
structure CachedInterval where
  lo : Int
  hi : Int
  result : AffineSummary Int
  deriving DecidableEq, Repr

def Prepared.certifyInterval (p : Prepared) (lo hi lower upper : Int) :
    Option CachedInterval :=
  if lo ≤ hi ∧ p.checkInterval lo hi lower upper = true then
    some ⟨lo, hi, p.result⟩
  else none

/-- Two comparisons on each use; no source, coefficient or guard-list walk. -/
def CachedInterval.contains (c : CachedInterval) (state : Int) : Bool :=
  decide (c.lo ≤ state ∧ state ≤ c.hi)

/-- Refusal means this artifact gives no answer, rather than source failure.
Arithmetic here is exact; a machine-word target needs separate target checks. -/
def CachedInterval.run (c : CachedInterval) (state : Int) : Option Int :=
  if c.contains state then some (c.result.act state) else none

theorem certifyInterval_some (p : Prepared) (lo hi lower upper : Int)
    (c : CachedInterval) (accepted : p.certifyInterval lo hi lower upper = some c) :
    c = ⟨lo, hi, p.result⟩ ∧ lo ≤ hi ∧ p.checkInterval lo hi lower upper = true := by
  unfold Prepared.certifyInterval at accepted
  split at accepted
  · cases accepted
    exact ⟨rfl, ‹lo ≤ hi ∧ p.checkInterval lo hi lower upper = true›⟩
  · contradiction

/-- Exact characterization of the source states covered by successful interval
preparation. Orderedness excludes an unusable empty cached interval. -/
theorem certifyInterval_exists_iff (e : Expr n) (p : Plan n)
    (accepted : compilePlan e = some p) (env : Fin n → Int)
    (lo hi lower upper : Int) :
    (∃ c, (p.prepare env).certifyInterval lo hi lower upper = some c) ↔
      lo ≤ hi ∧ ∀ state, lo ≤ state → state ≤ hi →
        (e.evalChecked lower upper env state).isSome = true := by
  by_cases ordered : lo ≤ hi
  · simp [Prepared.certifyInterval, ordered,
      prepared_guard_exact e p accepted env lo hi lower upper ordered]
  · simp [Prepared.certifyInterval, ordered]

/-- Once an interval is prepared, each accepted use requires only two bounds
comparisons and executes one exact affine summary. Source intermediates remain
safe without being recomputed by admission. -/
theorem cached_interval_sound (e : Expr n) (p : Plan n)
    (accepted : compilePlan e = some p) (env : Fin n → Int)
    (lo hi lower upper state : Int) (c : CachedInterval)
    (certified : (p.prepare env).certifyInterval lo hi lower upper = some c)
    (inside : c.contains state = true) :
    e.evalChecked lower upper env state = some (c.result.act state) := by
  obtain ⟨rfl, ordered, guard⟩ := certifyInterval_some _ _ _ _ _ c certified
  have bounds : lo ≤ state ∧ state ≤ hi := by
    simpa [CachedInterval.contains] using inside
  exact prepared_guard_sound_at e p accepted env lo hi lower upper state ordered
    guard bounds.1 bounds.2

theorem cached_run_sound (e : Expr n) (p : Plan n)
    (accepted : compilePlan e = some p) (env : Fin n → Int)
    (lo hi lower upper state value : Int) (c : CachedInterval)
    (certified : (p.prepare env).certifyInterval lo hi lower upper = some c)
    (run : c.run state = some value) :
    e.evalChecked lower upper env state = some value := by
  unfold CachedInterval.run at run
  split at run
  · cases run
    exact cached_interval_sound e p accepted env lo hi lower upper state c certified
      ‹c.contains state = true›
  · contradiction

end Mettapedia.GSLT.AffineExpression.IntervalGuard
