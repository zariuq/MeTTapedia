import Mettapedia.Machines.AdmissionRewriting.Invariance

/-!
# What a rewrite must preserve: `collapse`, empty scrutinees, and every fuel prefix

**`collapse` is a context.**  `(collapse t)` runs `t` to completion and answers once, the
tuple of `t`'s answers in order; `t`'s effects happen as they run.  The law
(`CollapseLaw`): the collapse of a term is a function of the term's trace in the same
dialect.  A rewrite that keeps traces therefore keeps collapses (`collapse_congr`), and
the normalizer is sound under `collapse` on a ready dialect (`collapse_N_sound`).

**Empty answers are not no answers.**  A scrutinee that answers the symbol `Empty` and a
scrutinee that completes without answers are different runs: `collapse` tells them apart
(`empty_answer_ne_no_answer`).  HE's `case` runs the first branch whose pattern matches
`Empty` in the second situation, a binding variable included, and at top level and under
`collapse` alike (`he_case_empty_composes`).  A collapse that evaluates its argument with
PeTTa's `case` rule (an explicit `Empty` branch only) answers `()` where HE answers `(z)`
(`machine_case_rule_breaks_collapse`): this was CeTTa's HE lane under `collapse`, whose
collections ran on the shared search machine with PeTTa's `case`; the machine host now
carries HE's rule (`case_switches_on_empty`).

**Every prefix, not the final bag.**  A metered run emits a step before each compound
node, and a run under fuel `n` shows its answers and effects up to the step that exhausts
the fuel (`underFuel`).  Equal traces give equal observations at every fuel
(`underFuel_congr`).  Charging the steps a rewrite saved after the run is not enough:
`(id (noisy))` and its normal form `(noisy)` charged one step afterwards take the same
number of steps, yet with fuel `1` the original stops before printing and the charged one
prints and answers (`charge_afterwards_insufficient`).  Nor is an equal answer bag with
equal effects enough: two orders of one `superpose` answer and print alike, and `once`
tells them apart (`bag_and_effects_insufficient`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdmissionRewriting.Observation

open AdmissionRewriting AdmissionRewriting.Dialects

/-! ## `collapse` -/

/-- Whether an event is an effect. -/
def Ev.isEff : Ev → Bool
  | .ans _ => false
  | .eff _ => true

/-- The collapse of a run: its effects in order, then one answer, the tuple of its answers
in order. -/
def collapseT (t : Trace) : Trace := t.filter Ev.isEff ++ [.ans (.tup (answers t))]

/-- The law of `collapse` in a dialect: the collapse of a term is its meter step, then the
collapse of the term's own run in that dialect. -/
def CollapseLaw (D : Dialect) (col : Tm → List Val → Trace) : Prop :=
  ∀ t ρ, col t ρ = D.meter ++ collapseT (eval D t ρ)

theorem collapse_congr {D : Dialect} {col : Tm → List Val → Trace} (h : CollapseLaw D col)
    {t t' : Tm} {ρ : List Val} (he : eval D t ρ = eval D t' ρ) : col t ρ = col t' ρ := by
  rw [h, h, he]

/-- On a ready dialect the normalizer is sound under `collapse`. -/
theorem collapse_N_sound {D : Dialect} (hD : Ready D) {col : Tm → List Val → Trace}
    (h : CollapseLaw D col) (Γ : Facts) (t : Tm) (ρ : List Val) (hρ : Sat Γ ρ) :
    col (N Γ t) ρ = col t ρ :=
  collapse_congr h (N_sound hD Γ t ρ hρ)

/-- A scrutinee that answers `Empty` and one with no answers collapse differently. -/
theorem empty_answer_ne_no_answer : collapseT [] ≠ collapseT (ret (.sym .emp)) := by
  simp [collapseT, answers, ret, Ev.isEff]

/-- `(case (empty) (($x z)))`. -/
def caseEmptyVar : Tm := .case_ .empty [(.bind, .lit (.sym zSym))]

/-- The collapse a dialect's own law gives. -/
def lawCollapse (D : Dialect) (t : Tm) (ρ : List Val) : Trace := D.meter ++ collapseT (eval D t ρ)

theorem lawCollapse_law (D : Dialect) : CollapseLaw D (lawCollapse D) := fun _ _ => rfl

/-- HE's rule composes: `[z]` at top level, `[(z)]` under `collapse`. -/
theorem he_case_empty_composes :
    eval he caseEmptyVar [] = ret (.sym zSym) ∧
      lawCollapse he caseEmptyVar [] = ret (.tup [.sym zSym]) := ⟨rfl, rfl⟩

/-- A collapse whose argument runs with PeTTa's `case` rule. -/
def machineCollapse (t : Tm) (ρ : List Val) : Trace :=
  he.meter ++ collapseT (eval { he with caseEmpty := .literal } t ρ)

/-- **The bug, as a law violated**: with PeTTa's `case` rule under `collapse`, the HE
program answers `()`, not `(z)`. -/
theorem machine_case_rule_breaks_collapse :
    machineCollapse caseEmptyVar [] = ret (.tup []) ∧ ¬ CollapseLaw he machineCollapse := by
  refine ⟨rfl, fun h => ?_⟩
  have h1 := h caseEmptyVar []
  rw [show machineCollapse caseEmptyVar [] = ret (.tup []) from rfl] at h1
  have h2 : he.meter ++ collapseT (eval he caseEmptyVar []) = ret (.tup [.sym zSym]) := rfl
  rw [h2] at h1
  simp [ret] at h1

/-- In HE a scrutinee answering `Empty` meets the `Empty` branch by matching, and one with
no answers meets it by HE's rule: one branch, two runs. -/
theorem he_empty_value_and_no_value :
    eval he (.case_ (.lit (.sym .emp)) [(.lit (.sym .emp), .lit (.sym zSym))]) [] =
        ret (.sym zSym) ∧
      eval he (.case_ .empty [(.lit (.sym .emp), .lit (.sym zSym))]) [] = ret (.sym zSym) ∧
      eval he (.lit (.sym .emp)) [] ≠ eval he .empty [] := by
  refine ⟨rfl, rfl, ?_⟩
  simp [eval, ret, he]

/-! ## Fuel -/

/-- The step a metered run emits before each compound node. -/
abbrev tick : ℕ := 7

/-- What a run shows under `n` units of fuel: its answers and effects up to the step that
exhausts the fuel, and whether it ran out. -/
def underFuel : ℕ → Trace → List Ev × Bool
  | _, [] => ([], false)
  | n, .ans v :: t => ((.ans v) :: (underFuel n t).1, (underFuel n t).2)
  | n, .eff k :: t =>
    if k = tick then
      match n with
      | 0 => ([], true)
      | n + 1 => underFuel n t
    else ((.eff k) :: (underFuel n t).1, (underFuel n t).2)

theorem underFuel_congr {t t' : Trace} (h : t = t') (n : ℕ) : underFuel n t = underFuel n t' := by
  rw [h]

/-- The steps of a run. -/
def ticks (t : Trace) : ℕ := (t.filter fun e => match e with | .eff k => k = tick | _ => false).length

/-- `(id (noisy))`: one call around another that prints. -/
def idNoisy : Tm := .call .id [.call noisy []]

theorem idNoisy_normal : N (fun _ => false) idNoisy = .call noisy [] := rfl

/-- **Charging the saved steps afterwards is not enough.**  The original takes two steps
before printing; its normal form, charged one step after its run, takes as many steps, but
with fuel `1` it prints and answers where the original stops before printing. -/
theorem charge_afterwards_insufficient :
    eval metered idNoisy [] = [.eff tick, .eff tick, .eff 0, .ans (.int 1)] ∧
      eval metered (N (fun _ => false) idNoisy) [] = [.eff tick, .eff 0, .ans (.int 1)] ∧
      ticks (eval metered idNoisy []) =
        ticks (eval metered (N (fun _ => false) idNoisy) [] ++ [.eff tick]) ∧
      (underFuel 1 (eval metered idNoisy [])).1 = [] ∧
      (underFuel 1 (eval metered (N (fun _ => false) idNoisy) [] ++ [.eff tick])).1 =
        [.eff 0, .ans (.int 1)] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `(superpose (1 (noisy)))` and `(superpose ((noisy) 1))`. -/
def oneThenNoisy : Tm := .sup [.lit (.int 1), .call noisy []]
def noisyThenOne : Tm := .sup [.call noisy [], .lit (.int 1)]

/-- **An equal answer bag with equal effects is not enough**: the two orders answer `1 1`
and print once, and `once` prints in one of them only. -/
theorem bag_and_effects_insufficient :
    answers (eval petta oneThenNoisy []) = answers (eval petta noisyThenOne []) ∧
      effects (eval petta oneThenNoisy []) = effects (eval petta noisyThenOne []) ∧
      eval petta (.once oneThenNoisy) [] = [.ans (.int 1)] ∧
      eval petta (.once noisyThenOne) [] = [.eff 0, .ans (.int 1)] := by
  refine ⟨rfl, rfl, rfl, rfl⟩

end Mettapedia.Machines.AdmissionRewriting.Observation
