import Mettapedia.GSLT.Dynamics.WeightCost
import Mettapedia.GSLT.Dynamics.PathIntegral
import Mettapedia.GSLT.Causality.Trace
import Mathlib.Algebra.Group.Int.Defs

/-!
# Costs on paths and on the reversible envelope

Meredith's Theorem 7.1 is conservation on the envelope: a path that
returns to the same extended term has net cost zero. That is a
structural consequence of reversibility (unique parent / stack log),
not of exactness. The history itself is a potential for *every*
`ActionMap`.

Exactness is a different law: the potential depends only on the
current term, so it survives forgetting the log. Forward-only "zero
on loops" does not imply exactness (two-route control below).
Livšic on paths that may run backward is: exact iff the cost
survives `forgetHistory` along envelope paths.

Path concatenation is `rewritePathAppend` from `PathIntegral`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

variable {S : GSLT}

/-- A step action is the coboundary of a potential on terms. -/
def ActionMap.Exact {A : Type*} [Sub A] (am : ActionMap S A) (φ : S.Term → A) : Prop :=
  ∀ {t u} (h : S.Step t u), am.action h = φ u - φ t

/-- Net action vanishes on loops. -/
def ActionMap.Conserves {A : Type*} [AddCommGroup A] (am : ActionMap S A) : Prop :=
  ∀ t (γ : S.RewritePath t t), totalAction am γ = 0

/-- Path totals depend only on endpoints. -/
def ActionMap.PathIndependent {A : Type*} [AddMonoid A] (am : ActionMap S A) : Prop :=
  ∀ {t u} (γ δ : S.RewritePath t u), totalAction am γ = totalAction am δ

theorem exact_totalAction {A : Type*} [AddCommGroup A] (am : ActionMap S A)
    (φ : S.Term → A) (hex : am.Exact φ) {t u : S.Term} (γ : S.RewritePath t u) :
    totalAction am γ = φ u - φ t := by
  induction γ with
  | nil t =>
      simp [totalAction]
  | cons h rest ih =>
      simp [totalAction, hex h, ih]

theorem ActionMap.exact_conserves {A : Type*} [AddCommGroup A] {am : ActionMap S A}
    {φ : S.Term → A} (hex : am.Exact φ) : am.Conserves := by
  intro t γ
  simpa [sub_self] using exact_totalAction am φ hex γ

theorem ActionMap.conserves_of_pathIndependent {A : Type*} [AddCommGroup A]
    {am : ActionMap S A} (h : am.PathIndependent) : am.Conserves := by
  intro t γ
  have := h γ (GSLT.RewritePath.nil t)
  simpa [totalAction] using this

/-- Path-independence from a root reconstructs the potential. -/
theorem ActionMap.exact_of_pathIndependent {A : Type*} [AddCommGroup A]
    (am : ActionMap S A) (root : S.Term)
    (reach : ∀ t, S.RewritePath root t) (hpi : am.PathIndependent) :
    am.Exact fun t => totalAction am (reach t) := by
  intro t u step
  have h :=
    hpi (rewritePathAppend (reach t) (.cons step (.nil u))) (reach u)
  rw [totalAction_append, totalAction, totalAction, add_zero] at h
  rw [eq_sub_iff_add_eq, add_comm (am.action step)]
  exact h

/-! ## Envelope costs (Theorem 7.1)

Forward motion costs `am.action`; backward credits the negation.
The log is a stack, so every extended term has at most one parent.
The sum of recorded forward actions is therefore a potential for
*every* cost map, exact or not.
-/

def envelopeAction {A : Type*} [Neg A] (am : ActionMap S A)
    {et eu : ExtendedTerm S} : ReversibleStep S et eu → A
  | .forward h _ => am.action h
  | .backward h _ => -am.action h

def totalEnvelopeAction {A : Type*} [AddGroup A] (am : ActionMap S A) :
    {et eu : ExtendedTerm S} → EnvelopePath (S := S) et eu → A
  | _, _, .nil _ => 0
  | _, _, .cons st rest => envelopeAction am st + totalEnvelopeAction am rest

def traceEntries (τ : Trace S) : List (TraceEntry S) := τ

def historyPotentialEntries {A : Type*} [AddMonoid A] (am : ActionMap S A) :
    List (TraceEntry S) → A
  | [] => 0
  | e :: rest => am.action e.step + historyPotentialEntries am rest

/-- Potential of an extended term: total recorded forward cost of its log. -/
def historyPotential {A : Type*} [AddMonoid A] (am : ActionMap S A)
    (et : ExtendedTerm S) : A :=
  historyPotentialEntries am (traceEntries et.history)

theorem envelopeAction_eq_historyDelta {A : Type*} [AddGroup A]
    (am : ActionMap S A) {et eu : ExtendedTerm S}
    (st : ReversibleStep S et eu) :
    envelopeAction am st = historyPotential am eu - historyPotential am et := by
  cases st <;>
    simp [envelopeAction, historyPotential, historyPotentialEntries, traceEntries]

theorem totalEnvelopeAction_eq_historyDelta {A : Type*} [AddCommGroup A]
    (am : ActionMap S A) {et eu : ExtendedTerm S}
    (γ : EnvelopePath (S := S) et eu) :
    totalEnvelopeAction am γ = historyPotential am eu - historyPotential am et := by
  induction γ with
  | nil et =>
      simp [totalEnvelopeAction, historyPotential]
  | cons st rest ih =>
      rw [totalEnvelopeAction, envelopeAction_eq_historyDelta am st, ih]
      rw [add_comm]
      exact sub_add_sub_cancel (historyPotential am _) (historyPotential am _)
        (historyPotential am _)

/-- Theorem 7.1: a closed envelope path (same extended term) has net cost
zero, with no exactness hypothesis. -/
theorem envelope_conserves {A : Type*} [AddCommGroup A] (am : ActionMap S A)
    (et : ExtendedTerm S) (γ : EnvelopePath (S := S) et et) :
    totalEnvelopeAction am γ = 0 := by
  have := totalEnvelopeAction_eq_historyDelta am γ
  simpa [sub_self] using this

/-- Remaining fuel plus recorded spend equals the initial budget. -/
def remaining {A : Type*} [AddGroup A] (am : ActionMap S A) (initial : A)
    (et : ExtendedTerm S) : A :=
  initial - historyPotential am et

theorem ledger_law {A : Type*} [AddGroup A] (am : ActionMap S A) (initial : A)
    (et : ExtendedTerm S) :
    remaining am initial et + historyPotential am et = initial :=
  sub_add_cancel initial (historyPotential am et)

/-- The potential survives forgetting the log along a path: same current
term implies net envelope cost zero. Exact costs satisfy this; arbitrary
costs need not. -/
def SurvivesForgetting {A : Type*} [AddGroup A] (am : ActionMap S A) : Prop :=
  ∀ {et eu : ExtendedTerm S} (γ : EnvelopePath (S := S) et eu),
    et.current = eu.current → totalEnvelopeAction am γ = 0

theorem exact_envelopeAction {A : Type*} [AddCommGroup A]
    (am : ActionMap S A) (φ : S.Term → A) (hex : am.Exact φ)
    {et eu : ExtendedTerm S} (st : ReversibleStep S et eu) :
    envelopeAction am st = φ eu.current - φ et.current := by
  cases st with
  | forward h τ =>
      simpa [envelopeAction] using hex h
  | backward h τ =>
      rw [envelopeAction, hex h]
      exact neg_sub (φ _) (φ _)

theorem exact_totalEnvelopeAction {A : Type*} [AddCommGroup A]
    (am : ActionMap S A) (φ : S.Term → A) (hex : am.Exact φ)
    {et eu : ExtendedTerm S} (γ : EnvelopePath (S := S) et eu) :
    totalEnvelopeAction am γ = φ eu.current - φ et.current := by
  induction γ with
  | nil et =>
      simp [totalEnvelopeAction]
  | cons st rest ih =>
      rw [totalEnvelopeAction, exact_envelopeAction am φ hex st, ih]
      rw [add_comm]
      exact sub_add_sub_cancel (φ _) (φ _) (φ _)

theorem exact_envelope_of_same_current {A : Type*} [AddCommGroup A]
    (am : ActionMap S A) (φ : S.Term → A) (hex : am.Exact φ)
    {et eu : ExtendedTerm S} (γ : EnvelopePath (S := S) et eu)
    (same : et.current = eu.current) :
    totalEnvelopeAction am γ = 0 := by
  have := exact_totalEnvelopeAction am φ hex γ
  simp [same, sub_self] at this
  exact this

theorem survivesForgetting_of_exact {A : Type*} [AddCommGroup A]
    (am : ActionMap S A) {φ : S.Term → A} (hex : am.Exact φ) :
    SurvivesForgetting am :=
  fun γ same => exact_envelope_of_same_current am φ hex γ same

theorem exact_envelope_conserves {A : Type*} [AddCommGroup A]
    (am : ActionMap S A) (φ : S.Term → A) (_hex : am.Exact φ)
    (et : ExtendedTerm S) (γ : EnvelopePath (S := S) et et) :
    totalEnvelopeAction am γ = 0 :=
  envelope_conserves am et γ

/-- A step cost is the coboundary of a vectorial potential. -/
def CostMap.Exact {A : Type*} {k : Nat} [Sub A] (cm : CostMap S A k)
    (φ : S.Term → VectorialAccount A k) : Prop :=
  ∀ {t u} (h : S.Step t u), cm.cost h = φ u - φ t

/-- One resource coordinate of a cost map, as an action map. -/
def CostMap.component {A : Type*} {k : Nat} (cm : CostMap S A k) (i : Fin k) :
    ActionMap S A where
  action := fun {_t _u} h => cm.cost h i

theorem totalAction_component {A : Type*} {k : Nat} [AddMonoid A]
    (cm : CostMap S A k) (i : Fin k) {t u : S.Term} (γ : S.RewritePath t u) :
    totalAction (cm.component i) γ = totalCost cm γ i := by
  induction γ with
  | nil _ =>
      simp [totalAction, totalCost]
      exact (rfl : (0 : A) = (0 : VectorialAccount A k) i)
  | cons h rest ih =>
      simp [totalAction, totalCost]
      rw [ih]
      exact (rfl : cm.cost h i + totalCost cm rest i =
        (cm.cost h + totalCost cm rest) i)

theorem CostMap.component_exact {A : Type*} {k : Nat} [Sub A]
    {cm : CostMap S A k} {φ : S.Term → VectorialAccount A k}
    (hex : cm.Exact φ) (i : Fin k) :
    (cm.component i).Exact fun t => φ t i := by
  intro t u h
  exact congrArg (fun f : VectorialAccount A k => f i) (hex h)

theorem CostMap.exact_conserves {A : Type*} {k : Nat} [AddCommGroup A]
    {cm : CostMap S A k} {φ : S.Term → VectorialAccount A k}
    (hex : cm.Exact φ) : cm.conserves := by
  intro t γ
  refine VectorialAccount.ext fun i =>
    (totalAction_component cm i γ).symm.trans <|
      (ActionMap.exact_conserves (CostMap.component_exact hex i) t γ).trans
        (rfl : (0 : A) = (0 : VectorialAccount A k) i)

/-! ## Two-point control

A language on `Bool` whose only steps flip the bit. The coboundary of
`false ↦ 0`, `true ↦ 1` conserves. Charging 1 to `false → true` and 0
to the return step does not.
-/

def flipGSLT : GSLT where
  Term := Bool
  equations := ⟨(· = ·), eq_equivalence⟩
  rewrites := fun t u => t ≠ u
  rewrites_resp_left := by
    intro t t' u ht hstep
    exact ⟨u, ht ▸ hstep, rfl⟩
  rewrites_resp_right := by
    intro t u u' hstep hu
    exact hu ▸ hstep

def flipPotential : Bool → ℤ
  | false => 0
  | true => 1

def exactFlip : ActionMap flipGSLT ℤ where
  action := fun {t u} _ => flipPotential u - flipPotential t

theorem exactFlip_is_exact : exactFlip.Exact flipPotential := by
  intro t u h
  rfl

theorem exactFlip_conserves : exactFlip.Conserves :=
  ActionMap.exact_conserves exactFlip_is_exact

def dissipativeFlip : ActionMap flipGSLT ℤ where
  action := fun {t _u} _ =>
    match t with
    | false => (1 : ℤ)
    | true => 0

theorem flip_false_true : flipGSLT.Step false true := Bool.false_ne_true

theorem flip_true_false : flipGSLT.Step true false :=
  Ne.symm Bool.false_ne_true

def dissipativeLoop : flipGSLT.RewritePath false false :=
  GSLT.RewritePath.cons (S := flipGSLT) flip_false_true
    (GSLT.RewritePath.cons (S := flipGSLT) flip_true_false
      (GSLT.RewritePath.nil (S := flipGSLT) false))

theorem dissipative_loop_cost : totalAction dissipativeFlip dissipativeLoop = 1 := by
  simp [totalAction, dissipativeFlip, dissipativeLoop]

theorem dissipativeFlip_not_conserves : ¬ dissipativeFlip.Conserves := by
  intro h
  have := h false dissipativeLoop
  simp [dissipative_loop_cost] at this

theorem exactFlip_envelope_of_same_current
    {et eu : ExtendedTerm flipGSLT} (γ : EnvelopePath (S := flipGSLT) et eu)
    (same : et.current = eu.current) :
    totalEnvelopeAction exactFlip γ = 0 :=
  exact_envelope_of_same_current exactFlip flipPotential exactFlip_is_exact γ same

def dissipativeEnvelopeStart : ExtendedTerm flipGSLT :=
  envelopeEmbed flipGSLT false

def dissipativeEnvelopeEnd : ExtendedTerm flipGSLT :=
  { current := false
    history := [⟨true, false, flip_true_false⟩, ⟨false, true, flip_false_true⟩] }

def dissipativeEnvelopePath :
    EnvelopePath (S := flipGSLT) dissipativeEnvelopeStart dissipativeEnvelopeEnd :=
  EnvelopePath.cons (S := flipGSLT)
    (ReversibleStep.forward (S := flipGSLT) flip_false_true [])
    (EnvelopePath.cons (S := flipGSLT)
      (ReversibleStep.forward (S := flipGSLT) flip_true_false
        [⟨false, true, flip_false_true⟩])
      (EnvelopePath.nil (S := flipGSLT) dissipativeEnvelopeEnd))

theorem dissipative_envelope_same_current :
    dissipativeEnvelopeStart.current = dissipativeEnvelopeEnd.current :=
  rfl

theorem dissipative_envelope_cost :
    totalEnvelopeAction dissipativeFlip dissipativeEnvelopePath = 1 := by
  simp [totalEnvelopeAction, envelopeAction, dissipativeFlip, dissipativeEnvelopePath]

theorem dissipativeFlip_not_envelope_current_invariant :
    ¬ ∀ {et eu : ExtendedTerm flipGSLT} (γ : EnvelopePath (S := flipGSLT) et eu),
        et.current = eu.current → totalEnvelopeAction dissipativeFlip γ = 0 := by
  intro h
  have := h dissipativeEnvelopePath dissipative_envelope_same_current
  simp [dissipative_envelope_cost] at this

theorem dissipativeFlip_envelope_loops_conserve
    (et : ExtendedTerm flipGSLT)
    (γ : EnvelopePath (S := flipGSLT) et et) :
    totalEnvelopeAction dissipativeFlip γ = 0 :=
  envelope_conserves dissipativeFlip et γ

/-! ## Forward-only loops do not imply exactness

A diamond with unequal route costs has no term potential, yet no
forward loop exists, so `Conserves` holds vacuously on nontrivial
`RewritePath` cycles.
-/

inductive TwoRoute where
  | src | left | right | tgt
  deriving DecidableEq

def twoRoute : GSLT where
  Term := TwoRoute
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := fun t u =>
    (t = .src ∧ (u = .left ∨ u = .right)) ∨
      (t = .left ∧ u = .tgt) ∨ (t = .right ∧ u = .tgt)
  rewrites_resp_left := by
    intro t t' u htt hstep
    exact ⟨u, htt ▸ hstep, rfl⟩
  rewrites_resp_right := by
    intro t u u' hstep huu
    exact huu ▸ hstep

def twoRouteRank : TwoRoute → ℕ
  | .src => 0
  | .left => 1
  | .right => 1
  | .tgt => 2

theorem twoRoute_rank_lt {t u : TwoRoute} (h : twoRoute.Step t u) :
    twoRouteRank t < twoRouteRank u := by
  rcases h with h | h | h
  · rcases h with ⟨rfl, h | h⟩ <;> simp [twoRouteRank, h]
  · rcases h with ⟨rfl, rfl⟩; simp [twoRouteRank]
  · rcases h with ⟨rfl, rfl⟩; simp [twoRouteRank]

theorem twoRoute_rank_le_path :
    ∀ {t u : TwoRoute} (_γ : twoRoute.RewritePath t u),
      twoRouteRank t ≤ twoRouteRank u
  | _, _, .nil _ => le_rfl
  | _, _, .cons h rest =>
      (twoRoute_rank_lt h).le.trans (twoRoute_rank_le_path rest)

def twoRouteCost : ActionMap twoRoute ℤ where
  action := fun {t u} _ =>
    match t, u with
    | .src, .left => (1 : ℤ)
    | _, _ => 0

theorem twoRoute_src_left : twoRoute.Step TwoRoute.src TwoRoute.left :=
  Or.inl ⟨rfl, Or.inl rfl⟩

theorem twoRoute_left_tgt : twoRoute.Step TwoRoute.left TwoRoute.tgt :=
  Or.inr (Or.inl ⟨rfl, rfl⟩)

theorem twoRoute_src_right : twoRoute.Step TwoRoute.src TwoRoute.right :=
  Or.inl ⟨rfl, Or.inr rfl⟩

theorem twoRoute_right_tgt : twoRoute.Step TwoRoute.right TwoRoute.tgt :=
  Or.inr (Or.inr ⟨rfl, rfl⟩)

def twoRoute_via_left : twoRoute.RewritePath TwoRoute.src TwoRoute.tgt :=
  .cons twoRoute_src_left
    (.cons twoRoute_left_tgt (.nil (S := twoRoute) TwoRoute.tgt))

def twoRoute_via_right : twoRoute.RewritePath TwoRoute.src TwoRoute.tgt :=
  .cons twoRoute_src_right
    (.cons twoRoute_right_tgt (.nil (S := twoRoute) TwoRoute.tgt))

theorem twoRoute_via_left_cost : totalAction twoRouteCost twoRoute_via_left = 1 := by
  simp [totalAction, twoRouteCost, twoRoute_via_left]

theorem twoRoute_via_right_cost : totalAction twoRouteCost twoRoute_via_right = 0 := by
  simp [totalAction, twoRouteCost, twoRoute_via_right]

theorem twoRoute_conserves : twoRouteCost.Conserves := by
  intro t γ
  cases γ with
  | nil => simp [totalAction]
  | cons h rest =>
      have : twoRouteRank t < twoRouteRank t :=
        (twoRoute_rank_lt h).trans_le (twoRoute_rank_le_path rest)
      exact (lt_irrefl _ this).elim

theorem twoRoute_not_exact : ¬ ∃ φ, twoRouteCost.Exact φ := by
  rintro ⟨φ, hex⟩
  have h₁ := exact_totalAction twoRouteCost φ hex twoRoute_via_left
  have h₂ := exact_totalAction twoRouteCost φ hex twoRoute_via_right
  rw [twoRoute_via_left_cost] at h₁
  rw [twoRoute_via_right_cost] at h₂
  have : (1 : ℤ) = 0 := h₁.trans h₂.symm
  exact absurd this (by decide)

end Mettapedia.GSLT
