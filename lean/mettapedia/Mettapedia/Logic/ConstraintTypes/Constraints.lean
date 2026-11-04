import Mettapedia.Logic.ConstraintTypes.RegularTree

/-!
# Substitution, delayed checks, and visible residual constraints

A delayed check is a predicate of a valuation with finite support. A check that
is not ready succeeds provisionally; binding its support runs the whole check.
This is not a decision procedure for satisfiability. Collection retains the
component reachable from the answer, rather than inventing an answer constructor
for a suspended check on an unreachable variable.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes

universe u v

inductive OpenTree (Variable : Type v) (Symbol : Type u) (arity : Symbol → Nat) where
  | var (name : Variable)
  | node (symbol : Symbol)
      (children : Fin (arity symbol) → OpenTree Variable Symbol arity)

namespace OpenTree

variable {X Y : Type v} {S : Type u} {arity : S → Nat}

def evaluate (valuation : X → Tree S arity) : OpenTree X S arity → Tree S arity
  | .var x => valuation x
  | .node s children => .node s (fun i => evaluate valuation (children i))

def substitute (substitution : X → OpenTree Y S arity) :
    OpenTree X S arity → OpenTree Y S arity
  | .var x => substitution x
  | .node s children => .node s (fun i => substitute substitution (children i))

/-- Checking after term substitution equals checking under the corresponding
valuation. The membership predicate itself is arbitrary. -/
theorem evaluate_substitute (substitution : X → OpenTree Y S arity)
    (valuation : Y → Tree S arity) (term : OpenTree X S arity) :
    (term.substitute substitution).evaluate valuation =
      term.evaluate (fun x => (substitution x).evaluate valuation) := by
  induction term with
  | var _ => rfl
  | node s children ih =>
      exact congrArg (Tree.node s) (funext ih)

theorem membership_substitute (member : Tree S arity → Bool)
    (substitution : X → OpenTree Y S arity) (valuation : Y → Tree S arity)
    (term : OpenTree X S arity) :
    member ((term.substitute substitution).evaluate valuation) =
      member (term.evaluate (fun x => (substitution x).evaluate valuation)) := by
  rw [evaluate_substitute]

end OpenTree

structure Obligation (World Variable Value : Type) where
  support : List Variable
  test : World → (Variable → Value) → Bool
  respects : ∀ world left right,
    (∀ x ∈ support, left x = right x) → test world left = test world right

namespace Obligation

variable {W X V : Type}

abbrev PartialValuation (X V : Type) := X → Option V

def Extends (before after : PartialValuation X V) : Prop :=
  ∀ x value, before x = some value → after x = some value

def realize (fallback : V) (valuation : PartialValuation X V) (x : X) : V :=
  (valuation x).getD fallback

def ready (obligation : Obligation W X V) (valuation : PartialValuation X V) : Bool :=
  obligation.support.all fun x => (valuation x).isSome

def check (obligation : Obligation W X V) (world : W) (fallback : V)
    (valuation : PartialValuation X V) : Bool :=
  if obligation.ready valuation then obligation.test world (realize fallback valuation) else true

theorem ready_mono (obligation : Obligation W X V)
    {before after : PartialValuation X V} (hExt : Extends before after)
    (ready : obligation.ready before = true) : obligation.ready after = true := by
  simp only [Obligation.ready, List.all_eq_true] at ready ⊢
  intro x hx
  cases hb : before x with
  | none => simpa [hb] using ready x hx
  | some value => simp [hExt x value hb]

theorem ready_values_stable (obligation : Obligation W X V) (fallback : V)
    {before after : PartialValuation X V} (hExt : Extends before after)
    (ready : obligation.ready before = true) :
    ∀ x ∈ obligation.support, realize fallback before x = realize fallback after x := by
  intro x hx
  have hr := (List.all_eq_true.1 ready) x hx
  cases hb : before x with
  | none => simp [hb] at hr
  | some value => simp [realize, hb, hExt x value hb]

/-- On a fixed world, checking before and after a monotone binding has exactly
the same acceptance as checking after it. No such law is asserted across edits. -/
theorem binding_commutes_with_check (obligation : Obligation W X V)
    (world : W) (fallback : V) {before after : PartialValuation X V}
    (hExt : Extends before after) :
    (obligation.check world fallback before && obligation.check world fallback after) =
      obligation.check world fallback after := by
  by_cases hr : obligation.ready before = true
  · have ha := obligation.ready_mono hExt hr
    have ht := obligation.respects world _ _ (obligation.ready_values_stable fallback hExt hr)
    simp [check, hr, ha, ht]
  · simp [check, hr]

/-- Once ready, a check is the full joint predicate, not an arbitrary first
overload whose delayed subchecks happened to post successfully. -/
theorem ready_check (obligation : Obligation W X V) (world : W) (fallback : V)
    (valuation : PartialValuation X V) (h : obligation.ready valuation = true) :
    obligation.check world fallback valuation = obligation.test world (realize fallback valuation) := by
  simp [check, h]

def checkAll (store : List (Obligation W X V)) (world : W) (fallback : V)
    (valuation : PartialValuation X V) : Bool :=
  store.all fun obligation => obligation.check world fallback valuation

theorem empty_store (world : W) (fallback : V) (valuation : PartialValuation X V) :
    checkAll [] world fallback valuation = true := rfl

theorem checkAll_append (left right : List (Obligation W X V)) (world : W)
    (fallback : V) (valuation : PartialValuation X V) :
    checkAll (left ++ right) world fallback valuation =
      (checkAll left world fallback valuation && checkAll right world fallback valuation) := by
  simp [checkAll]

/-- Finite stores inherit the fixed-world binding law. -/
theorem binding_commutes_with_store (store : List (Obligation W X V))
    (world : W) (fallback : V) {before after : PartialValuation X V}
    (hExt : Extends before after) :
    (checkAll store world fallback before && checkAll store world fallback after) =
      checkAll store world fallback after := by
  induction store with
  | nil => rfl
  | cons o rest ih =>
      have ho := o.binding_commutes_with_check world fallback hExt
      simp only [checkAll, List.all_cons] at ih ⊢
      cases h₁ : o.check world fallback before <;>
        cases h₂ : o.check world fallback after <;>
        cases h₃ : rest.all (fun a => a.check world fallback before) <;>
        cases h₄ : rest.all (fun a => a.check world fallback after) <;>
        simp_all

/-- Variables occurring in delayed goals on reachable variables are reachable
too. This includes indirect links through several joint obligations. -/
inductive Reachable (store : List (Obligation W X V)) (roots : List X) : X → Prop where
  | root {x : X} : x ∈ roots → Reachable store roots x
  | linked {obligation : Obligation W X V} {x y : X} :
      obligation ∈ store → x ∈ obligation.support → y ∈ obligation.support →
      Reachable store roots x → Reachable store roots y

/-- Semantic projection of residual attributes. Native copying supplies this
reachability boundary; this definition is not an extra runtime collection pass. -/
noncomputable def project (store : List (Obligation W X V)) (roots : List X) :
    List (Obligation W X V) := by
  classical
  exact store.filter fun obligation =>
    decide (∃ x ∈ obligation.support, Reachable store roots x)

theorem mem_project (store : List (Obligation W X V)) (roots : List X)
    (obligation : Obligation W X V) :
    obligation ∈ project store roots ↔
      obligation ∈ store ∧ ∃ x ∈ obligation.support, Reachable store roots x := by
  classical
  simp [project]

theorem projected_support_reachable (store : List (Obligation W X V)) (roots : List X)
    (obligation : Obligation W X V) (h : obligation ∈ project store roots) :
    ∀ y ∈ obligation.support, Reachable store roots y := by
  obtain ⟨hs, x, hx, hr⟩ := (mem_project store roots obligation).1 h
  exact fun y hy => .linked hs hx hy hr

theorem reachable_visible_check_retained (store : List (Obligation W X V)) (roots : List X)
    (obligation : Obligation W X V) (hs : obligation ∈ store)
    {x : X} (hx : x ∈ obligation.support) (hr : x ∈ roots) :
    obligation ∈ project store roots :=
  (mem_project store roots obligation).2 ⟨hs, x, hx, .root hr⟩

theorem hidden_component_discarded (store : List (Obligation W X V)) (roots : List X)
    (obligation : Obligation W X V)
    (hidden : ∀ x ∈ obligation.support, ¬ Reachable store roots x) :
    obligation ∉ project store roots := by
  intro h
  obtain ⟨_, x, hx, hr⟩ := (mem_project store roots obligation).1 h
  exact hidden x hx hr

theorem no_roots_no_residuals (store : List (Obligation W X V)) : project store [] = [] := by
  have noReach : ∀ x, ¬ Reachable store [] x := by
    intro x h
    induction h with
    | root h => cases h
    | linked _ _ _ _ ih => exact ih
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro obligation h
  obtain ⟨_, x, _, hr⟩ := (mem_project store [] obligation).1 h
  exact noReach x hr

structure GuardState (W X V : Type) where
  world : W
  valuation : PartialValuation X V
  pending : List (Obligation W X V)

/-- Posting checks the known portion first; successful posting records the
joint residual obligation without binding a program variable or changing data. -/
def post (fallback : V) (obligation : Obligation W X V) (state : GuardState W X V) :
    Option (GuardState W X V) :=
  if obligation.check state.world fallback state.valuation then
    some { state with pending := state.pending ++ [obligation] }
  else none

theorem post_preserves_world (fallback : V) (obligation : Obligation W X V)
    (before after : GuardState W X V) (h : post fallback obligation before = some after) :
    after.world = before.world := by
  unfold post at h
  split at h
  · cases h
    rfl
  · cases h

theorem post_preserves_bindings (fallback : V) (obligation : Obligation W X V)
    (before after : GuardState W X V) (h : post fallback obligation before = some after) :
    after.valuation = before.valuation := by
  unfold post at h
  split at h
  · cases h
    rfl
  · cases h

theorem post_records_joint_check (fallback : V) (obligation : Obligation W X V)
    (before after : GuardState W X V) (h : post fallback obligation before = some after) :
    obligation ∈ after.pending := by
  unfold post at h
  split at h
  · cases h
    simp
  · cases h

theorem post_rejects_ready_mismatch (fallback : V) (obligation : Obligation W X V)
    (state : GuardState W X V) (ready : obligation.ready state.valuation = true)
    (mismatch : obligation.test state.world (realize fallback state.valuation) = false) :
    post fallback obligation state = none := by
  simp [post, check, ready, mismatch]

/-- Waking pending checks can fail, but does not synthesize any answer value. -/
def wake (fallback : V) (state : GuardState W X V) : Option (GuardState W X V) :=
  if checkAll state.pending state.world fallback state.valuation then
    some { state with pending := state.pending.filter fun obligation => !obligation.ready state.valuation }
  else none

theorem wake_checks_every_ready_obligation (fallback : V) (before after : GuardState W X V)
    (success : wake fallback before = some after)
    (obligation : Obligation W X V) (posted : obligation ∈ before.pending)
    (ready : obligation.ready before.valuation = true) :
    obligation.test before.world (realize fallback before.valuation) = true := by
  unfold wake at success
  split at success
  next accepted =>
    have checked := (List.all_eq_true.1 accepted) obligation posted
    simpa [check, ready] using checked
  next => cases success

end Obligation

end Mettapedia.Logic.ConstraintTypes
