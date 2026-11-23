import Mettapedia.Languages.HOLLight.RuleModuleComponents

/-! The order observed by HOL Light's hypothesis-list operations. The source
equations below follow the `alphaorder`, `orda` and `ordav` rules of the
named kernel module. A prepared key eliminates paired binder environments.
A malformed abstraction can still be ordered by its outer constructor,
so a failed preparation must defer to the original judgment. -/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RuleModuleAlphaOrder

open RuleModulePrimitives (Str Flag)
open RuleModuleComparisonLaws (Ty Term cmpLeaf cmpType tmEq)
abbrev Result := RuleModulePrimitives.Ord
abbrev Key := Str × Ty
abbrev Env := List (Key × Key)

private def asVar (x : Key) : Term := .Var x.1 x.2

/-- The cases of ordav-cons and its four continuations, with the empty
environment using cmp-term on two free variables. -/
def namedVarOrder (x y : Key) : Env → Result
  | [] => RuleModuleComparisonLaws.cmpTerm (asVar x) (asVar y)
  | (a, b) :: rest =>
    match tmEq (asVar x) (asVar a), tmEq (asVar y) (asVar b) with
    | .yes, .yes => .eq
    | .yes, .no => .lt
    | .no, .yes => .gt
    | .no, .no => namedVarOrder x y rest

/-- Continue the lexicographic comparison only on a tie. -/
private def next (o : Result) (body : Unit → Option Result) : Option Result :=
  match o with
  | .lt => some .lt
  | .gt => some .gt
  | .eq => body ()

/-- Named reference: mixed constructors are Const < Var < Comb < Abs.
The module has no same-head abstraction rule for a non-variable binder. -/
def namedOrder (env : Env) : Term → Term → Option Result
  | .Const n a, .Const m b => some (cmpLeaf n a m b)
  | .Var n a, .Var m b => some (namedVarOrder (n,a) (m,b) env)
  | .Comb f x, .Comb g y => do
    let o ← namedOrder env f g
    next o (fun _ => namedOrder env x y)
  | .Abs (.Var n a) s, .Abs (.Var m b) t =>
    next (cmpType a b) (fun _ => namedOrder (((n,a),(m,b)) :: env) s t)
  | .Abs .., .Abs .. => none
  | .Const .., _ | .Var .., .Comb .. | .Var .., .Abs .. | .Comb .., .Abs .. => some .lt
  | _, _ => some .gt
termination_by structural left _ => left

/-- Resolve only declared binder positions. Free variables retain both name
and type. Nearest binder is zero. -/
inductive Position (K : Type) where
  | bound (index : Nat)
  | free (key : K)
  deriving DecidableEq

private def deeper {K : Type} : Position K → Position K
  | .bound n => .bound (n + 1)
  | .free x => .free x

def locate {K : Type} [DecidableEq K] (x : K) : List K → Position K
  | [] => .free x
  | k :: ks => if x = k then .bound 0 else deeper (locate x ks)

def comparePosition {K : Type} (freeCmp : K → K → Result) : Position K → Position K → Result
  | .bound n, .bound m => RuleModuleComponents.natCmp n m
  | .bound _, .free _ => .lt
  | .free _, .bound _ => .gt
  | .free x, .free y => freeCmp x y

private def freeCmp (x y : Key) := cmpLeaf x.1 x.2 y.1 y.2

private theorem deeper_order {K : Type} (cmp : K → K → Result) (x y : Position K) :
    comparePosition cmp (deeper x) (deeper y) = comparePosition cmp x y := by
  cases x <;> cases y <;> simp [deeper, comparePosition, RuleModuleComponents.natCmp]

private theorem eq_flag (x y : Key) : tmEq (asVar x) (asVar y) = if x = y then .yes else .no := by
  have h := RuleModuleInterning.tmEq_eq_yes_iff (asVar x) (asVar y)
  by_cases same : x = y
  · subst y; simp [RuleModuleComparisonLaws.tmEq_refl]
  · have ne : asVar x ≠ asVar y := by simpa [asVar, Prod.ext_iff] using same
    cases value : tmEq (asVar x) (asVar y) with
    | yes => exact False.elim (ne (h.mp value))
    | no => simp [same]

theorem positions_compute_ordav (env : Env) (x y : Key) :
    comparePosition freeCmp (locate x (env.map Prod.fst)) (locate y (env.map Prod.snd)) =
      namedVarOrder x y env := by
  induction env with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨a,b⟩
    simp only [List.map_cons, locate, namedVarOrder, eq_flag]
    by_cases hx : x = a <;> by_cases hy : y = b <;> simp [hx, hy, deeper_order, ← ih]
    all_goals first
      | rfl
      | (cases locate x (List.map Prod.fst rest) <;> rfl)
      | (cases locate y (List.map Prod.snd rest) <;> rfl)

/-- A reusable comparison key. Each binder's annotation remains outside its
body, and neither an application nor a constant loses its constructor. -/
inductive Scoped where
  | const (name : Str) (ty : Ty)
  | var (position : Position Key)
  | app (fn arg : Scoped)
  | abs (domain : Ty) (body : Scoped)
  deriving DecidableEq

def prepare (env : List Key) : Term → Option Scoped
  | .Const n a => some (.const n a)
  | .Var n a => some (.var (locate (n,a) env))
  | .Comb f x => return .app (← prepare env f) (← prepare env x)
  | .Abs (.Var n a) t => return .abs a (← prepare ((n,a)::env) t)
  | .Abs _ _ => none

def order : Scoped → Scoped → Result
  | .const n a, .const m b => cmpLeaf n a m b
  | .var x, .var y => comparePosition freeCmp x y
  | .app f x, .app g y =>
    match order f g with
    | .lt => .lt | .gt => .gt | .eq => order x y
  | .abs a s, .abs b t =>
    match cmpType a b with
    | .lt => .lt | .gt => .gt | .eq => order s t
  | .const .., _ | .var .., .app .. | .var .., .abs .. | .app .., .abs .. => .lt
  | _, _ => .gt

theorem prepared_order (env : Env) (left right : Term) {l r : Scoped}
    (hl : prepare (env.map Prod.fst) left = some l)
    (hr : prepare (env.map Prod.snd) right = some r) :
    namedOrder env left right = some (order l r) := by
  induction left generalizing env right l r with
  | Var n a | Const n a =>
    cases right with
    | Var m b | Const m b =>
      simp [prepare] at hl hr
      subst l; subst r
      first | rfl | exact congrArg some (positions_compute_ordav env _ _).symm
    | Comb g y =>
      simp [prepare, Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, _, _, rfl⟩ := hr
      simp [prepare] at hl
      subst l; rfl
    | Abs v t =>
      cases v <;> simp [prepare, Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, rfl⟩ := hr
      simp [prepare] at hl
      subst l; rfl
  | Comb f x hf hx =>
    simp [prepare, Option.bind_eq_some_iff] at hl
    obtain ⟨_, pf, _, px, rfl⟩ := hl
    cases right with
    | Var m b | Const m b => simp [prepare] at hr; subst r; rfl
    | Abs v t =>
      cases v <;> simp [prepare, Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, rfl⟩ := hr
      rfl
    | Comb g y =>
      simp [prepare, Option.bind_eq_some_iff] at hr
      obtain ⟨_, pg, _, py, rfl⟩ := hr
      simp only [namedOrder, hf env g pf pg, order]
      cases order _ _ <;> simp [next, hx env y px py]
  | Abs v s _ hs =>
    cases v <;> simp [prepare, Option.bind_eq_some_iff] at hl
    rename_i n a _binderIH
    obtain ⟨_, ps, rfl⟩ := hl
    cases right with
    | Var m b | Const m b => simp [prepare] at hr; subst r; rfl
    | Comb g y =>
      simp [prepare, Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, _, _, rfl⟩ := hr
      rfl
    | Abs v t =>
      cases v <;> simp [prepare, Option.bind_eq_some_iff] at hr
      rename_i m b
      obtain ⟨_, pt, rfl⟩ := hr
      simp only [namedOrder, order]
      cases cmpType a b <;> first | rfl | exact hs (((n,a),(m,b)) :: env) t ps pt

def compiledOrder (env : Env) (left right : Term) : Option Result :=
  match prepare (env.map Prod.fst) left, prepare (env.map Prod.snd) right with
  | some l, some r => some (order l r)
  | _, _ => namedOrder env left right

/-- Preserves successes, failures and the sign used by ordered hypothesis sets. -/
theorem compiledOrder_exact (env : Env) (left right : Term) :
    compiledOrder env left right = namedOrder env left right := by
  unfold compiledOrder
  split <;> first | rfl | exact (prepared_order env left right ‹_› ‹_›).symm

private theorem number_eq (i j : Nat) : RuleModuleComponents.natCmp i j = .eq ↔ i = j := by
  unfold RuleModuleComponents.natCmp
  by_cases h : i < j <;> by_cases k : j < i <;> simp [h, k] <;> omega

private theorem position_eq (x y : Position Key) : comparePosition freeCmp x y = .eq ↔ x = y := by
  cases x <;> cases y <;> simp [comparePosition, number_eq, freeCmp, Prod.ext_iff,
    RuleModuleInterning.cmpLeaf_eq_iff]

private theorem tie (first second : Result) :
    (match first with | .lt => RuleModulePrimitives.Ord.lt | .gt => .gt | .eq => second) = .eq ↔
    first = .eq ∧ second = .eq := by cases first <;> simp

/-- Alpha equivalence is the zero case of the complete order; the other
two outcomes must survive compilation for the hypothesis-set clients. -/
theorem order_eq_iff (l r : Scoped) : order l r = .eq ↔ l = r := by
  induction l generalizing r with
  | const n a => cases r <;> simp [order, RuleModuleInterning.cmpLeaf_eq_iff]
  | var pos => cases r <;> simp [order, position_eq]
  | app f x hf hx => cases r <;> simp [order, tie, hf, hx]
  | abs a s ih =>
    cases r with
    | var | app | const => simp [order]
    | abs b t =>
      exact (tie (cmpType a b) (order s t)).trans
        ((and_congr (RuleModuleInterning.cmpType_eq_iff a b) (ih t)).trans (Scoped.abs.injEq ..).symm.to_iff)

end Mettapedia.Languages.HOLLight.RuleModuleAlphaOrder
