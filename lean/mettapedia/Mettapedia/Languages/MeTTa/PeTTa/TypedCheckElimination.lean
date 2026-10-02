import Mathlib.Data.List.Forall2
import Mathlib.Order.Defs.Unbundled

/-!
# Type checks on typed PeTTa calls that can be eliminated

PeTTa's Prolog reference implementation (`get-type` in `src/metta.pl`) guards a call of a
function that has a declared type by `get-type` checks: of the arguments against the declared
domains, and of the result against the declared codomain.  This file models the `get-type`
relation and proves the facts that allow such checks to be removed.

When such a check fails the reference tries the metatype of the value instead.  A check that
succeeds does not reach that alternative, so it plays no role for the checks shown here to
succeed.

## The relation

`get-type` relates a value to a type and is called in two modes.

* *Fresh mode*: the type is unknown.  `answers decls v` is the ordered list of answers, with
  multiplicity.
* *Bound mode*: the type is expected.  `check decls v d` is the number of times the check of
  `v` against `d` succeeds.  The expected type may have unconstrained positions `Ty.any`,
  independent of each other; against the wholly unconstrained type the check succeeds once
  for every fresh answer (`check_any`).

For a table `decls` of declarations `(: symbol type)` the rules are:

* a variable has the unconstrained type, and passes every check once;
* a symbol has its declared types, in declaration order, or `%Undefined%` if it has none;
* an application of `n` arguments whose head symbol is declared `(-> D₁ … Dₙ C)` has type
  `C`, once for every way its arguments check against `D₁ … Dₙ`; the declarations of the head
  are taken in declaration order;
* an application without such a candidate is a data tuple: its types are the tuples of the
  types of its elements, the leftmost element varying slowest, and it is checked element by
  element against a tuple type of the same length;
* a check that no candidate passes succeeds once if the expected type accepts `%Undefined%`.

Bound mode is not a filter on the fresh answers.  By the last rule a symbol declared with
some type passes the check against the domain `%Undefined%`, and a data tuple is checked
element by element, not through its type.  Against a named type the two do coincide
(`check_con`).

## Scope

* No equation for `get-type` is user-defined, and the subject of every declaration is a
  symbol.  Numbers, strings and booleans behave as symbols with one built-in declaration.
* Declarations are monomorphic (`Monomorphic`): declared types have no type variable.
  Polymorphic declarations are not modelled, because a type variable shared between two
  positions of a declaration constrains them jointly, whereas the positions `Ty.any` are
  independent.  A symbol with a polymorphic declaration, such as a typed function whose call
  is being checked, is not part of the table and must not occur in the values.  The theorems
  hold for every table; it is the agreement of the model with the reference that needs
  monomorphic declarations.
* Function types are a constructor of their own, whereas the reference represents
  `(-> D₁ … Dₙ C)` as the tuple headed by the symbol `->`.  The two agree as long as `->` is
  not used as the name of a type and no application whose head is a variable is compared with
  a function type, neither as the value checked against a function type nor, through its own
  type, as the expected type.

## Main results

* `answers_singleton_of_functional`: with at most one declaration per symbol (`Functional`)
  every value has exactly one answer, `ty decls v`.  `check_of_functional`: a check then
  succeeds at most once, namely when `passes decls v d`.  Functional declarations are also
  necessary (`functional_iff_answers_singleton`).
* `ty_subst_inst`: instantiating the variables of a value refines its type (`Inst`), provided
  the value is `SpineSafe`: no application has a variable as its head, and the arguments of a
  head symbol with a function-type declaration are closed.  Neither condition can be dropped,
  see `Examples`.
* `checkAgainst_iff`: `checkAgainst` decides `Inst`.  `result_check_redundant` and
  `result_check_once`: the check of an instance of a spine-safe value against the type of
  that value succeeds, and exactly once when declarations are functional.  More generally a
  value passes once the check against every type that generalizes its own
  (`check_eq_one_of_inst`).
* `dead_binding_erasure`, `check_erasure` and `result_check_erasure`: a guard with a single
  answer that leaves the continuation unchanged can be erased from an ordered answer
  pipeline.  A guard with two answers cannot (`flatMap_pair`).
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.TypedCheckElimination

universe u v

/-! ## Types, values and declarations -/

/-- Types. -/
inductive Ty : Type
  /-- The unconstrained type: the type of a variable occurrence, and in an expected type a
  position that accepts every type. -/
  | any : Ty
  /-- `%Undefined%`, the type of a symbol without declaration. -/
  | undef : Ty
  /-- A named type. -/
  | con (n : Nat) : Ty
  /-- A tuple type `(t₁ … tₙ)`, the type of a data tuple. -/
  | tup (ts : List Ty) : Ty
  /-- A function type `(-> D₁ … Dₙ C)`. -/
  | arrow (doms : List Ty) (cod : Ty) : Ty

/-- Values. -/
inductive Val : Type
  /-- An occurrence of the variable `x`. -/
  | var (x : Nat) : Val
  /-- The symbol `s`. -/
  | sym (s : Nat) : Val
  /-- The application `(e₁ … eₙ)`; its head is `e₁`.  The empty application is allowed. -/
  | app (es : List Val) : Val

/-- A table of declarations: `decls s` lists the types declared for the symbol `s` by
`(: s type)`, in declaration order and with repetitions. -/
abbrev Decls := Nat → List Ty

/-- Declarations are functional when every symbol has at most one declaration. -/
def Functional (decls : Decls) : Prop := ∀ s, (decls s).length ≤ 1

/-- A type is ground when it has no unconstrained position. -/
inductive Ty.Ground : Ty → Prop
  | undef : Ground .undef
  | con (n : Nat) : Ground (.con n)
  | tup {ts : List Ty} : (∀ t ∈ ts, Ground t) → Ground (.tup ts)
  | arrow {doms : List Ty} {cod : Ty} :
      (∀ d ∈ doms, Ground d) → Ground cod → Ground (.arrow doms cod)

/-- Declarations are monomorphic when every declared type is ground. -/
def Monomorphic (decls : Decls) : Prop := ∀ s, ∀ t ∈ decls s, t.Ground

/-! ## The instance preorder -/

/-- `Inst g s`: the type `s` is an instance of the type `g`, that is, `s` refines unconstrained
positions of `g`.  The unconstrained type is above every type, `%Undefined%` and named types
are above themselves only, tuple and function types are compared componentwise and need
equal lengths. -/
inductive Inst : Ty → Ty → Prop
  | any (t : Ty) : Inst .any t
  | undef : Inst .undef .undef
  | con (n : Nat) : Inst (.con n) (.con n)
  | tup {gs ss : List Ty} : List.Forall₂ Inst gs ss → Inst (.tup gs) (.tup ss)
  | arrow {gds sds : List Ty} {gc sc : Ty} :
      List.Forall₂ Inst gds sds → Inst gc sc → Inst (.arrow gds gc) (.arrow sds sc)

mutual
theorem Inst.refl : ∀ t : Ty, Inst t t
  | .any => .any _
  | .undef => .undef
  | .con n => .con n
  | .tup ts => .tup (Inst.reflList ts)
  | .arrow ds c => .arrow (Inst.reflList ds) (Inst.refl c)
private theorem Inst.reflList : ∀ ts : List Ty, List.Forall₂ Inst ts ts
  | [] => .nil
  | t :: ts => .cons (Inst.refl t) (Inst.reflList ts)
end

mutual
private theorem Inst.transAux : ∀ a b c : Ty, Inst a b → Inst b c → Inst a c
  | .any, _, _, _, _ => .any _
  | .undef, _, _, h₁, h₂ => by cases h₁; exact h₂
  | .con _, _, _, h₁, h₂ => by cases h₁; exact h₂
  | .tup as, _, _, h₁, h₂ => by
      cases h₁ with
      | tup h₁ =>
        cases h₂ with
        | tup h₂ => exact .tup (Inst.transListAux as _ _ h₁ h₂)
  | .arrow as a, _, _, h₁, h₂ => by
      cases h₁ with
      | arrow h₁ h₁' =>
        cases h₂ with
        | arrow h₂ h₂' =>
          exact .arrow (Inst.transListAux as _ _ h₁ h₂) (Inst.transAux a _ _ h₁' h₂')
private theorem Inst.transListAux : ∀ as bs cs : List Ty,
    List.Forall₂ Inst as bs → List.Forall₂ Inst bs cs → List.Forall₂ Inst as cs
  | [], _, _, h₁, h₂ => by cases h₁; cases h₂; exact .nil
  | a :: as, _, _, h₁, h₂ => by
      cases h₁ with
      | cons h₁ h₁' =>
        cases h₂ with
        | cons h₂ h₂' =>
          exact .cons (Inst.transAux a _ _ h₁ h₂) (Inst.transListAux as _ _ h₁' h₂')
end

theorem Inst.trans {a b c : Ty} (h₁ : Inst a b) (h₂ : Inst b c) : Inst a c :=
  Inst.transAux a b c h₁ h₂

instance : IsPreorder Ty Inst where
  refl := Inst.refl
  trans := fun _ _ _ => Inst.trans

mutual
/-- `checkAgainst g s` decides whether `s` is an instance of `g`: the unification of an
expected type `g`, whose unconstrained positions are independent, with a candidate type
`s`. -/
def checkAgainst : (general specific : Ty) → Bool
  | .any, _ => true
  | .undef, .undef => true
  | .con n, .con m => decide (n = m)
  | .tup gs, .tup ss => checkAgainstList gs ss
  | .arrow gds gc, .arrow sds sc => checkAgainstList gds sds && checkAgainst gc sc
  | _, _ => false
/-- `checkAgainst` on lists of the same length, componentwise. -/
def checkAgainstList : List Ty → List Ty → Bool
  | [], [] => true
  | g :: gs, s :: ss => checkAgainst g s && checkAgainstList gs ss
  | _, _ => false
end

mutual
theorem inst_of_checkAgainst : ∀ g s : Ty, checkAgainst g s = true → Inst g s
  | .any, s, _ => .any s
  | .undef, s, h => by
      cases s with
      | undef => exact .undef
      | _ => simp [checkAgainst] at h
  | .con n, s, h => by
      cases s with
      | con m =>
        rw [checkAgainst] at h
        cases of_decide_eq_true h
        exact .con n
      | _ => simp [checkAgainst] at h
  | .tup gs, s, h => by
      cases s with
      | tup ss =>
        rw [checkAgainst] at h
        exact .tup (forall₂_of_checkAgainstList gs ss h)
      | _ => simp [checkAgainst] at h
  | .arrow gds gc, s, h => by
      cases s with
      | arrow sds sc =>
        rw [checkAgainst, Bool.and_eq_true] at h
        exact .arrow (forall₂_of_checkAgainstList gds sds h.1) (inst_of_checkAgainst gc sc h.2)
      | _ => simp [checkAgainst] at h
theorem forall₂_of_checkAgainstList : ∀ gs ss : List Ty,
    checkAgainstList gs ss = true → List.Forall₂ Inst gs ss
  | [], ss, h => by
      cases ss with
      | nil => exact .nil
      | cons _ _ => simp [checkAgainstList] at h
  | g :: gs, ss, h => by
      cases ss with
      | nil => simp [checkAgainstList] at h
      | cons s ss =>
        rw [checkAgainstList, Bool.and_eq_true] at h
        exact .cons (inst_of_checkAgainst g s h.1) (forall₂_of_checkAgainstList gs ss h.2)
end

mutual
theorem checkAgainst_of_inst : ∀ g s : Ty, Inst g s → checkAgainst g s = true
  | .any, _, _ => by simp [checkAgainst]
  | .undef, _, h => by cases h; simp [checkAgainst]
  | .con n, _, h => by cases h; simp [checkAgainst]
  | .tup gs, _, h => by
      cases h with
      | tup h => simpa [checkAgainst] using checkAgainstList_of_forall₂ gs _ h
  | .arrow gds gc, _, h => by
      cases h with
      | arrow hd hc =>
        simp [checkAgainst, checkAgainstList_of_forall₂ gds _ hd, checkAgainst_of_inst gc _ hc]
theorem checkAgainstList_of_forall₂ : ∀ gs ss : List Ty,
    List.Forall₂ Inst gs ss → checkAgainstList gs ss = true
  | [], _, h => by cases h; simp [checkAgainstList]
  | g :: gs, _, h => by
      cases h with
      | cons h hs =>
        simp [checkAgainstList, checkAgainst_of_inst g _ h, checkAgainstList_of_forall₂ gs _ hs]
end

/-- `checkAgainst` decides the instance preorder. -/
theorem checkAgainst_iff (g s : Ty) : checkAgainst g s = true ↔ Inst g s :=
  ⟨inst_of_checkAgainst g s, checkAgainst_of_inst g s⟩

theorem checkAgainstList_iff (gs ss : List Ty) :
    checkAgainstList gs ss = true ↔ List.Forall₂ Inst gs ss :=
  ⟨forall₂_of_checkAgainstList gs ss, checkAgainstList_of_forall₂ gs ss⟩

instance : DecidableRel Inst := fun g s => decidable_of_iff _ (checkAgainst_iff g s)

/-- The types that generalize the named type `con n` are the unconstrained type and `con n`
itself. -/
theorem checkAgainst_con_right (t : Ty) (n : Nat) :
    checkAgainst t (.con n) = true ↔ t = .any ∨ t = .con n := by
  cases t <;> simp [checkAgainst]

/-! ## The `get-type` relation -/

/-- Fresh-mode fallback: when there is no candidate the answer is `%Undefined%`. -/
def orUndef : List Ty → List Ty
  | [] => [.undef]
  | t :: ts => t :: ts

/-- Bound-mode fallback: when no candidate passes, the check against `d` succeeds once if `d`
accepts `%Undefined%`. -/
def orFallback (c : Nat) (d : Ty) : Nat :=
  if c = 0 then (checkAgainst d .undef).toNat else c

/-- All ways of picking one member from each list, the leftmost choice varying slowest. -/
def tuples {α : Type u} : List (List α) → List (List α)
  | [] => [[]]
  | ts :: rest => ts.flatMap fun t => (tuples rest).map (t :: ·)

/-- The types against which the `n` elements of a data tuple are checked when the tuple is
expected to have type `d`: an unconstrained `d` constrains no element, a tuple type gives its
components, every other type rejects the tuple. -/
def Ty.components : Ty → Nat → Option (List Ty)
  | .any, n => some (List.replicate n .any)
  | .tup ds, _ => some ds
  | _, _ => none

mutual
/-- Fresh mode: the ordered answers of `get-type` on `v`, with multiplicity. -/
def answers (decls : Decls) : Val → List Ty
  | .var _ => [.any]
  | .sym s => orUndef (decls s)
  | .app es =>
      match funCands decls es with
      | [] => (tuples (answersList decls es)).map .tup
      | t :: ts => t :: ts
/-- The answers of each element of a list of values. -/
def answersList (decls : Decls) : List Val → List (List Ty)
  | [] => []
  | e :: es => answers decls e :: answersList decls es
/-- Bound mode: the number of times the check of `v` against the expected type `d`
succeeds. -/
def check (decls : Decls) : Val → Ty → Nat
  | .var _, _ => 1
  | .sym s, d => orFallback ((decls s).countP (checkAgainst d)) d
  | .app es, d =>
      match funCands decls es with
      | [] =>
          orFallback
            (match d.components es.length with
             | some ds => checkList decls es ds
             | none => 0) d
      | t :: ts => orFallback ((t :: ts).countP (checkAgainst d)) d
/-- The number of ways a list of values checks against a list of expected types of the same
length. -/
def checkList (decls : Decls) : List Val → List Ty → Nat
  | [], [] => 1
  | e :: es, d :: ds => check decls e d * checkList decls es ds
  | _, _ => 0
/-- The function-type candidates of the application `(e₁ … eₙ)`: for each declaration
`(-> D₁ … Dₘ C)` of a head symbol, in declaration order, `C` once for every way the arguments
check against the domains. -/
def funCands (decls : Decls) : List Val → List Ty
  | .sym f :: args =>
      (decls f).flatMap fun
        | .arrow doms cod => List.replicate (checkList decls args doms) cod
        | _ => []
  | _ => []
end

theorem answersList_eq_map (decls : Decls) :
    ∀ es : List Val, answersList decls es = es.map (answers decls)
  | [] => rfl
  | e :: es => by rw [answersList, answersList_eq_map decls es, List.map_cons]

theorem orUndef_ne_nil (ts : List Ty) : orUndef ts ≠ [] := by
  cases ts <;> simp [orUndef]

theorem orFallback_toNat (b : Bool) (d : Ty) :
    orFallback b.toNat d = (b || checkAgainst d .undef).toNat := by
  cases b <;> simp [orFallback]

theorem orFallback_of_ne_zero {c : Nat} (hc : c ≠ 0) (d : Ty) : orFallback c d = c := by
  simp [orFallback, hc]

theorem orFallback_con (c n : Nat) : orFallback c (.con n) = c := by
  cases c <;> simp [orFallback, checkAgainst]

theorem orFallback_undef_ne_zero (c : Nat) : orFallback c .undef ≠ 0 := by
  cases c <;> simp [orFallback, checkAgainst]

theorem tuples_map_singleton {α : Type u} (ts : List α) :
    tuples (ts.map fun t => [t]) = [ts] := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [tuples, ih]

theorem tuples_ne_nil {α : Type u} :
    ∀ {L : List (List α)}, (∀ ts ∈ L, ts ≠ []) → tuples L ≠ []
  | [], _ => by simp [tuples]
  | ts :: rest, h => by
      obtain ⟨t, ts', rfl⟩ := List.exists_cons_of_ne_nil (h ts (List.mem_cons_self ..))
      obtain ⟨r, rs, hr⟩ := List.exists_cons_of_ne_nil
        (tuples_ne_nil fun ts' h' => h ts' (List.mem_cons_of_mem _ h'))
      simp [tuples, hr]

theorem length_tuples_cons {α : Type u} (ts : List α) (rest : List (List α)) :
    (tuples (ts :: rest)).length = ts.length * (tuples rest).length := by
  induction ts with
  | nil => simp [tuples]
  | cons t ts ih =>
      simp only [tuples, List.flatMap_cons, List.length_append, List.length_map,
        List.length_cons] at ih ⊢
      rw [ih, Nat.succ_mul, Nat.add_comm]

theorem countP_checkAgainst_any (l : List Ty) : l.countP (checkAgainst .any) = l.length := by
  induction l with
  | nil => rfl
  | cons t ts _ => simp [checkAgainst]

section

variable {decls : Decls}

mutual
/-- `get-type` never fails in fresh mode. -/
theorem answers_ne_nil : ∀ v : Val, answers decls v ≠ []
  | .var _ => by simp [answers]
  | .sym s => by simp [answers, orUndef_ne_nil]
  | .app es => by
      simp only [answers]
      split
      · simpa using tuples_ne_nil (answersList_ne_nil es)
      · simp
theorem answersList_ne_nil : ∀ es : List Val, ∀ ts ∈ answersList decls es, ts ≠ []
  | [], _, h => by simp [answersList] at h
  | e :: es, ts, h => by
      simp only [answersList, List.mem_cons] at h
      rcases h with rfl | h
      · exact answers_ne_nil e
      · exact answersList_ne_nil es ts h
end

mutual
/-- Fresh mode is bound mode against the unconstrained type: the check succeeds once for
every fresh answer. -/
theorem check_any : ∀ v : Val, check decls v .any = (answers decls v).length
  | .var _ => by simp [check, answers]
  | .sym s => by
      simp only [check, answers, countP_checkAgainst_any]
      cases decls s <;> simp [orUndef, orFallback, checkAgainst]
  | .app es => by
      have hne : (tuples (answersList decls es)).length ≠ 0 := fun h =>
        tuples_ne_nil (answersList_ne_nil (decls := decls) es) (List.eq_nil_of_length_eq_zero h)
      simp only [check, answers]
      cases funCands decls es with
      | nil =>
          simp only [Ty.components, checkList_any es, List.length_map]
          exact orFallback_of_ne_zero hne _
      | cons t ts =>
          simp only [countP_checkAgainst_any]
          exact orFallback_of_ne_zero (by simp) _
theorem checkList_any : ∀ es : List Val,
    checkList decls es (List.replicate es.length .any) = (tuples (answersList decls es)).length
  | [] => by simp [checkList, answersList, tuples]
  | e :: es => by
      simp only [List.length_cons, List.replicate_succ, checkList, answersList,
        length_tuples_cons, check_any e, checkList_any es]
end

/-- Every function-type candidate is the codomain of a declared function type. -/
theorem mem_funCands {es : List Val} {t : Ty} (h : t ∈ funCands decls es) :
    ∃ f doms, Ty.arrow doms t ∈ decls f := by
  match es, h with
  | .sym f :: args, h =>
    simp only [funCands, List.mem_flatMap] at h
    obtain ⟨a, ha, ht⟩ := h
    split at ht
    · next doms cod => exact ⟨f, doms, (List.eq_of_mem_replicate ht) ▸ ha⟩
    · simp at ht

/-- Every value passes the check against `%Undefined%`. -/
theorem check_undef_ne_zero (v : Val) : check decls v .undef ≠ 0 := by
  cases v with
  | var x => simp [check]
  | sym s => rw [check]; exact orFallback_undef_ne_zero _
  | app es =>
    rw [check]
    split <;> exact orFallback_undef_ne_zero _

/-- Against a named type, bound mode is the test of each fresh answer when declarations are
monomorphic: the check succeeds once for every answer that is unconstrained or equal to the
expected type (`checkAgainst_con_right`). -/
theorem check_con (hm : Monomorphic decls) (v : Val) (n : Nat) :
    check decls v (.con n) = (answers decls v).countP fun t => checkAgainst t (.con n) := by
  have key : ∀ l : List Ty, (∀ t ∈ l, t ≠ .any) →
      orFallback (l.countP (checkAgainst (.con n))) (.con n) =
        l.countP fun t => checkAgainst t (.con n) := by
    intro l hl
    rw [orFallback_con]
    refine List.countP_congr fun t ht => ?_
    cases t with
    | any => exact absurd rfl (hl _ ht)
    | con m => rw [checkAgainst, checkAgainst, decide_eq_true_eq, decide_eq_true_eq]; exact eq_comm
    | _ => rfl
  cases v with
  | var x => simp [check, answers, checkAgainst]
  | sym s =>
    simp only [check, answers]
    rcases hd : decls s with _ | ⟨t, ts⟩
    · simp [orUndef, orFallback, checkAgainst]
    · rw [orUndef]
      exact key _ fun t ht h => by cases h ▸ hm s t (hd ▸ ht)
  | app es =>
    simp only [check, answers]
    rcases hc : funCands decls es with _ | ⟨t, ts⟩
    · simp only [Ty.components, orFallback_con, List.countP_map]
      generalize tuples (answersList decls es) = L
      induction L with
      | nil => rfl
      | cons a L ih => rw [List.countP_cons_of_neg (by simp [checkAgainst]), ← ih]
    · refine key _ fun t ht h => ?_
      obtain ⟨f, doms, hf⟩ := mem_funCands (hc ▸ ht)
      cases hm f _ hf with
      | arrow _ hcod => cases h ▸ hcod

end

/-! ## Typing under functional declarations -/

mutual
/-- The type of a value, read off the first declaration of each symbol. -/
def ty (decls : Decls) : Val → Ty
  | .var _ => .any
  | .sym s => (decls s).headD .undef
  | .app es =>
      match funTy decls es with
      | some cod => cod
      | none => .tup (tyList decls es)
/-- The types of a list of values. -/
def tyList (decls : Decls) : List Val → List Ty
  | [] => []
  | e :: es => ty decls e :: tyList decls es
/-- Whether the check of `v` against the expected type `d` succeeds, reading the first
declaration of each symbol. -/
def passes (decls : Decls) : Val → Ty → Bool
  | .var _, _ => true
  | .sym s, d => checkAgainst d ((decls s).headD .undef) || checkAgainst d .undef
  | .app es, d =>
      match funTy decls es with
      | some cod => checkAgainst d cod || checkAgainst d .undef
      | none =>
          (match d.components es.length with
           | some ds => passesList decls es ds
           | none => false) || checkAgainst d .undef
/-- Whether a list of values checks against a list of expected types of the same length. -/
def passesList (decls : Decls) : List Val → List Ty → Bool
  | [], [] => true
  | e :: es, d :: ds => passes decls e d && passesList decls es ds
  | _, _ => false
/-- The codomain of the first declaration of the head symbol of `(e₁ … eₙ)`, when that
declaration is a function type whose domains the arguments check against. -/
def funTy (decls : Decls) : List Val → Option Ty
  | .sym f :: args =>
      match decls f with
      | .arrow doms cod :: _ => if passesList decls args doms then some cod else none
      | _ => none
  | _ => none
end

theorem tyList_eq_map (decls : Decls) : ∀ es : List Val, tyList decls es = es.map (ty decls)
  | [] => rfl
  | e :: es => by rw [tyList, tyList_eq_map decls es, List.map_cons]

section

variable {decls : Decls}

mutual
/-- Under functional declarations typing is a function: every value has exactly one fresh
answer. -/
theorem answers_singleton_of_functional (hf : Functional decls) :
    ∀ v : Val, answers decls v = [ty decls v]
  | .var _ => by simp [answers, ty]
  | .sym s => by
      have hs := hf s
      simp only [answers, ty]
      rcases h : decls s with _ | ⟨t, _ | ⟨t', l⟩⟩
      · simp [orUndef]
      · simp [orUndef]
      · simp [h] at hs
  | .app es => by
      simp only [answers, ty, funCands_of_functional hf es, answersList_of_functional hf es]
      cases funTy decls es <;> simp [tuples_map_singleton]
theorem answersList_of_functional (hf : Functional decls) :
    ∀ es : List Val, answersList decls es = (tyList decls es).map fun t => [t]
  | [] => by simp [answersList, tyList]
  | e :: es => by
      simp [answersList, tyList, answers_singleton_of_functional hf e,
        answersList_of_functional hf es]
/-- Under functional declarations a check succeeds at most once, namely when `passes`. -/
theorem check_of_functional (hf : Functional decls) :
    ∀ (v : Val) (d : Ty), check decls v d = (passes decls v d).toNat
  | .var _, _ => by simp [check, passes]
  | .sym s, d => by
      have hs := hf s
      simp only [check, passes]
      rcases h : decls s with _ | ⟨t, _ | ⟨t', l⟩⟩
      · simpa using orFallback_toNat false d
      · cases hc : checkAgainst d t <;> simp [orFallback, hc]
      · simp [h] at hs
  | .app es, d => by
      simp only [check, passes, funCands_of_functional hf es]
      cases funTy decls es with
      | none =>
          cases d.components es.length with
          | none => simpa using orFallback_toNat false d
          | some ds => simpa [checkList_of_functional hf es ds] using orFallback_toNat _ d
      | some cod => cases hc : checkAgainst d cod <;> simp [orFallback, hc]
theorem checkList_of_functional (hf : Functional decls) :
    ∀ (es : List Val) (ds : List Ty), checkList decls es ds = (passesList decls es ds).toNat
  | [], [] => by simp [checkList, passesList]
  | [], _ :: _ => by simp [checkList, passesList]
  | _ :: _, [] => by simp [checkList, passesList]
  | e :: es, d :: ds => by
      simp only [checkList, passesList, check_of_functional hf e d,
        checkList_of_functional hf es ds]
      cases passes decls e d <;> cases passesList decls es ds <;> rfl
theorem funCands_of_functional (hf : Functional decls) :
    ∀ es : List Val, funCands decls es = (funTy decls es).toList
  | [] => by simp [funCands, funTy]
  | .var _ :: _ => by simp [funCands, funTy]
  | .app _ :: _ => by simp [funCands, funTy]
  | .sym f :: args => by
      have hs := hf f
      simp only [funCands, funTy]
      rcases h : decls f with _ | ⟨t, _ | ⟨t', l⟩⟩
      · rfl
      · cases t with
        | arrow doms cod =>
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
            checkList_of_functional hf args doms]
          cases passesList decls args doms <;> rfl
        | _ => rfl
      · simp [h] at hs
end

/-- Under functional declarations a check has no choice point. -/
theorem check_le_one_of_functional (hf : Functional decls) (v : Val) (d : Ty) :
    check decls v d ≤ 1 := by
  rw [check_of_functional hf]
  exact Bool.toNat_le _

/-- Under functional declarations every value passes the check against `%Undefined%` exactly
once. -/
theorem check_undef_of_functional (hf : Functional decls) (v : Val) :
    check decls v .undef = 1 :=
  Nat.le_antisymm (check_le_one_of_functional hf v _)
    (Nat.pos_of_ne_zero (check_undef_ne_zero v))

/-- Typing is single-valued exactly when declarations are functional. -/
theorem functional_iff_answers_singleton :
    Functional decls ↔ ∀ v : Val, ∃ t, answers decls v = [t] := by
  refine ⟨fun hf v => ⟨_, answers_singleton_of_functional hf v⟩, fun h s => ?_⟩
  obtain ⟨t, ht⟩ := h (.sym s)
  rw [answers] at ht
  rcases hd : decls s with _ | ⟨a, _ | ⟨b, l⟩⟩
  · simp
  · simp
  · rw [hd, orUndef] at ht
    cases ht

end

/-! ## Substitution and spine-safe values -/

namespace Val

mutual
/-- Simultaneous substitution of values for variables: every occurrence of the variable `x`
becomes `θ x`. -/
def subst (θ : Nat → Val) : Val → Val
  | .var x => θ x
  | .sym s => .sym s
  | .app es => .app (substList θ es)
/-- Substitution in each element of a list of values. -/
def substList (θ : Nat → Val) : List Val → List Val
  | [] => []
  | e :: es => subst θ e :: substList θ es
end

theorem substList_eq_map (θ : Nat → Val) : ∀ es : List Val, substList θ es = es.map (subst θ)
  | [] => rfl
  | e :: es => by rw [substList, substList_eq_map θ es, List.map_cons]

@[simp] theorem subst_var (θ : Nat → Val) (x : Nat) : (var x).subst θ = θ x := by rw [subst]

@[simp] theorem subst_sym (θ : Nat → Val) (s : Nat) : (sym s).subst θ = sym s := by rw [subst]

@[simp] theorem subst_app (θ : Nat → Val) (es : List Val) :
    (app es).subst θ = app (es.map (subst θ)) := by rw [subst, substList_eq_map]

/-- A value is closed when no variable occurs in it. -/
inductive Closed : Val → Prop
  | sym (s : Nat) : Closed (.sym s)
  | app {es : List Val} : (∀ e ∈ es, Closed e) → Closed (.app es)

/-- A substitution leaves a closed value unchanged. -/
theorem Closed.subst_eq {v : Val} (h : v.Closed) (θ : Nat → Val) : v.subst θ = v := by
  induction h with
  | sym s => exact subst_sym θ s
  | app _ ih => rw [subst_app, List.map_congr_left ih, List.map_id']

end Val

/-- The symbol `f` has a function-type declaration. -/
def HasArrow (decls : Decls) (f : Nat) : Prop := ∃ doms cod, Ty.arrow doms cod ∈ decls f

/-- The condition on the head of the application `(e₁ … eₙ)`: the head is not a variable, and
if it is a symbol with a function-type declaration then the arguments are closed. -/
def HeadSafe (decls : Decls) : List Val → Prop
  | .var _ :: _ => False
  | .sym f :: args => HasArrow decls f → ∀ a ∈ args, a.Closed
  | _ => True

/-- A value is spine-safe when every application in it, at any depth, satisfies `HeadSafe`:
its head is not a variable, and a head symbol with a function-type declaration has closed
arguments.

Under these conditions an application is typed by a function type before a substitution
exactly when it is after it.  An instantiated argument of a typed head can stop checking
against its domain, and an instantiated head variable can become a typed head; either way the
type of the application changes to an unrelated one.  The condition on typed heads ignores
arities, so it is sufficient but not necessary. -/
inductive SpineSafe (decls : Decls) : Val → Prop
  | var (x : Nat) : SpineSafe decls (.var x)
  | sym (s : Nat) : SpineSafe decls (.sym s)
  | app {es : List Val} :
      HeadSafe decls es → (∀ e ∈ es, SpineSafe decls e) → SpineSafe decls (.app es)

section

variable {decls : Decls}

/-- A closed value is spine-safe. -/
theorem Val.Closed.spineSafe {v : Val} (h : v.Closed) : SpineSafe decls v := by
  induction h with
  | sym s => exact .sym s
  | @app es hes ih =>
      refine .app ?_ ih
      match es, hes with
      | [], _ => trivial
      | .var _ :: _, hes => cases hes _ (List.mem_cons_self ..)
      | .sym _ :: _, hes => exact fun _ a ha => hes a (List.mem_cons_of_mem _ ha)
      | .app _ :: _, _ => trivial

/-- A substitution either leaves the elements of a head-safe application unchanged, or the
application is a data tuple before and after it. -/
theorem HeadSafe.map_subst {es : List Val} (h : HeadSafe decls es) (θ : Nat → Val) :
    es.map (Val.subst θ) = es ∨
      (funTy decls es = none ∧ funTy decls (es.map (Val.subst θ)) = none) := by
  match es, h with
  | [], _ => exact .inr ⟨by simp [funTy], by simp [funTy]⟩
  | .var _ :: _, h => exact h.elim
  | .app _ :: _, _ => exact .inr ⟨by simp [funTy], by simp [funTy]⟩
  | .sym f :: args, h =>
    rcases hd : decls f with _ | ⟨t, rest⟩
    · exact .inr ⟨by simp [funTy, hd], by simp [funTy, hd]⟩
    · cases t with
      | arrow doms cod =>
        have hc := h ⟨doms, cod, by rw [hd]; exact List.mem_cons_self ..⟩
        refine .inl ?_
        rw [List.map_cons, Val.subst_sym,
          List.map_congr_left fun a ha => (hc a ha).subst_eq θ, List.map_id']
      | _ => exact .inr ⟨by simp [funTy, hd], by simp [funTy, hd]⟩

/-- Instantiating the variables of a spine-safe value refines its type. -/
theorem ty_subst_inst {v : Val} (h : SpineSafe decls v) (θ : Nat → Val) :
    Inst (ty decls v) (ty decls (v.subst θ)) := by
  induction h with
  | var x => rw [ty]; exact .any _
  | sym s => rw [Val.subst_sym]; exact Inst.refl _
  | @app es hhead _ ih =>
    rw [Val.subst_app]
    rcases hhead.map_subst θ with heq | ⟨h₁, h₂⟩
    · rw [heq]; exact Inst.refl _
    · simp only [ty, h₁, h₂, tyList_eq_map, List.map_map]
      exact .tup (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
        (List.forall₂_same.2 ih)))

/-- The fresh answers of a spine-safe value and of its instances, under functional
declarations: one each, the second an instance of the first. -/
theorem answers_subst_inst (hf : Functional decls) {v : Val} (h : SpineSafe decls v)
    (θ : Nat → Val) :
    ∃ g s, answers decls v = [g] ∧ answers decls (v.subst θ) = [s] ∧ Inst g s :=
  ⟨_, _, answers_singleton_of_functional hf v, answers_singleton_of_functional hf _,
    ty_subst_inst h θ⟩

/-! ## The result check -/

/-- The type of an instance of a spine-safe value unifies with the type of the value. -/
theorem result_check_redundant {v : Val} (h : SpineSafe decls v) (θ : Nat → Val) :
    checkAgainst (ty decls v) (ty decls (v.subst θ)) = true :=
  (checkAgainst_iff _ _).2 (ty_subst_inst h θ)

mutual
/-- A value passes the check against every type that its own type is an instance of. -/
theorem passes_of_inst : ∀ (v : Val) (g : Ty), Inst g (ty decls v) → passes decls v g = true
  | .var _, _, _ => by rw [passes]
  | .sym s, g, h => by
      rw [ty] at h
      rw [passes, checkAgainst_of_inst _ _ h]; rfl
  | .app es, g, h => by
      rw [ty] at h
      rw [passes]
      cases hft : funTy decls es with
      | some cod =>
          rw [hft] at h
          simp [checkAgainst_of_inst _ _ h]
      | none =>
          rw [hft] at h
          cases h with
          | any => simp [checkAgainst]
          | tup hs => simp [Ty.components, passesList_of_forall₂ es _ hs]
theorem passesList_of_forall₂ : ∀ (es : List Val) (gs : List Ty),
    List.Forall₂ Inst gs (tyList decls es) → passesList decls es gs = true
  | [], _, h => by
      rw [tyList] at h
      cases h
      rw [passesList]
  | e :: es, _, h => by
      rw [tyList] at h
      cases h with
      | cons h hs => simp [passesList, passes_of_inst e _ h, passesList_of_forall₂ es _ hs]
end

/-- Under functional declarations a value passes exactly once the check against every type
that its own type is an instance of. -/
theorem check_eq_one_of_inst (hf : Functional decls) {v : Val} {g : Ty}
    (h : Inst g (ty decls v)) : check decls v g = 1 := by
  rw [check_of_functional hf, passes_of_inst v g h]; rfl

/-- Under functional declarations, the check of an instance of a spine-safe value against the
type of that value succeeds exactly once. -/
theorem result_check_once (hf : Functional decls) {v : Val} (h : SpineSafe decls v)
    (θ : Nat → Val) : check decls (v.subst θ) (ty decls v) = 1 :=
  check_eq_one_of_inst hf (ty_subst_inst h θ)

end

/-! ## Erasing a guard from an answer pipeline -/

section

variable {σ : Type u} {α : Type v}

/-- A guard with the single answer `s'` can be erased when the continuation `k` does not
distinguish `s'` from the state `s` before the guard: the bindings made by the guard are
dead. -/
theorem dead_binding_erasure (k : σ → List α) (s s' : σ) (h : k s' = k s) :
    [s'].flatMap k = k s :=
  (List.append_nil (k s')).trans h

/-- A guard with two answers runs the continuation twice. -/
theorem flatMap_pair (k : σ → List α) (s' s'' : σ) :
    [s', s''].flatMap k = k s' ++ k s'' :=
  congrArg (k s' ++ ·) (List.append_nil (k s''))

variable {decls : Decls}

/-- Erasure of a check: under functional declarations, a guard that answers once for every
success of the check of `v` against a type that generalizes the type of `v`, and whose
bindings are dead, can be erased. -/
theorem check_erasure (hf : Functional decls) {v : Val} {g : Ty} (h : Inst g (ty decls v))
    (k : σ → List α) (s : σ) (guard : List σ) (hlen : guard.length = check decls v g)
    (hdead : ∀ s' ∈ guard, k s' = k s) : guard.flatMap k = k s := by
  rw [check_eq_one_of_inst hf h] at hlen
  obtain ⟨s', rfl⟩ := List.length_eq_one_iff.1 hlen
  exact dead_binding_erasure k s s' (hdead s' (List.mem_singleton_self s'))

/-- Erasure of the result check: under functional declarations, the check of an instance of a
spine-safe value against the type of that value can be erased when its bindings are dead. -/
theorem result_check_erasure (hf : Functional decls) {v : Val} (h : SpineSafe decls v)
    (θ : Nat → Val) (k : σ → List α) (s : σ) (guard : List σ)
    (hlen : guard.length = check decls (v.subst θ) (ty decls v))
    (hdead : ∀ s' ∈ guard, k s' = k s) : guard.flatMap k = k s :=
  check_erasure hf (ty_subst_inst h θ) k s guard hlen hdead

end

/-! ## Examples -/

namespace Examples

/-- The named types are `Nat` (`con 0`), `A` (`con 1`) and `B` (`con 2`).  The symbols are

* `0`: `w`, declared `(-> Nat Nat)`;
* `1`: `foo`, not declared;
* `2`: `Z`, declared `Nat`;
* `3`: `pair`, not declared;
* `5`: `fu`, declared `(-> %Undefined% Nat)`;
* `6`: `a`, declared `A`;
* `7`: `gt`, declared `(-> (A B) Nat)`. -/
def sig : Decls
  | 0 => [.arrow [.con 0] (.con 0)]
  | 2 => [.con 0]
  | 5 => [.arrow [.undef] (.con 0)]
  | 6 => [.con 1]
  | 7 => [.arrow [.tup [.con 1, .con 2]] (.con 0)]
  | _ => []

/-- `sig` with two symbols that are declared twice: `4`, `two`, declared `A` and `B`, and
`8`, `m`, declared `(-> A X)` and `(-> B Y)`, where `X` is `con 3` and `Y` is `con 4`. -/
def sig₂ : Decls
  | 4 => [.con 1, .con 2]
  | 8 => [.arrow [.con 1] (.con 3), .arrow [.con 2] (.con 4)]
  | s => sig s

theorem functional_sig : Functional sig := by
  intro s
  unfold sig
  split <;> simp

theorem monomorphic_sig : Monomorphic sig := by
  intro s t ht
  unfold sig at ht
  split at ht <;> simp only [List.mem_singleton, List.not_mem_nil] at ht <;> subst ht
  · exact .arrow (List.forall_mem_singleton.2 (.con 0)) (.con 0)
  · exact .con 0
  · exact .arrow (List.forall_mem_singleton.2 .undef) (.con 0)
  · exact .con 1
  · exact .arrow (List.forall_mem_singleton.2 (.tup (List.forall_mem_cons.2
      ⟨.con 1, List.forall_mem_singleton.2 (.con 2)⟩))) (.con 0)

/-- A declaration with a type variable is not monomorphic. -/
example : ¬ Monomorphic fun _ => [.any] := fun h => nomatch h 0 _ (List.mem_cons_self ..)

/-- A symbol with two declarations has two answers, and a check against an unconstrained type
succeeds twice. -/
example : answers sig₂ (.sym 4) = [.con 1, .con 2] := rfl
example : (answers sig₂ (.sym 4)).length = 2 := rfl
example : check sig₂ (.sym 4) .any = 2 := rfl
example : ¬ Functional sig₂ := fun h => absurd (h 4) (by decide)

/-- A data tuple of symbols with two declarations: the leftmost element varies slowest. -/
example : answers sig₂ (.app [.sym 4, .sym 4]) =
    [.tup [.con 1, .con 1], .tup [.con 1, .con 2], .tup [.con 2, .con 1],
      .tup [.con 2, .con 2]] := rfl

/-- `(m two)` has the types `X` and `Y`: the function types of the head are tried in
declaration order. -/
example : answers sig₂ (.app [.sym 8, .sym 4]) = [.con 3, .con 4] := rfl

/-- A symbol without declaration has the single answer `%Undefined%`. -/
example : answers sig (.sym 1) = [.undef] := rfl

/-- `(pair $u $u)` has type `(%Undefined% $_0 $_1)`: each occurrence of a variable has its
own unconstrained type. -/
example : answers sig (.app [.sym 3, .var 0, .var 0]) = [.tup [.undef, .any, .any]] := rfl

/-- `(w $q)` and `(w Z)` have type `Nat`; `(w foo)` is a data tuple. -/
example : answers sig (.app [.sym 0, .var 0]) = [.con 0] := rfl
example : answers sig (.app [.sym 0, .sym 2]) = [.con 0] := rfl
example : answers sig (.app [.sym 0, .sym 1]) =
    [.tup [.arrow [.con 0] (.con 0), .undef]] := rfl

/-- `(fu Z)` has type `Nat`: `Z` passes the check against the domain `%Undefined%`, although
its only answer is `Nat`. -/
example : answers sig (.app [.sym 5, .sym 2]) = [.con 0] := rfl
example : check sig (.sym 2) .undef = 1 := rfl
example : (answers sig (.sym 2)).countP (fun t => checkAgainst t .undef) = 0 := rfl

/-- `(fu two)` has type `Nat` once, not once for every declaration of `two`. -/
example : answers sig₂ (.app [.sym 5, .sym 4]) = [.con 0] := rfl

/-- `(gt (a $x))` has type `Nat`: the data tuple `(a $x)` is checked element by element
against the domain `(A B)`, which is not its answer `(A $_0)`. -/
example : answers sig (.app [.sym 7, .app [.sym 6, .var 0]]) = [.con 0] := rfl
example : answers sig (.app [.sym 6, .var 0]) = [.tup [.con 1, .any]] := rfl

/-- The arguments of a typed head must be closed.  `(w $q)` has type `Nat`, its instance
`(w foo)` has a tuple type and fails the check against `Nat`. -/
example : ¬ Inst (ty sig (.app [.sym 0, .var 0]))
    (ty sig ((Val.app [.sym 0, .var 0]).subst fun _ => .sym 1)) := by decide

example : check sig ((Val.app [.sym 0, .var 0]).subst fun _ => .sym 1)
    (ty sig (.app [.sym 0, .var 0])) = 0 := rfl

example : ¬ SpineSafe sig (.app [.sym 0, .var 0]) := by
  intro h
  cases h with
  | app hh _ => cases hh ⟨_, _, List.mem_cons_self ..⟩ (.var 0) (List.mem_cons_self ..)

/-- The head of an application must not be a variable.  `($h Z)` has no head symbol and the
tuple type `($_0 Nat)`; its instance `(w Z)` has type `Nat` and fails the check against
`($_0 Nat)`. -/
example : ¬ Inst (ty sig (.app [.var 0, .sym 2]))
    (ty sig ((Val.app [.var 0, .sym 2]).subst fun _ => .sym 0)) := by decide

example : check sig ((Val.app [.var 0, .sym 2]).subst fun _ => .sym 0)
    (ty sig (.app [.var 0, .sym 2])) = 0 := rfl

example : ¬ SpineSafe sig (.app [.var 0, .sym 2]) := by
  intro h
  cases h with
  | app hh _ => exact hh

/-- The requirement of `SpineSafe` on typed heads alone: at any depth, a head symbol with a
function-type declaration has closed arguments.  Variable heads are allowed. -/
inductive TypedHeadsClosed (decls : Decls) : Val → Prop
  | var (x : Nat) : TypedHeadsClosed decls (.var x)
  | sym (s : Nat) : TypedHeadsClosed decls (.sym s)
  | app {es : List Val} :
      (∀ f args, es = .sym f :: args → HasArrow decls f → ∀ a ∈ args, a.Closed) →
      (∀ e ∈ es, TypedHeadsClosed decls e) → TypedHeadsClosed decls (.app es)

/-- The requirement on typed heads alone does not make instantiation refine the type: `($h Z)`
meets it, having no head symbol. -/
theorem not_inst_of_typedHeadsClosed :
    ∃ (v : Val) (θ : Nat → Val),
      TypedHeadsClosed sig v ∧ ¬ Inst (ty sig v) (ty sig (v.subst θ)) := by
  refine ⟨.app [.var 0, .sym 2], fun _ => .sym 0, .app (fun f args h => by cases h) ?_,
    by decide⟩
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> constructor

/-- `(pair Z Z)` is closed, `(pair $u $u)` is not. -/
example : (Val.app [.sym 3, .sym 2, .sym 2]).Closed := by
  refine .app fun e he => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> constructor

example : ¬ (Val.app [.sym 3, .var 0, .var 0]).Closed := by
  intro h
  cases h with
  | app h => cases h (.var 0) (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- `(pair $u $u)` is spine-safe: its head has no function-type declaration. -/
theorem spineSafe_pair : SpineSafe sig (.app [.sym 3, .var 0, .var 0]) := by
  refine .app (fun h => ?_) fun e he => ?_
  · obtain ⟨doms, cod, h⟩ := h
    cases h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> constructor

/-- `(pair $u (w Z))` is spine-safe: the typed head `w` has the closed argument `Z`. -/
example : SpineSafe sig (.app [.sym 3, .var 0, .app [.sym 0, .sym 2]]) := by
  refine .app (fun h => ?_) fun e he => ?_
  · obtain ⟨doms, cod, h⟩ := h
    cases h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact .sym 3
    · exact .var 0
    · refine .app (fun _ a ha => ?_) fun e he => ?_
      · rw [List.mem_singleton] at ha
        subst ha
        exact .sym 2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> constructor

/-- The type `(%Undefined% Nat Nat)` of the instance `(pair Z Z)` of `(pair $u $u)` is an
instance of the type `(%Undefined% $_0 $_1)` of `(pair $u $u)`, and `(pair Z Z)` passes the
check against the latter exactly once. -/
example : Inst (.tup [.undef, .any, .any]) (.tup [.undef, .con 0, .con 0]) :=
  ty_subst_inst spineSafe_pair fun _ => .sym 2

example : check sig ((Val.app [.sym 3, .var 0, .var 0]).subst fun _ => .sym 2)
    (ty sig (.app [.sym 3, .var 0, .var 0])) = 1 :=
  result_check_once functional_sig spineSafe_pair _

/-- The check of `(pair Z Z)` against the type of `(pair $u $u)` can be erased: a guard with
the single answer `()` in front of any continuation `k`. -/
example (k : Unit → List Bool) : [()].flatMap k = k () :=
  result_check_erasure functional_sig spineSafe_pair (fun _ => .sym 2) k () [()] rfl
    fun _ _ => rfl

/-- A guard with two answers duplicates the answers of the continuation, even when both
answers leave the continuation unchanged. -/
example : ([(), ()] : List Unit).flatMap (fun _ => [true]) = [true, true] := rfl
example : ([(), ()] : List Unit).flatMap (fun _ => [true]) ≠ (fun _ : Unit => [true]) () := by
  decide

end Examples

end Mettapedia.Languages.MeTTa.PeTTa.TypedCheckElimination
