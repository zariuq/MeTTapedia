import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedUnification
import Mathlib.Data.Nat.Pairing

/-!
# Capture-avoiding COMM for the MeTTa-calculus

A guard `for(t <- x)P` binds every variable of its pattern `t`, in `t` and in
`P`; the channel `x` is outside its scope. Alpha-equivalence is decided by
closing every guard: each bound occurrence becomes the code of its guard's
depth and its position in the guard's pattern (`close`). Two processes are
alpha-equivalent when their closed forms are equal (`AlphaEq`), and the
manuscript's renaming rule preserves the closed form (`alpha_rule_close`).

The executable step works on the closed form, so alpha-equivalent sources have
the same reducts (`cstep_alpha_invariant`). Its COMM opens each input apart:
the bound variables of both patterns become fresh names, distinct from each
other and from every free name of the redex; then the patterns are unified by
the principal unifier, and each continuation receives the dotted unifier.

The relational semantics `Step admit` has the manuscript's four rules over
named processes, with alpha-equivalence as its equivalence. Its COMM carries
the variable convention (`Apart`): the inputs' pattern variables are distinct
from each other, absent from the other input, and never rebound inside their
own continuation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm
  (psubst pvars PSubst firstOrder applyDot_eq)

/-! ## Binding structure -/

/-- Where a bound variable is bound: the depth of its guard, counted outward,
and its position in that guard's frame. -/
def lookupBound : List (List String) → String → Option (ℕ × ℕ)
  | [], _ => none
  | vs :: env, x =>
      if x ∈ vs then some (0, vs.idxOf x)
      else (lookupBound env x).map fun found => (found.1 + 1, found.2)

/-- The code of a bound occurrence. -/
def boundCode (depth index : ℕ) : Pattern := .bvar (Nat.pair depth index)

mutual
/-- Close every guard: bound occurrences become codes. -/
def closeIn (env : List (List String)) : Pattern → Pattern
  | .fvar x =>
      match lookupBound env x with
      | some found => boundCode found.1 found.2
      | none => .fvar x
  | .bvar n => .bvar n
  | .apply c args => .apply c (if c = "MFor" then closeFor env args else closeList env args)
  | .lambda nm body => .lambda nm (closeIn env body)
  | .multiLambda n nms body => .multiLambda n nms (closeIn env body)
  | .subst body repl => .subst (closeIn env body) (closeIn env repl)
  | .collection ct elems rest => .collection ct (closeList env elems) rest
def closeList (env : List (List String)) : List Pattern → List Pattern
  | [] => []
  | p :: ps => closeIn env p :: closeList env ps
/-- The arguments of a guard: pattern, channel, continuation. -/
def closeFor (env : List (List String)) : List Pattern → List Pattern
  | [] => []
  | [p] => [closeIn env p]
  | [p, q] => [closeIn env p, closeIn env q]
  | t :: x :: k :: rest =>
      closeIn [pvars (closeIn [] t)] t :: closeIn env x :: closeIn (pvars (closeIn [] t) :: env) k ::
        closeList env rest
end

/-- The variables a guard with pattern `t` binds: the free variables of `t`,
listed by occurrence; a variable's position is its first occurrence. Guards
quoted inside a pattern bind their own variables. -/
def frame (t : Pattern) : List String := pvars (closeIn [] t)

/-- The closed form of a process. -/
def close (p : Pattern) : Pattern := closeIn [] p

/-- Alpha-equivalence: equal closed forms. -/
def AlphaEq (p q : Pattern) : Prop := close p = close q

instance (p q : Pattern) : Decidable (AlphaEq p q) := inferInstanceAs (Decidable (close p = close q))

/-! ## Opening a closed guard -/

mutual
/-- Replace the codes bound at depth `depth` by the given values. Patterns of
inner guards bind only their own frame and are left alone. -/
def instantiateAt (depth : ℕ) (value : ℕ → Option Pattern) : Pattern → Pattern
  | .bvar n =>
      if (Nat.unpair n).1 = depth then (value (Nat.unpair n).2).getD (.bvar n) else .bvar n
  | .fvar x => .fvar x
  | .apply c args =>
      .apply c (if c = "MFor" then instantiateFor depth value args
        else instantiateList depth value args)
  | .lambda nm body => .lambda nm (instantiateAt depth value body)
  | .multiLambda n nms body => .multiLambda n nms (instantiateAt depth value body)
  | .subst body repl => .subst (instantiateAt depth value body) (instantiateAt depth value repl)
  | .collection ct elems rest => .collection ct (instantiateList depth value elems) rest
def instantiateList (depth : ℕ) (value : ℕ → Option Pattern) : List Pattern → List Pattern
  | [] => []
  | p :: ps => instantiateAt depth value p :: instantiateList depth value ps
def instantiateFor (depth : ℕ) (value : ℕ → Option Pattern) : List Pattern → List Pattern
  | [] => []
  | [p] => [instantiateAt depth value p]
  | [p, q] => [instantiateAt depth value p, instantiateAt depth value q]
  | t :: x :: k :: rest =>
      t :: instantiateAt depth value x :: instantiateAt (depth + 1) value k ::
        instantiateList depth value rest
end

/-- Open the outermost frame with names. -/
def openWith (names : List String) (p : Pattern) : Pattern :=
  instantiateAt 0 (fun index => names[index]?.map Pattern.fvar) p

/-- Open a guard's own pattern: its codes are all at depth zero. -/
def openPattern (names : List String) (t : Pattern) : Pattern :=
  instantiateAt 0 (fun index => names[index]?.map Pattern.fvar) t

/-! ## Fresh names -/

def maxLength : List String → ℕ
  | [] => 0
  | name :: names => max name.length (maxLength names)

/-- A name longer than every name in `avoid`. -/
def freshName (avoid : List String) (slot : ℕ) : String :=
  String.ofList (List.replicate (maxLength avoid + slot + 1) '#')

/-- `count` fresh names starting at `start`. -/
def freshNames (avoid : List String) (start count : ℕ) : List String :=
  (List.range count).map fun slot => freshName avoid (start + slot)

/-! ## Guard-free patterns and code counts -/

mutual
/-- No guard occurs anywhere in the pattern. -/
def guardFree : Pattern → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .apply c args => c != "MFor" && guardFreeList args
  | .lambda _ body => guardFree body
  | .multiLambda _ _ body => guardFree body
  | .subst body repl => guardFree body && guardFree repl
  | .collection _ elems _ => guardFreeList elems
def guardFreeList : List Pattern → Bool
  | [] => true
  | p :: ps => guardFree p && guardFreeList ps
end

mutual
/-- How many codes occur; enough names to open a closed pattern. -/
def codeCount : Pattern → ℕ
  | .bvar _ => 1
  | .fvar _ => 0
  | .apply _ args => codeCountList args
  | .lambda _ body => codeCount body
  | .multiLambda _ _ body => codeCount body
  | .subst body repl => codeCount body + codeCount repl
  | .collection _ elems _ => codeCountList elems
def codeCountList : List Pattern → ℕ
  | [] => 0
  | p :: ps => codeCount p + codeCountList ps
end

/-! ## The corrected executable step -/

/-- Is this a guard? Returns pattern, channel and continuation. -/
def asGuard : Pattern → Option (Pattern × Pattern × Pattern)
  | .apply "MFor" [t, x, k] => some (t, x, k)
  | _ => none

/-- Complete a binding list: every variable of `vs` that it leaves unbound is
bound to itself. The dot of the completed list quotes every pattern variable:
a bound one reads the quotation of its value, an unbound one the quotation
of itself. -/
def completeBindings (vs : List String) (bs : Bindings) : Bindings :=
  bs ++ (vs.filter fun v => (bs.lookup v).isNone).map fun v => (v, .fvar v)

/-- COMM on closed guards: open both inputs apart, unify, and dot both bodies
with the completed unifier. -/
def commClosed (avoid : List String) (first second : Pattern) : List Pattern :=
  match asGuard first, asGuard second with
  | some (t, x, k), some (u, y, l) =>
      if x = y ∧ guardFree t = true ∧ guardFree u = true then
        let leftNames := freshNames avoid 0 (codeCount t)
        let rightNames := freshNames avoid (codeCount t) (codeCount u)
        match unify (openPattern leftNames t) (openPattern rightNames u) with
        | some bs =>
            let all := completeBindings
              (pvars (openPattern leftNames t) ++ pvars (openPattern rightNames u)) bs
            [par (applyDot all (openWith leftNames k)) (applyDot all (openWith rightNames l))]
        | none => []
      else []
  | _, _ => []

/-- One step of a closed process: COMM at a binary parallel composition, the
left component's steps under it, and reflection over its process's steps. -/
def stepClosed (avoid : List String) : Pattern → List Pattern
  | .collection .hashBag [p, q] none =>
      commClosed avoid p q ++ (stepClosed avoid p).map fun next => par next q
  | .apply "MRef" [x, p] => (stepClosed avoid p).map fun next => pFor (tProc next) x pZero
  | _ => []

/-- **The corrected executable step.** -/
def cstep (p : Pattern) : List Pattern := stepClosed (pvars (close p)) (close p)

/-! ## Equations of the closed form -/

theorem pvars_apply (c : String) (args : List Pattern) :
    pvars (.apply c args) = pvars.pvarsList args := by simp [pvars]

theorem mem_pvarsList {ps : List Pattern} {x : String} :
    x ∈ pvars.pvarsList ps ↔ ∃ p ∈ ps, x ∈ pvars p := by
  induction ps with
  | nil => simp [pvars.pvarsList]
  | cons p ps ih => simp [pvars.pvarsList, ih]

theorem closeIn_pFor (env : List (List String)) (t x k : Pattern) :
    closeIn env (pFor t x k) = pFor (closeIn [frame t] t) (closeIn env x) (closeIn (frame t :: env) k) := by
  simp [pFor, closeIn, closeFor, closeList, frame]

theorem closeIn_par (env : List (List String)) (p q : Pattern) :
    closeIn env (par p q) = par (closeIn env p) (closeIn env q) := by
  simp [par, pPar, closeIn, closeList]

theorem closeIn_pReflect (env : List (List String)) (x p : Pattern) :
    closeIn env (pReflect x p) = pReflect (closeIn env x) (closeIn env p) := by
  simp [pReflect, closeIn, closeList]

theorem closeIn_nQuote (env : List (List String)) (p : Pattern) :
    closeIn env (nQuote p) = nQuote (closeIn env p) := by
  simp [nQuote, closeIn, closeList]

theorem closeIn_tProc (env : List (List String)) (p : Pattern) :
    closeIn env (tProc p) = tProc (closeIn env p) := by
  simp [tProc, closeIn, closeList]

theorem closeIn_pZero (env : List (List String)) : closeIn env pZero = pZero := by
  simp [pZero, closeIn, closeList]

/-- Frames that bind nothing find nothing. -/
theorem lookupBound_of_empty {env : List (List String)} (empty : ∀ f ∈ env, f = []) (x : String) :
    lookupBound env x = none := by
  induction env with
  | nil => rfl
  | cons f env ih =>
      have head := empty f (List.mem_cons_self ..)
      subst head
      simp [lookupBound, ih fun g member => empty g (List.mem_cons_of_mem _ member)]

theorem lookupBound_isSome_of_mem {env : List (List String)} {f : List String} {x : String}
    (inside : f ∈ env) (member : x ∈ f) : ∃ found, lookupBound env x = some found := by
  induction env with
  | nil => cases inside
  | cons g env ih =>
      by_cases here : x ∈ g
      · exact ⟨(0, g.idxOf x), by simp [lookupBound, here]⟩
      · rcases List.mem_cons.mp inside with same | later
        · subst same; exact absurd member here
        · obtain ⟨found, eq⟩ := ih later
          exact ⟨(found.1 + 1, found.2), by simp [lookupBound, here, eq]⟩

theorem lookupBound_cons_isSome {env : List (List String)} {f : List String} {x : String}
    (found : ∃ found, lookupBound env x = some found) : ∃ found, lookupBound (f :: env) x = some found := by
  obtain ⟨found, eq⟩ := found
  by_cases here : x ∈ f
  · exact ⟨(0, f.idxOf x), by simp [lookupBound, here]⟩
  · exact ⟨(found.1 + 1, found.2), by simp [lookupBound, here, eq]⟩

theorem pvarsList_eq_flatMap (ps : List Pattern) : pvars.pvarsList ps = ps.flatMap pvars := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [pvars.pvarsList, ih]

theorem mem_pvars_apply_of' {c : String} {args : List Pattern} {q : Pattern} (member : q ∈ args)
    {x : String} (occurs : x ∈ pvars q) : x ∈ pvars (.apply c args) := by
  rw [pvars_apply, pvarsList_eq_flatMap]; exact List.mem_flatMap.mpr ⟨q, member, occurs⟩

theorem closeList_eq_map (env : List (List String)) (ps : List Pattern) :
    closeList env ps = ps.map (closeIn env) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [closeList, ih]

theorem closeFor_cons3 (env : List (List String)) (t x k : Pattern) (rest : List Pattern) :
    closeFor env (t :: x :: k :: rest) =
      closeIn [frame t] t :: closeIn env x :: closeIn (frame t :: env) k :: rest.map (closeIn env) := by
  simp [closeFor, closeList_eq_map, frame]

/-- The arguments of `apply`, closed. -/
theorem closeIn_apply (env : List (List String)) (c : String) (args : List Pattern) :
    closeIn env (.apply c args) =
      .apply c (if c = "MFor" then closeFor env args else args.map (closeIn env)) := by
  simp [closeIn, closeList_eq_map]

/-- Every way of closing an argument list closes each argument in some
environment that extends `env` by at most one frame of the arguments. -/
theorem closeFor_cases (env : List (List String)) (args : List Pattern) :
    (args.length < 3 ∧ closeFor env args = args.map (closeIn env)) ∨
      ∃ t x k rest, args = t :: x :: k :: rest ∧
        closeFor env args =
          closeIn [frame t] t :: closeIn env x :: closeIn (frame t :: env) k :: rest.map (closeIn env) := by
  match args with
  | [] => exact .inl ⟨by simp, rfl⟩
  | [p] => exact .inl ⟨by simp, by simp [closeFor]⟩
  | [p, q] => exact .inl ⟨by simp, by simp [closeFor]⟩
  | t :: x :: k :: rest => exact .inr ⟨t, x, k, rest, rfl, closeFor_cons3 env t x k rest⟩

theorem filter_flatMap' {α β : Type} (l : List α) (f : α → List β) (P : β → Bool) :
    (l.flatMap f).filter P = l.flatMap fun a => (f a).filter P := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.filter_append, ih]

theorem lookupBound_cons_isNone (f : List String) (env : List (List String)) (y : String) :
    (lookupBound (f :: env) y).isNone = ((lookupBound [f] y).isNone && (lookupBound env y).isNone) := by
  by_cases here : y ∈ f
  · simp [lookupBound, here]
  · simp [lookupBound, here]

/-- Closing in an environment removes exactly the free variables it binds. -/
theorem pvars_closeIn (p : Pattern) : ∀ env : List (List String),
    pvars (closeIn env p) = (pvars (closeIn [] p)).filter fun y => (lookupBound env y).isNone := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ env : List (List String),
      pvars (closeIn env q) = (pvars (closeIn [] q)).filter fun y => (lookupBound env y).isNone) with
  | bvar n => intro env; simp [closeIn, pvars]
  | fvar x =>
      intro env
      cases h : lookupBound env x <;> simp [closeIn, h, boundCode, pvars, lookupBound]
  | apply c args ih =>
      intro env
      rw [closeIn_apply, closeIn_apply]
      by_cases guard : c = "MFor"
      · simp only [guard, if_true]
        rcases closeFor_cases env args with ⟨short, eq⟩ | ⟨t, x, k, rest, rfl, eq⟩
        · rcases closeFor_cases [] args with ⟨_, eq'⟩ | ⟨_, _, _, _, same, _⟩
          · rw [eq, eq', pvars_apply, pvars_apply, pvarsList_eq_flatMap, pvarsList_eq_flatMap,
              List.flatMap_map, List.flatMap_map, filter_flatMap']
            exact List.flatMap_congr fun q member => ih q member env
          · subst same; simp at short; omega
        · rw [eq, closeFor_cons3, pvars_apply, pvars_apply, pvarsList_eq_flatMap, pvarsList_eq_flatMap]
          have patternNil : pvars (closeIn [frame t] t) = [] := by
            rw [ih t (by simp) [frame t], List.filter_eq_nil_iff]
            intro y member
            simp [lookupBound, frame, member]
          simp only [List.flatMap_cons, List.flatMap_map, patternNil, List.nil_append,
            List.filter_append, filter_flatMap']
          rw [ih x (by simp) env, ih k (by simp) (frame t :: env), ih k (by simp) [frame t],
            List.filter_filter]
          congr 1
          congr 1
          · congr 1
            funext y
            rw [lookupBound_cons_isNone, Bool.and_comm]
          · exact List.flatMap_congr fun q member => ih q (by simp [member]) env
      · simp only [guard, if_false]
        rw [pvars_apply, pvars_apply, pvarsList_eq_flatMap, pvarsList_eq_flatMap,
          List.flatMap_map, List.flatMap_map, filter_flatMap']
        exact List.flatMap_congr fun q member => ih q member env
  | lambda nm body ih => intro env; simpa [closeIn, pvars] using ih env
  | multiLambda n nms body ih => intro env; simpa [closeIn, pvars] using ih env
  | subst body repl ihb ihr => intro env; simp [closeIn, pvars, ihb env, ihr env, List.filter_append]
  | collection ct elems rest ih =>
      intro env
      simp only [closeIn, closeList_eq_map, pvars, pvarsList_eq_flatMap, List.flatMap_map,
        filter_flatMap']
      exact List.flatMap_congr fun q member => ih q member env
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member env
      rcases List.mem_cons.mp member with rfl | later
      · exact head env
      · exact tail q later env

/-- Closing only removes variables. -/
theorem pvars_closeIn_subset (p : Pattern) : ∀ env : List (List String), ∀ y ∈ pvars (closeIn env p),
    y ∈ pvars p := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ env : List (List String),
      ∀ y ∈ pvars (closeIn env q), y ∈ pvars q) with
  | bvar n => intro env y occurs; simp [closeIn, pvars] at occurs
  | fvar x =>
      intro env y occurs
      cases h : lookupBound env x <;> simp_all [closeIn, boundCode, pvars]
  | apply c args ih =>
      intro env y occurs
      rw [closeIn_apply, pvars_apply, pvarsList_eq_flatMap] at occurs
      obtain ⟨r, member, inR⟩ := List.mem_flatMap.mp occurs
      split at member
      · rcases closeFor_cases env args with ⟨_, eq⟩ | ⟨t, x, k, rest, rfl, eq⟩
        · rw [eq] at member
          obtain ⟨q, inside, rfl⟩ := List.mem_map.mp member
          exact mem_pvars_apply_of' inside (ih q inside env y inR)
        · rw [eq] at member
          simp only [List.mem_cons, List.mem_map] at member
          rcases member with rfl | rfl | rfl | ⟨q, inside, rfl⟩
          · exact mem_pvars_apply_of' (by simp) (ih t (by simp) _ y inR)
          · exact mem_pvars_apply_of' (by simp) (ih x (by simp) _ y inR)
          · exact mem_pvars_apply_of' (by simp) (ih k (by simp) _ y inR)
          · exact mem_pvars_apply_of' (by simp [inside]) (ih q (by simp [inside]) _ y inR)
      · obtain ⟨q, inside, rfl⟩ := List.mem_map.mp member
        exact mem_pvars_apply_of' inside (ih q inside env y inR)
  | lambda nm body ih => intro env y occurs; simpa [pvars] using ih env y (by simpa [closeIn, pvars] using occurs)
  | multiLambda n nms body ih =>
      intro env y occurs; simpa [pvars] using ih env y (by simpa [closeIn, pvars] using occurs)
  | subst body repl ihb ihr =>
      intro env y occurs
      simp only [closeIn, pvars, List.mem_append] at occurs ⊢
      rcases occurs with h | h
      · exact .inl (ihb env y h)
      · exact .inr (ihr env y h)
  | collection ct elems rest ih =>
      intro env y occurs
      simp only [closeIn, closeList_eq_map, pvars, pvarsList_eq_flatMap, List.mem_flatMap,
        List.mem_map] at occurs ⊢
      obtain ⟨r, ⟨q, inside, rfl⟩, inR⟩ := occurs
      exact ⟨q, inside, ih q inside env y inR⟩
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member env y occurs
      rcases List.mem_cons.mp member with rfl | later
      · exact head env y occurs
      · exact tail q later env y occurs

theorem frame_subset (t : Pattern) : ∀ y ∈ frame t, y ∈ pvars t := pvars_closeIn_subset t []

/-- A guard's pattern, closed in its own frame, has no variables. -/
theorem pvars_closed_pattern (t : Pattern) : pvars (closeIn [frame t] t) = [] := by
  rw [pvars_closeIn, List.filter_eq_nil_iff]
  intro y member
  simp [lookupBound, frame, member]

theorem frame_closed_pattern (t : Pattern) : frame (closeIn [frame t] t) = [] := by
  have sub := pvars_closeIn_subset (closeIn [frame t] t) []
  rw [pvars_closed_pattern] at sub
  show pvars (closeIn [] (closeIn [frame t] t)) = []
  exact List.eq_nil_iff_forall_not_mem.mpr fun y member => by simpa using sub y member

/-- Closing again in frames that bind nothing changes nothing. -/
theorem closeIn_closeIn (p : Pattern) :
    ∀ env env' : List (List String), (∀ f ∈ env, f = []) →
      closeIn env (closeIn env' p) = closeIn env' p := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps,
      ∀ env env' : List (List String), (∀ f ∈ env, f = []) →
        closeIn env (closeIn env' q) = closeIn env' q) with
  | bvar n => intro env env' _; simp [closeIn]
  | fvar x =>
      intro env env' empty
      cases eq : lookupBound env' x with
      | none => simp [closeIn, eq, lookupBound_of_empty empty]
      | some found => simp [closeIn, eq, boundCode]
  | apply c args ih =>
      intro env env' empty
      rw [closeIn_apply, closeIn_apply]
      by_cases guard : c = "MFor"
      · simp only [guard, if_true]
        rcases closeFor_cases env' args with ⟨short, eq⟩ | ⟨t, x, k, rest, rfl, eq⟩
        · rw [eq]
          rcases closeFor_cases env (args.map (closeIn env')) with ⟨_, eq'⟩ | ⟨t', x', k', rest', same, _⟩
          · rw [eq', List.map_map]
            congr 1
            apply List.map_congr_left
            intro q member
            exact ih q member env env' empty
          · have := congrArg List.length same
            simp at this
            omega
        · rw [eq, closeFor_cons3, frame_closed_pattern, List.map_map]
          congr 1
          refine List.cons_eq_cons.mpr ⟨ih t (by simp) [[]] [frame t] (by simp), ?_⟩
          refine List.cons_eq_cons.mpr ⟨ih x (by simp) env env' empty, ?_⟩
          refine List.cons_eq_cons.mpr ⟨ih k (by simp) ([] :: env) (frame t :: env') ?_, ?_⟩
          · intro f member
            rcases List.mem_cons.mp member with rfl | later
            · rfl
            · exact empty f later
          · apply List.map_congr_left
            intro q member
            exact ih q (by simp [member]) env env' empty
      · simp only [guard, if_false, List.map_map]
        congr 1
        apply List.map_congr_left
        intro q member
        exact ih q member env env' empty
  | lambda nm body ih => intro env env' empty; simp [closeIn, ih env env' empty]
  | multiLambda n nms body ih => intro env env' empty; simp [closeIn, ih env env' empty]
  | subst body repl ihb ihr => intro env env' empty; simp [closeIn, ihb env env' empty, ihr env env' empty]
  | collection ct elems rest ih =>
      intro env env' empty
      simp only [closeIn, closeList_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q member
      exact ih q member env env' empty
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member env env' empty
      rcases List.mem_cons.mp member with rfl | later
      · exact head env env' empty
      · exact tail q later env env' empty

/-- The closed form is a fixed point of closing. -/
theorem close_close (p : Pattern) : close (close p) = close p :=
  closeIn_closeIn p [] [] (by simp)

theorem alphaEq_close (p : Pattern) : AlphaEq (close p) p := close_close p

theorem AlphaEq.refl (p : Pattern) : AlphaEq p p := rfl
theorem AlphaEq.symm {p q : Pattern} (h : AlphaEq p q) : AlphaEq q p := Eq.symm h
theorem AlphaEq.trans {p q r : Pattern} (h : AlphaEq p q) (h' : AlphaEq q r) : AlphaEq p r := Eq.trans h h'

theorem AlphaEq.par {p p' q q' : Pattern} (hp : AlphaEq p p') (hq : AlphaEq q q') :
    AlphaEq (par p q) (par p' q') := by
  unfold AlphaEq close at *
  rw [closeIn_par, closeIn_par, hp, hq]

/-! ## The calculus fragment and renaming -/

mutual
/-- MeTTa-calculus syntax: variables, constructors and closed collections. It
has no MeTTa-IL binder, no code and no collection rest. -/
def calcTerm : Pattern → Bool
  | .bvar _ => false
  | .fvar _ => true
  | .apply _ args => calcList args
  | .lambda _ _ => false
  | .multiLambda _ _ _ => false
  | .subst _ _ => false
  | .collection _ elems rest => rest.isNone && calcList elems
def calcList : List Pattern → Bool
  | [] => true
  | p :: ps => calcTerm p && calcList ps
end

theorem calcList_iff (ps : List Pattern) : calcList ps = true ↔ ∀ p ∈ ps, calcTerm p = true := by
  induction ps with
  | nil => simp [calcList]
  | cons p ps ih => simp [calcList, ih]

theorem guardFreeList_iff (ps : List Pattern) :
    guardFreeList ps = true ↔ ∀ p ∈ ps, guardFree p = true := by
  induction ps with
  | nil => simp [guardFreeList]
  | cons p ps ih => simp [guardFreeList, ih]

/-- A guard-free process is its own closed form. -/
theorem closeIn_nil_of_guardFree (t : Pattern) (free : guardFree t = true) : closeIn [] t = t := by
  induction t using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, guardFree q = true → closeIn [] q = q) with
  | bvar n => rfl
  | fvar x => simp [closeIn, lookupBound]
  | apply c args ih =>
      simp only [guardFree, Bool.and_eq_true, bne_iff_ne, ne_eq, guardFreeList_iff] at free
      rw [closeIn_apply, if_neg free.1]
      conv_rhs => rw [← List.map_id args]
      exact congrArg _ (List.map_congr_left fun q member => ih q member (free.2 q member))
  | lambda nm body ih => simp [closeIn, ih free]
  | multiLambda n nms body ih => simp [closeIn, ih free]
  | subst body repl ihb ihr =>
      simp only [guardFree, Bool.and_eq_true] at free
      simp [closeIn, ihb free.1, ihr free.2]
  | collection ct elems rest ih =>
      simp only [guardFree, guardFreeList_iff] at free
      simp only [closeIn, closeList_eq_map]
      rw [List.map_congr_left fun q member => ih q member (free q member), List.map_id']
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member freeQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head freeQ
      · exact tail q later freeQ

/-- A guard-free pattern binds all its variables. -/
theorem frame_of_guardFree (t : Pattern) (free : guardFree t = true) : frame t = pvars t := by
  unfold frame; rw [closeIn_nil_of_guardFree t free]


/-- Rename every variable occurrence. -/
def rename (g : String → String) (p : Pattern) : Pattern := psubst (fun x => some (.fvar (g x))) p

theorem guardFree_rename (g : String → String) (p : Pattern) : guardFree (rename g p) = guardFree p := by
  unfold rename
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps,
      guardFree (psubst (fun x => some (.fvar (g x))) q) = guardFree q) with
  | bvar n => rfl
  | fvar x => rfl
  | apply c args ih =>
      simp only [psubst, psubstList_eq_map, guardFree]
      congr 1
      have each : ∀ ps : List Pattern, (∀ q ∈ ps, guardFree (psubst (fun x => some (.fvar (g x))) q) =
          guardFree q) → guardFreeList (ps.map (psubst fun x => some (.fvar (g x)))) = guardFreeList ps := by
        intro ps hps
        induction ps with
        | nil => rfl
        | cons p ps ihp =>
            simp only [List.map_cons, guardFreeList, hps p (List.mem_cons_self ..),
              ihp fun q m => hps q (List.mem_cons_of_mem _ m)]
      exact each args ih
  | lambda nm body ih => simpa [psubst, guardFree] using ih
  | multiLambda n nms body ih => simpa [psubst, guardFree] using ih
  | subst body repl ihb ihr => simp [psubst, guardFree, ihb, ihr]
  | collection ct elems rest ih =>
      simp only [psubst, psubstList_eq_map, guardFree]
      have each : ∀ ps : List Pattern, (∀ q ∈ ps, guardFree (psubst (fun x => some (.fvar (g x))) q) =
          guardFree q) → guardFreeList (ps.map (psubst fun x => some (.fvar (g x)))) = guardFreeList ps := by
        intro ps hps
        induction ps with
        | nil => rfl
        | cons p ps ihp =>
            simp only [List.map_cons, guardFreeList, hps p (List.mem_cons_self ..),
              ihp fun q m => hps q (List.mem_cons_of_mem _ m)]
      exact each elems ih
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact tail q later

theorem pvars_rename (g : String → String) (p : Pattern) : pvars (rename g p) = (pvars p).map g := by
  unfold rename
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps,
      pvars (psubst (fun x => some (.fvar (g x))) q) = (pvars q).map g) with
  | bvar n => rfl
  | fvar x => simp [psubst, pvars]
  | apply c args ih =>
      simp only [psubst, pvars, psubstList_eq_map, pvarsList_eq_flatMap, List.flatMap_map,
        List.map_flatMap]
      exact List.flatMap_congr ih
  | lambda nm body ih => simpa [psubst, pvars] using ih
  | multiLambda n nms body ih => simpa [psubst, pvars] using ih
  | subst body repl ihb ihr => simp [psubst, pvars, ihb, ihr]
  | collection ct elems rest ih =>
      simp only [psubst, pvars, psubstList_eq_map, pvarsList_eq_flatMap, List.flatMap_map,
        List.map_flatMap]
      exact List.flatMap_congr ih
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact tail q later

theorem idxOf_map_of_injOn {α β : Type} [DecidableEq α] [DecidableEq β] (g : α → β) :
    ∀ (l : List α), (∀ a ∈ l, ∀ b ∈ l, g a = g b → a = b) → ∀ {v : α}, v ∈ l →
      (l.map g).idxOf (g v) = l.idxOf v := by
  intro l
  induction l with
  | nil => intro _ v member; cases member
  | cons a l ih =>
      intro inj v member
      by_cases same : a = v
      · subst same; simp
      · have different : g a ≠ g v := fun eq =>
          same (inj a (List.mem_cons_self ..) v member eq)
        have later : v ∈ l := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        rw [List.map_cons, List.idxOf_cons, List.idxOf_cons]
        have b1 : (g a == g v) = false := by simpa using different
        have b2 : (a == v) = false := by simpa using same
        rw [b1, b2]
        simp only [cond_false]
        rw [ih (fun x hx y hy eq => inj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) eq)
          later]

/-! ## Lookups in composite environments -/

theorem lookupBound_lt {env : List (List String)} {x : String} {found : ℕ × ℕ}
    (eq : lookupBound env x = some found) : found.1 < env.length := by
  induction env generalizing found with
  | nil => cases eq
  | cons f env ih =>
      by_cases here : x ∈ f
      · simp [lookupBound, here] at eq; subst eq; simp
      · simp only [lookupBound, here, if_false, Option.map_eq_some_iff] at eq
        obtain ⟨inner, eq', rfl⟩ := eq
        have := ih eq'
        simp; omega

theorem lookupBound_append (front back : List (List String)) (x : String) :
    lookupBound (front ++ back) x =
      match lookupBound front x with
      | some found => some found
      | none => (lookupBound back x).map fun found => (found.1 + front.length, found.2) := by
  induction front with
  | nil => simp [lookupBound]
  | cons f front ih =>
      by_cases here : x ∈ f
      · simp [lookupBound, here]
      · simp only [List.cons_append, lookupBound, here, if_false, ih]
        cases lookupBound front x with
        | some found => simp
        | none =>
            cases lookupBound back x with
            | none => simp
            | some found => simp; omega

theorem lookupBound_replicate (n : ℕ) (back : List (List String)) (x : String) :
    lookupBound (List.replicate n [] ++ back) x =
      (lookupBound back x).map fun found => (found.1 + n, found.2) := by
  rw [lookupBound_append, lookupBound_of_empty (by simp)]
  simp

/-! ## Equations of instantiation -/

theorem instantiateList_eq_map (depth : ℕ) (value : ℕ → Option Pattern) (ps : List Pattern) :
    instantiateList depth value ps = ps.map (instantiateAt depth value) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [instantiateList, ih]

theorem instantiateAt_apply (depth : ℕ) (value : ℕ → Option Pattern) (c : String) (args : List Pattern) :
    instantiateAt depth value (.apply c args) =
      .apply c (if c = "MFor" then instantiateFor depth value args
        else args.map (instantiateAt depth value)) := by
  simp [instantiateAt, instantiateList_eq_map]

theorem instantiateFor_cons3 (depth : ℕ) (value : ℕ → Option Pattern) (t x k : Pattern)
    (rest : List Pattern) :
    instantiateFor depth value (t :: x :: k :: rest) =
      t :: instantiateAt depth value x :: instantiateAt (depth + 1) value k ::
        rest.map (instantiateAt depth value) := by
  simp [instantiateFor, instantiateList_eq_map]

theorem instantiateFor_short (depth : ℕ) (value : ℕ → Option Pattern) (ps : List Pattern)
    (short : ps.length < 3) : instantiateFor depth value ps = ps.map (instantiateAt depth value) := by
  match ps, short with
  | [], _ => rfl
  | [p], _ => simp [instantiateFor]
  | [p, q], _ => simp [instantiateFor]

theorem instantiateAt_code (depth : ℕ) (value : ℕ → Option Pattern) (d i : ℕ) :
    instantiateAt depth value (boundCode d i) =
      if d = depth then (value i).getD (boundCode d i) else boundCode d i := by
  simp [instantiateAt, boundCode]

/-! ## Opening a closed guard and closing it again -/

/-- The names given to a frame's variables: the variable at first position `i`
gets the `i`-th name. -/
def nameOf (names frameVars : List String) (v : String) : String :=
  names.getD (frameVars.idxOf v) v

theorem nameOf_injOn {names frameVars : List String} (nodup : names.Nodup)
    (long : frameVars.length ≤ names.length) :
    ∀ a ∈ frameVars, ∀ b ∈ frameVars, nameOf names frameVars a = nameOf names frameVars b → a = b := by
  intro a ha b hb eq
  have ia := List.idxOf_lt_length_of_mem ha
  have ib := List.idxOf_lt_length_of_mem hb
  simp only [nameOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : frameVars.idxOf a < names.length),
    List.getElem?_eq_getElem (by omega : frameVars.idxOf b < names.length), Option.getD_some] at eq
  have := (List.Nodup.getElem_inj_iff nodup).mp eq
  exact (List.idxOf_inj ha).mp this

theorem nameOf_mem {names frameVars : List String} (long : frameVars.length ≤ names.length)
    {v : String} (member : v ∈ frameVars) : nameOf names frameVars v ∈ names := by
  have := List.idxOf_lt_length_of_mem member
  simp only [nameOf, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega : frameVars.idxOf v < names.length), Option.getD_some]
  exact List.getElem_mem _

theorem names_getElem?_nameOf {names l : List String} (long : l.length ≤ names.length)
    {v : String} (member : v ∈ l) : names[l.idxOf v]? = some (nameOf names l v) := by
  have := List.idxOf_lt_length_of_mem member
  simp [nameOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : l.idxOf v < names.length)]

theorem lookupBound_single_mem {l : List String} {v : String} (member : v ∈ l) :
    lookupBound [l] v = some (0, l.idxOf v) := by
  simp [lookupBound, member]

theorem lookupBound_single_not_mem {l : List String} {v : String} (outside : v ∉ l) :
    lookupBound [l] v = none := by
  simp [lookupBound, outside]

/-- Opening a closed guard-free pattern renames its variables to the given names. -/
theorem open_closed_pattern (names l : List String) (long : l.length ≤ names.length) (t : Pattern)
    (inCalc : calcTerm t = true) (free : guardFree t = true) (inside : ∀ x ∈ pvars t, x ∈ l) :
    instantiateAt 0 (fun i => names[i]?.map Pattern.fvar) (closeIn [l] t) = rename (nameOf names l) t := by
  unfold rename
  induction t using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, calcTerm q = true →
      guardFree q = true → (∀ x ∈ pvars q, x ∈ l) →
      instantiateAt 0 (fun i => names[i]?.map Pattern.fvar) (closeIn [l] q) =
        psubst (fun x => some (.fvar (nameOf names l x))) q) with
  | bvar n => simp [calcTerm] at inCalc
  | fvar x =>
      have member := inside x (by simp [pvars])
      simp [closeIn, lookupBound_single_mem member, instantiateAt_code, psubst,
        names_getElem?_nameOf long member]
  | apply c args ih =>
      have notGuard : c ≠ "MFor" := by
        intro same; subst same; simp [guardFree] at free
      rw [closeIn_apply, if_neg notGuard, instantiateAt_apply, if_neg notGuard]
      simp only [psubst, psubstList_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q member
      simp only [calcTerm, calcList_iff] at inCalc
      simp only [guardFree, Bool.and_eq_true, bne_iff_ne, ne_eq, guardFreeList_iff] at free
      exact ih q member (inCalc q member) (free.2 q member) fun x occurs => inside x
        (by rw [pvars_apply, pvarsList_eq_flatMap]; exact List.mem_flatMap.mpr ⟨q, member, occurs⟩)
  | lambda nm body ih => simp [calcTerm] at inCalc
  | multiLambda n nms body ih => simp [calcTerm] at inCalc
  | subst body repl ihb ihr => simp [calcTerm] at inCalc
  | collection ct elems rest ih =>
      simp only [calcTerm, Bool.and_eq_true, Option.isNone_iff_eq_none, calcList_iff] at inCalc
      obtain ⟨rfl, inCalc⟩ := inCalc
      simp only [closeIn, closeList_eq_map, instantiateAt, instantiateList_eq_map, psubst,
        psubstList_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q member
      simp only [guardFree, guardFreeList_iff] at free
      exact ih q member (inCalc q member) (free q member) fun x occurs => inside x
        (by simp only [pvars, pvarsList_eq_flatMap]; exact List.mem_flatMap.mpr ⟨q, member, occurs⟩)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member calcQ freeQ insideQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head calcQ freeQ insideQ
      · exact tail q later calcQ freeQ insideQ

theorem mem_pvars_apply_of {c : String} {args : List Pattern} {q : Pattern} (member : q ∈ args)
    {x : String} (occurs : x ∈ pvars q) : x ∈ pvars (.apply c args) := by
  rw [pvars_apply, pvarsList_eq_flatMap]; exact List.mem_flatMap.mpr ⟨q, member, occurs⟩

theorem mem_pvars_collection_of {ct : CollType} {elems : List Pattern} {rest : Option String}
    {q : Pattern} (member : q ∈ elems) {x : String} (occurs : x ∈ pvars q) :
    x ∈ pvars (.collection ct elems rest) := by
  simp only [pvars, pvarsList_eq_flatMap]; exact List.mem_flatMap.mpr ⟨q, member, occurs⟩

/-- Closing an opened body in the opened names gives the closed body back. -/
theorem reclose_open (names l : List String) (nodup : names.Nodup) (long : l.length ≤ names.length)
    (A : Pattern) (inCalc : calcTerm A = true) :
    ∀ inner : List (List String), (∀ x ∈ pvars (closeIn (inner ++ [l]) A), x ∉ names) →
      closeIn (List.replicate inner.length [] ++ [l.map (nameOf names l)])
        (instantiateAt inner.length (fun i => names[i]?.map Pattern.fvar) (closeIn (inner ++ [l]) A)) =
      closeIn (inner ++ [l]) A := by
  induction A using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, calcTerm q = true →
      ∀ inner : List (List String), (∀ x ∈ pvars (closeIn (inner ++ [l]) q), x ∉ names) →
      closeIn (List.replicate inner.length [] ++ [l.map (nameOf names l)])
        (instantiateAt inner.length (fun i => names[i]?.map Pattern.fvar) (closeIn (inner ++ [l]) q)) =
      closeIn (inner ++ [l]) q) with
  | bvar n => simp [calcTerm] at inCalc
  | fvar x =>
      intro inner fresh
      cases eqInner : lookupBound inner x with
      | some found =>
          have small := lookupBound_lt eqInner
          have whole : lookupBound (inner ++ [l]) x = some found := by
            rw [lookupBound_append, eqInner]
          simp only [closeIn, whole, instantiateAt_code, if_neg (Nat.ne_of_lt small)]
          simp [closeIn, boundCode]
      | none =>
          by_cases member : x ∈ l
          · have whole : lookupBound (inner ++ [l]) x = some (inner.length, l.idxOf x) := by
              rw [lookupBound_append, eqInner, lookupBound_single_mem member]
              simp
            have injOn := nameOf_injOn nodup long
            have reclosed : lookupBound (List.replicate inner.length [] ++ [l.map (nameOf names l)])
                (nameOf names l x) = some (inner.length, l.idxOf x) := by
              rw [lookupBound_replicate, lookupBound_single_mem (List.mem_map_of_mem member),
                idxOf_map_of_injOn _ l injOn member]
              simp
            simp only [closeIn, whole, instantiateAt_code, names_getElem?_nameOf long member,
              Option.map_some, Option.getD_some, if_true]
            simp only [reclosed]
          · have whole : lookupBound (inner ++ [l]) x = none := by
              rw [lookupBound_append, eqInner, lookupBound_single_not_mem member]
              simp
            have notName : x ∉ names := fresh x (by simp [closeIn, whole, pvars])
            have notMapped : x ∉ l.map (nameOf names l) := by
              intro mapped
              obtain ⟨v, vin, eq⟩ := List.mem_map.mp mapped
              exact notName (eq ▸ nameOf_mem long vin)
            have reclosed : lookupBound (List.replicate inner.length [] ++ [l.map (nameOf names l)]) x =
                none := by
              rw [lookupBound_replicate, lookupBound_single_not_mem notMapped]
              simp
            simp [closeIn, whole, instantiateAt, reclosed]
  | apply c args ih =>
      intro inner fresh
      simp only [calcTerm, calcList_iff] at inCalc
      rw [closeIn_apply] at fresh
      rw [closeIn_apply, instantiateAt_apply, closeIn_apply]
      by_cases guard : c = "MFor"
      · simp only [guard, if_true] at fresh ⊢
        rcases closeFor_cases (inner ++ [l]) args with ⟨short, eq⟩ | ⟨t, x, k, rest, rfl, eq⟩
        · rw [eq] at fresh
          rw [eq, instantiateFor_short _ _ _ (by simpa using short)]
          rcases closeFor_cases (List.replicate inner.length [] ++ [l.map (nameOf names l)])
              ((args.map (closeIn (inner ++ [l]))).map
                (instantiateAt inner.length fun i => names[i]?.map Pattern.fvar)) with
            ⟨_, eq'⟩ | ⟨t', x', k', rest', same, _⟩
          · rw [eq', List.map_map, List.map_map]
            congr 1
            apply List.map_congr_left
            intro q member
            exact ih q member (inCalc q member) inner fun y occurs =>
              fresh y (mem_pvars_apply_of (List.mem_map_of_mem member) occurs)
          · have := congrArg List.length same
            simp at this
            omega
        · rw [eq] at fresh
          rw [eq, instantiateFor_cons3, closeFor_cons3]
          rw [frame_closed_pattern]
          congr 1
          refine List.cons_eq_cons.mpr ⟨closeIn_closeIn t [[]] [frame t] (by simp), ?_⟩
          refine List.cons_eq_cons.mpr ⟨ih x (by simp) (inCalc x (by simp)) inner fun y occurs =>
            fresh y (mem_pvars_apply_of (by simp) occurs), ?_⟩
          refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
          · have step := ih k (by simp) (inCalc k (by simp)) (frame t :: inner) fun y occurs =>
              fresh y (mem_pvars_apply_of (q := closeIn (frame t :: (inner ++ [l])) k) (by simp)
                (by simpa using occurs))
            simpa [List.replicate_succ] using step
          · rw [List.map_map, List.map_map]
            apply List.map_congr_left
            intro q member
            exact ih q (by simp [member]) (inCalc q (by simp [member])) inner fun y occurs =>
              fresh y (mem_pvars_apply_of (q := closeIn (inner ++ [l]) q)
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_map_of_mem member)))) occurs)
      · simp only [guard, if_false, List.map_map] at fresh ⊢
        congr 1
        apply List.map_congr_left
        intro q member
        exact ih q member (inCalc q member) inner fun y occurs =>
          fresh y (mem_pvars_apply_of (List.mem_map_of_mem member) occurs)
  | lambda nm body ih => simp [calcTerm] at inCalc
  | multiLambda n nms body ih => simp [calcTerm] at inCalc
  | subst body repl ihb ihr => simp [calcTerm] at inCalc
  | collection ct elems rest ih =>
      intro inner fresh
      simp only [calcTerm, Bool.and_eq_true, Option.isNone_iff_eq_none, calcList_iff] at inCalc
      obtain ⟨rfl, inCalc⟩ := inCalc
      simp only [closeIn, closeList_eq_map] at fresh
      simp only [closeIn, closeList_eq_map, instantiateAt, instantiateList_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q member
      exact ih q member (inCalc q member) inner fun y occurs =>
        fresh y (mem_pvars_collection_of (List.mem_map_of_mem member) occurs)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member calcQ inner freshQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head calcQ inner freshQ
      · exact tail q later calcQ inner freshQ

/-! ## Fresh names -/

theorem length_le_maxLength {names : List String} {name : String} (member : name ∈ names) :
    name.length ≤ maxLength names := by
  induction names with
  | nil => cases member
  | cons head names ih =>
      rcases List.mem_cons.mp member with rfl | later
      · simp [maxLength]
      · have := ih later; simp only [maxLength]; omega

theorem freshName_length (avoid : List String) (slot : ℕ) :
    (freshName avoid slot).length = maxLength avoid + slot + 1 := by
  simp [freshName, String.length_ofList]

theorem freshName_not_mem (avoid : List String) (slot : ℕ) : freshName avoid slot ∉ avoid := by
  intro member
  have := length_le_maxLength member
  rw [freshName_length] at this
  omega

theorem freshName_injective (avoid : List String) : Function.Injective (freshName avoid) := by
  intro a b same
  have := congrArg String.length same
  simp only [freshName_length] at this
  omega

theorem mem_freshNames {avoid : List String} {start count : ℕ} {name : String} :
    name ∈ freshNames avoid start count ↔ ∃ slot, start ≤ slot ∧ slot < start + count ∧
      name = freshName avoid slot := by
  simp only [freshNames, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, small, rfl⟩; exact ⟨start + i, by omega, by omega, rfl⟩
  · rintro ⟨slot, low, high, rfl⟩; exact ⟨slot - start, by omega, by congr 1; omega⟩

theorem freshNames_length (avoid : List String) (start count : ℕ) :
    (freshNames avoid start count).length = count := by simp [freshNames]

theorem freshNames_nodup (avoid : List String) (start count : ℕ) :
    (freshNames avoid start count).Nodup := by
  unfold freshNames
  refine List.Nodup.map (fun a b same => ?_) List.nodup_range
  have := freshName_injective avoid same
  omega

theorem freshNames_fresh {avoid : List String} {start count : ℕ} {name : String}
    (member : name ∈ freshNames avoid start count) : name ∉ avoid := by
  obtain ⟨slot, _, _, rfl⟩ := mem_freshNames.mp member
  exact freshName_not_mem avoid slot

theorem freshNames_disjoint {avoid : List String} {first second : ℕ} {name : String}
    (left : name ∈ freshNames avoid 0 first) (right : name ∈ freshNames avoid first second) : False := by
  obtain ⟨a, _, ha, rfl⟩ := mem_freshNames.mp left
  obtain ⟨b, hb, _, same⟩ := mem_freshNames.mp right
  have := freshName_injective avoid same
  omega

/-! ## Binders -/

mutual
/-- The variables bound by inner guards. Patterns are data: a guard inside a
pattern binds nothing of its own. -/
def binders : Pattern → List String
  | .bvar _ => []
  | .fvar _ => []
  | .apply c args => if c = "MFor" then bindersFor args else bindersList args
  | .lambda _ body => binders body
  | .multiLambda _ _ body => binders body
  | .subst body repl => binders body ++ binders repl
  | .collection _ elems _ => bindersList elems
def bindersList : List Pattern → List String
  | [] => []
  | p :: ps => binders p ++ bindersList ps
def bindersFor : List Pattern → List String
  | [] => []
  | [p] => binders p
  | [p, q] => binders p ++ binders q
  | t :: x :: k :: rest => pvars t ++ binders x ++ binders k ++ bindersList rest
end

theorem bindersList_eq_flatMap (ps : List Pattern) : bindersList ps = ps.flatMap binders := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [bindersList, ih]

theorem binders_apply (c : String) (args : List Pattern) :
    binders (.apply c args) = if c = "MFor" then bindersFor args else args.flatMap binders := by
  simp [binders, bindersList_eq_flatMap]

theorem bindersFor_cons3 (t x k : Pattern) (rest : List Pattern) :
    bindersFor (t :: x :: k :: rest) = pvars t ++ binders x ++ binders k ++ rest.flatMap binders := by
  simp [bindersFor, bindersList_eq_flatMap]

theorem bindersFor_short (ps : List Pattern) (short : ps.length < 3) :
    bindersFor ps = ps.flatMap binders := by
  match ps, short with
  | [], _ => rfl
  | [p], _ => simp [bindersFor]
  | [p, q], _ => simp [bindersFor]

/-- A closed process binds no names. -/
theorem binders_closeIn (p : Pattern) : ∀ env : List (List String), binders (closeIn env p) = [] := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps,
      ∀ env : List (List String), binders (closeIn env q) = []) with
  | bvar n => intro env; simp [closeIn, binders]
  | fvar x =>
      intro env
      cases eq : lookupBound env x <;> simp [closeIn, eq, binders, boundCode]
  | apply c args ih =>
      intro env
      rw [closeIn_apply, binders_apply]
      by_cases guard : c = "MFor"
      · simp only [guard, if_true]
        rcases closeFor_cases env args with ⟨short, eq⟩ | ⟨t, x, k, rest, rfl, eq⟩
        · rw [eq, bindersFor_short _ (by simpa using short), List.flatMap_eq_nil_iff]
          intro r member
          obtain ⟨q, inside, rfl⟩ := List.mem_map.mp member
          exact ih q inside env
        · rw [eq, bindersFor_cons3, pvars_closed_pattern]
          simp only [List.nil_append, List.append_eq_nil_iff, List.flatMap_eq_nil_iff]
          refine ⟨⟨ih x (by simp) env, ih k (by simp) (frame t :: env)⟩, ?_⟩
          intro r member
          obtain ⟨q, inside, rfl⟩ := List.mem_map.mp member
          exact ih q (by simp [inside]) env
      · simp only [guard, if_false, List.flatMap_eq_nil_iff]
        intro r member
        obtain ⟨q, inside, rfl⟩ := List.mem_map.mp member
        exact ih q inside env
  | lambda nm body ih => intro env; simp [closeIn, binders, ih env]
  | multiLambda n nms body ih => intro env; simp [closeIn, binders, ih env]
  | subst body repl ihb ihr => intro env; simp [closeIn, binders, ihb env, ihr env]
  | collection ct elems rest ih =>
      intro env
      simp only [closeIn, binders, closeList_eq_map, bindersList_eq_flatMap, List.flatMap_eq_nil_iff]
      intro r member
      obtain ⟨q, inside, rfl⟩ := List.mem_map.mp member
      exact ih q inside env
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member env
      rcases List.mem_cons.mp member with rfl | later
      · exact head env
      · exact tail q later env

/-- Opening with names adds no binder. -/
theorem binders_instantiateAt (value : ℕ → Option Pattern)
    (noBinders : ∀ i v, value i = some v → binders v = []) (p : Pattern) :
    ∀ depth, binders (instantiateAt depth value p) = binders p := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps,
      ∀ depth, binders (instantiateAt depth value q) = binders q) with
  | bvar n =>
      intro depth
      simp only [instantiateAt]
      split
      · cases eq : value (Nat.unpair n).2 with
        | none => simp [binders]
        | some v => simp [noBinders _ v eq, binders]
      · rfl
  | fvar x => intro depth; rfl
  | apply c args ih =>
      intro depth
      rw [instantiateAt_apply, binders_apply, binders_apply]
      by_cases guard : c = "MFor"
      · simp only [guard, if_true]
        by_cases short : args.length < 3
        · rw [instantiateFor_short _ _ _ short, bindersFor_short _ (by simpa using short),
            bindersFor_short _ short, List.flatMap_map]
          exact List.flatMap_congr fun q member => ih q member depth
        · match args, short with
          | [_], h => simp at h
          | [_, _], h => simp at h
          | t :: x :: k :: rest, _ =>
              rw [instantiateFor_cons3, bindersFor_cons3, bindersFor_cons3, ih x (by simp) depth,
                ih k (by simp) (depth + 1), List.flatMap_map]
              congr 1
              exact List.flatMap_congr fun q member => ih q (by simp [member]) depth
      · simp only [guard, if_false, List.flatMap_map]
        exact List.flatMap_congr fun q member => ih q member depth
  | lambda nm body ih => intro depth; simp [instantiateAt, binders, ih depth]
  | multiLambda n nms body ih => intro depth; simp [instantiateAt, binders, ih depth]
  | subst body repl ihb ihr => intro depth; simp [instantiateAt, binders, ihb depth, ihr depth]
  | collection ct elems rest ih =>
      intro depth
      simp only [instantiateAt, binders, instantiateList_eq_map, bindersList_eq_flatMap,
        List.flatMap_map]
      exact List.flatMap_congr fun q member => ih q member depth
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member depth
      rcases List.mem_cons.mp member with rfl | later
      · exact head depth
      · exact tail q later depth

/-- The variables of an opened process: its own, and the names it was opened with. -/
theorem pvars_instantiateAt (value : ℕ → Option Pattern) (p : Pattern) :
    ∀ depth, ∀ x ∈ pvars (instantiateAt depth value p),
      x ∈ pvars p ∨ ∃ i v, value i = some v ∧ x ∈ pvars v := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps,
      ∀ depth, ∀ x ∈ pvars (instantiateAt depth value q),
        x ∈ pvars q ∨ ∃ i v, value i = some v ∧ x ∈ pvars v) with
  | bvar n =>
      intro depth x occurs
      simp only [instantiateAt] at occurs
      split at occurs
      · cases eq : value (Nat.unpair n).2 with
        | none => rw [eq] at occurs; simp [pvars] at occurs
        | some v => rw [eq] at occurs; exact .inr ⟨_, v, eq, occurs⟩
      · simp [pvars] at occurs
  | fvar y => intro depth x occurs; exact .inl occurs
  | apply c args ih =>
      intro depth x occurs
      rw [instantiateAt_apply, pvars_apply, pvarsList_eq_flatMap] at occurs
      obtain ⟨r, member, inR⟩ := List.mem_flatMap.mp occurs
      by_cases guard : c = "MFor"
      · rw [if_pos guard] at member
        by_cases short : args.length < 3
        · rw [instantiateFor_short _ _ _ short] at member
          obtain ⟨q, inside, rfl⟩ := List.mem_map.mp member
          rcases ih q inside depth x inR with own | named
          · exact .inl (mem_pvars_apply_of inside own)
          · exact .inr named
        · match args, short with
          | [_], h => simp at h
          | [_, _], h => simp at h
          | t :: y :: k :: rest, _ =>
              rw [instantiateFor_cons3] at member
              simp only [List.mem_cons, List.mem_map] at member
              rcases member with rfl | rfl | rfl | ⟨q, inside, rfl⟩
              · exact .inl (mem_pvars_apply_of (by simp) inR)
              · rcases ih y (by simp) depth x inR with own | named
                · exact .inl (mem_pvars_apply_of (by simp) own)
                · exact .inr named
              · rcases ih k (by simp) (depth + 1) x inR with own | named
                · exact .inl (mem_pvars_apply_of (by simp) own)
                · exact .inr named
              · rcases ih q (by simp [inside]) depth x inR with own | named
                · exact .inl (mem_pvars_apply_of (by simp [inside]) own)
                · exact .inr named
      · rw [if_neg guard] at member
        obtain ⟨q, inside, rfl⟩ := List.mem_map.mp member
        rcases ih q inside depth x inR with own | named
        · exact .inl (mem_pvars_apply_of inside own)
        · exact .inr named
  | lambda nm body ih =>
      intro depth x occurs
      simpa [pvars] using ih depth x (by simpa [instantiateAt, pvars] using occurs)
  | multiLambda n nms body ih =>
      intro depth x occurs
      simpa [pvars] using ih depth x (by simpa [instantiateAt, pvars] using occurs)
  | subst body repl ihb ihr =>
      intro depth x occurs
      simp only [instantiateAt, pvars, List.mem_append] at occurs
      rcases occurs with inB | inR
      · rcases ihb depth x inB with own | named
        · exact .inl (by simp [pvars, own])
        · exact .inr named
      · rcases ihr depth x inR with own | named
        · exact .inl (by simp [pvars, own])
        · exact .inr named
  | collection ct elems rest ih =>
      intro depth x occurs
      simp only [instantiateAt, pvars, instantiateList_eq_map, pvarsList_eq_flatMap] at occurs
      obtain ⟨r, member, inR⟩ := List.mem_flatMap.mp occurs
      obtain ⟨q, inside, rfl⟩ := List.mem_map.mp member
      rcases ih q inside depth x inR with own | named
      · exact .inl (mem_pvars_collection_of inside own)
      · exact .inr named
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member depth x occurs
      rcases List.mem_cons.mp member with rfl | later
      · exact head depth x occurs
      · exact tail q later depth x occurs

theorem pvars_openWith {names : List String} {p : Pattern} {x : String}
    (occurs : x ∈ pvars (openWith names p)) : x ∈ pvars p ∨ x ∈ names := by
  rcases pvars_instantiateAt _ p 0 x occurs with own | ⟨i, v, eq, inV⟩
  · exact .inl own
  · cases found : names[i]? with
    | none => simp [found] at eq
    | some name =>
        simp only [found, Option.map_some, Option.some.injEq] at eq
        subst eq
        simp only [pvars, List.mem_singleton] at inV
        subst inV
        exact .inr (List.mem_of_getElem? found)

theorem binders_openWith (names : List String) (p : Pattern) : binders (openWith names p) = binders p :=
  binders_instantiateAt _ (fun i v eq => by
    cases found : names[i]? with
    | none => simp [found] at eq
    | some name => simp only [found, Option.map_some, Option.some.injEq] at eq; subst eq; rfl) p 0

/-! ## Facts about closed guards -/

theorem codeCountList_eq_sum (ps : List Pattern) : codeCountList ps = (ps.map codeCount).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [codeCountList, ih]

/-- A closed guard-free pattern has one code per variable occurrence. -/
theorem codeCount_closeIn (env : List (List String)) (t : Pattern) (inCalc : calcTerm t = true)
    (free : guardFree t = true) (bound : ∀ x ∈ pvars t, ∃ found, lookupBound env x = some found) :
    codeCount (closeIn env t) = (pvars t).length := by
  induction t using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, calcTerm q = true →
      guardFree q = true → (∀ x ∈ pvars q, ∃ found, lookupBound env x = some found) →
      codeCount (closeIn env q) = (pvars q).length) with
  | bvar n => simp [calcTerm] at inCalc
  | fvar x =>
      obtain ⟨found, eq⟩ := bound x (by simp [pvars])
      simp [closeIn, eq, boundCode, codeCount, pvars]
  | apply c args ih =>
      have notGuard : c ≠ "MFor" := by intro same; subst same; simp [guardFree] at free
      rw [closeIn_apply, if_neg notGuard]
      simp only [codeCount, codeCountList_eq_sum, pvars, pvarsList_eq_flatMap, List.length_flatMap,
        List.map_map]
      congr 1
      apply List.map_congr_left
      intro q member
      simp only [calcTerm, calcList_iff] at inCalc
      simp only [guardFree, Bool.and_eq_true, bne_iff_ne, ne_eq, guardFreeList_iff] at free
      exact ih q member (inCalc q member) (free.2 q member) fun x occurs =>
        bound x (mem_pvars_apply_of member occurs)
  | lambda nm body ih => simp [calcTerm] at inCalc
  | multiLambda n nms body ih => simp [calcTerm] at inCalc
  | subst body repl ihb ihr => simp [calcTerm] at inCalc
  | collection ct elems rest ih =>
      simp only [closeIn, codeCount, closeList_eq_map, codeCountList_eq_sum, pvars,
        pvarsList_eq_flatMap, List.length_flatMap, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q member
      simp only [calcTerm, Bool.and_eq_true, calcList_iff] at inCalc
      simp only [guardFree, guardFreeList_iff] at free
      exact ih q member (inCalc.2 q member) (free q member) fun x occurs =>
        bound x (mem_pvars_collection_of member occurs)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member calcQ freeQ boundQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head calcQ freeQ boundQ
      · exact tail q later calcQ freeQ boundQ

theorem guardFree_closeIn (t : Pattern) : ∀ env : List (List String),
    guardFree (closeIn env t) = guardFree t := by
  induction t using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps,
      ∀ env : List (List String), guardFree (closeIn env q) = guardFree q) with
  | bvar n => intro env; rfl
  | fvar x => intro env; cases eq : lookupBound env x <;> simp [closeIn, eq, guardFree, boundCode]
  | apply c args ih =>
      intro env
      rw [closeIn_apply]
      by_cases guard : c = "MFor"
      · subst guard; simp [guardFree]
      · simp only [guard, if_false, guardFree]
        have each : ∀ ps : List Pattern, (∀ q ∈ ps, guardFree (closeIn env q) = guardFree q) →
            guardFreeList (ps.map (closeIn env)) = guardFreeList ps := by
          intro ps hps
          induction ps with
          | nil => rfl
          | cons p ps ihp =>
              simp only [List.map_cons, guardFreeList, hps p (List.mem_cons_self ..),
                ihp fun q m => hps q (List.mem_cons_of_mem _ m)]
        rw [each args fun q member => ih q member env]
  | lambda nm body ih => intro env; simp [closeIn, guardFree, ih env]
  | multiLambda n nms body ih => intro env; simp [closeIn, guardFree, ih env]
  | subst body repl ihb ihr => intro env; simp [closeIn, guardFree, ihb env, ihr env]
  | collection ct elems rest ih =>
      intro env
      simp only [closeIn, guardFree, closeList_eq_map]
      have each : ∀ ps : List Pattern, (∀ q ∈ ps, guardFree (closeIn env q) = guardFree q) →
          guardFreeList (ps.map (closeIn env)) = guardFreeList ps := by
        intro ps hps
        induction ps with
        | nil => rfl
        | cons p ps ihp =>
            simp only [List.map_cons, guardFreeList, hps p (List.mem_cons_self ..),
              ihp fun q m => hps q (List.mem_cons_of_mem _ m)]
      exact each elems fun q member => ih q member env
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member env
      rcases List.mem_cons.mp member with rfl | later
      · exact head env
      · exact tail q later env

theorem asGuard_pFor (t x k : Pattern) : asGuard (pFor t x k) = some (t, x, k) := rfl

theorem asGuard_eq_some {p : Pattern} {r : Pattern × Pattern × Pattern} :
    asGuard p = some r → p = pFor r.1 r.2.1 r.2.2 := by
  intro found
  unfold asGuard at found
  split at found
  · cases found; rfl
  · cases found

/-- Only a guard closes to a guard. -/
theorem asGuard_closeIn {env : List (List String)} {p : Pattern} {r : Pattern × Pattern × Pattern}
    (found : asGuard (closeIn env p) = some r) :
    ∃ t x k, p = pFor t x k ∧ r = (closeIn [frame t] t, closeIn env x, closeIn (frame t :: env) k) := by
  have shape := asGuard_eq_some found
  cases p with
  | fvar y => cases eq : lookupBound env y <;> simp [closeIn, eq, boundCode, pFor] at shape
  | bvar n => simp [closeIn, pFor] at shape
  | apply c args =>
      rw [closeIn_apply] at shape
      simp only [pFor, Pattern.apply.injEq] at shape
      obtain ⟨rfl, list⟩ := shape
      simp only [if_true] at list
      rcases closeFor_cases env args with ⟨short, eq⟩ | ⟨t, x, k, rest, rfl, eq⟩
      · rw [eq] at list
        have := congrArg List.length list
        simp at this
        omega
      · rw [eq] at list
        simp only [List.cons.injEq, List.map_eq_nil_iff] at list
        obtain ⟨h1, h2, h3, rfl⟩ := list
        refine ⟨t, x, k, rfl, ?_⟩
        obtain ⟨a, b, c⟩ := r
        simp only at h1 h2 h3
        subst h1 h2 h3
        rfl
  | lambda nm body => simp [closeIn, pFor] at shape
  | multiLambda n nms body => simp [closeIn, pFor] at shape
  | subst body repl => simp [closeIn, pFor] at shape
  | collection ct elems rest => simp [closeIn, pFor] at shape

/-! ## The relational semantics -/

/-- `bs` is a principal unifier of `t` and `u`: one pass makes them equal, and
every unifier absorbs it. -/
structure Principal (t u : Pattern) (bs : Bindings) : Prop where
  solves : psubst bs.lookup t = psubst bs.lookup u
  general : ∀ τ : PSubst, psubst τ t = psubst τ u → ∀ p, psubst τ (psubst bs.lookup p) = psubst τ p
  keys : ∀ entry ∈ bs, entry.1 ∈ pvars t ++ pvars u

theorem unify_principal {t u : Pattern} {bs : Bindings} (found : unify t u = some bs) :
    Principal t u bs :=
  ⟨unify_sound found, unify_most_general found, unify_keys found⟩

/-- The variable convention for one COMM redex: the two patterns share no
variable, neither input mentions the other's pattern variables, and no inner
guard of a continuation rebinds its own input's pattern variables. -/
structure Apart (t A u B : Pattern) : Prop where
  patterns : ∀ v ∈ pvars t, v ∉ pvars u
  leftOutside : ∀ v ∈ pvars t, v ∉ pvars B
  rightOutside : ∀ v ∈ pvars u, v ∉ pvars A
  leftKept : ∀ v ∈ pvars t, v ∉ binders A
  rightKept : ∀ v ∈ pvars u, v ∉ binders B

/-- Which COMM instances a relation admits: pattern, continuation, pattern,
continuation, unifier. -/
abbrev Admission := Pattern → Pattern → Pattern → Pattern → Bindings → Prop

/-- The manuscript's COMM, PAR, EQUIV and REFL, with alpha-equivalence as the
equivalence, the principal unifier, and the admission on COMM. -/
inductive Step (admit : Admission) : Pattern → Pattern → Prop where
  | comm (t u x A B : Pattern) (bs : Bindings) (principal : Principal t u bs)
      (admitted : admit t A u B bs) :
      Step admit (par (pFor t x A) (pFor u x B)) (par (applyDot bs A) (applyDot bs B))
  | parallel {source target : Pattern} (surrounding : Pattern) :
      Step admit source target → Step admit (par source surrounding) (par target surrounding)
  | congruence {source source' target' target : Pattern} :
      AlphaEq source source' → Step admit source' target' → AlphaEq target' target →
      Step admit source target
  | reflect (x : Pattern) {source target : Pattern} :
      Step admit source target → Step admit (pReflect x source) (pFor (tProc target) x pZero)

/-- COMM under the variable convention. -/
def conventional : Admission := fun t A u B _ => Apart t A u B

/-- COMM under the variable convention, with guard-free calculus patterns and
calculus continuations, whose read pattern variables the unifier grounds. -/
def closing : Admission := fun t A u B bs =>
  Apart t A u B ∧ guardFree t = true ∧ guardFree u = true ∧ calcTerm t = true ∧ calcTerm u = true ∧
    calcTerm A = true ∧ calcTerm B = true ∧
    ∀ v ∈ pvars t ++ pvars u, v ∈ pvars A ++ pvars B → ∃ g, bs.lookup v = some g ∧ pvars g = []

theorem Step.mono {admit admit' : Admission} (weaker : ∀ t A u B bs, admit t A u B bs → admit' t A u B bs)
    {p q : Pattern} (step : Step admit p q) : Step admit' p q := by
  induction step with
  | comm t u x A B bs principal admitted => exact .comm t u x A B bs principal (weaker _ _ _ _ _ admitted)
  | parallel surrounding _ ih => exact .parallel surrounding ih
  | congruence before _ after ih => exact .congruence before ih after
  | reflect x _ ih => exact .reflect x ih

theorem closing_conventional (t A u B : Pattern) (bs : Bindings) (h : closing t A u B bs) :
    conventional t A u B bs := h.1

/-- The binding list names every pattern variable, so that the dot quotes each
one: a bound variable reads the quotation of its value, an unbound one the
quotation of itself. -/
def Complete (t u : Pattern) (bs : Bindings) : Prop :=
  ∀ v ∈ pvars t ++ pvars u, (bs.lookup v).isSome

/-- **The uniform dot.** COMM under the variable convention with a principal
binding list that names every pattern variable. Its reduct does not depend on
how a most general unifier is oriented, up to renaming residual names. -/
def uniform : Admission := fun t A u B bs => Apart t A u B ∧ Complete t u bs

/-- The uniform dot on guard-free calculus patterns and calculus continuations. -/
def uniformCalc : Admission := fun t A u B bs =>
  uniform t A u B bs ∧ guardFree t = true ∧ guardFree u = true ∧ calcTerm t = true ∧
    calcTerm u = true ∧ calcTerm A = true ∧ calcTerm B = true

theorem uniform_conventional (t A u B : Pattern) (bs : Bindings) (h : uniform t A u B bs) :
    conventional t A u B bs := h.1

theorem uniformCalc_uniform (t A u B : Pattern) (bs : Bindings) (h : uniformCalc t A u B bs) :
    uniform t A u B bs := h.1

/-! ## Completed binding lists -/

theorem lookup_append (front back : Bindings) (x : String) :
    Bindings.lookup (front ++ back) x =
      match front.lookup x with
      | some value => some value
      | none => back.lookup x := by
  unfold Bindings.lookup
  rw [List.find?_append]
  cases front.find? (fun entry => entry.1 == x) <;> rfl

theorem lookup_identityEntries (ws : List String) (x : String) :
    Bindings.lookup (ws.map fun v => (v, Pattern.fvar v)) x = if x ∈ ws then some (.fvar x) else none := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      by_cases same : w = x
      · subst same; simp [Bindings.lookup]
      · have : (w == x) = false := by simpa using same
        simp only [List.map_cons, List.mem_cons]
        unfold Bindings.lookup at ih ⊢
        simp only [List.find?_cons, this, ih, Ne.symm same, false_or]

theorem lookup_completeBindings (vs : List String) (bs : Bindings) (x : String) :
    (completeBindings vs bs).lookup x =
      match bs.lookup x with
      | some value => some value
      | none => if x ∈ vs then some (.fvar x) else none := by
  unfold completeBindings
  rw [lookup_append]
  cases found : bs.lookup x with
  | some value => rfl
  | none =>
      simp only
      rw [lookup_identityEntries]
      simp [List.mem_filter, found]

/-- Completing a list changes no instance: each new entry binds a variable to itself. -/
theorem getD_lookup_completeBindings (vs : List String) (bs : Bindings) (x : String) :
    ((completeBindings vs bs).lookup x).getD (.fvar x) = (bs.lookup x).getD (.fvar x) := by
  rw [lookup_completeBindings]
  cases h : bs.lookup x with
  | some value => rfl
  | none => by_cases member : x ∈ vs <;> simp [member]

theorem psubst_completeBindings (vs : List String) (bs : Bindings) (p : Pattern) :
    psubst (completeBindings vs bs).lookup p = psubst bs.lookup p :=
  psubst_getD_congr (getD_lookup_completeBindings vs bs) p

/-- A completed principal list is principal. -/
theorem principal_completeBindings {t u : Pattern} {bs : Bindings} (principal : Principal t u bs) :
    Principal t u (completeBindings (pvars t ++ pvars u) bs) := by
  refine ⟨by rw [psubst_completeBindings, psubst_completeBindings]; exact principal.solves, ?_, ?_⟩
  · intro τ solves p
    rw [psubst_completeBindings]
    exact principal.general τ solves p
  · intro entry member
    unfold completeBindings at member
    rcases List.mem_append.mp member with old | new
    · exact principal.keys entry old
    · obtain ⟨v, inside, rfl⟩ := List.mem_map.mp new
      exact (List.mem_filter.mp inside).1

theorem complete_completeBindings (t u : Pattern) (bs : Bindings) :
    Complete t u (completeBindings (pvars t ++ pvars u) bs) := by
  intro v member
  rw [lookup_completeBindings]
  cases bs.lookup v with
  | some value => rfl
  | none => simp [member]

/-! ## Soundness of the corrected step -/

theorem pvars_par (p q : Pattern) : pvars (par p q) = pvars p ++ pvars q := by
  simp [par, pPar, pvars, pvars.pvarsList]

theorem pvars_pFor (t x k : Pattern) : pvars (pFor t x k) = pvars t ++ pvars x ++ pvars k := by
  simp [pFor, pvars, pvars.pvarsList]

theorem pvars_pReflect (x p : Pattern) : pvars (pReflect x p) = pvars x ++ pvars p := by
  simp [pReflect, pvars, pvars.pvarsList]

/-- The names an input is opened with, read as a renaming of its pattern. -/
theorem opened_pattern (avoid : List String) (start : ℕ) (t : Pattern) (inCalc : calcTerm t = true)
    (free : guardFree t = true) :
    openPattern (freshNames avoid start (codeCount (closeIn [frame t] t))) (closeIn [frame t] t) =
      rename (nameOf (freshNames avoid start (codeCount (closeIn [frame t] t))) (frame t)) t ∧
    (frame t).length ≤ (freshNames avoid start (codeCount (closeIn [frame t] t))).length := by
  have long : (frame t).length ≤ (freshNames avoid start (codeCount (closeIn [frame t] t))).length := by
    rw [freshNames_length, codeCount_closeIn [frame t] t inCalc free fun x occurs =>
      lookupBound_isSome_of_mem (List.mem_singleton_self _) (by rw [frame_of_guardFree t free]; exact occurs),
      frame_of_guardFree t free]
  exact ⟨open_closed_pattern _ (frame t) long t inCalc free fun x occurs => by
    rw [frame_of_guardFree t free]; exact occurs, long⟩

/-- The executable COMM is the manuscript's COMM on the two inputs opened apart,
whenever the names to avoid contain the free names of the two continuations.
The channel is outside both scopes and needs no fresh names. -/
theorem commClosed_sound_bodies (avoid : List String) (t x A u y B : Pattern)
    (calcT : calcTerm t = true) (calcU : calcTerm u = true) (calcA : calcTerm A = true)
    (calcB : calcTerm B = true)
    (fresh : ∀ z, z ∈ pvars (closeIn [frame t] A) ∨ z ∈ pvars (closeIn [frame u] B) → z ∈ avoid)
    {Q : Pattern} (produced : Q ∈ commClosed avoid (close (pFor t x A)) (close (pFor u y B))) :
    Step uniform (par (pFor t x A) (pFor u y B)) Q := by
  have closeT : close (pFor t x A) = pFor (closeIn [frame t] t) (close x) (closeIn [frame t] A) :=
    closeIn_pFor [] t x A
  have closeU : close (pFor u y B) = pFor (closeIn [frame u] u) (close y) (closeIn [frame u] B) :=
    closeIn_pFor [] u y B
  have closeWhole : close (par (pFor t x A) (pFor u y B)) =
      par (pFor (closeIn [frame t] t) (close x) (closeIn [frame t] A))
        (pFor (closeIn [frame u] u) (close y) (closeIn [frame u] B)) := by
    unfold close; rw [closeIn_par]; exact congrArg₂ par closeT closeU
  rw [closeT, closeU] at produced
  simp only [commClosed, asGuard_pFor] at produced
  split at produced
  · rename_i condition
    obtain ⟨sameChannel, freeT, freeU⟩ := condition
    rw [guardFree_closeIn] at freeT freeU
    split at produced
    rotate_left
    · cases produced
    rename_i _ bs found
    · simp only [List.mem_singleton] at produced
      subst produced
      -- names
      let L := freshNames avoid 0 (codeCount (closeIn [frame t] t))
      let R := freshNames avoid (codeCount (closeIn [frame t] t)) (codeCount (closeIn [frame u] u))
      obtain ⟨openT, longT⟩ := opened_pattern avoid 0 t calcT freeT
      obtain ⟨openU, longU⟩ := opened_pattern avoid (codeCount (closeIn [frame t] t)) u calcU freeU
      have freshAvoid : ∀ z, z ∈ pvars (closeIn [frame t] A) ∨ z ∈ pvars (closeIn [frame u] B) →
          z ∉ L ∧ z ∉ R :=
        fun z occurs => ⟨fun inL => freshNames_fresh inL (fresh z occurs),
          fun inR => freshNames_fresh inR (fresh z occurs)⟩
      have tVars : ∀ v ∈ pvars (openPattern L (closeIn [frame t] t)), v ∈ L := by
        intro v occurs
        rw [openT, pvars_rename] at occurs
        obtain ⟨w, inside, rfl⟩ := List.mem_map.mp occurs
        exact nameOf_mem longT (by rw [frame_of_guardFree t freeT]; exact inside)
      have uVars : ∀ v ∈ pvars (openPattern R (closeIn [frame u] u)), v ∈ R := by
        intro v occurs
        rw [openU, pvars_rename] at occurs
        obtain ⟨w, inside, rfl⟩ := List.mem_map.mp occurs
        exact nameOf_mem longU (by rw [frame_of_guardFree u freeU]; exact inside)
      have disjointLR : ∀ v, v ∈ L → v ∉ R := fun v inL inR => freshNames_disjoint inL inR
      refine Step.congruence (source' := par
          (pFor (openPattern L (closeIn [frame t] t)) (close x) (openWith L (closeIn [frame t] A)))
          (pFor (openPattern R (closeIn [frame u] u)) (close x) (openWith R (closeIn [frame u] B))))
        ?_ (Step.comm _ _ _ _ _ _ (principal_completeBindings (unify_principal found))
          ⟨?_, complete_completeBindings _ _ _⟩) (AlphaEq.refl _)
      · -- the opened redex has the source's closed form
        unfold AlphaEq
        rw [closeWhole]
        unfold close
        rw [closeIn_par, closeIn_pFor, closeIn_pFor]
        have frameT : frame (openPattern L (closeIn [frame t] t)) =
            (frame t).map (nameOf L (frame t)) := by
          have renamed : guardFree (rename (nameOf L (frame t)) t) = true := by
            rw [guardFree_rename]; exact freeT
          calc frame (openPattern L (closeIn [frame t] t))
              = frame (rename (nameOf L (frame t)) t) := congrArg frame openT
            _ = (pvars t).map (nameOf L (frame t)) := by
                rw [frame_of_guardFree _ renamed]; exact pvars_rename _ t
            _ = (frame t).map (nameOf L (frame t)) := by rw [← frame_of_guardFree t freeT]
        have frameU : frame (openPattern R (closeIn [frame u] u)) =
            (frame u).map (nameOf R (frame u)) := by
          have renamed : guardFree (rename (nameOf R (frame u)) u) = true := by
            rw [guardFree_rename]; exact freeU
          calc frame (openPattern R (closeIn [frame u] u))
              = frame (rename (nameOf R (frame u)) u) := congrArg frame openU
            _ = (pvars u).map (nameOf R (frame u)) := by
                rw [frame_of_guardFree _ renamed]; exact pvars_rename _ u
            _ = (frame u).map (nameOf R (frame u)) := by rw [← frame_of_guardFree u freeU]
        have sameChannel' : closeIn [] x = closeIn [] y := sameChannel
        rw [frameT, frameU, closeIn_closeIn x [] [] (by simp), ← sameChannel']
        have reT := reclose_open L (frame t) (freshNames_nodup _ _ _) longT t calcT []
          (by rw [List.nil_append, pvars_closed_pattern]; simp)
        have reA := reclose_open L (frame t) (freshNames_nodup _ _ _) longT A calcA []
          (fun z occurs => (freshAvoid z (.inl (by simpa using occurs))).1)
        have reU := reclose_open R (frame u) (freshNames_nodup _ _ _) longU u calcU []
          (by rw [List.nil_append, pvars_closed_pattern]; simp)
        have reB := reclose_open R (frame u) (freshNames_nodup _ _ _) longU B calcB []
          (fun z occurs => (freshAvoid z (.inr (by simpa using occurs))).2)
        simp only [List.length_nil, List.replicate_zero, List.nil_append] at reT reA reU reB
        unfold openPattern openWith
        rw [reT, reA, reU, reB]
      · -- the opened redex satisfies the variable convention
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro v inT inU
          exact disjointLR v (tVars v inT) (uVars v inU)
        · intro v inT inB
          rcases pvars_openWith inB with own | named
          · exact (freshAvoid v (.inr own)).1 (tVars v inT)
          · exact disjointLR v (tVars v inT) named
        · intro v inU inA
          rcases pvars_openWith inA with own | named
          · exact (freshAvoid v (.inl own)).2 (uVars v inU)
          · exact disjointLR v named (uVars v inU)
        · intro v _ bound
          rw [binders_openWith, binders_closeIn] at bound
          cases bound
        · intro v _ bound
          rw [binders_openWith, binders_closeIn] at bound
          cases bound
  · cases produced

/-- The free names of a closed continuation are free names of the redex. -/
theorem mem_pvars_close_redex {t x A u y B : Pattern} {z : String}
    (occurs : z ∈ pvars (closeIn [frame t] A) ∨ z ∈ pvars (closeIn [frame u] B)) :
    z ∈ pvars (close (par (pFor t x A) (pFor u y B))) := by
  unfold close
  rw [closeIn_par, closeIn_pFor, closeIn_pFor, pvars_par, pvars_pFor, pvars_pFor]
  rcases occurs with h | h <;> simp [h]

/-- The executable COMM is the manuscript's COMM on the two inputs opened apart. -/
theorem commClosed_sound_uniform (avoid : List String) (t x A u y B : Pattern)
    (calcT : calcTerm t = true) (calcU : calcTerm u = true) (calcA : calcTerm A = true)
    (calcB : calcTerm B = true)
    (fresh : ∀ z ∈ pvars (close (par (pFor t x A) (pFor u y B))), z ∈ avoid)
    {Q : Pattern} (produced : Q ∈ commClosed avoid (close (pFor t x A)) (close (pFor u y B))) :
    Step uniform (par (pFor t x A) (pFor u y B)) Q :=
  commClosed_sound_bodies avoid t x A u y B calcT calcU calcA calcB
    (fun z occurs => fresh z (mem_pvars_close_redex occurs)) produced

/-- The executable COMM is the manuscript's COMM under the variable convention. -/
theorem commClosed_sound (avoid : List String) (t x A u y B : Pattern)
    (calcT : calcTerm t = true) (calcU : calcTerm u = true) (calcA : calcTerm A = true)
    (calcB : calcTerm B = true)
    (fresh : ∀ z ∈ pvars (close (par (pFor t x A) (pFor u y B))), z ∈ avoid)
    {Q : Pattern} (produced : Q ∈ commClosed avoid (close (pFor t x A)) (close (pFor u y B))) :
    Step conventional (par (pFor t x A) (pFor u y B)) Q :=
  (commClosed_sound_uniform avoid t x A u y B calcT calcU calcA calcB fresh produced).mono
    uniform_conventional

/-- What a step of a closed process can be. -/
theorem mem_stepClosed {avoid : List String} {N Q : Pattern} (member : Q ∈ stepClosed avoid N) :
    (∃ a b, N = par a b ∧ (Q ∈ commClosed avoid a b ∨ ∃ n ∈ stepClosed avoid a, Q = par n b)) ∨
      (∃ x a, N = pReflect x a ∧ ∃ n ∈ stepClosed avoid a, Q = pFor (tProc n) x pZero) := by
  unfold stepClosed at member
  split at member
  · rename_i p q
    rcases List.mem_append.mp member with comm | parallel
    · exact .inl ⟨p, q, rfl, .inl comm⟩
    · obtain ⟨n, inside, rfl⟩ := List.mem_map.mp parallel
      exact .inl ⟨p, q, rfl, .inr ⟨n, inside, rfl⟩⟩
  · rename_i x p
    obtain ⟨n, inside, rfl⟩ := List.mem_map.mp member
    exact .inr ⟨x, p, rfl, n, inside, rfl⟩
  · cases member

theorem closeIn_eq_par {env : List (List String)} {P a b : Pattern} (eq : closeIn env P = par a b) :
    ∃ P₁ P₂, P = par P₁ P₂ ∧ a = closeIn env P₁ ∧ b = closeIn env P₂ := by
  cases P with
  | fvar y => cases h : lookupBound env y <;> simp [closeIn, h, boundCode, par, pPar] at eq
  | bvar n => simp [closeIn, par, pPar] at eq
  | apply c args => rw [closeIn_apply] at eq; simp [par, pPar] at eq
  | lambda nm body => simp [closeIn, par, pPar] at eq
  | multiLambda n nms body => simp [closeIn, par, pPar] at eq
  | subst body repl => simp [closeIn, par, pPar] at eq
  | collection ct elems rest =>
      simp only [closeIn, closeList_eq_map, par, pPar, Pattern.collection.injEq] at eq
      obtain ⟨rfl, list, rfl⟩ := eq
      match elems, list with
      | [P₁, P₂], list =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at list
          exact ⟨P₁, P₂, rfl, list.1.symm, list.2.symm⟩

theorem closeIn_eq_pReflect {env : List (List String)} {P x a : Pattern}
    (eq : closeIn env P = pReflect x a) :
    ∃ x' A, P = pReflect x' A ∧ x = closeIn env x' ∧ a = closeIn env A := by
  cases P with
  | fvar y => cases h : lookupBound env y <;> simp [closeIn, h, boundCode, pReflect] at eq
  | bvar n => simp [closeIn, pReflect] at eq
  | apply c args =>
      rw [closeIn_apply] at eq
      simp only [pReflect, Pattern.apply.injEq] at eq
      obtain ⟨rfl, list⟩ := eq
      simp only [show ("MRef" = "MFor") = False from by decide, if_false] at list
      match args, list with
      | [x', A], list =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at list
          exact ⟨x', A, rfl, list.1.symm, list.2.symm⟩
  | lambda nm body => simp [closeIn, pReflect] at eq
  | multiLambda n nms body => simp [closeIn, pReflect] at eq
  | subst body repl => simp [closeIn, pReflect] at eq
  | collection ct elems rest => simp [closeIn, pReflect] at eq

theorem commClosed_of_not_guard {avoid : List String} {a b : Pattern}
    (notGuard : asGuard a = none ∨ asGuard b = none) : commClosed avoid a b = [] := by
  unfold commClosed
  rcases notGuard with h | h <;> simp [h]

theorem calcTerm_par {p q : Pattern} (h : calcTerm (par p q) = true) :
    calcTerm p = true ∧ calcTerm q = true := by
  simpa [par, pPar, calcTerm, calcList] using h

theorem calcTerm_pFor {t x k : Pattern} (h : calcTerm (pFor t x k) = true) :
    calcTerm t = true ∧ calcTerm x = true ∧ calcTerm k = true := by
  simpa [pFor, calcTerm, calcList] using h

theorem calcTerm_pReflect {x p : Pattern} (h : calcTerm (pReflect x p) = true) :
    calcTerm x = true ∧ calcTerm p = true := by
  simpa [pReflect, calcTerm, calcList] using h

theorem alphaEq_pFor_channel (t x k : Pattern) : AlphaEq (pFor t x k) (pFor t (close x) k) := by
  unfold AlphaEq close
  rw [closeIn_pFor, closeIn_pFor, closeIn_closeIn x [] [] (by simp)]

theorem sizeOf_lt_par_left (p q : Pattern) : sizeOf p < sizeOf (par p q) := by
  simp [par, pPar]; omega

theorem sizeOf_lt_pReflect (x p : Pattern) : sizeOf p < sizeOf (pReflect x p) := by
  simp [pReflect]; omega

/-- **Soundness.** Every step of a closed calculus process is a step of the
relational semantics under the variable convention. -/
theorem stepClosed_sound_uniform (avoid : List String) :
    ∀ (n : ℕ) (P : Pattern), sizeOf P ≤ n → calcTerm P = true → (∀ z ∈ pvars (close P), z ∈ avoid) →
      ∀ Q ∈ stepClosed avoid (close P), Step uniform P Q := by
  intro n
  induction n with
  | zero =>
      intro P size
      have : 0 < sizeOf P := by cases P <;> simp
      omega
  | succ n ih =>
      intro P size inCalc fresh Q member
      rcases mem_stepClosed member with ⟨a, b, shape, which⟩ | ⟨x, a, shape, next, inside, rfl⟩
      · obtain ⟨P₁, P₂, rfl, rfl, rfl⟩ := closeIn_eq_par shape
        have calcs := calcTerm_par inCalc
        rcases which with comm | ⟨next, inside, rfl⟩
        · cases g1 : asGuard (closeIn [] P₁) with
          | none => rw [commClosed_of_not_guard (.inl g1)] at comm; cases comm
          | some r1 =>
              cases g2 : asGuard (closeIn [] P₂) with
              | none => rw [commClosed_of_not_guard (.inr g2)] at comm; cases comm
              | some r2 =>
                  obtain ⟨t, x, A, rfl, _⟩ := asGuard_closeIn g1
                  obtain ⟨u, y, B, rfl, _⟩ := asGuard_closeIn g2
                  obtain ⟨calcT, _, calcA⟩ := calcTerm_pFor calcs.1
                  obtain ⟨calcU, _, calcB⟩ := calcTerm_pFor calcs.2
                  exact commClosed_sound_uniform avoid t x A u y B calcT calcU calcA calcB fresh comm
        · have smaller := sizeOf_lt_par_left P₁ P₂
          have step := ih P₁ (by omega) calcs.1 (fun z occurs => fresh z (by
            unfold close; rw [closeIn_par, pvars_par]; exact List.mem_append_left _ occurs)) next inside
          exact Step.congruence (AlphaEq.refl _) (Step.parallel P₂ step)
            (AlphaEq.par (AlphaEq.refl _) (alphaEq_close P₂).symm)
      · obtain ⟨x', A, rfl, rfl, rfl⟩ := closeIn_eq_pReflect shape
        have calcs := calcTerm_pReflect inCalc
        have smaller := sizeOf_lt_pReflect x' A
        have step := ih A (by omega) calcs.2 (fun z occurs => fresh z (by
          unfold close; rw [closeIn_pReflect, pvars_pReflect]; exact List.mem_append_right _ occurs))
          next inside
        exact Step.congruence (AlphaEq.refl _) (Step.reflect x' step) (alphaEq_pFor_channel _ x' pZero)

theorem stepClosed_sound (avoid : List String) (n : ℕ) (P : Pattern) (size : sizeOf P ≤ n)
    (inCalc : calcTerm P = true) (fresh : ∀ z ∈ pvars (close P), z ∈ avoid) :
    ∀ Q ∈ stepClosed avoid (close P), Step conventional P Q := fun Q member =>
  (stepClosed_sound_uniform avoid n P size inCalc fresh Q member).mono uniform_conventional

/-- **Soundness of the corrected executable step**, with the uniform dot. -/
theorem cstep_sound_uniform {P Q : Pattern} (inCalc : calcTerm P = true) (member : Q ∈ cstep P) :
    Step uniform P Q :=
  stepClosed_sound_uniform (pvars (close P)) (sizeOf P) P le_rfl inCalc (fun _ occurs => occurs) Q member

/-- **Soundness of the corrected executable step.** -/
theorem cstep_sound {P Q : Pattern} (inCalc : calcTerm P = true) (member : Q ∈ cstep P) :
    Step conventional P Q :=
  (cstep_sound_uniform inCalc member).mono uniform_conventional

/-- **Alpha-invariance.** Alpha-equivalent processes have the same reducts. -/
theorem cstep_alpha_invariant {P P' : Pattern} (alpha : AlphaEq P P') : cstep P = cstep P' := by
  unfold cstep
  rw [show close P = close P' from alpha]

/-! ## The manuscript's renaming rule preserves the closed form -/

/-- Rename `y` to `z`, and nothing else. -/
def swapTo (y z : String) (v : String) : String := if v = y then z else v

theorem rename_of_fixed (g : String → String) (p : Pattern) (fixed : ∀ v ∈ pvars p, g v = v) :
    rename g p = p := by
  unfold rename
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, (∀ v ∈ pvars q, g v = v) →
      psubst (fun x => some (.fvar (g x))) q = q) with
  | bvar n => rfl
  | fvar x => simp [psubst, fixed x (by simp [pvars])]
  | apply c args ih =>
      simp only [psubst, psubstList_eq_map]
      rw [List.map_congr_left (g := id) fun q member =>
        ih q member fun v occurs => fixed v (mem_pvars_apply_of member occurs), List.map_id]
  | lambda nm body ih => simp only [psubst]; rw [ih fun v occurs => fixed v (by simpa [pvars] using occurs)]
  | multiLambda n nms body ih =>
      simp only [psubst]; rw [ih fun v occurs => fixed v (by simpa [pvars] using occurs)]
  | subst body repl ihb ihr =>
      simp only [psubst]
      rw [ihb fun v occurs => fixed v (by simp [pvars, occurs]),
        ihr fun v occurs => fixed v (by simp [pvars, occurs])]
  | collection ct elems rest ih =>
      simp only [psubst, psubstList_eq_map]
      rw [List.map_congr_left (g := id) fun q member =>
        ih q member fun v occurs => fixed v (mem_pvars_collection_of member occurs), List.map_id]
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member fixedQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head fixedQ
      · exact tail q later fixedQ


theorem binders_of_guardFree (p : Pattern) (free : guardFree p = true) : binders p = [] := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, guardFree q = true → binders q = []) with
  | bvar n => rfl
  | fvar x => rfl
  | apply c args ih =>
      simp only [guardFree, Bool.and_eq_true, bne_iff_ne, ne_eq, guardFreeList_iff] at free
      rw [binders_apply, if_neg free.1, List.flatMap_eq_nil_iff]
      exact fun q member => ih q member (free.2 q member)
  | lambda nm body ih => exact ih free
  | multiLambda n nms body ih => exact ih free
  | subst body repl ihb ihr =>
      simp only [guardFree, Bool.and_eq_true] at free
      simp [binders, ihb free.1, ihr free.2]
  | collection ct elems rest ih =>
      simp only [guardFree, guardFreeList_iff] at free
      simp only [binders, bindersList_eq_flatMap, List.flatMap_eq_nil_iff]
      exact fun q member => ih q member (free q member)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member freeQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head freeQ
      · exact tail q later freeQ

theorem swapTo_injOn {y z : String} {l : List String} (outside : z ∉ l) :
    ∀ a ∈ l, ∀ b ∈ l, swapTo y z a = swapTo y z b → a = b := by
  intro a ha b hb eq
  unfold swapTo at eq
  split at eq <;> split at eq
  · rename_i h1 h2; rw [h1, h2]
  · exact absurd (eq ▸ hb) outside
  · exact absurd (eq.symm ▸ ha) outside
  · exact eq

theorem lookupBound_none_of_not_mem {env : List (List String)} {x : String}
    (outside : ∀ f ∈ env, x ∉ f) : lookupBound env x = none := by
  induction env with
  | nil => rfl
  | cons f env ih =>
      simp [lookupBound, outside f (List.mem_cons_self ..),
        ih fun g member => outside g (List.mem_cons_of_mem _ member)]

/-- Renaming a bound variable to a fresh name, in the frame and in every
occurrence below it, does not change the closed form. -/
theorem closeIn_swap (y z : String) (l : List String) (yIn : y ∈ l) (zOut : z ∉ l) (k : Pattern) :
    z ∉ pvars k → y ∉ binders k → ∀ (inner env : List (List String)), (∀ f ∈ inner, y ∉ f ∧ z ∉ f) →
      closeIn (inner ++ l.map (swapTo y z) :: env) (rename (swapTo y z) k) =
        closeIn (inner ++ l :: env) k := by
  unfold rename
  induction k using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, z ∉ pvars q → y ∉ binders q →
      ∀ (inner env : List (List String)), (∀ f ∈ inner, y ∉ f ∧ z ∉ f) →
      closeIn (inner ++ l.map (swapTo y z) :: env) (psubst (fun x => some (.fvar (swapTo y z x))) q) =
        closeIn (inner ++ l :: env) q) with
  | bvar n => intro _ _ inner env _; rfl
  | fvar x =>
      intro zNot _ inner env innerOk
      have xz : x ≠ z := by intro same; subst same; simp [pvars] at zNot
      have injOn := swapTo_injOn (y := y) zOut
      simp only [psubst, Option.getD_some]
      by_cases xy : x = y
      · subst xy
        have inInner : lookupBound inner x = none :=
          lookupBound_none_of_not_mem fun f member => (innerOk f member).1
        have inInnerZ : lookupBound inner z = none :=
          lookupBound_none_of_not_mem fun f member => (innerOk f member).2
        have sw : swapTo x z x = z := by simp [swapTo]
        rw [sw]
        simp only [closeIn, lookupBound_append, inInner, inInnerZ]
        have zMem : z ∈ l.map (swapTo x z) := List.mem_map.mpr ⟨x, yIn, sw⟩
        have idx : (l.map (swapTo x z)).idxOf (swapTo x z x) = l.idxOf x :=
          idxOf_map_of_injOn _ l injOn yIn
        rw [sw] at idx
        simp [lookupBound, zMem, yIn, idx]
      · have sw : swapTo y z x = x := by simp [swapTo, xy]
        rw [sw]
        simp only [closeIn, lookupBound_append]
        cases hInner : lookupBound inner x with
        | some found => rfl
        | none =>
            by_cases inL : x ∈ l
            · have mapped : x ∈ l.map (swapTo y z) := List.mem_map.mpr ⟨x, inL, sw⟩
              have idx : (l.map (swapTo y z)).idxOf x = l.idxOf x := by
                conv_lhs => rw [← sw]
                exact idxOf_map_of_injOn _ l injOn inL
              simp [lookupBound, inL, mapped, idx]
            · have notMapped : x ∉ l.map (swapTo y z) := by
                intro member
                obtain ⟨w, wIn, eq⟩ := List.mem_map.mp member
                unfold swapTo at eq
                split at eq
                · exact xz eq.symm
                · exact inL (eq ▸ wIn)
              simp [lookupBound, inL, notMapped]
  | apply c args ih =>
      intro zNot yNot inner env innerOk
      simp only [psubst, psubstList_eq_map]
      rw [closeIn_apply, closeIn_apply]
      have eachZ : ∀ q ∈ args, z ∉ pvars q := fun q member occurs => zNot (mem_pvars_apply_of member occurs)
      by_cases guard : c = "MFor"
      · simp only [guard, if_true]
        rw [binders_apply, if_pos guard] at yNot
        by_cases short : args.length < 3
        · rw [bindersFor_short _ short] at yNot
          rcases closeFor_cases (inner ++ l.map (swapTo y z) :: env)
              (args.map (psubst fun x => some (.fvar (swapTo y z x)))) with ⟨_, eq⟩ | ⟨_, _, _, _, same, _⟩
          · rcases closeFor_cases (inner ++ l :: env) args with ⟨_, eq'⟩ | ⟨_, _, _, _, rfl, _⟩
            · rw [eq, eq', List.map_map]
              congr 1
              apply List.map_congr_left
              intro q member
              exact ih q member (eachZ q member)
                (fun bound => yNot (List.mem_flatMap.mpr ⟨q, member, bound⟩)) inner env innerOk
            · exact absurd short (by simp)
          · have := congrArg List.length same; simp at this; omega
        · match args, short with
          | [_], h => simp at h
          | [_, _], h => simp at h
          | t :: x :: k :: rest, _ =>
              rw [bindersFor_cons3] at yNot
              simp only [List.mem_append, not_or] at yNot
              obtain ⟨⟨⟨yT, yX⟩, yK⟩, yRest⟩ := yNot
              have zT : z ∉ pvars t := eachZ t (by simp)
              have tFixed : psubst (fun x => some (.fvar (swapTo y z x))) t = t := by
                have := rename_of_fixed (swapTo y z) t fun v occurs => by
                  have : v ≠ y := fun same => yT (same ▸ occurs)
                  simp [swapTo, this]
                exact this
              rw [List.map_cons, List.map_cons, List.map_cons, tFixed, closeFor_cons3, closeFor_cons3]
              congr 1
              refine List.cons_eq_cons.mpr ⟨rfl, ?_⟩
              refine List.cons_eq_cons.mpr ⟨ih x (by simp) (eachZ x (by simp))
                (fun bound => yX bound) inner env innerOk, ?_⟩
              refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
              · have step := ih k (by simp) (eachZ k (by simp)) yK (frame t :: inner) env (by
                  intro f member
                  rcases List.mem_cons.mp member with rfl | later
                  · exact ⟨fun m => yT (frame_subset t y m), fun m => zT (frame_subset t z m)⟩
                  · exact innerOk f later)
                simpa using step
              · rw [List.map_map]
                apply List.map_congr_left
                intro q member
                exact ih q (by simp [member]) (eachZ q (by simp [member]))
                  (fun bound => yRest (List.mem_flatMap.mpr ⟨q, member, bound⟩)) inner env innerOk
      · simp only [guard, if_false, List.map_map]
        rw [binders_apply, if_neg guard] at yNot
        congr 1
        apply List.map_congr_left
        intro q member
        exact ih q member (eachZ q member)
          (fun bound => yNot (List.mem_flatMap.mpr ⟨q, member, bound⟩)) inner env innerOk
  | lambda nm body ih =>
      intro zNot yNot inner env innerOk
      simp only [psubst, closeIn]
      rw [ih zNot yNot inner env innerOk]
  | multiLambda n nms body ih =>
      intro zNot yNot inner env innerOk
      simp only [psubst, closeIn]
      rw [ih zNot yNot inner env innerOk]
  | subst body repl ihb ihr =>
      intro zNot yNot inner env innerOk
      simp only [pvars, List.mem_append, not_or] at zNot
      simp only [binders, List.mem_append, not_or] at yNot
      simp only [psubst, closeIn]
      rw [ihb zNot.1 yNot.1 inner env innerOk, ihr zNot.2 yNot.2 inner env innerOk]
  | collection ct elems rest ih =>
      intro zNot yNot inner env innerOk
      simp only [psubst, closeIn, psubstList_eq_map, closeList_eq_map, List.map_map]
      simp only [binders, bindersList_eq_flatMap] at yNot
      congr 1
      apply List.map_congr_left
      intro q member
      exact ih q member (fun occurs => zNot (mem_pvars_collection_of member occurs))
        (fun bound => yNot (List.mem_flatMap.mpr ⟨q, member, bound⟩)) inner env innerOk
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member zNot yNot inner env innerOk
      rcases List.mem_cons.mp member with rfl | later
      · exact head zNot yNot inner env innerOk
      · exact tail q later zNot yNot inner env innerOk

/-- The manuscript's alpha rule `for(t <- x)P ≡ for(t{z/y} <- x)(P{z/y})`, for a
guard-free pattern. Its side conditions: `y` occurs in `t`, the new name `z`
occurs in neither `t` nor `P`, and `y` is not rebound inside `P`. The
manuscript states only `z ∉ FN(P)`; without `z ∉ t` the rule would merge two
pattern variables (`alpha_side_condition_needed`). -/
inductive AlphaRule : Pattern → Pattern → Prop where
  | rename (t x k : Pattern) (y z : String) (bound : y ∈ pvars t) (newInPattern : z ∉ pvars t)
      (newInBody : z ∉ pvars k) (notRebound : y ∉ binders k) (free : guardFree t = true) :
      AlphaRule (pFor t x k) (pFor (rename (swapTo y z) t) x (rename (swapTo y z) k))

/-- The least equivalence containing the alpha rule and closed under every
constructor position except a guard's pattern, which is data. -/
inductive Alpha : Pattern → Pattern → Prop where
  | rule {p q : Pattern} : AlphaRule p q → Alpha p q
  | refl (p : Pattern) : Alpha p p
  | symm {p q : Pattern} : Alpha p q → Alpha q p
  | trans {p q r : Pattern} : Alpha p q → Alpha q r → Alpha p r
  | apply (c : String) (before after : List Pattern) {a a' : Pattern} :
      ¬ (c = "MFor" ∧ before = []) → Alpha a a' →
      Alpha (.apply c (before ++ a :: after)) (.apply c (before ++ a' :: after))
  | collection (ct : CollType) (before after : List Pattern) (rest : Option String) {a a' : Pattern} :
      Alpha a a' →
      Alpha (.collection ct (before ++ a :: after) rest) (.collection ct (before ++ a' :: after) rest)

theorem closeIn_alphaRule {p q : Pattern} (rule : AlphaRule p q) (env : List (List String)) :
    closeIn env p = closeIn env q := by
  cases rule with
  | rename t x k y z bound newInPattern newInBody notRebound free =>
      rw [closeIn_pFor, closeIn_pFor]
      have frameNew : frame (rename (swapTo y z) t) = (frame t).map (swapTo y z) := by
        rw [frame_of_guardFree _ (by rw [guardFree_rename]; exact free), frame_of_guardFree t free]
        exact pvars_rename _ t
      rw [frameNew]
      have boundF : y ∈ frame t := by rw [frame_of_guardFree t free]; exact bound
      have newF : z ∉ frame t := by rw [frame_of_guardFree t free]; exact newInPattern
      have patternSame := closeIn_swap y z (frame t) boundF newF t newInPattern
        (by rw [binders_of_guardFree t free]; simp) [] [] (by simp)
      have bodySame := closeIn_swap y z (frame t) boundF newF k newInBody notRebound [] env
        (by simp)
      simp only [List.nil_append] at patternSame bodySame
      rw [patternSame, bodySame]

theorem closeFor_congr_later (env : List (List String)) (before after : List Pattern) {a a' : Pattern}
    (notFirst : before ≠ []) (same : ∀ env : List (List String), closeIn env a = closeIn env a') :
    closeFor env (before ++ a :: after) = closeFor env (before ++ a' :: after) := by
  match before, notFirst with
  | [b₀], _ =>
      cases after with
      | nil => simp [closeFor, same env]
      | cons k rest =>
          simp only [List.singleton_append]
          rw [closeFor_cons3, closeFor_cons3, same env]
  | [b₀, b₁], _ =>
      simp only [List.cons_append, List.nil_append]
      rw [closeFor_cons3, closeFor_cons3, same (frame b₀ :: env)]
  | b₀ :: b₁ :: b₂ :: more, _ =>
      simp only [List.cons_append]
      rw [closeFor_cons3, closeFor_cons3]
      simp [List.map_append, same env]

/-- **The manuscript's alpha-equivalence is contained in `AlphaEq`.** -/
theorem alpha_closeIn {p q : Pattern} (alpha : Alpha p q) :
    ∀ env : List (List String), closeIn env p = closeIn env q := by
  induction alpha with
  | rule rule => exact closeIn_alphaRule rule
  | refl p => intro env; rfl
  | symm _ ih => intro env; exact (ih env).symm
  | trans _ _ ih₁ ih₂ => intro env; exact (ih₁ env).trans (ih₂ env)
  | apply c before after notPattern _ ih =>
      intro env
      rw [closeIn_apply, closeIn_apply]
      by_cases guard : c = "MFor"
      · simp only [guard, if_true]
        have notFirst : before ≠ [] := fun empty => notPattern ⟨guard, empty⟩
        rw [closeFor_congr_later env before after notFirst ih]
      · simp [guard, ih env]
  | collection ct before after rest _ ih =>
      intro env
      simp [closeIn, closeList_eq_map, ih env]

theorem alpha_alphaEq {p q : Pattern} (alpha : Alpha p q) : AlphaEq p q := alpha_closeIn alpha []

/-- The executable step is invariant under the manuscript's alpha-equivalence. -/
theorem cstep_alpha_rule_invariant {P P' : Pattern} (alpha : Alpha P P') : cstep P = cstep P' :=
  cstep_alpha_invariant (alpha_alphaEq alpha)

/-! ## Completeness on the closing fragment -/

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm
  (psubst_of_pvars_nil psubst_comp pcomp)

theorem firstOrderList_iff (ps : List Pattern) :
    firstOrder.firstOrderList ps = true ↔ ∀ p ∈ ps, firstOrder p = true := by
  induction ps with
  | nil => simp [firstOrder.firstOrderList]
  | cons p ps ih => simp [firstOrder.firstOrderList, ih]

/-- Closing keeps a process free of substitution nodes and collection rests. -/
theorem firstOrder_closeIn (p : Pattern) (inCalc : calcTerm p = true) :
    ∀ env : List (List String), firstOrder (closeIn env p) = true := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, calcTerm q = true →
      ∀ env : List (List String), firstOrder (closeIn env q) = true) with
  | bvar n => simp [calcTerm] at inCalc
  | fvar x => intro env; cases eq : lookupBound env x <;> simp [closeIn, eq, firstOrder, boundCode]
  | apply c args ih =>
      intro env
      simp only [calcTerm, calcList_iff] at inCalc
      rw [closeIn_apply]
      simp only [firstOrder, firstOrderList_iff]
      split
      · rcases closeFor_cases env args with ⟨_, eq⟩ | ⟨t, x, k, rest, rfl, eq⟩
        · rw [eq]; intro r member
          obtain ⟨q, inside, rfl⟩ := List.mem_map.mp member
          exact ih q inside (inCalc q inside) env
        · rw [eq]; intro r member
          simp only [List.mem_cons, List.mem_map] at member
          rcases member with rfl | rfl | rfl | ⟨q, inside, rfl⟩
          · exact ih t (by simp) (inCalc t (by simp)) _
          · exact ih x (by simp) (inCalc x (by simp)) _
          · exact ih k (by simp) (inCalc k (by simp)) _
          · exact ih q (by simp [inside]) (inCalc q (by simp [inside])) _
      · intro r member
        obtain ⟨q, inside, rfl⟩ := List.mem_map.mp member
        exact ih q inside (inCalc q inside) env
  | lambda nm body ih => simp [calcTerm] at inCalc
  | multiLambda n nms body ih => simp [calcTerm] at inCalc
  | subst body repl ihb ihr => simp [calcTerm] at inCalc
  | collection ct elems rest ih =>
      intro env
      simp only [calcTerm, Bool.and_eq_true, Option.isNone_iff_eq_none, calcList_iff] at inCalc
      obtain ⟨rfl, inCalc⟩ := inCalc
      simp only [closeIn, closeList_eq_map, firstOrder, Option.isNone_none, Bool.true_and,
        firstOrderList_iff]
      intro r member
      obtain ⟨q, inside, rfl⟩ := List.mem_map.mp member
      exact ih q inside (inCalc q inside) env
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member calcQ env
      rcases List.mem_cons.mp member with rfl | later
      · exact head calcQ env
      · exact tail q later calcQ env

/-- Opening with first-order values keeps a process first-order. -/
theorem firstOrder_instantiateAt (value : ℕ → Option Pattern)
    (values : ∀ i v, value i = some v → firstOrder v = true) (p : Pattern) (fo : firstOrder p = true) :
    ∀ depth, firstOrder (instantiateAt depth value p) = true := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, firstOrder q = true →
      ∀ depth, firstOrder (instantiateAt depth value q) = true) with
  | bvar n =>
      intro depth
      simp only [instantiateAt]
      split
      · cases eq : value (Nat.unpair n).2 with
        | none => simp [firstOrder]
        | some v => simpa using values _ v eq
      · rfl
  | fvar x => intro depth; rfl
  | apply c args ih =>
      intro depth
      simp only [firstOrder, firstOrderList_iff] at fo
      rw [instantiateAt_apply]
      simp only [firstOrder, firstOrderList_iff]
      split
      · by_cases short : args.length < 3
        · rw [instantiateFor_short _ _ _ short]
          intro r member
          obtain ⟨q, inside, rfl⟩ := List.mem_map.mp member
          exact ih q inside (fo q inside) depth
        · match args, short with
          | [_], h => simp at h
          | [_, _], h => simp at h
          | t :: x :: k :: rest, _ =>
              rw [instantiateFor_cons3]
              intro r member
              simp only [List.mem_cons, List.mem_map] at member
              rcases member with rfl | rfl | rfl | ⟨q, inside, rfl⟩
              · exact fo r (by simp)
              · exact ih x (by simp) (fo x (by simp)) depth
              · exact ih k (by simp) (fo k (by simp)) (depth + 1)
              · exact ih q (by simp [inside]) (fo q (by simp [inside])) depth
      · intro r member
        obtain ⟨q, inside, rfl⟩ := List.mem_map.mp member
        exact ih q inside (fo q inside) depth
  | lambda nm body ih => intro depth; exact ih fo depth
  | multiLambda n nms body ih => intro depth; exact ih fo depth
  | subst body repl ihb ihr => simp [firstOrder] at fo
  | collection ct elems rest ih =>
      intro depth
      simp only [firstOrder, Bool.and_eq_true, Option.isNone_iff_eq_none, firstOrderList_iff] at fo
      obtain ⟨rfl, fo⟩ := fo
      simp only [instantiateAt, instantiateList_eq_map, firstOrder, Option.isNone_none, Bool.true_and,
        firstOrderList_iff]
      intro r member
      obtain ⟨q, inside, rfl⟩ := List.mem_map.mp member
      exact ih q inside (fo q inside) depth
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member foQ depth
      rcases List.mem_cons.mp member with rfl | later
      · exact head foQ depth
      · exact tail q later foQ depth

/-- A process with no variables is already closed. -/
theorem closeIn_of_pvars_nil (p : Pattern) (closed : pvars p = []) :
    ∀ env : List (List String), closeIn env p = p := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, pvars q = [] →
      ∀ env : List (List String), closeIn env q = q) with
  | bvar n => intro env; rfl
  | fvar x => simp [pvars] at closed
  | apply c args ih =>
      intro env
      rw [pvars_apply, pvarsList_eq_flatMap, List.flatMap_eq_nil_iff] at closed
      rw [closeIn_apply]
      congr 1
      split
      · rcases closeFor_cases env args with ⟨_, eq⟩ | ⟨t, x, k, rest, rfl, eq⟩
        · rw [eq]
          conv_rhs => rw [← List.map_id args]
          exact List.map_congr_left fun q member => ih q member (closed q member) env
        · rw [eq]
          have frameNil : frame t = [] := List.eq_nil_iff_forall_not_mem.mpr fun y member => by
            simpa [closed t (by simp)] using frame_subset t y member
          rw [frameNil, ih t (by simp) (closed t (by simp)), ih x (by simp) (closed x (by simp)),
            ih k (by simp) (closed k (by simp))]
          congr 3
          conv_rhs => rw [← List.map_id rest]
          exact List.map_congr_left fun q member =>
            ih q (by simp [member]) (closed q (by simp [member])) env
      · conv_rhs => rw [← List.map_id args]
        exact List.map_congr_left fun q member => ih q member (closed q member) env
  | lambda nm body ih => intro env; simp [closeIn, ih (by simpa [pvars] using closed) env]
  | multiLambda n nms body ih => intro env; simp [closeIn, ih (by simpa [pvars] using closed) env]
  | subst body repl ihb ihr =>
      intro env
      simp only [pvars, List.append_eq_nil_iff] at closed
      simp [closeIn, ihb closed.1 env, ihr closed.2 env]
  | collection ct elems rest ih =>
      intro env
      simp only [pvars, pvarsList_eq_flatMap, List.flatMap_eq_nil_iff] at closed
      simp only [closeIn, closeList_eq_map]
      congr 1
      conv_rhs => rw [← List.map_id elems]
      exact List.map_congr_left fun q member => ih q member (closed q member) env
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member closedQ env
      rcases List.mem_cons.mp member with rfl | later
      · exact head closedQ env
      · exact tail q later closedQ env

theorem lookupBound_some_mem {env : List (List String)} {x : String} {found : ℕ × ℕ}
    (eq : lookupBound env x = some found) : ∃ f ∈ env, x ∈ f := by
  induction env generalizing found with
  | nil => cases eq
  | cons f env ih =>
      by_cases here : x ∈ f
      · exact ⟨f, List.mem_cons_self .., here⟩
      · simp only [lookupBound, here, if_false, Option.map_eq_some_iff] at eq
        obtain ⟨inner, eq', _⟩ := eq
        obtain ⟨g, member, inG⟩ := ih eq'
        exact ⟨g, List.mem_cons_of_mem _ member, inG⟩

theorem psubst_of_none (θ : PSubst) (p : Pattern) (none : ∀ v ∈ pvars p, θ v = none) : psubst θ p = p := by
  rw [Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm.psubst_congr θ
      (fun _ => Option.none) p none,
    Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm.psubst_none]

/-- Substituting closed values for a frame's variables commutes with closing:
substitute and close, or close, open the frame with names, and substitute the
names. -/
theorem psubst_open_closeIn (names l : List String) (long : l.length ≤ names.length)
    (θ θ' : PSubst) (A : Pattern) (inCalc : calcTerm A = true) :
    (∀ v ∈ l, v ∉ binders A) → ∀ inner : List (List String), (∀ f ∈ inner, ∀ v ∈ l, v ∉ f) →
      (∀ v ∈ pvars A, v ∈ l → ∃ g, θ v = some g ∧ pvars g = [] ∧ θ' (nameOf names l v) = some g) →
      (∀ v ∈ pvars A, v ∉ l → θ v = none) →
      (∀ x ∈ pvars (closeIn (inner ++ [l]) A), θ' x = none) →
      psubst θ' (instantiateAt inner.length (fun i => names[i]?.map Pattern.fvar)
          (closeIn (inner ++ [l]) A)) = closeIn inner (psubst θ A) := by
  induction A using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, calcTerm q = true →
      (∀ v ∈ l, v ∉ binders q) → ∀ inner : List (List String), (∀ f ∈ inner, ∀ v ∈ l, v ∉ f) →
      (∀ v ∈ pvars q, v ∈ l → ∃ g, θ v = some g ∧ pvars g = [] ∧ θ' (nameOf names l v) = some g) →
      (∀ v ∈ pvars q, v ∉ l → θ v = none) →
      (∀ x ∈ pvars (closeIn (inner ++ [l]) q), θ' x = none) →
      psubst θ' (instantiateAt inner.length (fun i => names[i]?.map Pattern.fvar)
          (closeIn (inner ++ [l]) q)) = closeIn inner (psubst θ q)) with
  | bvar n => simp [calcTerm] at inCalc
  | fvar v =>
      intro _ inner innerOk inL outL closedNone
      cases eqInner : lookupBound inner v with
      | some found =>
          have small := lookupBound_lt eqInner
          have whole : lookupBound (inner ++ [l]) v = some found := by rw [lookupBound_append, eqInner]
          obtain ⟨f, fIn, vIn⟩ := lookupBound_some_mem eqInner
          have notL : v ∉ l := fun member => innerOk f fIn v member vIn
          have θv : θ v = none := outL v (by simp [pvars]) notL
          simp only [closeIn, whole, instantiateAt_code, if_neg (Nat.ne_of_lt small)]
          simp [psubst, boundCode, θv, closeIn, eqInner]
      | none =>
          by_cases member : v ∈ l
          · obtain ⟨g, θv, closedG, θ'v⟩ := inL v (by simp [pvars]) member
            have whole : lookupBound (inner ++ [l]) v = some (inner.length, l.idxOf v) := by
              rw [lookupBound_append, eqInner, lookupBound_single_mem member]; simp
            simp only [closeIn, whole, instantiateAt_code, if_true, names_getElem?_nameOf long member,
              Option.map_some, Option.getD_some]
            simp only [psubst, θ'v, θv, Option.getD_some]
            exact (closeIn_of_pvars_nil g closedG inner).symm
          · have whole : lookupBound (inner ++ [l]) v = none := by
              rw [lookupBound_append, eqInner, lookupBound_single_not_mem member]; simp
            have θv : θ v = none := outL v (by simp [pvars]) member
            have θ'v : θ' v = none := closedNone v (by simp [closeIn, whole, pvars])
            simp [closeIn, whole, instantiateAt, psubst, θv, θ'v, eqInner]
  | apply c args ih =>
      intro kept inner innerOk inL outL closedNone
      simp only [calcTerm, calcList_iff] at inCalc
      have inLQ : ∀ q ∈ args, ∀ v ∈ pvars q, v ∈ l →
          ∃ g, θ v = some g ∧ pvars g = [] ∧ θ' (nameOf names l v) = some g :=
        fun q member v occurs => inL v (mem_pvars_apply_of member occurs)
      have outLQ : ∀ q ∈ args, ∀ v ∈ pvars q, v ∉ l → θ v = none :=
        fun q member v occurs => outL v (mem_pvars_apply_of member occurs)
      rw [closeIn_apply] at closedNone
      rw [closeIn_apply, instantiateAt_apply]
      simp only [psubst, psubstList_eq_map]
      rw [closeIn_apply, binders_apply] at *
      by_cases guard : c = "MFor"
      · subst guard
        simp only [if_true] at closedNone kept ⊢
        by_cases short : args.length < 3
        · rw [bindersFor_short _ short] at kept
          rcases closeFor_cases (inner ++ [l]) args with ⟨_, eq⟩ | ⟨_, _, _, _, rfl, _⟩
          · rw [eq] at closedNone ⊢
            rw [instantiateFor_short _ _ _ (by simpa using short)]
            rcases closeFor_cases inner (args.map (psubst θ)) with ⟨_, eq'⟩ | ⟨_, _, _, _, same, _⟩
            · rw [eq']
              simp only [List.map_map]
              congr 1
              apply List.map_congr_left
              intro q member
              exact ih q member (inCalc q member)
                (fun v vin bound => kept v vin (List.mem_flatMap.mpr ⟨q, member, bound⟩)) inner innerOk
                (inLQ q member) (outLQ q member)
                (fun x occurs => closedNone x (mem_pvars_apply_of (List.mem_map_of_mem member) occurs))
            · have := congrArg List.length same; simp at this; omega
          · exact absurd short (by simp)
        · match args, short with
          | [_], h => simp at h
          | [_, _], h => simp at h
          | t :: x :: k :: rest, _ =>
              rw [bindersFor_cons3] at kept
              simp only [List.mem_append, not_or] at kept
              rw [closeFor_cons3] at closedNone ⊢
              rw [instantiateFor_cons3]
              simp only [List.map_cons]
              rw [closeFor_cons3]
              have tFixed : psubst θ t = t := psubst_of_none θ t fun v occurs =>
                outL v (mem_pvars_apply_of (by simp) occurs)
                  (fun vin => (kept v vin).1.1.1 occurs)
              have tcFixed : psubst θ' (closeIn [frame t] t) = closeIn [frame t] t :=
                psubst_of_pvars_nil θ' _ (pvars_closed_pattern t)
              rw [tFixed, tcFixed]
              have closedAt : ∀ q y, q ∈ (closeIn [frame t] t :: closeIn (inner ++ [l]) x ::
                  closeIn (frame t :: (inner ++ [l])) k :: rest.map (closeIn (inner ++ [l]))) →
                  y ∈ pvars q → θ' y = none :=
                fun q y member occurs => closedNone y (mem_pvars_apply_of member occurs)
              congr 1
              refine List.cons_eq_cons.mpr ⟨rfl, ?_⟩
              refine List.cons_eq_cons.mpr ⟨ih x (by simp) (inCalc x (by simp))
                (fun v vin => (kept v vin).1.1.2) inner innerOk (inLQ x (by simp)) (outLQ x (by simp))
                (fun y occurs => closedAt _ y (by simp) occurs), ?_⟩
              refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
              · have step := ih k (by simp) (inCalc k (by simp)) (fun v vin => (kept v vin).1.2)
                  (frame t :: inner) (by
                    intro f member v vin
                    rcases List.mem_cons.mp member with rfl | later
                    · exact fun m => (kept v vin).1.1.1 (frame_subset t v m)
                    · exact innerOk f later v vin)
                  (inLQ k (by simp)) (outLQ k (by simp)) (fun y occurs => closedAt _ y (by simp) occurs)
                simpa using step
              · simp only [List.map_map]
                apply List.map_congr_left
                intro q member
                exact ih q (by simp [member]) (inCalc q (by simp [member]))
                  (fun v vin bound => (kept v vin).2 (List.mem_flatMap.mpr ⟨q, member, bound⟩))
                  inner innerOk (inLQ q (by simp [member])) (outLQ q (by simp [member]))
                  (fun y occurs => closedAt _ y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (List.mem_map_of_mem member)))) occurs)
      · simp only [guard, if_false] at closedNone kept ⊢
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro q member
        exact ih q member (inCalc q member)
          (fun v vin bound => kept v vin (List.mem_flatMap.mpr ⟨q, member, bound⟩)) inner innerOk
          (inLQ q member) (outLQ q member)
          (fun x occurs => closedNone x (mem_pvars_apply_of (List.mem_map_of_mem member) occurs))
  | lambda nm body ih => simp [calcTerm] at inCalc
  | multiLambda n nms body ih => simp [calcTerm] at inCalc
  | subst body repl ihb ihr => simp [calcTerm] at inCalc
  | collection ct elems rest ih =>
      intro kept inner innerOk inL outL closedNone
      simp only [calcTerm, Bool.and_eq_true, Option.isNone_iff_eq_none, calcList_iff] at inCalc
      obtain ⟨rfl, inCalc⟩ := inCalc
      simp only [closeIn, closeList_eq_map] at closedNone
      simp only [binders, bindersList_eq_flatMap] at kept
      simp only [closeIn, closeList_eq_map, instantiateAt, instantiateList_eq_map, psubst,
        psubstList_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q member
      exact ih q member (inCalc q member)
        (fun v vin bound => kept v vin (List.mem_flatMap.mpr ⟨q, member, bound⟩)) inner innerOk
        (fun v occurs => inL v (mem_pvars_collection_of member occurs))
        (fun v occurs => outL v (mem_pvars_collection_of member occurs))
        (fun x occurs => closedNone x (mem_pvars_collection_of (List.mem_map_of_mem member) occurs))
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member calcQ keptQ inner innerOk inLQ outLQ closedQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head calcQ keptQ inner innerOk inLQ outLQ closedQ
      · exact tail q later calcQ keptQ inner innerOk inLQ outLQ closedQ

theorem psubst_getD_congr_on {σ τ : PSubst} {p : Pattern}
    (agree : ∀ v ∈ pvars p, (σ v).getD (.fvar v) = (τ v).getD (.fvar v)) : psubst σ p = psubst τ p := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps,
      (∀ v ∈ pvars q, (σ v).getD (.fvar v) = (τ v).getD (.fvar v)) → psubst σ q = psubst τ q) with
  | bvar n => rfl
  | fvar x => simp only [psubst]; exact agree x (by simp [pvars])
  | apply c args ih =>
      simp only [psubst, psubstList_eq_map]
      exact congrArg _ (List.map_congr_left fun q member =>
        ih q member fun v occurs => agree v (mem_pvars_apply_of member occurs))
  | lambda nm body ih => simp only [psubst]; rw [ih fun v occurs => agree v (by simpa [pvars] using occurs)]
  | multiLambda n nms body ih =>
      simp only [psubst]; rw [ih fun v occurs => agree v (by simpa [pvars] using occurs)]
  | subst body repl ihb ihr =>
      simp only [psubst]
      rw [ihb fun v occurs => agree v (by simp [pvars, occurs]),
        ihr fun v occurs => agree v (by simp [pvars, occurs])]
  | collection ct elems rest ih =>
      simp only [psubst, psubstList_eq_map]
      rw [List.map_congr_left fun q member =>
        ih q member fun v occurs => agree v (mem_pvars_collection_of member occurs)]
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member agreeQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head agreeQ
      · exact tail q later agreeQ

theorem psubst_rename (θ : PSubst) (g : String → String) (p : Pattern) :
    psubst θ (rename g p) = psubst (fun v => some (psubst θ (.fvar (g v)))) p := by
  unfold rename
  rw [psubst_comp]
  rfl

theorem rename_congr {g g' : String → String} {p : Pattern} (agree : ∀ v ∈ pvars p, g v = g' v) :
    rename g p = rename g' p := by
  unfold rename
  exact Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm.psubst_congr
    _ _ p fun v occurs => by simp [agree v occurs]

/-- Two principal unifiers agree on every variable one of them grounds: the
unifier of the inputs opened apart reads, at each opened name, the closed value
the source unifier gives the original variable. -/
theorem principal_agree {t u : Pattern} {bs : Bindings} (principal : Principal t u bs)
    (ρ : String → String) {σ : Bindings} (opened : Principal (rename ρ t) (rename ρ u) σ)
    {v : String} {g : Pattern} (found : bs.lookup v = some g) (closed : pvars g = []) :
    σ.lookup (ρ v) = some g := by
  let σρ : PSubst := fun w => some (psubst σ.lookup (.fvar (ρ w)))
  have composed : ∀ p, psubst σρ p = psubst σ.lookup (rename ρ p) := fun p =>
    (psubst_rename σ.lookup ρ p).symm
  have unifies : psubst σρ t = psubst σρ u := by rw [composed, composed]; exact opened.solves
  have absorbs := principal.general σρ unifies (.fvar v)
  simp only [psubst, found, Option.getD_some] at absorbs
  rw [psubst_of_pvars_nil σρ g closed] at absorbs
  simp only [σρ, Option.getD_some, psubst] at absorbs
  cases lookupV : σ.lookup (ρ v) with
  | none =>
      rw [lookupV] at absorbs
      simp only [Option.getD_none] at absorbs
      rw [absorbs] at closed
      simp [pvars] at closed
  | some value =>
      rw [lookupV] at absorbs
      simp only [Option.getD_some] at absorbs
      rw [absorbs]

/-- Inverting the opening renaming. -/
def unopen (left right : List String) (gL gR : String → String) (w : String) : String :=
  match left.find? (fun v => gL v = w) with
  | some v => v
  | none =>
      match right.find? (fun v => gR v = w) with
      | some v => v
      | none => w

theorem unopen_left {left right : List String} {gL gR : String → String}
    (inj : ∀ a ∈ left, ∀ b ∈ left, gL a = gL b → a = b) {v : String} (member : v ∈ left) :
    unopen left right gL gR (gL v) = v := by
  unfold unopen
  cases found : left.find? (fun v' => decide (gL v' = gL v)) with
  | none =>
      exfalso
      have := List.find?_eq_none.mp found v member
      simp at this
  | some v' =>
      simp only
      have same := List.find?_some found
      simp only [decide_eq_true_eq] at same
      exact inj v' (List.mem_of_find?_eq_some found) v member same

theorem unopen_right {left right : List String} {gL gR : String → String}
    (inj : ∀ a ∈ right, ∀ b ∈ right, gR a = gR b → a = b)
    (apart : ∀ a ∈ left, ∀ b ∈ right, gL a ≠ gR b) {w : String} (member : w ∈ right) :
    unopen left right gL gR (gR w) = w := by
  unfold unopen
  cases found : left.find? (fun v' => decide (gL v' = gR w)) with
  | some v' =>
      exfalso
      have same := List.find?_some found
      simp only [decide_eq_true_eq] at same
      exact apart v' (List.mem_of_find?_eq_some found) w member same
  | none =>
      simp only
      cases found' : right.find? (fun v' => decide (gR v' = gR w)) with
      | none =>
          exfalso
          have := List.find?_eq_none.mp found' w member
          simp at this
      | some w' =>
          simp only
          have same := List.find?_some found'
          simp only [decide_eq_true_eq] at same
          exact inj w' (List.mem_of_find?_eq_some found') w member same

/-- Inputs that unify still unify after their variables are renamed apart. -/
theorem unify_opened_exists {t u : Pattern} {bs : Bindings} (principal : Principal t u bs)
    (gL gR : String → String) (injL : ∀ a ∈ pvars t, ∀ b ∈ pvars t, gL a = gL b → a = b)
    (injR : ∀ a ∈ pvars u, ∀ b ∈ pvars u, gR a = gR b → a = b)
    (apart : ∀ a ∈ pvars t, ∀ b ∈ pvars u, gL a ≠ gR b) :
    ∃ σ, unify (rename gL t) (rename gR u) = some σ := by
  apply unify_complete
  let back := unopen (pvars t) (pvars u) gL gR
  refine ⟨fun w => some (psubst bs.lookup (.fvar (back w))), ?_⟩
  rw [psubst_rename, psubst_rename]
  have left : psubst (fun v => some (psubst (fun w => some (psubst bs.lookup (.fvar (back w))))
      (.fvar (gL v)))) t = psubst bs.lookup t := by
    apply psubst_getD_congr_on
    intro v occurs
    simp [psubst, back, unopen_left injL occurs]
  have right : psubst (fun v => some (psubst (fun w => some (psubst bs.lookup (.fvar (back w))))
      (.fvar (gR v)))) u = psubst bs.lookup u := by
    apply psubst_getD_congr_on
    intro v occurs
    simp [psubst, back, unopen_right injR apart occurs]
  rw [left, right]
  exact principal.solves

/-! ## Closing depends only on the closed form -/

mutual
/-- Bind the free variables an environment binds, below `depth` guards. -/
def abstractAt (env : List (List String)) (depth : ℕ) : Pattern → Pattern
  | .fvar x =>
      match lookupBound env x with
      | some found => boundCode (found.1 + depth) found.2
      | none => .fvar x
  | .bvar n => .bvar n
  | .apply c args =>
      .apply c (if c = "MFor" then abstractFor env depth args else abstractList env depth args)
  | .lambda nm body => .lambda nm (abstractAt env depth body)
  | .multiLambda n nms body => .multiLambda n nms (abstractAt env depth body)
  | .subst body repl => .subst (abstractAt env depth body) (abstractAt env depth repl)
  | .collection ct elems rest => .collection ct (abstractList env depth elems) rest
def abstractList (env : List (List String)) (depth : ℕ) : List Pattern → List Pattern
  | [] => []
  | p :: ps => abstractAt env depth p :: abstractList env depth ps
def abstractFor (env : List (List String)) (depth : ℕ) : List Pattern → List Pattern
  | [] => []
  | [p] => [abstractAt env depth p]
  | [p, q] => [abstractAt env depth p, abstractAt env depth q]
  | t :: x :: k :: rest =>
      t :: abstractAt env depth x :: abstractAt env (depth + 1) k :: abstractList env depth rest
end

theorem abstractList_eq_map (env : List (List String)) (depth : ℕ) (ps : List Pattern) :
    abstractList env depth ps = ps.map (abstractAt env depth) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [abstractList, ih]

/-- Closing in a longer environment closes in the inner part, then binds the
rest. -/
theorem closeIn_append (p : Pattern) : ∀ inner env : List (List String),
    closeIn (inner ++ env) p = abstractAt env inner.length (closeIn inner p) := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ inner env : List (List String),
      closeIn (inner ++ env) q = abstractAt env inner.length (closeIn inner q)) with
  | bvar n => intro inner env; rfl
  | fvar x =>
      intro inner env
      cases hInner : lookupBound inner x with
      | some found =>
          simp [closeIn, lookupBound_append, hInner, abstractAt, boundCode]
      | none =>
          cases hEnv : lookupBound env x with
          | none => simp [closeIn, lookupBound_append, hInner, hEnv, abstractAt]
          | some found => simp [closeIn, lookupBound_append, hInner, hEnv, abstractAt, boundCode]
  | apply c args ih =>
      intro inner env
      rw [closeIn_apply, closeIn_apply]
      by_cases guard : c = "MFor"
      · subst guard
        simp only [if_true, abstractAt]
        rcases closeFor_cases (inner ++ env) args with ⟨short, eq⟩ | ⟨t, x, k, rest, rfl, eq⟩
        · rcases closeFor_cases inner args with ⟨_, eq'⟩ | ⟨_, _, _, _, same, _⟩
          · rw [eq, eq']
            match args, short with
            | [], _ => rfl
            | [p], _ =>
                simp only [List.map_cons, List.map_nil, abstractFor]
                rw [ih p (by simp) inner env]
            | [p, q], _ =>
                simp only [List.map_cons, List.map_nil, abstractFor]
                rw [ih p (by simp) inner env, ih q (by simp) inner env]
          · subst same; simp at short; omega
        · rw [eq, closeFor_cons3]
          simp only [abstractFor, abstractList_eq_map, List.map_map]
          rw [ih x (by simp) inner env]
          have step := ih k (by simp) (frame t :: inner) env
          simp only [List.cons_append, List.length_cons] at step
          rw [step]
          congr 4
          apply List.map_congr_left
          intro q member
          exact ih q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)))
            inner env
      · simp only [guard, if_false, abstractAt, abstractList_eq_map, List.map_map]
        congr 1
        exact List.map_congr_left fun q member => ih q member inner env
  | lambda nm body ih => intro inner env; simp [closeIn, abstractAt, ih inner env]
  | multiLambda n nms body ih => intro inner env; simp [closeIn, abstractAt, ih inner env]
  | subst body repl ihb ihr =>
      intro inner env; simp [closeIn, abstractAt, ihb inner env, ihr inner env]
  | collection ct elems rest ih =>
      intro inner env
      simp only [closeIn, closeList_eq_map, abstractAt, abstractList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun q member => ih q member inner env
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member inner env
      rcases List.mem_cons.mp member with rfl | later
      · exact head inner env
      · exact tail q later inner env

/-- Alpha-equivalent processes close alike in every environment. -/
theorem closeIn_of_alphaEq {p q : Pattern} (alpha : AlphaEq p q) (env : List (List String)) :
    closeIn env p = closeIn env q := by
  have hp := closeIn_append p [] env
  have hq := closeIn_append q [] env
  simp only [List.nil_append, List.length_nil] at hp hq
  rw [hp, hq]
  exact congrArg (abstractAt env 0) alpha

/-- A reflected listener is determined by the alpha class of its process. -/
theorem alphaEq_listener {p q x y : Pattern} (alpha : AlphaEq p q) (channel : AlphaEq x y) :
    AlphaEq (pFor (tProc p) x pZero) (pFor (tProc q) y pZero) := by
  unfold AlphaEq close
  rw [closeIn_pFor, closeIn_pFor]
  have sameFrame : frame (tProc p) = frame (tProc q) := by
    unfold frame
    rw [closeIn_tProc, closeIn_tProc]
    exact congrArg (fun r => pvars (tProc r)) alpha
  rw [sameFrame, closeIn_of_alphaEq (show AlphaEq (tProc p) (tProc q) from by
    unfold AlphaEq close; rw [closeIn_tProc, closeIn_tProc]; exact congrArg tProc alpha) _]
  rw [show closeIn [] x = closeIn [] y from channel]

/-! ## Completeness -/

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm
  (lookup_eq_none_of_keys)

/-- The manuscript's dot: each bound variable reads the quotation of its value. -/
def dotOf (bs : Bindings) : PSubst := fun x => (bs.lookup x).map nQuote

theorem firstOrder_of_calcTerm (p : Pattern) (inCalc : calcTerm p = true) : firstOrder p = true := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, calcTerm q = true → firstOrder q = true) with
  | bvar n => simp [calcTerm] at inCalc
  | fvar x => rfl
  | apply c args ih =>
      simp only [calcTerm, calcList_iff] at inCalc
      simp only [firstOrder, firstOrderList_iff]
      exact fun q member => ih q member (inCalc q member)
  | lambda nm body ih => simp [calcTerm] at inCalc
  | multiLambda n nms body ih => simp [calcTerm] at inCalc
  | subst body repl ihb ihr => simp [calcTerm] at inCalc
  | collection ct elems rest ih =>
      simp only [calcTerm, Bool.and_eq_true, calcList_iff] at inCalc
      simp only [firstOrder, Bool.and_eq_true, firstOrderList_iff]
      exact ⟨inCalc.1, fun q member => ih q member (inCalc.2 q member)⟩
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member calcQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head calcQ
      · exact tail q later calcQ

theorem stepClosed_par (avoid : List String) (p q : Pattern) :
    stepClosed avoid (par p q) = commClosed avoid p q ++ (stepClosed avoid p).map fun n => par n q := by
  simp [stepClosed, par, pPar]

theorem stepClosed_reflect (avoid : List String) (x p : Pattern) :
    stepClosed avoid (pReflect x p) = (stepClosed avoid p).map fun n => pFor (tProc n) x pZero := by
  simp [stepClosed, pReflect]

theorem pvars_nQuote (p : Pattern) : pvars (nQuote p) = pvars p := by
  simp [nQuote, pvars, pvars.pvarsList]

/-- **COMM completeness on the closing fragment.** -/
theorem commClosed_complete (avoid : List String) (t u x A B : Pattern) (bs : Bindings)
    (principal : Principal t u bs) (admitted : closing t A u B bs)
    (fresh : ∀ z ∈ pvars (close (par (pFor t x A) (pFor u x B))), z ∈ avoid) :
    ∃ Q' ∈ commClosed avoid (close (pFor t x A)) (close (pFor u x B)),
      AlphaEq Q' (par (applyDot bs A) (applyDot bs B)) := by
  obtain ⟨apart, freeT, freeU, calcT, calcU, calcA, calcB, ground⟩ := admitted
  have closeT : close (pFor t x A) = pFor (closeIn [frame t] t) (close x) (closeIn [frame t] A) :=
    closeIn_pFor [] t x A
  have closeU : close (pFor u x B) = pFor (closeIn [frame u] u) (close x) (closeIn [frame u] B) :=
    closeIn_pFor [] u x B
  have closeWhole : close (par (pFor t x A) (pFor u x B)) =
      par (pFor (closeIn [frame t] t) (close x) (closeIn [frame t] A))
        (pFor (closeIn [frame u] u) (close x) (closeIn [frame u] B)) := by
    unfold close; rw [closeIn_par]; exact congrArg₂ par closeT closeU
  rw [closeT, closeU]
  obtain ⟨openT, longT⟩ := opened_pattern avoid 0 t calcT freeT
  obtain ⟨openU, longU⟩ := opened_pattern avoid (codeCount (closeIn [frame t] t)) u calcU freeU
  have frameT : frame t = pvars t := frame_of_guardFree t freeT
  have frameU : frame u = pvars u := frame_of_guardFree u freeU
  let L := freshNames avoid 0 (codeCount (closeIn [frame t] t))
  let R := freshNames avoid (codeCount (closeIn [frame t] t)) (codeCount (closeIn [frame u] u))
  let gL := nameOf L (frame t)
  let gR := nameOf R (frame u)
  have injL : ∀ a ∈ pvars t, ∀ b ∈ pvars t, gL a = gL b → a = b := by
    rw [← frameT]; exact nameOf_injOn (freshNames_nodup _ _ _) longT
  have injR : ∀ a ∈ pvars u, ∀ b ∈ pvars u, gR a = gR b → a = b := by
    rw [← frameU]; exact nameOf_injOn (freshNames_nodup _ _ _) longU
  have inL : ∀ a ∈ pvars t, gL a ∈ L := fun a member => nameOf_mem longT (by rw [frameT]; exact member)
  have inR : ∀ b ∈ pvars u, gR b ∈ R := fun b member => nameOf_mem longU (by rw [frameU]; exact member)
  have apartLR : ∀ a ∈ pvars t, ∀ b ∈ pvars u, gL a ≠ gR b := fun a ha b hb same =>
    freshNames_disjoint (inL a ha) (same ▸ inR b hb)
  obtain ⟨σ, found⟩ := unify_opened_exists principal gL gR injL injR apartLR
  have principalσ := unify_principal found
  -- one renaming for both inputs
  let ρ : String → String := fun w => if w ∈ pvars t then gL w else gR w
  have ρt : rename ρ t = rename gL t := rename_congr fun w member => by simp [ρ, member]
  have ρu : rename ρ u = rename gR u := rename_congr fun w member => by
    have : w ∉ pvars t := fun inT => apart.patterns w inT member
    simp [ρ, this]
  have openedPrincipal : Principal (rename ρ t) (rename ρ u) σ := by rw [ρt, ρu]; exact principalσ
  -- σ binds only opened names
  have σKeys : ∀ z, z ∉ L → z ∉ R → σ.lookup z = none := by
    intro z notL notR
    apply lookup_eq_none_of_keys principalσ.keys
    intro member
    rcases List.mem_append.mp member with inT | inU
    · rw [pvars_rename] at inT
      obtain ⟨w, wIn, rfl⟩ := List.mem_map.mp inT
      exact notL (inL w wIn)
    · rw [pvars_rename] at inU
      obtain ⟨w, wIn, rfl⟩ := List.mem_map.mp inU
      exact notR (inR w wIn)
  -- the completed unifier, which the executable dots with
  let S := completeBindings (pvars (openPattern L (closeIn [frame t] t)) ++
    pvars (openPattern R (closeIn [frame u] u))) σ
  have outsideVs : ∀ z, z ∉ L → z ∉ R →
      z ∉ pvars (openPattern L (closeIn [frame t] t)) ++ pvars (openPattern R (closeIn [frame u] u)) := by
    intro z notL notR member
    rw [openT, openU, pvars_rename, pvars_rename] at member
    rcases List.mem_append.mp member with inT | inU
    · obtain ⟨w, wIn, rfl⟩ := List.mem_map.mp inT
      exact notL (inL w wIn)
    · obtain ⟨w, wIn, rfl⟩ := List.mem_map.mp inU
      exact notR (inR w wIn)
  have freshAvoid : ∀ z ∈ pvars (close (par (pFor t x A) (pFor u x B))), z ∉ L ∧ z ∉ R :=
    fun z occurs => ⟨fun h => freshNames_fresh h (fresh z occurs), fun h => freshNames_fresh h (fresh z occurs)⟩
  have inWhole : ∀ z, z ∈ pvars (closeIn [frame t] A) ∨ z ∈ pvars (closeIn [frame u] B) →
      z ∈ pvars (close (par (pFor t x A) (pFor u x B))) := by
    intro z occurs
    rw [closeWhole, pvars_par, pvars_pFor, pvars_pFor]
    rcases occurs with h | h <;> simp [h]
  -- each continuation, dotted after opening, is the closed dotted source continuation
  have bodyA : psubst (dotOf S) (openWith L (closeIn [frame t] A)) = close (applyDot bs A) := by
    rw [applyDot_eq bs A (firstOrder_of_calcTerm A calcA)]
    have := psubst_open_closeIn L (frame t) longT (dotOf bs) (dotOf S) A calcA
      (by rw [frameT]; exact apart.leftKept) [] (by simp)
      (by
        intro v occurs member
        rw [frameT] at member
        obtain ⟨g, lookupV, closedG⟩ := ground v (List.mem_append_left _ member)
          (List.mem_append_left _ occurs)
        refine ⟨nQuote g, by simp [dotOf, lookupV], by rw [pvars_nQuote, closedG], ?_⟩
        have agree := principal_agree principal ρ openedPrincipal lookupV closedG
        have ρv : ρ v = gL v := by simp [ρ, member]
        rw [ρv] at agree
        show (S.lookup (gL v)).map nQuote = some (nQuote g)
        rw [lookup_completeBindings, agree]; rfl)
      (by
        intro v occurs notFrame
        rw [frameT] at notFrame
        have notU : v ∉ pvars u := fun inU => apart.rightOutside v inU occurs
        show (bs.lookup v).map nQuote = none
        rw [lookup_eq_none_of_keys (x := v) principal.keys (by simp [notFrame, notU])]
        rfl)
      (by
        intro z occurs
        have both := freshAvoid z (inWhole z (.inl (by simpa using occurs)))
        simp [dotOf, S, lookup_completeBindings, σKeys z both.1 both.2, outsideVs z both.1 both.2])
    simp only [List.length_nil, List.nil_append] at this
    exact this
  have bodyB : psubst (dotOf S) (openWith R (closeIn [frame u] B)) = close (applyDot bs B) := by
    rw [applyDot_eq bs B (firstOrder_of_calcTerm B calcB)]
    have := psubst_open_closeIn R (frame u) longU (dotOf bs) (dotOf S) B calcB
      (by rw [frameU]; exact apart.rightKept) [] (by simp)
      (by
        intro v occurs member
        rw [frameU] at member
        obtain ⟨g, lookupV, closedG⟩ := ground v (List.mem_append_right _ member)
          (List.mem_append_right _ occurs)
        refine ⟨nQuote g, by simp [dotOf, lookupV], by rw [pvars_nQuote, closedG], ?_⟩
        have agree := principal_agree principal ρ openedPrincipal lookupV closedG
        have notT : v ∉ pvars t := fun inT => apart.patterns v inT member
        have ρv : ρ v = gR v := by simp [ρ, notT]
        rw [ρv] at agree
        show (S.lookup (gR v)).map nQuote = some (nQuote g)
        rw [lookup_completeBindings, agree]; rfl)
      (by
        intro v occurs notFrame
        rw [frameU] at notFrame
        have notT : v ∉ pvars t := fun inT => apart.leftOutside v inT occurs
        show (bs.lookup v).map nQuote = none
        rw [lookup_eq_none_of_keys (x := v) principal.keys (by simp [notFrame, notT])]
        rfl)
      (by
        intro z occurs
        have both := freshAvoid z (inWhole z (.inr (by simpa using occurs)))
        simp [dotOf, S, lookup_completeBindings, σKeys z both.1 both.2, outsideVs z both.1 both.2])
    simp only [List.length_nil, List.nil_append] at this
    exact this
  refine ⟨par (applyDot S (openWith L (closeIn [frame t] A))) (applyDot S (openWith R (closeIn [frame u] B))),
    ?_, ?_⟩
  · have found' : unify (openPattern (freshNames avoid 0 (codeCount (closeIn [frame t] t)))
          (closeIn [frame t] t)) (openPattern (freshNames avoid (codeCount (closeIn [frame t] t))
          (codeCount (closeIn [frame u] u))) (closeIn [frame u] u)) = some σ := by
      rw [openT, openU]; exact found
    simp [commClosed, asGuard_pFor, guardFree_closeIn, freeT, freeU, found']
    rfl
  · have foA : firstOrder (openWith L (closeIn [frame t] A)) = true :=
      firstOrder_instantiateAt _ (fun i v eq => by
        cases h : L[i]? with
        | none => simp [h] at eq
        | some n => simp only [h, Option.map_some, Option.some.injEq] at eq; subst eq; rfl)
        _ (firstOrder_closeIn A calcA _) 0
    have foB : firstOrder (openWith R (closeIn [frame u] B)) = true :=
      firstOrder_instantiateAt _ (fun i v eq => by
        cases h : R[i]? with
        | none => simp [h] at eq
        | some n => simp only [h, Option.map_some, Option.some.injEq] at eq; subst eq; rfl)
        _ (firstOrder_closeIn B calcB _) 0
    have target : par (applyDot S (openWith L (closeIn [frame t] A)))
        (applyDot S (openWith R (closeIn [frame u] B))) = close (par (applyDot bs A) (applyDot bs B)) := by
      rw [applyDot_eq S _ foA, applyDot_eq S _ foB]
      unfold close
      rw [closeIn_par]
      exact congrArg₂ par bodyA bodyB
    unfold AlphaEq
    rw [target, close_close]

/-- **Completeness on the closing fragment.** Every relational step whose COMM
instances are closing is matched, up to alpha, by a step of the closed form,
for any avoidance list containing its free names. -/
theorem stepClosed_complete {P Q : Pattern} (step : Step closing P Q) :
    ∀ avoid : List String, (∀ z ∈ pvars (close P), z ∈ avoid) →
      ∃ Q' ∈ stepClosed avoid (close P), AlphaEq Q' Q := by
  induction step with
  | comm t u x A B bs principal admitted =>
      intro avoid fresh
      obtain ⟨Q', member, alpha⟩ := commClosed_complete avoid t u x A B bs principal admitted fresh
      refine ⟨Q', ?_, alpha⟩
      unfold close
      rw [closeIn_par, stepClosed_par]
      exact List.mem_append_left _ member
  | parallel R _ ih =>
      intro avoid fresh
      obtain ⟨Q₁, member, alpha⟩ := ih avoid fun z occurs => fresh z (by
        unfold close; rw [closeIn_par, pvars_par]; exact List.mem_append_left _ occurs)
      refine ⟨par Q₁ (close R), ?_, AlphaEq.par alpha (alphaEq_close R)⟩
      unfold close at member ⊢
      rw [closeIn_par, stepClosed_par]
      exact List.mem_append_right _ (List.mem_map_of_mem member)
  | congruence before _ after ih =>
      intro avoid fresh
      have same : close _ = close _ := before
      obtain ⟨Q₁, member, alpha⟩ := ih avoid (by rw [← same]; exact fresh)
      exact ⟨Q₁, by rw [same]; exact member, alpha.trans after⟩
  | reflect x _ ih =>
      intro avoid fresh
      obtain ⟨Q₁, member, alpha⟩ := ih avoid fun z occurs => fresh z (by
        unfold close; rw [closeIn_pReflect, pvars_pReflect]; exact List.mem_append_right _ occurs)
      refine ⟨pFor (tProc Q₁) (close x) pZero, ?_, alphaEq_listener alpha (alphaEq_close x)⟩
      unfold close at member ⊢
      rw [closeIn_pReflect, stepClosed_reflect]
      exact List.mem_map_of_mem member

/-- **Completeness of the corrected executable step** on the closing fragment. -/
theorem cstep_complete {P Q : Pattern} (step : Step closing P Q) : ∃ Q' ∈ cstep P, AlphaEq Q' Q :=
  stepClosed_complete step (pvars (close P)) fun _ occurs => occurs

/-- Soundness and completeness together: on the closing fragment the corrected
step computes, up to alpha, exactly the relational reducts. -/
theorem cstep_adequate {P Q : Pattern} (inCalc : calcTerm P = true) :
    (Step closing P Q → ∃ Q' ∈ cstep P, AlphaEq Q' Q) ∧
      ((∃ Q' ∈ cstep P, AlphaEq Q' Q) → Step conventional P Q) :=
  ⟨cstep_complete, fun ⟨_, member, alpha⟩ =>
    Step.congruence (AlphaEq.refl P) (cstep_sound inCalc member) alpha⟩

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected
