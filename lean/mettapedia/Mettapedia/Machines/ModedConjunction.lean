import Mettapedia.Machines.ConjunctionOrder

/-!
# Reordering a conjunction whose legs need their inputs

A planner runs the legs of a conjunction in an order of its choosing.
`ConjunctionOrder` proves that every order gives the same bag when any two
legs commute everywhere.  Legs that need inputs do not: a leg that reads a
space named by a variable, computes a value from bound variables, tests a
guard, or asks that no row match (an anti-join) can run only once its inputs
are bound, and before that it asks something else.

A moded leg runs from a state to a bag of states and is enabled on some
states.  Two properties suffice:

* running a leg keeps every enabled leg enabled (`Monotone`): legs only add
  bindings;
* two legs commute on every state where both are enabled
  (`CommuteWhenEnabled`).

Then every order in which each leg is enabled when it runs (`Executable`)
gives the same bag (`chain_perm`).  Legs always enabled and commuting
everywhere are `ConjunctionOrder`'s case (`conj_eq_chain`,
`commuteWhenEnabled_ofConj`).

* A guard keeps a state when a test holds.  Once enabled, its verdict does not
  change as other legs bind more, so it commutes with them
  (`guard_commute`).  An if-guard and a negated match over a snapshot are
  guards.
* A computed leg binds a variable to a function of bound inputs, or checks it
  when bound: a let-bound pure value between nested matches.  It commutes
  with a leg that its binding commutes with and that does not change its
  inputs (`computed_commute`).

**Values in bindings.**  A flat leg binds a variable or checks it against
the value bound before, with the matcher's equality of values
(`bindOrCheck`).  With equality decided by identity, two such legs commute
(`bindOrCheck_comm`), so a join may compare ids in any order.  Matching modulo
the kernel of a canonical form is matching canonical forms by identity
(`bindOrCheck_canon`): a join may compare canonical ids, provided each answer
takes the value the source order binds first.

Controls: an anti-join run before the leg that binds its variable asks
whether any row matches at all, and answers differently
(`Controls.antijoin_too_early`); a leg reading a space named by an unbound
variable reads nothing (`Controls.space_unbound`); an equality coarser than
identity binds a different representative in another order
(`Controls.representative_order`); a reflexive, symmetric, intransitive
equality changes the verdict with the order (`Controls.intransitive_order`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ModedConjunction

universe u
variable {S : Type u}

/-! ## Moded legs -/

/-- A leg of a conjunction: the bag of states it extends a state to, and the
states on which it may run. -/
structure Leg (S : Type u) where
  run : S → Multiset S
  enabled : S → Prop

/-- The legs, run in order. -/
def chain : List (Leg S) → S → Multiset S
  | [], s => {s}
  | leg :: legs, s => (leg.run s).bind (chain legs)

/-- Each leg is enabled when it runs. -/
def Executable : List (Leg S) → S → Prop
  | [], _ => True
  | leg :: legs, s => leg.enabled s ∧ ∀ t ∈ leg.run s, Executable legs t

/-- Running any of the legs keeps every one of them enabled that was. -/
def Monotone (legs : List (Leg S)) : Prop :=
  ∀ a ∈ legs, ∀ b ∈ legs, ∀ s, a.enabled s → ∀ t ∈ b.run s, a.enabled t

/-- Two legs commute wherever both are enabled. -/
def CommuteWhenEnabled (a b : Leg S) : Prop :=
  ∀ s, a.enabled s → b.enabled s → (a.run s).bind b.run = (b.run s).bind a.run

theorem bind_singleton_self {α : Type*} (m : Multiset α) : m.bind (fun t => {t}) = m := by
  have h := Multiset.bind_singleton (s := m) (fun t => t)
  simpa using h

theorem Monotone.of_subset {legs small : List (Leg S)} (mono : Monotone legs)
    (sub : ∀ x ∈ small, x ∈ legs) : Monotone small :=
  fun a ha b hb s h t ht => mono a (sub a ha) b (sub b hb) s h t ht

/-- An enabled leg moves to the front of an executable order without changing
the bag, and the moved order is executable. -/
theorem chain_move (a : Leg S) (post : List (Leg S)) :
    ∀ (pre : List (Leg S)) (s : S),
      Monotone (pre ++ a :: post) →
      (∀ x ∈ pre ++ a :: post, ∀ y ∈ pre ++ a :: post, CommuteWhenEnabled x y) →
      Executable (pre ++ a :: post) s → a.enabled s →
      chain (pre ++ a :: post) s = chain (a :: (pre ++ post)) s ∧
        Executable (a :: (pre ++ post)) s
  | [], _, _, _, ex, _ => ⟨rfl, ex⟩
  | b :: pre, s, mono, comm, ex, ha => by
      simp only [List.cons_append, Executable] at ex
      obtain ⟨hb, hrest⟩ := ex
      have sub : ∀ x ∈ pre ++ a :: post, x ∈ b :: (pre ++ a :: post) :=
        fun x hx => List.mem_cons_of_mem _ hx
      have aMem : a ∈ b :: (pre ++ a :: post) :=
        List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
      have bMem : b ∈ b :: (pre ++ a :: post) := List.mem_cons_self
      have mono' : Monotone (b :: (pre ++ a :: post)) := by
        simpa only [List.cons_append] using mono
      have comm' : ∀ x ∈ b :: (pre ++ a :: post), ∀ y ∈ b :: (pre ++ a :: post),
          CommuteWhenEnabled x y := by
        simpa only [List.cons_append] using comm
      have ih : ∀ t ∈ b.run s,
          chain (pre ++ a :: post) t = chain (a :: (pre ++ post)) t ∧
            Executable (a :: (pre ++ post)) t :=
        fun t ht => chain_move a post pre t (mono'.of_subset sub)
          (fun x hx y hy => comm' x (sub x hx) y (sub y hy)) (hrest t ht)
          (mono' a aMem b bMem s ha t ht)
      have swap := comm' b bMem a aMem s hb ha
      constructor
      · simp only [List.cons_append, chain]
        rw [Multiset.bind_congr fun t ht => (ih t ht).1]
        simp only [chain]
        rw [← Multiset.bind_assoc, swap, Multiset.bind_assoc]
      · simp only [List.cons_append, Executable]
        refine ⟨ha, fun t ht => ⟨mono' b bMem a aMem s hb t ht, fun w hw => ?_⟩⟩
        have hw' : w ∈ (a.run s).bind b.run := Multiset.mem_bind.mpr ⟨t, ht, hw⟩
        rw [← swap] at hw'
        obtain ⟨t', ht', hw''⟩ := Multiset.mem_bind.mp hw'
        exact ((ih t' ht').2.2 w hw'')

/-- **Every executable order gives the same bag**, when running a leg keeps
legs enabled and legs commute wherever both are enabled. -/
theorem chain_perm {legs legs' : List (Leg S)} (perm : legs.Perm legs')
    (mono : Monotone legs) (comm : ∀ x ∈ legs, ∀ y ∈ legs, CommuteWhenEnabled x y)
    {s : S} (ex : Executable legs s) (ex' : Executable legs' s) :
    chain legs s = chain legs' s := by
  induction legs' generalizing legs s with
  | nil => rw [List.perm_nil.mp perm]
  | cons a rest ih =>
      simp only [Executable] at ex'
      obtain ⟨ha, hrest⟩ := ex'
      obtain ⟨pre, post, rfl⟩ := List.append_of_mem (perm.symm.subset List.mem_cons_self)
      obtain ⟨moved, exMoved⟩ := chain_move a post pre s mono comm ex ha
      rw [moved]
      have permRest : (pre ++ post).Perm rest := (List.perm_middle.symm.trans perm).cons_inv
      have sub : ∀ x ∈ pre ++ post, x ∈ pre ++ a :: post := fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append_left _ hx
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)
      simp only [Executable] at exMoved
      simp only [chain]
      exact Multiset.bind_congr fun t ht =>
        ih permRest (mono.of_subset sub) (fun x hx y hy => comm x (sub x hx) y (sub y hy))
          (exMoved.2 t ht) (hrest t ht)

/-! ### Legs always enabled -/

/-- A leg of `ConjunctionOrder`, always enabled. -/
def ofConj {R : Type*} (leg : ConjunctionOrder.Leg S R) : Leg S where
  run := leg.run
  enabled _ := True

theorem conj_eq_chain {R : Type*} :
    ∀ (legs : List (ConjunctionOrder.Leg S R)) (s : S),
      ConjunctionOrder.conj legs s = chain (legs.map ofConj) s
  | [], _ => rfl
  | leg :: legs, s => by
      simp only [ConjunctionOrder.conj, List.map_cons, chain, ofConj]
      exact Multiset.bind_congr fun t _ => conj_eq_chain legs t

/-- `ConjunctionOrder`'s commuting legs commute wherever they are enabled. -/
theorem commuteWhenEnabled_ofConj {R : Type*} {a b : ConjunctionOrder.Leg S R}
    (commute : ConjunctionOrder.Commute a b) : CommuteWhenEnabled (ofConj a) (ofConj b) := by
  intro s _ _
  have h := ConjunctionOrder.run_bind_run_comm a b commute (fun t => {t}) s
  simpa [ofConj, bind_singleton_self] using h

theorem executable_ofConj {R : Type*} :
    ∀ (legs : List (ConjunctionOrder.Leg S R)) (s : S), Executable (legs.map ofConj) s
  | [], _ => trivial
  | _ :: legs, _ => ⟨trivial, fun t _ => executable_ofConj legs t⟩

/-! ### Guards and computed values -/

/-- A guard: keeps a state when the test holds. -/
def guard (test : S → Prop) [DecidablePred test] (enabled : S → Prop) : Leg S where
  run s := if test s then {s} else 0
  enabled := enabled

/-- **A guard commutes with a leg that cannot change its verdict.** -/
theorem guard_commute (test : S → Prop) [DecidablePred test] (enabled : S → Prop) (b : Leg S)
    (stable : ∀ s, enabled s → ∀ t ∈ b.run s, (test t ↔ test s)) :
    CommuteWhenEnabled (guard test enabled) b := by
  intro s hs _
  by_cases h : test s
  · simp only [guard, h, if_true, Multiset.singleton_bind]
    calc b.run s = (b.run s).bind (fun t => {t}) := (bind_singleton_self _).symm
      _ = (b.run s).bind (fun t => if test t then {t} else 0) :=
        Multiset.bind_congr fun t ht => by rw [if_pos ((stable s hs t ht).mpr h)]
  · simp only [guard, h, if_false, Multiset.zero_bind]
    calc (0 : Multiset S) = (b.run s).bind (fun _ => 0) := by rw [Multiset.bind_zero]
      _ = (b.run s).bind (fun t => if test t then {t} else 0) :=
        Multiset.bind_congr fun t ht => by
          rw [if_neg fun ht' => h ((stable s hs t ht).mp ht')]

/-- A leg that runs `extend` with a value computed from the state. -/
def computed (extend : S → Leg S) (enabled : S → Prop) : Leg S where
  run s := (extend s).run s
  enabled := enabled

/-- **A computed leg commutes with a leg that commutes with each of its
extensions and does not change the computed value.** -/
theorem computed_commute (extend : S → Leg S) (enabled : S → Prop) (b : Leg S)
    (commutes : ∀ s, enabled s → b.enabled s →
      ((extend s).run s).bind b.run = (b.run s).bind (extend s).run)
    (stable : ∀ s, enabled s → ∀ t ∈ b.run s, extend t = extend s) :
    CommuteWhenEnabled (computed extend enabled) b := by
  intro s hs hb
  simp only [computed]
  rw [commutes s hs hb]
  exact Multiset.bind_congr fun t ht => by rw [stable s hs t ht]

/-! ## Values in bindings -/

section Values

variable {V W : Type*} [DecidableEq V]

/-- Bind `v` to `w` when it is unbound; when it is bound, keep the state
exactly when the matcher's equality `same` accepts the bound value and `w`. -/
def bindOrCheck (same : W → W → Bool) (v : V) (w : W) (s : V → Option W) :
    Option (V → Option W) :=
  match s v with
  | none => some (Function.update s v (some w))
  | some bound => if same bound w then some s else none

/-- Identity on values, decided. -/
def identical [DecidableEq W] (a b : W) : Bool := decide (a = b)

theorem bindOrCheck_identical [DecidableEq W] (v : V) (w : W) (s : V → Option W) :
    bindOrCheck identical v w s =
      if s v = none ∨ s v = some w then some (Function.update s v (some w)) else none := by
  unfold bindOrCheck identical
  cases hs : s v with
  | none => simp
  | some bound =>
      by_cases e : bound = w
      · subst e
        simp only [decide_true, if_true, reduceCtorEq, false_or]
        rw [← hs, Function.update_eq_self]
      · simp [e]

/-- **With identity, binding legs commute**: in either order the state binds
both variables, or both orders fail. -/
theorem bindOrCheck_comm [DecidableEq W] (v v' : V) (w w' : W) (s : V → Option W) :
    (bindOrCheck identical v w s).bind (bindOrCheck identical v' w') =
      (bindOrCheck identical v' w' s).bind (bindOrCheck identical v w) := by
  simp only [bindOrCheck_identical]
  by_cases same : v = v'
  · subst same
    by_cases e : w = w'
    · subst e
      split_ifs <;> simp_all
    · have e' : w' ≠ w := Ne.symm e
      split_ifs <;> simp_all [Function.update_self]
  · have keep : ∀ (t : V → Option W) (x : V) (y : W) (z : V), z ≠ x →
        Function.update t x (some y) z = t z := fun t x y z ne => Function.update_of_ne ne _ _
    split_ifs <;> simp_all [Function.update_comm same, keep _ _ _ _ (Ne.symm same)]

/-- **Matching modulo a canonical form is matching canonical forms by
identity**: the verdict and the canonical bindings are the same. -/
theorem bindOrCheck_canon {W' : Type*} [DecidableEq W'] (canon : W → W') (v : V) (w : W)
    (s : V → Option W) :
    (bindOrCheck (fun a b => identical (canon a) (canon b)) v w s).map
        (fun t => Option.map canon ∘ t) =
      bindOrCheck identical v (canon w) (Option.map canon ∘ s) := by
  unfold bindOrCheck
  cases hs : s v with
  | none =>
      simp only [Option.map_some, Function.comp_apply, hs, Option.map_none]
      rw [Function.comp_update]
      rfl
  | some bound =>
      simp only [Function.comp_apply, hs, Option.map_some]
      by_cases e : identical (canon bound) (canon w) = true
      · simp [e]
      · simp [e]

/-- A leg binding or checking one variable against one value. -/
def oneLeg (same : W → W → Bool) (v : V) (w : W) : Leg (V → Option W) where
  run s := ConjunctionOrder.optionMs (bindOrCheck same v w s)
  enabled _ := True

/-- **Legs binding values by identity commute**, so they give one bag in
every order. -/
theorem oneLeg_commute [DecidableEq W] (v v' : V) (w w' : W) :
    CommuteWhenEnabled (oneLeg identical v w) (oneLeg identical v' w') := by
  intro s _ _
  have left := ConjunctionOrder.optionMs_bind_bind (bindOrCheck identical v w s)
    (bindOrCheck identical v' w') (fun t => {t})
  have right := ConjunctionOrder.optionMs_bind_bind (bindOrCheck identical v' w' s)
    (bindOrCheck identical v w) (fun t => {t})
  simp only [bind_singleton_self] at left right
  simp only [oneLeg]
  rw [left, right, bindOrCheck_comm v v' w w' s]

end Values

/-! ## Controls -/

namespace Controls

/-- The state binds one variable, `x`. -/
abbrev X := Option ℕ

/-- `(p $x)` over the rows `(p 1)` and `(p 2)`. -/
def pLeg : Leg X where
  run
    | none => {some 1, some 2}
    | some v => if v = 1 ∨ v = 2 then {some v} else 0
  enabled _ := True

/-- `(== (collapse (match S (q $x) ())) ())` over the row `(q 1)`: with `x`
bound, that `x` is not 1; with `x` unbound, that no row matches `(q $x)` at
all, which fails. -/
def notQ : Leg X where
  run
    | none => 0
    | some v => if v = 1 then 0 else {some v}
  enabled s := s.isSome

/-- **An anti-join before the leg binding its variable answers
differently.** -/
theorem antijoin_too_early :
    chain [pLeg, notQ] none = {some 2} ∧ chain [notQ, pLeg] none = 0 ∧
      Executable [pLeg, notQ] none ∧ ¬ Executable [notQ, pLeg] none := by
  refine ⟨by decide, by decide, ⟨trivial, fun t ht => ?_⟩,
    fun h => by simp [Executable, notQ] at h⟩
  simp only [pLeg, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ht
  rcases ht with rfl | rfl <;> exact ⟨rfl, fun _ _ => trivial⟩

/-- States `(space, value)`: `(sp $s)` binds the space, `(match $s (v $y) ...)`
reads it. -/
abbrev SV := Option ℕ × Option ℕ

/-- `(sp $s)` over the rows naming spaces 3 and 4. -/
def spLeg : Leg SV where
  run s := if s.1 = none then {(some 3, s.2), (some 4, s.2)} else {s}
  enabled _ := True

/-- `(match $s (v $y) ...)`: space 3 holds `(v 30)`, space 4 holds `(v 40)`;
with no space bound there is nothing to read. -/
def readLeg : Leg SV where
  run
    | (some k, none) => {(some k, some (10 * k))}
    | _ => 0
  enabled s := s.1.isSome

/-- **A leg reading a space named by an unbound variable reads nothing.** -/
theorem space_unbound :
    chain [spLeg, readLeg] (none, none) = {(some 3, some 30), (some 4, some 40)} ∧
      chain [readLeg, spLeg] (none, none) = 0 := by
  decide

/-- An equality of values coarser than identity: equal halves. -/
def halves (a b : ℕ) : Bool := identical (a / 2) (b / 2)

/-- **An equality coarser than identity binds a different representative in
another order**: 4 and 5 are equal halves, and the first leg's value is
kept. -/
theorem representative_order :
    ((bindOrCheck halves () 4 (fun _ => none)).bind (bindOrCheck halves () 5)).map (· ()) =
        some (some 4) ∧
      ((bindOrCheck halves () 5 (fun _ => none)).bind (bindOrCheck halves () 4)).map (· ()) =
        some (some 5) := by
  decide

/-- Reflexive, symmetric, intransitive: equal or adjacent. -/
def near (a b : ℕ) : Bool := a == b || a + 1 == b || b + 1 == a

/-- **An intransitive equality changes the verdict with the order**: bound
to 2, both 1 and 3 are near; bound to 1, 3 is not. -/
theorem intransitive_order :
    (((bindOrCheck near () 2 (fun _ => none)).bind (bindOrCheck near () 1)).bind
        (bindOrCheck near () 3)).isSome = true ∧
      (((bindOrCheck near () 1 (fun _ => none)).bind (bindOrCheck near () 3)).bind
        (bindOrCheck near () 2)).isSome = false := by
  decide

end Controls

end Mettapedia.Machines.ModedConjunction
