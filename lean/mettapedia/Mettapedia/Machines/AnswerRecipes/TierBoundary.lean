import Mettapedia.Machines.AnswerRecipes.Recipes

/-!
# The compiled tier's boundary: one cell per identity, kinds by provenance, exports by kind

A compiled tier imports terms by three routes (the call's arguments, a host goal's
answers, a stored value it reads) and exports its own answers and the arguments it passes
to host goals.  An import gives each variable a cell; an export spells each unbound cell.
This is the abstraction and instantiation of `Recipes`, run inside one cursor.

**Kinds.**  What an arrival knows of a variable: that it is the caller's (`caller`), an
identity held outside the answer that brings it (`retained`: a stored value's variable, a
sealed payload's), or that answer's own (`own`: a replay's fresh variables, a host goal's
new ones).  Knowledge only grows: `Kind.join` is commutative, associative and idempotent,
with `own` its unit, so the kind of an identity is the join of its arrivals.

**The import.**  `enter` keeps one entry per identity: a known identity keeps its cell and
joins what the new arrival knows; a new identity gets the next cell.  This file proves:
* `kindOf_importAll_perm`: the kinds after a sequence of arrivals do not depend on their
  order;
* `kindOf_importAll_own_iff`: an identity is answer-local exactly when every one of its
  arrivals says so;
* `cellOf_injective`: one cell per identity, whatever the route: two variables share a
  cell only when they are one identity.

**The export.**  `exportTerm` spells caller and retained cells by their identities, and
each answer-local cell by the export's own fresh variable for that cell:
* `exportTerm_localVariant`: an export is a local variant of the term it spells, the kept
  identities fixed: aliasing is kept and none is created;
* `exportTerm_own_vars`: every answer-local variable of an export is the export's own, so
  no producer's variable escapes as an identity;
* `exports_disjoint`: two exports with disjoint supplies share only kept identities;
* `collectTerm_localVariant`: a collection's copy freshens every cell, the full renaming
  `collapse` makes of each answer.

**The tier's current shapes against this contract**, each with its failure:
* a known identity that keeps what its first arrival said depends on arrival order
  (`enterFirst_order_dependent`);
* a stored-value route that does not consult the call's cells gives one identity two
  cells (`split_cells`);
* answer-local for every host arrival exports a retained identity fresh
  (`hostOwn_loses_retained`);
* retained for every host arrival exports the producer's variable, the same in every
  export (`hostRetained_shares`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AnswerRecipes.TierBoundary

open Mettapedia.Machines.AnswerRecipes Tm

/-- What an arrival knows of a variable. -/
inductive Kind
  /-- The answer that brings it introduced it. -/
  | own
  /-- An identity held outside the answer that brings it. -/
  | retained
  /-- The caller's own variable. -/
  | caller
  deriving DecidableEq

/-- Knowledge only grows: retained beats answer-local, the caller's beats both. -/
def Kind.join : Kind → Kind → Kind
  | .caller, _ => .caller
  | _, .caller => .caller
  | .retained, _ => .retained
  | _, .retained => .retained
  | .own, .own => .own

theorem Kind.join_comm (a b : Kind) : a.join b = b.join a := by
  cases a <;> cases b <;> rfl

theorem Kind.join_assoc (a b c : Kind) : (a.join b).join c = a.join (b.join c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem Kind.join_self (a : Kind) : a.join a = a := by cases a <;> rfl

theorem Kind.own_join (a : Kind) : Kind.own.join a = a := by cases a <;> rfl

theorem Kind.join_eq_own {a b : Kind} : a.join b = .own ↔ a = .own ∧ b = .own := by
  cases a <;> cases b <;> simp [Kind.join]

variable {V : Type} [DecidableEq V]

/-- The tier's cells: one entry per identity with what is known of it; an entry's position
is its cell. -/
abbrev Table (V : Type) := List (V × Kind)

/-- An arrival: a known identity keeps its cell and joins what the arrival knows; a new
identity gets the next cell. -/
def enter : Table V → V → Kind → Table V
  | [], v, k => [(v, k)]
  | (w, k') :: t, v, k => if w = v then (w, k'.join k) :: t else (w, k') :: enter t v k

/-- What the table knows of an identity. -/
def kindOf : Table V → V → Option Kind
  | [], _ => none
  | (w, k) :: t, v => if w = v then some k else kindOf t v

/-- The cell of an identity. -/
def cellOf : Table V → V → Option ℕ
  | [], _ => none
  | (w, _) :: t, v => if w = v then some 0 else (cellOf t v).map (· + 1)

/-- Join an arrival into what is known. -/
def joinOpt : Option Kind → Kind → Kind
  | none, k => k
  | some k', k => k'.join k

/-- What an arrival changes in the knowledge of every identity. -/
def learn (f : V → Option Kind) (a : V × Kind) : V → Option Kind :=
  fun w => if a.1 = w then some (joinOpt (f w) a.2) else f w

theorem kindOf_enter (t : Table V) (v : V) (k : Kind) :
    kindOf (enter t v k) = learn (kindOf t) (v, k) := by
  funext w
  induction t with
  | nil =>
    by_cases hw : v = w
    · subst hw; simp [enter, kindOf, learn, joinOpt]
    · simp [enter, kindOf, learn, hw]
  | cons e t ih =>
    obtain ⟨u, k'⟩ := e
    by_cases hu : u = v
    · subst hu
      by_cases hw : u = w
      · subst hw; simp [enter, kindOf, learn, joinOpt]
      · simp [enter, kindOf, learn, hw]
    · by_cases hw : u = w
      · subst hw
        have hv : v ≠ u := fun h => hu h.symm
        simp [enter, kindOf, learn, hu, hv]
      · simp only [enter, hu, if_false, kindOf, hw, ih]
        simp [learn, hw]

/-- Arrivals, one after another. -/
def importAll (t : Table V) (as : List (V × Kind)) : Table V :=
  as.foldl (fun t a => enter t a.1 a.2) t

theorem kindOf_importAll (t : Table V) (as : List (V × Kind)) :
    kindOf (importAll t as) = as.foldl learn (kindOf t) := by
  induction as generalizing t with
  | nil => rfl
  | cons a as ih =>
    simp only [importAll, List.foldl_cons] at ih ⊢
    rw [ih, kindOf_enter]

omit [DecidableEq V] in
theorem joinOpt_comm (o : Option Kind) (a b : Kind) :
    joinOpt (some (joinOpt o a)) b = joinOpt (some (joinOpt o b)) a := by
  cases o with
  | none => exact Kind.join_comm a b
  | some k =>
    simp only [joinOpt]
    rw [Kind.join_assoc, Kind.join_comm a b, ← Kind.join_assoc]

theorem learn_comm (f : V → Option Kind) (x y : V × Kind) :
    learn (learn f x) y = learn (learn f y) x := by
  funext w
  simp only [learn]
  by_cases hx : x.1 = w <;> by_cases hy : y.1 = w <;> simp [hx, hy, joinOpt_comm]

/-- **Order independence.**  The kinds after a sequence of arrivals do not depend on their
order. -/
theorem kindOf_importAll_perm (t : Table V) {as bs : List (V × Kind)} (h : as.Perm bs) :
    kindOf (importAll t as) = kindOf (importAll t bs) := by
  rw [kindOf_importAll, kindOf_importAll]
  exact h.foldl_eq' (fun x _ y _ f => learn_comm f x y) _

/-- The arrivals of one identity, in order. -/
def arrivalsOf (v : V) (as : List (V × Kind)) : List Kind :=
  as.filterMap fun a => if a.1 = v then some a.2 else none

theorem mem_arrivalsOf {v : V} {as : List (V × Kind)} {k : Kind} :
    k ∈ arrivalsOf v as ↔ (v, k) ∈ as := by
  simp only [arrivalsOf, List.mem_filterMap]
  constructor
  · rintro ⟨⟨u, k'⟩, hmem, he⟩
    by_cases hu : u = v
    · simp only [hu, if_true, Option.some.injEq] at he
      subst hu; subst he; exact hmem
    · simp [hu] at he
  · intro h
    exact ⟨(v, k), h, by simp⟩

/-- Joining a sequence of arrivals into what is known. -/
def joins : Option Kind → List Kind → Option Kind
  | o, [] => o
  | o, k :: ks => joins (some (joinOpt o k)) ks

theorem foldl_learn_apply (v : V) :
    ∀ (as : List (V × Kind)) (f : V → Option Kind),
      as.foldl learn f v = joins (f v) (arrivalsOf v as)
  | [], _ => rfl
  | a :: as, f => by
    rw [List.foldl_cons, foldl_learn_apply v as (learn f a)]
    obtain ⟨u, k⟩ := a
    by_cases hu : u = v
    · subst hu
      simp [arrivalsOf, learn, joins]
    · simp [arrivalsOf, learn, hu]

omit [DecidableEq V] in
theorem joins_eq_own : ∀ (o : Option Kind) (ks : List Kind),
    joins o ks = some .own ↔ (o = some .own ∨ (o = none ∧ ks ≠ [])) ∧ ∀ k ∈ ks, k = .own
  | o, [] => by cases o <;> simp [joins]
  | o, k :: ks => by
    rw [joins, joins_eq_own]
    cases o with
    | none =>
      simp only [joinOpt, Option.some.injEq, reduceCtorEq, false_and, or_false,
        List.mem_cons, forall_eq_or_imp, ne_eq, not_false_eq_true, and_true]
      tauto
    | some k₀ =>
      simp only [joinOpt, Option.some.injEq, Kind.join_eq_own, reduceCtorEq, false_and,
        or_false, List.mem_cons, forall_eq_or_imp]
      tauto

/-- **Answer-local only by consensus.**  From an empty table, an identity is answer-local
exactly when it arrived and every one of its arrivals says so: one arrival that knows it
as retained or the caller's keeps it. -/
theorem kindOf_importAll_own_iff (as : List (V × Kind)) (v : V) :
    kindOf (importAll [] as) v = some .own ↔
      (∃ k, (v, k) ∈ as) ∧ ∀ k, (v, k) ∈ as → k = .own := by
  rw [kindOf_importAll, foldl_learn_apply, joins_eq_own]
  simp only [kindOf, reduceCtorEq, false_or, true_and]
  constructor
  · rintro ⟨hne, hall⟩
    obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨⟨k, mem_arrivalsOf.mp hk⟩, fun k' hk' => hall k' (mem_arrivalsOf.mpr hk')⟩
  · rintro ⟨⟨k, hk⟩, hall⟩
    exact ⟨List.ne_nil_of_mem (mem_arrivalsOf.mpr hk),
      fun k' hk' => hall k' (mem_arrivalsOf.mp hk')⟩

theorem cellOf_cons (u : V) (k : Kind) (t : Table V) (v : V) :
    cellOf ((u, k) :: t) v = if u = v then some 0 else (cellOf t v).map (· + 1) := rfl

/-- **One cell per identity.**  Two variables share a cell only when they are one
identity. -/
theorem cellOf_injective : ∀ (t : Table V) {v w : V} {i : ℕ},
    cellOf t v = some i → cellOf t w = some i → v = w
  | [], _, _, _, hv, _ => by simp [cellOf] at hv
  | (u, k) :: t, v, w, i, hv, hw => by
    rw [cellOf_cons] at hv hw
    by_cases hu : u = v <;> by_cases hu' : u = w
    · exact hu.symm.trans hu'
    · rw [if_pos hu] at hv
      rw [if_neg hu'] at hw
      obtain ⟨j, -, hj⟩ := Option.map_eq_some_iff.mp hw
      have := Option.some.inj hv
      omega
    · rw [if_neg hu] at hv
      rw [if_pos hu'] at hw
      obtain ⟨j, -, hj⟩ := Option.map_eq_some_iff.mp hv
      have := Option.some.inj hw
      omega
    · rw [if_neg hu] at hv
      rw [if_neg hu'] at hw
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hv
      obtain ⟨j', hj', hjj⟩ := Option.map_eq_some_iff.mp hw
      have : j' = j := by omega
      subst this
      exact cellOf_injective t hj hj'

theorem cellOf_enter_self (t : Table V) (v : V) (k : Kind) :
    (cellOf (enter t v k) v).isSome := by
  induction t with
  | nil => simp [enter, cellOf]
  | cons e t ih =>
    obtain ⟨u, k'⟩ := e
    by_cases hu : u = v
    · simp [enter, cellOf, hu]
    · simp only [enter, hu, if_false, cellOf, Option.isSome_map]
      exact ih

/-! ## Exports -/

/-- How an export spells a variable: an answer-local identity by the export's fresh
variable for its cell, any other identity as itself. -/
def spell (kind : V → Kind) (cell : V → ℕ) (ψ : ℕ → V) (v : V) : V :=
  if kind v = .own then ψ (cell v) else v

/-- An export of a term. -/
def exportTerm (kind : V → Kind) (cell : V → ℕ) (ψ : ℕ → V) (t : Tm V) : Tm V :=
  t.map (spell kind cell ψ)

/-- The identities an export keeps. -/
def Kept (kind : V → Kind) (v : V) : Prop := kind v ≠ .own

omit [DecidableEq V] in
theorem spell_own {kind : V → Kind} {cell : V → ℕ} {ψ : ℕ → V} {v : V} (h : kind v = .own) :
    spell kind cell ψ v = ψ (cell v) := by
  simp [spell, h]

omit [DecidableEq V] in
theorem spell_kept {kind : V → Kind} {cell : V → ℕ} {ψ : ℕ → V} {v : V} (h : kind v ≠ .own) :
    spell kind cell ψ v = v := by
  simp [spell, h]

omit [DecidableEq V] in
/-- **Exports are local variants.**  With one cell per answer-local identity, an injective
supply and supply variables the tier does not keep, an export renames only the
answer-local identities, injectively: aliasing is kept and none is created. -/
theorem exportTerm_localVariant (kind : V → Kind) (cell : V → ℕ) (ψ : ℕ → V) (t : Tm V)
    (hcell : Set.InjOn cell {v | v ∈ t.vars ∧ kind v = .own})
    (hψ : Function.Injective ψ) (hfresh : ∀ n, kind (ψ n) = .own) :
    LocalVariant (Kept kind) t (exportTerm kind cell ψ t) := by
  refine ⟨spell kind cell ψ, ?_, ?_, ?_, rfl⟩
  · intro v hv w hw he
    by_cases hkv : kind v = .own <;> by_cases hkw : kind w = .own
    · rw [spell_own hkv, spell_own hkw] at he
      exact hcell ⟨hv, hkv⟩ ⟨hw, hkw⟩ (hψ he)
    · rw [spell_own hkv, spell_kept hkw] at he
      exact absurd (he ▸ hfresh (cell v)) hkw
    · rw [spell_kept hkv, spell_own hkw] at he
      exact absurd (he.symm ▸ hfresh (cell w)) hkv
    · rw [spell_kept hkv, spell_kept hkw] at he
      exact he
  · intro v _ hk
    exact spell_kept hk
  · intro v _ hk
    have hown : kind v = .own := not_not.mp hk
    rw [spell_own hown]
    exact fun h => h (hfresh _)

omit [DecidableEq V] in
/-- Every answer-local variable of an export is one of the export's own supply. -/
theorem exportTerm_own_vars (kind : V → Kind) (cell : V → ℕ) (ψ : ℕ → V) (t : Tm V)
    (x : V) (hx : x ∈ (exportTerm kind cell ψ t).vars) (hown : kind x = .own) :
    ∃ n, ψ n = x := by
  obtain ⟨v, -, rfl⟩ := mem_vars_map.mp hx
  by_cases hkv : kind v = .own
  · exact ⟨cell v, (spell_own hkv).symm⟩
  · rw [spell_kept hkv] at hown
    exact absurd hown hkv

omit [DecidableEq V] in
/-- Two exports with disjoint supplies share only kept identities. -/
theorem exports_disjoint (kind : V → Kind) (cell : V → ℕ) (ψ₁ ψ₂ : ℕ → V)
    (hfresh₁ : ∀ n, kind (ψ₁ n) = .own) (hdisj : ∀ m n, ψ₁ m ≠ ψ₂ n) (t t' : Tm V) (x : V)
    (h₁ : x ∈ (exportTerm kind cell ψ₁ t).vars) (h₂ : x ∈ (exportTerm kind cell ψ₂ t').vars) :
    Kept kind x := by
  obtain ⟨v, -, rfl⟩ := mem_vars_map.mp h₁
  obtain ⟨w, -, hw⟩ := mem_vars_map.mp h₂
  by_cases hkv : kind v = .own
  · exfalso
    rw [spell_own hkv] at hw
    by_cases hkw : kind w = .own
    · rw [spell_own hkw] at hw
      exact hdisj _ _ hw.symm
    · rw [spell_kept hkw] at hw
      exact hkw (hw ▸ hfresh₁ (cell v))
  · rw [spell_kept hkv]
    exact hkv

/-- A collection's copy: every cell freshened, the caller's included, as `collapse` copies
each answer. -/
def collectTerm (cell : V → ℕ) (ψ : ℕ → V) (t : Tm V) : Tm V := t.map (fun v => ψ (cell v))

omit [DecidableEq V] in
theorem collectTerm_localVariant (cell : V → ℕ) (ψ : ℕ → V) (t : Tm V)
    (hcell : Set.InjOn cell {v | v ∈ t.vars}) (hψ : Function.Injective ψ) :
    LocalVariant (fun _ => False) t (collectTerm cell ψ t) :=
  ⟨fun v => ψ (cell v), fun _ hv _ hw he => hcell hv hw (hψ he), fun _ _ h => h.elim,
    fun _ _ _ h => h, rfl⟩

/-! ## A replay through the tier -/

/-- **A replay through the tier agrees with the uncached answer.**  The table replays the
recipe of an answer for the call renamed by `π`; the tier imports the replay and exports
it.  When the tier keeps exactly the anchors (the new call's variables and the retained
identities), with one cell per answer-local identity and a fresh injective supply, the
export is the uncached answer of the renamed call up to renaming its own variables. -/
theorem replay_through_tier (q : Tm V) (R : V → Bool) (π : Equiv.Perm V)
    (hπ : FixesRetained R π) (φ : V → V) (a : Tm V) (hφ : Fresh q R π φ a)
    (kind : V → Kind) (cell : V → ℕ) (ψ : ℕ → V)
    (hkind : ∀ w, Kept kind w ↔ Anchors q R π w)
    (hcell : Set.InjOn cell {v | v ∈ (replay π φ (recipe q R a)).vars ∧ kind v = .own})
    (hψ : Function.Injective ψ) (hfresh : ∀ n, kind (ψ n) = .own) :
    LocalVariant (Anchors q R π) (a.map π)
      (exportTerm kind cell ψ (replay π φ (recipe q R a))) := by
  have h₁ := replay_recipe q R π hπ φ a hφ
  have h₂ := exportTerm_localVariant kind cell ψ _ hcell hψ hfresh
  exact h₁.trans (LocalVariant.congr_anchors h₂ (fun w _ => hkind w))

/-! ## The tier's current shapes against the contract -/

/-- The arrival rule the tier has: a known identity keeps its cell and what its first
arrival said. -/
def enterFirst : Table V → V → Kind → Table V
  | [], v, k => [(v, k)]
  | (w, k') :: t, v, k => if w = v then (w, k') :: t else (w, k') :: enterFirst t v k

/-- Keeping the first arrival's word depends on arrival order; the join does not. -/
theorem enterFirst_order_dependent (v : V) :
    kindOf (enterFirst (enterFirst [] v .own) v .retained) v = some .own ∧
      kindOf (enterFirst (enterFirst [] v .retained) v .own) v = some .retained ∧
      kindOf (importAll [] [(v, .own), (v, .retained)]) v = some .retained ∧
      kindOf (importAll [] [(v, .retained), (v, .own)]) v = some .retained := by
  simp [enterFirst, kindOf, importAll, enter, Kind.join]

/-- The routes by which a variable reaches the tier besides the call. -/
inductive Route
  /-- A host goal's answer. -/
  | host
  /-- A stored value read. -/
  | state

/-- Cells as the tier keeps them: the call's cells apart from one table the other routes
share; a host answer's variable is looked up among the call's cells first, a stored
value's is not. -/
def cellSplit (callers : List V) (tab : Table V) : Route → V → Option (ℕ ⊕ ℕ)
  | .host, v =>
    match cellOf (callers.map fun c => (c, Kind.caller)) v with
    | some i => some (.inl i)
    | none => (cellOf tab v).map .inr
  | .state, v => (cellOf tab v).map .inr

/-- A variable of the call that is also a stored value's: the host route finds the call's
cell, the stored-value route makes a second one.  With one table, the same arrivals give
one cell, known as the caller's. -/
theorem split_cells (v : V) :
    cellSplit [v] (enterFirst [] v .retained) .host v = some (.inl 0) ∧
      cellSplit [v] (enterFirst [] v .retained) .state v = some (.inr 0) ∧
      cellOf (enter [(v, .caller)] v .retained) v = some 0 ∧
      kindOf (enter [(v, .caller)] v .retained) v = some .caller := by
  simp [cellSplit, enterFirst, cellOf, enter, kindOf, Kind.join]

namespace Controls

/-- A sealed payload's variable `7` (retained) and a replay's variable `8` (its own), in
one host answer. -/
def answer : Tm ℕ := .app (.var 7) (.var 8)
/-- What their provenance says. -/
def provenance : ℕ → Kind := fun v => if v = 7 then .retained else .own
/-- Their cells. -/
def cell : ℕ → ℕ := fun v => v - 7
/-- An export's supply. -/
def ψ : ℕ → ℕ := fun n => 1000 + n

theorem ψ_fresh : ∀ n, provenance (ψ n) = .own := by
  intro n
  have h : ψ n ≠ 7 := by simp only [ψ]; omega
  simp [provenance, h]

/-- By provenance: the payload's variable kept, the replay's renamed. -/
theorem provenance_export :
    exportTerm provenance cell ψ answer = .app (.var 7) (.var 1001) ∧
      LocalVariant (Kept provenance) answer (exportTerm provenance cell ψ answer) :=
  ⟨by decide, exportTerm_localVariant _ _ _ _ (fun x hx y hy h => by
      simp only [Set.mem_ofPred_eq, answer, vars_app, vars_var, List.mem_append,
        List.mem_singleton] at hx hy
      rcases hx with ⟨rfl | rfl, -⟩ <;> rcases hy with ⟨rfl | rfl, -⟩ <;> simp_all [cell])
    (fun a b h => by simpa [ψ] using h) ψ_fresh⟩

/-- Answer-local for every host arrival: the payload's variable leaves fresh, so it is no
longer the payload's. -/
theorem hostOwn_loses_retained :
    exportTerm (fun _ => .own) cell ψ answer = .app (.var 1000) (.var 1001) ∧
      ¬ LocalVariant (Kept provenance) answer (exportTerm (fun _ => .own) cell ψ answer) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨θ, -, hfix, -, he⟩
  have h7 : θ 7 = 7 := hfix 7 (by simp [answer]) (by simp [Kept, provenance])
  have hexp : exportTerm (fun _ => Kind.own) cell ψ answer = .app (.var 1000) (.var 1001) := by
    decide
  rw [hexp] at he
  simp only [answer, map_app, map_var, Tm.app.injEq, Tm.var.injEq] at he
  omega

/-- Retained for every host arrival: every export spells the replay's variable `8` as
itself, so two exports share it although it is that answer's own. -/
theorem hostRetained_shares :
    exportTerm (fun _ => .retained) cell ψ answer = answer ∧
      exportTerm (fun _ => .retained) cell (fun n => 2000 + n) answer = answer ∧
      ¬ Kept provenance 8 := by
  refine ⟨by decide, by decide, ?_⟩
  simp [Kept, provenance]

end Controls

end Mettapedia.Machines.AnswerRecipes.TierBoundary
