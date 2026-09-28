import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Multiset.Bind

/-!
# The order of a conjunction's legs

A conjunctive query runs its legs one after another: a leg extends each
current state by each of its rows that the state admits.  When the rows stay
fixed during the whole enumeration and extending by rows of two legs at
different places commutes (as adding two equations to a solved system does),
the bag of final states does not depend on the order of the legs
(`conj_perm`).

It does not depend on a choice made per state either: a strategy may choose,
in each state reached, which remaining leg runs next, for example the leg
with the fewest candidates under that state's bindings, and the bag is the
same (`dynamic_eq_conj`).

Rows that change during the enumeration (an effect of an earlier answer's
continuation, seen by a later leg's snapshot) are outside this law, and so is
an extension that depends on the order it is applied in
(`Controls.order_matters_without_commuting`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ConjunctionOrder

variable {S R : Type*}

/-- An optional state as a bag of at most one state. -/
def optionMs : Option S → Multiset S
  | none => 0
  | some t => {t}

theorem optionMs_bind_bind (o : Option S) (f : S → Option S) (k : S → Multiset S) :
    (optionMs o).bind (fun t => (optionMs (f t)).bind k) = (optionMs (o.bind f)).bind k := by
  cases o with
  | none => simp [optionMs]
  | some t => simp [optionMs]

/-- A leg: the rows it offers, and the extension of a state by a row. -/
structure Leg (S R : Type*) where
  rows : List R
  extend : R → S → Option S

/-- The states one leg produces from one state. -/
def Leg.run (leg : Leg S R) (s : S) : Multiset S :=
  (leg.rows : Multiset R).bind fun r => optionMs (leg.extend r s)

/-- The legs in order, from one state. -/
def conj : List (Leg S R) → S → Multiset S
  | [], s => {s}
  | leg :: legs, s => (leg.run s).bind fun t => conj legs t

/-- Extending by a row of one leg and by a row of another commutes. -/
def Commute (a b : Leg S R) : Prop :=
  ∀ r ∈ a.rows, ∀ q ∈ b.rows, ∀ s : S,
    (a.extend r s).bind (b.extend q) = (b.extend q s).bind (a.extend r)

/-- Two legs run in turn, as one loop over pairs of rows. -/
theorem run_bind_run (x y : Leg S R) (k : S → Multiset S) (s : S) :
    (x.run s).bind (fun t => (y.run t).bind k) =
      (x.rows : Multiset R).bind fun r => (y.rows : Multiset R).bind fun q =>
        (optionMs ((x.extend r s).bind (y.extend q))).bind k := by
  simp only [Leg.run, Multiset.bind_assoc]
  refine Multiset.bind_congr fun r _ => ?_
  rw [Multiset.bind_bind]
  refine Multiset.bind_congr fun q _ => ?_
  exact optionMs_bind_bind _ _ _

theorem run_bind_run_comm (a b : Leg S R) (commute : Commute a b)
    (k : S → Multiset S) (s : S) :
    (a.run s).bind (fun t => (b.run t).bind k) =
      (b.run s).bind (fun t => (a.run t).bind k) := by
  rw [run_bind_run, run_bind_run, Multiset.bind_bind]
  refine Multiset.bind_congr fun q hq => Multiset.bind_congr fun r hr => ?_
  rw [commute r (Multiset.mem_coe.mp hr) q (Multiset.mem_coe.mp hq) s]

theorem Commute.symm {a b : Leg S R} (commute : Commute a b) : Commute b a :=
  fun q hq r hr s => (commute r hr q hq s).symm

/-- Swapping two adjacent legs that commute leaves the bag unchanged. -/
theorem conj_swap (a b : Leg S R) (commute : Commute a b) (legs : List (Leg S R))
    (s : S) : conj (a :: b :: legs) s = conj (b :: a :: legs) s := by
  simp only [conj]
  exact run_bind_run_comm a b commute (fun t => conj legs t) s

/-- Legs of which any two at different places commute give one bag in every
order. -/
theorem conj_perm {legs legs' : List (Leg S R)} (perm : legs.Perm legs') :
    legs.Pairwise Commute → ∀ s, conj legs s = conj legs' s := by
  induction perm with
  | nil => intro _ s; rfl
  | cons x _ ih =>
      intro commute s
      simp only [conj]
      exact congrArg (Multiset.bind _)
        (funext fun t => ih (List.pairwise_cons.mp commute).2 t)
  | swap x y l =>
      intro commute s
      exact conj_swap y x
        ((List.pairwise_cons.mp commute).1 x List.mem_cons_self) l s
  | trans p₁ _ ih₁ ih₂ =>
      intro commute s
      exact (ih₁ commute s).trans
        (ih₂ ((p₁.pairwise_iff fun h => Commute.symm h).mp commute) s)

/-- A leg taken out of a list, before the rest, is a permutation of it. -/
theorem perm_getElem_cons_eraseIdx (legs : List (Leg S R)) (i : ℕ) (hi : i < legs.length) :
    (legs[i] :: legs.eraseIdx i).Perm legs := by
  have split : legs = legs.take i ++ legs[i] :: legs.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  rw [List.eraseIdx_eq_take_drop_succ]
  conv_rhs => rw [split]
  exact List.perm_middle.symm

/-- A strategy's choice, in each state, of the leg to run next. -/
abbrev Strategy (S R : Type*) :=
  S → (legs : List (Leg S R)) → legs ≠ [] → Fin legs.length

/-- The legs, each next one chosen by the strategy in the state reached. -/
def dynamic (choose : Strategy S R) : List (Leg S R) → S → Multiset S
  | [], s => {s}
  | leg :: legs, s =>
      ((leg :: legs)[choose s (leg :: legs) (List.cons_ne_nil _ _)].run s).bind
        fun t => dynamic choose
          ((leg :: legs).eraseIdx (choose s (leg :: legs) (List.cons_ne_nil _ _))) t
termination_by legs _ => legs.length
decreasing_by
  rw [List.length_eraseIdx_of_lt (Fin.isLt _)]
  simp

/-- However the strategy chooses, the bag is the conjunction's. -/
theorem dynamic_eq_conj (choose : Strategy S R) :
    ∀ (legs : List (Leg S R)), legs.Pairwise Commute →
      ∀ s, dynamic choose legs s = conj legs s
  | [], _, s => by simp [dynamic, conj]
  | leg :: rest, commute, s => by
      rw [dynamic]
      have perm := perm_getElem_cons_eraseIdx (leg :: rest)
        (choose s (leg :: rest) (List.cons_ne_nil _ _))
        (Fin.isLt _)
      have front : (((leg :: rest)[choose s (leg :: rest) (List.cons_ne_nil _ _)] ::
          (leg :: rest).eraseIdx (choose s (leg :: rest) (List.cons_ne_nil _ _))) :
            List (Leg S R)).Pairwise Commute :=
        (perm.pairwise_iff fun h => Commute.symm h).mpr commute
      rw [← conj_perm perm front s]
      simp only [conj]
      exact congrArg (Multiset.bind _) (funext fun t =>
        dynamic_eq_conj choose _ (List.pairwise_cons.mp front).2 t)
termination_by legs => legs.length
decreasing_by
  rw [List.length_eraseIdx_of_lt (Fin.isLt _)]
  simp

/-! ## Controls -/

namespace Controls

/-- Two one-row legs whose extensions record the order they ran in: the
states differ with the order, so the bags do. -/
def first : Leg (List ℕ) Unit := ⟨[()], fun _ s => some (1 :: s)⟩
def second : Leg (List ℕ) Unit := ⟨[()], fun _ s => some (2 :: s)⟩

theorem order_matters_without_commuting :
    conj [first, second] [] ≠ conj [second, first] [] := by
  simp [conj, Leg.run, first, second, optionMs]

/-- Two legs that each constrain their own coordinate commute, and give one
bag in both orders. -/
def left : Leg (ℕ × ℕ) ℕ := ⟨[1, 2], fun r s => some (r, s.2)⟩
def right : Leg (ℕ × ℕ) ℕ := ⟨[3, 4], fun r s => some (s.1, r)⟩

theorem independent_commute : Commute left right := by
  intro r _ q _ s
  rfl

theorem independent_order : conj [left, right] (0, 0) = conj [right, left] (0, 0) :=
  conj_perm (List.Perm.swap right left []) (List.pairwise_pair.mpr independent_commute) _

/-- A leg that overwrites its own coordinate does not commute with itself:
the law asks commuting only of legs at different places. -/
theorem overwrite_not_self_commuting : ¬ Commute left left := by
  intro h
  have := h 1 (by simp [left]) 2 (by simp [left]) (0, 0)
  simp [left] at this

end Controls

end Mettapedia.Machines.ConjunctionOrder
