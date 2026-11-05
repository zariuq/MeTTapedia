import Mettapedia.Algebra.Collections.TermBagFunctionFree
import Mettapedia.Algebra.Collections.FlatBagBasisControls
import Mathlib.Tactic.FinCases

/-!
# Controls for bags of first-order terms

Concrete problems over a signature with a pair constructor `pair`, a unary
`f` and a free binary `bag2`, constants `a`, `b`, `c` and variables `x`, `y`,
`z`. The theorems are kernel-checked; the `#guard` lines are executable counts
of families and retained families, kept apart from the theorems.

* **Nested pairs** (`pair_basis`): the basis of
  `{pair(x, a) | R} = {pair(b, y) | S}` is exactly two families, the one
  leaving both elements to the rests and the one pairing them, which sends
  `x` to `b` and `y` to `a` and leaves both rests to the common bag.
* **A clash inside a pair** (`clash_basis`): pairing `pair(x, x)` with
  `pair(a, b)` would need `x = a` and `x = b`; the basis is the single family
  leaving both elements to the rests, so every solution keeps `pair(a, b)` in
  the left rest (`clash_rest_keeps_pair`).
* **The occurs check** (`occurs_basis`): `x` is not paired with `f(x)`, while
  `x` is paired with `f(y)` (`occurs_free_pairing`).
* **Deeper nesting** (`deep_pairing`): pairing `pair(x, pair(y, a))` with
  `pair(b, pair(c, z))` sends `x` to `b`, `y` to `c` and `z` to `a`.
* **Finitary, not unitary** (`swap_not_unitary`, `swap_finitary`): the
  problem `{pair(x, y), pair(y, x) | R} = {pair(a, b), pair(b, a) | S}` has the
  solutions `x ↦ a, y ↦ b` and `x ↦ b, y ↦ a` with empty rests, and no sound
  family has both as instances (`no_family_covers_both`).
* **Scope: a bag inside an element is not free syntax**
  (`inner_bag_is_not_free_syntax`): `{a, b}` and `{b, a}` are one bag, while no
  substitution makes `{bag2(a, b)}` and `{bag2(b, a)}` one bag of terms. Bags
  below the root therefore cannot be handed to the syntactic element unifier.
* **Independent and shared rests differ** (`independent_rests_compensate`,
  `aliased_rests_reject`): `{a | R} = {b | S}` is solved with `R = {b}` and
  `S = {a}`, and by no answer whose two rests are equal, since a shared rest
  cancels (`TermBagBasis.shared_rest_solves_iff`).
* **Redundancy**: `{pair(x, y), pair(x, y) | R} = {pair(x, y), pair(x, y) | S}`
  has seven families, one per partial matching, and the basis retains one.
* **Function-free instance**: the flat control problem `{x | R} = {y | S}`
  has the decoded term basis as its flat basis (`flat_control_is_function_free`).
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.TermBagBasis.Controls

open Mettapedia.Logic.LP (LPSignature Term Subst Unifies unifyTotal)
open TermBagUnifiers (Answer Family Instance MoreGeneral Solves families candidate genericAnswer instantiate
  fromMatching Matching)

/-! ## The signature -/

/-- A pair constructor, a unary symbol, and a free binary symbol standing for
a two-element bag written as syntax. -/
inductive Fn where
  | pair
  | f
  | bag2
  deriving DecidableEq, Repr

abbrev Fn.arity : Fn → ℕ
  | .pair => 2
  | .f => 1
  | .bag2 => 2

/-- Numerals as constants and three variables. -/
abbrev sig : LPSignature where
  constants := ℕ
  vars := Fin 3
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Fn
  functionArity := Fn.arity

abbrev T := Term sig

def x : T := .var 0
def y : T := .var 1
def z : T := .var 2
def a : T := .const 0
def b : T := .const 1
def c : T := .const 2
def pair (s t : T) : T := .app .pair ![s, t]
def f (s : T) : T := .app .f ![s]
def bag2 (s t : T) : T := .app .bag2 ![s, t]

/-- The substitution sending `x`, `y`, `z` to the three given terms. -/
def subst3 (s t u : T) : Subst sig := fun v => ![s, t, u] v

@[simp] theorem subst3_x (s t u : T) : subst3 s t u 0 = s := rfl
@[simp] theorem subst3_y (s t u : T) : subst3 s t u 1 = t := rfl
@[simp] theorem subst3_z (s t u : T) : subst3 s t u 2 = u := rfl

@[simp] theorem comp_apply (outer inner : Subst sig) (v : Fin 3) :
    (outer ∘ₛ inner) v = outer.applyTerm (inner v) := rfl

@[simp] theorem applyTerm_x (θ : Subst sig) : θ.applyTerm x = θ 0 := rfl
@[simp] theorem applyTerm_y (θ : Subst sig) : θ.applyTerm y = θ 1 := rfl
@[simp] theorem applyTerm_z (θ : Subst sig) : θ.applyTerm z = θ 2 := rfl
@[simp] theorem applyTerm_a (θ : Subst sig) : θ.applyTerm a = a := rfl
@[simp] theorem applyTerm_b (θ : Subst sig) : θ.applyTerm b = b := rfl
@[simp] theorem applyTerm_c (θ : Subst sig) : θ.applyTerm c = c := rfl

@[simp] theorem applyTerm_pair (θ : Subst sig) (s t : T) :
    θ.applyTerm (pair s t) = pair (θ.applyTerm s) (θ.applyTerm t) := by
  unfold pair
  rw [Subst.applyTerm_app]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem applyTerm_f (θ : Subst sig) (s : T) : θ.applyTerm (f s) = f (θ.applyTerm s) := by
  unfold f
  rw [Subst.applyTerm_app]
  congr 1
  funext i
  fin_cases i
  rfl

@[simp] theorem applyTerm_bag2 (θ : Subst sig) (s t : T) :
    θ.applyTerm (bag2 s t) = bag2 (θ.applyTerm s) (θ.applyTerm t) := by
  unfold bag2
  rw [Subst.applyTerm_app]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem pair_inj {s t s' t' : T} : pair s t = pair s' t' ↔ s = s' ∧ t = t' := by
  constructor
  · intro same
    have args := eq_of_heq (Term.app.inj same).2
    exact ⟨congrFun args 0, congrFun args 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem bag2_inj {s t s' t' : T} : bag2 s t = bag2 s' t' ↔ s = s' ∧ t = t' := by
  constructor
  · intro same
    have args := eq_of_heq (Term.app.inj same).2
    exact ⟨congrFun args 0, congrFun args 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem a_ne_b : a ≠ b := by simp [a, b]
@[simp] theorem b_ne_a : b ≠ a := by simp [a, b]
@[simp] theorem var_ne_b (v : Fin 3) : (Term.var v : T) ≠ b := by simp [b]

/-- A term sent to two different constants by two substitutions is a variable. -/
theorem var_of_two_constants {t : T} {first second : Subst sig} {p q : ℕ} (different : p ≠ q)
    (toFirst : first.applyTerm t = .const p) (toSecond : second.applyTerm t = .const q) : ∃ v, t = .var v := by
  cases t with
  | var v => exact ⟨v, rfl⟩
  | const k =>
      have kp : k = p := Term.const.inj toFirst
      have kq : k = q := Term.const.inj toSecond
      exact (different (kp.symm.trans kq)).elim
  | app g ts =>
      rw [Subst.applyTerm_app] at toFirst
      cases toFirst

/-- The selector keeps a list none of whose entries is more general than
another. -/
theorem select_eq_self {α : Type*} (items : List α) (covers : α → α → Prop) [DecidableRel covers]
    (reflexive : ∀ item, covers item item)
    (incomparable : ∀ i j : Fin items.length, i ≠ j → ¬ covers (items.get i) (items.get j)) :
    FiniteUnifierBasis.select items covers = items := by
  have kept (i : Fin items.length) : i ∈ FiniteUnifierBasis.retained items covers := by
    rw [FiniteUnifierBasis.mem_retained]
    rintro ⟨other, general, strictOrEarlier⟩
    by_cases same : other = i
    · subst same
      rcases strictOrEarlier with strict | earlier
      · exact strict (reflexive _)
      · exact lt_irrefl _ earlier
    · exact incomparable other i same general
  unfold FiniteUnifierBasis.select FiniteUnifierBasis.indices
  rw [List.filter_eq_self.mpr fun i _ => decide_eq_true (kept i)]
  exact List.map_get_finRange items

theorem unifyTotal_nil : unifyTotal ([] : List (T × T)) = some (Subst.id sig) := by
  simp [unifyTotal]

/-- No term is a proper subterm of itself. -/
theorem ne_f_self (t : T) : t ≠ f t := by
  intro same
  have smaller := Term.size_subterm (σ := sig) (f := Fn.f) (ts := ![t]) 0
  change t.size < (f t).size at smaller
  rw [← same] at smaller
  exact lt_irrefl _ smaller

/-! ## Nested pairs -/

def pairLeft : List T := [pair x a]
def pairRight : List T := [pair b y]

def unpaired : Matching sig := ([], [pair x a], [pair b y])
def paired : Matching sig := ([(pair x a, pair b y)], [], [])

theorem pair_matchings : Unification.matchings pairLeft pairRight = [unpaired, paired] := rfl

/-- The family leaving both elements to the rests. -/
def apart : Family sig := fromMatching unpaired (Subst.id sig)

theorem candidate_unpaired : candidate unpaired = some apart := by
  change (unifyTotal ([] : List (T × T))).map (fromMatching unpaired) = some apart
  rw [unifyTotal_nil]
  rfl

theorem paired_unifiable : ∃ θ : Subst sig, Unifies θ paired.1 := by
  refine ⟨subst3 b a z, ?_⟩
  intro equation member
  simp only [paired, List.mem_singleton] at member
  subst member
  simp

/-- **The basis of `{pair(x, a) | R} = {pair(b, y) | S}` is exactly two
families**: the one leaving both elements to the rests, and the one pairing
them, whose element substitution sends `x` to `b` and `y` to `a` and whose two
bases are empty. -/
theorem pair_basis : ∃ θ : Subst sig, θ 0 = b ∧ θ 1 = a ∧
    executable pairLeft pairRight = [apart, fromMatching paired θ] ∧
    (fromMatching paired θ).base .left = 0 ∧ (fromMatching paired θ).base .right = 0 := by
  obtain ⟨θ, accepted⟩ := Mettapedia.Logic.LP.unifyTotal_complete paired_unifiable
  have unified := Mettapedia.Logic.LP.unifyTotal_sound _ θ accepted (pair x a, pair b y) (by simp [paired])
  simp only [applyTerm_pair, applyTerm_x, applyTerm_y, applyTerm_a, applyTerm_b, pair_inj] at unified
  obtain ⟨atX, atY⟩ := unified
  have pairedCandidate : candidate paired = some (fromMatching paired θ) := by
    simp [candidate, accepted]
  have familiesEq : families pairLeft pairRight = [apart, fromMatching paired θ] := by
    unfold families
    rw [pair_matchings, List.filterMap_cons_some candidate_unpaired, List.filterMap_cons_some pairedCandidate]
    rfl
  have noApartAbove : ¬ MoreGeneral (fromMatching paired θ) apart := by
    rintro ⟨remainder, common, represented⟩
    have atZero := congrFun (congrArg Answer.elements represented) 0
    change (Term.var 0 : T) = remainder.applyTerm (θ 0) at atZero
    rw [atX, applyTerm_b] at atZero
    exact var_ne_b 0 atZero
  have noPairedBelow : ¬ MoreGeneral apart (fromMatching paired θ) := by
    rintro ⟨remainder, common, represented⟩
    have leftRest := congrFun (congrArg Answer.rest represented) .left
    change (0 : Multiset T) = ((([pair b y].map (Subst.id sig).applyTerm : List T) : Multiset T)).map
      remainder.applyTerm + common at leftRest
    have count := congrArg Multiset.card leftRest
    simp at count
  refine ⟨θ, atX, atY.symm, ?_, rfl, rfl⟩
  unfold executable basis
  rw [familiesEq]
  refine select_eq_self _ _ TermBagUnifiers.MoreGeneral.refl ?_
  intro i j different
  fin_cases i <;> fin_cases j
  · exact (different rfl).elim
  · exact noPairedBelow
  · exact noApartAbove
  · exact (different rfl).elim

-- Executable counts agreeing with `pair_basis`.
#guard (families pairLeft pairRight).length == 2
#guard (executable pairLeft pairRight).length == 2

/-- The pairing answer `x ↦ b`, `y ↦ a` with empty rests solves the problem. -/
theorem paired_answer_solves : Solves pairLeft pairRight ⟨subst3 b a z, fun _ => 0⟩ := by
  simp [Solves, pairLeft, pairRight]

/-! ## A clash inside a pair -/

def clashLeft : List T := [pair x x]
def clashRight : List T := [pair a b]

def clashUnpaired : Matching sig := ([], [pair x x], [pair a b])
def clashPaired : Matching sig := ([(pair x x, pair a b)], [], [])

theorem clash_matchings : Unification.matchings clashLeft clashRight = [clashUnpaired, clashPaired] := rfl

/-- **Pairing `pair(x, x)` with `pair(a, b)` is refused**: it needs `x = a` and
`x = b`. -/
theorem clash_refused : candidate clashPaired = none := by
  have rejected : unifyTotal clashPaired.1 = none := by
    apply (Mettapedia.Logic.LP.unifyTotal_none_iff_not_unifiable clashPaired.1).mpr
    rintro ⟨θ, unifies⟩
    have same := unifies (pair x x, pair a b) (by simp [clashPaired])
    simp only [applyTerm_pair, applyTerm_x, applyTerm_a, applyTerm_b, pair_inj] at same
    exact a_ne_b (same.1.symm.trans same.2)
  simp [candidate, rejected]

def clashApart : Family sig := fromMatching clashUnpaired (Subst.id sig)

theorem candidate_clashUnpaired : candidate clashUnpaired = some clashApart := by
  change (unifyTotal ([] : List (T × T))).map (fromMatching clashUnpaired) = some clashApart
  rw [unifyTotal_nil]
  rfl

/-- **The basis of the clash is the single family leaving both elements to
the rests.** -/
theorem clash_basis : executable clashLeft clashRight = [clashApart] := by
  have familiesEq : families clashLeft clashRight = [clashApart] := by
    unfold families
    rw [clash_matchings, List.filterMap_cons_some candidate_clashUnpaired, List.filterMap_cons_none clash_refused]
    rfl
  unfold executable basis
  rw [familiesEq]
  refine select_eq_self _ _ TermBagUnifiers.MoreGeneral.refl ?_
  intro i j different
  fin_cases i
  fin_cases j
  exact (different rfl).elim

/-- Every solution keeps `pair(a, b)` in the left rest. -/
theorem clash_rest_keeps_pair (answer : Answer sig) (solved : Solves clashLeft clashRight answer) :
    pair a b ∈ answer.rest .left := by
  obtain ⟨family, member, remainder, common, rfl⟩ := (executable_solves_iff clashLeft clashRight answer).mp solved
  rw [clash_basis, List.mem_singleton] at member
  subst member
  change pair a b ∈ ((([pair a b].map (Subst.id sig).applyTerm : List T) : Multiset T)).map remainder.applyTerm +
    common
  simp

/-- There is no solution with both rests empty. -/
theorem clash_no_closed_solution (θ : Subst sig) : ¬ Solves clashLeft clashRight ⟨θ, fun _ => 0⟩ := by
  intro solved
  have kept := clash_rest_keeps_pair _ solved
  simp at kept

#guard (executable clashLeft clashRight).length == 1

/-! ## The occurs check -/

def occursPaired : Matching sig := ([(x, f x)], [], [])

/-- **`x` is not paired with `f(x)`.** -/
theorem occurs_refused : candidate occursPaired = none := by
  have rejected : unifyTotal occursPaired.1 = none := by
    apply (Mettapedia.Logic.LP.unifyTotal_none_iff_not_unifiable occursPaired.1).mpr
    rintro ⟨θ, unifies⟩
    have same := unifies (x, f x) (by simp [occursPaired])
    simp only [applyTerm_x, applyTerm_f] at same
    exact ne_f_self (θ 0) same
  simp [candidate, rejected]

def occursUnpaired : Matching sig := ([], [x], [f x])

theorem occurs_matchings : Unification.matchings [x] [f x] = [occursUnpaired, occursPaired] := rfl

def occursApart : Family sig := fromMatching occursUnpaired (Subst.id sig)

theorem occurs_basis : executable [x] [f x] = [occursApart] := by
  have unpairedCandidate : candidate occursUnpaired = some occursApart := by
    change (unifyTotal ([] : List (T × T))).map (fromMatching occursUnpaired) = some occursApart
    rw [unifyTotal_nil]
    rfl
  have familiesEq : families [x] [f x] = [occursApart] := by
    unfold families
    rw [occurs_matchings, List.filterMap_cons_some unpairedCandidate, List.filterMap_cons_none occurs_refused]
    rfl
  unfold executable basis
  rw [familiesEq]
  refine select_eq_self _ _ TermBagUnifiers.MoreGeneral.refl ?_
  intro i j different
  fin_cases i
  fin_cases j
  exact (different rfl).elim

/-- `x` is paired with `f(y)`: the pairing family sends `x` to `f` of the
image of `y`. -/
theorem occurs_free_pairing : ∃ θ : Subst sig, candidate (([(x, f y)], [], []) : Matching sig) =
    some (fromMatching ([(x, f y)], [], []) θ) ∧ θ 0 = f (θ 1) := by
  have unifiable : ∃ θ : Subst sig, Unifies θ [(x, f y)] := by
    refine ⟨subst3 (f a) a z, ?_⟩
    intro equation member
    simp only [List.mem_singleton] at member
    subst member
    simp
  obtain ⟨θ, accepted⟩ := Mettapedia.Logic.LP.unifyTotal_complete unifiable
  have unified := Mettapedia.Logic.LP.unifyTotal_sound _ θ accepted (x, f y) (by simp)
  simp only [applyTerm_x, applyTerm_f, applyTerm_y] at unified
  exact ⟨θ, by simp [candidate, accepted], unified⟩

/-! ## Deeper nesting -/

def deepPaired : Matching sig := ([(pair x (pair y a), pair b (pair c z))], [], [])

/-- **Pairing `pair(x, pair(y, a))` with `pair(b, pair(c, z))` sends `x` to `b`,
`y` to `c` and `z` to `a`.** -/
theorem deep_pairing : ∃ θ : Subst sig, candidate deepPaired = some (fromMatching deepPaired θ) ∧
    θ 0 = b ∧ θ 1 = c ∧ θ 2 = a := by
  have unifiable : ∃ θ : Subst sig, Unifies θ deepPaired.1 := by
    refine ⟨subst3 b c a, ?_⟩
    intro equation member
    simp only [deepPaired, List.mem_singleton] at member
    subst member
    simp
  obtain ⟨θ, accepted⟩ := Mettapedia.Logic.LP.unifyTotal_complete unifiable
  have unified := Mettapedia.Logic.LP.unifyTotal_sound _ θ accepted _ (List.mem_singleton_self _)
  simp only [applyTerm_pair, applyTerm_x, applyTerm_y, applyTerm_z, applyTerm_a, applyTerm_b, applyTerm_c,
    pair_inj] at unified
  exact ⟨θ, by simp [candidate, accepted], unified.1, unified.2.1, unified.2.2.symm⟩

#guard (executable [pair x (pair y a)] [pair b (pair c z)]).length == 2

/-! ## Finitary, not unitary -/

def swapLeft : List T := [pair x y, pair y x]
def swapRight : List T := [pair a b, pair b a]

/-- The ground families `x ↦ a, y ↦ b` and `x ↦ b, y ↦ a`, with empty bases. -/
def straight : Family sig := ⟨subst3 a b z, fun _ => 0⟩
def crossed : Family sig := ⟨subst3 b a z, fun _ => 0⟩

theorem straight_unifier : Unifier swapLeft swapRight straight := by
  rintro answer ⟨remainder, common, rfl⟩
  simp [Solves, swapLeft, swapRight, instantiate, straight]

theorem crossed_unifier : Unifier swapLeft swapRight crossed := by
  rintro answer ⟨remainder, common, rfl⟩
  simp only [Solves, swapLeft, swapRight, instantiate, crossed, List.map_cons, List.map_nil, applyTerm_pair,
    applyTerm_x, applyTerm_y, comp_apply, subst3_x, subst3_y, applyTerm_a, applyTerm_b, Multiset.map_zero,
    zero_add]
  rw [Multiset.coe_eq_coe.mpr (List.Perm.swap (pair a b) (pair b a) [])]

/-- **No sound family has both swapped solutions as instances.** Its element
terms for `x` and `y` would be distinct variables, and sending both to `a`
would solve the problem with `{pair(a, a), pair(a, a)}` on the left. -/
theorem no_family_covers_both (family : Family sig) (sound : Unifier swapLeft swapRight family)
    (first : Instance family (genericAnswer straight)) (second : Instance family (genericAnswer crossed)) :
    False := by
  obtain ⟨first, firstCommon, firstRepresented⟩ := first
  obtain ⟨second, secondCommon, secondRepresented⟩ := second
  have firstElements := congrArg Answer.elements firstRepresented
  have secondElements := congrArg Answer.elements secondRepresented
  have xFirst : first.applyTerm (family.elements 0) = .const 0 := (congrFun firstElements 0).symm
  have xSecond : second.applyTerm (family.elements 0) = .const 1 := (congrFun secondElements 0).symm
  have yFirst : first.applyTerm (family.elements 1) = .const 1 := (congrFun firstElements 1).symm
  have ySecond : second.applyTerm (family.elements 1) = .const 0 := (congrFun secondElements 1).symm
  obtain ⟨u, atX⟩ := var_of_two_constants (by decide) xFirst xSecond
  obtain ⟨w, atY⟩ := var_of_two_constants (by decide) yFirst ySecond
  have emptyBase (slot : FlatBagUnifiers.RestSlot) : family.base slot = 0 := by
    have rest := congrFun (congrArg Answer.rest firstRepresented) slot
    change (0 : Multiset T) = (family.base slot).map first.applyTerm + firstCommon at rest
    exact map_eq_zero (eq_zero_of_add_eq_zero rest.symm).1
  have solved := sound (instantiate family (fun _ => a) 0) ⟨_, _, rfl⟩
  change (((swapLeft.map ((fun _ => a) ∘ₛ family.elements).applyTerm : List T)) : Multiset T) +
      ((family.base .left).map (Subst.applyTerm fun _ => a) + 0) =
    ((swapRight.map ((fun _ => a) ∘ₛ family.elements).applyTerm : List T) : Multiset T) +
      ((family.base .right).map (Subst.applyTerm fun _ => a) + 0) at solved
  have imageX : ((fun _ => a) ∘ₛ family.elements) 0 = a := by
    change (Subst.applyTerm (fun _ => a) (family.elements 0)) = a
    rw [atX]
    rfl
  have imageY : ((fun _ => a) ∘ₛ family.elements) 1 = a := by
    change (Subst.applyTerm (fun _ => a) (family.elements 1)) = a
    rw [atY]
    rfl
  simp only [swapLeft, swapRight, List.map_cons, List.map_nil, applyTerm_pair, applyTerm_x, applyTerm_y,
    applyTerm_a, applyTerm_b, imageX, imageY, emptyBase, Multiset.map_zero, add_zero] at solved
  have present : pair a a ∈ (([pair a b, pair b a] : List T) : Multiset T) := by
    rw [← solved]
    simp
  simp at present

/-- **Unification of bags of terms is not unitary**: no complete set of
families has at most one member for the swapped problem. -/
theorem swap_not_unitary : ¬ Unification.Unitary (Unifier swapLeft swapRight) MoreGeneral := by
  rintro ⟨families, complete, single⟩
  obtain ⟨first, firstMember, firstCovers⟩ := complete.covers straight straight_unifier
  obtain ⟨second, secondMember, secondCovers⟩ := complete.covers crossed crossed_unifier
  have same : first = second := single firstMember secondMember
  subst same
  exact no_family_covers_both first (complete.sound first firstMember) firstCovers secondCovers

/-- It is finitary: the retained families form a finite complete set. -/
theorem swap_finitary : Unification.Finitary (Unifier swapLeft swapRight) MoreGeneral :=
  ⟨_, (executable_irredundant swapLeft swapRight).toIsComplete, finite swapLeft swapRight⟩

-- Seven matchings, all consistent; the two crossed full matchings subsume the
-- four partial ones, and the family leaving all elements to the rests stays.
#guard (families swapLeft swapRight).length == 7
#guard (executable swapLeft swapRight).length == 3

/-! ## Scope -/

/-- **A bag inside an element is not free syntax.** As bags `{a, b}` and
`{b, a}` are equal, but no substitution makes the bags of terms
`{bag2(a, b)}` and `{bag2(b, a)}` equal. -/
theorem inner_bag_is_not_free_syntax :
    ({a, b} : Multiset T) = {b, a} ∧ ∀ θ : Subst sig, ¬ Solves [bag2 a b] [bag2 b a] ⟨θ, fun _ => 0⟩ := by
  refine ⟨Multiset.pair_comm a b, fun θ solved => ?_⟩
  simp [Solves] at solved

/-- Independent rests compensate different elements. -/
theorem independent_rests_compensate :
    Solves [a] [b] ⟨Subst.id sig, fun slot => match slot with | .left => {b} | .right => {a}⟩ := by
  change (([a].map (Subst.id sig).applyTerm : List T) : Multiset T) + {b} = ([b].map (Subst.id sig).applyTerm : List T) + {a}
  simp only [List.map_cons, List.map_nil, applyTerm_a, applyTerm_b]
  exact add_comm _ _

/-- **Aliased rests are a different problem**: no answer with equal rests
solves `{a | R} = {b | S}`. -/
theorem aliased_rests_reject (answer : Answer sig) (sameRest : answer.rest .left = answer.rest .right) :
    ¬ Solves [a] [b] answer := by
  intro solved
  change (([a].map answer.elements.applyTerm : List T) : Multiset T) + answer.rest .left =
    ([b].map answer.elements.applyTerm : List T) + answer.rest .right at solved
  rw [sameRest] at solved
  simp only [List.map_cons, List.map_nil, applyTerm_a, applyTerm_b] at solved
  exact a_ne_b (Multiset.singleton_inj.mp (add_right_cancel solved))

/-! ## Redundancy -/

def repeated : List T := [pair x y, pair x y]

-- Seven matchings give seven families; the full matchings subsume the rest
-- and are equivalent to each other, so one family is retained.
#guard (families repeated repeated).length == 7
#guard (executable repeated repeated).length == 1

/-! ## The function-free instance -/

/-- The flat control `{x | R} = {y | S}` has the decoded term basis as its
flat basis. -/
theorem flat_control_is_function_free :
    FlatBagBasis.executable FlatBagBasis.Controls.leftVariable FlatBagBasis.Controls.rightVariable =
      (executable (FlatBagBasis.Controls.leftVariable.map FlatElementEncoding.encode)
        (FlatBagBasis.Controls.rightVariable.map FlatElementEncoding.encode)).map
          TermBagFunctionFree.decodeFamily :=
  TermBagFunctionFree.flat_executable_eq _ _

#guard (executable (FlatBagBasis.Controls.leftVariable.map FlatElementEncoding.encode)
  (FlatBagBasis.Controls.rightVariable.map FlatElementEncoding.encode)).length == 2

end Mettapedia.Algebra.Collections.TermBagBasis.Controls
