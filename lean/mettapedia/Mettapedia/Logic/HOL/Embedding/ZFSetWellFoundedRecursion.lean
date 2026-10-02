import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetEliminators

/-!
# Well-founded recursion in sets

A relation well-founded on a set `A`, together with a step that reads the
values at earlier members, determines exactly one function on `A`. Packaged
as a traced graph, that function is an element of the set of functions from
`A` into a set `B` of values, and an element of every closed universe that
contains `A` and `B`.

The set face thus carries a recursion the type face does not have to take as
a scheme. When every recursive call of a written right side lands on an
earlier member, the function satisfies the equation as written. On the
natural numbers this supplies `half` and `log2`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetWellFoundedRecursion

open ZFSetHenkinInterpretation ZFSetUniverseClosure ZFSetDependentProducts
open ZFSetTraceProducts
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
  (numeral numeral_injective numeral_mem_omega numeral_succ natOf
    numeral_natOf natOf_numeral insert_mem_omega)
open scoped ZFSet
open Classical

universe u

noncomputable section

/-! ## Earlier members -/

/-- `y` is an earlier member of `A`: it lies in `A` and `r` places it before `x`. -/
def before (A : ZFSet.{u}) (r : ZFSet.{u} → ZFSet.{u} → Prop)
    (y x : ZFSet.{u}) : Prop :=
  y ∈ A ∧ r y x

/-- The set of members of `A` that `r` places before `x`. -/
def earlier (A : ZFSet.{u}) (r : ZFSet.{u} → ZFSet.{u} → Prop) (x : ZFSet.{u}) :
    ZFSet.{u} :=
  ZFSet.sep (fun y => r y x) A

theorem mem_earlier {A : ZFSet.{u}} {r : ZFSet.{u} → ZFSet.{u} → Prop}
    {y x : ZFSet.{u}} : y ∈ earlier A r x ↔ before A r y x := by
  unfold earlier before
  exact ZFSet.mem_sep

/-- Two maps that agree on a set have the same graph. This belongs with the
graph operations; it is proved here so this module need not import the
inductive development. -/
theorem graph_congr {a : ZFSet.{u}} {f g : ZFSet.{u} → ZFSet.{u}}
    (h : ∀ x, x ∈ a → f x = g x) : graph a f = graph a g := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := mem_graph.mp hz
    exact mem_graph.mpr ⟨x, hx, by rw [h x hx]⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := mem_graph.mp hz
    exact mem_graph.mpr ⟨x, hx, by rw [← h x hx]⟩

/-! ## The unique solution -/

/-- The function on `A` defined by well-founded recursion. At each set the
step sees the traced graph of the solution on the earlier members of `A`.
Off those members the graph carries the empty set. -/
noncomputable def solution (A : ZFSet.{u}) (r : ZFSet.{u} → ZFSet.{u} → Prop)
    (hwf : WellFounded (before A r)) (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (x : ZFSet.{u}) : ZFSet.{u} :=
  WellFounded.fix hwf
    (fun x ih =>
      step x (traceLam (graph (earlier A r x)
        (fun y => if h : before A r y x then ih y h else ∅))))
    x

theorem solution_unfold (A : ZFSet.{u}) (r : ZFSet.{u} → ZFSet.{u} → Prop)
    (hwf : WellFounded (before A r)) (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (x : ZFSet.{u}) :
    solution A r hwf step x =
      step x (traceLam (graph (earlier A r x)
        (fun y => if _ : before A r y x then solution A r hwf step y else ∅))) := by
  unfold solution
  rw [WellFounded.fix_eq]

/-- **Existence.** On `A`, the solution equals the step applied to the traced
graph of the solution on the earlier members. -/
theorem solution_eq {A : ZFSet.{u}} {r : ZFSet.{u} → ZFSet.{u} → Prop}
    (hwf : WellFounded (before A r)) (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (hx : x ∈ A) :
    solution A r hwf step x =
      step x (traceLam (graph (earlier A r x) (solution A r hwf step))) :=
  (fun _ : x ∈ A => by
    refine (solution_unfold A r hwf step x).trans ?_
    apply congrArg (step x)
    apply congrArg traceLam
    refine graph_congr ?_
    intro y hy
    rw [dif_pos (mem_earlier.mp hy)]) hx

/-- **Uniqueness.** Two functions that satisfy the recursion equation on `A`
agree on `A`. -/
theorem solution_unique {A : ZFSet.{u}} {r : ZFSet.{u} → ZFSet.{u} → Prop}
    (hwf : WellFounded (before A r)) (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {f g : ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ x, x ∈ A →
      f x = step x (traceLam (graph (earlier A r x) f)))
    (hg : ∀ x, x ∈ A →
      g x = step x (traceLam (graph (earlier A r x) g)))
    {x : ZFSet.{u}} (hx : x ∈ A) : f x = g x := by
  suffices ∀ z, z ∈ A → f z = g z from this x hx
  intro z
  refine WellFounded.induction (hwf := hwf)
    (C := fun w => w ∈ A → f w = g w) z ?_
  intro w ih hw
  rw [hf w hw, hg w hw]
  apply congrArg (step w)
  apply congrArg traceLam
  refine graph_congr ?_
  intro y hy
  exact ih y (mem_earlier.mp hy) (mem_earlier.mp hy).1

/-- The constructed solution is the only function satisfying the equation. -/
theorem solution_only {A : ZFSet.{u}} {r : ZFSet.{u} → ZFSet.{u} → Prop}
    (hwf : WellFounded (before A r)) (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {f : ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ x, x ∈ A →
      f x = step x (traceLam (graph (earlier A r x) f)))
    {x : ZFSet.{u}} (hx : x ∈ A) : f x = solution A r hwf step x :=
  solution_unique hwf step hf (fun _ hy => solution_eq hwf step hy) hx

/-! ## The solution as a set -/

theorem solution_mem {A : ZFSet.{u}} {r : ZFSet.{u} → ZFSet.{u} → Prop}
    (hwf : WellFounded (before A r)) (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {B : ZFSet.{u}}
    (lands : ∀ x prev, x ∈ A →
      prev ∈ tracePiSet (earlier A r x) (fun _ : ZFSet.{u} => B) →
      step x prev ∈ B)
    {x : ZFSet.{u}} (hx : x ∈ A) : solution A r hwf step x ∈ B := by
  suffices ∀ z, z ∈ A → solution A r hwf step z ∈ B from this x hx
  intro z
  refine WellFounded.induction (hwf := hwf)
    (C := fun w => w ∈ A → solution A r hwf step w ∈ B) z ?_
  intro w ih hw
  rw [solution_eq hwf step hw]
  refine lands w _ hw ?_
  refine mem_tracePiSet.mpr
    ⟨graph (earlier A r w) (solution A r hwf step), ?_, rfl⟩
  refine graph_mem_piSet ?_
  intro y hy
  exact ih y (mem_earlier.mp hy) (mem_earlier.mp hy).1

/-- **As a set.** The traced graph of the solution is a function from `A` into `B`. -/
theorem solution_pack {A : ZFSet.{u}} {r : ZFSet.{u} → ZFSet.{u} → Prop}
    (hwf : WellFounded (before A r)) (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {B : ZFSet.{u}}
    (lands : ∀ x prev, x ∈ A →
      prev ∈ tracePiSet (earlier A r x) (fun _ : ZFSet.{u} => B) →
      step x prev ∈ B) :
    traceLam (graph A (solution A r hwf step)) ∈
      tracePiSet A (fun _ : ZFSet.{u} => B) := by
  refine mem_tracePiSet.mpr ⟨graph A (solution A r hwf step), ?_, rfl⟩
  exact graph_mem_piSet (fun x hx => solution_mem hwf step lands hx)

/-- **As a set, in a closed universe.** The same traced graph belongs to every
closed universe that contains `A` and `B`. -/
theorem solution_pack_closed {U A : ZFSet.{u}} (closed : Closed U) (hA : A ∈ U)
    {B : ZFSet.{u}} (hB : B ∈ U)
    {r : ZFSet.{u} → ZFSet.{u} → Prop} (hwf : WellFounded (before A r))
    {step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    (lands : ∀ x prev, x ∈ A →
      prev ∈ tracePiSet (earlier A r x) (fun _ : ZFSet.{u} => B) →
      step x prev ∈ B) :
    traceLam (graph A (solution A r hwf step)) ∈ U := by
  apply closed.traceLam_mem
  unfold graph
  refine closed.replacement_mem hA
    (fun x => ZFSet.pair x (solution A r hwf step x)) ?_
  intro x hx
  exact closed.pair_mem
    (ZFSet.IsTransitive.mem_trans closed.transitive hx hA)
    (ZFSet.IsTransitive.mem_trans closed.transitive
      (solution_mem hwf step lands hx) hB)

/-! ## The equations as written -/

/-- The values of a traced graph at a finite list of arguments. -/
def readAll (prev : ZFSet.{u}) : List ZFSet.{u} → List ZFSet.{u}
  | [] => []
  | c :: cs => traceApp prev c :: readAll prev cs

/-- The values of a function at a finite list of arguments. -/
def applyAll (f : ZFSet.{u} → ZFSet.{u}) : List ZFSet.{u} → List ZFSet.{u}
  | [] => []
  | c :: cs => f c :: applyAll f cs

theorem readAll_nil (prev : ZFSet.{u}) : readAll prev [] = [] := rfl

theorem readAll_cons (prev c : ZFSet.{u}) (cs : List ZFSet.{u}) :
    readAll prev (c :: cs) = traceApp prev c :: readAll prev cs := rfl

theorem applyAll_nil (f : ZFSet.{u} → ZFSet.{u}) : applyAll f [] = [] := rfl

theorem applyAll_cons (f : ZFSet.{u} → ZFSet.{u}) (c : ZFSet.{u})
    (cs : List ZFSet.{u}) :
    applyAll f (c :: cs) = f c :: applyAll f cs := rfl

theorem readAll_graph {a : ZFSet.{u}} (f : ZFSet.{u} → ZFSet.{u})
    (cs : List ZFSet.{u}) (hcs : ∀ c, c ∈ cs → c ∈ a) :
    readAll (traceLam (graph a f)) cs = applyAll f cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [readAll_cons, applyAll_cons, traceApp_graph_beta f (hcs c List.mem_cons_self)]
    exact congrArg (fun t => f c :: t)
      (ih (fun d hd => hcs d (List.mem_cons_of_mem c hd)))

/-- **One recursive call.** If the call sits earlier than the argument, the
solution satisfies the equation with that call replaced by the solution. -/
theorem equation_one {A : ZFSet.{u}} {r : ZFSet.{u} → ZFSet.{u} → Prop}
    (hwf : WellFounded (before A r)) (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (body : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) (call : ZFSet.{u} → ZFSet.{u})
    (hcall : ∀ x, x ∈ A → call x ∈ earlier A r x)
    (hstep : ∀ x prev, x ∈ A →
      step x prev = body x (traceApp prev (call x)))
    {x : ZFSet.{u}} (hx : x ∈ A) :
    solution A r hwf step x =
      body x (solution A r hwf step (call x)) := by
  refine (solution_eq hwf step hx).trans ?_
  rw [hstep x (traceLam (graph (earlier A r x) (solution A r hwf step))) hx]
  rw [traceApp_graph_beta (solution A r hwf step) (hcall x hx)]

/-- **Finitely many recursive calls.** Each call sits earlier than the
argument, and the step reads the finite list of values in the traced graph.
The solution satisfies the equation with those calls replaced by the solution. -/
theorem equation_finite {A : ZFSet.{u}} {r : ZFSet.{u} → ZFSet.{u} → Prop}
    (hwf : WellFounded (before A r)) (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (body : ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    (calls : ZFSet.{u} → List ZFSet.{u})
    (hcalls : ∀ x, x ∈ A → ∀ c, c ∈ calls x → c ∈ earlier A r x)
    (hstep : ∀ x prev, x ∈ A →
      step x prev = body x (readAll prev (calls x)))
    {x : ZFSet.{u}} (hx : x ∈ A) :
    solution A r hwf step x =
      body x (applyAll (solution A r hwf step) (calls x)) := by
  refine (solution_eq hwf step hx).trans ?_
  rw [hstep x (traceLam (graph (earlier A r x) (solution A r hwf step))) hx]
  rw [readAll_graph (solution A r hwf step) (calls x) (hcalls x hx)]

/-! ## The order of the natural numbers -/

/-- The von Neumann order: `y` comes before `x` when `y ∈ x`. -/
def natBefore (y x : ZFSet.{u}) : Prop := y ∈ x

theorem nat_wf : WellFounded (before ZFSet.omega natBefore) := by
  refine ⟨fun x => ?_⟩
  refine WellFounded.induction (hwf := ZFSet.mem_wf)
    (C := fun z => Acc (before ZFSet.omega natBefore) z) x ?_
  intro x ih
  exact Acc.intro x (fun y hy => ih y hy.2)

/-- A numeral is a member of another exactly when its natural is smaller.
This belongs with the numerals. -/
theorem numeral_mem_iff (j k : ℕ) :
    numeral.{u} j ∈ numeral.{u} k ↔ j < k := by
  induction k with
  | zero =>
    constructor
    · intro h
      exact False.elim (ZFSet.notMem_empty _ h)
    · intro h
      exact False.elim (Nat.not_lt_zero j h)
  | succ k ih =>
    constructor
    · intro h
      rw [numeral_succ, ZFSet.mem_insert_iff] at h
      rcases h with heq | hmem
      · exact (numeral_injective heq) ▸ Nat.lt_succ_self k
      · exact Nat.lt_succ_of_lt (ih.mp hmem)
    · intro h
      rw [numeral_succ, ZFSet.mem_insert_iff]
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h) with heq | hlt
      · exact Or.inl (congrArg numeral.{u} heq)
      · exact Or.inr (ih.mpr hlt)

theorem numeral_pred_two_mem {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega)
    (hbig : 1 < natOf x) :
    numeral.{u} (natOf x - 2) ∈ earlier ZFSet.omega natBefore x := by
  have hmem : numeral.{u} (natOf x - 2) ∈ numeral.{u} (natOf x) :=
    (numeral_mem_iff _ _).mpr
      (Nat.sub_lt (Nat.zero_lt_of_lt hbig) (Nat.succ_pos 1))
  rw [numeral_natOf hx] at hmem
  exact ZFSet.mem_sep.mpr ⟨numeral_mem_omega _, hmem⟩

/-! ## Half -/

/-- `half x = 0` for `x ≤ 1`, and the successor of `half` at `x - 2` otherwise. -/
def halfStep (x prev : ZFSet.{u}) : ZFSet.{u} :=
  if natOf x ≤ 1 then numeral 0 else
    insert (traceApp prev (numeral (natOf x - 2)))
      (traceApp prev (numeral (natOf x - 2)))

noncomputable def half (x : ZFSet.{u}) : ZFSet.{u} :=
  solution ZFSet.omega natBefore nat_wf halfStep x

theorem halfStep_small {x : ZFSet.{u}} (hsmall : natOf x ≤ 1) (prev : ZFSet.{u}) :
    halfStep x prev = numeral 0 := by
  unfold halfStep
  rw [if_pos hsmall]

theorem halfStep_large {x : ZFSet.{u}} (hbig : 1 < natOf x) (prev : ZFSet.{u}) :
    halfStep x prev =
      insert (traceApp prev (numeral (natOf x - 2)))
        (traceApp prev (numeral (natOf x - 2))) := by
  unfold halfStep
  rw [if_neg (Nat.not_le_of_gt hbig)]

theorem half_small {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) (hsmall : natOf x ≤ 1) :
    half x = numeral.{u} 0 := by
  refine (solution_eq nat_wf halfStep hx).trans ?_
  exact halfStep_small hsmall _

theorem half_large {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) (hbig : 1 < natOf x) :
    half x =
      insert (half (numeral.{u} (natOf x - 2)))
        (half (numeral.{u} (natOf x - 2))) := by
  refine (solution_eq nat_wf halfStep hx).trans ?_
  rw [halfStep_large hbig]
  rw [traceApp_graph_beta (solution ZFSet.omega natBefore nat_wf halfStep)
    (numeral_pred_two_mem hx hbig)]
  rfl

theorem half_numeral : ∀ k : ℕ, half (numeral.{u} k) = numeral.{u} (k / 2)
  | 0 => by
      rw [half_small (numeral_mem_omega 0) (by rw [natOf_numeral]; exact Nat.zero_le 1)]
  | 1 =>
      half_small (numeral_mem_omega 1) (by rw [natOf_numeral])
  | k + 2 => by
      have hbig : 1 < natOf (numeral.{u} (k + 2)) := by
        rw [natOf_numeral]
        exact Nat.succ_lt_succ (Nat.succ_pos k)
      have hcall : numeral.{u} ((k + 2) - 2) = numeral.{u} k := by
        rw [Nat.add_sub_cancel]
      rw [half_large (numeral_mem_omega (k + 2)) hbig, natOf_numeral, hcall,
        half_numeral k]
      have hs : numeral.{u} (k / 2 + 1) =
          insert (numeral.{u} (k / 2)) (numeral.{u} (k / 2)) :=
        numeral_succ (k / 2)
      rw [← hs]
      exact congrArg numeral.{u} (Nat.add_div_right k (Nat.succ_pos 1)).symm

theorem half_value {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) :
    half x = numeral.{u} (natOf x / 2) :=
  (congrArg half (numeral_natOf hx).symm).trans (half_numeral (natOf x))

theorem half_mem_earlier {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) (hbig : 1 < natOf x) :
    half x ∈ earlier ZFSet.omega natBefore x := by
  have hmem : numeral.{u} (natOf x / 2) ∈ numeral.{u} (natOf x) :=
    (numeral_mem_iff _ _).mpr
      (Nat.div_lt_self (Nat.zero_lt_of_lt hbig) (Nat.lt_succ_self 1))
  rw [numeral_natOf hx] at hmem
  rw [half_value hx]
  exact ZFSet.mem_sep.mpr ⟨numeral_mem_omega _, hmem⟩

/-- `half` as a set: the traced graph of `half` on the natural numbers. -/
noncomputable def halfSet : ZFSet.{u} :=
  traceLam (graph ZFSet.omega half)

theorem halfStep_mem {x prev : ZFSet.{u}} (hx : x ∈ ZFSet.omega)
    (hp : prev ∈ tracePiSet (earlier ZFSet.omega natBefore x)
      (fun _ : ZFSet.{u} => ZFSet.omega)) :
    halfStep x prev ∈ ZFSet.omega := by
  unfold halfStep
  cases hle : decide (natOf x ≤ 1) with
  | true =>
    rw [if_pos (of_decide_eq_true hle)]
    exact numeral_mem_omega 0
  | false =>
    rw [if_neg (of_decide_eq_false hle)]
    have harg := numeral_pred_two_mem hx (Nat.gt_of_not_le (of_decide_eq_false hle))
    exact insert_mem_omega (traceApp_mem ⟨prev, hp⟩ ⟨numeral (natOf x - 2), harg⟩)

theorem halfSet_mem :
    halfSet ∈ tracePiSet ZFSet.omega (fun _ : ZFSet.{u} => ZFSet.omega) := by
  unfold halfSet
  exact solution_pack nat_wf halfStep (fun x prev hx hp => halfStep_mem hx hp)

/-! ## Base-two logarithm -/

/-- `log2 x = 0` for `x ≤ 1`, and the successor of `log2 (half x)` otherwise. -/
def logStep (x prev : ZFSet.{u}) : ZFSet.{u} :=
  if natOf x ≤ 1 then numeral 0 else
    insert (traceApp prev (half x)) (traceApp prev (half x))

noncomputable def log2 (x : ZFSet.{u}) : ZFSet.{u} :=
  solution ZFSet.omega natBefore nat_wf logStep x

theorem logStep_small {x : ZFSet.{u}} (hsmall : natOf x ≤ 1) (prev : ZFSet.{u}) :
    logStep x prev = numeral 0 := by
  unfold logStep
  rw [if_pos hsmall]

theorem logStep_large {x : ZFSet.{u}} (hbig : 1 < natOf x) (prev : ZFSet.{u}) :
    logStep x prev = insert (traceApp prev (half x)) (traceApp prev (half x)) := by
  unfold logStep
  rw [if_neg (Nat.not_le_of_gt hbig)]

theorem log2_small {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) (hsmall : natOf x ≤ 1) :
    log2 x = numeral.{u} 0 := by
  refine (solution_eq nat_wf logStep hx).trans ?_
  exact logStep_small hsmall _

theorem log2_large {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) (hbig : 1 < natOf x) :
    log2 x = insert (log2 (half x)) (log2 (half x)) := by
  refine (solution_eq nat_wf logStep hx).trans ?_
  rw [logStep_large hbig]
  rw [traceApp_graph_beta (solution ZFSet.omega natBefore nat_wf logStep)
    (half_mem_earlier hx hbig)]
  rfl

theorem log2_eight : log2 (numeral.{u} 8) = numeral.{u} 3 := by
  have h8 : log2 (numeral.{u} 8) =
      insert (log2 (numeral.{u} 4)) (log2 (numeral.{u} 4)) := by
    rw [log2_large (numeral_mem_omega 8) (by rw [natOf_numeral]; decide)]
    rw [half_value (numeral_mem_omega 8), natOf_numeral]
  have h4 : log2 (numeral.{u} 4) =
      insert (log2 (numeral.{u} 2)) (log2 (numeral.{u} 2)) := by
    rw [log2_large (numeral_mem_omega 4) (by rw [natOf_numeral]; decide)]
    rw [half_value (numeral_mem_omega 4), natOf_numeral]
  have h2 : log2 (numeral.{u} 2) =
      insert (log2 (numeral.{u} 1)) (log2 (numeral.{u} 1)) := by
    rw [log2_large (numeral_mem_omega 2) (by rw [natOf_numeral]; decide)]
    rw [half_value (numeral_mem_omega 2), natOf_numeral]
  have h1 : log2 (numeral.{u} 1) = numeral.{u} 0 :=
    log2_small (numeral_mem_omega 1) (by rw [natOf_numeral])
  have n1 : numeral.{u} 1 = insert (numeral.{u} 0) (numeral.{u} 0) := numeral_succ 0
  have n2 : numeral.{u} 2 = insert (numeral.{u} 1) (numeral.{u} 1) := numeral_succ 1
  have n3 : numeral.{u} 3 = insert (numeral.{u} 2) (numeral.{u} 2) := numeral_succ 2
  rw [h8, h4, h2, h1, ← n1, ← n2, ← n3]

/-- `log2` as a set: the traced graph of `log2` on the natural numbers. -/
noncomputable def logSet : ZFSet.{u} :=
  traceLam (graph ZFSet.omega log2)

theorem logStep_mem {x prev : ZFSet.{u}} (hx : x ∈ ZFSet.omega)
    (hp : prev ∈ tracePiSet (earlier ZFSet.omega natBefore x)
      (fun _ : ZFSet.{u} => ZFSet.omega)) :
    logStep x prev ∈ ZFSet.omega := by
  unfold logStep
  cases hle : decide (natOf x ≤ 1) with
  | true =>
    rw [if_pos (of_decide_eq_true hle)]
    exact numeral_mem_omega 0
  | false =>
    rw [if_neg (of_decide_eq_false hle)]
    have harg := half_mem_earlier hx (Nat.gt_of_not_le (of_decide_eq_false hle))
    exact insert_mem_omega (traceApp_mem ⟨prev, hp⟩ ⟨half x, harg⟩)

theorem logSet_mem :
    logSet ∈ tracePiSet ZFSet.omega (fun _ : ZFSet.{u} => ZFSet.omega) := by
  unfold logSet
  exact solution_pack nat_wf logStep (fun x prev hx hp => logStep_mem hx hp)

/-! ## Where the equation does not determine a function -/

/-- A function that ignores its argument. -/
def constantFn (c : ZFSet.{u}) (_x : ZFSet.{u}) : ZFSet.{u} := c

/-- Without well-foundedness, uniqueness fails: every constant function satisfies
`f n = f (suc n)` on the natural numbers. The successor of a number `n` is
`insert n n`. -/
theorem constants_satisfy (c : ZFSet.{u}) :
    ∀ n, n ∈ ZFSet.omega → constantFn c n = constantFn c (insert n n) :=
  fun _ _ => rfl

theorem constants_differ :
    constantFn (numeral.{u} 0) (numeral.{u} 0) ≠
      constantFn (numeral.{u} 1) (numeral.{u} 0) := by
  intro same
  exact Nat.succ_ne_zero 0 (numeral_injective same).symm

/-- Existence can fail. No function from the natural numbers into the natural
numbers satisfies `f n = suc (f n)`. -/
theorem no_self_successor (f : ZFSet.{u} → ZFSet.{u}) :
    ¬ ∀ n, n ∈ ZFSet.omega →
        f n ∈ ZFSet.omega ∧ f n = insert (f n) (f n) := by
  intro hf
  have hmem : f (numeral.{u} 0) ∈ ZFSet.omega :=
    (hf _ (numeral_mem_omega 0)).1
  have heq : f (numeral.{u} 0) =
      insert (f (numeral.{u} 0)) (f (numeral.{u} 0)) :=
    (hf _ (numeral_mem_omega 0)).2
  rw [← numeral_natOf hmem] at heq
  apply Nat.ne_of_lt (Nat.lt_succ_self (natOf (f (numeral.{u} 0))))
  apply numeral_injective
  rw [numeral_succ]
  exact heq

end

end Mettapedia.Logic.HOL.Embedding.ZFSetWellFoundedRecursion
