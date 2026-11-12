import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.FrameInstances
import Mathlib.Data.Nat.Pairing

/-!
# Readback: when the knowledge determines an answer

A program's answer is a term of its result frame. Reading it off at one exhibited solution gives
one value; the answer is **determined** when every solution of the result knowledge reads it as
that value (`Determined`). In the fibration of solution predicates (`SolutionFibration`) this is an
ask: the models of the knowledge lie below the models of the answer equation
(`determined_iff_le`), so the answer equation adds nothing to the knowledge
(`determined_iff_redundant`). The observation is observational (`observational_answer`), and it
survives every later firing, read along the firing (`determined_along`), and every run
(`determined_run`).

## Which knowledge determines an answer

Whether a matched spine determines its arguments is a property of the frame's equivalence on that
spine. On a frame of two variables over the naturals (`Controls.pairFrames`):

* `Controls.pairing_determines`: knowledge equating an injective spine of the variables with a
  value determines each variable (`Nat.pair` is injective, as a rigid constructor is);
* `Controls.sum_undetermined`: knowledge equating a computing spine `x + y` with `1` is solvable and
  does not determine `x`: the solutions `x ↦ 1, y ↦ 0` and `x ↦ 0, y ↦ 1` read it as `1` and as `0`.

For the dependent full step's programs over the rigid vector package (`ProgrammingOnTheStep`), the
same question is whether the typed equality identifies same-head rigid spines only argument by
argument. The tree proves that rigid spines with distinct heads are never equal
(`TypedEquality.Normalization.not_equal_of_rigid_heads`); `RigidReadback` proves the same-head,
argument-wise half for `lookup` and `cons` from the tree's algorithmic equality, and with it that
the lookup program's answer is determined.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Readback

open Interface
open SolutionFibration

universe uO uT uH uOcc uS uF

section Generic

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom)

/-- **The knowledge determines the answer as the value**: every solution reads them alike. -/
def Determined {a : Obj} (store : EquationStore (Tm a)) (answer value : Tm a) : Prop :=
  X.Entails store fun _ σ => X.E (X.act σ answer) (X.act σ value)

/-- **Determinacy is an inequality in the fibre**: the models of the knowledge lie below those of
the answer equation. -/
theorem determined_iff_le {a : Obj} (store : EquationStore (Tm a)) (answer value : Tm a) :
    Determined X store answer value ↔ models X store ≤ models X [(answer, value)] := by
  constructor
  · intro determined σ solved e member
    rw [List.mem_singleton.mp member]
    exact determined σ.1 σ.2 solved
  · intro le b σ solved
    exact le ⟨b, σ⟩ solved (answer, value) (List.mem_singleton_self _)

/-- **Determinacy is redundancy**: adding the answer equation changes no solution. -/
theorem determined_iff_redundant {a : Obj} (store : EquationStore (Tm a)) (answer value : Tm a) :
    Determined X store answer value ↔ models X (store ++ [(answer, value)]) = models X store := by
  constructor
  · intro determined
    funext σ
    apply propext
    constructor
    · intro solved e member
      exact solved e (List.mem_append_left _ member)
    · intro solved e member
      rcases List.mem_append.mp member with inStore | single
      · exact solved e inStore
      · rw [List.mem_singleton.mp single]
        exact determined σ.1 σ.2 solved
  · intro same b σ solved
    have extended : models X (store ++ [(answer, value)]) ⟨b, σ⟩ := by
      rw [same]
      exact solved
    exact extended (answer, value) (List.mem_append_right _ (List.mem_singleton_self _))

/-- The observation "the answer reads as the value" cannot tell agreeing solutions apart. -/
theorem observational_answer {a : Obj} (answer value : Tm a) :
    Observational X (fun σ : Frames.Solution Hom a => X.E (X.act σ.2 answer) (X.act σ.2 value)) := by
  intro b f g same
  have first := same answer
  have second := same value
  constructor
  · intro holds
    exact (X.equivalence b).trans ((X.equivalence b).symm first) ((X.equivalence b).trans holds second)
  · intro holds
    exact (X.equivalence b).trans first
      ((X.equivalence b).trans holds ((X.equivalence b).symm second))

variable {X} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}

/-- **A determined answer stays determined along every firing**, read along it. -/
theorem determined_along (P : Interface.Step X O State Firing) {s : State} {f : Firing s}
    (admitted : P.Admits f) {answer value : Tm (P.frame s)}
    (determined : Determined X (P.knowledge s) answer value) :
    Determined X (P.knowledge (P.result f admitted)) (X.act (P.along f admitted) answer)
      (X.act (P.along f admitted) value) := by
  intro b σ solved
  have back : X.E (X.act (X.comp σ (P.along f admitted)) answer)
      (X.act (X.comp σ (P.along f admitted)) value) :=
    FrameInstances.entails_along P admitted determined b σ solved
  rw [X.act_comp, X.act_comp] at back
  exact back

/-- **A determined answer stays determined along every run**, read along it. -/
theorem determined_run (P : Interface.Step X O State Firing) {s : State} (r : P.Run s)
    {answer value : Tm (P.frame s)} (determined : Determined X (P.knowledge s) answer value) :
    Determined X (P.knowledge r.last) (X.act r.toLast answer) (X.act r.toLast value) := by
  intro b σ solved
  have back : X.E (X.act (X.comp σ r.toLast) answer) (X.act (X.comp σ r.toLast) value) :=
    determined b (X.comp σ r.toLast) (r.models_start σ solved)
  rw [X.act_comp, X.act_comp] at back
  exact back

end Generic

/-! ## Controls: injective spines determine, computing spines do not -/

namespace Controls

/-- **Two variables over the naturals**: a term denotes a function of their values; a morphism
keeps both variables or instantiates both. -/
def pairFrames : Frames (fun _ : Unit => ℕ × ℕ → ℕ) (fun _ _ : Unit => Option (ℕ × ℕ)) where
  E := Eq
  equivalence _ := ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩
  act f t := match f with
    | none => t
    | some p => fun _ => t p
  id _ := none
  comp g f := match f with
    | none => g
    | some p => some p
  act_id _ := rfl
  act_comp g f t := by cases f <;> cases g <;> rfl
  preserves := @fun _ _ _ _ _ same => by subst same; rfl

/-- The variable `x`. -/
def x : ℕ × ℕ → ℕ := fun p => p.1

/-- The constants `0` and `1`. -/
def zero : ℕ × ℕ → ℕ := fun _ => 0
def one : ℕ × ℕ → ℕ := fun _ => 1

/-- The computing spine `x + y`. -/
def sum : ℕ × ℕ → ℕ := fun p => p.1 + p.2

/-- The injective spine `pair x y`, and its value at `x = 1, y = 0`. -/
def pairing : ℕ × ℕ → ℕ := fun p => Nat.pair p.1 p.2
def pairingOneZero : ℕ × ℕ → ℕ := fun _ => Nat.pair 1 0

/-- A solution, read at a point: an equation of functions read at every point. -/
theorem solves_at {σ : Option (ℕ × ℕ)} {s t : ℕ × ℕ → ℕ}
    (solved : pairFrames.Models (a := ()) (b := ()) σ [(s, t)]) (p : ℕ × ℕ) :
    pairFrames.act (a := ()) (b := ()) σ s p = pairFrames.act (a := ()) (b := ()) σ t p :=
  congrFun (solved (s, t) (List.mem_singleton_self _)) p

/-- **An injective spine determines its arguments**: the knowledge `pair x y ≐ pair 1 0`
determines `x` as `1`, and is solvable. -/
theorem pairing_determines :
    pairFrames.Solvable (a := ()) [(pairing, pairingOneZero)] ∧
      Determined pairFrames (a := ()) [(pairing, pairingOneZero)] x one := by
  constructor
  · refine ⟨(), some (1, 0), fun e member => ?_⟩
    rw [List.mem_singleton.mp member]
    rfl
  · intro b σ solved
    cases σ with
    | none =>
        have atOrigin := solves_at solved (0, 0)
        have paired : Nat.pair 0 0 = Nat.pair 1 0 := atOrigin
        exact absurd (Nat.pair_eq_pair.mp paired).1 (by decide)
    | some p =>
        have atPoint := solves_at solved (0, 0)
        have paired : Nat.pair p.1 p.2 = Nat.pair 1 0 := atPoint
        funext q
        exact (Nat.pair_eq_pair.mp paired).1

/-- **A computing spine does not determine its arguments**: the knowledge `x + y ≐ 1` is solvable,
and its solutions read `x` as `1` and as `0`, so it determines neither. -/
theorem sum_undetermined :
    pairFrames.Solvable (a := ()) [(sum, one)] ∧
      ¬ Determined pairFrames (a := ()) [(sum, one)] x one ∧
      ¬ Determined pairFrames (a := ()) [(sum, one)] x zero := by
  have solvedOneZero : pairFrames.Models (a := ()) (b := ()) (some (1, 0)) [(sum, one)] := by
    intro e member
    rw [List.mem_singleton.mp member]
    rfl
  have solvedZeroOne : pairFrames.Models (a := ()) (b := ()) (some (0, 1)) [(sum, one)] := by
    intro e member
    rw [List.mem_singleton.mp member]
    rfl
  refine ⟨⟨(), some (1, 0), solvedOneZero⟩, fun determined => ?_, fun determined => ?_⟩
  · have reads := congrFun (determined () (some (0, 1)) solvedZeroOne) (0, 0)
    have bad : (0 : ℕ) = 1 := reads
    exact absurd bad (by decide)
  · have reads := congrFun (determined () (some (1, 0)) solvedOneZero) (0, 0)
    have bad : (1 : ℕ) = 0 := reads
    exact absurd bad (by decide)

end Controls

#print axioms determined_iff_le
#print axioms determined_iff_redundant
#print axioms observational_answer
#print axioms determined_along
#print axioms determined_run
#print axioms Controls.pairing_determines
#print axioms Controls.sum_undetermined

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Readback
