import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure

/-!
# Controlled Prefix Measures (Finite Alphabet)

This file adds the action-conditioned analogue of the finite-alphabet prefix
measure interface.

The key point is that actions are treated as externally supplied side
information. A controlled prefix law assigns mass to finite action-observation
traces `[(a₀, y₀), ..., (aₙ₋₁, yₙ₋₁)]`, and normalization is expressed by
summing over the *next observation* for a fixed next action.

Positive example:
* narrowing to a fixed action stream yields an ordinary prefix measure on
  observation words.

Negative example:
* this file does not yet define any controlled Solomonoff universal mixture.
-/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet

open scoped Classical BigOperators

universe uA uY

/-- Finite action-observation traces. -/
abbrev ControlledWord (Action : Type uA) (Y : Type uY) : Type (max uA uY) :=
  List (Action × Y)

/-- Pair an observation word with the initial segment of an action stream. -/
def pairWithActionStream (u : ℕ → Action) : Word Y → ControlledWord Action Y
  | [] => []
  | y :: ys => (u 0, y) :: pairWithActionStream (fun n => u (n + 1)) ys

@[simp] theorem pairWithActionStream_nil
    (u : ℕ → Action) :
    pairWithActionStream (Action := Action) (Y := Y) u [] = [] := rfl

@[simp] theorem pairWithActionStream_cons
    (u : ℕ → Action) (y : Y) (ys : Word Y) :
    pairWithActionStream (Action := Action) (Y := Y) u (y :: ys) =
      (u 0, y) :: pairWithActionStream (Action := Action) (Y := Y) (fun n => u (n + 1)) ys := rfl

@[simp] theorem map_snd_pairWithActionStream
    (u : ℕ → Action)
    (ys : Word Y) :
    List.map Prod.snd (pairWithActionStream (Action := Action) (Y := Y) u ys) = ys := by
  induction ys generalizing u with
  | nil =>
      simp [pairWithActionStream]
  | cons y ys ih =>
      simp [pairWithActionStream, ih]

theorem pairWithActionStream_append_singleton
    (u : ℕ → Action)
    (ys : Word Y)
    (y : Y) :
    pairWithActionStream (Action := Action) (Y := Y) u (ys ++ [y]) =
      pairWithActionStream (Action := Action) (Y := Y) u ys ++ [(u ys.length, y)] := by
  induction ys generalizing u with
  | nil =>
      simp [pairWithActionStream]
  | cons y' ys ih =>
      simp [pairWithActionStream, ih, List.length]

/-- Controlled semimeasure: a semimeasure on action-observation traces where
the next-step partition sums over observations for a fixed action. -/
structure ControlledSemimeasure (Action : Type uA) (Y : Type uY) [Fintype Y] where
  /-- Trace mass on completed action-observation cycles. -/
  toFun : ControlledWord Action Y → ENNReal
  /-- Controlled semimeasure inequality: summing over the next observation at a
  fixed next action does not exceed the current prefix mass. -/
  superadditive' : ∀ zs : ControlledWord Action Y, ∀ a : Action,
    (∑ y : Y, toFun (zs ++ [(a, y)])) ≤ toFun zs
  /-- Root bound. -/
  root_le_one' : toFun [] ≤ 1

instance {Action : Type uA} {Y : Type uY} [Fintype Y] :
    CoeFun (ControlledSemimeasure Action Y) (fun _ => ControlledWord Action Y → ENNReal) where
  coe := ControlledSemimeasure.toFun

namespace ControlledSemimeasure

variable {Action : Type uA} {Y : Type uY} [Fintype Y]

@[simp] theorem root_le_one (ξ : ControlledSemimeasure Action Y) :
    ξ ([] : ControlledWord Action Y) ≤ 1 :=
  ξ.root_le_one'

/-- Freeze the action side-information to obtain an ordinary semimeasure on
observation words. -/
noncomputable def conditionOnActionStream
    (ξ : ControlledSemimeasure Action Y)
    (u : ℕ → Action) :
    Semimeasure Y where
  toFun ys := ξ (pairWithActionStream (Action := Action) (Y := Y) u ys)
  superadditive' := by
    intro ys
    calc
      (∑ y : Y,
          ξ (pairWithActionStream (Action := Action) (Y := Y) u (ys ++ [y])))
        =
          ∑ y : Y,
            ξ (pairWithActionStream (Action := Action) (Y := Y) u ys ++
              [(u ys.length, y)]) := by
                refine Finset.sum_congr rfl ?_
                intro y hy
                rw [pairWithActionStream_append_singleton (Action := Action) (Y := Y) (u := u)
                  (ys := ys) (y := y)]
    _ ≤ ξ (pairWithActionStream (Action := Action) (Y := Y) u ys) := by
          exact ξ.superadditive' _ (u ys.length)
  root_le_one' := by
    simp [ControlledSemimeasure.root_le_one]

@[simp] theorem conditionOnActionStream_apply
    (ξ : ControlledSemimeasure Action Y)
    (u : ℕ → Action)
    (ys : Word Y) :
    ξ.conditionOnActionStream u ys =
      ξ (pairWithActionStream (Action := Action) (Y := Y) u ys) := rfl

/-- Lift an ordinary observation semimeasure to a controlled semimeasure by
ignoring the action side-information. -/
noncomputable def ofObservationSemimeasure
    (ξ : Semimeasure Y) :
    ControlledSemimeasure Action Y where
  toFun zs := ξ (List.map Prod.snd zs)
  superadditive' := by
    intro zs a
    simpa [List.map_append] using ξ.superadditive' (List.map Prod.snd zs)
  root_le_one' := by
    simp [Semimeasure.root_le_one]

@[simp] theorem ofObservationSemimeasure_apply
    (ξ : Semimeasure Y)
    (zs : ControlledWord Action Y) :
    ofObservationSemimeasure (Action := Action) ξ zs =
      ξ (List.map Prod.snd zs) := rfl

@[simp] theorem conditionOnActionStream_ofObservationSemimeasure_apply
    (ξ : Semimeasure Y)
    (u : ℕ → Action)
    (ys : Word Y) :
    (ofObservationSemimeasure (Action := Action) ξ).conditionOnActionStream u ys = ξ ys := by
  simp [ControlledSemimeasure.conditionOnActionStream_apply]

end ControlledSemimeasure

/-- Controlled prefix measure: a normalized law on action-observation traces. -/
structure ControlledPrefixMeasure (Action : Type uA) (Y : Type uY) [Fintype Y] where
  /-- Trace mass on completed action-observation cycles. -/
  toFun : ControlledWord Action Y → ENNReal
  /-- Root normalization. -/
  root_eq_one' : toFun [] = 1
  /-- Controlled cylinder partition identity at a fixed next action. -/
  additive' : ∀ zs : ControlledWord Action Y, ∀ a : Action,
    (∑ y : Y, toFun (zs ++ [(a, y)])) = toFun zs

instance {Action : Type uA} {Y : Type uY} [Fintype Y] :
    CoeFun (ControlledPrefixMeasure Action Y) (fun _ => ControlledWord Action Y → ENNReal) where
  coe := ControlledPrefixMeasure.toFun

namespace ControlledPrefixMeasure

variable {Action : Type uA} {Y : Type uY} [Fintype Y] (μ : ControlledPrefixMeasure Action Y)

/-- A controlled prefix measure is in particular a controlled semimeasure. -/
def toControlledSemimeasure : ControlledSemimeasure Action Y where
  toFun := μ
  superadditive' := by
    intro zs a
    exact le_of_eq (μ.additive' zs a)
  root_le_one' := by
    exact le_of_eq μ.root_eq_one'

@[simp] theorem toControlledSemimeasure_apply (zs : ControlledWord Action Y) :
    μ.toControlledSemimeasure zs = μ zs := rfl

/-- Freezing the action side-information of a controlled prefix measure yields
an ordinary prefix measure on observations. -/
noncomputable def conditionOnActionStream
    (u : ℕ → Action) :
    PrefixMeasure Y where
  toFun ys := μ (pairWithActionStream (Action := Action) (Y := Y) u ys)
  root_eq_one' := by
    simpa using μ.root_eq_one'
  additive' := by
    intro ys
    calc
      (∑ y : Y,
          μ (pairWithActionStream (Action := Action) (Y := Y) u (ys ++ [y])))
        =
          ∑ y : Y,
            μ (pairWithActionStream (Action := Action) (Y := Y) u ys ++
              [(u ys.length, y)]) := by
                refine Finset.sum_congr rfl ?_
                intro y hy
                rw [pairWithActionStream_append_singleton (Action := Action) (Y := Y) (u := u)
                  (ys := ys) (y := y)]
    _ = μ (pairWithActionStream (Action := Action) (Y := Y) u ys) := by
          exact μ.additive' _ (u ys.length)

@[simp] theorem conditionOnActionStream_apply
    (u : ℕ → Action)
    (ys : Word Y) :
    μ.conditionOnActionStream u ys =
      μ (pairWithActionStream (Action := Action) (Y := Y) u ys) := rfl

end ControlledPrefixMeasure

/-! ## Dominance -/

/-- Controlled dominance: `ξ` dominates `μ` uniformly on all completed
action-observation prefixes. -/
def ControlledDominates
    {Action : Type uA} {Y : Type uY} [Fintype Y]
    (ξ : ControlledSemimeasure Action Y)
    (μ : ControlledPrefixMeasure Action Y)
    (c : ENNReal) : Prop :=
  ∀ zs : ControlledWord Action Y, c * μ zs ≤ ξ zs

theorem controlledDominates_conditionOnActionStream
    {Action : Type uA} {Y : Type uY} [Fintype Y]
    {ξ : ControlledSemimeasure Action Y}
    {μ : ControlledPrefixMeasure Action Y}
    {c : ENNReal}
    (hdom : ControlledDominates ξ μ c)
    (u : ℕ → Action) :
    Dominates (ξ.conditionOnActionStream u) (μ.conditionOnActionStream u) c := by
  intro ys
  simpa [ControlledDominates,
    ControlledSemimeasure.conditionOnActionStream_apply,
    ControlledPrefixMeasure.conditionOnActionStream_apply]
    using hdom (pairWithActionStream (Action := Action) (Y := Y) u ys)

end Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet
