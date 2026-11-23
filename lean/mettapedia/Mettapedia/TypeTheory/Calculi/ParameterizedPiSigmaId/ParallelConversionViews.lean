import Mettapedia.Logic.Relation.Development
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SigmaConversionBoundary

/-!
# Conversion boundaries from parallel constructor views

An auxiliary parallel reduction contains authored steps and reads back
as authored conversion. Its diamond gives common parallel reducts.
Inverting the constructor at those reducts recovers component conversions
and separates dependent functions and pairs from universe heads.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ParallelConversionViews

open Mettapedia.Logic.Relation (BinaryDecomposition confluent_of_diamond Confluent image_of_path)
open _root_.Relation

variable {Head : Type} {R : Rules Head} {n : Nat}

/-- Scoped parallel reduction, with its context implicit in the endpoints. -/
abbrev Reduction (Head : Type) := {n : Nat} → Tm Head n → Tm Head n → Prop

abbrev Paths (parallel : Reduction Head) {n : Nat} :=
  ReflTransGen (@parallel n)

abbrev Sound (R : Rules Head) (parallel : Reduction Head) : Prop :=
  ∀ {n : Nat} {source target : Tm Head n},
    parallel source target → Conv R.headEq source target R.computation

abbrev Joins (R : Rules Head) (parallel : Reduction Head) : Prop :=
  ∀ {n : Nat} {left right : Tm Head n},
    Conv R.headEq left right R.computation → Join (@Paths _ parallel n) left right

theorem path_sound {parallel : Reduction Head} (sound : Sound R parallel)
    {left right : Tm Head n} (steps : Paths parallel left right) :
    Conv R.headEq left right R.computation := by
  induction steps with
  | refl => exact .refl _
  | tail _ final previous => exact .trans _ _ _ previous (sound final)

theorem joins_of_diamond {parallel : Reduction Head}
    (covers : ∀ {n : Nat} {left right : Tm Head n},
      Step R.headEq left right R.computation → parallel left right)
    (diamond : ∀ {n : Nat} {source left right : Tm Head n},
      parallel source left → parallel source right → Join (@parallel n) left right) :
    Joins R parallel := by
  intro n left right conversion
  have confluence : Confluent (@parallel n) := confluent_of_diamond diamond
  exact confluence.eqvGen_iff_join.mp (EqvGen.mono (fun _ _ step => covers step) _ _ conversion)

abbrev BinaryViews (parallel : Reduction Head)
    (assemble : {n : Nat} → Tm Head n → Tm Head (n + 1) → Tm Head n) : Prop :=
  ∀ {n : Nat}, BinaryDecomposition (@parallel n) (@parallel (n + 1)) (@parallel n) (@assemble n)

abbrev HeadViews (parallel : Reduction Head) : Prop :=
  ∀ {n : Nat} {head : Head} {target : Tm Head n},
    parallel (.head head) target → ∃ other, target = .head other

theorem head_path {parallel : Reduction Head} (closed : HeadViews parallel)
    {value : Head} {target : Tm Head n} (steps : Paths parallel (.head value) target) :
    ∃ other, target = .head other :=
  image_of_path Tm.head (fun step => closed step) steps

private theorem components {parallel : Reduction Head}
    {assemble : {n : Nat} → Tm Head n → Tm Head (n + 1) → Tm Head n}
    (injective : ∀ {n : Nat} {a a' : Tm Head n} {b b' : Tm Head (n + 1)},
      assemble a b = assemble a' b' → a = a' ∧ b = b')
    (view : BinaryViews parallel assemble)
    (sound : Sound R parallel) (joins : Joins R parallel)
    {a a' : Tm Head n} {b b' : Tm Head (n + 1)}
    (conversion : Conv R.headEq (assemble a b) (assemble a' b') R.computation) :
    Conv R.headEq a a' R.computation ∧ Conv R.headEq b b' R.computation := by
  obtain ⟨common, leftSteps, rightSteps⟩ := joins conversion
  obtain ⟨_, _, leftShape, firstLeft, secondLeft⟩ := Mettapedia.Logic.Relation.BinaryDecomposition.path (view (n := n)) leftSteps
  obtain ⟨_, _, rightShape, firstRight, secondRight⟩ := Mettapedia.Logic.Relation.BinaryDecomposition.path (view (n := n)) rightSteps
  obtain ⟨sameFirst, sameSecond⟩ := injective (leftShape.symm.trans rightShape)
  cases sameFirst
  cases sameSecond
  exact ⟨.trans _ _ _ (path_sound sound firstLeft) (.symm _ _ (path_sound sound firstRight)),
    .trans _ _ _ (path_sound sound secondLeft) (.symm _ _ (path_sound sound secondRight))⟩

theorem no_common_head {parallel : Reduction Head}
    {assemble : {n : Nat} → Tm Head n → Tm Head (n + 1) → Tm Head n}
    (separated : ∀ {n : Nat} (a : Tm Head n) (b : Tm Head (n + 1)) (head : Head),
      assemble a b ≠ .head head)
    (view : BinaryViews parallel assemble) (heads : HeadViews parallel)
    {a : Tm Head n} {b : Tm Head (n + 1)} {head : Head} :
    ¬ Join (@Paths _ parallel n) (assemble a b) (.head head) := by
  rintro ⟨_, leftSteps, rightSteps⟩
  obtain ⟨a', b', leftShape, _, _⟩ := Mettapedia.Logic.Relation.BinaryDecomposition.path (view (n := n)) leftSteps
  obtain ⟨head', rightShape⟩ := head_path heads rightSteps
  exact separated a' b' head' (leftShape.symm.trans rightShape)

theorem pi_boundary {parallel : Reduction Head} (view : BinaryViews parallel Tm.pi)
    (heads : HeadViews parallel) (sound : Sound R parallel) (joins : Joins R parallel) :
    PiConversionBoundary R where
  components := components Tm.pi.inj view sound joins
  headDisjoint conversion :=
    no_common_head (fun _ _ _ same => by cases same) view heads (joins conversion)

theorem sigma_boundary {parallel : Reduction Head} (view : BinaryViews parallel Tm.sigma)
    (heads : HeadViews parallel) (sound : Sound R parallel) (joins : Joins R parallel) :
    SigmaConversionBoundary R where
  components := components Tm.sigma.inj view sound joins
  headDisjoint conversion :=
    no_common_head (fun _ _ _ same => by cases same) view heads (joins conversion)

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ParallelConversionViews
