import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Substitution

/-!
# The interpretation of types

In the consistency model a type denotes a partial equivalence on the terms of
a world. The interpretation reads a type from its weak-head normal form, level
by level:

* a universe below the level: types whose interpretations agree at every
  world reached by a morphism;
* a head that is not a universe: every pair of terms;
* a dependent function type: pairs of functions that send related arguments
  to related results, at every world reached by a morphism;
* a dependent pair type: pairs whose projections are related, with its
  components interpreted at every world reached by a morphism;
* an identity type: every pair of terms when its endpoints are related, no
  pair otherwise;
* the numbers: pairs of terms with the same numeral;
* the codes: pairs of codes with the same truth value;
* `holds c`, for a code `c` with a truth value: every pair of terms when `c`
  is true, no pair otherwise;
* any other rigid type: every pair of terms.

Proofs are therefore irrelevant: a proposition or an identity type relates all
terms or none. The model's reduction does not decode `holds`: in the model
`holds c` is rigid and means the truth of `c`. That the decoding equations of
the package hold in the model is a theorem about these partial equivalences.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization
open UniverseLevel (LevelOrder)

/-- What the model reads from a rule package beyond truth: the type of numbers,
the type of codes and its decoder, and a level in the level order `L` for every
universe. -/
structure Model (Head L : Type) [LevelOrder L] extends Setting Head where
  num : DeclName
  prop : DeclName
  holds : DeclName
  levels : LevelModel rules L

variable {Head L : Type} [LevelOrder L]

/-- A relation on the terms of a world. -/
abbrev Rel (Head : Type) (n : Nat) := Tm Head n → Tm Head n → Prop

/-- A relation between types in worlds and their partial equivalences. -/
abbrev IRel (S : Reading Head) := ∀ {n : Nat}, World S n → Tm Head n → Rel Head n → Prop

section Relations

variable {S : Reading Head}

/-- No type is interpreted. -/
def IRel.empty : IRel S := fun _ _ _ => False

/-- The partial equivalence of a universe: types that have one interpretation
at every world reached by a morphism. -/
def universeRel (below : IRel S) {n : Nat} (ξ : World S n) : Rel Head n := fun A B =>
  ∀ {m : Nat} {ξ' : World S m} {ρ : Ren n m}, Morph ξ ξ' ρ →
    ∃ R, below ξ' (Presentation.rename ρ A) R ∧ below ξ' (Presentation.rename ρ B) R

/-- The partial equivalences of a dependent function type's domain and
codomain, at every world reached by a morphism. -/
structure PiRel (Head : Type) {S : Reading Head} {n : Nat} (ξ : World S n) where
  dom : ∀ {m : Nat} {ξ' : World S m} {ρ : Ren n m}, Morph ξ ξ' ρ → Rel Head m
  cod : ∀ {m : Nat} {ξ' : World S m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) {a : Tm Head m},
    dom w a a → Rel Head m

/-- Functions that send related arguments to related results. -/
def PiRel.rel {n : Nat} {ξ : World S n} (P : PiRel Head ξ) : Rel Head n := fun f g =>
  ∀ {m : Nat} {ξ' : World S m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) {a b : Tm Head m}
    (ha : P.dom w a a), P.dom w a b →
      P.cod w ha (.app (Presentation.rename ρ f) a) (.app (Presentation.rename ρ g) b)

/-- Pairs whose projections are related, at the world itself. -/
def PiRel.pairRel {n : Nat} {ξ : World S n} (P : PiRel Head ξ) : Rel Head n := fun p q =>
  ∃ hp : P.dom (Morph.id ξ) (.fst p) (.fst p), P.dom (Morph.id ξ) (.fst p) (.fst q) ∧
    P.cod (Morph.id ξ) hp (.snd p) (.snd q)

end Relations

/-- The reading of the model: codes mean their truth values. -/
abbrev Model.reading (M : Model Head L) : Reading Head := M.toSetting.truthReading

variable (M : Model Head L)

/-- The interpretation of types at level `l`, given the interpretations below. -/
inductive Interp (l : L) (below : L → IRel M.reading) : IRel M.reading where
  | sort {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {u : Head}
      (isUniverse : M.rules.isUniverse u) (level : M.levels.level u < l)
      (red : WhRed M.rules M.roles A (.head u)) :
      Interp l below ξ A (universeRel (below (M.levels.level u)) ξ)
  | ground {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {h : Head}
      (notUniverse : ¬ M.rules.isUniverse h) (red : WhRed M.rules M.roles A (.head h)) :
      Interp l below ξ A (fun _ _ => True)
  | pi {n : Nat} {ξ : World M.reading n} {A dom : Tm Head n} {cod : Tm Head (n + 1)}
      (red : WhRed M.rules M.roles A (.pi dom cod)) (P : PiRel Head ξ)
      (domInterp : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ),
        Interp l below ξ' (Presentation.rename ρ dom) (P.dom w))
      (codInterp : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
        {a : Tm Head m} (ha : P.dom w a a),
        Interp l below ξ' (inst0 a (Presentation.rename (liftRen ρ) cod)) (P.cod w ha))
      (codRespect : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
        {a b : Tm Head m} (ha : P.dom w a a) (hb : P.dom w b b), P.dom w a b →
          P.cod w ha = P.cod w hb) :
      Interp l below ξ A P.rel
  | sigma {n : Nat} {ξ : World M.reading n} {A dom : Tm Head n} {cod : Tm Head (n + 1)}
      (red : WhRed M.rules M.roles A (.sigma dom cod)) (P : PiRel Head ξ)
      (domInterp : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ),
        Interp l below ξ' (Presentation.rename ρ dom) (P.dom w))
      (codInterp : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
        {a : Tm Head m} (ha : P.dom w a a),
        Interp l below ξ' (inst0 a (Presentation.rename (liftRen ρ) cod)) (P.cod w ha))
      (codRespect : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
        {a b : Tm Head m} (ha : P.dom w a a) (hb : P.dom w b b), P.dom w a b →
          P.cod w ha = P.cod w hb) :
      Interp l below ξ A P.pairRel
  | ident {n : Nat} {ξ : World M.reading n} {A ty lhs rhs : Tm Head n}
      (red : WhRed M.rules M.roles A (.id ty lhs rhs)) (R : Rel Head n)
      (tyInterp : Interp l below ξ ty R) (lhsRefl : R lhs lhs) (rhsRefl : R rhs rhs) :
      Interp l below ξ A (fun _ _ => R lhs rhs)
  | num {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
      (red : WhRed M.rules M.roles A (.const M.num)) :
      Interp l below ξ A (fun t t' => ∃ k, NumVal M.reading t k ∧ NumVal M.reading t' k)
  | prop {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
      (red : WhRed M.rules M.roles A (.const M.prop)) :
      Interp l below ξ A (fun c c' => ∃ P, Truth M.reading ξ c P ∧ Truth M.reading ξ c' P)
  | holds {n : Nat} {ξ : World M.reading n} {A c : Tm Head n}
      (red : WhRed M.rules M.roles A (.app (.const M.holds) c))
      (good : ∃ P, Truth M.reading ξ c P) :
      Interp l below ξ A (fun _ _ => ∃ P, Truth M.reading ξ c P ∧ P)
  | rigid {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {T : DeclName}
      {args : List (Tm Head n)}
      (red : WhRed M.rules M.roles A (appSpine (.const T) args)) (role : M.roles T = .rigid)
      (notProp : T ≠ M.prop) (notHolds : T ≠ M.holds) :
      Interp l below ξ A (fun _ _ => True)

/-- The interpretations below each level: the level order's table of `Interp`. -/
noncomputable def levelsBelow : L → L → IRel M.reading :=
  UniverseLevel.below (fun l below => fun ξ A R => Interp M l below ξ A R) IRel.empty

/-- The interpretation of types at level `l`. -/
noncomputable def InterpAt (l : L) : IRel M.reading :=
  fun ξ A R => Interp M l (levelsBelow M l) ξ A R

theorem levelsBelow_iff :
    ∀ {l k : L}, k < l → ∀ {n : Nat} (ξ : World M.reading n) (A : Tm Head n) (R : Rel Head n),
      levelsBelow M l k ξ A R ↔ InterpAt M k ξ A R := by
  intro l k h n ξ A R
  unfold InterpAt levelsBelow
  rw [UniverseLevel.below_eq _ _ l]
  simp only [if_pos h]

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
