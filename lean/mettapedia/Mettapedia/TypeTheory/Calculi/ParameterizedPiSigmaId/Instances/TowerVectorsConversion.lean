import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsPrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Decidability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.NeutralHeads

/-!
# Conversion is decided in the tower with vectors

The declarations of `TowerVectorsModel` are stated at any generic equality with the laws of the
model. At the algorithmic equality they make every declared constant semantic for it as well
(`algorithmicConstants`), so the conversion algorithm is **complete** for the package with
vectors, finite types, their eliminators and the identity eliminator (`complete`): derivably
equal terms of a formed context are compared by the algorithm. With soundness, the algorithm derives exactly the typed
equalities (`algorithm_iff`), and the typed equality is decided between two terms of a type and
between two types (`equal_decided`, `typeEq_decided`).

Completeness is what separates terms. Where conversion stops:

* `add x zero` is not `x`, at any type (`add_right_zero_apart`): addition recurses on its first
  argument, and the two sides are neutral terms with different heads. Its positive twin is the
  equation `add zero m ≡ m` of the package.
* So `vec A (add x zero)` is not `vec A x` (`vec_right_zero_apart`): two neutral types that are
  equal have equal last arguments (`neutral_application_arguments`). A vector of length
  `add x zero` is not a vector of length `x` by conversion alone. Its positive twin:
  `vec A (add zero m) ≡ vec A m` (`vec_left_zero_meets`).
* At a neutral length, such as a variable, the type `vec A k` is stuck: it is no pair type and
  not the unit type (`vec_stuck_not_sigma`, `vec_stuck_not_unit`). So the projection `fst v` of a
  vector `v` of unknown length has no type (`head_unknown_length_rejected`): the head is defined
  on vectors of successor length only, and at an unknown length only the eliminator applies.

The ways across the second point are programs of the package: a coercion by recursion on the
length (`TowerVectorsCoercion`), and transport along a proof of `add n zero = n`
(`TowerVectorsIdentity`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel

namespace TowerVectorsConversion

open TowerVectorsModel TowerVectorsPrograms

variable (lv : LevelExpr Nat)

/-! ## Completeness -/

/-- **The declared constants are semantic for the algorithmic equality too**: the declarations
hold at every generic equality with the laws. -/
theorem algorithmicConstants : SemanticConstants (algorithmicSetting (setting lv fun _ => 0)) :=
  constantsAt lv (fun _ => 0)
    (algorithmicSetting_laws (S := setting lv fun _ => 0) (laws lv _) (constants lv _) (roots lv)
      (heads lv) (algebra lv))

/-- **The algorithmic equality is complete for the tower with vectors**: derivably equal terms
of a formed context are algorithmically equal. -/
theorem complete : AlgorithmicComplete (rules lv) roles :=
  AlgorithmicComplete.ofSemantic (S := setting lv fun _ => 0) (laws lv _) (constants lv _)
    (roots lv) (heads lv) (algebra lv) (algorithmicConstants lv)

/-- Head equality of the package is decided. -/
theorem decideHeads (h h' : Tower.Head) : HeadSame (rules lv) h h' ∨ ¬ HeadSame (rules lv) h h' := by
  rcases Decidable.em (Tower.HeadEq h h') with same | different
  · exact .inl (.inr same)
  · rcases Decidable.em (h = h') with equal | unequal
    · exact .inl (.inl equal)
    · exact .inr fun same => same.elim unequal different

variable {lv} {n : Nat} {Γ : Ctx Tower.Head n}

/-- **Completeness of the conversion algorithm**: derivably equal terms are compared by it. -/
theorem algorithm_complete {t u T : Tm Tower.Head n} (formed : CtxFormed (rules lv) Γ)
    (equal : Equal (rules lv) Γ t u T) : Algorithm (rules lv) (.compare Γ t u T) :=
  Equal.algorithm (S := setting lv fun _ => 0) (complete lv) equal formed

/-- **On typed terms of a formed context, the conversion algorithm derives exactly the typed
equalities.** -/
theorem algorithm_iff {t u T : Tm Tower.Head n} (formed : CtxFormed (rules lv) Γ)
    (typedT : Typed (rules lv) Γ t T) (typedU : Typed (rules lv) Γ u T) :
    Algorithm (rules lv) (.compare Γ t u T) ↔ Equal (rules lv) Γ t u T :=
  algorithm_iff_equal (S := setting lv fun _ => 0) (facts lv) (roots lv) (heads lv) (algebra lv)
    (complete lv) formed typedT typedU

/-- **The typed equality is decided between two terms of a type**: the conversion algorithm
terminates on them. -/
theorem equal_decided {t u T : Tm Tower.Head n} (formed : CtxFormed (rules lv) Γ)
    (typedT : Typed (rules lv) Γ t T) (typedU : Typed (rules lv) Γ u T) :
    Equal (rules lv) Γ t u T ∨ ¬ Equal (rules lv) Γ t u T :=
  Equal.decide (S := setting lv fun _ => 0) (facts lv) (roots lv) (heads lv) (algebra lv)
    (decideHeads lv) (complete lv) formed typedT typedU

/-- **The equality of two types is decided.** -/
theorem typeEq_decided {A B : Tm Tower.Head n} (formed : CtxFormed (rules lv) Γ)
    (typeA : IsType (rules lv) Γ A) (typeB : IsType (rules lv) Γ B) :
    TypeEq (rules lv) Γ A B ∨ ¬ TypeEq (rules lv) Γ A B :=
  TypeEq.decide (S := setting lv fun _ => 0) (facts lv) (roots lv) (heads lv) (algebra lv)
    (decideHeads lv) (complete lv) formed typeA typeB

/-! ## Where conversion stops -/

/-- `add x m` is stuck on a variable `x`. -/
theorem add_stuck (x : Fin n) (m : Tm Tower.Head n) : Neutral roles (addC (.var x) m) :=
  Neutral.stuck_single (before := []) (after := [m]) roles_add rfl (.var x)

/-- `vec A k` is stuck on a neutral length `k`. -/
theorem vec_stuck (A : Tm Tower.Head n) {k : Tm Tower.Head n} (neutral : Neutral roles k) :
    Neutral roles (vecC A k) :=
  Neutral.stuck_single (before := [A]) (after := []) roles_vec rfl neutral

/-- **Negative control: `add x zero` is not `x`**, at any type. Addition recurses on its first
argument; on a variable it is neutral, headed by `add`, and the variable is headed by itself. -/
theorem add_right_zero_apart (formed : CtxFormed (rules lv) Γ) (x : Fin n) {T : Tm Tower.Head n} :
    ¬ Equal (rules lv) Γ (addC (.var x) zeroC) (.var x) T :=
  not_equal_of_neutral_heads (S := setting lv fun _ => 0) (complete lv) formed (add_stuck x zeroC)
    (.var x) nofun

/-- **Two neutral applications that are equal types have equal last arguments**, at some type:
the algorithm compares neutral types as spines, argument by argument. -/
theorem neutral_application_arguments {f g a b : Tm Tower.Head n} (formed : CtxFormed (rules lv) Γ)
    (neutralLeft : Neutral roles (.app f a)) (neutralRight : Neutral roles (.app g b))
    (equal : TypeEq (rules lv) Γ (.app f a) (.app g b)) : ∃ A, Equal (rules lv) Γ a b A := by
  have derivation := AlgorithmicComplete.types (S := setting lv fun _ => 0) (complete lv) equal formed
  cases derivation with
  | types redA redB _ _ compared =>
      have eA := WhRed.eq_of_whnf (S := setting lv fun _ => 0) (neutralLeft.whnf (shape lv)) redA.red
      have eB := WhRed.eq_of_whnf (S := setting lv fun _ => 0) (neutralRight.whnf (shape lv)) redB.red
      subst eA
      subst eB
      cases compared with
      | neutralTypes _ _ _ spines =>
          cases spines with
          | spinesW spine _ _ =>
              cases spine with
              | app _ arguments =>
                  exact ⟨_, Algorithmic.sound_terms (S := setting lv fun _ => 0) (facts lv) (roots lv)
                    (heads lv) (algebra lv) formed arguments⟩

/-- **Negative control: `vec A (add x zero)` is not `vec A x`.** A vector of length `add x zero`
is not a vector of length `x` by conversion alone. -/
theorem vec_right_zero_apart (formed : CtxFormed (rules lv) Γ) (A : Tm Tower.Head n) (x : Fin n) :
    ¬ TypeEq (rules lv) Γ (vecC A (addC (.var x) zeroC)) (vecC A (.var x)) := by
  intro equal
  obtain ⟨T, lengths⟩ := neutral_application_arguments formed (vec_stuck A (add_stuck x zeroC))
    (vec_stuck A (.var x)) equal
  exact add_right_zero_apart formed x lengths

/-- **Positive twin: `vec A (add zero m) ≡ vec A m`**, by addition's equation at `zero`. -/
theorem vec_left_zero_meets {A m : Tm Tower.Head n} (tA : Typed (rules lv) Γ A U0)
    (tm : Typed (rules lv) Γ m numC) :
    TypeEq (rules lv) Γ (vecC A (addC zeroC m)) (vecC A m) :=
  vec_congr lv tA (TowerVectors.add_zero tm)

/-- **Negative control: on a variable length the eliminator is not its case at `zero`.**
`vec-elim A P pn pc x y`, at variables `x` and `y`, and the term its equation at `zero` would give
are neutral terms with different heads, so they are equal at no type: the equation does not fire
on a variable. -/
theorem vecElim_variable_length_apart (formed : CtxFormed (rules lv) Γ) (x y : Fin n)
    {A P pn pc Q T : Tm Tower.Head n} :
    ¬ Equal (rules lv) Γ (vecElimC A P pn pc (.var x) (.var y)) (unitRecC Q pn (.var y)) T :=
  not_equal_of_neutral_heads (S := setting lv fun _ => 0) (complete lv) formed
    (TowerVectors.vecElim_stuck_length (lv := lv) x).1
    (Neutral.stuck_single (before := [Q, pn]) (after := []) roles_unitRec rfl (.var y))
    (fun same => absurd (Tm.const.inj same) (by decide))

/-! ## A vector type of unknown length is stuck -/

/-- **At a neutral length the family is stuck: it is no pair type.** -/
theorem vec_stuck_not_sigma (formed : CtxFormed (rules lv) Γ) {A k : Tm Tower.Head n}
    (neutral : Neutral roles k) {S : Tm Tower.Head n} {T : Tm Tower.Head (n + 1)} :
    ¬ TypeEq (rules lv) Γ (vecC A k) (.sigma S T) := fun equal =>
  (TypeEq.neutral_form (facts lv) equal formed (vec_stuck A neutral)
    (.inr (.inr (.inl ⟨_, _, rfl⟩)))).not_former.2.2.1 _ _ rfl

/-- **Nor is it the unit type.** -/
theorem vec_stuck_not_unit (formed : CtxFormed (rules lv) Γ) {A k : Tm Tower.Head n}
    (neutral : Neutral roles k) : ¬ TypeEq (rules lv) Γ (vecC A k) unitC := fun equal =>
  (TypeEq.neutral_form (facts lv) equal formed (vec_stuck A neutral)
    (.inr (.inr (.inr (.inr (.inr ⟨unit, unitCtors, roles_unit, rfl⟩)))))).ne_inductive roles_unit rfl

/-- **Negative control: the head of a vector of unknown length is rejected.** For a variable `v`
declared at `vec A k` with `k` neutral, such as a variable length, the projection `fst v` has no
type: the family is stuck, and a stuck type is no pair type. Its positive twins: `fst v` is typed
at a successor length (`TowerVectorsPrograms.head_typed`), and the eliminator applies at every
length. -/
theorem head_unknown_length_rejected (formed : CtxFormed (rules lv) Γ) (v : Fin n)
    {A k : Tm Tower.Head n} (declared : Ctx.lookup Γ v = vecC A k) (neutral : Neutral roles k)
    {T : Tm Tower.Head n} : ¬ Typed (rules lv) Γ (.fst (.var v)) T := by
  intro typing
  obtain ⟨A', B', tp, _⟩ := Typed.generation typing
  have le : TypeLe (rules lv) Γ (Ctx.lookup Γ v) (.sigma A' B') := Typed.generation tp
  rw [declared] at le
  have stuck := vec_stuck A neutral
  have equal : TypeEq (rules lv) Γ (vecC A k) (.sigma A' B') :=
    TypeLe.rigid (S := setting lv fun _ => 0) le
      (Typed.isType (S := setting lv fun _ => 0) tp formed) formed
      (fun _ _ e => (TypeEq.neutral_form (facts lv) e formed stuck (.inl ⟨_, rfl⟩)).not_former.1 _ rfl)
      (fun _ _ e =>
        (TypeEq.neutral_form (facts lv) e formed stuck (.inr (.inl ⟨_, _, rfl⟩))).not_former.2.1 _ _ rfl)
      (fun _ _ e => vec_stuck_not_sigma formed neutral e)
  exact vec_stuck_not_sigma formed neutral equal

end TowerVectorsConversion

#print axioms TowerVectorsConversion.vecElim_variable_length_apart
#print axioms TowerVectorsConversion.vec_stuck_not_sigma
#print axioms TowerVectorsConversion.vec_stuck_not_unit
#print axioms TowerVectorsConversion.head_unknown_length_rejected
#print axioms TowerVectorsConversion.algorithmicConstants
#print axioms TowerVectorsConversion.complete
#print axioms TowerVectorsConversion.algorithm_complete
#print axioms TowerVectorsConversion.algorithm_iff
#print axioms TowerVectorsConversion.equal_decided
#print axioms TowerVectorsConversion.typeEq_decided
#print axioms TowerVectorsConversion.add_right_zero_apart
#print axioms TowerVectorsConversion.neutral_application_arguments
#print axioms TowerVectorsConversion.vec_right_zero_apart
#print axioms TowerVectorsConversion.vec_left_zero_meets

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
