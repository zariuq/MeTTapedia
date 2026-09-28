import Mettapedia.GSLT.LanguageDef.AffineExpressionOSLF
import Mettapedia.GSLT.LanguageDef.AffineExpressionRealization

/-!
# Native refinements generated from the affine-expression GSLT

Instantiate the existing OSLF native-type carrier, then explore structural,
behavioral and resource refinements. The source has equality equations, so
each source predicate below has a direct equation-invariance proof.

The concrete payoff is quantifier elimination for affine result ranges: under
an ordered input interval, two endpoint checks are equivalent to a native
result refinement for every initial accumulator in that interval. This is a
final-result theorem, not an intermediate machine-overflow theorem.

These are refinements in the generated OSLF predicate fibers. This module does
not construct the entire presheaf internal language, dependent substitution
calculus, or an automatic decision procedure for arbitrary native predicates.
-/

namespace Mettapedia.GSLT.AffineExpression.NativeTypes

open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

abbrev Native (env : Fin n → Int) (state : Int) :=
  GSLTNativeType (theory env state).closure

def Holds (env : Fin n → Int) (state : Int) (e : Expr n) (T : Native env state) : Prop :=
  (gsltOSLF (theory env state).closure).satisfies (S := T.sort) e T.pred

/-- Native predicates are constructed through the actual generated system. -/
def predicateType (env : Fin n → Int) (state : Int) (P : Expr n → Prop) :
    Native env state where
  sort := ()
  pred := invariantPredicate (theory env state).closure P (by
    intro left right eq
    change left = right at eq
    cases eq
    rfl)

@[simp] theorem holds_predicateType (env : Fin n → Int) (state : Int)
    (e : Expr n) (P : Expr n → Prop) :
    Holds env state e (predicateType env state P) ↔ P e := Iff.rfl

/-- The generated behavioral type: can terminate with a value satisfying P. -/
def resultType (env : Fin n → Int) (state : Int) (P : Int → Prop) : Native env state where
  sort := ()
  pred := semanticDiamond (theory env state).closure
    (predicateType env state (terminalPredicate P)).pred

/-- Native result membership is computed by the independent source evaluator. -/
theorem result_membership (env : Fin n → Int) (state : Int) (e : Expr n) (P : Int → Prop) :
    Holds env state e (resultType env state P) ↔ P (e.eval env state) := by
  change gsltDiamond (theory env state).closure (terminalPredicate P) e ↔ _
  erw [gsltDiamond_spec]
  constructor
  · rintro ⟨target, reached, hp⟩
    cases target with
    | lit v =>
        have hv := (closure_literal_iff env state e v).mp reached
        change P v at hp
        simpa [hv] using hp
    | input | acc | bin => exact False.elim hp
  · intro hp
    exact ⟨.lit (e.eval env state),
      (closure_literal_iff env state e _).mpr rfl, hp⟩

theorem compiled_result_membership (env : Fin n → Int) (state : Int)
    (e : Expr n) (f : Form n) (accepted : compile e = some f) (P : Int → Prop) :
    Holds env state e (resultType env state P) ↔ P (f.apply env state) := by
  rw [result_membership, compile_sound e f accepted]

def admissionType (env : Fin n → Int) (state : Int) : Native env state :=
  predicateType env state (fun e => (compile e).isSome = true)

theorem admission_membership (env : Fin n → Int) (state : Int) (e : Expr n) :
    Holds env state e (admissionType env state) ↔ e.degree ≤ 1 := by
  change (compile e).isSome = true ↔ e.degree ≤ 1
  rw [← compile_exists_iff]
  cases compile e <;> simp

def accumulatorFreeType (env : Fin n → Int) (state : Int) : Native env state :=
  predicateType env state (fun e => e.degree = 0)

/-- A native constructor rule: addition preserves affine admission exactly
when both source operands have the affine refinement. -/
theorem add_admission_iff (env : Fin n → Int) (state : Int) (l r : Expr n) :
    Holds env state (.bin .add l r) (admissionType env state) ↔
      Holds env state l (admissionType env state) ∧
      Holds env state r (admissionType env state) := by
  simp only [admission_membership, Expr.degree, Op.degree, max_le_iff]

/-- Multiplication's inherited typing rule exposes the important asymmetry:
at least one factor must be independent of the accumulator. -/
theorem mul_admission_iff (env : Fin n → Int) (state : Int) (l r : Expr n) :
    Holds env state (.bin .mul l r) (admissionType env state) ↔
      (Holds env state l (accumulatorFreeType env state) ∧
        Holds env state r (admissionType env state)) ∨
      (Holds env state l (admissionType env state) ∧
        Holds env state r (accumulatorFreeType env state)) := by
  simp only [admission_membership, accumulatorFreeType, holds_predicateType,
    Expr.degree, Op.degree]
  omega

def wordSafeType (env : Fin n → Int) (state lo hi : Int) : Native env state :=
  predicateType env state (fun e => (e.evalChecked lo hi env state).isSome = true)

def budgetType (env : Fin n → Int) (state : Int) (fuel : Nat) : Native env state :=
  predicateType env state (fun e => e.work ≤ fuel)

/-- Intersection in the generated native predicate frame. -/
noncomputable def guardedType (env : Fin n → Int) (state lo hi : Int) (fuel : Nat) :
    Native env state :=
  letI := (gsltOSLF (theory env state).closure).frame ()
  { sort := ()
    pred := (admissionType env state).pred ⊓
      ((wordSafeType env state lo hi).pred ⊓ (budgetType env state fuel).pred) }

theorem guarded_membership (env : Fin n → Int) (state lo hi : Int) (fuel : Nat)
    (e : Expr n) :
    Holds env state e (guardedType env state lo hi fuel) ↔
      (compile e).isSome = true ∧
      (e.evalChecked lo hi env state).isSome = true ∧ e.work ≤ fuel := by
  rfl

/-- A reference checker for the guard type. Evaluating the source here can
cost as much as the source itself; it is not proposed as a fast runtime guard. -/
def checkGuard (env : Fin n → Int) (state lo hi : Int) (fuel : Nat) (e : Expr n) : Bool :=
  (compile e).isSome && (e.evalChecked lo hi env state).isSome && decide (e.work ≤ fuel)

theorem checkGuard_exact (env : Fin n → Int) (state lo hi : Int) (fuel : Nat) (e : Expr n) :
    checkGuard env state lo hi fuel e = true ↔
      Holds env state e (guardedType env state lo hi fuel) := by
  rw [guarded_membership]
  simp [checkGuard, and_assoc]

/-- Taking a future modality of structural admission loses its discrimination:
every source expression reduces to an admitted literal, including squares. -/
def eventuallyAdmittedType (env : Fin n → Int) (state : Int) : Native env state where
  sort := ()
  pred := semanticDiamond (theory env state).closure (admissionType env state).pred

theorem every_expression_eventually_admitted (env : Fin n → Int) (state : Int) (e : Expr n) :
    Holds env state e (eventuallyAdmittedType env state) := by
  change gsltDiamond (theory env state).closure
    (fun e => (compile e).isSome = true) e
  apply (gsltDiamond_spec _ _ _).mpr
  exact ⟨.lit (e.eval env state), (closure_literal_iff env state e _).mpr rfl, rfl⟩

def InRange (lo hi value : Int) : Prop := lo ≤ value ∧ value ≤ hi

/-- Both endpoints suffice even when the affine coefficient is negative. -/
theorem affine_interval_endpoints (a b lo hi lower upper : Int) (ordered : lo ≤ hi) :
    (∀ x, lo ≤ x → x ≤ hi → InRange lower upper (a * x + b)) ↔
      InRange lower upper (a * lo + b) ∧ InRange lower upper (a * hi + b) := by
  constructor
  · intro h
    exact ⟨h lo le_rfl ordered, h hi ordered le_rfl⟩
  · rintro ⟨hlo, hhi⟩ x hxlo hxhi
    by_cases positive : 0 ≤ a
    · have low := mul_le_mul_of_nonneg_left hxlo positive
      have high := mul_le_mul_of_nonneg_left hxhi positive
      dsimp [InRange] at *
      omega
    · have negative : a ≤ 0 := le_of_not_ge positive
      have low := mul_le_mul_of_nonpos_left hxhi negative
      have high := mul_le_mul_of_nonpos_left hxlo negative
      dsimp [InRange] at *
      omega

/-- Two finite checks replace universal membership in the generated result
type over an interval of initial accumulators. -/
theorem native_interval_endpoints (env : Fin n → Int) (e : Expr n) (f : Form n)
    (accepted : compile e = some f) (lo hi lower upper : Int) (ordered : lo ≤ hi) :
    (∀ state, lo ≤ state → state ≤ hi →
      Holds env state e (resultType env state (InRange lower upper))) ↔
      InRange lower upper (f.apply env lo) ∧ InRange lower upper (f.apply env hi) := by
  simp_rw [compiled_result_membership env _ e f accepted]
  exact affine_interval_endpoints _ _ _ _ _ _ ordered

instance (lo hi value : Int) : Decidable (InRange lo hi value) :=
  inferInstanceAs (Decidable (lo ≤ value ∧ value ≤ hi))

def checkEndpoints (env : Fin n → Int) (f : Form n) (lo hi lower upper : Int) : Bool :=
  decide (InRange lower upper (f.apply env lo) ∧ InRange lower upper (f.apply env hi))

theorem checkEndpoints_exact (env : Fin n → Int) (e : Expr n) (f : Form n)
    (accepted : compile e = some f) (lo hi lower upper : Int) (ordered : lo ≤ hi) :
    checkEndpoints env f lo hi lower upper = true ↔
      ∀ state, lo ≤ state → state ≤ hi →
        Holds env state e (resultType env state (InRange lower upper)) := by
  simp only [checkEndpoints, decide_eq_true_eq]
  exact (native_interval_endpoints env e f accepted lo hi lower upper ordered).symm

end Mettapedia.GSLT.AffineExpression.NativeTypes
