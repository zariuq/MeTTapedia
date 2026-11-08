import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragmentStore

/-!
# The census of fragment equations

An equation of the dynamic pattern fragment is read through its **opened sides**: both sides applied to
the locals of the left side's abstractions, in normal form (`InFragment`). The census classifies every
equation by

* how its two annotations relate: one code, two convertible codes, or two types that are not equal;
* the **shape** of each opened side, read from its spine head (`spineHead`) and the marking of the
  context into metavariables and locals: a Miller pattern of a metavariable, another spine of a
  metavariable, a spine of a local, of a constant, or headed by a projection, a type former (Π, Σ,
  identity type, or a head: a universe or a ground type), a pair, reflexivity, an abstraction, or a
  non-neutral head applied to arguments.

The census is defined from the syntax alone. The opened normal side of a normal side is computed by
**opening syntactically** (`openNormal`): an abstraction is entered, any other code is applied to the
next local. This is the normal form of the opening (`openCode_star`, `openNormal_normal`), so on a
store whose sides are normal, as every prepared store is, the fragment's condition applies to the
census's sides: **no fragment equation has a metavariable spine that is not a Miller pattern, and its
annotations are equal types** (`census_fragment`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCensus

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ContextualDependentExecutableJoin ContextualDependentDynamicFragment

variable {Head : Type}

/-! ## The shapes of a side -/

/-- The kinds of type formers. -/
inductive FormerKind where
  | pi
  | sigma
  | id
  | head
  deriving DecidableEq, Repr

/-- **The shape of an opened side.** -/
inductive SideShape where
  /-- A metavariable applied to distinct locals. -/
  | pattern
  /-- Any other spine of a metavariable. -/
  | flexOther
  /-- A spine of a local. -/
  | local
  /-- A spine of a constant. -/
  | constant
  /-- A spine headed by a projection. -/
  | projection
  /-- A type former, unapplied. -/
  | former (kind : FormerKind)
  /-- A pair. -/
  | pair
  /-- Reflexivity. -/
  | refl
  /-- An abstraction. -/
  | lam
  /-- A type former, pair, reflexivity or abstraction applied to arguments. -/
  | applied
  deriving DecidableEq, Repr

/-- An unapplied shape, or `applied`. -/
def unapplied {n : Nat} (t : Tm Head n) (shape : SideShape) : SideShape :=
  if spineLength t = 0 then shape else .applied

/-- **The shape of a side**, from its spine head and the marking of the context. -/
def sideShape {n : Nat} (flexible : Fin n → Bool) (t : Tm Head n) : SideShape :=
  match spineHead t with
  | .var i => if flexible i then (if millerSpine flexible t then .pattern else .flexOther) else .local
  | .const _ => .constant
  | .fst _ | .snd _ => .projection
  | .app _ _ => .applied
  | .pi _ _ => unapplied t (.former .pi)
  | .sigma _ _ => unapplied t (.former .sigma)
  | .id _ _ _ => unapplied t (.former .id)
  | .head _ => unapplied t (.former .head)
  | .pair _ _ => unapplied t .pair
  | .refl _ => unapplied t .refl
  | .lam _ => unapplied t .lam

theorem spineHead_readSpine {n : Nat} {t : Tm Head n} {head : Fin n} {arguments : List (Fin n)}
    (read : readSpine t = some (head, arguments)) : spineHead t = .var head := by
  rw [readSpine_spec read, spineHead_appsVar]

/-- **A side with Miller occurrences is never another spine of a metavariable.** -/
theorem sideShape_miller {n : Nat} {flexible : Fin n → Bool} {t : Tm Head n} (holds : miller flexible t = true) :
    sideShape flexible t ≠ .flexOther := by
  rcases side_shape t holds with spine | rigid
  · unfold millerSpine at spine
    cases read : readSpine t with
    | none => rw [read] at spine; cases spine
    | some found =>
        obtain ⟨head, arguments⟩ := found
        rw [read] at spine
        have flexibleHead : flexible head = true := by
          simp only [Bool.and_eq_true] at spine
          exact spine.1.1
        have isSpine : millerSpine flexible t = true := by
          unfold millerSpine
          rw [read]
          exact spine
        unfold sideShape
        rw [spineHead_readSpine read]
        simp [flexibleHead, isSpine]
  · unfold sideShape
    cases headIs : spineHead t with
    | var i =>
        rw [headIs] at rigid
        simp only [flexHead] at rigid
        simp [rigid]
    | pi _ _ | sigma _ _ | id _ _ _ | head _ | pair _ _ | refl _ | lam _ =>
        simp only [unapplied]
        split <;> simp
    | const _ | fst _ | snd _ | app _ _ => simp

/-! ## Opening a normal side -/

/-- **Open a side syntactically**: enter an abstraction, or apply any other code to the next local. -/
def openNormal {n : Nat} : (count : Nat) → Tm Head n → Tm Head (n + count)
  | 0, code => code
  | count + 1, code =>
      match openNormal count code with
      | .lam body => body
      | other => .app (Presentation.rename wk other) (.var 0)

variable {R : Rules Head}

/-- **The opening reduces to the syntactic opening.** -/
theorem openCode_star {n : Nat} (code : Tm Head n) :
    ∀ count, Star (R := R) (openCode count code) (openNormal count code)
  | 0 => .refl
  | count + 1 => by
      have inner := star_rename (R := R) wk (openCode_star code count)
      change Star (R := R) (.app (Presentation.rename wk (openCode count code)) (.var 0))
        (match openNormal count code with
          | .lam body => body
          | other => .app (Presentation.rename wk other) (.var 0))
      refine (star_app inner .refl).trans ?_
      generalize openNormal count code = opened
      cases opened
      case lam body =>
        refine Relation.ReflTransGen.single ?_
        have beta := StepCore.betaPi (root := R.computation) (headEq := StrongNormalization.noHeadSteps)
          (Presentation.rename (liftRen wk) body) (.var 0)
        rw [TypedContextual.Products.fresh_instantiation] at beta
        exact beta
      all_goals exact .refl

variable (empty : R.computation = RootComputation.empty)
include empty

/-- **The syntactic opening of a normal side is normal.** -/
theorem openNormal_normal {n : Nat} {code : Tm Head n} (normal : Normal R code) :
    ∀ count, Normal R (openNormal count code)
  | 0 => normal
  | count + 1 => by
      have inner := openNormal_normal normal count
      change Normal R (match openNormal count code with
        | .lam body => body
        | other => .app (Presentation.rename wk other) (.var 0))
      generalize openNormal count code = opened at inner ⊢
      cases opened
      case lam body => exact (normal_lam_iff empty).mp inner
      all_goals
        dsimp only
        exact (normal_app_iff empty).mpr
          ⟨rfl, (ContextualDependentNormalizing.normal_rename_iff empty wk _).mpr inner, normal_var empty 0⟩

/-- **On a normal side, the fragment's opened normal form is the syntactic opening.** -/
theorem openNormal_inFragment {n : Nat} {context : Ctx Head n} {count : Nat} {code : Tm Head n}
    (normal : Normal R code)
    (inside : ∀ opened, Star (R := R) (openCode count code) opened → Normal R opened →
      InFragmentCode context count opened) :
    InFragmentCode context count (openNormal count code) :=
  inside _ (openCode_star code count) (openNormal_normal empty normal count)

omit empty

/-! ## The census of an equation -/

/-- How the two annotations of an equation relate. -/
inductive AnnotationKind where
  | same
  | convertible
  | heterogeneous
  deriving DecidableEq, Repr

/-- **The census entry of an equation**: its annotations, its opening depth, and its two opened shapes. -/
structure Census where
  annotations : AnnotationKind
  depth : Nat
  left : SideShape
  right : SideShape
  deriving DecidableEq, Repr

variable {rules : Rules Head}

open Classical in
/-- The relation of the two annotations of an equation. -/
noncomputable def annotationKind {Θ : Context rules} (equation : Equation (TotalTerm Θ)) : AnnotationKind :=
  if equation.2.1.code = equation.1.1.code then .same
  else if TypeEq rules Θ.raw equation.1.1.code equation.2.1.code then .convertible else .heterogeneous

/-- **The census of an equation**, read from the store alone. -/
noncomputable def census {Θ : Context rules} (equation : Equation (TotalTerm Θ)) : Census :=
  let count := ContextualDependentPatternSolver.lamDepth equation.1.2.code
  ⟨annotationKind equation, count,
    sideShape (openedFlexible count) (openNormal count equation.1.2.code),
    sideShape (openedFlexible count) (openNormal count equation.2.2.code)⟩

theorem annotationKind_of_typeEq {Θ : Context rules} {equation : Equation (TotalTerm Θ)}
    (same : TypeEq rules Θ.raw equation.1.1.code equation.2.1.code) : annotationKind equation ≠ .heterogeneous := by
  unfold annotationKind
  split
  · simp
  · simp

/-- **The census of the fragment**: on an equation of the fragment whose sides are normal, the
annotations are equal types and neither opened side is a metavariable spine other than a Miller
pattern. -/
theorem census_fragment (empty : rules.computation = RootComputation.empty) {Θ : Context rules}
    {equation : Equation (TotalTerm Θ)} (inside : InFragment equation)
    (leftNormal : Normal rules equation.1.2.code) (rightNormal : Normal rules equation.2.2.code) :
    (census equation).annotations ≠ .heterogeneous ∧ (census equation).left ≠ .flexOther ∧
      (census equation).right ≠ .flexOther := by
  obtain ⟨same, _, _, leftSide, rightSide⟩ := inside
  refine ⟨annotationKind_of_typeEq same, ?_, ?_⟩
  · exact sideShape_miller (openNormal_inFragment empty leftNormal leftSide).1
  · exact sideShape_miller (openNormal_inFragment empty rightNormal rightSide).1

/-- **Shapes of the fragment, read on the opened sides.** On an equation of the fragment whose sides
are normal, both opened sides have Miller occurrences and every metavariable at its arity. -/
theorem fragment_opened (empty : rules.computation = RootComputation.empty) {Θ : Context rules}
    {equation : Equation (TotalTerm Θ)} (inside : InFragment equation)
    (leftNormal : Normal rules equation.1.2.code) (rightNormal : Normal rules equation.2.2.code) :
    InFragmentCode Θ.raw (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
        (openNormal (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) ∧
      InFragmentCode Θ.raw (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
        (openNormal (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) :=
  ⟨openNormal_inFragment empty leftNormal inside.2.2.2.1, openNormal_inFragment empty rightNormal inside.2.2.2.2⟩

end ContextualDependentCensus
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
