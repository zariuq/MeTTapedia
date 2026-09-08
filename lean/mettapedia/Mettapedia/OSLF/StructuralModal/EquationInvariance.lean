import Mettapedia.OSLF.StructuralModal.Formula

/-!
# Equation invariance of the structural-modal formula language

The behavioural formers (`diamond`, `box`) are interpreted over the
step modulo equations of the language, so they cannot distinguish
representatives that the equations identify.  The spatial former `headed`
reads the outermost constructor of the representative itself, and that is not
an equation-invariant observation: in rho the singleton parallel wrapper and
the quote/drop law both change the outermost shape without changing the
process.

Two results follow.  The behavioural fragment (no spatial former) is
invariant over every language.  Reading the spatial former modulo the
equations, on some representative rather than the given one, makes the whole
language invariant and agrees with the direct reading on the behavioural
fragment.
-/

namespace Mettapedia.OSLF.StructuralModal.EquationInvariance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.StructuralModal

set_option autoImplicit false

/-! ## The behavioural fragment -/

/-- Formulas built without the spatial former. -/
inductive Admissible : Formula → Prop
  | top : Admissible .top
  | bot : Admissible .bot
  | and {left right : Formula} :
      Admissible left → Admissible right → Admissible (.and left right)
  | or {left right : Formula} :
      Admissible left → Admissible right → Admissible (.or left right)
  | diamond {inner : Formula} : Admissible inner → Admissible (.diamond inner)
  | box {inner : Formula} : Admissible inner → Admissible (.box inner)

theorem not_admissible_headed (constructor : String) (arguments : List Formula) :
    ¬ Admissible (.headed constructor arguments) := by
  intro admissible
  cases admissible

/-! ## The derived modalities over the saturated span are invariant -/

section Modalities

variable (relEnv : RelationEnv) (lang : LanguageDef)

/-- Step-future over the saturated span respects the equations. -/
theorem derivedDiamond_langSpanUsing_equationInvariant
    {predicate : Pattern → Prop}
    (invariant : EquationInvariant (langGSLTUsing relEnv lang) predicate) :
    EquationInvariant (langGSLTUsing relEnv lang)
      (derivedDiamond (langSpanUsing relEnv lang) predicate) := by
  intro left right equivalent
  constructor
  · rintro ⟨edge, sourceEq, holds⟩
    have sourceEq' : edge.val.1 = left := sourceEq
    have step : langSemanticReducesUsing relEnv lang left edge.val.2 := by
      rw [← sourceEq']
      exact edge.2
    obtain ⟨target', step', targetEquivalent⟩ :=
      (langGSLTUsing relEnv lang).rewrites_resp_left equivalent step
    exact ⟨⟨(right, target'), step'⟩, rfl, (invariant targetEquivalent).mp holds⟩
  · rintro ⟨edge, sourceEq, holds⟩
    have sourceEq' : edge.val.1 = right := sourceEq
    have step : langSemanticReducesUsing relEnv lang right edge.val.2 := by
      rw [← sourceEq']
      exact edge.2
    obtain ⟨target', step', targetEquivalent⟩ :=
      (langGSLTUsing relEnv lang).rewrites_resp_left
        ((langGSLTUsing relEnv lang).equations.iseqv.symm equivalent) step
    exact ⟨⟨(left, target'), step'⟩, rfl, (invariant targetEquivalent).mp holds⟩

/-- Step-past over the saturated span respects the equations, for every
predicate on sources. -/
theorem derivedBox_langSpanUsing_equationInvariant
    (predicate : Pattern → Prop) :
    EquationInvariant (langGSLTUsing relEnv lang)
      (derivedBox (langSpanUsing relEnv lang) predicate) := by
  intro left right equivalent
  constructor
  · intro holds edge targetEq
    have targetEq' : edge.val.2 = right := targetEq
    have step : langSemanticReducesUsing relEnv lang edge.val.1 right := by
      rw [← targetEq']
      exact edge.2
    have step' : langSemanticReducesUsing relEnv lang edge.val.1 left :=
      (langGSLTUsing relEnv lang).rewrites_resp_right step
        ((langGSLTUsing relEnv lang).equations.iseqv.symm equivalent)
    exact holds ⟨(edge.val.1, left), step'⟩ rfl
  · intro holds edge targetEq
    have targetEq' : edge.val.2 = left := targetEq
    have step : langSemanticReducesUsing relEnv lang edge.val.1 left := by
      rw [← targetEq']
      exact edge.2
    have step' : langSemanticReducesUsing relEnv lang edge.val.1 right :=
      (langGSLTUsing relEnv lang).rewrites_resp_right step equivalent
    exact holds ⟨(edge.val.1, right), step'⟩ rfl

end Modalities

/-! ## The behavioural fragment is invariant -/

/-- Every admissible formula denotes an equation-invariant predicate over the
saturated span of any language. -/
theorem satisfiesOver_langSpanUsing_equationInvariant
    (relEnv : RelationEnv) (lang : LanguageDef) {formula : Formula}
    (admissible : Admissible formula) :
    EquationInvariant (langGSLTUsing relEnv lang)
      (satisfiesOver (langSpanUsing relEnv lang) formula) := by
  induction admissible with
  | top =>
      intro left right _
      exact Iff.rfl
  | bot =>
      intro left right _
      exact Iff.rfl
  | and _ _ leftIH rightIH =>
      intro left right equivalent
      exact and_congr (leftIH equivalent) (rightIH equivalent)
  | or _ _ leftIH rightIH =>
      intro left right equivalent
      exact or_congr (leftIH equivalent) (rightIH equivalent)
  | diamond _ innerIH =>
      exact derivedDiamond_langSpanUsing_equationInvariant relEnv lang innerIH
  | box _ _ =>
      exact derivedBox_langSpanUsing_equationInvariant relEnv lang _

/-- Default-environment form. -/
theorem satisfies_equationInvariant (lang : LanguageDef) {formula : Formula}
    (admissible : Admissible formula) :
    EquationInvariant (langGSLT lang) (satisfies lang formula) :=
  satisfiesOver_langSpanUsing_equationInvariant RelationEnv.empty lang admissible

/-! ## The spatial former read modulo the equations -/

mutual
  /-- Structural-modal satisfaction in which the spatial former is read on
  some representative equivalent to the given term. -/
  def satisfiesModuloOver (equiv : Pattern → Pattern → Prop)
      (span : ReductionSpan Pattern) : Formula → Pattern → Prop
    | .top, _ => True
    | .bot, _ => False
    | .and left right, pattern =>
        satisfiesModuloOver equiv span left pattern ∧
          satisfiesModuloOver equiv span right pattern
    | .or left right, pattern =>
        satisfiesModuloOver equiv span left pattern ∨
          satisfiesModuloOver equiv span right pattern
    | .headed constructor arguments, pattern =>
        ∃ children : List Pattern,
          equiv pattern (.apply constructor children) ∧
            satisfiesAllModuloOver equiv span arguments children
    | .diamond inner, pattern =>
        derivedDiamond span (satisfiesModuloOver equiv span inner) pattern
    | .box inner, pattern =>
        derivedBox span (satisfiesModuloOver equiv span inner) pattern

  /-- Pointwise form for argument vectors. -/
  def satisfiesAllModuloOver (equiv : Pattern → Pattern → Prop)
      (span : ReductionSpan Pattern) : List Formula → List Pattern → Prop
    | [], [] => True
    | argument :: arguments, child :: children =>
        satisfiesModuloOver equiv span argument child ∧
          satisfiesAllModuloOver equiv span arguments children
    | _, _ => False
end

/-- Structural-modal satisfaction modulo the equations of a language. -/
def satisfiesModuloUsing (relEnv : RelationEnv) (lang : LanguageDef) :
    Formula → Pattern → Prop :=
  satisfiesModuloOver (langGSLTUsing relEnv lang).Equiv (langSpanUsing relEnv lang)

/-- Default-environment satisfaction modulo the equations. -/
def satisfiesModulo (lang : LanguageDef) : Formula → Pattern → Prop :=
  satisfiesModuloUsing RelationEnv.empty lang

/-- The whole language is invariant when the spatial former is read modulo the
equations.  The spatial case needs only that equivalence composes; the
argument formulas are evaluated on the representative's children. -/
theorem satisfiesModuloUsing_equationInvariant
    (relEnv : RelationEnv) (lang : LanguageDef) :
    ∀ formula : Formula,
      EquationInvariant (langGSLTUsing relEnv lang)
        (satisfiesModuloUsing relEnv lang formula)
  | .top => fun _ _ _ => Iff.rfl
  | .bot => fun _ _ _ => Iff.rfl
  | .and left right => fun _ _ equivalent =>
      and_congr (satisfiesModuloUsing_equationInvariant relEnv lang left equivalent)
        (satisfiesModuloUsing_equationInvariant relEnv lang right equivalent)
  | .or left right => fun _ _ equivalent =>
      or_congr (satisfiesModuloUsing_equationInvariant relEnv lang left equivalent)
        (satisfiesModuloUsing_equationInvariant relEnv lang right equivalent)
  | .headed constructor arguments => by
      intro left right equivalent
      constructor
      · rintro ⟨children, representative, holds⟩
        exact ⟨children,
          (langGSLTUsing relEnv lang).equations.iseqv.trans
            ((langGSLTUsing relEnv lang).equations.iseqv.symm equivalent) representative,
          holds⟩
      · rintro ⟨children, representative, holds⟩
        exact ⟨children,
          (langGSLTUsing relEnv lang).equations.iseqv.trans equivalent representative,
          holds⟩
  | .diamond inner =>
      derivedDiamond_langSpanUsing_equationInvariant relEnv lang
        (satisfiesModuloUsing_equationInvariant relEnv lang inner)
  | .box inner =>
      derivedBox_langSpanUsing_equationInvariant relEnv lang _

/-- Default-environment form. -/
theorem satisfiesModulo_equationInvariant (lang : LanguageDef) (formula : Formula) :
    EquationInvariant (langGSLT lang) (satisfiesModulo lang formula) :=
  satisfiesModuloUsing_equationInvariant RelationEnv.empty lang formula

/-- Every formula denotes a predicate of the sole OSLF predicate frame. -/
def moduloPredicate (relEnv : RelationEnv) (lang : LanguageDef) (formula : Formula) :
    EquationPredicate (langGSLTUsing relEnv lang) :=
  ⟨satisfiesModuloUsing relEnv lang formula,
    satisfiesModuloUsing_equationInvariant relEnv lang formula⟩

/-- On the behavioural fragment the two readings agree. -/
theorem satisfiesModuloOver_iff_satisfiesOver_of_admissible
    (equiv : Pattern → Pattern → Prop) (span : ReductionSpan Pattern)
    {formula : Formula} (admissible : Admissible formula) (pattern : Pattern) :
    satisfiesModuloOver equiv span formula pattern ↔
      satisfiesOver span formula pattern := by
  induction admissible generalizing pattern with
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | and _ _ leftIH rightIH =>
      exact and_congr (leftIH pattern) (rightIH pattern)
  | or _ _ leftIH rightIH =>
      exact or_congr (leftIH pattern) (rightIH pattern)
  | diamond _ innerIH =>
      show (∃ edge, span.source edge = pattern ∧ _) ↔ (∃ edge, span.source edge = pattern ∧ _)
      exact exists_congr fun edge => and_congr Iff.rfl (innerIH _)
  | box _ innerIH =>
      show (∀ edge, span.target edge = pattern → _) ↔ (∀ edge, span.target edge = pattern → _)
      exact forall_congr' fun edge => imp_congr Iff.rfl (innerIH _)

mutual
  /-- The direct reading implies the reading modulo a reflexive relation. -/
  theorem satisfiesModuloOver_of_satisfiesOver
      {equiv : Pattern → Pattern → Prop} (reflexive : ∀ pattern, equiv pattern pattern)
      (span : ReductionSpan Pattern) :
      ∀ (formula : Formula) (pattern : Pattern),
        satisfiesOver span formula pattern → satisfiesModuloOver equiv span formula pattern
    | .top, _, _ => trivial
    | .bot, _, absurd => absurd
    | .and left right, pattern, ⟨leftHolds, rightHolds⟩ =>
        ⟨satisfiesModuloOver_of_satisfiesOver reflexive span left pattern leftHolds,
          satisfiesModuloOver_of_satisfiesOver reflexive span right pattern rightHolds⟩
    | .or left right, pattern, holds =>
        holds.elim
          (fun leftHolds =>
            Or.inl (satisfiesModuloOver_of_satisfiesOver reflexive span left pattern leftHolds))
          (fun rightHolds =>
            Or.inr (satisfiesModuloOver_of_satisfiesOver reflexive span right pattern rightHolds))
    | .headed _ arguments, _, ⟨children, shape, holds⟩ =>
        ⟨children, shape ▸ reflexive _,
          satisfiesAllModuloOver_of_satisfiesAllOver reflexive span arguments children holds⟩
    | .diamond inner, _, ⟨edge, sourceEq, holds⟩ =>
        ⟨edge, sourceEq,
          satisfiesModuloOver_of_satisfiesOver reflexive span inner _ holds⟩
    | .box inner, _, holds => fun edge targetEq =>
        satisfiesModuloOver_of_satisfiesOver reflexive span inner _ (holds edge targetEq)

  /-- Pointwise form. -/
  theorem satisfiesAllModuloOver_of_satisfiesAllOver
      {equiv : Pattern → Pattern → Prop} (reflexive : ∀ pattern, equiv pattern pattern)
      (span : ReductionSpan Pattern) :
      ∀ (arguments : List Formula) (children : List Pattern),
        satisfiesAllOver span arguments children →
          satisfiesAllModuloOver equiv span arguments children
    | [], [], _ => trivial
    | argument :: arguments, child :: children, ⟨holds, rest⟩ =>
        ⟨satisfiesModuloOver_of_satisfiesOver reflexive span argument child holds,
          satisfiesAllModuloOver_of_satisfiesAllOver reflexive span arguments children rest⟩
    | [], _ :: _, absurd => absurd
    | _ :: _, [], absurd => absurd
end

end Mettapedia.OSLF.StructuralModal.EquationInvariance
