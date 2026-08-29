import Mettapedia.Languages.MeTTa.Pure.Intrinsic.RegularNormalizationBoundary

/-!
# Accessibility-driven normalization for regular Pure

This module supplies the executable half of the regular normalizer.  It chooses
one outermost-leftmost reduction step, proves that failure to choose a step is
exactly irreducibility, and iterates the strategy to a normal form from an
`Acc Red` witness.  The remaining logical-relations theorem must show that every
term and type in a regular judgment is accessible.
-/

namespace Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary

open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction

/-- One executable outermost-leftmost reduction step, carrying its soundness
proof.  Proof fields erase; runtime data is only the selected target term. -/
def reduceOnce? : (term : PureTm n) → Option {target : PureTm n // Red term target}
  | .var _ => none
  | .const _ => none
  | .u0 => none
  | .u1 => none
  | .pi A B =>
      match reduceOnce? A with
      | some next => some ⟨.pi next.1 B, .congPiDom next.2⟩
      | none =>
          match reduceOnce? B with
          | some next => some ⟨.pi A next.1, .congPiCod next.2⟩
          | none => none
  | .sigma A B =>
      match reduceOnce? A with
      | some next => some ⟨.sigma next.1 B, .congSigmaDom next.2⟩
      | none =>
          match reduceOnce? B with
          | some next => some ⟨.sigma A next.1, .congSigmaCod next.2⟩
          | none => none
  | .id A a b =>
      match reduceOnce? A with
      | some next => some ⟨.id next.1 a b, .congIdTy next.2⟩
      | none =>
          match reduceOnce? a with
          | some next => some ⟨.id A next.1 b, .congIdLeft next.2⟩
          | none =>
              match reduceOnce? b with
              | some next => some ⟨.id A a next.1, .congIdRight next.2⟩
              | none => none
  | .lam body =>
      match reduceOnce? body with
      | some next => some ⟨.lam next.1, .congLam next.2⟩
      | none => none
  | .app (.lam body) argument =>
      some ⟨inst0 argument body, .betaPi body argument⟩
  | .app function argument =>
      match reduceOnce? function with
      | some next => some ⟨.app next.1 argument, .congAppFun next.2⟩
      | none =>
          match reduceOnce? argument with
          | some next => some ⟨.app function next.1, .congAppArg next.2⟩
          | none => none
  | .pair first second =>
      match reduceOnce? first with
      | some next => some ⟨.pair next.1 second, .congPairFst next.2⟩
      | none =>
          match reduceOnce? second with
          | some next => some ⟨.pair first next.1, .congPairSnd next.2⟩
          | none => none
  | .fst (.pair first second) =>
      some ⟨first, .betaSigmaFst first second⟩
  | .fst pair =>
      match reduceOnce? pair with
      | some next => some ⟨.fst next.1, .congFst next.2⟩
      | none => none
  | .snd (.pair first second) =>
      some ⟨second, .betaSigmaSnd first second⟩
  | .snd pair =>
      match reduceOnce? pair with
      | some next => some ⟨.snd next.1, .congSnd next.2⟩
      | none => none
  | .refl term =>
      match reduceOnce? term with
      | some next => some ⟨.refl next.1, .congRefl next.2⟩
      | none => none
termination_by term => sizeOf term

/-- Every declarative one-step redex makes the executable strategy select some
step.  The selected target need not be the same target: confluence is what makes
any complete strategy adequate for conversion. -/
theorem reduceOnce_isSome_of_red {source target : PureTm n}
    (step : Red source target) : (reduceOnce? source).isSome = true := by
  induction step with
  | betaPi => simp [reduceOnce?]
  | betaSigmaFst => simp [reduceOnce?]
  | betaSigmaSnd => simp [reduceOnce?]
  | congPiDom _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      simp [reduceOnce?, selected]
  | @congPiCod _ A B B' _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      cases domainStep : reduceOnce? A <;> simp [reduceOnce?, domainStep, selected]
  | congSigmaDom _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      simp [reduceOnce?, selected]
  | @congSigmaCod _ A B B' _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      cases domainStep : reduceOnce? A <;> simp [reduceOnce?, domainStep, selected]
  | congIdTy _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      simp [reduceOnce?, selected]
  | @congIdLeft _ A a a' b _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      cases typeStep : reduceOnce? A <;> simp [reduceOnce?, typeStep, selected]
  | @congIdRight _ A a b b' _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      cases typeStep : reduceOnce? A <;>
        cases leftStep : reduceOnce? a <;>
        simp [reduceOnce?, typeStep, leftStep, selected]
  | congLam _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      simp [reduceOnce?, selected]
  | @congAppFun _ f f' a _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      cases f <;> simp_all [reduceOnce?]
  | @congAppArg _ f a a' _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      cases f <;> simp_all [reduceOnce?] <;>
        repeat' split <;> simp_all
  | congPairFst _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      simp [reduceOnce?, selected]
  | @congPairSnd _ a b b' _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      cases firstStep : reduceOnce? a <;> simp [reduceOnce?, firstStep, selected]
  | @congFst _ p p' _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      cases p <;> simp [reduceOnce?, selected]
  | @congSnd _ p p' _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      cases p <;> simp [reduceOnce?, selected]
  | congRefl _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      simp [reduceOnce?, selected]

/-- Executable failure is exactly declarative irreducibility. -/
theorem reduceOnce_eq_none_iff_normal (term : PureTm n) :
    reduceOnce? term = none ↔ RedNormal term := by
  constructor
  · intro noStep target step
    have selected := reduceOnce_isSome_of_red step
    rw [noStep] at selected
    contradiction
  · intro normal
    cases selected : reduceOnce? term with
    | none => simp
    | some next => exact False.elim (normal next.1 next.2)

/-- A computed normal form and its complete correctness evidence. -/
structure NormalizationResult (source : PureTm n) where
  normalForm : PureTm n
  reduces : RedStar source normalForm
  irreducible : RedNormal normalForm

/-- Iterate the executable strategy using accessibility of the declarative
reduction relation.  This is total exactly where strong normalization supplies
the `Acc` witness. -/
def normalizeAccessible (source : PureTm n)
    (accessible : Acc (fun reduct term => Red term reduct) source) :
    NormalizationResult source := by
  induction accessible with
  | intro term smaller ih =>
      cases selected : reduceOnce? term with
      | none =>
          exact
            { normalForm := term
              reduces := RedStar.refl term
              irreducible := (reduceOnce_eq_none_iff_normal term).1 selected }
      | some next =>
          let result := ih next.1 next.2
          exact
            { normalForm := result.normalForm
              reduces := Relation.ReflTransGen.head next.2 result.reduces
              irreducible := result.irreducible }

/-! ## A concrete exact normalization domain -/

/-- Accessibility in the direction used by normalization: every immediate
reduct is structurally smaller in the accessibility tree. -/
def ReductionAccessible (term : PureTm n) : Prop :=
  Acc (fun reduct source => Red source reduct) term

/-- The executable normalizer on the intersection of the accessibility domain
and the declaration-free presentation fragment.  This is a genuine
nondegenerate normalization specification: it computes reductions and induces
an exact NIK decision procedure on its domain.  The later strong-normalization
theorem enlarges its certified coverage to every regular typing judgment. -/
def accessibleNormalizationSpecification : NormalizationSpecification where
  Domain := fun term => ReductionAccessible term ∧ ConstantFree term
  normalize := fun term covered =>
    (normalizeAccessible term covered.1).normalForm
  reduces := fun term covered =>
    (normalizeAccessible term covered.1).reduces
  irreducible := fun term covered =>
    (normalizeAccessible term covered.1).irreducible
  fragment := fun _ covered => covered.2

/-- The transparent accessibility tree for the lower universe. -/
def u0ReductionAccessibility (n : Nat) :
    ReductionAccessible (.u0 : PureTm n) := by
  constructor
  intro reduct step
  cases step

/-- The lower universe is accessible because it has no reducts. -/
theorem u0_reductionAccessible (n : Nat) :
    ReductionAccessible (.u0 : PureTm n) :=
  u0ReductionAccessibility n

/-- The transparent accessibility tree for the upper universe. -/
def u1ReductionAccessibility (n : Nat) :
    ReductionAccessible (.u1 : PureTm n) := by
  constructor
  intro reduct step
  cases step

/-- The upper universe is likewise accessible. -/
theorem u1_reductionAccessible (n : Nat) :
    ReductionAccessible (.u1 : PureTm n) :=
  u1ReductionAccessibility n

theorem u0_redNormal (n : Nat) : RedNormal (.u0 : PureTm n) := by
  intro target step
  cases step

theorem u1_redNormal (n : Nat) : RedNormal (.u1 : PureTm n) := by
  intro target step
  cases step

/-- A closed, genuinely reducible example in the exact domain. -/
def regularIdentityU0 : PureTm 0 :=
  .app (.lam (.var 0)) .u0

theorem regularIdentityU0_constantFree : ConstantFree regularIdentityU0 := by
  exact .app (.lam (.var 0)) .u0

theorem regularIdentityU0_reduct_eq {target : PureTm 0}
    (step : Red regularIdentityU0 target) : target = .u0 := by
  cases step with
  | betaPi => rfl
  | congAppFun functionStep =>
      cases functionStep with
      | congLam bodyStep => cases bodyStep
  | congAppArg argumentStep => cases argumentStep

theorem regularIdentityU0_reductionAccessible :
    ReductionAccessible regularIdentityU0 := by
  constructor
  intro reduct step
  rw [regularIdentityU0_reduct_eq step]
  exact u0_reductionAccessible 0

/-- A transparent accessibility tree used by the executable example. -/
def regularIdentityU0ReductionAccessibility :
    ReductionAccessible regularIdentityU0 := by
  constructor
  intro reduct step
  cases step with
  | betaPi => exact u0ReductionAccessibility 0
  | congAppFun functionStep =>
      cases functionStep with
      | congLam bodyStep => cases bodyStep
  | congAppArg argumentStep => cases argumentStep

def accessibleIdentityU0 : accessibleNormalizationSpecification.Term 0 :=
  ⟨regularIdentityU0,
    regularIdentityU0ReductionAccessibility, regularIdentityU0_constantFree⟩

def accessibleU0 : accessibleNormalizationSpecification.Term 0 :=
  ⟨.u0, u0ReductionAccessibility 0, .u0⟩

def accessibleU1 : accessibleNormalizationSpecification.Term 0 :=
  ⟨.u1, u1ReductionAccessibility 0, .u1⟩

/-- The concrete normalizer performs the beta step rather than merely accepting
a relation supplied by the caller. -/
theorem accessible_normalize_identityU0 :
    accessibleNormalizationSpecification.normalize
      accessibleIdentityU0.1 accessibleIdentityU0.2 = .u0 := by
  apply normalForms_eq_of_conv
    (accessibleNormalizationSpecification.reduces
      accessibleIdentityU0.1 accessibleIdentityU0.2)
    (RedStar.refl .u0)
    (accessibleNormalizationSpecification.irreducible
      accessibleIdentityU0.1 accessibleIdentityU0.2)
    (u0_redNormal 0)
  exact Relation.EqvGen.rel _ _
    (Red.betaPi (.var 0) (.u0 : PureTm 0))

theorem accessible_normalize_u0 :
    accessibleNormalizationSpecification.normalize
      accessibleU0.1 accessibleU0.2 = .u0 := by
  exact (u0_redNormal 0).redStar_eq
    (accessibleNormalizationSpecification.reduces
      accessibleU0.1 accessibleU0.2)

theorem accessible_normalize_u1 :
    accessibleNormalizationSpecification.normalize
      accessibleU1.1 accessibleU1.2 = .u1 := by
  exact (u1_redNormal 0).redStar_eq
    (accessibleNormalizationSpecification.reduces
      accessibleU1.1 accessibleU1.2)

/-- Positive exact-decision witness: the reducible identity application and
its normal form are accepted as convertible. -/
theorem accessible_decides_identityU0_u0 :
    (accessibleNormalizationSpecification.decidedConversion 0).decide
      accessibleIdentityU0 accessibleU0 = true := by
  rw [NormalizationSpecification.decidedConversion_is_direct,
    accessible_normalize_identityU0, accessible_normalize_u0]
  decide

/-- Negative exact-decision witness: the two universe constructors remain
distinct. -/
theorem accessible_rejects_u0_u1 :
    (accessibleNormalizationSpecification.decidedConversion 0).decide
      accessibleU0 accessibleU1 = false := by
  rw [NormalizationSpecification.decidedConversion_is_direct,
    accessible_normalize_u0, accessible_normalize_u1]
  decide

/-- The self-reducing untyped term is excluded from the concrete domain. -/
theorem regularOmega_not_accessibly_normalized :
    ¬ accessibleNormalizationSpecification.Domain regularOmega :=
  accessibleNormalizationSpecification.omega_not_in_domain

/-! ## Axiom audit -/

#print axioms reduceOnce_isSome_of_red
#print axioms reduceOnce_eq_none_iff_normal
#print axioms u0_reductionAccessible
#print axioms u1_reductionAccessible
#print axioms u0_redNormal
#print axioms u1_redNormal
#print axioms regularIdentityU0_constantFree
#print axioms regularIdentityU0_reduct_eq
#print axioms regularIdentityU0_reductionAccessible
#print axioms accessible_normalize_identityU0
#print axioms accessible_normalize_u0
#print axioms accessible_normalize_u1
#print axioms accessible_decides_identityU0_u0
#print axioms accessible_rejects_u0_u1
#print axioms regularOmega_not_accessibly_normalized

end Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary
