import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.Languages.MeTTa.PureKernel.RegularDefEq

/-!
# Exact normalization boundary for regular Pure conversion

Confluence alone does not make conversion decidable, and a fuelled or one-pass
evaluator does not become complete by being called a normalizer.  This module
states the exact computational specification still required from regular Pure
normalization and proves that any implementation satisfying it induces an exact
NIK `DecidedRelation` for fragment-internal conversion.

An executable normalizer may first be constructed on any honest accessibility
domain.  An inhabitant of `RegularNormalizationSpecification` additionally
requires the strong-normalization theorem showing that the domain covers every
regular subject and type.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Confluence
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-- A term is in reduction normal form when it has no one-step reduct. -/
def RedNormal (term : PureTm n) : Prop :=
  ∀ target, ¬ Red term target

/-- A reduction path starting at a normal form is reflexive. -/
theorem RedNormal.redStar_eq {term target : PureTm n}
    (normal : RedNormal term) (steps : RedStar term target) : target = term := by
  induction steps with
  | refl => rfl
  | tail earlier finalStep ih =>
      have earlierEq := ih
      subst earlierEq
      exact False.elim (normal _ finalStep)

/-- Confluence makes reachable normal forms unique across conversion. -/
theorem normalForms_eq_of_conv
    {left right leftNormal rightNormal : PureTm n}
    (leftSteps : RedStar left leftNormal)
    (rightSteps : RedStar right rightNormal)
    (leftIrreducible : RedNormal leftNormal)
    (rightIrreducible : RedNormal rightNormal)
    (conversion : Mettapedia.Languages.MeTTa.PureKernel.Typing.Conv left right) :
    leftNormal = rightNormal := by
  have normalConversion :
      Mettapedia.Languages.MeTTa.PureKernel.Typing.Conv leftNormal rightNormal :=
    Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (redStar_implies_conv leftSteps))
      (Relation.EqvGen.trans _ _ _ conversion
        (redStar_implies_conv rightSteps))
  rcases church_rosser_conv normalConversion with
    ⟨common, leftCommon, rightCommon⟩
  have leftEq : common = leftNormal := leftIrreducible.redStar_eq leftCommon
  have rightEq : common = rightNormal := rightIrreducible.redStar_eq rightCommon
  exact leftEq.symm.trans rightEq

/-- The exact contract for normalization on an explicitly delimited domain.

`Domain` identifies the terms on which termination is established.  The
domain witness is a proposition and is erased from executable code. -/
structure NormalizationSpecification where
  Domain : {n : Nat} → PureTm n → Prop
  normalize : {n : Nat} → (term : PureTm n) → Domain term → PureTm n
  reduces : ∀ {n : Nat} (term : PureTm n) (covered : Domain term),
    RedStar term (normalize term covered)
  irreducible : ∀ {n : Nat} (term : PureTm n) (covered : Domain term),
    RedNormal (normalize term covered)
  fragment : ∀ {n : Nat} (term : PureTm n), Domain term → ConstantFree term

/-- A normalization domain covers regular Pure exactly when it contains both
sides of every regular typing judgment and the distinguished top sort.  This is
the strong-normalization boundary, separate from the evaluator itself. -/
structure RegularNormalizationSpecification extends NormalizationSpecification where
  covers_subject : ∀ {n : Nat} {Γ : Context.Ctx n} {term type : PureTm n},
    RegularJudgment Γ term type → Domain term
  covers_type : ∀ {n : Nat} {Γ : Context.Ctx n} {term type : PureTm n},
    RegularJudgment Γ term type → Domain type
  covers_u1 : ∀ n : Nat, Domain (.u1 : PureTm n)

/-! ### Why the domain must be typed

Declaration-freedom is a syntax boundary, not a termination theorem.  The
usual untyped self-application term is declaration-free and reduces to itself.
The following negative witness proves that no valid regular-normalization
specification can claim all declaration-free terms as its domain. -/

def regularOmegaBody : PureTm 1 :=
  .app (.var 0) (.var 0)

def regularDelta : PureTm 0 :=
  .lam regularOmegaBody

def regularOmega : PureTm 0 :=
  .app regularDelta regularDelta

theorem regularOmega_constantFree : ConstantFree regularOmega := by
  exact .app (.lam (.app (.var 0) (.var 0)))
    (.lam (.app (.var 0) (.var 0)))

theorem regularDelta_normal : RedNormal regularDelta := by
  intro target step
  cases step with
  | congLam bodyStep =>
      cases bodyStep with
      | congAppFun variableStep => cases variableStep
      | congAppArg variableStep => cases variableStep

theorem regularOmega_reduces_to_self : Red regularOmega regularOmega := by
  simpa [regularOmega, regularDelta, regularOmegaBody, inst0, subst, subst0] using
    (Red.betaPi regularOmegaBody regularDelta)

theorem regularOmega_reduct_eq {target : PureTm 0}
    (step : Red regularOmega target) : target = regularOmega := by
  cases step with
  | betaPi =>
      simp [regularOmega, regularDelta, regularOmegaBody, inst0, subst, subst0]
  | congAppFun deltaStep =>
      exact False.elim (regularDelta_normal _ deltaStep)
  | congAppArg deltaStep =>
      exact False.elim (regularDelta_normal _ deltaStep)

theorem regularOmega_redStar_eq {target : PureTm 0}
    (steps : RedStar regularOmega target) : target = regularOmega := by
  induction steps with
  | refl => rfl
  | tail earlier finalStep ih =>
      subst ih
      exact regularOmega_reduct_eq finalStep

/-- A valid normalization specification cannot include the untyped looping
term.  This rules out the tempting but false domain `ConstantFree`. -/
theorem NormalizationSpecification.omega_not_in_domain
    (specification : NormalizationSpecification) :
    ¬ specification.Domain regularOmega := by
  intro covered
  have targetEq := regularOmega_redStar_eq
    (specification.reduces regularOmega covered)
  have normal := specification.irreducible regularOmega covered
  rw [targetEq] at normal
  exact normal regularOmega regularOmega_reduces_to_self

namespace NormalizationSpecification

/-- Runtime terms paired, only in the theorem layer, with evidence that the
normalizer's termination theorem covers them. -/
abbrev Term (specification : NormalizationSpecification) (n : Nat) :=
  {term : PureTm n // specification.Domain term}

/-- The declarative relation decided by a regular normalizer. -/
def Converts (specification : NormalizationSpecification)
    (left right : specification.Term n) : Prop :=
  ConstantFreeConv left.1 right.1

/-- Equal computed normal forms yield fragment-internal conversion. -/
theorem converts_of_normalize_eq
    (specification : NormalizationSpecification)
    {left right : specification.Term n}
    (equal : specification.normalize left.1 left.2 =
      specification.normalize right.1 right.2) :
    specification.Converts left right := by
  have leftPath := (specification.fragment left.1 left.2).redStar
    (specification.reduces left.1 left.2)
  have rightPath := (specification.fragment right.1 right.2).redStar
    (specification.reduces right.1 right.2)
  exact .trans leftPath.1 (.symm (equal ▸ rightPath.1))

/-- Fragment-internal conversion yields equal computed normal forms. -/
theorem normalize_eq_of_converts
    (specification : NormalizationSpecification)
    {left right : specification.Term n}
    (conversion : specification.Converts left right) :
    specification.normalize left.1 left.2 =
      specification.normalize right.1 right.2 := by
  exact normalForms_eq_of_conv
    (specification.reduces left.1 left.2)
    (specification.reduces right.1 right.2)
    (specification.irreducible left.1 left.2)
    (specification.irreducible right.1 right.2)
    conversion.toConv

/-- Exact normalization characterization of regular fragment conversion. -/
theorem normalize_eq_iff_converts
    (specification : NormalizationSpecification)
    (left right : specification.Term n) :
    specification.normalize left.1 left.2 =
      specification.normalize right.1 right.2 ↔
      specification.Converts left right :=
  ⟨specification.converts_of_normalize_eq,
    specification.normalize_eq_of_converts⟩

/-- Any implementation meeting the normalization specification supplies the
exact certificate-free conversion decision required by NIK. -/
def decidedConversion (specification : NormalizationSpecification)
    (n : Nat) : DecidedRelation (specification.Term n) specification.Converts where
  decide := fun left right =>
    decide (specification.normalize left.1 left.2 =
      specification.normalize right.1 right.2)
  correct := by
    intro left right
    rw [decide_eq_true_eq]
    exact specification.normalize_eq_iff_converts left right

/-- The induced decision has no certificate input: it is definitionally direct
comparison of the two computed normal forms. -/
theorem decidedConversion_is_direct
    (specification : NormalizationSpecification) (n : Nat)
    (left right : specification.Term n) :
    (specification.decidedConversion n).decide left right =
      decide (specification.normalize left.1 left.2 =
        specification.normalize right.1 right.2) :=
  rfl

end NormalizationSpecification

/-! ## Axiom audit -/

#print axioms RedNormal.redStar_eq
#print axioms normalForms_eq_of_conv
#print axioms regularOmega_constantFree
#print axioms regularDelta_normal
#print axioms regularOmega_reduces_to_self
#print axioms regularOmega_reduct_eq
#print axioms regularOmega_redStar_eq
#print axioms NormalizationSpecification.omega_not_in_domain
#print axioms NormalizationSpecification.converts_of_normalize_eq
#print axioms NormalizationSpecification.normalize_eq_of_converts
#print axioms NormalizationSpecification.normalize_eq_iff_converts
#print axioms NormalizationSpecification.decidedConversion_is_direct

end Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary
