import Mettapedia.TypeTheory.DependentFamilyObserverFactorization
import Mathlib.Data.Setoid.Basic

/-!
# Sections and total spaces of descending dependent families

A factorization of a family through an observation does not make every term
of that family observation-invariant. The sections on the observed base are
exactly the source sections whose identified values agree inside each observation
fibre. A supplied split readout constructs this equivalence without choosing
representatives implicitly.

The corresponding total-space observation is generally lossy. Its kernel
quotient, rather than the unquotiented source total space, is equivalent to the
observed total space. Reindexing along a commuting square preserves the term
comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentFamilySectionDescent

open Mettapedia.TypeTheory.ExtensionalReadout
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization

universe uSource uTarget uFibre uSource' uTarget'

variable {Source : Type uSource} {Target : Type uTarget}
variable {observe : Source → Target} {family : Source → Type uFibre}

/-- Equality transport commutes with forming the dependent pair. -/
theorem sigma_mk_cast {B : Target → Type uFibre} {x y : Target}
    (e : x = y) (value : B x) :
    (⟨y, cast (congrArg B e) value⟩ : Sigma B) = ⟨x, value⟩ := by
  cases e
  rfl

/-- A dependent section respects equality transport in its base. -/
theorem cast_section {B : Target → Type uFibre} {x y : Target}
    (e : x = y) (term : ∀ target, B target) :
    cast (congrArg B e) (term x) = term y := by
  cases e
  rfl

/-- A term's value together with its observed base point. -/
def sectionObservation (d : FamilyFactorization observe family)
    (term : ∀ source, family source) (source : Source) : Sigma d.targetFamily :=
  d.totalObservation ⟨source, term source⟩

/-- The identified values of a term agree inside each observation fibre.
This condition applies to the selected term, not to all source terms. -/
def Compatible (d : FamilyFactorization observe family)
    (term : ∀ source, family source) : Prop :=
  ∀ left right, observe left = observe right →
    sectionObservation d term left = sectionObservation d term right

/-- Pull an observed term back through the actual fibre equivalences. -/
def liftSection (d : FamilyFactorization observe family)
    (term : ∀ target, d.targetFamily target) : ∀ source, family source :=
  fun source => (d.identify source).symm (term (observe source))

@[simp] theorem observe_liftSection (d : FamilyFactorization observe family)
    (term : ∀ target, d.targetFamily target) (source : Source) :
    sectionObservation d (liftSection d term) source =
      ⟨observe source, term (observe source)⟩ := by
  simp [sectionObservation, FamilyFactorization.totalObservation, liftSection]

/-- Every term pulled back from the observed base is compatible. -/
theorem liftSection_compatible (d : FamilyFactorization observe family)
    (term : ∀ target, d.targetFamily target) : Compatible d (liftSection d term) := by
  intro left right same
  simp only [observe_liftSection]
  exact congrArg (fun target => (⟨target, term target⟩ : Sigma d.targetFamily)) same

section Split

variable (readout : SplitReadout Source Target)
variable (d : FamilyFactorization readout.observe family)

/-- Evaluate at a supplied representative, then transport to its observed base. -/
def descendSection (term : ∀ source, family source) (target : Target) :
    d.targetFamily target :=
  cast (congrArg d.targetFamily (readout.observe_representative target))
    (d.identify (readout.representative target) (term (readout.representative target)))

theorem pair_descendSection (term : ∀ source, family source) (target : Target) :
    (⟨target, descendSection readout d term target⟩ : Sigma d.targetFamily) =
      sectionObservation d term (readout.representative target) :=
  sigma_mk_cast (readout.observe_representative target) _

/-- Descent after pullback returns the original term on the observed base. -/
@[simp] theorem descend_liftSection (term : ∀ target, d.targetFamily target) :
    descendSection readout d (liftSection d term) = term := by
  funext target
  have pairs := (pair_descendSection readout d (liftSection d term) target).trans
    (observe_liftSection d term (readout.representative target))
  have back :
      (⟨readout.observe (readout.representative target),
          term (readout.observe (readout.representative target))⟩ : Sigma d.targetFamily) =
        ⟨target, term target⟩ := by
    exact congrArg (fun target => (⟨target, term target⟩ : Sigma d.targetFamily))
      (readout.observe_representative target)
  exact eq_of_heq (Sigma.mk.inj_iff.mp (pairs.trans back)).2

/-- A compatible source term is recovered exactly after descent and pullback. -/
theorem lift_descendSection (term : ∀ source, family source)
    (compatible : Compatible d term) :
    liftSection d (descendSection readout d term) = term := by
  funext source
  apply (d.identify source).injective
  rw [liftSection, Equiv.apply_symm_apply]
  have pairs :=
    (pair_descendSection readout d term (readout.observe source)).trans
      (compatible source (readout.representative (readout.observe source))
        (readout.observe_representative _).symm).symm
  exact eq_of_heq (Sigma.mk.inj_iff.mp pairs).2

/-- The exact term-descent criterion. No assumption of universal proof
irrelevance or universal family descent is made. -/
theorem compatible_iff_lift_descend (term : ∀ source, family source) :
    Compatible d term ↔
      liftSection d (descendSection readout d term) = term := by
  constructor
  · exact lift_descendSection readout d term
  · intro same
    rw [← same]
    exact liftSection_compatible d _

/-- Sections on the observed base are exactly compatible source sections. -/
def sectionEquiv :
    (∀ target, d.targetFamily target) ≃
      {term : ∀ source, family source // Compatible d term} where
  toFun term := ⟨liftSection d term, liftSection_compatible d term⟩
  invFun term := descendSection readout d term.1
  left_inv := descend_liftSection readout d
  right_inv term := Subtype.ext (lift_descendSection readout d term.1 term.2)

/-- The kernel relation identifies exactly equal observed dependent pairs. -/
def totalSetoid : Setoid (Sigma family) := Setoid.ker d.totalObservation

/-- A representative of an observed dependent pair, using only the supplied
base representative and inverse fibre equivalence. -/
def totalRepresentative (value : Sigma d.targetFamily) : Sigma family :=
  ⟨readout.representative value.1,
    (d.identify (readout.representative value.1)).symm
      (cast (congrArg d.targetFamily (readout.observe_representative value.1).symm) value.2)⟩

@[simp] theorem observe_totalRepresentative (value : Sigma d.targetFamily) :
    d.totalObservation (totalRepresentative readout d value) = value := by
  obtain ⟨target, value⟩ := value
  dsimp [totalRepresentative, FamilyFactorization.totalObservation]
  rw [Equiv.apply_symm_apply]
  exact sigma_mk_cast (readout.observe_representative target).symm value

/-- The total-space kernel quotient has exactly the observed dependent values. -/
def totalQuotientEquiv :
    Quotient (totalSetoid readout d) ≃ Sigma d.targetFamily where
  toFun := Quotient.lift d.totalObservation (fun _ _ same => same)
  invFun value := Quotient.mk _ (totalRepresentative readout d value)
  left_inv := by
    intro value
    induction value using Quotient.inductionOn with
    | h value =>
      apply Quotient.sound
      exact observe_totalRepresentative readout d (d.totalObservation value)
  right_inv := observe_totalRepresentative readout d

@[simp] theorem totalQuotientEquiv_mk (value : Sigma family) :
    totalQuotientEquiv readout d (Quotient.mk _ value) = d.totalObservation value := rfl

end Split

section Reindex

variable {Source' : Type uSource'} {Target' : Type uTarget'}
variable (d : FamilyFactorization observe family)
variable (sourceMap : Source' → Source) (observe' : Source' → Target')
variable (targetMap : Target' → Target)
variable (commutes : ∀ source, observe (sourceMap source) = targetMap (observe' source))

/-- Equality induces an equivalence by equality elimination alone. -/
def equalityEquiv {A B : Type uFibre} (same : A = B) : A ≃ B := by
  cases same
  exact Equiv.refl A

theorem equalityEquiv_apply_heq {A B : Type uFibre} (same : A = B) (value : A) :
    HEq (equalityEquiv same value) value := by
  cases same
  rfl

@[simp] theorem equalityEquiv_symm_apply {A B : Type uFibre} (same : A = B) (value : B) :
    (equalityEquiv same).symm value = cast same.symm value := by
  cases same
  rfl

/-- Pull a family interpretation back along a commuting substitution square.
The equality comparison uses equality elimination rather than a classical
proof of the inverse laws. -/
def reindexFamily :
    FamilyFactorization observe' (fun source => family (sourceMap source)) where
  targetFamily := fun target => d.targetFamily (targetMap target)
  identify source := (d.identify (sourceMap source)).trans
    (equalityEquiv (congrArg d.targetFamily (commutes source)))

/-- Pullback of an observed term commutes with reindexing the actual family
factorization along the given square. -/
theorem liftSection_reindex (term : ∀ target, d.targetFamily target) :
    liftSection (reindexFamily d sourceMap observe' targetMap commutes)
        (fun target => term (targetMap target)) =
      fun source => liftSection d term (sourceMap source) := by
  funext source
  change (d.identify (sourceMap source)).symm
      ((equalityEquiv (congrArg d.targetFamily (commutes source))).symm
        (term (targetMap (observe' source)))) =
    (d.identify (sourceMap source)).symm (term (observe (sourceMap source)))
  congr 1
  rw [equalityEquiv_symm_apply]
  exact cast_section (commutes source).symm term

/-- A compatible term remains compatible under a commuting source/target
substitution square, without requiring representatives of observed points. -/
theorem compatible_reindex (term : ∀ source, family source)
    (compatible : Compatible d term) :
    Compatible (reindexFamily d sourceMap observe' targetMap commutes)
      (fun source => term (sourceMap source)) := by
  intro left right same
  have originalSame : observe (sourceMap left) = observe (sourceMap right) :=
    (commutes left).trans ((congrArg targetMap same).trans (commutes right).symm)
  have values := (Sigma.mk.inj_iff.mp
    (compatible (sourceMap left) (sourceMap right) originalSame)).2
  change (⟨observe' left,
    equalityEquiv (congrArg d.targetFamily (commutes left))
      (d.identify (sourceMap left) (term (sourceMap left)))⟩ :
      Sigma (fun target => d.targetFamily (targetMap target))) =
    ⟨observe' right,
      equalityEquiv (congrArg d.targetFamily (commutes right))
        (d.identify (sourceMap right) (term (sourceMap right)))⟩
  exact Sigma.mk.inj_iff.mpr ⟨same,
    (equalityEquiv_apply_heq _ _).trans
      (values.trans (equalityEquiv_apply_heq _ _).symm)⟩

end Reindex

end Mettapedia.TypeTheory.DependentFamilySectionDescent
