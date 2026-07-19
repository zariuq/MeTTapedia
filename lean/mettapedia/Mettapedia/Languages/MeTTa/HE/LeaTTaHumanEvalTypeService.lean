import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationRecursiveExact
import Mettapedia.Languages.MeTTa.HE.HumanEvalSpec

/-!
# Exact package recovery for the repaired runtime type service

The published evaluator consumes ordered atom presentations, while repaired
LeaTTa's inferred candidates also carry private finite-substitution
provenance.  `PackagesPresent` is the single recovery boundary between those
views.  Recovery is total and functional up to private alpha-renaming, so a
negative candidate premise cannot choose a different package presentation
from its positive counterpart.

The generic service builder at the end keeps the published service carrier
unchanged.  A runtime candidate scan must recover the operator packages
through this boundary and then consume those packages directly.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaHumanEvalTypeService

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HumanTypeSpec
open HumanTypePresentation
open HumanTypePresentationAlpha
open HumanTypePresentationExact
open HumanEvalSpec
open LeaTTaBridge
open LeaTTaTypeConformance
open LeaTTaTypePresentationApplicationExact
open LeaTTaTypePresentationRecursiveExact

/-- One ordered atom presentation together with the exact package list from
which it was observed.  The final relation permits only private injective
alpha-renaming; order and multiplicity remain exact. -/
def PackagesPresent
    (space : Space) (atom : Atom) (presented : List Atom) : Prop :=
  ∃ packages,
    RuntimeTypePackagesRel space atom packages ∧
      List.Forall₂ ObservedTypeAlphaRel
        (observedTypes packages) presented

private theorem observedTypeAlphaList_refl (types : List Atom) :
    List.Forall₂ ObservedTypeAlphaRel types types := by
  induction types with
  | nil => exact List.Forall₂.nil
  | cons type types ih =>
      exact List.Forall₂.cons (ObservedTypeAlphaRel.refl type) ih

private theorem observedTypeAlphaList_symm
    {left right : List Atom}
    (alpha : List.Forall₂ ObservedTypeAlphaRel left right) :
    List.Forall₂ ObservedTypeAlphaRel right left := by
  induction alpha with
  | nil => exact List.Forall₂.nil
  | cons headAlpha _ tailIH =>
      exact List.Forall₂.cons headAlpha.symm tailIH

/-- Every independent atom has at least one exact presented candidate list. -/
theorem packagesPresent_exists (space : Space) (atom : Atom) :
    ∃ presented, PackagesPresent space atom presented := by
  obtain ⟨packages, packagesRel⟩ := runtimeTypePackages_exists space atom
  exact ⟨observedTypes packages, packages, packagesRel,
    observedTypeAlphaList_refl _⟩

/-- The complete concrete `getTypes` result realizes the recovery contract. -/
theorem packagesPresent_runtimeGetTypes
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env) (atom : Atom) :
    PackagesPresent space atom
      (fromLeaTTaAtoms
        (Metta.Minimal.getTypes env (toLeaTTaAtom atom))) := by
  obtain ⟨packages, packagesRel, alpha⟩ :=
    runtimeGetTypes_has_exact_package_presentation index atom
  exact ⟨packages, packagesRel, alpha⟩

/-- Two recoveries for one atom present alpha-equivalent lists.  In
particular, all alpha-invariant negative consumers quantify over one exact
candidate set rather than over a permissive union. -/
theorem PackagesPresent.alpha_unique
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {atom : Atom} {left right : List Atom}
    (leftPresent : PackagesPresent space atom left)
    (rightPresent : PackagesPresent space atom right) :
    List.Forall₂ ObservedTypeAlphaRel left right := by
  obtain ⟨leftPackages, leftRel, leftAlpha⟩ := leftPresent
  obtain ⟨rightPackages, rightRel, rightAlpha⟩ := rightPresent
  exact observedTypeAlphaList_trans
    (observedTypeAlphaList_trans
      (observedTypeAlphaList_symm leftAlpha)
      (runtimeTypePackages_alpha_unique
        index leftRel rightRel))
    rightAlpha

/-- Candidate-list length is part of the recovery contract. -/
theorem PackagesPresent.length_eq
    {space : Space} {atom : Atom} {presented : List Atom}
    (present : PackagesPresent space atom presented) :
    ∃ packages,
      RuntimeTypePackagesRel space atom packages ∧
        packages.length = presented.length := by
  obtain ⟨packages, packagesRel, alpha⟩ := present
  refine ⟨packages, packagesRel, ?_⟩
  simpa [observedTypes] using alpha.length_eq

/-- A package-level candidate scan recovered from the exact ordered atom
surface.  The expression shape identifies the operator whose packages are
being recovered. -/
def RecoveredPackageCandidateScanRel
    (packageScan :
      Space → Atom → Atom → Bindings →
        List TypePackage → FunctionCandidateScanOutcome → Prop)
    (space : Space) (expression expectedType : Atom)
    (bindings : Bindings) (presented : List Atom)
    (outcome : FunctionCandidateScanOutcome) : Prop :=
  ∃ operator arguments packages,
    expression = .expression (operator :: arguments) ∧
      RuntimeTypePackagesRel space operator packages ∧
      List.Forall₂ ObservedTypeAlphaRel
        (observedTypes packages) presented ∧
      packageScan space expression expectedType bindings packages outcome

/-- Build an evaluator type service whose atom-facing lookup is exact package
presentation and whose ordered scan is forced through package recovery. -/
def packageRecoveringTypeService
    (typeCast : Space → Atom → Atom → Bindings → ResultPair → Prop)
    (packageScan :
      Space → Atom → Atom → Bindings →
        List TypePackage → FunctionCandidateScanOutcome → Prop) :
    HumanEvalTypeService where
  typesOf := PackagesPresent
  typeCast := typeCast
  candidateScan := RecoveredPackageCandidateScanRel packageScan

/-! ## Recovery canaries -/

/-- Positive: an undeclared symbol has the exact singleton undefined
presentation. -/
example : PackagesPresent Space.empty (.symbol "untyped")
    [Atom.undefinedType] := by
  refine ⟨[publishedPackage Atom.undefinedType],
    RuntimeTypePackagesRel.symbolUndefined AnnotationTypesRel.nil, ?_⟩
  change List.Forall₂ ObservedTypeAlphaRel
    [Atom.undefinedType] [Atom.undefinedType]
  exact List.Forall₂.cons (ObservedTypeAlphaRel.refl _)
    List.Forall₂.nil

/-- Negative: recovery cannot silently erase the mandatory undefined
candidate. -/
example : ¬PackagesPresent Space.empty (.symbol "untyped") [] := by
  rintro ⟨packages, packagesRel, alpha⟩
  have packagesEmpty : packages = [] := by
    apply List.length_eq_zero_iff.mp
    simpa [observedTypes] using alpha.length_eq
  exact packagesRel.nonempty packagesEmpty

end Mettapedia.Languages.MeTTa.HE.LeaTTaHumanEvalTypeService
