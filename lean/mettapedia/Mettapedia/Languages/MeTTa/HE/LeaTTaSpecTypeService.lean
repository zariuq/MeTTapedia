import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationRecursiveExact
import Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-!
# Exact prepared-package recovery for the repaired runtime type service

The published evaluator consumes ordered atom presentations, while repaired
LeaTTa first prepares an atom against the live space and its inferred
candidates carry private finite-substitution provenance.  Preparation is an
abstract relation in this conformance layer: neither the published service nor
the evaluator judgments mention LeaTTa's `World`.

`PackagesPresent` is the package-recovery boundary after preparation.
`PreparedPackagesPresent` composes it with the abstract preparation oracle.
Functionality and totality are separate instance laws rather than fields of
the oracle, so partial preparation models remain expressible and no future
space-algebra law is assumed in advance.

The generic service builder at the end keeps the published service carrier
unchanged.  A runtime candidate scan must recover the operator packages
through this boundary and then consume those packages directly.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaSpecTypeService

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.Exact
open Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation
open Spec.Eval
open LeaTTaBridge
open LeaTTaTypeConformance
open LeaTTaTypePresentationApplicationExact
open LeaTTaTypePresentationRecursiveExact

/-! ## Abstract preparation boundary -/

/-- Runtime-specific type preparation, stated over the independent space and
atom languages.  This carrier deliberately asserts neither totality nor
functionality; concrete instances establish exactly the laws they support. -/
structure TypePreparationOracle where
  prepare : Space → Atom → Atom → Prop

/-- Preparation is functional when one source atom has at most one prepared
presentation in a fixed space. -/
def TypePreparationFunctional (oracle : TypePreparationOracle) : Prop :=
  ∀ space atom left right,
    oracle.prepare space atom left →
      oracle.prepare space atom right → left = right

/-- Preparation is total when every source atom has a prepared presentation.
This law is needed by completeness, not by the service carrier itself. -/
def TypePreparationTotal (oracle : TypePreparationOracle) : Prop :=
  ∀ space atom, ∃ prepared, oracle.prepare space atom prepared

/-! ## Shared type-service scopes -/

/-- Names whose observations survive one complete type-service call.  This
scope is executable-independent: it contains the space theory and the public
atom/expected-type boundary, but no runtime state or generated name. -/
def typeServiceObservationScope
    (space : Space) (atom expectedType : Atom) : List String :=
  TypeSubst.typeVarsList (space.atoms ++ [atom, expectedType])

/-- The complete finite set avoided by private type candidates introduced at
one type-service boundary. -/
def typeServicePrivateAvoid
    (space : Space) (atom expectedType : Atom)
    (bindings : Bindings) : List String :=
  typeServiceObservationScope space atom expectedType ++
    specBindingVars bindings

/-- One ordered atom presentation together with the exact package list from
which it was observed.  The final relation permits only private injective
alpha-renaming; order and multiplicity remain exact. -/
def PackagesPresent
    (space : Space) (atom : Atom) (presented : List Atom) : Prop :=
  ∃ packages,
    RuntimeTypePackagesRel space atom packages ∧
      List.Forall₂ ObservedTypeAlphaRel
        (observedTypes packages) presented

/-- Exact package presentation after one abstract preparation step.  Only the
repaired runtime service uses this relation; the published textual service
continues to use `TypesOfRel` directly. -/
def PreparedPackagesPresent (oracle : TypePreparationOracle)
    (space : Space) (atom : Atom) (presented : List Atom) : Prop :=
  ∃ prepared,
    oracle.prepare space atom prepared ∧
      PackagesPresent space prepared presented

/-! ## Exact prepared type cast -/

/-- Declaration-ordered first successful native type match.  Failure of a
head candidate is explicit and selection commits as soon as a head succeeds;
there is no post-success backtracking. -/
inductive FirstTypeCastSuccessRel
    (expectedType : Atom) (bindings : Bindings) :
    List Atom → Bindings → Prop where
  | head {actualType : Atom} {candidates : List Atom} {output : Bindings} :
      CorePlusR2TypeMatchRel expectedType actualType bindings output →
      FirstTypeCastSuccessRel expectedType bindings
        (actualType :: candidates) output
  | tail {actualType : Atom} {candidates : List Atom} {output : Bindings} :
      (∀ candidate,
        ¬CorePlusR2TypeMatchRel
          expectedType actualType bindings candidate) →
      FirstTypeCastSuccessRel expectedType bindings candidates output →
      FirstTypeCastSuccessRel expectedType bindings
        (actualType :: candidates) output

/-- The former split presentation of first-success evidence constructs the
structural fold without changing candidate order or the commit point. -/
theorem FirstTypeCastSuccessRel.of_split
    {expectedType : Atom} {bindings output : Bindings}
    {candidates before after : List Atom} {actualType : Atom}
    (split : candidates = before ++ actualType :: after)
    (beforeFailed : ∀ earlier ∈ before, ∀ candidate,
      ¬CorePlusR2TypeMatchRel
        expectedType earlier bindings candidate)
    (selected : CorePlusR2TypeMatchRel
      expectedType actualType bindings output) :
    FirstTypeCastSuccessRel expectedType bindings candidates output := by
  subst candidates
  induction before with
  | nil => simpa using FirstTypeCastSuccessRel.head selected
  | cons earlier before inductionHypothesis =>
      apply FirstTypeCastSuccessRel.tail
      · exact beforeFailed earlier (by simp)
      · apply inductionHypothesis
        intro candidate member
        exact beforeFailed candidate (by simp [member])

/-- Exact `type_cast` over an ordered, privately localized type presentation.

Preparation and package lookup remain relational.  `ArgumentAlphaVariantsRel`
is reused as the neutral left-to-right freshening relation for the candidate
list: its growing avoid set preserves declaration order and separates private
variables without naming a generator.  Matching follows the reference
interpreter's semantically relevant `(expected, actual)` operand order. -/
inductive PreparedTypeCastRel (oracle : TypePreparationOracle)
    (space : Space) (atom expectedType : Atom)
    (bindings : Bindings) : ResultPair →
      (protectedScope : List String := []) → Prop where
  | success {sourceCandidates candidates : List Atom}
      {output : Bindings} :
      PreparedPackagesPresent oracle space atom sourceCandidates →
      ArgumentAlphaVariantsRel
        (protectedScope ++
          typeServicePrivateAvoid space atom expectedType bindings)
        sourceCandidates candidates →
      FirstTypeCastSuccessRel expectedType bindings candidates output →
      PreparedTypeCastRel oracle space atom expectedType bindings
        (atom, output) protectedScope
  | failure {sourceCandidates candidates : List Atom}
      {actualType : Atom} :
      PreparedPackagesPresent oracle space atom sourceCandidates →
      ArgumentAlphaVariantsRel
        (protectedScope ++
          typeServicePrivateAvoid space atom expectedType bindings)
        sourceCandidates candidates →
      actualType ∈ candidates →
      (∀ candidateType ∈ candidates, ∀ candidate,
        ¬CorePlusR2TypeMatchRel
          expectedType candidateType bindings candidate) →
      PreparedTypeCastRel oracle space atom expectedType bindings
        (mkError atom (.badType expectedType actualType), bindings)
        protectedScope

/-- A cast derivation whose result atom is the unchanged source must be the
first-success case.  The failure constructor strictly increases atom size by
wrapping the source in `Error`, so it cannot inhabit this index. -/
theorem PreparedTypeCastRel.of_atom_result
    {oracle : TypePreparationOracle} {space : Space}
    {atom expectedType : Atom} {bindings output : Bindings}
    {protectedScope : List String}
    (cast : PreparedTypeCastRel oracle space atom expectedType bindings
      (atom, output) protectedScope) :
    ∃ sourceCandidates candidates,
      PreparedPackagesPresent oracle space atom sourceCandidates ∧
      ArgumentAlphaVariantsRel
        (protectedScope ++
          typeServicePrivateAvoid space atom expectedType bindings)
        sourceCandidates candidates ∧
      FirstTypeCastSuccessRel expectedType bindings candidates output := by
  generalize resultEquation : (atom, output) = result at cast
  cases cast with
  | success present variants first =>
      rename_i sourceCandidates candidates constructorOutput
      have outputEquation : output = constructorOutput := by
        simpa using congrArg Prod.snd resultEquation
      subst constructorOutput
      exact ⟨_, _, present, variants, first⟩
  | failure _present _variants _member _allFailed =>
      rename_i _sourceCandidates _candidates actualType
      have atomEquation : atom =
          mkError atom (.badType expectedType actualType) := by
        simpa using congrArg Prod.fst resultEquation
      have sizeEquation := congrArg sizeOf atomEquation
      simp [mkError, Atom.error, ErrorCode.toAtom] at sizeEquation
      omega

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

/-- A concrete runtime preparation equation realizes the abstract prepared
package interface.  The equation orientation is fixed for the later
space-algebra instance: executable preparation equals the translation of the
independent prepared atom. -/
theorem preparedPackagesPresent_runtimeGetTypes
    {oracle : TypePreparationOracle}
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    (world : Metta.Minimal.World) (atom prepared : Atom)
    (preparation : oracle.prepare space atom prepared)
    (preparationEquation :
      Metta.Minimal.typePrep world (toLeaTTaAtom atom) =
        toLeaTTaAtom prepared) :
    PreparedPackagesPresent oracle space atom
      (fromLeaTTaAtoms
        (Metta.Minimal.getTypes env
          (Metta.Minimal.typePrep world (toLeaTTaAtom atom)))) := by
  refine ⟨prepared, preparation, ?_⟩
  rw [preparationEquation]
  exact packagesPresent_runtimeGetTypes index prepared

/-- A total preparation instance supplies at least one exact candidate list
for every source atom. -/
theorem preparedPackagesPresent_exists
    {oracle : TypePreparationOracle}
    (total : TypePreparationTotal oracle)
    (space : Space) (atom : Atom) :
    ∃ presented, PreparedPackagesPresent oracle space atom presented := by
  obtain ⟨prepared, preparation⟩ := total space atom
  obtain ⟨presented, present⟩ := packagesPresent_exists space prepared
  exact ⟨presented, prepared, preparation, present⟩

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

/-- Functional preparation lifts package uniqueness across the complete
prepared lookup.  The exact candidate sequence therefore cannot differ
between a positive and a negative use of the runtime service. -/
theorem PreparedPackagesPresent.alpha_unique
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {atom : Atom} {left right : List Atom}
    (leftPresent : PreparedPackagesPresent oracle space atom left)
    (rightPresent : PreparedPackagesPresent oracle space atom right) :
    List.Forall₂ ObservedTypeAlphaRel left right := by
  obtain ⟨leftPrepared, leftPreparation, leftPackages⟩ := leftPresent
  obtain ⟨rightPrepared, rightPreparation, rightPackages⟩ := rightPresent
  have preparedEquation := functional space atom leftPrepared rightPrepared
    leftPreparation rightPreparation
  subst rightPrepared
  exact PackagesPresent.alpha_unique index leftPackages rightPackages

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
interface.  The expression shape identifies the operator whose packages are
being recovered. -/
def RecoveredPackageCandidateScanRel
    (oracle : TypePreparationOracle)
    (packageScan :
      Space → Atom → Atom → Bindings →
        List TypePackage → FunctionCandidateScanOutcome → Prop)
    (space : Space) (expression expectedType : Atom)
    (bindings : Bindings) (presented : List Atom)
    (outcome : FunctionCandidateScanOutcome) : Prop :=
  ∃ operator arguments prepared packages,
    expression = .expression (operator :: arguments) ∧
      oracle.prepare space operator prepared ∧
      RuntimeTypePackagesRel space prepared packages ∧
      List.Forall₂ ObservedTypeAlphaRel
        (observedTypes packages) presented ∧
      packageScan space expression expectedType bindings packages outcome

/-- Build an evaluator type service whose atom-facing lookup is exact package
presentation and whose ordered scan is forced through package recovery. -/
def packageRecoveringTypeService
    (oracle : TypePreparationOracle)
    (typeCast : List String → Space → Atom → Atom → Bindings →
      ResultPair → Prop)
    (packageScan :
      Space → Atom → Atom → Bindings →
        List TypePackage → FunctionCandidateScanOutcome → Prop) :
    EvalTypeService where
  typesOf := PreparedPackagesPresent oracle
  typeCast := typeCast
  candidateScan := RecoveredPackageCandidateScanRel oracle packageScan

/-! ## Recovery canaries -/

private def identityPreparation : TypePreparationOracle where
  prepare := fun _ atom prepared => prepared = atom

private theorem identityPreparation_functional :
    TypePreparationFunctional identityPreparation := by
  intro space atom left right leftEquation rightEquation
  simpa [identityPreparation] using leftEquation.trans rightEquation.symm

private theorem identityPreparation_total :
    TypePreparationTotal identityPreparation := by
  intro space atom
  exact ⟨atom, rfl⟩

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

/-- Positive: identity preparation exposes the same mandatory singleton
undefined presentation through the exact runtime service boundary. -/
example : PreparedPackagesPresent identityPreparation Space.empty
    (.symbol "untyped") [Atom.undefinedType] := by
  refine ⟨.symbol "untyped", rfl, ?_⟩
  exact ⟨[publishedPackage Atom.undefinedType],
    RuntimeTypePackagesRel.symbolUndefined AnnotationTypesRel.nil,
    List.Forall₂.cons (ObservedTypeAlphaRel.refl _) List.Forall₂.nil⟩

/-- Negative: recovery cannot silently erase the mandatory undefined
candidate. -/
example : ¬PackagesPresent Space.empty (.symbol "untyped") [] := by
  rintro ⟨packages, packagesRel, alpha⟩
  have packagesEmpty : packages = [] := by
    apply List.length_eq_zero_iff.mp
    simpa [observedTypes] using alpha.length_eq
  exact packagesRel.nonempty packagesEmpty

/-- Negative: preparation cannot erase the mandatory undefined candidate. -/
example : ¬PreparedPackagesPresent identityPreparation Space.empty
    (.symbol "untyped") [] := by
  rintro ⟨prepared, preparation, present⟩
  have preparedEquation : prepared = .symbol "untyped" := by
    simpa [identityPreparation] using preparation
  subst prepared
  exact (show ¬PackagesPresent Space.empty (.symbol "untyped") [] from by
    rintro ⟨packages, packagesRel, alpha⟩
    have packagesEmpty : packages = [] := by
      apply List.length_eq_zero_iff.mp
      simpa [observedTypes] using alpha.length_eq
    exact packagesRel.nonempty packagesEmpty) present

end Mettapedia.Languages.MeTTa.HE.LeaTTaSpecTypeService
