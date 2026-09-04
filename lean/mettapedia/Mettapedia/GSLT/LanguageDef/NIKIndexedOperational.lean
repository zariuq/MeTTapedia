import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.LanguageDef.NIKGSLT

/-!
# External-certificate NIK diagrams as indexed operational GSLTs

An authored external-certificate authority diagram already contains more than
a behavioral map between checker machines: Boolean checking commutes, source
steps map to target steps, and every target step leaving a translated checker
state lifts to a source step.  These are exactly the obligations of a covered
operational translation.

This module exposes that fact once.  It gives an authority diagram the same
indexed operational command semantics and OSLF-generated native types as any
other covered GSLT diagram; it does not add a second checker relation or infer
semantic authority from operational replay.

Its scope is deliberately narrower than NIK itself.  Certificate-free native
decision, proof, construction, inference, and transformation services live in
the canonical `Mettapedia.GSLT.LanguageDef.NIK` doctrine.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKGSLT.Indexed

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority

universe uKind uClaim uCertificate uFormula uHom

/-! ## The authority-indexed evidence judgment -/

namespace InternalJudgment

variable {Kind : Type uKind} (family : AuthorityFamily Kind)

/-- The primitive judgment of the external-certificate subinterface:
authority `kind` accepts certificate `certificate` for claim `claim`.  A guest
logic may encode a hypothetical context inside `claim`, but this boundary does
not add one. -/
def Checks (kind : Kind) (claim : family.Claim kind)
    (certificate : family.Certificate kind) : Prop :=
  (family.checker kind).check claim certificate = true

/-- Proof-relevant evidence for one authority-indexed claim.  The Boolean
acceptance proof is retained together with the certificate that was checked. -/
abbrev Evidence (kind : Kind) (claim : family.Claim kind) :=
  { certificate : family.Certificate kind //
    Checks family kind claim certificate }

/-- One accepted claim-certificate pair in a selected authority fibre. -/
structure Accepted (kind : Kind) where
  claim : family.Claim kind
  certificate : family.Certificate kind
  accepted : Checks family kind claim certificate

@[ext]
theorem Accepted.ext {kind : Kind}
    {left right : Accepted family kind}
    (claimEq : left.claim = right.claim)
    (certificateEq : left.certificate = right.certificate) :
    left = right := by
  cases left
  cases right
  cases claimEq
  cases certificateEq
  rfl

/-- Exact checker authority says precisely that the evidence fibre is
inhabited for the declared certified scope. -/
theorem nonempty_evidence_iff_certified
    (kind : Kind) (claim : family.Claim kind) :
    Nonempty (Evidence family kind claim) <-> family.Certified kind claim := by
  constructor
  · rintro ⟨⟨certificate, accepted⟩⟩
    exact (family.projection kind).authority.sound claim certificate accepted
  · intro certified
    obtain ⟨certificate, accepted⟩ :=
      (family.projection kind).authority.complete claim certified
    exact ⟨⟨certificate, accepted⟩⟩

/-- An inhabited NIK evidence fibre projects soundly into the hosted guest
meaning.  Completeness for that broader meaning is deliberately not claimed. -/
theorem nonempty_evidence_implies_meaning
    (kind : Kind) (claim : family.Claim kind) :
    Nonempty (Evidence family kind claim) -> family.Meaning kind claim := by
  intro inhabited
  exact (family.projection kind).project claim
    ((nonempty_evidence_iff_certified family kind claim).mp inhabited)

/-- Packing a dependent authority family into one tagged replay checker does
not change any same-authority judgment. -/
theorem checks_iff_packed_sameKind [DecidableEq Kind]
    (kind : Kind) (claim : family.Claim kind)
    (certificate : family.Certificate kind) :
    Checks family kind claim certificate <->
      family.packedChecker.check
        ⟨kind, claim⟩ ⟨kind, certificate⟩ = true := by
  simp [Checks]

/-! ### Fixed replay authorities are the singleton case -/

/-- Regard one exact replay authority as a one-fibre NIK family. -/
def singletonFamily
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate)
    (Certified Meaning : Claim -> Prop)
    (projection : checker.AuthorityProjection Certified Meaning) :
    AuthorityFamily Unit where
  Claim := fun _ => Claim
  Certificate := fun _ => Certificate
  checker := fun _ => checker
  Certified := fun _ => Certified
  Meaning := fun _ => Meaning
  projection := fun _ => projection

/-- Singleton embedding preserves the fixed replay judgment definitionally. -/
theorem singleton_checks_iff
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate)
    (Certified Meaning : Claim -> Prop)
    (projection : checker.AuthorityProjection Certified Meaning)
    (claim : Claim) (certificate : Certificate) :
    Checks (singletonFamily checker Certified Meaning projection) ()
        claim certificate <->
      checker.check claim certificate = true :=
  Iff.rfl

/-! ### Hypothetical judgments are an optional guest interface -/

/-- A guest logic may expose an ordered hypothesis context by encoding it in
the claim language of each authority.  This data is not derivable from a raw
checker family. -/
structure HypotheticalPresentation where
  Formula : Kind -> Type uFormula
  encode : (kind : Kind) -> List (Formula kind) -> Formula kind ->
    family.Claim kind

/-- Evidence for the guest judgment `kind ; context ⊢ certificate : goal`. -/
abbrev HypotheticalEvidence
    (presentation : HypotheticalPresentation.{uKind, uClaim, uCertificate,
      uFormula} family)
    (kind : Kind) (context : List (presentation.Formula kind))
    (goal : presentation.Formula kind) :=
  Evidence family kind (presentation.encode kind context goal)

/-- Proof-relevant structural operations, when a hosted guest calculus admits
them.  NIK requires none of these operations merely to replay evidence. -/
structure StructuralRules
    (presentation : HypotheticalPresentation.{uKind, uClaim, uCertificate,
      uFormula} family) where
  identity : forall (kind : Kind) (formula : presentation.Formula kind),
    HypotheticalEvidence family presentation kind [formula] formula
  weakening : forall (kind : Kind)
      (context : List (presentation.Formula kind))
      (goal extra : presentation.Formula kind),
    HypotheticalEvidence family presentation kind context goal ->
      HypotheticalEvidence family presentation kind (extra :: context) goal
  exchange : forall (kind : Kind)
      (context : List (presentation.Formula kind))
      (goal left right : presentation.Formula kind),
    HypotheticalEvidence family presentation kind
        (left :: right :: context) goal ->
      HypotheticalEvidence family presentation kind
        (right :: left :: context) goal
  contraction : forall (kind : Kind)
      (context : List (presentation.Formula kind))
      (goal repeated : presentation.Formula kind),
    HypotheticalEvidence family presentation kind
        (repeated :: repeated :: context) goal ->
      HypotheticalEvidence family presentation kind
        (repeated :: context) goal
  cut : forall (kind : Kind)
      (sourceContext targetContext : List (presentation.Formula kind))
      (cutFormula goal : presentation.Formula kind),
    HypotheticalEvidence family presentation kind sourceContext cutFormula ->
      HypotheticalEvidence family presentation kind
        (cutFormula :: targetContext) goal ->
      HypotheticalEvidence family presentation kind
        (sourceContext ++ targetContext) goal

/-- Weakening alone, isolated so its absence can be witnessed without
assuming any of the other structural rules. -/
def HasWeakening
    (presentation : HypotheticalPresentation.{uKind, uClaim, uCertificate,
      uFormula} family) :=
  forall (kind : Kind) (context : List (presentation.Formula kind))
    (goal extra : presentation.Formula kind),
    HypotheticalEvidence family presentation kind context goal ->
      HypotheticalEvidence family presentation kind (extra :: context) goal

def StructuralRules.hasWeakening
    {presentation : HypotheticalPresentation.{uKind, uClaim, uCertificate,
      uFormula} family}
    (rules : StructuralRules family presentation) :
    HasWeakening family presentation :=
  rules.weakening

end InternalJudgment

namespace CheckerTranslation

variable {Kind : Type uKind} {family : AuthorityFamily Kind}
    {source target : Kind}

/-- A lawful checker translation is an exact covered operational translation
between its two checker GSLTs. -/
def toCoveredTranslation
    (translation : CheckerTranslation family source target) :
    CoveredTranslation (fiberTheory family source)
      (fiberTheory family target) where
  mapTerm := translation.stateMap
  mapEquiv := by
    intro left right equivalent
    cases equivalent
    rfl
  cover :=
    { mapStep := translation.step_map
      liftStep := by
        intro state targetNext step
        obtain ⟨sourceNext, sourceStep, targetEq⟩ :=
          translation.step_cover step
        exact ⟨sourceNext, sourceStep, targetEq.symm⟩ }

@[simp]
theorem toCoveredTranslation_mapTerm
    (translation : CheckerTranslation family source target)
    (state : (fiberTheory family source).Term) :
    translation.toCoveredTranslation.mapTerm state =
      translation.stateMap state :=
  rfl

/-- A lawful authority translation pushes an accepted claim-certificate pair
to accepted evidence in the target authority. -/
def mapAccepted
    (translation : CheckerTranslation family source target)
    (evidence : InternalJudgment.Accepted family source) :
    InternalJudgment.Accepted family target where
  claim := translation.mapClaim evidence.claim
  certificate := translation.mapCertificate evidence.certificate
  accepted := translation.accepted_evidence_transports evidence.accepted

@[simp]
theorem mapAccepted_claim
    (translation : CheckerTranslation family source target)
    (evidence : InternalJudgment.Accepted family source) :
    (translation.mapAccepted evidence).claim =
      translation.mapClaim evidence.claim :=
  rfl

@[simp]
theorem mapAccepted_certificate
    (translation : CheckerTranslation family source target)
    (evidence : InternalJudgment.Accepted family source) :
    (translation.mapAccepted evidence).certificate =
      translation.mapCertificate evidence.certificate :=
  rfl

end CheckerTranslation

namespace AuthorityDiagram

variable {Index : Type uKind} [CategoryTheory.Category.{uHom} Index]
    (diagram : AuthorityDiagram.{uKind, uClaim, uCertificate, uHom} Index)

/-! ### Claims and accepted evidence as covariant indexed families -/

/-- Authored claim translation is a genuine covariant family over the
authority category. -/
def claimFunctor :
    CategoryTheory.Functor Index (Type (max uClaim uCertificate)) where
  obj kind := ULift.{uCertificate} (diagram.family.Claim kind)
  map route := TypeCat.ofHom fun claim =>
    ULift.up ((diagram.transport route).mapClaim claim.down)
  map_id kind := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro claim
    exact ULift.ext _ _ (diagram.mapClaim_id kind claim.down)
  map_comp earlier later := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro claim
    exact ULift.ext _ _ (diagram.mapClaim_comp earlier later claim.down)

/-- Accepted proof-relevant evidence is functorial exactly because the
authority diagram supplies checker commutation plus identity/composition laws. -/
def acceptedFunctor :
    CategoryTheory.Functor Index (Type (max uClaim uCertificate)) where
  obj kind := InternalJudgment.Accepted diagram.family kind
  map route := TypeCat.ofHom (diagram.transport route).mapAccepted
  map_id kind := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro evidence
    apply InternalJudgment.Accepted.ext
    · exact diagram.mapClaim_id kind evidence.claim
    · exact diagram.mapCertificate_id kind evidence.certificate
  map_comp earlier later := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro evidence
    apply InternalJudgment.Accepted.ext
    · exact diagram.mapClaim_comp earlier later evidence.claim
    · exact diagram.mapCertificate_comp earlier later evidence.certificate

/-- Forgetting a certificate to its claim is natural in the authority index.
This is the proved proof-to-claim projection; it does not by itself supply an
object logic or a universal property for all proof calculi. -/
def evidenceToClaim : acceptedFunctor diagram ⟶ claimFunctor diagram where
  app _ := TypeCat.ofHom fun evidence => ULift.up evidence.claim
  naturality _ _ _ := rfl

/-- Total category of an authority together with one accepted
claim-certificate pair. -/
abbrev AcceptedTotal := (acceptedFunctor diagram).Elements

/-- Forget accepted evidence and retain the authority that checked it. -/
def acceptedProjection :
    CategoryTheory.Functor (AcceptedTotal diagram) Index :=
  CategoryTheory.CategoryOfElements.π (acceptedFunctor diagram)

/-- Embed accepted evidence as an object of the total evidence category. -/
def acceptedObject (kind : Index)
    (evidence : (acceptedFunctor diagram).obj kind) :
    AcceptedTotal diagram :=
  ⟨kind, evidence⟩

/-- Canonical push-forward of accepted evidence along an authority route. -/
def pushforwardObject
    (object : AcceptedTotal diagram) {target : Index}
    (route : object.1 ⟶ target) : AcceptedTotal diagram :=
  ⟨target, (acceptedFunctor diagram).map route object.2⟩

/-- The canonical morphism from accepted evidence to its push-forward. -/
def pushforwardLift
    (object : AcceptedTotal diagram) {target : Index}
    (route : object.1 ⟶ target) :
    object ⟶ pushforwardObject diagram object route :=
  CategoryTheory.CategoryOfElements.homMk _ _ route rfl

/-- The chosen push-forward lift satisfies the full strongly cocartesian
unique-factorization property.  Thus the accepted-evidence category of
elements earns cocartesian transport; this property is not inferred for an
arbitrary unstructured family of authority tags. -/
instance pushforwardLift_isStronglyCocartesian
    (object : AcceptedTotal diagram) {target : Index}
    (route : object.1 ⟶ target) :
    (acceptedProjection diagram).IsStronglyCocartesian route
      (pushforwardLift diagram object route) where
  toIsHomLift := by
    change (acceptedProjection diagram).IsHomLift
      ((acceptedProjection diagram).map (pushforwardLift diagram object route))
      (pushforwardLift diagram object route)
    infer_instance
  universal_property' := by
    intro targetObject tailRoute candidate candidateLift
    letI : (acceptedProjection diagram).IsHomLift
        (CategoryTheory.CategoryStruct.comp route tailRoute) candidate :=
      candidateLift
    have baseEq :
        CategoryTheory.CategoryStruct.comp route tailRoute = candidate.val :=
      @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
        (acceptedProjection diagram) object targetObject
        (CategoryTheory.CategoryStruct.comp route tailRoute) candidate
        candidateLift
    let mediator : pushforwardObject diagram object route ⟶ targetObject :=
      CategoryTheory.CategoryOfElements.homMk _ _ tailRoute (by
        change (acceptedFunctor diagram).map tailRoute
            ((acceptedFunctor diagram).map route object.2) = targetObject.2
        calc
          _ = (acceptedFunctor diagram).map
                (CategoryTheory.CategoryStruct.comp route tailRoute) object.2 :=
              (CategoryTheory.Functor.map_comp_apply
                (acceptedFunctor diagram) route tailRoute object.2).symm
          _ = (acceptedFunctor diagram).map candidate.val object.2 := by
              exact congrArg
                (fun arrow => (acceptedFunctor diagram).map arrow object.2)
                baseEq
          _ = targetObject.2 := candidate.property)
    have mediatorLift :
        (acceptedProjection diagram).IsHomLift tailRoute mediator := by
      change (acceptedProjection diagram).IsHomLift
        ((acceptedProjection diagram).map mediator) mediator
      infer_instance
    have factor : CategoryTheory.CategoryStruct.comp
        (pushforwardLift diagram object route) mediator = candidate := by
      apply CategoryTheory.CategoryOfElements.ext
      exact baseEq
    refine ⟨mediator, ⟨mediatorLift, factor⟩, ?_⟩
    intro other properties
    letI : (acceptedProjection diagram).IsHomLift tailRoute other := properties.1
    have otherBase : tailRoute = (acceptedProjection diagram).map other :=
      @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
        (acceptedProjection diagram) (pushforwardObject diagram object route)
        targetObject tailRoute other properties.1
    change tailRoute = other.val at otherBase
    apply CategoryTheory.CategoryOfElements.ext
    change other.val = tailRoute
    exact otherBase.symm

/-- Injectivity of the evidence action along one authority route. -/
def EvidenceMapInjective {source target : Index}
    (route : source ⟶ target) : Prop :=
  Function.Injective ((acceptedFunctor diagram).map route)

/-- Pointwise injectivity of evidence transport at one accepted certificate. -/
def EvidenceMapInjectiveAt {source target : Index}
    (route : source ⟶ target)
    (evidence : (acceptedFunctor diagram).obj source) : Prop :=
  ∀ candidate,
    (acceptedFunctor diagram).map route candidate =
        (acceptedFunctor diagram).map route evidence →
      candidate = evidence

/-- If an authority route is injective at this accepted evidence, its
canonical push-forward lift also satisfies the strongly cartesian universal
property. -/
@[reducible] def pushforwardLift_isStronglyCartesian
    (object : AcceptedTotal diagram) {target : Index}
    (route : object.1 ⟶ target)
    (injectiveAt : EvidenceMapInjectiveAt diagram route object.2) :
    (acceptedProjection diagram).IsStronglyCartesian route
      (pushforwardLift diagram object route) where
  toIsHomLift := by
    change (acceptedProjection diagram).IsHomLift
      ((acceptedProjection diagram).map (pushforwardLift diagram object route))
      (pushforwardLift diagram object route)
    infer_instance
  universal_property' := by
    intro sourceObject prior candidate candidateLift
    letI : (acceptedProjection diagram).IsHomLift
        (CategoryTheory.CategoryStruct.comp prior route) candidate :=
      candidateLift
    have baseEq :
        CategoryTheory.CategoryStruct.comp prior route = candidate.val :=
      @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
        (acceptedProjection diagram) sourceObject
        (pushforwardObject diagram object route)
        (CategoryTheory.CategoryStruct.comp prior route) candidate
        candidateLift
    have evidenceEq :
        (acceptedFunctor diagram).map prior sourceObject.2 = object.2 := by
      apply injectiveAt
      have candidateEvidenceEq := candidate.property
      change (acceptedFunctor diagram).map candidate.val sourceObject.2 =
        (acceptedFunctor diagram).map route object.2 at candidateEvidenceEq
      rw [← baseEq] at candidateEvidenceEq
      exact (CategoryTheory.Functor.map_comp_apply
        (acceptedFunctor diagram) prior route sourceObject.2).symm.trans
          candidateEvidenceEq
    let mediator : sourceObject ⟶ object :=
      CategoryTheory.CategoryOfElements.homMk _ _ prior evidenceEq
    have mediatorLift :
        (acceptedProjection diagram).IsHomLift prior mediator := by
      change (acceptedProjection diagram).IsHomLift
        ((acceptedProjection diagram).map mediator) mediator
      infer_instance
    have factor : CategoryTheory.CategoryStruct.comp mediator
        (pushforwardLift diagram object route) = candidate := by
      apply CategoryTheory.CategoryOfElements.ext
      exact baseEq
    refine ⟨mediator, ⟨mediatorLift, factor⟩, ?_⟩
    intro other properties
    have otherBase : prior = (acceptedProjection diagram).map other :=
      @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
        (acceptedProjection diagram) sourceObject object prior other
        properties.1
    change prior = other.val at otherBase
    apply CategoryTheory.CategoryOfElements.ext
    change other.val = prior
    exact otherBase.symm

/-- Cartesianity of the canonical evidence push-forward forces injectivity of
the underlying evidence map. -/
theorem evidenceMapInjectiveAt_of_pushforwardLift_isCartesian
    (object : AcceptedTotal diagram) {target : Index}
    (route : object.1 ⟶ target)
    (cartesian : (acceptedProjection diagram).IsCartesian route
      (pushforwardLift diagram object route)) :
    EvidenceMapInjectiveAt diagram route object.2 := by
  intro left imageEq
  let leftObject : AcceptedTotal diagram := ⟨object.1, left⟩
  let candidate : leftObject ⟶ pushforwardObject diagram object route :=
    CategoryTheory.CategoryOfElements.homMk _ _ route imageEq
  have candidateLift :
      (acceptedProjection diagram).IsHomLift route candidate := by
    change (acceptedProjection diagram).IsHomLift
      ((acceptedProjection diagram).map candidate) candidate
    infer_instance
  letI : (acceptedProjection diagram).IsHomLift route candidate :=
    candidateLift
  letI : (acceptedProjection diagram).IsCartesian route
      (pushforwardLift diagram object route) := cartesian
  obtain ⟨mediator, ⟨mediatorLift, factor⟩, unique⟩ :=
    CategoryTheory.Functor.IsCartesian.universal_property
      (p := acceptedProjection diagram) (f := route)
      (φ := pushforwardLift diagram object route) candidate
  have baseEq : CategoryTheory.CategoryStruct.id object.1 =
      (acceptedProjection diagram).map mediator :=
    @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
      (acceptedProjection diagram) leftObject object
      (CategoryTheory.CategoryStruct.id object.1) mediator
      mediatorLift
  change CategoryTheory.CategoryStruct.id object.1 = mediator.val at baseEq
  have elementEq := mediator.property
  change (acceptedFunctor diagram).map mediator.val left = object.2 at elementEq
  rw [← baseEq] at elementEq
  rw [CategoryTheory.Functor.map_id_apply] at elementEq
  exact elementEq

/-- For the accepted-evidence category of elements, the canonical lift at one
evidence object is cartesian exactly when transport is injective at that
object. -/
theorem pushforwardLift_isCartesian_iff_evidenceMapInjectiveAt
    (object : AcceptedTotal diagram) {target : Index}
    (route : object.1 ⟶ target) :
    (acceptedProjection diagram).IsCartesian route
      (pushforwardLift diagram object route) ↔
      EvidenceMapInjectiveAt diagram route object.2 := by
  constructor
  · exact evidenceMapInjectiveAt_of_pushforwardLift_isCartesian
      diagram object route
  · intro injective
    letI : (acceptedProjection diagram).IsStronglyCartesian route
        (pushforwardLift diagram object route) :=
      pushforwardLift_isStronglyCartesian diagram object route injective
    infer_instance

/-- Global injectivity is exactly pointwise injectivity at every accepted
evidence object in the source authority. -/
theorem evidenceMapInjective_iff_forall_evidenceMapInjectiveAt
    {source target : Index} (route : source ⟶ target) :
    EvidenceMapInjective diagram route ↔
      ∀ evidence : (acceptedFunctor diagram).obj source,
        EvidenceMapInjectiveAt diagram route evidence := by
  constructor
  · intro injective evidence candidate imageEq
    exact injective imageEq
  · intro pointwise left right imageEq
    exact pointwise right left imageEq

/-- Consequently, every canonical push-forward lift along a fixed route is
cartesian exactly when evidence transport along that route is injective. -/
theorem all_pushforwardLifts_areCartesian_iff_evidenceMapInjective
    {source target : Index} (route : source ⟶ target) :
    (∀ evidence : (acceptedFunctor diagram).obj source,
      (acceptedProjection diagram).IsCartesian route
        (pushforwardLift diagram
          (⟨source, evidence⟩ : AcceptedTotal diagram) route)) ↔
      EvidenceMapInjective diagram route := by
  rw [evidenceMapInjective_iff_forall_evidenceMapInjectiveAt]
  constructor
  · intro cartesian evidence
    exact (pushforwardLift_isCartesian_iff_evidenceMapInjectiveAt diagram
      (⟨source, evidence⟩ : AcceptedTotal diagram) route).mp
        (cartesian evidence)
  · intro injectiveAt evidence
    exact (pushforwardLift_isCartesian_iff_evidenceMapInjectiveAt diagram
      (⟨source, evidence⟩ : AcceptedTotal diagram) route).mpr
        (injectiveAt evidence)

/-- Bijectivity of the evidence action along one authority route. -/
def EvidenceMapBijective {source target : Index}
    (route : source ⟶ target) : Prop :=
  Function.Bijective ((acceptedFunctor diagram).map route)

/-- Existence of strongly cartesian evidence lifts into every target evidence
object along one fixed authority route. -/
def HasStronglyCartesianLiftsAlong {source target : Index}
    (route : source ⟶ target) : Prop :=
  ∀ targetEvidence : (acceptedFunctor diagram).obj target,
    ∃ (sourceEvidence : (acceptedFunctor diagram).obj source)
      (lift : acceptedObject diagram source sourceEvidence ⟶
        acceptedObject diagram target targetEvidence),
      (acceptedProjection diagram).IsStronglyCartesian route lift

/-- Any cartesian lift in the accepted-evidence total category identifies its
domain evidence as the unique preimage of its target evidence. -/
theorem evidenceMapInjectiveAt_of_cartesianLift
    {source target : Index} (route : source ⟶ target)
    (sourceEvidence : (acceptedFunctor diagram).obj source)
    (targetEvidence : (acceptedFunctor diagram).obj target)
    (lift : acceptedObject diagram source sourceEvidence ⟶
      acceptedObject diagram target targetEvidence)
    (cartesian : (acceptedProjection diagram).IsCartesian route lift) :
    ∀ candidate,
      (acceptedFunctor diagram).map route candidate = targetEvidence →
        candidate = sourceEvidence := by
  intro candidate imageEq
  let candidateObject : AcceptedTotal diagram := ⟨source, candidate⟩
  let candidateLift : candidateObject ⟶
      acceptedObject diagram target targetEvidence :=
    CategoryTheory.CategoryOfElements.homMk _ _ route imageEq
  have candidateIsLift :
      (acceptedProjection diagram).IsHomLift route candidateLift := by
    change (acceptedProjection diagram).IsHomLift
      ((acceptedProjection diagram).map candidateLift) candidateLift
    infer_instance
  letI : (acceptedProjection diagram).IsHomLift route candidateLift :=
    candidateIsLift
  letI : (acceptedProjection diagram).IsCartesian route lift := cartesian
  obtain ⟨mediator, ⟨mediatorLift, factor⟩, unique⟩ :=
    CategoryTheory.Functor.IsCartesian.universal_property
      (p := acceptedProjection diagram) (f := route) (φ := lift)
      candidateLift
  have baseEq : CategoryTheory.CategoryStruct.id source =
      (acceptedProjection diagram).map mediator :=
    @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
      (acceptedProjection diagram) candidateObject
      (acceptedObject diagram source sourceEvidence)
      (CategoryTheory.CategoryStruct.id source) mediator mediatorLift
  change CategoryTheory.CategoryStruct.id source = mediator.val at baseEq
  have elementEq := mediator.property
  change (acceptedFunctor diagram).map mediator.val candidate =
    sourceEvidence at elementEq
  rw [← baseEq] at elementEq
  exact (CategoryTheory.Functor.map_id_apply
    (acceptedFunctor diagram) source candidate).symm.trans elementEq

/-- The accepted-evidence projection admits cartesian lifts along a route
exactly when that route transports evidence bijectively.  Forward
cocartesian transport needs no such reversibility hypothesis. -/
theorem hasStronglyCartesianLiftsAlong_iff_evidenceMapBijective
    {source target : Index} (route : source ⟶ target) :
    HasStronglyCartesianLiftsAlong diagram route ↔
      EvidenceMapBijective diagram route := by
  constructor
  · intro lifts
    constructor
    · intro left right imageEq
      obtain ⟨preimage, lift, stronglyCartesian⟩ :=
        lifts ((acceptedFunctor diagram).map route right)
      letI : (acceptedProjection diagram).IsStronglyCartesian route lift :=
        stronglyCartesian
      have leftEq : left = preimage :=
        evidenceMapInjectiveAt_of_cartesianLift diagram route preimage
          ((acceptedFunctor diagram).map route right) lift inferInstance
          left imageEq
      have rightEq : right = preimage :=
        evidenceMapInjectiveAt_of_cartesianLift diagram route preimage
          ((acceptedFunctor diagram).map route right) lift inferInstance
          right rfl
      exact leftEq.trans rightEq.symm
    · intro targetEvidence
      obtain ⟨sourceEvidence, lift, stronglyCartesian⟩ :=
        lifts targetEvidence
      letI : (acceptedProjection diagram).IsStronglyCartesian route lift :=
        stronglyCartesian
      have baseEq : route = (acceptedProjection diagram).map lift :=
        @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
          (acceptedProjection diagram)
          (acceptedObject diagram source sourceEvidence)
          (acceptedObject diagram target targetEvidence)
          route lift stronglyCartesian.toIsHomLift
      change route = lift.val at baseEq
      have evidenceEq := lift.property
      change (acceptedFunctor diagram).map lift.val sourceEvidence =
        targetEvidence at evidenceEq
      rw [← baseEq] at evidenceEq
      exact ⟨sourceEvidence, evidenceEq⟩
  · intro bijective targetEvidence
    obtain ⟨sourceEvidence, imageEq⟩ := bijective.2 targetEvidence
    subst targetEvidence
    let object : AcceptedTotal diagram := ⟨source, sourceEvidence⟩
    refine ⟨sourceEvidence, pushforwardLift diagram object route, ?_⟩
    exact pushforwardLift_isStronglyCartesian diagram object route
      (fun candidate equalImage => bijective.1 equalImage)

/-- The authority-bearing diagram, viewed in the stronger covered operational
category.  The objects and transition functions are definitionally the same
checker machines used by NIK. -/
def toCoveredOperationalDiagram : IndexedOperational.CoveredDiagram Index where
  obj kind := ⟨fiberTheory diagram.family kind⟩
  map route := (diagram.transport route).toCoveredTranslation
  map_id kind := by
    apply CoveredTranslation.ext
    funext state
    exact diagram.stateMap_id kind state
  map_comp earlier later := by
    apply CoveredTranslation.ext
    funext state
    exact diagram.stateMap_comp earlier later state

/-- Forget the local-reflection certificate to obtain the general forward
operational diagram consumed by the command calculus. -/
def toOperationalDiagram : IndexedOperational.Diagram Index :=
  diagram.toCoveredOperationalDiagram.toOperational

@[simp]
theorem toOperationalDiagram_obj (kind : Index) :
    (diagram.toOperationalDiagram.obj kind).theory =
      fiberTheory diagram.family kind :=
  rfl

@[simp]
theorem toOperationalDiagram_mapTerm
    {source target : Index} (route : source ⟶ target)
    (state : (fiberTheory diagram.family source).Term) :
    (diagram.toOperationalDiagram.map route).mapTerm state =
      (diagram.transport route).stateMap state :=
  rfl

/-- The single explicit command GSLT obtained from an authority diagram.
`via` is now language-visible control state, while fibre steps remain the
original checker transitions. -/
abbrev commandGSLT :=
  IndexedOperational.Command.commandGSLT diagram.toOperationalDiagram

/-- Every native NIK checker step embeds as an exact fibre step of the
indexed command GSLT. -/
theorem checkerStep_is_commandStep
    (kind : Index)
    {source target : (fiberTheory diagram.family kind).Term}
    (step : (fiberTheory diagram.family kind).Step source target) :
    (diagram.commandGSLT).Step
      (.at kind (Quotient.mk _ source))
      (.at kind (Quotient.mk _ target)) := by
  exact ⟨IndexedOperational.Command.Step.fibre
    (semanticStep_mk step)⟩

/-- Conversely, a command fibre step between authored checker states is an
actual step of the original NIK checker fibre.  Quotienting by the equality
equations of the atomic checker does not enlarge replay behavior. -/
theorem commandStep_between_checkerStates_iff
    (kind : Index)
    (source target : (fiberTheory diagram.family kind).Term) :
    (diagram.commandGSLT).Step
        (.at kind (Quotient.mk _ source))
        (.at kind (Quotient.mk _ target)) ↔
      (fiberTheory diagram.family kind).Step source target := by
  constructor
  · rintro ⟨commandStep⟩
    cases commandStep with
    | fibre semanticStep =>
        exact (semanticStep_mk_iff_step _ source target).mp semanticStep
  · exact diagram.checkerStep_is_commandStep kind

/-- The same checker step inhabits the exact target type generated by OSLF
for the unified NIK command machine. -/
theorem checkerStep_satisfies_generated_nativeType
    (kind : Index)
    {source target : (fiberTheory diagram.family kind).Term}
    (step : (fiberTheory diagram.family kind).Step source target) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      diagram.commandGSLT).satisfies
        (.at kind (Quotient.mk _ source))
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
          diagram.commandGSLT
          (.at kind (Quotient.mk _ target))).pred := by
  exact IndexedOperational.Command.fibre_satisfies_nativeType
    diagram.toOperationalDiagram (semanticStep_mk step)

/-- OSLF generates the predicate-valued native type of the exact NIK command
machine rather than a parallel hand-authored judgment language. -/
abbrev NativeType :=
  IndexedOperational.Command.NativeType diagram.toOperationalDiagram

end AuthorityDiagram

/-! ## Boundary canaries -/

namespace InternalJudgmentCanary

open InternalJudgment

/-! ### Structural rules are guest structure, not checker structure -/

def nonemptyContextChecker : Checker (List Unit) Unit where
  check context _ := !context.isEmpty

def NonemptyContext (context : List Unit) : Prop := context ≠ []

theorem nonemptyContextChecker_authority :
    nonemptyContextChecker.Authority NonemptyContext where
  sound := by
    intro context certificate accepted
    cases context with
    | nil => simp [nonemptyContextChecker] at accepted
    | cons => simp [NonemptyContext]
  complete := by
    intro context nonempty
    cases context with
    | nil => exact (nonempty rfl).elim
    | cons => exact ⟨(), rfl⟩

def nonemptyContextFamily : AuthorityFamily Unit where
  Claim := fun _ => List Unit
  Certificate := fun _ => Unit
  checker := fun _ => nonemptyContextChecker
  Certified := fun _ => NonemptyContext
  Meaning := fun _ => NonemptyContext
  projection := fun _ => nonemptyContextChecker_authority.toProjection

def nonemptyContextPresentation :
    HypotheticalPresentation nonemptyContextFamily where
  Formula := fun _ => Unit
  encode := fun _ context _ => context

/-- A small nontrivial hosted calculus: empty contexts are rejected, while
all five ordinary structural operations preserve its accepted evidence. -/
def nonemptyContextStructuralRules :
    StructuralRules nonemptyContextFamily nonemptyContextPresentation where
  identity := by
    intro kind formula
    exact ⟨(), rfl⟩
  weakening := by
    intro kind context goal extra evidence
    exact ⟨(), rfl⟩
  exchange := by
    intro kind context goal left right evidence
    exact ⟨(), rfl⟩
  contraction := by
    intro kind context goal repeated evidence
    exact ⟨(), rfl⟩
  cut := by
    intro kind sourceContext targetContext cutFormula goal sourceEvidence
      targetEvidence
    cases sourceContext with
    | nil =>
        have impossible := sourceEvidence.property
        simp [Checks, nonemptyContextPresentation, nonemptyContextFamily,
          nonemptyContextChecker] at impossible
    | cons => exact ⟨(), rfl⟩

theorem nonemptyContext_has_structuralRules :
    Nonempty (StructuralRules nonemptyContextFamily
      nonemptyContextPresentation) :=
  ⟨nonemptyContextStructuralRules⟩

def emptyContextChecker : Checker (List Unit) Unit where
  check context _ := context.isEmpty

def EmptyContext (context : List Unit) : Prop := context = []

theorem emptyContextChecker_authority :
    emptyContextChecker.Authority EmptyContext where
  sound := by
    intro context certificate accepted
    cases context with
    | nil => rfl
    | cons => simp [emptyContextChecker] at accepted
  complete := by
    intro context empty
    subst context
    exact ⟨(), rfl⟩

def emptyContextFamily : AuthorityFamily Unit where
  Claim := fun _ => List Unit
  Certificate := fun _ => Unit
  checker := fun _ => emptyContextChecker
  Certified := fun _ => EmptyContext
  Meaning := fun _ => EmptyContext
  projection := fun _ => emptyContextChecker_authority.toProjection

def emptyContextPresentation :
    HypotheticalPresentation emptyContextFamily where
  Formula := fun _ => Unit
  encode := fun _ context _ => context

/-- A lawful exact NIK authority can reject weakening.  Therefore weakening,
and hence the complete structural-rule bundle, is not a theorem of the NIK
waist alone. -/
theorem emptyContext_has_no_weakening :
    ¬ Nonempty (HasWeakening emptyContextFamily
      emptyContextPresentation) := by
  rintro ⟨weakening⟩
  have source : HypotheticalEvidence emptyContextFamily
      emptyContextPresentation () [] () := ⟨(), rfl⟩
  have target := weakening () [] () () source
  have impossible := target.property
  simp [Checks, emptyContextPresentation, emptyContextFamily,
    emptyContextChecker] at impossible

/-! ### Covariant evidence transport need not be reversible -/

inductive ProofEnrichmentKind where
  | source
  | target

def proofEnrichmentFamily : AuthorityFamily ProofEnrichmentKind where
  Claim := fun _ => Unit
  Certificate
    | .source => Unit
    | .target => Bool
  checker
    | .source => { check := fun _ _ => true }
    | .target => { check := fun _ _ => true }
  Certified := fun _ claim => claim = ()
  Meaning := fun _ claim => claim = ()
  projection := by
    intro kind
    cases kind <;> exact
      { authority :=
          { sound := by intro claim certificate accepted; cases claim; rfl
            complete := by intro claim meaningful; cases claim; exact ⟨default, rfl⟩ }
        project := by intro claim certified; exact certified }

/-- The target authority recognizes two distinct proof objects for the sole
claim, while the source recognizes one. -/
def proofEnrichmentTranslation :
    CheckerTranslation proofEnrichmentFamily .source .target where
  mapClaim := id
  mapCertificate := fun _ => false
  check_commutes := by intro claim certificate; rfl
  certified_preserved := by intro claim certified; exact certified
  meaning_preserved := by intro claim meaningful; exact meaningful

def targetTrueEvidence :
    Accepted proofEnrichmentFamily .target where
  claim := ()
  certificate := true
  accepted := rfl

/-- Lawful forward evidence transport can fail to cover target evidence.
Reverse/cartesian transport therefore requires additional hypotheses. -/
theorem proofEnrichment_mapAccepted_not_surjective :
    ¬ Function.Surjective proofEnrichmentTranslation.mapAccepted := by
  intro surjective
  obtain ⟨sourceEvidence, mapped⟩ := surjective targetTrueEvidence
  have certificateEq := congrArg Accepted.certificate mapped
  change false = true at certificateEq
  cases certificateEq

/-- The same evidence map is injective: forward transport preserves the sole
source proof even though it does not cover all target proofs. -/
theorem proofEnrichment_mapAccepted_injective :
    Function.Injective proofEnrichmentTranslation.mapAccepted := by
  intro left right _mappedEqual
  apply Accepted.ext
  · cases left.claim
    cases right.claim
    rfl
  · cases left.certificate
    cases right.certificate
    rfl

/-- Hence lawful authority translation does not imply bijective evidence
transport, the exact condition for cartesian lifts into every target proof. -/
theorem proofEnrichment_mapAccepted_not_bijective :
    ¬ Function.Bijective proofEnrichmentTranslation.mapAccepted := by
  intro bijective
  exact proofEnrichment_mapAccepted_not_surjective bijective.2

/-! ### Index erasure loses plural-authority judgments -/

/-- No single tag-erasing checker on the common payload carriers agrees with
both fibres of the positive/negative flip family.  Packing works because it
retains the authority tag; erasure does not. -/
theorem no_tag_erased_checker_preserves_both_flip_fibres :
    ¬ ∃ erased : Checker Bool Unit,
      (∀ claim certificate,
        erased.check claim certificate =
          (Mettapedia.GSLT.LanguageDef.NIKGSLT.Canary.flipFamily.checker
            .positive).check claim certificate) ∧
      (∀ claim certificate,
        erased.check claim certificate =
          (Mettapedia.GSLT.LanguageDef.NIKGSLT.Canary.flipFamily.checker
            .negative).check claim certificate) := by
  rintro ⟨erased, positiveAgreement, negativeAgreement⟩
  have positive := positiveAgreement true ()
  have negative := negativeAgreement true ()
  simp [Mettapedia.GSLT.LanguageDef.NIKGSLT.Canary.flipFamily] at positive negative
  rw [positive] at negative
  cases negative

end InternalJudgmentCanary

#print axioms AuthorityDiagram.commandStep_between_checkerStates_iff
#print axioms AuthorityDiagram.checkerStep_satisfies_generated_nativeType
#print axioms InternalJudgment.nonempty_evidence_iff_certified
#print axioms AuthorityDiagram.pushforwardLift_isStronglyCocartesian
#print axioms AuthorityDiagram.hasStronglyCartesianLiftsAlong_iff_evidenceMapBijective
#print axioms InternalJudgmentCanary.emptyContext_has_no_weakening
#print axioms InternalJudgmentCanary.proofEnrichment_mapAccepted_not_bijective
#print axioms InternalJudgmentCanary.no_tag_erased_checker_preserves_both_flip_fibres

end Mettapedia.GSLT.LanguageDef.NIKGSLT.Indexed
