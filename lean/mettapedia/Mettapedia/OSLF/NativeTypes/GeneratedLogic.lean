import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Semantics
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Substitution
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Reference
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Transfer
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Invariance
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Generated
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Controls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Finite
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FiniteControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateEquations
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateFreshEquations
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateFreshEquationsControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Certificates
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.EquationControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Exploration
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BoundedMorphism
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ClosedExploration
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SearchControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ClosedControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Verdicts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.VerdictControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Equivalence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.EquivalenceControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.StructuralEquivalence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.StructuralControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrder
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrderControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SyntacticEmbeddings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.MuEmbedding
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorEmbeddings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.DriverBridge
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorAgreement
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SplitMorphism
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBagReading
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBagControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ObservationAtoms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ObservationAtomsControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.LocalDriverReading
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PartrecDriverReading
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PartrecDriverReadingControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.LambdaDriverReading
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.LambdaDriverReadingControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoDriverReading
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoPresentations
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoDriverReadingControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.NormalizedDriverReading
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.NormalizedAuthoredReading
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.NormalizedAuthoredReadingControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.EmbeddingControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.VerdictCatalogue
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.VerdictCatalogueControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CountingControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Completeness
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CompletenessControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AcceptanceMatrix
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegions
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CompletenessModulo
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Resumption
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Persistence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegionControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalUnwrapControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SubstitutionControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ProtocolControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CalculusPresentation
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CalculusControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RegexControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.InstanceControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AlgebraCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartnerAdequacy
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartnerControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiStore
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiStoreControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiNamedAdequacy
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiNamedControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSyncPrenexForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSyncPrenexControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSyncPartnerAdequacy
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSumPrenexForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSumPrenexControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSumStore
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSumStoreControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSPartnerAdequacy
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSPartnerControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRepForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRepControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecPartners
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecPartnerAdequacy
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecPartnerControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ComputedNormalForm
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AlgebraTypedForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientNuForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientNuControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientCommForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientCommControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientContextLabels
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientContextControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Readings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.GroundSetReadings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.GroundSetForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HereditarySets
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembership
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RelationalTranslation
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipExtensional
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipKernel
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipTrinity
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipSentences
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipDerivations
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipRegions
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipProofs
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipProofTerms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCertificateControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HypersetGraphs
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ExactMorphism
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipHFUniverse
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.TwoLevelSetRules
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.TwoLevelSetRuleControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.NestedSetRules
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.NestedSetRuleControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FeatureControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureSetRules
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureFreshness
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureSteps
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureModulo
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureModuloControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySorted
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySortedControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySortedHigherOrder
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySortedStructural
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PresheafReading
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.OpenTerms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Judgments
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.EntailmentHigherOrder
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.JudgmentControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PresheafControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.DependentJudgments
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.DependentJudgmentControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BackwardReach
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ExploredDecider
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ExploredControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCrossing
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCrossingControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Hints
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ScopedCongruences
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCountedTypes
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCountedFormers
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCountedFixedPoints
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCountedDecision
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCountedControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipRepresentatives
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPracticalStage
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetDriver
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModelLanguage
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModelEquality
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModelSteps
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModelAgreement
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModelReading
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModelReadingControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetDriverControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetDriverCertified
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.EngineAgreement
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ObservedSystems
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RelationalAnswerFrontDoor
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PathSystems
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SortWitnesses
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.StaticDecider
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ContextLabels
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.TokenNets
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.TokenNetAdequacy
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.TokenNetDistinctions
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PresentedContexts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PresentedContextControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ForwardEquivalence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoPartnerAdequacy
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoPartnerControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoLeastPartners
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoLeastPartnerControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiLeastPartners
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiMoleculeSoundness
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiMoleculeHarmony
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiLeastPartnerControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiMoleculeCongruence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiMoleculeLiftings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiMoleculeRepresentation
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiRepresentationControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CarrierTyping
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CarrierControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HostEvaluation
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HostEvaluationControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ServedRelations
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ServedRelationControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.LanguageEquality
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RelationFreeReadings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadingControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredHereditaryControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ContextLabelControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBagNames
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipSplits
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipSplitControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipSomeDescriptions
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipSplitProofs
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HypersetProofs
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HypersetProofControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HypersetMeaning
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipExcludedMiddle
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipExcludedMiddleControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipIndependence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipKripkeSets
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipExtensionalIndependence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipUpwardSplits
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipUpwardSplitControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalParts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagCanonicalParts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorParts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalPresentations
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriPartsControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.GroundSetParts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.GroundSetPartsControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPartsControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastModalities
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastModalityControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipHFSentence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPlainTypes
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPlainTypeProofs
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastSentences
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastVerdicts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastProofs
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastProofControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedPointTransport
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedTypes
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedVerdicts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedPastProofs
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedPastControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipTwoWay
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipTwoWayControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipTypes
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipDetermined
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedPoints
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedPointDecision
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedPointControls

/-!
# The native type language a language generates

- `Formula`: the formulas, in negation normal form with an involutive dual: structural formers from
  constructors, collection kinds and binders; modalities from steps, labelled by rule and by site;
  counting modalities, which count distinct terms one step away; types, singletons and quantifiers over
  a type; atoms of the language's declared relations; least and greatest fixed points.
- `Semantics`: satisfaction in a native structure over a carrier; the dual is negation.
- `Substitution`: renaming and substituting fixed-point variables, with their meaning; substituting closed
  formulas for free atoms closes a formula with the same truth.
- `Reference`: the native structure of a language, its terms read modulo its equations. A term is in a declared
  relation when a query of the relation at an equivalent term succeeds (`inRelation`, `relationHolds`).
- `Transfer`: existential formulas hold at images of a homomorphism, universal ones come back.
- `Invariance`: formulas are monotone, and closed formulas hold alike at equivalent terms.
- `Generated`: Φ(L), the formulas whose formers the language provides, closed under the dual.
- `Controls`: positive and negative examples of each.
- `Finite`: an exact evaluator on finite structures, with fixed points by iteration.
- `CertificateEquations`: finite checks that a certificate's model respects the language's equations
  (bag, set and algebra laws, and first-order authored equations).
- `CertificateFreshEquations`, `CertificateFreshEquationsControls`: certificates for equations with binders, read with
  fresh values: a metavariable used under fewer binders than it is captured under is closed, and its table is a
  constant. A model passing the check respects every reading of fresh or closed discipline; the η-law, with a model
  that separates two terms the syntax theory equates, and a model that breaks η refused.
- `Certificates`: a valid finite-model certificate maps the language's structure into a finite one, so
  the evaluator's verdicts there are theorems about the language.
- `Exploration`: a listed region of terms sits inside the language, so existential formulas that hold
  there hold in the language, and universal formulas whose dual holds there fail.
- `BoundedMorphism`: along a homomorphism whose image's steps and shapes come from the source, every
  forward formula is preserved and reflected. The inclusion of a generated set of elements is one.
- `ClosedExploration`: a closed region (complete successor lists, all parts, no duplicates) decides every
  forward formula exactly: stuckness, ∀∃ alternations and counting of results included.
- `CanonicalRegions`: closed regions modulo equations. Along a step morphism every behavioural formula is
  preserved and reflected; canonical forms that meet their contract, with coherence, make a closed region
  of canonical terms decide those formulas exactly for the language read modulo its equations. A region
  lists each state's steps at its presentations, terms with it as canonical form, and checks that they are.
- `BagCanonicalForms`: canonical forms for bags, every bag sorted bottom up, on object terms with no set
  whose bags are sorted at a bag carrier. They meet the contract in a language with no authored equation
  and no collection algebra, and rules whose premises are guards (relation queries with no arguments) are
  coherent with them: matching commutes with sorting, and instantiation respects it.
- `AlgebraCanonicalForms`, `PiCanonicalForms`: canonical forms for a collection algebra in one sort, from the
  bag normal form on closed sorted terms; π's parallel fragment read modulo its parallel laws, coherent for plain
  steps.
- `PiPrenexForms`, `PiPrenexControls`: the π-calculus modulo its bag, its restriction laws and its laws of
  replication, from its prenex canonical form, in the typed reading with free names, coherent for plain steps: a step
  of a process is matched by a step of a presentation of its canonical form, an unfolding of its replicated
  components.
- `PiPartnerAdequacy`, `PiPartnerControls`: π's parallel partners at the front door. A step beside a partner is a
  reduction of the two; partner steps are finitely many up to the laws, so the partner-labelled native types
  characterize π's saturated reduction bisimilarity; π's decider evaluates the step modalities, partners' labels
  included, at the listed successors.
- `PiStore`, `PiStoreControls`: π's store. A process is kept as its canonical block, and its steps are read off a
  communication index of its inputs and outputs by channel, where a replicated input or output generates copies. When
  every replicated component copies one component, the index lists no step the front door does not list, and every
  reduction ends at a process equivalent to one it lists; otherwise the store lists the front door's successors. π's
  decider runs on the store.
- `PiNamedAdequacy`, `PiNamedControls`: the front door and the named π-calculus. A reduction of a translation is a
  named reduction and conversely, up to the laws and structural congruence; so the named calculus's saturated
  reduction bisimilarity is `piCalc`'s beside named partners, implied by `piCalc`'s beside every partner, and the
  native types under named partners characterize it. Unfolding a server is invisible to them.
- `PiSyncPrenexForms`, `PiSyncPrenexControls`, `PiSyncPartnerAdequacy`: the synchronous π-calculus modulo its bag,
  its restriction laws and its laws of replication, by the same canonical form, coherent for plain steps through the
  presentations of a state; its partner-labelled native types characterize its saturated reduction bisimilarity. An
  output guards its continuation.
- `PiSumPrenexForms`, `PiSumPrenexControls`: the π-calculus with guarded sums, synchronous outputs, silent prefixes,
  restriction and replication of any process, modulo its bag, its sums, its restriction laws, the empty sum and its
  laws of replication, coherent for plain steps through the presentations of a state. Choices resolved, silent
  alternatives, servers, divergence, extrusion and privacy answered at the front door, with their negatives.
- `PiSumStore`, `PiSumStoreControls`: the π-calculus with sums on its store. A process is kept as its canonical
  block, and its reductions are read off it by the generic store plan of calculi with restriction and replication,
  given the calculus's keys (channels and the silent key) and what parts leave; every successor is a reduction and
  every reduction is matched by one, so the step modalities are decided on the store.
- `CCSCanonicalForms`, `CCSControls`: CCS with guarded sums, the silent action and restriction, modulo its parallel
  bag, its sums and its restriction laws, by the canonical form of its restriction blocks, coherent for plain steps.
  Reactions, choices resolved and discarded, silent steps, private names, nested compositions and stuck terms
  answered at the front door, with their negatives.
- `CCSPartnerAdequacy`, `CCSPartnerControls`: CCS's parallel partners at the front door. A step beside a partner is a
  reduction of the two; partner steps are finitely many up to the laws, so the partner-labelled native types
  characterize CCS's saturated reduction bisimilarity; CCS's decider evaluates the step modalities, partners' labels
  included, at the listed successors. The labels separate `a.(b.0 + c.0)` from `a.b.0 + a.c.0`, which have the same
  traces.
- `CCSRepForms`, `CCSRepControls`: CCS with replication, modulo its parallel bag, its sums, its restriction laws and
  its laws of replication, by the replication theory's canonical form; a step is matched at an unfolding of the
  canonical form within two unfoldings, a replicated sum being one component. Servers that serve once and stay,
  replicated partners and pairs that run forever, names apart and private servers answered at the front door.
- `CCSRecForms`, `CCSRecControls`: CCS with recursion, parametric constants defined by guarded sums, in the
  environment of their definitions. A call is an atom of the static theory; it offers the summands of its body, and an
  action and the co-action offered by two components, sums or calls, react, so a call is unfolded exactly when one of
  its body's summands is taken. The block canonical form decides the static theory, and a step is matched at the
  canonical form. Servers, clients, calls reacting with calls, silent loops, alternating parameters and private names
  passed as arguments answered at the front door, with their negatives.
- `CCSRecPartners`, `CCSRecPartnerAdequacy`, `CCSRecPartnerControls`: the labelled transitions of CCS with recursion
  recovered at the front door. A reduction is a silent transition up to the canonical form; a process performs an
  action exactly when, beside its least partner followed by a fresh sentinel, it reduces to the residual beside the
  sentinel; and bisimilarity of reductions, alone and beside every least partner with a fresh sentinel, is strong
  bisimilarity. The partner-labelled native types characterize saturated reduction bisimilarity, which strong
  bisimilarity implies. Without the sentinel a reduction beside the partner misleads, and saturated reduction
  bisimilarity is strictly coarser than strong bisimilarity: a silent loop answers every reduction beside a partner,
  so `a.0 | D` and `D` agree on the partner-labelled native types.
- `AmbientContextLabels`, `AmbientContextControls`: two-level context labels of mobile ambients with communication.
  The hole beside a partner, at the top, inside an ambient, inside an ambient beside another ambient, or inside an
  ambient inside another: a step in such a context is a reduction of the filled context, matched up to the laws by a
  firing of a presentation of its canonical form, and the firings of a presentation are listed. The native types under
  these contexts characterize two-level saturated reduction bisimilarity, and a modal decider answers them. Each family
  enables a step the inert process lacks; two steps in a sibling context already tell `out b.0` from `0`.
- `ComputedNormalForm`: the bag normal form computed by insertion sort and structural recursion, so the kernel
  evaluates it.
- `AlgebraTypedForms`: canonical forms for a collection algebra in several sorts, in the typed reading at the sorts:
  each law relates closed terms of one sort, and the bag normal form is read off them.
- `AmbientNuForms`, `AmbientNuControls`: mobile ambients with restriction and replication, modulo all their laws, the
  boundary law among them. A process is read located: each ambient a restricted location, its marker and capabilities
  placed at locations, a flat calculus whose static theory is the restriction-block theory with replication. Its
  canonical form read back at a root location, in the ambient calculus's own canonical form, is the ambient canonical
  form: a closed process equivalent to the process, the same for equivalent processes. Steps are listed at the
  unfoldings of the root canonical block, read back; a step from any equivalent of a canonical process is matched
  there. Entering, leaving and opening in sequence, under capabilities, under restriction and with ambients of one
  name, answered at the front door with their negatives.
- `AmbientCommForms`, `AmbientCommControls`: mobile ambients with communication of names and capability terms and with
  paths, modulo all their laws, the laws of paths among them. A process is read through its path normal form, which the
  laws without paths relate for equivalent processes, and then located as above, inputs and outputs placed at
  locations; a communication is a reaction of an input and an output at one place, leaving the input's body with the
  message received. A step of a process is matched by a step of its path normal form, and that at a presentation.
  Communication of names, of private names and of capability terms, paths moving an ambient, and the laws of paths,
  answered at the front door with their negatives.
- `Readings`: a language's rules fired at a chosen presentation of each state, with canonical targets; a
  closed region of a reading decides every behavioural formula exactly. Its steps are listed by the fuel, or, where
  derivations nest without bound, by a certified table of the region, exact over the rule labels.
- `SetReadings`: three readings of a set language. Consume fires at the canonical form, keep where every
  member is written more often than any rule matches, and either is the language's own semantics; they
  are separated on one rule, and keep only adds members.
- `GroundSetReadings`: for rules that take atoms and give atoms back, the three readings characterized
  exactly. Either is consume together with keep for rules that take one atom, has mixtures for rules that
  take several, and is consume once each rule gives back each part of what it takes; keep is consume once
  each rule gives back all of it; keep cannot encode consume.
- `GroundSetForms`: canonical forms for such a language read with either, with presentations that write
  some members twice, coherent with all labels, so the front door decides the language's own semantics.
- `HereditarySets`: sets of sets. Hereditary terms (atoms and sets of hereditary terms) have canonical forms, every
  set sorted without repetition bottom up. Flat set rules (element patterns metavariables or closed canonical terms)
  are coherent at presentations that write each member up to the rule width plus one times: a match at any
  presentation transfers to such a presentation with like captures.
- `SetMembership`: the language `Set ::= {Set*}` with `{x, ...rest} ⇒ x`, whose states are the hereditarily finite
  sets. Hereditary terms are equivalent exactly when they denote the same ZF set, a step is membership, `◇` and `□`
  are bounded quantifiers over members, and native types are indiscernibility up to extensional equality; the front
  door decides membership formulas.
- `SetMembershipExtensional`: the same relations on ZF sets. Denotation is a bounded morphism from the hereditary
  terms, so a forward native type holds at a term exactly when it holds at the set the term denotes.
- `SetMembershipKernel`: those relations defined in the higher-order logic of the sets. A forward native type of a
  hereditary term becomes a sentence of set theory, true exactly when the term has the type, and a proposition of
  every package over the set theory, whose proofs exist in the package's set model exactly then.
- `SetMembershipTrinity`: the operational, intensional and extensional readings of a native type agree and form a
  triangle, which is not exact: holding everywhere and being well founded have the same sets.
- `SetMembershipSentences`, `SetMembershipDerivations`, `SetMembershipRegions`, `SetMembershipProofs`,
  `SetMembershipProofTerms`: modal native types (steps, named terms, emptiness, types, both fixed points) as core
  sentences of set theory; proofs from the laws of the empty set, the power set and separation, in the checker's
  calculus modulo conversion, of each one that holds and the negation of each one that fails, following the
  meaning on the term's finite region by stages; and so closed proof terms in the package of set theory, which
  decide every such native type. The compilers are programs: a decision procedure on the region chooses every
  branch and witness, and the derivations and the package terms are computed.
- `SetMembershipSplits`: splits of hereditarily finite sets, the parts of a set being its subsets. On the parts
  region of a term, closed under membership and under parts, the region decision is exact for the regional
  fragment, the modal fragment with splits and their duals.
- `SetMembershipSplitControls`: split verdicts decided and carried to the membership language: disjoint and
  overlapping parts, a refused split, a dual, a split under a step and a split under a least fixed point.
- `SetMembershipSomeDescriptions`: descriptions said forward and existentially: every member is described by a
  listed term, and each listed term describes some member. Among the sets they agree with descriptions; the
  compiler describes all its subjects this way, and moves them between presentations, separates different sets and
  counts with them, with no membership on the left of a described set.
- `SetMembershipSplitProofs`: splits through the certificate compiler, nested anywhere, in two profiles. The parts
  of a split are separated from the set by a covering; refuting a split is a case analysis whose goal is falsity, so
  it needs no excluded middle, and proving an every-split is the same case analysis with excluded middle, or, with
  upward parts, the union's own case analysis. Every regional native type that fails is refuted from the three laws;
  one whose every-splits have upward parts that holds is proved from them; every one that holds is proved from them
  and excluded middle. The certified set front door returns the closed package term its profile gives.
- `SetMembershipExcludedMiddle`, `SetMembershipExcludedMiddleControls`: how much excluded middle the every-splits
  need. At a set with a member, "every split has a first part that is empty or has a member" is equivalent to
  excluded middle over the three laws, and "... empty or not empty" to weak excluded middle; so hypotheses with the
  three laws prove every regional native type that holds exactly when they prove excluded middle. At the empty set the
  first is proved from the three laws alone, and excluded middle for a bounded formula is the full one here.
- `SetMembershipIndependence`: excluded middle does not follow from the laws of the empty set, the power set,
  separation, union, replacement and induction along membership, even with weak excluded middle and the Gödel–Dummett
  law: a Kripke model of three-valued sets over two stages, coded in base three, satisfies them all and refutes it. So
  "every split of `1` has a first part that is empty or has a member" is true with no proof from them, and no such
  hypotheses are complete for the regional fragment. In every Kripke model, two stages above a stage where the three
  laws hold have a common later stage (Cantor), so weak excluded middle holds wherever the laws hold.
- `SetMembershipKripkeSets`: sets over any listing of stages, with an equality that grows along the stages: two sets
  are equal at a stage when their members agree at every later stage. Membership respects it, and the laws of the
  empty set, the power set, separation, union, replacement and induction along membership hold, with extensionality
  and the indiscernibility of equal sets, in a Kripke–Henkin model of the checker's proofs.
- `SetMembershipExtensionalIndependence`: over two stages excluded middle fails, and over a fork weak excluded middle
  fails, so neither follows from those laws, extensionality included; neither does its every-split at `1`. The fork
  escapes the Cantor argument because the sets of `P(∅)` cut out at the root become equal at the later stages.
- `SetMembershipUpwardSplits`, `SetMembershipUpwardSplitControls`: every-splits whose part formulas have upward
  shapes (true of a part as soon as it has certain members) are proved from the three laws, nested anywhere, since
  the union says which part each member lies in. What costs excluded middle is a part formula that says a part lacks
  members.
- `SetMembershipCertificateControls`: the compiler run on front-door verdicts, with the sizes of the derivations and
  of a closed package term.
- `HypersetGraphs`: finite membership graphs, which may have cycles, as finite structures whose nodes are the same
  when bisimilar. Decoration is a step morphism into the hypersets, so the evaluation decides the behavioural native
  types of the hypersets the nodes picture: Ω descends forever and has no well-founded descent.
- `HypersetProofs`, `HypersetProofControls`: hyperset verdicts as theorems of the package of set theory, which has
  set induction, about coded graphs. A step is an edge between codes, and the compiler proves the sentence of a
  native type at a node, with steps, connectives and both fixed points, when the graph's evaluation accepts it, and
  refutes it otherwise, each with a closed package term: Ω descends forever, by the invariant of its codes.
- `HypersetMeaning`: the sentences mean the coded graph among the sets, and coding is a step morphism, so a
  sentence about a coded graph is true among the sets exactly when the hyperset its node pictures has the native
  type.
- `CanonicalPresentations`: constructor formers, every-built formers and types at the front door for any language
  with canonical forms, through a listing of the presentations of canonical terms that extends a listing of parts;
  over admitted labels, with a certified decider.
- `CanonicalParts`, `FrontDoorParts`: splits at the front door for any language with canonical forms. Canonical
  forms list the parts of each canonical collection, complete and sound for the language's splits; a closed region
  that also holds the listed parts decides the behavioural formulas with splits and emptiness exactly, and is a
  certified decider for the front door. An equation-free language lists the cuts of its collections.
- `BagCanonicalParts`, `PetriPartsControls`: the parts of sorted bags, by dealing their elements into two, and of
  vectors, by their cuts; sub-collections of admitted collections stay admitted. The Petri net's markings split and
  the front door proves and refutes splits of markings.
- `GroundSetParts`, `GroundSetPartsControls`, `SetMembershipPartsControls`: the parts of sets, by coverings, whose
  parts may share members, for ground sets and for hereditary sets; the pair pool's sets split into overlapping parts
  at the front door, and the membership language decides its splits through the generic contract with the same
  verdicts as its own set decider. Bags, vectors and sets decide their splits through one contract, and certified
  deciders never disagree.
- `ExactMorphism`: a bounded morphism that is onto, whose image's predecessors come from predecessors, and that
  commutes with application under a body. Along it every formula transfers, past modalities and quantifiers over a
  type included.
- `SetMembershipHFUniverse`: the hereditarily finite sets as a structure of their own. Denotation is an exact morphism
  from the hereditary terms onto them, so every native type of a hereditary term is the same native type of its set
  among the hereditarily finite sets.
- `SetMembershipPastModalities`, `SetMembershipPastModalityControls`: past modalities and quantifiers over the type
  by finite search. A plain modal formula of modal depth `k` holds alike at elements bisimilar up to `k`, in any
  native structure; a set is bisimilar up to `k` to its truncation, which lies in `V_k`. So whether some, or every,
  hereditarily finite set containing a given one, or at all, has a plain modal formula is a search over the subsets of
  a finite stage, computed with the parts-region decision and exact among the hereditary terms.
- `SetMembershipHFSentence`: hereditary finiteness as a core sentence of set theory: every predicate holding of the
  empty sets and closed under adjoining a new member holds of the set. It means hereditary finiteness in the model of
  the sets and is its own induction principle.
- `SetMembershipPlainTypes`, `SetMembershipPlainTypeProofs`: types of plain bodies (the truth values of their
  subformulas) and representatives grown by adjunction, which close within `2^m + 1` rounds for `m` subformulas and
  cover every hereditary term. In the logic of the sets, with no excluded middle: native formulas move along same
  members, the empty sets have the empty set's type, a set adjoining a member has the type of the adjunction, and every
  hereditarily finite set has a representative's type, by instantiating hereditary finiteness with the predicate
  `some representative's type holds`.
- `SetMembershipPastSentences`, `SetMembershipPastVerdicts`, `SetMembershipPastProofs`,
  `SetMembershipPastProofControls`: past modalities and quantifiers over a type with plain bodies as core sentences
  relativized to hereditary finiteness, true exactly where the hereditarily finite sets have them; verdicts on the
  representatives, exact; and their proof terms in the package. A verdict that holds is proved by witness search (the
  term adjoined to a representative without a conflict, or a representative), one that fails is refuted by induction
  along membership (each representative refuted by the body's literal or by a conflict with the term). Every such
  type at a hereditary term is decided by a computed closed proof term of its proposition or of its negation.
  Controls: six proved and five refuted, each verdict computed by the kernel.
- `SetMembershipFixedPointTransport`: substitution in the logic of the sets for fixed-point bodies: the native formula
  of a substituted formula, read with predicates, transports to another substitution and reading when the substituted
  formulas' predicates are contained in each other; monotonicity is its special case. With it, a least or greatest
  fixed point of the guarded closure's form holds at a set exactly when its unfolding does (Knaster–Tarski in the
  logic, no excluded middle).
- `SetMembershipFixedTypes`, `SetMembershipFixedVerdicts`, `SetMembershipFixedPastProofs`,
  `SetMembershipFixedPastControls`: past modalities and quantifiers over a type with guarded fixed-point bodies (count-
  guarded closures). A body's type is read through the tree of its occurrences with closed formulas for their
  variables; in the logic, empty sets and adjunctions get their types node by node (a fixed point from its unfolding,
  a variable from the fixed point above it), so every hereditarily finite set has a representative's type. Verdicts
  on the practical stage's representatives, with conflicts anywhere in the tree, are exact, and every such type at a
  hereditary term is decided by a closed proof term of the package. Controls: well-founded and endless descents,
  reaching an empty set, five proved and four refuted.
- `SetMembershipTwoWay`, `SetMembershipTwoWayControls`: the two-way native types (steps forward and back, splits,
  emptiness, named sets and quantifiers over the sort, without fixed points, counting or singletons) of the
  hereditarily finite sets are decidable. A step back sees one level less, so a two-way formula holds alike at sets
  bisimilar up to its two-way depth; steps back and sorts become searches over subsets of a finite stage, and an
  evaluation on hereditary terms is exact.
- `SetMembershipTypes`: the types of hereditarily finite sets for a finite list of closed formulas. When each formula is
  decided by the members' types, the realized types stabilize by stage `2 ^ n`, so a step back or a sort over a formula
  of the list is decided by the subsets, or the sets, of that stage.
- `SetMembershipDetermined`: each former preserves being decided by the members' types: a step forward reads them, a
  named set is pinned by its members' names, a split is matched part for part, and a step back reads the set's own type,
  which a local closure decides.
- `SetMembershipFixedPoints`, `SetMembershipFixedPointDecision`, `SetMembershipFixedPointControls`: fixed points under
  steps back, nested freely. A guarded formula reads each fixed-point variable under a step forward taken after its
  binder and never across a step back or a sort. Its closure (each subformula with the enclosing fixed points put back)
  is local, and the evaluation, fixed points iterated by height and steps back by the stage of the closure, decides
  every guarded native type of the hereditarily finite sets. The two-way formulas are guarded. The bound is doubly
  exponential; fixed points whose variable crosses a step back stay open.
- `TwoLevelSetRules`: set rules whose members may be set patterns with a rest, as in `{ {x, y, ...inner}, ...rest }`.
  Matching a set or a bag is invariant under permuting the members of each layer, and the listed presentations write
  each member between once and a bound times, each copy canonical or with copies of its own members. Every step from
  any presentation of a canonical hereditary set is matched, with the same labels and up to canonical form, by a step
  at a listed presentation, so these languages have canonical forms.
- `TwoLevelSetRuleControls`: a rule that picks a member of a member with two members. At `{{0}}` the step needs an
  inner copy: it is proved over the canonical region and unknown without the forms.
- `NestedSetRules`, `NestedSetRuleControls`: set rules nested at any depth, with copies bounded depth by depth: a
  match at any presentation moves to a listed presentation, each set holding each member up to its depth's bound
  times, each copy listed one depth below (`nested_transfer`). The generic bag transfer and regrouping by classes
  are shared with the two-level rules. A rule three sets deep fires at a copy two sets down, with its negatives.
- `FeatureControls`: universally quantified premises over vectors, vector matching, and freshness premises on
  closed terms, at the front door, with their negatives.
- `CanonicalCaptureSetRules`, `CanonicalCaptureFreshness`, `CanonicalCaptureSteps`, `CanonicalCaptureControls`: set
  rules listed at presentations whose captures are all canonical: partners, then the canonical set of the remaining
  members. Premises that hold at canonical captures (relation queries over metavariables in an environment respecting
  canonical forms, guards, universally quantified premises over them, freshness premises over subjects without
  explicit substitutions) are coherent. A premise that steps a captured member is coherent with presentations listed
  to the state's height, the member captured where its step fires. Controls: a query two sets down, a quantified
  premise over a rest, a freshness premise, and a member step that fires only at a copy, with negatives.
- `CanonicalCaptureModulo`, `CanonicalCaptureModuloControls`: hereditary set languages read modulo the set laws at
  every boundary inside a step (the either reading): canonical forms for the front door whatever the premises are
  (step premises from any schema, relation queries in an environment that answers alike requests alike, freshness,
  quantified premises), every label kept unless a quantified premise's body steps. Where a premise's child has the
  class of its term, derivations nest without bound, and a certified table of the region lists them, keeping the rule
  labels. Controls: a step premise of a compound and of a rest, a scoped step, a query with freshness and a step, and
  a quantified premise whose body steps, with negatives.
- `ManySorted`, `ManySortedControls`: many-sorted native types, over carriers by sort, as one-sorted native types with
  sort guards: the sorted structure of any one-sorted structure, and the guarded translation, exact in corresponding
  environments; sorted verdicts at the front door for a language of names and processes, with negatives.
- `ManySortedHigherOrder`, `ManySortedStructural`: the higher-order translation of many-sorted formulas through their
  guarded translation; the sorted structural logic embedded exactly, its classes forming a sorted structure.
- `PresheafReading`: native types read in the presheaf topos over a site of stages by Kripke–Joyal forcing; forcing is
  closed under pulling back and sound for the classical judgment over valuations, equal to it on negative formulas at
  every stage, and equal to classical truth (so to the higher-order translation) at the closed stage on existential
  formers over negative formulas.
- `OpenTerms`: open terms with named free variables; substitution with identity and composition; contexts,
  valuations and substitutions between contexts; the site of a language's inhabited contexts; the open judgment
  `Γ ⊢ t : φ`, closed under substitution and reached one variable at a time; forcing at a context.
- `Judgments`, `EntailmentHigherOrder`: front-door entries with evidence for `Γ ⊢ t : φ` (decided over complete
  fibres, refuted by a typed valuation), for entailment `φ ⊑ ψ` at a type (an open judgment of a variable; proved by a
  finite-model certificate or a derivation in higher-order logic, refuted by a separating value), for inhabitation
  (a witness, or emptiness), and for Σ and Π over a type of families of native types indexed by its values (compiled
  over complete fibres, a witness or a counter-value otherwise); fibres of constant sorts.
- `JudgmentControls`, `PresheafControls`: each judgment at the front door with positive and negative verdicts; the
  readings agreeing on a negative formula and at the closed stage, and parting on a disjunction and on excluded middle
  at an open stage, and on a box over a disjunction at a closed term.
- `DependentJudgments`: dependent and parametric types, generated for every language. Terms inside types and
  substitution into them; dependent contexts whose refinements mention earlier variables, and `Γ ⊢ t : φ` over them,
  carried along substitutions between contexts; dependent products and sums of families over refined sorts with their
  introduction and elimination rules; parametric types, the parameter read positively and negatively, over all
  predicates or those on a sort, eliminated at any formula or any type of the sort (a parameter occurring only
  positively carries nothing: such a type is its instance at falsity). The front door decides dependent judgments
  over complete fibres from its verdicts on refinements and instances, and bounded parametric types over discrete
  fibres from its verdicts at each predicate on the sort, exactly when it decides those.
- `DependentJudgmentControls`: on the coins, a refinement mentioning an earlier variable, a type depending on a value
  (`x : Side ⊢ Show(x) : ◇(is x)`), Π introduced from a judgment and eliminated at a value, Σ, determinism as a
  parametric type over the sides (refuted at `Toss` at `X = {H}` though both extreme instances hold), and covariant
  parametric types, each with negatives.
- `BackwardReach`: backward search as evidence of the front door. Reaching named goals and having an ancestor among them
  are least fixed points; in an equation-free, unconditional, first-order language the reference steps are root
  rewrites, so the Herbrand backward search decides both formulas and their duals, on infinite state spaces too.
- `ExploredDecider`: explored graphs as a certified decider. Two spans with the same steps between forward-closed good
  states satisfy the same future formulas; a root-profile language's compiled plan has the reference steps between
  well-sorted states; a valid query's explored verdict is exact about its generated formula. The runs of a first-order
  language between object states are its reference steps, so μ-calculus statements about them are generated formulas.
- `ExploredControls`: the counters, never halting from four by backward search though they run forever, and never
  deadlocking or recurring to even counts through explored graphs over abstractions of their counts; the finite
  models' questions about a rising level, asked at the front door and read back as μ-calculus statements.
- `SetMembershipCrossing`, `SetMembershipCrossingControls`: fixed points whose variable crosses steps back, decided on
  the hereditarily finite sets when the variable sits at no greater depth than its binder: every unfolding is a
  two-way formula of bounded depth, determined by its values at the subsets of `V_D`, so the unfoldings stabilize
  within the number of those subsets, and a stable unfolding is the fixed point; ascending chains, going up from `{∅}`
  never meeting `∅`, and a property read after a step forward and a step back, kernel-evaluated.
- `SetMembershipCountedTypes`, `SetMembershipCountedFormers`, `SetMembershipCountedFixedPoints`,
  `SetMembershipCountedDecision`, `SetMembershipCountedControls`: counting members and singletons with fixed points
  under steps back. Sets are described by their members' types counted up to a cap; each former is decided by the
  counts at the cap it needs (a split at the sum of its parts' caps, a step back by swapping the set inside its
  container); the multiplicities of the types in `V_k`, read up to one more than the cap, stabilize, and a stable stage
  holds distinct representatives enough for every container and sort search. The count-guarded formulas are decided by
  an exact evaluation; kernel-evaluated controls count distinct members, singletons, and members lying in some set.
- `SetMembershipRepresentatives`, `SetMembershipPracticalStage`: steps back and quantifiers over sets searched among
  representatives. A list of hereditary sets is closed for a local closure when it realizes every closure vector of
  every set over its sublists; then a set's container, and some set of a sort, can be chosen with members among the
  representatives. The representatives are grown from the empty list by adding sets over sublists with new closure
  vectors, checked closed once, and searched in place of every set below the stage rank; the practical evaluation
  agrees with the evaluation on every count-guarded formula.
- `RhoModelLanguage`, `RhoModelEquality`: the normalized ρ profile's model written as a language: ρ's constructors
  without the declared algebra, its rules read where the plan fires, the model's parallel laws and name equation
  authored as equations (flattening one member, flattening the empty bag, removing `0`, `@(*n) = n`). Its equivalence
  of object terms without sets is the profile's equality: each equation step is a move of the model, and each move is
  a chain of equation steps, permutations included, from moving any member to the front in four steps.
- `RhoModelSteps`, `RhoModelAgreement`, `RhoModelReading`, `RhoModelReadingControls`: the normalized ρ profile read at
  the front door. The model's rules fire at ρ's carrier (closed, sorted, sealed by quotations), syntactically, with ρ's
  reflective substitution; there every firing of the plan is a step of the model and every step of the model a firing,
  up to the order of a bag's members (COMM at the root, ParCong at a member's bag site), and every step of the model is
  a step of ρ, so the carrier is closed under steps. Moves keep scoping, law steps and the name equation read forwards
  keep sealing, so normal forms stay in the carrier. On the class of the carrier the profile agrees with the reference
  structure (steps, closure, equality), so it has a faithful reading, `Done` read as `is {}`. Canonical forms: the
  normal form (computed by structural recursion, proved equal), coherent at every fuel since a normal form's bag has no
  bag among its members, so every step there is a COMM at the root. Controls: the runtime's eight verdicts (COMM on
  `@(*@0)`, `@0`, not on `@{}`, `Done`, every step, `⊥`) through the generated front door, kernel-evaluated.
- `SetDriver`, `SetDriverControls`: the set driver, the membership language read on its hereditary terms. A
  context-free formula at a hereditary term is answered by its fragment's decision, count-guarded formulas by the
  practical evaluation and crossing fixed points by elimination, each answer exact in the hereditary reading; on
  forward formulas it agrees with the front door of the reference structure. Controls: past modalities, counting,
  quantifiers over a type and crossing fixed points, with negatives and refusals; questions whose stage holds a tower
  of twos of candidates, answered over at most 2⁶ representative candidates.
- `SetDriverCertified`: the set driver with proof terms. At a hereditary term, a context-free past type with a guarded
  fixed-point or plain body, or a regional type of the core profile is proved or refuted by a closed proof term of the package, one family
  of sentences for both; the certificate is a proof exactly where the hereditary reading holds, so it agrees with every
  answer of the set driver.
- `EngineAgreement`: on aligned, equation-free languages the front door steps where the engine steps over a relation
  environment, so consumers stated through the engine's relation ask the front door: some step to a term, no step.
- `ObservedSystems`: a transition system with declared observations is the one-rule language `x ~> y` when
  `next(x, y)`, its observations declared relations read by `inRelation`; the front door's steps are the system's, and
  for a system on an encoded carrier "some successor has the observation" is the native type `◇(inRelation name)`,
  and `◇`, `□` at an encoded configuration range over the encodings of its successors.
- `SortWitnesses`: the sort quantifiers by witness search: a sort's closed terms, enumerated from the grammar and
  checked by the well-sortedness checker, each asked with the front door; a witness proves `someOf`, a counterexample
  refutes `everyOf`; certified deciders combine (`Decider.orElse`).
- `StaticDecider`: in a language with no equations the static formers (named terms, types, constructors, collections,
  binders, bound variables, with their duals and the connectives) are decided at the term, whatever its region.
- `ContextLabels`: a context label `.context x C ℓ` ranges over the steps with label `ℓ` of the term placed in the
  context `C` at its metavariable `x`, read up to the equations (a placed presentation steps); in a congruent context it
  is a step of the term itself, placed. Complete successors decide the connectives and the step modalities, context
  labels included (`modalDecider`); canonical forms list them, for contexts congruent on the domain, which every context
  is in an equation-free language and with sorted bags. Morphisms between native structures, and the fragments they
  carry, speak of a term's own labels; context labels are the language's.
- `TokenNets`: a language of bags of tokens whose rules consume and produce tokens beside a rest is a reactive system in
  the parallel context category: markings are equivalent exactly when they are permutations, a marking's steps are the
  net's reactions, its steps beside tokens are its reactions in that context, and a least-labelled transition, whose
  label is what the marking lacks of a rule's consumed tokens, is a context step at the front door.
- `TokenNetAdequacy`: a formula over parallel contexts of tokens is a context-labelled native type with the same truth
  at markings; with finitely many reactions, saturated bisimilarity of markings against every environment of tokens is
  agreement on those native types (Hennessy–Milner for parallel contexts, `GSLT/Logic/BagHennessyMilner`); a token no
  rule consumes is inert.
- `TokenNetDistinctions`: the native types of a token net are an observer of the distinction calculus (the crisp
  metric tolerance of the native-type report); two markings are indistinguishable under it exactly when saturated
  bisimilar, apart exactly when some environment tells them apart.
- `PresentedContexts`: a language's presented context theory (`GSLT/LanguageDef/Contexts`), whose one-hole contexts
  are labels, has the front door's context steps as its transitions: in an equation-free language aligned with the
  reference relation, between closed interfaces, a presented transition is the context step whose label is the
  context's shape with its hole a fresh metavariable. Its bisimilarity, as any probe sees it, is characterized by the
  probe's modal formulas when steps are finitely many up to the equations (`GSLT/Contexts/ContextHennessyMilner`).
- `PresentedContextControls`: the contact theory's presented labels read at the front door.
- `ForwardEquivalence`: forward bisimilarity over a class of labels. Forward-bisimilar elements satisfy the same
  forward formulas over those labels; on a region closed under their steps, with finitely many successors up to an
  equivalence the formulas respect, agreement on those formulas is forward bisimilarity. Neither predecessors nor
  the other labels need be finite.
- `RhoPartnerAdequacy`: ρ at the front door, with the parallel partners `{x, Q}` as context labels. Its plain
  steps between closed processes are its steps modulo its equations, a partner's context step is the
  partner-labelled step, partner steps are finitely many up to the equations, and so the front door's native
  types under partners characterize ρ's partner bisimilarity.
- `RhoPartnerControls`: a waiting receiver and the inert process agree on the plain forward formulas and are told
  apart by a partner's formula.
- `RhoLeastPartners`: ρ's COMM as a reactive system on bags of closed canonical primes; saturated bisimilarity against
  every partner is partner bisimilarity, so the front door's partner-labelled native types are decided by least
  labels; the least partners of a closed process are finitely many rule schemas with metavariables (the payload of an
  output partner, the body of an input partner).
- `RhoLeastPartnerControls`: two least partners from one payload schema, a body-schema instance, the empty label on a
  whole redex, no one-prime least label for the inert process, and the waiting receiver told apart from it.
- `PiLeastPartners`: π's least partners, aware of scope. A process is a bag of molecules, each a scope of restricted
  names over guarded processes; partners are bags of molecules with their own scopes, so they cannot name what the
  agent restricts. Communication inside a molecule, and between two molecules renamed apart, which merges their
  scopes (extrusion). Molecules apart communicate only on unrestricted channels; least labels are what the agent lacks
  of a redex, with payload and body schemas for receivers and senders on unrestricted channels; saturated
  bisimilarity is semi-saturated; a private molecule is observed only through its own steps and, with none, is inert.
- `PiMoleculeSoundness`: molecules denote π processes (restricted names over a parallel composition, in any order),
  unique up to structural congruence; renaming a restricted name is α-conversion; every reaction of a bag of molecules
  is a π reduction between denoted processes.
- `PiMoleculeHarmony`: harmony. Every π reduction is realized by a communication inside one molecule, under any
  substitutions and avoiding any finite set of names; so a process reduces to another exactly when some molecule
  denoting it communicates to one denoting the other, up to structural congruence.
- `PiLeastPartnerControls`: `(νc) c<d>` and `(νc) c(y).0` inert while `c<d>` is not; a restricted channel has no
  partner; `(νv) c<v>` sends its name to `c(y). y<d>` and the result `(νv) v<d>` keeps it restricted.
- `PiMoleculeCongruence`: molecules up to congruence. A guarded process replaced by a related one, a replicated input
  unfolded once, an unused restricted name dropped; congruent molecules communicate alike.
- `PiMoleculeLiftings`: liftings of α-equivalent processes have the same scope and related bodies, and structurally
  congruent processes, under any substitutions, have liftings related both ways (`liftsRel_of_congruent`).
- `PiMoleculeRepresentation`: representation independence. Renaming a restricted name keeps communications; a bag
  merges into one molecule whose communications are the bag's reactions; every reduction of what a bag denotes is a
  reaction of that bag; bags denoting structurally congruent processes are saturated bisimilar.
- `PiRepresentationControls`: `c<d>` beside `c(y).0` as two molecules or as one, and `(νv) c<v>` against `(νw) c<w>`,
  are saturated bisimilar; `c<d>` and the inert process are not.
- `CarrierTyping`: the typing former reads the carriers a language declares, through the carrier-aware companion of
  the declaration-derived typing, decided exactly; without builtin carriers the two typings coincide.
- `CarrierControls`: integer and string carriers at the front door (`42 : Int`, `Var(x) : Expr`, a regex literal over
  a string atom), with negatives.
- `HostEvaluation`: constructors the host evaluates (`fold`, `oracle`) meet their host in the relation environment:
  each gets a host rule `f(x₁, …, xₙ) ⇒ y if host:f(x₁, …, xₙ, y)`, which steps exactly as the host answers; without a
  host nothing is evaluated.
- `HostEvaluationControls`: a natively evaluated addition on numerals, with and without its host.
- `ServedRelations`: relations that dynamic services serve are native to the front door: a provider with services
  reads as the relation environment that answers its rows and what its services serve for each request.
- `ServedRelationControls`: a rule querying a served relation fires on what the service serves, and not unregistered.
- `LanguageEquality`: languages have decidable equality, so what is proved for one language serves it wherever it is
  met.
- `RelationFreeReadings`: formulas without relations hold alike whatever the relations; the substructure some elements
  generate; a language without premises has one structure in every relation environment but for its relations.
- `DeclaredReadings`: a language declares how it reads its sets (consume, keep, either) and where its native types
  range (all terms, or the hereditary terms of a sort with what they generate); the front door answers by the
  declaration, exactly in the declared structure, the set driver over the hereditary terms of the membership language;
  either is consume over all presentations.
- `DeclaredReadingControls`: languages declared three ways, with the readings' verdicts where they part: at the top of
  a step, at a member, at a premise's child and at a rest.
- `DeclaredHereditaryControls`: the membership language declared over its hereditary terms, answered at the front door
  by the set driver (past modalities, counting, quantifiers over sets, crossing fixed points), with its refusals, and
  what the answers say in every relation environment.
- `ContextLabelControls`: context labels in `tiny` (a term that needs its context, a context that offers nothing, a
  binder context) and on the Petri net beside tokens, with its least labels, an inert token and a token told apart.
- `PathSystems`: a transition system with listed successors, whose configurations need no encoding, unfolded from a
  root on paths of successor positions encoded as patterns; `◇`, `□` and the observations at a path are those of the
  configuration it reaches.
- `RelationalAnswerFrontDoor`: a relational answer source whose runs of a request are listed exactly unfolds, per
  request, into a finite system of the request, its runs and their answer occurrences; "some run emits an observed
  answer" is `◇◇(inRelation "answer")` and "the request completes and every run is observed" is
  `◇⊤ ∧ □(inRelation "run")` at the request.
- `Hints`: hints by search for the front door: the signature a language's models interpret, the goals a formula is
  about when it says they are reached or never reached, and the finder's cells separating the term from them, given to
  `ask` as a candidate it checks (`askFound`).
- `ScopedCongruences`: a scoped step premise whose local binders fit within its source's capture depth steps as the
  congruence between its endpoints; written so, the language keeps its reference relation witness for witness, its
  equation instances under every reading, and its native types, and strategies that read congruences apply to the core
  form of congruences under binders.
- `CalculusPresentation`: a proof calculus read as rewriting on goal stacks. A rule whose conclusion fixes
  its instance is the rewrite `[conclusion, ...rest] ⇒ [premises, ...rest]`; on proper goal lists the
  presentation's steps are exactly resolution steps by such rules, and where only such rules conclude,
  derivability is the formula "some run reaches the empty stack".
- `Search`: certificates as codes with Kraft lengths; Levin search over them; `ask`, which answers
  proved or refuted with its evidence, or open with a proved lower bound on the complexity of any
  certificate that would decide the question. Given canonical forms, it also weighs closed canonical
  regions.
- `Completeness`: on an equation-free language, a term whose closure under steps and parts is finite and
  completely listed gets an answer from `ask` for every forward formula, proved or refuted, never open.
- `CompletenessModulo`: given canonical forms, a term whose canonical closure is finite and completely
  listed gets an answer from `ask` for every behavioural formula, proved or refuted, never open.
- `Resumption`: the work of a question (three regions and two searches) kept as progress; resuming it
  reads only what it keeps, gives the progress of the longer question, and answers as the front door
  does with all the rounds.
- `Persistence`: more rounds never undo an answer: proved stays proved and refuted stays refuted, since
  each kind of evidence persists. The portfolio is fair: when any one kind of evidence decides the
  question, the front door answers then and at every later round.
- `AcceptanceMatrix`: the front door's answers over a grid of terms and formulas for λ with full β, and
  over the constants of a language with an equation, with the kind of evidence that settled each.
- `Verdicts`: one verdict type, displayed evidence about a proposition, into which `ask`, the shared
  proof-carrying outcome and the strategies' own verdicts map with their soundness.
- `VerdictCatalogue`: the remaining verdict types (checking, admission, backward past boxes, MM2 batches,
  focus and discovery sessions, native queries, the OSLF checker) read the same way; a negative answer
  without a soundness theorem makes no claim. The OSLF checker's verdicts are verdicts about the
  generated formulas its formulas embed as.
- `Equivalence`: the equivalence native types induce. All of Φ(L) separates a language's states exactly
  up to its equations; the behavioural fragment induces forward-backward bisimilarity on finitely
  branching structures (Hennessy–Milner, with past steps and fixed points).
- `StructuralEquivalence`: the first-order fragment induces structural bisimilarity, which also matches
  decompositions, splits, members, bodies and atoms.
- `HigherOrder`: every formula is a predicate of higher-order logic over a native structure's relations,
  built from equality, abstraction and application, with the same truth in the standard model; a
  formula of Φ(L) mentions only L's own relations.
- `RelationalTranslation`: every formula is a predicate of any higher-order signature that defines a native
  structure's relations, with the logic's own connectives, and has the same truth in every model with full
  domains whose definitions denote those relations.
- `SyntacticEmbeddings`, `MuEmbedding`, `FrontDoorEmbeddings`: the other formula languages embed with
  their meanings. These are the structural-modal formulas, the original OSLF formulas, the modal
  μ-calculus over any labelled transition system a structure realizes, the front-door formulas with
  their queries, and the propositional codes. Negation is translated by polarity, atoms become paired
  free variables, and fixed points need their variables at the polarity of their binders.
- `DriverBridge`: the driver-based front door read in the generated logic. Given a faithful rendering of
  a driver's GSLT into the reference structure and its tests as closed formulas, a driver formula's
  meaning is the truth of a closed generated formula; the generated front door's answers settle it, and
  in an equation-free language it decides every driver formula on a finite closure. A reading (`Reading`), by a
  split morphism or by steps, makes a decided answer of the driver-based front door the truth of the query's closed
  formula; a rendering whose image the steps (and splits) do not leave is a step (split) morphism from the structure
  it pulls back. A formula's tests are listed in a table (`LeafTable`), so drivers with infinitely many tests are read.
- `SplitMorphism`: steps and splits forth and back carry the formulas of steps, splits and connectives.
- `FrontDoorAgreement`: the runtime and the generated front door agree on installed drivers, at every budget, also
  with a certified decider (`frontDoorWith`), on queries and on driver formulas (`frontDoorOn`); the generated front
  door with the runtime as its first strategy is one front door (`askThrough`).
- `AnswerBagReading`, `AnswerBagControls`: the answer-bag driver read in the answer language of a payload language:
  on bags of closed payloads with no bag inside, the reference equivalence is permutation, splits are partitions, and
  every driver formula means its closed formula; the completed-answer verdicts agree with the generated front door
  and the bag parts decider.
- `AnswerBagNames`: every bag formula at every bag of answers is the front door's native type at the bag of the
  answers' names (numerals of a payload language, by position among the answers and the formula's values); renaming
  injective on them keeps every bag formula; the front door's decided answers are sound.
- `ObservationAtoms`, `ObservationAtomsControls`: a driver's observations declared with the language as unary
  relations, read as relation atoms; the λ-calculus observing sizes.
- `LocalDriverReading`, `PartrecDriverReading`, `LambdaDriverReading`: readings of the runtime drivers. The local
  driver of a language whose rules fire at the root, are first-order and aligned; the partial-recursive machine's two
  drivers; the λ-calculus driver by steps, in the authored λ language restricted to the selected rules, whose steps
  are the intrinsically scoped λ semantics (`Instances.Lambda.ReferenceAgreement`). Constructor tests are constructor
  formulas for represented declarations: simple parameters and abstractions over one variable.
- `RhoCanonicalForms`, `RhoDriverReading`: ρ in its own reading, its equations as the typed judgment at its element
  types under its scope policy and its rules through its reflection profile. Its admitted elements (closed processes,
  names and input continuations, sealed) keep their kind along the equivalence, canonicalization gives canonical forms
  on them, coherent for plain steps; the ρ driver is read by steps there.
- `NormalizedDriverReading`, `NormalizedAuthoredReading`, `NormalizedAuthoredReadingControls`: the sixth runtime
  driver, `Instances.Normalized`, decides over the plan occurrence semantics (rule-job receipts and equation-job
  completions). It is read at the front door from an agreement on admitted closed terms: its steps are the reference
  structure's, they stay admitted, and its equality is identification; an observation testing for a term is `is t`.
  Profiles on a first-order root plan agree by the plan semantics' agreement with the reference relation; the
  authored conditional-equation profile agrees by its own analysis, with canonical forms, and its seven runtime
  verdicts are obtained from the generated front door. The ρ profile keeps the wrappers `{P}` and `{}` apart, unlike
  ρ's declared algebra, so its reading is in a language whose equality is that model.
- `RhoPresentations`: ρ's presentations listed for its canonical forms: splits by dealing parallel components, the
  quotation `@P` presented also as `@*@P`, types by kind; its presentation decider.
- `PartrecDriverReadingControls`, `LambdaDriverReadingControls`, `RhoDriverReadingControls`: the runtime's verdicts
  about the machine, the λ-calculus and the ρ-calculus, obtained from the generated front door, with the agreement
  proved; ρ's presentations modulo its equations, and its communications open without its forms.
- `FiniteControls`, `CertificateControls`, `SearchControls`, `EquivalenceControls`, `StructuralControls`,
  `HigherOrderControls`, `EmbeddingControls`, `VerdictCatalogueControls`, `CountingControls`,
  `CompletenessControls`, `CanonicalRegionControls`, `CanonicalUnwrapControls`, `SubstitutionControls`,
  `PetriControls`, `ProtocolControls`, `CalculusControls`, `RegexControls`, `InstanceControls`:
  fixed points on small structures; full β under binders, proved safe by a two-value certificate;
  asking with evidence from both sides; bisimilar but distinct, past steps that separate, shapes that
  separate, copies that agree; translations true and false where their formulas are, a primitive
  conjunction outside the basis, and a missing rule outside the signature; embedded formulas that hold
  and fail where their originals do, and `μX. ¬X`, whose reading changes without positivity; the OSLF
  checker proving a generated formula; determinism decided by closed regions, where two steps to the same
  term count once; every forward formula about a finite term decided in ten rounds; a constant with no
  step as written that steps modulo an equation, decided through canonical forms by the front door, and
  canonical forms that mislead without coherence; an equation with a metavariable whose rule fires on
  terms that are not canonical, coherent because canonical forms simulate steps; an atom closed by
  substitution, true and false where the closed formula is; the authored Petri net and guarded workflow,
  decided modulo their bag laws, with steps to different presentations of one marking counted once, and
  sets left out because their matches read repetitions; GödelClaw's reconciliation and display tables,
  total and deterministic, with an absorbing finished state, and not composed without a congruence;
  derivations found and refuted by the front door in HOL Light's kernel, NARS revision and PLN evidence,
  where disjoint sources license revision and overlapping ones do not; regular expressions matched by
  big-step derivative rules, with letters compared by a relation environment; the tree's λ-calculus and
  TinyML as written, where a closed region of one term proves that Ω runs forever.
-/
