import Mettapedia.Languages.SUMO.Native.SignatureSemantics
import Mettapedia.Languages.SUMO.Native.NIKAuthority

/-!
# Source-signature inference for native SUMO

SUMO `domain` and `domainSubclass` declarations do more than annotate source
text.  A true relation application supplies domain judgments for its actual
arguments.  This module makes that inference explicit and gives it a native NIK
authority.

The authority keeps the submitted ontology assumptions unchanged.  Before
checking a natural-deduction certificate, it deterministically adds exactly the
domain consequences licensed by ground relation atoms and the finite source
signature.  Soundness requires two semantic laws:

* the model realizes the submitted finite source signature;
* every true relation application respects its denoted operator domains.

No object-language domain fact is accepted merely because it was requested by
a certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.SUMO.Native.SignatureInference

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKGSLT
open Mettapedia.Languages.SUMO.Native
open Mettapedia.Languages.SUMO.Native.SourceElaboration
open Mettapedia.Languages.SUMO.Native.SignatureSemantics

universe uModel

/-- A true relation application places every actual argument in its effective
operator domain. -/
def RelationApplicationsRespectDomains
    (model : Model String String) : Prop :=
  forall (operator : model.Carrier) (arguments : List model.Carrier)
      (world : model.World),
    model.applyRelation operator arguments world ->
      model.everyTailArgumentInDomain operator 0 arguments world

/-- The object-language formula corresponding to one source restriction on a
closed argument term. -/
def restrictionFormula
    (argument : Term String String 0 0)
    (restriction : DomainRestriction) : NIKAuthority.Claim :=
  let predicate := match restriction.kind with
    | .object => "instance"
    | .class => "subclass"
  .atom (.constant predicate)
    (.term argument (.term (.constant restriction.className) .nil))

/-- A closed spine contains no row occurrence, so it has an exact term list. -/
def closedTerms : Spine String String 0 0 -> List (Term String String 0 0)
  | .nil => []
  | .term value rest => value :: closedTerms rest
  | .row index _ => Fin.elim0 index

/-- Source-signature consequences for an exact closed argument list, beginning
at one zero-based operator position. -/
def consequencesFrom
    (signature : SourceSignature) (operator : String) :
    Nat -> List (Term String String 0 0) -> List NIKAuthority.Claim
  | _, [] => []
  | position, argument :: rest =>
      (signature.argumentRestrictions operator (position + 1)).map
          (restrictionFormula argument) ++
        consequencesFrom signature operator (position + 1) rest

/-- Direct domain consequences of one closed, constant-headed relation atom.
Only operators in the finite source inventory can contribute facts. -/
def atomDomainConsequences
    (signature : SourceSignature) :
    NIKAuthority.Claim -> List NIKAuthority.Claim
  | .atom (.constant operator) arguments =>
      if operator ∈ signature.declaredOperators then
        consequencesFrom signature operator 0 (closedTerms arguments)
      else []
  | _ => []

/-- Every direct domain consequence contributed by an ontology context. -/
def domainConsequences
    (signature : SourceSignature)
    (assumptions : List NIKAuthority.Claim) : List NIKAuthority.Claim :=
  assumptions.flatMap (atomDomainConsequences signature)

/-- The exact checker context: submitted ontology formulas first, followed by
their deterministic source-signature consequences. -/
def expandedAssumptions
    (signature : SourceSignature)
    (assumptions : List NIKAuthority.Claim) : List NIKAuthority.Claim :=
  assumptions ++ domainConsequences signature assumptions

private theorem denote_closedTermsLifted
    (model : Model String String) :
    (arguments : Spine String String 0 0) ->
    model.denoteSpineLifted model.emptyObjects model.emptyRows arguments =
      (closedTerms arguments).map
        (model.denoteTermLifted model.emptyObjects model.emptyRows)
  | .nil => by simp [Model.denoteSpineLifted, closedTerms]
  | .term value rest => by
      simp [Model.denoteSpineLifted, closedTerms,
        denote_closedTermsLifted model rest]
  | .row index _ => Fin.elim0 index

private theorem denote_closedTerms
    (model : Model String String)
    (arguments : Spine String String 0 0) :
    model.denoteSpine model.emptyObjects model.emptyRows arguments =
      (closedTerms arguments).map
        (model.denoteTerm model.emptyObjects model.emptyRows) := by
  exact denote_closedTermsLifted model arguments

private theorem satisfies_restrictionFormula
    (model : Model String String) (world : model.World)
    (argument : Term String String 0 0)
    (restriction : DomainRestriction) :
    model.satisfies model.emptyObjects model.emptyRows
        (restrictionFormula argument restriction) world <->
      restrictionHolds model
        (model.denoteTerm model.emptyObjects model.emptyRows argument)
        restriction world := by
  cases restriction.kind <;> rfl

private theorem consequencesFrom_sound
    {signature : SourceSignature}
    {model : Model String String}
    {operator : String}
    (realizes : RealizesOperator signature model operator)
    (world : model.World) :
    forall (position : Nat) (arguments : List (Term String String 0 0)),
      model.everyTailArgumentInDomain (model.symbol operator) position
          (arguments.map
            (model.denoteTerm model.emptyObjects model.emptyRows)) world ->
        SatisfiesAssumptions model model.emptyObjects model.emptyRows world
          (consequencesFrom signature operator position arguments) := by
  intro position arguments
  induction arguments generalizing position with
  | nil =>
      intro domains body membership
      simp [consequencesFrom] at membership
  | cons argument rest inductionHypothesis =>
      intro domains body membership
      simp only [consequencesFrom, List.mem_append, List.mem_map] at membership
      rcases membership with ⟨restriction, restrictionMember, rfl⟩ | tailMember
      · apply (satisfies_restrictionFormula model world argument restriction).2
        exact ((realizes.domain position
          (model.denoteTerm model.emptyObjects model.emptyRows argument) world).mp
            domains.1) restriction restrictionMember
      · exact inductionHypothesis (position + 1) domains.2 body tailMember

private theorem atomDomainConsequences_sound
    {signature : SourceSignature}
    {model : Model String String}
    (realizes : RealizesSourceSignature signature model)
    (applicationsRespectDomains : RelationApplicationsRespectDomains model)
    (world : model.World)
    (source : NIKAuthority.Claim)
    (sourceHolds :
      model.satisfies model.emptyObjects model.emptyRows source world) :
    SatisfiesAssumptions model model.emptyObjects model.emptyRows world
      (atomDomainConsequences signature source) := by
  cases source with
  | atom operator arguments =>
      cases operator with
      | constant operator =>
          simp only [atomDomainConsequences]
          split
          next declared =>
            have operatorRealized := realizes.operator operator declared
            apply consequencesFrom_sound operatorRealized world 0
              (closedTerms arguments)
            rw [← denote_closedTerms model arguments]
            exact applicationsRespectDomains (model.symbol operator)
              (model.denoteSpine model.emptyObjects model.emptyRows arguments)
              world sourceHolds
          next notDeclared =>
            intro body membership
            simp at membership
      | var index => exact Fin.elim0 index
      | literal literal =>
          intro body membership
          simp [atomDomainConsequences] at membership
      | application function arguments =>
          intro body membership
          simp [atomDomainConsequences] at membership
      | quote quoted =>
          intro body membership
          simp [atomDomainConsequences] at membership
      | kappa body =>
          intro result membership
          simp [atomDomainConsequences] at membership
  | top =>
      intro body membership
      simp [atomDomainConsequences] at membership
  | bottom =>
      intro body membership
      simp [atomDomainConsequences] at membership
  | asserted _ =>
      intro body membership
      simp [atomDomainConsequences] at membership
  | equal _ _ =>
      intro body membership
      simp [atomDomainConsequences] at membership
  | inOperatorDomain _ _ _ =>
      intro body membership
      simp [atomDomainConsequences] at membership
  | tailInOperatorDomain _ _ _ =>
      intro body membership
      simp [atomDomainConsequences] at membership
  | not _ =>
      intro body membership
      simp [atomDomainConsequences] at membership
  | and _ _ =>
      intro body membership
      simp [atomDomainConsequences] at membership
  | or _ _ =>
      intro body membership
      simp [atomDomainConsequences] at membership
  | implies _ _ =>
      intro body membership
      simp [atomDomainConsequences] at membership
  | iff _ _ =>
      intro body membership
      simp [atomDomainConsequences] at membership
  | allInSpine _ _ =>
      intro body membership
      simp [atomDomainConsequences] at membership
  | allObject _ =>
      intro body membership
      simp [atomDomainConsequences] at membership
  | someObject _ =>
      intro body membership
      simp [atomDomainConsequences] at membership
  | allRow _ =>
      intro body membership
      simp [atomDomainConsequences] at membership
  | someRow _ =>
      intro body membership
      simp [atomDomainConsequences] at membership

theorem domainConsequences_sound
    {signature : SourceSignature}
    {model : Model String String}
    (realizes : RealizesSourceSignature signature model)
    (applicationsRespectDomains : RelationApplicationsRespectDomains model)
    (world : model.World)
    (assumptions : List NIKAuthority.Claim)
    (assumptionsHold :
      SatisfiesAssumptions model model.emptyObjects model.emptyRows world
        assumptions) :
    SatisfiesAssumptions model model.emptyObjects model.emptyRows world
      (domainConsequences signature assumptions) := by
  intro body membership
  simp only [domainConsequences, List.mem_flatMap] at membership
  obtain ⟨source, sourceMember, bodyMember⟩ := membership
  exact atomDomainConsequences_sound realizes applicationsRespectDomains world
    source (assumptionsHold source sourceMember) body bodyMember

theorem expandedAssumptions_sound
    {signature : SourceSignature}
    {model : Model String String}
    (realizes : RealizesSourceSignature signature model)
    (applicationsRespectDomains : RelationApplicationsRespectDomains model)
    (world : model.World)
    (assumptions : List NIKAuthority.Claim)
    (assumptionsHold :
      SatisfiesAssumptions model model.emptyObjects model.emptyRows world
        assumptions) :
    SatisfiesAssumptions model model.emptyObjects model.emptyRows world
      (expandedAssumptions signature assumptions) := by
  intro body membership
  simp only [expandedAssumptions, List.mem_append] at membership
  rcases membership with sourceMember | consequenceMember
  · exact assumptionsHold body sourceMember
  · exact domainConsequences_sound realizes applicationsRespectDomains world
      assumptions assumptionsHold body consequenceMember

/-! ## Native NIK authority -/

/-- A source-signature judgment retains the finite signature, the original
ontology assumptions, and the requested conclusion. -/
structure EntailmentClaim where
  signature : SourceSignature
  assumptions : List NIKAuthority.Claim
  conclusion : NIKAuthority.Claim

abbrev Evidence := NIKAuthority.Evidence

/-- Derivability from the exact source context after its deterministic domain
consequences have been added. -/
def Certified (claim : EntailmentClaim) : Prop :=
  Derivation String String
    (expandedAssumptions claim.signature claim.assumptions) claim.conclusion

/-- Semantic consequence in every domain-respecting model that realizes the
submitted finite source signature. -/
def Meaning (claim : EntailmentClaim) : Prop :=
  forall (model : Model.{0, 0, 0} String String) (world : model.World),
    RealizesSourceSignature claim.signature model ->
    RelationApplicationsRespectDomains model ->
    SatisfiesAssumptions model model.emptyObjects model.emptyRows world
      claim.assumptions ->
    model.satisfies model.emptyObjects model.emptyRows claim.conclusion world

/-- The checker reconstructs a conclusion under the deterministic expanded
context; evidence contains no asserted conclusion or trusted domain fact. -/
def checker : Checker EntailmentClaim Evidence where
  check := fun claim certificate =>
    decide (Certificate.infer
      (expandedAssumptions claim.signature claim.assumptions) certificate =
        some claim.conclusion)

@[simp] theorem checker_accepts_iff
    (claim : EntailmentClaim) (certificate : Evidence) :
    checker.check claim certificate = true <->
      Certificate.infer
        (expandedAssumptions claim.signature claim.assumptions) certificate =
          some claim.conclusion := by
  simp [checker]

theorem checker_authority : checker.Authority Certified where
  sound := by
    intro claim certificate accepted
    exact Certificate.infer_sound
      ((checker_accepts_iff claim certificate).mp accepted)
  complete := by
    intro claim derivable
    obtain ⟨certificate, accepted⟩ := Certificate.infer_complete derivable
    exact ⟨certificate, (checker_accepts_iff claim certificate).mpr accepted⟩

theorem checker_projection : checker.AuthorityProjection Certified Meaning where
  authority := checker_authority
  project := by
    intro claim derivable model world realizes applicationsRespectDomains
      assumptionsHold
    exact derivable.sound model model.emptyObjects model.emptyRows world
      (expandedAssumptions_sound realizes applicationsRespectDomains world
        claim.assumptions assumptionsHold)

def family : AuthorityFamily Unit where
  Claim := fun _ => EntailmentClaim
  Certificate := fun _ => Evidence
  checker := fun _ => checker
  Certified := fun _ => Certified
  Meaning := fun _ => Meaning
  projection := fun _ => checker_projection

/-- The fail-closed public NIK invocation machine for source-signature
consequences. -/
abbrev invocationGSLT : Mettapedia.GSLT.GSLT := Atomic.theory checker

theorem invocation_accepts_iff
    (claim : EntailmentClaim) (certificate : Evidence) :
    invocationGSLT.MultiStep
        (.submitted claim certificate) (.accepted claim) <->
      Certificate.infer
        (expandedAssumptions claim.signature claim.assumptions) certificate =
          some claim.conclusion := by
  rw [Atomic.submitted_multiStep_accepted_iff]
  exact checker_accepts_iff claim certificate

/-- Accepted evidence exposes the complete rule-by-rule native proof route
under the checked source-signature context. -/
theorem invocation_acceptance_reaches_native_empty
    {claim : EntailmentClaim} {certificate : Evidence}
    (accepted : invocationGSLT.MultiStep
      (.submitted claim certificate) (.accepted claim)) :
    (ProofSearch.nativeProofSearchGSLT String String).MultiStep
      [ProofSearch.Sequent.of
        (expandedAssumptions claim.signature claim.assumptions)
        claim.conclusion] [] :=
  ProofSearch.accepted_certificate_reaches_empty
    ((invocation_accepts_iff claim certificate).mp accepted)

abbrev NIKEvidence (claim : EntailmentClaim) :=
  { certificate : Evidence // checker.check claim certificate = true }

theorem nonempty_nikEvidence_iff_derivable (claim : EntailmentClaim) :
    Nonempty (NIKEvidence claim) <-> Certified claim := by
  constructor
  · rintro ⟨⟨certificate, accepted⟩⟩
    exact checker_authority.sound claim certificate accepted
  · intro derivable
    obtain ⟨certificate, accepted⟩ := checker_authority.complete claim derivable
    exact ⟨⟨certificate, accepted⟩⟩

theorem nonempty_nikEvidence_valid_in_model
    (claim : EntailmentClaim)
    (evidence : Nonempty (NIKEvidence claim))
    (model : Model.{0, 0, uModel} String String) (world : model.World)
    (realizes : RealizesSourceSignature claim.signature model)
    (applicationsRespectDomains : RelationApplicationsRespectDomains model)
    (assumptionsHold :
      SatisfiesAssumptions model model.emptyObjects model.emptyRows world
        claim.assumptions) :
    model.satisfies model.emptyObjects model.emptyRows claim.conclusion world := by
  have derivable := (nonempty_nikEvidence_iff_derivable claim).mp evidence
  exact derivable.sound model model.emptyObjects model.emptyRows world
    (expandedAssumptions_sound realizes applicationsRespectDomains world
      claim.assumptions assumptionsHold)

end Mettapedia.Languages.SUMO.Native.SignatureInference
