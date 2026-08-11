import Mettapedia.Languages.TPTP.NIKAuthority

/-!
# Whole-problem authority for TPTP derivations

Checking every local inference in a TSTP DAG is not yet a proof about the
submitted problem.  Three independently checkable obligations meet at that
boundary:

1. the initial nodes are authenticated against the submitted problem;
2. every chronological inference is accepted by its declared rule authority;
3. the global proof condition is certified (for example assumption discharge,
   freshness, a refutation objective, or a recurrent acceptance condition).

This module composes those obligations without conflating their completeness
claims.  The composite checker is exact for its declared certificate scope and
sound for a named whole-problem objective.  It becomes complete for that
objective only after a separate reverse theorem is supplied.
-/

namespace Mettapedia.Languages.TPTP.ProblemAuthority

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKGSLT
open Mettapedia.Languages.TPTP.StatusSemantics
open Mettapedia.Languages.TPTP.NIKAuthority

universe uProblem uFormula uLeafCertificate uRuleCertificate
  uGlobalCertificate uModel

/-! ## The three authority boundaries -/

/-- The source-facing claim checked by a leaf authority. -/
structure LeafClaim (Problem : Type uProblem) (Formula : Type uFormula) where
  problem : Problem
  initial : List (Entry Formula)

/-- A submitted problem together with a claimed chronological derivation. -/
structure Submission (Problem : Type uProblem) (Formula : Type uFormula) where
  problem : Problem
  derivation : Skeleton Formula

namespace Submission

variable {Problem : Type uProblem} {Formula : Type uFormula}

def leafClaim (submission : Submission Problem Formula) :
    LeafClaim Problem Formula :=
  { problem := submission.problem
    initial := submission.derivation.initial }

end Submission

/-- Exact certificate authority for connecting initial DAG nodes to source
material, together with its projection to an independently stated source
meaning. -/
structure LeafAuthority (Problem : Type uProblem) (Formula : Type uFormula) where
  Certificate : Type uLeafCertificate
  checker : Checker (LeafClaim Problem Formula) Certificate
  Certified : LeafClaim Problem Formula -> Prop
  Meaning : LeafClaim Problem Formula -> Prop
  projection : checker.AuthorityProjection Certified Meaning

/-- Exact certificate authority for a whole-DAG side condition.  This is the
home for obligations that cannot be validated node by node. -/
structure GlobalAuthority (Problem : Type uProblem) (Formula : Type uFormula) where
  Certificate : Type uGlobalCertificate
  checker : Checker (Submission Problem Formula) Certificate
  Certified : Submission Problem Formula -> Prop
  Meaning : Submission Problem Formula -> Prop
  projection : checker.AuthorityProjection Certified Meaning

variable {Problem : Type uProblem} {Formula : Type uFormula}
    {semantics : StatusMeaning Formula}
    (rules : RuleAuthorityFamily Formula semantics)
    (leaves : LeafAuthority Problem Formula)
    (global : GlobalAuthority Problem Formula)

/-- The evidence components remain physically distinct at the wire boundary. -/
abbrev Evidence :=
  leaves.Certificate ×
    (List rules.PackedCertificate × global.Certificate)

/-- The exact scope for which the composed evidence format is complete. -/
def Certified (submission : Submission Problem Formula) : Prop :=
  leaves.Certified submission.leafClaim /\
    NIKAuthority.Certified rules submission.derivation /\
      global.Certified submission

/-- The independently projected meanings of all three authorities. -/
def ComponentMeaning (submission : Submission Problem Formula) : Prop :=
  leaves.Meaning submission.leafClaim /\
    NIKAuthority.Meaning rules submission.derivation /\
      global.Meaning submission

/-- A fail-closed checker for all three evidence components. -/
def checker [DecidableEq Formula] :
    Checker (Submission Problem Formula) (Evidence rules leaves global) where
  check submission evidence :=
    (leaves.checker.check submission.leafClaim evidence.1 &&
      (NIKAuthority.proofChecker rules).check
        submission.derivation evidence.2.1) &&
      global.checker.check submission evidence.2.2

theorem checker_sound [DecidableEq Formula] :
    (checker rules leaves global).Sound (Certified rules leaves global) := by
  intro submission evidence accepted
  have parts :
      (leaves.checker.check submission.leafClaim evidence.1 = true /\
        (NIKAuthority.proofChecker rules).check
          submission.derivation evidence.2.1 = true) /\
        global.checker.check submission evidence.2.2 = true := by
    simpa only [checker, Bool.and_eq_true] using accepted
  exact
    ⟨leaves.projection.authority.sound _ _ parts.1.1,
      (NIKAuthority.proofChecker_authority rules).sound _ _ parts.1.2,
      global.projection.authority.sound _ _ parts.2⟩

theorem checker_complete [DecidableEq Formula] :
    (checker rules leaves global).CertificateComplete
      (Certified rules leaves global) := by
  intro submission certified
  obtain ⟨leafCertified, localCertified, globalCertified⟩ := certified
  obtain ⟨leafEvidence, leafAccepted⟩ :=
    leaves.projection.authority.complete _ leafCertified
  obtain ⟨localEvidence, localAccepted⟩ :=
    (NIKAuthority.proofChecker_authority rules).complete _ localCertified
  obtain ⟨globalEvidence, globalAccepted⟩ :=
    global.projection.authority.complete _ globalCertified
  exact
    ⟨⟨leafEvidence, localEvidence, globalEvidence⟩, by
      simp [checker, leafAccepted, localAccepted, globalAccepted]⟩

/-- Exact certificate authority for the explicitly named conjunction. -/
theorem checker_authority [DecidableEq Formula] :
    (checker rules leaves global).Authority (Certified rules leaves global) where
  sound := checker_sound rules leaves global
  complete := checker_complete rules leaves global

theorem certified_implies_componentMeaning
    (submission : Submission Problem Formula) :
    Certified rules leaves global submission ->
      ComponentMeaning rules leaves global submission := by
  rintro ⟨leafCertified, localCertified, globalCertified⟩
  exact
    ⟨leaves.projection.project _ leafCertified,
      NIKAuthority.certified_implies_meaning rules _ localCertified,
      global.projection.project _ globalCertified⟩

/-! ## Whole-problem objectives and the exact completeness gate -/

/-- A semantic discharge theorem states how the three independent component
meanings establish one whole-problem objective. -/
structure ObjectiveBridge where
  Objective : Submission Problem Formula -> Prop
  discharge : forall submission,
    leaves.Meaning submission.leafClaim ->
    NIKAuthority.Meaning rules submission.derivation ->
    global.Meaning submission ->
    Objective submission

namespace ObjectiveBridge

variable (bridge : ObjectiveBridge rules leaves global)

theorem certified_implies_objective
    (submission : Submission Problem Formula) :
    Certified rules leaves global submission -> bridge.Objective submission := by
  intro certified
  obtain ⟨leafMeaning, localMeaning, globalMeaning⟩ :=
    certified_implies_componentMeaning rules leaves global submission certified
  exact bridge.discharge submission leafMeaning localMeaning globalMeaning

/-- The ordinary whole-problem result: exact replay for the declared evidence
scope, followed by a sound semantic discharge. -/
def authorityProjection [DecidableEq Formula] :
    (checker rules leaves global).AuthorityProjection
      (Certified rules leaves global) bridge.Objective where
  authority := checker_authority rules leaves global
  project := bridge.certified_implies_objective

/-- Semantic certificate completeness is an additional theorem, not a
consequence of local replay. -/
def ObjectiveComplete : Prop :=
  forall submission, bridge.Objective submission ->
    Certified rules leaves global submission

/-- Only a reverse theorem from the whole objective into the exact
certificate scope promotes the composite to semantic authority. -/
theorem semanticAuthority [DecidableEq Formula]
    (complete : bridge.ObjectiveComplete) :
    (checker rules leaves global).Authority bridge.Objective where
  sound := bridge.authorityProjection.sound
  complete := by
    intro submission meaningful
    exact (checker_authority rules leaves global).complete _
      (complete submission meaningful)

/-- The composed fail-closed NIK is itself an ordinary checker GSLT. -/
def theory [DecidableEq Formula] : Mettapedia.GSLT.GSLT :=
  Atomic.theory (checker rules leaves global)

theorem acceptance_implies_objective [DecidableEq Formula]
    {submission : Submission Problem Formula}
    {evidence : Evidence rules leaves global}
    (path : (theory rules leaves global).MultiStep
      (.submitted submission evidence) (.accepted submission)) :
    bridge.Objective submission := by
  exact Refinement.acceptance_sound
    (Refinement.atomic (checker rules leaves global))
    bridge.authorityProjection.sound path

end ObjectiveBridge

/-! ## A model-theoretic theorem-DAG profile -/

namespace TheoremDAG

variable (modelSemantics : ClassicalModelSemantics.{uFormula, uModel} Formula)

/-- Source authentication for the basic theorem-DAG profile: the initial
node formulas are exactly the submitted premise list. -/
def InitialMatches (claim : LeafClaim (List Formula) Formula) : Prop :=
  claim.initial.map Entry.formula = claim.problem

def leafAuthority [DecidableEq Formula] :
    LeafAuthority (List Formula) Formula where
  Certificate := Unit
  checker :=
    { check := fun claim _ =>
        decide (claim.initial.map Entry.formula = claim.problem) }
  Certified := InitialMatches
  Meaning := InitialMatches
  projection :=
    { authority :=
        { sound := by
            intro claim certificate accepted
            change claim.initial.map Entry.formula = claim.problem
            exact of_decide_eq_true accepted
          complete := by
            intro claim matched
            change claim.initial.map Entry.formula = claim.problem at matched
            exact ⟨(), decide_eq_true matched⟩ }
      project := by intro claim matched; exact matched }

/-- Every internal edge claims ordinary theorem preservation. -/
def AllTheoremNodes (submission : Submission (List Formula) Formula) : Prop :=
  submission.derivation.nodes.all
    (fun node => node.key.status == .thm) = true

def globalAuthority : GlobalAuthority (List Formula) Formula where
  Certificate := Unit
  checker :=
    { check := fun submission _ =>
        submission.derivation.nodes.all
          (fun node => node.key.status == .thm) }
  Certified := AllTheoremNodes
  Meaning := AllTheoremNodes
  projection :=
    { authority :=
        { sound := by
            intro submission certificate accepted
            exact accepted
          complete := by
            intro submission allTheorem
            exact ⟨(), allTheorem⟩ }
      project := by intro submission allTheorem; exact allTheorem }

def EntriesSatisfy (model : modelSemantics.Model)
    (entries : List (Entry Formula)) : Prop :=
  forall entry, entry ∈ entries ->
    modelSemantics.satisfies model entry.formula

theorem findEntry?_eq_some_mem
    {entries : List (Entry Formula)} {id : Nat} {entry : Entry Formula}
    (found : findEntry? entries id = some entry) : entry ∈ entries := by
  induction entries with
  | nil => simp [findEntry?] at found
  | cons head tail ih =>
      simp only [findEntry?] at found
      split at found
      next equal =>
        have : head = entry := Option.some.inj found
        subst entry
        simp
      next different =>
        exact List.mem_cons_of_mem head (ih found)

theorem resolveParents?_satisfied
    {entries : List (Entry Formula)} {ids : List Nat}
    {parents : List Formula} {model : modelSemantics.Model}
    (resolved : resolveParents? entries ids = some parents)
    (satisfied : EntriesSatisfy modelSemantics model entries) :
    modelSemantics.SatisfiesAll model parents := by
  induction ids generalizing parents with
  | nil =>
      simp [resolveParents?] at resolved
      subst parents
      simp [ClassicalModelSemantics.SatisfiesAll]
  | cons id ids ih =>
      simp only [resolveParents?] at resolved
      cases found : findEntry? entries id with
      | none => simp [found] at resolved
      | some entry =>
          cases rest : resolveParents? entries ids with
          | none => simp [found, rest] at resolved
          | some tail =>
              simp [found, rest] at resolved
              subst parents
              intro formula member
              simp only [List.mem_cons] at member
              rcases member with equal | inTail
              · subst formula
                exact satisfied entry (findEntry?_eq_some_mem found)
              · exact (ih (parents := tail) rest) formula inTail

def TheoremProperty (key : RuleKey) (claim : RelationClaim Formula) : Prop :=
  key.status = .thm /\ modelSemantics.TheoremRelation claim

theorem replay_to_theoremProperty
    {entries final : List (Entry Formula)} {nodes : List (Node Formula)}
    (replay : Replay
      (fun key => modelSemantics.commonStatusMeaning.Meaning key.status)
      entries nodes final)
    (allTheorem : nodes.all
      (fun node => node.key.status == .thm) = true) :
    Replay (TheoremProperty modelSemantics) entries nodes final := by
  induction replay with
  | nil entries => exact .nil entries
  | @cons entries parents nodes final node fresh resolved meaning rest ih =>
      have status : node.key.status = .thm :=
        by
          have statusBool := List.all_eq_true.mp allTheorem node (by simp)
          simpa using statusBool
      have theoremRelation : modelSemantics.TheoremRelation
          (nodeClaim node parents) := by
        simpa [ClassicalModelSemantics.commonStatusMeaning, status] using meaning
      exact .cons node fresh resolved ⟨status, theoremRelation⟩
        (ih (by
          exact List.all_eq_true.mpr (by
            intro later member
            exact List.all_eq_true.mp allTheorem later (by simp [member]))))

theorem theoremReplay_preserves_satisfaction
    {entries final : List (Entry Formula)} {nodes : List (Node Formula)}
    {model : modelSemantics.Model}
    (replay : Replay (TheoremProperty modelSemantics) entries nodes final)
    (satisfied : EntriesSatisfy modelSemantics model entries) :
    EntriesSatisfy modelSemantics model final := by
  induction replay with
  | nil entries => exact satisfied
  | @cons entries parents nodes final node fresh resolved theoremStep rest ih =>
      apply ih
      intro entry member
      simp only [List.mem_cons] at member
      rcases member with equal | old
      · subst entry
        exact theoremStep.2 model
          (resolveParents?_satisfied modelSemantics resolved satisfied)
      · exact satisfied entry old

theorem initialMatches_satisfy
    {problem : List Formula} {initial : List (Entry Formula)}
    {model : modelSemantics.Model}
    (sourceMatches : initial.map Entry.formula = problem)
    (satisfied : modelSemantics.SatisfiesAll model problem) :
    EntriesSatisfy modelSemantics model initial := by
  intro entry member
  apply satisfied entry.formula
  rw [← sourceMatches]
  exact List.mem_map.mpr ⟨entry, member, rfl⟩

/-- The independently stated whole-problem objective for a theorem DAG. -/
def Objective (submission : Submission (List Formula) Formula) : Prop :=
  modelSemantics.TheoremRelation
    { parents := submission.problem
      inferred := submission.derivation.expected }

theorem discharge
    (rules : RuleAuthorityFamily Formula modelSemantics.commonStatusMeaning)
    (submission : Submission (List Formula) Formula)
    (source : InitialMatches submission.leafClaim)
    (localMeaning : NIKAuthority.Meaning rules submission.derivation)
    (global : AllTheoremNodes submission) :
    Objective modelSemantics submission := by
  intro model problemSatisfied
  obtain ⟨initialUnique, final, replay, root⟩ := localMeaning
  have initialSatisfied : EntriesSatisfy modelSemantics model
      submission.derivation.initial :=
    initialMatches_satisfy modelSemantics source problemSatisfied
  have theoremReplay : Replay (TheoremProperty modelSemantics)
      submission.derivation.initial submission.derivation.nodes final :=
    replay_to_theoremProperty modelSemantics replay global
  have finalSatisfied := theoremReplay_preserves_satisfaction
    modelSemantics theoremReplay initialSatisfied
  obtain ⟨rootEntry, found, rootFormula⟩ := root
  rw [← rootFormula]
  exact finalSatisfied rootEntry
    (findEntry?_eq_some_mem found)

def objectiveBridge [DecidableEq Formula]
    (rules : RuleAuthorityFamily Formula modelSemantics.commonStatusMeaning) :
    ObjectiveBridge rules (leafAuthority (Formula := Formula))
      (globalAuthority (Formula := Formula)) where
  Objective := Objective modelSemantics
  discharge := discharge modelSemantics rules

end TheoremDAG

/-! ## Positive and negative whole-problem canaries -/

namespace Canary

open StatusSemantics.Canary
open NIKAuthority.Canary

def validSubmission : Submission (List Bool) Bool where
  problem := [true]
  derivation := validSkeleton

def validCompositeEvidence :
    Evidence finiteRuleFamily (TheoremDAG.leafAuthority (Formula := Bool))
      (TheoremDAG.globalAuthority (Formula := Bool)) :=
  ⟨(), validEvidence, ()⟩

theorem valid_submission_accepted :
    (checker finiteRuleFamily (TheoremDAG.leafAuthority (Formula := Bool))
      (TheoremDAG.globalAuthority (Formula := Bool))).check
      validSubmission validCompositeEvidence = true := by
  decide

theorem valid_acceptance_establishes_theorem_objective :
    TheoremDAG.Objective boolSemantics validSubmission := by
  let bridge := TheoremDAG.objectiveBridge boolSemantics finiteRuleFamily
  apply bridge.acceptance_implies_objective
  exact (Atomic.submitted_multiStep_accepted_iff
    (checker finiteRuleFamily (TheoremDAG.leafAuthority (Formula := Bool))
      (TheoremDAG.globalAuthority (Formula := Bool)))
    validSubmission validCompositeEvidence).mpr valid_submission_accepted

def wrongLeafSubmission : Submission (List Bool) Bool :=
  { validSubmission with problem := [false] }

theorem wrong_leaf_rejected :
    (checker finiteRuleFamily (TheoremDAG.leafAuthority (Formula := Bool))
      (TheoremDAG.globalAuthority (Formula := Bool))).check
      wrongLeafSubmission validCompositeEvidence = false := by
  decide

def wrongGlobalSubmission : Submission (List Bool) Bool :=
  { validSubmission with
    derivation :=
      { validSkeleton with
        nodes := [⟨1, ⟨"resolution", .cth⟩, [0], false⟩]
        expected := false } }

def wrongGlobalEvidence :
    Evidence finiteRuleFamily (TheoremDAG.leafAuthority (Formula := Bool))
      (TheoremDAG.globalAuthority (Formula := Bool)) :=
  ⟨(), [⟨⟨"resolution", .cth⟩, ()⟩], ()⟩

theorem non_theorem_global_profile_rejected :
    (checker finiteRuleFamily (TheoremDAG.leafAuthority (Formula := Bool))
      (TheoremDAG.globalAuthority (Formula := Bool))).check
      wrongGlobalSubmission wrongGlobalEvidence = false := by
  decide

def semanticallyTrueButMalformed : Submission (List Bool) Bool where
  problem := [true]
  derivation := missingParentSkeleton

theorem malformed_objective_is_semantically_true :
    TheoremDAG.Objective boolSemantics semanticallyTrueButMalformed := by
  simp [TheoremDAG.Objective,
    ClassicalModelSemantics.TheoremRelation,
    ClassicalModelSemantics.SatisfiesAll, semanticallyTrueButMalformed,
    missingParentSkeleton, validSkeleton, boolSemantics]

/-- Local certificate completeness does not imply semantic completeness for
the whole theorem objective: a true statement may be paired with a malformed
purported derivation. -/
theorem theorem_objective_not_complete_for_fixed_submission :
    Not (Certified finiteRuleFamily
      (TheoremDAG.leafAuthority (Formula := Bool))
      (TheoremDAG.globalAuthority (Formula := Bool))
      semanticallyTrueButMalformed) := by
  rintro ⟨leafCertified, localCertified, globalCertified⟩
  obtain ⟨initialUnique, final, replay, root⟩ := localCertified
  cases replay with
  | cons node fresh resolved certified rest =>
      simp [semanticallyTrueButMalformed, missingParentSkeleton,
        validSkeleton, resolveParents?, findEntry?] at resolved

end Canary

end Mettapedia.Languages.TPTP.ProblemAuthority
