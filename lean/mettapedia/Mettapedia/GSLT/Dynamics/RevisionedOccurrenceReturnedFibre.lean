import Mettapedia.GSLT.Dynamics.RevisionedOccurrenceProofFlow

/-!
# Exact returned-fibre comparison for revisioned occurrence proof flow

This comparison uses one occurrence source and one keying policy throughout.
It transports retained edges, open derivations, and their substitution into
the returned-command fragment of a one-stage indexed operational diagram.

The pending-command counterexample keeps full GSLT-IL strictly outside that
image; the proof-fibre equivalence does not claim an equivalence with all
commands or select an operational host.
-/

namespace Mettapedia.GSLT.Dynamics.RevisionedOccurrenceReturnedFibre

universe uSpace uRequest uAnswer uKey

variable {Space : Type uSpace} {Request : Type uRequest}
  {Answer : Type uAnswer} [DecidableEq Answer]

open _root_.CategoryTheory
open scoped _root_.CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.Dynamics.OccurrenceSemantics
open Mettapedia.GSLT.Dynamics.ProofRelevantNeed
open Mettapedia.GSLT.Dynamics.RevisionedOccurrenceProofFlow

/-- The proposition underlying one proof-relevant admitted Need step. -/
def ClaimStep (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (source target : Claim occurrences keying) : Prop :=
  (revisionedOccurrenceGSLT occurrences keying).Step source.term target.term ∧
    source.expected = target.expected

/-- Forget only proof irrelevance from the retained Need step. -/
theorem stepToClaimStep (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    {source target : Claim occurrences keying}
    (step : Step occurrences keying source target) : ClaimStep occurrences keying source target :=
  ⟨step.operational.down, step.expected_eq⟩

/-- Reconstruct the retained Need step from its two defining propositions. -/
def stepOfClaimStep (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    {source target : Claim occurrences keying}
    (step : ClaimStep occurrences keying source target) : Step occurrences keying source target where
  operational := ⟨step.1⟩
  expected_eq := step.2

/-- The claim-indexed GSLT used as the single returned fibre.  It reuses the
live Need relation and retains the complete expected bag in every state. -/
def claimGSLT (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request) : GSLT where
  Term := Claim occurrences keying
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := ClaimStep occurrences keying
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- One-object index category for the selected revisioned occurrence fibre. -/
abbrev Index := CategoryTheory.Discrete PUnit.{1}

def stage : Index := CategoryTheory.Discrete.mk PUnit.unit

/-- The constant one-stage operational diagram.  The one object is not a
claim that all of GSLT-IL has one stage; it selects the returned-fibre fragment
used by this comparison. -/
def diagram (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request) : Diagram Index where
  obj _ := ⟨claimGSLT occurrences keying⟩
  map _ := OperationalTranslation.id (claimGSLT occurrences keying)
  map_id _ := by
    apply OperationalTranslation.ext
    rfl
  map_comp _ _ := by
    apply OperationalTranslation.ext
    rfl

/-- Quote one full Need claim into the equation class of the selected stage. -/
def quoteClaim (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (claim : Claim occurrences keying) :
    SemanticTerm (claimGSLT occurrences keying) :=
  Quotient.mk (claimGSLT occurrences keying).equations claim

/-- The returned GSLT-IL command representing one revisioned occurrence claim. -/
def encodeClaim (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (claim : Claim occurrences keying) : Command (diagram occurrences keying) :=
  .at stage (quoteClaim occurrences keying claim)

/-- The actual GSLT-IL step relation restricted to encoded returned claims. -/
abbrev ReturnedStep (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (source target : Claim occurrences keying) :=
  Command.Step (diagram occurrences keying) (encodeClaim occurrences keying source)
    (encodeClaim occurrences keying target)

instance step_subsingleton (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (source target : Claim occurrences keying) :
    Subsingleton (Step occurrences keying source target) where
  allEq first second := by
    cases first with
    | mk firstOperational firstExpected =>
      cases second with
      | mk secondOperational secondExpected =>
        have operationalEqual : firstOperational = secondOperational :=
          Subsingleton.elim _ _
        cases operationalEqual
        have expectedEqual : firstExpected = secondExpected :=
          Subsingleton.elim _ _
        cases expectedEqual
        rfl

instance returnedStep_subsingleton (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (source target : Claim occurrences keying) :
    Subsingleton (ReturnedStep occurrences keying source target) where
  allEq first second := by
    cases first with
    | fibre firstStep =>
      cases second with
      | fibre secondStep =>
        congr

/-- Exact proof-fibre equivalence between a retained occurrence edge and the
corresponding returned-fibre GSLT-IL edge. -/
def stepEquiv (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    {source target : Claim occurrences keying} :
    Step occurrences keying source target ≃ ReturnedStep occurrences keying source target where
  toFun step :=
    .fibre (semanticStep_mk (stepToClaimStep occurrences keying step))
  invFun commandStep := by
    cases commandStep with
    | fibre semanticStep =>
      apply stepOfClaimStep occurrences keying
      exact (semanticStep_mk_iff_step (claimGSLT occurrences keying) source target).mp
        semanticStep
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Native derivations in the returned GSLT-IL fragment use the original
revisioned occurrence claims and seeds; only the one-step evidence is represented by an actual
`Command.Step`. -/
abbrev ReturnedClone (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request) :=
  operationalDerivationClone (ReturnedStep occurrences keying) (Seed occurrences keying)

/-- Map every open revisioned occurrence derivation into the returned command fragment. -/
def toReturned (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    {context : List (Claim occurrences keying)}
    {target : Claim occurrences keying} :
    (Clone occurrences keying).Hom context target → (ReturnedClone occurrences keying).Hom context target
  | .assumption index => .assumption index
  | .admittedSeed evidence => .admittedSeed evidence
  | .advance prior step =>
      .advance (toReturned occurrences keying prior) (stepEquiv occurrences keying step)

/-- Recover every open revisioned occurrence derivation from the returned command fragment. -/
def fromReturned (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    {context : List (Claim occurrences keying)}
    {target : Claim occurrences keying} :
    (ReturnedClone occurrences keying).Hom context target → (Clone occurrences keying).Hom context target
  | .assumption index => .assumption index
  | .admittedSeed evidence => .admittedSeed evidence
  | .advance prior step =>
      .advance (fromReturned occurrences keying prior) ((stepEquiv occurrences keying).symm step)

theorem fromReturned_toReturned (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    {context : List (Claim occurrences keying)} {target : Claim occurrences keying}
    (proof : (Clone occurrences keying).Hom context target) :
    fromReturned occurrences keying (toReturned occurrences keying proof) = proof := by
  induction proof with
  | assumption => rfl
  | admittedSeed => rfl
  | advance prior step inductionHypothesis =>
      simp only [toReturned, fromReturned]
      rw [inductionHypothesis, Equiv.symm_apply_apply]

theorem toReturned_fromReturned (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    {context : List (Claim occurrences keying)} {target : Claim occurrences keying}
    (proof : (ReturnedClone occurrences keying).Hom context target) :
    toReturned occurrences keying (fromReturned occurrences keying proof) = proof := by
  induction proof with
  | assumption => rfl
  | admittedSeed => rfl
  | advance prior step inductionHypothesis =>
      simp only [toReturned, fromReturned]
      rw [inductionHypothesis, Equiv.apply_symm_apply]

theorem toReturned_bind (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    {sourceContext targetContext : List (Claim occurrences keying)} {target : Claim occurrences keying}
    (proof : (Clone occurrences keying).Hom sourceContext target)
    (environment : (index : Fin sourceContext.length) →
      (Clone occurrences keying).Hom targetContext (sourceContext.get index)) :
    toReturned occurrences keying (OperationalDerivation.bind proof environment) =
      OperationalDerivation.bind (toReturned occurrences keying proof)
        (fun index => toReturned occurrences keying (environment index)) := by
  induction proof with
  | assumption => rfl
  | admittedSeed => rfl
  | advance prior step inductionHypothesis =>
      simp only [OperationalDerivation.bind, toReturned]
      rw [inductionHypothesis]

theorem fromReturned_bind (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    {sourceContext targetContext : List (Claim occurrences keying)} {target : Claim occurrences keying}
    (proof : (ReturnedClone occurrences keying).Hom sourceContext target)
    (environment : (index : Fin sourceContext.length) →
      (ReturnedClone occurrences keying).Hom targetContext (sourceContext.get index)) :
    fromReturned occurrences keying (OperationalDerivation.bind proof environment) =
      OperationalDerivation.bind (fromReturned occurrences keying proof)
        (fun index => fromReturned occurrences keying (environment index)) := by
  induction proof with
  | assumption => rfl
  | admittedSeed => rfl
  | advance prior step inductionHypothesis =>
      simp only [OperationalDerivation.bind, fromReturned]
      rw [inductionHypothesis]

/-- The exact open-clone equivalence: hypotheses, occurrence indices, and
simultaneous proof substitution are preserved both ways. -/
def cloneEquivalence (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request) :
    CloneEquivalence (Clone occurrences keying) (ReturnedClone occurrences keying) where
  toHom :=
    { map := toReturned occurrences keying
      map_project := fun _ => rfl
      map_substitute := toReturned_bind occurrences keying }
  invHom :=
    { map := fromReturned occurrences keying
      map_project := fun _ => rfl
      map_substitute := fromReturned_bind occurrences keying }
  left_inv := fromReturned_toReturned occurrences keying
  right_inv := toReturned_fromReturned occurrences keying

/-- Semantic preservation transported to the returned GSLT-IL edge family. -/
theorem returnedStep_sound (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    {source target : Claim occurrences keying} (step : ReturnedStep occurrences keying source target)
    (sourceMeaning : Meaning occurrences keying source) : Meaning occurrences keying target :=
  step_sound occurrences keying ((stepEquiv occurrences keying).symm step) sourceMeaning

/-- Returned-fibre GSLT-IL edges are admitted into the same common operation
algebra as the original revisioned occurrence edges. -/
def returnedAdmittedRules (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request) :
    AdmittedCloneRules (ReturnedClone occurrences keying) (Meaning occurrences keying) :=
  operationalAdmittedRules (returnedStep_sound occurrences keying)

/-- Map a retained revisioned occurrence rule to the exactly corresponding returned command
rule without changing either endpoint claim. -/
def toReturnedRule (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (rule : OperationalRule (Step occurrences keying)) :
    OperationalRule (ReturnedStep occurrences keying) where
  source := rule.source
  target := rule.target
  step := stepEquiv occurrences keying rule.step

/-- The returned singleton proof environment. -/
def returnedSingletonEnvironment (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    {source : Claim occurrences keying}
    (proof : (ReturnedClone occurrences keying).Hom [] source) :
    (index : Fin ([source].length)) →
      (ReturnedClone occurrences keying).Hom [] ([source].get index) := by
  intro index
  refine Fin.cases proof ?_ index
  intro impossible
  exact Fin.elim0 impossible

/-- The admission square commutes on execution: applying the revisioned occurrence admitted
operation and then entering GSLT-IL is exactly applying the corresponding
returned-fibre admitted operation.  Both sides are native substitution and
neither invokes a checker. -/
theorem admission_square_commutes (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (rule : OperationalRule (Step occurrences keying))
    (prior : (Clone occurrences keying).Hom [] rule.source) :
    toReturned occurrences keying
        ((admittedRules occurrences keying).toAdmissionHom rule |>.run
          (singletonEnvironment occurrences keying prior)) =
      ((returnedAdmittedRules occurrences keying).toAdmissionHom
          (toReturnedRule occurrences keying rule) |>.run
        (returnedSingletonEnvironment occurrences keying (toReturned occurrences keying prior))) := by
  rfl

/-- The GSLT-IL pending command at the unique stage. -/
def pendingClaim (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (claim : Claim occurrences keying) : Command (diagram occurrences keying) :=
  .via (CategoryTheory.CategoryStruct.id stage) (quoteClaim occurrences keying claim)

/-- Positive strict-extension witness: GSLT-IL can explicitly apply a route
even in the one-object diagram. -/
def applyIdentityVia (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (claim : Claim occurrences keying) :
    Command.Step (diagram occurrences keying) (pendingClaim occurrences keying claim)
      (.at stage (transportTerm (diagram occurrences keying)
        (CategoryTheory.CategoryStruct.id stage)
        (quoteClaim occurrences keying claim))) :=
  Command.Step.applyVia (diagram := diagram occurrences keying)
    (CategoryTheory.CategoryStruct.id stage) (quoteClaim occurrences keying claim)

/-- Negative boundary: a pending route command is outside the returned revisioned occurrence
Need image.  Thus the clone equivalence above cannot identify full GSLT-IL
with revisioned occurrence. -/
theorem pendingClaim_not_encoded (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (claim other : Claim occurrences keying) :
    pendingClaim occurrences keying claim ≠ encodeClaim occurrences keying other := by
  intro equality
  cases equality


/-- Exact comparison laws for the same occurrence source and keying policy. -/
structure Witness (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request) where
  clone : CloneEquivalence (Clone occurrences keying) (ReturnedClone occurrences keying)
  admissionCommutes :
    ∀ (rule : OperationalRule (Step occurrences keying))
      (prior : (Clone occurrences keying).Hom [] rule.source),
    toReturned occurrences keying
        ((admittedRules occurrences keying).toAdmissionHom rule |>.run
          (singletonEnvironment occurrences keying prior)) =
      ((returnedAdmittedRules occurrences keying).toAdmissionHom
          (toReturnedRule occurrences keying rule) |>.run
        (returnedSingletonEnvironment occurrences keying
          (toReturned occurrences keying prior)))
  strictExtension : ∀ (claim : Claim occurrences keying),
    ∃ pending : Command (diagram occurrences keying),
      pending = pendingClaim occurrences keying claim ∧
        ∀ other : Claim occurrences keying,
          pending ≠ encodeClaim occurrences keying other

/-- The returned fragment satisfies the exact comparison while retaining a
concrete pending command outside its image. -/
def witness (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request) :
    Witness occurrences keying where
  clone := cloneEquivalence occurrences keying
  admissionCommutes := admission_square_commutes occurrences keying
  strictExtension := by
    intro claim
    exact ⟨pendingClaim occurrences keying claim, rfl,
      pendingClaim_not_encoded occurrences keying claim⟩

#print axioms stepEquiv
#print axioms fromReturned_toReturned
#print axioms toReturned_fromReturned
#print axioms cloneEquivalence
#print axioms admission_square_commutes
#print axioms pendingClaim_not_encoded
#print axioms witness

end Mettapedia.GSLT.Dynamics.RevisionedOccurrenceReturnedFibre
