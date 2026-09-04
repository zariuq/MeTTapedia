import Mettapedia.Logic.ProofProducingSearch
import Mettapedia.TypeTheory.TH0SimultaneousSubstitutionService

/-!
# A proof-producing syntactic unifier service for TH0 packets

This module turns the portable TH0 simultaneous-substitution kernel into one
small, independently replayable algorithm boundary.  A producer may propose a
substitution for two typed terms.  The checker verifies its contexts, decodes
the terms and substitution intrinsically, applies capture-avoiding
simultaneous substitution, and compares the resulting typed terms.

The service is intentionally *syntactic*.  Full higher-order unification works
modulo beta-eta conversion and may enumerate several incomparable unifiers.
The functional-variable canary below is a beta-unifier that this service
correctly rejects.  This proves that a substitution kernel is useful TH0
infrastructure but is not, by itself, higher-order unification or a
lambda-superposition prover.

Staged candidate generation is connected through `ProofProducingSearch`.
Search origins and rejected guesses remain visible, while semantic acceptance
depends only on this independent checker.  A canonical wire lowering provides
the same boundary for a future native implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.TH0SyntacticUnifierService

open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Logic.HOL
open Mettapedia.Logic.ProofProducingSearch
open Mettapedia.TypeTheory.TH0InterchangeAlgorithmBoundary
open Mettapedia.TypeTheory.TH0SimultaneousSubstitutionService

/-! ## Typed unifiability and its checker -/

/-- A syntactic unification query in explicitly declared source and target
contexts.  Both terms have one expected type in the source context. -/
structure Problem where
  source : Ctx String
  target : Ctx String
  type : TypePacket
  left : TermPacket
  right : TermPacket
deriving Repr, DecidableEq

/-- Intrinsic evidence for one syntactic unifier.  The fields refer to the
typed HOL algebra and its decoder, not to the Boolean checker below. -/
structure Unifier (problem : Problem) where
  substitution : TypedSubstitution problem.target problem.source
  left : Term Constant problem.source problem.type.decode
  right : Term Constant problem.source problem.type.decode
  leftReplay :
    decodeTerm? problem.source problem.left problem.type.decode = some left
  rightReplay :
    decodeTerm? problem.source problem.right problem.type.decode = some right
  equal : subst substitution.toSubst left = subst substitution.toSubst right

/-- Independent intrinsic meaning: a typed unifier exists.  No packet checker
occurs in this definition. -/
def Problem.Meaning (problem : Problem) : Prop :=
  Nonempty (Unifier problem)

@[simp] theorem encodeSubstitution_source
    {source target : Ctx String}
    (substitution : Subst Constant source target) :
    (encodeSubstitution substitution).source = source :=
  rfl

@[simp] theorem encodeSubstitution_target
    {source target : Ctx String}
    (substitution : Subst Constant source target) :
    (encodeSubstitution substitution).target = target :=
  rfl

/-- Executable replay compares the two canonical results of the already
qualified substitution service.  The context guards prevent a certificate
for another problem from being reused.  This definition is deliberately
first-order data processing; the theorem below reconstructs the dependent
intrinsic witness separately. -/
def check (problem : Problem) (certificate : SubstitutionPacket) : Bool :=
  if certificate.source = problem.source then
    if certificate.target = problem.target then
      match substitutePacket? certificate problem.type problem.left,
          substitutePacket? certificate problem.type problem.right with
      | some left, some right => left == right
      | _, _ => false
    else
      false
  else
    false

/-- Every accepted certificate constructs an intrinsic typed unifier. -/
theorem check_sound {problem : Problem} {certificate : SubstitutionPacket}
    (accepted : check problem certificate = true) :
    problem.Meaning := by
  rcases problem with ⟨source, target, type, left, right⟩
  rcases certificate with ⟨certificateSource, certificateTarget, images⟩
  unfold check at accepted
  split at accepted
  · rename_i sourceEqual
    change certificateSource = source at sourceEqual
    subst source
    split at accepted
    · rename_i targetEqual
      change certificateTarget = target at targetEqual
      subst target
      cases leftEquation : substitutePacket?
          ⟨certificateSource, certificateTarget, images⟩ type left with
      | none => simp [leftEquation] at accepted
      | some leftResult =>
          cases rightEquation : substitutePacket?
              ⟨certificateSource, certificateTarget, images⟩ type right with
          | none => simp [leftEquation, rightEquation] at accepted
          | some rightResult =>
              have resultsEqual : leftResult = rightResult := by
                simpa [leftEquation, rightEquation] using accepted
              rcases substitutePacket?_reflects leftEquation with
                ⟨leftSubstitution, decodedLeft, leftSubstitutionReplay,
                  leftReplay, leftResultReplay⟩
              rcases substitutePacket?_reflects rightEquation with
                ⟨rightSubstitution, decodedRight, rightSubstitutionReplay,
                  rightReplay, rightResultReplay⟩
              have substitutionsEqual :
                  leftSubstitution = rightSubstitution := by
                exact Option.some.inj
                  (leftSubstitutionReplay.symm.trans
                    rightSubstitutionReplay)
              subst rightSubstitution
              have intrinsicEqual :
                  subst leftSubstitution.toSubst decodedLeft =
                    subst leftSubstitution.toSubst decodedRight := by
                apply encodeTerm_injective
                calc
                  encodeTerm (subst leftSubstitution.toSubst decodedLeft) =
                      leftResult := leftResultReplay.symm
                  _ = rightResult := resultsEqual
                  _ = encodeTerm
                      (subst leftSubstitution.toSubst decodedRight) :=
                    rightResultReplay
              exact ⟨{
                substitution := leftSubstitution
                left := decodedLeft
                right := decodedRight
                leftReplay := leftReplay
                rightReplay := rightReplay
                equal := intrinsicEqual }⟩
    · simp_all
  · simp_all

/-- The versioned semantic authority for syntactic unifiability. -/
def authority : SemanticAuthority Unit Problem where
  id := ()
  Certificate := SubstitutionPacket
  check := check
  Meaning := Problem.Meaning
  sound := check_sound

/-! ## Canonical problem wire and native certificate lowering -/

def problemWireVersion : Nat := 1

def encodeProblemWire (problem : Problem) : WireTerm :=
  .list [.symbol "TH0SyntacticUnificationProblem",
    .natural problemWireVersion,
    encodeContextWire problem.source,
    encodeContextWire problem.target,
    encodeTypeWire problem.type,
    encodeTermWire problem.left,
    encodeTermWire problem.right]

def decodeProblemWire : WireTerm → Option Problem
  | .list [.symbol "TH0SyntacticUnificationProblem", .natural version,
      source, target, type, left, right] => do
      if version != problemWireVersion then none
      let decodedSource ← decodeContextWire source
      let decodedTarget ← decodeContextWire target
      let decodedType ← decodeTypeWire type
      let decodedLeft ← decodeTermWire left
      let decodedRight ← decodeTermWire right
      pure ⟨decodedSource, decodedTarget, decodedType,
        decodedLeft, decodedRight⟩
  | _ => none

@[simp] theorem decodeProblemWire_encodeProblemWire (problem : Problem) :
    decodeProblemWire (encodeProblemWire problem) = some problem := by
  cases problem
  simp [decodeProblemWire, encodeProblemWire, problemWireVersion]

theorem encodeProblemWire_injective :
    Function.Injective encodeProblemWire := by
  intro first second equal
  have decoded := congrArg decodeProblemWire equal
  simpa using decoded

/-- Total fallback needed only by the abstract lowering record.  A malformed
wire never reaches it through `nativeCheck`, which fails before replay. -/
def fallbackCertificate : SubstitutionPacket :=
  ⟨[], [], []⟩

def lowerCertificateWire (wire : WireTerm) : SubstitutionPacket :=
  (decodeSubstitutionWire wire).getD fallbackCertificate

def nativeCheck (problem : Problem) (wire : WireTerm) : Bool :=
  match decodeSubstitutionWire wire with
  | none => false
  | some certificate => check problem certificate

/-- Canonical wire acceptance is inside the trusted boundary only because it
replays at the packet authority after decoding. -/
def wireLowering : CheckedLowering authority WireTerm where
  nativeCheck := nativeCheck
  lower := lowerCertificateWire
  replay := by
    intro problem wire accepted
    unfold nativeCheck at accepted
    unfold lowerCertificateWire
    change check problem
      ((decodeSubstitutionWire wire).getD fallbackCertificate) = true
    cases decoded : decodeSubstitutionWire wire with
    | none => simp [decoded] at accepted
    | some certificate =>
        simpa [decoded] using accepted

theorem nativeCheck_sound {problem : Problem} {wire : WireTerm}
    (accepted : nativeCheck problem wire = true) :
    problem.Meaning :=
  wireLowering.sound accepted

/-! ## Concrete positive and negative instruments -/

namespace Canary

def individual : Ty String := .base "individual"

def constantA : Constant individual := ⟨"a"⟩
def constantB : Constant individual := ⟨"b"⟩

def sourceVariable : Term Constant [individual] individual :=
  .var .vz

def sourceA : Term Constant [individual] individual :=
  .const constantA

def closedA : Term Constant [] individual :=
  .const constantA

def closedB : Term Constant [] individual :=
  .const constantB

def substituteA : Subst Constant [individual] []
  := Subst.single closedA

def substituteB : Subst Constant [individual] []
  := Subst.single closedB

def certificateA : SubstitutionPacket :=
  encodeSubstitution substituteA

def certificateB : SubstitutionPacket :=
  encodeSubstitution substituteB

/-- The source variable must be instantiated to `a`. -/
def baseProblem : Problem where
  source := [individual]
  target := []
  type := .encode individual
  left := encodeTerm sourceVariable
  right := encodeTerm sourceA

theorem certificateA_accepted :
    check baseProblem certificateA = true := by
  simp [check, baseProblem, certificateA, substitutePacket?_encode,
    sourceVariable, sourceA, substituteA, closedA, subst, Subst.single]

theorem certificateB_rejected :
    check baseProblem certificateB = false := by
  unfold check baseProblem certificateB
  rw [if_pos (by rfl), if_pos (by rfl)]
  rw [substitutePacket?_encode, substitutePacket?_encode]
  simp [sourceVariable, sourceA, substituteB, closedB, subst,
    Subst.single, constantA, constantB, encodeTerm]

theorem baseProblem_meaning : baseProblem.Meaning :=
  check_sound certificateA_accepted

/-- The reflexive query has several distinguishable substitution
certificates, even though its proposition-valued unifiability meaning is one
thin observation. -/
def reflexiveProblem : Problem where
  source := [individual]
  target := []
  type := .encode individual
  left := encodeTerm sourceVariable
  right := encodeTerm sourceVariable

theorem encoded_substitution_accepts_reflexive
    (substitution : Subst Constant [individual] []) :
    check reflexiveProblem (encodeSubstitution substitution) = true := by
  simp [check, reflexiveProblem, substitutePacket?_encode]

theorem reflexive_accepts_two_distinct_certificates :
    check reflexiveProblem certificateA = true ∧
      check reflexiveProblem certificateB = true ∧
        certificateA ≠ certificateB := by
  refine ⟨encoded_substitution_accepts_reflexive substituteA,
    encoded_substitution_accepts_reflexive substituteB, ?_⟩
  intro equal
  have pointwise :=
    encodeSubstitution_reflects_pointwise_equality equal
      (Var.vz : Var [individual] individual)
  simp [substituteA, substituteB, Subst.single, closedA, closedB,
    constantA, constantB] at pointwise

/-! ### Substitution alone is strictly below beta-eta unification -/

def functionType : Ty String := .arr individual individual

def functionalVariable : Term Constant [functionType] functionType :=
  .var .vz

def sourceArgument : Term Constant [functionType] individual :=
  .const constantA

def functionalApplication : Term Constant [functionType] individual :=
  .app functionalVariable sourceArgument

def functionalRight : Term Constant [functionType] individual :=
  .const constantA

def identityBody : Term Constant [individual] individual :=
  .var .vz

def closedIdentity : Term Constant [] functionType :=
  .lam identityBody

def substituteIdentity : Subst Constant [functionType] []
  := Subst.single closedIdentity

def identityCertificate : SubstitutionPacket :=
  encodeSubstitution substituteIdentity

def betaProblem : Problem where
  source := [functionType]
  target := []
  type := .encode individual
  left := encodeTerm functionalApplication
  right := encodeTerm functionalRight

/-- Instantiating the functional variable produces `(fun x => x) a`, which is
not literally the packet `a`; a syntactic checker therefore rejects it. -/
theorem beta_unifier_rejected_by_syntactic_service :
    check betaProblem identityCertificate = false := by
  simp [check, betaProblem, identityCertificate, substitutePacket?_encode,
    substituteIdentity, functionalApplication,
    functionalVariable, sourceArgument, functionalRight, closedIdentity,
    identityBody, subst, Subst.single, individual, functionType, constantA]
  intro encodedEqual
  have intrinsicEqual := encodeTerm_injective encodedEqual
  cases intrinsicEqual

/-- The missing equality is exactly one intrinsic beta step, not a typing or
capture failure. -/
theorem beta_unifier_reduces_to_right :
    betaResult? [] individual individual
      (encodeTerm closedA) (encodeTerm identityBody) =
        some (encodeTerm closedA) := by
  simp [betaResult?, closedA, identityBody]

theorem substitution_is_not_betaEta_unification :
    check betaProblem identityCertificate = false ∧
      betaResult? [] individual individual
        (encodeTerm closedA) (encodeTerm identityBody) =
          some (encodeTerm closedA) :=
  ⟨beta_unifier_rejected_by_syntactic_service,
    beta_unifier_reduces_to_right⟩

/-! ### One replaceable staged producer -/

inductive SearchOrigin where
  | speculative
  | enumerated
deriving Repr, DecidableEq

/-- The producer guesses `b` first and finds `a` one stage later.  Its order is
operational policy, not logical meaning. -/
def producer : StagedProducer authority SearchOrigin where
  batch
    | 0 => [⟨baseProblem, certificateB, .speculative⟩]
    | 1 => [⟨baseProblem, certificateA, .enumerated⟩]
    | _ => []

theorem stage_zero_has_no_accepted_unifier :
    ¬ Nonempty (producer.EvidenceFor baseProblem 0) := by
  rintro ⟨evidence⟩
  have onlyRejected : evidence.accepted.proposal =
      (⟨baseProblem, certificateB, .speculative⟩ :
        Proposal authority SearchOrigin) := by
    simpa [producer, StagedProducer.through] using evidence.accepted.offered
  have replay := evidence.accepted.replay
  rw [onlyRejected] at replay
  simp [authority, certificateB_rejected] at replay

def stageOneEvidence : producer.EvidenceFor baseProblem 1 where
  accepted :=
    { proposal := ⟨baseProblem, certificateA, .enumerated⟩
      offered := by simp [producer, StagedProducer.through]
      replay := certificateA_accepted }
  targets := rfl

theorem baseProblem_eventuallyAccepted :
    producer.EventuallyAccepts baseProblem :=
  ⟨1, ⟨stageOneEvidence⟩⟩

/-- The same accepted certificate survives canonical wire transport. -/
theorem certificateA_wire_accepted :
    nativeCheck baseProblem (encodeSubstitutionWire certificateA) = true := by
  simpa [nativeCheck] using certificateA_accepted

theorem malformed_wire_rejected :
    nativeCheck baseProblem (.symbol "not-a-substitution") = false := by
  rfl

end Canary

/-! ## Audited theorem crowns -/

#print axioms check_sound
#print axioms decodeProblemWire_encodeProblemWire
#print axioms encodeProblemWire_injective
#print axioms nativeCheck_sound
#print axioms Canary.certificateA_accepted
#print axioms Canary.certificateB_rejected
#print axioms Canary.reflexive_accepts_two_distinct_certificates
#print axioms Canary.substitution_is_not_betaEta_unification
#print axioms Canary.stage_zero_has_no_accepted_unifier
#print axioms Canary.baseProblem_eventuallyAccepted
#print axioms Canary.certificateA_wire_accepted
#print axioms Canary.malformed_wire_rejected

end Mettapedia.Logic.HOL.TH0SyntacticUnifierService
