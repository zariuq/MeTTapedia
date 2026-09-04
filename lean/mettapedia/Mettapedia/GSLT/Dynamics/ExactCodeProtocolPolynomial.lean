import Mettapedia.Computability.ReflectiveCode
import Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
import Mettapedia.TypeTheory.ExactCodeModalityModel

/-!
# Exact command code for indexed-polynomial protocols

A state-indexed reflective-code interface can replace the command shapes of a
protocol polynomial by code shapes.  Decoding alone gives reflection from
coded endpoint steps to the underlying protocol.  Static beta is the
additional law needed to represent every underlying endpoint step.  Static
eta is additionally needed for exact command occurrence and dependent
strategy identity.

The distinction is material.  An eta-only constant token loses an underlying
branch.  A beta-only representation with duplicate codes preserves the
endpoint relation but introduces duplicate proof-relevant occurrences.  A
nonidentity exact-code layer satisfies both laws and transports complete
dependent rounds by equivalence.

These are representation and operational correspondence results.  They do
not make quotation an execution rule, identify rho name equations with
contextual splicing, or choose a protocol scheduler.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ExactCodeProtocolPolynomial

open Mettapedia.Computability.ReflectiveCode
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.ExactCodeModalityModel

universe uState uShape uResponse uCode uResult

variable {State : Type uState}
variable (protocol : ProtocolPolynomial.{uState, uShape, uResponse} State)
variable (Code : State -> Type uCode)

/-- A reflective command representation at every protocol state. -/
abbrev CommandInterface :=
  forall state, Interface (Command protocol state) (Code state)

variable (representation : CommandInterface protocol Code)

/-- Replace command shapes by their codes, deriving response and successor
data by splicing each code back to its represented command. -/
def coded : ProtocolPolynomial.{uState, uCode, uResponse} State where
  Shape := fun _ state => Code state
  Position := fun code =>
    protocol.Position ((representation _).drop code)
  next := fun code response =>
    protocol.next ((representation _).drop code) response

/-- Every coded endpoint step decodes to an underlying endpoint step.  This
direction requires no beta or eta law. -/
theorem step_reflects {source target : State} :
    (lts (coded protocol Code representation)).Step source target ->
      (lts protocol).Step source target := by
  rintro ⟨move⟩
  cases move with
  | fire code response =>
      exact ⟨Move.fire ((representation source).drop code) response⟩

/-- Static beta at every state represents each underlying endpoint step by a
coded endpoint step. -/
theorem step_preserves
    (beta : forall state, (representation state).StaticBeta)
    {source target : State} :
    (lts protocol).Step source target ->
      (lts (coded protocol Code representation)).Step source target := by
  rintro ⟨move⟩
  cases move with
  | fire command response =>
      have recovers := beta source command
      let represent :
          forall (represented : Command protocol source)
            (code : Code source),
            (representation source).drop code = represented ->
            (reply : Response protocol represented) ->
            Nonempty
              (Move (coded protocol Code representation) source
                (protocol.next represented reply)) :=
        fun represented code equal reply => by
          subst represented
          exact ⟨Move.fire
            (protocol := coded protocol Code representation) code reply⟩
      exact represent command ((representation source).quote command)
        recovers response

/-- Beta gives exact agreement of the endpoint transition relations. -/
theorem step_iff
    (beta : forall state, (representation state).StaticBeta)
    {source target : State} :
    (lts (coded protocol Code representation)).Step source target <->
      (lts protocol).Step source target :=
  ⟨step_reflects protocol Code representation,
    step_preserves protocol Code representation beta⟩

/-- Beta and eta identify commands with command codes at one state. -/
def commandEquiv
    (beta : forall state, (representation state).StaticBeta)
    (eta : forall state, (representation state).StaticEta)
    (state : State) :
    Command protocol state ≃ Code state :=
  (representation state).exactEquiv (beta state) (eta state)

/-- Exact command code transports a complete dependent protocol round.  The
response family and every successor-indexed result are transported with the
decoded command, so no cast or runtime tag remains in the interface. -/
def oneRoundEquiv
    (beta : forall state, (representation state).StaticBeta)
    (eta : forall state, (representation state).StaticEta)
    (Result : State -> Type uResult) (state : State) :
    OneRound protocol Result state ≃
      OneRound (coded protocol Code representation) Result state := by
  let commandCode := commandEquiv protocol Code representation beta eta state
  exact Equiv.sigmaCongrLeft' commandCode

/-- Exact command code also transports the complete proof-relevant enabled
event fibre.  This is stronger than endpoint-step agreement: distinct command
codes cannot introduce or erase interaction occurrences. -/
def enabledEventEquiv
    (beta : forall state, (representation state).StaticBeta)
    (eta : forall state, (representation state).StaticEta)
    (state : State) :
    (interaction protocol).Enabled state ≃
      (interaction (coded protocol Code representation)).Enabled state := by
  let commandCode := commandEquiv protocol Code representation beta eta state
  let pairEquiv :
      Sigma (fun command : Command protocol state => Response protocol command) ≃
        Sigma (fun code : Code state =>
          Response (coded protocol Code representation) code) := by
    exact Equiv.sigmaCongrLeft' commandCode
  exact (enabledEquiv protocol state).trans
    (pairEquiv.trans
      (enabledEquiv (coded protocol Code representation) state).symm)

/-- Exact code preserves and reflects the existence of complete dependent
rounds, not merely endpoint reachability. -/
theorem oneRound_nonempty_iff
    (beta : forall state, (representation state).StaticBeta)
    (eta : forall state, (representation state).StaticEta)
    (Result : State -> Type uResult) (state : State) :
    Nonempty (OneRound (coded protocol Code representation) Result state) <->
      Nonempty (OneRound protocol Result state) := by
  constructor
  · rintro ⟨round⟩
    exact ⟨(oneRoundEquiv protocol Code representation beta eta Result state).symm round⟩
  · rintro ⟨round⟩
    exact ⟨oneRoundEquiv protocol Code representation beta eta Result state round⟩

/-! ## Exact nonidentity code control -/

namespace ExactCanary

/-- A looping protocol with a Boolean response. -/
def loop : ProtocolPolynomial.{0, 0, 0} Unit where
  Shape := fun _ _ => PUnit
  Position := fun _ => Bool
  next := fun _ _ => ()

/-- One explicit code layer around each command. -/
abbrev CommandCode (_state : Unit) := ExactCodeIter 1 PUnit

def codeRepresentation : CommandInterface loop CommandCode :=
  fun _ =>
    { quote := quoteIter 1
      drop := spliceIter 1 }

theorem representation_beta (state : Unit) :
    (codeRepresentation state).StaticBeta :=
  splice_quote 1

theorem representation_eta (state : Unit) :
    (codeRepresentation state).StaticEta :=
  quote_splice 1

/-- The representation is visibly nonidentity: the command is wrapped in one
material code constructor. -/
theorem quoted_command_has_one_layer :
    (codeRepresentation ()).quote PUnit.unit =
      ExactCodeLayer.mk PUnit.unit :=
  rfl

/-- Exact nonidentity code preserves the complete endpoint protocol. -/
theorem coded_step_exact (source target : Unit) :
    (lts (coded loop CommandCode codeRepresentation)).Step source target <->
      (lts loop).Step source target :=
  step_iff loop CommandCode codeRepresentation representation_beta
    (source := source) (target := target)

/-- Exact nonidentity code transports a response-indexed dependent round. -/
def dependentRoundEquiv (Result : Unit -> Type uResult) :
    OneRound loop Result () ≃
      OneRound (coded loop CommandCode codeRepresentation) Result () :=
  oneRoundEquiv loop CommandCode codeRepresentation representation_beta
    representation_eta Result ()

end ExactCanary

/-! ## Eta without beta loses behavior -/

namespace BetaFailureCanary

/-- At every Boolean state, a Boolean command selects the next Boolean state. -/
def branching : ProtocolPolynomial.{0, 0, 0} Bool where
  Shape := fun _ _ => Bool
  Position := fun _ => PUnit
  next := fun command _ => command

abbrev CommandCode (_state : Bool) := PUnit

/-- The constant token has eta because the code carrier is singleton, but it
decodes every command as `false` and therefore lacks beta. -/
def codeRepresentation : CommandInterface branching CommandCode :=
  fun _ => Mettapedia.Computability.ReflectiveCode.Canary.etaOnly

theorem representation_eta (state : Bool) :
    (codeRepresentation state).StaticEta :=
  Mettapedia.Computability.ReflectiveCode.Canary.etaOnly_staticEta

theorem representation_not_beta :
    ¬ (forall state, (codeRepresentation state).StaticBeta) := by
  intro beta
  exact Mettapedia.Computability.ReflectiveCode.Canary.etaOnly_not_staticBeta
    (beta false)

/-- The underlying protocol can take the `true` command. -/
theorem underlying_reaches_true :
    (lts branching).Step false true :=
  ⟨Move.fire (protocol := branching) true PUnit.unit⟩

/-- The coded protocol cannot reach `true`: its sole code decodes to the
`false` command. -/
theorem coded_does_not_reach_true :
    ¬ (lts (coded branching CommandCode codeRepresentation)).Step false true := by
  rintro ⟨move⟩
  cases move

/-- Eta alone does not preserve protocol behavior. -/
theorem eta_without_beta_loses_a_branch :
    (forall state, (codeRepresentation state).StaticEta) /\
      (lts branching).Step false true /\
      ¬ (lts (coded branching CommandCode codeRepresentation)).Step false true :=
  ⟨representation_eta, underlying_reaches_true,
    coded_does_not_reach_true⟩

end BetaFailureCanary

/-! ## Beta without eta duplicates occurrences -/

namespace EtaFailureCanary

/-- One command and one response generate a single looping occurrence. -/
def singleton : ProtocolPolynomial.{0, 0, 0} Unit where
  Shape := fun _ _ => PUnit
  Position := fun _ => PUnit
  next := fun _ _ => ()

abbrev CommandCode (_state : Unit) := Bool

/-- Both codes decode to the sole command; quotation chooses `false`. -/
def codeRepresentation : CommandInterface singleton CommandCode :=
  fun _ =>
    { quote := fun _ => false
      drop := fun _ => PUnit.unit }

theorem representation_beta (state : Unit) :
    (codeRepresentation state).StaticBeta := by
  intro command
  cases command
  rfl

theorem representation_not_eta :
    ¬ (forall state, (codeRepresentation state).StaticEta) := by
  intro eta
  have impossible := eta () true
  exact Bool.false_ne_true impossible

def falseCodeEvent :
    (interaction (coded singleton CommandCode codeRepresentation)).Enabled () :=
  enabled (coded singleton CommandCode codeRepresentation) false PUnit.unit

def trueCodeEvent :
    (interaction (coded singleton CommandCode codeRepresentation)).Enabled () :=
  enabled (coded singleton CommandCode codeRepresentation) true PUnit.unit

theorem coded_events_distinct : falseCodeEvent ≠ trueCodeEvent := by
  intro equalEvents
  have equalPairs := congrArg
    (enabledEquiv (coded singleton CommandCode codeRepresentation) ()) equalEvents
  have equalCodes := congrArg Sigma.fst equalPairs
  exact Bool.false_ne_true equalCodes

/-- The underlying singleton protocol has only one enabled occurrence. -/
theorem underlying_events_subsingleton
    (first second : (interaction singleton).Enabled ()) : first = second := by
  apply (enabledEquiv singleton ()).injective
  obtain ⟨firstCommand, firstResponse⟩ := enabledEquiv singleton () first
  obtain ⟨secondCommand, secondResponse⟩ := enabledEquiv singleton () second
  cases firstCommand
  cases firstResponse
  cases secondCommand
  cases secondResponse
  rfl

/-- Endpoint behavior agrees under beta, but no equivalence can preserve the
proof-relevant enabled-event fibre because the coded side has duplicate codes. -/
theorem beta_without_eta_duplicates_occurrences :
    (forall source target,
      (lts (coded singleton CommandCode codeRepresentation)).Step source target <->
        (lts singleton).Step source target) /\
      ¬ Nonempty
        ((interaction singleton).Enabled () ≃
          (interaction (coded singleton CommandCode codeRepresentation)).Enabled ()) := by
  constructor
  · intro source target
    exact step_iff singleton CommandCode codeRepresentation representation_beta
      (source := source) (target := target)
  · rintro ⟨equivalence⟩
    have samePreimages :
        equivalence.symm falseCodeEvent = equivalence.symm trueCodeEvent :=
      underlying_events_subsingleton _ _
    apply coded_events_distinct
    exact (equivalence.apply_symm_apply falseCodeEvent).symm.trans
      ((congrArg equivalence samePreimages).trans
        (equivalence.apply_symm_apply trueCodeEvent))

end EtaFailureCanary

/-! ## Axiom audit -/

#print axioms step_reflects
#print axioms step_preserves
#print axioms step_iff
#print axioms commandEquiv
#print axioms oneRoundEquiv
#print axioms enabledEventEquiv
#print axioms oneRound_nonempty_iff
#print axioms ExactCanary.coded_step_exact
#print axioms ExactCanary.dependentRoundEquiv
#print axioms BetaFailureCanary.eta_without_beta_loses_a_branch
#print axioms EtaFailureCanary.beta_without_eta_duplicates_occurrences

end Mettapedia.GSLT.Dynamics.ExactCodeProtocolPolynomial
