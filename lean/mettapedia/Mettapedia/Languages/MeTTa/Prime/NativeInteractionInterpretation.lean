import Mettapedia.Languages.MeTTa.Prime.NativeInteractionCost

/-!
# Partial interpretations of MeTTa Native terms as interaction endpoints

An interaction theory need not interpret every MeTTa Native term.  The
primitive interface is therefore a deterministic partial lowering into the
term carrier of an arbitrary GSLT.  Its admitted endpoints index exact,
occurrence-preserving event paths.

This factors the current rho integration into two independent choices:

* which native terms have an operational interpretation; and
* which interaction presentation supplies their events.

The rho instance admits first-class runtime patterns.  Other instances may
interpret staged, typed, spatial, or external-service terms without changing the
generic computation type.  Failure to lower a term means that the associated
interaction fibre is empty; it never manufactures a fallback interpretation.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.Languages.MeTTa.NativeTypeTheory
open Mettapedia.Languages.MeTTa.Prime.NativeInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A deterministic partial interpretation of closed MeTTa Native terms as
terms of an interaction theory. -/
structure EndpointInterpretation (theory : GSLT) where
  lower? : NativeRawTm 0 0 → Option theory.Term

namespace EndpointInterpretation

variable {theory : GSLT}

/-- A successful endpoint admission retains both the lowered theory term and
the exact successful result of the partial interpretation. -/
def Endpoint (interpretation : EndpointInterpretation theory)
    (term : NativeRawTm 0 0) : Type :=
  { endpoint : theory.Term // interpretation.lower? term = some endpoint }

/-- Determinism of `Option` lowering makes endpoint admission proof-relevant
but endpoint identity unique. -/
instance endpointSubsingleton
    (interpretation : EndpointInterpretation theory)
    (term : NativeRawTm 0 0) : Subsingleton (interpretation.Endpoint term) :=
  ⟨by
    rintro ⟨left, leftEq⟩ ⟨right, rightEq⟩
    have endpointEq : left = right :=
      Option.some.inj (leftEq.symm.trans rightEq)
    subst right
    rfl⟩

/-- The generic interaction computation between two native terms admitted by
one interpretation.  Both endpoint admissions and the exact event path are
retained in the inhabitant. -/
def computationTy (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory)
    (source target : NativeRawTm 0 0) :
    familiesCwF.Ty PrimeContext :=
  fun _ =>
    Σ sourceEndpoint : interpretation.Endpoint source,
      Σ targetEndpoint : interpretation.Endpoint target,
        EventPath presentation sourceEndpoint.1 targetEndpoint.1

/-- An admitted native endpoint has the empty interaction computation. -/
def returnPath (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory)
    {term : NativeRawTm 0 0} (endpoint : interpretation.Endpoint term) :
    familiesCwF.Tm PrimeContext
      (interpretation.computationTy presentation term term) :=
  fun _ => ⟨endpoint, endpoint, .nil endpoint.1⟩

/-- Exact native interaction computations compose.  The shared native term
forces its independently retained lowered endpoints to agree. -/
def composePath (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory)
    {source middle target : NativeRawTm 0 0}
    (first : familiesCwF.Tm PrimeContext
      (interpretation.computationTy presentation source middle))
    (second : familiesCwF.Tm PrimeContext
      (interpretation.computationTy presentation middle target)) :
    familiesCwF.Tm PrimeContext
      (interpretation.computationTy presentation source target) :=
  fun context => by
    obtain ⟨sourceEndpoint, firstMiddle, firstPath⟩ := first context
    obtain ⟨secondMiddle, targetEndpoint, secondPath⟩ := second context
    have middleEq : firstMiddle = secondMiddle := Subsingleton.elim _ _
    subst secondMiddle
    exact ⟨sourceEndpoint, targetEndpoint,
      EventPath.append presentation firstPath secondPath⟩

@[simp] theorem return_compose
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory)
    {source target : NativeRawTm 0 0}
    (sourceEndpoint : interpretation.Endpoint source)
    (path : familiesCwF.Tm PrimeContext
      (interpretation.computationTy presentation source target)) :
    interpretation.composePath presentation
      (interpretation.returnPath presentation sourceEndpoint) path = path := by
  funext context
  rcases pathEq : path context with ⟨pathSource, pathTarget, eventPath⟩
  have sourceEq : sourceEndpoint = pathSource := Subsingleton.elim _ _
  subst pathSource
  simp only [composePath, returnPath, pathEq]
  rw [EventPath.nil_append]

@[simp] theorem compose_return
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory)
    {source target : NativeRawTm 0 0}
    (targetEndpoint : interpretation.Endpoint target)
    (path : familiesCwF.Tm PrimeContext
      (interpretation.computationTy presentation source target)) :
    interpretation.composePath presentation path
      (interpretation.returnPath presentation targetEndpoint) = path := by
  funext context
  rcases pathEq : path context with ⟨pathSource, pathTarget, eventPath⟩
  have targetEq : pathTarget = targetEndpoint := Subsingleton.elim _ _
  subst targetEndpoint
  simp only [composePath, returnPath, pathEq]
  rw [EventPath.append_nil]

end EndpointInterpretation

/-! ## Rho instance -/

/-- The conservative rho interpretation admits exactly first-class runtime
patterns.  Every other MeTTa Native constructor remains uninterpreted. -/
def rhoInterpretation : EndpointInterpretation rhoOccurrenceTheory where
  lower?
    | .pattern pattern => some pattern
    | _ => none

@[simp] theorem rhoInterpretation_pattern (pattern : Pattern) :
    rhoInterpretation.lower? (.pattern pattern) = some pattern :=
  rfl

@[simp] theorem rhoInterpretation_pi
    (domain : NativeRawTm 0 0) (body : NativeRawTm 0 1) :
    rhoInterpretation.lower? (.pi domain body) = none :=
  rfl

def rhoPatternEndpoint (pattern : Pattern) :
    rhoInterpretation.Endpoint (.pattern pattern) :=
  ⟨pattern, rfl⟩

/-- The fully generic native interaction type specializes to exact rho paths
at pattern endpoints. -/
abbrev interpretedRhoComputationTy (source target : NativeRawTm 0 0) :=
  rhoInterpretation.computationTy rhoOccurrencePresentation source target

/-- Positive: every exact rho step inhabits the generic interpretation at its
two first-class pattern endpoints. -/
def interpretedRhoStep {source target : Pattern}
    (step : Reduces source target) :
    familiesCwF.Tm PrimeContext
      (interpretedRhoComputationTy (.pattern source) (.pattern target)) :=
  fun _ =>
    ⟨rhoPatternEndpoint source, rhoPatternEndpoint target,
      .cons (site := ()) step (.nil (rhoPatternEndpoint target).1)⟩

/-- Negative: an uninterpreted dependent-function constructor cannot acquire
an outgoing rho computation through the generic interface. -/
theorem pi_has_no_interpreted_rho_computation
    (domain : NativeRawTm 0 0) (body : NativeRawTm 0 1)
    (target : NativeRawTm 0 0) :
    ¬ Nonempty
      ((interpretedRhoComputationTy (.pi domain body) target) PUnit.unit) := by
  rintro ⟨sourceEndpoint, _targetEndpoint, _path⟩
  have impossible : False := by
    simpa [EndpointInterpretation.Endpoint, rhoInterpretation] using
      sourceEndpoint.2
  exact impossible

/-! ## A dependent request/response protocol -/

def indexedChannel : Pattern := .apply "prime-indexed-service" []

def naturalPayload (count : Nat) : Pattern :=
  .apply "Natural" [.apply (toString count) []]

def indexedCommSource (count : Nat) : Pattern :=
  .collection .hashBag
    [.apply "POutput" [indexedChannel, naturalPayload count],
      .apply "PInput" [indexedChannel, .lambda none (.bvar 0)]] none

def indexedCommTarget (count : Nat) : Pattern :=
  .collection .hashBag [semanticCommSubst (.bvar 0) (naturalPayload count)] none

/-- COMM is uniform in the requested response size. -/
def indexedComm (count : Nat) :
    Reduces (indexedCommSource count) (indexedCommTarget count) :=
  Reduces.comm

/-- A response whose actual arity is proven equal to the requested arity.
The field family is indexed by the actual arity, so the proof transports it
to the continuation selected by the request. -/
structure SizedResponse (expected : Nat) where
  actual : Nat
  field : Fin actual → Pattern
  exactSize : actual = expected

def exactResponse (count : Nat) : SizedResponse count where
  actual := count
  field := fun _ => naturalPayload count
  exactSize := rfl

/-- The body of the dependent protocol: after receiving `count`, retain both
the exact COMM event and a response whose size is indexed by `count`. -/
def indexedProtocolBodyTy :
    familiesCwF.Ty (familiesCwF.ext PrimeContext (fun _ => Nat)) :=
  fun indexed =>
    ((interpretedRhoComputationTy
        (.pattern (indexedCommSource indexed.2))
        (.pattern (indexedCommTarget indexed.2))) indexed.1) ×
      SizedResponse indexed.2

/-- Prime's native semantic type for the protocol:
`(count : Nat) → Compρ(source count, target count) × SizedResponse count`. -/
def indexedProtocolTy : familiesCwF.Ty PrimeContext :=
  familiesCwF.pi (fun _ => Nat) indexedProtocolBodyTy

/-- A single dependent Prime inhabitant handles every natural payload.  The
rho event and the result index are selected by the same received value. -/
def indexedResponder : familiesCwF.Tm PrimeContext indexedProtocolTy :=
  fun context count =>
    ⟨interpretedRhoStep (indexedComm count) context, exactResponse count⟩

@[simp] theorem indexedResponder_exact_size (count : Nat) :
    (indexedResponder PUnit.unit count).2.actual = count :=
  rfl

/-- Negative control: the typed continuation cannot report two fields for a
request whose index was one. -/
theorem one_request_rejects_two_field_response :
    ¬ ∃ response : SizedResponse 1, response.actual = 2 := by
  rintro ⟨response, actualEq⟩
  have impossible : 2 = 1 := actualEq.symm.trans response.exactSize
  omega

#print axioms EndpointInterpretation.return_compose
#print axioms EndpointInterpretation.compose_return
#print axioms pi_has_no_interpreted_rho_computation
#print axioms indexedResponder_exact_size
#print axioms one_request_rejects_two_field_response

end Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation
