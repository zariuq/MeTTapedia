import Mettapedia.GSLT.Core.InteractionComposition
import Mettapedia.Languages.MeTTa.NativeTypeTheoryDerivation
import Mettapedia.Languages.MeTTa.Prime.RhoNonCollapse
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-!
# Prime-native interaction computations

Rho-style interaction belongs inside Prime as an indexed computation fibre,
not as a replacement for MeTTa Native's dependent core.  This module
internalizes occurrence-preserving `EventPath`s as ordinary types and terms of
Prime's semantic CwF.  Endpoints index the type, so a computation cannot claim
an endpoint that is absent from its authenticated event path.

The generic construction is instantiated with the foundational rho reduction
relation.  `Reduction.Reduces` is already `Type`-valued, so individual COMM,
EQUIV, and PAR derivations remain distinguishable interaction events.  Their
erasure is the ordinary propositional GSLT step relation; no scheduler or
handler receives authority to manufacture a transition.

This is a semantic internalization boundary.  It does not claim that the
corresponding authored syntax has already been added to Prime's grammar.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeInteraction

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.Languages.MeTTa.NativeTypeTheory
open Mettapedia.Languages.MeTTa.Prime.RhoNonCollapse
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Generic internal interaction fibre -/

/-- Closed stage-zero context used for Prime semantic values. -/
abbrev PrimeContext := familiesCwF.empty (stageOfNat 0)

/-- An endpoint-indexed interaction computation is a Prime semantic type.
Its inhabitants retain every exact event occurrence. -/
def interactionComputationTy {theory : GSLT}
    (presentation : InteractionPresentation theory)
    (source target : theory.Term) : familiesCwF.Ty PrimeContext :=
  fun _ => EventPath presentation source target

/-- An authenticated event path is an ordinary closed Prime semantic term. -/
def internalPath {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {source target : theory.Term}
    (path : EventPath presentation source target) :
    familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation source target) :=
  fun _ => path

/-- The empty path is the identity interaction computation. -/
def returnPath {theory : GSLT}
    (presentation : InteractionPresentation theory)
    (term : theory.Term) :
    familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation term term) :=
  internalPath (.nil term)

/-- Sequential composition is authenticated path append, internalized as a
Prime term. -/
def composePath {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {source middle target : theory.Term}
    (firstPath : familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation source middle))
    (secondPath : familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation middle target)) :
    familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation source target) :=
  fun context =>
    EventPath.append presentation (firstPath context) (secondPath context)

@[simp] theorem return_compose {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {source target : theory.Term}
    (path : familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation source target)) :
    composePath (returnPath presentation source) path = path :=
  rfl

@[simp] theorem compose_return {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {source target : theory.Term}
    (path : familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation source target)) :
    composePath path (returnPath presentation target) = path := by
  funext context
  exact EventPath.append_nil presentation (path context)

@[simp] theorem compose_assoc {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {first second third fourth : theory.Term}
    (left : familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation first second))
    (middle : familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation second third))
    (right : familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation third fourth)) :
    composePath (composePath left middle) right =
      composePath left (composePath middle right) := by
  funext context
  exact EventPath.append_assoc presentation
    (left context) (middle context) (right context)

/-- Erasing occurrence identity yields an ordinary authorized rewrite path. -/
def eraseInternalPath {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {source target : theory.Term}
    (path : familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation source target)) :
    familiesCwF.Tm PrimeContext (fun _ => theory.RewritePath source target) :=
  fun context => (path context).erase

@[simp] theorem eraseInternalPath_length {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {source target : theory.Term}
    (path : familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation source target))
    (context : PrimeContext) :
    (eraseInternalPath path context).length =
      EventPath.pathLength presentation (path context) :=
  EventPath.erase_length presentation (path context)

/-- One authenticated event becomes a one-edge internal computation. -/
def internalEvent {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {site : presentation.Site} {source target : theory.Term}
    (event : presentation.Event site source target) :
    familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation source target) :=
  internalPath (.cons event (.nil target))

/-- Erasing an internal one-event computation exposes exactly the semantic
step authorized by that event. -/
@[simp] theorem eraseInternalEvent {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {site : presentation.Site} {source target : theory.Term}
    (event : presentation.Event site source target)
    (context : PrimeContext) :
    eraseInternalPath (internalEvent event) context =
      .cons (presentation.sound event) (.nil target) :=
  rfl

/-! ## The foundational rho calculus as an interaction presentation -/

/-- Endpoint semantics of the foundational rho calculus.  The GSLT step is
the propositional erasure of the `Type`-valued reduction derivation. -/
def rhoOccurrenceTheory : GSLT where
  Term := Pattern
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => Nonempty (Reduces source target)
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Every exact rho reduction derivation is an occurrence-specific event. -/
def rhoOccurrencePresentation : InteractionPresentation rhoOccurrenceTheory where
  Site := Unit
  Event := fun _ source target => Reduces source target
  sound := fun event => ⟨event⟩

/-- The occurrence presentation covers every erased rho step. -/
theorem rhoOccurrencePresentation_complete :
    rhoOccurrencePresentation.Complete := by
  intro source target step
  obtain ⟨event⟩ := step
  exact ⟨⟨(), event⟩⟩

/-- Prime's internal endpoint-indexed computation type for rho reduction. -/
abbrev rhoComputationTy (source target : Pattern) :
    familiesCwF.Ty PrimeContext :=
  interactionComputationTy rhoOccurrencePresentation source target

/-- Any exact rho derivation enters Prime as an authenticated interaction
computation, without becoming a new static type-theory constructor. -/
def internalRhoStep {source target : Pattern}
    (step : Reduces source target) :
    familiesCwF.Tm PrimeContext (rhoComputationTy source target) :=
  internalEvent (site := ()) step

@[simp] theorem internalRhoStep_erases {source target : Pattern}
    (step : Reduces source target) (context : PrimeContext) :
    eraseInternalPath (internalRhoStep step) context =
      .cons (show rhoOccurrenceTheory.Step source target from ⟨step⟩)
        (GSLT.RewritePath.nil (S := rhoOccurrenceTheory) target) :=
  rfl

/-! ## Applying rho interaction to MeTTa Native terms -/

/-- Evidence that one exact closed MeTTa Native term is a rho-executable
runtime pattern.  This is an indexed admission witness, not a partial cast. -/
structure RhoEndpoint (term : NativeRawTm 0 0) where
  pattern : Pattern
  term_eq : term = (.pattern pattern : NativeRawTm 0 0)

/-- Every first-class runtime pattern has its canonical rho endpoint. -/
def patternEndpoint (pattern : Pattern) :
    RhoEndpoint (.pattern pattern : NativeRawTm 0 0) where
  pattern := pattern
  term_eq := rfl

/-- A rho interaction computation indexed by its actual MeTTa Native endpoint
terms.  An inhabitant must retain both endpoint admissions and the exact
occurrence-preserving rho path between their patterns. -/
def nativeRhoComputationTy (source target : NativeRawTm 0 0) :
    familiesCwF.Ty PrimeContext :=
  fun _ =>
    Σ sourceEndpoint : RhoEndpoint source,
      Σ targetEndpoint : RhoEndpoint target,
        EventPath rhoOccurrencePresentation sourceEndpoint.pattern
          targetEndpoint.pattern

/-- A rho reduction lifts directly to a computation between the corresponding
first-class MeTTa Native pattern terms. -/
def internalNativeRhoStep {source target : Pattern}
    (step : Reduces source target) :
    familiesCwF.Tm PrimeContext
      (nativeRhoComputationTy (.pattern source) (.pattern target)) :=
  fun context =>
    ⟨patternEndpoint source, patternEndpoint target,
      internalRhoStep step context⟩

/-- A dependent function type is not an admitted rho endpoint. -/
theorem nativeDependentFunctionType_has_no_rhoEndpoint :
    ¬ Nonempty (RhoEndpoint nativeDependentFunctionType) := by
  rintro ⟨endpoint⟩
  apply nativeDependentFunctionType_not_directRho
  rw [endpoint.term_eq]
  exact .pattern endpoint.pattern

/-- Consequently no rho interaction computation can use the dependent
function type as its native source endpoint. -/
theorem nativeDependentFunctionType_has_no_outgoing_rhoComputation
    (target : NativeRawTm 0 0) :
    ¬ Nonempty
      ((nativeRhoComputationTy nativeDependentFunctionType target) PUnit.unit) := by
  rintro ⟨sourceEndpoint, _targetEndpoint, _path⟩
  exact nativeDependentFunctionType_has_no_rhoEndpoint ⟨sourceEndpoint⟩

/-! ## Positive and negative controls -/

def commChannel : Pattern := .apply "prime-rho-channel" []
def commPayload : Pattern := .apply "prime-rho-payload" []
def commBody : Pattern := .bvar 0

def commSource : Pattern :=
  .collection .hashBag
    [.apply "POutput" [commChannel, commPayload],
      .apply "PInput" [commChannel, .lambda none commBody]] none

def commTarget : Pattern :=
  .collection .hashBag [semanticCommSubst commBody commPayload] none

/-- Positive: a concrete COMM derivation is an intrinsic Prime interaction
term whose type fixes both endpoints. -/
def internalComm :
    familiesCwF.Tm PrimeContext (rhoComputationTy commSource commTarget) :=
  internalRhoStep Reduces.comm

/-- The same COMM step, now indexed by its exact MeTTa Native terms. -/
def internalNativeComm :
    familiesCwF.Tm PrimeContext
      (nativeRhoComputationTy (.pattern commSource) (.pattern commTarget)) :=
  internalNativeRhoStep Reduces.comm

@[simp] theorem internalComm_length (context : PrimeContext) :
    EventPath.pathLength rhoOccurrencePresentation (internalComm context) = 1 :=
  rfl

def emptyParallel : Pattern := .collection .hashBag [] none

/-- Negative: the empty parallel process cannot manufacture an interaction
event. -/
theorem emptyParallel_has_no_event (target : Pattern) :
    ¬ Nonempty (Reduces emptyParallel target) := by
  rintro ⟨event⟩
  exact emptyBag_SC_irreducible (.refl _) event

/-- Internalizing rho interaction leaves the structural non-collapse theorem
intact: the dependent native core is still not spanned by direct rho terms. -/
theorem nativeInteraction_does_not_collapse_prime_to_rho :
    ¬ RhoSpansNativeAt 0 0 :=
  rho_does_not_span_closed_native_core

#print axioms compose_assoc
#print axioms eraseInternalEvent
#print axioms rhoOccurrencePresentation_complete
#print axioms internalRhoStep_erases
#print axioms nativeDependentFunctionType_has_no_rhoEndpoint
#print axioms nativeDependentFunctionType_has_no_outgoing_rhoComputation
#print axioms emptyParallel_has_no_event
#print axioms nativeInteraction_does_not_collapse_prime_to_rho

end Mettapedia.Languages.MeTTa.Prime.NativeInteraction
