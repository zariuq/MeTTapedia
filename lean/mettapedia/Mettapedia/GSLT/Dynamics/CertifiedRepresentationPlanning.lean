import Mettapedia.GSLT.Dynamics.RepresentationSwitching
import Mettapedia.GSLT.Core.CertifiedPlanning

/-!
# Work plans with certificates for mixed representation execution

The authored Region/Hole plan describes the requested computation. A proposed
work plan chooses an engine for each segment and supplies concrete conversion
arrows. `CertifiedRoute` additionally ties its erased route to that authored
plan; the local proof obligations reside in its family and transfer objects.

This bridge embeds those routes into the existing certified-planning layer.
Finite support governs reusable program knowledge. It does not cache a binding
image: the current input state is passed to each selected execution separately.
Changing the implementation environment may change the physical result, but
cannot change the decoded residual computation. Invalidated admission uses
the existing `PartialRealization.withFallback` contract.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.CertifiedRepresentationPlanning

open RegionHolePlan RepresentationSwitching OrderedOccurrenceBodyAlgebra

universe uObj uRegion uHole uEngine uState uDeclaration uConfig

variable {Obj : Type uObj} {Region : Obj → Obj → Type uRegion}
  {Hole : Obj → Obj → Type uHole} {Engine : Type uEngine}
  {source : IndexedCategory Obj Region}
  {family : Family source Hole functionCategory.{uState} Engine}
  {start : Engine} {X Y : Obj}

/-- A complete work plan carries all local boundary evidence and proves it
implements the requested source plan, rather than a convenient substitute. -/
structure CertifiedRoute (family : Family source Hole functionCategory.{uState} Engine)
    (start : Engine) {X Y : Obj} (authored : Plan Obj Region Hole X Y) where
  finish : Engine
  execution : Execution family start X finish Y
  source_exact : execution.erase = authored

abbrev Result (family : Family source Hole functionCategory.{uState} Engine) (Y : Obj) :=
  (mode : Engine) × (family.engine mode).objectMap Y

def observeResult (result : Result family Y) : family.reference.objectMap Y :=
  (family.decode result.1).component Y result.2

def CertifiedRoute.run {authored : Plan Obj Region Hole X Y}
    (route : CertifiedRoute family start authored)
    (initial : (family.engine start).objectMap X) : Result family Y :=
  ⟨route.finish, route.execution.denote initial⟩

/-- This is derived from generator-local proofs and path composition; it is
not an equality of two definitions which invoke the same interpreter. -/
theorem CertifiedRoute.run_exact {authored : Plan Obj Region Hole X Y}
    (route : CertifiedRoute family start authored)
    (initial : (family.engine start).objectMap X) :
    observeResult (route.run initial) =
      Plan.denote family.reference authored ((family.decode start).component X initial) := by
  have square := congrFun (Execution.denote_decode route.execution) initial
  change observeResult (route.run initial) =
    Plan.denote family.reference route.execution.erase
      ((family.decode start).component X initial) at square
  rw [route.source_exact] at square
  exact square

/-- Every subsequent observer of the reference residual sees the same
execution. This includes running a remaining continuation before observing. -/
theorem CertifiedRoute.continue_exact {authored : Plan Obj Region Hole X Y}
    (route : CertifiedRoute family start authored)
    (initial : (family.engine start).objectMap X)
    {Observation : Type*} (continuation : family.reference.objectMap Y → Observation) :
    continuation (observeResult (route.run initial)) =
      continuation (Plan.denote family.reference authored
        ((family.decode start).component X initial)) :=
  congrArg continuation (route.run_exact initial)

/-- A choice of certified routes gives the standard observation-indexed
realization. The output retains which physical engine owns the residual. -/
def realization
    (select : (authored : Plan Obj Region Hole X Y) →
      CertifiedRoute family start authored) :
    Mettapedia.GSLT.Realization
      (fun _ : Unit => Plan Obj Region Hole X Y × (family.engine start).objectMap X)
      (fun _ : Unit => Result family Y)
      (fun _ : Unit => family.reference.objectMap Y) where
  compile _ request := (select request.1).run request.2
  observeSource _ request := Plan.denote family.reference request.1
    ((family.decode start).component X request.2)
  observeArtifact _ := observeResult
  adequate _ request := (select request.1).run_exact request.2

/-- Supported planning and mixed execution compose without a new cache
authority. Support is inherited from the selected route; the input branch
image is an explicit argument, not one of the cached program facts. -/
def supportedRealization
    {Declaration : Type uDeclaration} [DecidableEq Declaration]
    {Config : Type uConfig}
    (plans : (authored : Plan Obj Region Hole X Y) →
      Mettapedia.GSLT.FinitelySupportedPlan Declaration Config
        (CertifiedRoute family start authored)) :
    Mettapedia.GSLT.PlannedRealization (Declaration := Declaration) Config
      (fun _ : Unit => Plan Obj Region Hole X Y × (family.engine start).objectMap X)
      (fun _ : Unit => Result family Y)
      (fun _ : Unit => family.reference.objectMap Y) where
  plan _ request := (plans request.1).map (fun route => route.run request.2)
  observeSource _ request := Plan.denote family.reference request.1
    ((family.decode start).component X request.2)
  observeArtifact _ := observeResult
  adequate _ request environment := ((plans request.1).run environment).run_exact request.2

/-- An option-valued runtime converter is the operational form of the
existing partial-realization contract. Refusal is admission failure, not a
claim that the source computation has no answers. -/
def guardedAsPartial {Source Target Observation : Type*}
    {sourceView : Source → Observation} {targetView : Target → Observation}
    (transfer : GuardedTransfer sourceView targetView) :
    Mettapedia.GSLT.PartialRealization (fun _ : Unit => Source)
      (fun _ : Unit => Target) (fun _ : Unit => Observation) where
  accepts _ state := (transfer.attempt state).isSome
  compile _ state accepted := (transfer.attempt state).get (by simpa using accepted)
  observeSource _ := sourceView
  observeArtifact _ := targetView
  adequate _ state accepted :=
    transfer.correct state _ (Option.some_get accepted).symm

#print axioms CertifiedRoute.run_exact
#print axioms supportedRealization
#print axioms guardedAsPartial

end Mettapedia.GSLT.Dynamics.CertifiedRepresentationPlanning
