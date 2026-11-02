import Mettapedia.GSLT.Dynamics.RegionPortfolio
import Mettapedia.Machines.LiveRegionAdmission

/-!
# Region portfolios at the existing indexed cursor boundary

Replies may change the type of the next state. A portfolio is therefore
indexed by the actual request and current protocol position. Selection keeps
the full reply and residual state, then inherits the existing adaptive-client
theorem. No second cursor syntax or scheduler is introduced.

This bridge is deliberately for full-response boundaries. A lossy summary
cannot implement this interface merely because it preserves a final scalar;
it needs its own sufficient continuation observer and residual reconstruction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObservationQualified.ProtocolBridge

open Mettapedia.Machines.Cursor
open Mettapedia.Machines.Cursor.LiveAdmission
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.TypeTheory

universe u

variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u, u, u, u} Base Index}

def requestBoundary (reference : Provider P) {base : Base} {index : Index base}
    (request : P.Shape base index) :
    Boundary (reference.State base index) (Response reference request) (Response reference request) where
  source state := reference.step state request
  summarize := id
  future := {
    Question := Response reference request → Response reference request
    Answer _ := Response reference request
    read continuation result := continuation result }
  sufficient _ _ same continuation := congrArg continuation same

/-- A proved existing worker is usable by the new catalogue without changing
its algorithm or inventing a fresh adequacy premise. -/
def ofWorker {Regime : Type u} {reference : Provider P}
    (worker : PartialWorker reference) (regime : Regime) {base : Base} {index : Index base}
    (request : P.Shape base index) : CertifiedRegion (requestBoundary reference request) Regime where
  regime := regime
  Artifact := Response reference request
  attempt state := match worker.attempt state request with
    | none => .declined state
    | some result => .committed result
  decode := id
  restores state restored declined := by
    cases attempted : worker.attempt state request with
    | none => simpa [attempted] using declined.symm
    | some result => simp [attempted] at declined
  exact state result accepted := by
    cases attempted : worker.attempt state request with
    | none => simp [attempted] at accepted
    | some observed =>
        have same : observed = result := by simpa [attempted] using accepted
        subst result
        exact worker.correct state request observed attempted

abbrev Catalogue (reference : Provider P) (Regime : Type u) :=
  {base : Base} → {index : Index base} → (request : P.Shape base index) →
    List (Candidate (requestBoundary reference request) Regime)

/-- The selected worker returns its real dependent reply. On refusal no
response is fabricated; the existing PartialWorker driver runs the reference. -/
def worker {Regime : Type u} {reference : Provider P} (catalogue : Catalogue reference Regime) :
    PartialWorker reference where
  attempt state request :=
    match RegionPortfolio.select state (catalogue request) with
    | none => none
    | some selected => match selected.region.attempt state with
      | .declined _ => none
      | .committed artifact => some (selected.region.decode artifact)
  correct state request result accepted := by
    cases chosen : RegionPortfolio.select state (catalogue request) with
    | none => simp [chosen] at accepted
    | some selected =>
        cases attempted : selected.region.attempt state with
        | declined restored => simp [chosen, attempted] at accepted
        | committed artifact =>
            have same : selected.region.decode artifact = result := by
              simpa [chosen, attempted] using accepted
            exact same.symm.trans (selected.region.exact state artifact attempted)

theorem execute_same_reply_and_residual {Regime : Type u} {reference : Provider P}
    (catalogue : Catalogue reference Regime) {base : Base} {index : Index base}
    (state : reference.State base index) (request : P.Shape base index) :
    (worker catalogue).execute state request = reference.step state request :=
  (worker catalogue).execute_exact state request

/-- An adaptive client can form later requests from earlier replies. Its
actual completion/paused residual agrees after any finite scheduler page.
Physical charge receipts remain separate and need not equal source debits. -/
theorem adaptive_page_exact {Regime : Type u} {reference : Provider P}
    (catalogue : Catalogue reference Regime)
    {Return : (base : Base) → Index base → Type u}
    (client : Client (P := P) (Return := Return))
    (actualCharge : Charge (worker catalogue).provider) (referenceCharge : Charge reference)
    (fuel : Nat) {base : Base} (packet : Packet (worker catalogue).provider client base) :
    (worker catalogue).hom.outcome client
      (advance (worker catalogue).provider client actualCharge fuel packet).2 =
      (advance reference client referenceCharge fuel
        ((worker catalogue).hom.packet client packet)).2 :=
  (worker catalogue).advance_exact client actualCharge referenceCharge fuel packet

#print axioms ofWorker
#print axioms worker
#print axioms execute_same_reply_and_residual
#print axioms adaptive_page_exact

end Mettapedia.GSLT.Dynamics.ObservationQualified.ProtocolBridge
