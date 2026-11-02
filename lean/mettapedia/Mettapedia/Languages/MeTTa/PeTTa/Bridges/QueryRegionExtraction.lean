import Mettapedia.Languages.MeTTa.PeTTa.Bridges.OptionalCallExtraction
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallPortfolio

/-!
# Snapshot-qualified extraction of match/collapse/count source regions

The source matcher produces the exact row-local bindings in occurrence order.
Each selected body is independently certified to return zero or one answer
without effects. The prepared route keeps that ordered answer list; a count
route may expose only its length because its actual source includes size-atom.

Execution rereads the space through the original captured handle and checks
the complete snapshot. A mismatch declines with the entrance state unchanged.
This is an Atom-level validity law, not a native root, allocation or lifetime
proof. Preparation and answer storage costs are not hidden in a speed claim.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryRegionExtraction

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.GSLT.Dynamics ObservationQualified
open Eval SpaceSemantics

def collectionSource (spaceName : String) (pattern body : Atom) : Atom :=
  .expression [.symbol "collapse", .expression [.symbol "match", .var spaceName, pattern, body]]

def countSource (spaceName : String) (pattern body : Atom) : Atom :=
  .expression [.symbol "size-atom", collectionSource spaceName pattern body]

def read (state : Effects.State) (caller : Subst) (spaceName : String) : Option (List Atom) :=
  Effects.readHandle (applySubst caller (.var spaceName)) >>= state.read

structure Prepared (program : Program) (caller : Subst) (spaceName : String) (pattern body : Atom) where
  rows : List Atom
  compiled : OptionalCallExtraction.Alternatives program (queryBodies caller rows pattern body)

def prepare (budget : Nat) (program : Program) (caller : Subst) (spaceName : String)
    (pattern body : Atom) (state : Effects.State) :
    Option (Prepared program caller spaceName pattern body) := do
  let rows ← read state caller spaceName
  let compiled ← OptionalCallExtraction.prepare.alternatives program
    (OptionalCallExtraction.prepare budget program) (queryBodies caller rows pattern body)
  return ⟨rows, compiled⟩

private theorem path_trans {system : Mettapedia.GSLT.GSLT} {a b c : system.Term}
    (first : system.MultiStep a b) (second : system.MultiStep b c) : system.MultiStep a c := by
  induction first with
  | refl _ => exact second
  | step step _ ih => exact .step step (ih second)

theorem Prepared.collection_returns {program : Program} {caller : Subst} {spaceName : String}
    {pattern body : Atom} (prepared : Prepared program caller spaceName pattern body)
    (state : Effects.State) (snapshot : read state caller spaceName = some prepared.rows) :
    PureReturns program caller state (collectionSource spaceName pattern body) state
      (.expression prepared.compiled.values) := by
  apply collapse_returns program caller state state _ _
  refine .step (step_transition rfl) (path_trans
    (path_with_caller_frames program [.query caller pattern body]
      (variable_returns program caller state spaceName)) ?_)
  refine .step (step_transition rfl) ?_
  simp only [withFrames, finished, List.nil_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  change (theory program).MultiStep
    {state, control := .sequence (queryAlternatives state caller
      (applySubst caller (.var spaceName)) pattern body) []}
    (finished state prepared.compiled.values [] [])
  unfold read at snapshot
  simp only [queryAlternatives, snapshot]
  simpa using prepared.compiled.returns state []

theorem Prepared.count_returns {program : Program} {caller : Subst} {spaceName : String}
    {pattern body : Atom} (prepared : Prepared program caller spaceName pattern body)
    (state : Effects.State) (snapshot : read state caller spaceName = some prepared.rows) :
    PureReturns program caller state (countSource spaceName pattern body) state
      (.grounded (.int prepared.compiled.values.length)) := by
  apply native_unary_call_returns program caller state state state "size-atom"
    (collectionSource spaceName pattern body) (.expression prepared.compiled.values)
    (.grounded (.int prepared.compiled.values.length))
    (by decide) (by decide) (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (prepared.collection_returns state snapshot) rfl (by decide)

inductive Observer | collection | count
  deriving DecidableEq

def source (observer : Observer) (spaceName : String) (pattern body : Atom) : Atom :=
  match observer with
  | .collection => collectionSource spaceName pattern body
  | .count => countSource spaceName pattern body

def Prepared.value {program : Program} {caller : Subst} {spaceName : String} {pattern body : Atom}
    (prepared : Prepared program caller spaceName pattern body) : Observer → Atom
  | .collection => .expression prepared.compiled.values
  | .count => .grounded (.int prepared.compiled.values.length)

theorem Prepared.returns {program : Program} {caller : Subst} {spaceName : String} {pattern body : Atom}
    (prepared : Prepared program caller spaceName pattern body) (observer : Observer)
    (state : Effects.State) (snapshot : read state caller spaceName = some prepared.rows) :
    PureReturns program caller state (source observer spaceName pattern body) state
      (prepared.value observer) := by
  cases observer
  · exact prepared.collection_returns state snapshot
  · exact prepared.count_returns state snapshot

theorem Prepared.source_singleton {program : Program} {caller : Subst} {spaceName : String}
    {pattern body : Atom} (prepared : Prepared program caller spaceName pattern body)
    (observer : Observer) (state : Effects.State) (snapshot : read state caller spaceName = some prepared.rows) :
    PureCallPortfolio.sourceMeaning program caller (source observer spaceName pattern body) state =
      {PureCallPortfolio.complete state (prepared.value observer)} := by
  ext observed
  change DeclarativeSpec.Runs program {state, control := .evaluate caller (source observer spaceName pattern body)}
      (.complete observed.state observed.answers observed.input observed.output) ↔ _
  rw [pure_returns_derivation_iff program caller state state _ _ (prepared.returns observer state snapshot)]
  cases observed
  simp [PureCallPortfolio.complete, PureCallPortfolio.Completed.mk.injEq]

def Prepared.region {program : Program} {caller : Subst} {spaceName : String} {pattern body : Atom}
    (prepared : Prepared program caller spaceName pattern body) (observer : Observer) :
    CertifiedRegion (PureCallPortfolio.boundary program caller (source observer spaceName pattern body)) Nat where
  regime := 1
  Artifact := PureCallPortfolio.Completed
  attempt state := if read state caller spaceName = some prepared.rows then
    .committed (PureCallPortfolio.complete state (prepared.value observer)) else .declined state
  decode observed := {observed}
  restores state restored declined := by
    dsimp only at declined
    split at declined
    · cases declined
    · exact (PartialRegionPlan.Attempt.declined.inj declined).symm
  exact state observed committed := by
    split at committed
    next snapshot =>
      cases committed
      exact (prepared.source_singleton observer state snapshot).symm
    next => cases committed

theorem snapshot_change_declines {program : Program} {caller : Subst} {spaceName : String}
    {pattern body : Atom} (prepared : Prepared program caller spaceName pattern body)
    (observer : Observer) (state : Effects.State) (changed : read state caller spaceName ≠ some prepared.rows) :
    (prepared.region observer).attempt state = .declined state := by
  simp [Prepared.region, changed]

/-- An invalid handle cannot supply complete-domain evidence for absence. -/
theorem invalid_space_refuses (budget : Nat) (program : Program) (caller : Subst) (spaceName : String)
    (pattern body : Atom) (state : Effects.State) (invalid : read state caller spaceName = none) :
    prepare budget program caller spaceName pattern body state = none := by
  simp [prepare, invalid]

/-- Parse the actual source observation, then prepare its row-scoped bodies.
No caller-supplied query IR or function-name whitelist supplies the meaning. -/
def classify (observation : PureCallExtraction.Observation) (budget : Nat)
    (program : Program) (caller : Subst) (state : Effects.State) :
    (source : Atom) → Option (CertifiedRegion (PureCallPortfolio.boundary program caller source) Nat)
  | .expression [.symbol "collapse", .expression [.symbol "match", .var name, pattern, body]] =>
      if observation = .exactPage then none else
        (prepare budget program caller name pattern body state).map (fun p => p.region .collection)
  | .expression [.symbol "size-atom", .expression [.symbol "collapse",
      .expression [.symbol "match", .var name, pattern, body]]] =>
      if observation = .exactPage then none else
        (prepare budget program caller name pattern body state).map (fun p => p.region .count)
  | _ => none

theorem classification_exact (observation : PureCallExtraction.Observation) (budget : Nat)
    (program : Program) (caller : Subst) (entrance : Effects.State) (source : Atom)
    (region : CertifiedRegion (PureCallPortfolio.boundary program caller source) Nat)
    (_classified : classify observation budget program caller entrance source = some region)
    (current : Effects.State) :
    region.execute current = PureCallPortfolio.sourceMeaning program caller source current :=
  congrFun region.execute_eq_reference current

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryRegionExtraction
