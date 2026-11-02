import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallExtraction

/-!
# Pure-call extraction at the completed-source observation boundary

The reference is the set of completed observations of the existing independent
PeTTa operational judgment. It includes the final store, ordered answer list
and input/output observations. Successful partial evaluation produces a
singleton whose equality with that reference is proved, not defined.

Exact source-page observers are refused by this classifier. They use the
reference evaluator until a separate source-debit/residual correspondence
licenses a faster page. Program, captured environment and source occurrence
index the certificate; currentness is still required before cache reuse.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallPortfolio

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.Dynamics ObservationQualified
open Eval SpaceSemantics PureCallExtraction
open DeclarativeSpec (Runs)

structure Completed where
  state : Effects.State
  answers : List Atom
  input : List Atom
  output : List Atom

def sourceMeaning (program : Program) (caller : Subst) (source : Atom)
    (state : Effects.State) : Set Completed :=
  { observed | Runs program {state, control := .evaluate caller source}
      (.complete observed.state observed.answers observed.input observed.output) }

def questions : RegionObservations.Family (Set Completed) where
  Question := Set Completed → Bool
  Answer _ := Bool
  read question observed := question observed

def boundary (program : Program) (caller : Subst) (source : Atom) :
    Boundary Effects.State (Set Completed) (Set Completed) where
  source := sourceMeaning program caller source
  summarize := id
  future := questions
  sufficient _ _ same question := congrArg question same

def complete (state : Effects.State) (value : Atom) : Completed := ⟨state, [value], [], []⟩

theorem sourceMeaning_singleton {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) (state : Effects.State) :
    sourceMeaning program caller source state = {complete state compiled.value} := by
  ext observed
  change Runs program {state, control := .evaluate caller source}
      (.complete observed.state observed.answers observed.input observed.output) ↔ _
  rw [pure_returns_derivation_iff program caller state state source compiled.value
    (compiled.returns state)]
  cases observed
  simp [complete, Completed.mk.injEq]

def region {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) : CertifiedRegion (boundary program caller source) Nat where
  regime := 0
  Artifact := Completed
  attempt state := .committed (complete state compiled.value)
  decode observed := {observed}
  restores _ _ impossible := by cases impossible
  exact state _ committed := by
    cases committed
    exact (sourceMeaning_singleton compiled state).symm

/-- Source fuel and residual identity are not erased merely because the
expression has a unique eventual answer. -/
def classify (observation : Observation) (budget : Nat) (program : Program)
    (caller : Subst) (source : Atom) : Option (CertifiedRegion (boundary program caller source) Nat) :=
  match observation with
  | .exactPage => none
  | .completedResult => (prepare budget program caller source).map region

theorem page_refused (budget : Nat) (program : Program) (caller : Subst) (source : Atom) :
    classify .exactPage budget program caller source = none := rfl

theorem unsupported_refused (budget : Nat) (program : Program) (caller : Subst) (source : Atom)
    (unsupported : prepare budget program caller source = none) :
    classify .completedResult budget program caller source = none := by
  simp [classify, unsupported]

theorem classified_preserves_observation (observation : Observation) (budget : Nat)
    (program : Program) (caller : Subst) (source : Atom)
    (candidate : CertifiedRegion (boundary program caller source) Nat)
    (_accepted : classify observation budget program caller source = some candidate)
    (state : Effects.State) : candidate.execute state = sourceMeaning program caller source state := by
  exact congrFun candidate.execute_eq_reference state

/-- A renamed captured-call interface can reuse the same compiled value
when the actual captured values and the source's demand contract agree. -/
theorem transported_value_unchanged {allowed : String → Bool} {first second : Program}
    {caller : Subst} {source : Atom} (compiled : Certified first caller source)
    (closed : ProgramClosed allowed first) (agreement : ProgramAgreementOn allowed first second)
    (within : codeWithin allowed source = true) (state : Effects.State) :
    (region (compiled.transport closed agreement within)).execute state =
      (region compiled).execute state := by
  rw [CertifiedRegion.execute_eq_reference, CertifiedRegion.execute_eq_reference]
  change sourceMeaning second caller source state = sourceMeaning first caller source state
  rw [sourceMeaning_singleton (compiled.transport closed agreement within) state,
    sourceMeaning_singleton compiled state]
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallPortfolio
