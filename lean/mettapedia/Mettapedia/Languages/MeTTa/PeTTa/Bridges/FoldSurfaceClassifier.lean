import Mettapedia.Languages.MeTTa.PeTTa.Bridges.AdditiveFoldSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldCallbackExtraction
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallPortfolio

/-!
# Captured fold-surface classification and its portfolio

Named callbacks use source-certified private unfolding. Natural inline bodies
use the stronger uniform additive certificate and an input-only summary.
Both produce evidence for the independently defined captured host driver.
The classifier reads the actual source Atom and captured operands; it refuses
unsupported shapes, binder aliases, missing captures and non-natural inputs
to the additive worker. It does not implement general evaluator dispatch.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldSurfaceClassifier

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.Dynamics ObservationQualified
open FoldSource SpaceSemantics
open MeTTaIL.WireKit (number)

structure Certified (program : Program) (caller : Subst) (source : Atom) where
  result : Atom
  returns : ∀ state, SurfaceEvaluates program caller state source result

def prepare (budget : Nat) (program : Program) (caller : Subst) :
    (source : Atom) → Option (Certified program caller source)
  | .expression [.symbol "foldl-atom", .var listName, .var initialName, .symbol head] => do
      match listFound : caller.lookup listName with
      | some (.expression items) =>
          match initialFound : caller.lookup initialName with
          | none => none
          | some initial =>
              let compiled ← FoldCallbackExtraction.prepare budget program (.named head) items initial
              return ⟨compiled.result, fun state =>
                .named listName initialName head items initial compiled.result listFound initialFound
                  (compiled.returns state)⟩
      | _ => none
  | .expression [.symbol "foldl-atom", .var listName, .var initialName,
      .var accumulatorName, .var itemName, body] => do
      let certificate ← AdditiveFoldSource.infer caller accumulatorName itemName body
      match listFound : caller.lookup listName with
      | some (.expression items) =>
          match decoded : AdditiveFoldSource.naturals items with
          | none => none
          | some values =>
              match initialFound : caller.lookup initialName with
              | none => none
              | some initialAtom =>
                  match initialDecoded : AdditiveFoldSource.natural initialAtom with
                  | none => none
                  | some initial =>
                      return ⟨number (AdditiveFoldSource.aggregate certificate.weight values initial),
                        fun state => AdditiveFoldSource.surface_returns certificate program state listName initialName values initial
                          (by rw [← AdditiveFoldSource.naturals_exact items values decoded]; exact listFound)
                          (by rw [← AdditiveFoldSource.natural_exact initialAtom initial initialDecoded]; exact initialFound)⟩
      | _ => none
  | _ => none

def sourceMeaning (program : Program) (caller : Subst) (source : Atom)
    (state : Effects.State) : Set PureCallPortfolio.Completed :=
  { observed | ∃ value, SurfaceEvaluates program caller state source value ∧
      observed = PureCallPortfolio.complete state value }

def boundary (program : Program) (caller : Subst) (source : Atom) :
    Boundary Effects.State (Set PureCallPortfolio.Completed) (Set PureCallPortfolio.Completed) where
  source := sourceMeaning program caller source
  summarize := id
  future := PureCallPortfolio.questions
  sufficient _ _ same question := congrArg question same

theorem source_singleton {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) (state : Effects.State) :
    sourceMeaning program caller source state = {PureCallPortfolio.complete state compiled.result} := by
  ext observed
  constructor
  · rintro ⟨value, returned, rfl⟩
    rw [surface_unique returned (compiled.returns state)]
    exact Set.mem_singleton _
  · intro present
    rw [Set.mem_singleton_iff] at present
    exact ⟨compiled.result, compiled.returns state, present⟩

def region {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) : CertifiedRegion (boundary program caller source) Nat where
  regime := 0
  Artifact := PureCallPortfolio.Completed
  attempt state := .committed (PureCallPortfolio.complete state compiled.result)
  decode observed := {observed}
  restores _ _ impossible := by cases impossible
  exact state _ committed := by
    cases committed
    exact (source_singleton compiled state).symm

inductive Observer | completed | callbackPrefixes | sourcePage
  deriving DecidableEq

/-- A summary route does not inherit the stronger trace or source-page
observation merely because those clients share the same final value. -/
def classify (observer : Observer) (budget : Nat) (program : Program) (caller : Subst)
    (source : Atom) : Option (CertifiedRegion (boundary program caller source) Nat) :=
  match observer with
  | .completed => (prepare budget program caller source).map region
  | .callbackPrefixes | .sourcePage => none

theorem callback_prefixes_decline (budget : Nat) (program : Program) (caller : Subst) (source : Atom) :
    classify .callbackPrefixes budget program caller source = none := rfl

theorem source_pages_decline (budget : Nat) (program : Program) (caller : Subst) (source : Atom) :
    classify .sourcePage budget program caller source = none := rfl

theorem classified_exact (observer : Observer) (budget : Nat) (program : Program) (caller : Subst)
    (source : Atom) (candidate : CertifiedRegion (boundary program caller source) Nat)
    (_accepted : classify observer budget program caller source = some candidate) (state : Effects.State) :
    candidate.execute state = sourceMeaning program caller source state :=
  congrFun candidate.execute_eq_reference state

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldSurfaceClassifier
