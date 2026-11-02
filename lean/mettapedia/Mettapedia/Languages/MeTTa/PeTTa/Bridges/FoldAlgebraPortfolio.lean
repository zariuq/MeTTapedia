import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldRegionEntry
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ExtremumFoldSource

/-!
# Multiple source-certified algebras for one captured fold

The portfolio gathers ordered callback execution, additive word aggregation,
integer minimum and integer maximum. It does not stop at the first source
spelling recognized. Every candidate has a derivation of the same captured
host fold; external estimates may rank those candidates but cannot admit one.

Mode's histogram route is intentionally absent here: it preserves the final
label after readout, not the fold's four-field accumulator. That route belongs
at the larger mode/readout boundary.

This dispatcher observes completed pure folds. Source pages, callback effects
and prefix observers continue through their unchanged reference interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldAlgebraPortfolio

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.Dynamics ObservationQualified
open SpaceSemantics FoldSourceBoundary MeTTaIL.WireKit

def integerValue : Atom → Option Int
  | .grounded (.int value) => some value
  | _ => none

theorem integerValue_exact (atom : Atom) (value : Int) (decoded : integerValue atom = some value) :
    atom = integer value := by
  cases atom with
  | grounded ground => cases ground <;> cases decoded; rfl
  | var | symbol | expression => cases decoded

def integers (atoms : List Atom) : Option (List Int) := atoms.mapM integerValue

theorem integers_exact (atoms : List Atom) (values : List Int) (decoded : integers atoms = some values) :
    atoms = values.map integer := by
  induction atoms generalizing values with
  | nil => cases decoded; rfl
  | cons atom atoms ih =>
      simp only [integers, List.mapM_cons, Option.bind_eq_bind] at decoded
      obtain ⟨value, first, rest⟩ := Option.bind_eq_some_iff.mp decoded
      obtain ⟨tail, later, result⟩ := Option.bind_eq_some_iff.mp rest
      have same : value :: tail = values := Option.some.inj result
      rw [← same]
      simp [integerValue_exact atom value first, ih tail later]

def extremum (direction : ExtremumFoldSource.Direction) (program : Program) (caller : Subst) :
    (code : Code) → (items : List Atom) → (initial : Atom) → Option (FoldRegionEntry.Driver program caller code items initial)
  | .named _ _ _, _, _ => none
  | .inline _ _ accumulatorName itemName body, items, initial => do
      let certificate ← ExtremumFoldSource.infer direction program caller accumulatorName itemName body
      match decoded : integers items with
      | none => none
      | some values =>
          match start : integerValue initial with
          | none => none
          | some accumulator =>
              return ⟨integer (ExtremumFoldSource.aggregate direction values accumulator), fun world => by
                rw [integers_exact items values decoded, integerValue_exact initial accumulator start]
                exact certificate.fold world values accumulator⟩

def ordered (budget : Nat) (program : Program) (caller : Subst) (code : Code)
    (items : List Atom) (initial : Atom) : Option (FoldRegionEntry.Driver program caller code items initial) :=
  (FoldCallbackExtraction.prepare budget program (code.callback caller) items initial).map fun result =>
    ⟨result.result, result.returns⟩

def additive (budget : Nat) (program : Program) (caller : Subst) (code : Code)
    (items : List Atom) (initial : Atom) : Option (FoldRegionEntry.Driver program caller code items initial) :=
  match code with
  | .named _ _ _ => none
  | .inline list initialSource accumulatorName itemName body =>
      FoldRegionEntry.compileDriver budget program caller (.inline list initialSource accumulatorName itemName body) items initial

inductive Regime | ordered | additive | minimum | maximum
  deriving DecidableEq

def sourceMeaning (program : Program) (caller : Subst) (code : Code) (items : List Atom) (initial : Atom)
    (world : Effects.State) : Set Atom :=
  {answer | FoldSource.Evaluates program (code.callback caller) world items initial answer}

def boundary (program : Program) (caller : Subst) (code : Code) (items : List Atom) (initial : Atom) :
    Boundary Effects.State (Set Atom) (Set Atom) where
  source := sourceMeaning program caller code items initial
  summarize := id
  future := {Question := Set Atom → Bool, Answer _ := Bool, read question answers := question answers}
  sufficient _ _ same question := congrArg question same

theorem source_singleton {program : Program} {caller : Subst} {code : Code} {items : List Atom} {initial : Atom}
    (driver : FoldRegionEntry.Driver program caller code items initial) (world : Effects.State) :
    sourceMeaning program caller code items initial world = {driver.result} := by
  ext answer
  constructor
  · intro source
    exact FoldSource.evaluates_unique source (driver.returns world)
  · rintro rfl
    exact driver.returns world

def region {program : Program} {caller : Subst} {code : Code} {items : List Atom} {initial : Atom}
    (driver : FoldRegionEntry.Driver program caller code items initial) (regime : Regime) :
    CertifiedRegion (boundary program caller code items initial) Regime where
  regime := regime
  Artifact := Atom
  attempt _ := .committed driver.result
  decode answer := {answer}
  restores _ _ impossible := by cases impossible
  exact world _ committed := by
    cases committed
    exact (source_singleton driver world).symm

def drivers (budget : Nat) (program : Program) (caller : Subst) (code : Code)
    (items : List Atom) (initial : Atom) :
    List (Nat × Regime × FoldRegionEntry.Driver program caller code items initial) :=
  let plans := [(Regime.ordered, ordered budget program caller code items initial),
    (.additive, additive budget program caller code items initial),
    (.minimum, extremum .minimum program caller code items initial),
    (.maximum, extremum .maximum program caller code items initial)]
  plans.zipIdx.filterMap fun (entry, ordinal) => entry.2.map fun driver =>
    (ordinal, entry.1, driver)

def gather (budget : Nat) (program : Program) (caller : Subst) (code : Code)
    (items : List Atom) (initial : Atom) (estimate : Regime → Effects.State → Estimate) :
    List (Candidate (boundary program caller code items initial) Regime) :=
  (drivers budget program caller code items initial).map fun (ordinal, regime, driver) =>
    ⟨region driver regime, estimate regime, ordinal⟩

theorem estimates_cannot_change_source_meaning (budget : Nat) (program : Program) (caller : Subst) (code : Code)
    (items : List Atom) (initial : Atom) (estimate : Regime → Effects.State → Estimate) (world : Effects.State) :
    RegionPortfolio.execute world (gather budget program caller code items initial estimate) =
      sourceMeaning program caller code items initial world := RegionPortfolio.execute_exact _ _

theorem all_candidates_agree {program : Program} {caller : Subst} {code : Code} {items : List Atom} {initial : Atom}
    (first second : FoldRegionEntry.Driver program caller code items initial) (world : Effects.State) :
    first.result = second.result := FoldSource.evaluates_unique (first.returns world) (second.returns world)

namespace Controls

def program : Program := {equations := [], declarations := []}
def minCode : Code := .inline (.var "input") (.var "seed") "a" "x" ExtremumFoldSource.Controls.minimumBody
def sumCode : Code := .inline (.var "input") (.var "seed") "a" "x" (apply "+" [.var "a", .var "x"])

theorem ordered_and_minimum_are_both_collected :
    (gather 4 program [] minCode ([-3, 7, -8].map integer) (integer 0) (fun _ _ => ⟨1, 1⟩)).map
      (fun candidate => candidate.region.regime) = [.ordered, .minimum] := by decide +kernel

theorem ordered_and_additive_are_both_collected :
    (gather 4 program [] sumCode ([1, 2, 3].map integer) (integer 0) (fun _ _ => ⟨1, 1⟩)).map
      (fun candidate => candidate.region.regime) = [.ordered, .additive] := by decide +kernel

theorem a_boolean_cannot_enter_the_integer_extremum :
    (extremum .minimum program [] minCode [Effects.boolean true] (integer 0)).isNone = true := by decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldAlgebraPortfolio
