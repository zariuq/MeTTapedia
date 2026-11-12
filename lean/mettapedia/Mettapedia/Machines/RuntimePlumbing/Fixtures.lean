import Mettapedia.Machines.RuntimePlumbing.ContextualReuse
import Mettapedia.Machines.RuntimePlumbing.DeclarationDependencies
import Mettapedia.Machines.RuntimePlumbing.RegionalCandidates
import Mettapedia.Machines.RuntimePlumbing.ViewCoordinates
import Mettapedia.Machines.RuntimePlumbing.ProgressTransfer
import Mettapedia.Machines.ReadCertifiedQueryReuse
import Mettapedia.Machines.Cursor.ReaderResidualIndexControls

/-!
# Model-computed runtime adapter controls

These rows are observations of executable Lean models, not native execution
results. A native test translates the corresponding schedule through its real
API, normalizes only representations named by the contract, and compares the
result. Negative rows are outputs of the deliberately wrong alternatives.
Occurrence IDs are retained even when payloads coincide.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RuntimePlumbing.Fixtures

open ReadOnlyQuery

def observations : List (String × String) :=
  let absent := DependencyStamps.Controls.empty
  let question := DependencyStamps.Controls.lookup
  let declared := DeclarationDependencies.Controls.initial
  let typeQuestion := DeclarationDependencies.Controls.answers
  let rows := RegionalCandidates.Controls.rows
  let route := RegionalCandidates.Controls.route
  let matchRow := RegionalCandidates.Controls.matchRow
  let cursor := ViewCoordinates.Controls.frontier
  let before := ViewCoordinates.Controls.old
  let after := ViewCoordinates.Controls.compacted
  let move := ViewCoordinates.Controls.move
  let resumed := ProgressTransfer.Controls.resumed
  let replayed := ProgressTransfer.Controls.restarted
  let service := ProgressTransfer.Controls.sample
  [ ("D01-unrelated-absence-stamp", reprStr <|
      DependencyStamps.check absent (DependencyStamps.write absent 8 (some 17))
        (run absent.value question).reads),
    ("D02-missing-declaration-now-present", reprStr <|
      (run (DependencyStamps.write absent 3 (some 17)).value question).answer),
    ("D03-rollback-rebind", reprStr <|
      (run DependencyStamps.Controls.rebound.value question).answer),
    ("D04-unrelated-subject-cache-hit", reprStr <|
      DependencyStamps.check declared (DependencyStamps.write declared (.subject 2) [99])
        (run declared.value typeQuestion).reads),
    ("D05-general-subject-change", reprStr <|
      (run (DependencyStamps.write declared .generalSubjects [20]).value typeQuestion).answer),
    ("D06-subtype-change", reprStr <|
      (run (DependencyStamps.write declared .subtypes [30]).value typeQuestion).answer),
    ("B01-contextual-root-remains-live", reprStr <|
      DependencyStamps.check ContextualReuse.Controls.before ContextualReuse.Controls.after
        (run ContextualReuse.Controls.before.value (CellRootObservation.query 3 (.var 0))).reads),
    ("I01-general-and-duplicate-occurrences", reprStr <|
      (RegionalCandidates.candidates (RegionalCandidates.build route rows) 1).filterMap (matchRow 1)),
    ("I02-negative-exact-bucket-only", reprStr <|
      ((RegionalCandidates.build route rows).named 1).filterMap (matchRow 1)),
    ("R01-relocated-residual", reprStr <|
      (ViewCoordinates.remaining after (ViewCoordinates.relocate move cursor)).map
        (fun answer => (answer.1.serial, answer.2))),
    ("R02-negative-unmoved-coordinates", reprStr <|
      (ViewCoordinates.remaining after cursor).map (fun answer => (answer.1.serial, answer.2))),
    ("R03-negative-rewound-entry", reprStr <|
      (ViewCoordinates.remaining before (⟨1, 5, .row 0⟩ :: cursor)).map
        (fun answer => (answer.1.serial, answer.2))),
    ("R04-stamped-rebuild-after-write", reprStr <|
      Cursor.ReaderResidualIndex.bitResidual Cursor.ReaderResidualIndex.Controls.written
        Cursor.ReaderResidualIndex.Controls.rebuilt Cursor.ReaderResidualIndex.Controls.advanced 0 1),
    ("R05-unloaded-keeps-position", reprStr <|
      Cursor.ReaderLoadedSnapshot.step (Cursor.ReaderLoadedSnapshot.unloaded :
        Cursor.ReaderLoadedSnapshot.Cache Nat) ViewCoordinates.Controls.slotReader),
    ("R06-loaded-next-slot", reprStr <|
      Cursor.ReaderLoadedSnapshot.step
        (Cursor.ReaderLoadedSnapshot.load ViewCoordinates.Controls.slotStore
          Cursor.ReaderLoadedSnapshot.unloaded 0) ViewCoordinates.Controls.slotReader),
    ("P01-paused-with-output-no-store-write", reprStr <|
      (Cursor.ReadOnlyQuery.Sampled.savedState service ProgressTransfer.Controls.cut.2).1),
    ("P02-exact-resume-world", reprStr <|
      (Cursor.ReadOnlyQuery.Sampled.savedState service resumed.2).1),
    ("P03-negative-replayed-world", reprStr <|
      (Cursor.ReadOnlyQuery.Sampled.savedState service replayed.2).1),
    ("P04-resumed-paid-work", reprStr resumed.1),
    ("P05-switched-provider-world", reprStr <|
      (Cursor.ReadOnlyQuery.Sampled.savedState service ProgressTransfer.Controls.switched.2).1) ]

def emit : IO Unit := do
  IO.println "case\tmodel_observation"
  for (name, observation) in observations do
    IO.println (name ++ "\t" ++ observation.replace "\n" " ")

end Mettapedia.Machines.RuntimePlumbing.Fixtures

def main : IO Unit := Mettapedia.Machines.RuntimePlumbing.Fixtures.emit
