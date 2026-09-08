import Mettapedia.GSLT.Parsing.CanonicalSourceHornElaboration
import Mettapedia.GSLT.Parsing.HornCertificateGSLT

/-!
# Authored source compositions as operational Horn GSLTs

This module is the narrow bridge from the exact `gslt-presentation-v1`
source schema to an operational semantic object.  A closed source composition
must first elaborate, with exact re-quotation, into the established ordered
Horn program.  Only then is the program equipped with the leftmost-obligation
GSLT whose terminal paths are equivalent to bounded Horn derivability and
certificate replay.

This construction does not reinterpret source `equations` as directed rules.
Nor does it claim that a `metta-equation` Horn fact already realizes the
downstream evaluator equation emitted by a target compiler; that projection
requires its own operational correspondence theorem.

In particular, this is clause-only execution: an
`oslf-external-relation-decl-v1` fact does not answer queries to the declared
relation. The authored PeTTa providers require target-equation evaluation,
which this Horn GSLT does not supply. `HornCertificateBoundary` checks this
limitation on source rows and rules out finite proofs of unseeded relations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.CanonicalSourceOperationalGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
open Mettapedia.GSLT.Parsing.HornCertificate
open Mettapedia.GSLT.Parsing.CanonicalSourceHornElaboration
open Mettapedia.GSLT.Parsing.HornCertificateGSLT

/-- The operational theory exists exactly when the authored source composition
is admitted by the exact first-order Horn elaborator. -/
def elaborateTheory? (sources : List Source) : Option GSLT :=
  match elaborateProgram? sources with
  | none => none
  | some program => some (theory program)

theorem elaborateTheory?_of_program {sources : List Source}
    {program : Program}
    (accepted : elaborateProgram? sources = some program) :
    elaborateTheory? sources = some (theory program) := by
  simp [elaborateTheory?, accepted]

/-- Once a source composition elaborates, its bounded Horn certificate
successes are exactly the terminal executions of the clause-only GSLT. This
does not assert execution of declared external relations or target equations. -/
theorem source_program_operational_correspondence {sources : List Source}
    {program : Program}
    (accepted : elaborateProgram? sources = some program)
    (fuel : Nat) (goal : GroundAtom) :
    elaborateTheory? sources = some (theory program) ∧
      ((∃ certificate, replay program fuel goal certificate = true) ↔
        (theory program).MultiStep [(fuel, goal)] []) := by
  exact ⟨elaborateTheory?_of_program accepted,
    replay_iff_terminal_path program fuel goal⟩

/-- Negative control: an unelaborable source composition receives no semantic
Horn GSLT by this bridge. -/
theorem no_theory_without_program {sources : List Source}
    (refused : elaborateProgram? sources = none) :
    elaborateTheory? sources = none := by
  simp [elaborateTheory?, refused]

#print axioms elaborateTheory?_of_program
#print axioms source_program_operational_correspondence
#print axioms no_theory_without_program

end Mettapedia.GSLT.Parsing.CanonicalSourceOperationalGSLT
