import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.IssuedNames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.FirstOrderNames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.StructuralCodes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.IssuedNamesControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.IssuedNamesRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.CodeOnlyLoading
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.MicromathSoundness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.ScopeReservations

/-!
# Names on the step

Two sorts of name, kept apart by construction.

* **Generative names** are issued by the firing that makes them (`IssuedNames`). Over any step with a
  local naming, the ledger step admits a firing when the base step does and the firing's issued names
  are new and its written names were issued. Every admitted firing preserves the invariant that every
  name in the store and the knowledge was issued; every name issued along a run is new to the store,
  the knowledge and every earlier issue; no firing writes a name before it is issued. The first-order
  step has a local naming for every action (`FirstOrderNames`). Both halves of the discipline are
  necessary, and it is not stricter than necessary (`IssuedNamesControls`, `IssuedNamesRuns`).
  Opening stored schemas reserves activation scopes that meet the freshness half of that discipline
  (`ScopeReservations`); the use check, a ledger step and the invariant are not proved for scopes.
* **Structural codes** are computed from terms (`StructuralCodes`): quote is injective, unquote
  inverts it on codes, a code mentions exactly its term's names, and unquoting forges none. Comparing
  modulo an equivalence of terms keeps codes and generative names apart by the definition of that
  comparison, a design choice rather than a derived property.
* **Loading** a theory whose rules mention only codes needs no issuing at any ledger and forges no
  name (`CodeOnlyLoading`), with Micromath's rule set as data. Micromath on the step is sound: every
  run keeps every model of its start, reinterpreting only the names it issues, and freshness is
  necessary for that (`MicromathSoundness`).
-/
