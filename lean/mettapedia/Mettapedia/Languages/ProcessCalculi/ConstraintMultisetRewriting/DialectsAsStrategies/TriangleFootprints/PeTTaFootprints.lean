import Mettapedia.Languages.MeTTa.PeTTa.RunsPredicateQueries
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingRename

/-!
# PeTTa's request word with the region it enumerated

`PeTTa.RunsAsFirings` records, for a call of an authored function, a read of the equation rows the
call selects (`askEquations`, through `scanCall`), and nothing about the rows it left. PeTTa
enumerates every clause of the called predicate, so its answer depends on the absence of other
matching equations as much as on the rows it used. Here the request carries that completeness.

* `pettaCallRegion`: the region of a call of `head` with the values `values`, as a predicate of a
  row's atom: an equation of `head` with as many arguments, whose argument patterns match the
  values.
* `scanCall_ground`: on the first-order fragment (ground values, a substitution with ground values
  that binds no name of the uses), **the rows a call's scan selects are exactly the rows of its
  region, in store order**. The machine renames each equation apart for its own use; matching a
  renamed pattern is matching the pattern, renamed (`Unifying.matchValues_rename`), so the selection
  does not depend on the use.
* `completeCall`: the request of a call with its predicate query: the region's rows of the program's
  own space, read, and the observation that they are all of them.
* `ground_call_query`: on that fragment the complete request reads exactly what the machine's scan
  selects, and the ordered-store step, told each occurrence with its space, admits it: its admission
  checks the observation.

## Controls

* `Controls.double_request_complete`: for `(double 4)` against `{(p a), (= (double $x) (+ $x $x))}`
  (the program of `RunsAsFirings.Controls`), the machine's request reads the equation's row, and the
  complete request reads the same row with the observation of its region.
* `Controls.double_region`: the equation is inside the region of `(double 4)`; `(p a)`, a `triple`
  equation and the equation `(= (double 5) 10)` are outside.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open Mettapedia.Languages.MeTTa.ContextualTransform
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings
open PeTTaStoreSelection (atomFrames)
open NamedSpaces (Handle)

/-! ## The region of a call -/

/-- **The region of a call** of `head` with the values `values`: the rows that are equations of
`head` with as many arguments as there are values, whose argument patterns match the values. -/
def pettaCallRegion (head : String) (values : List Atom) (atom : Atom) : Bool :=
  match LiveEquations.equationOfRow atom with
  | some equation =>
      (equation.head == head && equation.arguments.length == values.length) &&
        (SpaceSemantics.matchValue.matchValues [] equation.arguments values).isSome
  | none => false

/-- A row that is not an equation is outside every call's region. -/
theorem pettaCallRegion_not_equation {head : String} {values : List Atom} {atom : Atom}
    (notEquation : LiveEquations.equationOfRow atom = none) : pettaCallRegion head values atom = false := by
  simp [pettaCallRegion, notEquation]

/-- **On ground values, a call's scan selects exactly the rows of its region**, in store order. -/
theorem scanCall_ground {O : Type} (label : O → Atom) {bindings : Subst} {head : String}
    {values : List Atom} (range : Unifying.GroundRange bindings)
    (ground : ∀ value ∈ values, isGroundAtom value = true) :
    ∀ (use : Nat) (rows : List O), (∀ step, Unifying.FreshFor (use + step) bindings) →
      ∃ packets, scanCall label bindings head values use rows = some packets ∧
        packets.map Prod.fst = rows.filter fun row => pettaCallRegion head values (label row)
  | _, [], _ => ⟨[], rfl, rfl⟩
  | use, row :: rest, fresh => by
      cases equation : LiveEquations.equationOfRow (label row) with
      | none =>
          obtain ⟨packets, scanned, read⟩ :=
            scanCall_ground (head := head) label range ground use rest fresh
          refine ⟨packets, ?_, ?_⟩
          · simp [scanCall, equation, scanned]
          · simp [pettaCallRegion, equation, read]
      | some found =>
          by_cases candidate :
              (found.head == head && found.arguments.length == values.length) = true
          · have restFresh : ∀ step, Unifying.FreshFor (use + 1 + step) bindings := by
              intro step
              have := fresh (1 + step)
              rwa [← Nat.add_assoc] at this
            obtain ⟨later, scanned, read⟩ :=
              scanCall_ground (head := head) label range ground (use + 1) rest restFresh
            have renamed := Unifying.matchValues_rename (use := use) (outer := bindings)
              (by simpa using fresh 0) found.arguments values []
            rw [Unifying.renameKeys_nil, List.nil_append] at renamed
            have unified : Unifying.unifyArguments bindings
                (found.arguments.map (Unifying.rename use)) values =
                  Unifying.ofMatch ((SpaceSemantics.matchValue.matchValues [] found.arguments
                    values).map fun bound => Unifying.renameKeys use bound ++ bindings) := by
              rw [Unifying.arguments_ground range ground, renamed]
            cases matched : SpaceSemantics.matchValue.matchValues [] found.arguments values with
            | none =>
                refine ⟨later, ?_, ?_⟩
                · simp [scanCall, equation, candidate, scanned, unified, matched, Unifying.ofMatch]
                · simp [pettaCallRegion, equation, candidate, matched, read]
            | some bound =>
                refine ⟨(row, .evaluate (Unifying.renameKeys use bound ++ bindings)
                  (Unifying.rename use found.body)) :: later, ?_, ?_⟩
                · simp [scanCall, equation, candidate, scanned, unified, matched, Unifying.ofMatch]
                · simp [pettaCallRegion, equation, candidate, matched, read]
          · obtain ⟨packets, scanned, read⟩ :=
              scanCall_ground (head := head) label range ground use rest fresh
            have refused :
                (found.head == head && found.arguments.length == values.length) = false := by
              simpa using candidate
            refine ⟨packets, ?_, ?_⟩
            · simp only [scanCall, equation, refused, Bool.false_eq_true, if_false]
              exact scanned
            · simp [pettaCallRegion, equation, refused, read]

variable {O : Type} [DecidableEq O]

/-- **The complete request of a call**: the rows of the call's region in the program's own space,
read, with the observation that they are all of them. -/
abbrev completeCall (S : Supply O) (head : String) (values : List Atom) (ids : List O) :
    OrderedStore.Publication Atom O :=
  readWithQuery S (selectAt .self (pettaCallRegion head values)) ids

variable {S : Supply O}

/-- **On ground values a call reads with its predicate query.** The occurrences the machine's scan
selects are exactly those the complete request reads, and the ordered-store step, told each
occurrence with its space, admits the complete request: its admission checks the observation. -/
theorem ground_call_query {ids : List O} {state : Effects.State} (tracks : Tracks S ids state)
    {bindings : Subst} (head : String) (values : List Atom) (use : Nat)
    (range : Unifying.GroundRange bindings) (ground : ∀ value ∈ values, isGroundAtom value = true)
    (fresh : ∀ step, Unifying.FreshFor (use + step) bindings)
    (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    ∃ packets, scanCall S.label bindings head values use (S.rowsAt .self ids) = some packets ∧
      (completeCall S head values ids).selection.read = packets.map Prod.fst ∧
      (completeCall S head values ids).selection.taken = [] ∧
      (completeCall S head values ids).selection.made = [] ∧
      (OrderedStore.step atomFrames PUnit.unit S.located).Admits (s := (knowledge, ids))
        (completeCall S head values ids) := by
  obtain ⟨packets, scanned, read⟩ :=
    scanCall_ground S.label range ground use (S.rowsAt .self ids) fresh
  refine ⟨packets, scanned, ?_, rfl, rfl, ?_⟩
  · rw [read]
    exact filter_selectAt S .self _ ids
  · exact (StoreOperations.read_admits_exact atomFrames PUnit.unit S.located _ knowledge
      ids).mpr ⟨tracks.distinct, consistent⟩

/-! ## Controls -/

namespace Controls

open RunsAsFirings.Controls (p a doubling codeStore codeIds callDouble doubleEquation shape)

/-- `(= (double 5) 10)`. -/
def doubleFive : Atom :=
  .expression [.symbol "=", .expression [.symbol "double", .grounded (.int 5)], .grounded (.int 10)]

/-- `(= (triple $x) (+ $x (+ $x $x)))`. -/
def tripleEquation : Atom :=
  .expression [.symbol "=", .expression [.symbol "triple", .var "x"],
    .expression [.symbol "+", .var "x", .expression [.symbol "+", .var "x", .var "x"]]]

/-- **The region of `(double 4)`**: the equation `(= (double $x) (+ $x $x))` is inside; `(p a)`,
the `triple` equation and `(= (double 5) 10)` are outside. -/
theorem double_region :
    pettaCallRegion "double" [.grounded (.int 4)] doubleEquation = true ∧
      pettaCallRegion "double" [.grounded (.int 4)] (p a) = false ∧
      pettaCallRegion "double" [.grounded (.int 4)] tripleEquation = false ∧
      pettaCallRegion "double" [.grounded (.int 4)] doubleFive = false := by
  decide +kernel

/-- **The complete request of `(double 4)`**: the machine's request reads the equation's row, and
the complete request reads that same row, takes and makes nothing, and observes that the region of
`(double 4)` in the own space holds exactly it. -/
theorem double_request_complete :
    (requests rowSupply doubling 30 (Streaming.enter { state := codeStore } callDouble)
        codeIds).map shape = [([], [⟨1, .self, doubleEquation⟩], [])] ∧
      shape (completeCall rowSupply "double" [.grounded (.int 4)] codeIds) =
        ([], [⟨1, .self, doubleEquation⟩], []) ∧
      (completeCall rowSupply "double" [.grounded (.int 4)] codeIds).observations.map
          (fun query => query.seen) = [{⟨1, .self, doubleEquation⟩}] ∧
      (completeCall rowSupply "double" [.grounded (.int 4)] codeIds).observations.map
          (fun query => query.region) = [selectAt .self (pettaCallRegion "double" [.grounded (.int 4)])] := by
  refine ⟨RunsAsFirings.Controls.callDouble_requests.1, ?_, ?_, rfl⟩
  · decide +kernel
  · decide +kernel

end Controls

#print axioms pettaCallRegion_not_equation
#print axioms scanCall_ground
#print axioms ground_call_query
#print axioms Controls.double_region
#print axioms Controls.double_request_complete

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
