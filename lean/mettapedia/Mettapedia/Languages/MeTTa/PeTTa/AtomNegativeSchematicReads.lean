import Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeFreshNamespaces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericProtocol

/-!
# Constructed schematic-read openings with retained disequations

Rows have their own local positive knowledge and parameters. Their local
negative frame is empty; the caller's negative frame is retained. The two
openings of the existing direct-read firing are realized independently by a
constructed morphism that preserves all caller coordinates and disequations.
Admission and execution are separate from this freshness theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeSchematicReads

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open RuleSyntax SchematicRows HeldReadGenericSources
open AtomNegativeFreshNamespaces (Frame Hom X)

abbrev Terms : Frame → Type := fun _ => Atom
abbrev E : Extensions.{0, 0, 0} Hom := Extensions.identity X

def emptyFrame : Frame := ⟨[], Disequality.separates_nil atomAction.identity⟩

structure RowData where
  knowledge : EquationStore Atom
  parameters : List Atom
  value : Atom

def RowData.schema (row : RowData) : Schema Terms :=
  ⟨emptyFrame, row.knowledge, row.parameters, row.value⟩

def RowData.close (row : RowData) (ambient : Frame) (arguments : List Atom) : Closure Terms ambient :=
  ⟨row.schema, arguments⟩

def opening (ambient : Frame) (bound index : Nat) : Hom emptyFrame ambient :=
  ⟨AtomFreshNamespaces.opening bound index, by intro _ _ _ absent; cases absent⟩

variable {O R : Type*} (ordinary : RuleSyntax.State Terms O) (rows : Finset R)
  (data : R → RowData) (arguments : R → List Atom)

def closures : R → Closure Terms ordinary.frame := fun row => (data row).close ordinary.frame (arguments row)

noncomputable def callerTerms : List Atom :=
  let source := (mixed ordinary rows (closures ordinary data arguments)).scope
  AtomFreshNamespaces.sourceTerms source.knowledge source.present source.label

noncomputable def bound : Nat := AtomNegativeFreshNamespaces.bound ordinary.frame
  (callerTerms ordinary rows data arguments)

noncomputable def direct (selected : R) (output : O) :=
  HeldReadGenericFirings.direct ordinary rows (closures ordinary data arguments) (E := E)
    selected PUnit.unit (opening ordinary.frame (bound ordinary rows data arguments) 0)
    (opening ordinary.frame (bound ordinary rows data arguments) 1) output

theorem direct_fresh (selected : R) (output : O) :
    (direct ordinary rows data arguments selected output).Fresh X := by
  intro target caller first second
  change Hom ordinary.frame target at caller
  change Hom emptyFrame target at first second
  let protectedTerms := callerTerms ordinary rows data arguments
  let requested := fun index => if index = 0 then first.1 else second.1
  let assignment := AtomNegativeFreshNamespaces.combine protectedTerms caller requested
  refine ⟨assignment, ⟨?_, ?_⟩, ?_⟩
  · intro term mentioned
    have member : term ∈ protectedTerms :=
      AtomFreshNamespaces.mentioned_in_source mentioned
    have kept := AtomNegativeFreshNamespaces.combine_protected protectedTerms caller requested term member
    change subst assignment.1 (subst Mettapedia.Languages.MeTTa.SubstitutionAlgebra.empty term) =
      subst caller.1 term
    rw [Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_empty]
    exact kept
  · intro term _
    change subst assignment.1
      (subst (AtomFreshNamespaces.opening (bound ordinary rows data arguments) 0) term) = subst first.1 term
    exact AtomFreshNamespaces.combine_opening (bound ordinary rows data arguments) caller.1 requested 0 term
  · intro term _
    change subst assignment.1
      (subst (AtomFreshNamespaces.opening (bound ordinary rows data arguments) 1) term) = subst second.1 term
    exact AtomFreshNamespaces.combine_opening (bound ordinary rows data arguments) caller.1 requested 1 term

variable [DecidableEq O] [DecidableEq R]

noncomputable def materialize (selected : R) (temporary : O) :=
  HeldReadGenericFirings.datum ordinary rows (closures ordinary data arguments) (E := E)
    selected PUnit.unit (opening ordinary.frame (bound ordinary rows data arguments) 1) temporary

noncomputable def consume (selected : R) (temporary output : O) :=
  HeldReadGenericFirings.consumer ordinary rows (closures ordinary data arguments) (E := E)
    selected PUnit.unit (opening ordinary.frame (bound ordinary rows data arguments) 0)
    (opening ordinary.frame (bound ordinary rows data arguments) 1) X temporary output

theorem stages_fresh (selected : R) (temporary output : O)
    (ambient : Set (HeldReadEncoding.Code Terms)) (present : selected ∈ rows) :
    (materialize ordinary rows data arguments selected temporary).Fresh X ∧
      (consume ordinary rows data arguments selected temporary output).Fresh X :=
  HeldReadGenericFirings.staged_fresh_of_direct (E := E) X ordinary rows
    (closures ordinary data arguments) selected PUnit.unit
    (opening ordinary.frame (bound ordinary rows data arguments) 0)
    (opening ordinary.frame (bound ordinary rows data arguments) 1)
    temporary output ambient present (direct_fresh ordinary rows data arguments selected output)

/-- Capture arity, physical availability, fresh output identities and
solvable matching information construct the two actual protocol events.
The negative frame is retained throughout; no admitted run is assumed. -/
theorem execution_of_solvable (selected : R) (temporary output : O)
    (ambient : Set (HeldReadEncoding.Code Terms))
    (available : Sum.inr (HeldReadGenericFirings.consumeRule
      ((closures ordinary data arguments) selected).schema) ∈ ambient)
    (wellFormed : ((closures ordinary data arguments) selected).WellFormed)
    (present : selected ∈ rows) (outputFresh : output ∉ ordinary.present)
    (temporaryFresh : temporary ∉ ordinary.present) (different : temporary ≠ output)
    (solvable : X.Solvable (a := ordinary.frame)
      ((direct ordinary rows data arguments selected output).information X)) :
    ∃ run : (HeldReadGenericFirings.protocolMachine (E := E) (O := O) (R := R) X ambient).Run
        (hosted ordinary rows (closures ordinary data arguments)),
      run.word.length = 2 ∧
      run.last = (consume ordinary rows data arguments selected temporary output).result X ∧
      run.last.present = ordinary.present ∪ {output} ∧ run.last.rules = rows ∧
        temporary ∉ run.last.present := by
  apply HeldReadGenericFirings.execution_of_direct (E := E) X ordinary rows
    (closures ordinary data arguments) selected PUnit.unit
    (opening ordinary.frame (bound ordinary rows data arguments) 0)
    (opening ordinary.frame (bound ordinary rows data arguments) 1)
    temporary output ambient available temporaryFresh different
  refine ⟨HeldReadGenericFirings.direct_shapes (E := E) X ordinary rows
      (closures ordinary data arguments) selected PUnit.unit
      (opening ordinary.frame (bound ordinary rows data arguments) 0)
      (opening ordinary.frame (bound ordinary rows data arguments) 1)
      output (direct_fresh ordinary rows data arguments selected output) wellFormed,
    HeldReadGenericFirings.direct_enabled (E := E) ordinary rows
      (closures ordinary data arguments) selected PUnit.unit
      (opening ordinary.frame (bound ordinary rows data arguments) 0)
      (opening ordinary.frame (bound ordinary rows data arguments) 1) output present outputFresh,
    solvable, ?_⟩
  intro target assignment _
  exact HeldReadGenericFirings.direct_holds (E := E) X ordinary rows
    (closures ordinary data arguments) selected PUnit.unit
    (opening ordinary.frame (bound ordinary rows data arguments) 0)
    (opening ordinary.frame (bound ordinary rows data arguments) 1) output assignment

end Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeSchematicReads
