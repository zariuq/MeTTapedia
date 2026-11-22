import Mettapedia.Logic.LinearLogic.KnowledgeTensorFrameGrades
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Rearrangements

/-!
# The grade of an interchange cell, for checks that read the frame

A checked system's firings ask a check of the residual frame: absence and counting are such
checks. Its interchange cells are taken with the semantic admissibility: a swap is allowed where
the two firings run in both orders to one state (`SemanticCell`). A cell made at a state is
**placed** beside more atoms (`beside`) exactly where each of its swaps still runs in both orders
there (`Rearrangement.Survives`); this set of frames is the cell's grade.

* `fires_beside_of_blind`, `square_beside_of_blind`: where the checks are blind to the frame, a
  firing and a square are placed beside any atoms.
* `SemanticCell.beside`, `events_beside`: **blind checks interchange at every frame**: every cell is
  placed beside any atoms, with the same event map.
* `checked_blind`: the guards of a two-zone system, read as checks, are blind. So the cells of every
  two-zone system have the full grade.

The controls file shows that counting and absence do not: a counting cell is not placed beside one
more counted atom although one of its two runs still runs there, and an absence check has two runs
of the same uses, in two orders, joined by no cell.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns

open Mettapedia.Logic.LinearLogic.KnowledgeTensor

universe uK uAtom uRule

variable {K : Type uK} {Atom : Type uAtom} {Rule : Type uRule} [SemilatticeInf K]

/-- One firing of a checked system, between states of knowledge and atoms. -/
def checkedFires (csys : CheckedSystem K Atom Rule) (s : K × Multiset Atom) (declaration : Rule)
    (t : K × Multiset Atom) : Prop :=
  csys.Fires declaration s.1 s.2 t.1 t.2

/-- The interchange cells of a checked system, with the semantic admissibility. -/
abbrev SemanticCell (csys : CheckedSystem K Atom Rule) :=
  Rearrangement (checkedFires csys) (Square (checkedFires csys))

/-- Beside more atoms. -/
def beside (extra : Multiset Atom) (s : K × Multiset Atom) : K × Multiset Atom :=
  (s.1, s.2 + extra)

variable {csys : CheckedSystem K Atom Rule}

theorem checkedFires_deterministic : Deterministic (checkedFires csys) := by
  intro s t t' a one two
  obtain ⟨same, same'⟩ := CheckedSystem.Fires.deterministic one two
  exact Prod.ext same same'

/-- The checks of a system are **blind** when they do not read the frame. -/
def Blind (csys : CheckedSystem K Atom Rule) : Prop :=
  ∀ (declaration : Rule) (k : K) (frame frame' : Multiset Atom),
    csys.check declaration k frame ↔ csys.check declaration k frame'

/-- Where the checks are blind, a firing is placed beside any atoms. -/
theorem fires_beside_of_blind (blind : Blind csys) (extra : Multiset Atom) {s t : K × Multiset Atom}
    {a : Rule} (step : checkedFires csys s a t) : checkedFires csys (beside extra s) a (beside extra t) := by
  obtain ⟨frame, source, checked, told, target⟩ := step
  refine ⟨frame + extra, ?_, (blind a _ frame (frame + extra)).mp checked, told, ?_⟩
  · show s.2 + extra = _
    rw [source, add_assoc]
  · show t.2 + extra = _
    rw [target, add_assoc]

theorem runs_beside_of_blind (blind : Blind csys) (extra : Multiset Atom) {s t : K × Multiset Atom}
    {w : List Rule} (run : Runs (checkedFires csys) s w t) :
    Runs (checkedFires csys) (beside extra s) w (beside extra t) := by
  induction run with
  | nil s => exact Runs.nil _
  | cons step _ ih => exact Runs.cons (fires_beside_of_blind blind extra step) ih

/-- Where the checks are blind, a square is placed beside any atoms. -/
theorem square_beside_of_blind (blind : Blind csys) (extra : Multiset Atom) {s : K × Multiset Atom}
    {a b : Rule} (square : Square (checkedFires csys) s a b) :
    Square (checkedFires csys) (beside extra s) a b := by
  obtain ⟨t, one, two⟩ := square
  exact ⟨beside extra t, runs_beside_of_blind blind extra one, runs_beside_of_blind blind extra two⟩

/-- **Blind checks interchange at every frame**: every cell is placed beside any atoms. -/
def SemanticCell.beside (blind : Blind csys) (extra : Multiset Atom) {s : K × Multiset Atom}
    {w w' : List Rule} (cell : SemanticCell csys s w w') :
    SemanticCell csys (ProofRelevantRuns.beside extra s) w w' :=
  cell.mapAlong (ProofRelevantRuns.beside extra) (fires_beside_of_blind blind extra)
    (Rearrangement.survives_of_keeps _ (square_beside_of_blind blind extra) cell)

/-- **A placed cell moves every event as the cell does.** -/
theorem events_beside (blind : Blind csys) (extra : Multiset Atom) {s : K × Multiset Atom}
    {w w' : List Rule} (cell : SemanticCell csys s w w') :
    (SemanticCell.beside blind extra cell).events = cell.events :=
  Rearrangement.events_mapAlong _ _ cell _

/-- **The guards of a two-zone system, read as checks, are blind.** -/
theorem checked_blind (sys : System K Atom Rule) : Blind sys.checked :=
  fun _ _ _ _ => Iff.rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns
