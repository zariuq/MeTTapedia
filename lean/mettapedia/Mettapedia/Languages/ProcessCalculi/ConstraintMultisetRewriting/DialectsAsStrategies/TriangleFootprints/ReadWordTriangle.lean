import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.Race
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep.NamedDifferences

/-!
# The read-word triangle with honest footprints

H1's `reads_differ` found that HE on the step read the whole space, `(p a)` included, while PeTTa's
projection read only the equation's row and left out that no other equation matched. With honest
footprints both read the matched rows and observe their region (`HEFootprints`,
`PeTTaFootprints`). This module compares the two read words.

* `completeCall_load`: on a loaded program, the rows PeTTa's complete call request reads, with their
  positions, are the rows of the call's region.
* `read_word_triangle`: **on a loaded program, HE's equation query and PeTTa's complete call read
  the same positioned rows exactly when the two regions agree on the program's rows.** With the
  machines: a firing of HE's call reads its region's rows (`HEFootprints.he_reads_exact`), and on
  ground arguments PeTTa's machine request reads the complete call's rows
  (`PeTTaFootprints.ground_call_query`). Whether the two regions agree on a row is the remaining
  semantic question: HE's equation matching (`MatchRel`, merge, fresh variants) against PeTTa's
  argument matching (`matchValues`).

## Instances

* `Instance.triangle_double`: on `{(p a), (= (double 4) 8)}` the regions agree on both rows, so the
  read words coincide: HE's query of `(double 4)` and PeTTa's complete request both read the one row
  `(= (double 4) 8)` at position `1`, and neither reads `(p a)`. On the tree's machines both answer
  `8`: PeTTa's streaming machine with its request word, and HE's executable evaluator.
* `Instance.h1_program`: on H1's program `{(p a), (= (double $x) (+ $x $x))}`, neither dialect's
  footprint contains `(p a)`, and PeTTa's complete request reads the equation's row.
* `Instance.region_disagreement`: a negative control for the criterion: a row `(= ($h 4) 8)` with a
  variable head is outside PeTTa's call region (no clause of `double`), so the read words on a
  program holding it coincide only if HE's region also leaves it out.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings

/-! ## Positioned rows on both sides -/

section Coincidence

/-- Two regions select the same positioned rows of a list exactly when they agree on its rows. -/
theorem regionRows_eq_iff {X : Type} (ρ σ : X → Bool) (rows : List X) :
    regionRows ρ rows = regionRows σ rows ↔ ∀ x ∈ rows, ρ x = σ x := by
  constructor
  · intro same x member
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp member
    have inZip : (x, i) ∈ rows.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr hi
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro inside
      have here : (x, i) ∈ regionRows ρ rows := List.mem_filter.mpr ⟨inZip, inside⟩
      rw [same] at here
      exact (List.mem_filter.mp here).2
    · intro inside
      have here : (x, i) ∈ regionRows σ rows := List.mem_filter.mpr ⟨inZip, inside⟩
      rw [← same] at here
      exact (List.mem_filter.mp here).2
  · intro agree
    unfold regionRows
    apply List.filter_congr
    intro q member
    exact agree q.1 (List.fst_mem_of_mem_zipIdx member)

/-- Rows loaded in order, filtered by their atoms, as positioned rows. -/
theorem load_filter (p : Atom → Bool) : ∀ (serial : ℕ) (atoms : List Atom),
    ((Row.load serial atoms).filter fun row => p row.atom).map (fun row => (row.atom, row.serial)) =
      (atoms.zipIdx serial).filter fun q => p q.1
  | _, [] => rfl
  | serial, atom :: rest => by
      by_cases inside : p atom = true
      · simp [Row.load, inside, load_filter p (serial + 1) rest]
      · simp [Row.load, inside, load_filter p (serial + 1) rest]

theorem rowsAt_load (atoms : List Atom) :
    rowSupply.rowsAt .self (Row.load 0 atoms) = Row.load 0 atoms := by
  apply List.filter_eq_self.mpr
  intro row member
  exact decide_eq_true (Row.load_serial 0 atoms row member).2

/-- **On a loaded program, PeTTa's complete call request reads the rows of the call's region**,
with their positions. -/
theorem completeCall_load (head : String) (values : List Atom) (atoms : List Atom) :
    (completeCall rowSupply head values (Row.load 0 atoms)).selection.read.map
        (fun row => (row.atom, row.serial)) =
      regionRows (pettaCallRegion head values) atoms := by
  change ((Row.load 0 atoms).filter fun row =>
      selectAt .self (pettaCallRegion head values) (rowSupply.located row)).map _ = _
  rw [filter_selectAt rowSupply .self _ (Row.load 0 atoms), rowsAt_load]
  exact load_filter _ 0 atoms

/-- **The read-word triangle on a loaded program.** HE's equation query (region
`eqRegion live query incoming`) and PeTTa's complete request of a call of `head` with `values`
read the same positioned rows exactly when the two regions agree on the program's rows. -/
theorem read_word_triangle (atoms live : List Atom) (query : Atom)
    (incoming : Mettapedia.Languages.MeTTa.HE.Bindings) (head : String) (values : List Atom) :
    regionRows (eqRegion live query incoming) (Space.ofList atoms).atoms =
        (completeCall rowSupply head values (Row.load 0 atoms)).selection.read.map
          (fun row => (row.atom, row.serial)) ↔
      ∀ a ∈ atoms, eqRegion live query incoming a = pettaCallRegion head values a := by
  rw [completeCall_load]
  exact regionRows_eq_iff _ _ atoms

/-- **PeTTa's machine on a loaded program**: on ground values, the rows a call's scan selects are
the rows of the call's region, with their positions. -/
theorem scanCall_load {bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst} {head : String}
    {values : List Atom} (atoms : List Atom) (use : Nat) (range : Unifying.GroundRange bindings)
    (ground : ∀ value ∈ values, Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom value = true)
    (fresh : ∀ step, Unifying.FreshFor (use + step) bindings) :
    ∃ packets, scanCall rowSupply.label bindings head values use
        (rowSupply.rowsAt .self (Row.load 0 atoms)) = some packets ∧
      packets.map (fun packet => (packet.1.atom, packet.1.serial)) =
        regionRows (pettaCallRegion head values) atoms := by
  obtain ⟨packets, scanned, read⟩ := scanCall_ground (head := head) rowSupply.label range ground
    use (rowSupply.rowsAt .self (Row.load 0 atoms)) fresh
  refine ⟨packets, scanned, ?_⟩
  have split : packets.map (fun packet => (packet.1.atom, packet.1.serial)) =
      (packets.map Prod.fst).map (fun row => (row.atom, row.serial)) := by
    simp [List.map_map, Function.comp_def]
  rw [split, read, rowsAt_load]
  exact load_filter _ 0 atoms

/-- **The read-word triangle on the machines.** On a loaded program and ground call values, the
rows PeTTa's scan selects and the rows of HE's equation region, with their positions, coincide
exactly when the two regions agree on the program's rows. A firing of HE's equation query reads
exactly its region's rows (`HEFootprints.he_reads_exact`). -/
theorem machine_read_words (atoms live : List Atom) (query : Atom)
    (incoming : Mettapedia.Languages.MeTTa.HE.Bindings)
    {bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst} {head : String} {values : List Atom}
    (use : Nat) (range : Unifying.GroundRange bindings)
    (ground : ∀ value ∈ values, Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom value = true)
    (fresh : ∀ step, Unifying.FreshFor (use + step) bindings) :
    ∃ packets, scanCall rowSupply.label bindings head values use
        (rowSupply.rowsAt .self (Row.load 0 atoms)) = some packets ∧
      (regionRows (eqRegion live query incoming) (Space.ofList atoms).atoms =
          packets.map (fun packet => (packet.1.atom, packet.1.serial)) ↔
        ∀ a ∈ atoms, eqRegion live query incoming a = pettaCallRegion head values a) := by
  obtain ⟨packets, scanned, read⟩ := scanCall_load (head := head) atoms use range ground fresh
  exact ⟨packets, scanned, by rw [read]; exact regionRows_eq_iff _ _ atoms⟩

end Coincidence

/-! ## Instances -/

namespace Instance

open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (AlphaVariantRel EquationRowResultsRel
  atomOccurs_mem_typeVars)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (MatchRel equalityGroundedSemantic
  semanticLoopFree_empty constraints)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst.typeVars
  TypeSubst.typeVarsList)
open RunsAsFirings.Controls (p a shape)

/-- `(double 4)`. -/
def doubleFour : Atom := .expression [.symbol "double", .grounded (.int 4)]

/-- `8`. -/
def eight : Atom := .grounded (.int 8)

/-- `(= (double 4) 8)`. -/
def doubleEight : Atom := .expression [.symbol "=", doubleFour, eight]

/-- The program `{(p a), (= (double 4) 8)}`. -/
def program : List Atom := [p a, doubleEight]

/-- The same program as PeTTa's registry and store. -/
def registry : SpaceSemantics.Program :=
  { equations := [⟨"double", [.grounded (.int 4)], .grounded (.int 8)⟩], declarations := [] }
def store : Effects.State := NamedSpaces.Store.new program []
def ids : List Row := Row.load 0 program

/-- `(= (double 4) 8)` is its own fresh variant: it has no variables. -/
theorem doubleEight_alpha (live : List Atom) :
    AlphaVariantRel live doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty doubleFour eight
      doubleFour eight := by
  refine ⟨id, Function.injective_id,
    .expression (.cons (.symbol "double") (.cons (.grounded (.int 4)) .nil)),
    .grounded (.int 8), ?_⟩
  intro name occurs
  rcases occurs with left | right
  · have used := atomOccurs_mem_typeVars left
    simp [doubleFour, TypeSubst.typeVars, TypeSubst.typeVarsList] at used
  · cases right

/-- `(double 4)` matches itself with no bindings. -/
theorem doubleFour_matches :
    MatchRel equalityGroundedSemantic doubleFour doubleFour
      Mettapedia.Languages.MeTTa.HE.Bindings.empty :=
  .expression
    (.cons (.symSym "double" semanticLoopFree_empty)
      (.mk (by simp [constraints, Mettapedia.Languages.MeTTa.HE.Bindings.empty]) .nil)
      (.cons (.groundedLeftCustom rfl trivial ⟨rfl, rfl⟩ semanticLoopFree_empty)
        (.mk (by simp [constraints, Mettapedia.Languages.MeTTa.HE.Bindings.empty]) .nil) .nil))
    semanticLoopFree_empty

/-- **`(= (double 4) 8)` is inside the region of HE's query `(double 4)`.** -/
theorem he_inside (live : List Atom) :
    eqRegion live doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty doubleEight = true := by
  apply eqRegion_of_not_inert
  intro inert
  have hit : EquationRowResultsRel live doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty 1
      doubleEight [⟨1, doubleFour, eight, doubleFour, eight,
        Mettapedia.Languages.MeTTa.HE.Bindings.empty⟩] :=
    .hit 1 doubleFour eight doubleFour eight Mettapedia.Languages.MeTTa.HE.Bindings.empty
      Mettapedia.Languages.MeTTa.HE.Bindings.empty (doubleEight_alpha live) doubleFour_matches
      Controls.mergeEmpty
  cases (inert 1 _).mp hit

theorem he_pa_outside (live : List Atom) (query : Atom)
    (incoming : Mettapedia.Languages.MeTTa.HE.Bindings) : eqRegion live query incoming (p a) = false :=
  Controls.pa_outside live query incoming

theorem petta_inside : pettaCallRegion "double" [.grounded (.int 4)] doubleEight = true := by
  decide +kernel

theorem petta_pa_outside : pettaCallRegion "double" [.grounded (.int 4)] (p a) = false := by
  decide +kernel

/-- **The regions agree on the program's rows.** -/
theorem regions_agree (live : List Atom) :
    ∀ x ∈ program, eqRegion live doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty x =
      pettaCallRegion "double" [.grounded (.int 4)] x := by
  intro x member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [he_pa_outside, petta_pa_outside]
  · rw [he_inside, petta_inside]

/-- **The read-word triangle holds on `(double 4)`.** HE's equation query and PeTTa's complete
request read the one row `(= (double 4) 8)` at position `1`; `(p a)` is read by neither. On the
tree's machines PeTTa's evaluation makes exactly that read request and answers `8`, and HE's
executable evaluator answers `8`. -/
theorem triangle_double (live : List Atom) :
    regionRows (eqRegion live doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty)
        (Space.ofList program).atoms = [(doubleEight, 1)] ∧
      (completeCall rowSupply "double" [.grounded (.int 4)] ids).selection.read.map
        (fun row => (row.atom, row.serial)) = [(doubleEight, 1)] ∧
      (requests rowSupply registry 30 (Streaming.enter { state := store } doubleFour) ids).map
        shape = [([], [⟨1, .self, doubleEight⟩], [])] ∧
      Streaming.values (Streaming.advance registry 30
        (Streaming.enter { state := store } doubleFour)) = [eight] ∧
      (Mettapedia.Languages.MeTTa.HE.evalAtom (Space.ofList program)
        HEOnTheStep.NamedDifferences.plus doubleFour Atom.undefinedType
          Mettapedia.Languages.MeTTa.HE.Bindings.empty 40).map Prod.fst = [eight] := by
  have heRows : regionRows (eqRegion live doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty)
      (Space.ofList program).atoms = [(doubleEight, 1)] := by
    simp [regionRows, program, Space.ofList, he_inside, he_pa_outside]
  refine ⟨heRows, ?_, ?_, ?_, ?_⟩
  · have agreement := (read_word_triangle program live doubleFour _ "double"
      [.grounded (.int 4)]).mpr (regions_agree live)
    exact agreement.symm.trans heRows
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- **H1's program revisited**: on `{(p a), (= (double $x) (+ $x $x))}` the row `(p a)` is in neither
footprint of `(double 4)`, and PeTTa's complete request reads the equation's row at position `1`. -/
theorem h1_program (live : List Atom) :
    (p a, 0) ∉ regionRows (eqRegion live RunsAsFirings.Controls.callDouble
        Mettapedia.Languages.MeTTa.HE.Bindings.empty)
      [p a, RunsAsFirings.Controls.doubleEquation] ∧
      (completeCall rowSupply "double" [.grounded (.int 4)] RunsAsFirings.Controls.codeIds).selection.read.map
        (fun row => (row.atom, row.serial)) = [(RunsAsFirings.Controls.doubleEquation, 1)] := by
  refine ⟨fun member => ?_, ?_⟩
  · have := (List.mem_filter.mp member).2
    rw [he_pa_outside] at this
    cases this
  · decide +kernel

/-- `(= ($h 4) 8)`: an equation whose head is a variable. -/
def variableHead : Atom :=
  .expression [.symbol "=", .expression [.var "h", .grounded (.int 4)], .grounded (.int 8)]

/-- **Negative control for the criterion**: a variable-headed equation is outside PeTTa's region of
`(double 4)`, as it is no clause of `double`. On a program holding it, the read words coincide only
if HE's region of `(double 4)` leaves it out as well. -/
theorem region_disagreement (live : List Atom) :
    pettaCallRegion "double" [.grounded (.int 4)] variableHead = false ∧
      (regionRows (eqRegion live doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty)
          (Space.ofList [variableHead]).atoms =
        (completeCall rowSupply "double" [.grounded (.int 4)] (Row.load 0 [variableHead])).selection.read.map
          (fun row => (row.atom, row.serial)) ↔
        eqRegion live doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty variableHead = false) := by
  have outside : pettaCallRegion "double" [.grounded (.int 4)] variableHead = false := by
    decide +kernel
  refine ⟨outside, ?_⟩
  rw [read_word_triangle]
  simp [outside]

/-! ### H1's program: `(= (double $x) (+ $x $x))` -/

/-- The sides of H1's equation: `(double $x)` and `(+ $x $x)`. -/
def doubleX : Atom := .expression [.symbol "double", .var "x"]
def sumXX : Atom := .expression [.symbol "+", .var "x", .var "x"]

/-- `$x ↦ 4`. -/
def xFour : Mettapedia.Languages.MeTTa.HE.Bindings :=
  Mettapedia.Languages.MeTTa.HE.Bindings.empty.assign "x" (.grounded (.int 4))

/-- H1's equation is its own fresh variant for every caller scope that does not show `$x`. -/
theorem doubleX_alpha (live : List Atom)
    (fresh : ∀ atom ∈ live, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs atom "x") :
    AlphaVariantRel live RunsAsFirings.Controls.callDouble
      Mettapedia.Languages.MeTTa.HE.Bindings.empty doubleX sumXX doubleX sumXX := by
  refine ⟨id, Function.injective_id,
    .expression (.cons (.symbol "double") (.cons (.variable "x") .nil)),
    .expression (.cons (.symbol "+") (.cons (.variable "x") (.cons (.variable "x") .nil))), ?_⟩
  intro name occurs visible
  have isX : name = "x" := by
    rcases occurs with left | right
    · have used := atomOccurs_mem_typeVars left
      simpa [doubleX, TypeSubst.typeVars, TypeSubst.typeVarsList] using used
    · have used := atomOccurs_mem_typeVars right
      simpa [sumXX, TypeSubst.typeVars, TypeSubst.typeVarsList] using used
  subst isX
  simp only [Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.QueryVisibleName, id] at visible
  rcases visible with inQuery | ⟨atom, member, occurs⟩ | ⟨value, assigned⟩ |
      ⟨key, value, assigned, _⟩ | ⟨left, right, equal, _⟩
  · have used := atomOccurs_mem_typeVars inQuery
    simp [RunsAsFirings.Controls.callDouble, TypeSubst.typeVars, TypeSubst.typeVarsList] at used
  · exact fresh atom member occurs
  · simp [Mettapedia.Languages.MeTTa.HE.Bindings.empty] at assigned
  · simp [Mettapedia.Languages.MeTTa.HE.Bindings.empty] at assigned
  · simp [Mettapedia.Languages.MeTTa.HE.Bindings.empty] at equal

theorem xFour_free : Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.SemanticLoopFree xFour :=
  Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.semanticLoopFree_single_assignment
    (fun occurs => by cases occurs)

theorem merge_xFour :
    Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.MergeRel equalityGroundedSemantic
      Mettapedia.Languages.MeTTa.HE.Bindings.empty xFour xFour :=
  .mk (order := [.value "x" (.grounded (.int 4))]) (by decide) (.value (.fresh (by rfl)) .nil)

/-- `(double 4)` matches `(double $x)`, binding `$x` to `4`. -/
theorem doubleX_matches :
    MatchRel equalityGroundedSemantic RunsAsFirings.Controls.callDouble doubleX xFour :=
  .expression
    (.cons (.symSym "double" semanticLoopFree_empty)
      (.mk (by simp [constraints, Mettapedia.Languages.MeTTa.HE.Bindings.empty]) .nil)
      (.cons (.nonVarVar rfl xFour_free) merge_xFour .nil))
    xFour_free

theorem merge_logical :
    Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.LogicalMergeRel xFour
      Mettapedia.Languages.MeTTa.HE.Bindings.empty xFour := by
  refine ⟨?_, fun name => if name = "x" then .grounded (.int 4) else .var name, ?_, ?_⟩
  · have same : (⟨xFour.assignments ++ Mettapedia.Languages.MeTTa.HE.Bindings.empty.assignments,
        xFour.equalities ++ Mettapedia.Languages.MeTTa.HE.Bindings.empty.equalities⟩ :
          Mettapedia.Languages.MeTTa.HE.Bindings) = xFour := by decide
    rw [same]
  · intro name value member
    have shape : xFour.assignments = [("x", .grounded (.int 4))] := by decide
    rw [shape, List.mem_singleton] at member
    cases member
    simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.applyTypeValuation]
  · intro left right member
    have shape : xFour.equalities = [] := by decide
    rw [shape] at member
    cases member

/-- **H1's equation is inside the region of HE's query `(double 4)`**, for every caller scope
that does not show `$x`. -/
theorem h1_inside (live : List Atom)
    (fresh : ∀ atom ∈ live, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs atom "x") :
    eqRegion live RunsAsFirings.Controls.callDouble Mettapedia.Languages.MeTTa.HE.Bindings.empty
      RunsAsFirings.Controls.doubleEquation = true := by
  apply eqRegion_of_not_inert
  intro inert
  have hit : EquationRowResultsRel live RunsAsFirings.Controls.callDouble
      Mettapedia.Languages.MeTTa.HE.Bindings.empty 1 RunsAsFirings.Controls.doubleEquation
      [⟨1, doubleX, sumXX, doubleX, sumXX, xFour⟩] :=
    .hit 1 doubleX sumXX doubleX sumXX xFour xFour (doubleX_alpha live fresh) doubleX_matches
      merge_logical
  cases (inert 1 _).mp hit

/-- **The read-word triangle on H1's program.** On `{(p a), (= (double $x) (+ $x $x))}` and for
every caller scope that does not show `$x`, HE's equation query of `(double 4)` and PeTTa's
complete request read the one equation row at position `1`, and `(p a)` is read by neither: H1's
`reads_differ` came from the two encodings, not from the dialects. -/
theorem h1_triangle (live : List Atom)
    (fresh : ∀ atom ∈ live, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs atom "x") :
    regionRows (eqRegion live RunsAsFirings.Controls.callDouble
        Mettapedia.Languages.MeTTa.HE.Bindings.empty)
        (Space.ofList [p a, RunsAsFirings.Controls.doubleEquation]).atoms =
      [(RunsAsFirings.Controls.doubleEquation, 1)] ∧
      (completeCall rowSupply "double" [.grounded (.int 4)]
          (Row.load 0 [p a, RunsAsFirings.Controls.doubleEquation])).selection.read.map
        (fun row => (row.atom, row.serial)) = [(RunsAsFirings.Controls.doubleEquation, 1)] := by
  have heRows : regionRows (eqRegion live RunsAsFirings.Controls.callDouble
      Mettapedia.Languages.MeTTa.HE.Bindings.empty)
      (Space.ofList [p a, RunsAsFirings.Controls.doubleEquation]).atoms =
        [(RunsAsFirings.Controls.doubleEquation, 1)] := by
    simp [regionRows, Space.ofList, h1_inside live fresh, he_pa_outside]
  refine ⟨heRows, ?_⟩
  have agree : ∀ x ∈ [p a, RunsAsFirings.Controls.doubleEquation],
      eqRegion live RunsAsFirings.Controls.callDouble Mettapedia.Languages.MeTTa.HE.Bindings.empty x =
        pettaCallRegion "double" [.grounded (.int 4)] x := by
    intro x member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · rw [he_pa_outside, petta_pa_outside]
    · rw [h1_inside live fresh]
      exact Controls.double_region.1.symm
  exact ((read_word_triangle _ live RunsAsFirings.Controls.callDouble _ "double"
    [.grounded (.int 4)]).mpr agree).symm.trans heRows

/-- A registry with no function. -/
def noFunctions : SpaceSemantics.Program := { equations := [], declarations := [] }

/-- **Where the triangle fails: a variable-headed equation.** Against `{(= ($h 4) 8)}`, HE's equation
query of `(double 4)` matches the row, its head variable taking `double`, and HE answers `8`.
PeTTa's clauses are indexed by a symbol head, so `(double 4)` has no clause: the row is outside its
call region, PeTTa makes no request at all, and it answers `(double 4)`. The shared first-order
fragment therefore excludes equations whose head is not a symbol. -/
theorem variable_head_distinguishes :
    (Mettapedia.Languages.MeTTa.HE.evalAtom (Space.ofList [variableHead])
        HEOnTheStep.NamedDifferences.plus doubleFour Atom.undefinedType
          Mettapedia.Languages.MeTTa.HE.Bindings.empty 40).map Prod.fst = [eight] ∧
      Streaming.values (Streaming.advance noFunctions 30
        (Streaming.enter { state := NamedSpaces.Store.new [variableHead] [] } doubleFour)) =
          [doubleFour] ∧
      requests rowSupply noFunctions 30
        (Streaming.enter { state := NamedSpaces.Store.new [variableHead] [] } doubleFour)
        (Row.load 0 [variableHead]) = [] ∧
      pettaCallRegion "double" [.grounded (.int 4)] variableHead = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Instance

#print axioms regionRows_eq_iff
#print axioms completeCall_load
#print axioms read_word_triangle
#print axioms scanCall_load
#print axioms machine_read_words
#print axioms Instance.he_inside
#print axioms Instance.regions_agree
#print axioms Instance.triangle_double
#print axioms Instance.h1_program
#print axioms Instance.h1_inside
#print axioms Instance.h1_triangle
#print axioms Instance.region_disagreement
#print axioms Instance.variable_head_distinguishes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
