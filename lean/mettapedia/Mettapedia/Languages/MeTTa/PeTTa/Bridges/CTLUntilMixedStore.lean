import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceCapture

/-!
# Occurrence-preserving CTL views of mixed source stores

The source store may interleave frontier, edge, satisfaction and unrelated
constructor rows. Every view selects from the original ordinal stream.
Formula labels use the existing literal codec, so symbol and integer labels
are instances of the same laws. Unrelated open declarations require a rigid
head mismatch; they are not silently treated as ground data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedStore

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics
open CTLUntilSourceRows (number located scan_encoded)
open FlatQueryRelationCompilation (sourceScan)
open FlatQueryRowCodec (Codec)

inductive Row (Label : Type) where
  | frontier (label : Label) (round node : Nat)
  | edge (prior next : Nat)
  | satisfaction (label : Label) (node : Nat)
  | other (head : String) (children : List Atom)
  deriving DecidableEq, Repr

def Row.admitted {Label : Type} : Row Label → Prop
  | .other head _ => head ≠ "fr" ∧ head ≠ "rt" ∧ head ≠ "sat"
  | _ => True

variable {Label : Type} [DecidableEq Label]

def render (codec : Codec Label) : Row Label → Atom
  | .frontier label round node => .expression [.symbol "fr", codec.encode label, number round, number node]
  | .edge prior next => .expression [.symbol "rt", number next, number prior]
  | .satisfaction label node => .expression [.symbol "sat", codec.encode label, number node]
  | .other head children => .expression (.symbol head :: children)

def frontierPattern (codec : Codec Label) (label : Label) (round : Nat) (slot : String) : Atom :=
  .expression [.symbol "fr", codec.encode label, number round, .var slot]
def edgePattern (nextSlot priorSlot : String) : Atom := CTLUntilSourceRows.reversePattern nextSlot priorSlot
def satisfactionPattern (codec : Codec Label) (label : Label) (slot : String) : Atom :=
  .expression [.symbol "sat", codec.encode label, .var slot]

def frontSelect (label : Label) (round : Nat) : Row Label → Option Nat
  | .frontier other step node => if other = label ∧ step = round then some node else none
  | _ => none
def edgeSelect (next : Nat) : Row Label → Option Nat
  | .edge prior target => if target = next then some prior else none
  | _ => none
def satSelect (label : Label) (prior : Nat) : Row Label → Option Unit
  | .satisfaction other node => if other = label ∧ node = prior then some () else none
  | _ => none

theorem different_head (bindings : Subst) (head other : String) (patterns values : List Atom)
    (ordinary : head ≠ "cons") (different : head ≠ other) :
    matchValue bindings (.expression (.symbol head :: patterns)) (.expression (.symbol other :: values)) = none :=
  ClosedQueryAdmission.rigidHeadClash_blocks_match _ _ bindings (by
    simp [ClosedQueryAdmission.rigidHeadClash, ordinary, different])

theorem frontier_match (codec : Codec Label) (label : Label) (round : Nat) (slot : String)
    (row : Row Label) (admitted : row.admitted) :
    matchValue [] (frontierPattern codec label round slot) (render codec row) =
      (frontSelect label round row).map (fun node => [(slot, number node)]) := by
  cases row with
  | frontier other step node =>
      unfold frontierPattern render
      rw [matchValue_expression_of_not_cons _ _ _ (by simp)]
      by_cases sameLabel : other = label
      · subst other
        by_cases sameRound : step = round
        · simp [matchValue.matchValues, matchValue_literal (codec.literal label), matchValue, Subst.lookup,
            Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, number, frontSelect, sameRound]
        · simp [matchValue.matchValues, matchValue_literal (codec.literal label), matchValue, Subst.lookup,
            Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, number, frontSelect, sameRound, Ne.symm sameRound]
      · simp [matchValue.matchValues, matchValue_literal (codec.literal label), codec.injective.eq_iff,
          matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, frontSelect, sameLabel, Ne.symm sameLabel]
  | edge prior next => exact different_head [] "fr" "rt" _ _ (by decide) (by decide)
  | satisfaction other node => exact different_head [] "fr" "sat" _ _ (by decide) (by decide)
  | other head children => exact different_head [] "fr" head _ _ (by decide) (Ne.symm admitted.1)

omit [DecidableEq Label] in
theorem edge_match (codec : Codec Label) (nextSlot priorSlot : String) (apart : priorSlot ≠ nextSlot)
    (next : Nat) (row : Row Label) (admitted : row.admitted) :
    matchValue [(nextSlot, number next)] (edgePattern nextSlot priorSlot) (render codec row) =
      (edgeSelect next row).map (fun prior => [(priorSlot, number prior), (nextSlot, number next)]) := by
  cases row with
  | frontier label round node => exact different_head _ "rt" "fr" _ _ (by decide) (by decide)
  | edge prior target =>
      change matchValue [(nextSlot, number next)] (CTLUntilSourceRows.reversePattern nextSlot priorSlot)
        (CTLPreimageSource.reverseEdge "rt" (prior, target)) = _
      rw [CTLUntilSourceRows.edge_match nextSlot priorSlot apart]
      by_cases same : target = next <;> simp [edgeSelect, same]
  | satisfaction label node => exact different_head _ "rt" "sat" _ _ (by decide) (by decide)
  | other head children => exact different_head _ "rt" head _ _ (by decide) (Ne.symm admitted.2.1)

theorem satisfaction_match (codec : Codec Label) (label : Label) (nextSlot priorSlot : String)
    (next prior : Nat) (row : Row Label) (admitted : row.admitted) :
    matchValue [(priorSlot, number prior), (nextSlot, number next)] (satisfactionPattern codec label priorSlot)
      (render codec row) = (satSelect label prior row).map
        (fun _ => [(priorSlot, number prior), (nextSlot, number next)]) := by
  cases row with
  | frontier other round node => exact different_head _ "sat" "fr" _ _ (by decide) (by decide)
  | edge previous target => exact different_head _ "sat" "rt" _ _ (by decide) (by decide)
  | satisfaction other node =>
      unfold satisfactionPattern render
      rw [matchValue_expression_of_not_cons _ _ _ (by simp)]
      by_cases sameLabel : other = label
      · subst other
        by_cases sameNode : node = prior <;>
          simp [matchValue.matchValues, matchValue_literal (codec.literal label), matchValue, Subst.lookup,
            Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, number, satSelect, sameNode]
      · simp [matchValue.matchValues, matchValue_literal (codec.literal label), codec.injective.eq_iff,
          matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, satSelect, sameLabel, Ne.symm sameLabel]
  | other head children => exact different_head _ "sat" head _ _ (by decide) (Ne.symm admitted.2.2)

omit [DecidableEq Label] in
/-- Restricting the per-row correspondence to the actual input list allows
unrelated rows without assuming that every possible row is admitted. -/
theorem scan_admitted {Value : Type} (codec : Codec Label) (select : Row Label → Option Value)
    (bindings : Value → Subst) (caller : Subst) (pattern : Atom)
    (matching : ∀ row, row.admitted → matchValue caller pattern (render codec row) = (select row).map bindings)
    (offset : Nat) (rows : List (Row Label)) (admitted : ∀ row ∈ rows, row.admitted) :
    sourceScan caller pattern offset (rows.map (render codec)) =
      (located select offset rows).map (fun entry => (entry.1, bindings entry.2)) := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rows ih =>
      have later := ih (offset + 1) (fun value member => admitted value (List.mem_cons_of_mem _ member))
      simp only [List.map_cons, sourceScan, matching row (admitted row List.mem_cons_self), later,
        located, List.zipIdx_cons, List.filterMap_cons]
      cases select row <;> simp

theorem frontier_scan (codec : Codec Label) (label : Label) (round : Nat) (slot : String)
    (offset : Nat) (rows : List (Row Label)) (admitted : ∀ row ∈ rows, row.admitted) :
    sourceScan [] (frontierPattern codec label round slot) offset (rows.map (render codec)) =
      (located (frontSelect label round) offset rows).map (fun entry => (entry.1, [(slot, number entry.2)])) :=
  scan_admitted codec _ _ _ _ (frontier_match codec label round slot) offset rows admitted

omit [DecidableEq Label] in
theorem edge_scan (codec : Codec Label) (nextSlot priorSlot : String) (apart : priorSlot ≠ nextSlot)
    (next offset : Nat) (rows : List (Row Label)) (admitted : ∀ row ∈ rows, row.admitted) :
    sourceScan [(nextSlot, number next)] (edgePattern nextSlot priorSlot) offset (rows.map (render codec)) =
      (located (edgeSelect next) offset rows).map
        (fun entry => (entry.1, [(priorSlot, number entry.2), (nextSlot, number next)])) :=
  scan_admitted codec _ _ _ _ (edge_match codec nextSlot priorSlot apart next) offset rows admitted

theorem satisfaction_scan (codec : Codec Label) (label : Label) (nextSlot priorSlot : String)
    (next prior offset : Nat) (rows : List (Row Label)) (admitted : ∀ row ∈ rows, row.admitted) :
    sourceScan [(priorSlot, number prior), (nextSlot, number next)] (satisfactionPattern codec label priorSlot)
      offset (rows.map (render codec)) =
      (located (satSelect label prior) offset rows).map
        (fun entry => (entry.1, [(priorSlot, number prior), (nextSlot, number next)])) :=
  scan_admitted codec _ (fun (_ : Unit) => [(priorSlot, number prior), (nextSlot, number next)]) _ _
    (satisfaction_match codec label nextSlot priorSlot next prior) offset rows admitted

def sourceCandidates (codec : Codec Label) (label : Label) (round : Nat) (holds : Label)
    (nextSlot priorSlot : String) (fronts graph facts : List (Row Label)) : List CTLUntilSourceRows.Candidate :=
  (sourceScan [] (frontierPattern codec label round nextSlot) 0 (fronts.map (render codec))).flatMap fun outer =>
    (sourceScan outer.2 (edgePattern nextSlot priorSlot) 0 (graph.map (render codec))).flatMap fun middle =>
      (sourceScan middle.2 (satisfactionPattern codec holds priorSlot) 0 (facts.map (render codec))).map fun inner =>
        ⟨outer.1, middle.1, inner.1, inner.2⟩

def locatedCandidates (label : Label) (round : Nat) (holds : Label) (nextSlot priorSlot : String)
    (fronts graph facts : List (Row Label)) : List CTLUntilSourceRows.Candidate :=
  (located (frontSelect label round) 0 fronts).flatMap fun outer =>
    (located (edgeSelect outer.2) 0 graph).flatMap fun middle =>
      (located (satSelect holds middle.2) 0 facts).map fun inner =>
        ⟨outer.1, middle.1, inner.1, [(priorSlot, number middle.2), (nextSlot, number outer.2)]⟩

theorem source_candidates_exact (codec : Codec Label) (label : Label) (round : Nat) (holds : Label)
    (nextSlot priorSlot : String) (apart : priorSlot ≠ nextSlot) (fronts graph facts : List (Row Label))
    (frontsReady : ∀ row ∈ fronts, row.admitted) (graphReady : ∀ row ∈ graph, row.admitted)
    (factsReady : ∀ row ∈ facts, row.admitted) :
    sourceCandidates codec label round holds nextSlot priorSlot fronts graph facts =
      locatedCandidates label round holds nextSlot priorSlot fronts graph facts := by
  simp only [sourceCandidates, frontier_scan codec label round nextSlot 0 fronts frontsReady,
    List.flatMap_map, Function.comp_def, edge_scan codec nextSlot priorSlot apart _ 0 graph graphReady,
    satisfaction_scan codec holds nextSlot priorSlot _ _ 0 facts factsReady, List.map_map, locatedCandidates]

def graphView (rows : List (Row Label)) : List (Nat × Nat) :=
  rows.filterMap fun row => match row with | .edge prior next => some (prior, next) | _ => none

def satisfactionView (label : Label) (rows : List (Row Label)) : List Nat :=
  rows.filterMap fun row => match row with
    | .satisfaction other node => if other = label then some node else none
    | _ => none

omit [DecidableEq Label] in
theorem edge_view (next : Nat) (rows : List (Row Label)) :
    rows.filterMap (edgeSelect next) = (graphView rows).filterMap (CTLUntilSourceRows.edgeSelect next) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      cases row <;>
        simp only [graphView, List.filterMap_cons, edgeSelect, CTLUntilSourceRows.edgeSelect] at ih ⊢
      all_goals first
        | exact ih
        | split <;> simp_all

theorem satisfaction_values (label : Label) (prior : Nat) (rows : List (Row Label)) :
    (rows.filterMap (satSelect label prior)).map (fun _ => prior) =
      (satisfactionView label rows).filter (fun node => node == prior) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      cases row with
      | frontier | edge | other =>
          simpa only [satisfactionView, List.filterMap_cons, satSelect] using ih
      | satisfaction other node =>
          by_cases sameLabel : other = label <;> by_cases sameNode : node = prior <;>
            simp [satSelect, satisfactionView, sameLabel, sameNode, ih]

/-- The ordered candidate bag is independent of colocating the relations.
Coordinates are forgotten only after the exact source scan has retained them. -/
theorem candidate_values (codec : Codec Label) (label : Label) (round : Nat) (holds : Label)
    (nextSlot priorSlot : String) (apart : priorSlot ≠ nextSlot) (fronts graph facts : List (Row Label))
    (frontsReady : ∀ row ∈ fronts, row.admitted) (graphReady : ∀ row ∈ graph, row.admitted)
    (factsReady : ∀ row ∈ facts, row.admitted) :
    (sourceCandidates codec label round holds nextSlot priorSlot fronts graph facts).map
      (fun candidate => Mettapedia.Languages.ProcessCalculi.MORK.applySubst candidate.bindings (.var priorSlot)) =
      (Mettapedia.Machines.CTLUntilCandidateBag.candidates (graphView graph)
        (satisfactionView holds facts) (fronts.filterMap (frontSelect label round))).map number := by
  rw [source_candidates_exact codec label round holds nextSlot priorSlot apart fronts graph facts frontsReady graphReady factsReady]
  have captured : ∀ prior next,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst [(priorSlot, number prior), (nextSlot, number next)]
        (.var priorSlot) = number prior := by
    intro prior next
    simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst, Subst.lookup]
  simp only [locatedCandidates, List.map_flatMap, List.map_map, Function.comp_def, captured]
  rw [CTLUntilSourceRows.located_flatMap (frontSelect label round) 0 fronts
    (fun next => (located (edgeSelect next) 0 graph).flatMap
      (fun edge => (located (satSelect holds edge.2) 0 facts).map (fun _ => number edge.2)))]
  unfold Mettapedia.Machines.CTLUntilCandidateBag.candidates
  rw [List.map_flatMap]
  apply congrArg (fun body : Nat → List Atom => (fronts.filterMap (frontSelect label round)).flatMap body)
  funext next
  rw [CTLUntilSourceRows.located_flatMap (edgeSelect next) 0 graph
    (fun prior => (located (satSelect holds prior) 0 facts).map (fun _ => number prior))]
  have witnesses : ∀ prior,
      (located (satSelect holds prior) 0 facts).map (fun _ => number prior) =
        ((satisfactionView holds facts).filter (fun node => node == prior)).map number := by
    intro prior
    rw [CTLUntilSourceRows.located_map (satSelect holds prior) 0 facts (fun _ => number prior)]
    rw [← satisfaction_values holds prior facts, List.map_map]
    rfl
  simp only [witnesses, ← List.map_flatMap]
  rw [edge_view, CTLUntilSourceRows.edge_values]

omit [DecidableEq Label] in
/-- Open unrelated declarations are admitted by a rigid head mismatch.
Candidate rows themselves are ground codec images. -/
theorem rows_ready (codec : Codec Label) (head : String) (arguments : List Atom)
    (recognized : head ∈ ["fr", "rt", "sat"]) (rows : List (Row Label))
    (admitted : ∀ row ∈ rows, row.admitted) :
    ClosedQueryAdmission.rowsReady (.expression (.symbol head :: arguments)) (rows.map (render codec)) = true := by
  apply List.all_eq_true.mpr
  intro atom member
  obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
  cases row with
  | frontier label round node =>
      simp [ClosedQueryAdmission.rowReady, render, number,
        Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom,
        Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom.isGroundList,
        ClosedQueryAdmission.literal_ground (codec.literal label)]
  | edge prior next =>
      simp [ClosedQueryAdmission.rowReady, render, number,
        Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom,
        Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom.isGroundList]
  | satisfaction label node =>
      simp [ClosedQueryAdmission.rowReady, render, number,
        Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom,
        Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom.isGroundList,
        ClosedQueryAdmission.literal_ground (codec.literal label)]
  | other other children =>
      have safe := admitted (.other other children) present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recognized
      rcases recognized with rfl | rfl | rfl <;>
        simp [ClosedQueryAdmission.rowReady, ClosedQueryAdmission.rigidHeadClash, render,
          Ne.symm safe.1, Ne.symm safe.2.1, Ne.symm safe.2.2]

def natural? : Atom → Option Nat
  | .grounded (.int value) => if 0 ≤ value then some value.toNat else none
  | _ => none

theorem natural_exact (atom : Atom) (value : Nat) (decoded : natural? atom = some value) :
    number value = atom := by
  unfold natural? at decoded
  split at decoded
  next integer =>
    split at decoded
    next nonnegative =>
      cases Option.some.inj decoded
      simp [number, Int.toNat_of_nonneg nonnegative]
    next => cases decoded
  next => cases decoded

def decode (codec : Codec Label) : Atom → Option (Row Label)
  | .expression [.symbol "fr", formula, round, node] => do
      return .frontier (← codec.decode formula) (← natural? round) (← natural? node)
  | .expression [.symbol "rt", next, prior] => do
      return .edge (← natural? prior) (← natural? next)
  | .expression [.symbol "sat", formula, node] => do
      return .satisfaction (← codec.decode formula) (← natural? node)
  | .expression (.symbol head :: children) =>
      if head ≠ "fr" ∧ head ≠ "rt" ∧ head ≠ "sat" then some (.other head children) else none
  | _ => none

omit [DecidableEq Label] in
theorem decode_sound (codec : Codec Label) (atom : Atom) (row : Row Label)
    (decoded : decode codec atom = some row) : row.admitted ∧ render codec row = atom := by
  unfold decode at decoded
  split at decoded
  next formula round node =>
    obtain ⟨label, labelRead, step, stepRead, vertex, vertexRead, same⟩ :
        ∃ label, codec.decode formula = some label ∧ ∃ step, natural? round = some step ∧
          ∃ vertex, natural? node = some vertex ∧ Row.frontier label step vertex = row := by
      simpa only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using decoded
    subst row
    exact ⟨trivial, by simp [render, codec.exact _ _ labelRead, natural_exact _ _ stepRead, natural_exact _ _ vertexRead]⟩
  next target previous =>
    obtain ⟨prior, priorRead, next, nextRead, same⟩ :
        ∃ prior, natural? previous = some prior ∧ ∃ next, natural? target = some next ∧ Row.edge prior next = row := by
      simpa only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using decoded
    subst row
    exact ⟨trivial, by simp [render, natural_exact _ _ priorRead, natural_exact _ _ nextRead]⟩
  next formula node =>
    obtain ⟨label, labelRead, vertex, vertexRead, same⟩ :
        ∃ label, codec.decode formula = some label ∧ ∃ vertex, natural? node = some vertex ∧
          Row.satisfaction label vertex = row := by
      simpa only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using decoded
    subst row
    exact ⟨trivial, by simp [render, codec.exact _ _ labelRead, natural_exact _ _ vertexRead]⟩
  next head children =>
    split at decoded
    next safe => cases Option.some.inj decoded; exact ⟨safe, rfl⟩
    next => cases decoded
  next => cases decoded

omit [DecidableEq Label] in
theorem decode_render (codec : Codec Label) (row : Row Label) (admitted : row.admitted) :
    decode codec (render codec row) = some row := by
  cases row with
  | frontier label round node => simp [decode, render, codec.roundtrip, natural?, number]
  | edge prior next => simp [decode, render, natural?, number]
  | satisfaction label node => simp [decode, render, codec.roundtrip, natural?, number]
  | other head children =>
      simp only [render]
      unfold decode
      split <;> simp_all [Row.admitted]

def decodeRows (codec : Codec Label) : List Atom → Option (List (Row Label))
  | [] => some []
  | atom :: atoms => do return (← decode codec atom) :: (← decodeRows codec atoms)

omit [DecidableEq Label] in
theorem decode_rows_sound (codec : Codec Label) (atoms : List Atom) (rows : List (Row Label))
    (decoded : decodeRows codec atoms = some rows) :
    rows.map (render codec) = atoms ∧ ∀ row ∈ rows, row.admitted := by
  induction atoms generalizing rows with
  | nil => cases Option.some.inj decoded; simp
  | cons atom atoms ih =>
      obtain ⟨row, rowRead, rest, restRead, same⟩ :
          ∃ row, decode codec atom = some row ∧ ∃ rest, decodeRows codec atoms = some rest ∧ row :: rest = rows := by
        simpa only [decodeRows, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using decoded
      subst rows
      obtain ⟨ready, actual⟩ := decode_sound codec atom row rowRead
      obtain ⟨remainder, restReady⟩ := ih rest restRead
      exact ⟨by simp [actual, remainder], by simpa using And.intro ready restReady⟩

omit [DecidableEq Label] in
theorem decode_rows_complete (codec : Codec Label) (rows : List (Row Label))
    (admitted : ∀ row ∈ rows, row.admitted) : decodeRows codec (rows.map (render codec)) = some rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons, decodeRows, decode_render codec row (admitted row List.mem_cons_self),
        ih (fun value member => admitted value (List.mem_cons_of_mem _ member))]
      rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedStore
