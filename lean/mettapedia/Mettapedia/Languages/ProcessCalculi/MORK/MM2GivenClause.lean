import Mettapedia.Languages.ProcessCalculi.MORK.MM2MatchingBatch
import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternMonotonicity
import Mettapedia.GSLT.Core.ResumableGivenClause

/-!
# Positive MM2 inference as resumable given-clause generation

A selected occurrence supplies a `selected` fact. Positive MM2 premises join
that fact with the captured processed context; one authored add conclusion
creates new owned occurrences. Generation runs through the actual matching
cursor, including suspension before any row is available. Completed publication
uses the existing GCL operation on processed/passive occurrences.

This is a declared positive, add-only inference protocol. It does not identify
the mutable raw MM2 driver with monotone saturation. Its MM2 store observation
forgets occurrence traces and retains the support of instantiated add outputs.
The full selected-exec and reflective add/remove boundary is proved separately
in `MM2MatchingBatch`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2GivenClause

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Core
open InferenceControl (WorkOccurrence)
open Mettapedia.GSLT.LanguageDef
open HostCalls (Pull collect)
open Mettapedia.Machines.Cursor
open MM2MatchingCursor
open ReflectiveComputable
open Conformance.Computable

abbrev Node := WorkOccurrence Atom

def context (given : Node) (processed : List Node) : List Atom :=
  .expression [.symbol "selected", given.state] :: processed.map WorkOccurrence.state

/-- Each row has its own child identity even when its instantiated conclusion
is equal to another row's conclusion. -/
def children (given : Node) (conclusion : Atom) (rows : List Row) (first : Nat) : List Node :=
  (rows.zipIdx first).filterMap fun (row, index) =>
    (instantiateTemplateAtom? row.1 conclusion).map fun answer =>
      ⟨answer, given.trace ++ [index]⟩

def referenceRows (pattern : Pattern) (given : Node) (processed : List Node) : List Row :=
  residualRows (entries (context given processed))
    (start (context given processed) (.compat pattern))

def system (pattern : Pattern) (conclusion : Atom) : GivenClauseLoop.System Node Node where
  observe given _ := some given
  generate given processed := children given conclusion (referenceRows pattern given processed) 0

structure Generation where
  matcher : MM2MatchingCursor.State
  rowIndex : Nat

def initial (pattern : Pattern) (given : Node) (processed : List Node) : Generation :=
  ⟨start (context given processed) (.compat pattern), 0⟩

/-- A match row is transformed by one finite authored template. A declined
unbound template is not an invented answer, and it still consumes its row. -/
def pullChild (patternSpace : List Entry) (given : Node) (conclusion : Atom)
    (state : Generation) : Pull Generation Node :=
  match pull patternSpace state.matcher with
  | .done => .done
  | .suspend residual => .suspend ⟨residual, state.rowIndex⟩
  | .yield row residual =>
      let next : Generation := ⟨residual, state.rowIndex + 1⟩
      match instantiateTemplateAtom? row.1 conclusion with
      | none => .suspend next
      | some answer => .yield ⟨answer, given.trace ++ [state.rowIndex]⟩ next

def generated (space : List Entry) (given : Node) (conclusion : Atom)
    (state : Generation) : List Node :=
  children given conclusion (residualRows space state.matcher) state.rowIndex

theorem pullChild_rows (space : List Entry) (given : Node) (conclusion : Atom)
    (state : Generation) :
    match pullChild space given conclusion state with
    | .done => generated space given conclusion state = []
    | .suspend next => generated space given conclusion state = generated space given conclusion next
    | .yield child next => generated space given conclusion state =
        child :: generated space given conclusion next := by
  have localLaw := pull_rows space state.matcher
  unfold pullChild
  cases moved : pull space state.matcher with
  | done =>
      simp only [moved] at localLaw
      simp [generated, children, localLaw]
  | suspend next =>
      simp only [moved] at localLaw
      simp only [generated, localLaw]
  | yield row next =>
      simp only [moved] at localLaw
      cases result : instantiateTemplateAtom? row.1 conclusion <;>
        simp [result, generated, children, localLaw, List.zipIdx_cons]

theorem pullChild_cost (space : List Entry) (given : Node) (conclusion : Atom)
    (state : Generation) :
    match pullChild space given conclusion state with
    | .done => remainingCost space state.matcher = 0
    | .suspend next => remainingCost space next.matcher < remainingCost space state.matcher
    | .yield _ next => remainingCost space next.matcher < remainingCost space state.matcher := by
  have decreases := pull_cost space state.matcher
  unfold pullChild
  cases moved : pull space state.matcher with
  | done => simpa only [moved] using decreases
  | suspend next => simpa only [moved] using decreases
  | yield row next =>
      simp only [moved] at decreases
      cases found : instantiateTemplateAtom? row.1 conclusion <;>
        simpa only [found] using decreases

theorem collect_complete (space : List Entry) (given : Node) (conclusion : Atom)
    (fuel : Nat) (state : Generation) (enough : remainingCost space state.matcher < fuel) :
    collect (pullChild space given conclusion) fuel state =
      some (generated space given conclusion state) := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
      have semantic := pullChild_rows space given conclusion state
      have decreases := pullChild_cost space given conclusion state
      cases moved : pullChild space given conclusion state with
      | done =>
          simp only [moved] at semantic
          simp [collect, moved, semantic]
      | suspend next =>
          simp only [moved] at semantic decreases
          have small : remainingCost space next.matcher < fuel := by omega
          simp [collect, moved, ih next small, semantic]
      | yield child next =>
          simp only [moved] at semantic decreases
          have small : remainingCost space next.matcher < fuel := by omega
          simp [collect, moved, ih next small, semantic]

theorem collect_sound (space : List Entry) (given : Node) (conclusion : Atom)
    (fuel : Nat) (state : Generation) (result : List Node)
    (completed : collect (pullChild space given conclusion) fuel state = some result) :
    result = generated space given conclusion state := by
  induction fuel generalizing state result with
  | zero => simp [collect] at completed
  | succ fuel ih =>
      have semantic := pullChild_rows space given conclusion state
      cases moved : pullChild space given conclusion state with
      | done =>
          simp only [moved] at semantic
          simpa [collect, moved, semantic] using completed.symm
      | suspend next =>
          simp only [moved] at semantic
          simp only [collect, moved] at completed
          exact (ih next result completed).trans semantic.symm
      | yield child next =>
          simp only [moved] at semantic
          simp only [collect, moved] at completed
          cases found : collect (pullChild space given conclusion) fuel next with
          | none => simp [found] at completed
          | some tail =>
              simp only [found, Option.map_some, Option.some.injEq] at completed
              subst result
              rw [ih next tail found, semantic]

theorem children_values (given : Node) (conclusion : Atom) (rows : List Row) (first : Nat) :
    (children given conclusion rows first).map WorkOccurrence.state =
      rows.filterMap (fun row => instantiateTemplateAtom? row.1 conclusion) := by
  induction rows generalizing first with
  | nil => rfl
  | cons row rest ih =>
      simp only [children, List.zipIdx_cons, List.filterMap_cons]
      cases found : instantiateTemplateAtom? row.1 conclusion <;>
        simp only [Option.map_none, Option.map_some, List.map_cons,
          List.cons.injEq, true_and] <;>
        exact ih (first + 1)

theorem generated_values (pattern : Pattern) (conclusion : Atom)
    (given : Node) (processed : List Node) :
    ((system pattern conclusion).generate given processed).map WorkOccurrence.state =
      (cmatchPattern [] (context given processed) pattern).filterMap
        (fun row => instantiateTemplateAtom? row.1 conclusion) := by
  rw [system, children_values]
  have erasure := start_rows_erase (context given processed) (.compat pattern) []
  change (referenceRows pattern given processed).map eraseRow =
    cmatchPattern [] (context given processed) pattern at erasure
  rw [← erasure, List.filterMap_map]
  rfl

/-- The independent positive input judgment and template instantiation are the
entire inference authority for a generated value. -/
def Derives (pattern : Pattern) (conclusion : Atom) (given : Node)
    (processed : List Node) (answer : Atom) : Prop :=
  ∃ substitution witnesses,
    (substitution, witnesses) ∈ matchPattern [] (context given processed).toFinset pattern ∧
      instantiateTemplateAtom? substitution conclusion = some answer

theorem generates_iff_derives (pattern : Pattern) (conclusion : Atom)
    (given : Node) (processed : List Node) (answer : Atom) :
    (∃ child ∈ (system pattern conclusion).generate given processed, child.state = answer) ↔
      Derives pattern conclusion given processed answer := by
  rw [← List.mem_map (f := WorkOccurrence.state)]
  rw [generated_values, List.mem_filterMap]
  constructor
  · rintro ⟨⟨substitution, witnesses⟩, matched, instantiates⟩
    exact ⟨substitution, witnesses.toFinset,
      Conformance.cmatchPattern_toFinset_sound [] _ pattern _ _ matched, instantiates⟩
  · rintro ⟨substitution, witnesses, matched, instantiates⟩
    obtain ⟨physical, found, _⟩ :=
      Conformance.matchPattern_toFinset_complete [] _ pattern _ _ matched
    exact ⟨(substitution, physical), found, instantiates⟩

theorem generation_support_mono (pattern : Pattern) (conclusion : Atom)
    (given : Node) (early later : List Node)
    (included : ∀ node ∈ early, node ∈ later) (answer : Atom)
    (generated : answer ∈ ((system pattern conclusion).generate given early).map
      WorkOccurrence.state) :
    answer ∈ ((system pattern conclusion).generate given later).map WorkOccurrence.state := by
  rw [generated_values, List.mem_filterMap] at generated ⊢
  obtain ⟨row, matched, instantiates⟩ := generated
  refine ⟨row, ?_, instantiates⟩
  apply cmatchPattern_mono [] (context given early) (context given later) pattern
    (fun atom member => ?_) row.1 row.2 matched
  simp only [context, List.mem_cons, List.mem_map] at member ⊢
  rcases member with marker | ⟨node, member, rfl⟩
  · exact Or.inl marker
  · exact Or.inr ⟨node, included node member, rfl⟩

/-- The concrete authored MM2 activation for the positive inference rule. -/
def directive (pattern : Pattern) (conclusion : Atom) : SourceExecFact :=
  let input := .expression (.symbol "," :: pattern.atoms)
  let output := .expression [.symbol ",", conclusion]
  { atom := .expression [.symbol "exec", .symbol "inference", input, output]
    loc := .symbol "inference"
    rule := ⟨0, "unnamed", .compat pattern, [], ⟨[.add conclusion]⟩⟩ }

theorem directive_decodes (pattern : Pattern) (conclusion : Atom) :
    extractSupportedSourceExecFact (directive pattern conclusion).atom =
      some (directive pattern conclusion) := by rfl

/-- A structurally excluded control atom cannot create an extra premise match. -/
theorem cmatchPattern_prepend_inert (pattern : Pattern) (control : Atom)
    (space : List Atom)
    (irrelevant : ∀ substitution premise, premise ∈ pattern.atoms →
      cmatchAtom substitution premise control = none) :
    cmatchPattern [] (control :: space) pattern = cmatchPattern [] space pattern := by
  suffices general : ∀ patterns : List Atom,
      (∀ premise ∈ patterns, premise ∈ pattern.atoms) → ∀ substitution witnesses,
        cmatchPattern.go (control :: space) patterns substitution witnesses =
          cmatchPattern.go space patterns substitution witnesses by
    exact general pattern.atoms (fun _ member => member) [] []
  intro patterns included
  induction patterns with
  | nil => intros; rfl
  | cons premise rest ih =>
      intro substitution witnesses
      simp only [cmatchPattern.go, List.filterMap_cons,
        irrelevant substitution premise (included premise (by simp)), Option.map_none]
      apply List.flatMap_congr
      intro found _
      exact ih (fun later member => included later (by simp [member])) found.1
        (found.2 :: witnesses)

/-- The actual MM2 add sink observes the support of generated conclusions.
Its support observation does not silently become an occurrence bag. -/
theorem native_activation_support (pattern : Pattern) (conclusion : Atom)
    (given : Node) (processed : List Node)
    (irrelevant : ∀ substitution premise, premise ∈ pattern.atoms →
      cmatchAtom substitution premise (directive pattern conclusion).atom = none)
    (answer : Atom) :
    answer ∈ cFireReflectiveSourceExecFact
      ((directive pattern conclusion).atom :: context given processed)
      (directive pattern conclusion) ↔
      answer ∈ context given processed ∨
        ∃ child ∈ (system pattern conclusion).generate given processed, child.state = answer := by
  have exactRows := cmatchPattern_prepend_inert pattern
    (directive pattern conclusion).atom (context given processed) irrelevant
  change answer ∈ cApplyReflectiveTemplate
    (((directive pattern conclusion).atom :: context given processed).erase
      (directive pattern conclusion).atom)
    ((cmatchInputSpec []
      ((directive pattern conclusion).atom ::
        (((directive pattern conclusion).atom :: context given processed).erase
          (directive pattern conclusion).atom)) (.compat pattern)).map Prod.fst)
    ⟨[.add conclusion]⟩ ↔ _
  simp only [List.erase_cons_head, cmatchInputSpec, exactRows,
    cApplyReflectiveTemplate, cApplyReflectiveSinkBatch]
  change answer ∈ WQComputable.cUnionSupport (context given processed) _ ↔ _
  rw [mem_cUnionSupport_iff, mem_foldl_stageReflectiveSupportSink_iff]
  simp only [List.not_mem_nil, false_or]
  rw [← List.mem_map (f := WorkOccurrence.state), generated_values, List.mem_filterMap]
  simp only [List.mem_map]
  aesop

theorem child_origin (given : Node) (conclusion : Atom) (rows : List Row)
    (first : Nat) (child : Node) (present : child ∈ children given conclusion rows first) :
    ∃ row index, (row, index) ∈ rows.zipIdx first ∧
      instantiateTemplateAtom? row.1 conclusion = some child.state ∧
      child.trace = given.trace ++ [index] := by
  simp only [children, List.mem_filterMap] at present
  obtain ⟨⟨row, index⟩, member, found⟩ := present
  simp only [Option.map_eq_some_iff] at found
  obtain ⟨answer, instantiates, equal⟩ := found
  cases equal
  exact ⟨row, index, member, instantiates, rfl⟩

theorem children_occurrence_nodup (given : Node) (conclusion : Atom)
    (rows : List Row) (first : Nat) :
    ((children given conclusion rows first).map WorkOccurrence.trace).Nodup := by
  induction rows generalizing first with
  | nil => simp [children]
  | cons row rest ih =>
      have restUnique := ih (first + 1)
      have headFresh : given.trace ++ [first] ∉
          (children given conclusion rest (first + 1)).map WorkOccurrence.trace := by
        intro member
        obtain ⟨child, present, same⟩ := List.mem_map.mp member
        obtain ⟨matched, index, located, _, traceEq⟩ :=
          child_origin given conclusion rest (first + 1) child present
        have lower := List.le_snd_of_mem_zipIdx located
        rw [traceEq] at same
        have equal : index = first := by simpa using same
        omega
      simp only [children, List.zipIdx_cons, List.filterMap_cons]
      cases found : instantiateTemplateAtom? row.1 conclusion with
      | none => exact restUnique
      | some answer =>
          change ((given.trace ++ [first]) ::
            (children given conclusion rest (first + 1)).map WorkOccurrence.trace).Nodup
          exact List.nodup_cons.mpr ⟨headFresh, restUnique⟩

variable {count : Nat} [NeZero count]

abbrev Snapshot := GivenClauseLoop.Snapshot Node Node count

abbrev Generator (_pattern : Pattern) (conclusion : Atom)
    (state : Snapshot (count := count)) (selected : ResumableGivenClause.Selected state) :=
  NativeControlCursor.provider
    (pullChild (entries (context selected.val state.processed)) selected.val conclusion)

def openGeneration (pattern : Pattern) (conclusion : Atom)
    (state : Snapshot (count := count)) (selected : ResumableGivenClause.Selected state) :
    Packet (Generator pattern conclusion state selected) (NativeControlCursor.client Node) () :=
  NativeControlCursor.packet _ (initial pattern selected.val state.processed) []

def publish (pattern : Pattern) (conclusion : Atom)
    (disciplines : Fin count → WeightedOccurrenceControl.QueueDiscipline Node)
    (state : Snapshot (count := count)) (selected : ResumableGivenClause.Selected state) :
    Outcome (Generator pattern conclusion state selected) (NativeControlCursor.client Node) () →
      Option (Snapshot (count := count))
  | .paused _ => none
  | .done result =>
      ResumableGivenClause.publish (system pattern conclusion) disciplines state selected
        (provider := Sequence.tails Node) (.done ⟨(), result.2.1, []⟩)

def allowance (pattern : Pattern) (state : Snapshot (count := count))
    (selected : ResumableGivenClause.Selected state) : Nat :=
  remainingCost (entries (context selected.val state.processed))
    (initial pattern selected.val state.processed).matcher + 2

theorem completed_publication (pattern : Pattern) (conclusion : Atom)
    (disciplines : Fin count → WeightedOccurrenceControl.QueueDiscipline Node)
    (state : Snapshot (count := count)) (selected : ResumableGivenClause.Selected state) :
    publish pattern conclusion disciplines state selected
      (advance (Generator pattern conclusion state selected) (NativeControlCursor.client Node)
        (fun _ _ => 1) (allowance pattern state selected)
        (openGeneration pattern conclusion state selected)).2 =
      some (GivenClauseLoop.Snapshot.tick (system pattern conclusion) disciplines state) := by
  have collection := NativeControlCursor.advance_collect
    (pullChild (entries (context selected.val state.processed)) selected.val conclusion)
    (remainingCost (entries (context selected.val state.processed))
      (initial pattern selected.val state.processed).matcher + 1)
    (initial pattern selected.val state.processed) []
  rw [collect_complete _ _ _ _ _ (Nat.lt_succ_self _)] at collection
  simp only [List.reverse_nil, List.nil_append, Option.map_some] at collection
  let outcome := (advance (Generator pattern conclusion state selected)
    (NativeControlCursor.client Node) (fun _ _ => 1) (allowance pattern state selected)
    (openGeneration pattern conclusion state selected)).2
  change NativeControlCursor.published _ outcome = some _ at collection
  change publish pattern conclusion disciplines state selected outcome = _
  cases splitOutcome : outcome with
  | paused residual => simp [splitOutcome, NativeControlCursor.published] at collection
  | done result =>
      simp only [splitOutcome, NativeControlCursor.published, Option.some.injEq] at collection
      simp only [publish, ResumableGivenClause.publish, collection,
        GivenClauseLoop.Snapshot.tick, selected.property]
      rfl

/-- No smaller successful budget may publish an incomplete GCL generation. -/
theorem publication_sound (pattern : Pattern) (conclusion : Atom)
    (disciplines : Fin count → WeightedOccurrenceControl.QueueDiscipline Node)
    (state : Snapshot (count := count)) (selected : ResumableGivenClause.Selected state)
    (fuel : Nat) (target : Snapshot (count := count))
    (published : publish pattern conclusion disciplines state selected
      (advance (Generator pattern conclusion state selected) (NativeControlCursor.client Node)
        (fun _ _ => 1) fuel (openGeneration pattern conclusion state selected)).2 = some target) :
    target = GivenClauseLoop.Snapshot.tick (system pattern conclusion) disciplines state := by
  cases fuel with
  | zero => simp [advance, publish] at published
  | succ fuel =>
      have collection := NativeControlCursor.advance_collect
        (pullChild (entries (context selected.val state.processed)) selected.val conclusion)
        fuel (initial pattern selected.val state.processed) []
      simp only [List.reverse_nil, List.nil_append] at collection
      let outcome := (advance (Generator pattern conclusion state selected)
        (NativeControlCursor.client Node) (fun _ _ => 1) (fuel + 1)
        (openGeneration pattern conclusion state selected)).2
      change publish pattern conclusion disciplines state selected outcome = some target at published
      change NativeControlCursor.published _ outcome = _ at collection
      cases splitOutcome : outcome with
      | paused residual => simp [splitOutcome, publish] at published
      | done result =>
          cases matched : collect
              (pullChild (entries (context selected.val state.processed)) selected.val conclusion)
              fuel (initial pattern selected.val state.processed) with
          | none => simp [splitOutcome, NativeControlCursor.published, matched] at collection
          | some nodes =>
              simp only [splitOutcome, NativeControlCursor.published, matched,
                Option.map_some, Option.some.injEq] at collection
              have complete := collect_sound _ _ _ _ _ nodes matched
              simp only [splitOutcome, publish, ResumableGivenClause.publish,
                collection, complete, Option.some.injEq] at published
              rw [← published]
              simp only [GivenClauseLoop.Snapshot.tick, selected.property]
              rfl

omit [NeZero count] in
/-- Retained row position, substitution stack and collected occurrences survive
arbitrary budget partitions without restarting the join. -/
theorem pause_resume_exact (pattern : Pattern) (conclusion : Atom)
    (state : Snapshot (count := count)) (selected : ResumableGivenClause.Selected state)
    (first second : Nat) :
    advance (Generator pattern conclusion state selected) (NativeControlCursor.client Node)
      (fun _ _ => 1) (first + second) (openGeneration pattern conclusion state selected) =
    resume (Generator pattern conclusion state selected) (NativeControlCursor.client Node)
      (fun _ _ => 1) second
      (advance (Generator pattern conclusion state selected) (NativeControlCursor.client Node)
        (fun _ _ => 1) first (openGeneration pattern conclusion state selected)) := by
  exact advance_add _ _ _ first second _

theorem paused_cannot_publish (pattern : Pattern) (conclusion : Atom)
    (disciplines : Fin count → WeightedOccurrenceControl.QueueDiscipline Node)
    (state : Snapshot (count := count)) (selected : ResumableGivenClause.Selected state)
    (residual : Packet (Generator pattern conclusion state selected)
      (NativeControlCursor.client Node) ()) :
    publish pattern conclusion disciplines state selected (.paused residual) = none := rfl

namespace Controls

def symbol (name : String) : Atom := .symbol name
def term (name : String) (args : List Atom) : Atom := .expression (symbol name :: args)
def edge (left right : String) : Atom := term "edge" [symbol left, symbol right]
def root : Node := ⟨term "query" [symbol "A", symbol "C"], [7]⟩
def processed : List Node := [⟨edge "A" "B", [0]⟩, ⟨edge "B" "C", [1]⟩,
  ⟨edge "A" "D", [2]⟩, ⟨edge "D" "C", [3]⟩]
def premises : Pattern := ⟨[
  term "selected" [term "query" [.var "from", .var "to"]],
  term "edge" [.var "from", .var "middle"],
  term "edge" [.var "middle", .var "to"]]⟩
def conclusion : Atom := term "reachable" [.var "from", .var "to"]
def answer : Atom := term "reachable" [symbol "A", symbol "C"]

theorem two_derivations_one_value :
    (system premises conclusion).generate root processed =
      [⟨answer, [7, 0]⟩, ⟨answer, [7, 1]⟩] := by decide

theorem generated_support_is_one_fact :
    (((system premises conclusion).generate root processed).map WorkOccurrence.state).toFinset =
      {answer} := by decide

theorem match_cursor_reaches_the_join :
    collect (pullChild (entries (context root processed)) root conclusion) 100
      (initial premises root processed) = some [⟨answer, [7, 0]⟩, ⟨answer, [7, 1]⟩] := by
  decide

theorem insufficient_quantum_does_not_publish :
    collect (pullChild (entries (context root processed)) root conclusion) 2
      (initial premises root processed) = none := rfl

theorem control_shell_is_not_a_premise (substitution : Subst) (premise : Atom)
    (present : premise ∈ premises.atoms) :
    cmatchAtom substitution premise (directive premises conclusion).atom = none := by
  simp only [premises, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl <;> rfl

theorem actual_mm2_activation_has_the_same_new_fact :
    answer ∈ cFireReflectiveSourceExecFact
      ((directive premises conclusion).atom :: context root processed)
      (directive premises conclusion) := by
  apply (native_activation_support premises conclusion root processed
    control_shell_is_not_a_premise answer).2
  exact Or.inr ⟨⟨answer, [7, 0]⟩, by rw [two_derivations_one_value]; simp, rfl⟩

theorem unbound_conclusion_does_not_invent_a_child :
    (system premises (.var "missing")).generate root processed = [] := by decide

end Controls

#print axioms generates_iff_derives
#print axioms generation_support_mono
#print axioms native_activation_support
#print axioms children_occurrence_nodup
#print axioms completed_publication
#print axioms publication_sound
#print axioms pause_resume_exact

end Mettapedia.Languages.ProcessCalculi.MORK.MM2GivenClause
