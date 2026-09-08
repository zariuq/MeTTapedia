import Mettapedia.GSLT.Parsing.HornEquationContextual

/-!
# Contextual execution of the authored BNF text-append equations

This is an all-input list-concatenation theorem for two source equation
shapes. The source qualification client must prove that its actual source
occurrences have these shapes; this module does not install replacement
equations or define the source program from an expected answer.

The path records the recursive calls under `bnf-v1:text-cons`. Its result
is compared with ordinary list append, independently of source rewriting.
It supplies a helper law for denotation, not the whole denotation theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PlainBnfSourceTextAppend

open HornCertificate HornEquationInstantiation HornEquationContextual

/-- Expected shape, to be checked against an actual source occurrence. -/
def emptyShape : Term × Term :=
  (.app "bnf-v1:text-append"
    (.cons (.app "bnf-v1:text-nil" .nil) (.cons (.var 0) .nil)), .var 0)

/-- Expected shape, to be checked against an actual source occurrence. -/
def consShape : Term × Term :=
  (.app "bnf-v1:text-append"
    (.cons (.app "bnf-v1:text-cons" (.cons (.var 0) (.cons (.var 1) .nil)))
      (.cons (.var 2) .nil)),
   .app "bnf-v1:text-cons"
    (.cons (.var 0)
      (.cons (.app "bnf-v1:text-append" (.cons (.var 1) (.cons (.var 2) .nil))) .nil)))

def encodeText : List Char → GroundTerm
  | [] => .app "bnf-v1:text-nil" .nil
  | character :: rest => .app "bnf-v1:text-cons"
      (.cons (.integer character.toNat) (.cons (encodeText rest) .nil))

def appendCall (left right : List Char) : GroundTerm :=
  .app "bnf-v1:text-append" (.cons (encodeText left) (.cons (encodeText right) .nil))

/-- There is one source use for every left character, followed by the base
case. Addresses descend through the second argument of the output cons. -/
def appendActions (emptyOccurrence consOccurrence : Nat) : Nat → List Action
  | 0 => [⟨emptyOccurrence, []⟩]
  | count + 1 =>
      ⟨consOccurrence, []⟩ ::
        (appendActions emptyOccurrence consOccurrence count).map (underArgument 1)

@[simp] theorem appendActions_length (emptyOccurrence consOccurrence count : Nat) :
    (appendActions emptyOccurrence consOccurrence count).length = count + 1 := by
  induction count with
  | zero => rfl
  | succ count ih => simp [appendActions, ih, Nat.add_assoc]

theorem appendActions_occurrences (emptyOccurrence consOccurrence count : Nat) :
    (appendActions emptyOccurrence consOccurrence count).map Action.occurrence =
      List.replicate count consOccurrence ++ [emptyOccurrence] := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [appendActions, List.map_cons, contextual_occurrence_order, ih,
      List.replicate_succ, List.cons_append]

private theorem source_root {program : Program} {occurrence : Nat}
    {left right : Term} {substitution : Substitution} {source target : GroundTerm}
    (shape : (program[occurrence]?).bind equationSides? = some (left, right))
    (valid : substitutionValid substitution = true)
    (input : instantiateTerm substitution left = some source)
    (output : instantiateTerm substitution right = some target) :
    StepAt program occurrence [] source target := by
  cases selected : program[occurrence]? with
  | none => simp [selected] at shape
  | some rule =>
    exact .root selected (by simpa [selected] using shape) valid input output

theorem append_source_path {program : Program} {emptyOccurrence consOccurrence : Nat}
    (emptySource : (program[emptyOccurrence]?).bind equationSides? = some emptyShape)
    (consSource : (program[consOccurrence]?).bind equationSides? = some consShape)
    (left right : List Char) :
    Path program (appendActions emptyOccurrence consOccurrence left.length)
      (appendCall left right) (encodeText (left ++ right)) := by
  induction left with
  | nil =>
    have step : StepAt program emptyOccurrence [] (appendCall [] right) (encodeText right) :=
      source_root emptySource (substitution := [(0, encodeText right)])
        (by rfl) (by rfl) (by rfl)
    exact .cons step (.nil _)
  | cons character rest ih =>
    have contextual := ih.context "bnf-v1:text-cons" [.integer character.toNat] []
    have step := source_root consSource
      (substitution := [(0, .integer character.toNat), (1, encodeText rest),
        (2, encodeText right)]) (by rfl)
      (source := appendCall (character :: rest) right)
      (target := .app "bnf-v1:text-cons"
        (.cons (.integer character.toNat) (.cons (appendCall rest right) .nil)))
      (by rfl) (by rfl)
    simpa [appendActions, encodeText, GroundTerms.ofList] using Path.cons step contextual

private theorem appendActions_range_safe {program : Program}
    {emptyOccurrence consOccurrence : Nat}
    (emptySource : (program[emptyOccurrence]?).bind equationSides? = some emptyShape)
    (consSource : (program[consOccurrence]?).bind equationSides? = some consShape)
    (count : Nat) :
    ∀ action ∈ appendActions emptyOccurrence consOccurrence count,
      OccurrenceRangeSafe program action.occurrence := by
  have emptySafe : OccurrenceRangeSafe program emptyOccurrence :=
    occurrenceRangeSafe_of_shape emptySource (by
      intro identifier occurs
      simpa [emptyShape, HornSpecialization.termVariables, HornSpecialization.termsVariables]
        using occurs)
  have consSafe : OccurrenceRangeSafe program consOccurrence :=
    occurrenceRangeSafe_of_shape consSource (by
      intro identifier occurs
      simpa [consShape, HornSpecialization.termVariables, HornSpecialization.termsVariables]
        using occurs)
  intro action member
  have used := List.mem_map_of_mem (f := Action.occurrence) member
  rw [appendActions_occurrences] at used
  simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at used
  rcases used with ⟨_, equal⟩ | equal
  · simpa [equal] using consSafe
  · simpa [equal] using emptySafe

/-- The actual generic checker executes the same recursive path. Only the
two used source occurrences need to have the checked shapes. -/
theorem append_replay {program : Program}
    {emptyOccurrence consOccurrence : Nat}
    (emptySource : (program[emptyOccurrence]?).bind equationSides? = some emptyShape)
    (consSource : (program[consOccurrence]?).bind equationSides? = some consShape)
    (left right : List Char) :
    replayPath program (appendActions emptyOccurrence consOccurrence left.length)
      (appendCall left right) = some (encodeText (left ++ right)) :=
  replayPath_complete_on (append_source_path emptySource consSource left right)
    (appendActions_range_safe emptySource consSource left.length)

/-- No different result is authorized along the retained recursive route.
This does not assert confluence of arbitrary source reductions. -/
theorem append_path_iff {program : Program}
    {emptyOccurrence consOccurrence : Nat}
    (emptySource : (program[emptyOccurrence]?).bind equationSides? = some emptyShape)
    (consSource : (program[consOccurrence]?).bind equationSides? = some consShape)
    (left right : List Char) (result : GroundTerm) :
    Path program (appendActions emptyOccurrence consOccurrence left.length)
      (appendCall left right) result ↔ result = encodeText (left ++ right) := by
  constructor
  · intro path
    have replayed := replayPath_complete_on path
      (appendActions_range_safe emptySource consSource left.length)
    rw [append_replay emptySource consSource left right] at replayed
    exact (Option.some.inj replayed).symm
  · intro equal
    subst result
    exact append_source_path emptySource consSource left right

theorem duplicate_characters_are_retained :
    encodeText ['a', 'a'] ≠ encodeText ['a'] := by decide

theorem zero_scalar_is_representable :
    encodeText [Char.ofNat 0] = .app "bnf-v1:text-cons"
      (.cons (.integer 0) (.cons (.app "bnf-v1:text-nil" .nil) .nil)) := by decide

#print axioms append_source_path
#print axioms append_replay
#print axioms append_path_iff

end Mettapedia.GSLT.Parsing.PlainBnfSourceTextAppend
