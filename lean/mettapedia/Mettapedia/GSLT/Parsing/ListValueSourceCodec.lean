import Mettapedia.Logic.Unification.ListSpliceTerms

/-!
# Structural list/expression tokens and profile dispatch

The bracket codec starts after lexical analysis. Atom and variable payloads are
already classified lexical values; no assumption about an opaque text parser is
used. The concrete stack reader checks every delimiter and preserves every
payload. The raw syntax codec includes a standalone rest marker and keeps its
prefix and tail separate. Applying the independently specified splice normalizer
after reading gives the semantic list value without confusing it with syntax.

The final section models the native reader's ordered scalar dispatch separately
from the structural codec. Disabling the list branch preserves base dispatch;
absence of list-delimiter tokens preserves the entire stack computation. Neither
theorem claims correspondence with generated native code, UTF-8 decoding, string
escaping, or every rule of the HE, PeTTa, and Prime lexical presentations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ListValueSourceCodec

open Mettapedia.Logic.Unification.ListSplice

inductive Token (Leaf Var : Type) where
  | atom : Leaf → Token Leaf Var
  | variable : Var → Token Leaf Var
  | openExpr | closeExpr | openList | closeList | restMarker
  deriving Repr

inductive FrameKind where
  | expr | list
  deriving DecidableEq, Repr

variable {Leaf Var : Type}

structure State (Leaf Var : Type) where
  frames : List (FrameKind × List (Term Leaf Var) × Option (List (Term Leaf Var)))
  reverseValues : List (Term Leaf Var)
  restPrefix : Option (List (Term Leaf Var))

def initial : State Leaf Var := ⟨[], [], none⟩

def push (value : Term Leaf Var) (state : State Leaf Var) : State Leaf Var :=
  { state with reverseValues := value :: state.reverseValues }

def pushMany (values : List (Term Leaf Var)) (state : State Leaf Var) :
    State Leaf Var :=
  { state with reverseValues := values.reverse ++ state.reverseValues }

def openFrame (kind : FrameKind) (state : State Leaf Var) : State Leaf Var :=
  ⟨(kind, state.reverseValues, state.restPrefix) :: state.frames, [], none⟩

def markRest (state : State Leaf Var) : State Leaf Var :=
  { state with reverseValues := [], restPrefix := some state.reverseValues }

def finishValue (kind : FrameKind) (state : State Leaf Var) : Option (Term Leaf Var) :=
  match kind, state.restPrefix, state.reverseValues with
  | .expr, none, values => some (.expr values.reverse)
  | .list, none, values => some (.list values.reverse)
  | .list, some front, [tail] => some (.rest front.reverse tail)
  | _, _, _ => none

def closeFrame (kind : FrameKind) (state : State Leaf Var) :
    Option (State Leaf Var) :=
  match state.frames with
  | [] => none
  | (stored, values, front) :: rest =>
    if stored = kind then do
      let value ← finishValue kind state
      some ⟨rest, value :: values, front⟩
    else none

def step (listsEnabled : Bool) (state : State Leaf Var) :
    Token Leaf Var → Option (State Leaf Var)
  | .atom value => some (push (.atom value) state)
  | .variable name => some (push (.var name) state)
  | .openExpr => some (openFrame .expr state)
  | .closeExpr => closeFrame .expr state
  | .openList => if listsEnabled then some (openFrame .list state) else none
  | .closeList => if listsEnabled then closeFrame .list state else none
  | .restMarker =>
    if listsEnabled then
      match state.frames, state.restPrefix with
      | (.list, _, _) :: _, none => some (markRest state)
      | _, _ => none
    else none

/-- A terminating, fault-producing stack computation on the actual token list. -/
def run (listsEnabled : Bool) (state : State Leaf Var) :
    List (Token Leaf Var) → Option (State Leaf Var)
  | [] => some state
  | token :: tokens => do
    run listsEnabled (← step listsEnabled state token) tokens

theorem run_append (listsEnabled : Bool) (state : State Leaf Var)
    (first second : List (Token Leaf Var)) :
    run listsEnabled state (first ++ second) =
      (run listsEnabled state first >>= fun middle => run listsEnabled middle second) := by
  induction first generalizing state with
  | nil => rfl
  | cons token tokens ih =>
    simp only [List.cons_append, run]
    cases step listsEnabled state token <;> simp [ih]

def readMany? (listsEnabled : Bool) (tokens : List (Token Leaf Var)) :
    Option (List (Term Leaf Var)) := do
  let state ← run listsEnabled initial tokens
  match state.frames, state.restPrefix with
  | [], none => some state.reverseValues.reverse
  | _, _ => none

def readOne? (listsEnabled : Bool) (tokens : List (Token Leaf Var)) :
    Option (Term Leaf Var) := do
  match ← readMany? listsEnabled tokens with
  | [value] => some value
  | _ => none

mutual
  def printTokens? : Term Leaf Var → Option (List (Token Leaf Var))
    | .atom value => some [.atom value]
    | .var name => some [.variable name]
    | .expr values => do
      return .openExpr :: (← printManyTokens? values) ++ [.closeExpr]
    | .list values => do
      return .openList :: (← printManyTokens? values) ++ [.closeList]
    | .rest values tail => do
      return .openList :: (← printManyTokens? values) ++
        [.restMarker] ++ (← printTokens? tail) ++ [.closeList]

  def printManyTokens? : List (Term Leaf Var) → Option (List (Token Leaf Var))
    | [] => some []
    | value :: values => do
      return (← printTokens? value) ++ (← printManyTokens? values)
end

mutual
  theorem printTokens_total (value : Term Leaf Var) :
      ∃ tokens, printTokens? value = some tokens := by
    cases value with
    | atom value => exact ⟨[.atom value], rfl⟩
    | var name => exact ⟨[.variable name], rfl⟩
    | expr values =>
      obtain ⟨body, children⟩ := printManyTokens_total values
      exact ⟨.openExpr :: body ++ [.closeExpr], by simp [printTokens?, children]⟩
    | list values =>
      obtain ⟨body, children⟩ := printManyTokens_total values
      exact ⟨.openList :: body ++ [.closeList], by simp [printTokens?, children]⟩
    | rest values tail =>
      obtain ⟨body, children⟩ := printManyTokens_total values
      obtain ⟨tailTokens, tailPrinted⟩ := printTokens_total tail
      exact ⟨.openList :: body ++ [.restMarker] ++ tailTokens ++ [.closeList],
        by simp [printTokens?, children, tailPrinted]⟩
  termination_by sizeOf value

  theorem printManyTokens_total (values : List (Term Leaf Var)) :
      ∃ tokens, printManyTokens? values = some tokens := by
    cases values with
    | nil => exact ⟨[], rfl⟩
    | cons value values =>
      obtain ⟨headTokens, headPrinted⟩ := printTokens_total value
      obtain ⟨tailTokens, tailPrinted⟩ := printManyTokens_total values
      exact ⟨headTokens ++ tailTokens, by simp [printManyTokens?, headPrinted, tailPrinted]⟩
  termination_by sizeOf values
end

@[simp] theorem pushMany_nil (state : State Leaf Var) : pushMany [] state = state := by
  cases state
  rfl

theorem pushMany_cons (value : Term Leaf Var) (values : List (Term Leaf Var))
    (state : State Leaf Var) :
    pushMany (value :: values) state = pushMany values (push value state) := by
  simp [pushMany, push, List.reverse_cons, List.append_assoc]

@[simp] theorem close_open_expr (values : List (Term Leaf Var))
    (state : State Leaf Var) :
    closeFrame .expr (pushMany values (openFrame .expr state)) =
      some (push (.expr values) state) := by
  simp [closeFrame, finishValue, pushMany, openFrame, push]

@[simp] theorem close_open_list (values : List (Term Leaf Var))
    (state : State Leaf Var) :
    closeFrame .list (pushMany values (openFrame .list state)) =
      some (push (.list values) state) := by
  simp [closeFrame, finishValue, pushMany, openFrame, push]

@[simp] theorem rest_after_prefix (values : List (Term Leaf Var))
    (state : State Leaf Var) :
    step true (pushMany values (openFrame .list state)) .restMarker =
      some (markRest (pushMany values (openFrame .list state))) := rfl

@[simp] theorem close_open_rest (values : List (Term Leaf Var))
    (tail : Term Leaf Var) (state : State Leaf Var) :
    closeFrame .list (push tail (markRest (pushMany values (openFrame .list state)))) =
      some (push (.rest values tail) state) := by
  simp [closeFrame, finishValue, pushMany, openFrame, markRest, push]

mutual
  /-- Reading printed tokens works in every surrounding parser state. -/
  theorem run_printTokens (value : Term Leaf Var) (tokens : List (Token Leaf Var))
      (printed : printTokens? value = some tokens) (state : State Leaf Var) :
      run true state tokens = some (push value state) := by
    cases value with
    | atom value => cases printed; rfl
    | var name => cases printed; rfl
    | rest values tail =>
      cases children : printManyTokens? values with
      | none => simp [printTokens?, children] at printed
      | some body =>
        cases tailPrinted : printTokens? tail with
        | none => simp [printTokens?, children, tailPrinted] at printed
        | some tailTokens =>
          simp [printTokens?, children, tailPrinted] at printed
          subst tokens
          simp only [run, step, bind, Option.bind, ↓reduceIte]
          rw [run_append, run_printManyTokens values body children]
          simp only [bind, Option.bind, run, rest_after_prefix]
          rw [run_append, run_printTokens tail tailTokens tailPrinted]
          simp [run, step]
    | expr values =>
      cases children : printManyTokens? values with
      | none => simp [printTokens?, children] at printed
      | some body =>
        simp [printTokens?, children] at printed
        subst tokens
        simp only [run, step, bind, Option.bind]
        rw [run_append, run_printManyTokens values body children]
        simp [run, step]
    | list values =>
      cases children : printManyTokens? values with
      | none => simp [printTokens?, children] at printed
      | some body =>
        simp [printTokens?, children] at printed
        subst tokens
        simp only [run, step, bind, Option.bind, ↓reduceIte]
        rw [run_append, run_printManyTokens values body children]
        simp [run, step]
  termination_by sizeOf value

  theorem run_printManyTokens (values : List (Term Leaf Var))
      (tokens : List (Token Leaf Var)) (printed : printManyTokens? values = some tokens)
      (state : State Leaf Var) :
      run true state tokens = some (pushMany values state) := by
    cases values with
    | nil => cases printed; simp [run]
    | cons value values =>
      cases head : printTokens? value with
      | none => simp [printManyTokens?, head] at printed
      | some headTokens =>
        cases tail : printManyTokens? values with
        | none => simp [printManyTokens?, head, tail] at printed
        | some tailTokens =>
          simp [printManyTokens?, head, tail] at printed
          subst tokens
          rw [run_append, run_printTokens value headTokens head]
          simpa [pushMany_cons] using run_printManyTokens values tailTokens tail
            (push value state)
  termination_by sizeOf values
end

theorem readMany_printMany (values : List (Term Leaf Var))
    (tokens : List (Token Leaf Var)) (printed : printManyTokens? values = some tokens) :
    readMany? true tokens = some values := by
  simp [readMany?, run_printManyTokens values tokens printed, pushMany, initial]

theorem readOne_print (value : Term Leaf Var) (tokens : List (Token Leaf Var))
    (printed : printTokens? value = some tokens) :
    readOne? true tokens = some value := by
  simp [readOne?, readMany?, run_printTokens value tokens printed, push, initial]

/-- No printability assumption is required: every raw term has a token round trip. -/
theorem raw_round_trip (value : Term Leaf Var) :
    (printTokens? value >>= readOne? true) = some value := by
  obtain ⟨tokens, printed⟩ := printTokens_total value
  simp [printed, readOne_print value tokens printed]

/-- Successful token spellings cannot identify two distinct values. -/
theorem printTokens_injective_on_domain (left right : Term Leaf Var)
    (tokens : List (Token Leaf Var))
    (leftPrinted : printTokens? left = some tokens)
    (rightPrinted : printTokens? right = some tokens) : left = right := by
  have leftRead := readOne_print left tokens leftPrinted
  have rightRead := readOne_print right tokens rightPrinted
  rw [leftRead] at rightRead
  exact Option.some.inj rightRead

def BaseToken : Token Leaf Var → Prop
  | .openList | .closeList | .restMarker => False
  | _ => True

theorem step_base_token (state : State Leaf Var) (token : Token Leaf Var)
    (base : BaseToken token) : step true state token = step false state token := by
  cases token <;> simp_all [BaseToken, step]

/-- Actual parser computations agree on the shared token alphabet, including faults. -/
theorem run_base_tokens (state : State Leaf Var) (tokens : List (Token Leaf Var))
    (base : ∀ token ∈ tokens, BaseToken token) :
    run true state tokens = run false state tokens := by
  induction tokens generalizing state with
  | nil => rfl
  | cons token tokens ih =>
    simp only [run]
    rw [step_base_token state token (base token (by simp))]
    cases step false state token <;>
      simp [ih _ (fun item member => base item (by simp [member]))]

theorem readMany_base_tokens (tokens : List (Token Leaf Var))
    (base : ∀ token ∈ tokens, BaseToken token) :
    readMany? true tokens = readMany? false tokens := by
  unfold readMany?
  rw [run_base_tokens initial tokens base]

theorem literal_brackets_remain_payload (spelling : Leaf) :
    readOne? false ([.atom spelling] : List (Token Leaf Var)) =
      some (.atom spelling) := rfl

theorem base_list_delimiters_rejected :
    readOne? false ([.openList, .closeList] : List (Token Leaf Var)) = none := rfl

theorem empty_list_distinct_from_no_answers :
    readMany? true ([.openList, .closeList] : List (Token Leaf Var)) =
      some [.list []] ∧
    readMany? true ([] : List (Token Leaf Var)) = some [] := ⟨rfl, rfl⟩

theorem mismatched_delimiters_rejected :
    readMany? true ([.openExpr, .closeList] : List (Token Leaf Var)) = none ∧
    readMany? true ([.openList, .closeExpr] : List (Token Leaf Var)) = none :=
  ⟨rfl, rfl⟩

theorem incomplete_list_rejected :
    readMany? true ([.openList] : List (Token Leaf Var)) = none := rfl

theorem rest_without_tail_rejected :
    readMany? true ([.openList, .restMarker, .closeList] :
      List (Token Leaf Var)) = none := rfl

theorem rest_with_two_tails_rejected (first second : Leaf) :
    readMany? true ([.openList, .restMarker, .atom first, .atom second, .closeList] :
      List (Token Leaf Var)) = none := rfl

theorem expression_rest_rejected :
    readMany? true ([.openExpr, .restMarker, .closeExpr] :
      List (Token Leaf Var)) = none := rfl

def readNormalized? (listsEnabled : Bool) (tokens : List (Token Leaf Var)) :
    Option (Term Leaf Var) := normalize <$> readOne? listsEnabled tokens

/-- The semantic reader performs exactly the separately proved splice normalization. -/
theorem readNormalized_print (value : Term Leaf Var) (tokens : List (Token Leaf Var))
    (printed : printTokens? value = some tokens) :
    readNormalized? true tokens = some (normalize value) := by
  simp [readNormalized?, readOne_print value tokens printed]

theorem normalized_round_trip (value : Term Leaf Var) :
    (printTokens? value >>= readNormalized? true) = some (normalize value) := by
  obtain ⟨tokens, printed⟩ := printTokens_total value
  simp [printed, readNormalized_print value tokens printed]

/-- Nested rest syntax retains its raw tree, then splices in the semantic view. -/
example : readNormalized? true
    ([.openList, .atom 1, .restMarker, .openList, .atom 2, .closeList, .closeList] :
      List (Token Nat String)) = some (.list [.atom 1, .atom 2]) := by
  change some (normalize (Term.rest [.atom 1] (.list [.atom 2]))) = _
  simp [normalize, splice]

example : readOne? true
    ([.openList, .atom 1, .restMarker, .variable "xs", .closeList] :
      List (Token Nat String)) = some (.rest [.atom 1] (.var "xs")) := rfl

example : readNormalized? true
    ([.openList, .restMarker, .variable "xs", .closeList] :
      List (Token Nat String)) = some (.var "xs") := by
  change some (normalize (Term.rest [] (.var "xs"))) = _
  simp [normalize]

/-! ## Ordered scalar dispatch of the native reader -/

inductive Branch where
  | string | variable | expression | list | word | invalid
  deriving DecidableEq, Repr

structure DispatchPlan where
  stringOpen : Nat
  variableMarker : Nat
  expressionOpen : Nat
  listOpen : Nat
  wordStart : Nat → Bool

def baseDispatch (plan : DispatchPlan) (scalar : Nat) : Branch :=
  if scalar = plan.stringOpen then .string
  else if scalar = plan.variableMarker then .variable
  else if scalar = plan.expressionOpen then .expression
  else if plan.wordStart scalar then .word
  else .invalid

def dispatch (listsEnabled : Bool) (plan : DispatchPlan) (scalar : Nat) : Branch :=
  if scalar = plan.stringOpen then .string
  else if scalar = plan.variableMarker then .variable
  else if scalar = plan.expressionOpen then .expression
  else if listsEnabled && plan.listOpen != 0 && scalar == plan.listOpen then .list
  else if plan.wordStart scalar then .word
  else .invalid

theorem disabled_dispatch_conservative (plan : DispatchPlan) (scalar : Nat) :
    dispatch false plan scalar = baseDispatch plan scalar := by
  simp [dispatch, baseDispatch]

theorem non_list_start_dispatch_conservative (plan : DispatchPlan) (scalar : Nat)
    (notList : scalar ≠ plan.listOpen) :
    dispatch true plan scalar = baseDispatch plan scalar := by
  simp [dispatch, baseDispatch, notList]

theorem zero_list_open_dispatch_conservative (plan : DispatchPlan) (scalar : Nat)
    (disabled : plan.listOpen = 0) :
    dispatch true plan scalar = baseDispatch plan scalar := by
  simp [dispatch, baseDispatch, disabled]

/-- This plan fixes only the relevant punctuation and delegates word classification. -/
def mettaPunctuation (wordStart : Nat → Bool) : DispatchPlan :=
  ⟨34, 36, 40, 91, wordStart⟩

theorem bracket_profile_boundary (wordStart : Nat → Bool)
    (bracketIsWord : wordStart 91 = true) :
    dispatch false (mettaPunctuation wordStart) 91 = .word ∧
    dispatch true (mettaPunctuation wordStart) 91 = .list := by
  simp [dispatch, mettaPunctuation, bracketIsWord]

#print axioms run_printTokens
#print axioms readOne_print
#print axioms normalized_round_trip
#print axioms run_base_tokens
#print axioms disabled_dispatch_conservative

end Mettapedia.GSLT.Parsing.ListValueSourceCodec
