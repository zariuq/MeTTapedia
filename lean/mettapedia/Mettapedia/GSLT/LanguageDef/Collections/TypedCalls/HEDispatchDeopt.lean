import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEExpressionBoundary

/-!
# Per-call deoptimization at HE's dispatch step

A typed HE call `(f a₁ … aₙ)` whose head has one declared function type runs
in three stages (`interpret_expression`, `interpret_args`, `metta_call` in
hyperon-experimental's interpreter):

1. **Applicability** is decided on the argument *expressions*
   (`checkIfFunctionTypeIsApplicable`), giving binding records `bs`.
2. **Arguments** are evaluated, each at its formal (`interpretArgs`). A reply
   that is the argument packet becomes the call with evaluated arguments; an
   `Empty` or `Error` reply that differs from the argument expression is
   delivered as it is.
3. **Delivery**: each such reply is invoked at the instantiated range
   (`invoke … (.ordinary R)`), and the call node keeps the successes of the
   whole batch, or its errors when there is no success (`HEReturns.keep`).

`strict_call` states this factorization of the interpreter for any number of
arguments; `strict_call_one` specializes it to one argument, where the second
stage is the argument's own evaluation at its formal. Where the argument is
read without a cast at its formal (`HEReturns.Reads` with the readings `none`
or `neutral`), that evaluation is the argument's evaluation at `%Undefined%`,
which is what an untyped shared machine computes (`machine_arguments`).

The expected type of the call reaches its answers only through the
applicability check: where that check gives the same records at `E` as at
`%Undefined%`, the call evaluates at `E` as at `%Undefined%`
(`strict_call_expected`).

**The deoptimization boundary** is the third stage. Replacing the delivery by
a prepared implementation that, where it answers, answers what the delivery
answers, and otherwise falls back to the delivery itself, leaves the call's
answers unchanged, multiplicity and order included (`tiered_delivery`). The
fallback starts at the delivery: evaluating the whole call again would repeat
stage 1 on the values instead of the expressions.

**The batch selection** is not per alternative. Keeping per alternative and
concatenating differs from keeping the batch
(`Controls.per_alternative_selection_differs`), so delivered outcomes cannot
be streamed into a shared machine one alternative at a time unless the call
node keeps a frontier: successes may be published as they arrive, since
those published from any prefix are a prefix of the final answers
(`keepBy_prefix`); errors wait until the batch closes, since an error
published early can be retracted by a later success
(`Controls.early_error_retracted`). The streaming procedure that publishes
successes at once and holds errors to the close is the selection
(`stream_eq_keepBy`, `stream_eq_keep`). Where no reply can be an error, the
selection is the identity and no frontier is needed (`HEReturns.keep_clean`).

The C frontier (`he_canonical_frontier_publish`) also holds `Empty` and drops
it at the close when the batch has any other outcome (`frontierKeep`). The
model's `keep` treats an `Empty` reply as a success; the two differ on a batch
of `Empty` and an error (`Controls.empty_against_error`). Hyperon-experimental
answers the error there.

**Literal `Empty` arguments are packed.** An argument expression that is
itself `Empty` evaluates to itself, so the second stage does not pass it
through: the call is made with `Empty` as an argument
(`literal_empty_packed`). Hyperon-experimental answers `(* Empty Empty)` for
`(sq Empty)` with `sq : (-> Number Number)` and `(= (sq $x) (* $x $x))`. A
machine that drops `Empty` alternatives must leave such a call to the
canonical evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDispatchDeopt

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open HEReturns

/-! ## Stage 2 to stage 3: the delivered call -/

/-- What stage 2 hands to the delivery: the call with evaluated arguments for
an argument packet, and any other reply (an `Empty` or `Error` result) as it
is. -/
def delivered (head : String) (reply : Atom) : Atom :=
  if argumentsSucceeded reply then .expression (.symbol head :: argumentValues reply) else reply

theorem argumentsSucceeded_of_emptyOrError {v : Atom} (failed : isEmptyOrError v = true) :
    argumentsSucceeded v = false := by
  unfold isEmptyOrError isEmptyAtom isErrorAtom at failed
  unfold argumentsSucceeded unpackArguments
  rcases v with _ | _ | _ | items
  · simp
  · simp
  · simp
  · rcases items with _ | ⟨first, rest⟩
    · simp
    · rcases rest with _ | ⟨second, rest⟩
      · cases first <;> simp
      · rcases rest with _ | ⟨third, rest⟩
        · cases first with
          | symbol tag =>
              cases second with
              | expression args =>
                  by_cases ok : tag = "Ok"
                  · subst ok; simp [Atom.empty] at failed
                  · simp [ok]
              | _ => simp
          | _ => simp
        · cases first <;> simp

theorem delivered_packet (head : String) (values : List Atom) :
    delivered head (argumentPacket values) = .expression (.symbol head :: values) := by
  simp [delivered]

theorem delivered_failed (head : String) {v : Atom} (failed : isEmptyOrError v = true) :
    delivered head v = v := by
  simp [delivered, argumentsSucceeded_of_emptyOrError failed]

/-- The function stage of a typed head: the head evaluates to itself under its
declared arrow, and the argument replies are delivered. -/
theorem interpretFunction_delivered {space : Space} {dispatch : GroundedDispatch}
    {head : String} {params args : List Atom} {range : Atom} {others : List Atom}
    (declared : getAtomTypes space (.symbol head) = arrowType params range :: others)
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") (bindings : Bindings) {fuel : Nat}
    (enough : matchFuel (arrowType params range) ≤ fuel) (live : List Atom) :
    interpretFunction space dispatch (.expression (.symbol head :: args)) (arrowType params range)
      bindings (fuel + 2) live =
      (interpretArgs space dispatch args params bindings (fuel + 1) (.symbol head :: live)).map
        fun reply => (delivered head reply.1, reply.2) := by
  rw [interpretFunction, evalAtom_head declared ground notEmpty bindings enough]
  simp only [isEmptyOrError_symbol notEmpty, Bool.false_eq_true, if_false,
    getFunctionArgTypes_arrowType, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  apply List.map_congr_left
  intro reply _
  by_cases ok : argumentsSucceeded reply.1 = true
  · simp [delivered, ok]
  · simp [delivered, ok]

/-! ## The factorization of a strict typed call -/

/-- **Stages 1 to 3, for any number of arguments.** A head with one declared
ground arrow, whose applicability check on the argument expressions gives the
records `bs`: the interpretation of the call is, for each record, the
argument replies, each delivered and invoked at the range. -/
theorem interpretExpression_strict {space : Space} {dispatch : GroundedDispatch}
    {head : String} {params args : List Atom} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") {bindings : Bindings} {bs : List Bindings} {fuel : Nat}
    (applicable : checkIfFunctionTypeIsApplicable (.expression (.symbol head :: args))
      (arrowType params range) expected space bindings (fuel + 2) = .inr bs)
    (enough : matchFuel (arrowType params range) ≤ fuel) (live : List Atom) :
    interpretExpression space dispatch (.expression (.symbol head :: args)) expected bindings
      (fuel + 3) live =
      bs.flatMap fun b =>
        (interpretArgs space dispatch args params b (fuel + 1)
            (.symbol head :: callReturnType range :: live)).flatMap fun reply =>
          invoke space dispatch (.ordinary (callReturnType range)) (delivered head reply.1)
            reply.2 (fuel + 2) live := by
  have first : getAtomTypes space (.symbol head) = arrowType params range :: [] := declared
  rw [interpretExpression]
  simp only [declared, isFunctionType_arrowType, if_true, applicable,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, callReturnType_arrowType]
  have nonFunction : ([arrowType params range].any fun type =>
      !isFunctionType type || type == Atom.undefinedType) = false := by
    simp [isFunctionType_arrowType, arrowType_beq_symbol, Atom.undefinedType]
  simp only [nonFunction, Bool.false_eq_true, if_false, List.append_nil]
  have body : (bs.flatMap fun b =>
      (interpretFunction space dispatch (.expression (.symbol head :: args))
        (arrowType params range) b (fuel + 2) (callReturnType range :: live)).flatMap fun r =>
          invoke space dispatch (.ordinary (callReturnType range)) r.1 r.2 (fuel + 2) live) =
      bs.flatMap fun b =>
        (interpretArgs space dispatch args params b (fuel + 1)
            (.symbol head :: callReturnType range :: live)).flatMap fun reply =>
          invoke space dispatch (.ordinary (callReturnType range)) (delivered head reply.1)
            reply.2 (fuel + 2) live := by
    apply List.flatMap_congr
    intro b _
    rw [interpretFunction_delivered first ground notEmpty b enough, List.flatMap_map]
  rw [body]
  cases (bs.flatMap fun b =>
      (interpretArgs space dispatch args params b (fuel + 1)
          (.symbol head :: callReturnType range :: live)).flatMap fun reply =>
        invoke space dispatch (.ordinary (callReturnType range)) (delivered head reply.1)
          reply.2 (fuel + 2) live) with
  | cons _ _ => simp
  | nil => simp [isFunctionType_arrowType, applicable]

/-- **The strict call, at the evaluator.** The evaluator keeps the successes of
the whole batch of delivered answers, or its errors when there is none. -/
theorem strict_call {space : Space} {dispatch : GroundedDispatch}
    {head : String} {params args : List Atom} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    {bindings : Bindings} {bs : List Bindings} {fuel : Nat}
    (applicable : checkIfFunctionTypeIsApplicable (.expression (.symbol head :: args))
      (arrowType params range) expected space bindings (fuel + 2) = .inr bs)
    (enough : matchFuel (arrowType params range) ≤ fuel) (live : List Atom) :
    evalAtom space dispatch (.expression (.symbol head :: args)) expected bindings (fuel + 4) live =
      keep (bs.flatMap fun b =>
        (interpretArgs space dispatch args params b (fuel + 1)
            (.symbol head :: callReturnType range :: live)).flatMap fun reply =>
          invoke space dispatch (.ordinary (callReturnType range)) (delivered head reply.1)
            reply.2 (fuel + 2) live) := by
  rw [evalAtom_expression (isEmptyOrError_call notError args) notAtom notExpression,
    interpretExpression_strict declared ground notEmpty applicable enough]

/-- **The expected type of a strict call matters only through applicability.**
Where the applicability check gives the same records at the expected type
`E` as at `%Undefined%`, as it does when `E` accepts a closed range, the call
evaluates at `E` as at `%Undefined%`: a typed head nested at a typed
parameter, such as `(+ 0 (sum xs))`, runs as at top level. -/
theorem strict_call_expected {space : Space} {dispatch : GroundedDispatch}
    {head : String} {params args : List Atom} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    {bindings : Bindings} {bs : List Bindings} {fuel : Nat}
    (applicable : checkIfFunctionTypeIsApplicable (.expression (.symbol head :: args))
      (arrowType params range) expected space bindings (fuel + 2) = .inr bs)
    (applicableUndefined : checkIfFunctionTypeIsApplicable (.expression (.symbol head :: args))
      (arrowType params range) Atom.undefinedType space bindings (fuel + 2) = .inr bs)
    (enough : matchFuel (arrowType params range) ≤ fuel) (live : List Atom) :
    evalAtom space dispatch (.expression (.symbol head :: args)) expected bindings (fuel + 4) live =
      evalAtom space dispatch (.expression (.symbol head :: args)) Atom.undefinedType bindings
        (fuel + 4) live := by
  rw [strict_call declared ground notEmpty notError notAtom notExpression applicable enough,
    strict_call declared ground notEmpty notError (by simp [Atom.undefinedType, Atom.atomType])
      (by simp [Atom.undefinedType, Atom.expressionType]) applicableUndefined enough]

/-! ## One argument: stage 2 is the argument's evaluation -/

/-- One argument at its formal: each evaluation answer is packed, except an
`Empty` or `Error` answer that differs from the argument expression, which
is passed through. -/
theorem interpretArgs_one {space : Space} {dispatch : GroundedDispatch} (arg param : Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    interpretArgs space dispatch [arg] [param] bindings (fuel + 2) live =
      (evalAtom space dispatch arg param bindings (fuel + 1) live).map fun answer =>
        if (answer.1 != arg && isEmptyOrError answer.1) = true then answer
        else (argumentPacket [answer.1], answer.2) := by
  rw [interpretArgs]
  simp only [List.nil_append]
  rw [List.map_eq_flatMap]
  apply List.flatMap_congr
  intro answer _
  obtain ⟨v, vb⟩ := answer
  by_cases pass : (v != arg && isEmptyOrError v) = true
  · simp [pass]
  · simp only [pass, Bool.false_eq_true, if_false]
    rw [interpretArgs]
    simp

/-- **The strict call with one argument.** -/
theorem strict_call_one {space : Space} {dispatch : GroundedDispatch}
    {head : String} {param arg range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType [param] range])
    (ground : atomVariables (arrowType [param] range) = [])
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    {bindings : Bindings} {bs : List Bindings} {fuel : Nat}
    (applicable : checkIfFunctionTypeIsApplicable (.expression [.symbol head, arg])
      (arrowType [param] range) expected space bindings (fuel + 3) = .inr bs)
    (enough : matchFuel (arrowType [param] range) ≤ fuel + 1) (live : List Atom) :
    evalAtom space dispatch (.expression [.symbol head, arg]) expected bindings (fuel + 5) live =
      keep (bs.flatMap fun b =>
        (evalAtom space dispatch arg param b (fuel + 1)
            (.symbol head :: callReturnType range :: live)).flatMap fun answer =>
          invoke space dispatch (.ordinary (callReturnType range))
            (if (answer.1 != arg && isEmptyOrError answer.1) = true then answer.1
              else .expression [.symbol head, answer.1])
            answer.2 (fuel + 3) live) := by
  rw [strict_call declared ground notEmpty notError notAtom notExpression applicable enough]
  congr 1
  apply List.flatMap_congr
  intro b _
  rw [interpretArgs_one, List.flatMap_map]
  apply List.flatMap_congr
  intro answer _
  by_cases pass : (answer.1 != arg && isEmptyOrError answer.1) = true
  · have failed : isEmptyOrError answer.1 = true := by
      simp only [Bool.and_eq_true] at pass
      exact pass.2
    simp [pass, delivered_failed head failed]
  · simp [pass, delivered_packet]

/-- **What an untyped machine computes is stage 2.** Where the argument is read
at its formal (a value class) without a cast, its evaluation at the formal is
its evaluation at `%Undefined%`. -/
theorem machine_argument {space : Space} {dispatch : GroundedDispatch} {param arg : Atom}
    (formal : ValueClass param) {reading : Cast}
    (uncast : reading = .none ∨ reading = .neutral)
    {b : Bindings} {fuel : Nat} {live : List Atom}
    (reads : Reads space dispatch param reading arg b fuel live) :
    evalAtom space dispatch arg param b fuel live =
      evalAtom space dispatch arg Atom.undefinedType b fuel live := by
  rw [Reads.sound formal reads]
  rcases uncast with rfl | rfl <;> rfl

/-- **The strict call over the machine's argument evaluation.** With the
argument read without a cast at every record of the applicability check, the
call keeps the batch of its delivered answers over the argument's untyped
evaluation. -/
theorem machine_arguments {space : Space} {dispatch : GroundedDispatch}
    {head : String} {param arg range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType [param] range])
    (ground : atomVariables (arrowType [param] range) = [])
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (formal : ValueClass param)
    {bindings : Bindings} {bs : List Bindings} {fuel : Nat}
    (applicable : checkIfFunctionTypeIsApplicable (.expression [.symbol head, arg])
      (arrowType [param] range) expected space bindings (fuel + 3) = .inr bs)
    (enough : matchFuel (arrowType [param] range) ≤ fuel + 1) (live : List Atom)
    (reading : Bindings → Cast) (uncast : ∀ b ∈ bs, reading b = .none ∨ reading b = .neutral)
    (reads : ∀ b ∈ bs, Reads space dispatch param (reading b) arg b (fuel + 1)
      (.symbol head :: callReturnType range :: live)) :
    evalAtom space dispatch (.expression [.symbol head, arg]) expected bindings (fuel + 5) live =
      keep (bs.flatMap fun b =>
        (evalAtom space dispatch arg Atom.undefinedType b (fuel + 1)
            (.symbol head :: callReturnType range :: live)).flatMap fun answer =>
          invoke space dispatch (.ordinary (callReturnType range))
            (if (answer.1 != arg && isEmptyOrError answer.1) = true then answer.1
              else .expression [.symbol head, answer.1])
            answer.2 (fuel + 3) live) := by
  rw [strict_call_one declared ground notEmpty notError notAtom notExpression applicable enough]
  congr 1
  apply List.flatMap_congr
  intro b member
  rw [machine_argument formal (uncast b member) (reads b member)]

/-! ## The deoptimization boundary is the delivery -/

/-- A prepared delivery: it answers, or declines with `none`; a decline falls
back to the canonical delivery of the same call with evaluated arguments. -/
def tiered (canonical : Atom → Bindings → ResultSet)
    (prepared : Atom → Bindings → Option ResultSet) (call : Atom) (b : Bindings) : ResultSet :=
  match prepared call b with
  | some answers => answers
  | none => canonical call b

theorem tiered_eq (canonical : Atom → Bindings → ResultSet)
    (prepared : Atom → Bindings → Option ResultSet)
    (sound : ∀ call b answers, prepared call b = some answers → answers = canonical call b)
    (call : Atom) (b : Bindings) : tiered canonical prepared call b = canonical call b := by
  unfold tiered
  cases accepted : prepared call b with
  | none => rfl
  | some answers => exact sound call b answers accepted

/-- **Per-call deoptimization at dispatch is exact.** A prepared delivery that
answers what the canonical delivery answers wherever it answers, and declines
otherwise, gives the strict call's answers, multiplicity and order included. -/
theorem tiered_delivery {space : Space} {dispatch : GroundedDispatch}
    {head : String} {params args : List Atom} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    {bindings : Bindings} {bs : List Bindings} {fuel : Nat}
    (applicable : checkIfFunctionTypeIsApplicable (.expression (.symbol head :: args))
      (arrowType params range) expected space bindings (fuel + 2) = .inr bs)
    (enough : matchFuel (arrowType params range) ≤ fuel) (live : List Atom)
    (prepared : Atom → Bindings → Option ResultSet)
    (sound : ∀ call b answers, prepared call b = some answers →
      answers = invoke space dispatch (.ordinary (callReturnType range)) call b (fuel + 2) live) :
    keep (bs.flatMap fun b =>
        (interpretArgs space dispatch args params b (fuel + 1)
            (.symbol head :: callReturnType range :: live)).flatMap fun reply =>
          tiered (fun call b => invoke space dispatch (.ordinary (callReturnType range)) call b
            (fuel + 2) live) prepared (delivered head reply.1) reply.2) =
      evalAtom space dispatch (.expression (.symbol head :: args)) expected bindings (fuel + 4)
        live := by
  rw [strict_call declared ground notEmpty notError notAtom notExpression applicable enough]
  congr 1
  apply List.flatMap_congr
  intro b _
  apply List.flatMap_congr
  intro reply _
  exact tiered_eq _ prepared sound _ _

/-! ## The call node's frontier -/

/-- Selection by a success predicate: the successes of the batch, or its other
outcomes when there is no success. -/
def keepBy (success : Atom → Bool) (results : ResultSet) : ResultSet :=
  if (results.filter fun r => success r.1).isEmpty then results.filter fun r => !success r.1
  else results.filter fun r => success r.1

theorem keep_eq_keepBy (results : ResultSet) :
    keep results = keepBy (fun a => !isErrorAtom a) results := by
  unfold keep keepBy
  by_cases empty : (results.filter fun r => !isErrorAtom r.1).isEmpty = true
  · simp [empty]
  · simp [empty]

/-- One step of the streaming procedure: a success is published, any other
outcome is held. -/
def holdStep (success : Atom → Bool) (state : ResultSet × ResultSet) (r : Atom × Bindings) :
    ResultSet × ResultSet :=
  if success r.1 then (state.1 ++ [r], state.2) else (state.1, state.2 ++ [r])

theorem holdStep_fold (success : Atom → Bool) (results : ResultSet) (published held : ResultSet) :
    results.foldl (holdStep success) (published, held) =
      (published ++ results.filter (fun r => success r.1),
        held ++ results.filter fun r => !success r.1) := by
  induction results generalizing published held with
  | nil => simp
  | cons r rest ih =>
      rw [List.foldl_cons]
      by_cases ok : success r.1 = true
      · simp [holdStep, ok, ih]
      · simp [holdStep, ok, ih]

/-- The streaming procedure: successes published as they arrive; the held
outcomes released at the close when nothing was published. -/
def stream (success : Atom → Bool) (results : ResultSet) : ResultSet :=
  let state := results.foldl (holdStep success) ([], [])
  if state.1.isEmpty then state.2 else state.1

/-- **The streaming procedure is the selection.** -/
theorem stream_eq_keepBy (success : Atom → Bool) (results : ResultSet) :
    stream success results = keepBy success results := by
  unfold stream
  simp only
  rw [holdStep_fold]
  simp [keepBy]

theorem stream_eq_keep (results : ResultSet) :
    stream (fun a => !isErrorAtom a) results = keep results := by
  rw [stream_eq_keepBy, keep_eq_keepBy]

/-- **Successes may be published as they arrive**: the successes of any prefix
of the batch are a prefix of its final answers. -/
theorem keepBy_prefix (success : Atom → Bool) (seen rest : ResultSet) :
    seen.filter (fun r => success r.1) <+: keepBy success (seen ++ rest) := by
  unfold keepBy
  by_cases none : (seen.filter fun r => success r.1) = []
  · rw [none]
    exact List.nil_prefix
  · rw [List.filter_append, List.filter_append]
    have some : ((seen.filter fun r => success r.1) ++
        rest.filter fun r => success r.1).isEmpty = false := by
      cases h : seen.filter (fun r => success r.1) with
      | nil => exact absurd h none
      | cons _ _ => rfl
    rw [some]
    exact List.prefix_append _ _

/-- The C frontier: successes are outcomes that are neither `Empty` nor an
error; without one, the errors; without an error either, the `Empty`
outcomes. -/
def frontierKeep (results : ResultSet) : ResultSet :=
  let good := results.filter fun r => !isEmptyOrError r.1
  let errors := results.filter fun r => isErrorAtom r.1
  if !good.isEmpty then good else if !errors.isEmpty then errors
  else results.filter fun r => isEmptyAtom r.1

/-- On batches without `Empty`, the C frontier is the model's selection. -/
theorem frontierKeep_eq_keep (results : ResultSet)
    (noEmpty : ∀ r ∈ results, isEmptyAtom r.1 = false) : frontierKeep results = keep results := by
  have good : (results.filter fun r => !isEmptyOrError r.1) =
      results.filter fun r => !isErrorAtom r.1 := by
    apply List.filter_congr
    intro r member
    simp [isEmptyOrError, noEmpty r member]
  have errors : (results.filter fun r => isErrorAtom r.1) =
      results.filter fun r => !!isErrorAtom r.1 := by simp
  unfold frontierKeep keep
  simp only [good]
  by_cases some : (results.filter fun r => !isErrorAtom r.1).isEmpty = true
  · have errorsAll : (results.filter fun r => isErrorAtom r.1) = results := by
      apply List.filter_eq_self.mpr
      intro r member
      have : r ∉ results.filter fun r => !isErrorAtom r.1 := by
        rw [List.isEmpty_iff.mp some]; simp
      simpa [member] using this
    have emptyAll : (results.filter fun r => isEmptyAtom r.1) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro r member
      simp [noEmpty r member]
    by_cases noResults : results = []
    · subst noResults; simp
    · have nonempty : (results.filter fun r => isErrorAtom r.1).isEmpty = false := by
        rw [errorsAll]
        cases results with
        | nil => exact absurd rfl noResults
        | cons _ _ => rfl
      simp [some, nonempty]
  · simp [some]

namespace Controls

def okReply : Atom × Bindings := (.grounded (.int 4), Bindings.empty)
def errReply : Atom × Bindings :=
  (Atom.error (.symbol "e") (.symbol "BadArgType"), Bindings.empty)
def emptyReply : Atom × Bindings := (Atom.empty, Bindings.empty)

/-- The replies of three alternatives: `1` and `4` succeed, the middle one is
an error. -/
def alternatives : List ResultSet := [[(.grounded (.int 1), Bindings.empty)], [errReply], [okReply]]

/-- **Selection per alternative differs from selection of the batch**: kept
one by one, the error survives; kept as a batch, it is dropped. -/
theorem per_alternative_selection_differs :
    (alternatives.map keep).flatten ≠ keep alternatives.flatten := by
  decide

/-- With an outer selection the inner ones do not matter (`HEReturns.flatMap_keep`). -/
theorem outer_selection_suffices :
    keep (alternatives.map keep).flatten = keep alternatives.flatten :=
  keep_flatten_keep alternatives

/-- **An error published early is retracted**: alone it is the answer, but a
later success removes it. -/
theorem early_error_retracted :
    keep [errReply] = [errReply] ∧ errReply ∉ keep [errReply, okReply] := by
  decide

/-- A success published early stays. -/
theorem early_success_stays :
    [okReply] <+: keep ([okReply] ++ [errReply]) := by
  rw [keep_eq_keepBy]
  have := keepBy_prefix (fun a => !isErrorAtom a) [okReply] [errReply]
  simpa [okReply, Atom.error, isErrorAtom] using this

/-- **`Empty` against an error**: the model's selection keeps `Empty` as a
success; the C frontier, like hyperon-experimental, answers the error. -/
theorem empty_against_error :
    keep [emptyReply, errReply] = [emptyReply] ∧
      frontierKeep [emptyReply, errReply] = [errReply] := by
  decide

/-- A literal `Empty` argument evaluates to itself and is packed into the call. -/
theorem literal_empty_packed (space : Space) (dispatch : GroundedDispatch) (param : Atom)
    (b : Bindings) (fuel : Nat) (live : List Atom) :
    interpretArgs space dispatch [Atom.empty] [param] b (fuel + 2) live =
      [(argumentPacket [Atom.empty], b)] := by
  rw [interpretArgs_one]
  rw [evalAtom]
  simp [isEmptyOrError, isEmptyAtom]

/-- An argument whose evaluation answers `Empty` passes it through: the call
is not made. -/
theorem computed_empty_passes (space : Space) (dispatch : GroundedDispatch) (arg param : Atom)
    (b : Bindings) (fuel : Nat) (live : List Atom) (other : arg ≠ Atom.empty)
    (answers : evalAtom space dispatch arg param b (fuel + 1) live = [(Atom.empty, b)]) :
    interpretArgs space dispatch [arg] [param] b (fuel + 2) live = [(Atom.empty, b)] := by
  rw [interpretArgs_one, answers]
  simp only [isEmptyOrError, isEmptyAtom, List.map_cons, List.map_nil]
  have : (Atom.empty != arg) = true := by simpa [bne_iff_ne, ne_comm] using other
  simp [this]

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDispatchDeopt
