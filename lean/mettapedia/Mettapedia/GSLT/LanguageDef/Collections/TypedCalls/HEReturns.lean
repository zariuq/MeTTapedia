import Mettapedia.GSLT.LanguageDef.Collections.HECorrespondence
import Mettapedia.Languages.MeTTa.HE.CompletedDelivery
import Mettapedia.Languages.MeTTa.HE.BindingComposition

/-!
# HE: the type at which a call's result is evaluated

HE's interpreter (`Languages.MeTTa.HE.evalAtom`) evaluates the raw result of a
call, an equation's right-hand side, at a type that depends on the head. Every
theorem below holds for every space, head, argument list, record and budget
from a stated one on.

* **A typed head evaluates its result once, at its own range**
  (`typed_call_once`). For one ground declared arrow `(-> P₁ … Pₙ R)`,
  arguments that pass their checks once and are their own values, and an
  expected type `E` that accepts `R`, the answers are the results of the head's
  equations, each evaluated once at `R` (at `%Undefined%` for `Expression`).
  The expected type does not reach them (`typed_call_expected`). At `R = Atom`
  each result is returned as written (`typed_call_atom_range`). This is the
  rule of `Dialect.he` in the model, as written at `Atom` and evaluated once at
  every other range (`he_returning`): the general form of
  `HECorrespondence.he_w`.
* **An untyped head evaluates its result at the expected type**
  (`untyped_call_at_expected`).
* **A value at a type is a class test** (`evalAtom_grounded`): a number, string
  or truth value at a ground type other than `Atom` and `Grounded` is itself,
  once, when the type accepts its class, and `(Error v (BadType T C))`
  otherwise.
* **A range that the expected type rejects is a `BadType` naming the call**
  (`typed_call_rejected_range`), whatever the equations answer; `Expression`
  at a value class is such a range (`Controls.expression_range_rejected`), and
  so is `Number` at `String` for `+` (`Controls.native_range_names_call`).

So HE casts a value at the range of the innermost typed head that returns it,
and at the expected type only where untyped heads alone return it. Through
`(: g (-> Number %Undefined%))`, `(u 1)` expected at `Number` answers `"s"`
(`Controls.cast_through_undefined_range`), where a cast at `Number` is an
error (`Controls.cast_would_be_error`).

**Value signatures.** For a head whose one signature has its positions among
`Number`, `String`, `Bool` and `%Undefined%`, called on values whose types the
parameters accept, HE's checks pass once and bind nothing, each argument is its
own value, and the call is its equations' results, each evaluated once at the
range (`value_call`). Where those results are values, HE's answers are the
class-checked run, which tests each argument's class at its parameter and each
answer's at the range, exact in multiplicity (`value_call_classRun`). Where an
untyped call's results are values, its answers at a value class are their
casts there (`untyped_value_call_cast`).

**Parameter ranges.** For `(-> pre… $t post… $t)`, with `$t` at one parameter
and every other position a value class, called at `%Undefined%`, HE's check
binds `$t` once to the class of the argument there (`checkArgumentType_var`),
and the answers are the results, each evaluated once at `$t` under that binding
(`param_range_call`). A value at `$t` is then that class's test: itself where
its class is the argument's, and `BadType` at `$t`, which the bindings read as
that class, otherwise (`evalAtom_grounded_var`). So a check of the answers
against the argument's class, with a decline on a mismatch, has exactly HE's
answers (`param_range_classRun`; `Controls.keep_string`, `Controls.bad_number`).

**`if`.** With `(: if (-> Bool Atom Atom $t))`, an `if` expected at a value
class `E` binds `$t` to `E` and evaluates its chosen branch once at `$t`
(`if_call`), so a value branch is cast at `E` (`if_value_branch`;
`Controls.if_branch_kept`, `Controls.if_branch_cast`).

**The static reading** (`Reads`). A value is read as cast at `E`; a typed head
with range `%Undefined%`, `Atom` or `E` as keeping `E` from its results; an
untyped head as passing `E` to its results, each read alike; a neutral reading
whose answers have `E`'s class as a cast. Where the reading is a cast, none or
neutral, HE's evaluation at `E` is its evaluation at `%Undefined%` followed by
that treatment (`Reads.sound`). An `if` evaluates its branch at its range
variable, which `if_call` treats one step at a time.

The model's evaluator follows every applicable function type and every
successful binding path; Rust's and CeTTa's take the first. For the arguments
above, which have one type each, both take one path. The model renames no type
variable of a declaration, so the record of a parameter range or an `if`
carries the variable's equalities with itself (`checkedRecord`, `ifRecord`);
they leave its class value unchanged (`classValues_self`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## The evaluator's answers on an expression -/

/-- What the evaluator keeps of an interpretation: its successes, or its
errors when it has no success. -/
def keep (results : ResultSet) : ResultSet :=
  if !(results.filter fun r => !isErrorAtom r.1).isEmpty then
    results.filter fun r => !isErrorAtom r.1
  else results.filter fun r => isErrorAtom r.1

/-- An interpretation without errors is kept whole. -/
theorem keep_clean {results : ResultSet} (clean : ∀ r ∈ results, isErrorAtom r.1 = false) :
    keep results = results := by
  have kept : (results.filter fun r => !isErrorAtom r.1) = results :=
    List.filter_eq_self.mpr fun r member => by simp [clean r member]
  cases results with
  | nil => rfl
  | cons first others => simp [keep, kept]

theorem isErrorAtom_call {head : String} (notError : head ≠ "Error") (args : List Atom) :
    isErrorAtom (.expression (.symbol head :: args)) = false := by
  simp [isErrorAtom, notError]

theorem isEmptyOrError_call {head : String} (notError : head ≠ "Error") (args : List Atom) :
    isEmptyOrError (.expression (.symbol head :: args)) = false := by
  simp [isEmptyOrError, isEmptyAtom, Atom.empty, isErrorAtom_call notError args]

/-- An expression evaluated at a type other than `Atom` and `Expression` is
interpreted, and the evaluator keeps what `keep` keeps. -/
theorem evalAtom_expression {space : Space} {dispatch : GroundedDispatch} {head : Atom}
    {rest : List Atom} {type_ : Atom} (clean : isEmptyOrError (.expression (head :: rest)) = false)
    (notAtom : type_ ≠ Atom.atomType) (notExpression : type_ ≠ Atom.expressionType)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    evalAtom space dispatch (.expression (head :: rest)) type_ bindings (fuel + 1) live =
      keep (interpretExpression space dispatch (.expression (head :: rest)) type_ bindings fuel
        live) := by
  have notAtom' : ¬type_ = Atom.symbol "Atom" := notAtom
  have notExpression' : ¬type_ = Atom.symbol "Expression" := notExpression
  rw [evalAtom]
  simp only [clean, Bool.false_eq_true, if_false]
  simp [getMetaType, Atom.expressionType, Atom.symbolType, Atom.groundedType,
    Atom.variableType, Atom.atomType, Atom.unit, notAtom', notExpression', keep]

/-! ## A typed head evaluates its result once, at its range -/

/-- **A typed head evaluates its result once, at its range.** For a head whose
one declared type is a ground arrow `(-> P₁ … Pₙ R)`, called on arguments that
pass their checks once and are their own values, at an expected type `E` that
accepts `R`: the answers are the results of the head's equations, each returned
through HE's ordinary call return, which evaluates it once at `R` (at
`%Undefined%` for `Expression`). The expected type does not reach the results. -/
theorem typed_call_once {space : Space} {dispatch : GroundedDispatch} {head : String}
    {params args : List Atom} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notExecutable : dispatch.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (.expression (.symbol head :: args)) = false)
    (checked : List.Forall₂ (ArgumentChecked space) params args)
    (returns : accepts expected range = true)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (bindings : Bindings) {fuel : Nat} (enough : matchFuel (arrowType params range) ≤ fuel)
    (arguments : ∀ live, interpretArgs space dispatch args params bindings (fuel + 1) live =
      [(argumentPacket args, bindings)])
    {live : List Atom} {replies : ResultSet}
    (queried : rawQueryResults space (.expression (.symbol head :: args)) (callReturnType range)
      bindings (fuel + 1) live = replies)
    (nonempty : replies ≠ [])
    (plain : ∀ reply ∈ replies, ∀ body, reply.1 ≠ .expression [.symbol "function", body]) :
    evalAtom space dispatch (.expression (.symbol head :: args)) expected bindings (fuel + 4) live =
      keep (replies.flatMap fun reply =>
        ordinaryCallReturn (.expression (.symbol head :: args)) reply.1 reply.2
          fun value b => evalAtom space dispatch value (callReturnType range) b (fuel + 1) live) := by
  rw [evalAtom_expression (isEmptyOrError_call notError args) notAtom notExpression,
    interpretExpression_typed (copies := 0) declared ground notEmpty checked returns bindings enough
      arguments (invoke_queried notExecutable notInstruction (isErrorAtom_call notError args)
        queried nonempty plain none)]
  simp

/-- At the range `Atom` each result is returned as written. -/
theorem typed_call_atom_range {space : Space} {dispatch : GroundedDispatch} {head : String}
    {params args : List Atom} {expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params Atom.atomType])
    (ground : atomVariables (arrowType params Atom.atomType) = [])
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notExecutable : dispatch.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (.expression (.symbol head :: args)) = false)
    (checked : List.Forall₂ (ArgumentChecked space) params args)
    (returns : accepts expected Atom.atomType = true)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (bindings : Bindings) {fuel : Nat} (enough : matchFuel (arrowType params Atom.atomType) ≤ fuel)
    (arguments : ∀ live, interpretArgs space dispatch args params bindings (fuel + 1) live =
      [(argumentPacket args, bindings)])
    {live : List Atom} {replies : ResultSet}
    (queried : rawQueryResults space (.expression (.symbol head :: args)) Atom.atomType
      bindings (fuel + 1) live = replies)
    (nonempty : replies ≠ [])
    (plain : ∀ reply ∈ replies, ∀ body, reply.1 ≠ .expression [.symbol "function", body]) :
    evalAtom space dispatch (.expression (.symbol head :: args)) expected bindings (fuel + 4) live =
      keep (replies.flatMap fun reply =>
        ordinaryCallReturn (.expression (.symbol head :: args)) reply.1 reply.2
          fun value b => [(value, b)]) := by
  have atomReturn : callReturnType Atom.atomType = Atom.atomType := by
    simp [callReturnType, Atom.atomType, Atom.expressionType]
  rw [typed_call_once declared ground notEmpty notError notExecutable notInstruction checked
    returns notAtom notExpression bindings enough arguments (atomReturn ▸ queried) nonempty plain,
    atomReturn]
  simp only [HECorrespondence.he_atom_demand]

/-- The model's result type of a declared range: `Atom` is data, and every
other range is evaluated. -/
def resultTypeOf (range : Atom) : Evaluation.ResultType :=
  if range = Atom.atomType then .data else .undefined

/-- What the model's dialect `Dialect.he` does with a raw result at a range:
returned as written at `Atom`, evaluated once at any other range. -/
def heReturn (space : Space) (dispatch : GroundedDispatch) (range : Atom) (fuel : Nat)
    (live : List Atom) (value : Atom) (bindings : Bindings) : ResultSet :=
  match Evaluation.Dialect.he.returning (resultTypeOf range) with
  | .asWritten => [(value, bindings)]
  | .once => evalAtom space dispatch value range bindings (fuel + 1) live

/-- **HE's interpreter returns a result as `Dialect.he` states**: evaluating a
raw result at the range is returning it as written at `Atom` and evaluating it
once at every other range. With `typed_call_once`, every result of a typed
head is returned by the model's rule for its declared range. -/
theorem he_returning (space : Space) (dispatch : GroundedDispatch) (range : Atom) (fuel : Nat)
    (live : List Atom) (value : Atom) (bindings : Bindings) :
    evalAtom space dispatch value range bindings (fuel + 1) live =
      heReturn space dispatch range fuel live value bindings := by
  unfold heReturn resultTypeOf
  by_cases atomRange : range = Atom.atomType
  · subst atomRange
    simp only [if_true, Evaluation.Dialect.he]
    exact HECorrespondence.he_atom_demand space dispatch value bindings fuel live
  · simp [atomRange, Evaluation.Dialect.he]

/-! ## An untyped head evaluates its result at the expected type -/

/-- A tuple of atoms that are their own values at `%Undefined%` from some fuel
on is its own value. -/
theorem interpretTuple_values {space : Space} {dispatch : GroundedDispatch} {bindings : Bindings}
    {base : Nat} :
    ∀ (elements : List Atom), elements ≠ [] →
      (∀ x ∈ elements, isEmptyOrError x = false ∧ x ≠ .symbol "Error" ∧
        ∀ m, base ≤ m → ∀ live,
          evalAtom space dispatch x Atom.undefinedType bindings m live = [(x, bindings)]) →
      ∀ m, base + elements.length ≤ m → ∀ live,
        interpretTuple space dispatch (.expression elements) bindings m live =
          [(.expression elements, bindings)]
  | [], nonempty, _, _, _, _ => absurd rfl nonempty
  | [x], _, values, m, enough, live => by
      obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp at enough; omega⟩
      obtain ⟨clean, _, self⟩ := values x (by simp)
      rw [interpretTuple, self m (by simp at enough; omega)]
      simp [tupleSingleton, clean]
  | x :: y :: rest, _, values, m, enough, live => by
      simp only [List.length_cons] at enough
      obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      obtain ⟨clean, _, self⟩ := values x (by simp)
      have tail := interpretTuple_values (y :: rest) (by simp)
        (fun z member => values z (List.mem_cons_of_mem x member)) m
        (by simp only [List.length_cons]; omega)
      obtain ⟨cleanY, notErrorY, _⟩ := values y (by simp)
      have tailClean : isEmptyOrError (.expression (y :: rest)) = false := by
        cases y with
        | symbol name =>
            have : name ≠ "Error" := fun same => notErrorY (by rw [same])
            simp [isEmptyOrError, isEmptyAtom, Atom.empty, isErrorAtom, this]
        | var _ => simp [isEmptyOrError, isEmptyAtom, Atom.empty, isErrorAtom]
        | grounded _ => simp [isEmptyOrError, isEmptyAtom, Atom.empty, isErrorAtom]
        | expression _ => simp [isEmptyOrError, isEmptyAtom, Atom.empty, isErrorAtom]
      rw [interpretTuple, self m (by omega)]
      simp [clean, tail, tailClean, atomElements]

/-- **An untyped head evaluates its result at the expected type.** For a head
declared with no type, whose call is its own tuple, at an expected type `E`
other than `Atom` and `Expression`: the answers are the results of the head's
equations, each returned through HE's ordinary call return, which evaluates it
at `E`. -/
theorem untyped_call_at_expected {space : Space} {dispatch : GroundedDispatch} {head : String}
    {args : List Atom} {expected : Atom}
    (untyped : getAtomTypes space (.symbol head) = [Atom.undefinedType])
    (notError : head ≠ "Error")
    (notExecutable : dispatch.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (.expression (.symbol head :: args)) = false)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    {bindings : Bindings} {fuel : Nat}
    (tuple : ∀ live, interpretTuple space dispatch (.expression (.symbol head :: args)) bindings
      (fuel + 2) live = [(.expression (.symbol head :: args), bindings)])
    {live : List Atom} {replies : ResultSet}
    (queried : rawQueryResults space (.expression (.symbol head :: args)) expected bindings
      (fuel + 1) live = replies)
    (nonempty : replies ≠ [])
    (plain : ∀ reply ∈ replies, ∀ body, reply.1 ≠ .expression [.symbol "function", body]) :
    evalAtom space dispatch (.expression (.symbol head :: args)) expected bindings (fuel + 4) live =
      keep (replies.flatMap fun reply =>
        ordinaryCallReturn (.expression (.symbol head :: args)) reply.1 reply.2
          fun value b => evalAtom space dispatch value expected b (fuel + 1) live) := by
  rw [evalAtom_expression (isEmptyOrError_call notError args) notAtom notExpression]
  congr 1
  have invoked := invoke_queried notExecutable notInstruction (isErrorAtom_call notError args)
    queried nonempty plain none
  rw [interpretExpression]
  simp only [untyped, tuple, List.flatMap_cons, List.flatMap_nil, List.append_nil, invoked]
  have function : isFunctionType Atom.undefinedType = false := rfl
  simp only [function, Bool.false_eq_true, if_false, List.nil_append, List.any_cons,
    List.any_nil, Bool.not_false, beq_self_eq_true, Bool.or_true, Bool.or_false, if_true]
  split
  · rfl
  · next empty =>
      simp only [Bool.not_eq_true', Bool.not_eq_false] at empty
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      exact (List.isEmpty_iff.mp (by simpa using empty)).symm

/-! ## A value at a type is a class test -/

theorem getAtomTypes_grounded (space : Space) (value : GroundedValue) :
    getAtomTypes space (.grounded value) = [getGroundedType value] := by
  unfold getAtomTypes
  by_cases undefined : getGroundedType value = Atom.undefinedType
  · simp [undefined]
  · have : (getGroundedType value == Atom.undefinedType) = false := by simpa using undefined
    simp [this]

theorem getGroundedType_symbol (value : GroundedValue) :
    ∃ name, getGroundedType value = .symbol name := by
  cases value <;> exact ⟨_, rfl⟩

theorem getGroundedType_ground (value : GroundedValue) :
    atomVariables (getGroundedType value) = [] := by
  obtain ⟨name, same⟩ := getGroundedType_symbol value
  rw [same]
  rfl

/-- **A value at a type is a class test.** A number, string or truth value,
evaluated at a ground type other than `Atom` and `Grounded`, is itself once
when the type accepts its class, and HE's `(Error v (BadType T C))` otherwise. -/
theorem evalAtom_grounded {space : Space} {dispatch : GroundedDispatch} (value : GroundedValue)
    {type_ : Atom} (ground : atomVariables type_ = []) (notAtom : type_ ≠ Atom.atomType)
    (notGrounded : type_ ≠ Atom.groundedType) (bindings : Bindings) {fuel : Nat}
    (enough : matchFuel type_ ≤ fuel) (live : List Atom) :
    evalAtom space dispatch (.grounded value) type_ bindings (fuel + 1) live =
      if accepts type_ (getGroundedType value) then [(.grounded value, bindings)]
      else [(mkError (.grounded value) (.badType type_ (getGroundedType value)), bindings)] := by
  have cast : typeCast (.grounded value) type_ space bindings fuel =
      if accepts type_ (getGroundedType value) then [(.grounded value, bindings)]
      else [(mkError (.grounded value) (.badType type_ (getGroundedType value)), bindings)] := by
    unfold typeCast
    simp only [rawTypeLookup, getAtomTypes_grounded]
    rw [typeCast.typeCastLoop]
    cases accepted : accepts type_ (getGroundedType value) with
    | true =>
        rw [matchTypes_accepted ground accepted bindings enough]
        simp
    | false =>
        rw [matchTypes_rejected ground (getGroundedType_ground value) accepted]
        simp [typeCast.typeCastLoop]
  have notAtom' : ¬type_ = Atom.symbol "Atom" := notAtom
  have notGrounded' : ¬type_ = Atom.symbol "Grounded" := notGrounded
  rw [evalAtom]
  simp [isEmptyOrError, isEmptyAtom, Atom.empty, isErrorAtom, getMetaType, Atom.atomType,
    Atom.groundedType, Atom.variableType, Atom.symbolType, notAtom', notGrounded', cast]

/-! ## Value signatures -/

/-- A position of a value signature: `Number`, `String`, `Bool` or `%Undefined%`. -/
def ValueClass (type_ : Atom) : Prop :=
  type_ = .symbol "Number" ∨ type_ = .symbol "String" ∨ type_ = .symbol "Bool" ∨
    type_ = Atom.undefinedType

namespace ValueClass

variable {type_ : Atom}

theorem symbol (valueClass : ValueClass type_) : ∃ name, type_ = .symbol name := by
  rcases valueClass with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem ground (valueClass : ValueClass type_) : atomVariables type_ = [] := by
  obtain ⟨_, rfl⟩ := valueClass.symbol
  rfl

theorem matchFuel_eq (valueClass : ValueClass type_) : matchFuel type_ = 1 := by
  obtain ⟨_, rfl⟩ := valueClass.symbol
  rfl

theorem notAtom (valueClass : ValueClass type_) : type_ ≠ Atom.atomType := by
  rcases valueClass with rfl | rfl | rfl | rfl <;> simp [Atom.atomType, Atom.undefinedType]

theorem notGrounded (valueClass : ValueClass type_) : type_ ≠ Atom.groundedType := by
  rcases valueClass with rfl | rfl | rfl | rfl <;> simp [Atom.groundedType, Atom.undefinedType]

theorem notExpression (valueClass : ValueClass type_) : type_ ≠ Atom.expressionType := by
  rcases valueClass with rfl | rfl | rfl | rfl <;> simp [Atom.expressionType, Atom.undefinedType]

theorem callReturnType_eq (valueClass : ValueClass type_) : callReturnType type_ = type_ := by
  simp [callReturnType, valueClass.notExpression]

end ValueClass

/-- The class test of the prepared machine at a position: the value's type is
accepted there. -/
def classTests : List Atom → List GroundedValue → Bool
  | [], [] => true
  | param :: params, value :: values =>
      accepts param (getGroundedType value) && classTests params values
  | _, _ => false

theorem classTests_iff : ∀ (params : List Atom) (values : List GroundedValue),
    classTests params values = true ↔
      List.Forall₂ (fun param value => accepts param (getGroundedType value) = true) params values
  | [], [] => by simp [classTests]
  | [], _ :: _ => by simp [classTests]
  | _ :: _, [] => by simp [classTests]
  | param :: params, value :: values => by
      simp [classTests, classTests_iff params values]

/-- A value passes HE's check at a position that accepts its class exactly
once, binding nothing. -/
theorem argumentChecked_grounded (space : Space) {param : Atom} (value : GroundedValue)
    (passes : accepts param (getGroundedType value) = true) :
    ArgumentChecked space param (.grounded value) where
  once := by simp [getAtomTypes_grounded, passes]
  rejectedGround := by
    intro type member _
    rw [getAtomTypes_grounded, List.mem_singleton] at member
    rw [member]
    exact getGroundedType_ground value

/-- Values that pass the class tests of value-class parameters are their own
argument packet, from a fuel of one more than their number on. -/
theorem interpretArgs_values {space : Space} {dispatch : GroundedDispatch} {bindings : Bindings} :
    ∀ (params : List Atom) (values : List GroundedValue),
      (∀ param ∈ params, ValueClass param) →
      List.Forall₂ (fun param value => accepts param (getGroundedType value) = true) params
        values →
      ∀ fuel, values.length + 1 ≤ fuel → ∀ live,
        interpretArgs space dispatch (values.map .grounded) params bindings (fuel + 1) live =
          [(argumentPacket (values.map .grounded), bindings)]
  | [], [], _, _, fuel, _, live => by
      simpa using interpretArgs_nil_self (space := space) (dispatch := dispatch) bindings fuel live
  | param :: params, value :: values, classes, passes, fuel, enough, live => by
      simp only [List.length_cons] at enough
      obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      have valueClass := classes param (by simp)
      have rest := interpretArgs_values (space := space) (dispatch := dispatch)
        (bindings := bindings) params values
        (fun other member => classes other (by simp [member])) (List.forall₂_cons.mp passes).2
        fuel (by omega)
      have first : ∀ live, evalAtom space dispatch (.grounded value) param bindings (fuel + 1) live =
          [(.grounded value, bindings)] := by
        intro live
        obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
        rw [evalAtom_grounded value valueClass.ground valueClass.notAtom valueClass.notGrounded
          bindings (by rw [valueClass.matchFuel_eq]; omega) live,
          if_pos (List.forall₂_cons.mp passes).1]
      exact interpretArgs_cons_self first rest live
  | [], _ :: _, _, passes, _, _, _ => by cases passes
  | _ :: _, [], _, passes, _, _, _ => by cases passes

theorem length_lt_matchListFuel : ∀ atoms : List Atom, atoms.length < matchListFuel atoms
  | [] => by simp [matchListFuel]
  | atom :: atoms => by
      have := length_lt_matchListFuel atoms
      simp only [matchListFuel, List.length_cons]
      omega

theorem length_lt_matchFuel_arrow (params : List Atom) (range : Atom) :
    params.length + 2 < matchFuel (arrowType params range) := by
  have := length_lt_matchListFuel (.symbol "->" :: (params ++ [range]))
  simp only [arrowType, matchFuel, List.length_cons, List.length_append] at this ⊢
  omega

/-- **HE's typed call of a value signature is its class tests, then its results
evaluated once at its range.** For a head whose one signature has positions in
`Number`, `String`, `Bool` and `%Undefined%`, called on numbers, strings and
truth values whose types the parameters accept, at an expected type that accepts
the range: HE's argument checks pass once and bind nothing, each argument is
its own value, and the answers are the results of the head's equations, each
evaluated once at the range. -/
theorem value_call {space : Space} {dispatch : GroundedDispatch} {head : String}
    {params : List Atom} {values : List GroundedValue} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (classes : ∀ position ∈ range :: params, ValueClass position)
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notExecutable : dispatch.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (.expression (.symbol head :: values.map .grounded)) =
      false)
    (passes : classTests params values = true)
    (returns : accepts expected range = true)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (bindings : Bindings) {fuel : Nat} (enough : matchFuel (arrowType params range) ≤ fuel)
    {live : List Atom} {replies : ResultSet}
    (queried : rawQueryResults space (.expression (.symbol head :: values.map .grounded)) range
      bindings (fuel + 1) live = replies)
    (nonempty : replies ≠ [])
    (plain : ∀ reply ∈ replies, ∀ body, reply.1 ≠ .expression [.symbol "function", body]) :
    evalAtom space dispatch (.expression (.symbol head :: values.map .grounded)) expected bindings
        (fuel + 4) live =
      keep (replies.flatMap fun reply =>
        ordinaryCallReturn (.expression (.symbol head :: values.map .grounded)) reply.1 reply.2
          fun value b => evalAtom space dispatch value range b (fuel + 1) live) := by
  have rangeClass := classes range (by simp)
  have paramClasses : ∀ param ∈ params, ValueClass param :=
    fun param member => classes param (by simp [member])
  have passes' := (classTests_iff params values).mp passes
  have ground : atomVariables (arrowType params range) = [] := by
    have whole : atomListVariables (.symbol "->" :: (params ++ [range])) = [] := by
      simp only [atomListVariables, atomVariables, List.nil_append]
      have lists : ∀ xs : List Atom, (∀ x ∈ xs, ValueClass x) → atomListVariables xs = [] := by
        intro xs
        induction xs with
        | nil => intro _; rfl
        | cons x xs ih =>
            intro each
            simp only [atomListVariables, (each x (by simp)).ground, List.nil_append]
            exact ih fun y member => each y (by simp [member])
      exact lists _ fun x member => by
        rcases List.mem_append.mp member with member | member
        · exact paramClasses x member
        · rw [List.mem_singleton.mp member]; exact rangeClass
    simpa [arrowType, atomVariables] using whole
  have checked : List.Forall₂ (ArgumentChecked space) params (values.map .grounded) := by
    rw [List.forall₂_map_right_iff]
    exact passes'.imp fun _ value passing => argumentChecked_grounded space value passing
  have lengths : values.length = params.length := passes'.length_eq.symm
  have arguments := interpretArgs_values (space := space) (dispatch := dispatch)
    (bindings := bindings) params values paramClasses passes' fuel
    (by have := length_lt_matchFuel_arrow params range; omega)
  rw [typed_call_once declared ground notEmpty notError notExecutable notInstruction checked
    returns notAtom notExpression bindings enough arguments
    (by rw [rangeClass.callReturnType_eq]; exact queried) nonempty plain,
    rangeClass.callReturnType_eq]

/-! ## The class-checked run -/

/-- The prepared machine's run of one call of a value-class head, given the
values its equations answer: each argument's class is tested at its parameter
and each answer's class at the range; `none` declines to the canonical
evaluator. -/
def classRun (params : List Atom) (range : Atom) (values : List GroundedValue)
    (answers : List (GroundedValue × Bindings)) : Option ResultSet :=
  if (classTests params values && answers.all fun answer =>
      accepts range (getGroundedType answer.1)) = true then
    some (answers.map fun answer => (.grounded answer.1, answer.2))
  else none

/-- The ordinary call return of a value is its evaluation. -/
theorem ordinaryCallReturn_grounded (original : Atom) (value : GroundedValue) (bindings : Bindings)
    (evaluate : Atom → Bindings → ResultSet) :
    ordinaryCallReturn original (.grounded value) bindings evaluate =
      evaluate (.grounded value) bindings := by
  apply ordinaryCallReturn_evaluate
  · simp [Atom.notReducible]
  · simp [isEmptyOrError, isEmptyAtom, Atom.empty, isErrorAtom]

/-- **HE's typed call of a value signature is the class-checked run, exact in
multiplicity**, when the head's equations answer values (literals or
parameters): wherever the machine's run answers, HE answers the same results,
each as often. -/
theorem value_call_classRun {space : Space} {dispatch : GroundedDispatch} {head : String}
    {params : List Atom} {values : List GroundedValue} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (classes : ∀ position ∈ range :: params, ValueClass position)
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notExecutable : dispatch.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (.expression (.symbol head :: values.map .grounded)) =
      false)
    (returns : accepts expected range = true)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (bindings : Bindings) {fuel : Nat} (enough : matchFuel (arrowType params range) ≤ fuel)
    {live : List Atom} {answers : List (GroundedValue × Bindings)}
    (queried : rawQueryResults space (.expression (.symbol head :: values.map .grounded)) range
      bindings (fuel + 1) live = answers.map fun answer => (.grounded answer.1, answer.2))
    (nonempty : answers ≠ [])
    {results : ResultSet} (run : classRun params range values answers = some results) :
    evalAtom space dispatch (.expression (.symbol head :: values.map .grounded)) expected bindings
      (fuel + 4) live = results := by
  unfold classRun at run
  split at run
  · next passing =>
      cases run
      simp only [Bool.and_eq_true, List.all_eq_true] at passing
      have rangeClass := classes range (by simp)
      rw [value_call declared classes notEmpty notError notExecutable notInstruction passing.1
        returns notAtom notExpression bindings enough queried
        (by simpa using nonempty) (fun reply member body => by
          obtain ⟨answer, _, rfl⟩ := List.mem_map.mp member
          simp)]
      have each : ∀ answer ∈ answers,
          ordinaryCallReturn (.expression (.symbol head :: values.map .grounded))
            (.grounded answer.1) answer.2
            (fun value b => evalAtom space dispatch value range b (fuel + 1) live) =
          [(.grounded answer.1, answer.2)] := by
        intro answer member
        rw [ordinaryCallReturn_grounded,
          evalAtom_grounded answer.1 rangeClass.ground rangeClass.notAtom rangeClass.notGrounded
            answer.2 (by have := length_lt_matchFuel_arrow params range; rw [rangeClass.matchFuel_eq]; omega) live,
          if_pos (passing.2 answer member)]
      rw [List.flatMap_map, List.flatMap_congr each, ← List.map_eq_flatMap]
      exact keep_clean fun r member => by
        obtain ⟨answer, _, rfl⟩ := List.mem_map.mp member
        rfl
  · cases run

/-- **An untyped call whose equations answer values is the cast of those values
at the expected type**: each value is itself where the type accepts its class,
and HE's `BadType` error otherwise, and the evaluator keeps the successes. This
is the cast that a closed untyped call's answers may take at the expected type. -/
theorem untyped_value_call_cast {space : Space} {dispatch : GroundedDispatch} {head : String}
    {values : List GroundedValue} {expected : Atom}
    (untyped : getAtomTypes space (.symbol head) = [Atom.undefinedType])
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notExecutable : dispatch.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (.expression (.symbol head :: values.map .grounded)) =
      false)
    (expectedClass : ValueClass expected)
    (bindings : Bindings) {fuel : Nat} (enough : values.length + 1 ≤ fuel)
    {live : List Atom} {answers : List (GroundedValue × Bindings)}
    (queried : rawQueryResults space (.expression (.symbol head :: values.map .grounded)) expected
      bindings (fuel + 1) live = answers.map fun answer => (.grounded answer.1, answer.2))
    (nonempty : answers ≠ []) :
    evalAtom space dispatch (.expression (.symbol head :: values.map .grounded)) expected bindings
        (fuel + 4) live =
      keep (answers.map fun answer =>
        if accepts expected (getGroundedType answer.1) then (.grounded answer.1, answer.2)
        else (mkError (.grounded answer.1) (.badType expected (getGroundedType answer.1)),
          answer.2)) := by
  have headSelf : ∀ m, 2 ≤ m → ∀ live, evalAtom space dispatch (.symbol head) Atom.undefinedType
      bindings m live = [(.symbol head, bindings)] := by
    intro m bound live
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [evalAtom_symbol notEmpty (by simp [Atom.undefinedType, Atom.atomType])
      (by simp [Atom.undefinedType, Atom.symbolType]) bindings m live]
    unfold typeCast
    simp only [rawTypeLookup, untyped, typeCast.typeCastLoop]
    simp [matchTypes]
  have valueSelf : ∀ value : GroundedValue, ∀ m, 2 ≤ m → ∀ live,
      evalAtom space dispatch (.grounded value) Atom.undefinedType bindings m live =
        [(.grounded value, bindings)] := by
    intro value m bound live
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have undefinedClass : ValueClass Atom.undefinedType := Or.inr (Or.inr (Or.inr rfl))
    rw [evalAtom_grounded value undefinedClass.ground undefinedClass.notAtom
      undefinedClass.notGrounded bindings (by rw [undefinedClass.matchFuel_eq]; omega) live]
    simp [accepts]
  have tuple : ∀ live, interpretTuple space dispatch
      (.expression (.symbol head :: values.map .grounded)) bindings (fuel + 2) live =
        [(.expression (.symbol head :: values.map .grounded), bindings)] := by
    intro live
    apply interpretTuple_values (base := 2) _ (by simp)
    · intro x member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨isEmptyOrError_symbol notEmpty, fun same => notError (by cases same; rfl),
          headSelf⟩
      · obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
        exact ⟨by simp [isEmptyOrError, isEmptyAtom, Atom.empty, isErrorAtom], by simp,
          valueSelf value⟩
    · simp only [List.length_cons, List.length_map]
      omega
  rw [untyped_call_at_expected untyped notError notExecutable notInstruction
    expectedClass.notAtom expectedClass.notExpression tuple queried (by simpa using nonempty)
    (fun reply member body => by
      obtain ⟨answer, _, rfl⟩ := List.mem_map.mp member
      simp), List.flatMap_map]
  congr 1
  rw [List.map_eq_flatMap (l := answers)]
  apply List.flatMap_congr
  intro answer _
  rw [ordinaryCallReturn_grounded,
    evalAtom_grounded answer.1 expectedClass.ground expectedClass.notAtom expectedClass.notGrounded
      answer.2 (by rw [expectedClass.matchFuel_eq]; omega) live]
  split <;> rfl

/-! ## Ranges written as a parameter's type variable -/

theorem matchAtoms_var_symbol (name label : String) (fuel : Nat) :
    matchAtoms (.var name) (.symbol label) (fuel + 1) =
      [Bindings.empty.assign name (.symbol label)] := by
  have noLoop : (Bindings.empty.assign name (.symbol label)).hasLoop = false :=
    Bindings.hasLoop_false_of_assignment_vars_nil _ fun entry member => by
      simp [Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup] at member
      rw [member]
      rfl
  simp [matchAtoms, getMetaType, Atom.variableType, Atom.symbolType, noLoop]

/-- The match of a type variable against a value's class, as `matchTypes`
makes it. -/
theorem matchTypes_var_grounded (value : GroundedValue) (name : String) (bindings : Bindings)
    (notUndefined : getGroundedType value ≠ Atom.undefinedType)
    (notAtom : getGroundedType value ≠ Atom.atomType) (fuel : Nat) :
    matchTypes (.var name) (getGroundedType value) bindings (fuel + 2) =
      mergeBindings bindings (Bindings.empty.assign name (getGroundedType value)) (fuel + 2) := by
  obtain ⟨label, same⟩ := getGroundedType_symbol value
  rw [same] at notUndefined notAtom ⊢
  have notUndefined' : ¬label = "%Undefined%" := fun h => notUndefined (by rw [h]; rfl)
  have notAtom' : ¬label = "Atom" := fun h => notAtom (by rw [h]; rfl)
  unfold matchTypes
  rw [if_neg (by simp [Atom.undefinedType, Atom.atomType, notUndefined', notAtom']),
    matchAtoms_var_symbol]
  simp

/-- **HE's check at an unbound type variable binds it once, to the value's
class.** -/
theorem checkArgumentType_var (space : Space) (value : GroundedValue) {name : String}
    {bindings : Bindings} (unbound : bindings.lookup name = none)
    (noEqualities : bindings.equalities = [])
    (notUndefined : getGroundedType value ≠ Atom.undefinedType)
    (notAtom : getGroundedType value ≠ Atom.atomType) (fuel : Nat) :
    checkArgumentType space (.grounded value) (.var name) bindings (fuel + 2) =
      [.inr (bindings.assign name (getGroundedType value))] := by
  unfold checkArgumentType
  simp only [rawTypeLookup, getAtomTypes_grounded, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [matchTypes_var_grounded value name bindings notUndefined notAtom,
    mergeBindings_single_assign_fresh unbound noEqualities]
  simp

/-- **A value at a type variable whose class carries one type is that type's
class test**: itself once where its class is that type, and HE's `BadType` at
the variable, which the bindings read as that type, otherwise. -/
theorem evalAtom_grounded_var {space : Space} {dispatch : GroundedDispatch}
    (value : GroundedValue) {name : String} {bindings : Bindings} {fixed : Atom}
    (carries : bindings.classValues name = [fixed]) (fixedGround : atomVariables fixed = [])
    (notUndefined : getGroundedType value ≠ Atom.undefinedType)
    (notAtom : getGroundedType value ≠ Atom.atomType) (fuel : Nat) (live : List Atom) :
    evalAtom space dispatch (.grounded value) (.var name) bindings (fuel + 3) live =
      if getGroundedType value = fixed then [(.grounded value, bindings)]
      else [(mkError (.grounded value) (.badType (.var name) (getGroundedType value)),
        bindings)] := by
  have matched : matchTypes (.var name) (getGroundedType value) bindings (fuel + 2) =
      if getGroundedType value = fixed then [bindings] else [] := by
    rw [matchTypes_var_grounded value name bindings notUndefined notAtom,
      mergeBindings_single_assign]
    rw [addVarBinding]
    simp only [carries, Bindings.valuesConsistent, List.all_nil, if_true]
    by_cases same : getGroundedType value = fixed
    · simp [same]
    · have distinct : (fixed == getGroundedType value) = false :=
        beq_eq_false_iff_ne.mpr (Ne.symm same)
      rw [if_neg (by simp [distinct]), if_neg same,
        (matchAtoms_ground_ne fuel).1 fixed (getGroundedType value) fixedGround
          (getGroundedType_ground value) (Ne.symm same)]
      rfl
  have cast : typeCast (.grounded value) (.var name) space bindings (fuel + 2) =
      if getGroundedType value = fixed then [(.grounded value, bindings)]
      else [(mkError (.grounded value) (.badType (.var name) (getGroundedType value)),
        bindings)] := by
    unfold typeCast
    simp only [rawTypeLookup, getAtomTypes_grounded]
    rw [typeCast.typeCastLoop, matched]
    by_cases same : getGroundedType value = fixed
    · simp [same]
    · simp [same, typeCast.typeCastLoop]
  rw [evalAtom]
  simp [isEmptyOrError, isEmptyAtom, Atom.empty, isErrorAtom, getMetaType, Atom.atomType,
    Atom.groundedType, Atom.variableType, Atom.symbolType, cast]


/-! ### The record a type variable's check leaves -/

/-- Every equality of the record equates `name` with itself. -/
def SelfEqualities (name : String) (bindings : Bindings) : Prop :=
  ∀ e ∈ bindings.equalities, e = (name, name)

theorem eqStep_self {name : String} : ∀ (equalities : List (String × String)),
    (∀ e ∈ equalities, e = (name, name)) → ∀ acc : List String, name ∈ acc →
      Bindings.eqStep equalities acc = acc
  | [], _, _, _ => rfl
  | e :: rest, self, acc, member => by
      have same := self e (by simp)
      subst same
      have contains : acc.contains name = true := by simpa using member
      unfold Bindings.eqStep
      rw [List.foldl_cons]
      simp only [contains, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
      exact eqStep_self rest (fun e' member' => self e' (by simp [member'])) acc member

theorem eqClassAux_self {name : String} {equalities : List (String × String)}
    (self : ∀ e ∈ equalities, e = (name, name)) :
    ∀ k, Bindings.eqClassAux equalities k [name] = [name]
  | 0 => rfl
  | k + 1 => by
      rw [Bindings.eqClassAux, eqStep_self equalities self [name] (by simp)]
      exact eqClassAux_self self k

theorem foldl_self_names {name : String} (F : List String → String × String → List String)
    (fromEmpty : F [] (name, name) = [name]) (fromSingle : F [name] (name, name) = [name]) :
    ∀ (equalities : List (String × String)), (∀ e ∈ equalities, e = (name, name)) →
      ∀ acc, (acc = [] ∨ acc = [name]) →
        equalities.foldl F acc = [] ∨ equalities.foldl F acc = [name]
  | [], _, _, start => start
  | e :: rest, self, acc, start => by
      have same := self e (by simp)
      subst same
      rw [List.foldl_cons]
      apply foldl_self_names F fromEmpty fromSingle rest
        (fun e' member => self e' (by simp [member]))
      rcases start with rfl | rfl
      · exact Or.inr fromEmpty
      · exact Or.inr fromSingle

/-- In a record whose equalities equate `name` with itself, `name`'s class is
`name` alone, so its class values are its own value. -/
theorem classValues_self {name : String} {bindings : Bindings} {fixed : Atom}
    (self : SelfEqualities name bindings) (assigned : bindings.lookup name = some fixed) :
    bindings.classValues name = [fixed] := by
  have ordered : bindings.eqVarsInOrder = [] ∨ bindings.eqVarsInOrder = [name] := by
    unfold Bindings.eqVarsInOrder
    exact foldl_self_names _ (by simp) (by simp) bindings.equalities self [] (Or.inl rfl)
  have classOf : bindings.eqClass name = [name] := by
    unfold Bindings.eqClass
    exact eqClassAux_self self _
  have members : bindings.eqClassOrdered name = [name] := by
    unfold Bindings.eqClassOrdered
    rcases ordered with ordered | ordered <;> simp [ordered, classOf]
  simp [Bindings.classValues, members, assigned]

theorem selfEqualities_addEquality {name : String} {bindings : Bindings}
    (self : SelfEqualities name bindings) : SelfEqualities name (bindings.addEquality name name) := by
  intro e member
  simp only [Bindings.addEquality, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact self e member
  · rfl

theorem lookup_addEquality (bindings : Bindings) (left right name : String) :
    (bindings.addEquality left right).lookup name = bindings.lookup name := rfl

theorem classValues_nil_of_assignments_nil {bindings : Bindings} (empty : bindings.assignments = [])
    (name : String) : bindings.classValues name = [] := by
  simp [Bindings.classValues, Bindings.lookup, empty]

/-- Matching symbols and occurrences of one variable against themselves records
the variable's equality with itself once per occurrence. -/
theorem matchAtomsList_self {name : String} : ∀ (atoms : List Atom)
    (equalities : List (String × String)) (fuel : Nat),
    (∀ atom ∈ atoms, (∃ label, atom = .symbol label) ∨ atom = .var name) →
    atoms.length + 3 ≤ fuel →
    matchAtomsList atoms atoms [⟨[], equalities⟩] fuel =
      [⟨[], equalities ++ List.replicate (atoms.count (.var name)) (name, name)⟩]
  | [], equalities, fuel, _, enough => by
      obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at enough; omega⟩
      simp [matchAtomsList]
  | atom :: atoms, equalities, fuel, shapes, enough => by
      simp only [List.length_cons] at enough
      obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      obtain ⟨g, rfl⟩ : ∃ k, fuel = k + 2 := ⟨fuel - 2, by omega⟩
      have rest := matchAtomsList_self (name := name) atoms
      rw [matchAtomsList]
      rcases shapes atom (by simp) with ⟨label, rfl⟩ | rfl
      · have selfMatch : matchAtoms (.symbol label) (.symbol label) (g + 2) = [Bindings.empty] := by
          simp [matchAtoms, getMetaType, Atom.symbolType, Bindings.hasLoop_empty]
        rw [selfMatch]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, mergeBindings_empty]
        rw [rest equalities (g + 2) (fun other member => shapes other (by simp [member]))
          (by omega)]
        simp
      · have noLoop : (Bindings.empty.addEquality name name).hasLoop = false :=
          Bindings.hasLoop_false_of_assignments_nil _ rfl
        have selfMatch : matchAtoms (.var name) (.var name) (g + 2) =
            [Bindings.empty.addEquality name name] := by
          simp [matchAtoms, getMetaType, Atom.variableType, noLoop]
        have merged : mergeBindings ⟨[], equalities⟩ (Bindings.empty.addEquality name name) (g + 2) =
            [⟨[], equalities ++ [(name, name)]⟩] := by
          simp only [mergeBindings, Bindings.empty, Bindings.addEquality, List.nil_append,
            List.foldl_nil, List.foldl_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil]
          rw [addVarEquality]
          simp [Bindings.addEquality, classValues_nil_of_assignments_nil (bindings :=
            ⟨[], equalities ++ [(name, name)]⟩) rfl, Bindings.valuesConsistent]
        rw [selfMatch]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, merged]
        rw [rest (equalities ++ [(name, name)]) (g + 2)
          (fun other member => shapes other (by simp [member])) (by omega)]
        rw [List.count_cons_self, List.replicate_succ]
        simp

/-- Merging the self-equalities of a match into a record that fixes `name`
appends them. -/
theorem mergeBindings_selfEqualities {name : String} : ∀ (count : Nat) (bindings : Bindings)
    (fixed : Atom), SelfEqualities name bindings → bindings.lookup name = some fixed →
    ∀ fuel, count.succ ≤ fuel →
      (List.replicate count (name, name)).foldl (fun acc (pair : String × String) =>
          acc.flatMap fun binds => addVarEquality binds pair.1 pair.2 fuel) [bindings] =
        [⟨bindings.assignments, bindings.equalities ++ List.replicate count (name, name)⟩]
  | 0, bindings, _, _, _, _, _ => by simp
  | count + 1, bindings, fixed, self, assigned, fuel, enough => by
      obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      have step : addVarEquality bindings name name (fuel + 1) = [bindings.addEquality name name] := by
        rw [addVarEquality]
        simp [classValues_self (selfEqualities_addEquality self)
          (by rw [lookup_addEquality]; exact assigned), Bindings.valuesConsistent]
      rw [List.replicate_succ, List.foldl_cons]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, step]
      rw [mergeBindings_selfEqualities count (bindings.addEquality name name) fixed
        (selfEqualities_addEquality self) (by rw [lookup_addEquality]; exact assigned)
        (fuel + 1) (by omega)]
      simp [Bindings.addEquality]


/-! ### The typed call of a parameter range -/

/-- Argument checks that each pass once, each from the record that the one
before it left. -/
inductive CheckSteps (space : Space) (fuel : Nat) :
    List Atom → List Atom → Bindings → Bindings → Prop
  | nil (bindings : Bindings) : CheckSteps space fuel [] [] bindings bindings
  | cons {param arg : Atom} {params args : List Atom} {bindings middle last : Bindings} :
      checkSuccesses (checkArgumentType space arg param bindings fuel) = [middle] →
      CheckSteps space fuel params args middle last →
      CheckSteps space fuel (param :: params) (arg :: args) bindings last

theorem CheckSteps.append {space : Space} {fuel : Nat} {params args params' args' : List Atom}
    {bindings middle last : Bindings} (first : CheckSteps space fuel params args bindings middle)
    (second : CheckSteps space fuel params' args' middle last) :
    CheckSteps space fuel (params ++ params') (args ++ args') bindings last := by
  induction first with
  | nil => exact second
  | cons step _ ih => exact .cons step (ih second)

theorem checkArgLoop_steps {space : Space} {fuel : Nat} {expr : Atom} {params args : List Atom}
    {bindings last : Bindings} (steps : CheckSteps space fuel params args bindings last)
    (errors : List Atom) (idx : Nat) :
    (checkIfFunctionTypeIsApplicable.checkArgLoop args params expr [bindings] errors space fuel
      idx).2 = [last] := by
  induction steps generalizing errors idx with
  | nil => rfl
  | cons first _ ih =>
      rw [checkIfFunctionTypeIsApplicable.checkArgLoop]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [foldl_checks_snd _ (fun _ _ => rfl) (fun _ _ => rfl), first, List.nil_append]
      exact ih _ _

/-- Values that pass the class tests of value-class parameters pass their checks
once and keep the record. -/
theorem checkSteps_values {space : Space} {bindings : Bindings} {fuel : Nat} :
    ∀ (params : List Atom) (values : List GroundedValue),
      (∀ param ∈ params, ValueClass param) → classTests params values = true → 1 ≤ fuel →
      CheckSteps space fuel params (values.map .grounded) bindings bindings
  | [], [], _, _, _ => .nil bindings
  | param :: params, value :: values, classes, passes, enough => by
      simp only [classTests, Bool.and_eq_true] at passes
      have valueClass := classes param (by simp)
      refine .cons ?_ (checkSteps_values params values
        (fun other member => classes other (by simp [member])) passes.2 enough)
      exact checkArgumentType_checked valueClass.ground
        (argumentChecked_grounded space value passes.1) bindings
        (by rw [valueClass.matchFuel_eq]; exact enough)
  | [], _ :: _, _, passes, _ => by simp [classTests] at passes
  | _ :: _, [], _, passes, _ => by simp [classTests] at passes

/-- Atoms that are their own values at their parameters, from a fuel of three on,
under one record, are their own argument packet. -/
theorem interpretArgs_selves {space : Space} {dispatch : GroundedDispatch}
    {bindings : Bindings} {params args : List Atom}
    (selves : List.Forall₂ (fun param arg => ∀ m, 3 ≤ m → ∀ live,
      evalAtom space dispatch arg param bindings m live = [(arg, bindings)]) params args) :
    ∀ fuel, args.length + 2 ≤ fuel → ∀ live,
      interpretArgs space dispatch args params bindings (fuel + 1) live =
        [(argumentPacket args, bindings)] := by
  induction selves with
  | nil =>
      intro fuel _ live
      exact interpretArgs_nil_self bindings fuel live
  | @cons param arg params args first _ ih =>
      intro fuel enough live
      simp only [List.length_cons] at enough
      obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      exact interpretArgs_cons_self (first (fuel + 1) (by omega)) (ih fuel (by omega)) live

/-- The record HE's typed call of a parameter range invokes the equations
under: the variable bound to the argument's class, and the two equalities of
the variable with itself that matching the head's declared arrow against itself
records. -/
def checkedRecord (bindings : Bindings) (name : String) (class_ : Atom) : Bindings :=
  ⟨(bindings.assign name class_).assignments,
    (bindings.assign name class_).equalities ++ [(name, name), (name, name)]⟩

theorem checkedRecord_lookup {bindings : Bindings} {name : String} {class_ : Atom}
    (unbound : bindings.lookup name = none) :
    (checkedRecord bindings name class_).lookup name = some class_ :=
  lookup_assign_of_lookup_none bindings name class_ unbound

theorem checkedRecord_self {bindings : Bindings} {name : String} {class_ : Atom}
    (noEqualities : bindings.equalities = []) :
    SelfEqualities name (checkedRecord bindings name class_) := by
  intro e member
  simp only [checkedRecord, Bindings.assign, noEqualities, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem checkedRecord_classValues {bindings : Bindings} {name : String} {class_ : Atom}
    (unbound : bindings.lookup name = none) (noEqualities : bindings.equalities = []) :
    (checkedRecord bindings name class_).classValues name = [class_] :=
  classValues_self (checkedRecord_self noEqualities) (checkedRecord_lookup unbound)

/-- The elements of the parameter-range arrow `(-> pre… $t post… $t)`. -/
abbrev paramArrowElements (pre post : List Atom) (name : String) : List Atom :=
  .symbol "->" :: ((pre ++ .var name :: post) ++ [.var name])

theorem paramArrow_shapes {pre post : List Atom} {name : String}
    (classes : ∀ position ∈ pre ++ post, ValueClass position) :
    ∀ atom ∈ paramArrowElements pre post name,
      (∃ label, atom = .symbol label) ∨ atom = .var name := by
  intro atom member
  simp only [paramArrowElements, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | (member | rfl | member) | rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ((classes atom (by simp [member])).symbol)
  · exact Or.inr rfl
  · exact Or.inl ((classes atom (by simp [member])).symbol)
  · exact Or.inr rfl

theorem paramArrow_count {pre post : List Atom} {name : String}
    (classes : ∀ position ∈ pre ++ post, ValueClass position) :
    (paramArrowElements pre post name).count (.var name) = 2 := by
  have absent : ∀ position ∈ pre ++ post, position ≠ .var name := by
    intro position member same
    obtain ⟨_, symbolic⟩ := (classes position member).symbol
    rw [same] at symbolic
    cases symbolic
  have preAbsent : pre.count (.var name) = 0 :=
    List.count_eq_zero.mpr fun member => absent _ (by simp [member]) rfl
  have postAbsent : post.count (.var name) = 0 :=
    List.count_eq_zero.mpr fun member => absent _ (by simp [member]) rfl
  simp [paramArrowElements, List.count_append, preAbsent, postAbsent]

/-- A head whose one declared arrow is written with symbols and one variable
evaluates to itself at that arrow, adding one equality of the variable with
itself per occurrence to a record that fixes the variable. -/
theorem evalAtom_head_selfMatch {space : Space} {dispatch : GroundedDispatch} {head : String}
    {params : List Atom} {range : Atom} {name : String}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (shapes : ∀ atom ∈ (.symbol "->" :: (params ++ [range]) : List Atom),
      (∃ label, atom = .symbol label) ∨ atom = .var name)
    (notEmpty : head ≠ "Empty")
    {bindings : Bindings} {fixed : Atom} (self : SelfEqualities name bindings)
    (assigned : bindings.lookup name = some fixed)
    {fuel : Nat} (enough : params.length + 6 ≤ fuel) (live : List Atom) :
    evalAtom space dispatch (.symbol head) (arrowType params range) bindings (fuel + 1) live =
      [(.symbol head, ⟨bindings.assignments, bindings.equalities ++
        List.replicate ((.symbol "->" :: (params ++ [range]) : List Atom).count (.var name))
          (name, name)⟩)] := by
  obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  have listed := matchAtomsList_self (.symbol "->" :: (params ++ [range])) [] f shapes
    (by simp only [List.length_cons, List.length_append, List.length_nil]; omega)
  rw [List.nil_append] at listed
  have noLoop : ∀ equalities : List (String × String),
      (⟨[], equalities⟩ : Bindings).hasLoop = false :=
    fun _ => Bindings.hasLoop_false_of_assignments_nil _ rfl
  have selfMatch : matchAtoms (arrowType params range) (arrowType params range) (f + 1) =
      [⟨[], List.replicate ((.symbol "->" :: (params ++ [range]) : List Atom).count (.var name))
        (name, name)⟩] := by
    unfold arrowType
    rw [matchAtoms]
    simp only [getMetaType, Atom.expressionType]
    have emptyRecord : Bindings.empty = ⟨[], []⟩ := rfl
    simp [emptyRecord, listed, noLoop]
  have merged : mergeBindings bindings ⟨[], List.replicate ((.symbol "->" :: (params ++ [range]) :
      List Atom).count (.var name)) (name, name)⟩ (f + 1) =
      [⟨bindings.assignments, bindings.equalities ++ List.replicate ((.symbol "->" ::
        (params ++ [range]) : List Atom).count (.var name)) (name, name)⟩] := by
    rw [mergeBindings]
    simp only [List.foldl_nil]
    exact mergeBindings_selfEqualities _ bindings fixed self assigned f (by
      have := List.count_le_length (a := Atom.var name) (l := (.symbol "->" :: (params ++ [range]) :
        List Atom))
      simp only [List.length_cons, List.length_append, List.length_nil] at this
      omega)
  have notAtomType : arrowType params range ≠ Atom.atomType := by simp [arrowType, Atom.atomType]
  have notSymbolType : arrowType params range ≠ Atom.symbolType := by
    simp [arrowType, Atom.symbolType]
  have matched : matchTypes (arrowType params range) (arrowType params range) bindings (f + 1) =
      [⟨bindings.assignments, bindings.equalities ++ List.replicate ((.symbol "->" ::
        (params ++ [range]) : List Atom).count (.var name)) (name, name)⟩] := by
    unfold matchTypes
    rw [if_neg (by simp [arrowType, Atom.undefinedType, Atom.atomType]), selfMatch,
      List.flatMap_singleton]
    exact merged
  rw [evalAtom_symbol notEmpty notAtomType notSymbolType bindings (f + 1) live]
  unfold typeCast
  simp only [rawTypeLookup, declared]
  rw [typeCast.typeCastLoop, matched]
  simp

/-- The head of a parameter range evaluates to itself at its declared arrow,
adding the arrow's two self-equalities to a record that fixes the variable. -/
theorem evalAtom_head_param {space : Space} {dispatch : GroundedDispatch} {head : String}
    {pre post : List Atom} {name : String}
    (declared : getAtomTypes space (.symbol head) =
      [arrowType (pre ++ .var name :: post) (.var name)])
    (classes : ∀ position ∈ pre ++ post, ValueClass position) (notEmpty : head ≠ "Empty")
    {bindings : Bindings} {fixed : Atom} (self : SelfEqualities name bindings)
    (assigned : bindings.lookup name = some fixed)
    {fuel : Nat} (enough : (pre ++ post).length + 7 ≤ fuel) (live : List Atom) :
    evalAtom space dispatch (.symbol head) (arrowType (pre ++ .var name :: post) (.var name))
        bindings (fuel + 1) live =
      [(.symbol head,
        ⟨bindings.assignments, bindings.equalities ++ [(name, name), (name, name)]⟩)] := by
  rw [evalAtom_head_selfMatch declared (paramArrow_shapes classes) notEmpty self assigned
    (by simp only [List.length_append, List.length_cons] at enough ⊢; omega) live]
  have count := paramArrow_count (name := name) classes
  simp only [paramArrowElements] at count
  rw [count]
  rfl

/-- A call of a parameter range on values: values before and after the
variable's position, and the value at it. -/
abbrev paramCall (head : String) (preValues postValues : List GroundedValue)
    (value : GroundedValue) : Atom :=
  .expression (.symbol head ::
    (preValues.map .grounded ++ .grounded value :: postValues.map .grounded))

/-- HE's applicability check of a parameter range on values, at `%Undefined%`:
the values at value-class positions pass and keep the record, the value at the
variable binds it once to its class, and the range meets `%Undefined%`. -/
theorem applicable_param {space : Space} {head : String} {pre post : List Atom}
    {name : String} {preValues postValues : List GroundedValue} {value : GroundedValue}
    (classes : ∀ position ∈ pre ++ post, ValueClass position)
    (passPre : classTests pre preValues = true) (passPost : classTests post postValues = true)
    (notUndefined : getGroundedType value ≠ Atom.undefinedType)
    (notAtom : getGroundedType value ≠ Atom.atomType)
    {bindings : Bindings} (unbound : bindings.lookup name = none)
    (noEqualities : bindings.equalities = []) (fuel : Nat) :
    checkIfFunctionTypeIsApplicable (paramCall head preValues postValues value)
        (arrowType (pre ++ .var name :: post) (.var name)) Atom.undefinedType space bindings
        (fuel + 3) =
      .inr [bindings.assign name (getGroundedType value)] := by
  have preClasses : ∀ position ∈ pre, ValueClass position :=
    fun position member => classes position (by simp [member])
  have postClasses : ∀ position ∈ post, ValueClass position :=
    fun position member => classes position (by simp [member])
  have bound : checkSuccesses (checkArgumentType space (.grounded value) (.var name) bindings
      (fuel + 2)) = [bindings.assign name (getGroundedType value)] := by
    rw [checkArgumentType_var space value unbound noEqualities notUndefined notAtom fuel]
    rfl
  have steps : CheckSteps space (fuel + 2) (pre ++ .var name :: post)
      (preValues.map .grounded ++ .grounded value :: postValues.map .grounded) bindings
      (bindings.assign name (getGroundedType value)) :=
    (checkSteps_values pre preValues preClasses passPre (by omega)).append
      (.cons bound (checkSteps_values post postValues postClasses passPost (by omega)))
  have loop := checkArgLoop_steps (expr := paramCall head preValues postValues value) steps [] 1
  have lengths : preValues.length + (postValues.length + 1) = pre.length + (post.length + 1) := by
    have preLength := ((classTests_iff pre preValues).mp passPre).length_eq
    have postLength := ((classTests_iff post postValues).mp passPost).length_eq
    omega
  have returned : matchTypes Atom.undefinedType (.var name)
      (bindings.assign name (getGroundedType value)) (fuel + 2) =
        [bindings.assign name (getGroundedType value)] := by
    simp [matchTypes]
  rw [checkIfFunctionTypeIsApplicable]
  simp only [getFunctionArgTypes_arrowType, getFunctionRetType_arrowType]
  simp [loop, lengths, returned]

/-- Values that pass the class tests of value-class positions are their own
values there, under any record. -/
theorem valueSelves {space : Space} {dispatch : GroundedDispatch} {record : Bindings} :
    ∀ (positions : List Atom) (values : List GroundedValue),
      (∀ position ∈ positions, ValueClass position) → classTests positions values = true →
      List.Forall₂ (fun param arg => ∀ m, 3 ≤ m → ∀ live,
        evalAtom space dispatch arg param record m live = [(arg, record)])
        positions (values.map .grounded)
  | [], [], _, _ => .nil
  | position :: positions, value :: values, classes, passes => by
      simp only [classTests, Bool.and_eq_true] at passes
      have positionClass := classes position (by simp)
      refine .cons ?_ (valueSelves positions values
        (fun other member => classes other (by simp [member])) passes.2)
      intro m bound live
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [evalAtom_grounded value positionClass.ground positionClass.notAtom
        positionClass.notGrounded record (by rw [positionClass.matchFuel_eq]; omega) live,
        if_pos passes.1]
  | [], _ :: _, _, passes => by simp [classTests] at passes
  | _ :: _, [], _, passes => by simp [classTests] at passes

/-- **HE's typed call of a parameter range, on values.** For a head whose one
signature is `(-> pre… $t post… $t)`, with `$t` written at one parameter and the
range and every other position a value class, called at `%Undefined%` on values
that pass the other positions' class tests: HE's check binds `$t` once to the
class of the argument at its position, and the answers are the results of the
head's equations, each evaluated once at `$t` under that binding. -/
theorem param_range_call {space : Space} {dispatch : GroundedDispatch} {head : String}
    {pre post : List Atom} {name : String} {preValues postValues : List GroundedValue}
    {value : GroundedValue}
    (declared : getAtomTypes space (.symbol head) =
      [arrowType (pre ++ .var name :: post) (.var name)])
    (classes : ∀ position ∈ pre ++ post, ValueClass position)
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notExecutable : dispatch.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (paramCall head preValues postValues value) = false)
    (passPre : classTests pre preValues = true) (passPost : classTests post postValues = true)
    (notUndefined : getGroundedType value ≠ Atom.undefinedType)
    (notAtom : getGroundedType value ≠ Atom.atomType)
    {bindings : Bindings} (unbound : bindings.lookup name = none)
    (noEqualities : bindings.equalities = [])
    {fuel : Nat} (enough : (pre ++ post).length + 8 ≤ fuel)
    {live : List Atom} {replies : ResultSet}
    (queried : rawQueryResults space (paramCall head preValues postValues value) (.var name)
      (checkedRecord bindings name (getGroundedType value)) (fuel + 1) live = replies)
    (nonempty : replies ≠ [])
    (plain : ∀ reply ∈ replies, ∀ body, reply.1 ≠ .expression [.symbol "function", body]) :
    evalAtom space dispatch (paramCall head preValues postValues value) Atom.undefinedType
        bindings (fuel + 4) live =
      keep (replies.flatMap fun reply =>
        ordinaryCallReturn (paramCall head preValues postValues value) reply.1 reply.2
          fun w b => evalAtom space dispatch w (.var name) b (fuel + 1) live) := by
  obtain ⟨g, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  have preClasses : ∀ position ∈ pre, ValueClass position :=
    fun position member => classes position (by simp [member])
  have postClasses : ∀ position ∈ post, ValueClass position :=
    fun position member => classes position (by simp [member])
  have undefinedClass : ValueClass Atom.undefinedType := Or.inr (Or.inr (Or.inr rfl))
  have bound : (bindings.assign name (getGroundedType value)).lookup name =
      some (getGroundedType value) := lookup_assign_of_lookup_none bindings name _ unbound
  have boundSelf : SelfEqualities name (bindings.assign name (getGroundedType value)) := by
    intro e member
    simp [Bindings.assign, noEqualities] at member
  have record := checkedRecord_classValues (class_ := getGroundedType value) unbound noEqualities
  have valueAtVariable : ∀ m, 3 ≤ m → ∀ live,
      evalAtom space dispatch (.grounded value) (.var name)
        (checkedRecord bindings name (getGroundedType value)) m live =
          [(.grounded value, checkedRecord bindings name (getGroundedType value))] := by
    intro m bound live
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
    rw [evalAtom_grounded_var value record (getGroundedType_ground value) notUndefined notAtom
      k live, if_pos rfl]
  have selves := List.rel_append (valueSelves (space := space) (dispatch := dispatch)
    (record := checkedRecord bindings name (getGroundedType value)) pre preValues preClasses
    passPre) (List.Forall₂.cons valueAtVariable (valueSelves post postValues postClasses passPost))
  have arguments : ∀ live, interpretArgs space dispatch
      (preValues.map .grounded ++ .grounded value :: postValues.map .grounded)
      (pre ++ .var name :: post) (checkedRecord bindings name (getGroundedType value))
      (g + 1 + 1) live =
        [(argumentPacket (preValues.map .grounded ++ .grounded value :: postValues.map .grounded),
          checkedRecord bindings name (getGroundedType value))] :=
    interpretArgs_selves selves (g + 1) (by
      have preLength := ((classTests_iff pre preValues).mp passPre).length_eq
      have postLength := ((classTests_iff post postValues).mp passPost).length_eq
      simp only [List.length_append, List.length_cons, List.length_map] at enough ⊢
      omega)
  have headEval : ∀ live, evalAtom space dispatch (.symbol head)
      (arrowType (pre ++ .var name :: post) (.var name)) (bindings.assign name (getGroundedType value))
      (g + 1 + 1) live =
        [(.symbol head, checkedRecord bindings name (getGroundedType value))] := fun live =>
    evalAtom_head_param declared classes notEmpty boundSelf bound (by omega) live
  have interpreted : ∀ live, interpretFunction space dispatch
      (paramCall head preValues postValues value) (arrowType (pre ++ .var name :: post) (.var name))
      (bindings.assign name (getGroundedType value)) (g + 1 + 2) live =
        [(paramCall head preValues postValues value,
          checkedRecord bindings name (getGroundedType value))] := by
    intro live
    have general := interpretFunction_general headEval (isEmptyOrError_symbol notEmpty)
      (getFunctionArgTypes_arrowType _ _) arguments live
    simp only [argumentsSucceeded_packet, argumentValues_packet, Bool.true_eq_false,
      if_false] at general
    exact general
  have returnType : callReturnType (.var name) = .var name := by
    simp [callReturnType, Atom.expressionType]
  have invoked : invoke space dispatch (.ordinary (callReturnType (.var name)))
      (paramCall head preValues postValues value)
      (checkedRecord bindings name (getGroundedType value)) (g + 1 + 2) live =
        replies.flatMap fun reply =>
          ordinaryCallReturn (paramCall head preValues postValues value) reply.1 reply.2
            fun w b => evalAtom space dispatch w (.var name) b (g + 1 + 1) live := by
    rw [returnType]
    exact invoke_queried notExecutable notInstruction (isErrorAtom_call notError _)
      queried nonempty plain none
  rw [evalAtom_expression (isEmptyOrError_call notError _) undefinedClass.notAtom
      undefinedClass.notExpression,
    interpretExpression_single declared
      (applicable_param classes passPre passPost notUndefined notAtom unbound noEqualities g)
      interpreted invoked]

/-- **The class check at the return of a parameter range has exactly HE's
answers.** When the equations of a parameter range answer values, each in a
record that keeps `$t` at the argument's class, and every answer has that
class, HE's answers are those values, each once. An answer of another class is
HE's `BadType` at `$t` (`evalAtom_grounded_var`), where the machine declines to
the canonical evaluator. -/
theorem param_range_classRun {space : Space} {dispatch : GroundedDispatch} {head : String}
    {pre post : List Atom} {name : String} {preValues postValues : List GroundedValue}
    {value : GroundedValue}
    (declared : getAtomTypes space (.symbol head) =
      [arrowType (pre ++ .var name :: post) (.var name)])
    (classes : ∀ position ∈ pre ++ post, ValueClass position)
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notExecutable : dispatch.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (paramCall head preValues postValues value) = false)
    (passPre : classTests pre preValues = true) (passPost : classTests post postValues = true)
    (notUndefined : getGroundedType value ≠ Atom.undefinedType)
    (notAtom : getGroundedType value ≠ Atom.atomType)
    {bindings : Bindings} (unbound : bindings.lookup name = none)
    (noEqualities : bindings.equalities = [])
    {fuel : Nat} (enough : (pre ++ post).length + 8 ≤ fuel)
    {live : List Atom} {answers : List (GroundedValue × Bindings)}
    (queried : rawQueryResults space (paramCall head preValues postValues value) (.var name)
      (checkedRecord bindings name (getGroundedType value)) (fuel + 1) live =
        answers.map fun answer => (.grounded answer.1, answer.2))
    (nonempty : answers ≠ [])
    (keeps : ∀ answer ∈ answers, answer.2.classValues name = [getGroundedType value])
    (sameClass : ∀ answer ∈ answers, getGroundedType answer.1 = getGroundedType value) :
    evalAtom space dispatch (paramCall head preValues postValues value) Atom.undefinedType
        bindings (fuel + 4) live =
      answers.map fun answer => (.grounded answer.1, answer.2) := by
  obtain ⟨g, rfl⟩ : ∃ k, fuel = k + 2 := ⟨fuel - 2, by omega⟩
  rw [param_range_call declared classes notEmpty notError notExecutable notInstruction passPre
    passPost notUndefined notAtom unbound noEqualities enough queried (by simpa using nonempty)
    (fun reply member body => by
      obtain ⟨answer, _, rfl⟩ := List.mem_map.mp member
      simp), List.flatMap_map]
  have each : ∀ answer ∈ answers,
      ordinaryCallReturn (paramCall head preValues postValues value) (.grounded answer.1)
        answer.2 (fun w b => evalAtom space dispatch w (.var name) b (g + 2 + 1) live) =
      [(.grounded answer.1, answer.2)] := by
    intro answer member
    rw [ordinaryCallReturn_grounded, evalAtom_grounded_var answer.1 (keeps answer member)
      (getGroundedType_ground value) (by rw [sameClass answer member]; exact notUndefined)
      (by rw [sameClass answer member]; exact notAtom) g live, if_pos (sameClass answer member)]
  rw [List.flatMap_congr each, ← List.map_eq_flatMap]
  exact keep_clean fun r member => by
    obtain ⟨answer, _, rfl⟩ := List.mem_map.mp member
    rfl

/-! ## HE's `if`: its range takes the expected type -/

theorem matchAtoms_symbol_var (label name : String) (fuel : Nat) :
    matchAtoms (.symbol label) (.var name) (fuel + 1) =
      [Bindings.empty.assign name (.symbol label)] := by
  have noLoop : (Bindings.empty.assign name (.symbol label)).hasLoop = false :=
    Bindings.hasLoop_false_of_assignment_vars_nil _ fun entry member => by
      simp [Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup] at member
      rw [member]
      rfl
  simp [matchAtoms, getMetaType, Atom.variableType, Atom.symbolType, noLoop]

/-- **A range written as a type variable takes a ground expected type**: the
range check binds the variable to it once. -/
theorem matchTypes_class_var {expected : Atom} (expectedClass : ValueClass expected)
    (notUndefined : expected ≠ Atom.undefinedType) (name : String) {bindings : Bindings}
    (unbound : bindings.lookup name = none) (noEqualities : bindings.equalities = [])
    (fuel : Nat) :
    matchTypes expected (.var name) bindings (fuel + 2) = [bindings.assign name expected] := by
  obtain ⟨label, rfl⟩ := expectedClass.symbol
  have notUndefined' : ¬label = "%Undefined%" := fun h => notUndefined (by rw [h]; rfl)
  have notAtom' : ¬label = "Atom" := fun h => expectedClass.notAtom (by rw [h]; rfl)
  unfold matchTypes
  rw [if_neg (by simp [Atom.undefinedType, Atom.atomType, notUndefined', notAtom']),
    matchAtoms_symbol_var, List.flatMap_singleton]
  exact mergeBindings_single_assign_fresh unbound noEqualities fuel

/-- HE's declaration of `if`: `(-> Bool Atom Atom $t)`. -/
abbrev ifArrow (name : String) : Atom :=
  arrowType [.symbol "Bool", Atom.atomType, Atom.atomType] (.var name)

/-- The record under which HE evaluates the chosen branch of an `if` expected
at `E`: the range variable bound to `E`, and its equality with itself from
matching `if`'s arrow against itself. -/
def ifRecord (bindings : Bindings) (name : String) (expected : Atom) : Bindings :=
  ⟨(bindings.assign name expected).assignments,
    (bindings.assign name expected).equalities ++ [(name, name)]⟩

theorem ifRecord_classValues {bindings : Bindings} {name : String} {expected : Atom}
    (unbound : bindings.lookup name = none) (noEqualities : bindings.equalities = []) :
    (ifRecord bindings name expected).classValues name = [expected] := by
  apply classValues_self
  · intro e member
    simp only [ifRecord, Bindings.assign, noEqualities, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rw [member]
  · exact lookup_assign_of_lookup_none bindings name expected unbound

/-- **HE's `if` at a value class evaluates its chosen branch at its range
variable, bound to that class.** With `if` declared `(-> Bool Atom Atom $t)`,
a condition that HE evaluates to `truth` at `Bool`, and branches checked once
at `Atom`, `(if c a b)` expected at a value class `E` binds `$t` to `E`, keeps
the branches as written, and answers the results of `if`'s equations on
`(if truth a b)`, each evaluated once at `$t` under that binding. -/
theorem if_call {space : Space} {dispatch : GroundedDispatch} {name : String}
    {condition truth chosen other expected : Atom}
    (declared : getAtomTypes space (.symbol "if") = [ifArrow name])
    (notExecutable : dispatch.isExecutable (.symbol "if") = false)
    (notInstruction : minimalInstruction (.expression [.symbol "if", truth, chosen, other]) = false)
    (expectedClass : ValueClass expected) (notUndefined : expected ≠ Atom.undefinedType)
    (conditionChecked : ArgumentChecked space (.symbol "Bool") condition)
    (chosenChecked : ArgumentChecked space Atom.atomType chosen)
    (otherChecked : ArgumentChecked space Atom.atomType other)
    {bindings : Bindings} (unbound : bindings.lookup name = none)
    (noEqualities : bindings.equalities = [])
    {fuel : Nat} (enough : 9 ≤ fuel)
    (decided : ∀ live, evalAtom space dispatch condition (.symbol "Bool")
      (ifRecord bindings name expected) fuel live =
        [(truth, ifRecord bindings name expected)])
    (running : isEmptyOrError truth = false)
    {live : List Atom} {replies : ResultSet}
    (queried : rawQueryResults space (.expression [.symbol "if", truth, chosen, other])
      (.var name) (ifRecord bindings name expected) (fuel + 1) live = replies)
    (nonempty : replies ≠ [])
    (plain : ∀ reply ∈ replies, ∀ body, reply.1 ≠ .expression [.symbol "function", body]) :
    evalAtom space dispatch (.expression [.symbol "if", condition, chosen, other]) expected
        bindings (fuel + 4) live =
      keep (replies.flatMap fun reply =>
        ordinaryCallReturn (.expression [.symbol "if", truth, chosen, other]) reply.1 reply.2
          fun w b => evalAtom space dispatch w (.var name) b (fuel + 1) live) := by
  obtain ⟨g, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  have boolClass : ValueClass (.symbol "Bool") := Or.inr (Or.inr (Or.inl rfl))
  have atomGround : atomVariables Atom.atomType = [] := rfl
  have bound : (bindings.assign name expected).lookup name = some expected :=
    lookup_assign_of_lookup_none bindings name expected unbound
  have boundSelf : SelfEqualities name (bindings.assign name expected) := by
    intro e member
    simp [Bindings.assign, noEqualities] at member
  have steps : CheckSteps space (g + 2) [.symbol "Bool", Atom.atomType, Atom.atomType]
      [condition, chosen, other] bindings bindings :=
    .cons (checkArgumentType_checked boolClass.ground conditionChecked bindings
        (by rw [boolClass.matchFuel_eq]; omega))
      (.cons (checkArgumentType_checked atomGround chosenChecked bindings (by simp [matchFuel, Atom.atomType]))
        (.cons (checkArgumentType_checked atomGround otherChecked bindings (by simp [matchFuel, Atom.atomType]))
          (.nil bindings)))
  have loop := checkArgLoop_steps (expr := .expression [.symbol "if", condition, chosen, other])
    steps [] 1
  have applicable : checkIfFunctionTypeIsApplicable
      (.expression [.symbol "if", condition, chosen, other]) (ifArrow name) expected space bindings
      (g + 1 + 2) = .inr [bindings.assign name expected] := by
    rw [checkIfFunctionTypeIsApplicable]
    simp only [getFunctionArgTypes_arrowType, getFunctionRetType_arrowType]
    simp [loop, matchTypes_class_var expectedClass notUndefined name unbound noEqualities g]
  have shapes : ∀ atom ∈ (.symbol "->" :: ([.symbol "Bool", Atom.atomType, Atom.atomType] ++
      [.var name]) : List Atom), (∃ label, atom = .symbol label) ∨ atom = .var name := by
    intro atom member
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr rfl
  have headEval : ∀ live, evalAtom space dispatch (.symbol "if") (ifArrow name)
      (bindings.assign name expected) (g + 1 + 1) live =
        [(.symbol "if", ifRecord bindings name expected)] := by
    intro live
    rw [evalAtom_head_selfMatch declared shapes (by decide) boundSelf bound (by simp; omega) live]
    have count : (.symbol "->" :: ([.symbol "Bool", Atom.atomType, Atom.atomType] ++ [.var name]) :
        List Atom).count (.var name) = 1 := by
      simp [Atom.atomType]
    rw [count]
    rfl
  have branches : ∀ live, interpretArgs space dispatch [chosen, other] [Atom.atomType, Atom.atomType]
      (ifRecord bindings name expected) (g + 1) live =
        [(argumentPacket [chosen, other], ifRecord bindings name expected)] := by
    intro live
    obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
    exact interpretArgs_cons_self
      (fun live => HECorrespondence.he_atom_demand space dispatch chosen _ (k + 1) live)
      (interpretArgs_cons_self
        (fun live => HECorrespondence.he_atom_demand space dispatch other _ k live)
        (fun live => interpretArgs_nil_self _ k live) ) live
  have arguments : ∀ live, interpretArgs space dispatch [condition, chosen, other]
      [.symbol "Bool", Atom.atomType, Atom.atomType] (ifRecord bindings name expected)
      (g + 1 + 1) live =
        [(argumentPacket [truth, chosen, other], ifRecord bindings name expected)] := by
    intro live
    exact interpretArgs_cons_value decided running branches live
  have interpreted : ∀ live, interpretFunction space dispatch
      (.expression [.symbol "if", condition, chosen, other]) (ifArrow name)
      (bindings.assign name expected) (g + 1 + 2) live =
        [(.expression [.symbol "if", truth, chosen, other], ifRecord bindings name expected)] := by
    intro live
    have general := interpretFunction_general headEval (isEmptyOrError_symbol (by decide))
      (getFunctionArgTypes_arrowType _ _) arguments live
    simp only [argumentsSucceeded_packet, argumentValues_packet, Bool.true_eq_false,
      if_false] at general
    exact general
  have returnType : callReturnType (.var name) = .var name := by
    simp [callReturnType, Atom.expressionType]
  have invoked : invoke space dispatch (.ordinary (callReturnType (.var name)))
      (.expression [.symbol "if", truth, chosen, other]) (ifRecord bindings name expected)
      (g + 1 + 2) live =
        replies.flatMap fun reply =>
          ordinaryCallReturn (.expression [.symbol "if", truth, chosen, other]) reply.1 reply.2
            fun w b => evalAtom space dispatch w (.var name) b (g + 1 + 1) live := by
    rw [returnType]
    exact invoke_queried notExecutable notInstruction (isErrorAtom_call (by decide) _)
      queried nonempty plain none
  rw [evalAtom_expression (isEmptyOrError_call (by decide) _) expectedClass.notAtom
      expectedClass.notExpression,
    interpretExpression_single declared applicable interpreted invoked]

/-- **A value branch of HE's `if` is cast at the expected class.** -/
theorem if_value_branch {space : Space} {dispatch : GroundedDispatch} (value : GroundedValue)
    {name : String} {expected : Atom} {record : Bindings} (expectedClass : ValueClass expected)
    (fixed : record.classValues name = [expected])
    (notUndefined : getGroundedType value ≠ Atom.undefinedType)
    (notAtom : getGroundedType value ≠ Atom.atomType) (fuel : Nat) (live : List Atom) :
    evalAtom space dispatch (.grounded value) (.var name) record (fuel + 3) live =
      if getGroundedType value = expected then [(.grounded value, record)]
      else [(mkError (.grounded value) (.badType (.var name) (getGroundedType value)), record)] :=
  evalAtom_grounded_var value fixed expectedClass.ground notUndefined notAtom fuel live

/-! ## The expected type at a typed head -/

/-- The results of a call's equations do not depend on a ground expected type. -/
theorem rawQueryResults_ground_expected {space : Space} {value expected other : Atom}
    {incoming : Bindings} {depth : Nat} {live : List Atom}
    (groundExpected : atomVariables expected = []) (groundOther : atomVariables other = []) :
    rawQueryResults space value expected incoming depth live =
      rawQueryResults space value other incoming depth live := by
  simp only [rawQueryResults, equationScope, groundExpected, groundOther]

/-- **A typed head's answers are the same at every expected type that accepts
its range**: the expected type does not reach its results, so it neither casts
them (a range `%Undefined%` or `Atom`) nor casts them again (a range equal to
the expected type). -/
theorem typed_call_expected {space : Space} {dispatch : GroundedDispatch} {head : String}
    {params args : List Atom} {range expected other : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notExecutable : dispatch.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (.expression (.symbol head :: args)) = false)
    (checked : List.Forall₂ (ArgumentChecked space) params args)
    (returns : accepts expected range = true) (returnsOther : accepts other range = true)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (otherNotAtom : other ≠ Atom.atomType) (otherNotExpression : other ≠ Atom.expressionType)
    (bindings : Bindings) {fuel : Nat} (enough : matchFuel (arrowType params range) ≤ fuel)
    (arguments : ∀ live, interpretArgs space dispatch args params bindings (fuel + 1) live =
      [(argumentPacket args, bindings)])
    {live : List Atom}
    (nonempty : rawQueryResults space (.expression (.symbol head :: args)) (callReturnType range)
      bindings (fuel + 1) live ≠ [])
    (plain : ∀ reply ∈ rawQueryResults space (.expression (.symbol head :: args))
      (callReturnType range) bindings (fuel + 1) live,
        ∀ body, reply.1 ≠ .expression [.symbol "function", body]) :
    evalAtom space dispatch (.expression (.symbol head :: args)) expected bindings (fuel + 4) live =
      evalAtom space dispatch (.expression (.symbol head :: args)) other bindings (fuel + 4) live := by
  rw [typed_call_once declared ground notEmpty notError notExecutable notInstruction checked
      returns notAtom notExpression bindings enough arguments rfl nonempty plain,
    typed_call_once declared ground notEmpty notError notExecutable notInstruction checked
      returnsOther otherNotAtom otherNotExpression bindings enough arguments rfl nonempty plain]

/-- A value checked at a ground position that accepts its class passes once and
binds nothing, with no mismatch. -/
theorem checkArgumentType_grounded (space : Space) (value : GroundedValue) {param : Atom}
    (ground : atomVariables param = []) (passes : accepts param (getGroundedType value) = true)
    (bindings : Bindings) {fuel : Nat} (enough : matchFuel param ≤ fuel) :
    checkArgumentType space (.grounded value) param bindings fuel = [.inr bindings] := by
  unfold checkArgumentType
  simp only [rawTypeLookup, getAtomTypes_grounded, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, matchTypes_accepted ground passes bindings enough]
  simp

/-- The argument checks of values at ground positions that accept their classes
keep the errors and the record. -/
theorem checkArgLoop_values {space : Space} {expr : Atom} {bindings : Bindings} {fuel : Nat} :
    ∀ (params : List Atom) (values : List GroundedValue),
      (∀ param ∈ params, atomVariables param = [] ∧ matchFuel param ≤ fuel) →
      classTests params values = true → ∀ (errors : List Atom) (idx : Nat),
        checkIfFunctionTypeIsApplicable.checkArgLoop (values.map .grounded) params expr
          [bindings] errors space fuel idx = (errors, [bindings])
  | [], [], _, _, errors, idx => by simp [checkIfFunctionTypeIsApplicable.checkArgLoop]
  | param :: params, value :: values, admissible, passes, errors, idx => by
      simp only [classTests, Bool.and_eq_true] at passes
      have first := admissible param (by simp)
      rw [List.map_cons, checkIfFunctionTypeIsApplicable.checkArgLoop]
      simp only [List.foldl_cons, List.foldl_nil,
        checkArgumentType_grounded space value first.1 passes.1 bindings first.2]
      simp only [List.nil_append]
      exact checkArgLoop_values params values
        (fun other member => admissible other (by simp [member])) passes.2 errors (idx + 1)
  | [], _ :: _, _, passes, _, _ => by simp [classTests] at passes
  | _ :: _, [], _, passes, _, _ => by simp [classTests] at passes

/-- **A typed head whose range the expected type rejects answers HE's
`BadType` naming the call**, whatever its equations would answer: on values
that pass its ground parameters, the range check fails, and the call's one
answer is `(Error call (BadType E R))`. A range of `Expression` at a value
class is such a range, so its results are not returned uncast. -/
theorem typed_call_rejected_range {space : Space} {dispatch : GroundedDispatch} {head : String}
    {params : List Atom} {values : List GroundedValue} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notError : head ≠ "Error")
    (passes : classTests params values = true)
    (groundExpected : atomVariables expected = [])
    (rejected : accepts expected range = false)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (bindings : Bindings) {fuel : Nat} (enough : matchFuel (arrowType params range) ≤ fuel)
    (live : List Atom) :
    evalAtom space dispatch (.expression (.symbol head :: values.map .grounded)) expected bindings
        (fuel + 3) live =
      [(mkError (.expression (.symbol head :: values.map .grounded)) (.badType expected range),
        bindings)] := by
  obtain ⟨paramsGround, rangeGround⟩ := arrowType_ground ground
  have loop := checkArgLoop_values (space := space)
    (expr := .expression (.symbol head :: values.map .grounded)) (bindings := bindings)
    (fuel := fuel) params values
    (fun param member => ⟨paramsGround param member,
      by have := matchFuel_param_lt (range := range) member; omega⟩) passes [] 1
  have lengths : (values.map Atom.grounded).length = params.length := by
    simp [((classTests_iff params values).mp passes).length_eq]
  have noReturn : matchTypes expected range bindings fuel = [] :=
    matchTypes_rejected groundExpected rangeGround rejected bindings fuel
  have applicable : checkIfFunctionTypeIsApplicable
      (.expression (.symbol head :: values.map .grounded)) (arrowType params range) expected
      space bindings (fuel + 1) =
        .inl [mkError (.expression (.symbol head :: values.map .grounded))
          (.badType expected range)] := by
    rw [checkIfFunctionTypeIsApplicable]
    simp only [getFunctionArgTypes_arrowType, getFunctionRetType_arrowType]
    simp [loop, lengths, noReturn]
  rw [evalAtom_expression (isEmptyOrError_call notError _) notAtom notExpression,
    interpretExpression_rejected declared (isFunctionType_arrowType params range) applicable]
  simp [keep, mkError, Atom.error, isErrorAtom]

/-! ## The static reading of where HE casts -/

/-- Where the answers of a return position meet the expected type: cast at it,
left as they are, or either, since the range is the expected type. -/
inductive Cast where
  | atExpected
  | none
  | neutral
  deriving DecidableEq, Repr

/-- The cast of one answer at a type, as HE casts a value. -/
def castAt (expected : Atom) (answer : Atom × Bindings) : ResultSet :=
  match answer.1 with
  | .grounded value =>
      if accepts expected (getGroundedType value) then [answer]
      else [(mkError (.grounded value) (.badType expected (getGroundedType value)), answer.2)]
  | _ => [answer]

/-- The treatment that a reading gives the machine's answers. -/
def treat (expected : Atom) : Cast → ResultSet → ResultSet
  | .atExpected, answers => keep (answers.flatMap (castAt expected))
  | .none, answers => answers
  | .neutral, answers => answers

theorem keep_errors_or_successes (results : ResultSet) :
    keep results = results.filter (fun r => !isErrorAtom r.1) ∨
      (results.filter (fun r => !isErrorAtom r.1) = [] ∧
        keep results = results.filter fun r => isErrorAtom r.1) := by
  unfold keep
  by_cases empty : (results.filter fun r => !isErrorAtom r.1) = []
  · right; simp [empty]
  · left
    have : (results.filter fun r => !isErrorAtom r.1).isEmpty = false := by
      cases h : results.filter (fun r => !isErrorAtom r.1) with
      | nil => exact absurd h empty
      | cons _ _ => rfl
    simp [this]

theorem filter_keep_successes (results : ResultSet) :
    (keep results).filter (fun r => !isErrorAtom r.1) =
      results.filter fun r => !isErrorAtom r.1 := by
  rcases keep_errors_or_successes results with same | ⟨empty, same⟩
  · rw [same, List.filter_filter]
    apply List.filter_congr
    intro r _
    simp
  · rw [same, empty, List.filter_filter]
    apply List.filter_eq_nil_iff.mpr
    intro r _
    simp

theorem filter_keep_errors_of_none (results : ResultSet)
    (empty : (results.filter fun r => !isErrorAtom r.1) = []) :
    (keep results).filter (fun r => isErrorAtom r.1) = results.filter fun r => isErrorAtom r.1 := by
  have same : keep results = results.filter fun r => isErrorAtom r.1 := by
    simp [keep, empty]
  rw [same, List.filter_filter]
  apply List.filter_congr
  intro r _
  simp

/-- The evaluator's filter depends only on the successes, and on the errors
where there is no success. -/
theorem keep_congr {first second : ResultSet}
    (successes : (first.filter fun r => !isErrorAtom r.1) =
      second.filter fun r => !isErrorAtom r.1)
    (errors : (second.filter fun r => !isErrorAtom r.1) = [] →
      (first.filter fun r => isErrorAtom r.1) = second.filter fun r => isErrorAtom r.1) :
    keep first = keep second := by
  unfold keep
  rw [successes]
  by_cases none : (second.filter fun r => !isErrorAtom r.1) = []
  · rw [errors none]
  · have full : (second.filter fun r => !isErrorAtom r.1).isEmpty = false := by
      cases h : second.filter (fun r => !isErrorAtom r.1) with
      | nil => exact absurd h none
      | cons _ _ => rfl
    simp only [full, Bool.not_false, if_true]

/-- The evaluator's filter of a concatenation of filtered parts is its filter of
the concatenation. -/
theorem keep_flatten_keep (parts : List ResultSet) :
    keep (parts.map keep).flatten = keep parts.flatten := by
  apply keep_congr
  · simp only [List.filter_flatten, List.map_map]
    congr 1
    apply List.map_congr_left
    intro part _
    exact filter_keep_successes part
  · intro none
    have each : ∀ part ∈ parts, (part.filter fun r => !isErrorAtom r.1) = [] := by
      intro part member
      rw [List.filter_flatten, List.flatten_eq_nil_iff] at none
      exact none _ (List.mem_map_of_mem member)
    simp only [List.filter_flatten, List.map_map]
    congr 1
    apply List.map_congr_left
    intro part member
    exact filter_keep_errors_of_none part (each part member)

theorem keep_keep (results : ResultSet) : keep (keep results) = keep results := by
  have := keep_flatten_keep [results]
  simpa using this

theorem flatMap_keep (items : List (Atom × Bindings)) (parts : Atom × Bindings → ResultSet) :
    keep (items.flatMap fun item => keep (parts item)) = keep (items.flatMap parts) := by
  rw [List.flatMap_def, List.flatMap_def, ← keep_flatten_keep (items.map parts), List.map_map]
  rfl

/-- **The static reading of where HE casts a return position's answers**, at a
ground expected type `E`: a value is cast at `E`; a typed head whose range is
`%Undefined%`, `Atom` or `E` keeps `E` from its results; an untyped head
passes `E` to the results of its equations, each read the same way; a call
read as neutral whose answers have `E`'s class may be read as cast at `E`. -/
inductive Reads (space : Space) (dispatch : GroundedDispatch) (expected : Atom) :
    Cast → Atom → Bindings → Nat → List Atom → Prop
  | value (value : GroundedValue) (bindings : Bindings) (fuel : Nat) (live : List Atom) :
      Reads space dispatch expected .atExpected (.grounded value) bindings (fuel + 2) live
  | typed {head : String} {params args : List Atom} {range : Atom} {bindings : Bindings}
      {fuel : Nat} {live : List Atom}
      (declared : getAtomTypes space (.symbol head) = [arrowType params range])
      (ground : atomVariables (arrowType params range) = [])
      (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
      (notExecutable : dispatch.isExecutable (.symbol head) = false)
      (notInstruction : minimalInstruction (.expression (.symbol head :: args)) = false)
      (checked : List.Forall₂ (ArgumentChecked space) params args)
      (stops : range = Atom.undefinedType ∨ range = Atom.atomType ∨ range = expected)
      (enough : matchFuel (arrowType params range) ≤ fuel)
      (arguments : ∀ live, interpretArgs space dispatch args params bindings (fuel + 1) live =
        [(argumentPacket args, bindings)])
      (nonempty : rawQueryResults space (.expression (.symbol head :: args))
        (callReturnType range) bindings (fuel + 1) live ≠ [])
      (plain : ∀ reply ∈ rawQueryResults space (.expression (.symbol head :: args))
        (callReturnType range) bindings (fuel + 1) live,
          ∀ body, reply.1 ≠ .expression [.symbol "function", body]) :
      Reads space dispatch expected (if range = expected then .neutral else .none)
        (.expression (.symbol head :: args)) bindings (fuel + 4) live
  | untyped {head : String} {args : List Atom} {reading : Cast} {bindings : Bindings}
      {fuel : Nat} {live : List Atom}
      (untyped : getAtomTypes space (.symbol head) = [Atom.undefinedType])
      (notError : head ≠ "Error")
      (notExecutable : dispatch.isExecutable (.symbol head) = false)
      (notInstruction : minimalInstruction (.expression (.symbol head :: args)) = false)
      (tuple : ∀ live, interpretTuple space dispatch (.expression (.symbol head :: args))
        bindings (fuel + 2) live = [(.expression (.symbol head :: args), bindings)])
      (nonempty : rawQueryResults space (.expression (.symbol head :: args)) expected bindings
        (fuel + 1) live ≠ [])
      (plain : ∀ reply ∈ rawQueryResults space (.expression (.symbol head :: args)) expected
        bindings (fuel + 1) live, ∀ body, reply.1 ≠ .expression [.symbol "function", body])
      (evaluated : ∀ reply ∈ rawQueryResults space (.expression (.symbol head :: args)) expected
        bindings (fuel + 1) live, reply.1 ≠ Atom.notReducible ∧ isEmptyOrError reply.1 = false)
      (clean : ∀ reply ∈ rawQueryResults space (.expression (.symbol head :: args)) expected
        bindings (fuel + 1) live, ∀ answer ∈ evalAtom space dispatch reply.1 Atom.undefinedType
          reply.2 (fuel + 1) live, isErrorAtom answer.1 = false)
      (results : ∀ reply ∈ rawQueryResults space (.expression (.symbol head :: args)) expected
        bindings (fuel + 1) live, Reads space dispatch expected reading reply.1 reply.2
          (fuel + 1) live) :
      Reads space dispatch expected reading (.expression (.symbol head :: args)) bindings
        (fuel + 4) live
  | neutralCast {atom : Atom} {bindings : Bindings} {fuel : Nat} {live : List Atom}
      (neutral : Reads space dispatch expected .neutral atom bindings fuel live)
      (classed : ∀ answer ∈ evalAtom space dispatch atom Atom.undefinedType bindings fuel live,
        castAt expected answer = [answer] ∧ isErrorAtom answer.1 = false) :
      Reads space dispatch expected .atExpected atom bindings fuel live


/-- **The static reading agrees with HE's interpreter.** Where it reads a call
at a value class `E` as cast at `E`, left as it is, or neutral, HE's
evaluation of the call at `E` is its evaluation at `%Undefined%`, which is what
the machine answers, followed by that treatment. -/
theorem Reads.sound {space : Space} {dispatch : GroundedDispatch} {expected : Atom}
    (expectedClass : ValueClass expected) {reading : Cast} {atom : Atom} {bindings : Bindings}
    {fuel : Nat} {live : List Atom}
    (reads : Reads space dispatch expected reading atom bindings fuel live) :
    evalAtom space dispatch atom expected bindings fuel live =
      treat expected reading
        (evalAtom space dispatch atom Atom.undefinedType bindings fuel live) := by
  have undefinedClass : ValueClass Atom.undefinedType := Or.inr (Or.inr (Or.inr rfl))
  induction reads with
  | value value bindings fuel live =>
      rw [evalAtom_grounded value expectedClass.ground expectedClass.notAtom
          expectedClass.notGrounded bindings (by rw [expectedClass.matchFuel_eq]; omega) live,
        evalAtom_grounded value undefinedClass.ground undefinedClass.notAtom
          undefinedClass.notGrounded bindings (by rw [undefinedClass.matchFuel_eq]; omega) live]
      have undefinedAccepts : accepts Atom.undefinedType (getGroundedType value) = true := by
        simp [accepts]
      rw [if_pos undefinedAccepts]
      simp only [treat, List.flatMap_cons, List.flatMap_nil, List.append_nil, castAt]
      split
      · exact (keep_clean (by simp [isErrorAtom])).symm
      · simp [keep, mkError, Atom.error, isErrorAtom]
  | typed declared ground notEmpty notError notExecutable notInstruction checked stops enough
      arguments nonempty plain =>
      rename_i head params args range bindings fuel live
      have returns : accepts expected range = true := by
        rcases stops with same | same | same <;> rw [same] <;> simp [accepts]
      have returnsUndefined : accepts Atom.undefinedType range = true := by simp [accepts]
      rw [typed_call_expected declared ground notEmpty notError notExecutable notInstruction
        checked returns returnsUndefined expectedClass.notAtom expectedClass.notExpression
        undefinedClass.notAtom undefinedClass.notExpression _ enough arguments nonempty plain]
      split <;> rfl
  | untyped untyped notError notExecutable notInstruction tuple nonempty plain evaluated clean
      results ih =>
      rename_i head args reading bindings fuel live
      have sameReplies : rawQueryResults space (.expression (.symbol head :: args))
          Atom.undefinedType bindings (fuel + 1) live =
            rawQueryResults space (.expression (.symbol head :: args)) expected bindings
              (fuel + 1) live :=
        rawQueryResults_ground_expected undefinedClass.ground expectedClass.ground
      rw [untyped_call_at_expected untyped notError notExecutable notInstruction
          expectedClass.notAtom expectedClass.notExpression tuple rfl nonempty plain,
        untyped_call_at_expected untyped notError notExecutable notInstruction
          undefinedClass.notAtom undefinedClass.notExpression tuple sameReplies nonempty plain]
      have each : ∀ reply ∈ rawQueryResults space (.expression (.symbol head :: args)) expected
          bindings (fuel + 1) live,
          ordinaryCallReturn (.expression (.symbol head :: args)) reply.1 reply.2
              (fun value b => evalAtom space dispatch value expected b (fuel + 1) live) =
            treat expected reading (ordinaryCallReturn (.expression (.symbol head :: args))
              reply.1 reply.2
                (fun value b => evalAtom space dispatch value Atom.undefinedType b (fuel + 1)
                  live)) := by
        intro reply member
        obtain ⟨notReducible, running⟩ := evaluated reply member
        rw [ordinaryCallReturn_evaluate _ _ _ _ notReducible running,
          ordinaryCallReturn_evaluate _ _ _ _ notReducible running]
        exact ih reply member
      have undefinedEach : ∀ reply ∈ rawQueryResults space (.expression (.symbol head :: args))
          expected bindings (fuel + 1) live,
          ordinaryCallReturn (.expression (.symbol head :: args)) reply.1 reply.2
              (fun value b => evalAtom space dispatch value Atom.undefinedType b (fuel + 1)
                live) =
            evalAtom space dispatch reply.1 Atom.undefinedType reply.2 (fuel + 1) live := by
        intro reply member
        obtain ⟨notReducible, running⟩ := evaluated reply member
        exact ordinaryCallReturn_evaluate _ _ _ _ notReducible running
      rw [List.flatMap_congr each]
      cases reading with
      | none => rfl
      | neutral => rfl
      | atExpected =>
          have cleanUndefined : ∀ answer ∈ (rawQueryResults space
              (.expression (.symbol head :: args)) expected bindings (fuel + 1) live).flatMap
                (fun reply => ordinaryCallReturn (.expression (.symbol head :: args)) reply.1
                  reply.2 (fun value b => evalAtom space dispatch value Atom.undefinedType b
                    (fuel + 1) live)),
              isErrorAtom answer.1 = false := by
            intro answer member
            obtain ⟨reply, replyMember, answerMember⟩ := List.mem_flatMap.mp member
            rw [undefinedEach reply replyMember] at answerMember
            exact clean reply replyMember answer answerMember
          simp only [treat]
          rw [flatMap_keep, keep_clean cleanUndefined, List.flatMap_assoc]
  | neutralCast neutral classed ih =>
      rw [ih]
      simp only [treat]
      rw [List.flatMap_congr (fun answer member => (classed answer member).1),
        List.flatMap_singleton', keep_clean (fun answer member => (classed answer member).2)]


/-! ## Controls -/

namespace Controls

open Mettapedia.GSLT.LanguageDef.Collections.HECorrespondence.Interpreter
  (symbol apply equation typed arrow)

/-- A number. -/
def num (n : ℤ) : Atom := .grounded (.int n)

/-- A string. -/
def str (text : String) : Atom := .grounded (.string text)

/-- `(: g (-> Number %Undefined%))`, `(= (g $x) "s")`, `(= (u $x) (g $x))`,
`(: k (-> Number Number))`, `(= (k $x) (u $x))`, `(: h (-> Number Expression))`
and `(= (h $x) 5)`. -/
def castSpace : Space := Space.ofList [
  typed "g" (arrow [symbol "Number", Atom.undefinedType]),
  equation (apply "g" [.var "x"]) (str "s"),
  equation (apply "u" [.var "x"]) (apply "g" [.var "x"]),
  typed "k" (arrow [symbol "Number", symbol "Number"]),
  equation (apply "k" [.var "x"]) (apply "u" [.var "x"]),
  typed "h" (arrow [symbol "Number", symbol "Expression"]),
  equation (apply "h" [.var "x"]) (num 5)]

/-- `(: + (-> Number Number Number))` and `(= (inc $x) (+ $x 1))`. -/
def nativeSpace : Space := Space.ofList [
  typed "+" (arrow [symbol "Number", symbol "Number", symbol "Number"]),
  equation (apply "inc" [.var "x"]) (apply "+" [.var "x", num 1])]

/-- `(: keep (-> Number $t $t))`, `(= (keep $n $acc) $acc)`,
`(: bad (-> Number $t $t))` and `(= (bad $n $acc) "s")`. -/
def paramSpace : Space := Space.ofList [
  typed "keep" (arrow [symbol "Number", .var "t", .var "t"]),
  equation (apply "keep" [.var "n", .var "acc"]) (.var "acc"),
  typed "bad" (arrow [symbol "Number", .var "t", .var "t"]),
  equation (apply "bad" [.var "n", .var "acc"]) (str "s")]

/-- HE's `if`, `(: if (-> Bool Atom Atom $t))` with its two equations,
`(= (v $x) (if True 5 "s"))` and `(= (w $x) (if True "s" 5))`. -/
def ifSpace : Space := Space.ofList [
  typed "if" (arrow [symbol "Bool", Atom.atomType, Atom.atomType, .var "t"]),
  equation (apply "if" [.grounded (.bool true), .var "then", .var "else"]) (.var "then"),
  equation (apply "if" [.grounded (.bool false), .var "then", .var "else"]) (.var "else"),
  equation (apply "v" [.var "x"]) (apply "if" [.grounded (.bool true), num 5, str "s"]),
  equation (apply "w" [.var "x"]) (apply "if" [.grounded (.bool true), str "s", num 5])]

/-- HE's answers for an atom at an expected type and budget, each answer's
bindings applied to it. -/
def answersAt (space : Space) (atom expected : Atom) (fuel : ℕ) : List Atom :=
  (evalAtom space GroundedDispatch.none atom expected Bindings.empty fuel).map
    fun answer => answer.2.applyFull answer.1 20

set_option maxHeartbeats 8000000 in
/-- **Through a typed head with range `%Undefined%`, HE does not cast**: `(u 1)`
expected at `Number` answers `"s"`, from every budget of twelve on. -/
theorem cast_through_undefined_range (fuel : ℕ) (enough : 12 ≤ fuel) :
    answersAt castSpace (apply "u" [num 1]) (symbol "Number") fuel = [str "s"] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 12 := ⟨fuel - 12, by omega⟩
  cbv

/-- Casting that answer at `Number` is the `BadType` error, which HE does not
answer. -/
theorem cast_would_be_error :
    evalAtom castSpace GroundedDispatch.none (str "s") (symbol "Number") Bindings.empty 2 [] =
      [(mkError (str "s") (.badType (symbol "Number") (symbol "String")), Bindings.empty)] := by
  have numberClass : ValueClass (symbol "Number") := Or.inl rfl
  have cast := evalAtom_grounded (space := castSpace) (dispatch := GroundedDispatch.none)
    (.string "s") numberClass.ground numberClass.notAtom numberClass.notGrounded Bindings.empty
    (fuel := 1) (by rw [numberClass.matchFuel_eq]) []
  rw [if_neg (by decide)] at cast
  exact cast

set_option maxHeartbeats 8000000 in
/-- The same `"s"` returns through `k`, whose range is `Number`, from every
budget of fifteen on. -/
theorem reply_through_undefined_range (fuel : ℕ) (enough : 15 ≤ fuel) :
    answersAt castSpace (apply "k" [num 1]) Atom.undefinedType fuel = [str "s"] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 15 := ⟨fuel - 15, by omega⟩
  cbv

/-- **A range of `Expression` at `Number` is HE's `BadType` naming the call**,
not an answer returned uncast. -/
theorem expression_range_rejected (fuel : ℕ) (enough : matchFuel
    (arrowType [symbol "Number"] (symbol "Expression")) ≤ fuel) :
    evalAtom castSpace GroundedDispatch.none (.expression [symbol "h", num 1]) (symbol "Number")
        Bindings.empty (fuel + 3) [] =
      [(mkError (.expression [symbol "h", num 1])
        (.badType (symbol "Number") (symbol "Expression")), Bindings.empty)] :=
  typed_call_rejected_range (values := [.int 1]) (by decide) rfl (by decide) (by decide) rfl
    (by decide) (by decide) (by decide) Bindings.empty enough []

/-- The error of a typed native whose range the expected type rejects names the
call: `(+ 1 1)` expected at `String`. -/
theorem native_range_names_call (fuel : ℕ) (enough : matchFuel
    (arrowType [symbol "Number", symbol "Number"] (symbol "Number")) ≤ fuel) :
    evalAtom nativeSpace GroundedDispatch.none (.expression [symbol "+", num 1, num 1])
        (symbol "String") Bindings.empty (fuel + 3) [] =
      [(mkError (.expression [symbol "+", num 1, num 1])
        (.badType (symbol "String") (symbol "Number")), Bindings.empty)] :=
  typed_call_rejected_range (values := [.int 1, .int 1]) (by decide) rfl (by decide) (by decide)
    rfl (by decide) (by decide) (by decide) Bindings.empty enough []

set_option maxHeartbeats 8000000 in
/-- Through the untyped `inc`, `(inc 1)` expected at `String` answers that
error, from every budget of eight on. -/
theorem untyped_native_range (fuel : ℕ) (enough : 8 ≤ fuel) :
    answersAt nativeSpace (apply "inc" [num 1]) (symbol "String") fuel =
      [mkError (apply "+" [num 1, num 1]) (.badType (symbol "String") (symbol "Number"))] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 8 := ⟨fuel - 8, by omega⟩
  cbv

/-- **A parameter range keeps a value of the argument's class**: `(keep 2 "s")`
answers `"s"`, at budget eleven and at budget forty. -/
theorem keep_string :
    answersAt paramSpace (apply "keep" [num 2, str "s"]) Atom.undefinedType 11 = [str "s"] ∧
      answersAt paramSpace (apply "keep" [num 2, str "s"]) Atom.undefinedType 40 = [str "s"] := by
  constructor <;> decide

/-- **An answer of another class is HE's `BadType` at the argument's class**:
`(bad 2 0)` answers `(Error "s" (BadType Number String))`, its `$t` read through
its bindings, at budget eleven and at budget forty. -/
theorem bad_number :
    answersAt paramSpace (apply "bad" [num 2, num 0]) Atom.undefinedType 11 =
        [mkError (str "s") (.badType (symbol "Number") (symbol "String"))] ∧
      answersAt paramSpace (apply "bad" [num 2, num 0]) Atom.undefinedType 40 =
        [mkError (str "s") (.badType (symbol "Number") (symbol "String"))] := by
  constructor <;> decide

/-- **`if`'s range takes the expected type**: `(v 1)`, whose chosen branch is
`5`, answers `5` at `Number`, at budget fifteen and at budget forty. -/
theorem if_branch_kept :
    answersAt ifSpace (apply "v" [num 1]) (symbol "Number") 15 = [num 5] ∧
      answersAt ifSpace (apply "v" [num 1]) (symbol "Number") 40 = [num 5] := by
  constructor <;> decide

/-- `(w 1)`, whose chosen branch is `"s"`, answers HE's `BadType` at `Number`, at
budget fifteen and at budget forty. -/
theorem if_branch_cast :
    answersAt ifSpace (apply "w" [num 1]) (symbol "Number") 15 =
        [mkError (str "s") (.badType (symbol "Number") (symbol "String"))] ∧
      answersAt ifSpace (apply "w" [num 1]) (symbol "Number") 40 =
        [mkError (str "s") (.badType (symbol "Number") (symbol "String"))] := by
  constructor <;> decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns
