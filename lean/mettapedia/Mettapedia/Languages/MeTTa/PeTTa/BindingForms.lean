import Mettapedia.TypeTheory.BindingDispatch
import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.EffectfulLet
import Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
import Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences
import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Binding, invocation and value occurrences

These contracts separate the proposed dispatch policy from relational pattern
binding. They are not a proof of the Prolog translator or the C runtime.
The matcher-to-body bridge accepts the environments produced by a matcher;
the separate ground-store controls use an implemented refinement operation.
Non-ground unification and evaluation of pattern subterms remain outside
this module's correspondence claim.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BindingForms

open Mettapedia.TypeTheory.BindingDispatch
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst subst)

/-- A fresh binder captures a previously computed value without evaluating
its syntax again. This connects the value-inertness contract to an actual
execution path, including values whose expression head names a function. -/
theorem captured_value_binding_returns (program : SpaceSemantics.Program)
    (state : Effects.State) (stored captured : String) (value : Atom)
    (fresh : captured ≠ stored) :
    Eval.PureReturns program [(stored, value)] state
      (.expression [.symbol "let", .var captured, .var stored, .var captured])
      state value := by
  apply Eval.let_returns program [(stored, value)]
    [(captured, value), (stored, value)] state state state
      (.var captured) (.var stored) (.var captured) value value
  · simpa [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup] using
      Eval.variable_returns program [(stored, value)] state stored
  · simp [SpaceSemantics.matchValue,
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, Ne.symm fresh]
  · simpa [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup] using
      Eval.variable_returns program [(captured, value), (stored, value)] state captured
open ValueOccurrences

/-- Quoted patterns keep literal constructor structure while capturing the
same completed value and using the existing relational binding rule. -/
theorem quoted_pattern_binding_returns (program : SpaceSemantics.Program)
    (bindings bound : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (before middle after : Effects.State) (pattern expression body value answer : Atom)
    (computed : Eval.PureReturns program bindings before expression middle value)
    (matched : Mettapedia.Languages.ProcessCalculi.MORK.matchAtom bindings pattern value = some bound)
    (returned : Eval.PureReturns program bound middle body after answer) :
    Eval.PureReturns program bindings before
      (.expression [.symbol "let", .expression [.symbol "quote", pattern], expression, body])
      after answer := by
  exact Eval.let_returns program bindings bound before middle after
    (.expression [.symbol "quote", pattern]) expression body value answer
    computed (by simpa using matched) returned

/-- A selected answer is matched once; each resulting environment executes
the authored body with its variables denoting values. -/
def relationalLet (program : Program) (answers : List Atom)
    (matcher : Atom → List Subst) (body : Atom) : List Atom :=
  answers.flatMap fun answer =>
    (matcher answer).flatMap fun environment => evalIn program environment body

/-- The corresponding materialized execution retains the body's occurrence
plan, even when an inserted value happens to spell a special form. -/
def materializedLet (program : Program) (answers : List Atom)
    (matcher : Atom → List Subst) (body : Atom) : List Atom :=
  answers.flatMap fun answer =>
    (matcher answer).flatMap fun environment =>
      evalPlanned program (planOf body) (subst environment body)

theorem materializedLet_eq_relationalLet (program : Program) (answers : List Atom)
    (matcher : Atom → List Subst) (body : Atom) :
    materializedLet program answers matcher body = relationalLet program answers matcher body := by
  simp only [materializedLet, relationalLet, evalPlanned_planOf_subst]

theorem relationalLet_append (program : Program) (left right : List Atom)
    (matcher : Atom → List Subst) (body : Atom) :
    relationalLet program (left ++ right) matcher body =
      relationalLet program left matcher body ++ relationalLet program right matcher body := by
  simp only [relationalLet, List.flatMap_append]

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline in
/-- The same logical variable cannot acquire two different ground values.
This is refinement of one variable identity, not lexical shadowing. -/
theorem repeated_ground_variable_conflicts (name : String) (a b : Nat) (different : a ≠ b) :
    refineRun Store.empty [(name, a), (name, b)] = none := by
  simp [refineRun, refineStep, Store.empty, different]

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline in
theorem repeated_ground_variable_agrees (name : String) (a : Nat) :
    ∃ store, refineRun Store.empty [(name, a), (name, a)] = some store ∧ store name = some a := by
  simp [refineRun, refineStep, Store.empty]

/-! A concrete call-resolution instance. Results retain order and duplicates.
The argument packet here is abstracted by a natural number; it is not a
surface-language parser or an arity model. -/

inductive Result where
  | number : Nat → Result
  | residual : String → Result → Result
  deriving DecidableEq, Repr

def declared : Runtime List String Result where
  lookup name _ := if name = "let" then some [.number 10, .number 20] else none
  data := .residual
  recover := id

def absent : Runtime List String Result where
  lookup _ _ := none
  data := .residual
  recover := id

def names : Nat → String := fun _ => "let"
def noValues : Fin 0 → Result := Fin.elim0

def writtenBinding : Expr List String Result 0 :=
  .bind (.value (.number 1)) (.value (.number 2))

def variableCall : Expr List String Result 0 :=
  .invoke (.dynamic 0) (.value (.number 1))

theorem written_binding_only : writtenBinding.eval declared names noValues = [.number 2] := rfl
theorem user_equations_only :
    variableCall.eval declared names noValues = [.number 10, .number 20] := by rfl
theorem unknown_call_is_data :
    variableCall.eval absent names noValues = [.residual "let" (.number 1)] := rfl

def knownLet : Nat → Option String := fun _ => some "let"

theorem knownLet_agrees : Agrees knownLet names := by
  intro index name h
  exact Option.some.inj h

theorem specialized_user_equations :
    (variableCall.specialize knownLet).eval declared names noValues =
      [.number 10, .number 20] := by
  rw [Expr.eval_specialize declared knownLet names knownLet_agrees]
  exact user_equations_only

/-- Name specialization is still valid after declarations change: the
resolver is a universally quantified argument, not baked into the plan. -/
theorem specialized_lookup_remains_live (runtime : Runtime List String Result) :
    (variableCall.specialize knownLet).eval runtime names noValues =
      variableCall.eval runtime names noValues :=
  Expr.eval_specialize runtime knownLet names knownLet_agrees _ _

theorem absence_is_not_a_stable_result :
    variableCall.eval absent names noValues ≠ variableCall.eval declared names noValues := by
  rw [unknown_call_is_data, user_equations_only]
  decide

def declaredFailure : Runtime List String Result where
  lookup _ _ := some []
  data := .residual
  recover := id

/-- Failure of a known relation must not fall through to unknown syntax. -/
theorem known_failure_is_not_data :
    variableCall.eval declaredFailure names noValues = [] := rfl

/-- Reclassifying a known dynamic head as binder syntax is observably wrong. -/
theorem reparsing_call_as_binder_changes_answers :
    variableCall.eval declared names noValues ≠ writtenBinding.eval declared names noValues := by
  rw [user_equations_only, written_binding_only]
  decide

/-- Any representation that merges these two occurrences loses information
needed by this observer. This applies regardless of how the representation
or its evaluator is implemented. -/
theorem role_erasure_cannot_preserve_both {Representation : Type}
    (encode : Expr List String Result 0 → Representation)
    (collision : encode variableCall = encode writtenBinding) :
    ¬ ∃ execute : Representation → List Result,
      execute (encode variableCall) = variableCall.eval declared names noValues ∧
      execute (encode writtenBinding) = writtenBinding.eval declared names noValues := by
  rintro ⟨execute, callEq, bindingEq⟩
  apply reparsing_call_as_binder_changes_answers
  exact callEq.symm.trans ((congrArg execute collision).trans bindingEq)

/-! An effectful instance detects handler loss and overly broad handlers. -/

def catches : Runtime (Except String) String Nat where
  lookup _ _ := some (.error "callee")
  data _ argument := argument
  recover
    | .ok value => .ok value
    | .error _ => .ok 0

def checkedCall : Expr (Except String) String Nat 0 :=
  .invoke (.dynamic 0) (.value 1)

theorem specialized_handler_is_preserved :
    (checkedCall.specialize knownLet).eval catches names Fin.elim0 = .ok 0 := rfl

def badArgument : Expr (Except String) String Nat 0 :=
  .invoke (.dynamic 0) (.action (.error "argument"))

theorem argument_error_is_outside_callee_handler :
    badArgument.eval catches names Fin.elim0 = .error "argument" := rfl

theorem dropping_handler_changes_result :
    checkedCall.eval catches names Fin.elim0 ≠
      checkedCall.eval { catches with recover := id } names Fin.elim0 := by decide

open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.EffectfulLet in
/-- A lexical binder's body error propagates in this semantics. A compiler
cannot replace it by a dispatch which adds the recovery used above. -/
theorem lexical_binding_does_not_add_dispatch_handler :
    (Term.letE (.lit 1) (.effect (.error "body")) :
      Term (Except String) Nat [] .atom).eval emptyEnv = .error "body" := rfl

end Mettapedia.Languages.MeTTa.PeTTa.BindingForms
