import Mettapedia.Languages.MM0.Kernel.Context

/-!
# MM0 expression typing

Typing retains unapplied binders until an expression is saturated. A bound
slot accepts a bound context variable of its declared sort; a regular slot
accepts a saturated expression. Dependencies constrain theorem substitution
and definition admission, not ordinary constructor application.

The signature here exposes previously admitted term declarations. Its
well-formedness and the admission of new declarations are separate judgments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

structure TermDecl where
  arguments : Context
  resultSort : Nat
  dependencies : Finset Nat

abbrev TermSignature := Nat → Option TermDecl
abbrev ExpressionType := Context × Nat

namespace Preterm

def boundSort? (context : Context) : Preterm → Option Nat
  | .var index =>
      match context[index]? with
      | some (.bound sort) => some sort
      | _ => none
  | _ => none

theorem boundSort_eq_some_iff (context : Context) (expression : Preterm) (sort : Nat) :
    boundSort? context expression = some sort ↔
      ∃ index, expression = .var index ∧ context[index]? = some (.bound sort) := by
  cases expression with
  | var index =>
      cases lookup : context[index]? with
      | none => simp [boundSort?, lookup]
      | some binder => cases binder <;> simp [boundSort?, lookup]
  | term index => simp [boundSort?]
  | app function argument => simp [boundSort?]

inductive HasType (signature : TermSignature) (context : Context) :
    Preterm → Context → Nat → Prop where
  | var {index : Nat} {binder : Binder} : context[index]? = some binder →
      HasType signature context (.var index) [] binder.sort
  | term {index : Nat} {declaration : TermDecl} : signature index = some declaration →
      HasType signature context (.term index) declaration.arguments declaration.resultSort
  | bound {function : Preterm} {index sort result : Nat} {remaining : Context} :
      HasType signature context function (.bound sort :: remaining) result →
      context[index]? = some (.bound sort) →
      HasType signature context (.app function (.var index)) remaining result
  | regular {function argument : Preterm} {sort result : Nat}
      {dependencies : Finset Nat} {remaining : Context} :
      HasType signature context function (.regular sort dependencies :: remaining) result →
      HasType signature context argument [] sort →
      HasType signature context (.app function argument) remaining result

def infer (signature : TermSignature) (context : Context) : Preterm → Option ExpressionType
  | .var index => do
      let binder ← context[index]?
      pure ([], binder.sort)
  | .term index => do
      let declaration ← signature index
      pure (declaration.arguments, declaration.resultSort)
  | .app function argument => do
      let (arguments, result) ← infer signature context function
      match arguments with
      | [] => none
      | .bound sort :: remaining =>
          if boundSort? context argument = some sort then some (remaining, result) else none
      | .regular sort _ :: remaining =>
          if infer signature context argument = some ([], sort) then some (remaining, result)
          else none

theorem HasType.eval {signature : TermSignature} {context remaining : Context}
    {expression : Preterm} {sort : Nat} (typing : HasType signature context expression remaining sort) :
    infer signature context expression = some (remaining, sort) := by
  induction typing with
  | var lookup => simp [infer, lookup]
  | term lookup => simp [infer, lookup]
  | bound _ lookup ih => simp [infer, ih, boundSort?, lookup]
  | regular _ _ ihFunction ihArgument => simp [infer, ihFunction, ihArgument]

theorem infer_sound {signature : TermSignature} {context remaining : Context}
    {expression : Preterm} {sort : Nat}
    (accepted : infer signature context expression = some (remaining, sort)) :
    HasType signature context expression remaining sort := by
  induction expression generalizing remaining sort with
  | var index =>
      cases lookup : context[index]? with
      | none => simp [infer, lookup] at accepted
      | some binder =>
          simp [infer, lookup] at accepted
          rcases accepted with ⟨rfl, rfl⟩
          exact .var lookup
  | term index =>
      cases lookup : signature index with
      | none => simp [infer, lookup] at accepted
      | some declaration =>
          simp [infer, lookup] at accepted
          rcases accepted with ⟨rfl, rfl⟩
          exact .term lookup
  | app function argument ihFunction ihArgument =>
      cases functionResult : infer signature context function with
      | none => simp [infer, functionResult] at accepted
      | some type =>
          rcases type with ⟨arguments, result⟩
          cases arguments with
          | nil => simp [infer, functionResult] at accepted
          | cons binder rest =>
              cases binder with
              | bound expected =>
                  by_cases bound : boundSort? context argument = some expected
                  · simp [infer, functionResult, bound] at accepted
                    rcases accepted with ⟨rfl, rfl⟩
                    obtain ⟨index, rfl, lookup⟩ := (boundSort_eq_some_iff _ _ _).mp bound
                    exact .bound (ihFunction functionResult) lookup
                  · simp [infer, functionResult, bound] at accepted
              | regular expected dependencies =>
                  by_cases regular : infer signature context argument = some ([], expected)
                  · simp [infer, functionResult, regular] at accepted
                    rcases accepted with ⟨rfl, rfl⟩
                    exact .regular (ihFunction functionResult) (ihArgument regular)
                  · simp [infer, functionResult, regular] at accepted

theorem infer_eq_some_iff (signature : TermSignature) (context : Context)
    (expression : Preterm) (remaining : Context) (sort : Nat) :
    infer signature context expression = some (remaining, sort) ↔
      HasType signature context expression remaining sort := ⟨infer_sound, HasType.eval⟩

theorem HasType.deterministic {signature : TermSignature} {context first second : Context}
    {expression : Preterm} {firstSort secondSort : Nat}
    (left : HasType signature context expression first firstSort)
    (right : HasType signature context expression second secondSort) :
    first = second ∧ firstSort = secondSort := by
  exact Prod.mk.inj (Option.some.inj (left.eval.symm.trans right.eval))

theorem infer_none_iff (signature : TermSignature) (context : Context) (expression : Preterm) :
    infer signature context expression = none ↔
      ¬ ∃ remaining sort, HasType signature context expression remaining sort := by
  constructor
  · intro refused ⟨remaining, sort, typing⟩
    have accepted := typing.eval
    rw [refused] at accepted
    contradiction
  · intro noType
    cases result : infer signature context expression with
    | none => rfl
    | some type => exact False.elim (noType ⟨type.1, type.2, infer_sound result⟩)

inductive FitsBinder (signature : TermSignature) (context : Context) : Preterm → Binder → Prop where
  | bound {index sort : Nat} : context[index]? = some (.bound sort) →
      FitsBinder signature context (.var index) (.bound sort)
  | regular {expression : Preterm} {sort : Nat} {dependencies : Finset Nat} :
      HasType signature context expression [] sort →
      FitsBinder signature context expression (.regular sort dependencies)

def checkBinder (signature : TermSignature) (context : Context) (expression : Preterm) : Binder → Bool
  | .bound sort => decide (boundSort? context expression = some sort)
  | .regular sort _ => decide (infer signature context expression = some ([], sort))

theorem checkBinder_iff (signature : TermSignature) (context : Context)
    (expression : Preterm) (binder : Binder) :
    checkBinder signature context expression binder = true ↔
      FitsBinder signature context expression binder := by
  cases binder with
  | bound sort =>
      simp only [checkBinder, decide_eq_true_eq, boundSort_eq_some_iff]
      constructor
      · rintro ⟨index, rfl, lookup⟩; exact .bound lookup
      · intro fits; cases fits with
        | bound lookup => exact ⟨_, rfl, lookup⟩
  | regular sort dependencies =>
      simp only [checkBinder, decide_eq_true_eq, infer_eq_some_iff]
      constructor
      · exact FitsBinder.regular
      · intro fits; cases fits with
        | regular typing => exact typing

theorem HasType.support_exists {signature : TermSignature} {context remaining : Context}
    {expression : Preterm} {sort : Nat} (typing : HasType signature context expression remaining sort) :
    ∃ support, Supports context expression support := by
  induction typing with
  | var lookup =>
      rename_i binder
      cases binder with
      | bound sort => exact ⟨_, .bound lookup⟩
      | regular sort dependencies => exact ⟨_, .regular lookup⟩
  | term => exact ⟨_, .term _⟩
  | bound _ lookup ih =>
      obtain ⟨support, supported⟩ := ih
      exact ⟨_, .app supported (.bound lookup)⟩
  | regular _ _ ihFunction ihArgument =>
      obtain ⟨left, functionSupport⟩ := ihFunction
      obtain ⟨right, argumentSupport⟩ := ihArgument
      exact ⟨_, .app functionSupport argumentSupport⟩

theorem FitsBinder.support_exists {signature : TermSignature} {context : Context}
    {expression : Preterm} {binder : Binder} (fits : FitsBinder signature context expression binder) :
    ∃ support, Supports context expression support := by
  cases fits with
  | bound lookup => exact ⟨_, .bound lookup⟩
  | regular typing => exact typing.support_exists

end Preterm

end Mettapedia.Languages.MM0.Kernel
