import Mettapedia.TypeTheory.Calculi.StagedScopedReflective.Presentation

/-!
# Quoted templates select their own substitution stage

These controls use the existing staged syntax and its substitution action.
They distinguish changing a runtime variable from filling a code-stage hole.
No surface syntax, drop evaluator, or new conversion equation is selected.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.StagedScopedReflective.QuotationConstruction

open NativeModalTyping

/-- A quoted open application. The variable is a code-stage hole. -/
def applicationTemplate : StagedReflectiveTm 0 1 :=
  .quote oneToZeroQuotation (.app (.const (.str .anonymous "f")) (.var 0))

/-- Change the one variable only at the selected stage, keeping its slot at
every other stage. -/
def replaceAt (selected : Nat) : NativeSub 1 1 :=
  fun stage index => if stage = selected then .const (.str .anonymous "a") else .var index

theorem ordinary_stage_leaves_template :
    nativeSubst (replaceAt 0) applicationTemplate = applicationTemplate :=
  rfl

theorem code_stage_fills_template :
    nativeSubst (replaceAt 1) applicationTemplate =
      .quote oneToZeroQuotation
        (.app (.const (.str .anonymous "f")) (.const (.str .anonymous "a"))) :=
  rfl

/-- The choice of stage has an observable effect on the retained source. -/
theorem stage_results_differ :
    nativeSubst (replaceAt 0) applicationTemplate ≠
      nativeSubst (replaceAt 1) applicationTemplate := by
  intro equal
  cases equal

/-- A template `lambda y. x` whose hole `x` lies outside the inner binder. -/
def nestedTemplate : StagedReflectiveTm 0 2 :=
  .quote oneToZeroQuotation (.lam (.var 1))

/-- Splice a free target-context variable into the template hole. -/
def freeVariable : TermFamily 1 := fun _ => .var 0

theorem filling_nested_template_preserves_free_variable :
    inst0 freeVariable nestedTemplate =
      (.quote oneToZeroQuotation (.lam (.var 1)) : StagedReflectiveTm 0 1) :=
  rfl

theorem filling_nested_template_does_not_capture :
    inst0 freeVariable nestedTemplate ≠
      (.quote oneToZeroQuotation (.lam (.var 0)) : StagedReflectiveTm 0 1) := by
  intro equal
  cases equal

/-- Reindexing the code and then filling its hole agrees with first filling
and then reindexing, including the binder and quotation stage. -/
theorem filling_commutes_with_reindex {source target stage : Nat}
    (substitution : NativeSub source target)
    (argument : TermFamily source)
    (template : StagedReflectiveTm stage (source + 1)) :
    nativeSubst substitution (inst0 argument template) =
      inst0 (fun current => nativeSubst substitution (argument current))
        (nativeSubst (nativeLiftSub substitution) template) :=
  subst_inst0 substitution argument template

end Mettapedia.TypeTheory.Calculi.StagedScopedReflective.QuotationConstruction
