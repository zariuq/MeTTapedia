import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeTraceBetaInstantiation

/-!
# Domain information is necessary for native trace reduction soundness

The unannotated trace denotation relation is not a substitute for a formed
native typing derivation. Actual equalities of set-coded product families can
forget their domains. The controls below use such an equality, not an arbitrary
semantic equivalence, and distinguish this boundary from the aligned beta
substitution theorem.

No semantic cast is installed as native conversion. These are controls for the
semantic relation alone; they do not establish a checker or runtime defect.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeTraceReductionBoundary

open Presentation
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetContextualInterpretation (SetFamily Section Extension)
open NativeTraceLambdaSemantics

universe u

def nonemptyValue : ZFSet.{u} := {∅}

theorem nonemptyValue_ne_empty : nonemptyValue.{u} ≠ ∅ := by
  intro equality
  have member : (∅ : ZFSet.{u}) ∈ nonemptyValue := by
    exact ZFSet.mem_singleton.mpr rfl
  rw [equality] at member
  exact ZFSet.notMem_empty _ member

/-- An actual inhabited context whose old variable is a nonempty set. -/
def context : Context.{u} 1 where
  Environment := PUnit
  family := fun _ _ => {nonemptyValue}
  projection := fun _ _ => ⟨nonemptyValue, ZFSet.mem_singleton.mpr rfl⟩

def unitFamily : SetFamily context.{u}.Environment := fun _ => {∅}

def emptyDomain : SetFamily context.{u}.Environment := fun _ => ∅

def oldBodyFamily : SetFamily (Extension emptyDomain.{u}) :=
  fun point => context.family 0 point.1

def unitCodomain : SetFamily (Extension (context.{u}.family 0)) := fun _ => {∅}

/-- The source product over an empty domain has exactly the empty trace. -/
theorem empty_product_code :
    ZFSetTraceContextual.piFamily emptyDomain.{u} oldBodyFamily = unitFamily := by
  funext environment
  apply (ZFSetTraceProducts.tracePiSet_eq_unit_iff ?_).mpr
  · intro value member
    exact False.elim (ZFSet.notMem_empty _ member)
  · intro value member
    exact False.elim (ZFSet.notMem_empty _ member)

/-- A nonempty domain with constant empty-set output has the very same code. -/
theorem unit_product_code :
    ZFSetTraceContextual.piFamily (context.{u}.family 0) unitCodomain = unitFamily := by
  funext environment
  apply (ZFSetTraceProducts.tracePiSet_eq_unit_iff ?_).mpr
  · intro value member
    rw [ZFSetContextualInterpretation.totalFamily_at _ _ ⟨value, member⟩]
    rfl
  · intro value member
    rw [ZFSetContextualInterpretation.totalFamily_at _ _ ⟨value, member⟩]
    exact fun _ hypothesis => hypothesis

theorem product_codes_equal :
    ZFSetTraceContextual.piFamily emptyDomain.{u} oldBodyFamily =
      ZFSetTraceContextual.piFamily (context.family 0) unitCodomain :=
  empty_product_code.trans unit_product_code.symm

/-- Equality of the product codes has not made their domains equal. -/
theorem domains_differ : emptyDomain.{u} ≠ context.family 0 := by
  intro equal
  have atPoint : (∅ : ZFSet.{u}) = {nonemptyValue} := congrFun equal PUnit.unit
  have member : nonemptyValue.{u} ∈ (∅ : ZFSet.{u}) :=
    atPoint.symm ▸ ZFSet.mem_singleton.mpr rfl
  exact ZFSet.notMem_empty _ member

def oldBodyValue : Section oldBodyFamily.{u} :=
  (context.snoc emptyDomain).projection 1

noncomputable def castFunction :
    Section (ZFSetTraceContextual.piFamily (context.{u}.family 0) unitCodomain) :=
  product_codes_equal ▸ ZFSetTraceContextual.lam oldBodyValue

theorem castFunction_denotes :
    Denotes context.{u} (.lam (.var 1))
      (ZFSetTraceContextual.piFamily (context.family 0) unitCodomain) castFunction :=
  (Denotes.lam (Denotes.var (context.snoc emptyDomain) 1)).cast product_codes_equal

theorem castFunction_empty (environment : context.{u}.Environment) :
    (castFunction environment).1 = ∅ := by
  let raw : ZFSet.{u} := (castFunction environment).1
  have member : raw ∈ ZFSetTraceContextual.piFamily
      (context.family 0) unitCodomain environment := (castFunction environment).2
  rw [congrFun unit_product_code environment] at member
  exact ZFSet.mem_singleton.mp member

def redex : NativeTraceLambdaSemantics.Tm 1 := .app (.lam (.var 1)) (.var 0)

def emptySection : Section unitFamily.{u} := fun _ => ⟨∅, ZFSet.mem_singleton.mpr rfl⟩

/-- The raw relation permits a denotation after the domain-forgetting cast. -/
theorem cast_redex_denotes_empty :
    Denotes context.{u} redex unitFamily emptySection := by
  have application := Denotes.app castFunction_denotes (Denotes.var context 0)
  apply application.change_value
  funext environment
  apply Subtype.ext
  change (ZFSetTraceContextual.piDecode (context.family 0) unitCodomain environment
    (castFunction environment) (context.projection 0 environment)).1 = ∅
  rw [ZFSetTraceContextual.piDecode_value, castFunction_empty,
    ZFSetTraceProducts.traceApp_empty]

/-- Its actual native beta reduct is the old contextual variable. -/
theorem redex_beta (headEquality : Tower.Head → Tower.Head → Prop)
    (root : RootComputation Tower.Head) :
    Step headEquality redex.erase (Presentation.Tm.var (0 : Fin 1)) root := by
  exact .betaPi (.var 1) (.var 0)

/-- An actual variable derivation retains its selected context family. -/
theorem variable_family {n : Nat} {selectedContext : Context.{u} n} {index : Fin n}
    {family : SetFamily selectedContext.Environment} {value : Section family}
    (meaning : Denotes selectedContext (.var index) family value) :
    family = selectedContext.family index := by
  cases meaning
  rfl

/-- The actual argument cannot supply a component at the lambda's original
empty domain. The aligned substitution theorem therefore does not authorize
this cast call. -/
theorem argument_not_at_original_domain :
    ¬ ∃ value : Section emptyDomain.{u}, Denotes context (.var 0) emptyDomain value := by
  rintro ⟨value, meaning⟩
  exact domains_differ (variable_family meaning)

/-- The reduct cannot denote the empty set in the cast result family. -/
theorem reduct_does_not_denote_empty :
    ¬ Denotes context.{u} (.var 0) unitFamily emptySection := by
  intro meaning
  have equality : ({∅} : ZFSet.{u}) = {nonemptyValue} :=
    congrFun (variable_family meaning) PUnit.unit
  have member : (∅ : ZFSet.{u}) ∈ ({nonemptyValue} : ZFSet.{u}) :=
    equality ▸ ZFSet.mem_singleton.mpr rfl
  exact nonemptyValue_ne_empty (ZFSet.mem_singleton.mp member).symm

/-- Ordinary aligned beta interpretation retains the actual nonempty value. -/
theorem aligned_redex_denotes_old :
    Denotes context.{u} redex (context.family 0) (context.projection 0) := by
  exact NativeTraceLambdaSemantics.beta
    (Denotes.var (context.snoc (context.family 0)) 1)
    (Denotes.var context 0)

/-- A blanket reduction-soundness law for raw denotations is false, even with
only an actual beta step and a literal equality of product codes. -/
theorem arbitrary_step_preservation_false
    (headEquality : Tower.Head → Tower.Head → Prop)
    (root : RootComputation Tower.Head) :
    ¬ (∀ (n : Nat) (selectedContext : Context.{u} n)
      (term result : NativeTraceLambdaSemantics.Tm n)
      (family : SetFamily selectedContext.Environment) (value : Section family),
      Step headEquality term.erase result.erase root →
      Denotes selectedContext term family value →
      Denotes selectedContext result family value) := by
  intro preserves
  exact reduct_does_not_denote_empty
    (preserves 1 context redex (.var 0) unitFamily emptySection
      (redex_beta headEquality root) cast_redex_denotes_empty)

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeTraceReductionBoundary
