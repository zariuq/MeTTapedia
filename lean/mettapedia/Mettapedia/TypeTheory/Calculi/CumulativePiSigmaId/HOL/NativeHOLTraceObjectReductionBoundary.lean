import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceDisplayedTerms
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeTraceReductionBoundary

/-!
# Equal HOL set codes do not identify object derivations

The object denotation judgment retains a HOL result type, but its variable
constructor consults the semantic context's set family. Different HOL types
can have literally equal, inhabited trace codes. A variable can consequently
be interpreted at either type although replacing it by an object term need
not preserve the smaller object judgment.

The controls concern the existing semantic relation, not formed native
typing, conversion, source HOL typing, or a runtime checker.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceObjectReductionBoundary

open Presentation Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetContextualInterpretation (SetFamily Section Extension)
open NativeTraceLambdaSemantics
open NativeHOLTraceDisplayedTerms
open ZFSetUniformListTraceTypeInterpretation

universe u

def emptyContext : Context.{u} 0 := Context.nil

abbrev firstType : HOL.Ty BaseSort := .arr element element

abbrev secondType : HOL.Ty BaseSort := .arr .prop firstType

def identity : Tower.Tm 0 := .lam (.var 0)

theorem first_code : typeCode (∅ : ZFSet.{u}) firstType = {∅} := by
  apply (ZFSetTraceProducts.tracePiSet_eq_unit_iff ?_).mpr
  · intro value member
    exact False.elim (ZFSet.notMem_empty _ member)
  · intro value member
    exact False.elim (ZFSet.notMem_empty _ member)

theorem second_code : typeCode (∅ : ZFSet.{u}) secondType = {∅} := by
  change ZFSetTraceProducts.tracePiSet _ (fun _ => typeCode (∅ : ZFSet.{u}) firstType) = _
  rw [first_code]
  apply (ZFSetTraceProducts.tracePiSet_eq_unit_iff ?_).mpr
  · intro value member
    rfl
  · intro value member
    exact fun _ hypothesis => hypothesis

theorem codes_equal : typeCode (∅ : ZFSet.{u}) firstType =
    typeCode (∅ : ZFSet.{u}) secondType := first_code.trans second_code.symm

theorem types_differ : firstType ≠ secondType := by
  intro equal
  have domains := (HOL.Ty.arr.inj equal).1
  cases domains

noncomputable def identityValue : Value (∅ : ZFSet.{u}) firstType :=
  ZFSetUniformListTraceTypeInterpretation.lam (fun argument => argument)

theorem identity_denotes_first :
    NativeHOLTraceDisplayedTerms.Denotes (∅ : ZFSet.{u}) emptyContext identity
      (fun _ => identityValue) := by
  change NativeHOLTraceDisplayedTerms.Denotes (∅ : ZFSet.{u}) emptyContext
    (.lam (.var 0)) (fun _ =>
      ZFSetUniformListTraceTypeInterpretation.lam (fun argument : Value ∅ element => argument))
  apply NativeHOLTraceDisplayedTerms.Denotes.abstraction
    (domain := element) (codomain := element) (bodyValue := fun point => point.2)
  exact .variable 0 (NativeTraceLambdaSemantics.Denotes.var _ 0)

/-- An interpreted identity over an inhabited domain must retain that domain's
set code in the body's variable family. This need not imply HOL type equality. -/
theorem identity_code_alignment {a : ZFSet.{u}} {domain codomain : HOL.Ty BaseSort}
    {value : emptyContext.Environment → Value a (.arr domain codomain)}
    (meaning : NativeHOLTraceDisplayedTerms.Denotes a emptyContext identity value)
    (argument : Value a domain) : typeCode a domain = typeCode a codomain := by
  cases meaning with
  | abstraction bodyMeaning =>
      cases bodyMeaning with
      | «variable» index variableMeaning =>
          have families := NativeTraceReductionBoundary.variable_family variableMeaning
          exact (congrFun families ⟨PUnit.unit, argument⟩).symm

theorem identity_not_second :
    ¬ ∃ value : emptyContext.Environment → Value (∅ : ZFSet.{u}) secondType,
      NativeHOLTraceDisplayedTerms.Denotes (∅ : ZFSet.{u}) emptyContext identity value := by
  rintro ⟨value, meaning⟩
  have codes := identity_code_alignment meaning ZFSetHOLTypeInterpretation.trueValue
  have truthMember : (ZFSetHOLTypeInterpretation.trueValue :
      Elements ZFSetHOLTypeInterpretation.truthCode.{u}).1 ∈
      typeCode (∅ : ZFSet.{u}) firstType := codes ▸
    ZFSetHOLTypeInterpretation.trueValue.2
  rw [first_code] at truthMember
  have equalEmpty := ZFSet.mem_singleton.mp truthMember
  exact NativeTraceReductionBoundary.nonemptyValue_ne_empty equalEmpty

noncomputable def bodyContext : Context.{u} 1 :=
  emptyContext.snoc (typeFamily (∅ : ZFSet.{u}) emptyContext firstType)

theorem body_family_equal : bodyContext.{u}.family 0 =
    typeFamily (∅ : ZFSet.{u}) bodyContext secondType := by
  funext point
  exact codes_equal

noncomputable def bodyValue : Section (typeFamily (∅ : ZFSet.{u}) bodyContext secondType) :=
  body_family_equal ▸ bodyContext.projection 0

theorem variable_denotes_second :
    NativeHOLTraceDisplayedTerms.Denotes (∅ : ZFSet.{u}) bodyContext
      (.var 0) bodyValue :=
  .variable 0 ((NativeTraceLambdaSemantics.Denotes.var bodyContext 0).cast body_family_equal)

def redex : Tower.Tm 0 := .app (.lam (.var 0)) identity

noncomputable def redexValue : emptyContext.{u}.Environment →
    Value (∅ : ZFSet.{u}) secondType := fun point =>
  ZFSetUniformListTraceTypeInterpretation.app
    (ZFSetUniformListTraceTypeInterpretation.lam (fun argument => bodyValue ⟨point, argument⟩))
    identityValue

theorem redex_denotes_second :
    NativeHOLTraceDisplayedTerms.Denotes (∅ : ZFSet.{u}) emptyContext redex redexValue := by
  exact .application
    (.abstraction (domain := firstType) (codomain := secondType)
      (bodyValue := bodyValue) variable_denotes_second) identity_denotes_first

theorem redex_beta (headEquality : Tower.Head → Tower.Head → Prop)
    (root : RootComputation Tower.Head) :
    Step headEquality redex identity root :=
  .betaPi (.var 0) identity

/-- Retaining only a HOL result index and semantic variable families is not
enough for a blanket object-denotation reduction law. -/
theorem arbitrary_object_step_preservation_false
    (headEquality : Tower.Head → Tower.Head → Prop)
    (root : RootComputation Tower.Head) :
    ¬ (∀ (n : Nat) (context : Context.{u} n) (type : HOL.Ty BaseSort)
      (term result : Tower.Tm n) (value : context.Environment → Value (∅ : ZFSet.{u}) type),
      Step headEquality term result root →
      NativeHOLTraceDisplayedTerms.Denotes (∅ : ZFSet.{u}) context term value →
      NativeHOLTraceDisplayedTerms.Denotes (∅ : ZFSet.{u}) context result value) := by
  intro preserves
  exact identity_not_second ⟨redexValue,
    preserves 0 emptyContext secondType redex identity redexValue
      (redex_beta headEquality root) redex_denotes_second⟩

def sourceIdentity : HOL.Term Symbol [] firstType := .lam (.var .vz)

theorem source_identity_represents :
    HOLNaturalDeductionNativeTranslation.represent sourceIdentity = some identity := rfl

/-- The unsound raw retyping is outside the actual typed HOL representation.
Its rejection follows from the existing representation square, not from a
second checker or a stipulated admission predicate. -/
theorem source_second_identity_unrepresentable
    (term : HOL.Term Symbol [] secondType) :
    HOLNaturalDeductionNativeTranslation.represent term ≠ some identity := by
  intro represented
  have meaning := NativeHOLTraceDisplayedTerms.representation_square
    (a := (∅ : ZFSet.{0})) term represented
    emptyContext.{0} (fun index => Fin.elim0 index)
    (fun _ {_} index => nomatch index) (by intro type index; nomatch index)
  exact identity_not_second.{0} ⟨_, meaning⟩

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceObjectReductionBoundary
