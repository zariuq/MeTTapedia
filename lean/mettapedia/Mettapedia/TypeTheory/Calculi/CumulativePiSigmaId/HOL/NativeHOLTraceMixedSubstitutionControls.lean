import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceMixedSubstitution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeTraceReductionBoundary
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceObjectReductionBoundary

/-!
# Constant-bearing and retained-projection controls for mixed substitution

The actual native beta reduct retains the supplied trace section. Constants
are ordinary existing HOL native constants; no opaque result or evaluation
oracle is added. The projection control rejects replacing an old value by a
newly introduced empty-valued variable.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceMixedSubstitutionControls

open Presentation Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetContextualInterpretation (SetFamily Section)
open NativeTraceLambdaSemantics (Context)
open NativeHOLTraceDisplayedTerms (typeFamily)
open NativeHOLTraceMixedTermSemantics (Denotes)
open NativeHOLTraceMixedSubstitution
open ZFSetUniformListTraceTypeInterpretation (Value constant)

universe u

def emptyContext : Context.{u} 0 := Context.nil

def zeroTerm {n : Nat} : Tower.Tm n :=
  .const (FormationSensitiveHOLUniformList.symbolName Symbol.zero)

def successorTerm {n : Nat} : Tower.Tm n :=
  .const (FormationSensitiveHOLUniformList.symbolName Symbol.succ)

theorem successor_beta (a : ZFSet.{u})
    (headEquality : Tower.Head → Tower.Head → Prop) (root : RootComputation Tower.Head) :
    Step headEquality (.app (.lam (.app successorTerm (.var 0))) zeroTerm)
      (.app successorTerm zeroTerm : Tower.Tm 0) root ∧
    Denotes a emptyContext (.app (.lam (.app successorTerm (.var 0))) zeroTerm)
      (typeFamily a emptyContext count)
      (fun _ => ZFSetUniformListTraceTypeInterpretation.app
        (constant a Symbol.succ) (constant a Symbol.zero)) ∧
    Denotes a emptyContext (.app successorTerm zeroTerm)
      (typeFamily a emptyContext count)
      (fun _ => ZFSetUniformListTraceTypeInterpretation.app
        (constant a Symbol.succ) (constant a Symbol.zero)) := by
  have bodyMeaning : Denotes a (emptyContext.snoc (typeFamily a emptyContext count))
      (.app successorTerm (.var 0))
      (fun _ => ZFSetUniformListTraceTypeInterpretation.typeCode a count)
      (fun point => ZFSetUniformListTraceTypeInterpretation.app
        (constant a Symbol.succ) point.2) :=
    Denotes.object (NativeHOLTraceDisplayedTerms.Denotes.application
      (.constant Symbol.succ) (.variable 0 (NativeTraceLambdaSemantics.Denotes.var _ 0)))
  exact beta_square bodyMeaning (Denotes.object (.constant Symbol.zero)) headEquality root

/-- A variable has its actual projected set value even when its family index
has been transported along literal equality. -/
theorem lambda_variable_value {n : Nat} {context : Context.{u} n} {index : Fin n}
    {family : SetFamily context.Environment} {value : Section family}
    (meaning : NativeTraceLambdaSemantics.Denotes context (.var index) family value)
    (point : context.Environment) :
    (value point).1 = (context.projection index point).1 := by
  cases meaning
  rfl

theorem object_variable_value {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {index : Fin n} {type : HOL.Ty BaseSort} {value : context.Environment → Value a type}
    (meaning : NativeHOLTraceDisplayedTerms.Denotes a context (.var index) value)
    (point : context.Environment) :
    (value point).1 = (context.projection index point).1 := by
  cases meaning with
  | «variable» index variableMeaning => exact lambda_variable_value variableMeaning point

theorem mixed_variable_value {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {index : Fin n} {family : SetFamily context.Environment} {value : Section family}
    (meaning : Denotes a context (.var index) family value) (point : context.Environment) :
    (value point).1 = (context.projection index point).1 := by
  cases meaning with
  | «variable» => rfl
  | object meaning => exact object_variable_value meaning point

open NativeTraceReductionBoundary (context unitFamily nonemptyValue nonemptyValue_ne_empty)

def extendedContext : Context.{u} 2 := context.snoc unitFamily

def nilTerm {n : Nat} : Tower.Tm n :=
  .const (FormationSensitiveHOLUniformList.symbolName Symbol.nil)

/-- The beta binder is removed while the older contextual variable remains
at index one, beyond the unrelated fresh field at index zero. -/
theorem old_projection_under_new_binder (a : ZFSet.{u})
    (headEquality : Tower.Head → Tower.Head → Prop) (root : RootComputation Tower.Head) :
    Step headEquality (.app (.lam (.var (2 : Fin 3))) nilTerm) (.var (1 : Fin 2)) root ∧
      Denotes a extendedContext (.app (.lam (.var 2)) nilTerm)
        (fun point => context.family 0 point.1) (fun point => context.projection 0 point.1) ∧
      Denotes a extendedContext (.var 1)
        (fun point => context.family 0 point.1) (fun point => context.projection 0 point.1) :=
  beta_square (Denotes.variable
      (extendedContext.snoc (typeFamily a extendedContext sequence)) (1 : Fin 2).succ)
    (Denotes.object (.constant Symbol.nil)) headEquality root

theorem fresh_projection_is_wrong (a : ZFSet.{u}) :
    ¬ Denotes a extendedContext (.var 0)
      (fun point => context.family 0 point.1) (fun point => context.projection 0 point.1) := by
  intro meaning
  have equal := mixed_variable_value meaning
    ⟨PUnit.unit, ⟨∅, ZFSet.mem_singleton.mpr rfl⟩⟩
  exact nonemptyValue_ne_empty equal

namespace ObjectBoundary

open NativeHOLTraceObjectReductionBoundary

/-- The mixed judgment retains the real substituted section where the
smaller object-only judgment cannot retain its HOL type index. -/
theorem mixed_reduct_retains_section :
    Denotes (∅ : ZFSet.{u}) NativeHOLTraceObjectReductionBoundary.emptyContext identity
      (typeFamily ∅ NativeHOLTraceObjectReductionBoundary.emptyContext secondType)
      redexValue := by
  have reduced := instantiate (Denotes.object variable_denotes_second)
    (Denotes.object identity_denotes_first)
  apply reduced.change_value
  funext point
  exact (ZFSetUniformListTraceTypeInterpretation.app_lam
    (fun argument => bodyValue ⟨point, argument⟩) identityValue).symm

theorem mixed_closure_does_not_claim_object_closure :
    Denotes (∅ : ZFSet.{u}) NativeHOLTraceObjectReductionBoundary.emptyContext identity
      (typeFamily ∅ NativeHOLTraceObjectReductionBoundary.emptyContext secondType) redexValue ∧
      ¬ NativeHOLTraceDisplayedTerms.Denotes (∅ : ZFSet.{u})
        NativeHOLTraceObjectReductionBoundary.emptyContext identity redexValue :=
  ⟨mixed_reduct_retains_section, fun meaning => identity_not_second ⟨_, meaning⟩⟩

end ObjectBoundary

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceMixedSubstitutionControls
