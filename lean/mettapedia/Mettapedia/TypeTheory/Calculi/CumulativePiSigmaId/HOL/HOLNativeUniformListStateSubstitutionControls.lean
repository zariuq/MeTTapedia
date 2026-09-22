import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeUniformListStateSubstitution

/-!
# State-qualified substitution of retained native proof applications

An actual compiled universal elimination contains both a hypothesis occurrence
and an object variable. Replacing its object by zero or successor-zero produces
different native outputs, each justified by the existing trace compiler
semantics. A proof-binder control retains an older hypothesis rather than
returning the newly supplied proof argument.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler.UniformListStateSubstitutionControls

open Presentation Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open FormationSensitiveHOLInterface
open NativeTraceLambdaSemantics (Context)
open UniformListSemantics UniformListStateSubstitution

universe u

abbrev gamma : SourceContext := [count]
def argument : HOL.Term Symbol gamma count := .var .vz
def body : Formula (count :: gamma) := .eq (.var .vz) (.var .vz)
def premise : Formula gamma := .all body
def conclusion : Formula gamma := HOL.instantiate argument body
def source : HOL.ProofSyntax Symbol [premise] conclusion := .allE argument (.hyp 0)
def objects : Sub Tower.Head gamma.length 2 := fun _ => .var 1
def hypotheses : Fin ([premise] : List (Formula gamma)).length → Tower.Tm 2 := fun _ => .var 0
def retained : Tower.Tm 2 := .app (.var 0) (.var 1)

theorem retained_compilation :
    compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations source objects hypotheses = some retained := rfl

def universalProof {n : Nat} : Tower.Tm n := .lam FormationSensitiveHOLLeibnizDerived.reflTerm
def zeroTerm {n : Nat} : Tower.Tm n :=
  .const (FormationSensitiveHOLUniformList.symbolName Symbol.zero)
def oneTerm {n : Nat} : Tower.Tm n :=
  .app (.const (FormationSensitiveHOLUniformList.symbolName Symbol.succ)) zeroTerm
def replacements (term : Tower.Tm 0) : Sub Tower.Head 2 0 :=
  Fin.cases universalProof (fun _ => term)

def targetState (a : ZFSet.{u}) (term : Tower.Tm 0)
    (value : ZFSetUniformListTraceTypeInterpretation.Value a count)
    (meaning : NativeHOLTraceDisplayedTerms.Denotes a Context.nil term (fun _ => value)) :
    State a (fun index => subst (replacements term) (objects index)) where
  context := Context.nil
  valuation := fun _ => ZFSetUniformListTraceTermInterpretation.extend
    ZFSetUniformListTraceTermInterpretation.emptyValuation value
  objectsDenote := by
    intro type index
    cases index with
    | vz => exact meaning
    | vs prior => nomatch prior

theorem universal_denotes (a : ZFSet.{u}) (term : Tower.Tm 0)
    (value : ZFSetUniformListTraceTypeInterpretation.Value a count)
    (meaning : NativeHOLTraceDisplayedTerms.Denotes a Context.nil term (fun _ => value)) :
    Denotes a (targetState a term value meaning) universalProof premise := by
  apply UniformListSemantics.universalIntro
  exact UniformListSemantics.reflexivity a
    (objectExtension a (targetState a term value meaning) count)
    (term := (.var .vz : HOL.Term Symbol (count :: gamma) count)) rfl rfl

theorem substituted_output_denotes (a : ZFSet.{u}) (term : Tower.Tm 0)
    (value : ZFSetUniformListTraceTypeInterpretation.Value a count)
    (meaning : NativeHOLTraceDisplayedTerms.Denotes a Context.nil term (fun _ => value)) :
    Denotes a (targetState a term value meaning) (subst (replacements term) retained)
      conclusion := by
  apply retained_substitution source retained_compilation (replacements term)
  intro index
  refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index
  exact universal_denotes a term value meaning

theorem zero_object_denotes (a : ZFSet.{u}) :
    NativeHOLTraceDisplayedTerms.Denotes a Context.nil zeroTerm
      (fun _ => ZFSetUniformListTraceTypeInterpretation.constant a Symbol.zero) :=
  .constant Symbol.zero

theorem one_object_denotes (a : ZFSet.{u}) :
    NativeHOLTraceDisplayedTerms.Denotes a Context.nil oneTerm
      (fun _ => ZFSetUniformListTraceTypeInterpretation.app
        (ZFSetUniformListTraceTypeInterpretation.constant a Symbol.succ)
        (ZFSetUniformListTraceTypeInterpretation.constant a Symbol.zero)) :=
  .application (.constant Symbol.succ) (.constant Symbol.zero)

theorem zero_substituted_output (a : ZFSet.{u}) :
    Denotes a (targetState a zeroTerm _ (zero_object_denotes a))
      (subst (replacements zeroTerm) retained) conclusion :=
  substituted_output_denotes a zeroTerm _ (zero_object_denotes a)

theorem one_substituted_output (a : ZFSet.{u}) :
    Denotes a (targetState a oneTerm _ (one_object_denotes a))
      (subst (replacements oneTerm) retained) conclusion :=
  substituted_output_denotes a oneTerm _ (one_object_denotes a)

theorem distinct_actual_outputs :
    subst (replacements zeroTerm) retained ≠ subst (replacements oneTerm) retained := by
  decide

theorem distinct_object_values (a : ZFSet.{u}) :
    ZFSetUniformListTraceTypeInterpretation.constant a Symbol.zero ≠
      ZFSetUniformListTraceTypeInterpretation.app
        (ZFSetUniformListTraceTypeInterpretation.constant a Symbol.succ)
        (ZFSetUniformListTraceTypeInterpretation.constant a Symbol.zero) := by
  intro equality
  have decoded := congrArg ZFSetUniformListModel.decodeCount equality
  simp [ZFSetUniformListTraceTypeInterpretation.constant] at decoded

theorem outputs_are_actual_applications :
    subst (replacements zeroTerm) retained = .app universalProof zeroTerm ∧
      subst (replacements oneTerm) retained = .app universalProof oneTerm := ⟨rfl, rfl⟩

def closedUniversal : Formula [] := .all (σ := count) (.eq (.var .vz) (.var .vz))

theorem object_binder_compiled :
    compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations source (liftSub (Fin.elim0 : Sub Tower.Head 0 1))
        (fun _ => .var 1) = some (.app (.var 1) (.var 0) : Tower.Tm 2) := rfl

/-- Opening an object binder replaces the actual object argument while the
older universal-proof occurrence remains the same native variable. -/
theorem object_binder_zero_keeps_old_proof (a : ZFSet.{u}) :
    Denotes a
      (instantiateObjectState
        (UniformListSemantics.Controls.assumptionState a [closedUniversal])
        (NativeHOLTraceDisplayedTerms.Denotes.constant Symbol.zero))
      (.app (.var 0) zeroTerm) conclusion := by
  let state := UniformListSemantics.Controls.assumptionState a [closedUniversal]
  apply object_binder_instantiation source object_binder_compiled state
    (NativeHOLTraceDisplayedTerms.Denotes.constant Symbol.zero)
  intro index
  refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index
  exact object_instance_old_proof state
    (NativeHOLTraceDisplayedTerms.Denotes.constant Symbol.zero)
    (UniformListSemantics.Controls.assumptionHypotheses a [closedUniversal] 0)

theorem object_binder_one_keeps_old_proof (a : ZFSet.{u}) :
    Denotes a
      (instantiateObjectState
        (UniformListSemantics.Controls.assumptionState a [closedUniversal])
        (NativeHOLTraceDisplayedTerms.Denotes.application
          (.constant Symbol.succ) (.constant Symbol.zero)))
      (.app (.var 0) oneTerm) conclusion := by
  let state := UniformListSemantics.Controls.assumptionState a [closedUniversal]
  apply object_binder_instantiation source object_binder_compiled state
    (NativeHOLTraceDisplayedTerms.Denotes.application
      (.constant Symbol.succ) (.constant Symbol.zero))
  intro index
  refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index
  exact object_instance_old_proof state
    (NativeHOLTraceDisplayedTerms.Denotes.application
      (.constant Symbol.succ) (.constant Symbol.zero))
    (UniformListSemantics.Controls.assumptionHypotheses a [closedUniversal] 0)

theorem object_binder_outputs_differ :
    (.app (.var 0) zeroTerm : Tower.Tm 1) ≠ .app (.var 0) oneTerm := by decide

def closedPremise : Formula [] := .eq (.const Symbol.zero) (.const Symbol.zero)
def olderSource : HOL.ProofSyntax Symbol [closedPremise, closedPremise] closedPremise := .hyp 1
def olderHypotheses : Fin ([closedPremise] : List (Formula [])).length → Tower.Tm 1 := .var

theorem older_compiled :
    compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations olderSource (fun index : Fin 0 => rename wk (Fin.elim0 index))
        (Fin.cases (.var 0) (fun index => rename wk (olderHypotheses index))) =
      some (.var 1 : Tower.Tm 2) := rfl

theorem old_hypothesis_survives_proof_argument (a : ZFSet.{u}) :
    Denotes a (UniformListSemantics.Controls.assumptionState a [closedPremise])
      (.var 0) closedPremise := by
  let state := UniformListSemantics.Controls.assumptionState a [closedPremise]
  have argumentMeaning : Denotes a state FormationSensitiveHOLLeibnizDerived.reflTerm
      closedPremise :=
    UniformListSemantics.reflexivity a state
      (term := (.const Symbol.zero : HOL.Term Symbol [] count)) rfl rfl
  exact proof_binder_instantiation olderSource older_compiled state argumentMeaning
    (UniformListSemantics.Controls.assumptionHypotheses a [closedPremise])

/-- An equal proof proposition does not license replacing the retained
old-variable syntax by the newly supplied reflexivity term. -/
theorem old_result_not_new_argument :
    inst0 (FormationSensitiveHOLLeibnizDerived.reflTerm : Tower.Tm 1)
      (.var (1 : Fin 2)) ≠ FormationSensitiveHOLLeibnizDerived.reflTerm := by
  decide

theorem unsupported_source_stays_none :
    compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations (HOL.ProofSyntax.topI : HOL.ProofSyntax Symbol (Γ := []) [] .top)
        (n := 0) Fin.elim0 Fin.elim0 = none := rfl

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler.UniformListStateSubstitutionControls
