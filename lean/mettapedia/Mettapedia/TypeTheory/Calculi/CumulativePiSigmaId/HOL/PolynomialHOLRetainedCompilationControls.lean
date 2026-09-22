import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.PolynomialHOLRetainedCompilation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeUniformListStateSubstitutionControls

/-!
# Retained branching compilation with different hypothesis occurrences

An implication method consumes two universal-elimination children. Its leaves
are already compiled hypothesis occurrences. Expanding the composite method
assembles exactly the retained child terms, without recursively compiling them.
Equal child propositions do not identify distinct proof occurrences.
-/

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PolynomialHOLRetainedCompilationControls

open Mettapedia.Logic Presentation FormationSensitiveHOLInterface
open HOLNativeGenericProofCompiler ProofSearch ProofObligations
open PolynomialHOLRetainedCompilation
open Mettapedia.TypeTheory.IndexedPolynomial
open HOL.UniformListInduction Mettapedia.Logic.HOL.Embedding
open UniformListSemantics

abbrev Goal := HOLAdapter.Goal BaseSort Symbol
abbrev Solution := @HOLAdapter.Solution BaseSort Symbol
abbrev signature := FormationSensitiveHOLLeibnizInterface.signature
abbrev operations := UniformList.operations
abbrev proofName := UniformList.proofName

inductive Method : Goal → Type
  | implication {gamma : SourceContext} {delta : List (Formula gamma)}
      (antecedent conclusion : Formula gamma) : Method ⟨gamma, delta, conclusion⟩
  | universal {gamma : SourceContext} {delta : List (Formula gamma)}
      {type : HOL.Ty BaseSort} (body : Formula (type :: gamma))
      (argument : HOL.Term Symbol gamma type) (code : Tower.Tm gamma.length)
      (represented : represent signature argument = some code) :
      Method ⟨gamma, delta, HOL.instantiate argument body⟩

def methods : ∀ goal, Method goal → Refinement Solution goal
  | _, .implication antecedent conclusion => ProofObligations.HOL.impE antecedent conclusion
  | _, .universal body argument _ _ => ProofObligations.HOL.allE body argument

def objectInputs (goal : Goal) : Sub Tower.Head goal.context.length 4 := fun _ => .var 3
def hypothesisInputs (goal : Goal) : Fin goal.hypotheses.length → Tower.Tm 4 :=
  fun index => if index.val = 0 then .var 0 else if index.val = 1 then .var 1 else .var 2

def assembly : LocalAssembly signature proofName operations methods objectInputs hypothesisInputs := by
  intro goal method children
  cases method with
  | implication antecedent conclusion =>
      exact (implicationApplication signature proofName operations
        (children ⟨0⟩) (children ⟨1⟩)).2
  | universal body argument code represented =>
      exact (universalApplication signature proofName operations argument represented
        (children ⟨0⟩)).2

/-- The same two constructor assemblies at transported inputs. Their child
contexts agree definitionally; no whole-plan transport law is assumed. -/
def transportedAssembly {scope : Nat} (sigma : Sub Tower.Head 4 scope) :
    LocalAssembly signature proofName operations methods
      (fun goal index => subst sigma (objectInputs goal index))
      (fun goal index => subst sigma (hypothesisInputs goal index)) := by
  intro goal method children
  cases method with
  | implication antecedent conclusion =>
      exact (implicationApplication signature proofName operations
        (children ⟨0⟩) (children ⟨1⟩)).2
  | universal body argument code represented =>
      exact (universalApplication signature proofName operations argument represented
        (children ⟨0⟩)).2

abbrev gamma : SourceContext := [count]
def argument : HOL.Term Symbol gamma count := .var .vz
def body : Formula (count :: gamma) := .eq (.var .vz) (.var .vz)
def minorFormula : Formula gamma := .all body
def majorFormula : Formula gamma := .all (.imp body body)
def conclusion : Formula gamma := HOL.instantiate argument body
def delta : List (Formula gamma) := [majorFormula, minorFormula, minorFormula]
def root : Goal := ⟨gamma, delta, conclusion⟩
def outer : Method root := .implication conclusion conclusion

def composite : PolynomialPlans.CompositeRoutes methods root := by
  refine ⟨outer, ?_⟩
  intro occurrence
  rcases occurrence with ⟨occurrence⟩
  refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index)
    occurrence
  · exact .universal (.imp body body) argument (.var 0) rfl
  · exact .universal body argument (.var 0) rfl

abbrev route := PolynomialPlans.compositeMethods methods root composite

def major : Retained signature proofName operations
    (goal := ⟨gamma, delta, majorFormula⟩)
    (objectInputs ⟨gamma, delta, majorFormula⟩) (hypothesisInputs ⟨gamma, delta, majorFormula⟩) :=
  ⟨HOL.ProofSyntax.hyp (Const := Symbol) (Δ := delta) ⟨0, by decide⟩, .var 0, rfl⟩

def minor (older : Bool) : Retained signature proofName operations
    (goal := ⟨gamma, delta, minorFormula⟩)
    (objectInputs ⟨gamma, delta, minorFormula⟩) (hypothesisInputs ⟨gamma, delta, minorFormula⟩) :=
  if older then ⟨HOL.ProofSyntax.hyp (Const := Symbol) (Δ := delta) ⟨2, by decide⟩, .var 2, rfl⟩
  else ⟨HOL.ProofSyntax.hyp (Const := Symbol) (Δ := delta) ⟨1, by decide⟩, .var 1, rfl⟩

def receipts (older : Bool) : ∀ occurrence, Retained signature proofName operations
    (objectInputs (route.query occurrence)) (hypothesisInputs (route.query occurrence)) := by
  intro occurrence
  rcases occurrence with ⟨⟨outerIndex⟩, innerIndex⟩
  revert innerIndex
  refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index)
    outerIndex
  · intro _; exact major
  · intro _; exact minor older

abbrev Holes (_ : Unit) (goal : Goal) :=
  Retained signature proofName operations (objectInputs goal) (hypothesisInputs goal)

def macroPlan (older : Bool) :
    (PolynomialPlans.polynomial (PolynomialPlans.compositeMethods methods)).Free Holes () root :=
  Free.node _ composite (fun occurrence => Free.pure _ (receipts older occurrence))

noncomputable def expandedPlan (older : Bool) :=
  (PolynomialPlans.expansion methods).run () root (macroPlan older)

noncomputable def retained (older : Bool) :=
  assemblePlan signature proofName operations methods objectInputs hypothesisInputs assembly
    (fun _ _ receipt => receipt) () root (expandedPlan older)

def expected (older : Bool) : Tower.Tm 4 :=
  .app (.app (.var 0) (.var 3)) (.app (if older then .var 2 else .var 1) (.var 3))

def expectedProof (older : Bool) : Solution root :=
  .impE (.allE argument major.1) (.allE argument (minor older).1)

theorem actual_output (older : Bool) : (retained older).2.1 = expected older := by
  cases older <;> rfl

theorem actual_source (older : Bool) : (retained older).1 = expectedProof older := by
  cases older <;> rfl

theorem actual_compiler_receipt (older : Bool) :
    compile signature proofName operations (expectedProof older)
      (objectInputs root) (hypothesisInputs root) = some (expected older) := by
  have actual := (retained older).2.2
  simpa only [actual_source, actual_output] using actual

/-- Exchanging major and minor is not licensed by having two child terms. -/
theorem wrong_child_order_rejected :
    compile signature proofName operations (expectedProof false)
      (objectInputs root) (hypothesisInputs root) ≠
      some (.app (.app (.var 1) (.var 3)) (.app (.var 0) (.var 3))) := by
  rw [actual_compiler_receipt]
  decide

/-- A syntactically valid source constructor still needs compiler support.
The retained-artifact carrier cannot manufacture a receipt for this case. -/
theorem unsupported_constructor_has_no_receipt :
    ¬ ∃ native, compile signature proofName operations
      (HOL.ProofSyntax.topI : HOL.ProofSyntax Symbol delta .top)
      (objectInputs root) (hypothesisInputs root) = some native := by
  rintro ⟨native, impossible⟩
  cases impossible

theorem expanded_native_is_macro_native (older : Bool) :
    (retained older).2.1 =
    (assemblePlan signature proofName operations (PolynomialPlans.compositeMethods methods)
      objectInputs hypothesisInputs
      (compositeAssembly signature proofName operations methods objectInputs hypothesisInputs assembly)
      (fun _ _ receipt => receipt) () root (macroPlan older)).2.1 :=
  assembled_expansion signature proofName operations methods objectInputs hypothesisInputs assembly
    (fun _ _ receipt => receipt) (macroPlan older)

theorem old_occurrences_not_identified : (retained false).2.1 ≠ (retained true).2.1 := by
  rw [actual_output, actual_output]
  decide

theorem proof_occurrences_not_identified : (retained false).1 ≠ (retained true).1 := by
  intro same
  exact old_occurrences_not_identified
    (same_source_same_native signature proofName operations objectInputs hypothesisInputs
      (retained false) (retained true) same)

theorem two_retained_children : Fintype.card route.Premise = 2 := by decide

def missing : ∀ occurrence, Option (Holes () (route.query occurrence)) :=
  fun occurrence => if occurrence.1.down.val = 0 then some (receipts false occurrence) else none

theorem missing_occurrence_no_output :
    (partialAlgebra signature proofName operations (PolynomialPlans.compositeMethods methods)
      objectInputs hypothesisInputs
      (compositeAssembly signature proofName operations methods objectInputs hypothesisInputs assembly)).act
      () root ⟨composite, missing⟩ = none := by
  apply missing_child_no_assembly
  exact ⟨⟨⟨1⟩, ⟨0⟩⟩, rfl⟩

def majorNative : Tower.Tm 0 := .lam (.lam (.var 0))

def substitution (objectTerm : Tower.Tm 0) : Sub Tower.Head 4 0 :=
  fun index => Fin.cases majorNative
    (fun rest => Fin.cases UniformListStateSubstitutionControls.universalProof
      (fun last => Fin.cases UniformListStateSubstitutionControls.universalProof
        (fun _ => objectTerm) last) rest) index

noncomputable def reassembled (older : Bool) (objectTerm : Tower.Tm 0) :=
  assemblePlan signature proofName operations methods
    (fun goal index => subst (substitution objectTerm) (objectInputs goal index))
    (fun goal index => subst (substitution objectTerm) (hypothesisInputs goal index))
    (transportedAssembly (substitution objectTerm))
    (fun _ _ receipt => transportRetained signature proofName operations
      UniformList.rawOperations_natural (substitution objectTerm) receipt)
    () root (expandedPlan older)

theorem assemble_after_transport (older : Bool) (objectTerm : Tower.Tm 0) :
    (reassembled older objectTerm).2.1 = subst (substitution objectTerm) (retained older).2.1 :=
  assembly_naturality signature proofName operations methods objectInputs hypothesisInputs
    UniformList.rawOperations_natural assembly (substitution objectTerm)
    (transportedAssembly (substitution objectTerm)) (fun _ _ receipt => receipt) (expandedPlan older)

theorem transported_major_keeps_source (objectTerm : Tower.Tm 0) :
    (transportRetained signature proofName operations UniformList.rawOperations_natural
      (substitution objectTerm) major).1 = major.1 := rfl

universe u

def finalState (a : ZFSet.{u}) (objectTerm : Tower.Tm 0)
    (value : ZFSetUniformListTraceTypeInterpretation.Value a count)
    (meaning : NativeHOLTraceDisplayedTerms.Denotes a NativeTraceLambdaSemantics.Context.nil
      objectTerm (fun _ => value)) :
    State a (fun index => subst (substitution objectTerm) (objectInputs root index)) :=
  UniformListStateSubstitutionControls.targetState a objectTerm value meaning

theorem major_meaning (a : ZFSet.{u}) (objectTerm : Tower.Tm 0)
    (value : ZFSetUniformListTraceTypeInterpretation.Value a count)
    (meaning : NativeHOLTraceDisplayedTerms.Denotes a NativeTraceLambdaSemantics.Context.nil
      objectTerm (fun _ => value)) :
    Denotes a (finalState a objectTerm value meaning) majorNative majorFormula := by
  apply UniformListSemantics.compile_denotes a
    (HOL.ProofSyntax.allI (HOL.ProofSyntax.impI (HOL.ProofSyntax.hyp 0)) :
      HOL.ProofSyntax Symbol ([] : List (Formula gamma)) majorFormula)
    (hypotheses := Fin.elim0) (native := majorNative)
  · rfl
  · intro index; exact Fin.elim0 index

theorem final_meaning (older : Bool) (a : ZFSet.{u}) (objectTerm : Tower.Tm 0)
    (value : ZFSetUniformListTraceTypeInterpretation.Value a count)
    (meaning : NativeHOLTraceDisplayedTerms.Denotes a NativeTraceLambdaSemantics.Context.nil
      objectTerm (fun _ => value)) :
    Denotes a (finalState a objectTerm value meaning)
      (subst (substitution objectTerm) (retained older).2.1) conclusion := by
  apply assembled_substitution methods objectInputs hypothesisInputs assembly
    (fun _ _ receipt => receipt) (expandedPlan older) (substitution objectTerm)
  intro index
  refine Fin.cases ?_ (fun rest => Fin.cases ?_
    (fun last => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) last) rest) index
  · exact major_meaning a objectTerm value meaning
  · exact UniformListStateSubstitutionControls.universal_denotes a objectTerm value meaning
  · exact UniformListStateSubstitutionControls.universal_denotes a objectTerm value meaning

theorem zero_result_denotes (a : ZFSet.{u}) :
    Denotes a (finalState a UniformListStateSubstitutionControls.zeroTerm _
      (UniformListStateSubstitutionControls.zero_object_denotes a))
      (subst (substitution UniformListStateSubstitutionControls.zeroTerm) (retained false).2.1)
      conclusion := final_meaning false a _ _
        (UniformListStateSubstitutionControls.zero_object_denotes a)

theorem one_result_denotes (a : ZFSet.{u}) :
    Denotes a (finalState a UniformListStateSubstitutionControls.oneTerm _
      (UniformListStateSubstitutionControls.one_object_denotes a))
      (subst (substitution UniformListStateSubstitutionControls.oneTerm) (retained false).2.1)
      conclusion := final_meaning false a _ _
        (UniformListStateSubstitutionControls.one_object_denotes a)

theorem instantiated_outputs_differ :
    subst (substitution UniformListStateSubstitutionControls.zeroTerm) (retained false).2.1 ≠
      subst (substitution UniformListStateSubstitutionControls.oneTerm) (retained false).2.1 := by
  rw [actual_output]
  decide

theorem target_assembly_outputs_differ :
    (reassembled false UniformListStateSubstitutionControls.zeroTerm).2.1 ≠
      (reassembled false UniformListStateSubstitutionControls.oneTerm).2.1 := by
  rw [assemble_after_transport, assemble_after_transport]
  exact instantiated_outputs_differ

theorem target_zero_assembly_denotes (a : ZFSet.{u}) :
    Denotes a (finalState a UniformListStateSubstitutionControls.zeroTerm _
      (UniformListStateSubstitutionControls.zero_object_denotes a))
      (reassembled false UniformListStateSubstitutionControls.zeroTerm).2.1 conclusion := by
  rw [assemble_after_transport]
  exact zero_result_denotes a

theorem target_one_assembly_denotes (a : ZFSet.{u}) :
    Denotes a (finalState a UniformListStateSubstitutionControls.oneTerm _
      (UniformListStateSubstitutionControls.one_object_denotes a))
      (reassembled false UniformListStateSubstitutionControls.oneTerm).2.1 conclusion := by
  rw [assemble_after_transport]
  exact one_result_denotes a

namespace BinderControls

def predicate : Formula [] := .all (.eq (.var .vz) (.var .vz) : Formula [count])

def noObjects : Sub Tower.Head 0 0 := Fin.elim0
def noHypotheses : Fin 0 → Tower.Tm 0 := Fin.elim0
def proofObjects : Sub Tower.Head 0 1 := fun index => rename wk (noObjects index)
def proofHypotheses : Fin 1 → Tower.Tm 1 :=
  Fin.cases (.var 0) (fun index => rename wk (noHypotheses index))
def boundObjects : Sub Tower.Head 1 2 := liftSub proofObjects
def boundHypotheses : Fin (HOL.weakenHyps (σ := count) [predicate]).length → Tower.Tm 2 :=
  fun index => rename wk (proofHypotheses (index.cast (by simp [HOL.weakenHyps])))

/-- Under a new object binder, the older proof remains native variable one. -/
def olderUniversal : Retained signature proofName operations
    (goal := ⟨[count], HOL.weakenHyps [predicate], HOL.weaken (σ := count) predicate⟩)
    boundObjects boundHypotheses :=
  ⟨HOL.ProofSyntax.hyp (Const := Symbol) (Δ := HOL.weakenHyps (σ := count) [predicate])
      ⟨0, by simp [HOL.weakenHyps]⟩,
    .var 1, rfl⟩

def appliedOlderUniversal := universalApplication signature proofName operations
  (.var .vz : HOL.Term Symbol [count] count) (by rfl) olderUniversal

def introducedObject : Retained signature proofName operations
    (goal := ⟨[], [predicate], predicate⟩)
    proofObjects proofHypotheses :=
  universalAbstraction signature proofName operations appliedOlderUniversal

/-- Both native abstractions are assembled from the retained leaf, not chosen
by recursively compiling the reconstructed parent. -/
def introducedProof : Retained signature proofName operations
    (goal := ⟨[], [], .imp predicate predicate⟩)
    noObjects noHypotheses :=
  implicationAbstraction signature proofName operations (by rfl) introducedObject

def expectedSource : HOL.ProofSyntax Symbol [] (.imp predicate predicate) :=
  .impI (.allI (.allE (.var .vz)
    (HOL.ProofSyntax.hyp (Const := Symbol) (Δ := HOL.weakenHyps (σ := count) [predicate])
      ⟨0, by simp [HOL.weakenHyps]⟩)))

theorem mixed_binders_retain_source : introducedProof.1 = expectedSource := rfl

theorem mixed_binders_actual_compiler_receipt :
    compile signature proofName operations expectedSource
      (Fin.elim0 : Sub Tower.Head 0 0) (Fin.elim0 : Fin 0 → Tower.Tm 0) =
      some (.lam (.lam (.app (.var 1) (.var 0)))) := introducedProof.2.2

theorem mixed_binders_preserve_distinct_roles :
    introducedProof.2.1 = (.lam (.lam (.app (.var 1) (.var 0))) : Tower.Tm 0) := rfl

/-- A new object binder does not turn the older proof into the new variable. -/
theorem wrong_mixed_binder_order_rejected :
    compile signature proofName operations expectedSource
      (Fin.elim0 : Sub Tower.Head 0 0) (Fin.elim0 : Fin 0 → Tower.Tm 0) ≠
      some (.lam (.lam (.app (.var 0) (.var 1)))) := by
  rw [mixed_binders_actual_compiler_receipt]
  decide

end BinderControls

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PolynomialHOLRetainedCompilationControls
