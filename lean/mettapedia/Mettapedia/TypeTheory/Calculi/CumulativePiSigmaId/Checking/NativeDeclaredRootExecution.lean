import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeRecursiveRootComputation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeBranchReturnExecution

/-!
# Checked certificate execution for every declared native root

The unchanged List/identity/relator package has five declared root forms.
Their selected raw code and an accepted source typing tree compute an accepted
result at the original displayed type. Branch-return cases use the existing
executor unchanged; recursive cases instantiate their recovered schemas.

This executes selected declared roots, not arbitrary contextual steps or a
normalization strategy. The raw source/target decoder remains the authority
for the selected computation's endpoints.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.DeclaredRootExecution

open Presentation NativeIndexedFamilies RecursiveRootComputation

def execute {n : Nat} (contextCode : ContextCode n) (displayed : Tower.Tm n)
    (code : Code n) (root : NativeRelatorRootConversionCode.Code n) :
    Option (PrincipalComputation.Result n) :=
  match root with
  | .indexed (.cons element motive nilCase consCase head tail) =>
      (listCons contextCode element motive nilCase consCase head tail displayed code).map
        fun output => ⟨.app (.app (.app consCase head) tail)
          (Intrinsic.eliminateApp element motive nilCase consCase tail), output, .root root⟩
  | .relCons source target relation motive nilCase consCase sourceHead targetHead
      sourceTail targetTail headEvidence tailEvidence =>
      (relCons contextCode source target relation motive nilCase consCase sourceHead targetHead
        sourceTail targetTail headEvidence tailEvidence displayed code).map
        fun output => ⟨.app (.app (.app (.app (.app (.app (.app consCase sourceHead) targetHead)
          sourceTail) targetTail) headEvidence) tailEvidence)
          (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase
            sourceTail targetTail tailEvidence), output, .root root⟩
  | _ => BranchReturnExecution.execute contextCode displayed code root

theorem execute_branch_unchanged {n : Nat} (contextCode : ContextCode n) (displayed : Tower.Tm n)
    (code : Code n) (root : NativeRelatorRootConversionCode.Code n)
    (branch : BranchReturnExecution.returnsBranch root = true) :
    execute contextCode displayed code root = BranchReturnExecution.execute contextCode displayed code root := by
  cases root with
  | indexed root => cases root <;> first | rfl | cases branch
  | relNil => rfl
  | relCons => cases branch

theorem execute_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {source target displayed : Tower.Tm n} {code : Code n}
    (root : NativeRelatorRootConversionCode.Code n)
    (decoded : NativeRelatorRootConversionCode.decode root = some (source, target))
    (accepted : check context source displayed contextCode code = true) :
    ∃ result, execute contextCode displayed code root = some result ∧
      result.term = target ∧ result.step = .root root ∧
      check context result.term displayed contextCode result.code = true := by
  cases root with
  | indexed root =>
      cases root with
      | nil element motive nilCase consCase =>
          exact BranchReturnExecution.execute_complete _ decoded accepted rfl
      | identity element point motive reflCase =>
          exact BranchReturnExecution.execute_complete _ decoded accepted rfl
      | cons element motive nilCase consCase head tail =>
          cases Option.some.inj decoded
          obtain ⟨output, computed, checked⟩ := listCons_checked accepted
          refine ⟨⟨_, output, _⟩, ?_, rfl, rfl, checked⟩
          simp only [execute, computed, Option.map_some]
  | relNil source target relation motive nilCase consCase =>
      exact BranchReturnExecution.execute_complete _ decoded accepted rfl
  | relCons source target relation motive nilCase consCase sourceHead targetHead
      sourceTail targetTail headEvidence tailEvidence =>
      cases Option.some.inj decoded
      obtain ⟨output, computed, checked⟩ := relCons_checked accepted
      refine ⟨⟨_, output, _⟩, ?_, rfl, rfl, checked⟩
      simp only [execute, computed, Option.map_some]

theorem execute_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {source target displayed : Tower.Tm n} {code : Code n}
    {root : NativeRelatorRootConversionCode.Code n} {result : PrincipalComputation.Result n}
    (decoded : NativeRelatorRootConversionCode.decode root = some (source, target))
    (accepted : check context source displayed contextCode code = true)
    (computed : execute contextCode displayed code root = some result) :
    result.term = target ∧ result.step = .root root ∧
      check context result.term displayed contextCode result.code = true ∧
      NativeRelatorConversionChecking.checkStep result.step source result.term = true := by
  obtain ⟨returned, equation, termEq, stepEq, checked⟩ := execute_complete root decoded accepted
  rw [computed] at equation
  cases Option.some.inj equation
  refine ⟨termEq, stepEq, checked, ?_⟩
  rw [stepEq, termEq]
  simp [NativeRelatorConversionChecking.checkStep, StructuralConversionCode.StepCode.check,
    StructuralConversionCode.StepCode.decode, decoded]

def checkedExecute {n : Nat} (context : Tower.Ctx n) (contextCode : ContextCode n)
    (subject displayed : Tower.Tm n) (code : Code n) (root : NativeRelatorRootConversionCode.Code n) :
    Option (PrincipalComputation.Result n) := do
  let (source, _) ← NativeRelatorRootConversionCode.decode root
  if source = subject ∧ check context subject displayed contextCode code = true then
    execute contextCode displayed code root
  else none

theorem checkedExecute_branch_unchanged {n : Nat} (context : Tower.Ctx n) (contextCode : ContextCode n)
    (subject displayed : Tower.Tm n) (code : Code n) (root : NativeRelatorRootConversionCode.Code n)
    (branch : BranchReturnExecution.returnsBranch root = true) :
    checkedExecute context contextCode subject displayed code root =
      BranchReturnExecution.checkedExecute context contextCode subject displayed code root := by
  simp only [checkedExecute, BranchReturnExecution.checkedExecute,
    execute_branch_unchanged contextCode displayed code root branch]

theorem checkedExecute_sound {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {subject displayed : Tower.Tm n} {code : Code n} {root : NativeRelatorRootConversionCode.Code n}
    {result : PrincipalComputation.Result n}
    (computed : checkedExecute context contextCode subject displayed code root = some result) :
    check context subject displayed contextCode code = true ∧ result.step = .root root ∧
      check context result.term displayed contextCode result.code = true ∧
      NativeRelatorConversionChecking.checkStep result.step subject result.term = true := by
  unfold checkedExecute at computed
  cases decoded : NativeRelatorRootConversionCode.decode root with
  | none => simp [decoded] at computed
  | some pair =>
      obtain ⟨source, target⟩ := pair
      simp only [decoded, bind, Option.bind] at computed
      split at computed
      · rename_i admitted
        obtain ⟨rfl, accepted⟩ := admitted
        exact ⟨accepted, (execute_checked decoded accepted computed).2⟩
      · contradiction

/-- Every admitted matching source executes; no root-specific success flag
or additional target-typing assumption remains. -/
theorem checkedExecute_domain {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {subject source target displayed : Tower.Tm n} {code : Code n}
    (root : NativeRelatorRootConversionCode.Code n)
    (decoded : NativeRelatorRootConversionCode.decode root = some (source, target)) :
    (checkedExecute context contextCode subject displayed code root).isSome =
      (decide (source = subject) && check context subject displayed contextCode code) := by
  simp only [checkedExecute, decoded, bind, Option.bind]
  split
  · rename_i admitted
    obtain ⟨rfl, accepted⟩ := admitted
    obtain ⟨result, computed, _⟩ := execute_complete root decoded accepted
    simp [computed, accepted]
  · rename_i rejected
    cases admission : decide (source = subject) && check context subject displayed contextCode code
    · rfl
    · have admitted : source = subject ∧ check context subject displayed contextCode code = true := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using admission
      exact (rejected admitted).elim

def resultReceipt {context : NativeCheckedSubstitution.Context}
    (source : NativeCheckedSubstitution.JudgmentReceipt context)
    (root : NativeRelatorRootConversionCode.Code context.arity)
    (result : PrincipalComputation.Result context.arity)
    (computed : checkedExecute context.raw context.code source.subject source.type source.code root = some result) :
    NativeCheckedSubstitution.JudgmentReceipt context :=
  ⟨result.term, source.type, result.code, (checkedExecute_sound computed).2.2.1⟩

theorem checkedExecute_observation {context : NativeCheckedSubstitution.Context}
    (source : NativeCheckedSubstitution.JudgmentReceipt context)
    (root : NativeRelatorRootConversionCode.Code context.arity)
    (result : PrincipalComputation.Result context.arity)
    (computed : checkedExecute context.raw context.code source.subject source.type source.code root = some result) :
    source.observe = (resultReceipt source root result computed).observe :=
  source.observe_eq_of_checkedStep (resultReceipt source root result computed) rfl
    result.step (checkedExecute_sound computed).2.2.2

theorem checkedExecute_root {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {subject displayed : Tower.Tm n} {code : Code n} {root : NativeRelatorRootConversionCode.Code n}
    {result : PrincipalComputation.Result n}
    (computed : checkedExecute context contextCode subject displayed code root = some result) :
    NativeRelatorRootConversionCode.decode root = some (subject, result.term) := by
  have checked := (checkedExecute_sound computed).2.2.2
  rw [(checkedExecute_sound computed).2.1] at checked
  change decide (NativeRelatorRootConversionCode.decode root = some (subject, result.term)) = true at checked
  exact of_decide_eq_true checked

theorem checkedExecute_reindex {context destination : NativeCheckedSubstitution.Context}
    (source : NativeCheckedSubstitution.JudgmentReceipt context)
    (morphism : NativeCheckedSubstitution.Hom destination context)
    (root : NativeRelatorRootConversionCode.Code context.arity)
    (result : PrincipalComputation.Result context.arity)
    (computed : checkedExecute context.raw context.code source.subject source.type source.code root = some result) :
    ∃ (output : PrincipalComputation.Result destination.arity)
      (outputComputed : checkedExecute destination.raw destination.code
        (source.reindex morphism).subject (source.reindex morphism).type (source.reindex morphism).code
        (NativeRelatorRootConversionCode.substitute morphism.substitution root) = some output),
      output.term = subst morphism.substitution result.term ∧
      output.step = .root (NativeRelatorRootConversionCode.substitute morphism.substitution root) ∧
      (resultReceipt (source.reindex morphism)
        (NativeRelatorRootConversionCode.substitute morphism.substitution root) output outputComputed).observe =
        ((resultReceipt source root result computed).reindex morphism).observe := by
  have decoded := checkedExecute_root computed
  have mappedDecoded : NativeRelatorRootConversionCode.decode
      (NativeRelatorRootConversionCode.substitute morphism.substitution root) =
      some ((source.reindex morphism).subject, subst morphism.substitution result.term) := by
    rw [NativeRelatorRootConversionCode.decode_substitute, decoded]
    rfl
  obtain ⟨output, executed, termEq, stepEq, _⟩ := execute_complete _ mappedDecoded
    (source.reindex morphism).accepted
  have outputComputed : checkedExecute destination.raw destination.code
      (source.reindex morphism).subject (source.reindex morphism).type (source.reindex morphism).code
      (NativeRelatorRootConversionCode.substitute morphism.substitution root) = some output := by
    simp only [checkedExecute, mappedDecoded, bind, Option.bind,
      (source.reindex morphism).accepted, and_self, ↓reduceIte, executed]
  refine ⟨output, outputComputed, termEq, stepEq, ?_⟩
  apply (NativeCheckedSubstitution.JudgmentReceipt.observe_eq_iff _ _).mpr
  change Conv IntrinsicRelator.rules.headEq (subst morphism.substitution source.type)
      (subst morphism.substitution source.type) IntrinsicRelator.rules.computation ∧
    Conv IntrinsicRelator.rules.headEq output.term (subst morphism.substitution result.term)
      IntrinsicRelator.rules.computation
  rw [termEq]
  exact ⟨.refl _, .refl _⟩

#print axioms execute_complete
#print axioms execute_branch_unchanged
#print axioms checkedExecute_branch_unchanged
#print axioms checkedExecute_sound
#print axioms checkedExecute_domain
#print axioms checkedExecute_observation
#print axioms checkedExecute_reindex

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.DeclaredRootExecution
