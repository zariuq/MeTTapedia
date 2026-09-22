import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeBranchReturnComputation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativePrincipalComputationReplay

/-!+# Checked execution of native branch-return roots

An actual selected native root and an accepted source typing certificate
compute a result certificate at the original displayed type. The selected
root remains in the directed-step receipt. Admission checks the decoded
source as well as its complete context and typing certificate.

The success domain is exactly the List-nil, identity-reflexivity and
relational List-nil roots. The two recursive cons roots require further
certificate construction; this module does not execute them.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.BranchReturnExecution

open Presentation NativeIndexedFamilies BranchReturnComputation

def returnsBranch {n : Nat} : NativeRelatorRootConversionCode.Code n → Bool
  | .indexed (.nil ..) | .indexed (.identity ..) | .relNil .. => true
  | .indexed (.cons ..) | .relCons .. => false

def execute {n : Nat} (contextCode : ContextCode n) (displayed : Tower.Tm n)
    (code : Code n) (root : NativeRelatorRootConversionCode.Code n) :
    Option (PrincipalComputation.Result n) :=
  match root with
  | .indexed (.nil element motive nilCase consCase) =>
      (listNil contextCode element motive nilCase consCase displayed code).map
        fun output => ⟨nilCase, output, .root root⟩
  | .indexed (.identity element point motive reflCase) =>
      (identity contextCode element point motive reflCase displayed code).map
        fun output => ⟨reflCase, output, .root root⟩
  | .relNil source target relation motive nilCase consCase =>
      (relNil contextCode source target relation motive nilCase consCase displayed code).map
        fun output => ⟨nilCase, output, .root root⟩
  | .indexed (.cons ..) | .relCons .. => none

theorem execute_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {source target displayed : Tower.Tm n} {code : Code n}
    (root : NativeRelatorRootConversionCode.Code n)
    (decoded : NativeRelatorRootConversionCode.decode root = some (source, target))
    (accepted : check context source displayed contextCode code = true)
    (supported : returnsBranch root = true) :
    ∃ result, execute contextCode displayed code root = some result ∧
      result.term = target ∧ result.step = .root root ∧
      check context result.term displayed contextCode result.code = true := by
  cases root with
  | indexed root =>
      cases root with
      | nil element motive nilCase consCase =>
          cases Option.some.inj decoded
          obtain ⟨output, computed, checked⟩ := listNil_checked accepted
          refine ⟨⟨_, output, _⟩, ?_, rfl, rfl, checked⟩
          simp only [execute, computed, Option.map_some]
      | identity element point motive reflCase =>
          cases Option.some.inj decoded
          obtain ⟨output, computed, checked⟩ := identity_checked accepted
          refine ⟨⟨_, output, _⟩, ?_, rfl, rfl, checked⟩
          simp only [execute, computed, Option.map_some]
      | cons => cases supported
  | relNil source target relation motive nilCase consCase =>
      cases Option.some.inj decoded
      obtain ⟨output, computed, checked⟩ := relNil_checked accepted
      refine ⟨⟨_, output, _⟩, ?_, rfl, rfl, checked⟩
      simp only [execute, computed, Option.map_some]
  | relCons => cases supported

theorem execute_requires_branch {n : Nat} {contextCode : ContextCode n}
    {displayed : Tower.Tm n} {code : Code n} {root : NativeRelatorRootConversionCode.Code n}
    {result : PrincipalComputation.Result n}
    (computed : execute contextCode displayed code root = some result) :
    returnsBranch root = true := by
  cases root with
  | indexed root => cases root <;> first | rfl | cases computed
  | relNil => rfl
  | relCons => cases computed

theorem execute_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {source target displayed : Tower.Tm n} {code : Code n}
    {root : NativeRelatorRootConversionCode.Code n} {result : PrincipalComputation.Result n}
    (decoded : NativeRelatorRootConversionCode.decode root = some (source, target))
    (accepted : check context source displayed contextCode code = true)
    (computed : execute contextCode displayed code root = some result) :
    result.term = target ∧ result.step = .root root ∧
      check context result.term displayed contextCode result.code = true ∧
      NativeRelatorConversionChecking.checkStep result.step source result.term = true := by
  obtain ⟨returned, equation, termEq, stepEq, checked⟩ :=
    execute_complete root decoded accepted (execute_requires_branch computed)
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

theorem checkedExecute_sound {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {subject displayed : Tower.Tm n} {code : Code n} {root : NativeRelatorRootConversionCode.Code n}
    {result : PrincipalComputation.Result n}
    (computed : checkedExecute context contextCode subject displayed code root = some result) :
    check context subject displayed contextCode code = true ∧
      result.step = .root root ∧
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

theorem checkedExecute_domain {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {subject source target displayed : Tower.Tm n} {code : Code n}
    (root : NativeRelatorRootConversionCode.Code n)
    (decoded : NativeRelatorRootConversionCode.decode root = some (source, target)) :
    (checkedExecute context contextCode subject displayed code root).isSome =
      (decide (source = subject) && check context subject displayed contextCode code && returnsBranch root) := by
  simp only [checkedExecute, decoded, bind, Option.bind]
  split
  · rename_i admitted
    obtain ⟨rfl, accepted⟩ := admitted
    simp only [decide_true, accepted, Bool.true_and]
    cases supported : returnsBranch root with
    | false =>
        cases computed : execute contextCode displayed code root with
        | none => rfl
        | some result =>
            have impossible := execute_requires_branch computed
            simp [supported] at impossible
    | true =>
        obtain ⟨result, computed, _⟩ := execute_complete root decoded accepted supported
        simp [computed]
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

theorem returnsBranch_substitute {n m : Nat} (sigma : Sub Tower.Head n m)
    (root : NativeRelatorRootConversionCode.Code n) :
    returnsBranch (NativeRelatorRootConversionCode.substitute sigma root) = returnsBranch root := by
  cases root with
  | indexed root => cases root <;> rfl
  | relNil => rfl
  | relCons => rfl

/-- Execution and checked substitution agree on the actual result term and
selected root, and hence on semantic observation. The computed typing trees
are not identified: argument alignment may change after substitution. -/
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
  have domain := congrArg Option.isSome computed
  rw [checkedExecute_domain root decoded] at domain
  have supported : returnsBranch root = true := by simpa [source.accepted] using domain
  have mappedDecoded :
      NativeRelatorRootConversionCode.decode
        (NativeRelatorRootConversionCode.substitute morphism.substitution root) =
        some ((source.reindex morphism).subject, subst morphism.substitution result.term) := by
    rw [NativeRelatorRootConversionCode.decode_substitute, decoded]
    rfl
  obtain ⟨output, executed, termEq, stepEq, _⟩ := execute_complete _ mappedDecoded
    (source.reindex morphism).accepted (by rw [returnsBranch_substitute]; exact supported)
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
#print axioms execute_checked
#print axioms checkedExecute_sound
#print axioms checkedExecute_domain
#print axioms checkedExecute_observation
#print axioms checkedExecute_root
#print axioms checkedExecute_reindex

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.BranchReturnExecution
