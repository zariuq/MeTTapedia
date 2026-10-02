import Mettapedia.Languages.VibeITP.Presentation.SignatureExtensionDerivation

/-!
# Signature-extension boundary controls

These are kernel-checked logical controls.  Execution observations are
explicit inputs to derivability; no control claims to execute machine code.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.SignatureExtensionControls

open Mettapedia.Languages.VibeITP.Spec

def before : Sig :=
  sigOf fun index => if index = 0 then some ⟨.constant, [1, 0]⟩ else none

def after : Sig :=
  sigOf fun index =>
    if index = 0 then some ⟨.constant, [1, 0]⟩
    else if index = 1 then some (SymInfo.fvarOf 1) else none

def later : Sig :=
  sigOf fun index =>
    if index = 0 then some ⟨.constant, [1, 0]⟩
    else if index = 1 then some (SymInfo.fvarOf 1)
    else if index = 2 then some ⟨.constant, []⟩ else none

theorem before_after : SigExt before after := by
  intro symbol info allocated
  cases symbol with
  | builtin builtin => simpa only [before, after, sigOf] using allocated
  | fresh index =>
      by_cases zero : index = 0
      · simpa only [before, after, sigOf, zero, if_true] using allocated
      · simp [before, sigOf, zero] at allocated

theorem after_later : SigExt after later := by
  intro symbol info allocated
  cases symbol with
  | builtin builtin => simpa only [after, later, sigOf] using allocated
  | fresh index =>
      by_cases zero : index = 0
      · simpa only [after, later, sigOf, zero, if_true] using allocated
      · by_cases one : index = 1
        · simpa only [after, later, sigOf, zero, one, if_false, if_true] using allocated
        · simp [after, sigOf, zero, one] at allocated

def traversalTerm : Term := .app (.fresh 0) [.bvar 2, .bvar 0]

theorem traversal_shape : TermShape before traversalTerm :=
  .app rfl rfl (.cons (.bvar 2) (.cons (.bvar 0) .nil))

theorem old_head_and_binders_preserved :
    after (.fresh 0) = some ⟨.constant, [1, 0]⟩ := rfl

theorem shift_under_binder :
    shift before 1 0 traversalTerm = some (.app (.fresh 0) [.bvar 3, .bvar 1]) := by decide

theorem shift_under_binder_preserved :
    shift after 1 0 traversalTerm = shift before 1 0 traversalTerm :=
  shift_sigExt before_after 1 0 traversalTerm traversal_shape

theorem reverse_substitution :
    substBVars before 2 [.lit [7], .lit [9]] traversalTerm 0 =
      some (.app (.fresh 0) [.lit [7], .lit [9]]) := by decide

theorem reverse_substitution_preserved :
    substBVars after 2 [.lit [7], .lit [9]] traversalTerm 0 =
      substBVars before 2 [.lit [7], .lit [9]] traversalTerm 0 :=
  substBVars_sigExt before_after 2 _ (.cons (.lit _) (.cons (.lit _) .nil))
    traversalTerm traversal_shape 0

theorem zero_argument_pruning :
    substBVars before 0 [] (.bvar wordBound) wordBound = some (.bvar wordBound) := rfl

theorem unknown_parameter_refused :
    instantiateStatement before (.fresh 1) (.lit []) (.lit []) = none := by decide

theorem newly_allocated_parameter_accepted :
    instantiateStatement after (.fresh 1) (.lit []) (.lit []) = some (.lit []) := by decide

theorem allocation_changes_prior_refusal :
    instantiateStatement before (.fresh 1) (.lit []) (.lit []) ≠
      instantiateStatement after (.fresh 1) (.lit []) (.lit []) := by decide

theorem unknown_parameter_not_known : ¬KnownSymbol before (.fresh 1) := by
  rintro ⟨info, allocated⟩
  simp [before, sigOf] at allocated

def instantiationStatement : Term := .eq (.app (.fresh 1) [.lit [7]]) (.lit [7])

theorem instantiation_statement_shape : TermShape after instantiationStatement :=
  .app rfl rfl (.cons (.app rfl rfl (.cons (.lit _) .nil)) (.cons (.lit _) .nil))

theorem known_parameter_instantiation :
    instantiateStatement after (.fresh 1) (.bvar 0) instantiationStatement =
      some (.eq (.lit [7]) (.lit [7])) := by decide

theorem known_parameter_success_preserved :
    instantiateStatement later (.fresh 1) (.bvar 0) instantiationStatement =
      some (.eq (.lit [7]) (.lit [7])) :=
  instantiateStatement_success_sigExt after_later (.fresh 1) (.bvar 0)
    instantiationStatement _ (.bvar 0) instantiation_statement_shape known_parameter_instantiation

theorem known_parameter_depth_refusal :
    instantiateStatement after (.fresh 1) (.bvar 1) instantiationStatement = none := by decide

theorem known_parameter_refusal_preserved :
    instantiateStatement later (.fresh 1) (.bvar 1) instantiationStatement = none := by
  rw [instantiateStatement_sigExt after_later (.fresh 1) ⟨SymInfo.fvarOf 1, rfl⟩
    (.bvar 1) instantiationStatement (.bvar 1) instantiation_statement_shape]
  exact known_parameter_depth_refusal

theorem constant_parameter_refused :
    instantiateStatement before (.fresh 0) (.lit []) (.lit []) = none := by decide

theorem constant_parameter_refusal_preserved :
    instantiateStatement after (.fresh 0) (.lit []) (.lit []) = none := by
  rw [instantiateStatement_sigExt before_after (.fresh 0) ⟨⟨.constant, [1, 0]⟩, rfl⟩
    (.lit []) (.lit []) (.lit []) (.lit [])]
  exact constant_parameter_refused

theorem unknown_application_formation_refused :
    WellFormed before (.app (.fresh 1) [.lit []]) = false := by decide

theorem newly_allocated_application_formation_accepted :
    WellFormed after (.app (.fresh 1) [.lit []]) = true := by decide

theorem unknown_application_has_no_profile :
    ¬TermShape before (.app (.fresh 1) [.lit []]) := by
  intro shape
  obtain ⟨info, allocated, _, _⟩ := TermShape.app_iff.mp shape
  simp [before, sigOf] at allocated

theorem unbounded_index_profile : TermShape before (.bvar wordBound) := .bvar _

theorem unbounded_index_formation_refused : WellFormed before (.bvar wordBound) = false := by decide

theorem zero_shift_prunes_unbounded_index :
    shift before 0 0 (.bvar wordBound) = some (.bvar wordBound) := rfl

theorem overflowing_shift_refused : shift before 1 0 (.bvar (wordBound - 1)) = none := by decide

theorem overflowing_shift_refusal_preserved :
    shift after 1 0 (.bvar (wordBound - 1)) = none := by
  rw [shift_sigExt before_after 1 0 (.bvar (wordBound - 1)) (.bvar _)]
  exact overflowing_shift_refused

theorem arbitrary_arity_eta_profile (arity : Nat) :
    TermShape (sigOf fun index => if index = 0 then some (SymInfo.fvarOf arity) else none)
      (etaFvar (.fresh 0) arity) := by
  let sig : Sig := sigOf fun index => if index = 0 then some (SymInfo.fvarOf arity) else none
  have allocated : (sig (.fresh 0)).isSome = true := rfl
  have declared : symArity sig (.fresh 0) = arity := by
    simp [sig, sigOf, symArity, SymInfo.fvarOf, SymInfo.arity]
  simpa only [declared] using etaFvar_termShape sig (.fresh 0) allocated

def overflowBinders : Sig :=
  sigOf fun index => if index = 0 then some ⟨.constant, [wordBound]⟩ else none

theorem overflowing_binder_offset_refused :
    shift overflowBinders 1 0 (.app (.fresh 0) [.bvar wordBound]) = none := by decide

theorem closed_pruning_avoids_binder_overflow :
    shift overflowBinders 1 0 (.app (.fresh 0) [.bvar 0]) =
      some (.app (.fresh 0) [.bvar 0]) := by decide

theorem definition_admission_preserved :
    definitionAdmissible later [.fresh 1] [0] (.app (.fresh 1) [.lit [7]]) =
      definitionAdmissible after [.fresh 1] [0] (.app (.fresh 1) [.lit [7]]) :=
  definitionAdmissible_sigExt after_later _ _ _
    (by intro parameter member; simp at member; subst parameter; exact ⟨_, rfl⟩)
    (.app rfl rfl (.cons (.lit _) .nil))

theorem definition_admission_accepted :
    definitionAdmissible after [.fresh 1] [0] (.app (.fresh 1) [.lit [7]]) = true := by decide

theorem missing_definition_hint_refused :
    definitionAdmissible after [.fresh 1] [] (.app (.fresh 1) [.lit [7]]) = false := by decide

theorem surplus_definition_hint_accepted :
    definitionAdmissible after [.fresh 1] [0, 0] (.app (.fresh 1) [.lit [7]]) = true := by decide

theorem definition_parameter_arity_preserved :
    definitionInfo later [.fresh 1] = ⟨.constant, [1]⟩ := rfl

theorem definition_statement_preserved :
    definitionStatement later (.fresh 2) [.fresh 1] (.app (.fresh 1) [.lit [7]]) =
      definitionStatement after (.fresh 2) [.fresh 1] (.app (.fresh 1) [.lit [7]]) :=
  definitionStatement_sigExt after_later _ _ _
    (by intro parameter member; simp at member; subst parameter; exact ⟨_, rfl⟩)

def changedBinders : Sig :=
  sigOf fun index => if index = 0 then some ⟨.constant, [0, 0]⟩ else none

theorem changing_binders_is_not_extension : ¬SigExt before changedBinders := by
  intro extension
  have changed := extension (.fresh 0) ⟨.constant, [1, 0]⟩ rfl
  simp [changedBinders, sigOf] at changed

theorem changing_binders_changes_pruning :
    shift before 1 0 (.app (.fresh 0) [.bvar 0, .lit []]) ≠
      shift changedBinders 1 0 (.app (.fresh 0) [.bvar 0, .lit []]) := by decide

def safeStatement : Term :=
  .app (.builtin .isSafeCode) [.lit [195], .lit [], .lit [], .lit [1]]

def observation : ExecutionObservation :=
  ⟨⟨[195], [], [], 1⟩, [7]⟩

def sourceTheory : Theory := ⟨before, [safeStatement], []⟩
def targetTheory : Theory := ⟨after, [litIsNatStatement 1, safeStatement], []⟩

theorem source_hosted : Hosted sourceTheory 1 := by
  constructor
  · intro builtin
    rfl
  · intro index
    by_cases zero : index = 0
    · simp [sourceTheory, before, sigOf, zero]
    · simp only [sourceTheory, before, sigOf, zero, if_false, Option.isSome_none, Bool.false_eq_true,
        false_iff]
      intro smaller
      exact zero (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ smaller))
  · intro symbol info allocated kind
    cases symbol with
    | builtin builtin =>
        simp only [sourceTheory, before, sigOf, Option.some.injEq] at allocated
        subst info
        simp [Builtin.info] at kind
    | fresh index =>
        by_cases zero : index = 0
        · simp only [sourceTheory, before, sigOf, zero, if_true, Option.some.injEq] at allocated
          subst info
          contradiction
        · simp [sourceTheory, before, sigOf, zero] at allocated
  · intro statement member
    have statement_eq : statement = safeStatement := by simpa [sourceTheory] using member
    subst statement
    exact ⟨by decide, by decide⟩
  · intro definition member
    simp [sourceTheory] at member

theorem theory_extension : TheoryExt sourceTheory targetTheory := by
  refine ⟨before_after, ?_, ?_⟩
  · intro statement member
    simpa [sourceTheory, targetTheory] using Or.inr member
  · intro definition member
    simp [sourceTheory] at member

theorem static_axiom_preserved : Spec.Derives targetTheory safeStatement :=
  derives_theory_extension source_hosted theory_extension (.axiom (by simp [sourceTheory]))

theorem observation_guard_accepted : GuardedExecution safeStatement observation := by
  unfold GuardedExecution
  decide

theorem observation_wrong_output_length_refused :
    ¬GuardedExecution safeStatement ⟨observation.request, []⟩ := by
  unfold GuardedExecution
  decide

theorem observation_absent_from_empty_run : observation ∉ ([] : List ExecutionObservation) := by decide

theorem guarded_execution_source :
    DerivesWithExecution sourceTheory [observation] observation.statement :=
  .jit (.axiom (by simp [sourceTheory])) (by simp) observation_guard_accepted

theorem guarded_execution_preserved :
    DerivesWithExecution targetTheory [observation, ⟨observation.request, []⟩] observation.statement :=
  derives_with_execution_theory_extension source_hosted theory_extension
    (by intro event member; simp at member; subst event; simp) guarded_execution_source

theorem guarded_execution_statement_profile : TermShape before observation.statement :=
  derivesWithExecution_termShape source_hosted guarded_execution_source

end Mettapedia.Languages.VibeITP.Presentation.SignatureExtensionControls
