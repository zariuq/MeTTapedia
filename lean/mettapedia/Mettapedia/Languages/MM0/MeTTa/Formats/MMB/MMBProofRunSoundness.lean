import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MMBDefinitionUnificationSoundness

/-!
# Ordered evidence through actual binary proof runs

All command cases use the retained machine and the existing kernel evidence.
Recorded hypotheses are authorized by the final source statement match;
available declarations and definition bodies remain independently supplied.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.MMBProofRunSoundness

open Formats.MMB Kernel
open MMBMachineSoundness MMBDependencySoundness MMBStateScopeSoundness

theorem step_conversion_keeps_store_heap (tables : Tables) (mode : Mode)
    (before after : Formats.MMB.State) (command : ProofCmd)
    (selected : command = .conv ∨ command = .refl ∨ command = .symm ∨ command = .cong ∨
      command = .unfold ∨ command = .convCut)
    (executed : step tables mode before command = some after) :
    after.store = before.store ∧ after.heap = before.heap := by
  have keeps := step_nonallocating_keeps_store tables mode before after command
    (by intro term same; subst same; simp at selected)
    (by intro term same; subst same; simp at selected)
    (by intro sort same; subst same; simp at selected) executed
  refine ⟨keeps, ?_⟩
  cases command with
  | term _ | termSave _ | ref _ | dummy _ | thm _ | thmSave _ | hyp | convSave | save => simp at selected
  | conv | refl | symm | convCut =>
      simp only [step] at executed
      repeat' split at executed
      all_goals try cases executed
      all_goals rfl
  | cong =>
      simp only [step] at executed
      split at executed
      · obtain ⟨left, _, checked⟩ := Option.bind_eq_some_iff.mp executed
        obtain ⟨right, _, checked⟩ := Option.bind_eq_some_iff.mp checked
        rcases left with ⟨leftNode, leftType⟩
        rcases right with ⟨rightNode, rightType⟩
        cases leftNode <;> cases rightNode <;> simp at checked
        obtain ⟨_, rfl⟩ := checked
        rfl
      · cases executed
  | unfold =>
      simp only [step] at executed
      split at executed
      · obtain ⟨allocation, _, checked⟩ := Option.bind_eq_some_iff.mp executed
        rcases allocation with ⟨node, type⟩
        cases node with
        | var _ => cases checked
        | app _ _ =>
            obtain ⟨entry, _, checked⟩ := Option.bind_eq_some_iff.mp checked
            obtain ⟨value, _, checked⟩ := Option.bind_eq_some_iff.mp checked
            obtain ⟨unifier, _, checked⟩ := Option.bind_eq_some_iff.mp checked
            cases Option.some.inj checked
            rfl
      · cases executed

theorem step_preserves_evidence (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (hypotheses : List Preterm) (tables : Tables)
    (termsAvailable : ∀ (term : Nat) (entry : TermEntry), tables.terms[term]? = some entry →
      ∃ declaration body, Statements.termDecl tables.terms entry = some (declaration, body) ∧ signature term = some declaration)
    (definitionsAvailable : ∀ (term : Nat) (entry : TermEntry) (commands : List UnifyCmd),
      tables.terms[term]? = some entry → entry.value = some commands →
      ∃ declaration body, Statements.termDecl tables.terms entry = some (declaration, some body) ∧
        signature term = some declaration ∧ definitions term = some body ∧
        Preterm.HasType signature (declaration.arguments ++ body.dummies.map Binder.bound)
          body.expression [] declaration.resultSort)
    (theoremsAvailable : ∀ (theorem_ : Nat) (entry : ThmEntry), tables.thms[theorem_]? = some entry →
      ∃ declaration, Statements.theoremDecl tables.terms entry = some declaration ∧ theorems theorem_ = some declaration)
    (arities : ∀ term declaration, signature term = some declaration →
      Statements.arityOf tables.terms term = some declaration.arguments.length)
    (args : List ExprType) (seen : List Nat) (remaining : List ProofCmd) (command : ProofCmd)
    (before after finalState : Formats.MMB.State)
    (boundCounter : before.nextBound = (Statements.boundPositions args).length + seen.length)
    (variableCounter : before.varCount = args.length + seen.length)
    (typed : TypedStore signature
      (Statements.context args ++ (seen ++ dummySorts (command :: remaining)).map Binder.bound) before.store)
    (ranked : RankedStore
      (Statements.context args ++ (seen ++ dummySorts (command :: remaining)).map Binder.bound) before.store)
    (sound : StackSound signature definitions theorems
      (Statements.context args ++ (seen ++ dummySorts (command :: remaining)).map Binder.bound)
      hypotheses before.store before.stack)
    (heap : HeapSound signature definitions theorems
      (Statements.context args ++ (seen ++ dummySorts (command :: remaining)).map Binder.bound)
      hypotheses before.store before.heap)
    (executed : step tables .assertion before command = some after)
    (continued : run tables .assertion after remaining = some finalState)
    (original : finalState.hyps.reverse.mapM (Soundness.decode finalState.store) = some hypotheses) :
    let context := Statements.context args ++ (seen ++ dummySorts (command :: remaining)).map Binder.bound
    TypedStore signature context after.store ∧ RankedStore context after.store ∧
      StackSound signature definitions theorems context hypotheses after.store after.stack ∧
      HeapSound signature definitions theorems context hypotheses after.store after.heap := by
  dsimp only
  have typing := MMBRunSoundness.step_preserves_fixed_store signature tables termsAvailable args seen remaining command
    before after boundCounter variableCounter typed ranked executed
  refine ⟨typing.1, typing.2, ?_⟩
  cases command with
  | term term =>
      have capture := executed
      change stepTerm tables .assertion before term false = some after at capture
      unfold stepTerm at capture
      obtain ⟨entry, entryRead, _⟩ := Option.bind_eq_some_iff.mp capture
      obtain ⟨declaration, body, decoded, declared⟩ := termsAvailable term entry entryRead
      have fields := MMBRunSoundness.termDecl_fields tables.terms entry declaration body decoded
      exact (stepTerm_preserves_evidence tables .assertion before after term false entry declaration typed sound heap
        entryRead declared fields.1 fields.2.1 executed).2
  | termSave term =>
      have capture := executed
      change stepTerm tables .assertion before term true = some after at capture
      unfold stepTerm at capture
      obtain ⟨entry, entryRead, _⟩ := Option.bind_eq_some_iff.mp capture
      obtain ⟨declaration, body, decoded, declared⟩ := termsAvailable term entry entryRead
      have fields := MMBRunSoundness.termDecl_fields tables.terms entry declaration body decoded
      exact (stepTerm_preserves_evidence tables .assertion before after term true entry declaration typed sound heap
        entryRead declared fields.1 fields.2.1 executed).2
  | dummy sort =>
      have position := fixed_dummy_position args seen (dummySorts remaining) sort
      have history : dummySorts (.dummy sort :: remaining) = sort :: dummySorts remaining := rfl
      dsimp only at position
      have lookup : (Statements.context args ++ (seen ++ dummySorts (.dummy sort :: remaining)).map Binder.bound)[before.varCount]? =
          some (.bound sort) := by simpa only [history, variableCounter] using position.1
      have rankLookup : (Soundness.rankPositions
          (Statements.context args ++ (seen ++ dummySorts (.dummy sort :: remaining)).map Binder.bound)).getD
          before.nextBound before.nextBound = before.varCount := by
        simpa only [history, boundCounter, variableCounter] using position.2.1
      have rankBound : before.nextBound < (Soundness.rankPositions
          (Statements.context args ++ (seen ++ dummySorts (.dummy sort :: remaining)).map Binder.bound)).length := by
        simpa only [history, boundCounter] using position.2.2
      exact (step_dummy_preserves_evidence signature definitions theorems _ hypotheses tables .assertion before after sort
        typed ranked sound heap lookup rankLookup rankBound executed).2.2
  | ref index => exact step_ref_preserves_evidence tables .assertion before after index sound heap executed
  | thm theorem_ =>
      have checked : stepThm tables before theorem_ false = some after := by simpa only [step, ↓reduceIte] using executed
      have capture := checked
      unfold stepThm at capture
      obtain ⟨entry, entryRead, _⟩ := Option.bind_eq_some_iff.mp capture
      obtain ⟨declaration, decoded, available⟩ := theoremsAvailable theorem_ entry entryRead
      exact (MMBDependencySoundness.stepThm_preserves_evidence signature definitions theorems _ hypotheses tables before after theorem_ false
        entry declaration typed ranked sound heap entryRead decoded available arities checked).2.2
  | thmSave theorem_ =>
      have checked : stepThm tables before theorem_ true = some after := by simpa only [step, ↓reduceIte] using executed
      have capture := checked
      unfold stepThm at capture
      obtain ⟨entry, entryRead, _⟩ := Option.bind_eq_some_iff.mp capture
      obtain ⟨declaration, decoded, available⟩ := theoremsAvailable theorem_ entry entryRead
      exact (MMBDependencySoundness.stepThm_preserves_evidence signature definitions theorems _ hypotheses tables before after theorem_ true
        entry declaration typed ranked sound heap entryRead decoded available arities checked).2.2
  | hyp => exact (step_hyp_preserves_original_scope signature definitions theorems _ hypotheses tables before after finalState remaining
      typed ranked sound heap executed continued original).2.2
  | conv =>
      have keeps := step_conversion_keeps_store_heap tables .assertion before after .conv (by simp) executed
      exact ⟨step_conv_preserves_stack tables .assertion before after sound executed,
        by simpa only [keeps.1, keeps.2] using heap⟩
  | refl =>
      have keeps := step_conversion_keeps_store_heap tables .assertion before after .refl (by simp) executed
      exact ⟨step_refl_preserves_stack tables .assertion before after sound executed,
        by simpa only [keeps.1, keeps.2] using heap⟩
  | symm =>
      have keeps := step_conversion_keeps_store_heap tables .assertion before after .symm (by simp) executed
      exact ⟨step_symm_preserves_stack tables .assertion before after sound executed,
        by simpa only [keeps.1, keeps.2] using heap⟩
  | cong =>
      have keeps := step_conversion_keeps_store_heap tables .assertion before after .cong (by simp) executed
      exact ⟨step_cong_preserves_stack tables .assertion before after typed sound executed,
        by simpa only [keeps.1, keeps.2] using heap⟩
  | unfold =>
      have keeps := step_conversion_keeps_store_heap tables .assertion before after .unfold (by simp) executed
      exact ⟨MMBDefinitionUnificationSoundness.step_unfold_preserves_stack signature definitions theorems _ hypotheses tables .assertion before after
        typed ranked arities definitionsAvailable sound executed, by simpa only [keeps.1, keeps.2] using heap⟩
  | convCut =>
      have keeps := step_conversion_keeps_store_heap tables .assertion before after .convCut (by simp) executed
      exact ⟨step_convCut_preserves_stack tables .assertion before after sound executed,
        by simpa only [keeps.1, keeps.2] using heap⟩
  | convSave => exact step_convSave_preserves_evidence tables .assertion before after sound heap executed
  | save => exact step_save_preserves_evidence tables .assertion before after sound heap executed

end Mettapedia.Languages.MM0.MeTTa.MMBProofRunSoundness
