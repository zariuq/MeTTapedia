import Mettapedia.Languages.VibeITP.Spec.ProtocolMaintenance
import Mettapedia.Languages.VibeITP.Spec.ProtocolDefinitions
import Mettapedia.Languages.VibeITP.Spec.ProtocolInference

/-! Every successful bounded static instruction preserves the independent kernel invariant. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolStaticPreservation

open ProtocolExecution ProtocolInvariant ProtocolAdmission ProtocolStorage ProtocolMaintenance
open ProtocolDefinitions ProtocolInference ProtocolSuccess

theorem wellFormedList_of_members (sig : Sig) (terms : List Term)
    (formed : ∀ term ∈ terms, WellFormed sig term = true) : WellFormedList sig terms = true := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
    simp only [WellFormedList, Bool.and_eq_true]
    exact ⟨formed term (by simp), ih (fun value member => formed value (List.mem_cons_of_mem _ member))⟩

theorem placeChallenge_result {before after : State} {destination : Nat} {statement : Term}
    (accepted : before.placeChallenge destination statement = .ok after) :
    after = { before with challenges := setSlot before.challenges destination (some statement) } := by
  unfold State.placeChallenge at accepted
  split at accepted
  · cases accepted
  · exact (Except.ok.inj accepted).symm

theorem execute_preserves {before : ObservedState} {after : State} (instruction : Instr)
    (invariant : LogicalInvariant before) (bounded : instruction.MachineBounded)
    (accepted : execute before.kernel instruction = some (.ok after)) :
    LogicalInvariant ⟨after, before.observations⟩ := by
  cases instruction with
  | fvarNew arity destination =>
    have allocated := allocate_invariant before (SymInfo.fvarOf arity) invariant (by
      intro _ binder member
      simpa [SymInfo.fvarOf] using (List.eq_of_mem_replicate member))
    exact place_symbol_invariant (before := ⟨(before.kernel.allocate (SymInfo.fvarOf arity)).2,
      before.observations⟩) (symbol := .fresh before.kernel.nextFresh) (destination := destination) allocated
      (by simp [State.sig, State.allocate, sigOf, setSlot]) (Option.some.inj accepted)
  | constNew binders destination =>
    have allocated := allocate_invariant before ⟨.constant, binders⟩ invariant (by
      intro impossible
      cases impossible)
    exact place_symbol_invariant (before := ⟨(before.kernel.allocate ⟨.constant, binders⟩).2,
      before.observations⟩) (symbol := .fresh before.kernel.nextFresh) (destination := destination) allocated
      (by simp [State.sig, State.allocate, sigOf, setSlot]) (Option.some.inj accepted)
  | symbolSwap first second =>
    have same := Except.ok.inj (Option.some.inj accepted)
    rw [← same]
    exact swap_symbol_invariant before first second invariant
  | symbolFree slot =>
    simp only [execute, Option.some.injEq] at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · have same := Except.ok.inj accepted
        rw [← same]
        exact clear_symbol_invariant before slot invariant
  | termNewBVar index destination =>
    simp only [execute, Option.some.injEq] at accepted
    split at accepted
    · exact place_term_invariant invariant (by simp [WellFormed, show index + 1 < wordBound by assumption]) accepted
    · cases accepted
  | termNewLiteral bytes destination =>
    simp only [execute, Option.some.injEq] at accepted
    split at accepted
    · exact place_term_invariant invariant (by simp [WellFormed, show bytes.length + 8 < wordBound by assumption]) accepted
    · cases accepted
  | termNewApp source arguments destination =>
    have run := Option.some.inj accepted
    obtain ⟨head, read, matched⟩ := (bind_ok_iff _ _ _).mp run
    cases head with
    | bvarMarker => cases matched
    | literalMarker => cases matched
    | sym symbol =>
      dsimp only at matched
      have allocated := invariant.symbols source symbol ((need_ok_iff _ _ _).mp read)
      cases signature : before.kernel.sig symbol with
      | none => simp [signature] at allocated
      | some info =>
        split at matched
        · rename_i arity
          obtain ⟨terms, reads, placed⟩ := (bind_ok_iff _ _ _).mp matched
          obtain ⟨length, formed⟩ := mapM_need_success .term before.kernel.terms
            (fun term => WellFormed before.kernel.sig term = true) invariant.terms arguments terms reads
          have exactArity : terms.length = info.arity := by
            rw [length, arity]
            simp [symArity, signature]
          have termFormed : WellFormed before.kernel.sig (.app symbol terms) = true := by
            simp [WellFormed, signature, exactArity, wellFormedList_of_members _ _ formed]
          exact place_term_invariant invariant termFormed placed
        · cases matched
  | termSwap first second =>
    have same := Except.ok.inj (Option.some.inj accepted)
    rw [← same]
    exact swap_term_invariant before first second invariant
  | termFree slot =>
    simp only [execute, Option.some.injEq] at accepted
    split at accepted
    · cases accepted
    · have same := Except.ok.inj accepted
      rw [← same]
      exact clear_term_invariant before slot invariant
  | addAxiom source destination =>
    simp only [execute, Option.some.injEq] at accepted
    cases phase : before.kernel.phase with
    | proofs => simp [phase] at accepted
    | setup =>
      simp only [phase] at accepted
      obtain ⟨statement, read, closedCheck⟩ := (bind_ok_iff _ _ _).mp accepted
      have formed := invariant.terms source statement ((need_ok_iff _ _ _).mp read)
      split at closedCheck
      · rename_i closed
        obtain ⟨placed, placement, complete⟩ := (bind_ok_iff _ _ _).mp closedCheck
        have final : { placed with axioms := placed.axioms ++ [statement] } = after := Except.ok.inj complete
        have base := admit_axiom_invariant before statement invariant formed closed
        have newStatement : DerivesWithExecution
            ({ before.kernel with axioms := before.kernel.axioms ++ [statement] } : State).theory
            before.observations statement := .axiom (by simp [State.theory])
        have published := set_theorem_invariant _ destination statement base newStatement
        rw [placeTheorem_result placement] at final
        rw [← final]
        exact published
      · cases closedCheck
  | thmExchange theoremSlot termSlot =>
    have run := Option.some.inj accepted
    obtain ⟨statement, _, following⟩ := (bind_ok_iff _ _ _).mp run
    obtain ⟨term, _, matched⟩ := (bind_ok_iff _ _ _).mp following
    split at matched
    · have same : before.kernel = after := Except.ok.inj matched
      rw [← same]
      exact invariant
    · cases matched
  | thmFree slot =>
    simp only [execute, Option.some.injEq] at accepted
    split at accepted
    · cases accepted
    · have same := Except.ok.inj accepted
      rw [← same]
      exact clear_theorem_invariant before slot invariant
  | thmSwap first second =>
    have same := Except.ok.inj (Option.some.inj accepted)
    rw [← same]
    exact swap_theorem_invariant before first second invariant
  | challengeAdd source destination =>
    have run := Option.some.inj accepted
    obtain ⟨statement, _, following⟩ := (bind_ok_iff _ _ _).mp run
    obtain ⟨placed, placement, complete⟩ := (bind_ok_iff _ _ _).mp following
    have final : ({ placed with
        openChallenges := placed.openChallenges + 1
        proofChallenges := match before.kernel.phase with
          | .proofs => placed.proofChallenges + 1
          | .setup => placed.proofChallenges } : State) = after := Except.ok.inj complete
    rw [placeChallenge_result placement] at final
    rw [← final]
    exact logical_frame _ _ _ invariant rfl rfl rfl rfl rfl rfl
  | challengeSatisfy source theoremSlot =>
    simp only [execute, Option.some.injEq] at accepted
    cases phase : before.kernel.phase with
    | setup => simp [phase] at accepted
    | proofs =>
      simp only [phase] at accepted
      obtain ⟨statement, read, matched⟩ := (bind_ok_iff _ _ _).mp accepted
      have derived := invariant.theorems theoremSlot statement ((need_ok_iff _ _ _).mp read)
      cases challenge : before.kernel.challenges source with
      | none => simp [challenge] at matched
      | some goal =>
        simp only [challenge] at matched
        split at matched
        · have same : ({ before.kernel with
              challenges := setSlot before.kernel.challenges source none
              openChallenges := before.kernel.openChallenges - 1
              satisfied := before.kernel.satisfied ++ [statement] } : State) = after := by
            simpa only [phase] using Except.ok.inj matched
          rw [← same]
          constructor
          · exact invariant.theory
          · exact invariant.symbols
          · exact invariant.terms
          · exact invariant.theorems
          · intro value member
            rcases List.mem_append.mp member with previous | newest
            · exact invariant.satisfied value previous
            · have equal : value = statement := by simpa using newest
              subst value
              exact derived
        · cases matched
  | modusPonens implication premise destination =>
    exact modusPonens_preserved implication premise destination invariant accepted
  | thmInstantiate theoremSlot symbolSlot valueSlot destination =>
    exact instantiate_preserved theoremSlot symbolSlot valueSlot destination invariant accepted
  | defineConst fvars hints valueSlot symbolDestination theoremDestination =>
    exact defineConst_preserved fvars hints valueSlot symbolDestination theoremDestination invariant accepted
  | litIsNat value destination =>
    exact litIsNat_preserved value destination invariant
      (bounded value (by simp [Instr.machineWords])) accepted
  | litLt left right destination =>
    exact litLt_preserved left right destination invariant
      (bounded right (by simp [Instr.machineWords])) accepted
  | litAdd left right destination =>
    exact litAdd_preserved left right destination invariant
      (bounded left (by simp [Instr.machineWords])) (bounded right (by simp [Instr.machineWords])) accepted
  | litMul left right destination =>
    exact litMul_preserved left right destination invariant
      (bounded left (by simp [Instr.machineWords])) (bounded right (by simp [Instr.machineWords])) accepted
  | litDiv left right destination =>
    exact litDiv_preserved left right destination invariant
      (bounded left (by simp [Instr.machineWords])) (bounded right (by simp [Instr.machineWords])) accepted
  | litLength source destination =>
    exact litLength_preserved source destination invariant accepted
  | litGet source index destination =>
    exact litGet_preserved source index destination invariant accepted
  | jit safe destination output => simp [execute] at accepted

end Mettapedia.Languages.VibeITP.Spec.ProtocolStaticPreservation
