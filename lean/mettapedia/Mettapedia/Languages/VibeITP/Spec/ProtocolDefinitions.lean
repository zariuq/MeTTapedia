import Mettapedia.Languages.VibeITP.Spec.ProtocolStorage
import Mettapedia.Languages.VibeITP.Spec.ProtocolSuccess

/-! Fresh checked definitions extend the theory before their equation is published. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolDefinitions

open ProtocolExecution ProtocolInvariant ProtocolAdmission ProtocolStorage ProtocolSuccess
open Mettapedia.Languages.VibeITP.Presentation

theorem placeSymbol_result {before after : State} {destination : Nat} {symbol : SlotSymbol}
    (accepted : before.placeSymbol destination symbol = .ok after) :
    after = { before with symbols := setSlot before.symbols destination (some symbol) } := by
  unfold State.placeSymbol at accepted
  split at accepted
  · cases accepted
  · exact (Except.ok.inj accepted).symm

theorem allocate_definition_invariant (before : ObservedState) (parameters : List SymId)
    (hints : List Nat) (value : Term) (invariant : LogicalInvariant before)
    (formed : WellFormed before.kernel.sig value = true)
    (admitted : definitionAdmissible before.kernel.sig parameters hints value = true) :
    let allocated := (before.kernel.allocate (definitionInfo before.kernel.sig parameters)).2
    let definition : Definition := ⟨.fresh before.kernel.nextFresh, parameters, value⟩
    LogicalInvariant ⟨{ allocated with definitions := allocated.definitions ++ [definition] },
      before.observations⟩ := by
  dsimp only
  have allocated := allocate_invariant before (definitionInfo before.kernel.sig parameters) invariant
    (by intro impossible; cases impossible)
  exact replace_admissions_invariant _ _ _ allocated
    (allocate_definition_hosted before.kernel parameters hints value invariant.theory formed admitted)
    (fun _ member => member) (fun _ member => List.mem_append_left _ member)

theorem defineConst_preserved {before : ObservedState} {after : State}
    (fvarSlots hints : List Nat) (valueSlot symbolDestination theoremDestination : Nat)
    (invariant : LogicalInvariant before)
    (accepted : execute before.kernel (.defineConst fvarSlots hints valueSlot symbolDestination
      theoremDestination) = some (.ok after)) :
    LogicalInvariant ⟨after, before.observations⟩ := by
  have run := Option.some.inj accepted
  obtain ⟨heads, _, following⟩ := (bind_ok_iff _ _ _).mp run
  obtain ⟨value, valueRead, matched⟩ := (bind_ok_iff _ _ _).mp following
  have formed := invariant.terms valueSlot value ((need_ok_iff _ _ _).mp valueRead)
  cases ids : slotIds heads with
  | none => simp [ids] at matched
  | some parameters =>
    simp only [ids] at matched
    split at matched
    · rename_i admitted
      obtain ⟨declared, declaration, following⟩ := (bind_ok_iff _ _ _).mp matched
      obtain ⟨published, publication, complete⟩ := (bind_ok_iff _ _ _).mp following
      have final : { published with definitions := published.definitions ++
          [⟨.fresh before.kernel.nextFresh, parameters, value⟩] } = after := Except.ok.inj complete
      let allocated := (before.kernel.allocate (definitionInfo before.kernel.sig parameters)).2
      let definition : Definition := ⟨.fresh before.kernel.nextFresh, parameters, value⟩
      let admittedState : State := { allocated with definitions := allocated.definitions ++ [definition] }
      have base : LogicalInvariant ⟨admittedState, before.observations⟩ :=
        allocate_definition_invariant before parameters hints value invariant formed admitted
      have newSymbol : (admittedState.sig (.fresh before.kernel.nextFresh)).isSome = true := by
        simp [admittedState, allocated, State.sig, State.allocate, sigOf, setSlot]
      have declaredInvariant := set_symbol_invariant ⟨admittedState, before.observations⟩
        symbolDestination (.fresh before.kernel.nextFresh) base newSymbol
      have known := definitionAdmissible_parameters_known before.kernel.sig parameters hints value admitted
      have extension := allocate_sig_extension before.kernel (definitionInfo before.kernel.sig parameters)
        invariant.theory
      have equation : DerivesWithExecution admittedState.theory before.observations
          (definitionStatement before.kernel.sig (.fresh before.kernel.nextFresh) parameters value) := by
        rw [← definitionStatement_sigExt extension (.fresh before.kernel.nextFresh) parameters value known]
        exact .definition (d := definition) (by simp [admittedState, definition, State.theory])
      have finalInvariant := set_theorem_invariant _ theoremDestination _ declaredInvariant equation
      rw [placeTheorem_result publication, placeSymbol_result declaration] at final
      rw [← final]
      exact finalInvariant
    · cases matched

end Mettapedia.Languages.VibeITP.Spec.ProtocolDefinitions
