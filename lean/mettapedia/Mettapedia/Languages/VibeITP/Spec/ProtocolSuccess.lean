import Mettapedia.Languages.VibeITP.Spec.Protocol
import Mathlib.Data.List.Basic

/-! Success inversion for the protocol's checked reads and sequential effects. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolSuccess

theorem bind_ok_iff {α β : Type} (first : StepM α) (next : α → StepM β) (result : β) :
    (first >>= next) = .ok result ↔ ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error error => simp [bind, Except.bind]
  | ok value => simp [bind, Except.bind]

theorem need_ok_iff {α : Type} (space : Space) (slot : Option α) (value : α) :
    need space slot = .ok value ↔ slot = some value := by
  cases slot <;> simp [need]

theorem inProofs_ok_iff (state : State) (primitive : Primitive) :
    state.inProofs primitive = .ok () ↔ state.phase = .proofs := by
  cases phase : state.phase <;> simp [State.inProofs, phase]

theorem mapM_success {α β : Type} (effect : α → StepM β) (property : β → Prop)
    (valid : ∀ source result, effect source = .ok result → property result) :
    ∀ (inputs : List α) (outputs : List β), inputs.mapM effect = .ok outputs →
      outputs.length = inputs.length ∧ ∀ output ∈ outputs, property output := by
  intro inputs
  induction inputs with
  | nil =>
    intro outputs accepted
    simp [pure, Except.pure] at accepted
    subst outputs
    simp
  | cons input inputs ih =>
    intro outputs accepted
    rw [List.mapM_cons] at accepted
    obtain ⟨output, first, following⟩ := (bind_ok_iff _ _ _).mp accepted
    obtain ⟨rest, tail, complete⟩ := (bind_ok_iff _ _ _).mp following
    have equal : output :: rest = outputs := Except.ok.inj complete
    subst outputs
    obtain ⟨length, retained⟩ := ih rest tail
    constructor
    · simp [length]
    · intro result member
      rcases List.mem_cons.mp member with newest | previous
      · subst result
        exact valid input output first
      · exact retained result previous

theorem mapM_need_success {α : Type} (space : Space) (slots : Nat → Option α)
    (property : α → Prop) (valid : ∀ slot value, slots slot = some value → property value)
    (inputs : List Nat) (outputs : List α)
    (accepted : inputs.mapM (fun slot => need space (slots slot)) = .ok outputs) :
    outputs.length = inputs.length ∧ ∀ output ∈ outputs, property output :=
  mapM_success _ property (fun slot value found =>
    valid slot value ((need_ok_iff space (slots slot) value).mp found)) inputs outputs accepted

end Mettapedia.Languages.VibeITP.Spec.ProtocolSuccess
