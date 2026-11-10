import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionContracts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionMachine

/-!
# Open observers with explicit client firings

Program and client actions use the same transform step and admission law.
Their label families remain distinct. Stability for the combined system is
exactly stability for each family; no total context map is assumed. This
supports partial, guarded and state-dependent environment interactions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionOpen
open Interface
open DistinctionObserver
universe uOb uT uH uO uS uF uL uC
variable {Obj : Type uOb} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uO} [DecidableEq O] {State : Type uS}
  {Fir : State → Type uF} {L : Type uL} {C : Type uC}
  (P : Interface.Step X O State Fir)
  (program : L → (s : State) → Fir s → Prop) (clients : C → (s : State) → Fir s → Prop)

def offers : L ⊕ C → (s : State) → Fir s → Prop
  | .inl label => program label
  | .inr label => clients label

theorem stable_iff {Code : Type*} (encode : State → Code) :
    Stable P (offers program clients) encode ↔
      Stable P program encode ∧ Stable P clients encode := by
  constructor
  · intro stable
    exact ⟨fun s t h a => stable s t h (.inl a), fun s t h a => stable s t h (.inr a)⟩
  · rintro ⟨left, right⟩ s t same label
    cases label with
    | inl a => exact left s t same a
    | inr a => exact right s t same a

theorem exact_iff {Code Value : Type*} (encode : State → Code) (read : State → Value) :
    Stable P (offers program clients) encode ∧ Reads encode read ↔
      (Stable P program encode ∧ Reads encode read) ∧ Stable P clients encode := by
  rw [stable_iff]
  tauto

namespace Controls
open DistinctionFinite

def swap (s : Bool × Bool) : Bool × Bool := (s.2, s.1)
def machine : Machine (Bool × Bool) Bool Bool :=
  ⟨Prod.fst, fun s a => [if a then swap s else s]⟩
def idleOffers (_ : Unit) (_ : Nat × (Bool × Bool)) (f : Bool × (Bool × Bool)) : Prop := f.1 = false
def client (_ : Unit) (_ : Nat × (Bool × Bool)) (f : Bool × (Bool × Bool)) : Prop := f.1 = true
def encode (s : Nat × (Bool × Bool)) : Bool := s.2.1

theorem program_stable : Stable machine.step.toStep idleOffers encode := by
  apply (stable_iff_matching _ _ _).mpr
  intro s t same a s' moved
  have payload := List.mem_singleton.mp (machine.no_extra_successor s false s' moved)
  refine ⟨(t.1 + 1, t.2), machine.every_successor_fires t false t.2 (List.mem_singleton_self _), ?_⟩
  change s'.2.1 = t.2.1
  change s'.2 = s.2 at payload
  rw [payload]
  exact same

theorem client_breaks_view : ¬ Stable machine.step.toStep client encode := by
  intro stable
  have step := machine.every_successor_fires (0, (false, false)) true (false, false)
    (List.mem_singleton_self _)
  obtain ⟨target, moved, same⟩ := (stable_iff_matching _ _ _).mp stable
    (0, (false, false)) (0, (false, true)) rfl () (1, (false, false)) step
  have payload := List.mem_singleton.mp (machine.no_extra_successor (0, (false, true)) true target moved)
  change target.2 = (true, false) at payload
  change false = target.2.1 at same
  rw [payload] at same
  cases same

theorem closed_exact_open_refused :
    (Stable machine.step.toStep idleOffers encode ∧ Reads encode encode) ∧
      ¬ Stable machine.step.toStep (offers idleOffers client) encode := by
  refine ⟨⟨program_stable, fun _ _ h => h⟩, ?_⟩
  intro stable
  exact client_breaks_view ((stable_iff _ _ _ _).mp stable).2

end Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionOpen
