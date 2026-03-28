import Mettapedia.Ethics.Core

set_option autoImplicit false

namespace Mettapedia.Ethics

universe u v w

namespace Theory

/-- Push a theory forward along a sentence translation function. -/
def map {α : Type u} {β : Type v} (f : α → β) (T : Theory α) : Theory β :=
  fun b => ∃ a, a ∈ T ∧ f a = b

theorem mem_map_of_mem {α : Type u} {β : Type v} {f : α → β} {T : Theory α} {a : α}
    (h : a ∈ T) : f a ∈ map f T :=
  ⟨a, h, rfl⟩

theorem map_singleton {α : Type u} {β : Type v} (f : α → β) (a : α) :
    map f ({a} : Theory α) = ({f a} : Theory β) := by
  funext b
  apply propext
  constructor
  · intro hb
    rcases hb with ⟨a', ha', hEq⟩
    cases ha'
    exact hEq.symm
  · intro hb
    refine ⟨a, rfl, ?_⟩
    exact hb.symm

end Theory

/--
Semantic entailment under an additional model-side premise `C`.

For ethics this is the contextual form used when a theory is evaluated inside a
particular situation description.
-/
def EntailsUnder {S : Type u} {M : Type v}
    (sem : Semantics S M) (T : Theory S) (C : M → Prop) (φ : S) : Prop :=
  ∀ m, C m → Models sem m T → sem.Sat m φ

theorem models_map_iff {S₁ : Type u} {S₂ : Type v} {M : Type w}
    (sem₁ : Semantics S₁ M) (sem₂ : Semantics S₂ M)
    (f : S₁ → S₂)
    (h_sat : ∀ m s, sem₁.Sat m s ↔ sem₂.Sat m (f s))
    (m : M) (T : Theory S₁) :
    Models sem₁ m T ↔ Models sem₂ m (Theory.map f T) := by
  constructor
  · intro hT s₂ hs₂
    rcases hs₂ with ⟨s₁, hs₁, hEq⟩
    have hSat₁ : sem₁.Sat m s₁ := hT s₁ hs₁
    have hSat₂ : sem₂.Sat m (f s₁) := (h_sat m s₁).1 hSat₁
    simpa [hEq] using hSat₂
  · intro hTf s₁ hs₁
    have hs₂ : f s₁ ∈ Theory.map f T := Theory.mem_map_of_mem (T := T) (f := f) hs₁
    have hSat₂ : sem₂.Sat m (f s₁) := hTf (f s₁) hs₂
    exact (h_sat m s₁).2 hSat₂

theorem entails_map_iff {S₁ : Type u} {S₂ : Type v} {M : Type w}
    (sem₁ : Semantics S₁ M) (sem₂ : Semantics S₂ M)
    (f : S₁ → S₂)
    (h_sat : ∀ m s, sem₁.Sat m s ↔ sem₂.Sat m (f s))
    (T : Theory S₁) (s : S₁) :
    Entails sem₁ T s ↔ Entails sem₂ (Theory.map f T) (f s) := by
  constructor
  · intro hEnt m hm
    have hm₁ : Models sem₁ m T := (models_map_iff sem₁ sem₂ f h_sat m T).2 hm
    have hSat₁ : sem₁.Sat m s := hEnt m hm₁
    exact (h_sat m s).1 hSat₁
  · intro hEnt m hm
    have hm₂ : Models sem₂ m (Theory.map f T) := (models_map_iff sem₁ sem₂ f h_sat m T).1 hm
    have hSat₂ : sem₂.Sat m (f s) := hEnt m hm₂
    exact (h_sat m s).2 hSat₂

theorem entails_map_iff_under {S₁ : Type u} {S₂ : Type v} {M : Type w}
    (sem₁ : Semantics S₁ M) (sem₂ : Semantics S₂ M)
    (f : S₁ → S₂)
    (h_sat : ∀ m s, sem₁.Sat m s ↔ sem₂.Sat m (f s))
    (T : Theory S₁) (C : M → Prop) (s : S₁) :
    EntailsUnder sem₁ T C s ↔ EntailsUnder sem₂ (Theory.map f T) C (f s) := by
  constructor
  · intro hEnt m hC hm
    have hm₁ : Models sem₁ m T := (models_map_iff sem₁ sem₂ f h_sat m T).2 hm
    have hSat₁ : sem₁.Sat m s := hEnt m hC hm₁
    exact (h_sat m s).1 hSat₁
  · intro hEnt m hC hm
    have hm₂ : Models sem₂ m (Theory.map f T) := (models_map_iff sem₁ sem₂ f h_sat m T).1 hm
    have hSat₂ : sem₂.Sat m (f s) := hEnt m hC hm₂
    exact (h_sat m s).2 hSat₂

/-- A theory is satisfiable if it has at least one model. -/
def Satisfiable {S : Type u} {M : Type v} (sem : Semantics S M) (T : Theory S) : Prop :=
  ∃ m, Models sem m T

/-- Two theories are equivalent if they have the same semantic consequences. -/
def Equivalent {S : Type u} {M : Type v} (sem : Semantics S M) (T₁ T₂ : Theory S) : Prop :=
  ∀ φ, Entails sem T₁ φ ↔ Entails sem T₂ φ

end Mettapedia.Ethics
