import Mettapedia.Ethics.Core
import Mettapedia.Ethics.Translation

set_option autoImplicit false

namespace Mettapedia.Ethics

universe u v

/-- A tiny typed sentence AST with connectives and quantifiers. -/
inductive StructuredSentence (World : Type u) (Atom : Type (max u 1)) : Type (u + 1) where
  | atom : Atom → StructuredSentence World Atom
  | and : StructuredSentence World Atom → StructuredSentence World Atom → StructuredSentence World Atom
  | or : StructuredSentence World Atom → StructuredSentence World Atom → StructuredSentence World Atom
  | not : StructuredSentence World Atom → StructuredSentence World Atom
  | imp : StructuredSentence World Atom → StructuredSentence World Atom → StructuredSentence World Atom
  | iff : StructuredSentence World Atom → StructuredSentence World Atom → StructuredSentence World Atom
  | forall_ {α : Type u} : (α → StructuredSentence World Atom) → StructuredSentence World Atom
  | exists_ {α : Type u} : (α → StructuredSentence World Atom) → StructuredSentence World Atom

namespace StructuredSentence

def map {World : Type u} {Atom₁ Atom₂ : Type (max u 1)} (f : Atom₁ → Atom₂) :
    StructuredSentence World Atom₁ → StructuredSentence World Atom₂
  | atom a => atom (f a)
  | and p q => and (map f p) (map f q)
  | or p q => or (map f p) (map f q)
  | not p => not (map f p)
  | imp p q => imp (map f p) (map f q)
  | iff p q => iff (map f p) (map f q)
  | forall_ g => forall_ (fun x => map f (g x))
  | exists_ g => exists_ (fun x => map f (g x))

def Sat {World : Type u} {Atom : Type (max u 1)} {M : Type v}
    (satAtom : M → Atom → Prop) :
    M → StructuredSentence World Atom → Prop
  | m, atom a => satAtom m a
  | m, and p q => Sat satAtom m p ∧ Sat satAtom m q
  | m, or p q => Sat satAtom m p ∨ Sat satAtom m q
  | m, not p => ¬ Sat satAtom m p
  | m, imp p q => Sat satAtom m p → Sat satAtom m q
  | m, iff p q => Sat satAtom m p ↔ Sat satAtom m q
  | m, forall_ g => ∀ x, Sat satAtom m (g x)
  | m, exists_ g => ∃ x, Sat satAtom m (g x)

def semantics {World : Type u} {Atom : Type (max u 1)} {M : Type v}
    (semAtom : Semantics Atom M) :
    Semantics (StructuredSentence World Atom) M :=
  ⟨fun m s => Sat (fun m a => semAtom.Sat m a) m s⟩

/-- Lift an atom-level translation relation to structured sentences. -/
def relLift {World : Type u} {Atom₁ Atom₂ : Type (max u 1)}
    (R : TranslationRel Atom₁ Atom₂) :
    TranslationRel (StructuredSentence World Atom₁) (StructuredSentence World Atom₂)
  | atom a₁, atom a₂ => R a₁ a₂
  | and p₁ q₁, and p₂ q₂ => relLift R p₁ p₂ ∧ relLift R q₁ q₂
  | or p₁ q₁, or p₂ q₂ => relLift R p₁ p₂ ∧ relLift R q₁ q₂
  | not p₁, not p₂ => relLift R p₁ p₂
  | imp p₁ q₁, imp p₂ q₂ => relLift R p₁ p₂ ∧ relLift R q₁ q₂
  | iff p₁ q₁, iff p₂ q₂ => relLift R p₁ p₂ ∧ relLift R q₁ q₂
  | forall_ (α := α₁) g₁, forall_ (α := α₂) g₂ =>
      ∃ h : α₁ = α₂, ∀ x : α₁, relLift R (g₁ x) (g₂ (cast h x))
  | exists_ (α := α₁) g₁, exists_ (α := α₂) g₂ =>
      ∃ h : α₁ = α₂, ∀ x : α₁, relLift R (g₁ x) (g₂ (cast h x))
  | _, _ => False

/-- Recursively lift witness-carrying atom translations to structured sentences. -/
def witnessedLift {World : Type u} {Atom₁ Atom₂ : Type (max u 1)}
    (R : TranslationRel Atom₁ Atom₂)
    (choose : ∀ a : Atom₁, Witnessed R a) :
    ∀ s : StructuredSentence World Atom₁,
      Witnessed (relLift (World := World) (Atom₁ := Atom₁) (Atom₂ := Atom₂) R) s
  | atom a =>
      ⟨atom (choose a).fst, by
        simpa [relLift] using (choose a).snd⟩
  | and p q =>
      let hp := witnessedLift R choose p
      let hq := witnessedLift R choose q
      ⟨and hp.fst hq.fst, by
        simpa [relLift] using And.intro hp.snd hq.snd⟩
  | or p q =>
      let hp := witnessedLift R choose p
      let hq := witnessedLift R choose q
      ⟨or hp.fst hq.fst, by
        simpa [relLift] using And.intro hp.snd hq.snd⟩
  | not p =>
      let hp := witnessedLift R choose p
      ⟨not hp.fst, by
        simpa [relLift] using hp.snd⟩
  | imp p q =>
      let hp := witnessedLift R choose p
      let hq := witnessedLift R choose q
      ⟨imp hp.fst hq.fst, by
        simpa [relLift] using And.intro hp.snd hq.snd⟩
  | iff p q =>
      let hp := witnessedLift R choose p
      let hq := witnessedLift R choose q
      ⟨iff hp.fst hq.fst, by
        simpa [relLift] using And.intro hp.snd hq.snd⟩
  | forall_ g =>
      ⟨forall_ (fun x => (witnessedLift R choose (g x)).fst), by
        refine ⟨rfl, ?_⟩
        intro x
        simpa [relLift] using (witnessedLift R choose (g x)).snd⟩
  | exists_ g =>
      ⟨exists_ (fun x => (witnessedLift R choose (g x)).fst), by
        refine ⟨rfl, ?_⟩
        intro x
        simpa [relLift] using (witnessedLift R choose (g x)).snd⟩

theorem sat_map_iff {World : Type u} {Atom₁ Atom₂ : Type (max u 1)} {M : Type v}
    (sem₁ : Semantics Atom₁ M) (sem₂ : Semantics Atom₂ M) (f : Atom₁ → Atom₂)
    (h_sat : ∀ m a, sem₁.Sat m a ↔ sem₂.Sat m (f a))
    (m : M) (s : StructuredSentence World Atom₁) :
    (semantics (World := World) sem₁).Sat m s ↔
      (semantics (World := World) sem₂).Sat m (map f s) := by
  induction s generalizing m with
  | atom a =>
      simpa [semantics, Sat, map] using (h_sat m a)
  | and p q ihp ihq =>
      have ihp' := ihp m
      have ihq' := ihq m
      have ihpSat :
          Sat (fun m a => sem₁.Sat m a) m p ↔
            Sat (fun m a => sem₂.Sat m a) m (map f p) := by
        simpa [semantics] using ihp'
      have ihqSat :
          Sat (fun m a => sem₁.Sat m a) m q ↔
            Sat (fun m a => sem₂.Sat m a) m (map f q) := by
        simpa [semantics] using ihq'
      constructor
      · intro h
        exact ⟨(ihpSat).1 h.1, (ihqSat).1 h.2⟩
      · intro h
        exact ⟨(ihpSat).2 h.1, (ihqSat).2 h.2⟩
  | or p q ihp ihq =>
      have ihp' := ihp m
      have ihq' := ihq m
      have ihpSat :
          Sat (fun m a => sem₁.Sat m a) m p ↔
            Sat (fun m a => sem₂.Sat m a) m (map f p) := by
        simpa [semantics] using ihp'
      have ihqSat :
          Sat (fun m a => sem₁.Sat m a) m q ↔
            Sat (fun m a => sem₂.Sat m a) m (map f q) := by
        simpa [semantics] using ihq'
      constructor
      · intro h
        cases h with
        | inl hp => exact Or.inl ((ihpSat).1 hp)
        | inr hq => exact Or.inr ((ihqSat).1 hq)
      · intro h
        cases h with
        | inl hp => exact Or.inl ((ihpSat).2 hp)
        | inr hq => exact Or.inr ((ihqSat).2 hq)
  | not p ih =>
      have ih' := ih m
      constructor
      · intro hNot hSat₂
        have hSat₁ : (semantics (World := World) sem₁).Sat m p := ih'.2 hSat₂
        exact hNot hSat₁
      · intro hNot hSat₁
        have hSat₂ : (semantics (World := World) sem₂).Sat m (map f p) := ih'.1 hSat₁
        exact hNot hSat₂
  | imp p q ihp ihq =>
      have ihp' := ihp m
      have ihq' := ihq m
      constructor
      · intro hImp hSat₂p
        have hSat₁p : (semantics (World := World) sem₁).Sat m p := ihp'.2 hSat₂p
        have hSat₁q : (semantics (World := World) sem₁).Sat m q := hImp hSat₁p
        exact ihq'.1 hSat₁q
      · intro hImp hSat₁p
        have hSat₂p : (semantics (World := World) sem₂).Sat m (map f p) := ihp'.1 hSat₁p
        have hSat₂q : (semantics (World := World) sem₂).Sat m (map f q) := hImp hSat₂p
        exact ihq'.2 hSat₂q
  | iff p q ihp ihq =>
      have ihp' := ihp m
      have ihq' := ihq m
      constructor
      · intro hIff
        constructor
        · intro hSat₂p
          have hSat₁p : (semantics (World := World) sem₁).Sat m p := ihp'.2 hSat₂p
          have hSat₁q : (semantics (World := World) sem₁).Sat m q := hIff.1 hSat₁p
          exact ihq'.1 hSat₁q
        · intro hSat₂q
          have hSat₁q : (semantics (World := World) sem₁).Sat m q := ihq'.2 hSat₂q
          have hSat₁p : (semantics (World := World) sem₁).Sat m p := hIff.2 hSat₁q
          exact ihp'.1 hSat₁p
      · intro hIff
        constructor
        · intro hSat₁p
          have hSat₂p : (semantics (World := World) sem₂).Sat m (map f p) := ihp'.1 hSat₁p
          have hSat₂q : (semantics (World := World) sem₂).Sat m (map f q) := hIff.1 hSat₂p
          exact ihq'.2 hSat₂q
        · intro hSat₁q
          have hSat₂q : (semantics (World := World) sem₂).Sat m (map f q) := ihq'.1 hSat₁q
          have hSat₂p : (semantics (World := World) sem₂).Sat m (map f p) := hIff.2 hSat₂q
          exact ihp'.2 hSat₂p
  | forall_ g ih =>
      constructor
      · intro h x
        exact (ih x m).1 (h x)
      · intro h x
        exact (ih x m).2 (h x)
  | exists_ g ih =>
      constructor
      · intro h
        rcases h with ⟨x, hx⟩
        exact ⟨x, (ih x m).1 hx⟩
      · intro h
        rcases h with ⟨x, hx⟩
        exact ⟨x, (ih x m).2 hx⟩

theorem models_map_iff {World : Type u} {Atom₁ Atom₂ : Type (max u 1)} {M : Type v}
    (sem₁ : Semantics Atom₁ M) (sem₂ : Semantics Atom₂ M) (f : Atom₁ → Atom₂)
    (h_sat : ∀ m a, sem₁.Sat m a ↔ sem₂.Sat m (f a))
    (m : M) (T : Theory (StructuredSentence World Atom₁)) :
    Models (semantics (World := World) sem₁) m T ↔
      Models (semantics (World := World) sem₂) m (Theory.map (map f) T) := by
  simpa using
    (Mettapedia.Ethics.models_map_iff
      (sem₁ := semantics (World := World) sem₁)
      (sem₂ := semantics (World := World) sem₂)
      (f := map f)
      (h_sat := fun m s => sat_map_iff (sem₁ := sem₁) (sem₂ := sem₂) (f := f) h_sat m s)
      (m := m) (T := T))

theorem entails_map_iff {World : Type u} {Atom₁ Atom₂ : Type (max u 1)} {M : Type v}
    (sem₁ : Semantics Atom₁ M) (sem₂ : Semantics Atom₂ M) (f : Atom₁ → Atom₂)
    (h_sat : ∀ m a, sem₁.Sat m a ↔ sem₂.Sat m (f a))
    (T : Theory (StructuredSentence World Atom₁)) (s : StructuredSentence World Atom₁) :
    Entails (semantics (World := World) sem₁) T s ↔
      Entails (semantics (World := World) sem₂) (Theory.map (map f) T) (map f s) := by
  simpa using
    (Mettapedia.Ethics.entails_map_iff
      (sem₁ := semantics (World := World) sem₁)
      (sem₂ := semantics (World := World) sem₂)
      (f := map f)
      (h_sat := fun m s => sat_map_iff (sem₁ := sem₁) (sem₂ := sem₂) (f := f) h_sat m s)
      (T := T) (s := s))

end StructuredSentence

end Mettapedia.Ethics
