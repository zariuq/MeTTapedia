import Mettapedia.Languages.MeTTa.PureKernel.Renaming

namespace Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming

/-- A closed declaration entry for a global kernel constant. -/
structure DeclEntry where
  type : PureTm 0
  value? : Option (PureTm 0) := none
deriving Repr

/-- Global declaration environment for kernel constants. -/
structure DeclEnv where
  entries : DeclName → Option DeclEntry

/-- `Efull` preserves all declaration entries already present in `Epre`. -/
def Extends (Epre Efull : DeclEnv) : Prop :=
  ∀ {c : DeclName} {entry : DeclEntry},
    Epre.entries c = some entry →
    Efull.entries c = some entry

/-- Empty declaration environment (fail-closed). -/
def empty : DeclEnv := { entries := fun _ => none }

/-- Lookup type of a constant. -/
def typeOf? (E : DeclEnv) (c : DeclName) : Option (PureTm 0) :=
  (E.entries c).map (fun e => e.type)

/-- Lookup optional definitional unfolding of a constant. -/
def valueOf? (E : DeclEnv) (c : DeclName) : Option (PureTm 0) :=
  (E.entries c).bind (fun e => e.value?)

/-- Insert/update a constant entry. -/
def insert (E : DeclEnv) (c : DeclName) (entry : DeclEntry) : DeclEnv :=
  { entries := fun d => if d == c then some entry else E.entries d }

/-- Build a declaration environment from a list of named entries. Earlier entries shadow later ones. -/
def ofList : List (DeclName × DeclEntry) → DeclEnv
  | [] => empty
  | (c, e) :: rest => insert (ofList rest) c e

/-- Lift a closed term into any de Bruijn depth. -/
def liftClosed (t : PureTm 0) : PureTm n :=
  rename (fun i : Fin 0 => nomatch i) t

@[simp] theorem typeOf_empty (c : DeclName) : typeOf? empty c = none := rfl

@[simp] theorem valueOf_empty (c : DeclName) : valueOf? empty c = none := rfl

@[simp] theorem typeOf_insert_eq (E : DeclEnv) (c : DeclName) (entry : DeclEntry) :
    typeOf? (insert E c entry) c = some entry.type := by
  simp [typeOf?, insert]

@[simp] theorem valueOf_insert_eq (E : DeclEnv) (c : DeclName) (entry : DeclEntry) :
    valueOf? (insert E c entry) c = entry.value? := by
  simp [valueOf?, insert]

theorem Extends.typeOf {Epre Efull : DeclEnv} (hExt : Extends Epre Efull)
    {c : DeclName} {A0 : PureTm 0}
    (hTy : typeOf? Epre c = some A0) :
    typeOf? Efull c = some A0 := by
  unfold typeOf? at hTy ⊢
  cases hEntries : Epre.entries c with
  | none =>
      simp [hEntries] at hTy
  | some entry =>
      have hType : entry.type = A0 := by
        simpa [hEntries] using hTy
      have hFull : Efull.entries c = some entry := hExt hEntries
      simp [hFull, hType]

theorem Extends.valueOf {Epre Efull : DeclEnv} (hExt : Extends Epre Efull)
    {c : DeclName} {v0 : PureTm 0}
    (hVal : valueOf? Epre c = some v0) :
    valueOf? Efull c = some v0 := by
  unfold valueOf? at hVal ⊢
  cases hEntries : Epre.entries c with
  | none =>
      simp [hEntries] at hVal
  | some entry =>
      have hValue : entry.value? = some v0 := by
        simpa [hEntries] using hVal
      have hFull : Efull.entries c = some entry := hExt hEntries
      simp [hFull, hValue]

theorem Extends.refl (E : DeclEnv) : Extends E E := by
  intro c entry h
  exact h

theorem Extends.trans {E₁ E₂ E₃ : DeclEnv}
    (h₁₂ : Extends E₁ E₂)
    (h₂₃ : Extends E₂ E₃) :
    Extends E₁ E₃ := by
  intro c entry h
  exact h₂₃ (h₁₂ h)

@[simp] theorem liftClosed_u0 : liftClosed (.u0 : PureTm 0) = (.u0 : PureTm n) := rfl
@[simp] theorem liftClosed_u1 : liftClosed (.u1 : PureTm 0) = (.u1 : PureTm n) := rfl
@[simp] theorem liftClosed_const (c : DeclName) : liftClosed (.const c : PureTm 0) = (.const c : PureTm n) := rfl
@[simp] theorem liftClosed_zero (t : PureTm 0) : liftClosed (n := 0) t = t := by
  unfold liftClosed
  calc
    rename (fun i : Fin 0 => nomatch i) t = rename (idRen (n := 0)) t := by
      apply rename_ext
      intro i
      nomatch i
    _ = t := by
      exact rename_id (t := t)

@[simp] theorem rename_liftClosed {n m : Nat} (ρ : Ren n m) (t : PureTm 0) :
    rename ρ (liftClosed (n := n) t) = liftClosed (n := m) t := by
  unfold liftClosed
  calc
    rename ρ (rename (fun i : Fin 0 => nomatch i) t)
        = rename (fun i : Fin 0 => ρ ((fun j : Fin 0 => nomatch j) i)) t := by
            exact rename_comp (ρ₂ := ρ) (ρ₁ := (fun i : Fin 0 => nomatch i)) t
    _ = rename (fun i : Fin 0 => nomatch i) t := by
          apply rename_ext
          intro i
          nomatch i
    _ = liftClosed (n := m) t := rfl

end Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv
