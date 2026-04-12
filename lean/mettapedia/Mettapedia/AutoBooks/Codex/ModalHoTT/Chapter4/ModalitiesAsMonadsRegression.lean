import Mettapedia.AutoBooks.Codex.ModalHoTT.Chapter4.ModalitiesAsMonads

namespace Mettapedia.AutoBooks.Codex.ModalHoTT.Chapter4

/-!
# Modal HoTT, Chapter 4 Regression

Positive and negative canaries for the `owner : Dog → Person` example from the
opening discussion of modalities as monads.
-/

namespace Regression

inductive Person where
  | alice
  | bob
  deriving DecidableEq, Repr

inductive Dog where
  | otis
  | mabel
  | fido
  deriving DecidableEq, Repr

open Person Dog

def owner : Dog → Person
  | .otis => .alice
  | .mabel => .alice
  | .fido => .bob

def pugs : Set Dog := {d | d = .otis}

def bobDogs : Set Dog := {d | d = .fido}

example : .otis ∈ possibleAlong owner pugs := by
  rw [mem_possibleAlong_iff]
  exact ⟨.otis, by simp [pugs], rfl⟩

example : .mabel ∈ possibleAlong owner pugs := by
  rw [mem_possibleAlong_iff]
  exact ⟨.otis, by simp [pugs], by simp [owner]⟩

example : .fido ∉ possibleAlong owner pugs := by
  rw [mem_possibleAlong_iff]
  intro h
  rcases h with ⟨d, hd, howner⟩
  cases d <;> simp [pugs, owner] at hd howner

example : .fido ∈ necessaryAlong owner bobDogs := by
  rw [mem_necessaryAlong_iff]
  intro d hd
  cases d <;> simp [bobDogs, owner] at hd ⊢

example : .otis ∉ necessaryAlong owner pugs := by
  rw [mem_necessaryAlong_iff]
  intro hall
  have hmabel : Dog.mabel ∈ pugs := hall .mabel (by simp [owner])
  simp [pugs] at hmabel

end Regression

end Mettapedia.AutoBooks.Codex.ModalHoTT.Chapter4
