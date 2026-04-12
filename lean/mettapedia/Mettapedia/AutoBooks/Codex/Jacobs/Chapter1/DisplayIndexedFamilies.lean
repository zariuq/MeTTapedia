import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Basic

namespace Mettapedia.AutoBooks.Codex.Jacobs.Chapter1

/-!
# Jacobs, Chapter 1: Display-Indexed Families

This file formalizes the concrete sets-level display-indexing and substitution
story from the opening pages of Jacobs Chapter 1.
-/

universe u v

/-- A set-indexed family in display form: a projection onto the index set. -/
structure DisplayFamily (I : Type u) where
  Carrier : Type v
  proj : Carrier → I

namespace DisplayFamily

variable {I : Type u} {J : Type v} {K : Type*}

/-- The fibre of a display-indexed family over an index `i`. -/
def fiber (F : DisplayFamily I) (i : I) : Type v := {x : F.Carrier // F.proj x = i}

/-- Reindex a display-indexed family along a map of index sets. -/
def reindex (u : I → J) (F : DisplayFamily J) : DisplayFamily I where
  Carrier := Σ i : I, fiber F (u i)
  proj := fun p => p.1

/-- The fibre of a reindexed family over `i` is equivalent to the old fibre over `u i`. -/
def fiberReindexEquiv (u : I → J) (F : DisplayFamily J) (i : I) :
    fiber (reindex u F) i ≃ fiber F (u i) where
  toFun x := by
    cases x with
    | mk p hp =>
        cases p with
        | mk i' y =>
            cases hp
            exact y
  invFun y := ⟨⟨i, y⟩, rfl⟩
  left_inv := by
    intro x
    cases x with
    | mk x hx =>
        cases x with
        | mk i' y =>
            cases hx
            rfl
  right_inv := by
    intro y
    rfl

/-- Constant display-indexed family with fibre `X` over every index. -/
def const (I : Type u) (X : Type v) : DisplayFamily I where
  Carrier := I × X
  proj := Prod.fst

/-- The fibre of a constant family is equivalent to the constant carrier. -/
def fiberConstEquiv (I : Type u) (X : Type v) (i : I) :
    fiber (const I X) i ≃ X where
  toFun x := x.1.2
  invFun x := ⟨(i, x), rfl⟩
  left_inv := by
    intro x
    cases x with
    | mk x hx =>
        cases x with
        | mk i' x =>
            cases hx
            rfl
  right_inv := by
    intro x
    rfl

/-- Reindexing a constant family stays constant, up to a canonical equivalence on carriers. -/
def reindexConstEquiv (u : I → J) (X : Type K) :
    (reindex u (const J X)).Carrier ≃ (const I X).Carrier where
  toFun p := (p.1, p.2.1.2)
  invFun p := ⟨p.1, ⟨(u p.1, p.2), rfl⟩⟩
  left_inv := by
    intro p
    cases p with
    | mk i x =>
        cases x with
        | mk x hx =>
            cases x with
            | mk j x =>
                cases hx
                rfl
  right_inv := by
    intro p
    cases p
    rfl

/-- Positive example from the text: substituting a family along a point yields the fibre. -/
def fiberAtPointEquiv (F : DisplayFamily J) (j : J) :
    fiber (reindex (fun _ : PUnit => j) F) PUnit.unit ≃ fiber F j :=
  fiberReindexEquiv (fun _ : PUnit => j) F PUnit.unit

/-- Positive example from the text: reindexing along a projection adds a dummy variable. -/
def fiberOverProjectionEquiv (F : DisplayFamily J) (i : I) (j : J) :
    fiber (reindex (fun p : J × I => p.1) F) (j, i) ≃ fiber F j :=
  fiberReindexEquiv (fun p : J × I => p.1) F (j, i)

/-- Positive example from the text: reindexing along the diagonal restricts to equal indices. -/
def fiberOverDiagonalEquiv (F : DisplayFamily (J × J)) (j : J) :
    fiber (reindex (fun x : J => (x, x)) F) j ≃ fiber F (j, j) :=
  fiberReindexEquiv (fun x : J => (x, x)) F j

end DisplayFamily

end Mettapedia.AutoBooks.Codex.Jacobs.Chapter1
