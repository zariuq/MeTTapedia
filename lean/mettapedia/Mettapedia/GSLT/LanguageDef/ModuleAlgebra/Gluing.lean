import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Presentation
import Mettapedia.GSLT.Logic.RelativePushout
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# The universal property of a compatible declaration join

A join amalgamates the two declaration sets over their actual shared entries.
The square is a Mathlib `IsPushout` and an instance of the library's relative
pushout theory. Maps agreeing on the overlap have a unique extension. These
declaration-set laws are not conservativity theorems for models or rewriting.
Origin compatibility ensures that shared origins have identical representatives.
-/

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra

open CategoryTheory CategoryTheory.Limits

universe u

variable {Origin Label Body : Type u}
  [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body]

abbrev Member (p : Presentation Origin Label Body) := {entry // entry ∈ p.val}

def includeLeft {p q r : Presentation Origin Label Body} (joined : join p q = some r)
    (entry : Member p) : Member r :=
  ⟨entry.val, (join_eq_some_iff.mp joined) ▸ Finset.mem_union_left _ entry.property⟩

def includeRight {p q r : Presentation Origin Label Body} (joined : join p q = some r)
    (entry : Member q) : Member r :=
  ⟨entry.val, (join_eq_some_iff.mp joined) ▸ Finset.mem_union_right _ entry.property⟩

abbrev CommonMember (p q : Presentation Origin Label Body) :=
  {entry // entry ∈ p.val ∧ entry ∈ q.val}

def commonLeft (p q : Presentation Origin Label Body) (entry : CommonMember p q) : Member p :=
  ⟨entry.val, entry.property.1⟩

def commonRight (p q : Presentation Origin Label Body) (entry : CommonMember p q) : Member q :=
  ⟨entry.val, entry.property.2⟩

/-- The declared overlap is the pullback of the two actual inclusions. -/
theorem join_isPullback {p q r : Presentation Origin Label Body} (joined : join p q = some r) :
    IsPullback (↾(commonLeft p q)) (↾(commonRight p q))
      (↾(includeLeft joined)) (↾(includeRight joined)) := by
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext entry
    rfl
  · intro a b equal
    exact Subtype.ext (congrArg (fun entry : Member p => entry.val) equal.1)
  · intro a b equal
    have value : a.val = b.val := congrArg Subtype.val equal
    refine ⟨⟨a.val, a.property, value.symm ▸ b.property⟩, ?_, ?_⟩
    · rfl
    · exact Subtype.ext value

/-- The origin-sensitive join is an actual pushout in the existing category
of types. The general injective-pullback/joint-surjectivity theorem supplies
the universal property; it is not redefined here. -/
theorem join_isPushout {p q r : Presentation Origin Label Body} (joined : join p q = some r) :
    IsPushout (↾(commonLeft p q)) (↾(commonRight p q))
      (↾(includeLeft joined)) (↾(includeRight joined)) := by
  let : Mono (↾(includeLeft joined)) := (mono_iff_injective _).mpr
    (fun a b equal => Subtype.ext (congrArg (fun entry : Member r => entry.val) equal))
  apply Types.isPushout_of_isPullback_of_mono' (join_isPullback joined)
  · ext entry
    simp only [Set.sup_eq_union, Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    have member : entry.val ∈ p.val ∪ q.val :=
      (join_eq_some_iff.mp joined).symm ▸ entry.property
    rcases Finset.mem_union.mp member with hp | hq
    · exact Or.inl ⟨⟨entry.val, hp⟩, Subtype.ext rfl⟩
    · exact Or.inr ⟨⟨entry.val, hq⟩, Subtype.ext rfl⟩
  · intro a b _ _ equal
    exact Subtype.ext (congrArg (fun entry : Member r => entry.val) equal)

/-- The same square is usable by the established relative-pushout API. -/
theorem join_isIdemPushout {p q r : Presentation Origin Label Body} (joined : join p q = some r) :
    RelativePushout.IsIdemPushout (↾(commonLeft p q)) (↾(commonRight p q))
      (↾(includeLeft joined)) (↾(includeRight joined)) (join_isPushout joined).w :=
  RelativePushout.isIdemPushout_of_isPushout (join_isPushout joined)

/-- The mediator is constructed by a membership test, not postulated. -/
def glue {Target : Type u} {p q r : Presentation Origin Label Body}
    (joined : join p q = some r) (left : Member p → Target) (right : Member q → Target)
    (entry : Member r) : Target :=
  if h : entry.val ∈ p.val then left ⟨entry.val, h⟩
  else right ⟨entry.val, by
    have member : entry.val ∈ p.val ∪ q.val := (join_eq_some_iff.mp joined).symm ▸ entry.property
    exact (Finset.mem_union.mp member).resolve_left h⟩

theorem glue_left {Target : Type u} {p q r : Presentation Origin Label Body}
    (joined : join p q = some r) (left : Member p → Target) (right : Member q → Target)
    (entry : Member p) : glue joined left right (includeLeft joined entry) = left entry := by
  simp [glue, includeLeft, entry.property]

theorem glue_right {Target : Type u} {p q r : Presentation Origin Label Body}
    (joined : join p q = some r) (left : Member p → Target) (right : Member q → Target)
    (agree : ∀ entry hp hq, left ⟨entry, hp⟩ = right ⟨entry, hq⟩)
    (entry : Member q) : glue joined left right (includeRight joined entry) = right entry := by
  by_cases h : entry.val ∈ p.val
  · simpa [glue, includeRight, h] using agree entry.val h entry.property
  · simp [glue, includeRight, h]

theorem glue_unique {Target : Type u} {p q r : Presentation Origin Label Body}
    (joined : join p q = some r) (left : Member p → Target) (right : Member q → Target)
    (candidate : Member r → Target)
    (onLeft : ∀ entry, candidate (includeLeft joined entry) = left entry)
    (onRight : ∀ entry, candidate (includeRight joined entry) = right entry) :
    candidate = glue joined left right := by
  have agree : ∀ entry hp hq, left ⟨entry, hp⟩ = right ⟨entry, hq⟩ := by
    intro entry hp hq
    exact (onLeft ⟨entry, hp⟩).symm.trans (onRight ⟨entry, hq⟩)
  have equal : (↾candidate) = (↾(glue joined left right)) :=
    (join_isPushout joined).hom_ext (by
      ext entry
      exact (onLeft entry).trans (glue_left joined left right entry).symm) (by
      ext entry
      exact (onRight entry).trans (glue_right joined left right agree entry).symm)
  exact congrArg (fun map => map.hom.toFun) equal

/-- Existence and uniqueness of a map extending both branches. -/
theorem existsUnique_glue {Target : Type u} {p q r : Presentation Origin Label Body}
    (joined : join p q = some r) (left : Member p → Target) (right : Member q → Target)
    (agree : ∀ entry hp hq, left ⟨entry, hp⟩ = right ⟨entry, hq⟩) :
    ∃! mediator : Member r → Target,
      (∀ entry, mediator (includeLeft joined entry) = left entry) ∧
      (∀ entry, mediator (includeRight joined entry) = right entry) := by
  refine ⟨glue joined left right, ⟨glue_left joined left right,
    glue_right joined left right agree⟩, ?_⟩
  rintro candidate ⟨onLeft, onRight⟩
  exact glue_unique joined left right candidate onLeft onRight

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra
