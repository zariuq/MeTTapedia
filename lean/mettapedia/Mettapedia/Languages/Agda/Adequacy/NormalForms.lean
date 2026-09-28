import Mettapedia.Languages.Agda.Adequacy.Embedding
import Mettapedia.Languages.Agda.Structural.Reduction

/-!
# Embedded reference terms are structural normal forms

Every term, annotated type, and elimination spine of the independent reference
embeds into a term with no structural reduction occurrence. This theorem is
relative to the application-only root rules, with opaque definitions. It does
not assert normalization, confluence, or completeness of the structural system.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Adequacy

open Mettapedia.OSLF.Binding
open Structural (sig scope)

/-- Absence of all compatible root occurrences, at every structural position. -/
def Normal {Γ : Ctx sig} {s : Structural.Srt} (term : Term sig Γ s) : Prop :=
  ∀ target, IsEmpty (Structural.Step term target)

private def NormalArgs {Γ : Ctx sig} {arity : List (List Structural.Srt × Structural.Srt)}
    (args : Args sig arity Γ) : Prop :=
  ∀ target, IsEmpty (Structural.ArgsStep args target)

private theorem normalArgs_nil {Γ : Ctx sig} : NormalArgs (Args.nil (Γ := Γ)) := by
  intro target
  constructor
  intro h
  cases h

private theorem normalArgs_cons {Γ : Ctx sig} {bs : Ctx sig}
    {s : sig.Srt} {rest : List (Ctx sig × sig.Srt)}
    {head : Term sig (bs ++ Γ) s} {tail : Args sig rest Γ}
    (hh : Normal head) (ht : NormalArgs tail) : NormalArgs (.cons head tail) := by
  intro target
  constructor
  intro h
  cases h with
  | head _ step => exact (hh _).false step
  | tail _ step => exact (ht _).false step

private theorem normal_op {Γ : Ctx sig} {s : Structural.Srt} {op : Structural.Op s}
    {args : Args sig (sig.arity op) Γ}
    (hr : ∀ target, IsEmpty (Structural.Root (.op op args) target))
    (ha : NormalArgs args) : Normal (.op op args) := by
  intro target
  constructor
  intro h
  cases h with
  | root root => exact (hr _).false root
  | congr _ args => exact (ha _).false args

private theorem normal_levelClosed {Γ : Ctx sig} (l : Nat) :
    Normal (Structural.levelClosed (Γ := Γ) l) := by
  apply normal_op
  · intro target; exact ⟨fun h => by cases h⟩
  · exact normalArgs_nil

private theorem normal_set {Γ : Ctx sig} (l : Nat) :
    Normal (Structural.set (Structural.levelClosed (Γ := Γ) l)) := by
  apply normal_op
  · intro target; exact ⟨fun h => by cases h⟩
  · exact normalArgs_cons (normal_levelClosed l) normalArgs_nil

private theorem normal_defined {Γ : Ctx sig} (f : String) :
    Normal (Structural.defined (Γ := Γ) f) := by
  apply normal_op
  · intro target; exact ⟨fun h => by cases h⟩
  · exact normalArgs_nil

private theorem normal_constructor {Γ : Ctx sig} (c : String) :
    Normal (Structural.constructor (Γ := Γ) c) := by
  apply normal_op
  · intro target; exact ⟨fun h => by cases h⟩
  · exact normalArgs_nil

private theorem normal_apply {Γ : Ctx sig} {t : Structural.Tm Γ}
    (ht : Normal t) : Normal (Structural.apply t) := by
  apply normal_op
  · intro target; exact ⟨fun h => by cases h⟩
  · exact normalArgs_cons ht normalArgs_nil

mutual
  /-- Source heads carry nonempty spines only when the head is neutral. -/
  theorem embedTerm_normal {n : Nat} (term : Specification.Term n) : Normal (embedTerm term) := by
    match term with
    | .var i .nil => exact Structural.variable_inert (embedVar i)
    | .var i (.cons (.apply argument) es) =>
      apply normal_op
      · intro target; exact ⟨fun h => by cases h⟩
      · exact normalArgs_cons (Structural.variable_inert (embedVar i))
          (normalArgs_cons (embedSpine_normal (.cons (.apply argument) es)) normalArgs_nil)
    | .defn f .nil => exact normal_defined f
    | .defn f (.cons (.apply argument) es) =>
      apply normal_op
      · intro target; exact ⟨fun h => by cases h⟩
      · exact normalArgs_cons (normal_defined f)
          (normalArgs_cons (embedSpine_normal (.cons (.apply argument) es)) normalArgs_nil)
    | .con c .nil => exact normal_constructor c
    | .con c (.cons (.apply argument) es) =>
      apply normal_op
      · intro target; exact ⟨fun h => by cases h⟩
      · exact normalArgs_cons (normal_constructor c)
          (normalArgs_cons (embedSpine_normal (.cons (.apply argument) es)) normalArgs_nil)
    | .lam (.bind body) =>
      apply normal_op
      · intro target; exact ⟨fun h => by cases h⟩
      · exact normalArgs_cons (embedTerm_normal body) normalArgs_nil
    | .lam (.noBind body) =>
      apply normal_op
      · intro target; exact ⟨fun h => by cases h⟩
      · exact normalArgs_cons (embedTerm_normal body) normalArgs_nil
    | .pi domain (.bind body) =>
      apply normal_op
      · intro target; exact ⟨fun h => by cases h⟩
      · exact normalArgs_cons (embedTy_normal domain)
          (normalArgs_cons (embedTy_normal body) normalArgs_nil)
    | .pi domain (.noBind body) =>
      apply normal_op
      · intro target; exact ⟨fun h => by cases h⟩
      · exact normalArgs_cons (embedTy_normal domain)
          (normalArgs_cons (embedTy_normal body) normalArgs_nil)
    | .sort l =>
      apply normal_op
      · intro target; exact ⟨fun h => by cases h⟩
      · exact normalArgs_cons (normal_set l) normalArgs_nil
    | .level l =>
      apply normal_op
      · intro target; exact ⟨fun h => by cases h⟩
      · exact normalArgs_cons (normal_levelClosed l) normalArgs_nil

  /-- Both a type's sort annotation and its term have no reduction occurrence. -/
  theorem embedTy_normal {n : Nat} (ty : Specification.Ty n) : Normal (embedTy ty) := by
    match ty with
    | .el l term =>
      apply normal_op
      · intro target; exact ⟨fun h => by cases h⟩
      · exact normalArgs_cons (normal_set l)
          (normalArgs_cons (embedTerm_normal term) normalArgs_nil)

  /-- Every argument in an embedded spine is a normal reference term. -/
  theorem embedSpine_normal {n : Nat} (spine : Specification.Spine n) :
      Normal (embedSpine spine) := by
    match spine with
    | .nil =>
      apply normal_op
      · intro target; exact ⟨fun h => by cases h⟩
      · exact normalArgs_nil
    | .cons (.apply term) rest =>
      apply normal_op
      · intro target; exact ⟨fun h => by cases h⟩
      · exact normalArgs_cons (normal_apply (embedTerm_normal term))
          (normalArgs_cons (embedSpine_normal rest) normalArgs_nil)
end

#print axioms embedTerm_normal
#print axioms embedTy_normal
#print axioms embedSpine_normal

end Mettapedia.Languages.Agda.Adequacy
