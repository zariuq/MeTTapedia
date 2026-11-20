import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Simple
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Transport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Declaration

/-!
# Simple inductive types as declared families

A simple inductive type `T` in a universe `u` is the declared family `simpleDecl T u ctors`
with no parameters and no indices: a closed field is a value field of that type, a recursive
field is a recursive occurrence at no indices, and every target is empty. Read at no
parameters, with packs for the instantiated field types that are the packs of the closed
field types, the declaration and the simple reading carry over to each other
(`simpleDecl_carries`, `simple_carries_decl`). So the family pack at the declaration has
the reducible terms, the reducible equalities and, when the field packs are reflexive on
their types, the reducibly equal types of `indPack` (`simpleDecl_redTm`, `simpleDecl_eqTm`,
`simpleDecl_eqTy`), and is equal to it (`simpleDecl_pack_eq`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace Families

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## The declaration -/

/-- The fields of a constructor of a simple inductive type as a constructor telescope with
no parameters, after `j` earlier fields. -/
def fieldsTele : List (Field Head) → (j : Nat) → CtorTele Head 0 j
  | [], _ => .target []
  | .recursive :: rest, j => .recursive [] (fieldsTele rest (j + 1))
  | .closed F :: rest, j => .value F (fieldsTele rest (j + 1))

/-- A simple inductive type as a declared family with no parameters and no indices. -/
def simpleDecl (T : DeclName) (u : Head) (ctors : List (DeclName × List (Field Head))) :
    FamilyDecl Head where
  name := T
  params := 0
  paramEntry _ := .head u
  indexTypes := []
  sort := u
  ctors := ctors.map fun entry => (entry.1, fieldsTele entry.2 0)

theorem fieldsTele_valueTypes {F : Tm Head 0} :
    ∀ (fields : List (Field Head)) (j : Nat), F ∈ (fieldsTele fields j).valueTypes →
      Field.closed F ∈ fields
  | [], _, h => nomatch h
  | .recursive :: rest, j, h =>
      List.mem_cons_of_mem _ (fieldsTele_valueTypes rest (j + 1) h)
  | .closed F' :: rest, j, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (fieldsTele_valueTypes rest (j + 1) h)

/-! ## The declaration and the simple reading carry over to each other -/

section Carries

variable {n : Nat} {Γ : Ctx Head n} {T : DeclName} {u : Head}
  {ctors : List (DeclName × List (Field Head))} {typePack : Tm Head n → Pack Head n}
  {fieldPack : Tm Head 0 → Pack Head n}

theorem fieldsTele_target :
    ∀ (fields : List (Field Head)) (j : Nat),
      (fieldsTele fields j).targetAt ([] : List (Tm Head n)) = fun _ => []
  | [], _ => rfl
  | .recursive :: rest, j => fieldsTele_target rest (j + 1)
  | .closed _ :: rest, j => fieldsTele_target rest (j + 1)

variable (hPack : ∀ F : Tm Head 0, typePack (inst [] F) = fieldPack F)
include hPack

theorem fieldsTele_carries :
    ∀ (fields : List (Field Head)) (j : Nat),
      List.Forall₂ FieldAt.Carries ((fieldsTele fields j).fieldsAt typePack [])
        (fields.map (simpleField fieldPack))
  | [], _ => .nil
  | .recursive :: rest, j => .cons (.recursive _) (fieldsTele_carries rest (j + 1))
  | .closed F :: rest, j =>
      .cons (.value (fun h => hPack F ▸ h) (fun h => hPack F ▸ h))
        (fieldsTele_carries rest (j + 1))

theorem fieldsTele_carried :
    ∀ (fields : List (Field Head)) (j : Nat),
      List.Forall₂ FieldAt.Carries (fields.map (simpleField fieldPack))
        ((fieldsTele fields j).fieldsAt typePack [])
  | [], _ => .nil
  | .recursive :: rest, j => .cons (.recursive _) (fieldsTele_carried rest (j + 1))
  | .closed F :: rest, j =>
      .cons (.value (fun h => (hPack F).symm ▸ h) (fun h => (hPack F).symm ▸ h))
        (fieldsTele_carried rest (j + 1))

theorem ctors_carries :
    ∀ (sub : List (DeclName × List (Field Head))),
      List.Forall₂ CtorAt.Carries
        ((sub.map fun entry => (entry.1, fieldsTele entry.2 0)).map
          ((simpleDecl T u ctors).ctorAt S Γ typePack []))
        (sub.map (simpleCtor fieldPack))
  | [] => .nil
  | entry :: rest => by
      refine .cons ⟨?_, fieldsTele_carries hPack entry.2 0, fieldsTele_target entry.2 0⟩
        (ctors_carries rest)
      rintro nf fs ⟨ps', rfl, len, _⟩
      have hps : ps' = [] := List.length_eq_zero_iff.mp len
      subst hps
      rfl

theorem ctors_carried :
    ∀ (sub : List (DeclName × List (Field Head))),
      List.Forall₂ CtorAt.Carries (sub.map (simpleCtor fieldPack))
        ((sub.map fun entry => (entry.1, fieldsTele entry.2 0)).map
          ((simpleDecl T u ctors).ctorAt S Γ typePack []))
  | [] => .nil
  | entry :: rest => by
      refine .cons ⟨?_, fieldsTele_carried hPack entry.2 0, (fieldsTele_target entry.2 0).symm⟩
        (ctors_carried rest)
      rintro nf fs rfl
      exact ⟨[], rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- The declaration read at no parameters carries over to the simple reading. -/
theorem simpleDecl_carries :
    ((simpleDecl T u ctors).view S Γ typePack []).Carries S Γ (simpleFamily T ctors fieldPack) where
  type _ := .inl rfl
  ctors := ctors_carries hPack ctors
  indexPacks := .nil

/-- The simple reading carries over to the declaration read at no parameters. -/
theorem simple_carries_decl :
    (simpleFamily T ctors fieldPack).Carries S Γ ((simpleDecl T u ctors).view S Γ typePack []) where
  type _ := .inl rfl
  ctors := ctors_carried hPack ctors
  indexPacks := .nil

end Carries

/-! ## The same packs -/

section Same

variable {n : Nat} {Γ : Ctx Head n} {T : DeclName} {u : Head}
  {ctors : List (DeclName × List (Field Head))} {typePack : Tm Head n → Pack Head n}
  {fieldPack : Tm Head 0 → Pack Head n}

theorem simpleDecl_redTm (laws : S.E.Laws S.R S.roles)
    (hPack : ∀ F : Tm Head 0, typePack (inst [] F) = fieldPack F) {t : Tm Head n} :
    (familyPack S Γ ((simpleDecl T u ctors).view S Γ typePack []) []).redTm t ↔
      (indPack S Γ T ctors fieldPack).redTm t :=
  ⟨fun h => simple_redTm.mp (FamRedTm.transport laws (simpleDecl_carries hPack) h),
    fun h => FamRedTm.transport laws (simple_carries_decl hPack) (simple_redTm.mpr h)⟩

theorem simpleDecl_eqTm (laws : S.E.Laws S.R S.roles)
    (hPack : ∀ F : Tm Head 0, typePack (inst [] F) = fieldPack F) {t t' : Tm Head n} :
    (familyPack S Γ ((simpleDecl T u ctors).view S Γ typePack []) []).eqTm t t' ↔
      (indPack S Γ T ctors fieldPack).eqTm t t' :=
  ⟨fun h => simple_eqTm.mp (FamEqTm.transport laws (simpleDecl_carries hPack) h),
    fun h => FamEqTm.transport laws (simple_carries_decl hPack) (simple_eqTm.mpr h)⟩

/-- The two packs have the same reducibly equal types, when the type constant is
convertible to itself and the packs of the closed field types are reflexive on them. -/
theorem simpleDecl_eqTy (hPack : ∀ F : Tm Head 0, typePack (inst [] F) = fieldPack F)
    (constRefl : S.E.convTy Γ (.const T) (.const T))
    (fieldRefl : ∀ {F : Tm Head 0}, IsClosedField ctors F → (fieldPack F).eqTy (inst [] F))
    {B : Tm Head n} :
    (familyPack S Γ ((simpleDecl T u ctors).view S Γ typePack []) []).eqTy B ↔
      (indPack S Γ T ctors fieldPack).eqTy B := by
  constructor
  · rintro ⟨X, is', red, ⟨ps₂, rfl, len, conv, _⟩, _, _⟩
    have hps : ps₂ = [] := List.length_eq_zero_iff.mp conv.1
    have his : is' = [] := List.length_eq_zero_iff.mp len
    subst hps his
    exact red
  · intro red
    refine ⟨.const T, [], red, ⟨[], rfl, rfl, ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      ?_, fun _ h => nomatch h⟩, constRefl, .nil⟩
    intro entry mem F memF
    obtain ⟨⟨k, fields⟩, entryMem, rfl⟩ := List.mem_map.mp mem
    exact (hPack F).symm ▸ fieldRefl ⟨k, fields, entryMem, fieldsTele_valueTypes fields 0 memF⟩

/-- **The pack of a simple inductive type is the family pack at its declaration**, under the
premises of the inductive case of the relation and packs of the instantiated field types
that are the packs of the closed field types, reflexive on them. -/
theorem simpleDecl_pack_eq (laws : S.E.Laws S.R S.roles) {v : Head}
    (role : S.roles T = .inductive ctors) (typing : Typed S.R Γ (.const T) (.head v))
    (isUniverse : S.R.isUniverse v)
    (hPack : ∀ F : Tm Head 0, typePack (inst [] F) = fieldPack F)
    (fieldRefl : ∀ {F : Tm Head 0}, IsClosedField ctors F → (fieldPack F).eqTy (inst [] F)) :
    familyPack S Γ ((simpleDecl T u ctors).view S Γ typePack []) [] =
      indPack S Γ T ctors fieldPack :=
  PackEquiv.eq ⟨simpleDecl_eqTy hPack (const_convTy_refl laws role typing isUniverse) fieldRefl,
    simpleDecl_redTm laws hPack, simpleDecl_eqTm laws hPack⟩

end Same

end Families
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
