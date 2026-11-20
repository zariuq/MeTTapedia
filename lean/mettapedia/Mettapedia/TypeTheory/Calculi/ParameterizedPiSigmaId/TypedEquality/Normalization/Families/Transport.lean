import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Laws

/-!
# Inductive families: transport between readings

Irrelevance compares the packs of two reducibly equal types. For families these are two
readings of one declaration, possibly at different parameters: the same constructors in the
same order, whose forms, value-field packs and index packs carry over, with the same target
and recursive index functions, and whose types at equal indices are equal. Then reducible
terms and reducible equalities carry over at the same indices (`FamRedTm.transport`,
`FamEqTm.transport`), and, with `FamRedTm.transfer`, to reducibly equal indices.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace Families

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

section Transport

variable {n : Nat}

/-- A field of one reading that carries over to a field of another. -/
inductive FieldAt.Carries : FieldAt Head n → FieldAt Head n → Prop where
  | value {P P' : Pack Head n} (redTm : ∀ {a : Tm Head n}, P.redTm a → P'.redTm a)
      (eqTm : ∀ {a b : Tm Head n}, P.eqTm a b → P'.eqTm a b) :
      FieldAt.Carries (.value P) (.value P')
  | recursive (idx : List (Tm Head n) → List (Tm Head n)) :
      FieldAt.Carries (.recursive idx) (.recursive idx)

/-- A constructor of one reading that carries over to a constructor of another. -/
structure CtorAt.Carries (c c' : CtorAt Head n) : Prop where
  form : ∀ {nf : Tm Head n} {fs : List (Tm Head n)}, c.form nf fs → c'.form nf fs
  fields : List.Forall₂ FieldAt.Carries c.fields c'.fields
  target : c.target = c'.target

/-- Two types that are the same term, or equal at a universe. -/
def SameOrEq (S : Setting Head L) (Γ : Ctx Head n) (A B : Tm Head n) : Prop :=
  A = B ∨ TypeEq S.R Γ A B

theorem SameOrEq.redTm {Γ : Ctx Head n} {A B t u : Tm Head n} (same : SameOrEq S Γ A B)
    (red : RedTm S.R S.roles Γ t u A) : RedTm S.R S.roles Γ t u B := by
  rcases same with rfl | equal
  · exact red
  · exact red.conv equal

theorem SameOrEq.convTm (laws : S.E.Laws S.R S.roles) {Γ : Ctx Head n} {A B t u : Tm Head n}
    (same : SameOrEq S Γ A B) (conv : S.E.convTm Γ t u A) : S.E.convTm Γ t u B := by
  rcases same with rfl | equal
  · exact conv
  · exact laws.convTm_conv conv equal

theorem SameOrEq.convNe (laws : S.E.Laws S.R S.roles) {Γ : Ctx Head n} {A B t u : Tm Head n}
    (same : SameOrEq S Γ A B) (conv : S.E.convNe Γ t u A) : S.E.convNe Γ t u B := by
  rcases same with rfl | equal
  · exact conv
  · exact laws.convNe_conv conv equal

/-- A reading of a family that carries over to another reading in the same context: at
every list of indices the two types are the same term or equal types. -/
structure FamilyAt.Carries (S : Setting Head L) (Γ : Ctx Head n) (F F' : FamilyAt Head n) :
    Prop where
  type : ∀ is : List (Tm Head n), SameOrEq S Γ (F.type is) (F'.type is)
  ctors : List.Forall₂ CtorAt.Carries F.ctors F'.ctors
  indexPacks : List.Forall₂ (fun (P P' : Pack Head n) => ∀ {a b : Tm Head n},
    P.eqTm a b → P'.eqTm a b) F.indexPacks F'.indexPacks

theorem IndexAgree.carry :
    ∀ {Ps Ps' : List (Pack Head n)},
      List.Forall₂ (fun (P P' : Pack Head n) => ∀ {a b : Tm Head n}, P.eqTm a b → P'.eqTm a b)
        Ps Ps' →
      ∀ {is js : List (Tm Head n)}, IndexAgree Ps is js → IndexAgree Ps' is js := by
  intro Ps Ps' rel is js agree
  induction agree generalizing Ps' with
  | nil => cases rel; exact .nil
  | cons head _ ih =>
      cases rel with
      | cons r rest => exact .cons (r head) (ih rest)

variable {Γ : Ctx Head n} {F F' : FamilyAt Head n}

mutual

theorem FamRedTm.transport (laws : S.E.Laws S.R S.roles) (carries : F.Carries S Γ F') :
    ∀ {is : List (Tm Head n)} {t : Tm Head n}, FamRedTm S Γ F is t → FamRedTm S Γ F' is t
  | is, _, .mk red conv normal =>
      .mk ((carries.type is).redTm red) ((carries.type is).convTm laws conv)
        (FamNf.transport laws carries normal)

theorem FamNf.transport (laws : S.E.Laws S.R S.roles) (carries : F.Carries S Γ F') :
    ∀ {is : List (Tm Head n)} {nf : Tm Head n}, FamNf S Γ F is nf → FamNf S Γ F' is nf
  | _, _, .ctor (fs := fs) mem form fields agree => by
      obtain ⟨c', mem', rc⟩ := forall₂_exists_of_mem carries.ctors mem
      have agree' := IndexAgree.carry carries.indexPacks agree
      rw [rc.target] at agree'
      exact .ctor mem' (rc.form form) (FamFields.transport laws carries rc.fields fields) agree'
  | is, _, .neutral nNf conv => .neutral nNf ((carries.type is).convNe laws conv)

theorem FamFields.transport (laws : S.E.Laws S.R S.roles) (carries : F.Carries S Γ F') :
    ∀ {all : List (Tm Head n)} {fields fields' : List (FieldAt Head n)}
      {args : List (Tm Head n)}, List.Forall₂ FieldAt.Carries fields fields' →
      FamFields S Γ F all fields args → FamFields S Γ F' all fields' args
  | _, _, _, _, rel, .nil => by cases rel; exact .nil
  | _, _, _, _, rel, .value head tail => by
      cases rel with
      | cons r rest =>
          cases r with
          | value redTm _ => exact .value (redTm head) (FamFields.transport laws carries rest tail)
  | _, _, _, _, rel, .recursive head tail => by
      cases rel with
      | cons r rest =>
          cases r with
          | recursive _ =>
              exact .recursive (FamRedTm.transport laws carries head)
                (FamFields.transport laws carries rest tail)

end

mutual

theorem FamEqTm.transport (laws : S.E.Laws S.R S.roles) (carries : F.Carries S Γ F') :
    ∀ {is : List (Tm Head n)} {t t' : Tm Head n}, FamEqTm S Γ F is t t' →
      FamEqTm S Γ F' is t t'
  | is, _, _, .mk red red' conv normal =>
      .mk ((carries.type is).redTm red) ((carries.type is).redTm red')
        ((carries.type is).convTm laws conv) (FamEqNf.transport laws carries normal)

theorem FamEqNf.transport (laws : S.E.Laws S.R S.roles) (carries : F.Carries S Γ F') :
    ∀ {is : List (Tm Head n)} {nf nf' : Tm Head n}, FamEqNf S Γ F is nf nf' →
      FamEqNf S Γ F' is nf nf'
  | _, _, _, .ctor (fs := fs) (fs' := fs') mem form form' fields agree agree' => by
      obtain ⟨c', mem', rc⟩ := forall₂_exists_of_mem carries.ctors mem
      have a := IndexAgree.carry carries.indexPacks agree
      have a' := IndexAgree.carry carries.indexPacks agree'
      rw [rc.target] at a a'
      exact .ctor mem' (rc.form form) (rc.form form')
        (FamEqFields.transport laws carries rc.fields fields) a a'
  | is, _, _, .neutral nNf nNf' conv => .neutral nNf nNf' ((carries.type is).convNe laws conv)

theorem FamEqFields.transport (laws : S.E.Laws S.R S.roles) (carries : F.Carries S Γ F') :
    ∀ {all : List (Tm Head n)} {fields fields' : List (FieldAt Head n)}
      {args args' : List (Tm Head n)}, List.Forall₂ FieldAt.Carries fields fields' →
      FamEqFields S Γ F all fields args args' → FamEqFields S Γ F' all fields' args args'
  | _, _, _, _, _, rel, .nil => by cases rel; exact .nil
  | _, _, _, _, _, rel, .value head tail => by
      cases rel with
      | cons r rest =>
          cases r with
          | value _ eqTm => exact .value (eqTm head) (FamEqFields.transport laws carries rest tail)
  | _, _, _, _, _, rel, .recursive head tail => by
      cases rel with
      | cons r rest =>
          cases r with
          | recursive _ =>
              exact .recursive (FamEqTm.transport laws carries head)
                (FamEqFields.transport laws carries rest tail)

end

/-- **Transport of the family pack** to another reading at reducibly equal indices: what the
irrelevance case of the relation asks of a family. -/
theorem familyPack_forward (laws : S.E.Laws S.R S.roles) (carries : F.Carries S Γ F')
    (per' : IndexPER F') (congr' : TypeCongr S Γ F') {is is' : List (Tm Head n)}
    (agree : IndexAgree F'.indexPacks is is') :
    (∀ {t : Tm Head n}, (familyPack S Γ F is).redTm t → (familyPack S Γ F' is').redTm t) ∧
      (∀ {t t' : Tm Head n}, (familyPack S Γ F is).eqTm t t' →
        (familyPack S Γ F' is').eqTm t t') :=
  ⟨fun h => FamRedTm.transfer laws per' congr' agree (FamRedTm.transport laws carries h),
    fun h => FamEqTm.transfer laws per' congr' agree (FamEqTm.transport laws carries h)⟩

end Transport

end Families
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
