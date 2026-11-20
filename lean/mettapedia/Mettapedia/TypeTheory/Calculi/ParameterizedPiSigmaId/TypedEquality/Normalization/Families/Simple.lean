import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Laws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Irrelevance

/-!
# Simple inductive types are families

A simple inductive type `T` is the family with no parameters and no indices whose
constructors are those of `T`: a closed field is a value field at the pack of its type, a
recursive field is a recursive occurrence at no indices, and every constructor targets no
indices. Its canonical forms are the constructor spines.

The family pack at this reading and the pack `indPack` of simple inductive types are
defined separately; they have the same reducible terms and the same reducible equalities
(`simple_redTm`, `simple_eqTm`), and the same reducibly equal types when the type constant
is convertible to itself (`simple_eqTy`). The hypotheses the laws of the family pack ask
for hold at this reading (`simpleFamily_rigid` and the others), so the laws of the family
pack specialise to simple inductive types.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace Families

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## The reading -/

section Reading

variable {n : Nat}

/-- A field of a simple inductive type read as a family field. -/
def simpleField (fieldPack : Tm Head 0 → Pack Head n) : Field Head → FieldAt Head n
  | .recursive => .recursive fun _ => []
  | .closed F => .value (fieldPack F)

/-- A constructor of a simple inductive type read as a family constructor: its canonical
forms are its spines, and it targets no indices. -/
def simpleCtor (fieldPack : Tm Head 0 → Pack Head n) (entry : DeclName × List (Field Head)) :
    CtorAt Head n where
  form nf fs := nf = appSpine (.const entry.1) fs
  fields := entry.2.map (simpleField fieldPack)
  target _ := []

/-- A simple inductive type read as a family with no parameters and no indices: its type at
the indices `is` is the spine `T is`, which is `T` itself at the only indices it has, none. -/
def simpleFamily (T : DeclName) (ctors : List (DeclName × List (Field Head)))
    (fieldPack : Tm Head 0 → Pack Head n) : FamilyAt Head n where
  type is := appSpine (.const T) is
  ctors := ctors.map (simpleCtor fieldPack)
  indexPacks := []
  sameFormer X is := X = .const T ∧ is = []

end Reading

/-! ## The same reducible terms -/

section Terms

variable {n : Nat} {Γ : Ctx Head n} {T : DeclName} {ctors : List (DeclName × List (Field Head))}
  {fieldPack : Tm Head 0 → Pack Head n}

mutual

theorem FamRedTm.toSimple :
    ∀ {is : List (Tm Head n)} {t : Tm Head n}, is = [] →
      FamRedTm S Γ (simpleFamily T ctors fieldPack) is t → IndRedTm S Γ T ctors fieldPack t
  | _, _, h, .mk red conv normal =>
      .mk (by rw [h] at red; exact red) (by rw [h] at conv; exact conv) (FamNf.toSimple h normal)

theorem FamNf.toSimple :
    ∀ {is : List (Tm Head n)} {nf : Tm Head n}, is = [] →
      FamNf S Γ (simpleFamily T ctors fieldPack) is nf → IndNf S Γ T ctors fieldPack nf
  | _, nf, _, .ctor (c := c) (fs := fs) mem form fields _ => by
      obtain ⟨⟨k, kfields⟩, entryMem, hc⟩ := List.mem_map.mp mem
      have hform : nf = appSpine (.const k) fs := by rw [← hc] at form; exact form
      have hfields : c.fields = kfields.map (simpleField fieldPack) := by rw [← hc]; rfl
      rw [hform]
      exact .ctor entryMem (FamFields.toSimple hfields fields)
  | _, _, h, .neutral nNf conv => .neutral nNf (by rw [h] at conv; exact conv)

theorem FamFields.toSimple :
    ∀ {all : List (Tm Head n)} {flds : List (FieldAt Head n)} {fields : List (Field Head)}
      {args : List (Tm Head n)}, flds = fields.map (simpleField fieldPack) →
      FamFields S Γ (simpleFamily T ctors fieldPack) all flds args →
      IndFields S Γ T ctors fieldPack fields args
  | _, _, [], _, _, .nil => .nil
  | _, _, _ :: _, _, h, .nil => nomatch h
  | _, _, [], _, h, .value _ _ => nomatch h
  | _, _, .closed F :: fields, _, h, .value head tail =>
      .closed (FieldAt.value.inj (List.cons.inj h).1 ▸ head)
        (FamFields.toSimple (List.cons.inj h).2 tail)
  | _, _, .recursive :: _, _, h, .value _ _ => by
      obtain ⟨hf, _⟩ := List.cons.inj h
      cases hf
  | _, _, [], _, h, .recursive _ _ => nomatch h
  | all, _, .recursive :: fields, _, h, .recursive head tail =>
      .recursive (FamRedTm.toSimple (congrFun (FieldAt.recursive.inj (List.cons.inj h).1) all) head)
        (FamFields.toSimple (List.cons.inj h).2 tail)
  | _, _, .closed _ :: _, _, h, .recursive _ _ => by
      obtain ⟨hf, _⟩ := List.cons.inj h
      cases hf

end

mutual

theorem IndRedTm.toFamily :
    ∀ {t : Tm Head n}, IndRedTm S Γ T ctors fieldPack t →
      FamRedTm S Γ (simpleFamily T ctors fieldPack) [] t
  | _, .mk red conv normal => .mk red conv (IndNf.toFamily normal)

theorem IndNf.toFamily :
    ∀ {nf : Tm Head n}, IndNf S Γ T ctors fieldPack nf →
      FamNf S Γ (simpleFamily T ctors fieldPack) [] nf
  | _, .ctor mem arguments =>
      .ctor (List.mem_map_of_mem mem) rfl (IndFields.toFamily arguments) .nil
  | _, .neutral nNf conv => .neutral nNf conv

theorem IndFields.toFamily :
    ∀ {all : List (Tm Head n)} {fields : List (Field Head)} {args : List (Tm Head n)},
      IndFields S Γ T ctors fieldPack fields args →
      FamFields S Γ (simpleFamily T ctors fieldPack) all (fields.map (simpleField fieldPack)) args
  | _, _, _, .nil => .nil
  | _, _, _, .recursive head tail => .recursive (IndRedTm.toFamily head) (IndFields.toFamily tail)
  | _, _, _, .closed head tail => .value head (IndFields.toFamily tail)

end

/-- The family pack at a simple inductive type has the reducible terms of `indPack`. -/
theorem simple_redTm {t : Tm Head n} :
    (familyPack S Γ (simpleFamily T ctors fieldPack) []).redTm t ↔
      (indPack S Γ T ctors fieldPack).redTm t :=
  ⟨FamRedTm.toSimple rfl, IndRedTm.toFamily⟩

end Terms

/-! ## The same reducible equalities -/

section Equalities

variable {n : Nat} {Γ : Ctx Head n} {T : DeclName} {ctors : List (DeclName × List (Field Head))}
  {fieldPack : Tm Head 0 → Pack Head n}

mutual

theorem FamEqTm.toSimple :
    ∀ {is : List (Tm Head n)} {t t' : Tm Head n}, is = [] →
      FamEqTm S Γ (simpleFamily T ctors fieldPack) is t t' → IndEqTm S Γ T ctors fieldPack t t'
  | _, _, _, h, .mk red red' conv normal =>
      .mk (by rw [h] at red; exact red) (by rw [h] at red'; exact red')
        (by rw [h] at conv; exact conv) (FamEqNf.toSimple h normal)

theorem FamEqNf.toSimple :
    ∀ {is : List (Tm Head n)} {nf nf' : Tm Head n}, is = [] →
      FamEqNf S Γ (simpleFamily T ctors fieldPack) is nf nf' →
      IndEqNf S Γ T ctors fieldPack nf nf'
  | _, nf, nf', _, .ctor (c := c) (fs := fs) (fs' := fs') mem form form' fields _ _ => by
      obtain ⟨⟨k, kfields⟩, entryMem, hc⟩ := List.mem_map.mp mem
      have hform : nf = appSpine (.const k) fs := by rw [← hc] at form; exact form
      have hform' : nf' = appSpine (.const k) fs' := by rw [← hc] at form'; exact form'
      have hfields : c.fields = kfields.map (simpleField fieldPack) := by rw [← hc]; rfl
      rw [hform, hform']
      exact .ctor entryMem (FamEqFields.toSimple hfields fields)
  | _, _, _, h, .neutral nNf nNf' conv => .neutral nNf nNf' (by rw [h] at conv; exact conv)

theorem FamEqFields.toSimple :
    ∀ {all : List (Tm Head n)} {flds : List (FieldAt Head n)} {fields : List (Field Head)}
      {args args' : List (Tm Head n)}, flds = fields.map (simpleField fieldPack) →
      FamEqFields S Γ (simpleFamily T ctors fieldPack) all flds args args' →
      IndEqFields S Γ T ctors fieldPack fields args args'
  | _, _, [], _, _, _, .nil => .nil
  | _, _, _ :: _, _, _, h, .nil => nomatch h
  | _, _, [], _, _, h, .value _ _ => nomatch h
  | _, _, .closed F :: fields, _, _, h, .value head tail =>
      .closed (FieldAt.value.inj (List.cons.inj h).1 ▸ head)
        (FamEqFields.toSimple (List.cons.inj h).2 tail)
  | _, _, .recursive :: _, _, _, h, .value _ _ => by
      obtain ⟨hf, _⟩ := List.cons.inj h
      cases hf
  | _, _, [], _, _, h, .recursive _ _ => nomatch h
  | all, _, .recursive :: fields, _, _, h, .recursive head tail =>
      .recursive (FamEqTm.toSimple (congrFun (FieldAt.recursive.inj (List.cons.inj h).1) all) head)
        (FamEqFields.toSimple (List.cons.inj h).2 tail)
  | _, _, .closed _ :: _, _, _, h, .recursive _ _ => by
      obtain ⟨hf, _⟩ := List.cons.inj h
      cases hf

end

mutual

theorem IndEqTm.toFamily :
    ∀ {t t' : Tm Head n}, IndEqTm S Γ T ctors fieldPack t t' →
      FamEqTm S Γ (simpleFamily T ctors fieldPack) [] t t'
  | _, _, .mk red red' conv normal => .mk red red' conv (IndEqNf.toFamily normal)

theorem IndEqNf.toFamily :
    ∀ {nf nf' : Tm Head n}, IndEqNf S Γ T ctors fieldPack nf nf' →
      FamEqNf S Γ (simpleFamily T ctors fieldPack) [] nf nf'
  | _, _, .ctor mem arguments =>
      .ctor (List.mem_map_of_mem mem) rfl rfl (IndEqFields.toFamily arguments) .nil .nil
  | _, _, .neutral nNf nNf' conv => .neutral nNf nNf' conv

theorem IndEqFields.toFamily :
    ∀ {all : List (Tm Head n)} {fields : List (Field Head)} {args args' : List (Tm Head n)},
      IndEqFields S Γ T ctors fieldPack fields args args' →
      FamEqFields S Γ (simpleFamily T ctors fieldPack) all (fields.map (simpleField fieldPack))
        args args'
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .recursive head tail =>
      .recursive (IndEqTm.toFamily head) (IndEqFields.toFamily tail)
  | _, _, _, _, .closed head tail => .value head (IndEqFields.toFamily tail)

end

/-- The family pack at a simple inductive type has the reducible equalities of `indPack`. -/
theorem simple_eqTm {t t' : Tm Head n} :
    (familyPack S Γ (simpleFamily T ctors fieldPack) []).eqTm t t' ↔
      (indPack S Γ T ctors fieldPack).eqTm t t' :=
  ⟨FamEqTm.toSimple rfl, IndEqTm.toFamily⟩

/-- The two packs have the same reducibly equal types, when the type constant is
convertible to itself. -/
theorem simple_eqTy (constRefl : S.E.convTy Γ (.const T) (.const T)) {B : Tm Head n} :
    (familyPack S Γ (simpleFamily T ctors fieldPack) []).eqTy B ↔
      (indPack S Γ T ctors fieldPack).eqTy B := by
  constructor
  · rintro ⟨X, is', red, ⟨rfl, rfl⟩, _, _⟩
    exact red
  · intro red
    exact ⟨.const T, [], red, ⟨rfl, rfl⟩, constRefl, .nil⟩

/-- The type constant of a simple inductive type, typed at a universe, is convertible to
itself; this is how the inductive case of the relation obtains `constRefl`. -/
theorem const_convTy_refl (laws : S.E.Laws S.R S.roles) {u : Head}
    (role : S.roles T = .inductive ctors) (typing : Typed S.R Γ (.const T) (.head u))
    (isUniverse : S.R.isUniverse u) : S.E.convTy Γ (.const T) (.const T) :=
  laws.convTy_of_convTm (laws.convTm_of_convNe (.inr (.inr ⟨T, ctors, role, rfl⟩))
    (.inr (.inr ⟨T, ctors, role, rfl⟩)) (laws.convNe_const T typing)) isUniverse

/-- **The pack of a simple inductive type is the family pack at its reading**, under the
premises of the inductive case of the relation: the type constant has its role and is typed
at a universe. -/
theorem simple_pack_eq (laws : S.E.Laws S.R S.roles) {u : Head}
    (role : S.roles T = .inductive ctors) (typing : Typed S.R Γ (.const T) (.head u))
    (isUniverse : S.R.isUniverse u) :
    familyPack S Γ (simpleFamily T ctors fieldPack) [] = indPack S Γ T ctors fieldPack :=
  PackEquiv.eq ⟨simple_eqTy (const_convTy_refl laws role typing isUniverse), simple_redTm,
    simple_eqTm⟩

end Equalities

/-! ## The hypotheses of the laws hold -/

section Hypotheses

variable {n : Nat} {Γ : Ctx Head n} {T : DeclName} {ctors : List (DeclName × List (Field Head))}
  {fieldPack : Tm Head 0 → Pack Head n}

theorem simpleFamily_rigid (role : S.roles T = .inductive ctors) :
    FormsRigid S (simpleFamily T ctors fieldPack) where
  whnf := by
    intro c nf fs mem form
    obtain ⟨⟨k, kfields⟩, entryMem, rfl⟩ := List.mem_map.mp mem
    have e : nf = appSpine (.const k) fs := form
    subst e
    exact canonical_whnf S.shape (ctorSpine_canonical role entryMem fs)
  not_neutral := by
    intro c nf fs mem form nNf
    obtain ⟨⟨k, kfields⟩, entryMem, rfl⟩ := List.mem_map.mp mem
    have e : nf = appSpine (.const k) fs := form
    subst e
    exact nNf.not_canonical (ctorSpine_canonical role entryMem fs)
  unique := by
    intro c c' nf fs fs' mem mem' form form'
    obtain ⟨⟨k, kfields⟩, entryMem, rfl⟩ := List.mem_map.mp mem
    obtain ⟨⟨k', kfields'⟩, entryMem', rfl⟩ := List.mem_map.mp mem'
    have e : nf = appSpine (.const k) fs := form
    have e' : nf = appSpine (.const k') fs' := form'
    obtain ⟨rfl, rfl⟩ := appSpine_const_injective (e.symm.trans e')
    have := S.constructors.fields_unique role entryMem entryMem'
    subst this
    exact ⟨rfl, rfl⟩

theorem simpleFamily_per : IndexPER (simpleFamily T ctors fieldPack) where
  symm := fun mem => nomatch mem
  trans := fun mem => nomatch mem

theorem simpleFamily_congr (formed : IsType S.R Γ (.const T)) :
    TypeCongr S Γ (simpleFamily T ctors fieldPack) := by
  intro is is' agree
  cases agree
  exact formed.refl

theorem simpleFamily_recExt : RecursiveExt S Γ (simpleFamily T ctors fieldPack) := by
  intro c fs fs' mem _ idx recMem
  obtain ⟨⟨k, kfields⟩, _, rfl⟩ := List.mem_map.mp mem
  obtain ⟨f, _, hf⟩ := List.mem_map.mp recMem
  cases f with
  | recursive =>
      cases hf
      exact .nil
  | closed F => cases hf

end Hypotheses

end Families
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
