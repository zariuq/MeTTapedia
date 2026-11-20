import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Definition

/-!
# Inductive families: the pack

An inductive family is read at its parameters in a context. Its type at a list of indices
is a weak-head normal type; each constructor has canonical forms built from its fields, a
list of fields, and the indices it targets at given fields. A field is a value of a type
whose pack is given, or a recursive occurrence of the family at indices computed from the
constructor's fields.

The reducible terms of the family at indices `is` are the terms that reduce to a
constructor form whose fields are reducible, the value fields at their packs and the
recursive fields at the family itself at their indices, and whose target indices are
reducibly equal to `is` at the packs of the index types; or that reduce to a neutral term
convertible to itself. Reducibility is defined at all indices at once, since recursive
fields sit at other indices than the term itself.

Two reducible terms are reducibly equal when they reduce to convertible normal forms that
are the same constructor with reducibly equal fields, both agreeing with `is`, or
convertible neutral terms. Recursive fields are compared at the indices computed from the
left-hand fields.

The data are semantic: which normal forms are which constructor (`CtorAt.form`, which also
states how stored parameters agree with the family's), the packs of the value fields and of
the index types, and the index functions. The simple inductive types and the identity type
are instances (modules `Simple` and `Identity`); declared families are read from their
declarations (module `Declaration`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace Families

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## The data of a family at its parameters -/

/-- A field of a constructor, read at the family's parameters: a value with the pack of its
type, or a recursive occurrence of the family at the indices computed from all the fields
of the constructor. -/
inductive FieldAt (Head : Type) (n : Nat) where
  | value (pack : Pack Head n)
  | recursive (indices : List (Tm Head n) → List (Tm Head n))

/-- A constructor, read at the family's parameters. `form nf fs` says that the weak-head
normal form `nf` is this constructor applied to the fields `fs`, with any parameters it
stores agreeing with the family's. -/
structure CtorAt (Head : Type) (n : Nat) where
  form : Tm Head n → List (Tm Head n) → Prop
  fields : List (FieldAt Head n)
  target : List (Tm Head n) → List (Tm Head n)

/-- An inductive family read at its parameters: its type at given indices, its constructors,
the packs of its index types, and which weak-head normal types are the same family, at
agreeing parameters, at given indices. -/
structure FamilyAt (Head : Type) (n : Nat) where
  type : List (Tm Head n) → Tm Head n
  ctors : List (CtorAt Head n)
  indexPacks : List (Pack Head n)
  sameFormer : Tm Head n → List (Tm Head n) → Prop

/-- Two lists of indices that are reducibly equal position by position, at the packs of the
index types. -/
inductive IndexAgree {n : Nat} :
    List (Pack Head n) → List (Tm Head n) → List (Tm Head n) → Prop where
  | nil : IndexAgree [] [] []
  | cons {P : Pack Head n} {Ps : List (Pack Head n)} {i j : Tm Head n}
      {is js : List (Tm Head n)} (head : P.eqTm i j) (tail : IndexAgree Ps is js) :
      IndexAgree (P :: Ps) (i :: is) (j :: js)

/-! ## Reducible terms -/

section Packs

variable (S : Setting Head L)

mutual

/-- Reducible terms of a family at the indices `is`. -/
inductive FamRedTm {n : Nat} (Γ : Ctx Head n) (F : FamilyAt Head n) :
    List (Tm Head n) → Tm Head n → Prop where
  | mk {is : List (Tm Head n)} {t nf : Tm Head n}
      (red : RedTm S.R S.roles Γ t nf (F.type is))
      (conv : S.E.convTm Γ nf nf (F.type is)) (normal : FamNf Γ F is nf) :
      FamRedTm Γ F is t

/-- The weak-head normal forms of reducible terms of a family: a constructor form with
reducible fields whose target agrees with the indices, or a neutral term. -/
inductive FamNf {n : Nat} (Γ : Ctx Head n) (F : FamilyAt Head n) :
    List (Tm Head n) → Tm Head n → Prop where
  | ctor {is : List (Tm Head n)} {c : CtorAt Head n} {fs : List (Tm Head n)} {nf : Tm Head n}
      (mem : c ∈ F.ctors) (form : c.form nf fs) (fields : FamFields Γ F fs c.fields fs)
      (agree : IndexAgree F.indexPacks is (c.target fs)) : FamNf Γ F is nf
  | neutral {is : List (Tm Head n)} {nf : Tm Head n} (neutral : Neutral S.roles nf)
      (conv : S.E.convNe Γ nf nf (F.type is)) : FamNf Γ F is nf

/-- Reducible fields of a constructor. `all` is the whole list of fields, from which the
indices of recursive fields are computed. -/
inductive FamFields {n : Nat} (Γ : Ctx Head n) (F : FamilyAt Head n) :
    List (Tm Head n) → List (FieldAt Head n) → List (Tm Head n) → Prop where
  | nil {all : List (Tm Head n)} : FamFields Γ F all [] []
  | value {all : List (Tm Head n)} {P : Pack Head n} {fields : List (FieldAt Head n)}
      {a : Tm Head n} {args : List (Tm Head n)} (head : P.redTm a)
      (tail : FamFields Γ F all fields args) :
      FamFields Γ F all (.value P :: fields) (a :: args)
  | recursive {all : List (Tm Head n)} {idx : List (Tm Head n) → List (Tm Head n)}
      {fields : List (FieldAt Head n)} {a : Tm Head n} {args : List (Tm Head n)}
      (head : FamRedTm Γ F (idx all) a) (tail : FamFields Γ F all fields args) :
      FamFields Γ F all (.recursive idx :: fields) (a :: args)

end

mutual

/-- Reducibly equal terms of a family at the indices `is`. -/
inductive FamEqTm {n : Nat} (Γ : Ctx Head n) (F : FamilyAt Head n) :
    List (Tm Head n) → Tm Head n → Tm Head n → Prop where
  | mk {is : List (Tm Head n)} {t t' nf nf' : Tm Head n}
      (red : RedTm S.R S.roles Γ t nf (F.type is))
      (red' : RedTm S.R S.roles Γ t' nf' (F.type is))
      (conv : S.E.convTm Γ nf nf' (F.type is)) (normal : FamEqNf Γ F is nf nf') :
      FamEqTm Γ F is t t'

/-- Reducibly equal weak-head normal forms: the same constructor with reducibly equal fields,
both agreeing with the indices, or convertible neutral terms. -/
inductive FamEqNf {n : Nat} (Γ : Ctx Head n) (F : FamilyAt Head n) :
    List (Tm Head n) → Tm Head n → Tm Head n → Prop where
  | ctor {is : List (Tm Head n)} {c : CtorAt Head n} {fs fs' : List (Tm Head n)}
      {nf nf' : Tm Head n} (mem : c ∈ F.ctors) (form : c.form nf fs) (form' : c.form nf' fs')
      (fields : FamEqFields Γ F fs c.fields fs fs')
      (agree : IndexAgree F.indexPacks is (c.target fs))
      (agree' : IndexAgree F.indexPacks is (c.target fs')) : FamEqNf Γ F is nf nf'
  | neutral {is : List (Tm Head n)} {nf nf' : Tm Head n} (neutral : Neutral S.roles nf)
      (neutral' : Neutral S.roles nf') (conv : S.E.convNe Γ nf nf' (F.type is)) :
      FamEqNf Γ F is nf nf'

/-- Reducibly equal fields of a constructor. Recursive fields are compared at the indices
computed from `all`, the left-hand fields. -/
inductive FamEqFields {n : Nat} (Γ : Ctx Head n) (F : FamilyAt Head n) :
    List (Tm Head n) → List (FieldAt Head n) → List (Tm Head n) → List (Tm Head n) → Prop where
  | nil {all : List (Tm Head n)} : FamEqFields Γ F all [] [] []
  | value {all : List (Tm Head n)} {P : Pack Head n} {fields : List (FieldAt Head n)}
      {a a' : Tm Head n} {args args' : List (Tm Head n)} (head : P.eqTm a a')
      (tail : FamEqFields Γ F all fields args args') :
      FamEqFields Γ F all (.value P :: fields) (a :: args) (a' :: args')
  | recursive {all : List (Tm Head n)} {idx : List (Tm Head n) → List (Tm Head n)}
      {fields : List (FieldAt Head n)} {a a' : Tm Head n} {args args' : List (Tm Head n)}
      (head : FamEqTm Γ F (idx all) a a') (tail : FamEqFields Γ F all fields args args') :
      FamEqFields Γ F all (.recursive idx :: fields) (a :: args) (a' :: args')

end

/-- The pack of a family at the indices `is`. A type is reducibly equal to it when it
reduces to the same family, at agreeing parameters, at reducibly equal indices, and is
convertible to it. -/
def familyPack {n : Nat} (Γ : Ctx Head n) (F : FamilyAt Head n) (is : List (Tm Head n)) :
    Pack Head n where
  eqTy B := ∃ X is', RedTy S.R S.roles Γ B X ∧ F.sameFormer X is' ∧
    S.E.convTy Γ (F.type is) X ∧ IndexAgree F.indexPacks is is'
  redTm t := FamRedTm S Γ F is t
  eqTm t t' := FamEqTm S Γ F is t t'

end Packs

end Families
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
