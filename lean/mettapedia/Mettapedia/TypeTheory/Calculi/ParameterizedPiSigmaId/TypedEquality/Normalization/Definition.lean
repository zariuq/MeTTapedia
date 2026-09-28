import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Generic

/-!
# The reducibility relation

A reducible type comes with a pack: which types it is reducibly equal to,
which terms are reducible at it, and which pairs of terms are reducibly equal
at it. Instead of defining the pack by recursion on a reducibility derivation,
reducibility is an inductive relation between a type and its pack; the pack is
an index. This is the encoding without induction-recursion.

A type is reducible when it reduces to a universe below the current level, to
a neutral type, to a head that is not a universe, to a dependent function,
pair or identity type whose parts are reducible, or to a simple inductive type
whose closed field types are reducible. Function and pair types are
Kripke: their parts are reducible in every formed context reached by a
renaming.

Levels follow a level model of the universe heads, in any level order. The
relation at a level refers to the relations below it through the level order's
table (`UniverseLevel.below`), which unfolds by its equation
(`levelsBelow_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-- The fixed data of a normalization model. -/
structure Setting (Head L : Type) [LevelOrder L] where
  R : Rules Head
  roles : Roles Head
  E : GenericEquality Head
  levels : LevelModel R L
  shape : RootShape R roles
  constructors : ConstructorsDeclared roles

/-- What a reducible type provides. -/
structure Pack (Head : Type) (n : Nat) where
  eqTy : Tm Head n → Prop
  redTm : Tm Head n → Prop
  eqTm : Tm Head n → Tm Head n → Prop

/-- A relation between types in contexts and their packs. -/
abbrev RedRel (Head : Type) := ∀ {n : Nat}, Ctx Head n → Tm Head n → Pack Head n → Prop

/-- The relation with no reducible types. -/
def RedRel.empty : RedRel Head := fun _ _ _ => False

/-- A renaming into a formed context. -/
def World (S : Setting Head L) {n m : Nat} (Γ : Ctx Head n) (Δ : Ctx Head m)
    (ρ : Ren n m) : Prop :=
  CtxRen Γ Δ ρ ∧ CtxFormed S.R Δ

/-- Packs of the parts of a dependent function or pair type, in every world:
one for the domain, and one for the codomain at every reducible argument.
Reducibly equal arguments give reducibly equal codomains. -/
structure PolyPack (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (dom : Tm Head n)
    (cod : Tm Head (n + 1)) where
  domPack : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m}, World S Γ Δ ρ → Pack Head m
  codPack : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ)
    {a : Tm Head m}, (domPack w).redTm a → Pack Head m
  codExt : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ)
    {a b : Tm Head m} (ha : (domPack w).redTm a), (domPack w).redTm b →
    (domPack w).eqTm a b →
    (codPack w ha).eqTy (inst0 b (Presentation.rename (liftRen ρ) cod))

/-! ## Packs of the cases -/

section Packs

variable (S : Setting Head L)

/-- Universe `u`: types reducible below its level are its terms. -/
def universePack (rec : L → RedRel Head) {n : Nat} (Γ : Ctx Head n) (u : Head) :
    Pack Head n where
  eqTy B := ∃ u', RedTy S.R S.roles Γ B (.head u') ∧ (u = u' ∨ S.R.headEq u u')
  redTm t := ∃ nf, RedTm S.R S.roles Γ t nf (.head u) ∧ IsTypeForm S.roles nf ∧
    S.E.convTm Γ nf nf (.head u) ∧ ∃ P, rec (S.levels.level u) Γ t P
  eqTm t t' := ∃ nf nf', RedTm S.R S.roles Γ t nf (.head u) ∧
    RedTm S.R S.roles Γ t' nf' (.head u) ∧ IsTypeForm S.roles nf ∧ IsTypeForm S.roles nf' ∧
    S.E.convTm Γ nf nf' (.head u) ∧
    (∃ P', rec (S.levels.level u) Γ t' P') ∧
    ∃ P, rec (S.levels.level u) Γ t P ∧ P.eqTy t'

/-- A neutral type `ty`: its terms reduce to neutral terms. -/
def neutralPack {n : Nat} (Γ : Ctx Head n) (ty : Tm Head n) : Pack Head n where
  eqTy B := ∃ ty', RedTy S.R S.roles Γ B ty' ∧ Neutral S.roles ty' ∧
    ∃ v, S.R.isUniverse v ∧ S.E.convNe Γ ty ty' (.head v)
  redTm t := ∃ nf, RedTm S.R S.roles Γ t nf ty ∧ Neutral S.roles nf ∧
    S.E.convNe Γ nf nf ty
  eqTm t t' := ∃ nf nf', RedTm S.R S.roles Γ t nf ty ∧ RedTm S.R S.roles Γ t' nf' ty ∧
    Neutral S.roles nf ∧ Neutral S.roles nf' ∧ S.E.convNe Γ nf nf' ty

/-- A head `h` that is not a universe: its terms reduce to neutral terms. -/
def groundPack {n : Nat} (Γ : Ctx Head n) (h : Head) : Pack Head n where
  eqTy B := ∃ h', RedTy S.R S.roles Γ B (.head h') ∧ (h = h' ∨ S.R.headEq h h')
  redTm t := ∃ nf, RedTm S.R S.roles Γ t nf (.head h) ∧ Neutral S.roles nf ∧
    S.E.convNe Γ nf nf (.head h)
  eqTm t t' := ∃ nf nf', RedTm S.R S.roles Γ t nf (.head h) ∧
    RedTm S.R S.roles Γ t' nf' (.head h) ∧ Neutral S.roles nf ∧ Neutral S.roles nf' ∧
    S.E.convNe Γ nf nf' (.head h)

/-- Reducible terms of a dependent function type. -/
def PiRedTm {n : Nat} {Γ : Ctx Head n} {dom : Tm Head n} {cod : Tm Head (n + 1)}
    (P : PolyPack S Γ dom cod) (t : Tm Head n) : Prop :=
  ∃ nf, RedTm S.R S.roles Γ t nf (.pi dom cod) ∧ IsFun S.roles nf ∧
    S.E.convTm Γ nf nf (.pi dom cod) ∧
    (∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ) {a : Tm Head m}
      (ha : (P.domPack w).redTm a),
      (P.codPack w ha).redTm (.app (Presentation.rename ρ nf) a)) ∧
    (∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ) {a b : Tm Head m}
      (ha : (P.domPack w).redTm a), (P.domPack w).redTm b → (P.domPack w).eqTm a b →
      (P.codPack w ha).eqTm (.app (Presentation.rename ρ nf) a)
        (.app (Presentation.rename ρ nf) b))

/-- Dependent function type with the given part packs. -/
def piPack {n : Nat} (Γ : Ctx Head n) (dom : Tm Head n) (cod : Tm Head (n + 1))
    (P : PolyPack S Γ dom cod) : Pack Head n where
  eqTy B := ∃ dom' cod', RedTy S.R S.roles Γ B (.pi dom' cod') ∧
    S.E.convTy Γ (.pi dom cod) (.pi dom' cod') ∧
    (∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
      (P.domPack w).eqTy (Presentation.rename ρ dom')) ∧
    (∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ) {a : Tm Head m}
      (ha : (P.domPack w).redTm a),
      (P.codPack w ha).eqTy (inst0 a (Presentation.rename (liftRen ρ) cod')))
  redTm t := PiRedTm S P t
  eqTm t t' := PiRedTm S P t ∧ PiRedTm S P t' ∧
    ∃ nf nf', RedTm S.R S.roles Γ t nf (.pi dom cod) ∧
      RedTm S.R S.roles Γ t' nf' (.pi dom cod) ∧ IsFun S.roles nf ∧ IsFun S.roles nf' ∧
      S.E.convTm Γ nf nf' (.pi dom cod) ∧
      ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ) {a : Tm Head m}
        (ha : (P.domPack w).redTm a),
        (P.codPack w ha).eqTm (.app (Presentation.rename ρ nf) a)
          (.app (Presentation.rename ρ nf') a)

/-- Reducible terms of a dependent pair type. -/
def SigmaRedTm {n : Nat} {Γ : Ctx Head n} {dom : Tm Head n} {cod : Tm Head (n + 1)}
    (P : PolyPack S Γ dom cod) (t : Tm Head n) : Prop :=
  ∃ nf, RedTm S.R S.roles Γ t nf (.sigma dom cod) ∧ IsPair S.roles nf ∧
    S.E.convTm Γ nf nf (.sigma dom cod) ∧
    ∃ first : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
        (P.domPack w).redTm (.fst (Presentation.rename ρ nf)),
      ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
        (P.codPack w (first w)).redTm (.snd (Presentation.rename ρ nf))

/-- Dependent pair type with the given part packs. -/
def sigmaPack {n : Nat} (Γ : Ctx Head n) (dom : Tm Head n) (cod : Tm Head (n + 1))
    (P : PolyPack S Γ dom cod) : Pack Head n where
  eqTy B := ∃ dom' cod', RedTy S.R S.roles Γ B (.sigma dom' cod') ∧
    S.E.convTy Γ (.sigma dom cod) (.sigma dom' cod') ∧
    (∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
      (P.domPack w).eqTy (Presentation.rename ρ dom')) ∧
    (∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ) {a : Tm Head m}
      (ha : (P.domPack w).redTm a),
      (P.codPack w ha).eqTy (inst0 a (Presentation.rename (liftRen ρ) cod')))
  redTm t := SigmaRedTm S P t
  eqTm t t' := SigmaRedTm S P t ∧ SigmaRedTm S P t' ∧
    ∃ nf nf', RedTm S.R S.roles Γ t nf (.sigma dom cod) ∧
      RedTm S.R S.roles Γ t' nf' (.sigma dom cod) ∧ IsPair S.roles nf ∧ IsPair S.roles nf' ∧
      S.E.convTm Γ nf nf' (.sigma dom cod) ∧
      (∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
        (P.domPack w).eqTm (.fst (Presentation.rename ρ nf))
          (.fst (Presentation.rename ρ nf'))) ∧
      ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ)
        (first : (P.domPack w).redTm (.fst (Presentation.rename ρ nf))),
        (P.codPack w first).eqTm (.snd (Presentation.rename ρ nf))
          (.snd (Presentation.rename ρ nf'))

/-- The weak-head normal forms of an identity proof: reflexivity at a subject
reducibly equal to both endpoints, or a neutral term. -/
def IdProp {n : Nat} (Γ : Ctx Head n) (ty lhs rhs : Tm Head n) (tyPack : Pack Head n)
    (nf : Tm Head n) : Prop :=
  (∃ x, nf = .refl x ∧ Typed S.R Γ x ty ∧ tyPack.eqTm lhs x ∧ tyPack.eqTm rhs x) ∨
    (Neutral S.roles nf ∧ S.E.convNe Γ nf nf (.id ty lhs rhs))

/-- Reducibly equal weak-head normal forms of identity proofs. -/
def IdPropEq {n : Nat} (Γ : Ctx Head n) (ty lhs rhs : Tm Head n) (tyPack : Pack Head n)
    (nf nf' : Tm Head n) : Prop :=
  (∃ x x', nf = .refl x ∧ nf' = .refl x' ∧ Typed S.R Γ x ty ∧ Typed S.R Γ x' ty ∧
      tyPack.eqTm lhs x ∧ tyPack.eqTm lhs x' ∧ tyPack.eqTm rhs x ∧ tyPack.eqTm rhs x') ∨
    (Neutral S.roles nf ∧ Neutral S.roles nf' ∧ S.E.convNe Γ nf nf' (.id ty lhs rhs))

/-- Identity type at a carrier with pack `tyPack`. -/
def idPack {n : Nat} (Γ : Ctx Head n) (ty lhs rhs : Tm Head n) (tyPack : Pack Head n) :
    Pack Head n where
  eqTy B := ∃ ty' lhs' rhs', RedTy S.R S.roles Γ B (.id ty' lhs' rhs') ∧
    S.E.convTy Γ (.id ty lhs rhs) (.id ty' lhs' rhs') ∧
    tyPack.eqTy ty' ∧ tyPack.eqTm lhs lhs' ∧ tyPack.eqTm rhs rhs'
  redTm t := ∃ nf, RedTm S.R S.roles Γ t nf (.id ty lhs rhs) ∧
    S.E.convTm Γ nf nf (.id ty lhs rhs) ∧ IdProp S Γ ty lhs rhs tyPack nf
  eqTm t t' := ∃ nf nf', RedTm S.R S.roles Γ t nf (.id ty lhs rhs) ∧
    RedTm S.R S.roles Γ t' nf' (.id ty lhs rhs) ∧
    S.E.convTm Γ nf nf' (.id ty lhs rhs) ∧ IdPropEq S Γ ty lhs rhs tyPack nf nf'

/-! ## Simple inductive types -/

mutual

/-- Reducible terms of a simple inductive type `T` with constructors `ctors`,
given the packs of the closed field types: terms reducing to a constructor
applied to reducible arguments, or to a neutral term. -/
inductive IndRedTm {n : Nat} (Γ : Ctx Head n) (T : DeclName)
    (ctors : List (DeclName × List (Field Head))) (fieldPack : Tm Head 0 → Pack Head n) :
    Tm Head n → Prop where
  | mk {t nf : Tm Head n} (red : RedTm S.R S.roles Γ t nf (.const T))
      (conv : S.E.convTm Γ nf nf (.const T)) (normal : IndNf Γ T ctors fieldPack nf) :
      IndRedTm Γ T ctors fieldPack t

/-- The weak-head normal forms of reducible terms of a simple inductive type. -/
inductive IndNf {n : Nat} (Γ : Ctx Head n) (T : DeclName)
    (ctors : List (DeclName × List (Field Head))) (fieldPack : Tm Head 0 → Pack Head n) :
    Tm Head n → Prop where
  | ctor {k : DeclName} {fields : List (Field Head)} {args : List (Tm Head n)}
      (mem : (k, fields) ∈ ctors) (arguments : IndFields Γ T ctors fieldPack fields args) :
      IndNf Γ T ctors fieldPack (appSpine (.const k) args)
  | neutral {nf : Tm Head n} (neutral : Neutral S.roles nf)
      (conv : S.E.convNe Γ nf nf (.const T)) : IndNf Γ T ctors fieldPack nf

/-- Reducible arguments for the fields of a constructor. -/
inductive IndFields {n : Nat} (Γ : Ctx Head n) (T : DeclName)
    (ctors : List (DeclName × List (Field Head))) (fieldPack : Tm Head 0 → Pack Head n) :
    List (Field Head) → List (Tm Head n) → Prop where
  | nil : IndFields Γ T ctors fieldPack [] []
  | recursive {fields : List (Field Head)} {args : List (Tm Head n)} {a : Tm Head n}
      (head : IndRedTm Γ T ctors fieldPack a) (tail : IndFields Γ T ctors fieldPack fields args) :
      IndFields Γ T ctors fieldPack (.recursive :: fields) (a :: args)
  | closed {fields : List (Field Head)} {args : List (Tm Head n)} {F : Tm Head 0}
      {a : Tm Head n} (head : (fieldPack F).redTm a)
      (tail : IndFields Γ T ctors fieldPack fields args) :
      IndFields Γ T ctors fieldPack (.closed F :: fields) (a :: args)

end

mutual

/-- Reducibly equal terms of a simple inductive type. -/
inductive IndEqTm {n : Nat} (Γ : Ctx Head n) (T : DeclName)
    (ctors : List (DeclName × List (Field Head))) (fieldPack : Tm Head 0 → Pack Head n) :
    Tm Head n → Tm Head n → Prop where
  | mk {t t' nf nf' : Tm Head n} (red : RedTm S.R S.roles Γ t nf (.const T))
      (red' : RedTm S.R S.roles Γ t' nf' (.const T)) (conv : S.E.convTm Γ nf nf' (.const T))
      (normal : IndEqNf Γ T ctors fieldPack nf nf') : IndEqTm Γ T ctors fieldPack t t'

/-- Reducibly equal weak-head normal forms of a simple inductive type: the same
constructor applied to reducibly equal arguments, or convertible neutral
terms. -/
inductive IndEqNf {n : Nat} (Γ : Ctx Head n) (T : DeclName)
    (ctors : List (DeclName × List (Field Head))) (fieldPack : Tm Head 0 → Pack Head n) :
    Tm Head n → Tm Head n → Prop where
  | ctor {k : DeclName} {fields : List (Field Head)} {args args' : List (Tm Head n)}
      (mem : (k, fields) ∈ ctors) (arguments : IndEqFields Γ T ctors fieldPack fields args args') :
      IndEqNf Γ T ctors fieldPack (appSpine (.const k) args) (appSpine (.const k) args')
  | neutral {nf nf' : Tm Head n} (neutral : Neutral S.roles nf) (neutral' : Neutral S.roles nf')
      (conv : S.E.convNe Γ nf nf' (.const T)) : IndEqNf Γ T ctors fieldPack nf nf'

/-- Reducibly equal arguments for the fields of a constructor. -/
inductive IndEqFields {n : Nat} (Γ : Ctx Head n) (T : DeclName)
    (ctors : List (DeclName × List (Field Head))) (fieldPack : Tm Head 0 → Pack Head n) :
    List (Field Head) → List (Tm Head n) → List (Tm Head n) → Prop where
  | nil : IndEqFields Γ T ctors fieldPack [] [] []
  | recursive {fields : List (Field Head)} {args args' : List (Tm Head n)} {a a' : Tm Head n}
      (head : IndEqTm Γ T ctors fieldPack a a')
      (tail : IndEqFields Γ T ctors fieldPack fields args args') :
      IndEqFields Γ T ctors fieldPack (.recursive :: fields) (a :: args) (a' :: args')
  | closed {fields : List (Field Head)} {args args' : List (Tm Head n)} {F : Tm Head 0}
      {a a' : Tm Head n} (head : (fieldPack F).eqTm a a')
      (tail : IndEqFields Γ T ctors fieldPack fields args args') :
      IndEqFields Γ T ctors fieldPack (.closed F :: fields) (a :: args) (a' :: args')

end

/-- A simple inductive type with the given packs of its closed field types. -/
def indPack {n : Nat} (Γ : Ctx Head n) (T : DeclName) (ctors : List (DeclName × List (Field Head)))
    (fieldPack : Tm Head 0 → Pack Head n) : Pack Head n where
  eqTy B := RedTy S.R S.roles Γ B (.const T)
  redTm t := IndRedTm S Γ T ctors fieldPack t
  eqTm t t' := IndEqTm S Γ T ctors fieldPack t t'

end Packs

/-! ## The relation at one level -/

/-- Reducibility at level `l`, given the relations below `l`. -/
inductive LR (S : Setting Head L) (l : L) (rec : L → RedRel Head) :
    {n : Nat} → Ctx Head n → Tm Head n → Pack Head n → Prop where
  | sort {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {u : Head}
      (isUniverse : S.R.isUniverse u) (below : S.levels.level u < l)
      (formed : CtxFormed S.R Γ) (red : RedTy S.R S.roles Γ A (.head u)) :
      LR S l rec Γ A (universePack S rec Γ u)
  | neutral {n : Nat} {Γ : Ctx Head n} {A ty : Tm Head n} {u : Head}
      (red : RedTy S.R S.roles Γ A ty) (neutral : Neutral S.roles ty)
      (isUniverse : S.R.isUniverse u) (typing : Typed S.R Γ ty (.head u))
      (refl : S.E.convNe Γ ty ty (.head u)) :
      LR S l rec Γ A (neutralPack S Γ ty)
  | ground {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {h u : Head}
      (notUniverse : ¬ S.R.isUniverse h) (red : RedTy S.R S.roles Γ A (.head h))
      (typing : Typed S.R Γ (.head h) (.head u)) (isUniverse : S.R.isUniverse u) :
      LR S l rec Γ A (groundPack S Γ h)
  | pi {n : Nat} {Γ : Ctx Head n} {A dom : Tm Head n} {cod : Tm Head (n + 1)}
      (red : RedTy S.R S.roles Γ A (.pi dom cod)) (domType : IsType S.R Γ dom)
      (codType : IsType S.R (.snoc Γ dom) cod)
      (refl : S.E.convTy Γ (.pi dom cod) (.pi dom cod)) (P : PolyPack S Γ dom cod)
      (domAdequate : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
        LR S l rec Δ (Presentation.rename ρ dom) (P.domPack w))
      (codAdequate : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ)
        {a : Tm Head m} (ha : (P.domPack w).redTm a),
        LR S l rec Δ (inst0 a (Presentation.rename (liftRen ρ) cod)) (P.codPack w ha)) :
      LR S l rec Γ A (piPack S Γ dom cod P)
  | sigma {n : Nat} {Γ : Ctx Head n} {A dom : Tm Head n} {cod : Tm Head (n + 1)}
      (red : RedTy S.R S.roles Γ A (.sigma dom cod)) (domType : IsType S.R Γ dom)
      (codType : IsType S.R (.snoc Γ dom) cod)
      (refl : S.E.convTy Γ (.sigma dom cod) (.sigma dom cod)) (P : PolyPack S Γ dom cod)
      (domAdequate : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
        LR S l rec Δ (Presentation.rename ρ dom) (P.domPack w))
      (codAdequate : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ)
        {a : Tm Head m} (ha : (P.domPack w).redTm a),
        LR S l rec Δ (inst0 a (Presentation.rename (liftRen ρ) cod)) (P.codPack w ha)) :
      LR S l rec Γ A (sigmaPack S Γ dom cod P)
  | ident {n : Nat} {Γ : Ctx Head n} {A ty lhs rhs : Tm Head n}
      (red : RedTy S.R S.roles Γ A (.id ty lhs rhs))
      (refl : S.E.convTy Γ (.id ty lhs rhs) (.id ty lhs rhs))
      (tyPack : Pack Head n) (tyAdequate : LR S l rec Γ ty tyPack)
      (lhsRed : tyPack.redTm lhs) (rhsRed : tyPack.redTm rhs)
      (lhsRefl : tyPack.eqTm lhs lhs) (rhsRefl : tyPack.eqTm rhs rhs)
      (tySymm : ∀ {t t'}, tyPack.eqTm t t' → tyPack.eqTm t' t)
      (tyTrans : ∀ {t t' t''}, tyPack.eqTm t t' → tyPack.eqTm t' t'' → tyPack.eqTm t t'') :
      LR S l rec Γ A (idPack S Γ ty lhs rhs tyPack)
  | inductiveType {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {T : DeclName}
      {ctors : List (DeclName × List (Field Head))} {u : Head}
      (red : RedTy S.R S.roles Γ A (.const T)) (role : S.roles T = .inductive ctors)
      (typing : Typed S.R Γ (.const T) (.head u)) (isUniverse : S.R.isUniverse u)
      (fieldPack : Tm Head 0 → Pack Head n)
      (fieldAdequate : ∀ {k : DeclName} {fields : List (Field Head)} {F : Tm Head 0},
        (k, fields) ∈ ctors → Field.closed F ∈ fields →
        LR S l rec Γ (liftClosed F) (fieldPack F)) :
      LR S l rec Γ A (indPack S Γ T ctors fieldPack)

/-! ## All levels -/

/-- The relations below each level: the level order's table of `LR`. -/
noncomputable def levelsBelow (S : Setting Head L) : L → L → RedRel Head :=
  UniverseLevel.below (fun l rec => fun Γ A P => LR S l rec Γ A P) RedRel.empty

/-- Reducibility at level `l`. -/
noncomputable def LogRel (S : Setting Head L) (l : L) : RedRel Head :=
  fun Γ A P => LR S l (levelsBelow S l) Γ A P

theorem levelsBelow_iff (S : Setting Head L) :
    ∀ {l k : L}, k < l → ∀ {n : Nat} (Γ : Ctx Head n) (A : Tm Head n) (P : Pack Head n),
      levelsBelow S l k Γ A P ↔ LogRel S k Γ A P := by
  intro l k h n Γ A P
  unfold LogRel levelsBelow
  rw [UniverseLevel.below_eq _ _ l]
  simp only [if_pos h]

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
