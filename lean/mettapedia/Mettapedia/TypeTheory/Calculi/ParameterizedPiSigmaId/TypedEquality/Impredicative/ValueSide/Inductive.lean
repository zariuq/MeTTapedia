import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Pack

/-!
# Packs of simple inductive types

A simple inductive type `T` lists its constructors, each with fields that are
`T` itself or a closed type not mentioning it. Its pack, given the packs of the
closed field types:

* relates two terms that reduce to one constructor applied to arguments
  related field by field, recursive fields by the pack itself, closed fields
  by the field type's pack; and two terms that reduce to daimonic terms;
* realizes a value by the meet of the realizers of its *shapes*: a constructor
  with the shapes of its recursive fields and the values of its closed fields,
  read by `ctorReal T k`, or a term stuck on the daimon, read by `stuckReal T`.

The numbers are the instance with the constructors `zero`, without fields,
and `suc`, with one recursive field.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open UniverseLevel (LevelOrder)
open Realizability (Daimonic HasShape)

variable {Head L : Type} [LevelOrder L]

/-- The closed types among the fields of a list of constructors. -/
def closedFields (cs : List (DeclName × List (Field Head))) : List (Tm Head 0) :=
  cs.flatMap fun c => c.2.filterMap fun
    | .recursive => none
    | .closed F => some F

mutual

/-- Terms related at an inductive type with constructors `cs`, given the packs
`field` of its closed field types: two terms reducing to one constructor applied
to arguments related field by field, or two terms reducing to daimonic terms. -/
inductive IndRel (V : Model Head L) (cs : List (DeclName × List (Field Head))) {n : Nat}
    (field : Tm Head 0 → Pack V n) : Tm Head n → Tm Head n → Prop where
  | ctor {k : DeclName} {fs : List (Field Head)} {t t' : Tm Head n}
      {as as' : List (Tm Head n)} :
      (k, fs) ∈ cs → WhRed V.rules V.roles t (appSpine (.const k) as) →
      WhRed V.rules V.roles t' (appSpine (.const k) as') →
      IndFields V cs field fs as as' → IndRel V cs field t t'
  | star {t t' u u' : Tm Head n} :
      WhRed V.rules V.roles t u → Daimonic V.roles V.star u →
      WhRed V.rules V.roles t' u' → Daimonic V.roles V.star u' → IndRel V cs field t t'

/-- Arguments related field by field. -/
inductive IndFields (V : Model Head L) (cs : List (DeclName × List (Field Head))) {n : Nat}
    (field : Tm Head 0 → Pack V n) :
    List (Field Head) → List (Tm Head n) → List (Tm Head n) → Prop where
  | nil : IndFields V cs field [] [] []
  | recursive {fs : List (Field Head)} {t t' : Tm Head n} {as as' : List (Tm Head n)} :
      IndRel V cs field t t' → IndFields V cs field fs as as' →
      IndFields V cs field (.recursive :: fs) (t :: as) (t' :: as')
  | closed {F : Tm Head 0} {fs : List (Field Head)} {t t' : Tm Head n}
      {as as' : List (Tm Head n)} :
      (field F).rel t t' → IndFields V cs field fs as as' →
      IndFields V cs field (.closed F :: fs) (t :: as) (t' :: as')

end

mutual

/-- The shape of a value of an inductive type: a constructor with the shapes of
its fields, or stuck on the daimon. -/
inductive IndShape (Head : Type) (n : Nat) : Type where
  | ctor (k : DeclName) (fields : IndShapes Head n)
  | star

/-- The shapes of the fields of a constructor: the shape of a recursive field,
the value of a closed field with its type. -/
inductive IndShapes (Head : Type) (n : Nat) : Type where
  | nil
  | recursive (shape : IndShape Head n) (rest : IndShapes Head n)
  | closed (type : Tm Head 0) (value : Tm Head n) (rest : IndShapes Head n)

end

mutual

/-- The realizers of a shape of a value of `T`: `ctorReal T k` of the realizers of
the fields at a constructor `k`, `stuckReal T` at the daimon. -/
def IndShape.real (V : Model Head L) (T : DeclName) {n : Nat} (field : Tm Head 0 → Pack V n) :
    IndShape Head n → V.alg.Cand
  | .ctor k fields => V.alg.ctorReal T k (IndShapes.reals V T field fields)
  | .star => V.alg.stuckReal T

/-- The realizers of the fields of a constructor: those of the shape of a
recursive field, and those of the value of a closed field in its type's pack. -/
def IndShapes.reals (V : Model Head L) (T : DeclName) {n : Nat}
    (field : Tm Head 0 → Pack V n) : IndShapes Head n → List V.alg.Cand
  | .nil => []
  | .recursive shape rest => IndShape.real V T field shape :: IndShapes.reals V T field rest
  | .closed F value rest => (field F).real value :: IndShapes.reals V T field rest

end

mutual

/-- A term of an inductive type with constructors `cs` has a shape: it reduces to
a constructor applied to arguments with the shapes of the fields, or to a
daimonic term. -/
inductive HasIndShape (V : Model Head L) (cs : List (DeclName × List (Field Head))) {n : Nat} :
    Tm Head n → IndShape Head n → Prop where
  | ctor {k : DeclName} {fs : List (Field Head)} {t : Tm Head n} {as : List (Tm Head n)}
      {fields : IndShapes Head n} :
      (k, fs) ∈ cs → WhRed V.rules V.roles t (appSpine (.const k) as) →
      HasIndShapes V cs fs as fields → HasIndShape V cs t (.ctor k fields)
  | star {t u : Tm Head n} :
      WhRed V.rules V.roles t u → Daimonic V.roles V.star u → HasIndShape V cs t .star

/-- Arguments with the shapes of the fields: a recursive field has a shape, a
closed field is recorded with its value. -/
inductive HasIndShapes (V : Model Head L) (cs : List (DeclName × List (Field Head))) {n : Nat} :
    List (Field Head) → List (Tm Head n) → IndShapes Head n → Prop where
  | nil : HasIndShapes V cs [] [] .nil
  | recursive {fs : List (Field Head)} {a : Tm Head n} {as : List (Tm Head n)}
      {shape : IndShape Head n} {rest : IndShapes Head n} :
      HasIndShape V cs a shape → HasIndShapes V cs fs as rest →
      HasIndShapes V cs (.recursive :: fs) (a :: as) (.recursive shape rest)
  | closed {F : Tm Head 0} {fs : List (Field Head)} {a : Tm Head n} {as : List (Tm Head n)}
      {rest : IndShapes Head n} :
      HasIndShapes V cs fs as rest →
      HasIndShapes V cs (.closed F :: fs) (a :: as) (.closed F a rest)

end

variable (V : Model Head L)

/-- The pack of the inductive type `T` with constructors `cs`, given the packs of
its closed field types: terms related by `IndRel`, realized by the meet of the
realizers of their shapes. -/
def indPack (T : DeclName) (cs : List (DeclName × List (Field Head))) {n : Nat}
    (field : Tm Head 0 → Pack V n) : Pack V n where
  rel := IndRel V cs field
  real := fun a => V.alg.meet fun s : {s : IndShape Head n // HasIndShape V cs a s} =>
    s.1.real V T field

/-- The constructors of the numbers: `zero` without fields, `suc` with one
recursive field. -/
def numConstructors : List (DeclName × List (Field Head)) :=
  [(V.zero, []), (V.suc, [.recursive])]

/-- The numbers have no closed field types. -/
theorem closedFields_numConstructors : closedFields (numConstructors V) = [] :=
  rfl

/-- The numbers are an inductive type with the constructors `numConstructors`. -/
theorem Model.Laws.num_role {V : Model Head L} (laws : V.Laws) :
    V.roles V.num = .inductive (numConstructors V) :=
  laws.values.num

/-- The pack of the numbers: the inductive pack, with no closed field. -/
def numIndPack (n : Nat) : Pack V n :=
  indPack V V.num (numConstructors V) (n := n) fun _ => Pack.total V n

variable {V}

/-- **The relation of the numbers is unchanged**: terms are related at the
inductive type of the numbers exactly when they have a common shape. -/
theorem indRel_num_iff {n : Nat} {field : Tm Head 0 → Pack V n} {t t' : Tm Head n} :
    IndRel V (numConstructors V) field t t' ↔
      ∃ s, HasShape V.toSetting V.star t s ∧ HasShape V.toSetting V.star t' s := by
  constructor
  · intro h
    refine IndRel.rec
      (motive_1 := fun t t' _ =>
        ∃ s, HasShape V.toSetting V.star t s ∧ HasShape V.toSetting V.star t' s)
      (motive_2 := fun fs as as' _ => fs = [.recursive] → ∃ a a', as = [a] ∧ as' = [a'] ∧
        ∃ s, HasShape V.toSetting V.star a s ∧ HasShape V.toSetting V.star a' s)
      ?_ ?_ ?_ ?_ ?_ h
    · intro k fs t t' as as' mem red red' fields ih
      rcases List.mem_cons.mp mem with e | mem
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
        cases fields
        exact ⟨.zero, .zero red, .zero red'⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp mem)
        obtain ⟨a, a', rfl, rfl, s, ha, ha'⟩ := ih rfl
        exact ⟨.suc s, .suc red ha, .suc red' ha'⟩
    · intro t t' u u' red daimonic red' daimonic'
      exact ⟨.star, .star red daimonic, .star red' daimonic'⟩
    · intro e
      cases e
    · intro fs t t' as as' _ fields ih _ e
      obtain ⟨-, rfl⟩ := List.cons.inj e
      cases fields
      exact ⟨t, t', rfl, rfl, ih⟩
    · intro F fs t t' as as' _ _ _ e
      cases (List.cons.inj e).1
  · rintro ⟨s, h, h'⟩
    induction h generalizing t' with
    | zero red =>
        cases h' with
        | zero red' => exact .ctor (as := []) (as' := []) (.head _) red red' .nil
    | suc red _ ih =>
        cases h' with
        | suc red' shape' =>
            exact .ctor (as := [_]) (as' := [_]) (.tail _ (.head _)) red red'
              (.recursive (ih shape') .nil)
    | star red daimonic =>
        cases h' with
        | star red' daimonic' => exact .star red daimonic red' daimonic'

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
