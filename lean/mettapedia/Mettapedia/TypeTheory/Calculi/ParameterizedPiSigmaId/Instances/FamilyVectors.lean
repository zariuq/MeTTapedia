import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Indices

/-!
# Vectors as a declared inductive family

Vectors over a type `A` of a universe `u`, indexed by their length in a simple inductive type
of numbers with constructors `zero` and `succ`, declared in the schema of families:

* `vec : Π (A : U). num → U`;
* `vnil : Π (A : U). vec A zero`;
* `vcons : Π (A : U) (m : num) (x : A) (xs : vec A m). vec A (succ m)`.

The parameter `A` is a type; the recursive field `xs` sits at the index `m`, an earlier field;
the target `succ m` is computed from the fields.

Read at the parameter `A` in any setting where the numbers are a simple inductive type and the
constructors are declared as constructors, the family pack separates vectors from encodings:

* at the length `zero` the canonical forms are exactly `vnil A'` with `A'` convertible to `A`
  (`canonical_at_zero`);
* at the length `succ i` they are exactly `vcons A' m x xs` with `m` reducibly equal to `i`
  (`canonical_at_succ`);
* at a variable length there is no canonical form at all, only neutral terms
  (`neutral_at_variable`), while a variable of a vector type is a reducible neutral element
  (`variable_reducible`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace FamilyVectors

open Families
open UniverseLevel (LevelOrder)

/-! ## The declaration -/

/-- The family of vectors. -/
def vec : DeclName := .mkSimple "vec"
/-- The empty vector. -/
def vnil : DeclName := .mkSimple "vnil"
/-- Extending a vector. -/
def vcons : DeclName := .mkSimple "vcons"
/-- The numbers, the index type. -/
def num : DeclName := .mkSimple "num"
/-- The number zero. -/
def zero : DeclName := .mkSimple "zero"
/-- The successor. -/
def succ : DeclName := .mkSimple "succ"

theorem zero_ne_succ : zero ≠ succ := by decide
theorem vnil_ne_vcons : vnil ≠ vcons := by decide

/-- The constructors of the numbers. -/
def numCtors {Head : Type} : List (DeclName × List (Field Head)) :=
  [(zero, []), (succ, [.recursive])]

variable {Head L : Type} [LevelOrder L]

/-- `vnil : Π (A : U). vec A zero`: no fields. -/
def vnilTele : CtorTele Head 1 0 := .target [.const zero]

/-- `vcons : Π (A : U) (m : num) (x : A) (xs : vec A m). vec A (succ m)`. -/
def vconsTele : CtorTele Head 1 0 :=
  .value (.const num) (.value (.var 0)
    (.recursive [.var ⟨1, by decide⟩] (.target [.app (.const succ) (.var ⟨2, by decide⟩)])))

/-- Vectors over a type of the universe `u`, indexed by their length. -/
def vecDecl (u : Head) : FamilyDecl Head where
  name := vec
  params := 1
  paramEntry _ := .head u
  indexTypes := [.const num]
  sort := u
  ctors := [(vnil, vnilTele), (vcons, vconsTele)]

/-! ## The reading at a parameter -/

section Reading

variable {S : Setting Head L} {n : Nat} {Γ : Ctx Head n} {u : Head}
  {typePack : Tm Head n → Pack Head n} {A : Tm Head n}

/-- Vectors read at the parameter `A`. -/
abbrev view (S : Setting Head L) (Γ : Ctx Head n) (u : Head) (typePack : Tm Head n → Pack Head n)
    (A : Tm Head n) : FamilyAt Head n :=
  (vecDecl u).view S Γ typePack [A]

theorem view_type (is : List (Tm Head n)) :
    (view S Γ u typePack A).type is = appSpine (.const vec) (A :: is) := rfl

theorem view_indexPacks :
    (view S Γ u typePack A).indexPacks = [typePack (.const num)] := rfl

/-- The target of `vcons` at its fields is `succ m`. -/
theorem vcons_target (m x xs : Tm Head n) :
    vconsTele.targetAt [A] [m, x, xs] = [.app (.const succ) m] := rfl

/-- The stored parameter of a canonical form is convertible to `A`. -/
theorem paramsConv_iff {A' : Tm Head n} :
    (vecDecl u).ParamsConv S Γ [A] [A'] ↔ S.E.convTm Γ A' A (.head u) := by
  constructor
  · rintro ⟨_, h⟩
    exact h 0 Nat.one_pos
  · intro h
    refine ⟨rfl, fun j hj => ?_⟩
    have hj' : j < 1 := hj
    obtain rfl : j = 0 := by omega
    exact h

/-- A canonical form of the reading is a constructor of the declaration. -/
theorem ctor_cases {c : CtorAt Head n} (mem : c ∈ (view S Γ u typePack A).ctors) :
    c = (vecDecl u).ctorAt S Γ typePack [A] (vnil, vnilTele) ∨
      c = (vecDecl u).ctorAt S Γ typePack [A] (vcons, vconsTele) := by
  obtain ⟨entry, entryMem, rfl⟩ := List.mem_map.mp mem
  rcases List.mem_cons.mp entryMem with rfl | entryMem
  · exact .inl rfl
  · obtain rfl := List.mem_singleton.mp entryMem
    exact .inr rfl

end Reading

/-! ## Canonical forms at an index -/

section Canonical

variable {S : Setting Head L} {n : Nat} {Γ : Ctx Head n} {u : Head}
  {typePack : Tm Head n → Pack Head n} {A : Tm Head n} {fp : Tm Head 0 → Pack Head n}

/-- The packs at a canonical `vcons` form: its fields are a number, an element and a vector. -/
theorem vcons_fields {fs : List (Tm Head n)}
    (fields : FamFields S Γ (view S Γ u typePack A) fs (vconsTele.fieldsAt typePack [A]) fs) :
    ∃ m x xs, fs = [m, x, xs] := by
  cases fields with
  | value _ tail =>
      cases tail with
      | value _ tail =>
          cases tail with
          | recursive _ tail =>
              cases tail
              exact ⟨_, _, _, rfl⟩

variable (hNum : typePack (.const num) = indPack S Γ num numCtors fp)
  (hZero : S.roles zero = .constructor 0) (hSucc : S.roles succ = .constructor 1)
include hNum hZero hSucc

/-- **At the length `zero` the canonical forms are exactly the empty vectors**, with stored
parameter convertible to `A`; every other normal form is neutral. -/
theorem canonical_at_zero {nf : Tm Head n}
    (normal : FamNf S Γ (view S Γ u typePack A) [.const zero] nf) :
    (∃ A', nf = appSpine (.const vnil) [A'] ∧ S.E.convTm Γ A' A (.head u)) ∨
      Neutral S.roles nf := by
  cases normal with
  | neutral nNf _ => exact .inr nNf
  | ctor mem form fields agree =>
      rcases ctor_cases mem with rfl | rfl
      · obtain ⟨ps', rfl, conv⟩ := form
        cases fields
        obtain ⟨A', rfl⟩ := List.length_eq_one_iff.mp conv.1
        exact .inl ⟨A', rfl, paramsConv_iff.mp conv⟩
      · obtain ⟨m, x, xs, rfl⟩ := vcons_fields fields
        change IndexAgree [typePack (.const num)] [.const zero] [.app (.const succ) m] at agree
        rw [hNum] at agree
        cases agree with
        | cons head _ =>
            exact absurd head (not_ctorEq_ctor (args := []) (args' := [m]) hZero hSucc zero_ne_succ)

/-- **At the length `succ i` the canonical forms are exactly the extensions** `vcons A' m x xs`
whose stored parameter is convertible to `A` and whose length `m` is reducibly equal to `i`;
every other normal form is neutral. -/
theorem canonical_at_succ {i nf : Tm Head n}
    (normal : FamNf S Γ (view S Γ u typePack A) [.app (.const succ) i] nf) :
    (∃ A' m x xs, nf = appSpine (.const vcons) [A', m, x, xs] ∧ S.E.convTm Γ A' A (.head u) ∧
      (indPack S Γ num numCtors fp).eqTm i m) ∨ Neutral S.roles nf := by
  cases normal with
  | neutral nNf _ => exact .inr nNf
  | ctor mem form fields agree =>
      rcases ctor_cases mem with rfl | rfl
      · cases fields
        change IndexAgree [typePack (.const num)] [.app (.const succ) i] [.const zero] at agree
        rw [hNum] at agree
        cases agree with
        | cons head _ =>
            exact absurd head (not_ctorEq_ctor (args := [i]) (args' := []) hSucc hZero
              (Ne.symm zero_ne_succ))
      · obtain ⟨m, x, xs, rfl⟩ := vcons_fields fields
        obtain ⟨ps', rfl, conv⟩ := form
        obtain ⟨A', rfl⟩ := List.length_eq_one_iff.mp conv.1
        change IndexAgree [typePack (.const num)] [.app (.const succ) i] [.app (.const succ) m]
          at agree
        rw [hNum] at agree
        cases agree with
        | cons head _ =>
            obtain ⟨_, fields', mem', eqFields⟩ :=
              ctorEq_inv (args := [i]) (args' := [m]) hSucc hSucc head
            have hfields : fields' = [.recursive] := by
              rcases List.mem_cons.mp mem' with h | h
              · exact absurd (congrArg Prod.fst h) (Ne.symm zero_ne_succ)
              · exact (Prod.mk.inj (List.mem_singleton.mp h)).2
            subst hfields
            cases eqFields with
            | recursive head' _ =>
                exact .inl ⟨A', m, x, xs, rfl, paramsConv_iff.mp conv, head'⟩

/-- **At a variable length there is no canonical vector**: every reducible normal form is
neutral. An encoding of vectors by lists with a length proof has the canonical element
`(nil, p)` there, with a neutral proof `p : length nil = n`. -/
theorem neutral_at_variable {j : Fin n} {nf : Tm Head n}
    (normal : FamNf S Γ (view S Γ u typePack A) [.var j] nf) : Neutral S.roles nf := by
  cases normal with
  | neutral nNf _ => exact nNf
  | ctor mem form fields agree =>
      rcases ctor_cases mem with rfl | rfl
      · cases fields
        change IndexAgree [typePack (.const num)] [.var j] [.const zero] at agree
        rw [hNum] at agree
        cases agree with
        | cons head _ => exact absurd head (not_varEq_ctor (args := []) hZero j)
      · obtain ⟨m, x, xs, rfl⟩ := vcons_fields fields
        change IndexAgree [typePack (.const num)] [.var j] [.app (.const succ) m] at agree
        rw [hNum] at agree
        cases agree with
        | cons head _ => exact absurd head (not_varEq_ctor (args := [m]) hSucc j)

end Canonical

/-! ## Elements -/

section Elements

variable {S : Setting Head L} {n : Nat} {Γ : Ctx Head n} {u : Head}
  {typePack : Tm Head (n + 1) → Pack Head (n + 1)}

/-- **A variable of a vector type is a reducible neutral vector**, at any length. -/
theorem variable_reducible (laws : S.E.Laws S.R S.roles) (A len : Tm Head n) :
    FamRedTm S (.snoc Γ (appSpine (.const vec) [A, len]))
      (view S (.snoc Γ (appSpine (.const vec) [A, len])) u typePack (Presentation.rename wk A))
      [Presentation.rename wk len] (.var 0) := by
  have typing : Typed S.R (.snoc Γ (appSpine (.const vec) [A, len])) (.var 0)
      (appSpine (.const vec) [Presentation.rename wk A, Presentation.rename wk len]) := by
    have h : Typed S.R (.snoc Γ (appSpine (.const vec) [A, len])) (.var 0)
        (Ctx.lookup (.snoc Γ (appSpine (.const vec) [A, len])) 0) := .var 0
    have e : Ctx.lookup (.snoc Γ (appSpine (.const vec) [A, len])) 0 =
        appSpine (.const vec) [Presentation.rename wk A, Presentation.rename wk len] := by
      show Presentation.rename wk (appSpine (.const vec) [A, len]) = _
      rw [rename_appSpine]
      rfl
    rw [e] at h
    exact h
  exact FamRedTm.of_neutral laws (.var 0) typing (laws.convNe_var 0 typing)

/-- The empty vector is canonical at the length `zero`, once its stored parameter is
convertible to `A` and `zero` is reducibly equal to itself. -/
theorem vnil_canonical {S : Setting Head L} {n : Nat} {Γ : Ctx Head n}
    {typePack : Tm Head n → Pack Head n} {A A' : Tm Head n}
    (conv : S.E.convTm Γ A' A (.head u))
    (zeroRefl : (typePack (.const num)).eqTm (.const zero) (.const zero)) :
    FamNf S Γ (view S Γ u typePack A) [.const zero] (appSpine (.const vnil) [A']) :=
  .ctor (List.mem_map_of_mem (List.mem_cons_self ..)) ⟨[A'], rfl, paramsConv_iff.mpr conv⟩ .nil
    (.cons zeroRefl .nil)

/-- An extension is canonical at the length `succ i` once its fields are reducible, its stored
parameter is convertible to `A`, and `succ i` is reducibly equal to `succ m`. -/
theorem vcons_canonical {S : Setting Head L} {n : Nat} {Γ : Ctx Head n}
    {typePack : Tm Head n → Pack Head n} {A A' i m x xs : Tm Head n}
    (conv : S.E.convTm Γ A' A (.head u))
    (numField : (typePack (.const num)).redTm m) (elemField : (typePack A).redTm x)
    (tail : FamRedTm S Γ (view S Γ u typePack A) [m] xs)
    (lengths : (typePack (.const num)).eqTm (.app (.const succ) i) (.app (.const succ) m)) :
    FamNf S Γ (view S Γ u typePack A) [.app (.const succ) i]
      (appSpine (.const vcons) [A', m, x, xs]) :=
  .ctor (List.mem_map_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    ⟨[A'], rfl, paramsConv_iff.mpr conv⟩ (.value numField (.value elemField (.recursive tail .nil)))
    (.cons lengths .nil)

end Elements

end FamilyVectors
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
