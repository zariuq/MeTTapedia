import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Indices

/-!
# Typed expressions as a declared inductive family

The expressions of a small typed language, indexed by their type in a simple inductive type
`ty` with the two constructors `tnum` and `tbool`, declared in the schema of families:

* `exp : ty → U`;
* `lit : num → exp tnum`;
* `add : exp tnum → exp tnum → exp tnum`;
* `ite : Π (t : ty). exp tbool → exp t → exp t → exp t`;
* `iszero : exp tnum → exp tbool`.

Several constructors sit at one index (`lit`, `add` and `ite` at `tnum`); `ite` sits at every
index, and its recursive fields sit at an index that is one of its own fields.

The same language was encoded extrinsically (untyped expressions with a typing computed by
recursion, paired): there, at a variable type `t`, the pair of the untyped literal and a
neutral proof of the computed typing equation is a canonical element of `exp t`
(`TowerSyntaxModel.junk_typed`). The family pack has no such element: at a variable index the
only canonical forms are conditionals whose type field is reducibly equal to the variable
(`canonical_at_variable`), so a literal is not a reducible element there
(`lit_not_reducible_at_variable`). At the closed indices the canonical forms are exactly the
constructors whose target is reducibly equal to the index (`canonical_at_tnum`,
`canonical_at_tbool`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace FamilyExpressions

open Families
open UniverseLevel (LevelOrder)

/-! ## The declaration -/

/-- The types of the language. -/
def ty : DeclName := .mkSimple "ty"
/-- The type of numbers. -/
def tnum : DeclName := .mkSimple "tnum"
/-- The type of Booleans. -/
def tbool : DeclName := .mkSimple "tbool"
/-- The numbers, the type of literals. -/
def num : DeclName := .mkSimple "num"
/-- The family of expressions. -/
def exp : DeclName := .mkSimple "exp"
/-- A numeral. -/
def lit : DeclName := .mkSimple "lit"
/-- Addition. -/
def add : DeclName := .mkSimple "add"
/-- The conditional, at every type. -/
def ite : DeclName := .mkSimple "ite"
/-- The zero test. -/
def iszero : DeclName := .mkSimple "iszero"

theorem tnum_ne_tbool : tnum ≠ tbool := by decide
theorem lit_ne_ite : lit ≠ ite := by decide

/-- The constructors of the types. -/
def tyCtors {Head : Type} : List (DeclName × List (Field Head)) := [(tnum, []), (tbool, [])]

variable {Head L : Type} [LevelOrder L]

/-- `lit : num → exp tnum`. -/
def litTele : CtorTele Head 0 0 := .value (.const num) (.target [.const tnum])

/-- `add : exp tnum → exp tnum → exp tnum`. -/
def addTele : CtorTele Head 0 0 :=
  .recursive [.const tnum] (.recursive [.const tnum] (.target [.const tnum]))

/-- `ite : Π (t : ty). exp tbool → exp t → exp t → exp t`. -/
def iteTele : CtorTele Head 0 0 :=
  .value (.const ty) (.recursive [.const tbool] (.recursive [.var ⟨1, by decide⟩]
    (.recursive [.var ⟨2, by decide⟩] (.target [.var ⟨3, by decide⟩]))))

/-- `iszero : exp tnum → exp tbool`. -/
def iszeroTele : CtorTele Head 0 0 := .recursive [.const tnum] (.target [.const tbool])

/-- Typed expressions in the universe `u`, indexed by their type. -/
def expDecl (u : Head) : FamilyDecl Head where
  name := exp
  params := 0
  paramEntry _ := .head u
  indexTypes := [.const ty]
  sort := u
  ctors := [(lit, litTele), (add, addTele), (ite, iteTele), (iszero, iszeroTele)]

/-! ## The reading -/

section Reading

variable {S : Setting Head L} {n : Nat} {Γ : Ctx Head n} {u : Head}
  {typePack : Tm Head n → Pack Head n}

/-- Expressions read as a family (there are no parameters). -/
abbrev view (S : Setting Head L) (Γ : Ctx Head n) (u : Head)
    (typePack : Tm Head n → Pack Head n) : FamilyAt Head n :=
  (expDecl u).view S Γ typePack []

/-- A canonical form of the reading is one of the four constructors. -/
theorem ctor_cases {c : CtorAt Head n} (mem : c ∈ (view S Γ u typePack).ctors) :
    c = (expDecl u).ctorAt S Γ typePack [] (lit, litTele) ∨
      c = (expDecl u).ctorAt S Γ typePack [] (add, addTele) ∨
      c = (expDecl u).ctorAt S Γ typePack [] (ite, iteTele) ∨
      c = (expDecl u).ctorAt S Γ typePack [] (iszero, iszeroTele) := by
  obtain ⟨entry, entryMem, rfl⟩ := List.mem_map.mp mem
  rcases List.mem_cons.mp entryMem with rfl | entryMem
  · exact .inl rfl
  rcases List.mem_cons.mp entryMem with rfl | entryMem
  · exact .inr (.inl rfl)
  rcases List.mem_cons.mp entryMem with rfl | entryMem
  · exact .inr (.inr (.inl rfl))
  obtain rfl := List.mem_singleton.mp entryMem
  exact .inr (.inr (.inr rfl))

/-- A canonical form stores no parameters. -/
theorem form_spine {k : DeclName} {tele : CtorTele Head 0 0} {nf : Tm Head n}
    {fs : List (Tm Head n)} (form : ((expDecl u).ctorAt S Γ typePack [] (k, tele)).form nf fs) :
    nf = appSpine (.const k) fs := by
  obtain ⟨ps', rfl, len, _⟩ := form
  have hps : ps' = [] := List.length_eq_zero_iff.mp len
  subst hps
  rfl

theorem lit_fields {fs : List (Tm Head n)}
    (fields : FamFields S Γ (view S Γ u typePack) fs (litTele.fieldsAt typePack []) fs) :
    ∃ k, fs = [k] := by
  cases fields with
  | value _ tail =>
      cases tail
      exact ⟨_, rfl⟩

theorem add_fields {fs : List (Tm Head n)}
    (fields : FamFields S Γ (view S Γ u typePack) fs (addTele.fieldsAt typePack []) fs) :
    ∃ x y, fs = [x, y] := by
  cases fields with
  | recursive _ tail =>
      cases tail with
      | recursive _ tail =>
          cases tail
          exact ⟨_, _, rfl⟩

theorem ite_fields {fs : List (Tm Head n)}
    (fields : FamFields S Γ (view S Γ u typePack) fs (iteTele.fieldsAt typePack []) fs) :
    ∃ t c x y, fs = [t, c, x, y] := by
  cases fields with
  | value _ tail =>
      cases tail with
      | recursive _ tail =>
          cases tail with
          | recursive _ tail =>
              cases tail with
              | recursive _ tail =>
                  cases tail
                  exact ⟨_, _, _, _, rfl⟩

theorem iszero_fields {fs : List (Tm Head n)}
    (fields : FamFields S Γ (view S Γ u typePack) fs (iszeroTele.fieldsAt typePack []) fs) :
    ∃ x, fs = [x] := by
  cases fields with
  | recursive _ tail =>
      cases tail
      exact ⟨_, rfl⟩

end Reading

/-! ## Canonical forms at an index -/

section Canonical

variable {S : Setting Head L} {n : Nat} {Γ : Ctx Head n} {u : Head}
  {typePack : Tm Head n → Pack Head n} {fp : Tm Head 0 → Pack Head n}
  (hTy : typePack (.const ty) = indPack S Γ ty tyCtors fp)
  (hTnum : S.roles tnum = .constructor 0) (hTbool : S.roles tbool = .constructor 0)
include hTy hTnum hTbool

/-- **At a variable type the canonical forms are the conditionals at that type**: every other
normal form is neutral, and the type field of a canonical conditional is reducibly equal to
the variable. -/
theorem canonical_at_variable {j : Fin n} {nf : Tm Head n}
    (normal : FamNf S Γ (view S Γ u typePack) [.var j] nf) :
    (∃ t c x y, nf = appSpine (.const ite) [t, c, x, y] ∧
      (indPack S Γ ty tyCtors fp).eqTm (.var j) t) ∨ Neutral S.roles nf := by
  cases normal with
  | neutral nNf _ => exact .inr nNf
  | ctor mem form fields agree =>
      rcases ctor_cases mem with rfl | rfl | rfl | rfl <;> have hform := form_spine form
      · obtain ⟨k, rfl⟩ := lit_fields fields
        change IndexAgree [typePack (.const ty)] [.var j] [.const tnum] at agree
        rw [hTy] at agree
        cases agree with
        | cons head _ => exact absurd head (not_varEq_ctor (args := []) hTnum j)
      · obtain ⟨x, y, rfl⟩ := add_fields fields
        change IndexAgree [typePack (.const ty)] [.var j] [.const tnum] at agree
        rw [hTy] at agree
        cases agree with
        | cons head _ => exact absurd head (not_varEq_ctor (args := []) hTnum j)
      · obtain ⟨t, c, x, y, rfl⟩ := ite_fields fields
        change IndexAgree [typePack (.const ty)] [.var j] [t] at agree
        rw [hTy] at agree
        cases agree with
        | cons head _ => exact .inl ⟨t, c, x, y, hform, head⟩
      · obtain ⟨x, rfl⟩ := iszero_fields fields
        change IndexAgree [typePack (.const ty)] [.var j] [.const tbool] at agree
        rw [hTy] at agree
        cases agree with
        | cons head _ => exact absurd head (not_varEq_ctor (args := []) hTbool j)

/-- **A literal is not a reducible expression at a variable type**, though the extrinsic
encoding has the literal, paired with a neutral typing proof, there. -/
theorem lit_not_reducible_at_variable (hLit : S.roles lit = .constructor 1) {j : Fin n}
    (k : Tm Head n) :
    ¬ FamRedTm S Γ (view S Γ u typePack) [.var j] (appSpine (.const lit) [k]) := by
  rintro ⟨red, _, normal⟩
  have e := whnf_reduct_eq (ctorSpine_rigid hLit [k]).1 red.red
  subst e
  rcases canonical_at_variable hTy hTnum hTbool normal with ⟨t, c, x, y, e, _⟩ | nNf
  · exact lit_ne_ite (appSpine_const_injective e).1
  · exact (ctorSpine_rigid hLit [k]).2 nNf

/-- **At the type `tnum` the canonical forms are exactly** literals, sums, and conditionals
whose type field is reducibly equal to `tnum`; zero tests are excluded. -/
theorem canonical_at_tnum {nf : Tm Head n}
    (normal : FamNf S Γ (view S Γ u typePack) [.const tnum] nf) :
    (∃ k, nf = appSpine (.const lit) [k]) ∨ (∃ x y, nf = appSpine (.const add) [x, y]) ∨
      (∃ t c x y, nf = appSpine (.const ite) [t, c, x, y] ∧
        (indPack S Γ ty tyCtors fp).eqTm (.const tnum) t) ∨ Neutral S.roles nf := by
  cases normal with
  | neutral nNf _ => exact .inr (.inr (.inr nNf))
  | ctor mem form fields agree =>
      rcases ctor_cases mem with rfl | rfl | rfl | rfl <;> have hform := form_spine form
      · obtain ⟨k, rfl⟩ := lit_fields fields
        exact .inl ⟨k, hform⟩
      · obtain ⟨x, y, rfl⟩ := add_fields fields
        exact .inr (.inl ⟨x, y, hform⟩)
      · obtain ⟨t, c, x, y, rfl⟩ := ite_fields fields
        change IndexAgree [typePack (.const ty)] [.const tnum] [t] at agree
        rw [hTy] at agree
        cases agree with
        | cons head _ => exact .inr (.inr (.inl ⟨t, c, x, y, hform, head⟩))
      · obtain ⟨x, rfl⟩ := iszero_fields fields
        change IndexAgree [typePack (.const ty)] [.const tnum] [.const tbool] at agree
        rw [hTy] at agree
        cases agree with
        | cons head _ =>
            exact absurd head (not_ctorEq_ctor (args := []) (args' := []) hTnum hTbool tnum_ne_tbool)

/-- **At the type `tbool` the canonical forms are exactly** zero tests and conditionals whose
type field is reducibly equal to `tbool`; literals and sums are excluded. -/
theorem canonical_at_tbool {nf : Tm Head n}
    (normal : FamNf S Γ (view S Γ u typePack) [.const tbool] nf) :
    (∃ x, nf = appSpine (.const iszero) [x]) ∨
      (∃ t c x y, nf = appSpine (.const ite) [t, c, x, y] ∧
        (indPack S Γ ty tyCtors fp).eqTm (.const tbool) t) ∨ Neutral S.roles nf := by
  cases normal with
  | neutral nNf _ => exact .inr (.inr nNf)
  | ctor mem form fields agree =>
      rcases ctor_cases mem with rfl | rfl | rfl | rfl <;> have hform := form_spine form
      · obtain ⟨k, rfl⟩ := lit_fields fields
        change IndexAgree [typePack (.const ty)] [.const tbool] [.const tnum] at agree
        rw [hTy] at agree
        cases agree with
        | cons head _ =>
            exact absurd head (not_ctorEq_ctor (args := []) (args' := []) hTbool hTnum
              (Ne.symm tnum_ne_tbool))
      · obtain ⟨x, y, rfl⟩ := add_fields fields
        change IndexAgree [typePack (.const ty)] [.const tbool] [.const tnum] at agree
        rw [hTy] at agree
        cases agree with
        | cons head _ =>
            exact absurd head (not_ctorEq_ctor (args := []) (args' := []) hTbool hTnum
              (Ne.symm tnum_ne_tbool))
      · obtain ⟨t, c, x, y, rfl⟩ := ite_fields fields
        change IndexAgree [typePack (.const ty)] [.const tbool] [t] at agree
        rw [hTy] at agree
        cases agree with
        | cons head _ => exact .inr (.inl ⟨t, c, x, y, hform, head⟩)
      · obtain ⟨x, rfl⟩ := iszero_fields fields
        exact .inl ⟨x, hform⟩

end Canonical

/-! ## Elements -/

section Elements

variable {S : Setting Head L} {n : Nat} {Γ : Ctx Head n} {u : Head}
  {typePack : Tm Head n → Pack Head n}

/-- A conditional at a variable type is canonical there, once its fields are reducible and
the variable is reducibly equal to itself: the constructor at every index is admitted at a
variable index. -/
theorem ite_canonical_at_variable {j : Fin n} {c x y : Tm Head n}
    (tyField : (typePack (.const ty)).redTm (.var j))
    (cond : FamRedTm S Γ (view S Γ u typePack) [.const tbool] c)
    (thenBranch : FamRedTm S Γ (view S Γ u typePack) [.var j] x)
    (elseBranch : FamRedTm S Γ (view S Γ u typePack) [.var j] y)
    (self : (typePack (.const ty)).eqTm (.var j) (.var j)) :
    FamNf S Γ (view S Γ u typePack) [.var j] (appSpine (.const ite) [.var j, c, x, y]) :=
  .ctor (List.mem_map_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
    ⟨[], rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    (.value tyField (.recursive cond (.recursive thenBranch (.recursive elseBranch .nil))))
    (.cons self .nil)

/-- A literal is canonical at `tnum` once its field is reducible and `tnum` is reducibly
equal to itself. -/
theorem lit_canonical_at_tnum {k : Tm Head n} (numField : (typePack (.const num)).redTm k)
    (self : (typePack (.const ty)).eqTm (.const tnum) (.const tnum)) :
    FamNf S Γ (view S Γ u typePack) [.const tnum] (appSpine (.const lit) [k]) :=
  .ctor (List.mem_map_of_mem (List.mem_cons_self ..))
    ⟨[], rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩ (.value numField .nil)
    (.cons self .nil)

/-- **A variable of an expression type is a reducible neutral expression**, at any type. -/
theorem variable_reducible (laws : S.E.Laws S.R S.roles) {typePack' : Tm Head (n + 1) → Pack Head (n + 1)}
    (t : Tm Head n) :
    FamRedTm S (.snoc Γ (appSpine (.const exp) [t]))
      (view S (.snoc Γ (appSpine (.const exp) [t])) u typePack') [Presentation.rename wk t]
      (.var 0) := by
  have typing : Typed S.R (.snoc Γ (appSpine (.const exp) [t])) (.var 0)
      (appSpine (.const exp) [Presentation.rename wk t]) := by
    have h : Typed S.R (.snoc Γ (appSpine (.const exp) [t])) (.var 0)
        (Ctx.lookup (.snoc Γ (appSpine (.const exp) [t])) 0) := .var 0
    have e : Ctx.lookup (.snoc Γ (appSpine (.const exp) [t])) 0 =
        appSpine (.const exp) [Presentation.rename wk t] := by
      show Presentation.rename wk (appSpine (.const exp) [t]) = _
      rw [rename_appSpine]
      rfl
    rw [e] at h
    exact h
  exact FamRedTm.of_neutral laws (.var 0) typing (laws.convNe_var 0 typing)

end Elements

end FamilyExpressions
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
