import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.GradedIdentity.Typed

/-!
# Binary numbers as declared datatypes, with their value in the naturals

The numbers of the object package are unary: `zero`, `suc`. This module declares binary
numbers over the object package as ordinary datatypes and defines their arithmetic by written
equations, so that nothing about them is trusted: every operation is a declared constant that
computes by its equations, and the package with all of them has a set model.

**The datatypes**, admitted by the criterion for datatypes (`posDecl_admissible`,
`natDecl_admissible`):

* `pos`, the positive numbers: `one`, and `bit0 p` (twice `p`) and `bit1 p` (twice `p` and
  one), the last digit written outermost;
* `nat`, the natural numbers: `n0`, and `npos p` for a positive `p`.

**The operations** (`binaryProgram`), each a definition by cases on its first argument, one
constructor deep, recursing only on a field of it, so each is a definition by structural
recursion of the declaration lists (or an explicit one); where a second argument must be
inspected, a helper does it:

* `psucc`, the successor; `phalf` and `nhalf`, half a number rounded down;
* `padd-nat p m`, the sum of a positive and a natural number, from the sum with half of `m`
  and the last digit of `m`: `padd-nat (bit0 p) m ⟶ low0 m (padd-nat p (nhalf m))` and
  `padd-nat (bit1 p) m ⟶ low1 m (padd-nat p (nhalf m))`, where `low0 m r` writes the last
  digit of `m` after `r` and `low1 m r` does the same with a carry (`low0-pos`, `low1-pos` read
  the digit of a positive number, `nsucc-pos` is the successor of a natural number);
* `padd p q ⟶ padd-nat p (npos q)`, and `pmul`, the product: `pmul one q ⟶ q`,
  `pmul (bit0 p) q ⟶ bit0 (pmul p q)`, `pmul (bit1 p) q ⟶ padd q (bit0 (pmul p q))`;
* `pval` and `nval`, the value maps into the numbers of the object package:
  `pval (bit0 p) ⟶ add (pval p) (pval p)` and `pval (bit1 p) ⟶ suc (add (pval p) (pval p))`.

These are the declarations of the same names in the C draft's fixture
`tests/prime/trinity/arith.binary.metta`, with the same equations; there the C checker admits
each by structural recursion, as here.

**Admissible, with a set model.** The list is admissible over the object package
(`binaryProgram_admissible`), so the package has a set model and is consistent, relative to
`CofinalInaccessibles` (`binary_model`, `binary_consistent`).

**The equations are typed computation rules.** Each written equation holds in the judgment of
the package at typed arguments (`psuccBit1_rule`, `paddNatBit0_rule`, `pmulBit1_rule`, ...,
thirty-two in all), from the general theorem for the equations of a declared definition.

**The value map is a homomorphism.** In the set model, by induction on the set of positive
numbers (`pos_induct`, from the reading of the datatype as the least set closed under its
constructors), the value of a sum is the sum of the values, by the object package's addition
(`padd_value`, through `paddNat_value` with its carry), and the value of a product is the
product of the values (`pmul_value`). At closed terms of the judgment the same holds of their
values (`padd_value_closed`, `pmul_value_closed`).

Positive example: the value of `6 + 7`, written `bit0 (bit1 one)` and `bit1 (bit1 one)`, is
`13` (`six_plus_seven`). Negative example: `one` is a positive number and not a natural
number; `n0` and `npos one` are the natural numbers zero and one (`one_not_nat`). The carry is
needed: with `low1-pos one r ⟶ bit1 r` in place of `bit0 (psucc r)`, `3 + 1` would compute to
`3`, the value of the carry (`low1Pos_value`) would be `2r + 1` where `2r + 2` is stated, and
with it the sum would not be a homomorphism.

**The rewriting-level counterpart** is `Mettapedia.GSLT.LanguageDef.WaltersZantemaDA`: the
digit-application arithmetic of Walters and Zantema, a premise-free language definition for
every radix, whose terms are rewritten to canonical numerals. At radix two its canonical
numerals are the empty numeral and the digit strings whose first digit is `1`; they correspond
one to one to the natural numbers here: the empty numeral to `n0`, the digit `1` after the
empty numeral to `one`, and a digit `0` or `1` after a numeral to `bit0` or `bit1`. There the
absence of leading zeros is reached by a rule; here it holds by the types, since a positive
number has no zero. Nothing of that module is restated here.

Not here: the integers, the fractions, and division and the greatest common divisor of the C
fixture. The last two are admitted there by a bound on their calls, which the declaration
lists do not state; and the associativity of the binary sum is not proved in the judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Arith.Binary

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram
open ExecutableModel ExecutableModel.CodeModel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.GradedIdentity.Typed
  (tNum tZero tSuc tAdd tPi uSort)

/-! ## The names -/

/-- The type of the positive binary numbers. -/
def posN : DeclName := .str .anonymous "pos"
/-- The positive number one. -/
def oneN : DeclName := .str .anonymous "one"
/-- Twice a positive number: a digit `0` written after it. -/
def bit0N : DeclName := .str .anonymous "bit0"
/-- Twice a positive number and one: a digit `1` written after it. -/
def bit1N : DeclName := .str .anonymous "bit1"
/-- The recursor of the positive numbers. -/
def posRecN : DeclName := .str .anonymous "pos-rec"
/-- The type of the binary natural numbers. -/
def natN : DeclName := .str .anonymous "nat"
/-- The natural number zero. -/
def n0N : DeclName := .str .anonymous "n0"
/-- A positive number as a natural number. -/
def nposN : DeclName := .str .anonymous "npos"
/-- The recursor of the natural numbers. -/
def natRecN : DeclName := .str .anonymous "nat-rec"
/-- The successor of a positive number. -/
def psuccN : DeclName := .str .anonymous "psucc"
/-- Half a positive number, rounded down, as a natural number. -/
def phalfN : DeclName := .str .anonymous "phalf"
/-- Half a natural number, rounded down. -/
def nhalfN : DeclName := .str .anonymous "nhalf"
/-- The successor of a natural number, as a positive number. -/
def nsuccPosN : DeclName := .str .anonymous "nsucc-pos"
/-- A digit `0` or `1` after a positive number, the digit being the last digit of another. -/
def low0PosN : DeclName := .str .anonymous "low0-pos"
/-- The same, the last digit read from a natural number. -/
def low0N : DeclName := .str .anonymous "low0"
/-- The digit and a carry after a positive number, the last digit read from another. -/
def low1PosN : DeclName := .str .anonymous "low1-pos"
/-- The same, the last digit read from a natural number. -/
def low1N : DeclName := .str .anonymous "low1"
/-- The sum of a positive and a natural number. -/
def paddNatN : DeclName := .str .anonymous "padd-nat"
/-- The sum of two positive numbers. -/
def paddN : DeclName := .str .anonymous "padd"
/-- The product of two positive numbers. -/
def pmulN : DeclName := .str .anonymous "pmul"
/-- The value of a positive number in the numbers of the object package. -/
def pvalN : DeclName := .str .anonymous "pval"
/-- The value of a natural number in the numbers of the object package. -/
def nvalN : DeclName := .str .anonymous "nval"

section Terms

variable {n : Nat}

abbrev cpos : CTm Tower.Head n := .const posN
abbrev cnat : CTm Tower.Head n := .const natN
abbrev pone : CTm Tower.Head n := .const oneN
abbrev pbit0 (p : CTm Tower.Head n) : CTm Tower.Head n := .app (.const bit0N) p
abbrev pbit1 (p : CTm Tower.Head n) : CTm Tower.Head n := .app (.const bit1N) p
abbrev nzero : CTm Tower.Head n := .const n0N
abbrev npos (p : CTm Tower.Head n) : CTm Tower.Head n := .app (.const nposN) p
abbrev call1 (f : DeclName) (a : CTm Tower.Head n) : CTm Tower.Head n := .app (.const f) a
abbrev call2 (f : DeclName) (a b : CTm Tower.Head n) : CTm Tower.Head n :=
  .app (.app (.const f) a) b

end Terms

/-! ## The datatypes -/

/-- The constructors of the positive numbers: one, and a digit `0` or `1` after a number. -/
def posCtors : List (DeclName × List CtorField) :=
  [(oneN, []), (bit0N, [.recursive]), (bit1N, [.recursive])]

/-- The constructors of the natural numbers: zero, and a positive number. -/
def natCtors : List (DeclName × List CtorField) :=
  [(n0N, []), (nposN, [.closed (.const posN)])]

/-- **The positive binary numbers**, `one`, `bit0 p` and `bit1 p`. -/
def posDecl : Datatype Tower.Head where
  type := posN
  typeUniverse := .sort Tower.zero
  ctors := posCtors
  recursor := posRecN
  motiveUniverse := listMotives

/-- **The binary natural numbers**, `n0` and `npos p`. -/
def natDecl : Datatype Tower.Head where
  type := natN
  typeUniverse := .sort Tower.zero
  ctors := natCtors
  recursor := natRecN
  motiveUniverse := listMotives

/-- The three constructors of the positive numbers. -/
theorem posCtors_entry {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : posCtors[i]? = some (k, fields)) :
    (k = oneN ∧ fields = []) ∨ (k = bit0N ∧ fields = [.recursive]) ∨
      (k = bit1N ∧ fields = [.recursive]) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨same, sameFields⟩ := Prod.mk.inj (Option.some.inj entry)
    exact .inl ⟨same.symm, sameFields.symm⟩
  | 1, entry =>
    obtain ⟨same, sameFields⟩ := Prod.mk.inj (Option.some.inj entry)
    exact .inr (.inl ⟨same.symm, sameFields.symm⟩)
  | 2, entry =>
    obtain ⟨same, sameFields⟩ := Prod.mk.inj (Option.some.inj entry)
    exact .inr (.inr ⟨same.symm, sameFields.symm⟩)
  | i + 3, entry => exact nomatch entry

/-- The two constructors of the natural numbers. -/
theorem natCtors_entry {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : natCtors[i]? = some (k, fields)) :
    (k = n0N ∧ fields = []) ∨ (k = nposN ∧ fields = [.closed (.const posN)]) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨same, sameFields⟩ := Prod.mk.inj (Option.some.inj entry)
    exact .inl ⟨same.symm, sameFields.symm⟩
  | 1, entry =>
    obtain ⟨same, sameFields⟩ := Prod.mk.inj (Option.some.inj entry)
    exact .inr ⟨same.symm, sameFields.symm⟩
  | i + 2, entry => exact nomatch entry

theorem posDecl_admissible : posDecl.Admissible objectChurch where
  typeUniverse := LevelTower.IsUniverse.sort _
  motiveUniverse := LevelTower.IsUniverse.sort _
  distinct := ⟨by decide, by decide, by decide, by decide⟩
  new := ⟨by decide, by decide, by decide⟩
  lamFree := by
    intro entry member F field
    simp only [posDecl, posCtors, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp at field
  fields := by
    intro entry member F field
    simp only [posDecl, posCtors, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp at field

abbrev stage1 : List (Declaration Tower.Head) := [.datatype posDecl]

theorem stage1_admissible : AdmissibleDeclarations objectChurch stage1 :=
  ⟨trivial, posDecl_admissible⟩

theorem natDecl_admissible : natDecl.Admissible (withDeclarations objectChurch stage1) where
  typeUniverse := LevelTower.IsUniverse.sort _
  motiveUniverse := LevelTower.IsUniverse.sort _
  distinct := ⟨by decide, by decide, by decide, by decide⟩
  new := ⟨by decide, by decide, by decide⟩
  lamFree := by
    intro entry member F field
    simp only [natDecl, natCtors, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp at field
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
      obtain rfl : F = .const posN := by injection field
      rfl
  fields := by
    intro entry member F field
    simp only [natDecl, natCtors, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp at field
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
      obtain rfl : F = .const posN := by injection field
      exact stage1_admissible.type_typed ConvRules.objectLevels List.mem_cons_self

abbrev stage2 : List (Declaration Tower.Head) := .datatype natDecl :: stage1

theorem stage2_admissible : AdmissibleDeclarations objectChurch stage2 :=
  ⟨stage1_admissible, natDecl_admissible⟩

/-! ## The definitions -/

/-- The right sides of a definition by recursion on a positive number with no later
argument, from the right side at one, at `bit0 p` and at `bit1 p` (over `p` and the value at
`p`). -/
def posBody1 (atOne : CTm Tower.Head 0) (at0 at1 : CTm Tower.Head 2) :
    (k : DeclName) → (fields : List CtorField) →
      CTm Tower.Head ((CTele.nil : CTele Tower.Head 1 1).endAt
        (fields.length + (recPositions fields).length))
  | _, [] => atOne
  | k, [.recursive] => bif k == bit0N then at0 else at1
  | _, _ => .const .anonymous

/-- The right sides of a definition by recursion on a positive number with one later argument
of type `X`: at one over the later argument, at `bit0 p` and `bit1 p` over `p`, the value at
`p` (a function of the later argument) and the later argument. -/
def posBody2 (X : CTm Tower.Head 1) (atOne : CTm Tower.Head 1) (at0 at1 : CTm Tower.Head 3) :
    (k : DeclName) → (fields : List CtorField) →
      CTm Tower.Head ((CTele.cons X .nil : CTele Tower.Head 1 2).endAt
        (fields.length + (recPositions fields).length))
  | _, [] => atOne
  | k, [.recursive] => bif k == bit0N then at0 else at1
  | _, _ => .const .anonymous

/-- The right sides of a definition by cases on a natural number with no later argument: at
zero, and at `npos q` over `q`. -/
def natBody1 (atZero : CTm Tower.Head 0) (atPos : CTm Tower.Head 1) :
    (k : DeclName) → (fields : List CtorField) →
      CTm Tower.Head ((CTele.nil : CTele Tower.Head 1 1).endAt
        (fields.length + (recPositions fields).length))
  | _, [] => atZero
  | _, [.closed _] => atPos
  | _, _ => .const .anonymous

/-- The same with one later argument of type `X`. -/
def natBody2 (X : CTm Tower.Head 1) (atZero : CTm Tower.Head 1) (atPos : CTm Tower.Head 2) :
    (k : DeclName) → (fields : List CtorField) →
      CTm Tower.Head ((CTele.cons X .nil : CTele Tower.Head 1 2).endAt
        (fields.length + (recPositions fields).length))
  | _, [] => atZero
  | _, [.closed _] => atPos
  | _, _ => .const .anonymous

/-- `psucc one ⟶ bit0 one`, `psucc (bit0 p) ⟶ bit1 p`, `psucc (bit1 p) ⟶ bit0 (psucc p)`. -/
def psuccDef : RecursiveDefinition Tower.Head where
  name := psuccN
  datatype := posDecl
  width := 1
  later := .nil
  result := cpos
  body := posBody1 (pbit0 pone) (pbit1 (.var 1)) (pbit0 (.var 0))

/-- `phalf one ⟶ n0`, `phalf (bit0 p) ⟶ npos p`, `phalf (bit1 p) ⟶ npos p`. -/
def phalfDef : RecursiveDefinition Tower.Head where
  name := phalfN
  datatype := posDecl
  width := 1
  later := .nil
  result := cnat
  body := posBody1 nzero (npos (.var 1)) (npos (.var 1))

/-- `nhalf n0 ⟶ n0`, `nhalf (npos p) ⟶ phalf p`. -/
def nhalfDef : RecursiveDefinition Tower.Head where
  name := nhalfN
  datatype := natDecl
  width := 1
  later := .nil
  result := cnat
  body := natBody1 nzero (call1 phalfN (.var 0))

/-- `nsucc-pos n0 ⟶ one`, `nsucc-pos (npos q) ⟶ psucc q`. -/
def nsuccPosDef : RecursiveDefinition Tower.Head where
  name := nsuccPosN
  datatype := natDecl
  width := 1
  later := .nil
  result := cpos
  body := natBody1 pone (call1 psuccN (.var 0))

/-- `low0-pos one r ⟶ bit1 r`, `low0-pos (bit0 q) r ⟶ bit0 r`, `low0-pos (bit1 q) r ⟶ bit1 r`. -/
def low0PosDef : RecursiveDefinition Tower.Head where
  name := low0PosN
  datatype := posDecl
  width := 2
  later := .cons cpos .nil
  result := cpos
  body := posBody2 cpos (pbit1 (.var 0)) (pbit0 (.var 0)) (pbit1 (.var 0))

/-- `low0 n0 r ⟶ bit0 r`, `low0 (npos q) r ⟶ low0-pos q r`. -/
def low0Def : RecursiveDefinition Tower.Head where
  name := low0N
  datatype := natDecl
  width := 2
  later := .cons cpos .nil
  result := cpos
  body := natBody2 cpos (pbit0 (.var 0)) (call2 low0PosN (.var 1) (.var 0))

/-- `low1-pos one r ⟶ bit0 (psucc r)`, `low1-pos (bit0 q) r ⟶ bit1 r`,
`low1-pos (bit1 q) r ⟶ bit0 (psucc r)`: the carry. -/
def low1PosDef : RecursiveDefinition Tower.Head where
  name := low1PosN
  datatype := posDecl
  width := 2
  later := .cons cpos .nil
  result := cpos
  body := posBody2 cpos (pbit0 (call1 psuccN (.var 0))) (pbit1 (.var 0))
    (pbit0 (call1 psuccN (.var 0)))

/-- `low1 n0 r ⟶ bit1 r`, `low1 (npos q) r ⟶ low1-pos q r`. -/
def low1Def : RecursiveDefinition Tower.Head where
  name := low1N
  datatype := natDecl
  width := 2
  later := .cons cpos .nil
  result := cpos
  body := natBody2 cpos (pbit1 (.var 0)) (call2 low1PosN (.var 1) (.var 0))

/-- `padd-nat one m ⟶ nsucc-pos m`,
`padd-nat (bit0 p) m ⟶ low0 m (padd-nat p (nhalf m))`,
`padd-nat (bit1 p) m ⟶ low1 m (padd-nat p (nhalf m))`. -/
def paddNatDef : RecursiveDefinition Tower.Head where
  name := paddNatN
  datatype := posDecl
  width := 2
  later := .cons cnat .nil
  result := cpos
  body := posBody2 cnat (call1 nsuccPosN (.var 0))
    (call2 low0N (.var 0) (.app (.var 1) (call1 nhalfN (.var 0))))
    (call2 low1N (.var 0) (.app (.var 1) (call1 nhalfN (.var 0))))

/-- `padd p q ⟶ padd-nat p (npos q)`. -/
def paddDef : ExplicitDefinition Tower.Head where
  name := paddN
  width := 2
  arguments := .cons cpos (.cons cpos .nil)
  result := cpos
  body := (call2 paddNatN (.var 1) (npos (.var 0)) : CTm Tower.Head 2)

/-- `pmul one q ⟶ q`, `pmul (bit0 p) q ⟶ bit0 (pmul p q)`,
`pmul (bit1 p) q ⟶ padd q (bit0 (pmul p q))`. -/
def pmulDef : RecursiveDefinition Tower.Head where
  name := pmulN
  datatype := posDecl
  width := 2
  later := .cons cpos .nil
  result := cpos
  body := posBody2 cpos (.var 0) (pbit0 (.app (.var 1) (.var 0)))
    (call2 paddN (.var 0) (pbit0 (.app (.var 1) (.var 0))))

/-- `pval one ⟶ suc zero`, `pval (bit0 p) ⟶ add (pval p) (pval p)`,
`pval (bit1 p) ⟶ suc (add (pval p) (pval p))`. -/
def pvalDef : RecursiveDefinition Tower.Head where
  name := pvalN
  datatype := posDecl
  width := 1
  later := .nil
  result := cnum
  body := posBody1 (csuc czero) (cadd (.var 0) (.var 0)) (csuc (cadd (.var 0) (.var 0)))

/-- `nval n0 ⟶ zero`, `nval (npos q) ⟶ pval q`. -/
def nvalDef : RecursiveDefinition Tower.Head where
  name := nvalN
  datatype := natDecl
  width := 1
  later := .nil
  result := cnum
  body := natBody1 czero (call1 pvalN (.var 0))

/-! ## The stages of the program -/

abbrev stage3 : List (Declaration Tower.Head) := .definition (.recursive psuccDef) :: stage2
abbrev stage4 : List (Declaration Tower.Head) := .definition (.recursive phalfDef) :: stage3
abbrev stage5 : List (Declaration Tower.Head) := .definition (.recursive nhalfDef) :: stage4
abbrev stage6 : List (Declaration Tower.Head) := .definition (.recursive nsuccPosDef) :: stage5
abbrev stage7 : List (Declaration Tower.Head) := .definition (.recursive low0PosDef) :: stage6
abbrev stage8 : List (Declaration Tower.Head) := .definition (.recursive low0Def) :: stage7
abbrev stage9 : List (Declaration Tower.Head) := .definition (.recursive low1PosDef) :: stage8
abbrev stage10 : List (Declaration Tower.Head) := .definition (.recursive low1Def) :: stage9
abbrev stage11 : List (Declaration Tower.Head) := .definition (.recursive paddNatDef) :: stage10
abbrev stage12 : List (Declaration Tower.Head) := .definition (.explicit paddDef) :: stage11
abbrev stage13 : List (Declaration Tower.Head) := .definition (.recursive pmulDef) :: stage12
abbrev stage14 : List (Declaration Tower.Head) := .definition (.recursive pvalDef) :: stage13

/-- **The binary program**: the positive and the natural numbers, the successor, halving, the
sum digit by digit with its carry, the product, and the two value maps into the numbers of
the object package. The head of the list is the declaration added last. -/
abbrev binaryProgram : List (Declaration Tower.Head) := .definition (.recursive nvalDef) :: stage14

/-- **The binary package**: the object package with the binary program. -/
abbrev binary := withDeclarations objectChurch binaryProgram

/-! ## The declared constants are typed where they are declared -/

section Declared

variable {ds : List (Declaration Tower.Head)} (adm : AdmissibleDeclarations objectChurch ds)
  {n : Nat} {Γ : CCtx Tower.Head n}

include adm

local notation "P" => withDeclarations objectChurch ds

theorem tPos (member : Declaration.datatype posDecl ∈ ds) : CTyped P Γ cpos cU0 :=
  adm.type_typed ConvRules.objectLevels member

theorem tNat (member : Declaration.datatype natDecl ∈ ds) : CTyped P Γ cnat cU0 :=
  adm.type_typed ConvRules.objectLevels member

theorem tOne (member : Declaration.datatype posDecl ∈ ds) : CTyped P Γ pone cpos :=
  adm.ctor_typed ConvRules.objectLevels (d := posDecl) member (i := 0) rfl

theorem tBit0 (member : Declaration.datatype posDecl ∈ ds) {a : CTm Tower.Head n}
    (ha : CTyped P Γ a cpos) : CTyped P Γ (pbit0 a) cpos :=
  .appElim (B := cpos) (adm.ctor_typed ConvRules.objectLevels (d := posDecl) member (i := 1) rfl)
    ha

theorem tBit1 (member : Declaration.datatype posDecl ∈ ds) {a : CTm Tower.Head n}
    (ha : CTyped P Γ a cpos) : CTyped P Γ (pbit1 a) cpos :=
  .appElim (B := cpos) (adm.ctor_typed ConvRules.objectLevels (d := posDecl) member (i := 2) rfl)
    ha

theorem tN0 (member : Declaration.datatype natDecl ∈ ds) : CTyped P Γ nzero cnat :=
  adm.ctor_typed ConvRules.objectLevels (d := natDecl) member (i := 0) rfl

theorem tNpos (member : Declaration.datatype natDecl ∈ ds) {a : CTm Tower.Head n}
    (ha : CTyped P Γ a cpos) : CTyped P Γ (npos a) cnat :=
  .appElim (B := cnat) (adm.ctor_typed ConvRules.objectLevels (d := natDecl) member (i := 1) rfl)
    ha

theorem tPsucc (member : Declaration.definition (.recursive psuccDef) ∈ ds) {a : CTm Tower.Head n}
    (ha : CTyped P Γ a cpos) : CTyped P Γ (call1 psuccN a) cpos :=
  .appElim (B := cpos)
    (adm.definition_typed ConvRules.objectLevels (D := .recursive psuccDef) member) ha

theorem tPhalf (member : Declaration.definition (.recursive phalfDef) ∈ ds) {a : CTm Tower.Head n}
    (ha : CTyped P Γ a cpos) : CTyped P Γ (call1 phalfN a) cnat :=
  .appElim (B := cnat)
    (adm.definition_typed ConvRules.objectLevels (D := .recursive phalfDef) member) ha

theorem tNhalf (member : Declaration.definition (.recursive nhalfDef) ∈ ds) {a : CTm Tower.Head n}
    (ha : CTyped P Γ a cnat) : CTyped P Γ (call1 nhalfN a) cnat :=
  .appElim (B := cnat)
    (adm.definition_typed ConvRules.objectLevels (D := .recursive nhalfDef) member) ha

theorem tNsuccPos (member : Declaration.definition (.recursive nsuccPosDef) ∈ ds)
    {a : CTm Tower.Head n} (ha : CTyped P Γ a cnat) : CTyped P Γ (call1 nsuccPosN a) cpos :=
  .appElim (B := cpos)
    (adm.definition_typed ConvRules.objectLevels (D := .recursive nsuccPosDef) member) ha

theorem tLow0Pos (member : Declaration.definition (.recursive low0PosDef) ∈ ds)
    {a b : CTm Tower.Head n} (ha : CTyped P Γ a cpos) (hb : CTyped P Γ b cpos) :
    CTyped P Γ (call2 low0PosN a b) cpos :=
  .appElim (B := cpos) (.appElim (B := .pi cpos cpos)
    (adm.definition_typed ConvRules.objectLevels (D := .recursive low0PosDef) member) ha) hb

theorem tLow0 (member : Declaration.definition (.recursive low0Def) ∈ ds)
    {a b : CTm Tower.Head n} (ha : CTyped P Γ a cnat) (hb : CTyped P Γ b cpos) :
    CTyped P Γ (call2 low0N a b) cpos :=
  .appElim (B := cpos) (.appElim (B := .pi cpos cpos)
    (adm.definition_typed ConvRules.objectLevels (D := .recursive low0Def) member) ha) hb

theorem tLow1Pos (member : Declaration.definition (.recursive low1PosDef) ∈ ds)
    {a b : CTm Tower.Head n} (ha : CTyped P Γ a cpos) (hb : CTyped P Γ b cpos) :
    CTyped P Γ (call2 low1PosN a b) cpos :=
  .appElim (B := cpos) (.appElim (B := .pi cpos cpos)
    (adm.definition_typed ConvRules.objectLevels (D := .recursive low1PosDef) member) ha) hb

theorem tLow1 (member : Declaration.definition (.recursive low1Def) ∈ ds)
    {a b : CTm Tower.Head n} (ha : CTyped P Γ a cnat) (hb : CTyped P Γ b cpos) :
    CTyped P Γ (call2 low1N a b) cpos :=
  .appElim (B := cpos) (.appElim (B := .pi cpos cpos)
    (adm.definition_typed ConvRules.objectLevels (D := .recursive low1Def) member) ha) hb

theorem tPaddNat (member : Declaration.definition (.recursive paddNatDef) ∈ ds)
    {a b : CTm Tower.Head n} (ha : CTyped P Γ a cpos) (hb : CTyped P Γ b cnat) :
    CTyped P Γ (call2 paddNatN a b) cpos :=
  .appElim (B := cpos) (.appElim (B := .pi cnat cpos)
    (adm.definition_typed ConvRules.objectLevels (D := .recursive paddNatDef) member) ha) hb

theorem tPadd (member : Declaration.definition (.explicit paddDef) ∈ ds)
    {a b : CTm Tower.Head n} (ha : CTyped P Γ a cpos) (hb : CTyped P Γ b cpos) :
    CTyped P Γ (call2 paddN a b) cpos :=
  .appElim (B := cpos) (.appElim (B := .pi cpos cpos)
    (adm.definition_typed ConvRules.objectLevels (D := .explicit paddDef) member) ha) hb

theorem tPmul (member : Declaration.definition (.recursive pmulDef) ∈ ds)
    {a b : CTm Tower.Head n} (ha : CTyped P Γ a cpos) (hb : CTyped P Γ b cpos) :
    CTyped P Γ (call2 pmulN a b) cpos :=
  .appElim (B := cpos) (.appElim (B := .pi cpos cpos)
    (adm.definition_typed ConvRules.objectLevels (D := .recursive pmulDef) member) ha) hb

theorem tPval (member : Declaration.definition (.recursive pvalDef) ∈ ds) {a : CTm Tower.Head n}
    (ha : CTyped P Γ a cpos) : CTyped P Γ (call1 pvalN a) cnum :=
  .appElim (B := cnum)
    (adm.definition_typed ConvRules.objectLevels (D := .recursive pvalDef) member) ha

theorem tNval (member : Declaration.definition (.recursive nvalDef) ∈ ds) {a : CTm Tower.Head n}
    (ha : CTyped P Γ a cnat) : CTyped P Γ (call1 nvalN a) cnum :=
  .appElim (B := cnum)
    (adm.definition_typed ConvRules.objectLevels (D := .recursive nvalDef) member) ha

end Declared

/-! ## Admissibility, by the shape of each definition -/

theorem posBody1_one (atOne : CTm Tower.Head 0) (at0 at1 : CTm Tower.Head 2) (k : DeclName) :
    posBody1 atOne at0 at1 k [] = atOne := rfl

theorem posBody1_bit0 (atOne : CTm Tower.Head 0) (at0 at1 : CTm Tower.Head 2) :
    posBody1 atOne at0 at1 bit0N [.recursive] = at0 :=
  rfl

theorem posBody1_bit1 (atOne : CTm Tower.Head 0) (at0 at1 : CTm Tower.Head 2) :
    posBody1 atOne at0 at1 bit1N [.recursive] = at1 :=
  rfl

theorem posBody2_one (X atOne : CTm Tower.Head 1) (at0 at1 : CTm Tower.Head 3) (k : DeclName) :
    posBody2 X atOne at0 at1 k [] = atOne := rfl

theorem posBody2_bit0 (X atOne : CTm Tower.Head 1) (at0 at1 : CTm Tower.Head 3) :
    posBody2 X atOne at0 at1 bit0N [.recursive] = at0 :=
  rfl

theorem posBody2_bit1 (X atOne : CTm Tower.Head 1) (at0 at1 : CTm Tower.Head 3) :
    posBody2 X atOne at0 at1 bit1N [.recursive] = at1 :=
  rfl

section Shapes

variable {ds : List (Declaration Tower.Head)} (adm : AdmissibleDeclarations objectChurch ds)

include adm

local notation "P" => withDeclarations objectChurch ds

/-- A type named by a constant, typed in every context of the package. -/
abbrev ConstType (c : DeclName) : Prop :=
  ∀ {m : Nat} {Δ : CCtx Tower.Head m}, CTyped P Δ (.const c) cU0

/-- **A definition by recursion on a positive number with no later argument** is admissible
when its three right sides are typed. -/
theorem posRec1_admissible (memPos : Declaration.datatype posDecl ∈ ds) (name c : DeclName)
    (atOne : CTm Tower.Head 0) (at0 at1 : CTm Tower.Head 2)
    (new : (withDeclarations objectChurch ds).constantType name = none)
    (hC : ConstType (ds := ds) c)
    (hOne : CTyped P .nil atOne (.const c))
    (h0 : CTyped P (.snoc (.snoc .nil cpos) (.const c)) at0 (.const c))
    (h1 : CTyped P (.snoc (.snoc .nil cpos) (.const c)) at1 (.const c)) :
    RecursiveDefinition.Admissible P
      { name := name, datatype := posDecl, width := 1, later := .nil, result := .const c,
        body := posBody1 atOne at0 at1 } where
  new := new
  typeFormed := ⟨_, uSort (withDeclarations_base _ ds) _,
    tPi (withDeclarations_base _ ds) (tPos adm memPos) hC⟩
  family := ⟨_, uSort (withDeclarations_base _ ds) _, hC⟩
  formed := fun entry => by
    rcases posCtors_entry entry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (.nil : CCtxFormed P (.nil : CCtx Tower.Head 0))
    all_goals exact (.snoc (.snoc .nil ⟨_, uSort (withDeclarations_base _ ds) _, tPos adm memPos⟩)
      ⟨_, uSort (withDeclarations_base _ ds) _, hC⟩ :
        CCtxFormed P (.snoc (.snoc .nil cpos) (.const c) : CCtx Tower.Head 2))
  resultType := fun entry => by
    rcases posCtors_entry entry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (⟨_, uSort (withDeclarations_base _ ds) _, hC⟩ :
        CIsType P (.nil : CCtx Tower.Head 0) (.const c))
    all_goals exact (⟨_, uSort (withDeclarations_base _ ds) _, hC⟩ :
        CIsType P (.snoc (.snoc .nil cpos) (.const c) : CCtx Tower.Head 2) (.const c))
  bodies := fun entry => by
    rcases posCtors_entry entry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hOne
    · exact (by rw [posBody1_bit0]; exact h0 :
        CTyped P (.snoc (.snoc .nil cpos) (.const c)) (posBody1 atOne at0 at1 bit0N [.recursive])
          (.const c))
    · exact (by rw [posBody1_bit1]; exact h1 :
        CTyped P (.snoc (.snoc .nil cpos) (.const c)) (posBody1 atOne at0 at1 bit1N [.recursive])
          (.const c))

/-- **A definition by recursion on a positive number with one later argument** of the type
named `x` is admissible when its three right sides are typed. -/
theorem posRec2_admissible (memPos : Declaration.datatype posDecl ∈ ds) (name x c : DeclName)
    (atOne : CTm Tower.Head 1) (at0 at1 : CTm Tower.Head 3)
    (new : (withDeclarations objectChurch ds).constantType name = none)
    (hX : ConstType (ds := ds) x) (hC : ConstType (ds := ds) c)
    (hOne : CTyped P (.snoc .nil (.const x)) atOne (.const c))
    (h0 : CTyped P (.snoc (.snoc (.snoc .nil cpos) (.pi (.const x) (.const c))) (.const x)) at0
      (.const c))
    (h1 : CTyped P (.snoc (.snoc (.snoc .nil cpos) (.pi (.const x) (.const c))) (.const x)) at1
      (.const c)) :
    RecursiveDefinition.Admissible P
      { name := name, datatype := posDecl, width := 2, later := .cons (.const x) .nil,
        result := .const c, body := posBody2 (.const x) atOne at0 at1 } where
  new := new
  typeFormed := ⟨_, uSort (withDeclarations_base _ ds) _,
    tPi (withDeclarations_base _ ds) (tPos adm memPos) (tPi (withDeclarations_base _ ds) hX hC)⟩
  family := ⟨_, uSort (withDeclarations_base _ ds) _, tPi (withDeclarations_base _ ds) hX hC⟩
  formed := fun entry => by
    rcases posCtors_entry entry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (.snoc .nil ⟨_, uSort (withDeclarations_base _ ds) _, hX⟩ :
        CCtxFormed P (.snoc .nil (.const x) : CCtx Tower.Head 1))
    all_goals exact (.snoc (.snoc (.snoc .nil
        ⟨_, uSort (withDeclarations_base _ ds) _, tPos adm memPos⟩)
        ⟨_, uSort (withDeclarations_base _ ds) _, tPi (withDeclarations_base _ ds) hX hC⟩)
        ⟨_, uSort (withDeclarations_base _ ds) _, hX⟩ :
      CCtxFormed P (.snoc (.snoc (.snoc .nil cpos) (.pi (.const x) (.const c))) (.const x) :
        CCtx Tower.Head 3))
  resultType := fun entry => by
    rcases posCtors_entry entry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (⟨_, uSort (withDeclarations_base _ ds) _, hC⟩ :
        CIsType P (.snoc .nil (.const x) : CCtx Tower.Head 1) (.const c))
    all_goals exact (⟨_, uSort (withDeclarations_base _ ds) _, hC⟩ :
        CIsType P (.snoc (.snoc (.snoc .nil cpos) (.pi (.const x) (.const c))) (.const x) :
          CCtx Tower.Head 3) (.const c))
  bodies := fun entry => by
    rcases posCtors_entry entry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hOne
    · exact (by rw [posBody2_bit0]; exact h0 :
        CTyped P (.snoc (.snoc (.snoc .nil cpos) (.pi (.const x) (.const c))) (.const x))
          (posBody2 (.const x) atOne at0 at1 bit0N [.recursive]) (.const c))
    · exact (by rw [posBody2_bit1]; exact h1 :
        CTyped P (.snoc (.snoc (.snoc .nil cpos) (.pi (.const x) (.const c))) (.const x))
          (posBody2 (.const x) atOne at0 at1 bit1N [.recursive]) (.const c))

/-- **A definition by cases on a natural number with no later argument** is admissible when
its two right sides are typed. -/
theorem natRec1_admissible (memPos : Declaration.datatype posDecl ∈ ds)
    (memNat : Declaration.datatype natDecl ∈ ds) (name c : DeclName)
    (atZero : CTm Tower.Head 0) (atPos : CTm Tower.Head 1)
    (new : (withDeclarations objectChurch ds).constantType name = none)
    (hC : ConstType (ds := ds) c)
    (hZero : CTyped P .nil atZero (.const c))
    (hPos : CTyped P (.snoc .nil cpos) atPos (.const c)) :
    RecursiveDefinition.Admissible P
      { name := name, datatype := natDecl, width := 1, later := .nil, result := .const c,
        body := natBody1 atZero atPos } where
  new := new
  typeFormed := ⟨_, uSort (withDeclarations_base _ ds) _,
    tPi (withDeclarations_base _ ds) (tNat adm memNat) hC⟩
  family := ⟨_, uSort (withDeclarations_base _ ds) _, hC⟩
  formed := fun entry => by
    rcases natCtors_entry entry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (.nil : CCtxFormed P (.nil : CCtx Tower.Head 0))
    · exact (.snoc .nil ⟨_, uSort (withDeclarations_base _ ds) _, tPos adm memPos⟩ :
        CCtxFormed P (.snoc .nil cpos : CCtx Tower.Head 1))
  resultType := fun entry => by
    rcases natCtors_entry entry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (⟨_, uSort (withDeclarations_base _ ds) _, hC⟩ :
        CIsType P (.nil : CCtx Tower.Head 0) (.const c))
    · exact (⟨_, uSort (withDeclarations_base _ ds) _, hC⟩ :
        CIsType P (.snoc .nil cpos : CCtx Tower.Head 1) (.const c))
  bodies := fun entry => by
    rcases natCtors_entry entry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hZero
    · exact hPos

/-- **A definition by cases on a natural number with one later argument** of the type named
`x` is admissible when its two right sides are typed. -/
theorem natRec2_admissible (memPos : Declaration.datatype posDecl ∈ ds)
    (memNat : Declaration.datatype natDecl ∈ ds) (name x c : DeclName)
    (atZero : CTm Tower.Head 1) (atPos : CTm Tower.Head 2)
    (new : (withDeclarations objectChurch ds).constantType name = none)
    (hX : ConstType (ds := ds) x) (hC : ConstType (ds := ds) c)
    (hZero : CTyped P (.snoc .nil (.const x)) atZero (.const c))
    (hPos : CTyped P (.snoc (.snoc .nil cpos) (.const x)) atPos (.const c)) :
    RecursiveDefinition.Admissible P
      { name := name, datatype := natDecl, width := 2, later := .cons (.const x) .nil,
        result := .const c, body := natBody2 (.const x) atZero atPos } where
  new := new
  typeFormed := ⟨_, uSort (withDeclarations_base _ ds) _,
    tPi (withDeclarations_base _ ds) (tNat adm memNat) (tPi (withDeclarations_base _ ds) hX hC)⟩
  family := ⟨_, uSort (withDeclarations_base _ ds) _, tPi (withDeclarations_base _ ds) hX hC⟩
  formed := fun entry => by
    rcases natCtors_entry entry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (.snoc .nil ⟨_, uSort (withDeclarations_base _ ds) _, hX⟩ :
        CCtxFormed P (.snoc .nil (.const x) : CCtx Tower.Head 1))
    · exact (.snoc (.snoc .nil ⟨_, uSort (withDeclarations_base _ ds) _, tPos adm memPos⟩)
        ⟨_, uSort (withDeclarations_base _ ds) _, hX⟩ :
        CCtxFormed P (.snoc (.snoc .nil cpos) (.const x) : CCtx Tower.Head 2))
  resultType := fun entry => by
    rcases natCtors_entry entry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (⟨_, uSort (withDeclarations_base _ ds) _, hC⟩ :
        CIsType P (.snoc .nil (.const x) : CCtx Tower.Head 1) (.const c))
    · exact (⟨_, uSort (withDeclarations_base _ ds) _, hC⟩ :
        CIsType P (.snoc (.snoc .nil cpos) (.const x) : CCtx Tower.Head 2) (.const c))
  bodies := fun entry => by
    rcases natCtors_entry entry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hZero
    · exact hPos

end Shapes

/-! ## The program is admissible, declaration by declaration -/

section Stages

variable {n : Nat}

theorem stage3_admissible : AdmissibleDeclarations objectChurch stage3 :=
  ⟨stage2_admissible, by member_tac,
    posRec1_admissible stage2_admissible (by member_tac) psuccN posN _ _ _ (by decide)
      (tPos stage2_admissible (by member_tac))
      (tBit0 stage2_admissible (by member_tac) (tOne stage2_admissible (by member_tac)))
      (tBit1 stage2_admissible (by member_tac) (.var 1))
      (tBit0 stage2_admissible (by member_tac) (.var 0))⟩

theorem stage4_admissible : AdmissibleDeclarations objectChurch stage4 :=
  ⟨stage3_admissible, by member_tac,
    posRec1_admissible stage3_admissible (by member_tac) phalfN natN _ _ _ (by decide)
      (tNat stage3_admissible (by member_tac))
      (tN0 stage3_admissible (by member_tac))
      (tNpos stage3_admissible (by member_tac) (.var 1))
      (tNpos stage3_admissible (by member_tac) (.var 1))⟩

theorem stage5_admissible : AdmissibleDeclarations objectChurch stage5 :=
  ⟨stage4_admissible, by member_tac,
    natRec1_admissible stage4_admissible (by member_tac) (by member_tac) nhalfN natN _ _
      (by decide) (tNat stage4_admissible (by member_tac))
      (tN0 stage4_admissible (by member_tac))
      (tPhalf stage4_admissible (by member_tac) (.var 0))⟩

theorem stage6_admissible : AdmissibleDeclarations objectChurch stage6 :=
  ⟨stage5_admissible, by member_tac,
    natRec1_admissible stage5_admissible (by member_tac) (by member_tac) nsuccPosN posN _ _
      (by decide) (tPos stage5_admissible (by member_tac))
      (tOne stage5_admissible (by member_tac))
      (tPsucc stage5_admissible (by member_tac) (.var 0))⟩

theorem stage7_admissible : AdmissibleDeclarations objectChurch stage7 :=
  ⟨stage6_admissible, by member_tac,
    posRec2_admissible stage6_admissible (by member_tac) low0PosN posN posN _ _ _ (by decide)
      (tPos stage6_admissible (by member_tac)) (tPos stage6_admissible (by member_tac))
      (tBit1 stage6_admissible (by member_tac) (.var 0))
      (tBit0 stage6_admissible (by member_tac) (.var 0))
      (tBit1 stage6_admissible (by member_tac) (.var 0))⟩

theorem stage8_admissible : AdmissibleDeclarations objectChurch stage8 :=
  ⟨stage7_admissible, by member_tac,
    natRec2_admissible stage7_admissible (by member_tac) (by member_tac) low0N posN posN _ _
      (by decide) (tPos stage7_admissible (by member_tac)) (tPos stage7_admissible (by member_tac))
      (tBit0 stage7_admissible (by member_tac) (.var 0))
      (tLow0Pos stage7_admissible (by member_tac) (.var 1) (.var 0))⟩

theorem stage9_admissible : AdmissibleDeclarations objectChurch stage9 :=
  ⟨stage8_admissible, by member_tac,
    posRec2_admissible stage8_admissible (by member_tac) low1PosN posN posN _ _ _ (by decide)
      (tPos stage8_admissible (by member_tac)) (tPos stage8_admissible (by member_tac))
      (tBit0 stage8_admissible (by member_tac) (tPsucc stage8_admissible (by member_tac) (.var 0)))
      (tBit1 stage8_admissible (by member_tac) (.var 0))
      (tBit0 stage8_admissible (by member_tac) (tPsucc stage8_admissible (by member_tac) (.var 0)))⟩

theorem stage10_admissible : AdmissibleDeclarations objectChurch stage10 :=
  ⟨stage9_admissible, by member_tac,
    natRec2_admissible stage9_admissible (by member_tac) (by member_tac) low1N posN posN _ _
      (by decide) (tPos stage9_admissible (by member_tac)) (tPos stage9_admissible (by member_tac))
      (tBit1 stage9_admissible (by member_tac) (.var 0))
      (tLow1Pos stage9_admissible (by member_tac) (.var 1) (.var 0))⟩

theorem stage11_admissible : AdmissibleDeclarations objectChurch stage11 :=
  ⟨stage10_admissible, by member_tac,
    posRec2_admissible stage10_admissible (by member_tac) paddNatN natN posN _ _ _ (by decide)
      (tNat stage10_admissible (by member_tac)) (tPos stage10_admissible (by member_tac))
      (tNsuccPos stage10_admissible (by member_tac) (.var 0))
      (tLow0 stage10_admissible (by member_tac) (.var 0)
        (.appElim (B := cpos) (.var 1) (tNhalf stage10_admissible (by member_tac) (.var 0))))
      (tLow1 stage10_admissible (by member_tac) (.var 0)
        (.appElim (B := cpos) (.var 1) (tNhalf stage10_admissible (by member_tac) (.var 0))))⟩

theorem paddDef_admissible : paddDef.Admissible (withDeclarations objectChurch stage11) where
  new := by decide
  formed :=
    .snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, tPos stage11_admissible (by member_tac)⟩)
      ⟨_, LevelTower.IsUniverse.sort _, tPos stage11_admissible (by member_tac)⟩
  resultType := ⟨_, LevelTower.IsUniverse.sort _, tPos stage11_admissible (by member_tac)⟩
  body := by
    have first : CTyped (withDeclarations objectChurch stage11)
        (CCtx.snoc (.snoc .nil cpos) cpos : CCtx Tower.Head 2) (.var 1) cpos := .var 1
    have second : CTyped (withDeclarations objectChurch stage11)
        (CCtx.snoc (.snoc .nil cpos) cpos : CCtx Tower.Head 2) (.var 0) cpos := .var 0
    exact tPaddNat stage11_admissible (by member_tac) first
      (tNpos stage11_admissible (by member_tac) second)

theorem stage12_admissible : AdmissibleDeclarations objectChurch stage12 :=
  ⟨stage11_admissible, paddDef_admissible⟩

theorem stage13_admissible : AdmissibleDeclarations objectChurch stage13 :=
  ⟨stage12_admissible, by member_tac,
    posRec2_admissible stage12_admissible (by member_tac) pmulN posN posN _ _ _ (by decide)
      (tPos stage12_admissible (by member_tac)) (tPos stage12_admissible (by member_tac))
      (.var 0)
      (tBit0 stage12_admissible (by member_tac) (.appElim (B := cpos) (.var 1) (.var 0)))
      (tPadd stage12_admissible (by member_tac) (.var 0)
        (tBit0 stage12_admissible (by member_tac) (.appElim (B := cpos) (.var 1) (.var 0))))⟩

theorem stage14_admissible : AdmissibleDeclarations objectChurch stage14 :=
  ⟨stage13_admissible, by member_tac,
    posRec1_admissible stage13_admissible (by member_tac) pvalN numN _ _ _ (by decide)
      (tNum (withDeclarations_base _ stage13))
      (tSuc (withDeclarations_base _ stage13) (tZero (withDeclarations_base _ stage13)))
      (tAdd (withDeclarations_base _ stage13) (.var 0) (.var 0))
      (tSuc (withDeclarations_base _ stage13) (tAdd (withDeclarations_base _ stage13) (.var 0)
        (.var 0)))⟩

/-- **The binary program is an admissible list of declarations** over the object package. -/
theorem binaryProgram_admissible : AdmissibleDeclarations objectChurch binaryProgram :=
  ⟨stage14_admissible, by member_tac,
    natRec1_admissible stage14_admissible (by member_tac) (by member_tac) nvalN numN _ _
      (by decide) (tNum (withDeclarations_base _ stage14))
      (tZero (withDeclarations_base _ stage14))
      (tPval stage14_admissible (by member_tac) (.var 0))⟩

end Stages

/-! ## The written equations -/

/-- `(psucc one) ⟶ (bit0 one)`. -/
def psuccOneEq : DefiningEquation Tower.Head where
  arity := 0
  telescope := .nil
  left := call1 psuccN pone
  right := pbit0 pone

/-- `(psucc (bit0 $p)) ⟶ (bit1 $p)`. -/
def psuccBit0Eq : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cpos
  left := call1 psuccN (pbit0 (.var 0))
  right := pbit1 (.var 0)

/-- `(psucc (bit1 $p)) ⟶ (bit0 (psucc $p))`. -/
def psuccBit1Eq : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cpos
  left := call1 psuccN (pbit1 (.var 0))
  right := pbit0 (call1 psuccN (.var 0))

/-- `(phalf one) ⟶ n0`. -/
def phalfOneEq : DefiningEquation Tower.Head where
  arity := 0
  telescope := .nil
  left := call1 phalfN pone
  right := nzero

/-- `(phalf (bit0 $p)) ⟶ (npos $p)`. -/
def phalfBit0Eq : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cpos
  left := call1 phalfN (pbit0 (.var 0))
  right := npos (.var 0)

/-- `(phalf (bit1 $p)) ⟶ (npos $p)`. -/
def phalfBit1Eq : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cpos
  left := call1 phalfN (pbit1 (.var 0))
  right := npos (.var 0)

/-- `(nhalf n0) ⟶ n0`. -/
def nhalfZeroEq : DefiningEquation Tower.Head where
  arity := 0
  telescope := .nil
  left := call1 nhalfN nzero
  right := nzero

/-- `(nhalf (npos $q)) ⟶ (phalf $q)`. -/
def nhalfPosEq : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cpos
  left := call1 nhalfN (npos (.var 0))
  right := call1 phalfN (.var 0)

/-- `(nsucc-pos n0) ⟶ one`. -/
def nsuccPosZeroEq : DefiningEquation Tower.Head where
  arity := 0
  telescope := .nil
  left := call1 nsuccPosN nzero
  right := pone

/-- `(nsucc-pos (npos $q)) ⟶ (psucc $q)`. -/
def nsuccPosPosEq : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cpos
  left := call1 nsuccPosN (npos (.var 0))
  right := call1 psuccN (.var 0)

/-- `(low0-pos one $r) ⟶ (bit1 $r)`. -/
def low0PosOneEq : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cpos
  left := call2 low0PosN pone (.var 0)
  right := pbit1 (.var 0)

/-- `(low0-pos (bit0 $q) $r) ⟶ (bit0 $r)`. -/
def low0PosBit0Eq : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cpos) cpos
  left := call2 low0PosN (pbit0 (.var 1)) (.var 0)
  right := pbit0 (.var 0)

/-- `(low0-pos (bit1 $q) $r) ⟶ (bit1 $r)`. -/
def low0PosBit1Eq : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cpos) cpos
  left := call2 low0PosN (pbit1 (.var 1)) (.var 0)
  right := pbit1 (.var 0)

/-- `(low0 n0 $r) ⟶ (bit0 $r)`. -/
def low0ZeroEq : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cpos
  left := call2 low0N nzero (.var 0)
  right := pbit0 (.var 0)

/-- `(low0 (npos $q) $r) ⟶ (low0-pos $q $r)`. -/
def low0PosEq : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cpos) cpos
  left := call2 low0N (npos (.var 1)) (.var 0)
  right := call2 low0PosN (.var 1) (.var 0)

/-- `(low1-pos one $r) ⟶ (bit0 (psucc $r))`. -/
def low1PosOneEq : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cpos
  left := call2 low1PosN pone (.var 0)
  right := pbit0 (call1 psuccN (.var 0))

/-- `(low1-pos (bit0 $q) $r) ⟶ (bit1 $r)`. -/
def low1PosBit0Eq : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cpos) cpos
  left := call2 low1PosN (pbit0 (.var 1)) (.var 0)
  right := pbit1 (.var 0)

/-- `(low1-pos (bit1 $q) $r) ⟶ (bit0 (psucc $r))`. -/
def low1PosBit1Eq : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cpos) cpos
  left := call2 low1PosN (pbit1 (.var 1)) (.var 0)
  right := pbit0 (call1 psuccN (.var 0))

/-- `(low1 n0 $r) ⟶ (bit1 $r)`. -/
def low1ZeroEq : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cpos
  left := call2 low1N nzero (.var 0)
  right := pbit1 (.var 0)

/-- `(low1 (npos $q) $r) ⟶ (low1-pos $q $r)`. -/
def low1PosEq : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cpos) cpos
  left := call2 low1N (npos (.var 1)) (.var 0)
  right := call2 low1PosN (.var 1) (.var 0)

/-- `(padd-nat one $m) ⟶ (nsucc-pos $m)`. -/
def paddNatOneEq : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cnat
  left := call2 paddNatN pone (.var 0)
  right := call1 nsuccPosN (.var 0)

/-- `(padd-nat (bit0 $p) $m) ⟶ (low0 $m (padd-nat $p (nhalf $m)))`. -/
def paddNatBit0Eq : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cpos) cnat
  left := call2 paddNatN (pbit0 (.var 1)) (.var 0)
  right := call2 low0N (.var 0) (call2 paddNatN (.var 1) (call1 nhalfN (.var 0)))

/-- `(padd-nat (bit1 $p) $m) ⟶ (low1 $m (padd-nat $p (nhalf $m)))`. -/
def paddNatBit1Eq : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cpos) cnat
  left := call2 paddNatN (pbit1 (.var 1)) (.var 0)
  right := call2 low1N (.var 0) (call2 paddNatN (.var 1) (call1 nhalfN (.var 0)))

/-- `(padd $p $q) ⟶ (padd-nat $p (npos $q))`. -/
def paddEqEq : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cpos) cpos
  left := call2 paddN (.var 1) (.var 0)
  right := call2 paddNatN (.var 1) (npos (.var 0))

/-- `(pmul one $q) ⟶ $q`. -/
def pmulOneEq : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cpos
  left := call2 pmulN pone (.var 0)
  right := .var 0

/-- `(pmul (bit0 $p) $q) ⟶ (bit0 (pmul $p $q))`. -/
def pmulBit0Eq : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cpos) cpos
  left := call2 pmulN (pbit0 (.var 1)) (.var 0)
  right := pbit0 (call2 pmulN (.var 1) (.var 0))

/-- `(pmul (bit1 $p) $q) ⟶ (padd $q (bit0 (pmul $p $q)))`. -/
def pmulBit1Eq : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cpos) cpos
  left := call2 pmulN (pbit1 (.var 1)) (.var 0)
  right := call2 paddN (.var 0) (pbit0 (call2 pmulN (.var 1) (.var 0)))

/-- `(pval one) ⟶ (suc zero)`. -/
def pvalOneEq : DefiningEquation Tower.Head where
  arity := 0
  telescope := .nil
  left := call1 pvalN pone
  right := csuc czero

/-- `(pval (bit0 $p)) ⟶ (add (pval $p) (pval $p))`. -/
def pvalBit0Eq : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cpos
  left := call1 pvalN (pbit0 (.var 0))
  right := cadd (call1 pvalN (.var 0)) (call1 pvalN (.var 0))

/-- `(pval (bit1 $p)) ⟶ (suc (add (pval $p) (pval $p)))`. -/
def pvalBit1Eq : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cpos
  left := call1 pvalN (pbit1 (.var 0))
  right := csuc (cadd (call1 pvalN (.var 0)) (call1 pvalN (.var 0)))

/-- `(nval n0) ⟶ zero`. -/
def nvalZeroEq : DefiningEquation Tower.Head where
  arity := 0
  telescope := .nil
  left := call1 nvalN nzero
  right := czero

/-- `(nval (npos $q)) ⟶ (pval $q)`. -/
def nvalPosEq : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cpos
  left := call1 nvalN (npos (.var 0))
  right := call1 pvalN (.var 0)

theorem psuccDef_equations : psuccDef.equations = [psuccOneEq, psuccBit0Eq, psuccBit1Eq] := rfl
theorem phalfDef_equations : phalfDef.equations = [phalfOneEq, phalfBit0Eq, phalfBit1Eq] := rfl
theorem nhalfDef_equations : nhalfDef.equations = [nhalfZeroEq, nhalfPosEq] := rfl
theorem nsuccPosDef_equations : nsuccPosDef.equations = [nsuccPosZeroEq, nsuccPosPosEq] := rfl
theorem low0PosDef_equations :
    low0PosDef.equations = [low0PosOneEq, low0PosBit0Eq, low0PosBit1Eq] := rfl
theorem low0Def_equations : low0Def.equations = [low0ZeroEq, low0PosEq] := rfl
theorem low1PosDef_equations :
    low1PosDef.equations = [low1PosOneEq, low1PosBit0Eq, low1PosBit1Eq] := rfl
theorem low1Def_equations : low1Def.equations = [low1ZeroEq, low1PosEq] := rfl
theorem paddNatDef_equations :
    paddNatDef.equations = [paddNatOneEq, paddNatBit0Eq, paddNatBit1Eq] := rfl
theorem paddDef_equations : paddDef.equations = [paddEqEq] := rfl
theorem pmulDef_equations : pmulDef.equations = [pmulOneEq, pmulBit0Eq, pmulBit1Eq] := rfl
theorem pvalDef_equations : pvalDef.equations = [pvalOneEq, pvalBit0Eq, pvalBit1Eq] := rfl
theorem nvalDef_equations : nvalDef.equations = [nvalZeroEq, nvalPosEq] := rfl

/-! ### Typing in the binary package -/

section Typing

variable {n : Nat} {Γ : CCtx Tower.Head n}

theorem bOne :
    CTyped binary Γ (pone) cpos :=
  tOne binaryProgram_admissible (by member_tac)

theorem bBit0 {a : CTm Tower.Head n} (ha : CTyped binary Γ a cpos) :
    CTyped binary Γ (pbit0 a) cpos :=
  tBit0 binaryProgram_admissible (by member_tac) ha

theorem bBit1 {a : CTm Tower.Head n} (ha : CTyped binary Γ a cpos) :
    CTyped binary Γ (pbit1 a) cpos :=
  tBit1 binaryProgram_admissible (by member_tac) ha

theorem bN0 :
    CTyped binary Γ (nzero) cnat :=
  tN0 binaryProgram_admissible (by member_tac)

theorem bNpos {a : CTm Tower.Head n} (ha : CTyped binary Γ a cpos) :
    CTyped binary Γ (npos a) cnat :=
  tNpos binaryProgram_admissible (by member_tac) ha

theorem bPsucc {a : CTm Tower.Head n} (ha : CTyped binary Γ a cpos) :
    CTyped binary Γ (call1 psuccN a) cpos :=
  tPsucc binaryProgram_admissible (by member_tac) ha

theorem bPhalf {a : CTm Tower.Head n} (ha : CTyped binary Γ a cpos) :
    CTyped binary Γ (call1 phalfN a) cnat :=
  tPhalf binaryProgram_admissible (by member_tac) ha

theorem bNhalf {a : CTm Tower.Head n} (ha : CTyped binary Γ a cnat) :
    CTyped binary Γ (call1 nhalfN a) cnat :=
  tNhalf binaryProgram_admissible (by member_tac) ha

theorem bNsuccPos {a : CTm Tower.Head n} (ha : CTyped binary Γ a cnat) :
    CTyped binary Γ (call1 nsuccPosN a) cpos :=
  tNsuccPos binaryProgram_admissible (by member_tac) ha

theorem bLow0Pos {a b : CTm Tower.Head n}
    (ha : CTyped binary Γ a cpos)
    (hb : CTyped binary Γ b cpos) :
    CTyped binary Γ (call2 low0PosN a b) cpos :=
  tLow0Pos binaryProgram_admissible (by member_tac) ha hb

theorem bLow0 {a b : CTm Tower.Head n} (ha : CTyped binary Γ a cnat) (hb : CTyped binary Γ b cpos) :
    CTyped binary Γ (call2 low0N a b) cpos :=
  tLow0 binaryProgram_admissible (by member_tac) ha hb

theorem bLow1Pos {a b : CTm Tower.Head n}
    (ha : CTyped binary Γ a cpos)
    (hb : CTyped binary Γ b cpos) :
    CTyped binary Γ (call2 low1PosN a b) cpos :=
  tLow1Pos binaryProgram_admissible (by member_tac) ha hb

theorem bLow1 {a b : CTm Tower.Head n} (ha : CTyped binary Γ a cnat) (hb : CTyped binary Γ b cpos) :
    CTyped binary Γ (call2 low1N a b) cpos :=
  tLow1 binaryProgram_admissible (by member_tac) ha hb

theorem bPaddNat {a b : CTm Tower.Head n}
    (ha : CTyped binary Γ a cpos)
    (hb : CTyped binary Γ b cnat) :
    CTyped binary Γ (call2 paddNatN a b) cpos :=
  tPaddNat binaryProgram_admissible (by member_tac) ha hb

theorem bPadd {a b : CTm Tower.Head n} (ha : CTyped binary Γ a cpos) (hb : CTyped binary Γ b cpos) :
    CTyped binary Γ (call2 paddN a b) cpos :=
  tPadd binaryProgram_admissible (by member_tac) ha hb

theorem bPmul {a b : CTm Tower.Head n} (ha : CTyped binary Γ a cpos) (hb : CTyped binary Γ b cpos) :
    CTyped binary Γ (call2 pmulN a b) cpos :=
  tPmul binaryProgram_admissible (by member_tac) ha hb

theorem bPval {a : CTm Tower.Head n} (ha : CTyped binary Γ a cpos) :
    CTyped binary Γ (call1 pvalN a) cnum :=
  tPval binaryProgram_admissible (by member_tac) ha

theorem bNval {a : CTm Tower.Head n} (ha : CTyped binary Γ a cnat) :
    CTyped binary Γ (call1 nvalN a) cnum :=
  tNval binaryProgram_admissible (by member_tac) ha

theorem bZero :
    CTyped binary Γ (czero) cnum :=
  tZero (withDeclarations_base _ binaryProgram)

theorem bSuc {a : CTm Tower.Head n} (ha : CTyped binary Γ a cnum) :
    CTyped binary Γ (csuc a) cnum :=
  tSuc (withDeclarations_base _ binaryProgram) ha

theorem bAdd {a b : CTm Tower.Head n} (ha : CTyped binary Γ a cnum) (hb : CTyped binary Γ b cnum) :
    CTyped binary Γ (cadd a b) cnum :=
  tAdd (withDeclarations_base _ binaryProgram) ha hb

end Typing

/-! ## The equations are typed computation rules of the binary package -/

section Rules

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- `(psucc one) ≡ (bit0 one)`, at typed arguments. -/
theorem psuccOne_rule :
    CEqual binary Γ (call1 psuccN pone) (pbit0 pone) cpos :=
  definition_equation_holds (D := .recursive psuccDef) (by member_tac) (e := psuccOneEq)
    (by rw [show Definition.equations (.recursive psuccDef) = psuccDef.equations from rfl,
      psuccDef_equations]; member_tac)
    (fun i => i.elim0) (fun j => j.elim0)
    (bPsucc bOne)
    (bBit0 bOne)

/-- `(psucc (bit0 $p)) ≡ (bit1 $p)`, at typed arguments. -/
theorem psuccBit0_rule {p : CTm Tower.Head n}
    (hp : CTyped binary Γ p cpos) :
    CEqual binary Γ (call1 psuccN (pbit0 p)) (pbit1 p) cpos :=
  definition_equation_holds (D := .recursive psuccDef) (by member_tac) (e := psuccBit0Eq)
    (by rw [show Definition.equations (.recursive psuccDef) = psuccDef.equations from rfl,
      psuccDef_equations]; member_tac)
    (fun i => [p].getD i.val p)
    (fun j => match j with | ⟨0, _⟩ => hp)
    (bPsucc (bBit0 hp))
    (bBit1 hp)

/-- `(psucc (bit1 $p)) ≡ (bit0 (psucc $p))`, at typed arguments. -/
theorem psuccBit1_rule {p : CTm Tower.Head n}
    (hp : CTyped binary Γ p cpos) :
    CEqual binary Γ (call1 psuccN (pbit1 p)) (pbit0 (call1 psuccN p)) cpos :=
  definition_equation_holds (D := .recursive psuccDef) (by member_tac) (e := psuccBit1Eq)
    (by rw [show Definition.equations (.recursive psuccDef) = psuccDef.equations from rfl,
      psuccDef_equations]; member_tac)
    (fun i => [p].getD i.val p)
    (fun j => match j with | ⟨0, _⟩ => hp)
    (bPsucc (bBit1 hp))
    (bBit0 (bPsucc hp))

/-- `(phalf one) ≡ n0`, at typed arguments. -/
theorem phalfOne_rule :
    CEqual binary Γ (call1 phalfN pone) (nzero) cnat :=
  definition_equation_holds (D := .recursive phalfDef) (by member_tac) (e := phalfOneEq)
    (by rw [show Definition.equations (.recursive phalfDef) = phalfDef.equations from rfl,
      phalfDef_equations]; member_tac)
    (fun i => i.elim0) (fun j => j.elim0)
    (bPhalf bOne)
    bN0

/-- `(phalf (bit0 $p)) ≡ (npos $p)`, at typed arguments. -/
theorem phalfBit0_rule {p : CTm Tower.Head n}
    (hp : CTyped binary Γ p cpos) :
    CEqual binary Γ (call1 phalfN (pbit0 p)) (npos p) cnat :=
  definition_equation_holds (D := .recursive phalfDef) (by member_tac) (e := phalfBit0Eq)
    (by rw [show Definition.equations (.recursive phalfDef) = phalfDef.equations from rfl,
      phalfDef_equations]; member_tac)
    (fun i => [p].getD i.val p)
    (fun j => match j with | ⟨0, _⟩ => hp)
    (bPhalf (bBit0 hp))
    (bNpos hp)

/-- `(phalf (bit1 $p)) ≡ (npos $p)`, at typed arguments. -/
theorem phalfBit1_rule {p : CTm Tower.Head n}
    (hp : CTyped binary Γ p cpos) :
    CEqual binary Γ (call1 phalfN (pbit1 p)) (npos p) cnat :=
  definition_equation_holds (D := .recursive phalfDef) (by member_tac) (e := phalfBit1Eq)
    (by rw [show Definition.equations (.recursive phalfDef) = phalfDef.equations from rfl,
      phalfDef_equations]; member_tac)
    (fun i => [p].getD i.val p)
    (fun j => match j with | ⟨0, _⟩ => hp)
    (bPhalf (bBit1 hp))
    (bNpos hp)

/-- `(nhalf n0) ≡ n0`, at typed arguments. -/
theorem nhalfZero_rule :
    CEqual binary Γ (call1 nhalfN nzero) (nzero) cnat :=
  definition_equation_holds (D := .recursive nhalfDef) (by member_tac) (e := nhalfZeroEq)
    (by rw [show Definition.equations (.recursive nhalfDef) = nhalfDef.equations from rfl,
      nhalfDef_equations]; member_tac)
    (fun i => i.elim0) (fun j => j.elim0)
    (bNhalf bN0)
    bN0

/-- `(nhalf (npos $q)) ≡ (phalf $q)`, at typed arguments. -/
theorem nhalfPos_rule {q : CTm Tower.Head n}
    (hq : CTyped binary Γ q cpos) :
    CEqual binary Γ (call1 nhalfN (npos q)) (call1 phalfN q) cnat :=
  definition_equation_holds (D := .recursive nhalfDef) (by member_tac) (e := nhalfPosEq)
    (by rw [show Definition.equations (.recursive nhalfDef) = nhalfDef.equations from rfl,
      nhalfDef_equations]; member_tac)
    (fun i => [q].getD i.val q)
    (fun j => match j with | ⟨0, _⟩ => hq)
    (bNhalf (bNpos hq))
    (bPhalf hq)

/-- `(nsucc-pos n0) ≡ one`, at typed arguments. -/
theorem nsuccPosZero_rule :
    CEqual binary Γ (call1 nsuccPosN nzero) (pone) cpos :=
  definition_equation_holds (D := .recursive nsuccPosDef) (by member_tac) (e := nsuccPosZeroEq)
    (by rw [show Definition.equations (.recursive nsuccPosDef) = nsuccPosDef.equations from rfl,
      nsuccPosDef_equations]; member_tac)
    (fun i => i.elim0) (fun j => j.elim0)
    (bNsuccPos bN0)
    bOne

/-- `(nsucc-pos (npos $q)) ≡ (psucc $q)`, at typed arguments. -/
theorem nsuccPosPos_rule {q : CTm Tower.Head n}
    (hq : CTyped binary Γ q cpos) :
    CEqual binary Γ (call1 nsuccPosN (npos q)) (call1 psuccN q) cpos :=
  definition_equation_holds (D := .recursive nsuccPosDef) (by member_tac) (e := nsuccPosPosEq)
    (by rw [show Definition.equations (.recursive nsuccPosDef) = nsuccPosDef.equations from rfl,
      nsuccPosDef_equations]; member_tac)
    (fun i => [q].getD i.val q)
    (fun j => match j with | ⟨0, _⟩ => hq)
    (bNsuccPos (bNpos hq))
    (bPsucc hq)

/-- `(low0-pos one $r) ≡ (bit1 $r)`, at typed arguments. -/
theorem low0PosOne_rule {r : CTm Tower.Head n}
    (hr : CTyped binary Γ r cpos) :
    CEqual binary Γ (call2 low0PosN pone r) (pbit1 r) cpos :=
  definition_equation_holds (D := .recursive low0PosDef) (by member_tac) (e := low0PosOneEq)
    (by rw [show Definition.equations (.recursive low0PosDef) = low0PosDef.equations from rfl,
      low0PosDef_equations]; member_tac)
    (fun i => [r].getD i.val r)
    (fun j => match j with | ⟨0, _⟩ => hr)
    (bLow0Pos bOne hr)
    (bBit1 hr)

/-- `(low0-pos (bit0 $q) $r) ≡ (bit0 $r)`, at typed arguments. -/
theorem low0PosBit0_rule {q r : CTm Tower.Head n}
    (hq : CTyped binary Γ q cpos)
    (hr : CTyped binary Γ r cpos) :
    CEqual binary Γ (call2 low0PosN (pbit0 q) r) (pbit0 r) cpos :=
  definition_equation_holds (D := .recursive low0PosDef) (by member_tac) (e := low0PosBit0Eq)
    (by rw [show Definition.equations (.recursive low0PosDef) = low0PosDef.equations from rfl,
      low0PosDef_equations]; member_tac)
    (fun i => [r, q].getD i.val q)
    (fun j => match j with | ⟨0, _⟩ => hr | ⟨1, _⟩ => hq)
    (bLow0Pos (bBit0 hq) hr)
    (bBit0 hr)

/-- `(low0-pos (bit1 $q) $r) ≡ (bit1 $r)`, at typed arguments. -/
theorem low0PosBit1_rule {q r : CTm Tower.Head n}
    (hq : CTyped binary Γ q cpos)
    (hr : CTyped binary Γ r cpos) :
    CEqual binary Γ (call2 low0PosN (pbit1 q) r) (pbit1 r) cpos :=
  definition_equation_holds (D := .recursive low0PosDef) (by member_tac) (e := low0PosBit1Eq)
    (by rw [show Definition.equations (.recursive low0PosDef) = low0PosDef.equations from rfl,
      low0PosDef_equations]; member_tac)
    (fun i => [r, q].getD i.val q)
    (fun j => match j with | ⟨0, _⟩ => hr | ⟨1, _⟩ => hq)
    (bLow0Pos (bBit1 hq) hr)
    (bBit1 hr)

/-- `(low0 n0 $r) ≡ (bit0 $r)`, at typed arguments. -/
theorem low0Zero_rule {r : CTm Tower.Head n}
    (hr : CTyped binary Γ r cpos) :
    CEqual binary Γ (call2 low0N nzero r) (pbit0 r) cpos :=
  definition_equation_holds (D := .recursive low0Def) (by member_tac) (e := low0ZeroEq)
    (by rw [show Definition.equations (.recursive low0Def) = low0Def.equations from rfl,
      low0Def_equations]; member_tac)
    (fun i => [r].getD i.val r)
    (fun j => match j with | ⟨0, _⟩ => hr)
    (bLow0 bN0 hr)
    (bBit0 hr)

/-- `(low0 (npos $q) $r) ≡ (low0-pos $q $r)`, at typed arguments. -/
theorem low0Pos_rule {q r : CTm Tower.Head n}
    (hq : CTyped binary Γ q cpos)
    (hr : CTyped binary Γ r cpos) :
    CEqual binary Γ (call2 low0N (npos q) r) (call2 low0PosN q r) cpos :=
  definition_equation_holds (D := .recursive low0Def) (by member_tac) (e := low0PosEq)
    (by rw [show Definition.equations (.recursive low0Def) = low0Def.equations from rfl,
      low0Def_equations]; member_tac)
    (fun i => [r, q].getD i.val q)
    (fun j => match j with | ⟨0, _⟩ => hr | ⟨1, _⟩ => hq)
    (bLow0 (bNpos hq) hr)
    (bLow0Pos hq hr)

/-- `(low1-pos one $r) ≡ (bit0 (psucc $r))`, at typed arguments. -/
theorem low1PosOne_rule {r : CTm Tower.Head n}
    (hr : CTyped binary Γ r cpos) :
    CEqual binary Γ (call2 low1PosN pone r) (pbit0 (call1 psuccN r)) cpos :=
  definition_equation_holds (D := .recursive low1PosDef) (by member_tac) (e := low1PosOneEq)
    (by rw [show Definition.equations (.recursive low1PosDef) = low1PosDef.equations from rfl,
      low1PosDef_equations]; member_tac)
    (fun i => [r].getD i.val r)
    (fun j => match j with | ⟨0, _⟩ => hr)
    (bLow1Pos bOne hr)
    (bBit0 (bPsucc hr))

/-- `(low1-pos (bit0 $q) $r) ≡ (bit1 $r)`, at typed arguments. -/
theorem low1PosBit0_rule {q r : CTm Tower.Head n}
    (hq : CTyped binary Γ q cpos)
    (hr : CTyped binary Γ r cpos) :
    CEqual binary Γ (call2 low1PosN (pbit0 q) r) (pbit1 r) cpos :=
  definition_equation_holds (D := .recursive low1PosDef) (by member_tac) (e := low1PosBit0Eq)
    (by rw [show Definition.equations (.recursive low1PosDef) = low1PosDef.equations from rfl,
      low1PosDef_equations]; member_tac)
    (fun i => [r, q].getD i.val q)
    (fun j => match j with | ⟨0, _⟩ => hr | ⟨1, _⟩ => hq)
    (bLow1Pos (bBit0 hq) hr)
    (bBit1 hr)

/-- `(low1-pos (bit1 $q) $r) ≡ (bit0 (psucc $r))`, at typed arguments. -/
theorem low1PosBit1_rule {q r : CTm Tower.Head n}
    (hq : CTyped binary Γ q cpos)
    (hr : CTyped binary Γ r cpos) :
    CEqual binary Γ (call2 low1PosN (pbit1 q) r) (pbit0 (call1 psuccN r)) cpos :=
  definition_equation_holds (D := .recursive low1PosDef) (by member_tac) (e := low1PosBit1Eq)
    (by rw [show Definition.equations (.recursive low1PosDef) = low1PosDef.equations from rfl,
      low1PosDef_equations]; member_tac)
    (fun i => [r, q].getD i.val q)
    (fun j => match j with | ⟨0, _⟩ => hr | ⟨1, _⟩ => hq)
    (bLow1Pos (bBit1 hq) hr)
    (bBit0 (bPsucc hr))

/-- `(low1 n0 $r) ≡ (bit1 $r)`, at typed arguments. -/
theorem low1Zero_rule {r : CTm Tower.Head n}
    (hr : CTyped binary Γ r cpos) :
    CEqual binary Γ (call2 low1N nzero r) (pbit1 r) cpos :=
  definition_equation_holds (D := .recursive low1Def) (by member_tac) (e := low1ZeroEq)
    (by rw [show Definition.equations (.recursive low1Def) = low1Def.equations from rfl,
      low1Def_equations]; member_tac)
    (fun i => [r].getD i.val r)
    (fun j => match j with | ⟨0, _⟩ => hr)
    (bLow1 bN0 hr)
    (bBit1 hr)

/-- `(low1 (npos $q) $r) ≡ (low1-pos $q $r)`, at typed arguments. -/
theorem low1Pos_rule {q r : CTm Tower.Head n}
    (hq : CTyped binary Γ q cpos)
    (hr : CTyped binary Γ r cpos) :
    CEqual binary Γ (call2 low1N (npos q) r) (call2 low1PosN q r) cpos :=
  definition_equation_holds (D := .recursive low1Def) (by member_tac) (e := low1PosEq)
    (by rw [show Definition.equations (.recursive low1Def) = low1Def.equations from rfl,
      low1Def_equations]; member_tac)
    (fun i => [r, q].getD i.val q)
    (fun j => match j with | ⟨0, _⟩ => hr | ⟨1, _⟩ => hq)
    (bLow1 (bNpos hq) hr)
    (bLow1Pos hq hr)

/-- `(padd-nat one $m) ≡ (nsucc-pos $m)`, at typed arguments. -/
theorem paddNatOne_rule {m : CTm Tower.Head n}
    (hm : CTyped binary Γ m cnat) :
    CEqual binary Γ (call2 paddNatN pone m) (call1 nsuccPosN m) cpos :=
  definition_equation_holds (D := .recursive paddNatDef) (by member_tac) (e := paddNatOneEq)
    (by rw [show Definition.equations (.recursive paddNatDef) = paddNatDef.equations from rfl,
      paddNatDef_equations]; member_tac)
    (fun i => [m].getD i.val m)
    (fun j => match j with | ⟨0, _⟩ => hm)
    (bPaddNat bOne hm)
    (bNsuccPos hm)

/-- `(padd-nat (bit0 $p) $m) ≡ (low0 $m (padd-nat $p (nhalf $m)))`, at typed arguments. -/
theorem paddNatBit0_rule {p m : CTm Tower.Head n}
    (hp : CTyped binary Γ p cpos)
    (hm : CTyped binary Γ m cnat) :
    CEqual binary Γ (call2 paddNatN (pbit0 p) m)
      (call2 low0N m (call2 paddNatN p (call1 nhalfN m))) cpos :=
  definition_equation_holds (D := .recursive paddNatDef) (by member_tac) (e := paddNatBit0Eq)
    (by rw [show Definition.equations (.recursive paddNatDef) = paddNatDef.equations from rfl,
      paddNatDef_equations]; member_tac)
    (fun i => [m, p].getD i.val p)
    (fun j => match j with | ⟨0, _⟩ => hm | ⟨1, _⟩ => hp)
    (bPaddNat (bBit0 hp) hm)
    (bLow0 hm (bPaddNat hp (bNhalf hm)))

/-- `(padd-nat (bit1 $p) $m) ≡ (low1 $m (padd-nat $p (nhalf $m)))`, at typed arguments. -/
theorem paddNatBit1_rule {p m : CTm Tower.Head n}
    (hp : CTyped binary Γ p cpos)
    (hm : CTyped binary Γ m cnat) :
    CEqual binary Γ (call2 paddNatN (pbit1 p) m)
      (call2 low1N m (call2 paddNatN p (call1 nhalfN m))) cpos :=
  definition_equation_holds (D := .recursive paddNatDef) (by member_tac) (e := paddNatBit1Eq)
    (by rw [show Definition.equations (.recursive paddNatDef) = paddNatDef.equations from rfl,
      paddNatDef_equations]; member_tac)
    (fun i => [m, p].getD i.val p)
    (fun j => match j with | ⟨0, _⟩ => hm | ⟨1, _⟩ => hp)
    (bPaddNat (bBit1 hp) hm)
    (bLow1 hm (bPaddNat hp (bNhalf hm)))

/-- `(padd $p $q) ≡ (padd-nat $p (npos $q))`, at typed arguments. -/
theorem paddEq_rule {p q : CTm Tower.Head n}
    (hp : CTyped binary Γ p cpos)
    (hq : CTyped binary Γ q cpos) :
    CEqual binary Γ (call2 paddN p q) (call2 paddNatN p (npos q)) cpos :=
  definition_equation_holds (D := .explicit paddDef) (by member_tac) (e := paddEqEq)
    (by rw [show Definition.equations (.explicit paddDef) = paddDef.equations from rfl,
      paddDef_equations]; member_tac)
    (fun i => [q, p].getD i.val p)
    (fun j => match j with | ⟨0, _⟩ => hq | ⟨1, _⟩ => hp)
    (bPadd hp hq)
    (bPaddNat hp (bNpos hq))

/-- `(pmul one $q) ≡ $q`, at typed arguments. -/
theorem pmulOne_rule {q : CTm Tower.Head n}
    (hq : CTyped binary Γ q cpos) :
    CEqual binary Γ (call2 pmulN pone q) (q) cpos :=
  definition_equation_holds (D := .recursive pmulDef) (by member_tac) (e := pmulOneEq)
    (by rw [show Definition.equations (.recursive pmulDef) = pmulDef.equations from rfl,
      pmulDef_equations]; member_tac)
    (fun i => [q].getD i.val q)
    (fun j => match j with | ⟨0, _⟩ => hq)
    (bPmul bOne hq)
    hq

/-- `(pmul (bit0 $p) $q) ≡ (bit0 (pmul $p $q))`, at typed arguments. -/
theorem pmulBit0_rule {p q : CTm Tower.Head n}
    (hp : CTyped binary Γ p cpos)
    (hq : CTyped binary Γ q cpos) :
    CEqual binary Γ (call2 pmulN (pbit0 p) q) (pbit0 (call2 pmulN p q)) cpos :=
  definition_equation_holds (D := .recursive pmulDef) (by member_tac) (e := pmulBit0Eq)
    (by rw [show Definition.equations (.recursive pmulDef) = pmulDef.equations from rfl,
      pmulDef_equations]; member_tac)
    (fun i => [q, p].getD i.val p)
    (fun j => match j with | ⟨0, _⟩ => hq | ⟨1, _⟩ => hp)
    (bPmul (bBit0 hp) hq)
    (bBit0 (bPmul hp hq))

/-- `(pmul (bit1 $p) $q) ≡ (padd $q (bit0 (pmul $p $q)))`, at typed arguments. -/
theorem pmulBit1_rule {p q : CTm Tower.Head n}
    (hp : CTyped binary Γ p cpos)
    (hq : CTyped binary Γ q cpos) :
    CEqual binary Γ (call2 pmulN (pbit1 p) q) (call2 paddN q (pbit0 (call2 pmulN p q))) cpos :=
  definition_equation_holds (D := .recursive pmulDef) (by member_tac) (e := pmulBit1Eq)
    (by rw [show Definition.equations (.recursive pmulDef) = pmulDef.equations from rfl,
      pmulDef_equations]; member_tac)
    (fun i => [q, p].getD i.val p)
    (fun j => match j with | ⟨0, _⟩ => hq | ⟨1, _⟩ => hp)
    (bPmul (bBit1 hp) hq)
    (bPadd hq (bBit0 (bPmul hp hq)))

/-- `(pval one) ≡ (suc zero)`, at typed arguments. -/
theorem pvalOne_rule :
    CEqual binary Γ (call1 pvalN pone) (csuc czero) cnum :=
  definition_equation_holds (D := .recursive pvalDef) (by member_tac) (e := pvalOneEq)
    (by rw [show Definition.equations (.recursive pvalDef) = pvalDef.equations from rfl,
      pvalDef_equations]; member_tac)
    (fun i => i.elim0) (fun j => j.elim0)
    (bPval bOne)
    (bSuc bZero)

/-- `(pval (bit0 $p)) ≡ (add (pval $p) (pval $p))`, at typed arguments. -/
theorem pvalBit0_rule {p : CTm Tower.Head n}
    (hp : CTyped binary Γ p cpos) :
    CEqual binary Γ (call1 pvalN (pbit0 p)) (cadd (call1 pvalN p) (call1 pvalN p)) cnum :=
  definition_equation_holds (D := .recursive pvalDef) (by member_tac) (e := pvalBit0Eq)
    (by rw [show Definition.equations (.recursive pvalDef) = pvalDef.equations from rfl,
      pvalDef_equations]; member_tac)
    (fun i => [p].getD i.val p)
    (fun j => match j with | ⟨0, _⟩ => hp)
    (bPval (bBit0 hp))
    (bAdd (bPval hp) (bPval hp))

/-- `(pval (bit1 $p)) ≡ (suc (add (pval $p) (pval $p)))`, at typed arguments. -/
theorem pvalBit1_rule {p : CTm Tower.Head n}
    (hp : CTyped binary Γ p cpos) :
    CEqual binary Γ (call1 pvalN (pbit1 p)) (csuc (cadd (call1 pvalN p) (call1 pvalN p))) cnum :=
  definition_equation_holds (D := .recursive pvalDef) (by member_tac) (e := pvalBit1Eq)
    (by rw [show Definition.equations (.recursive pvalDef) = pvalDef.equations from rfl,
      pvalDef_equations]; member_tac)
    (fun i => [p].getD i.val p)
    (fun j => match j with | ⟨0, _⟩ => hp)
    (bPval (bBit1 hp))
    (bSuc (bAdd (bPval hp) (bPval hp)))

/-- `(nval n0) ≡ zero`, at typed arguments. -/
theorem nvalZero_rule :
    CEqual binary Γ (call1 nvalN nzero) (czero) cnum :=
  definition_equation_holds (D := .recursive nvalDef) (by member_tac) (e := nvalZeroEq)
    (by rw [show Definition.equations (.recursive nvalDef) = nvalDef.equations from rfl,
      nvalDef_equations]; member_tac)
    (fun i => i.elim0) (fun j => j.elim0)
    (bNval bN0)
    bZero

/-- `(nval (npos $q)) ≡ (pval $q)`, at typed arguments. -/
theorem nvalPos_rule {q : CTm Tower.Head n}
    (hq : CTyped binary Γ q cpos) :
    CEqual binary Γ (call1 nvalN (npos q)) (call1 pvalN q) cnum :=
  definition_equation_holds (D := .recursive nvalDef) (by member_tac) (e := nvalPosEq)
    (by rw [show Definition.equations (.recursive nvalDef) = nvalDef.equations from rfl,
      nvalDef_equations]; member_tac)
    (fun i => [q].getD i.val q)
    (fun j => match j with | ⟨0, _⟩ => hq)
    (bNval (bNpos hq))
    (bPval hq)

end Rules


/-- A context of one variable. -/
abbrev ctx1 (A : CTm Tower.Head 0) : CCtx Tower.Head 1 := .snoc .nil A

/-- A context of two variables. -/
abbrev ctx2 (A : CTm Tower.Head 0) (B : CTm Tower.Head 1) : CCtx Tower.Head 2 :=
  .snoc (.snoc .nil A) B

/-! ## The set model, and the value of a binary number -/

section Model

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetTraceProducts (traceApp)

universe u

variable (h : CofinalInaccessibles.{u})

/-- **The binary package has a set model**, relative to `CofinalInaccessibles`, by the
criterion for admissible lists of declarations over the object package. -/
theorem binary_model :
    SetModel (objHeads h) (objectDeclarationsConsts h binaryProgram) binary :=
  objectDeclarations_model h binaryProgram_admissible

include h in
/-- **Consistency**: no closed term of the binary package has the type `Π (X : U₀). X`. -/
theorem binary_consistent (t : CTm Tower.Head 0) : ¬ CTyped binary .nil t emptyType :=
  objectDeclarations_consistent h binaryProgram_admissible t

/-- The values of the constants in the model. -/
noncomputable abbrev val : DeclName → ZFSet.{u} := objectDeclarationsConsts h binaryProgram

/-- A constant of one argument applied in the model. -/
noncomputable abbrev ap1 (f : DeclName) (x : ZFSet.{u}) : ZFSet.{u} := traceApp (val h f) x

/-- A constant of two arguments applied in the model. -/
noncomputable abbrev ap2 (f : DeclName) (x y : ZFSet.{u}) : ZFSet.{u} :=
  traceApp (traceApp (val h f) x) y

/-- **The value of a positive number** in the naturals: the number the model's `pval` gives. -/
noncomputable def pv (x : ZFSet.{u}) : ℕ := natOf (ap1 h pvalN x)

/-- The value of a natural number in the naturals. -/
noncomputable def nv (y : ZFSet.{u}) : ℕ := natOf (ap1 h nvalN y)

/-! ### From the judgment to the model -/

theorem rule0 {l r T : CTm Tower.Head 0} (e : CEqual binary .nil l r T) :
    ev (objHeads h) (val h) l Fin.elim0 = ev (objHeads h) (val h) r Fin.elim0 :=
  (objectDeclarations_sound h binaryProgram_admissible e Fin.elim0 (sat_nil _ _ _)).1

theorem rule1 {A : DeclName} {l r T : CTm Tower.Head 1}
    (e : CEqual binary (.snoc .nil (.const A)) l r T) {x : ZFSet.{u}} (hx : x ∈ val h A) :
    ev (objHeads h) (val h) l (extend Fin.elim0 x) =
      ev (objHeads h) (val h) r (extend Fin.elim0 x) :=
  (objectDeclarations_sound h binaryProgram_admissible e _
    ((sat_snoc _ _).mpr ⟨sat_nil _ _ _, hx⟩)).1

theorem rule2 {A B : DeclName} {l r T : CTm Tower.Head 2}
    (e : CEqual binary (.snoc (.snoc .nil (.const A)) (.const B)) l r T) {x y : ZFSet.{u}}
    (hx : x ∈ val h A) (hy : y ∈ val h B) :
    ev (objHeads h) (val h) l (extend (extend Fin.elim0 x) y) =
      ev (objHeads h) (val h) r (extend (extend Fin.elim0 x) y) :=
  (objectDeclarations_sound h binaryProgram_admissible e _
    ((sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ _, hx⟩, hy⟩)).1

theorem typed0 {B : DeclName} {t : CTm Tower.Head 0} (e : CTyped binary .nil t (.const B)) :
    ev (objHeads h) (val h) t Fin.elim0 ∈ val h B :=
  objectDeclarations_sound h binaryProgram_admissible e Fin.elim0 (sat_nil _ _ _)

theorem typed1 {A B : DeclName} {t : CTm Tower.Head 1}
    (e : CTyped binary (.snoc .nil (.const A)) t (.const B)) {x : ZFSet.{u}} (hx : x ∈ val h A) :
    ev (objHeads h) (val h) t (extend Fin.elim0 x) ∈ val h B :=
  objectDeclarations_sound h binaryProgram_admissible e _ ((sat_snoc _ _).mpr ⟨sat_nil _ _ _, hx⟩)

theorem typed2 {A B C : DeclName} {t : CTm Tower.Head 2}
    (e : CTyped binary (.snoc (.snoc .nil (.const A)) (.const B)) t (.const C)) {x y : ZFSet.{u}}
    (hx : x ∈ val h A) (hy : y ∈ val h B) :
    ev (objHeads h) (val h) t (extend (extend Fin.elim0 x) y) ∈ val h C :=
  objectDeclarations_sound h binaryProgram_admissible e _
    ((sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ _, hx⟩, hy⟩)

/-! ### The numbers of the object package in the model -/

theorem val_base {c : DeclName} (declared : objectDeclared c = true) :
    val h c = objectSetConsts h c :=
  declarationsConsts_base objectChurch (objectChurch_constantType_ne_none declared) binaryProgram
    binaryProgram_admissible

theorem val_num : val h numN = ZFSet.omega := by
  rw [val_base h (by decide)]; exact setConst_num h

theorem val_zero : val h zeroN = numeral 0 := by
  rw [val_base h (by decide)]; exact setConst_zero h

theorem val_suc_apply {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) :
    traceApp (val h sucN) x = insert x x := by
  rw [val_base h (by decide)]; exact suc_apply h hx

theorem val_add_apply {a b : ZFSet.{u}} (ha : a ∈ ZFSet.omega) (hb : b ∈ ZFSet.omega) :
    traceApp (traceApp (val h addN) a) b = numeral (natOf a + natOf b) := by
  rw [val_base h (by decide)]; exact add_apply h ha hb

/-! ### The datatypes in the model, and their induction -/

theorem posReading :
    InductiveReading (objHeads h) (val h) posN listMotives posCtors posRecN :=
  declarations_reading (heads := objHeads h) (base := objectSetConsts h) objectChurch
    binaryProgram binaryProgram_admissible posDecl (by member_tac) (val h) fun _ _ => rfl

theorem natReading :
    InductiveReading (objHeads h) (val h) natN listMotives natCtors natRecN :=
  declarations_reading (heads := objHeads h) (base := objectSetConsts h) objectChurch
    binaryProgram binaryProgram_admissible natDecl (by member_tac) (val h) fun _ _ => rfl

section Members

variable {a b : ZFSet.{u}}

theorem one_mem : val h oneN ∈ val h posN :=
  typed0 h (tOne binaryProgram_admissible (by member_tac))

theorem bit0_mem (ha : a ∈ val h posN) : ap1 h bit0N a ∈ val h posN :=
  typed1 h (tBit0 binaryProgram_admissible (by member_tac) (Γ := .snoc .nil cpos) (.var 0)) ha

theorem bit1_mem (ha : a ∈ val h posN) : ap1 h bit1N a ∈ val h posN :=
  typed1 h (tBit1 binaryProgram_admissible (by member_tac) (Γ := .snoc .nil cpos) (.var 0)) ha

theorem n0_mem : val h n0N ∈ val h natN :=
  typed0 h (tN0 binaryProgram_admissible (by member_tac))

theorem npos_mem (ha : a ∈ val h posN) : ap1 h nposN a ∈ val h natN :=
  typed1 h (tNpos binaryProgram_admissible (by member_tac) (Γ := .snoc .nil cpos) (.var 0)) ha

theorem psucc_mem (ha : a ∈ val h posN) : ap1 h psuccN a ∈ val h posN :=
  typed1 h (tPsucc binaryProgram_admissible (by member_tac) (Γ := .snoc .nil cpos) (.var 0)) ha

theorem nhalf_mem (ha : a ∈ val h natN) : ap1 h nhalfN a ∈ val h natN :=
  typed1 h (tNhalf binaryProgram_admissible (by member_tac) (Γ := .snoc .nil cnat) (.var 0)) ha

theorem paddNat_mem (ha : a ∈ val h posN) (hb : b ∈ val h natN) :
    ap2 h paddNatN a b ∈ val h posN :=
  typed2 h (tPaddNat binaryProgram_admissible (by member_tac)
    (Γ := .snoc (.snoc .nil cpos) cnat) (.var 1) (.var 0)) ha hb

theorem pmul_mem (ha : a ∈ val h posN) (hb : b ∈ val h posN) :
    ap2 h pmulN a b ∈ val h posN :=
  typed2 h (tPmul binaryProgram_admissible (by member_tac)
    (Γ := .snoc (.snoc .nil cpos) cpos) (.var 1) (.var 0)) ha hb

theorem pval_mem (ha : a ∈ val h posN) : ap1 h pvalN a ∈ ZFSet.omega := by
  rw [← val_num h]
  exact typed1 h (tPval binaryProgram_admissible (by member_tac) (Γ := .snoc .nil cpos) (.var 0)) ha

end Members

/-- **Induction on the positive numbers of the model**: a property of one, kept by the two
digits, holds of every member of the set of positive numbers. -/
theorem pos_induct {Q : ZFSet.{u} → Prop} (hOne : Q (val h oneN))
    (h0 : ∀ a ∈ val h posN, Q a → Q (ap1 h bit0N a))
    (h1 : ∀ a ∈ val h posN, Q a → Q (ap1 h bit1N a)) :
    ∀ x ∈ val h posN, Q x := by
  intro x hx
  have reading := posReading h
  have hx' := hx
  rw [reading.type] at hx'
  refine (ZFSetInductive.carrier_induct (P := fun y => y ∈ val h posN ∧ Q y) ?_ hx').2
  intro i c args atIndex fitting
  obtain ⟨k, fields, entry, rfl⟩ := exists_of_signature_getElem? (objHeads h) (val h) atIndex
  rcases posCtors_entry entry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases fitting
    rw [← reading.constant_value entry]
    exact ⟨one_mem h, hOne⟩
  · cases fitting with
    | recursive ha rest =>
      cases rest
      rw [← reading.apply entry _ (.recursive ha.1 .nil)]
      exact ⟨bit0_mem h ha.1, h0 _ ha.1 ha.2⟩
  · cases fitting with
    | recursive ha rest =>
      cases rest
      rw [← reading.apply entry _ (.recursive ha.1 .nil)]
      exact ⟨bit1_mem h ha.1, h1 _ ha.1 ha.2⟩

/-- **Cases on the natural numbers of the model**: zero, or a positive number. -/
theorem nat_cases {Q : ZFSet.{u} → Prop} (hZero : Q (val h n0N))
    (hPos : ∀ a ∈ val h posN, Q (ap1 h nposN a)) :
    ∀ y ∈ val h natN, Q y := by
  intro y hy
  have reading := natReading h
  have hy' := hy
  rw [reading.type] at hy'
  refine (ZFSetInductive.carrier_induct (P := fun z => z ∈ val h natN ∧ Q z) ?_ hy').2
  intro i c args atIndex fitting
  obtain ⟨k, fields, entry, rfl⟩ := exists_of_signature_getElem? (objHeads h) (val h) atIndex
  rcases natCtors_entry entry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases fitting
    rw [← reading.constant_value entry]
    exact ⟨n0_mem h, hZero⟩
  · cases fitting with
    | ofSet ha rest =>
      cases rest
      rw [← reading.apply entry _ (.ofSet ha .nil)]
      exact ⟨npos_mem h ha, hPos _ ha⟩

/-! ### The written equations in the model -/

section Equations

variable {a b : ZFSet.{u}}


theorem psucc_one_v : ap1 h psuccN (val h oneN) = ap1 h bit0N (val h oneN) :=
  rule0 h (psuccOne_rule (Γ := .nil))

theorem psucc_bit0_v (ha : a ∈ val h posN) : ap1 h psuccN (ap1 h bit0N a) = ap1 h bit1N a :=
  rule1 h (psuccBit0_rule (Γ := ctx1 cpos) (.var 0)) ha

theorem psucc_bit1_v (ha : a ∈ val h posN) :
    ap1 h psuccN (ap1 h bit1N a) = ap1 h bit0N (ap1 h psuccN a) :=
  rule1 h (psuccBit1_rule (Γ := ctx1 cpos) (.var 0)) ha

theorem phalf_one_v : ap1 h phalfN (val h oneN) = val h n0N :=
  rule0 h (phalfOne_rule (Γ := .nil))

theorem phalf_bit0_v (ha : a ∈ val h posN) : ap1 h phalfN (ap1 h bit0N a) = ap1 h nposN a :=
  rule1 h (phalfBit0_rule (Γ := ctx1 cpos) (.var 0)) ha

theorem phalf_bit1_v (ha : a ∈ val h posN) : ap1 h phalfN (ap1 h bit1N a) = ap1 h nposN a :=
  rule1 h (phalfBit1_rule (Γ := ctx1 cpos) (.var 0)) ha

theorem nhalf_zero_v : ap1 h nhalfN (val h n0N) = val h n0N :=
  rule0 h (nhalfZero_rule (Γ := .nil))

theorem nhalf_pos_v (ha : a ∈ val h posN) : ap1 h nhalfN (ap1 h nposN a) = ap1 h phalfN a :=
  rule1 h (nhalfPos_rule (Γ := ctx1 cpos) (.var 0)) ha

theorem nsuccPos_zero_v : ap1 h nsuccPosN (val h n0N) = val h oneN :=
  rule0 h (nsuccPosZero_rule (Γ := .nil))

theorem nsuccPos_pos_v (ha : a ∈ val h posN) : ap1 h nsuccPosN (ap1 h nposN a) = ap1 h psuccN a :=
  rule1 h (nsuccPosPos_rule (Γ := ctx1 cpos) (.var 0)) ha

theorem low0Pos_one_v (hb : b ∈ val h posN) : ap2 h low0PosN (val h oneN) b = ap1 h bit1N b :=
  rule1 h (low0PosOne_rule (Γ := ctx1 cpos) (.var 0)) hb

theorem low0Pos_bit0_v (ha : a ∈ val h posN) (hb : b ∈ val h posN) :
    ap2 h low0PosN (ap1 h bit0N a) b = ap1 h bit0N b :=
  rule2 h (low0PosBit0_rule (Γ := ctx2 cpos cpos) (.var 1) (.var 0)) ha hb

theorem low0Pos_bit1_v (ha : a ∈ val h posN) (hb : b ∈ val h posN) :
    ap2 h low0PosN (ap1 h bit1N a) b = ap1 h bit1N b :=
  rule2 h (low0PosBit1_rule (Γ := ctx2 cpos cpos) (.var 1) (.var 0)) ha hb

theorem low0_zero_v (hb : b ∈ val h posN) : ap2 h low0N (val h n0N) b = ap1 h bit0N b :=
  rule1 h (low0Zero_rule (Γ := ctx1 cpos) (.var 0)) hb

theorem low0_pos_v (ha : a ∈ val h posN) (hb : b ∈ val h posN) :
    ap2 h low0N (ap1 h nposN a) b = ap2 h low0PosN a b :=
  rule2 h (low0Pos_rule (Γ := ctx2 cpos cpos) (.var 1) (.var 0)) ha hb

theorem low1Pos_one_v (hb : b ∈ val h posN) :
    ap2 h low1PosN (val h oneN) b = ap1 h bit0N (ap1 h psuccN b) :=
  rule1 h (low1PosOne_rule (Γ := ctx1 cpos) (.var 0)) hb

theorem low1Pos_bit0_v (ha : a ∈ val h posN) (hb : b ∈ val h posN) :
    ap2 h low1PosN (ap1 h bit0N a) b = ap1 h bit1N b :=
  rule2 h (low1PosBit0_rule (Γ := ctx2 cpos cpos) (.var 1) (.var 0)) ha hb

theorem low1Pos_bit1_v (ha : a ∈ val h posN) (hb : b ∈ val h posN) :
    ap2 h low1PosN (ap1 h bit1N a) b = ap1 h bit0N (ap1 h psuccN b) :=
  rule2 h (low1PosBit1_rule (Γ := ctx2 cpos cpos) (.var 1) (.var 0)) ha hb

theorem low1_zero_v (hb : b ∈ val h posN) : ap2 h low1N (val h n0N) b = ap1 h bit1N b :=
  rule1 h (low1Zero_rule (Γ := ctx1 cpos) (.var 0)) hb

theorem low1_pos_v (ha : a ∈ val h posN) (hb : b ∈ val h posN) :
    ap2 h low1N (ap1 h nposN a) b = ap2 h low1PosN a b :=
  rule2 h (low1Pos_rule (Γ := ctx2 cpos cpos) (.var 1) (.var 0)) ha hb

theorem paddNat_one_v (hb : b ∈ val h natN) : ap2 h paddNatN (val h oneN) b = ap1 h nsuccPosN b :=
  rule1 h (paddNatOne_rule (Γ := ctx1 cnat) (.var 0)) hb

theorem paddNat_bit0_v (ha : a ∈ val h posN) (hb : b ∈ val h natN) :
    ap2 h paddNatN (ap1 h bit0N a) b = ap2 h low0N b (ap2 h paddNatN a (ap1 h nhalfN b)) :=
  rule2 h (paddNatBit0_rule (Γ := ctx2 cpos cnat) (.var 1) (.var 0)) ha hb

theorem paddNat_bit1_v (ha : a ∈ val h posN) (hb : b ∈ val h natN) :
    ap2 h paddNatN (ap1 h bit1N a) b = ap2 h low1N b (ap2 h paddNatN a (ap1 h nhalfN b)) :=
  rule2 h (paddNatBit1_rule (Γ := ctx2 cpos cnat) (.var 1) (.var 0)) ha hb

theorem padd_v (ha : a ∈ val h posN) (hb : b ∈ val h posN) :
    ap2 h paddN a b = ap2 h paddNatN a (ap1 h nposN b) :=
  rule2 h (paddEq_rule (Γ := ctx2 cpos cpos) (.var 1) (.var 0)) ha hb

theorem pmul_one_v (hb : b ∈ val h posN) : ap2 h pmulN (val h oneN) b = b :=
  rule1 h (pmulOne_rule (Γ := ctx1 cpos) (.var 0)) hb

theorem pmul_bit0_v (ha : a ∈ val h posN) (hb : b ∈ val h posN) :
    ap2 h pmulN (ap1 h bit0N a) b = ap1 h bit0N (ap2 h pmulN a b) :=
  rule2 h (pmulBit0_rule (Γ := ctx2 cpos cpos) (.var 1) (.var 0)) ha hb

theorem pmul_bit1_v (ha : a ∈ val h posN) (hb : b ∈ val h posN) :
    ap2 h pmulN (ap1 h bit1N a) b = ap2 h paddN b (ap1 h bit0N (ap2 h pmulN a b)) :=
  rule2 h (pmulBit1_rule (Γ := ctx2 cpos cpos) (.var 1) (.var 0)) ha hb

theorem pval_one_v : ap1 h pvalN (val h oneN) = traceApp (val h sucN) (val h zeroN) :=
  rule0 h (pvalOne_rule (Γ := .nil))

theorem pval_bit0_v (ha : a ∈ val h posN) :
    ap1 h pvalN (ap1 h bit0N a) = ap2 h addN (ap1 h pvalN a) (ap1 h pvalN a) :=
  rule1 h (pvalBit0_rule (Γ := ctx1 cpos) (.var 0)) ha

theorem pval_bit1_v (ha : a ∈ val h posN) :
    ap1 h pvalN (ap1 h bit1N a) =
      traceApp (val h sucN) (ap2 h addN (ap1 h pvalN a) (ap1 h pvalN a)) :=
  rule1 h (pvalBit1_rule (Γ := ctx1 cpos) (.var 0)) ha

theorem nval_zero_v : ap1 h nvalN (val h n0N) = val h zeroN :=
  rule0 h (nvalZero_rule (Γ := .nil))

theorem nval_pos_v (ha : a ∈ val h posN) : ap1 h nvalN (ap1 h nposN a) = ap1 h pvalN a :=
  rule1 h (nvalPos_rule (Γ := ctx1 cpos) (.var 0)) ha

end Equations

/-! ### The value map -/

section Values

variable {a b : ZFSet.{u}}

theorem add_ap2 (ha : a ∈ ZFSet.omega) (hb : b ∈ ZFSet.omega) :
    ap2 h addN a b = numeral (natOf a + natOf b) :=
  val_add_apply h ha hb

theorem pv_one : pv h (val h oneN) = 1 := by
  rw [pv, pval_one_v, val_zero, val_suc_apply h (numeral_mem_omega 0), ← numeral_succ,
    natOf_numeral]

theorem pv_bit0 (ha : a ∈ val h posN) : pv h (ap1 h bit0N a) = pv h a + pv h a := by
  rw [pv, pval_bit0_v h ha, add_ap2 h (pval_mem h ha) (pval_mem h ha), natOf_numeral]
  rfl

theorem pv_bit1 (ha : a ∈ val h posN) : pv h (ap1 h bit1N a) = pv h a + pv h a + 1 := by
  rw [pv, pval_bit1_v h ha, add_ap2 h (pval_mem h ha) (pval_mem h ha),
    val_suc_apply h (numeral_mem_omega _), ← numeral_succ, natOf_numeral]
  rfl

theorem nv_zero : nv h (val h n0N) = 0 := by
  rw [nv, nval_zero_v, val_zero, natOf_numeral]

theorem nv_npos (ha : a ∈ val h posN) : nv h (ap1 h nposN a) = pv h a := by
  rw [nv, nval_pos_v h ha]
  rfl

/-- The successor adds one. -/
theorem psucc_value : ∀ x ∈ val h posN, pv h (ap1 h psuccN x) = pv h x + 1 := by
  refine pos_induct h ?_ ?_ ?_
  · rw [psucc_one_v, pv_bit0 h (one_mem h), pv_one]
  · intro a ha _
    rw [psucc_bit0_v h ha, pv_bit1 h ha, pv_bit0 h ha]
  · intro a ha ih
    rw [psucc_bit1_v h ha, pv_bit0 h (psucc_mem h ha), ih, pv_bit1 h ha]
    omega

/-- Halving a positive number rounds down. -/
theorem phalf_value : ∀ x ∈ val h posN, nv h (ap1 h phalfN x) = pv h x / 2 := by
  refine pos_induct h ?_ ?_ ?_
  · rw [phalf_one_v, nv_zero, pv_one]
  · intro a ha _
    rw [phalf_bit0_v h ha, nv_npos h ha, pv_bit0 h ha]
    omega
  · intro a ha _
    rw [phalf_bit1_v h ha, nv_npos h ha, pv_bit1 h ha]
    omega

theorem nhalf_value : ∀ y ∈ val h natN, nv h (ap1 h nhalfN y) = nv h y / 2 := by
  refine nat_cases h ?_ ?_
  · rw [nhalf_zero_v, nv_zero]
  · intro a ha
    rw [nhalf_pos_v h ha, phalf_value h a ha, nv_npos h ha]

theorem nsuccPos_value : ∀ y ∈ val h natN, pv h (ap1 h nsuccPosN y) = nv h y + 1 := by
  refine nat_cases h ?_ ?_
  · rw [nsuccPos_zero_v, pv_one, nv_zero]
  · intro a ha
    rw [nsuccPos_pos_v h ha, psucc_value h a ha, nv_npos h ha]

/-- The digit `0` or `1` written after `r`, read from the last digit of a positive number. -/
theorem low0Pos_value : ∀ q ∈ val h posN, ∀ r ∈ val h posN,
    pv h (ap2 h low0PosN q r) = 2 * pv h r + pv h q % 2 := by
  refine pos_induct h ?_ ?_ ?_
  · intro r hr
    rw [low0Pos_one_v h hr, pv_bit1 h hr, pv_one]
    omega
  · intro a ha _ r hr
    rw [low0Pos_bit0_v h ha hr, pv_bit0 h hr, pv_bit0 h ha]
    omega
  · intro a ha _ r hr
    rw [low0Pos_bit1_v h ha hr, pv_bit1 h hr, pv_bit1 h ha]
    omega

theorem low0_value : ∀ y ∈ val h natN, ∀ r ∈ val h posN,
    pv h (ap2 h low0N y r) = 2 * pv h r + nv h y % 2 := by
  refine nat_cases h ?_ ?_
  · intro r hr
    rw [low0_zero_v h hr, pv_bit0 h hr, nv_zero]
    omega
  · intro a ha r hr
    rw [low0_pos_v h ha hr, low0Pos_value h a ha r hr, nv_npos h ha]

/-- The carry: the digit after `r` with one more, read from the last digit of a positive
number. -/
theorem low1Pos_value : ∀ q ∈ val h posN, ∀ r ∈ val h posN,
    pv h (ap2 h low1PosN q r) = 2 * pv h r + 1 + pv h q % 2 := by
  refine pos_induct h ?_ ?_ ?_
  · intro r hr
    rw [low1Pos_one_v h hr, pv_bit0 h (psucc_mem h hr), psucc_value h r hr, pv_one]
    omega
  · intro a ha _ r hr
    rw [low1Pos_bit0_v h ha hr, pv_bit1 h hr, pv_bit0 h ha]
    omega
  · intro a ha _ r hr
    rw [low1Pos_bit1_v h ha hr, pv_bit0 h (psucc_mem h hr), psucc_value h r hr, pv_bit1 h ha]
    omega

theorem low1_value : ∀ y ∈ val h natN, ∀ r ∈ val h posN,
    pv h (ap2 h low1N y r) = 2 * pv h r + 1 + nv h y % 2 := by
  refine nat_cases h ?_ ?_
  · intro r hr
    rw [low1_zero_v h hr, pv_bit1 h hr, nv_zero]
    omega
  · intro a ha r hr
    rw [low1_pos_v h ha hr, low1Pos_value h a ha r hr, nv_npos h ha]

/-- **The sum of a positive and a natural number has the sum of their values**, by induction
on the positive number, its last digit and the carry. -/
theorem paddNat_value : ∀ x ∈ val h posN, ∀ y ∈ val h natN,
    pv h (ap2 h paddNatN x y) = pv h x + nv h y := by
  refine pos_induct h ?_ ?_ ?_
  · intro y hy
    rw [paddNat_one_v h hy, nsuccPos_value h y hy, pv_one]
    omega
  · intro a ha ih y hy
    rw [paddNat_bit0_v h ha hy,
      low0_value h y hy _ (paddNat_mem h ha (nhalf_mem h hy)),
      ih _ (nhalf_mem h hy), nhalf_value h y hy, pv_bit0 h ha]
    omega
  · intro a ha ih y hy
    rw [paddNat_bit1_v h ha hy,
      low1_value h y hy _ (paddNat_mem h ha (nhalf_mem h hy)),
      ih _ (nhalf_mem h hy), nhalf_value h y hy, pv_bit1 h ha]
    omega

/-- **The value of a sum is the sum of the values.** -/
theorem pv_padd (ha : a ∈ val h posN) (hb : b ∈ val h posN) :
    pv h (ap2 h paddN a b) = pv h a + pv h b := by
  rw [padd_v h ha hb, paddNat_value h a ha _ (npos_mem h hb), nv_npos h hb]

theorem padd_mem (ha : a ∈ val h posN) (hb : b ∈ val h posN) : ap2 h paddN a b ∈ val h posN := by
  rw [padd_v h ha hb]
  exact paddNat_mem h ha (npos_mem h hb)

/-- **The value of a product is the product of the values**, by induction on the first
factor. -/
theorem pmul_value' : ∀ x ∈ val h posN, ∀ y ∈ val h posN,
    pv h (ap2 h pmulN x y) = pv h x * pv h y := by
  refine pos_induct h ?_ ?_ ?_
  · intro y hy
    rw [pmul_one_v h hy, pv_one, Nat.one_mul]
  · intro a ha ih y hy
    rw [pmul_bit0_v h ha hy, pv_bit0 h (pmul_mem h ha hy), ih y hy, pv_bit0 h ha, Nat.add_mul]
  · intro a ha ih y hy
    rw [pmul_bit1_v h ha hy, pv_padd h hy (bit0_mem h (pmul_mem h ha hy)),
      pv_bit0 h (pmul_mem h ha hy), ih y hy, pv_bit1 h ha]
    ring

end Values

/-! ### The value map is a homomorphism -/

/-- **The value map commutes with addition**: in the set model of the binary package, the value
of the sum of two positive numbers is the sum, by the object package's addition, of their
values. -/
theorem padd_value {x y : ZFSet.{u}} (hx : x ∈ val h posN) (hy : y ∈ val h posN) :
    ap1 h pvalN (ap2 h paddN x y) = ap2 h addN (ap1 h pvalN x) (ap1 h pvalN y) := by
  have sum := pv_padd h hx hy
  rw [add_ap2 h (pval_mem h hx) (pval_mem h hy), ← numeral_natOf
    (pval_mem h (padd_mem h hx hy))]
  exact congrArg numeral sum

/-- **The value map commutes with multiplication**: the value of the product of two positive
numbers is the natural number that is the product of their values. -/
theorem pmul_value {x y : ZFSet.{u}} (hx : x ∈ val h posN) (hy : y ∈ val h posN) :
    ap1 h pvalN (ap2 h pmulN x y) = numeral (pv h x * pv h y) := by
  rw [← numeral_natOf (pval_mem h (pmul_mem h hx hy))]
  exact congrArg numeral (pmul_value' h x hx y hy)

/-- At closed terms of the judgment: the value of `padd a b` is `add (pval a) (pval b)` in the
model, for every closed positive numbers `a` and `b` of the binary package. -/
theorem padd_value_closed {a b : CTm Tower.Head 0} (ha : CTyped binary .nil a cpos)
    (hb : CTyped binary .nil b cpos) :
    ev (objHeads h) (val h) (call1 pvalN (call2 paddN a b)) Fin.elim0 =
      ev (objHeads h) (val h) (cadd (call1 pvalN a) (call1 pvalN b)) Fin.elim0 :=
  padd_value h (typed0 h ha) (typed0 h hb)

/-- At closed terms of the judgment: the value of `pmul a b` is the product of the values. -/
theorem pmul_value_closed {a b : CTm Tower.Head 0} (ha : CTyped binary .nil a cpos)
    (hb : CTyped binary .nil b cpos) :
    natOf (ev (objHeads h) (val h) (call1 pvalN (call2 pmulN a b)) Fin.elim0) =
      natOf (ev (objHeads h) (val h) (call1 pvalN a) Fin.elim0) *
        natOf (ev (objHeads h) (val h) (call1 pvalN b) Fin.elim0) :=
  pmul_value' h _ (typed0 h ha) _ (typed0 h hb)

/-! ### Examples -/

/-- Positive example: in the model the value of `6 + 7` is `13`. -/
theorem six_plus_seven :
    pv h (ap2 h paddN (ap1 h bit0N (ap1 h bit1N (val h oneN)))
      (ap1 h bit1N (ap1 h bit1N (val h oneN)))) = 13 := by
  have one := one_mem h
  rw [pv_padd h (bit0_mem h (bit1_mem h one)) (bit1_mem h (bit1_mem h one)),
    pv_bit0 h (bit1_mem h one), pv_bit1 h (bit1_mem h one), pv_bit1 h one, pv_one]

include h in
/-- Negative example: **`one` is not a natural number.** In the model `one` is the constructor
value of its own name, and no constructor of `nat` carries that name. -/
theorem one_not_nat : ¬ CTyped binary .nil pone cnat := by
  intro typed
  have member : val h oneN ∈ val h natN := typed0 h typed
  rw [(posReading h).constant_value (i := 0) rfl] at member
  exact (natReading h).foreign_not_mem (k := oneN) (by decide) [] member

end Model

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Arith.Binary
