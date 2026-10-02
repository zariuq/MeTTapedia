import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConsistencySound
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Binders
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Definable
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerEncoding

/-!
# Choice is not derivable from the program's codes

The package is `objectRules`: the executable package (the numbers and their
recursion, the sets, identity elimination, and the package's definitions)
extended by the program's proposition codes. Its codes are `prop : U0`, the decoder
`holds : prop → U0`, implication, and at every simple type `A` over `prop`,
`num` and `set` a quantifier `all@A : (A → prop) → prop` and an equation
`eq@A : A → A → prop`. All carriers used here are simple types of the lowest
universe `U0`: `num`, `num → num`, the relations `num → num → prop`, and `prop`
itself, over which `all@prop` quantifies impredicatively.

Existence is a code, written impredicatively:

  `ex@B P := all@prop (λc. imp (all@B (λy. imp (P y) c)) c)`.

Its decoding eliminates only into propositions: a proof of `holds (ex@B P)`
yields `holds C` for every code `C` that follows from each witness, and yields
no witness. Choice and unique choice are the codes

* `acCode := all@(num → num → prop) (λR. (∀x. ∃y. R x y) ⇒ ∃f. ∀x. R x (f x))`;
* `ucCode := all@(num → num → prop) (λR. (∀x. ∃y. R x y) ⇒
  (∀x y y'. R x y ⇒ R x y' ⇒ eq@num y y') ⇒ ∃f. ∀x. R x (f x))`,

where `∀x` is `all@num`, `∃y` is `ex@num` and `∃f` is `ex@(num → num)`; unique
existence is stated as existence and uniqueness. Both are codes of the package
(`acCode_typed`, `ucCode_typed`).

## Nonderivability

No closed term proves `holds acCode` or `holds ucCode` (`ac_not_derivable`,
`uc_not_derivable`). The countermodel is the consistency model, for which the
package is sound (`objectSound`). It reads codes by Lean propositions:

* `all@A` means Lean's `∀` over every meaning at `A` (Girard's clause); at the
  generic carrier `num → num → prop` the meanings are all Lean relations on the
  model's numbers, definable or not;
* at the data carrier `num` a meaning is a class of closed terms computing one
  numeral, which is the value of that numeral (`Q.eq_numClass`);
* at the data carrier `num → num` a meaning is a class of closed terms that send
  numerals to numerals, and applying it to a number applies representatives
  (`Read.dataArg`, `dataValue_app`, `Q.apply`).

So `acCode` means that every total Lean relation on the numbers is followed by a
definable function (`acCode_truth`); since `all@(num → num → prop)` is read at
every meaning, any Lean relation instantiates it. Closed terms are countable
(`Tm.encode_injective`), so the definable functions are countably many, and the
graph of a diagonal function escapes them (`exists_not_apply`); that graph is
total and functional, which refutes unique choice as well
(`not_definableUniqueChoice`).

The metatheory is Lean with `propext` and `Quot.sound`. The diagonal decides
whether a closed term computes a numeral, which is classical: `Classical.choice`
enters there (`exists_undefinable`) and nowhere else.

This shows nonderivability, not independence: the consistency of the package
with choice is not established here.

Unique choice fails in this model because the model mixes two readings:
functions are definable programs while predicates are arbitrary Lean relations.
In the internal language of a topos unique choice holds; the consistency model
is not a set or topos semantics of functions. It reads rigid carriers, the sets
included, by a single point, so nothing follows here about choice or
description operators on sets.

## Choice with witnesses

The dependent pairs of the package carry witnesses, and choice between them is
derivable by projection (`witnessChoice_derivable`):

  `λR. λH. (λx. fst (H x), λx. snd (H x))`
  `: Π R : num → num → prop. (Π x : num. Σ y : num. holds (R x y)) →`
  `Σ f : num → num. Π x : num. holds (R x (f x))`.

The code-level statement differs only in that its existential is proof-only.
This is the type-theoretic counterpart of the fact that choice is not provable
in simple type theory: it is not a consequence of impredicative higher-order
logic, while it is a theorem about Σ-types.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Consistency
open Mettapedia.Logic
open Package (U0 numT)

namespace CodeModel

/-! ## The codes -/

/-- The simple type `num → num → prop` of relations on the numbers. -/
abbrev relTy : HOL.Ty SetProfile.SetBase := .arr SetProfile.numTy (.arr SetProfile.numTy .prop)

/-- The simple type `num → num` of functions on the numbers. -/
abbrev funTy : HOL.Ty SetProfile.SetBase := .arr SetProfile.numTy SetProfile.numTy

abbrev allRelN : DeclName := SetProfile.allName relTy
abbrev allFunN : DeclName := SetProfile.allName funTy

section Codes

variable {n : Nat}

/-- `∃ y : B. P y`, impredicatively: `all@prop (λc. imp (all@B (λy. imp (P y) c)) c)`,
for the quantifier `allB` over `B`. -/
def exCode (allB : DeclName) (P : Tower.Tm n) : Tower.Tm n :=
  .app (.const allPropN) (.lam (programCodes.impOf
    (.app (.const allB) (.lam (programCodes.impOf
      (.app (Presentation.rename wk (Presentation.rename wk P)) (.var 0)) (.var 1))))
    (.var 0)))

/-- Existence for the relation variable `R` (the newest variable):
`∀ x : num. ∃ y : num. R x y`. -/
def totalCode : Tower.Tm (n + 1) :=
  .app (.const allNumN) (.lam (exCode allNumN (.app (.var 1) (.var 0))))

/-- Uniqueness for the relation variable `R`:
`∀ x y y' : num. R x y ⇒ R x y' ⇒ eq@num y y'`. -/
def functionalCode : Tower.Tm (n + 1) :=
  .app (.const allNumN) (.lam (.app (.const allNumN) (.lam (.app (.const allNumN) (.lam
    (programCodes.impOf (.app (.app (.var 3) (.var 2)) (.var 1))
      (programCodes.impOf (.app (.app (.var 3) (.var 2)) (.var 0))
        (.app (.app (.const eqNumN) (.var 1)) (.var 0)))))))))

/-- A choice function for the relation variable `R`:
`∃ f : num → num. ∀ x : num. R x (f x)`. -/
def choiceCode : Tower.Tm (n + 1) :=
  exCode allFunN (.lam (.app (.const allNumN)
    (.lam (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0))))))

/-- The axiom of choice as a code:
`all@(num → num → prop) (λR. (∀x. ∃y. R x y) ⇒ ∃f. ∀x. R x (f x))`. -/
def acCode : Tower.Tm n :=
  .app (.const allRelN) (.lam (programCodes.impOf totalCode choiceCode))

/-- The axiom of unique choice as a code:
`all@(num → num → prop) (λR. (∀x. ∃y. R x y) ⇒
(∀x y y'. R x y ⇒ R x y' ⇒ y = y') ⇒ ∃f. ∀x. R x (f x))`. -/
def ucCode : Tower.Tm n :=
  .app (.const allRelN) (.lam (programCodes.impOf totalCode
    (programCodes.impOf functionalCode choiceCode)))

end Codes

/-! ## The codes are propositions of the package -/

section Typing

variable {n : Nat} {Γ : Tower.Ctx n}

/-- The type `num → num → prop` of relations on the numbers. -/
abbrev relT {n : Nat} : Tower.Tm n := .pi numT (.pi numT (.const propN))

/-- The type `num → num` of functions on the numbers. -/
abbrev funT {n : Nat} : Tower.Tm n := .pi numT numT

theorem rel_typedO : Typed objectRules Γ relT U0 :=
  piO num_typedO (piO num_typedO prop_typedO)

theorem fun_typedO : Typed objectRules Γ funT U0 :=
  piO num_typedO num_typedO

theorem allRel_typedO :
    Typed objectRules Γ (.const allRelN) (.pi (.pi relT (.const propN)) (.const propN)) :=
  .const (declared_allName relTy) (piO (piO rel_typedO prop_typedO) prop_typedO)
    (.sort Tower.zero)

theorem allFun_typedO :
    Typed objectRules Γ (.const allFunN) (.pi (.pi funT (.const propN)) (.const propN)) :=
  .const (declared_allName funTy) (piO (piO fun_typedO prop_typedO) prop_typedO)
    (.sort Tower.zero)

/-- Implication of two codes is a code. -/
theorem impO {p q : Tower.Tm n} (hp : Typed objectRules Γ p (.const propN))
    (hq : Typed objectRules Γ q (.const propN)) :
    Typed objectRules Γ (programCodes.impOf p q) (.const propN) := by
  have antecedent : Typed objectRules Γ (.app (.const impN) p)
      (.pi (.const propN) (.const propN)) := .appElim imp_typedO hp
  exact .appElim antecedent hq

/-- `all@num (λx. body)` is a code when the body is. -/
theorem allNumO {body : Tower.Tm (n + 1)}
    (h : Typed objectRules (.snoc Γ numT) body (.const propN)) :
    Typed objectRules Γ (.app (.const allNumN) (.lam body)) (.const propN) :=
  .appElim allNum_typedO (.lamIntro (piO num_typedO prop_typedO) (.sort _) h)

/-- A relation applied to two numbers is a code. -/
theorem relAppO {R x y : Tower.Tm n} (hR : Typed objectRules Γ R relT)
    (hx : Typed objectRules Γ x numT) (hy : Typed objectRules Γ y numT) :
    Typed objectRules Γ (.app (.app R x) y) (.const propN) := by
  have first : Typed objectRules Γ (.app R x) (.pi numT (.const propN)) := .appElim hR hx
  exact .appElim first hy

/-- `ex@B P` is a code when `P` is a predicate on `B` and `allB` quantifies
over `B`. -/
theorem exCode_typed {allB : DeclName} {B P : Tower.Tm n}
    (allTyped : Typed objectRules (.snoc Γ (.const propN)) (.const allB)
      (.pi (.pi (Presentation.rename wk B) (.const propN)) (.const propN)))
    (carrierTyped : Typed objectRules (.snoc Γ (.const propN)) (Presentation.rename wk B) U0)
    (predicate : Typed objectRules Γ P (.pi B (.const propN))) :
    Typed objectRules Γ (exCode allB P) (.const propN) := by
  have shifted : Typed objectRules
      (.snoc (.snoc Γ (.const propN)) (Presentation.rename wk B))
      (Presentation.rename wk (Presentation.rename wk P))
      (.pi (Presentation.rename wk (Presentation.rename wk B)) (.const propN)) :=
    (predicate.weaken (extension := .const propN)).weaken
  have witness : Typed objectRules (.snoc (.snoc Γ (.const propN)) (Presentation.rename wk B))
      (.var 0) (Presentation.rename wk (Presentation.rename wk B)) := .var 0
  have conclusion : Typed objectRules
      (.snoc (.snoc Γ (.const propN)) (Presentation.rename wk B)) (.var 1) (.const propN) :=
    .var 1
  have applied : Typed objectRules (.snoc (.snoc Γ (.const propN)) (Presentation.rename wk B))
      (.app (Presentation.rename wk (Presentation.rename wk P)) (.var 0)) (.const propN) :=
    .appElim shifted witness
  have inner : Typed objectRules (.snoc Γ (.const propN))
      (.app (.const allB) (.lam (programCodes.impOf
        (.app (Presentation.rename wk (Presentation.rename wk P)) (.var 0)) (.var 1))))
      (.const propN) :=
    .appElim allTyped (.lamIntro (piO carrierTyped prop_typedO) (.sort _)
      (impO applied conclusion))
  have code : Typed objectRules (.snoc Γ (.const propN)) (.var 0) (.const propN) := .var 0
  exact .appElim allProp_typedO (.lamIntro (piO prop_typedO prop_typedO) (.sort _)
    (impO inner code))

theorem totalCode_typed : Typed objectRules (.snoc Γ relT) totalCode (.const propN) := by
  have R : Typed objectRules (.snoc (.snoc Γ relT) numT) (.var 1) relT := .var 1
  have x : Typed objectRules (.snoc (.snoc Γ relT) numT) (.var 0) numT := .var 0
  have Rx : Typed objectRules (.snoc (.snoc Γ relT) numT) (.app (.var 1) (.var 0))
      (.pi numT (.const propN)) := .appElim R x
  exact allNumO (exCode_typed (B := numT) allNum_typedO num_typedO Rx)

theorem functionalCode_typed :
    Typed objectRules (.snoc Γ relT) functionalCode (.const propN) := by
  have R : Typed objectRules (.snoc (.snoc (.snoc (.snoc Γ relT) numT) numT) numT)
      (.var 3) relT := .var 3
  have x : Typed objectRules (.snoc (.snoc (.snoc (.snoc Γ relT) numT) numT) numT)
      (.var 2) numT := .var 2
  have y : Typed objectRules (.snoc (.snoc (.snoc (.snoc Γ relT) numT) numT) numT)
      (.var 1) numT := .var 1
  have y' : Typed objectRules (.snoc (.snoc (.snoc (.snoc Γ relT) numT) numT) numT)
      (.var 0) numT := .var 0
  have eqY : Typed objectRules (.snoc (.snoc (.snoc (.snoc Γ relT) numT) numT) numT)
      (.app (.const eqNumN) (.var 1)) (.pi numT (.const propN)) := .appElim eqNum_typedO y
  have eqYY : Typed objectRules (.snoc (.snoc (.snoc (.snoc Γ relT) numT) numT) numT)
      (.app (.app (.const eqNumN) (.var 1)) (.var 0)) (.const propN) := .appElim eqY y'
  exact allNumO (allNumO (allNumO (impO (relAppO R x y) (impO (relAppO R x y') eqYY))))

theorem choiceCode_typed : Typed objectRules (.snoc Γ relT) choiceCode (.const propN) := by
  have R : Typed objectRules (.snoc (.snoc (.snoc Γ relT) funT) numT) (.var 2) relT := .var 2
  have f : Typed objectRules (.snoc (.snoc (.snoc Γ relT) funT) numT) (.var 1) funT := .var 1
  have x : Typed objectRules (.snoc (.snoc (.snoc Γ relT) funT) numT) (.var 0) numT := .var 0
  have fx : Typed objectRules (.snoc (.snoc (.snoc Γ relT) funT) numT)
      (.app (.var 1) (.var 0)) numT := .appElim f x
  exact exCode_typed (B := funT) allFun_typedO fun_typedO
    (.lamIntro (piO fun_typedO prop_typedO) (.sort _) (allNumO (relAppO R x fx)))

/-- The axiom of choice is a code of the package. -/
theorem acCode_typed : Typed objectRules Γ acCode (.const propN) :=
  .appElim allRel_typedO (.lamIntro (piO rel_typedO prop_typedO) (.sort _)
    (impO totalCode_typed choiceCode_typed))

/-- The axiom of unique choice is a code of the package. -/
theorem ucCode_typed : Typed objectRules Γ ucCode (.const propN) :=
  .appElim allRel_typedO (.lamIntro (piO rel_typedO prop_typedO) (.sort _)
    (impO totalCode_typed (impO functionalCode_typed choiceCode_typed)))

/-- `holds acCode` is a type of the lowest universe. -/
theorem acProposition_typed : Typed objectRules Γ (programCodes.holdsOf acCode) U0 :=
  .appElim holds_typedO acCode_typed

/-- `holds ucCode` is a type of the lowest universe. -/
theorem ucProposition_typed : Typed objectRules Γ (programCodes.holdsOf ucCode) U0 :=
  .appElim holds_typedO ucCode_typed

end Typing

/-! ## The meaning of the codes in the consistency model -/

section Truth

variable (v : Nat → Nat)

theorem allCarrier_allName (type : HOL.Ty SetProfile.SetBase) :
    (model v).reading.allCarrier (SetProfile.allName type) = some (carrierOf type) := by
  change (SetProfile.allInstance? (SetProfile.allName type)).map carrierOf = _
  rw [SetProfile.allInstance?_allName]
  rfl

theorem eqCarrier_eqName (type : HOL.Ty SetProfile.SetBase) :
    (model v).reading.eqCarrier (SetProfile.eqName type) = some (carrierOf type) := by
  change (SetProfile.eqInstance? (SetProfile.eqName type)).map carrierOf = _
  rw [SetProfile.eqInstance?_eqName]
  rfl

/-- The carrier `num → num → prop`: a generic carrier, whose meanings are all
Lean relations on the model's numbers. -/
abbrev relCarrier : Carrier .gen := .arr .num (.arr .num .prop)

theorem allCarrier_prop : (model v).reading.allCarrier allPropN = some ⟨.gen, .prop⟩ :=
  allCarrier_allName v .prop

theorem allCarrier_num : (model v).reading.allCarrier allNumN = some ⟨.data, .num⟩ :=
  allCarrier_allName v SetProfile.numTy

theorem allCarrier_fun :
    (model v).reading.allCarrier allFunN = some ⟨.data, .arr .num .num⟩ :=
  allCarrier_allName v funTy

theorem allCarrier_rel : (model v).reading.allCarrier allRelN = some ⟨.gen, relCarrier⟩ :=
  allCarrier_allName v relTy

theorem eqCarrier_num : (model v).reading.eqCarrier eqNumN = some ⟨.data, .num⟩ :=
  eqCarrier_eqName v SetProfile.numTy

variable {v}

/-- `ex@B P` means that some meaning at `B` satisfies the meaning of `P`,
written impredicatively. -/
theorem exCode_truth {k m : Nat} {ξ : World (model v).reading m} {σ : Sub Tower.Head k m}
    {allB : DeclName} {kind : Kind} {B : Carrier kind}
    (carrier : (model v).reading.allCarrier allB = some ⟨kind, B⟩)
    {P : Tower.Tm k} {φ : B.V (model v).reading → Prop}
    (readP : Read (model v).reading ξ (subst σ P) (.arr B .prop) φ) :
    Truth (model v).reading ξ (subst σ (exCode allB P))
      (∀ C : Prop, (∀ y, φ y → C) → C) := by
  refine .all (A := .prop) (φ := fun (C : Prop) => (∀ y, φ y → C) → C) (allCarrier_prop v)
    .refl (Read.lam_gen fun (C : Prop) => .prop ?_)
  refine .imp .refl (.all (A := B) (φ := fun y => φ y → C) carrier .refl ?_)
    (Read.prop_inv (Read.generic_prop _ rfl))
  cases kind with
  | data =>
      refine Read.lam_data fun {_ ξ' ρ} morph {s} related => .prop ?_
      refine .imp .refl ?_ (Read.prop_inv (Read.generic_prop ξ' (morph 0)))
      have e : subst (consSub s fun i => Presentation.rename ρ (liftSub σ i))
          (Presentation.rename wk (Presentation.rename wk P)) =
          Presentation.rename ρ (Presentation.rename wk (subst σ P)) := by
        rw [subst_rename, subst_rename, rename_subst, rename_subst]
        exact subst_ext (fun _ => rfl) P
      have h : Truth (model v).reading ξ'
          (.app (Presentation.rename ρ (Presentation.rename wk (subst σ P))) s)
          (φ (dataValue (model v).reading.toDataSetting B s related)) :=
        Read.prop_inv (Read.app ((readP.rename (Morph.wk ξ ⟨.prop, C⟩)).rename morph)
          (.data related))
      rw [← e] at h
      exact h
  | gen =>
      refine Read.lam_gen fun y => .prop ?_
      refine .imp .refl ?_ (Read.prop_inv (Read.generic_prop _ rfl))
      have h : Truth (model v).reading ((ξ.snoc ⟨.prop, C⟩).snoc ⟨B, y⟩)
          (.app (Presentation.rename wk (Presentation.rename wk (subst σ P))) (.var 0)) (φ y) :=
        Read.prop_inv (Read.app ((readP.rename (Morph.wk ξ ⟨.prop, C⟩)).rename
          (Morph.wk _ ⟨B, y⟩)) (Read.generic' _ rfl))
      rw [← subst_liftSub_wk, ← subst_liftSub_wk] at h
      exact h

/-- Existence for a relation variable means that the relation is total. -/
theorem totalCode_truth {n m : Nat} {ξ : World (model v).reading m}
    {σ : Sub Tower.Head (n + 1) m} {R : relCarrier.V (model v).reading}
    (readR : Read (model v).reading ξ (σ 0) relCarrier R) :
    Truth (model v).reading ξ (subst σ totalCode) (TotalRelation (model v).toSetting R) := by
  refine .all (A := .num) (allCarrier_num v) .refl
    (Read.lam_data fun {_ _ _} morph {_} related => .prop ?_)
  exact exCode_truth (allCarrier_num v) (Read.app (readR.rename morph) (.data related))

/-- Uniqueness for a relation variable means that the relation is functional. -/
theorem functionalCode_truth {n m : Nat} {ξ : World (model v).reading m}
    {σ : Sub Tower.Head (n + 1) m} {R : relCarrier.V (model v).reading}
    (readR : Read (model v).reading ξ (σ 0) relCarrier R) :
    Truth (model v).reading ξ (subst σ functionalCode)
      (FunctionalRelation (model v).toSetting R) := by
  refine .all (A := .num) (allCarrier_num v) .refl
    (Read.lam_data fun {_ _ _} m₁ {_} rx => .prop ?_)
  refine .all (A := .num) (allCarrier_num v) .refl
    (Read.lam_data fun {_ _ _} m₂ {_} ry => .prop ?_)
  refine .all (A := .num) (allCarrier_num v) .refl
    (Read.lam_data fun {_ _ _} m₃ {_} ry' => .prop ?_)
  have readR₃ := ((readR.rename m₁).rename m₂).rename m₃
  have readX₃ := ((Read.data rx).rename m₂).rename m₃
  have readY₃ := (Read.data ry).rename m₃
  exact .imp .refl (Read.prop_inv (Read.app (Read.app readR₃ readX₃) readY₃))
    (.imp .refl (Read.prop_inv (Read.app (Read.app readR₃ readX₃) (.data ry')))
      (.eq (eqCarrier_num v) .refl readY₃ (.data ry')))

/-- A choice function for a relation variable means a value of `num → num` that
follows the relation. -/
theorem choiceCode_truth {n m : Nat} {ξ : World (model v).reading m}
    {σ : Sub Tower.Head (n + 1) m} {R : relCarrier.V (model v).reading}
    (readR : Read (model v).reading ξ (σ 0) relCarrier R) :
    Truth (model v).reading ξ (subst σ choiceCode)
      (HasDefinableChoice (model v).toSetting R) := by
  refine exCode_truth (allCarrier_fun v) (Read.lam_data fun {_ _ ρ₁} m₁ {f} rf => .prop ?_)
  refine .all (A := .num) (allCarrier_num v) .refl
    (Read.lam_data fun {_ ξ₂ ρ₂} m₂ {x} rx => ?_)
  have related : DataEq (model v).reading.toDataSetting .num
      (.app (Presentation.rename ρ₂ f) x) (.app (Presentation.rename ρ₂ f) x) := rf ρ₂ rx
  have readFx : Read (model v).reading ξ₂ (.app (Presentation.rename ρ₂ f) x) .num
      (Q.apply (dataValue (P := Prop) (model v).reading.toDataSetting (.arr .num .num) f rf)
        (dataValue (P := Prop) (model v).reading.toDataSetting .num x rx)) := by
    rw [← dataValue_app_rename ρ₂ rf rx related]
    exact .data related
  have readX : Read (model v).reading ξ₂ x .num
      (dataValue (P := Prop) (model v).reading.toDataSetting .num x rx) := .data rx
  have readRx : Read (model v).reading ξ₂
      (.app (Presentation.rename ρ₂ (Presentation.rename ρ₁ (σ 0))) x) (.arr .num .prop)
      (R (dataValue (P := Prop) (model v).reading.toDataSetting .num x rx)) :=
    Read.app ((readR.rename m₁).rename m₂) readX
  exact Read.app readRx readFx

/-- `acCode` under any substitution, in any world, means choice with definable
functions. The quantifier over relations is read at a fresh generic of every
meaning, that is at every Lean relation on the model's numbers, not only at the
relations that terms denote. -/
theorem acCode_truth_subst {n m : Nat} {ξ : World (model v).reading m}
    (σ : Sub Tower.Head n m) :
    Truth (model v).reading ξ (subst σ acCode) (DefinableChoice (model v).toSetting) := by
  refine .all (A := relCarrier) (allCarrier_rel v) .refl (Read.lam_gen fun _ => .prop ?_)
  exact .imp .refl (totalCode_truth (Read.generic' _ rfl))
    (choiceCode_truth (Read.generic' _ rfl))

/-- `ucCode` under any substitution, in any world, means unique choice with
definable functions. -/
theorem ucCode_truth_subst {n m : Nat} {ξ : World (model v).reading m}
    (σ : Sub Tower.Head n m) :
    Truth (model v).reading ξ (subst σ ucCode) (DefinableUniqueChoice (model v).toSetting) := by
  refine .all (A := relCarrier) (allCarrier_rel v) .refl (Read.lam_gen fun _ => .prop ?_)
  exact .imp .refl (totalCode_truth (Read.generic' _ rfl))
    (.imp .refl (functionalCode_truth (Read.generic' _ rfl))
      (choiceCode_truth (Read.generic' _ rfl)))

/-- The meaning of `acCode`: every total Lean relation on the model's numbers,
definable or not, is followed by a value of `num → num`, a class of closed
terms. -/
theorem acCode_truth :
    Truth (model v).reading World.closed (acCode (n := 0))
      (DefinableChoice (model v).toSetting) := by
  have h := acCode_truth_subst (v := v) (ξ := World.closed) (ids : Sub Tower.Head 0 0)
  rwa [subst_ids] at h

/-- The meaning of `ucCode`: every total functional Lean relation on the model's
numbers is followed by a value of `num → num`. -/
theorem ucCode_truth :
    Truth (model v).reading World.closed (ucCode (n := 0))
      (DefinableUniqueChoice (model v).toSetting) := by
  have h := ucCode_truth_subst (v := v) (ξ := World.closed) (ids : Sub Tower.Head 0 0)
  rwa [subst_ids] at h

end Truth

/-! ## Nonderivability -/

/-- **Choice is not derivable.** No closed term of the package proves
`holds acCode`: in the consistency model, for which the package is sound, the
graph of a diagonal function is a total relation followed by no definable
function. -/
theorem ac_not_derivable (t : Tower.Tm 0) :
    ¬ Typed objectRules .nil t (programCodes.holdsOf (acCode (n := 0))) :=
  no_closed_proof (objectSound fun _ => 0) acCode_truth
    (not_definableChoice (model_laws fun _ => 0).truth) t

/-- **Unique choice is not derivable.** No closed term of the package proves
`holds ucCode`: the graph of the diagonal is also functional. -/
theorem uc_not_derivable (t : Tower.Tm 0) :
    ¬ Typed objectRules .nil t (programCodes.holdsOf (ucCode (n := 0))) :=
  no_closed_proof (objectSound fun _ => 0) ucCode_truth
    (not_definableUniqueChoice (model_laws fun _ => 0).truth) t

/-! ## Choice with witnesses is derivable -/

section WitnessChoice

variable {n : Nat} {Γ : Tower.Ctx n}

theorem sigmaO {A : Tower.Tm n} {B : Tower.Tm (n + 1)} {level : LevelExpr Nat}
    (hA : Typed objectRules Γ A (sortTm level))
    (hB : Typed objectRules (.snoc Γ A) B (sortTm level)) :
    Typed objectRules Γ (.sigma A B) (sortTm level) :=
  .cumul (.sigmaForm hA (.sort level) hB (.sort level) (.sorts level level))
    (fun _ => Nat.le_of_eq (Nat.max_self _))

/-- `Π x : num. Σ y : num. holds (R x y)`, for the relation variable `R`. -/
def witnessTotal : Tower.Tm (n + 1) :=
  .pi numT (.sigma numT (programCodes.holdsOf (.app (.app (.var 2) (.var 1)) (.var 0))))

/-- `Σ f : num → num. Π x : num. holds (R x (f x))`, for the relation variable
`R` and a hypothesis. -/
def witnessChosen : Tower.Tm (n + 2) :=
  .sigma funT (.pi numT (programCodes.holdsOf
    (.app (.app (.var 3) (.var 0)) (.app (.var 1) (.var 0)))))

/-- Choice with witnesses:
`Π R : num → num → prop. (Π x. Σ y. holds (R x y)) → Σ f. Π x. holds (R x (f x))`. -/
def witnessChoiceType : Tower.Tm 0 := .pi relT (.pi witnessTotal witnessChosen)

/-- Its proof by projections: `λR. λH. (λx. fst (H x), λx. snd (H x))`. -/
def witnessChoiceProof : Tower.Tm 0 :=
  .lam (.lam (.pair (.lam (.fst (.app (.var 1) (.var 0))))
    (.lam (.snd (.app (.var 1) (.var 0))))))

theorem witnessTotal_typed : Typed objectRules (.snoc Γ relT) witnessTotal U0 := by
  have R : Typed objectRules (.snoc (.snoc (.snoc Γ relT) numT) numT) (.var 2) relT := .var 2
  have x : Typed objectRules (.snoc (.snoc (.snoc Γ relT) numT) numT) (.var 1) numT := .var 1
  have y : Typed objectRules (.snoc (.snoc (.snoc Γ relT) numT) numT) (.var 0) numT := .var 0
  exact piO num_typedO (sigmaO num_typedO (.appElim holds_typedO (relAppO R x y)))

theorem witnessChosen_typed :
    Typed objectRules (.snoc (.snoc Γ relT) witnessTotal) witnessChosen U0 := by
  have R : Typed objectRules (.snoc (.snoc (.snoc (.snoc Γ relT) witnessTotal) funT) numT)
      (.var 3) relT := .var 3
  have f : Typed objectRules (.snoc (.snoc (.snoc (.snoc Γ relT) witnessTotal) funT) numT)
      (.var 1) funT := .var 1
  have x : Typed objectRules (.snoc (.snoc (.snoc (.snoc Γ relT) witnessTotal) funT) numT)
      (.var 0) numT := .var 0
  have fx : Typed objectRules (.snoc (.snoc (.snoc (.snoc Γ relT) witnessTotal) funT) numT)
      (.app (.var 1) (.var 0)) numT := .appElim f x
  exact sigmaO fun_typedO (piO num_typedO (.appElim holds_typedO (relAppO R x fx)))

theorem witnessChoiceType_typed : Typed objectRules .nil witnessChoiceType U0 :=
  piO rel_typedO (piO witnessTotal_typed witnessChosen_typed)

/-- **Choice with witnesses is derivable**, by projections. -/
theorem witnessChoice_derivable :
    Typed objectRules .nil witnessChoiceProof witnessChoiceType := by
  -- The context `R, H, x` and one number deeper.
  have H : Typed objectRules (.snoc (.snoc (.snoc .nil relT) witnessTotal) numT) (.var 1)
      (.pi numT (.sigma numT (programCodes.holdsOf (.app (.app (.var 4) (.var 1)) (.var 0))))) :=
    .var 1
  have x : Typed objectRules (.snoc (.snoc (.snoc .nil relT) witnessTotal) numT) (.var 0) numT :=
    .var 0
  have R : Typed objectRules (.snoc (.snoc (.snoc .nil relT) witnessTotal) numT) (.var 2) relT :=
    .var 2
  have H' : Typed objectRules (.snoc (.snoc (.snoc (.snoc .nil relT) witnessTotal) numT) numT)
      (.var 2)
      (.pi numT (.sigma numT (programCodes.holdsOf (.app (.app (.var 5) (.var 1)) (.var 0))))) :=
    .var 2
  have x' : Typed objectRules (.snoc (.snoc (.snoc (.snoc .nil relT) witnessTotal) numT) numT)
      (.var 0) numT := .var 0
  -- `H x : Σ y : num. holds (R x y)`.
  have applied : Typed objectRules (.snoc (.snoc (.snoc .nil relT) witnessTotal) numT)
      (.app (.var 1) (.var 0))
      (.sigma numT (programCodes.holdsOf (.app (.app (.var 3) (.var 1)) (.var 0)))) :=
    .appElim H x
  have applied' : Typed objectRules
      (.snoc (.snoc (.snoc (.snoc .nil relT) witnessTotal) numT) numT)
      (.app (.var 2) (.var 0))
      (.sigma numT (programCodes.holdsOf (.app (.app (.var 4) (.var 1)) (.var 0)))) :=
    .appElim H' x'
  have first' : Typed objectRules (.snoc (.snoc (.snoc (.snoc .nil relT) witnessTotal) numT) numT)
      (.fst (.app (.var 2) (.var 0))) numT := .fstElim applied'
  -- The chosen function `λx. fst (H x)`, at `x`, computes `fst (H x)`.
  have chosenAt : Typed objectRules (.snoc (.snoc (.snoc .nil relT) witnessTotal) numT)
      (.app (.lam (.fst (.app (.var 2) (.var 0)))) (.var 0)) numT :=
    .appElim (.lamIntro fun_typedO (.sort _) first') x
  have beta : Equal objectRules (.snoc (.snoc (.snoc .nil relT) witnessTotal) numT)
      (.app (.lam (.fst (.app (.var 2) (.var 0)))) (.var 0)) (.fst (.app (.var 1) (.var 0)))
      numT :=
    .betaPi fun_typedO (.sort _) first' x
  have Rx : Typed objectRules (.snoc (.snoc (.snoc .nil relT) witnessTotal) numT)
      (.app (.var 2) (.var 0)) (.pi numT (.const propN)) := .appElim R x
  have argument : Equal objectRules (.snoc (.snoc (.snoc .nil relT) witnessTotal) numT)
      (.app (.app (.var 2) (.var 0)) (.fst (.app (.var 1) (.var 0))))
      (.app (.app (.var 2) (.var 0)) (.app (.lam (.fst (.app (.var 2) (.var 0)))) (.var 0)))
      (.const propN) :=
    .appCong (.refl Rx) (.symm beta)
  have congr : Equal objectRules (.snoc (.snoc (.snoc .nil relT) witnessTotal) numT)
      (programCodes.holdsOf (.app (.app (.var 2) (.var 0)) (.fst (.app (.var 1) (.var 0)))))
      (programCodes.holdsOf (.app (.app (.var 2) (.var 0))
        (.app (.lam (.fst (.app (.var 2) (.var 0)))) (.var 0)))) U0 :=
    .appCong (.refl holds_typedO) argument
  have second : Typed objectRules (.snoc (.snoc (.snoc .nil relT) witnessTotal) numT)
      (.snd (.app (.var 1) (.var 0)))
      (programCodes.holdsOf (.app (.app (.var 2) (.var 0)) (.fst (.app (.var 1) (.var 0))))) :=
    .sndElim applied
  have holdsChosen : Typed objectRules (.snoc (.snoc (.snoc .nil relT) witnessTotal) numT)
      (programCodes.holdsOf (.app (.app (.var 2) (.var 0))
        (.app (.lam (.fst (.app (.var 2) (.var 0)))) (.var 0)))) U0 :=
    .appElim holds_typedO (relAppO R x chosenAt)
  -- The witnesses `λx. snd (H x)`.
  have witnesses : Typed objectRules (.snoc (.snoc .nil relT) witnessTotal)
      (.lam (.snd (.app (.var 1) (.var 0))))
      (.pi numT (programCodes.holdsOf (.app (.app (.var 2) (.var 0))
        (.app (.lam (.fst (.app (.var 2) (.var 0)))) (.var 0))))) :=
    .lamIntro (piO num_typedO holdsChosen) (.sort _) (.conv second congr (.sort _))
  -- The chosen function `λx. fst (H x)`.
  have chosen : Typed objectRules (.snoc (.snoc .nil relT) witnessTotal)
      (.lam (.fst (.app (.var 1) (.var 0)))) funT :=
    .lamIntro fun_typedO (.sort _) (.fstElim applied)
  exact .lamIntro witnessChoiceType_typed (.sort _)
    (.lamIntro (piO witnessTotal_typed witnessChosen_typed) (.sort _)
      (.pairIntro witnessChosen_typed (.sort _) chosen witnesses))

end WitnessChoice

end CodeModel

end CertifiedTransformProgram.ExecutableModel
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
