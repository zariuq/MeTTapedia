import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFibreControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigid
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFull
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CheckingAlgorithm

/-!
# A package of naturals, vectors and finite indices for programs on the dependent step

The cumulative tower with twelve declared constants, all rigid:

* `nat : U0`, `zero : nat`, `succ : nat → nat`, `add : nat → nat → nat`;
* `vec : nat → U0`, `nil : vec zero`, `cons : Π (n : nat). nat → vec n → vec (succ n)`,
  `append : Π (m n : nat). vec m → vec n → vec (add m n)`;
* `fin : nat → U0`, `fz : Π (n : nat). fin (succ n)`, `fs : Π (n : nat). fin n → fin (succ n)`,
  `lookup : Π (n : nat). vec n → fin n → nat`.

Rigid means that no constant computes: `add`, `append` and `lookup` are heads of calls, and the
programs of `VectorPrograms` evaluate them by firings of the dependent full step. This is the
package the tree's metatheory covers: with every constant rigid, the normalization model applies
as in the point package (`ContextualDependentFibre.Controls`), so the facts about weak-head forms
(`facts`) and completeness of the algorithmic equality (`complete`) hold, and with them the
refutation of clashing stores (`ContextualDependentRigid.not_solvable_of_storeClashes`).

The tree's normalization framework has no indexed inductive families: its inductive types are
simple, with closed field types (`TypedEquality.Normalization.Field`). `vec` and `fin` are
therefore rigid families here, with rigid constructors and no eliminator; programs eliminate them
by matching.

Every declared type is formed (`declared_formed`), by explicit derivations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ProgrammingOnTheStep.VectorPackage

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual

/-! ## Names -/

def natN : DeclName := .mkSimple "nat"
def zeroN : DeclName := .mkSimple "zero"
def succN : DeclName := .mkSimple "succ"
def addN : DeclName := .mkSimple "add"
def vecN : DeclName := .mkSimple "vec"
def nilN : DeclName := .mkSimple "nil"
def consN : DeclName := .mkSimple "cons"
def appendN : DeclName := .mkSimple "append"
def finN : DeclName := .mkSimple "fin"
def fzN : DeclName := .mkSimple "fz"
def fsN : DeclName := .mkSimple "fs"
def lookupN : DeclName := .mkSimple "lookup"

/-! ## Terms -/

/-- The small universe `U0`. -/
abbrev u0 : Tower.Head := .sort Tower.zero

abbrev U0 {n : Nat} : Tower.Tm n := .head u0

def natC {n : Nat} : Tower.Tm n := .const natN
def zeroC {n : Nat} : Tower.Tm n := .const zeroN
def succC {n : Nat} (t : Tower.Tm n) : Tower.Tm n := .app (.const succN) t
def addC {n : Nat} (a b : Tower.Tm n) : Tower.Tm n := .app (.app (.const addN) a) b
def vecC {n : Nat} (t : Tower.Tm n) : Tower.Tm n := .app (.const vecN) t
def nilC {n : Nat} : Tower.Tm n := .const nilN
def consC {n : Nat} (k x xs : Tower.Tm n) : Tower.Tm n := .app (.app (.app (.const consN) k) x) xs
def appendC {n : Nat} (m k xs ys : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.const appendN) m) k) xs) ys
def finC {n : Nat} (t : Tower.Tm n) : Tower.Tm n := .app (.const finN) t
def fzC {n : Nat} (k : Tower.Tm n) : Tower.Tm n := .app (.const fzN) k
def fsC {n : Nat} (k i : Tower.Tm n) : Tower.Tm n := .app (.app (.const fsN) k) i
def lookupC {n : Nat} (k v i : Tower.Tm n) : Tower.Tm n := .app (.app (.app (.const lookupN) k) v) i

/-! ## Declared types -/

def natTy : Tower.Tm 0 := U0
def zeroTy : Tower.Tm 0 := natC
def succTy : Tower.Tm 0 := .pi natC natC
def addTy : Tower.Tm 0 := .pi natC (.pi natC natC)
def vecTy : Tower.Tm 0 := .pi natC U0
def nilTy : Tower.Tm 0 := vecC zeroC
def consTy : Tower.Tm 0 := .pi natC (.pi natC (.pi (vecC (.var 1)) (vecC (succC (.var 2)))))
def appendTy : Tower.Tm 0 :=
  .pi natC (.pi natC (.pi (vecC (.var 1)) (.pi (vecC (.var 1)) (vecC (addC (.var 3) (.var 2))))))
def finTy : Tower.Tm 0 := .pi natC U0
def fzTy : Tower.Tm 0 := .pi natC (finC (succC (.var 0)))
def fsTy : Tower.Tm 0 := .pi natC (.pi (finC (.var 0)) (finC (succC (.var 1))))
def lookupTy : Tower.Tm 0 := .pi natC (.pi (vecC (.var 0)) (.pi (finC (.var 1)) natC))

/-- The declarations. -/
def declared (name : DeclName) : Option (Tower.Tm 0) :=
  if name = natN then some natTy else
  if name = zeroN then some zeroTy else
  if name = succN then some succTy else
  if name = addN then some addTy else
  if name = vecN then some vecTy else
  if name = nilN then some nilTy else
  if name = consN then some consTy else
  if name = appendN then some appendTy else
  if name = finN then some finTy else
  if name = fzN then some fzTy else
  if name = fsN then some fsTy else
  if name = lookupN then some lookupTy else none

/-- **The package**: the cumulative tower with the twelve declarations and no computation. -/
def rules : Rules Tower.Head := { Tower.rules with constantType := declared }

/-! ## The normalization model -/

/-- Every constant is rigid. -/
def roles : Roles Tower.Head := fun _ => .rigid

theorem shape : RootShape rules roles where
  spine := fun step => False.elim step
  deterministic := fun step => False.elim step

def levels : LevelModel rules Nat := { TowerModel.levels (L := Nat) (fun _ => 0) with }

def setting : Setting Tower.Head Nat where
  R := rules
  roles := roles
  E := declarative rules
  levels := levels
  shape := shape
  constructors := .of_no_inductive fun _ _ role => by cases role

theorem rigid (name : DeclName) : setting.roles name = .rigid := rfl

theorem laws : setting.E.Laws setting.R setting.roles := declarative_laws roles levels

theorem constants : SemanticConstants setting := SemanticConstants.of_rigid laws fun _ => rfl

theorem facts : FormFacts rules roles := .ofSemantic (S := setting) laws constants

theorem algebra : CumulativeAlgebra rules := { TowerModel.algebra (L := Nat) with }

theorem heads : HeadPreserving rules := by
  intro n Γ h h' A same typing
  obtain ⟨u, headTyping, le⟩ := Typed.generation typing
  change LevelTower.HeadTyping h u at headTyping
  change LevelTower.HeadEq h h' at same
  cases headTyping with
  | legacyGround =>
      cases h' with
      | legacyGround => exact Typed.subsume (.headType .legacyGround) le
      | sort _ => exact same.elim
  | sort l =>
      cases h' with
      | legacyGround => exact same.elim
      | sort r =>
          have raise : rules.cumulative (.sort (.succ r)) (.sort (.succ l)) := by
            intro ν
            show UniverseLevel.LevelOrder.succ (LevelExpr.eval ν r) ≤
              UniverseLevel.LevelOrder.succ (LevelExpr.eval ν l)
            exact UniverseLevel.LevelOrder.succ_le_succ (le_of_eq (same ν).symm)
          exact Typed.subsume (.cumul (.headType (.sort r)) raise) le

theorem roots : RootPreserving rules := by
  intro n Γ l r A _ step
  exact False.elim step

theorem algorithmicConstants : SemanticConstants (algorithmicSetting setting) :=
  SemanticConstants.of_rigid
    (algorithmicSetting_laws (S := setting) laws constants roots heads algebra) fun _ => rfl

theorem complete : AlgorithmicComplete rules roles :=
  AlgorithmicComplete.ofSemantic (S := setting) laws constants roots heads algebra
    algorithmicConstants

instance headEqDecidable : DecidableRel setting.R.headEq := fun left right =>
  LevelTower.instDecidableHeadEq left right

instance cumulativeDecidable : DecidableRel setting.R.cumulative := fun left right =>
  LevelTower.instDecidableCumulative left right

instance universeDecidable (head : Tower.Head) : Decidable (setting.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

/-! ## Lookups -/

theorem declared_nat : rules.constantType natN = some natTy := by decide
theorem declared_zero : rules.constantType zeroN = some zeroTy := by decide
theorem declared_succ : rules.constantType succN = some succTy := by decide
theorem declared_add : rules.constantType addN = some addTy := by decide
theorem declared_vec : rules.constantType vecN = some vecTy := by decide
theorem declared_nil : rules.constantType nilN = some nilTy := by decide
theorem declared_cons : rules.constantType consN = some consTy := by decide
theorem declared_append : rules.constantType appendN = some appendTy := by decide
theorem declared_fin : rules.constantType finN = some finTy := by decide
theorem declared_fz : rules.constantType fzN = some fzTy := by decide
theorem declared_fs : rules.constantType fsN = some fsTy := by decide
theorem declared_lookup : rules.constantType lookupN = some lookupTy := by decide

/-! ## Formation -/

theorem collapse : rules.cumulative (.sort (.max Tower.zero Tower.zero)) (.sort Tower.zero) := by
  change LevelTower.Cumulative (.sort (.max Tower.zero Tower.zero)) (.sort Tower.zero)
  intro valuation
  simp [LevelExpr.eval]

theorem universe_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed rules Γ U0 (.head (.sort (.succ Tower.zero))) :=
  .headType (.sort _)

theorem nat_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ natC U0 :=
  .const declared_nat (universe_typed .nil) (.sort _)

/-- A dependent function type between small types is small. -/
theorem pi0 {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n} {B : Tower.Tm (n + 1)}
    (typedA : Typed rules Γ A U0) (typedB : Typed rules (.snoc Γ A) B U0) :
    Typed rules Γ (.pi A B) U0 :=
  .cumul (.piForm typedA (.sort _) typedB (.sort _) (.sorts _ _)) collapse

theorem succTy_typed : Typed rules .nil succTy U0 := pi0 (nat_typed _) (nat_typed _)

theorem addTy_typed : Typed rules .nil addTy U0 :=
  pi0 (nat_typed _) (pi0 (nat_typed _) (nat_typed _))

theorem vecTy_typed : Typed rules .nil vecTy (.head (.sort (.max Tower.zero (.succ Tower.zero)))) :=
  .piForm (nat_typed _) (.sort _) (universe_typed _) (.sort _) (.sorts _ _)

theorem finTy_typed : Typed rules .nil finTy (.head (.sort (.max Tower.zero (.succ Tower.zero)))) :=
  .piForm (nat_typed _) (.sort _) (universe_typed _) (.sort _) (.sorts _ _)

theorem zero_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ zeroC natC :=
  .const declared_zero (nat_typed .nil) (.sort _)

theorem succ_typed {n : Nat} {Γ : Tower.Ctx n} {t : Tower.Tm n} (typed : Typed rules Γ t natC) :
    Typed rules Γ (succC t) natC :=
  .appElim (.const declared_succ succTy_typed (.sort _)) typed

theorem add_typed {n : Nat} {Γ : Tower.Ctx n} {a b : Tower.Tm n} (typedA : Typed rules Γ a natC)
    (typedB : Typed rules Γ b natC) : Typed rules Γ (addC a b) natC :=
  .appElim (.appElim (.const declared_add addTy_typed (.sort _)) typedA) typedB

theorem vec_typed {n : Nat} {Γ : Tower.Ctx n} {t : Tower.Tm n} (typed : Typed rules Γ t natC) :
    Typed rules Γ (vecC t) U0 :=
  .appElim (.const declared_vec vecTy_typed (.sort _)) typed

theorem fin_typed {n : Nat} {Γ : Tower.Ctx n} {t : Tower.Tm n} (typed : Typed rules Γ t natC) :
    Typed rules Γ (finC t) U0 :=
  .appElim (.const declared_fin finTy_typed (.sort _)) typed

theorem nilTy_typed : Typed rules .nil nilTy U0 := vec_typed (zero_typed _)

theorem consTy_typed : Typed rules .nil consTy U0 :=
  pi0 (nat_typed _) (pi0 (nat_typed _) (pi0 (vec_typed (.var 1)) (vec_typed (succ_typed (.var 2)))))

theorem appendTy_typed : Typed rules .nil appendTy U0 :=
  pi0 (nat_typed _) (pi0 (nat_typed _) (pi0 (vec_typed (.var 1)) (pi0 (vec_typed (.var 1))
    (vec_typed (add_typed (.var 3) (.var 2))))))

theorem fzTy_typed : Typed rules .nil fzTy U0 := pi0 (nat_typed _) (fin_typed (succ_typed (.var 0)))

theorem fsTy_typed : Typed rules .nil fsTy U0 :=
  pi0 (nat_typed _) (pi0 (fin_typed (.var 0)) (fin_typed (succ_typed (.var 1))))

theorem lookupTy_typed : Typed rules .nil lookupTy U0 :=
  pi0 (nat_typed _) (pi0 (vec_typed (.var 0)) (pi0 (fin_typed (.var 1)) (nat_typed _)))

/-- **Every declared type is formed.** -/
theorem declared_formed : DeclaredTypesFormed rules := by
  intro name type known
  by_cases e1 : name = natN
  · subst e1; obtain rfl := Option.some.inj (declared_nat.symm.trans known)
    exact ⟨_, .sort _, universe_typed _⟩
  by_cases e2 : name = zeroN
  · subst e2; obtain rfl := Option.some.inj (declared_zero.symm.trans known)
    exact ⟨_, .sort _, nat_typed _⟩
  by_cases e3 : name = succN
  · subst e3; obtain rfl := Option.some.inj (declared_succ.symm.trans known)
    exact ⟨_, .sort _, succTy_typed⟩
  by_cases e4 : name = addN
  · subst e4; obtain rfl := Option.some.inj (declared_add.symm.trans known)
    exact ⟨_, .sort _, addTy_typed⟩
  by_cases e5 : name = vecN
  · subst e5; obtain rfl := Option.some.inj (declared_vec.symm.trans known)
    exact ⟨_, .sort _, vecTy_typed⟩
  by_cases e6 : name = nilN
  · subst e6; obtain rfl := Option.some.inj (declared_nil.symm.trans known)
    exact ⟨_, .sort _, nilTy_typed⟩
  by_cases e7 : name = consN
  · subst e7; obtain rfl := Option.some.inj (declared_cons.symm.trans known)
    exact ⟨_, .sort _, consTy_typed⟩
  by_cases e8 : name = appendN
  · subst e8; obtain rfl := Option.some.inj (declared_append.symm.trans known)
    exact ⟨_, .sort _, appendTy_typed⟩
  by_cases e9 : name = finN
  · subst e9; obtain rfl := Option.some.inj (declared_fin.symm.trans known)
    exact ⟨_, .sort _, finTy_typed⟩
  by_cases e10 : name = fzN
  · subst e10; obtain rfl := Option.some.inj (declared_fz.symm.trans known)
    exact ⟨_, .sort _, fzTy_typed⟩
  by_cases e11 : name = fsN
  · subst e11; obtain rfl := Option.some.inj (declared_fs.symm.trans known)
    exact ⟨_, .sort _, fsTy_typed⟩
  by_cases e12 : name = lookupN
  · subst e12; obtain rfl := Option.some.inj (declared_lookup.symm.trans known)
    exact ⟨_, .sort _, lookupTy_typed⟩
  change declared name = some type at known
  simp only [declared, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, if_false] at known
  cases known

/-! ## Terms used by the programs -/

theorem nil_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ nilC (vecC zeroC) :=
  .const declared_nil nilTy_typed (.sort _)

theorem cons_const_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed rules Γ (.const consN) (liftClosed consTy) :=
  .const declared_cons consTy_typed (.sort _)

theorem append_const_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed rules Γ (.const appendN) (liftClosed appendTy) :=
  .const declared_append appendTy_typed (.sort _)

theorem fz_const_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ (.const fzN) (liftClosed fzTy) :=
  .const declared_fz fzTy_typed (.sort _)

theorem fs_const_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ (.const fsN) (liftClosed fsTy) :=
  .const declared_fs fsTy_typed (.sort _)

theorem lookup_const_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed rules Γ (.const lookupN) (liftClosed lookupTy) :=
  .const declared_lookup lookupTy_typed (.sort _)

end ProgrammingOnTheStep.VectorPackage

#print axioms ProgrammingOnTheStep.VectorPackage.facts
#print axioms ProgrammingOnTheStep.VectorPackage.complete
#print axioms ProgrammingOnTheStep.VectorPackage.declared_formed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
