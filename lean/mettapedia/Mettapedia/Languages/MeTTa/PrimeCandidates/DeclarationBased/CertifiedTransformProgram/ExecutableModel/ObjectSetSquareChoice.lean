import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSetSquareControls
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ChoiceNonderivability

/-!
# The square fails at the functions on the numbers: choice

The code of the axiom of choice (`acCode`),

  `all@(num → num → prop) (λR. (∀x. ∃y. R x y) ⇒ ∃f. ∀x. R x (f x))`,

quantifies over the data carrier `num → num` through `ex@(num → num)`. The two readings
disagree on it, in the direction opposite to the controls at the sets and at `prop → num`:

* **Model SN's truth reading is false** (`acCode_modelSN`). Model SN reads a value of `num → num`
  as a class of closed terms that send numerals to numerals, and its truth reading reads the code
  as choice with definable functions (`acCode_truthS`), which a diagonal function refutes
  (`Consistency.not_definableChoice`); the relations `num → num → prop` range over every Lean
  relation.
* **The tower's value is the true truth value** (`acCode_tower`): its functions on `ω` are all
  the functions, and a total relation has a choice function, built from a choice of witness at
  each number.

So the square does not hold at the data carrier `num → num` (`square_fails_fun`), and the
carriers of `NumCarrier`, whose function types end in `prop`, cannot be widened to functions into
the numbers.

`Classical.choice` enters on the tower's side through the set layer: its trace products and
graphs, and the choice function of `tower_choice`. On model SN's side it enters only through the
diagonal function that escapes the definable functions (`Consistency.exists_undefinable`); the
reading of the code itself (`acCode_truthS`) is choice-free.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Consistency (Carrier Kind Setting Q Truth Read World
  Morph DataEq dataValue dataValue_app_rename TotalRelation HasDefinableChoice DefinableChoice
  not_definableChoice)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta)
open ZFSetTraceProofDecoding (truthCode)
open FormationSensitiveHOLInterface (typeAt)
open Mettapedia.Logic

universe u

namespace CodeModel
namespace SetSquare

/-! ## Model SN's truth reading of the choice code -/

section ModelSN

variable {rules : Rules Tower.Head} {roles : Roles Tower.Head}

/-- `all@(num → num)` is read at the data carrier `num → num`. -/
theorem allCarrier_fun :
    (objSetting rules roles).truthReading.allCarrier allFunN = some ⟨.data, .arr .num .num⟩ := by
  change (SetProfile.allInstance? (SetProfile.allName funTy)).map carrierOf = _
  rw [SetProfile.allInstance?_allName]
  rfl

/-- `ex@B P` means that some meaning at `B` satisfies the meaning of `P`, written
impredicatively. -/
theorem exCode_truthS {k m : Nat} {ξ : World (objSetting rules roles).truthReading m}
    {σ : Sub Tower.Head k m} {allB : DeclName} {kind : Kind} {B : Carrier kind}
    (carrier : (objSetting rules roles).truthReading.allCarrier allB = some ⟨kind, B⟩)
    {P : Tower.Tm k} {φ : B.V (objSetting rules roles).truthReading → Prop}
    (readP : Read (objSetting rules roles).truthReading ξ (subst σ P) (.arr B .prop) φ) :
    Truth (objSetting rules roles).truthReading ξ (subst σ (exCode allB P))
      (∀ C : Prop, (∀ y, φ y → C) → C) := by
  refine .all (A := .prop) (φ := fun (C : Prop) => (∀ y, φ y → C) → C)
    (allCarrier_toTy NumCarrier.prop) .refl (Read.lam_gen fun (C : Prop) => .prop ?_)
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
      have h : Truth (objSetting rules roles).truthReading ξ'
          (.app (Presentation.rename ρ (Presentation.rename wk (subst σ P))) s)
          (φ (dataValue (objSetting rules roles).truthReading.toDataSetting B s related)) :=
        Read.prop_inv (Read.app ((readP.rename (Morph.wk ξ ⟨.prop, C⟩)).rename morph)
          (.data related))
      rw [← e] at h
      exact h
  | gen =>
      refine Read.lam_gen fun y => .prop ?_
      refine .imp .refl ?_ (Read.prop_inv (Read.generic_prop _ rfl))
      have h : Truth (objSetting rules roles).truthReading ((ξ.snoc ⟨.prop, C⟩).snoc ⟨B, y⟩)
          (.app (Presentation.rename wk (Presentation.rename wk (subst σ P))) (.var 0)) (φ y) :=
        Read.prop_inv (Read.app ((readP.rename (Morph.wk ξ ⟨.prop, C⟩)).rename
          (Morph.wk _ ⟨B, y⟩)) (Read.generic' _ rfl))
      rw [← subst_liftSub_wk, ← subst_liftSub_wk] at h
      exact h

/-- Existence for a relation variable means that the relation is total. -/
theorem totalCode_truthS {n m : Nat} {ξ : World (objSetting rules roles).truthReading m}
    {σ : Sub Tower.Head (n + 1) m} {R : relCarrier.V (objSetting rules roles).truthReading}
    (readR : Read (objSetting rules roles).truthReading ξ (σ 0) relCarrier R) :
    Truth (objSetting rules roles).truthReading ξ (subst σ totalCode)
      (TotalRelation (objSetting rules roles) R) := by
  refine .all (A := .num) (allCarrier_toTy NumCarrier.num) .refl
    (Read.lam_data fun {_ _ _} morph {_} related => .prop ?_)
  exact exCode_truthS (allCarrier_toTy NumCarrier.num) (Read.app (readR.rename morph) (.data related))

/-- A choice function for a relation variable means a value of `num → num` that follows the
relation. -/
theorem choiceCode_truthS {n m : Nat} {ξ : World (objSetting rules roles).truthReading m}
    {σ : Sub Tower.Head (n + 1) m} {R : relCarrier.V (objSetting rules roles).truthReading}
    (readR : Read (objSetting rules roles).truthReading ξ (σ 0) relCarrier R) :
    Truth (objSetting rules roles).truthReading ξ (subst σ choiceCode)
      (HasDefinableChoice (objSetting rules roles) R) := by
  refine exCode_truthS allCarrier_fun (Read.lam_data fun {_ _ ρ₁} m₁ {f} rf => .prop ?_)
  refine .all (A := .num) (allCarrier_toTy NumCarrier.num) .refl
    (Read.lam_data fun {_ ξ₂ ρ₂} m₂ {x} rx => ?_)
  have related : DataEq (objSetting rules roles).truthReading.toDataSetting .num
      (.app (Presentation.rename ρ₂ f) x) (.app (Presentation.rename ρ₂ f) x) := rf ρ₂ rx
  have readFx : Read (objSetting rules roles).truthReading ξ₂ (.app (Presentation.rename ρ₂ f) x)
      .num (Presentation.TypedEquality.Impredicative.Consistency.Q.apply
        (dataValue (P := Prop) (objSetting rules roles).truthReading.toDataSetting (.arr .num .num)
          f rf)
        (dataValue (P := Prop) (objSetting rules roles).truthReading.toDataSetting .num x rx)) := by
    rw [← dataValue_app_rename ρ₂ rf rx related]
    exact .data related
  have readX : Read (objSetting rules roles).truthReading ξ₂ x .num
      (dataValue (P := Prop) (objSetting rules roles).truthReading.toDataSetting .num x rx) :=
    .data rx
  have readRx : Read (objSetting rules roles).truthReading ξ₂
      (.app (Presentation.rename ρ₂ (Presentation.rename ρ₁ (σ 0))) x) (.arr .num .prop)
      (R (dataValue (P := Prop) (objSetting rules roles).truthReading.toDataSetting .num x rx)) :=
    Read.app ((readR.rename m₁).rename m₂) readX
  exact Read.app readRx readFx

/-- **Model SN's truth reading of the choice code is choice with definable functions.** The
quantifier over relations is read at a fresh generic of every meaning, that is at every Lean
relation on the values of the numbers. -/
theorem acCode_truthS :
    Truth (objSetting rules roles).truthReading World.closed (acCode (n := 0))
      (DefinableChoice (objSetting rules roles)) := by
  have h : Truth (objSetting rules roles).truthReading World.closed
      (subst (Presentation.ids : Sub Tower.Head 0 0) acCode)
      (DefinableChoice (objSetting rules roles)) := by
    refine .all (A := relCarrier) (allCarrier_toTy (NumCarrier.arr .num (.arr .num .prop))) .refl
      (Read.lam_gen fun _ => .prop ?_)
    exact .imp .refl (totalCode_truthS (Read.generic' _ rfl))
      (choiceCode_truthS (Read.generic' _ rfl))
  rwa [subst_ids] at h

/-- **Negative, model SN's side: the choice code is false in model SN's truth reading.** -/
theorem acCode_modelSN (v : Nat → Nat) :
    ¬ ∃ P, Truth (vmodel v).toModel.reading World.closed (acCode (n := 0)) P ∧ P := fun holds =>
  not_definableChoice (tmodelC_laws v).truth
    ((Truth.holds_iff (tmodelC_laws v).truth.truthReading
      (acCode_truthS (rules := tmodelRules v) (roles := tmodelRoles))).mp holds)

end ModelSN

/-! ## The annotated choice code -/

section Annotated

/-- `∃ y : τ. P y`, annotated: `all@prop (λc. imp (all@τ (λy. imp (P y) c)) c)`. -/
def exCodeC {n : Nat} (τ : HOL.Ty SetProfile.SetBase) (P : CTm Tower.Head n) : CTm Tower.Head n :=
  .app (.const allPropN) (.lam (liftTm (typeAt SetProfile.types n .prop))
    (.app (.app (.const impN)
      (.app (.const (SetProfile.allName τ)) (.lam (liftTm (typeAt SetProfile.types (n + 1) τ))
        (.app (.app (.const impN) (.app (CTm.rename wk (CTm.rename wk P)) (.var 0))) (.var 1)))))
      (.var 0)))

/-- `∀ x : num. ∃ y : num. R x y`, annotated, for the newest variable `R`. -/
def totalCodeC {n : Nat} : CTm Tower.Head (n + 1) :=
  .app (.const allNumN) (.lam (liftTm (typeAt SetProfile.types (n + 1) SetProfile.numTy))
    (exCodeC SetProfile.numTy (.app (.var 1) (.var 0))))

/-- `∃ f : num → num. ∀ x : num. R x (f x)`, annotated, for the newest variable `R`. -/
def choiceCodeC {n : Nat} : CTm Tower.Head (n + 1) :=
  exCodeC funTy (.lam (liftTm (typeAt SetProfile.types (n + 1) funTy))
    (.app (.const allNumN) (.lam (liftTm (typeAt SetProfile.types (n + 2) SetProfile.numTy))
      (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0))))))

/-- The choice code, annotated. -/
def acCodeC : CTm Tower.Head 0 :=
  .app (.const allRelN) (.lam (liftTm (typeAt SetProfile.types 0 relTy))
    (.app (.app (.const impN) totalCodeC) choiceCodeC))

theorem exCodeC_erase {n : Nat} (τ : HOL.Ty SetProfile.SetBase) (P : CTm Tower.Head n) :
    (exCodeC τ P).erase = exCode (SetProfile.allName τ) P.erase := by
  simp only [exCodeC, exCode, CTm.erase, CTm.erase_rename]
  rfl

/-- **The annotated choice code erases to the choice code.** -/
theorem acCodeC_erase : acCodeC.erase = acCode (n := 0) := by
  simp only [acCodeC, acCode, totalCodeC, totalCode, choiceCodeC, choiceCode, CTm.erase,
    exCodeC_erase]
  rfl

end Annotated

/-! ## The tower's value of the choice code -/

section Tower

variable (h : CofinalInaccessibles.{u})

/-- The tower's impredicative existential over a predicate on a simple type is the truth value
of existence. -/
theorem ex_value (τ : HOL.Ty SetProfile.SetBase) {p : ZFSet.{u}}
    (hp : p ∈ simpleSet.{u} (.arr τ .prop)) :
    traceApp (objectSetConsts h allPropN) (traceLam (graph (simpleSet .prop) fun c =>
      traceApp (traceApp (objectSetConsts h impN)
        (traceApp (objectSetConsts h (SetProfile.allName τ)) (traceLam (graph (simpleSet τ)
          fun y => traceApp (traceApp (objectSetConsts h impN) (traceApp p y)) c)))) c)) =
      truthCode (∃ y ∈ simpleSet.{u} τ, (∅ : ZFSet.{u}) ∈ traceApp p y) := by
  have innerImp : ∀ c ∈ simpleSet.{u} .prop, ∀ y ∈ simpleSet.{u} τ,
      traceApp (traceApp (objectSetConsts h impN) (traceApp p y)) c =
        truthCode ((∅ : ZFSet.{u}) ∈ traceApp p y → (∅ : ZFSet.{u}) ∈ c) :=
    fun c hc y hy => imp_apply h (traceApp_mem_fibre hp hy) hc
  have overY : ∀ c ∈ simpleSet.{u} .prop,
      traceApp (objectSetConsts h (SetProfile.allName τ)) (traceLam (graph (simpleSet τ)
        fun y => traceApp (traceApp (objectSetConsts h impN) (traceApp p y)) c)) =
        truthCode (∀ y ∈ simpleSet.{u} τ, (∅ : ZFSet.{u}) ∈ traceApp p y → (∅ : ZFSet.{u}) ∈ c) := by
    intro c hc
    rw [all_graph h τ fun y hy => by
      rw [innerImp c hc y hy]
      exact Square.truthCode_mem_omega _]
    congr 1
    apply propext
    exact forall₂_congr fun y hy => by rw [innerImp c hc y hy, Square.square_truth_iff]
  have outerImp : ∀ c ∈ simpleSet.{u} .prop,
      traceApp (traceApp (objectSetConsts h impN)
        (traceApp (objectSetConsts h (SetProfile.allName τ)) (traceLam (graph (simpleSet τ)
          fun y => traceApp (traceApp (objectSetConsts h impN) (traceApp p y)) c)))) c =
        truthCode ((∀ y ∈ simpleSet.{u} τ, (∅ : ZFSet.{u}) ∈ traceApp p y →
          (∅ : ZFSet.{u}) ∈ c) → (∅ : ZFSet.{u}) ∈ c) := by
    intro c hc
    rw [overY c hc, imp_apply h (Square.truthCode_mem_omega _) hc, Square.square_truth_iff]
  rw [all_graph h .prop fun c hc => by
    rw [outerImp c hc]
    exact Square.truthCode_mem_omega _]
  congr 1
  apply propext
  constructor
  · intro all
    have atExists := all (truthCode (∃ y ∈ simpleSet.{u} τ, (∅ : ZFSet.{u}) ∈ traceApp p y))
      (Square.truthCode_mem_omega _)
    rw [outerImp _ (Square.truthCode_mem_omega _), Square.square_truth_iff] at atExists
    exact (Square.square_truth_iff _).mp
      (atExists fun y hy holds => (Square.square_truth_iff _).mpr ⟨y, hy, holds⟩)
  · rintro ⟨y, hy, holds⟩ c hc
    rw [outerImp c hc, Square.square_truth_iff]
    exact fun all => all y hy holds

/-- The annotated existential has the value of existence. -/
theorem ev_exCodeC {n : Nat} (τ : HOL.Ty SetProfile.SetBase) (P : CTm Tower.Head n)
    (η : Env.{u} n)
    (hP : ev (objHeads h) (objectSetConsts h) P η ∈ simpleSet.{u} (.arr τ .prop)) :
    ev (objHeads h) (objectSetConsts h) (exCodeC τ P) η =
      truthCode (∃ y ∈ simpleSet.{u} τ,
        (∅ : ZFSet.{u}) ∈ traceApp (ev (objHeads h) (objectSetConsts h) P η) y) := by
  have shift : ∀ c y, ev (objHeads h) (objectSetConsts h)
      (CTm.rename wk (CTm.rename wk P)) (extend (extend η c) y) =
      ev (objHeads h) (objectSetConsts h) P η := fun c y => by
    rw [ev_rename_wk, ev_rename_wk]
  change traceApp (objectSetConsts h allPropN) (traceLam (graph (ev (objHeads h) (objectSetConsts h)
      (liftTm (typeAt SetProfile.types n .prop)) η) fun c =>
      traceApp (traceApp (objectSetConsts h impN)
        (traceApp (objectSetConsts h (SetProfile.allName τ)) (traceLam (graph
          (ev (objHeads h) (objectSetConsts h) (liftTm (typeAt SetProfile.types (n + 1) τ))
            (extend η c)) fun y =>
          traceApp (traceApp (objectSetConsts h impN) (traceApp (ev (objHeads h) (objectSetConsts h)
            (CTm.rename wk (CTm.rename wk P)) (extend (extend η c) y)) y)) c)))) c)) = _
  simp only [ev_objTypeAt h, shift]
  exact ex_value h τ hP

/-- The annotated totality of a relation variable has the value of totality. -/
theorem ev_totalCodeC {n : Nat} (η : Env.{u} (n + 1)) (hR : η 0 ∈ simpleSet.{u} relTy) :
    ev (objHeads h) (objectSetConsts h) (totalCodeC (n := n)) η =
      truthCode (∀ x ∈ ZFSet.omega.{u}, ∃ y ∈ ZFSet.omega.{u},
        (∅ : ZFSet.{u}) ∈ traceApp (traceApp (η 0) x) y) := by
  have atX : ∀ x ∈ simpleSet.{u} SetProfile.numTy,
      ev (objHeads h) (objectSetConsts h)
        (exCodeC SetProfile.numTy (.app (.var 1) (.var 0) : CTm Tower.Head (n + 2)))
          (extend η x) =
        truthCode (∃ y ∈ simpleSet.{u} SetProfile.numTy,
          (∅ : ZFSet.{u}) ∈ traceApp (traceApp (η 0) x) y) :=
    fun x hx => ev_exCodeC h SetProfile.numTy _ (extend η x) (traceApp_mem_fibre hR hx)
  change traceApp (objectSetConsts h allNumN) (traceLam (graph (ev (objHeads h) (objectSetConsts h)
      (liftTm (typeAt SetProfile.types (n + 1) SetProfile.numTy)) η) fun x =>
      ev (objHeads h) (objectSetConsts h)
        (exCodeC SetProfile.numTy (.app (.var 1) (.var 0) : CTm Tower.Head (n + 2)))
          (extend η x))) = _
  rw [ev_objTypeAt h]
  rw [all_graph h SetProfile.numTy fun x hx => by
    rw [atX x hx]
    exact Square.truthCode_mem_omega _]
  congr 1
  apply propext
  exact forall₂_congr fun x hx => by rw [atX x hx, Square.square_truth_iff]; rfl

/-- The annotated choice of a relation variable has the value of the existence of a choice
function. -/
theorem ev_choiceCodeC {n : Nat} (η : Env.{u} (n + 1)) (hR : η 0 ∈ simpleSet.{u} relTy) :
    ev (objHeads h) (objectSetConsts h) (choiceCodeC (n := n)) η =
      truthCode (∃ f ∈ simpleSet.{u} funTy, ∀ x ∈ ZFSet.omega.{u},
        (∅ : ZFSet.{u}) ∈ traceApp (traceApp (η 0) x) (traceApp f x)) := by
  have atF : ∀ f ∈ simpleSet.{u} funTy,
      traceApp (objectSetConsts h allNumN) (traceLam (graph (simpleSet SetProfile.numTy) fun x =>
        traceApp (traceApp (η 0) x) (traceApp f x))) =
        truthCode (∀ x ∈ ZFSet.omega.{u},
          (∅ : ZFSet.{u}) ∈ traceApp (traceApp (η 0) x) (traceApp f x)) := by
    intro f hf
    refine all_graph h SetProfile.numTy fun x hx => ?_
    have hRx : traceApp (η 0) x ∈ simpleSet.{u} (.arr SetProfile.numTy .prop) :=
      traceApp_mem_fibre (b := fun _ => simpleSet.{u} (.arr SetProfile.numTy .prop)) hR hx
    have hfx : traceApp f x ∈ simpleSet.{u} SetProfile.numTy :=
      traceApp_mem_fibre (b := fun _ => simpleSet.{u} SetProfile.numTy) hf hx
    exact traceApp_mem_fibre (b := fun _ => simpleSet.{u} .prop) hRx hfx
  have predicate : ev (objHeads h) (objectSetConsts h)
      (.lam (liftTm (typeAt SetProfile.types (n + 1) funTy))
        (.app (.const allNumN) (.lam (liftTm (typeAt SetProfile.types (n + 2) SetProfile.numTy))
          (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0))))) : CTm Tower.Head (n + 1)) η =
      traceLam (graph (simpleSet funTy) fun f =>
        traceApp (objectSetConsts h allNumN) (traceLam (graph (simpleSet SetProfile.numTy) fun x =>
          traceApp (traceApp (η 0) x) (traceApp f x)))) := by
    change traceLam (graph (ev (objHeads h) (objectSetConsts h)
        (liftTm (typeAt SetProfile.types (n + 1) funTy)) η) fun f =>
        traceApp (objectSetConsts h allNumN) (traceLam (graph (ev (objHeads h) (objectSetConsts h)
          (liftTm (typeAt SetProfile.types (n + 2) SetProfile.numTy)) (extend η f)) fun x =>
          traceApp (traceApp (η 0) x) (traceApp f x)))) = _
    simp only [ev_objTypeAt h]
  have member : traceLam (graph (simpleSet funTy) fun f =>
      traceApp (objectSetConsts h allNumN) (traceLam (graph (simpleSet SetProfile.numTy) fun x =>
        traceApp (traceApp (η 0) x) (traceApp f x)))) ∈ simpleSet.{u} (.arr funTy .prop) :=
    traceLam_graph_mem fun f hf => by
      rw [atF f hf]
      exact Square.truthCode_mem_omega _
  unfold choiceCodeC
  rw [ev_exCodeC h funTy _ η (predicate ▸ member), predicate]
  congr 1
  apply propext
  refine exists_congr fun f => and_congr_right fun hf => ?_
  rw [traceApp_graph_beta _ hf, atF f hf, Square.square_truth_iff]

/-- **The tower's value of the choice code** is the truth value of choice for relations on `ω`
with functions on `ω`. -/
theorem ev_acCodeC :
    ev (objHeads h) (objectSetConsts h) acCodeC Fin.elim0 =
      truthCode (∀ R ∈ simpleSet.{u} relTy,
        (∀ x ∈ ZFSet.omega.{u}, ∃ y ∈ ZFSet.omega.{u},
          (∅ : ZFSet.{u}) ∈ traceApp (traceApp R x) y) →
        ∃ f ∈ simpleSet.{u} funTy, ∀ x ∈ ZFSet.omega.{u},
          (∅ : ZFSet.{u}) ∈ traceApp (traceApp R x) (traceApp f x)) := by
  have atR : ∀ R ∈ simpleSet.{u} relTy,
      traceApp (traceApp (objectSetConsts h impN)
        (ev (objHeads h) (objectSetConsts h) (totalCodeC (n := 0)) (extend Fin.elim0 R)))
        (ev (objHeads h) (objectSetConsts h) (choiceCodeC (n := 0)) (extend Fin.elim0 R)) =
      truthCode ((∀ x ∈ ZFSet.omega.{u}, ∃ y ∈ ZFSet.omega.{u},
          (∅ : ZFSet.{u}) ∈ traceApp (traceApp R x) y) →
        ∃ f ∈ simpleSet.{u} funTy, ∀ x ∈ ZFSet.omega.{u},
          (∅ : ZFSet.{u}) ∈ traceApp (traceApp R x) (traceApp f x)) := by
    intro R hR
    rw [ev_totalCodeC h (extend Fin.elim0 R) hR, ev_choiceCodeC h (extend Fin.elim0 R) hR,
      imp_apply h (Square.truthCode_mem_omega _) (Square.truthCode_mem_omega _),
      Square.square_truth_iff, Square.square_truth_iff]
    rfl
  change traceApp (objectSetConsts h allRelN) (traceLam (graph (ev (objHeads h) (objectSetConsts h)
      (liftTm (typeAt SetProfile.types 0 relTy)) Fin.elim0) fun R =>
      traceApp (traceApp (objectSetConsts h impN)
        (ev (objHeads h) (objectSetConsts h) (totalCodeC (n := 0)) (extend Fin.elim0 R)))
        (ev (objHeads h) (objectSetConsts h) (choiceCodeC (n := 0)) (extend Fin.elim0 R)))) = _
  rw [ev_objTypeAt h, all_graph h relTy fun R hR => by
    rw [atR R hR]
    exact Square.truthCode_mem_omega _]
  congr 1
  apply propext
  exact forall₂_congr fun R hR => by rw [atR R hR, Square.square_truth_iff]

/-- **Choice holds in the tower**: a total relation on `ω` has a choice function, the traced
graph of a choice of witness at each number. -/
theorem tower_choice :
    ∀ R ∈ simpleSet.{u} relTy,
      (∀ x ∈ ZFSet.omega.{u}, ∃ y ∈ ZFSet.omega.{u}, (∅ : ZFSet.{u}) ∈ traceApp (traceApp R x) y) →
      ∃ f ∈ simpleSet.{u} funTy, ∀ x ∈ ZFSet.omega.{u},
        (∅ : ZFSet.{u}) ∈ traceApp (traceApp R x) (traceApp f x) := by
  intro R _ total
  classical
  let witness : ZFSet.{u} → ZFSet.{u} := fun x =>
    if hx : x ∈ ZFSet.omega.{u} then Classical.choose (total x hx) else ∅
  have spec : ∀ x (hx : x ∈ ZFSet.omega.{u}), witness x ∈ ZFSet.omega.{u} ∧
      (∅ : ZFSet.{u}) ∈ traceApp (traceApp R x) (witness x) := fun x hx => by
    simp only [witness, dif_pos hx]
    exact Classical.choose_spec (total x hx)
  refine ⟨traceLam (graph ZFSet.omega witness), traceLam_graph_mem fun x hx => (spec x hx).1,
    fun x hx => ?_⟩
  rw [traceApp_graph_beta _ hx]
  exact (spec x hx).2

/-- **Negative, the tower's side: the value of `holds acCode` is the true truth value.** -/
theorem acCode_tower :
    (∅ : ZFSet.{u}) ∈ ev (objHeads h) (objectSetConsts h)
      (CTm.app (.const holdsN) acCodeC) Fin.elim0 := by
  change (∅ : ZFSet.{u}) ∈ traceApp (objectSetConsts h holdsN)
    (ev (objHeads h) (objectSetConsts h) acCodeC Fin.elim0)
  rw [ev_acCodeC h, holds_apply h (Square.truthCode_mem_omega _), Square.square_truth_iff]
  exact tower_choice

/-- **The square fails at the functions on the numbers.** At the choice code, model SN's truth
reading is false and the empty proof lies in the tower's value of `holds acCode`. -/
theorem square_fails_fun (v : Nat → Nat) :
    ¬ ((∃ P, Truth (vmodel v).toModel.reading World.closed acCodeC.erase P ∧ P) ↔
      (∅ : ZFSet.{u}) ∈ ev (objHeads h) (objectSetConsts h)
        (CTm.app (.const holdsN) acCodeC) Fin.elim0) := by
  rw [acCodeC_erase]
  exact fun same => acCode_modelSN v (same.mpr (acCode_tower h))

end Tower

end SetSquare
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
