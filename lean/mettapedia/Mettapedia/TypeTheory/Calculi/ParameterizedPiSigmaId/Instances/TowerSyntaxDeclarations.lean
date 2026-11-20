import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerSyntax

/-!
# Typed syntax in the cumulative tower: the declarations of the types and the typing relation

The six simple inductive types of the package (`num`, `unit`, `void`, `bool`, `ty`, `raw`) are declared
in stages, each with its recursor; `raw` has the closed fields `num` and `bool`, so its earlier stage
declares both. The families over the object types (`is-num`, `is-bool`, `val`), the zero test, addition
and the typing relation are declared by structural recursion, each over the stage of the constants its
right-hand sides mention.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType applyClosed)
open TowerNumbersModel (num zero succ numRec ctors u mem_zero mem_succ)
open TowerVectorsModel (unit tt unitRec void voidRec add unitCtors U0 numC zeroC succC unitC ttC
  addC unitRecC voidC voidRecC TowerLike)

namespace TowerSyntaxModel

variable (lv : LevelExpr Nat)

/-! ## Stage inclusions of the reused stages -/

theorem sub_numbers₁ : RulesSub TowerNumbersModel.rules₁ (rules lv) :=
  ⟨id, id, id, id, id, fun {name type} declared => (by
    change (if name = num then some (.head u) else none) = some type at declared
    split at declared
    · rename_i h
      subst h
      exact declared
    · cases declared), fun step => nomatch step⟩

theorem sub_numbers₂ : RulesSub TowerNumbersModel.rules₂ (rules lv) :=
  ⟨id, id, id, id, id, fun {name type} declared => (by
    change (if name = num then some (.head u) else if name = zero then some (ctorType num [])
      else if name = succ then some (ctorType num [.recursive]) else none) = some type at declared
    split at declared
    · rename_i h
      subst h
      exact declared
    · split at declared
      · rename_i h
        subst h
        exact declared
      · split at declared
        · rename_i h
          subst h
          exact declared
        · cases declared), fun step => nomatch step⟩

theorem sub_unit₁ : RulesSub TowerVectorsModel.unitStage₁ (rules lv) :=
  ⟨id, id, id, id, id, fun {name type} declared => (by
    change (if name = unit then some (.head u) else none) = some type at declared
    split at declared
    · rename_i h
      subst h
      exact declared
    · cases declared), fun step => nomatch step⟩

theorem sub_unit₂ : RulesSub TowerVectorsModel.unitStage₂ (rules lv) :=
  ⟨id, id, id, id, id, fun {name type} declared => (by
    change (if name = unit then some (.head u) else if name = tt then some (ctorType unit [])
      else none) = some type at declared
    split at declared
    · rename_i h
      subst h
      exact declared
    · split at declared
      · rename_i h
        subst h
        exact declared
      · cases declared), fun step => nomatch step⟩

theorem sub_void : RulesSub TowerVectorsModel.voidStage (rules lv) :=
  ⟨id, id, id, id, id, fun {name type} declared => (by
    change (if name = void then some (.head u) else none) = some type at declared
    split at declared
    · rename_i h
      subst h
      exact declared
    · cases declared), fun step => nomatch step⟩

/-- The type of `raw-rec`, written out. -/
theorem rawRecType_eq : recType raw (.sort lv) rawCtors =
    .pi (.pi rawC (.head (.sort lv)))
      (.pi (.pi numC (.app (.var 1) (rnumC (.var 0))))
      (.pi (.pi boolC (.app (.var 2) (rboolC (.var 0))))
      (.pi (.pi rawC (.pi rawC (.pi (.app (.var 4) (.var 1)) (.pi (.app (.var 5) (.var 1))
          (.app (.var 6) (raddC (.var 3) (.var 2)))))))
      (.pi (.pi rawC (.pi rawC (.pi rawC (.pi (.app (.var 6) (.var 2)) (.pi (.app (.var 7) (.var 2))
          (.pi (.app (.var 8) (.var 2)) (.app (.var 9) (rifC (.var 5) (.var 4) (.var 3)))))))))
      (.pi (.pi rawC (.pi (.app (.var 5) (.var 0)) (.app (.var 6) (rzeroC (.var 1)))))
      (.pi rawC (.app (.var 6) (.var 0)))))))) := rfl

/-! ## Typings of the recursors' types -/

section RecursorTypes

variable {R : Rules Tower.Head} (tw : TowerLike R)
include tw

/-- The recursor of a type with two constructors without fields:
`Π (P : T → V). P k₁ → P k₂ → Π (x : T). P x`. -/
theorem twoRecType_typed {T k₁ k₂ : DeclName} (dT : R.constantType T = some (.head u))
    (d₁ : R.constantType k₁ = some (.const T)) (d₂ : R.constantType k₂ = some (.const T)) :
    ∃ w, R.isUniverse w ∧ Typed R .nil (recType T (.sort lv) [(k₁, []), (k₂, [])]) (.head w) := by
  have tT : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed R Δ (.const T) U0 := fun {_ _} => tw.small dT
  have t₁ : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed R Δ (.const k₁) (.const T) :=
    fun {_ _} => .const d₁ tT (tw.isUniverse _)
  have t₂ : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed R Δ (.const k₂) (.const T) :=
    fun {_ _} => .const d₂ tT (tw.isUniverse _)
  have tM : Typed R .nil (.pi (.const T) (.head (.sort lv))) (.head (.sort (.max (.const 0) (.succ lv)))) :=
    .piForm tT (tw.isUniverse _) (.headType (tw.headTyping _)) (tw.isUniverse _) (tw.join _ _)
  let Γ₁ : Ctx Tower.Head 1 := .snoc .nil (.pi (.const T) (.head (.sort lv)))
  have tP₁ : Typed R Γ₁ (.var 0) (.pi (.const T) (.head (.sort lv))) := .var 0
  have e₁ : Typed R Γ₁ (.app (.var 0) (.const k₁)) (.head (.sort lv)) := .appElim tP₁ t₁
  let Γ₂ : Ctx Tower.Head 2 := .snoc Γ₁ (.app (.var 0) (.const k₁))
  have tP₂ : Typed R Γ₂ (.var 1) (.pi (.const T) (.head (.sort lv))) := .var 1
  have e₂ : Typed R Γ₂ (.app (.var 1) (.const k₂)) (.head (.sort lv)) := .appElim tP₂ t₂
  let Γ₃ : Ctx Tower.Head 3 := .snoc Γ₂ (.app (.var 1) (.const k₂))
  let Γ₄ : Ctx Tower.Head 4 := .snoc Γ₃ (.const T)
  have tP₄ : Typed R Γ₄ (.var 3) (.pi (.const T) (.head (.sort lv))) := .var 3
  have tx : Typed R Γ₄ (.var 0) (.const T) := .var 0
  have body : Typed R Γ₄ (.app (.var 3) (.var 0)) (.head (.sort lv)) := .appElim tP₄ tx
  have t₃ := Derivable.piForm (tT (Δ := Γ₃)) (tw.isUniverse _) body (tw.isUniverse _) (tw.join _ _)
  have t₂' := Derivable.piForm e₂ (tw.isUniverse _) t₃ (tw.isUniverse _) (tw.join _ _)
  have t₁' := Derivable.piForm e₁ (tw.isUniverse _) t₂' (tw.isUniverse _) (tw.join _ _)
  have t₀ := Derivable.piForm tM (tw.isUniverse _) t₁' (tw.isUniverse _) (tw.join _ _)
  exact ⟨_, tw.isUniverse _, t₀⟩

end RecursorTypes

/-! ### The recursor of the untyped expressions -/

/-- The motive type and the five method types of `raw-rec`, and the contexts they live in. -/
abbrev rawMot {n : Nat} : Tm Tower.Head n := .pi rawC (.head (.sort lv))
abbrev rawM₁ : Tm Tower.Head 1 := .pi numC (.app (.var 1) (rnumC (.var 0)))
abbrev rawM₂ : Tm Tower.Head 2 := .pi boolC (.app (.var 2) (rboolC (.var 0)))
abbrev rawM₃ : Tm Tower.Head 3 :=
  .pi rawC (.pi rawC (.pi (.app (.var 4) (.var 1)) (.pi (.app (.var 5) (.var 1))
    (.app (.var 6) (raddC (.var 3) (.var 2))))))
abbrev rawM₄ : Tm Tower.Head 4 :=
  .pi rawC (.pi rawC (.pi rawC (.pi (.app (.var 6) (.var 2)) (.pi (.app (.var 7) (.var 2))
    (.pi (.app (.var 8) (.var 2)) (.app (.var 9) (rifC (.var 5) (.var 4) (.var 3))))))))
abbrev rawM₅ : Tm Tower.Head 5 := .pi rawC (.pi (.app (.var 5) (.var 0)) (.app (.var 6) (rzeroC (.var 1))))
abbrev rawΓ₁ : Ctx Tower.Head 1 := .snoc .nil (rawMot lv)
abbrev rawΓ₂ : Ctx Tower.Head 2 := .snoc (rawΓ₁ lv) rawM₁
abbrev rawΓ₃ : Ctx Tower.Head 3 := .snoc (rawΓ₂ lv) rawM₂
abbrev rawΓ₄ : Ctx Tower.Head 4 := .snoc (rawΓ₃ lv) rawM₃
abbrev rawΓ₅ : Ctx Tower.Head 5 := .snoc (rawΓ₄ lv) rawM₄
abbrev rawΓ₆ : Ctx Tower.Head 6 := .snoc (rawΓ₅ lv) rawM₅

theorem rawRecType_split : recType raw (.sort lv) rawCtors =
    .pi (rawMot lv) (.pi rawM₁ (.pi rawM₂ (.pi rawM₃ (.pi rawM₄ (.pi rawM₅ (.pi rawC (.app (.var 6) (.var 0)))))))) :=
  rawRecType_eq lv

/-- A package declaring the untyped expressions, their constructors, the numbers and the Booleans. -/
structure RawDeclared (R : Rules Tower.Head) : Prop where
  tower : TowerLike R
  dRaw : R.constantType raw = some (.head u)
  dNum : R.constantType num = some (.head u)
  dBool : R.constantType bool = some (.head u)
  dRnum : R.constantType rnum = some (.pi numC rawC)
  dRbool : R.constantType rbool = some (.pi boolC rawC)
  dRadd : R.constantType radd = some (.pi rawC (.pi rawC rawC))
  dRif : R.constantType rif = some (.pi rawC (.pi rawC (.pi rawC rawC)))
  dRzero : R.constantType rzero = some (.pi rawC rawC)

namespace RawDeclared

variable {R : Rules Tower.Head} (D : RawDeclared R) {m : Nat} {Δ : Ctx Tower.Head m}
include D

theorem raw_typed : Typed R Δ rawC U0 := D.tower.small D.dRaw
theorem num_typed : Typed R Δ numC U0 := D.tower.small D.dNum
theorem bool_typed : Typed R Δ boolC U0 := D.tower.small D.dBool

theorem rnum_app {k : Tm Tower.Head m} (tk : Typed R Δ k numC) : Typed R Δ (rnumC k) rawC :=
  .appElim (A := numC) (B := rawC)
    (.const (type := .pi numC rawC) D.dRnum (D.tower.pi_small D.num_typed D.raw_typed) (D.tower.isUniverse _)) tk

theorem rbool_app {b : Tm Tower.Head m} (tb : Typed R Δ b boolC) : Typed R Δ (rboolC b) rawC :=
  .appElim (A := boolC) (B := rawC)
    (.const (type := .pi boolC rawC) D.dRbool (D.tower.pi_small D.bool_typed D.raw_typed)
      (D.tower.isUniverse _)) tb

theorem radd_app {a b : Tm Tower.Head m} (ta : Typed R Δ a rawC) (tb : Typed R Δ b rawC) :
    Typed R Δ (raddC a b) rawC :=
  .appElim (A := rawC) (B := rawC) (.appElim (A := rawC) (B := .pi rawC rawC)
    (.const (type := .pi rawC (.pi rawC rawC)) D.dRadd
      (D.tower.pi_small D.raw_typed (D.tower.pi_small D.raw_typed D.raw_typed)) (D.tower.isUniverse _)) ta) tb

theorem rif_app {c a b : Tm Tower.Head m} (tc : Typed R Δ c rawC) (ta : Typed R Δ a rawC)
    (tb : Typed R Δ b rawC) : Typed R Δ (rifC c a b) rawC :=
  .appElim (A := rawC) (B := rawC) (.appElim (A := rawC) (B := .pi rawC rawC)
    (.appElim (A := rawC) (B := .pi rawC (.pi rawC rawC))
      (.const (type := .pi rawC (.pi rawC (.pi rawC rawC))) D.dRif
        (D.tower.pi_small D.raw_typed (D.tower.pi_small D.raw_typed (D.tower.pi_small D.raw_typed D.raw_typed)))
        (D.tower.isUniverse _)) tc) ta) tb

theorem rzero_app {a : Tm Tower.Head m} (ta : Typed R Δ a rawC) : Typed R Δ (rzeroC a) rawC :=
  .appElim (A := rawC) (B := rawC)
    (.const (type := .pi rawC rawC) D.dRzero (D.tower.pi_small D.raw_typed D.raw_typed) (D.tower.isUniverse _)) ta

theorem mot_typed : Typed R .nil (rawMot lv) (.head (.sort (.max (.const 0) (.succ lv)))) :=
  .piForm D.raw_typed (D.tower.isUniverse _) (.headType (D.tower.headTyping _)) (D.tower.isUniverse _)
    (D.tower.join _ _)

theorem m₁_typed : ∃ l, Typed R (rawΓ₁ lv) rawM₁ (.head (.sort l)) := by
  have tP : Typed R (.snoc (rawΓ₁ lv) numC) (.var 1) (rawMot lv) := .var 1
  have tk : Typed R (.snoc (rawΓ₁ lv) numC) (.var 0) numC := .var 0
  have body : Typed R (.snoc (rawΓ₁ lv) numC) (.app (.var 1) (rnumC (.var 0))) (.head (.sort lv)) :=
    .appElim (A := rawC) (B := .head (.sort lv)) tP (D.rnum_app tk)
  exact ⟨_, .piForm D.num_typed (D.tower.isUniverse _) body (D.tower.isUniverse _) (D.tower.join _ _)⟩

theorem m₂_typed : ∃ l, Typed R (rawΓ₂ lv) rawM₂ (.head (.sort l)) := by
  have tP : Typed R (.snoc (rawΓ₂ lv) boolC) (.var 2) (rawMot lv) := .var 2
  have tb : Typed R (.snoc (rawΓ₂ lv) boolC) (.var 0) boolC := .var 0
  have body : Typed R (.snoc (rawΓ₂ lv) boolC) (.app (.var 2) (rboolC (.var 0))) (.head (.sort lv)) :=
    .appElim (A := rawC) (B := .head (.sort lv)) tP (D.rbool_app tb)
  exact ⟨_, .piForm D.bool_typed (D.tower.isUniverse _) body (D.tower.isUniverse _) (D.tower.join _ _)⟩

theorem m₃_typed : ∃ l, Typed R (rawΓ₃ lv) rawM₃ (.head (.sort l)) := by
  have tP₅ : Typed R (.snoc (.snoc (rawΓ₃ lv) rawC) rawC) (.var 4) (rawMot lv) := .var 4
  have ta₅ : Typed R (.snoc (.snoc (rawΓ₃ lv) rawC) rawC) (.var 1) rawC := .var 1
  have ha : Typed R (.snoc (.snoc (rawΓ₃ lv) rawC) rawC) (.app (.var 4) (.var 1)) (.head (.sort lv)) :=
    .appElim (A := rawC) (B := .head (.sort lv)) tP₅ ta₅
  have tP₆ : Typed R (.snoc (.snoc (.snoc (rawΓ₃ lv) rawC) rawC) (.app (.var 4) (.var 1))) (.var 5)
      (rawMot lv) := .var 5
  have tb₆ : Typed R (.snoc (.snoc (.snoc (rawΓ₃ lv) rawC) rawC) (.app (.var 4) (.var 1))) (.var 1) rawC :=
    .var 1
  have hb : Typed R (.snoc (.snoc (.snoc (rawΓ₃ lv) rawC) rawC) (.app (.var 4) (.var 1)))
      (.app (.var 5) (.var 1)) (.head (.sort lv)) :=
    .appElim (A := rawC) (B := .head (.sort lv)) tP₆ tb₆
  have tP₇ : Typed R (.snoc (.snoc (.snoc (.snoc (rawΓ₃ lv) rawC) rawC) (.app (.var 4) (.var 1)))
      (.app (.var 5) (.var 1))) (.var 6) (rawMot lv) := .var 6
  have ta₇ : Typed R (.snoc (.snoc (.snoc (.snoc (rawΓ₃ lv) rawC) rawC) (.app (.var 4) (.var 1)))
      (.app (.var 5) (.var 1))) (.var 3) rawC := .var 3
  have tb₇ : Typed R (.snoc (.snoc (.snoc (.snoc (rawΓ₃ lv) rawC) rawC) (.app (.var 4) (.var 1)))
      (.app (.var 5) (.var 1))) (.var 2) rawC := .var 2
  have r : Typed R (.snoc (.snoc (.snoc (.snoc (rawΓ₃ lv) rawC) rawC) (.app (.var 4) (.var 1)))
      (.app (.var 5) (.var 1))) (.app (.var 6) (raddC (.var 3) (.var 2))) (.head (.sort lv)) :=
    .appElim (A := rawC) (B := .head (.sort lv)) tP₇ (D.radd_app ta₇ tb₇)
  have s₁ := Derivable.piForm hb (D.tower.isUniverse _) r (D.tower.isUniverse _) (D.tower.join _ _)
  have s₂ := Derivable.piForm ha (D.tower.isUniverse _) s₁ (D.tower.isUniverse _) (D.tower.join _ _)
  have s₃ := Derivable.piForm D.raw_typed (D.tower.isUniverse _) s₂ (D.tower.isUniverse _) (D.tower.join _ _)
  exact ⟨_, Derivable.piForm D.raw_typed (D.tower.isUniverse _) s₃ (D.tower.isUniverse _) (D.tower.join _ _)⟩

/-- The method type for `rif`, over any context whose variable `3` is a motive: the context is kept
abstract, so that its entries are never compared. -/
theorem m₄_typed_gen {Γ : Ctx Tower.Head 4} (hP : Typed R Γ (.var 3) (rawMot lv)) :
    ∃ l, Typed R Γ rawM₄ (.head (.sort l)) := by
  have tP₇ : Typed R (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) (.var 6) (rawMot lv) :=
    hP.weaken.weaken.weaken
  have tc₇ : Typed R (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) (.var 2) rawC := .var 2
  have hc : Typed R (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) (.app (.var 6) (.var 2)) (.head (.sort lv)) :=
    .appElim (A := rawC) (B := .head (.sort lv)) tP₇ tc₇
  have tP₈ : Typed R (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) (.app (.var 6) (.var 2)))
      (.var 7) (rawMot lv) := tP₇.weaken
  have ta₈ : Typed R (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) (.app (.var 6) (.var 2)))
      (.var 2) rawC := .var 2
  have ha : Typed R (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) (.app (.var 6) (.var 2)))
      (.app (.var 7) (.var 2)) (.head (.sort lv)) :=
    .appElim (A := rawC) (B := .head (.sort lv)) tP₈ ta₈
  have tP₉ : Typed R (.snoc (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) (.app (.var 6) (.var 2)))
      (.app (.var 7) (.var 2))) (.var 8) (rawMot lv) := tP₈.weaken
  have tb₉ : Typed R (.snoc (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) (.app (.var 6) (.var 2)))
      (.app (.var 7) (.var 2))) (.var 2) rawC := .var 2
  have hb : Typed R (.snoc (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC) (.app (.var 6) (.var 2)))
      (.app (.var 7) (.var 2))) (.app (.var 8) (.var 2)) (.head (.sort lv)) :=
    .appElim (A := rawC) (B := .head (.sort lv)) tP₉ tb₉
  have tP₁₀ : Typed R (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC)
      (.app (.var 6) (.var 2))) (.app (.var 7) (.var 2))) (.app (.var 8) (.var 2))) (.var 9) (rawMot lv) :=
    tP₉.weaken
  have tc₁₀ : Typed R (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC)
      (.app (.var 6) (.var 2))) (.app (.var 7) (.var 2))) (.app (.var 8) (.var 2))) (.var 5) rawC := .var 5
  have ta₁₀ : Typed R (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC)
      (.app (.var 6) (.var 2))) (.app (.var 7) (.var 2))) (.app (.var 8) (.var 2))) (.var 4) rawC := .var 4
  have tb₁₀ : Typed R (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC)
      (.app (.var 6) (.var 2))) (.app (.var 7) (.var 2))) (.app (.var 8) (.var 2))) (.var 3) rawC := .var 3
  have r : Typed R (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc Γ rawC) rawC) rawC)
      (.app (.var 6) (.var 2))) (.app (.var 7) (.var 2))) (.app (.var 8) (.var 2)))
      (.app (.var 9) (rifC (.var 5) (.var 4) (.var 3))) (.head (.sort lv)) :=
    .appElim (A := rawC) (B := .head (.sort lv)) tP₁₀ (D.rif_app tc₁₀ ta₁₀ tb₁₀)
  have s₁ := Derivable.piForm hb (D.tower.isUniverse _) r (D.tower.isUniverse _) (D.tower.join _ _)
  have s₂ := Derivable.piForm ha (D.tower.isUniverse _) s₁ (D.tower.isUniverse _) (D.tower.join _ _)
  have s₃ := Derivable.piForm hc (D.tower.isUniverse _) s₂ (D.tower.isUniverse _) (D.tower.join _ _)
  have s₄ := Derivable.piForm D.raw_typed (D.tower.isUniverse _) s₃ (D.tower.isUniverse _) (D.tower.join _ _)
  have s₅ := Derivable.piForm D.raw_typed (D.tower.isUniverse _) s₄ (D.tower.isUniverse _) (D.tower.join _ _)
  exact ⟨_, Derivable.piForm D.raw_typed (D.tower.isUniverse _) s₅ (D.tower.isUniverse _) (D.tower.join _ _)⟩

theorem m₄_typed : ∃ l, Typed R (rawΓ₄ lv) rawM₄ (.head (.sort l)) := by
  have hP : Typed R (rawΓ₄ lv) (.var 3) (rawMot lv) := .var 3
  exact D.m₄_typed_gen lv hP

theorem m₅_typed : ∃ l, Typed R (rawΓ₅ lv) rawM₅ (.head (.sort l)) := by
  have tP₆ : Typed R (.snoc (rawΓ₅ lv) rawC) (.var 5) (rawMot lv) := .var 5
  have ta₆ : Typed R (.snoc (rawΓ₅ lv) rawC) (.var 0) rawC := .var 0
  have ha : Typed R (.snoc (rawΓ₅ lv) rawC) (.app (.var 5) (.var 0)) (.head (.sort lv)) :=
    .appElim (A := rawC) (B := .head (.sort lv)) tP₆ ta₆
  have tP₇ : Typed R (.snoc (.snoc (rawΓ₅ lv) rawC) (.app (.var 5) (.var 0))) (.var 6) (rawMot lv) := .var 6
  have ta₇ : Typed R (.snoc (.snoc (rawΓ₅ lv) rawC) (.app (.var 5) (.var 0))) (.var 1) rawC := .var 1
  have r : Typed R (.snoc (.snoc (rawΓ₅ lv) rawC) (.app (.var 5) (.var 0))) (.app (.var 6) (rzeroC (.var 1)))
      (.head (.sort lv)) :=
    .appElim (A := rawC) (B := .head (.sort lv)) tP₇ (D.rzero_app ta₇)
  have s₁ := Derivable.piForm ha (D.tower.isUniverse _) r (D.tower.isUniverse _) (D.tower.join _ _)
  exact ⟨_, Derivable.piForm D.raw_typed (D.tower.isUniverse _) s₁ (D.tower.isUniverse _) (D.tower.join _ _)⟩

theorem result_typed : ∃ l, Typed R (rawΓ₆ lv) (.pi rawC (.app (.var 6) (.var 0))) (.head (.sort l)) := by
  have tP : Typed R (.snoc (rawΓ₆ lv) rawC) (.var 6) (rawMot lv) := .var 6
  have tx : Typed R (.snoc (rawΓ₆ lv) rawC) (.var 0) rawC := .var 0
  have body : Typed R (.snoc (rawΓ₆ lv) rawC) (.app (.var 6) (.var 0)) (.head (.sort lv)) :=
    .appElim (A := rawC) (B := .head (.sort lv)) tP tx
  exact ⟨_, Derivable.piForm D.raw_typed (D.tower.isUniverse _) body (D.tower.isUniverse _) (D.tower.join _ _)⟩

/-- **The recursor of the untyped expressions is typed.** -/
theorem recType_typed : ∃ w, R.isUniverse w ∧ Typed R .nil (recType raw (.sort lv) rawCtors) (.head w) := by
  rw [rawRecType_split lv]
  obtain ⟨_, t₆⟩ := D.result_typed lv
  obtain ⟨_, e₅⟩ := D.m₅_typed lv
  obtain ⟨_, e₄⟩ := D.m₄_typed lv
  obtain ⟨_, e₃⟩ := D.m₃_typed lv
  obtain ⟨_, e₂⟩ := D.m₂_typed lv
  obtain ⟨_, e₁⟩ := D.m₁_typed lv
  have t₅ := Derivable.piForm e₅ (D.tower.isUniverse _) t₆ (D.tower.isUniverse _) (D.tower.join _ _)
  have t₄ := Derivable.piForm e₄ (D.tower.isUniverse _) t₅ (D.tower.isUniverse _) (D.tower.join _ _)
  have t₃ := Derivable.piForm e₃ (D.tower.isUniverse _) t₄ (D.tower.isUniverse _) (D.tower.join _ _)
  have t₂ := Derivable.piForm e₂ (D.tower.isUniverse _) t₃ (D.tower.isUniverse _) (D.tower.join _ _)
  have t₁ := Derivable.piForm e₁ (D.tower.isUniverse _) t₂ (D.tower.isUniverse _) (D.tower.join _ _)
  exact ⟨_, D.tower.isUniverse _, Derivable.piForm (D.mot_typed lv) (D.tower.isUniverse _) t₁
    (D.tower.isUniverse _) (D.tower.join _ _)⟩

end RawDeclared

/-! ## The declarations of the inductive types -/

/-- The earlier stage of the untyped expressions: the numbers and the Booleans. -/
def rawNames₀ : List DeclName := [num, zero, succ, bool, btrue, bfalse]
def rawNames₁ : List DeclName := raw :: rawNames₀
def rawNames₂ : List DeclName := rnum :: rbool :: radd :: rif :: rzero :: rawNames₁

section Declarations

variable (valuation : Nat → Nat) {E : GenericEquality Tower.Head}

/-- The package declares the natural numbers. -/
theorem declaresNum :
    DeclaresInductive (settingAt lv valuation E) (constantFreeRules (rules lv)) TowerNumbersModel.rules₁
      TowerNumbersModel.rules₂ num u ctors numRec (.sort lv) where
  role := roles_num
  recRole := roles_numRec
  hu := LevelTower.IsUniverse.sort _
  hv := LevelTower.IsUniverse.sort _
  sub₀ := RulesSub.constantFree _
  sub₁ := sub_numbers₁ lv
  sub₂ := sub_numbers₂ lv
  semantic₀ := fun declared => nomatch declared
  stage₁ := (TowerNumbersModel.declares lv valuation).stage₁
  stage₂ := (TowerNumbersModel.declares lv valuation).stage₂
  declared := rfl
  ctorDeclared := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  recDeclared := rfl
  fieldTyped := (TowerNumbersModel.declares lv valuation).fieldTyped
  ctorTyped := (TowerNumbersModel.declares lv valuation).ctorTyped
  recTyped := (TowerNumbersModel.declares lv valuation).recTyped
  iota := fun hms hi has hm =>
    RootComputation.step_unionAll mem_numRec ⟨_, _, _, _, _, _, _, hms, hi, has, hm, rfl, rfl⟩

/-- The package declares the unit type; the stage facts are those of the vectors package's
declaration, whose statements concern the stages only. -/
theorem declaresUnit :
    DeclaresInductive (settingAt lv valuation E) (constantFreeRules (rules lv)) TowerVectorsModel.unitStage₁
      TowerVectorsModel.unitStage₂ unit u unitCtors unitRec (.sort lv) where
  role := roles_unit
  recRole := roles_unitRec
  hu := LevelTower.IsUniverse.sort _
  hv := LevelTower.IsUniverse.sort _
  sub₀ := RulesSub.constantFree _
  sub₁ := sub_unit₁ lv
  sub₂ := sub_unit₂ lv
  semantic₀ := fun declared => nomatch declared
  stage₁ := (TowerVectorsModel.declaresUnit lv (fun _ => 0)
    (E := declarative (TowerVectorsModel.rules lv))).stage₁
  stage₂ := (TowerVectorsModel.declaresUnit lv (fun _ => 0)
    (E := declarative (TowerVectorsModel.rules lv))).stage₂
  declared := rfl
  ctorDeclared := by
    intro k fields mem
    simp only [unitCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    obtain ⟨rfl, rfl⟩ := mem
    rfl
  recDeclared := rfl
  fieldTyped := (TowerVectorsModel.declaresUnit lv (fun _ => 0)
    (E := declarative (TowerVectorsModel.rules lv))).fieldTyped
  ctorTyped := (TowerVectorsModel.declaresUnit lv (fun _ => 0)
    (E := declarative (TowerVectorsModel.rules lv))).ctorTyped
  recTyped := (TowerVectorsModel.declaresUnit lv (fun _ => 0)
    (E := declarative (TowerVectorsModel.rules lv))).recTyped
  iota := fun hms hi has hm =>
    RootComputation.step_unionAll mem_unitRec ⟨_, _, _, _, _, _, _, hms, hi, has, hm, rfl, rfl⟩

/-- The package declares the empty type; the stage facts are those of the vectors package's
declaration. -/
theorem declaresVoid :
    DeclaresInductive (settingAt lv valuation E) (constantFreeRules (rules lv)) TowerVectorsModel.voidStage
      TowerVectorsModel.voidStage void u [] voidRec (.sort lv) where
  role := roles_void
  recRole := roles_voidRec
  hu := LevelTower.IsUniverse.sort _
  hv := LevelTower.IsUniverse.sort _
  sub₀ := RulesSub.constantFree _
  sub₁ := sub_void lv
  sub₂ := sub_void lv
  semantic₀ := fun declared => nomatch declared
  stage₁ := (TowerVectorsModel.declaresVoid lv (fun _ => 0)
    (E := declarative (TowerVectorsModel.rules lv))).stage₁
  stage₂ := (TowerVectorsModel.declaresVoid lv (fun _ => 0)
    (E := declarative (TowerVectorsModel.rules lv))).stage₂
  declared := rfl
  ctorDeclared := fun mem => absurd mem List.not_mem_nil
  recDeclared := rfl
  fieldTyped := (TowerVectorsModel.declaresVoid lv (fun _ => 0)
    (E := declarative (TowerVectorsModel.rules lv))).fieldTyped
  ctorTyped := (TowerVectorsModel.declaresVoid lv (fun _ => 0)
    (E := declarative (TowerVectorsModel.rules lv))).ctorTyped
  recTyped := TowerVectorsModel.voidRecType_typed lv
  iota := fun _ found _ _ => by simp at found

/-- The first stage of a type with two constructors without fields lists the type alone; the second
adds the constructors. Its first stage is reached from the constant-free package. -/
theorem stage₁_single {T : DeclName} (dT : constantType lv T = some (.head u)) {name : DeclName}
    {type : Tm Tower.Head 0} (declared : (restrict lv [T]).constantType name = some type) :
    (constantFreeRules (rules lv)).constantType name = some type ∨ (name = T ∧ type = .head u) := by
  rcases restrict_cons lv declared with h | ⟨rfl, h⟩
  · obtain ⟨mem, -⟩ := restrict_declared lv h
    exact absurd mem List.not_mem_nil
  · rw [dT] at h
    exact .inr ⟨rfl, (Option.some.inj h).symm⟩

theorem stage₂_two {T k₁ k₂ : DeclName} (d₁ : constantType lv k₁ = some (ctorType T []))
    (d₂ : constantType lv k₂ = some (ctorType T [])) {name : DeclName} {type : Tm Tower.Head 0}
    (declared : (restrict lv [k₁, k₂, T]).constantType name = some type) :
    (restrict lv [T]).constantType name = some type ∨
      ∃ fields, (name, fields) ∈ [(k₁, ([] : List (Field Tower.Head))), (k₂, [])] ∧
        type = ctorType T fields := by
  rcases restrict_cons lv declared with h | ⟨rfl, h⟩
  · rcases restrict_cons lv h with h' | ⟨rfl, h'⟩
    · exact .inl h'
    · rw [d₂] at h'
      exact .inr ⟨[], by simp, (Option.some.inj h').symm⟩
  · rw [d₁] at h
    exact .inr ⟨[], by simp, (Option.some.inj h).symm⟩

/-- The package declares the Booleans. -/
theorem declaresBool :
    DeclaresInductive (settingAt lv valuation E) (constantFreeRules (rules lv)) (restrict lv [bool])
      (restrict lv [btrue, bfalse, bool]) bool u boolCtors boolRec (.sort lv) where
  role := roles_bool
  recRole := roles_boolRec
  hu := LevelTower.IsUniverse.sort _
  hv := LevelTower.IsUniverse.sort _
  sub₀ := RulesSub.constantFree _
  sub₁ := sub_restrict lv _ (by decide)
  sub₂ := sub_restrict lv _ (by decide)
  semantic₀ := fun declared => nomatch declared
  stage₁ := stage₁_single lv rfl
  stage₂ := stage₂_two lv rfl rfl
  declared := rfl
  ctorDeclared := by
    intro k fields mem
    simp only [boolCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  recDeclared := rfl
  fieldTyped := by
    intro k fields F mem closed
    simp only [boolCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at closed
  ctorTyped := by
    intro k fields mem
    simp only [boolCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨_, LevelTower.IsUniverse.sort _, (towerLike_restrict lv [bool]).small (c := bool) rfl⟩
  recTyped := twoRecType_typed lv (towerLike_restrict lv [btrue, bfalse, bool]) (T := bool) (k₁ := btrue)
    (k₂ := bfalse) rfl rfl rfl
  iota := fun hms hi has hm =>
    RootComputation.step_unionAll mem_boolRec ⟨_, _, _, _, _, _, _, hms, hi, has, hm, rfl, rfl⟩

/-- The package declares the object types. -/
theorem declaresTy :
    DeclaresInductive (settingAt lv valuation E) (constantFreeRules (rules lv)) (restrict lv [ty])
      (restrict lv [tnum, tbool, ty]) ty u tyCtors tyRec (.sort lv) where
  role := roles_ty
  recRole := roles_tyRec
  hu := LevelTower.IsUniverse.sort _
  hv := LevelTower.IsUniverse.sort _
  sub₀ := RulesSub.constantFree _
  sub₁ := sub_restrict lv _ (by decide)
  sub₂ := sub_restrict lv _ (by decide)
  semantic₀ := fun declared => nomatch declared
  stage₁ := stage₁_single lv rfl
  stage₂ := stage₂_two lv rfl rfl
  declared := rfl
  ctorDeclared := by
    intro k fields mem
    simp only [tyCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  recDeclared := rfl
  fieldTyped := by
    intro k fields F mem closed
    simp only [tyCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at closed
  ctorTyped := by
    intro k fields mem
    simp only [tyCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨_, LevelTower.IsUniverse.sort _, (towerLike_restrict lv [ty]).small (c := ty) rfl⟩
  recTyped := twoRecType_typed lv (towerLike_restrict lv [tnum, tbool, ty]) (T := ty) (k₁ := tnum)
    (k₂ := tbool) rfl rfl rfl
  iota := fun hms hi has hm =>
    RootComputation.step_unionAll mem_tyRec ⟨_, _, _, _, _, _, _, hms, hi, has, hm, rfl, rfl⟩

variable (lawsE : E.Laws (rules lv) roles)
include lawsE

/-- The earlier stage of the untyped expressions is semantic: numbers and Booleans. -/
theorem semantic_raw₀ : AllSemantic (settingAt lv valuation E) (restrict lv rawNames₀) := by
  refine allSemantic_restrict lv fun name mem type declared => ?_
  simp only [rawNames₀, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl <;> cases declared
  · exact (declaresNum lv valuation).type_semantic lawsE
  · exact (declaresNum lv valuation).ctor_semantic lawsE mem_zero
  · exact (declaresNum lv valuation).ctor_semantic lawsE mem_succ
  · exact (declaresBool lv valuation).type_semantic lawsE
  · exact (declaresBool lv valuation).ctor_semantic lawsE mem_btrue
  · exact (declaresBool lv valuation).ctor_semantic lawsE mem_bfalse

omit lawsE in
theorem raw_stage₁ {name : DeclName} {type : Tm Tower.Head 0}
    (declared : (restrict lv rawNames₁).constantType name = some type) :
    (restrict lv rawNames₀).constantType name = some type ∨ (name = raw ∧ type = .head u) := by
  rcases restrict_cons lv declared with h | ⟨rfl, h⟩
  · exact .inl h
  · exact .inr ⟨rfl, (Option.some.inj h).symm⟩

omit lawsE in
theorem raw_stage₂ {name : DeclName} {type : Tm Tower.Head 0}
    (declared : (restrict lv rawNames₂).constantType name = some type) :
    (restrict lv rawNames₁).constantType name = some type ∨
      ∃ fields, (name, fields) ∈ rawCtors ∧ type = ctorType raw fields := by
  rcases restrict_cons lv declared with h | ⟨rfl, h⟩
  · rcases restrict_cons lv h with h | ⟨rfl, h⟩
    · rcases restrict_cons lv h with h | ⟨rfl, h⟩
      · rcases restrict_cons lv h with h | ⟨rfl, h⟩
        · rcases restrict_cons lv h with h | ⟨rfl, h⟩
          · exact .inl h
          · exact .inr ⟨_, mem_rzero, (Option.some.inj h).symm⟩
        · exact .inr ⟨_, mem_rif, (Option.some.inj h).symm⟩
      · exact .inr ⟨_, mem_radd, (Option.some.inj h).symm⟩
    · exact .inr ⟨_, mem_rbool, (Option.some.inj h).symm⟩
  · exact .inr ⟨_, mem_rnum, (Option.some.inj h).symm⟩

/-- **The package declares the untyped expressions**, with the closed fields `num` and `bool`. -/
theorem declaresRaw :
    DeclaresInductive (settingAt lv valuation E) (restrict lv rawNames₀) (restrict lv rawNames₁)
      (restrict lv rawNames₂) raw u rawCtors rawRec (.sort lv) where
  role := roles_raw
  recRole := roles_rawRec
  hu := LevelTower.IsUniverse.sort _
  hv := LevelTower.IsUniverse.sort _
  sub₀ := sub_restrict lv _ (by decide)
  sub₁ := sub_restrict lv _ (by decide)
  sub₂ := sub_restrict lv _ (by decide)
  semantic₀ := semantic_raw₀ lv valuation lawsE
  stage₁ := raw_stage₁ lv
  stage₂ := raw_stage₂ lv
  declared := rfl
  ctorDeclared := by
    intro k fields mem
    simp only [rawCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  recDeclared := rfl
  fieldTyped := by
    intro k fields F mem closed
    simp only [rawCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [List.mem_cons, Field.closed.injEq, List.not_mem_nil, or_false] at closed
      subst closed
      exact (towerLike_restrict lv rawNames₀).small (c := num) rfl
    · simp only [List.mem_cons, Field.closed.injEq, List.not_mem_nil, or_false] at closed
      subst closed
      exact (towerLike_restrict lv rawNames₀).small (c := bool) rfl
    · simp at closed
    · simp at closed
    · simp at closed
  ctorTyped := by
    intro k fields mem
    have tw := towerLike_restrict lv rawNames₁
    have tRaw : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed (restrict lv rawNames₁) Δ rawC U0 :=
      fun {_ _} => tw.small rfl
    simp only [rawCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, LevelTower.IsUniverse.sort _, tw.pi_small (tw.small rfl) tRaw⟩
    · exact ⟨_, LevelTower.IsUniverse.sort _, tw.pi_small (tw.small rfl) tRaw⟩
    · exact ⟨_, LevelTower.IsUniverse.sort _, tw.pi_small tRaw (tw.pi_small tRaw tRaw)⟩
    · exact ⟨_, LevelTower.IsUniverse.sort _, tw.pi_small tRaw (tw.pi_small tRaw (tw.pi_small tRaw tRaw))⟩
    · exact ⟨_, LevelTower.IsUniverse.sort _, tw.pi_small tRaw tRaw⟩
  recTyped := RawDeclared.recType_typed lv (R := restrict lv rawNames₂)
    ⟨towerLike_restrict lv rawNames₂, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  iota := fun hms hi has hm =>
    RootComputation.step_unionAll mem_rawRec ⟨_, _, _, _, _, _, _, hms, hi, has, hm, rfl, rfl⟩

/-! ## The base stage is semantic -/

/-- **Every constant of the base stage is semantic**: the six inductive types and their constructors. -/
theorem semantic_base : AllSemantic (settingAt lv valuation E) (baseStage lv) := by
  refine allSemantic_restrict lv fun name mem type declared => ?_
  simp only [baseNames, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> cases declared
  · exact (declaresNum lv valuation).type_semantic lawsE
  · exact (declaresNum lv valuation).ctor_semantic lawsE mem_zero
  · exact (declaresNum lv valuation).ctor_semantic lawsE mem_succ
  · exact (declaresUnit lv valuation).type_semantic lawsE
  · exact (declaresUnit lv valuation).ctor_semantic lawsE TowerVectorsModel.mem_tt
  · exact (declaresVoid lv valuation).type_semantic lawsE
  · exact (declaresBool lv valuation).type_semantic lawsE
  · exact (declaresBool lv valuation).ctor_semantic lawsE mem_btrue
  · exact (declaresBool lv valuation).ctor_semantic lawsE mem_bfalse
  · exact (declaresTy lv valuation).type_semantic lawsE
  · exact (declaresTy lv valuation).ctor_semantic lawsE mem_tnum
  · exact (declaresTy lv valuation).ctor_semantic lawsE mem_tbool
  · exact (declaresRaw lv valuation lawsE).type_semantic lawsE
  · exact (declaresRaw lv valuation lawsE).ctor_semantic lawsE mem_rnum
  · exact (declaresRaw lv valuation lawsE).ctor_semantic lawsE mem_rbool
  · exact (declaresRaw lv valuation lawsE).ctor_semantic lawsE mem_radd
  · exact (declaresRaw lv valuation lawsE).ctor_semantic lawsE mem_rif
  · exact (declaresRaw lv valuation lawsE).ctor_semantic lawsE mem_rzero

/-! ## The families over the object types -/

omit lawsE in
/-- `ty → U0` is a type of the level above. -/
theorem tyFamily_typed {R : Rules Tower.Head} (tw : TowerLike R) (dTy : R.constantType ty = some (.head u))
    {m : Nat} {Δ : Ctx Tower.Head m} :
    Typed R Δ (.pi tyC U0) (.head (.sort (.max (.const 0) (.succ (.const 0))))) :=
  .piForm (tw.small dTy) (tw.isUniverse _) tw.u0_typed (tw.isUniverse _) (tw.join _ _)

/-- A family over the object types, by its two equations, with small values from the base stage. -/
theorem declaresTyFamily {f : DeclName} (role : roles f = .computes (0 + 1 + 0) (.split 0 .constructor fun _ => .leaf))
    (declared : (rules lv).constantType f = some tyFamType)
    (body : (k : DeclName) → (fields : List (Field Tower.Head)) →
      Tm Tower.Head (0 + fields.length + 0 + (recPositions fields).length))
    (atNum' : Typed (baseStage lv) .nil (body tnum []) U0) (atBool' : Typed (baseStage lv) .nil (body tbool []) U0)
    (rule : ∀ {k : DeclName} {fields : List (Field Tower.Head)}, (k, fields) ∈ tyCtors →
      ∀ {m : Nat} (σ : Sub Tower.Head (0 + 1 + 0) m) (as : List (Tm Tower.Head m)),
        as.length = fields.length →
        (rules lv).computation.step
          (applyClosed (ofEntries tyEntries (0 + 1 + 0)) (replaceScrut 0 (appSpine (.const k) as) 0 σ) (.const f))
          (Presentation.subst (matchSub 0 fields.length as 0 σ)
            (Presentation.subst (hypSub f tyEntries 0 0 fields) (body k fields)))) :
    DeclaresRecursion (settingAt lv valuation E) (baseStage lv) f ty tyCtors tyEntries 0 0 U0 body where
  role := role
  scrutinee := rfl
  declared := declared
  sub₀ := sub_restrict lv _ (by decide)
  semantic₀ := semantic_base lv valuation lawsE
  typed := ⟨_, LevelTower.IsUniverse.sort _, tyFamily_typed (towerLike_restrict lv baseNames) rfl⟩
  formed := by
    intro k fields mem
    simp only [tyCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact .nil
  bodyTyped := by
    intro k fields mem
    simp only [tyCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact atNum'
    · exact atBool'
  rule := rule

/-- **The package declares `is-num`**: `unit` at `tnum`, `void` at `tbool`. -/
theorem declaresIsNum :
    DeclaresRecursion (settingAt lv valuation E) (baseStage lv) isNum ty tyCtors tyEntries 0 0 U0 isNumBody :=
  declaresTyFamily lv valuation lawsE roles_isNum rfl isNumBody
    ((towerLike_restrict lv baseNames).small (c := unit) rfl)
    ((towerLike_restrict lv baseNames).small (c := void) rfl)
    fun mem _ σ as has => RootComputation.step_unionAll mem_isNum ⟨_, _, σ, as, mem, has, rfl, rfl⟩

/-- **The package declares `is-bool`**: `void` at `tnum`, `unit` at `tbool`. -/
theorem declaresIsBool :
    DeclaresRecursion (settingAt lv valuation E) (baseStage lv) isBool ty tyCtors tyEntries 0 0 U0
      isBoolBody :=
  declaresTyFamily lv valuation lawsE roles_isBool rfl isBoolBody
    ((towerLike_restrict lv baseNames).small (c := void) rfl)
    ((towerLike_restrict lv baseNames).small (c := unit) rfl)
    fun mem _ σ as has => RootComputation.step_unionAll mem_isBool ⟨_, _, σ, as, mem, has, rfl, rfl⟩

/-- **The package declares the value type** `val`: `num` at `tnum`, `bool` at `tbool`. -/
theorem declaresVal :
    DeclaresRecursion (settingAt lv valuation E) (baseStage lv) val ty tyCtors tyEntries 0 0 U0 valBody :=
  declaresTyFamily lv valuation lawsE roles_val rfl valBody
    ((towerLike_restrict lv baseNames).small (c := num) rfl)
    ((towerLike_restrict lv baseNames).small (c := bool) rfl)
    fun mem _ σ as has => RootComputation.step_unionAll mem_val ⟨_, _, σ, as, mem, has, rfl, rfl⟩

/-- **The package declares the zero test** `is-zero : num → bool`. -/
theorem declaresIsZero :
    DeclaresRecursion (settingAt lv valuation E) (baseStage lv) isZero num ctors numEntries 0 0 boolC
      isZeroBody where
  role := roles_isZero
  scrutinee := rfl
  declared := rfl
  sub₀ := sub_restrict lv _ (by decide)
  semantic₀ := semantic_base lv valuation lawsE
  typed := ⟨_, LevelTower.IsUniverse.sort _,
    (towerLike_restrict lv baseNames).pi_small ((towerLike_restrict lv baseNames).small (c := num) rfl)
      ((towerLike_restrict lv baseNames).small (c := bool) rfl)⟩
  formed := by
    intro k fields mem
    have tw := towerLike_restrict lv baseNames
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .nil
    · show CtxFormed (baseStage lv) (.snoc (.snoc .nil numC) boolC)
      exact .snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, tw.small (c := num) rfl⟩)
        ⟨_, LevelTower.IsUniverse.sort _, tw.small (c := bool) rfl⟩
  bodyTyped := by
    intro k fields mem
    have tw := towerLike_restrict lv baseNames
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show Typed (baseStage lv) .nil btrueC boolC
      exact .const (type := ctorType bool []) rfl (tw.small (c := bool) rfl) (LevelTower.IsUniverse.sort _)
    · show Typed (baseStage lv) (.snoc (.snoc .nil numC) boolC) bfalseC boolC
      exact .const (type := ctorType bool []) rfl (tw.small (c := bool) rfl) (LevelTower.IsUniverse.sort _)
  rule := by
    intro k fields mem m σ as has
    exact RootComputation.step_unionAll mem_isZero ⟨_, _, σ, as, mem, has, rfl, rfl⟩

/-- **The package declares addition**, by recursion on its first argument. -/
theorem declaresAdd :
    DeclaresRecursion (settingAt lv valuation E) (baseStage lv) add num ctors TowerVectorsModel.addEntries 0 1
      numC TowerVectorsModel.addBody where
  role := roles_add
  scrutinee := rfl
  declared := rfl
  sub₀ := sub_restrict lv _ (by decide)
  semantic₀ := semantic_base lv valuation lawsE
  typed := ⟨_, LevelTower.IsUniverse.sort _,
    (towerLike_restrict lv baseNames).pi_small ((towerLike_restrict lv baseNames).small (c := num) rfl)
      ((towerLike_restrict lv baseNames).pi_small ((towerLike_restrict lv baseNames).small (c := num) rfl)
        ((towerLike_restrict lv baseNames).small (c := num) rfl))⟩
  formed := by
    intro k fields mem
    have tw := towerLike_restrict lv baseNames
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show CtxFormed (baseStage lv) (.snoc .nil numC)
      exact .snoc .nil ⟨_, tw.isUniverse _, tw.small rfl⟩
    · show CtxFormed (baseStage lv) (.snoc (.snoc (.snoc .nil numC) numC) (.pi numC numC))
      exact .snoc (.snoc (.snoc .nil ⟨_, tw.isUniverse _, tw.small rfl⟩) ⟨_, tw.isUniverse _, tw.small rfl⟩)
        ⟨_, tw.isUniverse _, tw.pi_small (tw.small rfl) (tw.small rfl)⟩
  bodyTyped := by
    intro k fields mem
    have tw := towerLike_restrict lv baseNames
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show Typed (baseStage lv) (.snoc .nil numC) (.var 0) numC
      exact .var 0
    · show Typed (baseStage lv) (.snoc (.snoc (.snoc .nil numC) numC) (.pi numC numC))
        (succC (.app (.var 0) (.var 1))) numC
      have th : Typed (baseStage lv) (.snoc (.snoc (.snoc .nil numC) numC) (.pi numC numC))
          (.var 0) (.pi numC numC) := .var 0
      have tm : Typed (baseStage lv) (.snoc (.snoc (.snoc .nil numC) numC) (.pi numC numC))
          (.var 1) numC := .var 1
      have tSucc : Typed (baseStage lv) (.snoc (.snoc (.snoc .nil numC) numC) (.pi numC numC))
          (.const succ) (.pi numC numC) :=
        .const (type := .pi numC numC) rfl (tw.pi_small (tw.small rfl) (tw.small rfl)) (tw.isUniverse _)
      exact .appElim tSucc (.appElim th tm)
  rule := by
    intro k fields mem m σ as has
    exact RootComputation.step_unionAll mem_add ⟨_, _, σ, as, mem, has, rfl, rfl⟩

/-! ## The typing relation -/

/-- The stage of the typing relation is semantic. -/
theorem semantic_typing : AllSemantic (settingAt lv valuation E) (typingStage lv) := by
  refine allSemantic_restrict lv fun name mem type declared => ?_
  rcases List.mem_cons.mp mem with rfl | mem
  · cases declared
    intro m Δ formed P r
    exact (declaresIsNum lv valuation lawsE).semantic lawsE (declaresTy lv valuation) formed r
  rcases List.mem_cons.mp mem with rfl | mem
  · cases declared
    intro m Δ formed P r
    exact (declaresIsBool lv valuation lawsE).semantic lawsE (declaresTy lv valuation) formed r
  exact semantic_base lv valuation lawsE (by rw [restrict_of_mem lv mem]; exact declared)

omit lawsE in
/-- The stage of the typing relation has the tower's universes. -/
theorem tw_typing : TowerLike (typingStage lv) := towerLike_restrict lv _

omit lawsE in
theorem typing_isNum_typed {m : Nat} {Δ : Ctx Tower.Head m} {t : Tm Tower.Head m}
    (tt' : Typed (typingStage lv) Δ t tyC) : Typed (typingStage lv) Δ (isNumC t) U0 :=
  .appElim (.const (type := .pi tyC U0) rfl (tyFamily_typed (tw_typing lv) rfl) (LevelTower.IsUniverse.sort _)) tt'

omit lawsE in
theorem typing_isBool_typed {m : Nat} {Δ : Ctx Tower.Head m} {t : Tm Tower.Head m}
    (tt' : Typed (typingStage lv) Δ t tyC) : Typed (typingStage lv) Δ (isBoolC t) U0 :=
  .appElim (.const (type := .pi tyC U0) rfl (tyFamily_typed (tw_typing lv) rfl) (LevelTower.IsUniverse.sort _)) tt'

omit lawsE in
theorem typing_tnum_typed {m : Nat} {Δ : Ctx Tower.Head m} : Typed (typingStage lv) Δ tnumC tyC :=
  .const (type := ctorType ty []) rfl ((tw_typing lv).small (c := ty) rfl) (LevelTower.IsUniverse.sort _)

omit lawsE in
theorem typing_tbool_typed {m : Nat} {Δ : Ctx Tower.Head m} : Typed (typingStage lv) Δ tboolC tyC :=
  .const (type := ctorType ty []) rfl ((tw_typing lv).small (c := ty) rfl) (LevelTower.IsUniverse.sort _)

/-- **The package declares the typing relation**, by recursion on the expression. -/
theorem declaresTyping :
    DeclaresRecursion (settingAt lv valuation E) (typingStage lv) typing raw rawCtors typingEntries 0 1 U0
      typingBody where
  role := roles_typing
  scrutinee := rfl
  declared := rfl
  sub₀ := sub_restrict lv _ (by decide)
  semantic₀ := semantic_typing lv valuation lawsE
  typed := ⟨_, LevelTower.IsUniverse.sort _, .piForm ((tw_typing lv).small (c := raw) rfl)
    (LevelTower.IsUniverse.sort _) (tyFamily_typed (tw_typing lv) rfl) (LevelTower.IsUniverse.sort _)
    (LevelTower.Join.sorts _ _)⟩
  formed := by
    intro k fields mem
    have tw := tw_typing lv
    have fTy : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, IsType (typingStage lv) Δ (.pi tyC U0) :=
      fun {_ _} => ⟨_, tw.isUniverse _, tyFamily_typed tw rfl⟩
    have sRaw : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, IsType (typingStage lv) Δ rawC :=
      fun {_ _} => ⟨_, tw.isUniverse _, tw.small rfl⟩
    have sTy : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, IsType (typingStage lv) Δ tyC :=
      fun {_ _} => ⟨_, tw.isUniverse _, tw.small rfl⟩
    simp only [rawCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show CtxFormed (typingStage lv) (.snoc (.snoc .nil numC) tyC)
      exact .snoc (.snoc .nil ⟨_, tw.isUniverse _, tw.small rfl⟩) sTy
    · show CtxFormed (typingStage lv) (.snoc (.snoc .nil boolC) tyC)
      exact .snoc (.snoc .nil ⟨_, tw.isUniverse _, tw.small rfl⟩) sTy
    · show CtxFormed (typingStage lv)
        (.snoc (.snoc (.snoc (.snoc (.snoc .nil rawC) rawC) tyC) (.pi tyC U0)) (.pi tyC U0))
      exact .snoc (.snoc (.snoc (.snoc (.snoc .nil sRaw) sRaw) sTy) fTy) fTy
    · show CtxFormed (typingStage lv)
        (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil rawC) rawC) rawC) tyC) (.pi tyC U0))
          (.pi tyC U0)) (.pi tyC U0))
      exact .snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil sRaw) sRaw) sRaw) sTy) fTy) fTy) fTy
    · show CtxFormed (typingStage lv) (.snoc (.snoc (.snoc .nil rawC) tyC) (.pi tyC U0))
      exact .snoc (.snoc (.snoc .nil sRaw) sTy) fTy
  bodyTyped := by
    intro k fields mem
    have tw := tw_typing lv
    simp only [rawCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show Typed (typingStage lv) (.snoc (.snoc .nil numC) tyC) (isNumC (.var 0)) U0
      exact typing_isNum_typed lv (.var 0)
    · show Typed (typingStage lv) (.snoc (.snoc .nil boolC) tyC) (isBoolC (.var 0)) U0
      exact typing_isBool_typed lv (.var 0)
    · let Γ : Ctx Tower.Head 5 :=
        .snoc (.snoc (.snoc (.snoc (.snoc .nil rawC) rawC) tyC) (.pi tyC U0)) (.pi tyC U0)
      show Typed (typingStage lv) Γ
        (.sigma (isNumC (.var 2)) (.sigma (.app (.var 2) tnumC) (.app (.var 2) tnumC))) U0
      have tNum : Typed (typingStage lv) Γ (isNumC (.var 2)) U0 := typing_isNum_typed lv (.var 2)
      have ha : Typed (typingStage lv) (.snoc Γ (isNumC (.var 2))) (.app (.var 2) tnumC) U0 :=
        .appElim (A := tyC) (B := U0) (.var 2) (typing_tnum_typed lv)
      have hb : Typed (typingStage lv) (.snoc (.snoc Γ (isNumC (.var 2))) (.app (.var 2) tnumC))
          (.app (.var 2) tnumC) U0 :=
        .appElim (A := tyC) (B := U0) (.var 2) (typing_tnum_typed lv)
      exact tw.sigma_small tNum (tw.sigma_small ha hb)
    · let Γ : Ctx Tower.Head 7 :=
        .snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil rawC) rawC) rawC) tyC) (.pi tyC U0))
          (.pi tyC U0)) (.pi tyC U0)
      show Typed (typingStage lv) Γ
        (.sigma (.app (.var 2) tboolC) (.sigma (.app (.var 2) (.var 4)) (.app (.var 2) (.var 5)))) U0
      have hc : Typed (typingStage lv) Γ (.app (.var 2) tboolC) U0 :=
        .appElim (A := tyC) (B := U0) (.var 2) (typing_tbool_typed lv)
      have ha : Typed (typingStage lv) (.snoc Γ (.app (.var 2) tboolC)) (.app (.var 2) (.var 4)) U0 :=
        .appElim (A := tyC) (B := U0) (.var 2) (.var 4)
      have hb : Typed (typingStage lv) (.snoc (.snoc Γ (.app (.var 2) tboolC)) (.app (.var 2) (.var 4)))
          (.app (.var 2) (.var 5)) U0 :=
        .appElim (A := tyC) (B := U0) (.var 2) (.var 5)
      exact tw.sigma_small hc (tw.sigma_small ha hb)
    · let Γ : Ctx Tower.Head 3 := .snoc (.snoc (.snoc .nil rawC) tyC) (.pi tyC U0)
      show Typed (typingStage lv) Γ (.sigma (isBoolC (.var 1)) (.app (.var 1) tnumC)) U0
      have tBool : Typed (typingStage lv) Γ (isBoolC (.var 1)) U0 := typing_isBool_typed lv (.var 1)
      have ha : Typed (typingStage lv) (.snoc Γ (isBoolC (.var 1))) (.app (.var 1) tnumC) U0 :=
        .appElim (A := tyC) (B := U0) (.var 1) (typing_tnum_typed lv)
      exact tw.sigma_small tBool ha
  rule := by
    intro k fields mem m σ as has
    exact RootComputation.step_unionAll mem_typing ⟨_, _, σ, as, mem, has, rfl, rfl⟩

end Declarations

end TowerSyntaxModel

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
