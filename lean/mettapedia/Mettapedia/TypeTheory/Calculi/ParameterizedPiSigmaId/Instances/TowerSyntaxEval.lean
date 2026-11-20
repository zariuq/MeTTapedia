import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerSyntaxRecursion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Completeness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.NeutralHeads

/-!
# Typed expressions and their interpreter in the normalization model

The family `exp t = Σ (r : raw). typed r t` of the package `TowerSyntaxModel.rules lv`, with the
constructors

* `lit k = (rnum k, tt) : exp tnum` and `add x y = (radd x.1 y.1, (tt, (x.2, y.2))) : exp tnum`,
  **two constructors at one index**;
* `blit b = (rbool b, tt) : exp tbool` and `iszero x = (riszero x.1, (tt, x.2)) : exp tbool`;
* `ite x y z = (rif x.1 y.1 z.1, (x.2, (y.2, z.2))) : exp t`, at every index, a variable included;

its recursion principle `rec Q m t e = syntax-rec Q m e.1 t e.2 : Q t`, with a computation rule on
every constructor **on open arguments** (`expRec_lit`, `expRec_blit`, `expRec_add`, `expRec_ite`,
`expRec_iszero`), and the interpreter `eval = rec val (λ k. k) (λ b. b) add if is-zero : exp t → val t`.
`eval (add (lit 2) (lit 3))` is `5` by conversion (`eval_two_plus_three`).

**What is not obtained** (controls), against a true inductive family:

* proofs of typing are not definitionally unique: two elements with the same untyped expression and
  different proof variables are not equal (`same_raw_not_equal`); there is no η for the unit type;
* at a variable index an untyped constructor with a neutral proof is an element
  (`junk_typed`), on which the recursion unfolds once and stops (`unfolds_at_variable_index`);
* the type former separates the closed indices (`exp_tnum_ne_tbool`), but over a variable index `exp t`
  is a pair type, not a stuck family: every element has its untyped expression `e.1`.

What is obtained: the family is not degenerate (`lit_two_ne_three`, `lit_ne_add`), an ill-indexed
literal is rejected (`lit_not_bool`), the recursion is stuck on a variable expression
(`expRec_stuck_variable`), and the typing relation is not constantly the unit type
(`typing_rbool_tnum`, `void_ne_unit`).
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

/-! ## The family's constructors, the recursion principle and the interpreter, as terms -/

/-- `lit k : exp tnum`. -/
abbrev litE {n : Nat} (k : Tm Tower.Head n) : Tm Tower.Head n := .pair (rnumC k) ttC
/-- `blit b : exp tbool`. -/
abbrev blitE {n : Nat} (b : Tm Tower.Head n) : Tm Tower.Head n := .pair (rboolC b) ttC
/-- `add x y : exp tnum`. -/
abbrev addE {n : Nat} (x y : Tm Tower.Head n) : Tm Tower.Head n :=
  .pair (raddC (.fst x) (.fst y)) (.pair ttC (.pair (.snd x) (.snd y)))
/-- `ite x y z : exp t`. -/
abbrev iteE {n : Nat} (x y z : Tm Tower.Head n) : Tm Tower.Head n :=
  .pair (rifC (.fst x) (.fst y) (.fst z)) (.pair (.snd x) (.pair (.snd y) (.snd z)))
/-- `iszero x : exp tbool`. -/
abbrev iszeroE {n : Nat} (x : Tm Tower.Head n) : Tm Tower.Head n := .pair (rzeroC (.fst x)) (.pair ttC (.snd x))

/-- **The recursion principle of typed expressions**: `rec Q m t e = syntax-rec Q m e.1 t e.2`. -/
abbrev expRecC {n : Nat} (Q m₁ m₂ m₃ m₄ m₅ t e : Tm Tower.Head n) : Tm Tower.Head n :=
  synRecC Q m₁ m₂ m₃ m₄ m₅ (.fst e) t (.snd e)

/-- The interpreter's methods: numerals and Booleans are their own values, addition is `add`, the
conditional is the Booleans' recursor at the motive `λ _. val t`, the zero test is `is-zero`. -/
abbrev evalNum {n : Nat} : Tm Tower.Head n := .lam (.var 0)
abbrev evalBool {n : Nat} : Tm Tower.Head n := .lam (.var 0)
abbrev evalAdd {n : Nat} : Tm Tower.Head n := .const add
abbrev evalIf {n : Nat} : Tm Tower.Head n :=
  .lam (.lam (.lam (.lam (boolRecC (.lam (valC (.var 4))) (.var 1) (.var 0) (.var 2)))))
abbrev evalZero {n : Nat} : Tm Tower.Head n := .const isZero
abbrev valFam {n : Nat} : Tm Tower.Head n := .const val

/-- **The interpreter**: `eval t e = rec val (λ k. k) (λ b. b) add if is-zero t e`. -/
abbrev evalC {n : Nat} (t e : Tm Tower.Head n) : Tm Tower.Head n :=
  expRecC valFam evalNum evalBool evalAdd evalIf evalZero t e

/-- Numerals. -/
def numeral {n : Nat} : Nat → Tm Tower.Head n
  | 0 => zeroC
  | k + 1 => succC (numeral k)

variable (lv : LevelExpr Nat)

/-! ## The equations as steps -/

theorem atNum_tnum_step {n : Nat} (Q x p : Tm Tower.Head n) :
    (rules lv).computation.step (atNumC Q x tnumC p) x :=
  RootComputation.step_unionAll mem_atNum
    ⟨tnum, [], consSub p (consSub tnumC (consSub x (consSub Q fun i => Fin.elim0 i))), [], mem_tnum, rfl, rfl,
      rfl⟩

theorem atBool_tbool_step {n : Nat} (Q x p : Tm Tower.Head n) :
    (rules lv).computation.step (atBoolC Q x tboolC p) x :=
  RootComputation.step_unionAll mem_atBool
    ⟨tbool, [], consSub p (consSub tboolC (consSub x (consSub Q fun i => Fin.elim0 i))), [], mem_tbool, rfl,
      rfl, rfl⟩

theorem synRec_rnum_step {n : Nat} (Q m₁ m₂ m₃ m₄ m₅ k t p : Tm Tower.Head n) :
    (rules lv).computation.step (synRecC Q m₁ m₂ m₃ m₄ m₅ (rnumC k) t p) (atNumC Q (.app m₁ k) t p) :=
  RootComputation.step_unionAll mem_synRec
    ⟨rnum, [.closed numT], consSub p (consSub t (consSub (rnumC k) (consSub m₅ (consSub m₄ (consSub m₃
      (consSub m₂ (consSub m₁ (consSub Q fun i => Fin.elim0 i)))))))), [k], mem_rnum, rfl, rfl, rfl⟩

theorem synRec_rbool_step {n : Nat} (Q m₁ m₂ m₃ m₄ m₅ b t p : Tm Tower.Head n) :
    (rules lv).computation.step (synRecC Q m₁ m₂ m₃ m₄ m₅ (rboolC b) t p) (atBoolC Q (.app m₂ b) t p) :=
  RootComputation.step_unionAll mem_synRec
    ⟨rbool, [.closed boolT], consSub p (consSub t (consSub (rboolC b) (consSub m₅ (consSub m₄ (consSub m₃
      (consSub m₂ (consSub m₁ (consSub Q fun i => Fin.elim0 i)))))))), [b], mem_rbool, rfl, rfl, rfl⟩

theorem synRec_radd_step {n : Nat} (Q m₁ m₂ m₃ m₄ m₅ a b t p : Tm Tower.Head n) :
    (rules lv).computation.step (synRecC Q m₁ m₂ m₃ m₄ m₅ (raddC a b) t p)
      (atNumC Q (.app (.app m₃ (synRecC Q m₁ m₂ m₃ m₄ m₅ a tnumC (.fst (.snd p))))
        (synRecC Q m₁ m₂ m₃ m₄ m₅ b tnumC (.snd (.snd p)))) t (.fst p)) :=
  RootComputation.step_unionAll mem_synRec
    ⟨radd, [.recursive, .recursive], consSub p (consSub t (consSub (raddC a b) (consSub m₅ (consSub m₄
      (consSub m₃ (consSub m₂ (consSub m₁ (consSub Q fun i => Fin.elim0 i)))))))), [a, b], mem_radd, rfl,
      rfl, rfl⟩

theorem synRec_rif_step {n : Nat} (Q m₁ m₂ m₃ m₄ m₅ c a b t p : Tm Tower.Head n) :
    (rules lv).computation.step (synRecC Q m₁ m₂ m₃ m₄ m₅ (rifC c a b) t p)
      (.app (.app (.app (.app m₄ t) (synRecC Q m₁ m₂ m₃ m₄ m₅ c tboolC (.fst p)))
        (synRecC Q m₁ m₂ m₃ m₄ m₅ a t (.fst (.snd p)))) (synRecC Q m₁ m₂ m₃ m₄ m₅ b t (.snd (.snd p)))) :=
  RootComputation.step_unionAll mem_synRec
    ⟨rif, [.recursive, .recursive, .recursive], consSub p (consSub t (consSub (rifC c a b) (consSub m₅
      (consSub m₄ (consSub m₃ (consSub m₂ (consSub m₁ (consSub Q fun i => Fin.elim0 i)))))))), [c, a, b],
      mem_rif, rfl, rfl, rfl⟩

theorem synRec_rzero_step {n : Nat} (Q m₁ m₂ m₃ m₄ m₅ a t p : Tm Tower.Head n) :
    (rules lv).computation.step (synRecC Q m₁ m₂ m₃ m₄ m₅ (rzeroC a) t p)
      (atBoolC Q (.app m₅ (synRecC Q m₁ m₂ m₃ m₄ m₅ a tnumC (.snd p))) t (.fst p)) :=
  RootComputation.step_unionAll mem_synRec
    ⟨rzero, [.recursive], consSub p (consSub t (consSub (rzeroC a) (consSub m₅ (consSub m₄ (consSub m₃
      (consSub m₂ (consSub m₁ (consSub Q fun i => Fin.elim0 i)))))))), [a], mem_rzero, rfl, rfl, rfl⟩

theorem add_zero_step {n : Nat} (m : Tm Tower.Head n) : (rules lv).computation.step (addC zeroC m) m :=
  RootComputation.step_unionAll mem_add
    ⟨zero, [], consSub m (consSub zeroC fun i => Fin.elim0 i), [], mem_zero, rfl, rfl, rfl⟩

theorem add_succ_step {n : Nat} (k m : Tm Tower.Head n) :
    (rules lv).computation.step (addC (succC k) m) (succC (addC k m)) :=
  RootComputation.step_unionAll mem_add
    ⟨succ, [.recursive], consSub m (consSub (succC k) fun i => Fin.elim0 i), [k], mem_succ, rfl, rfl, rfl⟩

/-! ## Reductions in contexts -/

theorem red_appFun {n : Nat} {g g' a : Tm Tower.Head n} (h : Reduces (rules lv) g g') :
    Reduces (rules lv) (.app g a) (.app g' a) :=
  Relation.ReflTransGen.lift (fun g => Tm.app g a) (fun _ _ s => StepCore.congAppFun s) _ _ h

theorem red_appArg {n : Nat} {g a a' : Tm Tower.Head n} (h : Reduces (rules lv) a a') :
    Reduces (rules lv) (.app g a) (.app g a') :=
  Relation.ReflTransGen.lift (fun a => Tm.app g a) (fun _ _ s => StepCore.congAppArg s) _ _ h

/-- The empty substitution into any context. -/
theorem subst_nil {n : Nat} {Γ : Ctx Tower.Head n} :
    SubstMor (rules lv) .nil Γ (fun i => Fin.elim0 i) := fun i => Fin.elim0 i

/-! ## The computation rules, as reductions on open terms -/

section Reductions

variable {n : Nat} (Q m₁ m₂ m₃ m₄ m₅ : Tm Tower.Head n)

theorem expRec_lit_red (k : Tm Tower.Head n) :
    Reduces (rules lv) (expRecC Q m₁ m₂ m₃ m₄ m₅ tnumC (litE k)) (.app m₁ k) :=
  .tail (.tail (.tail (.single
    (.congAppFun (.congAppFun (.congAppArg (.betaSigmaFst (rnumC k) ttC)))))
    (.congAppArg (.betaSigmaSnd (rnumC k) ttC)))
    (.root (synRec_rnum_step lv Q m₁ m₂ m₃ m₄ m₅ k tnumC ttC)))
    (.root (atNum_tnum_step lv Q (.app m₁ k) ttC))

theorem expRec_blit_red (b : Tm Tower.Head n) :
    Reduces (rules lv) (expRecC Q m₁ m₂ m₃ m₄ m₅ tboolC (blitE b)) (.app m₂ b) :=
  .tail (.tail (.tail (.single
    (.congAppFun (.congAppFun (.congAppArg (.betaSigmaFst (rboolC b) ttC)))))
    (.congAppArg (.betaSigmaSnd (rboolC b) ttC)))
    (.root (synRec_rbool_step lv Q m₁ m₂ m₃ m₄ m₅ b tboolC ttC)))
    (.root (atBool_tbool_step lv Q (.app m₂ b) ttC))

theorem expRec_add_red (x y : Tm Tower.Head n) :
    Reduces (rules lv) (expRecC Q m₁ m₂ m₃ m₄ m₅ tnumC (addE x y))
      (.app (.app m₃ (expRecC Q m₁ m₂ m₃ m₄ m₅ tnumC x)) (expRecC Q m₁ m₂ m₃ m₄ m₅ tnumC y)) :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.single
    (.congAppFun (.congAppFun (.congAppArg
      (.betaSigmaFst (raddC (.fst x) (.fst y)) (.pair ttC (.pair (.snd x) (.snd y))))))))
    (.congAppArg (.betaSigmaSnd (raddC (.fst x) (.fst y)) (.pair ttC (.pair (.snd x) (.snd y))))))
    (.root (synRec_radd_step lv Q m₁ m₂ m₃ m₄ m₅ (.fst x) (.fst y) tnumC (.pair ttC (.pair (.snd x) (.snd y))))))
    (.root (atNum_tnum_step lv Q _ _)))
    (.congAppFun (.congAppArg (.congAppArg (.congFst (.betaSigmaSnd ttC (.pair (.snd x) (.snd y))))))))
    (.congAppFun (.congAppArg (.congAppArg (.betaSigmaFst (.snd x) (.snd y))))))
    (.congAppArg (.congAppArg (.congSnd (.betaSigmaSnd ttC (.pair (.snd x) (.snd y)))))))
    (.congAppArg (.congAppArg (.betaSigmaSnd (.snd x) (.snd y))))

theorem expRec_ite_red (t x y z : Tm Tower.Head n) :
    Reduces (rules lv) (expRecC Q m₁ m₂ m₃ m₄ m₅ t (iteE x y z))
      (.app (.app (.app (.app m₄ t) (expRecC Q m₁ m₂ m₃ m₄ m₅ tboolC x)) (expRecC Q m₁ m₂ m₃ m₄ m₅ t y))
        (expRecC Q m₁ m₂ m₃ m₄ m₅ t z)) :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.single
    (.congAppFun (.congAppFun (.congAppArg
      (.betaSigmaFst (rifC (.fst x) (.fst y) (.fst z)) (.pair (.snd x) (.pair (.snd y) (.snd z))))))))
    (.congAppArg (.betaSigmaSnd (rifC (.fst x) (.fst y) (.fst z)) (.pair (.snd x) (.pair (.snd y) (.snd z))))))
    (.root (synRec_rif_step lv Q m₁ m₂ m₃ m₄ m₅ (.fst x) (.fst y) (.fst z) t
      (.pair (.snd x) (.pair (.snd y) (.snd z))))))
    (.congAppFun (.congAppFun (.congAppArg (.congAppArg
      (.betaSigmaFst (.snd x) (.pair (.snd y) (.snd z))))))))
    (.congAppFun (.congAppArg (.congAppArg (.congFst (.betaSigmaSnd (.snd x) (.pair (.snd y) (.snd z))))))))
    (.congAppFun (.congAppArg (.congAppArg (.betaSigmaFst (.snd y) (.snd z))))))
    (.congAppArg (.congAppArg (.congSnd (.betaSigmaSnd (.snd x) (.pair (.snd y) (.snd z)))))))
    (.congAppArg (.congAppArg (.betaSigmaSnd (.snd y) (.snd z))))

theorem expRec_iszero_red (x : Tm Tower.Head n) :
    Reduces (rules lv) (expRecC Q m₁ m₂ m₃ m₄ m₅ tboolC (iszeroE x))
      (.app m₅ (expRecC Q m₁ m₂ m₃ m₄ m₅ tnumC x)) :=
  .tail (.tail (.tail (.tail (.single
    (.congAppFun (.congAppFun (.congAppArg (.betaSigmaFst (rzeroC (.fst x)) (.pair ttC (.snd x)))))))
    (.congAppArg (.betaSigmaSnd (rzeroC (.fst x)) (.pair ttC (.snd x)))))
    (.root (synRec_rzero_step lv Q m₁ m₂ m₃ m₄ m₅ (.fst x) tboolC (.pair ttC (.snd x)))))
    (.root (atBool_tbool_step lv Q _ _)))
    (.congAppArg (.congAppArg (.betaSigmaSnd ttC (.snd x))))

end Reductions

/-! ## Typings in the package -/

section Typing

variable {n : Nat} {Γ : Ctx Tower.Head n}

theorem tw_rules : TowerLike (rules lv) := towerLike_rules lv

theorem ty_typed : Typed (rules lv) Γ tyC U0 := (tw_rules lv).small (c := ty) rfl
theorem raw_typed : Typed (rules lv) Γ rawC U0 := (tw_rules lv).small (c := raw) rfl
theorem num_typed : Typed (rules lv) Γ numC U0 := (tw_rules lv).small (c := num) rfl
theorem bool_typed : Typed (rules lv) Γ boolC U0 := (tw_rules lv).small (c := bool) rfl
theorem unit_typed : Typed (rules lv) Γ unitC U0 := (tw_rules lv).small (c := unit) rfl
theorem void_typed : Typed (rules lv) Γ voidC U0 := (tw_rules lv).small (c := void) rfl

theorem tnum_typed : Typed (rules lv) Γ tnumC tyC :=
  .const (type := ctorType ty []) rfl (ty_typed lv) (LevelTower.IsUniverse.sort _)
theorem tbool_typed : Typed (rules lv) Γ tboolC tyC :=
  .const (type := ctorType ty []) rfl (ty_typed lv) (LevelTower.IsUniverse.sort _)
theorem tt_typed : Typed (rules lv) Γ ttC unitC :=
  .const (type := ctorType unit []) rfl (unit_typed lv) (LevelTower.IsUniverse.sort _)
theorem zero_typed : Typed (rules lv) Γ zeroC numC :=
  .const (type := ctorType num []) rfl (num_typed lv) (LevelTower.IsUniverse.sort _)
theorem btrue_typed : Typed (rules lv) Γ btrueC boolC :=
  .const (type := ctorType bool []) rfl (bool_typed lv) (LevelTower.IsUniverse.sort _)
theorem bfalse_typed : Typed (rules lv) Γ bfalseC boolC :=
  .const (type := ctorType bool []) rfl (bool_typed lv) (LevelTower.IsUniverse.sort _)

theorem succ_typed {k : Tm Tower.Head n} (tk : Typed (rules lv) Γ k numC) : Typed (rules lv) Γ (succC k) numC :=
  .appElim (A := numC) (B := numC) (.const (type := ctorType num [.recursive]) rfl
    ((tw_rules lv).pi_small (num_typed lv) (num_typed lv)) (LevelTower.IsUniverse.sort _)) tk

theorem numeral_typed : ∀ k : Nat, Typed (rules lv) Γ (numeral k) numC
  | 0 => zero_typed lv
  | k + 1 => succ_typed lv (numeral_typed k)

theorem tyFam_typed {f : DeclName} (declared : (rules lv).constantType f = some tyFamType) :
    Typed (rules lv) Γ (.const f) (.pi tyC U0) :=
  .const declared (tyFamily_typed (tw_rules lv) rfl) (LevelTower.IsUniverse.sort _)

theorem typing_typed {r t : Tm Tower.Head n} (tr : Typed (rules lv) Γ r rawC) (tt' : Typed (rules lv) Γ t tyC) :
    Typed (rules lv) Γ (typingC r t) U0 :=
  .appElim (A := tyC) (B := U0) (.appElim (A := rawC) (B := .pi tyC U0)
    (.const (type := typingType) rfl
      (.piForm (raw_typed lv) (LevelTower.IsUniverse.sort _) (tyFamily_typed (tw_rules lv) rfl)
        (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)) (LevelTower.IsUniverse.sort _)) tr) tt'

theorem isNum_typed {t : Tm Tower.Head n} (tt' : Typed (rules lv) Γ t tyC) : Typed (rules lv) Γ (isNumC t) U0 :=
  .appElim (A := tyC) (B := U0) (tyFam_typed lv rfl) tt'
theorem isBool_typed {t : Tm Tower.Head n} (tt' : Typed (rules lv) Γ t tyC) :
    Typed (rules lv) Γ (isBoolC t) U0 :=
  .appElim (A := tyC) (B := U0) (tyFam_typed lv rfl) tt'
theorem val_typed {t : Tm Tower.Head n} (tt' : Typed (rules lv) Γ t tyC) : Typed (rules lv) Γ (valC t) U0 :=
  .appElim (A := tyC) (B := U0) (tyFam_typed lv rfl) tt'

/-- The package declares the untyped expressions with their constructors. -/
theorem rawD : RawDeclared (rules lv) := ⟨tw_rules lv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Formation**: `exp t` is a small type at every object type `t`. -/
theorem exp_typed {t : Tm Tower.Head n} (tt' : Typed (rules lv) Γ t tyC) : Typed (rules lv) Γ (expC t) U0 := by
  have tr : Typed (rules lv) (.snoc Γ rawC) (.var 0) rawC := .var 0
  exact (tw_rules lv).sigma_small (raw_typed lv) (typing_typed lv tr tt'.weaken)

theorem isNum_tnum_eq : Equal (rules lv) Γ (isNumC tnumC) unitC U0 :=
  .root (isNum_tnum_step lv) (isNum_typed lv (tnum_typed lv)) (unit_typed lv)
theorem isNum_tbool_eq : Equal (rules lv) Γ (isNumC tboolC) voidC U0 :=
  .root (isNum_tbool_step lv) (isNum_typed lv (tbool_typed lv)) (void_typed lv)
theorem isBool_tbool_eq : Equal (rules lv) Γ (isBoolC tboolC) unitC U0 :=
  .root (isBool_tbool_step lv) (isBool_typed lv (tbool_typed lv)) (unit_typed lv)
theorem val_tnum_eq : Equal (rules lv) Γ (valC tnumC) numC U0 :=
  .root (val_tnum_step lv) (val_typed lv (tnum_typed lv)) (num_typed lv)
theorem val_tbool_eq : Equal (rules lv) Γ (valC tboolC) boolC U0 :=
  .root (val_tbool_step lv) (val_typed lv (tbool_typed lv)) (bool_typed lv)

/-- `tt` proves that a numeral literal is typed at `tnum`: `typed (rnum k) tnum ≡ unit`. -/
theorem typing_rnum_tnum {k : Tm Tower.Head n} (tk : Typed (rules lv) Γ k numC) :
    Equal (rules lv) Γ (typingC (rnumC k) tnumC) unitC U0 :=
  .trans (.root (typing_rnum_step lv k tnumC) (typing_typed lv ((rawD lv).rnum_app tk) (tnum_typed lv))
    (isNum_typed lv (tnum_typed lv))) (isNum_tnum_eq lv)

theorem typing_rbool_tbool {b : Tm Tower.Head n} (tb : Typed (rules lv) Γ b boolC) :
    Equal (rules lv) Γ (typingC (rboolC b) tboolC) unitC U0 :=
  .trans (.root (typing_rbool_step lv b tboolC) (typing_typed lv ((rawD lv).rbool_app tb) (tbool_typed lv))
    (isBool_typed lv (tbool_typed lv))) (isBool_tbool_eq lv)

/-- **The typing relation is not constantly the unit type**: a Boolean literal at `tnum` computes to the
empty type. -/
theorem typing_rbool_tnum {b : Tm Tower.Head n} (tb : Typed (rules lv) Γ b boolC) :
    Equal (rules lv) Γ (typingC (rboolC b) tnumC) voidC U0 :=
  .trans (.root (typing_rbool_step lv b tnumC) (typing_typed lv ((rawD lv).rbool_app tb) (tnum_typed lv))
    (isBool_typed lv (tnum_typed lv)))
    (.root (isBool_tnum_step lv) (isBool_typed lv (tnum_typed lv)) (void_typed lv))

/-! ### The constructors -/

/-- **`lit k : exp tnum`.** -/
theorem lit_typed {k : Tm Tower.Head n} (tk : Typed (rules lv) Γ k numC) :
    Typed (rules lv) Γ (litE k) (expC tnumC) :=
  .pairIntro (exp_typed lv (tnum_typed lv)) (LevelTower.IsUniverse.sort _) ((rawD lv).rnum_app tk)
    (Typed.convType (tt_typed lv) ⟨_, LevelTower.IsUniverse.sort _, (typing_rnum_tnum lv tk).symm⟩)

/-- **`blit b : exp tbool`.** -/
theorem blit_typed {b : Tm Tower.Head n} (tb : Typed (rules lv) Γ b boolC) :
    Typed (rules lv) Γ (blitE b) (expC tboolC) :=
  .pairIntro (exp_typed lv (tbool_typed lv)) (LevelTower.IsUniverse.sort _) ((rawD lv).rbool_app tb)
    (Typed.convType (tt_typed lv) ⟨_, LevelTower.IsUniverse.sort _, (typing_rbool_tbool lv tb).symm⟩)

end Typing

/-- The context of two expressions of the number type. -/
abbrev addVars : Ctx Tower.Head 2 := .snoc (.snoc .nil (expC tnumC)) (expC tnumC)

/-- `add x y : exp tnum`, for the variables `x y : exp tnum`. -/
theorem add_typed_vars : Typed (rules lv) addVars (addE (.var 1) (.var 0)) (expC tnumC) := by
  have tw := tw_rules lv
  have tx : Typed (rules lv) addVars (.var 1) (expC tnumC) := .var 1
  have ty' : Typed (rules lv) addVars (.var 0) (expC tnumC) := .var 0
  have ax : Typed (rules lv) addVars (.fst (.var 1)) rawC := .fstElim tx
  have ay : Typed (rules lv) addVars (.fst (.var 0)) rawC := .fstElim ty'
  have px : Typed (rules lv) addVars (.snd (.var 1)) (typingC (.fst (.var 1)) tnumC) := .sndElim tx
  have py : Typed (rules lv) addVars (.snd (.var 0)) (typingC (.fst (.var 0)) tnumC) := .sndElim ty'
  have ar : Typed (rules lv) addVars (raddC (.fst (.var 1)) (.fst (.var 0))) rawC := (rawD lv).radd_app ax ay
  -- the proof's type, computed
  have ax₁ : Typed (rules lv) (.snoc addVars (isNumC tnumC)) (.fst (.var 2)) rawC := .fstElim (.var 2)
  have ay₂ : Typed (rules lv) (.snoc (.snoc addVars (isNumC tnumC)) (typingC (.fst (.var 2)) tnumC))
      (.fst (.var 2)) rawC := .fstElim (.var 2)
  have tInner : Typed (rules lv) (.snoc addVars (isNumC tnumC))
      (.sigma (typingC (.fst (.var 2)) tnumC) (typingC (.fst (.var 2)) tnumC)) U0 :=
    tw.sigma_small (typing_typed lv ax₁ (tnum_typed lv)) (typing_typed lv ay₂ (tnum_typed lv))
  have tSigma : Typed (rules lv) addVars
      (.sigma (isNumC tnumC) (.sigma (typingC (.fst (.var 2)) tnumC) (typingC (.fst (.var 2)) tnumC))) U0 :=
    tw.sigma_small (isNum_typed lv (tnum_typed lv)) tInner
  have eq : Equal (rules lv) addVars (typingC (raddC (.fst (.var 1)) (.fst (.var 0))) tnumC)
      (.sigma (isNumC tnumC) (.sigma (typingC (.fst (.var 2)) tnumC) (typingC (.fst (.var 2)) tnumC))) U0 :=
    .root (typing_radd_step lv (.fst (.var 1)) (.fst (.var 0)) tnumC) (typing_typed lv ar (tnum_typed lv)) tSigma
  have tSigmaInner : Typed (rules lv) addVars (.sigma (typingC (.fst (.var 1)) tnumC) (typingC (.fst (.var 1)) tnumC))
      U0 := by
    have ay₁ : Typed (rules lv) (.snoc addVars (typingC (.fst (.var 1)) tnumC)) (.fst (.var 1)) rawC :=
      .fstElim (.var 1)
    exact tw.sigma_small (typing_typed lv ax (tnum_typed lv)) (typing_typed lv ay₁ (tnum_typed lv))
  have tPair : Typed (rules lv) addVars (.pair (.snd (.var 1)) (.snd (.var 0)))
      (.sigma (typingC (.fst (.var 1)) tnumC) (typingC (.fst (.var 1)) tnumC)) :=
    .pairIntro tSigmaInner (LevelTower.IsUniverse.sort _) px py
  have tProof : Typed (rules lv) addVars (.pair ttC (.pair (.snd (.var 1)) (.snd (.var 0))))
      (.sigma (isNumC tnumC) (.sigma (typingC (.fst (.var 2)) tnumC) (typingC (.fst (.var 2)) tnumC))) :=
    .pairIntro tSigma (LevelTower.IsUniverse.sort _)
      (Typed.convType (tt_typed lv) ⟨_, LevelTower.IsUniverse.sort _, (isNum_tnum_eq lv).symm⟩) tPair
  exact .pairIntro (exp_typed lv (tnum_typed lv)) (LevelTower.IsUniverse.sort _) ar
    (Typed.convType tProof ⟨_, LevelTower.IsUniverse.sort _, eq.symm⟩)

/-- The context of an index and three expressions: `t`, `x : exp tbool`, `y z : exp t`. -/
abbrev iteVars : Ctx Tower.Head 4 := .snoc (.snoc (.snoc (.snoc .nil tyC) (expC tboolC)) (expC (.var 1))) (expC (.var 2))

/-- `ite x y z : exp t`, for variables, at a variable index. -/
theorem ite_typed_vars : Typed (rules lv) iteVars (iteE (.var 2) (.var 1) (.var 0)) (expC (.var 3)) := by
  have tw := tw_rules lv
  have tt' : Typed (rules lv) iteVars (.var 3) tyC := .var 3
  have tx : Typed (rules lv) iteVars (.var 2) (expC tboolC) := .var 2
  have ty' : Typed (rules lv) iteVars (.var 1) (expC (.var 3)) := .var 1
  have tz : Typed (rules lv) iteVars (.var 0) (expC (.var 3)) := .var 0
  have ax : Typed (rules lv) iteVars (.fst (.var 2)) rawC := .fstElim tx
  have ay : Typed (rules lv) iteVars (.fst (.var 1)) rawC := .fstElim ty'
  have az : Typed (rules lv) iteVars (.fst (.var 0)) rawC := .fstElim tz
  have px : Typed (rules lv) iteVars (.snd (.var 2)) (typingC (.fst (.var 2)) tboolC) := .sndElim tx
  have py : Typed (rules lv) iteVars (.snd (.var 1)) (typingC (.fst (.var 1)) (.var 3)) := .sndElim ty'
  have pz : Typed (rules lv) iteVars (.snd (.var 0)) (typingC (.fst (.var 0)) (.var 3)) := .sndElim tz
  have ar : Typed (rules lv) iteVars (rifC (.fst (.var 2)) (.fst (.var 1)) (.fst (.var 0))) rawC :=
    (rawD lv).rif_app ax ay az
  have ay₁ : Typed (rules lv) (.snoc iteVars (typingC (.fst (.var 2)) tboolC)) (.fst (.var 2)) rawC :=
    .fstElim (.var 2)
  have tt₁ : Typed (rules lv) (.snoc iteVars (typingC (.fst (.var 2)) tboolC)) (.var 4) tyC := .var 4
  have az₂ : Typed (rules lv) (.snoc (.snoc iteVars (typingC (.fst (.var 2)) tboolC))
      (typingC (.fst (.var 2)) (.var 4))) (.fst (.var 2)) rawC := .fstElim (.var 2)
  have tt₂ : Typed (rules lv) (.snoc (.snoc iteVars (typingC (.fst (.var 2)) tboolC))
      (typingC (.fst (.var 2)) (.var 4))) (.var 5) tyC := .var 5
  have tSigma : Typed (rules lv) iteVars
      (.sigma (typingC (.fst (.var 2)) tboolC)
        (.sigma (typingC (.fst (.var 2)) (.var 4)) (typingC (.fst (.var 2)) (.var 5)))) U0 :=
    tw.sigma_small (typing_typed lv ax (tbool_typed lv))
      (tw.sigma_small (typing_typed lv ay₁ tt₁) (typing_typed lv az₂ tt₂))
  have eq : Equal (rules lv) iteVars (typingC (rifC (.fst (.var 2)) (.fst (.var 1)) (.fst (.var 0))) (.var 3))
      (.sigma (typingC (.fst (.var 2)) tboolC)
        (.sigma (typingC (.fst (.var 2)) (.var 4)) (typingC (.fst (.var 2)) (.var 5)))) U0 :=
    .root (typing_rif_step lv (.fst (.var 2)) (.fst (.var 1)) (.fst (.var 0)) (.var 3))
      (typing_typed lv ar tt') tSigma
  have az₁ : Typed (rules lv) (.snoc iteVars (typingC (.fst (.var 1)) (.var 3))) (.fst (.var 1)) rawC :=
    .fstElim (.var 1)
  have tt₁' : Typed (rules lv) (.snoc iteVars (typingC (.fst (.var 1)) (.var 3))) (.var 4) tyC := .var 4
  have tInner : Typed (rules lv) iteVars
      (.sigma (typingC (.fst (.var 1)) (.var 3)) (typingC (.fst (.var 1)) (.var 4))) U0 :=
    tw.sigma_small (typing_typed lv ay tt') (typing_typed lv az₁ tt₁')
  have tPair : Typed (rules lv) iteVars (.pair (.snd (.var 1)) (.snd (.var 0)))
      (.sigma (typingC (.fst (.var 1)) (.var 3)) (typingC (.fst (.var 1)) (.var 4))) :=
    .pairIntro tInner (LevelTower.IsUniverse.sort _) py pz
  have tProof : Typed (rules lv) iteVars (.pair (.snd (.var 2)) (.pair (.snd (.var 1)) (.snd (.var 0))))
      (.sigma (typingC (.fst (.var 2)) tboolC)
        (.sigma (typingC (.fst (.var 2)) (.var 4)) (typingC (.fst (.var 2)) (.var 5)))) :=
    .pairIntro tSigma (LevelTower.IsUniverse.sort _) px tPair
  exact .pairIntro (exp_typed lv tt') (LevelTower.IsUniverse.sort _) ar
    (Typed.convType tProof ⟨_, LevelTower.IsUniverse.sort _, eq.symm⟩)

/-- The context of one expression of the number type. -/
abbrev zeroVars : Ctx Tower.Head 1 := .snoc .nil (expC tnumC)

/-- `iszero x : exp tbool`, for a variable `x : exp tnum`. -/
theorem iszero_typed_vars : Typed (rules lv) zeroVars (iszeroE (.var 0)) (expC tboolC) := by
  have tw := tw_rules lv
  have tx : Typed (rules lv) zeroVars (.var 0) (expC tnumC) := .var 0
  have ax : Typed (rules lv) zeroVars (.fst (.var 0)) rawC := .fstElim tx
  have px : Typed (rules lv) zeroVars (.snd (.var 0)) (typingC (.fst (.var 0)) tnumC) := .sndElim tx
  have ar : Typed (rules lv) zeroVars (rzeroC (.fst (.var 0))) rawC := (rawD lv).rzero_app ax
  have ax₁ : Typed (rules lv) (.snoc zeroVars (isBoolC tboolC)) (.fst (.var 1)) rawC := .fstElim (.var 1)
  have tSigma : Typed (rules lv) zeroVars (.sigma (isBoolC tboolC) (typingC (.fst (.var 1)) tnumC)) U0 :=
    tw.sigma_small (isBool_typed lv (tbool_typed lv)) (typing_typed lv ax₁ (tnum_typed lv))
  have eq : Equal (rules lv) zeroVars (typingC (rzeroC (.fst (.var 0))) tboolC)
      (.sigma (isBoolC tboolC) (typingC (.fst (.var 1)) tnumC)) U0 :=
    .root (typing_rzero_step lv (.fst (.var 0)) tboolC) (typing_typed lv ar (tbool_typed lv)) tSigma
  have tProof : Typed (rules lv) zeroVars (.pair ttC (.snd (.var 0)))
      (.sigma (isBoolC tboolC) (typingC (.fst (.var 1)) tnumC)) :=
    .pairIntro tSigma (LevelTower.IsUniverse.sort _)
      (Typed.convType (tt_typed lv) ⟨_, LevelTower.IsUniverse.sort _, (isBool_tbool_eq lv).symm⟩) px
  exact .pairIntro (exp_typed lv (tbool_typed lv)) (LevelTower.IsUniverse.sort _) ar
    (Typed.convType tProof ⟨_, LevelTower.IsUniverse.sort _, eq.symm⟩)

section Instances

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- **`add x y : exp tnum`** for `x y : exp tnum`: two constructors at the index `tnum`. -/
theorem add_typed {x y : Tm Tower.Head n} (tx : Typed (rules lv) Γ x (expC tnumC))
    (ty' : Typed (rules lv) Γ y (expC tnumC)) : Typed (rules lv) Γ (addE x y) (expC tnumC) :=
  Typed.substitute (add_typed_vars lv) (SubstMor.cons (SubstMor.cons (subst_nil lv) tx) ty')

/-- **`ite x y z : exp t`** for `x : exp tbool` and `y z : exp t`, at every index. -/
theorem ite_typed {t x y z : Tm Tower.Head n} (tt' : Typed (rules lv) Γ t tyC)
    (tx : Typed (rules lv) Γ x (expC tboolC)) (ty' : Typed (rules lv) Γ y (expC t))
    (tz : Typed (rules lv) Γ z (expC t)) : Typed (rules lv) Γ (iteE x y z) (expC t) :=
  Typed.substitute (ite_typed_vars lv)
    (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (subst_nil lv) tt') tx) ty') tz)

/-- **`iszero x : exp tbool`** for `x : exp tnum`. -/
theorem iszero_typed {x : Tm Tower.Head n} (tx : Typed (rules lv) Γ x (expC tnumC)) :
    Typed (rules lv) Γ (iszeroE x) (expC tboolC) :=
  Typed.substitute (iszero_typed_vars lv) (SubstMor.cons (subst_nil lv) tx)

end Instances

/-! ## The recursion principle is typed -/

/-- A family over the object types and the five methods of the recursion principle. -/
structure Methods {n : Nat} (Γ : Ctx Tower.Head n) (Q m₁ m₂ m₃ m₄ m₅ : Tm Tower.Head n) : Prop where
  tQ : Typed (rules lv) Γ Q (.pi tyC U0)
  t₁ : Typed (rules lv) Γ m₁ (.pi numC (.app (Presentation.rename wk Q) tnumC))
  t₂ : Typed (rules lv) Γ m₂ (.pi boolC (.app (Presentation.rename wk Q) tboolC))
  t₃ : Typed (rules lv) Γ m₃ (.pi (.app Q tnumC) (.pi (.app (Presentation.rename wk Q) tnumC)
    (.app (Presentation.rename wk (Presentation.rename wk Q)) tnumC)))
  t₄ : Typed (rules lv) Γ m₄ (.pi tyC (.pi (.app (Presentation.rename wk Q) tboolC)
    (.pi (.app (Presentation.rename wk (Presentation.rename wk Q)) (.var 1))
      (.pi (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk Q))) (.var 2))
        (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
          (Presentation.rename wk Q)))) (.var 3))))))
  t₅ : Typed (rules lv) Γ m₅ (.pi (.app Q tnumC) (.app (Presentation.rename wk Q) tboolC))

section Recursion

variable {n : Nat} {Γ : Ctx Tower.Head n} {Q m₁ m₂ m₃ m₄ m₅ : Tm Tower.Head n}

/-- `syntax-rec Q m r t p : Q t`. -/
theorem synRec_typed (M : Methods lv Γ Q m₁ m₂ m₃ m₄ m₅) {r t p : Tm Tower.Head n}
    (tr : Typed (rules lv) Γ r rawC) (tt' : Typed (rules lv) Γ t tyC) (tp : Typed (rules lv) Γ p (typingC r t)) :
    Typed (rules lv) Γ (synRecC Q m₁ m₂ m₃ m₄ m₅ r t p) (.app Q t) := by
  have tc : Typed (rules lv) Γ (.const synRec) (liftClosed (closeType (ofEntries synEntries (6 + 1 + 2)) synResult)) :=
    (declaresSynRec lv (fun _ => 0) (laws lv fun _ => 0)).typing
  have m₀ : SubstMor (rules lv) .nil Γ fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) (ofEntries synEntries 9) Γ
      (consSub p (consSub t (consSub r (consSub m₅ (consSub m₄ (consSub m₃ (consSub m₂ (consSub m₁
        (consSub Q fun i => Fin.elim0 i))))))))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons
      (SubstMor.cons (SubstMor.cons m₀ M.tQ) M.t₁) M.t₂) M.t₃) M.t₄) M.t₅) tr) tt') tp
  exact Typed.telescope_apply mor tc

/-- **The recursion principle is typed**: `rec Q m t e : Q t` for `e : exp t`. -/
theorem expRec_typed (M : Methods lv Γ Q m₁ m₂ m₃ m₄ m₅) {t e : Tm Tower.Head n}
    (tt' : Typed (rules lv) Γ t tyC) (te : Typed (rules lv) Γ e (expC t)) :
    Typed (rules lv) Γ (expRecC Q m₁ m₂ m₃ m₄ m₅ t e) (.app Q t) := by
  have tp : Typed (rules lv) Γ (.snd e) (typingC (.fst e) t) := by
    have h := Derivable.sndElim te
    change Typed (rules lv) Γ (.snd e) (typingC (.fst e) (inst0 (.fst e) (Presentation.rename wk t))) at h
    rwa [inst0_rename_wk] at h
  exact synRec_typed lv M (.fstElim te) tt' tp

/-- Reduction preserves typing in the package. -/
theorem reduces_preserve (formed : CtxFormed (rules lv) Γ) {t t' T : Tm Tower.Head n}
    (red : Reduces (rules lv) t t') (typing : Typed (rules lv) Γ t T) :
    Typed (rules lv) Γ t' T ∧ Equal (rules lv) Γ t t' T :=
  Reduces.preserve (S := setting lv fun _ => 0) (facts lv) (roots lv) (heads lv) formed red typing

/-! ### The computation rules on every constructor, on open arguments -/

variable (formed : CtxFormed (rules lv) Γ) (M : Methods lv Γ Q m₁ m₂ m₃ m₄ m₅)
include formed M

/-- **At a numeral literal**: `rec Q m tnum (lit k) ≡ mnum k`. -/
theorem expRec_lit {k : Tm Tower.Head n} (tk : Typed (rules lv) Γ k numC) :
    Equal (rules lv) Γ (expRecC Q m₁ m₂ m₃ m₄ m₅ tnumC (litE k)) (.app m₁ k) (.app Q tnumC) :=
  (reduces_preserve lv formed (expRec_lit_red lv Q m₁ m₂ m₃ m₄ m₅ k)
    (expRec_typed lv M (tnum_typed lv) (lit_typed lv tk))).2

/-- **At a Boolean literal**: `rec Q m tbool (blit b) ≡ mbool b`. -/
theorem expRec_blit {b : Tm Tower.Head n} (tb : Typed (rules lv) Γ b boolC) :
    Equal (rules lv) Γ (expRecC Q m₁ m₂ m₃ m₄ m₅ tboolC (blitE b)) (.app m₂ b) (.app Q tboolC) :=
  (reduces_preserve lv formed (expRec_blit_red lv Q m₁ m₂ m₃ m₄ m₅ b)
    (expRec_typed lv M (tbool_typed lv) (blit_typed lv tb))).2

/-- **At an addition**, the second constructor at `tnum`, on open `x` and `y`:
`rec Q m tnum (add x y) ≡ madd (rec Q m tnum x) (rec Q m tnum y)`. -/
theorem expRec_add {x y : Tm Tower.Head n} (tx : Typed (rules lv) Γ x (expC tnumC))
    (ty' : Typed (rules lv) Γ y (expC tnumC)) :
    Equal (rules lv) Γ (expRecC Q m₁ m₂ m₃ m₄ m₅ tnumC (addE x y))
      (.app (.app m₃ (expRecC Q m₁ m₂ m₃ m₄ m₅ tnumC x)) (expRecC Q m₁ m₂ m₃ m₄ m₅ tnumC y)) (.app Q tnumC) :=
  (reduces_preserve lv formed (expRec_add_red lv Q m₁ m₂ m₃ m₄ m₅ x y)
    (expRec_typed lv M (tnum_typed lv) (add_typed lv tx ty'))).2

/-- **At a conditional, at every index, a variable included**:
`rec Q m t (ite x y z) ≡ mif t (rec Q m tbool x) (rec Q m t y) (rec Q m t z)`. -/
theorem expRec_ite {t x y z : Tm Tower.Head n} (tt' : Typed (rules lv) Γ t tyC)
    (tx : Typed (rules lv) Γ x (expC tboolC)) (ty' : Typed (rules lv) Γ y (expC t))
    (tz : Typed (rules lv) Γ z (expC t)) :
    Equal (rules lv) Γ (expRecC Q m₁ m₂ m₃ m₄ m₅ t (iteE x y z))
      (.app (.app (.app (.app m₄ t) (expRecC Q m₁ m₂ m₃ m₄ m₅ tboolC x)) (expRecC Q m₁ m₂ m₃ m₄ m₅ t y))
        (expRecC Q m₁ m₂ m₃ m₄ m₅ t z)) (.app Q t) :=
  (reduces_preserve lv formed (expRec_ite_red lv Q m₁ m₂ m₃ m₄ m₅ t x y z)
    (expRec_typed lv M tt' (ite_typed lv tt' tx ty' tz))).2

/-- **At a zero test**: `rec Q m tbool (iszero x) ≡ mzero (rec Q m tnum x)`. -/
theorem expRec_iszero {x : Tm Tower.Head n} (tx : Typed (rules lv) Γ x (expC tnumC)) :
    Equal (rules lv) Γ (expRecC Q m₁ m₂ m₃ m₄ m₅ tboolC (iszeroE x))
      (.app m₅ (expRecC Q m₁ m₂ m₃ m₄ m₅ tnumC x)) (.app Q tboolC) :=
  (reduces_preserve lv formed (expRec_iszero_red lv Q m₁ m₂ m₃ m₄ m₅ x)
    (expRec_typed lv M (tbool_typed lv) (iszero_typed lv tx))).2

end Recursion

/-! ## The interpreter -/

section Interpreter

variable {n : Nat} {Γ : Ctx Tower.Head n}

theorem valFam_typed : Typed (rules lv) Γ valFam (.pi tyC U0) := tyFam_typed lv rfl

/-- `val tnum → val tnum → val tnum` is `num → num → num`. -/
theorem addType_eq : Equal (rules lv) Γ (.pi (valC tnumC) (.pi (valC tnumC) (valC tnumC)))
    (.pi numC (.pi numC numC)) (.head (.sort (.max (.const 0) (.max (.const 0) (.const 0))))) :=
  .piCong (val_tnum_eq lv) (LevelTower.IsUniverse.sort _)
    (.piCong (val_tnum_eq lv) (LevelTower.IsUniverse.sort _) (val_tnum_eq lv) (LevelTower.IsUniverse.sort _)
      (LevelTower.Join.sorts _ _)) (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)

/-- `val tnum → val tbool` is `num → bool`. -/
theorem zeroType_eq : Equal (rules lv) Γ (.pi (valC tnumC) (valC tboolC)) (.pi numC boolC)
    (.head (.sort (.max (.const 0) (.const 0)))) :=
  .piCong (val_tnum_eq lv) (LevelTower.IsUniverse.sort _) (val_tbool_eq lv) (LevelTower.IsUniverse.sort _)
    (LevelTower.Join.sorts _ _)

theorem evalNum_typed : Typed (rules lv) Γ evalNum (.pi numC (.app valFam tnumC)) := by
  have tPi : Typed (rules lv) Γ (.pi numC (valC tnumC)) (.head (.sort (.max (.const 0) (.const 0)))) :=
    .piForm (num_typed lv) (LevelTower.IsUniverse.sort _) (val_typed lv (tnum_typed lv))
      (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)
  have body : Typed (rules lv) (.snoc Γ numC) (.var 0) (valC tnumC) :=
    Typed.convType (.var 0) ⟨_, LevelTower.IsUniverse.sort _, (val_tnum_eq lv).symm⟩
  exact .lamIntro tPi (LevelTower.IsUniverse.sort _) body

theorem evalBool_typed : Typed (rules lv) Γ evalBool (.pi boolC (.app valFam tboolC)) := by
  have tPi : Typed (rules lv) Γ (.pi boolC (valC tboolC)) (.head (.sort (.max (.const 0) (.const 0)))) :=
    .piForm (bool_typed lv) (LevelTower.IsUniverse.sort _) (val_typed lv (tbool_typed lv))
      (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)
  have body : Typed (rules lv) (.snoc Γ boolC) (.var 0) (valC tboolC) :=
    Typed.convType (.var 0) ⟨_, LevelTower.IsUniverse.sort _, (val_tbool_eq lv).symm⟩
  exact .lamIntro tPi (LevelTower.IsUniverse.sort _) body

theorem evalAdd_typed : Typed (rules lv) Γ evalAdd
    (.pi (.app valFam tnumC) (.pi (.app valFam tnumC) (.app valFam tnumC))) := by
  have tAdd : Typed (rules lv) Γ (.const add) (.pi numC (.pi numC numC)) :=
    .const (type := .pi numC (.pi numC numC)) rfl
      ((tw_rules lv).pi_small (num_typed lv) ((tw_rules lv).pi_small (num_typed lv) (num_typed lv)))
      (LevelTower.IsUniverse.sort _)
  exact Typed.convType tAdd ⟨_, LevelTower.IsUniverse.sort _, (addType_eq lv).symm⟩

theorem evalZero_typed : Typed (rules lv) Γ evalZero (.pi (.app valFam tnumC) (.app valFam tboolC)) := by
  have tZ : Typed (rules lv) Γ (.const isZero) (.pi numC boolC) :=
    .const (type := isZeroType) rfl ((tw_rules lv).pi_small (num_typed lv) (bool_typed lv))
      (LevelTower.IsUniverse.sort _)
  exact Typed.convType tZ ⟨_, LevelTower.IsUniverse.sort _, (zeroType_eq lv).symm⟩

/-- The Booleans' recursor at a motive, two cases and a scrutinee. -/
theorem boolRec_app_typed {P x y b : Tm Tower.Head n} (tP : Typed (rules lv) Γ P (.pi boolC (.head (.sort lv))))
    (tx : Typed (rules lv) Γ x (.app P btrueC)) (ty' : Typed (rules lv) Γ y (.app P bfalseC))
    (tb : Typed (rules lv) Γ b boolC) : Typed (rules lv) Γ (boolRecC P x y b) (.app P b) := by
  obtain ⟨w, hw, typed⟩ := twoRecType_typed lv (tw_rules lv) (T := bool) (k₁ := btrue) (k₂ := bfalse) rfl rfl rfl
  have tc : Typed (rules lv) Γ (.const boolRec) (liftClosed (recType bool (.sort lv) boolCtors)) :=
    .const rfl typed hw
  have m₀ : SubstMor (rules lv) .nil Γ fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) (recTele bool (.sort lv) boolCtors) Γ
      (consSub b (consSub y (consSub x (consSub P fun i => Fin.elim0 i)))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tP) tx) ty') tb
  exact Typed.telescope_apply mor tc

/-- The conditional's method: `λ t c y z. bool-rec (λ _. val t) y z c`. -/
theorem evalIf_typed : Typed (rules lv) Γ evalIf
    (.pi tyC (.pi (.app valFam tboolC) (.pi (.app valFam (.var 1)) (.pi (.app valFam (.var 2))
      (.app valFam (.var 3)))))) := by
  have tw := tw_rules lv
  -- the context `t, c, y, z`
  let Γ₄ : Ctx Tower.Head (n + 4) :=
    .snoc (.snoc (.snoc (.snoc Γ tyC) (valC tboolC)) (valC (.var 1))) (valC (.var 2))
  have tt₄ : Typed (rules lv) Γ₄ (.var 3) tyC := .var 3
  have tc₄ : Typed (rules lv) Γ₄ (.var 2) (valC tboolC) := .var 2
  have ty₄ : Typed (rules lv) Γ₄ (.var 1) (valC (.var 3)) := .var 1
  have tz₄ : Typed (rules lv) Γ₄ (.var 0) (valC (.var 3)) := .var 0
  -- the motive `λ _. val t`
  have tt₅ : Typed (rules lv) (.snoc Γ₄ boolC) (.var 4) tyC := .var 4
  have tBody : Typed (rules lv) (.snoc Γ₄ boolC) (valC (.var 4)) (.head (.sort lv)) :=
    tw.lift (val_typed lv tt₅) lv
  have tMty : Typed (rules lv) Γ₄ (.pi boolC (.head (.sort lv))) (.head (.sort (.max (.const 0) (.succ lv)))) :=
    .piForm (bool_typed lv) (LevelTower.IsUniverse.sort _) (.headType (tw.headTyping _))
      (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)
  have tM : Typed (rules lv) Γ₄ (.lam (valC (.var 4))) (.pi boolC (.head (.sort lv))) :=
    .lamIntro tMty (LevelTower.IsUniverse.sort _) tBody
  have betaT : Equal (rules lv) Γ₄ (.app (.lam (valC (.var 4))) btrueC) (valC (.var 3)) (.head (.sort lv)) :=
    .betaPi tMty (LevelTower.IsUniverse.sort _) tBody (btrue_typed lv)
  have betaF : Equal (rules lv) Γ₄ (.app (.lam (valC (.var 4))) bfalseC) (valC (.var 3)) (.head (.sort lv)) :=
    .betaPi tMty (LevelTower.IsUniverse.sort _) tBody (bfalse_typed lv)
  have tb : Typed (rules lv) Γ₄ (.var 2) boolC := Typed.convType tc₄ ⟨_, LevelTower.IsUniverse.sort _, val_tbool_eq lv⟩
  have betaB : Equal (rules lv) Γ₄ (.app (.lam (valC (.var 4))) (.var 2)) (valC (.var 3)) (.head (.sort lv)) :=
    .betaPi tMty (LevelTower.IsUniverse.sort _) tBody tb
  have tRec := boolRec_app_typed lv tM (Typed.convType ty₄ ⟨_, LevelTower.IsUniverse.sort _, betaT.symm⟩)
    (Typed.convType tz₄ ⟨_, LevelTower.IsUniverse.sort _, betaF.symm⟩) tb
  have tRec' : Typed (rules lv) Γ₄ (boolRecC (.lam (valC (.var 4))) (.var 1) (.var 0) (.var 2)) (valC (.var 3)) :=
    Typed.convType tRec ⟨_, LevelTower.IsUniverse.sort _, betaB⟩
  -- abstracting `z`, `y`, `c`, `t`
  have pz : Typed (rules lv) (.snoc (.snoc (.snoc Γ tyC) (valC tboolC)) (valC (.var 1)))
      (.pi (valC (.var 2)) (valC (.var 3))) (.head (.sort (.max (.const 0) (.const 0)))) :=
    .piForm (val_typed lv (.var 2)) (LevelTower.IsUniverse.sort _) (val_typed lv (.var 3))
      (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)
  have l₄ := Derivable.lamIntro pz (LevelTower.IsUniverse.sort _) tRec'
  have py : Typed (rules lv) (.snoc (.snoc Γ tyC) (valC tboolC))
      (.pi (valC (.var 1)) (.pi (valC (.var 2)) (valC (.var 3)))) (.head (.sort (.max (.const 0)
        (.max (.const 0) (.const 0))))) :=
    .piForm (val_typed lv (.var 1)) (LevelTower.IsUniverse.sort _) pz (LevelTower.IsUniverse.sort _)
      (LevelTower.Join.sorts _ _)
  have l₃ := Derivable.lamIntro py (LevelTower.IsUniverse.sort _) l₄
  have pc : Typed (rules lv) (.snoc Γ tyC) (.pi (valC tboolC) (.pi (valC (.var 1)) (.pi (valC (.var 2))
      (valC (.var 3))))) (.head (.sort (.max (.const 0) (.max (.const 0) (.max (.const 0) (.const 0)))))) :=
    .piForm (val_typed lv (tbool_typed lv)) (LevelTower.IsUniverse.sort _) py (LevelTower.IsUniverse.sort _)
      (LevelTower.Join.sorts _ _)
  have l₂ := Derivable.lamIntro pc (LevelTower.IsUniverse.sort _) l₃
  have pt : Typed (rules lv) Γ (.pi tyC (.pi (valC tboolC) (.pi (valC (.var 1)) (.pi (valC (.var 2))
      (valC (.var 3)))))) (.head (.sort (.max (.const 0) (.max (.const 0) (.max (.const 0)
        (.max (.const 0) (.const 0))))))) :=
    .piForm (ty_typed lv) (LevelTower.IsUniverse.sort _) pc (LevelTower.IsUniverse.sort _)
      (LevelTower.Join.sorts _ _)
  exact Derivable.lamIntro pt (LevelTower.IsUniverse.sort _) l₂

/-- **The interpreter's methods are typed** at the value type. -/
theorem evalMethods : Methods lv Γ valFam evalNum evalBool evalAdd evalIf evalZero where
  tQ := valFam_typed lv
  t₁ := evalNum_typed lv
  t₂ := evalBool_typed lv
  t₃ := evalAdd_typed lv
  t₄ := evalIf_typed lv
  t₅ := evalZero_typed lv

/-- **The interpreter is typed**: `eval t e : val t` for `e : exp t`. -/
theorem eval_typed {t e : Tm Tower.Head n} (tt' : Typed (rules lv) Γ t tyC) (te : Typed (rules lv) Γ e (expC t)) :
    Typed (rules lv) Γ (evalC t e) (valC t) :=
  expRec_typed lv (evalMethods lv) tt' te

/-- `eval tnum (lit k) ⟶* k`. -/
theorem eval_lit_red (k : Tm Tower.Head n) : Reduces (rules lv) (evalC tnumC (litE k)) k :=
  .tail (expRec_lit_red lv valFam evalNum evalBool evalAdd evalIf evalZero k) (.betaPi (.var 0) k)

/-- **The interpreter at a literal**: `eval tnum (lit k) ≡ k`. -/
theorem eval_lit (formed : CtxFormed (rules lv) Γ) {k : Tm Tower.Head n} (tk : Typed (rules lv) Γ k numC) :
    Equal (rules lv) Γ (evalC tnumC (litE k)) k (valC tnumC) :=
  (reduces_preserve lv formed (eval_lit_red lv k) (eval_typed lv (tnum_typed lv) (lit_typed lv tk))).2

/-- **The interpreter at an addition**, on open `x` and `y`: `eval tnum (add x y) ≡ add (eval x) (eval y)`. -/
theorem eval_add (formed : CtxFormed (rules lv) Γ) {x y : Tm Tower.Head n}
    (tx : Typed (rules lv) Γ x (expC tnumC)) (ty' : Typed (rules lv) Γ y (expC tnumC)) :
    Equal (rules lv) Γ (evalC tnumC (addE x y)) (addC (evalC tnumC x) (evalC tnumC y)) (valC tnumC) :=
  expRec_add lv formed (evalMethods lv) tx ty'

/-- `2 + 3 ⟶* 5`. -/
theorem add_two_three_red :
    Reduces (rules lv) (addC (numeral 2) (numeral 3) : Tm Tower.Head n) (numeral 5) :=
  .tail (.tail (.single (.root (add_succ_step lv (numeral 1) (numeral 3))))
    (.congAppArg (.root (add_succ_step lv (numeral 0) (numeral 3)))))
    (.congAppArg (.congAppArg (.root (add_zero_step lv (numeral 3)))))

/-- **`eval (add (lit 2) (lit 3)) ⟶* 5`**, by the package's computation. -/
theorem eval_two_plus_three_red :
    Reduces (rules lv) (evalC tnumC (addE (litE (numeral 2)) (litE (numeral 3))) : Tm Tower.Head n) (numeral 5) :=
  (expRec_add_red lv valFam evalNum evalBool evalAdd evalIf evalZero (litE (numeral 2)) (litE (numeral 3))).trans
    ((red_appFun lv (red_appArg lv (eval_lit_red lv (numeral 2)))).trans
      ((red_appArg lv (eval_lit_red lv (numeral 3))).trans (add_two_three_red lv)))

/-- **`eval (add (lit 2) (lit 3)) ≡ 5`, by conversion**, at the value type and at the numbers. -/
theorem eval_two_plus_three (formed : CtxFormed (rules lv) Γ) :
    Equal (rules lv) Γ (evalC tnumC (addE (litE (numeral 2)) (litE (numeral 3)))) (numeral 5) (valC tnumC) ∧
      Equal (rules lv) Γ (evalC tnumC (addE (litE (numeral 2)) (litE (numeral 3)))) (numeral 5) numC := by
  have typing : Typed (rules lv) Γ (evalC tnumC (addE (litE (numeral 2)) (litE (numeral 3)))) (valC tnumC) :=
    eval_typed lv (tnum_typed lv) (add_typed lv (lit_typed lv (numeral_typed lv 2)) (lit_typed lv (numeral_typed lv 3)))
  have e := (reduces_preserve lv formed (eval_two_plus_three_red lv) typing).2
  exact ⟨e, Equal.convType e ⟨_, LevelTower.IsUniverse.sort _, val_tnum_eq lv⟩⟩

end Interpreter

/-! ## Controls -/

section Controls

variable {n : Nat} {Γ : Ctx Tower.Head n} (formed : CtxFormed (rules lv) Γ)

theorem setting_roles_raw (valuation : Nat → Nat) : (setting lv valuation).roles raw = .inductive rawCtors :=
  roles_raw

theorem setting_roles_num (valuation : Nat → Nat) : (setting lv valuation).roles num = .inductive ctors :=
  roles_num

include formed

/-- The untyped expression of a literal. -/
theorem fst_lit {k : Tm Tower.Head n} (tk : Typed (rules lv) Γ k numC) :
    Equal (rules lv) Γ (.fst (litE k)) (rnumC k) rawC :=
  (reduces_preserve lv formed (.single (.betaSigmaFst (rnumC k) ttC)) (.fstElim (lit_typed lv tk))).2

/-- Numerals are injective. -/
theorem numeral_injective {a b : Tm Tower.Head n}
    (equal : Equal (rules lv) Γ (succC a) (succC b) numC) : Equal (rules lv) Γ a b numC := by
  obtain ⟨_, _, fieldsEqual⟩ := Equal.ctor_injective (S := setting lv fun _ => 0) (laws lv _) (constants lv _)
    formed (setting_roles_num lv _) mem_succ mem_succ (as := [a]) (bs := [b]) equal
  cases fieldsEqual with
  | cons head _ => exact head

/-- **The family is not degenerate**: `lit 2` and `lit 3` are different expressions of `exp tnum`. -/
theorem lit_two_ne_three :
    ¬ Equal (rules lv) Γ (litE (numeral 2)) (litE (numeral 3)) (expC tnumC) := by
  intro equal
  have e₁ : Equal (rules lv) Γ (.fst (litE (numeral 2))) (.fst (litE (numeral 3))) rawC := .fstCong equal
  have e₂ : Equal (rules lv) Γ (rnumC (numeral 2)) (rnumC (numeral 3)) rawC :=
    .trans (.symm (fst_lit lv formed (numeral_typed lv 2))) (.trans e₁ (fst_lit lv formed (numeral_typed lv 3)))
  obtain ⟨_, _, fieldsEqual⟩ := Equal.ctor_injective (S := setting lv fun _ => 0) (laws lv _) (constants lv _)
    formed (setting_roles_raw lv _) mem_rnum mem_rnum (as := [numeral 2]) (bs := [numeral 3]) e₂
  cases fieldsEqual with
  | cons head _ =>
      have e₃ : Equal (rules lv) Γ (numeral 2) (numeral 3) numC := head
      have e₄ := numeral_injective lv formed (numeral_injective lv formed e₃)
      exact Equal.ctor_discrimination (S := setting lv fun _ => 0) (laws lv _) (constants lv _) formed
        (setting_roles_num lv _) mem_zero mem_succ (by decide) (as := []) (bs := [zeroC]) e₄

/-- **No confusion between the two constructors at `tnum`**: a literal is no addition. -/
theorem lit_ne_add {k x y : Tm Tower.Head n} (tk : Typed (rules lv) Γ k numC)
    (tx : Typed (rules lv) Γ x (expC tnumC)) (ty' : Typed (rules lv) Γ y (expC tnumC)) :
    ¬ Equal (rules lv) Γ (litE k) (addE x y) (expC tnumC) := by
  intro equal
  have e₁ : Equal (rules lv) Γ (.fst (litE k)) (.fst (addE x y)) rawC := .fstCong equal
  have fstAdd : Equal (rules lv) Γ (.fst (addE x y)) (raddC (.fst x) (.fst y)) rawC :=
    (reduces_preserve lv formed (.single (.betaSigmaFst _ _)) (.fstElim (add_typed lv tx ty'))).2
  have e₂ : Equal (rules lv) Γ (rnumC k) (raddC (.fst x) (.fst y)) rawC :=
    .trans (.symm (fst_lit lv formed tk)) (.trans e₁ fstAdd)
  exact Equal.ctor_discrimination (S := setting lv fun _ => 0) (laws lv _) (constants lv _) formed
    (setting_roles_raw lv _) mem_rnum mem_radd (by decide) (as := [k]) (bs := [.fst x, .fst y]) e₂

/-- The empty type is not the unit type. -/
theorem void_ne_unit : ¬ TypeEq (rules lv) Γ voidC unitC := fun equal =>
  absurd (TypeEq.inductive_injective (facts lv) roles_void roles_unit equal formed) (by decide)

/-- **An ill-indexed literal is rejected**: `lit 0` is no expression of Boolean type, since its proof
would have the empty type `typed (rnum 0) tbool ≡ void`. -/
theorem lit_not_bool : ¬ Typed (rules lv) Γ (litE zeroC) (expC tboolC) := by
  intro typing
  have tSnd : Typed (rules lv) Γ (.snd (litE zeroC)) (typingC (.fst (litE zeroC)) tboolC) := .sndElim typing
  have tTt : Typed (rules lv) Γ ttC (typingC (.fst (litE zeroC)) tboolC) :=
    (reduces_preserve lv formed (.single (.betaSigmaSnd (rnumC zeroC) ttC)) tSnd).1
  have tyRed : Reduces (rules lv) (typingC (.fst (litE zeroC)) tboolC : Tm Tower.Head n) voidC :=
    .tail (.tail (.single (.congAppFun (.congAppArg (.betaSigmaFst (rnumC zeroC) ttC))))
      (.root (typing_rnum_step lv zeroC tboolC))) (.root (isNum_tbool_step lv))
  have tyEq : Equal (rules lv) Γ (typingC (.fst (litE zeroC)) tboolC) voidC U0 :=
    (reduces_preserve lv formed tyRed (typing_typed lv (.fstElim typing) (tbool_typed lv))).2
  have ttVoid : Typed (rules lv) Γ ttC voidC := Typed.convType tTt ⟨_, LevelTower.IsUniverse.sort _, tyEq⟩
  obtain ⟨type, w, declared, _, _, le⟩ := Typed.generation ttVoid
  have known : (rules lv).constantType tt = some unitC := rfl
  rw [known] at declared
  obtain rfl := Option.some.inj declared
  have equal : TypeEq (rules lv) Γ unitC voidC :=
    TypeLe.rigid (S := setting lv fun _ => 0) le ⟨_, LevelTower.IsUniverse.sort _, void_typed lv⟩ formed
      (fun _ _ e => TypeEq.inductive_ne_head (facts lv) roles_unit formed e)
      (fun _ _ e => TypeEq.inductive_ne_pi (facts lv) roles_unit formed e)
      (fun _ _ e => TypeEq.inductive_ne_sigma (facts lv) roles_unit formed e)
  exact void_ne_unit lv formed equal.symm

/-- **The type former separates the closed indices**: `exp tnum` is not `exp tbool`. -/
theorem exp_tnum_ne_tbool : ¬ TypeEq (rules lv) Γ (expC tnumC) (expC tboolC) := fun equal =>
  lit_not_bool lv formed (Typed.convType (lit_typed lv (zero_typed lv)) equal)

end Controls

section Neutral

variable {n : Nat}

/-- **Stuck on a variable expression**: `rec Q m t x` is neutral for a variable `x`. -/
theorem expRec_stuck_variable (Q m₁ m₂ m₃ m₄ m₅ t : Tm Tower.Head n) (x : Fin n) :
    Neutral roles (expRecC Q m₁ m₂ m₃ m₄ m₅ t (.var x)) ∧
      Whnf (rules lv) roles (expRecC Q m₁ m₂ m₃ m₄ m₅ t (.var x)) := by
  have neutral : Neutral roles (expRecC Q m₁ m₂ m₃ m₄ m₅ t (.var x)) :=
    Neutral.stuck_single (before := [Q, m₁, m₂, m₃, m₄, m₅]) (after := [t, .snd (.var x)]) roles_synRec rfl
      (.fst (.var x))
  exact ⟨neutral, neutral.whnf (shape lv)⟩

/-- **Not an inductive family: at a variable index the recursion unfolds on an untyped constructor**,
and stops at the transport, stuck on the index. A true inductive family has no constructor form at an
index that is not the constructor's. -/
theorem unfolds_at_variable_index (Q m₁ m₂ m₃ m₄ m₅ k p : Tm Tower.Head n) (x : Fin n) :
    WhStep (rules lv) roles (synRecC Q m₁ m₂ m₃ m₄ m₅ (rnumC k) (.var x) p) (atNumC Q (.app m₁ k) (.var x) p) ∧
      Neutral roles (atNumC Q (.app m₁ k) (.var x) p) :=
  ⟨.root (synRec_rnum_step lv Q m₁ m₂ m₃ m₄ m₅ k (.var x) p),
    Neutral.stuck_single (before := [Q, .app m₁ k]) (after := [p]) roles_atNum rfl (.var x)⟩

/-- The context `t : ty, p : is-num t`. -/
abbrev junkCtx : Ctx Tower.Head 2 := .snoc (.snoc .nil tyC) (isNumC (.var 0))

/-- **An element with an untyped constructor at a variable index**: `(rnum 0, p) : exp t` for a proof
`p : is-num t` of the computed equation of the index. -/
theorem junk_typed : Typed (rules lv) junkCtx (.pair (rnumC zeroC) (.var 0)) (expC (.var 1)) := by
  have tt' : Typed (rules lv) junkCtx (.var 1) tyC := .var 1
  have tp : Typed (rules lv) junkCtx (.var 0) (isNumC (.var 1)) := .var 0
  have eq : Equal (rules lv) junkCtx (typingC (rnumC zeroC) (.var 1)) (isNumC (.var 1)) U0 :=
    .root (typing_rnum_step lv zeroC (.var 1)) (typing_typed lv ((rawD lv).rnum_app (zero_typed lv)) tt')
      (isNum_typed lv tt')
  exact .pairIntro (exp_typed lv tt') (LevelTower.IsUniverse.sort _) ((rawD lv).rnum_app (zero_typed lv))
    (Typed.convType tp ⟨_, LevelTower.IsUniverse.sort _, eq.symm⟩)

end Neutral

section Uniqueness

/-- The algorithmic equality of the package is complete. -/
theorem complete : AlgorithmicComplete (rules lv) roles :=
  AlgorithmicComplete.ofSemantic (S := setting lv fun _ => 0) (laws lv _) (constants lv _) (roots lv) (heads lv)
    (algebra lv)
    (constantsAt lv (fun _ => 0) (algorithmicSetting_laws (S := setting lv fun _ => 0) (laws lv _)
      (constants lv _) (roots lv) (heads lv) (algebra lv)))

/-- The context of two proofs of the unit type. -/
abbrev twoProofs : Ctx Tower.Head 2 := .snoc (.snoc .nil unitC) unitC

theorem twoProofs_formed : CtxFormed (rules lv) twoProofs :=
  .snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, unit_typed lv⟩) ⟨_, LevelTower.IsUniverse.sort _, unit_typed lv⟩

theorem proof₁_typed : Typed (rules lv) twoProofs (.var 1) unitC := .var 1
theorem proof₀_typed : Typed (rules lv) twoProofs (.var 0) unitC := .var 0

/-- An element `(rnum 0, p)` of `exp tnum`, for a proof `p : unit`. -/
theorem pair_proof_typed {p : Tm Tower.Head 2} (tp : Typed (rules lv) twoProofs p unitC) :
    Typed (rules lv) twoProofs (.pair (rnumC zeroC) p) (expC tnumC) :=
  .pairIntro (exp_typed lv (tnum_typed lv)) (LevelTower.IsUniverse.sort _) ((rawD lv).rnum_app (zero_typed lv))
    (Typed.convType tp ⟨_, LevelTower.IsUniverse.sort _, (typing_rnum_tnum lv (zero_typed lv)).symm⟩)

/-- The proof component of `(rnum 0, p)` is `p`, at the computed type `typed (rnum 0) tnum`. -/
theorem snd_pair_proof {p : Tm Tower.Head 2} (tp : Typed (rules lv) twoProofs p unitC) :
    Equal (rules lv) twoProofs (.snd (.pair (rnumC zeroC) p)) p (typingC (rnumC zeroC) tnumC) := by
  have formed := twoProofs_formed lv
  have tSnd : Typed (rules lv) twoProofs (.snd (.pair (rnumC zeroC) p))
      (typingC (.fst (.pair (rnumC zeroC) p)) tnumC) := .sndElim (pair_proof_typed lv tp)
  have tyEq : Equal (rules lv) twoProofs (typingC (.fst (.pair (rnumC zeroC) p)) tnumC)
      (typingC (rnumC zeroC) tnumC) U0 :=
    (reduces_preserve lv formed (.single (.congAppFun (.congAppArg (.betaSigmaFst (rnumC zeroC) p))))
      (typing_typed lv (.fstElim (pair_proof_typed lv tp)) (tnum_typed lv))).2
  have e := (reduces_preserve lv formed (.single (.betaSigmaSnd (rnumC zeroC) p)) tSnd).2
  exact Equal.convType e ⟨_, LevelTower.IsUniverse.sort _, tyEq⟩

/-- **Proofs of typing are not definitionally unique**: two expressions with the same untyped
expression `rnum 0` and the two different proof variables `p q : unit` are not equal. The unit type has
no η; a true inductive family has no proof component at all. -/
theorem same_raw_not_equal :
    ¬ Equal (rules lv) twoProofs (.pair (rnumC zeroC) (.var 1)) (.pair (rnumC zeroC) (.var 0)) (expC tnumC) := by
  intro equal
  have formed := twoProofs_formed lv
  have e₁ : Equal (rules lv) twoProofs (.snd (.pair (rnumC zeroC) (.var 1))) (.snd (.pair (rnumC zeroC) (.var 0)))
      (typingC (.fst (.pair (rnumC zeroC) (.var 1))) tnumC) := .sndCong equal
  have tyEq : Equal (rules lv) twoProofs (typingC (.fst (.pair (rnumC zeroC) (.var 1))) tnumC)
      (typingC (rnumC zeroC) tnumC) U0 :=
    (reduces_preserve lv formed (.single (.congAppFun (.congAppArg (.betaSigmaFst (rnumC zeroC) (.var 1)))))
      (typing_typed lv (.fstElim (pair_proof_typed lv (proof₁_typed lv))) (tnum_typed lv))).2
  have e₁' := Equal.convType e₁ ⟨_, LevelTower.IsUniverse.sort _, tyEq⟩
  have e₂ : Equal (rules lv) twoProofs (.var 1) (.var 0) (typingC (rnumC zeroC) tnumC) :=
    .trans (snd_pair_proof lv (proof₁_typed lv)).symm (.trans e₁' (snd_pair_proof lv (proof₀_typed lv)))
  exact not_equal_of_neutral_heads (S := setting lv fun _ => 0) (complete lv) formed (.var 1) (.var 0)
    (by simp [eliminationHead]) e₂

end Uniqueness

end TowerSyntaxModel

#print axioms TowerSyntaxModel.lit_typed
#print axioms TowerSyntaxModel.add_typed
#print axioms TowerSyntaxModel.ite_typed
#print axioms TowerSyntaxModel.iszero_typed
#print axioms TowerSyntaxModel.expRec_typed
#print axioms TowerSyntaxModel.expRec_lit
#print axioms TowerSyntaxModel.expRec_blit
#print axioms TowerSyntaxModel.expRec_add
#print axioms TowerSyntaxModel.expRec_ite
#print axioms TowerSyntaxModel.expRec_iszero
#print axioms TowerSyntaxModel.eval_typed
#print axioms TowerSyntaxModel.eval_lit
#print axioms TowerSyntaxModel.eval_add
#print axioms TowerSyntaxModel.eval_two_plus_three
#print axioms TowerSyntaxModel.lit_two_ne_three
#print axioms TowerSyntaxModel.lit_ne_add
#print axioms TowerSyntaxModel.lit_not_bool
#print axioms TowerSyntaxModel.exp_tnum_ne_tbool
#print axioms TowerSyntaxModel.typing_rbool_tnum
#print axioms TowerSyntaxModel.void_ne_unit
#print axioms TowerSyntaxModel.expRec_stuck_variable
#print axioms TowerSyntaxModel.unfolds_at_variable_index
#print axioms TowerSyntaxModel.junk_typed
#print axioms TowerSyntaxModel.complete
#print axioms TowerSyntaxModel.same_raw_not_equal

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
