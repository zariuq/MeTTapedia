import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Package
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Structural

/-!
# The accessibility code

The inductive declarations of the calculus have fields that are the declared
type itself or a closed type (`Normalization.Field`), with no indices. The
accessibility predicate is an indexed family whose constructor takes a
function field `∀ y, R y x → Acc y`, so it is not a declared inductive type.
It is a code of the impredicative proposition layer instead, by its
second-order encoding over a carrier `A`:

`acc R a := ∀ X : A → prop. (∀ x. (∀ y. R y x → X y) → X x) → X a`.

The code uses two quantifier instances of a package of proposition codes: one
over the carrier and one over predicates on it. Nothing else is added: the
code, its introduction and its inversion are terms of the package.

* `below R X x` is `∀ y. R y x → X y`;
* `progressive R X` is `∀ x. below R X x → X x`;
* `acc R a` is `∀ X. progressive R X → X a`;
* `accBelow R a` is `∀ y. R y a → acc R y`.

Substitution and renaming commute with each builder (`subst_acc`,
`rename_acc`, …). Under the laws of the two quantifier instances, the codes are
typed (`Laws.acc_typed`), and the natural-deduction rules of implication and of
both quantifiers hold in the package (`Laws.impIntro`, `Laws.allIntro`, …).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Normalization (DecoderStep inst0_var_rename_liftRen_wk)

variable {Head : Type}

/-- The names an accessibility code uses: a package of proposition codes, the
quantifier over the carrier and the quantifier over predicates on it. -/
structure CodeNames (Head : Type) where
  codes : Codes Head
  /-- `all@A`, the quantifier over the carrier. -/
  point : DeclName
  /-- `all@(A → prop)`, the quantifier over predicates on the carrier. -/
  predicate : DeclName

/-! ## Numerals of substitutions

A numeral index at a symbolic depth is the successor form it denotes, so the
lifted and extended substitutions compute on it by `rfl`. -/

@[simp] theorem liftSub_one {n m : Nat} (σ : Sub Head (n + 1) m) :
    liftSub σ (1 : Fin (n + 2)) = rename wk (σ 0) := rfl

@[simp] theorem liftSub_two {n m : Nat} (σ : Sub Head (n + 2) m) :
    liftSub σ (2 : Fin (n + 3)) = rename wk (σ 1) := rfl

@[simp] theorem liftSub_three {n m : Nat} (σ : Sub Head (n + 3) m) :
    liftSub σ (3 : Fin (n + 4)) = rename wk (σ 2) := rfl

@[simp] theorem subst0_one {n : Nat} (u : Tm Head (n + 1)) :
    subst0 u (1 : Fin (n + 2)) = .var 0 := rfl

@[simp] theorem subst0_two {n : Nat} (u : Tm Head (n + 2)) :
    subst0 u (2 : Fin (n + 3)) = .var 1 := rfl

@[simp] theorem consSub_one {n m : Nat} (t : Tm Head m) (σ : Sub Head (n + 1) m) :
    consSub t σ (1 : Fin (n + 2)) = σ 0 := rfl

@[simp] theorem consSub_two {n m : Nat} (t : Tm Head m) (σ : Sub Head (n + 2) m) :
    consSub t σ (2 : Fin (n + 3)) = σ 1 := rfl

namespace CodeNames

variable (C : CodeNames Head)

/-- The relation applied, predecessor first: `R y x`. -/
abbrev relOf {n : Nat} (R y x : Tm Head n) : Tm Head n := .app (.app R y) x

/-- `∀ y. R y x → X y`: every predecessor of `x` satisfies `X`. -/
def below {n : Nat} (R X x : Tm Head n) : Tm Head n :=
  .app (.const C.point) (.lam (C.codes.impOf (relOf (rename wk R) (.var 0) (rename wk x))
    (.app (rename wk X) (.var 0))))

/-- `∀ x. (∀ y. R y x → X y) → X x`: `X` is closed under predecessors. -/
def progressive {n : Nat} (R X : Tm Head n) : Tm Head n :=
  .app (.const C.point) (.lam (C.codes.impOf (C.below (rename wk R) (rename wk X) (.var 0))
    (.app (rename wk X) (.var 0))))

/-- `∀ X. progressive R X → X a`: the accessibility code. -/
def acc {n : Nat} (R a : Tm Head n) : Tm Head n :=
  .app (.const C.predicate) (.lam (C.codes.impOf (C.progressive (rename wk R) (.var 0))
    (.app (.var 0) (rename wk a))))

/-- `∀ y. R y a → acc R y`: every predecessor of `a` is accessible. -/
def accBelow {n : Nat} (R a : Tm Head n) : Tm Head n :=
  .app (.const C.point) (.lam (C.codes.impOf (relOf (rename wk R) (.var 0) (rename wk a))
    (C.acc (rename wk R) (.var 0))))

/-! ## Substitution and renaming -/

@[simp] theorem subst_below {n m : Nat} (σ : Sub Head n m) (R X x : Tm Head n) :
    subst σ (C.below R X x) = C.below (subst σ R) (subst σ X) (subst σ x) := by
  simp [below, Presentation.subst, Codes.impOf]

@[simp] theorem subst_progressive {n m : Nat} (σ : Sub Head n m) (R X : Tm Head n) :
    subst σ (C.progressive R X) = C.progressive (subst σ R) (subst σ X) := by
  simp [progressive, Presentation.subst, Codes.impOf]

@[simp] theorem subst_acc {n m : Nat} (σ : Sub Head n m) (R a : Tm Head n) :
    subst σ (C.acc R a) = C.acc (subst σ R) (subst σ a) := by
  simp [acc, Presentation.subst, Codes.impOf]

@[simp] theorem subst_accBelow {n m : Nat} (σ : Sub Head n m) (R a : Tm Head n) :
    subst σ (C.accBelow R a) = C.accBelow (subst σ R) (subst σ a) := by
  simp [accBelow, Presentation.subst, Codes.impOf]

@[simp] theorem rename_below {n m : Nat} (ρ : Ren n m) (R X x : Tm Head n) :
    rename ρ (C.below R X x) = C.below (rename ρ R) (rename ρ X) (rename ρ x) := by
  simp only [below, Presentation.rename, Codes.impOf, rename_liftRen_wk]
  rfl

@[simp] theorem rename_progressive {n m : Nat} (ρ : Ren n m) (R X : Tm Head n) :
    rename ρ (C.progressive R X) = C.progressive (rename ρ R) (rename ρ X) := by
  simp only [progressive, Presentation.rename, Codes.impOf, rename_liftRen_wk, rename_below]
  rfl

@[simp] theorem rename_acc {n m : Nat} (ρ : Ren n m) (R a : Tm Head n) :
    rename ρ (C.acc R a) = C.acc (rename ρ R) (rename ρ a) := by
  simp only [acc, Presentation.rename, Codes.impOf, rename_liftRen_wk, rename_progressive]
  rfl

@[simp] theorem rename_accBelow {n m : Nat} (ρ : Ren n m) (R a : Tm Head n) :
    rename ρ (C.accBelow R a) = C.accBelow (rename ρ R) (rename ρ a) := by
  simp only [accBelow, Presentation.rename, Codes.impOf, rename_liftRen_wk, rename_acc]
  rfl

end CodeNames


/-! ## The laws of the two quantifier instances -/

namespace CodeNames

variable (C : CodeNames Head)

/-- The package of `C` over a base package `B`: the base extended by the codes. -/
abbrev rules (B : Rules Head) : Rules Head := C.codes.extend B

/-- The universe of proofs, as a term. -/
abbrev U {n : Nat} : Tm Head n := .head C.codes.proofs

/-- The type of relations on the carrier `A`: `A → A → prop`. -/
def relType (A : Tm Head 0) {n : Nat} : Tm Head n :=
  .pi (liftClosed A) (.pi (liftClosed A) C.codes.propT)

/-- The type of predicates on the carrier `A`: `A → prop`. -/
def predType (A : Tm Head 0) {n : Nat} : Tm Head n := .pi (liftClosed A) C.codes.propT

@[simp] theorem rename_relType (A : Tm Head 0) {n m : Nat} (ρ : Ren n m) :
    rename ρ (C.relType A) = C.relType A := by
  simp only [relType, Presentation.rename, rename_liftClosed]

@[simp] theorem subst_relType (A : Tm Head 0) {n m : Nat} (σ : Sub Head n m) :
    subst σ (C.relType A) = C.relType A := by
  simp only [relType, Presentation.subst, subst_liftClosed]

@[simp] theorem rename_predType (A : Tm Head 0) {n m : Nat} (ρ : Ren n m) :
    rename ρ (C.predType A) = C.predType A := by
  simp only [predType, Presentation.rename, rename_liftClosed]

@[simp] theorem subst_predType (A : Tm Head 0) {n m : Nat} (σ : Sub Head n m) :
    subst σ (C.predType A) = C.predType A := by
  simp only [predType, Presentation.subst, subst_liftClosed]

theorem liftClosed_predicateCarrier (A : Tm Head 0) {n : Nat} :
    (liftClosed (.pi A C.codes.propT) : Tm Head n) = C.predType A := by
  simp only [liftClosed, Presentation.rename, predType]

/-- The laws the accessibility code needs of a base package `B` and a closed
carrier `A`: the two quantifier instances range over `A` and over `A → prop`,
the code names are apart, the universe of proofs is a universe closed under
function types, the decoder's type is formed, and `A` is a type of proofs. -/
structure Laws (B : Rules Head) (A : Tm Head 0) : Prop where
  point : C.codes.quantifiers C.point = some A
  predicate : C.codes.quantifiers C.predicate = some (.pi A C.codes.propT)
  point_apart : C.point ≠ C.codes.prop ∧ C.point ≠ C.codes.holds ∧ C.point ≠ C.codes.imp
  predicate_apart : C.predicate ≠ C.codes.prop ∧ C.predicate ≠ C.codes.holds ∧
    C.predicate ≠ C.codes.imp
  imp_apart : C.codes.imp ≠ C.codes.prop ∧ C.codes.imp ≠ C.codes.holds
  holds_apart : C.codes.holds ≠ C.codes.prop
  proofs_universe : B.isUniverse C.codes.proofs
  proofs_typed : ∃ w, B.isUniverse w ∧ B.headTyping C.codes.proofs w
  proofs_pi : ∃ w, B.join C.codes.proofs C.codes.proofs w ∧ B.cumulative w C.codes.proofs
  holds_formed : ∃ w, B.isUniverse w ∧ Typed (C.rules B) .nil C.codes.holdsType (.head w)
  carrier_typed : Typed (C.rules B) .nil A (.head C.codes.proofs)

end CodeNames

namespace CodeNames.Laws

variable {C : CodeNames Head} {B : Rules Head} {A : Tm Head 0} (L : C.Laws B A)
include L

/-! ### Formation -/

theorem prop_typed {n : Nat} {Γ : Ctx Head n} : Typed (C.rules B) Γ C.codes.propT C.U := by
  obtain ⟨w, hw, ht⟩ := L.proofs_typed
  exact .const (C.codes.extend_constantType_of_code B C.codes.codeType_prop) (.headType ht) hw

theorem holds_typed {n : Nat} {Γ : Ctx Head n} :
    Typed (C.rules B) Γ (.const C.codes.holds) (.pi C.codes.propT C.U) := by
  obtain ⟨w, hw, ht⟩ := L.holds_formed
  exact .const (C.codes.extend_constantType_of_code B (C.codes.codeType_holds L.holds_apart)) ht hw

theorem holdsOf_typed {n : Nat} {Γ : Ctx Head n} {c : Tm Head n}
    (h : Typed (C.rules B) Γ c C.codes.propT) : Typed (C.rules B) Γ (C.codes.holdsOf c) C.U :=
  .appElim L.holds_typed h

theorem pi_typed {n : Nat} {Γ : Ctx Head n} {X : Tm Head n} {Y : Tm Head (n + 1)}
    (hX : Typed (C.rules B) Γ X C.U) (hY : Typed (C.rules B) (.snoc Γ X) Y C.U) :
    Typed (C.rules B) Γ (.pi X Y) C.U := by
  obtain ⟨w, hj, hc⟩ := L.proofs_pi
  exact .cumul (.piForm hX L.proofs_universe hY L.proofs_universe hj) hc

theorem equal_pi {n : Nat} {Γ : Ctx Head n} {X X' : Tm Head n} {Y Y' : Tm Head (n + 1)}
    (dom : Equal (C.rules B) Γ X X' C.U) (cod : Equal (C.rules B) (.snoc Γ X) Y Y' C.U) :
    Equal (C.rules B) Γ (.pi X Y) (.pi X' Y') C.U := by
  obtain ⟨w, hj, hc⟩ := L.proofs_pi
  exact Derivable.cumulEq (.piCong dom L.proofs_universe cod L.proofs_universe hj) hc

theorem imp_typed {n : Nat} {Γ : Ctx Head n} :
    Typed (C.rules B) Γ (.const C.codes.imp)
      (.pi C.codes.propT (.pi C.codes.propT C.codes.propT)) :=
  .const (C.codes.extend_constantType_of_code B (C.codes.codeType_imp L.imp_apart))
    (L.pi_typed L.prop_typed (L.pi_typed L.prop_typed L.prop_typed)) L.proofs_universe

theorem impOf_typed {n : Nat} {Γ : Ctx Head n} {p q : Tm Head n}
    (hp : Typed (C.rules B) Γ p C.codes.propT) (hq : Typed (C.rules B) Γ q C.codes.propT) :
    Typed (C.rules B) Γ (C.codes.impOf p q) C.codes.propT :=
  .appElim (.appElim L.imp_typed hp) hq

theorem carrier_typed' {n : Nat} {Γ : Ctx Head n} :
    Typed (C.rules B) Γ (liftClosed A) C.U := by
  exact L.carrier_typed.rename (Δ := Γ) (ρ := fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

theorem predType_typed {n : Nat} {Γ : Ctx Head n} : Typed (C.rules B) Γ (C.predType A) C.U :=
  L.pi_typed L.carrier_typed' L.prop_typed

theorem relType_typed {n : Nat} {Γ : Ctx Head n} : Typed (C.rules B) Γ (C.relType A) C.U :=
  L.pi_typed L.carrier_typed' (L.pi_typed L.carrier_typed' L.prop_typed)

/-! ### A quantifier instance -/

/-- A quantifier instance over a closed carrier `T` of the proofs universe is
typed at `(T → prop) → prop`. -/
theorem all_typed {q : DeclName} {T : Tm Head 0} (carrier : C.codes.quantifiers q = some T)
    (apart : q ≠ C.codes.prop ∧ q ≠ C.codes.holds ∧ q ≠ C.codes.imp)
    (formedT : ∀ {k : Nat} {Δ : Ctx Head k}, Typed (C.rules B) Δ (liftClosed T) C.U)
    {n : Nat} {Γ : Ctx Head n} :
    Typed (C.rules B) Γ (.const q) (.pi (.pi (liftClosed T) C.codes.propT) C.codes.propT) := by
  have declared := C.codes.extend_constantType_of_code B (C.codes.codeType_all apart carrier)
  have formed : Typed (C.rules B) .nil (C.codes.allType T) C.U := by
    have h := L.pi_typed (L.pi_typed (formedT (Δ := .nil)) L.prop_typed) L.prop_typed
    rwa [TelescopeAbstraction.liftClosed_zero] at h
  have h := Derivable.const (Γ := Γ) declared formed L.proofs_universe
  simpa only [Codes.allType, liftClosed, Presentation.rename] using h

/-- `holds (all@T (λx. P)) ≡ Π (x : T). holds P`. -/
theorem equal_holds_all_lam {q : DeclName} {T : Tm Head 0}
    (carrier : C.codes.quantifiers q = some T)
    (apart : q ≠ C.codes.prop ∧ q ≠ C.codes.holds ∧ q ≠ C.codes.imp)
    (formedT : ∀ {k : Nat} {Δ : Ctx Head k}, Typed (C.rules B) Δ (liftClosed T) C.U)
    {n : Nat} {Γ : Ctx Head n} {P : Tm Head (n + 1)}
    (hP : Typed (C.rules B) (.snoc Γ (liftClosed T)) P C.codes.propT) :
    Equal (C.rules B) Γ (C.codes.holdsOf (.app (.const q) (.lam P)))
      (.pi (liftClosed T) (C.codes.holdsOf P)) C.U := by
  have family : Typed (C.rules B) Γ (.lam P) (.pi (liftClosed T) C.codes.propT) :=
    .lamIntro (L.pi_typed formedT L.prop_typed) L.proofs_universe hP
  have step : (C.rules B).computation.step (C.codes.holdsOf (.app (.const q) (.lam P)))
      (.pi (liftClosed T) (C.codes.holdsOf (.app (rename wk (.lam P)) (.var 0)))) :=
    C.codes.extend_decoder_step B (DecoderStep.all (D := C.codes.decoders) carrier (.lam P))
  have hf' : Typed (C.rules B) (.snoc Γ (liftClosed T)) (rename wk (.lam P))
      (.pi (liftClosed T) C.codes.propT) := by
    have h := family.weaken (extension := liftClosed T)
    simpa only [Presentation.rename, rename_liftClosed] using h
  have var0 : Typed (C.rules B) (.snoc Γ (liftClosed T)) (.var 0) (liftClosed T) := by
    have h := Derivable.var (R := C.rules B) (Γ := .snoc Γ (liftClosed T)) 0
    simpa only [Ctx.lookup_snoc_zero, rename_liftClosed] using h
  have decoded : Equal (C.rules B) Γ (C.codes.holdsOf (.app (.const q) (.lam P)))
      (.pi (liftClosed T) (C.codes.holdsOf (.app (rename wk (.lam P)) (.var 0)))) C.U :=
    .root step (L.holdsOf_typed (.appElim (L.all_typed carrier apart formedT) family))
      (L.pi_typed formedT (L.holdsOf_typed (.appElim hf' var0)))
  refine .trans decoded (L.equal_pi (.refl formedT) (.appCong (.refl L.holds_typed) ?_))
  have lifted : Typed (C.rules B) (.snoc (.snoc Γ (liftClosed T)) (liftClosed T))
      (rename (liftRen wk) P) C.codes.propT := by
    have h := hP.rename (CtxRen.snoc (Gamma := Γ) (Delta := .snoc Γ (liftClosed T))
      (rho := wk) (fun _ => rfl) (liftClosed T))
    simpa only [rename_liftClosed, Codes.propT, Presentation.rename] using h
  have beta := Derivable.betaPi (L.pi_typed formedT L.prop_typed) L.proofs_universe lifted var0
  rw [inst0_var_rename_liftRen_wk] at beta
  exact beta

theorem allIntro {q : DeclName} {T : Tm Head 0} (carrier : C.codes.quantifiers q = some T)
    (apart : q ≠ C.codes.prop ∧ q ≠ C.codes.holds ∧ q ≠ C.codes.imp)
    (formedT : ∀ {k : Nat} {Δ : Ctx Head k}, Typed (C.rules B) Δ (liftClosed T) C.U)
    {n : Nat} {Γ : Ctx Head n} {P b : Tm Head (n + 1)}
    (hP : Typed (C.rules B) (.snoc Γ (liftClosed T)) P C.codes.propT)
    (hb : Typed (C.rules B) (.snoc Γ (liftClosed T)) b (C.codes.holdsOf P)) :
    Typed (C.rules B) Γ (.lam b) (C.codes.holdsOf (.app (.const q) (.lam P))) :=
  .conv (.lamIntro (L.pi_typed formedT (L.holdsOf_typed hP)) L.proofs_universe hb)
    (.symm (L.equal_holds_all_lam carrier apart formedT hP)) L.proofs_universe

theorem allElim {q : DeclName} {T : Tm Head 0} (carrier : C.codes.quantifiers q = some T)
    (apart : q ≠ C.codes.prop ∧ q ≠ C.codes.holds ∧ q ≠ C.codes.imp)
    (formedT : ∀ {k : Nat} {Δ : Ctx Head k}, Typed (C.rules B) Δ (liftClosed T) C.U)
    {n : Nat} {Γ : Ctx Head n} {P : Tm Head (n + 1)} {f a : Tm Head n}
    (hP : Typed (C.rules B) (.snoc Γ (liftClosed T)) P C.codes.propT)
    (hf : Typed (C.rules B) Γ f (C.codes.holdsOf (.app (.const q) (.lam P))))
    (ha : Typed (C.rules B) Γ a (liftClosed T)) :
    Typed (C.rules B) Γ (.app f a) (C.codes.holdsOf (inst0 a P)) :=
  .appElim (.conv hf (L.equal_holds_all_lam carrier apart formedT hP) L.proofs_universe) ha

/-! ### Implication -/

/-- `holds (imp p q) ≡ Π (_ : holds p). holds q`. -/
theorem equal_holds_imp {n : Nat} {Γ : Ctx Head n} {p q : Tm Head n}
    (hp : Typed (C.rules B) Γ p C.codes.propT) (hq : Typed (C.rules B) Γ q C.codes.propT) :
    Equal (C.rules B) Γ (C.codes.holdsOf (C.codes.impOf p q))
      (.pi (C.codes.holdsOf p) (C.codes.holdsOf (rename wk q))) C.U :=
  .root (C.codes.extend_decoder_step B (DecoderStep.imp p q))
    (L.holdsOf_typed (L.impOf_typed hp hq))
    (L.pi_typed (L.holdsOf_typed hp) (L.holdsOf_typed hq.weaken))

theorem impIntro {n : Nat} {Γ : Ctx Head n} {p q : Tm Head n} {b : Tm Head (n + 1)}
    (hp : Typed (C.rules B) Γ p C.codes.propT) (hq : Typed (C.rules B) Γ q C.codes.propT)
    (hb : Typed (C.rules B) (.snoc Γ (C.codes.holdsOf p)) b (C.codes.holdsOf (rename wk q))) :
    Typed (C.rules B) Γ (.lam b) (C.codes.holdsOf (C.codes.impOf p q)) :=
  .conv (.lamIntro (L.pi_typed (L.holdsOf_typed hp) (L.holdsOf_typed hq.weaken))
      L.proofs_universe hb)
    (.symm (L.equal_holds_imp hp hq)) L.proofs_universe

theorem impElim {n : Nat} {Γ : Ctx Head n} {p q f a : Tm Head n}
    (hp : Typed (C.rules B) Γ p C.codes.propT) (hq : Typed (C.rules B) Γ q C.codes.propT)
    (hf : Typed (C.rules B) Γ f (C.codes.holdsOf (C.codes.impOf p q)))
    (ha : Typed (C.rules B) Γ a (C.codes.holdsOf p)) :
    Typed (C.rules B) Γ (.app f a) (C.codes.holdsOf q) := by
  have h : Typed (C.rules B) Γ (.app f a) (C.codes.holdsOf (inst0 a (rename wk q))) :=
    .appElim (.conv hf (L.equal_holds_imp hp hq) L.proofs_universe) ha
  rwa [inst0_rename_wk] at h

/-! ### The two instances -/

theorem pointFormed {k : Nat} {Δ : Ctx Head k} : Typed (C.rules B) Δ (liftClosed A) C.U :=
  L.carrier_typed'

theorem predicateFormed {k : Nat} {Δ : Ctx Head k} :
    Typed (C.rules B) Δ (liftClosed (.pi A C.codes.propT)) C.U := by
  rw [C.liftClosed_predicateCarrier A]
  exact L.predType_typed

theorem point_typed {n : Nat} {Γ : Ctx Head n} :
    Typed (C.rules B) Γ (.const C.point) (.pi (C.predType A) C.codes.propT) :=
  L.all_typed L.point L.point_apart L.pointFormed

theorem pointIntro {n : Nat} {Γ : Ctx Head n} {P b : Tm Head (n + 1)}
    (hP : Typed (C.rules B) (.snoc Γ (liftClosed A)) P C.codes.propT)
    (hb : Typed (C.rules B) (.snoc Γ (liftClosed A)) b (C.codes.holdsOf P)) :
    Typed (C.rules B) Γ (.lam b) (C.codes.holdsOf (.app (.const C.point) (.lam P))) :=
  L.allIntro L.point L.point_apart L.pointFormed hP hb

theorem pointElim {n : Nat} {Γ : Ctx Head n} {P : Tm Head (n + 1)} {f a : Tm Head n}
    (hP : Typed (C.rules B) (.snoc Γ (liftClosed A)) P C.codes.propT)
    (hf : Typed (C.rules B) Γ f (C.codes.holdsOf (.app (.const C.point) (.lam P))))
    (ha : Typed (C.rules B) Γ a (liftClosed A)) :
    Typed (C.rules B) Γ (.app f a) (C.codes.holdsOf (inst0 a P)) :=
  L.allElim L.point L.point_apart L.pointFormed hP hf ha

theorem predicate_typed {n : Nat} {Γ : Ctx Head n} :
    Typed (C.rules B) Γ (.const C.predicate) (.pi (.pi (C.predType A) C.codes.propT) C.codes.propT) := by
  have h := L.all_typed (Γ := Γ) L.predicate L.predicate_apart L.predicateFormed
  rwa [C.liftClosed_predicateCarrier A] at h

theorem predicateIntro {n : Nat} {Γ : Ctx Head n} {P b : Tm Head (n + 1)}
    (hP : Typed (C.rules B) (.snoc Γ (C.predType A)) P C.codes.propT)
    (hb : Typed (C.rules B) (.snoc Γ (C.predType A)) b (C.codes.holdsOf P)) :
    Typed (C.rules B) Γ (.lam b) (C.codes.holdsOf (.app (.const C.predicate) (.lam P))) := by
  rw [← C.liftClosed_predicateCarrier A] at hP hb
  exact L.allIntro L.predicate L.predicate_apart L.predicateFormed hP hb

theorem predicateElim {n : Nat} {Γ : Ctx Head n} {P : Tm Head (n + 1)} {f X : Tm Head n}
    (hP : Typed (C.rules B) (.snoc Γ (C.predType A)) P C.codes.propT)
    (hf : Typed (C.rules B) Γ f (C.codes.holdsOf (.app (.const C.predicate) (.lam P))))
    (hX : Typed (C.rules B) Γ X (C.predType A)) :
    Typed (C.rules B) Γ (.app f X) (C.codes.holdsOf (inst0 X P)) := by
  rw [← C.liftClosed_predicateCarrier A] at hP hX
  exact L.allElim L.predicate L.predicate_apart L.predicateFormed hP hf hX

/-! ### The codes are codes -/

omit L in
theorem var_zero {n : Nat} {Γ : Ctx Head n} {X : Tm Head n} :
    Typed (C.rules B) (.snoc Γ X) (.var 0) (rename wk X) := by
  simpa only [Ctx.lookup_snoc_zero] using Derivable.var (R := C.rules B) (Γ := .snoc Γ X) 0

omit L in
theorem var_carrier {n : Nat} {Γ : Ctx Head n} :
    Typed (C.rules B) (.snoc Γ (liftClosed A)) (.var 0) (liftClosed A) := by
  simpa only [rename_liftClosed] using var_zero (C := C) (B := B) (Γ := Γ) (X := liftClosed A)

omit L in
theorem var_predicate {n : Nat} {Γ : Ctx Head n} :
    Typed (C.rules B) (.snoc Γ (C.predType A)) (.var 0) (C.predType A) := by
  simpa only [CodeNames.rename_predType] using var_zero (C := C) (B := B) (Γ := Γ) (X := C.predType A)

omit L in
theorem relOf_typed {n : Nat} {Γ : Ctx Head n} {R y x : Tm Head n}
    (hR : Typed (C.rules B) Γ R (C.relType A)) (hy : Typed (C.rules B) Γ y (liftClosed A))
    (hx : Typed (C.rules B) Γ x (liftClosed A)) :
    Typed (C.rules B) Γ (CodeNames.relOf R y x) C.codes.propT := by
  have h₁ := Derivable.appElim hR hy
  simp only [inst0, Presentation.subst, subst_liftClosed] at h₁
  exact .appElim h₁ hx

omit L in
theorem predOf_typed {n : Nat} {Γ : Ctx Head n} {X y : Tm Head n}
    (hX : Typed (C.rules B) Γ X (C.predType A)) (hy : Typed (C.rules B) Γ y (liftClosed A)) :
    Typed (C.rules B) Γ (.app X y) C.codes.propT :=
  .appElim hX hy

theorem below_typed {n : Nat} {Γ : Ctx Head n} {R X x : Tm Head n}
    (hR : Typed (C.rules B) Γ R (C.relType A)) (hX : Typed (C.rules B) Γ X (C.predType A))
    (hx : Typed (C.rules B) Γ x (liftClosed A)) :
    Typed (C.rules B) Γ (C.below R X x) C.codes.propT := by
  refine .appElim L.point_typed (.lamIntro (L.pi_typed L.carrier_typed' L.prop_typed)
    L.proofs_universe ?_)
  refine L.impOf_typed (relOf_typed ?_ var_carrier ?_) (predOf_typed ?_ var_carrier)
  · simpa only [CodeNames.rename_relType] using hR.weaken (extension := liftClosed A)
  · simpa only [rename_liftClosed] using hx.weaken (extension := liftClosed A)
  · simpa only [CodeNames.rename_predType] using hX.weaken (extension := liftClosed A)

theorem progressive_typed {n : Nat} {Γ : Ctx Head n} {R X : Tm Head n}
    (hR : Typed (C.rules B) Γ R (C.relType A)) (hX : Typed (C.rules B) Γ X (C.predType A)) :
    Typed (C.rules B) Γ (C.progressive R X) C.codes.propT := by
  have hR' : Typed (C.rules B) (.snoc Γ (liftClosed A)) (rename wk R) (C.relType A) := by
    simpa only [CodeNames.rename_relType] using hR.weaken (extension := liftClosed A)
  have hX' : Typed (C.rules B) (.snoc Γ (liftClosed A)) (rename wk X) (C.predType A) := by
    simpa only [CodeNames.rename_predType] using hX.weaken (extension := liftClosed A)
  refine .appElim L.point_typed (.lamIntro (L.pi_typed L.carrier_typed' L.prop_typed)
    L.proofs_universe ?_)
  exact L.impOf_typed (L.below_typed hR' hX' var_carrier) (predOf_typed hX' var_carrier)

theorem acc_typed {n : Nat} {Γ : Ctx Head n} {R a : Tm Head n}
    (hR : Typed (C.rules B) Γ R (C.relType A)) (ha : Typed (C.rules B) Γ a (liftClosed A)) :
    Typed (C.rules B) Γ (C.acc R a) C.codes.propT := by
  have hR' : Typed (C.rules B) (.snoc Γ (C.predType A)) (rename wk R) (C.relType A) := by
    simpa only [CodeNames.rename_relType] using hR.weaken (extension := C.predType A)
  have ha' : Typed (C.rules B) (.snoc Γ (C.predType A)) (rename wk a) (liftClosed A) := by
    simpa only [rename_liftClosed] using ha.weaken (extension := C.predType A)
  refine .appElim L.predicate_typed (.lamIntro (L.pi_typed L.predType_typed L.prop_typed)
    L.proofs_universe ?_)
  exact L.impOf_typed (L.progressive_typed hR' var_predicate)
    (predOf_typed var_predicate ha')

theorem accBelow_typed {n : Nat} {Γ : Ctx Head n} {R a : Tm Head n}
    (hR : Typed (C.rules B) Γ R (C.relType A)) (ha : Typed (C.rules B) Γ a (liftClosed A)) :
    Typed (C.rules B) Γ (C.accBelow R a) C.codes.propT := by
  have hR' : Typed (C.rules B) (.snoc Γ (liftClosed A)) (rename wk R) (C.relType A) := by
    simpa only [CodeNames.rename_relType] using hR.weaken (extension := liftClosed A)
  have ha' : Typed (C.rules B) (.snoc Γ (liftClosed A)) (rename wk a) (liftClosed A) := by
    simpa only [rename_liftClosed] using ha.weaken (extension := liftClosed A)
  refine .appElim L.point_typed (.lamIntro (L.pi_typed L.carrier_typed' L.prop_typed)
    L.proofs_universe ?_)
  exact L.impOf_typed (relOf_typed hR' var_carrier ha') (L.acc_typed hR' var_carrier)

end CodeNames.Laws

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion
