import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReadingCompile
import Mettapedia.Logic.HOL.PublishedFacts

/-!
# The published facts of a reading, realized in the selected judgment

Under the laws of a reading (the identity reading), the facts a proof library
publishes are realized by closed terms of the reading's package, typed at the
decoding of the codes of their formulas:

* reflexivity at every type by `λx. refl x` (`Laws.refl_typed`);
* substitution at every type by an identity eliminator of the package at the
  code motive `λ y p. holds (P y)` (`Laws.substRealization_typed`). The
  eliminator is given by its typing rule into the universe of proofs and a
  universe of motives above it (`IdentityEliminator`);
* η at every function type by `λf. refl f`, through typed η for functions
  (`Laws.etaRealization_typed`);
* the universal closure of a realized defining equation by `λx⃗. refl l`,
  through its root step (`Laws.equationRealization_typed`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative

open Normalization
open Mettapedia.Logic

universe u v

variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- `J A x M d y e`. -/
def jSpine {n : Nat} (J : DeclName) (A x M d y e : Tm Head n) : Tm Head n :=
  .app (.app (.app (.app (.app (.app (.const J) A) x) M) d) y) e

namespace HOLReading

/-- A universe of motives above the universe of proofs: it holds the universe
of proofs as a term, contains the types of proofs, and is closed under function
types. Motives of eliminators into proofs live there. -/
structure MotiveUniverse (ρ : HOLReading Head Base Const) : Prop where
  exists_universe : ∃ m, ρ.rules.isUniverse m ∧ ρ.rules.headTyping ρ.codes.proofs m ∧
    ρ.rules.cumulative ρ.codes.proofs m ∧ ∃ w, ρ.rules.join m m w ∧ ρ.rules.cumulative w m

/-- An identity eliminator of the package of a reading, into the universe of
proofs: its name and its typing rule. -/
structure IdentityEliminator (ρ : HOLReading Head Base Const) where
  name : DeclName
  /-- `J A x M d y e : M y e`. -/
  typed : ∀ {n : Nat} {Γ : Ctx Head n} {A x M d y e : Tm Head n},
    Typed ρ.rules Γ A ρ.U → Typed ρ.rules Γ x A →
    Typed ρ.rules Γ M
      (.pi A (.pi (.id (Presentation.rename wk A) (Presentation.rename wk x) (.var 0)) ρ.U)) →
    Typed ρ.rules Γ d (.app (.app M x) (.refl x)) → Typed ρ.rules Γ y A →
    Typed ρ.rules Γ e (.id A x y) →
    Typed ρ.rules Γ (jSpine name A x M d y e) (.app (.app M y) e)

namespace MotiveUniverse

variable {ρ : HOLReading Head Base Const}

/-- The formation rules of the universe of motives. -/
theorem formation (M : ρ.MotiveUniverse) : ∃ m, ρ.rules.isUniverse m ∧
    (∀ {n : Nat} {Γ : Ctx Head n}, Typed ρ.rules Γ ρ.U (.head m)) ∧
    (∀ {n : Nat} {Γ : Ctx Head n} {X : Tm Head n}, Typed ρ.rules Γ X ρ.U →
      Typed ρ.rules Γ X (.head m)) ∧
    (∀ {n : Nat} {Γ : Ctx Head n} {X : Tm Head n} {Y : Tm Head (n + 1)},
      Typed ρ.rules Γ X (.head m) → Typed ρ.rules (.snoc Γ X) Y (.head m) →
      Typed ρ.rules Γ (.pi X Y) (.head m)) := by
  obtain ⟨m, hm, ht, hc, w, hj, hw⟩ := M.exists_universe
  exact ⟨m, hm, fun {_ _} => .headType ht, fun h => .cumul h hc,
    fun hX hY => .cumul (.piForm hX hm hY hm hj) hw⟩

end MotiveUniverse

section Codes

variable (ρ : HOLReading Head Base Const)

/-- The code of `∀x. x = x`. -/
def reflCode (τ : HOL.Ty Base) : Tm Head 0 :=
  ρ.allOf τ (.lam (ρ.eqOf τ (.var 0) (.var 0)))

/-- The code of `∀P x y. x = y ⇒ P x ⇒ P y`. -/
def substCode (τ : HOL.Ty Base) : Tm Head 0 :=
  ρ.allOf (.arr τ .prop) (.lam (ρ.allOf τ (.lam (ρ.allOf τ (.lam
    (ρ.impOf (ρ.eqOf τ (.var 1) (.var 0))
      (ρ.impOf (.app (.var 2) (.var 1)) (.app (.var 2) (.var 0)))))))))

/-- The code of `∀f. (λx. f x) = f`. -/
def etaCode (σ τ : HOL.Ty Base) : Tm Head 0 :=
  ρ.allOf (.arr σ τ) (.lam (ρ.eqOf (.arr σ τ) (.lam (.app (.var 1) (.var 0))) (.var 0)))

theorem term_reflexivityFormula (τ : HOL.Ty Base) :
    ρ.term (HOL.reflexivityFormula (Const := Const) τ) = some (ρ.reflCode τ) := rfl

theorem term_substitutionFormula (τ : HOL.Ty Base) :
    ρ.term (HOL.substitutionFormula (Const := Const) τ) = some (ρ.substCode τ) := rfl

theorem term_etaFormula (σ τ : HOL.Ty Base) :
    ρ.term (HOL.etaFormula (Const := Const) σ τ) = some (ρ.etaCode σ τ) := rfl

/-- `λ y p. holds (P y)`, under the five binders `P x y e h`. -/
def substMotive : Tm Head 5 := .lam (.lam (ρ.holdsOf (.app (.var 6) (.var 1))))

/-- `λ P x y e h. J A x (λ y p. holds (P y)) h y e`, at the carrier `A` of `τ`. -/
def substRealization (J : DeclName) (τ : HOL.Ty Base) : Tm Head 0 :=
  .lam (.lam (.lam (.lam (.lam
    (jSpine J (ρ.carrierAt 5 τ) (.var 3) ρ.substMotive (.var 0) (.var 2) (.var 1))))))

/-- `λ x⃗. b`, over a source context, the oldest variable outermost. -/
def closeLams : (Θ : HOL.Ctx Base) → Tm Head Θ.length → Tm Head 0
  | [], b => b
  | _ :: Θ, b => closeLams Θ (.lam b)

/-- `λ x⃗. refl l`, for an equation `l = r`. -/
def equationRealization (equation : HOL.DefiningEquation Const) : Tm Head 0 :=
  closeLams equation.context (.refl ((ρ.term equation.left).getD (.const .anonymous)))

theorem term_closeAll : ∀ (Θ : HOL.Ctx Base) {φ : HOL.Formula Const Θ} {c : Tm Head Θ.length},
    ρ.term φ = some c → ∃ c', ρ.term (HOL.closeAll Θ φ) = some c'
  | [], _, _, h => ⟨_, h⟩
  | τ :: Θ, φ, c, h => term_closeAll Θ (φ := .all (σ := τ) φ) (c := ρ.allOf τ (.lam c))
      (by simp [term, h])

end Codes

/-- A variable of a carrier, seen past one more binder. -/
theorem var_weaken_carrier (ρ : HOLReading Head Base Const) {n : Nat} {Γ : Ctx Head n}
    {i : Fin n} {τ : HOL.Ty Base} {X : Tm Head n}
    (h : Typed ρ.rules Γ (.var i) (ρ.carrierAt n τ)) :
    Typed ρ.rules (.snoc Γ X) (.var i.succ) (ρ.carrierAt (n + 1) τ) := by
  simpa only [rename_carrierAt, Presentation.rename, wk] using h.weaken (extension := X)

/-- Two β-steps into a code-valued family of two arguments. -/
theorem betaTwo {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {M : Tm Head (n + 2)} {a b : Tm Head n} {U w : Head}
    (formed : Typed R Γ (.pi A (.pi B (.head U))) (.head w)) (hw : R.isUniverse w)
    (formed₂ : Typed R (.snoc Γ A) (.pi B (.head U)) (.head w))
    (body : Typed R (.snoc (.snoc Γ A) B) M (.head U))
    (ta : Typed R Γ a A) (tb : Typed R Γ b (inst0 a B)) :
    Equal R Γ (.app (.app (.lam (.lam M)) a) b)
      (inst0 b (Presentation.subst (liftSub (subst0 a)) M)) (.head U) := by
  have lamM : Typed R (.snoc Γ A) (.lam M) (.pi B (.head U)) := .lamIntro formed₂ hw body
  have e₁ := Derivable.betaPi formed hw lamM ta
  have e₂ : Equal R Γ (.app (.app (.lam (.lam M)) a) b) (.app (inst0 a (.lam M)) b)
      (inst0 b (.head U)) :=
    Derivable.appCong (A := inst0 a B) (B := .head U) e₁ (.refl tb)
  have formedInst : Typed R Γ (.pi (inst0 a B) (.head U)) (.head w) :=
    Typed.substitute formed₂ (SubstMor.single ta)
  have bodyInst : Typed R (.snoc Γ (inst0 a B)) (Presentation.subst (liftSub (subst0 a)) M)
      (.head U) :=
    Typed.substitute body (SubstMor.lift (SubstMor.single ta) B)
  exact .trans e₂ (Derivable.betaPi formedInst hw bodyInst tb)

namespace Laws

variable {ρ : HOLReading Head Base Const} (L : ρ.Laws)
include L

/-! ## Substitution -/

/-- **Substitution** at every carrier, by the identity eliminator at the code
motive `λ y p. holds (P y)`. -/
theorem substRealization_typed (M : ρ.MotiveUniverse) (J : IdentityEliminator ρ)
    (τ : HOL.Ty Base) :
    Typed ρ.rules .nil (ρ.substRealization J.name τ) (ρ.holdsOf (ρ.substCode τ)) := by
  let C : (k : Nat) → Tm Head k := fun k => ρ.carrierAt k τ
  let Θ1 : Ctx Head 1 := .snoc .nil (ρ.carrierAt 0 (.arr τ .prop))
  let Θ2 : Ctx Head 2 := .snoc Θ1 (C 1)
  let Θ3 : Ctx Head 3 := .snoc Θ2 (C 2)
  let Θ4 : Ctx Head 4 := .snoc Θ3 (ρ.holdsOf (ρ.eqOf τ (.var 1) (.var 0)))
  let Θ5 : Ctx Head 5 := .snoc Θ4 (ρ.holdsOf (.app (.var 3) (.var 2)))
  -- the variables
  have P1 : Typed ρ.rules Θ1 (.var 0) (ρ.carrierAt 1 (.arr τ .prop)) :=
    ρ.var_carrier (.arr τ .prop)
  have P3 : Typed ρ.rules Θ3 (.var 2) (ρ.carrierAt 3 (.arr τ .prop)) :=
    var_weaken_carrier ρ (var_weaken_carrier ρ P1)
  have x2 : Typed ρ.rules Θ2 (.var 0) (C 2) := ρ.var_carrier τ
  have x3 : Typed ρ.rules Θ3 (.var 1) (C 3) := var_weaken_carrier ρ x2
  have y3 : Typed ρ.rules Θ3 (.var 0) (C 3) := ρ.var_carrier τ
  have P5 : Typed ρ.rules Θ5 (.var 4) (ρ.carrierAt 5 (.arr τ .prop)) :=
    var_weaken_carrier ρ (var_weaken_carrier ρ P3)
  have x5 : Typed ρ.rules Θ5 (.var 3) (C 5) := var_weaken_carrier ρ (var_weaken_carrier ρ x3)
  have y5 : Typed ρ.rules Θ5 (.var 2) (C 5) := var_weaken_carrier ρ (var_weaken_carrier ρ y3)
  -- the codes
  have eq3 : Typed ρ.rules Θ3 (ρ.eqOf τ (.var 1) (.var 0)) ρ.codes.propT := L.eqOf_typed x3 y3
  have imp3 : Typed ρ.rules Θ3
      (ρ.impOf (.app (.var 2) (.var 1)) (.app (.var 2) (.var 0))) ρ.codes.propT :=
    L.impOf_typed (app_carrier (τ := .prop) P3 x3) (app_carrier (τ := .prop) P3 y3)
  have body3 : Typed ρ.rules Θ3 (ρ.impOf (ρ.eqOf τ (.var 1) (.var 0))
      (ρ.impOf (.app (.var 2) (.var 1)) (.app (.var 2) (.var 0)))) ρ.codes.propT :=
    L.impOf_typed eq3 imp3
  have code2 := L.allOf_typed (τ := τ) (.lamIntro (L.pi_typed (L.carrierAt_typed τ) L.prop_typed)
    L.proofs_universe body3)
  have P4 : Typed ρ.rules Θ4 (.var 3) (ρ.carrierAt 4 (.arr τ .prop)) := var_weaken_carrier ρ P3
  have x4 : Typed ρ.rules Θ4 (.var 2) (C 4) := var_weaken_carrier ρ x3
  have y4 : Typed ρ.rules Θ4 (.var 1) (C 4) := var_weaken_carrier ρ y3
  -- the motive universe
  obtain ⟨m, hm, U_typed, raise, piM⟩ := M.formation
  -- the eliminator at the code motive
  have C6 : Presentation.rename wk (C 5) = C 6 := rename_carrierAt ρ _ _
  have motiveBody : Typed ρ.rules
      (.snoc (.snoc Θ5 (C 5)) (.id (C 6) (.var 4) (.var 0)))
      (ρ.holdsOf (.app (.var 6) (.var 1))) ρ.U := by
    have P7 : Typed ρ.rules (.snoc (.snoc Θ5 (C 5)) (.id (C 6) (.var 4) (.var 0))) (.var 6)
        (ρ.carrierAt 7 (.arr τ .prop)) := var_weaken_carrier ρ (var_weaken_carrier ρ P5)
    have y7 : Typed ρ.rules (.snoc (.snoc Θ5 (C 5)) (.id (C 6) (.var 4) (.var 0))) (.var 1)
        (C 7) := var_weaken_carrier ρ (ρ.var_carrier τ)
    exact L.holdsOf_typed (app_carrier (τ := .prop) P7 y7)
  have x6 : Typed ρ.rules (.snoc Θ5 (C 5)) (.var 4) (C 6) := var_weaken_carrier ρ x5
  have y6 : Typed ρ.rules (.snoc Θ5 (C 5)) (.var 0) (C 6) := ρ.var_carrier τ
  have formed₂ : Typed ρ.rules (.snoc Θ5 (C 5)) (.pi (.id (C 6) (.var 4) (.var 0)) ρ.U)
      (.head m) :=
    piM (raise (.idForm (L.carrierAt_typed τ) L.proofs_universe x6 y6)) U_typed
  have formed : Typed ρ.rules Θ5 (.pi (C 5) (.pi (.id (C 6) (.var 4) (.var 0)) ρ.U))
      (.head m) :=
    piM (raise (L.carrierAt_typed τ)) formed₂
  have motive : Typed ρ.rules Θ5 ρ.substMotive
      (.pi (C 5) (.pi (.id (C 6) (.var 4) (.var 0)) ρ.U)) :=
    .lamIntro formed hm (.lamIntro formed₂ hm motiveBody)
  have reflAt : Typed ρ.rules Θ5 (.refl (.var 3)) (inst0 (.var 3) (.id (C 6) (.var 4) (.var 0))) := by
    have h : inst0 (.var 3) (.id (C 6) (.var 4) (.var 0)) = (.id (C 5) (.var 3) (.var 3) : Tm Head 5) := by
      simp only [inst0, Presentation.subst, C, subst_carrierAt]
      rfl
    rw [h]
    exact .reflIntro x5
  have method : Typed ρ.rules Θ5 (.var 0) (.app (.app ρ.substMotive (.var 3)) (.refl (.var 3))) :=
    .conv (.var 0) (.symm (betaTwo formed hm formed₂ motiveBody x5 reflAt))
      L.proofs_universe
  have path : Typed ρ.rules Θ5 (.var 1) (.id (C 5) (.var 3) (.var 2)) :=
    .conv (.var 1) (L.equal_holds_eq x5 y5) L.proofs_universe
  have pathAt : Typed ρ.rules Θ5 (.var 1) (inst0 (.var 2) (.id (C 6) (.var 4) (.var 0))) := by
    have h : inst0 (.var 2) (.id (C 6) (.var 4) (.var 0)) = (.id (C 5) (.var 3) (.var 2) : Tm Head 5) := by
      simp only [inst0, Presentation.subst, C, subst_carrierAt]
      rfl
    rw [h]
    exact path
  have eliminated := J.typed (L.carrierAt_typed τ) x5 (by rw [C6]; exact motive) method y5 path
  have body5 : Typed ρ.rules Θ5 (jSpine J.name (C 5) (.var 3) ρ.substMotive (.var 0) (.var 2) (.var 1))
      (ρ.holdsOf (.app (.var 4) (.var 2))) :=
    .conv eliminated (betaTwo formed hm formed₂ motiveBody y5 pathAt)
      L.proofs_universe
  have body4 : Typed ρ.rules Θ4
      (.lam (jSpine J.name (C 5) (.var 3) ρ.substMotive (.var 0) (.var 2) (.var 1)))
      (ρ.holdsOf (ρ.impOf (.app (.var 3) (.var 2)) (.app (.var 3) (.var 1)))) :=
    L.impIntro (app_carrier (τ := .prop) P4 x4) (app_carrier (τ := .prop) P4 y4) body5
  have body3' := L.impIntro eq3 imp3 body4
  have body2' := L.allIntro (τ := τ) body3 body3'
  have body1' := L.allIntro (τ := τ) code2 body2'
  exact L.allIntro (τ := .arr τ .prop)
    (L.allOf_typed (τ := τ) (.lamIntro (L.pi_typed (L.carrierAt_typed τ) L.prop_typed)
      L.proofs_universe code2)) body1'

/-! ## η -/

/-- **η** at every function carrier: `λf. refl f` proves `∀f. (λx. f x) = f`. -/
theorem etaRealization_typed (σ τ : HOL.Ty Base) :
    Typed ρ.rules .nil (.lam (.refl (.var 0))) (ρ.holdsOf (ρ.etaCode σ τ)) := by
  let Γ1 : Ctx Head 1 := .snoc .nil (ρ.carrierAt 0 (.arr σ τ))
  have f1 : Typed ρ.rules Γ1 (.var 0) (ρ.carrierAt 1 (.arr σ τ)) := ρ.var_carrier (.arr σ τ)
  -- `λx. f x : σ → τ`
  have f2 : Typed ρ.rules (.snoc Γ1 (ρ.carrierAt 1 σ)) (.var 1) (ρ.carrierAt 2 (.arr σ τ)) :=
    var_weaken_carrier ρ f1
  have x2 : Typed ρ.rules (.snoc Γ1 (ρ.carrierAt 1 σ)) (.var 0) (ρ.carrierAt 2 σ) := ρ.var_carrier σ
  have app2 : Typed ρ.rules (.snoc Γ1 (ρ.carrierAt 1 σ)) (.app (.var 1) (.var 0))
      (ρ.carrierAt 2 τ) := app_carrier f2 x2
  have expanded : Typed ρ.rules Γ1 (.lam (.app (.var 1) (.var 0))) (ρ.carrierAt 1 (.arr σ τ)) :=
    L.lam_carrier app2
  -- η: `λx. f x ≡ f`
  have lifted : Typed ρ.rules (.snoc (.snoc Γ1 (ρ.carrierAt 1 σ)) (ρ.carrierAt 2 σ))
      (.app (.var 2) (.var 0)) (ρ.carrierAt 3 τ) :=
    app_carrier (var_weaken_carrier ρ f2) (ρ.var_carrier σ)
  have beta : Equal ρ.rules (.snoc Γ1 (ρ.carrierAt 1 σ))
      (.app (.lam (.app (.var 2) (.var 0))) (.var 0)) (.app (.var 1) (.var 0)) (ρ.carrierAt 2 τ) := by
    have e := Derivable.betaPi (L.carrierAt_typed (.arr σ τ)) L.proofs_universe lifted x2
    simp only [inst0_carrierAt] at e
    exact e
  have eta : Equal ρ.rules Γ1 (.lam (.app (.var 1) (.var 0))) (.var 0) (ρ.carrierAt 1 (.arr σ τ)) :=
    Derivable.etaPi expanded f1 beta
  -- `refl f : Id (λx. f x) f`
  have reflF : Typed ρ.rules Γ1 (.refl (.var 0))
      (.id (ρ.carrierAt 1 (.arr σ τ)) (.lam (.app (.var 1) (.var 0))) (.var 0)) :=
    .conv (.reflIntro f1) (.idCong (.refl (L.carrierAt_typed (.arr σ τ))) L.proofs_universe
      (.symm eta) (.refl f1)) L.proofs_universe
  have coded : Typed ρ.rules Γ1 (.refl (.var 0))
      (ρ.holdsOf (ρ.eqOf (.arr σ τ) (.lam (.app (.var 1) (.var 0))) (.var 0))) :=
    .conv reflF (.symm (L.equal_holds_eq expanded f1)) L.proofs_universe
  exact L.allIntro (τ := .arr σ τ) (L.eqOf_typed expanded f1) coded

/-! ## Defining equations -/

/-- Abstraction over a source context: a proof in the object context of `Θ` of
the decoding of the code of `φ` closes to a proof of the decoding of the code
of `∀x⃗. φ`. -/
theorem closeAll_typed : ∀ (Θ : HOL.Ctx Base) {φ : HOL.Formula Const Θ} {c : Tm Head Θ.length}
    {b : Tm Head Θ.length}, ρ.term φ = some c → Typed ρ.rules (ρ.objCtx Θ) b (ρ.holdsOf c) →
      ∃ c', ρ.term (HOL.closeAll Θ φ) = some c' ∧
        Typed ρ.rules .nil (closeLams Θ b) (ρ.holdsOf c')
  | [], _, _, _, h, typed => ⟨_, h, typed⟩
  | τ :: Θ, φ, c, b, h, typed =>
      closeAll_typed Θ (φ := .all (σ := τ) φ) (c := ρ.allOf τ (.lam c)) (b := .lam b)
        (by simp [term, h]) (L.allIntro (L.term_typed h) typed)

/-- **Defining equations.** The universal closure of a realized defining
equation is proved by `λx⃗. refl l`, through its root step. -/
theorem equationRealization_typed {eqs : List (HOL.DefiningEquation Const)}
    (R : ρ.Realizes eqs) {equation : HOL.DefiningEquation Const} (listed : equation ∈ eqs) :
    ∃ code, ρ.term equation.closedFormula = some code ∧
      Typed ρ.rules .nil (ρ.equationRealization equation) (ρ.holdsOf code) := by
  obtain ⟨l, r, hl, hr, roots⟩ := R equation listed
  have tl := L.term_typed hl
  have tr := L.term_typed hr
  have step : ρ.base.computation.step l r := by
    simpa only [subst_ids] using roots (ids : Sub Head equation.context.length equation.context.length)
  have equal : Equal ρ.rules (ρ.objCtx equation.context) l r
      (ρ.carrierAt equation.context.length equation.type) :=
    .root (ρ.codes.extend_base_step ρ.base step) tl tr
  have reflLR : Typed ρ.rules (ρ.objCtx equation.context) (.refl l)
      (.id (ρ.carrierAt equation.context.length equation.type) l r) :=
    .conv (.reflIntro tl) (.idCong (.refl (L.carrierAt_typed _)) L.proofs_universe (.refl tl) equal)
      L.proofs_universe
  have coded : Typed ρ.rules (ρ.objCtx equation.context) (.refl l)
      (ρ.holdsOf (ρ.eqOf equation.type l r)) :=
    .conv reflLR (.symm (L.equal_holds_eq tl tr)) L.proofs_universe
  have read : ρ.term (HOL.Term.eq equation.left equation.right) = some (ρ.eqOf equation.type l r) := by
    simp only [term, hl, hr]
    rfl
  obtain ⟨code, hcode, typed⟩ := L.closeAll_typed equation.context read coded
  refine ⟨code, hcode, ?_⟩
  unfold equationRealization
  rw [hl]
  exact typed

end Laws

end HOLReading

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
