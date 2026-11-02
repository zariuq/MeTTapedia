import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipProofs
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedPoints

/-!
# Substitution in the logic of the sets, and fixed points unfolded

For the fixed-point bodies (`Formula.fixBody`: the connectives, steps and their duals, variables and fixed points), the
calculus of the package proves, with no excluded middle:

- **Transport along substitutions** (`transport`): the native formula of `φ` with the formulas `σ` substituted, read
  with the predicates `env₂`, gives the native formula of `φ` with `τ` substituted, read with `env₃`, as soon as each
  `σ i` read with `env₂` is contained in `τ i` read with `env₃`. It is the substitution lemma of the native formulas,
  with monotonicity in the predicates as its special case.
- **Fixed points unfold** (`unfoldMu`, `foldMu`, `unfoldNu`, `foldNu`): at every set, a fixed point of the closure's
  form `(μX. φ)[u]` holds exactly when its unfolding `φ[(μX. φ)[u], u]` does. Unfolding is Knaster–Tarski in the logic:
  the unfolding is a prefixed point, by transport and folding.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Ty Ctx Var Term ClosedFormula weaken rename subst instantiate Subst Rename weakenHyps)
open Mettapedia.Logic.HOL.ImpredicativeConnectives (truth falsity conjunctionFormula disjunctionFormula
  existentialInline subst_conjunctionFormula subst_disjunctionFormula subst_existentialInline)
open Mettapedia.Logic.HOL.ImpredicativeConnectives.Modulo (truthIntro conjunctionIntro conjunctionLeft
  conjunctionRight disjunctionLeft disjunctionRight disjunctionElim existentialIntro existentialElim)
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol member)
open Mettapedia.Logic.HOL.Term (isCore isCore_rename)

/-! ## Fixed-point bodies -/

/-- **Fixed-point bodies**: the connectives, steps and their duals, fixed-point variables and fixed points. -/
def _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula.fixBody : {n : ℕ} → Formula n → Bool
  | _, .top | _, .bot | _, .var _ => true
  | _, .and left right | _, .or left right => Formula.fixBody left && Formula.fixBody right
  | _, .possibly label inner | _, .necessarily label inner => !label.isContext && Formula.fixBody inner
  | _, .mu inner | _, .nu inner => Formula.fixBody inner
  | _, _ => false

theorem regional_of_fixBody : ∀ {n : ℕ} (formula : Formula n), formula.fixBody = true → formula.regional = true := by
  intro n formula body
  cases formula
  case top | bot | var => rfl
  case and left right | or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [Formula.regional, regional_of_fixBody left body.1, regional_of_fixBody right body.2, Bool.and_self]
  case possibly label inner | necessarily label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [Formula.regional, body.1, regional_of_fixBody inner body.2, Bool.and_self]
  case mu inner | nu inner =>
    simp only [Formula.fixBody] at body
    simp only [Formula.regional, regional_of_fixBody inner body]
  all_goals simp [Formula.fixBody] at body

theorem modal_of_fixBody : ∀ {n : ℕ} (formula : Formula n), formula.fixBody = true → formula.modal = true := by
  intro n formula body
  cases formula
  case top | bot | var => rfl
  case and left right | or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [Formula.modal, modal_of_fixBody left body.1, modal_of_fixBody right body.2, Bool.and_self]
  case possibly label inner | necessarily label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [Formula.modal, body.1, modal_of_fixBody inner body.2, Bool.and_self]
  case mu inner | nu inner =>
    simp only [Formula.fixBody] at body
    simp only [Formula.modal, modal_of_fixBody inner body]
  all_goals simp [Formula.fixBody] at body

theorem fixBody_rename : ∀ {n m : ℕ} (formula : Formula n) (along : Fin n → Fin m), formula.fixBody = true →
    (formula.rename along).fixBody = true := by
  intro n m formula along body
  cases formula
  case top | bot | var => rfl
  case and left right | or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [Formula.rename, Formula.fixBody, fixBody_rename left along body.1, fixBody_rename right along body.2,
      Bool.and_self]
  case possibly label inner | necessarily label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [Formula.rename, Formula.fixBody, body.1, fixBody_rename inner along body.2, Bool.and_self]
  case mu inner | nu inner =>
    simp only [Formula.fixBody] at body
    simp only [Formula.rename, Formula.fixBody, fixBody_rename inner _ body]
  all_goals simp [Formula.fixBody] at body

theorem fixBody_subst : ∀ {n m : ℕ} (formula : Formula n) (σ : Fin n → Formula m), formula.fixBody = true →
    (∀ i, (σ i).fixBody = true) → (formula.subst σ).fixBody = true := by
  intro n m formula σ body each
  cases formula
  case top | bot => rfl
  case var index => exact each index
  case and left right | or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [Formula.subst, Formula.fixBody, fixBody_subst left σ body.1 each, fixBody_subst right σ body.2 each,
      Bool.and_self]
  case possibly label inner | necessarily label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [Formula.subst, Formula.fixBody, body.1, fixBody_subst inner σ body.2 each, Bool.and_self]
  case mu inner | nu inner =>
    simp only [Formula.fixBody] at body
    refine fixBody_subst inner _ body fun i => ?_
    refine Fin.cases rfl (fun j => ?_) i
    exact fixBody_rename _ _ (each j)
  all_goals simp [Formula.fixBody] at body

/-! ## Native formulas of renamed formulas -/

section Rename

variable {Γ : Ctx Unit}

theorem native_rename : ∀ {n m : ℕ} (formula : Formula n), formula.fixBody = true → ∀ (along : Fin n → Fin m)
    {Γ : Ctx Unit} (x : Term Symbol Γ setTy) (env : Fin m → Term Symbol Γ predTy),
    nativeFormula (formula.rename along) x env = nativeFormula formula x fun i => env (along i) := by
  intro n m formula body along Γ x env
  cases formula
  case top | bot | var => rfl
  case and left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [Formula.rename, nativeFormula, native_rename left body.1, native_rename right body.2]
  case or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [Formula.rename, nativeFormula, native_rename left body.1, native_rename right body.2]
  case possibly label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [Formula.rename, nativeFormula, native_rename inner body.2]
    rfl
  case necessarily label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [Formula.rename, nativeFormula, native_rename inner body.2]
    rfl
  case mu inner =>
    simp only [Formula.fixBody] at body
    have lifted : (fun i => underFixedPoint env (liftRenaming along i)) = underFixedPoint fun i => env (along i) :=
      funext fun i => Fin.cases rfl (fun _ => rfl) i
    simp only [Formula.rename, nativeFormula, native_rename inner body, lifted]
  case nu inner =>
    simp only [Formula.fixBody] at body
    have lifted : (fun i => underFixedPoint env (liftRenaming along i)) = underFixedPoint fun i => env (along i) :=
      funext fun i => Fin.cases rfl (fun _ => rfl) i
    simp only [Formula.rename, nativeFormula, native_rename inner body, lifted]
  all_goals simp [Formula.fixBody] at body

end Rename

/-! ## Predicates of formulas and containment -/

section Predicates

variable {Γ Γ' : Ctx Unit}

/-- **The predicate of a formula** read with predicates for its variables. -/
def predOf {n : ℕ} (formula : Formula n) (env : Fin n → Term Symbol Γ predTy) : Term Symbol Γ predTy :=
  .lam (nativeFormula formula (.var .vz) (underElement env))

/-- **Containment of predicates**: `∀ w. A w → B w`. -/
def containedIn (first second : Term Symbol Γ predTy) : Term Symbol Γ .prop :=
  .all (σ := setTy) (.imp (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz)))

theorem subst_predOf (θ : Subst Symbol Γ Γ') {n : ℕ} (formula : Formula n) (regional : formula.regional = true)
    (env : Fin n → Term Symbol Γ predTy) : subst θ (predOf formula env) = predOf formula fun i => subst θ (env i) := by
  change Term.lam (subst (Subst.lift θ) (nativeFormula formula (.var .vz) (underElement env))) = _
  rw [subst_nativeFormula_regional _ formula regional, subst_underElement]
  rfl

theorem weaken_predOf {σ : Ty Unit} {n : ℕ} (formula : Formula n) (regional : formula.regional = true)
    (env : Fin n → Term Symbol Γ predTy) :
    weaken (σ := σ) (predOf formula env) = predOf formula fun i => weaken (env i) := by
  rw [weaken_eq_subst, subst_predOf _ formula regional]
  simp only [← weaken_eq_subst]

theorem subst_containedIn (θ : Subst Symbol Γ Γ') (first second : Term Symbol Γ predTy) :
    subst θ (containedIn first second) = containedIn (subst θ first) (subst θ second) := by
  change Term.all (.imp (.app (subst (Subst.lift θ) (weaken first)) (.var .vz))
    (.app (subst (Subst.lift θ) (weaken second)) (.var .vz))) = _
  rw [Mettapedia.Logic.HOL.subst_weaken, Mettapedia.Logic.HOL.subst_weaken]
  rfl

theorem weaken_containedIn {σ : Ty Unit} (first second : Term Symbol Γ predTy) :
    weaken (σ := σ) (containedIn first second) = containedIn (weaken first) (weaken second) := by
  rw [weaken_eq_subst, subst_containedIn, ← weaken_eq_subst, ← weaken_eq_subst]

theorem instantiate_predBody {n : ℕ} (formula : Formula n) (regional : formula.regional = true)
    (t : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    instantiate t (nativeFormula formula (.var .vz) (underElement env)) = nativeFormula formula t env := by
  unfold instantiate
  rw [subst_nativeFormula_regional _ formula regional, instantiate_underElement]
  rfl

theorem isCore_native : ∀ {n : ℕ} (formula : Formula n), formula.fixBody = true → ∀ {Γ : Ctx Unit}
    {x : Term Symbol Γ setTy} {env : Fin n → Term Symbol Γ predTy}, x.isCore = true → (∀ i, (env i).isCore = true) →
    (nativeFormula formula x env).isCore = true := by
  intro n formula body Γ x env coreX coreEnv
  have coreWeaken : ∀ {Γ' : Ctx Unit} {σ : Ty Unit} {τ : Ty Unit} {t : Term Symbol Γ' τ}, t.isCore = true →
      (weaken (σ := σ) t).isCore = true := fun core => by simp only [weaken, isCore_rename, core]
  cases formula
  case top | bot => rfl
  case var index => simp only [nativeFormula, isCore, coreEnv index, coreX, Bool.and_self]
  case and left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    exact isCore_conjunctionFormula (isCore_native left body.1 coreX coreEnv) (isCore_native right body.2 coreX coreEnv)
  case or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    exact isCore_disjunctionFormula (isCore_native left body.1 coreX coreEnv) (isCore_native right body.2 coreX coreEnv)
  case possibly label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [nativeFormula]
    split
    · simp only [existentialInline, isCore, isCore_rename, Bool.and_true]
      exact isCore_conjunctionFormula (isCore_member rfl (coreWeaken coreX))
        (isCore_native inner body.2 rfl fun i => coreWeaken (coreEnv i))
    · rfl
  case necessarily label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [nativeFormula]
    split
    · simp only [isCore, Bool.and_eq_true]
      exact ⟨isCore_member rfl (coreWeaken coreX), isCore_native inner body.2 rfl fun i => coreWeaken (coreEnv i)⟩
    · rfl
  case mu inner =>
    simp only [Formula.fixBody] at body
    have coreInner := isCore_native inner body (x := (.var .vz : Term Symbol (setTy :: predTy :: Γ) setTy))
      (env := underFixedPoint env) rfl fun i => Fin.cases rfl (fun j => coreWeaken (coreWeaken (coreEnv j))) i
    simp only [nativeFormula, isCore, coreInner, coreWeaken coreX, Bool.and_self]
  case nu inner =>
    simp only [Formula.fixBody] at body
    have coreInner := isCore_native inner body (x := (.var .vz : Term Symbol (setTy :: predTy :: Γ) setTy))
      (env := underFixedPoint env) rfl fun i => Fin.cases rfl (fun j => coreWeaken (coreWeaken (coreEnv j))) i
    change (existentialInline (σ := predTy) (conjunctionFormula
      (.all (σ := setTy) (.imp (.app (.var (.vs .vz)) (.var .vz)) (nativeFormula inner (.var .vz) (underFixedPoint env))))
      (.app (.var .vz) (weaken x)))).isCore = true
    simp only [existentialInline, isCore, isCore_rename]
    have first : (Term.all (σ := setTy) (.imp (.app (.var (.vs .vz)) (.var .vz))
        (nativeFormula inner (.var .vz) (underFixedPoint env)))).isCore = true := by
      simp only [isCore, coreInner, Bool.and_self]
    have second : (Term.app (.var .vz) (weaken x) : Term Symbol (predTy :: Γ) .prop).isCore = true := by
      simp only [isCore, coreWeaken coreX, Bool.and_self]
    rw [isCore_conjunctionFormula first second]
    rfl
  all_goals simp [Formula.fixBody] at body

theorem isCore_predOf {n : ℕ} {formula : Formula n} (body : formula.fixBody = true) {env : Fin n → Term Symbol Γ predTy}
    (coreEnv : ∀ i, (env i).isCore = true) : (predOf formula env).isCore = true :=
  isCore_native formula body rfl fun i => by simp only [underElement, weaken, isCore_rename, coreEnv i]

variable {Δ : List (Term Symbol Γ .prop)}

/-- Containment, at a set. -/
def containedAt {first second : Term Symbol Γ predTy} (contained : Proof Δ (containedIn first second))
    (t : Term Symbol Γ setTy) : Proof Δ (.imp (.app first t) (.app second t)) :=
  Proof.cast (by
      change Term.imp (.app (instantiate t (weaken first)) t) (.app (instantiate t (weaken second)) t) = _
      rw [Mettapedia.Logic.HOL.instantiate_weaken, Mettapedia.Logic.HOL.instantiate_weaken])
    (.allE (φ := .imp (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz))) t contained)

/-- Every predicate contains itself. -/
def containedRefl (predicate : Term Symbol Γ predTy) : Proof Δ (containedIn predicate predicate) :=
  .allI (.impI (Proof.newest _))

/-- Containment from a proof under a new set and its membership. -/
def containedIntro {first second : Term Symbol Γ predTy}
    (proof : Proof (.app (weaken first) (.var .vz) :: weakenHyps (σ := setTy) Δ) (.app (weaken second) (.var .vz))) :
    Proof Δ (containedIn first second) :=
  .allI (.impI proof)

/-- A formula's predicate applied, from the formula. -/
def predApp {n : ℕ} {formula : Formula n} (body : formula.fixBody = true) {env : Fin n → Term Symbol Γ predTy}
    (coreEnv : ∀ i, (env i).isCore = true) {t : Term Symbol Γ setTy} (coreT : t.isCore = true)
    (proof : Proof Δ (nativeFormula formula t env)) : Proof Δ (.app (predOf formula env) t) :=
  Proof.betaExpand (isCore_native formula body rfl fun i => by simp only [underElement, weaken, isCore_rename, coreEnv i])
    coreT (Proof.cast (instantiate_predBody formula (regional_of_fixBody formula body) t env).symm proof)

/-- The formula, from its predicate applied. -/
def predUnapp {n : ℕ} {formula : Formula n} (body : formula.fixBody = true) {env : Fin n → Term Symbol Γ predTy}
    (coreEnv : ∀ i, (env i).isCore = true) {t : Term Symbol Γ setTy} (coreT : t.isCore = true)
    (proof : Proof Δ (.app (predOf formula env) t)) : Proof Δ (nativeFormula formula t env) :=
  Proof.cast (instantiate_predBody formula (regional_of_fixBody formula body) t env)
    (Proof.betaReduce (isCore_native formula body rfl fun i => by simp only [underElement, weaken, isCore_rename, coreEnv i])
      coreT proof)

end Predicates

/-! ## Transport along substitutions -/

section Transport

theorem coreWeaken {Γ : Ctx Unit} {σ τ : Ty Unit} {t : Term Symbol Γ τ} (core : t.isCore = true) :
    (weaken (σ := σ) t).isCore = true := by
  simp only [weaken, isCore_rename, core]

theorem coreUnderFixedPoint {n : ℕ} {Γ : Ctx Unit} {env : Fin n → Term Symbol Γ predTy}
    (coreEnv : ∀ i, (env i).isCore = true) : ∀ i, (underFixedPoint env i).isCore = true :=
  fun i => Fin.cases rfl (fun j => coreWeaken (coreWeaken (coreEnv j))) i

/-- Containment of a substituted formula's predicates, lifted past a fixed-point binder. -/
def liftContained {n m k : ℕ} {σ : Fin n → Formula m} {τ : Fin n → Formula k}
    (bodiesσ : ∀ i, (σ i).fixBody = true) (bodiesτ : ∀ i, (τ i).fixBody = true) {Γ : Ctx Unit}
    {Δ : List (Term Symbol Γ .prop)} {env₂ : Fin m → Term Symbol Γ predTy} {env₃ : Fin k → Term Symbol Γ predTy}
    (contained : ∀ i, Proof Δ (containedIn (predOf (σ i) env₂) (predOf (τ i) env₃)))
    {Δ' : List (Term Symbol (setTy :: predTy :: Γ) .prop)}
    (lifted : ∀ {φ : Term Symbol Γ .prop}, Proof Δ φ → Proof Δ' (weaken (weaken φ))) :
    ∀ i : Fin (n + 1), Proof Δ' (containedIn (predOf (liftSubstitution σ i) (underFixedPoint env₂))
      (predOf (liftSubstitution τ i) (underFixedPoint env₃))) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact containedRefl _
  · change Proof Δ' (containedIn (predOf ((σ j).rename Fin.succ) (underFixedPoint env₂))
      (predOf ((τ j).rename Fin.succ) (underFixedPoint env₃)))
    have each := lifted (contained j)
    rw [weaken_containedIn, weaken_containedIn, weaken_predOf _ (regional_of_fixBody _ (bodiesσ j)),
      weaken_predOf _ (regional_of_fixBody _ (bodiesσ j)), weaken_predOf _ (regional_of_fixBody _ (bodiesτ j)),
      weaken_predOf _ (regional_of_fixBody _ (bodiesτ j))] at each
    unfold predOf at each ⊢
    rw [native_rename _ (bodiesσ j), native_rename _ (bodiesτ j)]
    exact each

/-- Containment of a substituted formula's predicates, lifted past an element binder. -/
def underContained {n m k : ℕ} {σ : Fin n → Formula m} {τ : Fin n → Formula k}
    (bodiesσ : ∀ i, (σ i).fixBody = true) (bodiesτ : ∀ i, (τ i).fixBody = true) {Γ : Ctx Unit}
    {Δ : List (Term Symbol Γ .prop)} {env₂ : Fin m → Term Symbol Γ predTy} {env₃ : Fin k → Term Symbol Γ predTy}
    (contained : ∀ i, Proof Δ (containedIn (predOf (σ i) env₂) (predOf (τ i) env₃)))
    {Δ' : List (Term Symbol (setTy :: Γ) .prop)} (lifted : ∀ {φ : Term Symbol Γ .prop}, Proof Δ φ → Proof Δ' (weaken φ)) :
    ∀ i, Proof Δ' (containedIn (predOf (σ i) (underElement env₂)) (predOf (τ i) (underElement env₃))) := by
  intro i
  have each := lifted (contained i)
  rw [weaken_containedIn, weaken_predOf _ (regional_of_fixBody _ (bodiesσ i)),
    weaken_predOf _ (regional_of_fixBody _ (bodiesτ i))] at each
  exact each

theorem weaken_existential {Γ : Ctx Unit} {σ τ : Ty Unit} (body : Term Symbol (τ :: Γ) .prop) :
    weaken (σ := σ) (existentialInline (σ := τ) body) = existentialInline (rename (Rename.lift Rename.weaken) body) := by
  rw [weaken_eq_subst, subst_existentialInline, rename_eq_subst]
  congr 1
  apply Mettapedia.Logic.HOL.subst_ext
  intro _ index
  cases index <;> rfl

/-- **Transport along substitutions**: `φ[σ]` read with `env₂` gives `φ[τ]` read with `env₃`, when each `σ i` read
with `env₂` is contained in `τ i` read with `env₃`. -/
def transport : ∀ {n m k : ℕ} (formula : Formula n), formula.fixBody = true →
    ∀ (σ : Fin n → Formula m) (τ : Fin n → Formula k), (∀ i, (σ i).fixBody = true) → (∀ i, (τ i).fixBody = true) →
    ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} (env₂ : Fin m → Term Symbol Γ predTy)
      (env₃ : Fin k → Term Symbol Γ predTy), (∀ i, (env₂ i).isCore = true) → (∀ i, (env₃ i).isCore = true) →
      (∀ i, Proof Δ (containedIn (predOf (σ i) env₂) (predOf (τ i) env₃))) →
      ∀ (x : Term Symbol Γ setTy), x.isCore = true →
        Proof Δ (nativeFormula (formula.subst σ) x env₂) → Proof Δ (nativeFormula (formula.subst τ) x env₃) := by
  intro n m k formula body σ τ bodiesσ bodiesτ Γ Δ env₂ env₃ core₂ core₃ contained x coreX proof
  have liftedσ : ∀ i, (liftSubstitution σ i).fixBody = true :=
    fun i => Fin.cases rfl (fun j => fixBody_rename _ _ (bodiesσ j)) i
  have liftedτ : ∀ i, (liftSubstitution τ i).fixBody = true :=
    fun i => Fin.cases rfl (fun j => fixBody_rename _ _ (bodiesτ j)) i
  cases formula
  case top => exact proof
  case bot => exact proof
  case and left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    exact conjunctionIntro
      (transport left body.1 σ τ bodiesσ bodiesτ env₂ env₃ core₂ core₃ contained x coreX (conjunctionLeft proof))
      (transport right body.2 σ τ bodiesσ bodiesτ env₂ env₃ core₂ core₃ contained x coreX (conjunctionRight proof))
  case or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    exact disjunctionElim proof
      (disjunctionLeft (transport left body.1 σ τ bodiesσ bodiesτ env₂ env₃ core₂ core₃
        (fun i => (contained i).prepend _) x coreX (Proof.newest _)))
      (disjunctionRight (transport right body.2 σ τ bodiesσ bodiesτ env₂ env₃ core₂ core₃
        (fun i => (contained i).prepend _) x coreX (Proof.newest _)))
  case var index =>
    exact predUnapp (bodiesτ index) core₃ coreX
      (.impE (containedAt (contained index) x) (predApp (bodiesσ index) core₂ coreX proof))
  case possibly label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have regionalτ := regional_of_fixBody _ (fixBody_subst inner τ body.2 bodiesτ)
    change Proof Δ (nativeFormula (.possibly label (inner.subst σ)) x env₂) at proof
    change Proof Δ (nativeFormula (.possibly label (inner.subst τ)) x env₃)
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [show nativeFormula (.possibly label (inner.subst σ)) x env₂ = existentialInline (σ := setTy)
        (conjunctionFormula (member (.var .vz) (weaken x)) (nativeFormula (inner.subst σ) (.var .vz) (underElement env₂)))
        by simp only [nativeFormula, if_pos labelled]] at proof
      refine existentialElim proof ?_
      rw [weaken_nativeFormula_regional _ (by simp only [Formula.regional, regionalτ, body.1, Bool.and_self])]
      rw [show nativeFormula (.possibly label (inner.subst τ)) (weaken x) (fun i => weaken (env₃ i)) =
        existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken (weaken x)))
          (nativeFormula (inner.subst τ) (.var .vz) (underElement fun i => weaken (env₃ i))))
        by simp only [nativeFormula, if_pos labelled]]
      refine existentialIntro (.var .vz) (Proof.cast (instantiate_possiblyBody regionalτ _ _ _).symm ?_)
      exact conjunctionIntro (conjunctionLeft (Proof.newest _))
        (transport inner body.2 σ τ bodiesσ bodiesτ (underElement env₂) (underElement env₃)
          (fun i => coreWeaken (core₂ i)) (fun i => coreWeaken (core₃ i))
          (underContained bodiesσ bodiesτ contained fun p => p.lift.prepend _) (.var .vz) rfl
          (conjunctionRight (Proof.newest _)))
    · rw [show nativeFormula (.possibly label (inner.subst σ)) x env₂ = falsity by
        simp only [nativeFormula, if_neg labelled]] at proof
      exact Proof.absurd proof
  case necessarily label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    change Proof Δ (nativeFormula (.necessarily label (inner.subst σ)) x env₂) at proof
    change Proof Δ (nativeFormula (.necessarily label (inner.subst τ)) x env₃)
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [show nativeFormula (.necessarily label (inner.subst σ)) x env₂ = .all (σ := setTy)
        (.imp (member (.var .vz) (weaken x)) (nativeFormula (inner.subst σ) (.var .vz) (underElement env₂)))
        by simp only [nativeFormula, if_pos labelled]] at proof
      rw [show nativeFormula (.necessarily label (inner.subst τ)) x env₃ = .all (σ := setTy)
        (.imp (member (.var .vz) (weaken x)) (nativeFormula (inner.subst τ) (.var .vz) (underElement env₃)))
        by simp only [nativeFormula, if_pos labelled]]
      refine .allI (.impI ?_)
      have every := Proof.atNewest (proof.lift.prepend (member (.var .vz) (weaken x)))
      exact transport inner body.2 σ τ bodiesσ bodiesτ (underElement env₂) (underElement env₃)
        (fun i => coreWeaken (core₂ i)) (fun i => coreWeaken (core₃ i))
        (underContained bodiesσ bodiesτ contained fun p => p.lift.prepend _) (.var .vz) rfl
        (.impE every (Proof.newest _))
    · rw [show nativeFormula (.necessarily label (inner.subst τ)) x env₃ = truth by
        simp only [nativeFormula, if_neg labelled]]
      exact truthIntro
  case mu inner =>
    simp only [Formula.fixBody] at body
    change Proof Δ (.all (σ := predTy) (.imp (closureHyp (inner.subst (liftSubstitution σ)) env₂)
      (.app (.var .vz) (weaken x)))) at proof
    change Proof Δ (.all (σ := predTy) (.imp (closureHyp (inner.subst (liftSubstitution τ)) env₃)
      (.app (.var .vz) (weaken x))))
    refine .allI (.impI (.impE (Proof.atNewest (proof.lift.prepend _)) ?_))
    refine .allI (.impI ?_)
    have before := Proof.atNewest (((Proof.newest (Δ := weakenHyps (σ := predTy) Δ)
      (closureHyp (inner.subst (liftSubstitution τ)) env₃)).lift (σ := setTy)).prepend
        (nativeFormula (inner.subst (liftSubstitution σ)) (.var .vz) (underFixedPoint env₂)))
    exact .impE before (transport inner body (liftSubstitution σ) (liftSubstitution τ) liftedσ liftedτ
      (underFixedPoint env₂) (underFixedPoint env₃) (coreUnderFixedPoint core₂) (coreUnderFixedPoint core₃)
      (liftContained bodiesσ bodiesτ contained fun p => ((p.lift.prepend _).lift (σ := setTy)).prepend _)
      (.var .vz) rfl (Proof.newest _))
  case nu inner =>
    simp only [Formula.fixBody] at body
    change Proof Δ (existentialInline (σ := predTy) (conjunctionFormula
      (invariantHyp (inner.subst (liftSubstitution σ)) env₂) (.app (.var .vz) (weaken x)))) at proof
    change Proof Δ (existentialInline (σ := predTy) (conjunctionFormula
      (invariantHyp (inner.subst (liftSubstitution τ)) env₃) (.app (.var .vz) (weaken x))))
    refine existentialElim proof ?_
    rw [weaken_existential]
    refine existentialIntro (.var .vz) (Proof.cast (instantiate_newest_lifted _).symm ?_)
    refine conjunctionIntro ?_ (conjunctionRight (Proof.newest _))
    refine .allI (.impI ?_)
    have after := Proof.atNewest ((Proof.lift (σ := setTy) (conjunctionLeft (Proof.newest (Δ := weakenHyps (σ := predTy) Δ)
      (conjunctionFormula (invariantHyp (inner.subst (liftSubstitution σ)) env₂) (.app (.var .vz) (weaken x)))))).prepend
        (.app (.var (.vs .vz)) (.var .vz)))
    exact transport inner body (liftSubstitution σ) (liftSubstitution τ) liftedσ liftedτ
      (underFixedPoint env₂) (underFixedPoint env₃) (coreUnderFixedPoint core₂) (coreUnderFixedPoint core₃)
      (liftContained bodiesσ bodiesτ contained fun p => ((p.lift.prepend _).lift (σ := setTy)).prepend _)
      (.var .vz) rfl (.impE after (Proof.newest _))
  all_goals exact absurd body (by simp [Formula.fixBody])

end Transport

/-! ## Fixed points unfolded -/

section Unfolding

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

theorem predOf_closed (formula : Formula 0) (first second : Fin 0 → Term Symbol Γ predTy) :
    predOf formula first = predOf formula second :=
  congrArg (predOf formula) (Subsingleton.elim _ _)

theorem native_closed {formula : Formula 0} {x : Term Symbol Γ setTy} (first second : Fin 0 → Term Symbol Γ predTy) :
    nativeFormula formula x first = nativeFormula formula x second :=
  congrArg (nativeFormula formula x) (Subsingleton.elim _ _)

theorem native_one {formula : Formula 1} {x : Term Symbol Γ setTy} (env : Fin 1 → Term Symbol Γ predTy) :
    nativeFormula formula x env = nativeFormula formula x (Fin.cons (env 0) Fin.elim0) :=
  congrArg (nativeFormula formula x) (funext fun i => Fin.cases rfl (fun j => j.elim0) i)

theorem coreElim0 : ∀ i : Fin 0, ((Fin.elim0 i : Term Symbol Γ predTy)).isCore = true := fun i => i.elim0

/-- The substitution unfolding a fixed point of the closure's form: the fixed point, then the substitution. -/
abbrev unfoldWith {n : ℕ} (fixed : Formula 0) (u : Fin n → Formula 0) : Fin (n + 1) → Formula 0 := Fin.cons fixed u

theorem unfoldWith_bodies {n : ℕ} {fixed : Formula 0} (fixedBody : fixed.fixBody = true) {u : Fin n → Formula 0}
    (bodies : ∀ i, (u i).fixBody = true) : ∀ i, (unfoldWith fixed u i).fixBody = true :=
  fun i => Fin.cases fixedBody bodies i

theorem lifted_bodies {n : ℕ} {u : Fin n → Formula 0} (bodies : ∀ i, (u i).fixBody = true) :
    ∀ i, (liftSubstitution u i).fixBody = true :=
  fun i => Fin.cases rfl (fun j => fixBody_rename _ _ (bodies j)) i

/-- A variable's predicate, read in a one-variable environment. -/
theorem predOf_var_zero {Γ' : Ctx Unit} (head : Term Symbol Γ' predTy) (tail : Fin 0 → Term Symbol Γ' predTy) :
    predOf (.var 0 : Formula 1) (Fin.cons head tail) = .lam (.app (weaken head) (.var .vz)) := rfl

/-- A renamed closed formula's predicate, read in a one-variable environment. -/
theorem predOf_rename_succ {Γ' : Ctx Unit} {formula : Formula 0} (body : formula.fixBody = true)
    (env : Fin 1 → Term Symbol Γ' predTy) (other : Fin 0 → Term Symbol Γ' predTy) :
    predOf (formula.rename Fin.succ) env = predOf formula other := by
  unfold predOf
  rw [native_rename _ body]
  exact congrArg (fun e => Term.lam (nativeFormula formula (.var .vz) e)) (Subsingleton.elim _ _)

theorem closureHyp_one {inner : Formula 1} (regional : inner.regional = true) (env : Fin 0 → Term Symbol Γ predTy) :
    weaken (σ := setTy) (closureHyp inner env) =
      .all (σ := setTy) (.imp (nativeFormula inner (.var .vz) (Fin.cons (.var (.vs (.vs .vz))) Fin.elim0))
        (.app (.var (.vs (.vs .vz))) (.var .vz))) := by
  unfold closureHyp
  rw [weaken_eq_subst]
  change Term.all (.imp (subst (Subst.lift (fun index => Term.var (Var.vs index)))
    (nativeFormula inner (.var .vz) (underFixedPoint env))) (.app (.var (.vs (.vs .vz))) (.var .vz))) = _
  rw [subst_nativeFormula_regional _ inner regional, native_one]
  rfl

theorem instantiate_muAt {inner : Formula 1} (regional : inner.regional = true) (t : Term Symbol (predTy :: Γ) setTy) :
    instantiate t (.imp (nativeFormula inner (.var .vz) (underFixedPoint (Fin.elim0 : Fin 0 → Term Symbol Γ predTy)))
      (.app (.var (.vs .vz)) (.var .vz))) =
      .imp (nativeFormula inner t (Fin.cons (.var .vz) Fin.elim0)) (.app (.var .vz) t) := by
  change Term.imp (subst (Subst.single t) (nativeFormula inner (.var .vz) (underFixedPoint Fin.elim0)))
    (.app (.var .vz) t) = _
  rw [subst_nativeFormula_regional _ inner regional, native_one]
  rfl

/-- **Folding a least fixed point**: its unfolding implies it. -/
def foldMu {n : ℕ} (inner : Formula (n + 1)) (body : inner.fixBody = true) (u : Fin n → Formula 0)
    (bodies : ∀ i, (u i).fixBody = true) {x : Term Symbol Γ setTy} (coreX : x.isCore = true)
    (proof : Proof Δ (nativeFormula (inner.subst (unfoldWith ((Formula.mu inner).subst u) u)) x Fin.elim0)) :
    Proof Δ (nativeFormula ((Formula.mu inner).subst u) x Fin.elim0) := by
  have fixedBody : ((Formula.mu inner).subst u).fixBody = true := fixBody_subst _ u body bodies
  have innerBody : (inner.subst (liftSubstitution u)).fixBody = true :=
    fixBody_subst inner _ body (lifted_bodies bodies)
  have innerRegional := regional_of_fixBody _ innerBody
  change Proof Δ (.all (σ := predTy) (.imp (closureHyp (inner.subst (liftSubstitution u)) Fin.elim0)
    (.app (.var .vz) (weaken x))))
  refine .allI (.impI ?_)
  have atX := Proof.cast (instantiate_muAt innerRegional (weaken x))
    (.allE (weaken x) (Proof.newest (Δ := weakenHyps (σ := predTy) Δ) (closureHyp (inner.subst (liftSubstitution u))
      Fin.elim0)))
  refine .impE atX ?_
  have lifted := Proof.cast ((weaken_nativeFormula_regional _ (regional_of_fixBody _
    (fixBody_subst _ _ body (unfoldWith_bodies fixedBody bodies))) x Fin.elim0).trans (native_closed _ Fin.elim0))
    (proof.lift.prepend (closureHyp (inner.subst (liftSubstitution u)) Fin.elim0))
  refine transport inner body (unfoldWith ((Formula.mu inner).subst u) u) (liftSubstitution u)
    (unfoldWith_bodies fixedBody bodies) (lifted_bodies bodies) Fin.elim0 (Fin.cons (.var .vz) Fin.elim0) coreElim0
    (fun i => Fin.cases rfl (fun j => j.elim0) i) (fun i => ?_) (weaken x) (coreWeaken coreX) lifted
  refine Fin.cases ?_ (fun j => ?_) i
  · -- the fixed point is contained in every prefixed point
    change Proof _ (containedIn (predOf ((Formula.mu inner).subst u) Fin.elim0)
      (predOf (.var 0) (Fin.cons (.var .vz) Fin.elim0)))
    rw [predOf_var_zero]
    refine containedIntro (Proof.betaExpand rfl rfl (Proof.cast (by rfl) ?_))
    have newestHyp : Proof (.app (weaken (predOf ((Formula.mu inner).subst u) Fin.elim0)) (.var .vz) ::
        weakenHyps (σ := setTy) (closureHyp (inner.subst (liftSubstitution u)) Fin.elim0 :: weakenHyps (σ := predTy) Δ))
        (.app (predOf ((Formula.mu inner).subst u) fun i => weaken (Fin.elim0 i)) (.var .vz)) :=
      Proof.cast (by rw [weaken_predOf _ (regional_of_fixBody _ fixedBody)]) (Proof.newest _)
    have fixedAt := predUnapp fixedBody (env := fun i => weaken (Fin.elim0 i)) (fun i => i.elim0)
      (t := .var .vz) rfl newestHyp
    change Proof _ (.all (σ := predTy) (.imp (closureHyp (inner.subst (liftSubstitution u)) _)
      (.app (.var .vz) (weaken (.var .vz))))) at fixedAt
    have instance' := Proof.cast (instantiate_muBody innerRegional (.var (.vs .vz)) (.var .vz) _)
      (.allE (.var (.vs .vz)) fixedAt)
    refine .impE instance' ?_
    have outer := ((Proof.newest (Δ := weakenHyps (σ := predTy) Δ) (closureHyp (inner.subst (liftSubstitution u))
      Fin.elim0)).lift (σ := setTy)).prepend (.app (weaken (predOf ((Formula.mu inner).subst u) Fin.elim0)) (.var .vz))
    rw [closureHyp_one innerRegional] at outer
    refine Proof.cast ?_ outer
    rw [native_one (Fin.cons (weaken (.var (.vs .vz))) (underElement _))]
    rfl
  · change Proof _ (containedIn (predOf (u j) Fin.elim0) (predOf ((u j).rename Fin.succ) (Fin.cons (.var .vz) Fin.elim0)))
    rw [predOf_rename_succ (bodies j) _ Fin.elim0]
    exact containedRefl _

/-- A one-variable predicate, applied after weakening, read back. -/
theorem lam_weaken_app {Γ' : Ctx Unit} (head : Term Symbol Γ' predTy) :
    instantiate (.var .vz) (rename (Rename.lift Rename.weaken)
      (Term.app (weaken head) (.var .vz) : Term Symbol (setTy :: Γ') .prop)) = .app (weaken head) (.var .vz) :=
  instantiate_newest_lifted _

theorem isCore_app_weaken {Γ' : Ctx Unit} {head : Term Symbol Γ' predTy} (core : head.isCore = true) :
    (Term.app (weaken (σ := setTy) head) (.var .vz) : Term Symbol (setTy :: Γ') .prop).isCore = true := by
  simp only [isCore, coreWeaken core, Bool.and_self]

/-- **Unfolding a least fixed point**: it implies its unfolding, Knaster–Tarski: the unfolding is a prefixed point. -/
def unfoldMu {n : ℕ} (inner : Formula (n + 1)) (body : inner.fixBody = true) (u : Fin n → Formula 0)
    (bodies : ∀ i, (u i).fixBody = true) {x : Term Symbol Γ setTy} (coreX : x.isCore = true)
    (proof : Proof Δ (nativeFormula ((Formula.mu inner).subst u) x Fin.elim0)) :
    Proof Δ (nativeFormula (inner.subst (unfoldWith ((Formula.mu inner).subst u) u)) x Fin.elim0) := by
  have fixedBody : ((Formula.mu inner).subst u).fixBody = true := fixBody_subst _ u body bodies
  have innerBody : (inner.subst (liftSubstitution u)).fixBody = true :=
    fixBody_subst inner _ body (lifted_bodies bodies)
  have innerRegional := regional_of_fixBody _ innerBody
  have unfoldedBody : (inner.subst (unfoldWith ((Formula.mu inner).subst u) u)).fixBody = true :=
    fixBody_subst _ _ body (unfoldWith_bodies fixedBody bodies)
  have unfoldedRegional := regional_of_fixBody _ unfoldedBody
  let Q : Term Symbol Γ predTy := predOf (inner.subst (unfoldWith ((Formula.mu inner).subst u) u)) Fin.elim0
  have coreQ : Q.isCore = true := isCore_predOf unfoldedBody coreElim0
  change Proof Δ (.all (σ := predTy) (.imp (closureHyp (inner.subst (liftSubstitution u)) Fin.elim0)
    (.app (.var .vz) (weaken x)))) at proof
  have inst := Proof.cast (instantiate_muBody innerRegional Q x Fin.elim0) (.allE Q proof)
  have weakQ : weaken (σ := setTy) Q = predOf (inner.subst (unfoldWith ((Formula.mu inner).subst u) u))
      (fun i => weaken (Fin.elim0 i)) := weaken_predOf _ unfoldedRegional _
  have weakWeakQ : weaken (σ := setTy) (weaken (σ := setTy) Q) =
      predOf (inner.subst (unfoldWith ((Formula.mu inner).subst u) u)) (fun i => weaken (weaken (Fin.elim0 i))) := by
    rw [weakQ, weaken_predOf _ unfoldedRegional]
  refine predUnapp unfoldedBody coreElim0 coreX (.impE inst (.allI (.impI ?_)))
  refine Proof.cast (congrArg (fun p => Term.app p (.var .vz)) weakQ.symm)
    (predApp unfoldedBody (env := fun i => weaken (Fin.elim0 i)) (fun i => i.elim0) rfl ?_)
  refine transport inner body (liftSubstitution u) (unfoldWith ((Formula.mu inner).subst u) u) (lifted_bodies bodies)
    (unfoldWith_bodies fixedBody bodies) (Fin.cons (weaken Q) (underElement Fin.elim0)) (fun i => weaken (Fin.elim0 i))
    (fun i => Fin.cases (coreWeaken coreQ) (fun j => j.elim0) i) (fun i => i.elim0) (fun i => ?_) (.var .vz) rfl
    (Proof.newest _)
  refine Fin.cases ?_ (fun j => ?_) i
  · change Proof _ (containedIn (predOf (.var 0) (Fin.cons (weaken Q) (underElement Fin.elim0)))
      (predOf ((Formula.mu inner).subst u) fun i => weaken (Fin.elim0 i)))
    rw [predOf_var_zero]
    refine containedIntro ?_
    rw [weaken_predOf _ (regional_of_fixBody _ fixedBody)]
    refine predApp fixedBody (fun i => i.elim0) rfl ?_
    refine Proof.cast (native_closed _ _) (foldMu inner body u bodies rfl ?_)
    refine Proof.cast (native_closed _ _)
      (predUnapp unfoldedBody (env := fun i => weaken (weaken (Fin.elim0 i))) (fun i => i.elim0) rfl ?_)
    exact Proof.cast ((lam_weaken_app (weaken Q)).trans (congrArg (fun p => Term.app p (.var .vz)) weakWeakQ))
      (Proof.betaReduce (by rw [isCore_rename]; exact isCore_app_weaken (coreWeaken coreQ)) rfl (Proof.newest _))
  · change Proof _ (containedIn (predOf ((u j).rename Fin.succ) (Fin.cons (weaken Q) (underElement Fin.elim0)))
      (predOf (u j) fun i => weaken (Fin.elim0 i)))
    rw [predOf_rename_succ (bodies j) _ (fun i => weaken (Fin.elim0 i))]
    exact containedRefl _

theorem instantiate_nuAt {inner : Formula 1} (regional : inner.regional = true) (t : Term Symbol (predTy :: Γ) setTy) :
    instantiate t (.imp (.app (.var (.vs .vz)) (.var .vz))
      (nativeFormula inner (.var .vz) (underFixedPoint (Fin.elim0 : Fin 0 → Term Symbol Γ predTy)))) =
      .imp (.app (.var .vz) t) (nativeFormula inner t (Fin.cons (.var .vz) Fin.elim0)) := by
  change Term.imp (.app (.var .vz) t)
    (subst (Subst.single t) (nativeFormula inner (.var .vz) (underFixedPoint Fin.elim0))) = _
  rw [subst_nativeFormula_regional _ inner regional, native_one]
  rfl

theorem invariantHyp_one {inner : Formula 1} (regional : inner.regional = true) (env : Fin 0 → Term Symbol Γ predTy) :
    weaken (σ := setTy) (invariantHyp inner env) =
      .all (σ := setTy) (.imp (.app (.var (.vs (.vs .vz))) (.var .vz))
        (nativeFormula inner (.var .vz) (Fin.cons (.var (.vs (.vs .vz))) Fin.elim0))) := by
  unfold invariantHyp
  rw [weaken_eq_subst]
  change Term.all (.imp (.app (.var (.vs (.vs .vz))) (.var .vz)) (subst (Subst.lift (fun index => Term.var (Var.vs index)))
    (nativeFormula inner (.var .vz) (underFixedPoint env)))) = _
  rw [subst_nativeFormula_regional _ inner regional, native_one]
  rfl

/-- **Unfolding a greatest fixed point**: it implies its unfolding. -/
def unfoldNu {n : ℕ} (inner : Formula (n + 1)) (body : inner.fixBody = true) (u : Fin n → Formula 0)
    (bodies : ∀ i, (u i).fixBody = true) {x : Term Symbol Γ setTy} (coreX : x.isCore = true)
    (proof : Proof Δ (nativeFormula ((Formula.nu inner).subst u) x Fin.elim0)) :
    Proof Δ (nativeFormula (inner.subst (unfoldWith ((Formula.nu inner).subst u) u)) x Fin.elim0) := by
  have fixedBody : ((Formula.nu inner).subst u).fixBody = true := fixBody_subst _ u body bodies
  have innerBody : (inner.subst (liftSubstitution u)).fixBody = true :=
    fixBody_subst inner _ body (lifted_bodies bodies)
  have innerRegional := regional_of_fixBody _ innerBody
  have unfoldedBody : (inner.subst (unfoldWith ((Formula.nu inner).subst u) u)).fixBody = true :=
    fixBody_subst _ _ body (unfoldWith_bodies fixedBody bodies)
  change Proof Δ (existentialInline (σ := predTy) (conjunctionFormula
    (invariantHyp (inner.subst (liftSubstitution u)) Fin.elim0) (.app (.var .vz) (weaken x)))) at proof
  refine existentialElim proof ?_
  rw [weaken_nativeFormula_regional _ (regional_of_fixBody _ unfoldedBody), native_closed _ Fin.elim0]
  have atX := Proof.cast (instantiate_nuAt innerRegional (weaken x))
    (.allE (weaken x) (conjunctionLeft (Proof.newest (Δ := weakenHyps (σ := predTy) Δ) (conjunctionFormula
      (invariantHyp (inner.subst (liftSubstitution u)) Fin.elim0) (.app (.var .vz) (weaken x))))))
  refine transport inner body (liftSubstitution u) (unfoldWith ((Formula.nu inner).subst u) u) (lifted_bodies bodies)
    (unfoldWith_bodies fixedBody bodies) (Fin.cons (.var .vz) Fin.elim0) Fin.elim0
    (fun i => Fin.cases rfl (fun j => j.elim0) i) (fun i => i.elim0) (fun i => ?_) (weaken x) (coreWeaken coreX)
    (.impE atX (conjunctionRight (Proof.newest _)))
  refine Fin.cases ?_ (fun j => ?_) i
  · change Proof _ (containedIn (predOf (.var 0) (Fin.cons (.var .vz) Fin.elim0))
      (predOf ((Formula.nu inner).subst u) Fin.elim0))
    rw [predOf_var_zero]
    refine containedIntro ?_
    rw [weaken_predOf _ (regional_of_fixBody _ fixedBody)]
    refine predApp fixedBody (fun i => i.elim0) rfl ?_
    change Proof _ (existentialInline (σ := predTy) (conjunctionFormula
      (invariantHyp (inner.subst (liftSubstitution u)) _) (.app (.var .vz) (weaken (.var .vz)))))
    refine existentialIntro (.var (.vs .vz)) (Proof.cast (instantiate_nuBody innerRegional _ _ _).symm ?_)
    refine conjunctionIntro ?_ (Proof.cast (lam_weaken_app (.var .vz))
      (Proof.betaReduce (by rw [isCore_rename]; exact isCore_app_weaken (by simp only [isCore])) rfl
        (Proof.newest _)))
    refine Proof.cast ?_ ((Proof.lift (σ := setTy) (conjunctionLeft (Proof.newest (Δ := weakenHyps (σ := predTy) Δ)
      (conjunctionFormula (invariantHyp (inner.subst (liftSubstitution u)) Fin.elim0)
        (.app (.var .vz) (weaken x)))))).prepend _)
    rw [invariantHyp_one innerRegional, native_one (Fin.cons (weaken (.var (.vs .vz))) (underElement _))]
    rfl
  · change Proof _ (containedIn (predOf ((u j).rename Fin.succ) (Fin.cons (.var .vz) Fin.elim0))
      (predOf (u j) Fin.elim0))
    rw [predOf_rename_succ (bodies j) _ Fin.elim0]
    exact containedRefl _

/-- **Folding a greatest fixed point**: its unfolding implies it, the unfolding being a postfixed point. -/
def foldNu {n : ℕ} (inner : Formula (n + 1)) (body : inner.fixBody = true) (u : Fin n → Formula 0)
    (bodies : ∀ i, (u i).fixBody = true) {x : Term Symbol Γ setTy} (coreX : x.isCore = true)
    (proof : Proof Δ (nativeFormula (inner.subst (unfoldWith ((Formula.nu inner).subst u) u)) x Fin.elim0)) :
    Proof Δ (nativeFormula ((Formula.nu inner).subst u) x Fin.elim0) := by
  have fixedBody : ((Formula.nu inner).subst u).fixBody = true := fixBody_subst _ u body bodies
  have innerBody : (inner.subst (liftSubstitution u)).fixBody = true :=
    fixBody_subst inner _ body (lifted_bodies bodies)
  have innerRegional := regional_of_fixBody _ innerBody
  have unfoldedBody : (inner.subst (unfoldWith ((Formula.nu inner).subst u) u)).fixBody = true :=
    fixBody_subst _ _ body (unfoldWith_bodies fixedBody bodies)
  have unfoldedRegional := regional_of_fixBody _ unfoldedBody
  let Q : Term Symbol Γ predTy := predOf (inner.subst (unfoldWith ((Formula.nu inner).subst u) u)) Fin.elim0
  have coreQ : Q.isCore = true := isCore_predOf unfoldedBody coreElim0
  change Proof Δ (existentialInline (σ := predTy) (conjunctionFormula
    (invariantHyp (inner.subst (liftSubstitution u)) Fin.elim0) (.app (.var .vz) (weaken x))))
  refine existentialIntro Q (Proof.cast (instantiate_nuBody innerRegional Q x Fin.elim0).symm
    (conjunctionIntro (.allI (.impI ?_)) (predApp unfoldedBody coreElim0 coreX proof)))
  have weakQ : weaken (σ := setTy) Q = predOf (inner.subst (unfoldWith ((Formula.nu inner).subst u) u))
      (fun i => weaken (Fin.elim0 i)) := weaken_predOf _ unfoldedRegional _
  have newestHyp : Proof (.app (weaken Q) (.var .vz) :: weakenHyps (σ := setTy) Δ)
      (.app (predOf (inner.subst (unfoldWith ((Formula.nu inner).subst u) u)) fun i => weaken (Fin.elim0 i))
        (.var .vz)) :=
    Proof.cast (congrArg (fun p => Term.app p (.var .vz)) weakQ) (Proof.newest _)
  have unfolded := predUnapp unfoldedBody (env := fun i => weaken (Fin.elim0 i)) (fun i => i.elim0)
    (t := .var .vz) rfl newestHyp
  refine transport inner body (unfoldWith ((Formula.nu inner).subst u) u) (liftSubstitution u)
    (unfoldWith_bodies fixedBody bodies) (lifted_bodies bodies) (fun i => weaken (Fin.elim0 i))
    (Fin.cons (weaken Q) (underElement Fin.elim0)) (fun i => i.elim0)
    (fun i => Fin.cases (coreWeaken coreQ) (fun j => j.elim0) i) (fun i => ?_) (.var .vz) rfl unfolded
  refine Fin.cases ?_ (fun j => ?_) i
  · change Proof _ (containedIn (predOf ((Formula.nu inner).subst u) fun i => weaken (Fin.elim0 i))
      (predOf (.var 0) (Fin.cons (weaken Q) (underElement Fin.elim0))))
    rw [predOf_var_zero]
    refine containedIntro (Proof.betaExpand (by rw [isCore_rename]; exact isCore_app_weaken (coreWeaken coreQ)) rfl
      (Proof.cast (lam_weaken_app (weaken Q)).symm ?_))
    have weakWeakQ : weaken (σ := setTy) (weaken (σ := setTy) Q) =
        predOf (inner.subst (unfoldWith ((Formula.nu inner).subst u) u)) (fun i => weaken (weaken (Fin.elim0 i))) := by
      rw [weakQ, weaken_predOf _ unfoldedRegional]
    refine Proof.cast (congrArg (fun p => Term.app p (.var .vz)) weakWeakQ.symm)
      (predApp unfoldedBody (env := fun i => weaken (weaken (Fin.elim0 i))) (fun i => i.elim0) rfl ?_)
    refine Proof.cast (native_closed Fin.elim0 _) (unfoldNu inner body u bodies rfl ?_)
    refine Proof.cast (native_closed (fun i => weaken (weaken (Fin.elim0 i))) Fin.elim0)
      (predUnapp fixedBody (env := fun i => weaken (weaken (Fin.elim0 i))) (fun i => i.elim0) rfl ?_)
    exact Proof.cast (congrArg (fun p => Term.app p (.var .vz)) (weaken_predOf _ (regional_of_fixBody _ fixedBody) _))
      (Proof.newest _)
  · change Proof _ (containedIn (predOf (u j) fun i => weaken (Fin.elim0 i))
      (predOf ((u j).rename Fin.succ) (Fin.cons (weaken Q) (underElement Fin.elim0))))
    rw [predOf_rename_succ (bodies j) _ (fun i => weaken (Fin.elim0 i))]
    exact containedRefl _

end Unfolding

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
