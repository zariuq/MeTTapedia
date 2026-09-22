import Mettapedia.Languages.OpenTheory.ExtensionalHOLInterpretation
import Mettapedia.Logic.HOL.Semantics.KripkeHenkinCountermodel

/-!
# Excluded middle is not a theorem of the axiom-free OpenTheory kernel

The OpenTheory base theory, following HOL Light, defines its connectives from
primitive equality:

* `T = ((λ p. p) = (λ p. p))`
* `∀ = λ P. P = (λ x. T)`
* `∧ = λ p q. (λ f. f p q) = (λ f. f T T)`
* `⇒ = λ p q. (p ∧ q) = p`
* `F = ∀ p. p`
* `¬ = λ p. p ⇒ F`
* `∨ = λ p q. ∀ r. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r`

With every connective replaced by its definition, excluded middle
`∀ p. p ∨ ¬ p` is a closed Boolean term of the primitive kernel
(`excludedMiddleTerm`).  In the extensional higher-order calculus each defined
connective is provably equivalent to the primitive one (`forall_iff`,
`and_iff`, `imp_iff`, `falsity_iff`, `not_iff`, `or_iff`), so the translated
definition implies the primitive `∀ p. p ∨ ¬ p`.  Its instance at a free
propositional variable is not derivable: transporting such a derivation into
the one-atom signature of the excluded-middle canary contradicts
`HOL.KripkeHenkin.em_not_derivable`.  By the interpretation theorem, no
untagged theorem of the primitive closure has the sequent `⊢ ∀ p. p ∨ ¬ p`
(`excludedMiddle_not_derivable`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

open Mettapedia.Logic

namespace ExcludedMiddle

open HOL.KripkeHenkin (EMCanaryBase EMCanaryConst)

/-! ## Transport into the excluded-middle canary signature -/

/-- Every base type becomes the proposition type of the canary signature. -/
def canaryBase : AtomicTy → HOL.Ty EMCanaryBase := fun _ => .prop

/-- Target symbols retyped into the canary type structure. -/
def RetypedSymbol (τ : HOL.Ty EMCanaryBase) : Type :=
  {symbol : Sigma Symbol // HOL.Ty.substitute canaryBase symbol.1 = τ}

def retypeSymbol {τ : HOL.Ty AtomicTy} (symbol : Symbol τ) :
    RetypedSymbol (HOL.Ty.substitute canaryBase τ) :=
  ⟨⟨τ, symbol⟩, rfl⟩

/-- A closed canary term of every type. -/
def canaryInhabitant : (τ : HOL.Ty EMCanaryBase) → HOL.ClosedTerm EMCanaryConst τ
  | .prop => .top
  | .base b => b.elim
  | .arr _ τ => .lam (HOL.weaken (canaryInhabitant τ))

/-- The free Boolean variable `p`. -/
abbrev pVar : SourceVar := ⟨Name.global "p", Ty.bool⟩

/-- The target symbol of `p`, a proposition. -/
abbrev pSymbol {Γ : HOL.Ctx AtomicTy} : HOL.Formula Symbol Γ :=
  .const (.variable pVar Ty.toHOL_bool)

open Classical in
/-- Send the symbol of `p` to the canary atom and every other retyped symbol
to a fixed closed term. -/
noncomputable def canaryImage {τ : HOL.Ty EMCanaryBase} (symbol : RetypedSymbol τ) :
    HOL.ClosedTerm EMCanaryConst τ :=
  if h : τ = .prop ∧ symbol.1.2.sourceVar? = some pVar then
    h.1 ▸ .const EMCanaryConst.p
  else
    canaryInhabitant τ

theorem canaryImage_pSymbol :
    @canaryImage HOL.propTy
        (@retypeSymbol HOL.propTy (@Symbol.variable pVar HOL.propTy Ty.toHOL_bool)) =
      .const EMCanaryConst.p := by
  unfold canaryImage
  rw [dif_pos ⟨rfl, rfl⟩]

/-- The excluded-middle instance for the symbol of `p` is not derivable from
no hypotheses. -/
theorem not_extDerivation_pSymbol :
    ¬ HOL.ExtDerivation Symbol ([] : List (HOL.ClosedFormula Symbol))
      (.or pSymbol (.not pSymbol)) := by
  intro derivation
  have retyped := HOL.ExtDerivation.mapTypes canaryBase
    (fun symbol => retypeSymbol symbol) derivation
  have replaced := HOL.ExtDerivation.substConst_derivation canaryImage retyped
  apply HOL.KripkeHenkin.em_not_derivable
  refine ⟨[], by simp, ?_⟩
  change HOL.ExtDerivation EMCanaryConst []
    (.or (.const EMCanaryConst.p) (.not (.const EMCanaryConst.p)))
  simp only [HOL.mapTypes, HOL.substConst, canaryImage_pSymbol] at replaced
  exact replaced

/-! ## Derivation helpers -/

section Helpers

variable {Γ : HOL.Ctx AtomicTy}

theorem extDerivation_weaken {σ : HOL.Ty AtomicTy} {Δ : List (HOL.Formula Symbol Γ)}
    {φ : HOL.Formula Symbol Γ} (derivation : HOL.ExtDerivation Symbol Δ φ) :
    HOL.ExtDerivation Symbol (HOL.weakenHyps (σ := σ) Δ) (HOL.weaken φ) :=
  HOL.ExtDerivation.rename HOL.Rename.weaken derivation

theorem instantiate_var_rename_lift_weaken {σ τ : HOL.Ty AtomicTy}
    (term : HOL.Term Symbol (σ :: Γ) τ) :
    HOL.instantiate (.var .vz) (HOL.rename (HOL.Rename.lift HOL.Rename.weaken) term) =
      term := by
  unfold HOL.instantiate
  rw [HOL.subst_rename]
  calc HOL.subst _ term = HOL.subst HOL.Subst.id term := by
        apply HOL.subst_ext
        intro τ' x
        cases x <;> rfl
    _ = term := HOL.subst_id term

/-- A universal statement yields its body in the extended context. -/
theorem extDerivation_all_inv {σ : HOL.Ty AtomicTy} {Δ : List (HOL.Formula Symbol Γ)}
    {φ : HOL.Formula Symbol (σ :: Γ)}
    (derivation : HOL.ExtDerivation Symbol Δ (.all φ)) :
    HOL.ExtDerivation Symbol (HOL.weakenHyps (σ := σ) Δ) φ := by
  have weakened := extDerivation_weaken (σ := σ) derivation
  have instantiated := HOL.ExtDerivation.allE
    (φ := HOL.rename (HOL.Rename.lift HOL.Rename.weaken) φ) (.var .vz) weakened
  rwa [instantiate_var_rename_lift_weaken] at instantiated

theorem extDerivation_mono_cons {Δ : List (HOL.Formula Symbol Γ)}
    {χ φ : HOL.Formula Symbol Γ} (derivation : HOL.ExtDerivation Symbol Δ φ) :
    HOL.ExtDerivation Symbol (χ :: Δ) φ :=
  HOL.ExtDerivation.mono (fun h => List.mem_cons_of_mem _ h) derivation

end Helpers

/-! ## The defined connectives of the OpenTheory base theory -/

section Connectives

variable {Γ : HOL.Ctx AtomicTy}

/-- `T = ((λ p. p) = (λ p. p))`. -/
abbrev truth : HOL.Formula Symbol Γ := PrimitiveSentences.truthFormula

/-- `∀ = λ P. P = (λ x. T)`. -/
def forallTerm (σ : HOL.Ty AtomicTy) : HOL.Term Symbol Γ (.arr (.arr σ .prop) .prop) :=
  .lam (.eq (.var .vz) (.lam truth))

theorem truth_provable (Δ : List (HOL.Formula Symbol Γ)) :
    HOL.ExtDerivation Symbol Δ (truth : HOL.Formula Symbol Γ) :=
  .eqRefl _

theorem eq_truth_of {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (derivation : HOL.ExtDerivation Symbol Δ φ) :
    HOL.ExtDerivation Symbol Δ (.eq φ truth) :=
  .eqPropI (.impI (truth_provable _)) (.impI (extDerivation_mono_cons derivation))

theorem of_eq_truth {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (derivation : HOL.ExtDerivation Symbol Δ (.eq φ truth)) :
    HOL.ExtDerivation Symbol Δ φ :=
  HOL.ExtDerivation.eqProp_mp_right derivation (truth_provable _)

theorem beta_forall {σ : HOL.Ty AtomicTy} (Δ : List (HOL.Formula Symbol Γ))
    (predicate : HOL.Term Symbol Γ (.arr σ .prop)) :
    HOL.ExtDerivation Symbol Δ
      (.eq (.app (forallTerm σ) predicate) (.eq predicate (.lam truth))) :=
  .beta predicate _

/-- The defined universal quantifier is provably the primitive one. -/
theorem forall_iff {σ : HOL.Ty AtomicTy} {Δ : List (HOL.Formula Symbol Γ)}
    {predicate : HOL.Term Symbol Γ (.arr σ .prop)} :
    HOL.ExtDerivation Symbol Δ (.app (forallTerm σ) predicate) ↔
      HOL.ExtDerivation Symbol Δ (.all (.app (HOL.weaken predicate) (.var .vz))) := by
  constructor
  · intro derivation
    have hequation := HOL.ExtDerivation.eqProp_mp_left (beta_forall Δ predicate) derivation
    have hweak : HOL.ExtDerivation Symbol (HOL.weakenHyps (σ := σ) Δ)
        (.eq (HOL.weaken predicate) (.lam truth)) := extDerivation_weaken hequation
    have happ := HOL.ExtDerivation.eqApp (.var .vz) hweak
    have hbeta : HOL.ExtDerivation Symbol (HOL.weakenHyps (σ := σ) Δ)
        (.eq (.app (.lam truth) (.var .vz)) truth) := .beta (.var .vz) truth
    exact .allI (of_eq_truth (.eqTrans happ hbeta))
  · intro derivation
    have hbody := extDerivation_all_inv derivation
    have hbeta : HOL.ExtDerivation Symbol (HOL.weakenHyps (σ := σ) Δ)
        (.eq (.app (HOL.weaken (.lam truth)) (.var .vz)) truth) := .beta (.var .vz) truth
    have hpoint : HOL.ExtDerivation Symbol (HOL.weakenHyps (σ := σ) Δ)
        (.eq (.app (HOL.weaken predicate) (.var .vz))
          (.app (HOL.weaken (.lam truth)) (.var .vz))) :=
      .eqTrans (eq_truth_of hbody) (.eqSymm hbeta)
    have hext : HOL.ExtDerivation Symbol Δ (.eq predicate (.lam truth)) :=
      .funExt (.allI hpoint)
    exact HOL.ExtDerivation.eqProp_mp_right (beta_forall Δ predicate) hext

/-- The type `bool -> bool -> bool`. -/
abbrev boolBinary : HOL.Ty AtomicTy := .arr .prop (.arr .prop .prop)

/-- `∧ = λ p q. (λ f. f p q) = (λ f. f T T)`. -/
def andTerm : HOL.Term Symbol Γ boolBinary :=
  .lam (.lam (.eq
    (.lam (.app (.app (.var .vz : HOL.Term Symbol (boolBinary :: _) boolBinary)
      (.var (.vs (.vs .vz)))) (.var (.vs .vz))))
    (.lam (.app (.app (.var .vz : HOL.Term Symbol (boolBinary :: _) boolBinary)
      truth) truth))))

/-- The beta-normal body of `p ∧ q`. -/
def andBody (p q : HOL.Formula Symbol Γ) : HOL.Formula Symbol Γ :=
  .eq (.lam (.app (.app (.var .vz : HOL.Term Symbol (boolBinary :: Γ) boolBinary)
      (HOL.weaken p)) (HOL.weaken q)))
    (.lam (.app (.app (.var .vz : HOL.Term Symbol (boolBinary :: Γ) boolBinary)
      truth) truth))

theorem subst_single_weaken {σ τ : HOL.Ty AtomicTy} (t : HOL.Term Symbol Γ σ)
    (u : HOL.Term Symbol Γ τ) : HOL.subst (HOL.Subst.single t) (HOL.weaken u) = u :=
  HOL.instantiate_weaken t u

theorem beta_and (Δ : List (HOL.Formula Symbol Γ)) (p q : HOL.Formula Symbol Γ) :
    HOL.ExtDerivation Symbol Δ (.eq (.app (.app andTerm p) q) (andBody p q)) := by
  have first := HOL.ExtDerivation.eqApp q (HOL.ExtDerivation.beta (Δ := Δ) p
    (.lam (.eq
      (.lam (.app (.app (.var .vz : HOL.Term Symbol (boolBinary :: _) boolBinary)
        (.var (.vs (.vs .vz)))) (.var (.vs .vz))))
      (.lam (.app (.app (.var .vz : HOL.Term Symbol (boolBinary :: _) boolBinary)
        truth) truth)))))
  have second := HOL.ExtDerivation.beta (Δ := Δ) q
    (.eq
      (.lam (.app (.app (.var .vz : HOL.Term Symbol (boolBinary :: _) boolBinary)
        (HOL.weaken (HOL.weaken p))) (.var (.vs .vz))))
      (.lam (.app (.app (.var .vz : HOL.Term Symbol (boolBinary :: _) boolBinary)
        truth) truth)))
  have hcompute : HOL.instantiate q (.eq
      (.lam (.app (.app (.var .vz : HOL.Term Symbol (boolBinary :: _) boolBinary)
        (HOL.weaken (HOL.weaken p))) (.var (.vs .vz))))
      (.lam (.app (.app (.var .vz : HOL.Term Symbol (boolBinary :: _) boolBinary)
        truth) truth))) = andBody p q := by
    show HOL.Term.eq
      (.lam (.app (.app (.var .vz)
        (HOL.subst (HOL.Subst.lift (HOL.Subst.single q)) (HOL.weaken (HOL.weaken p))))
        (HOL.weaken q))) _ = _
    rw [HOL.subst_weaken, subst_single_weaken]
    rfl
  rw [hcompute] at second
  exact .eqTrans first second

/-- `λ x y. x`. -/
def projectFirst : HOL.Term Symbol Γ boolBinary := .lam (.lam (.var (.vs .vz)))

/-- `λ x y. y`. -/
def projectSecond : HOL.Term Symbol Γ boolBinary := .lam (.lam (.var .vz))

theorem beta_projectFirst (Δ : List (HOL.Formula Symbol Γ)) (a b : HOL.Formula Symbol Γ) :
    HOL.ExtDerivation Symbol Δ (.eq (.app (.app projectFirst a) b) a) := by
  have first := HOL.ExtDerivation.eqApp b
    (HOL.ExtDerivation.beta (Δ := Δ) a (.lam (.var (.vs .vz)) : HOL.Term Symbol _ (.arr .prop .prop)))
  have second := HOL.ExtDerivation.beta (Δ := Δ) b (HOL.weaken (σ := .prop) a)
  rw [HOL.instantiate_weaken] at second
  exact .eqTrans first second

theorem beta_projectSecond (Δ : List (HOL.Formula Symbol Γ)) (a b : HOL.Formula Symbol Γ) :
    HOL.ExtDerivation Symbol Δ (.eq (.app (.app projectSecond a) b) b) := by
  have first := HOL.ExtDerivation.eqApp b
    (HOL.ExtDerivation.beta (Δ := Δ) a (.lam (.var .vz) : HOL.Term Symbol _ (.arr .prop .prop)))
  have second := HOL.ExtDerivation.beta (Δ := Δ) b (.var .vz : HOL.Formula Symbol (.prop :: Γ))
  exact .eqTrans first second

theorem beta_selector (Δ : List (HOL.Formula Symbol Γ)) (a b : HOL.Formula Symbol Γ)
    (selector : HOL.Term Symbol Γ boolBinary) :
    HOL.ExtDerivation Symbol Δ
      (.eq (.app (.lam (.app (.app (.var .vz : HOL.Term Symbol (boolBinary :: Γ) boolBinary)
          (HOL.weaken a)) (HOL.weaken b))) selector)
        (.app (.app selector a) b)) := by
  have reduced := HOL.ExtDerivation.beta (Δ := Δ) selector
    (.app (.app (.var .vz : HOL.Term Symbol (boolBinary :: Γ) boolBinary)
      (HOL.weaken a)) (HOL.weaken b))
  have hcompute : HOL.instantiate selector
      (.app (.app (.var .vz : HOL.Term Symbol (boolBinary :: Γ) boolBinary)
        (HOL.weaken a)) (HOL.weaken b)) = .app (.app selector a) b := by
    show HOL.Term.app (HOL.Term.app selector
        (HOL.subst (HOL.Subst.single selector) (HOL.weaken a)))
      (HOL.subst (HOL.Subst.single selector) (HOL.weaken b)) = _
    rw [subst_single_weaken, subst_single_weaken]
  rw [hcompute] at reduced
  exact reduced

/-- The defined conjunction is provably the primitive one. -/
theorem and_iff {Δ : List (HOL.Formula Symbol Γ)} {p q : HOL.Formula Symbol Γ} :
    HOL.ExtDerivation Symbol Δ (.app (.app andTerm p) q) ↔
      HOL.ExtDerivation Symbol Δ (.and p q) := by
  have hbody : HOL.ExtDerivation Symbol Δ (.app (.app andTerm p) q) ↔
      HOL.ExtDerivation Symbol Δ (andBody p q) :=
    ⟨HOL.ExtDerivation.eqProp_mp_left (beta_and Δ p q),
      HOL.ExtDerivation.eqProp_mp_right (beta_and Δ p q)⟩
  rw [hbody]
  constructor
  · intro body
    have select : ∀ selector : HOL.Term Symbol Γ boolBinary,
        HOL.ExtDerivation Symbol Δ
          (.eq (.app (.app selector p) q) (.app (.app selector truth) truth)) :=
      fun selector => .eqTrans (.eqSymm (beta_selector Δ p q selector))
        (.eqTrans (.eqApp selector body) (beta_selector Δ truth truth selector))
    exact .andI
      (of_eq_truth (.eqTrans (.eqSymm (beta_projectFirst Δ p q))
        (.eqTrans (select projectFirst) (beta_projectFirst Δ truth truth))))
      (of_eq_truth (.eqTrans (.eqSymm (beta_projectSecond Δ p q))
        (.eqTrans (select projectSecond) (beta_projectSecond Δ truth truth))))
  · intro conjunction
    have hp : HOL.ExtDerivation Symbol (HOL.weakenHyps (σ := boolBinary) Δ)
        (.eq (HOL.weaken p) truth) := extDerivation_weaken (eq_truth_of (.andEL conjunction))
    have hq : HOL.ExtDerivation Symbol (HOL.weakenHyps (σ := boolBinary) Δ)
        (.eq (HOL.weaken q) truth) := extDerivation_weaken (eq_truth_of (.andER conjunction))
    exact .eqLam (HOL.ExtDerivation.eqAppCongr (.eqAppArg (.var .vz) hp) hq)

/-- `⇒ = λ p q. (p ∧ q) = p`. -/
def impTerm : HOL.Term Symbol Γ boolBinary :=
  .lam (.lam (.eq (.app (.app andTerm (.var (.vs .vz))) (.var .vz)) (.var (.vs .vz))))

theorem beta_imp (Δ : List (HOL.Formula Symbol Γ)) (p q : HOL.Formula Symbol Γ) :
    HOL.ExtDerivation Symbol Δ
      (.eq (.app (.app impTerm p) q) (.eq (.app (.app andTerm p) q) p)) := by
  have first := HOL.ExtDerivation.eqApp q (HOL.ExtDerivation.beta (Δ := Δ) p
    (.lam (.eq (.app (.app andTerm (.var (.vs .vz))) (.var .vz)) (.var (.vs .vz)))))
  have second := HOL.ExtDerivation.beta (Δ := Δ) q
    (.eq (.app (.app andTerm (HOL.weaken (σ := .prop) p)) (.var .vz)) (HOL.weaken p))
  have hcompute : HOL.instantiate q
      (.eq (.app (.app andTerm (HOL.weaken (σ := .prop) p)) (.var .vz)) (HOL.weaken p)) =
        .eq (.app (.app andTerm p) q) p := by
    show HOL.Term.eq (.app (.app (HOL.subst (HOL.Subst.single q) andTerm)
        (HOL.subst (HOL.Subst.single q) (HOL.weaken p))) q)
      (HOL.subst (HOL.Subst.single q) (HOL.weaken p)) = _
    rw [subst_single_weaken]
    rfl
  rw [hcompute] at second
  exact .eqTrans first second

/-- The defined implication is provably the primitive one. -/
theorem imp_iff {Δ : List (HOL.Formula Symbol Γ)} {p q : HOL.Formula Symbol Γ} :
    HOL.ExtDerivation Symbol Δ (.app (.app impTerm p) q) ↔
      HOL.ExtDerivation Symbol Δ (.imp p q) := by
  have hbody : HOL.ExtDerivation Symbol Δ (.app (.app impTerm p) q) ↔
      HOL.ExtDerivation Symbol Δ (.eq (.app (.app andTerm p) q) p) :=
    ⟨HOL.ExtDerivation.eqProp_mp_left (beta_imp Δ p q),
      HOL.ExtDerivation.eqProp_mp_right (beta_imp Δ p q)⟩
  rw [hbody]
  constructor
  · intro equation
    refine .impI ?_
    have hand := HOL.ExtDerivation.eqProp_mp_right (extDerivation_mono_cons equation)
      (.hyp List.mem_cons_self)
    exact .andER (and_iff.mp hand)
  · intro implication
    refine .eqPropI (.impI ?_) (.impI ?_)
    · exact .andEL (and_iff.mp (.hyp List.mem_cons_self))
    · exact and_iff.mpr (.andI (.hyp List.mem_cons_self)
        (.impE (extDerivation_mono_cons implication) (.hyp List.mem_cons_self)))

/-- `F = ∀ p. p`. -/
def falsityDefinition : HOL.Formula Symbol Γ := .app (forallTerm .prop) (.lam (.var .vz))

/-- The defined falsity is provably the primitive one. -/
theorem falsity_iff {Δ : List (HOL.Formula Symbol Γ)} :
    HOL.ExtDerivation Symbol Δ falsityDefinition ↔ HOL.ExtDerivation Symbol Δ .bot := by
  constructor
  · intro derivation
    have instantiated := HOL.ExtDerivation.allE .bot (forall_iff.mp derivation)
    change HOL.ExtDerivation Symbol Δ (.app (.lam (.var .vz)) .bot) at instantiated
    exact HOL.ExtDerivation.eqProp_mp_left (.beta .bot (.var .vz)) instantiated
  · exact .botE

/-- `¬ = λ p. p ⇒ F`. -/
def notTerm : HOL.Term Symbol Γ (.arr .prop .prop) :=
  .lam (.app (.app impTerm (.var .vz)) falsityDefinition)

/-- The defined negation is provably the primitive one. -/
theorem not_iff {Δ : List (HOL.Formula Symbol Γ)} {p : HOL.Formula Symbol Γ} :
    HOL.ExtDerivation Symbol Δ (.app notTerm p) ↔ HOL.ExtDerivation Symbol Δ (.not p) := by
  have hbeta : HOL.ExtDerivation Symbol Δ
      (.eq (.app notTerm p) (.app (.app impTerm p) falsityDefinition)) :=
    .beta p _
  constructor
  · intro derivation
    have himp := imp_iff.mp (HOL.ExtDerivation.eqProp_mp_left hbeta derivation)
    exact .notI (falsity_iff.mp (.impE (extDerivation_mono_cons himp)
      (.hyp List.mem_cons_self)))
  · intro derivation
    refine HOL.ExtDerivation.eqProp_mp_right hbeta (imp_iff.mpr (.impI ?_))
    exact falsity_iff.mpr (.notE (extDerivation_mono_cons derivation)
      (.hyp List.mem_cons_self))

/-- Application of the defined implication. -/
abbrev impApp (p q : HOL.Formula Symbol Γ) : HOL.Formula Symbol Γ :=
  .app (.app impTerm p) q

/-- `∨ = λ p q. ∀ r. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r`. -/
def orTerm : HOL.Term Symbol Γ boolBinary :=
  .lam (.lam (.app (forallTerm .prop) (.lam
    (impApp (impApp (.var (.vs (.vs .vz))) (.var .vz))
      (impApp (impApp (.var (.vs .vz)) (.var .vz)) (.var .vz))))))

/-- The body of the defined disjunction, `(p ⇒ r) ⇒ (q ⇒ r) ⇒ r`. -/
abbrev orMatrix (p q : HOL.Formula Symbol Γ) : HOL.Formula Symbol (.prop :: Γ) :=
  impApp (impApp (HOL.weaken p) (.var .vz)) (impApp (impApp (HOL.weaken q) (.var .vz)) (.var .vz))

theorem beta_or (Δ : List (HOL.Formula Symbol Γ)) (p q : HOL.Formula Symbol Γ) :
    HOL.ExtDerivation Symbol Δ
      (.eq (.app (.app orTerm p) q) (.app (forallTerm .prop) (.lam (orMatrix p q)))) := by
  have first := HOL.ExtDerivation.eqApp q (HOL.ExtDerivation.beta (Δ := Δ) p
    (.lam (.app (forallTerm .prop) (.lam
      (impApp (impApp (.var (.vs (.vs .vz))) (.var .vz))
        (impApp (impApp (.var (.vs .vz)) (.var .vz)) (.var .vz)))))))
  have second := HOL.ExtDerivation.beta (Δ := Δ) q
    (.app (forallTerm .prop) (.lam
      (impApp (impApp (HOL.weaken (σ := .prop) (HOL.weaken (σ := .prop) p)) (.var .vz))
        (impApp (impApp (.var (.vs .vz)) (.var .vz)) (.var .vz)))))
  have hcompute : HOL.instantiate q
      (.app (forallTerm .prop) (.lam
        (impApp (impApp (HOL.weaken (σ := .prop) (HOL.weaken (σ := .prop) p)) (.var .vz))
          (impApp (impApp (.var (.vs .vz)) (.var .vz)) (.var .vz))))) =
        .app (forallTerm .prop) (.lam (orMatrix p q)) := by
    show HOL.Term.app (HOL.subst (HOL.Subst.single q) (forallTerm .prop)) (.lam
      (impApp (impApp (HOL.subst (HOL.Subst.lift (HOL.Subst.single q))
          (HOL.weaken (HOL.weaken p))) (.var .vz))
        (impApp (impApp (HOL.weaken q) (.var .vz)) (.var .vz)))) = _
    rw [HOL.subst_weaken, subst_single_weaken]
    rfl
  rw [hcompute] at second
  exact .eqTrans first second

theorem beta_weaken_lam_var {σ : HOL.Ty AtomicTy} (Δ : List (HOL.Formula Symbol (σ :: Γ)))
    (body : HOL.Formula Symbol (σ :: Γ)) :
    HOL.ExtDerivation Symbol Δ
      (.eq (.app (HOL.weaken (σ := σ) (.lam body)) (.var .vz)) body) := by
  have reduced := HOL.ExtDerivation.beta (Δ := Δ) (.var .vz)
    (HOL.rename (HOL.Rename.lift HOL.Rename.weaken) body)
  rw [instantiate_var_rename_lift_weaken] at reduced
  exact reduced

/-- The defined disjunction is provably the primitive one. -/
theorem or_iff {Δ : List (HOL.Formula Symbol Γ)} {p q : HOL.Formula Symbol Γ} :
    HOL.ExtDerivation Symbol Δ (.app (.app orTerm p) q) ↔
      HOL.ExtDerivation Symbol Δ (.or p q) := by
  have hbody : HOL.ExtDerivation Symbol Δ (.app (.app orTerm p) q) ↔
      HOL.ExtDerivation Symbol Δ (.app (forallTerm .prop) (.lam (orMatrix p q))) :=
    ⟨HOL.ExtDerivation.eqProp_mp_left (beta_or Δ p q),
      HOL.ExtDerivation.eqProp_mp_right (beta_or Δ p q)⟩
  rw [hbody, forall_iff]
  constructor
  · intro derivation
    have instantiated := HOL.ExtDerivation.allE (.or p q) derivation
    have hcompute : HOL.instantiate (.or p q)
        (.app (HOL.weaken (σ := .prop) (.lam (orMatrix p q))) (.var .vz)) =
          .app (.lam (orMatrix p q)) (.or p q) := by
      show HOL.Term.app (HOL.subst (HOL.Subst.single (.or p q))
        (HOL.weaken (.lam (orMatrix p q)))) (.or p q) = _
      rw [subst_single_weaken]
    rw [hcompute] at instantiated
    have reduced := HOL.ExtDerivation.eqProp_mp_left
      (.beta (.or p q) (orMatrix p q)) instantiated
    have hmatrix : HOL.instantiate (.or p q) (orMatrix p q) =
        impApp (impApp p (.or p q)) (impApp (impApp q (.or p q)) (.or p q)) := by
      show impApp (impApp (HOL.subst (HOL.Subst.single (.or p q)) (HOL.weaken p)) (.or p q))
        (impApp (impApp (HOL.subst (HOL.Subst.single (.or p q)) (HOL.weaken q)) (.or p q))
          (.or p q)) = _
      rw [subst_single_weaken, subst_single_weaken]
    rw [hmatrix] at reduced
    have left : HOL.ExtDerivation Symbol Δ (impApp p (.or p q)) :=
      imp_iff.mpr (.impI (.orIL (.hyp List.mem_cons_self)))
    have right : HOL.ExtDerivation Symbol Δ (impApp q (.or p q)) :=
      imp_iff.mpr (.impI (.orIR (.hyp List.mem_cons_self)))
    exact .impE (imp_iff.mp (.impE (imp_iff.mp reduced) left)) right
  · intro derivation
    refine .allI (HOL.ExtDerivation.eqProp_mp_right (beta_weaken_lam_var _ _) ?_)
    refine imp_iff.mpr (.impI (imp_iff.mpr (.impI ?_)))
    have weakened : HOL.ExtDerivation Symbol (HOL.weakenHyps (σ := .prop) Δ)
        (.or (HOL.weaken p) (HOL.weaken q)) := extDerivation_weaken derivation
    refine .orE (extDerivation_mono_cons (extDerivation_mono_cons weakened)) ?_ ?_
    · exact .impE (imp_iff.mp (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))) (.hyp List.mem_cons_self)
    · exact .impE (imp_iff.mp (.hyp (List.mem_cons_of_mem _ List.mem_cons_self)))
        (.hyp List.mem_cons_self)

/-- `∀ p. p ∨ ¬ p` with every connective replaced by its definition. -/
def excludedMiddleDefinition : HOL.Formula Symbol Γ :=
  .app (forallTerm .prop) (.lam (.app (.app orTerm (.var .vz)) (.app notTerm (.var .vz))))

/-- The defined excluded-middle sentence provably implies the primitive
one. -/
theorem excludedMiddle_of_definition {Δ : List (HOL.Formula Symbol Γ)}
    (derivation : HOL.ExtDerivation Symbol Δ excludedMiddleDefinition) :
    HOL.ExtDerivation Symbol Δ (.all (.or (.var .vz) (.not (.var .vz)))) := by
  have body := extDerivation_all_inv (forall_iff.mp derivation)
  have matrix := HOL.ExtDerivation.eqProp_mp_left (beta_weaken_lam_var _ _) body
  refine .allI (.orE (or_iff.mp matrix) (.orIL (.hyp List.mem_cons_self)) ?_)
  exact .orIR (not_iff.mp (.hyp List.mem_cons_self))

end Connectives

/-- The defined excluded-middle sentence is not derivable from no
hypotheses. -/
theorem not_extDerivation_excludedMiddleDefinition :
    ¬ HOL.ExtDerivation Symbol ([] : List (HOL.ClosedFormula Symbol))
      excludedMiddleDefinition := by
  intro derivation
  exact not_extDerivation_pSymbol
    (HOL.ExtDerivation.allE pSymbol (excludedMiddle_of_definition derivation))

/-! ## The defined connectives as OpenTheory terms -/

/-- The OpenTheory type `bool -> bool -> bool`. -/
def boolBinaryTy : Ty := .function Ty.bool (.function Ty.bool Ty.bool)

theorem boolBinaryTy_toHOL : boolBinaryTy.toHOL = boolBinary := by
  simp [boolBinaryTy]

/-- `∀ = λ P. P = (λ x. T)` at the element type `A`. -/
def forallDB (A : Ty) : DBTerm :=
  .abs (.function A Ty.bool)
    (CanonicalTerm.equalityDB (.function A Ty.bool) (.bound 0)
      (.abs A PrimitiveSentences.truthDB))

/-- `∧ = λ p q. (λ f. f p q) = (λ f. f T T)`. -/
def andDB : DBTerm :=
  .abs Ty.bool (.abs Ty.bool (CanonicalTerm.equalityDB (.function boolBinaryTy Ty.bool)
    (.abs boolBinaryTy (.app (.app (.bound 0) (.bound 2)) (.bound 1)))
    (.abs boolBinaryTy
      (.app (.app (.bound 0) PrimitiveSentences.truthDB) PrimitiveSentences.truthDB))))

/-- `⇒ = λ p q. (p ∧ q) = p`. -/
def impDB : DBTerm :=
  .abs Ty.bool (.abs Ty.bool
    (CanonicalTerm.equalityDB Ty.bool (.app (.app andDB (.bound 1)) (.bound 0)) (.bound 1)))

/-- Application of the defined implication. -/
def impAppDB (p q : DBTerm) : DBTerm := .app (.app impDB p) q

/-- `F = ∀ p. p`. -/
def falsityDefinitionDB : DBTerm := .app (forallDB Ty.bool) PrimitiveSentences.identityBool

/-- `¬ = λ p. p ⇒ F`. -/
def notDB : DBTerm := .abs Ty.bool (.app (.app impDB (.bound 0)) falsityDefinitionDB)

/-- `∨ = λ p q. ∀ r. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r`. -/
def orDB : DBTerm :=
  .abs Ty.bool (.abs Ty.bool (.app (forallDB Ty.bool) (.abs Ty.bool
    (impAppDB (impAppDB (.bound 2) (.bound 0))
      (impAppDB (impAppDB (.bound 1) (.bound 0)) (.bound 0))))))

/-- Excluded middle `∀ p. p ∨ ¬ p`, with each defined connective replaced by
its definition, as a term of the primitive kernel. -/
def excludedMiddleDB : DBTerm :=
  .app (forallDB Ty.bool) (.abs Ty.bool (.app (.app orDB (.bound 0)) (.app notDB (.bound 0))))

section Translations

variable (Γ : HOL.Ctx AtomicTy)

theorem forallDB_translates {A : Ty} {σ : HOL.Ty AtomicTy} (typed : A.toHOL = σ) :
    Translates Γ (forallDB A) (.arr (.arr σ .prop) .prop) (forallTerm σ) :=
  .abs (by rw [Ty.toHOL_function, typed, Ty.toHOL_bool])
    (.equalityApp (equalityOperand?_equality _)
      (by rw [Ty.toHOL_function, typed, Ty.toHOL_bool])
      (.bound .vz) (.abs typed (PrimitiveSentences.truthDB_translates _)))

theorem andDB_translates : Translates Γ andDB boolBinary andTerm :=
  .abs Ty.toHOL_bool (.abs Ty.toHOL_bool (.equalityApp (equalityOperand?_equality _)
    (by rw [Ty.toHOL_function, boolBinaryTy_toHOL, Ty.toHOL_bool])
    (.abs boolBinaryTy_toHOL
      (.app rfl (.app rfl (.bound .vz) (.bound (.vs (.vs .vz)))) (.bound (.vs .vz))))
    (.abs boolBinaryTy_toHOL
      (.app rfl (.app rfl (.bound .vz) (PrimitiveSentences.truthDB_translates _))
        (PrimitiveSentences.truthDB_translates _)))))

theorem impDB_translates : Translates Γ impDB boolBinary impTerm :=
  .abs Ty.toHOL_bool (.abs Ty.toHOL_bool (.equalityApp (equalityOperand?_equality _)
    Ty.toHOL_bool
    (.app rfl (.app rfl (andDB_translates _) (.bound (.vs .vz))) (.bound .vz))
    (.bound (.vs .vz))))

theorem impAppDB_translates {p q : DBTerm} {p' q' : HOL.Formula Symbol Γ}
    (hp : Translates Γ p .prop p') (hq : Translates Γ q .prop q') :
    Translates Γ (impAppDB p q) .prop (impApp p' q') :=
  .app rfl (.app rfl (impDB_translates Γ) hp) hq

theorem falsityDefinitionDB_translates :
    Translates Γ falsityDefinitionDB .prop falsityDefinition :=
  .app rfl (forallDB_translates Γ Ty.toHOL_bool)
    (PrimitiveSentences.identityBool_translates Γ)

theorem notDB_translates : Translates Γ notDB (.arr .prop .prop) notTerm :=
  .abs Ty.toHOL_bool (.app rfl (.app rfl (impDB_translates _) (.bound .vz))
    (falsityDefinitionDB_translates _))

theorem orDB_translates : Translates Γ orDB boolBinary orTerm :=
  .abs Ty.toHOL_bool (.abs Ty.toHOL_bool (.app rfl (forallDB_translates _ Ty.toHOL_bool)
    (.abs Ty.toHOL_bool
      (impAppDB_translates _
        (impAppDB_translates _ (.bound (.vs (.vs .vz))) (.bound .vz))
        (impAppDB_translates _
          (impAppDB_translates _ (.bound (.vs .vz)) (.bound .vz)) (.bound .vz))))))

theorem excludedMiddleDB_translates :
    Translates Γ excludedMiddleDB .prop excludedMiddleDefinition :=
  .app rfl (forallDB_translates Γ Ty.toHOL_bool)
    (.abs Ty.toHOL_bool
      (.app rfl (.app rfl (orDB_translates _) (.bound .vz))
        (.app rfl (notDB_translates _) (.bound .vz))))

end Translations

/-- Excluded middle as a checked Boolean term of the primitive kernel. -/
def excludedMiddleTerm : CanonicalTerm :=
  CanonicalTerm.ofFormulaTranslation excludedMiddleDB (excludedMiddleDB_translates [])

/-- **Excluded middle is not a theorem of the axiom-free kernel.**  No theorem
of the primitive closure without axiom tags has the sequent `⊢ ∀ p. p ∨ ¬ p`,
with the connectives given by their OpenTheory definitions. -/
theorem excludedMiddle_not_derivable_of_axioms_eq_empty {policy : AxiomPolicy}
    {out : Theorem}
    (derivation : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out)
    (untagged : out.axioms = ∅) :
    out.sequent ≠ ⟨∅, excludedMiddleTerm⟩ := by
  intro hsequent
  have provable := derives_translatedProvable_of_axioms_eq_empty derivation untagged
  rw [hsequent] at provable
  obtain ⟨φ, hφ, premises, hpremises, extDerivation⟩ := provable
  have hφ' : φ = excludedMiddleDefinition := hφ.unique_eq (excludedMiddleDB_translates [])
  subst hφ'
  refine not_extDerivation_excludedMiddleDefinition
    (HOL.ExtDerivation.mono (fun {χ} hχ => ?_) extDerivation)
  rcases hpremises χ hχ with hempty | ⟨term, hterm, _⟩
  · exact absurd hempty (Set.notMem_empty _)
  · exact absurd hterm (Finset.notMem_empty _)

/-- The axiom-free kernel does not derive excluded middle. -/
theorem excludedMiddle_not_derivable {out : Theorem}
    (derivation : Mettapedia.Logic.Derives (PolicyPrimitiveRule emptyAxiomPolicy) out) :
    out.sequent ≠ ⟨∅, excludedMiddleTerm⟩ :=
  excludedMiddle_not_derivable_of_axioms_eq_empty derivation
    (axioms_eq_empty_of_emptyAxiomPolicy derivation)

end ExcludedMiddle

end Mettapedia.Languages.OpenTheory
