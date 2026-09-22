import Mettapedia.Languages.OpenTheory.ExtensionalHOLInterpretation

/-!
# Eta is not a theorem of the axiom-free OpenTheory kernel

For a free variable `f` of function type, the eta equation `(λ x. f x) = f` is
provable in extensional higher-order logic (`HOL.ExtDerivation.eta`), so its
translated sequent is provable from no hypotheses
(`Eta.equation_translatedProvable`).  It is not a theorem of the closure of the
nine primitive rules under the empty axiom policy (`Eta.eta_not_derivable`).
The sequent is stated with the kernel's canonical terms: `Eta.equation` is what
`SourceTerm.check` returns for the named source term `(λ x. f x) = f`, for every
binder name `x` (`Eta.check_sourceEquation`).
The interpretation `derives_translatedProvable` is therefore not complete: its
converse fails at eta.

## Route

The interpretation into `HOL.ExtDerivation` cannot separate eta from the
kernel, because that calculus proves eta.  The existing higher-order semantics
validate eta as well: Henkin models (`HOL.PreModel.denote`) and Kripke-Henkin
models (`Semantics/KripkeHenkinGeneral.lean`) interpret an arrow type by
functions, `λ x. f x` by `fun x => f x`, and equality pointwise, while
Heyting-valued models (`HOL.HeytingSem.HeytingGeneralModel`) require eta among
their equations.  The calculi `HOL.Derivation`, `HOL.ExtDerivation`, and
`HOL.ProofSyntax` each have an eta rule, so there is no eta-free calculus to
route the nine rules through.  A model that refutes eta is therefore built
here: **tagged functions**.

* An arrow value is a pair of a Boolean tag and a function (`Value`); base
  types have arbitrary carriers and `bool` is `Prop`.
* Abstraction produces the tag `false`, application uses the function
  component, and equality at every type is equality of values, so at an arrow
  type it compares tags and functions.

The model interprets the targets of the compositional translation
`TranslatesCompositionally` of `ExtensionalHOLInterpretation.lean`, and reuses
its syntactic lemmas: `instantiateAt` for `betaConv`, `closeFreeAt` and
`noConstOccurrence` for `abs`, `applyDB` for `subst`, and
`equalityDB`/`equalityDB_inv` for the equality rules.  The semantic lemmas
proved here are the matching laws of the tagged denotation: renaming and
substitution (`denote_subst`, `denote_instantiate`), abstraction of a
constant (`denote_abstractConstAt`, with `update`), constant substitution
(`denote_substConst`), and type substitution (`denote_mapTypes`, along the
tag-preserving `valueEquiv`).  The side condition of `abs` enters through
`denote_update_of_noConstOccurrence`: the abstracted variable does not occur
in the hypotheses, so reinterpreting it leaves them true.

`derives_taggedValid` is soundness of all nine rules for tagged functions.
In `taggedDefaultInterpretation` every symbol of arrow type carries the tag
`true`, so `λ x. f x` and `f` differ in their tags and eta fails.

As a positive control, the same interpretation validates the derivable beta
instance `⊢ (λ x. f x) y = f y` at the same variable
(`Eta.betaTheorem_derives_and_taggedDefaultInterpretation_holds`): the two
sides of eta agree at every argument and differ only in the tag.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

open Mettapedia.Logic

namespace TaggedFunctions

/-! ## Tagged-function values -/

section Generic

variable {B : Type} {C : HOL.Ty B → Type}

/-- Values of a simple type: propositions at `prop`, a chosen carrier at each
base type, and a Boolean tag paired with a function at each arrow type. -/
def Value (Carrier : B → Type) : HOL.Ty B → Type
  | .prop => Prop
  | .base b => Carrier b
  | .arr σ τ => Bool × (Value Carrier σ → Value Carrier τ)

/-- An interpretation of every constant symbol. -/
abbrev Interpretation (Carrier : B → Type) (C : HOL.Ty B → Type) : Type :=
  ∀ {τ : HOL.Ty B}, C τ → Value Carrier τ

/-- Values of the bound variables of a context. -/
abbrev Valuation (Carrier : B → Type) (Γ : HOL.Ctx B) : Type :=
  ∀ {τ : HOL.Ty B}, HOL.Var Γ τ → Value Carrier τ

variable {Carrier : B → Type}

/-- Extend a valuation by one innermost value. -/
def extend {Γ : HOL.Ctx B} {σ : HOL.Ty B} (ρ : Valuation Carrier Γ)
    (x : Value Carrier σ) : Valuation Carrier (σ :: Γ)
  | _, .vz => x
  | _, .vs v => ρ v

/-- The valuation of the empty context. -/
def emptyValuation (Carrier : B → Type) : Valuation Carrier [] :=
  fun v => nomatch v

theorem valuation_nil_eq (ρ : Valuation Carrier []) :
    @Eq (Valuation Carrier []) ρ (emptyValuation Carrier) := by
  funext τ v
  cases v

/-- Denotation.  Abstraction carries the tag `false`, application uses the
function component, and equality at every type is equality of values, so at
arrow types it compares tags as well as functions. -/
def denote (I : Interpretation Carrier C) :
    {Γ : HOL.Ctx B} → {τ : HOL.Ty B} → HOL.Term C Γ τ → Valuation Carrier Γ →
      Value Carrier τ
  | _, _, .var v, ρ => ρ v
  | _, _, .const c, _ => I c
  | _, _, .app f t, ρ => (denote I f ρ).2 (denote I t ρ)
  | _, _, .lam t, ρ => (false, fun x => denote I t (extend ρ x))
  | _, _, .top, _ => True
  | _, _, .bot, _ => False
  | _, _, .and φ ψ, ρ => denote I φ ρ ∧ denote I ψ ρ
  | _, _, .or φ ψ, ρ => denote I φ ρ ∨ denote I ψ ρ
  | _, _, .imp φ ψ, ρ => denote I φ ρ → denote I ψ ρ
  | _, _, .not φ, ρ => ¬ denote I φ ρ
  | _, _, .eq t u, ρ => denote I t ρ = denote I u ρ
  | _, _, .all φ, ρ => ∀ x, denote I φ (extend ρ x)
  | _, _, .ex φ, ρ => ∃ x, denote I φ (extend ρ x)

/-- A closed formula holds under an interpretation. -/
def Holds (I : Interpretation Carrier C) (φ : HOL.ClosedFormula C) : Prop :=
  denote I φ (emptyValuation Carrier)

section Unfolding

variable (I : Interpretation Carrier C) {Γ : HOL.Ctx B} (ρ : Valuation Carrier Γ)

theorem denote_app {σ τ : HOL.Ty B} (f : HOL.Term C Γ (.arr σ τ)) (t : HOL.Term C Γ σ) :
    denote I (.app f t) ρ = (denote I f ρ).2 (denote I t ρ) := rfl

theorem denote_and (φ ψ : HOL.Formula C Γ) :
    denote I (.and φ ψ) ρ = (denote I φ ρ ∧ denote I ψ ρ) := rfl

theorem denote_or (φ ψ : HOL.Formula C Γ) :
    denote I (.or φ ψ) ρ = (denote I φ ρ ∨ denote I ψ ρ) := rfl

theorem denote_imp (φ ψ : HOL.Formula C Γ) :
    denote I (.imp φ ψ) ρ = (denote I φ ρ → denote I ψ ρ) := rfl

theorem denote_not (φ : HOL.Formula C Γ) :
    denote I (.not φ) ρ = ¬ denote I φ ρ := rfl

theorem denote_eq {τ : HOL.Ty B} (t u : HOL.Term C Γ τ) :
    denote I (.eq t u) ρ = (denote I t ρ = denote I u ρ) := rfl

end Unfolding

/-! ## Renaming and substitution -/

theorem extend_lift_rename {Γ Δ : HOL.Ctx B} {σ : HOL.Ty B}
    (r : HOL.Rename B Γ Δ) (ν : Valuation Carrier Δ) (x : Value Carrier σ) :
    @Eq (Valuation Carrier (σ :: Γ)) (fun v => extend ν x (HOL.Rename.lift r v))
      (extend (fun v => ν (r v)) x) := by
  funext τ v
  cases v <;> rfl

theorem denote_rename (I : Interpretation Carrier C) {Γ : HOL.Ctx B} {τ : HOL.Ty B}
    (t : HOL.Term C Γ τ) :
    ∀ {Δ : HOL.Ctx B} (r : HOL.Rename B Γ Δ) (ν : Valuation Carrier Δ),
      denote I (HOL.rename r t) ν = denote I t (fun v => ν (r v)) := by
  induction t with
  | var v => intro Δ r ν; rfl
  | const c => intro Δ r ν; rfl
  | app f t ihf iht =>
      intro Δ r ν
      show (denote I (HOL.rename r f) ν).2 (denote I (HOL.rename r t) ν) = _
      rw [ihf r ν, iht r ν]
      rfl
  | lam t ih =>
      intro Δ r ν
      refine congrArg (Prod.mk false) (funext fun x => ?_)
      show denote I (HOL.rename (HOL.Rename.lift r) t) (extend ν x) =
        denote I t (extend (fun v => ν (r v)) x)
      rw [ih (HOL.Rename.lift r) (extend ν x), extend_lift_rename]
  | top => intro Δ r ν; rfl
  | bot => intro Δ r ν; rfl
  | and φ ψ ihφ ihψ =>
      intro Δ r ν
      show (denote I (HOL.rename r φ) ν ∧ denote I (HOL.rename r ψ) ν) = _
      rw [ihφ r ν, ihψ r ν]
      rfl
  | or φ ψ ihφ ihψ =>
      intro Δ r ν
      show (denote I (HOL.rename r φ) ν ∨ denote I (HOL.rename r ψ) ν) = _
      rw [ihφ r ν, ihψ r ν]
      rfl
  | imp φ ψ ihφ ihψ =>
      intro Δ r ν
      show (denote I (HOL.rename r φ) ν → denote I (HOL.rename r ψ) ν) = _
      rw [ihφ r ν, ihψ r ν]
      rfl
  | not φ ih =>
      intro Δ r ν
      show (¬ denote I (HOL.rename r φ) ν) = _
      rw [ih r ν]
      rfl
  | eq t u iht ihu =>
      intro Δ r ν
      show (denote I (HOL.rename r t) ν = denote I (HOL.rename r u) ν) = _
      rw [iht r ν, ihu r ν]
      rfl
  | all φ ih =>
      intro Δ r ν
      show (∀ x, denote I (HOL.rename (HOL.Rename.lift r) φ) (extend ν x)) =
        ∀ x, denote I φ (extend (fun v => ν (r v)) x)
      refine forall_congr fun x => ?_
      rw [ih (HOL.Rename.lift r) (extend ν x), extend_lift_rename]
  | ex φ ih =>
      intro Δ r ν
      show (∃ x, denote I (HOL.rename (HOL.Rename.lift r) φ) (extend ν x)) =
        ∃ x, denote I φ (extend (fun v => ν (r v)) x)
      refine congrArg Exists (funext fun x => ?_)
      rw [ih (HOL.Rename.lift r) (extend ν x), extend_lift_rename]

theorem denote_weaken (I : Interpretation Carrier C) {Γ : HOL.Ctx B} {σ τ : HOL.Ty B}
    (t : HOL.Term C Γ τ) (ρ : Valuation Carrier Γ) (x : Value Carrier σ) :
    denote I (HOL.weaken (σ := σ) t) (extend ρ x) = denote I t ρ :=
  denote_rename I t HOL.Rename.weaken (extend ρ x)

theorem extend_lift_subst (I : Interpretation Carrier C) {Γ Δ : HOL.Ctx B} {σ : HOL.Ty B}
    (s : HOL.Subst C Γ Δ) (ν : Valuation Carrier Δ) (x : Value Carrier σ) :
    @Eq (Valuation Carrier (σ :: Γ)) (fun v => denote I (HOL.Subst.lift s v) (extend ν x))
      (extend (fun v => denote I (s v) ν) x) := by
  funext τ v
  cases v with
  | vz => rfl
  | vs v => exact denote_weaken I (s v) ν x

theorem denote_subst (I : Interpretation Carrier C) {Γ : HOL.Ctx B} {τ : HOL.Ty B}
    (t : HOL.Term C Γ τ) :
    ∀ {Δ : HOL.Ctx B} (s : HOL.Subst C Γ Δ) (ν : Valuation Carrier Δ),
      denote I (HOL.subst s t) ν = denote I t (fun v => denote I (s v) ν) := by
  induction t with
  | var v => intro Δ s ν; rfl
  | const c => intro Δ s ν; rfl
  | app f t ihf iht =>
      intro Δ s ν
      show (denote I (HOL.subst s f) ν).2 (denote I (HOL.subst s t) ν) = _
      rw [ihf s ν, iht s ν]
      rfl
  | lam t ih =>
      intro Δ s ν
      refine congrArg (Prod.mk false) (funext fun x => ?_)
      show denote I (HOL.subst (HOL.Subst.lift s) t) (extend ν x) =
        denote I t (extend (fun v => denote I (s v) ν) x)
      rw [ih (HOL.Subst.lift s) (extend ν x), extend_lift_subst]
  | top => intro Δ s ν; rfl
  | bot => intro Δ s ν; rfl
  | and φ ψ ihφ ihψ =>
      intro Δ s ν
      show (denote I (HOL.subst s φ) ν ∧ denote I (HOL.subst s ψ) ν) = _
      rw [ihφ s ν, ihψ s ν]
      rfl
  | or φ ψ ihφ ihψ =>
      intro Δ s ν
      show (denote I (HOL.subst s φ) ν ∨ denote I (HOL.subst s ψ) ν) = _
      rw [ihφ s ν, ihψ s ν]
      rfl
  | imp φ ψ ihφ ihψ =>
      intro Δ s ν
      show (denote I (HOL.subst s φ) ν → denote I (HOL.subst s ψ) ν) = _
      rw [ihφ s ν, ihψ s ν]
      rfl
  | not φ ih =>
      intro Δ s ν
      show (¬ denote I (HOL.subst s φ) ν) = _
      rw [ih s ν]
      rfl
  | eq t u iht ihu =>
      intro Δ s ν
      show (denote I (HOL.subst s t) ν = denote I (HOL.subst s u) ν) = _
      rw [iht s ν, ihu s ν]
      rfl
  | all φ ih =>
      intro Δ s ν
      show (∀ x, denote I (HOL.subst (HOL.Subst.lift s) φ) (extend ν x)) =
        ∀ x, denote I φ (extend (fun v => denote I (s v) ν) x)
      refine forall_congr fun x => ?_
      rw [ih (HOL.Subst.lift s) (extend ν x), extend_lift_subst]
  | ex φ ih =>
      intro Δ s ν
      show (∃ x, denote I (HOL.subst (HOL.Subst.lift s) φ) (extend ν x)) =
        ∃ x, denote I φ (extend (fun v => denote I (s v) ν) x)
      refine congrArg Exists (funext fun x => ?_)
      rw [ih (HOL.Subst.lift s) (extend ν x), extend_lift_subst]

/-- The beta law of the semantics. -/
theorem denote_instantiate (I : Interpretation Carrier C) {Γ : HOL.Ctx B}
    {σ τ : HOL.Ty B} (u : HOL.Term C Γ σ) (t : HOL.Term C (σ :: Γ) τ)
    (ν : Valuation Carrier Γ) :
    denote I (HOL.instantiate u t) ν = denote I t (extend ν (denote I u ν)) := by
  unfold HOL.instantiate
  rw [denote_subst]
  congr 1
  funext τ v
  cases v <;> rfl

/-! ## Closed-term weakening and constant substitution -/

theorem denote_weakenCtx (I : Interpretation Carrier C) {τ : HOL.Ty B}
    (t : HOL.ClosedTerm C τ) :
    ∀ (Γ : HOL.Ctx B) (ρ : Valuation Carrier Γ),
      denote I (HOL.weakenCtx Γ t) ρ = denote I t (emptyValuation Carrier)
  | [], ρ => congrArg (denote I t) (valuation_nil_eq ρ)
  | _ :: Γ, ρ =>
      (denote_rename I (HOL.weakenCtx Γ t) HOL.Rename.weaken ρ).trans
        (denote_weakenCtx I t Γ _)

section ConstantSubstitution

variable {C' : HOL.Ty B → Type}

/-- The interpretation of source constants induced by a closed-term
substitution `images` and an interpretation of the target constants. -/
def constantReduct (images : ∀ {τ : HOL.Ty B}, C τ → HOL.ClosedTerm C' τ)
    (I : Interpretation Carrier C') : Interpretation Carrier C :=
  fun c => denote I (images c) (emptyValuation Carrier)

theorem denote_substConst (images : ∀ {τ : HOL.Ty B}, C τ → HOL.ClosedTerm C' τ)
    (I : Interpretation Carrier C') {Γ : HOL.Ctx B} {τ : HOL.Ty B}
    (t : HOL.Term C Γ τ) :
    ∀ ρ : Valuation Carrier Γ,
      denote I (HOL.substConst images t) ρ = denote (constantReduct images I) t ρ := by
  induction t with
  | var v => intro ρ; rfl
  | const c => intro ρ; exact denote_weakenCtx I (images c) _ ρ
  | app f t ihf iht =>
      intro ρ
      show (denote I (HOL.substConst images f) ρ).2 (denote I (HOL.substConst images t) ρ) = _
      rw [ihf ρ, iht ρ]
      rfl
  | lam t ih =>
      intro ρ
      exact congrArg (Prod.mk false) (funext fun x => ih (extend ρ x))
  | top => intro ρ; rfl
  | bot => intro ρ; rfl
  | and φ ψ ihφ ihψ =>
      intro ρ
      show (denote I (HOL.substConst images φ) ρ ∧ denote I (HOL.substConst images ψ) ρ) = _
      rw [ihφ ρ, ihψ ρ]
      rfl
  | or φ ψ ihφ ihψ =>
      intro ρ
      show (denote I (HOL.substConst images φ) ρ ∨ denote I (HOL.substConst images ψ) ρ) = _
      rw [ihφ ρ, ihψ ρ]
      rfl
  | imp φ ψ ihφ ihψ =>
      intro ρ
      show (denote I (HOL.substConst images φ) ρ → denote I (HOL.substConst images ψ) ρ) = _
      rw [ihφ ρ, ihψ ρ]
      rfl
  | not φ ih =>
      intro ρ
      show (¬ denote I (HOL.substConst images φ) ρ) = _
      rw [ih ρ]
      rfl
  | eq t u iht ihu =>
      intro ρ
      show (denote I (HOL.substConst images t) ρ = denote I (HOL.substConst images u) ρ) = _
      rw [iht ρ, ihu ρ]
      rfl
  | all φ ih =>
      intro ρ
      exact forall_congr fun x => ih (extend ρ x)
  | ex φ ih =>
      intro ρ
      exact congrArg Exists (funext fun x => ih (extend ρ x))

end ConstantSubstitution

/-! ## Reinterpreting one constant -/

open Classical in
/-- Reinterpret the constant `c` as `value`, leaving every other constant. -/
noncomputable def update (I : Interpretation Carrier C) {σ : HOL.Ty B} (c : C σ)
    (value : Value Carrier σ) : Interpretation Carrier C :=
  fun {τ} d =>
    if h : (⟨τ, d⟩ : Sigma C) = ⟨σ, c⟩ then
      cast (congrArg (Value Carrier) (congrArg Sigma.fst h).symm) value
    else I d

theorem update_self (I : Interpretation Carrier C) {σ : HOL.Ty B} (c : C σ)
    (value : Value Carrier σ) : update I c value c = value := by
  unfold update
  rw [dif_pos rfl]
  rfl

theorem update_of_ne (I : Interpretation Carrier C) {σ τ : HOL.Ty B} (c : C σ)
    (value : Value Carrier σ) {d : C τ} (different : (⟨τ, d⟩ : Sigma C) ≠ ⟨σ, c⟩) :
    update I c value d = I d := by
  unfold update
  rw [dif_neg different]

/-- Reinterpreting a constant that does not occur leaves the denotation. -/
theorem denote_update_of_noConstOccurrence (I : Interpretation Carrier C)
    {σ : HOL.Ty B} (c : C σ) (value : Value Carrier σ) {Γ : HOL.Ctx B}
    {τ : HOL.Ty B} {t : HOL.Term C Γ τ} (absent : HOL.NoConstOccurrence c t) :
    ∀ ρ : Valuation Carrier Γ, denote (update I c value) t ρ = denote I t ρ := by
  induction absent with
  | var => intro ρ; rfl
  | const_diff_type different d =>
      intro ρ
      exact update_of_ne I c value fun h => different (congrArg Sigma.fst h).symm
  | const_same_ne d different =>
      intro ρ
      exact update_of_ne I c value fun h => different (eq_of_heq (Sigma.mk.inj h).2)
  | app _ _ ihf iht =>
      intro ρ
      rw [denote_app, denote_app, ihf ρ, iht ρ]
  | lam _ ih =>
      intro ρ
      exact congrArg (Prod.mk false) (funext fun x => ih (extend ρ x))
  | top => intro ρ; rfl
  | bot => intro ρ; rfl
  | and _ _ ihφ ihψ =>
      intro ρ
      rw [denote_and, denote_and, ihφ ρ, ihψ ρ]
  | or _ _ ihφ ihψ =>
      intro ρ
      rw [denote_or, denote_or, ihφ ρ, ihψ ρ]
  | imp _ _ ihφ ihψ =>
      intro ρ
      rw [denote_imp, denote_imp, ihφ ρ, ihψ ρ]
  | not _ ih =>
      intro ρ
      rw [denote_not, denote_not, ih ρ]
  | eq _ _ iht ihu =>
      intro ρ
      rw [denote_eq, denote_eq, iht ρ, ihu ρ]
  | all _ ih =>
      intro ρ
      exact forall_congr fun x => ih (extend ρ x)
  | ex _ ih =>
      intro ρ
      exact congrArg Exists (funext fun x => ih (extend ρ x))

/-- Abstracting the constant `c` into the binder at depth `Ξ` reads that
binder's value as the reinterpretation of `c`. -/
theorem denote_abstractConstAt (I : Interpretation Carrier C) {σ : HOL.Ty B}
    (c : C σ) {Γ : HOL.Ctx B} :
    ∀ (Ξ : HOL.Ctx B) {τ : HOL.Ty B} (t : HOL.Term C (Ξ ++ Γ) τ)
      (ρ : Valuation Carrier (Ξ ++ σ :: Γ)),
      denote I (HOL.abstractConstAt c Ξ t) ρ =
        denote (update I c (ρ (HOL.varAtDepth Ξ))) t (fun v => ρ (HOL.insertRen Ξ v))
  | Ξ, _, .var v, ρ => by
      rw [HOL.ExtDerivation.abstractConstAt_var]
      rfl
  | Ξ, _, .const d, ρ => by
      rw [HOL.abstractConstAt]
      by_cases same : (⟨_, d⟩ : Sigma C) = ⟨σ, c⟩
      · rw [dif_pos same]
        cases same
        rw [cast_eq]
        exact (update_self I c _).symm
      · rw [dif_neg same]
        exact (update_of_ne I c _ same).symm
  | Ξ, _, .app f t, ρ => by
      rw [HOL.ExtDerivation.abstractConstAt_app]
      show (denote I (HOL.abstractConstAt c Ξ f) ρ).2
          (denote I (HOL.abstractConstAt c Ξ t) ρ) = _
      rw [denote_abstractConstAt I c Ξ f ρ, denote_abstractConstAt I c Ξ t ρ]
      rfl
  | Ξ, _, .lam body, ρ => by
      rw [HOL.ExtDerivation.abstractConstAt_lam]
      refine congrArg (Prod.mk false) (funext fun x => ?_)
      exact (denote_abstractConstAt I c (_ :: Ξ) body (extend ρ x)).trans
        (congrArg (denote (update I c (ρ (HOL.varAtDepth Ξ))) body)
          (extend_lift_rename (HOL.insertRen Ξ) ρ x))
  | Ξ, _, .top, ρ => by
      rw [HOL.abstractConstAt]
      rfl
  | Ξ, _, .bot, ρ => by
      rw [HOL.abstractConstAt]
      rfl
  | Ξ, _, .and φ ψ, ρ => by
      rw [HOL.abstractConstAt]
      show (denote I (HOL.abstractConstAt c Ξ φ) ρ ∧
          denote I (HOL.abstractConstAt c Ξ ψ) ρ) = _
      rw [denote_abstractConstAt I c Ξ φ ρ, denote_abstractConstAt I c Ξ ψ ρ]
      rfl
  | Ξ, _, .or φ ψ, ρ => by
      rw [HOL.abstractConstAt]
      show (denote I (HOL.abstractConstAt c Ξ φ) ρ ∨
          denote I (HOL.abstractConstAt c Ξ ψ) ρ) = _
      rw [denote_abstractConstAt I c Ξ φ ρ, denote_abstractConstAt I c Ξ ψ ρ]
      rfl
  | Ξ, _, .imp φ ψ, ρ => by
      rw [HOL.abstractConstAt]
      show (denote I (HOL.abstractConstAt c Ξ φ) ρ →
          denote I (HOL.abstractConstAt c Ξ ψ) ρ) = _
      rw [denote_abstractConstAt I c Ξ φ ρ, denote_abstractConstAt I c Ξ ψ ρ]
      rfl
  | Ξ, _, .not φ, ρ => by
      rw [HOL.abstractConstAt]
      show (¬ denote I (HOL.abstractConstAt c Ξ φ) ρ) = _
      rw [denote_abstractConstAt I c Ξ φ ρ]
      rfl
  | Ξ, _, .eq t u, ρ => by
      rw [HOL.ExtDerivation.abstractConstAt_eq]
      show (denote I (HOL.abstractConstAt c Ξ t) ρ =
          denote I (HOL.abstractConstAt c Ξ u) ρ) = _
      rw [denote_abstractConstAt I c Ξ t ρ, denote_abstractConstAt I c Ξ u ρ]
      rfl
  | Ξ, _, .all body, ρ => by
      rw [HOL.ExtDerivation.abstractConstAt_all]
      exact forall_congr fun x =>
        (denote_abstractConstAt I c (_ :: Ξ) body (extend ρ x)).trans
          (congrArg (denote (update I c (ρ (HOL.varAtDepth Ξ))) body)
            (extend_lift_rename (HOL.insertRen Ξ) ρ x))
  | Ξ, _, .ex body, ρ => by
      rw [HOL.abstractConstAt]
      exact congrArg Exists (funext fun x =>
        (denote_abstractConstAt I c (_ :: Ξ) body (extend ρ x)).trans
          (congrArg (denote (update I c (ρ (HOL.varAtDepth Ξ))) body)
            (extend_lift_rename (HOL.insertRen Ξ) ρ x)))
  termination_by Ξ _ t _ => sizeOf t

end Generic

/-! ## Type substitution -/

section TypeSubstitution

variable {B B' : Type} {C : HOL.Ty B → Type} {C' : HOL.Ty B' → Type}
  (θ : B → HOL.Ty B') (constants : ∀ {a : HOL.Ty B}, C a → C' (HOL.Ty.substitute θ a))
  {Carrier : B' → Type}

/-- Values at a substituted type agree with values under the substituted
carriers.  Arrow values keep their tag. -/
def valueEquiv (Carrier : B' → Type) :
    (a : HOL.Ty B) →
      Value (fun b => Value Carrier (θ b)) a ≃ Value Carrier (HOL.Ty.substitute θ a)
  | .prop => Equiv.refl _
  | .base _ => Equiv.refl _
  | .arr a b => Equiv.prodCongr (Equiv.refl Bool)
      (Equiv.arrowCongr (valueEquiv Carrier a) (valueEquiv Carrier b))

theorem valueEquiv_app {a b : HOL.Ty B}
    (f : Value (fun c => Value Carrier (θ c)) (.arr a b))
    (x : Value (fun c => Value Carrier (θ c)) a) :
    valueEquiv θ Carrier b (f.2 x) =
      (valueEquiv θ Carrier (.arr a b) f).2 (valueEquiv θ Carrier a x) := by
  change _ = valueEquiv θ Carrier b
    (f.2 ((valueEquiv θ Carrier a).symm (valueEquiv θ Carrier a x)))
  rw [Equiv.symm_apply_apply]

/-- The source interpretation induced by a type substitution. -/
def typeReductInterpretation (I : Interpretation Carrier C') :
    Interpretation (fun b => Value Carrier (θ b)) C :=
  fun {a} c => (valueEquiv θ Carrier a).symm (I (constants c))

/-- Pull a valuation back along a type substitution. -/
def typeReductValuation {Γ : HOL.Ctx B}
    (ρ : Valuation Carrier (Γ.map (HOL.Ty.substitute θ))) :
    Valuation (fun b => Value Carrier (θ b)) Γ :=
  fun {a} x => (valueEquiv θ Carrier a).symm (ρ (x.mapTypes θ))

theorem typeReductValuation_extend {Γ : HOL.Ctx B} {a : HOL.Ty B}
    (ρ : Valuation Carrier (Γ.map (HOL.Ty.substitute θ)))
    (x : Value Carrier (HOL.Ty.substitute θ a)) :
    @Eq (Valuation (fun b => Value Carrier (θ b)) (a :: Γ))
      (typeReductValuation θ (Γ := a :: Γ) (extend ρ x))
      (extend (typeReductValuation θ ρ) ((valueEquiv θ Carrier a).symm x)) := by
  funext b y
  cases y <;> rfl

theorem denote_mapTypes (I : Interpretation Carrier C') {Γ : HOL.Ctx B} {a : HOL.Ty B}
    (t : HOL.Term C Γ a) (ρ : Valuation Carrier (Γ.map (HOL.Ty.substitute θ))) :
    valueEquiv θ Carrier a
        (denote (typeReductInterpretation θ constants I) t (typeReductValuation θ ρ)) =
      denote I (HOL.mapTypes θ constants t) ρ := by
  induction t with
  | var x => exact Equiv.apply_symm_apply _ _
  | const c => exact Equiv.apply_symm_apply _ _
  | app f t ihf iht =>
      show _ = (denote I (HOL.mapTypes θ constants f) ρ).2
        (denote I (HOL.mapTypes θ constants t) ρ)
      rw [← ihf ρ, ← iht ρ]
      exact valueEquiv_app θ _ _
  | lam t ih =>
      refine congrArg (Prod.mk false) (funext fun y => ?_)
      have h := ih (extend ρ y)
      rw [typeReductValuation_extend] at h
      exact h
  | top => rfl
  | bot => rfl
  | and φ ψ ihφ ihψ => exact congrArg₂ And (ihφ ρ) (ihψ ρ)
  | or φ ψ ihφ ihψ => exact congrArg₂ Or (ihφ ρ) (ihψ ρ)
  | imp φ ψ ihφ ihψ => exact congrArg₂ (fun p q : Prop => p → q) (ihφ ρ) (ihψ ρ)
  | not φ ih => exact congrArg Not (ih ρ)
  | eq t u iht ihu =>
      show (_ = _) = (denote I (HOL.mapTypes θ constants t) ρ =
        denote I (HOL.mapTypes θ constants u) ρ)
      rw [← iht ρ, ← ihu ρ]
      exact propext (Equiv.apply_eq_iff_eq _).symm
  | all φ ih =>
      apply propext
      constructor
      · intro holds y
        have h := ih (extend ρ y)
        rw [typeReductValuation_extend] at h
        exact h.mp (holds _)
      · intro holds x
        have h := ih (extend ρ (valueEquiv θ Carrier _ x))
        rw [typeReductValuation_extend, Equiv.symm_apply_apply] at h
        exact h.mpr (holds _)
  | ex φ ih =>
      apply propext
      constructor
      · rintro ⟨x, holds⟩
        have h := ih (extend ρ (valueEquiv θ Carrier _ x))
        rw [typeReductValuation_extend, Equiv.symm_apply_apply] at h
        exact ⟨_, h.mp holds⟩
      · rintro ⟨y, holds⟩
        have h := ih (extend ρ y)
        rw [typeReductValuation_extend] at h
        exact ⟨_, h.mpr holds⟩

end TypeSubstitution

/-! ## Validity of OpenTheory sequents -/

section Kernel

/-- A sequent is valid for tagged functions when its compositionally
translated conclusion holds in every tagged-function interpretation in which
its translated hypotheses hold. -/
def TaggedValid (sequent : Sequent) : Prop :=
  ∃ φ, TranslatesCompositionally [] sequent.concl.term .prop φ ∧
    ∀ (Carrier : AtomicTy → Type) (I : Interpretation Carrier Symbol),
      (∀ ψ ∈ compositionalHypotheses sequent.hyp, Holds I ψ) → Holds I φ

theorem holds_equalityLambda_app_app {Carrier : AtomicTy → Type}
    (I : Interpretation Carrier Symbol) {σ : HOL.Ty AtomicTy}
    (left right : HOL.ClosedTerm Symbol σ) :
    Holds I (.app (.app (equalityLambda σ) left) right) =
      (denote I left (emptyValuation Carrier) = denote I right (emptyValuation Carrier)) :=
  rfl

theorem taggedValid_assume {term : CanonicalTerm} (hbool : term.IsBool) :
    TaggedValid ⟨{term}, term⟩ := by
  obtain ⟨φ, hφ⟩ := CanonicalTerm.exists_formula hbool
  exact ⟨φ, hφ, fun _ _ hypotheses =>
    hypotheses φ ⟨term, Finset.mem_singleton_self term, hφ⟩⟩

theorem taggedValid_refl {term equality : CanonicalTerm}
    (construction : CanonicalTerm.EqualityConstructionSemantics term term equality) :
    TaggedValid ⟨∅, equality⟩ := by
  obtain ⟨target, htarget⟩ := term.exists_translation
  refine ⟨_, by rw [construction.2]; exact .equalityDB rfl htarget htarget, ?_⟩
  intro _ _ _
  rfl

theorem taggedValid_betaConv {redex reduced equality : CanonicalTerm}
    (reduction : CanonicalTerm.BetaReductionSemantics redex reduced)
    (construction : CanonicalTerm.EqualityConstructionSemantics redex reduced equality) :
    TaggedValid ⟨∅, equality⟩ := by
  obtain ⟨domain, body, argument, hredex, hreduced⟩ := reduction
  obtain ⟨target, htarget⟩ := redex.exists_translation
  have htarget' := htarget.of_term_eq hredex
  cases htarget' with
  | app hlambda hargument =>
      cases hlambda with
      | abs typed hbody =>
          have hinstance := TranslatesCompositionally.instantiateAt hargument
            (Ξ := []) hbody
          have hreducedTranslation := hinstance.of_term_eq hreduced.symm
          refine ⟨_, by
            rw [construction.2]
            exact .equalityDB rfl htarget hreducedTranslation, ?_⟩
          intro Carrier I _
          exact (denote_instantiate I _ _ _).symm

theorem taggedValid_app {functionEquality argumentEquality : Theorem}
    {functionLeft functionRight argumentLeft argumentRight applicationLeft
      applicationRight equality : CanonicalTerm}
    (functionView : CanonicalTerm.EqualityViewSemantics
      functionEquality.sequent.concl functionLeft functionRight)
    (argumentView : CanonicalTerm.EqualityViewSemantics
      argumentEquality.sequent.concl argumentLeft argumentRight)
    (leftApplication : CanonicalTerm.ApplicationSemantics
      functionLeft argumentLeft applicationLeft)
    (rightApplication : CanonicalTerm.ApplicationSemantics
      functionRight argumentRight applicationRight)
    (construction : CanonicalTerm.EqualityConstructionSemantics
      applicationLeft applicationRight equality)
    (functionValid : TaggedValid functionEquality.sequent)
    (argumentValid : TaggedValid argumentEquality.sequent) :
    TaggedValid ⟨functionEquality.sequent.hyp ∪ argumentEquality.sequent.hyp, equality⟩ := by
  obtain ⟨φf, hφf, vf⟩ := functionValid
  obtain ⟨σf, fl, fr, hσf, hfl, hfr, rfl⟩ :=
    (hφf.of_term_eq functionView.2).equalityDB_inv
  obtain ⟨φx, hφx, vx⟩ := argumentValid
  obtain ⟨σx, xl, xr, hσx, hxl, hxr, rfl⟩ :=
    (hφx.of_term_eq argumentView.2).equalityDB_inv
  obtain ⟨domain, codomain, hdest, hdomain, hleftTerm⟩ := leftApplication
  obtain ⟨domain', codomain', hdest', hdomain', hrightTerm⟩ := rightApplication
  have hfunctionTy := Ty.eq_function_of_destFunction? hdest
  have hfunctionTy' := Ty.eq_function_of_destFunction? hdest'
  rw [← functionView.1, hfunctionTy] at hfunctionTy'
  obtain ⟨rfl, rfl⟩ := Ty.function_inj hfunctionTy'
  have hσf' : σf = .arr domain.toHOL codomain.toHOL := by
    rw [← hσf, hfunctionTy, Ty.toHOL_function]
  subst hσf'
  have hσx' : σx = domain.toHOL := by rw [← hσx, hdomain]
  subst hσx'
  have hleft : TranslatesCompositionally [] applicationLeft.term codomain.toHOL
      (.app fl xl) := (TranslatesCompositionally.app hfl hxl).of_term_eq hleftTerm.symm
  have hright : TranslatesCompositionally [] applicationRight.term codomain.toHOL
      (.app fr xr) := (TranslatesCompositionally.app hfr hxr).of_term_eq hrightTerm.symm
  refine ⟨_, (TranslatesCompositionally.equalityDB
    (CanonicalTerm.toHOL_ty_of_translation hleft) hleft hright).of_term_eq
      construction.2.symm, ?_⟩
  intro Carrier I hypotheses
  have hf : denote I fl (emptyValuation Carrier) = denote I fr (emptyValuation Carrier) :=
    vf Carrier I fun ψ hψ =>
      hypotheses ψ (compositionalHypotheses_mono Finset.subset_union_left hψ)
  have hx : denote I xl (emptyValuation Carrier) = denote I xr (emptyValuation Carrier) :=
    vx Carrier I fun ψ hψ =>
      hypotheses ψ (compositionalHypotheses_mono Finset.subset_union_right hψ)
  rw [holds_equalityLambda_app_app, denote_app, denote_app, hf, hx]

/-- Discharging a hypothesis: the remaining hypotheses and the discharged one
give back every hypothesis of the premise. -/
theorem holds_hypotheses_of_erase {Carrier : AtomicTy → Type}
    {I : Interpretation Carrier Symbol} {hyp : Finset CanonicalTerm}
    {discharged : CanonicalTerm} {p : HOL.ClosedFormula Symbol}
    (hp : TranslatesCompositionally [] discharged.term .prop p)
    (remaining : ∀ ψ ∈ compositionalHypotheses (hyp.erase discharged), Holds I ψ)
    (holdsP : Holds I p) :
    ∀ ψ ∈ compositionalHypotheses hyp, Holds I ψ := by
  rintro ψ ⟨term, hterm, hψ⟩
  by_cases same : term = discharged
  · subst same
    rw [hψ.unique_eq hp]
    exact holdsP
  · exact remaining ψ ⟨term, Finset.mem_erase.mpr ⟨same, hterm⟩, hψ⟩

theorem taggedValid_deductAntisym {left right : Theorem} {equality : CanonicalTerm}
    (construction : CanonicalTerm.EqualityConstructionSemantics
      left.sequent.concl right.sequent.concl equality)
    (leftValid : TaggedValid left.sequent) (rightValid : TaggedValid right.sequent) :
    TaggedValid
      ⟨(left.sequent.hyp.erase right.sequent.concl) ∪
          (right.sequent.hyp.erase left.sequent.concl), equality⟩ := by
  obtain ⟨p, hp, vp⟩ := leftValid
  obtain ⟨q, hq, vq⟩ := rightValid
  refine ⟨_, (TranslatesCompositionally.equalityDB
    (CanonicalTerm.toHOL_ty_of_translation hp) hp hq).of_term_eq
      construction.2.symm, ?_⟩
  intro Carrier I hypotheses
  rw [holds_equalityLambda_app_app]
  apply propext
  constructor
  · intro holdsP
    exact vq Carrier I (holds_hypotheses_of_erase hp
      (fun ψ hψ => hypotheses ψ (compositionalHypotheses_mono Finset.subset_union_right hψ))
      holdsP)
  · intro holdsQ
    exact vp Carrier I (holds_hypotheses_of_erase hq
      (fun ψ hψ => hypotheses ψ (compositionalHypotheses_mono Finset.subset_union_left hψ))
      holdsQ)

theorem taggedValid_eqMp {equality premise : Theorem} {left right : CanonicalTerm}
    (view : CanonicalTerm.EqualityViewSemantics equality.sequent.concl left right)
    (hmatch : left = premise.sequent.concl)
    (equalityValid : TaggedValid equality.sequent)
    (premiseValid : TaggedValid premise.sequent) :
    TaggedValid ⟨equality.sequent.hyp ∪ premise.sequent.hyp, right⟩ := by
  obtain ⟨φe, hφe, ve⟩ := equalityValid
  obtain ⟨σ, l, r, hσ, hl, hr, rfl⟩ := (hφe.of_term_eq view.2).equalityDB_inv
  obtain ⟨φp, hφp, vp⟩ := premiseValid
  subst hmatch
  obtain ⟨rfl, hheq⟩ := hl.unique hφp
  cases hheq
  refine ⟨r, hr, ?_⟩
  intro Carrier I hypotheses
  have hequal : denote I φp (emptyValuation Carrier) = denote I r (emptyValuation Carrier) :=
    ve Carrier I fun ψ hψ =>
      hypotheses ψ (compositionalHypotheses_mono Finset.subset_union_left hψ)
  have holdsL : Holds I φp :=
    vp Carrier I fun ψ hψ =>
      hypotheses ψ (compositionalHypotheses_mono Finset.subset_union_right hψ)
  exact hequal.mp holdsL

theorem taggedValid_abs {sourceVar : SourceVar} {input : Theorem}
    {left right leftAbs rightAbs equality : CanonicalTerm}
    (fresh : ¬ FreeInHypotheses sourceVar input.sequent.hyp)
    (view : CanonicalTerm.EqualityViewSemantics input.sequent.concl left right)
    (leftAbstraction : CanonicalTerm.AbstractionSemantics sourceVar left leftAbs)
    (rightAbstraction : CanonicalTerm.AbstractionSemantics sourceVar right rightAbs)
    (construction : CanonicalTerm.EqualityConstructionSemantics leftAbs rightAbs equality)
    (inputValid : TaggedValid input.sequent) :
    TaggedValid ⟨input.sequent.hyp, equality⟩ := by
  obtain ⟨φ, hφ, valid⟩ := inputValid
  obtain ⟨σ, l, r, hσ, hl, hr, rfl⟩ := (hφ.of_term_eq view.2).equalityDB_inv
  have hleftAbs : TranslatesCompositionally [] leftAbs.term
      (.arr sourceVar.ty.toHOL σ)
      (.lam (HOL.abstractConstAt (Γ := []) (Symbol.ofVar sourceVar) [] l)) :=
    (TranslatesCompositionally.abs rfl
      (TranslatesCompositionally.closeFreeAt sourceVar (Ξ := []) hl)).of_term_eq
        leftAbstraction.symm
  have hrightAbs : TranslatesCompositionally [] rightAbs.term
      (.arr sourceVar.ty.toHOL σ)
      (.lam (HOL.abstractConstAt (Γ := []) (Symbol.ofVar sourceVar) [] r)) :=
    (TranslatesCompositionally.abs rfl
      (TranslatesCompositionally.closeFreeAt sourceVar (Ξ := []) hr)).of_term_eq
        rightAbstraction.symm
  refine ⟨_, (TranslatesCompositionally.equalityDB
    (CanonicalTerm.toHOL_ty_of_translation hleftAbs) hleftAbs hrightAbs).of_term_eq
      construction.2.symm, ?_⟩
  intro Carrier I hypotheses
  rw [holds_equalityLambda_app_app]
  refine congrArg (Prod.mk false) (funext fun x => ?_)
  have hleft := denote_abstractConstAt I (Symbol.ofVar sourceVar) (Γ := []) [] l
    (extend (emptyValuation Carrier) x)
  have hright := denote_abstractConstAt I (Symbol.ofVar sourceVar) (Γ := []) [] r
    (extend (emptyValuation Carrier) x)
  rw [valuation_nil_eq] at hleft hright
  refine hleft.trans (Eq.trans ?_ hright.symm)
  apply valid Carrier (update I (Symbol.ofVar sourceVar) x)
  rintro ψ ⟨term, hterm, hψ⟩
  have absent := hψ.noConstOccurrence sourceVar fun found => fresh ⟨term, hterm, found⟩
  unfold Holds
  rw [denote_update_of_noConstOccurrence I _ x absent]
  exact hypotheses ψ ⟨term, hterm, hψ⟩

/-- The interpretation read back through the target image of an OpenTheory
substitution. -/
noncomputable def substitutionReduct (substitution : TypeCorrectTermSubstitution)
    {Carrier : AtomicTy → Type} (I : Interpretation Carrier Symbol) :
    Interpretation (fun b => Value Carrier (substitution.raw.types.baseInstance b)) Symbol :=
  typeReductInterpretation substitution.raw.types.baseInstance
    substitution.raw.types.symbolInstance (constantReduct substitution.symbolImage I)

theorem holds_targetMap (substitution : TypeCorrectTermSubstitution)
    {Carrier : AtomicTy → Type} (I : Interpretation Carrier Symbol)
    (φ : HOL.ClosedFormula Symbol) :
    Holds I (substitution.targetMap φ : HOL.ClosedFormula Symbol) =
      Holds (substitutionReduct substitution I) φ := by
  have hconstants := denote_substConst substitution.symbolImage I
    (HOL.mapTypes substitution.raw.types.baseInstance substitution.raw.types.symbolInstance φ)
    (emptyValuation Carrier)
  have htypes := denote_mapTypes substitution.raw.types.baseInstance
    substitution.raw.types.symbolInstance (constantReduct substitution.symbolImage I) φ
    (emptyValuation Carrier)
  rw [valuation_nil_eq (typeReductValuation _ _)] at htypes
  exact hconstants.trans htypes.symm

theorem taggedValid_subst (substitution : TypeCorrectTermSubstitution) {input : Theorem}
    (inputValid : TaggedValid input.sequent) :
    TaggedValid
      ⟨substitution.applyHypotheses input.sequent.hyp,
        substitution.apply input.sequent.concl⟩ := by
  obtain ⟨φ, hφ, valid⟩ := inputValid
  refine ⟨substitution.targetMap φ, hφ.applyDB substitution, ?_⟩
  intro Carrier I hypotheses
  rw [holds_targetMap]
  apply valid _ (substitutionReduct substitution I)
  rintro ψ ⟨term, hterm, hψ⟩
  rw [← holds_targetMap]
  exact hypotheses _ ⟨substitution.apply term, Finset.mem_image_of_mem _ hterm,
    hψ.applyDB substitution⟩

/-- One primitive step preserves tagged validity, given tagged validity of its
theorem premises (under their own axiom tags) and of every axiom tag of the
result. -/
theorem taggedValid_of_primitiveEvidence {request : PrimitiveRequest} {out : Theorem}
    (evidence : PrimitiveEvidence request out)
    (premisesValid : ∀ premise ∈ request.premises,
      (∀ tagged ∈ premise.axioms, TaggedValid tagged) → TaggedValid premise.sequent)
    (axiomsValid : ∀ tagged ∈ out.axioms, TaggedValid tagged) :
    TaggedValid out.sequent := by
  cases evidence with
  | core evidence =>
      cases evidence with
      | «axiom» hbool parts =>
          rw [parts.sequent_eq]
          exact axiomsValid _ (by rw [parts.1]; exact Finset.mem_singleton_self _)
      | «assume» hbool parts =>
          rw [parts.sequent_eq]
          exact taggedValid_assume hbool
      | refl equality construction parts =>
          rw [parts.sequent_eq]
          exact taggedValid_refl construction
      | app functionLeft functionRight argumentLeft argumentRight applicationLeft
          applicationRight equality functionView argumentView leftApplication
          rightApplication construction parts =>
          rw [parts.sequent_eq]
          exact taggedValid_app functionView argumentView leftApplication
            rightApplication construction
            (premisesValid _ (by simp [PrimitiveRequest.premises]) fun tagged htagged =>
              axiomsValid tagged (by rw [parts.1]; exact Finset.mem_union_left _ htagged))
            (premisesValid _ (by simp [PrimitiveRequest.premises]) fun tagged htagged =>
              axiomsValid tagged (by rw [parts.1]; exact Finset.mem_union_right _ htagged))
      | deductAntisym equality construction parts =>
          rw [parts.sequent_eq]
          exact taggedValid_deductAntisym construction
            (premisesValid _ (by simp [PrimitiveRequest.premises]) fun tagged htagged =>
              axiomsValid tagged (by rw [parts.1]; exact Finset.mem_union_left _ htagged))
            (premisesValid _ (by simp [PrimitiveRequest.premises]) fun tagged htagged =>
              axiomsValid tagged (by rw [parts.1]; exact Finset.mem_union_right _ htagged))
      | eqMp left right view hmatch parts =>
          rw [parts.sequent_eq]
          exact taggedValid_eqMp view hmatch
            (premisesValid _ (by simp [PrimitiveRequest.premises]) fun tagged htagged =>
              axiomsValid tagged (by rw [parts.1]; exact Finset.mem_union_left _ htagged))
            (premisesValid _ (by simp [PrimitiveRequest.premises]) fun tagged htagged =>
              axiomsValid tagged (by rw [parts.1]; exact Finset.mem_union_right _ htagged))
  | binding evidence =>
      cases evidence with
      | abs fresh left right leftAbs rightAbs equality view leftAbstraction
          rightAbstraction construction parts =>
          rw [parts.sequent_eq]
          exact taggedValid_abs fresh view leftAbstraction rightAbstraction construction
            (premisesValid _ (by simp [PrimitiveRequest.premises]) fun tagged htagged =>
              axiomsValid tagged (by rw [parts.1]; exact htagged))
      | betaConv reduced equality reduction construction parts =>
          rw [parts.sequent_eq]
          exact taggedValid_betaConv reduction construction
  | subst evidence =>
      obtain ⟨haxioms, hhyp, hconcl⟩ := evidence
      have hsequent : out.sequent =
          ⟨_ , (TypeCorrectTermSubstitution.apply _ _)⟩ :=
        Sequent.ext
          ((applyHypotheses_semantics _ _).unique hhyp).symm
          ((apply_eq_iff_termSubstitutionSemantics _ _ _).mpr hconcl).symm
      rw [hsequent]
      exact taggedValid_subst _
        (premisesValid _ (by simp [PrimitiveRequest.premises]) fun tagged htagged =>
          axiomsValid tagged (by rw [haxioms]; exact htagged))

/-- **Soundness for tagged functions.**  Every theorem in the least closure of
the nine primitive rules, under any axiom policy, has a tagged-valid sequent
provided its axiom tags are tagged-valid. -/
theorem derives_taggedValid {policy : AxiomPolicy} {out : Theorem}
    (derivation : Derives (PolicyPrimitiveRule policy) out) :
    (∀ tagged ∈ out.axioms, TaggedValid tagged) → TaggedValid out.sequent := by
  induction derivation with
  | node premises conclusion rule _ ih =>
      intro axiomsValid
      obtain ⟨request, rfl, -, ⟨evidence⟩⟩ := rule
      exact taggedValid_of_primitiveEvidence evidence ih axiomsValid

/-- The axiom-free kernel is sound for tagged functions. -/
theorem derives_taggedValid_of_emptyAxiomPolicy {out : Theorem}
    (derivation : Derives (PolicyPrimitiveRule emptyAxiomPolicy) out) :
    TaggedValid out.sequent :=
  derives_taggedValid derivation fun tagged htagged => by
    rw [axioms_eq_empty_of_emptyAxiomPolicy derivation] at htagged
    exact absurd htagged (Finset.notMem_empty _)

end Kernel

/-! ## A countermodel to eta -/

/-- The value of each type over unit base carriers in which every arrow value
carries the tag `true`. -/
def taggedDefault {B : Type} : (τ : HOL.Ty B) → Value (fun _ : B => Unit) τ
  | .prop => True
  | .base _ => ()
  | .arr _ τ => (true, fun _ => taggedDefault τ)

/-- Unit base carriers, every symbol interpreted by its tagged default. -/
def taggedDefaultInterpretation : Interpretation (fun _ : AtomicTy => Unit) Symbol :=
  fun {τ} _ => taggedDefault τ

end TaggedFunctions

/-! ## Eta -/

namespace Eta

open TaggedFunctions

section Equation

variable (name : Name) (domain codomain : Ty)

/-- The free variable `f : domain -> codomain`. -/
def functionVar : SourceVar := ⟨name, .function domain codomain⟩

/-- `λ x. f x`. -/
def expansionDB : DBTerm :=
  .abs domain (.app (.free (functionVar name domain codomain)) (.bound 0))

/-- `(λ x. f x) = f`, with primitive equality. -/
def equationDB : DBTerm :=
  CanonicalTerm.equalityDB (.function domain codomain) (expansionDB name domain codomain)
    (.free (functionVar name domain codomain))

/-- The target symbol of `f`. -/
abbrev functionSymbol : Symbol (.arr domain.toHOL codomain.toHOL) :=
  .variable (functionVar name domain codomain) (Ty.toHOL_function domain codomain)

/-- The target formula `(λ x. f x) = f`. -/
def formula : HOL.ClosedFormula Symbol :=
  .eq (.lam (.app (.const (functionSymbol name domain codomain)) (.var .vz)))
    (.const (functionSymbol name domain codomain))

theorem equationDB_translates :
    Translates [] (equationDB name domain codomain) .prop (formula name domain codomain) :=
  .equalityApp (equalityOperand?_equality _) (Ty.toHOL_function domain codomain)
    (.abs rfl (.app rfl (.free _) (.bound .vz))) (.free _)

/-- The eta equation `(λ x. f x) = f` as a checked Boolean term of the
primitive kernel. -/
def equation : CanonicalTerm :=
  CanonicalTerm.ofFormulaTranslation (equationDB name domain codomain)
    (equationDB_translates name domain codomain)

/-- The named source term `(λ x. f x) = f`, for a binder name `x`. -/
def sourceEquation (binder : Name) : SourceTerm :=
  .app (.app (.const Const.equality (Ty.equality (.function domain codomain)))
      (.abs binder domain
        (.app (.var name (.function domain codomain)) (.var binder domain))))
    (.var name (.function domain codomain))

theorem functionVar_ne_binder (binder : Name) :
    functionVar name domain codomain ≠ ⟨binder, domain⟩ := by
  intro same
  have smaller := Ty.sizeOf_domain_lt domain codomain
  rw [show Ty.function domain codomain = domain from congrArg Var.ty same] at smaller
  exact lt_irrefl _ smaller

/-- Whatever the binder name, the alpha-canonical image of the named source
term is `equationDB`. -/
theorem sourceEquation_toDB (binder : Name) :
    (sourceEquation name domain codomain binder).toDB [] = equationDB name domain codomain := by
  have different := functionVar_ne_binder name domain codomain binder
  simp only [functionVar] at different
  simp [sourceEquation, equationDB, expansionDB, functionVar, CanonicalTerm.equalityDB,
    boundIndex, different]

/-- The source checker accepts the named source term and returns `equation`. -/
theorem check_sourceEquation (binder : Name) :
    (sourceEquation name domain codomain binder).check = some (equation name domain codomain) := by
  have accepted :
      (SourceTerm.check (sourceEquation name domain codomain binder)).isSome = true := by
    rw [SourceTerm.check_isSome_iff, ← DBTerm.inferType_toDB [] _]
    simp only [List.map_nil]
    rw [sourceEquation_toDB]
    exact Option.isSome_iff_exists.mpr ⟨_, (equation name domain codomain).checked⟩
  obtain ⟨checked, hchecked⟩ := Option.isSome_iff_exists.mp accepted
  rw [hchecked]
  congr 1
  apply CanonicalTerm.ext_term
  dsimp only [SourceTerm.check] at hchecked
  split at hchecked
  · cases hchecked
    exact sourceEquation_toDB name domain codomain binder
  · cases hchecked

/-- The compositional translation of the eta equation. -/
def compositionalFormula : HOL.ClosedFormula Symbol :=
  .app (.app (equalityLambda (.arr domain.toHOL codomain.toHOL))
      (.lam (.app (.const (functionSymbol name domain codomain)) (.var .vz))))
    (.const (functionSymbol name domain codomain))

theorem equationDB_translatesCompositionally :
    TranslatesCompositionally [] (equationDB name domain codomain) .prop
      (compositionalFormula name domain codomain) :=
  .equalityDB (Ty.toHOL_function domain codomain)
    (.abs rfl (.app (.free _) (.bound .vz))) (.free _)

/-- Extensional higher-order logic proves the translated eta sequent from no
hypotheses and no background sentences. -/
theorem equation_translatedProvable :
    TranslatedProvable ∅ ⟨∅, equation name domain codomain⟩ :=
  ⟨formula name domain codomain, equationDB_translates name domain codomain,
    [], by simp, .eta (.const (functionSymbol name domain codomain))⟩

/-- Eta fails in `taggedDefaultInterpretation`: `λ x. f x` carries the tag
`false`, while `f` carries the tag `true`. -/
theorem taggedDefaultInterpretation_not_holds :
    ¬ Holds taggedDefaultInterpretation (compositionalFormula name domain codomain) := by
  intro holds
  exact Bool.false_ne_true (congrArg Prod.fst holds)

/-- **Eta is not a theorem of the axiom-free kernel.**  No theorem of the
closure of the nine primitive rules under the empty axiom policy has the
sequent `⊢ (λ x. f x) = f`, for a free variable `f` of any function type. -/
theorem eta_not_derivable {out : Theorem}
    (derivation : Derives (PolicyPrimitiveRule emptyAxiomPolicy) out) :
    out.sequent ≠ ⟨∅, equation name domain codomain⟩ := by
  intro hsequent
  have valid := derives_taggedValid_of_emptyAxiomPolicy derivation
  rw [hsequent] at valid
  obtain ⟨φ, hφ, holds⟩ := valid
  have hφ' : φ = compositionalFormula name domain codomain :=
    hφ.unique_eq (equationDB_translatesCompositionally name domain codomain)
  subst hφ'
  exact taggedDefaultInterpretation_not_holds name domain codomain
    (holds _ taggedDefaultInterpretation fun _ ⟨_, hterm, _⟩ =>
      absurd hterm (Finset.notMem_empty _))

end Equation

/-! ## Positive control: beta at the same variable -/

section Beta

variable (name : Name) (domain codomain : Ty) (argumentName : Name)

/-- The free variable `y : domain`. -/
def argumentVar : SourceVar := ⟨argumentName, domain⟩

/-- `y` as a checked term. -/
def argument : CanonicalTerm :=
  ⟨.free (argumentVar domain argumentName), domain, by simp [argumentVar]⟩

/-- `(λ x. f x) y`. -/
def redex : CanonicalTerm :=
  ⟨.app (expansionDB name domain codomain) (.free (argumentVar domain argumentName)),
    codomain, DBTerm.inferType_app_eq_some_iff.mpr ⟨domain,
      DBTerm.inferType_abs_eq_some_iff.mpr ⟨codomain,
        DBTerm.inferType_app_eq_some_iff.mpr ⟨domain, by simp [functionVar], by simp⟩, rfl⟩,
      by simp [argumentVar]⟩⟩

/-- `f y`. -/
def contractum : CanonicalTerm :=
  ⟨.app (.free (functionVar name domain codomain)) (.free (argumentVar domain argumentName)),
    codomain, DBTerm.inferType_app_eq_some_iff.mpr
      ⟨domain, by simp [functionVar], by simp [argumentVar]⟩⟩

/-- The target symbol of `y`. -/
abbrev argumentSymbol : Symbol domain.toHOL :=
  Symbol.ofVar (argumentVar domain argumentName)

/-- `(λ x. f x) y = f y` with primitive equality. -/
def betaFormula : HOL.ClosedFormula Symbol :=
  .eq (.app (.lam (.app (.const (functionSymbol name domain codomain)) (.var .vz)))
      (.const (argumentSymbol domain argumentName)))
    (.app (.const (functionSymbol name domain codomain))
      (.const (argumentSymbol domain argumentName)))

theorem betaEquationDB_translates :
    Translates []
      (CanonicalTerm.equalityDB codomain (redex name domain codomain argumentName).term
        (contractum name domain codomain argumentName).term) .prop
      (betaFormula name domain codomain argumentName) :=
  .equalityApp (equalityOperand?_equality _) rfl
    (.app rfl (.abs rfl (.app rfl (.free _) (.bound .vz))) (.free rfl))
    (.app rfl (.free _) (.free rfl))

/-- `(λ x. f x) y = f y` as a checked Boolean term. -/
def betaEquation : CanonicalTerm :=
  CanonicalTerm.ofFormulaTranslation _ (betaEquationDB_translates name domain codomain argumentName)

/-- The beta theorem `⊢ (λ x. f x) y = f y`. -/
def betaTheorem : Theorem :=
  Theorem.emptyResult ∅ (betaEquation name domain codomain argumentName)

theorem betaTheorem_derives :
    Derives (PolicyPrimitiveRule emptyAxiomPolicy)
      (betaTheorem name domain codomain argumentName) := by
  refine derives_of_nullary_check emptyAxiomPolicy
    (.binding (.betaConv (redex name domain codomain argumentName)))
    (betaTheorem name domain codomain argumentName) rfl trivial ?_
  show checkBetaConv (redex name domain codomain argumentName) = _
  apply (checkBetaConv_eq_some_iff _ _).mpr
  refine ⟨contractum name domain codomain argumentName,
    betaEquation name domain codomain argumentName,
    ⟨domain, .app (.free (functionVar name domain codomain)) (.bound 0),
      argument domain argumentName, rfl, ?_⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
  simp [contractum, argument, DBTerm.instantiateAt]

/-- The compositional translation of the beta equation. -/
def betaCompositionalFormula : HOL.ClosedFormula Symbol :=
  .app (.app (equalityLambda codomain.toHOL)
      (.app (.lam (.app (.const (functionSymbol name domain codomain)) (.var .vz)))
        (.const (argumentSymbol domain argumentName))))
    (.app (.const (functionSymbol name domain codomain))
      (.const (argumentSymbol domain argumentName)))

/-- **Positive control.**  The interpretation refuting eta validates the derivable
beta instance `⊢ (λ x. f x) y = f y` at the same free variable `f`. -/
theorem betaTheorem_derives_and_taggedDefaultInterpretation_holds :
    Derives (PolicyPrimitiveRule emptyAxiomPolicy)
        (betaTheorem name domain codomain argumentName) ∧
      TranslatesCompositionally []
        (betaTheorem name domain codomain argumentName).sequent.concl.term .prop
        (betaCompositionalFormula name domain codomain argumentName) ∧
      Holds taggedDefaultInterpretation
        (betaCompositionalFormula name domain codomain argumentName) :=
  ⟨betaTheorem_derives name domain codomain argumentName,
    .equalityDB rfl (.app (.abs rfl (.app (.free _) (.bound .vz))) (.free rfl))
      (.app (.free _) (.free rfl)),
    rfl⟩

end Beta

end Eta

#print axioms TaggedFunctions.derives_taggedValid
#print axioms Eta.equation_translatedProvable
#print axioms Eta.check_sourceEquation
#print axioms Eta.eta_not_derivable
#print axioms Eta.betaTheorem_derives_and_taggedDefaultInterpretation_holds

end Mettapedia.Languages.OpenTheory
