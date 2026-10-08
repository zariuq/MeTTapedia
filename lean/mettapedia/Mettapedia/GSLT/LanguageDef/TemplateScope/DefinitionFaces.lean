import Mettapedia.GSLT.LanguageDef.TemplateScope.Evaluation
import Mettapedia.Logic.HOL.DefinitionExtensionSemantics

/-!
# Template scope, naming part 3: a definition has three faces

A definition `f x := t` is read three ways, on one small first-order fragment:
bodies `t` built from constants, application and the one variable `x : σ`,
arguments `a` ground terms over the same constants.  The three readings name
the same object, the ground term `t[a/x]` (`FO.subst`).

* **Operational** (the template-scope model): the equation `(= (f $x) t)`,
  nullary with a lambda body as all equations of the model are.  Calling
  `(f a)` answers the data term `t[a/x]` (`run_call`, `answerBag_call`).
* **Type face** (simply typed HOL terms): in the extension of the signature by
  the constant `f` (`DefinedConst`), definitional equality `DefEq` is the
  congruence closure of β and of δ, the unfolding of `f` into its body.  Then
  `f a ≡ t[a/x]` (`delta_unfold`).
* **Set face** (Henkin models): adding `f` with the defining axiom
  `∀x. f x = t` is a conservative extension, semantically (`conservative`:
  the old consequences of a theory are unchanged) and proof-theoretically
  (`conservative_derivation`: a derivation in the extension of an old formula
  from old hypotheses and the defining axiom gives a derivation without them).
  Both reuse `Mettapedia.Logic.HOL.DefinitionExtensionSemantics` and the
  constant-substitution closure of `ExtDerivation`.

## Relation to Prime's `set:define`

Prime's `set:define`, in a theory space with a selected profile, promises the
same three faces for an admitted definition: the constant runs there, the
kernel unfolds the same rule in conversion, and `set:` proofs reason about it.
This module is a small model of that promise for explicit, non-recursive
definitions, with the faces linked by theorems.  The model of `set:define`'s
explicit case in Prime's dependent calculus is
`ParameterizedPiSigmaId.TypedEquality.Annotated.ExplicitDefinitions` (type
face) and `ParameterizedPiSigmaId.TowerInterpretation.SetExplicitDefinitions`
(set face); this module states the faces in HOL instead, and adds the
operational link and conservativity.  Joining the two calculi is not done here,
nor are definitions by structural recursion.

## The links

* `DefEq.sound` — definitional equality is sound in every definitional
  extension of a Henkin model: β is sound, and δ holds because the constant
  denotes its body.
* `three_faces` — the operational answer of `(f a)` is `t[a/x]`; `f a ≡ t[a/x]`;
  and the set-theoretic function that `f` denotes, applied to the value of `a`,
  is the value of `t[a/x]`.
* On a concrete signature (`zero`, `succ`, and `f x := succ (succ x)`):
  the model answers `(succ (succ zero))`, and `f zero ≢ succ zero`
  (`f_zero_not_one`), refuted through soundness in the standard model of ℕ.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.DefinitionFaces

open Mettapedia.Logic.HOL
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v v' w

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## The fragment -/

/-- Ground first-order terms over the old signature: the arguments. -/
inductive Gr (Const : Ty Base → Type v) : Ty Base → Type (max u v) where
  | const {ρ : Ty Base} (c : Const ρ) : Gr Const ρ
  | app {α β : Ty Base} (f : Gr Const (α ⇒ β)) (a : Gr Const α) : Gr Const β

/-- First-order terms with the one variable `x : σ`: the bodies. -/
inductive FO (Const : Ty Base → Type v) (σ : Ty Base) : Ty Base → Type (max u v) where
  | x : FO Const σ σ
  | const {ρ : Ty Base} (c : Const ρ) : FO Const σ ρ
  | app {α β : Ty Base} (f : FO Const σ (α ⇒ β)) (a : FO Const σ α) : FO Const σ β

variable {σ τ : Ty Base}

/-- `t[a/x]`: substitute a ground argument for the variable. -/
def FO.subst (a : Gr Const σ) : {ρ : Ty Base} → FO Const σ ρ → Gr Const ρ
  | _, .x => a
  | _, .const c => .const c
  | _, .app f b => .app (FO.subst a f) (FO.subst a b)

/-- A ground term as a HOL term, in any context. -/
def Gr.toHOL {Γ : Ctx Base} : {ρ : Ty Base} → Gr Const ρ → Term Const Γ ρ
  | _, .const c => .const c
  | _, .app f a => .app (Gr.toHOL f) (Gr.toHOL a)

/-- A body as a HOL term in the context of its variable. -/
def FO.toHOL : {ρ : Ty Base} → FO Const σ ρ → Term Const [σ] ρ
  | _, .x => .var .vz
  | _, .const c => .const c
  | _, .app f a => .app (FO.toHOL f) (FO.toHOL a)

/-- Instantiating the HOL reading of a body is reading the substituted body. -/
theorem instantiate_toHOL (a : Gr Const σ) : ∀ {ρ : Ty Base} (t : FO Const σ ρ),
    instantiate (Base := Base) (Gr.toHOL a : Term Const [] σ) (FO.toHOL t) =
      Gr.toHOL (FO.subst a t)
  | _, .x => rfl
  | _, .const _ => rfl
  | _, .app f b => by
      show Term.app (instantiate _ (FO.toHOL f)) (instantiate _ (FO.toHOL b)) = _
      rw [instantiate_toHOL a f, instantiate_toHOL a b]
      rfl

/-- Weakening the body under its binder and instantiating by the bound
variable gives the body back. -/
theorem instantiate_var_rename : ∀ {ρ : Ty Base} (t : FO Const σ ρ),
    instantiate (Base := Base) (.var .vz : Term Const [σ] σ)
      (rename (Rename.lift (Rename.weaken (Base := Base) (Γ := []) (σ := σ))) (FO.toHOL t)) =
      FO.toHOL t
  | _, .x => rfl
  | _, .const _ => rfl
  | _, .app f b => by
      show Term.app (instantiate _ (rename _ (FO.toHOL f))) (instantiate _ (rename _ (FO.toHOL b))) = _
      rw [instantiate_var_rename f, instantiate_var_rename b]
      rfl

/-! ## The type face: δ-unfolding -/

/-- The extended signature. -/
abbrev Ext (Const : Ty Base → Type v) (σ τ : Ty Base) := DefinedConst Const (σ ⇒ τ)

/-- **Definitional equality** of the extension by a constant with closed body
`body`: the congruence closure of β and of δ, which unfolds the constant into
its body. -/
inductive DefEq (body : ClosedTerm Const (σ ⇒ τ)) :
    {Γ : Ctx Base} → {ρ : Ty Base} → Term (Ext Const σ τ) Γ ρ → Term (Ext Const σ τ) Γ ρ → Prop
  | refl {Γ : Ctx Base} {ρ : Ty Base} (s : Term (Ext Const σ τ) Γ ρ) : DefEq body s s
  | symm {Γ : Ctx Base} {ρ : Ty Base} {s s' : Term (Ext Const σ τ) Γ ρ} :
      DefEq body s s' → DefEq body s' s
  | trans {Γ : Ctx Base} {ρ : Ty Base} {s s' s'' : Term (Ext Const σ τ) Γ ρ} :
      DefEq body s s' → DefEq body s' s'' → DefEq body s s''
  | app {Γ : Ctx Base} {α β : Ty Base} {f f' : Term (Ext Const σ τ) Γ (α ⇒ β)}
      {a a' : Term (Ext Const σ τ) Γ α} :
      DefEq body f f' → DefEq body a a' → DefEq body (.app f a) (.app f' a')
  | lam {Γ : Ctx Base} {α β : Ty Base} {b b' : Term (Ext Const σ τ) (α :: Γ) β} :
      DefEq body b b' → DefEq body (.lam b) (.lam b')
  | beta {Γ : Ctx Base} {α β : Ty Base} (u : Term (Ext Const σ τ) (α :: Γ) β)
      (a : Term (Ext Const σ τ) Γ α) :
      DefEq body (.app (.lam u) a) (instantiate (Base := Base) a u)
  | delta {Γ : Ctx Base} :
      DefEq body (.const .defined : Term (Ext Const σ τ) Γ (σ ⇒ τ))
        (weakenCtx Γ (DefinedConst.embed (target := σ ⇒ τ) body))

/-- The body of `f x := t` as a closed lambda. -/
def lamBody (t : FO Const σ τ) : ClosedTerm Const (σ ⇒ τ) := .lam (FO.toHOL t)

/-- The call `f a` in the extension. -/
def call (a : Gr Const σ) : Term (Ext Const σ τ) [] τ :=
  .app (.const .defined) (DefinedConst.embed (Gr.toHOL a))

/-- **δ-unfolding.**  With `f := λx. t`, `f a ≡ t[a/x]`. -/
theorem delta_unfold (t : FO Const σ τ) (a : Gr Const σ) :
    DefEq (lamBody t) (call (τ := τ) a) (DefinedConst.embed (Gr.toHOL (FO.subst a t))) := by
  have h1 : DefEq (lamBody t) (call (τ := τ) a)
      (.app (.lam (DefinedConst.embed (target := σ ⇒ τ) (FO.toHOL t)))
        (DefinedConst.embed (Gr.toHOL a))) :=
    .app .delta (.refl _)
  have h2 := DefEq.beta (body := lamBody t) (DefinedConst.embed (target := σ ⇒ τ) (FO.toHOL t))
    (DefinedConst.embed (Gr.toHOL a : Term Const [] σ))
  have h3 : instantiate (Base := Base) (DefinedConst.embed (target := σ ⇒ τ) (Gr.toHOL a))
      (DefinedConst.embed (target := σ ⇒ τ) (FO.toHOL t)) =
      DefinedConst.embed (Gr.toHOL (FO.subst a t)) := by
    rw [← instantiate_toHOL a t]
    unfold DefinedConst.embed
    rw [mapConst_instantiate]
  rw [h3] at h2
  exact .trans h1 h2

/-! ## The set face: the defining axiom is a conservative extension -/

/-- The defining axiom `∀x. f x = t`. -/
def defAxiom (t : FO Const σ τ) : ClosedFormula (Ext Const σ τ) :=
  .all (.eq (.app (.const .defined) (.var .vz)) (DefinedConst.embed (FO.toHOL t)))

/-- Constant substitution by constants is constant renaming. -/
theorem substConst_const {Const' : Ty Base → Type v'} (g : ∀ {ρ : Ty Base}, Const ρ → Const' ρ) :
    ∀ {Γ : Ctx Base} {ρ : Ty Base} (s : Term Const Γ ρ),
      substConst (fun c => .const (g c)) s = mapConst g s := by
  intro Γ ρ s
  induction s with
  | const c => simp [substConst, mapConst]
  | _ => simp_all [substConst, mapConst]

/-- The empty valuation of a Henkin model. -/
def emptyVal {Const' : Ty Base → Type v'} (M : HenkinModel.{u, v', w} Base Const') :
    M.Valuation [] := fun v => nomatch v

/-- The defining axiom with `f` unfolded is a theorem: `∀x. (λx. t) x = t` by β. -/
theorem defAxiom_expanded_derivation (t : FO Const σ τ) {Δ : List (ClosedFormula Const)} :
    Derivation Const Δ (substConst (DefinedConst.expansion (lamBody t)) (defAxiom t)) := by
  have hb := Derivation.beta (Const := Const)
    (Δ := weakenHyps (Base := Base) (σ := σ) Δ) (.var .vz : Term Const [σ] σ)
    (rename (Rename.lift (Rename.weaken (Base := Base) (Γ := []) (σ := σ))) (FO.toHOL t))
  rw [instantiate_var_rename t] at hb
  refine Derivation.allI ?_
  have hexp := DefinedConst.expansion_embed (target := σ ⇒ τ) (lamBody t) (FO.toHOL t)
  simp only [substConst, hexp]
  exact hb

/-- The same in the extensional calculus. -/
theorem defAxiom_expanded (t : FO Const σ τ) {Δ : List (ClosedFormula Const)} :
    ExtDerivation Const Δ (substConst (DefinedConst.expansion (lamBody t)) (defAxiom t)) := by
  have hb := ExtDerivation.beta (Const := Const)
    (Δ := weakenHyps (Base := Base) (σ := σ) Δ) (.var .vz : Term Const [σ] σ)
    (rename (Rename.lift (Rename.weaken (Base := Base) (Γ := []) (σ := σ))) (FO.toHOL t))
  rw [instantiate_var_rename t] at hb
  refine ExtDerivation.allI ?_
  have hexp := DefinedConst.expansion_embed (target := σ ⇒ τ) (lamBody t) (FO.toHOL t)
  simp only [substConst, hexp]
  exact hb

/-- The definitional extension of every Henkin model satisfies the defining
axiom: `f` denotes the set-theoretic function `x ↦ ⟦t⟧(x)`. -/
theorem models_defAxiom (M : HenkinModel.{u, v, w} Base Const) (t : FO Const σ τ) :
    (M.definitionExtension (lamBody t)).models (defAxiom t) :=
  (HenkinModel.models_substConst _ M (defAxiom t)).1
    (Soundness.theorem_sound (defAxiom_expanded_derivation t) M)

/-- **The extension is conservative (Henkin semantics).**  For every theory
`T` and old sentence `φ`: `T ⊨ φ` iff `T` with the defining axiom entails `φ`
in the extended signature. -/
theorem conservative (t : FO Const σ τ) (T : Set (ClosedFormula Const))
    (φ : ClosedFormula Const) :
    (∀ M : HenkinModel.{u, v, w} Base Const, (∀ ψ ∈ T, M.models ψ) → M.models φ) ↔
      ∀ M' : HenkinModel.{u, max u v, w} Base (Ext Const σ τ),
        (∀ ψ ∈ T, M'.models (DefinedConst.embed ψ)) → M'.models (defAxiom t) →
          M'.models (DefinedConst.embed φ) := by
  have hred : ∀ (M' : HenkinModel.{u, max u v, w} Base (Ext Const σ τ)) (ψ : ClosedFormula Const),
      (HenkinModel.constantSubstitutionReduct (fun c => .const (DefinedConst.old c)) M').models ψ ↔
        M'.models (DefinedConst.embed ψ) := by
    intro M' ψ
    rw [← HenkinModel.models_substConst, substConst_const]
    rfl
  constructor
  · intro h M' hT _
    exact (hred M' φ).1 (h _ fun ψ hψ => (hred M' ψ).2 (hT ψ hψ))
  · intro h M hT
    exact (M.definitionExtension_models_embed (lamBody t) φ).1
      (h _ (fun ψ hψ => (M.definitionExtension_models_embed (lamBody t) ψ).2 (hT ψ hψ))
        (models_defAxiom M t))

/-- **The extension is conservative (derivations).**  A derivation, in the
extended signature, of an old formula from old hypotheses and the defining
equation of `f` gives a derivation of it from the old hypotheses alone: unfold
`f` everywhere and discharge the unfolded equation by β. -/
theorem conservative_derivation (t : FO Const σ τ) {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (d : ExtDerivation (Ext Const σ τ) (defAxiom t :: Δ.map DefinedConst.embed)
      (DefinedConst.embed φ)) :
    ExtDerivation Const Δ φ := by
  have d' := ExtDerivation.substConst_derivation (DefinedConst.expansion (lamBody t)) d
  have hφ := DefinedConst.expansion_embed (target := σ ⇒ τ) (lamBody t) φ
  have hΔ : (Δ.map DefinedConst.embed).map
      (substConst (DefinedConst.expansion (target := σ ⇒ τ) (lamBody t))) = Δ := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id Δ]
    apply List.map_congr_left
    intro ψ _
    exact DefinedConst.expansion_embed (lamBody t) ψ
  rw [List.map_cons, hΔ, hφ] at d'
  exact ExtDerivation.impE (ExtDerivation.impI d') (defAxiom_expanded t)

/-! ## The link between the type face and the set face -/

/-- **Definitional equality is sound** in every model of the extension that
interprets `f` by its body: β because denotation commutes with instantiation,
δ because the constant denotes its body. -/
theorem DefEq.sound {body : ClosedTerm Const (σ ⇒ τ)}
    (M' : HenkinModel.{u, max u v, w} Base (Ext Const σ τ))
    (hdef : ∀ ν₀ : M'.Valuation [], M'.constDen DefinedConst.defined =
      M'.denote (DefinedConst.embed body) ν₀) :
    ∀ {Γ : Ctx Base} {ρ : Ty Base} {s s' : Term (Ext Const σ τ) Γ ρ}, DefEq body s s' →
      ∀ ν : M'.Valuation Γ, M'.denote s ν = M'.denote s' ν := by
  intro Γ ρ s s' h
  induction h with
  | refl _ => intro ν; rfl
  | symm _ ih => intro ν; exact (ih ν).symm
  | trans _ _ ih₁ ih₂ => intro ν; exact (ih₁ ν).trans (ih₂ ν)
  | app _ _ ihf iha =>
      intro ν
      have h1 := ihf ν
      have h2 := iha ν
      simp only [HenkinModel.denote] at h1 h2 ⊢
      simp only [PreModel.denote]
      rw [h1, h2]
  | lam _ ih =>
      intro ν
      funext x
      exact ih _
  | beta u a =>
      intro ν
      exact (Soundness.denote_instantiate_term _ a u ν).symm
  | delta =>
      intro ν
      rename_i Γ'
      rw [HenkinModel.denote_weakenCtx M' Γ' _ ν]
      exact hdef _

/-- The definitional extension of a model interprets the constant by its body. -/
theorem definitionExtension_interprets (M : HenkinModel.{u, v, w} Base Const)
    (body : ClosedTerm Const (σ ⇒ τ)) (ν₀ : (M.definitionExtension body).Valuation []) :
    (M.definitionExtension body).constDen DefinedConst.defined =
      (M.definitionExtension body).denote (DefinedConst.embed body) ν₀ :=
  (M.definitionExtension_defined body).trans
    ((HenkinModel.denote_closed_valuation_eq M body _ ν₀).trans
      (M.definitionExtension_embed body body ν₀).symm)

/-! ## The operational face -/

section Operational

variable {S : Type*} {X : Type*} [DecidableEq S] [DecidableEq X]
variable (κ : ∀ {ρ : Ty Base}, Const ρ → S) (xN : Nm X)

/-- A ground term as a model term: constants are symbols, application is data. -/
def Gr.toTm : {ρ : Ty Base} → Gr Const ρ → Tm S X
  | _, .const c => .sym (κ c)
  | _, .app f a => .app (Gr.toTm f) (Gr.toTm a)

/-- A body as a model term: the variable is the rule's parameter. -/
def FO.toTm : {ρ : Ty Base} → FO Const σ ρ → Tm S X
  | _, .x => .pvar xN
  | _, .const c => .sym (κ c)
  | _, .app f a => .app (FO.toTm f) (FO.toTm a)

/-- The depth of a ground term. -/
def Gr.depth : {ρ : Ty Base} → Gr Const ρ → ℕ
  | _, .const _ => 0
  | _, .app f a => max (Gr.depth f) (Gr.depth a) + 1

/-- **The operational rule** `(= (f $x) t)`: the model's equations are nullary
with a lambda body over the parameter. -/
def rule (t : FO Const σ τ) : Tm S X := .lam xN [] (FO.toTm κ xN t)

omit [DecidableEq S] in
theorem subst_toTm (a : Gr Const σ) : ∀ {ρ : Ty Base} (t : FO Const σ ρ),
    TemplateScope.subst Sub.none (Sub.single xN (Gr.toTm (X := X) κ a)) (FO.toTm κ xN t) =
      Gr.toTm κ (FO.subst a t)
  | _, .x => by simp [FO.toTm, TemplateScope.subst, Sub.single, FO.subst]
  | _, .const _ => rfl
  | _, .app f b => by
      simp only [FO.toTm, TemplateScope.subst, FO.subst, Gr.toTm]
      rw [subst_toTm a f, subst_toTm a b]

/-- A ground term evaluates to itself, as data. -/
theorem run_ground (d : Disc) (prog : S → Option (Tm S X)) :
    ∀ {ρ : Ty Base} (g : Gr Const ρ) (n : ℕ) (π : Path) (σs : GStore S X), Gr.depth g < n →
      run d prog n π σs (Gr.toTm κ g) = some [(Gr.toTm κ g, σs)]
  | _, .const _, n + 1, _, _, _ => rfl
  | _, .app f a, n + 1, π, σs, h => by
      simp only [Gr.depth] at h
      show step d prog (run d prog n) π σs _ = _
      simp only [step, Gr.toTm]
      rw [run_ground d prog f n _ σs (by omega), bindOpt_some_singleton]
      simp only
      rw [run_ground d prog a n _ σs (by omega), bindOpt_some_singleton]
      cases f <;> rfl

/-- **The operational face.**  Calling the equation on a ground argument
answers the ground term `t[a/x]`, once, with the store unchanged. -/
theorem run_call (F : S) (prog : S → Option (Tm S X)) (t : FO Const σ τ)
    (hF : prog F = some (rule κ xN t)) (a : Gr Const σ) (n : ℕ)
    (hn : Gr.depth a + Gr.depth (FO.subst a t) + 3 ≤ n) (π : Path) (σs : GStore S X) :
    run .static prog n π σs (.app (.fn F) (Gr.toTm κ a)) =
      some [(Gr.toTm κ (FO.subst a t), σs)] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  show step .static prog (run .static prog (m + 2)) π σs _ = _
  simp only [step]
  have hfn : run .static prog (m + 2) (π ++ [0]) σs (.fn F) = some [(rule κ xN t, σs)] := by
    show step .static prog (run .static prog (m + 1)) _ σs (.fn F) = _
    simp only [step, hF]
    rfl
  rw [hfn, bindOpt_some_singleton]
  simp only
  rw [run_ground κ .static prog a (m + 2) _ σs (by omega), bindOpt_some_singleton]
  simp only [rule, activate, renameOwn_nil]
  rw [subst_toTm κ xN a t]
  exact run_ground κ .static prog _ (m + 2) _ σs (by omega)

omit [DecidableEq S] in
theorem act_toTm (σs : GStore S X) : ∀ {ρ : Ty Base} (g : Gr Const ρ),
    act σs (Gr.toTm (X := X) κ g) = Gr.toTm κ g
  | _, .const _ => rfl
  | _, .app f a => by
      simp only [Gr.toTm, act_app]
      rw [act_toTm σs f, act_toTm σs a]

/-- The operational face on answer bags. -/
theorem answerBag_call (F : S) (prog : S → Option (Tm S X)) (t : FO Const σ τ)
    (hF : prog F = some (rule κ xN t)) (a : Gr Const σ) :
    AnswerBag .static prog (.app (.fn F) (Gr.toTm κ a)) [Gr.toTm κ (FO.subst a t)] := by
  refine ⟨Gr.depth a + Gr.depth (FO.subst a t) + 3, ?_⟩
  unfold answers
  rw [run_call κ xN F prog t hF a _ le_rfl]
  simp [act_toTm]

/-! ## The three faces together -/

/-- **A definition has three faces, and they agree.**  For `f x := t` and a
ground argument `a`:
* operationally, the call `(f a)` answers `t[a/x]`;
* by definitional equality, `f a ≡ t[a/x]`;
* in every Henkin model, the function that `f` denotes, applied to the value of
  `a`, is the value of `t[a/x]`. -/
theorem three_faces (F : S) (prog : S → Option (Tm S X)) (t : FO Const σ τ)
    (hF : prog F = some (rule κ xN t)) (a : Gr Const σ) (M : HenkinModel.{u, v, w} Base Const) :
    AnswerBag .static prog (.app (.fn F) (Gr.toTm κ a)) [Gr.toTm κ (FO.subst a t)] ∧
    DefEq (lamBody t) (call (τ := τ) a) (DefinedConst.embed (Gr.toHOL (FO.subst a t))) ∧
    (M.definitionExtension (lamBody t)).constDen DefinedConst.defined
        (M.denote (Gr.toHOL a) (emptyVal M)) =
      M.denote (Gr.toHOL (FO.subst a t)) (emptyVal M) := by
  refine ⟨answerBag_call κ xN F prog t hF a, delta_unfold t a, ?_⟩
  have hsound := DefEq.sound (M.definitionExtension (lamBody t))
    (definitionExtension_interprets M (lamBody t)) (delta_unfold t a) (emptyVal M)
  have harg := M.definitionExtension_embed (lamBody t) (Gr.toHOL a : Term Const [] σ) (emptyVal M)
  have hres := M.definitionExtension_embed (lamBody t)
    (Gr.toHOL (FO.subst a t) : Term Const [] τ) (emptyVal M)
  have e1 : (M.definitionExtension (lamBody t)).constDen DefinedConst.defined
        (M.denote (Gr.toHOL a) (emptyVal M)) =
      (M.definitionExtension (lamBody t)).denote (call (τ := τ) a) (emptyVal M) := by
    show _ = (M.definitionExtension (lamBody t)).constDen DefinedConst.defined
      ((M.definitionExtension (lamBody t)).denote (DefinedConst.embed (Gr.toHOL a)) (emptyVal M))
    rw [harg]
  exact e1.trans (hsound.trans hres)

end Operational

/-! ## A concrete definition: `f x := succ (succ x)` -/

namespace NatExample

/-- Constants of a one-sorted signature of numerals. -/
inductive NatC : Ty Unit → Type
  | zero : NatC (.base ())
  | succ : NatC (.base () ⇒ .base ())

/-- The sort of numerals. -/
abbrev ι : Ty Unit := .base ()

/-- The body of `f x := succ (succ x)`. -/
def body : FO NatC ι ι := .app (.const .succ) (.app (.const .succ) .x)

def zeroG : Gr NatC ι := .const .zero

def oneG : Gr NatC ι := .app (.const .succ) (.const .zero)

/-- Symbols of the model's terms. -/
inductive NSy where
  | zero | succ | f
  deriving DecidableEq, Repr

def κN : {ρ : Ty Unit} → NatC ρ → NSy
  | _, .zero => .zero
  | _, .succ => .succ

/-- Spellings of the model's names. -/
inductive NSp where
  | x
  deriving DecidableEq, Repr

/-- The rule's parameter. -/
def xN : Nm NSp := .src .x

/-- The program holding the rule `(= (f $x) (succ (succ $x)))`. -/
def progN : NSy → Option (Tm NSy NSp) := fun s =>
  if s = .f then some (rule κN xN body) else none

/-- The standard model of the numerals. -/
def natDen : {τ : Ty Unit} → NatC τ → Ty.denote.{0, 0} (fun _ => ULift.{1} ℕ) τ
  | _, .zero => ULift.up 0
  | _, .succ => fun n => ULift.up (n.down + 1)

def Mℕ : HenkinModel.{0, 0, 0} Unit NatC := HenkinModel.standard (fun _ => ULift.{1} ℕ) natDen

/-- **Operational face, computed.**  `(f zero)` answers `(succ (succ zero))`. -/
theorem op_f_zero :
    answers .static progN 10 (.app (.fn .f) (Gr.toTm κN zeroG)) =
      some [.app (.sym .succ) (.app (.sym .succ) (.sym .zero))] := by
  decide

/-- **Type face.**  `f zero ≡ succ (succ zero)`. -/
theorem type_f_zero :
    DefEq (lamBody body) (call (τ := ι) zeroG)
      (DefinedConst.embed (target := ι ⇒ ι)
        (Term.app (Term.const NatC.succ) (Term.app (Term.const NatC.succ) (Term.const NatC.zero)) :
          Term NatC [] ι)) :=
  delta_unfold body zeroG

/-- **Set face.**  In the standard model, `f` denotes `n ↦ n + 2`. -/
theorem set_f (n : ℕ) :
    ((Mℕ.definitionExtension (lamBody body)).constDen DefinedConst.defined
      (ULift.up n : ULift.{1} ℕ) : ULift.{1} ℕ).down = n + 2 := rfl

/-- **Negative.**  `f zero ≢ succ zero`: definitional equality is sound in the
standard model, where the two sides denote 2 and 1. -/
theorem f_zero_not_one :
    ¬ DefEq (lamBody body) (call (τ := ι) zeroG) (DefinedConst.embed (Gr.toHOL oneG)) := by
  intro h
  have hs := DefEq.sound (Mℕ.definitionExtension (lamBody body))
    (definitionExtension_interprets Mℕ (lamBody body)) h (emptyVal _)
  have h2 : ((Mℕ.definitionExtension (lamBody body)).denote (call (τ := ι) zeroG) (emptyVal _) :
      ULift.{1} ℕ).down = 2 := rfl
  have h1 : ((Mℕ.definitionExtension (lamBody body)).denote
      (DefinedConst.embed (Gr.toHOL oneG)) (emptyVal _) : ULift.{1} ℕ).down = 1 := rfl
  rw [hs, h1] at h2
  exact absurd h2 (by decide)

/-- The three faces of `f` at `zero`, from the general theorem. -/
theorem three_faces_f_zero :
    AnswerBag .static progN (.app (.fn .f) (Gr.toTm κN zeroG))
      [Gr.toTm κN (FO.subst zeroG body)] ∧
    DefEq (lamBody body) (call (τ := ι) zeroG) (DefinedConst.embed (Gr.toHOL (FO.subst zeroG body))) ∧
    (Mℕ.definitionExtension (lamBody body)).constDen DefinedConst.defined
        (Mℕ.denote (Gr.toHOL zeroG) (emptyVal Mℕ)) =
      Mℕ.denote (Gr.toHOL (FO.subst zeroG body)) (emptyVal Mℕ) :=
  three_faces κN xN NSy.f progN body (by simp [progN]) zeroG Mℕ

end NatExample

end Mettapedia.GSLT.LanguageDef.TemplateScope.DefinitionFaces
