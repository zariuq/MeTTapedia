import Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

/-!
# Template scope, part 1: scope-bearing terms and the environment action

The term language of the template-scope study.  It is the smallest language
in which the activation question of Prime's binding structure can be stated:

* symbols, references to program equations, store-name occurrences,
  lambda-parameter occurrences, a one-parameter `lam`, application,
  a sealed quotation, contextual code (an open term under the code binders
  it mentions), a quotation written in pattern position, `let` with a
  pattern, and a binary choice (so that answers form a bag);
* a lambda carries its **own names as binders** (`lam x own body`).  Before
  elaboration the list is empty; elaboration (`TemplateScope.Elaboration`)
  fills it once, and every later substitution copies it with the lambda.

The role of a name belongs to its occurrence, not to its spelling: `var n` is
a store-name occurrence and `pvar n` a parameter occurrence, even when both
print the same.  A quotation in value position (`quote`) is sealed code; a
quotation written in pattern position (`pquote`) is pattern syntax, whose
`$` names are store-name occurrences.

Stores are the ground stores of `SequentialBindingDiscipline`, keyed by
store-name identities `Nm X` and valued in ground values `GVal S X`.

## Main results

* `act_absorb` — the environment action absorbs refinement:
  applying `σ` and then `τ ⊒ σ` equals applying `τ`.
* `act_idem` — the action is idempotent.
* `act_lam`, `act_pvar`, `act_quote` — it never touches a parameter, stops at
  a lambda's own binders, and never enters a sealed quotation.
* `act_plug` / `act_hole_local` — occurrence locality: the action on the
  content of a hole depends only on that content, the store and the binders
  on the path to the hole, never on siblings.

The action is *not* claimed to make evaluation order irrelevant: absorption
says a consumer may be handed the current store at its transition; moving a
consumer across a refinement is a different statement and fails for
non-monotone observers (see `TemplateScope.Corpus`).
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

/-- Evaluation paths: the position of a judgment in the evaluation tree. -/
abbrev Path := List ℕ

/-- Store-name identities.  `src x` is a name as written; `inst ρ n` is the
copy of `n` made by the activation whose body runs at path `ρ`.  Distinct
activations have distinct paths, so copies are fresh by construction. -/
inductive Nm (X : Type v) where
  | src (x : X)
  | inst (ρ : Path) (n : Nm X)
  deriving DecidableEq, Repr

/-- Scope-bearing terms.  `lam x own body` binds the parameter `x` (lexically)
and the store names `src y`, `y ∈ own` (its own names), in `body`. -/
inductive Tm (S : Type u) (X : Type v) where
  | sym (s : S)
  | fn (F : S)
  | var (n : Nm X)
  | pvar (x : Nm X)
  | lam (x : Nm X) (own : List X) (body : Tm S X)
  | app (f a : Tm S X)
  | quote (c : Tm S X)
  /-- Open code `body` under the code binders `ks`, outermost first. A value.
  The environment action does not enter it. -/
  | ctx (ks : List (Nm X)) (body : Tm S X)
  | pquote (c : Tm S X)
  | letP (p v b : Tm S X)
  | alt (t₁ t₂ : Tm S X)
  deriving DecidableEq, Repr

/-- Ground values: what a ground store may hold.  A quotation is ground: its
content is code, not a store-name occurrence. -/
inductive GVal (S : Type u) (X : Type v) where
  | sym (s : S)
  | app (f a : GVal S X)
  | quote (c : Tm S X)
  /-- Contextual code, the ground value of `Tm.ctx`. -/
  | ctx (ks : List (Nm X)) (body : Tm S X)
  deriving DecidableEq, Repr

variable {S : Type u} {X : Type v}

namespace GVal

/-- The term a ground value denotes. -/
def toTm : GVal S X → Tm S X
  | .sym s => .sym s
  | .app f a => .app f.toTm a.toTm
  | .quote c => .quote c
  | .ctx ks c => .ctx ks c

end GVal

namespace Tm

/-- Read a term back as a ground value, when it is one. -/
def toGVal? : Tm S X → Option (GVal S X)
  | .sym s => some (.sym s)
  | .app f a =>
      match f.toGVal?, a.toGVal? with
      | some f', some a' => some (.app f' a')
      | _, _ => none
  | .quote c => some (.quote c)
  | .ctx ks c => some (.ctx ks c)
  | _ => none

end Tm

theorem GVal.toTm_toGVal? (g : GVal S X) : g.toTm.toGVal? = some g := by
  induction g with
  | sym s => rfl
  | app f a ihf iha => simp [GVal.toTm, Tm.toGVal?, ihf, iha]
  | quote c => rfl
  | ctx ks c => rfl

variable [DecidableEq X]

/-- Whether a lambda's own-name list binds a store name.  Own lists bind
names as written (`src y`); copies made by activations are never rebound. -/
def ownKey (own : List X) : Nm X → Bool
  | .src y => own.contains y
  | .inst _ _ => false

/-! ## One generic, capture-avoiding substitution -/

/-- A substitution for store names or for parameters. -/
abbrev Sub (S : Type u) (X : Type v) := Nm X → Option (Tm S X)

namespace Sub

/-- The empty substitution. -/
def none : Sub S X := fun _ => Option.none

/-- Substitute one name. -/
def single (x : Nm X) (t : Tm S X) : Sub S X :=
  fun n => if n = x then some t else Option.none

/-- Stop at a lambda's own binders. -/
def hideOwn (own : List X) (θ : Sub S X) : Sub S X :=
  fun n => if ownKey own n then Option.none else θ n

/-- Stop at a parameter binder of the same name. -/
def hideParam (x : Nm X) (φ : Sub S X) : Sub S X :=
  fun n => if n = x then Option.none else φ n

end Sub

/-- Simultaneous substitution of store names (`θ`) and parameters (`φ`).

* It stops at a lambda's own binders (for `θ`) and at its parameter (for `φ`).
* It never enters a sealed quotation.
* It enters a quotation written in pattern position: its names are pattern
  holes.

Every name operation of the study is an instance: the environment action,
the evaluator's `let` substitution, activation renaming and parameter
instantiation. -/
def subst (θ φ : Sub S X) : Tm S X → Tm S X
  | .sym s => .sym s
  | .fn F => .fn F
  | .var n => (θ n).getD (.var n)
  | .pvar x => (φ x).getD (.pvar x)
  | .lam x own b => .lam x own (subst (θ.hideOwn own) (φ.hideParam x) b)
  | .app f a => .app (subst θ φ f) (subst θ φ a)
  | .quote c => .quote c
  | .ctx ks c => .ctx ks c
  | .pquote c => .pquote (subst θ φ c)
  | .letP p w b => .letP (subst θ φ p) (subst θ φ w) (subst θ φ b)
  | .alt t₁ t₂ => .alt (subst θ φ t₁) (subst θ φ t₂)

/-- Substitution never changes a ground value. -/
theorem subst_toTm (θ φ : Sub S X) (g : GVal S X) :
    subst θ φ g.toTm = g.toTm := by
  induction g with
  | sym s => rfl
  | app f a ihf iha => simp [GVal.toTm, subst, ihf, iha]
  | quote c => rfl
  | ctx ks c => rfl

/-- Substitutions that agree pointwise act alike. -/
theorem subst_congr {θ θ' φ φ' : Sub S X} (hθ : ∀ n, θ n = θ' n)
    (hφ : ∀ n, φ n = φ' n) (t : Tm S X) : subst θ φ t = subst θ' φ' t := by
  have hθ' : θ = θ' := funext hθ
  have hφ' : φ = φ' := funext hφ
  subst hθ' hφ'
  rfl

/-! ## Ground stores and the environment action -/

/-- Ground stores over store-name identities (the 8/07 `Store`). -/
abbrev GStore (S : Type u) (X : Type v) := Store (Nm X) (GVal S X)

/-- A store, read as a store-name substitution. -/
def envSub (σ : GStore S X) : Sub S X := fun n => (σ n).map GVal.toTm

/-- **The environment action**, store × term → term. -/
def act (σ : GStore S X) (t : Tm S X) : Tm S X := subst (envSub σ) Sub.none t

/-- Forget the bindings of a lambda's own names. -/
def GStore.hide (own : List X) (σ : GStore S X) : GStore S X :=
  fun n => if ownKey own n then Option.none else σ n

theorem envSub_hideOwn (own : List X) (σ : GStore S X) :
    (envSub σ).hideOwn own = envSub (σ.hide own) := by
  funext n
  unfold Sub.hideOwn envSub GStore.hide
  by_cases h : ownKey own n <;> simp [h]

theorem none_hideParam (x : Nm X) : (Sub.none : Sub S X).hideParam x = Sub.none := by
  funext n
  unfold Sub.hideParam Sub.none
  by_cases h : n = x <;> simp [h]

theorem GStore.hide_le {σ τ : GStore S X} (h : σ ⊑ τ) (own : List X) :
    σ.hide own ⊑ τ.hide own := by
  intro n w hn
  unfold GStore.hide at hn ⊢
  by_cases hk : ownKey own n
  · simp [hk] at hn
  · simp only [hk] at hn ⊢
    exact h n w hn

/-- The action fixes every ground value. -/
theorem act_toTm (σ : GStore S X) (g : GVal S X) : act σ g.toTm = g.toTm :=
  subst_toTm _ _ g

@[simp] theorem act_sym (σ : GStore S X) (s : S) : act σ (.sym s) = .sym s := rfl
@[simp] theorem act_fn (σ : GStore S X) (F : S) : act σ (.fn F) = .fn F := rfl

/-- The action never touches a parameter occurrence. -/
@[simp] theorem act_pvar (σ : GStore S X) (x : Nm X) :
    act σ (.pvar x) = .pvar x := rfl

/-- The action never enters a sealed quotation. -/
@[simp] theorem act_quote (σ : GStore S X) (c : Tm S X) :
    act σ (.quote c) = .quote c := rfl

/-- The action never enters contextual code. -/
@[simp] theorem act_ctx (σ : GStore S X) (ks : List (Nm X)) (c : Tm S X) :
    act σ (.ctx ks c) = .ctx ks c := rfl

/-- The action fills a store-name occurrence from the store. -/
theorem act_var (σ : GStore S X) (n : Nm X) :
    act σ (.var n) = match σ n with
      | some g => g.toTm
      | Option.none => .var n := by
  unfold act subst envSub
  cases σ n <;> rfl

/-- Under a lambda the action keeps the parameter declaration, leaves the
lambda's own names to activation, and continues on the body. -/
theorem act_lam (σ : GStore S X) (x : Nm X) (own : List X) (b : Tm S X) :
    act σ (.lam x own b) = .lam x own (act (σ.hide own) b) := by
  simp only [act, subst, envSub_hideOwn, none_hideParam]

@[simp] theorem act_app (σ : GStore S X) (f a : Tm S X) :
    act σ (.app f a) = .app (act σ f) (act σ a) := rfl

/-- In a pattern-position quotation the action fills the holes. -/
@[simp] theorem act_pquote (σ : GStore S X) (c : Tm S X) :
    act σ (.pquote c) = .pquote (act σ c) := rfl

@[simp] theorem act_letP (σ : GStore S X) (p w b : Tm S X) :
    act σ (.letP p w b) = .letP (act σ p) (act σ w) (act σ b) := rfl

@[simp] theorem act_alt (σ : GStore S X) (t₁ t₂ : Tm S X) :
    act σ (.alt t₁ t₂) = .alt (act σ t₁) (act σ t₂) := rfl

/-- **Absorption.**  Applying `σ` and then a refinement `τ ⊒ σ` is applying
`τ`.  A consumer may therefore be handed the current store at its
transition, whatever earlier applications happened. -/
theorem act_absorb {σ τ : GStore S X} (h : σ ⊑ τ) (t : Tm S X) :
    act τ (act σ t) = act τ t := by
  induction t generalizing σ τ with
  | sym s => rfl
  | fn F => rfl
  | var n =>
      rw [act_var σ n]
      cases hσ : σ n with
      | none => rfl
      | some g =>
          simp only
          rw [act_toTm, act_var τ n, h n g hσ]
  | pvar x => rfl
  | lam x own b ih =>
      rw [act_lam, act_lam, act_lam]
      exact congrArg _ (ih (GStore.hide_le h own))
  | app f a ihf iha => simp [ihf h, iha h]
  | quote c => rfl
  | ctx ks c => rfl
  | pquote c ih => simp [ih h]
  | letP p w b ihp ihw ihb => simp [ihp h, ihw h, ihb h]
  | alt t₁ t₂ ih₁ ih₂ => simp [ih₁ h, ih₂ h]

/-- **Idempotence.** -/
theorem act_idem (σ : GStore S X) (t : Tm S X) : act σ (act σ t) = act σ t :=
  act_absorb (Store.LE.refl σ) t

/-! ## Occurrence locality -/

/-- One step of a one-hole context. -/
inductive Frame (S : Type u) (X : Type v) where
  | lamBody (x : Nm X) (own : List X)
  | appL (a : Tm S X)
  | appR (f : Tm S X)
  | quoteC
  | pquoteC
  | letPat (w b : Tm S X)
  | letVal (p b : Tm S X)
  | letBody (p w : Tm S X)
  | altL (t₂ : Tm S X)
  | altR (t₁ : Tm S X)

/-- What a frame contributes to the action at the hole: nothing, binders, or
a seal.  Siblings are not part of it. -/
inductive FrameKind (X : Type v) where
  | through
  | binder (own : List X)
  | seal

namespace Frame

/-- Put a term into one frame. -/
def plug : Frame S X → Tm S X → Tm S X
  | .lamBody x own, t => .lam x own t
  | .appL a, t => .app t a
  | .appR f, t => .app f t
  | .quoteC, t => .quote t
  | .pquoteC, t => .pquote t
  | .letPat w b, t => .letP t w b
  | .letVal p b, t => .letP p t b
  | .letBody p w, t => .letP p w t
  | .altL t₂, t => .alt t t₂
  | .altR t₁, t => .alt t₁ t

/-- The kind of a frame. -/
def kind : Frame S X → FrameKind X
  | .lamBody _ own => .binder own
  | .quoteC => .seal
  | _ => .through

/-- The action on the siblings a frame holds. -/
def act (σ : GStore S X) : Frame S X → Frame S X
  | .lamBody x own => .lamBody x own
  | .appL a => .appL (TemplateScope.act σ a)
  | .appR f => .appR (TemplateScope.act σ f)
  | .quoteC => .quoteC
  | .pquoteC => .pquoteC
  | .letPat w b => .letPat (TemplateScope.act σ w) (TemplateScope.act σ b)
  | .letVal p b => .letVal (TemplateScope.act σ p) (TemplateScope.act σ b)
  | .letBody p w => .letBody (TemplateScope.act σ p) (TemplateScope.act σ w)
  | .altL t₂ => .altL (TemplateScope.act σ t₂)
  | .altR t₁ => .altR (TemplateScope.act σ t₁)

end Frame

/-- A context, outermost frame first. -/
def plug : List (Frame S X) → Tm S X → Tm S X
  | [], t => t
  | F :: K, t => F.plug (plug K t)

/-- The action on a context's siblings. -/
def ctxAct (σ : GStore S X) : List (Frame S X) → List (Frame S X)
  | [] => []
  | .lamBody x own :: K => .lamBody x own :: ctxAct (σ.hide own) K
  | .quoteC :: K => .quoteC :: K
  | F :: K => F.act σ :: ctxAct σ K

/-- The action at a hole, computed from the frame kinds alone. -/
def holeAct (σ : GStore S X) : List (FrameKind X) → Tm S X → Tm S X
  | [], t => act σ t
  | .through :: K, t => holeAct σ K t
  | .binder own :: K, t => holeAct (σ.hide own) K t
  | .seal :: _, t => t

/-- **Occurrence locality.**  The action on a plugged term is the action on
the context's siblings around the action at the hole, and the latter is
computed from the hole's content, the store and the kinds of the frames on
the path: binders and seals.  No sibling enters it. -/
theorem act_plug (σ : GStore S X) (K : List (Frame S X)) (t : Tm S X) :
    act σ (plug K t) = plug (ctxAct σ K) (holeAct σ (K.map Frame.kind) t) := by
  induction K generalizing σ with
  | nil => rfl
  | cons F K ih =>
      cases F with
      | lamBody x own =>
          simp only [plug, Frame.plug, act_lam, ih, ctxAct, List.map, Frame.kind, holeAct]
      | quoteC => rfl
      | appL a => simp only [plug, Frame.plug, act_app, ih, ctxAct, Frame.act, List.map,
            Frame.kind, holeAct]
      | appR f => simp only [plug, Frame.plug, act_app, ih, ctxAct, Frame.act, List.map,
            Frame.kind, holeAct]
      | pquoteC => simp only [plug, Frame.plug, act_pquote, ih, ctxAct, Frame.act, List.map,
            Frame.kind, holeAct]
      | letPat w b => simp only [plug, Frame.plug, act_letP, ih, ctxAct, Frame.act, List.map,
            Frame.kind, holeAct]
      | letVal p b => simp only [plug, Frame.plug, act_letP, ih, ctxAct, Frame.act, List.map,
            Frame.kind, holeAct]
      | letBody p w => simp only [plug, Frame.plug, act_letP, ih, ctxAct, Frame.act, List.map,
            Frame.kind, holeAct]
      | altL t₂ => simp only [plug, Frame.plug, act_alt, ih, ctxAct, Frame.act, List.map,
            Frame.kind, holeAct]
      | altR t₁ => simp only [plug, Frame.plug, act_alt, ih, ctxAct, Frame.act, List.map,
            Frame.kind, holeAct]

/-- Two contexts with the same binders and seals on the path to the hole give
the same action at the hole, whatever their siblings: a sibling, such as a
branch that never runs and mentions the same spelling in a pattern, cannot
change it. -/
theorem act_hole_local (σ : GStore S X) {K₁ K₂ : List (Frame S X)}
    (hK : K₁.map Frame.kind = K₂.map Frame.kind) (t : Tm S X) :
    holeAct σ (K₁.map Frame.kind) t = holeAct σ (K₂.map Frame.kind) t := by
  rw [hK]

/-- Under a seal, the hole is untouched whatever the store. -/
theorem holeAct_seal (σ : GStore S X) (K : List (FrameKind X)) (t : Tm S X) :
    holeAct σ (.seal :: K) t = t := rfl

end Mettapedia.GSLT.LanguageDef.TemplateScope
