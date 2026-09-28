import Mettapedia.Logic.HOL.ProofSyntaxModulo

/-!
# Kripke models of proofs modulo conversion

A Kripke model over a preorder of worlds reads a proposition as an
upward-closed set of worlds, a base type as a given type, and a function type
as all functions. Implication holds at a world when the conclusion holds at
every later world where the premise holds; the universal quantifier ranges over
every element of its type, so quantification over propositions ranges over
every upward-closed set. Equality is read as equality of the denotations,
everywhere or nowhere.

Denotation commutes with renaming and substitution (`denote_rename`,
`denote_subst`), a definitional step preserves it in every model of the
equations (`sourceStep_denote`), and every proof modulo the equations is sound
(`proofSyntaxModulo_sound`): at every world where the hypotheses hold, the
conclusion holds.

A two-world model refutes excluded middle, so, unlike Henkin models, these
models separate intuitionistic from classical consequences of proofs modulo
conversion.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.KripkeModulo

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- A preorder of worlds. -/
structure Frame where
  World : Type
  le : World → World → Prop
  le_refl : ∀ w, le w w
  le_trans : ∀ {u v w}, le u v → le v w → le u w

/-- An upward-closed proposition of a frame. -/
structure Frame.Up (F : Frame) where
  holds : F.World → Prop
  mono : ∀ {w v}, F.le w v → holds w → holds v

theorem Frame.Up.ext {F : Frame} {p q : F.Up} (h : p.holds = q.holds) : p = q := by
  cases p
  cases q
  cases h
  rfl

namespace Frame

variable (F : Frame)

/-- A proposition holding everywhere or nowhere. -/
def constUp (P : Prop) : F.Up := ⟨fun _ => P, fun _ h => h⟩

/-- Implication, at all later worlds. -/
def impUp (p q : F.Up) : F.Up :=
  ⟨fun w => ∀ v, F.le w v → p.holds v → q.holds v,
    fun hwv h u hvu hp => h u (F.le_trans hwv hvu) hp⟩

def andUp (p q : F.Up) : F.Up :=
  ⟨fun w => p.holds w ∧ q.holds w, fun hwv h => ⟨p.mono hwv h.1, q.mono hwv h.2⟩⟩

def orUp (p q : F.Up) : F.Up :=
  ⟨fun w => p.holds w ∨ q.holds w, fun hwv h => h.elim (fun hp => .inl (p.mono hwv hp))
    (fun hq => .inr (q.mono hwv hq))⟩

def allUp {α : Type} (f : α → F.Up) : F.Up :=
  ⟨fun w => ∀ x, (f x).holds w, fun hwv h x => (f x).mono hwv (h x)⟩

def exUp {α : Type} (f : α → F.Up) : F.Up :=
  ⟨fun w => ∃ x, (f x).holds w, fun hwv h => h.elim fun x hx => ⟨x, (f x).mono hwv hx⟩⟩

end Frame

/-- The denotation of a simple type: upward-closed propositions, the given
base types, and all functions. -/
def Den (F : Frame) (Carrier : Base → Type) : Ty Base → Type
  | .prop => F.Up
  | .base b => Carrier b
  | .arr a b => Den F Carrier a → Den F Carrier b

/-- A Kripke model of a signature. -/
structure Model (Base : Type u) (Const : Ty Base → Type v) where
  frame : Frame
  Carrier : Base → Type
  constDen : {τ : Ty Base} → Const τ → Den frame Carrier τ

namespace Model

variable (M : Model Base Const)

abbrev D (τ : Ty Base) : Type := Den M.frame M.Carrier τ

abbrev Valuation (Γ : Ctx Base) : Type (u) := ∀ {τ : Ty Base}, Var Γ τ → M.D τ

def extend {Γ : Ctx Base} {σ : Ty Base} (ρ : M.Valuation Γ) (x : M.D σ) :
    M.Valuation (σ :: Γ)
  | _, .vz => x
  | _, .vs i => ρ i

/-- The denotation of a term at a valuation. -/
def denote : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → M.Valuation Γ → M.D τ
  | _, _, .var i, ρ => ρ i
  | _, _, .const c, _ => M.constDen c
  | _, _, .app f a, ρ => (denote f ρ) (denote a ρ)
  | _, _, .lam b, ρ => fun x => denote b (M.extend ρ x)
  | _, _, .top, _ => M.frame.constUp True
  | _, _, .bot, _ => M.frame.constUp False
  | _, _, .and p q, ρ => M.frame.andUp (denote p ρ) (denote q ρ)
  | _, _, .or p q, ρ => M.frame.orUp (denote p ρ) (denote q ρ)
  | _, _, .imp p q, ρ => M.frame.impUp (denote p ρ) (denote q ρ)
  | _, _, .not p, ρ => M.frame.impUp (denote p ρ) (M.frame.constUp False)
  | _, _, .eq l r, ρ => M.frame.constUp (denote l ρ = denote r ρ)
  | _, _, .all b, ρ => M.frame.allUp fun x => denote b (M.extend ρ x)
  | _, _, .ex b, ρ => M.frame.exUp fun x => denote b (M.extend ρ x)

/-! ## Renaming and substitution -/

theorem denote_rename {Γ Δ : Ctx Base} {τ : Ty Base} (r : Rename Base Γ Δ)
    (t : Term Const Γ τ) (ν : M.Valuation Δ) :
    M.denote (rename r t) ν = M.denote t (fun i => ν (r i)) := by
  induction t generalizing Δ with
  | var | const | top | bot => rfl
  | app _ _ ihf iha => simp only [rename, denote, ihf, iha]
  | and _ _ ihp ihq | or _ _ ihp ihq | imp _ _ ihp ihq | eq _ _ ihp ihq =>
      simp only [rename, denote, ihp, ihq]
      rfl
  | not _ ih =>
      simp only [rename, denote, ih]
      rfl
  | lam _ ih =>
      funext x
      simp only [rename, denote]
      rw [ih]
      congr 1
      funext τ i
      cases i <;> rfl
  | all _ ih | ex _ ih =>
      simp only [rename, denote]
      congr 1
      funext x
      rw [ih]
      congr 1
      funext τ i
      cases i <;> rfl

theorem denote_weaken {Γ : Ctx Base} {σ τ : Ty Base} (t : Term Const Γ τ) (ρ : M.Valuation Γ)
    (x : M.D σ) : M.denote (weaken t) (M.extend ρ x) = M.denote t ρ :=
  M.denote_rename Rename.weaken t (M.extend ρ x)

theorem denote_subst {Γ Δ : Ctx Base} {τ : Ty Base} (s : Subst Const Γ Δ)
    (t : Term Const Γ τ) (ν : M.Valuation Δ) :
    M.denote (subst s t) ν = M.denote t (fun i => M.denote (s i) ν) := by
  induction t generalizing Δ with
  | var | const | top | bot => rfl
  | app _ _ ihf iha => simp only [subst, denote, ihf, iha]
  | and _ _ ihp ihq | or _ _ ihp ihq | imp _ _ ihp ihq | eq _ _ ihp ihq =>
      simp only [subst, denote, ihp, ihq]
      rfl
  | not _ ih =>
      simp only [subst, denote, ih]
      rfl
  | lam _ ih =>
      funext x
      simp only [subst, denote]
      rw [ih]
      congr 1
      funext τ i
      cases i with
      | vz => rfl
      | vs i => exact M.denote_weaken _ ν x
  | all _ ih | ex _ ih =>
      simp only [subst, denote]
      congr 1
      funext x
      rw [ih]
      congr 1
      funext τ i
      cases i with
      | vz => rfl
      | vs i => exact M.denote_weaken _ ν x

theorem denote_instantiate {Γ : Ctx Base} {σ τ : Ty Base} (a : Term Const Γ σ)
    (b : Term Const (σ :: Γ) τ) (ρ : M.Valuation Γ) :
    M.denote (instantiate a b) ρ = M.denote b (M.extend ρ (M.denote a ρ)) := by
  rw [instantiate, denote_subst]
  congr 1
  funext τ i
  cases i <;> rfl

/-! ## Conversion and soundness -/

/-- The defining equations hold: both sides denote the same value at every
valuation of the pattern telescope. -/
def EquationsHold (equations : List (DefiningEquation Const)) : Prop :=
  ∀ equation ∈ equations, ∀ ρ : M.Valuation equation.context,
    M.denote equation.left ρ = M.denote equation.right ρ

theorem sourceStep_denote {equations : List (DefiningEquation Const)}
    (hold : M.EquationsHold equations) {Γ : Ctx Base} {τ : Ty Base}
    {s t : Term Const Γ τ} (step : SourceStep equations s t) :
    ∀ ρ : M.Valuation Γ, M.denote s ρ = M.denote t ρ := by
  induction step with
  | beta body argument =>
      intro ρ
      exact (M.denote_instantiate argument body ρ).symm
  | delta equation listed substitution _ =>
      intro ρ
      rw [M.denote_subst, M.denote_subst]
      exact hold equation listed _
  | appFun argument _ ih => intro ρ; exact congrFun (ih ρ) _
  | appArg function _ ih => intro ρ; exact congrArg (M.denote function ρ) (ih ρ)
  | lam _ ih => intro ρ; funext x; exact ih _
  | impLeft right _ ih => intro ρ; exact congrArg (M.frame.impUp · _) (ih ρ)
  | impRight left _ ih => intro ρ; exact congrArg (M.frame.impUp _ ·) (ih ρ)
  | eqLeft right _ ih => intro ρ; exact congrArg (fun x => M.frame.constUp (x = _)) (ih ρ)
  | eqRight left _ ih => intro ρ; exact congrArg (fun x => M.frame.constUp (_ = x)) (ih ρ)
  | all _ ih => intro ρ; exact congrArg M.frame.allUp (funext fun x => ih _)

theorem coreConversion_denote {equations : List (DefiningEquation Const)}
    (hold : M.EquationsHold equations) {Γ : Ctx Base} {τ : Ty Base}
    {s t : Term Const Γ τ} (conversion : CoreConversion equations s t) (ρ : M.Valuation Γ) :
    M.denote s ρ = M.denote t ρ := by
  induction conversion with
  | rel _ _ step => exact M.sourceStep_denote hold step.2.2 ρ
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **Soundness.** At every world where the hypotheses hold, the conclusion of
a proof modulo the equations holds, in every Kripke model of the equations. -/
theorem proofSyntaxModulo_sound {equations : List (DefiningEquation Const)}
    (hold : M.EquationsHold equations) {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (proof : ProofSyntaxModulo equations Δ φ) :
    ∀ (ρ : M.Valuation Γ) (w : M.frame.World), (∀ δ ∈ Δ, (M.denote δ ρ).holds w) →
      (M.denote φ ρ).holds w := by
  induction proof with
  | hyp occurrence => exact fun ρ w hyps => hyps _ (List.get_mem _ occurrence)
  | impI _ ih =>
      intro ρ w hyps v hwv hp
      refine ih ρ v fun δ listed => ?_
      rcases List.mem_cons.mp listed with rfl | listed
      · exact hp
      · exact (M.denote δ ρ).mono hwv (hyps δ listed)
  | impE _ _ ihf iha =>
      intro ρ w hyps
      exact ihf ρ w hyps w (M.frame.le_refl w) (iha ρ w hyps)
  | allI _ ih =>
      intro ρ w hyps x
      refine ih (M.extend ρ x) w fun δ listed => ?_
      obtain ⟨δ₀, listed₀, rfl⟩ := List.mem_map.mp listed
      rw [M.denote_weaken]
      exact hyps δ₀ listed₀
  | allE term _ ih =>
      intro ρ w hyps
      rw [M.denote_instantiate]
      exact ih ρ w hyps (M.denote term ρ)
  | convert conversion _ ih =>
      intro ρ w hyps
      rw [← M.coreConversion_denote hold conversion ρ]
      exact ih ρ w hyps

end Model

end Mettapedia.Logic.HOL.KripkeModulo
