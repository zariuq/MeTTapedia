import Mettapedia.Logic.HOL.Soundness

/-!
# Impredicative elimination of derived HOL connectives

Truth, falsity, conjunction, disjunction, negation and existence are expressed
using implication and quantification over propositions. The transformation acts
on the existing intrinsically typed HOL syntax, preserving constants, equality,
application and abstraction. It commutes with renaming and substitution and
preserves denotation in every existing Henkin model, including restricted
function domains. No classical principle or choice operator is inserted into
the object language.

These are the implication/quantifier encodings used by the Megalodon logical
preamble. Equality is retained as supplied by the source signature; this module
does not identify its primitive equality with a particular Leibniz definition.
-/

namespace Mettapedia.Logic.HOL.ImpredicativeConnectives

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ Δ : Ctx Base} {τ : Ty Base}

def truth : Formula Const Γ := .all (.imp (.var .vz) (.var .vz))

def falsity : Formula Const Γ := .all (.var .vz)

def conjunction : Term Const Γ (propTy ⇒ propTy ⇒ propTy) :=
  .lam (.lam (.all (.imp
    (.imp (.var (.vs (.vs .vz))) (.imp (.var (.vs .vz)) (.var .vz)))
    (.var .vz))))

def disjunction : Term Const Γ (propTy ⇒ propTy ⇒ propTy) :=
  .lam (.lam (.all (.imp
    (.imp (.var (.vs (.vs .vz))) (.var .vz))
    (.imp (.imp (.var (.vs .vz)) (.var .vz)) (.var .vz)))))

def existential (σ : Ty Base) : Term Const Γ ((σ ⇒ propTy) ⇒ propTy) :=
  .lam (.all (.imp
    (.all (.imp (.app (.var (.vs (.vs .vz))) (.var .vz)) (.var (.vs .vz))))
    (.var .vz)))

/-- The target grammar retains arbitrary typed constants, lambda terms and
equality; only the six derived logical constructors are eliminated. -/
def IsCore : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Prop
  | _, _, .var _ | _, _, .const _ => True
  | _, _, .app f a => IsCore f ∧ IsCore a
  | _, _, .lam b | _, _, .all b => IsCore b
  | _, _, .imp p q | _, _, .eq p q => IsCore p ∧ IsCore q
  | _, _, .top | _, _, .bot | _, _, .and .. | _, _, .or ..
  | _, _, .not .. | _, _, .ex .. => False

/-- A total, type-preserving translation on the original HOL syntax. -/
def expand : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Term Const Γ τ
  | _, _, .var i => .var i
  | _, _, .const c => .const c
  | _, _, .app f a => .app (expand f) (expand a)
  | _, _, .lam b => .lam (expand b)
  | _, _, .top => truth
  | _, _, .bot => falsity
  | _, _, .and p q => .app (.app conjunction (expand p)) (expand q)
  | _, _, .or p q => .app (.app disjunction (expand p)) (expand q)
  | _, _, .imp p q => .imp (expand p) (expand q)
  | _, _, .not p => .imp (expand p) falsity
  | _, _, .eq p q => .eq (expand p) (expand q)
  | _, _, .all b => .all (expand b)
  | _, _, @Term.ex _ _ σ _ b => .app (existential σ) (.lam (expand b))

theorem expand_isCore (t : Term Const Γ τ) : IsCore (expand t) := by
  induction t <;>
    simp_all [expand, IsCore, truth, falsity, conjunction, disjunction, existential]

theorem expand_of_isCore (t : Term Const Γ τ) (h : IsCore t) : expand t = t := by
  induction t <;> simp_all [IsCore, expand]

theorem expand_idempotent (t : Term Const Γ τ) : expand (expand t) = expand t :=
  expand_of_isCore _ (expand_isCore t)

/-- Expansion introduces fixed-size operators and never duplicates an input
subterm. This bounds term nodes, not normalization time or runtime allocation. -/
theorem nodeCount_expand_le (t : Term Const Γ τ) :
    (expand t).nodeCount ≤ 14 * t.nodeCount := by
  induction t <;>
    simp only [expand, Term.nodeCount, truth, falsity, conjunction, disjunction,
      existential] at * <;> omega

theorem expand_rename (ρ : Rename Base Γ Δ) (t : Term Const Γ τ) :
    expand (rename ρ t) = rename ρ (expand t) := by
  induction t generalizing Δ <;>
    simp_all [expand, rename, truth, falsity, conjunction, disjunction, existential,
      Rename.lift]

private theorem expand_lift {σ : Ty Base} (σs : Subst Const Γ Δ) :
    (fun {τ} (i : Var (σ :: Γ) τ) => expand (Subst.lift σs i)) =
      (Subst.lift (fun i => expand (σs i)) : Subst Const (σ :: Γ) (σ :: Δ)) := by
  funext τ i
  cases i with
  | vz => rfl
  | vs i => exact expand_rename _ _

theorem expand_subst (σs : Subst Const Γ Δ) (t : Term Const Γ τ) :
    expand (subst σs t) = subst (fun i => expand (σs i)) (expand t) := by
  induction t generalizing Δ with
  | var i => rfl
  | const c => rfl
  | app f a ihf iha => simp only [subst, expand, ihf, iha]
  | lam b ih | all b ih | ex b ih =>
      simp only [subst, expand, ih, expand_lift] <;> rfl
  | top | bot => rfl
  | and p q ihp ihq | or p q ihp ihq | imp p q ihp ihq | eq p q ihp ihq =>
      simp only [subst, expand, ihp, ihq] <;> rfl
  | not p ih => simp only [subst, expand, ih]; rfl

private theorem denote_truth (M : HenkinModel.{u, v, w} Base Const)
    (ρ : M.Valuation Γ) : M.denote truth ρ = .up True := by
  apply ULift.ext
  apply propext
  simp [truth, PreModel.denote, PreModel.extend]

private theorem denote_falsity (M : HenkinModel.{u, v, w} Base Const)
    (ρ : M.Valuation Γ) : M.denote falsity ρ = .up False := by
  apply ULift.ext
  apply propext
  change (∀ p, M.adm propTy p → p.down) ↔ False
  exact ⟨fun h => h (.up False) (M.prop_mem _), False.elim⟩

private theorem denote_conjunction (M : HenkinModel.{u, v, w} Base Const)
    (ρ : M.Valuation Γ) (p q : Ty.denote M.Carrier propTy) :
    M.denote conjunction ρ p q = .up (p.down ∧ q.down) := by
  apply ULift.ext
  apply propext
  change (∀ r, M.adm propTy r → (p.down → q.down → r.down) → r.down) ↔ _
  constructor
  · intro h
    exact h (.up (p.down ∧ q.down)) (M.prop_mem _) And.intro
  · rintro ⟨hp, hq⟩ r _ f
    exact f hp hq

private theorem denote_disjunction (M : HenkinModel.{u, v, w} Base Const)
    (ρ : M.Valuation Γ) (p q : Ty.denote M.Carrier propTy) :
    M.denote disjunction ρ p q = .up (p.down ∨ q.down) := by
  apply ULift.ext
  apply propext
  change (∀ r, M.adm propTy r → (p.down → r.down) →
    (q.down → r.down) → r.down) ↔ _
  constructor
  · intro h
    exact h (.up (p.down ∨ q.down)) (M.prop_mem _) Or.inl Or.inr
  · intro h r _ f g
    exact h.elim f g

private theorem denote_existential (M : HenkinModel.{u, v, w} Base Const)
    (ρ : M.Valuation Γ) (σ : Ty Base) (p : Ty.denote M.Carrier (σ ⇒ propTy)) :
    M.denote (existential σ) ρ p = .up (∃ x, M.adm σ x ∧ (p x).down) := by
  apply ULift.ext
  apply propext
  change (∀ r, M.adm propTy r → (∀ x, M.adm σ x → (p x).down → r.down) →
    r.down) ↔ _
  constructor
  · intro h
    exact h (.up (∃ x, M.adm σ x ∧ (p x).down)) (M.prop_mem _)
      (fun x hx hp => ⟨x, hx, hp⟩)
  · rintro ⟨x, hx, hp⟩ r _ f
    exact f x hx hp

/-- Equality of denotations holds at every simple type and every environment,
not just for closed propositions or full function-space models. -/
theorem denote_expand (M : HenkinModel.{u, v, w} Base Const)
    (t : Term Const Γ τ) (ρ : M.Valuation Γ) :
    M.denote (expand t) ρ = M.denote t ρ := by
  induction t with
  | var i | const i => rfl
  | top => exact denote_truth M ρ
  | bot => exact denote_falsity M ρ
  | app f a ihf iha => simp only [expand, PreModel.denote, ihf, iha]
  | lam b ih => funext x; exact ih _
  | imp p q ihp ihq | eq p q ihp ihq =>
      simp only [expand, PreModel.denote, ihp, ihq]
      rfl
  | and p q ihp ihq =>
      change M.denote conjunction ρ (M.denote (expand p) ρ) (M.denote (expand q) ρ) =
        .up ((M.denote p ρ).down ∧ (M.denote q ρ).down)
      erw [denote_conjunction, ihp, ihq]
  | or p q ihp ihq =>
      change M.denote disjunction ρ (M.denote (expand p) ρ) (M.denote (expand q) ρ) =
        .up ((M.denote p ρ).down ∨ (M.denote q ρ).down)
      erw [denote_disjunction, ihp, ihq]
  | not p ih =>
      change ULift.up ((M.denote (expand p) ρ).down → (M.denote falsity ρ).down) =
        ULift.up (¬ (M.denote p ρ).down)
      erw [denote_falsity, ih]
  | all b ih => simp only [expand, PreModel.denote, ih]; rfl
  | @ex σ Γ b ih =>
      change M.denote (existential σ) ρ
        (fun x => M.denote (expand b) (M.extend ρ x)) =
          .up (∃ x, M.adm σ x ∧ (M.denote b (M.extend ρ x)).down)
      erw [denote_existential]
      simp only [ih]
      rfl

theorem models_expand (M : HenkinModel.{u, v, w} Base Const)
    (φ : ClosedFormula Const) : M.models (expand φ) ↔ M.models φ := by
  exact Iff.of_eq (congrArg ULift.down (denote_expand M φ (fun i => nomatch i)))

/-- Logical expansion does not turn a false input into an accepted truth. -/
theorem not_models_expanded_false (M : HenkinModel.{u, v, w} Base Const) :
    ¬ M.models (expand (.and .top .bot)) := by
  rw [models_expand]
  exact fun h => h.2

/-- Quantification over propositions suffices for the positive control. -/
theorem models_expanded_existential (M : HenkinModel.{u, v, w} Base Const) :
    M.models (expand (.ex (.var (.vz : Var [propTy] propTy)))) := by
  apply (models_expand M _).mpr
  exact ⟨.up True, M.prop_mem _, True.intro⟩

#print axioms expand_subst
#print axioms nodeCount_expand_le
#print axioms denote_expand

end Mettapedia.Logic.HOL.ImpredicativeConnectives
