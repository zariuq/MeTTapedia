import Mettapedia.Logic.HOL.ProofSyntaxModulo
import Mettapedia.Logic.HOL.ProofSyntaxStructural

/-!
# Structural operations on proofs modulo definitional conversion

The proofs of `ProofSyntaxModulo` are closed under the structural operations
of the source. Each operation keeps every rule of the proof and changes only
its sequent indices:

* **assumption transport** along an explicit occurrence map (`mono`);
* **renaming** of the object variables (`rename`, and `weaken` for one new
  variable);
* **substitution** of core terms for the object variables (`subst`, and
  `instantiate` for the newest variable). A definitional step instantiates an
  equation by core terms, so only a substitution whose images are core keeps
  the steps of an article (`CoreSubst`);
* **constant maps** that send every listed equation to a listed equation
  (`mapConst`).

A proof *uses* an assumption when one of its hypothesis rules refers to it
(`usesHyp`); `usedHyps` lists the used assumptions in order.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Core terms under the structural operations -/

/-- A substitution whose images are core terms. -/
abbrev CoreSubst {Γ Δ : Ctx Base} (θ : Subst Const Γ Δ) : Prop :=
  ∀ {τ : Ty Base} (i : Var Γ τ), (θ i).isCore = true

namespace Term

@[simp] theorem isCore_rename {Γ Δ : Ctx Base} {τ : Ty Base} (ρ : Rename Base Γ Δ)
    (t : Term Const Γ τ) : (HOL.rename ρ t).isCore = t.isCore := by
  induction t generalizing Δ <;> simp_all [HOL.rename, isCore]

@[simp] theorem isCore_mapConst {Const' : Ty Base → Type w}
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ) {Γ : Ctx Base} {τ : Ty Base}
    (t : Term Const Γ τ) : (HOL.mapConst f t).isCore = t.isCore := by
  induction t <;> simp_all [HOL.mapConst, isCore]

end Term

namespace CoreSubst

theorem lift {Γ Δ : Ctx Base} {θ : Subst Const Γ Δ} (core : CoreSubst θ) {σ : Ty Base} :
    CoreSubst (Subst.lift (σ := σ) θ) := by
  intro τ i
  cases i with
  | vz => rfl
  | vs i =>
      change (HOL.rename Rename.weaken (θ i)).isCore = true
      rw [Term.isCore_rename]
      exact core i

theorem single {Γ : Ctx Base} {σ : Ty Base} {t : Term Const Γ σ} (core : t.isCore = true) :
    CoreSubst (Subst.single t) := by
  intro τ i
  cases i with
  | vz => exact core
  | vs _ => rfl

theorem ofRename {Γ Δ : Ctx Base} (ρ : Rename Base Γ Δ) :
    CoreSubst (Subst.ofRename (Const := Const) ρ) :=
  fun _ => rfl

end CoreSubst

theorem Term.isCore_subst {Γ Δ : Ctx Base} {θ : Subst Const Γ Δ} (core : CoreSubst θ)
    {τ : Ty Base} {t : Term Const Γ τ} (h : t.isCore = true) : (HOL.subst θ t).isCore = true := by
  induction t generalizing Δ with
  | var i => exact core i
  | const => rfl
  | app f a ihf iha =>
      simp only [isCore, Bool.and_eq_true] at h
      simp only [HOL.subst, isCore, ihf core h.1, iha core h.2, Bool.and_self]
  | lam b ih => exact ih core.lift h
  | imp p q ihp ihq =>
      simp only [isCore, Bool.and_eq_true] at h
      simp only [HOL.subst, isCore, ihp core h.1, ihq core h.2, Bool.and_self]
  | eq l r ihl ihr =>
      simp only [isCore, Bool.and_eq_true] at h
      simp only [HOL.subst, isCore, ihl core h.1, ihr core h.2, Bool.and_self]
  | all b ih => exact ih core.lift h
  | top | bot | and | or | not | ex => simp [isCore] at h

/-! ## Equations under constant maps -/

/-- The image of a defining equation under a constant map. -/
def DefiningEquation.mapConst {Const' : Ty Base → Type w}
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ) (equation : DefiningEquation Const) :
    DefiningEquation Const' where
  context := equation.context
  type := equation.type
  left := HOL.mapConst f equation.left
  right := HOL.mapConst f equation.right

/-! ## Definitional steps and conversion articles under the structural operations -/

section Steps

variable {eqs : List (DefiningEquation Const)}

theorem SourceStep.rename {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ}
    (step : SourceStep eqs s t) :
    ∀ {Δ : Ctx Base} (ρ : Rename Base Γ Δ), SourceStep eqs (HOL.rename ρ s) (HOL.rename ρ t) := by
  induction step with
  | beta body argument =>
      intro Δ ρ
      rw [ExtDerivation.rename_instantiate]
      exact .beta _ _
  | delta equation listed substitution core =>
      intro Δ ρ
      rw [rename_subst, rename_subst]
      exact .delta equation listed _ fun i => by rw [Term.isCore_rename]; exact core i
  | appFun argument _ ih => intro Δ ρ; exact .appFun _ (ih ρ)
  | appArg function _ ih => intro Δ ρ; exact .appArg _ (ih ρ)
  | lam _ ih => intro Δ ρ; exact .lam (ih (Rename.lift ρ))
  | impLeft right _ ih => intro Δ ρ; exact .impLeft _ (ih ρ)
  | impRight left _ ih => intro Δ ρ; exact .impRight _ (ih ρ)
  | eqLeft right _ ih => intro Δ ρ; exact .eqLeft _ (ih ρ)
  | eqRight left _ ih => intro Δ ρ; exact .eqRight _ (ih ρ)
  | all _ ih => intro Δ ρ; exact .all (ih (Rename.lift ρ))

theorem SourceStep.subst {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ}
    (step : SourceStep eqs s t) :
    ∀ {Δ : Ctx Base} {θ : Subst Const Γ Δ}, CoreSubst θ →
      SourceStep eqs (HOL.subst θ s) (HOL.subst θ t) := by
  induction step with
  | beta body argument =>
      intro Δ θ _
      rw [ProofSyntax.subst_instantiate]
      exact .beta _ _
  | delta equation listed substitution core =>
      intro Δ θ coreθ
      rw [subst_comp, subst_comp]
      exact .delta equation listed _ fun i => Term.isCore_subst coreθ (core i)
  | appFun argument _ ih => intro Δ θ coreθ; exact .appFun _ (ih coreθ)
  | appArg function _ ih => intro Δ θ coreθ; exact .appArg _ (ih coreθ)
  | lam _ ih => intro Δ θ coreθ; exact .lam (ih coreθ.lift)
  | impLeft right _ ih => intro Δ θ coreθ; exact .impLeft _ (ih coreθ)
  | impRight left _ ih => intro Δ θ coreθ; exact .impRight _ (ih coreθ)
  | eqLeft right _ ih => intro Δ θ coreθ; exact .eqLeft _ (ih coreθ)
  | eqRight left _ ih => intro Δ θ coreθ; exact .eqRight _ (ih coreθ)
  | all _ ih => intro Δ θ coreθ; exact .all (ih coreθ.lift)

theorem SourceStep.mapConst {Const' : Ty Base → Type w} (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    {eqs' : List (DefiningEquation Const')}
    (listed : ∀ equation ∈ eqs, DefiningEquation.mapConst f equation ∈ eqs')
    {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ} (step : SourceStep eqs s t) :
    SourceStep eqs' (HOL.mapConst f s) (HOL.mapConst f t) := by
  induction step with
  | beta body argument =>
      rw [mapConst_instantiate]
      exact .beta _ _
  | delta equation mem substitution core =>
      rw [mapConst_subst, mapConst_subst]
      exact .delta (DefiningEquation.mapConst f equation) (listed equation mem) _
        fun i => by rw [Term.isCore_mapConst]; exact core i
  | appFun argument _ ih => exact .appFun _ ih
  | appArg function _ ih => exact .appArg _ ih
  | lam _ ih => exact .lam ih
  | impLeft right _ ih => exact .impLeft _ ih
  | impRight left _ ih => exact .impRight _ ih
  | eqLeft right _ ih => exact .eqLeft _ ih
  | eqRight left _ ih => exact .eqRight _ ih
  | all _ ih => exact .all ih

theorem CoreConversion.rename {Γ Δ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ}
    (ρ : Rename Base Γ Δ) (conversion : CoreConversion eqs s t) :
    CoreConversion eqs (HOL.rename ρ s) (HOL.rename ρ t) := by
  induction conversion with
  | rel a b step =>
      obtain ⟨ha, hb, source⟩ := step
      exact .rel _ _ ⟨by rw [Term.isCore_rename]; exact ha, by rw [Term.isCore_rename]; exact hb,
        source.rename ρ⟩
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem CoreConversion.subst {Γ Δ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ}
    {θ : Subst Const Γ Δ} (core : CoreSubst θ) (conversion : CoreConversion eqs s t) :
    CoreConversion eqs (HOL.subst θ s) (HOL.subst θ t) := by
  induction conversion with
  | rel a b step =>
      obtain ⟨ha, hb, source⟩ := step
      exact .rel _ _ ⟨Term.isCore_subst core ha, Term.isCore_subst core hb, source.subst core⟩
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem CoreConversion.mapConst {Const' : Ty Base → Type w}
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ) {eqs' : List (DefiningEquation Const')}
    (listed : ∀ equation ∈ eqs, DefiningEquation.mapConst f equation ∈ eqs')
    {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ} (conversion : CoreConversion eqs s t) :
    CoreConversion eqs' (HOL.mapConst f s) (HOL.mapConst f t) := by
  induction conversion with
  | rel a b step =>
      obtain ⟨ha, hb, source⟩ := step
      exact .rel _ _ ⟨by rw [Term.isCore_mapConst]; exact ha, by rw [Term.isCore_mapConst]; exact hb,
        source.mapConst f listed⟩
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

end Steps

/-! ## Proofs -/

namespace ProofSyntaxModulo

variable {eqs : List (DefiningEquation Const)}

/-- Change only equal sequent indices. -/
def castIndices {Γ : Ctx Base} {Δ Δ' : List (Formula Const Γ)} {φ ψ : Formula Const Γ}
    (assumptions : Δ = Δ') (conclusion : φ = ψ) (proof : ProofSyntaxModulo eqs Δ φ) :
    ProofSyntaxModulo eqs Δ' ψ :=
  assumptions ▸ conclusion ▸ proof

/-- Rule-by-rule assumption transport. Only hypothesis occurrences change. -/
def mono {Γ : Ctx Base} {Δ Δ' : List (Formula Const Γ)} {φ : Formula Const Γ}
    (transport : ProofSyntax.OccurrenceMap Δ Δ') (proof : ProofSyntaxModulo eqs Δ φ) :
    ProofSyntaxModulo eqs Δ' φ :=
  match proof with
  | .hyp occurrence => (transport.get_eq occurrence) ▸ .hyp (transport.index occurrence)
  | .impI body => .impI (mono (transport.lift _) body)
  | .impE function argument => .impE (mono transport function) (mono transport argument)
  | .allI body => .allI (mono (transport.map (weaken (σ := _))) body)
  | .allE term function => .allE term (mono transport function)
  | .convert article inner => .convert article (mono transport inner)

/-- Renaming of the object variables, through every rule. -/
def rename {Γ Γ' : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (ρ : Rename Base Γ Γ') (proof : ProofSyntaxModulo eqs Δ φ) :
    ProofSyntaxModulo eqs (Δ.map (HOL.rename ρ)) (HOL.rename ρ φ) :=
  match proof with
  | .hyp occurrence =>
      castIndices rfl (by simp) (.hyp (Δ := Δ.map (HOL.rename ρ)) (occurrence.cast (by simp)))
  | .impI body => .impI (rename ρ body)
  | .impE function argument => .impE (rename ρ function) (rename ρ argument)
  | .allI body =>
      .allI (castIndices (ExtDerivation.rename_weakenHyps ρ _).symm rfl
        (rename (Rename.lift ρ) body))
  | .allE term function =>
      castIndices rfl (ExtDerivation.rename_instantiate ρ term _).symm
        (.allE (HOL.rename ρ term) (rename ρ function))
  | .convert article inner => .convert (article.rename ρ) (rename ρ inner)

/-- Weakening by one new object variable. -/
def weaken {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} {σ : Ty Base}
    (proof : ProofSyntaxModulo eqs Δ φ) :
    ProofSyntaxModulo eqs (weakenHyps (σ := σ) Δ) (HOL.weaken (σ := σ) φ) :=
  proof.rename Rename.weaken

/-- Substitution of core terms for the object variables, through every rule. -/
def subst {Γ Γ' : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (θ : Subst Const Γ Γ') (core : CoreSubst θ) (proof : ProofSyntaxModulo eqs Δ φ) :
    ProofSyntaxModulo eqs (Δ.map (HOL.subst θ)) (HOL.subst θ φ) :=
  match proof with
  | .hyp occurrence =>
      castIndices rfl (by simp) (.hyp (Δ := Δ.map (HOL.subst θ)) (occurrence.cast (by simp)))
  | .impI body => .impI (subst θ core body)
  | .impE function argument => .impE (subst θ core function) (subst θ core argument)
  | .allI body =>
      .allI (castIndices (ProofSyntax.subst_weakenHyps θ _) rfl
        (subst (Subst.lift θ) core.lift body))
  | .allE term function =>
      castIndices rfl (ProofSyntax.subst_instantiate θ term _).symm
        (.allE (HOL.subst θ term) (subst θ core function))
  | .convert article inner => .convert (article.subst core) (subst θ core inner)

theorem weakenHyps_instantiate {Γ : Ctx Base} {σ : Ty Base} (t : Term Const Γ σ)
    (Δ : List (Formula Const Γ)) :
    (weakenHyps (σ := σ) Δ).map (HOL.subst (Subst.single t)) = Δ := by
  simp only [weakenHyps, List.map_map]
  conv_rhs => rw [← List.map_id Δ]
  apply List.map_congr_left
  intro φ _
  exact instantiate_weaken t φ

/-- **Specialization.** A proof under a new object variable, instantiated at a
core term. -/
def instantiate {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {σ : Ty Base}
    {φ : Formula Const (σ :: Γ)} (t : Term Const Γ σ) (core : t.isCore = true)
    (proof : ProofSyntaxModulo eqs (weakenHyps (σ := σ) Δ) φ) :
    ProofSyntaxModulo eqs Δ (HOL.instantiate t φ) :=
  castIndices (weakenHyps_instantiate t Δ) rfl (proof.subst (Subst.single t) (CoreSubst.single core))

/-- The image of a proof under a constant map that sends each listed equation
to a listed equation. -/
def mapConst {Const' : Ty Base → Type w} (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    {eqs' : List (DefiningEquation Const')}
    (listed : ∀ equation ∈ eqs, DefiningEquation.mapConst f equation ∈ eqs')
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntaxModulo eqs Δ φ) :
    ProofSyntaxModulo eqs' (Δ.map (HOL.mapConst f)) (HOL.mapConst f φ) :=
  match proof with
  | .hyp occurrence =>
      castIndices rfl (by simp) (.hyp (Δ := Δ.map (HOL.mapConst f)) (occurrence.cast (by simp)))
  | .impI body => .impI (mapConst f listed body)
  | .impE function argument => .impE (mapConst f listed function) (mapConst f listed argument)
  | .allI body =>
      .allI (castIndices (ExtDerivation.mapConst_weakenHyps f _).symm rfl
        (mapConst f listed body))
  | .allE term function =>
      castIndices rfl (mapConst_instantiate f term _).symm
        (.allE (HOL.mapConst f term) (mapConst f listed function))
  | .convert article inner => .convert (article.mapConst f listed) (mapConst f listed inner)

/-! ## The assumptions a proof uses -/

/-- Whether a hypothesis rule of the proof refers to the assumption. -/
def usesHyp : {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} → {φ : Formula Const Γ} →
    ProofSyntaxModulo eqs Δ φ → Fin Δ.length → Bool
  | _, _, _, .hyp occurrence, i => decide (occurrence = i)
  | _, _, _, .impI body, i => usesHyp body i.succ
  | _, _, _, .impE function argument, i => usesHyp function i || usesHyp argument i
  | _, _, _, .allI body, i => usesHyp body (i.cast (by simp [weakenHyps]))
  | _, _, _, .allE _ function, i => usesHyp function i
  | _, _, _, .convert _ inner, i => usesHyp inner i

/-- The used assumptions, in order. -/
def usedHyps {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntaxModulo eqs Δ φ) : List (Fin Δ.length) :=
  (List.finRange Δ.length).filter proof.usesHyp

theorem mem_usedHyps {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntaxModulo eqs Δ φ) (i : Fin Δ.length) :
    i ∈ proof.usedHyps ↔ proof.usesHyp i = true := by
  simp [usedHyps]

end ProofSyntaxModulo

end Mettapedia.Logic.HOL
