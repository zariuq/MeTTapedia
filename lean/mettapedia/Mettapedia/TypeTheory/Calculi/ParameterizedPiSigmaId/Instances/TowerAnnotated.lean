import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Coherence

/-!
# The annotated calculus in the cumulative tower: controls

Controls for annotated terms, their erasure and coherence of annotations, in
the cumulative tower of universes without declarations (`P₀`).

**Syntax and erasure.**

* Positive: erasure is surjective and commutes with opening a binder; an
  annotated derivation erases to a derivation of the rule package
  (`idU_erase`); an annotated head step erases to a weak-head step.
* Negative: erasure is not injective (`idU_ne`, the identity at `U₀` and at
  `U₁`); a step inside a domain is no step after erasure (`domainStep`).

**Coherence**, positive: for each case, two annotated terms with one erasure,
typed at one type, are shown equal by a direct derivation.

* β for functions, with elaborations that differ in levels:
  `(λ (f : U → U). x) (λ (y : U). y)` at `U = U₀` and at `U = U₁`
  (`beta_coherent`);
* β for pairs: `(x, λ (y : U). y).1` at the two levels (`fst_coherent`);
* cumulativity: the identity on `U₀` used at `U₀ → U₁` (`cumul_coherent`);
* universe levels equal under every valuation, `U₀` and `U_{max 0 0}`
  (`headEq_coherent`);
* η for functions: domains `F (λ (y : U₀). g y)` and `F g`, whose erasures
  differ, equal by η (`etaPi_coherent`);
* η for pairs: domains `F (p.1, p.2)` and `F p` (`etaSigma_coherent`).

**Coherence**, negative, from injectivity of the type formers: the identity at
`U₀` and at `U₁` have one erasure and no common type, so they are not equal at
any type (`idU_not_equal`). The typing premise of coherence cannot be dropped,
and the arguments of the two β-redexes above cannot be compared by congruence:
only contracting the redex makes the two elaborations equal.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated
namespace TowerControls

open Normalization (LevelModel HeadSame WhStep)
open UniverseLevel (LevelExpr)

/-- The tower of universes over a level order, without declarations, annotated. -/
def P₀ {L : Type} [UniverseLevel.LevelOrder L] : ChurchRules (LevelTower.rules L) :=
  ChurchRules.empty (LevelTower.rules L) (fun _ => rfl)

/-- The universe at a level. -/
abbrev U {n : Nat} (l : LevelExpr Nat) : CTm Tower.Head n := .head (.sort l)

/-- Level zero and level one. -/
abbrev l0 : LevelExpr Nat := .const 0
abbrev l1 : LevelExpr Nat := .succ (.const 0)

/-- The identity on the universe at a level. -/
abbrev idU {n : Nat} (l : LevelExpr Nat) : CTm Tower.Head n := .lam (U l) (.var 0)

section Typings

variable {n : Nat} {Γ : CCtx Tower.Head n}

theorem univ_typed (l : LevelExpr Nat) : CTyped P₀ Γ (U l) (U (.succ l)) := .headType (.sort l)

theorem piUU_typed (l : LevelExpr Nat) :
    CTyped P₀ Γ (.pi (U l) (U l)) (U (.max (.succ l) (.succ l))) :=
  .piForm (univ_typed l) (.sort _) (univ_typed l) (.sort _) (.sorts _ _)

theorem idU_typed (l : LevelExpr Nat) : CTyped P₀ Γ (idU l) (.pi (U l) (U l)) :=
  .lamIntro (univ_typed l) (.sort _) (piUU_typed l) (.sort _) (.var 0)

end Typings

/-! ## Syntax and erasure -/

/-- Negative: two annotated terms with one erasure. -/
theorem idU_ne {n : Nat} : (idU l0 : CTm Tower.Head n) ≠ idU l1 ∧
    (idU l0 : CTm Tower.Head n).erase = (idU l1).erase :=
  CTm.erase_not_injective (fun same => by cases same)

/-- Positive: every term is an erasure. -/
example : (CTm.annotateWith (U l0) (.lam (.var 0) : Tm Tower.Head 0)).erase = .lam (.var 0) :=
  CTm.erase_annotateWith _ _

/-- Positive: erasure commutes with opening a binder, on an instance. -/
example : (CTm.inst0 (idU l0) (.app (.var 0) (.var 0)) : CTm Tower.Head 0).erase =
    Presentation.inst0 (Tm.lam (.var 0)) (.app (.var 0) (.var 0)) := rfl

/-- Positive: the annotated identity's typing erases to the unannotated one. -/
theorem idU_erase :
    Typed Tower.rules .nil (.lam (.var 0)) (.pi (.head (.sort l0)) (.head (.sort l0))) :=
  CDerivable.erase (idU_typed (Γ := .nil) l0)

/-- Positive: an annotated β-step erases to a weak-head step. -/
example (roles : Normalization.Roles Tower.Head) :
    WhStep Tower.rules roles (CTm.app (idU l0) (U l0) : CTm Tower.Head 0).erase
      (U l0 : CTm _ 0).erase :=
  (CWhStep.beta (U l0) (.var 0) (U l0)).erase_whStep

/-- Negative: a step inside a domain is invisible after erasure. -/
theorem domainStep :
    CStepCore P₀.computation Tower.rules.headEq
      (.lam (.app (idU l1) (U l0)) (.var 0) : CTm Tower.Head 0) (idU l0) ∧
    (CTm.lam (.app (idU l1) (U l0)) (.var 0) : CTm Tower.Head 0).erase = (idU l0).erase :=
  ⟨.congLamDom (.betaPi _ _ _), rfl⟩

/-! ## Coherence, positive -/

/-- The context `X : U₀, x : X`. -/
abbrev Γ₂ : CCtx Tower.Head 2 := .snoc (.snoc .nil (U l0)) (.var 0)

/-- `(λ (f : U → U). x) (λ (y : U). y)` with `U` the universe at `l`. -/
abbrev betaAt (l : LevelExpr Nat) : CTm Tower.Head 2 :=
  .app (.lam (.pi (U l) (U l)) (.var 1)) (idU l)

theorem betaAt_equal (l : LevelExpr Nat) : CEqual P₀ Γ₂ (betaAt l) (.var 0) (.var 1) :=
  .betaPi (B := .var 2) (u := .sort (.max (.max (.succ l) (.succ l)) l0))
    (.piForm (piUU_typed l) (.sort _) (.var 2) (.sort _) (.sorts _ _)) (.sort _) (.var 1)
    (idU_typed l)

/-- **β for functions, at two levels.** -/
theorem beta_coherent :
    (betaAt l0).erase = (betaAt l1).erase ∧ CEqual P₀ Γ₂ (betaAt l0) (betaAt l1) (.var 1) :=
  ⟨rfl, .trans (betaAt_equal l0) (.symm (betaAt_equal l1))⟩

/-- `(x, λ (y : U). y).1` with `U` the universe at `l`. -/
abbrev fstAt (l : LevelExpr Nat) : CTm Tower.Head 2 := .fst (.pair (.var 0) (idU l))

theorem fstAt_equal (l : LevelExpr Nat) : CEqual P₀ Γ₂ (fstAt l) (.var 0) (.var 1) :=
  .betaFst (B := .pi (U l) (U l)) (u := .sort (.max l0 (.max (.succ l) (.succ l))))
    (.sigmaForm (.var 1) (.sort _) (piUU_typed l) (.sort _) (.sorts _ _)) (.sort _) (.var 0)
    (idU_typed l)

/-- **β for pairs, at two levels.** -/
theorem fst_coherent :
    (fstAt l0).erase = (fstAt l1).erase ∧ CEqual P₀ Γ₂ (fstAt l0) (fstAt l1) (.var 1) :=
  ⟨rfl, .trans (fstAt_equal l0) (.symm (fstAt_equal l1))⟩

/-- `U₀` is below `U₁`. -/
theorem cumul01 : Tower.rules.cumulative (.sort l0) (.sort l1) := fun _ => Nat.zero_le _

/-- `(λ (f : U₀ → U₁). x) (λ (y : U₀). y)`: the identity on `U₀` used at
`U₀ → U₁`. -/
abbrev betaCumul : CTm Tower.Head 2 := .app (.lam (.pi (U l0) (U l1)) (.var 1)) (idU l0)

theorem betaCumul_equal : CEqual P₀ Γ₂ betaCumul (.var 0) (.var 1) := by
  have tPi01 : CTyped P₀ Γ₂ (.pi (U l0) (U l1)) (U (.max (.succ l0) (.succ l1))) :=
    .piForm (univ_typed l0) (.sort _) (univ_typed l1) (.sort _) (.sorts _ _)
  have tArg : CTyped P₀ Γ₂ (idU l0) (.pi (U l0) (U l1)) :=
    .sub (idU_typed l0) (.subPi (piUU_typed l0) (.sort _) tPi01 (.sort _)
      (.refl (univ_typed l0)) (.sort _) (.subUniv cumul01))
  exact .betaPi (B := .var 2) (u := .sort (.max (.max (.succ l0) (.succ l1)) l0))
    (.piForm tPi01 (.sort _) (.var 2) (.sort _) (.sorts _ _)) (.sort _) (.var 1) tArg

/-- **Cumulativity**: the identity on `U₀` at `U₀ → U₁`, against the identity
on `U₁` at `U₁ → U₁`. -/
theorem cumul_coherent :
    betaCumul.erase = (betaAt l1).erase ∧ CEqual P₀ Γ₂ betaCumul (betaAt l1) (.var 1) :=
  ⟨rfl, .trans betaCumul_equal (.symm (betaAt_equal l1))⟩

/-- `max 0 0` and `0` agree under every valuation. -/
theorem headEq00 : Tower.rules.headEq (.sort l0) (.sort (.max l0 l0)) := fun _ => by
  show 0 = max 0 0
  rfl

/-- **Levels equal under every valuation**: the identity on `U₀` and on
`U_{max 0 0}`. -/
theorem headEq_coherent {n : Nat} {Γ : CCtx Tower.Head n} :
    (idU l0 : CTm Tower.Head n).erase = (idU (.max l0 l0)).erase ∧
    CEqual P₀ Γ (idU l0) (idU (.max l0 l0)) (.pi (U l0) (U l0)) := by
  refine ⟨rfl, ?_⟩
  have raise : Tower.rules.cumulative (.sort (.succ (.max l0 l0))) (.sort (.succ l0)) :=
    fun _ => le_refl _
  have eU : CEqual P₀ Γ (U l0) (U (.max l0 l0)) (U (.succ l0)) :=
    .headEq headEq00 (univ_typed l0) (.sub (univ_typed (.max l0 l0)) (.subUniv raise))
  exact .lamCong eU (.sort _) (piUU_typed l0) (.sort _) (.refl (.var 0))

/-- The context `g : U₀ → U₀, F : (U₀ → U₀) → U₀`. -/
abbrev Γη : CCtx Tower.Head 2 :=
  .snoc (.snoc .nil (.pi (U l0) (U l0))) (.pi (.pi (U l0) (U l0)) (U l0))

/-- `λ (y : U₀). g y`. -/
abbrev etaG : CTm Tower.Head 2 := .lam (U l0) (.app (.var 2) (.var 0))

theorem etaG_equal : CEqual P₀ Γη etaG (.var 1) (.pi (U l0) (U l0)) := by
  have tG : CTyped P₀ Γη etaG (.pi (U l0) (U l0)) :=
    .lamIntro (univ_typed l0) (.sort _) (piUU_typed l0) (.sort _)
      (.appElim (B := U l0) (.var 2) (.var 0))
  have body : CEqual P₀ (.snoc Γη (U l0)) (.app (etaG.rename wk) (.var 0))
      (.app ((CTm.var 1 : CTm Tower.Head 2).rename wk) (.var 0)) (U l0) :=
    .betaPi (B := U l0) (piUU_typed l0) (.sort _) (.appElim (B := U l0) (.var 3) (.var 0)) (.var 0)
  exact .etaPi tG (.var 1) body

/-- The domains `F (λ (y : U₀). g y)` and `F g`. -/
abbrev domEta : CTm Tower.Head 2 := .app (.var 0) etaG
abbrev domG : CTm Tower.Head 2 := .app (.var 0) (.var 1)

/-- **η for functions**: `λ (x : F (λ y. g y)). x` and `λ (x : F g). x`. The
domains' erasures differ; they are equal by η. -/
theorem etaPi_coherent :
    domEta.erase ≠ domG.erase ∧
    (CTm.lam domEta (.var 0)).erase = (CTm.lam domG (.var 0)).erase ∧
    CEqual P₀ Γη (.lam domEta (.var 0)) (.lam domG (.var 0)) (.pi domEta (domEta.rename wk)) := by
  refine ⟨by simp [CTm.erase], rfl, ?_⟩
  have tF : CTyped P₀ Γη (.var 0) (.pi (.pi (U l0) (U l0)) (U l0)) := .var 0
  have tD : CTyped P₀ Γη domEta (U l0) :=
    .appElim tF (.lamIntro (univ_typed l0) (.sort _) (piUU_typed l0) (.sort _)
      (.appElim (B := U l0) (.var 2) (.var 0)))
  have eD : CEqual P₀ Γη domEta domG (U l0) := .appCong (.refl tF) etaG_equal
  have tDD : CTyped P₀ (.snoc Γη domEta) (domEta.rename wk) (U l0) := CTyped.weaken tD
  exact .lamCong eD (.sort _) (.piForm tD (.sort _) tDD (.sort _) (.sorts _ _)) (.sort _)
    (.refl (.var 0))

/-- The context `p : Σ U₀ U₀, F : Σ U₀ U₀ → U₀`. -/
abbrev Γσ : CCtx Tower.Head 2 :=
  .snoc (.snoc .nil (.sigma (U l0) (U l0))) (.pi (.sigma (U l0) (U l0)) (U l0))

/-- `(p.1, p.2)`. -/
abbrev etaP : CTm Tower.Head 2 := .pair (.fst (.var 1)) (.snd (.var 1))

theorem sigmaUU_typed : CTyped P₀ Γσ (.sigma (U l0) (U l0)) (U (.max (.succ l0) (.succ l0))) :=
  .sigmaForm (univ_typed l0) (.sort _) (univ_typed l0) (.sort _) (.sorts _ _)

theorem etaP_typed : CTyped P₀ Γσ etaP (.sigma (U l0) (U l0)) :=
  .pairIntro sigmaUU_typed (.sort _) (.fstElim (.var 1)) (.sndElim (.var 1))

theorem etaP_equal : CEqual P₀ Γσ etaP (.var 1) (.sigma (U l0) (U l0)) :=
  .etaSigma etaP_typed (.var 1)
    (.betaFst sigmaUU_typed (.sort _) (.fstElim (.var 1)) (.sndElim (.var 1)))
    (.betaSnd sigmaUU_typed (.sort _) (.fstElim (.var 1)) (.sndElim (.var 1)))

/-- The domains `F (p.1, p.2)` and `F p`. -/
abbrev domPair : CTm Tower.Head 2 := .app (.var 0) etaP
abbrev domP : CTm Tower.Head 2 := .app (.var 0) (.var 1)

/-- **η for pairs**: `λ (x : F (p.1, p.2)). x` and `λ (x : F p). x`. The
domains' erasures differ; they are equal by η. -/
theorem etaSigma_coherent :
    domPair.erase ≠ domP.erase ∧
    (CTm.lam domPair (.var 0)).erase = (CTm.lam domP (.var 0)).erase ∧
    CEqual P₀ Γσ (.lam domPair (.var 0)) (.lam domP (.var 0))
      (.pi domPair (domPair.rename wk)) := by
  refine ⟨by simp [CTm.erase], rfl, ?_⟩
  have tF : CTyped P₀ Γσ (.var 0) (.pi (.sigma (U l0) (U l0)) (U l0)) := .var 0
  have tD : CTyped P₀ Γσ domPair (U l0) := .appElim tF etaP_typed
  have eD : CEqual P₀ Γσ domPair domP (U l0) := .appCong (.refl tF) etaP_equal
  have tDD : CTyped P₀ (.snoc Γσ domPair) (domPair.rename wk) (U l0) := CTyped.weaken tD
  exact .lamCong eD (.sort _) (.piForm tD (.sort _) tDD (.sort _) (.sorts _ _)) (.sort _)
    (.refl (.var 0))

/-! ## Coherence, negative -/

/-- **The identities on `U₀` and on `U₁` have no common type**, given
injectivity and no-confusion of the type formers. -/
theorem idU_no_common_type (facts : CFormerFacts (P₀ (L := Nat))) {n : Nat} {Γ : CCtx Tower.Head n}
    (formed : CCtxFormed P₀ Γ) {T : CTm Tower.Head n} (t₀ : CTyped P₀ Γ (idU l0) T)
    (t₁ : CTyped P₀ Γ (idU l1) T) : False := by
  have levels := Normalization.TowerModel.levels (fun _ => 0)
  have typeT := CTyped.isType levels t₀ formed
  obtain ⟨_, u, _, _, _, tPi, hu, _, le⟩ := t₀.generation
  obtain ⟨B, C, eT, eDB, _⟩ := CBelow.pi_source facts levels (CTypeLe.toBelow le typeT) formed
    (CIsType.refl ⟨u, hu, tPi⟩)
  obtain ⟨_, u', _, _, _, tPi', hu', _, le'⟩ := t₁.generation
  obtain ⟨B', C', eT', eDB', _⟩ := CBelow.pi_source facts levels (CTypeLe.toBelow le' typeT)
    formed (CIsType.refl ⟨u', hu', tPi'⟩)
  obtain ⟨eBB', _⟩ := CTypeEq.pi_injective facts (CTypeEq.trans levels eT.symm eT') formed
  have e01 : CTypeEq P₀ Γ (U l0) (U l1) :=
    CTypeEq.trans levels eDB (CTypeEq.trans levels eBB' eDB'.symm)
  rcases CTypeEq.head_injective facts e01 formed with same | same
  · cases same
  · exact absurd (same fun _ => 0) (by decide)

/-- The identities on `U₀` and on `U₁` are equal at no type. -/
theorem idU_not_equal (facts : CFormerFacts (P₀ (L := Nat))) {n : Nat} {Γ : CCtx Tower.Head n}
    (formed : CCtxFormed P₀ Γ) (T : CTm Tower.Head n) :
    ¬ CEqual P₀ Γ (idU l0) (idU l1) T := fun equal => by
  obtain ⟨t₀, t₁⟩ := CEqual.typed (Normalization.TowerModel.levels (fun _ => 0)) equal formed
  exact idU_no_common_type facts formed t₀ t₁

end TowerControls
end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
