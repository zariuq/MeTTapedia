import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerDecision
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbMeet

/-!
# Miller patterns with incomparable codomains: lowering both unknowns to a greatest lower bound

The fragment of Miller patterns asks the declared codomains to form a chain: on `λ ȳ. F y_ā ≐ λ ȳ. G y_b̄`, with
both sides covering each other, the solver solves the unknown with the larger codomain by the other, and is stuck
when the codomains are incomparable. The chain is not needed for principal answers: every solution sends `F` to a
family valued in `U_g`, for a greatest lower bound `g` of the codomains (`millerGlb_forced`), and likewise `G`; so
lowering both, in place, is exact (`millerGlbUpdate`, `millerGlb_exact`), after which the codomains are equal.

* **Forcing** (`millerGlb_forced`): open `F`'s value at its own domains, rename it into the annotation's locals; the
  opened equation makes it equal to a type of `U_{cG}`, so it is equal to a type `N` of `U_g` (`small_of_glb` with
  the trivial narrowing: the domains are exact, so no local widens); pulling `N` back along the injective renaming
  gives `F`'s value as `λ x̄. N'` with `N'` in `U_g`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Miller

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L]

section Forcing

variable {S : Setting Head L} (inh : Inhabitants S.R)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

include inh facts roots heads algebra rigid complete headTypingUnique in
/-- **What a Miller flex-flex equation forces at a greatest lower bound**: every solution sends `F` to a family
valued in `U_g`. -/
theorem millerGlb_forced {Θ Δ : Context S.R} (f : Δ ⟶ Θ) (qs : List Head) {d : Head} {F G : Fin Θ.arity}
    {psF psG : List Head} {cF cG g : Head} (imgF : Fin psF.length → Fin qs.length)
    (imgG : Fin psG.length → Fin qs.length) (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d)
    (domainsF : ∀ j, psF.get j = qs.get (imgF j)) (injectiveF : Function.Injective imgF)
    (domainsG : ∀ j, psG.get j = qs.get (imgG j))
    (declF : Ctx.lookup Θ.raw F = famCode psF cF) (declG : Ctx.lookup Θ.raw G = famCode psG cG)
    (universesF : AllUniverses S.R psF) (hcF : S.R.isUniverse cF) (hcG : S.R.isUniverse cG)
    (glb : IsGlb S.R g cF cG)
    (equal : Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs psF imgF) (opened psF (f.substitution F)))
      (Presentation.rename (sideRen qs psG imgG) (opened psG (f.substitution G))) (.head d)) :
    ∃ h, Typed S.R Δ.raw h (famCode psF g) ∧ Equal S.R Δ.raw (f.substitution F) h (famCode psF cF) := by
  have formedQ : CtxFormed S.R (ctx Δ.raw qs) := ctx_formed qs Δ.formed universes
  have tF : Typed S.R Δ.raw (f.substitution F) (famCode psF cF) := by
    have typed := f.typed F
    rw [declF, famCode_subst] at typed
    exact typed
  have tG : Typed S.R Δ.raw (f.substitution G) (famCode psG cG) := by
    have typed := f.typed G
    rw [declG, famCode_subst] at typed
    exact typed
  have rF : Typed S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs psF imgF) (opened psF (f.substitution F)))
      (.head cF) :=
    (opened_typed psF tF).rename (sideRen_ctxRen Δ.raw qs psF imgF domainsF)
  have rG : Typed S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs psG imgG) (opened psG (f.substitution G)))
      (.head cG) :=
    (opened_typed psG tG).rename (sideRen_ctxRen Δ.raw qs psG imgG domainsG)
  obtain ⟨N, tN, eN⟩ := small_of_glb facts roots heads algebra rigid complete headTypingUnique hcF hcG hcF glb
    (NarrowsBelow.refl g (ctx Δ.raw qs)) formedQ formedQ rF rF rG ⟨cF, hcF, .refl rF⟩ ⟨d, hd, equal.symm⟩
  have pulled := eN.substitute (pullSub_substMor inh Δ.raw qs psF imgF universes domainsF)
  rw [pull_cancel inh qs psF imgF injectiveF] at pulled
  have tPulled : Typed S.R (ctx Δ.raw psF) (Presentation.subst (pullSub inh qs psF imgF) N) (.head g) :=
    tN.substitute (pullSub_substMor inh Δ.raw qs psF imgF universes domainsF)
  refine ⟨lams psF (Presentation.subst (pullSub inh qs psF imgF) N),
    lams_typed psF Δ.formed universesF glb.1 tPulled, ?_⟩
  have body : Equal S.R (ctx Δ.raw psF) (opened psF (f.substitution F))
      (Presentation.subst (pullSub inh qs psF imgF) N) (.head cF) := pulled
  have lifted := (lams_equal_iff psF Δ.formed universesF hcF (opened_typed psF tF)
    (Derivable.cumul tPulled glb.2.1)).mpr body
  exact (eta_opened psF Δ.formed tF).symm.trans lifted

end Forcing

/-! ## The rule: both unknowns lowered to the greatest lower bound -/

section Rule

variable {S : Setting Head L} (inh : Inhabitants S.R)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

variable {Θ : Context S.R} {e : Equation (TotalTerm Θ)}

/-- `F` lowered to `g`. -/
def millerLowerF (families : Families Θ) (v : EqView (S := S) e) (D₁ : FlexData Θ.raw v.qs e.1.2.code)
    (cG : Head) {g : Head} (glb : IsGlb S.R g D₁.c cG) : CodomainLowering Θ where
  index := D₁.unknown
  ps := D₁.ps
  lower := g
  upper := D₁.c
  declared := D₁.declared
  universes := (famFacts families D₁.declared).1
  universe_lower := glb.1
  universe_upper := (famFacts families D₁.declared).2
  below := glb.2.1

/-- Then `G` lowered to `g`, over the first lowering. -/
def millerLowerG (families : Families Θ) (v : EqView (S := S) e) (D₁ : FlexData Θ.raw v.qs e.1.2.code)
    (D₂ : FlexData Θ.raw v.qs e.2.2.code) {g : Head} (glb : IsGlb S.R g D₁.c D₂.c)
    (ne : D₂.unknown ≠ D₁.unknown) : CodomainLowering (millerLowerF families v D₁ D₂.c glb).target where
  index := D₂.unknown
  ps := D₂.ps
  lower := g
  upper := D₂.c
  declared := ((millerLowerF families v D₁ D₂.c glb).lookup_ne ne).trans D₂.declared
  universes := (famFacts families D₂.declared).1
  universe_lower := glb.1
  universe_upper := (famFacts families D₂.declared).2
  below := glb.2.2.1

include inh facts roots heads algebra rigid complete headTypingUnique in
theorem millerLowerF_forced (families : Families Θ) (v : EqView (S := S) e) (D₁ : FlexData Θ.raw v.qs e.1.2.code)
    (b₁ : S.R.cumulative D₁.c v.d) (D₂ : FlexData Θ.raw v.qs e.2.2.code) (b₂ : S.R.cumulative D₂.c v.d)
    (hl : v.left = .flex D₁ b₁) (hr : v.right = .flex D₂ b₂) {g : Head} (glb : IsGlb S.R g D₁.c D₂.c)
    (rest : EquationStore (TotalTerm Θ)) : (millerLowerF families v D₁ D₂.c glb).Forced (e :: rest) := by
  intro Δ f solved
  exact millerGlb_forced inh facts roots heads algebra rigid complete headTypingUnique f v.qs D₁.img D₂.img
    v.universes v.universe_d D₁.domains D₁.injective D₂.domains D₁.declared D₂.declared
    (famFacts families D₁.declared).1 (famFacts families D₁.declared).2 (famFacts families D₂.declared).2 glb
    (opens_flexFlex v D₁ b₁ D₂ b₂ hl hr f solved)

include inh facts roots heads algebra rigid complete headTypingUnique in
theorem millerLowerG_forced (families : Families Θ) (v : EqView (S := S) e) (D₁ : FlexData Θ.raw v.qs e.1.2.code)
    (b₁ : S.R.cumulative D₁.c v.d) (D₂ : FlexData Θ.raw v.qs e.2.2.code) (b₂ : S.R.cumulative D₂.c v.d)
    (hl : v.left = .flex D₁ b₁) (hr : v.right = .flex D₂ b₂) {g : Head} (glb : IsGlb S.R g D₁.c D₂.c)
    (ne : D₂.unknown ≠ D₁.unknown) (rest : EquationStore (TotalTerm Θ)) :
    (millerLowerG families v D₁ D₂ glb ne).Forced
      ((frames S.levels).applyStore (millerLowerF families v D₁ D₂.c glb).hom (e :: rest)) := by
  intro Δ f solved
  have back := (Frames.models_applyStore (X := frames S.levels) _ f (e :: rest)).mp solved
  have equal := opens_flexFlex v D₁ b₁ D₂ b₂ hl hr (f ≫ (millerLowerF families v D₁ D₂.c glb).hom) back
  exact millerGlb_forced inh facts roots heads algebra rigid complete headTypingUnique
    (f ≫ (millerLowerF families v D₁ D₂.c glb).hom) v.qs D₂.img D₁.img v.universes v.universe_d D₂.domains
    D₂.injective D₁.domains D₂.declared D₁.declared (famFacts families D₂.declared).1
    (famFacts families D₂.declared).2 (famFacts families D₁.declared).2 glb.symm equal.symm

/-- **Both unknowns lowered to the greatest lower bound.** -/
def millerGlbUpdate (families : Families Θ) (v : EqView (S := S) e) (D₁ : FlexData Θ.raw v.qs e.1.2.code)
    (b₁ : S.R.cumulative D₁.c v.d) (D₂ : FlexData Θ.raw v.qs e.2.2.code) (b₂ : S.R.cumulative D₂.c v.d)
    (hl : v.left = .flex D₁ b₁) (hr : v.right = .flex D₂ b₂) {g : Head} (glb : IsGlb S.R g D₁.c D₂.c)
    (ne : D₂.unknown ≠ D₁.unknown) (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) :=
  (lowerAtUpdate (millerLowerF families v D₁ D₂.c glb) (e :: rest)
      (millerLowerF_forced inh facts roots heads algebra rigid complete headTypingUnique families v D₁ b₁ D₂ b₂ hl hr
        glb rest)).then
    (lowerAtUpdate (millerLowerG families v D₁ D₂ glb ne) _
      (millerLowerG_forced inh facts roots heads algebra rigid complete headTypingUnique families v D₁ b₁ D₂ b₂ hl hr
        glb ne rest))

include inh facts roots heads algebra rigid complete headTypingUnique in
/-- **Lowering both unknowns to the greatest lower bound is exact.** -/
theorem millerGlb_exact (families : Families Θ) (v : EqView (S := S) e) (D₁ : FlexData Θ.raw v.qs e.1.2.code)
    (b₁ : S.R.cumulative D₁.c v.d) (D₂ : FlexData Θ.raw v.qs e.2.2.code) (b₂ : S.R.cumulative D₂.c v.d)
    (hl : v.left = .flex D₁ b₁) (hr : v.right = .flex D₂ b₂) {g : Head} (glb : IsGlb S.R g D₁.c D₂.c)
    (ne : D₂.unknown ≠ D₁.unknown) (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest)
      (millerGlbUpdate inh facts roots heads algebra rigid complete headTypingUnique families v D₁ b₁ D₂ b₂ hl hr glb ne
        rest).answer
      (millerGlbUpdate inh facts roots heads algebra rigid complete headTypingUnique families v D₁ b₁ D₂ b₂ hl hr glb ne
        rest).remaining :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr ⟨_, rfl, rfl, rfl⟩

end Rule

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
