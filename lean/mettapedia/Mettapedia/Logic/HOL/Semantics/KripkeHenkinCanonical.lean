import Mettapedia.Logic.HOL.Semantics.KripkeHenkinCanonical.Support

/-!
# Canonical Kripke-Henkin packaging

Final content layer for the supported canonical construction: local membership
clauses, conditional full-presented upgrades, canonical `KripkeHenkin`
instances, and the supported consequence/completeness packaging surfaces.
The membership, frame, recursive forcing, and support towers are imported from
content modules under `KripkeHenkinCanonical/`; namespaces and declaration names
are preserved.
-/

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

open Mettapedia.Logic.HOL.WithParams

namespace KripkeHenkin

namespace SupportedCanonicalFrame

open ClosedTheorySet

/-- The remaining local membership clauses needed to package supported
presented worlds as a full substitutional `KripkeHenkin` structure.  The
nonlocal implication, negation, and universal clauses are supplied by a
`SchedulerProvider`; these local clauses are exactly the still-open
unsupported disjunction/existential gap. -/
structure LocalMembershipClauses (Const : Ty Base → Type v) where
  or_clause :
    ∀ {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
      {φ ψ : ClosedFormula (WithParams Const)},
      Forces (Base := Base) (Const := Const) W (.or φ ψ) ↔
        Forces (Base := Base) (Const := Const) W φ ∨
          Forces (Base := Base) (Const := Const) W ψ
  ex_clause :
    ∀ {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
      {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
      Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) ↔
        ∃ t : ClosedTerm (WithParams Const) σ,
          ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            Le (Base := Base) (Const := Const) W V →
              Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ)

/-- The local membership clauses are exactly a global-strength upgrade for each
supported presented world: they supply unrestricted disjunction primeness and
unrestricted existential witnesses for its deductive-closure carrier. -/
def LocalMembershipClauses.toFullPresented
    (L : LocalMembershipClauses (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const) :
    ClosedTheorySet.FullPresentedIntuitionisticWorld (Base := Base) Const :=
  { level := W.level
    raw := W.raw
    raw_avoids_future := W.raw_avoids_future
    consistent := W.consistent
    prime_or := by
      intro φ ψ hOr
      have hForces :
          Forces (Base := Base) (Const := Const) W (.or φ ψ) := by
        simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier] using hOr
      rcases (L.or_clause (W := W) (φ := φ) (ψ := ψ)).mp hForces with hφ | hψ
      · left
        simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier] using hφ
      · right
        simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier] using hψ
    exists_witness := by
      intro σ φ hEx
      have hForces :
          Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) := by
        simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier] using hEx
      obtain ⟨t, ht⟩ := (L.ex_clause (W := W) (σ := σ) (φ := φ)).mp hForces
      refine ⟨t, ?_⟩
      simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier] using
        ht W (le_refl (Base := Base) (Const := Const) W) }

/-- Upgrading a supported world through the local clauses and then forgetting
back to the supported interface preserves the underlying world. -/
@[simp] theorem LocalMembershipClauses.toFullPresented_toSupported
    (L : LocalMembershipClauses (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const) :
    (L.toFullPresented (Base := Base) W).toSupported = W := by
  cases W
  simp [LocalMembershipClauses.toFullPresented,
    ClosedTheorySet.FullPresentedIntuitionisticWorld.toSupported]

/-- An equivalent way to state the local canonical gap: every supported
presented world can be upgraded to a full presented world without changing its
raw presentation or support level.

**Do not attempt to discharge this for arbitrary supported worlds.**  Global
disjunction primeness of a fixed level-bounded closure over pairs mentioning
future-layer parameters is disjunction-property strength (normalization-route
work), and `FormulaPairFairAfter.incompatible_with_avoids_layers` refutes the
one-enumeration fairness route.  The viable completeness surface is the
support-bounded one (`provable_iff_supportedMembershipConsequence_*`); this
structure remains only as hypothesis packaging for the conditional
`KripkeHenkin`-class instances. -/
structure FullPresentedUpgrade (Const : Ty Base → Type v) where
  full :
    ∀ _ : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
      ClosedTheorySet.FullPresentedIntuitionisticWorld (Base := Base) Const
  forget :
    ∀ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
      (full W).toSupported = W

/-- Local membership clauses determine a full-presented upgrade for every
supported world. -/
def LocalMembershipClauses.toFullPresentedUpgrade
    (L : LocalMembershipClauses (Base := Base) Const) :
    FullPresentedUpgrade (Base := Base) Const where
  full := L.toFullPresented (Base := Base)
  forget := L.toFullPresented_toSupported (Base := Base)

theorem fullPresented_or_clause
    (W : ClosedTheorySet.FullPresentedIntuitionisticWorld Const)
    {φ ψ : ClosedFormula (WithParams Const)} :
    Forces (Base := Base) (Const := Const) W.toSupported (.or φ ψ) ↔
      Forces (Base := Base) (Const := Const) W.toSupported φ ∨
        Forces (Base := Base) (Const := Const) W.toSupported ψ := by
  constructor
  · intro hOr
    have hOr' : (.or φ ψ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure (Const := WithParams Const) W.raw := by
      simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier,
        ClosedTheorySet.FullPresentedIntuitionisticWorld.toSupported] using hOr
    rcases W.prime_or hOr' with hφ | hψ
    · left
      simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier,
        ClosedTheorySet.FullPresentedIntuitionisticWorld.toSupported] using hφ
    · right
      simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier,
        ClosedTheorySet.FullPresentedIntuitionisticWorld.toSupported] using hψ
  · intro hOr
    rcases hOr with hφ | hψ
    · exact SupportedCanonicalMembership.or_left_mem (W := W.toSupported) hφ
    · exact SupportedCanonicalMembership.or_right_mem (W := W.toSupported) hψ

theorem fullPresented_ex_clause
    (W : ClosedTheorySet.FullPresentedIntuitionisticWorld Const)
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]} :
    Forces (Base := Base) (Const := Const) W.toSupported (.ex φ : ClosedFormula (WithParams Const)) ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        Forces (Base := Base) (Const := Const) W.toSupported (instantiate (Base := Base) t φ) := by
  constructor
  · intro hEx
    have hEx' : (.ex φ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure (Const := WithParams Const) W.raw := by
      simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier,
        ClosedTheorySet.FullPresentedIntuitionisticWorld.toSupported] using hEx
    obtain ⟨t, ht⟩ := W.exists_witness hEx'
    refine ⟨t, ?_⟩
    simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier,
      ClosedTheorySet.FullPresentedIntuitionisticWorld.toSupported] using ht
  · intro hEx
    rcases hEx with ⟨t, ht⟩
    exact SupportedCanonicalMembership.ex_intro_mem (W := W.toSupported) t ht

theorem fullPresented_ex_kripke_clause
    (W : ClosedTheorySet.FullPresentedIntuitionisticWorld Const)
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]} :
    Forces (Base := Base) (Const := Const) W.toSupported (.ex φ : ClosedFormula (WithParams Const)) ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) W.toSupported V →
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  constructor
  · intro hEx
    obtain ⟨t, ht⟩ :=
      (fullPresented_ex_clause (Base := Base) (Const := Const) W).mp hEx
    refine ⟨t, ?_⟩
    intro V hWV
    exact forces_mono (Base := Base) (Const := Const) hWV ht
  · intro hEx
    rcases hEx with ⟨t, ht⟩
    exact (fullPresented_ex_clause (Base := Base) (Const := Const) W).mpr
      ⟨t, ht W.toSupported (le_refl (Base := Base) (Const := Const) W.toSupported)⟩

/-- A full-presented upgrade supplies exactly the local membership clauses
needed by the conditional canonical membership model. -/
def FullPresentedUpgrade.toLocalMembershipClauses
    (U : FullPresentedUpgrade (Base := Base) Const) :
    LocalMembershipClauses (Base := Base) Const where
  or_clause := by
    intro W φ ψ
    have hClause := fullPresented_or_clause (Base := Base) (Const := Const)
      (U.full W) (φ := φ) (ψ := ψ)
    simpa [U.forget W] using hClause
  ex_clause := by
    intro W σ φ
    have hClause := fullPresented_ex_kripke_clause (Base := Base) (Const := Const)
      (U.full W) (σ := σ) (φ := φ)
    simpa [U.forget W] using hClause

/-- Level-aware local membership clauses for the canonical membership model
whose preorder is `LevelLe`.  This is the honest package for truth-lemma work
that needs level growth along accessibility. -/
structure LevelLocalMembershipClauses (Const : Ty Base → Type v) where
  or_clause :
    ∀ {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
      {φ ψ : ClosedFormula (WithParams Const)},
      Forces (Base := Base) (Const := Const) W (.or φ ψ) ↔
        Forces (Base := Base) (Const := Const) W φ ∨
          Forces (Base := Base) (Const := Const) W ψ
  ex_clause :
    ∀ {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
      {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
      Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) ↔
        ∃ t : ClosedTerm (WithParams Const) σ,
          ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) W V →
              Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ)

/-- Ordinary local membership clauses also supply the level-aware version by
forgetting the level component of accessibility. -/
def LocalMembershipClauses.toLevelLocalMembershipClauses
    (L : LocalMembershipClauses (Base := Base) Const) :
    LevelLocalMembershipClauses (Base := Base) Const where
  or_clause := L.or_clause
  ex_clause := by
    intro W σ φ
    constructor
    · intro hEx
      obtain ⟨t, ht⟩ := (L.ex_clause (W := W) (σ := σ) (φ := φ)).mp hEx
      exact ⟨t, fun V hWV => ht V hWV.2⟩
    · intro hEx
      obtain ⟨t, ht⟩ := hEx
      exact SupportedCanonicalMembership.ex_intro_mem (Base := Base) (Const := Const)
        (W := W) t (ht W (levelLe_refl (Base := Base) (Const := Const) W))

/-- A full-presented upgrade supplies level-aware local membership clauses. -/
def FullPresentedUpgrade.toLevelLocalMembershipClauses
    (U : FullPresentedUpgrade (Base := Base) Const) :
    LevelLocalMembershipClauses (Base := Base) Const :=
  (U.toLocalMembershipClauses (Base := Base)).toLevelLocalMembershipClauses (Base := Base)

/-- Conditional canonical Kripke-Henkin package for membership forcing.  It is
conditional on the explicit local `∨`/`∃` gap; no hidden theory-specific
assumption is baked into the independent semantic interface. -/
noncomputable def canonicalKripkeHenkin
    (P : SchedulerProvider (Base := Base) Const)
    (L : LocalMembershipClauses (Base := Base) Const) :
    KripkeHenkin Base (WithParams Const) where
  World := ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const
  le := Le (Base := Base) (Const := Const)
  le_refl := le_refl (Base := Base) (Const := Const)
  le_trans := fun hUV hVW => le_trans (Base := Base) (Const := Const) hUV hVW
  atom := Atom (Base := Base) (Const := Const)
  atom_mono := fun hWV hφ => atom_mono (Base := Base) (Const := Const) hWV hφ
  eqVal := fun W s t => EqVal (Base := Base) (Const := Const) W s t
  eq_mono := fun hWV hst => eqVal_mono (Base := Base) (Const := Const) hWV hst
  eq_refl := fun W t => eq_refl (Base := Base) (Const := Const) W t
  eq_symm := fun hst => eq_symm (Base := Base) (Const := Const) hst
  eq_trans := fun hrs hst => eq_trans (Base := Base) (Const := Const) hrs hst
  eq_app_congr := fun hfg hst => eq_app_congr (Base := Base) (Const := Const) hfg hst
  eq_funext := fun hpoint => eq_funext (Base := Base) (Const := Const) hpoint
  eq_beta := fun t u => eq_beta (Base := Base) (Const := Const) _ t u
  eq_eta := fun f => eq_eta (Base := Base) (Const := Const) _ f
  forces := Forces (Base := Base) (Const := Const)
  forces_mono := fun hWV hφ => forces_mono (Base := Base) (Const := Const) hWV hφ
  forces_atom_const := fun c => forces_atom_const (Base := Base) (Const := Const) _ c
  forces_atom_app := fun f t => forces_atom_app (Base := Base) (Const := Const) _ f t
  forces_top := forces_top (Base := Base) (Const := Const) _
  forces_bot := forces_bot (Base := Base) (Const := Const) _
  forces_and := forces_and (Base := Base) (Const := Const)
  forces_or := L.or_clause
  forces_imp := forces_imp_provider (Base := Base) (Const := Const) P _
  forces_not := forces_not_provider (Base := Base) (Const := Const) P _
  forces_eq := forces_eq (Base := Base) (Const := Const)
  eq_prop_intro := fun hpq hqp =>
    SupportedCanonicalMembership.eq_prop_intro_mem (Base := Base) (Const := Const) hpq hqp
  eq_prop_elim_left := fun hpq =>
    SupportedCanonicalMembership.eq_prop_elim_left_mem (Base := Base) (Const := Const) hpq
  eq_prop_elim_right := fun hpq =>
    SupportedCanonicalMembership.eq_prop_elim_right_mem (Base := Base) (Const := Const) hpq
  forces_all := forces_all_provider (Base := Base) (Const := Const) P _
  forces_ex := L.ex_clause

/-- Level-respecting canonical Kripke-Henkin package for membership forcing.
Its preorder is `LevelLe`, so accessibility explicitly includes both carrier
extension and nondecreasing support level.  This package is useful for the
canonical truth-lemma spine; it does not replace the ordinary carrier-preorder
model above. -/
noncomputable def canonicalLevelKripkeHenkin
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const) :
    KripkeHenkin Base (WithParams Const) where
  World := ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const
  le := LevelLe (Base := Base) (Const := Const)
  le_refl := levelLe_refl (Base := Base) (Const := Const)
  le_trans := fun hUV hVW => levelLe_trans (Base := Base) (Const := Const) hUV hVW
  atom := Atom (Base := Base) (Const := Const)
  atom_mono := fun hWV hφ => atom_mono (Base := Base) (Const := Const) hWV.2 hφ
  eqVal := fun W s t => EqVal (Base := Base) (Const := Const) W s t
  eq_mono := fun hWV hst => eqVal_mono (Base := Base) (Const := Const) hWV.2 hst
  eq_refl := fun W t => eq_refl (Base := Base) (Const := Const) W t
  eq_symm := fun hst => eq_symm (Base := Base) (Const := Const) hst
  eq_trans := fun hrs hst => eq_trans (Base := Base) (Const := Const) hrs hst
  eq_app_congr := fun hfg hst => eq_app_congr (Base := Base) (Const := Const) hfg hst
  eq_funext := fun hpoint => eq_funext (Base := Base) (Const := Const) hpoint
  eq_beta := fun t u => eq_beta (Base := Base) (Const := Const) _ t u
  eq_eta := fun f => eq_eta (Base := Base) (Const := Const) _ f
  forces := Forces (Base := Base) (Const := Const)
  forces_mono := fun hWV hφ => forces_mono (Base := Base) (Const := Const) hWV.2 hφ
  forces_atom_const := fun c => forces_atom_const (Base := Base) (Const := Const) _ c
  forces_atom_app := fun f t => forces_atom_app (Base := Base) (Const := Const) _ f t
  forces_top := forces_top (Base := Base) (Const := Const) _
  forces_bot := forces_bot (Base := Base) (Const := Const) _
  forces_and := forces_and (Base := Base) (Const := Const)
  forces_or := L.or_clause
  forces_imp := forces_imp_level_provider (Base := Base) (Const := Const) P _
  forces_not := forces_not_level_provider (Base := Base) (Const := Const) P _
  forces_eq := forces_eq (Base := Base) (Const := Const)
  eq_prop_intro := fun hpq hqp =>
    SupportedCanonicalMembership.eq_prop_intro_mem (Base := Base) (Const := Const) hpq hqp
  eq_prop_elim_left := fun hpq =>
    SupportedCanonicalMembership.eq_prop_elim_left_mem (Base := Base) (Const := Const) hpq
  eq_prop_elim_right := fun hpq =>
    SupportedCanonicalMembership.eq_prop_elim_right_mem (Base := Base) (Const := Const) hpq
  forces_all := forces_all_level_provider (Base := Base) (Const := Const) P _
  forces_ex := L.ex_clause

/-- The ordinary canonical membership model reads forcing as carrier
membership by definition.  This is a readout theorem for the packaged
`KripkeHenkin` structure, not the separate recursive truth-bridge induction. -/
theorem canonicalKripkeHenkin_forces_iff_mem
    (P : SchedulerProvider (Base := Base) Const)
    (L : LocalMembershipClauses (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    (φ : ClosedFormula (WithParams Const)) :
    (canonicalKripkeHenkin (Base := Base) (Const := Const) P L).forces W φ ↔
      φ ∈ W.carrier := by
  rfl

/-- The level-respecting canonical membership model also reads forcing as
carrier membership by definition; its difference from the ordinary package is
the accessibility relation used by implication, negation, universals, and
existentials. -/
theorem canonicalLevelKripkeHenkin_forces_iff_mem
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    (φ : ClosedFormula (WithParams Const)) :
    (canonicalLevelKripkeHenkin (Base := Base) (Const := Const) P L).forces W φ ↔
      φ ∈ W.carrier := by
  rfl

/-- Empty-context forcing in the level-respecting canonical membership model is
exactly carrier membership. -/
theorem canonicalLevelKripkeHenkin_forcesAt_empty_iff_mem
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    (φ : ClosedFormula (WithParams Const))
    (ρ : ClosedEnv (Base := Base) (Const := WithParams Const) []) :
    ForcesAt (Base := Base) (Const := WithParams Const)
        (canonicalLevelKripkeHenkin (Base := Base) (Const := Const) P L) W ρ φ ↔
      φ ∈ W.carrier := by
  have hClosed : subst (Base := Base) (Const := WithParams Const) ρ φ = φ :=
    ClosedEnv.subst_empty (Base := Base) (Const := WithParams Const) ρ φ
  rw [ForcesAt, hClosed]
  rfl

/-- Canonical membership model packaged using the explicit full-presented
upgrade obligation rather than the opaque local-clause structure. -/
noncomputable def canonicalKripkeHenkinOfUpgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const) :
    KripkeHenkin Base (WithParams Const) :=
  canonicalKripkeHenkin (Base := Base) (Const := Const) P
    (U.toLocalMembershipClauses (Base := Base))

/-- Level-respecting canonical membership model packaged using an explicit
full-presented upgrade. -/
noncomputable def canonicalLevelKripkeHenkinOfUpgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const) :
    KripkeHenkin Base (WithParams Const) :=
  canonicalLevelKripkeHenkin (Base := Base) (Const := Const) P
    (U.toLevelLocalMembershipClauses (Base := Base))

/-- Upgrade-packaged level canonical forcing is carrier membership by
definition. -/
theorem canonicalLevelKripkeHenkinOfUpgrade_forces_iff_mem
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    (φ : ClosedFormula (WithParams Const)) :
    (canonicalLevelKripkeHenkinOfUpgrade (Base := Base) (Const := Const) P U).forces W φ ↔
      φ ∈ W.carrier := by
  rfl

/-- Empty-context forcing in the upgrade-packaged level canonical model is
carrier membership. -/
theorem canonicalLevelKripkeHenkinOfUpgrade_forcesAt_empty_iff_mem
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    (φ : ClosedFormula (WithParams Const))
    (ρ : ClosedEnv (Base := Base) (Const := WithParams Const) []) :
    ForcesAt (Base := Base) (Const := WithParams Const)
        (canonicalLevelKripkeHenkinOfUpgrade (Base := Base) (Const := Const) P U) W ρ φ ↔
      φ ∈ W.carrier :=
  canonicalLevelKripkeHenkin_forcesAt_empty_iff_mem
    (Base := Base) (Const := Const) P
    (U.toLevelLocalMembershipClauses (Base := Base)) W φ ρ

end SupportedCanonicalFrame

namespace SupportedCanonicalFrame

/-- Semantic consequence over the canonical supported-membership frame.  This is
an intermediate canonical countermodel surface, not the final independent
`KripkeHenkin` model class: worlds still carry raw presentations and forcing is
carrier membership. -/
def SupportedMembershipConsequence
    (T : ClosedTheorySet (WithParams Const))
    (θ : ClosedFormula (WithParams Const)) : Prop :=
  ∀ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
    (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T →
      Forces (Base := Base) (Const := Const) W ψ) →
        Forces (Base := Base) (Const := Const) W θ

/-- The supported-membership surface is exactly consequence over the ordinary
canonical membership model once that model is supplied. -/
theorem supportedMembershipConsequence_iff_canonicalKripkeHenkin
    (P : SchedulerProvider (Base := Base) Const)
    (L : LocalMembershipClauses (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)} :
    SupportedMembershipConsequence (Base := Base) (Const := Const) T θ ↔
      ∀ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T →
          (canonicalKripkeHenkin (Base := Base) (Const := Const) P L).forces W ψ) →
            (canonicalKripkeHenkin (Base := Base) (Const := Const) P L).forces W θ := by
  rfl

/-- The same supported-membership surface is exactly consequence over the
level-respecting canonical membership model; only the model's accessibility
relation differs. -/
theorem supportedMembershipConsequence_iff_canonicalLevelKripkeHenkin
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)} :
    SupportedMembershipConsequence (Base := Base) (Const := Const) T θ ↔
      ∀ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T →
          (canonicalLevelKripkeHenkin (Base := Base) (Const := Const) P L).forces W ψ) →
            (canonicalLevelKripkeHenkin (Base := Base) (Const := Const) P L).forces W θ := by
  rfl

/-- EM-free provability is sound for the supported-membership consequence
surface by deductive closure of every supported presented carrier. -/
theorem supportedMembershipConsequence_of_provable
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hθ : ClosedTheorySet.Provable (Const := WithParams Const) T θ) :
    SupportedMembershipConsequence (Base := Base) (Const := Const) T θ := by
  intro W hT
  exact W.closed
    (ClosedTheorySet.provable_mono (Const := WithParams Const)
      (T := T) (U := W.carrier) hT hθ)

/-- A supported canonical counterworld refutes supported-membership
consequence directly, without the full `KripkeHenkin` upgrade obligation. -/
theorem not_supportedMembershipConsequence_of_canonical_countermodel
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (hT : ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier)
    (hθ : θ ∉ W.carrier) :
    ¬ SupportedMembershipConsequence (Base := Base) (Const := Const) T θ := by
  intro hSem
  exact hθ (hSem W hT)

/-- If the supported raw construction supplies counterworlds for every
non-derivation, supported-membership semantic consequence implies provability. -/
theorem provable_of_supportedMembershipConsequence_with_canonical_countermodels
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hCounter :
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T θ →
        ∃ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const,
          (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier) ∧
            θ ∉ W.carrier)
    (hSem : SupportedMembershipConsequence (Base := Base) (Const := Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  classical
  by_contra hNot
  obtain ⟨W, hT, hθ⟩ := hCounter hNot
  exact (not_supportedMembershipConsequence_of_canonical_countermodel
    (Base := Base) (Const := Const) W hT hθ) hSem

/-- A supported raw alternating countermodel refutes supported-membership
consequence at a fixed parameter bound. -/
theorem not_supportedMembershipConsequence_of_supported_countermodel_at_bound
    (P : SchedulerProvider (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ)
    (hNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T θ) :
    ¬ SupportedMembershipConsequence (Base := Base) (Const := Const) T θ := by
  obtain ⟨W, _hLevel, hT, hθ⟩ :=
    ClosedTheorySet.exists_supported_presented_rawAlternatingScheduledStageLimit_separating
      (Base := Base) (Const := Const) (ℓ := m) (T := T)
      (P.scheduler m) hLayer hStage hθStage hNot
  exact not_supportedMembershipConsequence_of_canonical_countermodel
    (Base := Base) (Const := Const) W hT hθ

/-- Conditional completeness at a fixed parameter bound for the supported
canonical membership surface. -/
theorem provable_of_supportedMembershipConsequence_supported_at_bound
    (P : SchedulerProvider (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ)
    (hSem : SupportedMembershipConsequence (Base := Base) (Const := Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  classical
  by_contra hNot
  exact (not_supportedMembershipConsequence_of_supported_countermodel_at_bound
    (Base := Base) (Const := Const) P hLayer hStage hθStage hNot) hSem

/-- At a fixed parameter bound, the supported canonical membership surface is
complete for the EM-free calculus.  This is an intermediate equivalence for the
raw presented-world semantics, not yet the final independent `KripkeHenkin`
consequence theorem. -/
theorem provable_iff_supportedMembershipConsequence_supported_at_bound
    (P : SchedulerProvider (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      SupportedMembershipConsequence (Base := Base) (Const := Const) T θ := by
  constructor
  · exact supportedMembershipConsequence_of_provable (Base := Base) (Const := Const)
  · exact provable_of_supportedMembershipConsequence_supported_at_bound
      (Base := Base) (Const := Const) P hLayer hStage hθStage

/-- Param-free conditional completeness for the supported canonical membership
surface.  This avoids the full `KripkeHenkin` upgrade obligation and records only
what the current supported raw construction already proves. -/
theorem provable_of_supportedMembershipConsequence_param_free_supported
    (P : SchedulerProvider (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ)
    (hSem : SupportedMembershipConsequence (Base := Base) (Const := Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  refine provable_of_supportedMembershipConsequence_supported_at_bound
    (Base := Base) (Const := Const) P (m := 0) ?_ ?_ ?_ hSem
  · intro ψ hψ σ m k _hm
    exact hT0 ψ hψ σ (Nat.pair m k)
  · intro ψ hψ σ r k _hr
    exact hT0 ψ hψ σ (Nat.pair 0 (Nat.pair r k))
  · intro σ r k _hr
    exact hθ0 σ (Nat.pair 0 (Nat.pair r k))

/-- Param-free equivalence for the supported canonical membership surface.  The
remaining assumptions are exactly the scheduler data for the raw alternating
construction; the theorem deliberately does not claim the final model-class
`Consequence` result. -/
theorem provable_iff_supportedMembershipConsequence_param_free_supported
    (P : SchedulerProvider (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      SupportedMembershipConsequence (Base := Base) (Const := Const) T θ := by
  constructor
  · exact supportedMembershipConsequence_of_provable (Base := Base) (Const := Const)
  · exact provable_of_supportedMembershipConsequence_param_free_supported
      (Base := Base) (Const := Const) P hT0 hθ0

/-- Fixed-bound completeness stated directly against the level-respecting
canonical `KripkeHenkin` package.  The local `∨`/`∃` clauses remain explicit in
`L`; the RHS is no longer the intermediate supported-membership abbreviation. -/
theorem provable_iff_canonicalLevelKripkeHenkin_supported_at_bound
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      ∀ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T →
          (canonicalLevelKripkeHenkin (Base := Base) (Const := Const) P L).forces W ψ) →
            (canonicalLevelKripkeHenkin (Base := Base) (Const := Const) P L).forces W θ := by
  exact
    (provable_iff_supportedMembershipConsequence_supported_at_bound
      (Base := Base) (Const := Const) P hLayer hStage hθStage).trans
      (supportedMembershipConsequence_iff_canonicalLevelKripkeHenkin
        (Base := Base) (Const := Const) P L)

/-- Fixed-bound level-canonical completeness with the local canonical gap
expressed as an explicit full-presented upgrade obligation. -/
theorem provable_iff_canonicalLevelKripkeHenkin_supported_at_bound_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      ∀ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T →
          (canonicalLevelKripkeHenkinOfUpgrade
            (Base := Base) (Const := Const) P U).forces W ψ) →
            (canonicalLevelKripkeHenkinOfUpgrade
              (Base := Base) (Const := Const) P U).forces W θ := by
  exact provable_iff_canonicalLevelKripkeHenkin_supported_at_bound
    (Base := Base) (Const := Const) P
    (U.toLevelLocalMembershipClauses (Base := Base)) hLayer hStage hθStage

/-- Param-free completeness stated directly against the level-respecting
canonical `KripkeHenkin` package. -/
theorem provable_iff_canonicalLevelKripkeHenkin_param_free_supported
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      ∀ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T →
          (canonicalLevelKripkeHenkin (Base := Base) (Const := Const) P L).forces W ψ) →
            (canonicalLevelKripkeHenkin (Base := Base) (Const := Const) P L).forces W θ := by
  exact
    (provable_iff_supportedMembershipConsequence_param_free_supported
      (Base := Base) (Const := Const) P hT0 hθ0).trans
      (supportedMembershipConsequence_iff_canonicalLevelKripkeHenkin
        (Base := Base) (Const := Const) P L)

/-- Param-free level-canonical completeness with the local canonical gap
expressed as an explicit full-presented upgrade obligation. -/
theorem provable_iff_canonicalLevelKripkeHenkin_param_free_supported_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      ∀ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T →
          (canonicalLevelKripkeHenkinOfUpgrade
            (Base := Base) (Const := Const) P U).forces W ψ) →
            (canonicalLevelKripkeHenkinOfUpgrade
              (Base := Base) (Const := Const) P U).forces W θ := by
  exact provable_iff_canonicalLevelKripkeHenkin_param_free_supported
    (Base := Base) (Const := Const) P
    (U.toLevelLocalMembershipClauses (Base := Base)) hT0 hθ0

/-- Full semantic consequence over independent `KripkeHenkin` structures
restricts to the supported canonical membership surface whenever the conditional
canonical membership model is available. -/
theorem supportedMembershipConsequence_of_consequence
    (P : SchedulerProvider (Base := Base) Const)
    (L : LocalMembershipClauses (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hSem : Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ) :
    SupportedMembershipConsequence (Base := Base) (Const := Const) T θ := by
  intro W hT
  exact hSem (canonicalKripkeHenkin (Base := Base) (Const := Const) P L) W hT

/-- A supported-membership counterexample is already a counterexample to full
semantic consequence once the conditional canonical membership model is
available. -/
theorem not_consequence_of_not_supportedMembershipConsequence
    (P : SchedulerProvider (Base := Base) Const)
    (L : LocalMembershipClauses (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ SupportedMembershipConsequence (Base := Base) (Const := Const) T θ) :
    ¬ Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ := by
  intro hSem
  exact hNot (supportedMembershipConsequence_of_consequence
    (Base := Base) (Const := Const) P L hSem)

/-- Full semantic consequence restricts to supported-membership consequence
when the conditional canonical membership model is supplied by an explicit
full-presented upgrade. -/
theorem supportedMembershipConsequence_of_consequence_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hSem : Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ) :
    SupportedMembershipConsequence (Base := Base) (Const := Const) T θ :=
  supportedMembershipConsequence_of_consequence
    (Base := Base) (Const := Const) P (U.toLocalMembershipClauses (Base := Base)) hSem

/-- A supported-membership counterexample is a full semantic counterexample
when the canonical membership model is supplied by an explicit full-presented
upgrade. -/
theorem not_consequence_of_not_supportedMembershipConsequence_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ SupportedMembershipConsequence (Base := Base) (Const := Const) T θ) :
    ¬ Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ :=
  not_consequence_of_not_supportedMembershipConsequence
    (Base := Base) (Const := Const) P (U.toLocalMembershipClauses (Base := Base)) hNot

theorem not_consequence_of_canonical_countermodel
    (P : SchedulerProvider (Base := Base) Const)
    (L : LocalMembershipClauses (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (hT : ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier)
    (hθ : θ ∉ W.carrier) :
    ¬ Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ := by
  intro hSem
  exact hθ (hSem
    (canonicalKripkeHenkin (Base := Base) (Const := Const) P L) W hT)

/-- A supported canonical counterworld refutes full semantic consequence when
the canonical membership model is supplied by a full-presented upgrade. -/
theorem not_consequence_of_canonical_countermodel_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (hT : ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier)
    (hθ : θ ∉ W.carrier) :
    ¬ Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ :=
  not_consequence_of_canonical_countermodel
    (Base := Base) (Const := Const) P (U.toLocalMembershipClauses (Base := Base)) W hT hθ

theorem provable_of_consequence_with_canonical_countermodels
    (P : SchedulerProvider (Base := Base) Const)
    (L : LocalMembershipClauses (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hCounter :
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T θ →
        ∃ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const,
          (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier) ∧
            θ ∉ W.carrier)
    (hSem : Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  classical
  by_contra hNot
  obtain ⟨W, hT, hθ⟩ := hCounter hNot
  exact (not_consequence_of_canonical_countermodel
    (Base := Base) (Const := Const) P L W hT hθ) hSem

/-- Abstract countermodel completeness with the canonical membership model
supplied by an explicit full-presented upgrade. -/
theorem provable_of_consequence_with_canonical_countermodels_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hCounter :
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T θ →
        ∃ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const,
          (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier) ∧
            θ ∉ W.carrier)
    (hSem : Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ :=
  provable_of_consequence_with_canonical_countermodels
    (Base := Base) (Const := Const) P (U.toLocalMembershipClauses (Base := Base))
    hCounter hSem

/-- A supported raw alternating countermodel refutes semantic consequence in the
conditional canonical membership model. -/
theorem not_consequence_of_supported_countermodel_at_bound
    (P : SchedulerProvider (Base := Base) Const)
    (L : LocalMembershipClauses (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ)
    (hNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T θ) :
    ¬ Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ := by
  obtain ⟨W, _hLevel, hT, hθ⟩ :=
    ClosedTheorySet.exists_supported_presented_rawAlternatingScheduledStageLimit_separating
      (Base := Base) (Const := Const) (ℓ := m) (T := T)
      (P.scheduler m) hLayer hStage hθStage hNot
  exact not_consequence_of_canonical_countermodel
    (Base := Base) (Const := Const) P L W hT hθ

/-- Conditional completeness from the actual supported raw countermodel
construction at a fixed parameter bound. -/
theorem provable_of_consequence_supported_at_bound
    (P : SchedulerProvider (Base := Base) Const)
    (L : LocalMembershipClauses (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ)
    (hSem : Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  classical
  by_contra hNot
  exact (not_consequence_of_supported_countermodel_at_bound
    (Base := Base) (Const := Const) P L hLayer hStage hθStage hNot) hSem

/-- Conditional fixed-bound equivalence for the full independent
`KripkeHenkin.Consequence` relation, assuming the supported canonical frame has
the local membership clauses needed to become a full model. -/
theorem provable_iff_consequence_supported_at_bound
    (P : SchedulerProvider (Base := Base) Const)
    (L : LocalMembershipClauses (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ := by
  constructor
  · exact consequence_of_provable (Base := Base) (Const := WithParams Const)
  · exact provable_of_consequence_supported_at_bound
      (Base := Base) (Const := Const) P L hLayer hStage hθStage

/-- Param-free conditional completeness for the supported canonical membership
model.  The remaining hypotheses are precisely the scheduler data and the local
membership clauses still needed to package that membership model as a
`KripkeHenkin` structure. -/
theorem provable_of_consequence_param_free_supported
    (P : SchedulerProvider (Base := Base) Const)
    (L : LocalMembershipClauses (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ)
    (hSem : Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  refine provable_of_consequence_supported_at_bound
    (Base := Base) (Const := Const) P L (m := 0) ?_ ?_ ?_ hSem
  · intro ψ hψ σ m k _hm
    exact hT0 ψ hψ σ (Nat.pair m k)
  · intro ψ hψ σ r k _hr
    exact hT0 ψ hψ σ (Nat.pair 0 (Nat.pair r k))
  · intro σ r k _hr
    exact hθ0 σ (Nat.pair 0 (Nat.pair r k))

/-- Param-free conditional equivalence for the full independent
`KripkeHenkin.Consequence` relation, with the remaining canonical obligations
kept explicit. -/
theorem provable_iff_consequence_param_free_supported
    (P : SchedulerProvider (Base := Base) Const)
    (L : LocalMembershipClauses (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ := by
  constructor
  · exact consequence_of_provable (Base := Base) (Const := WithParams Const)
  · exact provable_of_consequence_param_free_supported
      (Base := Base) (Const := Const) P L hT0 hθ0

/-- Full semantic consequence also restricts to supported-membership
consequence through the level-respecting canonical membership model. -/
theorem supportedMembershipConsequence_of_consequence_level
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hSem : Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ) :
    SupportedMembershipConsequence (Base := Base) (Const := Const) T θ := by
  intro W hT
  exact hSem (canonicalLevelKripkeHenkin (Base := Base) (Const := Const) P L) W hT

/-- A supported-membership counterexample refutes full semantic consequence
through the level-respecting canonical membership model. -/
theorem not_consequence_of_not_supportedMembershipConsequence_level
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ SupportedMembershipConsequence (Base := Base) (Const := Const) T θ) :
    ¬ Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ := by
  intro hSem
  exact hNot (supportedMembershipConsequence_of_consequence_level
    (Base := Base) (Const := Const) P L hSem)

/-- A supported canonical counterworld refutes full semantic consequence using
the level-respecting canonical membership model. -/
theorem not_consequence_of_canonical_countermodel_level
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (hT : ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier)
    (hθ : θ ∉ W.carrier) :
    ¬ Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ := by
  intro hSem
  exact hθ (hSem
    (canonicalLevelKripkeHenkin (Base := Base) (Const := Const) P L) W hT)

/-- Full semantic consequence restricts to supported-membership consequence
through the level-respecting canonical membership model packaged from a
full-presented upgrade. -/
theorem supportedMembershipConsequence_of_consequence_level_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hSem : Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ) :
    SupportedMembershipConsequence (Base := Base) (Const := Const) T θ :=
  supportedMembershipConsequence_of_consequence_level
    (Base := Base) (Const := Const) P
    (U.toLevelLocalMembershipClauses (Base := Base)) hSem

/-- A supported-membership counterexample refutes full semantic consequence
through the level-respecting canonical membership model packaged from a
full-presented upgrade. -/
theorem not_consequence_of_not_supportedMembershipConsequence_level_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ SupportedMembershipConsequence (Base := Base) (Const := Const) T θ) :
    ¬ Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ :=
  not_consequence_of_not_supportedMembershipConsequence_level
    (Base := Base) (Const := Const) P
    (U.toLevelLocalMembershipClauses (Base := Base)) hNot

/-- A supported canonical counterworld refutes full semantic consequence using
the level-respecting canonical membership model packaged from a full-presented
upgrade. -/
theorem not_consequence_of_canonical_countermodel_level_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (hT : ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier)
    (hθ : θ ∉ W.carrier) :
    ¬ Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ :=
  not_consequence_of_canonical_countermodel_level
    (Base := Base) (Const := Const) P
    (U.toLevelLocalMembershipClauses (Base := Base)) W hT hθ

/-- Abstract countermodel completeness through the level-respecting canonical
membership model. -/
theorem provable_of_consequence_with_canonical_countermodels_level
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hCounter :
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T θ →
        ∃ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const,
          (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier) ∧
            θ ∉ W.carrier)
    (hSem : Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  classical
  by_contra hNot
  obtain ⟨W, hT, hθ⟩ := hCounter hNot
  exact (not_consequence_of_canonical_countermodel_level
    (Base := Base) (Const := Const) P L W hT hθ) hSem

/-- Abstract countermodel completeness through the level-respecting canonical
membership model packaged from a full-presented upgrade. -/
theorem provable_of_consequence_with_canonical_countermodels_level_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hCounter :
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T θ →
        ∃ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const,
          (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier) ∧
            θ ∉ W.carrier)
    (hSem : Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ :=
  provable_of_consequence_with_canonical_countermodels_level
    (Base := Base) (Const := Const) P
    (U.toLevelLocalMembershipClauses (Base := Base)) hCounter hSem

/-- A supported raw alternating countermodel refutes semantic consequence in
the level-respecting canonical membership model. -/
theorem not_consequence_of_supported_countermodel_at_bound_level
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ)
    (hNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T θ) :
    ¬ Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ := by
  obtain ⟨W, _hLevel, hT, hθ⟩ :=
    ClosedTheorySet.exists_supported_presented_rawAlternatingScheduledStageLimit_separating
      (Base := Base) (Const := Const) (ℓ := m) (T := T)
      (P.scheduler m) hLayer hStage hθStage hNot
  exact not_consequence_of_canonical_countermodel_level
    (Base := Base) (Const := Const) P L W hT hθ

/-- Conditional completeness from the supported raw countermodel construction
using the level-respecting canonical membership model. -/
theorem provable_of_consequence_supported_at_bound_level
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ)
    (hSem : Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  classical
  by_contra hNot
  exact (not_consequence_of_supported_countermodel_at_bound_level
    (Base := Base) (Const := Const) P L hLayer hStage hθStage hNot) hSem

/-- Conditional fixed-bound equivalence through the level-respecting canonical
membership model. -/
theorem provable_iff_consequence_supported_at_bound_level
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ := by
  constructor
  · exact consequence_of_provable (Base := Base) (Const := WithParams Const)
  · exact provable_of_consequence_supported_at_bound_level
      (Base := Base) (Const := Const) P L hLayer hStage hθStage

/-- Param-free conditional completeness through the level-respecting canonical
membership model. -/
theorem provable_of_consequence_param_free_supported_level
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ)
    (hSem : Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  refine provable_of_consequence_supported_at_bound_level
    (Base := Base) (Const := Const) P L (m := 0) ?_ ?_ ?_ hSem
  · intro ψ hψ σ m k _hm
    exact hT0 ψ hψ σ (Nat.pair m k)
  · intro ψ hψ σ r k _hr
    exact hT0 ψ hψ σ (Nat.pair 0 (Nat.pair r k))
  · intro σ r k _hr
    exact hθ0 σ (Nat.pair 0 (Nat.pair r k))

/-- Param-free conditional equivalence through the level-respecting canonical
membership model. -/
theorem provable_iff_consequence_param_free_supported_level
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ := by
  constructor
  · exact consequence_of_provable (Base := Base) (Const := WithParams Const)
  · exact provable_of_consequence_param_free_supported_level
      (Base := Base) (Const := Const) P L hT0 hθ0

/-- A supported raw alternating countermodel refutes semantic consequence in
the level-respecting canonical membership model packaged from a full-presented
upgrade. -/
theorem not_consequence_of_supported_countermodel_at_bound_level_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ)
    (hNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T θ) :
    ¬ Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ :=
  not_consequence_of_supported_countermodel_at_bound_level
    (Base := Base) (Const := Const) P
    (U.toLevelLocalMembershipClauses (Base := Base))
    hLayer hStage hθStage hNot

/-- Conditional completeness at a fixed parameter bound through the
level-respecting canonical membership model, with the remaining local canonical
obligation stated as a full-presented upgrade. -/
theorem provable_of_consequence_supported_at_bound_level_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ)
    (hSem : Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ :=
  provable_of_consequence_supported_at_bound_level
    (Base := Base) (Const := Const) P
    (U.toLevelLocalMembershipClauses (Base := Base))
    hLayer hStage hθStage hSem

/-- Conditional fixed-bound equivalence through the level-respecting canonical
membership model, with the remaining local canonical obligation stated as a
full-presented upgrade. -/
theorem provable_iff_consequence_supported_at_bound_level_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ :=
  provable_iff_consequence_supported_at_bound_level
    (Base := Base) (Const := Const) P
    (U.toLevelLocalMembershipClauses (Base := Base)) hLayer hStage hθStage

/-- Param-free conditional completeness through the level-respecting canonical
membership model, with the local canonical gap expressed as the explicit
full-presented upgrade obligation. -/
theorem provable_of_consequence_param_free_supported_level_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ)
    (hSem : Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ :=
  provable_of_consequence_param_free_supported_level
    (Base := Base) (Const := Const) P
    (U.toLevelLocalMembershipClauses (Base := Base)) hT0 hθ0 hSem

/-- Param-free conditional equivalence through the level-respecting canonical
membership model, with the local canonical gap expressed as the explicit
full-presented upgrade obligation. -/
theorem provable_iff_consequence_param_free_supported_level_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ :=
  provable_iff_consequence_param_free_supported_level
    (Base := Base) (Const := Const) P
    (U.toLevelLocalMembershipClauses (Base := Base)) hT0 hθ0

/-- A supported raw alternating countermodel refutes semantic consequence in
the canonical membership model packaged from a full-presented upgrade. -/
theorem not_consequence_of_supported_countermodel_at_bound_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ)
    (hNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T θ) :
    ¬ Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ := by
  exact not_consequence_of_supported_countermodel_at_bound
    (Base := Base) (Const := Const) P
    (U.toLocalMembershipClauses (Base := Base))
    hLayer hStage hθStage hNot

/-- Conditional completeness at a fixed parameter bound, with the remaining
local canonical obligation stated as a full-presented upgrade. -/
theorem provable_of_consequence_supported_at_bound_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ)
    (hSem : Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  exact provable_of_consequence_supported_at_bound
    (Base := Base) (Const := Const) P
    (U.toLocalMembershipClauses (Base := Base))
    hLayer hStage hθStage hSem

/-- Conditional fixed-bound equivalence with the remaining local canonical
obligation stated as a full-presented upgrade. -/
theorem provable_iff_consequence_supported_at_bound_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ := by
  exact provable_iff_consequence_supported_at_bound
    (Base := Base) (Const := Const) P
    (U.toLocalMembershipClauses (Base := Base)) hLayer hStage hθStage

/-- Param-free conditional completeness with the local canonical gap expressed
as the explicit full-presented upgrade obligation. -/
theorem provable_of_consequence_param_free_supported_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ)
    (hSem : Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  exact provable_of_consequence_param_free_supported
    (Base := Base) (Const := Const) P
    (U.toLocalMembershipClauses (Base := Base)) hT0 hθ0 hSem

/-- Param-free conditional equivalence with the local canonical gap expressed as
the explicit full-presented upgrade obligation. -/
theorem provable_iff_consequence_param_free_supported_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ := by
  exact provable_iff_consequence_param_free_supported
    (Base := Base) (Const := Const) P
    (U.toLocalMembershipClauses (Base := Base)) hT0 hθ0

/-! ## Intuitionistic HOL supported completeness surface -/

/-- Positive supported example: EM-free derivability is valid in every
supported canonical membership world. -/
theorem intuitionisticHOL_supported_soundness
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hθ : ClosedTheorySet.Provable (Const := WithParams Const) T θ) :
    SupportedMembershipConsequence (Base := Base) (Const := Const) T θ :=
  supportedMembershipConsequence_of_provable
    (Base := Base) (Const := Const) hθ

/-- Negative supported example: the raw alternating construction supplies a
counterworld for every fixed-bound non-derivation. -/
theorem intuitionisticHOL_supported_countermodel_at_bound
    (P : SchedulerProvider (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ)
    (hNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T θ) :
    ¬ SupportedMembershipConsequence (Base := Base) (Const := Const) T θ :=
  not_supportedMembershipConsequence_of_supported_countermodel_at_bound
    (Base := Base) (Const := Const) P hLayer hStage hθStage hNot

/-- Fixed-bound completeness for the supported canonical membership semantics. -/
theorem intuitionisticHOL_supported_completeness_at_bound
    (P : SchedulerProvider (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      SupportedMembershipConsequence (Base := Base) (Const := Const) T θ :=
  provable_iff_supportedMembershipConsequence_supported_at_bound
    (Base := Base) (Const := Const) P hLayer hStage hθStage

/-- Param-free completeness for the supported canonical membership semantics. -/
theorem intuitionisticHOL_supported_completeness_param_free
    (P : SchedulerProvider (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      SupportedMembershipConsequence (Base := Base) (Const := Const) T θ :=
  provable_iff_supportedMembershipConsequence_param_free_supported
    (Base := Base) (Const := Const) P hT0 hθ0

/-- Negative level-canonical example: the supported counterworld also refutes
the level-respecting canonical `KripkeHenkin` package. -/
theorem intuitionisticHOL_level_kripke_countermodel_at_bound
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ)
    (hNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T θ) :
    ¬ ∀ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T →
          (canonicalLevelKripkeHenkin (Base := Base) (Const := Const) P L).forces W ψ) →
            (canonicalLevelKripkeHenkin (Base := Base) (Const := Const) P L).forces W θ := by
  intro hSem
  have hMem :
      SupportedMembershipConsequence (Base := Base) (Const := Const) T θ :=
    (supportedMembershipConsequence_iff_canonicalLevelKripkeHenkin
      (Base := Base) (Const := Const) P L).mpr hSem
  exact (not_supportedMembershipConsequence_of_supported_countermodel_at_bound
    (Base := Base) (Const := Const) P hLayer hStage hθStage hNot) hMem

/-- Param-free completeness stated on the level-respecting canonical
`KripkeHenkin` package. -/
theorem intuitionisticHOL_level_kripke_completeness_param_free
    (P : SchedulerProvider (Base := Base) Const)
    (L : LevelLocalMembershipClauses (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      ∀ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T →
          (canonicalLevelKripkeHenkin (Base := Base) (Const := Const) P L).forces W ψ) →
            (canonicalLevelKripkeHenkin (Base := Base) (Const := Const) P L).forces W θ :=
  provable_iff_canonicalLevelKripkeHenkin_param_free_supported
    (Base := Base) (Const := Const) P L hT0 hθ0

/-- Param-free completeness for independent `KripkeHenkin` consequence remains
conditional on the explicit full-presented upgrade. -/
theorem intuitionisticHOL_full_kripke_completeness_param_free_of_upgrade
    (P : SchedulerProvider (Base := Base) Const)
    (U : FullPresentedUpgrade (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) T θ :=
  provable_iff_consequence_param_free_supported_of_upgrade
    (Base := Base) (Const := Const) P U hT0 hθ0

end SupportedCanonicalFrame

end KripkeHenkin

end Mettapedia.Logic.HOL
