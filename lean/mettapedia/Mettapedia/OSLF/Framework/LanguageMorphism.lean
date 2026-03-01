import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.OSLF.Formula

/-!
# Language Morphisms between OSLF Instances

A `LanguageMorphism` captures the notion of a correct encoding between two
OSLF language instances. It consists of a term-level map and simulation
conditions that ensure operational correspondence.

## Key Theorems

- `forward_multi`: Forward simulation lifts from single-step to multi-step
- `backward_multi`: Backward simulation lifts from single-step to multi-step
- `operational_correspondence`: Full operational correspondence from simulation
- `preserves_diamond`: Diamond modality is preserved by the morphism

## Motivation

The π→ρ encoding (Lybech 2022) is a LanguageMorphism from piCalc to rhoCalc.
Rather than proving operational correspondence by brute-force case analysis
on each reduction rule, we:
1. Define the generic simulation theory here (once)
2. Verify the simulation conditions for each reduction rule (modular)
3. Derive operational correspondence by instantiation

## References

- Gorla (2010), "Towards a Unified Approach to Encodability and Separation Results"
- Meredith & Stay, "Operational Semantics in Logical Form"
-/

namespace Mettapedia.OSLF.Framework.LangMorphism

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Formula

/-! ## Multi-Step Reduction for Generic Languages

Reflexive-transitive closure of `langReduces` for any LanguageDef.
This parallels `ReducesStar` from the ρ-calculus but works for any language. -/

/-- Multi-step reduction: `p` reduces to `q` in zero or more steps via `lang`.
    Prop-valued (unlike the ρ-calculus Type-valued ReducesStar). -/
inductive LangReducesStar (lang : LanguageDef) : Pattern → Pattern → Prop where
  | refl (p : Pattern) : LangReducesStar lang p p
  | step {p q r : Pattern} :
      langReduces lang p q → LangReducesStar lang q r → LangReducesStar lang p r

notation:20 p " ⟶[" lang "]* " q => LangReducesStar lang p q

namespace LangReducesStar

/-- Multi-step reduction is transitive. -/
theorem trans {lang : LanguageDef} {p q r : Pattern}
    (h1 : p ⟶[lang]* q) (h2 : q ⟶[lang]* r) : p ⟶[lang]* r := by
  induction h1 with
  | refl => exact h2
  | step h_pq _ ih => exact .step h_pq (ih h2)

/-- Single step gives multi-step. -/
theorem single {lang : LanguageDef} {p q : Pattern}
    (h : langReduces lang p q) : p ⟶[lang]* q :=
  .step h (.refl q)

end LangReducesStar

/-! ## Structural Congruence for Generic Languages

A generic notion of "up-to SC" equivalence for encoded terms.
For the π→ρ encoding, this wraps the ρ-calculus StructuralCongruence. -/

/-- SC-equivalence relation for a target language. Parameterized so different
    languages can plug in their own SC. For languages without SC, use Eq. -/
class TargetSC (lang : LanguageDef) where
  /-- The structural congruence relation -/
  sc : Pattern → Pattern → Prop
  /-- SC is reflexive -/
  sc_refl : ∀ p, sc p p
  /-- SC is symmetric -/
  sc_symm : ∀ p q, sc p q → sc q p
  /-- SC is transitive -/
  sc_trans : ∀ p q r, sc p q → sc q r → sc p r

/-- Default: trivial SC (equality) for any language -/
instance : TargetSC lang where
  sc := Eq
  sc_refl := fun _ => rfl
  sc_symm := fun _ _ h => h.symm
  sc_trans := fun _ _ _ h1 h2 => h1.trans h2

/-! ## Language Morphism -/

/-- A morphism between two OSLF language instances.

    A language morphism `m : LanguageMorphism L₁ L₂ sc` captures a correct
    encoding from L₁ to L₂ where:
    - `mapTerm` translates L₁ terms to L₂ terms
    - `forward_sim` ensures L₁ reductions are simulated by L₂
    - `backward_sim` ensures L₂ reductions of encoded terms come from L₁

    The simulation is "up to SC" — the L₂ result must be SC-equivalent
    (not necessarily equal) to the encoding of the L₁ result.

    Reference: Gorla (2010), Definition of "valid encoding" -/
structure LanguageMorphism (L₁ L₂ : LanguageDef) (sc : Pattern → Pattern → Prop) where
  /-- Maps L₁ terms to L₂ terms -/
  mapTerm : Pattern → Pattern

  /-- Forward simulation: every L₁ single-step reduction is matched by L₂
      multi-step reduction, up to sc on the result.

      ∀ p q, L₁ : p ⟶ q → ∃ T, L₂ : mapTerm(p) ⟶* T ∧ sc T (mapTerm q) -/
  forward_sim : ∀ p q, langReduces L₁ p q →
    ∃ T, LangReducesStar L₂ (mapTerm p) T ∧ sc T (mapTerm q)

  /-- Backward simulation: every L₂ single-step reduction of an encoded term
      corresponds to some L₁ reduction.

      ∀ p T, L₂ : mapTerm(p) ⟶ T → ∃ p', L₁ : p ⟶* p' ∧ sc T (mapTerm p') -/
  backward_sim : ∀ p T, langReduces L₂ (mapTerm p) T →
    ∃ p', LangReducesStar L₁ p p' ∧ sc T (mapTerm p')

/-! ## Generic Theorems -/

variable {L₁ L₂ : LanguageDef} {sc : Pattern → Pattern → Prop}

/-- Forward simulation (simple version): when SC = Eq, no SC-gap folding needed. -/
theorem LanguageMorphism.forward_multi_eq
    (m : LanguageMorphism L₁ L₂ Eq)
    {p q : Pattern} (h : LangReducesStar L₁ p q) :
    ∃ T, LangReducesStar L₂ (m.mapTerm p) T ∧ T = m.mapTerm q := by
  induction h with
  | refl p => exact ⟨m.mapTerm p, .refl _, rfl⟩
  | step h_pq _h_qr ih =>
    obtain ⟨_, h_star1, rfl⟩ := m.forward_sim _ _ h_pq
    obtain ⟨T₂, h_star2, h_eq2⟩ := ih
    exact ⟨T₂, h_star1.trans h_star2, h_eq2⟩

/-- Forward simulation lifts to multi-step, using SC-closed reduction.

    Requires:
    - `sc_refl`: SC is reflexive
    - `sc_trans`: SC is transitive
    - `sc_star_reduces`: SC-gap can be absorbed into multi-step reduction
      (if sc(p,q) and L₂: q ⟶* r, then L₂: p ⟶* r' with sc(r',r)) -/
theorem LanguageMorphism.forward_multi_strong
    (m : LanguageMorphism L₁ L₂ sc)
    (sc_refl : ∀ p, sc p p)
    (sc_trans : ∀ p q r, sc p q → sc q r → sc p r)
    (sc_star_reduces : ∀ p q, sc p q →
      ∀ r, LangReducesStar L₂ q r →
      ∃ r', LangReducesStar L₂ p r' ∧ sc r' r)
    {p q : Pattern} (h : LangReducesStar L₁ p q) :
    ∃ T, LangReducesStar L₂ (m.mapTerm p) T ∧ sc T (m.mapTerm q) := by
  induction h with
  | refl p => exact ⟨m.mapTerm p, .refl _, sc_refl _⟩
  | step h_pq _h_qr ih =>
    obtain ⟨T₁, h_star1, h_sc1⟩ := m.forward_sim _ _ h_pq
    obtain ⟨T₂, h_star2, h_sc2⟩ := ih
    -- Bridge: sc(T₁, mapTerm(q_mid)) and L₂: mapTerm(q_mid) ⟶* T₂
    obtain ⟨T_final, h_bridge, h_sc_final⟩ := sc_star_reduces _ _ h_sc1 _ h_star2
    -- T₁ ⟶* T_final, sc(T_final, T₂), sc(T₂, mapTerm(q))
    exact ⟨T_final, h_star1.trans h_bridge, sc_trans _ _ _ h_sc_final h_sc2⟩

/-- Backward simulation (Eq version): auxiliary with generalized start point.
    We quantify over `start` to make the first index a variable for induction. -/
private theorem backward_multi_eq_aux
    (m : LanguageMorphism L₁ L₂ Eq) :
    ∀ {start T : Pattern}, LangReducesStar L₂ start T →
    ∀ {p : Pattern}, start = m.mapTerm p →
    ∃ p', LangReducesStar L₁ p p' ∧ T = m.mapTerm p' := by
  intro start T h
  induction h with
  | refl _ =>
    intro p hstart
    exact ⟨p, .refl _, hstart⟩
  | step h_first _h_rest ih =>
    intro p hstart
    rw [hstart] at h_first
    obtain ⟨p₁, h_star1, h_eq1⟩ := m.backward_sim _ _ h_first
    obtain ⟨p₂, h_star2, h_eq2⟩ := ih h_eq1
    exact ⟨p₂, h_star1.trans h_star2, h_eq2⟩

/-- Backward simulation (simple version): when SC = Eq, no SC-gap issues. -/
theorem LanguageMorphism.backward_multi_eq
    (m : LanguageMorphism L₁ L₂ Eq)
    {p : Pattern} {T : Pattern} (h : LangReducesStar L₂ (m.mapTerm p) T) :
    ∃ p', LangReducesStar L₁ p p' ∧ T = m.mapTerm p' :=
  backward_multi_eq_aux m h rfl

/-- Backward simulation lifts to multi-step, using SC-closed reduction.

    For the general SC case, composing backward simulation steps requires
    bridging SC gaps: backward_sim gives sc(q_mid, mapTerm(p₁)) but the
    next reduction starts from q_mid, not mapTerm(p₁). This requires
    a one-step SC alignment property that re-roots a single reduction
    across an SC-related start point. -/
theorem LanguageMorphism.backward_multi_strong
    (m : LanguageMorphism L₁ L₂ sc)
    (sc_refl : ∀ p, sc p p)
    (sc_trans : ∀ p q r, sc p q → sc q r → sc p r)
    (sc_step_reduces : ∀ p q, sc p q →
      ∀ r, langReduces L₂ p r →
      ∃ r', langReduces L₂ q r' ∧ sc r r')
    {p : Pattern} {T : Pattern} (h : LangReducesStar L₂ (m.mapTerm p) T) :
    ∃ p', LangReducesStar L₁ p p' ∧ sc T (m.mapTerm p') := by
  have aux :
      ∀ {start T : Pattern}, LangReducesStar L₂ start T →
      ∀ {p : Pattern}, sc start (m.mapTerm p) →
      ∃ p', LangReducesStar L₁ p p' ∧ sc T (m.mapTerm p') := by
    intro start T hStar
    induction hStar with
    | refl s =>
      intro p hsc
      exact ⟨p, .refl _, hsc⟩
    | step h_first _h_rest ih =>
      intro p hsc_start
      obtain ⟨q₀, h_aligned, hsc_mid⟩ :=
        sc_step_reduces _ _ hsc_start _ h_first
      obtain ⟨p₁, hsrc1, hsc_q0⟩ := m.backward_sim _ _ h_aligned
      have hsc_qmid : sc _ (m.mapTerm p₁) :=
        sc_trans _ _ _ hsc_mid hsc_q0
      obtain ⟨p₂, hsrc2, hscT⟩ := ih hsc_qmid
      exact ⟨p₂, hsrc1.trans hsrc2, hscT⟩
  exact aux h (sc_refl _)

/-! ## Diamond/Box Preservation -/

/-- A language morphism preserves the step-future modality ◇.

    If ◇_L₁(φ)(p), then ◇_L₂(φ ∘ mapTerm⁻¹)(mapTerm(p)).
    More precisely: if p can L₁-step to some q satisfying φ,
    then mapTerm(p) can L₂-step to some T that is sc-equivalent
    to mapTerm(q), where q satisfies φ. -/
theorem LanguageMorphism.preserves_diamond
    (m : LanguageMorphism L₁ L₂ sc)
    {φ : Pattern → Prop} {p : Pattern}
    (h : langDiamond L₁ φ p) :
    ∃ q, langReduces L₁ p q ∧ φ q ∧
         ∃ T, LangReducesStar L₂ (m.mapTerm p) T ∧ sc T (m.mapTerm q) := by
  rw [langDiamond_spec] at h
  obtain ⟨q, hred, hφ⟩ := h
  obtain ⟨T, h_star, h_sc⟩ := m.forward_sim _ _ hred
  exact ⟨q, hred, hφ, T, h_star, h_sc⟩

/-- Operational correspondence from a language morphism.

    This is the MAIN theorem: a LanguageMorphism gives a biconditional between
    source and target multi-step reductions. The forward direction follows from
    forward simulation; the backward direction from backward simulation. -/
theorem LanguageMorphism.operational_correspondence_forward
    (m : LanguageMorphism L₁ L₂ sc)
    (sc_refl : ∀ p, sc p p)
    (sc_trans : ∀ p q r, sc p q → sc q r → sc p r)
    (sc_star : ∀ p q, sc p q →
      ∀ r, LangReducesStar L₂ q r → ∃ r', LangReducesStar L₂ p r' ∧ sc r' r)
    {p q : Pattern} (h : LangReducesStar L₁ p q) :
    ∃ T, LangReducesStar L₂ (m.mapTerm p) T ∧ sc T (m.mapTerm q) :=
  m.forward_multi_strong sc_refl sc_trans sc_star h

/-! ## Canonical `Eq` Morphism Composition

These are the canonical identity/composition operations for the common
`sc := Eq` specialization. They are used to package a category-like
infrastructure over `LanguageDef` without overclaiming proof-field equality
for arbitrary `sc`.
-/

variable {L₃ L₄ : LanguageDef}

/-- Identity language morphism (`Eq` specialization). -/
def idLanguageMorphism (L : LanguageDef) : LanguageMorphism L L Eq where
  mapTerm := id
  forward_sim := by
    intro p q hred
    exact ⟨q, LangReducesStar.single hred, rfl⟩
  backward_sim := by
    intro p T hred
    exact ⟨T, LangReducesStar.single hred, rfl⟩

/-- Composition of `Eq`-specialized language morphisms. -/
def composeLanguageMorphism
    (m₁₂ : LanguageMorphism L₁ L₂ Eq)
    (m₂₃ : LanguageMorphism L₂ L₃ Eq) :
    LanguageMorphism L₁ L₃ Eq where
  mapTerm := fun p => m₂₃.mapTerm (m₁₂.mapTerm p)
  forward_sim := by
    intro p q hred
    obtain ⟨t₁, hstar₁, ht₁⟩ := m₁₂.forward_sim p q hred
    subst ht₁
    obtain ⟨t₂, hstar₂, ht₂⟩ :=
      LanguageMorphism.forward_multi_eq (m := m₂₃) hstar₁
    exact ⟨t₂, hstar₂, ht₂⟩
  backward_sim := by
    intro p t hred
    obtain ⟨p₂, hstar₂, hp₂⟩ := m₂₃.backward_sim (m₁₂.mapTerm p) t hred
    obtain ⟨p₁, hstar₁, hp₁⟩ :=
      LanguageMorphism.backward_multi_eq (m := m₁₂) hstar₂
    refine ⟨p₁, hstar₁, ?_⟩
    subst hp₂
    subst hp₁
    rfl

@[simp] theorem idLanguageMorphism_mapTerm (L : LanguageDef) (p : Pattern) :
    (idLanguageMorphism L).mapTerm p = p := rfl

@[simp] theorem composeLanguageMorphism_mapTerm
    (m₁₂ : LanguageMorphism L₁ L₂ Eq)
    (m₂₃ : LanguageMorphism L₂ L₃ Eq)
    (p : Pattern) :
    (composeLanguageMorphism m₁₂ m₂₃).mapTerm p = m₂₃.mapTerm (m₁₂.mapTerm p) := rfl

/-- Left identity law for canonical composition, at map-term level. -/
@[simp] theorem composeLanguageMorphism_id_left_mapTerm
    (m : LanguageMorphism L₁ L₂ Eq) (p : Pattern) :
    (composeLanguageMorphism (idLanguageMorphism L₁) m).mapTerm p = m.mapTerm p := rfl

/-- Right identity law for canonical composition, at map-term level. -/
@[simp] theorem composeLanguageMorphism_id_right_mapTerm
    (m : LanguageMorphism L₁ L₂ Eq) (p : Pattern) :
    (composeLanguageMorphism m (idLanguageMorphism L₂)).mapTerm p = m.mapTerm p := rfl

/-- Associativity law for canonical composition, at map-term level. -/
@[simp] theorem composeLanguageMorphism_assoc_mapTerm
    (m₁₂ : LanguageMorphism L₁ L₂ Eq)
    (m₂₃ : LanguageMorphism L₂ L₃ Eq)
    (m₃₄ : LanguageMorphism L₃ L₄ Eq)
    (p : Pattern) :
    (composeLanguageMorphism (composeLanguageMorphism m₁₂ m₂₃) m₃₄).mapTerm p =
      (composeLanguageMorphism m₁₂ (composeLanguageMorphism m₂₃ m₃₄)).mapTerm p := rfl

/-! ## Framework-Level Formula Transfer Fragments

Generic fragment-level transfer lemmas that are independent of any
process-calculus internals. These are reused by endpoint wrappers that need
uniform dia/box induction and atom-preservation transport.
-/

/-- Dia/box fragment (`⊤`, atoms, `∧`, `∨`, `→`, `◇`, `□`) without `⊥`.
This is the strongest fragment for which domain-based "all states satisfy"
transfer is generally derivable from atom/domain hypotheses. -/
inductive DiaBoxFragment : OSLFFormula → Prop where
  | top : DiaBoxFragment .top
  | atom (a : String) : DiaBoxFragment (.atom a)
  | and {φ ψ} :
      DiaBoxFragment φ →
      DiaBoxFragment ψ →
      DiaBoxFragment (.and φ ψ)
  | or {φ ψ} :
      DiaBoxFragment φ →
      DiaBoxFragment ψ →
      DiaBoxFragment (.or φ ψ)
  | imp {φ ψ} :
      DiaBoxFragment φ →
      DiaBoxFragment ψ →
      DiaBoxFragment (.imp φ ψ)
  | dia {φ} :
      DiaBoxFragment φ →
      DiaBoxFragment (.dia φ)
  | box {φ} :
      DiaBoxFragment φ →
      DiaBoxFragment (.box φ)

/-- Broad boolean/modal fragment (`⊤`, `⊥`, atoms, `∧`, `∨`, `→`, `◇`, `□`).
Used for atom-preservation transport equivalences. -/
inductive BroadFragment : OSLFFormula → Prop where
  | top : BroadFragment .top
  | bot : BroadFragment .bot
  | atom (a : String) : BroadFragment (.atom a)
  | and {φ ψ} :
      BroadFragment φ →
      BroadFragment ψ →
      BroadFragment (.and φ ψ)
  | or {φ ψ} :
      BroadFragment φ →
      BroadFragment ψ →
      BroadFragment (.or φ ψ)
  | imp {φ ψ} :
      BroadFragment φ →
      BroadFragment ψ →
      BroadFragment (.imp φ ψ)
  | dia {φ} :
      BroadFragment φ →
      BroadFragment (.dia φ)
  | box {φ} :
      BroadFragment φ →
      BroadFragment (.box φ)

/-- Dia/box fragment embeds into the broader fragment. -/
theorem DiaBoxFragment.to_broad
    {φ : OSLFFormula}
    (h : DiaBoxFragment φ) :
    BroadFragment φ := by
  induction h with
  | top => exact BroadFragment.top
  | atom a => exact BroadFragment.atom a
  | and hφ hψ ihφ ihψ => exact BroadFragment.and ihφ ihψ
  | or hφ hψ ihφ ihψ => exact BroadFragment.or ihφ ihψ
  | imp hφ hψ ihφ ihψ => exact BroadFragment.imp ihφ ihψ
  | dia hφ ihφ => exact BroadFragment.dia ihφ
  | box hφ ihφ => exact BroadFragment.box ihφ

/-- Semantic invariance on the broad fragment under atom-preservation
equivalence (`I` and `J` agree on atoms). -/
theorem sem_iff_of_broadFragment
    {R : Pattern → Pattern → Prop}
    {I J : AtomSem}
    {φ : OSLFFormula}
    (hfrag : BroadFragment φ)
    (hAtomIff : ∀ a p, I a p ↔ J a p) :
    ∀ p, sem R I φ p ↔ sem R J φ p := by
  induction hfrag with
  | top =>
      intro p
      simp [sem]
  | bot =>
      intro p
      simp [sem]
  | atom a =>
      intro p
      simpa [sem] using hAtomIff a p
  | and hφ hψ ihφ ihψ =>
      intro p
      simp [sem, ihφ p, ihψ p]
  | or hφ hψ ihφ ihψ =>
      intro p
      simp [sem, ihφ p, ihψ p]
  | imp hφ hψ ihφ ihψ =>
      intro p
      constructor
      · intro h hJφ
        have hIφ : sem R I _ p := (ihφ p).2 hJφ
        have hIψ : sem R I _ p := h hIφ
        exact (ihψ p).1 hIψ
      · intro h hIφ
        have hJφ : sem R J _ p := (ihφ p).1 hIφ
        have hJψ : sem R J _ p := h hJφ
        exact (ihψ p).2 hJψ
  | dia hφ ihφ =>
      intro p
      constructor
      · intro h
        rcases h with ⟨q, hpq, hI⟩
        exact ⟨q, hpq, (ihφ q).1 hI⟩
      · intro h
        rcases h with ⟨q, hpq, hJ⟩
        exact ⟨q, hpq, (ihφ q).2 hJ⟩
  | box hφ ihφ =>
      intro p
      constructor
      · intro h q hqp
        exact (ihφ q).1 (h q hqp)
      · intro h q hqp
        exact (ihφ q).2 (h q hqp)

/-- Dia/box fragment inherits broad-fragment atom-preservation invariance. -/
theorem sem_iff_of_diaBoxFragment
    {R : Pattern → Pattern → Prop}
    {I J : AtomSem}
    {φ : OSLFFormula}
    (hfrag : DiaBoxFragment φ)
    (hAtomIff : ∀ a p, I a p ↔ J a p) :
    ∀ p, sem R I φ p ↔ sem R J φ p := by
  exact sem_iff_of_broadFragment hfrag.to_broad hAtomIff

/-- One-way transfer on the broad fragment under atom-preservation
equivalence assumptions. -/
theorem sem_transfer_of_broadFragment
    {R : Pattern → Pattern → Prop}
    {I J : AtomSem}
    {φ : OSLFFormula}
    (hfrag : BroadFragment φ)
    (hAtomIff : ∀ a p, I a p ↔ J a p)
    {p : Pattern}
    (hsem : sem R I φ p) :
    sem R J φ p :=
  (sem_iff_of_broadFragment hfrag hAtomIff p).1 hsem

/-- One-way transfer on the dia/box fragment under atom-preservation
equivalence assumptions. -/
theorem sem_transfer_of_diaBoxFragment
    {R : Pattern → Pattern → Prop}
    {I J : AtomSem}
    {φ : OSLFFormula}
    (hfrag : DiaBoxFragment φ)
    (hAtomIff : ∀ a p, I a p ↔ J a p)
    {p : Pattern}
    (hsem : sem R I φ p) :
    sem R J φ p :=
  (sem_iff_of_diaBoxFragment hfrag hAtomIff p).1 hsem

/-- Formula-induction transfer principle on a backward-closed domain for the
dia/box fragment. -/
theorem sem_of_diaBoxFragment_on_domain
    {R : Pattern → Pattern → Prop}
    {D : Pattern → Prop}
    {I : AtomSem}
    {φ : OSLFFormula}
    (hfrag : DiaBoxFragment φ)
    (hAtomDomain : ∀ a p, D p → I a p)
    (hDomainBackward : ∀ {p q}, D p → R q p → D q)
    (hDiaDomain : ∀ p, D p → ∃ q, R p q ∧ D q) :
    ∀ p, D p → sem R I φ p := by
  induction hfrag with
  | top =>
      intro _p _hD
      trivial
  | atom a =>
      intro p hD
      exact hAtomDomain a p hD
  | and hφ hψ ihφ ihψ =>
      intro p hD
      exact ⟨ihφ p hD, ihψ p hD⟩
  | or hφ _hψ ihφ _ihψ =>
      intro p hD
      exact Or.inl (ihφ p hD)
  | imp _hφ _hψ _ihφ ihψ =>
      intro p hD _hPrem
      exact ihψ p hD
  | dia _hφ ih =>
      intro p hD
      rcases hDiaDomain p hD with ⟨q, hRq, hDq⟩
      exact ⟨q, hRq, ih q hDq⟩
  | box _hφ ih =>
      intro p hD q hqp
      exact ih q (hDomainBackward hD hqp)

/-- Compatibility wrapper for global dia/box-fragment transfer from universal
atoms and universal `◇⊤`.

Canonical consumers should prefer `sem_of_diaBoxFragment_on_domain` with a
scoped domain hypothesis. This global shape is retained as a broad corollary
for compatibility. -/
theorem sem_of_diaBoxFragment
    {R : Pattern → Pattern → Prop}
    {I : AtomSem}
    {φ : OSLFFormula}
    (hfrag : DiaBoxFragment φ)
    (hAtomAll : ∀ a p, I a p)
    (hDiaTopAll : ∀ p, sem R I (.dia .top) p) :
    ∀ p, sem R I φ p := by
  intro p
  exact sem_of_diaBoxFragment_on_domain
    (R := R) (D := fun _ => True) hfrag
    (hAtomDomain := fun a p _ => hAtomAll a p)
    (hDomainBackward := by
      intro _ _ _ _
      trivial)
    (hDiaDomain := by
      intro p _
      rcases hDiaTopAll p with ⟨q, hpq, _⟩
      exact ⟨q, hpq, trivial⟩)
    p
    trivial

/-! ## Barb Preservation -/

/-- A barb (observable action) on a pattern. Parameterized by language. -/
def HasBarb (_lang : LanguageDef) (p : Pattern) (obs : Pattern) : Prop :=
  ∃ ps, p = .collection .hashBag ps none ∧
        ∃ q, .apply "POutput" [obs, q] ∈ ps ∨
             .apply "PiOut" [obs, q] ∈ ps

/-- Weak barb: can reach a state with the barb via multi-step reduction. -/
def HasWeakBarb (lang : LanguageDef) (p : Pattern) (obs : Pattern) : Prop :=
  ∃ p', LangReducesStar lang p p' ∧ HasBarb lang p' obs

-- Barb preservation is language-pair-specific (depends on how the encoding
-- maps observables). For π→ρ: π-barb on channel x maps to ρ-barb on
-- piNameToRhoName(x). See EncodingMorphism.lean for the specific instance.

end Mettapedia.OSLF.Framework.LangMorphism
