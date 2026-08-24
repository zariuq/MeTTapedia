import Mettapedia.GSLT.Meredith.GSLT
import Mettapedia.GSLT.Meredith.RhoExample

/-!
# Determinate images: the Milner corollary for MM → rho

Milner's *Functions as Processes* (INRIA RR-1154, 1990) encodes the
λ-calculus into π so that the image of every term lies in a sequential,
determinate fragment: the encoding makes no essential use of the target's
concurrency, and that is not a defect — it is the soundness of the encoding.
The same shape governs lowering Metamath (and MM0) checking into the
ρ-calculus: MM checking is an ordered, deterministic transition system, so a
correct lowering **must** land in the determinate fragment of ρ.  A lowering
whose image raced would leak target scheduling into verdicts — the compiler
bug, not a feature.

This file proves that discipline once, generically, against the project's
GSLT framework, and specializes it to the actual ρ GSLT
(`Meredith.RhoExample.rhoGSLT`):

* `Determinate` — Milner's determinacy (CCS ch. 11), up to the theory's
  equations: any two one-step reducts of a term are equated.
* `determinate_confluent` — determinacy gives confluence of multi-step
  reduction up to equations; `determinate_nf_unique` — normal forms are
  unique up to equations.  This is why a determinate checker has *a* verdict.
* `SequentialRealization` — the operational-correspondence interface a
  lowering must satisfy: it maps steps to steps, reflects every image step
  back to a source step (no junk: the target cannot invent behaviour), and
  respects equations.
* `image_locally_determinate` / `realization_multiStep` /
  `realization_multiStep_reflect` — a realization of a determinate source
  has a determinate image, and multi-step behaviour corresponds in both
  directions up to target equations.  Forward + backward correspondence is
  exactly the operational-correspondence format of the ρ literature.
* `rho_image_locally_determinate` — the specialization to `rhoGSLT`.  When
  the MM → ρ compiler exists, its source machine and lowering instantiate
  `Src` and `R`; this theorem is then the statement *"the MM image is
  determinate ρ"* — the fence against scheduler-dependent verdicts, and the
  precise sense in which MM checking exercises ρ's degenerate fragment
  (per-proof and per-match independence are the only concurrency MM affords;
  the declaration spine is order-rigid).

The realization interface deliberately does not ask for injectivity or
fullness: extra target *terms* are harmless; extra target *steps from image
points* are what `reflects_step` forbids, because they are where scheduling
could change an answer.
-/

namespace Mettapedia.GSLT.Meredith

open Mettapedia.GSLT

/-! ## Setoid conveniences -/

variable {S : GSLT}

theorem equiv_refl (S : GSLT) (t : S.Term) : S.Equiv t t :=
  S.equations.iseqv.refl t

theorem equiv_symm {t u : S.Term} (h : S.Equiv t u) : S.Equiv u t :=
  S.equations.iseqv.symm h

theorem equiv_trans {t u v : S.Term} (h₁ : S.Equiv t u) (h₂ : S.Equiv u v) :
    S.Equiv t v :=
  S.equations.iseqv.trans h₁ h₂

/-! ## Determinacy (Milner, CCS ch. 11, up to equations) -/

/-- A GSLT is determinate when any two one-step reducts of the same term are
equated by the theory.  For a checker this is the statement that the verdict
does not depend on scheduling. -/
def Determinate (S : GSLT) : Prop :=
  ∀ {t u v : S.Term}, S.Step t u → S.Step t v → S.Equiv u v

/-- Multi-step reduction transported along an equation on its source. -/
theorem multiStep_resp_left {t t' u : S.Term} (he : S.Equiv t t')
    (h : S.MultiStep t u) : ∃ u', S.MultiStep t' u' ∧ S.Equiv u u' := by
  induction h generalizing t' with
  | refl t => exact ⟨t', .refl t', he⟩
  | step hs _ ih =>
      obtain ⟨a', ha', hae⟩ := S.rewrites_resp_left he hs
      obtain ⟨u', hu', hue⟩ := ih hae
      exact ⟨u', .step ha' hu', hue⟩

/-- **Determinacy gives confluence up to equations.**  Two multi-step
reductions from one term extend to reducts the theory equates. -/
theorem determinate_confluent (hD : Determinate S) {t u v : S.Term}
    (hu : S.MultiStep t u) (hv : S.MultiStep t v) :
    ∃ u' v', S.MultiStep u u' ∧ S.MultiStep v v' ∧ S.Equiv u' v' := by
  induction hu generalizing v with
  | refl t => exact ⟨v, v, hv, .refl v, equiv_refl S v⟩
  | @step t a u hs hau ih =>
      cases hv with
      | refl => exact ⟨u, u, .refl u, .step hs hau, equiv_refl S u⟩
      | @step _ b v hs' hbv =>
          -- the two first steps are equated; transport the second path to `a`
          have hab : S.Equiv b a := equiv_symm (hD hs hs')
          obtain ⟨v₀, hav₀, hvv₀⟩ := multiStep_resp_left hab hbv
          obtain ⟨u', v₀', huu', hv₀v₀', he⟩ := ih hav₀
          obtain ⟨v', hvv', he'⟩ :=
            multiStep_resp_left (equiv_symm hvv₀) hv₀v₀'
          exact ⟨u', v', huu', hvv', equiv_trans he he'⟩

/-- From a normal form, multi-step reduction cannot move. -/
theorem multiStep_of_normalForm {u w : S.Term} (hnf : S.IsNormalForm u)
    (h : S.MultiStep u w) : w = u := by
  cases h with
  | refl => rfl
  | step hs _ => exact absurd ⟨_, hs⟩ hnf

/-- **Normal forms of a determinate theory are unique up to equations.**
The checker's verdict is well-defined. -/
theorem determinate_nf_unique (hD : Determinate S) {t u v : S.Term}
    (hu : S.MultiStep t u) (hv : S.MultiStep t v)
    (hnu : S.IsNormalForm u) (hnv : S.IsNormalForm v) : S.Equiv u v := by
  obtain ⟨u', v', huu', hvv', he⟩ := determinate_confluent hD hu hv
  rw [multiStep_of_normalForm hnu huu'] at he
  rw [multiStep_of_normalForm hnv hvv'] at he
  exact he

/-! ## Sequential realizations: the lowering interface -/

/-- A lowering of one GSLT into another that preserves and reflects one-step
behaviour up to the target's equations.  `reflects_step` is the load-bearing
clause: the target may not invent steps at image points, which is exactly
where a scheduler could otherwise change an answer. -/
structure SequentialRealization (Src Tgt : GSLT) where
  /-- The term translation. -/
  map : Src.Term → Tgt.Term
  /-- Equations are preserved. -/
  preserves_equiv : ∀ {t u : Src.Term}, Src.Equiv t u →
    Tgt.Equiv (map t) (map u)
  /-- Every source step is realized. -/
  preserves_step : ∀ {t u : Src.Term}, Src.Step t u →
    Tgt.Step (map t) (map u)
  /-- Every target step from an image point reflects a source step,
  up to target equations (no junk). -/
  reflects_step : ∀ {t : Src.Term} {u' : Tgt.Term},
    Tgt.Step (map t) u' → ∃ u, Src.Step t u ∧ Tgt.Equiv (map u) u'

namespace SequentialRealization

variable {Src Tgt : GSLT} (R : SequentialRealization Src Tgt)

/-- **The image of a determinate machine is locally determinate.**  Any two
target steps from an image point land in equated target terms. -/
theorem image_locally_determinate (hD : Determinate Src)
    {t : Src.Term} {u' v' : Tgt.Term}
    (hu : Tgt.Step (R.map t) u') (hv : Tgt.Step (R.map t) v') :
    Tgt.Equiv u' v' := by
  obtain ⟨u, hsu, heu⟩ := R.reflects_step hu
  obtain ⟨v, hsv, hev⟩ := R.reflects_step hv
  have h : Tgt.Equiv (R.map u) (R.map v) := R.preserves_equiv (hD hsu hsv)
  exact equiv_trans (equiv_symm heu) (equiv_trans h hev)

/-- Forward operational correspondence: multi-step source runs are realized
in the target. -/
theorem realization_multiStep {t u : Src.Term} (h : Src.MultiStep t u) :
    Tgt.MultiStep (R.map t) (R.map u) := by
  induction h with
  | refl t => exact .refl _
  | step hs _ ih => exact .step (R.preserves_step hs) ih

/-- Backward operational correspondence, up to target equations: every
multi-step target run from a point equated with an image point is the image
of a source run. -/
theorem realization_multiStep_reflect {w₀ w : Tgt.Term}
    (h : Tgt.MultiStep w₀ w) :
    ∀ {t : Src.Term}, Tgt.Equiv (R.map t) w₀ →
      ∃ u, Src.MultiStep t u ∧ Tgt.Equiv (R.map u) w := by
  induction h with
  | refl w₀ => exact fun {t} he => ⟨t, .refl t, he⟩
  | @step w₀ w₁ w hs _ ih =>
      intro t he
      obtain ⟨w₁', hw₁', he₁⟩ :=
        Tgt.rewrites_resp_left (equiv_symm he) hs
      obtain ⟨u₁, hsu₁, heu₁⟩ := R.reflects_step hw₁'
      obtain ⟨u, hu, heu⟩ := ih (equiv_trans heu₁ (equiv_symm he₁))
      exact ⟨u, .step hsu₁ hu, heu⟩

/-- The identity realization: the interface is inhabited (by the trivial
witness; a compiler supplies the interesting ones). -/
def id (S : GSLT) : SequentialRealization S S where
  map := fun t => t
  preserves_equiv := fun h => h
  preserves_step := fun h => h
  reflects_step := fun {_} {u'} h => ⟨u', h, equiv_refl S u'⟩

end SequentialRealization

/-! ## The ρ specialization -/

open RhoExample in
/-- **Determinacy of the MM image in ρ** (statement schema).  Once the
MM → ρ compiler exists, its source machine instantiates `Src` and its
lowering instantiates `R`; this theorem then says the compiled image lies in
the determinate fragment of the actual ρ GSLT: no two ρ steps from an image
point are distinguishable by the theory, so no ρ scheduling can change a
verdict.  This is the Milner λ→π discipline transported to MM → ρ, and the
formal fence against selling MM-on-ρ as more than a compiler-genericity
falsifier: the image provably does not exercise ρ's concurrency beyond
equation-invisible independence. -/
theorem rho_image_locally_determinate {Src : GSLT} (hD : Determinate Src)
    (R : SequentialRealization Src rhoGSLT)
    {t : Src.Term} {u' v' : rhoGSLT.Term}
    (hu : rhoGSLT.Step (R.map t) u') (hv : rhoGSLT.Step (R.map t) v') :
    rhoGSLT.Equiv u' v' :=
  R.image_locally_determinate hD hu hv

end Mettapedia.GSLT.Meredith
