import Mettapedia.ProbabilityTheory.WeightedInference
import Mettapedia.Logic.RandomClosure.DistributionalEvidence
import Mettapedia.Logic.WorldModel.DistributionalSpaceExecution
import Mettapedia.GSLT.Dynamics.WeightedLinearInterpretation
import Mettapedia.GSLT.Dynamics.ProbabilisticResumption

/-!
# Compositional finite inference handlers

This is a typed semantic language of finite stochastic algorithms, not a
text parser or a proof about a native random-number generator. Constructors
retain the target and discharge support obligations. Compilation constructs
the sampling law independently of the proper-weighting proof.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.Dynamics.WeightedInferenceHandlers
open Finset Mettapedia.InformationTheory Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.ProbabilityTheory.WeightedInference
open Mettapedia.Logic.DistributionalSpace

structure Experiment (S : Type) where
  Noise : Type
  finiteNoise : Fintype Noise
  law : @Prob Noise finiteNoise
  output : Noise → S
  weight : Noise → ℝ
attribute [instance] Experiment.finiteNoise

/-- There is no unchecked filtering or external-certificate constructor. -/
inductive Handler : {S : Type} → [Fintype S] → (S → ℝ) → Type 1 where
  | importance {S : Type} [Fintype S] (target : S → ℝ) (proposal : Prob S)
      (nonneg : ∀ s, 0 ≤ target s) (support : Covers proposal target) : Handler target
  | auxiliary {S A : Type} [Fintype S] [Fintype A] (target : S → ℝ)
      (proposal : Prob (S × A)) (backward : S → Prob A) (nonneg : ∀ s, 0 ≤ target s)
      (support : Covers proposal (fun sa => target sa.1 * (backward sa.1).1 sa.2)) : Handler target
  | adaptive {S H : Type} [Fintype S] [Fintype H] (target : S → ℝ)
      (history : Prob H) (proposal : H → Prob S) (nonneg : ∀ s, 0 ≤ target s)
      (support : ∀ h, Covers (proposal h) target) : Handler target
  | extend {S A : Type} [Fintype S] [Fintype A] {target : S → ℝ}
      (previous : Handler target) (proposal : S → Prob A) (factor : S → A → ℝ)
      (nonneg : ∀ s a, 0 ≤ factor s a) (support : ∀ s, Covers (proposal s) (factor s)) :
      Handler (fun sa : S × A => target sa.1 * factor sa.1 sa.2)

noncomputable def Handler.compile {S : Type} [Fintype S] {target : S → ℝ} : Handler target → Experiment S
  | @Handler.importance S _ γ q _ _ => ⟨S, inferInstance, q, id, fun s => γ s / q.1 s⟩
  | @Handler.auxiliary S A _ _ γ q r _ _ => ⟨S × A, inferInstance, q, Prod.fst,
      fun sa => γ sa.1 * (r sa.1).1 sa.2 / q.1 sa⟩
  | @Handler.adaptive S H _ _ γ past q _ _ => ⟨H × S, inferInstance, joint past q, Prod.snd,
      fun hs => γ hs.2 / (q hs.1).1 hs.2⟩
  | @Handler.extend S A _ _ γ old q factor _ _ =>
      let e := old.compile
      { Noise := e.Noise × A
        finiteNoise := inferInstance
        law := joint e.law (fun w => q (e.output w))
        output := fun wa => (e.output wa.1, wa.2)
        weight := fun wa => e.weight wa.1 * (factor (e.output wa.1) wa.2 / (q (e.output wa.1)).1 wa.2) }

/-- Fundamental theorem of the handler language. -/
theorem Handler.sound {S : Type} [Fintype S] {target : S → ℝ} (h : Handler target) :
    ProperlyWeighted h.compile.law h.compile.output h.compile.weight target := by
  induction h with
  | importance γ q hn hs => exact Mettapedia.ProbabilityTheory.WeightedInference.importance q γ hn hs
  | auxiliary γ q r hn hs => exact auxiliary_importance q γ r hn hs
  | adaptive γ past q hn hs => exact adaptive_importance past q γ hn hs
  | extend previous q factor hn hs ih => exact Mettapedia.ProbabilityTheory.WeightedInference.extend _ _ _ _ ih q factor hn hs

section Batches
variable {S I Ω : Type} [Fintype S] [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]

omit [Nonempty I] in
/-- The finite product probability already used by distributional models. -/
theorem product_coordinate (p : I → Prob Ω) (i : I) (f : Ω → ℝ) :
    expectation (independent p) (fun xs => f (xs i)) = expectation (p i) f := by
  classical
  have eq (xs : I → Ω) : (∏ j, (p j).1 (xs j)) * f (xs i) =
      ∏ j, (p j).1 (xs j) * (if j = i then f (xs j) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp
  unfold expectation
  change (∑ xs : I → Ω, (∏ j, (p j).1 (xs j)) * f (xs i)) = _
  simp_rw [eq]
  rw [← Fintype.prod_sum (fun j x => (p j).1 x * (if j = i then f x else 1))]
  have inner (j : I) : (∑ x, (p j).1 x * (if j = i then f x else 1)) =
      if j = i then expectation (p i) f else 1 := by
    by_cases h : j = i
    · subst j; simp [expectation]
    · simp [h, (p j).2.2]
  simp_rw [inner]
  simp [expectation]

theorem independent_batch {target : S → ℝ} (h : Handler target) :
    ProperBatch (independent (fun _ : I => h.compile.law))
      (fun xs i => h.compile.output (xs i)) (fun xs i => h.compile.weight (xs i)) target := by
  apply properBatch_of_members
  intro i
  refine ⟨fun xs => h.sound.nonnegative _, ?_⟩
  intro f
  rw [product_coordinate (fun _ : I => h.compile.law) i
    (fun w => h.compile.weight w * f (h.compile.output w))]
  exact h.sound.integral f

/-- One multinomial parent draw; zero total leaves zero offspring weight. -/
noncomputable def parentLaw (w : I → ℝ) (hn : ∀ i, 0 ≤ w i) : Prob I :=
  if h : 0 < ∑ i, w i then
    ⟨fun i => w i / ∑ j, w j, fun i => div_nonneg (hn i) h.le, by
      rw [← Finset.sum_div, div_self h.ne']⟩
  else Prob.dirac (Classical.choice (inferInstance : Nonempty I))

omit [Fintype S] in
/-- A concrete multinomial resampler keeps the batch mean weight, including
all-zero batches. Its offspring coordinates are sampled independently. -/
theorem multinomial_conditional (z : I → S) (w : I → ℝ) (hn : ∀ i, 0 ≤ w i) (f : S → ℝ) :
    expectation (independent (fun _ : I => parentLaw w hn))
      (fun draws => (∑ j, ((∑ i, w i) / Fintype.card I) * f (z (draws j))) / Fintype.card I) =
      (∑ i, w i * f (z i)) / Fintype.card I := by
  classical
  have nc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := I)
  have one (j : I) : expectation (independent (fun _ : I => parentLaw w hn))
      (fun draws => ((∑ i, w i) / Fintype.card I) * f (z (draws j))) =
      (∑ i, w i * f (z i)) / Fintype.card I := by
    rw [product_coordinate (fun _ : I => parentLaw w hn) j
      (fun i => ((∑ i, w i) / Fintype.card I) * f (z i))]
    by_cases hp : 0 < ∑ i, w i
    · simp only [parentLaw, dif_pos hp, expectation]
      conv_rhs => rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hp.ne']
    · have hz : ∑ i, w i = 0 := le_antisymm (le_of_not_gt hp) (Finset.sum_nonneg (fun i _ => hn i))
      have each (i : I) : w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp hz i (mem_univ i)
      simp [expectation, each]
  unfold expectation at one ⊢
  simp only [← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [one]
  simp [nc]

/-- Actual resampling of a random batch. The old random outcome is retained
in the joint law, so the new labels and weights have the correct dependence. -/
theorem multinomial_resampling (p : Prob Ω) (output : Ω → I → S) (weight : Ω → I → ℝ)
    (target : S → ℝ) (proper : ProperBatch p output weight target) :
    ProperBatch (joint p (fun ω => independent (fun _ : I => parentLaw (weight ω) (proper.nonnegative ω))))
      (fun wd i => output wd.1 (wd.2 i))
      (fun wd _ => (∑ i, weight wd.1 i) / Fintype.card I) target where
  positive_size := proper.positive_size
  nonnegative wd _ := div_nonneg (Finset.sum_nonneg (fun i _ => proper.nonnegative wd.1 i)) (by positivity)
  integral f := by
    unfold expectation batchEstimate
    simp only [Fintype.sum_prod_type, joint_apply, mul_assoc, ← Finset.mul_sum]
    have h (ω : Ω) := multinomial_conditional (output ω) (weight ω) (proper.nonnegative ω) f
    simp only [expectation, ← Finset.mul_sum] at h
    simp_rw [h]
    exact proper.integral f

variable {A J : Type} [Fintype A] [Fintype J] [DecidableEq J] [Nonempty J]

omit [Nonempty I] [Nonempty J] in
/-- Each pair has the product marginal although the complete pair population
shares rows and columns and is not an independent sample population. -/
theorem pair_coordinate (p : Prob S) (q : Prob A) (i : I) (j : J) (f : S × A → ℝ) :
    expectation (joint (independent (fun _ : I => p)) (fun _ => independent (fun _ : J => q)))
      (fun ab => f (ab.1 i, ab.2 j)) = expectation (joint p (fun _ => q)) f := by
  unfold expectation
  simp only [Fintype.sum_prod_type, joint_apply, mul_assoc, ← Finset.mul_sum]
  have inner (a : I → S) := product_coordinate (fun _ : J => q) j (fun b => f (a i, b))
  simp only [expectation] at inner
  simp_rw [inner]
  exact product_coordinate (fun _ : I => p) i (fun a => ∑ b, q.1 b * f (a,b))

theorem paired_batch (p : Prob S) (q : Prob A) (target : S × A → ℝ)
    (nonneg : ∀ sa, 0 ≤ target sa) (support : Covers (joint p (fun _ => q)) target) :
    ProperBatch (joint (independent (fun _ : I => p)) (fun _ => independent (fun _ : J => q)))
      (fun ab (ij : I × J) => (ab.1 ij.1, ab.2 ij.2))
      (fun ab (ij : I × J) => target (ab.1 ij.1, ab.2 ij.2) / (p.1 (ab.1 ij.1) * q.1 (ab.2 ij.2))) target := by
  apply properBatch_of_members
  intro ij
  refine ⟨fun ab => div_nonneg (nonneg _) (mul_nonneg (p.2.1 _) (q.2.1 _)), ?_⟩
  intro f
  rw [pair_coordinate p q ij.1 ij.2 (fun sa => target sa / (p.1 sa.1 * q.1 sa.2) * f sa)]
  exact (pair_importance p q target nonneg support).integral f

theorem paired_joined_batch {T : Type} [Fintype T] [DecidableEq T]
    (p : Prob S) (q : Prob A) (join : S × A → Option T) (split : T → S × A)
    (roundtrip : ∀ t, join (split t) = some t)
    (unique : ∀ sa t, join sa = some t → sa = split t)
    (target : T → ℝ) (nonneg : ∀ t, 0 ≤ target t)
    (support : Covers (joint p (fun _ => q)) (joinTarget join target)) :
    ProperBatch (joint (independent (fun _ : I => p)) (fun _ => independent (fun _ : J => q)))
      (fun ab (ij : I × J) => join (ab.1 ij.1, ab.2 ij.2))
      (fun ab (ij : I × J) => joinTarget join target (ab.1 ij.1, ab.2 ij.2) /
        (p.1 (ab.1 ij.1) * q.1 (ab.2 ij.2)))
      (fun t => match t with | none => 0 | some z => target z) := by
  have hn (sa : S × A) : 0 ≤ joinTarget join target sa := by
    unfold joinTarget; cases join sa <;> simp_all
  have h := (paired_batch (I := I) (J := J) p q (joinTarget join target) hn support).map join
  rw [joinTarget_pushforward join split roundtrip unique] at h
  convert h using 1
  congr 2

end Batches


structure BatchExperiment (S I : Type) where
  Noise : Type
  finiteNoise : Fintype Noise
  law : @Prob Noise finiteNoise
  output : Noise → I → S
  weight : Noise → I → ℝ
  nonnegative : ∀ w i, 0 ≤ weight w i
attribute [instance] BatchExperiment.finiteNoise

/-- Batch construction, resampling and all-pairs joining are explicit
operations. A join retains the original pair cardinality, including failures. -/
inductive BatchHandler : {S I : Type} → [Fintype S] → [Fintype I] → [DecidableEq I] →
    [Nonempty I] → (S → ℝ) → Type 1 where
  | draw {S I : Type} [Fintype S] [Fintype I] [DecidableEq I] [Nonempty I]
      {target : S → ℝ} (sampler : Handler target) : BatchHandler (I := I) target
  | resample {S I : Type} [Fintype S] [Fintype I] [DecidableEq I] [Nonempty I]
      {target : S → ℝ} (previous : BatchHandler (I := I) target) : BatchHandler (I := I) target
  | paired (A B T J K : Type) [Fintype A] [Fintype B] [Fintype T] [Fintype J] [Fintype K]
      [DecidableEq T] [DecidableEq J] [DecidableEq K] [Nonempty J] [Nonempty K]
      (p : Prob A) (q : Prob B) (join : A × B → Option T) (split : T → A × B)
      (roundtrip : ∀ t, join (split t) = some t)
      (unique : ∀ ab t, join ab = some t → ab = split t)
      (target : T → ℝ) (nonneg : ∀ t, 0 ≤ target t)
      (support : Covers (joint p (fun _ => q)) (joinTarget join target)) :
      BatchHandler (I := J × K) (fun t => match t with | none => 0 | some z => target z)

noncomputable def BatchHandler.compile {S I : Type} [Fintype S] [Fintype I] [DecidableEq I] [Nonempty I]
    {target : S → ℝ} : BatchHandler (I := I) target → BatchExperiment S I
  | @BatchHandler.draw S I fs fi di ni _ h =>
    letI : Fintype S := fs
    letI : Fintype I := fi
    letI : DecidableEq I := di
    letI : Nonempty I := ni
    { Noise := I → h.compile.Noise
      finiteNoise := inferInstance
      law := independent (fun _ : I => h.compile.law)
      output := fun xs i => h.compile.output (xs i)
      weight := fun xs i => h.compile.weight (xs i)
      nonnegative := fun xs i => h.sound.nonnegative (xs i) }
  | @BatchHandler.resample S I fs fi di ni _ previous =>
    letI : Fintype S := fs
    letI : Fintype I := fi
    letI : DecidableEq I := di
    letI : Nonempty I := ni
    let e := previous.compile
    { Noise := e.Noise × (I → I)
      finiteNoise := inferInstance
      law := joint e.law (fun ω => independent (fun _ : I => parentLaw (e.weight ω) (e.nonnegative ω)))
      output := fun wd i => e.output wd.1 (wd.2 i)
      weight := fun wd _ => (∑ i, e.weight wd.1 i) / Fintype.card I
      nonnegative := fun wd _ => div_nonneg (Finset.sum_nonneg (fun i _ => e.nonnegative wd.1 i)) (by positivity) }
  | @BatchHandler.paired A B _ J K fa fb _ fj fk _ dj dk _ _ p q join _ _ _ target nonneg _ =>
    letI : Fintype A := fa
    letI : Fintype B := fb
    letI : Fintype J := fj
    letI : Fintype K := fk
    letI : DecidableEq J := dj
    letI : DecidableEq K := dk
    { Noise := (J → A) × (K → B)
      finiteNoise := inferInstance
      law := joint (independent (fun _ : J => p)) (fun _ => independent (fun _ : K => q))
      output := fun ab ij => join (ab.1 ij.1, ab.2 ij.2)
      weight := fun ab ij => joinTarget join target (ab.1 ij.1, ab.2 ij.2) /
        (p.1 (ab.1 ij.1) * q.1 (ab.2 ij.2))
      nonnegative := by
        intro ab ij
        apply div_nonneg _ (mul_nonneg (p.2.1 _) (q.2.1 _))
        unfold joinTarget
        cases join (ab.1 ij.1, ab.2 ij.2) <;> simp_all }

/-- The certificate covers the whole returned batch, including joins and
resampling after joins. It gives no independent-sample variance formula. -/
theorem BatchHandler.sound {S I : Type} [Fintype S] [Fintype I] [DecidableEq I] [Nonempty I]
    {target : S → ℝ} (h : BatchHandler (I := I) target) :
    ProperBatch h.compile.law h.compile.output h.compile.weight target := by
  induction h with
  | @draw S I _ _ _ _ target sampler => exact independent_batch (I := I) sampler
  | resample previous ih => exact multinomial_resampling _ _ _ _ ih
  | paired A B T J K p q join split roundtrip unique target nonneg support =>
    exact paired_joined_batch (I := J) (J := K) p q join split roundtrip unique target nonneg support


section WorldModels
variable {Θ Ω O Id : Type} [Fintype Ω] [Fintype O]

/-- The certified target is the unnormalized mass of the independently
constructed world model, so posterior normalization is downstream. -/
theorem space_importance (m : Model Θ Ω O Id) (θ : Θ) (E : Finset Id) (proposal : Prob Ω)
    (support : Covers proposal (fun w => (m.prior θ).1 w * m.likelihood θ E w)) :
    ProperlyWeighted proposal id
      (fun w => (m.prior θ).1 w * m.likelihood θ E w / proposal.1 w)
      (fun w => (m.prior θ).1 w * m.likelihood θ E w) :=
  importance proposal _ (fun w => mul_nonneg ((m.prior θ).2.1 w) (m.likelihood_nonneg θ E w)) support

/-- Exact querying is the ratio of expected unnormalized masses, not the
expectation of the ratio of two finite Monte Carlo estimates. -/
theorem space_query_contract (m : Model Θ Ω O Id) (θ : Θ) (E : Finset Id)
    (h : Handler (fun w => (m.prior θ).1 w * m.likelihood θ E w)) (event : Ω → Bool) :
    m.probability? θ E event =
      if 0 < expectation h.compile.law h.compile.weight then
        some (expectation h.compile.law (fun u =>
          h.compile.weight u * if event (h.compile.output u) then 1 else 0) /
            expectation h.compile.law h.compile.weight)
      else none := by
  rw [h.sound.normalizer, h.sound.integral (fun w => if event w then 1 else 0), Model.probability?_formula]
  simp only [Model.normalizer, evidence, mul_ite, mul_one, mul_zero]

/-- Observation identities partition the catalogue; the probability product
comes from the constructed independent blocks, never from distinct IDs. -/
theorem owned_block_importance {J Y : Type} [Fintype J] [DecidableEq J] [Fintype Y]
    (prior : Prob Ω) (channels : Ω → J → Prob Y) (owner : Id → J) (test : Id → Y → Bool)
    (E : Finset Id) (proposal : Prob Ω)
    (support : Covers proposal (fun w => prior.1 w *
      ∏ j, Mettapedia.Logic.RandomClosure.DistributionalEvidence.blockLikelihood
        (channels w j) owner test E j)) :
    ProperlyWeighted proposal id
      (fun w => prior.1 w *
        (∏ j, Mettapedia.Logic.RandomClosure.DistributionalEvidence.blockLikelihood
          (channels w j) owner test E j) / proposal.1 w)
      (fun w => prior.1 w *
        ∏ j, Mettapedia.Logic.RandomClosure.DistributionalEvidence.blockLikelihood
          (channels w j) owner test E j) := by
  let model := Mettapedia.Logic.RandomClosure.DistributionalEvidence.ownedModel prior channels owner test
  have mass (w : Ω) : (model.prior ()).1 w * model.likelihood () E w = prior.1 w *
      ∏ j, Mettapedia.Logic.RandomClosure.DistributionalEvidence.blockLikelihood
        (channels w j) owner test E j := by
    change prior.1 w *
      (Mettapedia.Logic.RandomClosure.DistributionalEvidence.ownedModel prior channels owner test).likelihood () E w = _
    rw [Mettapedia.Logic.RandomClosure.DistributionalEvidence.owned_likelihood]
  have h := space_importance model () E proposal (by
    intro w hw
    apply support w
    dsimp only at hw ⊢
    rwa [← mass w])
  simpa only [mass] using h

/-- Likelihood scale cancels from the posterior but not the evidence. -/
theorem scale_boundary (prior : Prob Ω) (L : Ω → ℝ) (hn : ∀ w, 0 ≤ L w)
    (hz : 0 < evidence prior L) (c : ℝ) (hc : 0 < c) :
    posterior prior (fun w => c * L w) (fun w => mul_nonneg hc.le (hn w))
      (by rw [evidence_scale]; exact mul_pos hc hz) = posterior prior L hn hz ∧
    evidence prior (fun w => c * L w) = c * evidence prior L :=
  ⟨posterior_scale prior L hn hz c hc, evidence_scale prior L c⟩

inductive Purpose where
  | inference
  | control
  deriving DecidableEq

/-- Exact source data are retained; a hash is not the semantic identity. -/
structure Request (Θ Ω O Id : Type) [Fintype Ω] [Fintype O] where
  model : Model Θ Ω O Id
  parameter : Θ
  evidence : Finset Id
  proposal : Prob Ω
  purpose : Purpose

noncomputable def Request.target (r : Request Θ Ω O Id) (w : Ω) : ℝ :=
  (r.model.prior r.parameter).1 w * r.model.likelihood r.parameter r.evidence w

/-- A declaration is retained as an unresolved claim, never as a support proof. -/
inductive CoverageClaim (r : Request Θ Ω O Id) where
  | verified (support : Covers r.proposal r.target)
  | declared

noncomputable def Request.admit (r : Request Θ Ω O Id) : CoverageClaim r → Option (Handler r.target)
  | .verified support => some (.importance r.target r.proposal
      (fun w => mul_nonneg ((r.model.prior r.parameter).2.1 w)
        (r.model.likelihood_nonneg r.parameter r.evidence w)) support)
  | .declared => none

theorem declared_not_certified (r : Request Θ Ω O Id) : r.admit .declared = none := rfl

/-- Guidance changes a proposal, leaving the declared target unchanged. -/
theorem change_proposal_target (r : Request Θ Ω O Id) (p : Prob Ω) :
    ({r with proposal := p}).target = r.target := rfl

/-- A control result remains marked as control through proposal replacement. -/
theorem guidance_preserves_purpose (r : Request Θ Ω O Id) (p : Prob Ω) :
    ({r with proposal := p}).purpose = r.purpose := rfl

end WorldModels

section FactorTables
open Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable
open Mettapedia.Logic.WorldModel.DistributionalSpaceExecution
variable {n : Nat} {Id : Type} [DecidableEq Id]

/-- A frozen finite factor graph is a concrete consumer. The existing exact
variable-elimination machine and the checked sampling program serve the same
query; only the latter's unnormalized estimators have unbiasedness guarantees. -/
theorem factor_table_query_contract (domains : Fin n → Nat) (positive : ∀ v, 0 < domains v)
    (c : Context Id domains)
    (nonneg : ∀ x, 0 ≤ (combineAll domains positive c.tables).value domains positive x)
    (normalized : ∑ x : Config domains,
      (combineAll domains positive c.tables).value domains positive x = 1)
    (log : List Id) (q : List (Constraint domains))
    (h : Handler (fun x => ((c.space domains positive nonneg normalized).prior ()).1 x *
      (c.space domains positive nonneg normalized).likelihood () log.toFinset x)) :
    (c.evaluate domains positive log q).map (fun r => (r : ℝ)) =
      if 0 < expectation h.compile.law h.compile.weight then
        some (expectation h.compile.law (fun u => h.compile.weight u *
          if satisfies domains q (h.compile.output u) then 1 else 0) /
            expectation h.compile.law h.compile.weight)
      else none := by
  classical
  rw [c.evaluate_correct domains positive, c.answer_eq_space domains positive nonneg normalized]
  simpa only [decide_eq_true_eq] using
    space_query_contract (c.space domains positive nonneg normalized) () log.toFinset h
      (fun x => decide (satisfies domains q x))

end FactorTables
end Mettapedia.GSLT.Dynamics.WeightedInferenceHandlers
