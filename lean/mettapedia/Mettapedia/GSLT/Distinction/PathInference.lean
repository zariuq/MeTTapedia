import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy
import Mettapedia.Cybernetics.DistinctionCalculus.Completeness
import Mettapedia.Cybernetics.DistinctionCalculus.Examples

/-!
# The path-inference fragment of the distinction calculus as a GSLT

The distinction calculus derives upper bounds on observer distances from
authored edges, reflexivity, the unit bound, symmetry, capped triangle
composition and weakening (`Cybernetics.DistinctionCalculus.ProofSystem`).
Read as a GSLT, its terms are ordered lists of outstanding claims and one
rewrite replaces the first claim by the premises of one rule instance that
concludes it, the proof-search reading that
`GSLT.LanguageDef.CalculusAsLanguage` gives authored calculi.  The rules carry
rational side conditions (the capped sum of the triangle rule, the inequality
of weakening, the seed distance of an edge), so the GSLT is built over the
rule relation (`RuleInstance`), not as an authored five-field language
definition.

* **Adequacy** (`run_iff_derives`): a claim rewrites to the empty obligation
  list exactly when the existing declarative relation `Derives` derives it;
  hence exactly when some certificate is accepted by the existing checker
  (`run_iff_checked`), and, on a finite carrier, exactly when every metric
  tolerance extending the seed satisfies the bound (`run_iff_metric_valid`).
* **Controls.** The graded chain derives `0 ~ 2` at `2/5` by a run
  (`graded_run`); no run reaches the endpoint collapse at bound `0`
  (`graded_no_collapse_run`).  On the non-metric chain a run establishes
  distance `0` between endpoints that the seed puts at distance `1`
  (`chain_run_not_seed_truth`): a run certifies validity in every metric
  extension, not truth in the seed.
* **The fragment is infinitely branching** (`not_imageFinite`): weakening offers
  a premise for every smaller bound.  So the quantitative Hennessy–Milner
  theorem does not apply to the distinction calculus's own proof search
  without a finiteness restriction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction

open Mettapedia.GSLT

/-- Concatenating reflexive–transitive rewrite chains. -/
theorem multiStep_trans {S : GSLT} {first second third : S.Term}
    (firstSecond : S.MultiStep first second) (secondThird : S.MultiStep second third) :
    S.MultiStep first third := by
  induction firstSecond with
  | refl _ => exact secondThird
  | step head _ inductionHypothesis => exact .step head (inductionHypothesis secondThird)

namespace PathInference

open Mettapedia.Cybernetics.DistinctionCalculus

universe u

variable {V : Type u}

/-- One instance of a rule of the path-inference fragment: its ordered
premises and its conclusion. -/
inductive RuleInstance (a : Tolerance V) : List (Claim V) → Claim V → Prop where
  | edge (x y : V) : RuleInstance a [] ⟨x, y, a.distance x y⟩
  | refl (x : V) : RuleInstance a [] ⟨x, x, 0⟩
  | unitBound (x y : V) : RuleInstance a [] ⟨x, y, 1⟩
  | symm (x y : V) (r : ℚ) : RuleInstance a [⟨x, y, r⟩] ⟨y, x, r⟩
  | triangle (x y z : V) (r s : ℚ) :
      RuleInstance a [⟨x, y, r⟩, ⟨y, z, s⟩] ⟨x, z, min 1 (r + s)⟩
  | weaken (x y : V) (r s : ℚ) (le : r ≤ s) : RuleInstance a [⟨x, y, r⟩] ⟨x, y, s⟩

/-- A claim is derived exactly when some rule instance concludes it from
derived premises. -/
theorem derives_iff_ruleInstance (a : Tolerance V) (claim : Claim V) :
    Derives a claim ↔
      ∃ premises, RuleInstance a premises claim ∧ ∀ premise ∈ premises, Derives a premise := by
  constructor
  · intro derivation
    cases derivation with
    | edge x y => exact ⟨[], .edge x y, by simp⟩
    | refl x => exact ⟨[], .refl x, by simp⟩
    | unitBound x y => exact ⟨[], .unitBound x y, by simp⟩
    | @symm x y r premise => exact ⟨[⟨x, y, r⟩], .symm x y r, by simpa using premise⟩
    | @triangle x y z r s first second =>
        exact ⟨[⟨x, y, r⟩, ⟨y, z, s⟩], .triangle x y z r s, by simp [first, second]⟩
    | @weaken x y r s premise le => exact ⟨[⟨x, y, r⟩], .weaken x y r s le, by simpa using premise⟩
  · rintro ⟨premises, rule, derived⟩
    cases rule with
    | edge x y => exact .edge x y
    | refl x => exact .refl x
    | unitBound x y => exact .unitBound x y
    | symm x y r => exact .symm (derived ⟨x, y, r⟩ (by simp))
    | triangle x y z r s =>
        exact .triangle (derived ⟨x, y, r⟩ (by simp)) (derived ⟨y, z, s⟩ (by simp))
    | weaken x y r s le => exact .weaken (derived ⟨x, y, r⟩ (by simp)) le

/-- One backward proof-search step: the first obligation is replaced by the
premises of a rule instance concluding it. -/
def Resolves (a : Tolerance V) (source target : List (Claim V)) : Prop :=
  ∃ premises conclusion rest, RuleInstance a premises conclusion ∧
    source = conclusion :: rest ∧ target = premises ++ rest

/-- **The path-inference GSLT** of a seed tolerance. -/
abbrev pathInference (a : Tolerance V) : GSLT.{u} where
  Term := List (Claim V)
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Resolves a
  rewrites_resp_left := by
    intro _ _ target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ step equal
    exact equal ▸ step

variable {a : Tolerance V}

theorem resolves_append_right {source target : List (Claim V)} (step : Resolves a source target)
    (suffix : List (Claim V)) : Resolves a (source ++ suffix) (target ++ suffix) := by
  obtain ⟨premises, conclusion, rest, rule, rfl, rfl⟩ := step
  exact ⟨premises, conclusion, rest ++ suffix, rule, rfl, by simp⟩

theorem multiStep_append_right {source target : (pathInference a).Term}
    (steps : (pathInference a).MultiStep source target) (suffix : List (Claim V)) :
    (pathInference a).MultiStep (source ++ suffix) (target ++ suffix) := by
  induction steps with
  | refl _ => exact .refl _
  | step head _ inductionHypothesis =>
      exact .step (resolves_append_right head suffix) inductionHypothesis

/-- Soundness of proof search: every obligation of a list that rewrites to a
fully derived list is derived. -/
theorem derives_of_multiStep {source target : (pathInference a).Term}
    (steps : (pathInference a).MultiStep source target)
    (derivedTarget : ∀ claim ∈ target, Derives a claim) :
    ∀ claim ∈ source, Derives a claim := by
  induction steps with
  | refl _ => exact derivedTarget
  | step head _ inductionHypothesis =>
      obtain ⟨premises, conclusion, rest, rule, rfl, rfl⟩ := head
      have derivedMiddle := inductionHypothesis derivedTarget
      intro claim member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact (derives_iff_ruleInstance a claim).mpr
          ⟨premises, rule, fun premise inPremises =>
            derivedMiddle premise (List.mem_append_left _ inPremises)⟩
      · exact derivedMiddle claim (List.mem_append_right _ inRest)

/-- Completeness of proof search for one derived claim. -/
theorem run_of_derives {claim : Claim V} (derivation : Derives a claim) :
    (pathInference a).MultiStep [claim] [] := by
  induction derivation with
  | edge x y => exact .step ⟨[], _, [], .edge x y, rfl, rfl⟩ (.refl _)
  | refl x => exact .step ⟨[], _, [], .refl x, rfl, rfl⟩ (.refl _)
  | unitBound x y => exact .step ⟨[], _, [], .unitBound x y, rfl, rfl⟩ (.refl _)
  | @symm x y r _ inductionHypothesis =>
      exact .step ⟨[⟨x, y, r⟩], _, [], .symm x y r, rfl, rfl⟩ inductionHypothesis
  | @triangle x y z r s _ _ firstRun secondRun =>
      refine .step ⟨[⟨x, y, r⟩, ⟨y, z, s⟩], _, [], .triangle x y z r s, rfl, rfl⟩ ?_
      have first := multiStep_append_right firstRun [⟨y, z, s⟩]
      exact multiStep_trans first secondRun
  | @weaken x y r s _ le inductionHypothesis =>
      exact .step ⟨[⟨x, y, r⟩], _, [], .weaken x y r s le, rfl, rfl⟩ inductionHypothesis

/-- Completeness of proof search for a list of derived claims. -/
theorem run_of_all_derive :
    ∀ goals : List (Claim V), (∀ claim ∈ goals, Derives a claim) →
      (pathInference a).MultiStep goals []
  | [], _ => .refl _
  | claim :: rest, derived => by
      have head := multiStep_append_right (run_of_derives (derived claim List.mem_cons_self)) rest
      exact multiStep_trans head
        (run_of_all_derive rest fun other member => derived other (List.mem_cons_of_mem _ member))

/-- **A list of obligations rewrites to the empty list exactly when every
obligation is derived.** -/
theorem multiStep_nil_iff (goals : List (Claim V)) :
    (pathInference a).MultiStep goals [] ↔ ∀ claim ∈ goals, Derives a claim :=
  ⟨fun steps => derives_of_multiStep steps (by simp), run_of_all_derive goals⟩

/-- **Adequacy**: a claim rewrites to the empty obligation list exactly when the
declarative relation derives it. -/
theorem run_iff_derives (claim : Claim V) :
    (pathInference a).MultiStep [claim] [] ↔ Derives a claim := by
  rw [multiStep_nil_iff]
  simp

/-- **Adequacy for the checker**: a run exists exactly when the existing
checker accepts some certificate for the claim. -/
theorem run_iff_checked [DecidableEq V] (claim : Claim V) :
    (pathInference a).MultiStep [claim] [] ↔ ∃ proof, check a claim proof = true := by
  rw [run_iff_derives]
  exact derives_iff_checked a claim

/-- **Semantic adequacy on a finite carrier**: a run exists exactly when every
metric tolerance extending the seed satisfies the bound. -/
theorem run_iff_metric_valid [Fintype V] [DecidableEq V] (x y : V) (bound : ℚ) :
    (pathInference a).MultiStep [⟨x, y, bound⟩] [] ↔
      ∀ model, a.Extends model → model.Metric → model.distance x y ≤ bound := by
  rw [run_iff_derives]
  exact derives_iff_metric_valid a

/-! ## Controls -/

open Examples in
/-- The graded chain derives the endpoints at `2/5` by a run. -/
theorem graded_run : (pathInference graded).MultiStep [⟨0, 2, 2 / 5⟩] [] :=
  (run_iff_derives _).mpr graded_path_derives

open Examples in
/-- No run reaches the endpoint collapse at bound `0`. -/
theorem graded_no_collapse_run : ¬ (pathInference graded).MultiStep [⟨0, 2, 0⟩] [] := by
  rw [run_iff_checked]
  exact graded_no_endpoint_collapse_certificate

open Examples in
/-- **A run certifies validity in every metric extension, not truth in the
seed.** On the non-metric chain a run puts the endpoints at distance `0`,
while the seed puts them at distance `1`. -/
theorem chain_run_not_seed_truth :
    (pathInference chain).MultiStep [⟨0, 2, 0⟩] [] ∧ chain.distance 0 2 = 1 := by
  constructor
  · rw [run_iff_checked]
    refine ⟨throughMiddle 0 2, ?_⟩
    norm_num [check, throughMiddle, infer, Tolerance.distance, Fin.ext_iff]
  · norm_num [Tolerance.distance, Fin.ext_iff]

/-- The proof-search GSLT as an unlabelled system. -/
abbrev searchSystem (a : Tolerance V) : HennessyMilner.System.{0, 0} (pathInference a) where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Unit
  act _ := Resolves a
  act_resp_left := by
    intro _ _ _ target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  act_resp_right := by
    intro _ _ _ _ step equal
    exact equal ▸ step

/-- **Proof search is infinitely branching.** Weakening offers a premise for
every smaller bound, so no finite set of representatives covers the
successors of one obligation. -/
theorem not_imageFinite (a : Tolerance V) (x : V) : ¬ (searchSystem a).ImageFiniteModulo := by
  intro finite
  obtain ⟨representatives, representativesFinite, covered⟩ := finite () [⟨x, x, 1⟩]
  have contains : Set.range (fun r : ℕ => [(⟨x, x, -(r : ℚ)⟩ : Claim V)]) ⊆ representatives := by
    rintro _ ⟨r, rfl⟩
    have step : Resolves a [⟨x, x, 1⟩] [⟨x, x, -(r : ℚ)⟩] :=
      ⟨[⟨x, x, -(r : ℚ)⟩], ⟨x, x, 1⟩, [], .weaken x x _ 1 (by
        have : (0 : ℚ) ≤ r := Nat.cast_nonneg r
        linarith), rfl, rfl⟩
    obtain ⟨representative, membership, equal⟩ := covered step
    change [(⟨x, x, -(r : ℚ)⟩ : Claim V)] = representative at equal
    show [(⟨x, x, -(r : ℚ)⟩ : Claim V)] ∈ representatives
    rw [equal]
    exact membership
  have injective : Function.Injective fun r : ℕ => [(⟨x, x, -(r : ℚ)⟩ : Claim V)] := by
    intro first second equal
    simp only [List.cons.injEq, and_true, Claim.mk.injEq, true_and, neg_inj, Nat.cast_inj] at equal
    exact equal
  exact (Set.infinite_range_of_injective injective) (representativesFinite.subset contains)

end PathInference

end Mettapedia.GSLT.Distinction
