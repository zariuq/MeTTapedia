import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsGrades
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsWorldModel
import Mettapedia.Algebra.RationalComplexAmplitude

/-!
# Amplitudes over runs: exact complex grades, sums over causal histories, interference guards

A firing carries an exact amplitude in `ℚ[i]`, the quadratic algebra `QuadraticAlgebra ℚ (-1) 0`
of `RationalComplexAmplitude`, and its Born weight is the norm `born`.

## The amplitude of a run is a trace invariant

* `runAmplitude amp w` is the product of the amplitudes of the firings of `w`. It is R22's site
  account into the multiplicative monoid of `ℚ[i]` (`amplitudeAccount`, `amplitudeAccount_of`).
  That monoid is commutative, so the account factors through the static and the contextual traces
  (`amplitudeAccount_factors_static`, `amplitudeAccount_factors_contextual`). On words,
  round-equivalent and statically trace-equivalent runs have one amplitude
  (`runAmplitude_roundEquiv`, `runAmplitude_traceEquiv`).
* One history alone shows no interference: its Born weight is the product of the Born weights of
  its firings (`born_runAmplitude`).

## The regional amplitude `Z_Q`

* A causal history is a branch of R27's unfolding: a round-equivalence class of terminal
  histories. Its amplitude (`classAmplitude`) and the configuration class it ends in (`classEnd`)
  are well defined.
* A region `Q` is a set of configuration classes. `regionalAmplitude` sums the amplitudes of the
  branches that end in `Q`, each once. At a closed frontier these are all the terminal causal
  histories that end in `Q`, with no length bound (`regionBranches_exact_of_closed`). So `Z_Q`
  depends neither on the depth budget (`regionalAmplitude_eq_of_closed`) nor on the interleaving
  chosen to represent a branch (`regionalAmplitude_eq_sum_representatives`).
* **A sum over interleavings counts a branch once per interleaving**
  (`interleavingAmplitude_eq_sum_count`). A diamond is one branch reached by two words: summed
  over interleavings it gives `2z` where its branch gives `z`, with Born weight `4|z|²` where it
  should be `|z|²` (`born_double`; the control is in `AnnotatedRunsAmplitudeControls`).

## Interference guards

* `Constructive paths` says `born (Σ z) > Σ born z`; `Destructive paths` says `Σ z = 0` while
  `Σ born z > 0`. For two paths, these are a positive interference term (`constructive_pair_iff`,
  by the two-path law `born_add`) and exact opposition (`destructive_pair_iff`).
* **Both compare paths, so both are non-local.**
  * Every nonzero arrival refutes a cancellation (`destructive_refuted_by_arrival`).
  * The arrival of the negated sum creates one (`destructive_reached_by_arrival`) and refutes every
    reinforcement (`not_constructive_after_negated_sum`); a copy of a single path creates a
    reinforcement (`constructive_reached_by_arrival`).
  * Neither is a test of each path alone (`destructive_not_candidatewise`,
    `constructive_not_candidatewise`), unlike R22's local disciplines (`local_stable`).
* **At a cut, a guard needs a complete predicate query of the region.**
  * With a predicate query of the region among the firing's queries, every verdict on the region's
    paths at the cut is the verdict on the paths its query saw (`verdict_iff_query`, mirroring
    `argmax_iff_census`), and a path arriving in the region refuses the firing
    (`query_refuses_arrival`).
  * Without one, a firing whose guards are equations (`StoreGuard`, such as a verdict decided on
    the rows it read) and which is admitted where the region cancels stays admitted one arriving
    path later, where the region does not cancel (`storeGuards_valid_frame`,
    `reads_cannot_certify_cancellation`); likewise for reinforcement
    (`reads_cannot_certify_reinforcement`).

## Incompleteness

* `amplitudeCollection` carries R27's status: it is complete exactly when the frontier is closed
  (`amplitudeCollection_eq_complete_iff`).
* Only a complete collection certifies an amplitude, a cancellation or a reinforcement
  (`certifiedAmplitude`, `CertifiesCancellation`, `CertifiesReinforcement`,
  `interferenceVerdict`). An incomplete collection is never "amplitude zero", whatever its partial
  sum (`incomplete_never_zero`, `incomplete_never_cancels`), and a certified cancellation holds over
  every terminal causal history (`certifiesCancellation_iff`, `certifiedAmplitude_eq_zero_iff`).
-/

set_option autoImplicit false

open scoped QuadraticAlgebra

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace AmplitudeRuns

open Mettapedia.Algebra.RationalComplexAmplitude (Amplitude born born_formula born_nonnegative
  born_zero_iff)
open Mettapedia.Effects (RunAccount)
open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)
open Mettapedia.GSLT.Causality.TraceCostValuation (traceFunctor)
open Mettapedia.GSLT.Distinction.CausalGluing (TraceEquiv)
open MeTTaCalculus.OccurrenceCommits (regionOf PredicateQuery mem_regionOf)
open AnnotatedRunUnfolding (CausalClass completed mem_completed Terminal)
open AnnotatedRunBranchCollection (terminalBranches mem_terminalBranches Closed
  branches_exact_of_closed Collection)

universe uT uS uO

/-! ## Interference of a bag of path amplitudes -/

section Bags

/-- **The coherent amplitude** of a bag of paths: their sum. -/
def coherent (paths : Multiset Amplitude) : Amplitude := paths.sum

/-- **The incoherent weight** of a bag of paths: the sum of their Born weights, phases
discarded. -/
def incoherent (paths : Multiset Amplitude) : ℚ := (paths.map born).sum

/-- **Constructive interference**: the Born weight of the coherent sum exceeds the incoherent
weight. -/
def Constructive (paths : Multiset Amplitude) : Prop := incoherent paths < born (coherent paths)

/-- **Destructive cancellation**: the coherent sum vanishes while the incoherent weight does
not. -/
def Destructive (paths : Multiset Amplitude) : Prop := coherent paths = 0 ∧ 0 < incoherent paths

instance (paths : Multiset Amplitude) : Decidable (Constructive paths) := by
  unfold Constructive
  infer_instance

instance (paths : Multiset Amplitude) : Decidable (Destructive paths) := by
  unfold Destructive
  infer_instance

/-- The imaginary unit `i` of `ℚ[i]`. -/
def unitI : Amplitude := ⟨0, 1⟩

@[simp] theorem born_zero : born 0 = 0 := (born_zero_iff 0).mpr rfl

@[simp] theorem born_one : born 1 = 1 := map_one born

theorem born_neg (z : Amplitude) : born (-z) = born z := by
  rw [born_formula, born_formula]
  simp

theorem born_unitI : born unitI = 1 := by
  rw [born_formula]
  simp [unitI]

theorem born_pos_iff (z : Amplitude) : 0 < born z ↔ z ≠ 0 := by
  constructor
  · intro positive zero
    rw [zero, born_zero] at positive
    exact lt_irrefl _ positive
  · intro nonzero
    exact lt_of_le_of_ne (born_nonnegative z) fun same => nonzero ((born_zero_iff z).mp same.symm)

theorem one_ne_zero' : (1 : Amplitude) ≠ 0 := fun same => by
  have := congrArg QuadraticAlgebra.re same
  simp at this

/-- The interference term of two amplitudes: twice the real part of `z w̄`. -/
def interference (z w : Amplitude) : ℚ := 2 * (z.re * w.re + z.im * w.im)

/-- **The two-path law in `ℚ[i]`**: the Born weight of a sum is the sum of the Born weights plus
the interference term. -/
theorem born_add (z w : Amplitude) : born (z + w) = born z + born w + interference z w := by
  rw [born_formula, born_formula, born_formula]
  simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, interference]
  ring

theorem interference_self (z : Amplitude) : interference z z = 2 * born z := by
  rw [born_formula]
  unfold interference
  ring

/-- **Doubling an amplitude quadruples its Born weight**: `|2z|² = 4|z|²`. -/
theorem born_double (z : Amplitude) : born (z + z) = 4 * born z := by
  rw [born_add, interference_self]
  ring

@[simp] theorem coherent_zero : coherent 0 = 0 := Multiset.sum_zero

@[simp] theorem incoherent_zero : incoherent 0 = 0 := by simp [incoherent]

@[simp] theorem coherent_cons (z : Amplitude) (paths : Multiset Amplitude) :
    coherent (z ::ₘ paths) = z + coherent paths := Multiset.sum_cons z paths

@[simp] theorem incoherent_cons (z : Amplitude) (paths : Multiset Amplitude) :
    incoherent (z ::ₘ paths) = born z + incoherent paths := by
  simp [incoherent]

theorem coherent_add (paths others : Multiset Amplitude) :
    coherent (paths + others) = coherent paths + coherent others := Multiset.sum_add _ _

theorem incoherent_add (paths others : Multiset Amplitude) :
    incoherent (paths + others) = incoherent paths + incoherent others := by
  simp [incoherent]

theorem incoherent_nonneg (paths : Multiset Amplitude) : 0 ≤ incoherent paths :=
  Multiset.sum_nonneg fun x member => by
    obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp member
    exact born_nonnegative z

theorem coherent_pair (z w : Amplitude) : coherent {z, w} = z + w := by
  simp [coherent]

theorem incoherent_pair (z w : Amplitude) : incoherent {z, w} = born z + born w := by
  simp [incoherent]

/-- **Two paths reinforce exactly when their interference term is positive.** -/
theorem constructive_pair_iff (z w : Amplitude) : Constructive {z, w} ↔ 0 < interference z w := by
  unfold Constructive
  rw [coherent_pair, incoherent_pair, born_add]
  constructor <;> intro h <;> linarith

/-- **Two paths cancel exactly when they are opposite and nonzero.** -/
theorem destructive_pair_iff (z w : Amplitude) : Destructive {z, w} ↔ w = -z ∧ z ≠ 0 := by
  unfold Destructive
  rw [coherent_pair, incoherent_pair]
  constructor
  · rintro ⟨sum, positive⟩
    have opposite : w = -z := add_eq_zero_iff_eq_neg.mp (by rw [add_comm]; exact sum)
    refine ⟨opposite, fun zero => ?_⟩
    rw [opposite, zero, neg_zero, born_zero, add_zero] at positive
    exact lt_irrefl _ positive
  · rintro ⟨rfl, nonzero⟩
    refine ⟨add_neg_cancel z, ?_⟩
    rw [born_neg]
    have := (born_pos_iff z).mpr nonzero
    linarith

/-- **Every nonzero arrival refutes a cancellation.** -/
theorem destructive_refuted_by_arrival {paths : Multiset Amplitude} (cancels : Destructive paths)
    {z : Amplitude} (nonzero : z ≠ 0) : ¬ Destructive (z ::ₘ paths) := by
  rintro ⟨sum, -⟩
  rw [coherent_cons, cancels.1, add_zero] at sum
  exact nonzero sum

/-- **An arrival creates a cancellation**: a bag with a nonzero coherent amplitude cancels once the
negation of that amplitude arrives. -/
theorem destructive_reached_by_arrival {paths : Multiset Amplitude} (nonzero : coherent paths ≠ 0) :
    Destructive (-coherent paths ::ₘ paths) := by
  refine ⟨by rw [coherent_cons, neg_add_cancel], ?_⟩
  rw [incoherent_cons, born_neg]
  have := (born_pos_iff _).mpr nonzero
  linarith [incoherent_nonneg paths]

/-- A bag whose coherent amplitude vanishes never reinforces. -/
theorem not_constructive_of_coherent_eq_zero {paths : Multiset Amplitude}
    (zero : coherent paths = 0) : ¬ Constructive paths := by
  unfold Constructive
  rw [zero, born_zero]
  exact not_lt.mpr (incoherent_nonneg paths)

/-- **The arrival of the negated sum refutes every reinforcement.** -/
theorem not_constructive_after_negated_sum (paths : Multiset Amplitude) :
    ¬ Constructive (-coherent paths ::ₘ paths) :=
  not_constructive_of_coherent_eq_zero (by rw [coherent_cons, neg_add_cancel])

/-- **An arrival creates a reinforcement**: one nonzero path alone does not reinforce, and with a
copy of itself it does. -/
theorem constructive_reached_by_arrival {z : Amplitude} (nonzero : z ≠ 0) :
    ¬ Constructive {z} ∧ Constructive {z, z} := by
  refine ⟨?_, ?_⟩
  · unfold Constructive
    simp [coherent, incoherent]
  · rw [constructive_pair_iff, interference_self]
    have := (born_pos_iff z).mpr nonzero
    linarith

/-- **Cancellation is not a test of each path alone.** -/
theorem destructive_not_candidatewise :
    ¬ ∃ keep : Amplitude → Prop, ∀ paths, Destructive paths ↔ ∀ z ∈ paths, keep z := by
  rintro ⟨keep, tests⟩
  have pair : Destructive {1, -1} := (destructive_pair_iff 1 (-1)).mpr ⟨rfl, one_ne_zero'⟩
  have kept : keep 1 := (tests _).mp pair 1 (by simp)
  have single : Destructive {1} := (tests _).mpr fun z member => by
    rw [Multiset.mem_singleton] at member
    rw [member]
    exact kept
  have sum := single.1
  simp only [coherent, Multiset.sum_singleton] at sum
  exact one_ne_zero' sum

/-- **Reinforcement is not a test of each path alone.** -/
theorem constructive_not_candidatewise :
    ¬ ∃ keep : Amplitude → Prop, ∀ paths, Constructive paths ↔ ∀ z ∈ paths, keep z := by
  rintro ⟨keep, tests⟩
  obtain ⟨alone, doubled⟩ := constructive_reached_by_arrival one_ne_zero'
  have kept : keep 1 := (tests _).mp doubled 1 (by simp)
  exact alone ((tests _).mpr fun z member => by
    rw [Multiset.mem_singleton] at member
    rw [member]
    exact kept)

/-! ### Controls on bags -/

/-- **In phase**: two unit paths give `4` against an incoherent `2`. -/
theorem in_phase_control :
    born (coherent {1, 1}) = 4 ∧ incoherent {1, 1} = 2 ∧ Constructive {1, 1} := by
  refine ⟨?_, ?_, ?_⟩
  · rw [coherent_pair, born_double, born_one]
    norm_num
  · rw [incoherent_pair, born_one]
    norm_num
  · exact (constructive_reached_by_arrival one_ne_zero').2

/-- **Shifted by `π`**: the paths `1` and `e^{iπ} = -1` give `0` against an incoherent `2`. -/
theorem opposite_phase_control :
    born (coherent {1, -1}) = 0 ∧ incoherent {1, -1} = 2 ∧ Destructive {1, -1} := by
  refine ⟨?_, ?_, (destructive_pair_iff 1 (-1)).mpr ⟨rfl, one_ne_zero'⟩⟩
  · rw [coherent_pair, add_neg_cancel, born_zero]
  · rw [incoherent_pair, born_neg, born_one]
    norm_num

/-- **In quadrature** (positive control): the paths `1` and `i` do not interfere, `2` against
`2`. -/
theorem quadrature_control :
    born (coherent {1, unitI}) = 2 ∧ incoherent {1, unitI} = 2 ∧ ¬ Constructive {1, unitI} ∧
      ¬ Destructive {1, unitI} := by
  have coherentWeight : born (coherent {1, unitI}) = 2 := by
    rw [coherent_pair, born_formula]
    simp [unitI]
    norm_num
  have incoherentWeight : incoherent {1, unitI} = 2 := by
    rw [incoherent_pair, born_one, born_unitI]
    norm_num
  refine ⟨coherentWeight, incoherentWeight, ?_, ?_⟩
  · unfold Constructive
    rw [coherentWeight, incoherentWeight]
    exact lt_irrefl _
  · rintro ⟨zero, -⟩
    have weight := congrArg born zero
    rw [coherentWeight, born_zero] at weight
    norm_num at weight

/-- **A third path's arrival flips cancellation**: `1` and `-1` cancel; once a third path `1`
arrives they give `1` against an incoherent `3`. -/
theorem third_path_flips :
    Destructive {1, -1} ∧ coherent (1 ::ₘ {1, -1}) = 1 ∧ incoherent (1 ::ₘ {1, -1}) = 3 ∧
      ¬ Destructive (1 ::ₘ {1, -1}) := by
  have cancels := opposite_phase_control.2.2
  refine ⟨cancels, ?_, ?_, destructive_refuted_by_arrival cancels one_ne_zero'⟩
  · rw [coherent_cons, cancels.1, add_zero]
  · rw [incoherent_cons, opposite_phase_control.2.1, born_one]
    norm_num

end Bags

/-! ## The amplitude of a run -/

section Runs

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (amp : Firing T S O → Amplitude)

omit [DecidableEq O] in
/-- **The amplitude of a run**: the product of the amplitudes of its firings. -/
def runAmplitude (w : List (Firing T S O)) : Amplitude := (w.map amp).prod

omit [DecidableEq O] in
@[simp] theorem runAmplitude_nil : runAmplitude amp [] = 1 := rfl

omit [DecidableEq O] in
@[simp] theorem runAmplitude_cons (f : Firing T S O) (w : List (Firing T S O)) :
    runAmplitude amp (f :: w) = amp f * runAmplitude amp w := List.prod_cons

omit [DecidableEq O] in
theorem runAmplitude_append (w w' : List (Firing T S O)) :
    runAmplitude amp (w ++ w') = runAmplitude amp w * runAmplitude amp w' := by
  simp [runAmplitude]

omit [DecidableEq O] in
/-- A run's amplitude depends only on its bag of firings. -/
theorem runAmplitude_perm {w w' : List (Firing T S O)} (perm : w.Perm w') :
    runAmplitude amp w = runAmplitude amp w' :=
  (perm.map amp).prod_eq

/-- **Contextual trace invariance**: round-equivalent runs have one amplitude. -/
theorem runAmplitude_roundEquiv {C : Configuration T O} {w w' : List (Firing T S O)}
    (equivalent : RoundEquiv A label C w w') : runAmplitude amp w = runAmplitude amp w' :=
  runAmplitude_perm amp (RoundEquiv.perm A label equivalent)

/-- **Static trace invariance**: statically trace-equivalent runs have one amplitude. -/
theorem runAmplitude_traceEquiv {w w' : List (Firing T S O)}
    (equivalent : TraceEquiv (StaticIndependent label) w w') :
    runAmplitude amp w = runAmplitude amp w' :=
  runAmplitude_perm amp (Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv.perm equivalent)

/-- **The amplitude annotation**: R22's site account of runs into the multiplicative monoid of
`ℚ[i]`. -/
def amplitudeAccount : RunAccount (Runs A label) Amplitude := siteAccount A label amp

/-- **The amplitude annotation of a run is the amplitude of its firings.** -/
theorem amplitudeAccount_of {x y : (theory A label).Term}
    (p : OccurrencePath (presentation A label) x y) :
    (amplitudeAccount A label amp).of p = runAmplitude amp (OccurrencePath.sites p) :=
  siteAccount_of_eq A label amp p

/-- **The amplitude annotation factors through the static traces.** -/
theorem amplitudeAccount_factors_static :
    ∃ traced : RunAccount (StaticTraces A label) Amplitude,
      traced.comap (traceFunctor _) = amplitudeAccount A label amp :=
  siteAccount_factors_static A label amp

/-- **The amplitude annotation factors through the contextual traces.** -/
theorem amplitudeAccount_factors_contextual :
    ∃ traced : RunAccount (ContextualTraces A label) Amplitude,
      traced.comap (traceFunctor _) = amplitudeAccount A label amp :=
  siteAccount_factors_contextual A label amp

omit [DecidableEq O] in
/-- **One history alone does not interfere**: its Born weight is the product of the Born weights
of its firings. -/
theorem born_runAmplitude (w : List (Firing T S O)) :
    born (runAmplitude amp w) = (w.map fun f => born (amp f)).prod := by
  rw [runAmplitude, map_list_prod, List.map_map]
  rfl

end Runs

/-! ## The regional amplitude over causal histories -/

section Branches

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (amp : Firing T S O → Amplitude)

/-- **The amplitude of a causal history**: the amplitude of any of its runs. -/
def classAmplitude (root : Configuration T O) : CausalClass A label root → Amplitude :=
  Quot.lift (runAmplitude amp) fun _ _ related => runAmplitude_roundEquiv A label amp related

theorem classAmplitude_mk (root : Configuration T O) (w : List (Firing T S O)) :
    classAmplitude A label amp root (Quot.mk _ w) = runAmplitude amp w := rfl

/-- **The end of a causal history**: the class of the configuration its runs reach. -/
def classEnd (root : Configuration T O) : CausalClass A label root → ConfigurationClass A O :=
  Quot.lift (fun w => ConfigurationClass.mk A (follow label root w)) fun _ _ related =>
    Quotient.sound (AnnotatedRunBranchCollection.RoundEquiv.follow_sameUpTo A label related)

theorem classEnd_mk (root : Configuration T O) (w : List (Firing T S O)) :
    classEnd A label root (Quot.mk _ w) = ConfigurationClass.mk A (follow label root w) := rfl

variable (catalogue : List (Firing T S O)) (budget : ℕ) (root : Configuration T O)
  (Q : ConfigurationClass A O → Prop)

open Classical in
/-- **The branches of a region**: the causal histories of the unfolding that end in `Q`. -/
noncomputable def regionBranches : Finset (CausalClass A label root) :=
  (terminalBranches A label catalogue budget root).filter fun trace =>
    Q (classEnd A label root trace)

/-- **The paths of a region**: one amplitude per causal history that ends in `Q`. -/
noncomputable def branchAmplitudes : Multiset Amplitude :=
  (regionBranches A label catalogue budget root Q).val.map (classAmplitude A label amp root)

/-- **The regional amplitude** `Z_Q`: the sum of the amplitudes of the causal histories that end
in `Q`, each once. -/
noncomputable def regionalAmplitude : Amplitude :=
  ∑ trace ∈ regionBranches A label catalogue budget root Q, classAmplitude A label amp root trace

theorem regionalAmplitude_eq_coherent :
    regionalAmplitude A label amp catalogue budget root Q =
      coherent (branchAmplitudes A label amp catalogue budget root Q) := rfl

theorem mem_regionBranches (trace : CausalClass A label root) :
    trace ∈ regionBranches A label catalogue budget root Q ↔
      trace ∈ terminalBranches A label catalogue budget root ∧ Q (classEnd A label root trace) := by
  classical
  unfold regionBranches
  rw [Finset.mem_filter]

variable {catalogue budget root Q}

/-- **Exactness at a closed frontier**: the branches of the region are the causal classes of all
terminal histories that end in `Q`, with no length bound. -/
theorem regionBranches_exact_of_closed (closed : Closed A label catalogue budget root)
    (trace : CausalClass A label root) :
    trace ∈ regionBranches A label catalogue budget root Q ↔
      ∃ word, Executable A label root word ∧ (∀ f ∈ word, f ∈ catalogue) ∧
        Terminal A label catalogue (follow label root word) ∧
        Q (ConfigurationClass.mk A (follow label root word)) ∧ Quot.mk _ word = trace := by
  rw [mem_regionBranches, branches_exact_of_closed A label closed]
  constructor
  · rintro ⟨⟨word, run, covered, terminal, rfl⟩, inQ⟩
    exact ⟨word, run, covered, terminal, inQ, rfl⟩
  · rintro ⟨word, run, covered, terminal, inQ, rfl⟩
    exact ⟨⟨word, run, covered, terminal, rfl⟩, inQ⟩

/-- **`Z_Q` does not depend on the depth budget** once the frontier is closed. -/
theorem regionalAmplitude_eq_of_closed {budget' : ℕ} (closed : Closed A label catalogue budget root)
    (closed' : Closed A label catalogue budget' root) :
    regionalAmplitude A label amp catalogue budget root Q =
      regionalAmplitude A label amp catalogue budget' root Q := by
  have same : regionBranches A label catalogue budget root Q =
      regionBranches A label catalogue budget' root Q := by
    ext trace
    rw [regionBranches_exact_of_closed A label closed,
      regionBranches_exact_of_closed A label closed']
  unfold regionalAmplitude
  rw [same]

/-- **`Z_Q` does not depend on the interleavings that represent its branches**: summing the
amplitude of any one run of each branch gives it. -/
theorem regionalAmplitude_eq_sum_representatives
    (representative : CausalClass A label root → List (Firing T S O))
    (represents : ∀ trace, Quot.mk _ (representative trace) = trace) :
    regionalAmplitude A label amp catalogue budget root Q =
      ∑ trace ∈ regionBranches A label catalogue budget root Q,
        runAmplitude amp (representative trace) := by
  unfold regionalAmplitude
  refine Finset.sum_congr rfl fun trace _ => ?_
  conv_lhs => rw [← represents trace]
  rfl

variable (catalogue budget root Q)

open Classical in
/-- **The sum over interleavings**: the amplitudes of the terminal words that end in `Q`, once per
word. -/
noncomputable def interleavingAmplitude : Amplitude :=
  (((completed A label catalogue budget root).filter fun w =>
      decide (Q (ConfigurationClass.mk A (follow label root w)))).map (runAmplitude amp)).sum

open Classical in
/-- How many terminal words that end in `Q` interleave a causal history. -/
noncomputable def interleavings (trace : CausalClass A label root) : ℕ :=
  (((completed A label catalogue budget root).filter fun w =>
      decide (Q (ConfigurationClass.mk A (follow label root w)))).map (Quot.mk _)).count trace

open Classical in
/-- **A sum over interleavings counts each causal history once per interleaving.** -/
theorem interleavingAmplitude_eq_sum_count :
    interleavingAmplitude A label amp catalogue budget root Q =
      ∑ trace ∈ regionBranches A label catalogue budget root Q,
        interleavings A label catalogue budget root Q trace •
          classAmplitude A label amp root trace := by
  unfold interleavingAmplitude interleavings
  have mapped : ((completed A label catalogue budget root).filter fun w =>
        decide (Q (ConfigurationClass.mk A (follow label root w)))).map (runAmplitude amp) =
      (((completed A label catalogue budget root).filter fun w =>
        decide (Q (ConfigurationClass.mk A (follow label root w)))).map
          (Quot.mk (RoundEquiv A label root))).map (classAmplitude A label amp root) := by
    rw [List.map_map]
    rfl
  rw [mapped, Finset.sum_list_map_count]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext trace
  rw [mem_regionBranches, List.mem_toFinset, List.mem_map]
  unfold terminalBranches
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨w, member, rfl⟩
    rw [List.mem_filter, decide_eq_true_eq] at member
    exact ⟨⟨w, member.1, rfl⟩, member.2⟩
  · rintro ⟨⟨w, member, rfl⟩, inQ⟩
    exact ⟨w, List.mem_filter.mpr ⟨member, decide_eq_true_eq.mpr inQ⟩, rfl⟩

/-! ### The collection of a region's amplitudes, with R27's status -/

open Classical in
/-- **The amplitude collection of a region**: the paths of its branches, complete exactly when the
frontier is closed. -/
noncomputable def amplitudeCollection : Collection Amplitude :=
  if Closed A label catalogue budget root then
    .complete (branchAmplitudes A label amp catalogue budget root Q)
  else .incomplete (branchAmplitudes A label amp catalogue budget root Q)

/-- **The collection is complete exactly when the frontier is closed.** -/
theorem amplitudeCollection_eq_complete_iff (bag : Multiset Amplitude) :
    amplitudeCollection A label amp catalogue budget root Q = .complete bag ↔
      Closed A label catalogue budget root ∧
        bag = branchAmplitudes A label amp catalogue budget root Q := by
  classical
  unfold amplitudeCollection
  split
  · next closed =>
      constructor
      · intro same
        cases same
        exact ⟨closed, rfl⟩
      · rintro ⟨_, rfl⟩
        rfl
  · next open_ =>
      constructor
      · intro same
        cases same
      · rintro ⟨closed, _⟩
        exact absurd closed open_

variable {catalogue budget root Q}

/-- **An open frontier makes the collection incomplete**, whatever it found. -/
theorem amplitudeCollection_incomplete_of_open (open_ : ¬ Closed A label catalogue budget root) :
    amplitudeCollection A label amp catalogue budget root Q =
      .incomplete (branchAmplitudes A label amp catalogue budget root Q) := by
  classical
  unfold amplitudeCollection
  rw [if_neg open_]

end Branches

/-! ## What a collection certifies -/

section Certificates

/-- The amplitude a collection certifies: only a complete collection certifies one. -/
def certifiedAmplitude : Collection Amplitude → Option Amplitude
  | .complete bag => some (coherent bag)
  | .incomplete _ => none

/-- A collection certifies a cancellation only when it is complete and its paths cancel. -/
def CertifiesCancellation : Collection Amplitude → Prop
  | .complete bag => Destructive bag
  | .incomplete _ => False

/-- A collection certifies a reinforcement only when it is complete and its paths reinforce. -/
def CertifiesReinforcement : Collection Amplitude → Prop
  | .complete bag => Constructive bag
  | .incomplete _ => False

/-- The interference verdict of a collection. -/
inductive Interference where
  | cancels
  | reinforces
  | neither
  | incomplete
deriving DecidableEq

/-- **The verdict rule**: only a complete collection decides interference. -/
def interferenceVerdict : Collection Amplitude → Interference
  | .complete bag =>
      if Destructive bag then .cancels else if Constructive bag then .reinforces else .neither
  | .incomplete _ => .incomplete

/-- **Incomplete is never "amplitude zero"**, whatever was found. -/
theorem incomplete_never_zero (found : Multiset Amplitude) :
    certifiedAmplitude (.incomplete found) ≠ some 0 := fun same => by cases same

/-- **An incomplete collection never certifies a cancellation**, even when its partial paths
cancel. -/
theorem incomplete_never_cancels (found : Multiset Amplitude) :
    ¬ CertifiesCancellation (.incomplete found) := id

theorem incomplete_never_reinforces (found : Multiset Amplitude) :
    ¬ CertifiesReinforcement (.incomplete found) := id

theorem interferenceVerdict_cancels_iff (collection : Collection Amplitude) :
    interferenceVerdict collection = .cancels ↔ CertifiesCancellation collection := by
  cases collection with
  | complete bag =>
      simp only [interferenceVerdict, CertifiesCancellation]
      by_cases cancels : Destructive bag
      · simp [cancels]
      · by_cases reinforces : Constructive bag <;> simp [cancels, reinforces]
  | incomplete found => simp [interferenceVerdict, CertifiesCancellation]

theorem interferenceVerdict_incomplete_iff (collection : Collection Amplitude) :
    interferenceVerdict collection = .incomplete ↔ ∃ found, collection = .incomplete found := by
  cases collection with
  | complete bag =>
      simp only [interferenceVerdict, reduceCtorEq, exists_false, iff_false]
      by_cases cancels : Destructive bag
      · simp [cancels]
      · by_cases reinforces : Constructive bag <;> simp [cancels, reinforces]
  | incomplete found => simp [interferenceVerdict]

/-- A complete collection is never decided incomplete. -/
theorem interferenceVerdict_complete_ne (bag : Multiset Amplitude) :
    interferenceVerdict (.complete bag) ≠ .incomplete := fun same =>
  Collection.incomplete_ne_complete _ bag
    ((interferenceVerdict_incomplete_iff _).mp same).choose_spec.symm

end Certificates

section RegionCertificates

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (amp : Firing T S O → Amplitude)
variable {catalogue : List (Firing T S O)} {budget : ℕ} {root : Configuration T O}
  {Q : ConfigurationClass A O → Prop}

/-- **A certified cancellation is a cancellation over every terminal causal history**: the frontier
is closed and the paths of the region's branches, which are all its terminal causal histories
(`regionBranches_exact_of_closed`), cancel. -/
theorem certifiesCancellation_iff :
    CertifiesCancellation (amplitudeCollection A label amp catalogue budget root Q) ↔
      Closed A label catalogue budget root ∧
        Destructive (branchAmplitudes A label amp catalogue budget root Q) := by
  classical
  by_cases closed : Closed A label catalogue budget root
  · rw [(amplitudeCollection_eq_complete_iff A label amp catalogue budget root Q _).mpr
      ⟨closed, rfl⟩]
    exact ⟨fun cancels => ⟨closed, cancels⟩, fun both => both.2⟩
  · rw [amplitudeCollection_incomplete_of_open A label amp closed]
    exact ⟨False.elim, fun both => absurd both.1 closed⟩

/-- **A certified reinforcement is a reinforcement over every terminal causal history.** -/
theorem certifiesReinforcement_iff :
    CertifiesReinforcement (amplitudeCollection A label amp catalogue budget root Q) ↔
      Closed A label catalogue budget root ∧
        Constructive (branchAmplitudes A label amp catalogue budget root Q) := by
  classical
  by_cases closed : Closed A label catalogue budget root
  · rw [(amplitudeCollection_eq_complete_iff A label amp catalogue budget root Q _).mpr
      ⟨closed, rfl⟩]
    exact ⟨fun reinforces => ⟨closed, reinforces⟩, fun both => both.2⟩
  · rw [amplitudeCollection_incomplete_of_open A label amp closed]
    exact ⟨False.elim, fun both => absurd both.1 closed⟩

/-- **The certified amplitude is `Z_Q`, and only at a closed frontier.** -/
theorem certifiedAmplitude_eq_some_iff (z : Amplitude) :
    certifiedAmplitude (amplitudeCollection A label amp catalogue budget root Q) = some z ↔
      Closed A label catalogue budget root ∧
        regionalAmplitude A label amp catalogue budget root Q = z := by
  classical
  by_cases closed : Closed A label catalogue budget root
  · rw [(amplitudeCollection_eq_complete_iff A label amp catalogue budget root Q _).mpr
      ⟨closed, rfl⟩]
    simp only [certifiedAmplitude, Option.some.injEq, ← regionalAmplitude_eq_coherent]
    exact ⟨fun same => ⟨closed, same⟩, fun both => both.2⟩
  · rw [amplitudeCollection_incomplete_of_open A label amp closed]
    simp only [certifiedAmplitude, reduceCtorEq, false_iff, not_and]
    exact fun closed' => absurd closed' closed

/-- **Amplitude zero is certified only by a closed frontier whose `Z_Q` vanishes.** -/
theorem certifiedAmplitude_eq_zero_iff :
    certifiedAmplitude (amplitudeCollection A label amp catalogue budget root Q) = some 0 ↔
      Closed A label catalogue budget root ∧
        regionalAmplitude A label amp catalogue budget root Q = 0 :=
  certifiedAmplitude_eq_some_iff A label amp 0

/-- **An open frontier certifies nothing**, whatever its partial sum. -/
theorem open_certifies_nothing (open_ : ¬ Closed A label catalogue budget root) :
    certifiedAmplitude (amplitudeCollection A label amp catalogue budget root Q) = none ∧
      ¬ CertifiesCancellation (amplitudeCollection A label amp catalogue budget root Q) ∧
      ¬ CertifiesReinforcement (amplitudeCollection A label amp catalogue budget root Q) ∧
      interferenceVerdict (amplitudeCollection A label amp catalogue budget root Q) =
        .incomplete := by
  rw [amplitudeCollection_incomplete_of_open A label amp open_]
  exact ⟨rfl, id, id, rfl⟩

end RegionCertificates

/-! ## Interference guards at a cut -/

section Cut

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (wave : T → Amplitude)

omit [DecidableEq O] in
/-- **The paths a set of rows carries**: one amplitude per row, read from its label. -/
def pathsOf (rows : Finset O) : Multiset Amplitude := rows.val.map fun o => wave (label o)

omit [DecidableEq O] in
/-- **The paths of a region at a cut**: one per present row of the region. -/
def regionPaths (region : T → Bool) (C : Configuration T O) : Multiset Amplitude :=
  pathsOf label wave (regionOf label C.present region)

theorem pathsOf_insert {rows : Finset O} {o : O} (fresh : o ∉ rows) :
    pathsOf label wave (insert o rows) = wave (label o) ::ₘ pathsOf label wave rows := by
  unfold pathsOf
  rw [Finset.insert_val_of_notMem fresh, Multiset.map_cons]

/-- A row arriving in the region joins its rows. -/
theorem regionOf_union_singleton (region : T → Bool) (present : Finset O) {o : O}
    (inRegion : region (label o) = true) :
    regionOf label (present ∪ {o}) region = insert o (regionOf label present region) := by
  ext x
  simp only [mem_regionOf, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
  constructor
  · rintro ⟨inX | rfl, inside⟩
    · exact Or.inr ⟨inX, inside⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨inX, inside⟩)
    · exact ⟨Or.inr rfl, inRegion⟩
    · exact ⟨Or.inl inX, inside⟩

/-- **A path arriving in the region joins its paths.** -/
theorem regionPaths_arrival (region : T → Bool) (C : Configuration T O) {o : O}
    (absent : o ∉ C.present) (inRegion : region (label o) = true) :
    regionPaths label wave region ⟨C.equations, C.present ∪ {o}⟩ =
      wave (label o) ::ₘ regionPaths label wave region C := by
  unfold regionPaths
  rw [regionOf_union_singleton label region C.present inRegion]
  exact pathsOf_insert label wave fun member => absent (mem_regionOf.mp member).1

/-- **With a predicate query of the region, every verdict on the region's paths at the cut is a
verdict on the paths its query saw.** This is `argmax_iff_census` for any comparison of paths. -/
theorem verdict_iff_query (verdict : Multiset Amplitude → Prop) {f : Firing T S O}
    {C : Configuration T O} (valid : f.Valid A label C) {query : PredicateQuery O T}
    (member : PredicateQueryAdmission.Query.fixed query ∈ f.queries) :
    verdict (regionPaths label wave query.region C) ↔ verdict (pathsOf label wave query.seen) := by
  obtain ⟨σ, solved⟩ := valid.firing.consistent
  have saw : regionOf label C.present query.region = query.seen :=
    valid.observations _ member σ solved
  unfold regionPaths
  rw [saw]

/-- **Cancellation with a predicate query of the region is a test of the paths the query saw.** -/
theorem destructive_iff_query {f : Firing T S O} {C : Configuration T O} (valid : f.Valid A label C)
    {query : PredicateQuery O T} (member : PredicateQueryAdmission.Query.fixed query ∈ f.queries) :
    Destructive (regionPaths label wave query.region C) ↔
      Destructive (pathsOf label wave query.seen) :=
  verdict_iff_query A label wave Destructive valid member

/-- **Reinforcement with a predicate query of the region is a test of the paths the query saw.** -/
theorem constructive_iff_query {f : Firing T S O} {C : Configuration T O}
    (valid : f.Valid A label C) {query : PredicateQuery O T}
    (member : PredicateQueryAdmission.Query.fixed query ∈ f.queries) :
    Constructive (regionPaths label wave query.region C) ↔
      Constructive (pathsOf label wave query.seen) :=
  verdict_iff_query A label wave Constructive valid member

/-- **The regional amplitude at the cut is the coherent sum of the paths the query saw.** -/
theorem coherent_query {f : Firing T S O} {C : Configuration T O} (valid : f.Valid A label C)
    {query : PredicateQuery O T} (member : PredicateQueryAdmission.Query.fixed query ∈ f.queries) :
    coherent (regionPaths label wave query.region C) =
      coherent (pathsOf label wave query.seen) := by
  obtain ⟨σ, solved⟩ := valid.firing.consistent
  have saw : regionOf label C.present query.region = query.seen :=
    valid.observations _ member σ solved
  unfold regionPaths
  rw [saw]

/-- **A path arriving in the region refuses a firing with a predicate query of it**: the firing is
admitted only where its query saw the whole region, so the guard is decided again at the new
cut. -/
theorem query_refuses_arrival {f : Firing T S O} {C : Configuration T O} (valid : f.Valid A label C)
    {query : PredicateQuery O T} (member : PredicateQueryAdmission.Query.fixed query ∈ f.queries) {o : O}
    (absent : o ∉ C.present) (inRegion : query.region (label o) = true) :
    ¬ f.Valid A label ⟨C.equations, C.present ∪ {o}⟩ := by
  intro after
  obtain ⟨σ, solved⟩ := valid.firing.consistent
  have before : regionOf label C.present query.region = query.seen :=
    valid.observations _ member σ solved
  obtain ⟨τ, solved'⟩ := after.firing.consistent
  have later : regionOf label (C.present ∪ {o}) query.region = query.seen :=
    after.observations _ member τ solved'
  rw [regionOf_union_singleton label query.region C.present inRegion, before] at later
  have seen : o ∈ query.seen := by
    rw [← later]
    exact Finset.mem_insert_self o _
  rw [← before] at seen
  exact absent (mem_regionOf.mp seen).1

omit [DecidableEq O] in
/-- A guard that reads only the solutions of the store: an equation. Guards decided at instance
formation from the firing's own data, such as R30's `GuardBits.check`, are of this kind. -/
def StoreGuard (check : Check T) : Prop := ∃ left right, check = .equal left right

/-- **A firing whose guards are equations, without predicate queries, stays admitted when an
occurrence it does not make arrives.** -/
theorem storeGuards_valid_frame {f : Firing T S O} {C : Configuration T O}
    (guards : ∀ check ∈ f.rule.checks, StoreGuard check) (queries : f.queries = [])
    (valid : f.Valid A label C) {o : O} (unmade : o ∉ f.selection.made) :
    f.Valid A label ⟨C.equations, C.present ∪ {o}⟩ := by
  have firing := valid.firing
  have apart : Disjoint (f.selection.commit (T := T)).made {o} := by
    rw [Finset.disjoint_singleton_right]
    simpa [Selection.commit] using unmade
  refine ⟨⟨firing.take_distinct, firing.output_distinct, firing.take_length, firing.read_length,
    firing.outputs, firing.occurrences.frame_of_positive rfl apart, firing.consistent, ?_⟩, ?_⟩
  · intro check member σ solved
    obtain ⟨left, right, rfl⟩ := guards check member
    exact firing.checks _ member σ solved
  · intro query inQueries
    rw [queries] at inQueries
    cases inQueries

/-- **What a firing reads cannot certify a cancellation.** A firing whose guards are equations and
which has no predicate query, admitted at a cut where the region cancels, stays admitted when a
nonzero path arrives in the region; there the region does not cancel. Whatever the firing decided
from its own data, it decided it at both cuts. -/
theorem reads_cannot_certify_cancellation {f : Firing T S O} {C : Configuration T O}
    (region : T → Bool) (guards : ∀ check ∈ f.rule.checks, StoreGuard check)
    (queries : f.queries = []) (valid : f.Valid A label C)
    (cancels : Destructive (regionPaths label wave region C)) {o : O}
    (absent : o ∉ C.present) (unmade : o ∉ f.selection.made) (inRegion : region (label o) = true)
    (nonzero : wave (label o) ≠ 0) :
    f.Valid A label ⟨C.equations, C.present ∪ {o}⟩ ∧
      ¬ Destructive (regionPaths label wave region ⟨C.equations, C.present ∪ {o}⟩) := by
  refine ⟨storeGuards_valid_frame A label guards queries valid unmade, ?_⟩
  rw [regionPaths_arrival label wave region C absent inRegion]
  exact destructive_refuted_by_arrival cancels nonzero

/-- **What a firing reads cannot certify a reinforcement.** A firing whose guards are equations and
which has no predicate query stays admitted when the negation of the region's amplitude arrives
in the region; there the region does not reinforce. -/
theorem reads_cannot_certify_reinforcement {f : Firing T S O} {C : Configuration T O}
    (region : T → Bool) (guards : ∀ check ∈ f.rule.checks, StoreGuard check)
    (queries : f.queries = []) (valid : f.Valid A label C) {o : O} (absent : o ∉ C.present)
    (unmade : o ∉ f.selection.made) (inRegion : region (label o) = true)
    (negated : wave (label o) = -coherent (regionPaths label wave region C)) :
    f.Valid A label ⟨C.equations, C.present ∪ {o}⟩ ∧
      ¬ Constructive (regionPaths label wave region ⟨C.equations, C.present ∪ {o}⟩) := by
  refine ⟨storeGuards_valid_frame A label guards queries valid unmade, ?_⟩
  rw [regionPaths_arrival label wave region C absent inRegion, negated]
  exact not_constructive_after_negated_sum _

end Cut

end AmplitudeRuns

open AmplitudeRuns

#print axioms born_neg
#print axioms born_add
#print axioms born_double
#print axioms constructive_pair_iff
#print axioms destructive_pair_iff
#print axioms destructive_refuted_by_arrival
#print axioms destructive_reached_by_arrival
#print axioms not_constructive_after_negated_sum
#print axioms constructive_reached_by_arrival
#print axioms destructive_not_candidatewise
#print axioms constructive_not_candidatewise
#print axioms in_phase_control
#print axioms opposite_phase_control
#print axioms quadrature_control
#print axioms third_path_flips
#print axioms runAmplitude_perm
#print axioms runAmplitude_roundEquiv
#print axioms runAmplitude_traceEquiv
#print axioms amplitudeAccount_of
#print axioms amplitudeAccount_factors_static
#print axioms amplitudeAccount_factors_contextual
#print axioms born_runAmplitude
#print axioms mem_regionBranches
#print axioms regionBranches_exact_of_closed
#print axioms regionalAmplitude_eq_of_closed
#print axioms regionalAmplitude_eq_sum_representatives
#print axioms interleavingAmplitude_eq_sum_count
#print axioms amplitudeCollection_eq_complete_iff
#print axioms amplitudeCollection_incomplete_of_open
#print axioms incomplete_never_zero
#print axioms incomplete_never_cancels
#print axioms interferenceVerdict_cancels_iff
#print axioms interferenceVerdict_incomplete_iff
#print axioms interferenceVerdict_complete_ne
#print axioms certifiesCancellation_iff
#print axioms certifiesReinforcement_iff
#print axioms certifiedAmplitude_eq_some_iff
#print axioms certifiedAmplitude_eq_zero_iff
#print axioms open_certifies_nothing
#print axioms regionPaths_arrival
#print axioms verdict_iff_query
#print axioms destructive_iff_query
#print axioms constructive_iff_query
#print axioms coherent_query
#print axioms query_refuses_arrival
#print axioms storeGuards_valid_frame
#print axioms reads_cannot_certify_cancellation
#print axioms reads_cannot_certify_reinforcement

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
