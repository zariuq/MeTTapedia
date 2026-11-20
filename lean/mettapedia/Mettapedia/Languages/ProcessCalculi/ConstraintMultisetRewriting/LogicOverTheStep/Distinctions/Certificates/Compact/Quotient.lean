import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Lumping
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.OnTheStep

/-!
# Certificates on classes: a checked lumping and a certificate of the quotient

A **certificate on classes** (`OnClasses`) for a chain with rational masses on states `S` is a map
`view` of the states onto classes `C`, a chain on the classes, and a prefixpoint certificate of that
chain. The checker (`classCheck`) decides it in exact rational arithmetic:

* **the lumping** (`lumpCheck`): for every action, state and class, the mass the state's successor
  distribution puts on the fibre of the class is the quotient's mass from the state's class; and
  every observation of a state is that of its class. This is sums of masses and equalities: no
  product is computed;
* **the quotient** (`check` of `Upper`, unchanged): the prefixpoint certificate of the quotient chain.

**Soundness** (`classCheck_sound`): acceptance implies that the bisimulation metric of the chain read
in the reals is at most the quotient's kernel at the classes, at every discount `0 ≤ c`. The proof
reduces to the tree's theorems: the quotient's accepted certificate is a coupling bound
(`coreCheck_couplingBound`), it pulls back along the lumping (`couplingBound_lift`), and a rational
coupling bound bounds the real metric (`bisimulationMetric_le_real`).

**Exactness.** The metric of the chain is the metric of the quotient at the classes
(`bisimulationMetric_quotient`, at `0 < c ≤ 1`). So a dual post-fixpoint of the quotient that meets
its prefixpoint at two classes decides the distance of every pair of states in them
(`classCheck_exact_of_dual`, at `0 < c < 1`).

**On the transform step.** For rational data describing a closed region of step states, an accepted
certificate on classes of the region's chain bounds the region's behavioural metric
(`classCheck_sound_region`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact

open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.GSLT.Distinction.Probabilistic

variable {A Atom S C : Type*} [Fintype S] [Fintype C] [DecidableEq C]

/-! ## The certificate and its checker -/

/-- **A certificate on classes** for a chain with actions `A` and observations `Atom` on states `S`:
a map of the states onto classes `C`, a chain on the classes, and a prefixpoint certificate of that
chain. -/
structure OnClasses (A Atom S C : Type*) [Fintype C] where
  /-- The class of each state. -/
  view : S → C
  /-- The chain on the classes. -/
  quotient : LabelledMarkovChain ℚ A Atom C
  /-- The certificate of the chain on the classes. -/
  cert : Prefixpoint A C

section Checker

variable [Fintype A] [Fintype Atom]

/-- **The lumping check**: every successor distribution puts on each fibre the quotient's mass from
the state's class, and every observation of a state is that of its class. -/
def lumpCheck (P : LabelledMarkovChain ℚ A Atom S) (Q : LabelledMarkovChain ℚ A Atom C)
    (view : S → C) : Bool :=
  decide (∀ a s k, fibreMass view (P.trans a s) k = Q.trans a (view s) k) &&
    decide (∀ i s, P.observe i s = Q.observe i (view s))

/-- **The checker** of certificates on classes: the lumping, then the prefixpoint checker on the
quotient. -/
def classCheck (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ) (cert : OnClasses A Atom S C) : Bool :=
  lumpCheck P cert.quotient cert.view && check cert.quotient c cert.cert

variable {P : LabelledMarkovChain ℚ A Atom S} {Q : LabelledMarkovChain ℚ A Atom C} {view : S → C}

theorem lumpCheck_iff : lumpCheck P Q view = true ↔ IsLumping P Q view := by
  simp only [lumpCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨rows, readings⟩ => ⟨rows, readings⟩, fun lump => ⟨lump.trans_eq, lump.observe_eq⟩⟩

theorem classCheck_iff {c : ℚ} {cert : OnClasses A Atom S C} :
    classCheck P c cert = true ↔
      IsLumping P cert.quotient cert.view ∧ check cert.quotient c cert.cert = true := by
  simp only [classCheck, Bool.and_eq_true, lumpCheck_iff]

end Checker

/-! ## Rational lumpings read in the reals -/

/-- **A rational lumping is a lumping of the real chains.** -/
theorem isLumping_real {P : LabelledMarkovChain ℚ A Atom S} {Q : LabelledMarkovChain ℚ A Atom C}
    {view : S → C} (lump : IsLumping P Q view) :
    IsLumping (realChain P) (realChain Q) view where
  trans_eq a s k := by
    have rational := lump.trans_eq a s k
    simp only [fibreMass, realChain_trans] at rational ⊢
    exact_mod_cast rational
  observe_eq i s := by
    simp only [realChain_observe]
    exact_mod_cast lump.observe_eq i s

/-! ## Soundness and exactness -/

section Soundness

variable [Fintype A] [Fintype Atom] {P : LabelledMarkovChain ℚ A Atom S} {c : ℚ}
  {cert : OnClasses A Atom S C}

/-- **An accepted certificate gives a coupling bound of the chain**: the quotient's kernel with its
diagonal set to zero, read through the map, at every discount `0 ≤ c`. -/
theorem classCheck_couplingBound (accepted : classCheck P c cert = true) (c_nonneg : 0 ≤ c) :
    CouplingBound P P c fun s t => offDiagonal cert.cert.kernel (cert.view s) (cert.view t) := by
  obtain ⟨lump, quotientAccepted⟩ := classCheck_iff.mp accepted
  exact couplingBound_lift lump
    (coreCheck_couplingBound (check_iff.mp quotientAccepted).1 c_nonneg) c_nonneg

/-- **Soundness of the checker**: acceptance implies that the bisimulation metric of the real chain
is at most the quotient's kernel at the classes, at every discount `0 ≤ c`. -/
theorem classCheck_sound (accepted : classCheck P c cert = true) (c_nonneg : 0 ≤ c) (s t : S) :
    bisimulationMetric (realChain P) (realChain P) (c : ℝ) s t ≤
      (cert.cert.kernel (cert.view s) (cert.view t) : ℝ) := by
  obtain ⟨_, quotientAccepted⟩ := classCheck_iff.mp accepted
  refine (bisimulationMetric_le_real (classCheck_couplingBound accepted c_nonneg) c_nonneg s t).trans
    (Rat.cast_le.mpr ?_)
  exact offDiagonal_le (coreCheck_iff.mp (check_iff.mp quotientAccepted).1).1 _ _

/-- **The metric of the chain is the metric of the quotient** at the classes, at every discount
`0 < c ≤ 1`, when the map is a lumping. -/
theorem bisimulationMetric_quotient {Q : LabelledMarkovChain ℚ A Atom C} {view : S → C}
    (lump : IsLumping P Q view) (c_pos : 0 < c) (c_le : c ≤ 1) (s t : S) :
    bisimulationMetric (realChain P) (realChain P) (c : ℝ) s t =
      bisimulationMetric (realChain Q) (realChain Q) (c : ℝ) (view s) (view t) :=
  bisimulationMetric_lump (isLumping_real lump) (by exact_mod_cast c_pos) (by exact_mod_cast c_le) s t

/-- **Exact from the quotient's dual**: if a dual post-fixpoint of the quotient is accepted and meets
the quotient's kernel at the classes of two states, the distance of the two states is that rational,
at every discount `0 < c < 1`. -/
theorem classCheck_exact_of_dual (accepted : classCheck P c cert = true)
    {dual : DualPostfixpoint A C} (dualAccepted : dualCheck cert.quotient c dual = true) {s t : S}
    (meet : dual.kernel (cert.view s) (cert.view t) = cert.cert.kernel (cert.view s) (cert.view t))
    (c_pos : 0 < c) (c_lt : c < 1) :
    bisimulationMetric (realChain P) (realChain P) (c : ℝ) s t =
      (cert.cert.kernel (cert.view s) (cert.view t) : ℝ) := by
  refine le_antisymm (classCheck_sound accepted c_pos.le s t) ?_
  rw [bisimulationMetric_quotient (classCheck_iff.mp accepted).1 c_pos c_lt.le, ← meet]
  exact dualCheck_sound dualAccepted c_pos.le c_lt _ _

end Soundness

/-! ## On a region of the transform step -/

section Region

variable {State L V R : Type*} [Fintype R] [DecidableEq R] [Fintype L]
  {law : L → State → SubDistribution State} (region : ClosedRegion law R) (read : State → V)
  {data : RegionData L R}

/-- **An accepted certificate on classes of the region's chain bounds the region's behavioural
metric**, at every discount `0 ≤ c`. -/
theorem classCheck_sound_region (describes : data.Describes region read) {c : ℚ}
    {cert : OnClasses L (Option R) (Option R) C} (accepted : classCheck data.chain c cert = true)
    (c_nonneg : 0 ≤ c) (r r' : R) :
    behaviouralMetric (M := regionSystem region read) (c : ℝ) r r' ≤
      (cert.cert.kernel (cert.view (some r)) (cert.view (some r')) : ℝ) := by
  unfold behaviouralMetric
  rw [completion_eq_realChain region read describes]
  exact classCheck_sound accepted c_nonneg (some r) (some r')

end Region

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact
