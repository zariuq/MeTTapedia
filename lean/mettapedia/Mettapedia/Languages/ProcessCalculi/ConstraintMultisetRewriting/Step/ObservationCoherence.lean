import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObservationViews
import Mettapedia.Algebra.RationalComplexAmplitude

/-!
# The coherence contract: discarding a record is not merging it

A family of branches carries amplitudes, a system end and an environment record for each branch.
The joint amplitude at a system end and a record adds the amplitudes of the branches that leave
both (`joint`). Tracing out the environment gives the **reduced density** of the system
(`density`), whose diagonal is the **weight** of a system end (`weight`, `density_diag`).

## Discarding a record does not restore interference

* **Records read classically** (`weight_of_records`): when every branch has its own record, the
  weight is the classical sum of the branch weights.
* **A branch with its own record does not interfere** (`density_rephase`): changing its phase leaves
  the whole reduced density unchanged. Interference is sensitivity to relative phase, and a record
  left in an unobserved environment removes it, whether or not anyone reads the record.
* **Forgetting is not discarding** (`Controls.discard_is_not_forgetting`): the readout that pretends
  the environment holds no record (`forgetful`) reads `0` for the amplitudes `1` and `-1` where the
  discarded environment reads `2`.

## Coherent merge is an operation on the joint amplitude

* **A coherent merge** maps the records before the environment is traced out
  (`density_merge_of_constant`): when it sends every record to one value, the reduced density is
  the pure density of the summed amplitudes, and the weight is the forgetful readout
  (`weight_merge_of_constant`).
* **A merge of distinct records is not norm preserving** (`Controls.merge_not_norm_preserving`): the
  total weight of `1` and `-1` goes from `2` to `0`. A unitary evolution cannot merge orthogonal
  records; it can only move them.
* **A physical eraser reads the records in a complementary basis**
  (`fringe_add_antifringe`): the two conditional readouts, fringe and antifringe, add up to the
  decohered weight, so the interference appears only conditioned on the eraser's outcome.

## The eraser of the run layer is a coherent merge by construction

An eraser takes a record row and makes a common row (`eraser`). From states that differ only in
which record they hold, the erasers reach one configuration class (`eraser_merges`), so the end
after erasing is a merge that is constant on the records, and the erased family reads with its
pure density (`eraser_restores`). The erasers of R41 are instances: each is admitted after its
alternative (`Controls.eraser_valid_first`, `Controls.eraser_valid_second`), they merge the two ends
(`Controls.erased_ends_merge`), and the erased pair cancels even read by identities
(`Controls.erased_superposed_cancel`).

## Interference restated with private equivalence

The client-respecting end of a history is its configuration class up to private renaming for the
client's escaped identities (`Observation.privateEnd`). A firing and its alternative under a fresh
name (`alternativeEnd`) interfere for every client that has seen neither name
(`alternatives_interfere`), and read classically for a client that holds the first name
(`alternatives_recorded`). The superposed pair of R27 and R33 is such a pair: the alternative making
row `20` and the one making row `21`. With the amplitudes `1` and `-1` it reads `0` when its rows
are private and `2` when the row `20` escaped (`Controls.superposed_private`,
`Controls.superposed_escaped`).
For every client, the pair's two ends are one exactly when neither row has escaped
(`alternativeEnd_eq_iff`, `Controls.superposed_interferes_iff`).

A history's escapes belong to its end. Two histories that end in one state, one of which recorded
its row as evidence before consuming it, cancel when read by their states and add classically when
read by their joint ends (`Controls.evidence_suppresses_interference`): forgetting the row does not
unescape it. A ledger that names only a fresh identity is a record exactly when that identity was
public before (`Controls.fresh_evidence_relative`).

## What a physical interpretation needs in addition

The weights here are exact readouts of a chosen semantics. A physical reading additionally needs:
a Hilbert space whose orthonormal basis is the joint ends (states up to the client-respecting
equivalence, together with the environment's records); evolution by isometries, which the calculus
does not impose on amplitudes and which forbids merging distinct records; a measurement that reads
the records in a complementary basis, with readouts conditioned on its outcome; normalization of
the Born weights; and an environment that records nothing further after the merge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Coherence

open Mettapedia.Algebra.RationalComplexAmplitude (Amplitude born born_formula)
open scoped QuadraticAlgebra

/-! ## The reduced density -/

section Density

variable {ι : Type*} {X : Type*} {R : Type*} [DecidableEq X] [DecidableEq R]
variable (sys : ι → X) (env : ι → R) (amp : ι → Amplitude) (branches : Finset ι)

/-- **The joint amplitude** at a system end and an environment record: amplitudes add over the
branches that leave both. -/
def joint (x : X) (r : R) : Amplitude :=
  ∑ b ∈ branches.filter (fun b => sys b = x ∧ env b = r), amp b

/-- **The reduced density of the system**: the environment's records traced out. -/
def density (x y : X) : Amplitude :=
  ∑ r ∈ branches.image env, joint sys env amp branches x r * star (joint sys env amp branches y r)

/-- **The weight of a system end** once the environment is discarded. -/
def weight (x : X) : ℚ :=
  ∑ r ∈ branches.image env, born (joint sys env amp branches x r)

/-- **The forgetful readout**: the weight computed as if the environment held no record. -/
def forgetful (x : X) : ℚ :=
  born (∑ b ∈ branches.filter (fun b => sys b = x), amp b)

/-- **The diagonal of the reduced density is the weight.** -/
theorem density_diag (x : X) :
    density sys env amp branches x x = algebraMap ℚ Amplitude (weight sys env amp branches x) := by
  unfold density weight
  rw [map_sum]
  exact Finset.sum_congr rfl fun r _ => (QuadraticAlgebra.algebraMap_norm_eq_mul_star _).symm

theorem born_sum_of_subsingleton {s : Finset ι} (single : ∀ b ∈ s, ∀ b' ∈ s, b = b') :
    born (∑ b ∈ s, amp b) = ∑ b ∈ s, born (amp b) := by
  rcases s.eq_empty_or_nonempty with empty | ⟨b, member⟩
  · rw [empty, Finset.sum_empty, Finset.sum_empty]
    exact QuadraticAlgebra.norm_zero
  · have one : s = {b} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨member, fun b' member' => single b' member' b member⟩
    rw [one, Finset.sum_singleton, Finset.sum_singleton]

/-- **Records read classically**: when every branch has its own record, the weight of a system end
is the classical sum of the weights of the branches that reach it. -/
theorem weight_of_records (records : Set.InjOn env branches) (x : X) :
    weight sys env amp branches x =
      ∑ b ∈ branches.filter (fun b => sys b = x), born (amp b) := by
  unfold weight joint
  have split : ∀ r, branches.filter (fun b => sys b = x ∧ env b = r) =
      (branches.filter fun b => sys b = x).filter fun b => env b = r := by
    intro r
    rw [Finset.filter_filter]
  have each : ∀ r ∈ branches.image env,
      born (∑ b ∈ branches.filter (fun b => sys b = x ∧ env b = r), amp b) =
        ∑ b ∈ (branches.filter fun b => sys b = x).filter (fun b => env b = r), born (amp b) := by
    intro r _
    rw [split]
    refine born_sum_of_subsingleton amp fun b member b' member' => ?_
    simp only [Finset.mem_filter] at member member'
    exact records member.1.1 member'.1.1 (member.2.trans member'.2.symm)
  rw [Finset.sum_congr rfl each]
  exact Finset.sum_fiberwise_of_maps_to (fun b member =>
    Finset.mem_image_of_mem env (Finset.mem_filter.mp member).1) _

/-- **One record for every branch**: the weight is the forgetful readout, the Born weight of the
summed amplitudes. -/
theorem weight_of_one_record {r : R} (nonempty : branches.Nonempty)
    (shared : ∀ b ∈ branches, env b = r) (x : X) :
    weight sys env amp branches x = forgetful sys amp branches x := by
  have image : branches.image env = {r} := by
    ext r'
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨b, member, rfl⟩
      exact shared b member
    · rintro rfl
      obtain ⟨b, member⟩ := nonempty
      exact ⟨b, member, shared b member⟩
  have filters : branches.filter (fun b => sys b = x ∧ env b = r) =
      branches.filter fun b => sys b = x :=
    Finset.filter_congr fun b member => ⟨fun both => both.1, fun hit => ⟨hit, shared b member⟩⟩
  unfold weight joint forgetful
  rw [image, Finset.sum_singleton, filters]

variable [DecidableEq ι]

/-- **Multiply one branch's amplitude by a phase.** -/
def rephase (b₀ : ι) (u : Amplitude) : ι → Amplitude :=
  Function.update amp b₀ (u * amp b₀)

variable {sys env branches}

omit [DecidableEq ι] in
theorem joint_own {b₀ : ι} (member : b₀ ∈ branches) (own : ∀ b ∈ branches, env b = env b₀ → b = b₀)
    (amplitude : ι → Amplitude) (x : X) :
    joint sys env amplitude branches x (env b₀) = if sys b₀ = x then amplitude b₀ else 0 := by
  unfold joint
  split_ifs with hit
  · rw [Finset.sum_eq_single_of_mem b₀ (Finset.mem_filter.mpr ⟨member, hit, rfl⟩)]
    intro b inFilter apart
    exact absurd (own b (Finset.mem_filter.mp inFilter).1 (Finset.mem_filter.mp inFilter).2.2) apart
  · refine Finset.sum_eq_zero fun b inFilter => ?_
    obtain ⟨inBranches, reaches, recorded⟩ := Finset.mem_filter.mp inFilter
    have same := own b inBranches recorded
    subst same
    exact absurd reaches hit

theorem joint_rephase_other {b₀ : ι} {r : R} (other : r ≠ env b₀) (u : Amplitude) (x : X) :
    joint sys env (rephase amp b₀ u) branches x r = joint sys env amp branches x r := by
  unfold joint
  refine Finset.sum_congr rfl fun b inFilter => ?_
  have apart : b ≠ b₀ := by
    rintro rfl
    exact other (Finset.mem_filter.mp inFilter).2.2.symm
  exact Function.update_of_ne apart _ _

/-- **A branch with its own record does not interfere**: changing its phase leaves the reduced
density of the system unchanged. -/
theorem density_rephase {b₀ : ι} (member : b₀ ∈ branches)
    (own : ∀ b ∈ branches, env b = env b₀ → b = b₀) {u : Amplitude} (unit : born u = 1)
    (x y : X) :
    density sys env (rephase amp b₀ u) branches x y = density sys env amp branches x y := by
  have unitary : u * star u = 1 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    show algebraMap ℚ Amplitude (born u) = 1
    rw [unit, map_one]
  unfold density
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases mine : r = env b₀
  · subst mine
    rw [joint_own member own, joint_own member own, joint_own member own, joint_own member own]
    have moved : rephase amp b₀ u b₀ = u * amp b₀ := Function.update_self _ _ _
    rw [moved]
    split_ifs
    · rw [star_mul']
      calc u * amp b₀ * (star u * star (amp b₀)) = (u * star u) * (amp b₀ * star (amp b₀)) := by ring
        _ = amp b₀ * star (amp b₀) := by rw [unitary, one_mul]
    · simp
    · simp
    · simp
  · rw [joint_rephase_other amp mine u x, joint_rephase_other amp mine u y]

/-- **Its weight is unchanged**, whatever the phase. -/
theorem weight_rephase {b₀ : ι} (member : b₀ ∈ branches)
    (own : ∀ b ∈ branches, env b = env b₀ → b = b₀) {u : Amplitude} (unit : born u = 1) (x : X) :
    weight sys env (rephase amp b₀ u) branches x = weight sys env amp branches x := by
  have diag := density_rephase (sys := sys) amp member own unit x x
  rw [density_diag, density_diag] at diag
  exact (algebraMap ℚ Amplitude).injective diag

end Density

/-! ## Coherent merge -/

section Merge

variable {ι : Type*} {X : Type*} {R : Type*} {R' : Type*} [DecidableEq X] [DecidableEq R']
variable (sys : ι → X) (env : ι → R) (amp : ι → Amplitude) (branches : Finset ι)

/-- **A coherent merge that sends every record to one value restores the pure density**: it acts on
the joint amplitude before the environment is traced out. -/
theorem density_merge_of_constant (merge : R → R') (nonempty : branches.Nonempty)
    (constant : ∀ b ∈ branches, ∀ b' ∈ branches, merge (env b) = merge (env b')) (x y : X) :
    density sys (fun b => merge (env b)) amp branches x y =
      (∑ b ∈ branches.filter (fun b => sys b = x), amp b) *
        star (∑ b ∈ branches.filter (fun b => sys b = y), amp b) := by
  obtain ⟨b₁, member⟩ := nonempty
  have image : branches.image (fun b => merge (env b)) = {merge (env b₁)} := by
    ext r'
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨b, inBranches, rfl⟩
      exact constant b inBranches b₁ member
    · rintro rfl
      exact ⟨b₁, member, rfl⟩
  have filters : ∀ z : X, branches.filter (fun b => sys b = z ∧ merge (env b) = merge (env b₁)) =
      branches.filter fun b => sys b = z := fun z =>
    Finset.filter_congr fun b inBranches =>
      ⟨fun both => both.1, fun hit => ⟨hit, constant b inBranches b₁ member⟩⟩
  unfold density joint
  rw [image, Finset.sum_singleton, filters x, filters y]

/-- **Its weight is the forgetful readout.** -/
theorem weight_merge_of_constant (merge : R → R') (nonempty : branches.Nonempty)
    (constant : ∀ b ∈ branches, ∀ b' ∈ branches, merge (env b) = merge (env b')) (x : X) :
    weight sys (fun b => merge (env b)) amp branches x = forgetful sys amp branches x := by
  obtain ⟨b₁, member⟩ := nonempty
  exact weight_of_one_record sys (fun b => merge (env b)) amp branches ⟨b₁, member⟩
    (fun b inBranches => constant b inBranches b₁ member) x

/-- The parallelogram law of Born weights. -/
theorem born_add_add_born_sub (z w : Amplitude) :
    born (z + w) + born (z - w) = 2 * (born z + born w) := by
  simp only [born_formula, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
    QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub]
  ring

/-- **A physical eraser reads the records in a complementary basis.** With two records, the
readouts conditioned on the eraser's two outcomes, the fringe `born (j₁ + j₂) / 2` and the
antifringe `born (j₁ - j₂) / 2`, add up to the decohered weight: the interference appears only
conditioned on the outcome. -/
theorem fringe_add_antifringe (env : ι → R) [DecidableEq R] {r₁ r₂ : R} (apart : r₁ ≠ r₂)
    (records : branches.image env = {r₁, r₂}) (x : X) :
    born (joint sys env amp branches x r₁ + joint sys env amp branches x r₂) / 2 +
        born (joint sys env amp branches x r₁ - joint sys env amp branches x r₂) / 2 =
      weight sys env amp branches x := by
  have parallelogram := born_add_add_born_sub (joint sys env amp branches x r₁)
    (joint sys env amp branches x r₂)
  unfold weight
  rw [records, Finset.sum_pair apart]
  linarith

end Merge

/-! ## The eraser of the run layer -/

section RunLayer

open AnnotatedRuns
open GuardFreeProcessOrders (SameUpTo)

variable {T : Type*} {S : Type*} {O : Type*} [DecidableEq O]
  {A : SubstitutionAction T S} {label : O → T}

/-- **An eraser**: a firing that takes the record `record` and makes the common row `common`. -/
def eraser (rule : RuleInstance T) (record common : O) : Firing T S O :=
  ⟨rule, [], ⟨[record], [], [common]⟩⟩

omit [DecidableEq O] in
theorem equations_single {r r' : O} (labels : label r = label r') (patterns : List T) :
    Selection.equations label patterns [r] = Selection.equations label patterns [r'] := by
  cases patterns with
  | nil => rfl
  | cons pattern rest =>
      cases rest <;> simp [Selection.equations, labels]

theorem fire_eraser {K : Finset O} {r c : O} (outside : r ∉ K) :
    MeTTaCalculus.OccurrenceCommits.fire (insert r K)
        ((⟨[r], [], [c]⟩ : Selection O).commit (T := T)) = K ∪ {c} := by
  ext o
  simp only [MeTTaCalculus.OccurrenceCommits.mem_fire, Selection.commit, List.toFinset_cons,
    List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false, Finset.mem_union,
    Finset.mem_singleton]
  constructor
  · rintro (⟨inserted | inK, notR⟩ | isC)
    · exact absurd inserted notR
    · exact Or.inl inK
    · exact Or.inr isC
  · rintro (inK | isC)
    · exact Or.inl ⟨Or.inr inK, fun isR => outside (isR ▸ inK)⟩
    · exact Or.inr isC

/-- **The eraser is a coherent merge by construction**: from states that differ only in which record
they hold, erasing the records into one common row reaches one configuration class. -/
theorem eraser_merges (rule : RuleInstance T) {first second : EquationStore T}
    (same : A.Equivalent first second) {K : Finset O} {r₁ r₂ c : O} (out₁ : r₁ ∉ K)
    (out₂ : r₂ ∉ K) (labels : label r₁ = label r₂) :
    SameUpTo A ((eraser rule r₁ c : Firing T S O).result label ⟨first, insert r₁ K⟩)
      ((eraser rule r₂ c : Firing T S O).result label ⟨second, insert r₂ K⟩) := by
  refine ⟨fun σ => ?_, ?_⟩
  · show A.Models σ (first ++ Selection.equations label rule.take [r₁] ++
        Selection.equations label rule.read [] ++ rule.tell) ↔
      A.Models σ (second ++ Selection.equations label rule.take [r₂] ++
        Selection.equations label rule.read [] ++ rule.tell)
    rw [equations_single labels rule.take]
    simp only [SubstitutionAction.models_append, same σ]
  · show MeTTaCalculus.OccurrenceCommits.fire (insert r₁ K) ((⟨[r₁], [], [c]⟩ : Selection O).commit (T := T)) =
      MeTTaCalculus.OccurrenceCommits.fire (insert r₂ K) ((⟨[r₂], [], [c]⟩ : Selection O).commit (T := T))
    rw [fire_eraser out₁, fire_eraser out₂]

open Classical in
/-- **The erased family reads with its pure density**: when each branch's record is a row outside
a common context, all rows of one label, erasing the records into one common row merges them, and
the reduced density of the system is the pure density of the summed amplitudes. -/
theorem eraser_restores {ι X : Type*} [DecidableEq X] (sys : ι → X) (amp : ι → Amplitude)
    {branches : Finset ι} (nonempty : branches.Nonempty) (rule : RuleInstance T)
    (store : EquationStore T) (K : Finset O) (common : O) (record : ι → O)
    (outside : ∀ b ∈ branches, record b ∉ K)
    (labels : ∀ b ∈ branches, ∀ b' ∈ branches, label (record b) = label (record b')) (x y : X) :
    density sys (fun b => ConfigurationClass.mk A
        ((eraser rule (record b) common : Firing T S O).result label ⟨store, insert (record b) K⟩))
      amp branches x y =
      (∑ b ∈ branches.filter (fun b => sys b = x), amp b) *
        star (∑ b ∈ branches.filter (fun b => sys b = y), amp b) :=
  density_merge_of_constant sys record amp branches
    (fun r => ConfigurationClass.mk A
      ((eraser rule r common : Firing T S O).result label ⟨store, insert r K⟩))
    nonempty (fun b member b' member' => Quotient.sound
      (eraser_merges (first := store) (second := store) rule (fun _ => Iff.rfl) (outside b member)
        (outside b' member') (labels b member b' member'))) x y

end RunLayer

/-! ## Interference restated with private equivalence -/

section Interference

open AnnotatedRuns Observation

variable {T : Type*} {S : Type*} {O : Type*} [DecidableEq O]
  {A : SubstitutionAction T S} {label : O → T}

/-- **The ends of a firing and of its alternative under a fresh name**, read by a client whose
escaped identities are `E`. -/
def alternativeEnd (A : SubstitutionAction T S) (label : O → T) (E : Finset O)
    (f : Firing T S O) (C : Configuration T O) (r r' : O) :
    Bool → Quotient (classSetoid A label E)
  | false => privateEnd A label E (ConfigurationClass.mk A (f.result label C))
  | true => privateEnd A label E
      (ConfigurationClass.mk A ((f.rename (Equiv.swap r r')).result label C))

/-- Two branches with one record read their summed amplitude. -/
theorem weight_pair_shared {R : Type*} [DecidableEq R] (env : Bool → R) (shared : env false = env true)
    (amp : Bool → Amplitude) :
    weight (fun _ => ()) env amp Finset.univ () = born (amp false + amp true) := by
  rw [weight_of_one_record (fun _ => ()) env amp Finset.univ Finset.univ_nonempty
    (r := env false) (fun b _ => by cases b <;> simp [shared])]
  unfold forgetful
  rw [Finset.filter_true_of_mem fun _ _ => rfl, Fintype.sum_bool, add_comm]

/-- Two branches with different records read classically. -/
theorem weight_pair_apart {R : Type*} [DecidableEq R] (env : Bool → R) (apart : env false ≠ env true)
    (amp : Bool → Amplitude) :
    weight (fun _ => ()) env amp Finset.univ () = born (amp false) + born (amp true) := by
  have records : Set.InjOn env (Finset.univ : Finset Bool) := by
    intro b _ b' _ same
    cases b <;> cases b' <;> first | rfl | exact absurd same apart | exact absurd same.symm apart
  rw [weight_of_records (fun _ => ()) env amp Finset.univ records,
    Finset.filter_true_of_mem fun _ _ => rfl, Fintype.sum_bool, add_comm]

variable {f : Firing T S O} {C : Configuration T O} {r r' : O} {E : Finset O}

open Classical in
/-- **Unseen fresh names interfere**: for a client that has seen neither name, the two ends are one
end, and the amplitudes add. -/
theorem alternatives_interfere (valid : f.Valid A label C) (made : r ∈ f.selection.made)
    (absent : r' ∉ C.present) (same : label r' = label r) (unseen : r ∉ E) (unseen' : r' ∉ E)
    (amp : Bool → Amplitude) :
    weight (fun _ => ()) (alternativeEnd A label E f C r r') amp Finset.univ () =
      born (amp false + amp true) :=
  weight_pair_shared _ ((privateEnd_eq_iff A label E (ConfigurationClass.mk A (f.result label C))
    (ConfigurationClass.mk A ((f.rename (Equiv.swap r r')).result label C))).mpr
    (fresh_alternative_equivalent valid made absent same unseen unseen')) amp

open Classical in
/-- **A held fresh name records the alternative**: for a client holding the first name, the two
ends differ, and the weights add. -/
theorem alternatives_recorded (valid : f.Valid A label C) (made : r ∈ f.selection.made)
    (absent : r' ∉ C.present) (same : label r' = label r) (new : r' ∉ f.names) (seen : r ∈ E)
    (amp : Bool → Amplitude) :
    weight (fun _ => ()) (alternativeEnd A label E f C r r') amp Finset.univ () =
      born (amp false) + born (amp true) :=
  weight_pair_apart _ (fun ends => fresh_alternative_separated valid made absent same new seen
    ((privateEnd_eq_iff A label E (ConfigurationClass.mk A (f.result label C))
      (ConfigurationClass.mk A ((f.rename (Equiv.swap r r')).result label C))).mp ends)) amp

/-- **The two ends are one exactly when neither name has escaped.** -/
theorem alternativeEnd_eq_iff (valid : f.Valid A label C) (made : r ∈ f.selection.made)
    (absent : r' ∉ C.present) (same : label r' = label r) (new : r' ∉ f.names) :
    alternativeEnd A label E f C r r' false = alternativeEnd A label E f C r r' true ↔
      r ∉ E ∧ r' ∉ E :=
  (privateEnd_eq_iff A label E (ConfigurationClass.mk A (f.result label C))
    (ConfigurationClass.mk A ((f.rename (Equiv.swap r r')).result label C))).trans
    (fresh_alternative_equivalent_iff valid made absent same new)

end Interference

/-! ## Controls -/

namespace Controls

open AnnotatedRuns Observation
open GuardFreeProcessOrders (SameUpTo)
open ConstraintMultisetRewriting.Controls (A)
open AnnotatedRuns.Controls (label Run zeros)

/-! ### Discarding, forgetting and merging two records -/

/-- The amplitudes `1` and `-1`. -/
def opposite : Bool → Amplitude := fun b => if b then -1 else 1

/-- **Forgetting is not discarding**: with a record for each branch the discarded environment
reads `2`, and the forgetful readout reads `0`. -/
theorem discard_is_not_forgetting :
    weight (fun _ : Bool => ()) id opposite Finset.univ () = 2 ∧
      forgetful (fun _ : Bool => ()) opposite Finset.univ () = 0 := by
  refine ⟨?_, ?_⟩
  · rw [weight_pair_apart id (by decide) opposite]
    norm_num [opposite, born_formula]
  · unfold forgetful
    rw [Finset.filter_true_of_mem fun _ _ => rfl, Fintype.sum_bool]
    norm_num [opposite, born_formula]

/-- **The phase of a recorded branch is invisible**: rephasing the branch `true` by `-1` leaves the
discarded weight at `2`, while the forgetful readout moves from `0` to `4`. -/
theorem recorded_phase_invisible :
    weight (fun _ : Bool => ()) id (rephase opposite true (-1)) Finset.univ () = 2 ∧
      forgetful (fun _ : Bool => ()) (rephase opposite true (-1)) Finset.univ () = 4 := by
  refine ⟨?_, ?_⟩
  · rw [weight_rephase (env := id) (u := -1) opposite (Finset.mem_univ true) (fun b _ same => same)
      (by norm_num [born_formula])]
    exact discard_is_not_forgetting.1
  · unfold forgetful
    rw [Finset.filter_true_of_mem fun _ _ => rfl, Fintype.sum_bool]
    norm_num [rephase, opposite, born_formula]

/-- **A merge of distinct records is not norm preserving**: the total weight of `1` and `-1` goes
from `2`, records discarded, to `0`, records merged. -/
theorem merge_not_norm_preserving :
    weight (fun _ : Bool => ()) id opposite Finset.univ () = 2 ∧
      weight (fun _ : Bool => ()) (fun _ : Bool => ()) opposite Finset.univ () = 0 := by
  refine ⟨discard_is_not_forgetting.1, ?_⟩
  rw [weight_merge_of_constant (fun _ : Bool => ()) id opposite Finset.univ (fun _ : Bool => ())
    Finset.univ_nonempty (fun _ _ _ _ => rfl)]
  exact discard_is_not_forgetting.2

/-! ### The superposed pair -/

/-- The superposition token `9`. -/
def token : Configuration (Mettapedia.Logic.LP.Term ConstraintMultisetRewriting.Controls.signature) ℕ :=
  ⟨[], {9}⟩

/-- **The first superposed alternative** of R27 and R33: it takes the token and makes the answer row
`20`. The second makes the row `21` and is its renaming by the swap of `20` and `21`. -/
def superposed : Run := ⟨⟨[.const 9], [], [], [], [.const 2]⟩, [], ⟨[9], [], [20]⟩⟩

theorem superposed_valid : superposed.Valid A label token := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [superposed]⟩,
    by simp [superposed]⟩
  intro equation member
  have same : equation = (.const 9, label 9) := by
    simpa [Selection.problem, Selection.equations, token, superposed] using member
  subst same
  rfl

theorem second_alternative :
    superposed.rename (Equiv.swap 20 21) = ⟨⟨[.const 9], [], [], [], [.const 2]⟩, [], ⟨[9], [], [21]⟩⟩ := by
  simp [superposed, Firing.rename, renameSelection, Equiv.swap_apply_of_ne_of_ne]

open Classical in
/-- **Private rows interfere**: the amplitudes `1` and `-1` read `0`. -/
theorem superposed_private :
    weight (fun _ => ()) (alternativeEnd A label ∅ superposed token 20 21) opposite Finset.univ () = 0 := by
  rw [alternatives_interfere (r := 20) (r' := 21) superposed_valid (by simp [superposed]) (by decide) rfl
    (Finset.notMem_empty _) (Finset.notMem_empty _)]
  norm_num [opposite, born_formula]

/-- **The superposed pair interferes exactly when neither of its rows has escaped**, for every
client. -/
theorem superposed_interferes_iff (E : Finset ℕ) :
    alternativeEnd A label E superposed token 20 21 false =
        alternativeEnd A label E superposed token 20 21 true ↔ 20 ∉ E ∧ 21 ∉ E :=
  alternativeEnd_eq_iff (r := 20) (r' := 21) superposed_valid (by simp [superposed]) (by decide) rfl
    (by simp [Firing.names, superposed, sighted])

open Classical in
/-- **An escaped row records the alternative**: for a client holding the row `20`, the amplitudes
`1` and `-1` read `2`. -/
theorem superposed_escaped :
    weight (fun _ => ()) (alternativeEnd A label {20} superposed token 20 21) opposite Finset.univ () = 2 := by
  rw [alternatives_recorded (r := 20) (r' := 21) superposed_valid (by simp [superposed]) (by decide) rfl
    (by simp [Firing.names, superposed, sighted]) (Finset.mem_singleton_self 20)]
  norm_num [opposite, born_formula]

/-! ### The superposed pair erased -/

/-- The rule of the erasers of R41: take a row of label `2` and make a row of label `2`. -/
def eraseRule : RuleInstance (Mettapedia.Logic.LP.Term ConstraintMultisetRewriting.Controls.signature) :=
  ⟨[.const 2], [], [], [], [.const 2]⟩

theorem superposed_result :
    superposed.result label token = ⟨[(.const 9, label 9)], insert 20 ∅⟩ := by
  refine congrArg₂ Configuration.mk rfl ?_
  decide

theorem alternative_result :
    (superposed.rename (Equiv.swap 20 21)).result label token = ⟨[(.const 9, label 9)], insert 21 ∅⟩ := by
  refine congrArg₂ Configuration.mk rfl ?_
  decide

/-- **The eraser of the row `20` is admitted** after the first alternative. -/
theorem eraser_valid_first :
    (eraser eraseRule 20 30 : Run).Valid A label (superposed.result label token) := by
  rw [superposed_result]
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [eraser, eraseRule]⟩,
    by simp [eraser]⟩
  intro equation member
  have cases : equation = (.const 9, label 9) ∨ equation = (.const 2, label 20) := by
    simpa [Selection.problem, Selection.equations, eraser, eraseRule] using member
  rcases cases with rfl | rfl <;> rfl

/-- **The eraser of the row `21` is admitted** after the second alternative. -/
theorem eraser_valid_second :
    (eraser eraseRule 21 30 : Run).Valid A label ((superposed.rename (Equiv.swap 20 21)).result label token) := by
  rw [alternative_result]
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [eraser, eraseRule]⟩,
    by simp [eraser]⟩
  intro equation member
  have cases : equation = (.const 9, label 9) ∨ equation = (.const 2, label 21) := by
    simpa [Selection.problem, Selection.equations, eraser, eraseRule] using member
  rcases cases with rfl | rfl <;> rfl

/-- **The erasers merge the two ends.** -/
theorem erased_ends_merge :
    SameUpTo A ((eraser eraseRule 20 30 : Run).result label (superposed.result label token))
      ((eraser eraseRule 21 30 : Run).result label
        ((superposed.rename (Equiv.swap 20 21)).result label token)) := by
  rw [superposed_result, alternative_result]
  exact eraser_merges eraseRule (fun _ => Iff.rfl) (Finset.notMem_empty 20) (Finset.notMem_empty 21) rfl

open Classical in
/-- **Erased, the superposed pair cancels for every client**: the identity end of each history after
its eraser is one configuration class, and the amplitudes `1` and `-1` read `0`. -/
theorem erased_superposed_cancel :
    weight (fun _ : Bool => ())
        (fun b => ConfigurationClass.mk A (if b then
          (eraser eraseRule 21 30 : Run).result label
            ((superposed.rename (Equiv.swap 20 21)).result label token)
          else (eraser eraseRule 20 30 : Run).result label (superposed.result label token)))
        opposite Finset.univ () = 0 := by
  rw [weight_pair_shared
    (fun b => ConfigurationClass.mk A (if b then
      (eraser eraseRule 21 30 : Run).result label
        ((superposed.rename (Equiv.swap 20 21)).result label token)
      else (eraser eraseRule 20 30 : Run).result label (superposed.result label token)))
    (Quotient.sound erased_ends_merge) opposite]
  norm_num [opposite, born_formula]

/-! ### Records that escaped into evidence -/

open ObservationControls (erased)

/-- Joint ends up to joint equivalence. -/
def jointSetoid (E : Finset ℕ) :
    Setoid (Configuration (Mettapedia.Logic.LP.Term ConstraintMultisetRewriting.Controls.signature) ℕ ×
      Client ℕ) where
  r := JointEquivalent A label E
  iseqv := ⟨JointEquivalent.refl, JointEquivalent.symm, JointEquivalent.trans⟩

/-- A ledger holding one row as evidence. -/
def ledger (o : ℕ) : Client ℕ := ⟨[], ∅, {o}, ∅⟩

/-- The empty ledger. -/
def noLedger : Client ℕ := ⟨[], ∅, ∅, ∅⟩

open Classical in
/-- **A record that escaped into evidence and was then consumed still suppresses interference.** Two
histories end in the same state; one recorded its row `20` as evidence before consuming it, the
other recorded nothing. Read by their states alone the amplitudes `1` and `-1` cancel; read by their
joint ends they add classically. -/
theorem evidence_suppresses_interference :
    weight (fun _ : Bool => ())
        (fun _ => privateEnd A label ∅ (ConfigurationClass.mk A erased)) opposite Finset.univ () = 0 ∧
      weight (fun _ : Bool => ())
        (fun b => Quotient.mk (jointSetoid ∅) (erased, if b then noLedger else ledger 20))
        opposite Finset.univ () = 2 := by
  refine ⟨?_, ?_⟩
  · rw [weight_pair_shared _ rfl opposite]
    norm_num [opposite, born_formula]
  · rw [weight_pair_apart (fun b => Quotient.mk (jointSetoid ∅) (erased, if b then noLedger else ledger 20))
      (fun same => ObservationControls.evidence_outlives_record.2 (Quotient.exact same)) opposite]
    norm_num [opposite, born_formula]

open Classical in
/-- **A ledger of a fresh name alone is no record**: two histories that each recorded their own
fresh row as evidence and consumed it interfere when neither row was public before, and add
classically once the row `20` was. -/
theorem fresh_evidence_relative :
    weight (fun _ : Bool => ())
        (fun b => Quotient.mk (jointSetoid ∅) (erased, if b then ledger 21 else ledger 20))
        opposite Finset.univ () = 0 ∧
      weight (fun _ : Bool => ())
        (fun b => Quotient.mk (jointSetoid {20}) (erased, if b then ledger 21 else ledger 20))
        opposite Finset.univ () = 2 := by
  refine ⟨?_, ?_⟩
  · rw [weight_pair_shared (fun b => Quotient.mk (jointSetoid ∅) (erased, if b then ledger 21 else ledger 20))
      (Quotient.sound ObservationControls.fresh_records_relative.1) opposite]
    norm_num [opposite, born_formula]
  · rw [weight_pair_apart
      (fun b => Quotient.mk (jointSetoid {20}) (erased, if b then ledger 21 else ledger 20))
      (fun same => ObservationControls.fresh_records_relative.2 (Quotient.exact same)) opposite]
    norm_num [opposite, born_formula]

end Controls

#print axioms density_diag
#print axioms born_sum_of_subsingleton
#print axioms weight_of_records
#print axioms weight_of_one_record
#print axioms joint_own
#print axioms density_rephase
#print axioms weight_rephase
#print axioms density_merge_of_constant
#print axioms weight_merge_of_constant
#print axioms born_add_add_born_sub
#print axioms fringe_add_antifringe
#print axioms eraser_merges
#print axioms eraser_restores
#print axioms weight_pair_shared
#print axioms weight_pair_apart
#print axioms alternatives_interfere
#print axioms alternatives_recorded
#print axioms alternativeEnd_eq_iff
#print axioms Controls.discard_is_not_forgetting
#print axioms Controls.recorded_phase_invisible
#print axioms Controls.merge_not_norm_preserving
#print axioms Controls.superposed_valid
#print axioms Controls.second_alternative
#print axioms Controls.superposed_private
#print axioms Controls.superposed_escaped
#print axioms Controls.superposed_interferes_iff
#print axioms Controls.eraser_valid_first
#print axioms Controls.eraser_valid_second
#print axioms Controls.erased_ends_merge
#print axioms Controls.erased_superposed_cancel
#print axioms Controls.evidence_suppresses_interference
#print axioms Controls.fresh_evidence_relative

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Coherence
