import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.BorrowedSteps
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CommFootprint

/-!
# Binary steps cannot break symmetry

Rho's COMM takes one output and one input. Steps of that kind cannot elect one of two parties
that start in mirror-image positions: whatever one party can do, the other can do next, and the
configuration is a mirror image again. A step that takes two items at once (a Rholang join, or a
step taking several atoms) breaks the tie.

## Words

* **Mirror** (`Mirror`): an involution `σ` on atoms, swapping the two parties. Example: swap
  `fork a` with `fork b` and `hungry a` with `hungry b`.
* **Split symmetric** configuration (`SplitSymmetric`): a part together with its mirror image
  (`splitSymmetric_add_mirror`). Every atom occurs as often as its mirror, and an atom that is its
  own mirror an even number of times.
* **Binary** bag (`Binary`): it never holds an atom together with a different mirror image of it,
  and holds an atom that is its own mirror at most once. A COMM's redex, one output and one input,
  is binary for every mirror that maps outputs to outputs and inputs to inputs
  (`binary_of_kinds`, `commRule_binary`).
* **Maximal run** (`MaximalRun`): each configuration steps to the next, or nothing can step and the
  run stays where it is.
* **Elects** (`Elects`): every maximal run shows exactly one of the two announcements.

## Results

* `mirror_step`: from a split symmetric configuration, a binary step followed by its mirror image
  lands in a split symmetric configuration, and everything the first step made is mirrored there.
* `exists_symmetric_maximal_run`: under a family of positive binary rules closed under the mirror,
  every split symmetric configuration has a maximal run along which an atom is ever shown exactly
  when its mirror is.
* `no_symmetric_election`: such a family elects no leader from a split symmetric configuration.
* `rho_no_symmetric_election`: rho's COMM, read as a local bag rule (`CommFootprint`), whose steps
  are rho reductions (`rhoComm_reduces`), elects no leader from a split symmetric configuration,
  for every mirror that maps outputs to outputs, inputs to inputs and COMM instances to COMM
  instances. Name permutations are meant to be such mirrors; the equivariance of rho's
  substitution under them is a hypothesis here, not proved.

## Controls

* Two philosophers and two forks (`Table`). Binary rules (take your fork, then the other one):
  `binaryTable_family`, hence `binaryTable_no_election`; the symmetric run deadlocks
  (`binaryTable_deadlock`).
* Join rules (take both forks at once) elect: `joinTable_elects`. The join's redex is not binary
  (`joinRule_not_binary`): it holds `fork a` and its mirror `fork b`.

The theorem is Bougé's and Palamidessi's symmetry argument (CSP without output guards, the
asynchronous pi-calculus with separate choice) restated for bag rules; it is stated here for
every maximal run, not only for fair ones.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Weaknesses.Symmetry

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence (Rule Reduces)

variable {R : Type*} [DecidableEq R]

/-! ## Mirrors and symmetric configurations -/

/-- An involution swapping the two parties. -/
structure Mirror (R : Type*) where
  σ : R → R
  invol : ∀ x, σ (σ x) = x

namespace Mirror

omit [DecidableEq R] in
theorem injective (m : Mirror R) : Function.Injective m.σ := fun a b h => by
  simpa [m.invol] using congrArg m.σ h

/-- Counting in a mirror image. -/
theorem count_map (m : Mirror R) (S : Multiset R) (y : R) :
    (S.map m.σ).count y = S.count (m.σ y) := by
  conv_lhs => rw [← m.invol y]
  exact Multiset.count_map_eq_count' m.σ S m.injective (m.σ y)

end Mirror

/-- A configuration is **split symmetric** when every atom occurs as often as its mirror image,
and an atom that is its own mirror an even number of times. -/
def SplitSymmetric (m : Mirror R) (M : Multiset R) : Prop :=
  ∀ y, M.count (m.σ y) = M.count y ∧ (m.σ y = y → Even (M.count y))

/-- **A part and its mirror image are split symmetric.** -/
theorem splitSymmetric_add_mirror (m : Mirror R) (N : Multiset R) :
    SplitSymmetric m (N + N.map m.σ) := by
  intro y
  simp only [Multiset.count_add, m.count_map, m.invol]
  refine ⟨by omega, fun fixed => ⟨N.count y, by rw [fixed]⟩⟩

/-- The mirror image of a rule. -/
def mirrorRule (m : Mirror R) (ρ : Rule R) : Rule R :=
  ⟨ρ.take.map m.σ, ρ.keep.map m.σ, ρ.make.map m.σ, fun x => ρ.closed (m.σ x)⟩

omit [DecidableEq R] in
theorem mirrorRule_redex (m : Mirror R) (ρ : Rule R) :
    (mirrorRule m ρ).redex = ρ.redex.map m.σ := by
  simp [mirrorRule, Rule.redex, Multiset.map_add]

omit [DecidableEq R] in
theorem mirrorRule_positive (m : Mirror R) {ρ : Rule R} (h : ρ.Positive) :
    (mirrorRule m ρ).Positive := fun x => h (m.σ x)

/-! ## Binary bags -/

/-- A bag is **binary** for a mirror when it never holds an atom together with a different mirror
image of it, and holds an atom that is its own mirror at most once. -/
def Binary (m : Mirror R) (T : Multiset R) : Prop :=
  ∀ x, 0 < T.count x → (m.σ x ≠ x → T.count (m.σ x) = 0) ∧ (m.σ x = x → T.count x = 1)

/-- **A binary bag and its mirror image fit together in a split symmetric configuration that
holds the bag.** -/
theorem binary_count_le (m : Mirror R) {T M : Multiset R} (hT : Binary m T) (le : T ≤ M)
    (hM : SplitSymmetric m M) (y : R) : T.count y + T.count (m.σ y) ≤ M.count y := by
  have hle := Multiset.le_iff_count.mp le
  by_cases fixed : m.σ y = y
  · rw [fixed]
    rcases Nat.eq_zero_or_pos (T.count y) with h0 | hpos
    · simp [h0]
    · have h1 := (hT y hpos).2 fixed
      have hy := hle y
      obtain ⟨k, hk⟩ := (hM y).2 fixed
      omega
  · rcases Nat.eq_zero_or_pos (T.count y) with h0 | hpos
    · have h := hle (m.σ y)
      rw [(hM y).1] at h
      omega
    · have h1 := (hT y hpos).1 fixed
      have h2 := hle y
      omega

/-- **Kinds make a bag binary.** If the mirror preserves a kind (outputs stay outputs, inputs stay
inputs) and the bag holds at most one atom of each kind, the bag is binary. -/
theorem binary_of_kinds {K : Type*} (m : Mirror R) (kind : R → K)
    (preserves : ∀ x, kind (m.σ x) = kind x) {T : Multiset R} (nodup : (T.map kind).Nodup) :
    Binary m T := by
  have tNodup : T.Nodup := Multiset.Nodup.of_map kind nodup
  have injOn := Multiset.inj_on_of_nodup_map nodup
  intro x hx
  have xMem : x ∈ T := Multiset.count_pos.mp hx
  refine ⟨fun moved => ?_, fun _ => Multiset.count_eq_one_of_mem tNodup xMem⟩
  by_contra nonzero
  have mirrorMem : m.σ x ∈ T := Multiset.count_pos.mp (Nat.pos_of_ne_zero nonzero)
  exact moved (injOn _ mirrorMem _ xMem (preserves x))

/-! ## One step and its mirror image -/

/-- **A binary step followed by its mirror image.** From a split symmetric configuration, the
mirror image of an enabled positive binary rule is enabled after it, the configuration reached is
split symmetric again, and it holds the mirror image of everything the first step made. -/
theorem mirror_step (m : Mirror R) {ρ : Rule R} (hpos : ρ.Positive) (hbin : Binary m ρ.redex)
    {M : Multiset R} (hM : SplitSymmetric m M) (enabled : ρ.Enabled M) :
    (mirrorRule m ρ).Enabled (ρ.result M) ∧
      SplitSymmetric m ((mirrorRule m ρ).result (ρ.result M)) ∧
      ρ.make.map m.σ ≤ (mirrorRule m ρ).result (ρ.result M) := by
  have le : ρ.redex ≤ M := ((Rule.enabled_iff_of_positive hpos M).mp enabled)
  have takeLe : ρ.take ≤ ρ.redex := Rule.take_le_redex ρ
  have takeCount := Multiset.le_iff_count.mp takeLe
  have fit := binary_count_le m hbin le hM
  have redexCount : ∀ y, ρ.redex.count y = ρ.take.count y + ρ.keep.count y := fun y => by
    simp [Rule.redex, Multiset.count_add]
  -- counts of the configuration after the first step and after its mirror
  have count1 : ∀ y, (ρ.result M).count y = M.count y - ρ.take.count y + ρ.make.count y :=
    fun y => by simp [Rule.result, Multiset.count_add, Multiset.count_sub]
  have count2 : ∀ y, ((mirrorRule m ρ).result (ρ.result M)).count y =
      (M.count y - ρ.take.count y + ρ.make.count y) - ρ.take.count (m.σ y) +
        ρ.make.count (m.σ y) := fun y => by
    simp [Rule.result, mirrorRule, Multiset.count_add, Multiset.count_sub, m.count_map]
  refine ⟨?_, ?_, ?_⟩
  · rw [Rule.enabled_iff_of_positive (mirrorRule_positive m hpos), mirrorRule_redex,
      Multiset.le_iff_count]
    intro y
    rw [m.count_map, count1]
    have h1 := fit y
    have h2 := takeCount y
    omega
  · intro y
    have hy := fit y
    have hσy := fit (m.σ y)
    rw [m.invol] at hσy
    have ty := takeCount y
    have tσy := takeCount (m.σ y)
    refine ⟨?_, fun fixed => ?_⟩
    · rw [count2, count2, m.invol, (hM y).1]
      omega
    · obtain ⟨k, hk⟩ := (hM y).2 fixed
      rw [count2, fixed]
      rw [fixed] at hy
      exact ⟨k - ρ.take.count y + ρ.make.count y, by omega⟩
  · exact Multiset.le_add_left _ _

/-! ## Runs -/

/-- Nothing can step. -/
def Stuck (Γ : Rule R → Prop) (M : Multiset R) : Prop := ∀ M', ¬ Reduces Γ M M'

/-- A maximal run: each configuration steps to the next, or nothing can step and the run stays. -/
def MaximalRun (Γ : Rule R → Prop) (f : ℕ → Multiset R) : Prop :=
  ∀ n, Reduces Γ (f n) (f (n + 1)) ∨ (Stuck Γ (f n) ∧ f (n + 1) = f n)

/-- The run shows the atom at some point. -/
def Shows (f : ℕ → Multiset R) (x : R) : Prop := ∃ n, x ∈ f n

/-- **Electing between two announcements**: every maximal run from `M` shows exactly one. -/
def Elects (Γ : Rule R → Prop) (M : Multiset R) (a b : R) : Prop :=
  ∀ f, MaximalRun Γ f → f 0 = M → (Shows f a ↔ ¬ Shows f b)

/-- A family of rules that the mirror maps into itself, all positive and binary. -/
structure BinaryFamily (m : Mirror R) (Γ : Rule R → Prop) : Prop where
  positive : ∀ ρ, Γ ρ → ρ.Positive
  equivariant : ∀ ρ, Γ ρ → Γ (mirrorRule m ρ)
  binary : ∀ ρ, Γ ρ → Binary m ρ.redex

section Run

variable (Γ : Rule R → Prop) (m : Mirror R)

open Classical in
/-- One round: some enabled rule, then its mirror image; or stay when nothing is enabled. -/
noncomputable def round (M : Multiset R) : Multiset R × Multiset R :=
  if h : ∃ ρ, Γ ρ ∧ ρ.Enabled M then
    ((Classical.choose h).result M,
      (mirrorRule m (Classical.choose h)).result ((Classical.choose h).result M))
  else (M, M)

variable {Γ m}

/-- What a round does from a split symmetric configuration. -/
theorem round_spec (fam : BinaryFamily m Γ) {M : Multiset R} (hM : SplitSymmetric m M) :
    (Reduces Γ M (round Γ m M).1 ∧ Reduces Γ (round Γ m M).1 (round Γ m M).2 ∧
        SplitSymmetric m (round Γ m M).2 ∧
        ∀ x ∈ (round Γ m M).1, m.σ x ∈ M ∨ m.σ x ∈ (round Γ m M).2) ∨
      (Stuck Γ M ∧ round Γ m M = (M, M)) := by
  by_cases h : ∃ ρ, Γ ρ ∧ ρ.Enabled M
  · left
    have hρ := Classical.choose_spec h
    set ρ := Classical.choose h with hρdef
    have hround : round Γ m M = (ρ.result M, (mirrorRule m ρ).result (ρ.result M)) := by
      simp only [round, dif_pos h, hρdef]
    obtain ⟨en2, sym2, made⟩ :=
      mirror_step m (fam.positive ρ hρ.1) (fam.binary ρ hρ.1) hM hρ.2
    rw [hround]
    refine ⟨⟨ρ, hρ.1, hρ.2, rfl⟩, ⟨mirrorRule m ρ, fam.equivariant ρ hρ.1, en2, rfl⟩, sym2, ?_⟩
    intro x hx
    simp only [Rule.result, Multiset.mem_add] at hx
    rcases hx with old | new
    · left
      have xM : x ∈ M := Multiset.mem_of_le (Multiset.sub_le_self _ _) old
      rw [← Multiset.count_pos, (hM x).1]
      exact Multiset.count_pos.mpr xM
    · right
      exact Multiset.mem_of_le made (Multiset.mem_map_of_mem _ new)
  · right
    refine ⟨fun M' ⟨ρ, member, enabled, _⟩ => h ⟨ρ, member, enabled⟩, ?_⟩
    simp only [round, dif_neg h]

variable (Γ m)

/-- The split symmetric configurations of the run. -/
noncomputable def symmetricStates (M : Multiset R) : ℕ → Multiset R
  | 0 => M
  | k + 1 => (round Γ m (symmetricStates M k)).2

/-- The run: the split symmetric configurations, with each round's middle configuration between. -/
noncomputable def symmetricRun (M : Multiset R) (n : ℕ) : Multiset R :=
  if n % 2 = 0 then symmetricStates Γ m M (n / 2) else (round Γ m (symmetricStates Γ m M (n / 2))).1

variable {Γ m}

theorem symmetricStates_symmetric (fam : BinaryFamily m Γ) {M : Multiset R}
    (hM : SplitSymmetric m M) (k : ℕ) : SplitSymmetric m (symmetricStates Γ m M k) := by
  induction k with
  | zero => exact hM
  | succ k ih =>
    rcases round_spec fam ih with ⟨_, _, sym, _⟩ | ⟨_, eq⟩
    · exact sym
    · simp only [symmetricStates, eq]
      exact ih

theorem symmetricRun_even (M : Multiset R) (k : ℕ) :
    symmetricRun Γ m M (2 * k) = symmetricStates Γ m M k := by
  simp [symmetricRun]

theorem symmetricRun_odd (M : Multiset R) (k : ℕ) :
    symmetricRun Γ m M (2 * k + 1) = (round Γ m (symmetricStates Γ m M k)).1 := by
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [symmetricRun, h1, h2]

/-- **Binary rules keep a symmetric start symmetric along a whole maximal run**: an atom is ever
shown exactly when its mirror image is. -/
theorem exists_symmetric_maximal_run (fam : BinaryFamily m Γ) {M : Multiset R}
    (hM : SplitSymmetric m M) :
    ∃ f : ℕ → Multiset R, MaximalRun Γ f ∧ f 0 = M ∧ ∀ x, Shows f x → Shows f (m.σ x) := by
  refine ⟨symmetricRun Γ m M, ?_, by simp [symmetricRun, symmetricStates], ?_⟩
  · intro n
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [symmetricRun_even, symmetricRun_odd]
      rcases round_spec fam (symmetricStates_symmetric fam hM k) with ⟨step, _, _, _⟩ | ⟨stuck, eq⟩
      · exact Or.inl step
      · right
        rw [eq]
        exact ⟨stuck, rfl⟩
    · have next : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      rw [next, symmetricRun_even, symmetricRun_odd]
      rcases round_spec fam (symmetricStates_symmetric fam hM k) with ⟨_, step, _, _⟩ | ⟨stuck, eq⟩
      · exact Or.inl step
      · right
        have unfold : symmetricStates Γ m M (k + 1) = (round Γ m (symmetricStates Γ m M k)).2 := rfl
        rw [unfold, eq]
        exact ⟨stuck, rfl⟩
  · rintro x ⟨n, hx⟩
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · refine ⟨2 * k, ?_⟩
      rw [symmetricRun_even] at hx ⊢
      rw [← Multiset.count_pos, ((symmetricStates_symmetric fam hM k) x).1]
      exact Multiset.count_pos.mpr hx
    · rw [symmetricRun_odd] at hx
      rcases round_spec fam (symmetricStates_symmetric fam hM k) with
          ⟨_, _, _, mirrored⟩ | ⟨_, eq⟩
      · rcases mirrored x hx with old | new
        · exact ⟨2 * k, by rw [symmetricRun_even]; exact old⟩
        · refine ⟨2 * (k + 1), ?_⟩
          rw [symmetricRun_even]
          exact new
      · rw [eq] at hx
        refine ⟨2 * k, ?_⟩
        rw [symmetricRun_even]
        rw [← Multiset.count_pos, ((symmetricStates_symmetric fam hM k) x).1]
        exact Multiset.count_pos.mpr hx

/-- **No symmetric election by binary steps.** A family of positive binary rules closed under the
mirror elects no leader between an announcement and its mirror image, from any split symmetric
configuration. -/
theorem no_symmetric_election (fam : BinaryFamily m Γ) {M : Multiset R} (hM : SplitSymmetric m M)
    (a : R) : ¬ Elects Γ M a (m.σ a) := by
  intro elects
  obtain ⟨f, maximal, start, mirrored⟩ := exists_symmetric_maximal_run fam hM
  have exactlyOne := elects f maximal start
  have forth : Shows f a → Shows f (m.σ a) := mirrored a
  have back : Shows f (m.σ a) → Shows f a := fun h => by
    simpa [m.invol] using mirrored (m.σ a) h
  by_cases sa : Shows f a
  · exact exactlyOne.mp sa (forth sa)
  · exact sa (exactlyOne.mpr fun sb => sa (back sb))

end Run

/-! ## Rho's COMM -/

section Rho

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CommFootprint

/-- Rho's COMM as a rule over the bag of top-level components: take an output and an input on one
channel, make the continuation with the message substituted (`CommFootprint`). -/
def commRule (n q p : Pattern) : Rule Pattern :=
  ⟨commConsumed n q p, 0, commProduced q p, fun _ => false⟩

/-- The rule family of rho's COMM. -/
def RhoComm (ρ : Rule Pattern) : Prop := ∃ n q p, ρ = commRule n q p

/-- **Each step of the bag reading is a rho reduction** of the parallel compositions. -/
theorem rhoComm_reduces {elements targets : List Pattern}
    (h : Reduces RhoComm (elements : Multiset Pattern) (targets : Multiset Pattern)) :
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
      (bag elements) (bag targets)) := by
  obtain ⟨ρ, ⟨n, q, p, rfl⟩, enabled, result⟩ := h
  have le : commConsumed n q p ≤ (elements : Multiset Pattern) := by
    simpa [commRule, Rule.redex] using enabled.1
  apply reduces_of_commRule (n := n) (q := q) (p := p)
  refine ⟨(elements : Multiset Pattern) - commConsumed n q p, ?_, ?_⟩
  · exact (add_tsub_cancel_of_le le).symm
  · rw [result]
    simp only [Rule.result, commRule]
    exact add_comm _ _

/-- The head constructor of a top-level component: an output, an input, or something else. -/
def commKind (x : Pattern) : Fin 3 :=
  match x with
  | .apply "POutput" _ => 0
  | .apply "PInput" _ => 1
  | _ => 2

theorem commKind_out (n q : Pattern) : commKind (commOut n q) = 0 := by
  simp [commKind, commOut]

theorem commKind_in (n p : Pattern) : commKind (commIn n p) = 1 := by
  simp [commKind, commIn]

/-- **A COMM's redex is binary** for every mirror that maps outputs to outputs and inputs to
inputs. -/
theorem commRule_binary (m : Mirror Pattern) (preserves : ∀ x, commKind (m.σ x) = commKind x)
    (n q p : Pattern) : Binary m (commRule n q p).redex := by
  apply binary_of_kinds m commKind preserves
  simp [commRule, Rule.redex, commConsumed, commKind_out, commKind_in]

/-- **Rho's COMM elects no leader from a split symmetric configuration**, for every mirror that
maps outputs to outputs, inputs to inputs and COMM instances to COMM instances. -/
theorem rho_no_symmetric_election (m : Mirror Pattern)
    (preserves : ∀ x, commKind (m.σ x) = commKind x)
    (equivariant : ∀ ρ, RhoComm ρ → RhoComm (mirrorRule m ρ))
    {M : Multiset Pattern} (hM : SplitSymmetric m M) (a : Pattern) :
    ¬ Elects RhoComm M a (m.σ a) :=
  no_symmetric_election
    ⟨fun ρ ⟨n, q, p, h⟩ => by subst h; exact fun _ => rfl, equivariant,
      fun ρ ⟨n, q, p, h⟩ => by subst h; exact commRule_binary m preserves n q p⟩
    hM a

end Rho

/-! ## Controls: two philosophers, two forks -/

namespace Controls

/-- The two seats. -/
inductive Seat where
  | a | b
  deriving DecidableEq

def Seat.other : Seat → Seat
  | .a => .b
  | .b => .a

/-- Forks (messages), hungry and holding philosophers (receivers), and announcements. -/
inductive Table where
  | fork (s : Seat)
  | hungry (s : Seat)
  | holding (s : Seat)
  | leader (s : Seat)
  deriving DecidableEq

/-- Swap the seats. -/
def Table.flip : Table → Table
  | .fork s => .fork s.other
  | .hungry s => .hungry s.other
  | .holding s => .holding s.other
  | .leader s => .leader s.other

theorem Seat.other_other (s : Seat) : s.other.other = s := by cases s <;> rfl

def flipMirror : Mirror Table := ⟨Table.flip, fun x => by cases x <;> simp [Table.flip, Seat.other_other]⟩

/-- Take your own fork. -/
def pick (s : Seat) : Rule Table := ⟨{.fork s, .hungry s}, 0, {.holding s}, fun _ => false⟩

/-- Then take the other fork and announce. -/
def second (s : Seat) : Rule Table := ⟨{.fork s.other, .holding s}, 0, {.leader s}, fun _ => false⟩

/-- Binary rules: one fork per step. -/
def BinaryRules (ρ : Rule Table) : Prop := ∃ s, ρ = pick s ∨ ρ = second s

/-- The join: both forks in one step. -/
def joinRule (s : Seat) : Rule Table :=
  ⟨{.fork s, .fork s.other, .hungry s}, 0, {.leader s}, fun _ => false⟩

def JoinRules (ρ : Rule Table) : Prop := ∃ s, ρ = joinRule s

/-- Two forks, two hungry philosophers. -/
def start : Multiset Table := {.fork .a, .fork .b, .hungry .a, .hungry .b}

theorem start_symmetric : SplitSymmetric flipMirror start := by
  have : start = ({.fork .a, .hungry .a} : Multiset Table) +
      ({.fork .a, .hungry .a} : Multiset Table).map flipMirror.σ := by
    simp [start, flipMirror, Table.flip, Seat.other]
    decide
  rw [this]
  exact splitSymmetric_add_mirror flipMirror _

theorem flip_kind (x : Table) :
    (match flipMirror.σ x with | .fork _ => (0 : Fin 2) | _ => 1) =
      (match x with | .fork _ => (0 : Fin 2) | _ => 1) := by
  cases x <;> rfl

/-- **The binary rules form a binary family.** -/
theorem binaryTable_family : BinaryFamily flipMirror BinaryRules := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ρ ⟨s, rfl | rfl⟩ <;> exact fun _ => rfl
  · rintro ρ ⟨s, rfl | rfl⟩
    · refine ⟨s.other, Or.inl ?_⟩
      cases s <;> simp [mirrorRule, pick, flipMirror, Table.flip, Seat.other]
    · refine ⟨s.other, Or.inr ?_⟩
      cases s <;> simp [mirrorRule, second, flipMirror, Table.flip, Seat.other]
  · rintro ρ ⟨s, rfl | rfl⟩
    · exact binary_of_kinds flipMirror (fun x => match x with | .fork _ => (0 : Fin 2) | _ => 1)
        flip_kind (by cases s <;> simp [pick, Rule.redex])
    · exact binary_of_kinds flipMirror (fun x => match x with | .fork _ => (0 : Fin 2) | _ => 1)
        flip_kind (by cases s <;> simp [second, Rule.redex, Seat.other])

/-- **Binary steps elect no philosopher.** -/
theorem binaryTable_no_election : ¬ Elects BinaryRules start (.leader .a) (.leader .b) :=
  no_symmetric_election binaryTable_family start_symmetric (.leader .a)

/-- **The symmetric run deadlocks**: each philosopher holds one fork, and nothing can step. -/
theorem binaryTable_deadlock :
    Reduces BinaryRules start ({.fork .b, .hungry .b, .holding .a}) ∧
      Reduces BinaryRules ({.fork .b, .hungry .b, .holding .a}) ({.holding .a, .holding .b}) ∧
      Stuck BinaryRules ({.holding .a, .holding .b}) := by
  refine ⟨⟨pick .a, ⟨.a, Or.inl rfl⟩, ⟨by decide, fun _ _ => rfl⟩, by decide⟩,
    ⟨pick .b, ⟨.b, Or.inl rfl⟩, ⟨by decide, fun _ _ => rfl⟩, by decide⟩, ?_⟩
  rintro M' ⟨ρ, ⟨s, rfl | rfl⟩, ⟨le, _⟩, _⟩
  · have : Table.fork s ∈ ({.holding .a, .holding .b} : Multiset Table) :=
      Multiset.mem_of_le le (by simp [pick, Rule.redex])
    simp at this
  · have : Table.fork s.other ∈ ({.holding .a, .holding .b} : Multiset Table) :=
      Multiset.mem_of_le le (by simp [second, Rule.redex])
    simp at this

/-- The join's redex is not binary: it holds `fork a` and its mirror `fork b`. -/
theorem joinRule_not_binary : ¬ Binary flipMirror (joinRule .a).redex := by
  intro h
  have := (h (.fork .a) (by decide)).1 (by decide)
  revert this
  decide

theorem join_after (s : Seat) :
    (joinRule s).result start = {.hungry s.other, .leader s} := by
  cases s <;> decide

theorem join_stuck (s : Seat) : Stuck JoinRules {.hungry s.other, .leader s} := by
  rintro M' ⟨ρ, ⟨t, rfl⟩, ⟨le, _⟩, _⟩
  have : Table.fork t ∈ ({.hungry s.other, .leader s} : Multiset Table) :=
    Multiset.mem_of_le le (by simp [joinRule, Rule.redex])
  simp at this

/-- **One join step elects**: every maximal run shows exactly one leader. -/
theorem joinTable_elects : Elects JoinRules start (.leader .a) (.leader .b) := by
  intro f maximal f0
  -- the first step is one of the two joins
  have first : ∃ s, f 1 = {.hungry s.other, .leader s} := by
    rcases maximal 0 with step | ⟨stuck, _⟩
    · obtain ⟨ρ, ⟨s, rfl⟩, _, result⟩ := step
      exact ⟨s, by rw [result, f0, join_after]⟩
    · have enabled : (joinRule .a).Enabled (f 0) := by
        rw [f0]
        exact ⟨by decide, fun _ _ => rfl⟩
      exact (stuck _ ⟨joinRule .a, ⟨.a, rfl⟩, enabled, rfl⟩).elim
  obtain ⟨s, h1⟩ := first
  -- after it nothing moves
  have stays : ∀ k, f (k + 1) = {.hungry s.other, .leader s} := by
    intro k
    induction k with
    | zero => exact h1
    | succ k ih =>
      rcases maximal (k + 1) with step | ⟨_, eq⟩
      · exact absurd step (ih ▸ join_stuck s _)
      · rw [eq, ih]
  have showsIff : ∀ x, Shows f x ↔ x ∈ ({.hungry s.other, .leader s} : Multiset Table) ∨ x ∈ start := by
    intro x
    constructor
    · rintro ⟨n, hn⟩
      cases n with
      | zero => exact Or.inr (f0 ▸ hn)
      | succ k => exact Or.inl (stays k ▸ hn)
    · rintro (h | h)
      · exact ⟨1, by rw [stays 0]; exact h⟩
      · exact ⟨0, by rw [f0]; exact h⟩
  rw [showsIff, showsIff]
  cases s <;> decide

end Controls

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Weaknesses.Symmetry
