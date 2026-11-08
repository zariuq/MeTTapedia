import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CompletionGround
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchOutcome

/-!
# Correctness of fair ground completion, and its readout

## Derivations

A **completion derivation** (`Derivation`) is a sequence of item sets in which each set is the
previous one or follows from it by one rule. Its **persistent items** are its limit (`limit`).

* Every stage has the theory of the start (`Derivation.theory_iff`), and its rules stay decreasing
  (`Derivation.decreasing`).
* **Every step by an item that ever appears is provable by persistent items at no greater cost**
  (`Derivation.persistent_proof`): by well-founded induction on the cost, since an item that leaves
  is redundant in the next stage (`Transition.taken_redundant`).

## Fairness and correctness

A derivation is **fair** (`Fair`) when every ground critical pair of persistent rules, `d[r₁] ≈ r₂`
from the peak `d[l₁] = l₂`, is eventually provable by steps whose terms all lie below the peak:
the proof-ordering redundancy of the critical peak. The classical forms, a critical pair eventually
**deduced** as an equation or eventually **joinable** by the rules of some stage, are instances
(`DeducedOrJoined.fair`).

**Correctness** (`Derivation.convergent`): a fair, non-failing derivation (no persistent equation)
from decreasing rules has persistent rules `R∞` that

* are decreasing, so terminate (`terminating`);
* are confluent (`Derivation.confluent`): by well-founded induction on the peak, a nested peak is a
  critical pair, provable below the peak by fairness and the persistence of proofs, hence joinable
  by confluence below it (`joins_below`, Newman's lemma on the terms below the peak); apart peaks
  commute (`peak_cases`);
* decide the theory of the start: `s ≈ t` follows from `E₀` exactly when `s` and `t` join in `R∞`
  (`Derivation.decides`), so exactly when their normal forms agree (`theory_iff_normalForm`).

Joinability of a critical pair is confluence of one rewrite system. It is not independence of
firings, which asks that each firing survive the other (`CompletionFiring`).

## Failure

Completion **fails** when an equation persists. With a total order no equation is stuck: each is
oriented or deleted (`stuck_needs_partial`). A partial order that cannot compare the two sides of
an equation leaves it unoriented (`CompletionCommutativity`).

## The readout in the outcome algebra

* `completionReadout`: **commit** when the run finished with every equation oriented; then the
  final rules are convergent and decide the theory (`completionReadout_commit`). Otherwise it is
  **suspended**: a cut-off run or a failure. It never reads refuted (`completionReadout_ne_refuted`).
* `wordReadout s t`: after success, **commit** when `s` and `t` join, so `s ≈ t` follows from `E₀`
  (`wordReadout_commit`); **refuted** when they do not, so it does not follow and the normal forms
  differ (`wordReadout_refuted`); **suspended** without success (`wordReadout_suspended`).
* A fair, non-failing derivation reports success at its limit (`Derivation.reports`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Completion

open Mettapedia.Logic.LP
open Superposition (Ctx Ctx.fill_comp Rw Joins)
open _root_.Relation (ReflTransGen EqvGen Join)
open Mettapedia.Logic.Relation (Confluent confluent_of_accessible_forks NormalizationResult)

variable {sig : LPSignature}

/-! ## Derivations -/

section Derivations

variable [Preorder (GroundTerm sig)]

/-- **A completion derivation**: each stage is the previous one, or follows from it by one rule. -/
structure Derivation (N : ℕ → Set (Item sig)) : Prop where
  step : ∀ i, N (i + 1) = N i ∨ ∃ ρ, Transition ρ (N i) (N (i + 1))

/-- The items of some stage. -/
def union (N : ℕ → Set (Item sig)) : Set (Item sig) := {x | ∃ i, x ∈ N i}

/-- **The persistent items.** -/
def limit (N : ℕ → Set (Item sig)) : Set (Item sig) := {x | ∃ i, ∀ j, i ≤ j → x ∈ N j}

variable {N : ℕ → Set (Item sig)}

omit [Preorder (GroundTerm sig)] in
theorem limit_subset_union : limit N ⊆ union N := fun _ ⟨i, persistent⟩ => ⟨i, persistent i le_rfl⟩

/-- **Every stage has the theory of the start.** -/
theorem Derivation.theory_iff [SimplificationOrder sig] (derivation : Derivation N) :
    ∀ i a b, EqvGen (EqStep (N 0)) a b ↔ EqvGen (EqStep (N i)) a b
  | 0, _, _ => Iff.rfl
  | i + 1, a, b => by
      rw [derivation.theory_iff i a b]
      rcases derivation.step i with same | ⟨ρ, t⟩
      · rw [same]
      · exact t.theory_iff a b

theorem Derivation.decreasing [SimplificationOrder sig] (derivation : Derivation N) (start : Decreasing (N 0)) :
    ∀ i, Decreasing (N i)
  | 0 => start
  | i + 1 => by
      rcases derivation.step i with same | ⟨ρ, t⟩
      · rw [same]
        exact derivation.decreasing start i
      · exact t.decreasing (derivation.decreasing start i)

theorem Derivation.decreasing_limit [SimplificationOrder sig] (derivation : Derivation N)
    (start : Decreasing (N 0)) : Decreasing (limit N) := fun l r ⟨i, persistent⟩ =>
  derivation.decreasing start i l r (persistent i le_rfl)

omit [Preorder (GroundTerm sig)] in
/-- An item that appears and does not persist leaves at some stage. -/
theorem leaves {x : Item sig} (appears : x ∈ union N) (transient : x ∉ limit N) :
    ∃ j, x ∈ N j ∧ x ∉ N (j + 1) := by
  obtain ⟨i, member⟩ := appears
  by_contra stays
  push Not at stays
  apply transient
  refine ⟨i, fun j le => ?_⟩
  induction j, le using Nat.le_induction with
  | base => exact member
  | succ j _ ih => exact stays j ih

omit [Preorder (GroundTerm sig)] in
/-- A derivation that idles from stage `k` on has the items of stage `k` as its limit. -/
theorem limit_of_idle {k : ℕ} (idle : ∀ j, k ≤ j → N j = N k) : limit N = N k := by
  ext x
  constructor
  · rintro ⟨i, persistent⟩
    have member := persistent (max i k) (le_max_left _ _)
    rwa [idle _ (le_max_right _ _)] at member
  · intro member
    exact ⟨k, fun j le => by rw [idle j le]; exact member⟩

/-- Steps by persistent items, at cost at most `κ`. -/
def PersistentBelow (N : ℕ → Set (Item sig)) (κ : Cost sig) (a b : GroundTerm sig) : Prop :=
  ∃ y ∈ limit N, ∃ c, y.Rel c a b ∧ (y.cost c = κ ∨ CostLT (y.cost c) κ)

variable [SimplificationOrder sig] [WellFoundedLT (GroundTerm sig)]

/-- **Every step by an item that ever appears is provable by persistent items, at no greater
cost.** -/
theorem Derivation.persistent_proof (derivation : Derivation N) (start : Decreasing (N 0)) :
    ∀ x ∈ union N, ∀ c a b, x.Rel c a b → EqvGen (PersistentBelow N (x.cost c)) a b := by
  suffices key : ∀ κ, ∀ x ∈ union N, ∀ c, x.cost c = κ → ∀ a b, x.Rel c a b →
      EqvGen (PersistentBelow N κ) a b from
    fun x member c a b rel => key _ x member c rfl a b rel
  intro κ
  refine costLT_wf.induction (C := fun κ => ∀ x ∈ union N, ∀ c, x.cost c = κ → ∀ a b, x.Rel c a b →
      EqvGen (PersistentBelow N κ) a b) κ fun κ ih => ?_
  intro x member c same a b rel
  by_cases persistent : x ∈ limit N
  · exact EqvGen.rel _ _ ⟨x, persistent, c, rel, Or.inl same⟩
  · obtain ⟨j, inJ, outJ⟩ := leaves member persistent
    rcases derivation.step j with idle | ⟨ρ, t⟩
    · exact absurd (by rw [idle]; exact inJ) outJ
    · have taken : x ∈ ρ.takes := by
        by_contra notTaken
        exact outJ (t.keeps x inJ notTaken)
      have redundant := t.taken_redundant (derivation.decreasing start j) x taken c a b rel
      refine eqvGen_flatten (fun u v step => ?_) redundant
      obtain ⟨y, inY, c', rel', lt⟩ := step
      have lt' : CostLT (y.cost c') κ := by rw [← same]; exact lt
      refine EqvGen.mono (fun _ _ below => ?_) _ _ (ih (y.cost c') lt' y ⟨j + 1, inY⟩ c' rfl u v rel')
      obtain ⟨z, inZ, c'', relZ, le⟩ := below
      refine ⟨z, inZ, c'', relZ, Or.inr ?_⟩
      rcases le with equal | smaller
      · rw [equal]
        exact lt'
      · exact costLT_trans smaller lt'

end Derivations

/-! ## Rewriting below a term -/

section Below

variable [Preorder (GroundTerm sig)] [SimplificationOrder sig] [WellFoundedLT (GroundTerm sig)]

/-- **Decreasing rules terminate.** -/
theorem terminating {R : GroundTerm sig → GroundTerm sig → Prop} (decreasing : ∀ l r, R l r → r < l) :
    ∀ u, Acc (fun v u => Rw R u v) u :=
  fun u => Subrelation.accessible (fun {_ _} step => rw_lt decreasing step) (wellFounded_lt.apply u)

/-- Rewriting from terms below `u`. -/
def RwBelow (R : GroundTerm sig → GroundTerm sig → Prop) (u a b : GroundTerm sig) : Prop :=
  Rw R a b ∧ a < u

/-- **Confluence below a term**: if every peak below `u` is joinable, so is every conversion of
terms below `u` (Newman's lemma on the terms below `u`). -/
theorem joins_below {R : GroundTerm sig → GroundTerm sig → Prop} (decreasing : ∀ l r, R l r → r < l)
    {u : GroundTerm sig}
    (forks : ∀ v, v < u → ∀ left right, Rw R v left → Rw R v right → Joins R left right)
    {a b : GroundTerm sig} (conv : EqvGen (RwBelow R u) a b) : Joins R a b := by
  have lift : ∀ {v w : GroundTerm sig}, ReflTransGen (Rw R) v w → v < u → ReflTransGen (RwBelow R u) v w := by
    intro v w steps below
    induction steps with
    | refl => exact .refl
    | tail before step ih => exact ih.tail ⟨step, (steps_le decreasing before).trans_lt below⟩
  have confluent : Confluent (RwBelow R u) :=
    confluent_of_accessible_forks
      (fun s => Subrelation.accessible (fun {_ _} step => rw_lt decreasing step.1) (wellFounded_lt.apply s))
      (fun v left right one two => by
        obtain ⟨w, toLeft, toRight⟩ := forks v one.2 left right one.1 two.1
        exact ⟨w, lift toLeft ((rw_lt decreasing one.1).trans one.2),
          lift toRight ((rw_lt decreasing two.1).trans two.2)⟩)
  obtain ⟨w, left, right⟩ := confluent.eqvGen_iff_join.mp conv
  exact ⟨w, left.lift id fun _ _ step => step.1, right.lift id fun _ _ step => step.1⟩

/-- A step of `N` all of whose terms lie below `m`. -/
def EqStepBelow (N : Set (Item sig)) (m a b : GroundTerm sig) : Prop :=
  ∃ y ∈ N, ∃ c, y.Rel c a b ∧ Bounded m (y.cost c)

omit [WellFoundedLT (GroundTerm sig)] in
theorem bounded_ctx {m : GroundTerm sig} {y : Item sig} {c : Ctx sig} (bounded : Bounded m (y.cost c))
    (d : Ctx sig) : Bounded (d.fill m) (y.cost (d.comp c)) := by
  cases y with
  | eqn e =>
      induction e using Sym2.ind with
      | h s t =>
          intro z member
          change z ∈ (d.comp c).fill s ::ₘ {(d.comp c).fill t} at member
          rw [Ctx.fill_comp, Ctx.fill_comp] at member
          have inS : c.fill s ∈ ((Item.eqn s(s, t)).cost c).1 :=
            show c.fill s ∈ c.fill s ::ₘ {c.fill t} from Multiset.mem_cons_self _ _
          have inT : c.fill t ∈ ((Item.eqn s(s, t)).cost c).1 :=
            show c.fill t ∈ c.fill s ::ₘ {c.fill t} from Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _)
          rcases Multiset.mem_cons.mp member with rfl | inZ
          · exact fill_lt_fill d (bounded _ inS)
          · rw [Multiset.mem_singleton.mp inZ]
            exact fill_lt_fill d (bounded _ inT)
  | rule l r =>
      intro z member
      change z ∈ ({(d.comp c).fill l} : Multiset _) at member
      rw [Multiset.mem_singleton.mp member, Ctx.fill_comp]
      exact fill_lt_fill d (bounded _ (Multiset.mem_singleton_self _))

omit [WellFoundedLT (GroundTerm sig)] in
/-- A conversion below `m` stays below `d[m]` in the context `d`. -/
theorem eqStepBelow_ctx {M : Set (Item sig)} {m a b : GroundTerm sig} (conv : EqvGen (EqStepBelow M m) a b)
    (d : Ctx sig) : EqvGen (EqStepBelow M (d.fill m)) (d.fill a) (d.fill b) := by
  induction conv with
  | rel _ _ step =>
      obtain ⟨y, member, c, rel, bounded⟩ := step
      exact EqvGen.rel _ _ ⟨y, member, d.comp c, rel.ctx d, bounded_ctx bounded d⟩
  | refl => exact EqvGen.refl _
  | symm _ _ _ ih => exact EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact EqvGen.trans _ _ _ ih₁ ih₂

omit [WellFoundedLT (GroundTerm sig)] in
/-- A rewrite sequence of decreasing rules from a term below `m` is a conversion below `m`. -/
theorem steps_below {M : Set (Item sig)} (decreasing : Decreasing M) {m a w : GroundTerm sig}
    (steps : ReflTransGen (Rw (rules M)) a w) (below : a < m) : EqvGen (EqStepBelow M m) a w := by
  induction steps with
  | refl => exact EqvGen.refl _
  | tail before step ih =>
      obtain ⟨c, l, r, rule, rfl, rfl⟩ := step
      have top : c.fill l < m := (steps_le decreasing before).trans_lt below
      exact EqvGen.trans _ _ _ ih (EqvGen.rel _ _ ⟨_, rule, c, ⟨rfl, rfl⟩,
        fun z member => (Multiset.mem_singleton.mp member) ▸ top⟩)

end Below

/-! ## Fairness and correctness -/

section Correctness

variable [Preorder (GroundTerm sig)] [SimplificationOrder sig] [WellFoundedLT (GroundTerm sig)]
  {N : ℕ → Set (Item sig)}

/-- **Fairness**: every ground critical pair of persistent rules, `d[r₁] ≈ r₂` from the peak
`d[l₁] = l₂`, is eventually provable by steps below the peak. -/
def Fair (N : ℕ → Set (Item sig)) : Prop :=
  ∀ (l₁ r₁ l₂ r₂ : GroundTerm sig) (d : Ctx sig), Item.rule l₁ r₁ ∈ limit N → Item.rule l₂ r₂ ∈ limit N →
    d.fill l₁ = l₂ → ∃ i, EqvGen (EqStepBelow (N i) l₂) (d.fill r₁) r₂

/-- **The classical fairness**: every critical pair of persistent rules is eventually deduced as an
equation, or joinable by the rules of some stage. -/
def DeducedOrJoined (N : ℕ → Set (Item sig)) : Prop :=
  ∀ (l₁ r₁ l₂ r₂ : GroundTerm sig) (d : Ctx sig), Item.rule l₁ r₁ ∈ limit N → Item.rule l₂ r₂ ∈ limit N →
    d.fill l₁ = l₂ → ∃ i, Item.eqn s(d.fill r₁, r₂) ∈ N i ∨ Joins (rules (N i)) (d.fill r₁) r₂

omit [WellFoundedLT (GroundTerm sig)] in
/-- **A deduced or joinable critical pair is provable below its peak.** -/
theorem DeducedOrJoined.fair (derivation : Derivation N) (start : Decreasing (N 0))
    (classical : DeducedOrJoined N) : Fair N := by
  intro l₁ r₁ l₂ r₂ d one two overlap
  have decreasing := derivation.decreasing_limit start
  have left : d.fill r₁ < l₂ := overlap ▸ fill_lt_fill d (decreasing l₁ r₁ one)
  have right : r₂ < l₂ := decreasing l₂ r₂ two
  obtain ⟨i, deduced | ⟨w, toW, fromW⟩⟩ := classical l₁ r₁ l₂ r₂ d one two overlap
  · refine ⟨i, EqvGen.rel _ _ ⟨_, deduced, .hole, rel_eqn.mpr (Or.inl ⟨rfl, rfl⟩), fun z member => ?_⟩⟩
    change z ∈ d.fill r₁ ::ₘ {r₂} at member
    rcases Multiset.mem_cons.mp member with rfl | inR
    · exact left
    · rw [Multiset.mem_singleton.mp inR]
      exact right
  · have stage := derivation.decreasing start i
    exact ⟨i, EqvGen.trans _ _ _ (steps_below stage toW left) (EqvGen.symm _ _ (steps_below stage fromW right))⟩

omit [SimplificationOrder sig] [WellFoundedLT (GroundTerm sig)] in
/-- Steps by persistent items with bounded cost are rewrite steps below the bound, when no equation
persists. -/
theorem persistent_rwBelow
    (noEquations : ∀ e, Item.eqn e ∉ limit N) {u : GroundTerm sig} {κ : Cost sig} (bounded : Bounded u κ)
    {a b : GroundTerm sig} (conv : EqvGen (PersistentBelow N κ) a b) :
    EqvGen (RwBelow (rules (limit N)) u) a b := by
  refine EqvGen.mono (fun a' b' step => ?_) _ _ conv
  obtain ⟨y, member, c, rel, le⟩ := step
  have boundedY : Bounded u (y.cost c) := by
    rcases le with equal | smaller
    · rw [equal]
      exact bounded
    · exact bounded.of_costLT smaller
  cases y with
  | eqn e => exact absurd member (noEquations e)
  | rule l r =>
      obtain ⟨rfl, rfl⟩ := rel
      exact ⟨⟨c, l, r, member, rfl, rfl⟩, boundedY _ (Multiset.mem_singleton_self _)⟩

/-- **A critical pair of persistent rules in a context joins**, given joinable peaks below. -/
theorem critical_joins (derivation : Derivation N) (start : Decreasing (N 0)) (fair : Fair N)
    (noEquations : ∀ e, Item.eqn e ∉ limit N) {l₁ r₁ l₂ r₂ : GroundTerm sig} {d c : Ctx sig}
    (one : Item.rule l₁ r₁ ∈ limit N) (two : Item.rule l₂ r₂ ∈ limit N) (overlap : d.fill l₁ = l₂)
    (forks : ∀ v, v < c.fill l₂ → ∀ left right, Rw (rules (limit N)) v left → Rw (rules (limit N)) v right →
      Joins (rules (limit N)) left right) :
    Joins (rules (limit N)) (c.fill (d.fill r₁)) (c.fill r₂) := by
  obtain ⟨i, conv⟩ := fair l₁ r₁ l₂ r₂ d one two overlap
  have lifted := eqStepBelow_ctx conv c
  refine joins_below (derivation.decreasing_limit start) forks (eqvGen_flatten (fun a b step => ?_) lifted)
  obtain ⟨y, member, c', rel, bounded⟩ := step
  exact persistent_rwBelow noEquations bounded
    (derivation.persistent_proof start y ⟨i, member⟩ c' a b rel)

/-- **The persistent rules of a fair, non-failing derivation are confluent.** -/
theorem Derivation.confluent (derivation : Derivation N) (start : Decreasing (N 0)) (fair : Fair N)
    (noEquations : ∀ e, Item.eqn e ∉ limit N) : Confluent (Rw (rules (limit N))) := by
  have forks : ∀ u, ∀ left right, Rw (rules (limit N)) u left → Rw (rules (limit N)) u right →
      Joins (rules (limit N)) left right := by
    intro u
    refine (wellFounded_lt (α := GroundTerm sig)).induction (C := fun u => ∀ left right,
      Rw (rules (limit N)) u left → Rw (rules (limit N)) u right → Joins (rules (limit N)) left right) u ?_
    intro u ih left right first second
    obtain ⟨c₁, l₁, r₁, rule₁, at₁, rfl⟩ := first
    obtain ⟨c₂, l₂, r₂, rule₂, at₂, rfl⟩ := second
    rcases peak_cases c₁ c₂ (at₁.symm.trans at₂) with ⟨d, overlap, fills⟩ | ⟨d, overlap, fills⟩ | apart
    · rw [fills]
      exact critical_joins derivation start fair noEquations rule₁ rule₂ overlap (at₂ ▸ ih)
    · rw [fills]
      exact (critical_joins derivation start fair noEquations rule₂ rule₁ overlap (at₁ ▸ ih)).symm
    · obtain ⟨e₁, e₂, one, two, meet⟩ := apart r₁ r₂
      exact ⟨e₁.fill r₂, .single ⟨e₁, l₂, r₂, rule₂, one, rfl⟩, .single ⟨e₂, l₁, r₁, rule₁, two, meet⟩⟩
  exact confluent_of_accessible_forks (terminating (derivation.decreasing_limit start)) forks

omit [Preorder (GroundTerm sig)] [SimplificationOrder sig] [WellFoundedLT (GroundTerm sig)] in
/-- Without equations, a step of a set of items is a rewrite step either way. -/
theorem eqStep_iff_rw {M : Set (Item sig)} (noEquations : ∀ e, Item.eqn e ∉ M) {a b : GroundTerm sig} :
    EqStep M a b ↔ Rw (rules M) a b := by
  constructor
  · rintro ⟨x, member, c, rel⟩
    cases x with
    | eqn e => exact absurd member (noEquations e)
    | rule l r =>
        obtain ⟨rfl, rfl⟩ := rel
        exact ⟨c, l, r, member, rfl, rfl⟩
  · rintro ⟨c, l, r, member, rfl, rfl⟩
    exact ⟨_, member, c, rfl, rfl⟩

/-- **The persistent rules decide the theory of the start**: `a ≈ b` follows from `E₀` exactly
when `a` and `b` join in `R∞`. -/
theorem Derivation.decides (derivation : Derivation N) (start : Decreasing (N 0)) (fair : Fair N)
    (noEquations : ∀ e, Item.eqn e ∉ limit N) (a b : GroundTerm sig) :
    EqvGen (EqStep (N 0)) a b ↔ Joins (rules (limit N)) a b := by
  have confluent := derivation.confluent start fair noEquations
  refine Iff.trans ?_ (confluent.eqvGen_iff_join (left := a) (right := b))
  constructor
  · refine eqvGen_flatten fun u v step => ?_
    obtain ⟨x, member, c, rel⟩ := step
    refine EqvGen.mono (fun a' b' step => ?_) _ _ (derivation.persistent_proof start x ⟨0, member⟩ c u v rel)
    obtain ⟨y, inY, c', rel', -⟩ := step
    exact (eqStep_iff_rw noEquations).mp ⟨y, inY, c', rel'⟩
  · refine eqvGen_flatten fun u v step => ?_
    obtain ⟨c, l, r, member, rfl, rfl⟩ := step
    obtain ⟨i, persistent⟩ := member
    exact (derivation.theory_iff i _ _).mpr (rule_step (persistent i le_rfl) c)

/-- **Correctness of fair completion.** A fair derivation from decreasing rules in which no
equation persists has persistent rules that are decreasing, terminating and confluent, and that
decide the theory of the start by joinability. -/
theorem Derivation.convergent (derivation : Derivation N) (start : Decreasing (N 0)) (fair : Fair N)
    (noEquations : ∀ e, Item.eqn e ∉ limit N) :
    Decreasing (limit N) ∧ (∀ u, Acc (fun v u => Rw (rules (limit N)) u v) u) ∧
      Confluent (Rw (rules (limit N))) ∧
      ∀ a b, EqvGen (EqStep (N 0)) a b ↔ Joins (rules (limit N)) a b :=
  ⟨derivation.decreasing_limit start, terminating (derivation.decreasing_limit start),
    derivation.confluent start fair noEquations, derivation.decides start fair noEquations⟩

/-- **The theory of the start is the conversion of the persistent rules.** -/
theorem Derivation.theory_iff_conversion (derivation : Derivation N) (start : Decreasing (N 0)) (fair : Fair N)
    (noEquations : ∀ e, Item.eqn e ∉ limit N) (a b : GroundTerm sig) :
    EqvGen (EqStep (N 0)) a b ↔ EqvGen (Rw (rules (limit N))) a b :=
  (derivation.decides start fair noEquations a b).trans
    (derivation.confluent start fair noEquations).eqvGen_iff_join.symm

/-- **The theory is decided by normal forms.** -/
theorem theory_iff_normalForm (derivation : Derivation N) (start : Decreasing (N 0)) (fair : Fair N)
    (noEquations : ∀ e, Item.eqn e ∉ limit N) {a b : GroundTerm sig}
    (na : NormalizationResult (Rw (rules (limit N))) a) (nb : NormalizationResult (Rw (rules (limit N))) b) :
    EqvGen (EqStep (N 0)) a b ↔ na.normalForm = nb.normalForm := by
  have confluent := derivation.confluent start fair noEquations
  rw [derivation.decides start fair noEquations, na.eq_iff_eqvGen confluent nb]
  exact confluent.eqvGen_iff_join.symm

/-- Normal forms exist. -/
theorem normalForm_exists (derivation : Derivation N) (start : Decreasing (N 0)) (a : GroundTerm sig) :
    Nonempty (NormalizationResult (Rw (rules (limit N))) a) := by
  obtain ⟨w, steps, normal⟩ := Mettapedia.Logic.Relation.exists_normalForm_of_acc
    (terminating (derivation.decreasing_limit start) a)
  exact ⟨⟨w, steps, normal⟩⟩

end Correctness

/-! ## Failure needs a partial order -/

/-- **With a total order no equation is stuck**: it is oriented one way or the other, or deleted. -/
theorem stuck_needs_partial [LinearOrder (GroundTerm sig)] (s t : GroundTerm sig) :
    ∃ ρ : Rule sig, ρ.takes = [Item.eqn s(s, t)] ∧ ρ.reads = [] ∧ ρ.guard := by
  rcases lt_trichotomy t s with lt | same | gt
  · exact ⟨.orient s t, rfl, rfl, lt⟩
  · exact ⟨.delete s t, rfl, rfl, same.symm⟩
  · refine ⟨.orient t s, ?_, rfl, gt⟩
    show [Item.eqn s(t, s)] = [Item.eqn s(s, t)]
    rw [Sym2.eq_swap]

/-! ## The readout -/

section Readout

open Search (Outcome)

/-- **Success**: every equation is oriented. -/
def Succeeded (M : Set (Item sig)) (finished : Bool) : Prop := finished = true ∧ ∀ e, Item.eqn e ∉ M

/-- **The completion readout**: commit when the run finished with every equation oriented,
suspended otherwise. -/
noncomputable def completionReadout (M : Set (Item sig)) (finished : Bool) : Outcome Unit := by
  classical
  exact if Succeeded M finished then Outcome.pure () else Outcome.unknown

/-- **The word-problem readout** for `s ≈ t`: after success, commit when `s` and `t` join and
refuted when they do not; suspended without success. -/
noncomputable def wordReadout (M : Set (Item sig)) (finished : Bool) (s t : GroundTerm sig) : Outcome Unit := by
  classical
  exact if Succeeded M finished then (if Joins (rules M) s t then Outcome.pure () else Outcome.refuted)
    else Outcome.unknown

/-- **A run reports success only when its final rules are decreasing and confluent and keep the
theory of the start.** -/
def Reports [Preorder (GroundTerm sig)] (E₀ M : Set (Item sig)) (finished : Bool) : Prop :=
  finished = true → Decreasing M ∧ Confluent (Rw (rules M)) ∧
    ∀ a b, EqvGen (EqStep E₀) a b ↔ EqvGen (EqStep M) a b

theorem completionReadout_succeeded {M : Set (Item sig)} {finished : Bool}
    (commit : (completionReadout M finished).verdict = .commit) : Succeeded M finished := by
  classical
  by_contra failed
  have unknown : completionReadout M finished = Outcome.unknown := by simp [completionReadout, failed]
  rw [Outcome.verdict_eq_commit_iff, unknown] at commit
  exact commit rfl

/-- **Commit**: the final rules are convergent and decide the theory of the start by joinability. -/
theorem completionReadout_commit [Preorder (GroundTerm sig)] [SimplificationOrder sig] [WellFoundedLT (GroundTerm sig)]
    {E₀ M : Set (Item sig)} {finished : Bool} (reports : Reports E₀ M finished)
    (commit : (completionReadout M finished).verdict = .commit) :
    Decreasing M ∧ (∀ u, Acc (fun v u => Rw (rules M) u v) u) ∧ Confluent (Rw (rules M)) ∧
      ∀ a b, EqvGen (EqStep E₀) a b ↔ Joins (rules M) a b := by
  obtain ⟨finishedTrue, noEquations⟩ := completionReadout_succeeded commit
  obtain ⟨decreasing, confluent, theory⟩ := reports finishedTrue
  refine ⟨decreasing, terminating decreasing, confluent, fun a b => ?_⟩
  refine (theory a b).trans (Iff.trans ?_ (confluent.eqvGen_iff_join (left := a) (right := b)))
  exact ⟨EqvGen.mono (fun _ _ step => (eqStep_iff_rw noEquations).mp step) _ _,
    EqvGen.mono (fun _ _ step => (eqStep_iff_rw noEquations).mpr step) _ _⟩

/-- **Completion never reads refuted**: it cannot certify that no convergent system exists. -/
theorem completionReadout_ne_refuted (M : Set (Item sig)) (finished : Bool) :
    (completionReadout M finished).verdict ≠ .refuted := by
  classical
  rw [Ne, Outcome.verdict_eq_refuted_iff]
  unfold completionReadout
  split_ifs
  · intro same
    have := congrArg Outcome.answers same
    simp [Outcome.refuted] at this
  · intro same
    have := congrArg Outcome.status same
    simp [Outcome.refuted, Outcome.unknown] at this

/-- **Suspended**: without success the word problem is suspended. -/
theorem wordReadout_suspended {M : Set (Item sig)} {finished : Bool} (failed : ¬ Succeeded M finished)
    (s t : GroundTerm sig) : (wordReadout M finished s t).verdict = .suspended := by
  classical
  rw [Outcome.verdict_eq_suspended_iff]
  simp [wordReadout, failed]

/-- A failure, an equation left at the end, suspends. -/
theorem wordReadout_failure {M : Set (Item sig)} {finished : Bool} {e : Sym2 (GroundTerm sig)}
    (left : Item.eqn e ∈ M) (s t : GroundTerm sig) : (wordReadout M finished s t).verdict = .suspended :=
  wordReadout_suspended (fun ⟨_, noEquations⟩ => noEquations e left) s t

/-- A cut-off run never reads refuted. -/
theorem wordReadout_cutOff {M : Set (Item sig)} (s t : GroundTerm sig) :
    (wordReadout M false s t).verdict ≠ .refuted := by
  rw [wordReadout_suspended (fun ⟨cut, _⟩ => Bool.false_ne_true cut) s t]
  exact fun same => by cases same

theorem wordReadout_succeeded {M : Set (Item sig)} {finished : Bool} {s t : GroundTerm sig}
    (definite : (wordReadout M finished s t).verdict ≠ .suspended) : Succeeded M finished := by
  by_contra failed
  exact definite (wordReadout_suspended failed s t)

open Classical in
theorem wordReadout_of_succeeded {M : Set (Item sig)} {finished : Bool} (success : Succeeded M finished)
    (s t : GroundTerm sig) : wordReadout M finished s t =
      if Joins (rules M) s t then Outcome.pure () else Outcome.refuted := by
  classical
  simp [wordReadout, success]

variable [Preorder (GroundTerm sig)] [SimplificationOrder sig] [WellFoundedLT (GroundTerm sig)]

omit [SimplificationOrder sig] [WellFoundedLT (GroundTerm sig)] in
/-- **Commit**: `s ≈ t` follows from the start. -/
theorem wordReadout_commit {E₀ M : Set (Item sig)} {finished : Bool} {s t : GroundTerm sig}
    (reports : Reports E₀ M finished) (commit : (wordReadout M finished s t).verdict = .commit) :
    EqvGen (EqStep E₀) s t := by
  classical
  have success : Succeeded M finished := wordReadout_succeeded (s := s) (t := t) (by rw [commit]; exact fun same => by cases same)
  rw [wordReadout_of_succeeded success] at commit
  by_cases joined : Joins (rules M) s t
  · obtain ⟨w, left, right⟩ := joined
    rw [(reports success.1).2.2]
    have conv : EqvGen (Rw (rules M)) s t := (reports success.1).2.1.eqvGen_iff_join.mpr ⟨w, left, right⟩
    exact EqvGen.mono (fun _ _ step => (eqStep_iff_rw success.2).mpr step) _ _ conv
  · rw [if_neg joined, Outcome.verdict_eq_commit_iff] at commit
    exact absurd rfl commit

omit [SimplificationOrder sig] [WellFoundedLT (GroundTerm sig)] in
/-- **Refuted**: `s ≈ t` does not follow from the start, and the normal forms of `s` and `t`
differ. -/
theorem wordReadout_refuted {E₀ M : Set (Item sig)} {finished : Bool} {s t : GroundTerm sig}
    (reports : Reports E₀ M finished) (refuted : (wordReadout M finished s t).verdict = .refuted) :
    ¬ EqvGen (EqStep E₀) s t ∧ ∀ (ns : NormalizationResult (Rw (rules M)) s)
      (nt : NormalizationResult (Rw (rules M)) t), ns.normalForm ≠ nt.normalForm := by
  classical
  have success : Succeeded M finished := wordReadout_succeeded (s := s) (t := t) (by rw [refuted]; exact fun same => by cases same)
  rw [wordReadout_of_succeeded success] at refuted
  obtain ⟨-, confluent, theory⟩ := reports success.1
  have notJoined : ¬ Joins (rules M) s t := by
    intro joined
    rw [if_pos joined, Outcome.verdict_eq_refuted_iff] at refuted
    have := congrArg Outcome.answers refuted
    simp [Outcome.refuted] at this
  have notConv : ¬ EqvGen (Rw (rules M)) s t := fun conv => notJoined (confluent.eqvGen_iff_join.mp conv)
  refine ⟨fun derived => notConv ?_, fun ns nt same => notConv ((ns.eq_iff_eqvGen confluent nt).mp same)⟩
  exact EqvGen.mono (fun _ _ step => (eqStep_iff_rw success.2).mp step) _ _ ((theory s t).mp derived)

/-- **A fair, non-failing derivation reports success at its limit.** -/
theorem Derivation.reports {N : ℕ → Set (Item sig)} (derivation : Derivation N) (start : Decreasing (N 0))
    (fair : Fair N) (noEquations : ∀ e, Item.eqn e ∉ limit N) : Reports (N 0) (limit N) true := by
  intro _
  obtain ⟨decreasing, -, confluent, decides⟩ := derivation.convergent start fair noEquations
  refine ⟨decreasing, confluent, fun a b => ?_⟩
  refine (decides a b).trans (Iff.trans (confluent.eqvGen_iff_join (left := a) (right := b)).symm ?_)
  exact ⟨EqvGen.mono (fun _ _ step => (eqStep_iff_rw noEquations).mpr step) _ _,
    EqvGen.mono (fun _ _ step => (eqStep_iff_rw noEquations).mp step) _ _⟩

end Readout

#print axioms Derivation.theory_iff
#print axioms Derivation.decreasing
#print axioms leaves
#print axioms limit_of_idle
#print axioms Derivation.persistent_proof
#print axioms terminating
#print axioms joins_below
#print axioms eqStepBelow_ctx
#print axioms steps_below
#print axioms DeducedOrJoined.fair
#print axioms critical_joins
#print axioms Derivation.confluent
#print axioms Derivation.decides
#print axioms Derivation.convergent
#print axioms Derivation.theory_iff_conversion
#print axioms theory_iff_normalForm
#print axioms normalForm_exists
#print axioms stuck_needs_partial
#print axioms completionReadout_commit
#print axioms completionReadout_ne_refuted
#print axioms wordReadout_suspended
#print axioms wordReadout_failure
#print axioms wordReadout_cutOff
#print axioms wordReadout_commit
#print axioms wordReadout_refuted
#print axioms Derivation.reports

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Completion
