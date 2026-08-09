import Mettapedia.GSLT.Dynamics.UnfoldingTraversal
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.Dedup

/-!
# The proof-carrying collapse algebra

One language operation, `collapse-with algebra expression`, subsumes counting,
existence, bags, costed folds, and provenance — provided the algebra says,
checkably, which optimizations it admits.  This module is that contract.

A `CollapseAlgebra` consumes a stream of **observations** — answer, occurrence
multiplicity, receipt — and folds them into a result.  Optimizations are
licensed by **capability certificates**, each a small law set with exactly one
theorem:

| certificate | law | licensed optimization |
|---|---|---|
| `MonoidCert` | identity + associativity | chunking, stream/materialization fusion |
| `CommCert` | commutativity | reordering, parallel folding |
| `IdemCert` | idempotence | duplicate elimination |
| `AbsorbingCert` | an absorbing `done` | early termination (the per-row callback's Boolean stop) |
| `MultCoherenceCert` | counted emission splits | folding counted rows without expansion |

Nothing requires every algebra to support every optimization; an optimizer may
claim precisely the transformations whose certificates the algebra carries.
The negative witnesses at the end are part of the interface: each shows the
optimization *failing* for an algebra lacking the certificate, so no
transformation can be claimed on vibes.

The keystone is `foldChunks_eq` / `foldPull_eq_materialized`: folding a
chunked or streamed source equals collapsing the materialized whole, proved
from `MonoidCert` alone — **no commutativity** — which is the license to fold
backend rows directly instead of first constructing a giant tuple.  Reordering
is a separate license (`fold_perm`) sold separately by `CommCert`.

Control is deliberately absent: no bound or budget lives in the algebra.  The
single composition statement `fold_demandTake` says a demanded prefix folds as
the taken prefix of the reference stream — nothing more.  Scope throughout is
finite completed streams; infinite unfoldings, tabling, and anytime
convergence are later work and not implied here.

The legacy bridge: `Collect` reproduces today's collapse (exact occurrence
order); `Bag` is its order-quotient, schedule-invariant across complete
traversals by the sealed invariance theorems.
-/

namespace Mettapedia.GSLT.Dynamics.Collapse

open Mettapedia.GSLT.Dynamics.UnfoldingTraversal

/-! ## Observations and algebras -/

/-- One emitted observation: an answer, how many occurrences it stands for,
and a receipt.  Answer-only algebras take `Receipt := Unit`; counted sources
emit `multiplicity > 1` rows. -/
structure Obs (Ans Receipt : Type) where
  answer : Ans
  multiplicity : Nat
  receipt : Receipt

/-- A collapse algebra: the lawful sink for an observation stream. -/
structure CollapseAlgebra (O R Result : Type) where
  zero : R
  emit : O → R
  combine : R → R → R
  finish : R → Result

variable {O R Result : Type}

/-- Fold a completed observation stream.  This is the single semantic route;
everything an optimizer does must agree with it. -/
def foldStream (A : CollapseAlgebra O R Result) (l : List O) : R :=
  l.foldr (fun o acc => A.combine (A.emit o) acc) A.zero

@[simp] theorem foldStream_nil (A : CollapseAlgebra O R Result) :
    foldStream A [] = A.zero := rfl

@[simp] theorem foldStream_cons (A : CollapseAlgebra O R Result) (o : O) (l : List O) :
    foldStream A (o :: l) = A.combine (A.emit o) (foldStream A l) := rfl

/-- The observable result of a collapse. -/
def collapseWith (A : CollapseAlgebra O R Result) (l : List O) : Result :=
  A.finish (foldStream A l)

/-! ## Capability certificates -/

/-- Identity and associativity: the algebra is a monoid on its carrier. -/
structure MonoidCert (A : CollapseAlgebra O R Result) : Prop where
  zero_combine : ∀ r, A.combine A.zero r = r
  combine_zero : ∀ r, A.combine r A.zero = r
  assoc : ∀ a b c, A.combine (A.combine a b) c = A.combine a (A.combine b c)

/-- Commutativity: the stream may be reordered. -/
structure CommCert (A : CollapseAlgebra O R Result) : Prop where
  comm : ∀ a b, A.combine a b = A.combine b a

/-- Idempotence on emissions: duplicates of one observation may be elided. -/
structure IdemCert (A : CollapseAlgebra O R Result) : Prop where
  idem : ∀ o, A.combine (A.emit o) (A.emit o) = A.emit o

/-- An absorbing element: once reached, the fold may stop. -/
structure AbsorbingCert (A : CollapseAlgebra O R Result) (done : R) : Prop where
  absorb : ∀ r, A.combine done r = done

/-- Counted emission splits: a row carrying `m + n` occurrences means the same
as two rows carrying `m` and `n`. -/
structure MultCoherenceCert {Ans Receipt : Type}
    (A : CollapseAlgebra (Obs Ans Receipt) R Result) : Prop where
  split : ∀ (a : Ans) (ρ : Receipt) (m n : Nat),
    A.emit ⟨a, m + n, ρ⟩ = A.combine (A.emit ⟨a, m, ρ⟩) (A.emit ⟨a, n, ρ⟩)

/-! ## The monoid theorems: fusion without commutativity -/

/-- Streams concatenate under a monoid certificate. -/
theorem foldStream_append (A : CollapseAlgebra O R Result) (h : MonoidCert A)
    (l l' : List O) :
    foldStream A (l ++ l') = A.combine (foldStream A l) (foldStream A l') := by
  induction l with
  | nil => simp [h.zero_combine]
  | cons o rest ih => simp [ih, h.assoc]

/-- **Chunking/fusion.**  Folding chunk-results equals folding the flattened
stream — the streaming license, commutativity nowhere in sight. -/
theorem foldChunks_eq (A : CollapseAlgebra O R Result) (h : MonoidCert A)
    (chunks : List (List O)) :
    (chunks.map (foldStream A)).foldr A.combine A.zero
      = foldStream A chunks.flatten := by
  induction chunks with
  | nil => rfl
  | cons c rest ih => simp [List.flatten_cons, foldStream_append A h, ih]

/-- **Pull/fold refinement.**  A pull source that emits exactly the
materialized observations — same order, same multiplicity, once each — folds
to exactly the materialized collapse.  This is the license to fold backend
rows without constructing the intermediate tuple.  (The pull source's smallest
adequate model IS its emission list; sameness of emissions is literal
equality of that list.) -/
theorem foldPull_eq_materialized (A : CollapseAlgebra O R Result)
    {emissions materialized : List O} (hsame : emissions = materialized) :
    collapseWith A emissions = collapseWith A materialized := by
  rw [hsame]

/-! ## The commutativity theorem: reordering, sold separately -/

/-- **Reordering.**  With commutativity (and the monoid laws), permuted
streams fold equal: the schedule/parallel-merge license. -/
theorem fold_perm (A : CollapseAlgebra O R Result)
    (hm : MonoidCert A) (hc : CommCert A) {l l' : List O}
    (h : l.Perm l') : foldStream A l = foldStream A l' := by
  induction h with
  | nil => rfl
  | cons o _ ih => simp [ih]
  | swap a b l =>
    simp only [foldStream_cons]
    rw [← hm.assoc, ← hm.assoc, hc.comm (A.emit b) (A.emit a)]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## The idempotence theorem: deduplication -/

/-- **Deduplication.**  An adjacent duplicate emission may be elided under the
monoid and idempotence certificates. -/
theorem fold_dedup_adjacent (A : CollapseAlgebra O R Result)
    (hm : MonoidCert A) (hi : IdemCert A) (o : O) (l : List O) :
    foldStream A (o :: o :: l) = foldStream A (o :: l) := by
  simp only [foldStream_cons]
  rw [← hm.assoc, hi.idem]

/-! ## The absorbing theorem: early termination -/

/-- **Early termination.**  Once the running fold hits the absorbing element,
every suffix is irrelevant: stopping is sound.  Operationally this is the
per-row callback returning "stop". -/
theorem fold_absorbing_stop (A : CollapseAlgebra O R Result) {done : R}
    (h : AbsorbingCert A done) (suffix : List O) :
    suffix.foldl (fun acc o => A.combine acc (A.emit o)) done = done := by
  induction suffix with
  | nil => rfl
  | cons o rest ih => simpa [h.absorb] using ih

/-! ## The counted-row theorem -/

/-- Expand a counted observation into unit rows. -/
def expandObs {Ans Receipt : Type} (o : Obs Ans Receipt) : List (Obs Ans Receipt) :=
  List.replicate o.multiplicity ⟨o.answer, 1, o.receipt⟩

/-- **Counted rows.**  Under multiplicity-coherence (with zero-occurrence
emission meaning `zero`), a counted row folds as its expansion: a counted
source may feed the fold directly, no expansion materialized.  Notably the
monoid certificate is not needed — emission-level splitting suffices. -/
theorem fold_counted_row {Ans Receipt : Type}
    (A : CollapseAlgebra (Obs Ans Receipt) R Result)
    (hc : MultCoherenceCert A)
    (hzero : ∀ a ρ, A.emit ⟨a, 0, ρ⟩ = A.zero)
    (o : Obs Ans Receipt) :
    A.emit o = foldStream A (expandObs o) := by
  obtain ⟨a, m, ρ⟩ := o
  induction m with
  | zero => simp [expandObs, hzero]
  | succ k ih =>
    have hstep : foldStream A (expandObs ⟨a, k + 1, ρ⟩)
        = A.combine (A.emit ⟨a, 1, ρ⟩) (foldStream A (expandObs ⟨a, k, ρ⟩)) := by
      simp [expandObs, List.replicate_succ]
    rw [hstep, ← ih, show k + 1 = 1 + k from Nat.add_comm k 1]
    exact hc.split a ρ 1 k

/-! ## Instances -/

section Instances

variable {Ans Receipt : Type}

/-- The legacy algebra: collect answers in exact occurrence order.  This is
today's `collapse`. -/
def Collect (Ans Receipt : Type) :
    CollapseAlgebra (Obs Ans Receipt) (List Ans) (List Ans) where
  zero := []
  emit o := List.replicate o.multiplicity o.answer
  combine := (· ++ ·)
  finish := id

theorem collect_monoid : MonoidCert (Collect Ans Receipt) where
  zero_combine := by intro r; simp [Collect]
  combine_zero := by intro r; simp [Collect]
  assoc := by intro a b c; simp [Collect, List.append_assoc]

/-- The legacy bridge: on unit-multiplicity streams, `Collect` returns exactly
the answers in stream order — today's collapse, verbatim. -/
theorem collect_is_legacy_collapse (answers : List Ans) (ρ : Receipt) :
    collapseWith (Collect Ans Receipt)
        (answers.map fun a => ⟨a, 1, ρ⟩)
      = answers := by
  show foldStream (Collect Ans Receipt) (answers.map fun a => ⟨a, 1, ρ⟩) = answers
  induction answers with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, foldStream_cons, ih]
    simp [Collect]

/-- The bag algebra: the order-quotient of `Collect`. -/
def BagAlg (Ans Receipt : Type) :
    CollapseAlgebra (Obs Ans Receipt) (Multiset Ans) (Multiset Ans) where
  zero := 0
  emit o := Multiset.replicate o.multiplicity o.answer
  combine := (· + ·)
  finish := id

theorem bag_monoid : MonoidCert (BagAlg Ans Receipt) where
  zero_combine := by intro r; simp [BagAlg]
  combine_zero := by intro r; simp [BagAlg]
  assoc := by intro a b c; simp [BagAlg, add_assoc]

theorem bag_comm : CommCert (BagAlg Ans Receipt) where
  comm := by intro a b; simp [BagAlg, add_comm]

/-- **Bag schedule invariance.**  Complete traversals of one unfolding tree
give the same bag collapse — the sealed invariance theorem carried onto the
algebra interface. -/
theorem bag_schedule_invariant {trav trav' : Unfold Ans → List Ans}
    (h : Complete trav) (h' : Complete trav') (t : Unfold Ans) (ρ : Receipt) :
    collapseWith (BagAlg Ans Receipt) ((trav t).map fun a => ⟨a, 1, ρ⟩)
      = collapseWith (BagAlg Ans Receipt) ((trav' t).map fun a => ⟨a, 1, ρ⟩) :=
  fold_perm _ bag_monoid bag_comm
    ((complete_perm h h' t).map fun a => (⟨a, 1, ρ⟩ : Obs Ans Receipt))

/-- The counting algebra: answers weigh their multiplicities. -/
def CountAlg (Ans Receipt : Type) :
    CollapseAlgebra (Obs Ans Receipt) Nat Nat where
  zero := 0
  emit o := o.multiplicity
  combine := (· + ·)
  finish := id

theorem count_monoid : MonoidCert (CountAlg Ans Receipt) where
  zero_combine := by intro r; simp [CountAlg]
  combine_zero := by intro r; simp [CountAlg]
  assoc := by intro a b c; simp [CountAlg, Nat.add_assoc]

theorem count_multCoherence : MultCoherenceCert (CountAlg Ans Receipt) where
  split := by intro a ρ m n; simp [CountAlg]

/-- The existence algebra: `true` once anything is seen. -/
def AnyAlg (Ans Receipt : Type) :
    CollapseAlgebra (Obs Ans Receipt) Bool Bool where
  zero := false
  emit o := decide (o.multiplicity ≠ 0)
  combine := (· || ·)
  finish := id

theorem any_monoid : MonoidCert (AnyAlg Ans Receipt) where
  zero_combine := by intro r; simp [AnyAlg]
  combine_zero := by intro r; simp [AnyAlg]
  assoc := by intro a b c; simp [AnyAlg, Bool.or_assoc]

/-- `true` is absorbing for `Any`: stopping after the first witness is
sound. -/
theorem any_absorbing : AbsorbingCert (AnyAlg Ans Receipt) true where
  absorb := by intro r; simp [AnyAlg]

end Instances

/-! ## Negative witnesses: certificates are load-bearing

Each witness exhibits the optimization *changing an answer* for an algebra
without the certificate.  They are the optimizer's fence posts. -/

/-- A combine that subtracts (truncated): not associative. -/
def SubAlg : CollapseAlgebra Nat Nat Nat where
  zero := 0
  emit := id
  combine := (· - ·)
  finish := id

/-- **Chunking needs associativity.**  The subtracting algebra folds `[5,3,1]`
differently chunked as `[[5,3],[1]]` versus `[[5],[3,1]]`. -/
theorem chunking_needs_assoc :
    ([[5, 3], [1]].map (foldStream SubAlg)).foldr SubAlg.combine SubAlg.zero
      ≠ ([[5], [3, 1]].map (foldStream SubAlg)).foldr SubAlg.combine SubAlg.zero := by
  decide

/-- **Reordering needs commutativity.**  `Collect` (list append) distinguishes
`[a, b]` from `[b, a]`. -/
theorem reordering_needs_comm :
    foldStream (Collect Nat Unit) [⟨0, 1, ()⟩, ⟨1, 1, ()⟩]
      ≠ foldStream (Collect Nat Unit) [⟨1, 1, ()⟩, ⟨0, 1, ()⟩] := by
  simp [Collect, foldStream]

/-- The set algebra: idempotent union of answers (multiplicity forgotten). -/
def SetAlg : CollapseAlgebra (Obs Nat Unit) (List Nat) (List Nat) where
  zero := []
  emit o := [o.answer]
  combine a b := (a ++ b).dedup
  finish := id

/-- **Idempotent algebras cannot implement bag semantics.**  The set algebra
maps a duplicated observation stream to a single occurrence, while the bag
keeps two: dedup is a genuine quotient, not a free optimization. -/
theorem idempotent_is_not_bag :
    (foldStream SetAlg [⟨7, 1, ()⟩, ⟨7, 1, ()⟩]).length
      ≠ Multiset.card (foldStream (BagAlg Nat Unit) [⟨7, 1, ()⟩, ⟨7, 1, ()⟩]) := by
  decide

/-- **Early stopping needs an absorbing element.**  Stopping `Count` after the
first row changes the result. -/
theorem count_cannot_stop_early :
    foldStream (CountAlg Nat Unit) [⟨0, 1, ()⟩]
      ≠ foldStream (CountAlg Nat Unit) [⟨0, 1, ()⟩, ⟨1, 1, ()⟩] := by
  decide

/-- **And with an absorbing element it is sound**: `Any` may stop at its first
`true` — the suffix cannot change the outcome (positive twin, from the
certificate theorem). -/
theorem any_can_stop_early (suffix : List (Obs Nat Unit)) :
    suffix.foldl
      (fun acc o => (AnyAlg Nat Unit).combine acc ((AnyAlg Nat Unit).emit o))
      true = true :=
  fold_absorbing_stop _ any_absorbing suffix

/-! ## Control composes from outside only -/

/-- Folding a demanded prefix equals folding the taken prefix of the reference
stream — a composition fact about `demandTake`, not a property of any algebra.
No commutation with arbitrary algebras is claimed. -/
theorem fold_demandTake {Ans : Type} (A : CollapseAlgebra Ans R Result)
    (k : Nat) (t : Unfold Ans) :
    foldStream A (demandTake k t) = foldStream A ((preOrder t).take k) := by
  rw [demandTake_eq_take]

end Mettapedia.GSLT.Dynamics.Collapse
