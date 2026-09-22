/-
# A rule's right-hand side, compiled over all of its matched variables

`MetavariableRouting.lean` compiles the occurrences of **one** metavariable, with
duplication where they diverge. Running the census on `mettaHE` showed that is
the wrong shape for real rules, and showed it decisively:

```
    rules with ≥ 2 distinct metavariables in the right-hand side   58 of 58
    largest number of distinct metavariables in one right-hand side      7
    rules where some metavariable occurs more than once                  4
    largest multiplicity of a single metavariable                        2
```

So every rule has several metavariables, and duplication — the expensive case a
`Placement` is built around — is rare. The priority is inverted from what the
single-metavariable development assumed: what a rule needs is **one skeleton
reading from many names**, with duplication as the occasional extra.

A `Skeleton` is that: a binary tree over the target's two node shapes whose
leaves are either statically known subterms or a **read** of the matched value
arriving at a named channel. `fill` gives the right-hand side under an
environment; `supply` gives the messages that environment delivers; `compile`
emits the soup.

`compile_reaches`:

```
    compile s sk outName offset ‖ sk.supply env   ⟶*   mm outName (sk.fill env)
```

No positional bookkeeping: each leaf carries the name it reads from, so any
number of distinct matched variables is handled without threading a list of
inputs through the recursion.

## Cost

`atomCount_compile` is again an equality: one atom per leaf and one per node.
`cost_eq_leaves` turns it into `cost sk + 1 = 2 * leaves sk`, so a skeleton with
`n` leaves compiles to exactly `2n - 1` atoms — the leaves plus the `n-1`
internal nodes of a binary tree.

## Where duplication reappears

A metavariable used twice is two `read` leaves at the *same* name. Reachability
still holds — two forwarders and two messages at that name both fire — but
linearity does not, and correctly so: two atoms listening at one name is exactly
the condition `Linear` forbids. `linear_of_reads_nodup` proves the converse
boundary: when the read names are distinct, the compiled soup is linear.

By the census that covers 54 of the 58 rules directly. The remaining four need a
duplicator per repeated variable, which is what `MetavariableRouting.build`
supplies; composing the two is **not** done here.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.MetavariableRouting

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## Skeletons -/

/-- The shape of a rule's right-hand side over its matched variables: each leaf
is either statically known or a read of the value arriving at a named channel. -/
inductive Skeleton where
  | read : Comb → Skeleton
  | const : Comb → Skeleton
  | nodePar : Skeleton → Skeleton → Skeleton
  | nodeMsg : Skeleton → Skeleton → Skeleton

namespace Skeleton

/-- The right-hand side a skeleton denotes under an environment. -/
def fill : Skeleton → (Comb → Comb) → Comb
  | read channel, env => env channel
  | const subterm, _ => subterm
  | nodePar left right, env => par (left.fill env) (right.fill env)
  | nodeMsg left right, env => mm (left.fill env) (right.fill env)

/-- The messages the environment delivers: one per read. -/
def supply : Skeleton → (Comb → Comb) → Comb
  | read channel, env => mm channel (env channel)
  | const _, _ => nil
  | nodePar left right, env => par (left.supply env) (right.supply env)
  | nodeMsg left right, env => par (left.supply env) (right.supply env)

/-- The leaves of a skeleton. -/
def leaves : Skeleton → ℕ
  | read _ => 1
  | const _ => 1
  | nodePar left right => left.leaves + right.leaves
  | nodeMsg left right => left.leaves + right.leaves

/-- The channels a skeleton reads from, in order. -/
def readChannels : Skeleton → List Comb
  | read channel => [channel]
  | const _ => []
  | nodePar left right => left.readChannels ++ right.readChannels
  | nodeMsg left right => left.readChannels ++ right.readChannels

/-- How many slots a compiled skeleton reserves: two per internal node. -/
def slotsUsed : Skeleton → ℕ
  | read _ => 0
  | const _ => 0
  | nodePar left right => left.slotsUsed + right.slotsUsed + 2
  | nodeMsg left right => left.slotsUsed + right.slotsUsed + 2

/-- What compiling a skeleton costs: one atom per leaf, one per node. -/
def cost : Skeleton → ℕ
  | read _ => 1
  | const _ => 1
  | nodePar left right => left.cost + right.cost + 1
  | nodeMsg left right => left.cost + right.cost + 1

/-- **A skeleton with `n` leaves compiles to `2n - 1` atoms**: the leaves plus
the `n-1` internal nodes a binary tree has. -/
theorem cost_eq_leaves : ∀ sk : Skeleton, sk.cost + 1 = 2 * sk.leaves
  | read _ => rfl
  | const _ => rfl
  | nodePar left right | nodeMsg left right => by
      have ihl := cost_eq_leaves left
      have ihr := cost_eq_leaves right
      simp only [cost, leaves]
      omega

end Skeleton

/-! ## The compiler -/

/-- **Compile a skeleton.**  A read leaf forwards the arriving name to the
output; a constant leaf emits it directly; a node compiles both sides into
reserved slots and rejoins their results with a constructor. -/
def compileSkeleton (s : Comb) : Skeleton → Comb → ℕ → Comb
  | .read channel, outName, _ => fw channel outName
  | .const subterm, outName, _ => mm outName subterm
  | .nodePar left right, outName, offset =>
      par (compileSkeleton s left (slot s offset) (offset + 2))
        (par (compileSkeleton s right (slot s (offset + 1))
              (offset + 2 + left.slotsUsed))
          (consPar (slot s offset) (slot s (offset + 1)) outName))
  | .nodeMsg left right, outName, offset =>
      par (compileSkeleton s left (slot s offset) (offset + 2))
        (par (compileSkeleton s right (slot s (offset + 1))
              (offset + 2 + left.slotsUsed))
          (consMsg (slot s offset) (slot s (offset + 1)) outName))

/-- **One node.**  Two independently supplied sides run and their results are
rejoined.  Unlike a duplication node there is no name to split: the two sides
were supplied separately from the start. -/
theorem node_pair_reaches {sub₁ sub₂ sup₁ sup₂ o₁ o₂ r₁ r₂ atom result : Comb}
    (ih₁ : ReachesFull (par sub₁ sup₁) (mm o₁ r₁))
    (ih₂ : ReachesFull (par sub₂ sup₂) (mm o₂ r₂))
    (fire : ReachesFull (par atom (par (mm o₁ r₁) (mm o₂ r₂))) result) :
    ReachesFull (par (par sub₁ (par sub₂ atom)) (par sup₁ sup₂)) result := by
  refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
      components (par (par sub₁ (par sub₂ atom)) (par sup₁ sup₂))
        = components (par (par sub₁ sup₁) (par sup₂ (par sub₂ atom)))
      from by simp only [components]; ac_rfl))) ?_
  refine ReachesFull.trans (ReachesFull.parLeft _ ih₁) ?_
  refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
      components (par (mm o₁ r₁) (par sup₂ (par sub₂ atom)))
        = components (par (par sub₂ sup₂) (par (mm o₁ r₁) atom))
      from by simp only [components]; ac_rfl))) ?_
  refine ReachesFull.trans (ReachesFull.parLeft _ ih₂) ?_
  refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
      components (par (mm o₂ r₂) (par (mm o₁ r₁) atom))
        = components (par atom (par (mm o₁ r₁) (mm o₂ r₂)))
      from by simp only [components]; ac_rfl))) ?_
  exact fire

/-- **The compiled right-hand side is built from the matched values.**  Supplied
with one message per read, the compiled soup reaches the right-hand side the
skeleton denotes.  Any number of distinct matched variables is covered: each leaf
names its own channel. -/
theorem compileSkeleton_reaches (s : Comb) (env : Comb → Comb) :
    ∀ (sk : Skeleton) (outName : Comb) (offset : ℕ),
    ReachesFull (par (compileSkeleton s sk outName offset) (sk.supply env))
      (mm outName (sk.fill env))
  | .read channel, outName, _ =>
      ReachesFull.ofReaches (Reaches.single
        (StepMinus.forward outName (env channel) (Cong.refl channel)))
  | .const _subterm, _outName, _ =>
      ReachesFull.congruent (Cong.parNil _)
  | .nodePar left right, outName, offset =>
      node_pair_reaches
        (compileSkeleton_reaches s env left (slot s offset) (offset + 2))
        (compileSkeleton_reaches s env right (slot s (offset + 1))
          (offset + 2 + left.slotsUsed))
        (ReachesFull.single (Step.buildPar outName (left.fill env) (right.fill env)
          (Cong.refl _) (Cong.refl _)))
  | .nodeMsg left right, outName, offset =>
      node_pair_reaches
        (compileSkeleton_reaches s env left (slot s offset) (offset + 2))
        (compileSkeleton_reaches s env right (slot s (offset + 1))
          (offset + 2 + left.slotsUsed))
        (ReachesFull.single (Step.buildMsg outName (left.fill env) (right.fill env)
          (Cong.refl _) (Cong.refl _)))

/-- **The compiled soup has exactly `cost` atoms.** -/
theorem atomCount_compileSkeleton (s : Comb) :
    ∀ (sk : Skeleton) (outName : Comb) (offset : ℕ),
    atomCount (compileSkeleton s sk outName offset) = sk.cost
  | .read _, _, _ => rfl
  | .const _, _, _ => rfl
  | .nodePar left right, _outName, offset
  | .nodeMsg left right, _outName, offset => by
      have ihl := atomCount_compileSkeleton s left (slot s offset) (offset + 2)
      have ihr := atomCount_compileSkeleton s right (slot s (offset + 1))
        (offset + 2 + left.slotsUsed)
      simp only [atomCount, compileSkeleton, componentList, List.length_append,
        List.length_cons, List.length_nil, Skeleton.cost] at ihl ihr ⊢
      omega

/-- **Reachability and cost together**, with the leaf law. -/
theorem compileSkeleton_reaches_at_exact_cost (s : Comb) (env : Comb → Comb)
    (sk : Skeleton) (outName : Comb) :
    ReachesFull (par (compileSkeleton s sk outName 0) (sk.supply env))
        (mm outName (sk.fill env))
      ∧ atomCount (compileSkeleton s sk outName 0) = sk.cost
      ∧ sk.cost + 1 = 2 * sk.leaves :=
  ⟨compileSkeleton_reaches s env sk outName 0,
    atomCount_compileSkeleton s sk outName 0,
    Skeleton.cost_eq_leaves sk⟩

/-! ## A worked rule with two distinct variables

The shape a MeTTa rule of the form `f(X, Y) → g(Y, X)` induces: two distinct
matched variables, each read once, recombined in the other order.
-/

/-- Two distinct matched values, swapped. -/
def swapTwo (a b : Comb) : Skeleton :=
  .nodeMsg (.read b) (.read a)

theorem swapTwo_fill (a b : Comb) (env : Comb → Comb) :
    (swapTwo a b).fill env = mm (env b) (env a) := rfl

theorem swapTwo_leaves (a b : Comb) : (swapTwo a b).leaves = 2 := rfl

/-- **The worked rule, compiled and proved.**  Three atoms — one forwarder per
matched variable and one constructor to recombine them — deliver both values and
rebuild the right-hand side in the swapped order. -/
theorem swapTwo_compiles (s a b outName : Comb) (env : Comb → Comb) :
    ReachesFull (par (compileSkeleton s (swapTwo a b) outName 0)
        ((swapTwo a b).supply env))
        (mm outName (mm (env b) (env a)))
      ∧ atomCount (compileSkeleton s (swapTwo a b) outName 0) = 3 :=
  ⟨compileSkeleton_reaches s env (swapTwo a b) outName 0,
    atomCount_compileSkeleton s (swapTwo a b) outName 0⟩

/-! ## Linearity, and where duplication reappears -/

/-- **The listening positions of a compiled skeleton.**  The channels it reads
from, plus wiring slots inside the range it reserved. -/
theorem compileSkeleton_listening_structure (s : Comb) :
    ∀ (sk : Skeleton) (outName : Comb) (offset : ℕ),
    ∃ wiring : Multiset Comb,
      listeningSubjects (compileSkeleton s sk outName offset)
          = (sk.readChannels : Multiset Comb) + wiring
        ∧ wiring.Nodup
        ∧ ∀ x ∈ wiring, ∃ i, offset ≤ i ∧ i < offset + sk.slotsUsed ∧ x = slot s i
  | .read channel, outName, _ =>
      ⟨0, by
        rw [compileSkeleton, listeningSubjects_of_atom (t := fw channel outName) rfl]
        simp only [listenSubjects, Skeleton.readChannels, add_zero],
        Multiset.nodup_zero, by simp⟩
  | .const subterm, outName, _ =>
      ⟨0, by
        rw [compileSkeleton, listeningSubjects_of_atom (t := mm outName subterm) rfl]
        simp only [listenSubjects, Skeleton.readChannels, Multiset.coe_nil]
        rfl,
        Multiset.nodup_zero, by simp⟩
  | .nodePar left right, outName, offset
  | .nodeMsg left right, outName, offset => by
      obtain ⟨w₁, hEq₁, hN₁, hS₁⟩ :=
        compileSkeleton_listening_structure s left (slot s offset) (offset + 2)
      obtain ⟨w₂, hEq₂, hN₂, hS₂⟩ :=
        compileSkeleton_listening_structure s right (slot s (offset + 1))
          (offset + 2 + left.slotsUsed)
      refine ⟨(w₁ + w₂) + ({slot s offset} + {slot s (offset + 1)}), ?_, ?_, ?_⟩
      · rw [compileSkeleton, listeningSubjects_par, listeningSubjects_par,
          hEq₁, hEq₂]
        simp only [listeningSubjects, components, Multiset.singleton_bind,
          listenSubjects, Skeleton.readChannels, coe_pair]
        rw [show ((left.readChannels ++ right.readChannels : List Comb) : Multiset Comb)
            = (left.readChannels : Multiset Comb) + (right.readChannels : Multiset Comb)
          from rfl]
        ac_rfl
      · rw [Multiset.nodup_add]
        refine ⟨?_, nodup_pair_add (slot_ne (by omega)), ?_⟩
        · rw [Multiset.nodup_add]
          refine ⟨hN₁, hN₂, Multiset.disjoint_left.mpr ?_⟩
          intro a ha hb
          obtain ⟨i, hi, hiLt, rfl⟩ := hS₁ a ha
          obtain ⟨j, hj, hjLt, hslot⟩ := hS₂ _ hb
          have := slot_injective s hslot
          omega
        · refine Multiset.disjoint_left.mpr ?_
          intro a ha hb
          simp only [Multiset.mem_add, Multiset.mem_singleton] at ha hb
          rcases ha with h | h
          · obtain ⟨i, hi, hiLt, rfl⟩ := hS₁ a h
            rcases hb with hb | hb <;> exact absurd (slot_injective s hb) (by omega)
          · obtain ⟨i, hi, hiLt, rfl⟩ := hS₂ a h
            rcases hb with hb | hb <;> exact absurd (slot_injective s hb) (by omega)
      · intro x hx
        simp only [Multiset.mem_add, Multiset.mem_singleton] at hx
        simp only [Skeleton.slotsUsed]
        rcases hx with (h | h) | hb | hb
        · obtain ⟨i, hi, hiLt, rfl⟩ := hS₁ x h; exact ⟨i, by omega, by omega, rfl⟩
        · obtain ⟨i, hi, hiLt, rfl⟩ := hS₂ x h; exact ⟨i, by omega, by omega, rfl⟩
        · exact ⟨offset, by omega, by omega, hb⟩
        · exact ⟨offset + 1, by omega, by omega, hb⟩

/-- **The speaking positions of a compiled skeleton.**  Only constant leaves
speak, each at the slot its parent reads. -/
theorem compileSkeleton_speaking_structure (s : Comb) :
    ∀ (sk : Skeleton) (outName : Comb) (offset : ℕ),
    ∃ speaking : Multiset Comb,
      speakingSubjects (compileSkeleton s sk outName offset) = speaking
        ∧ speaking.Nodup
        ∧ ∀ x ∈ speaking, x = outName ∨
            ∃ i, offset ≤ i ∧ i < offset + sk.slotsUsed ∧ x = slot s i
  | .read channel, outName, _ =>
      ⟨0, by
        rw [compileSkeleton, speakingSubjects_of_atom (t := fw channel outName) rfl]
        simp only [speakSubjects, Multiset.coe_nil],
        Multiset.nodup_zero, by simp⟩
  | .const subterm, outName, _ =>
      ⟨{outName}, by
        rw [compileSkeleton, speakingSubjects_of_atom (t := mm outName subterm) rfl]
        simp only [speakSubjects, coe_single],
        Multiset.nodup_singleton _, by simp⟩
  | .nodePar left right, outName, offset
  | .nodeMsg left right, outName, offset => by
      obtain ⟨s₁, hEq₁, hN₁, hS₁⟩ :=
        compileSkeleton_speaking_structure s left (slot s offset) (offset + 2)
      obtain ⟨s₂, hEq₂, hN₂, hS₂⟩ :=
        compileSkeleton_speaking_structure s right (slot s (offset + 1))
          (offset + 2 + left.slotsUsed)
      refine ⟨s₁ + s₂, ?_, ?_, ?_⟩
      · rw [compileSkeleton, speakingSubjects_par, speakingSubjects_par,
          hEq₁, hEq₂]
        simp only [speakingSubjects, components, Multiset.singleton_bind,
          speakSubjects, Multiset.coe_nil]
        ac_rfl
      · rw [Multiset.nodup_add]
        refine ⟨hN₁, hN₂, Multiset.disjoint_left.mpr ?_⟩
        intro a ha hb
        rcases hS₁ a ha with rfl | ⟨i, hi, hiLt, rfl⟩
        · rcases hS₂ _ hb with hb' | ⟨j, hj, hjLt, hb'⟩
          · have := slot_injective s hb'; omega
          · have := slot_injective s hb'; omega
        · rcases hS₂ _ hb with hb' | ⟨j, hj, hjLt, hb'⟩
          · have := slot_injective s hb'; omega
          · have := slot_injective s hb'; omega
      · intro x hx
        simp only [Multiset.mem_add] at hx
        simp only [Skeleton.slotsUsed]
        refine Or.inr ?_
        rcases hx with h | h
        · rcases hS₁ x h with rfl | ⟨i, hi, hiLt, rfl⟩
          · exact ⟨offset, by omega, by omega, rfl⟩
          · exact ⟨i, by omega, by omega, rfl⟩
        · rcases hS₂ x h with rfl | ⟨i, hi, hiLt, rfl⟩
          · exact ⟨offset + 1, by omega, by omega, rfl⟩
          · exact ⟨i, by omega, by omega, rfl⟩

/-- **A skeleton with distinct read channels compiles to a linear soup.**  The
hypotheses are the two a caller controls: the matched variables are distinct, and
their channels come from a namespace the compiler does not allocate in.

By the census this covers 54 of `mettaHE`'s 58 rules.  The other four repeat a
metavariable, which is two reads at one channel — reachability survives, this
does not, and correctly so. -/
theorem compileSkeleton_linear (s : Comb) (sk : Skeleton) (outName : Comb)
    (hdistinct : sk.readChannels.Nodup)
    (hfresh : ∀ channel ∈ sk.readChannels, ∀ i : ℕ, channel ≠ slot s i) :
    Linear (compileSkeleton s sk outName 0) where
  listening := by
    obtain ⟨wiring, hEq, hN, hS⟩ :=
      compileSkeleton_listening_structure s sk outName 0
    rw [hEq, Multiset.nodup_add]
    refine ⟨Multiset.coe_nodup.mpr hdistinct, hN, Multiset.disjoint_left.mpr ?_⟩
    intro a ha hb
    obtain ⟨i, -, -, hi⟩ := hS a hb
    exact hfresh a (Multiset.mem_coe.mp ha) i hi
  speaking := by
    obtain ⟨speaking, hEq, hN, -⟩ :=
      compileSkeleton_speaking_structure s sk outName 0
    rw [hEq]; exact hN

/-- **All three guarantees for a compiled right-hand side.** -/
theorem compileSkeleton_verified (s : Comb) (env : Comb → Comb) (sk : Skeleton)
    (outName : Comb) (hdistinct : sk.readChannels.Nodup)
    (hfresh : ∀ channel ∈ sk.readChannels, ∀ i : ℕ, channel ≠ slot s i) :
    ReachesFull (par (compileSkeleton s sk outName 0) (sk.supply env))
        (mm outName (sk.fill env))
      ∧ atomCount (compileSkeleton s sk outName 0) = sk.cost
      ∧ Linear (compileSkeleton s sk outName 0) :=
  ⟨compileSkeleton_reaches s env sk outName 0,
    atomCount_compileSkeleton s sk outName 0,
    compileSkeleton_linear s sk outName hdistinct hfresh⟩

/-! ## Composing with duplication

A metavariable used twice is two reads at the same channel, which breaks
linearity.  The repair is to give the two occurrences **distinct** channels and
feed both from one duplicator — which is what `distributor` does, and
`distributor_broadcasts` already proves it delivers one payload to every
delivery subject.

So the two developments compose: the skeleton reads distinct channels, and a
distributor in front turns one matched value into one message per channel.
By the census the largest multiplicity in `mettaHE` is two, so a single
duplicator covers all four of the rules the linear case missed.
-/

/-- **A skeleton fed through a distributor.**  One message at the source reaches
one at each delivery subject, and the skeleton reads those.  The hypothesis says
exactly that the skeleton's reads are the distributor's deliveries, all carrying
the matched value. -/
theorem distributed_skeleton_reaches (s : Comb) (env : Comb → Comb)
    (sk : Skeleton) (outName subject payload : Comb) (chain : List (Comb × Comb))
    (hsupply : sk.supply env = broadcast payload (deliveries subject chain)) :
    ReachesFull (par (par (distributor subject chain)
        (compileSkeleton s sk outName 0)) (mm subject payload))
      (mm outName (sk.fill env)) := by
  refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
      components (par (par (distributor subject chain)
          (compileSkeleton s sk outName 0)) (mm subject payload))
        = components (par (par (distributor subject chain) (mm subject payload))
          (compileSkeleton s sk outName 0))
      from by simp only [components]; ac_rfl))) ?_
  refine ReachesFull.trans (ReachesFull.parLeft _
    (ReachesFull.ofReaches (distributor_broadcasts payload chain subject))) ?_
  refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
      components (par (broadcast payload (deliveries subject chain))
          (compileSkeleton s sk outName 0))
        = components (par (compileSkeleton s sk outName 0)
          (broadcast payload (deliveries subject chain)))
      from by simp only [components]; ac_rfl))) ?_
  rw [← hsupply]
  exact compileSkeleton_reaches s env sk outName 0

/-- A matched value read at two distinct channels. -/
def readTwice (first second : Comb) : Skeleton :=
  .nodePar (.read first) (.read second)

theorem readTwice_fill (first second v : Comb) :
    (readTwice first second).fill (fun _ => v) = par v v := rfl

/-- The two reads are exactly what one duplicator delivers.  The delivery
subjects of a one-link chain are its target and the name it ends at, whatever
subject it started from. -/
theorem readTwice_supply (subject first second v : Comb) :
    (readTwice first second).supply (fun _ => v)
      = broadcast v (deliveries subject [(first, second)]) := rfl

/-- **The repeated-metavariable case, composed and verified.**  One duplicator
and a two-read skeleton: the matched value arrives once at the source, the
duplicator splits it to the two occurrence channels, and the skeleton rebuilds
the right-hand side with the value in both positions. -/
theorem readTwice_composed_reaches (s subject first second outName v : Comb) :
    ReachesFull (par (par (distributor subject [(first, second)])
        (compileSkeleton s (readTwice first second) outName 0))
        (mm subject v))
      (mm outName (par v v)) :=
  distributed_skeleton_reaches s (fun _ => v) (readTwice first second)
    outName subject v [(first, second)] (readTwice_supply subject first second v)

/-- The composed soup is four atoms: the duplicator, the two forwarders that
place the occurrences, and the constructor that rejoins them.  Exactly the count
the single-metavariable compiler gives for the same rule. -/
theorem readTwice_composed_atomCount (s subject first second outName : Comb) :
    atomCount (par (distributor subject [(first, second)])
      (compileSkeleton s (readTwice first second) outName 0)) = 4 := by
  simp only [atomCount, distributor, compileSkeleton, readTwice, componentList,
    List.length_append, List.length_cons, List.length_nil]

/-- **The composed soup is linear.**  Five listening positions — the source, the
two occurrence channels, and the two wiring slots — pairwise distinct under the
stated hypotheses, so no name has two possible partners.  The hypotheses are the
ones a caller controls: three distinct channels, none of them a slot the
compiler allocates. -/
theorem readTwice_composed_linear (s subject first second outName : Comb)
    (hsf : subject ≠ first) (hss : subject ≠ second) (hfs : first ≠ second)
    (hsubject : ∀ i : ℕ, subject ≠ slot s i)
    (hfirst : ∀ i : ℕ, first ≠ slot s i)
    (hsecond : ∀ i : ℕ, second ≠ slot s i) :
    Linear (par (distributor subject [(first, second)])
      (compileSkeleton s (readTwice first second) outName 0)) where
  listening := by
    have shape : listeningSubjects (par (distributor subject [(first, second)])
        (compileSkeleton s (readTwice first second) outName 0))
        = ((([subject, first, second, slot s 0, slot s 1] : List Comb)) :
            Multiset Comb) := by
      simp only [listeningSubjects, distributor, compileSkeleton, readTwice,
        components, listenSubjects, Multiset.add_bind, Multiset.singleton_bind]
      rfl
    rw [shape, Multiset.coe_nodup]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, and_true, not_or]
    exact ⟨⟨hsf, hss, hsubject 0, hsubject 1⟩, ⟨hfs, hfirst 0, hfirst 1⟩,
      ⟨hsecond 0, hsecond 1⟩, ⟨slot_ne (by omega), not_false⟩⟩
  speaking := by
    have shape : speakingSubjects (par (distributor subject [(first, second)])
        (compileSkeleton s (readTwice first second) outName 0)) = 0 := by
      simp only [speakingSubjects, distributor, compileSkeleton, readTwice,
        components, speakSubjects, Multiset.add_bind, Multiset.singleton_bind]
      rfl
    rw [shape]
    exact Multiset.nodup_zero

/-- **All three guarantees for the composed repeated-variable case.**  With this
and `compileSkeleton_verified` the two shapes a MeTTa right-hand side can take —
several distinct variables, and one variable repeated — are both compiled with
reachability, exact cost, and linearity. -/
theorem readTwice_composed_verified (s subject first second outName v : Comb)
    (hsf : subject ≠ first) (hss : subject ≠ second) (hfs : first ≠ second)
    (hsubject : ∀ i : ℕ, subject ≠ slot s i)
    (hfirst : ∀ i : ℕ, first ≠ slot s i)
    (hsecond : ∀ i : ℕ, second ≠ slot s i) :
    ReachesFull (par (par (distributor subject [(first, second)])
        (compileSkeleton s (readTwice first second) outName 0)) (mm subject v))
        (mm outName (par v v))
      ∧ atomCount (par (distributor subject [(first, second)])
          (compileSkeleton s (readTwice first second) outName 0)) = 4
      ∧ Linear (par (distributor subject [(first, second)])
          (compileSkeleton s (readTwice first second) outName 0)) :=
  ⟨readTwice_composed_reaches s subject first second outName v,
    readTwice_composed_atomCount s subject first second outName,
    readTwice_composed_linear s subject first second outName hsf hss hfs
      hsubject hfirst hsecond⟩

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
