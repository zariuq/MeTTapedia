/-
# Renaming reads apart

Two places in this lane stop at the same boundary: a skeleton whose read
channels repeat is not linear, and `translate`'s input clause delivers to a
single proxy that several occurrences would contend for. `FanOut.lean` supplies
the delivery side — one name reaches `k` channels at `k - 1` atoms. What was
missing is the renaming: making the `k` channels distinct in the first place.

`freshReads` does it uniformly. Every read is renamed to a fresh channel, drawn
in order from an injective supply, with a counter threaded through the
recursion. No repetition analysis is needed — renaming *all* reads is simpler
than renaming the repeated ones and gives the same guarantee.

```
    readChannels (freshReads fresh sk n).1
        = (List.range (freshReads fresh sk n).2 - n).map fresh
```

which `readChannels_freshReads` states as an exact list and
`nodup_readChannels_freshReads` turns into distinctness. With that,
`compileSkeleton_linear`'s first hypothesis is discharged by construction rather
than assumed, and what remains is to supply the fresh channels — which is
`fanOut_broadcasts`.

## What the counter buys

The renaming is the third place in this lane where a counter replaced a
structural scheme and made a proof arithmetic: `assemble`'s slots, `build`'s
ranges, and now the read channels. The pattern is worth naming — when
distinctness is the property you need, allocate from a counter and distinctness
becomes an inequality between numbers.

## The denotation

`fill_freshReads` is the correspondence: the renamed skeleton denotes the same
term under an environment that agrees with the original's through the renaming.

The agreement is stated as `List.Forall₂` between the renamed channels and the
originals rather than as an indexed condition. That is what makes the node cases
go through: `forall₂_take_append` and `forall₂_drop_append` split the agreement
at the same place `readChannels` splits, and `length_readChannels_freshReads`
says the split lands in the right place. An indexed formulation needs
`getD`-across-append lemmas that do not exist, which is what an earlier attempt
foundered on.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.FanOut
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.RuleSkeleton

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## The renaming -/

/-- Rename every read to a fresh channel, drawn in order from `fresh`, threading
a counter.  The second component is the next unused index. -/
def freshReads (fresh : ℕ → Comb) : Skeleton → ℕ → Skeleton × ℕ
  | .read _, next => (.read (fresh next), next + 1)
  | .const subterm, next => (.const subterm, next)
  | .nodePar left right, next =>
      let leftResult := freshReads fresh left next
      let rightResult := freshReads fresh right leftResult.2
      (.nodePar leftResult.1 rightResult.1, rightResult.2)
  | .nodeMsg left right, next =>
      let leftResult := freshReads fresh left next
      let rightResult := freshReads fresh right leftResult.2
      (.nodeMsg leftResult.1 rightResult.1, rightResult.2)

/-- The counter advances by one per read. -/
theorem freshReads_counter (fresh : ℕ → Comb) :
    ∀ (sk : Skeleton) (next : ℕ),
      (freshReads fresh sk next).2 = next + sk.readChannels.length
  | .read _, next => by simp [freshReads, Skeleton.readChannels]
  | .const _, next => by simp [freshReads, Skeleton.readChannels]
  | .nodePar left right, next | .nodeMsg left right, next => by
      have ihl := freshReads_counter fresh left next
      have ihr := freshReads_counter fresh right (freshReads fresh left next).2
      simp only [freshReads, Skeleton.readChannels, List.length_append] at ihl ihr ⊢
      omega

/-- The renaming leaves the shape alone: same leaves, same nodes, same cost. -/
theorem cost_freshReads (fresh : ℕ → Comb) :
    ∀ (sk : Skeleton) (next : ℕ), (freshReads fresh sk next).1.cost = sk.cost
  | .read _, _ => rfl
  | .const _, _ => rfl
  | .nodePar left right, next | .nodeMsg left right, next => by
      have ihl := cost_freshReads fresh left next
      have ihr := cost_freshReads fresh right (freshReads fresh left next).2
      simp only [freshReads, Skeleton.cost] at ihl ihr ⊢
      omega

/-! ## The renamed channels are a run of the supply -/

/-- **The renamed read channels are exactly `fresh next, fresh (next+1), …`**, one
per read, in order. -/
theorem readChannels_freshReads (fresh : ℕ → Comb) :
    ∀ (sk : Skeleton) (next : ℕ),
      (freshReads fresh sk next).1.readChannels
        = (List.range' next sk.readChannels.length).map fresh
  | .read _, next => by simp [freshReads, Skeleton.readChannels]
  | .const _, next => by simp [freshReads, Skeleton.readChannels]
  | .nodePar left right, next | .nodeMsg left right, next => by
      have ihl := readChannels_freshReads fresh left next
      have ihr := readChannels_freshReads fresh right
        (freshReads fresh left next).2
      have counter := freshReads_counter fresh left next
      rw [counter] at ihr
      simp only [freshReads, Skeleton.readChannels, ihl, ihr, counter,
        List.length_append, ← List.map_append, List.range'_append_1]

/-- **And they are distinct**, whenever the supply is injective. -/
theorem nodup_readChannels_freshReads (fresh : ℕ → Comb)
    (hfresh : Function.Injective fresh) (sk : Skeleton) (next : ℕ) :
    (freshReads fresh sk next).1.readChannels.Nodup := by
  rw [readChannels_freshReads fresh sk next]
  exact List.Nodup.map hfresh List.nodup_range'

/-! ## Linearity by construction -/

/-- **A renamed skeleton compiles to a linear soup.**  The distinctness
hypothesis `compileSkeleton_linear` needs is discharged by the renaming rather
than assumed; what a caller still supplies is that the fresh channels avoid the
compiler's slots. -/
theorem freshReads_compiles_linear (s : Comb) (fresh : ℕ → Comb)
    (hfresh : Function.Injective fresh) (sk : Skeleton) (next : ℕ)
    (outName : Comb)
    (havoid : ∀ index : ℕ, ∀ slotIndex : ℕ, fresh index ≠ slot s slotIndex) :
    Linear (compileSkeleton s (freshReads fresh sk next).1 outName 0) := by
  refine compileSkeleton_linear s _ outName
    (nodup_readChannels_freshReads fresh hfresh sk next) ?_
  intro channel hchannel index
  rw [readChannels_freshReads fresh sk next] at hchannel
  obtain ⟨position, -, rfl⟩ := List.mem_map.mp hchannel
  exact havoid position index

/-- And the cost is unchanged by the renaming, so making a skeleton linear costs
nothing in the skeleton itself — the price is the fan-out that supplies the
renamed channels, which `fanOut_broadcasts` puts at one atom per extra use. -/
theorem freshReads_cost_unchanged (s : Comb) (fresh : ℕ → Comb) (sk : Skeleton)
    (next : ℕ) (outName : Comb) :
    atomCount (compileSkeleton s (freshReads fresh sk next).1 outName 0)
      = sk.cost := by
  rw [atomCount_compileSkeleton, cost_freshReads]

/-! ## The denotation correspondence -/

/-- The renaming preserves the number of reads. -/
theorem length_readChannels_freshReads (fresh : ℕ → Comb) (sk : Skeleton)
    (next : ℕ) :
    (freshReads fresh sk next).1.readChannels.length = sk.readChannels.length := by
  rw [readChannels_freshReads]
  simp

/-- **The renamed skeleton denotes the same term.**  The hypothesis is that the
two environments agree through the renaming, channel for channel — which is what
a caller establishes when it builds the fan-out delivering each original's value
to its renamed channel. -/
theorem fill_freshReads (fresh : ℕ → Comb) :
    ∀ (sk : Skeleton) (next : ℕ) (env renamed : Comb → Comb),
      List.Forall₂ (fun renamedChannel original => renamed renamedChannel = env original)
        (freshReads fresh sk next).1.readChannels sk.readChannels →
      (freshReads fresh sk next).1.fill renamed = sk.fill env
  | .read channel, next, env, renamed, hagree => by
      simp only [freshReads, Skeleton.readChannels] at hagree
      rcases hagree with _ | ⟨hhead, -⟩
      simpa only [freshReads, Skeleton.fill] using hhead
  | .const _, _, _, _, _ => rfl
  | .nodePar left right, next, env, renamed, hagree
  | .nodeMsg left right, next, env, renamed, hagree => by
      have hlen := length_readChannels_freshReads fresh left next
      simp only [freshReads, Skeleton.readChannels] at hagree
      have htake := List.forall₂_take_append _ _ _ hagree
      have hdrop := List.forall₂_drop_append _ _ _ hagree
      rw [List.take_left' hlen] at htake
      rw [List.drop_left' hlen] at hdrop
      simp only [freshReads, Skeleton.fill,
        fill_freshReads fresh left next env renamed htake,
        fill_freshReads fresh right (freshReads fresh left next).2 env renamed hdrop]

/-- **Renaming gives a linear soup that denotes the same term.**  The two halves
together: the reads are distinct by construction, so the compiled soup is
linear, and it denotes what the original did. -/
theorem freshReads_verified (s : Comb) (fresh : ℕ → Comb)
    (hfresh : Function.Injective fresh) (sk : Skeleton) (next : ℕ)
    (outName : Comb) (env renamed : Comb → Comb)
    (havoid : ∀ index slotIndex : ℕ, fresh index ≠ slot s slotIndex)
    (hagree : List.Forall₂
      (fun renamedChannel original => renamed renamedChannel = env original)
      (freshReads fresh sk next).1.readChannels sk.readChannels) :
    (freshReads fresh sk next).1.fill renamed = sk.fill env
      ∧ atomCount (compileSkeleton s (freshReads fresh sk next).1 outName 0)
          = sk.cost
      ∧ Linear (compileSkeleton s (freshReads fresh sk next).1 outName 0) :=
  ⟨fill_freshReads fresh sk next env renamed hagree,
    freshReads_cost_unchanged s fresh sk next outName,
    freshReads_compiles_linear s fresh hfresh sk next outName havoid⟩

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
