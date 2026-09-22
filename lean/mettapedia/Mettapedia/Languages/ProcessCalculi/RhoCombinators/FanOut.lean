/-
# Fanning one name out to all of its uses

Two places in this lane stop at the same boundary, and it is one boundary.

`translate`'s input clause delivers the received name to the body through a
single forwarder, so it is correct when the bound name is used **at most once**.
`skeletonOf` produces one read per metavariable occurrence, so a metavariable
used twice gives two reads at one channel — reachability survives, linearity
does not. Both are "one message, several consumers", and both are fixed the same
way: deliver the name to as many distinct channels as there are uses.

`distributor` and `distributor_broadcasts` already do the delivering. What was
missing is the chain: given a source and the list of channels the uses sit at,
build the duplicator chain that reaches all of them. `fanChain` builds it and
`deliveries_fanChain` proves it delivers exactly there.

```
    distributor source (fanChain fresh targets offset) ‖ mm source value
        ⟶*   broadcast value targets
```

## The cost

`length_fanChain` and `atomCount_distributor` give it exactly: `k` uses cost
`k - 1` atoms, one duplicator per branch of a chain with `k` leaves. Stated
without natural subtraction as `atoms + 1 = k`.

So the per-use charge is one, and it composes with the two laws already proved:
a skeleton's two atoms per leaf, and a placement's three per occurrence — that
last figure being exactly two for the leaf plus one for the duplicator edge,
which is where its constant came from.

## The input clause, generalized

`inp_releases_many` is `translate_inp_releases` with the single forwarder
replaced by a fan-out: the arriving name is split, the gate releases the body,
and the name reaches **every** proxy the body uses. That closes the affine
boundary for the input clause, which is the §2 side.

Threading the resulting list of proxies through `translate` itself — so that the
body is compiled against `k` proxy names rather than one — is the remaining
mechanical step, and the same pass serves the skeleton side.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Translation

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## The chain -/

/-- The duplicator chain delivering one name to each of several channels.  Each
link hands the remainder to a fresh intermediate; the last link hands it to the
final channel directly, so no intermediate is wasted. -/
def fanChain (fresh : ℕ → Comb) : List Comb → ℕ → List (Comb × Comb)
  | [], _ => []
  | [_], _ => []
  | [first, second], _ => [(first, second)]
  | first :: second :: third :: rest, offset =>
      (first, fresh offset) :: fanChain fresh (second :: third :: rest) (offset + 1)

/-- **The chain delivers exactly to the intended channels.**  The intermediates
never appear among the deliveries. -/
theorem deliveries_fanChain (fresh : ℕ → Comb) :
    ∀ (targets : List Comb) (source : Comb) (offset : ℕ),
      2 ≤ targets.length →
      deliveries source (fanChain fresh targets offset) = targets
  | [], _, _, h => by simp at h
  | [_], _, _, h => by simp at h
  | [first, second], source, _, _ => by
      simp only [fanChain, deliveries]
  | first :: second :: third :: rest, source, offset, _ => by
      have ih := deliveries_fanChain fresh (second :: third :: rest)
        (fresh offset) (offset + 1) (by simp)
      simp only [fanChain, deliveries, ih]

/-- A chain of `k-1` links delivers to `k` channels. -/
theorem length_fanChain (fresh : ℕ → Comb) :
    ∀ (targets : List Comb) (offset : ℕ), 1 ≤ targets.length →
      (fanChain fresh targets offset).length + 1 = targets.length
  | [], _, h => by simp at h
  | [_], _, _ => by simp [fanChain]
  | [_, _], _, _ => by simp [fanChain]
  | first :: second :: third :: rest, offset, _ => by
      have ih := length_fanChain fresh (second :: third :: rest) (offset + 1) (by simp)
      simp only [fanChain, List.length_cons] at ih ⊢
      omega

/-- A distributor is one atom per link. -/
theorem atomCount_distributor :
    ∀ (chain : List (Comb × Comb)) (source : Comb),
      atomCount (distributor source chain) = chain.length
  | [], _ => by simp [atomCount, distributor, componentList]
  | (target, next) :: rest, source => by
      have ih := atomCount_distributor rest next
      simp only [atomCount, distributor, componentList, List.length_append,
        List.length_cons, List.length_nil] at ih ⊢
      omega

/-- **One name reaches all of its uses, at one atom per use less one.** -/
theorem fanOut_broadcasts (fresh : ℕ → Comb) (payload source : Comb)
    (targets : List Comb) (offset : ℕ) (h : 2 ≤ targets.length) :
    Reaches (par (distributor source (fanChain fresh targets offset))
        (mm source payload)) (broadcast payload targets)
      ∧ atomCount (distributor source (fanChain fresh targets offset)) + 1
          = targets.length := by
  refine ⟨?_, ?_⟩
  · have reaches := distributor_broadcasts payload (fanChain fresh targets offset) source
    rwa [deliveries_fanChain fresh targets source offset h] at reaches
  · rw [atomCount_distributor]
    exact length_fanChain fresh targets offset (by omega)

/-! ## The input clause, with every use reached -/

/-- **The general input clause.**  The arriving name is split, the gate releases
the body, and the name reaches *every* proxy the body uses — not just one.  This
is `translate_inp_releases` with the single forwarder replaced by a fan-out, and
it closes the affine boundary for an input. -/
theorem inp_releases_many (fresh : ℕ → Comb)
    (subject trigger split store run body value : Comb)
    (proxies : List Comb) (offset : ℕ) (h : 2 ≤ proxies.length) :
    Reaches
      (par (par (dd subject trigger split)
        (par (gate trigger store run body)
          (distributor split (fanChain fresh proxies offset)))) (mm subject value))
      (par body (broadcast value proxies)) := by
  have ac : ∀ u v : Comb, components u = components v → Cong u v :=
    fun _ _ h => cong_of_components h
  -- split the arriving name to the gate's trigger and to the fan-out
  refine Reaches.trans (Reaches.congruent (ac _
    (par (par (dd subject trigger split) (mm subject value))
      (par (gate trigger store run body)
        (distributor split (fanChain fresh proxies offset))))
    (by simp only [components, gate]; ac_rfl))) ?_
  refine Reaches.trans (Reaches.parLeft _
    (Reaches.single (StepMinus.duplicate trigger split value (Cong.refl subject)))) ?_
  -- release the body
  refine Reaches.trans (Reaches.congruent (ac _
    (par (par (gate trigger store run body) (mm trigger value))
      (par (mm split value)
        (distributor split (fanChain fresh proxies offset))))
    (by simp only [components, gate]; ac_rfl))) ?_
  refine Reaches.trans (Reaches.parLeft _
    (gate_releases trigger store run body value)) ?_
  -- fan the received name out to every proxy
  refine Reaches.trans (Reaches.congruent (ac _
    (par (par (distributor split (fanChain fresh proxies offset)) (mm split value))
      body)
    (by simp only [components]; ac_rfl))) ?_
  refine Reaches.trans (Reaches.parLeft _
    ((fanOut_broadcasts fresh value split proxies offset h).1)) ?_
  exact Reaches.congruent (ac _ _ (by simp only [components]; ac_rfl))

/-- **The general input clause costs one atom per use.**  Four for the
mechanism — the duplicator, and the gate's three — plus one duplicator per extra
use of the bound name. -/
theorem atomCount_inp_many (fresh : ℕ → Comb)
    (subject trigger split store run body : Comb)
    (proxies : List Comb) (offset : ℕ) (h : 1 ≤ proxies.length) :
    atomCount (par (dd subject trigger split)
        (par (gate trigger store run body)
          (distributor split (fanChain fresh proxies offset)))) + 1
      = 4 + proxies.length := by
  have count := length_fanChain fresh proxies offset h
  have distributorCount := atomCount_distributor (fanChain fresh proxies offset) split
  simp only [atomCount, gate, componentList, List.length_append, List.length_cons,
    List.length_nil] at distributorCount ⊢
  omega

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
