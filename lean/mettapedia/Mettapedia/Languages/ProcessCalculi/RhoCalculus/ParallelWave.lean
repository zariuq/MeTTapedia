import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MultiStep

/-!
# Parallel Wave: Serializability for Disjoint COMMs in the ρ-Calculus

This file proves a *restricted diamond* (serializability) result for the
ρ-calculus reduction relation `Reduces` (`⇝`) and its multi-step closure
`ReducesStar` (`⇝*`).

## Scope and honesty

These are statements about the **reduction relation** — i.e. about the
*strategy* "fire pairwise-disjoint COMMs in parallel". They are **not** a
verification of any C / OS-threaded executor; they are the mathematical
soundness obligation that such an executor must meet: whatever order the
scheduler chooses for non-interfering COMMs, the result is the same up to
structural congruence and is reachable by ordinary single ρ-steps.

## Main results

* `disjointComm_diamond` (Stage A) — the restricted diamond for two
  non-interfering COMMs on *disjoint top-level components* of a parallel bag.
  Firing them in either order reaches the same residual up to `≡`, and that
  residual is reachable in exactly two single `Reduces` steps (a 2-step `⇝*`).

* `parallelWave_reducesStar` (Stage B) — a "parallel wave" is a list of
  pairwise-disjoint COMM claims over a bag; firing the whole wave is sound:
  `parallelWave p q → p ⇝* q`.

## Design

The COMM base constructor `Reduces.comm` only fires when the *head two*
components of the bag are a matching output/input pair on a common channel.
We lift it to fire on an arbitrary matching pair via structural congruence
(`Reduces.equiv` + `par_perm`); see `comm_anywhere`. Disjointness is then
exactly the statement that the two COMMs consume four *distinct* list
positions, so neither disables the other.

## References

- Meredith & Radestock (2005), "A Reflective Higher-Order Calculus" (COMM).
- Meredith & Stay, "Operational Semantics in Logical Form".
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-! ## A COMM redex as data

To talk about "a COMM" abstractly we package the four ingredients of a single
communication: the channel `n`, the sent process `q`, and the input
continuation `p` (a one-binder lambda body). The two top-level components it
consumes are `outComp` and `inComp`; the single residual it produces is
`residual`.
-/

/-- The output component consumed by a COMM on channel `n` sending `q`. -/
def commOut (n q : Pattern) : Pattern := .apply "POutput" [n, q]

/-- The input component consumed by a COMM on channel `n` with body `p`. -/
def commIn (n p : Pattern) : Pattern := .apply "PInput" [n, .lambda none p]

/-- The single residual produced by a COMM on channel `n` (body `p`, sent `q`). -/
def commRes (p q : Pattern) : Pattern := semanticCommSubst p q

/-- Bag former for parallel composition (a `hashBag` collection with no guard). -/
def bag (elems : List Pattern) : Pattern := .collection .hashBag elems none

@[simp] theorem bag_def (elems : List Pattern) :
    bag elems = .collection .hashBag elems none := rfl

/-! ## Firing a single COMM

The COMM base constructor `Reduces.comm` only fires on the head two components.
We package it twice: once at the head (`comm_at_head`), and once at an arbitrary
position reachable by permutation (`comm_anywhere`). The latter is the workhorse
for serializing two disjoint COMMs.
-/

/-- COMM fires on the head two components of a bag.

    `Reduces` is `Type`-valued (carries the derivation), so this is a `def`. -/
def comm_at_head (n q p : Pattern) (rest : List Pattern) :
    Reduces (bag (commOut n q :: commIn n p :: rest))
            (bag (commRes p q :: rest)) := by
  have h := @Reduces.comm n q p rest
  simpa [bag, commOut, commIn, commRes] using h

/-- COMM fires on *any* bag structurally congruent to one whose head two
    components are a matching output/input pair on channel `n`. The residual is
    the substituted continuation in parallel with the (permuted) `rest`. -/
def comm_anywhere {bagP : Pattern} {n q p : Pattern} {rest : List Pattern}
    (hsc : StructuralCongruence bagP (bag (commOut n q :: commIn n p :: rest))) :
    Reduces bagP (bag (commRes p q :: rest)) :=
  Reduces.equiv hsc (comm_at_head n q p rest) (StructuralCongruence.refl _)

/-! ## Bag reassembly via permutation

Parallel composition is commutative–associative, so any permutation of bag
components is a structural congruence. This is the only AC fact the diamond
needs, and it follows directly from the `par_perm` constructor. -/

/-- Any permutation of bag components is a structural congruence. -/
theorem bag_perm {xs ys : List Pattern} (h : xs.Perm ys) :
    StructuralCongruence (bag xs) (bag ys) :=
  StructuralCongruence.par_perm xs ys h

/-! ## Stage A — the restricted diamond for two disjoint COMMs

Setup. Consider a parallel bag whose top-level components include two
*disjoint* COMM redexes:

* COMM₁ on channel `n₁` consuming `o₁ = commOut n₁ q₁` and `i₁ = commIn n₁ p₁`,
  producing `r₁ = commRes p₁ q₁`;
* COMM₂ on channel `n₂` consuming `o₂ = commOut n₂ q₂` and `i₂ = commIn n₂ p₂`,
  producing `r₂ = commRes p₂ q₂`.

"Disjoint" means the two redexes consume *four distinct top-level positions* of
the bag — there is no shared component. We make this concrete by taking the
canonical bag

  `bag (o₁ :: i₁ :: o₂ :: i₂ :: rest)`,

in which the four endpoints sit at four different list positions. (Any actual
bag with two non-interfering redexes is `≡` to this canonical form by
`par_perm`; the diamond transports along that congruence via `Reduces.equiv`.)

We show both firing orders reach the same residual up to `≡`, each in exactly
two single `Reduces` steps.
-/

/-- The canonical bag holding the two disjoint redexes (and the rest):
    `o₁ :: i₁ :: o₂ :: i₂ :: rest`, with the four endpoints at four distinct
    top-level positions. -/
def srcBag (n₁ q₁ p₁ n₂ q₂ p₂ : Pattern) (rest : List Pattern) : Pattern :=
  bag (commOut n₁ q₁ :: commIn n₁ p₁ :: commOut n₂ q₂ :: commIn n₂ p₂ :: rest)

/-- The residual of firing COMM₁ then COMM₂ (order 1): `r₂ :: r₁ :: rest`. -/
def res1 (q₁ p₁ q₂ p₂ : Pattern) (rest : List Pattern) : Pattern :=
  bag (commRes p₂ q₂ :: commRes p₁ q₁ :: rest)

/-- The residual of firing COMM₂ then COMM₁ (order 2): `r₁ :: r₂ :: rest`. -/
def res2 (q₁ p₁ q₂ p₂ : Pattern) (rest : List Pattern) : Pattern :=
  bag (commRes p₁ q₁ :: commRes p₂ q₂ :: rest)

/-- Order 1, step 1: fire COMM₁ at the head. -/
private def order1_step1 (n₁ q₁ p₁ n₂ q₂ p₂ : Pattern) (rest : List Pattern) :
    Reduces (srcBag n₁ q₁ p₁ n₂ q₂ p₂ rest)
            (bag (commRes p₁ q₁ :: commOut n₂ q₂ :: commIn n₂ p₂ :: rest)) := by
  have h := @Reduces.comm n₁ q₁ p₁ (commOut n₂ q₂ :: commIn n₂ p₂ :: rest)
  simpa [srcBag, bag, commOut, commIn, commRes] using h

/-- Order 1, step 2: fire COMM₂ on the now-shifted redex (positions 1,2),
    reached by permuting it to the head. Residual: `r₂ :: r₁ :: rest`. -/
private def order1_step2 (_n₁ q₁ p₁ n₂ q₂ p₂ : Pattern) (rest : List Pattern) :
    Reduces (bag (commRes p₁ q₁ :: commOut n₂ q₂ :: commIn n₂ p₂ :: rest))
            (bag (commRes p₂ q₂ :: commRes p₁ q₁ :: rest)) := by
  -- Move `o₂, i₂` to the front so COMM fires; rest' = r₁ :: rest.
  -- r₁ :: ([o₂, i₂] ++ rest)  ~  [o₂, i₂] ++ (r₁ :: rest)
  have hperm : (commRes p₁ q₁ :: commOut n₂ q₂ :: commIn n₂ p₂ :: rest).Perm
               (commOut n₂ q₂ :: commIn n₂ p₂ :: commRes p₁ q₁ :: rest) :=
    (List.perm_middle (a := commRes p₁ q₁) (l₁ := [commOut n₂ q₂, commIn n₂ p₂])
      (l₂ := rest)).symm
  exact comm_anywhere (n := n₂) (q := q₂) (p := p₂)
      (rest := commRes p₁ q₁ :: rest) (bag_perm hperm)

/-- Order 2, step 1: fire COMM₂ first, by permuting `o₂, i₂` to the head.
    Residual: `r₂ :: o₁ :: i₁ :: rest`. -/
private def order2_step1 (n₁ q₁ p₁ n₂ q₂ p₂ : Pattern) (rest : List Pattern) :
    Reduces (srcBag n₁ q₁ p₁ n₂ q₂ p₂ rest)
            (bag (commRes p₂ q₂ :: commOut n₁ q₁ :: commIn n₁ p₁ :: rest)) := by
  -- o₁ :: i₁ :: o₂ :: i₂ :: rest  ~  o₂ :: i₂ :: o₁ :: i₁ :: rest
  have hperm : (commOut n₁ q₁ :: commIn n₁ p₁ :: commOut n₂ q₂ :: commIn n₂ p₂ :: rest).Perm
               (commOut n₂ q₂ :: commIn n₂ p₂ :: commOut n₁ q₁ :: commIn n₁ p₁ :: rest) := by
    have h := (List.perm_append_comm
      (l₁ := [commOut n₁ q₁, commIn n₁ p₁])
      (l₂ := [commOut n₂ q₂, commIn n₂ p₂])).append_right rest
    simpa [List.append_assoc] using h
  exact comm_anywhere (n := n₂) (q := q₂) (p := p₂)
      (rest := commOut n₁ q₁ :: commIn n₁ p₁ :: rest)
      (by simpa [srcBag, bag] using bag_perm hperm)

/-- Order 2, step 2: fire COMM₁ on the shifted redex (positions 1,2),
    by permuting it to the head. Residual: `r₁ :: r₂ :: rest`. -/
private def order2_step2 (n₁ q₁ p₁ _n₂ q₂ p₂ : Pattern) (rest : List Pattern) :
    Reduces (bag (commRes p₂ q₂ :: commOut n₁ q₁ :: commIn n₁ p₁ :: rest))
            (bag (commRes p₁ q₁ :: commRes p₂ q₂ :: rest)) := by
  -- r₂ :: ([o₁, i₁] ++ rest)  ~  [o₁, i₁] ++ (r₂ :: rest)
  have hperm : (commRes p₂ q₂ :: commOut n₁ q₁ :: commIn n₁ p₁ :: rest).Perm
               (commOut n₁ q₁ :: commIn n₁ p₁ :: commRes p₂ q₂ :: rest) :=
    (List.perm_middle (a := commRes p₂ q₂) (l₁ := [commOut n₁ q₁, commIn n₁ p₁])
      (l₂ := rest)).symm
  exact comm_anywhere (n := n₁) (q := q₁) (p := p₁)
      (rest := commRes p₂ q₂ :: rest) (bag_perm hperm)

/-! ### The diamond

We bundle the four single steps into one structure. `order1` (COMM₁ then COMM₂)
lands on `r₂ :: r₁ :: rest`; `order2` (COMM₂ then COMM₁) lands on
`r₁ :: r₂ :: rest`. The two residuals are equal up to `≡` (swap of the two
heads). Each order is a 2-step reduction sequence.

The structure carries `Type`-valued reduction data and the `Prop`-valued `≡`
witness together (a plain `×` cannot mix `Type` and `Prop`). -/

/-- Bundled conclusion of the restricted diamond for two disjoint COMMs.

    `order1`/`order2` are the two serializations as **exactly two** single
    `Reduces` steps; `joined` records that the two residuals are equal up to
    structural congruence. -/
structure DisjointCommDiamond (n₁ q₁ p₁ n₂ q₂ p₂ : Pattern) (rest : List Pattern) where
  /-- Order 1 (COMM₁ then COMM₂) as exactly two single steps. -/
  order1 : ReducesN 2 (srcBag n₁ q₁ p₁ n₂ q₂ p₂ rest) (res1 q₁ p₁ q₂ p₂ rest)
  /-- Order 2 (COMM₂ then COMM₁) as exactly two single steps. -/
  order2 : ReducesN 2 (srcBag n₁ q₁ p₁ n₂ q₂ p₂ rest) (res2 q₁ p₁ q₂ p₂ rest)
  /-- The two residuals agree up to structural congruence. -/
  joined : StructuralCongruence (res1 q₁ p₁ q₂ p₂ rest) (res2 q₁ p₁ q₂ p₂ rest)

/-- **Stage A — restricted diamond for two disjoint COMMs.**

    From the canonical bag `o₁ :: i₁ :: o₂ :: i₂ :: rest` (four distinct
    top-level positions consumed by the two redexes), firing the COMMs in
    either order reaches residuals that are equal up to structural congruence
    `≡`, each reachable in **exactly two** single `Reduces` steps.

    This is genuine serializability: the two non-interfering communications
    commute, so a scheduler may fire them in parallel (either serialization)
    and obtain the same process up to `≡`. -/
def disjointComm_diamond (n₁ q₁ p₁ n₂ q₂ p₂ : Pattern) (rest : List Pattern) :
    DisjointCommDiamond n₁ q₁ p₁ n₂ q₂ p₂ rest where
  order1 :=
    ReducesN.succ (order1_step1 n₁ q₁ p₁ n₂ q₂ p₂ rest)
      (ReducesN.succ (order1_step2 n₁ q₁ p₁ n₂ q₂ p₂ rest) (ReducesN.zero _))
  order2 :=
    ReducesN.succ (order2_step1 n₁ q₁ p₁ n₂ q₂ p₂ rest)
      (ReducesN.succ (order2_step2 n₁ q₁ p₁ n₂ q₂ p₂ rest) (ReducesN.zero _))
  joined := by
    refine bag_perm ?_
    exact List.Perm.swap _ _ _

/-- `⇝*` corollary of Stage A: order 1 reaches `res1` in (at most two) steps. -/
noncomputable def disjointComm_order1_star (n₁ q₁ p₁ n₂ q₂ p₂ : Pattern) (rest : List Pattern) :
    ReducesStar (srcBag n₁ q₁ p₁ n₂ q₂ p₂ rest) (res1 q₁ p₁ q₂ p₂ rest) :=
  reducesN_to_star (disjointComm_diamond n₁ q₁ p₁ n₂ q₂ p₂ rest).order1

/-- `⇝*` corollary of Stage A: order 2 reaches `res2` in (at most two) steps. -/
noncomputable def disjointComm_order2_star (n₁ q₁ p₁ n₂ q₂ p₂ : Pattern) (rest : List Pattern) :
    ReducesStar (srcBag n₁ q₁ p₁ n₂ q₂ p₂ rest) (res2 q₁ p₁ q₂ p₂ rest) :=
  reducesN_to_star (disjointComm_diamond n₁ q₁ p₁ n₂ q₂ p₂ rest).order2

/-! ## Stage B — lifting to a parallel wave

A **parallel wave** is a list of pairwise-disjoint COMM claims over a bag. Each
claim is one communication, and disjointness means the claims consume disjoint
top-level components. We model the disjoint layout directly: each claim occupies
its own consecutive 2-component block (`out :: in`), and the blocks are laid out
side by side via `List.flatMap`, followed by an inert `rest`.

Firing the whole wave is sound: every claim fires (in claim order, each at the
head after the preceding residuals settle), and the result is the bag of all
residuals in parallel with `rest`. Because the blocks are disjoint, no claim
ever consumes a component another claim needs — this is exactly the "claims
don't disable each other" property, and it is what lets a scheduler fire the
whole wave.
-/

/-- A single COMM claim: communicate on channel `chan`, sending `sent`, with the
    one-binder input continuation `body`. It consumes the two top-level
    components `claimOut` and `claimIn`, producing the single residual
    `claimRes`. -/
structure CommClaim where
  /-- The channel both endpoints share. -/
  chan : Pattern
  /-- The process sent by the output endpoint. -/
  sent : Pattern
  /-- The input continuation (a one-binder lambda body). -/
  body : Pattern

namespace CommClaim

/-- The output component consumed by this claim. -/
def out (c : CommClaim) : Pattern := commOut c.chan c.sent

/-- The input component consumed by this claim. -/
def inp (c : CommClaim) : Pattern := commIn c.chan c.body

/-- The two-component block this claim occupies in the source bag. -/
def endpoints (c : CommClaim) : List Pattern := [c.out, c.inp]

/-- The single residual this claim produces. -/
def residual (c : CommClaim) : Pattern := commRes c.body c.sent

end CommClaim

/-- The flat source bag of a wave: each claim's two endpoints laid out as two
    consecutive top-level components (hence the four-or-more endpoints occupy
    pairwise-disjoint positions), followed by the inert `rest`. This is the
    natural "disjoint top-level components" picture. -/
def waveSource (claims : List CommClaim) (rest : List Pattern) : Pattern :=
  bag (claims.flatMap CommClaim.endpoints ++ rest)

/-- The target bag of a wave: all residuals in parallel with the inert `rest`. -/
def waveTarget (claims : List CommClaim) (rest : List Pattern) : Pattern :=
  bag (claims.map CommClaim.residual ++ rest)

/-! ### Reducing one component independently of the others

Each claim is laid out as its own *single* component `bag [out, in]` (a nested
two-element bag). That component reduces, on its own, to the claim's residual:

  `bag [c.out, c.inp]  ⇝  c.residual`.

This single-component reduction lifts to the whole wave bag at the claim's
position via `ReducesStar.par_any_pos` — the standard "reduce one parallel
component, leave the rest fixed" rule. Because each claim owns a distinct
position, reducing one never touches another: this is the disjointness that
makes the wave sound. No prepend-under-a-head lemma is needed. -/

/-- The single source component owned by a claim: its two endpoints bundled as
    one nested two-element bag. -/
def CommClaim.comp (c : CommClaim) : Pattern := bag [c.out, c.inp]

/-- A claim's own component reduces to its residual in one step. -/
private def claim_comp_step (c : CommClaim) :
    Reduces c.comp c.residual := by
  -- COMM on `bag [out, in]` (rest = []) gives `bag [residual]`, then drop the
  -- singleton bag via `par_singleton`.
  have hcomm := @Reduces.comm c.chan c.sent c.body []
  have hsingle : StructuralCongruence (bag [c.residual]) c.residual :=
    StructuralCongruence.par_singleton c.residual
  refine Reduces.equiv (StructuralCongruence.refl _) ?_ hsingle
  simpa [CommClaim.comp, CommClaim.out, CommClaim.inp, CommClaim.residual,
    bag, commOut, commIn, commRes] using hcomm

/-- A claim's component reduces to its residual at *any* position of a bag,
    leaving every other component untouched. -/
private noncomputable def claim_par_any (c : CommClaim) (before after : List Pattern) :
    ReducesStar (bag (before ++ [c.comp] ++ after))
                (bag (before ++ [c.residual] ++ after)) :=
  ReducesStar.par_any_pos (ReducesStar.single (claim_comp_step c))

/-- The source bag where each claim is one nested component (its two endpoints),
    in claim order, followed by the inert `rest`. -/
def waveSourceComp (claims : List CommClaim) (rest : List Pattern) : Pattern :=
  bag (claims.map CommClaim.comp ++ rest)

/-- Reduce a wave **with a fixed prefix `before` already settled**.

    This is the inductive heart of Stage B. We process claims left to right,
    accumulating the residuals of already-fired claims into the prefix `before`.
    At each step the head claim's *single* component is reduced **in place** by
    `claim_par_any` (it sits at position `before.length`, with everything else
    fixed), then the prefix grows by that residual and we recurse. No claim ever
    touches a component owned by another — disjointness made literal. -/
private noncomputable def waveFrom :
    (before : List Pattern) → (claims : List CommClaim) → (rest : List Pattern) →
    ReducesStar (bag (before ++ claims.map CommClaim.comp ++ rest))
                (bag (before ++ claims.map CommClaim.residual ++ rest))
  | before, [], rest => by
      simpa using ReducesStar.refl (bag (before ++ rest))
  | before, c :: cs, rest => by
      -- Reduce c's component at position `before.length`, others fixed.
      have head : ReducesStar
          (bag (before ++ [c.comp] ++ (cs.map CommClaim.comp ++ rest)))
          (bag (before ++ [c.residual] ++ (cs.map CommClaim.comp ++ rest))) :=
        claim_par_any c before (cs.map CommClaim.comp ++ rest)
      -- Recurse with the residual appended to the settled prefix.
      have tail : ReducesStar
          (bag ((before ++ [c.residual]) ++ cs.map CommClaim.comp ++ rest))
          (bag ((before ++ [c.residual]) ++ cs.map CommClaim.residual ++ rest)) :=
        waveFrom (before ++ [c.residual]) cs rest
      -- Realign list shapes and chain.
      have hhead : ReducesStar
          (bag (before ++ (c :: cs).map CommClaim.comp ++ rest))
          (bag ((before ++ [c.residual]) ++ cs.map CommClaim.comp ++ rest)) := by
        simpa [List.map_cons, List.cons_append, List.append_assoc] using head
      have htail : ReducesStar
          (bag ((before ++ [c.residual]) ++ cs.map CommClaim.comp ++ rest))
          (bag (before ++ (c :: cs).map CommClaim.residual ++ rest)) := by
        simpa [List.map_cons, List.cons_append, List.append_assoc] using tail
      exact ReducesStar.trans hhead htail

/-- **Stage B — a parallel wave serializes to a multi-step reduction.**

    For a list of pairwise-disjoint COMM claims laid out as disjoint
    single-component blocks over a bag, the whole wave is reachable by ordinary
    single ρ-steps:

      `waveSourceComp claims rest  ⇝*  waveTarget claims rest`.

    The proof reduces each claim's component independently and in place
    (`waveFrom` with empty settled prefix), so no component ever depends on
    another — this is exactly the disjointness of the wave. A scheduler may
    therefore fire all the claims (in any interleaving consistent with this
    layout) and reach the same multiset of residuals. -/
noncomputable def parallelWave_reducesStar (claims : List CommClaim) (rest : List Pattern) :
    ReducesStar (waveSourceComp claims rest) (waveTarget claims rest) := by
  have h := waveFrom [] claims rest
  simpa [waveSourceComp, waveTarget, List.nil_append] using h

/-! ### Bridging the two source layouts

The two-endpoint *flat* layout (`waveSource`, the natural "four distinct
top-level positions" picture) and the single-nested-component layout
(`waveSourceComp`, on which the wave is proved) are structurally congruent:
each nested block `bag [out, in]` flattens into its two consecutive components
by `par_flatten`. Hence the wave theorem transports to the flat source up to
`≡`, consistent with the diamond's "up to `≡`" discipline. -/

/-- Flatten one nested head block: `bag (bag L :: tail) ≡ bag (L ++ tail)`.

    `par_flatten` only flattens a nested bag at the *end* of a prefix, so we
    permute the block to the end, flatten there, and permute back. -/
private theorem bag_flatten_head (L tail : List Pattern) :
    StructuralCongruence (bag (bag L :: tail)) (bag (L ++ tail)) := by
  -- bag (bag L :: tail) ≡ bag (tail ++ [bag L])    (perm)
  have h1 : StructuralCongruence (bag (bag L :: tail)) (bag (tail ++ [bag L])) :=
    bag_perm (by simpa using (List.perm_append_comm (l₁ := [bag L]) (l₂ := tail)))
  -- bag (tail ++ [bag L]) ≡ bag (tail ++ L)         (flatten, ps = tail, qs = L)
  have h2 : StructuralCongruence (bag (tail ++ [bag L])) (bag (tail ++ L)) := by
    simpa [bag] using StructuralCongruence.par_flatten tail L
  -- bag (tail ++ L) ≡ bag (L ++ tail)               (perm)
  have h3 : StructuralCongruence (bag (tail ++ L)) (bag (L ++ tail)) :=
    bag_perm (List.perm_append_comm (l₁ := tail) (l₂ := L))
  exact StructuralCongruence.trans _ _ _ (StructuralCongruence.trans _ _ _ h1 h2) h3

/-- Element-wise congruence for bags: `bag (x :: xs) ≡ bag (y :: ys)` from a
    head equality `x ≡ y` and a tail congruence `bag xs ≡ bag ys`. -/
private theorem bag_cons_cong {x y : Pattern} {xs ys : List Pattern}
    (hx : StructuralCongruence x y)
    (hxs : StructuralCongruence (bag xs) (bag ys)) :
    StructuralCongruence (bag (x :: xs)) (bag (y :: ys)) := by
  -- bag (x :: xs) ≡ bag [x, bag xs]  ≡ bag [y, bag ys] ≡ bag (y :: ys)
  have hLx : StructuralCongruence (bag (x :: xs)) (bag [x, bag xs]) := by
    simpa [bag, List.singleton_append] using
      (StructuralCongruence.par_flatten [x] xs).symm
  have hRy : StructuralCongruence (bag [y, bag ys]) (bag (y :: ys)) := by
    simpa [bag, List.singleton_append] using StructuralCongruence.par_flatten [y] ys
  have hmid : StructuralCongruence (bag [x, bag xs]) (bag [y, bag ys]) := by
    refine StructuralCongruence.par_cong [x, bag xs] [y, bag ys] rfl ?_
    intro i h₁ h₂
    match i with
    | 0 => simpa using hx
    | 1 => simpa using hxs
  exact StructuralCongruence.trans _ _ _ (StructuralCongruence.trans _ _ _ hLx hmid) hRy

/-- The two source layouts are structurally congruent: the single-nested-block
    layout (`waveSourceComp`, on which the wave is proved) flattens block by
    block into the flat two-endpoint layout (`waveSource`). -/
theorem waveSource_sc_waveSourceComp (claims : List CommClaim) (rest : List Pattern) :
    StructuralCongruence (waveSourceComp claims rest) (waveSource claims rest) := by
  induction claims with
  | nil =>
    simp only [waveSourceComp, waveSource, List.map_nil, List.flatMap_nil, List.nil_append]
    exact StructuralCongruence.refl _
  | cons c cs ih =>
    -- waveSourceComp (c::cs) = bag (c.comp :: (cs.map comp ++ rest))
    -- waveSource     (c::cs) = bag (c.endpoints ++ (cs.flatMap endpoints ++ rest))
    have hsrcComp : waveSourceComp (c :: cs) rest
        = bag (CommClaim.comp c :: (cs.map CommClaim.comp ++ rest)) := by
      simp only [waveSourceComp, List.map_cons, List.cons_append]
    have hsrcFlat : waveSource (c :: cs) rest
        = bag ([c.out, c.inp] ++ (cs.flatMap CommClaim.endpoints ++ rest)) := by
      simp only [waveSource, List.flatMap_cons, CommClaim.endpoints, List.append_assoc]
    rw [hsrcComp, hsrcFlat]
    -- Flatten the head block, then bridge the tail by `ih`.
    -- bag (bag [out,in] :: T) ≡ bag ([out,in] ++ T)   (flatten head)
    have hflat : StructuralCongruence
        (bag (CommClaim.comp c :: (cs.map CommClaim.comp ++ rest)))
        (bag ([c.out, c.inp] ++ (cs.map CommClaim.comp ++ rest))) := by
      simpa [CommClaim.comp] using bag_flatten_head [c.out, c.inp]
        (cs.map CommClaim.comp ++ rest)
    -- bag ([out,in] ++ tailComp) ≡ bag ([out,in] ++ tailFlat)   (congr on tail via ih)
    have htail : StructuralCongruence
        (bag ([c.out, c.inp] ++ (cs.map CommClaim.comp ++ rest)))
        (bag ([c.out, c.inp] ++ (cs.flatMap CommClaim.endpoints ++ rest))) := by
      -- [out, in] ++ T = out :: in :: T, so use bag_cons_cong twice with refl heads.
      have ihbag : StructuralCongruence
          (bag (cs.map CommClaim.comp ++ rest))
          (bag (cs.flatMap CommClaim.endpoints ++ rest)) := ih
      have : StructuralCongruence
          (bag (c.out :: c.inp :: (cs.map CommClaim.comp ++ rest)))
          (bag (c.out :: c.inp :: (cs.flatMap CommClaim.endpoints ++ rest))) :=
        bag_cons_cong (StructuralCongruence.refl _)
          (bag_cons_cong (StructuralCongruence.refl _) ihbag)
      simpa using this
    exact StructuralCongruence.trans _ _ _ hflat htail

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
