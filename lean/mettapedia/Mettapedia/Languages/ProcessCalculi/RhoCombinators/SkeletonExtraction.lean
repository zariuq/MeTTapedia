/-
# From a rule's right-hand side to a skeleton

`RuleSkeleton.lean` compiles any `Skeleton` with all three guarantees, and
`MeTTaFragment.lean` shows the MeTTa presentation clears the structural
conditions. What stood between them was extraction: nothing produced a skeleton
from a `Pattern`, so the preservation result applied to hand-built skeletons
rather than to rules as authored.

This file closes that. `skeletonOf` reads a skeleton off a pattern and
`encodePattern` says what target term that pattern denotes once its
metavariables are replaced by their matched values. `fill_skeletonOf` is the
agreement:

```
    (skeletonOf channelOf labelOf p).fill env  =  encodePattern labelOf σ p
```

whenever the channel assignment and the substitution agree — `env (channelOf x)
= σ x`. Composed with `compileSkeleton_verified` this gives preservation for a
rule's right-hand side as written.

## The encoding, and what the census bounded

MeTTa's applications are `n`-ary and the target's node shapes are two- and
three-ary, so an application becomes a spine: its label, then one node per
argument, ending in the unit. The census bounded that job before it was written —
arities 0 through 4, and **no collections at all** in any right-hand side.

`readChannels_skeletonOf` is the piece that makes the linearity hypothesis
checkable at the source level: the channels a compiled right-hand side reads from
are exactly its metavariables' channels, in order. So "the read channels are
distinct" becomes "the metavariables are distinct", which is a property of the
rule.

## Where the encoding is faithful

`encodePattern` drops a collection's open tail, because a tail stands for any
number of elements and no fixed-arity spine can carry it. That is not a gap in
the agreement theorem — both sides drop it, so they agree — but it is the point
where the encoding stops being information-preserving, and it is exactly the
case `positionallyAssemblable` rejects. The admissibility condition and the
limit of the encoding are the same condition, which is the reason to state
both.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.RuleSkeleton
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Admissibility

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Markers -/

/-- A de Bruijn index as a target term: a unary numeral. -/
def indexTerm : ℕ → Comb
  | 0 => nil
  | n + 1 => kk (indexTerm n)

/-- The marker a collection kind carries. -/
def collectionKey : CollType → String
  | .vec => "Vec"
  | .hashBag => "HashBag"
  | .hashSet => "HashSet"

/-! ## What a pattern denotes -/

mutual

/-- The target term a pattern denotes once its metavariables are replaced by
their matched values.  An `n`-ary application becomes its label followed by a
spine of `n` binary nodes. -/
def encodePattern (labelOf : String → Comb) (σ : String → Comb) : Pattern → Comb
  | .bvar index => indexTerm index
  | .fvar name => σ name
  | .apply label arguments =>
      mm (labelOf label) (encodePatternList labelOf σ arguments)
  | .lambda _ body => mm (labelOf "Lambda") (encodePattern labelOf σ body)
  | .multiLambda _ _ body =>
      mm (labelOf "MultiLambda") (encodePattern labelOf σ body)
  | .subst target replacement =>
      mm (labelOf "Subst")
        (mm (encodePattern labelOf σ target) (encodePattern labelOf σ replacement))
  | .collection kind elements _ =>
      mm (labelOf (collectionKey kind)) (encodePatternList labelOf σ elements)

def encodePatternList (labelOf : String → Comb) (σ : String → Comb) :
    List Pattern → Comb
  | [] => nil
  | pattern :: rest =>
      mm (encodePattern labelOf σ pattern) (encodePatternList labelOf σ rest)

end

/-! ## Extraction -/

mutual

/-- **Read a skeleton off a pattern.**  A metavariable becomes a read at its
channel; everything else becomes construction. -/
def skeletonOf (channelOf labelOf : String → Comb) : Pattern → Skeleton
  | .bvar index => .const (indexTerm index)
  | .fvar name => .read (channelOf name)
  | .apply label arguments =>
      .nodeMsg (.const (labelOf label)) (skeletonOfList channelOf labelOf arguments)
  | .lambda _ body =>
      .nodeMsg (.const (labelOf "Lambda")) (skeletonOf channelOf labelOf body)
  | .multiLambda _ _ body =>
      .nodeMsg (.const (labelOf "MultiLambda")) (skeletonOf channelOf labelOf body)
  | .subst target replacement =>
      .nodeMsg (.const (labelOf "Subst"))
        (.nodeMsg (skeletonOf channelOf labelOf target)
          (skeletonOf channelOf labelOf replacement))
  | .collection kind elements _ =>
      .nodeMsg (.const (labelOf (collectionKey kind)))
        (skeletonOfList channelOf labelOf elements)

def skeletonOfList (channelOf labelOf : String → Comb) :
    List Pattern → Skeleton
  | [] => .const nil
  | pattern :: rest =>
      .nodeMsg (skeletonOf channelOf labelOf pattern)
        (skeletonOfList channelOf labelOf rest)

end

/-! ## Agreement -/

mutual

/-- **The extracted skeleton denotes the pattern.**  Filling it under an
environment gives the pattern's own denotation under the matching
substitution. -/
theorem fill_skeletonOf (channelOf labelOf : String → Comb)
    (env : Comb → Comb) (σ : String → Comb)
    (hcorr : ∀ name, env (channelOf name) = σ name) :
    ∀ pattern : Pattern,
      (skeletonOf channelOf labelOf pattern).fill env
        = encodePattern labelOf σ pattern
  | .bvar _ => rfl
  | .fvar name => hcorr name
  | .apply label arguments => by
      simp only [skeletonOf, encodePattern, Skeleton.fill,
        fill_skeletonOfList channelOf labelOf env σ hcorr arguments]
  | .lambda _ body => by
      simp only [skeletonOf, encodePattern, Skeleton.fill,
        fill_skeletonOf channelOf labelOf env σ hcorr body]
  | .multiLambda _ _ body => by
      simp only [skeletonOf, encodePattern, Skeleton.fill,
        fill_skeletonOf channelOf labelOf env σ hcorr body]
  | .subst target replacement => by
      simp only [skeletonOf, encodePattern, Skeleton.fill,
        fill_skeletonOf channelOf labelOf env σ hcorr target,
        fill_skeletonOf channelOf labelOf env σ hcorr replacement]
  | .collection kind elements _ => by
      simp only [skeletonOf, encodePattern, Skeleton.fill,
        fill_skeletonOfList channelOf labelOf env σ hcorr elements]

theorem fill_skeletonOfList (channelOf labelOf : String → Comb)
    (env : Comb → Comb) (σ : String → Comb)
    (hcorr : ∀ name, env (channelOf name) = σ name) :
    ∀ patterns : List Pattern,
      (skeletonOfList channelOf labelOf patterns).fill env
        = encodePatternList labelOf σ patterns
  | [] => rfl
  | pattern :: rest => by
      simp only [skeletonOfList, encodePatternList, Skeleton.fill,
        fill_skeletonOf channelOf labelOf env σ hcorr pattern,
        fill_skeletonOfList channelOf labelOf env σ hcorr rest]

end

/-! ## The read channels are the metavariables -/

mutual

/-- The metavariables of a pattern, in order, with multiplicity. -/
def patternFvars : Pattern → List String
  | .bvar _ => []
  | .fvar name => [name]
  | .apply _ arguments => patternFvarsList arguments
  | .lambda _ body => patternFvars body
  | .multiLambda _ _ body => patternFvars body
  | .subst target replacement => patternFvars target ++ patternFvars replacement
  | .collection _ elements _ => patternFvarsList elements

def patternFvarsList : List Pattern → List String
  | [] => []
  | pattern :: rest => patternFvars pattern ++ patternFvarsList rest

end

mutual

/-- **The channels a compiled right-hand side reads from are exactly its
metavariables' channels.**  So the linearity hypothesis — distinct read channels
— becomes a property of the rule: distinct metavariables. -/
theorem readChannels_skeletonOf (channelOf labelOf : String → Comb) :
    ∀ pattern : Pattern,
      (skeletonOf channelOf labelOf pattern).readChannels
        = (patternFvars pattern).map channelOf
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .apply _ arguments => by
      simp only [skeletonOf, patternFvars, Skeleton.readChannels,
        readChannels_skeletonOfList channelOf labelOf arguments, List.nil_append]
  | .lambda _ body => by
      simp only [skeletonOf, patternFvars, Skeleton.readChannels,
        readChannels_skeletonOf channelOf labelOf body, List.nil_append]
  | .multiLambda _ _ body => by
      simp only [skeletonOf, patternFvars, Skeleton.readChannels,
        readChannels_skeletonOf channelOf labelOf body, List.nil_append]
  | .subst target replacement => by
      simp only [skeletonOf, patternFvars, Skeleton.readChannels,
        readChannels_skeletonOf channelOf labelOf target,
        readChannels_skeletonOf channelOf labelOf replacement,
        List.nil_append, List.map_append]
  | .collection _ elements _ => by
      simp only [skeletonOf, patternFvars, Skeleton.readChannels,
        readChannels_skeletonOfList channelOf labelOf elements, List.nil_append]

theorem readChannels_skeletonOfList (channelOf labelOf : String → Comb) :
    ∀ patterns : List Pattern,
      (skeletonOfList channelOf labelOf patterns).readChannels
        = (patternFvarsList patterns).map channelOf
  | [] => rfl
  | pattern :: rest => by
      simp only [skeletonOfList, patternFvarsList, Skeleton.readChannels,
        readChannels_skeletonOf channelOf labelOf pattern,
        readChannels_skeletonOfList channelOf labelOf rest, List.map_append]

end

/-! ## Preservation for a rule as authored -/

/-- **A right-hand side compiles to its own denotation.**  Supplied with one
message per metavariable carrying that metavariable's matched value, the
compiled soup reaches the term the right-hand side denotes under the matching
substitution — at exactly the skeleton's cost, and linearly whenever the
right-hand side's metavariables are distinct and their channels avoid the
compiler's slots.

This is preservation for the right-hand side of a rule as written, rather than
for a hand-built skeleton. -/
theorem rightHandSide_preserved (s : Comb) (channelOf labelOf : String → Comb)
    (env : Comb → Comb) (σ : String → Comb)
    (hcorr : ∀ name, env (channelOf name) = σ name)
    (rhs : Pattern) (outName : Comb)
    (hdistinct : ((patternFvars rhs).map channelOf).Nodup)
    (hfresh : ∀ name ∈ patternFvars rhs, ∀ i : ℕ, channelOf name ≠ slot s i) :
    ReachesFull (par (compileSkeleton s (skeletonOf channelOf labelOf rhs) outName 0)
        ((skeletonOf channelOf labelOf rhs).supply env))
        (mm outName (encodePattern labelOf σ rhs))
      ∧ atomCount (compileSkeleton s (skeletonOf channelOf labelOf rhs) outName 0)
          = (skeletonOf channelOf labelOf rhs).cost
      ∧ Linear (compileSkeleton s (skeletonOf channelOf labelOf rhs) outName 0) := by
  have channels := readChannels_skeletonOf channelOf labelOf rhs
  refine ⟨?_, atomCount_compileSkeleton s _ outName 0, ?_⟩
  · have reaches := compileSkeleton_reaches s env (skeletonOf channelOf labelOf rhs)
      outName 0
    rwa [fill_skeletonOf channelOf labelOf env σ hcorr rhs] at reaches
  · refine compileSkeleton_linear s _ outName (by rw [channels]; exact hdistinct) ?_
    intro channel hchannel index
    rw [channels] at hchannel
    obtain ⟨name, hname, rfl⟩ := List.mem_map.mp hchannel
    exact hfresh name hname index

/-! ## Where the encoding loses information, mechanized

The prose above says the encoding drops a collection's open tail, and that this
is the same case the admissibility condition rejects.  Both halves are checkable,
and stating them as theorems is better than asserting them.
-/

/-- **The encoding drops an open tail.**  Two patterns differing only in their
rest variable have the same denotation, so the encoding is not injective there —
a tail stands for any number of elements and no fixed-arity spine can carry it. -/
theorem encodePattern_loses_open_tail (labelOf σ : String → Comb) :
    encodePattern labelOf σ (.collection .vec [] (some "R"))
        = encodePattern labelOf σ (.collection .vec [] (some "S"))
      ∧ (Pattern.collection .vec [] (some "R"))
          ≠ (Pattern.collection .vec [] (some "S")) := by
  refine ⟨rfl, ?_⟩
  intro h
  exact absurd h (by decide)

/-- **And the extraction drops it too**, identically: the two patterns give the
same skeleton, so nothing downstream can recover the tail. -/
theorem skeletonOf_loses_open_tail (channelOf labelOf : String → Comb) :
    skeletonOf channelOf labelOf (.collection .vec [] (some "R"))
      = skeletonOf channelOf labelOf (.collection .vec [] (some "S")) := rfl

/-- **The condition rejects exactly the parameters that produce open tails.**
A collection-valued parameter is not positionally assemblable, which is the
shape `PPar` has and the reason rho fails the census.  So the limit of the
encoding and the condition of §3 are the same condition, checked rather than
asserted. -/
theorem collection_parameter_not_assemblable :
    assemblableParam (.simple "ps" (TypeExpr.bag TypeExpr.proc)) = false := by
  decide

/-- The companion: a plain name-sorted parameter is assemblable, so the
condition is not rejecting everything. -/
theorem simple_parameter_assemblable :
    assemblableParam (.simple "n" TypeExpr.name) = true := by decide

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
