/-
# Sufficiency: a presentation meeting the condition admits a target

`Admissibility.lean` states the condition a presentation must meet and checks it
against two real presentations — rho fails it at both levels, MeTTa clears it.
That is the **necessity** side: it says when a name-free target is impossible,
and why.

The other side was open for six turns: *a presentation satisfying the condition
admits a target.* The obstacle looked structural. The target has four code
constructors of arities two and three, and an arbitrary signature has shapes of
arbitrary arity, so there seemed to be nothing to construct for a general
signature.

The bridge turned out to already exist, in the MeTTa extraction. `skeletonOf`
encodes an `n`-ary application as a **spine**: the shape's name, then one binary
node per child. So the target's fixed, small constructor family realizes shapes
of any arity, and what was missing was not a construction but the observation
that the one already written is generic.

## What is proved

For **any** signature — any type of shapes with any declared arities — and any
term over it:

```
    fill_toSkeleton      the encoding is faithful
    leaves_toSkeleton    the compiled size is determined by the term
    leafCount_le         and is linear: leaves ≤ 2 · size
    signature_admits     reaches, exact cost, linear cost, and linear soup
```

`signature_admits_name_free_target` is the sufficiency statement. It hands back
what a target is supposed to provide: the compiled soup reaches the term the
signature term denotes, at exactly the skeleton's cost, with that cost linear in
the term, and linear in the non-interference sense whenever the supplied
channels are distinct and avoid the compiler's slots.

So the condition of §3 is now two-sided. A presentation whose shapes are
positionally assemblable admits the target this file builds; one whose shapes
are variadic or binding does not, which is what the rho census shows.

## What the arity is for

`Signature.arity` and `WellFormed` are not used by the encoding — a spine works
for a child list of any length. They are what connects this to the arity law:
for a well-formed term every node has exactly as many children as its shape
declares, so the compiled size is a function of the declared arities rather than
of anything discovered at compile time. `leafCount_node` is that dependence made
explicit.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.RuleSkeleton
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Admissibility

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Signatures and their terms -/

/-- A presentation's signature, as the condition of §3 reads it: shapes with
declared arities, each shape represented in the target by a name. -/
structure Signature where
  Shape : Type
  arity : Shape → ℕ
  shapeName : Shape → Comb

variable {Sig : Signature}

/-- A term over a signature: a value supplied at a channel, a statically known
subterm, or a shape applied to children. -/
inductive SigTerm (Sig : Signature) where
  | supplied : Comb → SigTerm Sig
  | fixed : Comb → SigTerm Sig
  | node : Sig.Shape → List (SigTerm Sig) → SigTerm Sig

namespace SigTerm

mutual

def size : SigTerm Sig → ℕ
  | supplied _ => 1
  | fixed _ => 1
  | node _ children => 1 + sizeList children

def sizeList : List (SigTerm Sig) → ℕ
  | [] => 0
  | child :: rest => size child + sizeList rest

end

mutual

/-- Every node has as many children as its shape declares. -/
def WellFormed : SigTerm Sig → Prop
  | supplied _ => True
  | fixed _ => True
  | node shape children =>
      children.length = Sig.arity shape ∧ WellFormedList children

def WellFormedList : List (SigTerm Sig) → Prop
  | [] => True
  | child :: rest => WellFormed child ∧ WellFormedList rest

end

mutual

/-- The compiled leaf count: two per node — its shape's name and the spine's
terminator — plus the children's. -/
def leafCount : SigTerm Sig → ℕ
  | supplied _ => 1
  | fixed _ => 1
  | node _ children => 2 + leafCountList children

def leafCountList : List (SigTerm Sig) → ℕ
  | [] => 0
  | child :: rest => leafCount child + leafCountList rest

end

mutual

/-- The target term a signature term denotes, under an environment for the
supplied values.  A shape applied to `n` children becomes its name followed by a
spine of `n` binary nodes. -/
def encode (env : Comb → Comb) : SigTerm Sig → Comb
  | supplied channel => env channel
  | fixed subterm => subterm
  | node shape children => mm (Sig.shapeName shape) (encodeList env children)

def encodeList (env : Comb → Comb) : List (SigTerm Sig) → Comb
  | [] => nil
  | child :: rest => mm (encode env child) (encodeList env rest)

end

mutual

/-- **The generic extraction.**  A supplied value becomes a read; everything else
becomes construction, with an `n`-ary shape becoming a spine. -/
def toSkeleton : SigTerm Sig → Skeleton
  | supplied channel => .read channel
  | fixed subterm => .const subterm
  | node shape children =>
      .nodeMsg (.const (Sig.shapeName shape)) (toSkeletonList children)

def toSkeletonList : List (SigTerm Sig) → Skeleton
  | [] => .const nil
  | child :: rest => .nodeMsg (toSkeleton child) (toSkeletonList rest)

end

mutual

/-- The channels a term's supplied values arrive at, in order. -/
def suppliedChannels : SigTerm Sig → List Comb
  | supplied channel => [channel]
  | fixed _ => []
  | node _ children => suppliedChannelsList children

def suppliedChannelsList : List (SigTerm Sig) → List Comb
  | [] => []
  | child :: rest => suppliedChannels child ++ suppliedChannelsList rest

end

end SigTerm

/-! ## The encoding is faithful -/

mutual

theorem fill_toSkeleton (env : Comb → Comb) :
    ∀ term : SigTerm Sig, (term.toSkeleton).fill env = term.encode env
  | .supplied _ => rfl
  | .fixed _ => rfl
  | .node shape children => by
      simp only [SigTerm.toSkeleton, SigTerm.encode, Skeleton.fill,
        fill_toSkeletonList env children]

theorem fill_toSkeletonList (env : Comb → Comb) :
    ∀ children : List (SigTerm Sig),
      (SigTerm.toSkeletonList children).fill env = SigTerm.encodeList env children
  | [] => rfl
  | child :: rest => by
      simp only [SigTerm.toSkeletonList, SigTerm.encodeList, Skeleton.fill,
        fill_toSkeleton env child, fill_toSkeletonList env rest]

end

/-! ## The compiled size -/

mutual

theorem leaves_toSkeleton :
    ∀ term : SigTerm Sig, (term.toSkeleton).leaves = term.leafCount
  | .supplied _ => rfl
  | .fixed _ => rfl
  | .node shape children => by
      simp only [SigTerm.toSkeleton, SigTerm.leafCount, Skeleton.leaves,
        leaves_toSkeletonList children]
      omega

theorem leaves_toSkeletonList :
    ∀ children : List (SigTerm Sig),
      (SigTerm.toSkeletonList children).leaves
        = 1 + SigTerm.leafCountList children
  | [] => rfl
  | child :: rest => by
      simp only [SigTerm.toSkeletonList, SigTerm.leafCountList, Skeleton.leaves,
        leaves_toSkeleton child, leaves_toSkeletonList rest]
      omega

end

mutual

/-- **The compiled size is linear in the term.**  Two leaves per node and one
per supplied or fixed value, so nothing multiplies. -/
theorem leafCount_le : ∀ term : SigTerm Sig, term.leafCount ≤ 2 * term.size
  | .supplied _ => by simp [SigTerm.leafCount, SigTerm.size]
  | .fixed _ => by simp [SigTerm.leafCount, SigTerm.size]
  | .node shape children => by
      have ih := leafCountList_le children
      simp only [SigTerm.leafCount, SigTerm.size] at ih ⊢
      omega

theorem leafCountList_le :
    ∀ children : List (SigTerm Sig),
      SigTerm.leafCountList children ≤ 2 * SigTerm.sizeList children
  | [] => by simp [SigTerm.leafCountList, SigTerm.sizeList]
  | child :: rest => by
      have ihc := leafCount_le child
      have ihr := leafCountList_le rest
      simp only [SigTerm.leafCountList, SigTerm.sizeList] at ihc ihr ⊢
      omega

end

/-- For a well-formed term the compiled size depends only on the declared
arities: a node contributes two leaves and exactly `arity` children. -/
theorem leafCount_node (shape : Sig.Shape) (children : List (SigTerm Sig))
    (hwf : (SigTerm.node shape children : SigTerm Sig).WellFormed) :
    (SigTerm.node shape children : SigTerm Sig).leafCount
        = 2 + SigTerm.leafCountList children
      ∧ children.length = Sig.arity shape :=
  ⟨rfl, hwf.1⟩

/-! ## The read channels are the supplied ones -/

mutual

theorem readChannels_toSkeleton :
    ∀ term : SigTerm Sig, (term.toSkeleton).readChannels = term.suppliedChannels
  | .supplied _ => rfl
  | .fixed _ => rfl
  | .node shape children => by
      simp only [SigTerm.toSkeleton, SigTerm.suppliedChannels,
        Skeleton.readChannels, readChannels_toSkeletonList children,
        List.nil_append]

theorem readChannels_toSkeletonList :
    ∀ children : List (SigTerm Sig),
      (SigTerm.toSkeletonList children).readChannels
        = SigTerm.suppliedChannelsList children
  | [] => rfl
  | child :: rest => by
      simp only [SigTerm.toSkeletonList, SigTerm.suppliedChannelsList,
        Skeleton.readChannels, readChannels_toSkeleton child,
        readChannels_toSkeletonList rest]

end

/-! ## Sufficiency -/

/-- **A presentation meeting the condition admits a name-free target.**  For any
signature and any term over it, the compiled soup reaches the term the signature
term denotes, at exactly the skeleton's cost, with that cost linear in the term,
and with no name having two possible partners whenever the supplied channels are
distinct and avoid the compiler's slots.

That is what a target is supposed to provide, and it is provided for an
arbitrary signature — shapes of any arity included, because an `n`-ary shape
compiles to a spine of binary nodes. -/
theorem signature_admits_name_free_target (Sig : Signature) (term : SigTerm Sig)
    (env : Comb → Comb) (s outName : Comb)
    (hdistinct : term.suppliedChannels.Nodup)
    (hfresh : ∀ channel ∈ term.suppliedChannels, ∀ i : ℕ, channel ≠ slot s i) :
    ReachesFull (par (compileSkeleton s term.toSkeleton outName 0)
        (term.toSkeleton.supply env))
        (mm outName (term.encode env))
      ∧ atomCount (compileSkeleton s term.toSkeleton outName 0)
          = term.toSkeleton.cost
      ∧ term.toSkeleton.cost + 1 = 2 * term.leafCount
      ∧ term.leafCount ≤ 2 * term.size
      ∧ Linear (compileSkeleton s term.toSkeleton outName 0) := by
  have channels := readChannels_toSkeleton term
  refine ⟨?_, atomCount_compileSkeleton s _ outName 0, ?_, leafCount_le term, ?_⟩
  · have reaches := compileSkeleton_reaches s env term.toSkeleton outName 0
    rwa [fill_toSkeleton env term] at reaches
  · rw [Skeleton.cost_eq_leaves, leaves_toSkeleton term]
  · refine compileSkeleton_linear s _ outName (by rw [channels]; exact hdistinct) ?_
    intro channel hchannel index
    rw [channels] at hchannel
    exact hfresh channel hchannel index

/-! ## The presentation's own signature

The condition of §3 is about a `LanguageDef`'s declared constructors, so the
signature sufficiency applies to is the one the presentation declares: one shape
per term constructor, with the arity that constructor declares and no other.
-/

/-- The signature a presentation declares. -/
def signatureOfPresentation (labelOf : String → Comb) : Signature where
  Shape := GrammarRule
  arity := fun rule => rule.params.length
  shapeName := fun rule => labelOf rule.label

/-- The arities are the declared ones — nothing is discovered at compile time. -/
theorem arity_signatureOfPresentation (labelOf : String → Comb) (rule : GrammarRule) :
    (signatureOfPresentation labelOf).arity rule = rule.params.length := rfl

/-- **The deliverable, sufficiency side.**  Over the signature a presentation
declares, every term compiles to a target that reaches the term's denotation, at
exactly the compiled cost, with that cost linear in the term, and with no name
having two possible partners.

Together with the necessity side — `rhoCalc_not_admits` and the census that says
why, and `defect` for the equation a target must not inherit — this is the
two-sided condition the lane set out to establish. What the condition does is
license the step *before* this theorem: a shape with a binding or variadic
parameter has no fixed arity and no name-valued children, so it cannot be a
`Signature.Shape` at all.  That is why the census failures are failures of
representability rather than of the construction below. -/
theorem presentation_admits_name_free_target (labelOf : String → Comb)
    (term : SigTerm (signatureOfPresentation labelOf))
    (env : Comb → Comb) (s outName : Comb)
    (hdistinct : term.suppliedChannels.Nodup)
    (hfresh : ∀ channel ∈ term.suppliedChannels, ∀ i : ℕ, channel ≠ slot s i) :
    ReachesFull (par (compileSkeleton s term.toSkeleton outName 0)
        (term.toSkeleton.supply env))
        (mm outName (term.encode env))
      ∧ atomCount (compileSkeleton s term.toSkeleton outName 0)
          = term.toSkeleton.cost
      ∧ term.toSkeleton.cost + 1 = 2 * term.leafCount
      ∧ term.leafCount ≤ 2 * term.size
      ∧ Linear (compileSkeleton s term.toSkeleton outName 0) :=
  signature_admits_name_free_target (signatureOfPresentation labelOf) term env s
    outName hdistinct hfresh

/-! ## Linking the construction to the condition's computed family

§3 asks three questions, and the condition answers them by computation:
`reflectedShapes` says which constructors must be reflected,
`codeConstructorFamily` says which node shapes require a code constructor and at
what arity, and `leafCount_le` says when the encoding is linear.

What was missing is that the construction actually *uses* that family. This
section closes the loop: the number of binary constructor applications a shape
compiles to is exactly the code-constructor arity the condition computes for it,
so the family is not a separate claim about the target but a measurement of it.
-/

/-- The internal nodes of a skeleton: the constructor applications it compiles
to. -/
def Skeleton.nodeCount : Skeleton → ℕ
  | .read _ => 0
  | .const _ => 0
  | .nodePar left right => left.nodeCount + right.nodeCount + 1
  | .nodeMsg left right => left.nodeCount + right.nodeCount + 1

/-- A skeleton's cost splits into its leaves and its constructor
applications. -/
theorem Skeleton.cost_eq_leaves_add_nodeCount :
    ∀ sk : Skeleton, sk.cost = sk.leaves + sk.nodeCount
  | .read _ => rfl
  | .const _ => rfl
  | .nodePar left right | .nodeMsg left right => by
      have ihl := Skeleton.cost_eq_leaves_add_nodeCount left
      have ihr := Skeleton.cost_eq_leaves_add_nodeCount right
      simp only [Skeleton.cost, Skeleton.leaves, Skeleton.nodeCount]
      omega

namespace SigTerm

mutual

/-- The constructor applications a signature term compiles to: one per child
plus one for the shape's own name. -/
def nodeCount : SigTerm Sig → ℕ
  | supplied _ => 0
  | fixed _ => 0
  | node _ children => nodeCountList children + 1

def nodeCountList : List (SigTerm Sig) → ℕ
  | [] => 0
  | child :: rest => child.nodeCount + nodeCountList rest + 1

end

/-- The list form, with the per-child charge made explicit. -/
theorem nodeCountList_eq :
    ∀ children : List (SigTerm Sig),
      nodeCountList children
        = (children.map SigTerm.nodeCount).sum + children.length
  | [] => rfl
  | child :: rest => by
      have ih := nodeCountList_eq rest
      simp only [nodeCountList, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      omega

end SigTerm

mutual

/-- The compiled constructor count is the one the term determines. -/
theorem nodeCount_toSkeleton :
    ∀ term : SigTerm Sig, (term.toSkeleton).nodeCount = term.nodeCount
  | .supplied _ => rfl
  | .fixed _ => rfl
  | .node shape children => by
      simp only [SigTerm.toSkeleton, SigTerm.nodeCount, Skeleton.nodeCount,
        nodeCount_toSkeletonList children]
      omega

theorem nodeCount_toSkeletonList :
    ∀ children : List (SigTerm Sig),
      (SigTerm.toSkeletonList children).nodeCount
        = SigTerm.nodeCountList children
  | [] => rfl
  | child :: rest => by
      simp only [SigTerm.toSkeletonList, SigTerm.nodeCountList, Skeleton.nodeCount,
        nodeCount_toSkeleton child, nodeCount_toSkeletonList rest]

end

/-- **A shape compiles to exactly the code-constructor arity the condition
computes for it.**  `codeConstructorArity` reads one name per parameter and
writes one; the compiled node uses one binary application per child plus one for
the shape's own name.  The two are the same number, so the family
`codeConstructorFamily` lists is a measurement of the target rather than a
separate claim about it. -/
theorem shape_compiles_to_codeConstructorArity (labelOf : String → Comb)
    (rule : GrammarRule)
    (children : List (SigTerm (signatureOfPresentation labelOf)))
    (hwf : children.length = rule.params.length) :
    (SigTerm.node rule children : SigTerm (signatureOfPresentation labelOf)).nodeCount
      = (children.map SigTerm.nodeCount).sum + codeConstructorArity rule := by
  simp only [SigTerm.nodeCount, SigTerm.nodeCountList_eq, codeConstructorArity, hwf]
  omega

/-- **And the declared arity is what determines it**, so the three questions §3
asks are answered by the same computation: which constructors are reflected,
which shapes need a code constructor and at what arity, and — by
`leafCount_le` — that the encoding is linear. -/
theorem arity_determines_compiled_shape (labelOf : String → Comb)
    (rule : GrammarRule)
    (children : List (SigTerm (signatureOfPresentation labelOf)))
    (hwf : children.length = rule.params.length) :
    (signatureOfPresentation labelOf).arity rule = rule.params.length
      ∧ codeConstructorArity rule = (signatureOfPresentation labelOf).arity rule + 1
      ∧ (SigTerm.node rule children :
            SigTerm (signatureOfPresentation labelOf)).nodeCount
          = (children.map SigTerm.nodeCount).sum + codeConstructorArity rule :=
  ⟨rfl, rfl, shape_compiles_to_codeConstructorArity labelOf rule children hwf⟩

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
