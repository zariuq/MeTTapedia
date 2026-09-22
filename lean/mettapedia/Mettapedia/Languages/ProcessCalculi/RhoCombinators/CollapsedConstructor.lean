/-
# The context-indexed constructor adds no power, and costs its arity

The draft records an alternative to the four-member constructor family: a single
atom indexed by a static one-hole context,

```
    cons[C](a,c) | mm(a,v)  →  mm(c, ⌜C[v]⌝)
```

and judges the conceptual cost of a context-indexed atom not worth paying. For
this tree the question is sharper, because the chapter-19 generator already
produces one-hole contexts from a presentation, so the collapsed form is closer
to machinery we own than the four-member family is.

This file settles the comparison in the direction that makes the collapsed form
safe to use as *notation*: **it adds no power.** `assemble` compiles a one-hole
context into a chain of ordinary constructors and `assemble_reaches` proves the
chain does exactly what the collapsed atom would do. A presentation may
therefore be described with context-indexed constructors, indexed by the
generated one-hole contexts, without committing the calculus to a rule set that
grows with the presentation.

## The arity law

`atomCount_assemble` is the size statement, and it is an equality:

```
    atoms (assemble C) = weight C + 1,      weight = Σ arity over the nodes of C
```

A node of arity `k` costs exactly `k` atoms — one constructor, which reads the
assembled child and the `k-1` statically known siblings, plus one message per
sibling. The hole costs one forwarder. Covering the binary shapes alone would
leave `2n + 1` looking like an accident of binarity; the context type below
covers **every** node shape the calculus has, binary and ternary, so the law is
visible as a law.

Read against the name-growth finding the pair is the point. The cost of
*building* a name is linear in the context that builds it; the name that gets
*built* can be exponentially larger than that context. Both are theorems here,
so the linear-cost claim and the exponential-name claim are not in tension —
they are about different objects, and conflating them is the error the cost
question was meant to prevent.

Wiring names are allocated from a slot counter: the node at offset `k` takes
slots `k`, `k+1`, `k+2` and hands `k+3` to its subtree, so distinctness of the
wiring is arithmetic and a caller may reserve a disjoint range for a sibling.

`assemble_linear` completes the picture: the compiled soup is linear in the
sense of `Inertness.Linear`, so no name in it has two possible partners. With
that and the size equality, `assemble` is a compiler with both a cost theorem
and a non-interference theorem.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.NameGrowth
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Inertness

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## One-hole contexts over name shapes -/

/-- A one-hole context over the node shapes a name can have: one constructor per
shape, one shape per position the hole can occupy. -/
inductive NameContext where
  | hole : NameContext
  | parLeft : NameContext → Comb → NameContext
  | parRight : Comb → NameContext → NameContext
  | msgLeft : NameContext → Comb → NameContext
  | msgRight : Comb → NameContext → NameContext
  | ddSubject : NameContext → Comb → Comb → NameContext
  | ddFirst : Comb → NameContext → Comb → NameContext
  | ddSecond : Comb → Comb → NameContext → NameContext
  | sySubject : NameContext → Comb → Comb → NameContext
  | syFirst : Comb → NameContext → Comb → NameContext
  | sySecond : Comb → Comb → NameContext → NameContext

namespace NameContext

/-- Filling the hole. -/
def fill : NameContext → Comb → Comb
  | hole, v => v
  | parLeft ctx right, v => par (ctx.fill v) right
  | parRight left ctx, v => par left (ctx.fill v)
  | msgLeft ctx payload, v => mm (ctx.fill v) payload
  | msgRight subject ctx, v => mm subject (ctx.fill v)
  | ddSubject ctx b c, v => dd (ctx.fill v) b c
  | ddFirst a ctx c, v => dd a (ctx.fill v) c
  | ddSecond a b ctx, v => dd a b (ctx.fill v)
  | sySubject ctx b c, v => sy (ctx.fill v) b c
  | syFirst a ctx c, v => sy a (ctx.fill v) c
  | sySecond a b ctx, v => sy a b (ctx.fill v)

/-- The sum of the arities of the nodes above the hole.  This, not the node
count, is what the compiled chain costs. -/
def weight : NameContext → ℕ
  | hole => 0
  | parLeft ctx _ => ctx.weight + 2
  | parRight _ ctx => ctx.weight + 2
  | msgLeft ctx _ => ctx.weight + 2
  | msgRight _ ctx => ctx.weight + 2
  | ddSubject ctx _ _ => ctx.weight + 3
  | ddFirst _ ctx _ => ctx.weight + 3
  | ddSecond _ _ ctx => ctx.weight + 3
  | sySubject ctx _ _ => ctx.weight + 3
  | syFirst _ ctx _ => ctx.weight + 3
  | sySecond _ _ ctx => ctx.weight + 3

/-- How many slots a compiled context reserves: three per node, so a caller can
hand a sibling a disjoint range by advancing this far. -/
def slotsUsed : NameContext → ℕ
  | hole => 0
  | parLeft ctx _ => ctx.slotsUsed + 3
  | parRight _ ctx => ctx.slotsUsed + 3
  | msgLeft ctx _ => ctx.slotsUsed + 3
  | msgRight _ ctx => ctx.slotsUsed + 3
  | ddSubject ctx _ _ => ctx.slotsUsed + 3
  | ddFirst _ ctx _ => ctx.slotsUsed + 3
  | ddSecond _ _ ctx => ctx.slotsUsed + 3
  | sySubject ctx _ _ => ctx.slotsUsed + 3
  | syFirst _ ctx _ => ctx.slotsUsed + 3
  | sySecond _ _ ctx => ctx.slotsUsed + 3

end NameContext

/-! ## Compiling a context into a constructor chain -/

/-- **The compiler.**  `assemble s ctx inName outName offset` is a soup that, given
a name arriving at `inName`, emits `ctx.fill` of it at `outName`.  Each node
contributes one constructor and one message per statically known sibling; the
hole contributes a forwarder. -/
def assemble (s : Comb) : NameContext → Comb → Comb → ℕ → Comb
  | .hole, inName, outName, _ => fw inName outName
  | .parLeft ctx right, inName, outName, offset =>
      par (assemble s ctx inName (slot s offset) (offset + 3))
        (par (mm (slot s (offset + 1)) right)
          (consPar (slot s offset) (slot s (offset + 1)) outName))
  | .parRight left ctx, inName, outName, offset =>
      par (assemble s ctx inName (slot s offset) (offset + 3))
        (par (mm (slot s (offset + 1)) left)
          (consPar (slot s (offset + 1)) (slot s offset) outName))
  | .msgLeft ctx payload, inName, outName, offset =>
      par (assemble s ctx inName (slot s offset) (offset + 3))
        (par (mm (slot s (offset + 1)) payload)
          (consMsg (slot s offset) (slot s (offset + 1)) outName))
  | .msgRight subject ctx, inName, outName, offset =>
      par (assemble s ctx inName (slot s offset) (offset + 3))
        (par (mm (slot s (offset + 1)) subject)
          (consMsg (slot s (offset + 1)) (slot s offset) outName))
  | .ddSubject ctx b c, inName, outName, offset =>
      par (assemble s ctx inName (slot s offset) (offset + 3))
        (par (mm (slot s (offset + 1)) b)
          (par (mm (slot s (offset + 2)) c)
            (consDup (slot s offset) (slot s (offset + 1))
              (slot s (offset + 2)) outName)))
  | .ddFirst a ctx c, inName, outName, offset =>
      par (assemble s ctx inName (slot s offset) (offset + 3))
        (par (mm (slot s (offset + 1)) a)
          (par (mm (slot s (offset + 2)) c)
            (consDup (slot s (offset + 1)) (slot s offset)
              (slot s (offset + 2)) outName)))
  | .ddSecond a b ctx, inName, outName, offset =>
      par (assemble s ctx inName (slot s offset) (offset + 3))
        (par (mm (slot s (offset + 1)) a)
          (par (mm (slot s (offset + 2)) b)
            (consDup (slot s (offset + 1)) (slot s (offset + 2))
              (slot s offset) outName)))
  | .sySubject ctx b c, inName, outName, offset =>
      par (assemble s ctx inName (slot s offset) (offset + 3))
        (par (mm (slot s (offset + 1)) b)
          (par (mm (slot s (offset + 2)) c)
            (consSyn (slot s offset) (slot s (offset + 1))
              (slot s (offset + 2)) outName)))
  | .syFirst a ctx c, inName, outName, offset =>
      par (assemble s ctx inName (slot s offset) (offset + 3))
        (par (mm (slot s (offset + 1)) a)
          (par (mm (slot s (offset + 2)) c)
            (consSyn (slot s (offset + 1)) (slot s offset)
              (slot s (offset + 2)) outName)))
  | .sySecond a b ctx, inName, outName, offset =>
      par (assemble s ctx inName (slot s offset) (offset + 3))
        (par (mm (slot s (offset + 1)) a)
          (par (mm (slot s (offset + 2)) b)
            (consSyn (slot s (offset + 1)) (slot s (offset + 2))
              (slot s offset) outName)))

/-! ## The traces -/

/-- **A binary node.**  A sub-assembly emitting at `mid`, one statically known
sibling, and a constructor reading both. -/
theorem node_reaches {sub inName payload mid w s1 v1 atom result : Comb}
    (ih : ReachesFull (par sub (mm inName payload)) (mm mid w))
    (fire : ReachesFull (par atom (par (mm mid w) (mm s1 v1))) result) :
    ReachesFull (par (par sub (par (mm s1 v1) atom)) (mm inName payload)) result := by
  refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
      components (par (par sub (par (mm s1 v1) atom)) (mm inName payload))
        = components (par (par sub (mm inName payload)) (par (mm s1 v1) atom))
      from by simp only [components]; ac_rfl))) ?_
  refine ReachesFull.trans (ReachesFull.parLeft _ ih) ?_
  refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
      components (par (mm mid w) (par (mm s1 v1) atom))
        = components (par atom (par (mm mid w) (mm s1 v1)))
      from by simp only [components]; ac_rfl))) ?_
  exact fire

/-- **A ternary node.**  The same, with two statically known siblings. -/
theorem node_reaches3 {sub inName payload mid w s1 v1 s2 v2 atom result : Comb}
    (ih : ReachesFull (par sub (mm inName payload)) (mm mid w))
    (fire : ReachesFull (par atom (par (mm mid w) (par (mm s1 v1) (mm s2 v2)))) result) :
    ReachesFull (par (par sub (par (mm s1 v1) (par (mm s2 v2) atom)))
      (mm inName payload)) result := by
  refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
      components (par (par sub (par (mm s1 v1) (par (mm s2 v2) atom)))
          (mm inName payload))
        = components (par (par sub (mm inName payload))
          (par (mm s1 v1) (par (mm s2 v2) atom)))
      from by simp only [components]; ac_rfl))) ?_
  refine ReachesFull.trans (ReachesFull.parLeft _ ih) ?_
  refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
      components (par (mm mid w) (par (mm s1 v1) (par (mm s2 v2) atom)))
        = components (par atom (par (mm mid w) (par (mm s1 v1) (mm s2 v2))))
      from by simp only [components]; ac_rfl))) ?_
  exact fire

/-- The constructor reads its children in its own argument order; when the hole
is not the first child the message block is permuted first. -/
theorem fire_after_reorder {atom block block' result : Comb}
    (h : components block = components block')
    (fire : ReachesFull (par atom block') result) :
    ReachesFull (par atom block) result :=
  ReachesFull.trans
    (ReachesFull.congruent (cong_of_components (by simp only [components, h])))
    fire

/-- **The compiled chain does what the collapsed atom would do.**  So the
context-indexed constructor is a notation for a constructor chain, not an
extension of the calculus. -/
theorem assemble_reaches (s : Comb) : ∀ (ctx : NameContext) (inName outName : Comb)
    (offset : ℕ) (v : Comb),
    ReachesFull (par (assemble s ctx inName outName offset) (mm inName v))
      (mm outName (ctx.fill v))
  | .hole, inName, outName, _, v =>
      ReachesFull.ofReaches (Reaches.single (StepMinus.forward outName v (Cong.refl inName)))
  | .parLeft ctx right, inName, outName, offset, v =>
      node_reaches (assemble_reaches s ctx inName (slot s offset)
          (offset + 3) v)
        (ReachesFull.single (Step.buildPar outName (ctx.fill v) right
          (Cong.refl _) (Cong.refl _)))
  | .msgLeft ctx payload, inName, outName, offset, v =>
      node_reaches (assemble_reaches s ctx inName (slot s offset)
          (offset + 3) v)
        (ReachesFull.single (Step.buildMsg outName (ctx.fill v) payload
          (Cong.refl _) (Cong.refl _)))
  | .parRight left ctx, inName, outName, offset, v =>
      node_reaches (assemble_reaches s ctx inName (slot s offset)
          (offset + 3) v)
        (fire_after_reorder (by simp only [components]; ac_rfl)
          (ReachesFull.single (Step.buildPar outName left (ctx.fill v)
            (Cong.refl _) (Cong.refl _))))
  | .msgRight subject ctx, inName, outName, offset, v =>
      node_reaches (assemble_reaches s ctx inName (slot s offset)
          (offset + 3) v)
        (fire_after_reorder (by simp only [components]; ac_rfl)
          (ReachesFull.single (Step.buildMsg outName subject (ctx.fill v)
            (Cong.refl _) (Cong.refl _))))
  | .ddSubject ctx b c, inName, outName, offset, v =>
      node_reaches3 (assemble_reaches s ctx inName (slot s offset)
          (offset + 3) v)
        (ReachesFull.single (Step.buildDup outName (ctx.fill v) b c
          (Cong.refl _) (Cong.refl _) (Cong.refl _)))
  | .sySubject ctx b c, inName, outName, offset, v =>
      node_reaches3 (assemble_reaches s ctx inName (slot s offset)
          (offset + 3) v)
        (ReachesFull.single (Step.buildSyn outName (ctx.fill v) b c
          (Cong.refl _) (Cong.refl _) (Cong.refl _)))
  | .ddFirst a ctx c, inName, outName, offset, v =>
      node_reaches3 (assemble_reaches s ctx inName (slot s offset)
          (offset + 3) v)
        (fire_after_reorder (by simp only [components]; ac_rfl)
          (ReachesFull.single (Step.buildDup outName a (ctx.fill v) c
            (Cong.refl _) (Cong.refl _) (Cong.refl _))))
  | .ddSecond a b ctx, inName, outName, offset, v =>
      node_reaches3 (assemble_reaches s ctx inName (slot s offset)
          (offset + 3) v)
        (fire_after_reorder (by simp only [components]; ac_rfl)
          (ReachesFull.single (Step.buildDup outName a b (ctx.fill v)
            (Cong.refl _) (Cong.refl _) (Cong.refl _))))
  | .syFirst a ctx c, inName, outName, offset, v =>
      node_reaches3 (assemble_reaches s ctx inName (slot s offset)
          (offset + 3) v)
        (fire_after_reorder (by simp only [components]; ac_rfl)
          (ReachesFull.single (Step.buildSyn outName a (ctx.fill v) c
            (Cong.refl _) (Cong.refl _) (Cong.refl _))))
  | .sySecond a b ctx, inName, outName, offset, v =>
      node_reaches3 (assemble_reaches s ctx inName (slot s offset)
          (offset + 3) v)
        (fire_after_reorder (by simp only [components]; ac_rfl)
          (ReachesFull.single (Step.buildSyn outName a b (ctx.fill v)
            (Cong.refl _) (Cong.refl _) (Cong.refl _))))

/-! ## The arity law -/

/-- **A node of arity `k` costs exactly `k` atoms.**  An equality, not a bound,
so it is also a lower bound on this compiler's output. -/
theorem atomCount_assemble (s : Comb) : ∀ (ctx : NameContext) (inName outName : Comb)
    (offset : ℕ),
    atomCount (assemble s ctx inName outName offset) = ctx.weight + 1
  | .hole, _, _, _ => rfl
  | .parLeft ctx _, inName, _, offset
  | .parRight _ ctx, inName, _, offset
  | .msgLeft ctx _, inName, _, offset
  | .msgRight _ ctx, inName, _, offset
  | .ddSubject ctx _ _, inName, _, offset
  | .ddFirst _ ctx _, inName, _, offset
  | .ddSecond _ _ ctx, inName, _, offset
  | .sySubject ctx _ _, inName, _, offset
  | .syFirst _ ctx _, inName, _, offset
  | .sySecond _ _ ctx, inName, _, offset => by
      have ih := atomCount_assemble s ctx inName (slot s offset) (offset + 3)
      simp only [atomCount, assemble, componentList, List.length_append,
        List.length_cons, List.length_nil, NameContext.weight] at ih ⊢
      omega

/-- **The comparison, both halves together.**  Every context-indexed constructor
is realized by a chain of the ordinary ones, at a cost equal to the sum of the
arities of its nodes plus one. -/
theorem collapsed_constructor_realized (s : Comb) (ctx : NameContext)
    (inName outName v : Comb) :
    ReachesFull (par (assemble s ctx inName outName 0) (mm inName v))
        (mm outName (ctx.fill v))
      ∧ atomCount (assemble s ctx inName outName 0) = ctx.weight + 1 :=
  ⟨assemble_reaches s ctx inName outName 0 v,
    atomCount_assemble s ctx inName outName 0⟩

/-- The converse direction, recorded: each member of the constructor family is
the collapsed atom at a one-hole context of a single node, so neither form
reaches further than the other.  The binary member costs two atoms, the ternary
member three. -/
theorem family_is_collapsed_at_one_node (right b c : Comb) :
    ((NameContext.parLeft NameContext.hole right).weight = 2 ∧
        ∀ v : Comb, (NameContext.parLeft NameContext.hole right).fill v = par v right) ∧
      ((NameContext.ddSubject NameContext.hole b c).weight = 3 ∧
        ∀ v : Comb, (NameContext.ddSubject NameContext.hole b c).fill v = dd v b c) :=
  ⟨⟨rfl, fun _ => rfl⟩, ⟨rfl, fun _ => rfl⟩⟩

/-! ## The compiled soup is linear -/

theorem listeningSubjects_par (p q : Comb) :
    listeningSubjects (par p q) = listeningSubjects p + listeningSubjects q := by
  simp only [listeningSubjects, components, Multiset.add_bind]

theorem speakingSubjects_par (p q : Comb) :
    speakingSubjects (par p q) = speakingSubjects p + speakingSubjects q := by
  simp only [speakingSubjects, components, Multiset.add_bind]

/-- The slot indices the compiled soup listens at, in the order the components
present them. -/
def listeningIndices : NameContext → ℕ → List ℕ
  | .hole, _ => []
  | .parLeft ctx _, d => listeningIndices ctx (d + 3) ++ [d, d + 1]
  | .parRight _ ctx, d => listeningIndices ctx (d + 3) ++ [d + 1, d]
  | .msgLeft ctx _, d => listeningIndices ctx (d + 3) ++ [d, d + 1]
  | .msgRight _ ctx, d => listeningIndices ctx (d + 3) ++ [d + 1, d]
  | .ddSubject ctx _ _, d => listeningIndices ctx (d + 3) ++ [d, d + 1, d + 2]
  | .ddFirst _ ctx _, d => listeningIndices ctx (d + 3) ++ [d + 1, d, d + 2]
  | .ddSecond _ _ ctx, d => listeningIndices ctx (d + 3) ++ [d + 1, d + 2, d]
  | .sySubject ctx _ _, d => listeningIndices ctx (d + 3) ++ [d, d + 1, d + 2]
  | .syFirst _ ctx _, d => listeningIndices ctx (d + 3) ++ [d + 1, d, d + 2]
  | .sySecond _ _ ctx, d => listeningIndices ctx (d + 3) ++ [d + 1, d + 2, d]

/-- The slot indices the compiled soup speaks at: one per statically known
sibling. -/
def speakingIndices : NameContext → ℕ → List ℕ
  | .hole, _ => []
  | .parLeft ctx _, d => speakingIndices ctx (d + 3) ++ [d + 1]
  | .parRight _ ctx, d => speakingIndices ctx (d + 3) ++ [d + 1]
  | .msgLeft ctx _, d => speakingIndices ctx (d + 3) ++ [d + 1]
  | .msgRight _ ctx, d => speakingIndices ctx (d + 3) ++ [d + 1]
  | .ddSubject ctx _ _, d => speakingIndices ctx (d + 3) ++ [d + 1, d + 2]
  | .ddFirst _ ctx _, d => speakingIndices ctx (d + 3) ++ [d + 1, d + 2]
  | .ddSecond _ _ ctx, d => speakingIndices ctx (d + 3) ++ [d + 1, d + 2]
  | .sySubject ctx _ _, d => speakingIndices ctx (d + 3) ++ [d + 1, d + 2]
  | .syFirst _ ctx _, d => speakingIndices ctx (d + 3) ++ [d + 1, d + 2]
  | .sySecond _ _ ctx, d => speakingIndices ctx (d + 3) ++ [d + 1, d + 2]

/-- Every wiring index belongs to the node's own offset or deeper. -/
theorem le_of_mem_listeningIndices : ∀ (ctx : NameContext) (d i : ℕ),
    i ∈ listeningIndices ctx d → d ≤ i
  | .hole, _, _, h => by simp [listeningIndices] at h
  | .parLeft ctx _, d, i, h
  | .parRight _ ctx, d, i, h
  | .msgLeft ctx _, d, i, h
  | .msgRight _ ctx, d, i, h => by
      simp only [listeningIndices, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at h
      rcases h with h | h
      · have := le_of_mem_listeningIndices ctx (d + 3) i h; omega
      · rcases h with rfl | rfl <;> omega
  | .ddSubject ctx _ _, d, i, h
  | .ddFirst _ ctx _, d, i, h
  | .ddSecond _ _ ctx, d, i, h
  | .sySubject ctx _ _, d, i, h
  | .syFirst _ ctx _, d, i, h
  | .sySecond _ _ ctx, d, i, h => by
      simp only [listeningIndices, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at h
      rcases h with h | h
      · have := le_of_mem_listeningIndices ctx (d + 3) i h; omega
      · rcases h with rfl | rfl | rfl <;> omega

theorem le_of_mem_speakingIndices : ∀ (ctx : NameContext) (d i : ℕ),
    i ∈ speakingIndices ctx d → d ≤ i
  | .hole, _, _, h => by simp [speakingIndices] at h
  | .parLeft ctx _, d, i, h
  | .parRight _ ctx, d, i, h
  | .msgLeft ctx _, d, i, h
  | .msgRight _ ctx, d, i, h => by
      simp only [speakingIndices, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at h
      rcases h with h | h
      · have := le_of_mem_speakingIndices ctx (d + 3) i h; omega
      · subst h; omega
  | .ddSubject ctx _ _, d, i, h
  | .ddFirst _ ctx _, d, i, h
  | .ddSecond _ _ ctx, d, i, h
  | .sySubject ctx _ _, d, i, h
  | .syFirst _ ctx _, d, i, h
  | .sySecond _ _ ctx, d, i, h => by
      simp only [speakingIndices, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at h
      rcases h with h | h
      · have := le_of_mem_speakingIndices ctx (d + 3) i h; omega
      · rcases h with rfl | rfl <;> omega

/-- Every wiring index stays inside the range the context reserved, which is
what lets a caller give a sibling a disjoint range. -/
theorem lt_of_mem_listeningIndices : ∀ (ctx : NameContext) (d i : ℕ),
    i ∈ listeningIndices ctx d → i < d + ctx.slotsUsed
  | .hole, _, _, h => by simp [listeningIndices] at h
  | .parLeft ctx _, d, i, h
  | .parRight _ ctx, d, i, h
  | .msgLeft ctx _, d, i, h
  | .msgRight _ ctx, d, i, h
  | .ddSubject ctx _ _, d, i, h
  | .ddFirst _ ctx _, d, i, h
  | .ddSecond _ _ ctx, d, i, h
  | .sySubject ctx _ _, d, i, h
  | .syFirst _ ctx _, d, i, h
  | .sySecond _ _ ctx, d, i, h => by
      simp only [listeningIndices, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, NameContext.slotsUsed] at h ⊢
      rcases h with h | h
      · have := lt_of_mem_listeningIndices ctx (d + 3) i h
        omega
      · have base : 3 ≤ ctx.slotsUsed + 3 := by omega
        rcases h with rfl | rfl | rfl <;> omega

theorem lt_of_mem_speakingIndices : ∀ (ctx : NameContext) (d i : ℕ),
    i ∈ speakingIndices ctx d → i < d + ctx.slotsUsed
  | .hole, _, _, h => by simp [speakingIndices] at h
  | .parLeft ctx _, d, i, h
  | .parRight _ ctx, d, i, h
  | .msgLeft ctx _, d, i, h
  | .msgRight _ ctx, d, i, h
  | .ddSubject ctx _ _, d, i, h
  | .ddFirst _ ctx _, d, i, h
  | .ddSecond _ _ ctx, d, i, h
  | .sySubject ctx _ _, d, i, h
  | .syFirst _ ctx _, d, i, h
  | .sySecond _ _ ctx, d, i, h => by
      simp only [speakingIndices, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, NameContext.slotsUsed] at h ⊢
      rcases h with h | h
      · have := lt_of_mem_speakingIndices ctx (d + 3) i h
        omega
      · rcases h with rfl | rfl <;> omega

/-- **The wiring indices are distinct.**  Each node's slots sit strictly below
its subtree's, so distinctness is arithmetic. -/
theorem nodup_listeningIndices : ∀ (ctx : NameContext) (d : ℕ),
    (listeningIndices ctx d).Nodup
  | .hole, _ => by simp [listeningIndices]
  | .parLeft ctx _, d
  | .parRight _ ctx, d
  | .msgLeft ctx _, d
  | .msgRight _ ctx, d => by
      have ih := nodup_listeningIndices ctx (d + 3)
      have bound := le_of_mem_listeningIndices ctx (d + 3)
      simp only [listeningIndices, List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      have deep := bound _ ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      omega
  | .ddSubject ctx _ _, d
  | .ddFirst _ ctx _, d
  | .ddSecond _ _ ctx, d
  | .sySubject ctx _ _, d
  | .syFirst _ ctx _, d
  | .sySecond _ _ ctx, d => by
      have ih := nodup_listeningIndices ctx (d + 3)
      have bound := le_of_mem_listeningIndices ctx (d + 3)
      simp only [listeningIndices, List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      have deep := bound _ ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      omega

theorem nodup_speakingIndices : ∀ (ctx : NameContext) (d : ℕ),
    (speakingIndices ctx d).Nodup
  | .hole, _ => by simp [speakingIndices]
  | .parLeft ctx _, d
  | .parRight _ ctx, d
  | .msgLeft ctx _, d
  | .msgRight _ ctx, d => by
      have ih := nodup_speakingIndices ctx (d + 3)
      have bound := le_of_mem_speakingIndices ctx (d + 3)
      simp only [speakingIndices, List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      have deep := bound _ ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      omega
  | .ddSubject ctx _ _, d
  | .ddFirst _ ctx _, d
  | .ddSecond _ _ ctx, d
  | .sySubject ctx _ _, d
  | .syFirst _ ctx _, d
  | .sySecond _ _ ctx, d => by
      have ih := nodup_speakingIndices ctx (d + 3)
      have bound := le_of_mem_speakingIndices ctx (d + 3)
      simp only [speakingIndices, List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      have deep := bound _ ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      omega

/-- Components are atoms, so an atom's subject multiset is its subject list. -/
theorem listeningSubjects_of_atom {t : Comb} (h : components t = {t}) :
    listeningSubjects t = (listenSubjects t : Multiset Comb) := by
  simp only [listeningSubjects, h, Multiset.singleton_bind]

theorem speakingSubjects_of_atom {t : Comb} (h : components t = {t}) :
    speakingSubjects t = (speakSubjects t : Multiset Comb) := by
  simp only [speakingSubjects, h, Multiset.singleton_bind]

theorem coe_single (a : Comb) : (([a] : List Comb) : Multiset Comb) = {a} := rfl
theorem coe_pair (a b : Comb) : (([a, b] : List Comb) : Multiset Comb) = {a} + {b} := rfl
theorem coe_triple (a b c : Comb) :
    (([a, b, c] : List Comb) : Multiset Comb) = {a} + ({b} + {c}) := rfl

theorem nodup_pair_add {a b : Comb} (h : a ≠ b) : (({a} + {b} : Multiset Comb)).Nodup := by
  rw [show ({a} + {b} : Multiset Comb) = ((([a, b] : List Comb)) : Multiset Comb) from rfl,
    Multiset.coe_nodup]
  simp [h]

theorem nodup_triple_add {a b c : Comb} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (({a} + ({b} + {c}) : Multiset Comb)).Nodup := by
  rw [show ({a} + ({b} + {c}) : Multiset Comb) = ((([a, b, c] : List Comb)) : Multiset Comb)
    from rfl, Multiset.coe_nodup]
  simp [hab, hac, hbc]

/-- **The listening positions of a compiled soup.**  One is the name the soup
waits for; every other is a wiring slot at the node's own offset or deeper, and
they are pairwise distinct. -/
theorem listening_structure (s : Comb) : ∀ (ctx : NameContext) (inName outName : Comb)
    (d : ℕ), ∃ wiring : Multiset Comb,
      listeningSubjects (assemble s ctx inName outName d) = {inName} + wiring
        ∧ wiring.Nodup
        ∧ ∀ x ∈ wiring, ∃ i, d ≤ i ∧ i < d + ctx.slotsUsed ∧ x = slot s i
  | .hole, inName, outName, _ =>
      ⟨0, by
        rw [assemble, listeningSubjects_of_atom (t := fw inName outName) rfl]
        simp only [listenSubjects, coe_single, add_zero], Multiset.nodup_zero, by simp⟩
  | .parLeft ctx _, inName, outName, d
  | .parRight _ ctx, inName, outName, d
  | .msgLeft ctx _, inName, outName, d
  | .msgRight _ ctx, inName, outName, d => by
      obtain ⟨wiring, hEq, hNodup, hSlots⟩ :=
        listening_structure s ctx inName (slot s d) (d + 3)
      refine ⟨wiring + ({slot s d} + {slot s (d + 1)}), ?_, ?_, ?_⟩
      · rw [assemble, listeningSubjects_par, listeningSubjects_par, hEq]
        simp only [listeningSubjects, components, Multiset.singleton_bind,
          listenSubjects, Multiset.coe_nil, coe_pair]
        ac_rfl
      · rw [Multiset.nodup_add]
        refine ⟨hNodup, nodup_pair_add (slot_ne (by omega)), ?_⟩
        refine Multiset.disjoint_left.mpr ?_
        intro a ha hb
        obtain ⟨i, hi, hiLt, rfl⟩ := hSlots a ha
        simp only [Multiset.mem_add, Multiset.mem_singleton] at hb
        rcases hb with h | h <;> exact slot_ne (by omega) h
      · intro x hx
        simp only [Multiset.mem_add, Multiset.mem_singleton] at hx
        rcases hx with h | h | h
        · obtain ⟨i, hi, hiLt, rfl⟩ := hSlots x h
          simp only [NameContext.slotsUsed]
          exact ⟨i, by omega, by omega, rfl⟩
        · exact ⟨d, by omega, by simp only [NameContext.slotsUsed]; omega, h⟩
        · exact ⟨d + 1, by omega, by simp only [NameContext.slotsUsed]; omega, h⟩
  | .ddSubject ctx _ _, inName, outName, d
  | .ddFirst _ ctx _, inName, outName, d
  | .ddSecond _ _ ctx, inName, outName, d
  | .sySubject ctx _ _, inName, outName, d
  | .syFirst _ ctx _, inName, outName, d
  | .sySecond _ _ ctx, inName, outName, d => by
      obtain ⟨wiring, hEq, hNodup, hSlots⟩ :=
        listening_structure s ctx inName (slot s d) (d + 3)
      refine ⟨wiring + ({slot s d} + ({slot s (d + 1)} + {slot s (d + 2)})),
        ?_, ?_, ?_⟩
      · rw [assemble, listeningSubjects_par, listeningSubjects_par,
          listeningSubjects_par, hEq]
        simp only [listeningSubjects, components, Multiset.singleton_bind,
          listenSubjects, Multiset.coe_nil, coe_triple]
        ac_rfl
      · rw [Multiset.nodup_add]
        refine ⟨hNodup, nodup_triple_add (slot_ne (by omega)) (slot_ne (by omega))
          (slot_ne (by omega)), ?_⟩
        refine Multiset.disjoint_left.mpr ?_
        intro a ha hb
        obtain ⟨i, hi, hiLt, rfl⟩ := hSlots a ha
        simp only [Multiset.mem_add, Multiset.mem_singleton] at hb
        rcases hb with h | h | h <;> exact slot_ne (by omega) h
      · intro x hx
        simp only [Multiset.mem_add, Multiset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · obtain ⟨i, hi, hiLt, rfl⟩ := hSlots x h
          simp only [NameContext.slotsUsed]
          exact ⟨i, by omega, by omega, rfl⟩
        · exact ⟨d, by omega, by simp only [NameContext.slotsUsed]; omega, h⟩
        · exact ⟨d + 1, by omega, by simp only [NameContext.slotsUsed]; omega, h⟩
        · exact ⟨d + 2, by omega, by simp only [NameContext.slotsUsed]; omega, h⟩

/-- **The speaking positions of a compiled soup.**  One per statically known
sibling, all at the node's own offset or deeper, pairwise distinct. -/
theorem speaking_structure (s : Comb) : ∀ (ctx : NameContext) (inName outName : Comb)
    (d : ℕ), ∃ wiring : Multiset Comb,
      speakingSubjects (assemble s ctx inName outName d) = wiring
        ∧ wiring.Nodup
        ∧ ∀ x ∈ wiring, ∃ i, d ≤ i ∧ i < d + ctx.slotsUsed ∧ x = slot s i
  | .hole, inName, outName, _ =>
      ⟨0, by
        rw [assemble, speakingSubjects_of_atom (t := fw inName outName) rfl]
        simp only [speakSubjects, Multiset.coe_nil], Multiset.nodup_zero, by simp⟩
  | .parLeft ctx _, inName, outName, d
  | .parRight _ ctx, inName, outName, d
  | .msgLeft ctx _, inName, outName, d
  | .msgRight _ ctx, inName, outName, d => by
      obtain ⟨wiring, hEq, hNodup, hSlots⟩ :=
        speaking_structure s ctx inName (slot s d) (d + 3)
      refine ⟨wiring + {slot s (d + 1)}, ?_, ?_, ?_⟩
      · rw [assemble, speakingSubjects_par, speakingSubjects_par, hEq]
        simp only [speakingSubjects, components, Multiset.singleton_bind,
          speakSubjects, Multiset.coe_nil, coe_single]
        ac_rfl
      · rw [Multiset.nodup_add]
        refine ⟨hNodup, Multiset.nodup_singleton _, ?_⟩
        refine Multiset.disjoint_left.mpr ?_
        intro a ha hb
        obtain ⟨i, hi, hiLt, rfl⟩ := hSlots a ha
        simp only [Multiset.mem_singleton] at hb
        exact slot_ne (by omega) hb
      · intro x hx
        simp only [Multiset.mem_add, Multiset.mem_singleton] at hx
        rcases hx with h | h
        · obtain ⟨i, hi, hiLt, rfl⟩ := hSlots x h
          simp only [NameContext.slotsUsed]
          exact ⟨i, by omega, by omega, rfl⟩
        · exact ⟨d + 1, by omega, by simp only [NameContext.slotsUsed]; omega, h⟩
  | .ddSubject ctx _ _, inName, outName, d
  | .ddFirst _ ctx _, inName, outName, d
  | .ddSecond _ _ ctx, inName, outName, d
  | .sySubject ctx _ _, inName, outName, d
  | .syFirst _ ctx _, inName, outName, d
  | .sySecond _ _ ctx, inName, outName, d => by
      obtain ⟨wiring, hEq, hNodup, hSlots⟩ :=
        speaking_structure s ctx inName (slot s d) (d + 3)
      refine ⟨wiring + ({slot s (d + 1)} + {slot s (d + 2)}), ?_, ?_, ?_⟩
      · rw [assemble, speakingSubjects_par, speakingSubjects_par,
          speakingSubjects_par, hEq]
        simp only [speakingSubjects, components, Multiset.singleton_bind,
          speakSubjects, Multiset.coe_nil, coe_single]
        ac_rfl
      · rw [Multiset.nodup_add]
        refine ⟨hNodup, nodup_pair_add (slot_ne (by omega)), ?_⟩
        refine Multiset.disjoint_left.mpr ?_
        intro a ha hb
        obtain ⟨i, hi, hiLt, rfl⟩ := hSlots a ha
        simp only [Multiset.mem_add, Multiset.mem_singleton] at hb
        rcases hb with h | h <;> exact slot_ne (by omega) h
      · intro x hx
        simp only [Multiset.mem_add, Multiset.mem_singleton] at hx
        rcases hx with h | h | h
        · obtain ⟨i, hi, hiLt, rfl⟩ := hSlots x h
          simp only [NameContext.slotsUsed]
          exact ⟨i, by omega, by omega, rfl⟩
        · exact ⟨d + 1, by omega, by simp only [NameContext.slotsUsed]; omega, h⟩
        · exact ⟨d + 2, by omega, by simp only [NameContext.slotsUsed]; omega, h⟩

/-- **The compiled soup is linear.**  Wired from the slots of the very term it
waits at, no name in the compiled chain has two possible partners.  Together
with `atomCount_assemble` this makes `assemble` a compiler carrying both a cost
theorem and a non-interference theorem. -/
theorem assemble_linear (s : Comb) (ctx : NameContext) (outName : Comb) :
    Linear (assemble s ctx s outName 0) where
  listening := by
    obtain ⟨wiring, hEq, hNodup, hSlots⟩ := listening_structure s ctx s outName 0
    rw [hEq, Multiset.nodup_add]
    refine ⟨Multiset.nodup_singleton _, hNodup, Multiset.disjoint_left.mpr ?_⟩
    intro a ha hb
    simp only [Multiset.mem_singleton] at ha
    subst ha
    obtain ⟨i, -, -, hi⟩ := hSlots a hb
    exact ne_slot_self a i hi
  speaking := by
    obtain ⟨wiring, hEq, hNodup, -⟩ := speaking_structure s ctx s outName 0
    rw [hEq]; exact hNodup

end Mettapedia.Languages.ProcessCalculi.RhoCombinators