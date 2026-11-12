import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic

/-!
# When pairwise compatibility gives a joint wave

A tell is read semantically as the set of solutions it allows. A wave of tells is jointly solvable
when their sets meet; a pair is compatible when the two sets meet. The waves form the nerve of the
family of sets, and "pairwise compatible families are waves" says that this nerve is a flag
complex: every set of tells that pairwise span edges spans a simplex. The hollow cube is a hollow
triangle in the nerve, the boundary of a simplex with no filler; it is not a failure of horn
filling, since all three edges are present.

## Two structural conditions

* **Helly through a ternary operation** (`helly`): if a ternary operation `m` keeps each set of a
  family whenever two of its three arguments lie in the set (`MedianConvex`), then pairwise
  meeting members of the family have a common point. Ground tells (`ground`: a variable equals a
  value) are convex for the coordinatewise median (`ground_convex`); a tell that equates two
  variables is not (`diagonal_not_convex`).
* **Gluing along a consistent join tree** (`ConsistentTree.glue`): local constraints with scopes,
  attached one at a time to a parent that covers the overlap of the new scope with the earlier ones
  (running intersection), where every solution of the parent extends to a solution of the child
  agreeing on their overlap, have a joint solution. This is the sheaf condition: agreement on
  overlaps, which is stronger than pairwise solvability.

## The hollow cube

`X = Y`, `X = 1`, `Y = 2` (`hollow_pairwise`, `hollow_not_joint`): pairwise solvable and not
jointly solvable. Its scopes `{X, Y}`, `{X}`, `{Y}` satisfy running intersection with `X = Y` as
parent (`hollow_running`), so acyclic scopes do not make pairwise solvability enough. What fails
is consistency: a solution of `X = Y` need not extend to `X = 1` (`hollow_not_consistent`), and no
consistent join tree holds the three (`hollow_no_consistent_tree`). The culprit is the equation
between variables: it is the one tell that is not median-convex.

The cyclic triangle of disequalities over two values (`triangle_pairwise_consistent`,
`triangle_not_joint`) shows that running intersection cannot be dropped from the gluing theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns

universe uSol uV uD

/-! ## Helly through a ternary operation -/

section Helly

variable {Sol : Type uSol}

/-- A set is **median-convex** for a ternary operation when it holds the operation's value as soon
as it holds two of the three arguments. -/
def MedianConvex (m : Sol → Sol → Sol → Sol) (A : Set Sol) : Prop :=
  ∀ x y z : Sol, (x ∈ A ∧ y ∈ A) ∨ (x ∈ A ∧ z ∈ A) ∨ (y ∈ A ∧ z ∈ A) → m x y z ∈ A

theorem MedianConvex.inter {m : Sol → Sol → Sol → Sol} {A B : Set Sol} (first : MedianConvex m A)
    (second : MedianConvex m B) : MedianConvex m (A ∩ B) := by
  intro x y z two
  rcases two with ⟨hx, hy⟩ | ⟨hx, hz⟩ | ⟨hy, hz⟩
  · exact ⟨first x y z (Or.inl ⟨hx.1, hy.1⟩), second x y z (Or.inl ⟨hx.2, hy.2⟩)⟩
  · exact ⟨first x y z (Or.inr (Or.inl ⟨hx.1, hz.1⟩)), second x y z (Or.inr (Or.inl ⟨hx.2, hz.2⟩))⟩
  · exact ⟨first x y z (Or.inr (Or.inr ⟨hy.1, hz.1⟩)), second x y z (Or.inr (Or.inr ⟨hy.2, hz.2⟩))⟩

/-- **Three convex sets that meet pairwise meet.** The operation of the three pairwise witnesses
is the common point. -/
theorem helly_three {m : Sol → Sol → Sol → Sol} {A B C : Set Sol} (convexA : MedianConvex m A)
    (convexB : MedianConvex m B) (convexC : MedianConvex m C) (AB : (A ∩ B).Nonempty)
    (AC : (A ∩ C).Nonempty) (BC : (B ∩ C).Nonempty) : (A ∩ B ∩ C).Nonempty := by
  obtain ⟨a, aB, aC⟩ := BC
  obtain ⟨b, bA, bC⟩ := AC
  obtain ⟨c, cA, cB⟩ := AB
  exact ⟨m a b c, ⟨convexA a b c (Or.inr (Or.inr ⟨bA, cA⟩)), convexB a b c (Or.inr (Or.inl ⟨aB, cB⟩))⟩,
    convexC a b c (Or.inl ⟨aC, bC⟩)⟩

theorem helly_cons {m : Sol → Sol → Sol → Sol} : ∀ (rest : List (Set Sol)) (A : Set Sol),
    (∀ C ∈ A :: rest, MedianConvex m C) →
    (∀ C ∈ A :: rest, ∀ D ∈ A :: rest, (C ∩ D).Nonempty) → ∃ x, ∀ C ∈ A :: rest, x ∈ C
  | [], A, _, pairwise => by
      obtain ⟨x, hx, _⟩ := pairwise A List.mem_cons_self A List.mem_cons_self
      refine ⟨x, fun C member => ?_⟩
      rw [List.mem_singleton.mp member]
      exact hx
  | B :: rest, A, convex, pairwise => by
      have inA : A ∈ A :: B :: rest := List.mem_cons_self
      have inB : B ∈ A :: B :: rest := List.mem_cons_of_mem _ List.mem_cons_self
      have inRest : ∀ C ∈ rest, C ∈ A :: B :: rest :=
        fun C member => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)
      have meets : ∀ D ∈ rest, (A ∩ B ∩ D).Nonempty := fun D member =>
        helly_three (convex A inA) (convex B inB) (convex D (inRest D member))
          (pairwise A inA B inB) (pairwise A inA D (inRest D member)) (pairwise B inB D (inRest D member))
      obtain ⟨x, hx⟩ := helly_cons rest (A ∩ B)
        (by
          intro C member
          rcases List.mem_cons.mp member with rfl | member
          · exact (convex A inA).inter (convex B inB)
          · exact convex C (inRest C member))
        (by
          intro C memberC D memberD
          rcases List.mem_cons.mp memberC with rfl | memberC <;>
            rcases List.mem_cons.mp memberD with rfl | memberD
          · rw [Set.inter_self]
            exact pairwise A inA B inB
          · exact meets D memberD
          · rw [Set.inter_comm]
            exact meets C memberC
          · exact pairwise C (inRest C memberC) D (inRest D memberD))
      have both := hx (A ∩ B) List.mem_cons_self
      refine ⟨x, fun C member => ?_⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact both.1
      rcases List.mem_cons.mp member with rfl | member
      · exact both.2
      exact hx C (List.mem_cons_of_mem _ member)

/-- **Helly through a ternary operation.** A nonempty family of median-convex sets that meet
pairwise has a common point: pairwise compatible convex tells form a joint wave. -/
theorem helly {m : Sol → Sol → Sol → Sol} (sets : List (Set Sol)) (nonempty : sets ≠ [])
    (convex : ∀ C ∈ sets, MedianConvex m C) (pairwise : ∀ C ∈ sets, ∀ D ∈ sets, (C ∩ D).Nonempty) :
    ∃ x, ∀ C ∈ sets, x ∈ C := by
  cases sets with
  | nil => exact absurd rfl nonempty
  | cons A rest => exact helly_cons rest A convex pairwise

end Helly

/-! ## Tells over assignments -/

section Tells

variable {V : Type uV} {D : Type uD}

/-- The coordinatewise median of three assignments: the second where the second and third agree,
and the first elsewhere. -/
def median [DecidableEq D] (x y z : V → D) : V → D :=
  fun v => if y v = z v then y v else x v

/-- The ground tell `v = c`. -/
def ground (v : V) (c : D) : Set (V → D) := {σ | σ v = c}

/-- The tell `v = w` between two variables. -/
def diagonal (v w : V) : Set (V → D) := {σ | σ v = σ w}

/-- **Ground tells are median-convex.** -/
theorem ground_convex [DecidableEq D] (v : V) (c : D) : MedianConvex median (ground v c : Set (V → D)) := by
  intro x y z two
  show (if y v = z v then y v else x v) = c
  rcases two with ⟨hx, hy⟩ | ⟨hx, hz⟩ | ⟨hy, hz⟩
  · have hx : x v = c := hx
    have hy : y v = c := hy
    split_ifs <;> assumption
  · have hx : x v = c := hx
    have hz : z v = c := hz
    split_ifs with same
    · exact same.trans hz
    · exact hx
  · have hy : y v = c := hy
    have hz : z v = c := hz
    split_ifs with same
    · exact hy
    · exact absurd (hy.trans hz.symm) same

/-- **Pairwise solvable ground tells are jointly solvable.** -/
theorem ground_joint [DecidableEq D] (tells : List (V × D)) (nonempty : tells ≠ [])
    (pairwise : ∀ p ∈ tells, ∀ q ∈ tells,
      ((ground p.1 p.2 : Set (V → D)) ∩ ground q.1 q.2).Nonempty) :
    ∃ σ : V → D, ∀ p ∈ tells, σ p.1 = p.2 := by
  obtain ⟨σ, every⟩ := helly (m := median) (tells.map fun p => (ground p.1 p.2 : Set (V → D)))
    (by simpa using nonempty)
    (by
      intro C member
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp member
      exact ground_convex p.1 p.2)
    (by
      intro C memberC E memberE
      obtain ⟨p, inP, rfl⟩ := List.mem_map.mp memberC
      obtain ⟨q, inQ, rfl⟩ := List.mem_map.mp memberE
      exact pairwise p inP q inQ)
  exact ⟨σ, fun p member => every _ (List.mem_map.mpr ⟨p, member, rfl⟩)⟩

/-- **An equation between two variables is not median-convex.** -/
theorem diagonal_not_convex :
    ¬ MedianConvex median (diagonal false true : Set (Bool → Nat)) := by
  intro convex
  have inside := convex (fun _ => 1) (fun _ => 2) (fun b => if b then 3 else 2)
    (Or.inl ⟨rfl, rfl⟩)
  have value : (median (fun _ => 1) (fun _ => 2) (fun b => if b then 3 else 2) : Bool → Nat) false =
      (median (fun _ => 1) (fun _ => 2) (fun b => if b then 3 else 2) : Bool → Nat) true := inside
  simp [median] at value

end Tells

/-! ## The hollow cube -/

section Hollow

/-- `X = Y`, with `X` the variable `false` and `Y` the variable `true`. -/
abbrev tellSame : Set (Bool → Nat) := diagonal false true

/-- `X = 1`. -/
abbrev tellOne : Set (Bool → Nat) := ground false 1

/-- `Y = 2`. -/
abbrev tellTwo : Set (Bool → Nat) := ground true 2

/-- **The three tells are pairwise solvable.** -/
theorem hollow_pairwise :
    (tellSame ∩ tellOne).Nonempty ∧ (tellSame ∩ tellTwo).Nonempty ∧ (tellOne ∩ tellTwo).Nonempty :=
  ⟨⟨fun _ => 1, rfl, rfl⟩, ⟨fun _ => 2, rfl, rfl⟩, ⟨fun b => if b then 2 else 1, rfl, rfl⟩⟩

/-- **The three tells are not jointly solvable.** -/
theorem hollow_not_joint : ¬ (tellSame ∩ tellOne ∩ tellTwo).Nonempty := by
  rintro ⟨σ, ⟨same, one⟩, two⟩
  have same : σ false = σ true := same
  have one : σ false = 1 := one
  have two : σ true = 2 := two
  omega

/-- **The nerve of the three tells is a hollow triangle**: every pair spans an edge and the three
span no simplex. -/
theorem hollow_not_flag :
    ¬ ∀ sets : List (Set (Bool → Nat)), sets ≠ [] → (∀ C ∈ sets, ∀ D ∈ sets, (C ∩ D).Nonempty) →
      ∃ x, ∀ C ∈ sets, x ∈ C := by
  intro flag
  obtain ⟨x, every⟩ := flag [tellSame, tellOne, tellTwo] (List.cons_ne_nil _ _) (by
    obtain ⟨sameOne, sameTwo, oneTwo⟩ := hollow_pairwise
    intro C memberC D memberD
    simp only [List.mem_cons, List.not_mem_nil, or_false] at memberC memberD
    rcases memberC with rfl | rfl | rfl <;> rcases memberD with rfl | rfl | rfl
    · rw [Set.inter_self]; exact sameOne.mono Set.inter_subset_left
    · exact sameOne
    · exact sameTwo
    · rw [Set.inter_comm]; exact sameOne
    · rw [Set.inter_self]; exact sameOne.mono Set.inter_subset_right
    · exact oneTwo
    · rw [Set.inter_comm]; exact sameTwo
    · rw [Set.inter_comm]; exact oneTwo
    · rw [Set.inter_self]; exact oneTwo.mono Set.inter_subset_right)
  exact hollow_not_joint ⟨x, ⟨every _ List.mem_cons_self,
    every _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩,
    every _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

end Hollow

/-! ## Gluing along a consistent join tree -/

section Gluing

variable {V : Type uV} {D : Type uD}

/-- A local constraint: a scope of variables, and a property of assignments that depends only on
the scope. -/
structure Local (V : Type uV) (D : Type uD) where
  scope : Set V
  holds : (V → D) → Prop
  depends : ∀ σ τ : V → D, (∀ v ∈ scope, σ v = τ v) → holds σ → holds τ

/-- **A consistent join tree**: constraints attached one at a time to a parent that covers the
overlap of the new scope with all earlier scopes, where every solution of the parent extends to
a solution of the new constraint that agrees with it on their overlap. -/
inductive ConsistentTree : List (Local V D) → Prop
  | root (c : Local V D) (inhabited : ∃ σ, c.holds σ) : ConsistentTree [c]
  | attach {cs : List (Local V D)} (parent child : Local V D) (tree : ConsistentTree cs)
      (member : parent ∈ cs)
      (running : ∀ v ∈ child.scope, (∃ c ∈ cs, v ∈ c.scope) → v ∈ parent.scope)
      (consistent : ∀ σ, parent.holds σ →
        ∃ τ, child.holds τ ∧ ∀ v ∈ child.scope, v ∈ parent.scope → τ v = σ v) :
      ConsistentTree (child :: cs)

/-- **Gluing**: the constraints of a consistent join tree have a joint solution. -/
theorem ConsistentTree.glue {cs : List (Local V D)} (tree : ConsistentTree cs) :
    ∃ σ : V → D, ∀ c ∈ cs, c.holds σ := by
  classical
  induction tree with
  | root c inhabited =>
      obtain ⟨σ, held⟩ := inhabited
      exact ⟨σ, fun c' member => by rw [List.mem_singleton.mp member]; exact held⟩
  | @attach cs parent child _ member running consistent ih =>
      obtain ⟨σ, every⟩ := ih
      obtain ⟨τ, childHolds, agree⟩ := consistent σ (every parent member)
      refine ⟨fun v => if v ∈ child.scope then τ v else σ v, fun c inside => ?_⟩
      rcases List.mem_cons.mp inside with rfl | earlier
      · refine c.depends τ _ (fun v inScope => ?_) childHolds
        simp [inScope]
      · refine c.depends σ _ (fun v inScope => ?_) (every c earlier)
        by_cases inChild : v ∈ child.scope
        · simp only [inChild, if_true]
          exact (agree v inChild (running v inChild ⟨c, earlier, inScope⟩)).symm
        · simp [inChild]

/-! ### The hollow cube as local constraints -/

/-- `X = Y` on the scope `{X, Y}`. -/
def localSame : Local Bool Nat where
  scope := Set.univ
  holds σ := σ false = σ true
  depends σ τ agree held := by
    rw [← agree false (Set.mem_univ _), ← agree true (Set.mem_univ _)]
    exact held

/-- `X = 1` on the scope `{X}`. -/
def localOne : Local Bool Nat where
  scope := {false}
  holds σ := σ false = 1
  depends σ τ agree held := by
    rw [← agree false rfl]
    exact held

/-- `Y = 2` on the scope `{Y}`. -/
def localTwo : Local Bool Nat where
  scope := {true}
  holds σ := σ true = 2
  depends σ τ agree held := by
    rw [← agree true rfl]
    exact held

/-- **The scopes of the hollow cube satisfy running intersection** with `X = Y` as parent: every
variable of `X = 1` or `Y = 2` lies in the scope of `X = Y`. -/
theorem hollow_running :
    (∀ v ∈ localOne.scope, v ∈ localSame.scope) ∧ (∀ v ∈ localTwo.scope, v ∈ localSame.scope) :=
  ⟨fun _ _ => Set.mem_univ _, fun _ _ => Set.mem_univ _⟩

/-- **The hollow cube is not consistent along its tree**: a solution of `X = Y` need not extend to a
solution of `X = 1` that agrees with it on `X`. -/
theorem hollow_not_consistent :
    ¬ ∀ σ, localSame.holds σ →
      ∃ τ, localOne.holds τ ∧ ∀ v ∈ localOne.scope, v ∈ localSame.scope → τ v = σ v := by
  intro consistent
  obtain ⟨τ, one, agree⟩ := consistent (fun _ => 0) rfl
  have here : τ false = 0 := agree false rfl (Set.mem_univ _)
  have one : τ false = 1 := one
  omega

/-- **No consistent join tree holds the hollow cube.** -/
theorem hollow_no_consistent_tree :
    ¬ ∃ cs : List (Local Bool Nat), ConsistentTree cs ∧ localSame ∈ cs ∧ localOne ∈ cs ∧ localTwo ∈ cs := by
  rintro ⟨cs, tree, inSame, inOne, inTwo⟩
  obtain ⟨σ, every⟩ := tree.glue
  have same : σ false = σ true := every _ inSame
  have one : σ false = 1 := every _ inOne
  have two : σ true = 2 := every _ inTwo
  omega

/-- **A consistent tree of two of the tells**: `X = 1` as root, and `X = Y` attached to it. -/
theorem one_then_same_consistent : ConsistentTree [localSame, localOne] := by
  refine ConsistentTree.attach localOne localSame (ConsistentTree.root localOne ⟨fun _ => 1, rfl⟩)
    List.mem_cons_self ?_ ?_
  · rintro v - ⟨c, member, inScope⟩
    rw [List.mem_singleton.mp member] at inScope
    exact inScope
  · intro σ one
    refine ⟨fun _ => 1, rfl, fun v _ inOne => ?_⟩
    have here : v = false := inOne
    subst here
    exact one.symm

/-! ### Running intersection cannot be dropped -/

/-- The disequality of two of three variables over two values. -/
def apart (i j : Fin 3) : Local (Fin 3) Bool where
  scope := {i, j}
  holds σ := σ i ≠ σ j
  depends σ τ agree held := by
    rw [← agree i (Or.inl rfl), ← agree j (Or.inr rfl)]
    exact held

/-- **The triangle of disequalities is pairwise consistent**: every solution of one side extends to
a solution of the next that agrees with it on their shared variable. -/
theorem triangle_pairwise_consistent (i j k : Fin 3) (jk : j ≠ k) :
    ∀ σ, (apart i j).holds σ → ∃ τ, (apart j k).holds τ ∧ τ j = σ j := by
  intro σ _
  refine ⟨fun v => if v = k then !σ j else σ v, ?_, ?_⟩
  · show (if j = k then !σ j else σ j) ≠ (if k = k then !σ j else σ k)
    simp [jk]
  · simp [jk]

/-- **The triangle has no joint solution.** -/
theorem triangle_not_joint :
    ¬ ∃ σ : Fin 3 → Bool, (apart 0 1).holds σ ∧ (apart 1 2).holds σ ∧ (apart 2 0).holds σ := by
  rintro ⟨σ, first, second, third⟩
  have first : σ 0 ≠ σ 1 := first
  have second : σ 1 ≠ σ 2 := second
  have third : σ 2 ≠ σ 0 := third
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;> simp_all

end Gluing

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns
