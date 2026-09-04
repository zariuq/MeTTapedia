import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation

/-!
# Colored set universes with opaque atoms

Mutually reflective families of set universes indexed by a *visibility graph*:
a color `c` builds sets of its own objects, and every color it sees
contributes its objects as *opaque atoms* — references that retain identity
but expose no membership structure.  This is the many-colored set-builder

  `(H_C U) c  =  P_small (U c)  +  Σ_{c sees d} U d`

of the two-color knotted-universe construction, generalized to an arbitrary
visibility graph and developed here at the finitary syntactic tier.
`WfObject` is the inductively generated, finite-branching syntax obtained
from the displayed constructors.  No initial-algebra universal property is
claimed here.  `ColoredSystem` supplies finitely branching cyclic transition
presentations, without claiming a final coalgebra or a bisimulation quotient.

The layers are kept separate:

* **data**: `VisibilityGraph`, with the complete (jewel-net) graph, the
  two-color knot, and the discrete graph as instances;
* **construction**: `WfObject` (well-founded finite-branching syntax),
  `ColoredSystem` (possibly cyclic, finitely branching presentations);
* **semantics**: same-color membership `MemberOf`, the color-local
  observation `blindView`, local and global unfolding steps;
* **theorems and canaries**: opacity, impossibility of transparent
  reflection, jewel-permutation equivariance, local foundation beside a
  global alternating cycle, and observer nonfaithfulness.

The two central results:

* **Reflection is reference, not containment.**  `atom` is injective
  (`atom_injective`: references retain identity) yet contributes no members
  (`atom_memberless`: opacity), and the embedding `U d ↪ U c` it induces is
  cardinality-safe (`atomEmbedding`).  By contrast a *transparent*
  reflection — an injective encoding of a universe's own powerclass into
  that universe — is impossible (`transparent_reflection_impossible`,
  Cantor's diagonal).  The veil is exactly what separates total mutual
  reflection from unrestricted comprehension.
* **The veil breaks transparency, not symmetry.**  Every automorphism of
  the visibility graph acts on objects preserving the set/atom structure
  and same-color membership (`relabel`, `memberOf_relabel`,
  `relabel_injective`); on the complete graph every permutation of jewels
  is such an automorphism (`completeAut`).

At class scale the same construction is the domain of algebraic set theory
(small maps, powerclass functors, and their initial algebras and final
coalgebras); nothing here presumes that machinery.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.ColoredOpaqueUniverses

universe u

/-! ## Data: visibility graphs -/

/-- A visibility graph: a type of colors (perspectives, jewels) and, for each
color, which other colors it may hold as opaque atoms. -/
structure VisibilityGraph : Type (u + 1) where
  Color : Type u
  Sees : Color → Color → Prop

namespace VisibilityGraph

/-- The complete visibility graph on `J`: every jewel sees every other. -/
def complete (J : Type u) : VisibilityGraph where
  Color := J
  Sees c d := c ≠ d

/-- The two-color knot: each of two colors sees exactly the other. -/
abbrev pair : VisibilityGraph := complete Bool

/-- The discrete graph: no color sees any other — isolated monochrome
worlds. -/
def discrete (J : Type u) : VisibilityGraph where
  Color := J
  Sees _ _ := False

/-- An automorphism of a visibility graph: a permutation of colors that
preserves visibility in both directions. -/
structure Aut (V : VisibilityGraph.{u}) where
  toEquiv : V.Color ≃ V.Color
  sees_iff : ∀ {c d : V.Color}, V.Sees (toEquiv c) (toEquiv d) ↔ V.Sees c d

/-- On the complete graph, every permutation of jewels is an automorphism:
the veil structure is fully symmetric. -/
def completeAut {J : Type u} (σ : Equiv.Perm J) : (complete J).Aut where
  toEquiv := σ
  sees_iff := by
    intro c d
    simp only [complete, ne_eq]
    exact not_congr σ.apply_eq_iff_eq

end VisibilityGraph

/-! ## Construction: the well-founded tier -/

/-- Well-founded finite-branching syntax: an object of color `c` is a finite
family of color-`c` objects, or an opaque atom holding an object of a color
that `c` sees.  Establishing an initial-algebra universal property for a
chosen small-powerclass functor is a separate obligation. -/
inductive WfObject (V : VisibilityGraph.{u}) : V.Color → Type u where
  | set {c : V.Color} (n : ℕ) (members : Fin n → WfObject V c) : WfObject V c
  | atom {c d : V.Color} (sees : V.Sees c d) (payload : WfObject V d) :
      WfObject V c

namespace WfObject

variable {V : VisibilityGraph.{u}}

/-! ## Semantics: same-color membership -/

/-- Same-color membership: only `set` nodes have members.  An atom is a
reference, not a container. -/
inductive MemberOf {c : V.Color} :
    WfObject V c → WfObject V c → Prop where
  | intro {n : ℕ} (members : Fin n → WfObject V c) (i : Fin n) :
      MemberOf (members i) (.set n members)

/-! ## The veil: reference without containment -/

/-- Opacity: an atom exposes no members, whatever its payload holds. -/
theorem atom_memberless {c d : V.Color} (sees : V.Sees c d)
    (payload : WfObject V d) (x : WfObject V c) :
    ¬ MemberOf x (.atom sees payload) := by
  intro h
  cases h

/-- Reference retains identity: distinct payloads give distinct atoms. -/
theorem atom_injective {c d : V.Color} (sees : V.Sees c d) :
    Function.Injective (WfObject.atom (V := V) (c := c) sees) := by
  intro p q h
  injection h

/-- The veiled embedding: color `d`'s whole universe enters color `c` as
atoms, injectively.  Reflection-as-reference is cardinality-safe. -/
def atomEmbedding {c d : V.Color} (sees : V.Sees c d) :
    WfObject V d ↪ WfObject V c :=
  ⟨WfObject.atom sees, atom_injective sees⟩

/-- Transparent reflection is impossible: no universe injectively encodes
its own powerclass.  Paired with `atomEmbedding`, this is the veil theorem:
objects of another world may be *referenced* wholesale, but no world can
*contain* the predicates over itself. -/
theorem transparent_reflection_impossible (α : Type u) :
    ¬ ∃ encode : Set α → α, Function.Injective encode := by
  rintro ⟨encode, hinj⟩
  exact Function.cantor_injective encode hinj

/-! ## Local foundation -/

/-- Local foundation: at the well-founded tier, every color's own membership
relation is well-founded — for every visibility graph, the complete jewel
net included. -/
theorem memberOf_wellFounded (c : V.Color) :
    WellFounded (MemberOf (V := V) (c := c)) := by
  refine ⟨fun x => ?_⟩
  induction x with
  | set n members ih =>
    constructor
    intro y hy
    cases hy with
    | intro members i => exact ih i
  | atom sees payload _ih =>
    exact ⟨_, fun y hy => absurd hy (atom_memberless sees payload y)⟩

/-! ## Symmetry: automorphisms act on objects -/

section Relabel

variable (σ : V.Aut)

/-- Transport an object along a visibility-graph automorphism. -/
def relabel : {c : V.Color} → WfObject V c → WfObject V (σ.toEquiv c)
  | _, .set n members => .set n fun i => relabel (members i)
  | _, .atom sees payload => .atom (σ.sees_iff.mpr sees) (relabel payload)

/-- Membership is equivariant under automorphisms: the veil breaks
transparency, not symmetry. -/
theorem memberOf_relabel {c : V.Color} {x y : WfObject V c}
    (h : MemberOf x y) : MemberOf (relabel σ x) (relabel σ y) := by
  cases h with
  | intro members i =>
    show MemberOf (relabel σ (members i)) (relabel σ (.set _ members))
    simp only [relabel]
    exact .intro (fun j => relabel σ (members j)) i

/-- Automorphisms act injectively on objects. -/
theorem relabel_injective : ∀ {c : V.Color} (x y : WfObject V c),
    relabel σ x = relabel σ y → x = y := by
  intro c x
  induction x with
  | set n f ih =>
    intro y h
    cases y with
    | set m g =>
      simp only [relabel] at h
      injection h with _hc hnm hf
      subst hnm
      have hf' : (fun i => relabel σ (f i)) = fun i => relabel σ (g i) :=
        eq_of_heq hf
      exact congrArg (WfObject.set n)
        (funext fun i => ih i (g i) (congrFun hf' i))
    | atom sees q =>
      simp only [relabel] at h
      injection h
  | atom sees p ih =>
    intro y h
    cases y with
    | set m g =>
      simp only [relabel] at h
      injection h
    | atom sees₂ q =>
      simp only [relabel] at h
      injection h with _hc hd hpay
      have hd' := σ.toEquiv.injective hd
      subst hd'
      rw [ih q (eq_of_heq hpay)]

end Relabel

/-! ## Observation: what one jewel can see -/

/-- The shape a color can observe of its own objects: own-color set
structure transparently, foreign atoms only as a veiled color tag. -/
inductive View (Color : Type u) : Type u where
  | set (n : ℕ) (members : Fin n → View Color) : View Color
  | veiled (d : Color) : View Color

/-- The color-local observation: forget every payload behind the veil. -/
def blindView : {c : V.Color} → WfObject V c → View V.Color
  | _, .set n members => .set n fun i => blindView (members i)
  | _, .atom (d := d) _ _ => .veiled d

/-- No jewel is the net: whenever anything at all is visible through the
veil, the local observation is nonfaithful — two objects that differ in
another world's fully real structure have the same view here. -/
theorem blindView_nonfaithful {c d : V.Color} (sees : V.Sees c d) :
    ∃ x y : WfObject V c, x ≠ y ∧ blindView x = blindView y := by
  refine ⟨.atom sees (.set 0 Fin.elim0),
    .atom sees (.set 1 fun _ => .set 0 Fin.elim0), ?_, ?_⟩
  · intro h
    have hpay := atom_injective sees h
    injection hpay with hn _
    omega
  · simp only [blindView]

/-! ## A finite one-layer complete-visibility specimen -/

section IndraNet

open VisibilityGraph

variable {J : Type u} [DecidableEq J] [Fintype J]

/-- The bare jewel: an empty set at color `j`. -/
def jewelBase (j : J) : WfObject (complete J) j := .set 0 Fin.elim0

/-- A finite member family at jewel `j`: one opaque atom, carrying the bare
base object, for every other jewel. -/
noncomputable def indraMember (j : J)
    (i : Fin (Fintype.card {d : J // d ≠ j})) : WfObject (complete J) j :=
  .atom (Ne.symm ((Fintype.equivFin {d : J // d ≠ j}).symm i).2)
    (jewelBase ((Fintype.equivFin {d : J // d ≠ j}).symm i).1)

/-- The one-layer complete-visibility specimen at jewel `j`.  It contains an
opaque reference to the bare base object at every other color.  It is not a
coinductive solution in which every payload is recursively the other
jewel's complete view. -/
noncomputable def indraNet (j : J) : WfObject (complete J) j :=
  .set _ (indraMember j)

/-- Evaluating one net member at a decoded jewel. -/
theorem indraMember_eq (j : J) (s : {d' : J // d' ≠ j})
    (i : Fin (Fintype.card {d' : J // d' ≠ j}))
    (h : (Fintype.equivFin {d' : J // d' ≠ j}).symm i = s) :
    indraMember j i = .atom (Ne.symm s.2) (jewelBase s.1) := by
  subst h
  rfl

/-- Every finite observer's specimen references the bare base object at
every other color. -/
theorem indraNet_reflects_all (j d : J) (hjd : j ≠ d) :
    MemberOf (.atom (V := complete J) hjd (jewelBase d)) (indraNet j) := by
  have key := indraMember_eq j ⟨d, Ne.symm hjd⟩
    ((Fintype.equivFin {d' : J // d' ≠ j}) ⟨d, Ne.symm hjd⟩)
    (Equiv.symm_apply_apply _ _)
  have mem := MemberOf.intro (indraMember j)
    ((Fintype.equivFin {d' : J // d' ≠ j}) ⟨d, Ne.symm hjd⟩)
  rw [key] at mem
  simpa [indraNet] using mem

end IndraNet

/-! ## The immediate-support boundary -/

/-- Finite immediate complete visibility from a distinguished observer.
The `target` family need not be injective; `coversOther` is the substantive
all-to-all condition. -/
structure FiniteCompleteView (J : Type u) (center : J) where
  count : Nat
  target : Fin count → J
  coversOther : ∀ d, d ≠ center → ∃ i, target i = d

/-- A finite immediate view that covers every other observer forces the
observer type itself to be finite.  Thus literal finite-branching all-to-all
reflection cannot be silently extrapolated to an infinite observer class. -/
theorem finite_of_finiteCompleteView {J : Type u} {center : J}
    (view : FiniteCompleteView J center) : Finite J := by
  let enumerate : Fin (Nat.succ view.count) → J :=
    Fin.cases center view.target
  apply Finite.of_surjective enumerate
  intro d
  by_cases h : d = center
  · exact ⟨0, by simp [enumerate, h]⟩
  · obtain ⟨i, hi⟩ := view.coversOther d h
    exact ⟨i.succ, by simpa [enumerate] using hi⟩

/-- Negative canary: an infinite observer type has no finite immediate view
covering every other observer.  Infinite reflection therefore requires
small rather than necessarily finite support, staging, or indirect depth. -/
theorem no_finiteCompleteView_of_infinite {J : Type u} [Infinite J]
    (center : J) : ¬ Nonempty (FiniteCompleteView J center) := by
  rintro ⟨view⟩
  letI : Finite J := finite_of_finiteCompleteView view
  exact not_finite J

end WfObject

/-! ## Finitely branching cyclic presentations -/

/-- A finitely branching presentation of colored objects: each vertex is a
set-node listing same-color vertices, or an atom-node referencing one vertex
of a seen color.  The vertex type need not be finite.  Relating these systems
to a rational fixed point or final coalgebra requires separate bisimulation,
quotient, and universal-property theorems. -/
structure ColoredSystem (V : VisibilityGraph.{u}) where
  Vertex : Type
  color : Vertex → V.Color
  body : (v : Vertex) →
    List {w : Vertex // color w = color v} ⊕
      {w : Vertex // V.Sees (color v) (color w)}

namespace ColoredSystem

variable {V : VisibilityGraph.{u}} {S : ColoredSystem V}

/-- Same-color unfolding: `w` is a set-member of `v`.  Atom references do
not count — the veil stops local membership. -/
inductive LocalStep (S : ColoredSystem V) : S.Vertex → S.Vertex → Prop where
  | mk {v w : S.Vertex} (h : S.color w = S.color v)
      (ms : List {w' : S.Vertex // S.color w' = S.color v})
      (hbody : S.body v = .inl ms) (mem : ⟨w, h⟩ ∈ ms) : LocalStep S v w

/-- Color-blind unfolding: `w` occurs in the body of `v`, through the veil
or not. -/
inductive GlobalStep (S : ColoredSystem V) : S.Vertex → S.Vertex → Prop where
  | member {v w : S.Vertex} (h : S.color w = S.color v)
      (ms : List {w' : S.Vertex // S.color w' = S.color v})
      (hbody : S.body v = .inl ms) (mem : ⟨w, h⟩ ∈ ms) : GlobalStep S v w
  | reference {v : S.Vertex} (a : {w : S.Vertex // V.Sees (S.color v) (S.color w)})
      (hbody : S.body v = .inr a) : GlobalStep S v a.1

/-- Every local step is a global step. -/
theorem LocalStep.toGlobal {v w : S.Vertex} (h : S.LocalStep v w) :
    S.GlobalStep v w := by
  cases h with
  | mk h ms hbody mem => exact .member h ms hbody mem

/-! ### The minimal knot -/

/-- The minimal knot: two jewels, each of whose object is exactly an opaque
reference to the other. -/
def mutualKnot : ColoredSystem VisibilityGraph.pair where
  Vertex := Bool
  color := id
  body v := .inr ⟨!v, by
    cases v <;> simp [VisibilityGraph.pair, VisibilityGraph.complete]⟩

/-- Color-blind unfolding steps through the veil: each jewel steps to the
other. -/
theorem mutualKnot_global_step (v : Bool) :
    mutualKnot.GlobalStep v (!v) :=
  GlobalStep.reference (S := mutualKnot) (v := v)
    ⟨!v, by
      cases v <;>
        simp [mutualKnot, VisibilityGraph.pair, VisibilityGraph.complete]⟩
    rfl

/-- The global alternating cycle: through the veil, each jewel reaches
itself again. -/
theorem mutualKnot_global_cycle (v : Bool) :
    Relation.TransGen mutualKnot.GlobalStep v v := by
  have h₁ := mutualKnot_global_step v
  have h₂ := mutualKnot_global_step (!v)
  rw [Bool.not_not] at h₂
  exact .tail (.single h₁) h₂

/-- No same-color membership occurs in the knot at all. -/
theorem mutualKnot_local_step_empty (v w : Bool) :
    ¬ mutualKnot.LocalStep v w := by
  intro h
  cases h with
  | mk h ms hbody mem => cases v <;> simp [mutualKnot] at hbody

/-- Local foundation beside global non-well-foundedness: the knot's
same-color unfolding is well-founded even though its color-blind unfolding
cycles.  A globally knotted world need not injure any local foundation. -/
theorem mutualKnot_localFoundation : WellFounded mutualKnot.LocalStep :=
  ⟨fun v => ⟨v, fun w h => absurd h (mutualKnot_local_step_empty w v)⟩⟩

/-! ### Infinite depth with locally finite support -/

/-- A countable visibility graph in which each observer sees only its
successor. -/
def successorVisibility : VisibilityGraph where
  Color := Nat
  Sees c d := d = c + 1

/-- An open-ended reflection chain.  Every node has exactly one immediate
opaque reference, while reflection depth is unbounded. -/
def successorReflection : ColoredSystem successorVisibility where
  Vertex := Nat
  color := id
  body n := .inr ⟨n + 1, rfl⟩

/-- One unfolding step advances to the next observer. -/
theorem successorReflection_global_step (n : Nat) :
    successorReflection.GlobalStep n (n + 1) :=
  GlobalStep.reference (S := successorReflection) (v := n) ⟨n + 1, rfl⟩ rfl

/-- Every finite reflection depth is realized in the open-ended chain. -/
theorem successorReflection_reaches (start depth : Nat) :
    Relation.ReflTransGen successorReflection.GlobalStep
      start (start + depth) := by
  induction depth with
  | zero => simpa using
      (Relation.ReflTransGen.refl :
        Relation.ReflTransGen successorReflection.GlobalStep start start)
  | succ depth ih =>
      rw [Nat.add_succ]
      exact Relation.ReflTransGen.tail ih
        (by simpa [Nat.succ_eq_add_one] using
          successorReflection_global_step (start + depth))

/-- No same-color membership step is hidden in the reflection chain. -/
theorem successorReflection_local_step_empty (v w : Nat) :
    ¬ successorReflection.LocalStep v w := by
  intro h
  cases h with
  | mk h ms hbody mem => simp [successorReflection] at hbody

/-- The open-ended global chain coexists with well-founded local
membership. -/
theorem successorReflection_localFoundation :
    WellFounded successorReflection.LocalStep :=
  ⟨fun v => ⟨v, fun w h =>
    absurd h (successorReflection_local_step_empty w v)⟩⟩

end ColoredSystem

/-! ## Axiom audit -/

#print axioms WfObject.atom_injective
#print axioms WfObject.transparent_reflection_impossible
#print axioms WfObject.memberOf_wellFounded
#print axioms WfObject.relabel_injective
#print axioms WfObject.memberOf_relabel
#print axioms WfObject.blindView_nonfaithful
#print axioms WfObject.indraNet_reflects_all
#print axioms WfObject.finite_of_finiteCompleteView
#print axioms WfObject.no_finiteCompleteView_of_infinite
#print axioms ColoredSystem.mutualKnot_global_cycle
#print axioms ColoredSystem.mutualKnot_localFoundation
#print axioms ColoredSystem.successorReflection_reaches
#print axioms ColoredSystem.successorReflection_localFoundation

end Mettapedia.SetTheory.ColoredOpaqueUniverses
