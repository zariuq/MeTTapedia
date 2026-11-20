import Mathlib.Order.CompleteLattice.Basic
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Tree

/-!
# The stores of a tree of worlds as a spatial constraint system

A spatial constraint system (Knight, Palamidessi, Panangaden and Valencia) is a complete lattice of
constraints, ordered by information (the bottom is no information, the top is the inconsistent
constraint, the join is the conjunction), with a space function for each space `i`: a self-map that
keeps the bottom (S.1) and the joins (S.2). The assertion `s i c` reads "`c` holds in the space `i`".

Over any complete lattice of constraints, **the information placed along the paths of a tree of
worlds is a spatial constraint system**: an element gives the information at the root and at every
path below it; the space function of `i` places an element under the child `i` (`inSpace`).

* `inSpace_bot` (S.1), `inSpace_sup` (S.2), and `inSpace_iSup`: it keeps every join.
* `inSpace_top_ne_top`: **an inconsistency is confined**: the inconsistent information, placed in a
  space, is not the inconsistent information.
* `extensive_not_confined`, `inSpace_not_extensive`: the reading in which what a world holds is true
  of all (a space function that is extensive, `c ≤ s c`) confines nothing, `s ⊤ = ⊤`; the space
  functions of the tree are not extensive. With one knowledge for a whole state there is one space,
  whose space function is the identity, which is extensive.
* `fromSpace_inSpace`, `no_extrusion`: reading the space of `i` from outside (`fromSpace`) undoes
  placing, but the space functions are not onto, so no function is a right inverse of one: the
  extrusion of that theory (`s i (e i c) = c`) has no instance here. A publication is not an
  extrusion: it copies a row, with the knowledge of it, to another space.

The constraints of the step are the stores of equations at a frame, read through their solutions:
`models_known_iff` says that what a world of a tree knows (`Tree.known`) is the join of the stores
above it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds

open Interface (Frames)

universe u v w x uO uT uH uOcc uN

/-! ## Information placed along the paths of a tree -/

section Spaces

variable {C : Type u} [CompleteLattice C] {I : Type v} [DecidableEq I]

/-- **The space function of `i`**: the information `c`, placed under the child `i`. Nothing is said at
the root or under another child. -/
def inSpace (i : I) (c : List I → C) : List I → C
  | [] => ⊥
  | j :: rest => if j = i then c rest else ⊥

/-- **S.1**: an empty space amounts to nothing. -/
theorem inSpace_bot (i : I) : inSpace i (⊥ : List I → C) = ⊥ := by
  funext path
  cases path with
  | nil => rfl
  | cons j rest =>
      show (if j = i then (⊥ : List I → C) rest else ⊥) = ⊥
      split_ifs <;> rfl

/-- **S.2**: placing a join is the join of the placings. -/
theorem inSpace_sup (i : I) (c d : List I → C) : inSpace i (c ⊔ d) = inSpace i c ⊔ inSpace i d := by
  funext path
  cases path with
  | nil => exact (sup_idem (⊥ : C)).symm
  | cons j rest =>
      show (if j = i then (c ⊔ d) rest else ⊥) =
        (if j = i then c rest else ⊥) ⊔ (if j = i then d rest else ⊥)
      split_ifs
      · rfl
      · exact (sup_idem (⊥ : C)).symm

/-- Placing keeps every join. -/
theorem inSpace_iSup {K : Sort w} (i : I) (c : K → List I → C) :
    inSpace i (⨆ k, c k) = ⨆ k, inSpace i (c k) := by
  funext path
  rw [iSup_apply]
  cases path with
  | nil => exact iSup_bot.symm
  | cons j rest =>
      show (if j = i then (⨆ k, c k) rest else ⊥) = ⨆ k, (if j = i then c k rest else ⊥)
      split_ifs
      · exact iSup_apply
      · exact iSup_bot.symm

/-- **An inconsistency is confined to its space.** -/
theorem inSpace_top_ne_top [Nontrivial C] (i : I) : inSpace i (⊤ : List I → C) ≠ ⊤ := by
  intro same
  have atRoot : (⊥ : C) = ⊤ := congrFun same []
  exact bot_ne_top atRoot

/-- **An extensive space function confines nothing**: if what a space holds holds outside, the
inconsistent information in a space is the inconsistent information. -/
theorem extensive_not_confined {D : Type x} [CompleteLattice D] {s : D → D}
    (extensive : ∀ c, c ≤ s c) : s ⊤ = ⊤ :=
  top_le_iff.mp (extensive ⊤)

/-- The space functions of the tree are not extensive. -/
theorem inSpace_not_extensive [Nontrivial C] (i : I) : ¬ ∀ c : List I → C, c ≤ inSpace i c :=
  fun extensive => inSpace_top_ne_top i (extensive_not_confined extensive)

/-- **Reading the space of `i` from outside**: what is under the child `i`. -/
def fromSpace (i : I) (c : List I → C) : List I → C := fun path => c (i :: path)

/-- Reading undoes placing. -/
theorem fromSpace_inSpace (i : I) (c : List I → C) : fromSpace i (inSpace i c) = c := by
  funext path
  show (if i = i then c path else ⊥) = c path
  rw [if_pos rfl]

/-- **No extrusion**: information that says something at the root is the placing of nothing, so no
function is a right inverse of a space function. -/
theorem no_extrusion (i : I) (c : List I → C) (atRoot : c [] ≠ ⊥) :
    ¬ ∃ e : List I → C, inSpace i e = c := by
  rintro ⟨e, same⟩
  exact atRoot (congrFun same []).symm

end Spaces

/-! ## What a world knows is the join of the stores above it -/

section Known

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {O : Type uOcc} {N : Type uN}

/-- **What a world knows is the join of the stores above it**: a solution of what the world knows is a
solution of each store of its chain. -/
theorem models_known_iff (X : Frames Tm Hom) (t : Tree Tm O N) (n : N) {b : Obj}
    (σ : Hom t.frame b) :
    X.Models σ (t.known n) ↔ ∀ a ∈ t.chain n, X.Models σ (t.stores a) := by
  constructor
  · intro solved a inChain e inStore
    exact solved e (List.mem_flatMap.mpr ⟨a, inChain, inStore⟩)
  · intro each e member
    obtain ⟨a, inChain, inStore⟩ := List.mem_flatMap.mp member
    exact each a inChain e inStore

end Known

#print axioms inSpace_bot
#print axioms inSpace_sup
#print axioms inSpace_iSup
#print axioms inSpace_top_ne_top
#print axioms extensive_not_confined
#print axioms inSpace_not_extensive
#print axioms fromSpace_inSpace
#print axioms no_extrusion
#print axioms models_known_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds
