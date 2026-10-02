import Mettapedia.GSLT.ProofPlans.Derivations
import Mettapedia.OSLF.Programs.Composition

/-!
# Plan composition is joint completion

Plans compose through what they share: role fillers such as a common ranking
function, bound or auxiliary construction, and obligations that mention them.
A **plan network** (`PlanNetwork`) has, for every component, fillers for its
roles and a plan whose goal depends on those fillers, and for every interface
an agreement relation between the fillers of its two components.

* A local completion of a component is a choice of fillers together with a
  completion of the component's plan at those fillers (`LocalCompletion`).  The
  network is a constraint network of partial programs (`toConstraintNetwork`),
  so its joint completions are global sections, and a joint completion exists
  exactly when the interface theory is consistent
  (`ConstraintNetwork.jointCompletion_iff_consistent`).
* **Joint completion is a global section of fillers with local completions**
  (`jointCompletion_nonempty_iff`): one filler assignment agreeing on every
  interface, at which every component's plan has a completion.
* **Invertible interfaces.**  When the local completions are presented as the
  views of a view system whose translations are the interfaces
  (`InvertibleInterfaces`), joint completions are exactly the global sections
  (`InvertibleInterfaces.jointCompletionEquivSections`).  On a connected index
  graph a joint completion exists exactly when some local completion at one
  component is fixed by every holonomy
  (`InvertibleInterfaces.jointCompletion_nonempty_iff_invariant`): the
  obstruction is a holonomy without fixed points.

**Control: pairwise-compatible plans that fail jointly** (`Triangle`).  Three
component plans in the two-bit calculus share the role fillers `x, y, z`; their
obligations are `Same(x, y)`, `Same(y, z)` and `Diff(z, x)`.  Every interface
can be satisfied on its own (`Triangle.pairwise`), and no joint completion
exists (`Triangle.no_joint`).  The local completions form the twisted
three-cycle, whose holonomy is negation (`Triangle.holonomy_is_negation`).  With
`Same(z, x)` in place of `Diff(z, x)`, the plans compose
(`Untwisted.joint`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProofPlans

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Scope
open Mettapedia.OSLF.Programs
open Mettapedia.OSLF.Programs.Composition

universe u v uI uF uE uW

variable {S : Type u} {C : MultiSortedClone.{u, v} S}

-- The filler and interface universes are independent parameters.
set_option linter.checkUnivs false in
/-- **A network of proof plans sharing role fillers.** -/
structure PlanNetwork (C : MultiSortedClone.{u, v} S) (Index : Type uI) where
  /-- The fillers of a component's roles. -/
  Filler : Index → Type uF
  /-- The goal of a component, depending on its fillers. -/
  goal : ∀ index, Filler index → S
  /-- The plan of a component at its fillers. -/
  plan : ∀ index (filler : Filler index), Plan C (goal index filler)
  /-- The interfaces between components. -/
  Edge : Index → Index → Type uE
  /-- Agreement of fillers along an interface. -/
  Agree : ∀ {i j : Index}, Edge i j → Filler i → Filler j → Prop

namespace PlanNetwork

variable {Index : Type uI} (network : PlanNetwork.{u, v, uI, uF, uE} C Index)

/-- **A local completion**: fillers for a component's roles and a completion of
its plan at those fillers. -/
def LocalCompletion (index : Index) : Type (max uF v) :=
  Σ filler : network.Filler index,
    { derivation : C.Hom [] (network.goal index filler) //
      derivation ∈ completions C (network.plan index filler) }

/-- The plan network as a constraint network of partial programs. -/
abbrev toConstraintNetwork : ConstraintNetwork.{uI, max uF v, uE} Index where
  Space := network.LocalCompletion
  Edge := network.Edge
  Compatible := fun edge first second => network.Agree edge first.1 second.1

/-- **Joint completion is a global section of fillers with local
completions.** -/
theorem jointCompletion_nonempty_iff :
    Nonempty network.toConstraintNetwork.JointCompletion ↔
      ∃ fillers : ∀ index, network.Filler index,
        (∀ {i j : Index} (edge : network.Edge i j), network.Agree edge (fillers i) (fillers j)) ∧
          Nonempty (∀ index, { derivation : C.Hom [] (network.goal index (fillers index)) //
            derivation ∈ completions C (network.plan index (fillers index)) }) := by
  constructor
  · rintro ⟨joint⟩
    exact ⟨fun index => (joint.1 index).1, fun edge => joint.2 edge,
      ⟨fun index => (joint.1 index).2⟩⟩
  · rintro ⟨fillers, agree, ⟨completion⟩⟩
    exact ⟨⟨fun index => ⟨fillers index, completion index⟩, fun edge => agree edge⟩⟩

/-- A joint completion makes every interface satisfiable on its own. -/
theorem pairwise_of_joint (joint : network.toConstraintNetwork.JointCompletion) :
    network.toConstraintNetwork.Pairwise :=
  network.toConstraintNetwork.pairwise_of_joint joint

/-- **Invertible interfaces**: the local completions presented as the views of
a view system, whose translations are the interfaces. -/
structure InvertibleInterfaces where
  /-- The view at a component. -/
  View : Index → Type uW
  /-- The local completions of a component, presented as its view. -/
  chart : ∀ index, network.LocalCompletion index ≃ View index
  /-- The translation along an interface. -/
  translate : ∀ {i j : Index}, network.Edge i j → View i ≃ View j
  /-- Agreement along an interface is its translation. -/
  agree_iff : ∀ {i j : Index} (edge : network.Edge i j) (first : network.LocalCompletion i)
    (second : network.LocalCompletion j),
    network.Agree edge first.1 second.1 ↔ translate edge (chart i first) = chart j second

namespace InvertibleInterfaces

variable {network}
variable (interfaces : InvertibleInterfaces.{u, v, uI, uF, uE, uW} network)

/-- The view system of the local completions. -/
abbrev viewSystem : ViewSystem.{uI, uE, uW} Index where
  View := interfaces.View
  Edge := network.Edge
  translate := interfaces.translate

/-- **With invertible interfaces, joint completions are global sections.** -/
def jointCompletionEquivSections :
    network.toConstraintNetwork.JointCompletion ≃ interfaces.viewSystem.Sections where
  toFun joint := ⟨fun index => interfaces.chart index (joint.1 index),
    fun edge => (interfaces.agree_iff edge _ _).mp (joint.2 edge)⟩
  invFun family := ⟨fun index => (interfaces.chart index).symm (family.1 index),
    fun {i j} edge => by
      refine (interfaces.agree_iff edge _ _).mpr ?_
      simp only [Equiv.apply_symm_apply]
      exact family.2 edge⟩
  left_inv joint := by
    apply Subtype.ext
    funext index
    exact (interfaces.chart index).symm_apply_apply (joint.1 index)
  right_inv family := by
    apply Subtype.ext
    funext index
    exact (interfaces.chart index).apply_symm_apply (family.1 index)

/-- **The obstruction is holonomy.**  On a connected index graph, a joint
completion exists exactly when some local completion at the root is fixed by
every holonomy. -/
theorem jointCompletion_nonempty_iff_invariant {root : Index}
    (connect : ∀ index : Index, Trunc (interfaces.viewSystem.Walk root index)) :
    Nonempty network.toConstraintNetwork.JointCompletion ↔
      ∃ view : interfaces.View root,
        ∀ loop : interfaces.viewSystem.Walk root root,
          interfaces.viewSystem.transport loop view = view := by
  rw [← nonempty_sections_iff connect]
  exact ⟨fun ⟨joint⟩ => ⟨interfaces.jointCompletionEquivSections joint⟩,
    fun ⟨family⟩ => ⟨interfaces.jointCompletionEquivSections.symm family⟩⟩

/-- **Gluing.**  Every local completion at the root extends to a joint
completion exactly when the holonomy is trivial. -/
theorem forall_extends_iff_trivialHolonomy {root : Index}
    (connect : ∀ index : Index, Trunc (interfaces.viewSystem.Walk root index)) :
    (∀ (view : interfaces.View root) (loop : interfaces.viewSystem.Walk root root),
        interfaces.viewSystem.transport loop view = view) ↔
      interfaces.viewSystem.TrivialHolonomy :=
  forall_invariant_iff_trivialHolonomy connect

end InvertibleInterfaces

end PlanNetwork

/-! ## Control: three plans sharing role fillers -/

namespace Triangle

open Fixture
open Mettapedia.GSLT.Scope.Twisted
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-- The obligation of each component: `Same(x, y)`, `Same(y, z)`, `Diff(z, x)`. -/
def goal : Vertex → Bool × Bool → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
  | .a, fillers => same fillers.1 fillers.2
  | .b, fillers => same fillers.1 fillers.2
  | .c, fillers => diff fillers.1 fillers.2

/-- Agreement on the shared role filler: the second filler of each component
is the first filler of the next. -/
def Agree : ∀ {i j : Vertex}, CycleEdge i j → Bool × Bool → Bool × Bool → Prop
  | _, _, .ab => fun first second => first.2 = second.1
  | _, _, .bc => fun first second => first.2 = second.1
  | _, _, .ca => fun first second => first.2 = second.1

/-- **The triangle of plans.**  Component `a` has fillers `(x, y)`, component `b`
has `(y, z)` and component `c` has `(z, x)`; each plan leaves its obligation
open. -/
def network : PlanNetwork (derivationClone sameDiff) Vertex where
  Filler _ := Bool × Bool
  goal := goal
  plan index fillers := Plan.assume _ (goal index fillers)
  Edge := CycleEdge
  Agree := Agree

/-- A completion of a component closes its obligation. -/
theorem derivable_of_completion {index : Vertex} {fillers : Bool × Bool}
    (completion : network.LocalCompletion index) (same : completion.1 = fillers) :
    Nonempty (Derivation sameDiffDefinition (goal index fillers)) := by
  subst same
  exact ⟨OpenDerivation.close completion.2.1⟩

/-- The local completion of a component at given fillers, when they are
realized. -/
def localAt (index : Vertex) (fillers : Bool × Bool)
    (derivation : Derivation sameDiffDefinition (goal index fillers)) :
    network.LocalCompletion index :=
  ⟨fillers, OpenDerivation.ofClosed derivation,
    mem_completions_assume (C := derivationClone sameDiff) (OpenDerivation.ofClosed derivation)⟩

/-- **Every interface is satisfiable on its own.** -/
theorem pairwise : network.toConstraintNetwork.Pairwise := by
  intro i j edge
  cases edge
  · exact ⟨localAt .a (true, true) (sameDerivation true),
      localAt .b (true, true) (sameDerivation true), rfl⟩
  · exact ⟨localAt .b (true, true) (sameDerivation true),
      localAt .c (true, false) (diffDerivation true), rfl⟩
  · exact ⟨localAt .c (true, false) (diffDerivation true),
      localAt .a (false, false) (sameDerivation false), rfl⟩

/-- The two fillers of a component are related by its obligation. -/
theorem fillers_of_local {index : Vertex} (completion : network.LocalCompletion index) :
    match index with
    | .a => completion.1.1 = completion.1.2
    | .b => completion.1.1 = completion.1.2
    | .c => completion.1.1 ≠ completion.1.2 := by
  have derivable := derivable_of_completion completion rfl
  cases index
  · exact (same_derivable_iff _ _).mp derivable
  · exact (same_derivable_iff _ _).mp derivable
  · exact (diff_derivable_iff _ _).mp derivable

/-- The chart of a component: its first filler. -/
def chart (index : Vertex) : network.LocalCompletion index ≃ Bool where
  toFun completion := completion.1.1
  invFun value := match index with
    | .a => localAt .a (value, value) (sameDerivation value)
    | .b => localAt .b (value, value) (sameDerivation value)
    | .c => localAt .c (value, !value) (diffDerivation value)
  left_inv completion := by
    obtain ⟨⟨first, second⟩, derivation, member⟩ := completion
    have related := fillers_of_local ⟨⟨first, second⟩, derivation, member⟩
    cases index <;> simp only at related
    · subst related
      have unique : OpenDerivation.ofClosed (sameDerivation first) = derivation :=
        (congrArg OpenDerivation.ofClosed (sameDiff_derivation_unique _ _)).trans
          (completion_eq_ofClosed derivation).symm
      subst unique
      rfl
    · subst related
      have unique : OpenDerivation.ofClosed (sameDerivation first) = derivation :=
        (congrArg OpenDerivation.ofClosed (sameDiff_derivation_unique _ _)).trans
          (completion_eq_ofClosed derivation).symm
      subst unique
      rfl
    · have equation : second = !first := by cases first <;> cases second <;> simp_all
      subst equation
      have unique : OpenDerivation.ofClosed (diffDerivation first) = derivation :=
        (congrArg OpenDerivation.ofClosed (sameDiff_derivation_unique _ _)).trans
          (completion_eq_ofClosed derivation).symm
      subst unique
      rfl
  right_inv value := by
    cases index <;> rfl

/-- **The interfaces are invertible**, with the translations of the twisted
three-cycle: identity, identity, negation. -/
def interfaces : network.InvertibleInterfaces where
  View _ := Bool
  chart := chart
  translate := twisted.translate
  agree_iff := by
    intro i j edge first second
    have firstRelated := fillers_of_local first
    have secondRelated := fillers_of_local second
    cases edge <;> simp only at firstRelated secondRelated
    · change first.1.2 = second.1.1 ↔ first.1.1 = second.1.1
      rw [firstRelated]
    · change first.1.2 = second.1.1 ↔ first.1.1 = second.1.1
      rw [firstRelated]
    · change first.1.2 = second.1.1 ↔ (!first.1.1) = second.1.1
      have negated : first.1.2 = !first.1.1 := by
        revert firstRelated
        cases first.1.1 <;> cases first.1.2 <;> simp
      rw [negated]

/-- The view system of the triangle is the twisted three-cycle. -/
theorem viewSystem_eq : interfaces.viewSystem = twisted := rfl

/-- **The holonomy around the triangle is negation.** -/
theorem holonomy_is_negation :
    interfaces.viewSystem.transport cycle true = false :=
  holonomy_moves

/-- **No joint completion**, although every interface is satisfiable. -/
theorem no_joint : IsEmpty network.toConstraintNetwork.JointCompletion :=
  ⟨fun joint => no_sections.false (interfaces.jointCompletionEquivSections joint)⟩

/-- **Pairwise-compatible plans fail jointly.** -/
theorem pairwise_not_joint :
    network.toConstraintNetwork.Pairwise ∧ IsEmpty network.toConstraintNetwork.JointCompletion :=
  ⟨pairwise, no_joint⟩

/-- Every component is reached from `a`. -/
def connect : ∀ index : Vertex, Trunc (interfaces.viewSystem.Walk Vertex.a index)
  | .a => Trunc.mk (.nil _)
  | .b => Trunc.mk (.forward CycleEdge.ab (.nil _))
  | .c => Trunc.mk (.forward CycleEdge.ab (.forward CycleEdge.bc (.nil _)))

/-- The same conclusion through the holonomy criterion: no filler at `a` is
fixed by the cycle. -/
theorem no_joint_by_holonomy : ¬ Nonempty network.toConstraintNetwork.JointCompletion := by
  rw [interfaces.jointCompletion_nonempty_iff_invariant connect]
  rintro ⟨view, fixed⟩
  have moved := fixed cycle
  cases view <;> exact Bool.noConfusion moved

end Triangle

/-! ## Positive control: the untwisted triangle composes -/

namespace Untwisted

open Fixture
open Mettapedia.GSLT.Scope.Twisted
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-- The same triangle with the obligation `Same(z, x)` at `c`. -/
def network : PlanNetwork (derivationClone sameDiff) Vertex where
  Filler _ := Bool × Bool
  goal _ fillers := same fillers.1 fillers.2
  plan _ fillers := Plan.assume _ (same fillers.1 fillers.2)
  Edge := CycleEdge
  Agree := Triangle.Agree

/-- **The untwisted plans compose**: all fillers `true`. -/
theorem joint : Nonempty network.toConstraintNetwork.JointCompletion :=
  ⟨⟨fun _ => ⟨(true, true), OpenDerivation.ofClosed (sameDerivation true),
      mem_completions_assume (C := derivationClone sameDiff) _⟩,
    fun edge => by cases edge <;> rfl⟩⟩

end Untwisted

end Mettapedia.GSLT.ProofPlans
