import Mettapedia.GSLT.Scope.Holonomy
import Mettapedia.GSLT.Logic.ObserverPresheafControls
import Mettapedia.OSLF.Programs.Completion

/-!
# Composing partial programs: joint completions and global sections

Components are composed along interfaces.  A **constraint network**
(`ConstraintNetwork`) has, for every component, the space of its local
completions and, for every interface between two components, a
compatibility relation between their local completions.  A **joint
completion** is a local completion of every component, compatible along
every interface: a global section (`JointCompletion`).

* **Joint completion is consistency** of the theory of the interfaces, read
  as sentences satisfied by global assignments (`jointCompletion_iff_consistent`);
  an interface between two different components is satisfiable on its own
  exactly when its one-sentence theory is consistent
  (`edgeCompatible_iff_consistent`).
* **Joint implies pairwise**: a joint completion makes every interface
  satisfiable on its own (`JointCompletion.edgeCompatible`).
* **Pairwise does not imply joint** (`Triangle.pairwise_not_joint`): three
  components with interfaces `a = b`, `b = c`, `c ≠ a` over booleans.  Every
  interface is satisfiable, and there is no joint completion.  This is W11's
  twisted cycle, whose holonomy is negation.
* Even without a cycle, interfaces that are not bijections can be pairwise but
  not jointly satisfiable (`Chain.pairwise_not_joint`).

**When interfaces are equivalences** the network is a W11 view system and joint
completions are its global sections (`ofViewSystem`,
`jointCompletionEquivSections`).  On a connected index graph:
* **joint completions are exactly the holonomy-invariant local completions at
  one component** (`sectionsEquivInvariant`), so a joint completion exists
  exactly when some local completion is fixed by every holonomy
  (`nonempty_sections_iff`);
* **every local completion extends to a joint completion exactly when the
  holonomy is trivial** (`forall_invariant_iff_trivialHolonomy`), which by W11's
  gluing theorem is exactly when the views glue.
So the obstruction to a joint completion is a holonomy without fixed points
(`Triangle.no_invariant`), and the obstruction to gluing is a non-trivial
holonomy: a network can have joint completions and still not glue
(`Swap.invariant_zero`, W11's `Swap.no_gluing`).

**Relational interfaces.**  For a cycle of relations, joint completions are
the fixed points of the composite relation (W11's `cycleSectionEquiv`); with
`a = b`, `b = c`, `c ≠ a` on three points, where `≠` is not a bijection,
there are none (`RelationalTriangle.no_joint`) although every relation is
inhabited (`RelationalTriangle.pairwise`).

**Two observational views** of one program, its `B`-stage and its `C`-stage,
that agree on a shared interface `A`, are always realised by one program
exactly when W5's amalgamation holds (`jointlyRealisable_iff_amalgamates`), the
Beck–Chevalley condition along forgetting.  Positive and negative instances:
`Independent.jointlyRealisable`, `Incompatible.not_jointlyRealisable`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Programs.Composition

open Mettapedia.GSLT.Scope

universe uI uV uE u

/-! ## Constraint networks -/

-- The component, interface and space universes are independent parameters.
set_option linter.checkUnivs false in
/-- **A constraint network of components**: a space of local completions for
every component and a compatibility relation along every interface. -/
structure ConstraintNetwork (Index : Type uI) where
  /-- The local completions of a component. -/
  Space : Index → Type uV
  /-- The interfaces between components. -/
  Edge : Index → Index → Type uE
  /-- Compatibility of local completions along an interface. -/
  Compatible : ∀ {i j : Index}, Edge i j → Space i → Space j → Prop

namespace ConstraintNetwork

variable {Index : Type uI} (C : ConstraintNetwork.{uI, uV, uE} Index)

/-- **A joint completion**: a local completion of every component, compatible
along every interface; a global section. -/
def JointCompletion : Type (max uI uV) :=
  {x : ∀ i, C.Space i // ∀ {i j : Index} (edge : C.Edge i j), C.Compatible edge (x i) (x j)}

/-- An interface is satisfiable on its own. -/
def EdgeCompatible {i j : Index} (edge : C.Edge i j) : Prop :=
  ∃ a b, C.Compatible edge a b

variable {C}

/-- **Joint implies pairwise.** -/
theorem JointCompletion.edgeCompatible (x : C.JointCompletion) {i j : Index}
    (edge : C.Edge i j) : C.EdgeCompatible edge :=
  ⟨x.1 i, x.1 j, x.2 edge⟩

variable (C)

/-- Pairwise satisfiability of every interface. -/
def Pairwise : Prop :=
  ∀ {i j : Index} (edge : C.Edge i j), C.EdgeCompatible edge

theorem pairwise_of_joint (x : C.JointCompletion) : C.Pairwise :=
  fun edge => x.edgeCompatible edge

/-- An interface, as a sentence about global assignments. -/
def Interface : Type (max uI uE) :=
  Σ i j : Index, C.Edge i j

/-- A global assignment satisfies an interface when its two local completions
are compatible. -/
def InterfaceSat (x : ∀ i, C.Space i) (edge : C.Interface) : Prop :=
  C.Compatible edge.2.2 (x edge.1) (x edge.2.1)

/-- **Joint completion is consistency of the interface theory.** -/
theorem jointCompletion_iff_consistent :
    Nonempty C.JointCompletion ↔ Completion.Consistent C.InterfaceSat Set.univ := by
  constructor
  · rintro ⟨x⟩
    exact ⟨x.1, fun edge _ => x.2 edge.2.2⟩
  · rintro ⟨x, model⟩
    exact ⟨⟨x, fun {i j} edge => model (Set.mem_univ (⟨i, j, edge⟩ : C.Interface))⟩⟩

/-- **An interface between two different components is satisfiable on its
own exactly when its one-sentence theory is consistent**, given a local
completion of every component and decidable equality of components. -/
theorem edgeCompatible_iff_consistent [DecidableEq Index] (default : ∀ i, C.Space i)
    {i j : Index} (different : i ≠ j) (edge : C.Edge i j) :
    C.EdgeCompatible edge ↔ Completion.Consistent C.InterfaceSat {⟨i, j, edge⟩} := by
  constructor
  · rintro ⟨a, b, compatible⟩
    refine ⟨Function.update (Function.update default i a) j b, fun sentence member => ?_⟩
    have isEdge : sentence = ⟨i, j, edge⟩ := member
    subst isEdge
    show C.Compatible edge (Function.update (Function.update default i a) j b i)
      (Function.update (Function.update default i a) j b j)
    rw [Function.update_self, Function.update_of_ne different, Function.update_self]
    exact compatible
  · rintro ⟨x, model⟩
    exact ⟨x i, x j, model (show (⟨i, j, edge⟩ : C.Interface) ∈ ({⟨i, j, edge⟩} : Set C.Interface)
      from rfl)⟩

/-- The network whose interfaces are the translations of a view system. -/
def ofViewSystem (S : ViewSystem.{uI, uE, uV} Index) : ConstraintNetwork.{uI, uV, uE} Index where
  Space := S.View
  Edge := S.Edge
  Compatible edge a b := S.translate edge a = b

/-- **Joint completions of a view system are its global sections.** -/
def jointCompletionEquivSections (S : ViewSystem.{uI, uE, uV} Index) :
    (ofViewSystem S).JointCompletion ≃ S.Sections where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end ConstraintNetwork

/-! ## Holonomy-invariant completions -/

section Invariant

open ViewSystem

variable {Index : Type uI} {S : ViewSystem.{uI, uE, uV} Index} {root : Index}

variable (S root) in
/-- The local completions at `root` fixed by every holonomy. -/
def Invariant : Type uV :=
  {v : S.View root // ∀ loop : S.Walk root root, S.transport loop v = v}

/-- Transport of an invariant value does not depend on the walk. -/
theorem Invariant.transport_eq (v : Invariant S root) {j : Index} (first second : S.Walk root j) :
    S.transport first v.1 = S.transport second v.1 := by
  have fixed := v.2 (first.append second.reverse)
  rw [transport_append] at fixed
  calc S.transport first v.1
      = S.transport second (S.transport second.reverse (S.transport first v.1)) :=
        (transport_reverse_right second _).symm
    _ = S.transport second v.1 := by rw [fixed]

/-- Extend an invariant value along any walk from the root. -/
def Invariant.extend (connect : ∀ j : Index, Trunc (S.Walk root j)) (v : Invariant S root)
    (j : Index) : S.View j :=
  Trunc.lift (fun walk => S.transport walk v.1) (fun first second => v.transport_eq first second)
    (connect j)

theorem Invariant.extend_eq (connect : ∀ j : Index, Trunc (S.Walk root j)) (v : Invariant S root)
    {j : Index} (walk : S.Walk root j) : v.extend connect j = S.transport walk v.1 := by
  change Trunc.lift _ _ (connect j) = _
  induction connect j using Trunc.induction_on with
  | h other => exact v.transport_eq other walk

/-- **Joint completions are the holonomy-invariant local completions at the
root**, on a connected index graph. -/
def sectionsEquivInvariant (connect : ∀ j : Index, Trunc (S.Walk root j)) :
    S.Sections ≃ Invariant S root where
  toFun family := ⟨family.1 root, fun loop => family.transport loop⟩
  invFun v := ⟨v.extend connect, fun {i j} edge => by
    refine Trunc.induction_on (connect i)
      (β := fun _ => S.translate edge (v.extend connect i) = v.extend connect j) fun walk => ?_
    rw [v.extend_eq connect walk, v.extend_eq connect (walk.append (.forward edge (.nil j))),
      transport_append]
    rfl⟩
  left_inv family := by
    apply Subtype.ext
    funext j
    refine Trunc.induction_on (connect j)
      (β := fun _ => (Invariant.extend connect ⟨family.1 root, fun loop => family.transport loop⟩ j)
        = family.1 j) fun walk => ?_
    exact (Invariant.extend_eq connect _ walk).trans (family.transport walk)
  right_inv v := Subtype.ext (v.extend_eq connect (.nil root))

/-- **A joint completion exists exactly when some local completion at the root
is fixed by every holonomy.** -/
theorem nonempty_sections_iff (connect : ∀ j : Index, Trunc (S.Walk root j)) :
    Nonempty S.Sections ↔ ∃ v : S.View root, ∀ loop : S.Walk root root, S.transport loop v = v :=
  ⟨fun ⟨family⟩ => ⟨_, (sectionsEquivInvariant connect family).2⟩,
    fun ⟨v, fixed⟩ => ⟨(sectionsEquivInvariant connect).symm ⟨v, fixed⟩⟩⟩

/-- **Every local completion at the root extends to a joint completion exactly
when the holonomy is trivial**, that is, exactly when the views glue. -/
theorem forall_invariant_iff_trivialHolonomy (connect : ∀ j : Index, Trunc (S.Walk root j)) :
    (∀ (v : S.View root) (loop : S.Walk root root), S.transport loop v = v) ↔
      S.TrivialHolonomy := by
  constructor
  · intro invariant i loop value
    refine Trunc.induction_on (connect i) (β := fun _ => S.transport loop value = value) ?_
    intro walk
    have fixed := invariant (S.transport walk.reverse value)
      (walk.append (loop.append walk.reverse))
    rw [transport_append, transport_append, transport_reverse_right] at fixed
    calc S.transport loop value
        = S.transport walk (S.transport walk.reverse (S.transport loop value)) :=
          (transport_reverse_right walk _).symm
      _ = S.transport walk (S.transport walk.reverse value) := by rw [fixed]
      _ = value := transport_reverse_right walk value
  · intro trivial v loop
    exact trivial loop v

/-- The same statement through W11's gluing theorem. -/
theorem forall_invariant_iff_gluing (connect : ∀ j : Index, Trunc (S.Walk root j)) :
    (∀ (v : S.View root) (loop : S.Walk root root), S.transport loop v = v) ↔
      Nonempty S.Gluing :=
  (forall_invariant_iff_trivialHolonomy connect).trans (nonempty_gluing_iff connect).symm

end Invariant

/-! ## Controls -/

/-! ### `a = b`, `b = c`, `c ≠ a` -/

namespace Triangle

open ConstraintNetwork Twisted

/-- The three components of W11's twisted cycle. -/
abbrev network : ConstraintNetwork.{0, 0, 0} Vertex :=
  ofViewSystem twisted

/-- Every component is reached from `a`. -/
def connect : ∀ j : Vertex, Trunc (twisted.Walk Vertex.a j)
  | .a => Trunc.mk (.nil _)
  | .b => Trunc.mk (.forward CycleEdge.ab (.nil _))
  | .c => Trunc.mk (.forward CycleEdge.ab (.forward CycleEdge.bc (.nil _)))

/-- **Every interface is satisfiable on its own.** -/
theorem pairwise : network.Pairwise := by
  intro i j edge
  cases edge
  · exact ⟨true, true, rfl⟩
  · exact ⟨true, true, rfl⟩
  · exact ⟨true, false, rfl⟩

/-- **There is no joint completion.** -/
theorem no_joint : IsEmpty network.JointCompletion :=
  ⟨fun x => no_sections.false (jointCompletionEquivSections twisted x)⟩

/-- **Pairwise does not imply joint.** -/
theorem pairwise_not_joint : network.Pairwise ∧ IsEmpty network.JointCompletion :=
  ⟨pairwise, no_joint⟩

/-- The obstruction is a holonomy without fixed points. -/
theorem no_invariant : ¬ ∃ v : Bool, ∀ loop : twisted.Walk Vertex.a Vertex.a,
    twisted.transport loop v = v := by
  rintro ⟨v, fixed⟩
  have moved := fixed cycle
  cases v <;> exact Bool.noConfusion moved

/-- The same conclusion from the invariant-section theorem. -/
theorem no_sections' : ¬ Nonempty twisted.Sections := by
  rw [nonempty_sections_iff connect]
  exact no_invariant

end Triangle

namespace Swap

open ConstraintNetwork Twisted Mettapedia.GSLT.Scope.Swap

/-- Every component is reached from `a`. -/
def connect : ∀ j : Vertex, Trunc (swapped.Walk Vertex.a j)
  | .a => Trunc.mk (.nil _)
  | .b => Trunc.mk (.forward CycleEdge.ab (.nil _))
  | .c => Trunc.mk (.forward CycleEdge.ab (.forward CycleEdge.bc (.nil _)))

/-- `0` is fixed by every holonomy of the swapped cycle. -/
theorem invariant_zero : ∀ loop : swapped.Walk Vertex.a Vertex.a,
    swapped.transport loop (0 : Fin 3) = (0 : Fin 3) := by
  intro loop
  have section_transport := fixedSection.transport loop
  exact section_transport

/-- **A joint completion exists without gluing**: the holonomy has a fixed
point, and is not trivial. -/
theorem joint_without_gluing : Nonempty swapped.Sections ∧ ¬ Nonempty swapped.Gluing :=
  ⟨(nonempty_sections_iff connect).mpr ⟨(0 : Fin 3), invariant_zero⟩, no_gluing⟩

end Swap

/-! ### Non-bijective interfaces along a chain -/

namespace Chain

/-- The two interfaces of a chain `a — b — c`. -/
inductive Edge : Twisted.Vertex → Twisted.Vertex → Type where
  | ab : Edge .a .b
  | bc : Edge .b .c

/-- `a — b` forces `b = 0`, `b — c` forces `b = 1`. -/
def network : ConstraintNetwork.{0, 0, 0} Twisted.Vertex where
  Space _ := Bool
  Edge := Edge
  Compatible
    | .ab => fun _ b => b = false
    | .bc => fun b _ => b = true

/-- **Pairwise does not imply joint, without any cycle**, once interfaces are
not bijections. -/
theorem pairwise_not_joint : network.Pairwise ∧ IsEmpty network.JointCompletion := by
  refine ⟨fun edge => ?_, ⟨fun x => ?_⟩⟩
  · cases edge
    · exact ⟨true, false, rfl⟩
    · exact ⟨true, true, rfl⟩
  · have first : x.1 .b = false := x.2 Edge.ab
    have second : x.1 .b = true := x.2 Edge.bc
    rw [first] at second
    exact Bool.noConfusion second

end Chain

/-! ### A relational cycle -/

namespace RelationalTriangle

open Mettapedia.GSLT.LooseRelationEquipment

/-- Equality on three points, as a proof-relevant relation. -/
def equal : Loose (Fin 3) (Fin 3) := fun a b => EqWitness a b

/-- Inequality on three points: a relation that is not a bijection. -/
def unequal : Loose (Fin 3) (Fin 3) := fun a b => ULift.{0} (PLift (a ≠ b))

/-- **Every relation is inhabited.** -/
theorem pairwise : Nonempty (equal 0 0) ∧ Nonempty (unequal 0 1) :=
  ⟨⟨⟨⟨rfl⟩⟩⟩, ⟨⟨⟨by decide⟩⟩⟩⟩

/-- **The cycle `a = b`, `b = c`, `c ≠ a` has no global section**: its
composite relation has no fixed point. -/
theorem no_joint : IsEmpty (CycleSection equal equal unequal) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨a, c, ⟨b, ⟨⟨ab⟩⟩, ⟨⟨bc⟩⟩⟩, ⟨⟨ca⟩⟩⟩ := cycleSectionEquiv equal equal unequal x
  exact ca (bc ▸ ab ▸ rfl)

end RelationalTriangle

/-! ## Two observational views of one program -/

section Views

open Mettapedia.GSLT
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.AdmissibleContextCongruence.AdmissibleClass

variable {S : GSLT} {rules : ContextualRules S}
variable (observations : ContextualRules.Observations S)

/-- Views of a program through the observers of `B` and of `C`, agreeing on
the shared interface `A`, are **jointly realisable** when one program has
both views. -/
def JointlyRealisable {A B C : AdmissibleClass rules} (hAB : A ≤ B) (hAC : A ≤ C) : Prop :=
  ∀ (x : Stage observations B) (y : Stage observations C),
    restrict observations hAB x = restrict observations hAC y →
      ∃ P : S.Term, stageClass observations B P = x ∧ stageClass observations C P = y

/-- **Joint realisability of agreeing views is W5's amalgamation.** -/
theorem jointlyRealisable_iff_amalgamates {A B C : AdmissibleClass rules} (hAB : A ≤ B)
    (hAC : A ≤ C) :
    JointlyRealisable observations hAB hAC ↔ Amalgamates observations A B C := by
  constructor
  · intro realisable left right related
    have agree : restrict observations hAB (stageClass observations B left) =
        restrict observations hAC (stageClass observations C right) := by
      rw [restrict_stageClass, restrict_stageClass]
      exact (stageClass_eq_iff observations A left right).mpr related
    obtain ⟨P, hB, hC⟩ := realisable _ _ agree
    exact ⟨P, (stageClass_eq_iff observations B P left).mp hB,
      (stageClass_eq_iff observations C P right).mp hC⟩
  · intro amalgamates x y agree
    induction x using Quotient.inductionOn with
    | _ left =>
      induction y using Quotient.inductionOn with
      | _ right =>
        have related : A.RelEquiv observations left right := by
          apply (stageClass_eq_iff observations A left right).mp
          rw [← restrict_stageClass observations hAB, ← restrict_stageClass observations hAC]
          exact agree
        obtain ⟨glued, hB, hC⟩ := amalgamates related
        exact ⟨glued, (stageClass_eq_iff observations B glued left).mpr hB,
          (stageClass_eq_iff observations C glued right).mpr hC⟩

end Views

namespace Views

open Mettapedia.GSLT.AdmissibleContextCongruence.AdmissibleClass
open Mettapedia.GSLT.AdmissibleContextCongruence.ObserverPresheafControls
open Mettapedia.GSLT.AdmissibleContextCongruence.ObserverPresheafControls.InertFunctions

/-- **Positive**: in W5's independent-observers fixture, agreeing views are
always realised by one program. -/
theorem Independent.jointlyRealisable :
    JointlyRealisable (hits Independent.Pt .yes) Independent.A_le_B Independent.A_le_C :=
  (jointlyRealisable_iff_amalgamates _ _ _).mpr Independent.amalgamates

/-- **Negative**: in W5's incompatible-observers fixture, some agreeing views
are realised by no program. -/
theorem Incompatible.not_jointlyRealisable :
    ¬ JointlyRealisable (hits Incompatible.Pt .yes) Incompatible.A_le_B Incompatible.A_le_C :=
  fun realisable =>
    Incompatible.not_amalgamates ((jointlyRealisable_iff_amalgamates _ _ _).mp realisable)

end Views

end Mettapedia.OSLF.Programs.Composition
