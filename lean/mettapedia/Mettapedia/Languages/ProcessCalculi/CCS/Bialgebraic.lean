import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSFinalBialgebra
import Mettapedia.Languages.ProcessCalculi.CCS.LanguageDef

/-!
# CCS by structural operational rules, and its bialgebraic semantics

The prefix-and-composition part of CCS (inaction, input and output prefixes,
and binary parallel composition) over a finite set of names is given by its
labelled rules:

* `a.p` has an `a` transition to `p`, and `ā.p` an `ā` transition to `p`;
* a parallel composition moves when either side moves, keeping the other side;
* on `τ`, complementary prefixes on one name synchronise.

These rules form a finite-branching GSOS law (`law`): premises test only the
transitions of the arguments, and conclusions are built from the variables.
Closed processes are therefore the initial compatible algebra, final action
trees the final one, and the semantics is the unique compatible map between
them (`FinalBialgebra.semantics`). Bisimilarity of closed processes is a
congruence for every operator (`FinalSemantics.constructor_kernel_congruent`;
for composition, `par_congr`).

The reduction presentation `ccsCalc` authors parallel composition as a bag,
so its static equivalence identifies `p | 0` with `p` and exchanges and
regroups components. In the labelled semantics these are not syntactic
identities but bisimilarities (`par_nil_bisimilar`, `par_comm_bisimilar`,
`par_assoc_bisimilar`). Consequently the semantics forgets program identity,
and no exact trinity has it as its program-to-space map (`semantics_not_exact`).
Exactness also fails on the other side: every transition shrinks a closed
process (`size_lt_of_mem_step`), so the behaviour of a silent loop is the
semantics of no closed process (`semantics_not_surjective`).

`toPattern` reads a closed process as a term of `ccsCalc`, each prefix a sum
of one summand, and each name a free name of the name sort, spelled by a given
map. The handshake reads as the authored handshake, and its one silent
transition is an authored reduction (`handshake_transitions_reduce`); the
two-name mismatch reads as the authored mismatch and is stuck in both.

**Control.** A constructor that tests its two arguments for syntactic
equality is outside the format. Bisimilarity is not preserved by it, so no
GSOS law has its transitions (`FinalBialgebra.EqualityTestControl`, beside the
other final-bialgebra controls).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.CCS.Bialgebraic

open _root_.CategoryTheory Mettapedia.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)
open Mettapedia.OSLF.FiniteBranching
open Classical

/-- The constructors: inaction, the two prefixes, and parallel composition. -/
inductive Operator (Name : Type) where
  | nil
  | input (name : Name)
  | output (name : Name)
  | par

/-- Visible actions on a name, and the silent synchronisation. -/
inductive Label (Name : Type) where
  | input (name : Name)
  | output (name : Name)
  | tau

variable (Name : Type)

/-- One sort of processes; prefixes have one argument, composition two. -/
abbrev signature : Signature.{0} where
  Srt := Unit
  Operator := fun _ => Operator Name
  Position := fun operator => match operator with
    | .nil => Empty
    | .input _ => Unit
    | .output _ => Unit
    | .par => Bool
  argument := fun _ _ => ()
  finite operator := by cases operator <;> infer_instance

abbrev actions : (signature Name).Srt → Type := fun _ => Label Name

variable {Name}

/-- Process terms with variables in `X`. -/
abbrev Process (X : (signature Name).Families) := (signature Name).Term X ()

def pure {X : (signature Name).Families} (value : X PUnit.unit ()) : Process X :=
  IndexedPolynomial.Free.pure (signature Name).polynomial value

def nil {X : (signature Name).Families} : Process X :=
  IndexedPolynomial.Free.node (signature Name).polynomial Operator.nil
    (fun position => position.elim)

def input {X : (signature Name).Families} (name : Name) (next : Process X) : Process X :=
  IndexedPolynomial.Free.node (signature Name).polynomial (Operator.input name) (fun _ => next)

def output {X : (signature Name).Families} (name : Name) (next : Process X) : Process X :=
  IndexedPolynomial.Free.node (signature Name).polynomial (Operator.output name) (fun _ => next)

def par {X : (signature Name).Families} (left right : Process X) : Process X :=
  IndexedPolynomial.Free.node (signature Name).polynomial Operator.par
    (fun position => if position then right else left)

/-- Relabelling variables acts componentwise on a composition. -/
theorem map_par {X Y : (signature Name).Families} (mapping : X ⟶ Y) (left right : Process X) :
    (signature Name).termMonad.map mapping PUnit.unit () (par left right) =
      par ((signature Name).termMonad.map mapping PUnit.unit () left)
        ((signature Name).termMonad.map mapping PUnit.unit () right) := by
  change IndexedPolynomial.Free.map (signature Name).polynomial (fun base sort => mapping base sort)
    PUnit.unit () (IndexedPolynomial.Free.node (signature Name).polynomial Operator.par _) = _
  rw [IndexedPolynomial.Free.map_node]
  apply congrArg (IndexedPolynomial.Free.node (signature Name).polynomial Operator.par)
  funext position
  cases position <;> rfl

/-- An argument of a constructor: its source and its complete behaviour. -/
abbrev Argument (X : (signature Name).Families) :=
  X PUnit.unit () × Behaviour (signature Name) (actions Name) X PUnit.unit ()

variable [Fintype Name]

/-- Synchronisations of two arguments: complementary actions on one name. -/
def syncSuccessors {X : (signature Name).Families} (left right : Argument X) :
    Finset (Process X) :=
  Finset.univ.biUnion fun name =>
    FinitePowerset.map (fun pair => par (pure pair.1) (pure pair.2))
      (left.2 (.input name) ×ˢ right.2 (.output name) ∪
        left.2 (.output name) ×ˢ right.2 (.input name))

/-- The rules of parallel composition. -/
def parSuccessors {X : (signature Name).Families} (left right : Argument X)
    (label : Label Name) : Finset (Process X) :=
  FinitePowerset.map (fun next => par (pure next) (pure right.1)) (left.2 label) ∪
    FinitePowerset.map (fun next => par (pure left.1) (pure next)) (right.2 label) ∪
    (match label with
      | .tau => syncSuccessors left right
      | _ => ∅)

/-- Relabel an argument's source and behaviour. -/
abbrev mapArgument {X Y : (signature Name).Families} (mapping : X ⟶ Y) (argument : Argument X) :
    Argument Y :=
  (mapping PUnit.unit () argument.1,
    Mettapedia.OSLF.FiniteBranching.behaviourMap (signature Name) (actions Name) mapping
      PUnit.unit () argument.2)

theorem parSuccessors_natural {X Y : (signature Name).Families} (mapping : X ⟶ Y)
    (left right : Argument X) (label : Label Name) :
    parSuccessors (mapArgument mapping left) (mapArgument mapping right) label =
      FinitePowerset.map ((signature Name).termMonad.map mapping PUnit.unit ())
        (parSuccessors left right label) := by
  ext term
  cases label <;>
    simp [parSuccessors, syncSuccessors, Mettapedia.OSLF.FiniteBranching.behaviourMap,
      map_par, pure, or_and_right, exists_or] <;>
    first
      | rfl
      | aesop

/-- The labelled rules of CCS as a natural law. -/
def law : Law (signature Name) (actions Name) where
  app X := fun base sort => match base, sort with
    | PUnit.unit, () => ↾(fun layer => match layer with
      | ⟨.nil, _⟩ => fun _ => ∅
      | ⟨.input name, child⟩ => fun label =>
          if label = .input name then {pure (child ()).1} else ∅
      | ⟨.output name, child⟩ => fun label =>
          if label = .output name then {pure (child ()).1} else ∅
      | ⟨.par, children⟩ => parSuccessors (children false) (children true))
  naturality {X Y} mapping := by
    funext base sort
    cases base
    cases sort
    apply ConcreteCategory.hom_ext
    intro layer
    rcases layer with ⟨operator, children⟩
    funext label
    cases operator with
    | nil =>
      exact (FinitePowerset.map_empty _).symm
    | input name =>
      change (if label = .input name then {pure (mapping PUnit.unit () (children ()).1)} else ∅) =
        FinitePowerset.map ((signature Name).termMonad.map mapping PUnit.unit ())
          (if label = .input name then {pure (children ()).1} else ∅)
      split_ifs
      · ext term
        simp only [Finset.mem_singleton, FinitePowerset.mem_map, exists_eq_left]
        exact eq_comm
      · exact (FinitePowerset.map_empty _).symm
    | output name =>
      change (if label = .output name then {pure (mapping PUnit.unit () (children ()).1)} else ∅) =
        FinitePowerset.map ((signature Name).termMonad.map mapping PUnit.unit ())
          (if label = .output name then {pure (children ()).1} else ∅)
      split_ifs
      · ext term
        simp only [Finset.mem_singleton, FinitePowerset.mem_map, exists_eq_left]
        exact eq_comm
      · exact (FinitePowerset.map_empty _).symm
    | par =>
      exact parSuccessors_natural mapping (children false) (children true) label

/-! ## Closed processes and their transitions -/

/-- Closed processes. -/
abbrev Closed (Name : Type) := (signature Name).ClosedTerm ()

/-- The operational transitions of closed processes, generated by `law`. -/
abbrev closedSystem (Name : Type) [Fintype Name] :
    Endofunctor.Coalgebra (behaviourFunctor (signature Name) (actions Name)) :=
  FinalBialgebra.closedOperational (law (Name := Name))

/-- The successors of a closed process under one label. -/
def step (process : Closed Name) (label : Label Name) : Finset (Closed Name) :=
  (closedSystem Name).str PUnit.unit () process label

omit [Fintype Name] in
theorem join_pure_par {X : (signature Name).Families} (left right : Process X) :
    IndexedPolynomial.Free.join (signature Name).polynomial
        (par (pure (X := (signature Name).polynomial.Free X) left) (pure right)) =
      par left right := by
  change IndexedPolynomial.Free.bind (signature Name).polynomial (fun _ _ tree => tree) PUnit.unit ()
    (IndexedPolynomial.Free.node (signature Name).polynomial Operator.par _) = _
  rw [IndexedPolynomial.Free.bind_node]
  apply congrArg (IndexedPolynomial.Free.node (signature Name).polynomial Operator.par)
  funext position
  cases position <;> rfl

theorem step_nil (label : Label Name) : step (nil : Closed Name) label = ∅ :=
  (Operational.coalgebra_node law _ Operator.nil _ label).trans (FinitePowerset.map_empty _)

theorem step_input (name : Name) (next : Closed Name) (label : Label Name) :
    step (input name next) label = if label = .input name then {next} else ∅ := by
  refine (Operational.coalgebra_node law _ (Operator.input name) (fun _ => next) label).trans ?_
  change FinitePowerset.map (IndexedPolynomial.Free.join (signature Name).polynomial)
      (if label = .input name then {pure next} else ∅) = _
  split_ifs
  · ext term
    simp only [FinitePowerset.mem_map, Finset.mem_singleton, exists_eq_left]
    exact eq_comm
  · exact FinitePowerset.map_empty _

theorem step_output (name : Name) (next : Closed Name) (label : Label Name) :
    step (output name next) label = if label = .output name then {next} else ∅ := by
  refine (Operational.coalgebra_node law _ (Operator.output name) (fun _ => next) label).trans ?_
  change FinitePowerset.map (IndexedPolynomial.Free.join (signature Name).polynomial)
      (if label = .output name then {pure next} else ∅) = _
  split_ifs
  · ext term
    simp only [FinitePowerset.mem_map, Finset.mem_singleton, exists_eq_left]
    exact eq_comm
  · exact FinitePowerset.map_empty _

/-- A complementary pair of transitions of the two components on one name. -/
def Synchronises (left right : Closed Name) (leftNext rightNext : Closed Name) : Prop :=
  ∃ name, (leftNext ∈ step left (.input name) ∧ rightNext ∈ step right (.output name)) ∨
    (leftNext ∈ step left (.output name) ∧ rightNext ∈ step right (.input name))

/-- The transitions of a closed composition are exactly those of its rules. -/
theorem mem_step_par (left right result : Closed Name) (label : Label Name) :
    result ∈ step (par left right) label ↔
      (∃ next ∈ step left label, result = par next right) ∨
        (∃ next ∈ step right label, result = par left next) ∨
          (label = .tau ∧ ∃ leftNext rightNext,
            Synchronises left right leftNext rightNext ∧ result = par leftNext rightNext) := by
  have readout : step (par left right) label =
      FinitePowerset.map (IndexedPolynomial.Free.join (signature Name).polynomial)
        (parSuccessors (left, step left) (right, step right) label) :=
    Operational.coalgebra_node law _ Operator.par _ label
  rw [readout]
  simp only [parSuccessors, FinitePowerset.mem_map, Finset.mem_union]
  constructor
  · rintro ⟨term, ((⟨next, member, rfl⟩ | ⟨next, member, rfl⟩) | synced), rfl⟩
    · exact Or.inl ⟨next, member, join_pure_par _ _⟩
    · exact Or.inr (Or.inl ⟨next, member, join_pure_par _ _⟩)
    · cases label with
      | tau =>
        simp only [syncSuccessors, Finset.mem_biUnion, Finset.mem_univ, true_and,
          FinitePowerset.mem_map, Finset.mem_union, Finset.mem_product] at synced
        obtain ⟨name, ⟨leftNext, rightNext⟩, members, rfl⟩ := synced
        exact Or.inr (Or.inr ⟨rfl, leftNext, rightNext, ⟨name, members⟩, join_pure_par _ _⟩)
      | input _ => exact absurd synced (Finset.notMem_empty _)
      | output _ => exact absurd synced (Finset.notMem_empty _)
  · rintro (⟨next, member, rfl⟩ | ⟨next, member, rfl⟩ |
        ⟨rfl, leftNext, rightNext, ⟨name, members⟩, rfl⟩)
    · exact ⟨_, Or.inl (Or.inl ⟨next, member, rfl⟩), join_pure_par _ _⟩
    · exact ⟨_, Or.inl (Or.inr ⟨next, member, rfl⟩), join_pure_par _ _⟩
    · refine ⟨par (pure leftNext) (pure rightNext), Or.inr ?_, join_pure_par _ _⟩
      simp only [syncSuccessors, Finset.mem_biUnion, Finset.mem_univ, true_and,
        FinitePowerset.mem_map, Finset.mem_union, Finset.mem_product]
      exact ⟨name, (leftNext, rightNext), members, rfl⟩

/-! ## Bisimilarity and the semantics -/

/-- Bisimilarity of closed processes under the CCS rules. -/
abbrev Bisimilar (first second : Closed Name) : Prop :=
  Bisimulation.Bisimilar (closedSystem Name) (closedSystem Name) PUnit.unit () first second

/-- A relation on closed processes whose related pairs match each other's
transitions, label by label, in both directions. -/
def IsBisimulation (relation : Closed Name → Closed Name → Prop) : Prop :=
  ∀ first second, relation first second → ∀ label,
    (∀ next ∈ step first label, ∃ other ∈ step second label, relation next other) ∧
      (∀ other ∈ step second label, ∃ next ∈ step first label, relation next other)

theorem bisimilar_of_isBisimulation {relation : Closed Name → Closed Name → Prop}
    (bisimulation : IsBisimulation relation) {first second : Closed Name}
    (held : relation first second) : Bisimilar first second := by
  refine ⟨fun base sort => match base, sort with | PUnit.unit, () => relation, ?_, held⟩
  intro base sort
  cases base
  cases sort
  exact bisimulation

/-- Two closed processes are bisimilar exactly when the unique compatible map
from closed syntax to final behaviour identifies them. -/
theorem bisimilar_iff_semantics (first second : Closed Name) :
    Bisimilar first second ↔
      (FinalBialgebra.semantics (law (Name := Name))).f.f PUnit.unit () first =
        (FinalBialgebra.semantics (law (Name := Name))).f.f PUnit.unit () second :=
  (FinalBialgebra.semantics_eq_iff_bisimilar law () first second).symm

/-- Bisimilarity is a congruence for parallel composition. -/
theorem par_congr {left left' right right' : Closed Name}
    (leftRelated : Bisimilar left left') (rightRelated : Bisimilar right right') :
    Bisimilar (par left right) (par left' right') := by
  have leftSame := (bisimilar_iff_semantics _ _).mp leftRelated
  have rightSame := (bisimilar_iff_semantics _ _).mp rightRelated
  rw [bisimilar_iff_semantics]
  rw [FinalBialgebra.semantics_readout] at leftSame rightSame ⊢
  apply FinalSemantics.constructor_kernel_congruent (lawEquiv _ _ law) _ PUnit.unit () Operator.par
  intro position
  cases position
  · exact leftSame
  · exact rightSame

/-- Inaction is a unit for composition up to bisimilarity. -/
theorem par_nil_bisimilar (process : Closed Name) : Bisimilar (par process nil) process := by
  refine bisimilar_of_isBisimulation (relation := fun first second => first = par second nil)
    ?_ rfl
  rintro _ second rfl label
  constructor
  · intro next member
    rcases (mem_step_par _ _ _ _).mp member with
      ⟨other, inStep, rfl⟩ | ⟨other, inStep, _⟩ | ⟨_, _, rightNext, ⟨name, synced⟩, _⟩
    · exact ⟨other, inStep, rfl⟩
    · rw [step_nil] at inStep
      exact absurd inStep (Finset.notMem_empty _)
    · rcases synced with ⟨_, inStep⟩ | ⟨_, inStep⟩ <;>
        · rw [step_nil] at inStep
          exact absurd inStep (Finset.notMem_empty _)
  · intro other member
    exact ⟨par other nil, (mem_step_par _ _ _ _).mpr (Or.inl ⟨other, member, rfl⟩), rfl⟩

theorem synchronises_symm {left right leftNext rightNext : Closed Name}
    (synced : Synchronises left right leftNext rightNext) :
    Synchronises right left rightNext leftNext := by
  obtain ⟨name, ⟨first, second⟩ | ⟨first, second⟩⟩ := synced
  · exact ⟨name, Or.inr ⟨second, first⟩⟩
  · exact ⟨name, Or.inl ⟨second, first⟩⟩

theorem step_par_swap {left right next : Closed Name} {label : Label Name}
    (member : next ∈ step (par left right) label) :
    ∃ other ∈ step (par right left) label,
      ∃ first second, next = par first second ∧ other = par second first := by
  rcases (mem_step_par _ _ _ _).mp member with
    ⟨leftNext, inStep, rfl⟩ | ⟨rightNext, inStep, rfl⟩ |
      ⟨rfl, leftNext, rightNext, synced, rfl⟩
  · exact ⟨par right leftNext, (mem_step_par _ _ _ _).mpr (Or.inr (Or.inl ⟨leftNext, inStep, rfl⟩)),
      leftNext, right, rfl, rfl⟩
  · exact ⟨par rightNext left, (mem_step_par _ _ _ _).mpr (Or.inl ⟨rightNext, inStep, rfl⟩),
      left, rightNext, rfl, rfl⟩
  · exact ⟨par rightNext leftNext, (mem_step_par _ _ _ _).mpr
      (Or.inr (Or.inr ⟨rfl, rightNext, leftNext, synchronises_symm synced, rfl⟩)),
      leftNext, rightNext, rfl, rfl⟩

/-- Composition is commutative up to bisimilarity. -/
theorem par_comm_bisimilar (left right : Closed Name) :
    Bisimilar (par left right) (par right left) := by
  refine bisimilar_of_isBisimulation
    (relation := fun first second => ∃ a b, first = par a b ∧ second = par b a) ?_
    ⟨left, right, rfl, rfl⟩
  rintro _ _ ⟨a, b, rfl, rfl⟩ label
  constructor
  · intro next member
    obtain ⟨other, inStep, c, d, rfl, rfl⟩ := step_par_swap member
    exact ⟨_, inStep, c, d, rfl, rfl⟩
  · intro other member
    obtain ⟨next, inStep, c, d, rfl, rfl⟩ := step_par_swap member
    exact ⟨_, inStep, d, c, rfl, rfl⟩

theorem step_par_left {left right next : Closed Name} {label : Label Name}
    (member : next ∈ step left label) : par next right ∈ step (par left right) label :=
  (mem_step_par _ _ _ _).mpr (Or.inl ⟨next, member, rfl⟩)

theorem step_par_right {left right next : Closed Name} {label : Label Name}
    (member : next ∈ step right label) : par left next ∈ step (par left right) label :=
  (mem_step_par _ _ _ _).mpr (Or.inr (Or.inl ⟨next, member, rfl⟩))

theorem step_par_sync {left right leftNext rightNext : Closed Name}
    (synced : Synchronises left right leftNext rightNext) :
    par leftNext rightNext ∈ step (par left right) .tau :=
  (mem_step_par _ _ _ _).mpr (Or.inr (Or.inr ⟨rfl, leftNext, rightNext, synced, rfl⟩))

/-- On a visible label a composition moves only by one of its components. -/
theorem step_par_visible {left right next : Closed Name} {label : Label Name}
    (visible : label ≠ .tau) (member : next ∈ step (par left right) label) :
    (∃ leftNext ∈ step left label, next = par leftNext right) ∨
      (∃ rightNext ∈ step right label, next = par left rightNext) := by
  rcases (mem_step_par _ _ _ _).mp member with moved | moved | ⟨silent, _⟩
  · exact Or.inl moved
  · exact Or.inr moved
  · exact absurd silent visible

/-- Every transition of `(a | b) | c` is matched by `a | (b | c)`. -/
theorem step_par_assoc {a b c next : Closed Name} {label : Label Name}
    (member : next ∈ step (par (par a b) c) label) :
    ∃ other ∈ step (par a (par b c)) label,
      ∃ x y z, next = par (par x y) z ∧ other = par x (par y z) := by
  rcases (mem_step_par _ _ _ _).mp member with
    ⟨inner, innerStep, rfl⟩ | ⟨cNext, cStep, rfl⟩ | ⟨rfl, inner, cNext, ⟨name, synced⟩, rfl⟩
  · rcases (mem_step_par _ _ _ _).mp innerStep with
      ⟨aNext, aStep, rfl⟩ | ⟨bNext, bStep, rfl⟩ | ⟨rfl, aNext, bNext, ⟨name, synced⟩, rfl⟩
    · exact ⟨_, step_par_left aStep, aNext, b, c, rfl, rfl⟩
    · exact ⟨_, step_par_right (step_par_left bStep), a, bNext, c, rfl, rfl⟩
    · refine ⟨par aNext (par bNext c), step_par_sync ⟨name, ?_⟩, aNext, bNext, c, rfl, rfl⟩
      rcases synced with ⟨aStep, bStep⟩ | ⟨aStep, bStep⟩
      · exact Or.inl ⟨aStep, step_par_left bStep⟩
      · exact Or.inr ⟨aStep, step_par_left bStep⟩
  · exact ⟨_, step_par_right (step_par_right cStep), a, b, cNext, rfl, rfl⟩
  · rcases synced with ⟨innerStep, cStep⟩ | ⟨innerStep, cStep⟩
    · rcases step_par_visible (by simp) innerStep with ⟨aNext, aStep, rfl⟩ | ⟨bNext, bStep, rfl⟩
      · exact ⟨_, step_par_sync ⟨name, Or.inl ⟨aStep, step_par_right cStep⟩⟩, aNext, b, cNext,
          rfl, rfl⟩
      · exact ⟨_, step_par_right (step_par_sync ⟨name, Or.inl ⟨bStep, cStep⟩⟩), a, bNext, cNext,
          rfl, rfl⟩
    · rcases step_par_visible (by simp) innerStep with ⟨aNext, aStep, rfl⟩ | ⟨bNext, bStep, rfl⟩
      · exact ⟨_, step_par_sync ⟨name, Or.inr ⟨aStep, step_par_right cStep⟩⟩, aNext, b, cNext,
          rfl, rfl⟩
      · exact ⟨_, step_par_right (step_par_sync ⟨name, Or.inr ⟨bStep, cStep⟩⟩), a, bNext, cNext,
          rfl, rfl⟩

/-- Every transition of `a | (b | c)` is matched by `(a | b) | c`. -/
theorem step_par_assoc_symm {a b c other : Closed Name} {label : Label Name}
    (member : other ∈ step (par a (par b c)) label) :
    ∃ next ∈ step (par (par a b) c) label,
      ∃ x y z, next = par (par x y) z ∧ other = par x (par y z) := by
  rcases (mem_step_par _ _ _ _).mp member with
    ⟨aNext, aStep, rfl⟩ | ⟨inner, innerStep, rfl⟩ | ⟨rfl, aNext, inner, ⟨name, synced⟩, rfl⟩
  · exact ⟨_, step_par_left (step_par_left aStep), aNext, b, c, rfl, rfl⟩
  · rcases (mem_step_par _ _ _ _).mp innerStep with
      ⟨bNext, bStep, rfl⟩ | ⟨cNext, cStep, rfl⟩ | ⟨rfl, bNext, cNext, ⟨name, synced⟩, rfl⟩
    · exact ⟨_, step_par_left (step_par_right bStep), a, bNext, c, rfl, rfl⟩
    · exact ⟨_, step_par_right cStep, a, b, cNext, rfl, rfl⟩
    · refine ⟨par (par a bNext) cNext, step_par_sync ⟨name, ?_⟩, a, bNext, cNext, rfl, rfl⟩
      rcases synced with ⟨bStep, cStep⟩ | ⟨bStep, cStep⟩
      · exact Or.inl ⟨step_par_right bStep, cStep⟩
      · exact Or.inr ⟨step_par_right bStep, cStep⟩
  · rcases synced with ⟨aStep, innerStep⟩ | ⟨aStep, innerStep⟩
    · rcases step_par_visible (by simp) innerStep with ⟨bNext, bStep, rfl⟩ | ⟨cNext, cStep, rfl⟩
      · exact ⟨_, step_par_left (step_par_sync ⟨name, Or.inl ⟨aStep, bStep⟩⟩), aNext, bNext, c,
          rfl, rfl⟩
      · exact ⟨_, step_par_sync ⟨name, Or.inl ⟨step_par_left aStep, cStep⟩⟩, aNext, b, cNext,
          rfl, rfl⟩
    · rcases step_par_visible (by simp) innerStep with ⟨bNext, bStep, rfl⟩ | ⟨cNext, cStep, rfl⟩
      · exact ⟨_, step_par_left (step_par_sync ⟨name, Or.inr ⟨aStep, bStep⟩⟩), aNext, bNext, c,
          rfl, rfl⟩
      · exact ⟨_, step_par_sync ⟨name, Or.inr ⟨step_par_left aStep, cStep⟩⟩, aNext, b, cNext,
          rfl, rfl⟩

/-- Composition is associative up to bisimilarity. -/
theorem par_assoc_bisimilar (a b c : Closed Name) :
    Bisimilar (par (par a b) c) (par a (par b c)) := by
  refine bisimilar_of_isBisimulation
    (relation := fun first second => ∃ x y z, first = par (par x y) z ∧ second = par x (par y z))
    ?_ ⟨a, b, c, rfl, rfl⟩
  rintro _ _ ⟨x, y, z, rfl, rfl⟩ label
  constructor
  · intro next member
    obtain ⟨other, inStep, related⟩ := step_par_assoc member
    exact ⟨other, inStep, related⟩
  · intro other member
    obtain ⟨next, inStep, related⟩ := step_par_assoc_symm member
    exact ⟨next, inStep, related⟩

omit [Fintype Name] in
/-- Inaction and an idle composition are different closed terms. -/
theorem nil_ne_par_nil : (par nil nil : Closed Name) ≠ nil := by
  intro equal
  cases equal

/-- The semantics forgets program identity: it identifies `0 | 0` with `0`.
Hence for every compatible model, no exact trinity has the semantics as its
program-to-space map. -/
theorem semantics_not_exact (model : FinalBialgebra.CompatibleAlgebra (law (Name := Name))) :
    ¬ ∃ isomorphism : (FinalBialgebra.trinity law model).program ≅
        (FinalBialgebra.trinity law model).space,
      isomorphism.hom = (FinalBialgebra.trinity law model).programToSpace :=
  FinalBialgebra.not_exact_of_bisimilar law model nil_ne_par_nil (par_nil_bisimilar nil)

/-! ## Behaviours that no closed process has -/

omit [Fintype Name] in
/-- Every closed process is built by one of the four constructors. -/
theorem closed_cases (process : Closed Name) :
    process = nil ∨ (∃ name next, process = input name next) ∨
      (∃ name next, process = output name next) ∨ ∃ left right, process = par left right := by
  rcases process with ⟨shape, children⟩
  rcases shape with hole | operator
  · exact hole.elim
  · cases operator with
    | nil =>
        refine Or.inl ?_
        change IndexedPolynomial.Fix.roll _ _ = IndexedPolynomial.Fix.roll _ _
        congr 1
        funext position
        exact position.elim
    | input name =>
        refine Or.inr (Or.inl ⟨name, children (), ?_⟩)
        change IndexedPolynomial.Fix.roll _ _ = IndexedPolynomial.Fix.roll _ _
        congr 1
    | output name =>
        refine Or.inr (Or.inr (Or.inl ⟨name, children (), ?_⟩))
        change IndexedPolynomial.Fix.roll _ _ = IndexedPolynomial.Fix.roll _ _
        congr 1
    | par =>
        refine Or.inr (Or.inr (Or.inr ⟨children false, children true, ?_⟩))
        change IndexedPolynomial.Fix.roll _ _ = IndexedPolynomial.Fix.roll _ _
        congr 1
        funext position
        cases position <;> rfl

/-- The number of constructors of a closed process. -/
def size (process : Closed Name) : Nat :=
  IndexedPolynomial.Free.fold (signature Name).polynomial
    (carrier := fun _ _ => Nat) (fun _ _ hole => PEmpty.elim hole)
    { act := fun _ _ layer => match layer with
        | ⟨.nil, _⟩ => 1
        | ⟨.input _, child⟩ => child () + 1
        | ⟨.output _, child⟩ => child () + 1
        | ⟨.par, children⟩ => children false + children true + 1 }
    PUnit.unit () process

omit [Fintype Name] in
theorem size_input (name : Name) (next : Closed Name) : size (input name next) = size next + 1 :=
  rfl

omit [Fintype Name] in
theorem size_output (name : Name) (next : Closed Name) : size (output name next) = size next + 1 :=
  rfl

omit [Fintype Name] in
theorem size_par (left right : Closed Name) : size (par left right) = size left + size right + 1 :=
  rfl

/-- Every transition of a closed process shrinks it. -/
theorem size_lt_of_mem_step {process next : Closed Name} {label : Label Name}
    (member : next ∈ step process label) : size next < size process := by
  induction h : size process using Nat.strong_induction_on generalizing process next label with
  | _ bound ih =>
    subst h
    rcases closed_cases process with rfl | ⟨name, rest, rfl⟩ | ⟨name, rest, rfl⟩ | ⟨left, right, rfl⟩
    · rw [step_nil] at member
      exact absurd member (Finset.notMem_empty _)
    · rw [step_input] at member
      split_ifs at member
      · rw [Finset.mem_singleton.mp member, size_input]
        exact Nat.lt_succ_self _
      · exact absurd member (Finset.notMem_empty _)
    · rw [step_output] at member
      split_ifs at member
      · rw [Finset.mem_singleton.mp member, size_output]
        exact Nat.lt_succ_self _
      · exact absurd member (Finset.notMem_empty _)
    · have leftSmaller : ∀ {next : Closed Name} {label : Label Name},
          next ∈ step left label → size next < size left := fun inStep =>
        ih (size left) (by rw [size_par]; omega) inStep rfl
      have rightSmaller : ∀ {next : Closed Name} {label : Label Name},
          next ∈ step right label → size next < size right := fun inStep =>
        ih (size right) (by rw [size_par]; omega) inStep rfl
      rw [size_par]
      rcases (mem_step_par _ _ _ _).mp member with
        ⟨leftNext, inStep, rfl⟩ | ⟨rightNext, inStep, rfl⟩ |
          ⟨_, leftNext, rightNext, ⟨name, synced⟩, rfl⟩
      · have := leftSmaller inStep
        rw [size_par]
        omega
      · have := rightSmaller inStep
        rw [size_par]
        omega
      · rcases synced with ⟨leftStep, rightStep⟩ | ⟨leftStep, rightStep⟩ <;>
        · have := leftSmaller leftStep
          have := rightSmaller rightStep
          rw [size_par]
          omega

/-- One state with a silent step to itself: a behaviour that never stops. -/
def silentLoop : Endofunctor.Coalgebra (behaviourFunctor (signature Name) (actions Name)) where
  V := fun _ _ => PUnit
  str := fun _ _ => ↾(fun state label => match label with
    | .tau => {state}
    | _ => ∅)

/-- No closed process is bisimilar to the silent loop. -/
theorem not_bisimilar_silentLoop (process : Closed Name) :
    ¬ Bisimulation.Bisimilar (closedSystem Name) (silentLoop (Name := Name)) PUnit.unit ()
      process PUnit.unit := by
  induction h : size process using Nat.strong_induction_on generalizing process with
  | _ bound ih =>
    subst h
    intro related
    have matching := Bisimulation.bisimilar_admitted (closedSystem Name) silentLoop
      PUnit.unit () process PUnit.unit related .tau
    obtain ⟨next, inStep, nextRelated⟩ := matching.2 PUnit.unit (Finset.mem_singleton_self _)
    exact ih (size next) (size_lt_of_mem_step inStep) next rfl nextRelated

/-- **The semantics is not surjective**: the final behaviour of the silent loop
is the semantics of no closed process. With `semantics_not_exact`, exactness
fails on both sides: distinct processes share a behaviour, and some behaviours
have no process. -/
theorem semantics_not_surjective :
    ¬ Function.Surjective ((FinalBialgebra.semantics (law (Name := Name))).f.f PUnit.unit ()) := by
  intro surjective
  obtain ⟨process, same⟩ := surjective
    ((FinalSemantics.observe (signature Name) (actions Name) silentLoop).f PUnit.unit () PUnit.unit)
  rw [FinalBialgebra.semantics_readout] at same
  exact not_bisimilar_silentLoop process
    ((FinalSemantics.kernel_iff_bisimilar (signature Name) (actions Name) (closedSystem Name)
      silentLoop PUnit.unit () process PUnit.unit).mp same)

/-! ## The handshake -/

/-- Complementary prefixes on one name synchronise silently, releasing both
continuations side by side. -/
theorem handshake_step (name : Name) :
    par (nil : Closed Name) (input name nil) ∈
      step (par (input name nil) (output name (input name nil))) .tau := by
  apply (mem_step_par _ _ _ _).mpr
  refine Or.inr (Or.inr ⟨rfl, nil, input name nil, ⟨name, Or.inl ⟨?_, ?_⟩⟩, rfl⟩)
  · rw [step_input]
    simp
  · rw [step_output]
    simp

/-- Prefixes on different names do not synchronise, and nothing else moves silently. -/
theorem mismatch_stuck {first second : Name} (different : first ≠ second) :
    step (par (input first nil) (output second nil) : Closed Name) .tau = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro next member
  rcases (mem_step_par _ _ _ _).mp member with
    ⟨_, inStep, _⟩ | ⟨_, inStep, _⟩ | ⟨_, _, _, ⟨name, synced⟩, _⟩
  · rw [step_input] at inStep
    simp at inStep
  · rw [step_output] at inStep
    simp at inStep
  · rcases synced with ⟨inLeft, inRight⟩ | ⟨inLeft, _⟩
    · rw [step_input] at inLeft
      rw [step_output] at inRight
      by_cases leftName : name = first
      · by_cases rightName : name = second
        · exact different (leftName.symm.trans rightName)
        · simp [rightName] at inRight
      · simp [leftName] at inLeft
    · rw [step_input] at inLeft
      simp at inLeft

/-! ## Agreement with the reduction presentation -/

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Read a closed process as a term of the authored presentation `ccsCalc`: each prefix becomes a sum of one summand,
`CAct` or `CCoAct` on the free name that `spell` gives, and a binary composition a two-element bag. -/
def toPattern {count : Nat} (spell : Fin count → String) (process : Closed (Fin count)) : Pattern :=
  IndexedPolynomial.Free.fold (signature (Fin count)).polynomial
    (carrier := fun _ _ => Pattern) (fun _ _ hole => PEmpty.elim hole)
    { act := fun _ _ layer => match layer with
        | ⟨.nil, _⟩ => Pattern.apply "CNil" []
        | ⟨.input name, child⟩ => CCS.sum [CCS.act (.fvar (spell name)) (child ())]
        | ⟨.output name, child⟩ => CCS.sum [CCS.coact (.fvar (spell name)) (child ())]
        | ⟨.par, children⟩ =>
            Pattern.collection .hashBag [children false, children true] none }
    PUnit.unit () process

/-- The handshake `a.0 | ā.(a.0)` over one name. -/
def handshakeProcess : Closed (Fin 1) := par (input 0 nil) (output 0 (input 0 nil))

theorem toPattern_handshake : toPattern (fun _ => "a") handshakeProcess = CCS.handshake := rfl

/-- The handshake has exactly one silent transition. -/
theorem step_handshake :
    step handshakeProcess .tau = {par nil (input 0 nil)} := by
  ext next
  rw [Finset.mem_singleton]
  constructor
  · intro member
    rcases (mem_step_par _ _ _ _).mp member with
      ⟨_, inStep, _⟩ | ⟨_, inStep, _⟩ | ⟨_, leftNext, rightNext, ⟨name, synced⟩, rfl⟩
    · rw [step_input] at inStep
      simp at inStep
    · rw [step_output] at inStep
      simp at inStep
    · rcases synced with ⟨inLeft, inRight⟩ | ⟨inLeft, _⟩
      · rw [step_input] at inLeft
        rw [step_output] at inRight
        have name_zero : name = 0 := Subsingleton.elim _ _
        subst name_zero
        simp only [if_true, Finset.mem_singleton] at inLeft inRight
        rw [inLeft, inRight]
      · rw [step_input] at inLeft
        simp at inLeft
  · rintro rfl
    exact handshake_step 0

/-- Every silent transition of the handshake is a reduction of the authored
presentation `ccsCalc`, read through `toPattern`. -/
theorem handshake_transitions_reduce :
    ∀ next ∈ step handshakeProcess .tau,
      Mettapedia.OSLF.MeTTaIL.ContextualStep.Step CCS.base CCS.ccsCalc
        (toPattern (fun _ => "a") handshakeProcess) (toPattern (fun _ => "a") next) := by
  intro next member
  rw [step_handshake, Finset.mem_singleton] at member
  subst member
  exact CCS.handshake_steps

/-- Prefixes on the two different names `a` and `b`. It reads as the authored `mismatch`, which `ccsCalc` cannot
rewrite (`CCS.mismatch_stuck`); here it has no silent transition (`mismatch_stuck`). -/
def mismatchProcess : Closed (Fin 2) := par (input 0 nil) (output 1 nil)

theorem toPattern_mismatch :
    toPattern (fun name => if name.val = 0 then "a" else "b") mismatchProcess = CCS.mismatch := rfl

end Mettapedia.Languages.ProcessCalculi.CCS.Bialgebraic
