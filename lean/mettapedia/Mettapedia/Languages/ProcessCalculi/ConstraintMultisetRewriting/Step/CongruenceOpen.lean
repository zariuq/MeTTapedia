import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CongruenceParallel

/-!
# Open bisimilarity: a context-labelled step and congruence at the ports

The experimenter of `RaceExperiments` adds atoms at a program's ports, one at a time, between
firings; open bisimilarity is the bisimilarity of that intervened step (`OpenBisimilar`).

## Composition with port atoms

* **Adding a set of atoms** (`addAll`) is parallel composition with a context of atoms and no
  knowledge (`tensor_ports`).
* **Open bisimilarity is a congruence for contexts of port atoms** (`OpenBisimilar.tensor_ports`):
  open-bisimilar configurations stay open bisimilar in parallel with any finite set of port atoms,
  disjoint or not. The experimenter could have added them (`OpenBisimilar.add_port`,
  `OpenBisimilar.add_ports`).
* **Closed bisimilarity is open bisimilarity with no ports** (`openBisimilar_noPorts_iff`), so a
  context atom outside the ports breaks the congruence (`Triggered.outside_ports_not_congruence`,
  from `Triggered.not_congruence`). With the triggers as ports, the two continuations are already
  told apart (`Triggered.continuations_not_openBisimilar`).

## The context-labelled step

Under the label `(ℓ, M)`, with `M` a finite set of ports, a configuration moves when, with the atoms
of `M` added, it fires a firing the program offers under `ℓ` (`ContextMoves`).

* **Its bisimilarity is open bisimilarity, for every program** (`contextBisimilar_iff_openBisimilar`).
  A one-atom intervention followed by a firing is one context move; conversely the context moves
  under the empty context are the program's moves, and context bisimilarity is closed under adding
  ports (`ContextBisimilar.add_ports`).
* **It is a congruence for contexts of port atoms** (`ContextBisimilar.tensor_ports`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing)
open Mettapedia.GSLT.HennessyMilner (System)

universe uT uS uO uL

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}

/-! ## Adding a set of atoms -/

/-- **Add every atom of a finite set**; the knowledge is unchanged. -/
def addAll (C : Configuration T O) (M : Finset O) : Configuration T O := ⟨C.equations, C.present ∪ M⟩

theorem addAll_empty (C : Configuration T O) : addAll C ∅ = C := by
  show (⟨C.equations, C.present ∪ ∅⟩ : Configuration T O) = C
  rw [Finset.union_empty]

theorem addAll_insert (C : Configuration T O) (o : O) (M : Finset O) :
    addAll C (insert o M) = addAtom (addAll C M) o := by
  show (⟨C.equations, C.present ∪ insert o M⟩ : Configuration T O) =
    ⟨C.equations, insert o (C.present ∪ M)⟩
  rw [Finset.union_insert]

theorem addAll_addAll (C : Configuration T O) (N M : Finset O) :
    addAll (addAll C N) M = addAll C (N ∪ M) := by
  show (⟨C.equations, C.present ∪ N ∪ M⟩ : Configuration T O) = ⟨C.equations, C.present ∪ (N ∪ M)⟩
  rw [Finset.union_assoc]

theorem addAll_singleton (C : Configuration T O) (o : O) : addAll C {o} = addAtom C o := by
  show (⟨C.equations, C.present ∪ {o}⟩ : Configuration T O) = ⟨C.equations, insert o C.present⟩
  rw [Finset.insert_eq, Finset.union_comm]

/-- **Adding atoms is composition with a context of atoms and no knowledge.** -/
theorem tensor_ports (C : Configuration T O) (M : Finset O) :
    AnnotatedRuns.tensor C ⟨[], M⟩ = addAll C M := by
  show (⟨C.equations ++ [], C.present ∪ M⟩ : Configuration T O) = ⟨C.equations, C.present ∪ M⟩
  rw [List.append_nil]

/-! ## Open bisimilarity at the ports -/

section Open

variable {A : SubstitutionAction T S} {label : O → T} {offers : L → Firing T S O → Prop}
  {ports : O → Prop}

theorem OpenBisimilar.step {C D : Configuration T O} (h : OpenBisimilar A label offers ports C D)
    {lab : L ⊕ O} {C' : Configuration T O} (moved : OpenMoves A label offers ports C lab C') :
    ∃ D', OpenMoves A label offers ports D lab D' ∧ OpenBisimilar A label offers ports C' D' := by
  obtain ⟨R, bisimulation, related⟩ := h
  obtain ⟨D', moved', related'⟩ := bisimulation.1 related lab moved
  exact ⟨D', moved', R, bisimulation, related'⟩

/-- **Open bisimilarity is closed under adding a port atom.** -/
theorem OpenBisimilar.add_port {C D : Configuration T O} (h : OpenBisimilar A label offers ports C D)
    {o : O} (port : ports o) : OpenBisimilar A label offers ports (addAtom C o) (addAtom D o) := by
  obtain ⟨D', ⟨-, rfl⟩, related⟩ := h.step (lab := .inr o)
    (show OpenMoves A label offers ports C (.inr o) (addAtom C o) from ⟨port, rfl⟩)
  exact related

/-- **Open bisimilarity is closed under adding a finite set of port atoms.** -/
theorem OpenBisimilar.add_ports {C D : Configuration T O} (h : OpenBisimilar A label offers ports C D)
    (M : Finset O) (portsM : ∀ o ∈ M, ports o) :
    OpenBisimilar A label offers ports (addAll C M) (addAll D M) := by
  induction M using Finset.induction_on with
  | empty =>
      rw [addAll_empty, addAll_empty]
      exact h
  | insert o M _ ih =>
      rw [addAll_insert, addAll_insert]
      exact (ih fun x member => portsM x (Finset.mem_insert_of_mem member)).add_port
        (portsM o (Finset.mem_insert_self o M))

/-- **Open bisimilarity is a congruence for contexts of port atoms.** -/
theorem OpenBisimilar.tensor_ports {C D : Configuration T O}
    (h : OpenBisimilar A label offers ports C D) (M : Finset O) (portsM : ∀ o ∈ M, ports o) :
    OpenBisimilar A label offers ports (AnnotatedRuns.tensor C ⟨[], M⟩) (AnnotatedRuns.tensor D ⟨[], M⟩) := by
  rw [Race.tensor_ports, Race.tensor_ports]
  exact h.add_ports M portsM

/-- **Closed bisimilarity is open bisimilarity with no ports.** -/
theorem openBisimilar_noPorts_iff {C D : Configuration T O} :
    OpenBisimilar A label offers (fun _ => False) C D ↔ Bisimilar A label offers C D := by
  refine ⟨bisimilar_of_openBisimilar, ?_⟩
  rintro ⟨R, ⟨forward, backward, -⟩, related⟩
  refine ⟨R, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, related⟩
  · rintro X Y rel (ℓ | o) X' moved
    · exact forward rel ℓ moved
    · obtain ⟨impossible, -⟩ := moved
      exact False.elim impossible
  · rintro X Y rel (ℓ | o) Y' moved
    · exact backward rel ℓ moved
    · obtain ⟨impossible, -⟩ := moved
      exact False.elim impossible

end Open

/-! ## The context-labelled step -/

section Context

variable (A : SubstitutionAction T S) (label : O → T) (offers : L → Firing T S O → Prop)
  (ports : O → Prop)

/-- **The context-labelled step**: under `(ℓ, M)`, with `M` a finite set of ports, the configuration
with the atoms of `M` added fires a firing offered under `ℓ`. -/
def ContextMoves (C : Configuration T O) (lab : L × Finset O) (D : Configuration T O) : Prop :=
  (∀ o ∈ lab.2, ports o) ∧ Moves A label offers (addAll C lab.2) lab.1 D

/-- The context-labelled step as a Hennessy–Milner system. -/
def contextSystem : System (gslt A label offers) where
  Atom := PEmpty.{1}
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := L × Finset O
  act lab C D := ContextMoves A label offers ports C lab D
  act_resp_left := by
    intro lab C C' D same step
    exact ⟨D, (same : C = C') ▸ step, rfl⟩
  act_resp_right := by
    intro lab C D D' step same
    exact (same : D = D') ▸ step

/-- **Bisimilarity of the context-labelled step.** -/
def ContextBisimilar (C D : Configuration T O) : Prop :=
  (contextSystem A label offers ports).Bisimilar C D

variable {A label offers ports}

theorem contextMoves_empty_iff {C D : Configuration T O} {ℓ : L} :
    ContextMoves A label offers ports C (ℓ, ∅) D ↔ Moves A label offers C ℓ D := by
  show ((∀ o ∈ (∅ : Finset O), ports o) ∧ Moves A label offers (addAll C ∅) ℓ D) ↔ _
  rw [addAll_empty]
  exact ⟨fun moved => moved.2, fun moved => ⟨fun o member => absurd member (Finset.notMem_empty o), moved⟩⟩

theorem ContextBisimilar.step {C D : Configuration T O} (h : ContextBisimilar A label offers ports C D)
    {lab : L × Finset O} {C' : Configuration T O} (moved : ContextMoves A label offers ports C lab C') :
    ∃ D', ContextMoves A label offers ports D lab D' ∧ ContextBisimilar A label offers ports C' D' := by
  obtain ⟨R, bisimulation, related⟩ := h
  obtain ⟨D', moved', related'⟩ := bisimulation.1 related lab moved
  exact ⟨D', moved', R, bisimulation, related'⟩

theorem ContextBisimilar.symm {C D : Configuration T O} (h : ContextBisimilar A label offers ports C D) :
    ContextBisimilar A label offers ports D C :=
  (contextSystem A label offers ports).bisimilar_symm h

/-- One direction of closure under adding ports, used for both. -/
theorem ContextBisimilar.add_ports_step {X₀ Y₀ : Configuration T O}
    (related : ContextBisimilar A label offers ports X₀ Y₀) {N₀ : Finset O} (portsN₀ : ∀ o ∈ N₀, ports o)
    {lab : L × Finset O} {X' : Configuration T O}
    (moved : ContextMoves A label offers ports (addAll X₀ N₀) lab X') :
    ∃ Y', ContextMoves A label offers ports (addAll Y₀ N₀) lab Y' ∧
      ContextBisimilar A label offers ports X' Y' := by
  obtain ⟨ℓ, M⟩ := lab
  obtain ⟨portsM, fired⟩ := moved
  have joint : ContextMoves A label offers ports X₀ (ℓ, N₀ ∪ M) X' := by
    refine ⟨fun o member => (Finset.mem_union.mp member).elim (portsN₀ o) (portsM o), ?_⟩
    show Moves A label offers (addAll X₀ (N₀ ∪ M)) ℓ X'
    rw [← addAll_addAll]
    exact fired
  obtain ⟨Y', ⟨-, fired'⟩, related'⟩ := related.step joint
  refine ⟨Y', ⟨portsM, ?_⟩, related'⟩
  show Moves A label offers (addAll (addAll Y₀ N₀) M) ℓ Y'
  rw [addAll_addAll]
  exact fired'

/-- **Context bisimilarity is closed under adding a finite set of port atoms.** -/
theorem ContextBisimilar.add_ports {C D : Configuration T O}
    (h : ContextBisimilar A label offers ports C D) (N : Finset O) (portsN : ∀ o ∈ N, ports o) :
    ContextBisimilar A label offers ports (addAll C N) (addAll D N) := by
  refine ⟨fun X Y => ∃ X₀ Y₀ N₀, ContextBisimilar A label offers ports X₀ Y₀ ∧ (∀ o ∈ N₀, ports o) ∧
      X = addAll X₀ N₀ ∧ Y = addAll Y₀ N₀, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩,
    C, D, N, h, portsN, rfl, rfl⟩
  · rintro X Y ⟨X₀, Y₀, N₀, related, portsN₀, rfl, rfl⟩ lab X' moved
    obtain ⟨Y', moved', related'⟩ := related.add_ports_step portsN₀ moved
    exact ⟨Y', moved', X', Y', ∅, related', fun o member => absurd member (Finset.notMem_empty o),
      (addAll_empty X').symm, (addAll_empty Y').symm⟩
  · rintro X Y ⟨X₀, Y₀, N₀, related, portsN₀, rfl, rfl⟩ lab Y' moved
    obtain ⟨X', moved', related'⟩ := related.symm.add_ports_step portsN₀ moved
    exact ⟨X', moved', X', Y', ∅, related'.symm, fun o member => absurd member (Finset.notMem_empty o),
      (addAll_empty X').symm, (addAll_empty Y').symm⟩

/-- **Context bisimilarity is closed under adding a port atom.** -/
theorem ContextBisimilar.add_port {C D : Configuration T O}
    (h : ContextBisimilar A label offers ports C D) {o : O} (port : ports o) :
    ContextBisimilar A label offers ports (addAtom C o) (addAtom D o) := by
  rw [← addAll_singleton, ← addAll_singleton]
  exact h.add_ports {o} fun x member => by
    rw [Finset.mem_singleton.mp member]
    exact port

/-- **The context-labelled step is a congruence for contexts of port atoms.** -/
theorem ContextBisimilar.tensor_ports {C D : Configuration T O}
    (h : ContextBisimilar A label offers ports C D) (M : Finset O) (portsM : ∀ o ∈ M, ports o) :
    ContextBisimilar A label offers ports (AnnotatedRuns.tensor C ⟨[], M⟩)
      (AnnotatedRuns.tensor D ⟨[], M⟩) := by
  rw [Race.tensor_ports, Race.tensor_ports]
  exact h.add_ports M portsM

/-- **The context-labelled step's bisimilarity is open bisimilarity**, for every program. -/
theorem contextBisimilar_iff_openBisimilar {C D : Configuration T O} :
    ContextBisimilar A label offers ports C D ↔ OpenBisimilar A label offers ports C D := by
  constructor
  · intro h
    refine ⟨ContextBisimilar A label offers ports, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, h⟩
    · rintro X Y related (ℓ | o) X' moved
      · obtain ⟨Y', moved', related'⟩ := related.step (contextMoves_empty_iff.mpr moved)
        exact ⟨Y', contextMoves_empty_iff.mp moved', related'⟩
      · obtain ⟨port, rfl⟩ := moved
        exact ⟨addAtom Y o, ⟨port, rfl⟩, related.add_port port⟩
    · rintro X Y related (ℓ | o) Y' moved
      · obtain ⟨X', moved', related'⟩ := related.symm.step (contextMoves_empty_iff.mpr moved)
        exact ⟨X', contextMoves_empty_iff.mp moved', related'.symm⟩
      · obtain ⟨port, rfl⟩ := moved
        exact ⟨addAtom X o, ⟨port, rfl⟩, related.add_port port⟩
  · intro h
    refine ⟨OpenBisimilar A label offers ports, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, h⟩
    · rintro X Y related ⟨ℓ, M⟩ X' ⟨portsM, fired⟩
      obtain ⟨Y', fired', related'⟩ := (related.add_ports M portsM).step (lab := .inl ℓ) fired
      exact ⟨Y', ⟨portsM, fired'⟩, related'⟩
    · rintro X Y related ⟨ℓ, M⟩ Y' ⟨portsM, fired⟩
      have flipped : OpenBisimilar A label offers ports Y X :=
        (openSystem A label offers ports).bisimilar_symm related
      obtain ⟨X', fired', related'⟩ := (flipped.add_ports M portsM).step (lab := .inl ℓ) fired
      exact ⟨X', ⟨portsM, fired'⟩, (openSystem A label offers ports).bisimilar_symm related'⟩

end Context

/-! ## Controls -/

namespace Triggered

variable (τ : T) (A : SubstitutionAction T S)

/-- **With the triggers as ports, the continuations `{k}` and `{kb}` are told apart**: adding the
trigger of `C` lets only the first fire. -/
theorem continuations_not_openBisimilar :
    ¬ OpenBisimilar A (label τ) (offers τ) trigger X Y := fun open_ =>
  (not_congruence τ A).2 (bisimilar_of_openBisimilar (open_.add_port (Or.inr (Or.inr rfl))))

/-- **A context atom outside the ports breaks open bisimilarity**: with no ports, the continuations
are open bisimilar, and in parallel with the trigger of `C` they are not. -/
theorem outside_ports_not_congruence :
    OpenBisimilar A (label τ) (offers τ) (fun _ => False) X Y ∧
      ¬ OpenBisimilar A (label τ) (offers τ) (fun _ => False)
        (AnnotatedRuns.tensor X ⟨[], {Site.tc}⟩) (AnnotatedRuns.tensor Y ⟨[], {Site.tc}⟩) := by
  refine ⟨openBisimilar_noPorts_iff.mpr (not_congruence τ A).1, fun open_ => ?_⟩
  rw [Race.tensor_ports, Race.tensor_ports, addAll_singleton, addAll_singleton] at open_
  exact (not_congruence τ A).2 (openBisimilar_noPorts_iff.mp open_)

/-- **With the triggers as ports, open bisimilarity is a congruence for the trigger of `C`**: every
pair of open-bisimilar configurations stays open bisimilar beside it. -/
theorem trigger_congruence {C D : Configuration T Site}
    (h : OpenBisimilar A (label τ) (offers τ) trigger C D) :
    OpenBisimilar A (label τ) (offers τ) trigger (AnnotatedRuns.tensor C ⟨[], {Site.tc}⟩)
      (AnnotatedRuns.tensor D ⟨[], {Site.tc}⟩) :=
  h.tensor_ports {Site.tc} fun o member => by
    rw [Finset.mem_singleton.mp member]
    exact Or.inr (Or.inr rfl)

end Triggered

#print axioms addAll_empty
#print axioms addAll_insert
#print axioms addAll_addAll
#print axioms addAll_singleton
#print axioms tensor_ports
#print axioms OpenBisimilar.step
#print axioms OpenBisimilar.add_port
#print axioms OpenBisimilar.add_ports
#print axioms OpenBisimilar.tensor_ports
#print axioms openBisimilar_noPorts_iff
#print axioms contextMoves_empty_iff
#print axioms ContextBisimilar.step
#print axioms ContextBisimilar.symm
#print axioms ContextBisimilar.add_ports_step
#print axioms ContextBisimilar.add_ports
#print axioms ContextBisimilar.add_port
#print axioms ContextBisimilar.tensor_ports
#print axioms contextBisimilar_iff_openBisimilar
#print axioms Triggered.continuations_not_openBisimilar
#print axioms Triggered.outside_ports_not_congruence
#print axioms Triggered.trigger_congruence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
