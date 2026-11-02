import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.IndexedOccurrences
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PositiveResourceProjection
import Mettapedia.OSLF.Syntax.RhoScopedEventPresheaf

/-!
# Scoped rho source profiles as ordinary occurrence-rule instances

The term carrier is the intrinsic process quotient at an arbitrary ambient
context. Its CMR substitution action is the actual capture-avoiding ambient
substitution, not an identity action. The declared source equations already
live in that quotient; operational COMM and Drop admission remain separate.

Each original source root compiles through the complete typed parallel
inventory. This fixes the observation at process classes while retaining
separate physical occurrences for duplicate components. The root carries its
authored rule index and both contextual assignments. No new source reduction
relation or unification solver is introduced.

This profile uses ordinary intrinsic substitution, including inside quoted
terms. It is not the paper-faithful rho semantic-substitution profile, which
seals quotation and executes received drops during communication.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationProfiles

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres
open RhoScopedParallelInventory RhoScopedEventPresheaf
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

abbrev Root (admitted : RhoScopedParallelEvents.SourceRule → Prop) (context : Ctx sig) :=
  RhoScopedParallelEvents.Root RhoScopedParallelEvents.sourceRules admitted context

def action (context : Ctx sig) :
    SubstitutionAction (Process context) (Sub sig context context) where
  E := Eq
  equivalence := eq_equivalence
  apply change process := bindQ (E := rhoSourceE) change process
  identity := fun _ position => .var position
  compose later earlier := fun sort position => bind later (earlier sort position)
  apply_identity := substitute_id
  apply_compose later earlier process := (substitute_comp earlier later process).symm
  preserves change _ _ same := congrArg (fun process : Process context => bindQ change process) same

def component {context : Ctx sig} (prime : Prime context) : Process context := write {prime}

/-- Canonical parallel components retain their source typing evidence. -/
def normalized {context : Ctx sig} (process : Process context) : Multiset (Process context) :=
  (read process).map component

/-- Read a bag of occurrence labels back as its actual parallel process class. -/
def assemble {context : Ctx sig} (parts : Multiset (Process context)) : Process context :=
  write ((parts.map read).sum)

theorem assemble_zero (context : Ctx sig) : assemble (0 : Multiset (Process context)) = zero context := by
  simp only [assemble, Multiset.map_zero, Multiset.sum_zero, write_zero]

theorem assemble_singleton {context : Ctx sig} (process : Process context) :
    assemble {process} = process := by
  simp only [assemble, Multiset.map_singleton, Multiset.sum_singleton, write_read]

theorem assemble_add {context : Ctx sig} (first second : Multiset (Process context)) :
    assemble (first + second) = join (assemble first) (assemble second) := by
  simp only [assemble, Multiset.map_add, Multiset.sum_add, write_add]

theorem assemble_cons {context : Ctx sig} (first : Process context) (rest : Multiset (Process context)) :
    assemble (first ::ₘ rest) = join first (assemble rest) := by
  rw [show first ::ₘ rest = {first} + rest from rfl, assemble_add, assemble_singleton]

theorem normalized_join {context : Ctx sig} (first second : Process context) :
    normalized (join first second) = normalized first + normalized second := by
  simp only [normalized, read_join, Multiset.map_add]

theorem assemble_normalized {context : Ctx sig} (process : Process context) :
    assemble (normalized process) = process := by
  unfold assemble normalized
  rw [Multiset.map_map]
  simp only [Function.comp_def]
  have components : (fun prime : Prime context => read (component prime)) =
      fun prime => ({prime} : Multiset (Prime context)) := by
    funext prime
    exact read_write {prime}
  rw [components, Multiset.sum_map_singleton, write_read]

theorem normalized_singleton_of_card_one {context : Ctx sig} (process : Process context)
    (one : (normalized process).card = 1) : normalized process = {process} := by
  obtain ⟨component, same⟩ := Multiset.card_eq_one.mp one
  have reads := assemble_normalized process
  rw [same, assemble_singleton] at reads
  exact same.trans (congrArg (fun value => ({value} : Multiset (Process context))) reads)

theorem assemble_substitution {context destination : Ctx sig}
    (change : Sub sig context destination) (parts : Multiset (Process context)) :
    assemble (parts.map (bindQ change)) = bindQ change (assemble parts) := by
  induction parts using Multiset.induction_on with
  | empty =>
      rw [Multiset.map_zero, assemble_zero, assemble_zero]
      rfl
  | cons first rest earlier =>
      rw [Multiset.map_cons, assemble_cons, assemble_cons, earlier, substitute_join]

def instanceRule {admitted : RhoScopedParallelEvents.SourceRule → Prop} {context : Ctx sig}
    (root : Root admitted context) : RuleInstance (Process context) where
  take := (normalized root.source).toList
  read := []
  tell := []
  checks := []
  produce := (normalized root.target).toList

theorem instance_take {admitted : RhoScopedParallelEvents.SourceRule → Prop} {context : Ctx sig}
    (root : Root admitted context) : ((instanceRule root).take : Multiset (Process context)) =
      normalized root.source := Multiset.coe_toList _

theorem instance_produce {admitted : RhoScopedParallelEvents.SourceRule → Prop} {context : Ctx sig}
    (root : Root admitted context) : ((instanceRule root).produce : Multiset (Process context)) =
      normalized root.target := Multiset.coe_toList _

theorem assemble_mapped_take {admitted : RhoScopedParallelEvents.SourceRule → Prop} {context : Ctx sig}
    (root : Root admitted context) (assignment : Sub sig context context) :
    assemble ((instanceRule root).take.map ((action context).apply assignment) : Multiset (Process context)) =
      bindQ assignment root.source := by
  rw [← Multiset.map_coe, instance_take]
  exact (assemble_substitution assignment (normalized root.source)).trans
    (congrArg (bindQ assignment) (assemble_normalized root.source))

theorem assemble_mapped_produce {admitted : RhoScopedParallelEvents.SourceRule → Prop} {context : Ctx sig}
    (root : Root admitted context) (assignment : Sub sig context context) :
    assemble ((instanceRule root).produce.map ((action context).apply assignment) : Multiset (Process context)) =
      bindQ assignment root.target := by
  rw [← Multiset.map_coe, instance_produce]
  exact (assemble_substitution assignment (normalized root.target)).trans
    (congrArg (bindQ assignment) (assemble_normalized root.target))

abbrev Occurrence (context : Ctx sig) := IndexedOccurrences.Occurrence (Process context)
abbrev label {context : Ctx sig} : Occurrence context → Process context := IndexedOccurrences.label

def observe {context : Ctx sig} (assignment : Sub sig context context)
    (world : Finset (Occurrence context)) : Process context :=
  assemble (labels (PositiveResourceProjection.realized (action context) assignment label) world)

theorem every_source_class_has_occurrences {context : Ctx sig} (process : Process context) :
    ∃ world : Finset (Occurrence context), labels label world = normalized process := by
  classical
  exact IndexedOccurrences.realize (normalized process)

theorem observe_identity_of_normalized {context : Ctx sig}
    (world : Finset (Occurrence context)) (process : Process context)
    (represents : labels label world = normalized process) :
    observe (action context).identity world = process := by
  have labelsFixed : PositiveResourceProjection.realized (action context)
      (action context).identity (label (context := context)) = label := by
    funext occurrence
    exact (action context).apply_identity _
  rw [observe, labelsFixed, represents, assemble_normalized]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationProfiles
