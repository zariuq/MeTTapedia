import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ModalComparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramAdequacy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.RhoRedexAmbiguity

/-!
# Rho's past along the narrowing

Reading a heated store as one rho process (`NarrowingToRho.narrow`) is an onto functional
bisimulation, so possibility and successor necessity pull back from rho to the store
(`Narrowings.Rho.modal_hom`). Predecessor necessity needs predecessors lifted
(`ModalComparison.backZag_iff_predecessorBox_le`).

## Predecessors do not lift

Every communication takes a message and a receiver: its source is a nonempty bag, so the firing
records its matches in the knowledge (`channelStep_learns`). A heated store with no knowledge
therefore has no predecessor (`no_predecessor_without_knowledge`), while its process can
(`forgetful_store`, from rho's own communication in `RhoRedexAmbiguity`). Hence:

* `rho_backZag_fails`: the narrowing does not lift predecessors;
* `rho_predecessorBox_fails`: "no predecessor" holds of that store and fails of its process.

One inclusion always holds (`rho_predecessorBox_le`): rho's predecessor necessity, read on the
store, implies the store's.

## Predecessors lift up to the heating class

For every onto functional bisimulation, predecessors lift up to the fibre
(`backZag_up_to_fibre`), and predecessor necessity pulls back exactly to predecessor necessity
over the whole fibre (`pb_predecessorBox_eq_fibre`). The fibre of the narrowing is one heating
class (`NarrowingToRho.same_narrowing_iff_same_heating`), so rho's predecessor necessity is the
store's taken over every store with the same bag of components, whatever their knowledge
(`rho_predecessorBox_eq_fibre`). Knowledge records history; the narrowing forgets it, and the
fibre puts it back as a quantifier.

## Control: an empty source lifts predecessors

The failure comes from nonempty sources. On the first-order step under the program that makes `T`
from nothing (`makesT`), a firing records no match, so reading a consistent store as its bag of
labels carries steps (`make_zig`) and lifts predecessors (`make_backZag`): remove one copy of `T`
and make it again. Predecessor necessity then pulls back exactly (`make_predecessorBox_pb`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.RhoPast

open Mettapedia.OSLF.Framework.DerivedModalities
open FragmentsOfTheStep.TransitionMaps
open ModalComparison

/-! ## Predecessor necessity over the fibre -/

section Fibre

universe u v

variable {X : Type u} {Y : Type v} {stepX : X → X → Prop} {stepY : Y → Y → Prop} {h : X → Y}

/-- **Predecessor necessity over the fibre**: every predecessor of every state with the same
image. -/
def fibrePredecessorBox (stepX : X → X → Prop) (h : X → Y) (φ : X → Prop) (x : X) : Prop :=
  ∀ x₁, h x₁ = h x → derivedBox (span stepX) φ x₁

/-- It is stronger than predecessor necessity at the state itself. -/
theorem fibre_le_predecessorBox (φ : X → Prop) :
    fibrePredecessorBox stepX h φ ≤ derivedBox (span stepX) φ :=
  fun x all => all x rfl

/-- **Predecessors lift up to the fibre**, along every onto functional bisimulation. -/
theorem backZag_up_to_fibre (bisimulation : FunctionalBisimulation stepX stepY h)
    (onto : Function.Surjective h) {x : X} {y : Y} (step : stepY y (h x)) :
    ∃ x₁ x', h x₁ = h x ∧ stepX x' x₁ ∧ h x' = y := by
  obtain ⟨x', rfl⟩ := onto y
  obtain ⟨x₁, step₁, mapped⟩ := bisimulation.zag step
  exact ⟨x₁, x', mapped, step₁, rfl⟩

/-- **Predecessor necessity pulls back to predecessor necessity over the fibre.** -/
theorem pb_predecessorBox_eq_fibre (bisimulation : FunctionalBisimulation stepX stepY h)
    (onto : Function.Surjective h) (φ : Y → Prop) :
    pb h (derivedBox (span stepY) φ) = fibrePredecessorBox stepX h (pb h φ) := by
  funext x
  apply propext
  constructor
  · intro all x₁ same
    refine (box_iff stepX _ x₁).mpr fun x' step => ?_
    have image : stepY (h x') (h x) := same ▸ bisimulation.zig step
    exact (box_iff stepY φ (h x)).mp all (h x') image
  · intro all
    refine (box_iff stepY φ (h x)).mpr fun y' step => ?_
    obtain ⟨x', rfl⟩ := onto y'
    obtain ⟨x₁, step₁, mapped⟩ := bisimulation.zag step
    exact (box_iff stepX _ x₁).mp (all x₁ mapped) x' step₁

end Fibre

/-! ## Rho -/

section Rho

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres
open ContextualCommunicationProfiles ContextualCommunicationAdequacy
open FragmentsOfTheStep.NarrowingToRho FragmentsOfTheStep.RhoChannelFragment

variable {context : Ctx sig}

local instance : DecidableEq (Process context) := Classical.decEq _

/-- **One inclusion always holds**: rho's predecessor necessity, read on the store, implies the
store's. -/
theorem rho_predecessorBox_le (φ : Process context → Prop) :
    pb narrow (derivedBox (span RhoStep) φ) ≤ derivedBox (span (heatedStep (context := context))) (pb narrow φ) :=
  (zig_iff_le_predecessorBox (stepX := heatedStep (context := context)) (stepY := RhoStep)
    (h := narrow)).mp narrowing_functionalBisimulation.zig φ

/-- **Rho's predecessor necessity is the store's over the heating class.** -/
theorem rho_predecessorBox_eq_fibre (φ : Process context → Prop) :
    pb narrow (derivedBox (span RhoStep) φ) =
      fibrePredecessorBox (heatedStep (context := context)) narrow (pb narrow φ) :=
  pb_predecessorBox_eq_fibre narrowing_functionalBisimulation narrowing_onto φ

/-- **Every communication learns**: its source is a nonempty bag, a message and a receiver, so the
firing records their matches in the knowledge. -/
theorem channelStep_learns {before after : Configuration (Process context) (Occurrence context)}
    (step : ChannelStep before after) : after.equations ≠ [] := by
  obtain ⟨rule, member, ⟨selection, valid, rfl⟩, _⟩ := step
  obtain ⟨_, _, _, name, payload, body, takes, _⟩ := (channelCommunication_iff rule).mp member
  have two : rule.take.length = 2 := by
    have counted := congrArg Multiset.card takes
    simpa using counted
  have takenTwo : selection.taken.length = 2 := valid.take_length.symm.trans two
  intro empty
  have lengths := congrArg List.length empty
  simp only [Selection.result, Selection.problem, Selection.equations, List.length_append,
    List.length_zipWith, two, takenTwo, List.length_nil] at lengths
  omega

/-- **A heated store with no knowledge has no predecessor.** -/
theorem no_predecessor_without_knowledge {C : HeatedStore context} (empty : C.1.equations = [])
    (C' : HeatedStore context) : ¬ heatedStep C' C :=
  fun step => channelStep_learns step empty

/-- **A heated store with no knowledge whose process has a rho predecessor**: the result of rho's
own communication in `RhoRedexAmbiguity`, its knowledge forgotten. -/
theorem forgetful_store :
    ∃ (C₀ : HeatedStore []) (P : Process []), C₀.1.equations = [] ∧ RhoStep P (narrow C₀) := by
  obtain ⟨C, C₁, _, represented, step, _⟩ := FragmentsOfTheStep.RhoRedexAmbiguity.rho_lifts_not_unique_on_firings
  have heatedC := (RhoStoreBisimulation.represents_iff_heated.mp represented).1
  obtain ⟨_, _, represented₁⟩ := channel_fragment_bisimulation.1 represented step
  have heated₁ := (RhoStoreBisimulation.represents_iff_heated.mp represented₁).1
  have heated₀ : RhoStoreBisimulation.Heated
      (⟨[], C₁.present⟩ : Configuration (Process []) (Occurrence [])) :=
    ⟨(action []).models_nil _, heated₁.2⟩
  have moved : RhoStep (narrow ⟨C, heatedC⟩) (narrow ⟨C₁, heated₁⟩) :=
    narrowing_functionalBisimulation.zig (show heatedStep ⟨C, heatedC⟩ ⟨C₁, heated₁⟩ from step)
  exact ⟨⟨_, heated₀⟩, narrow ⟨C, heatedC⟩, rfl, moved⟩

/-- **Predecessors do not lift along rho's narrowing.** -/
theorem rho_backZag_fails : ¬ BackZag (heatedStep (context := [])) RhoStep narrow := by
  intro back
  obtain ⟨C₀, P, empty, step⟩ := forgetful_store
  obtain ⟨C', back', _⟩ := back step
  exact no_predecessor_without_knowledge empty C' back'

/-- **Rho's predecessor necessity does not pull back to the store**: "no predecessor" holds of a
store with no knowledge and fails of its process. -/
theorem rho_predecessorBox_fails :
    ∃ C₀ : HeatedStore [],
      derivedBox (span (heatedStep (context := []))) (pb narrow (fun _ => False)) C₀ ∧
        ¬ pb narrow (derivedBox (span (RhoStep (context := []))) (fun _ => False)) C₀ := by
  obtain ⟨C₀, P, empty, step⟩ := forgetful_store
  refine ⟨C₀, (box_iff _ _ _).mpr fun C' back => absurd back (no_predecessor_without_knowledge empty C'),
    fun all => ?_⟩
  exact (box_iff _ _ _).mp all P step

end Rho

/-! ## Control: an empty source lifts predecessors -/

section MakeControl

open NamesOnTheStep NamesOnTheStep.IssuingControls ProgramAdequacy
open MeTTaCalculus.OccurrenceCommits (fire)

/-- The program that makes `T` from nothing: its source is the empty bag. -/
def makesT : RuleInstance Expr := ⟨[], [], [], [], [factT]⟩

/-- Ground stores with consistent knowledge. -/
abbrev GroundStore := {C : Conf // ∀ e ∈ C.equations, e.1 = e.2}

/-- The step under the program. -/
def makeStep (C C' : GroundStore) : Prop :=
  StepSpan.Succ (program ground (Prod.fst : Occ → Expr) {makesT}) C.1 C'.1

/-- The bag of labels: identities and knowledge forgotten. -/
def bag (C : GroundStore) : Multiset Expr := C.1.present.val.map Prod.fst

/-- The program's reaction on bags. -/
def grows (M M' : Multiset Expr) : Prop := M' = factT ::ₘ M

/-- **Reading the bag carries steps.** -/
theorem make_zig : Zig makeStep grows bag := by
  intro C C' step
  obtain ⟨rule, ⟨taken, read, made⟩, member, valid, reached⟩ :=
    (program_succ_iff ground Prod.fst {makesT} C.1 C'.1).mp step
  have isMake : rule = makesT := member
  subst isMake
  have takenNil : taken = [] := List.length_eq_zero_iff.mp valid.take_length.symm
  subst takenNil
  have madeOne : made.length = 1 := by simpa [makesT] using congrArg List.length valid.outputs
  obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp madeOne
  have labelled : o.1 = factT := by simpa [makesT] using valid.outputs
  have fresh : o ∉ C.1.present := fun inside =>
    Finset.disjoint_left.mp valid.occurrences.fresh (by simp [Selection.commit]) inside
  have present : C'.1.present = insert o C.1.present := by
    rw [← reached]
    ext y
    simp only [Selection.result, fire, Selection.commit, List.toFinset_nil, List.toFinset_cons,
      Finset.sdiff_empty, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
    exact or_comm
  show C'.1.present.val.map Prod.fst = factT ::ₘ C.1.present.val.map Prod.fst
  rw [present, Finset.insert_val_of_notMem fresh, Multiset.map_cons, labelled]

/-- **Reading the bag lifts predecessors**: remove one copy of `T` and make it again. -/
theorem make_backZag : BackZag makeStep grows bag := by
  rintro ⟨⟨equations, present⟩, consistent⟩ M grown
  have bagged : present.val.map Prod.fst = factT ::ₘ M := grown
  have inBag : factT ∈ present.val.map Prod.fst := by
    rw [bagged]
    simp
  obtain ⟨o, inside, labelled⟩ := Multiset.mem_map.mp inBag
  have member : o ∈ present := inside
  refine ⟨⟨⟨equations, present.erase o⟩, consistent⟩, ?_, ?_⟩
  · refine (program_succ_iff ground Prod.fst {makesT} _ _).mpr
      ⟨makesT, ⟨[], [], [o]⟩, rfl, ?_, ?_⟩
    · refine ⟨List.nodup_nil, List.nodup_singleton o, rfl, rfl, by simp [makesT, labelled],
        ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨(), ?_⟩, ?_⟩
      · simp [Selection.commit]
      · simp [Selection.commit]
      · simp [Selection.commit]
      · simp [Selection.commit]
      · intro _ inQueries
        simp [Selection.commit] at inQueries
      · intro e inProblem
        simp only [Selection.problem, Selection.equations, makesT, List.zipWith_nil_left,
          List.append_nil] at inProblem
        exact consistent e inProblem
      · intro check inChecks
        simp [makesT] at inChecks
    · simp only [Selection.result, Selection.problem, Selection.equations, makesT,
        List.zipWith_nil_left, List.append_nil]
      congr 1
      ext y
      simp only [fire, Selection.commit, List.toFinset_nil, List.toFinset_cons, Finset.sdiff_empty,
        Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.notMem_empty, or_false]
      by_cases same : y = o
      · subst same
        simp [member]
      · simp [same]
  · show (present.erase o).val.map Prod.fst = M
    rw [Finset.erase_val, Multiset.map_erase_of_mem _ _ inside, labelled, bagged,
      Multiset.erase_cons_head]

/-- **Control: with an empty source, predecessor necessity pulls back exactly.** -/
theorem make_predecessorBox_pb (φ : Multiset Expr → Prop) :
    pb bag (derivedBox (span grows) φ) = derivedBox (span makeStep) (pb bag φ) :=
  (predecessorBox_pb_iff (stepX := makeStep) (stepY := grows) (h := bag)).mp
    ⟨make_zig, make_backZag⟩ φ

end MakeControl

#print axioms fibre_le_predecessorBox
#print axioms backZag_up_to_fibre
#print axioms pb_predecessorBox_eq_fibre
#print axioms rho_predecessorBox_le
#print axioms rho_predecessorBox_eq_fibre
#print axioms channelStep_learns
#print axioms no_predecessor_without_knowledge
#print axioms forgetful_store
#print axioms rho_backZag_fails
#print axioms rho_predecessorBox_fails
#print axioms make_zig
#print axioms make_backZag
#print axioms make_predecessorBox_pb

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.RhoPast
