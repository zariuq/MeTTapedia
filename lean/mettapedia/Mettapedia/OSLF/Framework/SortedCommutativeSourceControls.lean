import Mettapedia.OSLF.Framework.SortedCommutativeSourceCategory
import Mettapedia.OSLF.Framework.SortedCommutativeInstrumentControls

/-!
# Conservative source equations and genuinely new observer contexts

Original arguments, positions and source equations survive the inclusion.
The extension also has an actual ask-then-get context outside that image.
Its separately defined context erasure is not a closed-value action
retraction: an auxiliary frame erases to a hole while its ground term erases
to the source unit. This rejects observation reflection from faithfulness.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeSourceControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open SortedCommutativeInstruments
open SortedCommutativeInstrumentControls (Symbol arity)

abbrev SourceValue := Source.Value arity

def low : SourceValue := Term.node (signature := Source.signature arity) Symbol.low (fun position => Fin.elim0 position)
def high : SourceValue := Term.node (signature := Source.signature arity) Symbol.high (fun position => Fin.elim0 position)

theorem entire_low_readout : Source.embed low = SortedCommutativeInstrumentControls.low := by
  apply congrArg (Term.node (signature := signature arity) (SortedCommutativeInstruments.Constructor.original Symbol.low))
  funext position
  exact Fin.elim0 position
theorem entire_high_readout : Source.embed high = SortedCommutativeInstrumentControls.high := by
  apply congrArg (Term.node (signature := signature arity) (SortedCommutativeInstruments.Constructor.original Symbol.high))
  funext position
  exact Fin.elim0 position

theorem source_values_are_distinct : classOf low ≠ classOf high := by
  intro same
  have images := congrArg Source.classEmbedding same
  change classOf (Source.embed low) = classOf (Source.embed high) at images
  rw [entire_low_readout, entire_high_readout] at images
  exact SortedCommutativeInstrumentControls.low_high_classes_distinct images

def sourceCut : SourceValue := .cut rfl low high
def swappedCut : SourceValue := .cut rfl high low

theorem original_commutative_equation : Equation sourceCut swappedCut :=
  Equation.comm (signature := Source.signature arity) (Parallel := Source.Parallel arity) rfl low high

theorem source_equation_survives_extension : Equation (Source.embed sourceCut) (Source.embed swappedCut) :=
  Source.embed_equation original_commutative_equation

theorem source_equation_is_reflected :
    Equation (Source.embed sourceCut) (Source.embed swappedCut) → Equation sourceCut swappedCut :=
  (Source.equation_iff_embedded sourceCut swappedCut).mpr

def firstHole : Source.Context (arity := arity) := RawContext.frame Symbol.pair 0 (fun _ _ => low) .hole
def secondHole : Source.Context (arity := arity) := RawContext.frame Symbol.pair 1 (fun _ _ => low) .hole

theorem source_position_collision : firstHole.fill low = secondHole.fill low := by
  apply congrArg (Term.node (signature := Source.signature arity) Symbol.pair)
  funext position
  fin_cases position <;> rfl

private theorem first_context_readout : Source.embedContext firstHole = SortedCommutativeInstrumentControls.firstHole := by
  simp only [firstHole, Source.embedContext, entire_low_readout, SortedCommutativeInstrumentControls.firstHole]

private theorem second_context_readout : Source.embedContext secondHole = SortedCommutativeInstrumentControls.secondHole := by
  simp only [secondHole, Source.embedContext, entire_low_readout, SortedCommutativeInstrumentControls.secondHole]

theorem original_positions_remain_distinct : ¬ContextEquation firstHole secondHole := by
  intro equation
  have images := Source.embedContext_equation equation
  rw [first_context_readout, second_context_readout] at images
  exact SortedCommutativeInstrumentControls.same_ground_does_not_identify_contexts images

theorem whole_source_filling_readout :
    (Source.embedContext firstHole).fill (Source.embed sourceCut) = Source.embed (firstHole.fill sourceCut) :=
  Source.embedContext_fill firstHole sourceCut

def extraContext : RawContext (signature arity) (Parallel arity) .base .base :=
  (probeContext arity (.ask (.ordinary Symbol.pair))).comp
    (probeContext arity (.get (.ordinary Symbol.pair) 0))

theorem extra_context_erases_to_hole : Source.eraseContext extraContext = (.hole : Source.Context (arity := arity)) := rfl

theorem extra_context_is_not_identity :
    contextClassOf extraContext ≠ contextClassOf (.hole : RawContext (signature arity) (Parallel arity) .base .base) := by
  intro same
  have counts := congrArg
    (fun context : ContextClass (signature arity) (Parallel arity) .base .base =>
      Mettapedia.CategoryTheory.MixedResidue.Context.frameCount (normalizeContext context)) same
  change 2 = 0 at counts
  cases counts

theorem extension_adds_actual_context :
    ¬∃ original : ContextClass (Source.signature arity) (Source.Parallel arity) (ULift.up ()) (ULift.up ()),
      Source.contextEmbedding original = contextClassOf extraContext := by
  rintro ⟨original, images⟩
  have old := (Source.context_retraction_embedding original).symm.trans (congrArg Source.contextRetraction images)
  have returned := congrArg Source.contextEmbedding old
  exact extra_context_is_not_identity (images.symm.trans returned)

theorem actual_source_inclusion_is_not_full : ¬(Source.inclusion (arity := arity)).Full := by
  intro full
  obtain ⟨original, mapped⟩ := full.map_surjective
    (X := (RawObject.interface (ULift.up ()) : Source.SourceCategory (arity := arity)))
    (Y := (RawObject.interface (ULift.up ()) : Source.SourceCategory (arity := arity)))
    (RawArrow.context (contextClassOf extraContext))
  cases original with
  | context suppliedContext => exact extension_adds_actual_context ⟨suppliedContext, RawArrow.context.inj mapped⟩

theorem low_is_not_source_unit : low ≠ (.zero rfl : SourceValue) := by
  intro same
  have inventories := congrArg inventory same
  exact Multiset.singleton_ne_zero _ inventories

theorem context_erasure_is_not_closed_value_action :
    ¬∀ context : RawContext (signature arity) (Parallel arity) .base .base,
      ∀ supplied : SourceValue,
        Source.erase (context.fill (Source.embed supplied)) = (Source.eraseContext context).fill supplied := by
  intro coherent
  have impossible := coherent extraContext low
  change (.zero rfl : SourceValue) = low at impossible
  exact low_is_not_source_unit impossible.symm

theorem whole_origin_firing_is_retained :
    (directReceipt (.get 37 (.ordinary Symbol.pair) (Fin.cases (Source.embed low) (fun _ => Source.embed high)) 1 :
      Occurrence arity Nat)).occurrence.origin = 37 := rfl

theorem whole_selected_value_is_retained :
    (directReceipt (.get 37 (.ordinary Symbol.pair) (Fin.cases (Source.embed low) (fun _ => Source.embed high)) 1 :
      Occurrence arity Nat)).occurrence.target =
        (RawArrow.value (Source.classEmbedding (classOf high)) : (.origin : ContextCategory arity) ⟶ .interface .base) := rfl

end Mettapedia.OSLF.Framework.SortedCommutativeSourceControls
