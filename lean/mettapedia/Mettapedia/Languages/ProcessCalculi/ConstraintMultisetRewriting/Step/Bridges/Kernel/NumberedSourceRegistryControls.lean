import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceRegistry
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceInputControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.SourceDAGReceive

/-!
# Actual initial registry, truth admission and visible-shadow controls

The initial registry is exactly SourceDAGReceive.start's registry. The
nonempty numbered truth prefix supplies independent decoded syntax and the
existing successful truth admission. Registry metadata and cache transport
do not constitute a SourceDAGReceive command run or literal packet receipt.

The shadowing registry is deliberately mismapped. Its control refutes an
admission-only lookup-preservation claim, not kernel soundness or the honest
captured input. Hidden duplicate payloads need no declaration authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceRegistryControls

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution DefinitionAdapters SignatureFormation
open NumberedSourceSyntax NumberedSourceRegistry

/-- The input is nonempty; only its actual start-registry metadata is used. -/
def input : SourceDAGReceive.Input :=
  ⟨NumberedSourceInputControls.typeBodies.toArray, NumberedSourceInputControls.termBodies.toArray, #[]⟩

def initial := SourceDAGReceive.start input
def initialSymbols : ExportCodec.Symbols := initial.symbols

def truthSymbols : ExportCodec.Symbols :=
  { initialSymbols with constants :=
    ("T", StandardTheoryInterpretation.Source.truthResult.output.constant) :: initialSymbols.constants }

theorem actual_truth_admitted :
    admitConstantInTheory initial.registered.registered.context
      (ExportReplay.instanceCertificates initial.registered.registered.context.signature)
      (.global "T") NumberedSourceSyntaxControls.decodedTruth =
        some StandardTheoryInterpretation.Source.truthResult :=
  NumberedSourceSyntaxControls.truth_constant_admitted

theorem initial_preserves_literal_prefix :
    preserves? NumberedSourceSyntaxControls.symbols initialSymbols = true := by decide +kernel

theorem truth_preserves_initial : preserves? initialSymbols truthSymbols = true := by decide +kernel

theorem truth_preserves_literal_prefix :
    preserves? NumberedSourceSyntaxControls.symbols truthSymbols = true :=
  (preserves?_eq_true_iff _ _).mpr
    (((preserves?_eq_true_iff _ _).mp initial_preserves_literal_prefix).trans
      ((preserves?_eq_true_iff _ _).mp truth_preserves_initial))

theorem truth_type_cache : TypeCacheCorrect truthSymbols NumberedSourceSyntaxControls.typeRows
    NumberedSourceSyntaxControls.typeCache :=
  typeCache_transport ((preserves?_eq_true_iff _ _).mp truth_preserves_literal_prefix) _ _
    NumberedSourceSyntaxControls.type_cache_correct

theorem truth_term_cache : TermCacheCorrect truthSymbols NumberedSourceSyntaxControls.typeRows
    NumberedSourceSyntaxControls.termRows NumberedSourceSyntaxControls.termCache :=
  termCache_transport ((preserves?_eq_true_iff _ _).mp truth_preserves_literal_prefix) _ _ _
    NumberedSourceSyntaxControls.term_cache_correct

/-- The actual numbered envelope and cached truth body survive registration. -/
theorem actual_numbered_truth_retained :
    ∃ original body, NumberedSourceSyntaxControls.rawTerms.toList[4]? = some original ∧
      NumberedSourceInput.identifier? original = some 4 ∧ ExportCodec.at? original 1 = some body ∧
      NumberedSourceInputControls.termBodies[4]? = some body ∧
      TermAt truthSymbols NumberedSourceSyntaxControls.typeRows
        (fun index => NumberedSourceInputControls.termBodies[index]?) 4 NumberedSourceSyntaxControls.decodedTruth := by
  exact NumberedSourceRegistry.certified_term_readback truth_preserves_literal_prefix _ _ _
    NumberedSourceInputControls.terms_numbered NumberedSourceSyntaxControls.termCache
    NumberedSourceInputControls.cache_correct_for_bodies 4 NumberedSourceSyntaxControls.decodedTruth
    (Option.some_get NumberedSourceSyntaxControls.term_four_available).symm

def hiddenBefore : ExportCodec.Symbols :=
  { initialSymbols with constants := initialSymbols.constants ++
    [("=", StandardTheoryInterpretation.Source.truthResult.output.constant),
      ("@", StandardTheoryInterpretation.Source.truthResult.output.constant)] }

def hiddenReordered : ExportCodec.Symbols :=
  { initialSymbols with constants := initialSymbols.constants ++
    [("@", Const.equality), ("=", ModelInterpretation.selectionConstant)] }

theorem hidden_duplicates_reflexive : preserves? hiddenBefore hiddenBefore = true :=
  (preserves?_eq_true_iff _ _).mpr (LookupPreserving.refl _)

theorem hidden_duplicates_may_be_dropped : preserves? hiddenBefore initialSymbols = true := by decide +kernel
theorem hidden_duplicates_may_change_and_reorder : preserves? hiddenBefore hiddenReordered = true := by decide +kernel

theorem same_value_prepend_allowed :
    preserves? initialSymbols { initialSymbols with constants := ("=", Const.equality) :: initialSymbols.constants } = true := by decide +kernel

/-- This deliberately mismaps the visible key T to the registered equality. -/
def shadowBefore : ExportCodec.Symbols :=
  { initialSymbols with constants := ("T", Const.equality) :: initialSymbols.constants }

def mismappedInitial : SourceDAGReceive.Reading := { initial with symbols := shadowBefore }

def shadowAfter : ExportCodec.Symbols :=
  { shadowBefore with constants :=
    ("T", StandardTheoryInterpretation.Source.truthResult.output.constant) :: shadowBefore.constants }

theorem admission_alone_does_not_preserve_lookups :
    admitConstantInTheory mismappedInitial.registered.registered.context
      (ExportReplay.instanceCertificates mismappedInitial.registered.registered.context.signature)
      (.global "T") NumberedSourceSyntaxControls.decodedTruth =
        some StandardTheoryInterpretation.Source.truthResult ∧
      preserves? shadowBefore shadowAfter = false :=
  ⟨actual_truth_admitted, by decide +kernel⟩

def annotation : Ty := Ty.function (Ty.function Ty.bool Ty.bool)
  (Ty.function (Ty.function Ty.bool Ty.bool) Ty.bool)

def shadowRaw : Json := .arr #[.str "const", .str "T", .num 3]
def shadowRows (index : Nat) : Option Json := if index = 0 then some shadowRaw else none
def oldTerm : SourceTerm := .const Const.equality annotation
def newTerm : SourceTerm := .const StandardTheoryInterpretation.Source.truthResult.output.constant annotation

theorem old_shadow_read : TermAt shadowBefore NumberedSourceSyntaxControls.typeRows shadowRows 0 oldTerm := by
  refine .constant rfl rfl rfl ?_
  exact typeAt_transport ((preserves?_eq_true_iff _ _).mp (by decide +kernel :
    preserves? NumberedSourceSyntaxControls.symbols shadowBefore = true)) _ 3 annotation
      (NumberedSourceSyntaxControls.type_cache_correct 3 annotation rfl)

theorem old_shadow_signature_checked :
    (checkSource initial.registered.registered.context.signature
      (ExportReplay.instanceCertificates initial.registered.registered.context.signature) oldTerm).isSome = true := by decide +kernel

theorem new_shadow_read : TermAt shadowAfter NumberedSourceSyntaxControls.typeRows shadowRows 0 newTerm := by
  refine .constant rfl rfl rfl ?_
  exact typeAt_transport ((preserves?_eq_true_iff _ _).mp (by decide +kernel :
    preserves? NumberedSourceSyntaxControls.symbols shadowAfter = true)) _ 3 annotation
      (NumberedSourceSyntaxControls.type_cache_correct 3 annotation rfl)

theorem old_shadow_read_not_retained :
    ¬ TermAt shadowAfter NumberedSourceSyntaxControls.typeRows shadowRows 0 oldTerm := by
  intro old
  have equal := NumberedSourceSyntax.term_unique shadowAfter NumberedSourceSyntaxControls.typeRows shadowRows
    0 oldTerm newTerm old new_shadow_read
  have same := (SourceTerm.same_eq_true_iff oldTerm newTerm).mpr equal
  have different : SourceTerm.same oldTerm newTerm = false := by decide +kernel
  rw [different] at same
  cases same

/-- Failure of the whole-visible check need not affect a cache that uses
neither the rebound key nor any node depending on it. No support checker is
introduced here. -/
theorem unrelated_truth_cache_survives_shadow :
    preserves? shadowBefore shadowAfter = false ∧
      TermCacheCorrect shadowBefore NumberedSourceSyntaxControls.typeRows
        NumberedSourceSyntaxControls.termRows NumberedSourceSyntaxControls.termCache ∧
      TermCacheCorrect shadowAfter NumberedSourceSyntaxControls.typeRows
        NumberedSourceSyntaxControls.termRows NumberedSourceSyntaxControls.termCache := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · exact termCache_transport ((preserves?_eq_true_iff _ _).mp (by decide +kernel :
      preserves? NumberedSourceSyntaxControls.symbols shadowBefore = true)) _ _ _ NumberedSourceSyntaxControls.term_cache_correct
  · exact termCache_transport ((preserves?_eq_true_iff _ _).mp (by decide +kernel :
      preserves? NumberedSourceSyntaxControls.symbols shadowAfter = true)) _ _ _ NumberedSourceSyntaxControls.term_cache_correct

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceRegistryControls
