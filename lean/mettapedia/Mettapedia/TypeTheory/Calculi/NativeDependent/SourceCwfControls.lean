import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfUniverseReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfCoherence

/-!
# Varying source types, actual substitution and empty-section controls

The original family model has distinct context, substitution and term
levels. Generated declarations retain a genuinely dependent finite family,
two different sections and a nonidentity substitution. Complete native
sections of an originally empty type cannot manufacture a source term.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfControls

open _root_.CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open SourceCwfDeclarations SourceCwfUniverseReadout

abbrev original := familiesCwf.{0}
abbrev presentation := raised original
abbrev context : original.Ctx := Nat
abbrev dependentType : original.Ty context := fun (n : Nat) => Fin (n + 1)

def diagonal : original.Tm context dependentType := fun n => ⟨n, Nat.lt_succ_self n⟩
def zeroSection : original.Tm context dependentType := fun n => ⟨0, Nat.zero_lt_succ n⟩
def successor : original.Sub context context := fun n => n + 1

def rawDiagonal : TermExpr (symbols presentation) 1 := sourceTerm (raisedTerm original diagonal)
def rawSubstitution : Substitution (symbols presentation) 1 1 :=
  originalSubstitution
    (show (⟨raisedContext original context⟩ : Base presentation) ⟶
      ⟨raisedContext original context⟩ from raisedSubstitution original successor)

def diagonalFormed : Derivation (signature presentation)
    (.term (objectContext (⟨raisedContext original context⟩ : Base presentation)) rawDiagonal
      (sourceType (raisedType original dependentType) (.var 0))) :=
  sourceTermFormed (raisedTerm original diagonal)

theorem raw_diagonal_full_readout :
    (model presentation).evaluateTerm
        (objectScope (⟨raisedContext original context⟩ : Base presentation)) rawDiagonal =
      some ⟨sourceMeaning (raisedType original dependentType), originalValue original diagonal⟩ :=
  source_term_read (raisedTerm original diagonal)

theorem diagonal_environment_and_witness (n : Nat) :
    let receipt := (originalValue original diagonal).val
      ⟨op (⟨raisedContext original context⟩ : Base presentation),
        ⟨PUnit.unit, raisedSubstitution original (original.idS context)⟩⟩
    (receipt.val.down n).1 = n ∧ (receipt.val.down n).2.val = n := ⟨rfl, rfl⟩

theorem substituted_environment_and_witness (n : Nat) :
    let receipt := (originalValue original diagonal).val
      ⟨op (⟨raisedContext original context⟩ : Base presentation),
        ⟨PUnit.unit, raisedSubstitution original successor⟩⟩
    (receipt.val.down n).1 = n + 1 ∧ (receipt.val.down n).2.val = n + 1 := ⟨rfl, rfl⟩

theorem full_substituted_raw_readout :
    (model presentation).evaluateTerm
        (objectScope (⟨raisedContext original context⟩ : Base presentation))
        (rawDiagonal.substitute rawSubstitution) =
      some ⟨(sourceMeaning (raisedType original dependentType)).reindex
        (originalMap (show (⟨raisedContext original context⟩ : Base presentation) ⟶
          ⟨raisedContext original context⟩ from raisedSubstitution original successor)),
        (Functor.sectionsFunctor _).map
          (sourceSubstitutionIso (raisedType original dependentType)
            (raisedSubstitution original successor)).hom
          (sourceValue (raisedTerm original (original.tmSub diagonal successor)))⟩ :=
  original_generated_substitution original diagonal successor

theorem section_recovery_retains_diagonal :
    recoverOriginalTerm original (originalValue original diagonal) = diagonal :=
  recover_originalValue original diagonal

theorem successor_is_nonidentity : successor ≠ original.idS context := by
  intro equal
  have value := congrArg (fun arrow : original.Sub context context => arrow 0) equal
  exact (by decide : (1 : Nat) ≠ 0) value

theorem distinct_source_sections : diagonal ≠ zeroSection := by
  intro equal
  have value := congrArg (fun term : original.Tm context dependentType => (term 1).val) equal
  exact (by decide : (1 : Nat) ≠ 0) value

theorem distinct_complete_native_sections : originalValue original diagonal ≠ originalValue original zeroSection :=
  fun equal => distinct_source_sections (originalValue_injective original equal)

theorem distinct_raw_parser_results :
    (model presentation).evaluateTerm (objectScope (⟨raisedContext original context⟩ : Base presentation))
        (sourceTerm (raisedTerm original diagonal)) ≠
      (model presentation).evaluateTerm (objectScope (⟨raisedContext original context⟩ : Base presentation))
        (sourceTerm (raisedTerm original zeroSection)) :=
  fun equal => distinct_source_sections ((original_parser_conservative original diagonal zeroSection).mp equal)

theorem diagonal_rejects_wrong_witness :
    ((originalValue original diagonal).val
      ⟨op (⟨raisedContext original context⟩ : Base presentation),
        ⟨PUnit.unit, raisedSubstitution original (original.idS context)⟩⟩).val.down (1 : Nat) |>.2.val ≠ 0 :=
  by decide

abbrev emptyType : original.Ty context := fun _ => PEmpty

theorem no_original_empty_section : ¬ Nonempty (original.Tm context emptyType) := by
  rintro ⟨term⟩
  exact PEmpty.elim (term 0)

theorem no_generated_empty_section :
    ¬ Nonempty ((sourceMeaning (raisedType original emptyType)).decoded.sections) := by
  rintro ⟨sectionValue⟩
  exact no_original_empty_section ⟨recoverOriginalTerm original sectionValue⟩

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfControls
