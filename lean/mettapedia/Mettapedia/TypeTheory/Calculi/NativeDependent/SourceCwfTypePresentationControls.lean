import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfUniverseReadout

/-!
# Distinct original type presentations can have the same display family

A source CwF may retain two codes for one varying family. Their display
maps and complete native families coincide, although the original codes and
independently generated raw type declarations differ. Full faithfulness on
display maps and recovery of terms at a supplied source type therefore do
not imply injectivity on original type presentations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfTypePresentationControls

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open SourceCwfDeclarations SourceCwfUniverseReadout

def taggedFamilies : Cwf.{1, 0, 1, 0} where
  Ctx := Type
  Sub first second := first → second
  idS _ := fun value => value
  compS later earlier := fun value => later (earlier value)
  id_comp _ := rfl
  comp_id _ := rfl
  comp_assoc _ _ _ := rfl
  Ty context := Bool × (context → Type)
  tySub type before := ⟨type.1, fun value => type.2 (before value)⟩
  tySub_id _ := rfl
  tySub_comp _ _ _ := rfl
  Tm context type := ∀ value : context, type.2 value
  tmSub term before := fun value => term (before value)
  tmSub_id _ := rfl
  tmSub_comp _ _ _ := rfl
  ext context type := Σ value : context, type.2 value
  wk _ := fun value => value.1
  vz _ := fun value => value.2
  pair before _ term := fun value => ⟨before value, term value⟩
  wk_pair _ _ _ := rfl
  vz_pair _ _ _ := rfl
  pair_eta _ _ := rfl

abbrev firstType : taggedFamilies.Ty Nat := ⟨false, fun n => Fin (n + 1)⟩
abbrev secondType : taggedFamilies.Ty Nat := ⟨true, fun n => Fin (n + 1)⟩
abbrev presentation := raised taggedFamilies

theorem distinct_original_codes : firstType ≠ secondType := by
  intro equal
  have tags := congrArg (fun type : taggedFamilies.Ty Nat => type.1) equal
  exact Bool.false_ne_true tags

theorem equal_original_display_maps : taggedFamilies.wk firstType = taggedFamilies.wk secondType := rfl

theorem equal_generated_native_families :
    sourceMeaning (raisedType taggedFamilies firstType) =
      sourceMeaning (raisedType taggedFamilies secondType) := rfl

def firstRawType : TypeExpr (symbols presentation) 1 :=
  sourceType (raisedType taggedFamilies firstType) (.var 0)

def secondRawType : TypeExpr (symbols presentation) 1 :=
  sourceType (raisedType taggedFamilies secondType) (.var 0)

def presentationTag : TypeSymbol presentation → Bool
  | .object _ => false
  | .source type => type.down.1

theorem distinct_raw_declarations : firstRawType ≠ secondRawType := by
  intro equal
  have symbolsEqual := TypeExpr.family.inj equal |>.1
  have tags := congrArg presentationTag symbolsEqual
  exact Bool.false_ne_true tags

theorem distinct_presentations_same_complete_type_readout :
    (model presentation).evaluateType
        (objectScope (⟨raisedContext taggedFamilies Nat⟩ : Base presentation)) firstRawType =
      (model presentation).evaluateType
        (objectScope (⟨raisedContext taggedFamilies Nat⟩ : Base presentation)) secondRawType := by
  exact (source_type_read (raisedType taggedFamilies firstType)).trans
    ((congrArg some equal_generated_native_families).trans
      (source_type_read (raisedType taggedFamilies secondType)).symm)

theorem native_type_readout_does_not_recover_all_raw_presentations :
    ¬ ∃ recover : NativeLocalTypeFormers.NativeType
        (objectScope (⟨raisedContext taggedFamilies Nat⟩ : Base presentation)).1 →
        TypeExpr (symbols presentation) 1,
      recover (sourceMeaning (raisedType taggedFamilies firstType)) = firstRawType ∧
      recover (sourceMeaning (raisedType taggedFamilies secondType)) = secondRawType := by
  rintro ⟨recover, first, second⟩
  apply distinct_raw_declarations
  exact first.symm.trans ((congrArg recover equal_generated_native_families).trans second)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfTypePresentationControls
