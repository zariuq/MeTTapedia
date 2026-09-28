import Mettapedia.Languages.Agda.SourceEvidence.ProofRecovery
import Mettapedia.Languages.Agda.StaticSpecification.Examples

/-! Positive reconstruction and rejection controls for the actual proof codec. -/

namespace Mettapedia.Languages.Agda.SourceEvidence.Codec.Controls
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.StaticSpecification.Examples

/-- All five families reconstruct actual evidence, including a substituted
variable type and the complete typed function-eta derivation. -/
theorem context_roundtrip : decode (encodeFormCtx twoTypesFormed) =
    some ⟨.context twoTypes, twoTypesFormed⟩ := decode_encodeFormCtx _

theorem dependent_formation_roundtrip : decode (encodeFormTy substitutedOlderType) =
    some ⟨.formation twoTypes (.el 0 (.var 1)), substitutedOlderType⟩ := decode_encodeFormTy _

theorem spine_application_roundtrip : decode (encodeTyping orderedSpineResult) =
    some ⟨.typing .nil (constantFunction.applySpine orderedSpine) (Ty.universe 1),
      orderedSpineResult⟩ := decode_encodeTyping _

theorem beta_roundtrip : decode (encodeTermEq closedBeta) =
    some ⟨.termEquality .nil (closedIdentity.app (.sort 0)) (.sort 0) (Ty.universe 1),
      closedBeta⟩ := decode_encodeTermEq _

theorem eta_roundtrip : decode (encodeTermEq closedEta) =
    some ⟨.termEquality .nil closedIdentity
      (.lam (.bind (closedIdentity.weaken.app (.var 0)))) closedIdentityType, closedEta⟩ :=
  decode_encodeTermEq _

def universeReflexivity : TypeEq (.nil : RawContext 0) (Ty.universe 0) (Ty.universe 0) :=
  .refl (.universe .nil 0)

theorem type_equality_roundtrip : decode (encodeTypeEq universeReflexivity) =
    some ⟨.typeEquality .nil (Ty.universe 0) (Ty.universe 0), universeReflexivity⟩ :=
  decode_encodeTypeEq _

def noAbsTyping : Typing (.nil : RawContext 0) (.lam (.noBind (.sort 0)))
    (Ty.pi (Ty.universe 0) (.noBind (Ty.universe 1))) :=
  .lam (.universe .nil 0) (.universe typeContextFormed 1) (.sort 0 typeContextFormed)

theorem noAbs_roundtrip : decode (encodeTyping noAbsTyping) =
    some ⟨.typing .nil (.lam (.noBind (.sort 0)))
      (Ty.pi (Ty.universe 0) (.noBind (Ty.universe 1))), noAbsTyping⟩ :=
  decode_encodeTyping _

theorem free_variable_rejected : decodeTerm 0 (encodeTerm (.var (0 : Fin 1))) = none := rfl

theorem bound_variable_accepted :
    decodeAbs 0 (.pair (.atom 0) (encodeTerm (.var (0 : Fin 1)))) =
      some (.bind (.var 0)) := rfl

theorem noAbs_has_no_extra_scope :
    decodeAbs 0 (.pair (.atom 1) (encodeTerm (.var (0 : Fin 1)))) = none := rfl

theorem malformed_node_rejected : decode (.atom 17) = none := rfl

theorem unknown_rule_rejected : decode (.node 18 [] []) = none := rfl

theorem missing_sort_premise_rejected :
    decode (.node 3 [.atom 0, encodeContext .nil, .atom 0] []) = none := rfl

theorem extra_sort_premise_rejected :
    decode (.node 3 [.atom 0, encodeContext .nil, .atom 0]
      [encodeFormCtx .nil, encodeFormCtx .nil]) = none := rfl

theorem wrong_context_length_rejected :
    decode (.node 3 [.atom 1, encodeContext .nil, .atom 0] [encodeFormCtx .nil]) = none := rfl

theorem wrong_premise_family_rejected :
    decode (.node 3 [.atom 0, encodeContext .nil, .atom 0]
      [encodeTyping directSortTyping]) = none := by
  change (show Option Packed from do
    let Γ ← decodeContext 0 (encodeContext .nil)
    let h ← fit (.context Γ) (← decode (encodeTyping directSortTyping))
    return ⟨.typing Γ (.sort 0) (Ty.universe 1), Typing.sort 0 h⟩) = none
  simp [decode_encodeTyping, fit, Option.bind]


theorem swapped_formation_premises_rejected :
    decode (.node 1 [.atom 0, encodeContext .nil, encodeTy (Ty.universe 0 : Ty 0)]
      [encodeFormTy (FormTy.universe .nil 0), encodeFormCtx .nil]) = none := by
  change (show Option Packed from do
    let Γ ← decodeContext 0 (encodeContext .nil)
    let a ← decodeTy 0 (encodeTy (Ty.universe 0))
    let h0 ← fit (.context Γ) (← decode (encodeFormTy (FormTy.universe .nil 0)))
    let h1 ← fit (.formation Γ a) (← decode (encodeFormCtx .nil))
    return ⟨.context (Γ.snoc a), FormCtx.snoc h0 h1⟩) = none
  simp [decode_encodeFormTy, fit, Option.bind]

/-- A scoped but ill-formed telescope is legitimate raw data. -/
theorem malformed_context_is_scoped :
    decodeContext 1 (encodeContext malformedTelescope) = some malformedTelescope :=
  decode_encodeContext _

/-- No finite code can manufacture a derivation at this ill-formed index. -/
theorem malformed_context_has_no_proof_code (code : Code) :
    decodeAt (.context malformedTelescope) code = none := by
  cases h : decodeAt (.context malformedTelescope) code with
  | none => rfl
  | some d => exact (malformed_telescope_rejected ⟨d⟩).elim

theorem wrong_universe_has_no_proof_code (code : Code) :
    decodeAt (.typing (.nil : RawContext 0) (.sort 0) (Ty.universe 0)) code = none := by
  cases h : decodeAt (.typing (.nil : RawContext 0) (.sort 0) (Ty.universe 0)) code with
  | none => rfl
  | some d => exact (wrong_universe_rejected ⟨d⟩).elim

theorem wrong_outer_index_rejected :
    decodeAt (.typing (.nil : RawContext 0) (.sort 0) (Ty.universe 0))
      (encodeTyping directSortTyping) = none := wrong_universe_has_no_proof_code _

theorem direct_and_detour_codes_distinct :
    encodeNat (.typing .nil (.sort 0) (Ty.universe 1)) directSortTyping ≠
      encodeNat (.typing .nil (.sort 0) (Ty.universe 1)) detouredSortTyping := by
  intro equal
  exact retained_derivations_distinct (encodeNat_injective _ equal)

def first : TermEq (.nil : RawContext 0) (.sort 0) (.sort 0) (Ty.universe 1) :=
  .refl directSortTyping

def second : TermEq (.nil : RawContext 0) (.sort 0) (.sort 0) (Ty.universe 1) := .symm first

def firstThenSecond := TermEq.trans first second

def secondThenFirst := TermEq.trans second first

theorem ordered_receipts_distinct :
    encodeTermEq firstThenSecond ≠ encodeTermEq secondThenFirst := by
  simp [firstThenSecond, secondThenFirst, first, second, encodeTermEq]

theorem ordered_source_histories_distinct : firstThenSecond ≠ secondThenFirst := by
  intro equal
  exact ordered_receipts_distinct (congrArg encodeTermEq equal)

theorem both_orderings_reconstruct :
    decode (encodeTermEq firstThenSecond) =
      some ⟨.termEquality .nil (.sort 0) (.sort 0) (Ty.universe 1), firstThenSecond⟩ ∧
    decode (encodeTermEq secondThenFirst) =
      some ⟨.termEquality .nil (.sort 0) (.sort 0) (Ty.universe 1), secondThenFirst⟩ :=
  ⟨decode_encodeTermEq _, decode_encodeTermEq _⟩

/-- Natural-number serialization also returns the very same eta history. -/
theorem eta_natural_roundtrip :
    decodeNat (.termEquality .nil closedIdentity
      (.lam (.bind (closedIdentity.weaken.app (.var 0)))) closedIdentityType)
      (encodeNat (.termEquality .nil closedIdentity
        (.lam (.bind (closedIdentity.weaken.app (.var 0)))) closedIdentityType) closedEta) = some closedEta := decodeNat_encodeNat _ _

/-- Inhabitation-driven reconstruction retains a checked source derivation;
it is not promised to return the witness hidden in the Prop proof. -/
def recoveredBeta := recoverTermEquality (Nonempty.intro closedBeta)

def recoveredNoAbs := recoverTyping (Nonempty.intro noAbsTyping)

end Mettapedia.Languages.Agda.SourceEvidence.Codec.Controls
