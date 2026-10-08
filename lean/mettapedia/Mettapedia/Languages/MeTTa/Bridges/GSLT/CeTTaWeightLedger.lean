import Mettapedia.Algebra.SharedCoefficientLedger
import Mettapedia.GSLT.Dynamics.WeightedBranchingResumption
import Mettapedia.Machines.NativeCostLedger
import Mettapedia.GSLT.LanguageDef.NativeOpsCNormalization
import Mettapedia.GSLT.LanguageDef.NativeOpsCFunctionComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsReferenceFieldLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsShortCircuitTarget
import Mettapedia.GSLT.LanguageDef.NativeOpsRunComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsTargetParameterFacts

/-!
# CeTTa's shared-factor comparison through the common C reader

The actual `factor_equal` function reads occurrence, dependency and coefficient
in that order. The shared C reader retains its const-qualified prototype and
checks its declared record alias before lowering the original body. Execution
uses the same short-circuit and invocation construction as other native clients.

The record layout and live borrowed cells are explicit boundaries. The
`atom_eq` service has its own value/dialect contract; a type or symbol does
not establish that contract. Fresh parameter storage is allocated and released
in the target model, preserving the whole caller state. The service's compiled
implementation, physical layout and concurrent memory are separate obligations.
The readout section connects chronological native factor records and scoped
claims to the common resumable snapshot fold. Its normalization service and
complete task carrier are explicit parameters. A callback may change the
whole supplied world; a pure monoid interpretation is a separate instance.
These models and finite native service comparisons do not establish whole
compiled-function or ISO C compiler refinement.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaWeightLedger

open Mettapedia.GSLT.LanguageDef.NativeOps
open NativeIR (Atom Instruction)

def atomEquality : External :=
  ⟨⟨"atom_eq", [⟨"left", .ref (.named "Atom")⟩,
    ⟨"right", .ref (.named "Atom")⟩], .bool⟩, "atom_eq", .pure, none⟩

/-- Positional layout of the independently supplied factor record. The
linked predecessor is present even though this comparison does not read it. -/
def interface : Interface :=
  ⟨[⟨"WeightFactor", [⟨"previous", .ref (.named "WeightFactor")⟩,
      ⟨"occurrence", .word⟩, ⟨"dependency", .word⟩,
      ⟨"value", .ref (.named "Atom")⟩]⟩],
    [⟨"Atom", "Atom", "atom.h"⟩], [], [atomEquality]⟩

def representation : NativeC.Representation := ⟨"WeightLedger", interface, []⟩

def bindings : NativeC.PrimitiveBindings :=
  [("left".toList, .temporary 1 (.ref (.named "WeightFactor"))),
   ("right".toList, .temporary 2 (.ref (.named "WeightFactor")))]

def factorBody : List Char := "{\n    return left->occurrence == right->occurrence &&\n        left->dependency == right->dependency &&\n        atom_eq(left->value, right->value);\n}".toList

def factorSource : List Char := "static bool factor_equal(const CettaWeightFactor *left,\n                         const CettaWeightFactor *right) {\n    return left->occurrence == right->occurrence &&\n        left->dependency == right->dependency &&\n        atom_eq(left->value, right->value);\n}".toList

def factorHeader : Header :=
  ⟨"factor_equal", [⟨"left", .ref (.named "WeightFactor")⟩,
    ⟨"right", .ref (.named "WeightFactor")⟩], .bool⟩

def factorAliases : NativeC.RecordAliases := [("CettaWeightFactor".toList, "WeightFactor")]

def factorTypes : NativeC.TypeNames := ["bool".toList, "CettaWeightFactor".toList]

private def factorTokens : List NativeC.Token :=
  [.punctuation ['{'], .identifier "return".toList,
   .identifier "left".toList, .punctuation ['-', '>'], .identifier "occurrence".toList,
   .punctuation ['=', '='], .identifier "right".toList, .punctuation ['-', '>'],
   .identifier "occurrence".toList, .punctuation ['&', '&'],
   .identifier "left".toList, .punctuation ['-', '>'], .identifier "dependency".toList,
   .punctuation ['=', '='], .identifier "right".toList, .punctuation ['-', '>'],
   .identifier "dependency".toList, .punctuation ['&', '&'],
   .identifier "atom_eq".toList, .punctuation ['('],
   .identifier "left".toList, .punctuation ['-', '>'], .identifier "value".toList,
   .punctuation [','], .identifier "right".toList, .punctuation ['-', '>'],
   .identifier "value".toList, .punctuation [')'], .punctuation [';'], .punctuation ['}']]

private theorem factor_lexed : NativeC.lex factorBody = .ok factorTokens := by
  decide +kernel

private def factorSourceTokens : List NativeC.Token :=
  [.identifier "static".toList, .identifier "bool".toList,
   .identifier "factor_equal".toList, .punctuation ['('],
   .identifier "const".toList, .identifier "CettaWeightFactor".toList,
   .punctuation ['*'], .identifier "left".toList, .punctuation [','],
   .identifier "const".toList, .identifier "CettaWeightFactor".toList,
   .punctuation ['*'], .identifier "right".toList, .punctuation [')']] ++ factorTokens

private theorem factor_source_lexed : NativeC.lex factorSource = .ok factorSourceTokens := by
  decide +kernel

private def cField (side member : String) : NativeC.CExpr :=
  .field (.identifier side.toList) member.toList true

def factorExpression : NativeC.CExpr :=
  .binary .and
    (.binary .and
      (.binary .eq (cField "left" "occurrence") (cField "right" "occurrence"))
      (.binary .eq (cField "left" "dependency") (cField "right" "dependency")))
    (.call "atom_eq".toList [cField "left" "value", cField "right" "value"])

/-- Actual positional address/load instructions, with no inserted null guard. -/
def fieldCode (side : Nat) (index : Nat) (type : NativeType) (first : Nat) :
    List Instruction :=
  fieldReadCode (.temporary side (.ref (.named "WeightFactor"))) "WeightFactor" index first type

def wordComparisonCode (index first : Nat) : List Instruction :=
  fieldCode 1 index .word first ++ fieldCode 2 index .word (first + 2) ++
    [.temporary (first + 4) .bool
      (.binary (.compare .eq) (.temporary (first + 1) .word) (.temporary (first + 3) .word))]

def coefficientCode : List Instruction :=
  fieldCode 1 3 (.ref (.named "Atom")) 15 ++
  fieldCode 2 3 (.ref (.named "Atom")) 17 ++
  [.call (some (.temporary 19 .bool)) (.external "atom_eq")
    [.temporary 16 (.ref (.named "Atom")), .temporary 18 (.ref (.named "Atom"))]]

def factorCode : List Instruction :=
  wordComparisonCode 1 3 ++
  [.temporary 8 .bool (.copy (.temporary 7 .bool)),
   .branch (.value (.temporary 8 .bool))
     (wordComparisonCode 2 9 ++ [.assign (.temporary 8 .bool) (.temporary 13 .bool)]) [],
   .temporary 14 .bool (.copy (.temporary 8 .bool)),
   .branch (.value (.temporary 14 .bool))
     (coefficientCode ++ [.assign (.temporary 14 .bool) (.temporary 19 .bool)]) [],
   .return (.temporary 14 .bool)]

def factorParsed : NativeC.CQualifiedFunction :=
  ⟨⟨"bool".toList, 0⟩, "factor_equal".toList,
    [⟨⟨⟨"CettaWeightFactor".toList, 1⟩, "left".toList⟩, true⟩,
     ⟨⟨⟨"CettaWeightFactor".toList, 1⟩, "right".toList⟩, true⟩],
    [.return (some factorExpression)]⟩

def factorFunction : NativeIR.Function :=
  ⟨factorHeader, NativeC.primitiveParameterCapture factorHeader.parameters ++ factorCode, 19⟩

theorem factor_source_parsed : NativeC.qualifiedFunction? (2 * factorSourceTokens.length + 4)
    factorTypes (NativeC.ordinaryFunctionTokens factorSourceTokens) = some (factorParsed, []) := by
  rfl

/-- The original prototype retains both const pointees. The record spelling
is mapped by a declared layout alias before the common body lowerer is used. -/
theorem factor_source_admitted : NativeC.qualifiedReadOnlyFunctionText? representation
    factorTypes factorHeader factorAliases [true, true] [] factorSource = some factorFunction := by
  rw [NativeC.qualified_readonly_text_of_parts representation factorTypes factorHeader factorAliases
    [true, true] [] factorSource factorSourceTokens factorParsed factor_source_lexed factor_source_parsed]
  rfl

theorem factor_missing_layout_alias_refused : NativeC.qualifiedReadOnlyFunctionText? representation
    factorTypes factorHeader [] [true, true] [] factorSource = none := by
  rw [NativeC.qualified_readonly_text_of_parts representation factorTypes factorHeader []
    [true, true] [] factorSource factorSourceTokens factorParsed factor_source_lexed factor_source_parsed]
  rfl

theorem factor_qualifications_not_discarded : NativeC.qualifiedReadOnlyFunctionText? representation
    factorTypes factorHeader factorAliases [false, false] [] factorSource = none := by
  rw [NativeC.qualified_readonly_text_of_parts representation factorTypes factorHeader factorAliases
    [false, false] [] factorSource factorSourceTokens factorParsed factor_source_lexed factor_source_parsed]
  rfl

theorem factor_lost_const_refused : NativeC.qualifiedReadOnlyFunction? representation factorHeader
    factorAliases [true, true] [] 50
    { factorParsed with parameters := (factorParsed.parameters.map
        (fun parameter => { parameter with pointeeConst := false })) } = none := by rfl

theorem factor_duplicate_alias_refused : NativeC.qualifiedReadOnlyFunction? representation factorHeader
    (factorAliases ++ factorAliases) [true, true] [] 50 factorParsed = none := by rfl

theorem factor_undeclared_layout_refused : NativeC.qualifiedReadOnlyFunction? representation factorHeader
    [("CettaWeightFactor".toList, "MissingRecord")] [true, true] [] 50 factorParsed = none := by rfl

theorem factor_effectful_service_refused : NativeC.qualifiedReadOnlyFunction?
    { representation with interface := { interface with externals := [{ atomEquality with effect := .effect }] } }
    factorHeader factorAliases [true, true] [] 50 factorParsed = none := by rfl

theorem factor_body_parsed : NativeC.blockText? [] factorBody =
    some [.return (some factorExpression)] := by
  unfold NativeC.blockText?
  rw [factor_lexed]
  rfl

theorem factor_body_admitted : NativeC.primitiveBodyText? [] bindings .bool factorBody ⟨2⟩
    [atomEquality] representation = some (factorCode, ⟨19⟩) := by
  unfold NativeC.primitiveBodyText?
  rw [factor_body_parsed]
  rfl

/-- Declaring the layout does not grant authority for its coefficient service. -/
theorem coefficient_service_required : NativeC.primitiveBodyText? [] bindings .bool factorBody ⟨2⟩
    [] representation = none := by
  unfold NativeC.primitiveBodyText?
  rw [factor_body_parsed]
  rfl

theorem missing_dependency_layout_refused :
    NativeC.primitiveExpression? bindings 10 (cField "left" "dependency") ⟨2⟩ [atomEquality]
      { representation with interface :=
        { interface with records := [⟨"WeightFactor", [⟨"occurrence", .word⟩]⟩] } } = none := by
  rfl

theorem wrong_coefficient_service_type_refused :
    NativeC.primitiveBodyText? [] bindings .bool factorBody ⟨2⟩
      [{ atomEquality with header := { atomEquality.header with result := .unit } }]
      representation = none := by
  unfold NativeC.primitiveBodyText?
  rw [factor_body_parsed]
  rfl

theorem trailing_body_source_refused : NativeC.primitiveBodyText? [] bindings .bool
    (factorBody ++ " trailing".toList) ⟨2⟩ [atomEquality] representation = none := by
  have extended : NativeC.lex (factorBody ++ " trailing".toList) =
      .ok (factorTokens ++ [.identifier "trailing".toList]) := by decide +kernel
  unfold NativeC.primitiveBodyText? NativeC.blockText?
  rw [extended]
  rfl

abbrev Factor (V : Type) :=
  Mettapedia.Algebra.SharedCoefficientLedger.Factor (BitVec 64) (BitVec 64) V

/-- The semantic comparison keeps all three factor fields. The coefficient
readout is separately supplied, so no equality law is granted to `atom_eq`. -/
def agrees {V : Type} (same : V → V → Bool) (left right : Factor V) : Bool :=
  decide (left.identity = right.identity) && decide (left.dependency = right.dependency) &&
    same left.coefficient right.coefficient

theorem agrees_iff {V : Type} (same : V → V → Bool) (left right : Factor V) :
    agrees same left right = true ↔
      left.identity = right.identity ∧ left.dependency = right.dependency ∧
        same left.coefficient right.coefficient = true := by
  simp [agrees, and_assoc]

/-- Ordinary factor equality is earned only on a coefficient profile whose
readout really decides coefficient equality. -/
theorem agrees_eq_iff {V : Type} (same : V → V → Bool)
    (law : ∀ left right, same left right = true ↔ left = right) (left right : Factor V) :
    agrees same left right = true ↔ left = right := by
  rw [agrees_iff, law]
  cases left
  cases right
  simp

theorem equal_values_do_not_merge_occurrences :
    agrees (fun left right : Nat => decide (left = right)) ⟨3, 7, 2⟩ ⟨4, 7, 2⟩ = false := by
  decide +kernel

theorem changed_dependency_is_not_shared :
    agrees (fun left right : Nat => decide (left = right)) ⟨3, 7, 2⟩ ⟨3, 8, 2⟩ = false := by
  decide +kernel

theorem same_occurrence_requires_coefficient_agreement :
    agrees (fun left right : Nat => decide (left = right)) ⟨3, 7, 2⟩ ⟨3, 7, 5⟩ = false := by
  decide +kernel

theorem nonreflexive_readout_is_not_factor_equality :
    agrees (fun _ _ : Nat => false) ⟨3, 7, 2⟩ ⟨3, 7, 2⟩ = false := by
  decide +kernel

private theorem field_code_exact {World : Type} {heap : TargetHeapSemantics World}
    {calls : TargetCalls World} {frame : TargetFrame} {state : TargetState World}
    {address : Address} {side lower first index : Nat} {type : NativeType} {value : TargetValue}
    (read : TargetAtomEval interface frame state
      (.temporary side (.ref (.named "WeightFactor"))) (.reference (some address)))
    (bounded : TemporaryNamesBound frame lower) (fresh : lower < first)
    (loaded : targetRead state.memory (sourceFieldAddress address index) = some value)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root (fieldCode side index type first) frame state out ↔
      out = ⟨.normal, fieldReadFrame frame address index first value, state⟩ :=
  field_read_code_exact read bounded fresh loaded "WeightFactor" root out

private def wordFrame (frame : TargetFrame) (leftAddress rightAddress : Address)
    (index first : Nat) (left right : BitVec 64) : TargetFrame :=
  targetDeclareTemporary
    (fieldReadFrame (fieldReadFrame frame leftAddress index first (.word left))
      rightAddress index (first + 2) (.word right))
    (first + 4) (.bool (left == right))

private theorem word_frame_bound {frame : TargetFrame} {lower first : Nat}
    (bounded : TemporaryNamesBound frame lower) (fresh : lower < first)
    (leftAddress rightAddress : Address) (index : Nat) (left right : BitVec 64) :
    TemporaryNamesBound (wordFrame frame leftAddress rightAddress index first left right)
      (first + 4) := by
  exact declared_temporary_bound
    (field_read_frame_bound (field_read_frame_bound bounded fresh _ _ _) (by omega) _ _ _)
    (by omega) (Nat.le_refl _) _

private theorem word_frame_protects {lower first : Nat} (frame : TargetFrame)
    (fresh : lower < first) (leftAddress rightAddress : Address) (index : Nat)
    (left right : BitVec 64) :
    TemporaryProtection lower frame
      (wordFrame frame leftAddress rightAddress index first left right) :=
  temporary_protection_trans
    (temporary_protection_trans (field_read_frame_protects frame fresh _ _ _)
      (field_read_frame_protects _ (by omega) _ _ _))
    (declare_temporary_protects _ _ (by omega))

private theorem word_frame_scoped {frame : TargetFrame} (hscope : TemporariesScoped frame)
    (leftAddress rightAddress : Address) (index first : Nat) (left right : BitVec 64) :
    TemporariesScoped (wordFrame frame leftAddress rightAddress index first left right) :=
  declared_temporaries_completeNames
    (field_read_frame_scoped (field_read_frame_scoped hscope _ _ _ _) _ _ _ _) _ _

private theorem word_comparison_exact {World : Type} {heap : TargetHeapSemantics World}
    {calls : TargetCalls World} {frame : TargetFrame} {state : TargetState World}
    {leftAddress rightAddress : Address} {lower first index : Nat} {left right : BitVec 64}
    (readLeft : TargetAtomEval interface frame state
      (.temporary 1 (.ref (.named "WeightFactor"))) (.reference (some leftAddress)))
    (readRight : TargetAtomEval interface frame state
      (.temporary 2 (.ref (.named "WeightFactor"))) (.reference (some rightAddress)))
    (bounded : TemporaryNamesBound frame lower) (inputs : 2 ≤ lower) (fresh : lower < first)
    (leftLoaded : targetRead state.memory (sourceFieldAddress leftAddress index) = some (.word left))
    (rightLoaded : targetRead state.memory (sourceFieldAddress rightAddress index) = some (.word right))
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root (wordComparisonCode index first) frame state out ↔
      out = ⟨.normal, wordFrame frame leftAddress rightAddress index first left right, state⟩ := by
  let middle := fieldReadFrame frame leftAddress index first (.word left)
  let last := fieldReadFrame middle rightAddress index (first + 2) (.word right)
  have protection :=  field_read_frame_protects frame fresh leftAddress index (.word left)
  have rightRead := (protection_atom_evaluation protection
    (.temporary 2 (.ref (.named "WeightFactor"))) inputs state state _).mp readRight
  have middleBound := field_read_frame_bound bounded fresh leftAddress index (.word left)
  have lastBound := field_read_frame_bound middleBound (show first + 1 < first + 2 by omega)
    rightAddress index (.word right)
  have firstRead : TargetAtomEval interface middle state (.temporary (first + 1) .word) (.word left) :=
    declared_temporary_atom interface _ state (first + 1) .word (.word left)
  have firstAtLast := (protection_atom_evaluation
    (field_read_frame_protects middle (show first + 1 < first + 2 by omega) rightAddress index (.word right))
    (.temporary (first + 1) .word) (Nat.le_refl _) state state _).mp firstRead
  have secondRead : TargetAtomEval interface last state (.temporary (first + 3) .word) (.word right) := by
    simpa only [last, fieldReadFrame, Nat.add_assoc] using
      (declared_temporary_atom interface _ state ((first + 2) + 1) .word (.word right))
  have compared : TargetPureEval interface last state
      (.binary (.compare .eq) (.temporary (first + 1) .word) (.temporary (first + 3) .word))
      (.bool (left == right)) := .binary firstAtLast secondRead rfl
  unfold wordComparisonCode
  rw [List.append_assoc]
  rw [target_normal_prefix_then_exact (by simp [fieldCode, fieldReadCode, jumpFreeCode, jumpFreeInstruction])
    (field_code_exact readLeft bounded fresh leftLoaded root)]
  rw [target_normal_prefix_then_exact (by simp [fieldCode, fieldReadCode, jumpFreeCode, jumpFreeInstruction])
    (field_code_exact rightRead middleBound (show first + 1 < first + 2 by omega) rightLoaded root)]
  exact target_run_temporary_exact (temporary_bound_fresh lastBound (by omega)) compared root out

private def coefficientFrame (frame : TargetFrame) (leftAddress rightAddress : Address)
    (leftAtom rightAtom : Option Address) (value : Bool) : TargetFrame :=
  targetDeclareTemporary
    (fieldReadFrame (fieldReadFrame frame leftAddress 3 15 (.reference leftAtom))
      rightAddress 3 17 (.reference rightAtom)) 19 (.bool value)

private theorem coefficient_frame_bound {frame : TargetFrame}
    (bounded : TemporaryNamesBound frame 14) (leftAddress rightAddress : Address)
    (leftAtom rightAtom : Option Address) (value : Bool) :
    TemporaryNamesBound (coefficientFrame frame leftAddress rightAddress leftAtom rightAtom value) 19 :=
  declared_temporary_bound
    (field_read_frame_bound (field_read_frame_bound bounded (by decide +kernel : 14 < 15) _ _ _)
      (by decide +kernel : 16 < 17) _ _ _) (by decide +kernel : 18 ≤ 19) (Nat.le_refl _) _

private theorem coefficient_frame_protects {lower : Nat} (frame : TargetFrame) (fresh : lower < 15)
    (leftAddress rightAddress : Address) (leftAtom rightAtom : Option Address) (value : Bool) :
    TemporaryProtection lower frame
      (coefficientFrame frame leftAddress rightAddress leftAtom rightAtom value) :=
  temporary_protection_trans
    (temporary_protection_trans (field_read_frame_protects frame fresh _ _ _)
      (field_read_frame_protects _ (by omega) _ _ _))
    (declare_temporary_protects _ _ (by omega))

private theorem coefficient_exact {World : Type} {heap : TargetHeapSemantics World}
    {calls : TargetCalls World} {frame : TargetFrame} {state : TargetState World}
    {leftAddress rightAddress : Address} {leftAtom rightAtom : Option Address} {value : Bool}
    (readLeft : TargetAtomEval interface frame state
      (.temporary 1 (.ref (.named "WeightFactor"))) (.reference (some leftAddress)))
    (readRight : TargetAtomEval interface frame state
      (.temporary 2 (.ref (.named "WeightFactor"))) (.reference (some rightAddress)))
    (bounded : TemporaryNamesBound frame 14)
    (leftLoaded : targetRead state.memory (sourceFieldAddress leftAddress 3) = some (.reference leftAtom))
    (rightLoaded : targetRead state.memory (sourceFieldAddress rightAddress 3) = some (.reference rightAtom))
    (action : ∀ raw post, calls (.external "atom_eq") [.reference leftAtom, .reference rightAtom]
        state raw post ↔ raw = .bool value ∧ post = state)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root coefficientCode frame state out ↔
      out = ⟨.normal, coefficientFrame frame leftAddress rightAddress leftAtom rightAtom value, state⟩ := by
  let middle := fieldReadFrame frame leftAddress 3 15 (.reference leftAtom)
  let last := fieldReadFrame middle rightAddress 3 17 (.reference rightAtom)
  have readRightAtMiddle := (protection_atom_evaluation
    (field_read_frame_protects frame (show 14 < 15 by decide +kernel) leftAddress 3 (.reference leftAtom))
    (.temporary 2 (.ref (.named "WeightFactor"))) (by decide +kernel : 2 ≤ 14) state state _).mp readRight
  have middleBound := field_read_frame_bound bounded (show 14 < 15 by decide +kernel)
    leftAddress 3 (.reference leftAtom)
  have lastBound := field_read_frame_bound middleBound (show 16 < 17 by decide +kernel)
    rightAddress 3 (.reference rightAtom)
  have firstRead : TargetAtomEval interface middle state
      (.temporary 16 (.ref (.named "Atom"))) (.reference leftAtom) :=
    declared_temporary_atom interface _ state 16 _ _
  have firstAtLast := (protection_atom_evaluation
    (field_read_frame_protects middle (show 16 < 17 by decide +kernel) rightAddress 3 (.reference rightAtom))
    (.temporary 16 (.ref (.named "Atom"))) (Nat.le_refl _) state state _).mp firstRead
  have secondRead : TargetAtomEval interface last state
      (.temporary 18 (.ref (.named "Atom"))) (.reference rightAtom) :=
    declared_temporary_atom interface _ state 18 _ _
  unfold coefficientCode
  rw [List.append_assoc]
  rw [target_normal_prefix_then_exact (by simp [fieldCode, fieldReadCode, jumpFreeCode, jumpFreeInstruction])
    (field_code_exact readLeft bounded (show 14 < 15 by decide +kernel) leftLoaded root)]
  rw [target_normal_prefix_then_exact (by simp [fieldCode, fieldReadCode, jumpFreeCode, jumpFreeInstruction])
    (field_code_exact readRightAtMiddle middleBound (show 16 < 17 by decide +kernel) rightLoaded root)]
  rw [target_normal_then_exact (target_call_temporary_instruction_exact
    (temporary_bound_fresh lastBound (show 18 < 19 by decide +kernel))
    (.cons firstAtLast (.cons secondRead .nil)) action)]
  exact target_run_empty_exact root _ state out

/-- A semantic factor with the addresses actually borrowed by this comparison.
Pointee meaning is supplied separately from the nominal `Atom` pointer type. -/
structure BorrowedFactor (V : Type) where
  address : Address
  coefficientAddress : Option Address
  factor : Factor V

/-- The three fields inspected by `factor_equal`, at their real positional
locations. The predecessor field is not read by this body. -/
def HasFactorCells {World V : Type} (state : TargetState World)
    (image : BorrowedFactor V) : Prop :=
  targetRead state.memory (sourceFieldAddress image.address 1) = some (.word image.factor.identity) ∧
  targetRead state.memory (sourceFieldAddress image.address 2) = some (.word image.factor.dependency) ∧
  targetRead state.memory (sourceFieldAddress image.address 3) = some (.reference image.coefficientAddress)

/-- Full private post-frame of the two authored short-circuit tests. Closing
each taken arm removes only that arm's temporary names. -/
def factorFrame {World V : Type} (frame : TargetFrame) (state : TargetState World)
    (left right : BorrowedFactor V) (same : V → V → Bool) : TargetFrame :=
  let occurrence := left.factor.identity == right.factor.identity
  let dependency := left.factor.dependency == right.factor.dependency
  let compared := wordFrame frame left.address right.address 1 3 left.factor.identity right.factor.identity
  let first := targetDeclareTemporary compared 8 (.bool occurrence)
  let checked := shortCircuitFrame true first
    (wordFrame first left.address right.address 2 9 left.factor.dependency right.factor.dependency)
    state 8 occurrence dependency
  let second := targetDeclareTemporary checked 14 (.bool (occurrence && dependency))
  shortCircuitFrame true second
    (coefficientFrame second left.address right.address left.coefficientAddress right.coefficientAddress
      (same left.factor.coefficient right.factor.coefficient))
    state 14 (occurrence && dependency) (same left.factor.coefficient right.factor.coefficient)

/-- Preservation and reflection for the body admitted from the original C
characters. The service contract is required at the actual two coefficient
addresses when both keys agree; it is not inferred from a service name, signature or algebra tag. -/
theorem factor_execution_exact {World V : Type} {heap : TargetHeapSemantics World}
    {calls : TargetCalls World} {frame : TargetFrame} {state : TargetState World}
    (left right : BorrowedFactor V) (same : V → V → Bool)
    (readLeft : TargetAtomEval interface frame state
      (.temporary 1 (.ref (.named "WeightFactor"))) (.reference (some left.address)))
    (readRight : TargetAtomEval interface frame state
      (.temporary 2 (.ref (.named "WeightFactor"))) (.reference (some right.address)))
    (bounded : TemporaryNamesBound frame 2) (hscope : TemporariesScoped frame)
    (leftCells : HasFactorCells state left) (rightCells : HasFactorCells state right)
    (action : left.factor.identity = right.factor.identity →
      left.factor.dependency = right.factor.dependency →
      ∀ raw post, calls (.external "atom_eq")
        [.reference left.coefficientAddress, .reference right.coefficientAddress] state raw post ↔
        raw = .bool (same left.factor.coefficient right.factor.coefficient) ∧ post = state)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root factorCode frame state out ↔
      out = ⟨.returned (.bool (agrees same left.factor right.factor)),
        factorFrame frame state left right same, state⟩ := by
  let occurrence := left.factor.identity == right.factor.identity
  let dependency := left.factor.dependency == right.factor.dependency
  let value := same left.factor.coefficient right.factor.coefficient
  let compared := wordFrame frame left.address right.address 1 3 left.factor.identity right.factor.identity
  let first := targetDeclareTemporary compared 8 (.bool occurrence)
  let current := wordFrame first left.address right.address 2 9 left.factor.dependency right.factor.dependency
  let checked := shortCircuitFrame true first current state 8 occurrence dependency
  let second := targetDeclareTemporary checked 14 (.bool (occurrence && dependency))
  let coefficient := coefficientFrame second left.address right.address
    left.coefficientAddress right.coefficientAddress value
  have comparedBound := word_frame_bound bounded (show 2 < 3 by decide +kernel)
    left.address right.address 1 left.factor.identity right.factor.identity
  have comparedScope := word_frame_scoped hscope left.address right.address 1 3
    left.factor.identity right.factor.identity
  have comparedProtection := word_frame_protects frame (show 2 < 3 by decide +kernel)
    left.address right.address 1 left.factor.identity right.factor.identity
  have occurrenceRead : TargetAtomEval interface compared state (.temporary 7 .bool) (.bool occurrence) :=
    declared_temporary_atom interface _ state 7 _ _
  have firstBound : TemporaryNamesBound first 8 :=
    declared_temporary_bound comparedBound (by decide +kernel : 7 ≤ 8) (Nat.le_refl _) _
  have firstScope := declared_temporaries_completeNames comparedScope 8 (.bool occurrence)
  have firstProtection := temporary_protection_trans comparedProtection
    (declare_temporary_protects compared (.bool occurrence) (by decide +kernel : 2 < 8))
  have leftAtFirst := (protection_atom_evaluation firstProtection
    (.temporary 1 (.ref (.named "WeightFactor"))) (by decide +kernel : 1 ≤ 2) state state _).mp readLeft
  have rightAtFirst := (protection_atom_evaluation firstProtection
    (.temporary 2 (.ref (.named "WeightFactor"))) (Nat.le_refl _) state state _).mp readRight
  have currentProtection := word_frame_protects first (show 8 < 9 by decide +kernel)
    left.address right.address 2 left.factor.dependency right.factor.dependency
  have currentLive : current.temporaryNames.contains 8 = true :=
    (currentProtection.names 8 (Nat.le_refl _)).trans (by simp [first, targetDeclareTemporary])
  have firstRead : TargetAtomEval interface first state (.temporary 8 .bool) (.bool occurrence) :=
    declared_temporary_atom interface compared state 8 _ _
  have dependencyRead : TargetAtomEval interface current state (.temporary 13 .bool) (.bool dependency) :=
    declared_temporary_atom interface _ state 13 _ _
  have dependencyExact := short_circuit_rhs_exact true (heap := heap) (calls := calls) firstScope firstRead
    (by simp [wordComparisonCode, fieldCode, fieldReadCode, jumpFreeCode, jumpFreeInstruction])
    (fun _ => word_comparison_exact leftAtFirst rightAtFirst firstBound (by decide +kernel : 2 ≤ 8)
      (by decide +kernel : 8 < 9) leftCells.2.1 rightCells.2.1)
    dependencyRead currentLive rfl
  have checkedBound := short_circuit_frame_bound true (current := current) firstBound state 8 occurrence dependency
  have checkedScope := short_circuit_frame_scoped true (current := current) firstScope state 8 occurrence dependency
  have checkedProtection := temporary_protection_trans firstProtection
    (short_circuit_frame_protects true firstScope
      (temporary_protection_weaken (by decide +kernel : 2 ≤ 8) currentProtection)
      (by decide +kernel : 2 < 8) state occurrence dependency)
  have checkedRead := short_circuit_frame_read true (value := dependency) firstRead currentLive rfl
  have secondBound : TemporaryNamesBound second 14 :=
    declared_temporary_bound checkedBound (by decide +kernel : 8 ≤ 14) (Nat.le_refl _) _
  have secondScope := declared_temporaries_completeNames checkedScope 14 (.bool (occurrence && dependency))
  have secondProtection := temporary_protection_trans checkedProtection
    (declare_temporary_protects checked (.bool (occurrence && dependency)) (by decide +kernel : 2 < 14))
  have leftAtSecond := (protection_atom_evaluation secondProtection
    (.temporary 1 (.ref (.named "WeightFactor"))) (by decide +kernel : 1 ≤ 2) state state _).mp readLeft
  have rightAtSecond := (protection_atom_evaluation secondProtection
    (.temporary 2 (.ref (.named "WeightFactor"))) (Nat.le_refl _) state state _).mp readRight
  have coefficientProtection := coefficient_frame_protects second (show 14 < 15 by decide +kernel)
    left.address right.address left.coefficientAddress right.coefficientAddress value
  have coefficientLive : coefficient.temporaryNames.contains 14 = true :=
    (coefficientProtection.names 14 (Nat.le_refl _)).trans (by simp [second, targetDeclareTemporary])
  have secondRead : TargetAtomEval interface second state (.temporary 14 .bool)
      (.bool (occurrence && dependency)) :=
    declared_temporary_atom interface checked state 14 _ _
  have valueRead : TargetAtomEval interface coefficient state (.temporary 19 .bool) (.bool value) :=
    declared_temporary_atom interface _ state 19 _ _
  have coefficientExact := short_circuit_rhs_exact true (heap := heap) (calls := calls)
    (rhs := coefficientCode) (current := coefficient) (ready := occurrence && dependency)
    secondScope secondRead
    (by simp [coefficientCode, fieldCode, fieldReadCode, jumpFreeCode, jumpFreeInstruction])
    (fun ready root out => by
      have equalKeys : left.factor.identity = right.factor.identity ∧
          left.factor.dependency = right.factor.dependency := by
        have readyKeys : ((left.factor.identity == right.factor.identity) &&
            (left.factor.dependency == right.factor.dependency)) = true := ready
        simpa only [Bool.and_eq_true, beq_iff_eq] using readyKeys
      exact coefficient_exact leftAtSecond rightAtSecond secondBound leftCells.2.2 rightCells.2.2
        (action equalKeys.1 equalKeys.2) root out)
    valueRead coefficientLive rfl
  have finalRead := short_circuit_frame_read true (value := value) secondRead coefficientLive rfl
  simp only [shortCircuitCondition, if_true] at dependencyExact coefficientExact
  simp only [if_true] at checkedRead finalRead
  have occurrenceEq : occurrence = decide (left.factor.identity = right.factor.identity) := by
    apply Bool.eq_iff_iff.mpr
    simp [occurrence]
  have dependencyEq : dependency = decide (left.factor.dependency = right.factor.dependency) := by
    apply Bool.eq_iff_iff.mpr
    simp [dependency]
  unfold factorCode
  rw [target_normal_prefix_then_exact
    (by simp [wordComparisonCode, fieldCode, fieldReadCode, jumpFreeCode, jumpFreeInstruction])
    (word_comparison_exact readLeft readRight bounded (Nat.le_refl _) (show 2 < 3 by decide +kernel)
      leftCells.1 rightCells.1 root)]
  rw [target_short_circuit_copy_exact
    (temporary_bound_fresh comparedBound (show 7 < 8 by decide +kernel)) occurrenceRead]
  rw [target_normal_then_exact dependencyExact]
  rw [target_short_circuit_copy_exact
    (temporary_bound_fresh checkedBound (show 8 < 14 by decide +kernel)) checkedRead]
  rw [target_normal_then_exact coefficientExact]
  simpa only [factorFrame, agrees, ← occurrenceEq, ← dependencyEq] using
    (target_return_then_exact finalRead root [] out)

/-- Distinct occurrence or dependency keys return false without any contract
on the coefficient service. The actual short-circuit branches keep the complete
state, including external state, unchanged. -/
theorem factor_key_mismatch_exact {World V : Type} {heap : TargetHeapSemantics World}
    {calls : TargetCalls World} {frame : TargetFrame} {state : TargetState World}
    (left right : BorrowedFactor V) (same : V → V → Bool)
    (readLeft : TargetAtomEval interface frame state
      (.temporary 1 (.ref (.named "WeightFactor"))) (.reference (some left.address)))
    (readRight : TargetAtomEval interface frame state
      (.temporary 2 (.ref (.named "WeightFactor"))) (.reference (some right.address)))
    (bounded : TemporaryNamesBound frame 2) (hscope : TemporariesScoped frame)
    (leftCells : HasFactorCells state left) (rightCells : HasFactorCells state right)
    (different : left.factor.identity ≠ right.factor.identity ∨
      left.factor.dependency ≠ right.factor.dependency)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root factorCode frame state out ↔
      out = ⟨.returned (.bool false), factorFrame frame state left right same, state⟩ := by
  have rejected : agrees same left.factor right.factor = false := by
    rcases different with occurrence | dependency
    · simp [agrees, occurrence]
    · simp [agrees, dependency]
  have exactBody := factor_execution_exact (heap := heap) (calls := calls) left right same readLeft readRight bounded hscope
    leftCells rightCells (fun occurrence dependency _ _ => False.elim
      (different.elim (fun unequal => unequal occurrence) (fun unequal => unequal dependency))) root out
  simpa only [rejected] using exactBody

/-- Both pointer parameters are stored in fresh invocation cells before
their values are captured by the ordinary body lowering. -/
def factorBound {World : Type} (state : TargetState World) (storage : Nat)
    (left right : Address) : TargetFrame × TargetState World :=
  let first := targetDeclareLocal (targetEmptyFrame storage) state "left"
    (.ref (.named "WeightFactor")) (.reference (some left))
  targetDeclareLocal first.1 first.2 "right" (.ref (.named "WeightFactor")) (.reference (some right))

private def factorCaptured (frame : TargetFrame) (left right : Address) : TargetFrame :=
  targetDeclareTemporary (targetDeclareTemporary frame 1 (.reference (some left)))
    2 (.reference (some right))

private theorem factor_parameters_readback {World : Type} (state : TargetState World)
    (storage : Nat) (left right : Address) :
    let bound := factorBound state storage left right
    targetLocalValue bound.1 bound.2 "left" = some (.reference (some left)) ∧
      targetLocalValue bound.1 bound.2 "right" = some (.reference (some right)) := by
  simp [factorBound, targetDeclareLocal, targetEmptyFrame, targetLocalValue,
    targetLocalAddress, targetRead, targetStoreCell, targetReadPath]

private theorem factor_capture_prefix_exact {World : Type}
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (left right : Address)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root factorFunction.body
      (factorBound state storage left right).1 (factorBound state storage left right).2 out ↔
      TargetRun interface heap calls .bool root factorCode
        (factorCaptured (factorBound state storage left right).1 left right)
        (factorBound state storage left right).2 out := by
  let bound := factorBound state storage left right
  obtain ⟨leftRead, rightRead⟩ := factor_parameters_readback state storage left right
  change TargetRun interface heap calls .bool root
    (.temporary 1 (.ref (.named "WeightFactor")) (.readLocal "left") ::
     .temporary 2 (.ref (.named "WeightFactor")) (.readLocal "right") :: factorCode)
      bound.1 bound.2 out ↔ _
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : bound.1.temporaryNames.contains 1 = false) (.local leftRead))]
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : (targetDeclareTemporary bound.1 1 (.reference (some left))).temporaryNames.contains 2 = false)
    (.local rightRead))]
  rfl

private theorem factor_cells_bound {World V : Type} (state : TargetState World)
    (storage : Nat) (left right : Address) (image : BorrowedFactor V)
    (fresh : targetFreshFrame state.memory storage) (cells : HasFactorCells state image) :
    HasFactorCells (factorBound state storage left right).2 image := by
  have separate := targetFreshFrame_storage_ne_read fresh cells.1
  change storage ≠ image.address.storage at separate
  change HasFactorCells { state with memory := (targetParameterMemory state.memory storage 0
    [.reference (some left), .reference (some right)]) } image
  have unchanged (index : Nat) := targetRead_parameter_memory_other_storage state.memory storage 0
    [.reference (some left), .reference (some right)] (sourceFieldAddress image.address index)
    (show (sourceFieldAddress image.address index).storage ≠ storage from Ne.symm separate)
  simpa only [HasFactorCells, unchanged] using cells

private theorem factor_frame_extent {World V : Type} (frame : TargetFrame)
    (state : TargetState World) (left right : BorrowedFactor V) (same : V → V → Bool) :
    (factorFrame frame state left right same).storage = frame.storage ∧
      (factorFrame frame state left right same).nextLocal = frame.nextLocal := by
  by_cases occurrence : left.factor.identity = right.factor.identity <;>
    by_cases dependency : left.factor.dependency = right.factor.dependency <;>
    simp [factorFrame, shortCircuitFrame, wordFrame, fieldReadFrame, coefficientFrame,
      targetDeclareTemporary, targetCloseBlock, targetLeaveScope, targetUpdateTemporary,
      occurrence, dependency]

private theorem factor_invocation_body_exact {World V : Type}
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (left right : BorrowedFactor V)
    (same : V → V → Bool) (fresh : targetFreshFrame state.memory storage)
    (leftCells : HasFactorCells state left) (rightCells : HasFactorCells state right)
    (action : left.factor.identity = right.factor.identity →
      left.factor.dependency = right.factor.dependency →
      ∀ raw post, calls (.external "atom_eq")
        [.reference left.coefficientAddress, .reference right.coefficientAddress]
        (factorBound state storage left.address right.address).2 raw post ↔
        raw = .bool (same left.factor.coefficient right.factor.coefficient) ∧
          post = (factorBound state storage left.address right.address).2)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    let bound := factorBound state storage left.address right.address
    TargetRun interface heap calls .bool root factorFunction.body bound.1 bound.2 out ↔
      out = ⟨.returned (.bool (agrees same left.factor right.factor)),
        factorFrame (factorCaptured bound.1 left.address right.address) bound.2 left right same, bound.2⟩ := by
  let bound := factorBound state storage left.address right.address
  dsimp only
  rw [factor_capture_prefix_exact]
  apply factor_execution_exact left right same
  · exact .temporary (by simp [factorCaptured, targetDeclareTemporary])
      (by simp [factorCaptured, targetDeclareTemporary])
  · exact .temporary (by simp [factorCaptured, targetDeclareTemporary])
      (by simp [factorCaptured, targetDeclareTemporary])
  · intro identity live
    have present : identity = 2 ∨ identity = 1 := by
      simpa [factorCaptured, factorBound, targetDeclareLocal, targetEmptyFrame,
        targetDeclareTemporary, List.contains_iff_mem] using live
    rcases present with rfl | rfl <;> decide +kernel
  · exact target_declared_names_complete _ _ _
      (target_declared_names_complete _ _ _ (by intro _ _; rfl))
  · exact factor_cells_bound state storage left.address right.address left fresh leftCells
  · exact factor_cells_bound state storage left.address right.address right fresh rightCells
  · exact action

private theorem factor_invocation_teardown {World V : Type}
    (state : TargetState World) (storage : Nat) (left right : BorrowedFactor V)
    (same : V → V → Bool) (fresh : targetFreshFrame state.memory storage) :
    let bound := factorBound state storage left.address right.address
    (targetLeaveScope (targetEmptyFrame storage)
      (factorFrame (factorCaptured bound.1 left.address right.address) bound.2 left right same)
      bound.2).2 = state := by
  let bound := factorBound state storage left.address right.address
  have parameters : targetBindParameters factorHeader.parameters
      [.reference (some left.address), .reference (some right.address)]
      (targetEmptyFrame storage) state = some bound := by rfl
  obtain ⟨_, _, _, stateExact⟩ := target_bind_parameters_facts factorHeader.parameters
    _ (targetEmptyFrame storage) state bound.1 bound.2 parameters
  obtain ⟨_, _, released⟩ := target_bound_parameters_release factorHeader.parameters
    _ storage state bound.1 bound.2 fresh parameters
  obtain ⟨sameStorage, sameExtent⟩ := factor_frame_extent
    (factorCaptured bound.1 left.address right.address) bound.2 left right same
  change { bound.2 with memory := (targetDropLocals bound.2.memory
    (factorFrame (factorCaptured bound.1 left.address right.address) bound.2 left right same).storage 0
    (factorFrame (factorCaptured bound.1 left.address right.address) bound.2 left right same).nextLocal) } = state
  rw [sameStorage, sameExtent]
  change { bound.2 with memory := targetDropLocals bound.2.memory storage 0 2 } = state
  change targetDropLocals bound.2.memory storage 0 2 = state.memory at released
  rw [released, stateExact]

/-- Complete invocation of the admitted original function, including its
parameter cells and their release. The service obligation is required only
at actual borrowed coefficient addresses and actual fresh invocation states. -/
theorem factor_invocation_exact {World V : Type}
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (left right : BorrowedFactor V) (same : V → V → Bool)
    (leftCells : HasFactorCells state left) (rightCells : HasFactorCells state right)
    (action : ∀ storage, targetFreshFrame state.memory storage →
      left.factor.identity = right.factor.identity → left.factor.dependency = right.factor.dependency →
      ∀ raw post, calls (.external "atom_eq")
        [.reference left.coefficientAddress, .reference right.coefficientAddress]
        (factorBound state storage left.address right.address).2 raw post ↔
        raw = .bool (same left.factor.coefficient right.factor.coefficient) ∧
          post = (factorBound state storage left.address right.address).2)
    (result : TargetRawResult World) :
    TargetFunctionBody interface heap calls factorFunction
      [.reference (some left.address), .reference (some right.address)] state result ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧
        result = ⟨.bool (agrees same left.factor right.factor), state⟩ := by
  constructor
  · intro ran
    cases ran with
    | @run storage frame bound out raw fresh parameters body returned =>
      have pair : (frame, bound) = factorBound state storage left.address right.address :=
        (Option.some.inj parameters).symm
      have frameEq : frame = (factorBound state storage left.address right.address).1 :=
        congrArg Prod.fst pair
      have stateEq : bound = (factorBound state storage left.address right.address).2 :=
        congrArg Prod.snd pair
      subst frame
      subst bound
      have exactBody := (factor_invocation_body_exact heap calls state storage left right same fresh
        leftCells rightCells (action storage fresh) factorFunction.body out).mp body
      have rawEq := TargetFlow.returned.inj
        (returned.symm.trans (congrArg TargetBlockOutcome.flow exactBody))
      refine ⟨⟨storage, fresh⟩, ?_⟩
      rw [rawEq, exactBody]
      exact congrArg (TargetRawResult.mk _) (factor_invocation_teardown state storage left right same fresh)
  · rintro ⟨⟨storage, fresh⟩, rfl⟩
    let bound := factorBound state storage left.address right.address
    let out : TargetBlockOutcome World := ⟨.returned (.bool (agrees same left.factor right.factor)),
      factorFrame (factorCaptured bound.1 left.address right.address) bound.2 left right same, bound.2⟩
    have body := (factor_invocation_body_exact heap calls state storage left right same fresh
      leftCells rightCells (action storage fresh) factorFunction.body out).mpr rfl
    have executed : TargetFunctionBody interface heap calls factorFunction
        [.reference (some left.address), .reference (some right.address)] state
        ⟨.bool (agrees same left.factor right.factor),
          (targetLeaveScope (targetEmptyFrame storage) out.frame out.state).2⟩ :=
      .run fresh (by rfl) body rfl
    simpa only [out, bound, factor_invocation_teardown state storage left right same fresh] using executed

/-- Different keys need no coefficient service even for a complete function
invocation. Its ordinary parameter cells are still allocated and released. -/
theorem factor_mismatched_invocation_exact {World V : Type}
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (left right : BorrowedFactor V) (same : V → V → Bool)
    (leftCells : HasFactorCells state left) (rightCells : HasFactorCells state right)
    (different : left.factor.identity ≠ right.factor.identity ∨
      left.factor.dependency ≠ right.factor.dependency) (result : TargetRawResult World) :
    TargetFunctionBody interface heap calls factorFunction
      [.reference (some left.address), .reference (some right.address)] state result ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧ result = ⟨.bool false, state⟩ := by
  have rejected : agrees same left.factor right.factor = false := by
    rcases different with occurrence | dependency
    · simp [agrees, occurrence]
    · simp [agrees, dependency]
  have checked := factor_invocation_exact heap calls state left right same leftCells rightCells
    (fun _ _ occurrence dependency _ _ => False.elim
      (different.elim (fun unequal => unequal occurrence) (fun unequal => unequal dependency))) result
  simpa only [rejected] using checked

namespace Controls

private def leftAddress : Address := ⟨11, 0, []⟩
private def rightAddress : Address := ⟨12, 0, []⟩
private def leftCoefficient : Address := ⟨21, 0, []⟩
private def rightCoefficient : Address := ⟨22, 0, []⟩

private def leftImage (factor : Factor Nat) : BorrowedFactor Nat :=
  ⟨leftAddress, some leftCoefficient, factor⟩
private def rightImage (factor : Factor Nat) : BorrowedFactor Nat :=
  ⟨rightAddress, some rightCoefficient, factor⟩

private def frame : TargetFrame :=
  ⟨0, 0, [], [1, 2], fun identity =>
    if identity = 1 then some (.reference (some leftAddress))
    else if identity = 2 then some (.reference (some rightAddress)) else none⟩

private def state (left right : Factor Nat) : TargetState Nat :=
  ⟨⟨fun storage element =>
    if storage = 11 ∧ element = 0 then some (.record "WeightFactor"
      [.reference (some ⟨31, 0, []⟩), .word left.identity, .word left.dependency,
        .reference (some leftCoefficient)])
    else if storage = 12 ∧ element = 0 then some (.record "WeightFactor"
      [.reference (some ⟨32, 0, []⟩), .word right.identity, .word right.dependency,
        .reference (some rightCoefficient)]) else none,
    fun _ => none⟩, none, true, false, 37, AllocatorStats.targetEmpty⟩

private theorem frame_bound : TemporaryNamesBound frame 2 := by
  intro identity live
  have present : identity = 1 ∨ identity = 2 := by
    simpa [frame, List.contains_iff_mem] using live
  rcases present with rfl | rfl <;> decide +kernel

private theorem frame_scoped : TemporariesScoped frame := by
  intro identity absent
  simp only [frame, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_false_iff, beq_eq_false_iff_ne] at absent
  simp [frame, absent.1, absent.2]

private theorem left_read (left right : Factor Nat) :
    TargetAtomEval interface frame (state left right)
      (.temporary 1 (.ref (.named "WeightFactor"))) (.reference (some leftAddress)) :=
  .temporary rfl rfl

private theorem right_read (left right : Factor Nat) :
    TargetAtomEval interface frame (state left right)
      (.temporary 2 (.ref (.named "WeightFactor"))) (.reference (some rightAddress)) :=
  .temporary rfl rfl

private theorem left_cells (left right : Factor Nat) :
    HasFactorCells (state left right) (leftImage left) := ⟨rfl, rfl, rfl⟩

private theorem right_cells (left right : Factor Nat) :
    HasFactorCells (state left right) (rightImage right) := ⟨rfl, rfl, rfl⟩

private def coefficientCalls (left right : Nat) : TargetCalls Nat :=
  fun target operands pre raw post => target = .external "atom_eq" ∧
    operands = [.reference (some leftCoefficient), .reference (some rightCoefficient)] ∧
    raw = .bool (decide (left = right)) ∧ post = pre

theorem complete_invocation_preserves_caller {heap : TargetHeapSemantics Nat} :
    TargetFunctionBody interface heap (coefficientCalls 9 9) factorFunction
      [.reference (some leftAddress), .reference (some rightAddress)]
      (state ⟨3, 7, 9⟩ ⟨3, 7, 9⟩) ⟨.bool true, state ⟨3, 7, 9⟩ ⟨3, 7, 9⟩⟩ := by
  let left : Factor Nat := ⟨3, 7, 9⟩
  let right : Factor Nat := ⟨3, 7, 9⟩
  apply (factor_invocation_exact heap (coefficientCalls 9 9) (state left right)
    (leftImage left) (rightImage right) (fun a b : Nat => decide (a = b))
    (left_cells left right) (right_cells left right) ?_ _).mpr
  · exact ⟨⟨0, rfl, fun _ => rfl⟩, rfl⟩
  · intro _ _ _ _ raw post
    simp [coefficientCalls, leftImage, rightImage, left, right]

theorem complete_key_mismatch_skips_unavailable_service {heap : TargetHeapSemantics Nat} :
    TargetFunctionBody interface heap (fun _ _ _ _ _ => False) factorFunction
      [.reference (some leftAddress), .reference (some rightAddress)]
      (state ⟨3, 7, 9⟩ ⟨4, 7, 9⟩) ⟨.bool false, state ⟨3, 7, 9⟩ ⟨4, 7, 9⟩⟩ := by
  let left : Factor Nat := ⟨3, 7, 9⟩
  let right : Factor Nat := ⟨4, 7, 9⟩
  exact (factor_mismatched_invocation_exact heap (fun _ _ _ _ _ => False) (state left right)
    (leftImage left) (rightImage right) (fun a b : Nat => decide (a = b))
    (left_cells left right) (right_cells left right) (.inl (by decide +kernel)) _).mpr
    ⟨⟨0, rfl, fun _ => rfl⟩, rfl⟩

/-- Different physical coefficient addresses may carry the same coefficient.
The actual field loads and service invocation return true and retain the whole
caller state, including its independent external value. -/
theorem equal_coefficients_at_distinct_addresses {heap : TargetHeapSemantics Nat} :
    ∃ out, TargetRun interface heap (coefficientCalls 9 9) .bool [] factorCode frame
      (state ⟨3, 7, 9⟩ ⟨3, 7, 9⟩) out ∧
      out.flow = .returned (.bool true) ∧ out.state = state ⟨3, 7, 9⟩ ⟨3, 7, 9⟩ := by
  let left : Factor Nat := ⟨3, 7, 9⟩
  let right : Factor Nat := ⟨3, 7, 9⟩
  let same := fun a b : Nat => decide (a = b)
  let out : TargetBlockOutcome Nat :=
    ⟨.returned (.bool true), factorFrame frame (state left right) (leftImage left)
      (rightImage right) same, state left right⟩
  refine ⟨out, ?_, rfl, rfl⟩
  apply (factor_execution_exact (leftImage left) (rightImage right) same
    (left_read left right) (right_read left right) frame_bound frame_scoped
    (left_cells left right) (right_cells left right) ?_ [] out).mpr
  · rfl
  · intro _ _ raw post
    simp [coefficientCalls, leftImage, rightImage, left, right, same]

/-- This execution has no available coefficient service. Different occurrence
keys nevertheless return false through the admitted original body. -/
theorem different_occurrences_skip_unavailable_service {heap : TargetHeapSemantics Nat} :
    ∃ out, TargetRun interface heap (fun _ _ _ _ _ => False) .bool [] factorCode frame
      (state ⟨3, 7, 9⟩ ⟨4, 7, 9⟩) out ∧
      out.flow = .returned (.bool false) ∧ out.state = state ⟨3, 7, 9⟩ ⟨4, 7, 9⟩ := by
  let left : Factor Nat := ⟨3, 7, 9⟩
  let right : Factor Nat := ⟨4, 7, 9⟩
  let same := fun a b : Nat => decide (a = b)
  let out : TargetBlockOutcome Nat :=
    ⟨.returned (.bool false), factorFrame frame (state left right) (leftImage left)
      (rightImage right) same, state left right⟩
  refine ⟨out, ?_, rfl, rfl⟩
  exact (factor_key_mismatch_exact (leftImage left) (rightImage right) same
    (left_read left right) (right_read left right) frame_bound frame_scoped
    (left_cells left right) (right_cells left right)
    (.inl (by decide +kernel)) [] out).mpr rfl

/-- Matching occurrence keys do not bypass a changed dependency revision. -/
theorem changed_dependencies_skip_unavailable_service {heap : TargetHeapSemantics Nat} :
    ∃ out, TargetRun interface heap (fun _ _ _ _ _ => False) .bool [] factorCode frame
      (state ⟨3, 7, 9⟩ ⟨3, 8, 9⟩) out ∧
      out.flow = .returned (.bool false) ∧ out.state = state ⟨3, 7, 9⟩ ⟨3, 8, 9⟩ := by
  let left : Factor Nat := ⟨3, 7, 9⟩
  let right : Factor Nat := ⟨3, 8, 9⟩
  let same := fun a b : Nat => decide (a = b)
  let out : TargetBlockOutcome Nat :=
    ⟨.returned (.bool false), factorFrame frame (state left right) (leftImage left)
      (rightImage right) same, state left right⟩
  refine ⟨out, ?_, rfl, rfl⟩
  exact (factor_key_mismatch_exact (leftImage left) (rightImage right) same
    (left_read left right) (right_read left right) frame_bound frame_scoped
    (left_cells left right) (right_cells left right)
    (.inr (by decide +kernel)) [] out).mpr rfl

/-- The selected coefficient service sees the two loaded coefficient addresses.
Even with identical keys it cannot publish true for unequal coefficients. -/
theorem unequal_coefficients_have_no_true_result {heap : TargetHeapSemantics Nat}
    (after : TargetFrame) (post : TargetState Nat) :
    ¬ TargetRun interface heap (coefficientCalls 9 10) .bool [] factorCode frame
      (state ⟨3, 7, 9⟩ ⟨3, 7, 10⟩) ⟨.returned (.bool true), after, post⟩ := by
  let left : Factor Nat := ⟨3, 7, 9⟩
  let right : Factor Nat := ⟨3, 7, 10⟩
  let same := fun a b : Nat => decide (a = b)
  have exactBody := factor_execution_exact (heap := heap) (calls := coefficientCalls 9 10)
    (leftImage left) (rightImage right) same (left_read left right) (right_read left right)
    frame_bound frame_scoped (left_cells left right) (right_cells left right)
    (by intro _ _ raw current; simp [coefficientCalls, leftImage, rightImage, left, right, same])
    [] ⟨.returned (.bool true), after, post⟩
  intro ran
  have flow := congrArg TargetBlockOutcome.flow (exactBody.mp ran)
  cases flow

end Controls

/-! ## Scoped native readout through the common fold

The factor fields use the native word representation. `Payload` contains the
remaining observed world and its authority; this section neither reconstructs
that payload from the coefficient nor supplies a new ownership framework.
`Job` is the complete retained task, not just its printed expression. Native
publication and scheduling have their own source-qualified comparisons.
-/

namespace Readout

open Mettapedia.Algebra

open Mettapedia.GSLT.Dynamics.WeightedBranchingResumption
open Mettapedia.GSLT.Dynamics.WeightedResumption

variable {V Payload Job Fault Grade : Type}

abbrev World (V Payload : Type) :=
  Payload × SharedCoefficientLedger.Scoped (BitVec 64) (BitVec 64) V (BitVec 64)

abbrev Cursor (V Job : Type) := SnapshotFold.Indexed (Factor V) Job
abbrev ReferenceCursor (V Job : Type) := SnapshotFold.Listed (Factor V) Job

/-- Validate the captured read world and claim the fixed source snapshot
before even the algebra's unit is normalized. The payload is retained whole. -/
def begin [DecidableEq V] (entry : SharedCoefficientLedger.Scoped (BitVec 64) (BitVec 64) V (BitVec 64))
    (received : World V Payload) (owner : BitVec 64) (unit : V)
    (normalize : V → World V Payload → Job) :
    Option (World V Payload × Cursor V Job) :=
  match SharedCoefficientLedger.Scoped.handle? entry received.2 owner with
  | none => none
  | some (handled, selected) =>
      let world := (received.1, handled)
      some (world, ⟨selected, 0, normalize unit world⟩)

/-- The reference selects a remaining list directly, rather than obtaining
its state by projecting the indexed execution. It reuses the common claim map. -/
def referenceBegin [DecidableEq V]
    (entry : SharedCoefficientLedger.Scoped (BitVec 64) (BitVec 64) V (BitVec 64))
    (received : World V Payload) (owner : BitVec 64) (unit : V)
    (normalize : V → World V Payload → Job) :
    Option (World V Payload × ReferenceCursor V Job) :=
  if SharedCoefficientLedger.Scoped.extendsCapture entry received.2 then
    let selected := SharedCoefficientLedger.Scoped.selected entry.productions.length received.2
    let world := (received.1, SharedCoefficientLedger.Scoped.handle entry.productions.length owner received.2)
    some (world, ⟨selected, 0, selected, normalize unit world⟩)
  else none

theorem begin_comparison [DecidableEq V]
    (entry : SharedCoefficientLedger.Scoped (BitVec 64) (BitVec 64) V (BitVec 64))
    (received : World V Payload) (owner : BitVec 64) (unit : V)
    (normalize : V → World V Payload → Job) :
    referenceBegin entry received owner unit normalize =
      (begin entry received owner unit normalize).map
        (fun prepared => (prepared.1, SnapshotFold.project prepared.2)) := by
  simp only [referenceBegin, begin, SharedCoefficientLedger.Scoped.handle?]
  split <;> simp [SnapshotFold.project]

theorem begin_retains_world_and_job [DecidableEq V]
    (entry : SharedCoefficientLedger.Scoped (BitVec 64) (BitVec 64) V (BitVec 64))
    (received : World V Payload) (owner : BitVec 64) (unit : V)
    (normalize : V → World V Payload → Job)
    {prepared : World V Payload × Cursor V Job}
    (accepted : begin entry received owner unit normalize = some prepared) :
    prepared.1.1 = received.1 ∧ prepared.1.2.productions = received.2.productions ∧
      prepared.2.snapshot = SharedCoefficientLedger.Scoped.selected entry.productions.length received.2 ∧
      prepared.2.index = 0 ∧ prepared.2.callback = normalize unit prepared.1 := by
  by_cases extended : SharedCoefficientLedger.Scoped.extendsCapture entry received.2 = true
  · simp only [begin, SharedCoefficientLedger.Scoped.handle?, extended, ite_true] at accepted
    cases accepted
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp [begin, SharedCoefficientLedger.Scoped.handle?, extended] at accepted

theorem begin_snapshot_claimed [DecidableEq V]
    (entry : SharedCoefficientLedger.Scoped (BitVec 64) (BitVec 64) V (BitVec 64))
    (received : World V Payload) (owner : BitVec 64) (unit : V)
    (normalize : V → World V Payload → Job)
    {prepared : World V Payload × Cursor V Job}
    (accepted : begin entry received owner unit normalize = some prepared)
    {factor : Factor V} (selected : factor ∈ prepared.2.snapshot) :
    prepared.1.2.claims factor.identity = some owner := by
  by_cases extended : SharedCoefficientLedger.Scoped.extendsCapture entry received.2 = true
  · simp only [begin, SharedCoefficientLedger.Scoped.handle?, extended, ite_true] at accepted
    cases accepted
    exact SharedCoefficientLedger.Scoped.selected_claimed _ _ _ selected
  · simp [begin, SharedCoefficientLedger.Scoped.handle?, extended] at accepted

/-- A prefix/claim refusal supplies no fold task. It is not an absent
normalization reply and gives no licence to discard the native child packet. -/
theorem refused_capture_does_not_start_fold [DecidableEq V]
    (entry : SharedCoefficientLedger.Scoped (BitVec 64) (BitVec 64) V (BitVec 64))
    (received : World V Payload) (owner : BitVec 64) (unit : V)
    (normalize : V → World V Payload → Job)
    (refused : SharedCoefficientLedger.Scoped.extendsCapture entry received.2 = false) :
    begin entry received owner unit normalize = none := by
  simp [begin, SharedCoefficientLedger.Scoped.handle?, refused]

/-- The native multiplication expression keeps the left accumulator,
right factor coefficient, descriptor and completed callback world. -/
def multiplyJob (call : V → V → V → World V Payload → Job) (multiplication : V)
    (value : V) (factor : Factor V) (world : World V Payload) : Job :=
  call multiplication value factor.coefficient world

abbrev source [One Grade] (callback : SnapshotFold.Callback Job V (World V Payload) Fault Grade)
    (call : V → V → V → World V Payload → Job) (multiplication : V) :=
  SnapshotFold.indexedSource callback (multiplyJob call multiplication)

abbrev referenceSource [One Grade]
    (callback : SnapshotFold.Callback Job V (World V Payload) Fault Grade)
    (call : V → V → V → World V Payload → Job) (multiplication : V) :=
  SnapshotFold.listedSource callback (multiplyJob call multiplication)

theorem fold_step_comparison [One Grade]
    (callback : SnapshotFold.Callback Job V (World V Payload) Fault Grade)
    (call : V → V → V → World V Payload → Job) (multiplication : V) (cursor : Cursor V Job) :
    referenceSource callback call multiplication (SnapshotFold.project cursor) =
      match source callback call multiplication cursor with
      | .inl result => .inl result
      | .inr alternatives =>
          .inr (alternatives.map fun next => (SnapshotFold.project next.1, next.2)) := by
  cases inspected : SnapshotFold.indexedSource callback (multiplyJob call multiplication) cursor <;>
    simpa only [referenceSource, source, inspected] using
      SnapshotFold.source_comparison callback (multiplyJob call multiplication) cursor

theorem completed_callback_starts_next_job [One Grade]
    (callback : SnapshotFold.Callback Job V (World V Payload) Fault Grade)
    (call : V → V → V → World V Payload → Job) (multiplication value : V)
    (cursor : Cursor V Job) (world : World V Payload) (factor : Factor V)
    (returned : callback cursor.callback = .inl (some (.inr value), world))
    (next : cursor.snapshot[cursor.index]? = some factor) :
    source callback call multiplication cursor =
      .inr [(⟨cursor.snapshot, cursor.index + 1,
        call multiplication value factor.coefficient world⟩, 1)] := by
  simp [source, SnapshotFold.indexedSource, returned, next, multiplyJob]

theorem finite_fold_comparison [Monoid Grade]
    (callback : SnapshotFold.Callback Job V (World V Payload) Fault Grade)
    (call : V → V → V → World V Payload → Job) (multiplication : V)
    (fuel : Nat) (cursor : Cursor V Job) :
    contributions (referenceSource callback call multiplication) fuel (SnapshotFold.project cursor) =
      (contributions (source callback call multiplication) fuel cursor).map
        (fun leaf => (Sum.map id SnapshotFold.project leaf.1, leaf.2)) :=
  SnapshotFold.contributions_comparison callback (multiplyJob call multiplication) fuel cursor

structure WeightedValue (V : Type) where
  subject : V
  coefficient : V
  provenance : List (Factor V)
  deriving DecidableEq, Repr

/-- Only a successful coefficient is wrapped as `Weighted`. Errors are
forwarded with their complete postworld before another factor is consumed. -/
def observe (subject : V) (result : SnapshotFold.Result (Factor V) V (World V Payload) Fault) :
    (Fault ⊕ WeightedValue V) × World V Payload :=
  (result.outcome.map id (fun value => ⟨subject, value, result.snapshot⟩), result.world)

theorem faults_forward_whole_world (subject : V) (snapshot : List (Factor V))
    (consumed : Nat) (fault : Fault) (world : World V Payload) :
    observe subject ⟨snapshot, consumed, .inl fault, world⟩ = (.inl fault, world) := rfl

theorem values_retain_original_provenance (subject value : V) (snapshot : List (Factor V))
    (consumed : Nat) (world : World V Payload) :
    observe (Fault := Fault) subject ⟨snapshot, consumed, .inr value, world⟩ =
      (.inr ⟨subject, value, snapshot⟩, world) := rfl

/-- A pure normalized monoid instance computes the ledger's ordered
denotation. It is not a law imposed on arbitrary authored normalization. -/
theorem pure_native_fold_denotation [Monoid V] [Monoid Grade]
    (snapshot : List (Factor V)) (world : World V Payload) :
    contributions
        (SnapshotFold.indexedSource (SnapshotFold.pureCallback (Fault := Fault))
          (SnapshotFold.pureMultiply SharedCoefficientLedger.Factor.coefficient))
        (snapshot.length + 1) (⟨snapshot, 0, (1, world)⟩ : Cursor V (V × World V Payload)) =
      [(.inl ⟨snapshot, snapshot.length, .inr (SharedCoefficientLedger.denote snapshot), world⟩,
        (1 : Grade))] :=
  SnapshotFold.pure_indexed_product_complete SharedCoefficientLedger.Factor.coefficient snapshot world

section ObservedRuns

open Mettapedia.GSLT.Core
open Mettapedia.Machines.NativeCostLedger.Recording (State ScopedCharge scopedController)
open InferenceControl (Controller Snapshot)

private abbrev FoldResult := SnapshotFold.Result (Factor V) V (World V Payload) Fault × Grade

variable [Monoid Grade]

/-- The indexed native cursor and independently defined remaining-list
cursor have the same globally scheduled cost-bearing prefixes under FIFO.
Charge comparison is a local service boundary: identities, destinations and
retention decisions must agree, not merely their eventual summed work. -/
theorem scoped_fold_run_comparison (maximum : Nat)
    (callback : SnapshotFold.Callback Job V (World V Payload) Fault Grade)
    (call : V → V → V → World V Payload → Job) (multiplication : V)
    (nativeCommands : Unit → Cursor V Job × Grade → Option (FoldResult (V := V)
      (Payload := Payload) (Fault := Fault) (Grade := Grade)) → List (Cursor V Job × Grade) →
        List (ScopedCharge 64))
    (referenceCommands : Unit → ReferenceCursor V Job × Grade → Option (FoldResult (V := V)
      (Payload := Payload) (Fault := Fault) (Grade := Grade)) → List (ReferenceCursor V Job × Grade) →
        List (ScopedCharge 64))
    (commands : ∀ memory node emission generated,
      nativeCommands memory node emission generated =
        referenceCommands memory (SnapshotFold.project node.1, node.2) emission
          (generated.map fun next => (SnapshotFold.project next.1, next.2)))
    (initialStore : Nat → State 64) (fuel : Nat)
    (snapshot : Snapshot (Cursor V Job × Grade)
      (FoldResult (V := V) (Payload := Payload) (Fault := Fault) (Grade := Grade))
      (Unit × (Nat → State 64))) :
    (Snapshot.run (Scheduled.system (source callback call multiplication))
      (scopedController maximum (Controller.fixed BranchingTemporal.Scheduler.breadthFirst)
        nativeCommands initialStore) fuel snapshot).mapNodes
          (fun next => (SnapshotFold.project next.1, next.2)) =
      Snapshot.run (Scheduled.system (referenceSource callback call multiplication))
        (scopedController maximum (Controller.fixed BranchingTemporal.Scheduler.breadthFirst)
          referenceCommands initialStore) fuel
        (snapshot.mapNodes (fun next => (SnapshotFold.project next.1, next.2))) := by
  apply Mettapedia.Machines.NativeCostLedger.Recording.scopedController_transport
    (transfer := id)
  · exact SnapshotFold.system_emissions callback (multiplyJob call multiplication)
  · exact SnapshotFold.system_successors callback (multiplyJob call multiplication)
  · intros; rfl
  · intros; exact List.map_append ..
  · intros; rfl
  · exact commands

/-- Recorded native fold prefixes transport the actual selected input,
emission and ordered successor capture, alongside the whole scoped store.
The source and reference keep their own fold implementations. Capacity and
omissions are transported rather than regenerated from successful results. -/
theorem recorded_scoped_fold_comparison (maximum : Nat)
    (callback : SnapshotFold.Callback Job V (World V Payload) Fault Grade)
    (call : V → V → V → World V Payload → Job) (multiplication : V)
    (nativeCommands : Unit → Cursor V Job × Grade → Option (FoldResult (V := V)
      (Payload := Payload) (Fault := Fault) (Grade := Grade)) → List (Cursor V Job × Grade) →
        List (ScopedCharge 64))
    (referenceCommands : Unit → ReferenceCursor V Job × Grade → Option (FoldResult (V := V)
      (Payload := Payload) (Fault := Fault) (Grade := Grade)) → List (ReferenceCursor V Job × Grade) →
        List (ScopedCharge 64))
    (commands : ∀ memory node emission generated,
      nativeCommands memory node emission generated =
        referenceCommands memory (SnapshotFold.project node.1, node.2) emission
          (generated.map fun next => (SnapshotFold.project next.1, next.2)))
    (initialStore : Nat → State 64) (capacity : Option Nat) (fuel : Nat)
    (snapshot : Snapshot (Cursor V Job × Grade)
      (FoldResult (V := V) (Payload := Payload) (Fault := Fault) (Grade := Grade))
      ((Unit × (Nat → State 64)) × Option (InferenceControl.Recording.Prefix
        (InferenceControl.Preparation.Capture (Cursor V Job × Grade)
          (FoldResult (V := V) (Payload := Payload) (Fault := Fault) (Grade := Grade)))))) :
    (Snapshot.run (Scheduled.system (source callback call multiplication))
      (InferenceControl.Recording.controller
        (scopedController maximum (Controller.fixed BranchingTemporal.Scheduler.breadthFirst)
          nativeCommands initialStore) InferenceControl.Recording.Replay.observe capacity)
      fuel snapshot).mapState (fun next => (SnapshotFold.project next.1, next.2))
        (InferenceControl.Recording.transferMemory id
          (InferenceControl.Preparation.Capture.mapNodes
            (fun next => (SnapshotFold.project next.1, next.2)))) =
      Snapshot.run (Scheduled.system (referenceSource callback call multiplication))
        (InferenceControl.Recording.controller
          (scopedController maximum (Controller.fixed BranchingTemporal.Scheduler.breadthFirst)
            referenceCommands initialStore) InferenceControl.Recording.Replay.observe capacity)
        fuel (snapshot.mapState (fun next => (SnapshotFold.project next.1, next.2))
          (InferenceControl.Recording.transferMemory id
            (InferenceControl.Preparation.Capture.mapNodes
              (fun next => (SnapshotFold.project next.1, next.2))))) := by
  apply InferenceControl.Recording.run_transport
  · exact SnapshotFold.system_emissions callback (multiplyJob call multiplication)
  · exact SnapshotFold.system_successors callback (multiplyJob call multiplication)
  · intros; rfl
  · intros; exact List.map_append ..
  · intro memory node emission generated
    simp only [scopedController, Controller.observing, Controller.fixed, commands]
    rfl
  · intros; rfl

end ObservedRuns

end Readout

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaWeightLedger
