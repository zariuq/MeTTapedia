import Mettapedia.GSLT.LanguageDef.ModuleSource.BinaryCollectionInterpretation
import Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraExtractionControls
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Laws

/-!
# Binary collection lowering and interpretation controls

The actual replacement producer supplies both bare and wrapped declarations.
The generic whole-pattern theorem covers nested terms and binder bodies.
The interpreted word model retains order and multiplicity, while the source
equations justify the carrier model. Data-fibre readouts remain separate.
-/

set_option autoImplicit false
open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_file "../../../../../../metta/gslt/module/BinaryCollectionJoin.module"

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.BinaryCollectionControls

open Mettapedia.OSLF.MeTTaIL Syntax WellSorted ReplacementTransport CanonicalBags CollectionLaws
open BinaryCollectionLowering

abbrev sourceValue := AlgebraExtractionControls.sourceMonoidValue
abbrev old := AlgebraExtractionControls.binarySourceRule
abbrev bareRow := AlgebraExtractionControls.wordReplacement
def wrappedRow : Replacement :=
  { bareRow with rule := { bareRow.rule with collectionRepresentation := .wrapped } }

def result (row : Replacement) : Value :=
  (replaceRow sourceValue row).toOption.getD sourceValue

def source : LanguageDef := flattenRaw "Source" sourceValue
def target (row : Replacement) : LanguageDef := flattenRaw "Target" (result row)
def item : TypeExpr := .base "Item"
def free : FreeTypeContext := fun _ => some item

theorem coherent : TermLabelsCoherent sourceValue :=
  (checkTermLabelsCoherent_iff _).mp (by decide +kernel)
theorem valid : ModuleAlgebra.Valid sourceValue.entries.toFinset := by decide +kernel
theorem bare_accepted : replaceRow sourceValue bareRow = .ok (result bareRow) :=
  AlgebraExtractionControls.actual_word_replacement_succeeds
theorem wrapped_accepted : replaceRow sourceValue wrappedRow = .ok (result wrappedRow) := by
  have checked : (replaceRow sourceValue wrappedRow).isOk = true := by decide +kernel
  unfold result
  generalize actual : replaceRow sourceValue wrappedRow = computed at checked ⊢
  cases computed with
  | error _ => cases checked
  | ok _ => rfl

def one : GrammarRule :=
  { label := "One", category := "Item", params := [], syntaxPattern := [.terminal "one"] }

theorem original_selected {rule : GrammarRule} (member : rule ∈ source.terms)
    (label : rule.label = bareRow.old) : rule = old := by
  have inventory : source.terms = [one, old] := by decide +kernel
  rw [inventory] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exfalso
    have impossible : ("One" : String) = "Op" := label
    exact (by decide : ("One" : String) ≠ "Op") impossible
  · rfl

theorem all_patterns_typed (row : Replacement)
    (accepted : replaceRow sourceValue row = .ok (result row))
    (label : row.old = bareRow.old)
    (named : namedArguments? old row.rule = false)
    (shape : row.rule.params = [.simple "xs" (.collection .vec item)])
    (represented : checkRepresentation source (target row) old row.rule .vec = true)
    (context : FreeTypeContext) (bound : List TypeExpr) {pattern : Pattern} {type : TypeExpr}
    (typed : HasType source context bound pattern type) :
    HasType (target row) context bound (translated (target row) old row.rule .vec pattern) type := by
  obtain ⟨selected, _, selectedLabel, _, checked, signature⟩ :=
    signature_of_replaceRow sourceValue row accepted coherent valid "Source" "Target"
  have same := original_selected signature.selected (selectedLabel.trans label)
  subst selected
  exact BinaryCollectionLowering.typed signature ((checkRepresentation_iff _ _ _ _ _).mp represented)
    checked named shape context bound typed

def nested : Pattern := .apply "Op" [.apply "Op" [.fvar "x", .fvar "y"], .fvar "z"]
def underBinder : Pattern := .lambda none (.apply "Op" [.bvar 0, .apply "Op" [.fvar "x", .fvar "y"]])
def lowered (row : Replacement) (pattern : Pattern) : Pattern :=
  translated (target row) old row.rule .vec pattern

theorem nested_typed : HasType source free [] nested item :=
  checkHasType_sound (by decide +kernel)
theorem binder_typed : HasType source free [] underBinder (.arrow item item) :=
  checkHasType_sound (by decide +kernel)

theorem nested_bare_typed : HasType (target bareRow) free [] (lowered bareRow nested) item :=
  all_patterns_typed bareRow bare_accepted rfl (by decide +kernel) rfl (by decide +kernel) _ _ nested_typed
theorem nested_wrapped_typed : HasType (target wrappedRow) free [] (lowered wrappedRow nested) item :=
  all_patterns_typed wrappedRow wrapped_accepted rfl (by decide +kernel) rfl (by decide +kernel) _ _ nested_typed
theorem binder_bare_typed : HasType (target bareRow) free [] (lowered bareRow underBinder) (.arrow item item) :=
  all_patterns_typed bareRow bare_accepted rfl (by decide +kernel) rfl (by decide +kernel) _ _ binder_typed
theorem binder_wrapped_typed : HasType (target wrappedRow) free [] (lowered wrappedRow underBinder) (.arrow item item) :=
  all_patterns_typed wrappedRow wrapped_accepted rfl (by decide +kernel) rfl (by decide +kernel) _ _ binder_typed

theorem old_label : old.label = "Op" := by decide +kernel
theorem bare_label : bareRow.rule.label = "Word" := by rfl
theorem wrapped_label : wrappedRow.rule.label = "Word" := by rfl
theorem bare_lookup : (CoreReduction.bareLabels (target bareRow)).lookup "Word" = some .vec := by
  decide +kernel
theorem wrapped_lookup : (CoreReduction.bareLabels (target wrappedRow)).lookup "Word" = none := by
  decide +kernel

theorem bare_shape : lowered bareRow nested =
    .collection .vec [.collection .vec [.fvar "x", .fvar "y"] none, .fvar "z"] none := by
  simp [lowered, translated, nested, renameConstructor, old_label, bare_label, packing,
    CoreReduction.unwrap, bare_lookup]
theorem wrapped_shape : lowered wrappedRow nested =
    .apply "Word" [.collection .vec [.apply "Word" [.collection .vec [.fvar "x", .fvar "y"] none], .fvar "z"] none] := by
  simp [lowered, translated, nested, renameConstructor, old_label, wrapped_label, packing,
    CoreReduction.unwrap, wrapped_lookup]

theorem representation_is_not_interchangeable :
    checkHasType (target wrappedRow) free [] (lowered bareRow nested) item = false ∧
      checkHasType (target bareRow) free [] (lowered wrappedRow nested) item = false := by
  rw [bare_shape, wrapped_shape]
  decide +kernel

theorem packing_does_not_change_kind :
    checkHasType (target wrappedRow) free []
      (.apply "Word" [.collection .hashBag [.fvar "x", .fvar "y"] none]) item = false := by decide +kernel

theorem missing_commutativity_refuses_bag :
    (replaceRow sourceValue { bareRow with rule :=
      { bareRow.rule with params := [.simple "xs" (.collection .hashBag item)] } }).isOk = false := by
  decide +kernel

/-- The actual producer and the source equations earn the full model and the
generic interpretation theorem; the control supplies no target algebra laws. -/
theorem actual_model (row : Replacement)
    (accepted : replaceRow sourceValue row = .ok (result row))
    (label : row.old = bareRow.old)
    (named : namedArguments? old row.rule = false)
    (shape : row.rule.params = [.simple "xs" (.collection .vec item)])
    (represented : checkRepresentation source (target row) old row.rule .vec = true)
    (fresh : BinaryCollectionInterpretation.checkFreshLabel source old row.rule = true) :
    ∃ unit, ∃ model : Mettapedia.Algebra.Collections.Folds.Model (List Nat),
      model.fold [] = AlgebraExtractionControls.wordOperations unit [] ∧
      (∀ first second, model.fold [first, second] = first ++ second) ∧
      ∀ assignment context bound pattern type answer,
        HasType source context bound pattern type →
        AlgebraInterpretation.read? AlgebraExtractionControls.wordOperations assignment pattern = some answer →
        BinaryCollectionInterpretation.read? AlgebraExtractionControls.wordOperations assignment row.rule.label .vec model
          (lowered row pattern) = some answer := by
  have selected : sourceValue.entries.find? (·.label == (.term, row.old)) =
      some AlgebraExtractionControls.binarySourceItem := by rw [label]; decide +kernel
  obtain ⟨unit, model, empty, binary, _, read⟩ :=
    BinaryCollectionInterpretation.replacement_model accepted selected rfl coherent valid "Source" "Target"
      (by decide +kernel) named shape represented fresh AlgebraExtractionControls.wordOperations
      AlgebraExtractionControls.source_monoid_word_model
  refine ⟨unit, model, empty, fun first second => by
    simpa [AlgebraExtractionControls.wordOperations] using binary first second, ?_⟩
  intro assignment context bound pattern type answer typed computed
  exact (read assignment context bound pattern type answer typed computed).1

theorem bare_nested_interpretation :
    ∃ model : Mettapedia.Algebra.Collections.Folds.Model (List Nat), ∀ assignment,
      BinaryCollectionInterpretation.read? AlgebraExtractionControls.wordOperations assignment "Word" .vec model
        (lowered bareRow nested) = some (assignment "x" ++ assignment "y" ++ assignment "z") := by
  obtain ⟨_, model, _, _, interpreted⟩ := actual_model bareRow bare_accepted rfl
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
  exact ⟨model, fun assignment => interpreted assignment free [] nested item _ nested_typed (by
    simp [nested, AlgebraInterpretation.read?, AlgebraExtractionControls.wordOperations])⟩

theorem wrapped_nested_interpretation :
    ∃ model : Mettapedia.Algebra.Collections.Folds.Model (List Nat), ∀ assignment,
      BinaryCollectionInterpretation.read? AlgebraExtractionControls.wordOperations assignment "Word" .vec model
        (lowered wrappedRow nested) = some (assignment "x" ++ assignment "y" ++ assignment "z") := by
  obtain ⟨_, model, _, _, interpreted⟩ := actual_model wrappedRow wrapped_accepted rfl
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
  exact ⟨model, fun assignment => interpreted assignment free [] nested item _ nested_typed (by
    simp [nested, AlgebraInterpretation.read?, AlgebraExtractionControls.wordOperations])⟩

/-! The source fold and the existing normalizer share one interpretation. The
following declaration readouts are checks; the generic preservation theorem
is `BinaryCollectionInterpretation.read_lawNormal`. -/

def nestedWithUnit : Pattern := .apply "Op" [.apply "One" [], nested]

theorem nestedWithUnit_typed : HasType source free [] nestedWithUnit item :=
  checkHasType_sound (by decide +kernel)

theorem normalized_interpretation (row : Replacement)
    (accepted : replaceRow sourceValue row = .ok (result row))
    (named : namedArguments? old row.rule = false)
    (shape : row.rule.params = [.simple "xs" (.collection .vec item)])
    (represented : BinaryCollectionLowering.checkRepresentation source (target row) old row.rule .vec = true)
    (fresh : BinaryCollectionInterpretation.checkFreshLabel source old row.rule = true)
    (oldLabel : row.old = bareRow.old) :
    ∃ model : Mettapedia.Algebra.Collections.Folds.Model (List Nat), ∀ assignment,
      BinaryCollectionInterpretation.read? AlgebraExtractionControls.wordOperations assignment row.rule.label .vec model
        (lawNormal [⟨.vec, some "One"⟩] (lowered row nestedWithUnit)) =
          some (assignment "x" ++ assignment "y" ++ assignment "z") := by
  obtain ⟨_, model, _, binary, interpreted⟩ := actual_model row accepted oldLabel named shape represented fresh
  have empty : model.fold [] = [] := by
    simpa only [binary, List.append_nil] using model.fold_left_unit []
  have different : ("One" : String) ≠ row.rule.label := by
    intro same
    have prior : one ∈ source.terms := by decide +kernel
    have selected : one.label ≠ old.label := by decide +kernel
    exact (BinaryCollectionInterpretation.freshLabel_of_check fresh prior selected) same
  refine ⟨model, fun assignment => ?_⟩
  have read := interpreted assignment free [] nestedWithUnit item (assignment "x" ++ assignment "y" ++ assignment "z") nestedWithUnit_typed (by
    simp [nestedWithUnit, nested, AlgebraInterpretation.read?, AlgebraExtractionControls.wordOperations, List.append_assoc])
  apply BinaryCollectionInterpretation.read_lawNormal AlgebraExtractionControls.wordOperations assignment row.rule.label .vec model
    [⟨.vec, some "One"⟩] ?_ (fun _ _ => rfl) read
  intro law chosen unit selected
  change some ({kind := .vec, unit := some "One"} : Laws) = some law at chosen
  cases Option.some.inj chosen
  cases Option.some.inj selected
  exact ⟨different, by simpa [AlgebraExtractionControls.wordOperations] using empty.symm⟩

theorem bare_normalized_interpretation :
    ∃ model : Mettapedia.Algebra.Collections.Folds.Model (List Nat), ∀ assignment,
      BinaryCollectionInterpretation.read? AlgebraExtractionControls.wordOperations assignment "Word" .vec model
        (lawNormal [⟨.vec, some "One"⟩] (lowered bareRow nestedWithUnit)) =
          some (assignment "x" ++ assignment "y" ++ assignment "z") :=
  normalized_interpretation bareRow bare_accepted (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) rfl

#guard (BinaryCollectionJoin.language.toOption.map CollectionLaws.declared) ==
  some [⟨.vec, some "One"⟩]

#guard let extracted := declareAlgebras (target wrappedRow) ["Word"]
  (CollectionLaws.declared extracted).isEmpty &&
    extracted.equations == (target wrappedRow).equations && !extracted.equations.isEmpty

def distinctUnitOperations (label : String) (arguments : List (List Nat)) : List Nat :=
  if label = "Wrong" then [9] else arguments.flatten

def wordFold : Mettapedia.Algebra.Collections.Folds.Model (List Nat) where
  «fold» := List.flatten
  singleton := by intro value; simp
  flatten := by intro pieces; exact List.flatten_flatten

theorem wrong_unit_changes_interpretation :
    let algebra := wordFold
    let term := Pattern.collection .vec [.apply "Wrong" []] none
    BinaryCollectionInterpretation.read? distinctUnitOperations (fun _ => []) "Word" .vec algebra term = some [9] ∧
      BinaryCollectionInterpretation.read? distinctUnitOperations (fun _ => []) "Word" .vec algebra
        (lawNormal [⟨.vec, some "Wrong"⟩] term) = some [] := by
  simp [wordFold, BinaryCollectionInterpretation.read?, distinctUnitOperations,
    lawNormal, CollectionLaws.normalize, splice, canon, arrange]

theorem undeclared_flattening_keeps_nested_carrier :
    lawNormal [] (.collection .vec [.collection .vec [.fvar "x"] none] none) ≠
      lawNormal [] (.collection .vec [.fvar "x"] none) := by
  simp [lawNormal, CollectionLaws.normalize, canon, arrange]


/-- The existing native checker realizes the generic lowered typing result.
The object-pattern condition is the checker's actual domain, and is separate
from declarative typing of explicit substitutions or open collection tails. -/
theorem native_typed_returns {source target : LanguageDef} {old new : GrammarRule}
    {parameterName carrierSort : String} {kind : CollType}
    (signature : Signature source target old new)
    (representation : Representation source target old new kind)
    (checked : checkReplacementTyping old new = true)
    (named : namedArguments? old new = false)
    (shape : new.params = [.simple parameterName (.collection kind (.base carrierSort))])
    (context : List (String × TypeExpr)) (bound : List TypeExpr) {pattern : Pattern} {expected : TypeExpr}
    (typed : HasType source (FreeTypeContext.ofList context) bound pattern expected)
    (object : WellSorted.isObjectPattern (translated target old new kind pattern) = true)
    (state : Mettapedia.Languages.MeTTa.PeTTa.Effects.State) :
    Mettapedia.Languages.MeTTa.PeTTa.Eval.PureReturns
      Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.program [] state
      (Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.DeclarationTyping.query
        target context bound (translated target old new kind pattern) expected) state
      (Mettapedia.Languages.MeTTa.PeTTa.Effects.boolean true) := by
  have lowered := BinaryCollectionLowering.typed signature representation checked named shape _ _ typed
  have accepted := (checkHasType_eq_true_iff object).mpr lowered
  simpa only [accepted] using
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.DeclarationTyping.check_has_type_returns
      target context bound (translated target old new kind pattern) expected state

def authored : LanguageDef := BinaryCollectionJoin.language.toOption.getD (LanguageDef.empty "")
def language : LanguageDef := (authored.toCore.toOption.map (·.language)).getD (LanguageDef.empty "")

#guard BinaryCollectionJoin.language.isOk
#guard authored.toCore.isOk
#guard language.equations.length == 2
#guard !CollectionOccurrenceAdmission.check
  (GeneralExecutionAdmission.compile ⟨language, [], ⟨[], [], []⟩⟩
    { sites := .all, includeDerivedEquations := false })

/-- The existing native law normalizer returns a pattern with the same
selected fold value. Its operational correspondence is reused directly. -/
theorem native_normalize_preserves_interpretation {A : Type}
    (operations : String → List A → A) (assignment : String → A)
    (label : String) (kind : CollType) (algebra : Mettapedia.Algebra.Collections.Folds.Model A)
    (laws : List CollectionLaws.Laws)
    (units : ∀ law, CollectionLaws.lawFor laws kind = some law →
      ∀ unit, law.unit = some unit → unit ≠ label ∧ operations unit [] = algebra.fold [])
    {pattern : Pattern} {value : A}
    (computed : BinaryCollectionInterpretation.read? operations assignment label kind algebra pattern = some value)
    (state : Mettapedia.Languages.MeTTa.PeTTa.Effects.State) :
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.NormalizeAt state laws pattern ∧
      BinaryCollectionInterpretation.read? operations assignment label kind algebra
        (CollectionLaws.normalize laws pattern) = some value :=
  ⟨Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.normalize_returns state laws pattern,
    BinaryCollectionInterpretation.read_normalize operations assignment label kind algebra laws units computed⟩

#print axioms normalized_interpretation
#print axioms wrong_unit_changes_interpretation
#print axioms native_normalize_preserves_interpretation

end Mettapedia.GSLT.LanguageDef.ModuleSource.BinaryCollectionControls
