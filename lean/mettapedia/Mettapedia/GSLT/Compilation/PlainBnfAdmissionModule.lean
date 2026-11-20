import Mettapedia.GSLT.Compilation.CanonicalHornSemantics
import Mettapedia.GSLT.Parsing.PlainBnfScalarOrderSource

/-!
# The authored plain-BNF admission clauses and their moded reading

The rows come from the existing exact source projection, not from a
second grammar. The masks here describe the selected BNF admission
entry and reachable declarations. Extensional providers are visibly
separate; their interpretation still has to be supplied.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.PlainBnfAdmissionModule

open Mettapedia.GSLT.Parsing
open CanonicalHornModule CanonicalHornSemantics ModedRuleModule
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax

private def intensionalModes : List (String × Nat × Nat) :=
  [("BNFAppendDefinitionV1", 2, 1),
   ("BNFAppendDiagnosticsV1", 2, 1),
   ("BNFCollectDefinitionsV1", 2, 2),
   ("BNFDefinitionLookupV1", 2, 1),
   ("BNFDefinitionStepV1", 5, 2),
   ("BNFFinishValidationV1", 5, 1),
   ("BNFLexicalClassDiagnosticV1", 3, 1),
   ("BNFLexicalClassLookupV1", 2, 1),
   ("BNFLexicalLabelDiagnosticV1", 3, 1),
   ("BNFLexicalLabelLookupV1", 2, 1),
   ("BNFLexicalMatcherDiagnosticV1", 3, 1),
   ("BNFLexicalReferenceDiagnosticV1", 3, 1),
   ("BNFLexicalReferenceLookupV1", 2, 1),
   ("BNFLexicalReferenceNameDiagnosticV1", 2, 1),
   ("BNFLexicalRuleConflictDiagnosticV1", 3, 1),
   ("BNFLexicalStringDiagnosticV1", 3, 1),
   ("BNFReferenceAfterDefinitionLookupV1", 5, 1),
   ("BNFReferenceAfterLexicalLookupV1", 4, 1),
   ("BNFScalarDiagnosticV1", 2, 1),
   ("BNFScalarOrderDiagnosticV1", 3, 1),
   ("BNFScanAlternativesReferencesV1", 4, 1),
   ("BNFScanElementReferencesV1", 4, 1),
   ("BNFScanElementsReferencesV1", 4, 1),
   ("BNFScanEntryReferencesV1", 3, 1),
   ("BNFScanExpressionReferencesV1", 4, 1),
   ("BNFStartAfterLookupV1", 2, 2),
   ("BNFValidateGrammarV1", 1, 1),
   ("BNFValidateLexicalsV1", 2, 1),
   ("BNFValidateScalarListV1", 2, 1)]

private def externalModes : List (String × Nat) :=
  [("different", 2), ("ground-integer-less", 2), ("ground-integer-not-less", 2),
   ("ground-unicode-scalar", 1), ("ground-non-unicode-scalar", 1)]

def modes : Modes := fun relation =>
  if externalModes.contains (relation.name, relation.arity) then some .external
  else
    (intensionalModes.find? fun (name, inputs, outputs) =>
      name == relation.name && inputs + outputs == relation.arity).map fun (_, inputs, outputs) =>
        .derived (List.replicate inputs true ++ List.replicate outputs false)

abbrev Labels := Fin 67

def source? : Option HornCertificate.Program :=
  CanonicalSourceHornElaboration.programOf <$>
    CanonicalSourceHornElaboration.elaborateRewrites? PlainBnfScalarOrderSource.sourceRows

def compiled? : Option (List (Clause (Signature Labels))) :=
  source?.bind (compileProgram? modes)

/-- The entry's original first column is the input; the second is the
answer. The guard columns, in contrast, are never outputs. -/
theorem entry_mode :
    modes ⟨"BNFValidateGrammarV1", 2⟩ = some (.derived [true, false]) ∧
      modes ⟨"ground-integer-less", 2⟩ = some .external :=
  ⟨rfl, rfl⟩

theorem wrong_entry_arity_refused :
    modes ⟨"BNFValidateGrammarV1", 3⟩ = none := rfl

theorem source_isSome : source?.isSome = true := by
  decide +kernel

theorem source_length : (source?.get source_isSome).length = 67 := by
  decide +kernel

/-- The mode check covers every authored semantic-admission rule. -/
theorem compiled_isSome : compiled?.isSome = true := by
  decide +kernel

def source : HornCertificate.Program := source?.get source_isSome

private theorem isSome_get_bind {α β : Type} (input : Option α) (f : α → Option β)
    (available : input.isSome = true) (result : (input.bind f).isSome = true) :
    (f (input.get available)).isSome = true := by
  cases input with
  | none => cases available
  | some _ => exact result

private theorem source_compiles : (compileProgram? (Labels := Labels) modes source).isSome = true :=
  isSome_get_bind source? (compileProgram? modes) source_isSome compiled_isSome

def clauses : List (Clause (Signature Labels)) :=
  (compileProgram? modes source).get source_compiles

theorem compile_source : compileProgram? modes source = some clauses :=
  (Option.some_get source_compiles).symm

theorem clauses_length : clauses.length = 67 :=
  (compileProgram?_length_and_scope modes source compile_source).1.trans source_length

/-- Labels are occurrence indices, not rule names. -/
def moduleClauses (label : Labels) : Clause (Signature Labels) :=
  clauses.get ⟨label.val, clauses_length.symm ▸ label.isLt⟩

/-- The source rule on each label is the authored occurrence in the
same list position, not a search by a possibly repeated rule name. -/
def sourceRules (label : Labels) : HornCertificate.Rule :=
  source.get ⟨label.val, source_length.symm ▸ label.isLt⟩

theorem rule_occurrence_compiles (label : Labels) :
    compileRule? modes (sourceRules label) = some (moduleClauses label) := by
  have atPosition := compileProgram?_at compile_source (i := label.val)
  have raw : source[label.val]? = some (sourceRules label) :=
    List.getElem?_eq_some_iff.mpr ⟨source_length.symm ▸ label.isLt, rfl⟩
  have lowered : clauses[label.val]? = some (moduleClauses label) :=
    List.getElem?_eq_some_iff.mpr ⟨clauses_length.symm ▸ label.isLt, rfl⟩
  simpa only [raw, lowered, Option.bind_some] using atPosition

theorem module_rangeRestricted (label : Labels) :
    ModuleReading.RangeRestricted (lower moduleClauses label) :=
  compileRule?_rangeRestricted (rule_occurrence_compiles label)

theorem module_queriesBound (label : Labels) :
    ModuleReading.QueriesBound (lower moduleClauses label) :=
  compileRule?_queriesBound (rule_occurrence_compiles label)

def validationInput (grammar : Datum Labels) : Datum Labels :=
  pack (Labels := Labels) (.call ⟨"BNFValidateGrammarV1", 2⟩ 1) [grammar].get

def validationOutput (result : Datum Labels) : Datum Labels :=
  pack (Labels := Labels) (.outputs 1) [result].get

/-- At a completed reference run, the compiled authored module answers
the validation call according to its moded least interpretation.
Provider facts are supplied by the caller. -/
theorem completed_validation_answers (timing : SetStore.AskTiming)
    (providers : Finset (Mettapedia.Logic.LP.Atom (Signature Labels)))
    (grammar result : Datum Labels) (ground : (validationInput grammar).isGround)
    (providerGround : ∀ atom ∈ providers, atom.isGround)
    {outcome : Finset (Datum Labels)}
    (run : Relation.ReflTransGen (SetStoreSyntax.QuantifiedStep .every timing
      (ModuleReading.reading (lower moduleClauses)))
      (ModuleReading.seed (validationInput grammar) providers) outcome)
    (finished : SetStoreSyntax.QuantifiedTerminal .every timing
      (ModuleReading.reading (lower moduleClauses)) outcome) :
    ModuleReading.valueRow (validationInput grammar) (validationOutput result) ∈ outcome ↔
      Least moduleClauses providers (validationInput grammar, validationOutput result) :=
  completed_every_answers (σ := signature) (Labels := Labels) (Equiv.refl Nat)
    timing moduleClauses providers module_rangeRestricted
    (validationInput grammar) (validationOutput result) ground providerGround run finished

def validationGoal (grammar result : RawTerm) : RawAtom :=
  ⟨⟨"BNFValidateGrammarV1", 2⟩, fun i => if i.val = 0 then grammar else result⟩

theorem validation_goal_lowers (grammar result : RawTerm) :
    lowerAtom? (Labels := Labels) modes (validationGoal grammar result) =
      some (.intensional ⟨validationInput (wrapTerm grammar), validationOutput (wrapTerm result)⟩) := by
  have chosen : modes (validationGoal grammar result).symbol = some (.derived [true, false]) :=
    entry_mode.1
  have arguments : List.ofFn (fun i => wrapTerm (Labels := Labels) ((validationGoal grammar result).args i)) =
      [wrapTerm grammar, wrapTerm result] := by
    simp [validationGoal, List.ofFn_succ]
  simp only [lowerAtom?, chosen, arguments]
  rfl

def validationProviders (providers : Finset RawAtom) : Finset (Mettapedia.Logic.LP.Atom (Signature Labels)) :=
  providers.image (wrapAtom (Labels := Labels))

/-- The authored validation relation and a completed reference tcalc
run agree on every encoded answer, with the same interpretation of
the external predicates. This is a theorem of the reference module,
not an assertion about native parser or provider code. -/
theorem completed_authored_validation_answers (timing : SetStore.AskTiming)
    (providers : Finset RawAtom) (grammar result : RawTerm) (ground : grammar.isGround)
    (providerGround : ∀ atom ∈ providers, atom.isGround)
    {outcome : Finset (Datum Labels)}
    (run : Relation.ReflTransGen (SetStoreSyntax.QuantifiedStep .every timing
      (ModuleReading.reading (lower moduleClauses)))
      (ModuleReading.seed (validationInput (wrapTerm grammar)) (validationProviders providers)) outcome)
    (finished : SetStoreSyntax.QuantifiedTerminal .every timing
      (ModuleReading.reading (lower moduleClauses)) outcome) :
    ModuleReading.valueRow (validationInput (wrapTerm grammar)) (validationOutput (wrapTerm result))
      ∈ outcome ↔
      SourceLeast (rolesOf modes) sourceRules providers (validationGoal grammar result) := by
  have inputGround : (validationInput (wrapTerm grammar)).isGround := by
    change ∀ i : Fin 1, ([wrapTerm (Labels := Labels) grammar].get i).isGround
    intro i
    have zero : i = 0 := Fin.eq_zero i
    subst i
    exact (wrap_ground_iff grammar).mpr ground
  have factsGround : ∀ atom ∈ validationProviders providers, atom.isGround := by
    intro atom member
    obtain ⟨original, known, rfl⟩ := Finset.mem_image.mp member
    exact (wrap_atom_ground_iff original).mpr (providerGround original known)
  refine (completed_validation_answers timing (validationProviders providers)
    (wrapTerm grammar) (wrapTerm result) inputGround factsGround run finished).trans ?_
  simpa only [validationProviders, Finset.coe_image] using least_iff_source modes sourceRules
    moduleClauses rule_occurrence_compiles (providers : Set RawAtom) (validationGoal grammar result)
    ⟨validationInput (wrapTerm grammar), validationOutput (wrapTerm result)⟩
    (validation_goal_lowers grammar result)

#print axioms source_isSome
#print axioms source_length
#print axioms compiled_isSome
#print axioms compile_source
#print axioms clauses_length
#print axioms rule_occurrence_compiles
#print axioms module_rangeRestricted
#print axioms module_queriesBound
#print axioms validation_goal_lowers
#print axioms completed_validation_answers
#print axioms completed_authored_validation_answers

end Mettapedia.GSLT.Compilation.PlainBnfAdmissionModule
