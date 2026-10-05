import Mettapedia.Languages.VibeITP.Presentation.DefinitionCorrespondence

/-!
# Definition queries for arbitrary signatures

The snapshot includes every body head and every parameter, including unused
parameters. The constant is supplied identity data; construction does not
look up its earlier declaration. Fresh allocation and sequential theory
admission remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalDefinitions

open ComputationalData ComputationalShift ComputationalInstantiation ComputationalInference
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

mutual

theorem occurrences_on_info (source target : Spec.Sig) (body : Spec.Term)
    (agree : InfoAgree source target (termHeads body)) :
    Spec.fvarOccurrences source body = Spec.fvarOccurrences target body := by
  cases body with
  | bvar _ => rfl
  | lit _ => rfl
  | app symbol arguments =>
      rw [Spec.fvarOccurrences, Spec.fvarOccurrences,
        isFvar_on_info source target symbol agree.head,
        occurrencesList_on_info source target arguments agree.tail]

theorem occurrencesList_on_info (source target : Spec.Sig) (arguments : List Spec.Term)
    (agree : InfoAgree source target (termHeadsList arguments)) :
    Spec.fvarOccurrencesList source arguments = Spec.fvarOccurrencesList target arguments := by
  cases arguments with
  | nil => rfl
  | cons first rest =>
      rw [Spec.fvarOccurrencesList, Spec.fvarOccurrencesList,
        occurrences_on_info source target first agree.left,
        occurrencesList_on_info source target rest agree.right]

end

theorem parameters_on_info (source target : Spec.Sig) (parameters : List Spec.SymId)
    (agree : InfoAgree source target parameters) :
    parameters.all (Spec.isFvarSym source) = parameters.all (Spec.isFvarSym target) := by
  induction parameters with
  | nil => rfl
  | cons first rest ih =>
      rw [List.all_cons, List.all_cons, isFvar_on_info source target first agree.head, ih agree.tail]

theorem arities_on_info (source target : Spec.Sig) (parameters : List Spec.SymId)
    (agree : InfoAgree source target parameters) :
    parameters.map (Spec.symArity source) = parameters.map (Spec.symArity target) := by
  apply List.map_congr_left
  intro symbol used
  unfold Spec.symArity
  rw [agree symbol used]

theorem definitionInfo_on_info (source target : Spec.Sig) (parameters : List Spec.SymId)
    (agree : InfoAgree source target parameters) :
    Spec.definitionInfo source parameters = Spec.definitionInfo target parameters := by
  unfold Spec.definitionInfo
  rw [arities_on_info source target parameters agree]

theorem definitionStatement_on_info (source target : Spec.Sig) (constant : Spec.SymId)
    (parameters : List Spec.SymId) (body : Spec.Term) (agree : InfoAgree source target parameters) :
    Spec.definitionStatement source constant parameters body =
      Spec.definitionStatement target constant parameters body := by
  have terms : (parameters.map fun symbol => Spec.etaFvar symbol (Spec.symArity source symbol)) =
      parameters.map fun symbol => Spec.etaFvar symbol (Spec.symArity target symbol) := by
    apply List.map_congr_left
    intro symbol used
    unfold Spec.symArity
    rw [agree symbol used]
  simp only [Spec.definitionStatement, terms]

theorem definitionAdmissible_on_info (source target : Spec.Sig) (request : DefinitionRequest)
    (agree : InfoAgree source target (termHeads request.body ++ request.parameters)) :
    Spec.definitionAdmissible source request.parameters request.hints request.body =
      Spec.definitionAdmissible target request.parameters request.hints request.body := by
  unfold Spec.definitionAdmissible
  rw [depth_on_heads source target request.body agree.left.binders,
    parameters_on_info source target request.parameters agree.right,
    occurrences_on_info source target request.body agree.left]

theorem definitionResult_on_info (source target : Spec.Sig) (request : DefinitionRequest)
    (agree : InfoAgree source target (termHeads request.body ++ request.parameters)) :
    request.result source = request.result target := by
  unfold DefinitionRequest.result
  rw [wellFormed_on_heads source target request.body agree.left,
    definitionAdmissible_on_info source target request agree,
    definitionStatement_on_info source target request.constant request.parameters request.body agree.right]

def definitionSnapshot (signature : Spec.Sig) (request : DefinitionRequest) : SignatureTable :=
  tableFor signature (termHeads request.body ++ request.parameters)

theorem definitionSnapshot_info (signature : Spec.Sig) (request : DefinitionRequest) :
    InfoAgree (signatureOf (definitionSnapshot signature request)) signature
      (termHeads request.body ++ request.parameters) := by
  intro symbol used
  simp only [definitionSnapshot, tableFor_lookup, used, ↓reduceIte]

theorem definitionQuery_computes_for_signature (signature : Spec.Sig) (request : DefinitionRequest) :
    Applies definitionProgram productDivisionHost "vibe:definition-query"
      [encodeTable (definitionSnapshot signature request), encodeSymbol request.constant,
        encodeSymbols request.parameters, encodeBinders request.hints, encode request.body]
      (encodeResult (request.result signature)) := by
  rw [← definitionResult_on_info _ signature request (definitionSnapshot_info signature request)]
  exact definitionQuery_computes _ _

theorem definitionQuery_signature_result_exact (signature : Spec.Sig) (request : DefinitionRequest) (result : Term) :
    Applies definitionProgram productDivisionHost "vibe:definition-query"
      [encodeTable (definitionSnapshot signature request), encodeSymbol request.constant,
        encodeSymbols request.parameters, encodeBinders request.hints, encode request.body] result ↔
      result = encodeResult (request.result signature) := by
  rw [definitionQuery_result_exact,
    definitionResult_on_info _ signature request (definitionSnapshot_info signature request)]

theorem definitionInfo_computes_for_signature (signature : Spec.Sig) (request : DefinitionRequest) :
    Applies definitionProgram productDivisionHost "vibe:def-info"
      [encodeTable (definitionSnapshot signature request), encodeSymbols request.parameters]
      (encodeInfoResult (if request.parameters.all (Spec.isFvarSym signature) then
        some (Spec.definitionInfo signature request.parameters) else none)) := by
  have run := definitionInfo_computes (definitionSnapshot signature request) request.parameters
  rw [parameters_on_info _ signature request.parameters (definitionSnapshot_info signature request).right,
    definitionInfo_on_info _ signature request.parameters (definitionSnapshot_info signature request).right] at run
  exact run

theorem checkDefinition_computes_for_signature (signature : Spec.Sig) (request : DefinitionRequest) (claimed : Spec.Term) :
    Applies definitionProgram productDivisionHost "vibe:check-definition"
      [encodeTable (definitionSnapshot signature request), encodeSymbol request.constant,
        encodeSymbols request.parameters, encodeBinders request.hints, encode request.body, encode claimed]
      (boolean (decide (request.result signature = some claimed))) := by
  rw [← definitionResult_on_info _ signature request (definitionSnapshot_info signature request)]
  exact checkDefinition_computes _ _ _

theorem checkDefinition_for_signature_iff (signature : Spec.Sig) (request : DefinitionRequest) (claimed : Spec.Term) :
    Applies definitionProgram productDivisionHost "vibe:check-definition"
      [encodeTable (definitionSnapshot signature request), encodeSymbol request.constant,
        encodeSymbols request.parameters, encodeBinders request.hints, encode request.body, encode claimed]
      (.sym "True") ↔ request.result signature = some claimed := by
  rw [checkDefinition_accepts_iff,
    definitionResult_on_info _ signature request (definitionSnapshot_info signature request)]

def DefinitionRequest.declaration (request : DefinitionRequest) : Spec.Definition :=
  ⟨request.constant, request.parameters, request.body⟩

theorem checkDefinition_derived (theory : Spec.Theory) (request : DefinitionRequest) (claimed : Spec.Term)
    (admitted : request.declaration ∈ theory.definitions)
    (checked : Applies definitionProgram productDivisionHost "vibe:check-definition"
      [encodeTable (definitionSnapshot theory.sig request), encodeSymbol request.constant,
        encodeSymbols request.parameters, encodeBinders request.hints, encode request.body, encode claimed]
      (.sym "True")) : Spec.Derives theory claimed := by
  have authorized := (checkDefinition_for_signature_iff theory.sig request claimed).mp checked
  unfold DefinitionRequest.result at authorized
  split at authorized
  · cases Option.some.inj authorized
    exact Spec.Derives.definition admitted
  · cases authorized

theorem admittedDefinition_check_exists {theory : Spec.Theory} {allocated : Nat}
    (hosted : Hosted theory allocated) (declaration : Spec.Definition)
    (admitted : declaration ∈ theory.definitions) :
    ∃ hints, let request : DefinitionRequest :=
        ⟨declaration.symbol, declaration.fvars, hints, declaration.value⟩
      Applies definitionProgram productDivisionHost "vibe:check-definition"
        [encodeTable (definitionSnapshot theory.sig request), encodeSymbol request.constant,
          encodeSymbols request.parameters, encodeBinders request.hints, encode request.body,
          encode (Spec.definitionStatement theory.sig declaration.symbol declaration.fvars declaration.value)]
        (.sym "True") := by
  obtain ⟨_, formed, hints, authorized⟩ := hosted.definitionsOk declaration admitted
  refine ⟨hints, ?_⟩
  apply (checkDefinition_for_signature_iff _ _ _).mpr
  simp only [DefinitionRequest.result, formed, authorized, Bool.true_and, ↓reduceIte]

end Mettapedia.Languages.VibeITP.Presentation.ComputationalDefinitions
