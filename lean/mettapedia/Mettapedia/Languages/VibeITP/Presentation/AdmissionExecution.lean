import Mettapedia.Languages.VibeITP.Presentation.AdmissionProgram

/-! Finite execution of authored list updates and static declarations. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalAdmission

open ComputationalData ComputationalShift ComputationalDefinitions ComputationalProofs
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => admissionProgram
local notation "A" => admissionEquations
local notation "H" => productDivisionHost

private theorem previous {head : String} {arguments : List Term} {result : Term}
    (used : head ∈ definitionProgram.calledHeads)
    (computed : Applies definitionProgram H head arguments result) : Applies P H head arguments result := by
  apply reuse_proof_call ?_ (reuse_definition_call used computed)
  simp only [proofProgram, Program.calledHeads, List.flatMap_append]
  exact List.mem_append_left _ used

private theorem view (items : List Term) : Applies P H "nik:list-view" [.list items] (listView items) :=
  .primitive (by decide +kernel) (computationalHost_list_view items)

private theorem cons (first : Term) (rest : List Term) :
    Applies P H "nik:list-cons" [first, .list rest] (.list (first :: rest)) :=
  .primitive (by decide +kernel) (computationalHost_list_cons first rest)

private theorem zero (count : Nat) :
    Applies P H "nik:nat-zero" [natural count] (boolean (decide (count = 0))) :=
  previous (by decide +kernel) (definition_zero count)

private theorem pred (count : Nat) : Applies P H "nik:nat-pred" [natural count] (natural count.pred) :=
  .primitive (by decide +kernel) (computationalHost_pred count)

private theorem add (left right : Nat) :
    Applies P H "nik:nat-add" [natural left, natural right] (natural (left + right)) :=
  .primitive (by decide +kernel) (naturalArithmeticHost_add left right)

private theorem someEval {environment : Env} {source target : Term}
    (child : Evaluates P H environment source target) :
    Evaluates P H environment (.expr [.sym "Some", source]) (.expr [.sym "Some", target]) :=
  Evaluates.call (by simp [Special]) (.cons child .nil) (.constructor (by decide +kernel) (by rfl))

private theorem stateEval {environment : Env} {phase identity table axioms definitions : Term}
    {phase' identity' table' axioms' definitions' : Term}
    (phaseRun : Evaluates P H environment phase phase')
    (identityRun : Evaluates P H environment identity identity')
    (tableRun : Evaluates P H environment table table')
    (axiomsRun : Evaluates P H environment axioms axioms')
    (definitionsRun : Evaluates P H environment definitions definitions') :
    Evaluates P H environment (.list [.sym "Vibe:Admission", phase, identity, table, axioms, definitions])
      (.list [.sym "Vibe:Admission", phase', identity', table', axioms', definitions']) :=
  Evaluates.list (.cons (.symbol _ _ _ _) (.cons phaseRun (.cons identityRun
    (.cons tableRun (.cons axiomsRun (.cons definitionsRun .nil))))))

private theorem bindingEval {environment : Env} {symbol kind binders symbol' kind' binders' : Term}
    (symbolRun : Evaluates P H environment symbol symbol')
    (kindRun : Evaluates P H environment kind kind')
    (bindersRun : Evaluates P H environment binders binders') :
    Evaluates P H environment (.expr [.sym "Vibe:Binding", symbol, kind, binders])
      (.expr [.sym "Vibe:Binding", symbol', kind', binders']) :=
  Evaluates.call (by simp [Special]) (.cons symbolRun (.cons kindRun (.cons bindersRun .nil)))
    (.constructor (by decide +kernel) (by rfl))

private def stateEnv (state : AdmissionState) : Env :=
  [("phase", encodePhase state.phase), ("identity", natural state.nextFresh), ("table", encodeTable state.table),
    ("axioms", encodeAxioms state.axioms), ("definitions", encodeDefinitions state.definitions)]

private theorem snoc_start (items : List Term) (last result : Term)
    (next : Applies P H "vibe:admission-snoc-view" [listView items, last] result) :
    Applies P H "vibe:admission-snoc" [.list items, last] result := by
  refine admission_equation (equation := A[0]) (environment := [("items", .list items), ("last", last)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view items)

theorem snoc_computes (items : List Term) (last : Term) :
    Applies P H "vibe:admission-snoc" [.list items, last] (.list (items ++ [last])) := by
  induction items with
  | nil =>
      apply snoc_start [] last
      refine admission_equation (equation := A[1]) (environment := [("last", last)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.list (.cons (.variable (by rfl)) .nil)
  | cons first rest ih =>
      apply snoc_start (first :: rest) last
      refine admission_equation (equation := A[2])
        (environment := [("first", first), ("rest", .list rest), ("last", last)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) (cons _ _)
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) ih

private theorem zeros_start (count : Nat) (result : Term)
    (next : Applies P H "vibe:admission-zeros-test" [boolean (decide (count = 0)), natural count] result) :
    Applies P H "vibe:admission-zeros" [natural count] result := by
  refine admission_equation (equation := A[3]) (environment := [("count", natural count)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (zero count)

theorem zeros_computes (count : Nat) :
    Applies P H "vibe:admission-zeros" [natural count] (encodeBinders (List.replicate count 0)) := by
  induction count with
  | zero => exact zeros_start 0 _ ⟨1, by rw [admission_apply _ (by decide +kernel)]; rfl⟩
  | succ count ih =>
      apply zeros_start (count + 1)
      refine admission_equation (equation := A[5]) (environment := [("count", natural (count + 1))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons (natural_passive P H 0 |>.evaluates _)
        (.cons ?_ .nil)) (cons _ _)
      refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) ih
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (pred (count + 1))

theorem allocate_computes (state : AdmissionState) (info : Spec.SymInfo) :
    Applies P H "vibe:admission-allocate" [encodeState state, encodeKind info.kind, encodeBinders info.binders]
      (encodeAdmissionResult (some (state.allocate info))) := by
  refine admission_equation (equation := A[6])
    (environment := stateEnv state ++ [("kind", encodeKind info.kind), ("binders", encodeBinders info.binders)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  apply someEval
  refine stateEval (.variable (by rfl)) ?_ ?_ (.variable (by rfl)) (.variable (by rfl))
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (natural_passive P H 1 |>.evaluates _) .nil)) (add _ _)
  · refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) (cons _ _)
    refine bindingEval ?_ (.variable (by rfl)) (.variable (by rfl))
    exact Evaluates.list (.cons (.symbol _ _ _ _) (.cons (.variable (by rfl)) .nil))

private theorem fvar_computes (state : AdmissionState) (arity : Nat) :
    Applies P H "vibe:admit" [encodeState state, encodeDeclaration (.fvar arity)]
      (encodeAdmissionResult (admit state (.fvar arity))) := by
  refine admission_equation (equation := A[7])
    (environment := stateEnv state ++ [("arity", natural arity)]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.symbol _ _ _ _) (.cons ?_ .nil)))
    (allocate_computes state (Spec.SymInfo.fvarOf arity))
  · exact stateEval (.variable (by rfl)) (.variable (by rfl)) (.variable (by rfl))
      (.variable (by rfl)) (.variable (by rfl))
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (zeros_computes arity)

private theorem constant_computes (state : AdmissionState) (binders : List Nat) :
    Applies P H "vibe:admit" [encodeState state, encodeDeclaration (.constant binders)]
      (encodeAdmissionResult (admit state (.constant binders))) := by
  refine admission_equation (equation := A[8])
    (environment := stateEnv state ++ [("binders", encodeBinders binders)]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.symbol _ _ _ _) (.cons (.variable (by rfl)) .nil)))
    (allocate_computes state ⟨.constant, binders⟩)
  exact stateEval (.variable (by rfl)) (.variable (by rfl)) (.variable (by rfl))
    (.variable (by rfl)) (.variable (by rfl))

private theorem axiom_closed (state : AdmissionState) (statement : Spec.Term) (setup : state.phase = .setup) :
    Applies P H "vibe:admission-axiom-closed"
      [boolean (decide (Spec.depth (signatureOf state.table) statement = 0)), natural state.nextFresh,
        encodeTable state.table, encodeAxioms state.axioms, encodeDefinitions state.definitions, encode statement]
      (encodeAdmissionResult (if Spec.depth (signatureOf state.table) statement = 0 then
        some (state.addAxiom statement) else none)) := by
  by_cases closed : Spec.depth (signatureOf state.table) statement = 0
  · simp only [closed, decide_true, boolean, ↓reduceIte]
    refine admission_equation (equation := A[14])
      (environment := [("identity", natural state.nextFresh), ("table", encodeTable state.table),
        ("axioms", encodeAxioms state.axioms), ("definitions", encodeDefinitions state.definitions),
        ("statement", encode statement)]) (by decide +kernel) (by rfl) (by rfl) ?_
    apply someEval
    simp only [encodeState, AdmissionState.addAxiom, setup, encodePhase]
    refine stateEval (.symbol _ _ _ _) (.variable (by rfl)) (.variable (by rfl)) ?_ (.variable (by rfl))
    have appended := snoc_computes (state.axioms.map encode) (encode statement)
    simp only [encodeAxioms, List.map_append, List.map_cons, List.map_nil]
    exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) appended
  · simp only [closed, decide_false, boolean, ↓reduceIte]
    exact ⟨1, by rw [admission_apply _ (by decide +kernel)]; rfl⟩

private theorem axiom_formed (state : AdmissionState) (statement : Spec.Term) (setup : state.phase = .setup) :
    Applies P H "vibe:admission-axiom-wf"
      [boolean (Spec.WellFormed (signatureOf state.table) statement), natural state.nextFresh,
        encodeTable state.table, encodeAxioms state.axioms, encodeDefinitions state.definitions, encode statement]
      (encodeAdmissionResult (admit state (.axiom statement))) := by
  cases formed : Spec.WellFormed (signatureOf state.table) statement with
  | false =>
      simp only [formed, boolean, admit, setup, Bool.false_eq_true, false_and, and_false, ↓reduceIte]
      exact ⟨1, by rw [admission_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      simp only [formed, boolean, admit, setup, true_and]
      refine admission_equation (equation := A[12])
        (environment := [("identity", natural state.nextFresh), ("table", encodeTable state.table),
          ("axioms", encodeAxioms state.axioms), ("definitions", encodeDefinitions state.definitions),
          ("statement", encode statement)]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) (axiom_closed state statement setup)
      refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (zero _)
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
        (previous (by decide +kernel) (definition_depth state.table statement))

private theorem axiom_computes (state : AdmissionState) (statement : Spec.Term) :
    Applies P H "vibe:admit" [encodeState state, encodeDeclaration (.axiom statement)]
      (encodeAdmissionResult (admit state (.axiom statement))) := by
  cases phase : state.phase with
  | proofs =>
      simp [admit, phase]
      refine ⟨1, ?_⟩
      rw [admission_apply _ (by decide +kernel)]
      simp only [encodeState, phase, encodePhase, encodeDeclaration, encodeAdmissionResult]
      rfl
  | setup =>
      refine admission_equation (equation := A[9])
        (environment := [("identity", natural state.nextFresh), ("table", encodeTable state.table),
          ("axioms", encodeAxioms state.axioms), ("definitions", encodeDefinitions state.definitions),
          ("statement", encode statement)]) (by decide +kernel) (by rfl)
        (by simp only [encodeState, phase, encodePhase, encodeDeclaration]; rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) (axiom_formed state statement phase)
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
        (previous (by decide +kernel) (definition_formed state.table statement))

private theorem definition_publish (state : AdmissionState) (parameters : List Spec.SymId) (body : Spec.Term) :
    Applies P H "vibe:admission-definition-info"
      [encodeInfoResult (some (Spec.definitionInfo (signatureOf state.table) parameters)), encodeState state,
        encodeSymbols parameters, encode body] (encodeAdmissionResult (some (state.define parameters body))) := by
  refine admission_equation (equation := A[19])
    (environment := [("binders", encodeBinders (parameters.map (Spec.symArity (signatureOf state.table))))] ++
      stateEnv state ++ [("parameters", encodeSymbols parameters), ("body", encode body)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  apply someEval
  refine stateEval (.variable (by rfl)) ?_ ?_ (.variable (by rfl)) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (natural_passive P H 1 |>.evaluates _) .nil)) (add _ _)
  · refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) (cons _ _)
    refine bindingEval ?_ (.symbol _ _ _ _) (.variable (by rfl))
    exact Evaluates.list (.cons (.symbol _ _ _ _) (.cons (.variable (by rfl)) .nil))
  · have appended := snoc_computes (state.definitions.map encodeDefinition)
      (encodeDefinition ⟨.fresh state.nextFresh, parameters, body⟩)
    simp only [AdmissionState.define, AdmissionState.allocate, encodeDefinitions,
      List.map_append, List.map_cons, List.map_nil]
    refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) appended
    refine Evaluates.list (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
    exact Evaluates.list (.cons (.symbol _ _ _ _) (.cons (.variable (by rfl)) .nil))

private theorem definition_checked (state : AdmissionState) (parameters : List Spec.SymId)
    (hints : List Nat) (body : Spec.Term) :
    Applies P H "vibe:admission-definition-result"
      [encodeResult ((⟨.fresh state.nextFresh, parameters, hints, body⟩ : DefinitionRequest).result (signatureOf state.table)),
        encodeState state, encodeSymbols parameters, encode body]
      (encodeAdmissionResult (admit state (.definition parameters hints body))) := by
  by_cases guards : (Spec.WellFormed (signatureOf state.table) body &&
      Spec.definitionAdmissible (signatureOf state.table) parameters hints body) = true
  · simp only [DefinitionRequest.result, admit, guards]
    refine admission_equation (equation := A[17])
      (environment := [("equation", encode (Spec.definitionStatement (signatureOf state.table)
        (.fresh state.nextFresh) parameters body))] ++ stateEnv state ++
        [("parameters", encodeSymbols parameters), ("body", encode body)])
      (by decide +kernel) (by rfl) (by rfl) ?_
    refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) .nil)))) (definition_publish state parameters body)
    · have valid : parameters.all (Spec.isFvarSym (signatureOf state.table)) = true := by
        have admitted := (Bool.and_eq_true_iff.mp guards).2
        simp only [Spec.definitionAdmissible, Bool.and_eq_true_iff] at admitted
        exact admitted.1.2
      have info := previous (by decide +kernel) (definitionInfo_computes state.table parameters)
      simp only [valid, ↓reduceIte] at info
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) info
    · exact stateEval (.variable (by rfl)) (.variable (by rfl)) (.variable (by rfl))
        (.variable (by rfl)) (.variable (by rfl))
  · simp only [DefinitionRequest.result, admit, guards]
    exact ⟨1, by rw [admission_apply _ (by decide +kernel)]; rfl⟩

private theorem definition_computes (state : AdmissionState) (parameters : List Spec.SymId)
    (hints : List Nat) (body : Spec.Term) :
    Applies P H "vibe:admit" [encodeState state, encodeDeclaration (.definition parameters hints body)]
      (encodeAdmissionResult (admit state (.definition parameters hints body))) := by
  have selected : admissionEquations.select "vibe:admit" [encodeState state, encodeDeclaration (.definition parameters hints body)] =
      some (A[15], stateEnv state ++ [("parameters", encodeSymbols parameters), ("hints", encodeBinders hints),
        ("body", encode body)]) := by
    cases phase : state.phase <;> simp only [encodeState, stateEnv, phase, encodePhase, encodeDeclaration] <;> rfl
  refine admission_equation (equation := A[15])
    (environment := stateEnv state ++ [("parameters", encodeSymbols parameters), ("hints", encodeBinders hints),
      ("body", encode body)]) (by decide +kernel) (by rfl) selected ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ (.cons (.variable (by rfl))
    (.cons (.variable (by rfl)) .nil)))) (definition_checked state parameters hints body)
  · refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
      (previous (by decide +kernel) (definitionQuery_computes state.table ⟨.fresh state.nextFresh, parameters, hints, body⟩))
    exact Evaluates.list (.cons (.symbol _ _ _ _) (.cons (.variable (by rfl)) .nil))
  · exact stateEval (.variable (by rfl)) (.variable (by rfl)) (.variable (by rfl))
      (.variable (by rfl)) (.variable (by rfl))

theorem admit_computes (state : AdmissionState) (declaration : Declaration) :
    Applies P H "vibe:admit" [encodeState state, encodeDeclaration declaration]
      (encodeAdmissionResult (admit state declaration)) := by
  cases declaration with
  | fvar arity => exact fvar_computes state arity
  | constant binders => exact constant_computes state binders
  | «axiom» statement => exact axiom_computes state statement
  | definition parameters hints body => exact definition_computes state parameters hints body
  | enterProofs =>
      have selected : admissionEquations.select "vibe:admit" [encodeState state, encodeDeclaration .enterProofs] =
          some (A[20], stateEnv state) := by
        cases phase : state.phase <;> simp only [encodeState, stateEnv, phase, encodePhase, encodeDeclaration] <;> rfl
      refine admission_equation (equation := A[20]) (environment := stateEnv state)
        (by decide +kernel) (by rfl) selected ?_
      exact someEval (stateEval (.symbol _ _ _ _) (.variable (by rfl)) (.variable (by rfl))
        (.variable (by rfl)) (.variable (by rfl)))

private theorem run_start (state : AdmissionState) (declarations : List Declaration) (result : Term)
    (next : Applies P H "vibe:admission-run-view"
      [listView (declarations.map encodeDeclaration), encodeState state] result) :
    Applies P H "vibe:admission-run" [encodeState state, encodeDeclarations declarations] result := by
  refine admission_equation (equation := A[22])
    (environment := [("state", encodeState state), ("declarations", encodeDeclarations declarations)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view _)

private theorem run_next (state : Option AdmissionState) (rest : List Declaration)
    (tails : ∀ after, Applies P H "vibe:admission-run" [encodeState after, encodeDeclarations rest]
      (encodeAdmissionResult (admitRun after rest))) :
    Applies P H "vibe:admission-run-next" [encodeAdmissionResult state, encodeDeclarations rest]
      (encodeAdmissionResult (state.bind fun after => admitRun after rest)) := by
  cases state with
  | none => exact ⟨1, by rw [admission_apply _ (by decide +kernel)]; rfl⟩
  | some after =>
      refine admission_equation (equation := A[26])
        (environment := [("state", encodeState after), ("rest", encodeDeclarations rest)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
        (tails after)

theorem admitRun_computes (state : AdmissionState) (declarations : List Declaration) :
    Applies P H "vibe:admission-run" [encodeState state, encodeDeclarations declarations]
      (encodeAdmissionResult (admitRun state declarations)) := by
  induction declarations generalizing state with
  | nil =>
      apply run_start state []
      refine admission_equation (equation := A[23]) (environment := [("state", encodeState state)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact someEval (.variable (by rfl))
  | cons declaration rest ih =>
      apply run_start state (declaration :: rest)
      refine admission_equation (equation := A[24])
        (environment := [("first", encodeDeclaration declaration), ("rest", encodeDeclarations rest),
          ("state", encodeState state)]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
        (run_next (admit state declaration) rest ih)
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
        (admit_computes state declaration)

private theorem check_after (state : Option AdmissionState) (witness : ProofWitness) (claimed : Spec.Term) :
    Applies P H "vibe:check-admitted-result" [encodeAdmissionResult state, encodeWitness witness, encode claimed]
      (boolean (match state with | none => false | some after => ProofWitness.check after.theory witness claimed)) := by
  cases state with
  | none => exact ⟨1, by rw [admission_apply _ (by decide +kernel)]; rfl⟩
  | some after =>
      refine admission_equation (equation := A[29])
        (environment := stateEnv after ++ [("witness", encodeWitness witness), ("claimed", encode claimed)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
        (reuse_proof_call (by decide +kernel) (checkProof_computes after.table after.axioms after.definitions witness claimed))

theorem checkAdmitted_computes (state : AdmissionState) (declarations : List Declaration)
    (witness : ProofWitness) (claimed : Spec.Term) :
    Applies P H "vibe:check-admitted" [encodeState state, encodeDeclarations declarations, encodeWitness witness, encode claimed]
      (boolean (checkAdmitted state declarations witness claimed)) := by
  refine admission_equation (equation := A[27])
    (environment := [("state", encodeState state), ("declarations", encodeDeclarations declarations),
      ("witness", encodeWitness witness), ("claimed", encode claimed)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl))
    (.cons (.variable (by rfl)) .nil))) (check_after (admitRun state declarations) witness claimed)
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
    (admitRun_computes state declarations)

private theorem binders_passive (binders : List Nat) : PassiveData P H (encodeBinders binders) := by
  apply PassiveData.list
  intro value member
  obtain ⟨binder, _, rfl⟩ := List.mem_map.mp member
  exact natural_passive P H binder

private theorem binding_passive (binding : Spec.SymId × Spec.SymInfo) : PassiveData P H (encodeBinding binding) := by
  apply PassiveData.node
  · simp [Special]
  · decide +kernel
  · rfl
  · intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact encodedSymbol_passive _ _ _
    · cases binding.2.kind <;> exact .sym _
    · exact binders_passive _

private theorem definition_passive (declaration : Spec.Definition) : PassiveData P H (encodeDefinition declaration) := by
  apply PassiveData.list
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact encodedSymbol_passive _ _ _
  · apply PassiveData.list
    intro value member
    obtain ⟨symbol, _, rfl⟩ := List.mem_map.mp member
    exact encodedSymbol_passive _ _ _
  · exact encoded_passive admissionProgram_dataSeparated _

theorem encodeState_passive (state : AdmissionState) : PassiveData P H (encodeState state) := by
  apply PassiveData.list
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .sym _
  · cases state.phase <;> exact .sym _
  · exact natural_passive P H _
  · apply PassiveData.list
    intro value member
    obtain ⟨binding, _, rfl⟩ := List.mem_map.mp member
    exact binding_passive binding
  · apply PassiveData.list
    intro value member
    obtain ⟨statement, _, rfl⟩ := List.mem_map.mp member
    exact encoded_passive admissionProgram_dataSeparated statement
  · apply PassiveData.list
    intro value member
    obtain ⟨declaration, _, rfl⟩ := List.mem_map.mp member
    exact definition_passive declaration

theorem admissionStart_computes (declarations : List Declaration) :
    Applies P H "vibe:admission-start" [encodeDeclarations declarations]
      (encodeAdmissionResult (admitRun initialAdmission declarations)) := by
  refine admission_equation (equation := A[30])
    (environment := [("declarations", encodeDeclarations declarations)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special]) (.cons ((encodeState_passive initialAdmission).evaluates _)
    (.cons (.variable (by rfl)) .nil)) (admitRun_computes initialAdmission declarations)

theorem checkStatic_computes (declarations : List Declaration) (witness : ProofWitness) (claimed : Spec.Term) :
    Applies P H "vibe:check-static" [encodeDeclarations declarations, encodeWitness witness, encode claimed]
      (boolean (checkStatic declarations witness claimed)) := by
  refine admission_equation (equation := A[31])
    (environment := [("declarations", encodeDeclarations declarations), ("witness", encodeWitness witness), ("claimed", encode claimed)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special]) (.cons ((encodeState_passive initialAdmission).evaluates _)
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
    (checkAdmitted_computes initialAdmission declarations witness claimed)

end Mettapedia.Languages.VibeITP.Presentation.ComputationalAdmission
