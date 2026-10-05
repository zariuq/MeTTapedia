import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaFresheningCorrespondence
import Mettapedia.Languages.MeTTa.HE.Spec.Match.DataPreservation

/-!
# Data frames for generated MeTTa calls

The generated representation stores guest names inside grounded strings.
Its structural tags cannot name evaluator instructions. Matching and merging
preserve this data class; every satisfiable data frame has a model whose
variable values are data. This distinguishes executable control syntax from
arbitrary atoms with the same binding observation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Bindings)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance
open Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance
open Mettapedia.Languages.MeTTa.HE.Spec.Match.DataPreservation
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps

def dataSymbols : List String :=
  ["nik:Sym", "nik:Lit", "nik:Var", "nik:Expr", "nik:List", "nik:Nil", "nik:Cons",
   "nik:Value", "nik:Failure", "nik:Exhausted", "nik:Malformed", "True", "False"]

inductive DataAtom : Atom → Prop where
  | symbol {name : String} : name ∈ dataSymbols → DataAtom (.symbol name)
  | grounded (value : GroundedValue) : DataAtom (.grounded value)
  | expression {items : List Atom} :
      (∀ atom ∈ items, DataAtom atom) → DataAtom (.expression items)

theorem DataAtom.not_var (name : String) : ¬DataAtom (.var name) := by
  rintro ⟨⟩

theorem DataAtom.subatoms (items : List Atom) (data : DataAtom (.expression items)) :
    ∀ atom ∈ items, DataAtom atom := by
  cases data with
  | expression children => exact children

private theorem tagged_data (head : String) (tag : head ∈ dataSymbols) (items : List Atom)
    (children : ∀ atom ∈ items, DataAtom atom) : DataAtom (MeTTaEmit.call head items) := by
  apply DataAtom.expression
  intro atom member
  rcases List.mem_cons.mp member with rfl | member
  · exact .symbol tag
  · exact children atom member

mutual

theorem encode_data (term : Term) : DataAtom (encode term) := by
  cases term with
  | sym name | lit name | var name =>
      apply tagged_data _ (by simp [dataSymbols])
      intro atom member
      rcases List.mem_singleton.mp member with rfl
      exact .grounded _
  | expr items | list items =>
      apply tagged_data _ (by simp [dataSymbols])
      intro atom member
      rcases List.mem_singleton.mp member with rfl
      exact encodeItems_data items
termination_by sizeOf term

theorem encodeItems_data (terms : List Term) : DataAtom (encodeItems terms) := by
  cases terms with
  | nil => exact .symbol (by simp [dataSymbols])
  | cons term terms =>
      apply tagged_data _ (by simp [dataSymbols])
      intro atom member
      rcases List.mem_cons.mp member with rfl | member
      · exact encode_data term
      · rcases List.mem_singleton.mp member with rfl
        exact encodeItems_data terms
termination_by sizeOf terms

end

theorem DataAtom.solution_fixed {atom : Atom} (data : DataAtom atom)
    (valuation : String → Metta.Atom) :
    applyClassSolution valuation (toLeaTTaAtom atom) = toLeaTTaAtom atom := by
  induction data with
  | symbol | grounded => simp only [toLeaTTaAtom, applyClassSolution]
  | expression children ih =>
      simp only [toLeaTTaAtom, applyClassSolution, Metta.Atom.expr.injEq,
        solutionTheory_toLeaTTaAtoms_eq_map, List.map_map]
      exact List.map_congr_left (fun atom member => ih atom member)

/-- Existing live bindings and new pattern bindings remain in the data class. -/
theorem unify_preserves_data {target pattern : Atom} {incoming output : Bindings}
    (targetData : DataAtom target) (stored : AssignmentsIn DataAtom incoming)
    (candidate : UnifyCandidateRel target pattern incoming output) :
    AssignmentsIn DataAtom output := by
  obtain ⟨matched, matchProof, mergeProof, _, _⟩ := candidate
  exact merge_preserves DataAtom.not_var DataAtom.subatoms mergeProof
    (match_preserves DataAtom.not_var DataAtom.subatoms matchProof (.inl targetData)) stored

theorem encoded_pattern_preserves_data (source value : Term) (first : Nat)
    {incoming output : Bindings} (stored : AssignmentsIn DataAtom incoming)
    (candidate : UnifyCandidateRel (encode value) (MeTTaEmit.pattern source first).1.1
      incoming output) : AssignmentsIn DataAtom output :=
  unify_preserves_data (encode_data value) stored candidate

/-- Free equality classes can be assigned inert data without changing any
stored assignment or equality constraint. -/
theorem data_model {bindings : Bindings} (stored : AssignmentsIn DataAtom bindings)
    (satisfiable : ∃ valuation, HEBindingSatisfied valuation bindings) :
    ∃ valuation, HEBindingSatisfied valuation bindings ∧
      ∀ name, ∃ atom, DataAtom atom ∧ valuation name = toLeaTTaAtom atom := by
  classical
  obtain ⟨original, satisfied⟩ := satisfiable
  let inData : Metta.Atom → Prop := fun value =>
    ∃ atom, DataAtom atom ∧ toLeaTTaAtom atom = value
  let clean : Metta.Atom → Metta.Atom := fun value =>
    if inData value then value else .sym "nik:Nil"
  have fixed : ∀ atom, DataAtom atom → clean (toLeaTTaAtom atom) = toLeaTTaAtom atom := by
    intro atom data
    exact if_pos ⟨atom, data, rfl⟩
  refine ⟨clean ∘ original, ⟨?_, ?_⟩, ?_⟩
  · intro name atom member
    have data := stored name atom member
    rw [data.solution_fixed]
    change clean (original name) = toLeaTTaAtom atom
    rw [satisfied.1 name atom member, data.solution_fixed, fixed atom data]
  · intro left right member
    exact congrArg clean (satisfied.2 left right member)
  · intro name
    by_cases supported : inData (original name)
    · obtain ⟨atom, data, same⟩ := supported
      refine ⟨atom, data, ?_⟩
      change clean (original name) = toLeaTTaAtom atom
      rw [← same, fixed atom data]
    · refine ⟨.symbol "nik:Nil", .symbol (by simp [dataSymbols]), ?_⟩
      exact if_neg supported

/-- Successful source matching admits a target model entirely in the data
representation, including variables unused by the pattern. -/
theorem patterns_data_model (source values : List Term) (first : Nat)
    {environment : Env} (matched : matchTerms source values = some environment) :
    ∃ valuation,
      applyClassSolution valuation (toLeaTTaAtom (MeTTaEmit.patterns source first).1.1) =
        toLeaTTaAtom (encodeItems values) ∧
      ∀ name, ∃ atom, DataAtom atom ∧ valuation name = toLeaTTaAtom atom := by
  obtain ⟨output, candidate⟩ :=
    (MeTTaEmit.patterns_unify_iff source values first).mpr ⟨environment, matched⟩
  have stored := unify_preserves_data (encodeItems_data values)
    (AssignmentsIn.empty DataAtom) candidate
  obtain ⟨bindings, matchProof, mergeProof, _, satisfiable⟩ := candidate
  obtain ⟨valuation, satisfied, data⟩ := data_model stored satisfiable
  have inputs :=
    (Spec.Match.SolutionTheory.mergeRel_solution_iff mergeProof valuation).mp satisfied
  have same :=
    (Spec.Match.SolutionTheory.matchRel_solution_iff matchProof valuation).mp inputs.1
  exact ⟨valuation, by simpa only [(encodeItems_data values).solution_fixed] using same.symm,
    data⟩

/-- A fresh recursive call preserves a data-valued model even when its
bindings store symbolic expressions rather than closed encoded values.
The existing match and merge relations determine the output frame. -/
theorem alpha_patterns_extend_data_model (source values : List Term) (first : Nat)
    {environment : Env} (matched : matchTerms source values = some environment)
    {live : List Atom} {query fresh : Atom} {incoming output : Bindings}
    {rename : String → String} (injective : Function.Injective rename)
    (renamed : AlphaRenameAtomRel rename (MeTTaEmit.patterns source first).1.1 fresh)
    (privateNames : ∀ name, AtomOccurs (MeTTaEmit.patterns source first).1.1 name →
      ¬QueryVisibleName live query incoming (rename name))
    (base : String → Metta.Atom) (satisfied : HEBindingSatisfied base incoming)
    (data : ∀ name, ∃ atom, DataAtom atom ∧ base name = toLeaTTaAtom atom)
    (queryValue : applyClassSolution base (toLeaTTaAtom query) =
      toLeaTTaAtom (encodeItems values))
    (candidate : UnifyCandidateRel query fresh incoming output) :
    ∃ extended,
      HEBindingSatisfied extended output ∧
      (∀ name, ∃ atom, DataAtom atom ∧ extended name = toLeaTTaAtom atom) ∧
      (∀ name, QueryVisibleName live query incoming name → extended name = base name) ∧
      applyClassSolution extended (toLeaTTaAtom fresh) =
        toLeaTTaAtom (encodeItems values) := by
  obtain ⟨sourceModel, patternValue, sourceData⟩ :=
    patterns_data_model source values first matched
  obtain ⟨extended, patternSame, incomingSatisfied, agrees, range⟩ :=
    MeTTaEmit.alpha_extend_model_range injective renamed privateNames sourceModel base satisfied
  have querySame : applyClassSolution extended (toLeaTTaAtom query) =
      toLeaTTaAtom (encodeItems values) := by
    exact (MeTTaEmit.query_visible_solution agrees).trans queryValue
  have freshValue := patternSame.trans patternValue
  obtain ⟨bindings, matchProof, mergeProof, _, _⟩ := candidate
  refine ⟨extended,
    (Spec.Match.SolutionTheory.mergeRel_solution_iff mergeProof extended).mpr
      ⟨(Spec.Match.SolutionTheory.matchRel_solution_iff matchProof extended).mpr
        (querySame.trans freshValue.symm), incomingSatisfied⟩,
    ?_, agrees, freshValue⟩
  intro name
  rcases range name with ⟨original, same⟩ | same
  · rw [same]
    exact sourceData original
  · rw [same]
    exact data name

theorem DataAtom.ne_control_symbol {atom : Atom} (data : DataAtom atom)
    {head : String} (control : head ∉ dataSymbols) :
    toLeaTTaAtom atom ≠ .sym head := by
  intro same
  cases data with
  | @symbol name member =>
      have equalName : name = head := by simpa only [toLeaTTaAtom, Metta.Atom.sym.injEq] using same
      exact control (equalName ▸ member)
  | grounded | expression => simp only [toLeaTTaAtom] at same; contradiction

theorem DataAtom.ne_control_call {atom : Atom} (data : DataAtom atom)
    {head : String} (control : head ∉ dataSymbols) (arguments : List Metta.Atom) :
    toLeaTTaAtom atom ≠ .expr (.sym head :: arguments) := by
  intro same
  cases data with
  | symbol | grounded => simp only [toLeaTTaAtom] at same; contradiction
  | @expression items children =>
      cases items with
      | nil => simp [toLeaTTaAtom, toLeaTTaAtoms] at same
      | cons first rest =>
          simp only [toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.expr.injEq,
            List.cons.injEq] at same
          exact (children first (by simp)).ne_control_symbol control same.1

/-- A valuation into inert data cannot hide a control head in a variable. -/
theorem control_shape_of_data_solution (valuation : String → Metta.Atom)
    (values : ∀ name, ∃ atom, DataAtom atom ∧ valuation name = toLeaTTaAtom atom)
    {head : String} (control : head ∉ dataSymbols) {atom : Atom}
    {arguments : List Metta.Atom}
    (same : applyClassSolution valuation (toLeaTTaAtom atom) =
      .expr (.sym head :: arguments)) :
    ∃ items, atom = MeTTaEmit.call head items ∧
      (toLeaTTaAtoms items).map (applyClassSolution valuation) = arguments := by
  cases atom with
  | symbol | grounded => simp only [toLeaTTaAtom, applyClassSolution] at same; contradiction
  | var name =>
      obtain ⟨value, data, assigned⟩ := values name
      simp only [toLeaTTaAtom, applyClassSolution, assigned] at same
      exact (data.ne_control_call control arguments same).elim
  | expression items =>
      cases items with
      | nil => simp [toLeaTTaAtom, toLeaTTaAtoms, applyClassSolution] at same
      | cons first rest =>
          simp only [toLeaTTaAtom, applyClassSolution, toLeaTTaAtoms, List.map_cons,
            Metta.Atom.expr.injEq, List.cons.injEq] at same
          cases first with
          | symbol name =>
              have equalName : name = head := by
                simpa only [toLeaTTaAtom, applyClassSolution, Metta.Atom.sym.injEq] using same.1
              subst name
              exact ⟨rest, rfl, same.2⟩
          | grounded | expression =>
              simp [toLeaTTaAtom, applyClassSolution] at same
          | var name =>
              obtain ⟨value, data, assigned⟩ := values name
              have equalSymbol : toLeaTTaAtom value = .sym head := by
                simpa only [toLeaTTaAtom, applyClassSolution, assigned] using same.1
              exact (data.ne_control_symbol control equalSymbol).elim

/-- An inert model rules out observational aliases that hide executable
control in variables, even when the frame stores symbolic expressions. -/
theorem control_shape_of_model {bindings : Bindings}
    (model : ∃ valuation, HEBindingSatisfied valuation bindings ∧
      ∀ name, ∃ atom, DataAtom atom ∧ valuation name = toLeaTTaAtom atom)
    {head : String} (control : head ∉ dataSymbols) (arguments : List Atom) (emitted : Atom)
    (observed : ∀ valuation, HEBindingSatisfied valuation bindings →
      HEAtomEquationSatisfied valuation emitted (MeTTaEmit.call head arguments)) :
    ∃ items, emitted = MeTTaEmit.call head items ∧
      ∀ valuation, HEBindingSatisfied valuation bindings →
        (toLeaTTaAtoms items).map (applyClassSolution valuation) =
          (toLeaTTaAtoms arguments).map (applyClassSolution valuation) := by
  obtain ⟨valuation, satisfied, values⟩ := model
  have same := observed valuation satisfied
  simp only [HEAtomEquationSatisfied, MeTTaEmit.call, toLeaTTaAtom, toLeaTTaAtoms,
    applyClassSolution, List.map_cons] at same
  obtain ⟨items, shape, _⟩ := control_shape_of_data_solution valuation values control same
  refine ⟨items, shape, ?_⟩
  intro anyModel anySatisfied
  have equalCode := observed anyModel anySatisfied
  rw [shape] at equalCode
  simpa only [HEAtomEquationSatisfied, MeTTaEmit.call, toLeaTTaAtom, toLeaTTaAtoms,
    applyClassSolution, List.map_cons, Metta.Atom.expr.injEq, List.cons.injEq,
    true_and] using equalCode

/-- Observationally selected control retains its actual head and argument
observations in a satisfiable data frame. No executable semantics is redefined. -/
theorem control_shape_of_observation {bindings : Bindings}
    (stored : AssignmentsIn DataAtom bindings)
    (satisfiable : ∃ valuation, HEBindingSatisfied valuation bindings)
    {head : String} (control : head ∉ dataSymbols) (arguments : List Atom) (emitted : Atom)
    (observed : ∀ valuation, HEBindingSatisfied valuation bindings →
      HEAtomEquationSatisfied valuation emitted (MeTTaEmit.call head arguments)) :
    ∃ items, emitted = MeTTaEmit.call head items ∧
      ∀ valuation, HEBindingSatisfied valuation bindings →
        (toLeaTTaAtoms items).map (applyClassSolution valuation) =
          (toLeaTTaAtoms arguments).map (applyClassSolution valuation) :=
  control_shape_of_model (data_model stored satisfiable) control arguments emitted observed

/-- The actual independent selector preserves a generated control head when
its scrutinee and incoming assignments are data. -/
theorem selected_control_shape {target pattern : Atom} {incoming output : Bindings}
    (targetData : DataAtom target) (stored : AssignmentsIn DataAtom incoming)
    {head : String} (control : head ∉ dataSymbols) (arguments : List Atom) (emitted : Atom)
    (selected : UnifySuccessRel target pattern (MeTTaEmit.call head arguments)
      incoming emitted output) :
    AssignmentsIn DataAtom output ∧
      ∃ items, emitted = MeTTaEmit.call head items ∧
        ∀ valuation, HEBindingSatisfied valuation output →
          (toLeaTTaAtoms items).map (applyClassSolution valuation) =
            (toLeaTTaAtoms arguments).map (applyClassSolution valuation) := by
  have outputData := unify_preserves_data targetData stored selected.1
  refine ⟨outputData, control_shape_of_observation outputData ?_ control
    arguments emitted selected.2⟩
  obtain ⟨_, _, _, _, satisfiable⟩ := selected.1
  exact satisfiable

/-- An actual successful fresh selection reflects a source match, records its
occurrence values in every output model, preserves a data model of the caller,
and retains the selected control head. Symbolic caller bindings are permitted. -/
theorem alpha_selected_control_reflects (source values : List Term) (first : Nat)
    {live : List Atom} {query fresh : Atom} {incoming output : Bindings}
    {rename : String → String} (injective : Function.Injective rename)
    (renamed : AlphaRenameAtomRel rename (MeTTaEmit.patterns source first).1.1 fresh)
    (privateNames : ∀ name, AtomOccurs (MeTTaEmit.patterns source first).1.1 name →
      ¬QueryVisibleName live query incoming (rename name))
    (base : String → Metta.Atom) (satisfied : HEBindingSatisfied base incoming)
    (data : ∀ name, ∃ atom, DataAtom atom ∧ base name = toLeaTTaAtom atom)
    (queryValue : ∀ valuation, HEBindingSatisfied valuation incoming →
      applyClassSolution valuation (toLeaTTaAtom query) = toLeaTTaAtom (encodeItems values))
    {head : String} (control : head ∉ dataSymbols) (arguments : List Atom) (emitted : Atom)
    (selected : UnifySuccessRel query fresh (MeTTaEmit.call head arguments)
      incoming emitted output) :
    ∃ environment, matchTerms source values = some environment ∧
      (∀ valuation, HEBindingSatisfied valuation output →
        MeTTaEmit.ValuationFor (valuation ∘ rename) first environment) ∧
      (∃ extended, HEBindingSatisfied extended output ∧
        (∀ name, ∃ atom, DataAtom atom ∧ extended name = toLeaTTaAtom atom) ∧
        ∀ name, QueryVisibleName live query incoming name → extended name = base name) ∧
      ∃ items, emitted = MeTTaEmit.call head items ∧
        ∀ valuation, HEBindingSatisfied valuation output →
          (toLeaTTaAtoms items).map (applyClassSolution valuation) =
            (toLeaTTaAtoms arguments).map (applyClassSolution valuation) := by
  obtain ⟨_, _, _, _, original, originalSatisfied⟩ := selected.1
  obtain ⟨environment, matched, _⟩ :=
    MeTTaEmit.alpha_patterns_binding_observation_observed source values first
      renamed queryValue selected.1 original originalSatisfied
  obtain ⟨extended, outputSatisfied, outputData, agrees, _⟩ :=
    alpha_patterns_extend_data_model source values first matched injective renamed privateNames
      base satisfied data (queryValue base satisfied) selected.1
  refine ⟨environment, matched, ?_, ⟨extended, outputSatisfied, outputData, agrees⟩,
    control_shape_of_model ⟨extended, outputSatisfied, outputData⟩ control
      arguments emitted selected.2⟩
  intro valuation model
  obtain ⟨other, otherMatch, reads⟩ :=
    MeTTaEmit.alpha_patterns_binding_observation_observed source values first
      renamed queryValue selected.1 valuation model
  have same : environment = other := Option.some.inj (matched.symm.trans otherMatch)
  exact same ▸ reads

/-- Guest names resembling instructions remain quoted data. -/
theorem quoted_control_is_data : DataAtom (encode (.expr [.sym "return", .var "caller"])) :=
  encode_data _

private def symbolicFrame : Bindings :=
  (Bindings.empty.assign "leaf" (.symbol "nik:Nil")).assign "wrapped"
    (MeTTaEmit.call "nik:Cons" [.var "leaf", .symbol "nik:Nil"])

/-- A symbolic stored expression can have an entirely inert interpretation. -/
theorem symbolic_frame_has_data_model :
    ∃ valuation, HEBindingSatisfied valuation symbolicFrame ∧
      ∀ name, ∃ atom, DataAtom atom ∧ valuation name = toLeaTTaAtom atom := by
  let closed := MeTTaEmit.call "nik:Cons" [.symbol "nik:Nil", .symbol "nik:Nil"]
  let valuation : String → Metta.Atom := fun name =>
    if name = "wrapped" then toLeaTTaAtom closed else .sym "nik:Nil"
  refine ⟨valuation, ⟨?_, ?_⟩, ?_⟩
  · intro name value member
    have casesOf : (name = "leaf" ∧ value = .symbol "nik:Nil") ∨
        (name = "wrapped" ∧ value =
          MeTTaEmit.call "nik:Cons" [.var "leaf", .symbol "nik:Nil"]) := by
      simpa [symbolicFrame, Bindings.assign, Bindings.empty, Bindings.isBound,
        Bindings.lookup] using member
    rcases casesOf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [valuation, closed, MeTTaEmit.call, toLeaTTaAtom, toLeaTTaAtoms, applyClassSolution]
  · intro left right member
    simp [symbolicFrame, Bindings.assign, Bindings.empty] at member
  · intro name
    by_cases same : name = "wrapped"
    · refine ⟨closed, tagged_data _ (by simp [dataSymbols]) _ ?_, ?_⟩
      · intro atom member
        simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
        subst atom
        exact .symbol (by simp [dataSymbols])
      · exact if_pos same
    · exact ⟨.symbol "nik:Nil", .symbol (by simp [dataSymbols]), if_neg same⟩

/-- Requiring every stored expression itself to be closed would exclude that
valid symbolic frame; the execution invariant therefore uses a data model. -/
theorem symbolic_frame_is_not_closed_data : ¬AssignmentsIn DataAtom symbolicFrame := by
  intro stored
  have wrapped := stored "wrapped"
    (MeTTaEmit.call "nik:Cons" [.var "leaf", .symbol "nik:Nil"])
    (by simp [symbolicFrame, Bindings.assign, Bindings.empty, Bindings.isBound, Bindings.lookup])
  exact DataAtom.not_var "leaf" (wrapped.subatoms _ (.var "leaf") (by simp))

/-- A code-valued binding defeats raw control-shape reflection without the
data-frame invariant. -/
theorem code_alias_observation (valuation : String → Metta.Atom)
    (satisfied : HEBindingSatisfied valuation
      (Bindings.empty.assign "saved" (MeTTaEmit.returned (.symbol "nik:Nil")))) :
    HEAtomEquationSatisfied valuation (.var "saved")
      (MeTTaEmit.returned (.symbol "nik:Nil")) := by
  simpa only [HEAtomEquationSatisfied, toLeaTTaAtom, applyClassSolution] using
    satisfied.1 "saved" (MeTTaEmit.returned (.symbol "nik:Nil"))
      (by simp [Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup])

theorem code_alias_has_no_control_shape :
    ¬∃ items, Atom.var "saved" = MeTTaEmit.call "return" items := by
  simp [MeTTaEmit.call]

theorem code_alias_is_satisfiable :
    ∃ valuation, HEBindingSatisfied valuation
      (Bindings.empty.assign "saved" (MeTTaEmit.returned (.symbol "nik:Nil"))) := by
  refine ⟨fun _ => .expr [.sym "return", .sym "nik:Nil"], ?_, ?_⟩
  · intro name value member
    have same : name = "saved" ∧ value = MeTTaEmit.returned (.symbol "nik:Nil") := by
      simpa [Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup] using member
    rcases same with ⟨rfl, rfl⟩
    simp [MeTTaEmit.returned, MeTTaEmit.call, toLeaTTaAtom, toLeaTTaAtoms, applyClassSolution]
  · intro left right member
    simp [Bindings.empty, Bindings.assign] at member

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaData
