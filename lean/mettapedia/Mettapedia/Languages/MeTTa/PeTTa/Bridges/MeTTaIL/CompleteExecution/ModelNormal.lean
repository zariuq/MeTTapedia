import Mettapedia.Languages.MeTTa.PeTTa.EquationEquality
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Canonical
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.QuoteDropNormal
import Mettapedia.OSLF.MeTTaIL.WrapperLaws

/-!
# The model normal form, in MeTTa

`gslt:canon:model-normal` is `Wrappers.modelNormal` (`model_normal_returns`), for every pattern whose
names are in the table, every reflective presentation and every list of declared laws whose units are in
the table: bottom up, the quote-drop test at each constructor
(`gslt:rule:scope-reflective-normalize-finish`, proved in the scoped library and raised), deep splicing
and unit removal at each collection of a kind with a law (`gslt:canon:deep-splice-all`), a set's elements
in canonical form once each (`gslt:canon:set-form`), then the wrapper collapse (`gslt:canon:wrap-finish`).

The model normal form adds no name but the units of the declared laws (`names_modelNormal`), so a name
table that holds those units keeps covering it (`covered_modelNormal`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.OSLF.MeTTaIL Syntax CollectionLaws CanonicalBags CanonicalCompare
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (finishNormalizeReflectiveApply)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open StandardWire

/-! ## The quote-drop test at a constructor -/

private def scopedFinishProofLibrary : Library :=
  ⟨{equations := [], declarations := []},
    {equations := [RuleExecutionProgram.scopedProgram.equations[183]'(by decide +kernel)],
     declarations := [RuleExecutionProgram.scopedProgram.declarations[183]'(by decide +kernel)]},
    ["gslt:rule:scope-reflective-normalize-finish"]⟩

private def scopedFinishProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || head == "gslt:rule:scope-reflective-normalize-finish"

private theorem scopedFinishProof_checked : scopedFinishProofLibrary.check = true := by decide +kernel

private local instance finishEquationEq : DecidableEq SpaceSemantics.Equation :=
  SpaceSemantics.Equation.decideEq

private theorem scopedFinishProof_agreement : ProgramAgreementOn scopedFinishProofHeads
    scopedFinishProofLibrary.runtime scopedLibrary.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

/-- Walk a body of the scoped library. -/
syntax "scoped_eval" (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| scoped_eval $[unfolding [$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in scopedFinishProof_checked using scopedFinishProof_agreement; metta_eval with scopedFinishProof_checked in scopedFinishProof_agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, pattern_symbol_unmatched,
        patternValue, patternsValue, encodePattern, encodePatterns, encodeBinder, encodeRest, $extra,*]))

/-- **`gslt:rule:scope-reflective-normalize-finish` is the quote-drop test at a constructor**, in the
scoped library. -/
@[metta_head "gslt:rule:scope-reflective-normalize-finish"]
theorem scoped_finish_returns (state : State) (declaration : ReflectivePresentationDecl) (label : String)
    (arguments : List Pattern) :
    PureReturns scopedLibrary.runtime [] state
      (apply "gslt:rule:scope-reflective-normalize-finish" [encoded (.string declaration.quoteConstructor),
        encoded (.string declaration.dropConstructor), encoded (.string label), patternsValue arguments]) state
      (patternValue (finishNormalizeReflectiveApply declaration label arguments)) := by
  by_cases quoted : label = declaration.quoteConstructor
  · subst quoted
    have kept : ∀ arguments : List Pattern, (∀ inner name, arguments ≠ [.apply inner [name]]) →
        finishNormalizeReflectiveApply declaration declaration.quoteConstructor arguments =
          .apply declaration.quoteConstructor arguments := by
      intro arguments ordinary
      rcases Wrappers.finish_cases (declaration := declaration) declaration.quoteConstructor arguments with
        same | ⟨name, shape, _⟩
      · exact same
      · exact absurd shape (ordinary _ name)
    match arguments with
    | [.apply inner [name]] =>
      by_cases dropped : inner = declaration.dropConstructor
      · subst dropped
        have shape : finishNormalizeReflectiveApply declaration declaration.quoteConstructor
            [.apply declaration.dropConstructor [name]] = name := by
          simp [finishNormalizeReflectiveApply]
        rw [shape]
        scoped_eval
      · have shape : finishNormalizeReflectiveApply declaration declaration.quoteConstructor [.apply inner [name]] =
            .apply declaration.quoteConstructor [.apply inner [name]] := by
          simp [finishNormalizeReflectiveApply, dropped]
        rw [shape]
        scoped_eval unfolding [dropped]
    | [] =>
      rw [kept [] (by simp)]
      scoped_eval
    | first :: second :: rest =>
      rw [kept (first :: second :: rest) (by simp)]
      cases first <;> scoped_eval
    | [.apply inner []] =>
      rw [kept _ (by simp)]
      scoped_eval
    | [.apply inner (first :: second :: rest)] =>
      rw [kept _ (by simp)]
      scoped_eval
    | [.bvar index] =>
      rw [kept _ (by simp)]
      scoped_eval
    | [.fvar name] =>
      rw [kept _ (by simp)]
      scoped_eval
    | [.lambda binder body] =>
      rw [kept _ (by simp)]
      scoped_eval
    | [.multiLambda arity binders body] =>
      rw [kept _ (by simp)]
      scoped_eval
    | [.subst body replacement] =>
      rw [kept _ (by simp)]
      scoped_eval
    | [.collection kind elements rest] =>
      rw [kept _ (by simp)]
      scoped_eval
  · have shape : finishNormalizeReflectiveApply declaration label arguments = .apply label arguments := by
      simp [finishNormalizeReflectiveApply, quoted]
    rw [shape]
    scoped_eval unfolding [quoted]

/-- The quote-drop test at a constructor, in the laws library. -/
theorem laws_finish_returns (state : State) (declaration : ReflectivePresentationDecl) (label : String)
    (arguments : List Pattern) :
    PureReturns lawsLibrary.runtime [] state
      (apply "gslt:rule:scope-reflective-normalize-finish" [encoded (.string declaration.quoteConstructor),
        encoded (.string declaration.dropConstructor), encoded (.string label), patternsValue arguments]) state
      (patternValue (finishNormalizeReflectiveApply declaration label arguments)) := by
  have complete : PureReturns runtime [] state
      (apply "gslt:rule:scope-reflective-normalize-finish" [encoded (.string declaration.quoteConstructor),
        encoded (.string declaration.dropConstructor), encoded (.string label), patternsValue arguments]) state
      (patternValue (finishNormalizeReflectiveApply declaration label arguments)) := by
    metta_raise ["quote", "drop", "head", "children"] (scoped_finish_returns state declaration label arguments)
  exact complete

/-! ## Raised into the canonical library -/

/-- The quote-drop test at a constructor, in the canonical library. -/
theorem canonical_finish_returns (state : State) (declaration : ReflectivePresentationDecl) (label : String)
    (arguments : List Pattern) :
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:rule:scope-reflective-normalize-finish" [encoded (.string declaration.quoteConstructor),
        encoded (.string declaration.dropConstructor), encoded (.string label), patternsValue arguments]) state
      (patternValue (finishNormalizeReflectiveApply declaration label arguments)) := by
  exact laws_finish_returns state declaration label arguments

theorem canonical_append_patterns_returns (state : State) (left right : List Pattern) :
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:automata:append" [patternsValue left, patternsValue right]) state (patternsValue (left ++ right)) := by
  exact laws_append_patterns_returns state left right

theorem canonical_law_for_returns (state : State) (kind : CollType) (laws : List Laws) :
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:laws:law-for" [lawsValue laws, encoded (encodeCollectionType kind)]) state
      (encoded (encodeOption lawTerm (lawFor laws kind))) := by
  exact law_for_returns state kind laws

/-! ## Name tables -/

/-- Deep splicing adds no name. -/
theorem names_deepSplice (law : Laws) (pattern : Pattern) :
    ∀ item ∈ Wrappers.deepSplice law pattern, ∀ name ∈ CanonicalCompare.names item,
      name ∈ CanonicalCompare.names pattern := by
  induction pattern using Pattern.inductionOn with
  | hcollection kind elements rest ih =>
    intro item member name named
    cases rest with
    | none =>
      rw [Wrappers.deepSplice] at member
      split at member
      · obtain ⟨element, elementIn, inside⟩ := List.mem_flatMap.mp member
        simp only [CanonicalCompare.names, List.mem_append, CanonicalCompare.mem_namesList]
        exact .inl ⟨element, elementIn, ih element elementIn item inside name named⟩
      · rw [List.mem_singleton] at member
        subst member
        exact named
    | some other =>
      have kept : Wrappers.deepSplice law (.collection kind elements (some other)) =
          [.collection kind elements (some other)] := by
        simp [Wrappers.deepSplice]
      rw [kept, List.mem_singleton] at member
      subst member
      exact named
  | happly label arguments _ =>
    intro item member name named
    cases arguments with
    | nil =>
      rw [Wrappers.deepSplice] at member
      split at member
      · simp at member
      · rw [List.mem_singleton] at member
        subst member
        exact named
    | cons first others =>
      have kept : Wrappers.deepSplice law (.apply label (first :: others)) = [.apply label (first :: others)] := by
        simp [Wrappers.deepSplice]
      rw [kept, List.mem_singleton] at member
      subst member
      exact named
  | hbvar index =>
    intro item member name named; simp [Wrappers.deepSplice] at member; subst member; exact named
  | hfvar other =>
    intro item member name named; simp [Wrappers.deepSplice] at member; subst member; exact named
  | hlambda binder body _ =>
    intro item member name named; simp [Wrappers.deepSplice] at member; subst member; exact named
  | hmultiLambda arity binders body _ =>
    intro item member name named; simp [Wrappers.deepSplice] at member; subst member; exact named
  | hsubst body replacement _ _ =>
    intro item member name named; simp [Wrappers.deepSplice] at member; subst member; exact named

/-- The wrapper collapse adds no name but the unit. -/
theorem names_wrapFinish (law : Laws) (kind : CollType) (items : List Pattern) (rest : Option String)
    (name : String) :
    name ∈ CanonicalCompare.names (Wrappers.wrapFinish law kind items rest) →
      name ∈ CanonicalCompare.names (.collection kind items rest) ∨ law.unit = some name := by
  intro member
  unfold Wrappers.wrapFinish at member
  split at member
  · exact .inl (by simpa [CanonicalCompare.names, CanonicalCompare.namesList] using member)
  · split at member
    · rename_i label unit
      simp only [CanonicalCompare.names, CanonicalCompare.namesList, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rw [member]
      exact .inr unit
    · exact .inl member
  · exact .inl member

/-- The canonical form adds no name. -/
theorem names_canon (pattern : Pattern) :
    ∀ name ∈ CanonicalCompare.names (canon pattern), name ∈ CanonicalCompare.names pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro name named; rw [canon] at named; exact named
  | hfvar other => intro name named; rw [canon] at named; exact named
  | happly label arguments ih =>
    intro name named
    rw [canon] at named
    simp only [CanonicalCompare.names, List.mem_cons, CanonicalCompare.mem_namesList, List.mem_map] at named ⊢
    rcases named with same | ⟨_, ⟨argument, argumentIn, rfl⟩, inside⟩
    · exact .inl same
    · exact .inr ⟨argument, argumentIn, ih argument argumentIn name inside⟩
  | hlambda binder body ih =>
    intro name named
    rw [canon] at named
    simp only [CanonicalCompare.names, List.mem_append] at named ⊢
    exact named.imp id (ih name)
  | hmultiLambda arity binders body ih =>
    intro name named
    rw [canon] at named
    simp only [CanonicalCompare.names, List.mem_append] at named ⊢
    exact named.imp id (ih name)
  | hsubst body replacement bodyIH replacementIH =>
    intro name named
    rw [canon] at named
    simp only [CanonicalCompare.names, List.mem_append] at named ⊢
    exact named.imp (bodyIH name) (replacementIH name)
  | hcollection kind elements rest ih =>
    intro name named
    rw [canon] at named
    simp only [CanonicalCompare.names, List.mem_append, CanonicalCompare.mem_namesList] at named ⊢
    rcases named with ⟨item, itemIn, inside⟩ | inRest
    · obtain ⟨element, elementIn, rfl⟩ := List.mem_map.mp ((arrange_mem item).mp itemIn)
      exact .inl ⟨element, elementIn, ih element elementIn name inside⟩
    · exact .inr inRest

/-- A set's elements in canonical form once each add no name. -/
theorem names_setForm (kind : CollType) (items : List Pattern) (name : String)
    (member : name ∈ CanonicalCompare.namesList (Wrappers.setForm kind items)) :
    name ∈ CanonicalCompare.namesList items := by
  cases kind with
  | vec => exact member
  | hashBag => exact member
  | hashSet =>
    rw [Wrappers.setForm_set] at member
    obtain ⟨item, itemIn, inside⟩ := CanonicalCompare.mem_namesList.mp member
    obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp itemIn)
    exact CanonicalCompare.mem_namesList.mpr ⟨original, originalIn, names_canon original name inside⟩

/-- **The model normal form adds no name but the units of the declared laws.** -/
theorem names_modelNormal (laws : List Laws) (declaration : ReflectivePresentationDecl) (pattern : Pattern)
    (name : String) :
    name ∈ CanonicalCompare.names (Wrappers.modelNormal laws declaration pattern) →
      name ∈ CanonicalCompare.names pattern ∨ ∃ law ∈ laws, law.unit = some name := by
  induction pattern using Pattern.inductionOn generalizing name with
  | hbvar index => intro member; rw [Wrappers.modelNormal] at member; exact .inl member
  | hfvar other => intro member; rw [Wrappers.modelNormal] at member; exact .inl member
  | happly label arguments ih =>
    intro member
    rw [Wrappers.modelNormal] at member
    have inside := names_finish declaration label _ name member
    simp only [CanonicalCompare.names, List.mem_cons, CanonicalCompare.mem_namesList, List.mem_map] at inside ⊢
    rcases inside with same | ⟨_, ⟨argument, argumentIn, rfl⟩, named⟩
    · exact .inl (.inl same)
    · exact (ih argument argumentIn name named).imp (fun old => .inr ⟨argument, argumentIn, old⟩) id
  | hlambda binder body ih =>
    intro member
    rw [Wrappers.modelNormal] at member
    simp only [CanonicalCompare.names, List.mem_append] at member ⊢
    rcases member with bound | inside
    · exact .inl (.inl bound)
    · exact (ih name inside).imp .inr id
  | hmultiLambda arity binders body ih =>
    intro member
    rw [Wrappers.modelNormal] at member
    simp only [CanonicalCompare.names, List.mem_append] at member ⊢
    rcases member with bound | inside
    · exact .inl (.inl bound)
    · exact (ih name inside).imp .inr id
  | hsubst body replacement bodyIH replacementIH =>
    intro member
    rw [Wrappers.modelNormal] at member
    simp only [CanonicalCompare.names, List.mem_append] at member ⊢
    rcases member with inside | inside
    · exact (bodyIH name inside).imp .inl id
    · exact (replacementIH name inside).imp .inr id
  | hcollection kind elements rest ih =>
    intro member
    have mapped : name ∈ CanonicalCompare.names
        (.collection kind (elements.map (Wrappers.modelNormal laws declaration)) rest) ∨
        ∃ law ∈ laws, law.unit = some name := by
      cases found : lawFor laws kind with
      | none =>
        rw [Wrappers.modelNormal, found] at member
        exact .inl member
      | some law =>
        rw [Wrappers.modelNormal, found] at member
        rcases names_wrapFinish law kind _ rest name member with inCollection | unit
        · simp only [CanonicalCompare.names, List.mem_append] at inCollection ⊢
          rcases inCollection with inItems | inRest
          · obtain ⟨item, itemIn, named⟩ := CanonicalCompare.mem_namesList.mp (names_setForm kind _ name inItems)
            obtain ⟨original, originalIn, spliced⟩ := List.mem_flatMap.mp itemIn
            exact .inl (.inl (CanonicalCompare.mem_namesList.mpr
              ⟨original, originalIn, names_deepSplice law original item spliced name named⟩))
          · exact .inl (.inr inRest)
        · exact .inr ⟨law, List.mem_of_find?_eq_some found, unit⟩
    rcases mapped with inMapped | unit
    · simp only [CanonicalCompare.names, List.mem_append, CanonicalCompare.mem_namesList, List.mem_map]
        at inMapped ⊢
      rcases inMapped with ⟨_, ⟨element, elementIn, rfl⟩, named⟩ | inRest
      · exact (ih element elementIn name named).imp (fun old => .inl ⟨element, elementIn, old⟩) id
      · exact .inl (.inr inRest)
    · exact .inr unit

/-- **The model normal form keeps a name table's coverage** when the table holds the declared units. -/
theorem covered_modelNormal {table : List String} {laws : List Laws} (declaration : ReflectivePresentationDecl)
    (units : ∀ law ∈ laws, ∀ label, law.unit = some label → label ∈ table) {pattern : Pattern}
    (covered : CanonicalCompare.Covered table pattern) :
    CanonicalCompare.Covered table (Wrappers.modelNormal laws declaration pattern) := fun name member =>
  (names_modelNormal laws declaration pattern name member).elim (covered name)
    fun ⟨law, lawIn, unit⟩ => units law lawIn name unit

/-! ## Deep splicing and the wrapper collapse -/

/-- What `gslt:canon:deep-splice` returns. -/
abbrev DeepSpliceAt (state : State) (law : Laws) (item : Pattern) : Prop :=
  PureReturns canonicalLibrary.runtime [] state
    (apply "gslt:canon:deep-splice" [encoded (lawTerm law), patternValue item]) state
    (patternsValue (Wrappers.deepSplice law item))

@[metta_head "gslt:canon:deep-splice-all"]
theorem deep_splice_all_of (state : State) (law : Laws) : ∀ items : List Pattern,
    (∀ item ∈ items, DeepSpliceAt state law item) →
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:deep-splice-all" [encoded (lawTerm law), patternsValue items]) state
      (patternsValue (items.flatMap (Wrappers.deepSplice law)))
  | [], _ => by canonical_eval unfolding [patternsValue, encodePatterns]
  | item :: rest, each => by
    have here := each item (by simp)
    have later := deep_splice_all_of state law rest (fun other member => each other (by simp [member]))
    have joined := canonical_append_patterns_returns state (Wrappers.deepSplice law item)
      (rest.flatMap (Wrappers.deepSplice law))
    canonical_eval [here, later, joined] unfolding [patternsValue, encodePatterns, List.flatMap_cons]

/-- **`gslt:canon:deep-splice` is `Wrappers.deepSplice`.** -/
@[metta_head "gslt:canon:deep-splice"]
theorem deep_splice_returns (state : State) (law : Laws) (item : Pattern) : DeepSpliceAt state law item := by
  obtain ⟨kind, unit⟩ := law
  induction item using Pattern.inductionOn with
  | hcollection actual elements rest ih =>
    cases rest with
    | none =>
      by_cases same : actual = kind
      · subst same
        have inner := deep_splice_all_of state ⟨actual, unit⟩ elements ih
        have shape : Wrappers.deepSplice ⟨actual, unit⟩ (.collection actual elements none) =
            elements.flatMap (Wrappers.deepSplice ⟨actual, unit⟩) := by
          rw [Wrappers.deepSplice]; simp
        unfold DeepSpliceAt
        rw [shape]
        canonical_eval [inner]
          unfolding [lawTerm, patternValue, patternsValue, encodePattern, encodePatterns, encodeRest]
      · have different : encodeCollectionType actual ≠ encodeCollectionType kind :=
          fun equal => same (encodeCollectionType_injective equal)
        have shape : Wrappers.deepSplice ⟨kind, unit⟩ (.collection actual elements none) =
            [.collection actual elements none] := by
          rw [Wrappers.deepSplice]; simp [same]
        unfold DeepSpliceAt
        rw [shape]
        canonical_eval unfolding [lawTerm, different, patternValue, patternsValue, encodePattern, encodePatterns,
          encodeRest]
    | some name =>
      have shape : Wrappers.deepSplice ⟨kind, unit⟩ (.collection actual elements (some name)) =
          [.collection actual elements (some name)] := by
        simp [Wrappers.deepSplice]
      unfold DeepSpliceAt
      rw [shape]
      canonical_eval unfolding [lawTerm, patternValue, patternsValue, encodePattern, encodePatterns, encodeRest]
  | happly label arguments _ =>
    cases arguments with
    | nil =>
      cases unit with
      | none =>
        have shape : Wrappers.deepSplice ⟨kind, none⟩ (.apply label []) = [.apply label []] := by
          simp [Wrappers.deepSplice]
        unfold DeepSpliceAt
        rw [shape]
        canonical_eval unfolding [lawTerm, unitTerm, patternValue, patternsValue, encodePattern, encodePatterns]
      | some name =>
        by_cases same : label = name
        · subst same
          have shape : Wrappers.deepSplice ⟨kind, some label⟩ (.apply label []) = [] := by
            simp [Wrappers.deepSplice]
          unfold DeepSpliceAt
          rw [shape]
          canonical_eval unfolding [lawTerm, unitTerm, patternValue, patternsValue, encodePattern, encodePatterns]
        · have different : label ≠ name := same
          have shape : Wrappers.deepSplice ⟨kind, some name⟩ (.apply label []) = [.apply label []] := by
            simp [Wrappers.deepSplice, Ne.symm different]
          unfold DeepSpliceAt
          rw [shape]
          canonical_eval unfolding [lawTerm, unitTerm, different, Ne.symm different, patternValue, patternsValue,
            encodePattern, encodePatterns]
    | cons first others =>
      have shape : Wrappers.deepSplice ⟨kind, unit⟩ (.apply label (first :: others)) =
          [.apply label (first :: others)] := by
        simp [Wrappers.deepSplice]
      unfold DeepSpliceAt
      rw [shape]
      canonical_eval unfolding [lawTerm, patternValue, patternsValue, encodePattern, encodePatterns]
  | hbvar index =>
    have shape : Wrappers.deepSplice ⟨kind, unit⟩ (.bvar index) = [.bvar index] := by simp [Wrappers.deepSplice]
    unfold DeepSpliceAt
    rw [shape]
    canonical_eval unfolding [lawTerm, patternValue, patternsValue, encodePattern, encodePatterns]
  | hfvar name =>
    have shape : Wrappers.deepSplice ⟨kind, unit⟩ (.fvar name) = [.fvar name] := by simp [Wrappers.deepSplice]
    unfold DeepSpliceAt
    rw [shape]
    canonical_eval unfolding [lawTerm, patternValue, patternsValue, encodePattern, encodePatterns]
  | hlambda binder body _ =>
    have shape : Wrappers.deepSplice ⟨kind, unit⟩ (.lambda binder body) = [.lambda binder body] := by
      simp [Wrappers.deepSplice]
    unfold DeepSpliceAt
    rw [shape]
    canonical_eval unfolding [lawTerm, patternValue, patternsValue, encodePattern, encodePatterns, encodeBinder]
  | hmultiLambda arity binders body _ =>
    have shape : Wrappers.deepSplice ⟨kind, unit⟩ (.multiLambda arity binders body) =
        [.multiLambda arity binders body] := by
      simp [Wrappers.deepSplice]
    unfold DeepSpliceAt
    rw [shape]
    canonical_eval unfolding [lawTerm, patternValue, patternsValue, encodePattern, encodePatterns]
  | hsubst body replacement _ _ =>
    have shape : Wrappers.deepSplice ⟨kind, unit⟩ (.subst body replacement) = [.subst body replacement] := by
      simp [Wrappers.deepSplice]
    unfold DeepSpliceAt
    rw [shape]
    canonical_eval unfolding [lawTerm, patternValue, patternsValue, encodePattern, encodePatterns]

/-- **`gslt:canon:wrap-finish` is `Wrappers.wrapFinish`.** -/
@[metta_head "gslt:canon:wrap-finish"]
theorem wrap_finish_returns (state : State) (law : Laws) (kind : CollType) (items : List Pattern)
    (rest : Option String) :
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:wrap-finish" [encoded (lawTerm law), encoded (encodeCollectionType kind), patternsValue items,
        encoded (encodeRest rest)]) state
      (patternValue (Wrappers.wrapFinish law kind items rest)) := by
  obtain ⟨lawKind, unit⟩ := law
  match rest, items with
  | none, [] =>
    cases unit with
    | none =>
      canonical_eval unfolding [Wrappers.wrapFinish, lawTerm, unitTerm, encodeRest, patternValue, patternsValue,
        encodePattern, encodePatterns]
    | some name =>
      canonical_eval unfolding [Wrappers.wrapFinish, lawTerm, unitTerm, encodeRest, patternValue, patternsValue,
        encodePattern, encodePatterns]
  | none, [item] =>
    canonical_eval unfolding [Wrappers.wrapFinish, lawTerm, encodeRest, patternValue, patternsValue, encodePattern,
      encodePatterns]
  | none, first :: second :: others =>
    canonical_eval unfolding [Wrappers.wrapFinish, lawTerm, encodeRest, patternValue, patternsValue, encodePattern,
      encodePatterns]
  | some name, items =>
    canonical_eval unfolding [Wrappers.wrapFinish, lawTerm, encodeRest, patternValue, patternsValue, encodePattern,
      encodePatterns]

/-! ## Sets -/

/-- **`gslt:canon:member` decides membership**, by structural equality of the encodings. -/
@[metta_head "gslt:canon:member"]
theorem member_returns (state : State) (item : Pattern) : ∀ items : List Pattern,
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:member" [patternValue item, patternsValue items]) state
      (Effects.boolean (decide (item ∈ items)))
  | [] => by canonical_eval unfolding [patternsValue, encodePatterns]
  | first :: rest => by
    have later := member_returns state item rest
    by_cases same : item = first
    · subst same
      canonical_eval unfolding [patternsValue, encodePatterns, List.mem_cons, true_or, decide_true]
    · have different : encodePattern item ≠ encodePattern first :=
        fun equal => same (InferenceCettaWire.encodePattern_injective equal)
      simp only [List.mem_cons, same, false_or]
      canonical_eval [later] unfolding [different, patternsValue, encodePatterns]

/-- **`gslt:canon:dedup` is `List.dedup`**: an element met again later is dropped. -/
@[metta_head "gslt:canon:dedup"]
theorem dedup_returns (state : State) : ∀ items : List Pattern,
    PureReturns canonicalLibrary.runtime [] state (apply "gslt:canon:dedup" [patternsValue items]) state
      (patternsValue items.dedup)
  | [] => by canonical_eval unfolding [patternsValue, encodePatterns, List.dedup_nil]
  | first :: rest => by
    have tail := dedup_returns state rest
    have tested := member_returns state first rest
    by_cases member : first ∈ rest
    · rw [List.dedup_cons_of_mem member]
      canonical_eval [tail, tested] unfolding [member, patternsValue, encodePatterns]
    · rw [List.dedup_cons_of_notMem member]
      canonical_eval [tail, tested] unfolding [member, patternsValue, encodePatterns]

/-- **`gslt:canon:set-form` is `Wrappers.setForm`** on covered items: a set's elements in canonical form
once each, a bag's or a vector's as they are. -/
@[metta_head "gslt:canon:set-form"]
theorem set_form_returns (state : State) {table : List String} (ordered : NameOrdered table) (kind : CollType)
    (items : List Pattern) (covered : ∀ item ∈ items, Covered table item) :
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:set-form" [tableValue table, encoded (encodeCollectionType kind), patternsValue items]) state
      (patternsValue (Wrappers.setForm kind items)) := by
  cases kind with
  | vec =>
    have isSet : PureReturns canonicalLibrary.runtime [] state
        (apply "gslt:canon:is-set" [encoded (encodeCollectionType .vec)]) state (Effects.boolean false) :=
      is_set_returns state .vec
    canonical_eval [isSet] unfolding [Wrappers.setForm]
  | hashBag =>
    have isSet : PureReturns canonicalLibrary.runtime [] state
        (apply "gslt:canon:is-set" [encoded (encodeCollectionType .hashBag)]) state (Effects.boolean false) :=
      is_set_returns state .hashBag
    canonical_eval [isSet] unfolding [Wrappers.setForm]
  | hashSet =>
    have isSet : PureReturns canonicalLibrary.runtime [] state
        (apply "gslt:canon:is-set" [encoded (encodeCollectionType .hashSet)]) state (Effects.boolean true) :=
      is_set_returns state .hashSet
    have canonical := canon_list_of state table items
      (fun item member => canon_by_returns state ordered item (covered item member))
    have mapped : items.map (canonBy table) = items.map canon :=
      List.map_congr_left fun item member => (canonBy_eq_canon ordered item (covered item member)).1
    rw [mapped] at canonical
    have deduped := dedup_returns state (items.map canon)
    canonical_eval [isSet, canonical, deduped] unfolding [Wrappers.setForm]

/-! ## The model normal form -/

/-- What `gslt:canon:model-normal` returns. -/
abbrev ModelNormalAt (state : State) (table : List String) (declaration : ReflectivePresentationDecl)
    (laws : List Laws) (pattern : Pattern) : Prop :=
  PureReturns canonicalLibrary.runtime [] state
    (apply "gslt:canon:model-normal" [tableValue table, encoded (.string declaration.quoteConstructor),
      encoded (.string declaration.dropConstructor), lawsValue laws, patternValue pattern])
    state (patternValue (Wrappers.modelNormal laws declaration pattern))

@[metta_head "gslt:canon:model-normal-list"]
theorem model_normal_list_of (state : State) (table : List String) (declaration : ReflectivePresentationDecl)
    (laws : List Laws) : ∀ patterns : List Pattern,
    (∀ pattern ∈ patterns, ModelNormalAt state table declaration laws pattern) →
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:model-normal-list" [tableValue table, encoded (.string declaration.quoteConstructor),
        encoded (.string declaration.dropConstructor), lawsValue laws, patternsValue patterns]) state
      (patternsValue (patterns.map (Wrappers.modelNormal laws declaration)))
  | [], _ => by canonical_eval unfolding [lawsValue, patternsValue, encodePatterns]
  | pattern :: rest, each => by
    have here := each pattern (by simp)
    have later := model_normal_list_of state table declaration laws rest
      (fun other member => each other (by simp [member]))
    canonical_eval [here, later] unfolding [lawsValue, patternsValue, patternValue, encodePatterns, List.map_cons]

/-- **`gslt:canon:model-normal` is `Wrappers.modelNormal`** on covered patterns, when the table holds the
declared units. -/
@[metta_head "gslt:canon:model-normal"]
theorem model_normal_returns (state : State) {table : List String} (ordered : NameOrdered table)
    (declaration : ReflectivePresentationDecl) (laws : List Laws)
    (units : ∀ law ∈ laws, ∀ label, law.unit = some label → label ∈ table) (pattern : Pattern)
    (covered : Covered table pattern) : ModelNormalAt state table declaration laws pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    have shape : Wrappers.modelNormal laws declaration (.bvar index) = .bvar index := by rw [Wrappers.modelNormal]
    unfold ModelNormalAt
    rw [shape]
    canonical_eval unfolding [lawsValue, patternValue, encodePattern]
  | hfvar name =>
    have shape : Wrappers.modelNormal laws declaration (.fvar name) = .fvar name := by rw [Wrappers.modelNormal]
    unfold ModelNormalAt
    rw [shape]
    canonical_eval unfolding [lawsValue, patternValue, encodePattern]
  | happly label arguments ih =>
    have inner := model_normal_list_of state table declaration laws arguments
      (fun argument member => ih argument member ((covered_apply covered).2 argument member))
    have finished := canonical_finish_returns state declaration label
      (arguments.map (Wrappers.modelNormal laws declaration))
    have shape : Wrappers.modelNormal laws declaration (.apply label arguments) =
        finishNormalizeReflectiveApply declaration label (arguments.map (Wrappers.modelNormal laws declaration)) := by
      rw [Wrappers.modelNormal]
    unfold ModelNormalAt
    rw [shape]
    canonical_eval [inner, finished] unfolding [lawsValue, patternValue, patternsValue, encodePattern]
  | hlambda binder body ih =>
    have inner := ih (covered_lambda covered).2
    have shape : Wrappers.modelNormal laws declaration (.lambda binder body) =
        .lambda binder (Wrappers.modelNormal laws declaration body) := by rw [Wrappers.modelNormal]
    unfold ModelNormalAt
    rw [shape]
    canonical_eval [inner] unfolding [lawsValue, patternValue, encodePattern]
  | hmultiLambda arity binders body ih =>
    have inner := ih (covered_multiLambda covered).2
    have shape : Wrappers.modelNormal laws declaration (.multiLambda arity binders body) =
        .multiLambda arity binders (Wrappers.modelNormal laws declaration body) := by rw [Wrappers.modelNormal]
    unfold ModelNormalAt
    rw [shape]
    canonical_eval [inner] unfolding [lawsValue, patternValue, encodePattern]
  | hsubst body replacement bodyIH replacementIH =>
    have first := bodyIH (covered_subst covered).1
    have second := replacementIH (covered_subst covered).2
    have shape : Wrappers.modelNormal laws declaration (.subst body replacement) =
        .subst (Wrappers.modelNormal laws declaration body) (Wrappers.modelNormal laws declaration replacement) := by
      rw [Wrappers.modelNormal]
    unfold ModelNormalAt
    rw [shape]
    canonical_eval [first, second] unfolding [lawsValue, patternValue, encodePattern]
  | hcollection kind elements rest ih =>
    obtain ⟨elementsIn, _⟩ := covered_collection covered
    have inner := model_normal_list_of state table declaration laws elements
      (fun element member => ih element member (elementsIn element member))
    have found := canonical_law_for_returns state kind laws
    cases law : lawFor laws kind with
    | none =>
      have shape : Wrappers.modelNormal laws declaration (.collection kind elements rest) =
          .collection kind (elements.map (Wrappers.modelNormal laws declaration)) rest := by
        rw [Wrappers.modelNormal, law]
      rw [law] at found
      unfold ModelNormalAt
      rw [shape]
      canonical_eval [inner, found] unfolding [lawsValue, patternValue, patternsValue, encodePattern]
    | some found' =>
      have shape : Wrappers.modelNormal laws declaration (.collection kind elements rest) =
          Wrappers.wrapFinish found' kind
            (Wrappers.setForm kind
              ((elements.map (Wrappers.modelNormal laws declaration)).flatMap (Wrappers.deepSplice found'))) rest := by
        rw [Wrappers.modelNormal, law]
      rw [law] at found
      have spliced := deep_splice_all_of state found' (elements.map (Wrappers.modelNormal laws declaration))
        (fun item _ => deep_splice_returns state found' item)
      have splicedCovered : ∀ item ∈ (elements.map (Wrappers.modelNormal laws declaration)).flatMap
          (Wrappers.deepSplice found'), Covered table item := by
        intro item member name named
        obtain ⟨original, originalIn, inside⟩ := List.mem_flatMap.mp member
        obtain ⟨element, elementIn, rfl⟩ := List.mem_map.mp originalIn
        exact covered_modelNormal declaration units (elementsIn element elementIn) name
          (names_deepSplice found' _ item inside name named)
      have formed := set_form_returns state ordered kind _ splicedCovered
      have finished := wrap_finish_returns state found' kind
        (Wrappers.setForm kind
          ((elements.map (Wrappers.modelNormal laws declaration)).flatMap (Wrappers.deepSplice found'))) rest
      unfold ModelNormalAt
      rw [shape]
      canonical_eval [inner, found, spliced, formed, finished]
        unfolding [lawsValue, patternValue, patternsValue, encodePattern]

#print axioms scopedFinishProof_checked
#print axioms scopedFinishProof_agreement

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
