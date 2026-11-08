import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshSyntaxBinding

/-!
# Exact branch values from selected conditional source equations

A physical source occurrence supplies its fresh simultaneous pattern/body
renaming and raw constraint record. An explicit contextual unification trace
binds the complete branch values, then certifies that actual source record.
Thus the emitted RHS retains its evaluation marks rather than being rebuilt
from the erased expression.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConditionalEquationFrames

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps
open Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory Spec.Bindings.ScopeObservation
open Spec.Match.SolutionTheory Spec.Bindings.ScopeObservation.ModelTransport

def query (condition : Bool) (yes no : Entry.Value) : Entry.Value :=
  .expression .active [.symbol "if", .grounded (.bool condition), yes, no]

def pattern (condition : Bool) : Atom :=
  .expression [.symbol "if", .grounded (.bool condition), .var "then", .var "else"]

def body (condition : Bool) : Atom := if condition then .var "then" else .var "else"

theorem query_ground (condition : Bool) (yes no : Entry.Value)
    (yesClosed : TypeSubst.typeVars yes.erase = []) (noClosed : TypeSubst.typeVars no.erase = []) :
    TypeSubst.typeVars (query condition yes no).erase = [] := by
  simp [query, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList, yesClosed, noClosed]

/-- The selected record is the physical source work item's record; only
its contextual readout is earned from the actual branch-binding trace. -/
theorem selected_frame (space : Space) (policy : Policy) (live : List Atom)
    (before : Frame) (condition : Bool) (yes no : Entry.Value)
    (yesClosed : TypeSubst.typeVars yes.erase = []) (noClosed : TypeSubst.typeVars no.erase = [])
    (works : List EquationWork) (work : EquationWork)
    (frontier : EquationFrontierRel space live (query condition yes no).erase before.bindings works)
    (member : work ∈ works) (left : work.left = pattern condition) (right : work.right = body condition) :
    ∃ after : Frame,
      after.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment (query condition yes no)
        (Entry.Value.ofAtom work.pattern) after.environment ∧
      after.read policy (Entry.Value.ofAtom work.body) = if condition then yes else no := by
  obtain ⟨matched, occurrence⟩ := frontier.occurrence member
  obtain ⟨rename, injective, renamedPattern, renamedBody, fresh⟩ := occurrence.selected.1
  have patternEq := EquationFreshening.alphaRename_eq renamedPattern
  have bodyEq := EquationFreshening.alphaRename_eq renamedBody
  rw [left] at patternEq
  rw [right] at bodyEq
  have ground := query_ground condition yes no yesClosed noClosed
  have absent (name : String) (parameter : name = "then" ∨ name = "else") :
      rename name ∉ specBindingVars before.bindings := by
    intro present
    have occurs : Spec.Match.Merge.AtomOccurs work.left name := by
      rw [left]
      rcases parameter with rfl | rfl
      · exact .expression (by simp) (.var "then")
      · exact .expression (by simp) (.var "else")
    exact fresh name (Or.inl occurs)
      ((EquationScope.mem_visibleNames_iff live (query condition yes no).erase before.bindings (rename name)).mp
        ((EquationScope.visible_closed_iff ground (rename name)).mpr (Or.inr present)))
  have different : rename "else" ≠ rename "then" := by
    intro equal
    exact (by decide : ("else" : String) ≠ "then") (injective equal)
  obtain ⟨captured, unified, read, _⟩ := HEFreshSyntaxBinding.conditional_parameters policy before
    (rename "then") (rename "else") yes no condition (absent "then" (Or.inl rfl))
    (absent "else" (Or.inr rfl)) different yesClosed noClosed
  have sourceUnified : Entry.Value.UnifyRel policy.rebuilding before.environment (query condition yes no)
      (Entry.Value.ofAtom work.pattern) captured.environment := by
    simpa only [patternEq, pattern, renameTypeVars, List.map_cons, List.map_nil, query] using unified
  have candidate : UnifyCandidateRel (query condition yes no).erase
      (Entry.Value.ofAtom work.pattern).erase before.bindings work.bindings := by
    simpa only [Entry.Value.erase_ofAtom] using
      (show UnifyCandidateRel (query condition yes no).erase work.pattern before.bindings work.bindings from
        ⟨matched, occurrence.selected.2, occurrence.result.1⟩)
  let after : Frame := ⟨work.bindings, captured.environment, sourceUnified.certifies before.certified candidate⟩
  refine ⟨after, rfl, sourceUnified, ?_⟩
  change captured.read policy (Entry.Value.ofAtom work.body) = _
  rw [bodyEq]
  cases condition with
  | false => simpa [body, renameTypeVars, Entry.Value.ofAtom] using (read policy).2
  | true => simpa [body, renameTypeVars, Entry.Value.ofAtom] using (read policy).1

/-- The matching standard-if equation has an actual fresh source occurrence
under any caller frame. Its common model is obtained from the constructed
contextual unification trace, rather than an assumed successful source run. -/
theorem fresh_occurrence (space : Space) (policy : Policy) (live : List Atom)
    (before : Frame) (condition : Bool) (yes no : Entry.Value)
    (yesClosed : TypeSubst.typeVars yes.erase = []) (noClosed : TypeSubst.typeVars no.erase = [])
    (position : Nat)
    (stored : space.atoms[position]? = some (.expression [.symbol "=", pattern condition, body condition])) :
    ∃ freshPattern freshBody matched output,
      EquationQueryOccurrenceRel space live (query condition yes no).erase before.bindings position
        (pattern condition) (body condition) freshPattern freshBody matched freshBody output := by
  let chosen := EquationFreshening.freshRule
    (EquationScope.visibleNames live (query condition yes no).erase before.bindings)
    position (pattern condition) (body condition)
  have alpha := EquationFreshening.freshRule_alphaVariant live (query condition yes no).erase
    (pattern condition) (body condition) before.bindings position
  change AlphaVariantRel live (query condition yes no).erase before.bindings
    (pattern condition) (body condition) chosen.1 chosen.2 at alpha
  obtain ⟨rename, injective, renamedPattern, renamedBody, fresh⟩ := alpha
  have ground := query_ground condition yes no yesClosed noClosed
  have absent (name : String) (parameter : name = "then" ∨ name = "else") :
      rename name ∉ specBindingVars before.bindings := by
    intro present
    have occurs : Spec.Match.Merge.AtomOccurs (pattern condition) name := by
      rcases parameter with rfl | rfl
      · exact .expression (by simp) (.var "then")
      · exact .expression (by simp) (.var "else")
    exact fresh name (Or.inl occurs)
      ((EquationScope.mem_visibleNames_iff live (query condition yes no).erase before.bindings (rename name)).mp
        ((EquationScope.visible_closed_iff ground (rename name)).mpr (Or.inr present)))
  have different : rename "else" ≠ rename "then" := by
    intro equal
    exact (by decide : ("else" : String) ≠ "then") (injective equal)
  obtain ⟨captured, unified, _, _⟩ := HEFreshSyntaxBinding.conditional_parameters policy before
    (rename "then") (rename "else") yes no condition (absent "then" (Or.inl rfl))
    (absent "else" (Or.inr rfl)) different yesClosed noClosed
  have sourceUnified : Entry.Value.UnifyRel policy.rebuilding before.environment (query condition yes no)
      (Entry.Value.ofAtom chosen.1) captured.environment := by
    simpa only [EquationFreshening.alphaRename_eq renamedPattern, pattern, renameTypeVars,
      List.map_cons, List.map_nil, query] using unified
  let valuation := Theory.presentedValuation (Entry.Value.eraseEnvironment captured.environment)
  have model := Theory.normal_presentedValuation_satisfied captured.certified.normal
  have reached := (sourceUnified.solutions before.certified.normal valuation).mp model
  have incoming : TypeBindingSatisfied valuation before.bindings := (before.certified.theory valuation).mp reached.1
  have equation : applyTypeValuation valuation (query condition yes no).erase = applyTypeValuation valuation chosen.1 := by
    simpa only [Entry.Value.erase_ofAtom] using reached.2
  have modelEquation : HEAtomEquationSatisfied
      (fun name => encodeModelAtom (valuation name))
      (query condition yes no).erase chosen.1 := by
    unfold HEAtomEquationSatisfied
    rw [← encodeModelAtom_applyTypeValuation, ← encodeModelAtom_applyTypeValuation]
    exact congrArg encodeModelAtom equation
  obtain ⟨matched, matching, matchedModel⟩ := Spec.Match.Completeness.exists_specMatch_of_solution modelEquation
  have merged := LogicalMergeRel.append_of_common_model
    ⟨valuation, (specTypeBindingSatisfied_iff_heBindingSatisfied_translated valuation matched).mpr matchedModel, incoming⟩
  exact ⟨chosen.1, chosen.2, matched, _, stored,
    ⟨⟨rename, injective, renamedPattern, renamedBody, fresh⟩, matching⟩, merged, fun _ _ => rfl⟩

/-- A complete source query and an exact annotated selected branch are
earned together from the stored physical conditional equation. -/
theorem source_frame (space : Space) (policy : Policy) (live : List Atom)
    (before : Frame) (condition : Bool) (yes no : Entry.Value)
    (yesClosed : TypeSubst.typeVars yes.erase = []) (noClosed : TypeSubst.typeVars no.erase = [])
    (position : Nat)
    (stored : space.atoms[position]? = some (.expression [.symbol "=", pattern condition, body condition])) :
    ∃ (works : List EquationWork) (work : EquationWork) (after : Frame),
      EquationFrontierRel space live (query condition yes no).erase before.bindings works ∧
      work ∈ works ∧ work.position = position ∧ after.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment (query condition yes no)
        (Entry.Value.ofAtom work.pattern) after.environment ∧
      after.read policy (Entry.Value.ofAtom work.body) = if condition then yes else no := by
  obtain ⟨works, frontier⟩ := EquationFreshening.equationFrontier_exists space live
    (query condition yes no).erase before.bindings
  obtain ⟨_, _, _, _, occurrence⟩ := fresh_occurrence space policy live before condition yes no yesClosed noClosed position stored
  obtain ⟨work, present, samePosition⟩ := frontier.covers occurrence
  obtain ⟨_, selected⟩ := frontier.occurrence present
  have selectedAt : space.atoms[position]? = some (.expression [.symbol "=", work.left, work.right]) := by
    simpa only [samePosition] using selected.stored
  have sameRaw : work.left = pattern condition ∧ work.right = body condition := by
    have same := Option.some.inj (selectedAt.symm.trans stored)
    simpa using same
  obtain ⟨after, bound, unified, read⟩ :=
    selected_frame space policy live before condition yes no yesClosed noClosed works work frontier present sameRaw.1 sameRaw.2
  exact ⟨works, work, after, frontier, present, samePosition, bound, unified, read⟩

/-- The wrong Boolean clause cannot be used to justify a chosen branch. -/
theorem opposite_clause_refused (policy : Policy) (before after : Frame) (condition : Bool)
    (yes no : Entry.Value) (left right : String) :
    ¬Entry.Value.UnifyRel policy.rebuilding before.environment (query condition yes no)
      (Entry.Value.ofAtom (.expression [.symbol "if", .grounded (.bool (!condition)), .var left, .var right]))
      after.environment := by
  intro unified
  have equal := HEFreshEquationFrames.unified_readbacks policy before after _ _ unified
  have test := congrArg (fun atom : Atom => match atom with
    | .expression (_ :: .grounded (.bool value) :: _) => some value
    | _ => none) equal
  cases condition <;> simp [query, Frame.read, Entry.Value.ofAtom, Entry.Value.substitute, Entry.Value.erase] at test

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConditionalEquationFrames
