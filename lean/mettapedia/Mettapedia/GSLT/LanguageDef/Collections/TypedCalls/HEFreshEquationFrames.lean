import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEContextualArithmeticSource

/-!
# Earned equation frames and ground-call RHS readback

Complete source frontiers and contextual unification already have independent
owners. This module composes them into actual retained Frames and derives RHS
materialization from the selected pattern equation. It does not take a desired
RHS value, completed evaluation, or output-frame certificate as a premise.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshEquationFrames

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps
open Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Type.Presentation.BindingTheory

/-- Every selected physical row receives its frame from the actual
unification trace and its derived readout certificate. -/
theorem frames_of_frontier (space : Space) (policy : Policy) (live : List Atom)
    (query : Entry.Value) (before : Frame) (works : List EquationWork)
    (frontier : EquationFrontierRel space live query.erase before.bindings works) :
    ∃ frames, List.Forall₂ (fun work (after : Frame) =>
      after.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment query (Entry.Value.ofAtom work.pattern)
        after.environment) works frames := by
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) before.certified frontier
  clear frontier
  induction paired with
  | nil => exact ⟨[], .nil⟩
  | @cons work environment works environments here paired ih =>
      obtain ⟨frames, rest⟩ := ih
      exact ⟨⟨work.bindings, environment, here.2⟩ :: frames, .cons ⟨rfl, here.1⟩ rest⟩

/-- The complete frontier itself is constructed from the finite source
space. The incoming record may contain aliases and unrelated bindings. -/
theorem source_frontier_frames (space : Space) (policy : Policy) (live : List Atom)
    (query : Entry.Value) (before : Frame) :
    ∃ works frames,
      EquationFrontierRel space live query.erase before.bindings works ∧
      List.Forall₂ (fun work (after : Frame) =>
        after.bindings = work.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding before.environment query (Entry.Value.ofAtom work.pattern)
          after.environment) works frames := by
  obtain ⟨works, frontier⟩ := EquationFreshening.equationFrontier_exists space live query.erase before.bindings
  obtain ⟨frames, paired⟩ := frames_of_frontier space policy live query before works frontier
  exact ⟨works, frames, frontier, paired⟩

/-- Unification retains every incoming binding constraint in the reached
frame; it does not erase a caller record simply because the call is ground. -/
theorem incoming_constraints_preserved (policy : Policy) (before after : Frame)
    (left right : Entry.Value)
    (unified : Entry.Value.UnifyRel policy.rebuilding before.environment left right after.environment)
    (valuation : String → Atom)
    (satisfied : TypeBindingSatisfied valuation after.bindings) :
    TypeBindingSatisfied valuation before.bindings := by
  have output := after.certified.theory valuation |>.mpr satisfied
  exact (before.certified.theory valuation).mp
    ((unified.solutions before.certified.normal valuation).mp output).1

/-- The reached normal presentation is itself a model of the selected
equation. Consequently both sides have exactly the same actual readback. -/
theorem unified_readbacks (policy : Policy) (before after : Frame)
    (left right : Entry.Value)
    (unified : Entry.Value.UnifyRel policy.rebuilding before.environment left right after.environment) :
    (after.read policy left).erase = (after.read policy right).erase := by
  let presented := Theory.presentedValuation (Entry.Value.eraseEnvironment after.environment)
  have model := Theory.normal_presentedValuation_satisfied after.certified.normal
  have same := ((unified.solutions before.certified.normal presented).mp model).2
  simp only [presented, Theory.applyTypeValuation_presented_eq_apply] at same
  simpa only [Frame.read, Entry.Value.erase_substitute_environment] using same

theorem ground_pattern_readback (policy : Policy) (before after : Frame)
    (query : Entry.Value) (pattern : Atom)
    (ground : TypeSubst.typeVars query.erase = [])
    (unified : Entry.Value.UnifyRel policy.rebuilding before.environment query (Entry.Value.ofAtom pattern)
      after.environment) :
    (after.read policy (Entry.Value.ofAtom pattern)).erase = query.erase := by
  have same := unified_readbacks policy before after query (Entry.Value.ofAtom pattern) unified
  have fixed : (after.read policy query).erase = query.erase := by
    rw [Frame.read, Entry.Value.erase_substitute_environment,
      ← Theory.applyTypeValuation_presented_eq_apply]
    exact applyTypeValuation_of_typeVars_eq_nil _ _ ground
  exact same.symm.trans fixed

/-- The selected pattern determines every RHS variable. A proposed
parameter assignment is checked on that pattern, and actual RHS readback
then follows from unification—not from an assumed body result. -/
theorem rhs_readback (policy : Policy) (before after : Frame)
    (query : Entry.Value) (pattern body : Atom) (parameters : String → Atom)
    (ground : TypeSubst.typeVars query.erase = [])
    (covered : ∀ name ∈ TypeSubst.typeVars body, name ∈ TypeSubst.typeVars pattern)
    (instantiated : applyTypeValuation parameters pattern = query.erase)
    (unified : Entry.Value.UnifyRel policy.rebuilding before.environment query (Entry.Value.ofAtom pattern)
      after.environment) :
    (after.read policy (Entry.Value.ofAtom body)).erase = applyTypeValuation parameters body := by
  let presented := Theory.presentedValuation (Entry.Value.eraseEnvironment after.environment)
  have selected := ground_pattern_readback policy before after query pattern ground unified
  simp only [Frame.read, Entry.Value.erase_substitute_environment, Entry.Value.erase_ofAtom] at selected
  have equation : applyTypeValuation presented pattern = applyTypeValuation parameters pattern := by
    dsimp only [presented]
    rw [Theory.applyTypeValuation_presented_eq_apply, selected, instantiated]
  have determined := applyTypeValuation_template_eq_of_pattern_eq presented parameters pattern body covered equation
  simpa only [Frame.read, Entry.Value.erase_substitute_environment, Entry.Value.erase_ofAtom,
    presented, Theory.applyTypeValuation_presented_eq_apply] using determined

namespace Range

open Spec.Bindings.ScopeObservation Spec.Bindings.ScopeObservation.ModelTransport
open Spec.Match.SolutionTheory

def number (value : Int) : Atom := .grounded (.int value)
def call (lower upper : Int) : Atom := .expression [.symbol "range", number lower, number upper]
def pattern : Atom := .expression [.symbol "range", .var "a", .var "b"]

/-- The authored ndcol range equation's body, with its parameters exposed.
The recursive call is retained as source syntax, not evaluated by this map. -/
def bodyAt (lower upper : Atom) : Atom :=
  .expression [.symbol "if", .expression [.symbol ">=", lower, upper], .expression [.symbol "empty"],
    .expression [.symbol "superpose", .expression [lower,
      .expression [.symbol "range", .expression [.symbol "+", lower, number 1], upper]]]]

def body : Atom := bodyAt (.var "a") (.var "b")

theorem ground_call (lower upper : Int) : TypeSubst.typeVars (call lower upper) = [] := by
  simp [call, number, TypeSubst.typeVars, TypeSubst.typeVarsList]

theorem body_variables_bound :
    ∀ name ∈ TypeSubst.typeVars body, name ∈ TypeSubst.typeVars pattern := by
  simp [body, bodyAt, pattern, number, TypeSubst.typeVars, TypeSubst.typeVarsList]

theorem active_rebuild (rebuilding : Entry.RebuildPolicy) (before after : Atom) :
    Entry.Value.rebuildStatus rebuilding .active before after = .active := by
  cases rebuilding <;> simp [Entry.Value.rebuildStatus]

theorem erase_grounded {value : Entry.Value} {grounded : Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue}
    (same : value.erase = .grounded grounded) : value = .grounded grounded := by
  cases value <;> simp_all [Entry.Value.erase]

/-- The reached source unifier fixes both range parameters to their actual
integer operands. This also fixes the complete annotated recursive body,
not just its erased syntax or its eventual answer set. -/
theorem read_range_body (policy : Policy) (before after : Frame) (lower upper : Int)
    (rename : String → String)
    (unified : Entry.Value.UnifyRel policy.rebuilding before.environment (Entry.Value.ofAtom (call lower upper))
      (Entry.Value.ofAtom (renameTypeVars rename pattern)) after.environment) :
    after.read policy (Entry.Value.ofAtom (renameTypeVars rename body)) =
      Entry.Value.ofAtom (bodyAt (number lower) (number upper)) := by
  have grounded : TypeSubst.typeVars (Entry.Value.ofAtom (call lower upper)).erase = [] := by
    simpa only [Entry.Value.erase_ofAtom] using ground_call lower upper
  have matched := ground_pattern_readback policy before after (Entry.Value.ofAtom (call lower upper))
    (renameTypeVars rename pattern) grounded unified
  have values :
      (Entry.Value.resolve after.environment (rename "a")).erase = number lower ∧
      (Entry.Value.resolve after.environment (rename "b")).erase = number upper := by
    simpa [Frame.read, pattern, call, renameTypeVars, Entry.Value.ofAtom,
      Entry.Value.substitute, Entry.Value.erase] using matched
  have lowerRead := erase_grounded values.1
  have upperRead := erase_grounded values.2
  simp [Frame.read, body, bodyAt, number, renameTypeVars, Entry.Value.ofAtom,
    Entry.Value.substitute, active_rebuild, lowerRead, upperRead]

/-- Specialization to a real selected physical row. Its fresh pattern and
body share the alpha witness owned by that occurrence. -/
theorem selected_body_readback (space : Space) (policy : Policy) (live : List Atom)
    (before after : Frame) (lower upper : Int) (works : List EquationWork) (work : EquationWork)
    (frontier : EquationFrontierRel space live (call lower upper) before.bindings works)
    (member : work ∈ works) (left : work.left = pattern) (right : work.right = body)
    (unified : Entry.Value.UnifyRel policy.rebuilding before.environment (Entry.Value.ofAtom (call lower upper))
      (Entry.Value.ofAtom work.pattern) after.environment) :
    after.read policy (Entry.Value.ofAtom work.body) = Entry.Value.ofAtom (bodyAt (number lower) (number upper)) := by
  obtain ⟨_, occurrence⟩ := frontier.occurrence member
  obtain ⟨rename, _, patternRenamed, bodyRenamed, _⟩ := occurrence.selected.1
  have patternEq := EquationFreshening.alphaRename_eq patternRenamed
  have bodyEq := EquationFreshening.alphaRename_eq bodyRenamed
  rw [left] at patternEq
  rw [right] at bodyEq
  rw [patternEq] at unified
  rw [bodyEq]
  exact read_range_body policy before after lower upper rename unified

/-- The stored range rule has a viable fresh instance under every certified
caller frame. A common model is constructed by changing only its two fresh
parameter coordinates. Body termination or nonemptiness is not assumed. -/
theorem fresh_occurrence (space : Space) (live : List Atom) (before : Frame)
    (lower upper : Int) (position : Nat)
    (stored : space.atoms[position]? = some (.expression [.symbol "=", pattern, body])) :
    ∃ freshPattern freshBody matched output,
      EquationQueryOccurrenceRel space live (call lower upper) before.bindings position pattern body
        freshPattern freshBody matched freshBody output := by
  let chosen := EquationFreshening.freshRule
    (EquationScope.visibleNames live (call lower upper) before.bindings) position pattern body
  have alpha := EquationFreshening.freshRule_alphaVariant live (call lower upper) pattern body before.bindings position
  change AlphaVariantRel live (call lower upper) before.bindings pattern body chosen.1 chosen.2 at alpha
  obtain ⟨rename, injective, renamedPattern, renamedBody, fresh⟩ := alpha
  have namesApart : rename "b" ≠ rename "a" := by
    intro same
    exact (by decide : ("b" : String) ≠ "a") (injective same)
  have absent (name : String) (parameter : name = "a" ∨ name = "b") :
      rename name ∉ specBindingVars before.bindings := by
    intro present
    have occurs : Spec.Match.Merge.AtomOccurs pattern name := by
      rcases parameter with rfl | rfl
      · exact .expression (by simp) (.var "a")
      · exact .expression (by simp) (.var "b")
    exact fresh name (Or.inl occurs)
      ((EquationScope.mem_visibleNames_iff live (call lower upper) before.bindings (rename name)).mp
        ((EquationScope.visible_closed_iff (ground_call lower upper) (rename name)).mpr (Or.inr present)))
  obtain ⟨oldModel, oldSatisfied⟩ := before.certified.satisfiable
  let newModel : String → Atom := fun name =>
    if name = rename "a" then number lower else if name = rename "b" then number upper else oldModel name
  have preserved : TypeBindingSatisfied newModel before.bindings := by
    apply (specTypeBindingSatisfied_congr_of_bindingVars (left := oldModel) (right := newModel) ?_).mp oldSatisfied
    intro name present
    have notA : name ≠ rename "a" := by intro same; subst name; exact absent "a" (Or.inl rfl) present
    have notB : name ≠ rename "b" := by intro same; subst name; exact absent "b" (Or.inr rfl) present
    simp [newModel, notA, notB]
  have equation : applyTypeValuation newModel (call lower upper) = applyTypeValuation newModel chosen.1 := by
    rw [EquationFreshening.alphaRename_eq renamedPattern]
    simp [call, pattern, number, renameTypeVars, applyTypeValuation, newModel, namesApart]
  have modelEquation : HEAtomEquationSatisfied (fun name => encodeModelAtom (newModel name))
      (call lower upper) chosen.1 := by
    unfold HEAtomEquationSatisfied
    rw [← encodeModelAtom_applyTypeValuation, ← encodeModelAtom_applyTypeValuation]
    exact congrArg encodeModelAtom equation
  obtain ⟨matched, matching, matchedModel⟩ := Spec.Match.Completeness.exists_specMatch_of_solution modelEquation
  have merged := LogicalMergeRel.append_of_common_model
    ⟨newModel, (specTypeBindingSatisfied_iff_heBindingSatisfied_translated newModel matched).mpr matchedModel, preserved⟩
  exact ⟨chosen.1, chosen.2, matched, _, stored,
    ⟨⟨rename, injective, renamedPattern, renamedBody, fresh⟩, matching⟩, merged, fun _ _ => rfl⟩

theorem query_frontier_nonempty (space : Space) (live : List Atom) (before : Frame)
    (lower upper : Int) (position : Nat) (works : List EquationWork)
    (stored : space.atoms[position]? = some (.expression [.symbol "=", pattern, body]))
    (frontier : EquationFrontierRel space live (call lower upper) before.bindings works) :
    works ≠ [] := by
  obtain ⟨_, _, _, _, occurrence⟩ := fresh_occurrence space live before lower upper position stored
  obtain ⟨work, present, _⟩ := frontier.covers occurrence
  exact List.ne_nil_of_mem present

/-- A complete source query, a source-earned selected frame, and its exact
numeric recursive body are obtained together. The source row is identified
by physical position, so another equation cannot stand in for this one. -/
theorem selected_range_frame (space : Space) (policy : Policy) (live : List Atom)
    (before : Frame) (lower upper : Int) (position : Nat)
    (stored : space.atoms[position]? = some (.expression [.symbol "=", pattern, body])) :
    ∃ works frames work after,
      EquationFrontierRel space live (call lower upper) before.bindings works ∧
      List.Forall₂ (fun item (frame : Frame) => frame.bindings = item.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding before.environment (Entry.Value.ofAtom (call lower upper))
          (Entry.Value.ofAtom item.pattern) frame.environment) works frames ∧
      work ∈ works ∧ after ∈ frames ∧ after.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment (Entry.Value.ofAtom (call lower upper))
        (Entry.Value.ofAtom work.pattern) after.environment ∧ work.position = position ∧
      after.read policy (Entry.Value.ofAtom work.body) = Entry.Value.ofAtom (bodyAt (number lower) (number upper)) := by
  obtain ⟨works, frames, frontier, paired⟩ :=
    source_frontier_frames space policy live (Entry.Value.ofAtom (call lower upper)) before
  simp only [Entry.Value.erase_ofAtom] at frontier
  obtain ⟨_, _, _, _, occurrence⟩ := fresh_occurrence space live before lower upper position stored
  obtain ⟨work, present, samePosition⟩ := frontier.covers occurrence
  obtain ⟨_, selected⟩ := frontier.occurrence present
  have selectedAt : space.atoms[position]? = some (.expression [.symbol "=", work.left, work.right]) := by
    simpa only [samePosition] using selected.stored
  have sameRaw : work.left = pattern ∧ work.right = body := by
    have same := Option.some.inj (selectedAt.symm.trans stored)
    simpa using same
  have matchedFrame : ∃ after ∈ frames, after.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment (Entry.Value.ofAtom (call lower upper))
        (Entry.Value.ofAtom work.pattern) after.environment := by
    clear frontier selected selectedAt occurrence stored samePosition sameRaw
    induction paired with
    | nil => cases present
    | @cons item frame items frames here paired ih =>
        rcases List.mem_cons.mp present with rfl | later
        · exact ⟨frame, by simp, here⟩
        · obtain ⟨after, member, related⟩ := ih later
          exact ⟨after, List.mem_cons_of_mem _ member, related⟩
  obtain ⟨after, frameMember, bound, unified⟩ := matchedFrame
  exact ⟨works, frames, work, after, frontier, paired, present, frameMember, bound, unified, samePosition,
    selected_body_readback space policy live before after lower upper works work frontier present sameRaw.1 sameRaw.2 unified⟩

namespace Controls

def sourceSpace : Space := Space.ofList [.expression [.symbol "=", pattern, body]]

/-- The real authored rule matches under a nonempty aliased caller; the
selected RHS remains a program containing comparison, addition and recursion. -/
theorem aliased_caller_range_frame (policy : Policy) (lower upper : Int) :
    ∃ (works : List EquationWork) (frames : List Frame) (work : EquationWork) (after : Frame),
      EquationFrontierRel sourceSpace [.var "x", .var "y"] (call lower upper)
        Completed.Controls.argumentAliasFrame.bindings works ∧
      work ∈ works ∧ after ∈ frames ∧ after.bindings = work.bindings ∧
      after.read policy (Entry.Value.ofAtom work.body) =
        Entry.Value.ofAtom (bodyAt (number lower) (number upper)) ∧
      (∀ valuation, TypeBindingSatisfied valuation after.bindings →
        TypeBindingSatisfied valuation Completed.Controls.argumentAliasFrame.bindings) := by
  obtain ⟨works, frames, work, after, frontier, _, present, included, bound, unified, _, read⟩ :=
    selected_range_frame sourceSpace policy [.var "x", .var "y"] Completed.Controls.argumentAliasFrame
      lower upper 0 rfl
  exact ⟨works, frames, work, after, frontier, present, included, bound, read,
    fun valuation satisfied => incoming_constraints_preserved policy _ _ _ _ unified valuation satisfied⟩

theorem hidden_rhs_variable_not_determined :
    ¬(∀ name ∈ TypeSubst.typeVars (.var "hidden"), name ∈ TypeSubst.typeVars pattern) := by
  simp [pattern, TypeSubst.typeVars, TypeSubst.typeVarsList]

/-- Identifying the two fresh parameter coordinates rejects valid unequal
endpoints; freshness is not a cosmetic renaming choice. -/
theorem colliding_parameters_refused (policy : Policy) (before after : Frame)
    (lower upper : Int) (different : lower ≠ upper) (name : String) :
    ¬Entry.Value.UnifyRel policy.rebuilding before.environment (Entry.Value.ofAtom (call lower upper))
      (Entry.Value.ofAtom (.expression [.symbol "range", .var name, .var name])) after.environment := by
  intro unified
  have ground : TypeSubst.typeVars (Entry.Value.ofAtom (call lower upper)).erase = [] := by
    simpa only [Entry.Value.erase_ofAtom] using ground_call lower upper
  have matched := ground_pattern_readback policy before after (Entry.Value.ofAtom (call lower upper))
    (.expression [.symbol "range", .var name, .var name]) ground unified
  have values : (Entry.Value.resolve after.environment name).erase = number lower ∧
      (Entry.Value.resolve after.environment name).erase = number upper := by
    simpa [Frame.read, call, Entry.Value.ofAtom, Entry.Value.substitute, Entry.Value.erase] using matched
  exact different (by simpa [number] using values.1.symm.trans values.2)

end Controls

end Range

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshEquationFrames
