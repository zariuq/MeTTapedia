import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.GroundUninterpretedVersions
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.GroundProtectedRegions
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingRefinement

/-!
# Caller dependencies carried by source call answers

The source machine is `PeTTa.Unifying`: every answer carries its branch's
finite substitution, and an enclosing `let` resumes under that substitution.
These laws expose the observation and dependency transport at that boundary.
They neither replace the machine with a value-only oracle nor assert native
contract-scanner adequacy. Type claims are relative to the stated declaration
space; preserving declaration currentness across effects is a separate check.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceCallAliasTransport

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi
open UnifyingRegions UnifyingFrames OpenFrameEffects

def readBindings (bindings : MORK.Subst) : Substitution :=
  fun name => Unifying.resolve bindings (.var name)

theorem resolve_eq_subst (bindings : MORK.Subst) : ∀ value : Atom,
    Unifying.resolve bindings value = substA (readBindings bindings) value := by
  intro value
  induction value using Atom.rec
      (motive_2 := fun values => MORK.applySubst.applySubstList bindings values = substL (readBindings bindings) values) with
  | var _ => rfl
  | symbol _ => rfl
  | grounded _ => rfl
  | expression values ih => exact congrArg Atom.expression ih
  | nil => rfl
  | cons first rest ihFirst ihRest =>
      change MORK.applySubst bindings first :: MORK.applySubst.applySubstList bindings rest =
        substA (readBindings bindings) first :: substL (readBindings bindings) rest
      exact congrArg₂ List.cons ihFirst ihRest

/-- A new alias is reflected in the current dependencies, even when the
callee's result has no typing claim and the source names are different. -/
theorem refined_support {before after : MORK.Subst} (refines : Unifying.Refines before after)
    (recipe : Atom) (name : String) :
    name ∈ support (Unifying.resolve after recipe) ↔
      ∃ old ∈ support (Unifying.resolve before recipe),
        name ∈ support (Unifying.resolve after (.var old)) := by
  rw [← refines recipe, resolve_eq_subst]
  exact support_subst (readBindings after) (Unifying.resolve before recipe) name

theorem refined_ground_observation {before after : MORK.Subst}
    (refines : Unifying.Refines before after) (recipe : Atom)
    (ground : support (Unifying.resolve before recipe) = ∅) :
    Unifying.resolve after recipe = Unifying.resolve before recipe := by
  rw [← refines recipe, resolve_eq_subst]
  exact CapturedUninterpretedRegions.subst_ground ground (readBindings after)

/-- A check on current dependencies, not on the names of source parameters.
This is a sufficient certificate, not a claim about the native analyser. -/
def dependencyCheck (before after : MORK.Subst) (recipe : Atom) : Bool :=
  decide (∀ name ∈ support (Unifying.resolve before recipe),
    Unifying.resolve after (.var name) = .var name)

theorem dependencyCheck_preserves {before after : MORK.Subst}
    (refines : Unifying.Refines before after) (recipe : Atom)
    (checked : dependencyCheck before after recipe = true) :
    Unifying.resolve after recipe = Unifying.resolve before recipe := by
  rw [← refines recipe, resolve_eq_subst]
  apply subst_fixes
  intro name present
  exact (of_decide_eq_true checked) name present

theorem dependencyCheck_transports_predicate {before after : MORK.Subst}
    (refines : Unifying.Refines before after) (recipe : Atom)
    (checked : dependencyCheck before after recipe = true)
    (predicate : Atom → Prop) (old : predicate (Unifying.resolve before recipe)) :
    predicate (Unifying.resolve after recipe) := by
  rw [dependencyCheck_preserves refines recipe checked]
  exact old

/-- Open uninterpreted values also survive when each of their current
dependencies is instantiated only by uninterpreted data. The condition is
on the returned branch substitution, not on the helper's result flag. -/
theorem refined_uninterpreted_observation {decls : Decls} {before after : MORK.Subst}
    (refines : Unifying.Refines before after) (recipe : Atom)
    (clean : Uninterp decls (Unifying.resolve before recipe))
    (dependencies : ∀ name ∈ support (Unifying.resolve before recipe),
      Uninterp decls (Unifying.resolve after (.var name))) :
    Uninterp decls (Unifying.resolve after recipe) := by
  rw [← refines recipe, resolve_eq_subst]
  exact GroundUninterpretedVersions.uninterp_substA_on clean dependencies

/-- The variable-pattern `let` used by the helper-alias reproducer uses
the real source unifier, and carries its refinement into the continuation. -/
theorem variable_binding_refines (bindings bound : MORK.Subst) (name : String) (value : Atom)
    (idempotent : Unifying.Idempotent bindings)
    (unified : Unifying.unifyBinding bindings (.var name) value = .ok bound) :
    Unifying.Idempotent bound ∧ Unifying.Refines bindings bound ∧
      Unifying.resolve bound (.var name) = Unifying.resolve bound value := by
  change Unifying.unifyTerms _ bindings (.var name) value = .ok bound at unified
  exact Unifying.unifyTerms_sound _ bindings bound (.var name) value idempotent unified

/-- A returned answer and the caller's binding refine the same caller
record; the callee's binding changes are not discarded at resumption. -/
theorem returned_variable_binding_refines {caller : MORK.Subst}
    (answer : Unifying.Answer) (bound : MORK.Subst) (name : String)
    (idempotent : Unifying.Idempotent answer.bindings)
    (returned : Unifying.Refines caller answer.bindings)
    (unified : Unifying.unifyBinding answer.bindings (.var name) answer.value = .ok bound) :
    Unifying.Idempotent bound ∧ Unifying.Refines caller bound := by
  obtain ⟨valid, refined, _⟩ := variable_binding_refines answer.bindings bound name answer.value idempotent unified
  exact ⟨valid, returned.trans refined⟩

theorem refined_facts {decls : Decls} {before after : MORK.Subst}
    (refines : Unifying.Refines before after) (facts : ContractBindingFacts.Facts)
    (sound : ContractBindingFacts.Sound decls (readBindings before) facts)
    (dependencies : ∀ entry ∈ facts, entry.2.uninterpreted = true → entry.2.ground ≠ true →
      ∀ name ∈ support (Unifying.resolve before (.var entry.1)),
        Uninterp decls (Unifying.resolve after (.var name))) :
    ContractBindingFacts.Sound decls (readBindings after) facts := by
  intro entry member
  have old := sound entry member
  refine ⟨fun ground => ?_, fun clean => ?_⟩
  · change support (Unifying.resolve after (.var entry.1)) = ∅
    rw [refined_ground_observation refines (.var entry.1) (old.1 ground)]
    exact old.1 ground
  · by_cases ground : entry.2.ground = true
    · change Uninterp decls (Unifying.resolve after (.var entry.1))
      rw [refined_ground_observation refines (.var entry.1) (old.1 ground)]
      exact old.2 clean
    · exact refined_uninterpreted_observation refines (.var entry.1) (old.2 clean)
        (dependencies entry member clean ground)

/-- The callee refinement here is earned from the actual whole source path,
including recursive returns and caller-visible substitutions. Only the
type-specific dependency obligation remains for an admission analyser. -/
theorem reached_facts_transport {registry : SpaceSemantics.Program} {initial : MORK.Subst}
    {source target : Unifying.Configuration} {decls : Decls}
    (steps : Relation.ReflTransGen (Unifying.Transition registry) source target)
    (good : Unifying.ConfigurationRefines initial source) (answers : List Unifying.Answer)
    (returned : target.control = .returned answers) (facts : ContractBindingFacts.Facts)
    (sound : ContractBindingFacts.Sound decls (readBindings initial) facts)
    (dependencies : ∀ answer ∈ answers, ∀ entry ∈ facts,
      entry.2.uninterpreted = true → entry.2.ground ≠ true →
      ∀ name ∈ support (Unifying.resolve initial (.var entry.1)),
        Uninterp decls (Unifying.resolve answer.bindings (.var name))) :
    ∀ answer ∈ answers, ContractBindingFacts.Sound decls (readBindings answer.bindings) facts := by
  intro answer present
  exact refined_facts (Unifying.reached_answers_refine steps good answers returned answer present).2
    facts sound (dependencies answer present)

theorem reached_ground_tail {registry : SpaceSemantics.Program} {initial bindings : MORK.Subst}
    {source target : Unifying.Configuration}
    (steps : Relation.ReflTransGen (Unifying.Transition registry) source target)
    (good : Unifying.ConfigurationRefines initial source) (name : String)
    (tail : target.control = .evaluate bindings (.var name))
    (ground : support (Unifying.resolve initial (.var name)) = ∅) :
    Unifying.step registry target = some { target with
      control := .returned [⟨Unifying.resolve initial (.var name), bindings⟩] } := by
  have final := (Unifying.steps_refine steps good).1
  have bound : Unifying.BindingRefines initial bindings := by
    simpa only [tail, Unifying.ControlRefines] using final
  have unchanged := refined_ground_observation bound.2 (.var name) ground
  simp [Unifying.step, tail, unchanged]

/-- A ground protected return reached after arbitrary real source calls
earns the polymorphic guard discharge at its delivered-value boundary. -/
theorem reached_ground_tail_guard {registry : SpaceSemantics.Program} {initial bindings : MORK.Subst}
    {source target : Unifying.Configuration} {decls : Decls}
    (steps : Relation.ReflTransGen (Unifying.Transition registry) source target)
    (good : Unifying.ConfigurationRefines initial source) (name : String)
    (tail : target.control = .evaluate bindings (.var name))
    (ground : support (Unifying.resolve initial (.var name)) = ∅)
    (clean : Uninterp decls (Unifying.resolve initial (.var name))) (kind : Atom → String) :
    chainCall decls kind (fun _ => {Unifying.resolve bindings (.var name)}) pairRow
      [Unifying.resolve initial (.var name)] = {Unifying.resolve initial (.var name)} := by
  have final := (Unifying.steps_refine steps good).1
  have bound : Unifying.BindingRefines initial bindings := by
    simpa only [tail, Unifying.ControlRefines] using final
  rw [refined_ground_observation bound.2 (.var name) ground]
  have exactGuard := UninterpretedLocalMultiplicity.pair_protocol_clean kind [] [] "a"
    (fun _ => {Unifying.resolve initial (.var name)}) [] [] (Unifying.resolve initial (.var name)) rfl clean (by
      intro result member
      simp only [Multiset.mem_singleton] at member
      subst result
      exact ⟨Atom.var, (substA_var_self _).symm, fun _ => trivial⟩)
  simpa [argCount, one_nsmul] using exactGuard

/-- Each branch keeps its own current substitution. The successful local
unifications determine the ordered continuation list, including repeats. -/
theorem bindAnswers_exact (pattern body : Atom) (answers : List Unifying.Answer)
    (bound : Unifying.Answer → MORK.Subst)
    (unifies : ∀ answer ∈ answers,
      Unifying.unifyBinding answer.bindings pattern answer.value = .ok (bound answer)) :
    Unifying.bindAnswers pattern body answers =
      some (answers.map fun answer => .evaluate (bound answer) body) := by
  induction answers with
  | nil => rfl
  | cons first rest ih =>
      simp only [Unifying.bindAnswers, List.map_cons]
      rw [ih (fun answer present => unifies answer (by simp [present])),
        unifies first (by simp)]
      rfl

theorem bindAnswers_append (pattern body : Atom) (first second : List Unifying.Answer)
    (left right : List Unifying.Control)
    (firstRun : Unifying.bindAnswers pattern body first = some left)
    (secondRun : Unifying.bindAnswers pattern body second = some right) :
    Unifying.bindAnswers pattern body (first ++ second) = some (left ++ right) := by
  induction first generalizing left with
  | nil =>
      have empty : left = [] := by simpa [Unifying.bindAnswers] using firstRun.symm
      subst left
      simpa using secondRun
  | cons answer rest ih =>
      simp only [Unifying.bindAnswers] at firstRun
      cases tailRun : Unifying.bindAnswers pattern body rest with
      | none => simp [tailRun] at firstRun
      | some tail =>
          simp only [tailRun] at firstRun
          cases unified : Unifying.unifyBinding answer.bindings pattern answer.value with
          | exhausted => simp [unified] at firstRun
          | clash =>
              simp [unified] at firstRun
              subst left
              simp [Unifying.bindAnswers, ih tail tailRun, unified]
          | ok bindings =>
              simp [unified] at firstRun
              subst left
              simp [Unifying.bindAnswers, ih tail tailRun, unified]

/-- The real returned-answer rule installs precisely these continuations;
the saved caller frames, effects and freshness counter are retained. -/
theorem source_return_composes (program : Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.Program)
    (source : Unifying.Configuration) (pattern body : Atom) (answers : List Unifying.Answer)
    (frames : List Unifying.Frame) (continued : List Unifying.Control)
    (control : source.control = .returned answers)
    (stack : source.frames = .bind pattern body :: frames)
    (bound : Unifying.bindAnswers pattern body answers = some continued) :
    Unifying.step program source = some { source with control := .sequence continued [], frames := frames } := by
  simp [Unifying.step, control, stack, bound]

namespace Controls

def sym (name : String) : Atom := .symbol name
def var (name : String) : Atom := .var name
def num (value : Int) : Atom := .grounded (.int value)
def tuple (items : List Atom) : Atom := .expression items
def call (head : String) (args : List Atom) : Atom := .expression (.symbol head :: args)
def letIn (pattern value body : Atom) : Atom := call "let" [pattern, value, body]

/-- The helper and caller are actual authored equations of the source
machine, not a supplied semantic function returning an alias. -/
def helperProgram (tag : String) : SpaceSemantics.Program where
  equations := [
    ⟨"head-any", [tuple [var "head", var "argument"]], var "head"⟩,
    ⟨"alias-one", [var "a"],
      letIn (var "b") (call "head-any" [var "a"])
        (letIn (var "b") (sym tag) (var "a"))⟩]
  declarations := [call ":" [sym "head-any", call "->" [sym "%Undefined%", sym "%Undefined%"]]]
  layout := [.equation, .equation, .declaration]

def observed (program : SpaceSemantics.Program) (expression : Atom) : LiveEquations.Observation :=
  Unifying.observed (Unifying.run program 250 (Unifying.start (Effects.loaded program) expression))

def openPair : Atom := tuple [var "x", num 1]

/-- The helper returns `$x`; binding the returned alias changes both the
caller's saved pair and the caller's own `$x`. -/
theorem helper_result_binds_caller :
    observed (helperProgram "Known")
      (letIn (var "result") (call "alias-one" [openPair]) (tuple [var "result", var "x"])) =
      .answers [tuple [tuple [sym "Known", num 1], sym "Known"]] := by
  decide +kernel

theorem helper_returns_changed_pair :
    observed (helperProgram "inc") (call "alias-one" [openPair]) =
      .answers [tuple [sym "inc", num 1]] := by
  decide +kernel

def recursiveProgram : SpaceSemantics.Program where
  equations := [
    ⟨"bind-known", [var "value"], letIn (var "value") (sym "Known") (sym "ack")⟩,
    ⟨"relay", [sym "Zero", var "value"], call "bind-known" [var "value"]⟩,
    ⟨"relay", [call "Next" [var "n"], var "value"], call "relay" [var "n", var "value"]⟩]
  declarations := []
  layout := [.equation, .equation, .equation]

/-- A recursive helper binds an input variable and returns unrelated data.
The outer caller nevertheless receives the changed input substitution. -/
theorem recursive_callee_binding_reaches_caller :
    observed recursiveProgram
      (letIn (var "result")
        (call "relay" [call "Next" [call "Next" [sym "Zero"]], var "x"])
        (tuple [var "result", var "x"])) =
      .answers [tuple [sym "ack", sym "Known"]] := by
  decide +kernel

def branchingProgram : SpaceSemantics.Program where
  equations := [
    ⟨"pick", [var "x"], letIn (var "x") (num 1) (sym "left")⟩,
    ⟨"pick", [var "x"], letIn (var "x") (num 1) (sym "left")⟩,
    ⟨"pick", [var "x"], letIn (var "x") (num 2) (sym "right")⟩]
  declarations := []
  layout := [.equation, .equation, .equation]

theorem ordered_duplicate_branches_keep_their_bindings :
    observed branchingProgram
      (letIn (var "result") (call "pick" [var "x"]) (tuple [var "result", var "x"])) =
      .answers [tuple [sym "left", num 1], tuple [sym "left", num 1], tuple [sym "right", num 2]] := by
  decide +kernel

def before : MORK.Subst := [("a", openPair)]
def returnedAlias : Unifying.Answer := ⟨var "x", before⟩
def boundAlias : MORK.Subst := Unifying.bindVar before "b" (var "x")
def reboundAlias : MORK.Subst := Unifying.bindVar boundAlias "x" (sym "inc")

theorem returned_alias_is_real_unification :
    Unifying.unifyBinding returnedAlias.bindings (var "b") returnedAlias.value = .ok boundAlias ∧
      Unifying.unifyBinding boundAlias (var "b") (sym "inc") = .ok reboundAlias := by
  decide +kernel

theorem before_idempotent : Unifying.Idempotent before := by
  intro name value found other member
  simp [before, MORK.Subst.lookup] at found
  rcases found with ⟨rfl, rfl⟩
  simp [openPair, tuple, var, num, MORK.atomFreeVars, MORK.atomFreeVars.atomFreeVarsList] at member
  subst other
  rfl

theorem caller_refined_through_returned_alias : Unifying.Refines before reboundAlias := by
  obtain ⟨valid, first, _⟩ := variable_binding_refines before boundAlias "b" (var "x")
    before_idempotent returned_alias_is_real_unification.1
  obtain ⟨_, second, _⟩ := variable_binding_refines boundAlias reboundAlias "b" (sym "inc")
    valid returned_alias_is_real_unification.2
  exact first.trans second

theorem newly_bound_name_still_shares_current_dependency :
    support (Unifying.resolve boundAlias (var "a")) = {"x"} ∧
      support (Unifying.resolve boundAlias (var "b")) = {"x"} := by
  decide +kernel

theorem current_dependency_check_detects_damage :
    dependencyCheck before reboundAlias (var "a") = false := by decide +kernel

theorem source_name_separation_does_not_protect :
    "a" ≠ "b" ∧ Unifying.resolve reboundAlias (var "a") = tuple [sym "inc", num 1] := by
  decide +kernel

theorem source_result_guard_still_matters (grounded : String → Bool) :
    chainCall TypedCalls.Controls.decls (metatype grounded)
      (fun _ => ({tuple [sym "inc", num 1]} : Multiset Atom)) pairRow
      [openPair] = 0 := by
  change chainCall TypedCalls.Controls.decls (metatype grounded)
    (fun _ => ({tuple [sym "inc", num 1]} : Multiset Atom)) pairRow [TypedCalls.Controls.gOne] = 0
  exact (TypedCalls.Controls.pair_rejects_declared_head grounded).2

theorem source_and_guard_boundary (grounded : String → Bool) :
    observed (helperProgram "inc") (call "alias-one" [openPair]) =
      .answers [tuple [sym "inc", num 1]] ∧
    chainCall TypedCalls.Controls.decls (metatype grounded)
      (fun _ => ({tuple [sym "inc", num 1]} : Multiset Atom)) pairRow [openPair] = 0 :=
  ⟨helper_returns_changed_pair, source_result_guard_still_matters grounded⟩

theorem deduplication_changes_source_result :
    observed branchingProgram
      (letIn (var "result") (call "pick" [var "x"]) (tuple [var "result", var "x"])) ≠
      .answers [tuple [sym "left", num 1], tuple [sym "right", num 2]] := by
  rw [ordered_duplicate_branches_keep_their_bindings]
  decide +kernel

theorem ground_dependency_certificate : dependencyCheck before reboundAlias (num 7) = true := by
  decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceCallAliasTransport
