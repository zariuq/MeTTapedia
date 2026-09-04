import Mettapedia.GSLT.Core.ProofRelevantGSLT
import Mettapedia.Languages.ProcessCalculi.MORK.GSLTSemantics

/-!
# Reflective MM2 execution

Ordinary MM2 permits an executable rule to match its own pattern and template
as expression-local byte data, then emit a later executable rule from those
captured values.  A captured pattern may contain variable-reference bytes; it
is nevertheless a closed value at the outer template level.

The earlier support model admitted an output only when the substituted `Atom`
contained no `.var` nodes.  That condition rejects MM2's standard reflective
self-staging idiom because the `Atom` carrier does not distinguish captured
inner variable bytes from unresolved variables in the outer template.

This module states the correct outer-level condition: every variable directly
written by the output template must be bound.  A value obtained from such a
binding is inserted opaquely, including any expression-local variables inside
the captured value.  Truly unbound output variables still fail closed.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT
open Mettapedia.GSLT.ProofRelevant

mutual
  /-- Every variable occurrence authored directly in a template has a match
  binding.  Bound replacement values are opaque at this stage: their internal
  variables belong to the captured expression, not the outer template. -/
  def templateCovered (substitution : Subst) : Atom → Bool
    | .var name => (substitution.lookup name).isSome
    | .symbol _ | .grounded _ => true
    | .expression children => templatesCovered substitution children

  def templatesCovered (substitution : Subst) : List Atom → Bool
    | [] => true
    | head :: tail =>
        templateCovered substitution head &&
          templatesCovered substitution tail
end

/-- Instantiate a template atom exactly when every outer variable is bound.
Captured expression-local variables may remain inside the resulting value. -/
def instantiateTemplateAtom? (substitution : Subst) (template : Atom) :
    Option Atom :=
  if templateCovered substitution template then
    some (applySubst substitution template)
  else
    none

/-- Instantiating a bare output variable succeeds exactly when the matcher
environment contains the value that will be republished. -/
theorem instantiateTemplateAtom?_var_eq_some_iff
    (substitution : Subst) (name : String) (atom : Atom) :
    instantiateTemplateAtom? substitution (.var name) = some atom ↔
      Subst.lookup substitution name = some atom := by
  cases lookup : Subst.lookup substitution name with
  | none => simp [instantiateTemplateAtom?, templateCovered, lookup]
  | some value =>
      simp [instantiateTemplateAtom?, templateCovered, applySubst, lookup]

/-- Coverage of an output template reconstructs a binding for every variable
authored in that template.  The bound value remains intentionally opaque and
need not itself be ground: expression-local variables inside a captured
continuation are not variables of the outer template. -/
theorem templateCovered_lookup_of_mem_freeVars
    : ∀ (substitution : Subst) (template : Atom),
    templateCovered substitution template = true →
    ∀ (name : String), name ∈ atomFreeVars template →
    ∃ value, Subst.lookup substitution name = some value := by
  intro substitution template covered name occurs
  match template with
  | .var variableName =>
      simp only [atomFreeVars, List.mem_cons, List.mem_nil_iff,
        or_false] at occurs
      subst name
      cases lookup : Subst.lookup substitution variableName with
      | none => simp [templateCovered, lookup] at covered
      | some value => exact ⟨value, rfl⟩
  | .symbol _ => simp [atomFreeVars] at occurs
  | .grounded _ => simp [atomFreeVars] at occurs
  | .expression children =>
      exact templatesCovered_lookup_of_mem_freeVars substitution children
        covered name occurs
where
  templatesCovered_lookup_of_mem_freeVars
      (substitution : Subst) :
      ∀ (templates : List Atom),
      templatesCovered substitution templates = true →
      ∀ (name : String),
      name ∈ atomFreeVars.atomFreeVarsList templates →
      ∃ value, Subst.lookup substitution name = some value
    | [], _, name, occurs => by simp [atomFreeVars.atomFreeVarsList] at occurs
    | head :: tail, covered, name, occurs => by
        simp only [templatesCovered, Bool.and_eq_true] at covered
        simp only [atomFreeVars.atomFreeVarsList, List.mem_append] at occurs
        rcases occurs with headOccurs | tailOccurs
        · exact templateCovered_lookup_of_mem_freeVars substitution head
            covered.1 name headOccurs
        · exact templatesCovered_lookup_of_mem_freeVars substitution tail
            covered.2 name tailOccurs

/-- On the shared well-bound, structurally ground image, reflective
instantiation is exactly the earlier ground-output instantiation. -/
theorem instantiateTemplateAtom_of_covered
    (substitution : Subst) (template : Atom)
    (covered : templateCovered substitution template = true) :
    instantiateTemplateAtom? substitution template =
      some (applySubst substitution template) := by
  simp [instantiateTemplateAtom?, covered]

/-- Stage one support-valued sink under reflective MM2 instantiation. -/
def stageReflectiveSupportSink (sink : Sink) (staged : List Atom)
    (substitution : Subst) : List Atom :=
  match instantiateTemplateAtom? substitution sink.atom with
  | none => staged
  | some instantiated => insertSupport staged instantiated

/-- The built-in support sink provider with expression-local byte capture. -/
def reflectiveSupportSinkProvider : BatchSinkProvider Sink where
  Stage := fun _ => List Atom
  init := fun _ => []
  stage := stageReflectiveSupportSink
  finalize := finalizeSupportSink

/-- Apply every authored sink after staging all reflectively instantiated
rows. -/
def applyReflectiveSinkBatch (space : Space) (rows : List Subst)
    (template : Template) : Space :=
  reflectiveSupportSinkProvider.run rows space template.sinks

/-- One sink row agrees with the existing support semantics whenever the
outer template is covered and its instantiated result is structurally
ground.  Reflective execution is therefore an extension, not a replacement,
of the admitted ground-output behavior. -/
theorem stageReflectiveSupportSink_eq_stageSupportSink_of_ground
    (sink : Sink) (staged : List Atom) (substitution : Subst)
    (covered : templateCovered substitution sink.atom = true)
    (ground : isGroundAtom (applySubst substitution sink.atom) = true) :
    stageReflectiveSupportSink sink staged substitution =
      stageSupportSink sink staged substitution := by
  cases sink with
  | add atom =>
      simp only [Sink.atom] at covered ground
      simp only [stageReflectiveSupportSink, Sink.atom]
      rw [instantiateTemplateAtom_of_covered _ _ covered]
      change insertSupport staged (applySubst substitution atom) =
        (if isGroundAtom (applySubst substitution atom) then
          insertSupport staged (applySubst substitution atom) else staged)
      simp [ground]
  | remove atom =>
      simp only [Sink.atom] at covered ground
      simp only [stageReflectiveSupportSink, Sink.atom]
      rw [instantiateTemplateAtom_of_covered _ _ covered]
      rfl
  | head count atom =>
      simp only [Sink.atom] at covered ground
      simp only [stageReflectiveSupportSink, Sink.atom]
      rw [instantiateTemplateAtom_of_covered _ _ covered]
      change insertSupport staged (applySubst substitution atom) =
        (if isGroundAtom (applySubst substitution atom) then
          insertSupport staged (applySubst substitution atom) else staged)
      simp [ground]
  | tail count atom =>
      simp only [Sink.atom] at covered ground
      simp only [stageReflectiveSupportSink, Sink.atom]
      rw [instantiateTemplateAtom_of_covered _ _ covered]
      change insertSupport staged (applySubst substitution atom) =
        (if isGroundAtom (applySubst substitution atom) then
          insertSupport staged (applySubst substitution atom) else staged)
      simp [ground]

/-- Fire one supported directive using reflective template instantiation. -/
noncomputable def fireReflectiveSourceExecFact
    (space : Space) (directive : SourceExecFact) : Space :=
  let live := consumeAtom space directive.atom
  let read := readCopyAtom space directive.atom
  let rows := matchInputSpec [] read directive.rule.input
  applyReflectiveSinkBatch live (rows.map Prod.fst) directive.rule.tmpl

/-- Full MM2 work-queue behavior for the modeled source/sink vocabulary,
including expression-local code capture. -/
noncomputable def reflectiveSourceWorkQueueStep
    (policy : UnsupportedExecPolicy) (space : Space) : Option Space :=
  match policy with
  | .leaveInert =>
      match selectNextScheduled (supportedSourceExecFactsOfSpace space) with
      | none => none
      | some directive =>
          some (fireReflectiveSourceExecFact space directive)
  | .consume =>
      match selectNextScheduled (rawExecFactsOfSpace space) with
      | none => none
      | some raw =>
          match decodeSupportedSourceExec raw with
          | some directive =>
              some (fireReflectiveSourceExecFact space directive)
          | none => some (space.erase raw.atom)

/-- Exact-fuel reflective execution over finite support. -/
noncomputable def reflectiveSourceWorkQueueRunN
    (policy : UnsupportedExecPolicy) : Nat → Space → Space × Nat
  | 0, space => (space, 0)
  | fuel + 1, space =>
      match reflectiveSourceWorkQueueStep policy space with
      | none => (space, 0)
      | some next =>
          let (final, used) :=
            reflectiveSourceWorkQueueRunN policy fuel next
          (final, used + 1)

/-! ## Computable list realization

The ordinary MM2 surface is executed over finite support.  The list
realization below is not a second semantics: the correspondence theorems in
this section prove that its finite support is exactly the support-level
reflective semantics above.  Keeping the list carrier explicit makes bounded
execution and generated `.mm2` qualification kernel-computable.
-/

namespace ReflectiveComputable

open WQComputable

/-- Batched reflective sinks over a duplicate-free list presentation of
finite support. -/
def cApplyReflectiveSinkBatch (rows : List Subst) :
    List Atom → List Sink → List Atom
  | space, [] => space
  | space, sink :: rest =>
      let staged := rows.foldl (stageReflectiveSupportSink sink) []
      cApplyReflectiveSinkBatch rows
        (cFinalizeSupportSink sink staged space) rest

/-- Computable list realization of one reflective template. -/
def cApplyReflectiveTemplate (space : List Atom) (rows : List Subst)
    (template : Template) : List Atom :=
  cApplyReflectiveSinkBatch rows space template.sinks

/-- Fire one source-aware directive with expression-local byte capture over a
list presentation. -/
def cFireReflectiveSourceExecFact
    (space : List Atom) (directive : SourceExecFact) : List Atom :=
  let live := space.erase directive.atom
  let read := directive.atom :: live
  let rows := Conformance.Computable.cmatchInputSpec [] read
    directive.rule.input
  cApplyReflectiveTemplate live (rows.map Prod.fst) directive.rule.tmpl

/-- Computable reflective least-key work-queue step. -/
def cReflectiveSourceWorkQueueStep
    (policy : UnsupportedExecPolicy) (space : List Atom) :
    Option (List Atom) :=
  match policy with
  | .leaveInert =>
      match selectNextScheduled (cSupportedSourceExecFacts space) with
      | none => none
      | some directive =>
          some (cFireReflectiveSourceExecFact space directive)
  | .consume =>
      match selectNextScheduled (cRawExecFacts space) with
      | none => none
      | some raw =>
          match decodeSupportedSourceExec raw with
          | some directive =>
              some (cFireReflectiveSourceExecFact space directive)
          | none => some (space.erase raw.atom)

/-- Exact-fuel computable reflective execution. -/
def cReflectiveSourceWorkQueueRunN (policy : UnsupportedExecPolicy) :
    Nat → List Atom → List Atom × Nat
  | 0, space => (space, 0)
  | fuel + 1, space =>
      match cReflectiveSourceWorkQueueStep policy space with
      | none => (space, 0)
      | some next =>
          let (final, used) :=
            cReflectiveSourceWorkQueueRunN policy fuel next
          (final, used + 1)

end ReflectiveComputable

open ReflectiveComputable
open WQComputable

/-! ## Scheduler membership -/

/-- The generic least-key scheduler can only return an element of the input
candidate list.  This elementary fact is kept explicit because whole-machine
invariants use it to inherit properties from the emitted verifier rule set. -/
theorem selectNextScheduled_mem {α : Type} [SchedulerKey α]
    {facts : List α} {selected : α}
    (selectedEq : selectNextScheduled facts = some selected) :
    selected ∈ facts := by
  unfold selectNextScheduled at selectedEq
  have foldMem : ∀ (remaining : List α) (best : Option α),
      remaining.foldl (fun current candidate =>
        match current with
        | none => some candidate
        | some incumbent =>
          if lexLt (SchedulerKey.key candidate)
              (SchedulerKey.key incumbent)
          then some candidate
          else some incumbent) best = some selected →
        selected ∈ remaining ∨ best = some selected := by
    intro remaining
    induction remaining with
    | nil =>
        intro best equal
        exact Or.inr equal
    | cons head tail induction =>
        intro best equal
        simp only [List.foldl_cons] at equal
        rcases induction _ equal with tailMember | nextBest
        · exact Or.inl (List.mem_cons_of_mem head tailMember)
        · cases best with
          | none =>
              change some head = some selected at nextBest
              have headEq : head = selected := Option.some.inj nextBest
              exact Or.inl (headEq ▸ List.mem_cons_self)
          | some incumbent =>
              change (if lexLt (SchedulerKey.key head)
                  (SchedulerKey.key incumbent)
                then some head else some incumbent) = some selected at nextBest
              split at nextBest
              · have headEq : head = selected := Option.some.inj nextBest
                exact Or.inl (headEq ▸ List.mem_cons_self)
              · exact Or.inr nextBest
  rcases foldMem facts none selectedEq with member | impossible
  · exact member
  · contradiction

/-! ## Executable reflective realization as a GSLT -/

/-- The duplicate-free list machine used by direct MM2 execution, exposed as
an executable realization GSLT.  Its term carrier deliberately retains list
order and possible duplicates; correspondence with the authored
support-valued MM2 GSLT is a separate theorem with explicit realization
invariants below. -/
def reflectiveNativeListExecGSLT
    (policy : UnsupportedExecPolicy) : GSLT where
  Term := List Atom
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    cReflectiveSourceWorkQueueStep policy source = some target
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

@[simp] theorem reflectiveNativeListExecGSLT_step_iff
    (policy : UnsupportedExecPolicy) (source target : List Atom) :
    (reflectiveNativeListExecGSLT policy).Step source target ↔
      cReflectiveSourceWorkQueueStep policy source = some target :=
  Iff.rfl

/-- The executable reflective realization is deterministic because its step
relation is the graph of the concrete work-queue function. -/
theorem reflectiveNativeListExecGSLT_step_deterministic
    (policy : UnsupportedExecPolicy) {source left right : List Atom}
    (leftStep : (reflectiveNativeListExecGSLT policy).Step source left)
    (rightStep : (reflectiveNativeListExecGSLT policy).Step source right) :
    left = right := by
  rw [reflectiveNativeListExecGSLT_step_iff] at leftStep rightStep
  exact Option.some.inj (leftStep.symm.trans rightStep)

/-- The computable reflective sink runner realizes the mathematical batch
provider on finite support. -/
theorem cApplyReflectiveSinkBatch_toFinset (rows : List Subst)
    (space : List Atom) (sinks : List Sink) :
    (cApplyReflectiveSinkBatch rows space sinks).toFinset =
      reflectiveSupportSinkProvider.run rows space.toFinset sinks := by
  induction sinks generalizing space with
  | nil => rfl
  | cons sink rest induction =>
      simp only [cApplyReflectiveSinkBatch, BatchSinkProvider.run_cons]
      rw [induction, cFinalizeSupportSink_toFinset]
      rfl

/-- Template-level reflective list/support correspondence. -/
theorem cApplyReflectiveTemplate_toFinset (space : List Atom)
    (rows : List Subst) (template : Template) :
    (cApplyReflectiveTemplate space rows template).toFinset =
      applyReflectiveSinkBatch space.toFinset rows template := by
  exact cApplyReflectiveSinkBatch_toFinset rows space template.sinks

/-- Exact matcher-row alignment required to relate a computable reflective
firing to its support-level counterpart. -/
def ReflectiveSourceRowAlignment
    (space : List Atom) (directive : SourceExecFact) : Prop :=
  (Conformance.Computable.cmatchInputSpec []
      (directive.atom :: space.erase directive.atom)
      directive.rule.input).map Prod.fst =
    (matchInputSpec [] (readCopyAtom space.toFinset directive.atom)
      directive.rule.input).map Prod.fst

/-- The representation-independent matcher obligation.  The list and
finite-support realizations may enumerate successful substitutions in
different orders; add/remove sinks observe only which substitutions occur. -/
def ReflectiveSourceRowSupportAlignment
    (space : List Atom) (directive : SourceExecFact) : Prop :=
  ((Conformance.Computable.cmatchInputSpec []
      (directive.atom :: space.erase directive.atom)
      directive.rule.input).map Prod.fst).toFinset =
    ((matchInputSpec [] (readCopyAtom space.toFinset directive.atom)
      directive.rule.input).map Prod.fst).toFinset

/-- Reflective staging contains an atom exactly when it was already staged
or some matcher row instantiates the sink to that atom. -/
theorem mem_foldl_stageReflectiveSupportSink_iff
    (sink : Sink) (rows : List Subst) (staged : List Atom)
    (candidate : Atom) :
    candidate ∈ rows.foldl (stageReflectiveSupportSink sink) staged ↔
      candidate ∈ staged ∨
        ∃ substitution ∈ rows,
          instantiateTemplateAtom? substitution sink.atom = some candidate := by
  induction rows generalizing staged with
  | nil => simp
  | cons substitution rest induction =>
      rw [List.foldl_cons, induction]
      have stageMembership :
          candidate ∈ stageReflectiveSupportSink sink staged substitution ↔
            candidate ∈ staged ∨
              instantiateTemplateAtom? substitution sink.atom =
                some candidate := by
        cases instantiated : instantiateTemplateAtom? substitution sink.atom with
        | none => simp [stageReflectiveSupportSink, instantiated]
        | some atom =>
            by_cases present : atom ∈ staged
            · simp only [stageReflectiveSupportSink, instantiated,
                insertSupport, present, if_pos]
              constructor
              · exact Or.inl
              · rintro (member | equal)
                · exact member
                · exact (Option.some.inj equal) ▸ present
            · simp [stageReflectiveSupportSink, instantiated, insertSupport,
                present, eq_comm]
      rw [stageMembership]
      aesop

/-- Staging add/remove support depends only on the finite support of matcher
substitutions, not their enumeration order or duplicate multiplicity. -/
theorem foldl_stageReflectiveSupportSink_toFinset_eq_of_rows_toFinset_eq
    (sink : Sink) (left right : List Subst)
    (rowsEqual : left.toFinset = right.toFinset) :
    (left.foldl (stageReflectiveSupportSink sink) []).toFinset =
      (right.foldl (stageReflectiveSupportSink sink) []).toFinset := by
  ext candidate
  simp only [List.mem_toFinset,
    mem_foldl_stageReflectiveSupportSink_iff, List.not_mem_nil, false_or]
  constructor
  · rintro ⟨substitution, member, instantiated⟩
    refine ⟨substitution, ?_, instantiated⟩
    have : substitution ∈ left.toFinset := List.mem_toFinset.mpr member
    rw [rowsEqual] at this
    exact List.mem_toFinset.mp this
  · rintro ⟨substitution, member, instantiated⟩
    refine ⟨substitution, ?_, instantiated⟩
    have : substitution ∈ right.toFinset := List.mem_toFinset.mpr member
    rw [← rowsEqual] at this
    exact List.mem_toFinset.mp this

/-- The sink fragment whose result depends only on matcher-row support.
Extrema sinks require a separate ordering theorem and are intentionally not
admitted through this boundary. -/
def ReflectiveSupportSetSink : Sink → Prop
  | .add _ | .remove _ => True
  | .head _ _ | .tail _ _ => False

def ReflectiveSupportSetTemplate (template : Template) : Prop :=
  ∀ sink ∈ template.sinks, ReflectiveSupportSetSink sink

/-- Executable recognition of the same support-insensitive sink fragment. -/
def reflectiveSupportSetSinkB : Sink → Bool
  | .add _ | .remove _ => true
  | .head _ _ | .tail _ _ => false

@[simp] theorem reflectiveSupportSetSinkB_eq_true_iff (sink : Sink) :
    reflectiveSupportSetSinkB sink = true ↔
      ReflectiveSupportSetSink sink := by
  cases sink <;> simp [reflectiveSupportSetSinkB, ReflectiveSupportSetSink]

/-- A finite MM2 template passes the executable support-fragment check exactly
when every one of its sinks is support-insensitive. -/
theorem all_reflectiveSupportSetSinkB_eq_true_iff (template : Template) :
    template.sinks.all reflectiveSupportSetSinkB = true ↔
      ReflectiveSupportSetTemplate template := by
  simp [ReflectiveSupportSetTemplate, List.all_eq_true]

/-- Extrema are deliberately excluded: their compact-key ordering requires
an additional theorem and cannot be smuggled through support-only adequacy. -/
theorem reflectiveHead_not_supportSetSink (count : Nat) (atom : Atom) :
    ¬ ReflectiveSupportSetSink (.head count atom) := by
  simp [ReflectiveSupportSetSink]

/-- Support insertion preserves the duplicate-free list representation. -/
theorem insertSupport_nodup (space : List Atom) (atom : Atom)
    (nodup : space.Nodup) :
    (insertSupport space atom).Nodup := by
  unfold insertSupport
  split
  · exact nodup
  · rename_i fresh
    exact List.Nodup.append nodup (List.nodup_singleton atom)
      (fun candidate member candidateSingleton =>
        fresh ((List.mem_singleton.mp candidateSingleton) ▸ member))

theorem cUnionSupport_nodup (space staged : List Atom)
    (nodup : space.Nodup) :
    (cUnionSupport space staged).Nodup := by
  induction staged generalizing space with
  | nil => exact nodup
  | cons atom rest induction =>
      exact induction _ (insertSupport_nodup space atom nodup)

theorem cSubtractSupport_nodup (space staged : List Atom)
    (nodup : space.Nodup) :
    (cSubtractSupport space staged).Nodup := by
  exact nodup.filter _

/-- Finalizing an add/remove sink cannot introduce a duplicate atom. -/
theorem cFinalizeSupportSetSink_nodup (sink : Sink)
    (staged space : List Atom)
    (supported : ReflectiveSupportSetSink sink)
    (nodup : space.Nodup) :
    (cFinalizeSupportSink sink staged space).Nodup := by
  cases sink with
  | add => exact cUnionSupport_nodup space staged nodup
  | remove => exact cSubtractSupport_nodup space staged nodup
  | head => contradiction
  | tail => contradiction

/-- Every add/remove-only reflective template preserves duplicate freedom,
independently of matcher row order or multiplicity. -/
theorem cApplyReflectiveTemplate_nodup
    (space : List Atom) (rows : List Subst) (template : Template)
    (supported : ReflectiveSupportSetTemplate template)
    (nodup : space.Nodup) :
    (cApplyReflectiveTemplate space rows template).Nodup := by
  change (cApplyReflectiveSinkBatch rows space template.sinks).Nodup
  have allSupported : ∀ sink ∈ template.sinks,
      ReflectiveSupportSetSink sink := supported
  generalize template.sinks = sinks at allSupported ⊢
  induction sinks generalizing space with
  | nil => exact nodup
  | cons sink rest induction =>
      simp only [cApplyReflectiveSinkBatch]
      apply induction
      · exact cFinalizeSupportSetSink_nodup sink
          (rows.foldl (stageReflectiveSupportSink sink) []) space
          (allSupported sink (by simp)) nodup
      · exact fun candidate member =>
          allSupported candidate (List.mem_cons_of_mem sink member)

/-- One firing of an add/remove-only directive preserves the duplicate-free
list carrier required by the executable-to-authored realization theorem. -/
theorem cFireReflectiveSourceExecFact_nodup
    (space : List Atom) (directive : SourceExecFact)
    (supported : ReflectiveSupportSetTemplate directive.rule.tmpl)
    (nodup : space.Nodup) :
    (cFireReflectiveSourceExecFact space directive).Nodup := by
  apply cApplyReflectiveTemplate_nodup
  · exact supported
  · exact nodup.erase directive.atom

/-- Atoms genuinely introduced by add sinks.  Remove sinks can only discard
atoms and therefore have no witnesses in this relation. -/
def ReflectiveAddedAtom (rows : List Subst) (sinks : List Sink)
    (atom : Atom) : Prop :=
  ∃ sink ∈ sinks, ∃ authored,
    sink = .add authored ∧
      ∃ substitution ∈ rows,
        instantiateTemplateAtom? substitution authored = some atom

@[simp] theorem mem_insertSupport_iff (candidate atom : Atom)
    (space : List Atom) :
    candidate ∈ insertSupport space atom ↔
      candidate ∈ space ∨ candidate = atom := by
  unfold insertSupport
  by_cases present : atom ∈ space
  · simp [present]
    exact fun equal => equal ▸ present
  · simp [present]

theorem mem_cUnionSupport_iff (candidate : Atom)
    (space staged : List Atom) :
    candidate ∈ cUnionSupport space staged ↔
      candidate ∈ space ∨ candidate ∈ staged := by
  induction staged generalizing space with
  | nil => simp [cUnionSupport]
  | cons atom rest induction =>
      simp only [cUnionSupport, induction, mem_insertSupport_iff,
        List.mem_cons]
      aesop

/-- An add-only suffix preserves every atom already present in the space. -/
theorem mem_cApplyReflectiveSinkBatch_of_all_add
    (rows : List Subst) {space : List Atom} {sinks : List Sink}
    {candidate : Atom}
    (allAdd : ∀ sink ∈ sinks, ∃ authored, sink = .add authored)
    (member : candidate ∈ space) :
    candidate ∈ cApplyReflectiveSinkBatch rows space sinks := by
  induction sinks generalizing space with
  | nil => exact member
  | cons sink rest induction =>
      obtain ⟨authored, rfl⟩ := allAdd sink (by simp)
      simp only [cApplyReflectiveSinkBatch]
      apply induction
      · intro later laterMember
        exact allAdd later (by simp [laterMember])
      · change candidate ∈ cUnionSupport space _
        exact (mem_cUnionSupport_iff candidate space _).2 (Or.inl member)

/-- A successful row for an add sink publishes the instantiated atom, and an
add-only continuation cannot erase it. -/
theorem mem_cApplyReflectiveSinkBatch_add_cons_of_row
    (rows : List Subst) (space : List Atom) (authored candidate : Atom)
    (rest : List Sink) (substitution : Subst)
    (rowMember : substitution ∈ rows)
    (instantiates :
      instantiateTemplateAtom? substitution authored = some candidate)
    (restAdd : ∀ sink ∈ rest, ∃ later, sink = .add later) :
    candidate ∈
      cApplyReflectiveSinkBatch rows space (.add authored :: rest) := by
  simp only [cApplyReflectiveSinkBatch]
  apply mem_cApplyReflectiveSinkBatch_of_all_add rows restAdd
  change candidate ∈ cUnionSupport space _
  rw [mem_cUnionSupport_iff]
  right
  rw [mem_foldl_stageReflectiveSupportSink_iff]
  exact Or.inr ⟨substitution, rowMember, instantiates⟩

/-- In an add/remove-only batch, every surviving atom was either already in
the input space or was instantiated by an authored add sink. -/
theorem mem_cApplyReflectiveTemplate_of_supportSet
    (space : List Atom) (rows : List Subst) (template : Template)
    (supported : ReflectiveSupportSetTemplate template)
    {candidate : Atom}
    (member : candidate ∈ cApplyReflectiveTemplate space rows template) :
    candidate ∈ space ∨
      ReflectiveAddedAtom rows template.sinks candidate := by
  change candidate ∈
    cApplyReflectiveSinkBatch rows space template.sinks at member
  have allSupported : ∀ sink ∈ template.sinks,
      ReflectiveSupportSetSink sink := supported
  generalize template.sinks = sinks at allSupported member ⊢
  induction sinks generalizing space with
  | nil =>
      exact Or.inl member
  | cons sink rest induction =>
      simp only [cApplyReflectiveSinkBatch] at member
      rcases induction
          (cFinalizeSupportSink sink
            (rows.foldl (stageReflectiveSupportSink sink) []) space)
          (fun candidate candidateMember =>
            allSupported candidate
              (List.mem_cons_of_mem sink candidateMember)) member with
        prior | laterAdded
      · cases sink with
        | add authored =>
            change candidate ∈ cUnionSupport space
              (rows.foldl
                (stageReflectiveSupportSink (.add authored)) []) at prior
            rw [mem_cUnionSupport_iff] at prior
            rcases prior with original | staged
            · exact Or.inl original
            · right
              refine ⟨.add authored, ?_, authored, rfl, ?_⟩
              · simp
              · exact
                  (mem_foldl_stageReflectiveSupportSink_iff
                    (.add authored) rows [] candidate).1 staged |>.resolve_left
                    (by simp)
        | remove authored =>
            change candidate ∈ cSubtractSupport space
              (rows.foldl
                (stageReflectiveSupportSink (.remove authored)) []) at prior
            exact Or.inl (List.mem_filter.mp prior).1
        | head count authored =>
            exact False.elim
              (allSupported (.head count authored) (by simp) )
        | tail count authored =>
            exact False.elim
              (allSupported (.tail count authored) (by simp))
      · right
        rcases laterAdded with
          ⟨laterSink, laterMember, authored, equal, witness⟩
        exact ⟨laterSink, by simp [laterMember], authored,
          equal, witness⟩

/-- Every atom in a concrete carrier satisfies a structural predicate.  This
is used for verifier-owned inert rows whose safety cannot be expressed by the
top-level executable whitelist alone. -/
def AtomsWithin (property : Atom → Prop) (space : List Atom) : Prop :=
  ∀ atom ∈ space, property atom

/-- Every atom introduced by an authored add sink satisfies a structural
predicate. -/
def ReflectiveAddedAtomsWithin (property : Atom → Prop)
    (rows : List Subst) (template : Template) : Prop :=
  ∀ atom, ReflectiveAddedAtom rows template.sinks atom → property atom

/-- Add/remove execution preserves any atom-local invariant when the input
and all actual additions satisfy it. -/
theorem cApplyReflectiveTemplate_atomsWithin
    (property : Atom → Prop) (space : List Atom) (rows : List Subst)
    (template : Template)
    (supported : ReflectiveSupportSetTemplate template)
    (sourceWithin : AtomsWithin property space)
    (addedWithin : ReflectiveAddedAtomsWithin property rows template) :
    AtomsWithin property
      (cApplyReflectiveTemplate space rows template) := by
  intro atom member
  rcases mem_cApplyReflectiveTemplate_of_supportSet space rows template
      supported member with prior | added
  · exact sourceWithin atom prior
  · exact addedWithin atom added

/-- One reflective firing preserves any atom-local invariant under the same
authorization condition for its actual additions. -/
theorem cFireReflectiveSourceExecFact_atomsWithin
    (property : Atom → Prop) (space : List Atom)
    (directive : SourceExecFact)
    (supported : ReflectiveSupportSetTemplate directive.rule.tmpl)
    (sourceWithin : AtomsWithin property space)
    (addedWithin : ReflectiveAddedAtomsWithin property
      ((Conformance.Computable.cmatchInputSpec []
        (directive.atom :: space.erase directive.atom)
        directive.rule.input).map Prod.fst)
      directive.rule.tmpl) :
    AtomsWithin property
      (cFireReflectiveSourceExecFact space directive) := by
  apply cApplyReflectiveTemplate_atomsWithin
  · exact supported
  · intro atom member
    exact sourceWithin atom (List.mem_of_mem_erase member)
  · exact addedWithin

/-- Every executable shell currently present belongs to the declared target
artifact. -/
def RawExecFactsWithin (allowed : List RawExecFact)
    (space : List Atom) : Prop :=
  ∀ raw ∈ cRawExecFacts space, raw ∈ allowed

/-- One atom carries executable authority only from the declared artifact.
Non-executable atoms satisfy the property without acquiring authority. -/
def RawExecAtomWithin (allowed : List RawExecFact) (atom : Atom) : Prop :=
  ∀ raw, extractRawExecFact atom = some raw → raw ∈ allowed

/-- An atom-local property holds of every opaque value exposed by a capture
relation inside the carrier.  This is the representation boundary used when
data rows may later republish their payloads. -/
def CapturedAtomsWithin (property : Atom → Prop)
    (captures : Atom → Atom → Prop) (space : List Atom) : Prop :=
  ∀ carrier ∈ space, ∀ payload,
    captures carrier payload → property payload

/-- Specialization of `CapturedAtomsWithin` to executable authority from a
declared rule inventory. -/
def CapturedRawExecWithin (allowed : List RawExecFact)
    (captures : Atom → Atom → Prop) (space : List Atom) : Prop :=
  CapturedAtomsWithin (RawExecAtomWithin allowed) captures space

/-- One reflective firing preserves authority carried inside data rows when
every newly added carrier satisfies the same capture-local invariant.  This
is the generic closure seam for generated machines that propagate opaque
continuations without interpreting them. -/
theorem cFireReflectiveSourceExecFact_capturedAtomsWithin
    (property : Atom → Prop) (captures : Atom → Atom → Prop)
    (space : List Atom) (directive : SourceExecFact)
    (supported : ReflectiveSupportSetTemplate directive.rule.tmpl)
    (sourceWithin : CapturedAtomsWithin property captures space)
    (addedWithin : ReflectiveAddedAtomsWithin
      (fun carrier => ∀ payload, captures carrier payload → property payload)
      ((Conformance.Computable.cmatchInputSpec []
        (directive.atom :: space.erase directive.atom)
        directive.rule.input).map Prod.fst)
      directive.rule.tmpl) :
    CapturedAtomsWithin property captures
      (cFireReflectiveSourceExecFact space directive) := by
  exact cFireReflectiveSourceExecFact_atomsWithin
    (fun carrier => ∀ payload, captures carrier payload → property payload)
    space directive supported sourceWithin addedWithin

/-- Top-level executable containment implies the corresponding atom-local
authority statement for every atom already present in the carrier. -/
theorem RawExecFactsWithin.atom
    {allowed : List RawExecFact} {space : List Atom}
    (within : RawExecFactsWithin allowed space) {atom : Atom}
    (member : atom ∈ space) : RawExecAtomWithin allowed atom := by
  intro raw extracted
  exact within raw (List.mem_filterMap.mpr ⟨atom, member, extracted⟩)

/-- Every executable atom newly produced by an add sink belongs to the
declared target artifact. -/
def ReflectiveAddedRawWithin (allowed : List RawExecFact)
    (rows : List Subst) (template : Template) : Prop :=
  ∀ atom, ReflectiveAddedAtom rows template.sinks atom →
    ∀ raw, extractRawExecFact atom = some raw → raw ∈ allowed

/-- Add/remove template execution preserves the executable whitelist when
every actually added executable atom is authorized. -/
theorem cApplyReflectiveTemplate_rawExecFactsWithin
    (allowed : List RawExecFact) (space : List Atom) (rows : List Subst)
    (template : Template)
    (supported : ReflectiveSupportSetTemplate template)
    (sourceWithin : RawExecFactsWithin allowed space)
    (addedWithin : ReflectiveAddedRawWithin allowed rows template) :
    RawExecFactsWithin allowed
      (cApplyReflectiveTemplate space rows template) := by
  intro raw rawMember
  rcases List.mem_filterMap.mp rawMember with
    ⟨atom, atomMember, extracted⟩
  rcases mem_cApplyReflectiveTemplate_of_supportSet space rows template
      supported atomMember with prior | added
  · apply sourceWithin raw
    exact List.mem_filterMap.mpr ⟨atom, prior, extracted⟩
  · exact addedWithin atom added raw extracted

/-- One reflective firing preserves the executable whitelist under the same
explicit authorization condition for its instantiated add sinks. -/
theorem cFireReflectiveSourceExecFact_rawExecFactsWithin
    (allowed : List RawExecFact) (space : List Atom)
    (directive : SourceExecFact)
    (supported : ReflectiveSupportSetTemplate directive.rule.tmpl)
    (sourceWithin : RawExecFactsWithin allowed space)
    (addedWithin : ReflectiveAddedRawWithin allowed
      ((Conformance.Computable.cmatchInputSpec []
        (directive.atom :: space.erase directive.atom)
        directive.rule.input).map Prod.fst)
      directive.rule.tmpl) :
    RawExecFactsWithin allowed
      (cFireReflectiveSourceExecFact space directive) := by
  apply cApplyReflectiveTemplate_rawExecFactsWithin
  · exact supported
  · intro raw rawMember
    apply sourceWithin raw
    rcases List.mem_filterMap.mp rawMember with
      ⟨atom, atomMember, extracted⟩
    exact List.mem_filterMap.mpr
      ⟨atom, List.mem_of_mem_erase atomMember, extracted⟩
  · exact addedWithin

private theorem finalizeReflectiveSupportSetSink_eq_of_staged_toFinset_eq
    (sink : Sink) (left right : List Atom) (space : Space)
    (supported : ReflectiveSupportSetSink sink)
    (stagedEqual : left.toFinset = right.toFinset) :
    finalizeSupportSink sink left space =
      finalizeSupportSink sink right space := by
  cases sink <;> simp_all [ReflectiveSupportSetSink, finalizeSupportSink]

/-- On add/remove sinks, the reflective provider depends only on the finite
support of matcher substitutions. -/
private theorem reflectiveSupportSinkProvider_run_eq_of_rows_toFinset_eq
    (space : Space) (left right : List Subst) (sinks : List Sink)
    (supported : ∀ sink ∈ sinks, ReflectiveSupportSetSink sink)
    (rowsEqual : left.toFinset = right.toFinset) :
    reflectiveSupportSinkProvider.run left space sinks =
      reflectiveSupportSinkProvider.run right space sinks := by
  induction sinks generalizing space with
  | nil => rfl
  | cons sink rest induction =>
      simp only [BatchSinkProvider.run_cons]
      have stagedEqual :=
        foldl_stageReflectiveSupportSink_toFinset_eq_of_rows_toFinset_eq
          sink left right rowsEqual
      have finalizedEqual :=
        finalizeReflectiveSupportSetSink_eq_of_staged_toFinset_eq sink
          (reflectiveSupportSinkProvider.stageAll sink left)
          (reflectiveSupportSinkProvider.stageAll sink right) space
          (supported sink (by simp))
          (by simpa [BatchSinkProvider.stageAll,
            reflectiveSupportSinkProvider] using stagedEqual)
      have finalizedEqual' :
          reflectiveSupportSinkProvider.finalize sink
              (reflectiveSupportSinkProvider.stageAll sink left) space =
            reflectiveSupportSinkProvider.finalize sink
              (reflectiveSupportSinkProvider.stageAll sink right) space :=
        finalizedEqual
      rw [finalizedEqual']
      exact induction _ (fun candidate member =>
        supported candidate (List.mem_cons_of_mem sink member))

/-- On add/remove templates, reflective batch execution depends only on the
finite support of matcher substitutions. -/
theorem applyReflectiveSinkBatch_eq_of_rows_toFinset_eq
    (space : Space) (left right : List Subst) (template : Template)
    (supported : ReflectiveSupportSetTemplate template)
    (rowsEqual : left.toFinset = right.toFinset) :
    applyReflectiveSinkBatch space left template =
      applyReflectiveSinkBatch space right template := by
  exact reflectiveSupportSinkProvider_run_eq_of_rows_toFinset_eq
    space left right template.sinks supported rowsEqual

/-- For a duplicate-free list presentation, computable and support-valued
matching always agree on the finite support of substitutions. -/
theorem reflectiveSourceRowSupportAlignment_of_nodup
    (space : List Atom) (directive : SourceExecFact)
    (nodup : space.Nodup) :
    ReflectiveSourceRowSupportAlignment space directive := by
  let read := directive.atom :: space.erase directive.atom
  have readNodup : read.Nodup := by
    exact List.nodup_cons.mpr
      ⟨List.Nodup.not_mem_erase nodup, nodup.erase directive.atom⟩
  have readSupport : read.toFinset =
      readCopyAtom space.toFinset directive.atom := by
    simpa [read] using cReadCopyAtom_toFinset space directive.atom nodup
  unfold ReflectiveSourceRowSupportAlignment
  rw [← readSupport]
  ext substitution
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨matched, consumed⟩, member, rfl⟩
    exact ⟨(matched, consumed.toFinset),
      Conformance.cmatchInputSpec_toFinset_sound [] read readNodup
        directive.rule.input matched consumed member,
      rfl⟩
  · rintro ⟨⟨matched, consumed⟩, member, rfl⟩
    obtain ⟨consumedList, computable, _⟩ :=
      Conformance.cmatchInputSpec_toFinset_complete [] read readNodup
        directive.rule.input matched consumed member
    exact ⟨(matched, consumedList), computable, rfl⟩

/-- Minimal one-firing realization obligation, independent of how either
matcher enumerates rows. -/
def ReflectiveSourceFiringAgreement
    (space : List Atom) (directive : SourceExecFact) : Prop :=
  (cFireReflectiveSourceExecFact space directive).toFinset =
    fireReflectiveSourceExecFact space.toFinset directive

/-- One computable reflective firing has exactly the same finite support as
the mathematical reflective firing. -/
theorem cFireReflectiveSourceExecFact_toFinset
    (space : List Atom) (directive : SourceExecFact)
    (nodup : space.Nodup)
    (alignment : ReflectiveSourceRowAlignment space directive) :
    (cFireReflectiveSourceExecFact space directive).toFinset =
      fireReflectiveSourceExecFact space.toFinset directive := by
  simp only [cFireReflectiveSourceExecFact,
    fireReflectiveSourceExecFact]
  rw [cApplyReflectiveTemplate_toFinset]
  rw [listErase_toFinset space directive.atom nodup]
  rw [alignment]
  rfl

/-- Exact row alignment is one sufficient, deliberately stronger route to
the representation-independent firing agreement. -/
theorem reflectiveSourceFiringAgreement_of_rowAlignment
    (space : List Atom) (directive : SourceExecFact)
    (nodup : space.Nodup)
    (alignment : ReflectiveSourceRowAlignment space directive) :
    ReflectiveSourceFiringAgreement space directive :=
  cFireReflectiveSourceExecFact_toFinset space directive nodup alignment

/-- Add/remove-only templates need only finite-support matcher agreement. -/
theorem reflectiveSourceFiringAgreement_of_supportAlignment
    (space : List Atom) (directive : SourceExecFact)
    (nodup : space.Nodup)
    (supported : ReflectiveSupportSetTemplate directive.rule.tmpl)
    (alignment : ReflectiveSourceRowSupportAlignment space directive) :
    ReflectiveSourceFiringAgreement space directive := by
  simp only [ReflectiveSourceFiringAgreement,
    cFireReflectiveSourceExecFact, fireReflectiveSourceExecFact]
  rw [cApplyReflectiveTemplate_toFinset]
  rw [listErase_toFinset space directive.atom nodup]
  exact applyReflectiveSinkBatch_eq_of_rows_toFinset_eq
    (space.toFinset.erase directive.atom)
    ((Conformance.Computable.cmatchInputSpec []
      (directive.atom :: space.erase directive.atom)
      directive.rule.input).map Prod.fst)
    ((matchInputSpec [] (readCopyAtom space.toFinset directive.atom)
      directive.rule.input).map Prod.fst)
    directive.rule.tmpl supported alignment

/-- One computable reflective scheduler step realizes the existing
support-level MM2 scheduler. -/
theorem cReflectiveSourceWorkQueueStep_toFinset
    (policy : UnsupportedExecPolicy) (space : List Atom)
    (nodup : space.Nodup)
    (supportedKeyInj : KeyInjective (cSupportedSourceExecFacts space))
    (rawKeyInj : KeyInjective (cRawExecFacts space))
    (supportedAgreement : ∀ directive,
      selectNextScheduled (cSupportedSourceExecFacts space) = some directive →
      ReflectiveSourceFiringAgreement space directive)
    (rawAgreement : ∀ raw directive,
      selectNextScheduled (cRawExecFacts space) = some raw →
      decodeSupportedSourceExec raw = some directive →
      ReflectiveSourceFiringAgreement space directive) :
    (cReflectiveSourceWorkQueueStep policy space).map List.toFinset =
      reflectiveSourceWorkQueueStep policy space.toFinset := by
  cases policy with
  | leaveInert =>
      simp only [cReflectiveSourceWorkQueueStep,
        reflectiveSourceWorkQueueStep]
      rw [← cSourceWorkQueueStep_selectSupported_eq space nodup
        supportedKeyInj]
      cases selected :
          selectNextScheduled (cSupportedSourceExecFacts space) with
      | none => rfl
      | some directive =>
          simp only [Option.map]
          exact congrArg some
            (supportedAgreement directive selected)
  | consume =>
      simp only [cReflectiveSourceWorkQueueStep,
        reflectiveSourceWorkQueueStep]
      rw [← cSourceWorkQueueStep_selectRaw_eq space nodup rawKeyInj]
      cases selected : selectNextScheduled (cRawExecFacts space) with
      | none => rfl
      | some raw =>
          cases decoded : decodeSupportedSourceExec raw with
          | none =>
              simp only [decoded, Option.map]
              exact congrArg some (listErase_toFinset space raw.atom nodup)
          | some directive =>
              simp only [decoded, Option.map]
              exact congrArg some
                (rawAgreement raw directive selected decoded)

/-- Per-state obligations for faithful computable reflective execution. -/
structure ReflectiveWorkQueueInvariant (space : List Atom) : Prop where
  nodup : space.Nodup
  supportedKeyInj : KeyInjective (cSupportedSourceExecFacts space)
  rawKeyInj : KeyInjective (cRawExecFacts space)
  supportedAgreement : ∀ directive,
    selectNextScheduled (cSupportedSourceExecFacts space) = some directive →
    ReflectiveSourceFiringAgreement space directive
  rawAgreement : ∀ raw directive,
    selectNextScheduled (cRawExecFacts space) = some raw →
    decodeSupportedSourceExec raw = some directive →
    ReflectiveSourceFiringAgreement space directive

/-- The load-bearing global obligation for an executable MM2 profile: every
concrete scheduler step preserves the complete realization invariant.  This
is deliberately separate from the one-state invariant so a compiler cannot
replace an execution proof by a collection of unrelated phase checks. -/
def ReflectiveWorkQueueInvariantPreserved
    (policy : UnsupportedExecPolicy) : Prop :=
  ∀ {source target : List Atom},
    ReflectiveWorkQueueInvariant source →
    cReflectiveSourceWorkQueueStep policy source = some target →
    ReflectiveWorkQueueInvariant target

/-- A duplicate-free space with deterministic scheduler keys and only
add/remove selected templates automatically satisfies the concrete-to-authored
firing obligations.  Matcher enumeration order is discharged once by the
generic conformance theorem above. -/
theorem reflectiveWorkQueueInvariant_of_supportSet
    (space : List Atom)
    (nodup : space.Nodup)
    (supportedKeyInj : KeyInjective (cSupportedSourceExecFacts space))
    (rawKeyInj : KeyInjective (cRawExecFacts space))
    (supportedTemplates : ∀ directive,
      selectNextScheduled (cSupportedSourceExecFacts space) = some directive →
      ReflectiveSupportSetTemplate directive.rule.tmpl)
    (rawTemplates : ∀ raw directive,
      selectNextScheduled (cRawExecFacts space) = some raw →
      decodeSupportedSourceExec raw = some directive →
      ReflectiveSupportSetTemplate directive.rule.tmpl) :
    ReflectiveWorkQueueInvariant space where
  nodup := nodup
  supportedKeyInj := supportedKeyInj
  rawKeyInj := rawKeyInj
  supportedAgreement directive selected :=
    reflectiveSourceFiringAgreement_of_supportAlignment space directive nodup
      (supportedTemplates directive selected)
      (reflectiveSourceRowSupportAlignment_of_nodup space directive nodup)
  rawAgreement raw directive selected decoded :=
    reflectiveSourceFiringAgreement_of_supportAlignment space directive nodup
      (rawTemplates raw directive selected decoded)
      (reflectiveSourceRowSupportAlignment_of_nodup space directive nodup)

/-- If every raw executable shell in a space belongs to an emitted artifact
and decoding the artifact is closed in its supported-directive inventory,
then every supported directive visible in the space belongs to that inventory.
This is the generic rule-origin bridge used by presentation compilers. -/
theorem supportedSourceExecFactsWithin_of_rawExecFactsWithin
    (allowedRaw : List RawExecFact)
    (allowedDirectives : List SourceExecFact)
    (space : List Atom)
    (rawWithin : RawExecFactsWithin allowedRaw space)
    (decodeClosed : ∀ {raw directive},
      raw ∈ allowedRaw → decodeSupportedSourceExec raw = some directive →
        directive ∈ allowedDirectives) :
    ∀ directive ∈ cSupportedSourceExecFacts space,
      directive ∈ allowedDirectives := by
  intro directive member
  rcases List.mem_filterMap.mp member with
    ⟨atom, atomMember, extracted⟩
  unfold extractSupportedSourceExecFact at extracted
  cases rawEq : extractRawExecFact atom with
  | none => simp [rawEq] at extracted
  | some raw =>
      simp [rawEq] at extracted
      have rawMember : raw ∈ cRawExecFacts space :=
        List.mem_filterMap.mpr ⟨atom, atomMember, rawEq⟩
      exact decodeClosed (rawWithin raw rawMember) extracted

/-- A finite emitted-rule inventory licenses the concrete-to-authored MM2
invariant for every duplicate-free state whose executable shells come from
that inventory.  The theorem is presentation-independent: callers must
supply the actual emitted inventories and their decoding, key, and sink laws. -/
theorem reflectiveWorkQueueInvariant_of_ruleInventory
    (allowedRaw : List RawExecFact)
    (allowedDirectives : List SourceExecFact)
    (space : List Atom)
    (nodup : space.Nodup)
    (rawWithin : RawExecFactsWithin allowedRaw space)
    (decodeClosed : ∀ {raw directive},
      raw ∈ allowedRaw → decodeSupportedSourceExec raw = some directive →
        directive ∈ allowedDirectives)
    (directiveKeys : KeyInjective allowedDirectives)
    (rawKeys : KeyInjective allowedRaw)
    (supportSet : ∀ directive ∈ allowedDirectives,
      ReflectiveSupportSetTemplate directive.rule.tmpl) :
    ReflectiveWorkQueueInvariant space := by
  have supportedWithin :=
    supportedSourceExecFactsWithin_of_rawExecFactsWithin allowedRaw
      allowedDirectives space rawWithin decodeClosed
  apply reflectiveWorkQueueInvariant_of_supportSet space nodup
  · intro left right leftMember rightMember keysEqual
    exact directiveKeys left right
      (supportedWithin left leftMember) (supportedWithin right rightMember)
      keysEqual
  · intro left right leftMember rightMember keysEqual
    exact rawKeys left right (rawWithin left leftMember)
      (rawWithin right rightMember) keysEqual
  · intro directive selected
    exact supportSet directive
      (supportedWithin directive (selectNextScheduled_mem selected))
  · intro raw directive selected decoded
    exact supportSet directive
      (decodeClosed (rawWithin raw (selectNextScheduled_mem selected)) decoded)

/-- A proof-relevant concrete execution trace carrying the exact realization
obligations at every nontrivial source state.  This is the strong boundary:
an executable list trace alone does not imply a path in authored
support-valued MM2 until these scheduler and matcher obligations are supplied. -/
inductive CReflectiveAdequateTrace (policy : UnsupportedExecPolicy) :
    Nat → List Atom → List Atom → Type where
  | refl : CReflectiveAdequateTrace policy fuel source source
  | step {fuel source middle target} :
      ReflectiveWorkQueueInvariant source →
      cReflectiveSourceWorkQueueStep policy source = some middle →
      CReflectiveAdequateTrace policy fuel middle target →
      CReflectiveAdequateTrace policy (fuel + 1) source target

/-- List states reachable by at most the stated number of computable
reflective steps. -/
inductive CReflectiveReachable (policy : UnsupportedExecPolicy) :
    Nat → List Atom → List Atom → Prop where
  | refl : CReflectiveReachable policy fuel space space
  | step {fuel source middle target} :
      cReflectiveSourceWorkQueueStep policy source = some middle →
      CReflectiveReachable policy fuel middle target →
      CReflectiveReachable policy (fuel + 1) source target

/-- Initial validity plus preservation proves the realization invariant at
every actually reachable state.  The induction follows the concrete
state-threaded execution evidence; it never reconstructs canonical phase
spaces. -/
theorem ReflectiveWorkQueueInvariant.of_reachable
    {policy : UnsupportedExecPolicy} {fuel : Nat}
    {source target : List Atom}
    (initial : ReflectiveWorkQueueInvariant source)
    (preserved : ReflectiveWorkQueueInvariantPreserved policy)
    (reachable : CReflectiveReachable policy fuel source target) :
    ReflectiveWorkQueueInvariant target := by
  induction reachable with
  | refl => exact initial
  | step moved _ induction =>
      exact induction (preserved initial moved)

/-- Every state-threaded path of the concrete reflective evaluator is finite
reachability in its executable realization GSLT. -/
theorem CReflectiveReachable.toMultiStep
    {policy : UnsupportedExecPolicy} {fuel : Nat}
    {source target : List Atom}
    (reachable : CReflectiveReachable policy fuel source target) :
    (reflectiveNativeListExecGSLT policy).MultiStep source target := by
  induction reachable with
  | refl => exact .refl _
  | step moved _ induction =>
      exact .step
        ((reflectiveNativeListExecGSLT_step_iff policy _ _).2 moved)
        induction

/-- Proof-relevant list execution trace.  Unlike `CReflectiveReachable`, this
evidence lives in `Type` and therefore retains every intermediate state and
step witness. -/
inductive CReflectiveTrace (policy : UnsupportedExecPolicy) :
    Nat → List Atom → List Atom → Type where
  | refl : CReflectiveTrace policy fuel source source
  | step {fuel source middle target} :
      cReflectiveSourceWorkQueueStep policy source = some middle →
      CReflectiveTrace policy fuel middle target →
      CReflectiveTrace policy (fuel + 1) source target

/-- A proof-relevant concrete path becomes an adequate trace when the
realization invariant is supplied at every reachable source state.  The input
must live in `Type`: proposition-valued reachability cannot be eliminated into
proof-relevant trace data. -/
def CReflectiveTrace.toAdequateTrace
    {policy : UnsupportedExecPolicy} {fuel : Nat}
    {source target : List Atom}
    (trace : CReflectiveTrace policy fuel source target)
    (invariant : ∀ residual,
      CReflectiveReachable policy fuel source residual →
      ReflectiveWorkQueueInvariant residual) :
    CReflectiveAdequateTrace policy fuel source target :=
  match trace with
  | .refl => .refl
  | .step moved tail =>
      .step (invariant _ .refl) moved
        (tail.toAdequateTrace (fun residual residualReachable =>
          invariant residual (.step moved residualReachable)))

/-- Every proof-relevant concrete trace is a rewrite path in the executable
realization GSLT, retaining the same intermediate list states. -/
def CReflectiveTrace.toRewritePath
    {policy : UnsupportedExecPolicy} {fuel : Nat}
    {source target : List Atom}
    (trace : CReflectiveTrace policy fuel source target) :
    (reflectiveNativeListExecGSLT policy).RewritePath source target :=
  match trace with
  | .refl => .nil _
  | .step moved tail =>
      .cons
        ((reflectiveNativeListExecGSLT_step_iff policy _ _).2 moved)
        tail.toRewritePath

/-- The exact-fuel evaluator constructs one proof-relevant trace to the
returned state. -/
def cReflectiveSourceWorkQueueRunN_trace
    (policy : UnsupportedExecPolicy) (fuel : Nat) (source : List Atom) :
    CReflectiveTrace policy fuel source
      (cReflectiveSourceWorkQueueRunN policy fuel source).1 := by
  induction fuel generalizing source with
  | zero => exact .refl
  | succ fuel induction =>
      simp only [cReflectiveSourceWorkQueueRunN]
      cases moved : cReflectiveSourceWorkQueueStep policy source with
      | none => exact .refl
      | some next => exact .step moved (induction next)

/-- The concrete evaluator produces an authored-adequate trace as soon as
the caller proves the realization invariant for every state reachable within
the chosen bound. -/
def cReflectiveSourceWorkQueueRunN_adequateTrace
    (policy : UnsupportedExecPolicy) (fuel : Nat) (source : List Atom)
    (invariant : ∀ residual,
      CReflectiveReachable policy fuel source residual →
      ReflectiveWorkQueueInvariant residual) :
    CReflectiveAdequateTrace policy fuel source
      (cReflectiveSourceWorkQueueRunN policy fuel source).1 :=
  (cReflectiveSourceWorkQueueRunN_trace policy fuel source).toAdequateTrace
    invariant

/-- A globally invariant-preserving executable MM2 profile automatically
produces an authored-adequate proof-relevant trace for every bounded run. -/
def cReflectiveSourceWorkQueueRunN_adequateTrace_of_preserved
    (policy : UnsupportedExecPolicy) (fuel : Nat) (source : List Atom)
    (initial : ReflectiveWorkQueueInvariant source)
    (preserved : ReflectiveWorkQueueInvariantPreserved policy) :
    CReflectiveAdequateTrace policy fuel source
      (cReflectiveSourceWorkQueueRunN policy fuel source).1 :=
  cReflectiveSourceWorkQueueRunN_adequateTrace policy fuel source
    (fun _ reachable => initial.of_reachable preserved reachable)

/-- The exact-fuel evaluator therefore returns along a proof-relevant path in
the executable realization GSLT. -/
def cReflectiveSourceWorkQueueRunN_rewritePath
    (policy : UnsupportedExecPolicy) (fuel : Nat) (source : List Atom) :
    (reflectiveNativeListExecGSLT policy).RewritePath source
      (cReflectiveSourceWorkQueueRunN policy fuel source).1 :=
  (cReflectiveSourceWorkQueueRunN_trace policy fuel source).toRewritePath

/-- Bounded computable reflective execution has exactly the same final finite
support and step count as the existing MM2 semantics. -/
theorem cReflectiveSourceWorkQueueRunN_toFinset
    (policy : UnsupportedExecPolicy) (fuel : Nat) (space : List Atom)
    (invariant : ∀ residual,
      CReflectiveReachable policy fuel space residual →
      ReflectiveWorkQueueInvariant residual) :
    (cReflectiveSourceWorkQueueRunN policy fuel space).1.toFinset =
        (reflectiveSourceWorkQueueRunN policy fuel space.toFinset).1 ∧
      (cReflectiveSourceWorkQueueRunN policy fuel space).2 =
        (reflectiveSourceWorkQueueRunN policy fuel space.toFinset).2 := by
  induction fuel generalizing space with
  | zero => simp [cReflectiveSourceWorkQueueRunN,
      reflectiveSourceWorkQueueRunN]
  | succ fuel induction =>
      simp only [cReflectiveSourceWorkQueueRunN,
        reflectiveSourceWorkQueueRunN]
      have current := invariant space .refl
      have stepAgreement := cReflectiveSourceWorkQueueStep_toFinset policy
        space current.nodup current.supportedKeyInj current.rawKeyInj
        current.supportedAgreement current.rawAgreement
      cases nativeStep : cReflectiveSourceWorkQueueStep policy space with
      | none =>
          simp only [nativeStep] at stepAgreement
          simp only [Option.map] at stepAgreement ⊢
          rw [← stepAgreement]
          exact ⟨rfl, rfl⟩
      | some next =>
          simp only [nativeStep, Option.map] at stepAgreement
          have semanticStep :
              reflectiveSourceWorkQueueStep policy space.toFinset =
                some next.toFinset := by
            rw [← stepAgreement]
          simp only [semanticStep]
          have nextInvariant : ∀ residual,
              CReflectiveReachable policy fuel next residual →
              ReflectiveWorkQueueInvariant residual :=
            fun residual reachable =>
              invariant residual (.step nativeStep reachable)
          obtain ⟨supportAgreement, countAgreement⟩ :=
            induction next nextInvariant
          exact ⟨supportAgreement, congrArg (· + 1) countAgreement⟩

/-- Reflective MM2 is an existing work-queue family member, not an
intermediate language. -/
noncomputable def reflectiveSourceExecProfile
    (policy : UnsupportedExecPolicy) : ExecutionProfile where
  step := reflectiveSourceWorkQueueStep policy

noncomputable def reflectiveSourceExecGSLT
    (policy : UnsupportedExecPolicy) : GSLT :=
  (reflectiveSourceExecProfile policy).toGSLT

@[simp] theorem reflectiveSourceExecGSLT_step_iff
    (policy : UnsupportedExecPolicy) (source target : Space) :
    (reflectiveSourceExecGSLT policy).Step source target ↔
      reflectiveSourceWorkQueueStep policy source = some target :=
  Iff.rfl

/-- An invariant-carrying concrete trace is a proof-relevant rewrite path in
the authored support-valued reflective MM2 GSLT. -/
def CReflectiveAdequateTrace.toSupportRewritePath
    {policy : UnsupportedExecPolicy} {fuel : Nat}
    {source target : List Atom}
    (trace : CReflectiveAdequateTrace policy fuel source target) :
    (reflectiveSourceExecGSLT policy).RewritePath source.toFinset
      target.toFinset :=
  match trace with
  | .refl => .nil _
  | .step invariant moved tail =>
      let agreement := cReflectiveSourceWorkQueueStep_toFinset policy source
        invariant.nodup invariant.supportedKeyInj invariant.rawKeyInj
        invariant.supportedAgreement invariant.rawAgreement
      .cons
        ((reflectiveSourceExecGSLT_step_iff policy _ _).2 (by
          simpa only [moved, Option.map] using agreement.symm))
        tail.toSupportRewritePath

/-- The reflective profile remains deterministic: byte capture changes
template instantiation, not scheduler choice. -/
theorem reflectiveSourceExecGSLT_step_deterministic
    (policy : UnsupportedExecPolicy) {source left right : Space}
    (leftStep : (reflectiveSourceExecGSLT policy).Step source left)
    (rightStep : (reflectiveSourceExecGSLT policy).Step source right) :
    left = right :=
  (reflectiveSourceExecProfile policy).step_deterministic leftStep rightStep

/-! ## Proof-relevant target presentation -/

/-- One selected supported MM2 directive and the exact successor obtained
with expression-local code capture. -/
structure ReflectiveScheduledEvent (source target : Space) : Type where
  directive : SourceExecFact
  selected :
    selectNextScheduled (supportedSourceExecFactsOfSpace source) =
      some directive
  fired : fireReflectiveSourceExecFact source directive = target

theorem reflectiveScheduledEvent_nonempty_iff_step
    (source target : Space) :
    Nonempty (ReflectiveScheduledEvent source target) ↔
      (reflectiveSourceExecGSLT .leaveInert).Step source target := by
  rw [reflectiveSourceExecGSLT_step_iff]
  constructor
  · rintro ⟨event⟩
    simp [reflectiveSourceWorkQueueStep, event.selected, event.fired]
  · intro step
    unfold reflectiveSourceWorkQueueStep at step
    cases selected :
        selectNextScheduled (supportedSourceExecFactsOfSpace source) with
    | none =>
        simp [selected] at step
    | some directive =>
        simp [selected] at step
        exact ⟨⟨directive, selected, step⟩⟩

/-- Proof-relevant presentation of the ordinary MM2 execution profile used
by compilers that may stage executable rules as data. -/
noncomputable def reflectiveStepEvidence :
    StepEvidence (reflectiveSourceExecGSLT .leaveInert) where
  Evidence := ReflectiveScheduledEvent
  erases_iff := reflectiveScheduledEvent_nonempty_iff_step

noncomputable def reflectivePresented : ProofRelevantGSLT :=
  { theory := reflectiveSourceExecGSLT .leaveInert
    steps := reflectiveStepEvidence }

/-- A selected directive yields its exact proof-relevant event. -/
def reflectiveEventOfSelected {source : Space} {directive : SourceExecFact}
    (selected :
      selectNextScheduled (supportedSourceExecFactsOfSpace source) =
        some directive) :
    ReflectiveScheduledEvent source
      (fireReflectiveSourceExecFact source directive) :=
  { directive
    selected
    fired := rfl }

/-- No target event can be invented when the supported queue is empty. -/
theorem no_reflective_event_of_no_supported
    {source target : Space}
    (empty :
      selectNextScheduled (supportedSourceExecFactsOfSpace source) = none) :
    IsEmpty (ReflectiveScheduledEvent source target) := by
  constructor
  intro event
  have selected := event.selected
  rw [empty] at selected
  contradiction

/-! ## Positive and negative controls -/

private def capturedPattern : Atom :=
  .expression
    [.symbol ",", .expression [.symbol "task", .var "inner"]]

private def capturedTemplate : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+",
        .expression [.symbol "done", .var "inner"]]]

private def captureSubstitution : Subst :=
  [("patterns", capturedPattern), ("templates", capturedTemplate)]

private def stagedExecTemplate : Atom :=
  .expression
    [.symbol "exec", .expression [.symbol "1", .symbol "next"],
      .var "patterns", .var "templates"]

/-- A standard staged exec is closed at the outer level even though its
captured pattern and template contain their own variables. -/
theorem captured_exec_is_covered :
    templateCovered captureSubstitution stagedExecTemplate = true := by
  decide +kernel

/-- The older structural-groundness test rejects the same lawful captured
code value, exposing the exact strict extension supplied here. -/
theorem captured_exec_is_not_structurally_ground :
    isGroundAtom (applySubst captureSubstitution stagedExecTemplate) = false := by
  decide +kernel

/-- Reflective instantiation retains the captured executable rule exactly. -/
theorem captured_exec_instantiates :
    instantiateTemplateAtom? captureSubstitution stagedExecTemplate =
      some
        (.expression
          [.symbol "exec", .expression [.symbol "1", .symbol "next"],
            capturedPattern, capturedTemplate]) := by
  decide +kernel

/-- The reflective sink inserts the complete captured executable expression,
including its expression-local variables. -/
theorem captured_exec_sink_stages_exactly :
    stageReflectiveSupportSink (.add stagedExecTemplate) []
      captureSubstitution =
      [.expression
        [.symbol "exec", .expression [.symbol "1", .symbol "next"],
          capturedPattern, capturedTemplate]] := by
  decide +kernel

/-- A genuinely unbound outer template variable is still rejected. -/
theorem unbound_output_variable_rejected :
    instantiateTemplateAtom? []
      (.expression [.symbol "result", .var "missing"]) = none := by
  decide +kernel

#print axioms captured_exec_is_covered
#print axioms instantiateTemplateAtom?_var_eq_some_iff
#print axioms templateCovered_lookup_of_mem_freeVars
#print axioms captured_exec_is_not_structurally_ground
#print axioms captured_exec_instantiates
#print axioms captured_exec_sink_stages_exactly
#print axioms unbound_output_variable_rejected
#print axioms stageReflectiveSupportSink_eq_stageSupportSink_of_ground
#print axioms reflectiveSourceExecGSLT_step_deterministic
#print axioms reflectiveScheduledEvent_nonempty_iff_step
#print axioms no_reflective_event_of_no_supported
#print axioms selectNextScheduled_mem
#print axioms insertSupport_nodup
#print axioms cApplyReflectiveTemplate_nodup
#print axioms cFireReflectiveSourceExecFact_nodup
#print axioms mem_cApplyReflectiveTemplate_of_supportSet
#print axioms cApplyReflectiveTemplate_atomsWithin
#print axioms cFireReflectiveSourceExecFact_atomsWithin
#print axioms cFireReflectiveSourceExecFact_capturedAtomsWithin
#print axioms RawExecFactsWithin.atom
#print axioms supportedSourceExecFactsWithin_of_rawExecFactsWithin
#print axioms reflectiveWorkQueueInvariant_of_ruleInventory
#print axioms cFireReflectiveSourceExecFact_rawExecFactsWithin
#print axioms reflectiveSourceRowSupportAlignment_of_nodup
#print axioms applyReflectiveSinkBatch_eq_of_rows_toFinset_eq
#print axioms reflectiveWorkQueueInvariant_of_supportSet
#print axioms ReflectiveWorkQueueInvariant.of_reachable
#print axioms CReflectiveTrace.toAdequateTrace
#print axioms cReflectiveSourceWorkQueueRunN_adequateTrace
#print axioms cReflectiveSourceWorkQueueRunN_adequateTrace_of_preserved

end Mettapedia.Languages.ProcessCalculi.MORK
