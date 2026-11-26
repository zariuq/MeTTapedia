import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaExecution
import Mettapedia.Languages.MeTTa.SpaceTheory.ModuleTheories
import Mettapedia.Languages.MeTTa.SpaceTheory.ModuleReferences
import Mettapedia.Languages.MeTTa.SpaceTheory.EffectfulModules
import Mettapedia.Machines.OrderedDependencyIds

/-!
# Linked and local PeTTa module extensions

The provided command source executes an included program in its
destination. A linked extension instead adds an existing instance to
the declaration view. The ordinary PeTTa rule still executes against
the actual store: installing a link does not write the destination or
replace the arguments, effects or continuation of an evaluator step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaModuleModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay
open Mettapedia.Languages.MeTTa.PeTTa.NamedSpaces (Handle Store)
open Mettapedia.GSLT (GSLT)
open Mettapedia.GSLT.IndexedOperational (OperationalTranslation)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Mettapedia.Machines.OrderedDependencyIds (insertDeps mem_insertDeps nodup_insertDeps)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic (SState)
open ModuleReferences (Reference)
open PeTTaExecution (programAt theoryAt)

/-- The flattened dependency scope of the current module. The receiver
is read separately, and repeated dependency paths do not duplicate an
instance. A reference under a different spelling can still read it. -/
structure Scope where
  dependencies : List Handle
  noSelf : .self ∉ dependencies
  distinct : dependencies.Nodup

def Scope.empty : Scope := ⟨[], by simp, .nil⟩

theorem Scope.ext {first second : Scope} (same : first.dependencies = second.dependencies) : first = second := by
  cases first
  cases second
  cases same
  rfl

def Scope.link (receiver : Scope) (provider : Handle) (external : provider ≠ .self) (transitive : Scope) : Scope where
  dependencies := insertDeps receiver.dependencies (provider :: transitive.dependencies)
  noSelf := by
    intro member
    rcases mem_insertDeps.mp member with existing | supplied
    · exact receiver.noSelf existing
    · rcases List.mem_cons.mp supplied with rfl | inherited
      · exact external rfl
      · exact transitive.noSelf inherited
  distinct := nodup_insertDeps _ receiver.distinct

theorem link_members (receiver : Scope) (provider : Handle) (external : provider ≠ .self)
    (transitive : Scope) (module : Handle) :
    module ∈ (receiver.link provider external transitive).dependencies ↔
      module ∈ receiver.dependencies ∨ module = provider ∨ module ∈ transitive.dependencies := by
  simp only [Scope.link, mem_insertDeps, List.mem_cons]

theorem link_twice (receiver : Scope) (provider : Handle) (external : provider ≠ .self) (transitive : Scope) :
    (receiver.link provider external transitive).link provider external transitive =
      receiver.link provider external transitive := by
  have same := Mettapedia.Machines.OrderedDependencyIds.insertDeps_insertDeps_self
    receiver.dependencies (provider :: transitive.dependencies)
  exact Scope.ext same

theorem dependency_seen_once (scope : Scope) {provider : Handle} (linked : provider ∈ scope.dependencies) :
    scope.dependencies.count provider = 1 := by
  have upper := (List.nodup_iff_count_le_one.mp scope.distinct) provider
  have lower := List.count_pos_iff.mpr linked
  omega

def linkedAtoms (whereabouts : Scope) (current : Effects.State) : Option (List Atom) := do
  let owned ← whereabouts.dependencies.mapM current.read
  pure (current.core ++ owned.flatten)

/-- Inversion of the ordered reading of linked instances. A missing
instance cannot be replaced by an empty module. -/
theorem linkedAtoms_exact (whereabouts : Scope) (current : Effects.State) (visible : List Atom) :
    linkedAtoms whereabouts current = some visible ↔
      ∃ linked, List.Forall₂ (fun handle atoms => current.read handle = some atoms) whereabouts.dependencies linked ∧
        visible = current.core ++ linked.flatten := by
  unfold linkedAtoms
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
  constructor
  · rintro ⟨linked, reads, rfl⟩
    exact ⟨linked, Mettapedia.Data.List.option_mapM_forall₂ _ _ _ reads, rfl⟩
  · rintro ⟨linked, reads, rfl⟩
    refine ⟨linked, ?_, rfl⟩
    have collected : ∀ (handles : List Handle) (blocks : List (List Atom)),
        List.Forall₂ (fun handle atoms => current.read handle = some atoms) handles blocks →
        handles.mapM current.read = some blocks := by
      intro handles blocks supplied
      induction supplied with
      | nil => rfl
      | cons first _ ih => simp [List.mapM_cons, first, ih]
    exact collected _ _ reads

theorem visible_member {scope : Scope} {store : Effects.State} {visible : List Atom}
    (seen : linkedAtoms scope store = some visible) (atom : Atom) :
    atom ∈ visible ↔ atom ∈ store.core ∨
      ∃ module ∈ scope.dependencies, ∃ atoms, store.read module = some atoms ∧ atom ∈ atoms := by
  obtain ⟨values, supplied, rfl⟩ := (linkedAtoms_exact scope store visible).mp seen
  have imports {handles : List Handle} {values : List (List Atom)}
      (paired : List.Forall₂ (fun module atoms => store.read module = some atoms) handles values) :
      atom ∈ values.flatten ↔ ∃ module ∈ handles, ∃ read, store.read module = some read ∧ atom ∈ read := by
    induction paired with
    | nil => simp
    | @cons handle atoms handles values first _ rest =>
      simp only [List.flatten_cons, List.mem_append, rest, List.mem_cons]
      constructor
      · rintro (head | ⟨other, member, payload, found, contained⟩)
        · exact ⟨handle, Or.inl rfl, atoms, first, head⟩
        · exact ⟨other, Or.inr member, payload, found, contained⟩
      · rintro ⟨module, rfl | later, payload, read, present⟩
        · have agrees := Option.some.inj (first.symm.trans read)
          exact Or.inl (agrees ▸ present)
        · exact Or.inr ⟨module, later, payload, read, present⟩
  exact List.mem_append.trans (or_congr_right (imports supplied))

def Transition (scope : Scope) (before after : Eval.Configuration) : Prop :=
  ∃ declarations, linkedAtoms scope before.state = some declarations ∧ (theoryAt declarations).Step before after

def theory (scope : Scope) : GSLT := equalityGSLT Eval.Configuration (Transition scope)

theorem step_iff (scope : Scope) (before after : Eval.Configuration) :
    (theory scope).Step before after ↔
      ∃ declarations, linkedAtoms scope before.state = some declarations ∧
        Eval.step (programAt declarations) before = some after := by
  change Transition scope before after ↔ _
  unfold Transition theoryAt
  simp only [Eval.theory_step_iff]

/-- With no links the extension is exactly original live PeTTa, not
a language in which imported definitions are a separate evaluator. -/
theorem empty_is_live (before after : Eval.Configuration) :
    (theory .empty).Step before after ↔ LiveRegistry.theory.Step before after := by
  have own : linkedAtoms Scope.empty before.state = some before.state.core := by
    simp [linkedAtoms, Scope.empty]
  change (∃ declarations, linkedAtoms Scope.empty before.state = some declarations ∧
    (theoryAt declarations).Step before after) ↔ _
  rw [own, PeTTaExecution.live_rewrite_iff]
  constructor
  · rintro ⟨_, eq, step⟩; exact (Option.some.inj eq).symm ▸ step
  · exact fun step => ⟨_, rfl, step⟩

/-- The linked view only interprets program questions. At a snapshot the
existing Transform program for those declarations realizes the same step
in the actual caller configuration, including its world and effects. -/
theorem step_on_transform_iff {O : Type} [DecidableEq O] [Infinite O]
    (scope : Scope) (before after : Eval.Configuration) {start : SState O}
    (shown : EvalOnTheStep.Shows before start) :
    (theory scope).Step before after ↔
      ∃ declarations, linkedAtoms scope before.state = some declarations ∧
        ∃ final, (EvalOnTheStep.stepSystem O (programAt declarations)).Step start final ∧
          EvalOnTheStep.Shows after final := by
  change Transition scope before after ↔ _
  constructor
  · rintro ⟨atoms, seen, step⟩
    exact ⟨atoms, seen, PeTTaExecution.snapshot_step_on_transform atoms shown step⟩
  · rintro ⟨atoms, seen, final, fired, result⟩
    obtain ⟨actual, step, reached⟩ := PeTTaExecution.snapshot_reflect_transform_step atoms shown fired
    have same := EvalOnTheStep.shows_unique reached result
    exact ⟨atoms, seen, same ▸ step⟩

def importMap (base : Atom → Atom → Prop) (scope : Scope) (store : Effects.State) {visible : List Atom}
    (seen : linkedAtoms scope store = some visible) :
    OperationalTranslation (ModuleTheories.theory base store.core) (ModuleTheories.theory base visible) :=
  ModuleTheories.inclusion base (by
    obtain ⟨imported, _, rfl⟩ := (linkedAtoms_exact scope store visible).mp seen
    exact List.subset_append_left _ _)

def providerMap (base : Atom → Atom → Prop) {scope : Scope} {store : Effects.State}
    {provider : Handle} (linked : provider ∈ scope.dependencies) {atoms visible : List Atom}
    (supplied : store.read provider = some atoms) (seen : linkedAtoms scope store = some visible) :
    OperationalTranslation (ModuleTheories.theory base atoms) (ModuleTheories.theory base visible) :=
  ModuleTheories.inclusion base (fun {a} present =>
    (visible_member seen a).mpr (Or.inr ⟨provider, linked, atoms, supplied, present⟩))

/-- The literal part of an include transfers its atoms into the current
destination; unlike linking, this creates locally owned occurrences.
Effectful provided programs use the existing command semantics instead
of this literal block operation. -/
def includeAtoms (current : Effects.State) (destination : Handle) (contributed : List Atom) :
    Option Effects.State := do
  let previous ← current.read destination
  current.write destination (previous ++ contributed)

theorem include_readback {current reached : Effects.State} {destination : Handle}
    {previous contributed : List Atom} (source : current.read destination = some previous)
    (included : includeAtoms current destination contributed = some reached) :
    reached.read destination = some (previous ++ contributed) := by
  apply Store.write_reads_back current destination _ reached
  simpa only [includeAtoms, source, bind, Option.bind_some] using included

theorem include_keeps_other_space {current reached : Effects.State} {destination other : Handle}
    {previous contributed : List Atom} (source : current.read destination = some previous)
    (included : includeAtoms current destination contributed = some reached) (separate : other ≠ destination) :
    reached.read other = current.read other := by
  apply Store.write_read_other current destination other (previous ++ contributed) reached _ separate
  simpa only [includeAtoms, source, bind, Option.bind_some] using included

def includeMap (base : Atom → Atom → Prop) (before contributed : List Atom) :
    OperationalTranslation (ModuleTheories.theory base contributed)
      (ModuleTheories.theory base (before ++ contributed)) :=
  ModuleTheories.inclusion base (List.subset_append_right _ _)

def instantiate (current : Effects.State) (initial : List Atom) : Reference Handle × Effects.State :=
  let allocation := current.allocate initial
  (Reference.named allocation.1, allocation.2)

theorem fresh_instance_reads_initial (current : Effects.State) (initial : List Atom) :
    (instantiate current initial).1.read (instantiate current initial).2.read = some initial := by
  simp only [instantiate, ModuleReferences.named_reads_original, Store.allocation_reads_empty]

theorem instantiation_keeps_live_references (current : Effects.State) (initial : List Atom)
    (reference : Reference Handle) (already : ∃ atoms, current.read reference.instanceId = some atoms) :
    reference.read (instantiate current initial).2.read = reference.read current.read := by
  obtain ⟨atoms, present⟩ := already
  have separate : reference.instanceId ≠ (current.allocate initial).1 := by
    intro equal
    rw [equal] at present
    change current.read (.privateSpace current.next) = some atoms at present
    rw [Store.read_unallocated current current.next (Nat.le_refl _)] at present
    cases present
  unfold Reference.read instantiate
  exact congrArg (Option.map (List.map (Renaming.atom reference.names)))
    (Store.allocation_read_existing current initial reference.instanceId separate)

theorem reference_follows_write {before after : Effects.State} (reference : Reference Handle)
    (written : List Atom) (update : before.write reference.instanceId written = some after) :
    reference.read after.read = some (written.map (Renaming.atom reference.names)) := by
  simp only [Reference.read, Store.write_reads_back _ _ _ _ update, Option.map_some]

/-- Loading uses the provider's identity and the module's own destination,
not the caller's choice of its printed names. -/
def initializationKey (declaredName : Atom) (view : Reference Handle) : EffectfulModules.Instance :=
  ⟨view.instanceId, declaredName⟩

theorem rename_keeps_initialization_key (declaredName : Atom) (view : Reference Handle)
    (names : Equiv.Perm String) :
    initializationKey declaredName (view.rename names) = initializationKey declaredName view := rfl

theorem rename_does_not_run_initializer_again
    {settings : MeTTaAuthoredProgramExecution.ProgramExecution.Settings}
    {before after : EffectfulModules.Acquisitions}
    (declaredName : Atom) (view : Reference Handle) (names : Equiv.Perm String)
    (loaded : EffectfulModules.Once settings (initializationKey declaredName view) before after)
    (later : EffectfulModules.Acquisitions) :
    EffectfulModules.Once settings (initializationKey declaredName (view.rename names)) after later ↔
      later = after := by
  rw [rename_keeps_initialization_key]
  exact EffectfulModules.repeat_after_success loaded later

theorem freshly_instantiated_key_is_separate (current : Effects.State) (initial : List Atom)
    (declaredName : Atom) (view : Reference Handle)
    (loaded : ∃ content, current.read view.instanceId = some content) :
    initializationKey declaredName (instantiate current initial).1 ≠ initializationKey declaredName view := by
  intro same
  have sameHome := congrArg EffectfulModules.Instance.destination same
  change Handle.privateSpace current.next = view.instanceId at sameHome
  obtain ⟨_, read⟩ := loaded
  rw [← sameHome, Store.read_unallocated current current.next (Nat.le_refl _)] at read
  cases read

section Controls

private def definition (answer : String) : Atom :=
  .expression [.symbol "=", .expression [.symbol "weather"], .symbol answer]
private def provider : Handle := (Effects.empty.allocate [definition "Cold"]).1
private def started : Effects.State := (Effects.empty.allocate [definition "Cold"]).2
private def links : Scope := Scope.empty.link provider (by decide +kernel) Scope.empty
private def copied : Effects.State := (includeAtoms started .self [definition "Cold"]).getD started
private def updated (store : Effects.State) : Effects.State :=
  (store.write provider [definition "Warm"]).getD store
private def ready (store : Effects.State) : Eval.Configuration :=
  { state := store, control := .arguments [] (.function "weather") [] [] 0 }
private def captured (store : Effects.State) (answer : String) : Eval.Configuration :=
  { ready store with control := .sequence [.evaluate [] (.symbol answer)] [] }

private theorem weather_clause (store : Effects.State) (answer : String) :
    Eval.step (programAt [definition answer]) (ready store) = some (captured store answer) := by
  have ordinary : Eval.ioHead "weather" = false := by decide +kernel
  have userDefined : StdLib.known "weather" = false := by decide +kernel
  have saturated : ([] : List Atom).length ∈ Eval.arities (programAt [definition answer]) "weather" := by
    rw [PeTTaExecution.programAt_exact]
    change (0 : Nat) ∈ [0]
    simp
  simp only [Eval.step, ready, captured, ordinary, userDefined, Bool.false_eq_true, ↓reduceIte]
  rw [Eval.application_saturated saturated, PeTTaExecution.programAt_exact]
  have indexed : (SpaceSemantics.index [definition answer]).equations =
      [⟨"weather", [], .symbol answer⟩] := rfl
  simp only [Eval.clauses, indexed, List.filterMap_cons, List.filterMap_nil,
    ↓reduceIte, SpaceSemantics.matchValue.matchValues, Option.map_some]

theorem linked_call_sees_edit_but_local_call_keeps_copy :
    (theory links).Step (ready (updated started)) (captured (updated started) "Warm") ∧
      (theory .empty).Step (ready (updated copied)) (captured (updated copied) "Cold") := by
  constructor
  · exact (step_iff links _ _).mpr ⟨[definition "Warm"], by decide +kernel, weather_clause _ _⟩
  · exact (step_iff .empty _ _).mpr ⟨[definition "Cold"], by decide +kernel, weather_clause _ _⟩

theorem linking_does_not_copy_into_self :
    (updated started).read .self = some [] ∧ (updated copied).read .self = some [definition "Cold"] := by
  decide +kernel

theorem rename_shares_a_live_instance_and_fresh_instance_does_not :
    let fresh := instantiate started [definition "Cold"]
    let now := updated fresh.2
    let first := Reference.named provider
    let renamed := first.rename (Equiv.swap "weather" "forecast")
    first.read now.read = some [definition "Warm"] ∧
      renamed.read now.read = some [.expression [.symbol "=", .expression [.symbol "forecast"], .symbol "Warm"]] ∧
      fresh.1.read now.read = some [definition "Cold"] := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaModuleModes
