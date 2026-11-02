import Mettapedia.GSLT.LanguageDef.ExecutableProtocol

/-!
# Protocol trace and ownership safety

An admitted source produces a trace of enabled operations. Each operation
records the facts and owners that authorized it; its successor context records
the actual Boolean branch. Returns discharge every owner, including raised,
suspended and failure returns. An exhausted test reply tape retains its
current owners instead of fabricating a successful return.

These are symbolic ownership obligations. A host must separately realize the
declared acquire, release and transfer operations and the meaning of facts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ExecutableProtocol

theorem findHook_spec {p : Protocol} {id : String} {hook : Hook}
    (found : findHook p id = some hook) : hook ∈ p.hooks ∧ hook.id = id := by
  exact ⟨List.mem_of_find?_eq_some found, by
    simpa using List.find?_some found⟩

theorem findResource_spec {p : Protocol} {id : String} {resource : Resource}
    (found : findResource p id = some resource) :
    resource ∈ p.resources ∧ resource.id = id := by
  exact ⟨List.mem_of_find?_eq_some found, by
    simpa using List.find?_some found⟩

theorem MetadataValid.hook_cName_injective {p : Protocol} (valid : MetadataValid p)
    {first second : Hook} (hfirst : first ∈ p.hooks) (hsecond : second ∈ p.hooks)
    (same : first.cName = second.cName) : first = second := by
  have nodup : (p.hooks.map Hook.cName).Nodup :=
    List.Nodup.of_append_left valid.calls
  exact List.inj_on_of_nodup_map nodup hfirst hsecond same

theorem MetadataValid.hook_resource_disjoint {p : Protocol} (valid : MetadataValid p)
    {hook : Hook} (hhook : hook ∈ p.hooks) {resource : Resource}
    (hresource : resource ∈ p.resources) {name : String}
    (hname : name ∈ [resource.acquire, resource.release, resource.transfer]) :
    hook.cName ≠ name := by
  have disjoint := (List.nodup_append.mp valid.calls).2.2
  exact disjoint hook.cName (List.mem_map.mpr ⟨hook, hhook, rfl⟩) name
    (List.mem_flatMap.mpr ⟨resource, hresource, hname⟩)

/-- One enabled source operation, observed as its actual named C call. -/
inductive Enabled (p : Protocol) : Context → Event → Context → Prop where
  | call (c : Context) (id : String) (hook : Hook) (reply : Bool)
      (declared : findHook p id = some hook)
      (facts : ∀ fact ∈ hook.requires, fact ∈ c.facts)
      (owners : ∀ resource ∈ hook.uses, resource ∈ c.owned) :
      Enabled p c (.boolean hook.cName reply) (callContext c hook reply)
  | acquire (c : Context) (id : String) (resource : Resource) (reply : Bool)
      (declared : findResource p id = some resource) (fresh : id ∉ c.owned)
      (facts : ∀ fact ∈ resource.acquireRequires, fact ∈ c.facts) :
      Enabled p c (.boolean resource.acquire reply) (acquireContext c id reply)
  | release (c : Context) (id : String) (resource : Resource)
      (declared : findResource p id = some resource) (owned : id ∈ c.owned) :
      Enabled p c (.void resource.release) (disposeContext c id)
  | transfer (c : Context) (id : String) (resource : Resource)
      (declared : findResource p id = some resource) (owned : id ∈ c.owned)
      (facts : ∀ fact ∈ resource.transferRequires, fact ∈ c.facts) :
      Enabled p c (.void resource.transfer) (transferContext c id)

/-- Ordered occurrences are retained; this is not a set of called hooks. -/
inductive Trace (p : Protocol) : Context → List Event → Context → Prop where
  | nil (c : Context) : Trace p c [] c
  | cons {first middle last : Context} {event : Event} {rest : List Event}
      (enabled : Enabled p first event middle) (after : Trace p middle rest last) :
      Trace p first (event :: rest) last

inductive SafeStop (p : Protocol) (c : Context) : Status → Prop where
  | returned (outcome : Outcome) (empty : c.owned = [])
      (decline : outcome = .declined → c.irreversible = false)
      (facts : ∀ fact ∈ exitRequires p outcome, fact ∈ c.facts) :
      SafeStop p c (.returned outcome)
  | noReply (name : String) : SafeStop p c (.noReply name)

theorem Enabled.owned_nodup {p : Protocol} {first last : Context} {event : Event}
    (enabled : Enabled p first event last) (unique : first.owned.Nodup) :
    last.owned.Nodup := by
  cases enabled with
  | call id hook reply => exact unique
  | acquire id resource reply declared fresh =>
      cases reply with
      | false => exact unique
      | true => exact List.nodup_cons.mpr ⟨fresh, unique⟩
  | release id resource => exact unique.erase id
  | transfer id resource => exact unique.erase id

/-- A certificate may be kept across every hook only if none invalidates it. -/
def StableFact (p : Protocol) (fact : String) : Prop :=
  ∀ hook ∈ p.hooks, fact ∉ hook.invalidates

theorem callContext_mem (c : Context) (hook : Hook) (reply : Bool) (fact : String) :
    fact ∈ (callContext c hook reply).facts ↔
      (reply = true ∧ fact ∈ hook.proves) ∨
      (fact ∈ c.facts ∧ fact ∉ hook.invalidates) := by
  cases reply <;> simp [callContext]

theorem callContext_invalidated (c : Context) (hook : Hook) (reply : Bool) (fact : String)
    (invalidated : fact ∈ hook.invalidates)
    (notReproved : reply = true → fact ∉ hook.proves) :
    fact ∉ (callContext c hook reply).facts := by
  rw [callContext_mem]
  rintro (⟨yes, proved⟩ | ⟨_, survived⟩)
  · exact notReproved yes proved
  · exact survived invalidated

theorem Enabled.facts_preserved {p : Protocol} {first last : Context} {event : Event}
    (enabled : Enabled p first event last) {fact : String} (stable : StableFact p fact)
    (known : fact ∈ first.facts) : fact ∈ last.facts := by
  cases enabled with
  | call id hook reply declared =>
      exact (callContext_mem _ _ _ _).mpr
        (Or.inr ⟨known, stable hook (findHook_spec declared).1⟩)
  | acquire id resource reply => cases reply <;> exact known
  | release => exact known
  | transfer => exact known

theorem Enabled.irreversible_mono {p : Protocol} {first last : Context} {event : Event}
    (enabled : Enabled p first event last) (effect : first.irreversible = true) :
    last.irreversible = true := by
  cases enabled with
  | call => simp [callContext, effect]
  | acquire id resource reply => cases reply <;> exact effect
  | release => exact effect
  | transfer => rfl

theorem Trace.owned_nodup {p : Protocol} {first last : Context} {calls : List Event}
    (trace : Trace p first calls last) (unique : first.owned.Nodup) : last.owned.Nodup := by
  induction trace with
  | nil => exact unique
  | cons enabled after ih => exact ih (enabled.owned_nodup unique)

theorem Trace.facts_preserved {p : Protocol} {first last : Context} {calls : List Event}
    (trace : Trace p first calls last) {fact : String} (stable : StableFact p fact)
    (known : fact ∈ first.facts) : fact ∈ last.facts := by
  induction trace with
  | nil => exact known
  | cons enabled after ih =>
      exact ih (enabled.facts_preserved stable known)

theorem Trace.irreversible_mono {p : Protocol} {first last : Context} {calls : List Event}
    (trace : Trace p first calls last) (effect : first.irreversible = true) :
    last.irreversible = true := by
  induction trace with
  | nil => exact effect
  | cons enabled after ih => exact ih (enabled.irreversible_mono effect)

/-- A C call is an effect event when it calls a declared irreversible hook.
Catalog name uniqueness is needed to distinguish these from resource calls. -/
def EffectEvent (p : Protocol) (event : Event) : Prop :=
  ∃ hook ∈ p.hooks, hook.kind = .effect ∧
    ∃ reply, event = .boolean hook.cName reply

def Event.name : Event → String
  | .boolean name _ | .void name => name

/-- Classifying source call sites retains the distinction between reversible
resource cleanup and ownership publication. Global C-name admission makes the
classification unambiguous for the observed call occurrences. -/
def classifiedCalls (p : Protocol) : List (String × Bool) :=
  p.hooks.map (fun hook => (hook.cName, hook.kind == .effect)) ++
    p.resources.flatMap (fun r => [(r.acquire, false), (r.release, false), (r.transfer, true)])

theorem classifiedCalls_names (p : Protocol) :
    (classifiedCalls p).map Prod.fst = cNames p := by
  simp [classifiedCalls, cNames, List.map_flatMap, List.map_map]

def IrreversibleEvent (p : Protocol) (event : Event) : Prop :=
  (event.name, true) ∈ classifiedCalls p

def TransferEvent (p : Protocol) (event : Event) : Prop :=
  ∃ resource ∈ p.resources, event = .void resource.transfer

theorem transferEvent_irreversible {p : Protocol} {event : Event}
    (publication : TransferEvent p event) : IrreversibleEvent p event := by
  obtain ⟨resource, member, rfl⟩ := publication
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨resource, member, by simp [Event.name]⟩)

theorem Enabled.no_irreversible_of_false {p : Protocol} (metadata : MetadataValid p)
    {first last : Context} {event : Event} (enabled : Enabled p first event last)
    (clean : last.irreversible = false) : ¬ IrreversibleEvent p event := by
  have reversible : (event.name, false) ∈ classifiedCalls p := by
    cases enabled with
    | call id hook reply declared =>
        have kind : (hook.kind == .effect) = false := by
          have parts : first.irreversible = false ∧ (hook.kind == .effect) = false := by
            simpa only [callContext, Bool.or_eq_false_iff] using clean
          exact parts.2
        exact List.mem_append_left _
          (List.mem_map.mpr ⟨hook, (findHook_spec declared).1, by simp [kind, Event.name]⟩)
    | acquire id resource reply declared =>
        exact List.mem_append_right _ (List.mem_flatMap.mpr
          ⟨resource, (findResource_spec declared).1, by simp [Event.name]⟩)
    | release id resource declared =>
        exact List.mem_append_right _ (List.mem_flatMap.mpr
          ⟨resource, (findResource_spec declared).1, by simp [Event.name]⟩)
    | transfer => simp [transferContext] at clean
  intro irreversible
  have unique : ((classifiedCalls p).map Prod.fst).Nodup := by
    rw [classifiedCalls_names]
    exact metadata.calls
  have impossible := List.inj_on_of_nodup_map unique reversible irreversible rfl
  exact Bool.noConfusion (congrArg Prod.snd impossible)

theorem Trace.no_irreversible_of_false {p : Protocol} (metadata : MetadataValid p)
    {first last : Context} {calls : List Event} (trace : Trace p first calls last)
    (clean : last.irreversible = false) : ∀ event ∈ calls, ¬ IrreversibleEvent p event := by
  induction trace with
  | nil => simp
  | @cons first middle last event rest enabled after ih =>
      have middleClean : middle.irreversible = false := by
        cases h : middle.irreversible with
        | false => rfl
        | true => have := after.irreversible_mono h; simp_all
      intro observed member
      rcases List.mem_cons.mp member with same | tail
      · subst observed
        exact enabled.no_irreversible_of_false metadata middleClean
      · exact ih clean observed tail

theorem Enabled.no_effect_of_false {p : Protocol} (metadata : MetadataValid p)
    {first last : Context} {event : Event} (enabled : Enabled p first event last)
    (clean : last.irreversible = false) : ¬ EffectEvent p event := by
  intro effect
  obtain ⟨other, otherMem, otherKind, reply, same⟩ := effect
  cases enabled with
  | call id hook actual declared facts owners =>
      have names := (Event.boolean.inj same).1
      have eq := metadata.hook_cName_injective (findHook_spec declared).1 otherMem names
      subst other
      simp [callContext, otherKind] at clean
  | acquire id resource actual declared fresh =>
      have names := (Event.boolean.inj same).1
      have disjoint := metadata.hook_resource_disjoint otherMem
        (findResource_spec declared).1 (name := resource.acquire) (by simp)
      exact disjoint names.symm
  | release => cases same
  | transfer => cases same

theorem Trace.no_effect_of_false {p : Protocol} (metadata : MetadataValid p)
    {first last : Context} {calls : List Event} (trace : Trace p first calls last)
    (clean : last.irreversible = false) : ∀ event ∈ calls, ¬ EffectEvent p event := by
  induction trace with
  | nil => simp
  | @cons first middle last event rest enabled after ih =>
      have middleClean : middle.irreversible = false := by
        cases h : middle.irreversible with
        | false => rfl
        | true => have := after.irreversible_mono h; simp_all
      intro observed member
      rcases List.mem_cons.mp member with same | tail
      · subst observed
        exact enabled.no_effect_of_false metadata middleClean
      · exact ih clean observed tail

/-- All executed operations are enabled, even if the finite reply tape runs
out. A return has no remaining owner; an exhausted tape is not a return. -/
theorem WellFormed.source_safe {World : Type} {p : Protocol} {c : Context}
    {body : Body} (wf : WellFormed p c body) (host : Host World)
    (world : World) (replies : List Bool) :
    ∃ last, Trace p c (evalSource p host body world replies).calls last ∧
      SafeStop p last (evalSource p host body world replies).status := by
  induction wf generalizing world replies with
  | ret c outcome empty decline facts =>
      exact ⟨c, by simp [evalSource, stop, Trace.nil], by
        simpa [evalSource, stop] using SafeStop.returned outcome empty decline facts⟩
  | call c id hook yes no declared facts owners yesWF noWF ihYes ihNo =>
      cases replies with
      | nil =>
          exact ⟨c, by simp [evalSource, declared, stop, Trace.nil], by
            simpa [evalSource, declared, stop] using (SafeStop.noReply (c := c) hook.cName)⟩
      | cons reply rest =>
          cases reply with
          | false =>
              obtain ⟨last, trace, safe⟩ := ihNo (host.boolean hook.cName world false) rest
              exact ⟨last, by
                simpa [evalSource, declared, record] using
                  Trace.cons (Enabled.call c id hook false declared facts owners) trace, by
                simpa [evalSource, declared, record] using safe⟩
          | true =>
              obtain ⟨last, trace, safe⟩ := ihYes (host.boolean hook.cName world true) rest
              exact ⟨last, by
                simpa [evalSource, declared, record] using
                  Trace.cons (Enabled.call c id hook true declared facts owners) trace, by
                simpa [evalSource, declared, record] using safe⟩
  | acquire c id resource yes no declared fresh facts yesWF noWF ihYes ihNo =>
      cases replies with
      | nil =>
          exact ⟨c, by simp [evalSource, declared, stop, Trace.nil], by
            simpa [evalSource, declared, stop] using
              (SafeStop.noReply (c := c) resource.acquire)⟩
      | cons reply rest =>
          cases reply with
          | false =>
              obtain ⟨last, trace, safe⟩ := ihNo (host.boolean resource.acquire world false) rest
              exact ⟨last, by
                simpa [evalSource, declared, record] using
                  Trace.cons (Enabled.acquire c id resource false declared fresh facts) trace, by
                simpa [evalSource, declared, record] using safe⟩
          | true =>
              obtain ⟨last, trace, safe⟩ := ihYes (host.boolean resource.acquire world true) rest
              exact ⟨last, by
                simpa [evalSource, declared, record] using
                  Trace.cons (Enabled.acquire c id resource true declared fresh facts) trace, by
                simpa [evalSource, declared, record] using safe⟩
  | release c id resource next declared owned nextWF ih =>
      obtain ⟨last, trace, safe⟩ := ih (host.void resource.release world) replies
      exact ⟨last, by
        simpa [evalSource, declared, record] using
          Trace.cons (Enabled.release c id resource declared owned) trace, by
        simpa [evalSource, declared, record] using safe⟩
  | transfer c id resource next declared owned facts nextWF ih =>
      obtain ⟨last, trace, safe⟩ := ih (host.void resource.transfer world) replies
      exact ⟨last, by
        simpa [evalSource, declared, record] using
          Trace.cons (Enabled.transfer c id resource declared owned facts) trace, by
        simpa [evalSource, declared, record] using safe⟩

/-- Safety is transferred to the independent target interpreter by the exact
lowering theorem, not by interpreting the target as source syntax. -/
theorem lower_target_safe {World : Type} {p : Protocol} {c : Context} {body : Body}
    (wf : WellFormed p c body) (target : CStmt) (compiled : lower p body = some target)
    (host : Host World) (world : World) (replies : List Bool) :
    ∃ last, Trace p c (evalC host target world replies).calls last ∧
      SafeStop p last (evalC host target world replies).status := by
  rw [lower_eval_exact p host body target compiled]
  exact wf.source_safe host world replies

/-- Every admitted return carries its declared exit certificates, including
the wake registration required by a suspension contract. -/
theorem lower_return_requires_facts {World : Type} {p : Protocol} {c : Context}
    {body : Body} (wf : WellFormed p c body) (target : CStmt)
    (compiled : lower p body = some target) (host : Host World)
    (world : World) (replies : List Bool) (outcome : Outcome)
    (returned : (evalC host target world replies).status = .returned outcome) :
    ∃ last, Trace p c (evalC host target world replies).calls last ∧
      ∀ fact ∈ exitRequires p outcome, fact ∈ last.facts := by
  obtain ⟨last, trace, safe⟩ := lower_target_safe wf target compiled host world replies
  rw [returned] at safe
  cases safe with
  | returned _ _ _ facts => exact ⟨last, trace, facts⟩

theorem lower_return_discharges_owners {World : Type} {p : Protocol} {c : Context}
    {body : Body} (wf : WellFormed p c body) (target : CStmt)
    (compiled : lower p body = some target) (host : Host World)
    (world : World) (replies : List Bool) (outcome : Outcome)
    (returned : (evalC host target world replies).status = .returned outcome) :
    ∃ last, Trace p c (evalC host target world replies).calls last ∧ last.owned = [] := by
  obtain ⟨last, trace, safe⟩ := lower_target_safe wf target compiled host world replies
  rw [returned] at safe
  cases safe with
  | returned _ empty => exact ⟨last, trace, empty⟩

theorem lower_decline_has_no_effect {World : Type} {p : Protocol}
    (metadata : MetadataValid p) {c : Context} {body : Body} (wf : WellFormed p c body)
    (target : CStmt) (compiled : lower p body = some target) (host : Host World)
    (world : World) (replies : List Bool)
    (declined : (evalC host target world replies).status = .returned .declined) :
    ∀ event ∈ (evalC host target world replies).calls, ¬ EffectEvent p event := by
  obtain ⟨last, trace, safe⟩ := lower_target_safe wf target compiled host world replies
  rw [declined] at safe
  cases safe with
  | returned _ _ clean _ => exact trace.no_effect_of_false metadata (clean rfl)

theorem lower_decline_has_no_publication {World : Type} {p : Protocol}
    (metadata : MetadataValid p) {c : Context} {body : Body} (wf : WellFormed p c body)
    (target : CStmt) (compiled : lower p body = some target) (host : Host World)
    (world : World) (replies : List Bool)
    (declined : (evalC host target world replies).status = .returned .declined) :
    ∀ event ∈ (evalC host target world replies).calls, ¬ IrreversibleEvent p event := by
  obtain ⟨last, trace, safe⟩ := lower_target_safe wf target compiled host world replies
  rw [declined] at safe
  cases safe with
  | returned _ _ clean _ => exact trace.no_irreversible_of_false metadata (clean rfl)

theorem lower_decline_has_no_transfer {World : Type} {p : Protocol}
    (metadata : MetadataValid p) {c : Context} {body : Body} (wf : WellFormed p c body)
    (target : CStmt) (compiled : lower p body = some target) (host : Host World)
    (world : World) (replies : List Bool)
    (declined : (evalC host target world replies).status = .returned .declined) :
    ∀ event ∈ (evalC host target world replies).calls, ¬ TransferEvent p event := by
  intro event member transferred
  exact lower_decline_has_no_publication metadata wf target compiled host world replies
    declined event member (transferEvent_irreversible transferred)

/-- After an effect has already occurred, no admitted continuation can return
declined, including continuations ending after a failed effect hook. -/
theorem lower_no_decline_after_effect {World : Type} {p : Protocol} {c : Context}
    {body : Body} (wf : WellFormed p c body) (effect : c.irreversible = true)
    (target : CStmt) (compiled : lower p body = some target) (host : Host World)
    (world : World) (replies : List Bool) :
    (evalC host target world replies).status ≠ .returned .declined := by
  intro declined
  obtain ⟨last, trace, safe⟩ := lower_target_safe wf target compiled host world replies
  rw [declined] at safe
  cases safe with
  | returned _ _ clean _ =>
      have marked := trace.irreversible_mono effect
      have unmarked := clean rfl
      simp_all

end Mettapedia.GSLT.LanguageDef.ExecutableProtocol
