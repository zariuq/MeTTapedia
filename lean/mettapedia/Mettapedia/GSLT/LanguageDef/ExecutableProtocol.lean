import Mettapedia.GSLT.LanguageDef.DeclaredTables

/-!
# Finite executable protocols

The source is a finite tree of declared hook and resource operations. Its
checker tracks known facts, exclusive resource obligations, and whether an
irreversible hook or ownership transfer has run. Lowering produces a separate
tree of ordinary Boolean C calls, void C calls and returns.

The two interpreters retain the complete host state, ordered call occurrences,
and remaining Boolean replies. Hooks are interpreted by an explicit host;
their declared purity and fact-establishing behavior remain host obligations.
Hooks explicitly invalidate certificates whose mutable dependencies they may
change. Invalidation forgets knowledge on both Boolean branches; it does not
assert the condition's negation or revoke live memory loans. Resource operations
must preserve certificates; a mutating operation is represented by a hook.
Neither this syntax nor its lowering introduces an implicit resumable machine.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ExecutableProtocol

inductive Outcome where
  | declined | answered | done | raised | suspended | resource_failure | engine_failure
  deriving DecidableEq, Repr

inductive HookKind where
  | guard | prepare | effect
  deriving DecidableEq, Repr

structure Hook where
  id : String
  cName : String
  kind : HookKind
  requires : List String
  uses : List String
  proves : List String
  invalidates : List String := []
  deriving DecidableEq, Repr

structure Resource where
  id : String
  acquire : String
  release : String
  transfer : String
  acquireRequires : List String := []
  transferRequires : List String := []
  deriving DecidableEq, Repr

inductive Body where
  | ret (outcome : Outcome)
  | call (hook : String) (yes no : Body)
  | acquire (resource : String) (yes no : Body)
  | release (resource : String) (next : Body)
  | transfer (resource : String) (next : Body)
  deriving DecidableEq, Repr

structure Protocol where
  name : String
  contextType : String
  hooks : List Hook
  resources : List Resource
  entryFacts : List String
  entryOwned : List String
  body : Body
  exitFacts : List (Outcome × List String) := []
  deriving DecidableEq, Repr

def exitRequires (p : Protocol) (outcome : Outcome) : List String :=
  p.exitFacts.flatMap fun entry => if entry.1 == outcome then entry.2 else []

structure Context where
  facts : List String
  owned : List String
  irreversible : Bool
  deriving DecidableEq, Repr

def initial (p : Protocol) : Context := ⟨p.entryFacts, p.entryOwned, false⟩

def findHook (p : Protocol) (id : String) : Option Hook :=
  p.hooks.find? (fun hook => hook.id == id)

def findResource (p : Protocol) (id : String) : Option Resource :=
  p.resources.find? (fun resource => resource.id == id)

def callContext (c : Context) (hook : Hook) (reply : Bool) : Context :=
  { c with
    facts := (if reply then hook.proves else []) ++
      c.facts.filter (fun fact => !hook.invalidates.contains fact)
    irreversible := c.irreversible || hook.kind == .effect }

def acquireContext (c : Context) (id : String) (reply : Bool) : Context :=
  if reply then { c with owned := id :: c.owned } else c

def disposeContext (c : Context) (id : String) : Context :=
  { c with owned := c.owned.erase id }

/-- Ownership publication commits the protocol even without an effect hook. -/
def transferContext (c : Context) (id : String) : Context :=
  { c with owned := c.owned.erase id, irreversible := true }

/-- The static judgment is independent of the executable Boolean checker. -/
inductive WellFormed (p : Protocol) : Context → Body → Prop where
  | ret (c : Context) (outcome : Outcome)
      (empty : c.owned = [])
      (decline : outcome = .declined → c.irreversible = false)
      (facts : ∀ fact ∈ exitRequires p outcome, fact ∈ c.facts) :
      WellFormed p c (.ret outcome)
  | call (c : Context) (id : String) (hook : Hook) (yes no : Body)
      (declared : findHook p id = some hook)
      (facts : ∀ fact ∈ hook.requires, fact ∈ c.facts)
      (owners : ∀ resource ∈ hook.uses, resource ∈ c.owned)
      (onTrue : WellFormed p (callContext c hook true) yes)
      (onFalse : WellFormed p (callContext c hook false) no) :
      WellFormed p c (.call id yes no)
  | acquire (c : Context) (id : String) (resource : Resource) (yes no : Body)
      (declared : findResource p id = some resource)
      (fresh : id ∉ c.owned)
      (facts : ∀ fact ∈ resource.acquireRequires, fact ∈ c.facts)
      (onTrue : WellFormed p (acquireContext c id true) yes)
      (onFalse : WellFormed p (acquireContext c id false) no) :
      WellFormed p c (.acquire id yes no)
  | release (c : Context) (id : String) (resource : Resource) (next : Body)
      (declared : findResource p id = some resource)
      (owned : id ∈ c.owned)
      (after : WellFormed p (disposeContext c id) next) :
      WellFormed p c (.release id next)
  | transfer (c : Context) (id : String) (resource : Resource) (next : Body)
      (declared : findResource p id = some resource)
      (owned : id ∈ c.owned)
      (facts : ∀ fact ∈ resource.transferRequires, fact ∈ c.facts)
      (after : WellFormed p (transferContext c id) next) :
      WellFormed p c (.transfer id next)

def checkBody (p : Protocol) : Context → Body → Bool
  | c, .ret outcome => c.owned.isEmpty &&
      (!c.irreversible || outcome != .declined) &&
      (exitRequires p outcome).all c.facts.contains
  | c, .call id yes no =>
      match findHook p id with
      | none => false
      | some hook => hook.requires.all (fun fact => c.facts.contains fact) &&
          hook.uses.all (fun resource => c.owned.contains resource) &&
          checkBody p (callContext c hook true) yes &&
          checkBody p (callContext c hook false) no
  | c, .acquire id yes no =>
      match findResource p id with
      | none => false
      | some resource => !c.owned.contains id &&
          resource.acquireRequires.all (fun fact => c.facts.contains fact) &&
          checkBody p (acquireContext c id true) yes &&
          checkBody p (acquireContext c id false) no
  | c, .release id next =>
      match findResource p id with
      | none => false
      | some _ => c.owned.contains id && checkBody p (disposeContext c id) next
  | c, .transfer id next =>
      match findResource p id with
      | none => false
      | some resource => c.owned.contains id &&
          resource.transferRequires.all (fun fact => c.facts.contains fact) &&
          checkBody p (transferContext c id) next

theorem checkBody_iff (p : Protocol) (c : Context) (body : Body) :
    checkBody p c body = true ↔ WellFormed p c body := by
  induction body generalizing c with
  | ret outcome =>
      simp only [checkBody, Bool.and_eq_true, List.isEmpty_iff,
        Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, List.all_eq_true, List.contains_iff_mem]
      constructor
      · rintro ⟨⟨empty, decline⟩, facts⟩
        exact .ret c outcome empty (fun h => decline.resolve_right (by simp [h])) facts
      · intro wf
        cases wf with
        | ret _ _ empty decline facts =>
            refine ⟨⟨empty, ?_⟩, facts⟩
            by_cases h : outcome = .declined
            · exact Or.inl (decline h)
            · exact Or.inr h
  | call id yes no ihYes ihNo =>
      cases declared : findHook p id with
      | none =>
          simp only [checkBody, declared, Bool.false_eq_true, false_iff]
          intro wf
          cases wf with
          | call _ _ hook _ _ h => simp [declared] at h
      | some hook =>
          simp only [checkBody, declared, Bool.and_eq_true, List.all_eq_true,
            List.contains_iff_mem, ihYes, ihNo]
          constructor
          · rintro ⟨⟨⟨facts, owners⟩, yesWF⟩, noWF⟩
            exact .call c id hook yes no declared facts owners yesWF noWF
          · intro wf
            cases wf with
            | call _ _ other _ _ h facts owners yesWF noWF =>
                have eq := Option.some.inj (declared.symm.trans h)
                subst other
                exact ⟨⟨⟨facts, owners⟩, yesWF⟩, noWF⟩
  | acquire id yes no ihYes ihNo =>
      cases declared : findResource p id with
      | none =>
          simp only [checkBody, declared, Bool.false_eq_true, false_iff]
          intro wf
          cases wf with
          | acquire _ _ resource _ _ h => simp [declared] at h
      | some resource =>
          simp [checkBody, declared, ihYes, ihNo]
          constructor
          · rintro ⟨⟨⟨fresh, facts⟩, yesWF⟩, noWF⟩
            exact .acquire c id resource yes no declared fresh facts yesWF noWF
          · intro wf
            cases wf with
            | acquire _ _ other _ _ h fresh facts yesWF noWF =>
                have eq := Option.some.inj (declared.symm.trans h)
                subst other
                exact ⟨⟨⟨fresh, facts⟩, yesWF⟩, noWF⟩
  | release id next ih =>
      cases declared : findResource p id with
      | none =>
          simp only [checkBody, declared, Bool.false_eq_true, false_iff]
          intro wf
          cases wf
          simp_all
      | some resource =>
          simp only [checkBody, declared, Bool.and_eq_true, List.contains_iff_mem, ih]
          constructor
          · rintro ⟨owned, nextWF⟩
            exact .release c id resource next declared owned nextWF
          · intro wf
            cases wf
            simp_all
  | transfer id next ih =>
      cases declared : findResource p id with
      | none =>
          simp only [checkBody, declared, Bool.false_eq_true, false_iff]
          intro wf
          cases wf
          simp_all
      | some resource =>
          simp only [checkBody, declared, Bool.and_eq_true, List.all_eq_true,
            List.contains_iff_mem, ih]
          constructor
          · rintro ⟨⟨owned, facts⟩, nextWF⟩
            exact .transfer c id resource next declared owned facts nextWF
          · intro wf
            cases wf
            simp_all

def cNames (p : Protocol) : List String :=
  p.hooks.map Hook.cName ++ p.resources.flatMap fun r => [r.acquire, r.release, r.transfer]

def sourceNames (p : Protocol) : List String :=
  [p.name, p.contextType] ++ p.hooks.flatMap
    (fun h => [h.id, h.cName] ++ h.requires ++ h.uses ++ h.proves ++ h.invalidates) ++
    p.resources.flatMap (fun r => [r.id, r.acquire, r.release, r.transfer] ++
      r.acquireRequires ++ r.transferRequires) ++
    p.entryFacts ++ p.entryOwned ++ p.exitFacts.flatMap Prod.snd

structure MetadataValid (p : Protocol) : Prop where
  names : ∀ name ∈ sourceNames p, DeclaredTables.identifier name = true
  hooks : (p.hooks.map Hook.id).Nodup
  resources : (p.resources.map Resource.id).Nodup
  calls : (cNames p).Nodup
  entryOwners : p.entryOwned.Nodup
  entryFacts : p.entryFacts.Nodup
  entryDeclared : ∀ id ∈ p.entryOwned, ∃ resource, findResource p id = some resource
  hookResources : ∀ hook ∈ p.hooks, ∀ id ∈ hook.uses,
    ∃ resource, findResource p id = some resource
  hookLists : ∀ hook ∈ p.hooks,
    hook.requires.Nodup ∧ hook.uses.Nodup ∧ hook.proves.Nodup ∧ hook.invalidates.Nodup
  resourceLists : ∀ resource ∈ p.resources,
    resource.acquireRequires.Nodup ∧ resource.transferRequires.Nodup
  exitLists : (p.exitFacts.map Prod.fst).Nodup ∧
    ∀ entry ∈ p.exitFacts, entry.2.Nodup

def checkMetadata (p : Protocol) : Bool :=
  (sourceNames p).all DeclaredTables.identifier &&
  decide (p.hooks.map Hook.id).Nodup &&
  decide (p.resources.map Resource.id).Nodup &&
  decide (cNames p).Nodup && decide p.entryOwned.Nodup && decide p.entryFacts.Nodup &&
  p.entryOwned.all (fun id => (findResource p id).isSome) &&
  p.hooks.all (fun hook => hook.uses.all (fun id => (findResource p id).isSome)) &&
  p.hooks.all (fun hook => decide hook.requires.Nodup && decide hook.uses.Nodup &&
    decide hook.proves.Nodup && decide hook.invalidates.Nodup) &&
  p.resources.all (fun resource => decide resource.acquireRequires.Nodup &&
    decide resource.transferRequires.Nodup) &&
  (decide (p.exitFacts.map Prod.fst).Nodup &&
    p.exitFacts.all (fun entry => decide entry.2.Nodup))

theorem checkMetadata_iff (p : Protocol) :
    checkMetadata p = true ↔ MetadataValid p := by
  simp only [checkMetadata, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, Option.isSome_iff_exists]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨names, hooks⟩, resources⟩, calls⟩, entryOwners⟩, entryFacts⟩,
      entryDeclared⟩, hookResources⟩, hookLists⟩, resourceLists⟩, exitLists⟩
    exact ⟨names, hooks, resources, calls, entryOwners, entryFacts, entryDeclared,
      hookResources, (fun hook member => ⟨(hookLists hook member).1.1.1,
        (hookLists hook member).1.1.2, (hookLists hook member).1.2,
        (hookLists hook member).2⟩), resourceLists, exitLists⟩
  · rintro ⟨names, hooks, resources, calls, entryOwners, entryFacts, entryDeclared,
      hookResources, hookLists, resourceLists, exitLists⟩
    have hookChecks : ∀ hook ∈ p.hooks,
        ((hook.requires.Nodup ∧ hook.uses.Nodup) ∧ hook.proves.Nodup) ∧ hook.invalidates.Nodup :=
      fun hook member => ⟨⟨⟨(hookLists hook member).1,
        (hookLists hook member).2.1⟩, (hookLists hook member).2.2.1⟩,
        (hookLists hook member).2.2.2⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨names, hooks⟩, resources⟩, calls⟩, entryOwners⟩, entryFacts⟩,
      entryDeclared⟩, hookResources⟩, hookChecks⟩, resourceLists⟩, exitLists⟩

def check (p : Protocol) : Bool :=
  checkMetadata p && checkBody p (initial p) p.body

structure Valid (p : Protocol) : Prop where
  metadata : MetadataValid p
  body : WellFormed p (initial p) p.body

theorem check_iff (p : Protocol) : check p = true ↔ Valid p := by
  simp only [check, Bool.and_eq_true, checkMetadata_iff, checkBody_iff]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.metadata, h.body⟩⟩

/-- This target has C call names and C control structure, with no source hook
IDs, ownership instructions, fact declarations or implicit interpreter loop. -/
inductive CStmt where
  | ret (outcome : Outcome)
  | ifCall (cName : String) (yes no : CStmt)
  | voidCall (cName : String) (next : CStmt)
  deriving DecidableEq, Repr

def lower (p : Protocol) : Body → Option CStmt
  | .ret outcome => some (.ret outcome)
  | .call id yes no => do
      let hook ← findHook p id
      let yes' ← lower p yes
      let no' ← lower p no
      pure (.ifCall hook.cName yes' no')
  | .acquire id yes no => do
      let resource ← findResource p id
      let yes' ← lower p yes
      let no' ← lower p no
      pure (.ifCall resource.acquire yes' no')
  | .release id next => do
      let resource ← findResource p id
      let next' ← lower p next
      pure (.voidCall resource.release next')
  | .transfer id next => do
      let resource ← findResource p id
      let next' ← lower p next
      pure (.voidCall resource.transfer next')

theorem WellFormed.lower_exists {p : Protocol} {c : Context} {body : Body}
    (wf : WellFormed p c body) : ∃ target, lower p body = some target := by
  induction wf with
  | ret c outcome => exact ⟨.ret outcome, rfl⟩
  | call c id hook yes no declared _ _ _ _ ihYes ihNo =>
      obtain ⟨yes', hyes⟩ := ihYes
      obtain ⟨no', hno⟩ := ihNo
      exact ⟨.ifCall hook.cName yes' no', by simp [lower, declared, hyes, hno]⟩
  | acquire c id resource yes no declared _ _ _ _ ihYes ihNo =>
      obtain ⟨yes', hyes⟩ := ihYes
      obtain ⟨no', hno⟩ := ihNo
      exact ⟨.ifCall resource.acquire yes' no', by simp [lower, declared, hyes, hno]⟩
  | release c id resource next declared _ _ ih =>
      obtain ⟨next', hnext⟩ := ih
      exact ⟨.voidCall resource.release next', by simp [lower, declared, hnext]⟩
  | transfer c id resource next declared _ _ _ ih =>
      obtain ⟨next', hnext⟩ := ih
      exact ⟨.voidCall resource.transfer next', by simp [lower, declared, hnext]⟩

inductive Event where
  | boolean (cName : String) (reply : Bool)
  | void (cName : String)
  deriving DecidableEq, Repr

inductive Status where
  | returned (outcome : Outcome)
  | noReply (cName : String)
  | unknownHook (id : String)
  | unknownResource (id : String)
  deriving DecidableEq, Repr

/-- Host transitions are explicit and may change arbitrary world state. The
reply tape supplies ordinary Boolean replies; void calls consume no reply. -/
structure Host (World : Type) where
  boolean : String → World → Bool → World
  void : String → World → World

structure Execution (World : Type) where
  status : Status
  world : World
  remaining : List Bool
  calls : List Event
  deriving DecidableEq, Repr

def stop {World : Type} (status : Status) (world : World) (replies : List Bool) :
    Execution World := ⟨status, world, replies, []⟩

def record {World : Type} (event : Event) (rest : Execution World) : Execution World :=
  { rest with calls := event :: rest.calls }

/-- Source execution performs declaration lookup and source resource
operations directly; it does not invoke `lower` or the target interpreter. -/
def evalSource {World : Type} (p : Protocol) (host : Host World) :
    Body → World → List Bool → Execution World
  | .ret outcome, world, replies => stop (.returned outcome) world replies
  | .call id yes no, world, replies =>
      match findHook p id with
      | none => stop (.unknownHook id) world replies
      | some hook => match replies with
          | [] => stop (.noReply hook.cName) world []
          | false :: rest => record (.boolean hook.cName false)
              (evalSource p host no (host.boolean hook.cName world false) rest)
          | true :: rest => record (.boolean hook.cName true)
              (evalSource p host yes (host.boolean hook.cName world true) rest)
  | .acquire id yes no, world, replies =>
      match findResource p id with
      | none => stop (.unknownResource id) world replies
      | some resource => match replies with
          | [] => stop (.noReply resource.acquire) world []
          | false :: rest => record (.boolean resource.acquire false)
              (evalSource p host no (host.boolean resource.acquire world false) rest)
          | true :: rest => record (.boolean resource.acquire true)
              (evalSource p host yes (host.boolean resource.acquire world true) rest)
  | .release id next, world, replies =>
      match findResource p id with
      | none => stop (.unknownResource id) world replies
      | some resource => record (.void resource.release)
          (evalSource p host next (host.void resource.release world) replies)
  | .transfer id next, world, replies =>
      match findResource p id with
      | none => stop (.unknownResource id) world replies
      | some resource => record (.void resource.transfer)
          (evalSource p host next (host.void resource.transfer world) replies)

/-- Independent execution of the C-shaped target. It has no protocol catalog
or knowledge of fact, resource, source-kind or source-ID annotations. -/
def evalC {World : Type} (host : Host World) :
    CStmt → World → List Bool → Execution World
  | .ret outcome, world, replies => stop (.returned outcome) world replies
  | .ifCall cName yes no, world, replies => match replies with
      | [] => stop (.noReply cName) world []
      | false :: rest => record (.boolean cName false)
          (evalC host no (host.boolean cName world false) rest)
      | true :: rest => record (.boolean cName true)
          (evalC host yes (host.boolean cName world true) rest)
  | .voidCall cName next, world, replies => record (.void cName)
      (evalC host next (host.void cName world) replies)

/-- Exact equality includes status, world, ordered repeated calls, Boolean
replies paired with those calls, and the unconsumed suffix of the reply tape. -/
theorem lower_eval_exact {World : Type} (p : Protocol) (host : Host World)
    (body : Body) (target : CStmt) (compiled : lower p body = some target)
    (world : World) (replies : List Bool) :
    evalC host target world replies = evalSource p host body world replies := by
  induction body generalizing target world replies with
  | ret outcome =>
      simp only [lower, Option.some.injEq] at compiled
      subst target
      simp [evalC, evalSource]
  | call id yes no ihYes ihNo =>
      simp only [lower] at compiled
      cases declared : findHook p id with
      | none => simp [declared] at compiled
      | some hook =>
          cases hyes : lower p yes with
          | none => simp [declared, hyes] at compiled
          | some yes' =>
              cases hno : lower p no with
              | none => simp [declared, hyes, hno] at compiled
              | some no' =>
                  simp [declared, hyes, hno] at compiled
                  subst target
                  cases replies with
                  | nil => simp [evalSource, evalC, declared]
                  | cons reply rest =>
                      cases reply with
                      | false => simp [evalSource, evalC, declared, ihNo no' hno]
                      | true => simp [evalSource, evalC, declared, ihYes yes' hyes]
  | acquire id yes no ihYes ihNo =>
      simp only [lower] at compiled
      cases declared : findResource p id with
      | none => simp [declared] at compiled
      | some resource =>
          cases hyes : lower p yes with
          | none => simp [declared, hyes] at compiled
          | some yes' =>
              cases hno : lower p no with
              | none => simp [declared, hyes, hno] at compiled
              | some no' =>
                  simp [declared, hyes, hno] at compiled
                  subst target
                  cases replies with
                  | nil => simp [evalSource, evalC, declared]
                  | cons reply rest =>
                      cases reply with
                      | false => simp [evalSource, evalC, declared, ihNo no' hno]
                      | true => simp [evalSource, evalC, declared, ihYes yes' hyes]
  | release id next ih | transfer id next ih =>
      simp only [lower] at compiled
      cases declared : findResource p id with
      | none => simp [declared] at compiled
      | some resource =>
          cases hnext : lower p next with
          | none => simp [declared, hnext] at compiled
          | some next' =>
              simp [declared, hnext] at compiled
              subst target
              simp [evalSource, evalC, declared, ih next' hnext]

def consumed (calls : List Event) : List Bool :=
  calls.filterMap fun event => match event with
    | .boolean _ reply => some reply
    | .void _ => none

@[simp] theorem consumed_nil : consumed [] = [] := rfl

@[simp] theorem consumed_boolean (name : String) (reply : Bool) (rest : List Event) :
    consumed (.boolean name reply :: rest) = reply :: consumed rest := rfl

@[simp] theorem consumed_void (name : String) (rest : List Event) :
    consumed (.void name :: rest) = consumed rest := rfl

/-- Every supplied reply is either consumed by one actual Boolean call or
retained in the suffix. Void calls never consume replies. -/
theorem evalC_reply_partition {World : Type} (host : Host World) (target : CStmt)
    (world : World) (replies : List Bool) :
    consumed (evalC host target world replies).calls ++
      (evalC host target world replies).remaining = replies := by
  induction target generalizing world replies with
  | ret outcome => simp [evalC, stop]
  | ifCall name yes no ihYes ihNo =>
      cases replies with
      | nil => simp [evalC, stop]
      | cons reply rest =>
          cases reply with
          | false => simp [evalC, record, ihNo]
          | true => simp [evalC, record, ihYes]
  | voidCall name next ih => simp [evalC, record, ih]

/-- Immediate refusal after an admission guard does not call either the true
branch or any preparation hidden inside it. This needs no purity assumption. -/
theorem evalC_early_refusal {World : Type} (host : Host World) (name : String)
    (accepted : CStmt) (world : World) (rest : List Bool) :
    evalC host (.ifCall name accepted (.ret .declined)) world (false :: rest) =
      ⟨.returned .declined, host.boolean name world false, rest,
        [.boolean name false]⟩ := by simp [evalC, stop, record]

/-- A recorded native target is independent input. Admission checks it
against lowering the recorded source; it is never defined to be that result. -/
structure Plan where
  protocol : Protocol
  target : CStmt
  deriving DecidableEq, Repr

def checkPlan (plan : Plan) : Bool :=
  check plan.protocol && decide (lower plan.protocol plan.protocol.body = some plan.target)

structure PlanValid (plan : Plan) : Prop where
  source : Valid plan.protocol
  target : lower plan.protocol plan.protocol.body = some plan.target

theorem checkPlan_iff (plan : Plan) : checkPlan plan = true ↔ PlanValid plan := by
  simp only [checkPlan, Bool.and_eq_true, check_iff, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.source, h.target⟩⟩

theorem PlanValid.eval_exact {World : Type} {plan : Plan} (valid : PlanValid plan)
    (host : Host World) (world : World) (replies : List Bool) :
    evalC host plan.target world replies =
      evalSource plan.protocol host plan.protocol.body world replies :=
  lower_eval_exact plan.protocol host plan.protocol.body plan.target valid.target world replies

/-- Exact lowering reflects a target return as well as preserving a source
return. This excludes extra target outcomes at the complete observation. -/
theorem PlanValid.returns_iff {World : Type} {plan : Plan} (valid : PlanValid plan)
    (host : Host World) (world : World) (replies : List Bool) (outcome : Outcome) :
    (evalC host plan.target world replies).status = .returned outcome ↔
      (evalSource plan.protocol host plan.protocol.body world replies).status =
        .returned outcome := by
  rw [valid.eval_exact host world replies]

theorem PlanValid.consumed_exact {World : Type} {plan : Plan} (valid : PlanValid plan)
    (host : Host World) (world : World) (replies : List Bool) :
    consumed (evalC host plan.target world replies).calls =
      consumed (evalSource plan.protocol host plan.protocol.body world replies).calls := by
  rw [valid.eval_exact host world replies]

end Mettapedia.GSLT.LanguageDef.ExecutableProtocol
