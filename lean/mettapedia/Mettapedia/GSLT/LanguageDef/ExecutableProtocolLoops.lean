import Mettapedia.GSLT.LanguageDef.ExecutableProtocolComposition

/-!
# Bounded protocol iteration

Iteration extends the finite protocol vocabulary with a countdown and an
explicit continuation back to its enclosing loop. Bounds are evaluated once.
The source retains hook/resource identifiers; the target contains only C call
names, branches, countdowns and returns. Their interpreters are independent.

Resource obligations remain symbolic. A context field supplying a bound is a
nonvolatile uint64_t in generated C; its abstract observation has the same
range. Native hook truth, physical ownership and compiler fidelity are separate
implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ExecutableProtocol.Loops

open Mettapedia.GSLT.LanguageDef

inductive Bound where
  | literal (value : Nat)
  | field (name : String)
  deriving DecidableEq, Repr

def checkBound : Bound → Bool
  | .literal value => decide (value < 2 ^ 64)
  | .field name => DeclaredTables.identifier name

inductive BoundValid : Bound → Prop where
  | literal (value : Nat) (fits : value < 2 ^ 64) : BoundValid (.literal value)
  | field (name : String) (identifier : DeclaredTables.identifier name = true) :
      BoundValid (.field name)

theorem checkBound_iff (bound : Bound) : checkBound bound = true ↔ BoundValid bound := by
  cases bound with
  | literal value =>
      simp only [checkBound, decide_eq_true_eq]
      exact ⟨BoundValid.literal value, fun h => by cases h; assumption⟩
  | field name =>
      exact ⟨BoundValid.field name, fun h => by cases h; assumption⟩

inductive Body where
  | ret (outcome : Outcome)
  | call (hook : String) (yes no : Body)
  | acquire (resource : String) (yes no : Body)
  | release (resource : String) (next : Body)
  | transfer (resource : String) (next : Body)
  | loop (bound : Bound) (body exhausted : Body)
  | cont
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

/-- A non-executable metadata projection for the existing declaration checker
and lookups. The dummy finite body is never interpreted. -/
def metadata (p : Protocol) : ExecutableProtocol.Protocol :=
  ⟨p.name, p.contextType, p.hooks, p.resources, p.entryFacts, p.entryOwned, .ret .done, p.exitFacts⟩

def initial (p : Protocol) : Context := ⟨p.entryFacts, p.entryOwned, false⟩

def loopEntry (c : Context) : Context := { c with irreversible := true }

def carries (entry current : Context) : Prop :=
  (∀ resource ∈ current.owned, resource ∈ entry.owned) ∧
  (∀ resource ∈ entry.owned, resource ∈ current.owned) ∧
  (∀ fact ∈ entry.facts, fact ∈ current.facts)

def checkCarries (entry current : Context) : Bool :=
  current.owned.all entry.owned.contains && entry.owned.all current.owned.contains &&
  entry.facts.all current.facts.contains

theorem checkCarries_iff (entry current : Context) :
    checkCarries entry current = true ↔ carries entry current := by
  simp only [checkCarries, carries, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  exact and_assoc

inductive WellFormed (p : Protocol) : Option Context → Context → Body → Prop where
  | ret (loop : Option Context) (c : Context) (outcome : Outcome)
      (empty : c.owned = []) (decline : outcome = .declined → c.irreversible = false)
      (facts : ∀ fact ∈ exitRequires (metadata p) outcome, fact ∈ c.facts) :
      WellFormed p loop c (.ret outcome)
  | call (loop : Option Context) (c : Context) (id : String) (hook : Hook) (yes no : Body)
      (declared : findHook (metadata p) id = some hook)
      (facts : ∀ fact ∈ hook.requires, fact ∈ c.facts)
      (owners : ∀ owner ∈ hook.uses, owner ∈ c.owned)
      (onTrue : WellFormed p loop (callContext c hook true) yes)
      (onFalse : WellFormed p loop (callContext c hook false) no) :
      WellFormed p loop c (.call id yes no)
  | acquire (loop : Option Context) (c : Context) (id : String) (resource : Resource) (yes no : Body)
      (declared : findResource (metadata p) id = some resource) (fresh : id ∉ c.owned)
      (facts : ∀ fact ∈ resource.acquireRequires, fact ∈ c.facts)
      (onTrue : WellFormed p loop (acquireContext c id true) yes)
      (onFalse : WellFormed p loop (acquireContext c id false) no) :
      WellFormed p loop c (.acquire id yes no)
  | release (loop : Option Context) (c : Context) (id : String) (resource : Resource) (next : Body)
      (declared : findResource (metadata p) id = some resource) (owned : id ∈ c.owned)
      (after : WellFormed p loop (disposeContext c id) next) :
      WellFormed p loop c (.release id next)
  | transfer (loop : Option Context) (c : Context) (id : String) (resource : Resource) (next : Body)
      (declared : findResource (metadata p) id = some resource) (owned : id ∈ c.owned)
      (facts : ∀ fact ∈ resource.transferRequires, fact ∈ c.facts)
      (after : WellFormed p loop (transferContext c id) next) :
      WellFormed p loop c (.transfer id next)
  | loop (outer : Option Context) (c : Context) (bound : Bound) (body exhausted : Body)
      (validBound : BoundValid bound)
      (iteration : WellFormed p (some (loopEntry c)) (loopEntry c) body)
      (after : WellFormed p outer (loopEntry c) exhausted) :
      WellFormed p outer c (.loop bound body exhausted)
  | cont (c entry : Context) (preserves : carries entry c) :
      WellFormed p (some entry) c .cont

def checkBody (p : Protocol) : Option Context → Context → Body → Bool
  | _, c, .ret outcome => c.owned.isEmpty && (!c.irreversible || outcome != .declined) &&
      (exitRequires (metadata p) outcome).all c.facts.contains
  | loop, c, .call id yes no =>
      match findHook (metadata p) id with
      | none => false
      | some hook => hook.requires.all c.facts.contains && hook.uses.all c.owned.contains &&
          checkBody p loop (callContext c hook true) yes &&
          checkBody p loop (callContext c hook false) no
  | loop, c, .acquire id yes no =>
      match findResource (metadata p) id with
      | none => false
      | some resource => !c.owned.contains id && resource.acquireRequires.all c.facts.contains &&
          checkBody p loop (acquireContext c id true) yes &&
          checkBody p loop (acquireContext c id false) no
  | loop, c, .release id next =>
      match findResource (metadata p) id with
      | none => false
      | some _ => c.owned.contains id && checkBody p loop (disposeContext c id) next
  | loop, c, .transfer id next =>
      match findResource (metadata p) id with
      | none => false
      | some resource => c.owned.contains id && resource.transferRequires.all c.facts.contains &&
          checkBody p loop (transferContext c id) next
  | outer, c, .loop bound body exhausted =>
      checkBound bound && checkBody p (some (loopEntry c)) (loopEntry c) body &&
      checkBody p outer (loopEntry c) exhausted
  | none, _, .cont => false
  | some entry, c, .cont => checkCarries entry c

theorem checkBody_iff (p : Protocol) (loop : Option Context) (c : Context) (body : Body) :
    checkBody p loop c body = true ↔ WellFormed p loop c body := by
  induction body generalizing loop c with
  | ret outcome =>
      simp only [checkBody, Bool.and_eq_true, List.isEmpty_iff, Bool.or_eq_true,
        Bool.not_eq_true', bne_iff_ne, List.all_eq_true, List.contains_iff_mem]
      constructor
      · rintro ⟨⟨empty, decline⟩, facts⟩
        exact .ret loop c outcome empty (fun h => decline.resolve_right (by simp [h])) facts
      · intro wf
        cases wf with
        | ret _ _ _ empty decline facts =>
            refine ⟨⟨empty, ?_⟩, facts⟩
            by_cases h : outcome = .declined
            · exact Or.inl (decline h)
            · exact Or.inr h
  | call id yes no ihYes ihNo =>
      cases declared : findHook (metadata p) id with
      | none =>
          simp only [checkBody, declared, Bool.false_eq_true, false_iff]
          intro wf; cases wf with
          | call _ _ _ _ _ _ h => simp [declared] at h
      | some hook =>
          simp only [checkBody, declared, Bool.and_eq_true, List.all_eq_true,
            List.contains_iff_mem, ihYes, ihNo]
          constructor
          · rintro ⟨⟨⟨facts, owners⟩, yesWF⟩, noWF⟩
            exact .call loop c id hook yes no declared facts owners yesWF noWF
          · intro wf
            cases wf with
            | call _ _ _ other _ _ h facts owners yesWF noWF =>
                have eq := Option.some.inj (declared.symm.trans h)
                subst other
                exact ⟨⟨⟨facts, owners⟩, yesWF⟩, noWF⟩
  | acquire id yes no ihYes ihNo =>
      cases declared : findResource (metadata p) id with
      | none =>
          simp only [checkBody, declared, Bool.false_eq_true, false_iff]
          intro wf; cases wf with
          | acquire _ _ _ _ _ _ h => simp [declared] at h
      | some resource =>
          simp [checkBody, declared, ihYes, ihNo]
          constructor
          · rintro ⟨⟨⟨fresh, facts⟩, yesWF⟩, noWF⟩
            exact .acquire loop c id resource yes no declared fresh facts yesWF noWF
          · intro wf
            cases wf with
            | acquire _ _ _ other _ _ h fresh facts yesWF noWF =>
                have eq := Option.some.inj (declared.symm.trans h)
                subst other
                exact ⟨⟨⟨fresh, facts⟩, yesWF⟩, noWF⟩
  | release id next ih =>
      cases declared : findResource (metadata p) id with
      | none =>
          simp only [checkBody, declared, Bool.false_eq_true, false_iff]
          intro wf; cases wf; simp_all
      | some resource =>
          simp only [checkBody, declared, Bool.and_eq_true, List.contains_iff_mem, ih]
          constructor
          · rintro ⟨owned, nextWF⟩
            exact .release loop c id resource next declared owned nextWF
          · intro wf; cases wf; simp_all
  | transfer id next ih =>
      cases declared : findResource (metadata p) id with
      | none =>
          simp only [checkBody, declared, Bool.false_eq_true, false_iff]
          intro wf; cases wf; simp_all
      | some resource =>
          simp only [checkBody, declared, Bool.and_eq_true, List.contains_iff_mem,
            List.all_eq_true, ih]
          constructor
          · rintro ⟨⟨owned, facts⟩, nextWF⟩
            exact .transfer loop c id resource next declared owned facts nextWF
          · intro wf; cases wf; simp_all
  | loop bound body exhausted ihBody ihExhausted =>
      simp only [checkBody, Bool.and_eq_true, checkBound_iff, ihBody, ihExhausted]
      constructor
      · rintro ⟨⟨validBound, iteration⟩, after⟩
        exact .loop loop c bound body exhausted validBound iteration after
      · intro wf; cases wf; simp_all
  | cont =>
      cases loop with
      | none =>
          simp only [checkBody, Bool.false_eq_true, false_iff]
          intro wf; cases wf
      | some entry =>
          simp only [checkBody, checkCarries_iff]
          exact ⟨WellFormed.cont c entry, fun wf => by cases wf; assumption⟩

def check (p : Protocol) : Bool :=
  checkMetadata (metadata p) && checkBody p none (initial p) p.body

structure Valid (p : Protocol) : Prop where
  metadata : MetadataValid (Loops.metadata p)
  body : WellFormed p none (initial p) p.body

theorem check_iff (p : Protocol) : check p = true ↔ Valid p := by
  simp only [check, Bool.and_eq_true, checkMetadata_iff, checkBody_iff]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.metadata, h.body⟩⟩

theorem continue_preserves_owners {p : Protocol} {entry current : Context}
    (wf : WellFormed p (some entry) current .cont) :
    ∀ resource, resource ∈ current.owned ↔ resource ∈ entry.owned := by
  cases wf with
  | cont _ _ preserves =>
      exact fun resource => ⟨preserves.1 resource, preserves.2.1 resource⟩

theorem return_discharges {p : Protocol} {loop : Option Context} {current : Context} {outcome : Outcome}
    (wf : WellFormed p loop current (.ret outcome)) : current.owned = [] := by
  cases wf; assumption

theorem committed_no_decline {p : Protocol} {loop : Option Context} {current : Context}
    (committed : current.irreversible = true) :
    ¬ WellFormed p loop current (.ret .declined) := by
  intro wf
  cases wf with
  | ret _ _ _ _ decline _ => simp [committed] at decline

inductive CStmt where
  | ret (outcome : Outcome)
  | ifCall (name : String) (yes no : CStmt)
  | voidCall (name : String) (next : CStmt)
  | loop (bound : Bound) (body exhausted : CStmt)
  | cont
  deriving DecidableEq, Repr

def lower (p : Protocol) : Body → Option CStmt
  | .ret outcome => some (.ret outcome)
  | .cont => some .cont
  | .call id yes no => do
      let hook ← findHook (metadata p) id
      pure (.ifCall hook.cName (← lower p yes) (← lower p no))
  | .acquire id yes no => do
      let resource ← findResource (metadata p) id
      pure (.ifCall resource.acquire (← lower p yes) (← lower p no))
  | .release id next => do
      let resource ← findResource (metadata p) id
      pure (.voidCall resource.release (← lower p next))
  | .transfer id next => do
      let resource ← findResource (metadata p) id
      pure (.voidCall resource.transfer (← lower p next))
  | .loop bound body exhausted => do
      pure (.loop bound (← lower p body) (← lower p exhausted))

inductive Exit where
  | returned (outcome : Outcome)
  | again
  | noReply (name : String)
  | unknownHook (id : String)
  | unknownResource (id : String)
  deriving DecidableEq, Repr

structure Host (World : Type) extends ExecutableProtocol.Host World where
  limit : String → World → Fin (2 ^ 64)

def boundValue {World : Type} (host : Host World) (world : World) : Bound → Nat
  | .literal value => value
  | .field name => (host.limit name world).val

structure Execution (World : Type) where
  exit : Exit
  world : World
  remaining : List Bool
  calls : List Event
  deriving DecidableEq, Repr

def stop {World : Type} (exit : Exit) (world : World) (replies : List Bool) : Execution World :=
  ⟨exit, world, replies, []⟩

def record {World : Type} (event : Event) (after : Execution World) : Execution World :=
  { after with calls := event :: after.calls }

def prependExecution {World : Type} (first after : Execution World) : Execution World :=
  { after with calls := first.calls ++ after.calls }

structure Iteration (World : Type) where
  execution : Execution World
  turns : Nat

def sourceLoop {World : Type} (body after : World → List Bool → Execution World) :
    Nat → World → List Bool → Iteration World
  | 0, world, replies => ⟨after world replies, 0⟩
  | n+1, world, replies =>
      let first := body world replies
      match first.exit with
      | .again =>
          let rest := sourceLoop body after n first.world first.remaining
          ⟨prependExecution first rest.execution, rest.turns+1⟩
      | _ => ⟨first, 1⟩

/-- C countdown execution evaluates its body and then tests whether control
continues at the decrement, rather than interpreting source loop instructions. -/
def targetLoop {World : Type} (body after : World → List Bool → Execution World) :
    Nat → World → List Bool → Iteration World
  | 0, world, replies => ⟨after world replies, 0⟩
  | n+1, world, replies =>
      let turn := body world replies
      if turn.exit = .again then
        let remaining := targetLoop body after n turn.world turn.remaining
        ⟨{ remaining.execution with calls := turn.calls ++ remaining.execution.calls },
          remaining.turns+1⟩
      else ⟨turn, 1⟩

def evalSource {World : Type} (p : Protocol) (host : Host World) :
    Body → World → List Bool → Execution World
  | .ret outcome, world, replies => stop (.returned outcome) world replies
  | .cont, world, replies => stop .again world replies
  | .call id yes no, world, replies =>
      match findHook (metadata p) id with
      | none => stop (.unknownHook id) world replies
      | some hook => match replies with
          | [] => stop (.noReply hook.cName) world []
          | false :: rest => record (.boolean hook.cName false)
              (evalSource p host no (host.boolean hook.cName world false) rest)
          | true :: rest => record (.boolean hook.cName true)
              (evalSource p host yes (host.boolean hook.cName world true) rest)
  | .acquire id yes no, world, replies =>
      match findResource (metadata p) id with
      | none => stop (.unknownResource id) world replies
      | some resource => match replies with
          | [] => stop (.noReply resource.acquire) world []
          | false :: rest => record (.boolean resource.acquire false)
              (evalSource p host no (host.boolean resource.acquire world false) rest)
          | true :: rest => record (.boolean resource.acquire true)
              (evalSource p host yes (host.boolean resource.acquire world true) rest)
  | .release id next, world, replies =>
      match findResource (metadata p) id with
      | none => stop (.unknownResource id) world replies
      | some resource => record (.void resource.release)
          (evalSource p host next (host.void resource.release world) replies)
  | .transfer id next, world, replies =>
      match findResource (metadata p) id with
      | none => stop (.unknownResource id) world replies
      | some resource => record (.void resource.transfer)
          (evalSource p host next (host.void resource.transfer world) replies)
  | .loop bound body after, world, replies =>
      (sourceLoop (evalSource p host body) (evalSource p host after)
        (boundValue host world bound) world replies).execution

def evalC {World : Type} (host : Host World) : CStmt → World → List Bool → Execution World
  | .ret outcome, world, replies => stop (.returned outcome) world replies
  | .cont, world, replies => stop .again world replies
  | .ifCall name yes no, world, replies => match replies with
      | [] => stop (.noReply name) world []
      | false :: rest => record (.boolean name false)
          (evalC host no (host.boolean name world false) rest)
      | true :: rest => record (.boolean name true)
          (evalC host yes (host.boolean name world true) rest)
  | .voidCall name next, world, replies => record (.void name)
      (evalC host next (host.void name world) replies)
  | .loop bound body after, world, replies =>
      (targetLoop (evalC host body) (evalC host after)
        (boundValue host world bound) world replies).execution

theorem sourceLoop_turns_le {World : Type} (body after : World → List Bool → Execution World)
    (fuel : Nat) (world : World) (replies : List Bool) :
    (sourceLoop body after fuel world replies).turns ≤ fuel := by
  induction fuel generalizing world replies with
  | zero => simp [sourceLoop]
  | succ n ih =>
      simp only [sourceLoop]
      split
      · exact Nat.add_le_add_right (ih _ _) 1
      · exact Nat.le_add_left 1 n

theorem iteration_exact {World : Type}
    (sourceBody sourceAfter targetBody targetAfter : World → List Bool → Execution World)
    (body : ∀ world replies, sourceBody world replies = targetBody world replies)
    (after : ∀ world replies, sourceAfter world replies = targetAfter world replies)
    (fuel : Nat) (world : World) (replies : List Bool) :
    sourceLoop sourceBody sourceAfter fuel world replies =
      targetLoop targetBody targetAfter fuel world replies := by
  induction fuel generalizing world replies with
  | zero => simp [sourceLoop, targetLoop, after]
  | succ n ih =>
      simp only [sourceLoop, targetLoop, body]
      cases found : (targetBody world replies).exit <;> simp [ih, prependExecution]

theorem lower_eval_exact {World : Type} (p : Protocol) (host : Host World)
    (body : Body) (target : CStmt) (lowered : lower p body = some target)
    (world : World) (replies : List Bool) :
    evalSource p host body world replies = evalC host target world replies := by
  induction body generalizing target world replies with
  | ret outcome => cases Option.some.inj lowered; rfl
  | cont => cases Option.some.inj lowered; rfl
  | call id yes no ihYes ihNo =>
      cases found : findHook (metadata p) id with
      | none => simp [lower, found] at lowered
      | some hook =>
          cases hy : lower p yes <;> cases hn : lower p no <;>
            simp [lower, found, hy, hn] at lowered
          subst target
          cases replies with
          | nil => simp [evalSource, evalC, found]
          | cons reply rest => cases reply <;> simp [evalSource, evalC, found, ihYes _ hy, ihNo _ hn]
  | acquire id yes no ihYes ihNo =>
      cases found : findResource (metadata p) id with
      | none => simp [lower, found] at lowered
      | some resource =>
          cases hy : lower p yes <;> cases hn : lower p no <;>
            simp [lower, found, hy, hn] at lowered
          subst target
          cases replies with
          | nil => simp [evalSource, evalC, found]
          | cons reply rest => cases reply <;> simp [evalSource, evalC, found, ihYes _ hy, ihNo _ hn]
  | release id next ih =>
      cases found : findResource (metadata p) id with
      | none => simp [lower, found] at lowered
      | some resource =>
          cases hn : lower p next <;> simp [lower, found, hn] at lowered
          subst target
          simp [evalSource, evalC, found, ih _ hn]
  | transfer id next ih =>
      cases found : findResource (metadata p) id with
      | none => simp [lower, found] at lowered
      | some resource =>
          cases hn : lower p next <;> simp [lower, found, hn] at lowered
          subst target
          simp [evalSource, evalC, found, ih _ hn]
  | loop bound body after ihBody ihAfter =>
      cases hb : lower p body <;> cases ha : lower p after <;> simp [lower, hb, ha] at lowered
      subst target
      exact congrArg Iteration.execution (iteration_exact _ _ _ _
        (ihBody _ hb) (ihAfter _ ha) _ world replies)

theorem targetLoop_turns_le {World : Type} (body after : World → List Bool → Execution World)
    (fuel : Nat) (world : World) (replies : List Bool) :
    (targetLoop body after fuel world replies).turns ≤ fuel := by
  rw [← iteration_exact body after body after (fun _ _ => rfl) (fun _ _ => rfl)]
  exact sourceLoop_turns_le body after fuel world replies

theorem sourceLoop_retains_charges {World : Type} (body after : World → List Bool → Execution World)
    (charge : Event → Nat) (fuel : Nat) (world : World) (replies : List Bool)
    (pending : (body world replies).exit = .again) :
    invoice charge (body world replies).calls ≤
      invoice charge (sourceLoop body after (fuel+1) world replies).execution.calls := by
  simp only [sourceLoop, pending, prependExecution, invoice_append]
  exact Nat.le_add_right _ _

structure Plan where
  source : Protocol
  target : CStmt
  deriving DecidableEq, Repr

def checkPlan (plan : Plan) : Bool :=
  check plan.source && decide (lower plan.source plan.source.body = some plan.target)

structure PlanValid (plan : Plan) : Prop where
  source : Valid plan.source
  lowering : lower plan.source plan.source.body = some plan.target

theorem checkPlan_iff (plan : Plan) : checkPlan plan = true ↔ PlanValid plan := by
  simp only [checkPlan, Bool.and_eq_true, check_iff, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.source, h.lowering⟩⟩

theorem changed_target_refused {plan : Plan} (valid : PlanValid plan)
    (target : CStmt) (different : target ≠ plan.target) :
    checkPlan { plan with target := target } = false := by
  have unequal : plan.target ≠ target := Ne.symm different
  simp [checkPlan, valid.lowering, unequal]

theorem PlanValid.eval_exact {World : Type} {plan : Plan} (valid : PlanValid plan)
    (host : Host World) (world : World) (replies : List Bool) :
    evalSource plan.source host plan.source.body world replies =
      evalC host plan.target world replies :=
  lower_eval_exact plan.source host plan.source.body plan.target valid.lowering world replies

end Mettapedia.GSLT.LanguageDef.ExecutableProtocol.Loops
