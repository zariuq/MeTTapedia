import Mettapedia.GSLT.LanguageDef.ExecutableProtocolComposition

/-!
# Checked protocol targets and decline accounting

Instrumentation is a separate target, not an interpretation of extra calls
by the ordinary protocol semantics. Validators are pure observations of the
host world, consume no ordinary Boolean replies, and fail-stop on a mismatch.
The host must justify their purity and their interpretation of declared facts
and ownership. Counter state is separate from the host world; the counter
model uses bounded, saturating unsigned values.

Missing validator mappings make checked lowering unavailable. Disabling
checks or counters skips their operations entirely. Native predicates, macro
overrides, C identifier hygiene and physical counter storage are separate
implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ExecutableProtocol.Instrumentation

inductive CheckKind where
  | fact | own
  deriving DecidableEq, Repr

structure Validator where
  kind : CheckKind
  id : String
  cName : String
  deriving DecidableEq, Repr

structure Check where
  kind : CheckKind
  id : String
  cName : String
  expected : Bool
  deriving DecidableEq, Repr

structure Request where
  kind : CheckKind
  id : String
  expected : Bool
  deriving DecidableEq, Repr

inductive DeclineKey where
  | entry
  | afterBool (cName : String) (reply : Bool)
  deriving DecidableEq, Repr

inductive IStmt where
  | ret (outcome : Outcome)
  | ifCall (cName : String) (yes no : IStmt)
  | voidCall (cName : String) (next : IStmt)
  | validate (check : Check) (next : IStmt)
  | tick (reason : DeclineKey) (next : IStmt)
  deriving DecidableEq, Repr

def IStmt.erase : IStmt → CStmt
  | .ret outcome => .ret outcome
  | .ifCall name yes no => .ifCall name yes.erase no.erase
  | .voidCall name next => .voidCall name next.erase
  | .validate _ next => next.erase
  | .tick _ next => next.erase

def IStmt.validateMany (checks : List Check) (next : IStmt) : IStmt :=
  checks.foldr IStmt.validate next

@[simp] theorem IStmt.erase_validateMany (checks : List Check) (next : IStmt) :
    (validateMany checks next).erase = next.erase := by
  induction checks with
  | nil => rfl
  | cons check rest ih => simpa [validateMany, List.foldr, erase] using ih

def factRequests (facts : List String) : List Request :=
  facts.map fun id => ⟨.fact, id, true⟩

def ownerRequests (ids : List String) (expected : Bool) : List Request :=
  ids.map fun id => ⟨.own, id, expected⟩

def allOwnerRequests (p : Protocol) (owned : List String) : List Request :=
  p.resources.map fun resource => ⟨.own, resource.id, owned.contains resource.id⟩

def findValidator (checks : List Validator) (kind : CheckKind) (id : String) :
    Option Validator := checks.find? fun v => v.kind == kind && v.id == id

def resolve (checks : List Validator) (request : Request) : Option Check := do
  let validator ← findValidator checks request.kind request.id
  pure ⟨request.kind, request.id, validator.cName, request.expected⟩

def resolveAll (checks : List Validator) : List Request → Option (List Check)
  | [] => some []
  | request :: rest => do
      let check ← resolve checks request
      let remaining ← resolveAll checks rest
      pure (check :: remaining)

def wrap (checks : List Validator) (requests : List Request) (next : IStmt) :
    Option IStmt := (resolveAll checks requests).map fun cs => next.validateMany cs

/-- Every source operation contributes its own pre/post checks. The last
ordinary Boolean call determines a decline reason; validation and cleanup
calls do not overwrite it. -/
def instrumentBody (p : Protocol) (checks : List Validator) :
    DeclineKey → Body → Option IStmt
  | last, .ret outcome =>
      wrap checks (factRequests (exitRequires p outcome) ++ allOwnerRequests p [])
        (if outcome = .declined then .tick last (.ret outcome) else .ret outcome)
  | _, .call id yes no => do
      let hook ← findHook p id
      let yes' ← instrumentBody p checks (.afterBool hook.cName true) yes
      let no' ← instrumentBody p checks (.afterBool hook.cName false) no
      wrap checks (factRequests hook.requires ++ ownerRequests hook.uses true)
        (.ifCall hook.cName yes' no')
  | _, .acquire id yes no => do
      let resource ← findResource p id
      let yes' ← instrumentBody p checks (.afterBool resource.acquire true) yes
      let no' ← instrumentBody p checks (.afterBool resource.acquire false) no
      let yes'' ← wrap checks (ownerRequests [id] true) yes'
      let no'' ← wrap checks (ownerRequests [id] false) no'
      wrap checks (factRequests resource.acquireRequires ++ ownerRequests [id] false)
        (.ifCall resource.acquire yes'' no'')
  | last, .release id next => do
      let resource ← findResource p id
      let next' ← instrumentBody p checks last next
      let after ← wrap checks (ownerRequests [id] false) next'
      wrap checks (ownerRequests [id] true) (.voidCall resource.release after)
  | last, .transfer id next => do
      let resource ← findResource p id
      let next' ← instrumentBody p checks last next
      let after ← wrap checks (ownerRequests [id] false) next'
      wrap checks (ownerRequests [id] true ++ factRequests resource.transferRequires)
        (.voidCall resource.transfer after)

def instrument (p : Protocol) (checks : List Validator) : Option IStmt := do
  let body ← instrumentBody p checks .entry p.body
  wrap checks (factRequests p.entryFacts ++ allOwnerRequests p p.entryOwned) body

def declaredFacts (p : Protocol) : List String :=
  p.entryFacts ++ p.hooks.flatMap (fun h => h.requires ++ h.proves ++ h.invalidates) ++
    p.resources.flatMap (fun r => r.acquireRequires ++ r.transferRequires) ++
    p.exitFacts.flatMap Prod.snd

def validatorDeclared (p : Protocol) (v : Validator) : Prop :=
  match v.kind with
  | .fact => v.id ∈ declaredFacts p
  | .own => v.id ∈ p.resources.map Resource.id

instance (p : Protocol) (v : Validator) : Decidable (validatorDeclared p v) := by
  unfold validatorDeclared
  split <;> infer_instance

structure ChecksValid (p : Protocol) (checks : List Validator) : Prop where
  keys : (checks.map fun v => (v.kind, v.id)).Nodup
  names : ∀ v ∈ checks, DeclaredTables.identifier v.cName = true
  declared : ∀ v ∈ checks, validatorDeclared p v

def checkChecks (p : Protocol) (checks : List Validator) : Bool :=
  decide (checks.map fun v => (v.kind, v.id)).Nodup &&
    checks.all (fun v => DeclaredTables.identifier v.cName && decide (validatorDeclared p v))

theorem checkChecks_iff (p : Protocol) (checks : List Validator) :
    checkChecks p checks = true ↔ ChecksValid p checks := by
  simp only [checkChecks, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨keys, properties⟩
    exact ⟨keys, fun v h => (properties v h).1, fun v h => (properties v h).2⟩
  · intro valid
    exact ⟨valid.keys, fun v h => ⟨valid.names v h, valid.declared v h⟩⟩

structure RecordedPlan where
  protocol : Protocol
  checks : List Validator
  target : IStmt
  deriving DecidableEq, Repr

def checkPlan (plan : RecordedPlan) : Bool :=
  ExecutableProtocol.check plan.protocol && checkChecks plan.protocol plan.checks &&
    decide (instrument plan.protocol plan.checks = some plan.target)

structure PlanValid (plan : RecordedPlan) : Prop where
  source : ExecutableProtocol.Valid plan.protocol
  checks : ChecksValid plan.protocol plan.checks
  target : instrument plan.protocol plan.checks = some plan.target

theorem checkPlan_iff (plan : RecordedPlan) :
    checkPlan plan = true ↔ PlanValid plan := by
  simp only [checkPlan, Bool.and_eq_true, ExecutableProtocol.check_iff,
    checkChecks_iff, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.source, h.checks⟩, h.target⟩⟩

def counterBound : Nat := 2 ^ 64

abbrev Counter := Fin counterBound

def counterZero : Counter := ⟨0, by decide⟩

def counterMax : Counter := ⟨counterBound - 1, by decide⟩

def saturatingSucc (counter : Counter) : Counter :=
  if h : counter.val + 1 < counterBound then ⟨counter.val + 1, h⟩ else counter

theorem saturatingSucc_value (counter : Counter) :
    (saturatingSucc counter).val = min (counter.val + 1) (counterBound - 1) := by
  have bound := counter.isLt
  unfold saturatingSucc
  split <;> rename_i h
  · change counter.val + 1 = min (counter.val + 1) (counterBound - 1)
    rw [Nat.min_eq_left (by omega)]
  · change counter.val = min (counter.val + 1) (counterBound - 1)
    rw [Nat.min_eq_right (by omega)]
    omega

@[simp] theorem saturatingSucc_max : saturatingSucc counterMax = counterMax := by
  apply Fin.ext
  rw [saturatingSucc_value]
  decide

abbrev CounterStore := DeclineKey → Counter

def emptyCounters : CounterStore := fun _ => counterZero

def countDecline (store : CounterStore) (key : DeclineKey) : CounterStore :=
  fun query => if query = key then saturatingSucc (store query) else store query

@[simp] theorem countDecline_same (store : CounterStore) (key : DeclineKey) :
    countDecline store key key = saturatingSucc (store key) := by simp [countDecline]

theorem countDecline_other (store : CounterStore) (key query : DeclineKey)
    (different : query ≠ key) : countDecline store key query = store query := by
  simp [countDecline, different]

structure Mode where
  checked : Bool
  counted : Bool
  deriving DecidableEq, Repr

inductive Observation where
  | call (event : Event)
  | validation (check : Check) (actual : Bool)
  | decline (reason : DeclineKey)
  deriving DecidableEq, Repr

def coreCalls (observations : List Observation) : List Event :=
  observations.filterMap fun observation => match observation with
    | .call event => some event
    | _ => none

def declineKeys (observations : List Observation) : List DeclineKey :=
  observations.filterMap fun observation => match observation with
    | .decline key => some key
    | _ => none

inductive IStatus where
  | core (status : Status)
  | failedCheck (check : Check) (actual : Bool)
  deriving DecidableEq, Repr

structure Result (World : Type) where
  status : IStatus
  world : World
  remaining : List Bool
  observations : List Observation
  counters : CounterStore

def halt {World : Type} (status : IStatus) (world : World) (replies : List Bool)
    (counters : CounterStore) : Result World := ⟨status, world, replies, [], counters⟩

def observe {World : Type} (event : Observation) (rest : Result World) : Result World :=
  { rest with observations := event :: rest.observations }

/-- Validators are pure host observations, outside the ordinary reply tape.
Counter storage is private and disjoint from the ordinary host world. -/
def eval {World : Type} (mode : Mode) (host : Host World)
    (validator : String → World → Bool) :
    IStmt → World → List Bool → CounterStore → Result World
  | .ret outcome, world, replies, counters =>
      halt (.core (.returned outcome)) world replies counters
  | .ifCall name yes no, world, replies, counters => match replies with
      | [] => halt (.core (.noReply name)) world [] counters
      | false :: rest => observe (.call (.boolean name false))
          (eval mode host validator no (host.boolean name world false) rest counters)
      | true :: rest => observe (.call (.boolean name true))
          (eval mode host validator yes (host.boolean name world true) rest counters)
  | .voidCall name next, world, replies, counters => observe (.call (.void name))
      (eval mode host validator next (host.void name world) replies counters)
  | .validate check next, world, replies, counters =>
      if mode.checked then
        let actual := validator check.cName world
        observe (.validation check actual)
          (if actual = check.expected then eval mode host validator next world replies counters
            else halt (.failedCheck check actual) world replies counters)
      else eval mode host validator next world replies counters
  | .tick key next, world, replies, counters =>
      if mode.counted then observe (.decline key)
        (eval mode host validator next world replies (countDecline counters key))
      else eval mode host validator next world replies counters

def Result.project {World : Type} (result : Result World) : Option (Execution World) :=
  match result.status with
  | .core status => some ⟨status, result.world, result.remaining, coreCalls result.observations⟩
  | .failedCheck _ _ => none

def lastDecision : DeclineKey → List Event → DeclineKey
  | last, [] => last
  | _, .boolean name reply :: rest => lastDecision (.afterBool name reply) rest
  | last, .void _ :: rest => lastDecision last rest

/-- The only counter instruction is immediately before its declined leaf;
its key is the latest Boolean control decision on the executed path. -/
inductive Disciplined : DeclineKey → IStmt → Prop where
  | ret (last : DeclineKey) (outcome : Outcome) (other : outcome ≠ .declined) :
      Disciplined last (.ret outcome)
  | decline (last : DeclineKey) : Disciplined last (.tick last (.ret .declined))
  | ifCall (last : DeclineKey) (name : String) (yes no : IStmt)
      (onTrue : Disciplined (.afterBool name true) yes)
      (onFalse : Disciplined (.afterBool name false) no) :
      Disciplined last (.ifCall name yes no)
  | voidCall (last : DeclineKey) (name : String) (next : IStmt)
      (after : Disciplined last next) : Disciplined last (.voidCall name next)
  | validate (last : DeclineKey) (check : Check) (next : IStmt)
      (after : Disciplined last next) : Disciplined last (.validate check next)

end Mettapedia.GSLT.LanguageDef.ExecutableProtocol.Instrumentation
