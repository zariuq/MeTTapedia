import Mettapedia.GSLT.LanguageDef.ExecutableProtocolLoops
import Mettapedia.GSLT.LanguageDef.ExecutableProtocolInstrumentation

/-!
# Validation at bounded protocol boundaries

The recorded checked target contains its real validation nodes. Continuation
checks the loop-entry facts and the complete owner vector before the next
iteration. Erasure preserves the ordinary target, including the countdown.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ExecutableProtocol.Loops.Instrumentation

open Mettapedia.GSLT.LanguageDef.ExecutableProtocol.Instrumentation
  (Check Validator DeclineKey Request resolveAll factRequests ownerRequests)

inductive IStmt where
  | ret (outcome : Outcome)
  | ifCall (name : String) (yes no : IStmt)
  | voidCall (name : String) (next : IStmt)
  | loop (bound : Bound) (body exhausted : IStmt)
  | cont
  | validate (check : Check) (next : IStmt)
  | tick (reason : DeclineKey) (next : IStmt)
  deriving DecidableEq, Repr

def IStmt.erase : IStmt → CStmt
  | .ret outcome => .ret outcome
  | .ifCall name yes no => .ifCall name yes.erase no.erase
  | .voidCall name next => .voidCall name next.erase
  | .loop bound body exhausted => .loop bound body.erase exhausted.erase
  | .cont => .cont
  | .validate _ next => next.erase
  | .tick _ next => next.erase

def wrap (checks : List Validator) (requests : List Request) (next : IStmt) : Option IStmt := do
  let resolved ← resolveAll checks requests
  pure (resolved.foldr IStmt.validate next)

theorem wrap_erase (checks : List Validator) (requests : List Request) (next result : IStmt)
    (wrapped : wrap checks requests next = some result) : result.erase = next.erase := by
  unfold wrap at wrapped
  cases resolved : resolveAll checks requests with
  | none => simp [resolved] at wrapped
  | some values =>
      simp [resolved] at wrapped
      subst result
      clear resolved
      induction values with
      | nil => rfl
      | cons check rest ih => simpa [List.foldr, IStmt.erase] using ih

def allOwners (p : Protocol) (owned : List String) : List Request :=
  p.resources.map fun r => ⟨.own, r.id, owned.contains r.id⟩

def declaredFacts (p : Protocol) : List String :=
  let values := p.hooks.flatMap (fun h => h.requires ++ h.proves ++ h.invalidates) ++
    p.resources.flatMap (fun r => r.acquireRequires ++ r.transferRequires) ++ p.entryFacts ++
    p.exitFacts.flatMap Prod.snd
  values.foldl (fun seen name => if seen.contains name then seen else seen ++ [name]) []

def continuationRequests (p : Protocol) (entry : Context) : List Request :=
  factRequests ((declaredFacts p).filter entry.facts.contains) ++ allOwners p entry.owned

def instrumentBody (p : Protocol) (checks : List Validator) :
    Option Context → Context → DeclineKey → Body → Option IStmt
  | _, _, key, .ret outcome =>
      wrap checks (factRequests (exitRequires (metadata p) outcome) ++ allOwners p [])
        (if outcome = .declined then .tick key (.ret outcome) else .ret outcome)
  | none, _, _, .cont => none
  | some entry, _, _, .cont => wrap checks (continuationRequests p entry) .cont
  | outer, c, key, .loop bound body exhausted => do
      let entry := loopEntry c
      pure (.loop bound (← instrumentBody p checks (some entry) entry key body)
        (← instrumentBody p checks outer entry key exhausted))
  | loop, c, _, .call id yes no => do
      let h ← findHook (metadata p) id
      let yes' ← instrumentBody p checks loop (callContext c h true) (.afterBool h.cName true) yes
      let no' ← instrumentBody p checks loop (callContext c h false) (.afterBool h.cName false) no
      wrap checks (factRequests h.requires ++ ownerRequests h.uses true)
        (.ifCall h.cName yes' no')
  | loop, c, _, .acquire id yes no => do
      let r ← findResource (metadata p) id
      let yes' ← instrumentBody p checks loop (acquireContext c id true) (.afterBool r.acquire true) yes
      let no' ← instrumentBody p checks loop (acquireContext c id false) (.afterBool r.acquire false) no
      let yes'' ← wrap checks [⟨.own, id, true⟩] yes'
      let no'' ← wrap checks [⟨.own, id, false⟩] no'
      wrap checks (factRequests r.acquireRequires ++ [⟨.own, id, false⟩])
        (.ifCall r.acquire yes'' no'')
  | loop, c, key, .release id next => do
      let r ← findResource (metadata p) id
      let next' ← instrumentBody p checks loop (disposeContext c id) key next
      let after ← wrap checks [⟨.own, id, false⟩] next'
      wrap checks [⟨.own, id, true⟩] (.voidCall r.release after)
  | loop, c, key, .transfer id next => do
      let r ← findResource (metadata p) id
      let next' ← instrumentBody p checks loop (transferContext c id) key next
      let after ← wrap checks [⟨.own, id, false⟩] next'
      let transferred ← wrap checks (factRequests r.transferRequires) (.voidCall r.transfer after)
      wrap checks [⟨.own, id, true⟩] transferred

def instrument (p : Protocol) (checks : List Validator) : Option IStmt := do
  let next ← instrumentBody p checks none (initial p) .entry p.body
  wrap checks (factRequests p.entryFacts ++ allOwners p p.entryOwned) next

theorem instrumentBody_erase (p : Protocol) (checks : List Validator)
    (body : Body) (loop : Option Context) (c : Context) (key : DeclineKey)
    (result : IStmt) (built : instrumentBody p checks loop c key body = some result) :
    lower p body = some result.erase := by
  induction body generalizing loop c key result with
  | ret outcome =>
      simp only [instrumentBody] at built
      have erased := wrap_erase checks
        (factRequests (exitRequires (metadata p) outcome) ++ allOwners p []) _ result built
      split at erased <;> simpa [IStmt.erase, lower] using congrArg some erased.symm
  | cont =>
      cases loop with
      | none => simp [instrumentBody] at built
      | some entry =>
          have erased := wrap_erase checks (continuationRequests p entry) .cont result built
          simpa [lower, IStmt.erase] using congrArg some erased.symm
  | loop bound body exhausted ihBody ihExhausted =>
      cases hb : instrumentBody p checks (some (loopEntry c)) (loopEntry c) key body <;>
        cases he : instrumentBody p checks loop (loopEntry c) key exhausted <;>
          simp [instrumentBody, hb, he] at built
      subst result
      simp [lower, ihBody _ _ _ _ hb, ihExhausted _ _ _ _ he, IStmt.erase]
  | call id yes no ihYes ihNo =>
      cases found : findHook (metadata p) id with
      | none => simp [instrumentBody, found] at built
      | some h =>
          cases hy : instrumentBody p checks loop (callContext c h true) (.afterBool h.cName true) yes <;>
            cases hn : instrumentBody p checks loop (callContext c h false) (.afterBool h.cName false) no <;>
              simp [instrumentBody, found, hy, hn] at built
          have erased := wrap_erase checks (factRequests h.requires ++ ownerRequests h.uses true) _ result built
          rw [erased]
          simp [lower, found, ihYes _ _ _ _ hy, ihNo _ _ _ _ hn, IStmt.erase]
  | acquire id yes no ihYes ihNo =>
      cases found : findResource (metadata p) id with
      | none => simp [instrumentBody, found] at built
      | some r =>
          cases hy : instrumentBody p checks loop (acquireContext c id true) (.afterBool r.acquire true) yes with
          | none => simp [instrumentBody, found, hy] at built
          | some yes' =>
            cases hn : instrumentBody p checks loop (acquireContext c id false) (.afterBool r.acquire false) no with
            | none => simp [instrumentBody, found, hy, hn] at built
            | some no' =>
              cases ha : wrap checks [⟨.own, id, true⟩] yes' with
              | none => simp [instrumentBody, found, hy, hn, ha] at built
              | some checkedYes =>
                cases hf : wrap checks [⟨.own, id, false⟩] no' with
                | none => simp [instrumentBody, found, hy, hn, hf] at built
                | some checkedNo =>
                  simp [instrumentBody, found, hy, hn, ha, hf] at built
                  have erased := wrap_erase checks (factRequests r.acquireRequires ++ [⟨.own, id, false⟩]) _ result built
                  rw [erased]
                  simp [lower, found, IStmt.erase, wrap_erase _ _ _ _ ha, wrap_erase _ _ _ _ hf,
                    ihYes _ _ _ _ hy, ihNo _ _ _ _ hn]
  | release id next ih =>
      cases found : findResource (metadata p) id with
      | none => simp [instrumentBody, found] at built
      | some r =>
          cases hn : instrumentBody p checks loop (disposeContext c id) key next with
          | none => simp [instrumentBody, found, hn] at built
          | some next' =>
            cases ha : wrap checks [⟨.own, id, false⟩] next' with
            | none => simp [instrumentBody, found, hn, ha] at built
            | some after =>
              simp [instrumentBody, found, hn, ha] at built
              have erased := wrap_erase checks [⟨.own, id, true⟩] _ result built
              rw [erased]
              simp [lower, found, IStmt.erase, wrap_erase _ _ _ _ ha, ih _ _ _ _ hn]
  | transfer id next ih =>
      cases found : findResource (metadata p) id with
      | none => simp [instrumentBody, found] at built
      | some r =>
          cases hn : instrumentBody p checks loop (transferContext c id) key next with
          | none => simp [instrumentBody, found, hn] at built
          | some next' =>
            cases ha : wrap checks [⟨.own, id, false⟩] next' with
            | none => simp [instrumentBody, found, hn, ha] at built
            | some after =>
              cases ht : wrap checks (factRequests r.transferRequires) (.voidCall r.transfer after) with
              | none => simp [instrumentBody, found, hn, ha, ht] at built
              | some transferred =>
                simp [instrumentBody, found, hn, ha, ht] at built
                have erased := wrap_erase checks [⟨.own, id, true⟩] _ result built
                rw [erased, wrap_erase _ _ _ _ ht]
                simp [lower, found, IStmt.erase, wrap_erase _ _ _ _ ha, ih _ _ _ _ hn]

/-! Successful checked execution is defined independently of erasure. A
failed validation has no ordinary continuation. Counters are a separate
observation; `Run` projects only the native world, replies and ordered calls. -/

mutual
inductive Run {World : Type} (host : Host World) (verify : Check → World → Bool) (checked : Bool) :
    IStmt → World → List Bool → Execution World → Prop where
  | ret (outcome : Outcome) (world : World) (replies : List Bool) :
      Run host verify checked (.ret outcome) world replies (stop (.returned outcome) world replies)
  | cont (world : World) (replies : List Bool) :
      Run host verify checked .cont world replies (stop .again world replies)
  | noReply (name : String) (yes no : IStmt) (world : World) :
      Run host verify checked (.ifCall name yes no) world [] (stop (.noReply name) world [])
  | onFalse (name : String) (yes no : IStmt) (world : World) (replies : List Bool) (result : Execution World)
      (after : Run host verify checked no (host.boolean name world false) replies result) :
      Run host verify checked (.ifCall name yes no) world (false :: replies)
        (record (.boolean name false) result)
  | onTrue (name : String) (yes no : IStmt) (world : World) (replies : List Bool) (result : Execution World)
      (after : Run host verify checked yes (host.boolean name world true) replies result) :
      Run host verify checked (.ifCall name yes no) world (true :: replies)
        (record (.boolean name true) result)
  | voidCall (name : String) (next : IStmt) (world : World) (replies : List Bool) (result : Execution World)
      (after : Run host verify checked next (host.void name world) replies result) :
      Run host verify checked (.voidCall name next) world replies (record (.void name) result)
  | validate (check : Check) (next : IStmt) (world : World) (replies : List Bool) (result : Execution World)
      (passes : checked = false ∨ verify check world = check.expected)
      (after : Run host verify checked next world replies result) :
      Run host verify checked (.validate check next) world replies result
  | tick (reason : DeclineKey) (next : IStmt) (world : World) (replies : List Bool) (result : Execution World)
      (after : Run host verify checked next world replies result) :
      Run host verify checked (.tick reason next) world replies result
  | loop (bound : Bound) (body exhausted : IStmt) (world : World) (replies : List Bool) (result : Execution World)
      (iterations : Iterates host verify checked body exhausted (boundValue host world bound) world replies result) :
      Run host verify checked (.loop bound body exhausted) world replies result

inductive Iterates {World : Type} (host : Host World) (verify : Check → World → Bool) (checked : Bool) :
    IStmt → IStmt → Nat → World → List Bool → Execution World → Prop where
  | exhausted (body after : IStmt) (world : World) (replies : List Bool) (result : Execution World)
      (run : Run host verify checked after world replies result) :
      Iterates host verify checked body after 0 world replies result
  | stop (body after : IStmt) (n : Nat) (world : World) (replies : List Bool) (first : Execution World)
      (run : Run host verify checked body world replies first) (finished : first.exit ≠ .again) :
      Iterates host verify checked body after (n+1) world replies first
  | next (body after : IStmt) (n : Nat) (world : World) (replies : List Bool)
      (first rest : Execution World) (run : Run host verify checked body world replies first)
      (continues : first.exit = .again)
      (remaining : Iterates host verify checked body after n first.world first.remaining rest) :
      Iterates host verify checked body after (n+1) world replies (prependExecution first rest)
end

theorem Run.erases {World : Type} {host : Host World} {verify : Check → World → Bool} {checked : Bool}
    {stmt : IStmt} {world : World} {replies : List Bool} {result : Execution World}
    (run : Run host verify checked stmt world replies result) :
    result = evalC host stmt.erase world replies := by
  induction run using Run.rec
      (motive_2 := fun body after fuel world replies result _ =>
        result = (targetLoop (evalC host body.erase) (evalC host after.erase) fuel world replies).execution) with
  | ret => rfl
  | cont => rfl
  | noReply => rfl
  | onFalse _ _ _ _ _ _ _ ih => simp [IStmt.erase, evalC, ih]
  | onTrue _ _ _ _ _ _ _ ih => simp [IStmt.erase, evalC, ih]
  | voidCall _ _ _ _ _ _ ih => simp [IStmt.erase, evalC, ih]
  | validate _ _ _ _ _ _ _ ih => simpa only [IStmt.erase] using ih
  | tick _ _ _ _ _ _ ih => simpa only [IStmt.erase] using ih
  | loop _ _ _ _ _ _ _ ih => simpa only [IStmt.erase, evalC] using ih
  | exhausted _ _ _ _ _ _ ih => simpa only [targetLoop] using ih
  | stop _ _ _ _ _ first _ finished ih =>
      simp only [targetLoop]
      rw [← ih]
      simp [finished]
  | next _ _ _ _ _ first rest _ continues _ ihBody ihRest =>
      simp only [targetLoop]
      rw [← ihBody]
      simp only [continues, if_true]
      rw [← ihRest]
      rfl

theorem Iterates.erases {World : Type} {host : Host World} {verify : Check → World → Bool} {checked : Bool}
    {body after : IStmt} {fuel : Nat} {world : World} {replies : List Bool} {result : Execution World}
    (run : Iterates host verify checked body after fuel world replies result) :
    result = (targetLoop (evalC host body.erase) (evalC host after.erase) fuel world replies).execution := by
  have wrapped : Run host verify checked (.loop (.literal fuel) body after) world replies result :=
    .loop (.literal fuel) body after world replies result run
  simpa only [IStmt.erase, evalC, boundValue] using Run.erases wrapped

theorem failed_validation_stops {World : Type} (host : Host World) (verify : Check → World → Bool)
    (check : Check) (next : IStmt) (world : World) (replies : List Bool) (result : Execution World)
    (failed : verify check world ≠ check.expected) :
    ¬ Run host verify true (.validate check next) world replies result := by
  intro run
  cases run with
  | validate _ _ _ _ _ passes _ =>
      rcases passes with h | h
      · contradiction
      · exact failed h

theorem instrument_erase (p : Protocol) (checks : List Validator) (target : IStmt)
    (built : instrument p checks = some target) : lower p p.body = some target.erase := by
  cases bodyBuilt : instrumentBody p checks none (initial p) .entry p.body with
  | none => simp [instrument, bodyBuilt] at built
  | some body =>
      simp [instrument, bodyBuilt] at built
      have erased := wrap_erase checks (factRequests p.entryFacts ++ allOwners p p.entryOwned) body target built
      rw [erased]
      exact instrumentBody_erase p checks p.body none (initial p) .entry body bodyBuilt

structure CheckedPlan where
  ordinary : Plan
  validators : List Validator
  instrumented : Option IStmt
  deriving DecidableEq, Repr

def checkCheckedPlan (plan : CheckedPlan) : Bool :=
  checkPlan plan.ordinary &&
  ExecutableProtocol.Instrumentation.checkChecks (metadata plan.ordinary.source) plan.validators &&
  decide (instrument plan.ordinary.source plan.validators = plan.instrumented)

structure CheckedPlanValid (plan : CheckedPlan) : Prop where
  ordinary : PlanValid plan.ordinary
  validators : ExecutableProtocol.Instrumentation.ChecksValid (metadata plan.ordinary.source) plan.validators
  instrumentation : instrument plan.ordinary.source plan.validators = plan.instrumented

theorem checkCheckedPlan_iff (plan : CheckedPlan) :
    checkCheckedPlan plan = true ↔ CheckedPlanValid plan := by
  simp only [checkCheckedPlan, Bool.and_eq_true, checkPlan_iff,
    ExecutableProtocol.Instrumentation.checkChecks_iff, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1.1,h.1.2,h.2⟩, fun h => ⟨⟨h.ordinary,h.validators⟩,h.instrumentation⟩⟩

theorem changed_instrumentation_refused {plan : CheckedPlan} (valid : CheckedPlanValid plan)
    (target : Option IStmt) (different : target ≠ plan.instrumented) :
    checkCheckedPlan { plan with instrumented := target } = false := by
  have unequal : plan.instrumented ≠ target := Ne.symm different
  simp [checkCheckedPlan, valid.instrumentation, unequal]

theorem CheckedPlanValid.success_exact {World : Type} {plan : CheckedPlan}
    (valid : CheckedPlanValid plan) (host : Host World) (verify : Check → World → Bool)
    (checked : Bool) (target : IStmt) (present : plan.instrumented = some target)
    (world : World) (replies : List Bool) (result : Execution World)
    (run : Run host verify checked target world replies result) :
    result = evalSource plan.ordinary.source host plan.ordinary.source.body world replies := by
  have erased := instrument_erase plan.ordinary.source plan.validators target
    (valid.instrumentation.trans present)
  have same := Option.some.inj (erased.symm.trans valid.ordinary.lowering)
  rw [Run.erases run, same]
  exact (valid.ordinary.eval_exact host world replies).symm

end Mettapedia.GSLT.LanguageDef.ExecutableProtocol.Loops.Instrumentation
