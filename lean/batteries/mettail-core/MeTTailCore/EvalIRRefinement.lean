import MeTTailCore.EvalIRMachine

namespace MeTTailCore.EvalIRRefinement

open MeTTailCore.EvalIR
open MeTTailCore.EvalIRMachine

/-- Encode the tree-shaped `EvalIR.ReqId` into a numeric request identifier for the
    abstract worklist machine.

    Positive example: `.root` maps to `0`.
    Negative example: this encoding is not claiming that unrelated scheduler states
    are already valid worklist states; it is only a request-id transport. -/
def reqIdCode : MeTTailCore.EvalIR.ReqId → Nat
  | .root => 0
  | .sub0 rid => 2 * reqIdCode rid + 1
  | .sub1 rid => 2 * reqIdCode rid + 2
  | .cond rid => 2 * reqIdCode rid + 3
  | .arg i rid => 2 * reqIdCode rid + 4 + i

/-- Extract a canonical worklist `CallKey` from a scheduler node, if that node is
    already a value-keyed user call.

    Positive example: `.userCall "fib" [.intLit 5]` projects to `some ⟨"fib", [.int 5]⟩`.
    Negative example: `.userCall "fib" [.subInt (.intLit 5) (.intLit 1)]` projects to
    `none`, because the argument is still syntax. -/
def callKeyOfNode? : EvalNode → Option CallKey
  | .userCall head args =>
    match argsToValues? args with
    | some vals => some ⟨head, vals⟩
    | none => none
  | _ => none

/-- If a scheduler node projects to a `CallKey`, then the node is exactly the
    corresponding user call on literalized values. -/
theorem callKeyOfNode?_sound {node : EvalNode} {ck : CallKey}
    (h : callKeyOfNode? node = some ck) :
    node = .userCall ck.head (ck.args.map EvalValue.toNode) := by
  cases node with
  | intLit n => simp [callKeyOfNode?] at h
  | boolLit b => simp [callKeyOfNode?] at h
  | ifCond c t e => simp [callKeyOfNode?] at h
  | eqInt a b => simp [callKeyOfNode?] at h
  | addInt a b => simp [callKeyOfNode?] at h
  | subInt a b => simp [callKeyOfNode?] at h
  | mulInt a b => simp [callKeyOfNode?] at h
  | strLit s => simp [callKeyOfNode?] at h
  | eqStr a b => simp [callKeyOfNode?] at h
  | userCall head args =>
    unfold callKeyOfNode? at h
    cases hArgs : argsToValues? args <;> simp [hArgs] at h
    case some vals =>
      cases h
      simp [argsToValues?_sound hArgs]

/-- Project one scheduler fact into the abstract worklist vocabulary when possible.
    Facts that are not yet at the canonical call level project to `none`. -/
def projectFact? : MM2Fact → Option Fact
  | .req rid node =>
    match callKeyOfNode? node with
    | some ck => some (.need (reqIdCode rid) ck)
    | none => none
  | .res rid v => some (.done (reqIdCode rid) v)
  | .memo head vals v => some (.memo ⟨head, vals⟩ v)
  | _ => none

/-- Project a scheduler/MM2 configuration into the abstract worklist fact space. -/
def projectConfig (facts : List MM2Fact) : Config :=
  facts.filterMap projectFact?

/-- Scheduler facts refine the abstract worklist machine when their projection is
    reachable from the abstract initial configuration for the same root call.

    Positive example: a fib scheduler run refines the abstract fib worklist machine
    once its projected facts are reachable from `initialConfig (fibCall n)`.
    Negative example: raw scheduler facts do not refine automatically; the reachability
    witness must still be provided or proved. -/
def Refines (rules : List EvalRule) (rootCall : CallKey) (facts : List MM2Fact) : Prop :=
  Reaches rules (initialConfig rootCall) (projectConfig facts)

/-- Generic membership bridge: if a fact appears in the scheduler config and projects
    to a worklist fact, then that worklist fact appears in the projected config. -/
theorem mem_projectConfig_of_projectFact
    {facts : List MM2Fact} {f : MM2Fact} {wf : Fact}
    (hmem : f ∈ facts) (hproj : projectFact? f = some wf) :
    wf ∈ projectConfig facts := by
  unfold projectConfig
  exact List.mem_filterMap.mpr ⟨f, hmem, hproj⟩

/-- Memo facts project directly to abstract machine memo facts. -/
theorem projectConfig_mem_memo
    {facts : List MM2Fact} {head : String} {vals : List EvalValue} {v : EvalValue}
    (hmem : .memo head vals v ∈ facts) :
    Fact.memo ⟨head, vals⟩ v ∈ projectConfig facts := by
  exact mem_projectConfig_of_projectFact hmem (by simp [projectFact?])

/-- Result facts project directly to abstract machine done facts. -/
theorem projectConfig_mem_done
    {facts : List MM2Fact} {rid : MeTTailCore.EvalIR.ReqId} {v : EvalValue}
    (hmem : .res rid v ∈ facts) :
    Fact.done (reqIdCode rid) v ∈ projectConfig facts := by
  exact mem_projectConfig_of_projectFact hmem (by simp [projectFact?])

/-- Canonical literal user-call requests project to abstract machine need facts. -/
theorem projectConfig_mem_need_of_userCall
    {facts : List MM2Fact} {rid : MeTTailCore.EvalIR.ReqId}
    {head : String} {args : List EvalNode} {vals : List EvalValue}
    (hReq : .req rid (.userCall head args) ∈ facts)
    (hVals : argsToValues? args = some vals) :
    Fact.need (reqIdCode rid) ⟨head, vals⟩ ∈ projectConfig facts := by
  exact mem_projectConfig_of_projectFact hReq (by
    simp [projectFact?, callKeyOfNode?, hVals])

/-- Any abstract-machine `need` fact in the projection really came from a scheduler
    request on a value-keyed user call.

    Positive example: if `.need 0 (fibCall 5)` appears in the projection, then the
    scheduler config contains `.req .root (.userCall "fib" [.intLit 5])`.
    Negative example: syntax-keyed requests like `.req r (.userCall "fib" [.subInt ...])`
    do not project to a `need` fact at all. -/
theorem projectConfig_need_source
    {facts : List MM2Fact} {rid : Nat} {ck : CallKey}
    (hNeed : Fact.need rid ck ∈ projectConfig facts) :
    ∃ srid args,
      MM2Fact.req srid (.userCall ck.head args) ∈ facts ∧
      reqIdCode srid = rid ∧
      argsToValues? args = some ck.args := by
  unfold projectConfig at hNeed
  rcases List.mem_filterMap.mp hNeed with ⟨f, hfMem, hfProj⟩
  cases f with
  | req srid node =>
    cases node with
    | userCall head args =>
      unfold projectFact? callKeyOfNode? at hfProj
      cases hArgs : argsToValues? args <;> simp [hArgs] at hfProj
      case some vals =>
        rcases hfProj with ⟨hRid, hCk⟩
        cases hRid
        cases hCk
        exact ⟨srid, args, hfMem, rfl, hArgs⟩
    | intLit n =>
      simp [projectFact?, callKeyOfNode?] at hfProj
    | boolLit b =>
      simp [projectFact?, callKeyOfNode?] at hfProj
    | ifCond c t e =>
      simp [projectFact?, callKeyOfNode?] at hfProj
    | eqInt a b =>
      simp [projectFact?, callKeyOfNode?] at hfProj
    | addInt a b =>
      simp [projectFact?, callKeyOfNode?] at hfProj
    | subInt a b =>
      simp [projectFact?, callKeyOfNode?] at hfProj
    | mulInt a b =>
      simp [projectFact?, callKeyOfNode?] at hfProj
    | strLit s =>
      simp [projectFact?, callKeyOfNode?] at hfProj
    | eqStr a b =>
      simp [projectFact?, callKeyOfNode?] at hfProj
  | res srid v =>
    simp [projectFact?] at hfProj
  | waitIf srid t e =>
    simp [projectFact?] at hfProj
  | waitArith op srid =>
    simp [projectFact?] at hfProj
  | waitUser srid head argc =>
    simp [projectFact?] at hfProj
  | memo head vals v =>
    simp [projectFact?] at hfProj
  | memoPending srid head vals =>
    simp [projectFact?] at hfProj

/-- `extractResult` witnesses a root result fact, which projects to the abstract
    machine's root `done` fact. -/
theorem extractResult_projects_root_done
    {facts : List MM2Fact} {v : EvalValue}
    (h : extractResult facts = some v) :
    Fact.done (reqIdCode .root) v ∈ projectConfig facts := by
  unfold extractResult at h
  obtain ⟨f, hf_mem, hf_some⟩ := List.exists_of_findSome?_eq_some h
  cases f with
  | req rid node => simp at hf_some
  | res rid w =>
    cases rid <;> simp at hf_some
    cases hf_some
    exact projectConfig_mem_done hf_mem
  | waitIf rid t e => simp at hf_some
  | waitArith op rid => simp at hf_some
  | waitUser rid head argc => simp at hf_some
  | memo head vals w => simp at hf_some
  | memoPending rid head vals => simp at hf_some

/-- The generic scheduler's canonical fib root request projects exactly to the
    abstract worklist machine's initial need fact. -/
theorem projectConfig_fibRoot (n : Int) :
    projectConfig [.req .root (.userCall "fib" [.intLit n])] =
      [.need 0 (fibCall n)] := by
  rfl

/-- First refinement bridge: if the projected scheduler configuration is reachable
    in the abstract worklist machine, then every scheduler-level memo fact is
    semantically correct.

    Positive example: once the fib scheduler run projects to a reachable abstract
    config, `(memo "fib" [.int 5] (.int 5))` certifies `EvalSem fibRules (fib 5) 5`.
    Negative example: this does not by itself prove reachability of the projected
    config; that is the next refinement theorem. -/
theorem projectConfig_memo_sound_of_reaches
    {rules : List EvalRule} {rootCall : CallKey} {facts : List MM2Fact}
    {head : String} {vals : List EvalValue} {v : EvalValue}
    (hReach : Reaches rules (initialConfig rootCall) (projectConfig facts))
    (hMemo : MM2Fact.memo head vals v ∈ facts) :
    EvalSem rules (.userCall head (vals.map EvalValue.toNode)) v := by
  exact machine_memo_sound hReach ⟨head, vals⟩ v (projectConfig_mem_memo hMemo)

/-- If the projected scheduler configuration is reachable in the abstract worklist
    machine, then any extracted root result from the scheduler is backed by an
    abstract-machine `done` fact, and therefore by semantic correctness.

    Positive example: for a reachable projected fib run, `extractResult = some (.int 5)`
    yields an `EvalSem` witness for that answer.
    Negative example: this theorem still leaves the specific root-call identity implicit;
    the current abstract machine proves answer soundness, not yet root-request identity. -/
theorem extractResult_sound_of_projectReaches
    {rules : List EvalRule} {rootCall : CallKey} {facts : List MM2Fact} {v : EvalValue}
    (hReach : Reaches rules (initialConfig rootCall) (projectConfig facts))
    (hResult : extractResult facts = some v) :
    ∃ ck : CallKey, EvalSem rules (.userCall ck.head (ck.args.map EvalValue.toNode)) v := by
  exact machine_done_sound hReach (reqIdCode .root) v (extractResult_projects_root_done hResult)

/-- Refinement-packaged memo soundness: this is the ergonomic form intended to guide
    the Rust side. Once a scheduler state is proved to refine the abstract machine,
    every projected memo fact is semantically correct. -/
theorem Refines.memo_sound
    {rules : List EvalRule} {rootCall : CallKey} {facts : List MM2Fact}
    (hRef : Refines rules rootCall facts)
    {head : String} {vals : List EvalValue} {v : EvalValue}
    (hMemo : MM2Fact.memo head vals v ∈ facts) :
    EvalSem rules (.userCall head (vals.map EvalValue.toNode)) v :=
  projectConfig_memo_sound_of_reaches hRef hMemo

/-- Refinement-packaged root-answer soundness. -/
theorem Refines.extractResult_sound
    {rules : List EvalRule} {rootCall : CallKey} {facts : List MM2Fact}
    (hRef : Refines rules rootCall facts)
    {v : EvalValue}
    (hResult : extractResult facts = some v) :
    ∃ ck : CallKey, EvalSem rules (.userCall ck.head (ck.args.map EvalValue.toNode)) v :=
  extractResult_sound_of_projectReaches hRef hResult

/-- First concrete scheduler-step bridge: a successful `tryMemoHit` exposes exactly
    the abstract ingredients of a worklist-machine memo-hit.

    Positive example: before the scheduler short-circuits `fib(5)` from the memo,
    the projection contains both `.need 0 (fibCall 5)` and `.memo (fibCall 5) 5`,
    and afterwards it contains the matching `.done 0 5`.
    Negative example: this does not yet identify the *entire* projected next config
    with an abstract `Step.memoHit` target; it only proves the key abstract facts
    are present. -/
theorem tryMemoHit_projects_memoHit
    {facts facts' : List MM2Fact}
    (hTry : tryMemoHit facts = some facts') :
    ∃ srid head vals v,
      Fact.need (reqIdCode srid) ⟨head, vals⟩ ∈ projectConfig facts ∧
      Fact.memo ⟨head, vals⟩ v ∈ projectConfig facts ∧
      Fact.done (reqIdCode srid) v ∈ projectConfig facts' := by
  unfold tryMemoHit at hTry
  obtain ⟨f, hfMem, hfSome⟩ := List.exists_of_findSome?_eq_some hTry
  cases f with
  | req srid node =>
    cases node with
    | userCall head args =>
      cases hArgs : argsToValues? args <;> simp [hArgs] at hfSome
      case some vals =>
        obtain ⟨g, hgMem, hgSome⟩ := List.exists_of_findSome?_eq_some hfSome
        cases g with
        | memo h vs v =>
          simp at hgSome
          rcases hgSome with ⟨hh, hFacts'⟩
          rcases hh with ⟨hHead, hVals⟩
          subst hHead
          subst hVals
          subst hFacts'
          refine ⟨srid, h, vs, v, ?_, ?_, ?_⟩
          · exact projectConfig_mem_need_of_userCall hfMem hArgs
          · exact projectConfig_mem_memo hgMem
          · apply projectConfig_mem_done
            simp
        | req rid node =>
          simp at hgSome
        | res rid v =>
          simp at hgSome
        | waitIf rid t e =>
          simp at hgSome
        | waitArith op rid =>
          simp at hgSome
        | waitUser rid head argc =>
          simp at hgSome
        | memoPending rid head vals =>
          simp at hgSome
    | intLit n =>
      simp at hfSome
    | boolLit b =>
      simp at hfSome
    | ifCond c t e =>
      simp at hfSome
    | eqInt a b =>
      simp at hfSome
    | addInt a b =>
      simp at hfSome
    | subInt a b =>
      simp at hfSome
    | mulInt a b =>
      simp at hfSome
    | strLit s =>
      simp at hfSome
    | eqStr a b =>
      simp at hfSome
  | res rid v =>
    simp at hfSome
  | waitIf rid t e =>
    simp at hfSome
  | waitArith op rid =>
    simp at hfSome
  | waitUser rid head argc =>
    simp at hfSome
  | memo head vals v =>
    simp at hfSome
  | memoPending rid head vals =>
    simp at hfSome

/-- Second concrete scheduler-step bridge: a successful `tryMemoStore` turns an
    existing root-local result into a projected abstract memo fact.

    Positive example: once `(memoPending root "fib" [5])` and `(res root 5)` coexist,
    the scheduler can materialize projected `.memo (fib 5) 5`.
    Negative example: this theorem does not yet say that the abstract machine has a
    corresponding single-step constructor for memo-store; it only exposes the abstract
    fact change that Rust must preserve. -/
theorem tryMemoStore_projects_memo
    {facts facts' : List MM2Fact}
    (hTry : tryMemoStore facts = some facts') :
    ∃ srid head vals v,
      MM2Fact.memoPending srid head vals ∈ facts ∧
      Fact.done (reqIdCode srid) v ∈ projectConfig facts ∧
      Fact.memo ⟨head, vals⟩ v ∈ projectConfig facts' := by
  unfold tryMemoStore at hTry
  obtain ⟨f, hfMem, hfSome⟩ := List.exists_of_findSome?_eq_some hTry
  cases f with
  | memoPending srid head vals =>
    obtain ⟨g, hgMem, hgSome⟩ := List.exists_of_findSome?_eq_some hfSome
    cases g with
    | res rid v =>
      simp at hgSome
      rcases hgSome with ⟨hRid, hFacts'⟩
      subst rid
      subst hFacts'
      refine ⟨srid, head, vals, v, hfMem, ?_, ?_⟩
      · exact projectConfig_mem_done hgMem
      · apply projectConfig_mem_memo
        simp
    | req rid node =>
      simp at hgSome
    | waitIf rid t e =>
      simp at hgSome
    | waitArith op rid =>
      simp at hgSome
    | waitUser rid head argc =>
      simp at hgSome
    | memo head vals v =>
      simp at hgSome
    | memoPending rid head vals =>
      simp at hgSome
  | req rid node =>
    simp at hfSome
  | res rid v =>
    simp at hfSome
  | waitIf rid t e =>
    simp at hfSome
  | waitArith op rid =>
    simp at hfSome
  | waitUser rid head argc =>
    simp at hfSome
  | memo head vals v =>
    simp at hfSome

open MeTTailCore.EvalIR in
#eval
  let facts := runToFixpoint fibRules [MM2Fact.req .root (.userCall "fib" [.intLit 5])] 2000
  if Fact.done 0 (.int 5) ∈ projectConfig facts
  then "refinement: projected root done for fib(5) ✓"
  else "FAIL: projected root done for fib(5) missing"

open MeTTailCore.EvalIR in
#eval
  let facts := runToFixpoint fibRules [MM2Fact.req .root (.userCall "fib" [.intLit 5])] 2000
  if Fact.memo (fibCall 5) (.int 5) ∈ projectConfig facts
  then "refinement: projected memo for fib(5) ✓"
  else "FAIL: projected memo for fib(5) missing"

-- ── Value-key discipline: round-trip theorem ────────────────────────────
-- Council: Carneiro/Buzzard — pure round-trip, prevents syntax-keyed memo bug.

/-- evalNodeToValue? is a left inverse of EvalValue.toNode. -/
theorem evalNodeToValue?_toNode (v : EvalValue) :
    evalNodeToValue? v.toNode = some v := by
  cases v <;> simp [EvalValue.toNode, evalNodeToValue?]

/-- argsToValues? round-trips through EvalValue.toNode mapping.
    This is the core value-key discipline contract: memo keys created from
    evaluated values will always be recognized as value-keyed. -/
theorem argsToValues?_toNode_roundtrip (vs : List EvalValue) :
    argsToValues? (vs.map EvalValue.toNode) = some vs := by
  induction vs with
  | nil => simp [argsToValues?]
  | cons v rest ih =>
    simp [argsToValues?, evalNodeToValue?_toNode, ih]

/-- Third concrete scheduler-step bridge: once `waitUser` has collected all arg
    subresults, the scheduler reconstructs a literal-arg user call whose projection
    is a canonical abstract `need` fact.

    Positive example: after collecting `(res (arg 0 root) 4)` and
    `(res (arg 1 root) 3)`, the reconstructed request projects to
    `.need 0 ⟨head, [.int 4, .int 3]⟩`.
    Negative example: this theorem does not say anything when arg collection is
    incomplete; in that case `tryCollectUserArgs` returns `none` and no projected
    `need` is formed yet. -/
theorem tryCollectUserArgs_projects_need
    {facts facts' : List MM2Fact}
    (hTry : tryCollectUserArgs facts = some facts') :
    ∃ srid head argCount vals,
      MM2Fact.waitUser srid head argCount ∈ facts ∧
      Fact.need (reqIdCode srid) ⟨head, vals⟩ ∈ projectConfig facts' := by
  unfold tryCollectUserArgs at hTry
  obtain ⟨f, hfMem, hfSome⟩ := List.exists_of_findSome?_eq_some hTry
  cases f with
  | waitUser srid head argCount =>
    cases hVals : collectedArgValues? facts srid argCount <;> simp [hVals] at hfSome
    case some vals =>
      cases hfSome
      refine ⟨srid, head, argCount, vals, hfMem, ?_⟩
      apply projectConfig_mem_need_of_userCall
      · show MM2Fact.req srid (EvalNode.userCall head (List.map EvalValue.toNode vals)) ∈
            removeFacts facts
              (MM2Fact.waitUser srid head argCount ::
                List.filterMap
                  (fun i =>
                    match vals[i]? with
                    | some v => some (MM2Fact.res (ReqId.arg i srid) v)
                    | none => none)
                  (List.range argCount)) ++
              [MM2Fact.req srid (EvalNode.userCall head (List.map EvalValue.toNode vals))]
        simp
      · simpa using argsToValues?_toNode_roundtrip vals
  | req rid node =>
    simp at hfSome
  | res rid v =>
    simp at hfSome
  | waitIf rid t e =>
    simp at hfSome
  | waitArith op rid =>
    simp at hfSome
  | memo head vals v =>
    simp at hfSome
  | memoPending rid head vals =>
    simp at hfSome

/-- Fourth concrete scheduler-step bridge: a successful literal-arg user-call
    expansion preserves the value-key on the scheduler side by emitting a
    `memoPending` fact keyed by evaluated args, plus a body request to evaluate.

    Positive example: `(req root (fib [5]))` expands to a body request together
    with `(memoPending root "fib" [.int 5])`.
    Negative example: this theorem does not claim the body request itself projects
    to an abstract `need`; the body is still general syntax and belongs to the
    backend/body-evaluation side of the hybrid protocol. -/
theorem tryExpandLiteralUserCall_projects_pending
    {rules : List EvalRule} {facts facts' : List MM2Fact}
    (hTry : tryExpandLiteralUserCall rules facts = some facts') :
    ∃ srid head vals body,
      Fact.need (reqIdCode srid) ⟨head, vals⟩ ∈ projectConfig facts ∧
      MM2Fact.memoPending srid head vals ∈ facts' ∧
      MM2Fact.req srid body ∈ facts' := by
  unfold tryExpandLiteralUserCall at hTry
  obtain ⟨f, hfMem, hfSome⟩ := List.exists_of_findSome?_eq_some hTry
  cases f with
  | req srid node =>
    cases node with
    | userCall head args =>
      cases hVals : argsToValues? args <;> simp [hVals] at hfSome
      case some vals =>
        cases hRule : lookupRule rules head args.length <;> simp [hRule] at hfSome
        case some rule =>
          cases hfSome
          refine ⟨srid, head, vals, substNode (rule.params.zip args) rule.body, ?_, ?_, ?_⟩
          · exact projectConfig_mem_need_of_userCall hfMem hVals
          · simp
          · simp
    | intLit n =>
      simp at hfSome
    | boolLit b =>
      simp at hfSome
    | ifCond c t e =>
      simp at hfSome
    | eqInt a b =>
      simp at hfSome
    | addInt a b =>
      simp at hfSome
    | subInt a b =>
      simp at hfSome
    | mulInt a b =>
      simp at hfSome
    | strLit s =>
      simp at hfSome
    | eqStr a b =>
      simp at hfSome
  | res rid v =>
    simp at hfSome
  | waitIf rid t e =>
    simp at hfSome
  | waitArith op rid =>
    simp at hfSome
  | waitUser rid head argc =>
    simp at hfSome
  | memo head vals v =>
    simp at hfSome
  | memoPending rid head vals =>
    simp at hfSome

/-- Fifth concrete scheduler-step bridge: when a user call is not yet value-keyed,
    the scheduler does not create a canonical `need` fact. Instead it spawns arg
    subrequests and a `waitUser` frame.

    Positive example: `(req root (fib [(subInt ...)]))` becomes arg requests plus
    `(waitUser root "fib" 1)`.
    Negative example: this step must not invent a value-keyed memo call before the
    arg expressions have been evaluated. -/
theorem trySpawnUserArgReqs_emits_waitUser
    {facts facts' : List MM2Fact}
    (hTry : trySpawnUserArgReqs facts = some facts') :
    ∃ srid head args spawned,
      MM2Fact.req srid (.userCall head args) ∈ facts ∧
      argsToValues? args = none ∧
      spawned =
        (args.zip (List.range args.length)).map
          (fun (p : EvalNode × Nat) => MM2Fact.req (.arg p.2 srid) p.1) ∧
      (∀ f, f ∈ spawned → f ∈ facts') ∧
      MM2Fact.waitUser srid head args.length ∈ facts' := by
  unfold trySpawnUserArgReqs at hTry
  obtain ⟨f, hfMem, hfSome⟩ := List.exists_of_findSome?_eq_some hTry
  cases f with
  | req srid node =>
    cases node with
    | userCall head args =>
      cases hVals : argsToValues? args <;> simp [hVals] at hfSome
      case none =>
        cases hfSome
        let spawned :=
          (args.zip (List.range args.length)).map
            (fun (p : EvalNode × Nat) => MM2Fact.req (.arg p.2 srid) p.1)
        refine ⟨srid, head, args, spawned, hfMem, hVals, rfl, ?_, ?_⟩
        · intro fact hIn
          dsimp [spawned] at hIn
          exact List.mem_append.mpr <| Or.inr <| List.mem_append.mpr <| Or.inl hIn
        · exact List.mem_append.mpr <| Or.inr <| List.mem_append.mpr <| Or.inr (by simp)
    | intLit n =>
      simp at hfSome
    | boolLit b =>
      simp at hfSome
    | ifCond c t e =>
      simp at hfSome
    | eqInt a b =>
      simp at hfSome
    | addInt a b =>
      simp at hfSome
    | subInt a b =>
      simp at hfSome
    | mulInt a b =>
      simp at hfSome
    | strLit s =>
      simp at hfSome
    | eqStr a b =>
      simp at hfSome
  | res rid v =>
    simp at hfSome
  | waitIf rid t e =>
    simp at hfSome
  | waitArith op rid =>
    simp at hfSome
  | waitUser rid head argc =>
    simp at hfSome
  | memo head vals v =>
    simp at hfSome
  | memoPending rid head vals =>
    simp at hfSome

-- ── fib(10) validation ──────────────────────────────────────────────────
open MeTTailCore.EvalIR in
#eval
  let facts := runToFixpoint fibRules [MM2Fact.req .root (.userCall "fib" [.intLit 10])] 5000
  let result := extractResult facts
  let projected := projectConfig facts
  if result != some (EvalValue.int 55) then
    s!"FAIL: fib(10) result = {repr result}, expected some (int 55)"
  else if !(Fact.memo (fibCall 10) (EvalValue.int 55) ∈ projected) then
    "FAIL: memo fib(10)=55 missing from projection"
  else if !(Fact.memo (fibCall 0) (EvalValue.int 0) ∈ projected) then
    "FAIL: memo fib(0)=0 missing from projection"
  else if !(Fact.memo (fibCall 5) (EvalValue.int 5) ∈ projected) then
    "FAIL: memo fib(5)=5 missing from projection"
  else
    "refinement: fib(10) = 55 ✓, key memo facts present in projection"

end MeTTailCore.EvalIRRefinement
