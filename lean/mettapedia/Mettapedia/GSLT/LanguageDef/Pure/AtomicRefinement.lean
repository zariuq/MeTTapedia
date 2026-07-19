/-
# Atomic refinement for the Pure dependent fragment

The neural/search boundary contains one action, `Refine(hole, head)`.  The
checker expands it into the sealed hole/head/spine transition triple.  Lambda
introduction, telescope order, dependent substitution, and terminal checking
remain deterministic elaborator work.
-/

import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.AtomicRefinement
import Mettapedia.GSLT.LanguageDef.Pure.Refinement

namespace Mettapedia.GSLT.LanguageDef.PureAtomicRefinement

open Mettapedia.GSLT.LanguageDef.AtomicRefinement
open Mettapedia.GSLT.LanguageDef.RefinementInterface
open Mettapedia.GSLT.LanguageDef.Pure
open Mettapedia.GSLT.LanguageDef.PureRefinement

/-- Pure uses natural-number hole ids and de Bruijn head indices. -/
abbrev AtomicAction := RefineAction Nat Nat

/-- The exact sealed events forced by one atomic choice at the current hole. -/
def forcedLegacyActions? (core : Core) (action : AtomicAction) : Option (List Action) :=
  match core with
  | .needHole holeId context _target _frames => do
      if action.hole != holeId then none
      let headType ← ctxLookup context action.head
      pure
        [.selectHole action.hole, .selectBoundHead action.head,
          .createDependentSpine headType.piArity]
  | _ => none

/-- Unbudgeted checker effect of one atomic refinement. -/
def rawRefine? (goal : Expr) (core : Core) (action : AtomicAction) : Option Core := do
  let forced ← forcedLegacyActions? core action
  rawRun goal forced core

/-- Unbudgeted atomic execution, used by decoding and equivalence proofs. -/
def rawRunAtomic (goal : Expr) : List AtomicAction → Core → Option Core
  | [], core => some core
  | action :: rest, core => do
      let next ← rawRefine? goal core action
      rawRunAtomic goal rest next

/-- Atomic terminality is an observation on an elaborated, independently typed term. -/
def coreTerminal (goal : Expr) : Core → Prop
  | .done term => inferNf [] term = some goal
  | _ => False

instance coreTerminalDecidable (goal : Expr) (core : Core) :
    Decidable (coreTerminal goal core) := by
  unfold coreTerminal
  split <;> infer_instance

/-- Only construction holes are policy-visible; completed terms have no finish hole. -/
def atomicHoles : Core → List Hole
  | .needHole holeId context target _ => [.term holeId context target]
  | .needHead holeId context target _ => [.term holeId context target]
  | .needSpine holeId context target _ _ _ => [.term holeId context target]
  | .done _ => []
  | .finished _ => []

/-- One atomic budget unit reserves the three sealed effects plus one final check. -/
def legacyBudget (atomicBudget : Nat) : Nat := 3 * atomicBudget + 1

def atomicInitial (goal : Expr) (atomicBudget : Nat) : State :=
  initial goal (legacyBudget atomicBudget)

/-- Budgeted atomic transition, delegated to the sealed filtered runner. -/
def step? (goal : Expr) (state : State) (action : AtomicAction) : Option State := do
  let forced ← forcedLegacyActions? state.core action
  (pureRoot goal).run forced state

/-- Heads exposed to a policy are exactly those accepted by the checker transition. -/
def legalHeads (goal : Expr) (state : State) (hole : Nat) : List Nat :=
  match state.core with
  | .needHole holeId context _ _ =>
      if hole = holeId then
        (List.range context.length).filter fun head =>
          (step? goal state ⟨hole, head⟩).isSome
      else
        []
  | _ => []

/-- Atomic decoding replays checker effects and independently infers the result type. -/
def decode (goal : Expr) (trace : List AtomicAction) : Option Nf :=
  match rawRunAtomic goal trace (prepare 0 [] goal []) with
  | some (.done term) =>
      if inferNf [] term = some goal then some term else none
  | _ => none

mutual
/-- Canonical atomic serialization; lambdas and dependent spines are checker-owned. -/
def encodeNfFuel : Nat → Ctx → Nf → List AtomicAction
  | 0, _, _ => []
  | fuel + 1, context, .lam domain body =>
      encodeNfFuel fuel (domain :: context) body
  | fuel + 1, context, .head index arguments =>
      ⟨0, index⟩ :: encodeArgsFuel fuel context arguments

def encodeArgsFuel : Nat → Ctx → List Nf → List AtomicAction
  | 0, _, _ => []
  | _fuel + 1, _, [] => []
  | fuel + 1, context, argument :: rest =>
      encodeNfFuel fuel context argument ++ encodeArgsFuel fuel context rest
end

def encode (term : Nf) : List AtomicAction :=
  encodeNfFuel (term.weight + 1) [] term

/-- The Pure atomic root.  The old viability predicate remains checker-internal. -/
def pureAtomicRoot (goal : Expr) : AtomicRoot where
  State := State
  Hole := Nat
  Head := Nat
  Program := Nf
  initial := atomicInitial goal
  holes := fun state =>
    match state.core with
    | .needHole holeId _ _ _ => [holeId]
    | _ => []
  legalHeads := legalHeads goal
  refine? := fun state hole head => step? goal state ⟨hole, head⟩
  terminal := fun state => coreTerminal goal state.core
  decode := decode goal
  wellFormed := fun term => HasType [] term goal
  programCost := fun term => (encode term).length
  encode := encode
  invariant := viable goal
  canComplete := viable goal
  budgetOK := fun budget =>
    canComplete goal (prepare 0 [] goal []) (legacyBudget budget) = true

/-- Pure exposes at most one current hole, so the outer support has no repeats. -/
theorem pureAtomicRoot_holes_nodup (goal : Expr) (state : State) :
    ((pureAtomicRoot goal).holes state).Nodup := by
  rcases state with ⟨core, tokensEmitted, maxLen⟩
  cases core <;> simp [pureAtomicRoot]

/-- Pure head support is a filtered range of de Bruijn indices. -/
theorem legalHeads_nodup (goal : Expr) (state : State) (hole : Nat) :
    (legalHeads goal state hole).Nodup := by
  rcases state with ⟨core, tokensEmitted, maxLen⟩
  cases core with
  | needHole holeId context target frames =>
      by_cases heq : hole = holeId
      · rw [show
          legalHeads goal ⟨.needHole holeId context target frames,
            tokensEmitted, maxLen⟩ hole =
            (List.range context.length).filter fun head =>
              (step? goal
                ⟨.needHole holeId context target frames,
                  tokensEmitted, maxLen⟩ ⟨hole, head⟩).isSome by
            simp [legalHeads, heq]]
        exact List.nodup_range.filter _
      · simp [legalHeads, heq]
  | needHead => simp [legalHeads]
  | needSpine => simp [legalHeads]
  | done => simp [legalHeads]
  | finished => simp [legalHeads]

/-- The concrete Pure legal-action enumeration is a genuine partition. -/
theorem pureAtomicRoot_legalActions_nodup (goal : Expr) (state : State) :
    ((pureAtomicRoot goal).legalActions state).Nodup := by
  apply (pureAtomicRoot goal).legalActions_nodup state
  · exact pureAtomicRoot_holes_nodup goal state
  · intro hole
    exact legalHeads_nodup goal state hole

/-- One elaboration record carries both the forced legacy trace and final core. -/
structure Elaboration where
  legacyTrace : List Action
  finalCore : Core
  deriving Repr

/-- Elaborate an atomic trace, recording every checker-forced legacy event. -/
def elaborateFrom? (goal : Expr) :
    List AtomicAction → Core → Option Elaboration
  | [], core => some ⟨[], core⟩
  | action :: rest, core => do
      let forced ← forcedLegacyActions? core action
      let next ← rawRun goal forced core
      let tail ← elaborateFrom? goal rest next
      pure ⟨forced ++ tail.legacyTrace, tail.finalCore⟩

def elaborate? (goal : Expr) (trace : List AtomicAction) : Option Elaboration :=
  elaborateFrom? goal trace (prepare 0 [] goal [])

/-- Accepted atomic traces elaborate to the old trace by adding the forced finish. -/
def expandAccepted? (goal : Expr) (trace : List AtomicAction) : Option (List Action) := do
  let elaboration ← elaborate? goal trace
  if coreTerminal goal elaboration.finalCore then
    pure (elaboration.legacyTrace ++ [.finish])
  else
    none

/-! ## First executable and structural gates -/

theorem forcedLegacyActions?_eq {holeId : Nat} {context : Ctx}
    {target : Expr} {frames : List Frame} {head : Nat} {headType : Expr}
    (hlookup : ctxLookup context head = some headType) :
    forcedLegacyActions? (.needHole holeId context target frames) ⟨holeId, head⟩ =
      some [.selectHole holeId, .selectBoundHead head,
        .createDependentSpine headType.piArity] := by
  simp [forcedLegacyActions?, hlookup]

/-- The complete successor, including substituted dependent slots, is deterministic. -/
theorem rawRefine_successor_deterministic {goal : Expr} {core first second : Core}
    {action : AtomicAction}
    (hfirst : rawRefine? goal core action = some first)
    (hsecond : rawRefine? goal core action = some second) :
    first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

/--
The atomic successor is exactly the sealed checker spine: argument holes are
created in telescope order, and later types are updated by `Expr.subst0` in
`deliver_spine_eq_startSpineWith`.
-/
theorem rawRefine_eq_checkerSpine (goal : Expr) {context : Ctx} {index : Nat}
    {headType target : Expr} {frames : List Frame}
    (hlookup : ctxLookup context index = some headType)
    (hatomic : target.Atomic) :
    rawRefine? goal (prepare 0 context target frames) ⟨0, index⟩ =
      startSpineWith context target frames index [] headType := by
  unfold rawRefine?
  rw [show
    forcedLegacyActions? (prepare 0 context target frames) ⟨0, index⟩ =
      some [.selectHole 0, .selectBoundHead index,
        .createDependentSpine headType.piArity] by
      rw [prepare_atomic hatomic]
      simp [forcedLegacyActions?, hlookup]]
  have hprefix :=
    rawRun_headPrefix goal (context := context) (index := index)
      (headType := headType) (target := target) (frames := frames) []
      hlookup hatomic
  cases hstart : startSpineWith context target frames index [] headType <;>
    simpa [rawRunFrom?, rawRun, hstart] using hprefix

/-- Atomic terminality has no policy action and no exposed construction hole. -/
theorem coreTerminal_holes_empty {goal : Expr} {core : Core}
    (hterminal : coreTerminal goal core) :
    atomicHoles core = [] := by
  cases core <;> simp [coreTerminal, atomicHoles] at hterminal ⊢

/-- Recorded elaboration executes to the recorded checker state. -/
theorem elaborateFrom?_legacy_run (goal : Expr) :
    ∀ {trace : List AtomicAction} {start : Core} {elaboration : Elaboration},
      elaborateFrom? goal trace start = some elaboration →
        rawRun goal elaboration.legacyTrace start = some elaboration.finalCore
  | [], start, elaboration, helab => by
      simp [elaborateFrom?] at helab
      subst elaboration
      rfl
  | action :: rest, start, elaboration, helab => by
      simp only [elaborateFrom?] at helab
      cases hforced : forcedLegacyActions? start action with
      | none => simp [hforced] at helab
      | some forced =>
          cases hstep : rawRun goal forced start with
          | none => simp [hforced, hstep] at helab
          | some next =>
              cases htail : elaborateFrom? goal rest next with
              | none => simp [hforced, hstep, htail] at helab
              | some tail =>
                  simp [hforced, hstep, htail] at helab
                  subst elaboration
                  rw [rawRun_append, hstep]
                  exact elaborateFrom?_legacy_run goal htail

/-- Recorded elaboration and direct atomic execution reach the same checker state. -/
theorem elaborateFrom?_atomic_run (goal : Expr) :
    ∀ {trace : List AtomicAction} {start : Core} {elaboration : Elaboration},
      elaborateFrom? goal trace start = some elaboration →
        rawRunAtomic goal trace start = some elaboration.finalCore
  | [], start, elaboration, helab => by
      simp [elaborateFrom?] at helab
      subst elaboration
      rfl
  | action :: rest, start, elaboration, helab => by
      simp only [elaborateFrom?] at helab
      cases hforced : forcedLegacyActions? start action with
      | none => simp [hforced] at helab
      | some forced =>
          cases hstep : rawRun goal forced start with
          | none => simp [hforced, hstep] at helab
          | some next =>
              cases htail : elaborateFrom? goal rest next with
              | none => simp [hforced, hstep, htail] at helab
              | some tail =>
                  simp [hforced, hstep, htail] at helab
                  subst elaboration
                  have hrefine : rawRefine? goal start action = some next := by
                    simp [rawRefine?, hforced, hstep]
                  simp only [rawRunAtomic, hrefine]
                  exact elaborateFrom?_atomic_run goal htail

/-- Expanding an accepted atomic trace produces a checker-accepted four-event trace. -/
theorem expandAccepted?_legacy_accepts {goal : Expr} {atomicTrace : List AtomicAction}
    {legacyTrace : List Action}
    (hexpand : expandAccepted? goal atomicTrace = some legacyTrace) :
    ∃ term,
      rawRun goal legacyTrace (prepare 0 [] goal []) = some (.finished term) ∧
        inferNf [] term = some goal := by
  unfold expandAccepted? at hexpand
  cases helab : elaborate? goal atomicTrace with
  | none => simp [helab] at hexpand
  | some elaboration =>
      rw [helab] at hexpand
      unfold elaborate? at helab
      by_cases hterminal : coreTerminal goal elaboration.finalCore
      · have hexpand' :
            elaboration.legacyTrace ++ [.finish] = legacyTrace := by
          simpa [hterminal] using hexpand
        generalize hcore : elaboration.finalCore = finalCore at hterminal
        cases finalCore with
        | done term =>
            have hinfer : inferNf [] term = some goal := by
              simpa [coreTerminal] using hterminal
            refine ⟨term, ?_, hinfer⟩
            rw [← hexpand', rawRun_append,
              elaborateFrom?_legacy_run goal helab, hcore]
            simp [rawRun, rawStep, hinfer]
        | needHole holeId context target frames =>
            simp [coreTerminal] at hterminal
        | needHead holeId context target frames =>
            simp [coreTerminal] at hterminal
        | needSpine holeId context target frames head headType =>
            simp [coreTerminal] at hterminal
        | finished term => simp [coreTerminal] at hterminal
      · simp [hterminal] at hexpand

/-! ## Reverse translation and the accepted-trace bijection -/

/-- States at which an atomic policy may act or observe acceptance. -/
inductive Boundary : Core → Prop where
  | needHole (holeId : Nat) (context : Ctx) (target : Expr) (frames : List Frame) :
      Boundary (.needHole holeId context target frames)
  | done (term : Nf) : Boundary (.done term)

theorem prepare_boundary (holeId : Nat) (context : Ctx) (target : Expr)
    (frames : List Frame) : Boundary (prepare holeId context target frames) := by
  induction target generalizing context frames with
  | pi domain body _domainIH bodyIH =>
      exact bodyIH (domain :: context) (.lambda domain :: frames)
  | sort => exact Boundary.needHole ..
  | bvar index => exact Boundary.needHole ..
  | lam domain body domainIH bodyIH => exact Boundary.needHole ..
  | app fn argument fnIH argumentIH => exact Boundary.needHole ..

theorem deliver_boundary : ∀ {term : Nf} {frames : List Frame} {core : Core},
    deliver term frames = some core → Boundary core := by
  intro term frames
  induction frames generalizing term with
  | nil =>
      intro core hdeliver
      simp [deliver] at hdeliver
      subst core
      exact Boundary.done term
  | cons frame rest ih =>
      intro core hdeliver
      cases frame with
      | lambda domain =>
          exact ih (by simpa [deliver] using hdeliver)
      | spine context head arguments body expected =>
          simp only [deliver] at hdeliver
          let arguments' := arguments ++ [term]
          let application := Nf.head head arguments'
          let nextType := Expr.subst0 term.erase body
          by_cases heq : nextType = expected
          · exact ih (by simpa [arguments', application, nextType, heq] using hdeliver)
          · cases hnext : nextType with
            | pi domain nextBody =>
                have hneq : Expr.pi domain nextBody ≠ expected := by
                  simpa [hnext] using heq
                have hcore :
                    prepare 0 context domain
                        (.spine context head arguments' nextBody expected :: rest) = core := by
                  simpa [arguments', application, nextType, hnext, hneq] using hdeliver
                rw [← hcore]
                exact prepare_boundary 0 context domain _
            | sort =>
                have hneq : Expr.sort ≠ expected := by simpa [hnext] using heq
                simp [nextType, hnext, hneq] at hdeliver
            | bvar index =>
                have hneq : Expr.bvar index ≠ expected := by simpa [hnext] using heq
                simp [nextType, hnext, hneq] at hdeliver
            | lam domain body =>
                have hneq : Expr.lam domain body ≠ expected := by
                  simpa [hnext] using heq
                simp [nextType, hnext, hneq] at hdeliver
            | app fn argument =>
                have hneq : Expr.app fn argument ≠ expected := by
                  simpa [hnext] using heq
                simp [nextType, hnext, hneq] at hdeliver

theorem startSpineWith_boundary {context : Ctx} {expected : Expr}
    {frames : List Frame} {head : Nat} {arguments : List Nf} {headType : Expr}
    {core : Core}
    (hstart : startSpineWith context expected frames head arguments headType = some core) :
    Boundary core := by
  cases headType with
  | pi domain body =>
      have hcore :
          prepare 0 context domain
              (.spine context head arguments body expected :: frames) = core := by
        simpa [startSpineWith] using hstart
      rw [← hcore]
      exact prepare_boundary 0 context domain _
  | sort =>
      by_cases heq : Expr.sort = expected
      · exact deliver_boundary (by simpa [startSpineWith, heq] using hstart)
      · simp [startSpineWith, heq] at hstart
  | bvar index =>
      by_cases heq : Expr.bvar index = expected
      · exact deliver_boundary (by simpa [startSpineWith, heq] using hstart)
      · simp [startSpineWith, heq] at hstart
  | lam domain body =>
      by_cases heq : Expr.lam domain body = expected
      · exact deliver_boundary (by simpa [startSpineWith, heq] using hstart)
      · simp [startSpineWith, heq] at hstart
  | app fn argument =>
      by_cases heq : Expr.app fn argument = expected
      · exact deliver_boundary (by simpa [startSpineWith, heq] using hstart)
      · simp [startSpineWith, heq] at hstart

/-- Every successful atomic refinement returns to an atomic boundary. -/
theorem rawRefine_boundary {goal : Expr} {core next : Core} {action : AtomicAction}
    (hstep : rawRefine? goal core action = some next) : Boundary next := by
  cases core with
  | needHole holeId context target frames =>
      unfold rawRefine? forcedLegacyActions? at hstep
      by_cases hhole : action.hole = holeId
      · simp [hhole] at hstep
        cases hlookup : ctxLookup context action.head with
        | none => simp [hlookup] at hstep
        | some headType =>
            simp [hlookup, rawRun, rawStep, startSpine] at hstep
            exact startSpineWith_boundary hstep
      · simp [hhole] at hstep
  | needHead holeId context target frames =>
      simp [rawRefine?, forcedLegacyActions?] at hstep
  | needSpine holeId context target frames head headType =>
      simp [rawRefine?, forcedLegacyActions?] at hstep
  | done term => simp [rawRefine?, forcedLegacyActions?] at hstep
  | finished term => simp [rawRefine?, forcedLegacyActions?] at hstep

/--
Delete only checker-forced triples and the final acceptance event.  The arity
field is checked against the elaborator before it is discarded.
-/
def compressFrom? (goal : Expr) : List Action → Core → Option (List AtomicAction)
  | [.finish], core =>
      if coreTerminal goal core then some [] else none
  | .selectHole hole :: .selectBoundHead head ::
      .createDependentSpine arity :: rest, core => do
      let atomic : AtomicAction := ⟨hole, head⟩
      let forced ← forcedLegacyActions? core atomic
      if forced !=
          [.selectHole hole, .selectBoundHead head,
            .createDependentSpine arity] then
        none
      let next ← rawRun goal forced core
      let tail ← compressFrom? goal rest next
      pure (atomic :: tail)
  | _, _ => none

def compressAccepted? (goal : Expr) (trace : List Action) :
    Option (List AtomicAction) :=
  compressFrom? goal trace (prepare 0 [] goal [])

theorem forcedLegacyActions?_shape {core : Core} {action : AtomicAction}
    {forced : List Action}
    (hforced : forcedLegacyActions? core action = some forced) :
    ∃ arity,
      forced =
        [.selectHole action.hole, .selectBoundHead action.head,
          .createDependentSpine arity] := by
  cases core with
  | needHole holeId context target frames =>
      unfold forcedLegacyActions? at hforced
      by_cases hhole : action.hole = holeId
      · subst holeId
        simp at hforced
        cases hlookup : ctxLookup context action.head with
        | none => simp [hlookup] at hforced
        | some headType =>
            simp [hlookup] at hforced
            subst forced
            exact ⟨headType.piArity, rfl⟩
      · simp [hhole] at hforced
  | needHead holeId context target frames =>
      simp [forcedLegacyActions?] at hforced
  | needSpine holeId context target frames head headType =>
      simp [forcedLegacyActions?] at hforced
  | done term => simp [forcedLegacyActions?] at hforced
  | finished term => simp [forcedLegacyActions?] at hforced

/-- Expanding and then deleting forced effects recovers the atomic trace. -/
theorem compressFrom?_of_elaborate (goal : Expr) :
    ∀ {trace : List AtomicAction} {start : Core} {elaboration : Elaboration},
      elaborateFrom? goal trace start = some elaboration →
      coreTerminal goal elaboration.finalCore →
      compressFrom? goal (elaboration.legacyTrace ++ [.finish]) start = some trace
  | [], start, elaboration, helab, hterminal => by
      simp [elaborateFrom?] at helab
      subst elaboration
      simp [compressFrom?, hterminal]
  | action :: rest, start, elaboration, helab, hterminal => by
      simp only [elaborateFrom?] at helab
      cases hforced : forcedLegacyActions? start action with
      | none => simp [hforced] at helab
      | some forced =>
          cases hstep : rawRun goal forced start with
          | none => simp [hforced, hstep] at helab
          | some next =>
              cases htail : elaborateFrom? goal rest next with
              | none => simp [hforced, hstep, htail] at helab
              | some tail =>
                  simp [hforced, hstep, htail] at helab
                  subst elaboration
                  have hcompressed :=
                    compressFrom?_of_elaborate goal htail hterminal
                  rcases forcedLegacyActions?_shape hforced with ⟨arity, rfl⟩
                  simp [compressFrom?, hforced, hstep, hcompressed]

/-- A successful reverse translation reconstructs one checker elaboration. -/
theorem elaborateFrom?_of_compress (goal : Expr) :
    ∀ {legacyTrace : List Action} {start : Core} {atomicTrace : List AtomicAction},
      compressFrom? goal legacyTrace start = some atomicTrace →
      ∃ elaboration,
        elaborateFrom? goal atomicTrace start = some elaboration ∧
          coreTerminal goal elaboration.finalCore ∧
          legacyTrace = elaboration.legacyTrace ++ [.finish]
  | [.finish], start, atomicTrace, hcompress => by
      by_cases hterminal : coreTerminal goal start
      · simp [compressFrom?, hterminal] at hcompress
        subst atomicTrace
        exact ⟨⟨[], start⟩, rfl, hterminal, rfl⟩
      · simp [compressFrom?, hterminal] at hcompress
  | .selectHole hole :: .selectBoundHead head ::
      .createDependentSpine arity :: rest, start, atomicTrace, hcompress => by
      simp only [compressFrom?] at hcompress
      let atomic : AtomicAction := ⟨hole, head⟩
      cases hforced : forcedLegacyActions? start atomic with
      | none =>
          dsimp [atomic] at hforced
          rw [hforced] at hcompress
          contradiction
      | some forced =>
          dsimp [atomic] at hforced
          rw [hforced] at hcompress
          by_cases heq :
              forced =
                [.selectHole hole, .selectBoundHead head,
                  .createDependentSpine arity]
          · simp [heq] at hcompress
            cases hstep :
                rawRun goal
                  [.selectHole hole, .selectBoundHead head,
                    .createDependentSpine arity] start with
            | none =>
                rw [hstep] at hcompress
                contradiction
            | some next =>
                rw [hstep] at hcompress
                simp only [Option.bind_some] at hcompress
                cases htail : compressFrom? goal rest next with
                | none =>
                    rw [htail] at hcompress
                    contradiction
                | some tail =>
                    rw [htail] at hcompress
                    simp only [Option.bind_some, Option.some.injEq] at hcompress
                    subst atomicTrace
                    rcases elaborateFrom?_of_compress goal htail with
                      ⟨tailElaboration, htailElab, hterminal, hrest⟩
                    let elaboration : Elaboration :=
                      ⟨[.selectHole hole, .selectBoundHead head,
                          .createDependentSpine arity] ++
                          tailElaboration.legacyTrace,
                        tailElaboration.finalCore⟩
                    refine ⟨elaboration, ?_, hterminal, ?_⟩
                    · simp [elaboration, elaborateFrom?, hforced, hstep,
                        heq, htailElab]
                    · rw [hrest]
                      rfl
          · simp [heq] at hcompress
  | legacyTrace, start, atomicTrace, hcompress => by
      cases legacyTrace with
      | nil => simp [compressFrom?] at hcompress
      | cons first rest =>
          cases rest with
          | nil =>
              cases first with
              | finish =>
                  by_cases hterminal : coreTerminal goal start
                  · simp [compressFrom?, hterminal] at hcompress
                    subst atomicTrace
                    exact ⟨⟨[], start⟩, rfl, hterminal, rfl⟩
                  · simp [compressFrom?, hterminal] at hcompress
              | selectHole hole => simp [compressFrom?] at hcompress
              | selectBoundHead head => simp [compressFrom?] at hcompress
              | createDependentSpine arity => simp [compressFrom?] at hcompress
          | cons second rest =>
              cases rest with
              | nil =>
                  cases first <;> cases second <;>
                    simp [compressFrom?] at hcompress
              | cons third rest =>
                  cases first with
                  | selectHole hole =>
                      cases second with
                      | selectBoundHead head =>
                          cases third with
                          | createDependentSpine arity =>
                              simp only [compressFrom?] at hcompress
                              let atomic : AtomicAction := ⟨hole, head⟩
                              cases hforced : forcedLegacyActions? start atomic with
                              | none =>
                                  dsimp [atomic] at hforced
                                  rw [hforced] at hcompress
                                  contradiction
                              | some forced =>
                                  dsimp [atomic] at hforced
                                  rw [hforced] at hcompress
                                  by_cases heq :
                                      forced =
                                        [.selectHole hole, .selectBoundHead head,
                                          .createDependentSpine arity]
                                  · simp [heq] at hcompress
                                    cases hstep :
                                        rawRun goal
                                          [.selectHole hole, .selectBoundHead head,
                                            .createDependentSpine arity] start with
                                    | none =>
                                        rw [hstep] at hcompress
                                        contradiction
                                    | some next =>
                                        rw [hstep] at hcompress
                                        simp only [Option.bind_some] at hcompress
                                        cases htail : compressFrom? goal rest next with
                                        | none =>
                                            rw [htail] at hcompress
                                            contradiction
                                        | some tail =>
                                            rw [htail] at hcompress
                                            simp only [Option.bind_some,
                                              Option.some.injEq] at hcompress
                                            subst atomicTrace
                                            rcases elaborateFrom?_of_compress goal htail with
                                              ⟨tailElaboration, htailElab,
                                                hterminal, hrest⟩
                                            let elaboration : Elaboration :=
                                              ⟨[.selectHole hole,
                                                  .selectBoundHead head,
                                                  .createDependentSpine arity] ++
                                                  tailElaboration.legacyTrace,
                                                tailElaboration.finalCore⟩
                                            refine
                                              ⟨elaboration, ?_, hterminal, ?_⟩
                                            · simp [elaboration, elaborateFrom?,
                                                hforced, hstep, heq, htailElab]
                                            · rw [hrest]
                                              rfl
                                  · simp [heq] at hcompress
                          | selectHole other => simp [compressFrom?] at hcompress
                          | selectBoundHead other => simp [compressFrom?] at hcompress
                          | finish => simp [compressFrom?] at hcompress
                      | selectHole other => simp [compressFrom?] at hcompress
                      | createDependentSpine other => simp [compressFrom?] at hcompress
                      | finish => simp [compressFrom?] at hcompress
                  | selectBoundHead head => simp [compressFrom?] at hcompress
                  | createDependentSpine arity => simp [compressFrom?] at hcompress
                  | finish => simp [compressFrom?] at hcompress

/-- The two executable translations are inverse on accepted atomic traces. -/
theorem compressAccepted?_expandAccepted {goal : Expr}
    {atomicTrace : List AtomicAction} {legacyTrace : List Action}
    (hexpand : expandAccepted? goal atomicTrace = some legacyTrace) :
    compressAccepted? goal legacyTrace = some atomicTrace := by
  unfold expandAccepted? at hexpand
  cases helab : elaborate? goal atomicTrace with
  | none => simp [helab] at hexpand
  | some elaboration =>
      rw [helab] at hexpand
      by_cases hterminal : coreTerminal goal elaboration.finalCore
      · have htrace : elaboration.legacyTrace ++ [.finish] = legacyTrace := by
          simpa [hterminal] using hexpand
        rw [← htrace]
        exact compressFrom?_of_elaborate goal helab hterminal
      · simp [hterminal] at hexpand

/-- The two executable translations are inverse on validated legacy traces. -/
theorem expandAccepted?_compressAccepted {goal : Expr}
    {legacyTrace : List Action} {atomicTrace : List AtomicAction}
    (hcompress : compressAccepted? goal legacyTrace = some atomicTrace) :
    expandAccepted? goal atomicTrace = some legacyTrace := by
  rcases elaborateFrom?_of_compress goal hcompress with
    ⟨elaboration, helab, hterminal, htrace⟩
  simp [expandAccepted?, elaborate?, helab, hterminal, htrace]

/-- Every checker-accepted four-event trace has the forced atomic grammar. -/
theorem legacyRun_compresses (goal : Expr) :
    ∀ {legacyTrace : List Action} {start : Core} {term : Nf},
      Boundary start →
      rawRun goal legacyTrace start = some (.finished term) →
      ∃ atomicTrace, compressFrom? goal legacyTrace start = some atomicTrace
  | [], start, term, _hboundary, hrun => by
      cases _hboundary <;> simp [rawRun] at hrun
  | first :: rest, start, term, hboundary, hrun => by
      cases hboundary with
      | done completed =>
          cases first with
          | finish =>
              by_cases hinfer : inferNf [] completed = some goal
              · cases rest with
                | nil =>
                    exact ⟨[], by simp [compressFrom?, coreTerminal, hinfer]⟩
                | cons next tail =>
                    simp [rawRun, rawStep, hinfer] at hrun
              · simp [rawRun, rawStep, hinfer] at hrun
          | selectHole hole => simp [rawRun, rawStep] at hrun
          | selectBoundHead head => simp [rawRun, rawStep] at hrun
          | createDependentSpine arity => simp [rawRun, rawStep] at hrun
      | needHole holeId context target frames =>
          cases first with
          | selectHole selected =>
              by_cases hselected : selected = holeId
              · subst selected
                cases rest with
                | nil => simp [rawRun, rawStep] at hrun
                | cons second rest =>
                    cases second with
                    | selectBoundHead head =>
                        cases hlookup : ctxLookup context head with
                        | none => simp [rawRun, rawStep, hlookup] at hrun
                        | some headType =>
                            cases rest with
                            | nil => simp [rawRun, rawStep, hlookup] at hrun
                            | cons third tail =>
                                cases third with
                                | createDependentSpine arity =>
                                    by_cases harity : arity = headType.piArity
                                    · subst arity
                                      simp [rawRun, rawStep, hlookup, startSpine] at hrun
                                      cases hnext :
                                          startSpine context target frames head headType with
                                      | none =>
                                          have hnext' :
                                              startSpineWith context target frames head []
                                                  headType = none := by
                                            simpa [startSpine] using hnext
                                          rw [hnext'] at hrun
                                          contradiction
                                      | some next =>
                                          have hnext' :
                                              startSpineWith context target frames head []
                                                  headType = some next := by
                                            simpa [startSpine] using hnext
                                          have htailRun :
                                              rawRun goal tail next =
                                                some (.finished term) := by
                                            rw [hnext'] at hrun
                                            simpa using hrun
                                          have hnextBoundary : Boundary next :=
                                            startSpineWith_boundary hnext'
                                          rcases legacyRun_compresses goal hnextBoundary
                                              htailRun with
                                            ⟨atomicTail, hcompressTail⟩
                                          let atomic : AtomicAction := ⟨holeId, head⟩
                                          have hforced :
                                              forcedLegacyActions?
                                                  (.needHole holeId context target frames)
                                                  atomic =
                                                some
                                                  [.selectHole holeId,
                                                    .selectBoundHead head,
                                                    .createDependentSpine
                                                      headType.piArity] := by
                                            simp [forcedLegacyActions?, atomic, hlookup]
                                          have htriple :
                                              rawRun goal
                                                  [.selectHole holeId,
                                                    .selectBoundHead head,
                                                    .createDependentSpine
                                                      headType.piArity]
                                                  (.needHole holeId context target frames) =
                                                some next := by
                                            simpa [rawRun, rawStep, hlookup, startSpine]
                                              using hnext
                                          refine ⟨atomic :: atomicTail, ?_⟩
                                          simp [compressFrom?, atomic, hforced, htriple,
                                            hcompressTail]
                                    · simp [rawRun, rawStep, hlookup, harity] at hrun
                                | selectHole other =>
                                    simp [rawRun, rawStep, hlookup] at hrun
                                | selectBoundHead other =>
                                    simp [rawRun, rawStep, hlookup] at hrun
                                | finish => simp [rawRun, rawStep, hlookup] at hrun
                    | selectHole other => simp [rawRun, rawStep] at hrun
                    | createDependentSpine arity => simp [rawRun, rawStep] at hrun
                    | finish => simp [rawRun, rawStep] at hrun
              · simp [rawRun, rawStep, hselected] at hrun
          | selectBoundHead head => simp [rawRun, rawStep] at hrun
          | createDependentSpine arity => simp [rawRun, rawStep] at hrun
          | finish => simp [rawRun, rawStep] at hrun

/-- Accepted legacy traces translate, and translating back is byte-for-byte exact. -/
theorem legacyAccepted_has_unique_atomic_translation {goal : Expr}
    {legacyTrace : List Action} {term : Nf}
    (hrun : rawRun goal legacyTrace (prepare 0 [] goal []) =
      some (.finished term)) :
    ∃! atomicTrace,
      compressAccepted? goal legacyTrace = some atomicTrace ∧
        expandAccepted? goal atomicTrace = some legacyTrace := by
  rcases legacyRun_compresses goal (prepare_boundary 0 [] goal []) hrun with
    ⟨atomicTrace, hcompress⟩
  refine ⟨atomicTrace, ⟨hcompress, expandAccepted?_compressAccepted hcompress⟩, ?_⟩
  intro other hother
  unfold compressAccepted? at hother
  rw [hcompress] at hother
  exact Option.some.inj hother.1.symm

/-- Raw atomic acceptance, with independent type inference at the terminal state. -/
def AtomicAccepted (goal : Expr) (trace : List AtomicAction) : Prop :=
  ∃ term,
    rawRunAtomic goal trace (prepare 0 [] goal []) = some (.done term) ∧
      inferNf [] term = some goal

/-- Raw four-event acceptance for the sealed Pure checker. -/
def LegacyAccepted (goal : Expr) (trace : List Action) : Prop :=
  ∃ term,
    rawRun goal trace (prepare 0 [] goal []) = some (.finished term) ∧
      inferNf [] term = some goal

/-- Successful direct atomic execution always has a recorded elaboration. -/
theorem exists_elaboration_of_rawRunAtomic (goal : Expr) :
    ∀ {trace : List AtomicAction} {start finalCore : Core},
      rawRunAtomic goal trace start = some finalCore →
      ∃ elaboration,
        elaborateFrom? goal trace start = some elaboration ∧
          elaboration.finalCore = finalCore
  | [], start, finalCore, hrun => by
      simp [rawRunAtomic] at hrun
      subst finalCore
      exact ⟨⟨[], start⟩, rfl, rfl⟩
  | action :: rest, start, finalCore, hrun => by
      simp only [rawRunAtomic, rawRefine?] at hrun
      cases hforced : forcedLegacyActions? start action with
      | none => simp [hforced] at hrun
      | some forced =>
          cases hstep : rawRun goal forced start with
          | none => simp [hforced, hstep] at hrun
          | some next =>
              simp [hforced, hstep] at hrun
              rcases exists_elaboration_of_rawRunAtomic goal hrun with
                ⟨tail, htail, hfinal⟩
              let elaboration : Elaboration :=
                ⟨forced ++ tail.legacyTrace, tail.finalCore⟩
              refine ⟨elaboration, ?_, hfinal⟩
              simp [elaboration, elaborateFrom?, hforced, hstep, htail]

/-- Every accepted atomic trace has one and only one forced legacy expansion. -/
theorem atomicAccepted_has_unique_legacy_translation {goal : Expr}
    {atomicTrace : List AtomicAction}
    (haccepted : AtomicAccepted goal atomicTrace) :
    ∃! legacyTrace, expandAccepted? goal atomicTrace = some legacyTrace := by
  rcases haccepted with ⟨term, hrun, hinfer⟩
  rcases exists_elaboration_of_rawRunAtomic goal hrun with
    ⟨elaboration, helab, hfinal⟩
  have hterminal : coreTerminal goal elaboration.finalCore := by
    rw [hfinal]
    exact hinfer
  let legacyTrace := elaboration.legacyTrace ++ [.finish]
  have hexpand : expandAccepted? goal atomicTrace = some legacyTrace := by
    simp [expandAccepted?, elaborate?, helab, hterminal, legacyTrace]
  refine ⟨legacyTrace, hexpand, ?_⟩
  intro other hother
  rw [hexpand] at hother
  exact Option.some.inj hother.symm

/--
T1 crown: the accepted four-event and atomic trace languages are in bijection;
both directions use the executable translations, and the legacy side remains
checker-accepted after forced effects are reinserted.
-/
theorem acceptedTrace_bijection (goal : Expr) :
    (∀ atomicTrace,
      AtomicAccepted goal atomicTrace →
        ∃! legacyTrace, expandAccepted? goal atomicTrace = some legacyTrace) ∧
    (∀ legacyTrace,
      LegacyAccepted goal legacyTrace →
        ∃! atomicTrace, expandAccepted? goal atomicTrace = some legacyTrace) := by
  constructor
  · intro atomicTrace haccepted
    exact atomicAccepted_has_unique_legacy_translation haccepted
  · intro legacyTrace haccepted
    rcases haccepted with ⟨term, hrun, _hinfer⟩
    rcases legacyAccepted_has_unique_atomic_translation hrun with
      ⟨atomicTrace, ⟨hcompress, hexpand⟩, hunique⟩
    refine ⟨atomicTrace, hexpand, ?_⟩
    intro other hother
    exact hunique other ⟨compressAccepted?_expandAccepted hother, hother⟩

/-- The two positive v1 traces compress to the intended atomic choices. -/
example :
    compressAccepted? PureRefinement.identityGoal PureRefinement.identityTrace =
      some [⟨0, 0⟩] := by
  decide

def dependentAtomicTrace : List AtomicAction := [⟨0, 0⟩, ⟨0, 1⟩]

example :
    expandAccepted? PureRefinement.identityGoal [⟨0, 0⟩] =
      some PureRefinement.identityTrace := by
  decide

#print axioms rawRefine_successor_deterministic
#print axioms pureAtomicRoot_legalActions_nodup
#print axioms rawRefine_eq_checkerSpine
#print axioms coreTerminal_holes_empty
#print axioms expandAccepted?_legacy_accepts
#print axioms compressAccepted?_expandAccepted
#print axioms expandAccepted?_compressAccepted
#print axioms legacyAccepted_has_unique_atomic_translation
#print axioms acceptedTrace_bijection

end Mettapedia.GSLT.LanguageDef.PureAtomicRefinement
