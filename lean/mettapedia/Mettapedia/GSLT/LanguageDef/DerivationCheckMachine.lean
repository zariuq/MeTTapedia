import Mettapedia.GSLT.Core.GSLT

/-!
# A streaming machine for checked derivation DAGs

This module defines the semantic machine that sits between a derivation format
such as TSTP and low-level targets such as StructuredC.  Formula and rule
semantics are parameters: the fixed machine owns chronological identities,
parent lookup, root relevance, deletion, termination, and explicit faults,
while a supplied calculus owns the local inference decision.

Relevance is checked in the same forward pass as inference.  Every non-root
node names one later child on a path toward the root and carries its remaining
distance.  Processing that child validates and discharges the promise.  Thus
an untrusted compiler cannot hide a disconnected component merely by placing
it in a topologically ordered stream.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationCheckMachine

open Mettapedia.GSLT

variable {Formula Rule Evidence Provenance Obligation ServiceState : Type}

abbrev NodeId := Nat

/-- A compact witness that this node lies on a path to the selected root. -/
structure RelevanceWitness where
  distance : Nat
  towardRoot : Option NodeId
deriving DecidableEq, Repr

/-- One live, already checked derivation occurrence.  `linked` records that
the promised child has actually consumed this occurrence as a parent. -/
structure Node (Formula : Type) where
  id : NodeId
  formula : Formula
  relevance : RelevanceWitness
  linked : Bool := false
deriving DecidableEq, Repr

/-- The tiny proof-DAG instruction language.  It contains no calculus opcode:
`infer` selects a rule supplied by the surrounding calculus instance. -/
inductive Instruction
    (Formula Rule Evidence Provenance Obligation : Type) where
  | input (id : NodeId) (formula : Formula) (provenance : Provenance)
      (relevance : RelevanceWitness)
  | infer (id : NodeId) (rule : Rule) (parents : List NodeId)
      (evidence : Evidence) (conclusion : Formula)
      (relevance : RelevanceWitness)
  | drop (id : NodeId)
  | root (id : NodeId) (obligation : Obligation)
  | finish
deriving DecidableEq, Repr

/-- The three semantic decisions specialized from the input problem and the
supplied calculus.  Production lowering specializes these functions; the
machine does not require a generic rule interpreter at runtime. -/
structure Services
    (Formula Rule Evidence Provenance Obligation ServiceState : Type) where
  initial : ServiceState
  input : ServiceState → Provenance → Formula → Option ServiceState
  infer : ServiceState → Rule → List Formula → Evidence → Formula →
    Option ServiceState
  root : ServiceState → Formula → Obligation → Bool

variable {services :
  Services Formula Rule Evidence Provenance Obligation ServiceState}

/-- Every malformed stream or negative semantic decision is explicit. -/
inductive Fault where
  | badNodeId (expected actual : NodeId)
  | malformedRelevance (id : NodeId)
  | inputRejected (id : NodeId)
  | duplicateParent (child parent : NodeId)
  | missingParent (child parent : NodeId)
  | badRelevanceEdge (child parent : NodeId)
  | ruleRejected (id : NodeId)
  | dropRejected (id : NodeId)
  | duplicateRoot
  | missingRootNode (id : NodeId)
  | rootRejected (id : NodeId)
  | irrelevantNode (id : NodeId)
  | malformedRecord
  | missingRoot
  | missingFinish
  | trailingAfterFinish
deriving DecidableEq, Repr

structure RootClaim (Formula Obligation : Type) where
  id : NodeId
  formula : Formula
  obligation : Obligation
deriving DecidableEq, Repr

inductive Outcome (Formula Obligation : Type) where
  | verified (root : RootClaim Formula Obligation)
  | fault (failure : Fault)
deriving DecidableEq, Repr

structure State
    (Formula Rule Evidence Provenance Obligation ServiceState : Type) where
  instructions : List
    (Instruction Formula Rule Evidence Provenance Obligation)
  nodes : List (Node Formula)
  nextId : NodeId
  root? : Option (RootClaim Formula Obligation)
  serviceState : ServiceState
deriving DecidableEq, Repr

inductive Config
    (Formula Rule Evidence Provenance Obligation ServiceState : Type) where
  | running (state :
      State Formula Rule Evidence Provenance Obligation ServiceState)
  | halted (outcome : Outcome Formula Obligation)
deriving DecidableEq, Repr

def initial
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (instructions : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    Config Formula Rule Evidence Provenance Obligation ServiceState :=
  .running {
    instructions := instructions
    nodes := []
    nextId := 0
    root? := none
    serviceState := services.initial
  }

/-- The local shape of a relevance witness.  A non-root witness must point
strictly forward and carry a positive distance; only a root candidate may
have no successor, in which case its distance is zero. -/
def RelevanceWitness.wellFormedFor
    (id : NodeId) (witness : RelevanceWitness) : Bool :=
  match witness.towardRoot with
  | none => witness.distance == 0
  | some child => decide (0 < witness.distance ∧ id < child)

def lookupNode? (id : NodeId) : List (Node Formula) → Option (Node Formula)
  | [] => none
  | node :: nodes =>
      if node.id = id then some node else lookupNode? id nodes

/-- Resolve one parent and, when this child is the promised successor, check
and discharge the parent's relevance edge. -/
def useParent? (child : NodeId) (childDistance : Nat) (parent : NodeId) :
    List (Node Formula) → Option (Formula × List (Node Formula))
  | [] => none
  | node :: nodes =>
      if node.id = parent then
        match node.relevance.towardRoot with
        | some promised =>
            if promised = child then
              if node.relevance.distance = childDistance + 1 then
                some (node.formula, { node with linked := true } :: nodes)
              else
                none
            else
              some (node.formula, node :: nodes)
        | none => some (node.formula, node :: nodes)
      else do
        let (formula, nextNodes) <-
          useParent? child childDistance parent nodes
        some (formula, node :: nextNodes)

/-- Parent order and multiplicity are preserved.  Repeating a parent means
that the calculus service receives the same checked formula occurrence at
each listed position; relevance is an occurrence property and is therefore
discharged idempotently. -/
def resolveParentsFrom?
    (child : NodeId) (childDistance : Nat) :
    List NodeId → List (Node Formula) →
      Except Fault (List Formula × List (Node Formula))
  | [], nodes => .ok ([], nodes)
  | parent :: parents, nodes =>
      match useParent? child childDistance parent nodes with
      | none =>
          match lookupNode? parent nodes with
          | none => .error (.missingParent child parent)
          | some _ => .error (.badRelevanceEdge child parent)
      | some (formula, nextNodes) =>
          match resolveParentsFrom? child childDistance parents nextNodes with
          | .error failure => .error failure
          | .ok (formulas, finalNodes) =>
              .ok (formula :: formulas, finalNodes)

def resolveParents?
    (child : NodeId) (childDistance : Nat)
    (parents : List NodeId) (nodes : List (Node Formula)) :
    Except Fault (List Formula × List (Node Formula)) :=
  resolveParentsFrom? child childDistance parents nodes

/-- A live occurrence may be discarded only after its promised relevance
edge has been witnessed.  The root is therefore not droppable. -/
def dropNode? (id : NodeId) :
    List (Node Formula) → Option (List (Node Formula))
  | [] => none
  | node :: nodes =>
      if node.id = id then
        if node.linked then some nodes else none
      else
        (dropNode? id nodes).map fun nextNodes => node :: nextNodes

def firstIrrelevant? (root : NodeId) :
    List (Node Formula) → Option NodeId
  | [] => none
  | node :: nodes =>
      if node.id = root then
        if node.relevance.towardRoot.isNone &&
            node.relevance.distance == 0 then
          firstIrrelevant? root nodes
        else
          some node.id
      else if node.linked then
        firstIrrelevant? root nodes
      else
        some node.id

def haltFault
    (failure : Fault) :
    Config Formula Rule Evidence Provenance Obligation ServiceState :=
  .halted (.fault failure)

/-- Execute one already decoded instruction.  `hasTrailing` is the only fact
about the remaining stream that the instruction needs: it is consulted solely
by `finish`.  Keeping this core independent of the instruction carrier lets a
list program and a compact word stream share one operational authority. -/
def advance
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (hasTrailing : Bool)
    (instruction : Instruction Formula Rule Evidence Provenance Obligation)
    (state : State Formula Rule Evidence Provenance Obligation ServiceState) :
    Config Formula Rule Evidence Provenance Obligation ServiceState :=
          match instruction with
          | .input id formula provenance relevance =>
              if id != state.nextId then
                haltFault (.badNodeId state.nextId id)
              else if !relevance.wellFormedFor id then
                haltFault (.malformedRelevance id)
              else
                match services.input state.serviceState provenance formula with
                | some nextServiceState =>
                    .running {
                      state with
                      instructions := []
                      nodes := { id, formula, relevance } :: state.nodes
                      nextId := state.nextId + 1
                      serviceState := nextServiceState
                    }
                | none => haltFault (.inputRejected id)
          | .infer id rule parents evidence conclusion relevance =>
              if id != state.nextId then
                haltFault (.badNodeId state.nextId id)
              else if !relevance.wellFormedFor id then
                haltFault (.malformedRelevance id)
              else
                match resolveParents? id relevance.distance parents state.nodes with
                | .error failure => haltFault failure
                | .ok (parentFormulas, nextNodes) =>
                    match services.infer state.serviceState rule parentFormulas
                        evidence conclusion with
                    | some nextServiceState =>
                        .running {
                          state with
                          instructions := []
                          nodes :=
                            { id, formula := conclusion, relevance } :: nextNodes
                          nextId := state.nextId + 1
                          serviceState := nextServiceState
                        }
                    | none => haltFault (.ruleRejected id)
          | .drop id =>
              match dropNode? id state.nodes with
              | none => haltFault (.dropRejected id)
              | some nextNodes =>
                  .running {
                    state with
                    instructions := []
                    nodes := nextNodes
                  }
          | .root id obligation =>
              match state.root? with
              | some _ => haltFault .duplicateRoot
              | none =>
                  match lookupNode? id state.nodes with
                  | none => haltFault (.missingRootNode id)
                  | some node =>
                      if node.relevance.towardRoot.isSome ||
                          node.relevance.distance != 0 then
                        haltFault (.malformedRelevance id)
                      else
                        .running {
                          state with
                          instructions := []
                          root? := some {
                            id := id
                            formula := node.formula
                            obligation := obligation
                          }
                        }
          | .finish =>
              if hasTrailing then
                haltFault .trailingAfterFinish
              else
                match state.root? with
                | none => haltFault .missingRoot
                | some root =>
                    match firstIrrelevant? root.id state.nodes with
                    | some id => haltFault (.irrelevantNode id)
                    | none =>
                        if services.root state.serviceState root.formula
                            root.obligation then
                          .halted (.verified root)
                        else
                          haltFault (.rootRejected root.id)

@[simp] theorem advance_set_instructions
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (hasTrailing : Bool)
    (instruction : Instruction Formula Rule Evidence Provenance Obligation)
    (state : State Formula Rule Evidence Provenance Obligation ServiceState)
    (instructions : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    advance services hasTrailing instruction
        { state with instructions := instructions } =
      advance services hasTrailing instruction state := by
  cases instruction <;> simp [advance]

def replaceInstructions
    (instructions : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    Config Formula Rule Evidence Provenance Obligation ServiceState →
      Config Formula Rule Evidence Provenance Obligation ServiceState
  | .running state => .running { state with instructions := instructions }
  | .halted outcome => .halted outcome

/-- One deterministic list-program transition. -/
def step?
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState) :
    Config Formula Rule Evidence Provenance Obligation ServiceState →
      Option (Config Formula Rule Evidence Provenance Obligation ServiceState)
  | .halted _ => none
  | .running state =>
      match state.instructions with
      | [] => some (haltFault .missingFinish)
      | instruction :: rest =>
          some (replaceInstructions rest
            (advance services (!rest.isEmpty) instruction state))

/-- Bounded execution.  Every running transition consumes one instruction or
halts, so `instructions.length + 1` is a complete bound. -/
def runFuel
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState) :
    Nat → Config Formula Rule Evidence Provenance Obligation ServiceState →
      Config Formula Rule Evidence Provenance Obligation ServiceState
  | 0, config => config
  | fuel + 1, config =>
      match step? services config with
      | none => config
      | some next => runFuel services fuel next

def execute
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (instructions : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    Config Formula Rule Evidence Provenance Obligation ServiceState :=
  runFuel services (instructions.length + 1) (initial services instructions)

/-- The semantic derivation-check machine is itself a genuine GSLT. -/
def gslt
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState) : GSLT where
  Term := Config Formula Rule Evidence Provenance Obligation ServiceState
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => step? services source = some target
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-! ## Semantic soundness interface -/

/-- Logical obligations for one specialized service catalog.  The persistent
state supports incremental freshness, assumption, and status checks without a
second derivation pass.  These theorems are the compile-time contract that
turns an accepted stream into an objective of the supplied calculus/problem. -/
structure SoundServices
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState) where
  Valid : Formula → Prop
  Objective : Obligation → Prop
  StateValid : ServiceState → Prop
  initial_sound : StateValid services.initial
  input_sound : ∀ state provenance formula nextState,
    services.input state provenance formula = some nextState →
      StateValid state → Valid formula ∧ StateValid nextState
  infer_sound : ∀ state rule parents evidence conclusion nextState,
    services.infer state rule parents evidence conclusion = some nextState →
      StateValid state →
      (∀ formula ∈ parents, Valid formula) →
      Valid conclusion ∧ StateValid nextState
  root_sound : ∀ state formula obligation,
    services.root state formula obligation = true →
      StateValid state → Valid formula → Objective obligation

def NodesValid (sound : SoundServices services)
    (nodes : List (Node Formula)) : Prop :=
  ∀ node ∈ nodes, sound.Valid node.formula

def RootValid (sound : SoundServices services) :
    Option (RootClaim Formula Obligation) → Prop
  | none => True
  | some root => sound.Valid root.formula

def ConfigValid (sound : SoundServices services) :
    Config Formula Rule Evidence Provenance Obligation ServiceState → Prop
  | .running state =>
      NodesValid sound state.nodes ∧ RootValid sound state.root? ∧
        sound.StateValid state.serviceState
  | .halted (.fault _) => True
  | .halted (.verified root) => sound.Objective root.obligation

theorem useParent?_preserves_valid
    (sound : SoundServices services)
    {nodes nextNodes : List (Node Formula)}
    {child childDistance parent : Nat} {formula : Formula}
    (valid : NodesValid sound nodes)
    (result : useParent? child childDistance parent nodes =
      some (formula, nextNodes)) :
    sound.Valid formula ∧ NodesValid sound nextNodes := by
  induction nodes generalizing formula nextNodes with
  | nil => simp [useParent?] at result
  | cons head tail induction =>
      by_cases same : head.id = parent
      · cases successor : head.relevance.towardRoot with
        | none =>
            have pairEqual :
                (head.formula, head :: tail) = (formula, nextNodes) := by
              apply Option.some.inj
              simpa [useParent?, same, successor] using result
            cases pairEqual
            constructor
            · exact valid head (by simp)
            · exact valid
        | some promised =>
            by_cases selected : promised = child
            · by_cases distance :
                head.relevance.distance = childDistance + 1
              · have pairEqual :
                    (head.formula,
                      { head with linked := true } :: tail) =
                      (formula, nextNodes) := by
                  apply Option.some.inj
                  simpa [useParent?, same, successor, selected, distance]
                    using result
                cases pairEqual
                constructor
                · exact valid head (by simp)
                · intro node membership
                  rcases List.mem_cons.mp membership with rfl | membership
                  · exact valid head (by simp)
                  · exact valid node (by simp [membership])
              · simp [useParent?, same, successor, selected, distance] at result
            · have pairEqual :
                  (head.formula, head :: tail) = (formula, nextNodes) := by
                apply Option.some.inj
                simpa [useParent?, same, successor, selected] using result
              cases pairEqual
              constructor
              · exact valid head (by simp)
              · exact valid
      · cases recursive : useParent? child childDistance parent tail with
        | none => simp [useParent?, same, recursive] at result
        | some pair =>
            rcases pair with ⟨recursiveFormula, recursiveNodes⟩
            have pairEqual :
                (recursiveFormula, head :: recursiveNodes) =
                  (formula, nextNodes) := by
              apply Option.some.inj
              simpa [useParent?, same, recursive] using result
            cases pairEqual
            have tailValid : NodesValid sound tail := by
              intro node membership
              exact valid node (by simp [membership])
            obtain ⟨formulaValid, recursiveValid⟩ :=
              induction tailValid recursive
            constructor
            · exact formulaValid
            · intro candidate membership
              rcases List.mem_cons.mp membership with sameCandidate | membership
              · subst candidate
                exact valid _ (by simp)
              · exact recursiveValid candidate membership

theorem resolveParentsFrom?_preserves_valid
    (sound : SoundServices services)
    {parents : List NodeId} {nodes nextNodes : List (Node Formula)}
    {child childDistance : Nat} {formulas : List Formula}
    (valid : NodesValid sound nodes)
    (result : resolveParentsFrom? child childDistance parents nodes =
      .ok (formulas, nextNodes)) :
    (∀ formula ∈ formulas, sound.Valid formula) ∧
      NodesValid sound nextNodes := by
  induction parents generalizing nodes formulas nextNodes with
  | nil =>
      have equal := result
      simp only [resolveParentsFrom?] at equal
      have pairEqual : ([], nodes) = (formulas, nextNodes) := by
        exact Except.ok.inj equal
      cases pairEqual
      exact ⟨by simp, valid⟩
  | cons parent parents induction =>
      cases used : useParent? child childDistance parent nodes with
      | none =>
          cases found : lookupNode? parent nodes <;>
            simp [resolveParentsFrom?, used, found] at result
      | some pair =>
          rcases pair with ⟨formula, usedNodes⟩
          cases recursive : resolveParentsFrom? child childDistance parents
              usedNodes with
          | error failure =>
              simp [resolveParentsFrom?, used, recursive] at result
          | ok pair =>
              rcases pair with ⟨recursiveFormulas, finalNodes⟩
              have pairEqual :
                  (formula :: recursiveFormulas, finalNodes) =
                    (formulas, nextNodes) := by
                have equal := result
                simp [resolveParentsFrom?, used, recursive] at equal
                exact Prod.ext equal.1 equal.2
              cases pairEqual
              obtain ⟨formulaValid, usedValid⟩ :=
                useParent?_preserves_valid sound valid used
              obtain ⟨recursiveValid, finalValid⟩ :=
                induction usedValid recursive
              constructor
              · intro candidate membership
                rcases List.mem_cons.mp membership with rfl | membership
                · exact formulaValid
                · exact recursiveValid candidate membership
              · exact finalValid

theorem resolveParents?_preserves_valid
    (sound : SoundServices services)
    {parents : List NodeId} {nodes nextNodes : List (Node Formula)}
    {child childDistance : Nat} {formulas : List Formula}
    (valid : NodesValid sound nodes)
    (result : resolveParents? child childDistance parents nodes =
      .ok (formulas, nextNodes)) :
    (∀ formula ∈ formulas, sound.Valid formula) ∧
      NodesValid sound nextNodes :=
  resolveParentsFrom?_preserves_valid sound valid result

theorem dropNode?_preserves_valid
    (sound : SoundServices services)
    {nodes nextNodes : List (Node Formula)} {id : NodeId}
    (valid : NodesValid sound nodes)
    (result : dropNode? id nodes = some nextNodes) :
    NodesValid sound nextNodes := by
  induction nodes generalizing nextNodes with
  | nil => simp [dropNode?] at result
  | cons head tail induction =>
      by_cases same : head.id = id
      · by_cases linked : head.linked
        · simp [dropNode?, same, linked] at result
          subst nextNodes
          intro node membership
          exact valid node (by simp [membership])
        · simp [dropNode?, same, linked] at result
      · cases recursive : dropNode? id tail with
        | none => simp [dropNode?, same, recursive] at result
        | some finalTail =>
            have listEqual : head :: finalTail = nextNodes := by
              apply Option.some.inj
              simpa [dropNode?, same, recursive] using result
            subst nextNodes
            intro node membership
            rcases List.mem_cons.mp membership with rfl | membership
            · exact valid _ (by simp)
            · exact induction
                (by
                  intro candidate member
                  exact valid candidate (by simp [member]))
                recursive node membership

theorem lookupNode?_valid
    (sound : SoundServices services)
    {nodes : List (Node Formula)} {id : NodeId} {node : Node Formula}
    (valid : NodesValid sound nodes)
    (found : lookupNode? id nodes = some node) :
    sound.Valid node.formula := by
  induction nodes with
  | nil => simp [lookupNode?] at found
  | cons head tail induction =>
      by_cases same : head.id = id
      · have equal : head = node := by
          apply Option.some.inj
          simpa [lookupNode?, same] using found
        subst node
        exact valid head (by simp)
      · apply induction
        · intro candidate membership
          exact valid candidate (by simp [membership])
        · simpa [lookupNode?, same] using found

theorem step?_preserves_valid
    (sound : SoundServices services)
    {source target :
      Config Formula Rule Evidence Provenance Obligation ServiceState}
    (valid : ConfigValid sound source)
    (transition : step? services source = some target) :
    ConfigValid sound target := by
  cases source with
  | halted outcome => simp [step?] at transition
  | running state =>
      rcases state with ⟨instructions, nodes, nextId, root?, serviceState⟩
      change NodesValid sound nodes ∧ RootValid sound root? ∧
        sound.StateValid serviceState at valid
      rcases valid with ⟨nodesValid, rootValid, serviceValid⟩
      cases instructions with
      | nil =>
          simp [step?] at transition
          subst target
          trivial
      | cons instruction rest =>
          cases instruction with
          | input id formula provenance relevance =>
              by_cases badId : id ≠ nextId
              · simp [step?, replaceInstructions, advance, badId] at transition
                subst target
                trivial
              · by_cases badRelevance :
                    relevance.wellFormedFor id = false
                · simp [step?, replaceInstructions, advance, badId,
                    badRelevance] at transition
                  subst target
                  trivial
                · have relevanceOk : relevance.wellFormedFor id = true := by
                    cases equation : relevance.wellFormedFor id <;> simp_all
                  cases accepted :
                      services.input serviceState provenance formula with
                  | none =>
                      simp [step?, replaceInstructions, advance, badId,
                        relevanceOk, accepted] at transition
                      subst target
                      trivial
                  | some nextServiceState =>
                      simp [step?, replaceInstructions, advance, badId,
                        relevanceOk, accepted] at transition
                      subst target
                      obtain ⟨formulaValid, nextServiceValid⟩ :=
                        sound.input_sound serviceState provenance formula
                          nextServiceState accepted serviceValid
                      exact ⟨
                        (by
                          intro node membership
                          rcases List.mem_cons.mp membership with rfl | membership
                          · exact formulaValid
                          · exact nodesValid node membership),
                        rootValid, nextServiceValid⟩
          | infer id rule parents evidence conclusion relevance =>
              by_cases badId : id ≠ nextId
              · simp [step?, replaceInstructions, advance, badId] at transition
                subst target
                trivial
              · by_cases badRelevance :
                    relevance.wellFormedFor id = false
                · simp [step?, replaceInstructions, advance, badId,
                    badRelevance] at transition
                  subst target
                  trivial
                · have relevanceOk : relevance.wellFormedFor id = true := by
                    cases equation : relevance.wellFormedFor id <;> simp_all
                  cases resolved :
                      resolveParents? id relevance.distance parents nodes with
                  | error failure =>
                      simp [step?, replaceInstructions, advance, badId,
                        relevanceOk, resolved] at transition
                      subst target
                      trivial
                  | ok pair =>
                      rcases pair with ⟨parentFormulas, nextNodes⟩
                      cases accepted : services.infer serviceState rule
                          parentFormulas evidence conclusion with
                      | none =>
                          simp [step?, replaceInstructions, advance, badId,
                            relevanceOk, resolved, accepted]
                            at transition
                          subst target
                          trivial
                      | some nextServiceState =>
                          simp [step?, replaceInstructions, advance, badId,
                            relevanceOk, resolved, accepted]
                            at transition
                          subst target
                          obtain ⟨parentValid, nextValid⟩ :=
                            resolveParents?_preserves_valid sound nodesValid resolved
                          obtain ⟨conclusionValid, nextServiceValid⟩ :=
                            sound.infer_sound serviceState rule parentFormulas
                              evidence conclusion nextServiceState accepted
                              serviceValid parentValid
                          exact ⟨
                            (by
                              intro node membership
                              rcases List.mem_cons.mp membership with
                                rfl | membership
                              · exact conclusionValid
                              · exact nextValid node membership),
                            rootValid, nextServiceValid⟩
          | drop id =>
              cases dropped : dropNode? id nodes with
              | none =>
                  simp [step?, replaceInstructions, advance, dropped]
                    at transition
                  subst target
                  trivial
              | some nextNodes =>
                  simp [step?, replaceInstructions, advance, dropped]
                    at transition
                  subst target
                  exact ⟨dropNode?_preserves_valid sound nodesValid dropped,
                    rootValid, serviceValid⟩
          | root id obligation =>
              cases root? with
              | some root =>
                  simp [step?, replaceInstructions, advance] at transition
                  subst target
                  trivial
              | none =>
                  cases found : lookupNode? id nodes with
                  | none =>
                      simp [step?, replaceInstructions, advance, found]
                        at transition
                      subst target
                      trivial
                  | some node =>
                      by_cases malformed :
                          (node.relevance.towardRoot.isSome ||
                            node.relevance.distance != 0) = true
                      · simp [step?, replaceInstructions, advance, found,
                          malformed] at transition
                        subst target
                        trivial
                      · have shapeOk :
                            (node.relevance.towardRoot.isSome ||
                              node.relevance.distance != 0) = false := by
                          cases equation :
                            (node.relevance.towardRoot.isSome ||
                              node.relevance.distance != 0) <;> simp_all
                        simp [step?, replaceInstructions, advance, found,
                          shapeOk] at transition
                        subst target
                        exact ⟨nodesValid,
                          lookupNode?_valid sound nodesValid found,
                          serviceValid⟩
          | finish =>
              by_cases trailing : rest.isEmpty = false
              · simp [step?, replaceInstructions, advance, trailing]
                  at transition
                subst target
                trivial
              · have noTrailing : rest.isEmpty = true := by
                    cases equation : rest.isEmpty <;> simp_all
                cases root? with
                | none =>
                    simp [step?, replaceInstructions, advance, noTrailing]
                      at transition
                    subst target
                    trivial
                | some root =>
                    cases irrelevant : firstIrrelevant? root.id nodes with
                    | some id =>
                        simp [step?, replaceInstructions, advance, noTrailing,
                          irrelevant] at transition
                        subst target
                        trivial
                    | none =>
                        by_cases accepted : services.root serviceState
                            root.formula root.obligation = true
                        · simp [step?, replaceInstructions, advance,
                            noTrailing, irrelevant, accepted]
                            at transition
                          subst target
                          exact sound.root_sound serviceState root.formula
                            root.obligation accepted serviceValid rootValid
                        · have rejected : services.root serviceState root.formula
                              root.obligation = false := by
                            cases equation : services.root serviceState root.formula
                              root.obligation <;> simp_all
                          simp [step?, replaceInstructions, advance,
                            noTrailing, irrelevant, rejected]
                            at transition
                          subst target
                          trivial

theorem runFuel_preserves_valid
    (sound : SoundServices services)
    (fuel : Nat)
    (config : Config Formula Rule Evidence Provenance Obligation ServiceState)
    (valid : ConfigValid sound config) :
    ConfigValid sound (runFuel services fuel config) := by
  induction fuel generalizing config with
  | zero => exact valid
  | succ fuel induction =>
      cases transition : step? services config with
      | none => simpa [runFuel, transition] using valid
      | some next =>
          simp only [runFuel, transition]
          exact induction next
            (step?_preserves_valid sound valid transition)

theorem execute_preserves_valid
    (sound : SoundServices services)
    (instructions : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    ConfigValid sound (execute services instructions) := by
  apply runFuel_preserves_valid sound
  exact ⟨by simp [NodesValid], by simp [RootValid], sound.initial_sound⟩

/-- Acceptance of a specialized instruction stream establishes the objective
of the supplied calculus/problem services.  The proof is independent of the
particular formula representation, calculus, and emitted backend. -/
theorem execute_verified_sound
    (sound : SoundServices services)
    (instructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (root : RootClaim Formula Obligation)
    (accepted : execute services instructions = .halted (.verified root)) :
    sound.Objective root.obligation := by
  have valid := execute_preserves_valid sound instructions
  rw [accepted] at valid
  exact valid

/-! ## Positive and negative executable witnesses -/

private def canaryServices :
    Services String String Unit String String Nat where
  initial := 0
  input := fun state provenance formula =>
    if provenance == "problem" && formula == "p" then some (state + 1)
    else none
  infer := fun state rule parents _ conclusion =>
    if rule == "copy" && parents == [conclusion] then some (state + 1)
    else none
  root := fun state formula obligation =>
    state == 2 && formula == "p" && obligation == "goal"

private def linkedTo (distance child : Nat) : RelevanceWitness :=
  ⟨distance, some child⟩

private def rootWitness : RelevanceWitness := ⟨0, none⟩

def canaryProgram : List (Instruction String String Unit String String) := [
  .input 0 "p" "problem" (linkedTo 1 1),
  .infer 1 "copy" [0] () "p" rootWitness,
  .root 1 "goal",
  .finish
]

theorem canaryProgram_verified :
    execute canaryServices canaryProgram =
      .halted (.verified ⟨1, "p", "goal"⟩) := by
  decide

def repeatedParentServices :
    Services String String Unit String String Nat where
  initial := 0
  input := fun state provenance formula =>
    if provenance == "problem" && formula == "p" then some (state + 1)
    else none
  infer := fun state rule parents _ conclusion =>
    if rule == "contract" && parents == ["p", "p"] && conclusion == "p" then
      some (state + 1)
    else none
  root := fun state formula obligation =>
    state == 2 && formula == "p" && obligation == "goal"

/-- TSTP parent lists are ordered lists, not sets.  A calculus may therefore
consume the same checked parent occurrence at two distinct argument positions. -/
def repeatedParentProgram :
    List (Instruction String String Unit String String) := [
  .input 0 "p" "problem" (linkedTo 1 1),
  .infer 1 "contract" [0, 0] () "p" rootWitness,
  .root 1 "goal",
  .finish
]

theorem repeated_parent_order_and_multiplicity_preserved :
    execute repeatedParentServices repeatedParentProgram =
      .halted (.verified ⟨1, "p", "goal"⟩) := by
  decide

def wrongRuleProgram : List (Instruction String String Unit String String) := [
  .input 0 "p" "problem" (linkedTo 1 1),
  .infer 1 "invent" [0] () "p" rootWitness,
  .root 1 "goal",
  .finish
]

theorem wrongRuleProgram_rejected :
    execute canaryServices wrongRuleProgram =
      .halted (.fault (.ruleRejected 1)) := by
  decide

def disconnectedProgram :
    List (Instruction String String Unit String String) := [
  .input 0 "p" "problem" (linkedTo 1 2),
  .input 1 "p" "problem" rootWitness,
  .root 1 "goal",
  .finish
]

theorem disconnectedProgram_rejected :
    execute canaryServices disconnectedProgram =
      .halted (.fault (.irrelevantNode 0)) := by
  decide

def missingParentProgram :
    List (Instruction String String Unit String String) := [
  .infer 0 "copy" [17] () "p" rootWitness,
  .root 0 "goal",
  .finish
]

theorem missingParentProgram_rejected :
    execute canaryServices missingParentProgram =
      .halted (.fault (.missingParent 0 17)) := by
  decide

#print axioms canaryProgram_verified
#print axioms repeated_parent_order_and_multiplicity_preserved
#print axioms wrongRuleProgram_rejected
#print axioms disconnectedProgram_rejected
#print axioms missingParentProgram_rejected
#print axioms step?_preserves_valid
#print axioms runFuel_preserves_valid
#print axioms execute_verified_sound

end Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
