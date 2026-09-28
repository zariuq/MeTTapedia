import Mettapedia.Machines.TransactionalSearchCode
import Mettapedia.GSLT.LanguageDef.CompiledTwoSidedHeadProgram

/-!
# Joining two-sided compiled heads to transactional search bodies

The head is the existing occurs-checked Martelli--Montanari compiler, including
open query arguments and repeated head variables. The residual body is finite
transactional search code with constructor-shape tests, template-instantiated
writes, ordered alternatives and persistent effects. The same body templates
are instantiated in the actual source and compiled head frames; no assumption
supplies a body-execution equivalence.

`head_body_exact` uses the head compiler's genuine fresh-variable renaming,
proves body evaluation commutes with that renaming, and then uses flat-code
correctness. It preserves ordered open-term answers up to that renaming,
projected head bindings, the final world, and restoration of the compiled frame.
The two activation methods also succeed on exactly the same heads.

Body tests here inspect constructor shape, not arbitrary variable identity.
The result does not yet cover additional body unification, body-recursive calls,
exceptions, scheduler fairness or native C correspondence. Templates are
instantiated at entry to this residual region. Extending the theorem to a
mutable program requires the explicit revision authority of the entry protocol.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TransactionalSearchHead

open TransactionalSearchCode
open Mettapedia.Logic.LP
open Mettapedia.GSLT.LanguageDef.CompiledTwoSidedHeadProgram

/-! ## Parametricity of the concrete transactional interpreter -/

section Mapping
variable {Slot Value Other Test Effect World Observation OtherObservation : Type}
variable [DecidableEq Slot]

/-- Map payload representations while keeping control, tests, effects and
alternative occurrences unchanged. -/
def mapValues (convert : Value → Other) :
    Region Slot Value Test Effect → Region Slot Other Test Effect
  | .fail => .fail
  | .answer => .answer
  | .write slot value body => .write slot (convert value) (mapValues convert body)
  | .guard test body => .guard test (mapValues convert body)
  | .perform effect body => .perform effect (mapValues convert body)
  | .choice left right => .choice (mapValues convert left) (mapValues convert right)

def mapStore (convert : Value → Other) (bindings : Store Slot Value) : Store Slot Other :=
  fun slot => convert (bindings slot)

theorem mapStore_write (convert : Value → Other) (bindings : Store Slot Value)
    (slot : Slot) (value : Value) :
    mapStore convert (Function.update bindings slot value) =
      Function.update (mapStore convert bindings) slot (convert value) := by
  funext other
  by_cases same : other = slot
  · subst other
    simp [mapStore]
  · simp [mapStore, Function.update_of_ne same]

/-- Primitive-level representation laws imply the complete finite region law.
Tests may not inspect information discarded by `convert`; effects are the same
world transitions. This is proved by source syntax, independently of lowering. -/
theorem source_map (before : Semantics Slot Value Test Effect World Observation)
    (after : Semantics Slot Other Test Effect World OtherObservation)
    (convert : Value → Other) (observed : Observation → OtherObservation)
    (tests : ∀ test bindings world, after.test test (mapStore convert bindings) world = before.test test bindings world)
    (effects : ∀ effect world, after.effect effect world = before.effect effect world)
    (observations : ∀ bindings world, after.observe (mapStore convert bindings) world =
      observed (before.observe bindings world))
    (region : Region Slot Value Test Effect) (bindings : Store Slot Value) (world : World) :
    source after (mapValues convert region) (mapStore convert bindings) world =
      ((source before region bindings world).1.map observed,
        (source before region bindings world).2) := by
  induction region generalizing bindings world with
  | fail => rfl
  | answer => simp only [mapValues, source, observations, List.map_cons, List.map_nil]
  | write slot value body ih =>
      simp only [mapValues, source, ← mapStore_write]
      exact ih _ _
  | guard test body ih =>
      simp only [mapValues, source, tests]
      split
      · exact ih _ _
      · rfl
  | perform effect body ih =>
      simp only [mapValues, source, effects]
      exact ih _ _
  | choice left right il ir =>
      simp only [mapValues, source, il, ir, List.map_append]

variable {Third : Type}

omit [DecidableEq Slot] in
theorem mapValues_comp (first : Value → Other) (second : Other → Third)
    (region : Region Slot Value Test Effect) :
    mapValues second (mapValues first region) = mapValues (second ∘ first) region := by
  induction region with
  | fail => rfl
  | answer => rfl
  | write slot value body ih => simp [mapValues, ih]
  | guard test body ih => simp [mapValues, ih]
  | perform effect body ih => simp [mapValues, ih]
  | choice left right il ir => simp [mapValues, il, ir]

end Mapping

/-! ## Body guards inspect constructors, not fresh-variable spelling -/

universe r
variable {σ : LPSignature.{0, 0, r, 0}}

inductive Shape (σ : LPSignature.{0, 0, r, 0}) where
  | variable
  | constant (value : σ.constants)
  | node (function : σ.functionSymbols)

instance [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] : DecidableEq (Shape σ)
  | .variable, .variable => isTrue rfl
  | .constant a, .constant b => decidable_of_iff (a = b) (by simp)
  | .node a, .node b => decidable_of_iff (a = b) (by simp)
  | .variable, .constant _ | .variable, .node _ | .constant _, .variable
  | .node _, .variable | .constant _, .node _ | .node _, .constant _ => isFalse nofun

def shape : Term σ → Shape σ
  | .var _ => .variable
  | .const value => .constant value
  | .app function _ => .node function

theorem shape_rename (rename : σ.vars → σ.vars) (term : Term σ) :
    shape ((renameVars rename).applyTerm term) = shape term := by
  cases term <;> rfl

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
variable {Effect World : Type} {k : Nat}

/-- Observe one result slot; the term may remain open. A test sees whether a
slot holds a variable, a named constant, or a particular constructor. -/
def semantics (perform : Effect → World → World) (result : Fin k) :
    Semantics (Fin k) (Term σ) (Fin k × Shape σ) Effect World (Term σ) where
  test := fun test bindings _ => decide (shape (bindings test.1) = test.2)
  effect := perform
  observe := fun bindings _ => bindings result

def instantiateBody (frame : Fin k → Term σ)
    (body : Region (Fin k) (HeadPattern σ (Fin k)) (Fin k × Shape σ) Effect) :
    Region (Fin k) (Term σ) (Fin k × Shape σ) Effect :=
  mapValues (instantiate frame) body

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- Body templates use the actual head-frame values. Renaming the frame and
then instantiating is the same as renaming the instantiated body. -/
theorem instantiateBody_rename (rename : σ.vars → σ.vars)
    (frame : Fin k → Term σ)
    (body : Region (Fin k) (HeadPattern σ (Fin k)) (Fin k × Shape σ) Effect) :
    instantiateBody (mapStore (renameVars rename).applyTerm frame) body =
      mapValues (renameVars rename).applyTerm (instantiateBody frame body) := by
  unfold instantiateBody
  rw [mapValues_comp]
  have same : instantiate (mapStore (renameVars rename).applyTerm frame) =
      (renameVars rename).applyTerm ∘ instantiate frame := by
    funext template
    exact (applyTerm_instantiate (renameVars rename) frame template).symm
  rw [same]

omit [DecidableEq σ.vars] in
/-- The concrete shape guards and open-term observer discharge the primitive
parametricity obligations. No arbitrary body-equivalence premise is assumed. -/
theorem body_rename (perform : Effect → World → World) (result : Fin k)
    (rename : σ.vars → σ.vars) (frame : Fin k → Term σ)
    (body : Region (Fin k) (HeadPattern σ (Fin k)) (Fin k × Shape σ) Effect)
    (world : World) :
    source (semantics perform result)
        (instantiateBody (mapStore (renameVars rename).applyTerm frame) body)
        (mapStore (renameVars rename).applyTerm frame) world =
      ((source (semantics perform result) (instantiateBody frame body) frame world).1.map
          (renameVars rename).applyTerm,
        (source (semantics perform result) (instantiateBody frame body) frame world).2) := by
  rw [instantiateBody_rename]
  apply source_map (semantics perform result) (semantics perform result)
    (renameVars rename).applyTerm (renameVars rename).applyTerm
  · intro test bindings world
    simp only [semantics, mapStore, shape_rename]
  · intros; rfl
  · intros; rfl

/-! ## Actual compiled-head / flat-body integration -/

variable (name : ℕ → σ.vars)
variable {Op : Type} (prim : Op → List (Term σ) → Subst σ × ℕ → Option (Term σ))
  (test : Op → List (Term σ) → Subst σ × ℕ → Option Bool)

/-- Run a resolved frame in flat transactional code. Answers are exported;
the frame itself is restored when this finite region exhausts. -/
def compiledBody (perform : Effect → World → World) (result : Fin k)
    (body : Region (Fin k) (HeadPattern σ (Fin k)) (Fin k × Shape σ) Effect)
    (frame : Fin k → Term σ) (world : World) : State (Fin k) (Term σ) World (Term σ) :=
  execute (semantics perform result) (lower (instantiateBody frame body))
    ⟨frame, [], world, [], 0⟩

/-- The joined theorem discharges a head/body boundary. Both head mechanisms
accept exactly the same queries. When they accept, their complete projected
head bindings are variants; the actual compiled body produces exactly the
source body's ordered answers under that same renaming, with the same effects
and the compiled frame restored. No closed-query restriction is present. -/
theorem head_body_exact (injective : Function.Injective name)
    (patterns : List (HeadPattern σ (Fin k))) (args : List (Term σ))
    (store : Subst σ) (supply : ℕ) (entry : EntryCondition name store supply args)
    (perform : Effect → World → World) (result : Fin k)
    (body : Region (Fin k) (HeadPattern σ (Fin k)) (Fin k × Shape σ) Effect)
    (world : World) :
    (compiledActivation name patterns args store supply).isSome =
      (sourceActivation name prim test patterns args store supply).isSome ∧
    ∀ compiled interpreted,
      compiledActivation name patterns args store supply = some compiled →
      sourceActivation name prim test patterns args store supply = some interpreted →
      ∃ rename : σ.vars → σ.vars,
        Set.InjOn rename {x |
          (∃ v, ¬ InSupply name supply v ∧ x ∈ (interpreted.2.1 v).freeVars) ∨
          ∃ slot, x ∈ (interpreted.2.1.applyTerm (interpreted.1 slot)).freeVars} ∧
        (∀ v, ¬ InSupply name supply v →
          compiled.2.1 v = (renameVars rename).applyTerm (interpreted.2.1 v)) ∧
        (∀ slot, compiled.2.1.applyTerm (compiled.1 slot) =
          (renameVars rename).applyTerm (interpreted.2.1.applyTerm (interpreted.1 slot))) ∧
        let compiledFrame := (observe compiled.1 compiled.2.1).2
        let sourceFrame := (observe interpreted.1 interpreted.2.1).2
        let target := compiledBody perform result body compiledFrame world
        let reference := source (semantics perform result)
          (instantiateBody sourceFrame body) sourceFrame world
        target.emitted = reference.1.map (renameVars rename).applyTerm ∧
        target.world = reference.2 ∧ target.bindings = compiledFrame ∧ target.trail = [] := by
  refine ⟨(activation_exact name prim test injective patterns args store supply entry).1, ?_⟩
  intro compiled interpreted accepted sourceAccepted
  obtain ⟨rename, oneToOne, outside, slots⟩ :=
    activation_variant name prim test injective patterns args store supply entry accepted sourceAccepted
  refine ⟨rename, oneToOne, outside, slots, ?_⟩
  have frames : (observe compiled.1 compiled.2.1).2 =
      mapStore (renameVars rename).applyTerm (observe interpreted.1 interpreted.2.1).2 := by
    funext slot
    exact slots slot
  dsimp only
  unfold compiledBody
  rw [lower_exact _ _ _ rfl]
  simp only [List.nil_append]
  dsimp only [observe] at frames
  rw [frames, body_rename]
  exact ⟨rfl, rfl, trivial, trivial⟩

/-- Body exhaustion restores the solved head frame, and that restored view
retains the head compiler's most-general solution, not just one successful
closed instance of it. -/
theorem exhausted_body_retains_mgu (injective : Function.Injective name)
    (patterns : List (HeadPattern σ (Fin k))) (args : List (Term σ))
    (store : Subst σ) (supply : ℕ) (entry : EntryCondition name store supply args)
    (perform : Effect → World → World) (result : Fin k)
    (body : Region (Fin k) (HeadPattern σ (Fin k)) (Fin k × Shape σ) Effect)
    (world : World) (compiled : (Fin k → Term σ) × Subst σ × ℕ)
    (accepted : compiledActivation name patterns args store supply = some compiled) :
    let final := compiledBody perform result body (observe compiled.1 compiled.2.1).2 world
    HeadSolution store patterns args compiled.2.1 final.bindings ∧
      ∀ δ frame, HeadSolution store patterns args δ frame →
        InstanceOffSupply name supply (compiled.2.1, final.bindings) (δ, frame) := by
  dsimp only
  unfold compiledBody
  rw [lower_exact _ _ _ rfl]
  exact ⟨compiledActivation_sound name injective patterns args store supply entry accepted,
    fun _ _ solution => compiledActivation_mostGeneral name injective patterns args store supply
      entry accepted solution⟩

namespace Controls

abbrev sig : LPSignature.{0, 0, 0, 0} where
  constants := Nat
  vars := Nat
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Unit
  functionArity _ := 1

def frame : Fin 2 → Term sig := fun i => .var (10 + i.val)

def box (value : Term sig) : Term sig := .app () fun _ => value

def body : Region (Fin 2) (HeadPattern sig (Fin 2)) (Fin 2 × Shape sig) Nat :=
  .choice
    (.guard (1, .variable) (.write 0 (.app () fun _ => .var 1) (.perform 3 .answer)))
    (.perform 5 .answer)

/-- The first branch constructs around an unbound variable. The second sees
its original frame, and both performed effects persist in order. -/
theorem open_body_answers_and_effects :
    (compiledBody Nat.add 0 body frame 0).emitted = [box (.var 11), .var 10] ∧
    (compiledBody Nat.add 0 body frame 0).world = 8 ∧
    (compiledBody Nat.add 0 body frame 0).bindings 0 = .var 10 := by
  simp [compiledBody, lower, instantiateBody, mapValues, execute, TransactionalSearchCode.step,
    semantics, shape, frame, instantiate, undo, body, box]

def openHead : List (HeadPattern sig (Fin 1)) := [.var 0]

def afterOpenHead : Region (Fin 1) (HeadPattern sig (Fin 1)) (Fin 1 × Shape sig) Nat :=
  .choice (.guard (0, .variable)
    (.write 0 (.app () fun _ => .var 0) (.perform 3 .answer))) (.perform 5 .answer)

/-- This control executes the actual compiled unification head and then the
flat transactional body, retaining an open query variable in both answers. -/
theorem compiled_open_head_body :
    (compiledActivation id openHead [.var 3] (Subst.id sig) 10).map
      (fun activated =>
        let ran := compiledBody Nat.add 0 afterOpenHead (observe activated.1 activated.2.1).2 0
        (ran.emitted, ran.world)) = some ([box (.var 3), .var 3], 8) := by
  rfl

def noPrim : Empty → List (Term sig) → Subst sig × Nat → Option (Term sig) :=
  fun instruction => instruction.elim

def noTest : Empty → List (Term sig) → Subst sig × Nat → Option Bool :=
  fun instruction => instruction.elim

/-- The independent source head and snapshot-body interpreter produce the same
open terms and world in the joined positive control. -/
theorem source_open_head_body :
    (sourceActivation id noPrim noTest openHead [.var 3] (Subst.id sig) 10).map
      (fun activated => source (semantics Nat.add 0)
        (instantiateBody (observe activated.1 activated.2.1).2 afterOpenHead)
        (observe activated.1 activated.2.1).2 0) = some ([box (.var 3), .var 3], 8) := by
  have unifies : unifyTotal [(Term.var (σ := sig) 10, .var 3)] =
      some (Subst.id sig ∘ₛ Subst.single 10 (.var 3)) := by
    rw [unifyTotal.eq_def (σ := sig)]
    simp [Subst.applyEqs]
    rw [unifyTotal.eq_def (σ := sig)]
  unfold sourceActivation
  simp [substitutionStore, Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies.unifyAll,
    Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies.instArgs,
    headTemplates, openHead, freshVariables, instantiate, unifies,
    source, semantics, instantiateBody, mapValues, afterOpenHead,
    shape, Subst.single, box]


/-- A deliberately representation-sensitive guard, unlike the shape guard. -/
def spelledTen : Term sig → Bool
  | .var name => name == 10
  | _ => false

/-- A source variable spelling may change under a valid activation renaming.
Inspecting that spelling would invalidate the constructor-shape theorem. -/
theorem spelling_test_is_not_equivariant :
    spelledTen (.var 10) = true ∧
    spelledTen ((renameVars (fun x : Nat => x + 100)).applyTerm (.var 10)) = false := by decide

/-- Renaming a still-open term does not turn it into a constructor or constant. -/
theorem variable_shape_survives :
    shape ((renameVars (fun x : Nat => x + 100)).applyTerm
      (Term.var (σ := sig) 10)) = .variable := rfl

end Controls

end Mettapedia.Machines.TransactionalSearchHead
