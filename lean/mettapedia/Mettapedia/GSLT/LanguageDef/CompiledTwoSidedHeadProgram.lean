import Mettapedia.Logic.LP.UnificationIdempotence
import Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies

/-!
# Compiled two-sided equation heads

An equation head is compiled to straight-line code that unifies it with an open
query: the query's arguments may contain unbound variables, the head's
variables may repeat, and both sides can be bound.  This is the two-sided
counterpart of `CompiledMatchProgram`, which matches a pattern against a closed
subject.

**Machine.**  Registers hold query subterms; slots are the activation's frame
(one per equation variable); the store is an idempotent substitution; fresh
variables come from the supply `name n, name (n + 1), ...`.  Four instructions
(`HeadOp`), each reading its register through the store:

* `bindSlot r x` — first occurrence of slot `x`: the slot takes register `r`;
* `equateSlot r x` — repeated occurrence: the slot's term and register `r` are
  unified by the total Martelli--Montanari unifier `unifyTotal`, occurs check
  included;
* `constant r c` — an unbound query variable is bound to `c`; `c` passes; any
  other term fails;
* `node r f t` — an unbound query variable is bound to `f` over fresh
  variables, which are loaded as the children into registers `t, t + 1, ...`;
  a term with head `f` loads its own children; any other term fails.

`emit` allocates registers in pre-order and decides at compile time whether a
slot occurrence is first (`bindSlot`) or repeated (`equateSlot`).

**Laws.**

* `emit_spec`, `emitHead_spec`: the emitted code solves its patterns exactly,
  up to the values of fresh variables (`Realizes`: every compatible solution
  survives the run, and every solution compatible with the final state was one),
  and preserves the invariant `WellFormed` (idempotent store, nothing held
  outside the store refers to an unallocated fresh variable).
* `compiledActivation_sound`, `_mostGeneral`, `_complete`, `_wellFormed`: the
  compiled activation (arity check, head code, a fresh variable for every slot
  the head leaves unbound) returns a most general solution of the head against
  the arguments, succeeds whenever one exists, and re-establishes the next
  activation's entry condition.
* `activation_exact`: against `DefunctionalizedEquationBodies.activate` over the
  store algebra `substitutionStore` (allocate the frame, then `unifyAll` the
  instantiated head with the arguments by `unifyTotal`), the compiled head
  succeeds iff the source activation does, and on success the two results
  (store, frame read through the store) are instances of each other on every
  variable outside the fresh supply and on every slot.
* `activation_variant`: on success the compiled result is the source result
  with its variables renamed, on every variable outside the fresh supply and on
  every slot (`VariantOffSupply`: the renaming is injective on the variables
  shown there); `variantOffSupply_of_instances` derives this from mutual
  instance.
* `compiledActivate_exact`: for a whole relation, the compiled activation step
  yields the same equations, in authored order, as the source activation step,
  pairwise related as above and sharing each equation's body.

Variables in the fresh supply are compared only through what the store and the
frame show: the two activations allocate different fresh variables, so their
stores may differ there.

**Not covered.**  Costs, deoptimization (the C machine's hand-off to the
general interpreter on resource exhaustion or a foreign variable), undoing
bindings on backtracking, and conformance of the C code: this is a model of the
compiled head, not a verified translation.

**Correspondence with the C open-equation machine.**  `OEM_M_BIND`,
`OEM_M_SAME`, `OEM_M_ATOM`, `OEM_M_EXPR` are `bindSlot`, `equateSlot`,
`constant`, `node`; `regs` are the registers, `locals` the slots, and the cells
created by `oem_new_cell` the fresh supply.  A MeTTa expression of length `n`
is the application of an `n`-ary tuple symbol, so `OEM_M_EXPR`'s length test
is `node`'s head test; the C compiler allocates registers in the same pre-order
(`oem_compile_param`) and classifies first versus repeated occurrences the same
way (`compile->bound`).  Differences:

* the C store is a cell array read by dereferencing the top-level cell chain,
  and a matched expression loads its raw children; the Lean store is an
  idempotent substitution applied to the whole register term, so loaded
  children are fully resolved;
* for a pair of unbound cells the C binds the younger to the older (so the
  binding dies with the younger cell and is not recorded for undo), and it
  unifies (register, slot); `unifyTotal` is given (slot, register) and binds the
  left variable of a variable pair.  Both are most general, which is all the
  theorems use;
* the C occurs-checks exactly the bindings made by unification (`OEM_M_SAME`);
  `OEM_M_ATOM` binds a literal, which has no variables, and `OEM_M_EXPR` a node
  of new cells, without a check, as `constant` and `node` do here;
* the C gives a new cell only to slots left unbound, whereas
  `compiledActivation` advances the supply by the slot count and skips the names
  of bound slots;
* the C identifies a relation by symbol and arity, so its argument count is
  structural; `compiledActivation` checks it;
* the empty expression `()` is an `OEM_M_ATOM` literal in C and a nullary
  `node` here; both accept `()` and bind an unbound query variable to it;
* a head subterm the host classifies as a relational occurrence
  (`oem_head_callable`) is compiled in C as an `OEM_M_BIND` of a temporary
  slot, and the call becomes a body step whose answer unifies with that slot.
  Here a head is data only: the rewrite of such an equation into a data head
  and a leading `letCall` of its body is not covered.  Quoted head patterns are
  rejected by the C compiler and have no counterpart here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CompiledTwoSidedHeadProgram

open Mettapedia.Logic.LP

universe u r

/-! ## Head patterns -/

/-- The symbols of `σ` with an equation's slots as variables. -/
abbrev slotSignature (σ : LPSignature.{u, u, r, u}) (Slot : Type u) :
    LPSignature.{u, u, r, u} :=
  { σ with vars := Slot }

/-- An equation-head pattern: an LP term whose variables are the equation's
slots.  A slot may occur more than once. -/
abbrev HeadPattern (σ : LPSignature.{u, u, r, u}) (Slot : Type u) : Type u :=
  Term (slotSignature σ Slot)

section Patterns

variable {σ : LPSignature.{u, u, r, u}} {Slot : Type u}

/-- Instantiate a head pattern: every slot becomes its frame term. -/
def instantiate (frame : Slot → Term σ) : HeadPattern σ Slot → Term σ
  | .var slot => frame slot
  | .const value => .const value
  | .app function children => .app function fun i => instantiate frame (children i)

theorem applyTerm_instantiate (θ : Subst σ) (frame : Slot → Term σ)
    (pattern : HeadPattern σ Slot) :
    θ.applyTerm (instantiate frame pattern) =
      instantiate (fun slot => θ.applyTerm (frame slot)) pattern := by
  induction pattern with
  | var slot => rfl
  | const value => rfl
  | app function children ih =>
      simp only [instantiate, Subst.applyTerm_app]
      congr 1
      funext i
      exact ih i

theorem instantiate_congr [DecidableEq Slot] {frame frame' : Slot → Term σ}
    {pattern : HeadPattern σ Slot}
    (agree : ∀ slot ∈ pattern.freeVars, frame slot = frame' slot) :
    instantiate frame pattern = instantiate frame' pattern := by
  induction pattern with
  | var slot => exact agree slot (Term.mem_freeVars_var.mpr rfl)
  | const value => rfl
  | app function children ih =>
      simp only [instantiate]
      congr 1
      funext i
      exact ih i fun slot member => agree slot (Term.mem_freeVars_app.mpr ⟨i, member⟩)

end Patterns

/-! ## Compiled heads -/

/-- One instruction of a compiled equation head.  Registers hold query
subterms; slots hold the terms the head's variables stand for. -/
inductive HeadOp (σ : LPSignature.{u, u, r, u}) (Slot : Type u) : Type u where
  /-- First occurrence of a slot: the slot takes the register's term. -/
  | bindSlot (source : ℕ) (slot : Slot)
  /-- Repeated occurrence of a slot: the slot's term and the register's term
  are unified, occurs-checked, by the total Martelli--Montanari unifier. -/
  | equateSlot (source : ℕ) (slot : Slot)
  /-- A constant of the head: an unbound query variable is bound to it, the
  same constant passes, anything else fails. -/
  | constant (source : ℕ) (value : σ.constants)
  /-- A constructor of the head whose children load into the registers from
  `target` on: an unbound query variable is bound to the constructor over
  fresh variables, which become the children (they are fresh, so the binding
  needs no occurs check); the same constructor loads its own children;
  anything else fails. -/
  | node (source : ℕ) (function : σ.functionSymbols) (target : ℕ)

instance {σ : LPSignature.{u, u, r, u}} {Slot : Type u} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq Slot] : DecidableEq (HeadOp σ Slot)
  | .bindSlot s x, .bindSlot s' x' => decidable_of_iff (s = s' ∧ x = x') (by simp)
  | .equateSlot s x, .equateSlot s' x' => decidable_of_iff (s = s' ∧ x = x') (by simp)
  | .constant s c, .constant s' c' => decidable_of_iff (s = s' ∧ c = c') (by simp)
  | .node s f t, .node s' f' t' => decidable_of_iff (s = s' ∧ f = f' ∧ t = t') (by simp)
  | .bindSlot .., .equateSlot .. | .bindSlot .., .constant .. | .bindSlot .., .node ..
  | .equateSlot .., .bindSlot .. | .equateSlot .., .constant .. | .equateSlot .., .node ..
  | .constant .., .bindSlot .. | .constant .., .equateSlot .. | .constant .., .node ..
  | .node .., .bindSlot .. | .node .., .equateSlot .. | .node .., .constant .. => isFalse nofun

/-- The state a compiled head transforms: registers, the frame of slots being
built, the binding store, and the fresh-variable supply. -/
structure HeadState (σ : LPSignature.{u, u, r, u}) (Slot : Type u) : Type u where
  registers : ℕ → Option (Term σ)
  slots : Slot → Option (Term σ)
  store : Subst σ
  supply : ℕ

section Emission

variable {σ : LPSignature.{u, u, r, u}} {Slot : Type u} [DecidableEq Slot]

/-- Emit a sequence of tasks, threading the next free register and the slots
bound so far. -/
def emitSeq {α : Type*}
    (emitOne : α → ℕ → List Slot → List (HeadOp σ Slot) × ℕ × List Slot) :
    List α → ℕ → List Slot → List (HeadOp σ Slot) × ℕ × List Slot
  | [], next, bound => ([], next, bound)
  | task :: rest, next, bound =>
      let first := emitOne task next bound
      let others := emitSeq emitOne rest first.2.1 first.2.2
      (first.1 ++ others.1, others.2.1, others.2.2)

/-- The code for one head pattern read from register `source`, allocating
registers from `next`, when the slots in `bound` are already bound.  Whether a
slot occurrence binds or unifies is decided here, not at run time.  The result
carries the code, the next free register and the slots bound after it. -/
def emit : HeadPattern σ Slot → ℕ → ℕ → List Slot →
    List (HeadOp σ Slot) × ℕ × List Slot
  | .var slot, source, next, bound =>
      if slot ∈ bound then ([.equateSlot source slot], next, bound)
      else ([.bindSlot source slot], next, slot :: bound)
  | .const value, source, next, bound => ([.constant source value], next, bound)
  | .app function children, source, next, bound =>
      let body := emitSeq
        (fun (i : Fin (σ.functionArity function)) => emit (children i) (next + i))
        (List.finRange (σ.functionArity function))
        (next + σ.functionArity function) bound
      (.node source function next :: body.1, body.2.1, body.2.2)

/-- The code for a head whose `j`-th pattern reads register `j`. -/
def emitHead (patterns : List (HeadPattern σ Slot)) : List (HeadOp σ Slot) :=
  (emitSeq (fun (j : Fin patterns.length) => emit (patterns.get j) j)
    (List.finRange patterns.length) patterns.length []).1

omit [DecidableEq Slot] in
theorem le_emitSeq_next {α : Type*}
    (emitOne : α → ℕ → List Slot → List (HeadOp σ Slot) × ℕ × List Slot)
    (grows : ∀ task next bound, next ≤ (emitOne task next bound).2.1) :
    ∀ (tasks : List α) (next : ℕ) (bound : List Slot),
      next ≤ (emitSeq emitOne tasks next bound).2.1
  | [], _, _ => le_rfl
  | task :: rest, next, bound =>
      (grows task next bound).trans (le_emitSeq_next emitOne grows rest _ _)

theorem le_emit_next (pattern : HeadPattern σ Slot) :
    ∀ source next bound, next ≤ (emit pattern source next bound).2.1 := by
  induction pattern with
  | var slot =>
      intro source next bound
      unfold emit
      split <;> exact le_rfl
  | const value => intro source next bound; exact le_rfl
  | app function children ih =>
      intro source next bound
      show next ≤ (emitSeq
        (fun (i : Fin (σ.functionArity function)) => emit (children i) (next + i))
        (List.finRange (σ.functionArity function)) (next + σ.functionArity function) bound).2.1
      exact (Nat.le_add_right next (σ.functionArity function)).trans
        (le_emitSeq_next _ (fun i next' bound' => ih i (next + i) next' bound') _ _ _)

end Emission

section Machine

variable {σ : LPSignature.{u, u, r, u}} {Slot : Type u}
variable [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq Slot]
variable (name : ℕ → σ.vars)

/-- Load `children` into the registers from `target` on. -/
def loadChildren (registers : ℕ → Option (Term σ)) (target : ℕ) {arity : ℕ}
    (children : Fin arity → Term σ) : ℕ → Option (Term σ) := fun index =>
  if inRange : target ≤ index ∧ index < target + arity then
    some (children ⟨index - target, by omega⟩)
  else registers index

/-- The fresh variables `name start, name (start + 1), ...`. -/
def freshVariables (start arity : ℕ) : Fin arity → Term σ :=
  fun i => .var (name (start + i))

/-- The state after binding the query variable `v` to `function` over fresh
variables, whose registers start at `target`. -/
def bindFreshNode (state : HeadState σ Slot) (function : σ.functionSymbols) (target : ℕ)
    (v : σ.vars) : HeadState σ Slot where
  registers := loadChildren state.registers target
    (freshVariables name state.supply (σ.functionArity function))
  slots := state.slots
  store := Subst.single v
      (.app function (freshVariables name state.supply (σ.functionArity function))) ∘ₛ
    state.store
  supply := state.supply + σ.functionArity function

/-- The state after loading a constructor's own children from `target` on. -/
def loadNode (state : HeadState σ Slot) (target : ℕ) {arity : ℕ}
    (children : Fin arity → Term σ) : HeadState σ Slot :=
  { state with registers := loadChildren state.registers target children }

/-- One instruction; `none` is failure. -/
def step : HeadOp σ Slot → HeadState σ Slot → Option (HeadState σ Slot)
  | .bindSlot source slot, state =>
      (state.registers source).map fun term =>
        { state with slots := Function.update state.slots slot (some term) }
  | .equateSlot source slot, state =>
      match state.registers source, state.slots slot with
      | some term, some previous =>
          (unifyTotal [(state.store.applyTerm previous, state.store.applyTerm term)]).map
            fun unifier => { state with store := unifier ∘ₛ state.store }
      | _, _ => none
  | .constant source value, state =>
      match state.registers source with
      | none => none
      | some term =>
          match state.store.applyTerm term with
          | .var v =>
              some { state with store := Subst.single v (.const value) ∘ₛ state.store }
          | .const actual => if value = actual then some state else none
          | .app _ _ => none
  | .node source function target, state =>
      match state.registers source with
      | none => none
      | some term =>
          match state.store.applyTerm term with
          | .var v => some (bindFreshNode name state function target v)
          | .app actual children =>
              if actual = function then some (loadNode state target children) else none
          | .const _ => none

/-- Run instructions in order, stopping at the first failure. -/
def exec : List (HeadOp σ Slot) → HeadState σ Slot → Option (HeadState σ Slot)
  | [], state => some state
  | instruction :: rest, state => (step name instruction state).bind (exec rest)

theorem exec_append (first second : List (HeadOp σ Slot)) (state : HeadState σ Slot) :
    exec name (first ++ second) state =
      (exec name first state).bind (exec name second) := by
  induction first generalizing state with
  | nil => simp [exec]
  | cons instruction rest ih =>
      simp only [List.cons_append, exec]
      cases step name instruction state with
      | none => simp
      | some next => simpa using ih next

theorem exec_singleton (instruction : HeadOp σ Slot) (state : HeadState σ Slot) :
    exec name [instruction] state = step name instruction state := by
  simp [exec]

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Slot] in
theorem loadChildren_below (registers : ℕ → Option (Term σ)) {target : ℕ}
    {arity : ℕ} (children : Fin arity → Term σ) {index : ℕ} (below : index < target) :
    loadChildren registers target children index = registers index := by
  simp only [loadChildren]
  rw [dif_neg (by omega)]

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Slot] in
theorem loadChildren_at (registers : ℕ → Option (Term σ)) (target : ℕ)
    {arity : ℕ} (children : Fin arity → Term σ) (i : Fin arity) :
    loadChildren registers target children (target + i) = some (children i) := by
  simp only [loadChildren]
  rw [dif_pos (by omega)]
  congr 2
  ext
  simp

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Slot] in
theorem loadChildren_cases (registers : ℕ → Option (Term σ)) (target : ℕ)
    {arity : ℕ} (children : Fin arity → Term σ) (index : ℕ) (term : Term σ)
    (loaded : loadChildren registers target children index = some term) :
    (∃ i, children i = term) ∨ registers index = some term := by
  simp only [loadChildren] at loaded
  split at loaded
  · exact .inl ⟨_, Option.some.inj loaded⟩
  · exact .inr loaded

/-! ## The fresh supply -/

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Slot] in
/-- `v` is still held by the fresh supply at `n`. -/
def InSupply (n : ℕ) (v : σ.vars) : Prop :=
  ∃ m, n ≤ m ∧ name m = v

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq Slot] in
/-- No variable of `t` is still held by the supply at `n`. -/
def AvoidsSupply (n : ℕ) (t : Term σ) : Prop :=
  ∀ v ∈ t.freeVars, ¬ InSupply name n v

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq Slot] in
/-- A store fixes the supply's variables and maps every other variable to a
term avoiding the supply. -/
def StoreAvoidsSupply (n : ℕ) (θ : Subst σ) : Prop :=
  ∀ v, (InSupply name n v → θ v = .var v) ∧
    (¬ InSupply name n v → AvoidsSupply name n (θ v))

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Slot] in
/-- Two substitutions agree on every variable outside the supply at `n`. -/
def AgreeOffSupply (n : ℕ) (δ δ' : Subst σ) : Prop :=
  ∀ v, ¬ InSupply name n v → δ v = δ' v

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Slot] in
theorem InSupply.mono {n n' : ℕ} (le : n ≤ n') {v : σ.vars}
    (member : InSupply name n' v) : InSupply name n v := by
  obtain ⟨m, bound, rfl⟩ := member
  exact ⟨m, le.trans bound, rfl⟩

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Slot] in
theorem name_inSupply (n i : ℕ) : InSupply name n (name (n + i)) :=
  ⟨n + i, Nat.le_add_right n i, rfl⟩

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Slot] in
theorem name_not_inSupply (injective : Function.Injective name) {n m : ℕ}
    (below : m < n) : ¬ InSupply name n (name m) := by
  rintro ⟨m', bound, same⟩
  have := injective same
  omega

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq Slot] in
theorem AvoidsSupply.mono {n n' : ℕ} (le : n ≤ n') {t : Term σ}
    (avoids : AvoidsSupply name n t) : AvoidsSupply name n' t :=
  fun v member inSupply => avoids v member (inSupply.mono name le)

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq Slot] in
theorem AvoidsSupply.applyTerm {n : ℕ} {θ : Subst σ} {t : Term σ}
    (store : StoreAvoidsSupply name n θ) (avoids : AvoidsSupply name n t) :
    AvoidsSupply name n (θ.applyTerm t) := by
  intro x member
  obtain ⟨v, memberV, occurs⟩ := Subst.mem_freeVars_applyTerm.mp member
  exact (store v).2 (avoids v memberV) x occurs

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq Slot] in
theorem StoreAvoidsSupply.mono {n n' : ℕ} (le : n ≤ n') {θ : Subst σ}
    (store : StoreAvoidsSupply name n θ) : StoreAvoidsSupply name n' θ := by
  intro v
  refine ⟨fun inSupply => (store v).1 (inSupply.mono name le), fun notInSupply => ?_⟩
  by_cases inOld : InSupply name n v
  · rw [(store v).1 inOld]
    intro x occurs
    rw [Term.mem_freeVars_var] at occurs
    subst occurs
    exact notInSupply
  · exact ((store v).2 inOld).mono name le

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq Slot] in
theorem AgreeOffSupply.applyTerm {n : ℕ} {δ δ' : Subst σ} {t : Term σ}
    (agree : AgreeOffSupply name n δ δ') (avoids : AvoidsSupply name n t) :
    δ.applyTerm t = δ'.applyTerm t :=
  Subst.applyTerm_congr fun v member => agree v (avoids v member)

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Slot] in
theorem AgreeOffSupply.refl (n : ℕ) (δ : Subst σ) : AgreeOffSupply name n δ δ :=
  fun _ _ => rfl

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Slot] in
theorem AgreeOffSupply.trans {n n' : ℕ} {δ₁ δ₂ δ₃ : Subst σ} (le : n ≤ n')
    (first : AgreeOffSupply name n δ₁ δ₂) (second : AgreeOffSupply name n' δ₂ δ₃) :
    AgreeOffSupply name n δ₁ δ₃ :=
  fun v notIn => (first v notIn).trans (second v fun inSupply => notIn (inSupply.mono name le))

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq Slot] in
/-- Absorbing a store that avoids the supply does not depend on the supply's
values. -/
theorem absorbs_of_agreeOffSupply {n : ℕ} {θ δ δ' : Subst σ}
    (store : StoreAvoidsSupply name n θ) (absorbs : δ.Absorbs θ)
    (agree : AgreeOffSupply name n δ δ') : δ'.Absorbs θ := by
  intro v
  by_cases inSupply : InSupply name n v
  · rw [(store v).1 inSupply]
    rfl
  · rw [← agree.applyTerm name ((store v).2 inSupply), absorbs v, agree v inSupply]

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq Slot] in
/-- The supply's variables from `start` can be given any values without
changing a substitution elsewhere. -/
theorem exists_extension (injective : Function.Injective name) (δ : Subst σ)
    (start arity : ℕ) (values : Fin arity → Term σ) :
    ∃ δ' : Subst σ, (∀ i : Fin arity, δ' (name (start + i)) = values i) ∧
      AgreeOffSupply name start δ δ' := by
  classical
  refine ⟨fun w => if h : ∃ i : Fin arity, name (start + i) = w then values h.choose
    else δ w, ?_, ?_⟩
  · intro i
    have found : ∃ j : Fin arity, name (start + j) = name (start + i) := ⟨i, rfl⟩
    simp only [dif_pos found]
    congr 1
    apply Fin.ext
    have := injective found.choose_spec
    omega
  · intro w notIn
    have missing : ¬ ∃ i : Fin arity, name (start + i) = w := by
      rintro ⟨i, rfl⟩
      exact notIn (name_inSupply name start i)
    simp only [dif_neg missing]

/-! ## Binding a query variable -/

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq Slot] in
/-- Binding `v := t` after an idempotent store stays idempotent when `v` does
not occur in `t` and the store leaves `t`'s variables unbound. -/
theorem idempotent_single_comp {θ : Subst σ} {v : σ.vars} {t : Term σ}
    (idempotent : θ.Absorbs θ) (notOccurs : v ∉ t.freeVars)
    (fixed : ∀ x ∈ t.freeVars, θ x = .var x) :
    (Subst.single v t ∘ₛ θ).Absorbs (Subst.single v t ∘ₛ θ) := by
  refine Subst.comp_idempotent (Subst.single_idempotent notOccurs) fun w => ?_
  apply Subst.applyTerm_eq_self
  intro x member
  rcases Finset.mem_union.mp (Subst.freeVars_single_subset v t (θ w) member) with
    inRead | inTerm
  · exact idempotent.var_fixed (.var w) x inRead
  · exact fixed x inTerm

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq Slot] in
/-- Binding a variable outside the supply to a term avoiding the (possibly
advanced) supply keeps the store avoiding it. -/
theorem storeAvoids_single_comp {n n' : ℕ} {θ : Subst σ} {v : σ.vars} {t : Term σ}
    (le : n ≤ n') (store : StoreAvoidsSupply name n θ)
    (notInSupply : ¬ InSupply name n v) (avoids : AvoidsSupply name n' t) :
    StoreAvoidsSupply name n' (Subst.single v t ∘ₛ θ) := by
  have store' := store.mono name le
  intro w
  constructor
  · intro inSupply
    have different : w ≠ v := fun same => notInSupply (same ▸ inSupply.mono name le)
    change (Subst.single v t).applyTerm (θ w) = .var w
    rw [(store' w).1 inSupply, Subst.applyTerm_var, Subst.single_ne _ different]
  · intro notIn x member
    rcases Finset.mem_union.mp (Subst.freeVars_single_subset v t (θ w) member) with
      inRead | inTerm
    · exact (store' w).2 notIn x inRead
    · exact avoids x inTerm

/-! ## Invariants and exactness -/

/-- The run-time invariant: an idempotent store avoiding the supply, and
registers and slots avoiding the supply. -/
structure WellFormed (state : HeadState σ Slot) : Prop where
  idempotent : state.store.Absorbs state.store
  store : StoreAvoidsSupply name state.supply state.store
  registers : ∀ index term, state.registers index = some term →
    AvoidsSupply name state.supply term
  slots : ∀ slot term, state.slots slot = some term → AvoidsSupply name state.supply term

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Slot] in
/-- A substitution and a frame compatible with a state: the substitution
extends the store and agrees with every bound slot. -/
def Compatible (state : HeadState σ Slot) (δ : Subst σ) (frame : Slot → Term σ) : Prop :=
  δ.Absorbs state.store ∧ ∀ slot term, state.slots slot = some term →
    frame slot = δ.applyTerm term

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Slot] in
/-- `bound` lists exactly the bound slots. -/
def BoundExact (bound : List Slot) (state : HeadState σ Slot) : Prop :=
  ∀ slot, slot ∈ bound ↔ (state.slots slot).isSome

/-- Running `code` from `state` solves the constraint `goal` exactly, up to the
values of fresh variables: every compatible solution survives the run
(`complete`), and every solution compatible with the final state was one
(`sound`). -/
structure Realizes (code : List (HeadOp σ Slot)) (state : HeadState σ Slot)
    (goal : Subst σ → (Slot → Term σ) → Prop) : Prop where
  complete : ∀ δ frame, Compatible state δ frame → goal δ frame →
    ∃ final, exec name code state = some final ∧
      ∃ δ', AgreeOffSupply name state.supply δ δ' ∧ Compatible final δ' frame
  sound : ∀ final, exec name code state = some final →
    ∀ δ frame, Compatible final δ frame → Compatible state δ frame ∧ goal δ frame

/-- A successful run keeps the invariant, never shrinks the supply, keeps every
register below `next`, and leaves exactly the slots in `bound` bound. -/
def Preserves (code : List (HeadOp σ Slot)) (state : HeadState σ Slot) (next : ℕ)
    (bound : List Slot) : Prop :=
  ∀ final, exec name code state = some final →
    WellFormed name final ∧ state.supply ≤ final.supply ∧
      (∀ index, index < next → final.registers index = state.registers index) ∧
      BoundExact bound final

/-- The specification of the code generated for one pattern read from
register `source`. -/
def EmitSpec (generate : ℕ → List Slot → List (HeadOp σ Slot) × ℕ × List Slot)
    (pattern : HeadPattern σ Slot) (source : ℕ) : Prop :=
  ∀ next bound (state : HeadState σ Slot) term,
    state.registers source = some term → WellFormed name state → BoundExact bound state →
    Realizes name (generate next bound).1 state
        (fun δ frame => instantiate frame pattern = δ.applyTerm term) ∧
      Preserves name (generate next bound).1 state next (generate next bound).2.2

theorem Realizes.congr {code : List (HeadOp σ Slot)} {state : HeadState σ Slot}
    {goal goal' : Subst σ → (Slot → Term σ) → Prop}
    (realizes : Realizes name code state goal)
    (same : ∀ δ frame, goal δ frame ↔ goal' δ frame) :
    Realizes name code state goal' where
  complete δ frame compatible holds :=
    realizes.complete δ frame compatible ((same δ frame).mpr holds)
  sound final ran δ frame compatible :=
    let result := realizes.sound final ran δ frame compatible
    ⟨result.1, (same δ frame).mp result.2⟩

/-- Sequencing: the second constraint must not depend on values of the fresh
variables the first code may allocate. -/
theorem Realizes.append {first second : List (HeadOp σ Slot)}
    {state : HeadState σ Slot} {goal₁ goal₂ : Subst σ → (Slot → Term σ) → Prop}
    (realizesFirst : Realizes name first state goal₁)
    (realizesSecond : ∀ mid, exec name first state = some mid →
      state.supply ≤ mid.supply ∧ Realizes name second mid goal₂)
    (stable : ∀ δ δ' frame, AgreeOffSupply name state.supply δ δ' →
      goal₂ δ frame → goal₂ δ' frame) :
    Realizes name (first ++ second) state
      (fun δ frame => goal₁ δ frame ∧ goal₂ δ frame) where
  complete δ frame compatible holds := by
    obtain ⟨mid, ranFirst, δ₁, agree₁, compatible₁⟩ :=
      realizesFirst.complete δ frame compatible holds.1
    obtain ⟨grows, realizesMid⟩ := realizesSecond mid ranFirst
    obtain ⟨final, ranSecond, δ₂, agree₂, compatible₂⟩ :=
      realizesMid.complete δ₁ frame compatible₁ (stable δ δ₁ frame agree₁ holds.2)
    refine ⟨final, ?_, δ₂, agree₁.trans name grows agree₂, compatible₂⟩
    rw [exec_append, ranFirst, Option.bind_some, ranSecond]
  sound final ran δ frame compatible := by
    rw [exec_append, Option.bind_eq_some_iff] at ran
    obtain ⟨mid, ranFirst, ranSecond⟩ := ran
    obtain ⟨compatibleMid, holds₂⟩ :=
      ((realizesSecond mid ranFirst).2).sound final ranSecond δ frame compatible
    obtain ⟨compatibleState, holds₁⟩ :=
      realizesFirst.sound mid ranFirst δ frame compatibleMid
    exact ⟨compatibleState, holds₁, holds₂⟩

/-! ## One instruction at a time -/

theorem bindSlot_spec {state : HeadState σ Slot} {source next : ℕ} {slot : Slot}
    {term : Term σ} {bound : List Slot}
    (loaded : state.registers source = some term) (wf : WellFormed name state)
    (exact : BoundExact bound state) (unbound : slot ∉ bound) :
    Realizes name [.bindSlot source slot] state
        (fun δ frame => frame slot = δ.applyTerm term) ∧
      Preserves name [.bindSlot source slot] state next (slot :: bound) := by
  have ran : exec name [.bindSlot source slot] state =
      some { state with slots := Function.update state.slots slot (some term) } := by
    simp [exec_singleton, step, loaded]
  have empty : state.slots slot = none := by
    cases present : state.slots slot with
    | none => rfl
    | some previous =>
        exact absurd ((exact slot).mpr (by simp [present])) unbound
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro δ frame compatible holds
    refine ⟨_, ran, δ, AgreeOffSupply.refl name _ δ, compatible.1, ?_⟩
    intro other value bound'
    dsimp only at bound'
    by_cases same : other = slot
    · subst same
      simp only [Function.update_self, Option.some.injEq] at bound'
      subst bound'
      exact holds
    · rw [Function.update_of_ne same] at bound'
      exact compatible.2 other value bound'
  · intro final finalRan δ frame compatible
    rw [ran, Option.some.injEq] at finalRan
    subst finalRan
    refine ⟨⟨compatible.1, fun other value bound' => ?_⟩, ?_⟩
    · have different : other ≠ slot := by
        rintro rfl
        rw [empty] at bound'
        cases bound'
      exact compatible.2 other value (by
        change Function.update state.slots slot (some term) other = some value
        rw [Function.update_of_ne different]
        exact bound')
    · exact compatible.2 slot term (by simp)
  · intro final finalRan
    rw [ran, Option.some.injEq] at finalRan
    subst finalRan
    refine ⟨⟨wf.idempotent, wf.store, wf.registers, fun other value bound' => ?_⟩,
      le_rfl, fun _ _ => rfl, fun other => ?_⟩
    · dsimp only at bound' ⊢
      by_cases same : other = slot
      · subst same
        simp only [Function.update_self, Option.some.injEq] at bound'
        subst bound'
        exact wf.registers source _ loaded
      · rw [Function.update_of_ne same] at bound'
        exact wf.slots other value bound'
    · dsimp only
      by_cases same : other = slot
      · subst same
        simp
      · simp only [List.mem_cons, same, false_or, ne_eq, not_false_eq_true,
          Function.update_of_ne]
        exact exact other

theorem equateSlot_spec {state : HeadState σ Slot} {source next : ℕ} {slot : Slot}
    {term : Term σ} {bound : List Slot}
    (loaded : state.registers source = some term) (wf : WellFormed name state)
    (exact : BoundExact bound state) (member : slot ∈ bound) :
    Realizes name [.equateSlot source slot] state
        (fun δ frame => frame slot = δ.applyTerm term) ∧
      Preserves name [.equateSlot source slot] state next bound := by
  obtain ⟨previous, bound'⟩ : ∃ previous, state.slots slot = some previous :=
    Option.isSome_iff_exists.mp ((exact slot).mp member)
  have ran : exec name [.equateSlot source slot] state =
      (unifyTotal [(state.store.applyTerm previous, state.store.applyTerm term)]).map
        fun unifier => { state with store := unifier ∘ₛ state.store } := by
    simp [exec_singleton, step, loaded, bound']
  -- every variable of the solved pair is unbound in the store and avoids the supply
  have pairFixed : ∀ x ∈ eqVars [(state.store.applyTerm previous,
      state.store.applyTerm term)], state.store x = .var x := by
    intro x memberX
    simp only [eqVars, Finset.union_empty, Finset.mem_union] at memberX
    rcases memberX with inPrevious | inTerm
    · exact wf.idempotent.var_fixed previous x inPrevious
    · exact wf.idempotent.var_fixed term x inTerm
  have pairAvoids : ∀ x ∈ eqVars [(state.store.applyTerm previous,
      state.store.applyTerm term)], ¬ InSupply name state.supply x := by
    intro x memberX
    simp only [eqVars, Finset.union_empty, Finset.mem_union] at memberX
    rcases memberX with inPrevious | inTerm
    · exact AvoidsSupply.applyTerm name wf.store (wf.slots slot previous bound') x inPrevious
    · exact AvoidsSupply.applyTerm name wf.store (wf.registers source term loaded) x inTerm
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro δ frame compatible holds
    have unifies : Unifies δ [(state.store.applyTerm previous, state.store.applyTerm term)] := by
      intro equation memberEquation
      simp only [List.mem_singleton] at memberEquation
      subst memberEquation
      change δ.applyTerm (state.store.applyTerm previous) =
        δ.applyTerm (state.store.applyTerm term)
      rw [compatible.1.applyTerm, compatible.1.applyTerm,
        ← compatible.2 slot previous bound', holds]
    obtain ⟨unifier, accepted⟩ := unifyTotal_complete ⟨δ, unifies⟩
    have absorbsUnifier : δ.Absorbs unifier :=
      Subst.absorbs_of_moreGeneral
        (unifyTotal_relevantIdempotent _ unifier accepted).absorbs
        (unifyTotal_mgu _ unifier accepted δ unifies)
    refine ⟨{ state with store := unifier ∘ₛ state.store }, ?_, δ,
      AgreeOffSupply.refl name _ δ, absorbsUnifier.comp compatible.1, compatible.2⟩
    rw [ran, accepted]
    rfl
  · intro final finalRan δ frame compatible
    rw [ran, Option.map_eq_some_iff] at finalRan
    obtain ⟨unifier, accepted, rfl⟩ := finalRan
    have absorbsFinal : δ.Absorbs (unifier ∘ₛ state.store) := compatible.1
    have absorbsStore : δ.Absorbs state.store :=
      absorbsFinal.trans (Subst.comp_absorbs wf.idempotent)
    refine ⟨⟨absorbsStore, compatible.2⟩, ?_⟩
    have solved := unifyTotal_sound _ unifier accepted
      (state.store.applyTerm previous, state.store.applyTerm term) (by simp)
    change frame slot = δ.applyTerm term
    rw [compatible.2 slot previous bound', ← absorbsFinal.applyTerm previous,
      ← absorbsFinal.applyTerm term, Subst.applyTerm_comp, Subst.applyTerm_comp]
    exact congrArg δ.applyTerm solved
  · intro final finalRan
    rw [ran, Option.map_eq_some_iff] at finalRan
    obtain ⟨unifier, accepted, rfl⟩ := finalRan
    have relevant := unifyTotal_relevantIdempotent _ unifier accepted
    refine ⟨⟨?_, ?_, wf.registers, wf.slots⟩, le_rfl, fun _ _ => rfl, exact⟩
    · refine Subst.comp_idempotent relevant.absorbs fun w => ?_
      apply Subst.applyTerm_eq_self
      intro x memberX
      rcases Finset.mem_union.mp (relevant.freeVars_applyTerm_subset _ memberX) with
        inRead | inPair
      · exact wf.idempotent.var_fixed (.var w) x inRead
      · exact pairFixed x inPair
    · intro w
      constructor
      · intro inSupply
        change unifier.applyTerm (state.store w) = .var w
        rw [(wf.store w).1 inSupply, Subst.applyTerm_var]
        exact relevant.fixes w fun inPair => pairAvoids w inPair inSupply
      · intro notIn x memberX
        rcases Finset.mem_union.mp (relevant.freeVars_applyTerm_subset _ memberX) with
          inRead | inPair
        · exact (wf.store w).2 notIn x inRead
        · exact pairAvoids x inPair

theorem constant_spec {state : HeadState σ Slot} {source next : ℕ}
    {value : σ.constants} {term : Term σ} {bound : List Slot}
    (loaded : state.registers source = some term) (wf : WellFormed name state)
    (exact : BoundExact bound state) :
    Realizes name [.constant source value] state
        (fun δ _ => Term.const value = δ.applyTerm term) ∧
      Preserves name [.constant source value] state next bound := by
  have readAvoids : AvoidsSupply name state.supply (state.store.applyTerm term) :=
    AvoidsSupply.applyTerm name wf.store (wf.registers source term loaded)
  cases read : state.store.applyTerm term with
  | var v =>
      have ran : exec name [.constant source value] state =
          some { state with store := Subst.single v (.const value) ∘ₛ state.store } := by
        simp [exec_singleton, step, loaded, read]
      have vFixed : state.store v = .var v :=
        wf.idempotent.var_fixed term v (by rw [read]; exact Term.mem_freeVars_var.mpr rfl)
      have vOutside : ¬ InSupply name state.supply v :=
        readAvoids v (by rw [read]; exact Term.mem_freeVars_var.mpr rfl)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro δ frame compatible holds
        have equates : δ v = δ.applyTerm (.const value) := by
          rw [Subst.applyTerm_const, holds, ← compatible.1.applyTerm term, read,
            Subst.applyTerm_var]
        exact ⟨{ state with store := Subst.single v (.const value) ∘ₛ state.store }, ran, δ,
          AgreeOffSupply.refl name _ δ, (Subst.absorbs_single equates).comp compatible.1,
          compatible.2⟩
      · intro final finalRan δ frame compatible
        rw [ran, Option.some.injEq] at finalRan
        subst finalRan
        have absorbsStore : δ.Absorbs state.store :=
          compatible.1.trans (Subst.comp_absorbs wf.idempotent)
        refine ⟨⟨absorbsStore, compatible.2⟩, ?_⟩
        have atV := compatible.1 v
        change δ.applyTerm ((Subst.single v (.const value)).applyTerm (state.store v)) = δ v
          at atV
        rw [vFixed, Subst.applyTerm_var, Subst.single_eq, Subst.applyTerm_const] at atV
        change Term.const value = δ.applyTerm term
        rw [← absorbsStore.applyTerm term, read, Subst.applyTerm_var, ← atV]
      · intro final finalRan
        rw [ran, Option.some.injEq] at finalRan
        subst finalRan
        refine ⟨⟨?_, ?_, wf.registers, wf.slots⟩, le_rfl, fun _ _ => rfl, exact⟩
        · exact idempotent_single_comp wf.idempotent Term.not_mem_freeVars_const
            fun x memberX => absurd memberX Term.not_mem_freeVars_const
        · exact storeAvoids_single_comp name le_rfl wf.store vOutside
            fun x memberX => absurd memberX Term.not_mem_freeVars_const
  | const actual =>
      by_cases same : value = actual
      · subst same
        have ran : exec name [.constant source value] state = some state := by
          simp [exec_singleton, step, loaded, read]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro δ frame compatible _
          exact ⟨state, ran, δ, AgreeOffSupply.refl name _ δ, compatible⟩
        · intro final finalRan δ frame compatible
          rw [ran, Option.some.injEq] at finalRan
          subst finalRan
          refine ⟨compatible, ?_⟩
          rw [← compatible.1.applyTerm term, read, Subst.applyTerm_const]
        · intro final finalRan
          rw [ran, Option.some.injEq] at finalRan
          subst finalRan
          exact ⟨wf, le_rfl, fun _ _ => rfl, exact⟩
      · have ran : exec name [.constant source value] state = none := by
          simp [exec_singleton, step, loaded, read, same]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro δ frame compatible holds
          rw [← compatible.1.applyTerm term, read, Subst.applyTerm_const] at holds
          exact absurd (Term.const.inj holds) same
        · intro final finalRan
          rw [ran] at finalRan
          cases finalRan
        · intro final finalRan
          rw [ran] at finalRan
          cases finalRan
  | app actual children =>
      have ran : exec name [.constant source value] state = none := by
        simp [exec_singleton, step, loaded, read]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro δ frame compatible holds
        rw [← compatible.1.applyTerm term, read, Subst.applyTerm_app] at holds
        cases holds
      · intro final finalRan
        rw [ran] at finalRan
        cases finalRan
      · intro final finalRan
        rw [ran] at finalRan
        cases finalRan

/-! ## Sequences of patterns -/

theorem emitSeq_spec {α : Type*}
    (emitOne : α → ℕ → List Slot → List (HeadOp σ Slot) × ℕ × List Slot)
    (grows : ∀ task next bound, next ≤ (emitOne task next bound).2.1)
    (pattern : α → HeadPattern σ Slot) (register : α → ℕ) (terms : α → Term σ) :
    ∀ (tasks : List α),
      (∀ task ∈ tasks, EmitSpec name (emitOne task) (pattern task) (register task)) →
      ∀ next bound (state : HeadState σ Slot),
        (∀ task ∈ tasks, register task < next ∧
          state.registers (register task) = some (terms task)) →
        WellFormed name state → BoundExact bound state →
        Realizes name (emitSeq emitOne tasks next bound).1 state
            (fun δ frame => ∀ task ∈ tasks,
              instantiate frame (pattern task) = δ.applyTerm (terms task)) ∧
          Preserves name (emitSeq emitOne tasks next bound).1 state next
            (emitSeq emitOne tasks next bound).2.2
  | [], _, next, bound, state, _, wf, exact => by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro δ frame compatible _
        exact ⟨state, rfl, δ, AgreeOffSupply.refl name _ δ, compatible⟩
      · intro final finalRan δ frame compatible
        simp only [emitSeq, exec, Option.some.injEq] at finalRan
        subst finalRan
        exact ⟨compatible, fun _ member => absurd member List.not_mem_nil⟩
      · intro final finalRan
        simp only [emitSeq, exec, Option.some.injEq] at finalRan
        subst finalRan
        exact ⟨wf, le_rfl, fun _ _ => rfl, exact⟩
  | task :: rest, each, next, bound, state, loaded, wf, exact => by
      obtain ⟨eachFirst, eachRest⟩ := List.forall_mem_cons.mp each
      obtain ⟨⟨_, loadedFirst⟩, loadedRest⟩ := List.forall_mem_cons.mp loaded
      set first := emitOne task next bound with firstEq
      obtain ⟨realizesFirst, preservesFirst⟩ :=
        eachFirst next bound state (terms task) loadedFirst wf exact
      have atMid : ∀ mid, exec name first.1 state = some mid →
          state.supply ≤ mid.supply ∧
          Realizes name (emitSeq emitOne rest first.2.1 first.2.2).1 mid
              (fun δ frame => ∀ task ∈ rest,
                instantiate frame (pattern task) = δ.applyTerm (terms task)) ∧
            Preserves name (emitSeq emitOne rest first.2.1 first.2.2).1 mid first.2.1
              (emitSeq emitOne rest first.2.1 first.2.2).2.2 := by
        intro mid ran
        obtain ⟨wfMid, grew, kept, exactMid⟩ := preservesFirst mid ran
        refine ⟨grew, emitSeq_spec emitOne grows pattern register terms rest eachRest
          first.2.1 first.2.2 mid (fun other member => ?_) wfMid exactMid⟩
        obtain ⟨below, loadedOther⟩ := loadedRest other member
        exact ⟨below.trans_le (grows task next bound),
          (kept (register other) below).trans loadedOther⟩
      have stable : ∀ δ δ' frame, AgreeOffSupply name state.supply δ δ' →
          (∀ task ∈ rest, instantiate frame (pattern task) = δ.applyTerm (terms task)) →
          ∀ task ∈ rest, instantiate frame (pattern task) = δ'.applyTerm (terms task) := by
        intro δ δ' frame agree holds other member
        rw [holds other member]
        exact agree.applyTerm name
          (wf.registers (register other) (terms other) (loadedRest other member).2)
      refine ⟨?_, ?_⟩
      · refine (Realizes.append name realizesFirst
          (fun mid ran => ⟨(atMid mid ran).1, (atMid mid ran).2.1⟩) stable).congr name ?_
        intro δ frame
        exact (List.forall_mem_cons
          (p := fun task => instantiate frame (pattern task) = δ.applyTerm (terms task))).symm
      · intro final finalRan
        change exec name (first.1 ++ (emitSeq emitOne rest first.2.1 first.2.2).1) state =
          some final at finalRan
        rw [exec_append, Option.bind_eq_some_iff] at finalRan
        obtain ⟨mid, ranFirst, ranRest⟩ := finalRan
        obtain ⟨grewFirst, _, preservesRest⟩ := atMid mid ranFirst
        obtain ⟨wfFinal, grewRest, keptRest, exactFinal⟩ := preservesRest final ranRest
        obtain ⟨_, _, keptFirst, _⟩ := preservesFirst mid ranFirst
        refine ⟨wfFinal, grewFirst.trans grewRest, fun index below => ?_, exactFinal⟩
        rw [keptRest index (below.trans_le (grows task next bound)), keptFirst index below]

/-! ## Constructors -/

theorem node_spec (injective : Function.Injective name) {function : σ.functionSymbols}
    {children : Fin (σ.functionArity function) → HeadPattern σ Slot}
    (childSpec : ∀ i source, EmitSpec name (emit (children i) source) (children i) source)
    {source next : ℕ} {bound : List Slot} {state : HeadState σ Slot} {term : Term σ}
    (loaded : state.registers source = some term) (wf : WellFormed name state)
    (exact : BoundExact bound state) :
    Realizes name
        (emit (Term.app (σ := slotSignature σ Slot) function children) source next bound).1
        state
        (fun δ frame => instantiate frame (Term.app (σ := slotSignature σ Slot) function children) =
          δ.applyTerm term) ∧
      Preserves name
        (emit (Term.app (σ := slotSignature σ Slot) function children) source next bound).1
        state next
        (emit (Term.app (σ := slotSignature σ Slot) function children) source next bound).2.2 := by
  obtain ⟨body, bodyEq⟩ : ∃ body, body = emitSeq
      (fun (i : Fin (σ.functionArity function)) => emit (children i) (next + i))
      (List.finRange (σ.functionArity function)) (next + σ.functionArity function) bound :=
    ⟨_, rfl⟩
  have code : emit (Term.app (σ := slotSignature σ Slot) function children) source next bound =
      (.node source function next :: body.1, body.2.1, body.2.2) := by
    rw [bodyEq]
    rfl
  rw [code]
  have readAvoids : AvoidsSupply name state.supply (state.store.applyTerm term) :=
    AvoidsSupply.applyTerm name wf.store (wf.registers source term loaded)
  -- the children's code, from any state holding the children in their registers
  have bodySpec : ∀ (mid : HeadState σ Slot) (values : Fin (σ.functionArity function) → Term σ),
      (∀ i : Fin (σ.functionArity function), mid.registers (next + i) = some (values i)) →
      WellFormed name mid → BoundExact bound mid →
      Realizes name body.1 mid
          (fun δ frame => ∀ i ∈ List.finRange (σ.functionArity function),
            instantiate frame (children i) = δ.applyTerm (values i)) ∧
        Preserves name body.1 mid (next + σ.functionArity function) body.2.2 := by
    intro mid values holding wfMid exactMid
    rw [bodyEq]
    exact emitSeq_spec name (fun i => emit (children i) (next + i))
      (fun i next' bound' => le_emit_next (children i) (next + i) next' bound')
      children (fun i => next + i) values (List.finRange _)
      (fun i _ => childSpec i (next + i)) (next + σ.functionArity function) bound mid
      (fun i _ => ⟨by omega, holding i⟩) wfMid exactMid
  have goalChildren : ∀ (δ : Subst σ) (frame : Slot → Term σ)
      (values : Fin (σ.functionArity function) → Term σ),
      (∀ i ∈ List.finRange (σ.functionArity function),
          instantiate frame (children i) = δ.applyTerm (values i)) ↔
        instantiate frame (Term.app (σ := slotSignature σ Slot) function children) =
          Term.app function fun i => δ.applyTerm (values i) := by
    intro δ frame values
    simp only [instantiate, Term.app.injEq, heq_eq_eq, true_and, List.mem_finRange,
      forall_const]
    exact ⟨fun holds => funext holds, fun holds i => congrFun holds i⟩
  cases read : state.store.applyTerm term with
  | var v =>
      have vOutside : ¬ InSupply name state.supply v :=
        readAvoids v (by rw [read]; exact Term.mem_freeVars_var.mpr rfl)
      have vFixed : state.store v = .var v :=
        wf.idempotent.var_fixed term v (by rw [read]; exact Term.mem_freeVars_var.mpr rfl)
      have freshVars : ∀ x ∈ (Term.app function
          (freshVariables name state.supply (σ.functionArity function))).freeVars,
          ∃ i : Fin (σ.functionArity function), x = name (state.supply + i) := by
        intro x memberX
        obtain ⟨i, memberI⟩ := Term.mem_freeVars_app.mp memberX
        exact ⟨i, Term.mem_freeVars_var.mp memberI⟩
      have notOccurs : v ∉ (Term.app function
          (freshVariables name state.supply (σ.functionArity function))).freeVars := by
        intro memberV
        obtain ⟨i, rfl⟩ := freshVars v memberV
        exact vOutside (name_inSupply name state.supply i)
      have stepped : step name (.node source function next) state =
          some (bindFreshNode name state function next v) := by
        simp [step, loaded, read]
      have ran : ∀ final, exec name (.node source function next :: body.1) state = some final ↔
          exec name body.1 (bindFreshNode name state function next v) = some final := by
        intro final
        simp only [exec, stepped, Option.bind_some]
      have wfMid : WellFormed name (bindFreshNode name state function next v) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact idempotent_single_comp wf.idempotent notOccurs fun x memberX => by
            obtain ⟨i, rfl⟩ := freshVars x memberX
            exact (wf.store _).1 (name_inSupply name state.supply i)
        · refine storeAvoids_single_comp name (Nat.le_add_right _ _) wf.store vOutside ?_
          intro x memberX
          obtain ⟨i, rfl⟩ := freshVars x memberX
          exact name_not_inSupply name injective (by simp [bindFreshNode])
        · intro index value holds
          rcases loadChildren_cases _ _ _ index value holds with ⟨i, rfl⟩ | old
          · intro x memberX
            rw [freshVariables, Term.mem_freeVars_var] at memberX
            subst memberX
            exact name_not_inSupply name injective (by simp [bindFreshNode])
          · exact (wf.registers index value old).mono name (Nat.le_add_right _ _)
        · intro slot value holds
          exact (wf.slots slot value holds).mono name (Nat.le_add_right _ _)
      obtain ⟨realizesBody, preservesBody⟩ :=
        bodySpec (bindFreshNode name state function next v)
          (freshVariables name state.supply (σ.functionArity function))
          (fun i => loadChildren_at _ _ _ i) wfMid exact
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro δ frame compatible holds
        have atV : δ v = instantiate frame (Term.app (σ := slotSignature σ Slot) function children) := by
          rw [holds, ← compatible.1.applyTerm term, read, Subst.applyTerm_var]
        obtain ⟨δ₁, onFresh, agree₁⟩ := exists_extension name injective δ state.supply
          (σ.functionArity function) (fun i => instantiate frame (children i))
        have compatibleMid : Compatible (bindFreshNode name state function next v) δ₁ frame := by
          refine ⟨?_, fun slot value holds' => ?_⟩
          · refine Subst.Absorbs.comp (Subst.absorbs_single ?_)
              (absorbs_of_agreeOffSupply name wf.store compatible.1 agree₁)
            rw [← agree₁ v vOutside, atV, Subst.applyTerm_app]
            simp only [instantiate]
            congr 1
            funext i
            exact (onFresh i).symm
          · rw [compatible.2 slot value holds']
            exact agree₁.applyTerm name (wf.slots slot value holds')
        have holdsChildren : ∀ i ∈ List.finRange (σ.functionArity function),
            instantiate frame (children i) =
              δ₁.applyTerm (freshVariables name state.supply (σ.functionArity function) i) :=
          fun i _ => (onFresh i).symm
        obtain ⟨final, ranBody, δ₂, agree₂, compatibleFinal⟩ :=
          realizesBody.complete δ₁ frame compatibleMid holdsChildren
        exact ⟨final, (ran final).mpr ranBody, δ₂,
          agree₁.trans name (Nat.le_add_right _ _) agree₂, compatibleFinal⟩
      · intro final finalRan δ frame compatible
        obtain ⟨compatibleMid, holdsChildren⟩ :=
          realizesBody.sound final ((ran final).mp finalRan) δ frame compatible
        have absorbsStore : δ.Absorbs state.store :=
          compatibleMid.1.trans (Subst.comp_absorbs wf.idempotent)
        refine ⟨⟨absorbsStore, compatibleMid.2⟩, ?_⟩
        have atV := compatibleMid.1 v
        change δ.applyTerm ((Subst.single v (.app function
            (freshVariables name state.supply (σ.functionArity function)))).applyTerm
              (state.store v)) = δ v at atV
        rw [vFixed, Subst.applyTerm_var, Subst.single_eq] at atV
        rw [← absorbsStore.applyTerm term, read, Subst.applyTerm_var, ← atV,
          Subst.applyTerm_app]
        exact ((goalChildren δ frame _).mp holdsChildren)
      · intro final finalRan
        obtain ⟨wfFinal, grew, kept, exactFinal⟩ :=
          preservesBody final ((ran final).mp finalRan)
        refine ⟨wfFinal, (Nat.le_add_right _ _).trans grew, fun index below => ?_,
          exactFinal⟩
        rw [kept index (by omega)]
        exact loadChildren_below _ _ below
  | const actual =>
      have ran : exec name (.node source function next :: body.1) state = none := by
        simp [exec, step, loaded, read]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro δ frame compatible holds
        rw [← compatible.1.applyTerm term, read, Subst.applyTerm_const] at holds
        simp [instantiate] at holds
      · intro final finalRan
        rw [ran] at finalRan
        cases finalRan
      · intro final finalRan
        rw [ran] at finalRan
        cases finalRan
  | app actual actualChildren =>
      by_cases same : actual = function
      · subst same
        have stepped : step name (.node source actual next) state =
            some (loadNode state next actualChildren) := by
          simp [step, loaded, read]
        have ran : ∀ final, exec name (.node source actual next :: body.1) state = some final ↔
            exec name body.1 (loadNode state next actualChildren) = some final := by
          intro final
          simp only [exec, stepped, Option.bind_some]
        have childrenAvoid : ∀ i, AvoidsSupply name state.supply (actualChildren i) := by
          intro i x memberX
          rw [read] at readAvoids
          exact readAvoids x (Term.mem_freeVars_app.mpr ⟨i, memberX⟩)
        have wfMid : WellFormed name (loadNode state next actualChildren) := by
          refine ⟨wf.idempotent, wf.store, ?_, wf.slots⟩
          intro index value holds
          rcases loadChildren_cases _ _ _ index value holds with ⟨i, rfl⟩ | old
          · exact childrenAvoid i
          · exact wf.registers index value old
        obtain ⟨realizesBody, preservesBody⟩ :=
          bodySpec (loadNode state next actualChildren) actualChildren
            (fun i => loadChildren_at _ _ _ i) wfMid exact
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro δ frame compatible holds
          have childrenHold : ∀ i ∈ List.finRange (σ.functionArity actual),
              instantiate frame (children i) = δ.applyTerm (actualChildren i) := by
            refine (goalChildren δ frame actualChildren).mpr ?_
            rw [holds, ← compatible.1.applyTerm term, read, Subst.applyTerm_app]
          obtain ⟨final, ranBody, δ₂, agree₂, compatibleFinal⟩ :=
            realizesBody.complete δ frame compatible childrenHold
          exact ⟨final, (ran final).mpr ranBody, δ₂, agree₂, compatibleFinal⟩
        · intro final finalRan δ frame compatible
          obtain ⟨compatibleMid, holdsChildren⟩ :=
            realizesBody.sound final ((ran final).mp finalRan) δ frame compatible
          have absorbsStore : δ.Absorbs state.store := compatibleMid.1
          refine ⟨compatibleMid, ?_⟩
          rw [← absorbsStore.applyTerm term, read, Subst.applyTerm_app]
          exact (goalChildren δ frame actualChildren).mp holdsChildren
        · intro final finalRan
          obtain ⟨wfFinal, grew, kept, exactFinal⟩ :=
            preservesBody final ((ran final).mp finalRan)
          refine ⟨wfFinal, grew, fun index below => ?_, exactFinal⟩
          rw [kept index (by omega)]
          exact loadChildren_below _ _ below
      · have ran : exec name (.node source function next :: body.1) state = none := by
          simp [exec, step, loaded, read, same]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro δ frame compatible holds
          rw [← compatible.1.applyTerm term, read, Subst.applyTerm_app] at holds
          simp only [instantiate, Term.app.injEq] at holds
          exact absurd holds.1.symm same
        · intro final finalRan
          rw [ran] at finalRan
          cases finalRan
        · intro final finalRan
          rw [ran] at finalRan
          cases finalRan

/-! ## The emitted code solves its pattern -/

theorem emit_spec (injective : Function.Injective name) (pattern : HeadPattern σ Slot) :
    ∀ source, EmitSpec name (emit pattern source) pattern source := by
  induction pattern with
  | var slot =>
      intro source next bound state term loaded wf exact
      by_cases member : slot ∈ bound
      · have code : emit (Term.var (σ := slotSignature σ Slot) slot) source next bound =
            ([.equateSlot source slot], next, bound) := by
          simp [emit, member]
        rw [code]
        exact equateSlot_spec name loaded wf exact member
      · have code : emit (Term.var (σ := slotSignature σ Slot) slot) source next bound =
            ([.bindSlot source slot], next, slot :: bound) := by
          simp [emit, member]
        rw [code]
        exact bindSlot_spec name loaded wf exact member
  | const value =>
      intro source next bound state term loaded wf exact
      exact constant_spec name loaded wf exact
  | app function children ih =>
      intro source next bound state term loaded wf exact
      exact node_spec name injective ih loaded wf exact

/-! ## Whole heads -/

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Slot] in
/-- The state an activation starts from: the arguments in registers `0, 1, ...`
and no slot bound. -/
def initialState (args : List (Term σ)) (θ : Subst σ) (n : ℕ) : HeadState σ Slot where
  registers index := args[index]?
  slots _ := none
  store := θ
  supply := n

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Slot] in
/-- A solution of the head `patterns` against `args` under the store `θ`: `δ`
extends the store and instantiating the head with `frame` gives the arguments
under `δ`. -/
def HeadSolution (θ : Subst σ) (patterns : List (HeadPattern σ Slot))
    (args : List (Term σ)) (δ : Subst σ) (frame : Slot → Term σ) : Prop :=
  δ.Absorbs θ ∧
    List.Forall₂ (fun pattern arg => instantiate frame pattern = δ.applyTerm arg) patterns args

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq Slot] in
/-- What an activation assumes of its caller: an idempotent store avoiding the
fresh supply, and arguments avoiding it. -/
structure EntryCondition (θ : Subst σ) (n : ℕ) (args : List (Term σ)) : Prop where
  idempotent : θ.Absorbs θ
  store : StoreAvoidsSupply name n θ
  args : ∀ arg ∈ args, AvoidsSupply name n arg

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq Slot] in
theorem initialState_wellFormed {args : List (Term σ)} {θ : Subst σ} {n : ℕ}
    (entry : EntryCondition name θ n args) :
    WellFormed name (initialState (Slot := Slot) args θ n) where
  idempotent := entry.idempotent
  store := entry.store
  registers _ term loaded := entry.args term (List.mem_of_getElem? loaded)
  slots _ _ bound := by cases bound

/-- The code emitted for a whole head solves it exactly. -/
theorem emitHead_spec (injective : Function.Injective name)
    (patterns : List (HeadPattern σ Slot)) (args : List (Term σ)) (θ : Subst σ) (n : ℕ)
    (lengths : patterns.length = args.length) (entry : EntryCondition name θ n args) :
    Realizes name (emitHead patterns) (initialState args θ n)
        (fun δ frame => List.Forall₂
          (fun pattern arg => instantiate frame pattern = δ.applyTerm arg) patterns args) ∧
      Preserves name (emitHead patterns) (initialState args θ n) patterns.length
        (emitSeq (fun (j : Fin patterns.length) => emit (patterns.get j) j)
          (List.finRange patterns.length) patterns.length []).2.2 := by
  obtain ⟨realizes, preserves⟩ := emitSeq_spec name
    (fun (j : Fin patterns.length) => emit (patterns.get j) j)
    (fun j next bound => le_emit_next (patterns.get j) j next bound)
    (fun j => patterns.get j) (fun j => j) (fun j => args.get (Fin.cast lengths j))
    (List.finRange patterns.length)
    (fun j _ => emit_spec name injective (patterns.get j) j) patterns.length []
    (initialState args θ n)
    (fun j _ => ⟨j.isLt, by simp [initialState]⟩)
    (initialState_wellFormed name entry) (fun slot => by simp [initialState])
  refine ⟨realizes.congr name fun δ frame => ?_, preserves⟩
  rw [List.forall₂_iff_get]
  constructor
  · intro holds
    exact ⟨lengths, fun i below _ => holds ⟨i, below⟩ (List.mem_finRange _)⟩
  · rintro ⟨_, holds⟩ j _
    exact holds j j.isLt (lengths ▸ j.isLt)

end Machine

section Activation

variable {σ : LPSignature.{0, 0, r, 0}}
variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
variable (name : ℕ → σ.vars)

/-- The compiled activation of an equation head with `k` slots: check the
arity, run the emitted code on the arguments, then give every slot the head
did not bind a fresh variable (a body-local variable).  The result is the
frame, the store and the supply. -/
def compiledActivation {k : ℕ} (patterns : List (HeadPattern σ (Fin k)))
    (args : List (Term σ)) (θ : Subst σ) (n : ℕ) :
    Option ((Fin k → Term σ) × Subst σ × ℕ) :=
  if patterns.length = args.length then
    (exec name (emitHead patterns) (initialState args θ n)).map fun final =>
      (fun i => (final.slots i).getD (.var (name (final.supply + i))), final.store,
        final.supply + k)
  else none

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- `general` has `specific` as an instance on every variable outside the supply
at `n` and on every slot. -/
def InstanceOffSupply {Slot : Type*} (n : ℕ) (general specific : Subst σ × (Slot → Term σ)) :
    Prop :=
  ∃ ρ : Subst σ, (∀ v, ¬ InSupply name n v → specific.1 v = ρ.applyTerm (general.1 v)) ∧
    ∀ slot, specific.2 slot = ρ.applyTerm (general.2 slot)

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- The substitution renaming every variable `x` to `ρ x`. -/
def renameVars (ρ : σ.vars → σ.vars) : Subst σ := fun x => .var (ρ x)

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- `specific` is `general` with its variables renamed, on every variable
outside the supply at `n` and on every slot: the renaming is injective on the
variables `general` shows there. -/
def VariantOffSupply {Slot : Type*} (n : ℕ) (general specific : Subst σ × (Slot → Term σ)) :
    Prop :=
  ∃ ρ : σ.vars → σ.vars,
    Set.InjOn ρ {x | (∃ v, ¬ InSupply name n v ∧ x ∈ (general.1 v).freeVars) ∨
      ∃ slot, x ∈ (general.2 slot).freeVars} ∧
    (∀ v, ¬ InSupply name n v → specific.1 v = (renameVars ρ).applyTerm (general.1 v)) ∧
    ∀ slot, specific.2 slot = (renameVars ρ).applyTerm (general.2 slot)

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- A term that a substitution sends to a variable is a variable. -/
private theorem eq_var_of_applyTerm_eq_var {θ : Subst σ} {t : Term σ} {x : σ.vars}
    (sends : θ.applyTerm t = .var x) : ∃ y, t = .var y ∧ θ y = .var x := by
  cases t with
  | var y => exact ⟨y, rfl, sends⟩
  | const c => simp [Subst.applyTerm_const] at sends
  | app f ts => simp [Subst.applyTerm_app] at sends

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- Results that are instances of each other are variants: mutual instances
differ only by a renaming of the variables they show. -/
theorem variantOffSupply_of_instances {Slot : Type*} {n : ℕ}
    {general specific : Subst σ × (Slot → Term σ)}
    (forward : InstanceOffSupply name n general specific)
    (backward : InstanceOffSupply name n specific general) :
    VariantOffSupply name n general specific := by
  classical
  obtain ⟨ρ₁, forwardVars, forwardSlots⟩ := forward
  obtain ⟨ρ₂, backwardVars, backwardSlots⟩ := backward
  set shown : Set σ.vars := {x | (∃ v, ¬ InSupply name n v ∧ x ∈ (general.1 v).freeVars) ∨
    ∃ slot, x ∈ (general.2 slot).freeVars} with shownEq
  -- `ρ₂ ∘ ρ₁` fixes every shown variable
  have roundTrip : ∀ x ∈ shown, ρ₂.applyTerm (ρ₁ x) = .var x := by
    rintro x (⟨v, outside, member⟩ | ⟨slot, member⟩)
    · have fixed : (ρ₂ ∘ₛ ρ₁).applyTerm (general.1 v) = general.1 v := by
        rw [Subst.applyTerm_comp, ← forwardVars v outside, ← backwardVars v outside]
      exact Subst.var_fixed_of_applyTerm_eq_self fixed x member
    · have fixed : (ρ₂ ∘ₛ ρ₁).applyTerm (general.2 slot) = general.2 slot := by
        rw [Subst.applyTerm_comp, ← forwardSlots slot, ← backwardSlots slot]
      exact Subst.var_fixed_of_applyTerm_eq_self fixed x member
  have toVar : ∀ x ∈ shown, ∃ y, ρ₁ x = .var y := fun x member =>
    (eq_var_of_applyTerm_eq_var (roundTrip x member)).imp fun _ found => found.1
  let ρ : σ.vars → σ.vars := fun x => if found : ∃ y, ρ₁ x = .var y then found.choose else x
  have onShown : ∀ x ∈ shown, ρ₁ x = .var (ρ x) := by
    intro x member
    have found := toVar x member
    simp only [ρ, dif_pos found]
    exact found.choose_spec
  refine ⟨ρ, fun x memberX x' memberX' same => ?_, fun v outside => ?_, fun slot => ?_⟩
  · have atX := roundTrip x memberX
    have atX' := roundTrip x' memberX'
    rw [onShown x memberX, Subst.applyTerm_var] at atX
    rw [onShown x' memberX', Subst.applyTerm_var, ← same, atX] at atX'
    exact Term.var.inj atX'
  · rw [forwardVars v outside]
    exact Subst.applyTerm_congr fun x member => onShown x (.inl ⟨v, outside, member⟩)
  · rw [forwardSlots slot]
    exact Subst.applyTerm_congr fun x member => onShown x (.inr ⟨slot, member⟩)

/-- What an activation result shows: the store, and every slot read through it. -/
abbrev observe {k : ℕ} (frame : Fin k → Term σ) (store : Subst σ) :
    Subst σ × (Fin k → Term σ) :=
  (store, fun i => store.applyTerm (frame i))

theorem compiledActivation_eq_some {k : ℕ} {patterns : List (HeadPattern σ (Fin k))}
    {args : List (Term σ)} {θ : Subst σ} {n : ℕ} {result : (Fin k → Term σ) × Subst σ × ℕ}
    (accepted : compiledActivation name patterns args θ n = some result) :
    patterns.length = args.length ∧ ∃ final,
      exec name (emitHead patterns) (initialState args θ n) = some final ∧
      result = ((fun i => (final.slots i).getD (.var (name (final.supply + i)))),
        final.store, final.supply + k) := by
  unfold compiledActivation at accepted
  split at accepted
  · rename_i lengths
    rw [Option.map_eq_some_iff] at accepted
    obtain ⟨final, ran, rfl⟩ := accepted
    exact ⟨lengths, final, ran, rfl⟩
  · cases accepted

/-- Soundness: the compiled activation's store solves the head, with every slot
read through it. -/
theorem compiledActivation_sound (injective : Function.Injective name) {k : ℕ}
    (patterns : List (HeadPattern σ (Fin k))) (args : List (Term σ)) (θ : Subst σ) (n : ℕ)
    (entry : EntryCondition name θ n args) {result : (Fin k → Term σ) × Subst σ × ℕ}
    (accepted : compiledActivation name patterns args θ n = some result) :
    HeadSolution θ patterns args result.2.1 (observe result.1 result.2.1).2 := by
  obtain ⟨lengths, final, ran, rfl⟩ := compiledActivation_eq_some name accepted
  obtain ⟨realizes, preserves⟩ := emitHead_spec name injective patterns args θ n lengths entry
  obtain ⟨wfFinal, _, _, _⟩ := preserves final ran
  have compatible : Compatible final final.store
      (fun i => final.store.applyTerm ((final.slots i).getD (.var (name (final.supply + i))))) := by
    refine ⟨wfFinal.idempotent, fun slot value bound => ?_⟩
    simp [bound]
  exact realizes.sound final ran _ _ compatible |>.imp And.left id

/-- Most generality: every solution of the head is an instance of the compiled
activation's result, on the variables outside the supply and on every slot. -/
theorem compiledActivation_mostGeneral (injective : Function.Injective name) {k : ℕ}
    (patterns : List (HeadPattern σ (Fin k))) (args : List (Term σ)) (θ : Subst σ) (n : ℕ)
    (entry : EntryCondition name θ n args) {result : (Fin k → Term σ) × Subst σ × ℕ}
    (accepted : compiledActivation name patterns args θ n = some result)
    {δ : Subst σ} {frame : Fin k → Term σ} (solution : HeadSolution θ patterns args δ frame) :
    InstanceOffSupply name n (observe result.1 result.2.1) (δ, frame) := by
  obtain ⟨lengths, final, ran, rfl⟩ := compiledActivation_eq_some name accepted
  obtain ⟨realizes, preserves⟩ := emitHead_spec name injective patterns args θ n lengths entry
  obtain ⟨wfFinal, grew, _, _⟩ := preserves final ran
  obtain ⟨final', ran', δ', agree, compatible⟩ :=
    realizes.complete δ frame ⟨solution.1, fun _ _ bound => by cases bound⟩ solution.2
  rw [ran] at ran'
  cases Option.some.inj ran'
  obtain ⟨ρ, onFresh, agreeρ⟩ :=
    exists_extension name injective δ' final.supply k frame
  have absorbs : ρ.Absorbs final.store :=
    absorbs_of_agreeOffSupply name wfFinal.store compatible.1 agreeρ
  refine ⟨ρ, fun v outside => ?_, fun i => ?_⟩
  · have outsideFinal : ¬ InSupply name final.supply v :=
      fun inSupply => outside (inSupply.mono name grew)
    change δ v = ρ.applyTerm (final.store v)
    rw [absorbs v, agree v outside, agreeρ v outsideFinal]
  · change frame i = ρ.applyTerm (final.store.applyTerm
      ((final.slots i).getD (.var (name (final.supply + i)))))
    rw [absorbs.applyTerm]
    cases bound : final.slots i with
    | none =>
        simp only [Option.getD_none, Subst.applyTerm_var]
        exact (onFresh i).symm
    | some value =>
        simp only [Option.getD_some]
        rw [compatible.2 i value bound]
        exact agreeρ.applyTerm name (wfFinal.slots i value bound)

/-- Completeness: whenever the head has a solution, the compiled activation
succeeds. -/
theorem compiledActivation_complete (injective : Function.Injective name) {k : ℕ}
    (patterns : List (HeadPattern σ (Fin k))) (args : List (Term σ)) (θ : Subst σ) (n : ℕ)
    (entry : EntryCondition name θ n args)
    (solvable : ∃ δ frame, HeadSolution θ patterns args δ frame) :
    ∃ result, compiledActivation name patterns args θ n = some result := by
  obtain ⟨δ, frame, solution⟩ := solvable
  have lengths := solution.2.length_eq
  obtain ⟨realizes, _⟩ := emitHead_spec name injective patterns args θ n lengths entry
  obtain ⟨final, ran, _⟩ :=
    realizes.complete δ frame ⟨solution.1, fun _ _ bound => by cases bound⟩ solution.2
  exact ⟨((fun i => (final.slots i).getD (.var (name (final.supply + i)))), final.store,
    final.supply + k), by simp [compiledActivation, lengths, ran]⟩

/-- The compiled activation leaves an idempotent store and a frame avoiding the
advanced supply, so the next activation's entry condition holds again. -/
theorem compiledActivation_wellFormed (injective : Function.Injective name) {k : ℕ}
    (patterns : List (HeadPattern σ (Fin k))) (args : List (Term σ)) (θ : Subst σ) (n : ℕ)
    (entry : EntryCondition name θ n args) {result : (Fin k → Term σ) × Subst σ × ℕ}
    (accepted : compiledActivation name patterns args θ n = some result) :
    result.2.1.Absorbs result.2.1 ∧ StoreAvoidsSupply name result.2.2 result.2.1 ∧
      (∀ i, AvoidsSupply name result.2.2 (result.1 i)) ∧ n ≤ result.2.2 := by
  obtain ⟨lengths, final, ran, rfl⟩ := compiledActivation_eq_some name accepted
  obtain ⟨_, preserves⟩ := emitHead_spec name injective patterns args θ n lengths entry
  obtain ⟨wfFinal, grew, _, _⟩ := preserves final ran
  refine ⟨wfFinal.idempotent, wfFinal.store.mono name (Nat.le_add_right _ _), fun i => ?_,
    grew.trans (Nat.le_add_right _ _)⟩
  cases bound : final.slots i with
  | none =>
      intro x member
      simp only [bound, Option.getD_none, Term.mem_freeVars_var] at member
      subst member
      exact name_not_inSupply name injective (by simp)
  | some value =>
      simp only [bound, Option.getD_some]
      exact (wfFinal.slots i value bound).mono name (Nat.le_add_right _ _)

end Activation

/-! ## The defunctionalized machine's activation step -/

/-- Head patterns as the template language of the defunctionalized machine:
templates over `k` slots are head patterns over `Fin k`. -/
abbrev headTemplates (σ : LPSignature.{0, 0, r, 0}) :
    DefunctionalizedEquationBodies.TemplateLanguage (Term σ) where
  Tmpl k := HeadPattern σ (Fin k)
  inst t frame := instantiate frame t
  support t := t.freeVars
  inst_congr _ _ _ agree := instantiate_congr agree

section DefunctionalizedActivation

open DefunctionalizedEquationBodies

variable {σ : LPSignature.{0, 0, r, 0}}
variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
variable (name : ℕ → σ.vars)
variable {Op : Type} (prim : Op → List (Term σ) → Subst σ × ℕ → Option (Term σ))
  (test : Op → List (Term σ) → Subst σ × ℕ → Option Bool)

/-- The store algebra of idempotent substitutions with a counter supply.
Unification reads both sides through the store and composes the total
Martelli--Montanari unifier after it; allocating `k` slots hands out
`name n, ..., name (n + k - 1)`. -/
def substitutionStore : StoreAlgebra (Term σ) (Subst σ × ℕ) Op where
  unify p a store := (unifyTotal [(store.1.applyTerm p, store.1.applyTerm a)]).map
    fun unifier => (unifier ∘ₛ store.1, store.2)
  fresh store k := (freshVariables name store.2 k, (store.1, store.2 + k))
  prim := prim
  test := test

/-- The defunctionalized machine's activation step for one head
(`DefunctionalizedEquationBodies.activate`): allocate the frame, then unify the
instantiated head with the arguments.  The result is the frame, the store and
the supply. -/
def sourceActivation {k : ℕ} (patterns : List (HeadPattern σ (Fin k)))
    (args : List (Term σ)) (θ : Subst σ) (n : ℕ) :
    Option ((Fin k → Term σ) × Subst σ × ℕ) :=
  let fresh := (substitutionStore name prim test).fresh (θ, n) k
  (unifyAll (substitutionStore name prim test)
    (instArgs (headTemplates σ) patterns fresh.1) args fresh.2).map fun store => (fresh.1, store)

/-- `unifyAll` over the substitution store is sound: it keeps the supply,
extends the entry store, and unifies every pair. -/
theorem unifyAll_sound :
    ∀ (patterns args : List (Term σ)) (θ : Subst σ) (n : ℕ) (result : Subst σ × ℕ),
      unifyAll (substitutionStore name prim test) patterns args (θ, n) = some result →
      result.2 = n ∧ (∃ later : Subst σ, result.1 = later ∘ₛ θ) ∧
        List.Forall₂ (fun p a => result.1.applyTerm p = result.1.applyTerm a) patterns args
  | [], [], θ, n, result, accepted => by
      simp only [unifyAll, Option.some.injEq] at accepted
      subst accepted
      exact ⟨rfl, ⟨Subst.id σ, (Subst.comp_id_left θ).symm⟩, .nil⟩
  | p :: ps, a :: as, θ, n, result, accepted => by
      simp only [unifyAll, substitutionStore, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at accepted
      obtain ⟨_, ⟨unifier, unified, rfl⟩, rest⟩ := accepted
      obtain ⟨supplyEq, ⟨later, storeEq⟩, pairs⟩ :=
        unifyAll_sound ps as (unifier ∘ₛ θ) n result rest
      refine ⟨supplyEq, ⟨later ∘ₛ unifier, by rw [storeEq, Subst.comp_assoc]⟩, .cons ?_ pairs⟩
      have solved := unifyTotal_sound _ unifier unified (θ.applyTerm p, θ.applyTerm a) (by simp)
      rw [storeEq, Subst.applyTerm_comp, Subst.applyTerm_comp, Subst.applyTerm_comp,
        Subst.applyTerm_comp]
      exact congrArg later.applyTerm solved
  | [], _ :: _, _, _, _, accepted => by simp [unifyAll] at accepted
  | _ :: _, [], _, _, _, accepted => by simp [unifyAll] at accepted

/-- `unifyAll` over the substitution store is most general. -/
theorem unifyAll_mgu :
    ∀ (patterns args : List (Term σ)) (θ : Subst σ) (n : ℕ) (result : Subst σ × ℕ),
      unifyAll (substitutionStore name prim test) patterns args (θ, n) = some result →
      ∀ δ : Subst σ, List.Forall₂
          (fun p a => δ.applyTerm (θ.applyTerm p) = δ.applyTerm (θ.applyTerm a)) patterns args →
        ∃ ρ : Subst σ, ∀ v, δ.applyTerm (θ v) = ρ.applyTerm (result.1 v)
  | [], [], θ, n, result, accepted, δ, _ => by
      simp only [unifyAll, Option.some.injEq] at accepted
      subst accepted
      exact ⟨δ, fun _ => rfl⟩
  | p :: ps, a :: as, θ, n, result, accepted, δ, unifies => by
      simp only [unifyAll, substitutionStore, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at accepted
      obtain ⟨_, ⟨unifier, unified, rfl⟩, rest⟩ := accepted
      obtain ⟨head, tail⟩ := List.forall₂_cons.mp unifies
      obtain ⟨ρ₁, factor⟩ := unifyTotal_mgu _ unifier unified δ (by
        intro equation member
        simp only [List.mem_singleton] at member
        subst member
        exact head)
      have split : δ = ρ₁ ∘ₛ unifier := funext factor
      obtain ⟨ρ, final⟩ := unifyAll_mgu ps as (unifier ∘ₛ θ) n result rest ρ₁ (by
        refine tail.imp fun p' a' holds => ?_
        rw [Subst.applyTerm_comp, Subst.applyTerm_comp, ← Subst.applyTerm_comp ρ₁,
          ← Subst.applyTerm_comp ρ₁, ← split]
        exact holds)
      refine ⟨ρ, fun v => ?_⟩
      rw [← final v, split, Subst.applyTerm_comp]
      rfl
  | [], _ :: _, _, _, _, accepted, _, _ => by simp [unifyAll] at accepted
  | _ :: _, [], _, _, _, accepted, _, _ => by simp [unifyAll] at accepted

/-- `unifyAll` over the substitution store succeeds on every unifiable list. -/
theorem unifyAll_complete :
    ∀ (patterns args : List (Term σ)) (θ : Subst σ) (n : ℕ) (δ : Subst σ),
      List.Forall₂
          (fun p a => δ.applyTerm (θ.applyTerm p) = δ.applyTerm (θ.applyTerm a)) patterns args →
        ∃ result, unifyAll (substitutionStore name prim test) patterns args (θ, n) = some result
  | [], [], θ, n, _, _ => ⟨(θ, n), rfl⟩
  | p :: ps, a :: as, θ, n, δ, unifies => by
      obtain ⟨head, tail⟩ := List.forall₂_cons.mp unifies
      have unifiesHead : Unifies δ [(θ.applyTerm p, θ.applyTerm a)] := by
        intro equation member
        simp only [List.mem_singleton] at member
        subst member
        exact head
      obtain ⟨unifier, unified⟩ := unifyTotal_complete ⟨δ, unifiesHead⟩
      obtain ⟨ρ₁, factor⟩ := unifyTotal_mgu _ unifier unified δ unifiesHead
      have split : δ = ρ₁ ∘ₛ unifier := funext factor
      obtain ⟨result, accepted⟩ := unifyAll_complete ps as (unifier ∘ₛ θ) n ρ₁ (by
        refine tail.imp fun p' a' holds => ?_
        rw [Subst.applyTerm_comp, Subst.applyTerm_comp, ← Subst.applyTerm_comp ρ₁,
          ← Subst.applyTerm_comp ρ₁, ← split]
        exact holds)
      refine ⟨result, ?_⟩
      simp only [unifyAll, substitutionStore, unified, Option.map_some, Option.bind_some]
      exact accepted
  | [], _ :: _, _, _, _, unifies => by cases unifies
  | _ :: _, [], _, _, _, unifies => by cases unifies

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
private theorem forall₂_imp_of_mem {α β : Type*} {R S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, (∀ a b, b ∈ l₂ → R a b → S a b) →
      List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂
  | _, _, _, .nil => .nil
  | _, _, imp, .cons head tail =>
      .cons (imp _ _ List.mem_cons_self head)
        (forall₂_imp_of_mem (fun a b member => imp a b (List.mem_cons_of_mem _ member)) tail)

theorem sourceActivation_eq_some {k : ℕ} {patterns : List (HeadPattern σ (Fin k))}
    {args : List (Term σ)} {θ : Subst σ} {n : ℕ} {result : (Fin k → Term σ) × Subst σ × ℕ}
    (accepted : sourceActivation name prim test patterns args θ n = some result) :
    result.1 = freshVariables name n k ∧
      unifyAll (substitutionStore name prim test)
        (patterns.map (instantiate (freshVariables name n k))) args (θ, n + k) =
        some result.2 := by
  simp only [sourceActivation, Option.map_eq_some_iff] at accepted
  obtain ⟨store, unified, rfl⟩ := accepted
  exact ⟨rfl, unified⟩

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- A solution of the head gives a unifier of the instantiated head and the
arguments, once the fresh frame variables take the solution's slot values. -/
theorem unifies_of_headSolution (injective : Function.Injective name) {k : ℕ}
    {patterns : List (HeadPattern σ (Fin k))} {args : List (Term σ)} {θ : Subst σ} {n : ℕ}
    (entry : EntryCondition name θ n args) {δ : Subst σ} {frame : Fin k → Term σ}
    (solution : HeadSolution θ patterns args δ frame) :
    ∃ δ' : Subst σ, (∀ i : Fin k, δ' (name (n + i)) = frame i) ∧
      AgreeOffSupply name n δ δ' ∧
      List.Forall₂
        (fun p a => δ'.applyTerm (θ.applyTerm p) = δ'.applyTerm (θ.applyTerm a))
        (patterns.map (instantiate (freshVariables name n k))) args := by
  obtain ⟨δ', onFresh, agree⟩ := exists_extension name injective δ n k frame
  refine ⟨δ', onFresh, agree, List.forall₂_map_left_iff.mpr
    (forall₂_imp_of_mem (fun p a member holds => ?_) solution.2)⟩
  have freshFixed : (fun i => θ.applyTerm (freshVariables name n k i)) =
      freshVariables name n k :=
    funext fun i => (entry.store _).1 (name_inSupply name n i)
  rw [applyTerm_instantiate, freshFixed, applyTerm_instantiate]
  have freshValues : (fun i => δ'.applyTerm (freshVariables name n k i)) = frame :=
    funext onFresh
  rw [freshValues, holds, ← solution.1.applyTerm a]
  exact agree.applyTerm name (AvoidsSupply.applyTerm name entry.store (entry.args a member))

/-- Soundness of the source activation. -/
theorem sourceActivation_sound {k : ℕ} (patterns : List (HeadPattern σ (Fin k)))
    (args : List (Term σ)) (θ : Subst σ) (n : ℕ) (entry : EntryCondition name θ n args)
    {result : (Fin k → Term σ) × Subst σ × ℕ}
    (accepted : sourceActivation name prim test patterns args θ n = some result) :
    HeadSolution θ patterns args result.2.1 (observe result.1 result.2.1).2 ∧
      result.2.2 = n + k := by
  obtain ⟨frameEq, unified⟩ := sourceActivation_eq_some name prim test accepted
  obtain ⟨supplyEq, ⟨later, storeEq⟩, pairs⟩ :=
    unifyAll_sound name prim test _ _ θ (n + k) result.2 unified
  refine ⟨⟨?_, ?_⟩, supplyEq⟩
  · rw [storeEq]
    exact Subst.comp_absorbs entry.idempotent
  · rw [frameEq]
    refine (List.forall₂_map_left_iff.mp pairs).imp fun p a holds => ?_
    rw [← applyTerm_instantiate]
    exact holds

/-- Most generality of the source activation. -/
theorem sourceActivation_mostGeneral (injective : Function.Injective name) {k : ℕ}
    (patterns : List (HeadPattern σ (Fin k))) (args : List (Term σ)) (θ : Subst σ) (n : ℕ)
    (entry : EntryCondition name θ n args) {result : (Fin k → Term σ) × Subst σ × ℕ}
    (accepted : sourceActivation name prim test patterns args θ n = some result)
    {δ : Subst σ} {frame : Fin k → Term σ} (solution : HeadSolution θ patterns args δ frame) :
    InstanceOffSupply name n (observe result.1 result.2.1) (δ, frame) := by
  obtain ⟨frameEq, unified⟩ := sourceActivation_eq_some name prim test accepted
  obtain ⟨δ', onFresh, agree, unifies⟩ := unifies_of_headSolution name injective entry solution
  obtain ⟨ρ, factor⟩ := unifyAll_mgu name prim test _ _ θ (n + k) result.2 unified δ' unifies
  refine ⟨ρ, fun v outside => ?_, fun i => ?_⟩
  · change δ v = ρ.applyTerm (result.2.1 v)
    rw [← factor v, ← solution.1 v]
    exact agree.applyTerm name ((entry.store v).2 outside)
  · change frame i = ρ.applyTerm (result.2.1.applyTerm (result.1 i))
    rw [frameEq, freshVariables, Subst.applyTerm_var, ← factor, ← onFresh i,
      (entry.store _).1 (name_inSupply name n i)]
    rfl

/-- Completeness of the source activation. -/
theorem sourceActivation_complete (injective : Function.Injective name) {k : ℕ}
    (patterns : List (HeadPattern σ (Fin k))) (args : List (Term σ)) (θ : Subst σ) (n : ℕ)
    (entry : EntryCondition name θ n args)
    (solvable : ∃ δ frame, HeadSolution θ patterns args δ frame) :
    ∃ result, sourceActivation name prim test patterns args θ n = some result := by
  obtain ⟨δ, frame, solution⟩ := solvable
  obtain ⟨δ', _, _, unifies⟩ := unifies_of_headSolution name injective entry solution
  obtain ⟨store, unified⟩ := unifyAll_complete name prim test _ _ θ (n + k) δ' unifies
  refine ⟨(freshVariables name n k, store), ?_⟩
  change (unifyAll (substitutionStore name prim test)
    (patterns.map (instantiate (freshVariables name n k))) args (θ, n + k)).map
      (fun store => (freshVariables name n k, store)) = _
  rw [unified]
  rfl

/-- **Exactness at the activation boundary.**  For every head, argument tuple
and entry store, the compiled head succeeds exactly when the defunctionalized
machine's activation step does, and on success each result is an instance of
the other on every variable outside the fresh supply and on every slot: the two
agree up to the names of fresh variables. -/
theorem activation_exact (injective : Function.Injective name) {k : ℕ}
    (patterns : List (HeadPattern σ (Fin k))) (args : List (Term σ)) (θ : Subst σ) (n : ℕ)
    (entry : EntryCondition name θ n args) :
    (compiledActivation name patterns args θ n).isSome =
        (sourceActivation name prim test patterns args θ n).isSome ∧
      ∀ compiled source, compiledActivation name patterns args θ n = some compiled →
        sourceActivation name prim test patterns args θ n = some source →
        InstanceOffSupply name n (observe compiled.1 compiled.2.1)
            (observe source.1 source.2.1) ∧
          InstanceOffSupply name n (observe source.1 source.2.1)
            (observe compiled.1 compiled.2.1) := by
  refine ⟨?_, fun compiled source compiledAccepted sourceAccepted => ⟨?_, ?_⟩⟩
  · cases compiledResult : compiledActivation name patterns args θ n with
    | none =>
        cases sourceResult : sourceActivation name prim test patterns args θ n with
        | none => rfl
        | some source =>
            obtain ⟨compiled, accepted⟩ := compiledActivation_complete name injective
              patterns args θ n entry ⟨_, _, (sourceActivation_sound name prim test patterns
                args θ n entry sourceResult).1⟩
            rw [compiledResult] at accepted
            cases accepted
    | some compiled =>
        obtain ⟨source, accepted⟩ := sourceActivation_complete name prim test injective
          patterns args θ n entry ⟨_, _, compiledActivation_sound name injective patterns
            args θ n entry compiledResult⟩
        rw [accepted]
        rfl
  · exact compiledActivation_mostGeneral name injective patterns args θ n entry
      compiledAccepted (sourceActivation_sound name prim test patterns args θ n entry
        sourceAccepted).1
  · exact sourceActivation_mostGeneral name prim test injective patterns args θ n entry
      sourceAccepted (compiledActivation_sound name injective patterns args θ n entry
        compiledAccepted)

/-- **Exactness up to renaming.**  Whenever both the compiled head and the
defunctionalized machine's activation step succeed, the compiled result is the
source result with its variables renamed, on every variable outside the fresh
supply and on every slot. -/
theorem activation_variant (injective : Function.Injective name) {k : ℕ}
    (patterns : List (HeadPattern σ (Fin k))) (args : List (Term σ)) (θ : Subst σ) (n : ℕ)
    (entry : EntryCondition name θ n args) {compiled source : (Fin k → Term σ) × Subst σ × ℕ}
    (compiledAccepted : compiledActivation name patterns args θ n = some compiled)
    (sourceAccepted : sourceActivation name prim test patterns args θ n = some source) :
    VariantOffSupply name n (observe source.1 source.2.1) (observe compiled.1 compiled.2.1) :=
  let related := (activation_exact name prim test injective patterns args θ n entry).2
    compiled source compiledAccepted sourceAccepted
  variantOffSupply_of_instances name related.2 related.1

/-! ### Programs -/

variable {Rel : Type} [DecidableEq Rel]

/-- The activation step with compiled heads: every equation of the called
relation, tried in authored order, activated by its compiled head. -/
def compiledActivate (P : EqProgram (headTemplates σ) Rel Op) :
    Call (Term σ) (Subst σ × ℕ) Rel → List (Activation (headTemplates σ) Rel Op (Subst σ × ℕ))
  | (rel, args, store) =>
      (P.equations rel).filterMap fun e =>
        (compiledActivation name e.params args store.1 store.2).map fun result =>
          ⟨e.slots, result.1, (result.2.1, result.2.2), e.rhs⟩

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Rel] in
/-- Two activations of the same equation body whose results are instances of
each other outside the supply at `n`. -/
def SameActivation (n : ℕ) (compiled source : Activation (headTemplates σ) Rel Op (Subst σ × ℕ)) :
    Prop :=
  compiled.slots = source.slots ∧
    ∃ (slots : ℕ) (code : Code (headTemplates σ) Rel Op slots)
      (compiledFrame sourceFrame : Fin slots → Term σ) (compiledStore sourceStore : Subst σ × ℕ),
      compiled = ⟨slots, compiledFrame, compiledStore, code⟩ ∧
      source = ⟨slots, sourceFrame, sourceStore, code⟩ ∧
      InstanceOffSupply name n (observe compiledFrame compiledStore.1)
          (observe sourceFrame sourceStore.1) ∧
        InstanceOffSupply name n (observe sourceFrame sourceStore.1)
          (observe compiledFrame compiledStore.1)

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Rel] in
private theorem forall₂_filterMap {α β γ : Type*} {R : β → γ → Prop}
    (f : α → Option β) (g : α → Option γ) :
    ∀ (l : List α), (∀ x ∈ l, (f x).isSome = (g x).isSome ∧
        ∀ b c, f x = some b → g x = some c → R b c) →
      List.Forall₂ R (l.filterMap f) (l.filterMap g)
  | [], _ => .nil
  | x :: rest, each => by
      obtain ⟨⟨same, related⟩, eachRest⟩ := List.forall_mem_cons.mp each
      have tail := forall₂_filterMap f g rest eachRest
      cases fx : f x with
      | none =>
          cases gx : g x with
          | none => simpa [List.filterMap_cons, fx, gx] using tail
          | some c => rw [fx, gx] at same; cases same
      | some b =>
          cases gx : g x with
          | none => rw [fx, gx] at same; cases same
          | some c =>
              simp only [List.filterMap_cons, fx, gx]
              exact .cons (related b c fx gx) tail

/-- **Exactness of the activation step.**  With compiled heads, the machine
activates the same equations of the called relation, in the same authored
order, as `DefunctionalizedEquationBodies.activate` over the substitution
store; each pair of activations shares the equation's body and agrees up to the
names of fresh variables. -/
theorem compiledActivate_exact (injective : Function.Injective name)
    (P : EqProgram (headTemplates σ) Rel Op) (rel : Rel) (args : List (Term σ))
    (θ : Subst σ) (n : ℕ) (entry : EntryCondition name θ n args) :
    List.Forall₂ (SameActivation name n) (compiledActivate name P (rel, args, (θ, n)))
      (activate (headTemplates σ) (substitutionStore name prim test) P (rel, args, (θ, n))) := by
  have source : activate (headTemplates σ) (substitutionStore name prim test) P
      (rel, args, (θ, n)) = (P.equations rel).filterMap fun e =>
        (sourceActivation name prim test e.params args θ n).map fun result =>
          ⟨e.slots, result.1, (result.2.1, result.2.2), e.rhs⟩ := by
    simp only [activate, sourceActivation, Option.map_map]
    rfl
  rw [source]
  refine forall₂_filterMap _ _ _ fun e _ => ⟨?_, fun compiled source compiledAccepted
    sourceAccepted => ?_⟩
  · simpa using (activation_exact name prim test injective e.params args θ n entry).1
  · rw [Option.map_eq_some_iff] at compiledAccepted sourceAccepted
    obtain ⟨compiledResult, compiledRan, rfl⟩ := compiledAccepted
    obtain ⟨sourceResult, sourceRan, rfl⟩ := sourceAccepted
    obtain ⟨forward, backward⟩ :=
      (activation_exact name prim test injective e.params args θ n entry).2
        compiledResult sourceResult compiledRan sourceRan
    exact ⟨rfl, e.slots, e.rhs, compiledResult.1, sourceResult.1,
      (compiledResult.2.1, compiledResult.2.2), (sourceResult.2.1, sourceResult.2.2),
      rfl, rfl, forward, backward⟩

end DefunctionalizedActivation

end Mettapedia.GSLT.LanguageDef.CompiledTwoSidedHeadProgram
