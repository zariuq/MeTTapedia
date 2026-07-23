/-
# The state-free fragment

The evaluator conformance seal splits cleanly into two deliverables, and this
module supplies the formal characterization that makes the split statable:

* **State-free seal** — closed evaluator configurations whose reachable work
  never reaches a world-mutating control instruction.  On this fragment the
  observable world is invariant, so the sequencing question ("alternatives
  share one final state") does not arise and no state chronology is required.
* **State-extension seal** — the remaining instructions, whose semantics is a
  conservative extension of the published specification and needs the
  abstract space algebra plus an ordered chronology.

`StateOpFree` below is the syntactic atom component of that boundary, read off
the runtime's nine direct `St.mapWorld` controls.  It is deliberately not the
whole closure condition: live bindings, rule right-hand sides, space reads,
and grounded results can introduce new work atoms.  The evaluator theorem
therefore combines this local predicate with corresponding environment and
configuration closure predicates rather than assuming source syntax alone is
preserved.

The predicate is stated on atoms only — no interpreter state, no `World` —
so it can index specification-side judgments without importing the runtime
carrier.
-/
import Mettapedia.Languages.MeTTa.HE.StateComponentAlgebra

namespace Mettapedia.Languages.MeTTa.HE.StateFreeFragment

open Metta

/-- The nine control instructions whose evaluator branches mutate the world.

Census taken from the runtime: every `St.mapWorld` site in the evaluator is
guarded by a head symbol in this list.  `get-state` and `get-atoms` are
deliberately ABSENT — they read the world without mutating it, so they remain
inside the state-free fragment. -/
def worldMutatingHeads : List String :=
  ["new-state", "change-state!", "new-space", "new-mork-space", "fork-space",
    "add-atom", "remove-atom", "bind!", "import!"]

/-- An atom whose head is one of the world-mutating instructions. -/
def IsWorldMutatingCall (a : Atom) : Prop :=
  ∃ head rest, a = .expr (.sym head :: rest) ∧ head ∈ worldMutatingHeads

mutual

/-- A grounded snapshot retained inside a binding payload cannot conceal a
world-mutating instruction. -/
def StoredGroundStateOpFree : StoredGround → Prop
  | .external typeName _ => typeName ∉ worldMutatingHeads
  | .bindings bindings => StoredBindingsStateOpFree bindings
  | _ => True

/-- State-operation freedom for an atom stored inside an opaque binding
payload.  This mirrors `StateOpFree` on the snapshot carrier. -/
def StoredAtomStateOpFree : StoredAtom → Prop
  | .sym name => name ∉ worldMutatingHeads
  | .var _ => True
  | .gnd ground => StoredGroundStateOpFree ground
  | .expr atoms =>
      (∀ head rest, StoredAtom.expr atoms = .expr (.sym head :: rest) →
        head ∉ worldMutatingHeads) ∧ StoredAtomsStateOpFree atoms

/-- State-operation freedom for one stored binding relation. -/
def StoredBindingStateOpFree : StoredBinding → Prop
  | .val _ value => StoredAtomStateOpFree value
  | .eq _ _ => True

/-- List companion for stored binding relations. -/
def StoredBindingsStateOpFree : List StoredBinding → Prop
  | [] => True
  | binding :: bindings =>
      StoredBindingStateOpFree binding ∧
        StoredBindingsStateOpFree bindings

/-- List companion for stored atoms. -/
def StoredAtomsStateOpFree : List StoredAtom → Prop
  | [] => True
  | atom :: atoms => StoredAtomStateOpFree atom ∧ StoredAtomsStateOpFree atoms

end

mutual

/-- The atom cannot expose a world-mutating instruction, either as syntax or
through the type tag that `getTypes` promotes from an external grounding or a
binding value restored by `superpose-bind`. -/
def StateOpFree : Atom → Prop
  | .sym name => name ∉ worldMutatingHeads
  | .var _ => True
  | .gnd (.external typeName _) => typeName ∉ worldMutatingHeads
  | .gnd (.bindings bindings) => StoredBindingsStateOpFree bindings
  | .gnd _ => True
  | .expr atoms =>
      (∀ head rest, Atom.expr atoms = .expr (.sym head :: rest) →
        head ∉ worldMutatingHeads) ∧ StateOpFreeList atoms

/-- List companion of `StateOpFree`. -/
def StateOpFreeList : List Atom → Prop
  | [] => True
  | a :: as => StateOpFree a ∧ StateOpFreeList as

end

/-! ## Runtime configuration components

These predicates lift the atom-local boundary to the data that the stack
machine actually carries.  They remain structural and executable-independent:
none states that evaluation preserves the property.  Environment and
grounded-result closure are separate premises of the eventual evaluator
theorem, where those producers are in scope. -/

/-- A binding relation is state-operation-free when its stored value is;
variable equalities carry no atom that could later become work. -/
def BindingRelStateOpFree : BindingRel → Prop
  | .val _ value => StateOpFree value
  | .eq _ _ => True

/-- Every value stored in a live binding set is state-operation-free. -/
def BindingsStateOpFree : Bindings → Prop
  | [] => True
  | binding :: bindings =>
      BindingRelStateOpFree binding ∧ BindingsStateOpFree bindings

/-- One continuation frame carries only a state-operation-free atom. -/
def FrameStateOpFree (frame : Metta.Minimal.Frame) : Prop :=
  StateOpFree frame.atom

/-- Every frame in one continuation stack is state-operation-free. -/
def StackStateOpFree : Metta.Minimal.Stack → Prop
  | [] => True
  | frame :: stack => FrameStateOpFree frame ∧ StackStateOpFree stack

/-- Both the continuation and its live binding values are safe local inputs. -/
def ItemStateOpFree (item : Metta.Minimal.Item) : Prop :=
  StackStateOpFree item.stack ∧ BindingsStateOpFree item.bnd

/-- Work-queue companion of `ItemStateOpFree`. -/
def WorkStateOpFree : List Metta.Minimal.Item → Prop
  | [] => True
  | item :: work => ItemStateOpFree item ∧ WorkStateOpFree work

/-- A completed evaluator result is state-operation-free in both its atom and
its retained binding values. -/
def ResultStateOpFree (result : Atom × Bindings) : Prop :=
  StateOpFree result.1 ∧ BindingsStateOpFree result.2

/-- Every result already accumulated by `interpretFuel` is safe. -/
def DoneStateOpFree (done : List (Atom × Bindings)) : Prop :=
  ∀ result ∈ done, ResultStateOpFree result

/-- Every atom obtainable from a named space is state-operation-free.  This is
stated through lookup rather than the hash-map representation, so later space
implementations can discharge the same interface. -/
def NamedSpacesStateOpFree (world : Metta.Minimal.World) : Prop :=
  ∀ (name : String) (atoms : List Atom),
    world.spaces[name]? = some atoms → StateOpFreeList atoms

/-- Every value obtainable from a mutable state cell is state-operation-free. -/
def StateCellsStateOpFree (world : Metta.Minimal.World) : Prop :=
  ∀ (id : Nat) (value : Atom),
    world.store[id]? = some value → StateOpFree value

/-- Every value obtainable through a `bind!` token is state-operation-free. -/
def TokensStateOpFree (world : Metta.Minimal.World) : Prop :=
  ∀ (name : String) (value : Atom),
    world.tokens[name]? = some value → StateOpFree value

/-- Closure of every atom-bearing component of the runtime world.  The
`imported` field stores only bookkeeping keys and therefore needs no atom
condition. -/
structure WorldStateOpFree (world : Metta.Minimal.World) : Prop where
  namedSpaces : NamedSpacesStateOpFree world
  stateCells : StateCellsStateOpFree world
  tokens : TokensStateOpFree world
  selfExtra : StateOpFreeList world.selfExtra
  selfImports : StateOpFreeList world.selfImports

/-- The static environment exposes no state operation through rule lookup,
visible-space reads, type inference, or documentation lookup.  These are the
four observable producer surfaces used by the evaluator; phrasing the fields
at those public boundaries avoids depending on `HashMap` iteration details. -/
structure MinEnvStateOpFree (env : Metta.Minimal.MinEnv) : Prop where
  atoms : StateOpFreeList env.atoms
  visibleAtoms : StateOpFreeList env.visibleAtoms
  candidates : ∀ query lhs rhs,
    StateOpFree query → (lhs, rhs) ∈ env.candidates query →
      StateOpFree lhs ∧ StateOpFree rhs
  inferredTypes : ∀ atom inferred,
    StateOpFree atom → inferred ∈ Metta.Minimal.getTypes env atom →
      StateOpFree inferred
  documentation : ∀ world atom,
    WorldStateOpFree world → StateOpFree atom →
      StateOpFree (Metta.Minimal.getDocOf env world atom)

/-- Safety of one grounded result.  Successful reductions expose their atoms;
runtime errors expose their message through `errAtom` as a symbol. -/
def GroundedOutcomeStateOpFree : ReduceResult → Prop
  | .ok results => StateOpFreeList results
  | .runtimeError message => message ∉ worldMutatingHeads
  | .incorrectArgument _ => True
  | .noReduce => True

/-- Grounded implementations are an explicit external closure boundary: safe
arguments may produce only outcomes that remain safe when the evaluator turns
them into atoms. -/
def GroundingTableStateOpFree (table : GroundingTable) : Prop :=
  ∀ grounding, grounding ∈ table → ∀ args,
    StateOpFreeList args → GroundedOutcomeStateOpFree (grounding.impl args)

@[simp] theorem bindingsStateOpFree_nil : BindingsStateOpFree [] := trivial

theorem bindingsStateOpFree_cons {binding : BindingRel} {bindings : Bindings} :
    BindingsStateOpFree (binding :: bindings) ↔
      BindingRelStateOpFree binding ∧ BindingsStateOpFree bindings := Iff.rfl

@[simp] theorem stackStateOpFree_nil : StackStateOpFree [] := trivial

theorem stackStateOpFree_cons {frame : Metta.Minimal.Frame}
    {stack : Metta.Minimal.Stack} :
    StackStateOpFree (frame :: stack) ↔
      FrameStateOpFree frame ∧ StackStateOpFree stack := Iff.rfl

@[simp] theorem workStateOpFree_nil : WorkStateOpFree [] := trivial

theorem workStateOpFree_cons {item : Metta.Minimal.Item}
    {work : List Metta.Minimal.Item} :
    WorkStateOpFree (item :: work) ↔
      ItemStateOpFree item ∧ WorkStateOpFree work := Iff.rfl

@[simp] theorem doneStateOpFree_nil : DoneStateOpFree [] := by
  simp [DoneStateOpFree]

theorem doneStateOpFree_cons {result : Atom × Bindings}
    {done : List (Atom × Bindings)} :
    DoneStateOpFree (result :: done) ↔
      ResultStateOpFree result ∧ DoneStateOpFree done := by
  simp [DoneStateOpFree]

/-! ## Closure algebra

The fragment is closed downward under structure, so an induction over the
evaluator inherits the hypothesis at every recursive call without extra
bookkeeping.  These are the lemmas that make the state-free seal's induction
mechanical. -/

@[simp] theorem stateOpFree_sym (s : String) :
    StateOpFree (.sym s) ↔ s ∉ worldMutatingHeads := Iff.rfl

@[simp] theorem stateOpFree_var (v : VarName) : StateOpFree (.var v) := trivial

@[simp] theorem stateOpFree_gnd (ground : Ground) :
    StateOpFree (.gnd ground) ↔
      match ground with
      | .external typeName _ => typeName ∉ worldMutatingHeads
      | .bindings bindings => StoredBindingsStateOpFree bindings
      | _ => True := by
  cases ground <;> rfl

@[simp] theorem stateOpFreeList_nil : StateOpFreeList [] := trivial

theorem stateOpFreeList_cons {a : Atom} {as : List Atom} :
    StateOpFreeList (a :: as) ↔ StateOpFree a ∧ StateOpFreeList as := Iff.rfl

/-- The recursive list predicate agrees with ordinary membership-wise
closure.  This is the adapter used by `map`, `filterMap`, and fold proofs. -/
theorem stateOpFreeList_iff_forall_mem {atoms : List Atom} :
    StateOpFreeList atoms ↔ ∀ atom ∈ atoms, StateOpFree atom := by
  induction atoms with
  | nil => simp
  | cons atom atoms inductionHypothesis =>
      simp only [stateOpFreeList_cons, inductionHypothesis, List.mem_cons]
      constructor
      · rintro ⟨head, tail⟩ candidate (rfl | member)
        · exact head
        · exact tail candidate member
      · intro all
        exact ⟨all atom (by simp), fun candidate member =>
          all candidate (by simp [member])⟩

/-- Every element of a state-free list is state-free. -/
theorem stateOpFree_of_mem :
    ∀ {as : List Atom} {a : Atom}, StateOpFreeList as → a ∈ as → StateOpFree a
  | b :: bs, a, h, hmem => by
    rcases List.mem_cons.mp hmem with rfl | htail
    · exact h.1
    · exact stateOpFree_of_mem h.2 htail

/-- Arguments of a state-free expression are state-free: the fragment is
closed under taking subterms, so recursive evaluation preserves it. -/
theorem stateOpFreeList_of_expr {atoms : List Atom}
    (h : StateOpFree (.expr atoms)) : StateOpFreeList atoms := h.2

/-- A state-free expression's head is not a world-mutating instruction: the
fact each evaluator branch consumes to rule out the mutating cases. -/
theorem head_not_mutating {head : String} {rest : List Atom}
    (h : StateOpFree (.expr (.sym head :: rest))) :
    head ∉ worldMutatingHeads :=
  h.1 head rest rfl

/-- A state-free call is not a world-mutating call. -/
theorem not_isWorldMutatingCall {atoms : List Atom}
    (h : StateOpFree (.expr atoms)) : ¬IsWorldMutatingCall (.expr atoms) := by
  rintro ⟨head, rest, heq, hmem⟩
  exact h.1 head rest heq hmem

/-- Sublists of state-free lists are state-free (tail closure). -/
theorem stateOpFreeList_tail {a : Atom} {as : List Atom}
    (h : StateOpFreeList (a :: as)) : StateOpFreeList as := h.2

/-- Appending state-free lists stays state-free: the evaluator concatenates
work items, and the fragment survives it. -/
theorem stateOpFreeList_append :
    ∀ {as bs : List Atom}, StateOpFreeList as → StateOpFreeList bs →
      StateOpFreeList (as ++ bs)
  | [], bs, _, hbs => hbs
  | a :: as, bs, has, hbs => by
    exact ⟨has.1, stateOpFreeList_append has.2 hbs⟩

/-- Once mutation-head symbols themselves are excluded, expression closure is
exactly child-list closure; the explicit head clause is a convenient runtime
eliminator, not an additional restriction. -/
theorem stateOpFree_expr_iff_list {atoms : List Atom} :
    StateOpFree (.expr atoms) ↔ StateOpFreeList atoms := by
  constructor
  · exact fun safe => safe.2
  · intro safe
    constructor
    · intro head rest equality
      have listEquation : atoms = .sym head :: rest := Atom.expr.inj equality
      subst atoms
      exact (safe.1 : StateOpFree (.sym head))
    · exact safe

/-- Mapping a pointwise state-operation-free transformation over a safe list
preserves the fragment. -/
theorem stateOpFreeList_map {f : Atom → Atom} {atoms : List Atom}
    (safe : StateOpFreeList atoms)
    (closed : ∀ atom ∈ atoms, StateOpFree atom → StateOpFree (f atom)) :
    StateOpFreeList (atoms.map f) := by
  rw [stateOpFreeList_iff_forall_mem] at safe ⊢
  intro result member
  obtain ⟨atom, atomMember, rfl⟩ := List.mem_map.mp member
  exact closed atom atomMember (safe atom atomMember)

/- Renaming variables cannot introduce a state-operation symbol. -/
mutual
  theorem stateOpFree_renameAllVars (rename : VarName → VarName) :
      ∀ {atom : Atom}, StateOpFree atom →
        StateOpFree (Metta.Minimal.renameAllVars rename atom)
    | .sym _, safe => by
        simpa [Metta.Minimal.renameAllVars, StateOpFree] using safe
    | .var _, _ => by
        simp [Metta.Minimal.renameAllVars]
    | .gnd _, safe => by
        simpa [Metta.Minimal.renameAllVars] using safe
    | .expr atoms, safe => by
        simp only [Metta.Minimal.renameAllVars, StateOpFree]
        constructor
        · intro head rest equality
          cases atoms with
          | nil => simp at equality
          | cons first tail =>
              cases first <;>
                simp [Metta.Minimal.renameAllVars] at equality
              case sym name =>
                rw [← equality.1]
                exact safe.1 name tail rfl
        · exact stateOpFreeList_renameAllVars rename safe.2

  theorem stateOpFreeList_renameAllVars (rename : VarName → VarName) :
      ∀ {atoms : List Atom}, StateOpFreeList atoms →
        StateOpFreeList (atoms.map (Metta.Minimal.renameAllVars rename))
    | [], _ => by simp
    | atom :: atoms, safe => by
        simp only [List.map_cons, StateOpFreeList]
        exact ⟨stateOpFree_renameAllVars rename safe.1,
          stateOpFreeList_renameAllVars rename safe.2⟩
end

/-! ## Closure of world-dependent atom preparation -/

/-- Token substitution preserves the fragment when every token value in the
world is safe. -/
theorem stateOpFree_subTokens (world : Metta.Minimal.World)
    (worldSafe : WorldStateOpFree world) :
    ∀ atom, StateOpFree atom →
      StateOpFree (Metta.Minimal.subTokens world atom)
  | .sym symbol, safe => by
      simp only [Metta.Minimal.subTokens]
      cases lookup : world.tokens[symbol]? with
      | none => simpa [lookup] using safe
      | some value =>
          simpa [lookup] using worldSafe.tokens symbol value lookup
  | .var name, safe => by
      simp [Metta.Minimal.subTokens]
  | .gnd value, safe => by
      simpa [Metta.Minimal.subTokens] using safe
  | .expr atoms, safe => by
      rw [Metta.Minimal.subTokens, stateOpFree_expr_iff_list]
      rw [stateOpFreeList_iff_forall_mem]
      intro result resultMember
      obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp resultMember
      exact stateOpFree_subTokens world worldSafe child
        (stateOpFree_of_mem safe.2 childMember)

/-- State-handle dereferencing preserves the fragment when cell contents are
safe. -/
theorem stateOpFree_resolveStates (world : Metta.Minimal.World)
    (worldSafe : WorldStateOpFree world) :
    ∀ atom, StateOpFree atom →
      StateOpFree (Metta.Minimal.resolveStates world atom) := by
  intro atom
  fun_induction Metta.Minimal.resolveStates world atom <;> intro safe
  case case1 id value lookup =>
    exact worldSafe.stateCells id.toNat value lookup
  case case2 id lookup =>
    exact safe
  case case3 atoms notHandle inductionHypothesis =>
    apply stateOpFree_expr_iff_list.mpr
    exact stateOpFreeList_map safe.2 (by
      intro child member childSafe
      exact inductionHypothesis child member childSafe)
  case case4 atom first second =>
    exact safe

/-- State wrapping used by type preparation preserves the fragment. -/
theorem stateOpFree_wrapStates (world : Metta.Minimal.World)
    (worldSafe : WorldStateOpFree world) :
    ∀ atom, StateOpFree atom →
      StateOpFree (Metta.Minimal.wrapStates world atom) := by
  intro atom
  fun_induction Metta.Minimal.wrapStates world atom <;> intro safe
  case case1 id value lookup =>
    apply stateOpFree_expr_iff_list.mpr
    exact ⟨by simp [StateOpFree, worldMutatingHeads],
      ⟨worldSafe.stateCells id.toNat value lookup, trivial⟩⟩
  case case2 id lookup =>
    exact safe
  case case3 atoms notHandle inductionHypothesis =>
    apply stateOpFree_expr_iff_list.mpr
    exact stateOpFreeList_map safe.2 (by
      intro child member childSafe
      exact inductionHypothesis child member childSafe)
  case case4 atom first second =>
    exact safe

/-- The complete type-preparation pipeline is state-operation-free. -/
theorem stateOpFree_typePrep (world : Metta.Minimal.World)
    (worldSafe : WorldStateOpFree world) {atom : Atom}
    (safe : StateOpFree atom) :
    StateOpFree (Metta.Minimal.typePrep world atom) := by
  exact stateOpFree_wrapStates world worldSafe _
    (stateOpFree_subTokens world worldSafe atom safe)

/-! ## Positive and negative witnesses

Both directions are required: the predicate must ADMIT ordinary programs and
must REJECT every censused instruction.  Without the negatives the fragment
could be vacuous or over-wide. -/

/-- Positive: an ordinary application is in the fragment. -/
theorem stateOpFree_ordinary_application :
    StateOpFree (.expr [.sym "f", .sym "a"]) := by
  refine ⟨?_, ?_⟩
  · rintro head rest ⟨rfl, rfl⟩
    decide
  · constructor
    · change "f" ∉ worldMutatingHeads
      decide
    · constructor
      · change "a" ∉ worldMutatingHeads
        decide
      · trivial

/-- Positive: reading state is NOT a mutation, so `get-state` stays in the
fragment.  This is the discrimination that keeps the fragment useful rather
than merely excluding everything state-adjacent. -/
theorem stateOpFree_get_state :
    StateOpFree (.expr [.sym "get-state", .sym "s"]) := by
  refine ⟨?_, ?_⟩
  · rintro head rest ⟨rfl, rfl⟩
    decide
  · constructor
    · change "get-state" ∉ worldMutatingHeads
      decide
    · constructor
      · change "s" ∉ worldMutatingHeads
        decide
      · trivial

/-- Positive: the initial runtime world satisfies every storage closure
component. -/
theorem worldStateOpFree_empty :
    WorldStateOpFree Metta.Minimal.World.empty := by
  constructor
  · intro name atoms lookup
    simp [Metta.Minimal.World.empty] at lookup
  · intro id value lookup
    simp [Metta.Minimal.World.empty] at lookup
  · intro name value lookup
    simp [Metta.Minimal.World.empty] at lookup
  · trivial
  · trivial

/-- Positive: an empty grounding table cannot introduce an unsafe outcome. -/
theorem groundingTableStateOpFree_nil : GroundingTableStateOpFree [] := by
  intro grounding member
  simp at member

/-- Negative: a runtime error message is observable as a symbol, so a table
that can emit a mutation name is outside the state-free profile. -/
theorem not_groundingTableStateOpFree_mutating_error :
    ¬GroundingTableStateOpFree
      [{ name := "unsafe-error", mode := .evalArgs, typeSig := none,
         impl := fun _ => .runtimeError "add-atom" }] := by
  intro safe
  have emitted := safe
    { name := "unsafe-error", mode := .evalArgs, typeSig := none,
      impl := fun _ => .runtimeError "add-atom" }
    (by simp) [] (by simp)
  simp [GroundedOutcomeStateOpFree, worldMutatingHeads] at emitted

/-- Negative: a mutating control symbol is excluded even while it is inert
data.  This conservative clause is required for evaluator closure because
`cons-atom` can promote a symbol value into expression-head position. -/
theorem not_stateOpFree_mutating_symbol :
    ¬StateOpFree (.sym "add-atom") := by
  change ¬("add-atom" ∉ worldMutatingHeads)
  decide

/-- Negative: the `cons-atom` escape hatch cannot manufacture a permitted
mutating call from otherwise inert data, because its head symbol is already
outside the fragment. -/
theorem not_stateOpFree_promoted_mutation_source :
    ¬StateOpFree
      (.expr [.sym "cons-atom", .sym "add-atom",
        .expr [.sym "&self", .sym "A"]]) := by
  intro free
  exact not_stateOpFree_mutating_symbol
    (stateOpFree_of_mem free.2 (by simp))

/-- Positive: an ordinary external type tag remains in the fragment. -/
theorem stateOpFree_external_ordinary_type :
    StateOpFree (.gnd (.external "Tensor" "payload")) := by
  simp [StateOpFree, worldMutatingHeads]

/-- Negative: an external grounding whose type tag would promote to a
mutation symbol is excluded before `getTypes` can expose it. -/
theorem not_stateOpFree_external_mutation_type :
    ¬StateOpFree (.gnd (.external "add-atom" "payload")) := by
  simp [StateOpFree, worldMutatingHeads]

/-- Positive: an opaque collapsed binding payload remains in the fragment
when every atom stored in it is safe. -/
theorem stateOpFree_safe_binding_payload :
    StateOpFree
      (.gnd (.bindings [.val "x" (.expr [.sym "f", .sym "A"])])) := by
  simp [StateOpFree, StoredBindingsStateOpFree, StoredBindingStateOpFree,
    StoredAtomStateOpFree, StoredAtomsStateOpFree, worldMutatingHeads]

/-- Negative: opacity does not hide a mutation that `superpose-bind` can
restore into live bindings. -/
theorem not_stateOpFree_hidden_binding_mutation :
    ¬StateOpFree
      (.gnd (.bindings
        [.val "x" (.expr [.sym "add-atom", .sym "&self", .sym "A"])])) := by
  simp [StateOpFree, StoredBindingsStateOpFree, StoredBindingStateOpFree,
    StoredAtomStateOpFree, StoredAtomsStateOpFree, worldMutatingHeads]

/-- Negative: `add-atom` is excluded. -/
theorem not_stateOpFree_add_atom :
    ¬StateOpFree (.expr [.sym "add-atom", .sym "s", .sym "a"]) := by
  rintro ⟨hhead, -⟩
  exact absurd (hhead "add-atom" [.sym "s", .sym "a"] rfl) (by decide)

/-- Negative: `change-state!` is excluded. -/
theorem not_stateOpFree_change_state :
    ¬StateOpFree (.expr [.sym "change-state!", .sym "s", .sym "v"]) := by
  rintro ⟨hhead, -⟩
  exact absurd (hhead "change-state!" [.sym "s", .sym "v"] rfl) (by decide)

/-- Negative: `bind!` is excluded. -/
theorem not_stateOpFree_bind :
    ¬StateOpFree (.expr [.sym "bind!", .sym "t", .sym "v"]) := by
  rintro ⟨hhead, -⟩
  exact absurd (hhead "bind!" [.sym "t", .sym "v"] rfl) (by decide)

/-- Negative: a mutation nested inside an argument is also excluded — the
fragment is closed downward, so hiding a state op deeper does not smuggle it
in. -/
theorem not_stateOpFree_nested_mutation :
    ¬StateOpFree (.expr [.sym "f", .expr [.sym "add-atom", .sym "s", .sym "a"]]) := by
  rintro ⟨-, hlist⟩
  exact not_stateOpFree_add_atom hlist.2.1

end Mettapedia.Languages.MeTTa.HE.StateFreeFragment
