import Mettapedia.GSLT.LanguageDef.CompiledTwoSidedHeadProgram

/-!
# Code trees over compiled equation heads

The equations of one relation are tried in authored order.  Their compiled heads
(`CompiledTwoSidedHeadProgram`) often begin with the same instructions, for
instance the same test of the first argument's top-level shape.  A code tree
stores that common code once: it is an ordered forest whose edges are head
instructions and whose leaves are heads, so a path from the root to a leaf is
one head's code.  Running the tree on a query runs a shared instruction once,
and its failure skips every head below it (`run_op_of_step_eq_none`).

**Laws.**

* `run_eq_runEach`: running a tree is running the code of each of its heads
  (`paths`) separately, in the tree's order.  This holds for every tree, so any
  construction whose paths are the heads in authored order inherits the results
  below; `run_perm` gives the same up to permutation for a tree whose paths are
  a permutation of the heads.
* `paths_build`: `build` inserts the heads in order, and its paths are exactly
  the heads, in order.
* `size_build`: `build` stores each head's code less the longest prefix it has
  in common with the code of the head before it (`sharedWithPrevious`).  Only
  adjacent heads share code: sharing with an earlier head across a different
  one would put the later head's results before the one in between.
* `exec_renumber`: the heads of a relation have different numbers of slots, so
  the tree numbers slots by `ℕ` (`renumber`); renumbered code, read back through
  the renumbering, is the original code.
* `treeActivate_relationTree`: running a relation's tree once on a call yields
  exactly the list of pairs (authored index, activation) that running each
  head's compiled code separately (`compiledActivation`) yields, for the heads
  that accept the call, in authored order; `treeActivate_indices`: the indices
  strictly increase.  `treeActivate_map_snd` identifies the activations with
  `compiledActivate`, and `treeActivate_exact` relates them pairwise, in order,
  to `DefunctionalizedEquationBodies.activate`: the same equations, the same
  bodies, results equal up to the names of fresh variables.

**Relation to `MatchDecisionCodeTree`.**  That tree selects candidate equations
by sampled positions of an observation before head unification runs; this tree
shares head unification itself, on open queries with repeated head variables.

**Not covered.**  A switch that jumps from a register's top-level symbol
straight to the non-adjacent heads expecting it: it needs ordered lists of heads
per symbol and a merge back into authored order, which this tree does not have.
Costs, and the C realization: the C cursor (`cetta_open_equation_cursor_pending`)
activates the equations of a relation one at a time in authored order, which is
`runEach`; a C code tree has to produce the same ordered list.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CompiledHeadCodeTree

open Mettapedia.Logic.LP
open Mettapedia.GSLT.LanguageDef.CompiledTwoSidedHeadProgram

universe u r v

/-! ## Trees -/

/-- An ordered code tree over compiled heads, as a forest of alternatives.
`op instruction below rest` runs `instruction` and, on success, the
alternatives `below`; the alternatives `rest` then run from the state before
`instruction`.  `leaf payload rest` ends the code of the head `payload`. -/
inductive CodeTree (σ : LPSignature.{u, u, r, u}) (Slot : Type u) (α : Type v) :
    Type (max u v) where
  | nil
  | leaf (payload : α) (rest : CodeTree σ Slot α)
  | op (instruction : HeadOp σ Slot) (below rest : CodeTree σ Slot α)

namespace CodeTree

variable {σ : LPSignature.{u, u, r, u}} {Slot : Type u} {α : Type v}

/-- The heads of a tree with their code, in the tree's order: the paths from
the root to the leaves. -/
def paths : CodeTree σ Slot α → List (α × List (HeadOp σ Slot))
  | .nil => []
  | .leaf payload rest => (payload, []) :: paths rest
  | .op instruction below rest =>
      (paths below).map (fun entry => (entry.1, instruction :: entry.2)) ++ paths rest

/-- The number of instructions stored in a tree. -/
def size : CodeTree σ Slot α → ℕ
  | .nil => 0
  | .leaf _ rest => size rest
  | .op _ below rest => size below + 1 + size rest

section Run

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Slot]
variable (name : ℕ → σ.vars)

/-- Run a tree from one state: the heads whose code succeeds, each with its
final state, in the tree's order.  An instruction shared by several heads runs
once, and its failure skips all of them. -/
def run : CodeTree σ Slot α → HeadState σ Slot → List (α × HeadState σ Slot)
  | .nil, _ => []
  | .leaf payload rest, state => (payload, state) :: run rest state
  | .op instruction below rest, state =>
      (match step name instruction state with
        | none => []
        | some next => run below next) ++ run rest state

/-- Running each head's code separately, in the given order, keeping the heads
that succeed. -/
def runEach (entries : List (α × List (HeadOp σ Slot))) (state : HeadState σ Slot) :
    List (α × HeadState σ Slot) :=
  entries.filterMap fun entry => (exec name entry.2 state).map (entry.1, ·)

theorem runEach_append (first second : List (α × List (HeadOp σ Slot)))
    (state : HeadState σ Slot) :
    runEach name (first ++ second) state = runEach name first state ++ runEach name second state :=
  List.filterMap_append

/-- **A tree runs its heads.**  Running a tree is running the code of each of
its heads separately, in the tree's order. -/
theorem run_eq_runEach (tree : CodeTree σ Slot α) (state : HeadState σ Slot) :
    run name tree state = runEach name (paths tree) state := by
  induction tree generalizing state with
  | nil => rfl
  | leaf payload rest ih =>
      simp [run, paths, runEach, exec, ih]
  | op instruction below rest ihBelow ihRest =>
      rw [run, paths, runEach_append, ihRest]
      congr 1
      simp only [runEach, List.filterMap_map, Function.comp_def, exec]
      cases step name instruction state with
      | none => simp
      | some next => simpa [runEach] using ihBelow next

/-- A failed instruction skips every head below it. -/
theorem run_op_of_step_eq_none {instruction : HeadOp σ Slot} {state : HeadState σ Slot}
    (failed : step name instruction state = none) (below rest : CodeTree σ Slot α) :
    run name (.op instruction below rest) state = run name rest state := by
  simp [run, failed]

/-- A tree whose heads are a permutation of `entries` runs them up to the same
permutation. -/
theorem run_perm {tree : CodeTree σ Slot α} {entries : List (α × List (HeadOp σ Slot))}
    (perm : (paths tree).Perm entries) (state : HeadState σ Slot) :
    (run name tree state).Perm (runEach name entries state) := by
  rw [run_eq_runEach]
  exact perm.filterMap _

end Run

/-! ## Building a tree -/

/-- The tree of one head's code. -/
def chain (payload : α) : List (HeadOp σ Slot) → CodeTree σ Slot α
  | [] => .leaf payload .nil
  | instruction :: program => .op instruction (chain payload program) .nil

theorem paths_chain (payload : α) (program : List (HeadOp σ Slot)) :
    paths (chain payload program) = [(payload, program)] := by
  induction program with
  | nil => rfl
  | cons instruction program ih => simp [chain, paths, ih]

variable [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq Slot]

/-- Add a head after every head of the tree.  Its code shares the longest
common prefix with the code of the tree's last head. -/
def insert (payload : α) : CodeTree σ Slot α → List (HeadOp σ Slot) → CodeTree σ Slot α
  | .nil, program => chain payload program
  | .leaf other rest, program => .leaf other (insert payload rest program)
  | .op instruction below rest, program =>
      match rest, program with
      | .nil, first :: remaining =>
          if first = instruction then .op instruction (insert payload below remaining) .nil
          else .op instruction below (chain payload program)
      | _, _ => .op instruction below (insert payload rest program)

/-- The code tree of a list of heads, inserted in order. -/
def build (entries : List (α × List (HeadOp σ Slot))) : CodeTree σ Slot α :=
  entries.foldl (fun tree entry => insert entry.1 tree entry.2) .nil

theorem paths_insert (payload : α) (tree : CodeTree σ Slot α) (program : List (HeadOp σ Slot)) :
    paths (insert payload tree program) = paths tree ++ [(payload, program)] := by
  induction tree generalizing program with
  | nil => exact paths_chain payload program
  | leaf other rest ih => simp [insert, paths, ih]
  | op instruction below rest ihBelow ihRest =>
      cases rest with
      | nil =>
          cases program with
          | nil => simp [insert, paths, paths_chain]
          | cons first remaining =>
              by_cases same : first = instruction
              · subst same
                simp [insert, paths, ihBelow]
              · simp [insert, paths, paths_chain, same]
      | leaf other rest' =>
          change paths (.op instruction below (insert payload (.leaf other rest') program)) = _
          rw [paths, ihRest]
          simp [paths]
      | op instruction' below' rest' =>
          change paths (.op instruction below
            (insert payload (.op instruction' below' rest') program)) = _
          rw [paths, ihRest]
          simp [paths]

theorem paths_foldl_insert (entries : List (α × List (HeadOp σ Slot))) (tree : CodeTree σ Slot α) :
    paths (entries.foldl (fun tree entry => insert entry.1 tree entry.2) tree) =
      paths tree ++ entries := by
  induction entries generalizing tree with
  | nil => simp
  | cons entry entries ih => simp [ih, paths_insert]

/-- The tree of a list of heads has exactly those heads, in order. -/
theorem paths_build (entries : List (α × List (HeadOp σ Slot))) :
    paths (build entries) = entries := by
  rw [build, paths_foldl_insert]
  rfl

/-! ## Sharing -/

/-- The longest common prefix of two instruction sequences. -/
def sharedPrefix (first second : List (HeadOp σ Slot)) : List (HeadOp σ Slot) :=
  (List.takeWhile₂ (fun a b => decide (a = b)) first second).1

/-- The code of the tree's last head; empty for a tree without heads. -/
def lastCode (tree : CodeTree σ Slot α) : List (HeadOp σ Slot) :=
  ((paths tree).getLast?.map Prod.snd).getD []

/-- The number of instructions each head's code shares with the code of the
head before it; the first head is compared with `previous`. -/
def sharedWithPrevious (previous : List (HeadOp σ Slot)) :
    List (List (HeadOp σ Slot)) → ℕ
  | [] => 0
  | program :: rest => (sharedPrefix previous program).length + sharedWithPrevious program rest

omit [DecidableEq σ.functionSymbols] [DecidableEq σ.constants] [DecidableEq Slot] in
/-- Every instruction of the tree leads to a head. -/
inductive Live : CodeTree σ Slot α → Prop
  | nil : Live .nil
  | leaf (payload : α) {rest : CodeTree σ Slot α} : Live rest → Live (.leaf payload rest)
  | op (instruction : HeadOp σ Slot) {below rest : CodeTree σ Slot α} :
      Live below → Live rest → paths below ≠ [] → Live (.op instruction below rest)

theorem sharedPrefix_cons_cons (a b : HeadOp σ Slot) (first second : List (HeadOp σ Slot)) :
    sharedPrefix (a :: first) (b :: second) =
      if a = b then a :: sharedPrefix first second else [] := by
  unfold sharedPrefix
  rw [List.takeWhile₂]
  by_cases same : a = b <;> simp [same]

theorem sharedPrefix_nil_right (first : List (HeadOp σ Slot)) :
    sharedPrefix first [] = [] := by
  cases first <;> rfl

theorem sharedPrefix_nil_left (second : List (HeadOp σ Slot)) :
    sharedPrefix [] second = [] := rfl

omit [DecidableEq σ.functionSymbols] [DecidableEq σ.constants] [DecidableEq Slot] in
theorem lastCode_leaf (payload : α) (rest : CodeTree σ Slot α) :
    lastCode (.leaf payload rest) = lastCode rest := by
  unfold lastCode
  rw [paths, List.getLast?_cons]
  cases (paths rest).getLast? <;> rfl

omit [DecidableEq σ.functionSymbols] [DecidableEq σ.constants] [DecidableEq Slot] in
theorem lastCode_op_nil (instruction : HeadOp σ Slot) {below : CodeTree σ Slot α}
    (reaches : paths below ≠ []) :
    lastCode (.op instruction below .nil) = instruction :: lastCode below := by
  unfold lastCode
  rw [paths, paths, List.append_nil, List.getLast?_map]
  cases last : (paths below).getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp last) reaches
  | some entry => rfl

omit [DecidableEq σ.functionSymbols] [DecidableEq σ.constants] [DecidableEq Slot] in
theorem lastCode_op (instruction : HeadOp σ Slot) (below : CodeTree σ Slot α)
    {rest : CodeTree σ Slot α} (reaches : paths rest ≠ []) :
    lastCode (.op instruction below rest) = lastCode rest := by
  unfold lastCode
  rw [paths, List.getLast?_append_of_ne_nil _ reaches]

theorem lastCode_insert (payload : α) (tree : CodeTree σ Slot α)
    (program : List (HeadOp σ Slot)) : lastCode (insert payload tree program) = program := by
  simp [lastCode, paths_insert]

omit [DecidableEq σ.functionSymbols] [DecidableEq σ.constants] [DecidableEq Slot] in
theorem size_chain (payload : α) (program : List (HeadOp σ Slot)) :
    size (chain payload program) = program.length := by
  induction program with
  | nil => rfl
  | cons instruction program ih => simp [chain, size, ih]

omit [DecidableEq σ.functionSymbols] [DecidableEq σ.constants] [DecidableEq Slot] in
theorem live_chain (payload : α) (program : List (HeadOp σ Slot)) :
    Live (chain payload program) := by
  induction program with
  | nil => exact .leaf payload .nil
  | cons instruction program ih =>
      exact .op instruction ih .nil (by simp [paths_chain])

theorem live_insert (payload : α) {tree : CodeTree σ Slot α} (live : Live tree)
    (program : List (HeadOp σ Slot)) : Live (insert payload tree program) := by
  induction live generalizing program with
  | nil => exact live_chain payload program
  | leaf other _ ih => exact .leaf other (ih program)
  | @op instruction below rest liveBelow liveRest reaches ihBelow ihRest =>
      cases liveRest with
      | nil =>
          cases program with
          | nil => exact .op instruction liveBelow (live_chain payload []) reaches
          | cons first remaining =>
              by_cases same : first = instruction
              · subst same
                simp only [insert]
                exact .op first (ihBelow remaining) .nil (by simp [paths_insert])
              · simp only [insert, if_neg same]
                exact .op instruction liveBelow (live_chain payload _) reaches
      | leaf other liveRest' =>
          exact .op instruction liveBelow (ihRest program) reaches
      | op instruction' liveBelow' liveRest' reaches' =>
          exact .op instruction liveBelow (ihRest program) reaches

theorem size_insert (payload : α) {tree : CodeTree σ Slot α} (live : Live tree)
    (program : List (HeadOp σ Slot)) :
    size (insert payload tree program) + (sharedPrefix (lastCode tree) program).length =
      size tree + program.length := by
  induction live generalizing program with
  | nil => simp [insert, size_chain, lastCode, paths, sharedPrefix_nil_left, size]
  | leaf other _ ih =>
      rw [lastCode_leaf]
      simpa [insert, size] using ih program
  | @op instruction below rest liveBelow liveRest reaches ihBelow ihRest =>
      cases liveRest with
      | nil =>
          rw [lastCode_op_nil instruction reaches]
          cases program with
          | nil =>
              simp [insert, size, size_chain, sharedPrefix_nil_right]
          | cons first remaining =>
              rw [sharedPrefix_cons_cons]
              by_cases same : instruction = first
              · subst same
                have := ihBelow remaining
                simp only [insert, size, List.length_cons, if_true]
                omega
              · simp only [insert, if_neg (Ne.symm same), if_neg same, size, size_chain,
                  List.length_nil, List.length_cons]
                omega
      | leaf other liveRest' =>
          rw [lastCode_op instruction below (by simp [paths])]
          have := ihRest program
          simp only [insert, size] at this ⊢
          omega
      | op instruction' liveBelow' liveRest' reaches' =>
          rw [lastCode_op instruction below (by simp [paths, reaches'])]
          have := ihRest program
          simp only [insert, size] at this ⊢
          omega

theorem size_foldl_insert (entries : List (α × List (HeadOp σ Slot)))
    {tree : CodeTree σ Slot α} (live : Live tree) :
    size (entries.foldl (fun tree entry => insert entry.1 tree entry.2) tree) +
        sharedWithPrevious (lastCode tree) (entries.map Prod.snd) =
      size tree + (entries.map fun entry => entry.2.length).sum := by
  induction entries generalizing tree with
  | nil => simp [sharedWithPrevious]
  | cons entry entries ih =>
      have step := size_insert entry.1 live entry.2
      have rest := ih (live_insert entry.1 live entry.2)
      rw [lastCode_insert] at rest
      simp only [List.foldl_cons, List.map_cons, sharedWithPrevious, List.sum_cons]
      omega

/-- **Sharing.**  The tree of a list of heads stores the heads' instructions
once for each run of consecutive heads sharing them: its size is the total
length of the heads' code less, for each head, the length of the prefix its
code shares with the code of the head before it. -/
theorem size_build (entries : List (α × List (HeadOp σ Slot))) :
    size (build entries) + sharedWithPrevious [] (entries.map Prod.snd) =
      (entries.map fun entry => entry.2.length).sum := by
  simpa [build, size, lastCode, paths] using size_foldl_insert entries Live.nil

end CodeTree

/-! ## Renumbering slots

The heads of one relation have different numbers of slots; their code shares
one tree once every slot is numbered by `ℕ`. -/

section Renumbering

variable {σ : LPSignature.{u, u, r, u}} {Slot Slot' : Type u}

/-- Renumber the slots an instruction names. -/
def renumber (f : Slot → Slot') : HeadOp σ Slot → HeadOp σ Slot'
  | .bindSlot source slot => .bindSlot source (f slot)
  | .equateSlot source slot => .equateSlot source (f slot)
  | .constant source value => .constant source value
  | .node source function target => .node source function target

/-- Read a state's slots through `f`. -/
def pullSlots (f : Slot → Slot') (state : HeadState σ Slot') : HeadState σ Slot where
  registers := state.registers
  slots := state.slots ∘ f
  store := state.store
  supply := state.supply

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Slot] [DecidableEq Slot']
variable (name : ℕ → σ.vars)

/-- An instruction on renumbered slots, read back through the renumbering, is
the original instruction. -/
theorem step_renumber {f : Slot → Slot'} (injective : Function.Injective f)
    (instruction : HeadOp σ Slot) (state : HeadState σ Slot') :
    (step name (renumber f instruction) state).map (pullSlots f) =
      step name instruction (pullSlots f state) := by
  cases instruction with
  | bindSlot source slot =>
      simp only [step, renumber, pullSlots]
      cases state.registers source <;>
        simp [pullSlots, Function.update_comp_eq_of_injective _ injective]
  | equateSlot source slot =>
      simp only [step, renumber, pullSlots, Function.comp_apply]
      cases state.registers source <;> cases state.slots (f slot) <;> simp [Option.map_map]
      rfl
  | constant source value =>
      simp only [step, renumber, pullSlots]
      cases loaded : state.registers source with
      | none => rfl
      | some term =>
          cases read : state.store.applyTerm term with
          | var v => simp [read, pullSlots]
          | const actual => by_cases same : value = actual <;> simp [read, same, pullSlots]
          | app _ _ => simp [read]
  | node source function target =>
      simp only [step, renumber, pullSlots]
      cases loaded : state.registers source with
      | none => rfl
      | some term =>
          cases read : state.store.applyTerm term with
          | var v => simp [read, bindFreshNode, pullSlots]
          | const actual => simp [read]
          | app actual children =>
              by_cases same : actual = function <;> simp [read, same, loadNode, pullSlots]

theorem exec_renumber {f : Slot → Slot'} (injective : Function.Injective f)
    (program : List (HeadOp σ Slot)) (state : HeadState σ Slot') :
    (exec name (program.map (renumber f)) state).map (pullSlots f) =
      exec name program (pullSlots f state) := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [List.map_cons, exec]
      rw [← step_renumber name injective instruction state]
      cases step name (renumber f instruction) state with
      | none => rfl
      | some next => simpa using ih next

end Renumbering

/-! ## The activation step through a code tree -/

section Activation

open DefunctionalizedEquationBodies

variable {σ : LPSignature.{0, 0, r, 0}}
variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
variable (name : ℕ → σ.vars)
variable {Rel Op : Type} [DecidableEq Rel]

/-- The code of an equation's head, with its slots numbered by `ℕ`. -/
def headCode (e : Equation (headTemplates σ) Rel Op) : List (HeadOp σ ℕ) :=
  (emitHead e.params).map (renumber Fin.val)

/-- The code tree of a relation: its equations in authored order, each with
its index and the code of its head. -/
def relationTree (P : EqProgram (headTemplates σ) Rel Op) (rel : Rel) :
    CodeTree σ ℕ (ℕ × Equation (headTemplates σ) Rel Op) :=
  CodeTree.build ((P.equations rel).zipIdx.map fun entry => ((entry.2, entry.1), headCode entry.1))

/-- Finish an equation's activation from the final state of its head's code:
check the argument count, and give every slot the head left unbound a fresh
variable. -/
def finish (args : List (Term σ)) (e : Equation (headTemplates σ) Rel Op)
    (final : HeadState σ ℕ) : Option (Activation (headTemplates σ) Rel Op (Subst σ × ℕ)) :=
  if e.params.length = args.length then
    some ⟨e.slots, fun i => (final.slots i).getD (.var (name (final.supply + i))),
      (final.store, final.supply + e.slots), e.rhs⟩
  else none

/-- The activation step through a code tree: the tree runs once on the call's
arguments, and every equation whose head code reaches its leaf is finished,
with its index. -/
def treeActivate (tree : CodeTree σ ℕ (ℕ × Equation (headTemplates σ) Rel Op))
    (args : List (Term σ)) (θ : Subst σ) (n : ℕ) :
    List (ℕ × Activation (headTemplates σ) Rel Op (Subst σ × ℕ)) :=
  (CodeTree.run name tree (initialState args θ n)).filterMap fun reached =>
    (finish name args reached.1.2 reached.2).map (reached.1.1, ·)

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq Rel] in
private theorem filterMap_sublist_map {β γ : Type} (f : β → Option γ) (h : β → γ)
    (agree : ∀ x y, f x = some y → y = h x) :
    ∀ l : List β, (l.filterMap f).Sublist (l.map h)
  | [] => .slnil
  | x :: rest => by
      rw [List.filterMap_cons, List.map_cons]
      cases fx : f x with
      | none => exact (filterMap_sublist_map f h agree rest).cons _
      | some y =>
          rw [agree x y fx]
          exact (filterMap_sublist_map f h agree rest).cons_cons _

omit [DecidableEq Rel] in
/-- An equation's head code on `ℕ`-numbered slots, finished, is the compiled
activation of the equation. -/
theorem finish_headCode (e : Equation (headTemplates σ) Rel Op) (args : List (Term σ))
    (θ : Subst σ) (n : ℕ) :
    (exec name (headCode e) (initialState args θ n)).bind (finish name args e) =
      (compiledActivation name e.params args θ n).map fun result =>
        ⟨e.slots, result.1, (result.2.1, result.2.2), e.rhs⟩ := by
  have renumbered := exec_renumber name Fin.val_injective (emitHead e.params)
    (initialState args θ n)
  change (exec name (headCode e) (initialState args θ n)).map (pullSlots Fin.val) =
    exec name (emitHead e.params) (initialState args θ n) at renumbered
  unfold compiledActivation
  by_cases lengths : e.params.length = args.length
  · rw [if_pos lengths, ← renumbered]
    cases exec name (headCode e) (initialState args θ n) with
    | none => rfl
    | some final => simp [finish, lengths, pullSlots]
  · rw [if_neg lengths]
    cases exec name (headCode e) (initialState args θ n) <;> simp [finish, lengths]

/-- **The code tree realizes the activation step.**  Running a relation's code
tree once on a call yields, in authored order, exactly the equations whose
compiled heads accept the call, each with its index and the activation its
compiled head produces when run on its own. -/
theorem treeActivate_relationTree (P : EqProgram (headTemplates σ) Rel Op) (rel : Rel)
    (args : List (Term σ)) (θ : Subst σ) (n : ℕ) :
    treeActivate name (relationTree P rel) args θ n =
      (P.equations rel).zipIdx.filterMap fun entry =>
        (compiledActivation name entry.1.params args θ n).map fun result =>
          (entry.2, ⟨entry.1.slots, result.1, (result.2.1, result.2.2), entry.1.rhs⟩) := by
  unfold treeActivate relationTree
  rw [CodeTree.run_eq_runEach, CodeTree.paths_build, CodeTree.runEach, List.filterMap_filterMap,
    List.filterMap_map]
  congr 1
  funext entry
  obtain ⟨e, index⟩ := entry
  have key := finish_headCode name e args θ n
  simp only [Function.comp_apply]
  cases ran : exec name (headCode e) (initialState args θ n) with
  | none =>
      rw [ran, Option.bind_none] at key
      cases accepted : compiledActivation name e.params args θ n with
      | none => rfl
      | some result =>
          rw [accepted] at key
          cases key
  | some final =>
      rw [ran, Option.bind_some] at key
      simp only [Option.map_some, Option.bind_some]
      rw [key]
      cases compiledActivation name e.params args θ n <;> rfl

/-- Without the indices, the tree's activation step is the compiled
activation step. -/
theorem treeActivate_map_snd (P : EqProgram (headTemplates σ) Rel Op) (rel : Rel)
    (args : List (Term σ)) (θ : Subst σ) (n : ℕ) :
    (treeActivate name (relationTree P rel) args θ n).map Prod.snd =
      compiledActivate name P (rel, args, (θ, n)) := by
  rw [treeActivate_relationTree, List.map_filterMap, compiledActivate]
  conv_rhs => rw [← List.zipIdx_map_fst 0 (P.equations rel), List.filterMap_map]
  congr 1
  funext entry
  simp [Option.map_map, Function.comp_def]

/-- The indices of the activated equations increase: each equation is
activated at most once, in authored order. -/
theorem treeActivate_indices (P : EqProgram (headTemplates σ) Rel Op) (rel : Rel)
    (args : List (Term σ)) (θ : Subst σ) (n : ℕ) :
    ((treeActivate name (relationTree P rel) args θ n).map Prod.fst).Pairwise (· < ·) := by
  rw [treeActivate_relationTree, List.map_filterMap]
  refine (List.pairwise_lt_range' (s := 0) (n := (P.equations rel).length)).sublist ?_
  rw [← List.zipIdx_map_snd]
  refine filterMap_sublist_map _ _ (fun entry index accepted => ?_) _
  cases result : compiledActivation name entry.1.params args θ n <;> simp_all

variable {Op : Type} (prim : Op → List (Term σ) → Subst σ × ℕ → Option (Term σ))
  (test : Op → List (Term σ) → Subst σ × ℕ → Option Bool)

/-- **Exactness against the defunctionalized machine.**  The code tree's
activation step activates the same equations, in the same authored order, as
`DefunctionalizedEquationBodies.activate` over the substitution store, each
pair sharing the equation's body and agreeing up to the names of fresh
variables. -/
theorem treeActivate_exact (injective : Function.Injective name)
    (P : EqProgram (headTemplates σ) Rel Op) (rel : Rel) (args : List (Term σ))
    (θ : Subst σ) (n : ℕ) (entry : EntryCondition name θ n args) :
    List.Forall₂ (SameActivation name n)
      ((treeActivate name (relationTree P rel) args θ n).map Prod.snd)
      (activate (headTemplates σ) (substitutionStore name prim test) P (rel, args, (θ, n))) := by
  rw [treeActivate_map_snd]
  exact compiledActivate_exact name prim test injective P rel args θ n entry

omit [DecidableEq σ.vars] in
/-- The relation's tree shares code: it stores the total length of its heads'
code less what each head shares with the head before it. -/
theorem size_relationTree (P : EqProgram (headTemplates σ) Rel Op) (rel : Rel) :
    (relationTree P rel).size +
        CodeTree.sharedWithPrevious [] ((P.equations rel).map headCode) =
      ((P.equations rel).map fun e => (headCode e).length).sum := by
  have := CodeTree.size_build ((P.equations rel).zipIdx.map fun entry =>
    (((entry.2, entry.1) : ℕ × Equation (headTemplates σ) Rel Op), headCode entry.1))
  simp only [List.map_map, Function.comp_def] at this
  rw [← List.zipIdx_map_fst 0 (P.equations rel), List.map_map, List.map_map]
  exact this

end Activation

end Mettapedia.GSLT.LanguageDef.CompiledHeadCodeTree
