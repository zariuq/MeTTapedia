import Mettapedia.Machines.TIsa.StoreInstructions.PackedRootedWorklist
import Mettapedia.Machines.TIsa.StoreInstructions.PackedGuardRoots

/-!
# The meaning of a transported root vector

The initialized vector has one slot per operand. After each
elimination, the slots denote precisely the original terms
under the accumulated substitution. The proof interprets the
trail; execution does not replay it.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedRootedMeaning

open Mettapedia.Logic.LP
open Derivation.FiniteUnifier (Configuration Equations Trail readTrail)
open PackedTerms (Arena lookup)
open PackedWorklist (Words)
open PackedRootedWorklist (Outcome)

universe u p
variable {σ : LPSignature.{u,u,p,u}}

def roots (symbols : UnifierHeaders.Symbols σ) (arena : Arena) (held : Array Word) : Option (List (Term σ)) :=
  held.toList.mapM (lookup symbols arena)

theorem valid_of_read (symbols : UnifierHeaders.Symbols σ) (arena : Arena) (held : Array Word) (terms : List (Term σ))
    (read : roots symbols arena held = some terms) : PackedRootedWorklist.Valid arena held := by
  have readable (handles : List Word) (decoded : List (Term σ))
      (ran : handles.mapM (lookup symbols arena) = some decoded) :
      ∀ handle ∈ handles, handle.toNat < arena.nodes.size := by
    induction handles generalizing decoded with
    | nil => simp
    | cons first tail ih =>
      rw [List.mapM_cons] at ran
      obtain ⟨value, fetched, rest⟩ := Option.bind_eq_some_iff.mp ran
      obtain ⟨values, readMore, _⟩ := Option.bind_eq_some_iff.mp rest
      intro handle member
      rcases List.mem_cons.mp member with here | later
      · subst handle
        obtain ⟨_, atIndex⟩ := PackedTermEdges.node_at symbols arena first value fetched
        exact (Array.getElem?_eq_some_iff.mp atIndex).choose
      · exact ih values readMore handle later
  exact readable held.toList terms read

def context : Outcome → Option (Arena × Words)
  | .working work => some (work.arena, work.trail)
  | .solved arena bindings => some (arena, bindings)
  | .inconsistent _ => none

variable [DecidableEq σ.vars]

def Denotes (symbols : UnifierHeaders.Symbols σ) (original : List (Term σ)) (state : Outcome) (held : Array Word) : Prop :=
  ∀ arena raw logical, context state = some (arena, raw) →
    PackedWorklist.readTrail symbols arena raw = some logical →
    roots symbols arena held = some (original.map (readTrail (Subst.id σ) logical).applyTerm)

theorem entered (symbols : UnifierHeaders.Symbols σ) (arena : Arena) (pending : Words)
    (held : Array Word) (original : List (Term σ)) (read : roots symbols arena held = some original) :
    Denotes symbols original (.working ⟨arena, pending, []⟩) held := by
  intro snapshot raw logical real traced
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj real)
  obtain rfl := Option.some.inj traced
  have identity : (Subst.id σ).applyTerm = id := funext Subst.applyTerm_id
  simpa [readTrail, identity] using read

variable [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
private theorem transport (symbols : UnifierHeaders.Symbols σ) (original : List (Term σ))
    (arena : Arena) (pending history : Words) (held moved : Array Word)
    (before : Denotes symbols original (.working ⟨arena, pending, history⟩) held)
    (oldTrace : Trail σ) (traceRead : PackedWorklist.readTrail symbols arena history = some oldTrace)
    (name value : Word) (variableName : σ.vars) (decoded : symbols.vars.decode name = some variableName)
    (named : symbols.vars.encode variableName = some name) (replacement : Term σ)
    (replacementRead : lookup symbols arena value = some replacement) (room : PackedWorklist.Room arena)
    (result : PackedSubstitution.State) (scanned : PackedSubstitution.substitute arena name value = some result)
    (translated : PackedSubstitution.translate result.mapped held = some moved) (following : Words) :
    Denotes symbols original (.working ⟨result.target, following, (name, value) :: history⟩) moved := by
  obtain ⟨graph, computed, represented⟩ := PackedSubstitution.substitute_exact symbols arena variableName
    name value replacement named replacementRead room.1 room.2
  obtain rfl := Option.some.inj (computed.symm.trans scanned)
  let answer := readTrail (Subst.id σ) oldTrace
  let binding := Subst.single variableName replacement
  have old := before arena history oldTrace rfl traceRead
  obtain ⟨new, remapped, meanings⟩ := PackedSubstitution.translate_exact
    (lookup symbols arena) (lookup symbols graph.target) graph.mapped held binding.applyTerm old
    (fun address _ => PackedSubstitution.in_completed_mapping symbols arena binding graph represented address)
  obtain rfl := Option.some.inj (remapped.symm.trans translated)
  have keptTrace := PackedWorklist.trail_kept symbols arena graph.target represented.keeps history oldTrace traceRead
  have trace : PackedWorklist.readTrail symbols graph.target ((name, value) :: history) =
      some ((variableName, replacement) :: oldTrace) := by
    unfold PackedWorklist.readTrail at keptTrace ⊢
    simp [List.mapM_cons, PackedWorklist.readBinding, decoded, represented.keeps value replacement replacementRead, keptTrace]
  intro snapshot raw logical real traced
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj real)
  obtain rfl := Option.some.inj (trace.symm.trans traced)
  have together : (binding ∘ₛ answer).applyTerm = binding.applyTerm ∘ answer.applyTerm :=
    funext (Subst.applyTerm_comp _ _)
  simpa only [roots, PackedGuardRoots.readTrail_cons, show Subst.single variableName replacement = binding from rfl,
    show readTrail (Subst.id σ) oldTrace = answer from rfl, together, List.map_map] using meanings

private theorem step_exact (symbols : UnifierHeaders.Symbols σ) (original : List (Term σ))
    (state result : Outcome) (held moved : Array Word) (typed : Configuration σ)
    (known : PackedWorklist.read symbols state = some typed)
    (room : PackedWorklist.nodeCount state + PackedWorklist.nodeCount state < 2 ^ 64 ∧
      PackedWorklist.edgeCount state + PackedWorklist.nodeCount state * PackedWorklist.edgeCount state < 2 ^ 64)
    (before : Denotes symbols original state held) (ran : PackedRootedWorklist.step state held = some (result, moved)) :
    PackedWorklist.step state = some result ∧ Denotes symbols original result moved := by
  cases state with
  | solved arena history =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ran)
    exact ⟨rfl, before⟩
  | inconsistent why =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ran)
    exact ⟨rfl, before⟩
  | working work =>
    rcases work with ⟨arena, todo, history⟩
    cases todo with
    | nil =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ran)
      exact ⟨rfl, before⟩
    | cons eq pending =>
      rcases eq with ⟨left, right⟩
      obtain ⟨action, looked, chosen⟩ := Option.bind_eq_some_iff.mp ran
      cases action with
      | discard =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj chosen)
        exact ⟨by simp [PackedWorklist.step, PackedWorklist.advance, looked], before⟩
      | decompose pairs =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj chosen)
        exact ⟨by simp [PackedWorklist.step, PackedWorklist.advance, looked], before⟩
      | refuse why =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj chosen)
        exact ⟨by simp [PackedWorklist.step, PackedWorklist.advance, looked], fun _ _ _ out => nomatch out⟩
      | bindVar name value =>
        obtain ⟨graph, computed, rest⟩ := Option.bind_eq_some_iff.mp chosen
        obtain ⟨future, movedSuffix, rest⟩ := Option.bind_eq_some_iff.mp rest
        obtain ⟨next, movedRoots, selected⟩ := Option.bind_eq_some_iff.mp rest
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj selected)
        obtain ⟨eqs, source, readRest⟩ := Option.bind_eq_some_iff.mp known
        obtain ⟨oldTrace, traced, _⟩ := Option.bind_eq_some_iff.mp readRest
        rw [PackedWorklist.readEquations, List.mapM_cons] at source
        obtain ⟨_, first, _⟩ := Option.bind_eq_some_iff.mp source
        obtain ⟨lTerm, readL, thenRight⟩ := Option.bind_eq_some_iff.mp first
        obtain ⟨rTerm, readR, _⟩ := Option.map_eq_some_iff.mp thenRight
        have meaning := PackedUnifierAction.inspect_exact symbols arena left right lTerm rTerm readL readR
        rw [looked, Option.bind_some] at meaning
        obtain ⟨variableName, replacement, decoded, named, valueRead, _⟩ :=
          PackedWorklist.bind_decoded symbols arena name value _ meaning
        exact ⟨by simp [PackedWorklist.step, PackedWorklist.advance, looked, computed, movedSuffix],
          transport symbols original arena ((left, right) :: pending) history held next before oldTrace traced name value
            variableName decoded named replacement valueRead room graph computed movedRoots future⟩

/-- Symbolic transport agrees with the source unifier at
every prefix, and hence also at successful termination. -/
theorem run_exact (symbols : UnifierHeaders.Symbols σ) (original : List (Term σ)) (fuel : ℕ)
    (state result : Outcome) (held final : Array Word) (typed : Configuration σ)
    (known : PackedWorklist.read symbols state = some typed) (before : Denotes symbols original state held)
    (room : PackedWorklist.Reserve fuel (PackedWorklist.nodeCount state) (PackedWorklist.edgeCount state))
    (ran : PackedRootedWorklist.run fuel state held = some (result, final)) :
    PackedWorklist.run fuel state = some result ∧
      PackedWorklist.read symbols result = some (Derivation.FiniteUnifier.run fuel typed) ∧ Denotes symbols original result final := by
  induction fuel generalizing state held typed with
  | zero =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ran)
    exact ⟨rfl, known, before⟩
  | succ fuel ih =>
    obtain ⟨⟨middle, moved⟩, taken, next⟩ := Option.bind_eq_some_iff.mp ran
    have numeric := PackedWorklist.reserve_current fuel _ _ room
    obtain ⟨baseStep, computed, decoded, nodes, edges⟩ := PackedWorklist.step_checked symbols state typed numeric known
    obtain ⟨projected, carried⟩ := step_exact symbols original state middle held moved typed known numeric before taken
    have same := Option.some.inj (computed.symm.trans projected)
    subst baseStep
    obtain ⟨rest, answer, kept⟩ := ih middle moved (Derivation.FiniteUnifier.step typed) decoded carried
      (PackedWorklist.reserve_mono fuel nodes edges room) next
    exact ⟨by simp only [PackedWorklist.run, computed, Option.bind_some, rest], answer, kept⟩

theorem solved_exact (symbols : UnifierHeaders.Symbols σ) (arena : Arena) (pending : Words)
    (held final : Array Word) (original : List (Term σ)) (equations : Equations σ)
    (read : PackedWorklist.readEquations symbols arena pending = some equations) (decoded : roots symbols arena held = some original)
    (fuel : ℕ) (room : PackedWorklist.Reserve fuel arena.nodes.size arena.children.size) (result : Arena) (trail : Words)
    (ran : PackedRootedWorklist.run fuel (.working ⟨arena, pending, []⟩) held = some (.solved result trail, final)) :
    ∃ ans, unifyTotal equations = some ans ∧ roots symbols result final = some (original.map ans.applyTerm) := by
  have started : PackedWorklist.read symbols (.working ⟨arena, pending, []⟩) = some (Derivation.FiniteUnifier.start equations) :=
    by simp [PackedWorklist.read, PackedWorklist.readTrail, read, Derivation.FiniteUnifier.start]
  obtain ⟨_, proof, meaning⟩ := run_exact symbols original fuel (.working ⟨arena, pending, []⟩) (.solved result trail)
    held final _ started (entered symbols arena pending held original decoded) room ran
  obtain ⟨logical, readTrail, solved⟩ := Option.map_eq_some_iff.mp proof
  exact ⟨Derivation.FiniteUnifier.readTrail (Subst.id σ) logical, Derivation.FiniteUnifier.solved_exact fuel equations logical solved.symm,
    meaning result trail logical rfl readTrail⟩

end Mettapedia.Machines.TIsa.StoreInstructions.PackedRootedMeaning
