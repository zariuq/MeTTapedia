import Mettapedia.Machines.TIsa.StoreInstructions.SymbolicGuardScan
import Mettapedia.Machines.TIsa.Derivation.SymbolicAllocation
import Mettapedia.Logic.LP.TotalUnificationStructural

/-!
# The symbolic store profile of p1

MATCH checks occurrence use and records an equation. A tell
records another equation. One TEST resolves the accumulated
information; later tests ask what holds in every residual
solution. Produced terms, like surviving terms, are kept open.
Neither the solver nor the guards writes to the occurrence store.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.SymbolicExecution

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting (Check EquationStore)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderLicence (certain potential)
open Derivation (Store Match Role Determinate)
open Derivation.SymbolicFiring (LiveWorld)
open SymbolicGuardScan (assures permits scan scan_map scan_correct)

universe u p
variable {σ : LPSignature.{u, u, p, u}}

abbrev Equations (σ : LPSignature) := EquationStore (Term σ)

/-- New equations are pushed in constant time. Reversing them at
resolution keeps the source ordering of take, read and tell. -/
structure Work (σ : LPSignature) where
  newer : Equations σ
  answer : Option (Subst σ)

def Work.extend (work : Work σ) (equation : Term σ × Term σ) : Work σ :=
  ⟨equation :: work.newer, none⟩

def Work.problem (base : Equations σ) (work : Work σ) : Equations σ := base ++ work.newer.reverse

theorem Work.extend_problem (base : Equations σ) (work : Work σ) (equation : Term σ × Term σ) :
    (work.extend equation).problem base = work.problem base ++ [equation] := by
  simp [Work.extend, Work.problem, List.append_assoc]

def initial (σ : LPSignature) : Match (Term σ) (Work σ) := ⟨⟨[], none⟩, [], [], [], []⟩

def propose (role : Role) (pattern : Term σ) (entry : Match (Term σ) (Work σ))
    (candidate : ℕ × Term σ) : Option (Match (Term σ) (Work σ)) :=
  if role.allows entry candidate.1 then
    some (entry.select role candidate.1 (entry.bindings.extend (pattern, candidate.2)))
  else none

/-- An unresolved value is not a failed match. Both its identity
and the exact equation are retained on the selected continuation. -/
theorem propose_records (base : Equations σ) (role : Role) (pattern : Term σ)
    (entry : Match (Term σ) (Work σ)) (candidate : ℕ × Term σ) (allows : role.allows entry candidate.1 = true) :
    ∃ following, propose role pattern entry candidate = some following ∧
      following.bindings.problem base = entry.bindings.problem base ++ [(pattern, candidate.2)] ∧
      following.bindings.answer = none := by
  have same := Work.extend_problem base entry.bindings (pattern, candidate.2)
  cases role <;>
    exact ⟨_, if_pos allows, same, rfl⟩

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

def resolve (base : Equations σ) (entry : Match (Term σ) (Work σ)) : Option (Match (Term σ) (Work σ)) :=
  (unifyTotalStructural (entry.bindings.problem base)).map fun answer =>
    { entry with bindings := { entry.bindings with answer := some answer } }

theorem resolve_exact (base : Equations σ) (entry : Match (Term σ) (Work σ)) :
    resolve base entry =
      (unifyTotal (entry.bindings.problem base)).map fun answer =>
        { entry with bindings := { entry.bindings with answer := some answer } } := by
  rw [resolve, unifyTotalStructural_eq_unifyTotal]

abbrev Atom (σ : LPSignature) := ℕ × Term σ

def assured (answer : Subst σ) (pattern : Term σ) (atom : Atom σ) : Bool :=
  decide (answer.applyTerm pattern = answer.applyTerm atom.2)

def possible (answer : Subst σ) (pattern : Term σ) (atom : Atom σ) : Bool :=
  (unifyTotalStructural [(answer.applyTerm pattern, answer.applyTerm atom.2)]).isSome

private theorem possible_agrees (answer : Subst σ) (pattern : Term σ) (atom : Atom σ) :
    possible answer pattern atom = (unifyTotal [(answer.applyTerm pattern, answer.applyTerm atom.2)]).isSome := by
  rw [possible, unifyTotalStructural_eq_unifyTotal]

def guard (answer : Subst σ) (atoms : List (Atom σ)) : Check (Term σ) → Bool
  | .equal left right => decide (answer.applyTerm left = answer.applyTerm right)
  | .predicate .any pattern => scan (assured answer pattern) (possible answer pattern) .any atoms
  | .predicate .none pattern => scan (assured answer pattern) (possible answer pattern) .absent atoms
  | .count pattern expected => scan (assured answer pattern) (possible answer pattern) (.count expected) atoms

theorem guard_exact (answer : Subst σ) (label : ℕ → Term σ) (live : List ℕ) (distinct : live.Nodup)
    (condition : Check (Term σ)) :
    guard answer (live.map fun i => (i, label i)) condition =
      Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderLicence.check
        answer label live.toFinset condition := by
  have indexed (query : IndexedGuard.Query) (pattern : Term σ) :
      scan (assured answer pattern) (possible answer pattern) query (live.map fun i => (i, label i)) =
        Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderLicence.check
          answer label live.toFinset (query.check pattern) := by
    have scanPossible : (possible answer pattern ∘ fun i => (i, label i)) = permits answer label pattern := by
      funext i
      exact possible_agrees answer pattern (i, label i)
    rw [scan_map, scanPossible]
    exact scan_correct answer label pattern live distinct query
  cases condition with
  | equal lhs rhs => rfl
  | predicate quantifier pattern =>
    cases quantifier with
    | any => exact indexed .any pattern
    | none => exact indexed .absent pattern
  | count pattern expected => exact indexed (.count expected) pattern

def collect (answer : Subst σ) (atoms : List (Atom σ)) (pattern : Term σ) : Option (Finset ℕ) :=
  if atoms.all (fun atom => assured answer pattern atom || !possible answer pattern atom) then
    some (((atoms.filter (assured answer pattern)).map Prod.fst).toFinset)
  else none

theorem collect_exact (answer : Subst σ) (label : ℕ → Term σ) (live : List ℕ) (pattern : Term σ) :
    collect answer (live.map fun i => (i, label i)) pattern =
      if potential answer label live.toFinset pattern ⊆ certain answer label live.toFinset pattern
      then some (certain answer label live.toFinset pattern) else none := by
  have certain_eq :
      (((live.map fun i => (i, label i)).filter (assured answer pattern)).map Prod.fst).toFinset =
        certain answer label live.toFinset pattern := by
    rw [List.filter_map, List.map_map, show Prod.fst ∘ (fun i => (i, label i)) = id from rfl, List.map_id]
    change (live.filter (fun i => assured answer pattern (i, label i))).toFinset = _
    ext i
    simp only [certain, List.mem_toFinset, List.mem_filter, Finset.mem_filter, assured, decide_eq_true_eq]
  have covers :
      (live.map fun i => (i, label i)).all (fun atom => assured answer pattern atom || !possible answer pattern atom) = true ↔
        potential answer label live.toFinset pattern ⊆ certain answer label live.toFinset pattern := by
    simp only [List.all_map, Function.comp_apply, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      possible_agrees, assured, decide_eq_true_eq, potential, certain, Finset.subset_iff, Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro closed i ⟨member, permitted⟩
      exact ⟨member, (closed i member).resolve_right (by simp [permitted])⟩
    · intro stable i member
      cases permitted : (unifyTotal [(answer.applyTerm pattern, answer.applyTerm (label i))]).isSome
      · exact Or.inr rfl
      · exact Or.inl (stable ⟨member, permitted⟩).2
  simp only [collect, covers, certain_eq]

inductive Goal (σ : LPSignature) where
  | resolve
  | perform (goal : Determinate (Term σ))

def test (base : Equations σ) (store : Store (Term σ))
    (goal : Goal σ) (entry : Match (Term σ) (Work σ)) : Option (Match (Term σ) (Work σ)) :=
  match goal with
  | .resolve => resolve base entry
  | .perform (.tell left right) => some { entry with bindings := entry.bindings.extend (left, right) }
  | .perform (.check condition) =>
    match entry.bindings.answer with
    | some answer => if guard answer store.occurrences condition then some entry else none
    | none => none
  | .perform (.collect pattern) =>
    match entry.bindings.answer with
    | none => none
    | some answer => (collect answer store.occurrences pattern).map
        fun visible => { entry with seen := entry.seen ++ [visible] }
  | .perform (.produce template) =>
    match entry.bindings.answer with
    | some _ => some { entry with made := entry.made ++ [template] }
    | none => none

abbrev Op (σ : LPSignature) := P1Source.StoreOp Role (Term σ) (Goal σ)
abbrev Code (σ : LPSignature) := P1Source.Statement (Op σ) true
abbrev Frame (σ : LPSignature) := StoreInstructions.State (Term σ) (Work σ)

def profile (base : Equations σ) : StoreProfile (Term σ) (Goal σ) (Term σ) (Work σ) :=
  ⟨initial σ, propose, test base⟩

abbrev execute (base : Equations σ) := executeWith (profile base).step

def storeOf (world : LiveWorld σ) : Store (Term σ) :=
  ⟨world.live.map (fun identity => (identity, world.state.label identity)), world.next⟩

def enter (machine : P1WordExecution.State) (world : LiveWorld σ) : Frame σ :=
  ⟨machine, storeOf world, fun _ => initial σ⟩

theorem execute_word (base : Equations σ) (state : Frame σ) (program : P1Source.Stmt) :
    execute base state program.toStore = Flow.lift state (P1WordExecution.execute state.machine program) := by
  have same := executeWith_ofP1 (profile base).step state program state.machine
  exact same

theorem resolution_is_private (base : Equations σ) (state : Frame σ) (level : ℕ) (dst : P1Source.Reg) :
    (execute base state (.instruction (.transform (.test .resolve level dst)))).after.store = state.store := by
  simp only [executeWith, executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, profile, test]
  cases resolve base (state.levels level) <;> rfl

end Mettapedia.Machines.TIsa.StoreInstructions.SymbolicExecution
