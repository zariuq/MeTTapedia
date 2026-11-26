import Mettapedia.Machines.TIsa.StoreInstructions.SymbolicGuardScan
import Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingTrail

/-!
# One solver run distinguishes certain, possible, and impossible

After applying the current principal answer, test a single
pair of terms. An empty successful trail does more than say
the terms unify: it says they were already equal. A nonempty
successful trail says equality is possible but not forced.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.SolverGuardTrichotomy

open Mettapedia.Logic.LP
open Derivation.FiniteUnifier (Configuration Conflict Equations Trail Work action advance step run start meaning readTrail)

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

private inductive Reflexive : Configuration σ → Prop
  | working (pending : Equations σ) (same : ∀ eq ∈ pending, eq.1 = eq.2) :
      Reflexive (.working ⟨pending, []⟩)
  | solved : Reflexive (.solved [])

private theorem reflexive_step {state : Configuration σ} (refl : Reflexive state) : Reflexive (step state) := by
  cases refl with
  | solved => exact .solved
  | working pending same =>
    cases pending with
    | nil => exact .solved
    | cons first rest =>
      rcases first with ⟨left, right⟩
      have equal : left = right := same (left, right) List.mem_cons_self
      subst right
      have inherited : ∀ eq ∈ rest, eq.1 = eq.2 := fun eq h => same eq (List.mem_cons_of_mem _ h)
      cases left with
      | var name => simpa [step, advance, action] using (Reflexive.working rest inherited)
      | const atom => simpa [step, advance, action] using (Reflexive.working rest inherited)
      | app f args =>
        have children : ∀ eq ∈ finPairsToList args args ++ rest, eq.1 = eq.2 := by
          intro eq seen
          rcases List.mem_append.mp seen with here | there
          · unfold finPairsToList at here
            obtain ⟨i, _, rfl⟩ := List.mem_map.mp here
            rfl
          · exact inherited eq there
        simpa [step, advance, action] using (Reflexive.working (finPairsToList args args ++ rest) children)

private theorem reflexive_run (fuel : ℕ) {state : Configuration σ} (refl : Reflexive state) :
    Reflexive (run fuel state) := by
  induction fuel generalizing state with
  | zero => exact refl
  | succ fuel ih => exact ih (reflexive_step refl)

theorem solved_empty_iff_equal (fuel : ℕ) (left right : Term σ) (trail : Trail σ)
    (solved : run fuel (start [(left, right)]) = .solved trail) : trail = [] ↔ left = right := by
  constructor
  · intro empty
    subst trail
    have exact := Derivation.FiniteUnifier.start_exact fuel [(left, right)]
    rw [solved] at exact
    have identical : unifyTotal [(left, right)] = some (Subst.id σ) := exact.symm
    have equality := unifyTotal_sound _ _ identical (left, right) List.mem_cons_self
    simpa only [Subst.applyTerm_id] using equality
  · intro same
    subst right
    have invariant : Reflexive (start [(left, left)]) :=
      .working _ (fun eq present => by obtain rfl := List.mem_singleton.mp present; rfl)
    have ends := reflexive_run fuel invariant
    rw [solved] at ends
    cases ends
    rfl

inductive Observation where
  | impossible | possible | assured
  deriving Repr, DecidableEq

def observe : Configuration σ → Option Observation
  | .working _ => none
  | .inconsistent _ => some .impossible
  | .solved [] => some .assured
  | .solved (_ :: _) => some .possible

def specification (left right : Term σ) : Observation :=
  if left = right then .assured else if (unifyTotal [(left, right)]).isSome then .possible else .impossible

/-- There is no second equality traversal after successful
unification. The trail already distinguishes the two cases. -/
theorem observe_finished (fuel : ℕ) (left right : Term σ)
    (terminal : Derivation.FiniteUnifier.terminal (run fuel (start [(left, right)])) = true) :
    observe (run fuel (start [(left, right)])) = some (specification left right) := by
  cases selected : run fuel (start [(left, right)]) with
  | working work => simp [selected, Derivation.FiniteUnifier.terminal] at terminal
  | inconsistent why =>
    have stuck := Derivation.FiniteUnifier.start_exact fuel [(left, right)]
    rw [selected] at stuck
    have failed : unifyTotal [(left, right)] = none := stuck.symm
    have different : left ≠ right := by
      intro same
      subst right
      have invariant : Reflexive (start [(left, left)]) :=
        .working _ (fun eq present => by obtain rfl := List.mem_singleton.mp present; rfl)
      have ends := reflexive_run fuel invariant
      rw [selected] at ends
      cases ends
    simp [specification, different, failed, observe]
  | solved trail =>
    have succeeded := Derivation.FiniteUnifier.start_exact fuel [(left, right)]
    rw [selected] at succeeded
    have found : unifyTotal [(left, right)] = some (readTrail (Subst.id σ) trail) := succeeded.symm
    have same := solved_empty_iff_equal fuel left right trail selected
    cases trail with
    | nil => simp [specification, same.mp rfl, observe]
    | cons first rest =>
      have different : left ≠ right := fun equal => List.cons_ne_nil _ _ (same.mpr equal)
      simp [specification, different, found, observe]

theorem complete_observation (left right : Term σ) :
    ∃ fuel, observe (run fuel (start [(left, right)])) = some (specification left right) := by
  obtain ⟨fuel, complete, _⟩ := Derivation.FiniteUnifier.complete [(left, right)]
  exact ⟨fuel, observe_finished fuel left right complete⟩

def Observation.must : Observation → Bool
  | .assured => true
  | _ => false

def Observation.may : Observation → Bool
  | .impossible => false
  | _ => true

theorem must_exact (left right : Term σ) : (specification left right).must = decide (left = right) := by
  by_cases equal : left = right
  · simp [specification, equal, Observation.must]
  · cases unifies : (unifyTotal [(left, right)]).isSome <;> simp [specification, equal, unifies, Observation.must]

theorem may_exact (left right : Term σ) : (specification left right).may = (unifyTotal [(left, right)]).isSome := by
  by_cases equal : left = right
  · subst right
    obtain ⟨answer, unifies⟩ := unifyTotal_complete (equations := [(left, left)])
      ⟨Subst.id σ, fun eq found => by obtain rfl := List.mem_singleton.mp found; rfl⟩
    simp [specification, unifies, Observation.may]
  · cases unifies : (unifyTotal [(left, right)]).isSome <;> simp [specification, equal, unifies, Observation.may]

/-- One completed three-way decision per occurrence suffices
for the three existing all-solutions observers. -/
theorem scan (answer : Subst σ) {O : Type} (label : O → Term σ) (pattern : Term σ)
    (occurrences : List O) (query : IndexedGuard.Query) :
    let tag := fun o => specification (answer.applyTerm pattern) (answer.applyTerm (label o))
    SymbolicGuardScan.scan Observation.must Observation.may query (occurrences.map tag) =
      SymbolicGuardScan.scan (SymbolicGuardScan.assures answer label pattern)
        (SymbolicGuardScan.permits answer label pattern) query occurrences := by
  dsimp only
  rw [SymbolicGuardScan.scan_map]
  congr 1
  · funext o
    exact must_exact _ _
  · funext o
    exact may_exact _ _

/-- A representation from which both must and may can be
recovered cannot identify two of the three outcomes. -/
theorem necessary_information {Code : Type*} (encode : Observation → Code) (must may : Code → Bool)
    (mustRead : ∀ x, must (encode x) = x.must) (mayRead : ∀ x, may (encode x) = x.may) :
    Function.Injective encode := by
  intro first second same
  have definite := (mustRead first).symm.trans ((congrArg must same).trans (mustRead second))
  have feasible := (mayRead first).symm.trans ((congrArg may same).trans (mayRead second))
  cases first <;> cases second <;> simp_all [Observation.must, Observation.may]

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem packed_trail_empty_iff_zero (arena : PackedEquations.Arena) (history : PackedWorklist.Words)
    (readable : PackedEquations.readWords arena (NativeBindingTrail.root arena) = some history) :
    history = [] ↔ NativeBindingTrail.root arena = 0 := by
  constructor
  · rintro rfl
    exact NativeAgendaRead.empty_cursor arena _ (NativeAgendaRecords.top_of_read arena _ [] readable)
  · intro zero
    rw [zero] at readable
    exact Option.some.inj readable.symm

namespace Examples

private abbrev Atoms : LPSignature where
  vars := ℕ
  constants := Bool
  functionSymbols := Empty
  functionArity := fun _ => 0
  relationSymbols := Empty
  relationArity := fun _ => 0

private instance : DecidableEq Atoms.vars := inferInstanceAs (DecidableEq ℕ)
private instance : DecidableEq Atoms.constants := inferInstanceAs (DecidableEq Bool)
private instance : DecidableEq Atoms.functionSymbols := inferInstanceAs (DecidableEq Empty)

theorem a_term_is_assured_equal_to_itself :
    observe (run 2 (start ([(Term.var 0, Term.var 0)] : Equations Atoms))) = some .assured := by decide +kernel

theorem unification_success_alone_does_not_make_a_guard_certain :
    observe (run 2 (start ([(Term.var 0, Term.const true)] : Equations Atoms))) = some .possible := by decide +kernel

theorem different_constants_are_impossible :
    observe (run 1 (start ([(Term.const false, Term.const true)] : Equations Atoms))) = some .impossible := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.SolverGuardTrichotomy
