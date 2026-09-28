import Mettapedia.Logic.LP.TotalUnification
import Mathlib.Tactic.FinCases

/-!
# Lossless variable coordinates preserve two-sided unification

A variable coordinate change has a left inverse. It may leave unused target
coordinates; surjectivity is unnecessary. Renaming both sides of every
equation preserves unifiability, and a solution can be transported in either
direction. Consequently the total first-order unifier rejects exactly the
same problems before and after a lossless coordinate change.

This concerns the existing first-order term and substitution types. It does
not identify distinct lexical frames or supply higher-order unification.
The controls include a non-ground implication-chain query and an explicit
failure caused by forgetting the distinction between two variables.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.UnificationRenaming

variable {σ : LPSignature}

/-- Rename variables without evaluating the constructors. -/
def rename (f : σ.vars → σ.vars) (term : Term σ) : Term σ :=
  Subst.applyTerm (fun v => .var (f v)) term

@[simp] theorem rename_var (f : σ.vars → σ.vars) (v : σ.vars) :
    rename f (.var v) = Term.var (f v) := rfl

@[simp] theorem rename_const (f : σ.vars → σ.vars) (c : σ.constants) :
    rename f (.const c) = Term.const c := rfl

@[simp] theorem rename_app (f : σ.vars → σ.vars)
    (c : σ.functionSymbols) (children : Fin (σ.functionArity c) → Term σ) :
    rename f (.app c children) = .app c (fun i => rename f (children i)) := rfl

theorem rename_comp (f g : σ.vars → σ.vars) (term : Term σ) :
    rename g (rename f term) = rename (g ∘ f) term := by
  induction term with
  | var v => rfl
  | const c => rfl
  | app c children ih => simp only [rename_app, ih]

theorem rename_id (term : Term σ) : rename id term = term :=
  Subst.applyTerm_id term

theorem rename_leftInverse (f g : σ.vars → σ.vars)
    (inverse : Function.LeftInverse g f) (term : Term σ) :
    rename g (rename f term) = term := by
  rw [rename_comp]
  have same : g ∘ f = id := funext inverse
  rw [same, rename_id]

theorem rename_injective (f g : σ.vars → σ.vars)
    (inverse : Function.LeftInverse g f) : Function.Injective (rename (σ := σ) f) := by
  intro left right equal
  have transported := congrArg (rename g) equal
  simpa only [rename_leftInverse f g inverse] using transported

/-- Interpret source bindings in target coordinates. The inverse is consulted
only on the image for the transport theorem. -/
def push (f g : σ.vars → σ.vars) (theta : Subst σ) : Subst σ :=
  fun v => rename f (theta (g v))

/-- Interpret any target solution back in source coordinates. -/
def pull (f g : σ.vars → σ.vars) (theta : Subst σ) : Subst σ :=
  fun v => rename g (theta (f v))

theorem push_apply (f g : σ.vars → σ.vars) (inverse : Function.LeftInverse g f)
    (theta : Subst σ) (term : Term σ) :
    (push f g theta).applyTerm (rename f term) = rename f (theta.applyTerm term) := by
  induction term with
  | var v => simp only [rename_var, Subst.applyTerm, push, inverse v]
  | const c => rfl
  | app c children ih => simp only [rename_app, Subst.applyTerm, ih]

theorem pull_apply (f g : σ.vars → σ.vars) (theta : Subst σ) (term : Term σ) :
    (pull f g theta).applyTerm term = rename g (theta.applyTerm (rename f term)) := by
  induction term with
  | var v => rfl
  | const c => rfl
  | app c children ih => simp only [rename_app, Subst.applyTerm, ih]

def equations (f : σ.vars → σ.vars) (eqs : List (Term σ × Term σ)) :
    List (Term σ × Term σ) := eqs.map fun pair => (rename f pair.1, rename f pair.2)

theorem push_unifies (f g : σ.vars → σ.vars) (inverse : Function.LeftInverse g f)
    (theta : Subst σ) (eqs : List (Term σ × Term σ)) (solves : Unifies theta eqs) :
    Unifies (push f g theta) (equations f eqs) := by
  intro pair member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  simp only [push_apply f g inverse]
  exact congrArg (rename f) (solves original present)

theorem pull_unifies (f g : σ.vars → σ.vars) (theta : Subst σ)
    (eqs : List (Term σ × Term σ)) (solves : Unifies theta (equations f eqs)) :
    Unifies (pull f g theta) eqs := by
  intro pair member
  rw [pull_apply, pull_apply]
  exact congrArg (rename g) (solves _ (List.mem_map.mpr ⟨pair, member, rfl⟩))

/-- Lossless coordinate encoding neither adds nor removes solutions. -/
theorem unifiable_iff (f g : σ.vars → σ.vars) (inverse : Function.LeftInverse g f)
    (eqs : List (Term σ × Term σ)) :
    (∃ theta, Unifies theta (equations f eqs)) ↔ ∃ theta, Unifies theta eqs := by
  constructor
  · rintro ⟨theta, solves⟩
    exact ⟨pull f g theta, pull_unifies f g theta eqs solves⟩
  · rintro ⟨theta, solves⟩
    exact ⟨push f g theta, push_unifies f g inverse theta eqs solves⟩

theorem rejection_iff [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (f g : σ.vars → σ.vars)
    (inverse : Function.LeftInverse g f) (eqs : List (Term σ × Term σ)) :
    unifyTotal (equations f eqs) = none ↔ unifyTotal eqs = none := by
  rw [unifyTotal_none_iff_not_unifiable, unifyTotal_none_iff_not_unifiable,
    unifiable_iff f g inverse]

/-- A solution from the encoded matcher remains sound when projected back.
This does not require its chosen most-general representative to be identical
to the representative chosen when running on the original coordinates. -/
theorem accepted_projection [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (f g : σ.vars → σ.vars)
    (theta : Subst σ) (eqs : List (Term σ × Term σ))
    (accepted : unifyTotal (equations f eqs) = some theta) :
    Unifies (pull f g theta) eqs :=
  pull_unifies f g theta eqs (unifyTotal_sound _ _ accepted)

namespace Controls

inductive Constructor where
  | arrow
  | sequent
  deriving DecidableEq

def Constructor.arity : Constructor → Nat
  | .arrow => 2
  | .sequent => 3

abbrev sig : LPSignature where
  constants := Unit
  vars := Nat
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Constructor
  functionArity := Constructor.arity

def arrow (a b : Term sig) : Term sig := .app .arrow ![a, b]
def sequent (a b c : Term sig) : Term sig := .app .sequent ![a, b, c]

@[simp] theorem apply_arrow (theta : Subst sig) (a b : Term sig) :
    theta.applyTerm (arrow a b) = arrow (theta.applyTerm a) (theta.applyTerm b) := by
  change Term.app _ _ = Term.app _ _
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem apply_sequent (theta : Subst sig) (a b c : Term sig) :
    theta.applyTerm (sequent a b c) =
      sequent (theta.applyTerm a) (theta.applyTerm b) (theta.applyTerm c) := by
  change Term.app _ _ = Term.app _ _
  congr 1
  funext i
  fin_cases i <;> rfl

def rule : Term sig := sequent (arrow (.var 0) (.var 1)) (.var 0) (.var 1)

def query : Term sig :=
  sequent
    (arrow (arrow (.var 2) (arrow (arrow (.var 3) (.var 2)) (.var 4)))
      (arrow (.var 2) (.var 4)))
    (arrow (.var 5) (arrow (.var 6) (.var 5)))
    (.var 7)

/-- `a=c=x`, `y=(b -> x)`, and the result is `(x -> x)`. -/
def witness : Subst sig
  | 0 => arrow (.var 5) (arrow (arrow (.var 3) (.var 5)) (.var 5))
  | 1 => arrow (.var 5) (.var 5)
  | 2 => .var 5
  | 4 => .var 5
  | 6 => arrow (.var 3) (.var 5)
  | 7 => arrow (.var 5) (.var 5)
  | v => .var v

theorem implication_query_unifiable : Unifies witness [(query, rule)] := by
  intro pair member
  simp only [List.mem_singleton] at member
  subst pair
  simp only [query, rule, apply_arrow, apply_sequent, Subst.applyTerm_var, witness]

theorem implication_query_accepted : ∃ theta, unifyTotal [(query, rule)] = some theta :=
  unifyTotal_complete ⟨witness, implication_query_unifiable⟩

theorem implication_query_result : witness.applyTerm (.var 7) = arrow (.var 5) (.var 5) := rfl

private theorem arrow_injective {a b c d : Term sig}
    (same : arrow a b = arrow c d) : a = c ∧ b = d := by
  have children : (![a, b] : Fin 2 → Term sig) = ![c, d] := by
    injection same
  exact ⟨congrFun children 0, congrFun children 1⟩

private theorem sequent_injective {a b c d e f : Term sig}
    (same : sequent a b c = sequent d e f) : a = d ∧ b = e ∧ c = f := by
  have children : (![a, b, c] : Fin 3 → Term sig) = ![d, e, f] := by
    injection same
  exact ⟨congrFun children 0, congrFun children 1, congrFun children 2⟩

/-- Reusing `a,b` in the second premise is a different logical problem from
introducing independent `x,y`. It requires the finite term `b` to contain
itself as a proper subterm. -/
def sharedQuery : Term sig :=
  sequent
    (arrow (arrow (.var 2) (arrow (arrow (.var 3) (.var 2)) (.var 4)))
      (arrow (.var 2) (.var 4)))
    (arrow (.var 2) (arrow (.var 3) (.var 2)))
    (.var 7)

theorem shared_query_not_unifiable : ¬∃ theta, Unifies theta [(sharedQuery, rule)] := by
  rintro ⟨theta, solves⟩
  have same := solves (sharedQuery, rule) (List.mem_singleton_self _)
  simp only [sharedQuery, rule, apply_arrow, apply_sequent, Subst.applyTerm_var] at same
  obtain ⟨first, second, _⟩ := sequent_injective same
  have samePremise := (arrow_injective first).1.trans second.symm
  have nested := (arrow_injective samePremise).2
  have loop := (arrow_injective nested).1
  have smaller := Term.size_subterm (σ := sig) (f := Constructor.arrow)
    (ts := ![theta 3, theta 2]) ⟨0, by decide⟩
  change (theta 3).size < (arrow (theta 3) (theta 2)).size at smaller
  rw [loop] at smaller
  exact (Nat.lt_irrefl _ smaller)

theorem shared_query_rejected : unifyTotal [(sharedQuery, rule)] = none :=
  (unifyTotal_none_iff_not_unifiable (σ := sig) _).mpr shared_query_not_unifiable

theorem renamed_implication_query_accepted (f g : Nat → Nat)
    (inverse : Function.LeftInverse g f) :
    ∃ theta, unifyTotal (equations f [(query, rule)]) = some theta :=
  unifyTotal_complete ⟨push f g witness,
    push_unifies f g inverse witness _ implication_query_unifiable⟩

/-- A new frame may use a disjoint coordinate range without changing this
problem. This concrete embedding has unused coordinates below its offset. -/
theorem shifted_implication_query_accepted (offset : Nat) :
    ∃ theta, unifyTotal (equations (fun v => offset + v) [(query, rule)]) = some theta := by
  apply renamed_implication_query_accepted _ (fun v => v - offset)
  intro v
  change offset + v - offset = v
  omega

def distinctProblem : List (Term sig × Term sig) :=
  [(.var 0, arrow (.var 1) (.const ()))]

def distinctWitness : Subst sig := Subst.single 0 (arrow (.var 1) (.const ()))

theorem distinct_variables_have_solution :
    ∃ theta, unifyTotal distinctProblem = some theta := by
  apply unifyTotal_complete
  refine ⟨distinctWitness, ?_⟩
  intro pair member
  simp only [distinctProblem, List.mem_singleton] at member
  subst pair
  simp only [apply_arrow, Subst.applyTerm_var, Subst.applyTerm_const]
  rfl

/-- Forgetting variable identity can turn a valid cross-frame reference into
an occurs-check cycle. This is not a permitted coordinate encoding. -/
theorem forgetting_identity_rejects :
    unifyTotal (equations (σ := sig) (fun _ => 0) distinctProblem) = none := by
  rw [unifyTotal.eq_def (σ := sig)]
  simp [equations, distinctProblem, rename, Subst.applyTerm, arrow, Term.occursIn,
    sig, Constructor.arity]

/-- Each proposed assignment passes a purely syntactic self-occurrence test,
yet the pair is cyclic after following the other assignment. -/
def indirectCycle : List (Term sig × Term sig) :=
  [(.var 0, arrow (.var 1) (.const ())),
    (.var 1, arrow (.var 0) (.const ()))]

theorem local_occurs_checks_miss_indirect_cycle :
    Term.occursIn (σ := sig) 0 (arrow (.var 1) (.const ())) = false ∧
    Term.occursIn (σ := sig) 1 (arrow (.var 0) (.const ())) = false := by
  simp [arrow, Term.occursIn, sig, Constructor.arity]

theorem indirect_cycle_not_unifiable : ¬∃ theta, Unifies theta indirectCycle := by
  rintro ⟨theta, solves⟩
  have first := solves (.var 0, arrow (.var 1) (.const ())) (by simp [indirectCycle])
  have second := solves (.var 1, arrow (.var 0) (.const ())) (by simp [indirectCycle])
  simp only [Subst.applyTerm_var, Subst.applyTerm_const, apply_arrow] at first second
  have smaller0 := Term.size_subterm (σ := sig) (f := Constructor.arrow)
    (ts := ![theta 0, Term.const ()]) ⟨0, by decide⟩
  have smaller1 := Term.size_subterm (σ := sig) (f := Constructor.arrow)
    (ts := ![theta 1, Term.const ()]) ⟨0, by decide⟩
  change (theta 0).size < (arrow (theta 0) (.const ())).size at smaller0
  change (theta 1).size < (arrow (theta 1) (.const ())).size at smaller1
  rw [← second] at smaller0
  rw [← first] at smaller1
  exact (Nat.lt_irrefl _ (smaller0.trans smaller1))

theorem indirect_cycle_rejected : unifyTotal indirectCycle = none :=
  (unifyTotal_none_iff_not_unifiable (σ := sig) _).mpr indirect_cycle_not_unifiable

/-- An exhausted resource allowance is not evidence of logical failure. The
total solver succeeds on exactly this input. -/
theorem fuel_failure_is_not_logical_failure :
    unifyFuel 0 distinctProblem = none ∧
      ∃ theta, unifyTotal distinctProblem = some theta :=
  ⟨rfl, distinct_variables_have_solution⟩

end Controls
end Mettapedia.Logic.LP.UnificationRenaming
