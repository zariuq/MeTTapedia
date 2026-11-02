import Mettapedia.Machines.StoredIdViews

/-!
# A resumable stored-ID unifier

Worklist operands and answer bindings are stored views with lazy substitution
closures. The algorithm uses one-head inspection and the ID-based occurs
walk; it does not invoke readback. Readback maps it to the existing tree
Martelli--Montanari implementation. Fuel exhaustion retains the exact pending
equations and binding prefix, separately from a logical conflict.

This is an immutable reference algorithm. It is not a proof of native mutable
cells, in-place trails, hash tables, allocation failure handling, or C code.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StoredIdUnification

open StoredIdViews ShapeScopedUnification
open Mettapedia.Logic.LP

variable {α Var Id : Type} [DecidableEq α] [DecidableEq Var]

abbrev Binding (Var Id : Type) := ScopedVar Var × View Var Id

inductive Action (Var Id : Type) where
  | advance (pending : Equations Var Id) (binding : Option (Binding Var Id))
  | conflict
  deriving DecidableEq

def bindAction (reader : Reader α Var Id) (c : ScopedVar Var) (value : View Var Id)
    (rest : Equations Var Id) : Action Var Id :=
  if occurs reader c value then .conflict else
    .advance (substitute c value rest) (some (c, value))

def inspectPair (reader : Reader α Var Id) (p q : View Var Id)
    (rest : Equations Var Id) : Action Var Id :=
  match head reader p, head reader q with
  | .cell c, .cell d => if c = d then .advance rest none else bindAction reader c q rest
  | .cell c, _ => bindAction reader c q rest
  | _, .cell c => bindAction reader c p rest
  | .atom a, .atom b => if a = b then .advance rest none else .conflict
  | .node a b, .node c d => .advance ((a, c) :: (b, d) :: rest) none
  | _, _ => .conflict

inductive Result (Var Id : Type) where
  | solved (bindings : List (Binding Var Id))
  | conflict
  | paused (pending : Equations Var Id) (bindings : List (Binding Var Id))
  deriving DecidableEq

def prepend (binding : Binding Var Id) : Result Var Id → Result Var Id
  | .solved rest => .solved (binding :: rest)
  | .conflict => .conflict
  | .paused pending rest => .paused pending (binding :: rest)

def decorate (binding : Option (Binding Var Id)) (result : Result Var Id) : Result Var Id :=
  match binding with
  | none => result
  | some b => prepend b result

def run (reader : Reader α Var Id) : Nat → Equations Var Id → Result Var Id
  | 0, pending => .paused pending []
  | _ + 1, [] => .solved []
  | fuel + 1, (p, q) :: rest =>
      match inspectPair reader p q rest with
      | .conflict => .conflict
      | .advance pending binding => decorate binding (run reader fuel pending)

def bindingsMeaning (reader : Reader α Var Id) :
    List (Binding Var Id) → Mettapedia.Logic.LP.Subst (signature α Var)
  | [] => Subst.id _
  | (c, value) :: rest => bindingsMeaning reader rest ∘ₛ Subst.single c (meaning reader value)

def solvedMeaning (reader : Reader α Var Id) : Result Var Id →
    Option (Mettapedia.Logic.LP.Subst (signature α Var))
  | .solved bindings => some (bindingsMeaning reader bindings)
  | _ => none

def applyBinding (reader : Reader α Var Id) (binding : Option (Binding Var Id))
    (answer : Mettapedia.Logic.LP.Subst (signature α Var)) :
    Mettapedia.Logic.LP.Subst (signature α Var) :=
  match binding with
  | none => answer
  | some (c, value) => answer ∘ₛ Subst.single c (meaning reader value)

omit [DecidableEq α] in
@[simp] theorem applyBinding_none (reader : Reader α Var Id) : applyBinding reader none = id := rfl

omit [DecidableEq α] in
@[simp] theorem applyBinding_some (reader : Reader α Var Id) (c : ScopedVar Var) (v : View Var Id) :
    applyBinding reader (some (c, v)) = (fun answer => answer ∘ₛ Subst.single c (meaning reader v)) := rfl

omit [DecidableEq α] in
theorem decorate_meaning (reader : Reader α Var Id) (binding : Option (Binding Var Id))
    (result : Result Var Id) :
    solvedMeaning reader (decorate binding result) =
      (solvedMeaning reader result).map (applyBinding reader binding) := by
  cases binding with
  | none => cases result <;> rfl
  | some b => cases b; cases result <;> rfl

theorem pair_decompose (fuel : Nat) (a b c d : LogicTerm α Var)
    (rest : List (LogicTerm α Var × LogicTerm α Var)) :
    unifyFuel (fuel + 1) ((pair a b, pair c d) :: rest) =
      unifyFuel fuel ((a, c) :: (b, d) :: rest) := by
  simp [unifyFuel, pair, finPairsToList, List.finRange_succ]

def stepMeaning (reader : Reader α Var Id) (fuel : Nat) : Action Var Id →
    Option (Mettapedia.Logic.LP.Subst (signature α Var))
  | .conflict => none
  | .advance pending binding =>
      (unifyFuel fuel (readEquations reader pending)).map (applyBinding reader binding)

theorem bindAction_meaning (reader : Reader α Var Id) (fuel : Nat)
    (c : ScopedVar Var) (value : View Var Id) (rest : Equations Var Id) :
    stepMeaning reader fuel (bindAction reader c value rest) =
      if (meaning reader value).occursIn c then none else
        (unifyFuel fuel ((Subst.single c (meaning reader value)).applyEqs
          (readEquations reader rest))).map
          (fun answer => answer ∘ₛ Subst.single c (meaning reader value)) := by
  simp only [bindAction, occurs_correct]
  split <;> simp only [stepMeaning, substitute_correct, applyBinding_some]

/-- A single stored-ID transition matches one tree-unifier transition. -/
theorem inspectPair_refines (reader : Reader α Var Id) (fuel : Nat)
    (p q : View Var Id) (rest : Equations Var Id) :
    unifyFuel (fuel + 1) (readEquations reader ((p, q) :: rest)) =
      stepMeaning reader fuel (inspectPair reader p q rest) := by
  have ep := (head_correct reader p).symm
  have eq := (head_correct reader q).symm
  change unifyFuel (fuel + 1) ((meaning reader p, meaning reader q) :: readEquations reader rest) = _
  cases hp : head reader p with
  | cell c =>
      have ep' : meaning reader p = .var c := by simpa [hp, headMeaning] using ep
      cases hq : head reader q with
      | cell d =>
          have eq' : meaning reader q = .var d := by simpa [hq, headMeaning] using eq
          by_cases same : c = d
          · simp [inspectPair, hp, hq, same, stepMeaning, ep', eq', unifyFuel]
          · simp only [inspectPair, hp, hq, bindAction_meaning, eq',
              Term.occursIn, beq_iff_eq, same, ↓reduceIte, ep', unifyFuel]
            cases unifyFuel fuel ((Subst.single c (.var d)).applyEqs (readEquations reader rest)) <;> rfl
      | atom a =>
          have eq' : meaning reader q = .const a := by simpa [hq, headMeaning] using eq
          simp only [inspectPair, hp, hq, bindAction_meaning, ep', eq', Term.occursIn,
            Bool.false_eq_true, ↓reduceIte, unifyFuel]
          cases unifyFuel fuel ((Subst.single c (.const a)).applyEqs (readEquations reader rest)) <;> rfl
      | node l r =>
          have eq' : meaning reader q = pair (meaning reader l) (meaning reader r) := by
            simpa [hq, headMeaning] using eq
          simp only [inspectPair, hp, hq, bindAction_meaning, ep', eq', pair, unifyFuel]
          split
          · rfl
          · cases unifyFuel fuel ((Subst.single c (.app () ![meaning reader l, meaning reader r])).applyEqs
              (readEquations reader rest)) <;> rfl
  | atom a =>
      have ep' : meaning reader p = .const a := by simpa [hp, headMeaning] using ep
      cases hq : head reader q with
      | cell c =>
          have eq' : meaning reader q = .var c := by simpa [hq, headMeaning] using eq
          simp only [inspectPair, hp, hq, bindAction_meaning, ep', eq', Term.occursIn,
            Bool.false_eq_true, ↓reduceIte, unifyFuel]
          cases unifyFuel fuel ((Subst.single c (.const a)).applyEqs (readEquations reader rest)) <;> rfl
      | atom b =>
          have eq' : meaning reader q = .const b := by simpa [hq, headMeaning] using eq
          by_cases same : a = b <;>
            simp [inspectPair, hp, hq, same, stepMeaning, ep', eq', unifyFuel]
      | node l r =>
          have eq' : meaning reader q = pair (meaning reader l) (meaning reader r) := by
            simpa [hq, headMeaning] using eq
          simp [inspectPair, hp, hq, ep', eq', pair, unifyFuel, stepMeaning]
  | node a b =>
      have ep' : meaning reader p = pair (meaning reader a) (meaning reader b) := by
        simpa [hp, headMeaning] using ep
      cases hq : head reader q with
      | cell c =>
          have eq' : meaning reader q = .var c := by simpa [hq, headMeaning] using eq
          simp only [inspectPair, hp, hq, bindAction_meaning, ep', eq', pair, unifyFuel]
          split
          · rfl
          · cases unifyFuel fuel ((Subst.single c (.app () ![meaning reader a, meaning reader b])).applyEqs
              (readEquations reader rest)) <;> rfl
      | atom c =>
          have eq' : meaning reader q = .const c := by simpa [hq, headMeaning] using eq
          simp [inspectPair, hp, hq, ep', eq', pair, unifyFuel, stepMeaning]
      | node c d =>
          have eq' : meaning reader q = pair (meaning reader c) (meaning reader d) := by
            simpa [hq, headMeaning] using eq
          rw [ep', eq', pair_decompose]
          simp [inspectPair, hp, hq, stepMeaning, readEquations]

/-- The algorithm and oracle are independently recursive; no operational
readback or call to the oracle occurs in `run`. -/
theorem run_refines (reader : Reader α Var Id) (fuel : Nat) (eqs : Equations Var Id) :
    solvedMeaning reader (run reader fuel eqs) = unifyFuel fuel (readEquations reader eqs) := by
  induction fuel generalizing eqs with
  | zero => rfl
  | succ fuel ih =>
      cases eqs with
      | nil => rfl
      | cons eq rest =>
          rcases eq with ⟨p, q⟩
          rw [inspectPair_refines]
          simp only [run]
          cases step : inspectPair reader p q rest with
          | conflict => rfl
          | advance pending binding => rw [decorate_meaning, ih]; rfl

theorem solved_sound (reader : Reader α Var Id) (fuel : Nat) (eqs : Equations Var Id)
    (bindings : List (Binding Var Id)) (success : run reader fuel eqs = .solved bindings) :
    Unifies (bindingsMeaning reader bindings) (readEquations reader eqs) := by
  have oracle := run_refines reader fuel eqs
  rw [success] at oracle
  exact unifyFuel_sound fuel _ _ oracle.symm

theorem solved_mgu (reader : Reader α Var Id) (fuel : Nat) (eqs : Equations Var Id)
    (bindings : List (Binding Var Id)) (success : run reader fuel eqs = .solved bindings)
    (candidate : Mettapedia.Logic.LP.Subst (signature α Var))
    (solves : Unifies candidate (readEquations reader eqs)) :
    (bindingsMeaning reader bindings).moreGeneral candidate := by
  have oracle := run_refines reader fuel eqs
  rw [success] at oracle
  exact unifyFuel_mgu fuel _ _ oracle.symm candidate solves

theorem finite_completeness (reader : Reader α Var Id) (eqs : Equations Var Id)
    (solvable : ∃ θ, Unifies θ (readEquations reader eqs)) :
    ∃ fuel bindings, run reader fuel eqs = .solved bindings := by
  obtain ⟨fuel, θ, accepted⟩ := unifyFuel_exists_of_unifies solvable
  have oracle := run_refines reader fuel eqs
  rw [accepted] at oracle
  cases hr : run reader fuel eqs with
  | conflict => simp [hr, solvedMeaning] at oracle
  | paused pending saved => simp [hr, solvedMeaning] at oracle
  | solved bindings => exact ⟨fuel, bindings, hr⟩

def prependAll (bindings : List (Binding Var Id)) (result : Result Var Id) : Result Var Id :=
  bindings.foldr prepend result

def resume (reader : Reader α Var Id) (fuel : Nat) : Result Var Id → Result Var Id
  | .paused pending saved => prependAll saved (run reader fuel pending)
  | terminal => terminal

theorem resume_prepend (reader : Reader α Var Id) (fuel : Nat) (binding : Binding Var Id)
    (result : Result Var Id) :
    resume reader fuel (prepend binding result) = prepend binding (resume reader fuel result) := by
  cases result <;> rfl

theorem resume_decorate (reader : Reader α Var Id) (fuel : Nat)
    (binding : Option (Binding Var Id)) (result : Result Var Id) :
    resume reader fuel (decorate binding result) = decorate binding (resume reader fuel result) := by
  cases binding with
  | none => rfl
  | some b => exact resume_prepend reader fuel b result

/-- Splitting the allowance preserves the full pending state and answer
binding sequence, not just the final yes/no verdict. -/
theorem run_add (reader : Reader α Var Id) (first second : Nat) (eqs : Equations Var Id) :
    run reader (first + second) eqs = resume reader second (run reader first eqs) := by
  induction first generalizing eqs with
  | zero => simp [run, resume, prependAll]
  | succ first ih =>
      cases eqs with
      | nil => simp [Nat.succ_add, run, resume]
      | cons eq rest =>
          rcases eq with ⟨p, q⟩
          simp only [Nat.succ_add, run]
          cases inspectPair reader p q rest with
          | conflict => rfl
          | advance pending binding =>
              change decorate binding (run reader (first + second) pending) =
                resume reader second (decorate binding (run reader first pending))
              rw [ih, resume_decorate]

theorem solved_persistent (reader : Reader α Var Id) (first extra : Nat)
    (eqs : Equations Var Id) (bindings : List (Binding Var Id))
    (success : run reader first eqs = .solved bindings) :
    run reader (first + extra) eqs = .solved bindings := by
  rw [run_add, success]
  rfl

theorem conflict_persistent (reader : Reader α Var Id) (first extra : Nat)
    (eqs : Equations Var Id) (failed : run reader first eqs = .conflict) :
    run reader (first + extra) eqs = .conflict := by
  rw [run_add, failed]
  rfl

/-- Logical rejection, unlike a pause, proves absence of any finite-term unifier. -/
theorem conflict_sound (reader : Reader α Var Id) (fuel : Nat) (eqs : Equations Var Id)
    (failed : run reader fuel eqs = .conflict) :
    ¬ ∃ θ, Unifies θ (readEquations reader eqs) := by
  intro solvable
  obtain ⟨enough, bindings, success⟩ := finite_completeness reader eqs solvable
  have hf := conflict_persistent reader fuel enough eqs failed
  have hs := solved_persistent reader enough fuel eqs bindings success
  rw [Nat.add_comm] at hf
  rw [hs] at hf
  cases hf

namespace Controls

open StoredIdViews.Controls (reader)

def crossFrame : Equations Nat Nat := [(.stored 0 0, .stored 2 1)]

/-- A variable and a compound term in another frame can meet. -/
theorem cross_frame_succeeds : ∃ fuel bindings, run reader fuel crossFrame = .solved bindings := by
  apply finite_completeness
  let θ : Mettapedia.Logic.LP.Subst (signature Bool Nat) :=
    fun c => if c.scope = 0 then pair (.var ⟨1, 0⟩) (.const false) else .var c
  refine ⟨θ, ?_⟩
  intro equation member
  simp only [readEquations, crossFrame, List.map_cons, List.map_nil, List.mem_singleton] at member
  subst equation
  change θ.applyTerm (.var ⟨0, 0⟩) = θ.applyTerm (pair (.var ⟨1, 0⟩) (.const false))
  rw [apply_pair]
  rfl

/-- Zero allowance retains the input; it does not claim conflict. -/
example : run reader 0 crossFrame = .paused crossFrame [] := rfl
example : resume reader 7 (run reader 2 crossFrame) = run reader 9 crossFrame :=
  (run_add reader 2 7 crossFrame).symm

end Controls

#print axioms run_refines
#print axioms solved_sound
#print axioms solved_mgu
#print axioms finite_completeness
#print axioms run_add
#print axioms conflict_sound

end Mettapedia.Machines.StoredIdUnification
