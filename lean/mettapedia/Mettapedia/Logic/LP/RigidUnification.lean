import Mettapedia.Logic.LP.TotalUnification

/-!
# Unification with protected variables

A protected variable is encoded as a fresh constant, while an unprotected
variable stays a variable. The existing total first-order unifier therefore
solves a whole constraint batch under one protection environment. Decoding the
answer yields ordinary LP substitutions that fix every protected identity.

This construction specifies finite first-order terms. It neither implements
waiting nor licenses changing scoped eigenvariables or higher-order binders.
-/

namespace Mettapedia.Logic.LP.RigidUnification

universe u v

variable {σ : LPSignature.{u, u, v, u}}

/-- Rigid variables are distinct from the signature's existing constants. -/
abbrev signature (σ : LPSignature.{u, u, v, u}) (rigid : σ.vars → Prop) :
    LPSignature.{u, u, v, u} :=
  { constants := σ.constants ⊕ {v : σ.vars // rigid v}
    vars := {v : σ.vars // ¬rigid v}
    relationSymbols := σ.relationSymbols
    relationArity := σ.relationArity
    functionSymbols := σ.functionSymbols
    functionArity := σ.functionArity }

def encode (rigid : σ.vars → Prop) [DecidablePred rigid] :
    Term σ → Term (signature σ rigid)
  | .var v => if h : rigid v then .const (.inr ⟨v, h⟩) else .var ⟨v, h⟩
  | .const c => .const (.inl c)
  | .app f args => .app f (fun i => encode rigid (args i))

def decode (rigid : σ.vars → Prop) : Term (signature σ rigid) → Term σ
  | .var v => .var v.1
  | .const (.inl c) => .const c
  | .const (.inr v) => .var v.1
  | .app f args => .app f (fun i => decode rigid (args i))

@[simp] theorem decode_encode (rigid : σ.vars → Prop) [DecidablePred rigid]
    (term : Term σ) : decode rigid (encode rigid term) = term := by
  induction term with
  | var v => by_cases h : rigid v <;> simp [encode, decode, h]
  | const c => rfl
  | app f args ih => simp only [encode, decode]; congr 1; funext i; exact ih i

@[simp] theorem encode_decode (rigid : σ.vars → Prop) [DecidablePred rigid]
    (term : Term (signature σ rigid)) : encode rigid (decode rigid term) = term := by
  induction term with
  | var v => simp [decode, encode, v.property]
  | const c =>
    cases c with
    | inl c => rfl
    | inr v => simp [decode, encode, v.property]
  | app f args ih => simp only [encode, decode]; congr 1; funext i; exact ih i

/-- Permission requirement for an answer substitution. -/
def Fixes (rigid : σ.vars → Prop) (substitution : Subst σ) : Prop :=
  ∀ v, rigid v → substitution v = .var v

def liftSubst (rigid : σ.vars → Prop) [DecidablePred rigid]
    (substitution : Subst σ) : Subst (signature σ rigid) :=
  fun v => encode rigid (substitution v.1)

def projectSubst (rigid : σ.vars → Prop) [DecidablePred rigid]
    (substitution : Subst (signature σ rigid)) : Subst σ :=
  fun v => if h : rigid v then .var v else decode rigid (substitution ⟨v, h⟩)

theorem projectSubst_fixes (rigid : σ.vars → Prop) [DecidablePred rigid]
    (substitution : Subst (signature σ rigid)) :
    Fixes rigid (projectSubst rigid substitution) := by
  intro v h
  simp [projectSubst, h]

theorem encode_applyTerm (rigid : σ.vars → Prop) [DecidablePred rigid]
    (substitution : Subst σ) (fixed : Fixes rigid substitution) (term : Term σ) :
    encode rigid (substitution.applyTerm term) =
      (liftSubst rigid substitution).applyTerm (encode rigid term) := by
  induction term with
  | var v =>
    by_cases h : rigid v
    · simp [Subst.applyTerm, encode, fixed v h, h]
    · simp [Subst.applyTerm, encode, liftSubst, h]
  | const c => rfl
  | app f args ih =>
    simp only [Subst.applyTerm, encode]
    congr 1
    funext i
    exact ih i

theorem decode_applyTerm (rigid : σ.vars → Prop) [DecidablePred rigid]
    (substitution : Subst (signature σ rigid))
    (term : Term (signature σ rigid)) :
    decode rigid (substitution.applyTerm term) =
      (projectSubst rigid substitution).applyTerm (decode rigid term) := by
  induction term with
  | var v => simp [Subst.applyTerm, decode, projectSubst, v.property]
  | const c =>
    cases c with
    | inl c => rfl
    | inr v => simp [Subst.applyTerm, decode, projectSubst, v.property]
  | app f args ih =>
    simp only [Subst.applyTerm, decode]
    congr 1
    funext i
    exact ih i

@[simp] theorem project_lift (rigid : σ.vars → Prop) [DecidablePred rigid]
    (substitution : Subst σ) (fixed : Fixes rigid substitution) :
    projectSubst rigid (liftSubst rigid substitution) = substitution := by
  funext v
  by_cases h : rigid v
  · simp [projectSubst, h, fixed v h]
  · simp [projectSubst, liftSubst, h]

theorem project_comp (rigid : σ.vars → Prop) [DecidablePred rigid]
    (first second : Subst (signature σ rigid)) :
    projectSubst rigid (first ∘ₛ second) =
      projectSubst rigid first ∘ₛ projectSubst rigid second := by
  funext v
  by_cases h : rigid v
  · simp [projectSubst, Subst.comp, h]
  · simp [projectSubst, Subst.comp, h, decode_applyTerm]

def encodeEqs (rigid : σ.vars → Prop) [DecidablePred rigid]
    (equations : List (Term σ × Term σ)) :
    List (Term (signature σ rigid) × Term (signature σ rigid)) :=
  equations.map fun pair => (encode rigid pair.1, encode rigid pair.2)

theorem lift_unifies (rigid : σ.vars → Prop) [DecidablePred rigid]
    (equations : List (Term σ × Term σ)) (substitution : Subst σ)
    (fixed : Fixes rigid substitution) (unifies : Unifies substitution equations) :
    Unifies (liftSubst rigid substitution) (encodeEqs rigid equations) := by
  rintro pair hp
  obtain ⟨⟨left, right⟩, present, rfl⟩ := List.mem_map.mp hp
  dsimp only
  rw [← encode_applyTerm rigid substitution fixed,
      ← encode_applyTerm rigid substitution fixed]
  exact congrArg (encode rigid) (unifies (left, right) present)

theorem project_unifies (rigid : σ.vars → Prop) [DecidablePred rigid]
    (equations : List (Term σ × Term σ))
    (substitution : Subst (signature σ rigid))
    (unifies : Unifies substitution (encodeEqs rigid equations)) :
    Unifies (projectSubst rigid substitution) equations := by
  rintro ⟨left, right⟩ present
  have h := unifies (encode rigid left, encode rigid right)
    (List.mem_map.mpr ⟨(left, right), present, rfl⟩)
  have hd := congrArg (decode rigid) h
  simpa only [decode_applyTerm, decode_encode] using hd

/-- A total solver for finite constraints with a fixed protection environment. -/
def solve (rigid : σ.vars → Prop) [DecidablePred rigid] [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (equations : List (Term σ × Term σ)) : Option (Subst σ) :=
  (unifyTotal (encodeEqs rigid equations)).map (projectSubst rigid)

theorem solve_sound (rigid : σ.vars → Prop) [DecidablePred rigid]
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (equations : List (Term σ × Term σ)) (substitution : Subst σ)
    (accepted : solve rigid equations = some substitution) :
    Fixes rigid substitution ∧ Unifies substitution equations := by
  unfold solve at accepted
  obtain ⟨encoded, success, rfl⟩ := Option.map_eq_some_iff.mp accepted
  exact ⟨projectSubst_fixes rigid encoded,
    project_unifies rigid equations encoded
      (unifyTotal_sound (encodeEqs rigid equations) encoded success)⟩

theorem solve_complete (rigid : σ.vars → Prop) [DecidablePred rigid]
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (equations : List (Term σ × Term σ))
    (solvable : ∃ substitution, Fixes rigid substitution ∧ Unifies substitution equations) :
    ∃ substitution, solve rigid equations = some substitution := by
  obtain ⟨substitution, fixed, unifies⟩ := solvable
  obtain ⟨encoded, success⟩ := unifyTotal_complete
    ⟨liftSubst rigid substitution, lift_unifies rigid equations substitution fixed unifies⟩
  exact ⟨projectSubst rigid encoded, by simp [solve, success]⟩

theorem solve_none_iff (rigid : σ.vars → Prop) [DecidablePred rigid]
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (equations : List (Term σ × Term σ)) :
    solve rigid equations = none ↔
      ¬∃ substitution, Fixes rigid substitution ∧ Unifies substitution equations := by
  constructor
  · intro rejected solvable
    obtain ⟨substitution, accepted⟩ := solve_complete rigid equations solvable
    simp [rejected] at accepted
  · intro impossible
    cases h : solve rigid equations with
    | none => rfl
    | some substitution => exact False.elim (impossible
        ⟨substitution, solve_sound rigid equations substitution h⟩)

/-- Every permitted solution factors through the returned answer using another
    substitution that also fixes the protected variables. -/
theorem solve_mgu (rigid : σ.vars → Prop) [DecidablePred rigid]
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (equations : List (Term σ × Term σ)) (answer candidate : Subst σ)
    (accepted : solve rigid equations = some answer)
    (fixed : Fixes rigid candidate) (unifies : Unifies candidate equations) :
    ∃ factor, Fixes rigid factor ∧ candidate = factor ∘ₛ answer := by
  unfold solve at accepted
  obtain ⟨encoded, success, rfl⟩ := Option.map_eq_some_iff.mp accepted
  obtain ⟨factor, factors⟩ := unifyTotal_mgu (encodeEqs rigid equations) encoded success
    (liftSubst rigid candidate) (lift_unifies rigid equations candidate fixed unifies)
  refine ⟨projectSubst rigid factor, projectSubst_fixes rigid factor, ?_⟩
  have h := congrArg (projectSubst rigid)
    (show liftSubst rigid candidate = factor ∘ₛ encoded from funext factors)
  simpa only [project_lift rigid candidate fixed, project_comp] using h

end Mettapedia.Logic.LP.RigidUnification
