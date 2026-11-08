import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeRelation
import Mettapedia.Logic.LP.TotalUnification

/-!
# Executable satisfiability of type equations

Type equations use the existing total first-order unifier. The codec preserves
substitution, and a successful unifier is grounded to a solution of `Sat`.
This supplies a decision procedure for the existing relation, not a second
notion of type consistency.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeEquationSolver

open Mettapedia.Logic.LP (LPSignature Term Subst unifyTotal)

abbrev signature (V : Type) : LPSignature where
  constants := String
  vars := V
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Nat
  functionArity := id

def encode {V : Type} : Ty V → Term (signature V)
  | .var name => .var name
  | .sym name => .const name
  | .app children => .app (f := (children.length : Nat)) (fun index => encode (children.get index))
termination_by type => sizeOf type
decreasing_by
  have := List.sizeOf_lt_of_mem (List.get_mem children index)
  simp only [Ty.app.sizeOf_spec]
  omega

def decode {V : Type} : Term (signature V) → Ty V
  | .var name => .var name
  | .const name => .sym name
  | .app _ children => .app (List.ofFn fun index => decode (children index))

@[simp] theorem decode_encode {V : Type} (type : Ty V) : decode (encode type) = type := by
  cases type with
  | var name => rw [encode]; rfl
  | sym name => rw [encode]; rfl
  | app children =>
    rw [encode]
    simp only [decode, Ty.app.injEq]
    apply List.ext_getElem
    · simp
    · intro index before after
      simp only [List.getElem_ofFn]
      exact decode_encode children[index]
termination_by sizeOf type
decreasing_by
  have := List.sizeOf_lt_of_mem (List.getElem_mem after)
  simp only [Ty.app.sizeOf_spec]
  omega

@[simp] theorem encode_decode {V : Type} (term : Term (signature V)) : encode (decode term) = term := by
  induction term with
  | var name => rw [decode, encode]
  | const name => rw [decode, encode]
  | app arity children ih =>
    simp only [decode, encode]
    have appExt : ∀ (n m : Nat) (same : n = m)
        (left : Fin n → Term (signature V)) (right : Fin m → Term (signature V)),
        (∀ i, left i = right (i.cast same)) →
          Term.app (σ := signature V) n left = Term.app (σ := signature V) m right := by
      intro n m same left right pointwise
      subst m
      exact congrArg (Term.app (σ := signature V) n) (funext pointwise)
    apply appExt _ _ (List.length_ofFn)
    intro index
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact ih _

theorem decode_apply {V : Type} (assignment : Subst (signature V)) (type : Ty V) :
    decode (assignment.applyTerm (encode type)) = type.bind (fun name => decode (assignment name)) := by
  cases type with
  | var name => rw [encode]; rfl
  | sym name => rw [encode]; rfl
  | app children =>
    rw [encode]
    simp only [Subst.applyTerm, decode, Ty.bind_app, Ty.app.injEq]
    apply List.ext_getElem
    · simp
    · intro index before after
      have valid : index < children.length := by simpa using after
      simp only [List.getElem_ofFn, List.getElem_map]
      exact decode_apply assignment (children.get ⟨index, valid⟩)
termination_by sizeOf type
decreasing_by
  have := List.sizeOf_lt_of_mem (List.get_mem children ⟨index, valid⟩)
  simp only [Ty.app.sizeOf_spec]
  omega

theorem encode_bind {V : Type} (assignment : V → Ty V) (type : Ty V) :
    encode (type.bind assignment) =
      Subst.applyTerm (fun name => encode (assignment name) : Subst (signature V)) (encode type) := by
  have decoded := decode_apply (fun name => encode (assignment name)) type
  simp only [decode_encode] at decoded
  exact (congrArg encode decoded).symm.trans (by simp)

def equations {V : Type} (store : List (Eqn V)) : List (Term (signature V) × Term (signature V)) :=
  store.map fun pair => (encode pair.1, encode pair.2)

/-- Grounding residual variables of a successful finite unifier supplies the
closed valuation required by the original type relation. -/
theorem sat_of_unifies {V : Type} (store : List (Eqn V)) (assignment : Subst (signature V))
    (solved : Mettapedia.Logic.LP.Unifies assignment (equations store)) : Sat store := by
  let close : V → Ty Empty := fun _ => .sym "Type"
  refine ⟨fun name => (decode (assignment name)).bind close, ?_⟩
  intro equation member
  have pair := solved (encode equation.1, encode equation.2)
    (List.mem_map.mpr ⟨equation, member, rfl⟩)
  have decoded := congrArg decode pair
  rw [decode_apply, decode_apply] at decoded
  simpa only [Ty.bind_bind] using congrArg (fun type => type.bind close) decoded

theorem unifies_of_sat {V : Type} (store : List (Eqn V)) (sat : Sat store) :
    ∃ assignment : Subst (signature V), Mettapedia.Logic.LP.Unifies assignment (equations store) := by
  obtain ⟨solution, solved⟩ := sat
  let lifted : V → Ty V := fun name => (solution name).lift
  refine ⟨fun name => encode (lifted name), ?_⟩
  intro equation member
  obtain ⟨pair, belongs, rfl⟩ := List.mem_map.mp member
  have same := congrArg (fun type : Ty Empty => (type.lift : Ty V)) (solved pair belongs)
  have translated : pair.1.bind lifted = pair.2.bind lifted := by
    simpa only [lifted, Ty.lift, Ty.map, Ty.bind_bind] using same
  simpa only [encode_bind] using congrArg encode translated

def check {V : Type} [DecidableEq V] (store : List (Eqn V)) : Bool :=
  (unifyTotal (equations store)).isSome

theorem check_iff_sat {V : Type} [DecidableEq V] (store : List (Eqn V)) :
    check store = true ↔ Sat store := by
  constructor
  · intro accepted
    obtain ⟨assignment, found⟩ := Option.isSome_iff_exists.mp accepted
    exact sat_of_unifies store assignment (Mettapedia.Logic.LP.unifyTotal_sound _ _ found)
  · intro sat
    obtain ⟨assignment, solved⟩ := unifies_of_sat store sat
    obtain ⟨result, found⟩ := Mettapedia.Logic.LP.unifyTotal_complete
      (equations := equations store) ⟨assignment, solved⟩
    simp [check, found]

open Classical in
theorem check_eq_decide {V : Type} [DecidableEq V] (store : List (Eqn V)) :
    check store = decide (Sat store) := by
  apply Bool.eq_iff_iff.mpr
  simp only [check_iff_sat, decide_eq_true_eq]

/-- Renaming into a fresh type-variable namespace preserves the executable
decision. Non-injective renamings are deliberately not admitted. -/
theorem check_injective_rename {V W : Type} [DecidableEq V] [DecidableEq W]
    (rename : V → W) (injective : Function.Injective rename) (store : List (Eqn V)) :
    check (store.map (Eqn.map rename)) = check store := by
  apply Bool.eq_iff_iff.mpr
  rw [check_iff_sat, check_iff_sat, sat_map_injective injective]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeEquationSolver
