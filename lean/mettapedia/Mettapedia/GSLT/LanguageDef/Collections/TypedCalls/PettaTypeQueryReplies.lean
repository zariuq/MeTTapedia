import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeServices
import Mettapedia.Logic.LP.ConjunctiveUnification

/-!
# Most-general reply schemes earned by ordered type derivations

Each reply is computed from one actual derivation by the existing total
unifier. Its ground instances are exactly the closed types realized by that
derivation. The ordered family does not drop a satisfiable derivation.
Fresh source allocation and caller-record delivery are subsequent boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypeQueryReplies

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Logic.LP (Term Subst unifyTotal)
open TypeEquationSolver (signature encode decode equations)

def Realizes (derivation : Deriv) (type : Ty Empty) : Prop :=
  ∃ assignment : DVar → Ty Empty,
    Solves assignment derivation.eqs ∧ derivation.ty.bind assignment = type

def solve (derivation : Deriv) : Option (Ty DVar) :=
  (unifyTotal (equations derivation.eqs)).map fun assignment =>
    decode (assignment.applyTerm (encode derivation.ty))

theorem decode_substitution (assignment : Subst (signature DVar)) (term : Term (signature DVar)) :
    decode (assignment.applyTerm term) =
      (decode term).bind (fun name => decode (assignment name)) := by
  simpa only [TypeEquationSolver.encode_decode] using
    TypeEquationSolver.decode_apply assignment (decode term)

theorem closed_assignment_unifies (store : List (Eqn DVar)) (assignment : DVar → Ty Empty)
    (solved : Solves assignment store) :
    Mettapedia.Logic.LP.Unifies (fun name => encode ((assignment name).lift : Ty DVar))
      (equations store) := by
  intro equation member
  obtain ⟨pair, belongs, rfl⟩ := List.mem_map.mp member
  have lifted := congrArg (fun type : Ty Empty => (type.lift : Ty DVar)) (solved pair belongs)
  have same : pair.1.bind (fun name => ((assignment name).lift : Ty DVar)) =
      pair.2.bind (fun name => ((assignment name).lift : Ty DVar)) := by
    simpa only [Ty.lift, Ty.map, Ty.bind_bind] using lifted
  simpa only [TypeEquationSolver.encode_bind] using congrArg encode same

theorem solution_instances_realize (derivation : Deriv) (assignment : Subst (signature DVar))
    (accepted : unifyTotal (equations derivation.eqs) = some assignment)
    (after : DVar → Ty Empty) :
    Realizes derivation ((decode (assignment.applyTerm (encode derivation.ty))).bind after) := by
  refine ⟨fun name => (decode (assignment name)).bind after, ?_, ?_⟩
  · intro equation member
    have same := Mettapedia.Logic.LP.unifyTotal_sound _ _ accepted
      (encode equation.1, encode equation.2) (List.mem_map.mpr ⟨equation, member, rfl⟩)
    have decoded := congrArg decode same
    rw [TypeEquationSolver.decode_apply, TypeEquationSolver.decode_apply] at decoded
    simpa only [Ty.bind_bind] using congrArg (fun type => type.bind after) decoded
  · rw [TypeEquationSolver.decode_apply, Ty.bind_bind]

theorem realization_is_solution_instance (derivation : Deriv) (assignment : Subst (signature DVar))
    (accepted : unifyTotal (equations derivation.eqs) = some assignment)
    (type : Ty Empty) (realized : Realizes derivation type) :
    ∃ after : DVar → Ty Empty,
      (decode (assignment.applyTerm (encode derivation.ty))).bind after = type := by
  obtain ⟨source, solved, result⟩ := realized
  let candidate : Subst (signature DVar) := fun name => encode ((source name).lift : Ty DVar)
  have candidateSolves : Mettapedia.Logic.LP.Unifies candidate (equations derivation.eqs) :=
    closed_assignment_unifies derivation.eqs source solved
  obtain ⟨post, factor⟩ := Mettapedia.Logic.LP.unifyTotal_mgu _ _ accepted candidate candidateSolves
  have sameFunctions : candidate = Subst.comp post assignment := funext factor
  let close : DVar → Ty Empty := fun _ => .sym "Type"
  refine ⟨fun name => (decode (post name)).bind close, ?_⟩
  have evaluated : post.applyTerm (assignment.applyTerm (encode derivation.ty)) =
      encode (type.lift : Ty DVar) := by
    rw [← Subst.applyTerm_comp, ← sameFunctions]
    change Subst.applyTerm (fun name => encode ((source name).lift : Ty DVar)) _ = _
    rw [← TypeEquationSolver.encode_bind]
    congr 1
    simpa only [Ty.lift, Ty.map, Ty.bind_bind] using
      congrArg (fun value : Ty Empty => (value.lift : Ty DVar)) result
  have decoded := congrArg decode evaluated
  rw [decode_substitution, TypeEquationSolver.decode_encode] at decoded
  have grounded := congrArg (fun value => value.bind close) decoded
  simpa only [Ty.bind_bind, Ty.lift_bind_ground] using grounded

/-- This is a most-general scheme theorem, not a guessed output type. -/
theorem solve_exact (derivation : Deriv) (scheme : Ty DVar)
    (computed : solve derivation = some scheme) (type : Ty Empty) :
    Realizes derivation type ↔ ∃ after : DVar → Ty Empty, scheme.bind after = type := by
  obtain ⟨assignment, accepted, rfl⟩ := Option.map_eq_some_iff.mp computed
  constructor
  · exact realization_is_solution_instance derivation assignment accepted type
  · rintro ⟨after, rfl⟩
    exact solution_instances_realize derivation assignment accepted after

theorem solve_exists (derivation : Deriv) (satisfiable : Sat derivation.eqs) :
    ∃ scheme, solve derivation = some scheme := by
  obtain ⟨assignment, unifies⟩ := TypeEquationSolver.unifies_of_sat derivation.eqs satisfiable
  obtain ⟨result, accepted⟩ := Mettapedia.Logic.LP.unifyTotal_complete ⟨assignment, unifies⟩
  exact ⟨decode (result.applyTerm (encode derivation.ty)), by simp [solve, accepted]⟩

def solveAll : List Deriv → Option (List (Ty DVar))
  | [] => some []
  | derivation :: rest => do
      let scheme ← solve derivation
      let schemes ← solveAll rest
      pure (scheme :: schemes)

theorem solveAll_exists (derivations : List Deriv)
    (satisfiable : ∀ derivation ∈ derivations, Sat derivation.eqs) :
    ∃ schemes, solveAll derivations = some schemes := by
  induction derivations with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
    obtain ⟨scheme, one⟩ := solve_exists first (satisfiable first (by simp))
    obtain ⟨schemes, more⟩ := ih fun derivation member => satisfiable derivation (List.mem_cons_of_mem _ member)
    exact ⟨scheme :: schemes, by simp [solveAll, one, more]⟩

/-- The reply at every list position comes from that same derivation
occurrence. Equal schemes are not deduplicated. -/
theorem solveAll_order (derivations : List Deriv) (schemes : List (Ty DVar))
    (computed : solveAll derivations = some schemes) :
    List.Forall₂ (fun derivation scheme => solve derivation = some scheme) derivations schemes := by
  induction derivations generalizing schemes with
  | nil =>
    have empty : schemes = [] := Option.some.inj computed |>.symm
    subst schemes
    exact .nil
  | cons first rest ih =>
    cases one : solve first with
    | none => simp [solveAll, one] at computed
    | some scheme =>
      cases more : solveAll rest with
      | none => simp [solveAll, one, more] at computed
      | some tail =>
        have same : schemes = scheme :: tail := by simpa [solveAll, one, more] using computed.symm
        subst schemes
        exact .cons one (ih tail more)

theorem solveAll_length (derivations : List Deriv) (schemes : List (Ty DVar))
    (computed : solveAll derivations = some schemes) : schemes.length = derivations.length :=
  (solveAll_order derivations schemes computed).length_eq.symm

theorem inferred_derivations_satisfiable (declarations : Decls) (value : Atom) :
    ∀ derivation ∈ OrderedTypeRelation.effective (OrderedTypeRelation.infer declarations value),
      Sat derivation.eqs := by
  intro derivation member
  have erased : derivation ∈ eff (info declarations value) := by
    rw [← OrderedTypeRelation.infer_erases declarations value, ← OrderedTypeRelation.effective_erases]
    exact member
  exact eff_sat (cands_sat declarations value) derivation erased

def inferred (declarations : Decls) (value : Atom) : Option (List (Ty DVar)) :=
  solveAll (OrderedTypeRelation.effective (OrderedTypeRelation.infer declarations value))

theorem inferred_exists (declarations : Decls) (value : Atom) :
    ∃ schemes, inferred declarations value = some schemes :=
  solveAll_exists _ (inferred_derivations_satisfiable declarations value)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypeQueryReplies
