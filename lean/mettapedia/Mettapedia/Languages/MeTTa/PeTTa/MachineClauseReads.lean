import Mettapedia.Languages.MeTTa.PeTTa.AtomFreshNamespaces
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingDisequality

/-!
# Joint matching of the machine's clause head and body

The machine stores `(pm:clause F INDEX HEAD BODY)` as one row. Its parameters
are opened together before matching: independently opening the head and body
would lose their shared variables. This module joins that concrete row syntax
to the model's computed unifier, principal substitutions and retained negative
information. The caller and the clause may both contain unknowns.

These are matching-boundary laws, not the complete machine simulation or a
proof that a native Space implements schematic-row activation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MachineClauseReads

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation (presentation)
open ListView Unifying UnifyingDisequality LibTransformStep

def row (function index head body : Atom) : Atom :=
  .expression [.symbol "pm:clause", function, index, head, body]

def head (arguments : Atom) : Atom := .expression [.symbol "pm:head", arguments]

theorem instantiate_row (valuation : Valuation) (function index pattern body : Atom) :
    instantiate valuation (row function index pattern body) =
      row (instantiate valuation function) (instantiate valuation index)
        (instantiate valuation pattern) (instantiate valuation body) := rfl

/-- A joint match retains every field and their variable correlations. -/
theorem equation_fields (valuation : Valuation)
    (function index pattern body called selected arguments output : Atom) :
    EquationHolds valuation (row function index pattern body,
      row called selected (head arguments) output) ↔
      instantiate valuation function = instantiate valuation called ∧
      instantiate valuation index = instantiate valuation selected ∧
      instantiate valuation pattern = head (instantiate valuation arguments) ∧
      instantiate valuation body = instantiate valuation output := by
  simp [EquationHolds, head, row, instantiate, instantiate.instantiateList]

theorem rename_row (scope : Nat) (function index pattern body : Atom) :
    LibTransformStep.rename scope (row function index pattern body) =
      row (LibTransformStep.rename scope function) (LibTransformStep.rename scope index)
        (LibTransformStep.rename scope pattern) (LibTransformStep.rename scope body) := rfl

/-- The successful computed answer presents precisely the incoming solutions
that jointly match the selected clause and the caller's result variable. -/
theorem read_solutions {bindings bound : Subst}
    {function index pattern body called selected arguments output : Atom}
    (valid : Idempotent bindings)
    (unified : unifyBinding bindings (GSLTBindingPatterns.quoted (row function index pattern body))
      (row called selected (head arguments) output) = .ok bound) :
    SolutionsOf EquationHolds (presentation bound) =
      SolutionsOf EquationHolds (presentation bindings) ∩
        {valuation |
          instantiate valuation function = instantiate valuation called ∧
          instantiate valuation index = instantiate valuation selected ∧
          instantiate valuation pattern = head (instantiate valuation arguments) ∧
          instantiate valuation body = instantiate valuation output} := by
  rw [unifyBinding_quoted_means valid unified]
  ext valuation
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, equation_fields]

/-- The actual computed result factors every independent solution of the
joint row equation, including its open body and the caller's old bindings. -/
theorem read_principal {bindings bound : Subst}
    {clause query : Atom} (valid : Idempotent bindings)
    (unified : unifyBinding bindings (GSLTBindingPatterns.quoted clause) query = .ok bound) :
    atomAction.Principal (presentation bindings ++ [(clause, query)]) (solved bound) :=
  quoted_principal valid unified

theorem read_preserves_apart {bindings bound : Subst} {clause query : Atom}
    (frame : Disequality.Frame atomAction) (valid : Idempotent bindings)
    (unified : unifyBinding bindings (GSLTBindingPatterns.quoted clause) query = .ok bound) :
    (Disequality.frames atomAction).Solvable (a := frame)
      (presentation bindings ++ [(clause, query)]) ↔
      Disequality.Separates atomAction (solved bound) frame.1 :=
  quoted_frame_solvable frame valid unified

end Mettapedia.Languages.MeTTa.PeTTa.MachineClauseReads
