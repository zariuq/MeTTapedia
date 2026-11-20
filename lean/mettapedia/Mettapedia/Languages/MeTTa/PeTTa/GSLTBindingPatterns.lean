import Mettapedia.Languages.MeTTa.PeTTa.GSLTDataPatterns

/-!
# Literal binding patterns for compiled source data

A quoted binding pattern uses the existing term unifier, rather than reading
source constructor names as target operations. Its solution law covers open
values and retains the incoming substitution. Complete spine packets can be
checked and converted to this representation before execution.

These are pattern-boundary laws. Text emission, runtime conformance and whole
rule compilation remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.GSLTBindingPatterns

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst atomFreeVars)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation (presentation)
open ListView Unifying

/-- Literal syntax at a binding boundary, including scalar or variable syntax. -/
def quoted (source : Atom) : Atom := .expression [.symbol "quote", source]

/-- Convert a complete data-spine packet. Open tails and computed patterns
are not packets of this codec and retain their separate interpretation. -/
def checked (view : String) (native : Atom) : Option Atom :=
  (GSLTDataPatterns.decode view native).map quoted

theorem checked_encode (view : String) (source : Atom) :
    checked view (GSLTDataPatterns.encode view source) = some (quoted source) := by
  simp [checked, GSLTDataPatterns.decode_encode]

/-- An accepted independently supplied packet determines its source exactly. -/
theorem checked_reflects {view : String} {native pattern : Atom}
    (accepted : checked view native = some pattern) :
    ∃ source, GSLTDataPatterns.encode view source = native ∧ pattern = quoted source := by
  unfold checked at accepted
  cases read : GSLTDataPatterns.decode view native with
  | none => simp [read] at accepted
  | some source =>
      refine ⟨source, GSLTDataPatterns.encode_decode view native source read, ?_⟩
      simpa only [read, Option.map_some, Option.some.injEq] using accepted.symm

theorem quoted_variables (source : Atom) :
    atomFreeVars (quoted source) = atomFreeVars source := by
  simp [quoted, atomFreeVars, atomFreeVars.atomFreeVarsList]

theorem checked_variables {view : String} {native pattern : Atom}
    (accepted : checked view native = some pattern) :
    atomFreeVars pattern = atomFreeVars native := by
  obtain ⟨source, encoded, rfl⟩ := checked_reflects accepted
  rw [← encoded, quoted_variables, GSLTDataPatterns.freeVars_encode]

/-- Substitution acts on the data, leaving the quotation boundary intact. -/
theorem quoted_instantiate (valuation : Valuation) (source : Atom) :
    instantiate valuation (quoted source) = quoted (instantiate valuation source) := by
  simp [quoted, instantiate, instantiate.instantiateList]

/-- Every successful target binding has exactly the source data solutions.
The value may contain unknowns; the initial equations are preserved. -/
theorem quoted_means {bindings bound : Subst} {source value : Atom}
    (valid : Idempotent bindings)
    (unified : unifyBinding bindings (quoted source) value = .ok bound) :
    SolutionsOf EquationHolds (presentation bound) =
      SolutionsOf EquationHolds (presentation bindings) ∩
        {valuation | PatternHolds valuation (GSLTDataPatterns.encode "cons" source) value} := by
  rw [unifyBinding_quoted_means valid unified]
  ext valuation
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, GSLTDataPatterns.patternHolds_iff,
    EquationHolds]

/-- Acceptance is equivalent to the existence of a compatible source
valuation, including repeated variables and open returned values. -/
theorem quoted_accepts_iff (bindings : Subst) (source value : Atom)
    (valid : Idempotent bindings) :
    (∃ bound, unifyBinding bindings (quoted source) value = .ok bound) ↔
      (SolutionsOf EquationHolds (presentation bindings) ∩
        {valuation | PatternHolds valuation (GSLTDataPatterns.encode "cons" source) value}).Nonempty := by
  constructor
  · rintro ⟨bound, unified⟩
    rw [← quoted_means valid unified]
    have boundValid := (unifyBinding_refines bindings bound (quoted source) value valid unified).1
    exact unifierReading.frame_satisfiable ⟨bound, boundValid⟩
  · intro solvable
    cases result : unifyBinding bindings (quoted source) value with
    | ok bound => exact ⟨bound, rfl⟩
    | clash =>
        obtain ⟨valuation, initial, holds⟩ := solvable
        have clashed : unifyTerms (fuelFor bindings source value) bindings source value = .clash :=
          result
        exact (terms_clash _ valid clashed valuation initial
          ((GSLTDataPatterns.patternHolds_iff valuation source value).mp holds)).elim
    | exhausted =>
        exact absurd result (unify_decides bindings source value valid)

theorem checked_means {view : String} {native pattern source value : Atom}
    {bindings bound : Subst}
    (read : GSLTDataPatterns.decode view native = some source)
    (accepted : checked view native = some pattern)
    (valid : Idempotent bindings)
    (unified : unifyBinding bindings pattern value = .ok bound) :
    SolutionsOf EquationHolds (presentation bound) =
      SolutionsOf EquationHolds (presentation bindings) ∩
        {valuation | PatternHolds valuation (GSLTDataPatterns.encode "cons" source) value} := by
  have exactPattern : pattern = quoted source := by
    simpa only [checked, read, Option.map_some, Option.some.injEq] using accepted.symm
  subst pattern
  exact quoted_means valid unified

end Mettapedia.Languages.MeTTa.PeTTa.GSLTBindingPatterns
