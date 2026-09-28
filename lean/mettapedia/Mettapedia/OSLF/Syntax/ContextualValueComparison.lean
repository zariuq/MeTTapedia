import Mathlib.Data.List.GetD
import Mettapedia.OSLF.Syntax.ContextSubstitutionComparison
import Mettapedia.OSLF.MeTTaIL.RuleBinding

/-!
# Typed values at executable rule occurrences

The pattern signature has one sort, so this comparison concerns binding scope
and occurrence substitution; it does not discharge an authored language's
many-sorted typing obligations. A declared dependency list still determines the
exact prefix length, and the ambient segment is kept separate from it.
-/

namespace Mettapedia.OSLF.Binding.PatternPresentation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding

set_option autoImplicit false

/-- Erase a vector of typed occurrence arguments without reordering it. -/
def rawArguments {dependencies ambient depth : Nat}
    (arguments : Fin dependencies →
      Term patSig (ctxOf (depth + ambient)) PatSrt.pat) : List Pattern :=
  List.ofFn fun i => erase (arguments i)

/-- The typed substitution selected by a dependency spine. Dependencies read
the supplied arguments; ambient variables retain their positions below the
newly opened local binders. -/
def occurrenceSub (dependencies ambient depth : Nat)
    (arguments : Fin dependencies →
      Term patSig (ctxOf (depth + ambient)) PatSrt.pat) :
    Sub patSig (ctxOf (dependencies + ambient))
      (ctxOf (depth + ambient)) :=
  fun s v => by
    cases s
    by_cases hdependency : varIndex v < dependencies
    · exact arguments ⟨varIndex v, hdependency⟩
    · have hsource : varIndex v < dependencies + ambient := by
        simpa [ctxOf] using varIndex_lt v
      exact .var (varOfFin ⟨depth + (varIndex v - dependencies), by omega⟩)

private theorem rawArguments_getD {dependencies ambient depth : Nat}
    (arguments : Fin dependencies →
      Term patSig (ctxOf (depth + ambient)) PatSrt.pat)
    {index : Nat} (hindex : index < dependencies) :
    (rawArguments arguments).getD index (.bvar 0) =
      erase (arguments ⟨index, hindex⟩) := by
  have hlength : index < (rawArguments arguments).length := by
    simpa [rawArguments] using hindex
  rw [List.getD_eq_getElem (rawArguments arguments) (.bvar 0) hlength]
  simp only [rawArguments, List.getElem_ofFn]

/-- The actual executable occurrence assignment is the erasure of the typed
one on every index admitted by its source context. -/
theorem occurrenceSub_erases (dependencies ambient depth : Nat)
    (arguments : Fin dependencies →
      Term patSig (ctxOf (depth + ambient)) PatSrt.pat) :
    ErasesAssignment (occurrenceSub dependencies ambient depth arguments)
      (occurrenceAssignment dependencies depth (rawArguments arguments)) := by
  intro s v
  cases s
  by_cases hdependency : varIndex v < dependencies
  · simp only [occurrenceSub, hdependency, dite_true, occurrenceAssignment, if_pos]
    exact (rawArguments_getD arguments hdependency).symm
  · simp [occurrenceSub, occurrenceAssignment, hdependency]
    simp only [erase, varIndex_varOfFin]

/-- The typed substitution and the actual executable occurrence substitution
give identical raw results for every typed body in the declared context. -/
theorem erase_bind_occurrence (dependencies ambient depth : Nat)
    (arguments : Fin dependencies →
      Term patSig (ctxOf (depth + ambient)) PatSrt.pat)
    (body : Term patSig (ctxOf (dependencies + ambient)) PatSrt.pat) :
    erase (bind (occurrenceSub dependencies ambient depth arguments) body) =
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
        (occurrenceAssignment dependencies depth (rawArguments arguments))
        (erase body) :=
  erase_bind_substitute _ _ (occurrenceSub_erases dependencies ambient depth arguments) body

/-- Regard one intrinsically scoped value as the executable value read in its
declared dependency prefix followed by the ambient context. -/
def erasedValue (sorts : List TypeExpr) (ambient : Nat)
    (body : Term patSig (ctxOf (sorts.length + ambient)) PatSrt.pat) :
    ContextualValue :=
  { dependencies := sorts, ambient, body := erase body }

private theorem rawArguments_all_scoped {dependencies ambient depth : Nat}
    (arguments : Fin dependencies →
      Term patSig (ctxOf (depth + ambient)) PatSrt.pat) :
    (rawArguments arguments).all
      (fun argument => argument.isWellScopedAt (depth + ambient)) = true := by
  apply List.all_eq_true.mpr
  intro argument hmem
  have hmem' : argument ∈ List.ofFn (fun i => erase (arguments i)) := hmem
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem'
  subst argument
  simpa [ctxOf] using erase_isWellScopedAt (arguments i)

/-- Executable value instantiation is the erasure of typed occurrence
substitution, including arbitrary nonvariable arguments and ambient variables
weakened below an occurrence's local binders. No success check is postulated:
the typed source and destination contexts discharge every executable check. -/
theorem instantiateValue?_erase_bind (sorts : List TypeExpr) (ambient depth : Nat)
    (body : Term patSig (ctxOf (sorts.length + ambient)) PatSrt.pat)
    (arguments : Fin sorts.length →
      Term patSig (ctxOf (depth + ambient)) PatSrt.pat) :
    instantiateValue? (erasedValue sorts ambient body) ambient depth
      (rawArguments arguments) =
    some (erase (bind (occurrenceSub sorts.length ambient depth arguments) body)) := by
  have hbody : (erase body).isWellScopedAt (sorts.length + ambient) = true := by
    simpa [ctxOf] using erase_isWellScopedAt body
  have hresult :
      (erase (bind (occurrenceSub sorts.length ambient depth arguments) body)).isWellScopedAt
        (depth + ambient) = true := by
    simpa [ctxOf] using
      erase_isWellScopedAt (bind (occurrenceSub sorts.length ambient depth arguments) body)
  have hlength : (rawArguments arguments).length = sorts.length := by
    simp only [rawArguments, List.length_ofFn]
  have hargs := rawArguments_all_scoped arguments
  have hcompare := erase_bind_occurrence sorts.length ambient depth arguments body
  simp [instantiateValue?, erasedValue, hbody, hlength, hargs, ← hcompare, hresult]

/-- An ambient variable supplied by a premise stays ambient when the output
occurrence is placed below one new binder. -/
theorem open_ambient_value_below_binder :
    instantiateValue?
      (erasedValue [] 1
        (Term.var (varOfFin (⟨0, by decide⟩ : Fin 1))))
      1 1 [] = some (.bvar 1) := by
  change instantiateValue?
      (erasedValue [] 1 (Term.var (varOfFin (⟨0, by decide⟩ : Fin 1))))
      1 1 (rawArguments (dependencies := 0) (ambient := 1) (depth := 1)
        (Fin.elim0 : Fin 0 → Term patSig (ctxOf 2) PatSrt.pat)) = _
  rw [instantiateValue?_erase_bind]
  decide +kernel

theorem open_ambient_value_is_not_captured :
    instantiateValue?
      (erasedValue [] 1
        (Term.var (varOfFin (⟨0, by decide⟩ : Fin 1))))
      1 1 [] ≠ some (.bvar 0) := by
  rw [open_ambient_value_below_binder]
  decide

end Mettapedia.OSLF.Binding.PatternPresentation
