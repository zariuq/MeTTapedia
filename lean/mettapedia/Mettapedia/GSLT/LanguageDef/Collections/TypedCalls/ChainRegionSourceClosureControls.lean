import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainRegionSourceClosure
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainDeclarationAdmissionControls

/-! # Source-region controls with an unrelated open datatype declaration -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainRegionSourceClosure.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open ChainRegion ChainDeclarationAdmission
open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Controls (num str env)

def listType (element : Ty String) : Ty String := .app [.sym "List", element]

def consRow : Ty String := arrow [.var "element", listType (.var "element")]
  (listType (.var "element"))

def source : Source := ChainDeclarationAdmission.Controls.source ++ [(.symbol "Cons", consRow)]

def heads : List String := ["main", "number", "string", "helper"]

theorem source_functional_checked : functionalCheck source = true := by decide

theorem region_metadata_checked : regionCheck source heads = true := by decide

theorem authored_source_closed :
    closedEquationsCheck heads ChainRegion.Controls.separateEqs = true := by decide

theorem open_constructor_preserved :
    declarations source "Cons" = [consRow] ∧ sourceSignature source "Cons" = some consRow := by decide

theorem whole_space_profile_not_required : closedSourceCheck source = false := by decide

theorem source_program_correspondence (grounded : String → Bool) (fuel : Nat) :
    run (declarations source) grounded (generatedRows source)
      (stepsOf env ChainRegion.Controls.separateEqs) fuel none "main" [] =
    protocolRunS (declarations source) grounded (sourceSignature source)
      (stepsOf env ChainRegion.Controls.separateEqs) fuel "main" [] :=
  region_source_run_eq_protocol source_functional_checked region_metadata_checked grounded env _
    authored_source_closed fuel "main" (by decide) []

/-- The new source contains an unsupported open constructor annotation, but
none of the region's actual callable metadata changes. -/
theorem generated_separate_rows : generatedRows source = ChainRegion.Controls.separateRows := by
  funext head
  by_cases main : head = "main"
  · subst head; decide
  by_cases number : head = "number"
  · subst head; decide
  by_cases string : head = "string"
  · subst head; decide
  by_cases cons : head = "Cons"
  · subst head; decide
  simp [generatedRows, lookup, status, declarations, Decls.idemAlpha, rawRows, source,
    ChainDeclarationAdmission.Controls.source, ChainRegion.Controls.separateRows,
    Ne.symm main, Ne.symm number, Ne.symm string, Ne.symm cons, dedupAlpha]

private theorem literal_return (grounded : String → Bool) (g : GroundedValue) (c : String)
    (classed : valueClass g = some c) (notMeta : ¬ MetaName (.sym c)) :
    owedCheck (declarations source) grounded (some (.sym c)) {.grounded g} = {.grounded g} := by
  simp only [owedCheck, rangeCheck, Multiset.singleton_bind]
  rw [guardCount_of_not_meta notMeta, count_class _ classed]
  simp [one_nsmul]

private theorem source_string (grounded : String → Bool) (n : Nat) :
    run (declarations source) grounded ChainRegion.Controls.separateRows
      (stepsOf env ChainRegion.Controls.separateEqs) (n + 1) none "string" [] = {str "s"} := by
  rw [run_accepted _ _ _ _ n none "string" [] (q := some (.sym "String")) (by decide) (by decide)]
  simpa [stepsOf, ChainRegion.Controls.separateEqs, Pat.matchAll, Expr.evalOut, Expr.eval, str] using
    literal_return grounded (.string "s") "String" rfl (by decide)

private theorem source_number (grounded : String → Bool) (n : Nat) :
    run (declarations source) grounded ChainRegion.Controls.separateRows
      (stepsOf env ChainRegion.Controls.separateEqs) (n + 1) (some (.sym "Number")) "number" [] = {num 7} := by
  rw [run_accepted _ _ _ _ n (some (.sym "Number")) "number" []
    (q := some (.sym "Number")) (by decide) (by decide)]
  simpa [stepsOf, ChainRegion.Controls.separateEqs, Pat.matchAll, Expr.evalOut, Expr.eval, num] using
    literal_return grounded (.int 7) "Number" rfl (by decide)

private theorem source_helper (grounded : String → Bool) (n : Nat) :
    run (declarations source) grounded ChainRegion.Controls.separateRows
      (stepsOf env ChainRegion.Controls.separateEqs) (n + 2) none "helper" [] = {str "s"} := by
  rw [run_accepted _ _ _ _ (n + 1) none "helper" [] (q := none) (by decide) (by decide)]
  simpa [stepsOf, ChainRegion.Controls.separateEqs, Pat.matchAll, Expr.evalOut, Expr.evalAll] using
    source_string grounded n

/-- Actual authored source, including the unrelated open Cons annotation,
retains the non-tail untyped helper and independent range obligations. -/
theorem open_space_separate_chains (grounded : String → Bool) (n : Nat) :
    run (declarations source) grounded (generatedRows source)
      (stepsOf env ChainRegion.Controls.separateEqs) (n + 3) none "main" [] = {num 7} := by
  rw [generated_separate_rows]
  rw [run_accepted _ _ _ _ (n + 2) none "main" []
    (q := some (.sym "Number")) (by decide) (by decide), ChainRegion.Controls.separate_main_step]
  rw [source_helper grounded n]
  simpa using source_number grounded (n + 1)

theorem open_space_source_answer (grounded : String → Bool) (n : Nat) :
    protocolRunS (declarations source) grounded (sourceSignature source)
      (stepsOf env ChainRegion.Controls.separateEqs) (n + 3) "main" [] = {num 7} := by
  rw [← source_program_correspondence]
  exact open_space_separate_chains grounded n

/-- Omitting an actual untyped callee does not evade source closure. -/
theorem missing_reachable_helper_rejected :
    closedEquationsCheck ["main", "number", "string"] ChainRegion.Controls.separateEqs = false := by decide

/-- Closure and signature admission are independent gates. The graph can be
closed while the reached helper has unsupported open typing metadata. -/
theorem unsupported_called_head_rejected :
    closedEquationsCheck heads ChainRegion.Controls.separateEqs = true ∧
    regionCheck (source ++ [(.symbol "helper", arrow [] (.var "range"))]) heads = false := by decide

theorem constructor_and_canonical_names_not_calls :
    reachedCalls "main" (.ctor "Cons" [.call "canonical" [.const (num 1)]]) = [] := rfl

theorem nested_argument_calls_kept :
    reachedCalls "main" (.call "canonical" [.ctor "Cons" [.enter "missing" []]]) = ["missing"] ∧
    (reachedCalls "main" (.call "canonical" [.ctor "Cons" [.enter "missing" []]])).all
      (within heads) = false := by decide

theorem self_and_branch_calls_kept :
    reachedCalls "main" (.ifE (.const truth) (.self []) (.enter "other" [])) = ["main", "other"] := rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainRegionSourceClosure.Controls
