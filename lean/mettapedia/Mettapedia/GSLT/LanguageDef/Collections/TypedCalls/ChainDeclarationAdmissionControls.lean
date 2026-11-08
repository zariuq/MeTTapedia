import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainDeclarationAdmission

/-! # Executable controls for declaration-derived checked call chains -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainDeclarationAdmission.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open ChainRegion
open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Controls (num str env)

def numberSignature : Signature := ⟨[], .number⟩
def stringSignature : Signature := ⟨[], .string⟩
def unaryNumberSignature : Signature := ⟨[.number], .number⟩

def source : Source :=
  [(.symbol "main", numberSignature.row),
   (.symbol "number", numberSignature.row),
   (.symbol "string", stringSignature.row)]

theorem source_checked : closedSourceCheck source = true := by decide

theorem source_functional : Functional (declarations source) :=
  functional_of_check (by decide)

theorem generated_separate_rows : generatedRows source = ChainRegion.Controls.separateRows := by
  funext head
  by_cases main : head = "main"
  · subst head; decide
  by_cases number : head = "number"
  · subst head; decide
  by_cases string : head = "string"
  · subst head; decide
  simp [generatedRows, lookup, status, declarations, Decls.idemAlpha, rawRows, source,
    ChainRegion.Controls.separateRows, Ne.symm main, Ne.symm number,
    Ne.symm string, dedupAlpha]

/-- Duplicate written rows leave admission unchanged. -/
theorem duplicate_row_preserves :
    declarations (source ++ [(.symbol "main", numberSignature.row)]) = declarations source :=
  repeat_preserves_index source "main" numberSignature.row
    ⟨numberSignature.row, by decide, rfl⟩

theorem duplicate_row_admitted :
    closedSourceCheck (source ++ [(.symbol "main", numberSignature.row)]) = true := by decide

theorem absent_helper_is_untyped : status source "helper" = .untyped := by decide

theorem overload_declines :
    status (source ++ [(.symbol "main", stringSignature.row)]) "main" = .unsupported ∧
    functionalCheck (source ++ [(.symbol "main", stringSignature.row)]) = false := by decide

theorem open_row_is_not_untyped :
    status [(.symbol "poly", arrow [.var "a"] (.var "a"))] "poly" = .unsupported ∧
    lookup [(.symbol "poly", arrow [.var "a"] (.var "a"))] "poly" = none := by decide

theorem atom_formal_declines :
    status [(.symbol "held", arrow [.sym "Atom"] (.sym "Number"))] "held" = .unsupported := by decide

theorem structural_formal_declines :
    status [(.symbol "list", arrow [.app [.sym "List", .sym "Number"]] (.sym "Number"))]
      "list" = .unsupported := by decide

theorem headless_subject_fails_gate :
    functionalCheck [(.var "head", numberSignature.row)] = false := by decide

theorem custom_get_type_fails_gate : nativeFunctionalGate source true = false := by decide

theorem wrong_arity_not_untyped :
    statusAt [(.symbol "f", unaryNumberSignature.row)] "f" 0 = .unsupported := by decide

theorem wrong_argument_refused :
    argumentsAccepted unaryNumberSignature.params [str "s"] = false := by decide

theorem correct_argument_accepted (n : Int) :
    argumentsAccepted unaryNumberSignature.params [num n] = true := by rfl

/-- An unrelated constructor declaration is allowed by local region
metadata, but is deliberately outside the stronger whole-source profile. -/
theorem local_region_with_unrelated_constructor :
    regionCheck (source ++ [(.symbol "Z", .sym "Nat")]) ["main", "number", "string", "helper"] = true ∧
    closedSourceCheck (source ++ [(.symbol "Z", .sym "Nat")]) = false := by decide

/-- Alpha-equivalent polymorphic rows remain one declaration; being unique
does not itself make their open value-class metadata supported. -/
theorem alpha_duplicate_not_closed :
    functionalCheck [(.symbol "f", arrow [.var "a"] (.var "a")),
      (.symbol "f", arrow [.var "b"] (.var "b"))] = true ∧
    status [(.symbol "f", arrow [.var "a"] (.var "a")),
      (.symbol "f", arrow [.var "b"] (.var "b"))] "f" = .unsupported := by decide

theorem source_program_correspondence (grounded : String → Bool) (fuel : Nat) :
    run (declarations source) grounded (generatedRows source)
      (stepsOf env ChainRegion.Controls.separateEqs) fuel none "main" [] =
    protocolRunS (declarations source) grounded (sourceSignature source)
      (stepsOf env ChainRegion.Controls.separateEqs) fuel "main" [] :=
  source_program_run_eq_protocol source_checked grounded env _ fuel "main" []

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

/-- The same authored non-tail untyped helper / separate Number and String
chains now run with their table and global declaration fact earned from
written annotations, and return exactly one Number answer. -/
theorem source_separate_chains (grounded : String → Bool) (n : Nat) :
    run (declarations source) grounded (generatedRows source)
      (stepsOf env ChainRegion.Controls.separateEqs) (n + 3) none "main" [] = {num 7} := by
  rw [generated_separate_rows]
  rw [run_accepted _ _ _ _ (n + 2) none "main" []
    (q := some (.sym "Number")) (by decide) (by decide), ChainRegion.Controls.separate_main_step]
  rw [source_helper grounded n]
  simpa using source_number grounded (n + 1)

theorem source_separate_chains_protocol (grounded : String → Bool) (n : Nat) :
    protocolRunS (declarations source) grounded (sourceSignature source)
      (stepsOf env ChainRegion.Controls.separateEqs) (n + 3) "main" [] = {num 7} := by
  rw [← source_program_correspondence]
  exact source_separate_chains grounded n

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainDeclarationAdmission.Controls
