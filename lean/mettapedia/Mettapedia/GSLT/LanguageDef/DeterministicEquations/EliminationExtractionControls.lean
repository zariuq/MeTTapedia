import Mettapedia.GSLT.LanguageDef.DeterministicEquations.EliminationExtraction

/-! # Constructor elimination, guarded evaluation and projection controls

The first controls consume generated certificates for actual kernel
definitions. The remaining sources exercise the shared guard and projection
lowering, including refusal outside their encoded input domains.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Elimination.Controls

open Lean Meta Elab Command
open Mettapedia.Languages
open MM0.Presentation.ComputationalContext

private def binderHead :=
  "nik:extracted:Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Elimination.binderSortProgram"

private def boundHead :=
  "nik:extracted:Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Elimination.boundSortProgram"

private def builtinHead :=
  "nik:extracted:Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Elimination.builtinArityProgram"

theorem bound_binder_preserves_sort (sort : Nat) :
    Applies binderSortProgram productDivisionHost binderHead [encodeBinder (.bound sort)]
      (natural sort) := binder_sort_computes (.bound sort)

theorem regular_binder_preserves_sort (sort : Nat) (dependencies : Finset Nat) :
    Applies binderSortProgram productDivisionHost binderHead [encodeBinder (.regular sort dependencies)]
      (natural sort) := binder_sort_computes (.regular sort dependencies)

theorem wrong_binder_sort_refuses (binder : MM0.Kernel.Binder) (sort : Nat)
    (different : sort ≠ binder.sort) :
    ¬ Applies binderSortProgram productDivisionHost binderHead [encodeBinder binder]
      (natural sort) := by
  intro accepted
  have same := accepted.deterministic (binder_sort_computes binder)
  exact different (natural_injective same)

theorem bound_variable_accepts (sort : Nat) :
    Applies boundSortProgram productDivisionHost boundHead
      [encodeList encodeBinder [.bound sort], MM0.Presentation.encode (.var 0)]
      (encodeOption natural (some sort)) := bound_sort_computes [.bound sort] (.var 0)

theorem regular_variable_refuses_as_data (sort : Nat) (dependencies : Finset Nat) :
    Applies boundSortProgram productDivisionHost boundHead
      [encodeList encodeBinder [.regular sort dependencies], MM0.Presentation.encode (.var 0)]
      (.sym "None") := bound_sort_computes [.regular sort dependencies] (.var 0)

theorem undefined_variable_refuses_as_data (index : Nat) :
    Applies boundSortProgram productDivisionHost boundHead
      [encodeList encodeBinder [], MM0.Presentation.encode (.var index)]
      (.sym "None") := bound_sort_computes [] (.var index)

theorem compound_is_not_a_bound_variable (context : MM0.Kernel.Context)
    (function argument : MM0.Kernel.Preterm) :
    Applies boundSortProgram productDivisionHost boundHead
      [encodeList encodeBinder context, MM0.Presentation.encode (.app function argument)]
      (.sym "None") := bound_sort_computes context (.app function argument)

theorem bound_sort_independent_characterization (context : MM0.Kernel.Context)
    (expression : MM0.Kernel.Preterm) (sort : Nat) :
    Applies boundSortProgram productDivisionHost boundHead
      [encodeList encodeBinder context, MM0.Presentation.encode expression]
      (encodeOption natural (some sort)) ↔
      ∃ index, expression = .var index ∧ context[index]? = some (.bound sort) := by
  rw [(MM0.Kernel.Preterm.boundSort_eq_some_iff context expression sort).symm]
  constructor
  · intro accepted
    have same := accepted.deterministic (bound_sort_computes context expression)
    exact (encodeOption_injective natural_injective same).symm
  · intro same
    simpa only [boundHead, same] using bound_sort_computes context expression

theorem all_builtins_have_exact_arity (builtin : VibeITP.Spec.Builtin) :
    Applies builtinArityProgram productDivisionHost builtinHead [encodeBuiltin builtin]
      (natural builtin.arity) := builtin_arity_computes builtin

theorem jit_builtin_arity_is_four :
    Applies builtinArityProgram productDivisionHost builtinHead [encodeBuiltin .executedTo]
      (natural 4) := builtin_arity_computes .executedTo

theorem wrong_builtin_arity_refuses (builtin : VibeITP.Spec.Builtin) (arity : Nat)
    (different : arity ≠ builtin.arity) :
    ¬ Applies builtinArityProgram productDivisionHost builtinHead [encodeBuiltin builtin]
      (natural arity) := by
  intro accepted
  have same := accepted.deterministic (builtin_arity_computes builtin)
  exact different (natural_injective same)

private def guardedLookup (take : Bool) (values : List Nat) (index : Nat) : Option Nat :=
  if take then values[index]? else none

extract_candidate guardedLookupProgram from guardedLookup
certify_extraction guardedLookupProgram from guardedLookup as guarded_lookup_computes

private def guardHead :=
  "nik:extracted:Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Elimination.Controls.guardedLookupProgram"

private def returnedNone : Outcome → Bool
  | .value (.sym name) => name == "None"
  | _ => false

private theorem returnedNone_iff (outcome : Outcome) :
    returnedNone outcome = true ↔ outcome = .value (.sym "None") := by
  cases outcome with
  | value value => cases value <;> simp [returnedNone]
  | failure => simp [returnedNone]
  | exhausted => simp [returnedNone]

private def refused : Outcome → Bool
  | .failure => true
  | _ => false

private theorem refused_iff (outcome : Outcome) :
    refused outcome = true ↔ outcome = .failure := by
  cases outcome <;> simp [refused]

private def exhausted : Outcome → Bool
  | .exhausted => true
  | _ => false

private theorem exhausted_iff (outcome : Outcome) :
    exhausted outcome = true ↔ outcome = .exhausted := by
  cases outcome <;> simp [exhausted]

theorem skipped_lookup_does_not_need_a_live_index (values : List Nat) (index : Nat) :
    Applies guardedLookupProgram productDivisionHost guardHead
      [boolean false, encodeList natural values, natural index] (.sym "None") :=
  guarded_lookup_computes false values index

theorem taken_lookup_retains_missing_index (index : Nat) :
    Applies guardedLookupProgram productDivisionHost guardHead
      [boolean true, encodeList natural [], natural index] (.sym "None") :=
  guarded_lookup_computes true [] index

theorem skipped_malformed_list_is_not_read :
    apply guardedLookupProgram productDivisionHost 32 guardHead
      [.sym "False", .sym "not-a-list", natural 0] = .value (.sym "None") := by
  apply (returnedNone_iff _).mp
  decide +kernel

theorem taken_malformed_list_is_a_fault :
    apply guardedLookupProgram productDivisionHost 32 guardHead
      [.sym "True", .sym "not-a-list", natural 0] = .failure := by
  apply (refused_iff _).mp
  decide +kernel

theorem guard_exhaustion_is_separate :
    apply guardedLookupProgram productDivisionHost 0 guardHead
      [.sym "False", .sym "not-a-list", natural 0] = .exhausted := by
  apply (exhausted_iff _).mp
  decide +kernel

private def guardedIncrement (value : Nat) : Option Nat :=
  if value + 1 < 18446744073709551616 then some (value + 1) else none

extract_candidate guardedIncrementProgram from guardedIncrement
certify_extraction guardedIncrementProgram from guardedIncrement as guarded_increment_computes

private def incrementHead :=
  "nik:extracted:Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Elimination.Controls.guardedIncrementProgram"

theorem increment_boundary_is_retained :
    Applies guardedIncrementProgram productDivisionHost incrementHead
      [natural 18446744073709551615] (.sym "None") := guarded_increment_computes _

theorem increment_above_word_boundary_is_retained (value : Nat)
    (outside : 18446744073709551616 ≤ value + 1) :
    Applies guardedIncrementProgram productDivisionHost incrementHead
      [natural value] (.sym "None") := by
  simpa only [incrementHead, guardedIncrement, if_neg (Nat.not_lt.mpr outside), encodeOption] using
    guarded_increment_computes value

private def pairSum (value : Nat × Nat) : Nat := value.1 + value.2

extract_candidate pairSumProgram from pairSum
certify_extraction pairSumProgram from pairSum as pair_sum_computes

private def pairHead :=
  "nik:extracted:Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Elimination.Controls.pairSumProgram"

theorem projections_preserve_both_fields (first second : Nat) :
    Applies pairSumProgram productDivisionHost pairHead
      [encodePair natural natural (first, second)] (natural (first + second)) :=
  pair_sum_computes (first, second)

theorem projection_wrong_arity_refuses :
    apply pairSumProgram productDivisionHost 32 pairHead [] = .failure := by
  apply (refused_iff _).mp
  decide +kernel

@[instance_reducible] private def foreignLookup :
    GetElem? (List Nat) Nat Nat (fun values index => index < values.length) where
  toGetElem := inferInstance
  getElem? _ _ := none
  getElem! _ _ := 0

private def foreignLookupSource (values : List Nat) (index : Nat) : Option Nat :=
  @GetElem?.getElem? (List Nat) Nat Nat (fun values index => index < values.length)
    foreignLookup values index

private def foreignNumeralSource : Nat := @OfNat.ofNat Nat 7 ⟨0⟩

@[instance_reducible] private def foreignOrder : LT Nat := ⟨fun _ _ => True⟩

private def foreignOrderSource (value : Nat) : Option Nat :=
  @ite (Option Nat) (@LT.lt Nat foreignOrder value 0) (.isTrue trivial) (some value) none

private def requireRefusal (operation : Elab.Term.TermElabM Unit) :
    Elab.Term.TermElabM Unit := do
  let saved ← saveState
  let refused ← try
    operation
    pure false
  catch _ =>
    saved.restore
    pure true
  unless refused do throwError "foreign source instance was silently accepted"

run_cmd liftTermElabM do
  for source in #[``foreignLookupSource, ``foreignNumeralSource, ``foreignOrderSource] do
    requireRefusal do
      let root ← inspectRoot source ("test:" ++ source.toString)
      let _ ← compileRoot root

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Elimination.Controls
