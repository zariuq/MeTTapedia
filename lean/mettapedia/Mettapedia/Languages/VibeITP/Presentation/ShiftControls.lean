import Mettapedia.Languages.VibeITP.Presentation.ShiftSignature

/-!
# Boundary controls for authored Vibe shifting

These are raw operation inputs. Some deliberately have unknown heads, extra
arguments or indices outside the formation profile, because the operation's
pruning behavior must be preserved independently of term formation.

The guard mutation changes only the authored strict word comparison. The
unchanged equation engine then returns a result the original equations refuse.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalShift.Controls

open ComputationalData
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => shiftProgram
local notation "H" => computationalHost

private def s : Spec.SymId := .fresh 13
private def t : Spec.SymId := .fresh 14
private def oneBinder : SignatureTable := [(s, ⟨.constant, [1]⟩)]
private def twoPositions : SignatureTable := [(s, ⟨.constant, [1, 0]⟩)]
private def nestedBinders : SignatureTable := [(s, ⟨.constant, [1]⟩), (t, ⟨.constant, [2]⟩)]

theorem free_variable_shifts :
    Applies P H "vibe:shift" [encodeTable [], encode (.bvar 0), natural 2, natural 0]
      (encodeResult (some (.bvar 2))) := shift_computes [] 2 0 (.bvar 0)

theorem bound_variable_stays :
    Applies P H "vibe:shift" [encodeTable [], encode (.bvar 0), natural 2, natural 1]
      (encodeResult (some (.bvar 0))) := shift_computes [] 2 1 (.bvar 0)

theorem positions_have_independent_binder_counts :
    Applies P H "vibe:shift"
      [encodeTable twoPositions, encode (.app s [.bvar 0, .bvar 0]), natural 2, natural 0]
      (encodeResult (some (.app s [.bvar 0, .bvar 2]))) :=
  shift_computes twoPositions 2 0 (.app s [.bvar 0, .bvar 0])

theorem nested_binders_accumulate :
    Applies P H "vibe:shift"
      [encodeTable nestedBinders, encode (.app s [.app t [.bvar 3]]), natural 1, natural 0]
      (encodeResult (some (.app s [.app t [.bvar 4]]))) :=
  shift_computes nestedBinders 1 0 (.app s [.app t [.bvar 3]])

theorem missing_binder_defaults_to_zero :
    Applies P H "vibe:shift"
      [encodeTable oneBinder, encode (.app s [.bvar 0, .bvar 0]), natural 2, natural 0]
      (encodeResult (some (.app s [.bvar 0, .bvar 2]))) :=
  shift_computes oneBinder 2 0 (.app s [.bvar 0, .bvar 0])

theorem unused_binder_overflow_is_not_inspected :
    Applies P H "vibe:shift"
      [encodeTable [(s, ⟨.constant, [0, Spec.wordBound]⟩)], encode (.app s [.bvar 0]), natural 2, natural 0]
      (encodeResult (some (.app s [.bvar 2]))) :=
  shift_computes [(s, ⟨.constant, [0, Spec.wordBound]⟩)] 2 0 (.app s [.bvar 0])

theorem unknown_head_defaults_to_zero :
    Applies P H "vibe:shift"
      [encodeTable [], encode (.app (.fresh 18446744073709551629) [.bvar 0]), natural 1, natural 0]
      (encodeResult (some (.app (.fresh 18446744073709551629) [.bvar 1]))) :=
  shift_computes [] 1 0 (.app (.fresh 18446744073709551629) [.bvar 0])

theorem literal_bytes_are_preserved :
    Applies P H "vibe:shift" [encodeTable [], encode (.lit [0, 255, 42]), natural Spec.wordBound,
      natural Spec.wordBound] (encodeResult (some (.lit [0, 255, 42]))) :=
  shift_computes [] Spec.wordBound Spec.wordBound (.lit [0, 255, 42])

theorem repeated_arguments_preserve_multiplicity :
    Applies P H "vibe:shift"
      [encodeTable [], encode (.app s [.bvar 0, .bvar 0]), natural 1, natural 0]
      (encodeResult (some (.app s [.bvar 1, .bvar 1]))) :=
  shift_computes [] 1 0 (.app s [.bvar 0, .bvar 0])

theorem zero_amount_preserves_out_of_word_index :
    Applies P H "vibe:shift" [encodeTable [], encode (.bvar (Spec.wordBound + 100)), natural 0, natural 0]
      (encodeResult (some (.bvar (Spec.wordBound + 100)))) :=
  shift_computes [] 0 0 (.bvar (Spec.wordBound + 100))

theorem cutoff_prunes_out_of_word_index :
    Applies P H "vibe:shift"
      [encodeTable [], encode (.bvar (Spec.wordBound + 100)), natural 7, natural (Spec.wordBound + 101)]
      (encodeResult (some (.bvar (Spec.wordBound + 100)))) :=
  shift_computes [] 7 (Spec.wordBound + 101) (.bvar (Spec.wordBound + 100))

theorem zero_amount_prunes_binder_overflow :
    Applies P H "vibe:shift"
      [encodeTable [(s, ⟨.constant, [Spec.wordBound]⟩)], encode (.app s [.bvar Spec.wordBound]),
        natural 0, natural 0] (encodeResult (some (.app s [.bvar Spec.wordBound]))) :=
  shift_computes [(s, ⟨.constant, [Spec.wordBound]⟩)] 0 0 (.app s [.bvar Spec.wordBound])

theorem depth_pruning_skips_binder_overflow :
    Applies P H "vibe:shift"
      [encodeTable [(s, ⟨.constant, [Spec.wordBound + 10]⟩)], encode (.app s [.bvar (Spec.wordBound + 1)]),
        natural 1, natural 0] (encodeResult (some (.app s [.bvar (Spec.wordBound + 1)]))) :=
  shift_computes [(s, ⟨.constant, [Spec.wordBound + 10]⟩)] 1 0 (.app s [.bvar (Spec.wordBound + 1)])

theorem largest_allowed_result_completes :
    Applies P H "vibe:shift"
      [encodeTable [], encode (.bvar 18446744073709551613), natural 1, natural 0]
      (encodeResult (some (.bvar 18446744073709551614))) :=
  shift_computes [] 1 0 (.bvar 18446744073709551613)

theorem exact_word_boundary_refuses :
    Applies P H "vibe:shift"
      [encodeTable [], encode (.bvar 18446744073709551614), natural 1, natural 0]
      (encodeResult none) := shift_computes [] 1 0 (.bvar 18446744073709551614)

theorem crossed_word_boundary_refuses :
    Applies P H "vibe:shift" [encodeTable [], encode (.bvar 0), natural Spec.wordBound, natural 0]
      (encodeResult none) := shift_computes [] Spec.wordBound 0 (.bvar 0)

theorem reached_binder_overflow_refuses :
    Applies P H "vibe:shift"
      [encodeTable [(s, ⟨.constant, [Spec.wordBound]⟩)], encode (.app s [.bvar Spec.wordBound]),
        natural 1, natural 0] (encodeResult none) :=
  shift_computes [(s, ⟨.constant, [Spec.wordBound]⟩)] 1 0 (.app s [.bvar Spec.wordBound])

theorem first_child_refusal_propagates :
    Applies P H "vibe:shift"
      [encodeTable [], encode (.app s [.bvar 18446744073709551614, .lit [42]]), natural 1, natural 0]
      (encodeResult none) :=
  shift_computes [] 1 0 (.app s [.bvar 18446744073709551614, .lit [42]])

theorem later_child_refusal_propagates :
    Applies P H "vibe:shift"
      [encodeTable [], encode (.app s [.lit [42], .bvar 18446744073709551614]), natural 1, natural 0]
      (encodeResult none) :=
  shift_computes [] 1 0 (.app s [.lit [42], .bvar 18446744073709551614])

theorem first_table_entry_wins :
    Applies P H "vibe:lookup-symbol"
      [encodeTable [(s, ⟨.fvar, [1]⟩), (s, ⟨.constant, []⟩)], encodeSymbol s]
      (encodeInfoResult (some ⟨.fvar, [1]⟩)) :=
  lookup_computes [(s, ⟨.fvar, [1]⟩), (s, ⟨.constant, []⟩)] s

theorem builtin_and_fresh_tags_do_not_collide :
    Applies P H "vibe:symbol-eq" [encodeSymbol (.builtin .impl), encodeSymbol (.fresh 2)]
      (.sym "False") := symbol_computes (.builtin .impl) (.fresh 2)

theorem incorrect_shifted_result_is_not_invented :
    ¬ Applies P H "vibe:shift"
      [encodeTable twoPositions, encode (.app s [.bvar 0, .bvar 0]), natural 2, natural 0]
      (encodeResult (some (.app s [.bvar 2, .bvar 2]))) := by
  intro invented
  have wrong := encodeResult_injective (invented.deterministic positions_have_independent_binder_counts)
  cases wrong

theorem original_strict_word_guard_rejects_boundary_result :
    ¬ Applies P H "vibe:shift"
      [encodeTable [], encode (.bvar 18446744073709551614), natural 1, natural 0]
      (encodeResult (some (.bvar 18446744073709551615))) := by
  intro invented
  have wrong := encodeResult_injective (invented.deterministic exact_word_boundary_refuses)
  cases wrong

private def relaxedGuard : Equation :=
  { (shiftProgram[26]) with body := .expr [.sym "vibe:shift-bvar-word",
      .expr [.sym "nik:nat-le",
        .expr [.sym "nik:nat-add", .expr [.sym "nik:nat-add", .var "i", .var "amount"], natural 1],
        natural Spec.wordBound],
      .expr [.sym "nik:nat-add", .var "i", .var "amount"]] }

private def relaxedProgram : Program := shiftProgram.set 26 relaxedGuard

local notation "R" => relaxedProgram

/- The two whole-call controls below compose the selected equations at their
actual fuel. Scalar calls use the shared primitive laws, so checking them does
not repeatedly unfold decimal parsing and the complete program. -/

private theorem variable_run {program : Program} {environment : Env} {fuel : Nat}
    {name : String} {value : Term} (positive : 0 < fuel)
    (found : environment.lookup name = some value) :
    eval program H fuel environment (.var name) = .value value := by
  cases fuel with
  | zero => exact (Nat.not_lt_zero _ positive).elim
  | succ fuel => simp only [eval, evalStep, found]

private theorem natural_run {program : Program} {environment : Env} {fuel : Nat}
    (positive : 0 < fuel) (value : Nat) :
    eval program H fuel environment (natural value) = .value (natural value) := by
  cases fuel with
  | zero => exact (Nat.not_lt_zero _ positive).elim
  | succ fuel => rfl

private theorem items_run {program : Program} {environment : Env} {fuel : Nat}
    {sources values : List Term}
    (children : List.Forall₂
      (fun source value => eval program H fuel environment source = .value value) sources values) :
    evalItems program H fuel environment sources = .values values := by
  induction children with
  | nil => rfl
  | cons first rest ih => simp only [evalItems, evalItemsWith, first, ih]

private theorem call_run {program : Program} {environment : Env} {fuel : Nat}
    {head : String} {arguments values : List Term} {result : Outcome}
    (ordinary : ¬ Special head arguments)
    (children : List.Forall₂
      (fun source value => eval program H fuel environment source = .value value) arguments values)
    (called : apply program H fuel head values = result) :
    eval program H (fuel + 1) environment (.expr (.sym head :: arguments)) = result := by
  rw [eval, evalStep_head ordinary]
  change (match evalItems program H fuel environment arguments with
    | .values values => apply program H fuel head values
    | .stop outcome => outcome) = result
  rw [items_run children]
  exact called

private theorem call_first_fault {program : Program} {environment : Env} {fuel : Nat}
    {head : String} {first : Term} {rest : List Term}
    (ordinary : ¬ Special head (first :: rest))
    (failed : eval program H fuel environment first = .failure) :
    eval program H (fuel + 1) environment (.expr (.sym head :: first :: rest)) = .failure := by
  rw [eval, evalStep_head ordinary]
  simp only [evalItemsWith, failed]

private theorem selected_run {program : Program} {fuel : Nat} {head : String}
    {arguments : List Term} {equation : Equation} {environment : Env} {result : Outcome}
    (defined : program.definesAt head arguments.length = true)
    (selected : program.select head arguments = some (equation, environment))
    (body : eval program H fuel environment equation.body = result) :
    apply program H fuel head arguments = result := by
  simp [apply, applyWith, defined, selected, body]

private theorem primitive_run {program : Program} {fuel : Nat} {head : String}
    {arguments : List Term} {value : Term} (undefined : program.defines head = false)
    (computed : (H).primitive head arguments = .value value) :
    apply program H fuel head arguments = .value value := by
  simp [apply, applyWith, Program.definesAt_false_of_defines_false undefined, undefined, computed]

private theorem primitive_fault {program : Program} {fuel : Nat} {head : String}
    {arguments : List Term} (undefined : program.defines head = false)
    (failed : (H).primitive head arguments = .fault) :
    apply program H fuel head arguments = .failure := by
  simp [apply, applyWith, Program.definesAt_false_of_defines_false undefined, undefined, failed]

private theorem constructor_run {program : Program} {fuel : Nat} {head : String}
    {arguments : List Term} (undefined : program.defines head = false)
    (unhandled : (H).primitive head arguments = .unhandled) :
    apply program H fuel head arguments = .value (.expr (.sym head :: arguments)) := by
  simp [apply, applyWith, Program.definesAt_false_of_defines_false undefined, undefined, unhandled]

private theorem add_run {program : Program} {environment : Env} {fuel left right : Nat}
    {leftSource rightSource : Term} (undefined : program.defines "nik:nat-add" = false)
    (first : eval program H fuel environment leftSource = .value (natural left))
    (second : eval program H fuel environment rightSource = .value (natural right)) :
    eval program H (fuel + 1) environment
      (.expr [.sym "nik:nat-add", leftSource, rightSource]) = .value (natural (left + right)) :=
  call_run (by simp [Special]) (.cons first (.cons second .nil))
    (primitive_run undefined (naturalArithmeticHost_add left right))

private theorem le_run {program : Program} {environment : Env} {fuel left right : Nat}
    {leftSource rightSource : Term} (undefined : program.defines "nik:nat-le" = false)
    (first : eval program H fuel environment leftSource = .value (natural left))
    (second : eval program H fuel environment rightSource = .value (natural right)) :
    eval program H (fuel + 1) environment
      (.expr [.sym "nik:nat-le", leftSource, rightSource]) =
      .value (boolean (decide (left ≤ right))) :=
  call_run (by simp [Special]) (.cons first (.cons second .nil))
    (primitive_run undefined (naturalArithmeticHost_le left right))

private theorem relaxed_word_run (index fuel : Nat) :
    apply R H (fuel + 3) "vibe:shift-bvar-word" [.sym "True", natural index] =
      .value (encodeResult (some (.bvar index))) := by
  refine selected_run (equation := shiftProgram[27])
    (environment := [("i", natural index)]) (by rfl) (by rfl) ?_
  change eval R H (fuel + 3) [("i", natural index)]
    (.expr [.sym "Some", .expr [.sym "Vibe:BVar", .var "i"]]) = _
  refine call_run (fuel := fuel + 2) (by simp [Special]) (.cons ?_ .nil)
    (constructor_run (by rfl) (by rfl))
  exact call_run (fuel := fuel + 1) (by simp [Special])
    (.cons (variable_run (Nat.zero_lt_succ _) (by rfl)) .nil)
    (constructor_run (by rfl) (by rfl))

private theorem relaxed_open_run :
    apply R H 10 "vibe:shift-bvar-closed"
      [.sym "False", natural 18446744073709551614, natural 1] =
      .value (encodeResult (some (.bvar 18446744073709551615))) := by
  refine selected_run (equation := relaxedGuard)
    (environment := [("i", natural 18446744073709551614), ("amount", natural 1)])
    (by rfl) (by rfl) ?_
  change eval R H 10 _ (.expr [.sym "vibe:shift-bvar-word",
    .expr [.sym "nik:nat-le",
      .expr [.sym "nik:nat-add", .expr [.sym "nik:nat-add", .var "i", .var "amount"], natural 1],
      natural Spec.wordBound],
    .expr [.sym "nik:nat-add", .var "i", .var "amount"]]) = _
  refine call_run (fuel := 9) (by simp [Special])
    (.cons ?_ (.cons ?_ .nil)) (relaxed_word_run 18446744073709551615 6)
  · refine le_run (fuel := 8) (left := Spec.wordBound) (right := Spec.wordBound) (by rfl) ?_
      (natural_run (by decide) _)
    refine add_run (fuel := 7) (left := 18446744073709551615) (right := 1) (by rfl) ?_
      (natural_run (by decide) _)
    exact add_run (fuel := 6) (left := 18446744073709551614) (right := 1) (by rfl)
      (variable_run (by decide) (by rfl)) (variable_run (by decide) (by rfl))
  · exact add_run (fuel := 8) (left := 18446744073709551614) (right := 1) (by rfl)
      (variable_run (by decide) (by rfl)) (variable_run (by decide) (by rfl))

private theorem relaxed_nonzero_run :
    apply R H 11 "vibe:shift-bvar-zero"
      [.sym "False", natural 18446744073709551614, natural 1, natural 0] =
      .value (encodeResult (some (.bvar 18446744073709551615))) := by
  refine selected_run (equation := shiftProgram[24])
    (environment := [("i", natural 18446744073709551614), ("amount", natural 1),
      ("cutoff", natural 0)]) (by rfl) (by rfl) ?_
  change eval R H 11 _ (.expr [.sym "vibe:shift-bvar-closed",
    .expr [.sym "nik:nat-le", .expr [.sym "nik:nat-add", .var "i", natural 1], .var "cutoff"],
    .var "i", .var "amount"]) = _
  refine call_run (fuel := 10) (by simp [Special])
    (.cons ?_ (.cons (variable_run (by decide) (by rfl))
      (.cons (variable_run (by decide) (by rfl)) .nil))) relaxed_open_run
  refine le_run (fuel := 9) (left := 18446744073709551615) (right := 0) (by rfl) ?_
    (variable_run (by decide) (by rfl))
  exact add_run (fuel := 8) (left := 18446744073709551614) (right := 1) (by rfl)
    (variable_run (by decide) (by rfl)) (natural_run (by decide) _)

private theorem bvar_start_run {program : Program} (index : Term) (result : Outcome)
    (zeroUndefined : program.defines "nik:nat-zero" = false)
    (defined : program.definesAt "vibe:shift" 4 = true)
    (selected : program.select "vibe:shift"
      [encodeTable [], .expr [.sym "Vibe:BVar", index], natural 1, natural 0] =
      some (shiftProgram[20], [("table", encodeTable []), ("i", index),
        ("amount", natural 1), ("cutoff", natural 0)]))
    (next : apply program H 11 "vibe:shift-bvar-zero"
      [.sym "False", index, natural 1, natural 0] = result) :
    apply program H 12 "vibe:shift"
      [encodeTable [], .expr [.sym "Vibe:BVar", index], natural 1, natural 0] = result := by
  refine selected_run defined selected ?_
  change eval program H 12 _ (.expr [.sym "vibe:shift-bvar-zero",
    .expr [.sym "nik:nat-zero", .var "amount"], .var "i", .var "amount", .var "cutoff"]) = _
  refine call_run (fuel := 11) (by simp [Special])
    (.cons ?_ (.cons (variable_run (by decide) (by rfl))
      (.cons (variable_run (by decide) (by rfl))
        (.cons (variable_run (by decide) (by rfl)) .nil)))) next
  refine call_run (fuel := 10) (by simp [Special])
    (.cons (variable_run (by decide) (by rfl)) .nil) ?_
  exact primitive_run zeroUndefined (computationalHost_zero 1)

/-- Only the strict comparison in equation 26 is changed. The shared engine
executes the changed authored definition without a guest-specific branch. -/
theorem changed_guard_changes_completed_result :
    apply relaxedProgram H 12 "vibe:shift"
      [encodeTable [], encode (.bvar 18446744073709551614), natural 1, natural 0] =
      .value (encodeResult (some (.bvar 18446744073709551615))) := by
  exact bvar_start_run (natural 18446744073709551614) _ (by rfl) (by rfl) (by rfl)
    relaxed_nonzero_run

theorem foreign_term_constructor_refuses :
    apply P H 1 "vibe:shift" [encodeTable [], .expr [.sym "MM0:Var", natural 0], natural 1, natural 0] =
      .failure := rfl

theorem wrong_call_arity_refuses :
    apply P H 1 "vibe:shift" [encodeTable [], encode (.bvar 0), natural 1] = .failure := rfl

theorem malformed_natural_operand_faults :
    apply P H 12 "vibe:shift"
      [encodeTable [], .expr [.sym "Vibe:BVar", .sym "not-a-number"], natural 1, natural 0] = .failure := by
  refine bvar_start_run (.sym "not-a-number") .failure (by rfl) (by rfl) (by rfl) ?_
  refine selected_run (equation := shiftProgram[24])
    (environment := [("i", .sym "not-a-number"), ("amount", natural 1),
      ("cutoff", natural 0)]) (by rfl) (by rfl) ?_
  change eval P H 11 _ (.expr [.sym "vibe:shift-bvar-closed",
    .expr [.sym "nik:nat-le", .expr [.sym "nik:nat-add", .var "i", natural 1], .var "cutoff"],
    .var "i", .var "amount"]) = .failure
  refine call_first_fault (fuel := 10) (by simp [Special]) ?_
  refine call_first_fault (fuel := 9) (by simp [Special]) ?_
  exact call_run (fuel := 8) (values := [.sym "not-a-number", natural 1]) (by simp [Special])
    (.cons (variable_run (by decide) (by rfl)) (.cons (natural_run (by decide) 1) .nil))
    (primitive_fault (by rfl)
      (naturalArithmeticHost_non_natural (head := "nik:nat-add") (operation := .add)
        (by rfl) (.sym "not-a-number") (natural 1) (Or.inl rfl)))

theorem zero_fuel_exhaustion_is_not_refusal :
    apply P H 0 "vibe:shift" [encodeTable [], encode (.bvar 0), natural 1, natural 0] = .exhausted := rfl

theorem completed_valid_input_cannot_fault (table : SignatureTable) (amount cutoff fuel : Nat) (source : Spec.Term) :
    apply P H fuel "vibe:shift" [encodeTable table, encode source, natural amount, natural cutoff] ≠ .failure := by
  intro failed
  have computed := shift_completed_exact table amount cutoff fuel source
    (by rw [failed]; intro same; cases same)
  rw [failed] at computed
  cases computed

theorem snapshot_preserves_unknown_heads :
    signatureOf (snapshot (fun _ => none) (.app s [.app t [.bvar 0]])) s = none := rfl

theorem snapshot_reuses_exact_nested_information (signature : Spec.Sig) :
    signatureOf (snapshot signature (.app s [.app t [.bvar 0]])) t = signature t :=
  snapshot_lookup _ _ _ (by simp [termHeads, termHeadsList])

end Mettapedia.Languages.VibeITP.Presentation.ComputationalShift.Controls
