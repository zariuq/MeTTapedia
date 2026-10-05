import Mettapedia.Languages.MM0.Presentation.TypingLookup

/-!
# Authored MM0 typing agrees with independent typing

The proof follows finite input structure and composes the actual selected
equation bodies. It covers successful typing and completed refusal for all
finite signature tables, contexts and preterms, without assuming well-formed
input declarations. Theory admission supplies that additional invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalTyping

open Kernel ComputationalContext
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => typingProgram
local notation "H" => computationalHost

private theorem binder_computes (binder : Option Kernel.Binder) :
    Applies P H "mm0:infer-binder" [encodeBinderResult binder]
      (encodeType (binder.map fun binder => ([], binder.sort))) := by
  cases binder with
  | none => exact ⟨1, rfl⟩
  | some binder => cases binder <;> exact ⟨2, rfl⟩

private theorem declaration_type_computes (declaration : Option TermDecl) :
    Applies P H "mm0:infer-declaration" [encodeDeclarationResult declaration]
      (encodeType (declaration.map fun decl => (decl.arguments, decl.resultSort))) := by
  cases declaration <;> exact ⟨2, rfl⟩

private theorem variable_computes (table : SignatureTable) (context : Context) (index : Nat) :
    Applies P H "mm0:infer" [encodeTable table, encodeContext context, encode (.var index)]
      (encodeType (Preterm.infer (signatureOf table) context (.var index))) := by
  have outcome : Preterm.infer (signatureOf table) context (.var index) =
      context[index]?.map (fun binder => ([], binder.sort)) := by
    cases found : context[index]? <;> simp [Preterm.infer, found]
  rw [outcome]
  refine Applies.equation (equation := P[10])
    (environment := [("table", encodeTable table), ("context", encodeContext context),
      ("index", natural index)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (binder_computes context[index]?)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (context_lookup_computes context index)

private theorem term_computes (table : SignatureTable) (context : Context) (index : Nat) :
    Applies P H "mm0:infer" [encodeTable table, encodeContext context, encode (.term index)]
      (encodeType (Preterm.infer (signatureOf table) context (.term index))) := by
  have outcome : Preterm.infer (signatureOf table) context (.term index) =
      (signatureOf table index).map (fun decl => (decl.arguments, decl.resultSort)) := by
    cases found : signatureOf table index <;> simp [Preterm.infer, found]
  rw [outcome]
  refine Applies.equation (equation := P[11])
    (environment := [("table", encodeTable table), ("context", encodeContext context),
      ("index", natural index)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (declaration_type_computes (signatureOf table index))
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (declaration_computes table index)

private theorem sort_computes (actual expected : Nat) (rest : Context) (result : Nat) :
    Applies P H "mm0:infer-sort-equal"
      [boolean (decide (actual = expected)), encodeContext rest, natural result]
      (encodeType (if actual = expected then some (rest, result) else none)) := by
  by_cases same : actual = expected
  · simp only [same, ↓reduceIte, decide_true, boolean]
    exact ⟨2, rfl⟩
  · simp only [same, ↓reduceIte, decide_false, boolean, Bool.false_eq_true]
    exact ⟨1, rfl⟩

private theorem bound_type_computes (actual : Option Nat) (expected : Nat) (rest : Context) (result : Nat) :
    Applies P H "mm0:infer-bound-sort" [encodeSortResult actual, natural expected, encodeContext rest, natural result]
      (encodeType (if actual = some expected then some (rest, result) else none)) := by
  cases actual with
  | none => exact ⟨1, rfl⟩
  | some actual =>
    simp only [Option.some.injEq]
    refine Applies.equation (equation := P[30])
      (environment := [("sort", natural actual), ("expected", natural expected),
        ("rest", encodeContext rest), ("result", natural result)]) (by rfl) (by rfl) ?_
    refine Evaluates.call (by simp [Special])
      (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
      (sort_computes actual expected rest result)
    exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (equal_applies actual expected)

private theorem saturated_computes (remaining rest : Context) (actual expected result : Nat) :
    Applies P H "mm0:infer-saturated"
      [listView (remaining.map encodeBinder), natural actual, natural expected, encodeContext rest, natural result]
      (encodeType (if (remaining, actual) = ([], expected) then some (rest, result) else none)) := by
  cases remaining with
  | nil =>
    simp only [Prod.mk.injEq, true_and]
    refine Applies.equation (equation := P[33])
      (environment := [("sort", natural actual), ("expected", natural expected),
        ("rest", encodeContext rest), ("result", natural result)]) (by rfl) (by rfl) ?_
    refine Evaluates.call (by simp [Special])
      (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
      (sort_computes actual expected rest result)
    exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (equal_applies actual expected)
  | cons first tail =>
    simp only [Prod.mk.injEq, List.cons_ne_nil, false_and, ↓reduceIte]
    exact ⟨1, rfl⟩

private theorem regular_type_computes (actual : Option ExpressionType) (expected : Nat)
    (rest : Context) (result : Nat) :
    Applies P H "mm0:infer-regular-type"
      [encodeType actual, natural expected, encodeContext rest, natural result]
      (encodeType (if actual = some ([], expected) then some (rest, result) else none)) := by
  cases actual with
  | none => exact ⟨1, rfl⟩
  | some actual =>
    obtain ⟨remaining, actual⟩ := actual
    simp only [Option.some.injEq]
    refine Applies.equation (equation := P[32])
      (environment := [("remaining", encodeContext remaining), ("sort", natural actual),
        ("expected", natural expected), ("rest", encodeContext rest), ("result", natural result)])
      (by rfl) (by rfl) ?_
    refine Evaluates.call (by simp [Special])
      (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
      (saturated_computes remaining rest actual expected result)
    exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies _)

private theorem bound_argument_computes (table : SignatureTable) (context rest : Context)
    (argument : Preterm) (sort result : Nat) :
    Applies P H "mm0:infer-arguments"
      [listView ((.bound sort :: rest).map encodeBinder), natural result,
        encodeTable table, encodeContext context, encode argument]
      (encodeType (if Preterm.boundSort? context argument = some sort then some (rest, result) else none)) := by
  refine Applies.equation (equation := P[21])
    (environment := [("sort", natural sort), ("rest", encodeContext rest), ("result", natural result),
      ("table", encodeTable table), ("context", encodeContext context), ("argument", encode argument)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
    (bound_type_computes (Preterm.boundSort? context argument) sort rest result)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (bound_sort_computes context argument)

private theorem regular_argument_computes (table : SignatureTable) (context rest : Context)
    (argument : Preterm) (sort result : Nat) (dependencies : Finset Nat)
    (child : Applies P H "mm0:infer" [encodeTable table, encodeContext context, encode argument]
      (encodeType (Preterm.infer (signatureOf table) context argument))) :
    Applies P H "mm0:infer-arguments"
      [listView ((.regular sort dependencies :: rest).map encodeBinder), natural result,
        encodeTable table, encodeContext context, encode argument]
      (encodeType (if Preterm.infer (signatureOf table) context argument = some ([], sort)
        then some (rest, result) else none)) := by
  refine Applies.equation (equation := P[22])
    (environment := [("sort", natural sort), ("dependencies", encodeDependencies dependencies),
      ("rest", encodeContext rest), ("result", natural result), ("table", encodeTable table),
      ("context", encodeContext context), ("argument", encode argument)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
    (regular_type_computes (Preterm.infer (signatureOf table) context argument) sort rest result)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) child

private theorem function_start (table : SignatureTable) (context remaining : Context)
    (argument : Preterm) (sort : Nat) (result : Term)
    (next : Applies P H "mm0:infer-arguments" [listView (remaining.map encodeBinder), natural sort,
      encodeTable table, encodeContext context, encode argument] result) :
    Applies P H "mm0:infer-function"
      [encodeType (some (remaining, sort)), encodeTable table, encodeContext context, encode argument] result := by
  refine Applies.equation (equation := P[19])
    (environment := [("arguments", encodeContext remaining), ("result", natural sort),
      ("table", encodeTable table), ("context", encodeContext context), ("argument", encode argument)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies _)

private theorem application_start (table : SignatureTable) (context : Context)
    (function argument : Preterm) (middle result : Term)
    (child : Applies P H "mm0:infer" [encodeTable table, encodeContext context, encode function] middle)
    (next : Applies P H "mm0:infer-function" [middle, encodeTable table, encodeContext context, encode argument] result) :
    Applies P H "mm0:infer" [encodeTable table, encodeContext context, encode (.app function argument)] result := by
  refine Applies.equation (equation := P[12])
    (environment := [("table", encodeTable table), ("context", encodeContext context),
      ("function", encode function), ("argument", encode argument)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) child

theorem infer_computes (table : SignatureTable) (context : Context) (expression : Preterm) :
    Applies P H "mm0:infer" [encodeTable table, encodeContext context, encode expression]
      (encodeType (Preterm.infer (signatureOf table) context expression)) := by
  induction expression with
  | var index => exact variable_computes table context index
  | term index => exact term_computes table context index
  | app function argument ihFunction ihArgument =>
    apply application_start table context function argument _ _ ihFunction
    cases found : Preterm.infer (signatureOf table) context function with
    | none => simp only [Preterm.infer, found]; exact ⟨1, rfl⟩
    | some type =>
      obtain ⟨remaining, sort⟩ := type
      simp only [Preterm.infer, found]
      apply function_start
      cases remaining with
      | nil => exact ⟨1, rfl⟩
      | cons binder rest =>
        cases binder with
        | bound expected => exact bound_argument_computes table context rest argument expected sort
        | regular expected dependencies =>
          exact regular_argument_computes table context rest argument expected sort dependencies ihArgument

theorem infer_result_exact (table : SignatureTable) (context : Context) (expression : Preterm) (result : Term) :
    Applies P H "mm0:infer" [encodeTable table, encodeContext context, encode expression] result ↔
      result = encodeType (Preterm.infer (signatureOf table) context expression) := by
  constructor
  · exact fun run => run.deterministic (infer_computes table context expression)
  · rintro rfl
    exact infer_computes table context expression

theorem infer_accepts_iff (table : SignatureTable) (context remaining : Context)
    (expression : Preterm) (sort : Nat) :
    Applies P H "mm0:infer" [encodeTable table, encodeContext context, encode expression]
      (encodeType (some (remaining, sort))) ↔
      Preterm.HasType (signatureOf table) context expression remaining sort := by
  rw [infer_result_exact]
  constructor
  · exact fun same => Preterm.infer_sound (encodeType_injective same).symm
  · exact fun typing => congrArg encodeType typing.eval.symm

theorem infer_refuses_iff (table : SignatureTable) (context : Context) (expression : Preterm) :
    Applies P H "mm0:infer" [encodeTable table, encodeContext context, encode expression] (.sym "None") ↔
      ¬ ∃ remaining sort, Preterm.HasType (signatureOf table) context expression remaining sort := by
  rw [infer_result_exact]
  constructor
  · intro same
    change encodeType none = _ at same
    exact (Preterm.infer_none_iff _ _ _).mp (encodeType_injective same).symm
  · intro refused
    rw [(Preterm.infer_none_iff _ _ _).mpr refused]
    rfl

theorem infer_completed_result (table : SignatureTable) (context : Context) (expression : Preterm) (fuel : Nat)
    (finished : apply P H fuel "mm0:infer" [encodeTable table, encodeContext context, encode expression] ≠ .exhausted) :
    apply P H fuel "mm0:infer" [encodeTable table, encodeContext context, encode expression] =
      .value (encodeType (Preterm.infer (signatureOf table) context expression)) :=
  (infer_computes table context expression).completed fuel finished

end Mettapedia.Languages.MM0.Presentation.ComputationalTyping
