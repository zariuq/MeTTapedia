import Mettapedia.Languages.MM0.Presentation.FreeVariablesContributions
import Mettapedia.Languages.MM0.Presentation.TypingTheory

/-!
# Exact execution of MM0's complete free-variable computation

The authored equations traverse every finite preterm and consult the actual
signature and context. Their results and refusals agree with independently
defined binding judgments. Resource exhaustion remains an unfinished run.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalFreeVariables

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => freeVariablesProgram
local notation "A" => freeVariablesEquations
local notation "H" => computationalHost
local notation "R" => ComputationalSupport.encodeResult

private theorem variable_start (table : SignatureTable) (context : Context) (index : Nat)
    (arguments : List Preterm) (freeLists : List (List Nat)) (result : Term)
    (next : Applies P H "mm0:free-variable-spine"
      [listView (arguments.map encode), listView (freeLists.map encodeNaturals), encodeContext context, natural index] result) :
    Applies P H "mm0:free-spine" [encodeTable table, encodeContext context, encode (.var index),
      encodeExpressions arguments, encodeFreeLists freeLists] result := by
  refine free_equation (equation := A[30])
    (environment := [("table", encodeTable table), ("context", encodeContext context), ("index", natural index),
      ("arguments", encodeExpressions arguments), ("free-lists", encodeFreeLists freeLists)])
    (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (.primitive (by rfl) (computationalHost_list_view _))
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (.primitive (by rfl) (computationalHost_list_view _))

private theorem variable_computes (table : SignatureTable) (context : Context) (index : Nat)
    (arguments : List Preterm) (freeLists : List (List Nat)) :
    Applies P H "mm0:free-spine" [encodeTable table, encodeContext context, encode (.var index),
      encodeExpressions arguments, encodeFreeLists freeLists]
      (R (indicesSpine? (signatureOf table) context (.var index) arguments freeLists)) := by
  apply variable_start
  cases arguments with
  | nil =>
      cases freeLists with
      | nil =>
          refine free_equation (equation := A[31])
            (environment := [("context", encodeContext context), ("index", natural index)])
            (by decide) (by rfl) (by rfl) ?_
          refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil))
            (support_reused context (.var index))
          exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
            (.constructor (by rfl) (by rfl))
      | cons => exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
  | cons => exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩

private theorem contributed_computes (context formal : Context) (arguments : List Preterm)
    (dependencies : Finset Nat) (contribution : Option (List Nat)) :
    Applies P H "mm0:free-contributed" [R contribution, encodeContext context, encodeContext formal,
      encodeExpressions arguments, encodeDependencies dependencies]
      (R (contribution.bind fun free =>
        (images? context formal arguments (dependencies.sort (· ≤ ·))).map (free ++ ·))) := by
  cases contribution with
  | none => exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
  | some free =>
      refine free_equation (equation := A[40])
        (environment := [("free", encodeNaturals free), ("context", encodeContext context),
          ("formal", encodeContext formal), ("arguments", encodeExpressions arguments),
          ("dependencies", encodeDependencies dependencies)]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil))
        (contribution_tail_computes free _)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) (images_computes context formal arguments _)

private def typedResult (typed : Bool) (context formal : Context) (arguments : List Preterm)
    (freeLists : List (List Nat)) (dependencies : Finset Nat) : Option (List Nat) :=
  if typed then do
    let contributed ← contributions? context formal arguments formal freeLists
    let returned ← images? context formal arguments (dependencies.sort (· ≤ ·))
    pure (contributed ++ returned)
  else none

private theorem typed_computes (typed : Bool) (context formal : Context) (arguments : List Preterm)
    (freeLists : List (List Nat)) (dependencies : Finset Nat) :
    Applies P H "mm0:free-typed" [boolean typed, encodeContext context, encodeContext formal,
      encodeExpressions arguments, encodeFreeLists freeLists, encodeDependencies dependencies]
      (R (typedResult typed context formal arguments freeLists dependencies)) := by
  cases typed with
  | false => exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
  | true =>
      refine free_equation (equation := A[38])
        (environment := [("context", encodeContext context), ("formal", encodeContext formal),
          ("arguments", encodeExpressions arguments), ("free-lists", encodeFreeLists freeLists),
          ("dependencies", encodeDependencies dependencies)]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [R (contributions? context formal arguments formal freeLists),
        encodeContext context, encodeContext formal, encodeExpressions arguments, encodeDependencies dependencies])
        (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) ?_
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
          (contributions_computes context formal arguments formal freeLists)
      · simpa [typedResult, Option.map_eq_bind] using
          contributed_computes context formal arguments dependencies
            (contributions? context formal arguments formal freeLists)

private def headResult (table : SignatureTable) (context : Context) (arguments : List Preterm)
    (freeLists : List (List Nat)) (declaration : Option TermDecl) : Option (List Nat) := do
  let declaration ← declaration
  typedResult (Substitution.checkArguments (signatureOf table) context arguments declaration.arguments)
    context declaration.arguments arguments freeLists declaration.dependencies

private theorem head_computes (table : SignatureTable) (context : Context) (arguments : List Preterm)
    (freeLists : List (List Nat)) (declaration : Option TermDecl) :
    Applies P H "mm0:free-head" [encodeDeclarationResult declaration, encodeTable table,
      encodeContext context, encodeExpressions arguments, encodeFreeLists freeLists]
      (R (headResult table context arguments freeLists declaration)) := by
  cases declaration with
  | none => exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
  | some declaration =>
      refine free_equation (equation := A[36])
        (environment := [("formal", encodeContext declaration.arguments), ("sort", natural declaration.resultSort),
          ("dependencies", encodeDependencies declaration.dependencies), ("table", encodeTable table),
          ("context", encodeContext context), ("arguments", encodeExpressions arguments),
          ("free-lists", encodeFreeLists freeLists)]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))
        (typed_computes _ context declaration.arguments arguments freeLists declaration.dependencies)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) .nil))))
        (arguments_reused "mm0:check-arguments" (by decide) _ _
          (arguments_computes table context arguments declaration.arguments))

private theorem term_computes (table : SignatureTable) (context : Context) (symbol : Nat)
    (arguments : List Preterm) (freeLists : List (List Nat)) :
    Applies P H "mm0:free-spine" [encodeTable table, encodeContext context, encode (.term symbol),
      encodeExpressions arguments, encodeFreeLists freeLists]
      (R (indicesSpine? (signatureOf table) context (.term symbol) arguments freeLists)) := by
  refine free_equation (equation := A[34])
    (environment := [("table", encodeTable table), ("context", encodeContext context), ("symbol", natural symbol),
      ("arguments", encodeExpressions arguments), ("free-lists", encodeFreeLists freeLists)])
    (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
    (head_computes table context arguments freeLists (signatureOf table symbol))
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
    (typing_reused "mm0:declaration" (by decide) _ _ (declaration_computes table symbol))

private theorem application_next (table : SignatureTable) (context : Context) (function argument : Preterm)
    (arguments : List Preterm) (free : List Nat) (freeLists : List (List Nat)) (result : Term)
    (next : Applies P H "mm0:free-spine" [encodeTable table, encodeContext context, encode function,
      encodeExpressions (argument :: arguments), encodeFreeLists (free :: freeLists)] result) :
    Applies P H "mm0:free-argument" [R (some free), encodeTable table, encodeContext context,
      encode function, encode argument, encodeExpressions arguments, encodeFreeLists freeLists] result := by
  refine free_equation (equation := A[43])
    (environment := [("free", encodeNaturals free), ("table", encodeTable table), ("context", encodeContext context),
      ("function", encode function), ("argument", encode argument), ("arguments", encodeExpressions arguments),
      ("free-lists", encodeFreeLists freeLists)]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons ?_ (.cons ?_ .nil))))) next
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
      (.primitive (by rfl) (computationalHost_list_cons _ _))
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
      (.primitive (by rfl) (computationalHost_list_cons _ _))

private theorem application_start (table : SignatureTable) (context : Context) (function argument : Preterm)
    (arguments : List Preterm) (freeLists : List (List Nat)) (free : Option (List Nat)) (result : Term)
    (child : Applies P H "mm0:free-spine" [encodeTable table, encodeContext context, encode argument,
      encodeExpressions [], encodeFreeLists []] (R free))
    (next : Applies P H "mm0:free-argument" [R free, encodeTable table, encodeContext context,
      encode function, encode argument, encodeExpressions arguments, encodeFreeLists freeLists] result) :
    Applies P H "mm0:free-spine" [encodeTable table, encodeContext context, encode (.app function argument),
      encodeExpressions arguments, encodeFreeLists freeLists] result := by
  refine free_equation (equation := A[41])
    (environment := [("table", encodeTable table), ("context", encodeContext context),
      ("function", encode function), ("argument", encode argument), ("arguments", encodeExpressions arguments),
      ("free-lists", encodeFreeLists freeLists)]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ .nil))))) child

theorem spine_computes (table : SignatureTable) (context : Context) (source : Preterm)
    (arguments : List Preterm) (freeLists : List (List Nat)) :
    Applies P H "mm0:free-spine" [encodeTable table, encodeContext context, encode source,
      encodeExpressions arguments, encodeFreeLists freeLists]
      (R (indicesSpine? (signatureOf table) context source arguments freeLists)) := by
  induction source generalizing arguments freeLists with
  | var index => exact variable_computes table context index arguments freeLists
  | term symbol => exact term_computes table context symbol arguments freeLists
  | app function argument ihFunction ihArgument =>
      apply application_start table context function argument arguments freeLists _ _ (ihArgument [] [])
      cases known : indicesSpine? (signatureOf table) context argument [] [] with
      | none =>
          simp only [indicesSpine?, known, ComputationalSupport.encodeResult]
          exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
      | some free =>
          simpa [indicesSpine?, known] using application_next table context function argument arguments free freeLists _
            (ihFunction (argument :: arguments) (free :: freeLists))

theorem free_variables_computes (table : SignatureTable) (context : Context) (source : Preterm) :
    Applies P H "mm0:free-variables" [encodeTable table, encodeContext context, encode source]
      (R (indices? (signatureOf table) context source)) := by
  refine free_equation (equation := A[44])
    (environment := [("table", encodeTable table), ("context", encodeContext context), ("source", encode source)])
    (by decide) (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ .nil))))) (spine_computes table context source [] [])

theorem free_variables_result_exact (table : SignatureTable) (context : Context) (source : Preterm) (result : Term) :
    Applies P H "mm0:free-variables" [encodeTable table, encodeContext context, encode source] result ↔
      result = R (indices? (signatureOf table) context source) := by
  constructor
  · exact fun run => run.deterministic (free_variables_computes table context source)
  · rintro rfl; exact free_variables_computes table context source

theorem free_variables_accepts_iff (table : SignatureTable) (context : Context) (source : Preterm) (result : Finset Nat) :
    (∃ free, Applies P H "mm0:free-variables" [encodeTable table, encodeContext context, encode source]
      (R (some free)) ∧ free.toFinset = result) ↔ Preterm.FreeVars (signatureOf table) context source result := by
  constructor
  · rintro ⟨free, run, rfl⟩
    exact indices_sound (ComputationalSupport.encodeResult_injective
      ((free_variables_result_exact _ _ _ _).mp run)).symm
  · intro derived
    obtain ⟨free, computed, same⟩ := indices_complete derived
    exact ⟨free, by simpa only [computed] using free_variables_computes table context source, same⟩

theorem free_variables_refuses_iff (table : SignatureTable) (context : Context) (source : Preterm) :
    Applies P H "mm0:free-variables" [encodeTable table, encodeContext context, encode source] (.sym "None") ↔
      ¬ ∃ free, Preterm.FreeVars (signatureOf table) context source free := by
  rw [← indices_refusal_iff]
  constructor
  · intro run
    exact (ComputationalSupport.encodeResult_injective ((free_variables_result_exact _ _ _ _).mp run)).symm
  · intro refused
    simpa only [refused, ComputationalSupport.encodeResult] using free_variables_computes table context source

theorem free_variables_completed (table : SignatureTable) (context : Context) (source : Preterm) (fuel : Nat)
    (finished : apply P H fuel "mm0:free-variables" [encodeTable table, encodeContext context, encode source] ≠ .exhausted) :
    apply P H fuel "mm0:free-variables" [encodeTable table, encodeContext context, encode source] =
      .value (R (indices? (signatureOf table) context source)) :=
  (free_variables_computes table context source).completed fuel finished

theorem free_variables_eventually_stable (table : SignatureTable) (context : Context) (source : Preterm) :
    ∃ fuel, ∀ more, fuel ≤ more →
      apply P H more "mm0:free-variables" [encodeTable table, encodeContext context, encode source] =
        .value (R (indices? (signatureOf table) context source)) :=
  (free_variables_computes table context source).at_least

theorem theory_free_variables_computes (theory : Theory) (context : Context) (source : Preterm) :
    Applies P H "mm0:free-variables" [encodeTable theory.terms, encodeContext context, encode source]
      (R (indices? theory.termSignature context source)) := by
  simpa only [theory_signature] using free_variables_computes theory.terms context source

theorem theory_free_variables_accepts_iff (theory : Theory) (context : Context) (source : Preterm) (result : Finset Nat) :
    (∃ free, Applies P H "mm0:free-variables" [encodeTable theory.terms, encodeContext context, encode source]
      (R (some free)) ∧ free.toFinset = result) ↔ Preterm.FreeVars theory.termSignature context source result := by
  simpa only [theory_signature] using free_variables_accepts_iff theory.terms context source result

end Mettapedia.Languages.MM0.Presentation.ComputationalFreeVariables
