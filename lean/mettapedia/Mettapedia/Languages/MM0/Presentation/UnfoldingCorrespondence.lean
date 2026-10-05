import Mettapedia.Languages.MM0.Presentation.UnfoldingImages

/-!
# Authored unfolding agrees with the independent MM0 judgment

The computation consumes the actual declaration and definition stores and the
supplied parameter and dummy images. Acceptance reflects that precise request.
A completed refusal is distinct from exhaustion and from failure of an
unrelated proof or conversion.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions

open Kernel ComputationalContext ComputationalArguments ComputationalTyping
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => unfoldingProgram
local notation "H" => computationalHost

private theorem unfold_start (table : SignatureTable) (definitions : DefinitionTable) (target : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) (result : Term)
    (next : Applies P H "mm0:unfold-declaration"
      [encodeDeclarationResult (signatureOf table symbol), encodeTable table, encodeDefinitions definitions,
        encodeContext target, natural symbol, encodeExpressions arguments, encodeNaturals images] result) :
    Applies P H "mm0:unfold"
      [encodeTable table, encodeDefinitions definitions, encodeContext target,
        natural symbol, encodeExpressions arguments, encodeNaturals images] result := by
  refine Applies.equation (equation := P[141])
    (environment := [("table", encodeTable table), ("definitions", encodeDefinitions definitions),
      ("target", encodeContext target), ("symbol", natural symbol),
      ("arguments", encodeExpressions arguments), ("images", encodeNaturals images)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (declaration_reused table symbol)

private theorem declaration_admitted (table : SignatureTable) (definitions : DefinitionTable) (target : Context)
    (symbol : Nat) (declaration : TermDecl) (arguments : List Preterm) (images : List Nat) (result : Term)
    (next : Applies P H "mm0:unfold-body"
      [encodeBodyResult (definitionsOf definitions symbol), encodeTable table, encodeContext target,
        encodeContext declaration.arguments, encodeExpressions arguments, encodeNaturals images] result) :
    Applies P H "mm0:unfold-declaration"
      [encodeDeclarationResult (some declaration), encodeTable table, encodeDefinitions definitions,
        encodeContext target, natural symbol, encodeExpressions arguments, encodeNaturals images] result := by
  refine Applies.equation (equation := P[143])
    (environment := [("formal", encodeContext declaration.arguments), ("sort", natural declaration.resultSort),
      ("dependencies", encodeDependencies declaration.dependencies), ("table", encodeTable table),
      ("definitions", encodeDefinitions definitions), ("target", encodeContext target),
      ("symbol", natural symbol), ("arguments", encodeExpressions arguments), ("images", encodeNaturals images)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (definition_lookup_reused definitions symbol)

private theorem body_admitted (table : SignatureTable) (target formal : Context)
    (arguments : List Preterm) (images : List Nat) (body : Definition.Body) (result : Term)
    (next : Applies P H "mm0:unfold-arguments"
      [boolean (Substitution.checkArguments (signatureOf table) target arguments formal), encodeContext target,
        encodeExpressions arguments, encodeNaturals body.dummies, encodeNaturals images, encode body.expression]
      result) :
    Applies P H "mm0:unfold-body"
      [encodeBodyResult (some body), encodeTable table, encodeContext target, encodeContext formal,
        encodeExpressions arguments, encodeNaturals images] result := by
  refine Applies.equation (equation := P[145])
    (environment := [("dummies", encodeNaturals body.dummies), ("expression", encode body.expression),
      ("table", encodeTable table), ("target", encodeContext target), ("formal", encodeContext formal),
      ("arguments", encodeExpressions arguments), ("images", encodeNaturals images)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
    (arguments_reused table target arguments formal)

private theorem arguments_admitted (target : Context) (arguments : List Preterm)
    (images : List Nat) (body : Definition.Body) (result : Term)
    (next : Applies P H "mm0:unfold-dummies"
      [boolean (Definition.checkDummies target arguments body.dummies images),
        encodeExpressions arguments, encodeNaturals images, encode body.expression] result) :
    Applies P H "mm0:unfold-arguments"
      [.sym "True", encodeContext target, encodeExpressions arguments, encodeNaturals body.dummies,
        encodeNaturals images, encode body.expression] result := by
  refine Applies.equation (equation := P[147])
    (environment := [("target", encodeContext target), ("arguments", encodeExpressions arguments),
      ("dummies", encodeNaturals body.dummies), ("images", encodeNaturals images), ("expression", encode body.expression)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
    (fresh_reused "mm0:check-dummies" (by
      simp only [ComputationalFreshDummies.freshProgram, ComputationalFreshDummies.freshEquations,
        encodeBinder, encodeDependencies, encodeNaturals, Finset.sort_empty]
      decide) _ _
      (ComputationalFreshDummies.dummies_computes target arguments body.dummies images))

theorem unfolding_computes (table : SignatureTable) (definitions : DefinitionTable) (target : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) :
    Applies P H "mm0:unfold"
      [encodeTable table, encodeDefinitions definitions, encodeContext target,
        natural symbol, encodeExpressions arguments, encodeNaturals images]
      (encodeResult (Definition.unfold? (signatureOf table) (definitionsOf definitions) target symbol arguments images)) := by
  apply unfold_start
  cases termLookup : signatureOf table symbol with
  | none =>
      simp only [Definition.unfold?, termLookup, encodeResult, encodeDeclarationResult]
      exact ⟨1, rfl⟩
  | some declaration =>
      simp only [Definition.unfold?, termLookup]
      apply declaration_admitted
      cases bodyLookup : definitionsOf definitions symbol with
      | none =>
          simp only [encodeResult, encodeBodyResult, Option.map_none, encodeLookupResult]
          exact ⟨1, rfl⟩
      | some body =>
          change Applies P H "mm0:unfold-body"
            [encodeBodyResult (some body), encodeTable table, encodeContext target,
              encodeContext declaration.arguments, encodeExpressions arguments, encodeNaturals images]
            (encodeResult (if Substitution.checkArguments (signatureOf table) target arguments declaration.arguments &&
              Definition.checkDummies target arguments body.dummies images then
              body.expression.substitute (Substitution.ofList (Definition.substitutionValues arguments images)) else none))
          apply body_admitted
          cases typed : Substitution.checkArguments (signatureOf table) target arguments declaration.arguments with
          | false =>
              simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, boolean, encodeResult]
              exact ⟨1, rfl⟩
          | true =>
              simp only [Bool.true_and, boolean]
              apply arguments_admitted
              cases fresh : Definition.checkDummies target arguments body.dummies images with
              | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte, boolean, encodeResult]
                  exact ⟨1, rfl⟩
              | true =>
                  simp only [↓reduceIte, boolean]
                  exact admitted_body_computes arguments images body.expression

theorem unfolding_result_exact (table : SignatureTable) (definitions : DefinitionTable) (target : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) (result : Term) :
    Applies P H "mm0:unfold"
      [encodeTable table, encodeDefinitions definitions, encodeContext target,
        natural symbol, encodeExpressions arguments, encodeNaturals images] result ↔
      result = encodeResult (Definition.unfold? (signatureOf table) (definitionsOf definitions) target symbol arguments images) := by
  constructor
  · exact fun run => run.deterministic (unfolding_computes table definitions target symbol arguments images)
  · rintro rfl; exact unfolding_computes table definitions target symbol arguments images

theorem unfolding_accepts_iff (table : SignatureTable) (definitions : DefinitionTable) (target : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) (result : Preterm) :
    Applies P H "mm0:unfold"
      [encodeTable table, encodeDefinitions definitions, encodeContext target,
        natural symbol, encodeExpressions arguments, encodeNaturals images] (encodeResult (some result)) ↔
      Definition.Unfolds (signatureOf table) (definitionsOf definitions) target symbol arguments images result := by
  rw [unfolding_result_exact, ← Definition.unfold_eq_some_iff]
  constructor
  · exact fun same => (encodeResult_injective same).symm
  · exact fun same => congrArg encodeResult same.symm

theorem unfolding_refuses_iff (table : SignatureTable) (definitions : DefinitionTable) (target : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) :
    Applies P H "mm0:unfold"
      [encodeTable table, encodeDefinitions definitions, encodeContext target,
        natural symbol, encodeExpressions arguments, encodeNaturals images] (.sym "None") ↔
      ¬ ∃ result, Definition.Unfolds (signatureOf table) (definitionsOf definitions) target symbol arguments images result := by
  rw [unfolding_result_exact, ← Definition.unfold_none_iff]
  constructor
  · exact fun same => (encodeResult_injective (show encodeResult none = _ from same)).symm
  · exact fun same => congrArg encodeResult same.symm

theorem admitted_body_has_typed_result (table : SignatureTable) (definitions : DefinitionTable) (target : Context)
    (symbol : Nat) (declaration : TermDecl) (body : Definition.Body)
    (termLookup : signatureOf table symbol = some declaration) (bodyLookup : definitionsOf definitions symbol = some body)
    (arguments : List Preterm) (images : List Nat)
    (typed : List.Forall₂ (Preterm.FitsBinder (signatureOf table) target) arguments declaration.arguments)
    (fresh : Definition.FreshDummies target arguments body.dummies images)
    (bodyTyped : Preterm.HasType (signatureOf table) (declaration.arguments ++ body.dummies.map Kernel.Binder.bound)
      body.expression [] declaration.resultSort) :
    ∃ result, Applies P H "mm0:unfold"
      [encodeTable table, encodeDefinitions definitions, encodeContext target,
        natural symbol, encodeExpressions arguments, encodeNaturals images] (encodeResult (some result)) ∧
      Preterm.HasType (signatureOf table) target result [] declaration.resultSort := by
  obtain ⟨result, computed, resultTyped⟩ := Definition.unfold_typed_total termLookup bodyLookup typed fresh bodyTyped
  exact ⟨result, (unfolding_accepts_iff _ _ _ _ _ _ _).mpr
    ((Definition.unfold_eq_some_iff _ _ _ _ _ _ _).mp computed), resultTyped⟩

theorem unfolding_completed_result (table : SignatureTable) (definitions : DefinitionTable) (target : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) (fuel : Nat)
    (finished : apply P H fuel "mm0:unfold"
      [encodeTable table, encodeDefinitions definitions, encodeContext target,
        natural symbol, encodeExpressions arguments, encodeNaturals images] ≠ .exhausted) :
    apply P H fuel "mm0:unfold"
      [encodeTable table, encodeDefinitions definitions, encodeContext target,
        natural symbol, encodeExpressions arguments, encodeNaturals images] =
      .value (encodeResult (Definition.unfold? (signatureOf table) (definitionsOf definitions) target symbol arguments images)) :=
  (unfolding_computes table definitions target symbol arguments images).completed fuel finished

end Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions
