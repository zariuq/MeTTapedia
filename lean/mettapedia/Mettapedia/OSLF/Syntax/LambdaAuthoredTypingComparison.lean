import Mettapedia.OSLF.Syntax.LambdaAuthoredCanonicalFreeComparison
import Mettapedia.OSLF.Syntax.LambdaPatternRendering
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Intrinsic lambda terms in the authored typing judgment

Every intrinsically scoped lambda term renders as an object term of the same
four-rule authored language, at the exact context obtained by mapping its
sorts to authored type expressions. The proof uses the declaration-derived
checker and then its established soundness theorem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaAuthoredTypingComparison

open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison
open Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile
open Mettapedia.OSLF.Binding.LambdaAuthoredCanonicalFreeComparison
open Mettapedia.OSLF.Binding.LambdaPatternRendering
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ScopedOperationalCertification
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef.WellSorted

private def termType : TypeExpr := .base "Term"

/-- The authored context corresponding to an intrinsic one-sort context. -/
def contextTypes (Γ : Ctx sig) : List TypeExpr :=
  Γ.map fun _ => termType

private theorem contextTypes_var : ∀ {Γ : Ctx sig} (v : Var Γ .term),
    (contextTypes Γ)[(varIdx v).val]? = some termType
  | _, .zero => rfl
  | _, .succ v => by simp [contextTypes, varIdx]

private def appDecl : GrammarRule :=
  language.terms.get ⟨0, by decide +kernel⟩

private def lamDecl : GrammarRule :=
  language.terms.get ⟨1, by decide +kernel⟩

private theorem appDecl_member : appDecl ∈ language.terms := by
  decide +kernel

private theorem lamDecl_member : lamDecl ∈ language.terms := by
  decide +kernel

private theorem appDecl_fields :
    appDecl.label = "App" ∧ appDecl.category = "Term" ∧
    appDecl.params = [.simple "f" termType, .simple "a" termType] ∧
    usesBareCollection? appDecl = false := by
  decide +kernel

private theorem lamDecl_fields :
    lamDecl.label = "Lam" ∧ lamDecl.category = "Term" ∧
    lamDecl.params =
      [.abstractionNamed (some "x") "body" (.arrow termType termType)] ∧
    usesBareCollection? lamDecl = false := by
  decide +kernel

private theorem check_app {Γ : Ctx sig} (f a : Pattern)
    (hf : checkHasType language FreeTypeContext.empty
      (contextTypes Γ) f termType = true)
    (ha : checkHasType language FreeTypeContext.empty
      (contextTypes Γ) a termType = true) :
    checkHasType language FreeTypeContext.empty (contextTypes Γ)
      (.apply "App" [f, a]) termType = true := by
  simp only [checkHasType, List.any_eq_true]
  refine ⟨appDecl, appDecl_member, ?_⟩
  obtain ⟨hlabel, hcategory, hparams, hbare⟩ := appDecl_fields
  simp [hlabel, hcategory, hparams, hbare,
    checkArgumentsHaveTypes, matchesParameterRepresentation?,
    parameterType?, termType]
  exact ⟨by simpa only [termType] using hf,
    by simpa only [termType] using ha⟩

private theorem check_lam {Γ : Ctx sig} (body : Pattern)
    (hbody : checkHasType language FreeTypeContext.empty
      (termType :: contextTypes Γ) body termType = true) :
    checkHasType language FreeTypeContext.empty (contextTypes Γ)
      (.apply "Lam" [.lambda none body]) termType = true := by
  simp only [checkHasType, List.any_eq_true]
  refine ⟨lamDecl, lamDecl_member, ?_⟩
  obtain ⟨hlabel, hcategory, hparams, hbare⟩ := lamDecl_fields
  simp [hlabel, hcategory, hparams, hbare,
    checkArgumentsHaveTypes, matchesParameterRepresentation?,
    parameterType?, checkHasType, termType]
  simpa only [termType] using hbody

private def ArgsChecked : ∀ {arity : List (List Srt × Srt)}
    {Γ : Ctx sig}, Args sig arity Γ → Prop
  | _, _, .nil => True
  | _, Γ, .cons (bs := bs) head tail =>
      checkHasType language FreeTypeContext.empty
        (contextTypes (bs ++ Γ)) (encodeTerm head) termType = true ∧
      ArgsChecked tail

mutual

/-- The actual four-rule authored checker accepts every rendered intrinsic
term, in every ambient binding context. -/
theorem encodeTerm_checked : ∀ {Γ : Ctx sig} {s : Srt} (t : Term sig Γ s),
    checkHasType language FreeTypeContext.empty (contextTypes Γ)
      (encodeTerm t) termType = true
  | _, .term, .var v => by
      simp [encodeTerm, checkHasType, contextTypes_var v]
  | Γ, _, .op .app (.cons f (.cons a .nil)) => by
      have hall : ArgsChecked (.cons f (.cons a .nil)) :=
        encodeArgs_checked _
      obtain ⟨hf, ha, _⟩ := hall
      change checkHasType language FreeTypeContext.empty (contextTypes _)
        (.apply "App" [encodeTerm f, encodeTerm a]) termType = true
      exact check_app (encodeTerm f) (encodeTerm a) hf ha
  | Γ, _, .op .lam (.cons body .nil) => by
      have hall : ArgsChecked (.cons body .nil) :=
        encodeArgs_checked _
      obtain ⟨hbody, _⟩ := hall
      change checkHasType language FreeTypeContext.empty (contextTypes _)
        (.apply "Lam" [.lambda none (encodeTerm body)]) termType = true
      exact check_lam (encodeTerm body) hbody

private theorem encodeArgs_checked : ∀ {arity : List (List Srt × Srt)}
    {Γ : Ctx sig} (args : Args sig arity Γ), ArgsChecked args
  | _, _, .nil => trivial
  | _, _, .cons head tail =>
      ⟨encodeTerm_checked head, encodeArgs_checked tail⟩

end

/-- Executable acceptance reflects the one declaration-derived typing
judgment; no second intrinsic-specific source typing system is introduced. -/
theorem encodeTerm_hasType {Γ : Ctx sig} (t : Term sig Γ .term) :
    HasType language FreeTypeContext.empty (contextTypes Γ)
      (encodeTerm t) termType :=
  checkHasType_sound (encodeTerm_checked t)

/-- Rendering an intrinsic simultaneous substitution agrees with the
authored pattern substitution and keeps the resulting term in its target
context. The existing binding comparison supplies the equality; the
declaration-derived typing theorem supplies its type. -/
theorem encoded_substitution_hasType {Γ Δ : Ctx sig}
    (sigma : Sub sig Γ Δ) (term : Term sig Γ .term) :
    HasType language FreeTypeContext.empty (contextTypes Δ)
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
        (Mettapedia.OSLF.Binding.PatternRendering.encodeSub
          rendering sigma) (encodeTerm term)) termType := by
  rw [← encodeTerm_bind sigma term]
  exact encodeTerm_hasType (bind sigma term)

/-- A left-application firing from the actual engine has the authored
typing judgment at both endpoints and a certified free firing witness. -/
theorem beta_under_appL_typed_certified {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument outer : Term sig Γ .term) :
    HasType language FreeTypeContext.empty (contextTypes Γ)
        (encodeTerm (appT (appT (lamT body) argument) outer)) termType ∧
    HasType language FreeTypeContext.empty (contextTypes Γ)
        (encodeTerm (appT (inst body argument) outer)) termType ∧
    ∃ tree : (presentation RelationEnv.empty language).Derivation ()
        ⟨2, Γ.length,
          encodeTerm (appT (appT (lamT body) argument) outer),
          encodeTerm (appT (inst body argument) outer)⟩,
      CertifiedTree RelationEnv.empty language _ tree ∧
        Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
          RelationEnv.empty language _ tree =
            some (.fire 2 [.step 0 0 (.fire 0 [])]) :=
  ⟨encodeTerm_hasType _, encodeTerm_hasType _,
    beta_under_appL_certified body argument outer⟩

/-- The right-application firing preserves its separate rule and history
while both endpoints use the same authored typing judgment. -/
theorem beta_under_appR_typed_certified {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument outer : Term sig Γ .term) :
    HasType language FreeTypeContext.empty (contextTypes Γ)
        (encodeTerm (appT outer (appT (lamT body) argument))) termType ∧
    HasType language FreeTypeContext.empty (contextTypes Γ)
        (encodeTerm (appT outer (inst body argument))) termType ∧
    ∃ tree : (presentation RelationEnv.empty language).Derivation ()
        ⟨2, Γ.length,
          encodeTerm (appT outer (appT (lamT body) argument)),
          encodeTerm (appT outer (inst body argument))⟩,
      CertifiedTree RelationEnv.empty language _ tree ∧
        Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
          RelationEnv.empty language _ tree =
            some (.fire 3 [.step 0 0 (.fire 0 [])]) :=
  ⟨encodeTerm_hasType _, encodeTerm_hasType _,
    beta_under_appR_certified body argument outer⟩

/-- A raw index with no corresponding ambient binder is rejected by the
same authored checker. -/
theorem unbound_root_rejected :
    checkHasType language FreeTypeContext.empty [] (.bvar 0) termType = false :=
  rfl

#print axioms encodeTerm_checked
#print axioms encodeTerm_hasType
#print axioms encoded_substitution_hasType
#print axioms beta_under_appL_typed_certified
#print axioms beta_under_appR_typed_certified
#print axioms unbound_root_rejected

end Mettapedia.OSLF.Binding.LambdaAuthoredTypingComparison
