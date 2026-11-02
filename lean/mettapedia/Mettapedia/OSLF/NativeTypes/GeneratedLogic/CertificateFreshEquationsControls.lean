import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateFreshEquations

/-!
# Controls: a certificate for the η-law

A language of abstractions and applications with the η-law `Lam (λx. App F x) = F` (`etaCalc`). Read with fresh values
(`freshReading`), `F` stands for a closed term: the law's side condition, `x` not free in `F`.

- **The certificate passes the fresh check** (`eta_checked`). Its model reads an abstraction as whether it is constant,
  `Lam` as negation, and `App f a` as `a` when `f` holds and as true otherwise. Both directions of η hold under every
  fresh table, where `F` is a constant. So it respects the fresh reading (`eta_respected`).
- **The law relates what it should**: `Lam (λx. App K x)` is `K` in the fresh reading (`eta_instance`).
- **The certificate separates what the law must not relate**: `Lam (λy. Lam (λx. App x x))` and `Lam (λy. y)` have
  different values (`apart`), so they are not equivalent in the fresh reading (`fresh_apart`).
- **The syntax theory relates them** (`syntax_relates`): matched by the scoped instantiation, `F` is bound to `x`, and
  put back under one binder fewer it names `y`. So no certificate that separates them respects the syntax theory
  (`syntax_not_respected`).
- **A model that breaks η is refused** (`identity_refused`): with `Lam` read as the identity, the check fails.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.FreshEquationControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.Framework.FiniteModels (FiniteModel value)
open Mettapedia.OSLF.MeTTaIL.Match (applyBindings applyBindingsScoped captureDepth captureDepthList)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext UsesBareCollection)

/-- `Lam (λ. body)`. -/
def lam (body : Pattern) : Pattern := .apply "Lam" [.lambda none body]

/-- `App function argument`. -/
def app (function argument : Pattern) : Pattern := .apply "App" [function, argument]

/-- The constant `K`. -/
def konst : Pattern := .apply "K" []

/-- **The η-law** `Lam (λx. App F x) = F`. -/
def eta : Equation :=
  { name := "Eta", typeContext := [("F", .base "Term")], premises := [], left := lam (app (.fvar "F") (.bvar 0)),
    right := .fvar "F" }

/-- Abstractions, applications, a constant, and η. -/
def etaCalc : LanguageDef :=
  { name := "Eta", types := ["Term"],
    terms := [
      { label := "Lam", category := "Term", params := [.abstraction "body" (.arrow (.base "Term") (.base "Term"))],
        syntaxPattern := [] },
      { label := "App", category := "Term", params := [.simple "f" (.base "Term"), .simple "a" (.base "Term")],
        syntaxPattern := [] },
      { label := "K", category := "Term", params := [], syntaxPattern := [] }],
    equations := [eta], rewrites := [] }

/-- The reading of η with fresh values. -/
def freshReading : LanguageReading := { equations := .instances .fresh }

/-! ## The certificate -/

/-- An abstraction is whether it is constant; `Lam` negates; `App f a` is `a` when `f` holds, and true otherwise. -/
def etaModel : FiniteModel Bool where
  junk := false
  lam function := function false == function true
  operation
    | "Lam", [body] => !body
    | "App", [function, argument] => if function then argument else true
    | _, _ => false

def etaCertificate : Mettapedia.OSLF.Framework.FiniteModels.Certificate Bool where
  elements := [false, true]
  complete := by decide
  model := etaModel
  below first second := first == second

theorem eta_contextual : etaCertificate.contextualValid etaCalc = true := by
  decide +kernel

/-- **The certificate passes the fresh check for η.** -/
theorem eta_checked : Certificate.freshEquationsValid etaCertificate etaCalc = true := by
  decide +kernel

/-- **It respects η read with fresh values.** -/
theorem eta_respected : RespectsEquations etaCertificate RelationEnv.empty etaCalc freshReading :=
  respectsEquations_of_freshEquationsValid eta_contextual eta_checked (by decide)

/-! ## What the law relates -/

/-- A single binding reads its metavariable. -/
theorem applyBindings_single (name : String) (value : Pattern) :
    applyBindings [(name, value)] (.fvar name) = value := by
  simp [applyBindings, List.find?]

theorem applyBindings_other {name other : String} (value : Pattern) (differs : other ≠ name) :
    applyBindings [(name, value)] (.fvar other) = .fvar other := by
  have notSame : (name == other) = false := by simpa [beq_eq_false_iff_ne] using Ne.symm differs
  simp only [applyBindings, List.find?, notSame]

/-- The matcher binds `F` to the function an η-redex applies. -/
theorem eta_matched (function : Pattern) :
    [("F", function)] ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern eta.left (lam (app function (.bvar 0))) :=
  Mettapedia.OSLF.MeTTaIL.MatchSpec.matchRel_complete
    (.apply (.cons (.lambda (.apply (.cons .fvar (.cons .bvar .nil rfl) rfl) rfl)) .nil rfl) rfl)

/-- `K` is a term. -/
theorem konst_typed : HasType etaCalc FreeTypeContext.empty [] konst (.base "Term") :=
  HasType.constructor (rule := { label := "K", category := "Term", params := [], syntaxPattern := [] })
    (by simp [etaCalc]) (by simp [UsesBareCollection, GrammarRule.bareParams]) .nil

/-- **`Lam (λx. App K x)` is `K`**, in the fresh reading. -/
theorem eta_instance : ObjectStep RelationEnv.empty etaCalc freshReading (lam (app konst (.bvar 0))) konst := by
  refine ⟨rfl, rfl, ?_⟩
  show DisciplinedStep RelationEnv.empty etaCalc .fresh _ _
  have step := DisciplinedStep.inContext (relEnv := RelationEnv.empty) (language := etaCalc) (discipline := .fresh)
    .hole (Or.inl (DisciplinedEquation.forward (equation := eta) (source := lam (app konst (.bvar 0)))
      (initial := [("F", konst)]) (List.mem_singleton_self _) rfl (eta_matched konst) (PremisesValid.nil _)
      (fun name type member => by
        simp only [eta, List.mem_singleton, Prod.mk.injEq] at member
        obtain ⟨rfl, rfl⟩ := member
        rw [applyBindings_single]
        exact ⟨FreeTypeContext.empty, [], konst_typed⟩)
      (by
        intro name captured _ _
        by_cases same : name = "F"
        · subst same
          rw [applyBindings_single]
          rfl
        · rw [applyBindings_other konst same]
          rfl)))
  simpa [OneHoleContext.fill, applyBindingsScoped, eta, captureSitesOf, captureDepth, captureDepthList,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars, applyBindings_single, List.find?] using step

/-! ## What the law must not relate -/

/-- `Lam (λy. Lam (λx. App x x))`. -/
def selfApplier : Pattern := lam (lam (app (.bvar 0) (.bvar 0)))

/-- `Lam (λy. y)`. -/
def identityLam : Pattern := lam (.bvar 0)

/-- **The certificate tells them apart.** -/
theorem apart : value etaModel selfApplier ≠ value etaModel identityLam := by
  decide +kernel

/-- **So they are not equivalent in the fresh reading.** -/
theorem fresh_apart : ¬ ObjectEquivalent RelationEnv.empty etaCalc freshReading selfApplier identityLam :=
  not_objectEquivalent_of_value eta_respected apart

/-- **The syntax theory relates them**: the scoped instantiation binds `F` to `x` and puts it back under one binder
fewer, where it names `y`. -/
theorem syntax_relates : ObjectStep RelationEnv.empty etaCalc .syntax selfApplier identityLam := by
  refine ⟨rfl, rfl, ?_⟩
  show EquationStep RelationEnv.empty etaCalc selfApplier identityLam
  have step := EquationStep.inContext (relEnv := RelationEnv.empty) (language := etaCalc)
    (.apply "Lam" [] (.lambda none .hole) [])
    (Or.inl (AuthoredEquation.forward (equation := eta) (source := lam (app (.bvar 0) (.bvar 0)))
      (initial := [("F", .bvar 0)]) (List.mem_singleton_self _) rfl (eta_matched (.bvar 0)) (PremisesValid.nil _)))
  simpa [OneHoleContext.fill, applyBindingsScoped, eta, captureSitesOf, captureDepth, captureDepthList,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars, selfApplier, identityLam, lam, app, applyBindings_single]
    using step

/-- **No certificate that separates them respects the syntax theory.** -/
theorem syntax_not_respected : ¬ RespectsEquations etaCertificate RelationEnv.empty etaCalc .syntax :=
  fun respects => apart (respects _ _ (Relation.EqvGen.rel _ _ syntax_relates))

/-! ## A model that breaks η -/

/-- `Lam` read as the identity. -/
def identityModel : FiniteModel Bool := { etaModel with
  operation := fun
    | "Lam", [body] => body
    | "App", [function, argument] => if function then argument else true
    | _, _ => false }

def identityCertificate : Mettapedia.OSLF.Framework.FiniteModels.Certificate Bool :=
  { etaCertificate with model := identityModel }

/-- **The check refuses it.** -/
theorem identity_refused : Certificate.freshEquationsValid identityCertificate etaCalc = false := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.FreshEquationControls
