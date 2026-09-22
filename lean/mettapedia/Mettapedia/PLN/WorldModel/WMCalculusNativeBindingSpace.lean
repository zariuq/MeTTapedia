import Mettapedia.PLN.WorldModel.WMCalculusNativeSpace
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Binding-valued additive space observations

The MeTTaIL matcher returns a list of binding maps, including multiple
solutions from collection matching. Against an explicit candidate list, a
multiplicity space can therefore extract a bag of bindings. Pointwise binding
counts are additive over space union, making this a second, richer instance of
the WM observation contract and a consumer of native dependent predicates.

This result assumes the candidate list supplied with a query. It does not
prove that a storage index enumerates all matching atoms or that every
candidate is well scoped for a particular MeTTa dialect.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.WMCalculusNativeBindingSpace

open _root_.CategoryTheory
open Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.LanguagePresheafSharing
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusNativeObservation
open Mettapedia.OSLF.PresheafNativeType
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading

/-- A query pairs the actual pattern matcher with a finite candidate
enumeration. -/
abbrev BindingQuery := Pattern × List Pattern

/-- Evidence is a bag of matcher-produced binding maps. -/
abbrev BindingBag := Bindings → ℕ

private abbrev wmLanguage : LanguageDef :=
  wmExtVertexLanguageDefWithCong wmExtVertexMinimal

/-- Multiplicity of one binding map in the matcher results for a candidate. -/
def bindingMultiplicity (pattern atom : Pattern) (bindings : Bindings) : ℕ :=
  (matchPattern pattern atom).count bindings

/-- Binding-bag extraction against an explicit candidate enumeration. -/
def bindingAnswers (space : MSpace Pattern) (query : BindingQuery) : BindingBag :=
  fun bindings =>
    (query.2.map fun atom => space atom * bindingMultiplicity query.1 atom bindings).sum

/-- Each binding's count distributes over multiplicity-space union. This
uses the real matcher result multiplicity, including duplicate solutions. -/
theorem bindingAnswers_union (left right : MSpace Pattern)
    (query : BindingQuery) :
    bindingAnswers (sUnion left right) query =
      bindingAnswers left query + bindingAnswers right query := by
  funext bindings
  cases query with
  | mk pattern candidates =>
    induction candidates with
    | nil => rfl
    | cons atom rest ih =>
      simp only [bindingAnswers, List.map_cons, List.sum_cons, Pi.add_apply] at ih ⊢
      rw [show sUnion left right atom = left atom + right atom by rfl]
      rw [Nat.add_mul, ih]
      omega

/-- Candidate-enumerated pattern matching is an additive WM observation
with binding bags, not merely a scalar candidate count. -/
instance : AdditiveWorldModel (MSpace Pattern) BindingQuery BindingBag where
  extract := bindingAnswers
  extract_add := bindingAnswers_union

/-- An exact binding-bag answer is a native observation type on WM state
terms; contextual rewrites preserve it by the generic WM/native transport. -/
def bindingBagNativeType
    (world : String → MSpace Pattern)
    (queryName : String → BindingQuery)
    (query : BindingQuery) (answers : BindingBag) :
    FullPresheafGrothendieckObj
      (Mettapedia.OSLF.Framework.WMCalculusContextClosure.wmExtVertexLanguageDefWithCong
        Mettapedia.OSLF.Framework.WMCalculusLanguageDef.wmExtVertexMinimal) :=
  observationNativeType (additiveReading (Ev := BindingBag) world queryName)
    .state (fun state => bindingAnswers state query = answers)

/-- The actual binding-bag observation is transported by a contextual
rewrite in the full native predicate category. -/
def bindingBagRewriteTransport
    (world : String → MSpace Pattern)
    (queryName : String → BindingQuery)
    (query : BindingQuery) (answers : BindingBag)
    {Γ : languagePresheafObj wmLanguage}
    {p q : Γ ⟶ languageProgramObj wmLanguage}
    (step : (languageOperationalLambdaTheory wmLanguage).rewriteRel p q) :
    FullPresheafGrothendieckHom wmLanguage
      (observationInContext
        (additiveReading (Ev := BindingBag) world queryName) .state
        (fun state => bindingAnswers state query = answers) Γ p)
      (observationInContext
        (additiveReading (Ev := BindingBag) world queryName) .state
        (fun state => bindingAnswers state query = answers) Γ q) :=
  observationRewriteTransport
    (additiveReading (Ev := BindingBag) world queryName)
    (additiveReading_coreLaws world queryName)
    .state (fun state => bindingAnswers state query = answers)
    (state_query_eq_invariant
      (additiveReading (Ev := BindingBag) world queryName) query answers)
    step

/-- A variable pattern produces the candidate atom as its binding, with
the exact multiplicity stored by the space. -/
theorem variable_binding_count (space : MSpace Pattern)
    (atom : Pattern) :
    bindingAnswers space (.fvar "x", [atom]) [("x", atom)] = space atom := by
  simp [bindingAnswers, bindingMultiplicity, matchPattern]

/-- A binding under the wrong variable name is not an answer to the query. -/
theorem wrong_variable_binding_count (space : MSpace Pattern)
    (atom : Pattern) :
    bindingAnswers space (.fvar "x", [atom]) [("y", atom)] = 0 := by
  simp [bindingAnswers, bindingMultiplicity, matchPattern]

/-- With every candidate-list query available, the actual matcher-produced
binding bags separate multiplicity-space states. In particular, the
observational quotient identifies exactly equal spaces for this reading. -/
theorem bindingSpaceAgree_iff_eq
    (world : String → MSpace Pattern) (queryName : String → BindingQuery)
    (first second : MSpace Pattern) :
    (additiveReading (Ev := BindingBag) world queryName).Agree .state first second ↔
      first = second := by
  constructor
  · intro agree
    funext atom
    have answer := agree (.fvar "x", [atom])
    change bindingAnswers first (.fvar "x", [atom]) =
      bindingAnswers second (.fvar "x", [atom]) at answer
    have count := congrArg (fun bag : BindingBag => bag [("x", atom)]) answer
    simpa only [variable_binding_count] using count
  · intro equal
    subst second
    intro query
    rfl

end Mettapedia.PLN.WorldModel.WMCalculusNativeBindingSpace
