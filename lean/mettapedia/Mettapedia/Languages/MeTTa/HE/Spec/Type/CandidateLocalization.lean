import Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-!
# Localized function-candidate applicability

The repaired runtime checks function-type arguments in a private finite
presentation, starting from no type bindings.  The published evaluator
threads the applicability result through the caller's binding state.  These
two shapes agree only when the candidate and selected actual types are
alpha-fresh for the caller-visible scope.

`LocalizedSelectedTypePolicyRel` is the thin boundary object joining the
existing presentation fold, its freshness theorem, and the exact semantic
extension of the caller binding theory.  It introduces no second matcher and
contains no executable or fuel premise.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.CandidateLocalization

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Bindings.ScopeObservation
open Spec.Eval
open Spec.Type.Presentation
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.Freshness

/-- Expected return types for which the published final applicability check
accepts every declared return without extending the private presentation.
This is the agreement fragment shared by the literal published scan and the
current runtime scan. -/
def ExpectedReturnUnconstrained (expectedType : Atom) : Prop :=
  expectedType = Atom.undefinedType ∨ expectedType = Atom.atomType

/-- Append one final type constraint to an already successful presentation
fold.  This is the structural boundary used to add the published return-type
check after the runtime's argument-only fold. -/
theorem presentationArgumentList_appendOne
    {expected actual : List Atom} {incoming next output : TypeSubst}
    {expectedLast actualLast : Atom}
    (fold : PresentationArgumentListMatchRel
      expected actual incoming next)
    (last : CorePlusR2TypePresentationMatchRel
      next expectedLast actualLast output) :
    PresentationArgumentListMatchRel
      (expected ++ [expectedLast]) (actual ++ [actualLast]) incoming output := by
  induction fold with
  | nil =>
      exact .cons last (.nil output)
  | cons head tail ih =>
      simp only [List.cons_append]
      exact .cons head (ih last)

/-- In the unconstrained-return fragment, the published conjunctive check is
the runtime's successful argument fold followed by one wildcard step. -/
theorem presentationArgumentList_appendUnconstrainedReturn
    {expected actual : List Atom} {substitution : TypeSubst}
    {expectedReturn actualReturn : Atom}
    (arguments : PresentationArgumentListMatchRel
      expected actual [] substitution)
    (unconstrained : ExpectedReturnUnconstrained expectedReturn) :
    PresentationArgumentListMatchRel
      (expected ++ [expectedReturn]) (actual ++ [actualReturn])
      [] substitution := by
  apply presentationArgumentList_appendOne arguments
  rcases unconstrained with rfl | rfl
  · exact .undefinedLeft substitution actualReturn
  · exact .atomLeft substitution actualReturn

/-- One selected arrow policy whose argument constraints and expected-return
constraint have been discharged in a private, caller-fresh presentation.

The final element of the expected list is the caller's expected return type;
the final element of the actual list is the arrow's declared return type.
Thus the relation models the published conjunctive per-candidate check rather
than an argument-only scan followed by an unrelated outer cast. -/
structure LocalizedSelectedTypePolicyRel
    (scope : List String) (incoming : Bindings)
    (expectedType : Atom) (actualTypes : List Atom)
    (policy : SelectedTypePolicy) (substitution : TypeSubst)
    (output : Bindings) : Prop where
  constraints : PresentationArgumentListMatchRel
    (policy.argumentTypes ++ [expectedType])
    (actualTypes ++ [policy.returnType]) [] substitution
  expectedFresh : AtomsAvoid
    (policy.argumentTypes ++ [expectedType])
    (scope ++ specBindingVars incoming)
  actualFresh : AtomsAvoid
    (actualTypes ++ [policy.returnType])
    (scope ++ specBindingVars incoming)
  extension : PrivatePresentationExtensionRel
    scope incoming substitution output

/-- The canonical spec binding carrier for one localized finite fold is the
incoming binding record with the private assignments appended. -/
theorem LocalizedSelectedTypePolicyRel.ofFold
    {scope : List String} {incoming : Bindings}
    {expectedType : Atom} {actualTypes : List Atom}
    {policy : SelectedTypePolicy} {substitution : TypeSubst}
    (constraints : PresentationArgumentListMatchRel
      (policy.argumentTypes ++ [expectedType])
      (actualTypes ++ [policy.returnType]) [] substitution)
    (expectedFresh : AtomsAvoid
      (policy.argumentTypes ++ [expectedType])
      (scope ++ specBindingVars incoming))
    (actualFresh : AtomsAvoid
      (actualTypes ++ [policy.returnType])
      (scope ++ specBindingVars incoming)) :
    LocalizedSelectedTypePolicyRel scope incoming expectedType actualTypes
      policy substitution
      ⟨incoming.assignments ++ substitution, incoming.equalities⟩ := by
  refine ⟨constraints, expectedFresh, actualFresh, ?_⟩
  exact
    Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.PresentationArgumentListMatchRel.privateExtension
      constraints expectedFresh actualFresh

/-- Runtime argument success localizes directly whenever the expected return
is one of the two published top-level gradual types.  No return constraint is
invented: the final fold step is the corresponding published wildcard rule. -/
theorem LocalizedSelectedTypePolicyRel.ofArgumentFold
    {scope : List String} {incoming : Bindings}
    {expectedType : Atom} {actualTypes : List Atom}
    {policy : SelectedTypePolicy} {substitution : TypeSubst}
    (arguments : PresentationArgumentListMatchRel
      policy.argumentTypes actualTypes [] substitution)
    (unconstrained : ExpectedReturnUnconstrained expectedType)
    (expectedFresh : AtomsAvoid
      (policy.argumentTypes ++ [expectedType])
      (scope ++ specBindingVars incoming))
    (actualFresh : AtomsAvoid
      (actualTypes ++ [policy.returnType])
      (scope ++ specBindingVars incoming)) :
    LocalizedSelectedTypePolicyRel scope incoming expectedType actualTypes
      policy substitution
      ⟨incoming.assignments ++ substitution, incoming.equalities⟩ := by
  exact .ofFold
    (presentationArgumentList_appendUnconstrainedReturn
      arguments unconstrained)
    expectedFresh actualFresh

/-- Localized applicability output is observationally identical to the
caller state at the declared public scope. -/
theorem LocalizedSelectedTypePolicyRel.scopedInert
    {scope : List String} {incoming output : Bindings}
    {expectedType : Atom} {actualTypes : List Atom}
    {policy : SelectedTypePolicy} {substitution : TypeSubst}
    (localized : LocalizedSelectedTypePolicyRel scope incoming expectedType
      actualTypes policy substitution output) :
    BindingTheoryEquivAt scope incoming output :=
  localized.extension.observationallyInert

/-! ## Boundary canaries -/

private def closedPolicy : SelectedTypePolicy :=
  ⟨.expression [.symbol "->", .symbol "R"], [], .symbol "R", rfl⟩

/-- Positive: a closed nullary arrow localizes without adding a private
assignment. -/
theorem closed_nullary_policy_localizes :
    LocalizedSelectedTypePolicyRel [] Bindings.empty Atom.undefinedType []
      closedPolicy [] Bindings.empty := by
  have constraints : PresentationArgumentListMatchRel
      [Atom.undefinedType] [.symbol "R"] [] [] :=
    .cons (.undefinedLeft [] (.symbol "R")) (.nil [])
  simpa [closedPolicy, Bindings.empty] using
    (LocalizedSelectedTypePolicyRel.ofFold
      (scope := []) (incoming := Bindings.empty)
      (expectedType := Atom.undefinedType) (actualTypes := [])
      (policy := closedPolicy) (substitution := []) constraints (by
        simp [AtomsAvoid, specBindingVars, Bindings.empty]) (by
        simp [AtomsAvoid, specBindingVars, Bindings.empty]))

private def capturingPolicy : SelectedTypePolicy :=
  ⟨.expression [.symbol "->", .var "public", .symbol "R"],
    [.var "public"], .symbol "R", rfl⟩

/-- Negative: a candidate that reuses a caller-visible variable spelling is
not a lawful localized policy.  It must first be alpha-freshened. -/
theorem unrenamed_public_type_variable_cannot_localize :
    ¬∃ output substitution,
      LocalizedSelectedTypePolicyRel ["public"] Bindings.empty
        Atom.undefinedType [.symbol "A"] capturingPolicy substitution output := by
  rintro ⟨output, substitution, localized⟩
  have forbidden := localized.expectedFresh "public"
  exact forbidden (by
    simp [capturingPolicy, TypeSubst.typeVars,
      TypeSubst.typeVarsList]) (by simp)

end Mettapedia.Languages.MeTTa.HE.Spec.Type.CandidateLocalization
