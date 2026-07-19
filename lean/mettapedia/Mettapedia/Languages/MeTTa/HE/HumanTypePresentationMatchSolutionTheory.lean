import Mettapedia.Languages.MeTTa.HE.HumanTypePresentationAlgebra

/-!
# Solution theory of presentation-preserving type matching

This module identifies the exact equation theory carried by every successful
finite type-presentation match.  It keeps two recursive lanes distinct:
literal `%Undefined%` provenance is interpreted only while traversing the raw
reduced types, whereas already-presented atoms use ordinary syntactic
unification with no wildcard constructor.
-/

namespace Mettapedia.Languages.MeTTa.HE.HumanTypePresentationMatchSolutionTheory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.HumanTypePresentation
open Mettapedia.Languages.MeTTa.HE.HumanTypePresentationTheory
open Mettapedia.Languages.MeTTa.HE.HumanTypeRuntimeRefinement

/-- A fixed variable of a normal presentation is genuinely unassigned; a
reflexive stored assignment is excluded by normality. -/
theorem lookup_eq_none_of_apply_var_eq_self
    {substitution : TypeSubst} (normal : substitution.Normal)
    {name : String}
    (fixed : substitution.apply (.var name) = .var name) :
    substitution.lookup name = none := by
  cases hlookup : substitution.lookup name with
  | none => rfl
  | some value =>
      exfalso
      have hvalue : value = .var name := by
        simpa [TypeSubst.apply, hlookup, Option.getD] using fixed
      have hmem : (name, value) ∈ substitution :=
        TypeSubst.lookup_eq_some_mem hlookup
      have hkey : name ∈ substitution.keys := by
        exact List.mem_map.mpr ⟨(name, value), hmem, rfl⟩
      have hnotKey := normal.2 name value hmem name
      exact (hnotKey (by simp [hvalue, TypeSubst.typeVars])) hkey

/-- Away from raw expression pairs and literal `%Undefined%`, reduced-type
consistency is ordinary equality after applying the valuation. -/
theorem reducedTypeConsistent_iff_applied_eq_of_leaf
    (valuation : String → Atom) (left right : Atom)
    (leafShape : ReducedTypeLeafShape left right)
    (leftNotUndefined : left ≠ Atom.undefinedType)
    (rightNotUndefined : right ≠ Atom.undefinedType) :
    ReducedTypeConsistent valuation left right ↔
      applyTypeValuation valuation left =
        applyTypeValuation valuation right := by
  have notBothExpressions : ∀ lefts rights,
      left = .expression lefts → right = .expression rights → False := by
    intro lefts rights hleft hright
    subst left
    subst right
    exact leafShape
  cases left <;> cases right
  all_goals
    simp [Atom.undefinedType] at notBothExpressions leftNotUndefined rightNotUndefined
  all_goals unfold ReducedTypeConsistent applyTypeValuation
  all_goals first | rfl | simp_all

private theorem reducedTypeConsistent_undefinedLeft
    (valuation : String → Atom) (right : Atom) :
    ReducedTypeConsistent valuation Atom.undefinedType right := by
  trivial

private theorem reducedTypeConsistent_undefinedRight
    (valuation : String → Atom) (left : Atom) :
    ReducedTypeConsistent valuation left Atom.undefinedType := by
  cases left with
  | symbol name =>
      by_cases hname : name = "%Undefined%"
      · subst name
        trivial
      · unfold ReducedTypeConsistent
        split <;> simp_all [Atom.undefinedType]
  | var => trivial
  | grounded => trivial
  | expression => trivial

mutual

private def appliedSolutions
    {substitution output : TypeSubst} {left right : Atom}
    (derivation : AppliedReducedTypeMatchRel substitution left right output)
    (normal : substitution.Normal)
    (leftFixed : substitution.apply left = left)
    (rightFixed : substitution.apply right = right) :
    ∀ valuation,
      TypeSubstSatisfied valuation output ↔
        TypeSubstSatisfied valuation substitution ∧
          applyTypeValuation valuation left =
            applyTypeValuation valuation right :=
  match derivation with
  | .identical _ _ => fun _ => by simp
  | .bindLeft _ => fun valuation => by
      have unassigned :=
        lookup_eq_none_of_apply_var_eq_self normal leftFixed
      simpa [applyTypeValuation] using
        (TypeSubstSatisfied.bind_iff
          (value := right) unassigned valuation)
  | .bindRight _ _ => fun valuation => by
      have unassigned :=
        lookup_eq_none_of_apply_var_eq_self normal rightFixed
      rw [TypeSubstSatisfied.bind_iff
        (value := left) unassigned valuation]
      constructor
      · rintro ⟨satisfied, equation⟩
        exact ⟨satisfied, by
          simpa [applyTypeValuation] using equation.symm⟩
      · rintro ⟨satisfied, equation⟩
        exact ⟨satisfied, by
          simpa [applyTypeValuation] using equation.symm⟩
  | .expression children => fun valuation => by
      simpa [applyTypeValuation] using
        appliedListSolutions children normal valuation

private def appliedPresentationSolutions
    {substitution output : TypeSubst} {left right : Atom}
    (derivation : AppliedTypePresentationMatchRel
      substitution left right output)
    (normal : substitution.Normal) :
    ∀ valuation,
      TypeSubstSatisfied valuation output ↔
        TypeSubstSatisfied valuation substitution ∧
          applyTypeValuation valuation left =
            applyTypeValuation valuation right :=
  match derivation with
  | .ordinary (resolvedLeft := resolvedLeft)
      (resolvedRight := resolvedRight) leftApply rightApply applied =>
    fun valuation => by
      have leftFixed : substitution.apply resolvedLeft = resolvedLeft := by
        rw [← leftApply]
        exact normal.apply_idempotent left
      have rightFixed : substitution.apply resolvedRight = resolvedRight := by
        rw [← rightApply]
        exact normal.apply_idempotent right
      have base := appliedSolutions applied normal
        leftFixed rightFixed valuation
      constructor
      · intro outputSatisfied
        obtain ⟨incomingSatisfied, equation⟩ := base.mp outputSatisfied
        refine ⟨incomingSatisfied, ?_⟩
        calc
          applyTypeValuation valuation left =
              applyTypeValuation valuation (substitution.apply left) :=
            (incomingSatisfied.absorbs left).symm
          _ = applyTypeValuation valuation resolvedLeft :=
            congrArg (applyTypeValuation valuation) leftApply
          _ = applyTypeValuation valuation resolvedRight := equation
          _ = applyTypeValuation valuation (substitution.apply right) :=
            congrArg (applyTypeValuation valuation) rightApply.symm
          _ = applyTypeValuation valuation right :=
            incomingSatisfied.absorbs right
      · rintro ⟨incomingSatisfied, equation⟩
        apply base.mpr
        refine ⟨incomingSatisfied, ?_⟩
        calc
          applyTypeValuation valuation resolvedLeft =
              applyTypeValuation valuation (substitution.apply left) :=
            congrArg (applyTypeValuation valuation) leftApply.symm
          _ = applyTypeValuation valuation left :=
            incomingSatisfied.absorbs left
          _ = applyTypeValuation valuation right := equation
          _ = applyTypeValuation valuation (substitution.apply right) :=
            (incomingSatisfied.absorbs right).symm
          _ = applyTypeValuation valuation resolvedRight :=
            congrArg (applyTypeValuation valuation) rightApply

private def appliedListSolutions
    {substitution output : TypeSubst} {left right : List Atom}
    (derivation : AppliedReducedTypeListMatchRel
      substitution left right output)
    (normal : substitution.Normal) :
    ∀ valuation,
      TypeSubstSatisfied valuation output ↔
        TypeSubstSatisfied valuation substitution ∧
          left.map (applyTypeValuation valuation) =
            right.map (applyTypeValuation valuation) :=
  match derivation with
  | .nil _ => fun _ => by simp
  | .cons head tail => fun valuation => by
      have nextNormal := head.output_normal normal
      have headTheory := appliedPresentationSolutions head normal valuation
      have tailTheory := appliedListSolutions tail nextNormal valuation
      constructor
      · intro outputSatisfied
        obtain ⟨nextSatisfied, tailEquation⟩ :=
          tailTheory.mp outputSatisfied
        obtain ⟨incomingSatisfied, headEquation⟩ :=
          headTheory.mp nextSatisfied
        exact ⟨incomingSatisfied, by
          simp only [List.map_cons, List.cons.injEq]
          exact ⟨headEquation, tailEquation⟩⟩
      · rintro ⟨incomingSatisfied, allEquations⟩
        simp only [List.map_cons, List.cons.injEq] at allEquations
        apply tailTheory.mpr
        exact ⟨headTheory.mpr ⟨incomingSatisfied, allEquations.1⟩,
          allEquations.2⟩

private def reducedSolutions
    {substitution output : TypeSubst} {left right : Atom}
    (derivation : ReducedTypePresentationMatchRel
      substitution left right output)
    (normal : substitution.Normal) :
    ∀ valuation,
      TypeSubstSatisfied valuation output ↔
        TypeSubstSatisfied valuation substitution ∧
          ReducedTypeConsistent valuation left right :=
  match derivation with
  | .undefinedLeft _ right => fun valuation => by
      constructor
      · intro satisfied
        exact ⟨satisfied,
          reducedTypeConsistent_undefinedLeft valuation right⟩
      · rintro ⟨satisfied, _⟩
        exact satisfied
  | .undefinedRight _ left => fun valuation => by
      constructor
      · intro satisfied
        exact ⟨satisfied,
          reducedTypeConsistent_undefinedRight valuation left⟩
      · rintro ⟨satisfied, _⟩
        exact satisfied
  | .expression children => fun valuation => by
      simpa [ReducedTypeConsistent] using
        reducedListSolutions children normal valuation
  | .ordinary leftNotUndefined rightNotUndefined leafShape
      leftApply rightApply applied => fun valuation => by
      have ordinary : AppliedTypePresentationMatchRel
          substitution left right output :=
        .ordinary leftApply rightApply applied
      rw [reducedTypeConsistent_iff_applied_eq_of_leaf
        valuation left right leafShape leftNotUndefined rightNotUndefined]
      exact appliedPresentationSolutions ordinary normal valuation

private def reducedListSolutions
    {substitution output : TypeSubst} {left right : List Atom}
    (derivation : ReducedTypePresentationListMatchRel
      substitution left right output)
    (normal : substitution.Normal) :
    ∀ valuation,
      TypeSubstSatisfied valuation output ↔
        TypeSubstSatisfied valuation substitution ∧
          ReducedTypeListConsistent valuation left right :=
  match derivation with
  | .nil _ => fun _ => by simp [ReducedTypeListConsistent]
  | .cons head tail => fun valuation => by
      have nextNormal := head.output_normal normal
      have headTheory := reducedSolutions head normal valuation
      have tailTheory := reducedListSolutions tail nextNormal valuation
      constructor
      · intro outputSatisfied
        obtain ⟨nextSatisfied, tailConsistent⟩ :=
          tailTheory.mp outputSatisfied
        obtain ⟨incomingSatisfied, headConsistent⟩ :=
          headTheory.mp nextSatisfied
        exact ⟨incomingSatisfied, by
          simp only [ReducedTypeListConsistent]
          exact ⟨headConsistent, tailConsistent⟩⟩
      · rintro ⟨incomingSatisfied, allConsistent⟩
        simp only [ReducedTypeListConsistent] at allConsistent
        apply tailTheory.mpr
        exact ⟨headTheory.mpr ⟨incomingSatisfied, allConsistent.1⟩,
          allConsistent.2⟩

end

/-- Ordinary applied matching presents exactly the incoming equations plus
one equality between its two already-presented atoms. -/
theorem AppliedReducedTypeMatchRel.solutions
    {substitution output : TypeSubst} {left right : Atom}
    (derivation : AppliedReducedTypeMatchRel substitution left right output)
    (normal : substitution.Normal)
    (leftFixed : substitution.apply left = left)
    (rightFixed : substitution.apply right = right)
    (valuation : String → Atom) :
    TypeSubstSatisfied valuation output ↔
      TypeSubstSatisfied valuation substitution ∧
        applyTypeValuation valuation left =
          applyTypeValuation valuation right :=
  appliedSolutions derivation normal leftFixed rightFixed valuation

/-- Raw reduced matching presents exactly the incoming equations plus the R2
consistency proposition, with literal wildcard provenance intact. -/
theorem ReducedTypePresentationMatchRel.solutions
    {substitution output : TypeSubst} {left right : Atom}
    (derivation : ReducedTypePresentationMatchRel
      substitution left right output)
    (normal : substitution.Normal)
    (valuation : String → Atom) :
    TypeSubstSatisfied valuation output ↔
      TypeSubstSatisfied valuation substitution ∧
        ReducedTypeConsistent valuation left right :=
  reducedSolutions derivation normal valuation

/-- The raw reduced list presentation carries exactly the incoming theory
plus pointwise R2 consistency.  This public list interface is the prefix
invariant used by application-fold completeness. -/
theorem ReducedTypePresentationListMatchRel.solutions
    {substitution output : TypeSubst} {left right : List Atom}
    (derivation : ReducedTypePresentationListMatchRel
      substitution left right output)
    (normal : substitution.Normal)
    (valuation : String → Atom) :
    TypeSubstSatisfied valuation output ↔
      TypeSubstSatisfied valuation substitution ∧
        ReducedTypeListConsistent valuation left right :=
  reducedListSolutions derivation normal valuation

/-- The presentation relation for published top-level wildcards plus R2 has
exactly the named core-plus-R2 solution theory. -/
theorem CorePlusR2TypePresentationMatchRel.solutions
    {substitution output : TypeSubst} {left right : Atom}
    (derivation : CorePlusR2TypePresentationMatchRel
      substitution left right output)
    (normal : substitution.Normal)
    (valuation : String → Atom) :
    TypeSubstSatisfied valuation output ↔
      TypeSubstSatisfied valuation substitution ∧
        CorePlusR2TypeConsistent valuation left right := by
  cases derivation with
  | undefinedLeft => simp [CorePlusR2TypeConsistent]
  | undefinedRight => simp [CorePlusR2TypeConsistent]
  | atomLeft => simp [CorePlusR2TypeConsistent]
  | atomRight => simp [CorePlusR2TypeConsistent]
  | reduced leftNotUndefined rightNotUndefined leftNotAtom rightNotAtom reduced =>
      simpa [CorePlusR2TypeConsistent, leftNotUndefined,
        rightNotUndefined, leftNotAtom, rightNotAtom] using
        reducedSolutions reduced normal valuation

/-- Regard a finite type presentation as an ordinary human binding record
with assignments only. -/
def typeSubstAsHumanBindings (substitution : TypeSubst) :
    Mettapedia.Languages.MeTTa.HE.Bindings where
  assignments := substitution
  equalities := []

/-- The assignment-only human binding semantics is exactly finite
presentation satisfaction. -/
theorem humanTypeBindingSatisfied_asHumanBindings_iff
    (valuation : String → Atom) (substitution : TypeSubst) :
    HumanTypeBindingSatisfied valuation
        (typeSubstAsHumanBindings substitution) ↔
      TypeSubstSatisfied valuation substitution := by
  simp [HumanTypeBindingSatisfied, typeSubstAsHumanBindings,
    TypeSubstSatisfied]

/-- A successful presentation match from a normal input always has a model:
its normal output's own presented valuation. -/
theorem corePlusR2_output_satisfiable
    {substitution output : TypeSubst} {left right : Atom}
    (derivation : CorePlusR2TypePresentationMatchRel
      substitution left right output)
    (normal : substitution.Normal) :
    ∃ valuation, TypeSubstSatisfied valuation output := by
  have outputNormal := derivation.output_normal normal
  exact ⟨presentedValuation output,
    normal_presentedValuation_satisfied outputNormal⟩

/-- Forgetting only finite-presentation syntax yields the named
core-plus-R2 observational match relation, with no executable matcher in the
proof route. -/
theorem corePlusR2_to_solutionTheory
    {substitution output : TypeSubst} {left right : Atom}
    (derivation : CorePlusR2TypePresentationMatchRel
      substitution left right output)
    (normal : substitution.Normal) :
    CorePlusR2TypeMatchRel left right
      (typeSubstAsHumanBindings substitution)
      (typeSubstAsHumanBindings output) := by
  constructor
  · obtain ⟨valuation, satisfied⟩ :=
      corePlusR2_output_satisfiable derivation normal
    exact ⟨valuation,
      (humanTypeBindingSatisfied_asHumanBindings_iff
        valuation output).mpr satisfied⟩
  · intro valuation
    rw [humanTypeBindingSatisfied_asHumanBindings_iff,
      humanTypeBindingSatisfied_asHumanBindings_iff]
    exact CorePlusR2TypePresentationMatchRel.solutions
      derivation normal valuation

end Mettapedia.Languages.MeTTa.HE.HumanTypePresentationMatchSolutionTheory
