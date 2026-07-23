import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Completeness
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Alpha
import Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
import Mathlib.Logic.Equiv.Fintype

/-!
# Alpha uniqueness of principal finite type presentations

A normal finite presentation is a most-general solution in syntactic form.
If another model is itself principal for the same finite theory, its
observation of any atom differs from the finite presentation only by a
renaming of the residual variables occurring in that observation.

The proof constructs that finite residual renaming from the two
factorizations and extends it to a permutation of all variable names.  It
does not choose equality-class representatives or compare presentation
order.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.PrincipalAlpha

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Theory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Alpha
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation

private theorem applyTypeValuation_eq_rename_of_variables
    (valuation : String → Atom) (rename : String → String) :
    ∀ atom : Atom,
      (∀ name, name ∈ TypeSubst.typeVars atom →
        valuation name = .var (rename name)) →
      applyTypeValuation valuation atom = renameTypeVars rename atom := by
  intro atom
  induction atom using Atom.rec (motive_2 := fun atoms =>
      (∀ name, name ∈ TypeSubst.typeVarsList atoms →
        valuation name = .var (rename name)) →
      atoms.map (applyTypeValuation valuation) =
        atoms.map (renameTypeVars rename)) with
  | symbol name => simp [applyTypeValuation, renameTypeVars]
  | var name =>
      intro agrees
      simpa [applyTypeValuation, renameTypeVars] using
        agrees name (by simp [TypeSubst.typeVars])
  | grounded value => simp [applyTypeValuation, renameTypeVars]
  | expression atoms ih =>
      intro agrees
      simp only [applyTypeValuation, renameTypeVars, Atom.expression.injEq]
      exact ih agrees
  | nil => simp
  | cons atom atoms ihAtom ihAtoms =>
      rename_i agrees
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · apply ihAtom
        intro name member
        exact agrees name (by
          simp only [TypeSubst.typeVarsList, List.mem_append]
          exact Or.inl member)
      · apply ihAtoms
        intro name member
        exact agrees name (by
          simp only [TypeSubst.typeVarsList, List.mem_append]
          exact Or.inr member)

mutual

/-- If a homomorphic valuation fixes a type atom, then it fixes every
variable occurring in that atom as the corresponding variable leaf. -/
theorem valuation_fixes_variable_of_apply_eq_self
    (valuation : String → Atom) : ∀ (atom : Atom) (name : String),
    applyTypeValuation valuation atom = atom →
      name ∈ TypeSubst.typeVars atom →
        valuation name = .var name := by
  intro atom name equation member
  cases atom with
  | symbol symbol => simp [TypeSubst.typeVars] at member
  | var variableName =>
      simp only [TypeSubst.typeVars, List.mem_singleton] at member
      subst name
      simpa [applyTypeValuation] using equation
  | grounded value => simp [TypeSubst.typeVars] at member
  | expression atoms =>
      apply valuation_fixes_list_variable_of_apply_eq_self
        valuation atoms name
      · have equation' :
            Atom.expression (atoms.map (applyTypeValuation valuation)) =
              Atom.expression atoms := by
          simpa [applyTypeValuation] using equation
        exact Atom.expression.inj equation'
      · simpa [TypeSubst.typeVars] using member

/-- List companion of
`valuation_fixes_variable_of_apply_eq_self`. -/
theorem valuation_fixes_list_variable_of_apply_eq_self
    (valuation : String → Atom) : ∀ (atoms : List Atom) (name : String),
    atoms.map (applyTypeValuation valuation) = atoms →
      name ∈ TypeSubst.typeVarsList atoms →
        valuation name = .var name := by
  intro atoms name equation member
  cases atoms with
  | nil => simp [TypeSubst.typeVarsList] at member
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq] at equation
      simp only [TypeSubst.typeVarsList, List.mem_append] at member
      rcases member with member | member
      · exact valuation_fixes_variable_of_apply_eq_self
          valuation atom name equation.1 member
      · exact valuation_fixes_list_variable_of_apply_eq_self
          valuation atoms name equation.2 member

end


/-- Two finite first-order type atoms that are instances of one another are
alpha variants.  This is the presentation-independent form of the classical
mutual-instance theorem. -/
theorem observedTypeAlpha_of_mutual_instances
    {left right : Atom}
    (rightInstance : ∃ forward : String → Atom,
      applyTypeValuation forward left = right)
    (leftInstance : ∃ backward : String → Atom,
      applyTypeValuation backward right = left) :
    ObservedTypeAlphaRel left right := by
  classical
  obtain ⟨forward, forwardEquation⟩ := rightInstance
  obtain ⟨backward, backwardEquation⟩ := leftInstance
  have composedEquation :
      applyTypeValuation
          (fun name => applyTypeValuation backward (forward name)) left =
        left := by
    rw [← applyTypeValuation_comp, forwardEquation, backwardEquation]
  let SourceVariable := {name : String // name ∈ TypeSubst.typeVars left}
  have forwardIsVariable (name : SourceVariable) :
      ∃ target, forward name.1 = .var target := by
    have recovered := valuation_fixes_variable_of_apply_eq_self
      (fun candidateName => applyTypeValuation backward (forward candidateName))
      left name.1 composedEquation name.2
    cases equation : forward name.1 with
    | symbol symbol => simp [equation, applyTypeValuation] at recovered
    | var target => exact ⟨target, rfl⟩
    | grounded value => simp [equation, applyTypeValuation] at recovered
    | expression atoms => simp [equation, applyTypeValuation] at recovered
  let target : SourceVariable → String := fun name =>
    Classical.choose (forwardIsVariable name)
  have targetEquation (name : SourceVariable) :
      forward name.1 = .var (target name) :=
    Classical.choose_spec (forwardIsVariable name)
  have targetInjective : Function.Injective target := by
    intro first second targetsEqual
    apply Subtype.ext
    have firstRecovered := valuation_fixes_variable_of_apply_eq_self
      (fun candidateName => applyTypeValuation backward (forward candidateName))
      left first.1 composedEquation first.2
    have secondRecovered := valuation_fixes_variable_of_apply_eq_self
      (fun candidateName => applyTypeValuation backward (forward candidateName))
      left second.1 composedEquation second.2
    rw [targetEquation first] at firstRecovered
    rw [targetEquation second] at secondRecovered
    rw [targetsEqual] at firstRecovered
    simp only [applyTypeValuation] at firstRecovered secondRecovered
    exact Atom.var.inj (firstRecovered.symm.trans secondRecovered)
  obtain ⟨permutation, extensionLaw⟩ :=
    Equiv.Perm.exists_extending_pair
      (fun name : SourceVariable => name.1) target
      Subtype.val_injective targetInjective
  have forwardOnVariables (name : String)
      (member : name ∈ TypeSubst.typeVars left) :
      forward name = .var (permutation name) := by
    let sourceName : SourceVariable := ⟨name, member⟩
    calc
      forward name = .var (target sourceName) := targetEquation sourceName
      _ = .var (permutation sourceName.1) := by
        rw [(extensionLaw sourceName).symm]
      _ = .var (permutation name) := rfl
  have renamedEquation :
      applyTypeValuation forward left =
        renameTypeVars permutation left :=
    applyTypeValuation_eq_rename_of_variables
      forward permutation left forwardOnVariables
  exact ⟨left, TypeVariableRenamingOf.refl left,
    ⟨permutation, permutation.injective, by
      rw [← forwardEquation, renamedEquation]⟩⟩

/-- A normal presentation and any mutually principal model of its theory
observe every atom up to one injective variable renaming.

`model` is the forward factorization premise: the comparison valuation is a
model of the finite presentation.  `presentationRefinesModel` is the reverse
factorization premise supplied by principality of that comparison model.
Only residual variables appearing in the presented atom participate in the
finite construction. -/
theorem observedTypeAlpha_of_mutuallyPrincipal
    {substitution : TypeSubst} (normal : substitution.Normal)
    {model : String → Atom}
    (modelSatisfied : TypeSubstSatisfied model substitution)
    (presentationRefinesModel :
      ∃ post : String → Atom, ∀ name,
        presentedValuation substitution name =
          applyTypeValuation post (model name))
    (atom : Atom) :
    ObservedTypeAlphaRel
      (substitution.apply atom) (applyTypeValuation model atom) := by
  classical
  let residualNames := TypeSubst.typeVars (substitution.apply atom)
  let Residual := {name : String // name ∈ residualNames}
  obtain ⟨post, hpost⟩ := presentationRefinesModel
  have presentedResidual (name : String) (member : name ∈ residualNames) :
      presentedValuation substitution name = .var name := by
    have notKey : name ∉ substitution.keys := by
      exact normal.apply_variable_not_key atom name (by simpa [residualNames] using member)
    simp [presentedValuation, TypeSubst.apply,
      TypeSubst.lookup_eq_none_of_not_mem_keys notKey, Option.getD]
  have modelResidual (name : String) (member : name ∈ residualNames) :
      ∃ target, model name = .var target := by
    have equation := hpost name
    rw [presentedResidual name member] at equation
    cases hmodel : model name with
    | symbol symbol => simp [hmodel, applyTypeValuation] at equation
    | var target => exact ⟨target, rfl⟩
    | grounded value => simp [hmodel, applyTypeValuation] at equation
    | expression atoms => simp [hmodel, applyTypeValuation] at equation
  let target : Residual → String := fun name =>
    Classical.choose (modelResidual name.1 name.2)
  have targetSpec (name : Residual) :
      model name.1 = .var (target name) := by
    exact Classical.choose_spec (modelResidual name.1 name.2)
  have targetInjective : Function.Injective target := by
    intro left right equalTargets
    apply Subtype.ext
    have leftEquation := hpost left.1
    have rightEquation := hpost right.1
    rw [presentedResidual left.1 left.2, targetSpec left] at leftEquation
    rw [presentedResidual right.1 right.2, targetSpec right] at rightEquation
    simp only [applyTypeValuation] at leftEquation rightEquation
    have : (Atom.var left.1) = .var right.1 := by
      calc
        Atom.var left.1 = post (target left) := leftEquation
        _ = post (target right) := congrArg post equalTargets
        _ = Atom.var right.1 := rightEquation.symm
    exact Atom.var.inj this
  obtain ⟨permutation, hextends⟩ :=
    Equiv.Perm.exists_extending_pair
      (fun name : Residual => name.1) target
      Subtype.val_injective targetInjective
  have modelOnResidual (name : String) (member : name ∈ residualNames) :
      model name = .var (permutation name) := by
    let residual : Residual := ⟨name, member⟩
    calc
      model name = .var (target residual) := targetSpec residual
      _ = .var (permutation residual.1) := by rw [(hextends residual).symm]
      _ = .var (permutation name) := rfl
  have renamedPresented :
      applyTypeValuation model (substitution.apply atom) =
        renameTypeVars permutation (substitution.apply atom) := by
    apply applyTypeValuation_eq_rename_of_variables
    intro name member
    exact modelOnResidual name (by simpa [residualNames] using member)
  refine ⟨substitution.apply atom,
    TypeVariableRenamingOf.refl _, ⟨permutation, permutation.injective, ?_⟩⟩
  rw [← renamedPresented]
  exact (modelSatisfied.absorbs atom).symm

/-- Two normal finite presentations with the same complete solution theory
observe every atom up to private alpha-renaming.  The comparison uses each
presentation's own canonical valuation and the other presentation's
factorization law; no substitution order or representative is exposed. -/
theorem observedTypeAlpha_of_solution_equiv
    {left right : TypeSubst}
    (leftNormal : left.Normal) (rightNormal : right.Normal)
    (sameSolutions : ∀ valuation,
      TypeSubstSatisfied valuation left ↔
        TypeSubstSatisfied valuation right)
    (atom : Atom) :
    ObservedTypeAlphaRel (left.apply atom) (right.apply atom) := by
  let rightModel := presentedValuation right
  have rightModelSatisfiesRight :
      TypeSubstSatisfied rightModel right :=
    normal_presentedValuation_satisfied rightNormal
  have rightModelSatisfiesLeft :
      TypeSubstSatisfied rightModel left :=
    (sameSolutions rightModel).mpr rightModelSatisfiesRight
  have leftModelSatisfiesRight :
      TypeSubstSatisfied (presentedValuation left) right :=
    (sameSolutions (presentedValuation left)).mp
      (normal_presentedValuation_satisfied leftNormal)
  have leftFactorsThroughRight :
      ∃ post : String → Atom, ∀ name,
        presentedValuation left name =
          applyTypeValuation post (rightModel name) := by
    refine ⟨presentedValuation left, ?_⟩
    intro name
    have factor := typeSubst_factorization
      leftModelSatisfiesRight (.var name)
    simpa [rightModel, applyTypeValuation] using factor.symm
  have alpha := observedTypeAlpha_of_mutuallyPrincipal
    leftNormal rightModelSatisfiesLeft leftFactorsThroughRight atom
  simpa [rightModel, applyTypeValuation_presented_eq_apply] using alpha

/-! ## Boundary examples -/

private def aliasPresentation : TypeSubst := [("x", .var "y")]

private def aliasModel (name : String) : Atom :=
  if name = "x" then .var "w"
  else if name = "y" then .var "w"
  else if name = "w" then .var "y"
  else .var name

private def aliasPost (name : String) : Atom :=
  if name = "w" then .var "y"
  else if name = "y" then .var "w"
  else .var name

/-- Positive: pure aliases exercise the residual-variable permutation rather
than a ground-value coincidence. -/
theorem pure_alias_presentations_alpha :
    ObservedTypeAlphaRel
      (aliasPresentation.apply (.expression [.var "x", .var "z"]))
      (applyTypeValuation aliasModel
        (.expression [.var "x", .var "z"])) := by
  apply observedTypeAlpha_of_mutuallyPrincipal
  · simp [aliasPresentation, TypeSubst.Normal, TypeSubst.keys,
      TypeSubst.typeVars]
  · intro name value member
    simp [aliasPresentation] at member
    rcases member with ⟨rfl, rfl⟩
    simp [aliasModel, applyTypeValuation]
  · refine ⟨aliasPost, ?_⟩
    intro name
    by_cases hx : name = "x"
    · subst name
      simp [presentedValuation, aliasPresentation, TypeSubst.apply,
        TypeSubst.lookup, aliasModel, aliasPost, applyTypeValuation]
    · by_cases hy : name = "y"
      · subst name
        simp [presentedValuation, aliasPresentation, TypeSubst.apply,
          TypeSubst.lookup, aliasModel, aliasPost, applyTypeValuation]
      · by_cases hw : name = "w"
        · subst name
          simp [presentedValuation, aliasPresentation, TypeSubst.apply,
            TypeSubst.lookup, aliasModel, aliasPost, applyTypeValuation]
        · simp [presentedValuation, aliasPresentation, TypeSubst.apply,
            TypeSubst.lookup, aliasModel, aliasPost, applyTypeValuation,
            hx, hy, hw]

/-- Negative: alpha presentation can rename variable leaves but cannot turn a
variable observation into a symbol. -/
theorem variable_symbol_not_alpha :
    ¬ObservedTypeAlphaRel (.var "x") (.symbol "A") := by
  rintro ⟨source, ⟨leftRename, _leftInjective, leftEq⟩,
    ⟨rightRename, _rightInjective, rightEq⟩⟩
  cases source <;> simp [renameTypeVars] at leftEq rightEq

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.PrincipalAlpha
