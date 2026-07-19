import Mettapedia.Languages.MeTTa.HE.HumanTypePresentationExact
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance
import MettaHyperonFull.Proofs.TypeInferenceFreshening

/-!
# Exact type-presentation conformance

The exact human type boundary describes fresh inference scopes relationally.
This file connects the repaired runtime's deterministic finite freshener to
that relation.  The correspondence is structural: translation commutes with
whole-type renaming, and the runtime's growing avoid list is exactly the human
type-variable list at every fold step.

The recursive `getTypes` characterization is built above these lemmas; no
negative consumer should use the exact relation before both directions of
that characterization are available.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.HumanTypePresentation
open Mettapedia.Languages.MeTTa.HE.HumanTypeRuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.HumanTypePresentationExact
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance

/-! ## Structural translation laws -/

mutual

/-- Translation commutes with whole-type variable renaming. -/
theorem toLeaTTaAtom_renameHumanTypeVars
    (rename : String → String) (atom : Atom) :
    toLeaTTaAtom (renameHumanTypeVars rename atom) =
      Metta.Minimal.renameAllVars rename (toLeaTTaAtom atom) := by
  cases atom with
  | symbol name =>
      simp [renameHumanTypeVars, toLeaTTaAtom,
        Metta.Minimal.renameAllVars]
  | var name =>
      simp [renameHumanTypeVars, toLeaTTaAtom,
        Metta.Minimal.renameAllVars]
  | grounded value =>
      simp [renameHumanTypeVars, toLeaTTaAtom,
        Metta.Minimal.renameAllVars]
  | expression atoms =>
      simp only [renameHumanTypeVars, toLeaTTaAtom,
        Metta.Minimal.renameAllVars]
      exact congrArg Metta.Atom.expr
        (toLeaTTaAtoms_renameHumanTypeVars rename atoms)
termination_by 2 * sizeOf atom

/-- List companion of `toLeaTTaAtom_renameHumanTypeVars`. -/
theorem toLeaTTaAtoms_renameHumanTypeVars
    (rename : String → String) (atoms : List Atom) :
    toLeaTTaAtoms (atoms.map (renameHumanTypeVars rename)) =
      (toLeaTTaAtoms atoms).map
        (Metta.Minimal.renameAllVars rename) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      exact congrArg₂ List.cons
        (toLeaTTaAtom_renameHumanTypeVars rename atom)
        (toLeaTTaAtoms_renameHumanTypeVars rename atoms)
termination_by 2 * sizeOf atoms + 1
decreasing_by
  all_goals simp_wf
  all_goals omega

end

mutual

/-- Variable collection is preserved literally by the structural atom
translation used by the type layer. -/
theorem toLeaTTaAtom_vars_eq_typeVars (atom : Atom) :
    (toLeaTTaAtom atom).vars = TypeSubst.typeVars atom := by
  cases atom with
  | symbol name => simp [toLeaTTaAtom, Metta.Atom.vars, TypeSubst.typeVars]
  | var name => simp [toLeaTTaAtom, Metta.Atom.vars, TypeSubst.typeVars]
  | grounded value =>
      simp [toLeaTTaAtom, Metta.Atom.vars, TypeSubst.typeVars]
  | expression atoms =>
      simp only [toLeaTTaAtom, Metta.Atom.vars, TypeSubst.typeVars]
      exact toLeaTTaAtoms_vars_eq_typeVars atoms
termination_by 2 * sizeOf atom

/-- List companion of `toLeaTTaAtom_vars_eq_typeVars`. -/
theorem toLeaTTaAtoms_vars_eq_typeVars (atoms : List Atom) :
    (toLeaTTaAtoms atoms).flatMap Metta.Atom.vars =
      TypeSubst.typeVarsList atoms := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [toLeaTTaAtoms, List.flatMap_cons,
        TypeSubst.typeVarsList]
      exact congrArg₂ List.append
        (toLeaTTaAtom_vars_eq_typeVars atom)
        (toLeaTTaAtoms_vars_eq_typeVars atoms)
termination_by 2 * sizeOf atoms + 1
decreasing_by
  all_goals simp_wf
  all_goals omega

end

/-! ## Runtime freshening realizes the relational alpha scopes -/

/-- One deterministic repaired-runtime candidate is a lawful human
alpha-variant satisfying the same finite avoidance contract. -/
theorem freshenTypeCandidate_alphaVariant
    (avoid : List String) (position : Nat) (source : Atom) :
    TypeCandidateAlphaVariantRel avoid source
      (fromLeaTTaAtom
        (Metta.Minimal.freshenTypeCandidate avoid position
          (toLeaTTaAtom source))) := by
  refine ⟨Metta.Minimal.captureAvoidingName avoid position,
    Metta.Minimal.captureAvoidingName_injective avoid position, ?_, ?_⟩
  · simp only [Metta.Minimal.freshenTypeCandidate]
    rw [← toLeaTTaAtom_renameHumanTypeVars,
      fromLeaTTaAtom_toLeaTTaAtom]
  · intro name _
    exact Metta.Minimal.captureAvoidingName_not_mem avoid position name

/-- The deterministic argument freshening fold realizes the human growing
avoid-set relation at every starting position. -/
theorem freshenArgumentTypes_alphaVariants
    (avoid : List String) (position : Nat) : ∀ sources : List Atom,
    ArgumentAlphaVariantsRel avoid sources
      (fromLeaTTaAtoms
        (Metta.Minimal.freshenArgumentTypes avoid position
          (toLeaTTaAtoms sources))) := by
  intro sources
  induction sources generalizing avoid position with
  | nil => exact ArgumentAlphaVariantsRel.nil avoid
  | cons source sources ih =>
      let freshLea := Metta.Minimal.freshenTypeCandidate avoid position
        (toLeaTTaAtom source)
      let target := fromLeaTTaAtom freshLea
      have hvariant : TypeCandidateAlphaVariantRel avoid source target := by
        simpa [freshLea, target] using
          freshenTypeCandidate_alphaVariant avoid position source
      have htarget : target = renameHumanTypeVars
          (Metta.Minimal.captureAvoidingName avoid position) source := by
        dsimp [target, freshLea]
        simp only [Metta.Minimal.freshenTypeCandidate]
        rw [← toLeaTTaAtom_renameHumanTypeVars,
          fromLeaTTaAtom_toLeaTTaAtom]
      have hfreshImage : freshLea = toLeaTTaAtom target := by
        rw [htarget]
        simpa [freshLea, Metta.Minimal.freshenTypeCandidate] using
          (toLeaTTaAtom_renameHumanTypeVars
            (Metta.Minimal.captureAvoidingName avoid position) source).symm
      have hvars : freshLea.vars = TypeSubst.typeVars target := by
        rw [hfreshImage, toLeaTTaAtom_vars_eq_typeVars]
      rw [Metta.Minimal.freshenArgumentTypes.eq_def]
      simp only [toLeaTTaAtoms, fromLeaTTaAtoms]
      apply ArgumentAlphaVariantsRel.cons hvariant
      simpa [freshLea, target, hvars] using
        ih (avoid ++ TypeSubst.typeVars target) (position + 1)

/-- Pointwise deterministic operator freshening realizes the human operator
candidate relation. -/
theorem freshenOperatorTypes_alphaVariants
    (avoid : List String) (position : Nat) : ∀ sources : List Atom,
    OperatorAlphaVariantsRel avoid sources
      (fromLeaTTaAtoms
        ((toLeaTTaAtoms sources).map
          (Metta.Minimal.freshenTypeCandidate avoid position))) := by
  intro sources
  induction sources with
  | nil => exact OperatorAlphaVariantsRel.nil
  | cons source sources ih =>
      simp only [toLeaTTaAtoms, List.map_cons, fromLeaTTaAtoms]
      exact OperatorAlphaVariantsRel.cons
        (freshenTypeCandidate_alphaVariant avoid position source) ih

/-! ## Fresh-scope separation -/

mutual

/-- Whole-type renaming maps the native variable-occurrence list
pointwise. -/
theorem typeVars_renameHumanTypeVars
    (rename : String → String) (atom : Atom) :
    TypeSubst.typeVars (renameHumanTypeVars rename atom) =
      (TypeSubst.typeVars atom).map rename := by
  cases atom with
  | symbol name => simp [renameHumanTypeVars, TypeSubst.typeVars]
  | var name => simp [renameHumanTypeVars, TypeSubst.typeVars]
  | grounded value => simp [renameHumanTypeVars, TypeSubst.typeVars]
  | expression atoms =>
      simpa [renameHumanTypeVars, TypeSubst.typeVars] using
        typeVarsList_renameHumanTypeVars rename atoms

/-- List companion of `typeVars_renameHumanTypeVars`. -/
theorem typeVarsList_renameHumanTypeVars
    (rename : String → String) (atoms : List Atom) :
    TypeSubst.typeVarsList
        (atoms.map (renameHumanTypeVars rename)) =
      (TypeSubst.typeVarsList atoms).map rename := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, TypeSubst.typeVarsList,
        List.map_append]
      exact congrArg₂ List.append
        (typeVars_renameHumanTypeVars rename atom)
        (typeVarsList_renameHumanTypeVars rename atoms)

end

/-- Every variable in the target of a lawful human alpha variant lies
outside the variant's declared avoid set. -/
theorem TypeCandidateAlphaVariantRel.target_vars_fresh
    {avoid : List String} {source target : Atom}
    (variant : TypeCandidateAlphaVariantRel avoid source target) :
    ∀ name ∈ TypeSubst.typeVars target, name ∉ avoid := by
  rcases variant with ⟨rename, _injective, rfl, fresh⟩
  intro name member
  rw [typeVars_renameHumanTypeVars] at member
  obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
  exact fresh original sourceMember

/-- Function candidates freshened against the complete argument-variable
set are structurally disjoint from those arguments.  This is the exact scope
premise consumed by application-candidate completeness. -/
theorem OperatorAlphaVariantsRel.disjoint_from_arguments
    {avoid : List String} {rawOperators freshOperators actualTypes : List Atom}
    (variants : OperatorAlphaVariantsRel
      (avoid ++ TypeSubst.typeVarsList actualTypes)
      rawOperators freshOperators) :
    ∀ operatorType ∈ freshOperators,
      VarsDisjoint operatorType (.expression actualTypes) := by
  induction variants with
  | nil => simp
  | @cons source target sources targets headVariant tailVariants ih =>
      intro operatorType member
      rcases List.mem_cons.mp member with rfl | tailMember
      · intro name operatorMember argumentMember
        rw [toLeaTTaAtom_vars_eq_typeVars] at operatorMember
        rw [toLeaTTaAtom_vars_eq_typeVars] at argumentMember
        exact TypeCandidateAlphaVariantRel.target_vars_fresh
          headVariant name operatorMember
          (List.mem_append_right avoid argumentMember)
      · exact ih operatorType tailMember

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance
