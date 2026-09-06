import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveDependencies

/-!
# A derivation-supported restriction of a cumulative rule package

The restricted package retains only requested constant declarations and the
renaming/substitution closure of requested root equations. The universe and
head-equality policy is unchanged. Every retained judgment can be reconstructed
in this package, and every restricted judgment reflects to the original one.

The construction is not a smallest theory, a change from dependent syntax to
STT, or an executable decision of arbitrary semantic requirements. It gives
an actual smaller declaration/computation package rather than only a condition
on an independently supplied target.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive.Dependencies

variable {Head : Type} {n : Nat}

/-- Requested root equations generate a structurally closed computation
package. Structural closure is necessary for reuse beneath binders. -/
inductive RetainedRoot (requirements : List (Requirement Head)) :
    {n : Nat} → Tm Head n → Tm Head n → Prop where
  | seed {n : Nat} {left right : Tm Head n} :
      Requirement.rootStep n left right ∈ requirements →
      RetainedRoot requirements left right
  | rename {n m : Nat} (rho : Ren n m) {left right : Tm Head n} :
      RetainedRoot requirements left right →
      RetainedRoot requirements (Presentation.rename rho left) (Presentation.rename rho right)
  | substitute {n m : Nat} (sigma : Sub Head n m) {left right : Tm Head n} :
      RetainedRoot requirements left right →
      RetainedRoot requirements (subst sigma left) (subst sigma right)

def retainedComputation (requirements : List (Requirement Head)) : RootComputation Head where
  step := RetainedRoot requirements
  rename := .rename
  substitute := .substitute

def constantNames (requirements : List (Requirement Head)) : List DeclName :=
  requirements.filterMap fun requirement => match requirement with
    | .constantType name _ => some name
    | _ => none

theorem constantName_mem {requirements : List (Requirement Head)}
    {name : DeclName} {type : Tm Head 0}
    (member : Requirement.constantType name type ∈ requirements) :
    name ∈ constantNames requirements := by
  exact List.mem_filterMap.mpr ⟨.constantType name type, member, rfl⟩

def restrict (source : Rules Head) (requirements : List (Requirement Head)) : Rules Head :=
  { source with
    constantType := fun name =>
      if name ∈ constantNames requirements then source.constantType name else none
    computation := retainedComputation requirements }

/-- The requested instances are genuine source steps, and their structural
closure remains genuine by the source's own structural laws. -/
theorem retainedRoot_reflects {source : Rules Head}
    {requirements : List (Requirement Head)} (valid : HoldsAll source requirements)
    {left right : Tm Head n} (step : RetainedRoot requirements left right) :
    source.computation.step left right := by
  induction step with
  | seed member => exact valid _ member
  | rename rho _ ih => exact source.computation.rename rho ih
  | substitute sigma _ ih => exact source.computation.substitute sigma ih

/-- Requesting no root equations genuinely removes all declared computation. -/
theorem retainedRoot_false_of_no_roots {requirements : List (Requirement Head)}
    (noRoots : ∀ (n : Nat) (left right : Tm Head n),
      Requirement.rootStep n left right ∉ requirements)
    {left right : Tm Head n} : ¬ RetainedRoot requirements left right := by
  intro step
  induction step with
  | seed member => exact noRoots _ _ _ member
  | rename _ _ ih => exact ih
  | substitute _ _ ih => exact ih

/-- The generated restriction satisfies the complete retained manifest. -/
theorem restrict_satisfies {source : Rules Head}
    {requirements : List (Requirement Head)} (valid : HoldsAll source requirements) :
    HoldsAll (restrict source requirements) requirements := by
  intro requirement member
  have original := valid requirement member
  cases requirement with
  | headTyping h u => exact original
  | isUniverse u => exact original
  | join u v w => exact original
  | cumulative u v => exact original
  | headEq h k => exact original
  | constantType name type =>
      change (if name ∈ constantNames requirements then source.constantType name else none) =
        some type
      rw [if_pos (constantName_mem member)]
      exact original
  | rootStep n left right => exact RetainedRoot.seed member

/-- Every atomic operation of the restricted package is licensed by the
original package; the converse is neither assumed nor generally true. -/
theorem requirement_reflects {source : Rules Head}
    {requirements : List (Requirement Head)} (valid : HoldsAll source requirements)
    (requirement : Requirement Head)
    (retained : requirement.Holds (restrict source requirements)) :
    requirement.Holds source := by
  cases requirement with
  | headTyping h u => exact retained
  | isUniverse u => exact retained
  | join u v w => exact retained
  | cumulative u v => exact retained
  | headEq h k => exact retained
  | constantType name type =>
      change (if name ∈ constantNames requirements then source.constantType name else none) =
        some type at retained
      split at retained
      · exact retained
      · contradiction
  | rootStep n left right => exact retainedRoot_reflects valid retained

theorem restrict_universeRegularity (source : Rules Head)
    (requirements : List (Requirement Head)) (regular : UniverseRegularity source) :
    UniverseRegularity (restrict source requirements) where
  head_target := regular.head_target
  join_target := regular.join_target
  cumulative_target := regular.cumulative_target
  universe_typed := regular.universe_typed

/-- Restriction cannot mint an additional formed typing judgment. -/
theorem restrict_typing_reflects {source : Rules Head}
    {requirements : List (Requirement Head)} (valid : HoldsAll source requirements)
    {Γ : Ctx Head n} {term type : Tm Head n}
    (typing : Typing (restrict source requirements) Γ term type) :
    Typing source Γ term type :=
  typing_transfer (requirement_reflects valid) typing

theorem restrict_judgment_reflects {source : Rules Head}
    {requirements : List (Requirement Head)} (valid : HoldsAll source requirements)
    {Γ : Ctx Head n} {term type : Tm Head n}
    (judgment : Judgment (restrict source requirements) Γ term type) :
    Judgment source Γ term type :=
  judgment_transfer (requirement_reflects valid) judgment

/-- Every existing admitted judgment has a finite, dependency-closed
declaration/computation restriction that still admits the identical terms. -/
theorem exists_restriction {source : Rules Head}
    {Γ : Ctx Head n} {term type : Tm Head n} (judgment : Judgment source Γ term type) :
    ∃ requirements : List (Requirement Head), HoldsAll source requirements ∧
      Judgment (restrict source requirements) Γ term type := by
  obtain ⟨requirements, valid, replay⟩ := judgment_supported judgment
  exact ⟨requirements, valid, replay _ (restrict_satisfies valid)⟩

/-- The forward retained-judgment law and global no-invention law belong to
the same constructed package. No global extension is required in reverse. -/
theorem exists_restriction_with_reflection {source : Rules Head}
    {Γ : Ctx Head n} {term type : Tm Head n} (judgment : Judgment source Γ term type) :
    ∃ requirements : List (Requirement Head), HoldsAll source requirements ∧
      Judgment (restrict source requirements) Γ term type ∧
      ∀ {m : Nat} {Δ : Ctx Head m} {term' type' : Tm Head m},
        Judgment (restrict source requirements) Δ term' type' →
          Judgment source Δ term' type' := by
  obtain ⟨requirements, valid, retained⟩ := exists_restriction judgment
  exact ⟨requirements, valid, retained, fun judgment => restrict_judgment_reflects valid judgment⟩

#print axioms retainedRoot_reflects
#print axioms retainedRoot_false_of_no_roots
#print axioms restrict_satisfies
#print axioms requirement_reflects
#print axioms restrict_universeRegularity
#print axioms restrict_typing_reflects
#print axioms restrict_judgment_reflects
#print axioms exists_restriction
#print axioms exists_restriction_with_reflection

end FormationSensitive.Dependencies
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
