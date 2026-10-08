import Mettapedia.OSLF.Syntax.BehavioralEquationDescent

/-!
# Complete constructor-law projection to binding equation classes

The independently formed raw law acts on arbitrary state/behavior pairs.
Its class-level constructor law is formed from representatives, and local
compatibility proves that projection commutes with the complete clause.
The actual equation-quotient clone and its descended coalgebra satisfy this
constructor law for arbitrary quotient-valued argument vectors.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BehavioralEquationDescent

open FreeBindingTerms BindingEquationFamilyCongruence

universe u

variable {S : Signature} {Actions : S.Srt → Type u}
  {M : List (MetaArity S)} (family : EqAxiom S M → Prop)

abbrev ClassResult (Γ : Ctx S) (sort : S.Srt) :=
  Classes family Γ sort × (Actions sort → Option (Classes family Γ sort))

def projectResult {Γ : Ctx S} {sort : S.Srt} (value : Result Actions Γ sort) :
    ClassResult (Actions := Actions) family Γ sort :=
  (project family value.1, fun action => (value.2 action).map (project family))

noncomputable def representativeResult {Γ : Ctx S} {sort : S.Srt}
    (value : ClassResult (Actions := Actions) family Γ sort) : Result Actions Γ sort :=
  (Quotient.out value.1, fun action => (value.2 action).map Quotient.out)

theorem projectResult_representative {Γ : Ctx S} {sort : S.Srt}
    (value : ClassResult (Actions := Actions) family Γ sort) :
    projectResult family (representativeResult family value) = value := by
  apply Prod.ext
  · exact Quotient.out_eq value.1
  · funext action
    change ((value.2 action).map Quotient.out).map (project family) = value.2 action
    cases value.2 action with
    | none => rfl
    | some target => exact congrArg some (Quotient.out_eq target)

theorem pairRelated_of_projection {Γ : Ctx S} {sort : S.Srt}
    {first second : Result Actions Γ sort}
    (same : projectResult family first = projectResult family second) :
    PairRelated family first second :=
  ⟨Quotient.exact (congrArg Prod.fst same),
    fun action => congrArg (fun value => value.2 action) same⟩

theorem representative_project_arguments :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (arguments : FamilyArgs S (Result Actions) arity Γ),
      PairArgsRelated family
        (FamilyArgs.map (representativeResult family)
          (FamilyArgs.map (projectResult family) arguments)) arguments
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
    .cons (pairRelated_of_projection family
      (projectResult_representative family (projectResult family head)))
      (representative_project_arguments tail)

variable (law : LocalLaw S Actions)

/-- A real optional-successor clause on arbitrary quotient state/behavior
inputs. The following theorem proves independence from raw representatives. -/
noncomputable def quotientOperation {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    (arguments : FamilyArgs S (ClassResult (Actions := Actions) family) (S.arity operator) Γ) :
    Actions sort → Option (Classes family Γ sort) :=
  fun action => (law.operation operator
    (FamilyArgs.map (representativeResult family) arguments) action).map (project family)

theorem quotientOperation_projection (constructors : ConstructorCompatible law family)
    {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    (arguments : FamilyArgs S (Result Actions) (S.arity operator) Γ) :
    quotientOperation family law operator (FamilyArgs.map (projectResult family) arguments) =
      fun action => (law.operation operator arguments action).map (project family) := by
  funext action
  exact constructors operator (representative_project_arguments family arguments) action

variable (constructors : ConstructorCompatible law family) (equations : EquationCompatible law family)

/-- Representatives of arbitrary quotient arguments retain both the exact
source classes and the complete actual descended successor readout. -/
theorem representative_operational_arguments :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (arguments : FamilyArgs S (Classes family) arity Γ),
      FamilyArgs.map (projectResult family)
        (FamilyArgs.map (fun term => (term, coalgebra law term))
          (syntaxToFamily
            (BindingTermCongruenceQuotient.representativeArgs
              (BindingEquationFamilyModel.congruence family) arguments))) =
        FamilyArgs.map (fun value => (value, quotientCoalgebra law constructors equations value)) arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
    apply congrArg₂ FamilyArgs.cons
    · apply Prod.ext
      · exact Quotient.out_eq head
      · funext action
        have computation := quotientCoalgebra_project law constructors equations (Quotient.out head) action
        have same : project family (Quotient.out head) = head := Quotient.out_eq head
        rw [same] at computation
        exact computation.symm
    · exact representative_operational_arguments tail

/-- The actual binding-clone constructors on arbitrary quotient values obey
the independently descended local behavior law. This includes binding heads. -/
theorem quotientCoalgebra_operation {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    (arguments : FamilyArgs S (Classes family) (S.arity operator) Γ) :
    quotientCoalgebra law constructors equations
        ((BindingEquationFamilyModel.algebra family).operation operator arguments) =
      quotientOperation family law operator
        (FamilyArgs.map (fun value => (value, quotientCoalgebra law constructors equations value)) arguments) := by
  change quotientCoalgebra law constructors equations
    (project family (.op operator
      (BindingTermCongruenceQuotient.representativeArgs
        (BindingEquationFamilyModel.congruence family) arguments))) = _
  rw [← representative_operational_arguments family law constructors equations arguments]
  funext action
  rw [quotientCoalgebra_project, coalgebra_operation]
  exact (congrArg (fun behavior => behavior action)
    (quotientOperation_projection family law constructors operator _)).symm

end Mettapedia.OSLF.Binding.BehavioralEquationDescent
