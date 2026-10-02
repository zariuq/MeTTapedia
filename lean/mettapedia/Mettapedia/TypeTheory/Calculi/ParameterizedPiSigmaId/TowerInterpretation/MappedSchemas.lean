import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.TypedInstances
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ElaborationHeadMap
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.PackageSum

/-!
# Set models of mapped packages and of sums of packages

A package presented by a schema family is moved to a larger language of heads by mapping its
heads (`ChurchRules.mapSchemas`), and two packages over one language of heads are put together
(`ChurchRules.sum`). This module gives the set models of both constructions.

* **Along a map of heads.** A schema that is valid at its typed instances, with the heads read
  through the map, stays valid after the map (`SchemaValid.mapHead`): a typed instance of the
  mapped left side is a typed instance of the left side (`TypedInstance.of_mapHead`), and the
  values of the mapped sides are the values of the sides. So the mapped package has a set
  model as soon as the package has one with the heads read through the map
  (`SetModel.mapSchemas`).
* **Sums.** Two set models at the same heads and the same constants are a set model of the
  sum of their packages (`SetModel.sum`).

Positive example: the object package of the MeTTa candidate, read at the heads of the tower
with level names and summed with the families over the names, has one set model
(`objectNames_model`, in the executable model of the candidate). Negative example: a model of
a sum gives a model of its first package (`SetModel.of_sum_left`), so a sum whose first
package has no set model has none.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality.Annotated
open AlgebraicSchema (SchemaFamily)
open Mettapedia.Logic.HOL.Embedding
open ZFSetReplayInterpretation (UniverseModel)

universe u

/-! ## Along a map of heads -/

section Mapped

variable {HeadOne HeadTwo : Type} (g : HeadOne → HeadTwo) {heads : HeadTwo → ZFSet.{u}}
  {consts : DeclName → ZFSet.{u}} {decls : DeclName → Option (CTm HeadOne 0)}

/-- **A typed instance of a mapped left side is a typed instance of the left side**, with the
heads read through the map. -/
theorem TypedInstance.of_mapHead {k : Nat} {L : Tm HeadOne k} {η : Env.{u} k}
    (typed : TypedInstance heads consts (mapDecls g decls) (L.mapHead g) η) :
    TypedInstance (fun h => heads (g h)) consts decls L η := by
  have knowledge := patternKnowledge_mapHead g decls L none
  have equations := patternEquations_mapHead g decls L none
  simp only [Option.map_none] at knowledge equations
  refine ⟨fun i T known => ?_, fun e mem => ?_⟩
  · have mapped : patternKnowledge (mapDecls g decls) none (L.mapHead g) i =
        some (T.mapHead g) := by
      rw [knowledge]
      show (patternKnowledge decls none L i).map (CTm.mapHead g) = _
      rw [known]
      rfl
    have member := typed.1 i _ mapped
    rwa [ev_mapHead] at member
  · have mapped : mapEquation g e ∈ patternEquations (mapDecls g decls) none (L.mapHead g) := by
      rw [equations]
      exact List.mem_map_of_mem mem
    have equal := typed.2 _ mapped
    change ev heads consts (e.1.mapHead g) η = ev heads consts (e.2.1.mapHead g) η at equal
    rwa [ev_mapHead, ev_mapHead] at equal

/-- **A schema valid at its typed instances stays valid along a map of heads.** -/
theorem SchemaValid.mapHead {k : Nat} {L R : Tm HeadOne k}
    (valid : SchemaValid (fun h => heads (g h)) consts decls L R) :
    SchemaValid heads consts (mapDecls g decls) (L.mapHead g) (R.mapHead g) := by
  intro η typed
  rw [elabLeft_mapHead, elabRight_mapHead, ev_mapHead, ev_mapHead]
  exact valid η (TypedInstance.of_mapHead g typed)

/-- Every schema of a mapped family is valid when every schema of the family is. -/
theorem FamilyValid.mapHead {S : SchemaFamily HeadOne}
    (valid : FamilyValid (fun h => heads (g h)) consts decls S) :
    FamilyValid heads consts (mapDecls g decls) (mapFamily g S) := by
  intro k L' R' rule
  obtain ⟨L, R, known, rfl, rfl⟩ := rule
  exact (valid known).mapHead g

/-- **A set model of a mapped package**: closed universes for the universe rules of the
target, equal values for its equal heads, and, with the heads read through the map, the
declared constants of the package in their declared types and its schemas valid at their
typed instances. -/
theorem SetModel.mapSchemas {target : Rules HeadTwo} {R : Rules HeadOne}
    {S : SchemaFamily HeadOne} (universes : UniverseModel target heads)
    (headEq : ∀ {h h' : HeadTwo}, target.headEq h h' → heads h = heads h')
    (constants : ∀ {c : DeclName} {T : CTm HeadOne 0},
      elabDeclarations R.constantType c = some T →
        consts c ∈ ev (fun h => heads (g h)) consts T Fin.elim0)
    (valid : FamilyValid (fun h => heads (g h)) consts (elabDeclarations R.constantType) S) :
    SetModel heads consts (ChurchRules.mapSchemas g target R S) := by
  show SetModel heads consts (ChurchRules.ofSchemas (Rules.mapSchemas g target R S)
    (mapFamily g S) (Rules.mapSchemas_presents g target R S))
  refine SetModel.ofSchemas (present := Rules.mapSchemas_presents g target R S)
    { universes with } headEq (fun {c T} known => ?_) ?_
  · have known' : mapDecls g (elabDeclarations R.constantType) c = some T := by
      rw [← ChurchRules.mapSchemas_constantType g target R S]
      exact known
    cases found : elabDeclarations R.constantType c with
    | none =>
      unfold mapDecls at known'
      rw [found] at known'
      exact nomatch known'
    | some T₀ =>
      unfold mapDecls at known'
      rw [found] at known'
      obtain rfl : T₀.mapHead g = T := Option.some.inj known'
      rw [ev_mapHead]
      exact constants found
  · show FamilyValid heads consts
      (elabDeclarations fun c => (R.constantType c).map (Tm.mapHead g)) (mapFamily g S)
    rw [elabDeclarations_mapHead]
    exact valid.mapHead g

end Mapped

/-! ## Sums -/

section Sums

variable {Head : Type} {heads : Head → ZFSet.{u}} {consts : DeclName → ZFSet.{u}}
  {R₁ R₂ : Rules Head} {P₁ : ChurchRules R₁} {P₂ : ChurchRules R₂}

/-- **Two set models at the same heads and constants are a set model of the sum of their
packages.** -/
theorem SetModel.sum (first : SetModel heads consts P₁) (second : SetModel heads consts P₂) :
    SetModel heads consts (P₁.sum P₂) where
  universes := { first.universes with }
  headEq := first.headEq
  constants := by
    intro c T known
    have known' : sumDecls P₁.constantType P₂.constantType c = some T := known
    cases found : P₁.constantType c with
    | none =>
      rw [sumDecls_right found] at known'
      exact second.constants known'
    | some D =>
      rw [sumDecls_left found] at known'
      obtain rfl := Option.some.inj known'
      exact first.constants found
  steps := by
    intro n Γ l r premises _ required holds ρ sat
    have required' : (P₁.computation.step l r ∧ P₁.computation.requires l r premises) ∨
        (P₂.computation.step l r ∧ P₂.computation.requires l r premises) := required
    rcases required' with here | there
    · exact first.steps here.1 here.2 holds ρ sat
    · exact second.steps there.1 there.2 holds ρ sat

/-- A set model of a sum is a set model of its first package. -/
theorem SetModel.of_sum_left (model : SetModel heads consts (P₁.sum P₂)) :
    SetModel heads consts P₁ where
  universes := { model.universes with }
  headEq := model.headEq
  constants := fun known => model.constants (sumDecls_left known)
  steps := fun step required holds ρ sat =>
    model.steps (.inl step) (.inl ⟨step, required⟩) holds ρ sat

end Sums

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
