import Mettapedia.Languages.SUMO.Native.Derivation

/-!
# Soundness of native SUMO derivations

Every rule of the native classical core preserves the general unityped,
world-indexed semantics.  The theorem covers arbitrary term heads, formula
arguments, ordinary quantification, exact-row quantification, and Leibniz
equality.  Ontology-specific and modal doctrines remain separate extensions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.SUMO.Native

universe uSymbol uLiteral uModel

/-- Every assumption in a native context holds at one model environment and
world. -/
def SatisfiesAssumptions
    {Symbol : Type uSymbol} {Literal : Type uLiteral}
    {ordinary rows : Nat}
    (model : Model Symbol Literal)
    (objects : model.ObjectEnvironment ordinary)
    (rowValues : model.RowEnvironment rows)
    (world : model.World)
    (assumptions : List (Formula Symbol Literal ordinary rows)) : Prop :=
  forall body, body ∈ assumptions ->
    model.satisfies objects rowValues body world

namespace SatisfiesAssumptions

variable {Symbol : Type uSymbol} {Literal : Type uLiteral}
variable {ordinary rows : Nat}
variable {model : Model Symbol Literal}
variable {objects : model.ObjectEnvironment ordinary}
variable {rowValues : model.RowEnvironment rows}
variable {world : model.World}
variable {assumptions : List (Formula Symbol Literal ordinary rows)}

theorem cons
    {head : Formula Symbol Literal ordinary rows}
    (headHolds : model.satisfies objects rowValues head world)
    (tailHolds : SatisfiesAssumptions model objects rowValues world assumptions) :
    SatisfiesAssumptions model objects rowValues world (head :: assumptions) := by
  intro body membership
  simp only [List.mem_cons] at membership
  rcases membership with equality | membership
  · subst body
    exact headHolds
  · exact tailHolds body membership

theorem tail
    {head : Formula Symbol Literal ordinary rows}
    (holds :
      SatisfiesAssumptions model objects rowValues world (head :: assumptions)) :
    SatisfiesAssumptions model objects rowValues world assumptions := by
  intro body membership
  exact holds body (List.mem_cons_of_mem head membership)

theorem weakenObject
    (holds : SatisfiesAssumptions model objects rowValues world assumptions)
    (fresh : model.Carrier) :
    SatisfiesAssumptions model (Fin.cases fresh objects) rowValues world
      (weakenObjectHypotheses assumptions) := by
  intro weakened membership
  obtain ⟨body, bodyMember, rfl⟩ := List.mem_map.mp membership
  exact (model.satisfies_weakenObject objects rowValues fresh body world).2
    (holds body bodyMember)

theorem weakenRow
    (holds : SatisfiesAssumptions model objects rowValues world assumptions)
    (fresh : List model.Carrier) :
    SatisfiesAssumptions model objects (Fin.cases fresh rowValues) world
      (weakenRowHypotheses assumptions) := by
  intro weakened membership
  obtain ⟨body, bodyMember, rfl⟩ := List.mem_map.mp membership
  exact (model.satisfies_weakenRow objects rowValues fresh body world).2
    (holds body bodyMember)

end SatisfiesAssumptions

namespace Derivation

variable {Symbol : Type uSymbol} {Literal : Type uLiteral}

/-- Every native derivation is valid in every general native SUMO model. -/
theorem sound
    {ordinary rows : Nat}
    {assumptions : List (Formula Symbol Literal ordinary rows)}
    {body : Formula Symbol Literal ordinary rows}
    (derivation : Derivation Symbol Literal assumptions body) :
    forall (model : Model Symbol Literal)
      (objects : model.ObjectEnvironment ordinary)
      (rowValues : model.RowEnvironment rows)
      (world : model.World),
      SatisfiesAssumptions model objects rowValues world assumptions ->
        model.satisfies objects rowValues body world := by
  induction derivation with
  | hypothesis membership =>
      intro model objects rowValues world assumptionsHold
      exact assumptionsHold _ membership
  | topIntroduction =>
      intro model objects rowValues world assumptionsHold
      trivial
  | bottomElimination premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold
      exact (inductionHypothesis model objects rowValues world assumptionsHold).elim
  | andIntroduction leftProof rightProof leftIH rightIH =>
      intro model objects rowValues world assumptionsHold
      exact ⟨leftIH model objects rowValues world assumptionsHold,
        rightIH model objects rowValues world assumptionsHold⟩
  | andEliminationLeft premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold
      exact (inductionHypothesis model objects rowValues world assumptionsHold).1
  | andEliminationRight premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold
      exact (inductionHypothesis model objects rowValues world assumptionsHold).2
  | orIntroductionLeft premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold
      exact Or.inl (inductionHypothesis model objects rowValues world assumptionsHold)
  | orIntroductionRight premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold
      exact Or.inr (inductionHypothesis model objects rowValues world assumptionsHold)
  | orElimination disjunction leftBranch rightBranch disjunctionIH leftIH rightIH =>
      intro model objects rowValues world assumptionsHold
      rcases disjunctionIH model objects rowValues world assumptionsHold with
        leftHolds | rightHolds
      · exact leftIH model objects rowValues world
          (SatisfiesAssumptions.cons leftHolds assumptionsHold)
      · exact rightIH model objects rowValues world
          (SatisfiesAssumptions.cons rightHolds assumptionsHold)
  | implicationIntroduction premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold antecedentHolds
      exact inductionHypothesis model objects rowValues world
        (SatisfiesAssumptions.cons antecedentHolds assumptionsHold)
  | implicationElimination functionProof argumentProof functionIH argumentIH =>
      intro model objects rowValues world assumptionsHold
      exact functionIH model objects rowValues world assumptionsHold
        (argumentIH model objects rowValues world assumptionsHold)
  | negationIntroduction premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold bodyHolds
      exact inductionHypothesis model objects rowValues world
        (SatisfiesAssumptions.cons bodyHolds assumptionsHold)
  | negationElimination negativeProof positiveProof negativeIH positiveIH =>
      intro model objects rowValues world assumptionsHold
      exact negativeIH model objects rowValues world assumptionsHold
        (positiveIH model objects rowValues world assumptionsHold)
  | iffIntroduction forwardProof reverseProof forwardIH reverseIH =>
      intro model objects rowValues world assumptionsHold
      exact ⟨forwardIH model objects rowValues world assumptionsHold,
        reverseIH model objects rowValues world assumptionsHold⟩
  | iffEliminationLeft premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold
      exact (inductionHypothesis model objects rowValues world assumptionsHold).mp
  | iffEliminationRight premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold
      exact (inductionHypothesis model objects rowValues world assumptionsHold).mpr
  | allInSpineFromAllObject arguments premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold value membership
      exact inductionHypothesis model objects rowValues world assumptionsHold value
  | allInSpineNilIntroduction body =>
      intro model objects rowValues world assumptionsHold value membership
      change value ∈ ([] : List model.Carrier) at membership
      cases membership
  | allInSpineTermIntroduction value rest valueProof restProof valueIH restIH =>
      intro model objects rowValues world assumptionsHold candidate membership
      change candidate ∈
        (model.denoteTerm objects rowValues value ::
          model.denoteSpine objects rowValues rest) at membership
      simp only [List.mem_cons] at membership
      rcases membership with equality | membership
      · subst candidate
        exact (model.satisfies_instantiateObject objects rowValues value _ world).1
          (valueIH model objects rowValues world assumptionsHold)
      · exact restIH model objects rowValues world assumptionsHold candidate membership
  | allInSpineHeadElimination premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold
      rename_i ordinaryDepth rowDepth value rest body localAssumptions
      have bodyHolds := inductionHypothesis model objects rowValues world
        assumptionsHold (model.denoteTerm objects rowValues value)
          (List.mem_cons_self)
      exact (model.satisfies_instantiateObject objects rowValues value body world).2
        bodyHolds
  | allInSpineTermTailElimination premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold value membership
      exact inductionHypothesis model objects rowValues world assumptionsHold value
        (List.mem_cons_of_mem _ membership)
  | allInSpineRowTailElimination premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold value membership
      exact inductionHypothesis model objects rowValues world assumptionsHold value
        (List.mem_append_right _ membership)
  | allObjectIntroduction premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold value
      exact inductionHypothesis model (Fin.cases value objects) rowValues world
        (SatisfiesAssumptions.weakenObject assumptionsHold value)
  | allObjectElimination value premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold
      apply (model.satisfies_instantiateObject objects rowValues value _ world).2
      exact inductionHypothesis model objects rowValues world assumptionsHold
        (model.denoteTerm objects rowValues value)
  | someObjectIntroduction value premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold
      refine ⟨model.denoteTerm objects rowValues value, ?_⟩
      exact (model.satisfies_instantiateObject objects rowValues value _ world).1
        (inductionHypothesis model objects rowValues world assumptionsHold)
  | someObjectElimination existentialProof branchProof existentialIH branchIH =>
      intro model objects rowValues world assumptionsHold
      obtain ⟨value, bodyHolds⟩ :=
        existentialIH model objects rowValues world assumptionsHold
      have weakenedAssumptions :=
        SatisfiesAssumptions.weakenObject assumptionsHold value
      have weakenedResult := branchIH model (Fin.cases value objects) rowValues world
        (by
          intro candidate membership
          simp only [List.mem_cons] at membership
          rcases membership with equality | membership
          · subst candidate
            exact bodyHolds
          · exact weakenedAssumptions candidate membership)
      exact (model.satisfies_weakenObject objects rowValues value _ world).1
        weakenedResult
  | allRowIntroduction premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold values
      exact inductionHypothesis model objects (Fin.cases values rowValues) world
        (SatisfiesAssumptions.weakenRow assumptionsHold values)
  | allRowElimination arguments premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold
      apply (model.satisfies_instantiateRow objects rowValues arguments _ world).2
      exact inductionHypothesis model objects rowValues world assumptionsHold
        (model.denoteSpine objects rowValues arguments)
  | someRowIntroduction arguments premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold
      refine ⟨model.denoteSpine objects rowValues arguments, ?_⟩
      exact (model.satisfies_instantiateRow objects rowValues arguments _ world).1
        (inductionHypothesis model objects rowValues world assumptionsHold)
  | someRowElimination existentialProof branchProof existentialIH branchIH =>
      intro model objects rowValues world assumptionsHold
      obtain ⟨values, bodyHolds⟩ :=
        existentialIH model objects rowValues world assumptionsHold
      have weakenedAssumptions :=
        SatisfiesAssumptions.weakenRow assumptionsHold values
      have weakenedResult := branchIH model objects (Fin.cases values rowValues) world
        (by
          intro candidate membership
          simp only [List.mem_cons] at membership
          rcases membership with equality | membership
          · subst candidate
            exact bodyHolds
          · exact weakenedAssumptions candidate membership)
      exact (model.satisfies_weakenRow objects rowValues values _ world).1
        weakenedResult
  | equalityReflexivity value =>
      intro model objects rowValues world assumptionsHold
      rfl
  | equalitySubstitution context equalityProof contextProof equalityIH contextIH =>
      intro model objects rowValues world assumptionsHold
      have valuesEqual := equalityIH model objects rowValues world assumptionsHold
      have leftContext := contextIH model objects rowValues world assumptionsHold
      change model.denoteTerm objects rowValues _ =
        model.denoteTerm objects rowValues _ at valuesEqual
      have leftContextExtended :=
        (model.satisfies_instantiateObject objects rowValues _ context world).1
          leftContext
      rw [valuesEqual] at leftContextExtended
      exact (model.satisfies_instantiateObject objects rowValues _ context world).2
        leftContextExtended
  | classicalContradiction premise inductionHypothesis =>
      intro model objects rowValues world assumptionsHold
      exact Classical.byContradiction (fun bodyDoesNotHold =>
        inductionHypothesis model objects rowValues world
          (SatisfiesAssumptions.cons bodyDoesNotHold assumptionsHold))

/-- A native theorem is true at every world of every model. -/
theorem theorem_valid
    {body : Sentence Symbol Literal}
    (proof : Derivation.Theorem body)
    (model : Model Symbol Literal) :
    model.ValidSentence body := by
  intro world
  exact proof.sound model model.emptyObjects model.emptyRows world
    (by intro assumption membership; simp at membership)

end Derivation

end Mettapedia.Languages.SUMO.Native
