import Mettapedia.Logic.HOL.Embedding.HenkinPredicateFamilyInterpretation
import Mettapedia.Logic.HOL.UniformListMapFusion

/-!
# Uniform HOL induction supplies dependent refinement witnesses

The retained object-HOL map-fusion proof uses the predicate-quantified list
induction principle. Its interpretation supplies a section at every admitted
list, uniformly in the function parameters. Equality congruence also proves
that any higher-order predicate of the unfused result is equivalent to the
same predicate of the fused result. Interpreting those two object proofs
gives a value-preserving equivalence of refinement comprehensions.

All sections remain conditional on the exact HOL theory. The ordinary-list
model supplies those assumptions. Incorrect composition order passes whole
sample families but has no universal section, and the equations-only junk
model has no map-length section. These are semantic dependent families, not
native dependent proof terms or a model of HOTG.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.UniformListPredicateFamily

open UniformListInduction UniformListMapFusion
open HenkinDependentFamilyInterpretation HenkinPredicateFamilyInterpretation

universe w

variable {Γ : Ctx BaseSort}

/-- The actual uniformly quantified induction proof, interpreted with its
original ordered assumptions rather than a list of sampled instances. -/
def fusionSection (M : HenkinModel.{0, 0, w} BaseSort Symbol)
    (respects : M.FunctionsRespectEqv) (f g : Expr Γ mapping)
    (valuation : SatisfiedContext M (theory (Γ := Γ))) :
    (xs : AdmissibleValue M sequence) →
      predicateFamily M (fuses (weaken f) (weaken g) (.var .vz)) valuation.1 xs :=
  universalProofSection M respects (allListsProof f g) valuation

/-- The property checked before applying the fusion equation. -/
def beforeFusion (property : Expr Γ predicate) (f g : Expr Γ mapping) :
    Formula Symbol (sequence :: Γ) :=
  .app (weaken property) (map (weaken f) (map (weaken g) (.var .vz)))

/-- The same property checked after fusion. -/
def afterFusion (property : Expr Γ predicate) (f g : Expr Γ mapping) :
    Formula Symbol (sequence :: Γ) :=
  .app (weaken property) (map (compose (weaken f) (weaken g)) (.var .vz))

/-- Congruence of an arbitrary higher-order property is an actual object
proof. No decision procedure for that property is required. -/
def refinementForwardProof (property : Expr Γ predicate) (f g : Expr Γ mapping) :
    ProofSyntax Symbol theory (.all (.imp (beforeFusion property f g)
      (afterFusion property f g))) := by
  apply ProofSyntax.allI
  simp only [weaken_theory]
  apply ProofSyntax.impI
  exact .impE
    ((ProofSyntax.eqPropEL (.eqAppArg (weaken property)
      (applyFusion (weaken f) (weaken g) (.var .vz)))).prepend _)
    (.hyp ⟨0, by simp⟩)

/-- The reverse implication keeps the same theory and the same submitted
function and predicate syntax. -/
def refinementBackwardProof (property : Expr Γ predicate) (f g : Expr Γ mapping) :
    ProofSyntax Symbol theory (.all (.imp (afterFusion property f g)
      (beforeFusion property f g))) := by
  apply ProofSyntax.allI
  simp only [weaken_theory]
  apply ProofSyntax.impI
  exact .impE
    ((ProofSyntax.eqPropER (.eqAppArg (weaken property)
      (applyFusion (weaken f) (weaken g) (.var .vz)))).prepend _)
    (.hyp ⟨0, by simp⟩)

/-- A semantic consumer can replace the unfused expression by the fused
one without losing the input list or its property witness. -/
def fusionRefinementEquiv (M : HenkinModel.{0, 0, w} BaseSort Symbol)
    (respects : M.FunctionsRespectEqv) (property : Expr Γ predicate)
    (f g : Expr Γ mapping) (valuation : SatisfiedContext M (theory (Γ := Γ))) :
    refinementFamily M (beforeFusion property f g) valuation.1 ≃
      refinementFamily M (afterFusion property f g) valuation.1 :=
  refinementEquivOfProofs M respects
    (refinementForwardProof property f g) (refinementBackwardProof property f g) valuation

theorem fusionRefinementEquiv_preserves_input
    (M : HenkinModel.{0, 0, w} BaseSort Symbol) (respects : M.FunctionsRespectEqv)
    (property : Expr Γ predicate) (f g : Expr Γ mapping)
    (valuation : SatisfiedContext M (theory (Γ := Γ)))
    (point : refinementFamily M (beforeFusion property f g) valuation.1) :
    (fusionRefinementEquiv M respects property f g valuation point).1 = point.1 := rfl

/-- Adding an admitted semantic parameter does not silently add any
logical assumption: the original theory is merely weakened. -/
def extendTheoryContext (M : HenkinModel.{0, 0, w} BaseSort Symbol)
    {A : Ty BaseSort} (valuation : SatisfiedContext M (theory (Γ := Γ)))
    (value : AdmissibleValue M A) : SatisfiedContext M (theory (Γ := A :: Γ)) :=
  ⟨extendContext M valuation.1 value, by
    change Soundness.SatisfiesHyps M (M.extend valuation.1.1 value.1) theory
    simpa only [weaken_theory] using
      Soundness.satisfies_weakenHyps M valuation.2 value.1⟩

namespace Standard

abbrev model := StandardListModel.model

def emptyContext : AdmissibleContext model [] :=
  ⟨(fun boundVar => nomatch boundVar), by intro A boundVar; exact nomatch boundVar⟩

def satisfied : SatisfiedContext model (theory (Γ := [])) :=
  ⟨emptyContext, by
    intro formula member
    refine Eq.mp ?_ (StandardListModel.theory_valid formula member)
    unfold HenkinModel.models PreModel.models
    apply congrArg ULift.down
    apply congrArg (PreModel.denote model.toPreModel formula)
    funext A boundVar
    nomatch boundVar⟩

theorem respects : model.FunctionsRespectEqv :=
  model.functionsRespectEqv_of_fullDomains
    (HenkinModel.fullDomains_standard StandardListModel.carrier StandardListModel.constant)

def functionValue (function : Bool → Bool) : AdmissibleValue model mapping :=
  ⟨fun value => ⟨function value.down⟩, by trivial⟩

def listValue (xs : List Bool) : AdmissibleValue model sequence := ⟨⟨xs⟩, by trivial⟩

def functionContext (f g : Bool → Bool) :
    SatisfiedContext model (theory (Γ := [mapping, mapping])) :=
  extendTheoryContext model (extendTheoryContext model satisfied (functionValue f))
    (functionValue g)

/-- Every ordinary list receives its witness from the object-HOL induction
proof, uniformly in two arbitrary semantic function parameters. -/
def listFusionWitness (f g : Bool → Bool) (xs : List Bool) :
    predicateFamily model
      (fuses (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
      (functionContext f g).1 (listValue xs) :=
  fusionSection model respects (.var (.vs .vz)) (.var .vz) (functionContext f g)
    (listValue xs)

/-- The dependent witness really asserts the familiar fusion equation.
Its proof comes from the object proof, not from `List.map_map`. -/
theorem listFusionWitness_equation (f g : Bool → Bool) (xs : List Bool) :
    (xs.map g).map f = xs.map (fun value => f (g value)) := by
  have equality := (listFusionWitness f g xs).down.down
  change (ULift.up ((xs.map g).map f) : StandardListModel.LiftedSequence) =
    ULift.up (xs.map (fun value => f (g value))) at equality
  exact congrArg ULift.down equality

def propertyValue (property : List Bool → Prop) : AdmissibleValue model predicate :=
  ⟨fun xs => ⟨property xs.down⟩, by trivial⟩

def propertyContext (property : List Bool → Prop) (f g : Bool → Bool) :
    SatisfiedContext model (theory (Γ := [predicate, mapping, mapping])) :=
  extendTheoryContext model (functionContext f g) (propertyValue property)

def inputRefinement (property : List Bool → Prop) (f g : Bool → Bool)
    (xs : List Bool) (holds : property ((xs.map g).map f)) :
    refinementFamily model
      (beforeFusion (.var .vz) (.var (.vs (.vs .vz))) (.var (.vs .vz)))
      (propertyContext property f g).1 :=
  ⟨listValue xs, ⟨⟨holds⟩⟩⟩

/-- An arbitrary property witness, including a nondecidable one, is reused
through the interpreted higher-order congruence proof. -/
def outputRefinement (property : List Bool → Prop) (f g : Bool → Bool)
    (xs : List Bool) (holds : property ((xs.map g).map f)) :
    refinementFamily model
      (afterFusion (.var .vz) (.var (.vs (.vs .vz))) (.var (.vs .vz)))
      (propertyContext property f g).1 :=
  fusionRefinementEquiv model respects (.var .vz) (.var (.vs (.vs .vz)))
    (.var (.vs .vz)) (propertyContext property f g)
    (inputRefinement property f g xs holds)

theorem outputRefinement_input (property : List Bool → Prop) (f g : Bool → Bool)
    (xs : List Bool) (holds : property ((xs.map g).map f)) :
    (outputRefinement property f g xs holds).1 = listValue xs := rfl

theorem outputRefinement_property (property : List Bool → Prop) (f g : Bool → Bool)
    (xs : List Bool) (holds : property ((xs.map g).map f)) :
    property (xs.map (fun value => f (g value))) :=
  (outputRefinement property f g xs holds).2.down.down

end Standard

namespace Controls

/-- Noncommuting functions expose the incorrect fusion order. -/
def wrongParameters := Standard.functionContext (fun _ => true) Bool.not

def wrongListFamily : AdmissibleValue Standard.model sequence → Type 1 :=
  predicateFamily Standard.model
    (UniformListMapFusion.Controls.wrongEquation
      (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)) wrongParameters.1

/-- The incorrect law really has a witness at the empty list. -/
def wrongEmptyWitness : wrongListFamily (Standard.listValue []) := ⟨⟨rfl⟩⟩

/-- But the same interpreted family has an empty fibre at this singleton. -/
theorem wrong_singleton_fibre_empty :
    ¬ Nonempty (wrongListFamily (Standard.listValue [false])) := by
  rintro ⟨witness⟩
  have impossible := witness.down.down
  change (ULift.up [true] : StandardListModel.LiftedSequence) = ULift.up [false] at impossible
  have bad := congrArg ULift.down impossible
  cases bad

/-- This is a genuinely varying HOL-generated family: an erased constant
type cannot represent both its inhabited and its empty fibres. -/
theorem wrong_family_not_constant :
    ¬ ∃ T : Type 1, wrongListFamily = fun _ => T := by
  rintro ⟨T, constant⟩
  have emptyPresent : Nonempty (wrongListFamily (Standard.listValue [])) :=
    ⟨wrongEmptyWitness⟩
  have singletonPresent : Nonempty (wrongListFamily (Standard.listValue [false])) := by
    rw [constant] at emptyPresent ⊢
    exact emptyPresent
  exact wrong_singleton_fibre_empty singletonPresent

/-- All empty-list samples and every equal-function pair have actual object
proofs even for the wrong composition order. They cannot supply the missing
universal dependent section. -/
theorem samples_do_not_supply_wrong_section :
    (∀ (f g : Expr Γ mapping), Nonempty (ProofSyntax Symbol equations
      (UniformListMapFusion.Controls.wrongEquation f g nil))) ∧
    (∀ (f : Expr Γ mapping) (xs : Expr Γ sequence), Nonempty (ProofSyntax Symbol theory
      (UniformListMapFusion.Controls.wrongEquation f f xs))) ∧
    ¬ Nonempty (truthFamily Standard.model
      (UniformListMapFusion.Controls.wrongFusion (Γ := [])) Standard.emptyContext) := by
  refine ⟨fun f g => ⟨UniformListMapFusion.Controls.wrong_empty_fits f g⟩,
    fun f xs => ⟨UniformListMapFusion.Controls.wrong_diagonal_fits f xs⟩, ?_⟩
  rintro ⟨sectionValue⟩
  exact UniformListMapFusion.Controls.wrongFusion_invalid sectionValue.down.down

def junkContext : AdmissibleContext JunkModel.model [] :=
  ⟨(fun boundVar => nomatch boundVar), by intro A boundVar; exact nomatch boundVar⟩

/-- This interpretation validates the exact equation assumptions but cannot
supply either induction truth or the universal map-length witness. -/
theorem equations_do_not_supply_induction_section :
    Soundness.SatisfiesHyps JunkModel.model junkContext.1 (equations (Γ := [])) ∧
    ¬ Nonempty (truthFamily JunkModel.model (inductionPrinciple (Γ := [])) junkContext) ∧
    ¬ Nonempty (truthFamily JunkModel.model (mapLength (Γ := [])) junkContext) := by
  refine ⟨?_, ?_, ?_⟩
  · intro formula member
    refine Eq.mp ?_ (JunkModel.equations_valid formula member)
    unfold HenkinModel.models PreModel.models
    apply congrArg ULift.down
    apply congrArg (PreModel.denote JunkModel.model.toPreModel formula)
    funext A boundVar
    nomatch boundVar
  · rintro ⟨sectionValue⟩
    exact JunkModel.induction_invalid sectionValue.down.down
  · rintro ⟨sectionValue⟩
    exact JunkModel.mapLength_invalid sectionValue.down.down

end Controls

#print axioms fusionSection
#print axioms refinementForwardProof
#print axioms refinementBackwardProof
#print axioms fusionRefinementEquiv
#print axioms fusionRefinementEquiv_preserves_input
#print axioms extendTheoryContext
#print axioms Standard.satisfied
#print axioms Standard.listFusionWitness
#print axioms Standard.listFusionWitness_equation
#print axioms Standard.outputRefinement
#print axioms Standard.outputRefinement_input
#print axioms Standard.outputRefinement_property
#print axioms Controls.wrongEmptyWitness
#print axioms Controls.wrong_singleton_fibre_empty
#print axioms Controls.wrong_family_not_constant
#print axioms Controls.samples_do_not_supply_wrong_section
#print axioms Controls.equations_do_not_supply_induction_section

end Mettapedia.Logic.HOL.Embedding.UniformListPredicateFamily
