import Mettapedia.Logic.HOL.IndexedContainerDirectPositions
import Mettapedia.Logic.HOL.OrderedConstructorSelectedChildren
import Mettapedia.Logic.HOL.OrderedPositionFunctionalityControls
import Mettapedia.GSLT.LanguageDef.IndexedContainerPositionTermsControls
import Mettapedia.GSLT.LanguageDef.AdmittedChildPremiseControls
import Mettapedia.GSLT.LanguageDef.AdmittedChildPremiseModelControls

/-!
# Source-selected recursive positions and repeated-index controls

The actual mixed List/Vector description has direct segments before and
after both registered segments. Their counts are proved equal to one and
their slot witnesses retain source ordinals through open prefixes. Separate
equal-index segments cannot exchange their slots. The original admitted
Cons child proof retains this stronger selection beside membership/motive.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.DirectPositionSelectionControls

open Mettapedia.Logic.HOL
open OrderedPositionPrograms SuccessorOrder FiniteConstructorEncoding CurriedPredicates

namespace Repeated

open OrderedPositionProofControls (number Symbol zero successor one model values full numbers zero_preserved successor_preserved)

def plan : Plan Symbol [] number .prop := [(one, .top), (one, .top)]

def first : ProofSyntax Symbol [] (selectedAt zero successor 0 plan Subst.id zero .top) :=
  .andI (lessNext successor zero) (.eqRefl .top)

def second : ProofSyntax Symbol [] (selectedAt zero successor 1 plan Subst.id one .top) :=
  selectedAt_later zero successor 0 (one, .top) [(one, .top)] Subst.id one zero .top
    (sumZero successor zero one) (.andI (lessNext successor zero) (.eqRefl .top))

theorem first_free : first.FunctionExtensionalityFree := ⟨lessNext_free _ _, True.intro⟩
theorem second_free : second.FunctionExtensionalityFree :=
  selectedAt_later_free zero successor 0 (one, .top) [(one, .top)] Subst.id one zero .top _ _
    (sumZero_free _ _ _) ⟨lessNext_free _ _, True.intro⟩

theorem first_valid : (model.denote (selectedAt zero successor 0 plan Subst.id zero .top) @values).down :=
  Soundness.extDerivation_sound first.erase (model.functionsRespectEqv_of_fullDomains full)
    (by intro _ impossible; nomatch impossible) (by intro _ impossible; nomatch impossible)

theorem second_valid : (model.denote (selectedAt zero successor 1 plan Subst.id one .top) @values).down :=
  Soundness.extDerivation_sound second.erase (model.functionsRespectEqv_of_fullDomains full)
    (by intro _ impossible; nomatch impossible) (by intro _ impossible; nomatch impossible)

theorem wrong_segment_at_zero_refused :
    ¬ Nonempty (ProofSyntax Symbol [] (selectedAt zero successor 1 plan Subst.id zero .top)) := by
  rintro ⟨proof⟩
  have valid := Soundness.extDerivation_sound proof.erase (M := model) (ρ := @values) (model.functionsRespectEqv_of_fullDomains full)
    (by intro _ impossible; nomatch impossible) (by intro _ impossible; nomatch impossible)
  change ∃ offset : ULift.{1} Nat, True ∧
    (model.denote (sum zero successor) @values (ULift.up 1) offset (ULift.up 0)).down ∧ _ at valid
  obtain ⟨offset, _, shifted, _⟩ := valid
  have impossible := (sum_iff model full successor @values zero numbers zero_preserved successor_preserved
    (ULift.up 1) offset (ULift.up 0)).mp shifted
  change (0 : Nat) = 1 + offset.down at impossible
  omega

theorem absent_segment_refused :
    ¬ Nonempty (ProofSyntax Symbol [] (selectedAt zero successor 2 plan Subst.id zero .top)) := by
  rintro ⟨proof⟩
  have valid := Soundness.extDerivation_sound proof.erase (M := model) (ρ := @values) (model.functionsRespectEqv_of_fullDomains full)
    (by intro _ impossible; nomatch impossible) (by intro _ impossible; nomatch impossible)
  change ∃ offset : ULift.{1} Nat, True ∧ _ ∧
    ∃ next : ULift.{1} Nat, True ∧ _ ∧ False at valid
  obtain ⟨_, _, _, _, _, _, impossible⟩ := valid
  exact impossible

end Repeated

namespace Mixed

open IndexedContainerPositionTerms IndexedContainerPositionTermsControls

abbrev context : Ctx Unit := [number, number, number, number]
def substitution : Subst Symbol [] context := fun impossible => nomatch impossible
def arguments : Arguments Symbol context (reading.fields mixedCode) :=
  (.var (.vs (.vs (.vs .vz))), (.var (.vs (.vs .vz)), (.var (.vs .vz), (.var .vz, PUnit.unit))))

def assumptions : List (Formula Symbol context) :=
  [NaturalRecursionProofs.inductionPrinciple (weakenCtx context zero) (weakenCtx context successor)]
def principle : ProofSyntax Symbol assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx context zero) (weakenCtx context successor)) :=
  .hyp (Δ := assumptions) ⟨0, by change 0 < 1; decide⟩

theorem exact_source_marks : Reading.directFlags mixedCode = [true, false, false, true] := rfl

def onePositive : ProofSyntax Symbol assumptions
    (.app (.app (weakenCtx context (less successor)) (weakenCtx context zero)) (weakenCtx context reading.one)) :=
  lessNext successor (weakenCtx context zero)

def first := Reading.directSelectedExists (reading := reading) mixedCode substitution arguments 0 (by decide) zero successor principle onePositive
def last := Reading.directSelectedExists (reading := reading) mixedCode substitution arguments 3 (by decide) zero successor principle onePositive

theorem first_free : first.FunctionExtensionalityFree := by
  apply Reading.directSelectedExists_free
  · trivial
  · exact lessNext_free _ _

theorem last_free : last.FunctionExtensionalityFree := by
  apply Reading.directSelectedExists_free
  · trivial
  · exact lessNext_free _ _

theorem registered_segment_not_direct : (Reading.directFlags mixedCode)[1]? ≠ some true := by decide

def firstCount := Reading.directCountProof (reading := reading) mixedCode substitution arguments 0 (by decide) (hypotheses := assumptions)
def lastCount := Reading.directCountProof (reading := reading) mixedCode substitution arguments 3 (by decide) (hypotheses := assumptions)

theorem assumptions_realizable (values : model.Valuation context) :
    ∀ formula ∈ assumptions, (model.denote formula values).down := by
  intro formula member
  have same : formula = NaturalRecursionProofs.inductionPrinciple (weakenCtx context zero) (weakenCtx context successor) := by
    simpa only [assumptions, List.mem_singleton] using member
  subst formula
  change ∀ predicate : ULift.{1} Nat → ULift.{1} Prop, True →
    ((predicate (ULift.up 0)).down ∧
      ∀ value : ULift.{1} Nat, True → (predicate value).down → (predicate (ULift.up (value.down + 1))).down) →
      ∀ value : ULift.{1} Nat, True → (predicate value).down
  intro predicate _ premises value _
  rcases value with ⟨n⟩
  induction n with
  | zero => exact premises.1
  | succ n previous => exact premises.2 (ULift.up n) True.intro previous

end Mixed

namespace Cons

open AdmittedContainerHOL AdmittedContainerGeneratedControls

noncomputable section

def selected : ProofSyntax Symbol AdmittedChildPremiseControls.assumptions
    (selectedAt AdmittedChildPremiseControls.zero AdmittedChildPremiseControls.successor 0
      (fieldTerms _ (AdmittedChildPremiseControls.plans consOccurrence) Subst.id AdmittedChildPremiseControls.arguments)
      Subst.id AdmittedChildPremiseControls.target AdmittedChildPremiseControls.target) := by
  let body : Formula Symbol AdmittedChildPremiseControls.context :=
    (.and (.app (.app (weakenCtx _ (less AdmittedChildPremiseControls.successor)) AdmittedChildPremiseControls.target)
      (applyFields _ ((AdmittedChildPremiseControls.plans consOccurrence).get ⟨0, by decide⟩).1 AdmittedChildPremiseControls.arguments))
      (.eq AdmittedChildPremiseControls.target AdmittedChildPremiseControls.fieldIndex))
  have same : selectedAt AdmittedChildPremiseControls.zero AdmittedChildPremiseControls.successor 0
      (fieldTerms _ (AdmittedChildPremiseControls.plans consOccurrence) Subst.id AdmittedChildPremiseControls.arguments)
      Subst.id AdmittedChildPremiseControls.target AdmittedChildPremiseControls.target = body :=
    eq_of_heq (stagedHEq% selectedAt AdmittedChildPremiseControls.zero AdmittedChildPremiseControls.successor 0
      (fieldTerms _ (AdmittedChildPremiseControls.plans consOccurrence) Subst.id AdmittedChildPremiseControls.arguments)
      Subst.id AdmittedChildPremiseControls.target AdmittedChildPremiseControls.target, body)
  apply ProofSyntax.castIndices rfl same.symm
  exact .andI
    (.impE (.eqPropER (.eqAppArg
      (.app (weakenCtx _ (less AdmittedChildPremiseControls.successor)) AdmittedChildPremiseControls.target)
      AdmittedChildPremiseControls.countBeta))
      (lessNext AdmittedChildPremiseControls.successor AdmittedChildPremiseControls.target))
    (.eqSymm AdmittedChildPremiseControls.indexBeta)

def child := IndexedConstructorGuards.PositionPrograms.selectedChildAtFromLookup
  AdmittedChildPremiseControls.constructors AdmittedChildPremiseControls.zero AdmittedChildPremiseControls.successor
  AdmittedChildPremiseControls.plans AdmittedContainerInductionControls.bottom AdmittedContainerInductionControls.ctor
  AdmittedContainerInductionControls.motive consOccurrence AdmittedChildPremiseControls.arguments
  AdmittedChildPremiseControls.children 0 AdmittedChildPremiseControls.target AdmittedChildPremiseControls.target
  AdmittedChildPremiseControls.peano AdmittedChildPremiseControls.conditionProof AdmittedChildPremiseControls.allowed selected

theorem selected_free : selected.FunctionExtensionalityFree := by
  unfold selected
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ⟨⟨AdmittedChildPremiseControls.countBeta_free, lessNext_free _ _⟩,
    AdmittedChildPremiseControls.indexBeta_free⟩

theorem child_free : child.FunctionExtensionalityFree := by
  apply IndexedConstructorGuards.PositionPrograms.selectedChildAtFromLookup_free
  · exact AdmittedChildPremiseControls.peano_free
  · exact AdmittedChildPremiseControls.conditionProof_free
  · exact AdmittedChildPremiseControls.allowed_free
  · exact selected_free

theorem child_valid : (model.denote
    (.and (selectedAt AdmittedChildPremiseControls.zero AdmittedChildPremiseControls.successor 0
      (fieldTerms _ (AdmittedChildPremiseControls.plans consOccurrence) Subst.id AdmittedChildPremiseControls.arguments)
      Subst.id AdmittedChildPremiseControls.target AdmittedChildPremiseControls.target)
      (.and (.app (.app (AdmittedChildPremiseControls.signature.memberProgram
        (AdmittedChildPremiseControls.constructors.rootProgram AdmittedContainerInductionControls.ctor))
        (.app AdmittedChildPremiseControls.children AdmittedChildPremiseControls.target)) AdmittedChildPremiseControls.target)
        (.app (.app AdmittedContainerInductionControls.motive
          (.app AdmittedChildPremiseControls.children AdmittedChildPremiseControls.target)) AdmittedChildPremiseControls.target)))
    AdmittedChildPremiseModelControls.world).down :=
  Soundness.extDerivation_sound child.erase (model.functionsRespectEqv_of_fullDomains full)
    (by intro type index; exact full type (AdmittedChildPremiseModelControls.world index))
    AdmittedChildPremiseModelControls.assumptions_realizable

end
end Cons

#print axioms Repeated.wrong_segment_at_zero_refused
#print axioms Repeated.absent_segment_refused
#print axioms Mixed.last_free
#print axioms Cons.child
#print axioms Cons.child_free
#print axioms Cons.child_valid

end Mettapedia.GSLT.LanguageDef.DirectPositionSelectionControls
