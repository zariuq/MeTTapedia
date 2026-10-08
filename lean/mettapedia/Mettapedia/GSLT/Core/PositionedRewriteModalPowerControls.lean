import Mettapedia.GSLT.Core.PositionedRewriteModalPower
import Mettapedia.GSLT.Core.PositionedRewriteModalControls

/-!
# A parameter-sensitive internal modal function

The two predicate inputs are independently named from proper native
subobjects. The postcondition depends on the supplied parameter, while
the rely predicate selects positive assay inputs. Complete evaluation
binds every rely input and admits exactly focuses above that parameter.
Changing the parameter changes the answer, including under a future map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.PositionedRewriteModalPowerControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory ElementaryTypePredicateReadout
open PositionedRewritePredicatePower

abbrev frame := PositionedRewriteModalControls.frame
abbrev classifier := PositionedRewriteModalControls.classifier
abbrev outgoing := frame.assay ⨯ PositionedRewriteModalControls.theory.program

def relies : Subobject (frame.assay ⊗ Nat) :=
  fromSet {supplied | (fst frame.assay Nat supplied).1 > 0}

def postcondition : Subobject (outgoing ⊗ Nat) :=
  fromSet {supplied | (prod.snd : outgoing ⟶ Nat) (fst outgoing Nat supplied) >
    ((prod.fst : outgoing ⟶ Nat × Nat) (fst outgoing Nat supplied)).1 + 1 + snd outgoing Nat supplied}

def relyName : Nat ⟶ power doctrine frame.assay := name doctrine relies
def postName : Nat ⟶ power doctrine outgoing := name doctrine postcondition

def inputs : Nat ⟶ profiles doctrine frame.assay outgoing :=
  lift relyName postName

def modalFunction : profiles doctrine frame.assay outgoing ⟶ power doctrine frame.carrier :=
  PositionedRewriteModalPower.operator frame classifier

theorem independent_rely_read : family doctrine (inputs ≫ fst _ _) = relies := by
  exact (congrArg (family doctrine) (lift_fst relyName postName)).trans
    (family_name doctrine relies)

theorem independent_post_read : family doctrine (inputs ≫ snd _ _) = postcondition := by
  exact (congrArg (family doctrine) (lift_snd relyName postName)).trans
    (family_name doctrine postcondition)

def condition : Subobject ((Nat × Nat) ⊗ Nat) :=
  conditionAt doctrine frame.instantiate frame.outgoing inputs

theorem relies_read (pair : Nat × Nat) (parameter : Nat) :
    Contains relies (pair, parameter) ↔ pair.1 > 0 :=
  contains_fromSet _ _

theorem outgoing_post_read (pair : Nat × Nat) (parameter : Nat) :
    Contains (doctrine.reindex (frame.outgoing ▷ Nat) postcondition) (pair, parameter) ↔
      parameter < pair.2 := by
  rw [contains_reindex]
  unfold postcondition
  rw [contains_fromSet]
  have valueRead := congrArg (fun arrow : (Nat × Nat) ⊗ Nat ⟶ outgoing => arrow (pair, parameter))
    (whiskerRight_fst frame.outgoing Nat)
  have parameterRead := congrArg (fun arrow : (Nat × Nat) ⊗ Nat ⟶ Nat => arrow (pair, parameter))
    (whiskerRight_snd frame.outgoing Nat)
  change fst outgoing Nat ((frame.outgoing ▷ Nat) (pair, parameter)) = frame.outgoing pair at valueRead
  change snd outgoing Nat ((frame.outgoing ▷ Nat) (pair, parameter)) = parameter at parameterRead
  change (prod.snd : outgoing ⟶ Nat) (fst outgoing Nat ((frame.outgoing ▷ Nat) (pair, parameter))) >
    ((prod.fst : outgoing ⟶ Nat × Nat) (fst outgoing Nat ((frame.outgoing ▷ Nat) (pair, parameter)))).1 +
      1 + snd outgoing Nat ((frame.outgoing ▷ Nat) (pair, parameter)) ↔ _
  rw [valueRead, parameterRead]
  have assayRead := congrArg (fun arrow : Nat × Nat ⟶ Nat × Nat => arrow pair)
    (prod.lift_fst frame.instantiate PositionedRewriteModalControls.rule.right)
  have reductRead := congrArg (fun arrow : Nat × Nat ⟶ Nat => arrow pair)
    (prod.lift_snd frame.instantiate PositionedRewriteModalControls.rule.right)
  change (prod.fst : outgoing ⟶ Nat × Nat) (frame.outgoing pair) = pair at assayRead
  change (prod.snd : outgoing ⟶ Nat) (frame.outgoing pair) = pair.1 + pair.2 + 1 at reductRead
  rw [assayRead, reductRead]
  change pair.1 + pair.2 + 1 > pair.1 + 1 + parameter ↔ parameter < pair.2
  omega

theorem condition_read (pair : Nat × Nat) (parameter : Nat) :
    Contains condition (pair, parameter) ↔ (pair.1 > 0 → parameter < pair.2) := by
  change Contains (doctrine.algebra _ |>.himp
    (doctrine.reindex (frame.instantiate ▷ Nat) (family doctrine (inputs ≫ fst _ _)))
    (doctrine.reindex (frame.outgoing ▷ Nat) (family doctrine (inputs ≫ snd _ _)))) _ ↔ _
  rw [independent_rely_read, independent_post_read, contains_implication, contains_reindex]
  have instanceRead : (frame.instantiate ▷ Nat) (pair, parameter) = (pair, parameter) := rfl
  rw [instanceRead, relies_read, outgoing_post_read]

def introduction : Subobject (frame.assignments ⊗ Nat) :=
  doctrine.forallAlong (frame.forget ▷ Nat) condition

theorem introduction_read (focus parameter : Nat) :
    Contains introduction (focus, parameter) ↔ parameter < focus := by
  change Contains (doctrine.forallAlong (frame.forget ▷ Nat) condition) _ ↔ _
  rw [contains_forall]
  constructor
  · intro held
    exact (condition_read (1, focus) parameter).mp (held ((1, focus), parameter) rfl) (by omega)
  · intro held supplied reading
    apply (condition_read supplied.1 supplied.2).mpr
    intro _
    change (supplied.1.2, supplied.2) = (focus, parameter) at reading
    have firstRead := congrArg Prod.fst reading
    have secondRead := congrArg Prod.snd reading
    change supplied.1.2 = focus at firstRead
    change supplied.2 = parameter at secondRead
    rw [firstRead, secondRead]
    exact held

def output : Subobject (frame.carrier ⊗ Nat) :=
  family doctrine (inputs ≫ modalFunction)

theorem output_read (focus parameter : Nat) :
    Contains output (focus, parameter) ↔ parameter < focus := by
  have exactReading := PositionedRewriteModalPower.output_reading frame classifier inputs
  change output = doctrine.existsAlong (frame.focus ▷ Nat) introduction at exactReading
  rw [exactReading, contains_exists]
  constructor
  · rintro ⟨supplied, admitted, reaches⟩
    change supplied = (focus, parameter) at reaches
    subst supplied
    exact (introduction_read focus parameter).mp admitted
  · intro admitted
    exact ⟨(focus, parameter), (introduction_read focus parameter).mpr admitted, rfl⟩

theorem the_parameter_changes_the_exact_answer :
    Contains output (2, 0) ∧ ¬ Contains output (2, 2) := by
  rw [output_read, output_read]
  exact ⟨by omega, Nat.lt_irrefl 2⟩

def future : Nat ⟶ Nat := TypeCat.ofHom Nat.succ

theorem complete_future_read (focus parameter : Nat) :
    Contains (family doctrine ((future ≫ inputs) ≫ modalFunction)) (focus, parameter) ↔
      parameter + 1 < focus := by
  have comparison : doctrine.reindex (frame.carrier ◁ future) output =
      family doctrine ((future ≫ inputs) ≫ modalFunction) := by
    exact (family_substitution doctrine future (inputs ≫ modalFunction)).trans
      (congrArg (family doctrine) (Category.assoc future inputs modalFunction).symm)
  rw [← comparison, contains_reindex]
  exact output_read focus (parameter + 1)

theorem future_context_changes_the_answer :
    Contains output (1, 0) ∧
      ¬ Contains (family doctrine ((future ≫ inputs) ≫
        modalFunction)) (1, 0) := by
  rw [output_read, complete_future_read]
  exact ⟨by omega, Nat.lt_irrefl 1⟩

theorem supplied_parameterized_introduction :
    doctrine.reindex (lift PositionedRewriteModalControls.varyingAssignment (𝟙 Nat))
      (PositionedRewritePredicateLogic.introPredicate doctrine.toFirstOrder (frame.forget ▷ Nat)
        (conditionAt doctrine frame.instantiate frame.outgoing inputs)) = ⊤ := by
  apply (eq_top_iff_contains _).mpr
  intro parameter
  apply (contains_reindex _ _ parameter).mpr
  change Contains introduction (parameter + 1, parameter)
  exact (introduction_read (parameter + 1) parameter).mpr (by omega)

theorem supplied_parameterized_rely :
    doctrine.reindex (lift PositionedRewriteModalControls.varyingAssay (𝟙 Nat))
      (family doctrine (inputs ≫ fst _ _)) = ⊤ := by
  rw [independent_rely_read]
  apply (eq_top_iff_contains _).mpr
  intro parameter
  apply (contains_reindex _ _ parameter).mpr
  change Contains relies ((parameter + 1, parameter + 1), parameter)
  exact (relies_read _ _).mpr (by omega)

/-- This arrow retains the original parameter and the exact native event target. -/
def completeReduct : Nat ⟶ outgoing ⊗ Nat :=
  lift (prod.lift PositionedRewriteModalControls.varyingAssay
    (PositionedRewriteModalControls.varyingEvent ≫ PositionedRewriteModalControls.theory.target)) (𝟙 Nat)

theorem the_supplied_parameterized_reduct_is_typed :
    doctrine.reindex completeReduct postcondition = ⊤ := by
  have retained : doctrine.reindex completeReduct (family doctrine (inputs ≫ snd _ _)) = ⊤ :=
    PositionedRewriteModalPower.supplied_reduct frame classifier inputs
      PositionedRewriteModalControls.varyingAssignment PositionedRewriteModalControls.varyingAssay
      PositionedRewriteModalControls.varying_match supplied_parameterized_introduction supplied_parameterized_rely
  rw [independent_post_read] at retained
  exact retained

theorem full_reduct_retains_the_parameter : completeReduct ≫ snd outgoing Nat = 𝟙 Nat :=
  lift_snd _ _

end Mettapedia.GSLT.Core.PositionedRewriteModalPowerControls
