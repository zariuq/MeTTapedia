import Mettapedia.GSLT.Contracts.RhoParallelLayout
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalOrderAgnosticDepths

/-!
# Changing the hereditary sort preserves rho successor classes

The existing keyed canonicalizer changes only the order of parallel
contents, possibly inside names, payloads and continuations. This
module transports actual authored steps through that relation.
It uses whole-name comparison and equality of canonical contracta,
not equality of the pre-substitution words or stability of their sort.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.RhoHereditaryLayout

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open ParallelOrderAgnostic.ParallelOrderAgnosticList (toForall₂ ofForall₂)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open DerivedContextualStep (RhoStep RhoStepAt)
open CanonicalRepresentativeStep (rhoStepAt_cases rhoStepAt_comm_at rhoStepAt_par_at rhoStepAt_source_bag
  canonicalize_hashBag_eq_of_perm canonicalize_commContractum)

private abbrev Same := ParallelOrderAgnostic rhoReflectivePresentation
private abbrev form := canonicalize rhoReflectivePresentation

mutual
  private theorem same_symm {declaration : ReflectivePresentationDecl} {left right : Pattern}
      (same : ParallelOrderAgnostic declaration left right) :
      ParallelOrderAgnostic declaration right left := by
    cases same with
    | bvar index => exact .bvar index
    | fvar name => exact .fvar name
    | apply head args => exact .apply head (sameList_symm args)
    | lambda binder body => exact .lambda binder (same_symm body)
    | multiLambda arity binders body => exact .multiLambda arity binders (same_symm body)
    | subst body value => exact .subst (same_symm body) (same_symm value)
    | collection kind rest items => exact .collection kind rest (sameList_symm items)
    | parallel first second =>
        obtain ⟨middle, aligned, reorder⟩ :=
          List.perm_comp_forall₂ second.symm (toForall₂ (sameList_symm first))
        exact .parallel (ofForall₂ aligned) reorder

  private theorem sameList_symm {declaration : ReflectivePresentationDecl} {left right : List Pattern}
      (same : ParallelOrderAgnosticList declaration left right) :
      ParallelOrderAgnosticList declaration right left := by
    cases same with
    | nil => exact .nil
    | cons head tail => exact .cons (same_symm head) (sameList_symm tail)
end

private theorem aligned_erase {A : Type*} {rel : A → A → Prop}
    {left right : List A} (aligned : List.Forall₂ rel left right) (i : Nat) :
    List.Forall₂ rel (left.eraseIdx i) (right.eraseIdx i) := by
  induction aligned generalizing i with
  | nil => exact .nil
  | cons first _ ih =>
      cases i with
      | zero => assumption
      | succ i => exact .cons first (ih i)

private theorem input_shape {channel body target : Pattern} {binder : Option String}
    (same : Same (.apply "PInput" [channel, .lambda binder body]) target) :
    ∃ chan' body', target = .apply "PInput" [chan', .lambda binder body'] ∧
      Same channel chan' ∧ Same body body' := by
  cases same with
  | apply _ args =>
      cases args with
      | cons eqChannel tail =>
          cases tail with
          | cons eqBody stop =>
              cases stop
              cases eqBody with
              | lambda _ bodyRel => exact ⟨_, _, rfl, eqChannel, bodyRel⟩

private theorem output_shape {channel value target : Pattern}
    (same : Same (.apply "POutput" [channel, value]) target) :
    ∃ chan' value', target = .apply "POutput" [chan', value'] ∧
      Same channel chan' ∧ Same value value' := by
  cases same with
  | apply _ args =>
      cases args with
      | cons eqChannel tail =>
          cases tail with
          | cons eqValue stop =>
              cases stop
              exact ⟨_, _, rfl, eqChannel, eqValue⟩

private theorem residue_keys {left right : List Pattern} (related : List.Forall₂ Same left right) :
    left.map form = right.map form := by
  induction related with
  | nil => rfl
  | cons same _ ih =>
      simp only [List.map_cons, same.canonicalize_eq, ih]

private theorem joined_result {first second : Pattern} {left right : List Pattern}
    (equal : form first = form second) (residue : List.Forall₂ Same left right) :
    form (.collection .hashBag (first :: left) none) =
      form (.collection .hashBag (second :: right) none) := by
  apply canonicalize_hashBag_eq_of_perm
  have words : (first :: left).map form = (second :: right).map form := by
    simp only [List.map_cons, equal, residue_keys residue]
  rw [words]

private theorem aligned_step {fuel : Nat} {left right : List Pattern} {rest : Option String}
    {target : Pattern}
    (recur : ∀ {depth : Nat}, depth < fuel → ∀ {source arranged out : Pattern},
      Same source arranged → RhoStepAt depth source out →
        ∃ result, RhoStep arranged result ∧ form out = form result)
    (aligned : List.Forall₂ Same left right)
    (start : RhoStepAt fuel (.collection .hashBag left rest) target) :
    ∃ result, RhoStep (.collection .hashBag right rest) result ∧ form target = form result := by
  rcases rhoStepAt_cases start with
    ⟨pieces, tail, inputIndex, inputBound, outputIndex, outputBound, inputChannel, body,
      binder, outputChannel, payload, sourceEq, inputEq, outputEq, agrees, targetEq⟩ |
    ⟨smaller, pieces, tail, index, bound, candidate, fuelEq, sourceEq, childStep, targetEq⟩
  · cases sourceEq
    have inputIn : inputIndex < right.length := aligned.length_eq ▸ inputBound
    have inputRel := aligned.get inputBound inputIn
    change Same left[inputIndex] right[inputIndex] at inputRel
    rw [inputEq] at inputRel
    obtain ⟨input', body', inputShape, chansIn, bodies⟩ := input_shape inputRel
    have withoutInput := aligned_erase aligned inputIndex
    have outputIn : outputIndex < (right.eraseIdx inputIndex).length :=
      withoutInput.length_eq ▸ outputBound
    have outputRel := withoutInput.get outputBound outputIn
    change Same (left.eraseIdx inputIndex)[outputIndex] (right.eraseIdx inputIndex)[outputIndex]
      at outputRel
    rw [outputEq] at outputRel
    obtain ⟨output', payload', outputShape, chansOut, payloads⟩ := output_shape outputRel
    have next := rhoStepAt_comm_at (termRest := rest) inputIn outputIn inputShape outputShape
      (chansIn.canonicalize_eq.symm.trans (agrees.trans chansOut.canonicalize_eq))
    refine ⟨_, ⟨1, next⟩, ?_⟩
    rw [targetEq]
    apply joined_result _ (aligned_erase withoutInput outputIndex)
    unfold form
    rw [canonicalize_commContractum body payload, canonicalize_commContractum body' payload',
      bodies.canonicalize_eq, payloads.canonicalize_eq]
  · cases sourceEq
    have chosenIn : index < right.length := aligned.length_eq ▸ bound
    have selected := aligned.get bound chosenIn
    obtain ⟨result, ⟨n, next⟩, equal⟩ := recur (by omega) selected childStep
    refine ⟨_, ⟨n + 1, rhoStepAt_par_at (termRest := rest) chosenIn next⟩, ?_⟩
    rw [targetEq]
    exact joined_result equal (aligned_erase aligned index)

private theorem transported_at {fuel : Nat} {source arranged target : Pattern}
    (layout : Same source arranged) (step : RhoStepAt fuel source target) :
    ∃ result, RhoStep arranged result ∧ form target = form result := by
  induction fuel using Nat.strong_induction_on generalizing source arranged target with
  | h fuel ih =>
    obtain ⟨pieces, rest, rfl⟩ := rhoStepAt_source_bag step
    cases layout with
    | collection _ _ aligned =>
        exact aligned_step (fun {depth} smaller {_ _ _} eq edge => ih depth smaller eq edge)
          (toForall₂ aligned) step
    | parallel aligned reorder =>
        obtain ⟨intermediate, next, equal⟩ :=
          aligned_step (fun {depth} smaller {_ _ _} eq edge => ih depth smaller eq edge)
            (toForall₂ aligned) step
        obtain ⟨result, later, agrees⟩ := RhoParallelLayout.permute_outer_step reorder next
        exact ⟨result, later, equal.trans agrees⟩

theorem successor_classes_iff {source arranged : Pattern}
    (layout : ParallelOrderAgnostic rhoReflectivePresentation source arranged) (resultKey : Pattern) :
    (∃ t, RhoStep source t ∧ form t = resultKey) ↔
      (∃ t, RhoStep arranged t ∧ form t = resultKey) := by
  constructor
  · rintro ⟨target, ⟨_, step⟩, equal⟩
    obtain ⟨result, transported, observed⟩ := transported_at layout step
    exact ⟨result, transported, observed.symm.trans equal⟩
  · rintro ⟨target, ⟨_, step⟩, equal⟩
    obtain ⟨result, transported, observed⟩ := transported_at (same_symm layout) step
    exact ⟨result, transported, observed.symm.trans equal⟩

/-- The keyed engine may order parallel contents by any rank in a
linear order, with independent choices of both recorded depths. A tie
need not be a canonical key because here only the step meaning is
compared, not literal equality of serialized words. -/
theorem keyed_successors_iff {Key : Type} [LinearOrder Key]
    (rank : Nat → Nat → Pattern → Key) (available scope : Nat) (source resultKey : Pattern) :
    (∃ t, RhoStep (canonicalizeByDepths rank rhoReflectivePresentation available scope source) t ∧
      form t = resultKey) ↔
      (∃ t, RhoStep (form source) t ∧ form t = resultKey) :=
  successor_classes_iff
    (canonicalizeByDepths_parallelOrderAgnostic rank rhoReflectivePresentation available scope source)
    resultKey

#print axioms successor_classes_iff
#print axioms keyed_successors_iff

end Mettapedia.GSLT.Contracts.RhoHereditaryLayout
