import Mettapedia.Languages.VibeITP.Presentation.SimultaneousEnvironmentSoundness

/-! The new traversal rules preserve the original source operation, including
the free-variable pruning branch, bound arithmetic and argument order. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Spec Spec.SimultaneousInstantiation SimultaneousFormation

theorem ms_rManyNofv (T : Theory) (entries offset term : Pattern)
    (noVariables : MeaningV2 T (jHasFv term cFalse)) :
    MeaningV2 T (jMany entries offset term term) := by
  change HasFvM T.sig term cFalse at noVariables
  intro prepared position source _ _ _ sourceCode
  have no := noVariables source sourceCode
  have absent : hasFvar T.sig source = false := by
    cases found : hasFvar T.sig source with
    | false => rfl
    | true => simp [found, encBool, cFalse, cTrue] at no
  refine ⟨source, ?_, sourceCode⟩
  cases source <;> simp [go, absent]

theorem ms_rManyConst (T : Theory) (entries o idv bs ts d us e g : Pattern)
    (children : MeaningV2 T (jManyArgs entries o bs ts us))
    (annotations : MeaningV2 T (jAnnArgs bs us e g)) :
    MeaningV2 T (jMany entries o
      (cApp (cSym idv cKConst bs) ts (cAnn d cTrue))
      (cApp (cSym idv cKConst bs) us (cAnn e g))) := by
  change ManyArgsM T.sig entries o bs ts us at children
  change AnnArgsM T.sig bs us e g at annotations
  intro prepared position source valid entriesCode offsetCode sourceCode
  obtain ⟨symbol, arguments, rfl, symbolCode, rfl, inputAnnotation⟩ :=
    encTerm_eq_app T.sig source _ _ _ sourceCode.symm
  obtain ⟨numberCode, kindCode, bindersCode⟩ := encSym_parts T.sig symbol symbolCode
  subst numberCode bindersCode
  have constant : kindOf T.sig symbol = .constant := by
    cases kind : kindOf T.sig symbol with
    | constant => rfl
    | fvar => simp [kind, encKind, cKConst, cKFvar] at kindCode
  have missed : lookup prepared symbol = none := by
    cases selected : lookup prepared symbol with
    | none => rfl
    | some entry =>
        obtain ⟨member, same⟩ := lookup_member _ _ _ selected
        have free := (valid entry member).1.2.1
        rw [same, constant] at free
        cases free
  simp only [cAnn, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at inputAnnotation
  have has : hasFvar T.sig (.app symbol arguments) = true := by
    rw [hasFvar_app]
    cases found : (isFvarSym T.sig symbol || hasFvarList T.sig arguments) with
    | false => simp [found, encBool, cFalse, cTrue] at inputAnnotation
    | true => rfl
  obtain ⟨output, computed, rfl, _⟩ := children prepared position _ arguments valid entriesCode offsetCode rfl rfl
  obtain ⟨rfl, rfl⟩ := annotations _ output rfl rfl
  refine ⟨.app symbol output, ?_, ?_⟩
  · simp only [go, has, Bool.true_eq_false, if_false, args_eq_argumentList, List.drop_zero, computed, missed]
  · rw [encTerm_app', encSym_eq, isFvarSym_eq, constant]
    rfl

theorem ms_rManyAbsent (T : Theory) (entries o fid fbs ts d us e g : Pattern)
    (absent : MeaningV2 T (jManyMiss entries (cSym fid cKFvar fbs)))
    (children : MeaningV2 T (jManyArgs entries o fbs ts us))
    (annotations : MeaningV2 T (jAnnArgs fbs us e g)) :
    MeaningV2 T (jMany entries o (cApp (cSym fid cKFvar fbs) ts (cAnn d cTrue))
      (cApp (cSym fid cKFvar fbs) us (cAnn e cTrue))) := by
  change MissM T.sig entries (cSym fid cKFvar fbs) at absent
  change ManyArgsM T.sig entries o fbs ts us at children
  change AnnArgsM T.sig fbs us e g at annotations
  intro prepared position source valid entriesCode offsetCode sourceCode
  obtain ⟨symbol, arguments, rfl, symbolCode, rfl, _⟩ :=
    encTerm_eq_app T.sig source _ _ _ sourceCode.symm
  obtain ⟨numberCode, kindCode, bindersCode⟩ := encSym_parts T.sig symbol symbolCode
  have free : kindOf T.sig symbol = .fvar := by
    cases kind : kindOf T.sig symbol with
    | constant => simp [kind, encKind, cKConst, cKFvar] at kindCode
    | fvar => rfl
  have missed := absent prepared symbol valid entriesCode symbolCode
  subst bindersCode
  obtain ⟨output, computed, rfl, _⟩ := children prepared position _ arguments valid entriesCode offsetCode rfl rfl
  obtain ⟨rfl, _⟩ := annotations _ output rfl rfl
  have isFree : isFvarSym T.sig symbol = true := by rw [isFvarSym_eq, free]; rfl
  have has : hasFvar T.sig (.app symbol arguments) = true := by rw [hasFvar_app, isFree]; rfl
  subst numberCode
  refine ⟨.app symbol output, ?_, ?_⟩
  · simp only [go, has, Bool.true_eq_false, if_false, args_eq_argumentList, List.drop_zero, computed, missed]
  · rw [encTerm_app', encSym_eq, isFree, free]
    rfl

theorem ms_rManySelected (T : Theory) (entries o fid fbs n v ts d us w r : Pattern)
    (selected : MeaningV2 T (jManyHit entries (cSym fid cKFvar fbs) n v))
    (children : MeaningV2 T (jManyArgs entries o fbs ts us))
    (shifted : MeaningV2 T (jShift o n v w))
    (substituted : MeaningV2 T (jSubstTop n us w r)) :
    MeaningV2 T (jMany entries o (cApp (cSym fid cKFvar fbs) ts (cAnn d cTrue)) r) := by
  change HitM T.sig entries (cSym fid cKFvar fbs) n v at selected
  change ManyArgsM T.sig entries o fbs ts us at children
  change ShiftM T.sig o n v w at shifted
  change SubstTopM T.sig n us w r at substituted
  intro prepared position source valid entriesCode offsetCode sourceCode
  obtain ⟨symbol, arguments, rfl, symbolCode, rfl, _⟩ :=
    encTerm_eq_app T.sig source _ _ _ sourceCode.symm
  obtain ⟨entry, found, arityCode, valueCode⟩ := selected prepared symbol valid entriesCode symbolCode
  obtain ⟨member, same⟩ := lookup_member _ _ _ found
  have entryValid := valid entry member
  have free : kindOf T.sig symbol = .fvar := by simpa only [same] using entryValid.1.2.1
  have arity : symArity T.sig symbol = entry.arity := by simpa only [same] using entryValid.1.2.2
  have bindersCode := (encSym_parts T.sig symbol symbolCode).2.2
  obtain ⟨output, computed, rfl, length⟩ := children prepared position _ arguments valid entriesCode offsetCode bindersCode rfl
  obtain ⟨shiftedValue, shiftedResult, rfl⟩ := shifted position entry.arity entry.value offsetCode arityCode valueCode
  have outputLength : output.length = entry.arity := by
    rw [argumentList_length _ _ _ _ _ _ computed, length, ← symArity_eq]
    exact arity
  obtain ⟨result, substitutedResult, rfl⟩ := substituted entry.arity output shiftedValue arityCode rfl outputLength rfl
  have isFree : isFvarSym T.sig symbol = true := by rw [isFvarSym_eq, free]; rfl
  have has : hasFvar T.sig (.app symbol arguments) = true := by rw [hasFvar_app, isFree]; rfl
  refine ⟨result, ?_, rfl⟩
  simp only [go, has, Bool.true_eq_false, if_false, args_eq_argumentList, List.drop_zero,
    computed, found, shiftedResult, substitutedResult]

theorem ms_rManyArgsNil (T : Theory) (entries o : Pattern) :
    MeaningV2 T (jManyArgs entries o cNil cNil cNil) := by
  intro prepared position binders terms _ _ _ bindersCode termsCode
  rw [encTermList_eq_nil T.sig terms termsCode.symm, encNatList_eq_nil binders bindersCode.symm]
  exact ⟨[], rfl, rfl, rfl⟩

theorem ms_rManyArgsCons (T : Theory) (entries o b bs t ts u us k : Pattern)
    (added : MeaningV2 T (jNAdd o b k)) (bounded : MeaningV2 T (jNWord k))
    (head : MeaningV2 T (jMany entries k t u)) (tail : MeaningV2 T (jManyArgs entries o bs ts us)) :
    MeaningV2 T (jManyArgs entries o (cCons b bs) (cCons t ts) (cCons u us)) := by
  change NAddM o b k at added
  change NWordM k at bounded
  change ManyM T.sig entries k t u at head
  change ManyArgsM T.sig entries o bs ts us at tail
  obtain ⟨word, readWord, bound⟩ := bounded
  intro prepared position binders terms valid entriesCode offsetCode bindersCode termsCode
  obtain ⟨binder, binders', rfl, firstBinder, restBinders⟩ := encNatList_eq_cons binders b bs bindersCode.symm
  obtain ⟨first, rest, rfl, firstCode, restCode⟩ := encTermList_eq_cons T.sig terms t ts termsCode.symm
  have sum := added.1 position binder (decNat_of_eq offsetCode) (decNat_of_eq firstBinder)
  rw [readWord] at sum
  cases sum
  obtain ⟨output, computed, rfl⟩ := head prepared (position + binder) first valid entriesCode
    (decNat_unique k _ readWord) firstCode
  obtain ⟨outputs, remaining, rfl, length⟩ := tail prepared position binders' rest valid entriesCode offsetCode restBinders restCode
  refine ⟨output :: outputs, ?_, by rw [encTermList_cons], by simp [length]⟩
  simp only [argumentList, List.headD_cons, List.tail_cons, bound, if_true, computed, remaining]

#print axioms ms_rManyConst
#print axioms ms_rManySelected
#print axioms ms_rManyArgsCons

end Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation
