import Mettapedia.Languages.VibeITP.Presentation.SignatureExtension
import Mettapedia.Languages.VibeITP.Presentation.OperationsWf

/-!
# Kernel operations under signature extension

Preserving the data of known heads preserves the exact optional result of
shifting, reverse substitution and postorder instantiation.  Arithmetic
refusals and traversal pruning are included in these equalities.  The
structural profile does not impose a word bound on arities or indices.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.Languages.VibeITP.Spec

theorem termShapeList_getD_bvar {sig : Sig} (terms : List Term)
    (shape : TermShapeList sig terms) (index default : Nat) :
    TermShape sig (terms.getD index (.bvar default)) := by
  induction terms generalizing index with
  | nil => simpa using TermShape.bvar (sig := sig) default
  | cons term terms ih =>
      obtain ⟨head, tail⟩ := TermShapeList.cons_iff.mp shape
      cases index with
      | zero => simpa using head
      | succ index => simpa using ih tail index

mutual
theorem shift_sigExt {source target : Sig} (extension : SigExt source target)
    (amount cutoff : Nat) (term : Term) (shape : TermShape source term) :
    shift target amount cutoff term = shift source amount cutoff term := by
  cases term with
  | bvar index => rfl
  | lit bytes => rfl
  | app symbol args =>
      obtain ⟨info, hs, _, hargs⟩ := TermShape.app_iff.mp shape
      simp only [shift, depth_sigExt extension (.app symbol args) shape,
        shiftArgs_eq, bindersOf_sigExt extension ⟨info, hs⟩,
        shiftList_sigExt extension amount cutoff _ args hargs]
termination_by sizeOf term
decreasing_by
  subst_vars
  exact Term.args_sizeOf_lt_app _ _

theorem shiftList_sigExt {source target : Sig} (extension : SigExt source target)
    (amount cutoff : Nat) (binders : List Nat) (terms : List Term)
    (shape : TermShapeList source terms) :
    shiftList target amount cutoff binders terms =
      shiftList source amount cutoff binders terms := by
  cases shape with
  | nil => rfl
  | cons head tail =>
      simp only [shiftList, shift_sigExt extension amount (cutoff + binders.headD 0) _ head,
        shiftList_sigExt extension amount cutoff binders.tail _ tail]
termination_by sizeOf terms
decreasing_by
  · exact term_head_sizeOf_lt_cons _ _
  · exact term_tail_sizeOf_lt_cons _ _
end

theorem shiftArgs_sigExt {source target : Sig} (extension : SigExt source target)
    (amount cutoff index : Nat) (symbol : SymId) (known : KnownSymbol source symbol)
    (terms : List Term) (shape : TermShapeList source terms) :
    shiftArgs target amount symbol cutoff index terms =
      shiftArgs source amount symbol cutoff index terms := by
  simp only [shiftArgs_eq, bindersOf_sigExt extension known,
    shiftList_sigExt extension amount cutoff _ terms shape]

mutual
theorem subst_sigExt {source target : Sig} (extension : SigExt source target)
    (numArgs : Nat) (args : List Term) (argsShape : TermShapeList source args)
    (offset : Nat) (term : Term) (shape : TermShape source term) :
    substGo target numArgs args offset term = substGo source numArgs args offset term := by
  cases term with
  | bvar index =>
      simp only [substGo, shift_sigExt extension offset 0 _
        (termShapeList_getD_bvar args argsShape (numArgs - 1 - (index - offset)) 0)]
  | lit bytes => rfl
  | app symbol terms =>
      obtain ⟨info, hs, _, hterms⟩ := TermShape.app_iff.mp shape
      simp only [substGo, depth_sigExt extension (.app symbol terms) shape,
        substGoArgs_eq, bindersOf_sigExt extension ⟨info, hs⟩,
        substList_sigExt extension numArgs args argsShape offset _ terms hterms]
termination_by sizeOf term
decreasing_by
  subst_vars
  exact Term.args_sizeOf_lt_app _ _

theorem substList_sigExt {source target : Sig} (extension : SigExt source target)
    (numArgs : Nat) (args : List Term) (argsShape : TermShapeList source args)
    (offset : Nat) (binders : List Nat) (terms : List Term)
    (shape : TermShapeList source terms) :
    substList target numArgs args offset binders terms =
      substList source numArgs args offset binders terms := by
  cases shape with
  | nil => rfl
  | cons head tail =>
      simp only [substList,
        subst_sigExt extension numArgs args argsShape (offset + binders.headD 0) _ head,
        substList_sigExt extension numArgs args argsShape offset binders.tail _ tail]
termination_by sizeOf terms
decreasing_by
  · exact term_head_sizeOf_lt_cons _ _
  · exact term_tail_sizeOf_lt_cons _ _
end

theorem substGoArgs_sigExt {source target : Sig} (extension : SigExt source target)
    (numArgs : Nat) (args : List Term) (argsShape : TermShapeList source args)
    (symbol : SymId) (known : KnownSymbol source symbol) (offset index : Nat)
    (terms : List Term) (shape : TermShapeList source terms) :
    substGoArgs target numArgs args symbol offset index terms =
      substGoArgs source numArgs args symbol offset index terms := by
  simp only [substGoArgs_eq, bindersOf_sigExt extension known,
    substList_sigExt extension numArgs args argsShape offset _ terms shape]

theorem substBVars_sigExt {source target : Sig} (extension : SigExt source target)
    (numArgs : Nat) (args : List Term) (argsShape : TermShapeList source args)
    (body : Term) (shape : TermShape source body) (offset : Nat) :
    substBVars target numArgs args body offset = substBVars source numArgs args body offset := by
  simp only [substBVars, subst_sigExt extension numArgs args argsShape offset body shape]

mutual
theorem inst_sigExt {source target : Sig} (extension : SigExt source target)
    (F : SymId) (arity : Nat) (value : Term) (valueShape : TermShape source value)
    (fvar : IsFvarOf source F arity) (offset : Nat) (term : Term)
    (shape : TermShape source term) :
    instGo target F arity value offset term = instGo source F arity value offset term := by
  cases term with
  | bvar index => rfl
  | lit bytes => rfl
  | app symbol terms =>
      obtain ⟨info, hs, _, hterms⟩ := TermShape.app_iff.mp shape
      simp only [instGo, hasFvar_sigExt extension (.app symbol terms) shape,
        instArgs_eq, bindersOf_sigExt extension ⟨info, hs⟩,
        instList_sigExt extension F arity value valueShape fvar offset _ terms hterms]
      split
      · rfl
      · cases hi : instList source F arity value offset
            ((bindersOf source symbol).drop 0) terms with
        | none => rfl
        | some terms' =>
            simp only
            have hterms' := instList_termShape source F arity value offset
              ((bindersOf source symbol).drop 0) terms terms' valueShape fvar hterms hi
            by_cases heq : symbol = F
            · simp only [heq, if_true]
              rw [shift_sigExt extension offset arity value valueShape]
              cases hv : shift source offset arity value with
              | none => rfl
              | some value' =>
                  exact substBVars_sigExt extension arity terms' hterms' value'
                    (shift_termShape source offset arity value value' valueShape hv) 0
            · simp only [heq, if_false]
termination_by sizeOf term
decreasing_by
  subst_vars
  exact Term.args_sizeOf_lt_app _ _

theorem instList_sigExt {source target : Sig} (extension : SigExt source target)
    (F : SymId) (arity : Nat) (value : Term) (valueShape : TermShape source value)
    (fvar : IsFvarOf source F arity) (offset : Nat) (binders : List Nat)
    (terms : List Term) (shape : TermShapeList source terms) :
    instList target F arity value offset binders terms =
      instList source F arity value offset binders terms := by
  cases shape with
  | nil => rfl
  | cons head tail =>
      simp only [instList,
        inst_sigExt extension F arity value valueShape fvar (offset + binders.headD 0) _ head,
        instList_sigExt extension F arity value valueShape fvar offset binders.tail _ tail]
termination_by sizeOf terms
decreasing_by
  · exact term_head_sizeOf_lt_cons _ _
  · exact term_tail_sizeOf_lt_cons _ _
end

theorem instArgs_sigExt {source target : Sig} (extension : SigExt source target)
    (F : SymId) (arity : Nat) (value : Term) (valueShape : TermShape source value)
    (fvar : IsFvarOf source F arity) (symbol : SymId) (known : KnownSymbol source symbol)
    (offset index : Nat) (terms : List Term) (shape : TermShapeList source terms) :
    instArgs target F arity value symbol offset index terms =
      instArgs source F arity value symbol offset index terms := by
  simp only [instArgs_eq, bindersOf_sigExt extension known,
    instList_sigExt extension F arity value valueShape fvar offset _ terms shape]

theorem isFvarOf_sigExt {source target : Sig} (extension : SigExt source target)
    {F : SymId} {arity : Nat} (fvar : IsFvarOf source F arity) :
    IsFvarOf target F arity := by
  obtain ⟨info, hs⟩ := Option.isSome_iff_exists.mp fvar.1
  refine ⟨by simp [extension F info hs], ?_, ?_⟩
  · rw [kindOf_sigExt extension ⟨info, hs⟩]
    exact fvar.2.1
  · rw [symArity_sigExt extension ⟨info, hs⟩]
    exact fvar.2.2

theorem instantiateStatement_sigExt {source target : Sig}
    (extension : SigExt source target) (F : SymId) (known : KnownSymbol source F)
    (value statement : Term) (valueShape : TermShape source value)
    (statementShape : TermShape source statement) :
    instantiateStatement target F value statement =
      instantiateStatement source F value statement := by
  obtain ⟨info, hs⟩ := known
  simp only [instantiateStatement, hs, extension F info hs,
    depth_sigExt extension value valueShape]
  by_cases guard : info.kind = .fvar ∧ depth source value ≤ info.arity
  · simp only [guard]
    have fvar : IsFvarOf source F info.arity := by
      simp [IsFvarOf, hs, kindOf, symArity, guard.1]
    rw [inst_sigExt extension F info.arity value valueShape fvar 0 statement statementShape]
    cases result : instGo source F info.arity value 0 statement with
    | none => rfl
    | some output =>
        have outputShape := inst_termShape source F info.arity value 0 statement output
          valueShape fvar statementShape result
        simp only [depth_sigExt extension output outputShape]
  · simp only [guard, if_false]

theorem instantiateStatement_known {sig : Sig} {F : SymId} {value statement result : Term}
    (success : instantiateStatement sig F value statement = some result) :
    KnownSymbol sig F := by
  cases hs : sig F with
  | none => simp [instantiateStatement, hs] at success
  | some info => exact ⟨info, hs⟩

theorem instantiateStatement_success_sigExt {source target : Sig}
    (extension : SigExt source target) (F : SymId) (value statement result : Term)
    (valueShape : TermShape source value) (statementShape : TermShape source statement)
    (success : instantiateStatement source F value statement = some result) :
    instantiateStatement target F value statement = some result := by
  rw [instantiateStatement_sigExt extension F (instantiateStatement_known success)
    value statement valueShape statementShape]
  exact success

end Mettapedia.Languages.VibeITP.Presentation
