import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeTyping

/-! A constructor context found in an encoded typed source term reads back
to its actual many-sorted source argument context. Siblings retain their
order, source terms, sorts and declaration. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

private theorem split_arguments {signature : Maude.Signature} {context : Maude.VariableContext}
    (before : List Pattern) {redex : Pattern} {after : List Pattern}
    {arguments : List Maude.Term} {sorts : List String}
    (typed : List.Forall₂ (Maude.HasSort signature context) arguments sorts)
    (shape : arguments.map encode = before ++ redex :: after) :
    ∃ beforeTerms afterTerms beforeSorts afterSorts child hole,
      arguments = beforeTerms ++ child :: afterTerms ∧ sorts = beforeSorts ++ hole :: afterSorts ∧
      beforeTerms.map encode = before ∧ encode child = redex ∧ afterTerms.map encode = after ∧
      List.Forall₂ (Maude.HasSort signature context) beforeTerms beforeSorts ∧
      Maude.HasSort signature context child hole ∧
      List.Forall₂ (Maude.HasSort signature context) afterTerms afterSorts := by
  induction before generalizing arguments sorts with
  | nil =>
      cases typed with
      | nil => simp at shape
      | @cons first sort rest sorts firstTyped restTyped =>
          simp only [List.map_cons, List.nil_append] at shape
          obtain ⟨head, tail⟩ := List.cons.inj shape
          exact ⟨[], rest, [], sorts, first, sort, rfl, rfl, rfl, head, tail, .nil, firstTyped, restTyped⟩
  | cons first before ih =>
      cases typed with
      | nil => simp at shape
      | @cons head sort rest sorts headTyped restTyped =>
          simp only [List.map_cons, List.cons_append] at shape
          obtain ⟨headShape, tailShape⟩ := List.cons.inj shape
          obtain ⟨beforeTerms, afterTerms, beforeSorts, afterSorts, child, hole,
            argumentsEq, sortsEq, beforeEq, childEq, afterEq, beforeTyped, childTyped, afterTyped⟩ :=
            ih restTyped tailShape
          exact ⟨head :: beforeTerms, afterTerms, sort :: beforeSorts, afterSorts, child, hole,
            congrArg (List.cons head) argumentsEq, congrArg (List.cons sort) sortsEq,
            by simp only [List.map_cons, headShape, beforeEq], childEq, afterEq,
            .cons headTyped beforeTyped, childTyped, afterTyped⟩

theorem argument_context_readback {signature : Maude.Signature} {context : Maude.VariableContext}
    {source : Maude.Term} {sort label : String} {before after : List Pattern} {redex : Pattern}
    (typed : Maude.HasSort signature context source sort)
    (shape : encode source = .apply label (before ++ redex :: after)) :
    ∃ (hole : String) (frame : Maude.ArgumentContext signature context hole sort) (child : Maude.Term),
      frame.declaration.id = label ∧ source = frame.plug child ∧ encode child = redex ∧
      frame.before.map encode = before ∧ frame.after.map encode = after ∧
      Maude.HasSort signature context child hole := by
  cases source with
  | var name => rw [encode] at shape; cases shape
  | app id arguments =>
      rw [encode] at shape
      obtain ⟨same, argumentsShape⟩ := Pattern.apply.inj shape
      subst id
      obtain ⟨declaration, declared, labelEq, result, argumentsTyped⟩ := Maude.HasSort.operator_arguments typed rfl
      obtain ⟨beforeTerms, afterTerms, beforeSorts, afterSorts, child, hole,
        argumentsEq, sortsEq, beforeEq, childEq, afterEq, beforeTyped, childTyped, afterTyped⟩ :=
        split_arguments before argumentsTyped argumentsShape
      refine ⟨hole, ⟨declaration, declared, beforeSorts, afterSorts, beforeTerms, afterTerms,
        sortsEq, result, beforeTyped, afterTyped⟩, child, labelEq, ?_, childEq, beforeEq, afterEq, childTyped⟩
      simp only [Maude.ArgumentContext.plug, labelEq]
      exact congrArg (Maude.Term.app label) argumentsEq

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
