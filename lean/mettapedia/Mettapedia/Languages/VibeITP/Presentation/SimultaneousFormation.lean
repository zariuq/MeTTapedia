import Mettapedia.Languages.VibeITP.Spec.SimultaneousInstantiation
import Mettapedia.Languages.VibeITP.Presentation.SignatureExtensionOperations

/-!
# Formation through simultaneous substitution

Prepared entries retain their actual signature arities and formed values.
Successful traversal preserves the existing structural term profile; arithmetic
and closure guards remain in the source operation. These laws supply the
formation premises needed by derivability and later theory extension.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousFormation

open Mettapedia.Languages.VibeITP.Spec
open Spec.SimultaneousInstantiation

def argumentList (sig : Spec.Sig) (entries : List Spec.SimultaneousInstantiation.Entry) (offset : Nat) :
    List Nat → List Spec.Term → Option (List Spec.Term)
  | _, [] => some []
  | binders, first :: rest =>
      if offset + binders.headD 0 < Spec.wordBound then
        match Spec.SimultaneousInstantiation.go sig entries (offset + binders.headD 0) first,
            argumentList sig entries offset binders.tail rest with
        | some first', some rest' => some (first' :: rest')
        | _, _ => none
      else none

theorem args_eq_argumentList (sig : Spec.Sig) (entries : List Spec.SimultaneousInstantiation.Entry)
    (symbol : Spec.SymId) (offset : Nat) : ∀ (index : Nat) (arguments : List Spec.Term),
    Spec.SimultaneousInstantiation.args sig entries symbol offset index arguments =
      argumentList sig entries offset ((bindersOf sig symbol).drop index) arguments
  | _, [] => rfl
  | index, first :: rest => by
      rw [Spec.SimultaneousInstantiation.args, argumentList,
        args_eq_argumentList sig entries symbol offset (index + 1) rest,
        binderAt_eq, drop_headD, drop_tail]
      split <;> rfl

theorem argumentList_length (sig : Sig) (entries : List Entry) (offset : Nat) :
    ∀ (binders : List Nat) (source result : List Spec.Term),
      argumentList sig entries offset binders source = some result → result.length = source.length
  | _, [], result, accepted => by
      have same : [] = result := Option.some.inj accepted
      subst result
      rfl
  | binders, first :: rest, result, accepted => by
      simp only [argumentList] at accepted
      split at accepted
      · cases head : go sig entries (offset + binders.headD 0) first with
        | none => simp only [head] at accepted; cases accepted
        | some output =>
            cases tail : argumentList sig entries offset binders.tail rest with
            | none => simp only [head, tail] at accepted; cases accepted
            | some outputs =>
                have same : output :: outputs = result := by simpa only [head, tail, Option.some.injEq] using accepted
                subst result
                simp only [List.length_cons, argumentList_length sig entries offset binders.tail rest outputs tail]
      · cases accepted

def EntryShape (sig : Sig) (entry : Entry) : Prop :=
  IsFvarOf sig entry.symbol entry.arity ∧ TermShape sig entry.value

def EntriesShape (sig : Sig) (entries : List Entry) : Prop :=
  ∀ entry ∈ entries, EntryShape sig entry

def ValuesShape (sig : Sig) (replacements : List (SymId × Term)) : Prop :=
  ∀ pair ∈ replacements, TermShape sig pair.2

theorem lookup_member : ∀ (entries : List Entry) (symbol : SymId) (entry : Entry),
    lookup entries symbol = some entry → entry ∈ entries ∧ entry.symbol = symbol
  | [], _, _, success => by simp [lookup] at success
  | first :: rest, symbol, entry, success => by
      simp only [lookup] at success
      split at success
      · rename_i same
        have identified := Option.some.inj success
        subst entry
        exact ⟨List.mem_cons_self, same.symm⟩
      · obtain ⟨member, same⟩ := lookup_member rest symbol entry success
        exact ⟨List.mem_cons_of_mem first member, same⟩

theorem prepare_shape (sig : Sig) : ∀ (replacements : List (SymId × Term)) (entries : List Entry),
    ValuesShape sig replacements → prepare sig replacements = some entries → EntriesShape sig entries
  | [], entries, _, accepted => by
      simp only [prepare, Option.some.injEq] at accepted
      subst entries
      intro entry member
      simp at member
  | (symbol, value) :: rest, entries, formed, accepted => by
      cases signature : sig symbol with
      | none => simp [prepare, signature] at accepted
      | some info =>
          simp only [prepare, signature] at accepted
          split at accepted
          · rename_i guard
            cases trailing : prepare sig rest with
            | none => simp [trailing] at accepted
            | some tail =>
                simp only [trailing, Option.map_some, Option.some.injEq] at accepted
                subst entries
                intro entry member
                rcases List.mem_cons.mp member with newest | earlier
                · subst entry
                  exact ⟨by simp [IsFvarOf, signature, kindOf, symArity, guard.1],
                    formed (symbol, value) (List.mem_cons_self)⟩
                · exact prepare_shape sig rest tail
                    (fun pair member => formed pair (List.mem_cons_of_mem _ member)) trailing entry earlier
          · simp at accepted

mutual
theorem go_shape (sig : Sig) (entries : List Entry) (valid : EntriesShape sig entries)
    (offset : Nat) (source result : Term) (formed : TermShape sig source)
    (accepted : go sig entries offset source = some result) : TermShape sig result := by
  cases source with
  | bvar index =>
      simp only [go, Option.some.injEq] at accepted
      subst result
      exact formed
  | lit bytes =>
      simp only [go, Option.some.injEq] at accepted
      subst result
      exact formed
  | app symbol children =>
      simp only [go] at accepted
      split at accepted
      · simp only [Option.some.injEq] at accepted
        subst result
        exact formed
      · obtain ⟨info, signature, arity, childrenFormed⟩ := TermShape.app_iff.mp formed
        cases traversed : args sig entries symbol offset 0 children with
        | none => simp [traversed] at accepted
        | some output =>
            have outputFormed := args_shape sig entries valid symbol offset 0
              children output childrenFormed traversed
            simp only [traversed] at accepted
            cases selected : lookup entries symbol with
            | none =>
                simp only [selected, Option.some.injEq] at accepted
                subst result
                exact .app signature (outputFormed.2.trans arity) outputFormed.1
            | some entry =>
                obtain ⟨member, same⟩ := lookup_member entries symbol entry selected
                have entryFormed := valid entry member
                have entryArity : info.arity = entry.arity := by
                  simpa only [symArity, same, signature] using entryFormed.1.2.2
                simp only [selected] at accepted
                cases shifted : shift sig offset entry.arity entry.value with
                | none => simp [shifted] at accepted
                | some value =>
                    simp only [shifted] at accepted
                    exact substBVars_termShape sig entry.arity output value result 0
                      (outputFormed.2.trans (arity.trans entryArity)) outputFormed.1
                      (shift_termShape sig offset entry.arity entry.value value entryFormed.2 shifted)
                      accepted
termination_by sizeOf source
decreasing_by
  subst_vars
  exact Term.args_sizeOf_lt_app _ _

theorem args_shape (sig : Sig) (entries : List Entry) (valid : EntriesShape sig entries)
    (symbol : SymId) (offset index : Nat) (source result : List Term)
    (formed : TermShapeList sig source)
    (accepted : args sig entries symbol offset index source = some result) :
    TermShapeList sig result ∧ result.length = source.length := by
  cases formed with
  | nil =>
      simp only [args, Option.some.injEq] at accepted
      subst result
      exact ⟨.nil, rfl⟩
  | @cons child rest childFormed restFormed =>
      simp only [args] at accepted
      split at accepted
      · cases headResult : go sig entries (offset + binderAt sig symbol index) child with
        | none => simp [headResult] at accepted
        | some newChild =>
            cases tailResult : args sig entries symbol offset (index + 1) rest with
            | none => simp [headResult, tailResult] at accepted
            | some newRest =>
                simp only [headResult, tailResult, Option.some.injEq] at accepted
                subst result
                obtain ⟨tailFormed, length⟩ := args_shape sig entries valid symbol offset (index + 1)
                  rest newRest restFormed tailResult
                exact ⟨.cons (go_shape sig entries valid _ child newChild childFormed headResult)
                  tailFormed, congrArg Nat.succ length⟩
      · simp at accepted
termination_by sizeOf source
decreasing_by
  all_goals subst_vars
  · exact term_tail_sizeOf_lt_cons _ _
  · exact term_head_sizeOf_lt_cons _ _
end

theorem statement_shape (sig : Sig) (replacements : List (SymId × Term))
    (source result : Term) (values : ValuesShape sig replacements)
    (formed : TermShape sig source)
    (accepted : SimultaneousInstantiation.statement sig replacements source = some result) :
    TermShape sig result := by
  cases prepared : prepare sig replacements with
  | none => simp [SimultaneousInstantiation.statement, prepared] at accepted
  | some entries =>
      have entriesFormed := prepare_shape sig replacements entries values prepared
      simp only [SimultaneousInstantiation.statement, prepared] at accepted
      by_cases empty : entries.isEmpty = true
      · simp only [empty, if_true] at accepted
        split at accepted
        · simp only [Option.some.injEq] at accepted
          subst result
          exact formed
        · simp at accepted
      · have emptyFalse : entries.isEmpty = false := Bool.eq_false_of_not_eq_true empty
        simp only [emptyFalse, Bool.false_eq_true, if_false] at accepted
        cases traversed : go sig entries 0 source with
        | none => simp [traversed] at accepted
        | some output =>
            simp only [traversed] at accepted
            split at accepted
            · simp only [Option.some.injEq] at accepted
              subst result
              exact go_shape sig entries entriesFormed 0 source output formed traversed
            · simp at accepted

#print axioms go_shape
#print axioms statement_shape

end Mettapedia.Languages.VibeITP.Presentation.SimultaneousFormation
