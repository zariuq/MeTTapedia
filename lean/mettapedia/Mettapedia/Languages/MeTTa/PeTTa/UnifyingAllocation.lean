import Mettapedia.Languages.MeTTa.PeTTa.ScopedSource
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingSound

/-!
# Logical identities are preserved by the actual unifier

Resolution and binding may propagate existing variables but cannot allocate a
new identity. Preservation covers the executable term unifier, list-view
pattern unifier, quoted bindings and argument traversal. It is not a premise
imposed on a matching service. Instantiating support with allocated activation
scopes connects these laws to the scoped source boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst atomFreeVars applySubst)

def Supported (allowed : String → Prop) (term : Atom) : Prop :=
  ∀ key ∈ atomFreeVars term, allowed key

def SupportedBindings (allowed : String → Prop) (bindings : Subst) : Prop :=
  ∀ binding ∈ bindings, allowed binding.1 ∧ Supported allowed binding.2

theorem Supported.mono {first later : String → Prop} (included : ∀ key, first key → later key)
    {term : Atom} (supported : Supported first term) : Supported later term :=
  fun key member => included key (supported key member)

theorem SupportedBindings.mono {first later : String → Prop} (included : ∀ key, first key → later key)
    {bindings : Subst} (supported : SupportedBindings first bindings) : SupportedBindings later bindings := by
  intro binding member
  exact ⟨included binding.1 (supported binding member).1,(supported binding member).2.mono included⟩

@[simp] theorem supported_var (allowed : String → Prop) (key : String) :
    Supported allowed (.var key) ↔ allowed key := by simp [Supported,atomFreeVars]

@[simp] theorem supported_symbol (allowed : String → Prop) (name : String) :
    Supported allowed (.symbol name) := by simp [Supported,atomFreeVars]

@[simp] theorem supported_grounded (allowed : String → Prop)
    (value : Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue) :
    Supported allowed (.grounded value) := by simp [Supported,atomFreeVars]

theorem supported_expression (allowed : String → Prop) (items : List Atom) :
    Supported allowed (.expression items) ↔ ∀ item ∈ items, Supported allowed item := by
  simp only [Supported,mem_freeVars_expression]
  aesop

theorem supported_lookup {allowed : String → Prop} {bindings : Subst}
    (supported : SupportedBindings allowed bindings) {key : String} {value : Atom}
    (found : bindings.lookup key = some value) : Supported allowed value := by
  unfold Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup at found
  cases searched : bindings.find? (fun binding => binding.1 == key) with
  | none => simp [searched] at found
  | some binding =>
      simp only [searched,Option.map_some,Option.some.injEq] at found
      rw [← found]
      exact (supported binding (List.mem_of_find?_eq_some searched)).2

theorem supported_resolve {allowed : String → Prop} {bindings : Subst}
    (bindingsSupported : SupportedBindings allowed bindings) :
    ∀ term : Atom, Supported allowed term → Supported allowed (resolve bindings term)
  | .var key, supported => by
      cases found : bindings.lookup key with
      | none => simpa only [resolve,applySubst,found,Option.getD_none] using supported
      | some value =>
          simpa only [resolve,applySubst,found,Option.getD_some] using
            supported_lookup bindingsSupported found
  | .symbol _, _ | .grounded _, _ => by simp [Supported,resolve,applySubst,atomFreeVars]
  | .expression items, supported => by
      apply (supported_expression allowed _).mpr
      exact list items ((supported_expression allowed items).mp supported)
where
  list : ∀ items : List Atom, (∀ item ∈ items, Supported allowed item) →
      ∀ item ∈ applySubst.applySubstList bindings items, Supported allowed item
    | [], _, _, present => by cases present
    | first :: rest, supported, item, present => by
        simp only [applySubst.applySubstList,List.mem_cons] at present
        rcases present with rfl | present
        · exact supported_resolve bindingsSupported first (supported first (by simp))
        · exact list rest (fun term member => supported term (List.mem_cons_of_mem _ member)) item present

theorem supported_bindVar {allowed : String → Prop} {bindings : Subst} {key : String} {value : Atom}
    (bindingsSupported : SupportedBindings allowed bindings) (keySupported : allowed key)
    (valueSupported : Supported allowed value) : SupportedBindings allowed (bindVar bindings key value) := by
  intro binding present
  simp only [bindVar,List.mem_cons,List.mem_map] at present
  rcases present with rfl | ⟨old,member,rfl⟩
  · exact ⟨keySupported,valueSupported⟩
  · refine ⟨(bindingsSupported old member).1,?_⟩
    apply supported_resolve (bindings := [(key,value)]) _ old.2 (bindingsSupported old member).2
    intro entry inside
    simp only [List.mem_singleton] at inside
    subst entry
    exact ⟨keySupported,valueSupported⟩

theorem unifyLists_supported (allowed : String → Prop) (unifier : Subst → Atom → Atom → Unified)
    (preserves : ∀ bindings bound left right, SupportedBindings allowed bindings →
      Supported allowed left → Supported allowed right → unifier bindings left right = .ok bound →
      SupportedBindings allowed bound) :
    ∀ (left right : List Atom) (bindings bound : Subst), SupportedBindings allowed bindings →
      (∀ term ∈ left, Supported allowed term) → (∀ term ∈ right, Supported allowed term) →
      unifyLists unifier bindings left right = .ok bound → SupportedBindings allowed bound := by
  intro left
  induction left with
  | nil =>
      intro right bindings bound good _ _ unified
      cases right with
      | nil => cases unified; exact good
      | cons => cases unified
  | cons first rest ih =>
      intro right bindings bound good leftGood rightGood unified
      cases right with
      | nil => cases unified
      | cons other others =>
          simp only [unifyLists] at unified
          cases computed : unifier bindings first other with
          | clash | exhausted => simp [computed] at unified
          | ok middle =>
              rw [computed,Unified.ok_andThen] at unified
              exact ih others middle bound
                (preserves bindings middle first other good (leftGood first (by simp))
                  (rightGood other (by simp)) computed)
                (fun term member => leftGood term (List.mem_cons_of_mem _ member))
                (fun term member => rightGood term (List.mem_cons_of_mem _ member)) unified

theorem unifyTerms_supported (allowed : String → Prop) (fuel : Nat) :
    ∀ (bindings bound : Subst) (left right : Atom), SupportedBindings allowed bindings →
      Supported allowed left → Supported allowed right → unifyTerms fuel bindings left right = .ok bound →
      SupportedBindings allowed bound := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ unified; cases unified
  | succ fuel ih =>
      intro bindings bound left right good leftGood rightGood unified
      have leftResolved := supported_resolve good left leftGood
      have rightResolved := supported_resolve good right rightGood
      unfold unifyTerms at unified
      generalize leftEq : resolve bindings left = resolvedLeft at unified leftResolved
      generalize rightEq : resolve bindings right = resolvedRight at unified rightResolved
      cases resolvedLeft <;> cases resolvedRight
      all_goals simp only at unified
      all_goals try solve | split at unified <;> cases unified <;> exact good
      all_goals try solve | cases unified
      all_goals try solve |
        simp only [supported_var] at leftResolved rightResolved
        split at unified
        · cases unified; exact good
        · cases unified
          exact supported_bindVar good leftResolved ((supported_var _ _).mpr rightResolved)
      all_goals try solve |
        split at unified
        · cases unified
        · cases unified
          exact supported_bindVar good ((supported_var _ _).mp leftResolved) rightResolved
      all_goals try solve |
        split at unified
        · cases unified
        · cases unified
          exact supported_bindVar good ((supported_var _ _).mp rightResolved) leftResolved
      exact unifyLists_supported allowed (unifyTerms fuel) ih _ _ bindings bound good
        ((supported_expression _ _).mp leftResolved) ((supported_expression _ _).mp rightResolved) unified

/-- Successful unification of admitted terms cannot introduce an identity
from a scope at or above the caller's next allocation supply. -/
theorem unifyTerms_allocated (next fuel : Nat) (bindings bound : Subst) (left right : Atom)
    (bindingsAllocated : SupportedBindings (Mettapedia.ScopedString.Before next) bindings)
    (leftAllocated : ScopedSource.Allocated next left) (rightAllocated : ScopedSource.Allocated next right)
    (unified : unifyTerms fuel bindings left right = .ok bound) :
    SupportedBindings (Mettapedia.ScopedString.Before next) bound :=
  unifyTerms_supported _ fuel bindings bound left right bindingsAllocated leftAllocated rightAllocated unified

theorem supported_expression_cons (allowed : String → Prop) (first : Atom) (rest : List Atom) :
    Supported allowed (.expression (first :: rest)) ↔
      Supported allowed first ∧ Supported allowed (.expression rest) := by
  simp only [supported_expression,List.mem_cons,forall_eq_or_imp]

theorem unifyPattern_supported (allowed : String → Prop) (fuel : Nat) :
    ∀ (bindings bound : Subst) (pattern value : Atom), SupportedBindings allowed bindings →
      Supported allowed pattern → Supported allowed value →
      unifyPattern fuel bindings pattern value = .ok bound → SupportedBindings allowed bound := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ unified; cases unified
  | succ fuel ih =>
      intro bindings bound pattern value good patternGood valueGood unified
      have resolvedGood := supported_resolve good value valueGood
      simp only [unifyPattern] at unified
      split at unified
      · rename_i _ _ first rest head tail resolved
        have pieces : Supported allowed first ∧ Supported allowed rest := by
          simpa [supported_expression] using patternGood
        rw [resolved] at resolvedGood
        have values := (supported_expression_cons allowed head tail).mp resolvedGood
        cases firstRun : unifyPattern fuel bindings first head with
        | clash | exhausted => simp [firstRun] at unified
        | ok middle =>
            rw [firstRun,Unified.ok_andThen] at unified
            exact ih middle bound rest (.expression tail)
              (ih bindings middle first head good pieces.1 values.1 firstRun)
              pieces.2 values.2 unified
      · exact unifyTerms_supported allowed fuel bindings bound _ value good patternGood valueGood unified
      · cases unified
      · rename_i _ _ _ _ resolved
        rw [resolved] at resolvedGood
        exact unifyLists_supported allowed (unifyPattern fuel) ih _ _ bindings bound good
          ((supported_expression _ _).mp patternGood) ((supported_expression _ _).mp resolvedGood) unified
      · exact unifyTerms_supported allowed fuel bindings bound _ value good patternGood valueGood unified
      · cases unified
      · exact unifyTerms_supported allowed fuel bindings bound _ value good patternGood valueGood unified

theorem unifyBinding_supported (allowed : String → Prop) (bindings bound : Subst) (pattern value : Atom)
    (good : SupportedBindings allowed bindings) (patternGood : Supported allowed pattern)
    (valueGood : Supported allowed value) (unified : unifyBinding bindings pattern value = .ok bound) :
    SupportedBindings allowed bound := by
  unfold unifyBinding at unified
  split at unified
  · rename_i written literal
    have literalGood : Supported allowed literal := by simpa [supported_expression] using patternGood
    exact unifyTerms_supported allowed _ bindings bound _ value good literalGood valueGood unified
  · exact unifyPattern_supported allowed _ bindings bound pattern value good patternGood valueGood unified

theorem unifyArguments_supported (allowed : String → Prop) (bindings bound : Subst)
    (patterns values : List Atom) (good : SupportedBindings allowed bindings)
    (patternsGood : ∀ term ∈ patterns, Supported allowed term)
    (valuesGood : ∀ term ∈ values, Supported allowed term)
    (unified : unifyArguments bindings patterns values = .ok bound) : SupportedBindings allowed bound :=
  unifyLists_supported allowed (unifyPattern _) (unifyPattern_supported allowed _) patterns values bindings bound
    good patternsGood valuesGood unified

theorem allocated_bindings_have_no_future_key (next : Nat) (bindings : Subst)
    (allocated : SupportedBindings (Mettapedia.ScopedString.Before next) bindings)
    (name : String) : bindings.lookup (freshName next name) = none := by
  unfold Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup
  cases found : bindings.find? (fun binding => binding.1 == freshName next name) with
  | none => rfl
  | some binding =>
      have member := List.mem_of_find?_eq_some found
      have selected := List.find?_some found
      have same : binding.1 = freshName next name := by simpa using selected
      exact False.elim (Mettapedia.ScopedString.new_identity_is_fresh (allocated binding member).1 name same.symm)

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
