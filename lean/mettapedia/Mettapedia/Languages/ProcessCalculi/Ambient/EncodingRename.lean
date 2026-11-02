import Mettapedia.Languages.ProcessCalculi.Ambient.EncodingTyped

/-!
# The located form and renaming

Renaming the free variables of a process and then reading it located is reading it with the composite renaming
(`encode_rename`); renaming the free variables of a located form is reading the process with the renaming composed
after, at the renamed location (`rename_encode`). Lifting past one binder is a renaming, so both hold for lifting.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Encoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (rename size sizeList rename_bvar rename_fvar rename_apply
  rename_lambda rename_collection rename_comp rename_multiLambda rename_subst)

/-- Lifting two renamings past binders lifts their composite. -/
theorem liftIndex_comp (count : Nat) (first second : Nat → Nat) :
    liftIndex count first ∘ liftIndex count second = liftIndex count (first ∘ second) := by
  funext index
  simp only [Function.comp, liftIndex]
  by_cases below : index < count
  · simp [below]
  · have notBelow : ¬ second (index - count) + count < count := by omega
    simp [below, notBelow]

/-- A renaming lifted past one binder, after moving past it, moves past it after renaming. -/
theorem liftIndex_one_succ (relabel : Nat → Nat) : liftIndex 1 relabel ∘ Nat.succ = Nat.succ ∘ relabel := by
  funext index
  simp [Function.comp, liftIndex]

/-- A renaming lifted past one binder keeps the binder. -/
theorem liftIndex_one_zero (relabel : Nat → Nat) : liftIndex 1 relabel 0 = 0 := by simp [liftIndex]

theorem rename_shiftName (relabel : Nat → Nat) (here : Pattern) :
    rename (liftIndex 1 relabel) (shiftName here) = shiftName (rename relabel here) := by
  simp only [shiftName, rename_comp, liftIndex_one_succ]

/-- The members of a list of patterns weigh less than the list. -/
theorem size_lt_of_mem' {element : Pattern} {elements : List Pattern} (member : element ∈ elements) :
    size element < sizeList elements + 1 := by
  have := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.size_lt_of_mem member
  omega

/-! ## The located form of an application -/

theorem encode_single {relabel : Nat → Nat} {here : Pattern} (label : String) {argument : Pattern}
    (notLambda : ∀ binder body, argument ≠ .lambda binder body) :
    encode relabel here (.apply label [argument]) =
      if label = "ARep" then .apply "LRep" [encode relabel here argument]
      else if label = "AOutName" then .apply "LOutName" [here, rename relabel argument]
      else if label = "AOutCap" then .apply "LOutCap" [here, rename relabel argument]
      else rename relabel (.apply label [argument]) := by
  cases argument with
  | lambda binder body => exact absurd rfl (notLambda binder body)
  | _ => simp [encode]

theorem encode_single_lambda (relabel : Nat → Nat) (here : Pattern) (label : String) (binder : Option String)
    (body : Pattern) :
    encode relabel here (.apply label [.lambda binder body]) =
      if label = "ANu" then .apply "LNu" [.lambda binder (encode (liftIndex 1 relabel) (shiftName here) body)]
      else if label = "AInName" then
        .apply "LInName" [here, .lambda binder (encode (liftIndex 1 relabel) (shiftName here) body)]
      else if label = "AInCap" then
        .apply "LInCap" [here, .lambda binder (encode (liftIndex 1 relabel) (shiftName here) body)]
      else rename relabel (.apply label [.lambda binder body]) := by
  simp [encode]

theorem encode_pair (relabel : Nat → Nat) (here : Pattern) (label : String) (name process : Pattern) :
    encode relabel here (.apply label [name, process]) =
      if label = "AAmb" then
        .apply "LNu" [.lambda none (.collection .hashBag
          [.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name],
            encode (Nat.succ ∘ relabel) (.bvar 0) process] none)]
      else if label = "AIn" then .apply "LIn" [here, rename relabel name, encode relabel here process]
      else if label = "AOut" then .apply "LOut" [here, rename relabel name, encode relabel here process]
      else if label = "AOpen" then .apply "LOpen" [here, rename relabel name, encode relabel here process]
      else if label = "ACap" then .apply "LCap" [here, rename relabel name, encode relabel here process]
      else rename relabel (.apply label [name, process]) := by
  simp [encode]

theorem rename_not_lambda {relabel : Nat → Nat} {pattern : Pattern}
    (notLambda : ∀ binder body, pattern ≠ .lambda binder body) :
    ∀ binder body, rename relabel pattern ≠ .lambda binder body := by
  intro binder body same
  cases pattern with
  | lambda binder' body' => exact notLambda binder' body' rfl
  | bvar index => simp [rename_bvar] at same
  | fvar name => simp [rename_fvar] at same
  | apply label arguments => simp [rename_apply] at same
  | multiLambda arity binders body' => simp [rename_multiLambda] at same
  | subst body' replacement => simp [rename_subst] at same
  | collection kind elements rest => simp [rename_collection] at same

/-- **Renaming and then reading located is reading located with the composite renaming.** -/
theorem encode_rename : ∀ (fuel : Nat) {pattern : Pattern}, size pattern < fuel →
    ∀ (relabel second : Nat → Nat) (here : Pattern),
      encode relabel here (rename second pattern) = encode (relabel ∘ second) here pattern
  | 0, _, small, _, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, pattern, small, relabel, second, here => by
      cases pattern with
      | bvar index => simp [encode, rename_bvar]
      | fvar name => simp [encode, rename_fvar]
      | lambda binder body => simp [encode, rename_lambda, rename_comp, liftIndex_comp]
      | multiLambda arity binders body => simp [encode, rename_multiLambda, rename_comp, liftIndex_comp]
      | subst body replacement => simp [encode, rename_subst, rename_comp, liftIndex_comp]
      | collection kind elements rest =>
          cases kind with
          | hashBag =>
              rw [rename_collection]
              simp only [encode, encodeList_eq_map, List.map_map]
              congr 1
              refine List.map_congr_left fun element member => ?_
              simp only [Function.comp]
              exact encode_rename fuel (by have := size_lt_of_mem' member; simp only [size] at small; omega)
                relabel second here
          | _ => simp [encode, rename_collection, rename_comp]
      | apply label arguments =>
          match arguments, small with
          | [], _ => simp [encode, rename_apply]
          | [argument], small =>
              have argumentSmall : size argument < fuel := by simp only [size, sizeList] at small; omega
              by_cases isLambda : ∃ binder body, argument = .lambda binder body
              · obtain ⟨binder, body, rfl⟩ := isLambda
                have bodySmall : size body < fuel := by simp only [size] at argumentSmall; omega
                rw [rename_apply, List.map_singleton, rename_lambda, encode_single_lambda, encode_single_lambda]
                split_ifs
                · rw [encode_rename fuel bodySmall, liftIndex_comp]
                · rw [encode_rename fuel bodySmall, liftIndex_comp]
                · rw [encode_rename fuel bodySmall, liftIndex_comp]
                · simp only [rename_apply, rename_lambda, List.map_cons, List.map_nil, rename_comp, liftIndex_comp]
              · push Not at isLambda
                have renamedNotLambda := rename_not_lambda (relabel := second) isLambda
                rw [rename_apply, List.map_singleton, encode_single label renamedNotLambda,
                  encode_single label isLambda]
                split_ifs
                · rw [encode_rename fuel argumentSmall]
                · rw [rename_comp]
                · rw [rename_comp]
                · simp only [rename_apply, List.map_cons, List.map_nil, rename_comp]
          | [name, process], small =>
              have processSmall : size process < fuel := by simp only [size, sizeList] at small; omega
              rw [rename_apply, List.map_cons, List.map_singleton, encode_pair, encode_pair]
              split_ifs
              · rw [rename_comp, encode_rename fuel processSmall]
                rfl
              · rw [encode_rename fuel processSmall, rename_comp]
              · rw [encode_rename fuel processSmall, rename_comp]
              · rw [encode_rename fuel processSmall, rename_comp]
              · rw [encode_rename fuel processSmall, rename_comp]
              · simp only [rename_apply, List.map_cons, List.map_nil, rename_comp]
          | _ :: _ :: _ :: _, _ => simp [encode, rename_apply, rename_comp]

/-- **Renaming a located form is reading the process with the renaming composed after**, at the renamed location. -/
theorem rename_encode : ∀ (fuel : Nat) {pattern : Pattern}, size pattern < fuel →
    ∀ (first relabel : Nat → Nat) (here : Pattern),
      rename first (encode relabel here pattern) = encode (first ∘ relabel) (rename first here) pattern
  | 0, _, small, _, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, pattern, small, first, relabel, here => by
      cases pattern with
      | bvar index => simp [encode, rename_bvar]
      | fvar name => simp [encode, rename_fvar]
      | lambda binder body => simp [encode, rename_lambda, rename_comp, liftIndex_comp]
      | multiLambda arity binders body => simp [encode, rename_multiLambda, rename_comp, liftIndex_comp]
      | subst body replacement => simp [encode, rename_subst, rename_comp, liftIndex_comp]
      | collection kind elements rest =>
          cases kind with
          | hashBag =>
              simp only [encode, encodeList_eq_map, rename_collection, List.map_map]
              congr 1
              refine List.map_congr_left fun element member => ?_
              simp only [Function.comp]
              exact rename_encode fuel (by have := size_lt_of_mem' member; simp only [size] at small; omega)
                first relabel here
          | _ => simp [encode, rename_collection, rename_comp]
      | apply label arguments =>
          match arguments, small with
          | [], _ =>
              simp only [encode]
              split_ifs <;> simp [rename_apply]
          | [argument], small =>
              have argumentSmall : size argument < fuel := by simp only [size, sizeList] at small; omega
              by_cases isLambda : ∃ binder body, argument = .lambda binder body
              · obtain ⟨binder, body, rfl⟩ := isLambda
                have bodySmall : size body < fuel := by simp only [size] at argumentSmall; omega
                rw [encode_single_lambda, encode_single_lambda]
                split_ifs
                · rw [rename_apply, List.map_singleton, rename_lambda,
                    rename_encode fuel bodySmall, liftIndex_comp, rename_shiftName]
                · simp only [rename_apply, List.map_cons, List.map_nil, rename_lambda,
                    rename_encode fuel bodySmall, liftIndex_comp, rename_shiftName]
                · simp only [rename_apply, List.map_cons, List.map_nil, rename_lambda,
                    rename_encode fuel bodySmall, liftIndex_comp, rename_shiftName]
                · rw [rename_comp]
              · push Not at isLambda
                rw [encode_single label isLambda, encode_single label isLambda]
                split_ifs
                · rw [rename_apply, List.map_singleton, rename_encode fuel argumentSmall]
                · simp only [rename_apply, List.map_cons, List.map_nil, rename_comp]
                · simp only [rename_apply, List.map_cons, List.map_nil, rename_comp]
                · rw [rename_comp]
          | [name, process], small =>
              have processSmall : size process < fuel := by simp only [size, sizeList] at small; omega
              rw [encode_pair, encode_pair]
              split_ifs
              · simp only [rename_apply, rename_lambda, rename_collection, List.map_cons, List.map_nil, rename_comp,
                  rename_bvar, liftIndex_one_zero, rename_shiftName, rename_encode fuel processSmall]
                simp only [← Function.comp_assoc, liftIndex_one_succ]
              · simp only [rename_apply, List.map_cons, List.map_nil, rename_comp, rename_encode fuel processSmall]
              · simp only [rename_apply, List.map_cons, List.map_nil, rename_comp, rename_encode fuel processSmall]
              · simp only [rename_apply, List.map_cons, List.map_nil, rename_comp, rename_encode fuel processSmall]
              · simp only [rename_apply, List.map_cons, List.map_nil, rename_comp, rename_encode fuel processSmall]
              · rw [rename_comp]
          | _ :: _ :: _ :: _, _ => simp [encode, rename_apply, rename_comp]

end Mettapedia.Languages.ProcessCalculi.Ambient.Encoding
