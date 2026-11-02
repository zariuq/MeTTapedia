import Mettapedia.OSLF.Syntax.BindingSignatureABT

/-!
# The common graft implements intrinsic contextual application

Lowering commutes with renaming and simultaneous object substitution.
Consequently the existing physical graft, with its executable scope and
arity checks, returns exactly the lowered intrinsic application. The proof
retains every binding prefix and permits arbitrary argument terms.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CommonABT

open Mettapedia.GSLT.LanguageDef
open SignatureIndexedABT

variable {S : Signature}

private theorem unit_count (count : Nat) :
    SortedSignatureIndexedABT.Term.binderCount () (List.replicate count ()) = count := by
  simp [SortedSignatureIndexedABT.Term.binderCount]

private theorem index_liftRen {Γ Δ : Ctx S} (rho : Ren S Γ Δ) (physical : Nat → Nat)
    (agrees : ∀ sort (position : Var Γ sort), index (rho sort position) = physical (index position)) :
    ∀ (binders : Ctx S) {sort : S.Srt} (position : Var (binders ++ Γ) sort),
      index (liftRen rho binders sort position) =
        SortedSignatureIndexedABT.Term.liftIndex binders.length physical (index position)
  | [], _, position => by simpa [liftRen, SortedSignatureIndexedABT.Term.liftIndex] using agrees _ position
  | _ :: _, _, .zero => by simp [liftRen, index, SortedSignatureIndexedABT.Term.liftIndex]
  | _ :: binders, sort, .succ position => by
      simp only [liftRen, index, List.length_cons, index_liftRen rho physical agrees binders position]
      by_cases below : index position < binders.length
      · have below' : index position + 1 < binders.length + 1 := by omega
        simp [SortedSignatureIndexedABT.Term.liftIndex, below, below']
      · have above' : ¬ index position + 1 < binders.length + 1 := by omega
        have remainder : index position + 1 - (binders.length + 1) = index position - binders.length := by omega
        simp only [SortedSignatureIndexedABT.Term.liftIndex, below, above', ↓reduceIte, remainder]
        omega

abbrev lowerSorted {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) :=
  SingleSort.encode (lower term)

abbrev lowerSortedArgs {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (arguments : Args S arities Γ) := SingleSort.encodeFields (lowerArgs arguments)

mutual

theorem lowerSorted_rename :
    ∀ {Γ Δ : Ctx S} {sort : S.Srt} (rho : Ren S Γ Δ) (physical : Nat → Nat),
      (∀ sort (position : Var Γ sort), index (rho sort position) = physical (index position)) →
      ∀ (term : Term S Γ sort), lowerSorted (rename rho term) =
        SortedSignatureIndexedABT.Term.parallelRename (fun _ => physical) (lowerSorted term)
  | _, _, _, rho, physical, agrees, .var position =>
      congrArg (SortedSignatureIndexedABT.Term.idx ()) (agrees _ position)
  | _, _, sort, rho, physical, agrees, .op operator arguments => by
      exact congrArg (SortedSignatureIndexedABT.Term.node (⟨sort, operator⟩ : Head S))
        (lowerSortedArgs_renameArgs rho physical agrees arguments)

theorem lowerSortedArgs_renameArgs :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S}
      (rho : Ren S Γ Δ) (physical : Nat → Nat),
      (∀ sort (position : Var Γ sort), index (rho sort position) = physical (index position)) →
      ∀ (arguments : Args S arities Γ), lowerSortedArgs (renameArgs rho arguments) =
        SortedSignatureIndexedABT.Term.Fields.parallelRename (fun _ => physical) (lowerSortedArgs arguments)
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, rho, physical, agrees, .cons (bs := binders) head tail => by
      change SortedSignatureIndexedABT.Fields.cons (List.replicate binders.length ())
          (lowerSorted (rename (liftRen rho binders) head)) (lowerSortedArgs (renameArgs rho tail)) =
        SortedSignatureIndexedABT.Fields.cons (List.replicate binders.length ())
          (SortedSignatureIndexedABT.Term.parallelRename
            (SortedSignatureIndexedABT.Term.liftRenaming (List.replicate binders.length ()) (fun _ => physical))
            (lowerSorted head))
          (SortedSignatureIndexedABT.Term.Fields.parallelRename (fun _ => physical) (lowerSortedArgs tail))
      have lifted : SortedSignatureIndexedABT.Term.liftRenaming
          (List.replicate binders.length ()) (fun _ => physical) =
          fun _ => SortedSignatureIndexedABT.Term.liftIndex binders.length physical := by
        funext sort index
        cases sort
        simp only [SortedSignatureIndexedABT.Term.liftRenaming, unit_count]
      rw [lifted]
      exact congrArg₂ (SortedSignatureIndexedABT.Fields.cons (List.replicate binders.length ()))
        (lowerSorted_rename (liftRen rho binders) _ (fun _ position => index_liftRen rho physical agrees binders position) head)
        (lowerSortedArgs_renameArgs rho physical agrees tail)

end

private theorem index_injPrefix : ∀ (binders : Ctx S) {Γ : Ctx S} {sort : S.Srt}
    (position : Var binders sort), index (injPrefix (Γ := Γ) binders position) = index position
  | [], _, _, position => nomatch position
  | _ :: _, _, _, .zero => rfl
  | _ :: binders, _, _, .succ position => congrArg Nat.succ (index_injPrefix binders position)

private theorem index_weakenVar : ∀ (binders : Ctx S) {Γ : Ctx S} {sort : S.Srt}
    (position : Var Γ sort), index (weakenVar binders position) = binders.length + index position
  | [], _, _, _ => by simp [weakenVar]
  | _ :: binders, _, _, position => by
      simp only [weakenVar, index, List.length_cons, index_weakenVar binders position]
      omega

private theorem prefix_or_tail : ∀ (binders : Ctx S) {Γ : Ctx S} {sort : S.Srt}
    (position : Var (binders ++ Γ) sort),
    (∃ boundPosition : Var binders sort, position = injPrefix binders boundPosition) ∨
      (∃ tail : Var Γ sort, position = weakenVar binders tail)
  | [], _, _, position => .inr ⟨position, rfl⟩
  | _ :: _, _, _, .zero => .inl ⟨.zero, rfl⟩
  | _ :: binders, _, _, .succ position => by
      rcases prefix_or_tail binders position with ⟨boundPosition, same⟩ | ⟨tail, same⟩
      · exact .inl ⟨.succ boundPosition, congrArg Var.succ same⟩
      · exact .inr ⟨tail, congrArg Var.succ same⟩

private theorem lowerSorted_liftSub {Γ Δ : Ctx S} (environment : Sub S Γ Δ)
    (physical : SortedSignatureIndexedABT.Term.Substitution Unit (Head S))
    (agrees : ∀ sort (position : Var Γ sort), lowerSorted (environment sort position) = physical () (index position))
    (binders : Ctx S) {sort : S.Srt} (position : Var (binders ++ Γ) sort) :
    lowerSorted (liftSub environment binders sort position) =
      SortedSignatureIndexedABT.Term.liftSubstitution (List.replicate binders.length ()) physical () (index position) := by
  rcases prefix_or_tail binders position with ⟨boundPosition, rfl⟩ | ⟨tail, rfl⟩
  · rw [liftSub_injPrefix]
    simp only [lowerSorted, lower, SingleSort.encode, index_injPrefix,
      SortedSignatureIndexedABT.Term.liftSubstitution, unit_count,
      if_pos (index_lt boundPosition)]
  · rw [liftSub_weakenVar, index_weakenVar]
    have above : ¬ binders.length + index tail < binders.length := by omega
    simp only [SortedSignatureIndexedABT.Term.liftSubstitution, unit_count, if_neg above,
      Nat.add_sub_cancel_left]
    rw [← agrees]
    have weakened := lowerSorted_rename (fun _ position => weakenVar binders position)
      (fun index => binders.length + index) (fun _ position => index_weakenVar binders position)
      (environment sort tail)
    have physicalWeaken : SortedSignatureIndexedABT.Term.weakenRenaming
        (List.replicate binders.length ()) = fun _ index => binders.length + index := by
      funext sort index
      cases sort
      simp only [SortedSignatureIndexedABT.Term.weakenRenaming, unit_count]
    rw [physicalWeaken]
    exact weakened

mutual

theorem lowerSorted_bind :
    ∀ {Γ Δ : Ctx S} {sort : S.Srt} (environment : Sub S Γ Δ)
      (physical : SortedSignatureIndexedABT.Term.Substitution Unit (Head S)),
      (∀ sort (position : Var Γ sort), lowerSorted (environment sort position) = physical () (index position)) →
      ∀ (term : Term S Γ sort), lowerSorted (bind environment term) =
        SortedSignatureIndexedABT.Term.parallelSubstitute physical (lowerSorted term)
  | _, _, _, environment, physical, agrees, .var position => agrees _ position
  | _, _, sort, environment, physical, agrees, .op operator arguments => by
      exact congrArg (SortedSignatureIndexedABT.Term.node (⟨sort, operator⟩ : Head S))
        (lowerSortedArgs_bindArgs environment physical agrees arguments)

theorem lowerSortedArgs_bindArgs :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S}
      (environment : Sub S Γ Δ) (physical : SortedSignatureIndexedABT.Term.Substitution Unit (Head S)),
      (∀ sort (position : Var Γ sort), lowerSorted (environment sort position) = physical () (index position)) →
      ∀ (arguments : Args S arities Γ), lowerSortedArgs (bindArgs environment arguments) =
        SortedSignatureIndexedABT.Term.Fields.parallelSubstitute physical (lowerSortedArgs arguments)
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, environment, physical, agrees, .cons (bs := binders) head tail => by
      exact congrArg₂ (SortedSignatureIndexedABT.Fields.cons (List.replicate binders.length ()))
        (lowerSorted_bind (liftSub environment binders) _
          (fun _ position => lowerSorted_liftSub environment physical agrees binders position) head)
        (lowerSortedArgs_bindArgs environment physical agrees tail)

end

/-- Equality with the common simultaneous substitution needs agreement only
at variables in the source context; outside indices cannot be observed. -/
theorem lower_bind {Γ Δ : Ctx S} {sort : S.Srt} (environment : Sub S Γ Δ)
    (physical : Nat → SignatureIndexedABT.Term (Head S))
    (agrees : ∀ sort (position : Var Γ sort), lower (environment sort position) = physical (index position))
    (term : Term S Γ sort) : lower (bind environment term) =
      SignatureIndexedABT.Term.substituteMany physical (lower term) := by
  apply SingleSort.encode_injective
  rw [SignatureIndexedABT.Term.encode_substituteMany]
  exact lowerSorted_bind environment (fun _ index => SingleSort.encode (physical index))
    (fun sort position => congrArg SingleSort.encode (agrees sort position)) term

def lowerSpine : {parameters : Ctx S} → {Γ : Ctx S} →
    Args S (parameters.map (fun sort => ([], sort))) Γ → List (SignatureIndexedABT.Term (Head S))
  | [], _, .nil => []
  | _ :: _, _, .cons head tail => lower head :: lowerSpine tail

theorem lowerSpine_length : ∀ {parameters : Ctx S} {Γ : Ctx S}
    (arguments : Args S (parameters.map (fun sort => ([], sort))) Γ),
    (lowerSpine arguments).length = parameters.length
  | [], _, .nil => rfl
  | _ :: _, _, .cons _ tail => congrArg Nat.succ (lowerSpine_length tail)

theorem lowerSpine_get : ∀ {parameters : Ctx S} {Γ : Ctx S}
    (arguments : Args S (parameters.map (fun sort => ([], sort))) Γ)
    {sort : S.Srt} (position : Var parameters sort),
    (lowerSpine arguments)[index position]? = some (lower (argsToSub arguments sort position))
  | [], _, _, _, position => nomatch position
  | _ :: _, _, .cons _ _, _, .zero => rfl
  | _ :: _, _, .cons _ tail, _, .succ position => lowerSpine_get tail position

/-- The existing executable graft performs precisely the intrinsic
capture-avoiding application, including non-variable and repeated arguments. -/
theorem graft_lower {parameters Γ : Ctx S} {sort : S.Srt}
    (body : Term S parameters sort)
    (arguments : Args S (parameters.map (fun sort => ([], sort))) Γ) :
    SignatureIndexedABT.ScopedApplication.graft parameters.length (lowerSpine arguments) (lower body) =
      some (lower (bind (argsToSub arguments) body)) := by
  unfold SignatureIndexedABT.ScopedApplication.graft
  rw [lowerSpine_length, lower_scoped]
  simp only [and_self, ↓reduceIte]
  apply congrArg some
  symm
  apply lower_bind
  intro sort position
  simp only [SignatureIndexedABT.ScopedApplication.argumentAt, lowerSpine_get, Option.getD_some]

end Mettapedia.OSLF.Binding.CommonABT
