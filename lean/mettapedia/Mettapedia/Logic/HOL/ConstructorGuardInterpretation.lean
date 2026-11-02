import Mettapedia.Logic.HOL.FiniteConstructorInterpretation
import Mettapedia.Logic.HOL.ConstructorDataPredicates

/-!
# Constructor-image guards under closed-term interpretation

The translation preserves the constructor ordinal, original ordered fields,
field conditions and payload equation. The result is a syntactic equality of
generated guards; no semantic truth or whole-guard agreement is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding
universe u v u' v'
variable {Base : Type u} {Const : Ty Base → Type v}
  {Target : Type u'} {Symbols : Ty Target → Type v'}
  (interpretation : TermInterpretation Base Const Target Symbols)
  {Γ Δ : Ctx Base}

theorem abstractArguments_interpret_as (fields : List (Ty Base))
    (targetFields : List (Ty Target))
    (same : fields.map (Ty.substitute interpretation.types) = targetFields)
    (body : ArgumentBody Const Γ fields)
    (targetBody : ArgumentBody Symbols (Γ.map (Ty.substitute interpretation.types)) targetFields)
    (compatibleBody : ∀ {Ξ : Ctx Base} (rho : Subst Const Γ Ξ)
      (mapped : Subst Symbols (Γ.map (Ty.substitute interpretation.types))
        (Ξ.map (Ty.substitute interpretation.types))),
      (∀ {type} (index : Var Γ type), interpretation.term (rho index) =
        mapped (index.mapTypes interpretation.types)) →
      ∀ arguments, interpretation.term (body rho arguments) =
        targetBody mapped (same ▸ interpretArguments interpretation fields arguments)) :
    HEq (interpretation.term (abstractArguments fields body))
      (abstractArguments targetFields targetBody) := by
  cases same
  exact abstractArguments_interpret interpretation fields body targetBody compatibleBody

theorem restrictedGuard_interpret (signature : List (List (Ty Base)))
    (occurrence : Fin signature.length)
    (condition : Term Const Γ (handlerType (signature.get occurrence)))
    (payload : Term Const Γ (payloadType signature))
    (targetCondition : Term Symbols (Γ.map (Ty.substitute interpretation.types))
      (handlerType ((signature.map (List.map (Ty.substitute interpretation.types))).get
        (mapOccurrence interpretation signature occurrence))))
    (targetPayload : Term Symbols (Γ.map (Ty.substitute interpretation.types))
      (payloadType (signature.map (List.map (Ty.substitute interpretation.types)))))
    (conditionSame : HEq (interpretation.term condition) targetCondition)
    (payloadSame : HEq (interpretation.term payload) targetPayload) :
    interpretation.term (restrictedGuard signature occurrence condition payload) =
      restrictedGuard (signature.map (List.map (Ty.substitute interpretation.types)))
        (mapOccurrence interpretation signature occurrence) targetCondition targetPayload := by
  have predicateSame := abstractArguments_interpret_as interpretation (signature.get occurrence) _
    (selectedFields_interpret interpretation signature occurrence)
    (restrictedBody signature occurrence condition payload)
    (restrictedBody (signature.map (List.map (Ty.substitute interpretation.types)))
      (mapOccurrence interpretation signature occurrence) targetCondition targetPayload) (by
      intro Ξ rho mapped compatible arguments
      simp only [restrictedBody, TermInterpretation.term_and, TermInterpretation.term_eq]
      apply congrArg₂ Term.and
      · rw [applyArguments_interpret]
        apply applyArguments_heq (selectedFields_interpret interpretation signature occurrence)
        apply (interpretHandler_heq interpretation _ _).trans
        exact TermInterpretation.term_subst_heq interpretation rho mapped compatible
          ((handlerType_interpret interpretation _).trans
            (congrArg handlerType (selectedFields_interpret interpretation signature occurrence)))
          _ _ conditionSame
      · congr 1
        · exact payloadType_interpret interpretation signature
        · exact TermInterpretation.term_subst_heq interpretation rho mapped compatible
            (payloadType_interpret interpretation signature) _ _ payloadSame
        · exact encode_interpret interpretation signature occurrence arguments)
  rw [restrictedGuard, existsArguments_interpret]
  exact existsArguments_heq (selectedFields_interpret interpretation signature occurrence) _ _
    ((interpretHandler_heq interpretation _ _).trans predicateSame)

theorem any_interpret (formulas : List (Formula Const Γ)) :
    interpretation.term (any formulas) = any (formulas.map interpretation.term) := by
  induction formulas with
  | nil => rfl
  | cons first rest previous =>
      simp only [any, List.foldr_cons, List.map_cons, TermInterpretation.term_or]
      exact congrArg (Term.or (interpretation.term first)) previous

theorem guard_interpret (signature : List (List (Ty Base)))
    (conditions : ConstructorDataPredicates.Conditions Const Γ signature)
    (payload : Term Const Γ (payloadType signature))
    (targetConditions : ConstructorDataPredicates.Conditions Symbols
      (Γ.map (Ty.substitute interpretation.types))
      (signature.map (List.map (Ty.substitute interpretation.types))))
    (targetPayload : Term Symbols (Γ.map (Ty.substitute interpretation.types))
      (payloadType (signature.map (List.map (Ty.substitute interpretation.types)))))
    (conditionsSame : ∀ occurrence, HEq (interpretation.term (conditions occurrence))
      (targetConditions (mapOccurrence interpretation signature occurrence)))
    (payloadSame : HEq (interpretation.term payload) targetPayload) :
    interpretation.term (ConstructorDataPredicates.guard signature conditions payload) =
      ConstructorDataPredicates.guard
        (signature.map (List.map (Ty.substitute interpretation.types))) targetConditions targetPayload := by
  rw [ConstructorDataPredicates.guard, any_interpret, ConstructorDataPredicates.guard]
  apply congrArg any
  apply List.ext_getElem
  · simp only [List.length_map, List.length_ofFn]
  · intro position firstBound secondBound
    simp only [List.getElem_map, List.getElem_ofFn]
    exact restrictedGuard_interpret interpretation signature ⟨position, by
      simpa only [List.length_map, List.length_ofFn] using firstBound⟩
      _ _ _ _ (conditionsSame _) payloadSame

#print axioms restrictedGuard_interpret
#print axioms guard_interpret
end Mettapedia.Logic.HOL.FiniteConstructorEncoding
