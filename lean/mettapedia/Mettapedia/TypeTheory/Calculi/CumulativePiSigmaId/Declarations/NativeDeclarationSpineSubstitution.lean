import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeDeclarationSpineReplay

/-!
# Substitution of declaration-spine descriptions

Exposing a declared Pi spine commutes with simultaneous substitution. The
ordered argument/domain description does too. These statements transport
successful descriptions; arbitrary substitution can expose additional spines
where a free variable previously prevented declaration-rooted description.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.DeclarationSpineReplay

open Presentation NativeIndexedFamilies

theorem declaredType_subst {n : Nat} (subject : Tower.Tm n) :
    ∀ {m : Nat} (sigma : Sub Tower.Head n m) {type : Tower.Tm n},
      declaredType subject = some type →
      declaredType (subst sigma subject) = some (subst sigma type) := by
  induction subject with
  | const name =>
      intro m sigma type predicted
      cases known : IntrinsicRelator.rules.constantType name with
      | none => simp [declaredType, known] at predicted
      | some declared =>
          simp [declaredType, known] at predicted
          subst type
          simp [subst, declaredType, known]
  | app function argument ih _ =>
      intro m sigma type predicted
      cases functionType : declaredType function with
      | none => simp [declaredType, functionType] at predicted
      | some actual =>
          cases actual <;> simp [declaredType, functionType] at predicted
          subst type
          simp [subst, declaredType, ih sigma functionType, subst_inst0]
  | _ => intros; simp_all [declaredType]

theorem declaredArguments_subst {n : Nat} (subject : Tower.Tm n) :
    ∀ {m : Nat} (sigma : Sub Tower.Head n m) {entries : List (Tower.Tm n × Tower.Tm n)},
      declaredArguments subject = some entries →
      declaredArguments (subst sigma subject) =
        some (entries.map fun entry => (subst sigma entry.1, subst sigma entry.2)) := by
  induction subject with
  | const name =>
      intro m sigma entries described
      cases known : IntrinsicRelator.rules.constantType name with
      | none => simp [declaredArguments, known] at described
      | some declared =>
          simp [declaredArguments, known] at described
          subst entries
          simp [subst, declaredArguments, known]
  | app function argument ih _ =>
      intro m sigma entries described
      cases previous : declaredArguments function with
      | none => simp [declaredArguments, previous] at described
      | some prior =>
          cases functionType : declaredType function with
          | none => simp [declaredArguments, previous, functionType] at described
          | some actual =>
              cases actual <;> simp [declaredArguments, previous, functionType] at described
              subst entries
              simp [subst, declaredArguments, ih sigma previous,
                declaredType_subst function sigma functionType]
  | _ => intros; simp_all [declaredArguments]

theorem selectedArgument_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    {subject argument type : Tower.Tm n} (position : Nat)
    (selected : (declaredArguments subject).bind (fun entries => entries[position]?) =
      some (argument, type)) :
    (declaredArguments (subst sigma subject)).bind (fun entries => entries[position]?) =
      some (subst sigma argument, subst sigma type) := by
  cases described : declaredArguments subject with
  | none => simp [described] at selected
  | some entries =>
      simp only [described, Option.bind_some] at selected
      simp only [declaredArguments_subst subject sigma described, Option.bind_some,
        List.getElem?_map, selected, Option.map_some]

#print axioms declaredType_subst
#print axioms declaredArguments_subst
#print axioms selectedArgument_subst

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.DeclarationSpineReplay
