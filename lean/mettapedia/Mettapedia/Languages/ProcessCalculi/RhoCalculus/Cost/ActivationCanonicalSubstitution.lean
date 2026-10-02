import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationCanonicalScope

/-!
# Canonical communication under the full cost structural observation

Communication uses the existing raw substitution and normalizer. On checked
whole-object scope, normalizing code and a closed payload before substitution
preserves the independent observation of all cost constructors. Parallel
occurrences form bags; seals, authority strings and ordered purse cells remain
fields of the observation. Literal raw equality is a separate stronger claim.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

theorem RawCostProc.structuralDenote_substitute_fromComponents
    (replacement : RawCostTerm) (depth : Nat) : ∀ items : List RawCostProc,
    (RawCostProc.substitute replacement depth (RawCostProc.fromComponents items)).structuralDenote =
      (items.map fun process => (RawCostProc.substitute replacement depth process).structuralDenote).sum
  | [] => rfl
  | [process] => by simp [RawCostProc.fromComponents]
  | head :: next :: rest => by
      simp [RawCostProc.structuralDenote,
        RawCostProc.structuralDenote_substitute_fromComponents replacement depth (next :: rest)]

theorem RawCostProc.structuralDenote_substitute_components
    (replacement : RawCostTerm) (depth : Nat) : ∀ process : RawCostProc,
    (process.components.map fun component =>
      (RawCostProc.substitute replacement depth component).structuralDenote).sum =
        (RawCostProc.substitute replacement depth process).structuralDenote
  | .nil => rfl
  | .par left right => by
      simp [RawCostProc.components, RawCostProc.structuralDenote,
        RawCostProc.structuralDenote_substitute_components replacement depth left,
        RawCostProc.structuralDenote_substitute_components replacement depth right]
  | .send name term => by simp [RawCostProc.components]
  | .recv name term => by simp [RawCostProc.components]

theorem RawCostTerm.structuralDenote_substitute_fromComponents
    (replacement : RawCostTerm) (depth : Nat) : ∀ items : List RawCostTerm,
    (RawCostTerm.substitute replacement depth (RawCostTerm.fromComponents items)).structuralDenote =
      ⟨(items.map fun term => (RawCostTerm.substitute replacement depth term).structuralDenote.atoms).sum,
       (items.map fun term => (RawCostTerm.substitute replacement depth term).structuralDenote.topDrops).sum⟩
  | [] => rfl
  | [term] => by simp [RawCostTerm.fromComponents]
  | head :: next :: rest => by
      rw [RawCostTerm.fromComponents, RawCostTerm.substitute, RawCostTerm.structuralDenote,
        RawCostTerm.structuralDenote_substitute_fromComponents replacement depth (next :: rest)]
      rfl

theorem RawCostTerm.structuralAtoms_substitute_components
    (replacement : RawCostTerm) (depth : Nat) : ∀ term : RawCostTerm,
    (term.components.map fun component =>
      (RawCostTerm.substitute replacement depth component).structuralDenote.atoms).sum =
        (RawCostTerm.substitute replacement depth term).structuralDenote.atoms
  | .nil => rfl
  | .par left right => by
      simp [RawCostTerm.components, RawCostTerm.structuralDenote,
        RawTermStructuralDenotation.combine,
        RawCostTerm.structuralAtoms_substitute_components replacement depth left,
        RawCostTerm.structuralAtoms_substitute_components replacement depth right]
  | .signed process signature => by simp [RawCostTerm.components]
  | .drop name => by simp [RawCostTerm.components]
  | .purse name stack => by simp [RawCostTerm.components]

theorem RawCostTerm.structuralDrops_substitute_components
    (replacement : RawCostTerm) (depth : Nat) : ∀ term : RawCostTerm,
    (term.components.map fun component =>
      (RawCostTerm.substitute replacement depth component).structuralDenote.topDrops).sum =
        (RawCostTerm.substitute replacement depth term).structuralDenote.topDrops
  | .nil => rfl
  | .par left right => by
      simp [RawCostTerm.components, RawCostTerm.structuralDenote,
        RawTermStructuralDenotation.combine,
        RawCostTerm.structuralDrops_substitute_components replacement depth left,
        RawCostTerm.structuralDrops_substitute_components replacement depth right]
  | .signed process signature => by simp [RawCostTerm.components]
  | .drop name => by simp [RawCostTerm.components]
  | .purse name stack => by simp [RawCostTerm.components]

mutual
  theorem RawCostName.structuralDenote_substitute_normalize
      (scope depth : Nat) (replacement : RawCostTerm)
      (replacementClosed : replacement.runtimeBinderSafeAt 0 = true) :
      ∀ name : RawCostName, name.runtimeBinderSafeAt scope = true →
      (name.normalize.substitute replacement.normalize depth).structuralDenote =
        (name.substitute replacement depth).structuralDenote
    | .bvar index, _ => by
      simp only [RawCostName.substitute]
      by_cases matched : index = depth
      · rw [if_pos matched, if_pos matched,
          RawCostTerm.runtimeBinderSafeAt_liftAbove_eq
            (RawCostTerm.runtimeBinderSafeAt_normalize 0 replacement replacementClosed) (le_refl 0),
          RawCostTerm.runtimeBinderSafeAt_liftAbove_eq replacementClosed (le_refl 0)]
        simp only [RawCostName.structuralDenote, RawCostTerm.structuralDenote_normalize]
      · rw [if_neg matched, if_neg matched]
    | .signature signature, _ => by
      simp [RawCostName.structuralDenote]
    | .quote term, safe => by
      have closed : (RawCostName.quote term).runtimeBinderSafeAt 0 = true := safe
      rw [RawCostName.substitute_closed_identity
        (RawCostName.runtimeBinderSafeAt_normalize 0 _ closed)]
      exact RawCostName.structuralDenote_normalize (.quote term)

  theorem RawCostProc.structuralDenote_substitute_normalize
      (scope depth : Nat) (replacement : RawCostTerm)
      (replacementClosed : replacement.runtimeBinderSafeAt 0 = true) :
      ∀ process : RawCostProc, process.runtimeBinderSafeAt scope = true →
      (process.normalize.substitute replacement.normalize depth).structuralDenote =
        (process.substitute replacement depth).structuralDenote
    | .nil, _ => rfl
    | .par left right, safe => by
      simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true] at safe
      simp only [RawCostProc.normalize]
      rw [RawCostProc.structuralDenote_substitute_fromComponents, List.sum_map_stableKeySort]
      simp only [List.map_append, List.sum_append,
        RawCostProc.structuralDenote_substitute_components,
        RawCostProc.structuralDenote_substitute_normalize scope depth replacement replacementClosed left safe.1,
        RawCostProc.structuralDenote_substitute_normalize scope depth replacement replacementClosed right safe.2,
        RawCostProc.structuralDenote]
    | .send name term, safe => by
      simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true] at safe
      simp only [RawCostProc.structuralDenote,
        RawCostName.structuralDenote_substitute_normalize scope depth replacement replacementClosed name safe.1,
        RawCostTerm.structuralDenote_substitute_normalize scope depth replacement replacementClosed term safe.2]
    | .recv name term, safe => by
      simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true] at safe
      simp only [RawCostProc.structuralDenote,
        RawCostName.structuralDenote_substitute_normalize scope depth replacement replacementClosed name safe.1,
        RawCostTerm.structuralDenote_substitute_normalize (scope + 1) (depth + 1)
          replacement replacementClosed term safe.2]

  theorem RawCostTerm.structuralDenote_substitute_normalize
      (scope depth : Nat) (replacement : RawCostTerm)
      (replacementClosed : replacement.runtimeBinderSafeAt 0 = true) :
      ∀ term : RawCostTerm, term.runtimeBinderSafeAt scope = true →
      (RawCostTerm.substitute replacement.normalize depth term.normalize).structuralDenote =
        (RawCostTerm.substitute replacement depth term).structuralDenote
    | .nil, _ => rfl
    | .signed process signature, safe => by
      simp only [RawCostTerm.structuralDenote,
        RawCostProc.structuralDenote_substitute_normalize scope depth replacement replacementClosed process safe,
        RawCostSig.normalize_toMultiset]
    | .par left right, safe => by
      simp only [RawCostTerm.runtimeBinderSafeAt, Bool.and_eq_true] at safe
      simp only [RawCostTerm.normalize]
      rw [RawCostTerm.structuralDenote_substitute_fromComponents]
      apply RawTermStructuralDenotation.ext
      · simp only [List.sum_map_stableKeySort, List.map_append, List.sum_append,
          RawCostTerm.structuralAtoms_substitute_components,
          RawCostTerm.structuralDenote_substitute_normalize scope depth replacement replacementClosed left safe.1,
          RawCostTerm.structuralDenote_substitute_normalize scope depth replacement replacementClosed right safe.2,
          RawCostTerm.structuralDenote, RawTermStructuralDenotation.combine]
      · simp only [List.sum_map_stableKeySort, List.map_append, List.sum_append,
          RawCostTerm.structuralDrops_substitute_components,
          RawCostTerm.structuralDenote_substitute_normalize scope depth replacement replacementClosed left safe.1,
          RawCostTerm.structuralDenote_substitute_normalize scope depth replacement replacementClosed right safe.2,
          RawCostTerm.structuralDenote, RawTermStructuralDenotation.combine]
    | .drop (.bvar index), _ => by
      simp only [RawCostTerm.substitute]
      by_cases matched : index = depth
      · rw [if_pos matched, if_pos matched,
          RawCostTerm.runtimeBinderSafeAt_liftAbove_eq
            (RawCostTerm.runtimeBinderSafeAt_normalize 0 replacement replacementClosed) (le_refl 0),
          RawCostTerm.runtimeBinderSafeAt_liftAbove_eq replacementClosed (le_refl 0),
          RawCostTerm.structuralDenote_normalize]
      · rw [if_neg matched, if_neg matched]
    | .drop (.quote term), safe => by
      have closed : (RawCostName.quote term).runtimeBinderSafeAt 0 = true := safe
      simp only [RawCostTerm.normalize]
      rw [RawCostTerm.substitute_drop_closed_identity
        (RawCostName.runtimeBinderSafeAt_normalize 0 _ closed)]
      simp only [RawCostTerm.structuralDenote]
      rw [RawCostName.structuralDenote_normalize (.quote term)]
    | .drop (.signature signature), _ => by
      simp [RawCostTerm.structuralDenote, RawCostName.structuralDenote]
    | .purse name stack, safe => by
      simp only [RawCostTerm.structuralDenote,
        RawCostName.structuralDenote_substitute_normalize scope depth replacement replacementClosed name safe,
        RawCostStack.structuralFrames_map_normalize]
end

theorem RawCostTerm.commSubst_normalize_structural
    {body payload : RawCostTerm} (bodyScope : Nat)
    (bodySafe : body.runtimeBinderSafeAt bodyScope = true)
    (payloadClosed : payload.runtimeBinderSafeAt 0 = true) :
    (body.normalize.commSubst payload.normalize).normalize.StructurallyEquivalent
      (body.commSubst payload).normalize := by
  unfold RawCostTerm.StructurallyEquivalent
  rw [RawCostTerm.structuralDenote_normalize, RawCostTerm.structuralDenote_normalize]
  exact RawCostTerm.structuralDenote_substitute_normalize bodyScope 0 payload payloadClosed body bodySafe

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
