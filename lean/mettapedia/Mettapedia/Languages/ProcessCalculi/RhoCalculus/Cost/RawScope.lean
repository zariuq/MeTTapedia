import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Normalization
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RawWrapping
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ScopedSyntax

/-!
# Binder-scope preservation for the executable cost syntax

The raw runtime checker mirrors the typed binder-safety judgment exactly.
This module proves that component flattening, stable ordering, structural
normalization, and residual assembly preserve that checked fragment.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-- A raw name safe at a smaller depth remains safe when more binders are
available. -/
theorem RawCostName.binderSafeAt_mono {small large : Nat}
    {name : RawCostName} (safe : name.binderSafeAt small = true)
    (scope : small ≤ large) : name.binderSafeAt large = true := by
  apply (RawCostName.binderSafeAt_iff_decode large name).mpr
  exact ((RawCostName.binderSafeAt_iff_decode small name).mp safe).mono scope

theorem RawCostProc.components_forall_binderSafeAt (depth : Nat) :
    ∀ process : RawCostProc, process.binderSafeAt depth = true →
      process.components.Forall
        (fun component => component.binderSafeAt depth = true)
  | .nil, _ => by simp
  | .par left right, safe => by
      simp only [RawCostProc.binderSafeAt, Bool.and_eq_true] at safe
      simp only [RawCostProc.components, List.forall_append]
      exact ⟨RawCostProc.components_forall_binderSafeAt depth left safe.1,
        RawCostProc.components_forall_binderSafeAt depth right safe.2⟩
  | .send channel payload, safe => by
      simpa [RawCostProc.components] using safe
  | .recv channel body, safe => by
      simpa [RawCostProc.components] using safe

theorem RawCostTerm.components_forall_binderSafeAt (depth : Nat) :
    ∀ term : RawCostTerm, term.binderSafeAt depth = true →
      term.components.Forall
        (fun component => component.binderSafeAt depth = true)
  | .nil, _ => by simp
  | .par left right, safe => by
      simp only [RawCostTerm.binderSafeAt, Bool.and_eq_true] at safe
      simp only [RawCostTerm.components, List.forall_append]
      exact ⟨RawCostTerm.components_forall_binderSafeAt depth left safe.1,
        RawCostTerm.components_forall_binderSafeAt depth right safe.2⟩
  | .signed process signature, safe => by
      simpa [RawCostTerm.components] using safe
  | .drop name, safe => by
      simpa [RawCostTerm.components] using safe
  | .purse surface stack, safe => by
      simp

/-- Binder safety of every flattened component reconstructs binder safety of
the original raw term. -/
theorem RawCostTerm.binderSafeAt_of_components (depth : Nat) :
    ∀ term : RawCostTerm,
      term.components.Forall
          (fun component => component.binderSafeAt depth = true) →
        term.binderSafeAt depth = true
  | .nil, _ => rfl
  | .par left right, componentsSafe => by
      simp only [RawCostTerm.components, List.forall_append] at componentsSafe
      simp only [RawCostTerm.binderSafeAt, Bool.and_eq_true]
      exact ⟨RawCostTerm.binderSafeAt_of_components depth left componentsSafe.1,
        RawCostTerm.binderSafeAt_of_components depth right componentsSafe.2⟩
  | .signed process signature, componentsSafe => by
      simpa [RawCostTerm.components] using componentsSafe
  | .drop name, componentsSafe => by
      simpa [RawCostTerm.components] using componentsSafe
  | .purse surface stack, _ => rfl

theorem RawCostProc.fromComponents_binderSafeAt (depth : Nat) :
    ∀ items : List RawCostProc,
      items.Forall (fun component => component.binderSafeAt depth = true) →
      (RawCostProc.fromComponents items).binderSafeAt depth = true
  | [], _ => rfl
  | head :: [], safe => by
      simpa [RawCostProc.fromComponents] using safe
  | head :: next :: rest, safe => by
      obtain ⟨headSafe, tailSafe⟩ :=
        (List.forall_cons
          (fun component : RawCostProc =>
            component.binderSafeAt depth = true)
          head (next :: rest)).mp safe
      simp only [RawCostProc.binderSafeAt, Bool.and_eq_true]
      exact ⟨headSafe,
        RawCostProc.fromComponents_binderSafeAt depth (next :: rest) tailSafe⟩

theorem RawCostTerm.fromComponents_binderSafeAt (depth : Nat) :
    ∀ items : List RawCostTerm,
      items.Forall (fun component => component.binderSafeAt depth = true) →
      (RawCostTerm.fromComponents items).binderSafeAt depth = true
  | [], _ => rfl
  | head :: [], safe => by
      simpa [RawCostTerm.fromComponents] using safe
  | head :: next :: rest, safe => by
      obtain ⟨headSafe, tailSafe⟩ :=
        (List.forall_cons
          (fun component : RawCostTerm =>
            component.binderSafeAt depth = true)
          head (next :: rest)).mp safe
      simp only [RawCostTerm.binderSafeAt, Bool.and_eq_true]
      exact ⟨headSafe,
        RawCostTerm.fromComponents_binderSafeAt depth (next :: rest) tailSafe⟩

mutual
  /-- Structural normalization preserves checked name scope. -/
  theorem RawCostName.binderSafeAt_normalize (depth : Nat) :
      ∀ name : RawCostName, name.binderSafeAt depth = true →
        name.normalize.binderSafeAt depth = true
    | .bvar index, safe => safe
    | .quote term, safe => by
        have termSafe : term.binderSafeAt 0 = true := by
          simpa [RawCostName.binderSafeAt] using safe
        have normalizedSafe :=
          RawCostTerm.binderSafeAt_normalize 0 term termSafe
        simp only [RawCostName.normalize]
        generalize normalizedEq : term.normalize = normalized
          at normalizedSafe ⊢
        cases normalized with
        | drop name =>
            have nameSafe : name.binderSafeAt 0 = true := by
              simpa [RawCostTerm.binderSafeAt] using normalizedSafe
            exact RawCostName.binderSafeAt_mono nameSafe (Nat.zero_le depth)
        | nil => rfl
        | signed process signature =>
            simpa [RawCostName.binderSafeAt] using normalizedSafe
        | par left right =>
            simpa [RawCostName.binderSafeAt] using normalizedSafe
        | purse surface stack =>
            rfl
    | .signature signature, _ => rfl

  /-- Structural normalization preserves checked process scope. -/
  theorem RawCostProc.binderSafeAt_normalize (depth : Nat) :
      ∀ process : RawCostProc, process.binderSafeAt depth = true →
        process.normalize.binderSafeAt depth = true
    | .nil, _ => rfl
    | .par left right, safe => by
        simp only [RawCostProc.binderSafeAt, Bool.and_eq_true] at safe
        have leftSafe := RawCostProc.binderSafeAt_normalize depth left safe.1
        have rightSafe := RawCostProc.binderSafeAt_normalize depth right safe.2
        apply RawCostProc.fromComponents_binderSafeAt depth
        apply stableSortBy_forall
        rw [List.forall_append]
        exact ⟨RawCostProc.components_forall_binderSafeAt depth
            left.normalize leftSafe,
          RawCostProc.components_forall_binderSafeAt depth
            right.normalize rightSafe⟩
    | .send channel payload, safe => by
        simp only [RawCostProc.binderSafeAt, Bool.and_eq_true] at safe ⊢
        exact ⟨RawCostName.binderSafeAt_normalize depth channel safe.1,
          RawCostTerm.binderSafeAt_normalize depth payload safe.2⟩
    | .recv channel body, safe => by
        simp only [RawCostProc.binderSafeAt, Bool.and_eq_true] at safe ⊢
        exact ⟨RawCostName.binderSafeAt_normalize depth channel safe.1,
          RawCostTerm.binderSafeAt_normalize (depth + 1) body safe.2⟩

  /-- Structural normalization preserves checked term scope. -/
  theorem RawCostTerm.binderSafeAt_normalize (depth : Nat) :
      ∀ term : RawCostTerm, term.binderSafeAt depth = true →
        term.normalize.binderSafeAt depth = true
    | .nil, _ => rfl
    | .signed process signature, safe => by
        simpa [RawCostTerm.normalize, RawCostTerm.binderSafeAt] using
          RawCostProc.binderSafeAt_normalize depth process safe
    | .par left right, safe => by
        simp only [RawCostTerm.binderSafeAt, Bool.and_eq_true] at safe
        have leftSafe := RawCostTerm.binderSafeAt_normalize depth left safe.1
        have rightSafe := RawCostTerm.binderSafeAt_normalize depth right safe.2
        apply RawCostTerm.fromComponents_binderSafeAt depth
        apply stableSortBy_forall
        rw [List.forall_append]
        exact ⟨RawCostTerm.components_forall_binderSafeAt depth
            left.normalize leftSafe,
          RawCostTerm.components_forall_binderSafeAt depth
            right.normalize rightSafe⟩
    | .drop name, safe => by
        simpa [RawCostTerm.normalize, RawCostTerm.binderSafeAt] using
          RawCostName.binderSafeAt_normalize depth name safe
    | .purse surface stack, _ => rfl
end

/-- Normalized top-level executable components remain in checked binder
scope. -/
theorem RawCostTerm.normalizeConfig_forall_binderSafe
    {term : RawCostTerm} (safe : term.binderSafe = true) :
    term.normalizeConfig.Forall (fun component => component.binderSafe = true) := by
  apply stableSortBy_forall
  exact RawCostTerm.components_forall_binderSafeAt 0 term.normalize
    (RawCostTerm.binderSafeAt_normalize 0 term safe)

/-- Reassembling and normalizing retained components, a safe contractum, and
purse tails preserves top-level scope. -/
theorem residualFor_forall_binderSafe
    {config : RawCostConfig}
    (participants : List Nat) (selected : List RawSelectedPurse)
    (retainedSafe :
      (eraseIndices config
        (participants ++ selected.map RawIndexedPurse.index)).Forall
          (fun term => term.binderSafe = true))
    {contractum : RawCostTerm} (contractumSafe : contractum.binderSafe = true) :
    (residualFor config participants selected contractum).normalizeConfig.Forall
      (fun term => term.binderSafe = true) := by
  let retained := eraseIndices config
    (participants ++ selected.map RawIndexedPurse.index)
  let tails := selected.map fun purse =>
    RawCostTerm.purse purse.surface purse.tail
  let items := retained ++ contractum.normalize.components ++ tails
  have normalizedContractumSafe :=
    RawCostTerm.binderSafeAt_normalize 0 contractum contractumSafe
  have contractumComponentsSafe :=
    RawCostTerm.components_forall_binderSafeAt 0 contractum.normalize
      normalizedContractumSafe
  have tailsSafe : tails.Forall (fun term => term.binderSafe = true) := by
    rw [List.forall_iff_forall_mem]
    intro term member
    obtain ⟨purse, _purseMember, rfl⟩ := List.mem_map.mp member
    rfl
  have itemsSafe : items.Forall (fun term => term.binderSafe = true) := by
    simp only [items, List.forall_append]
    exact ⟨⟨retainedSafe, contractumComponentsSafe⟩, tailsSafe⟩
  have assembledSafe := RawCostTerm.fromComponents_binderSafeAt 0 items itemsSafe
  have normalizedSafe := RawCostTerm.binderSafeAt_normalize 0
    (RawCostTerm.fromComponents items) assembledSafe
  have residualSafe :
      (residualFor config participants selected contractum).binderSafe = true := by
    simpa [residualFor, items, retained, tails,
      RawCostTerm.normalize_idempotent] using normalizedSafe
  exact RawCostTerm.normalizeConfig_forall_binderSafe residualSafe

/-- If the declarative residual ingredients are binder-safe, the executable
residual assembled from those same occurrences decodes to a binder-safe
configuration. -/
theorem residualFor_decode_binderSafe
    (config : RawCostConfig) (participants : List Nat)
    (selected : List RawSelectedPurse) (contractum : RawCostTerm)
    (ingredientsSafe : CostConfig.BinderSafe
      (decodeRawConfig
          (eraseIndices config
            (participants ++ selected.map RawIndexedPurse.index)) +
        (decodeCostTerm contractum).components +
        (selected.map
          (fun purse =>
            decodeCostTerm (.purse purse.surface purse.tail)) :
            Multiset (CostTerm String)))) :
    CostConfig.BinderSafe
      (decodeRawConfig
        (residualFor config participants selected contractum).normalizeConfig) := by
  let retained := eraseIndices config
    (participants ++ selected.map RawIndexedPurse.index)
  let tails := selected.map fun purse =>
    RawCostTerm.purse purse.surface purse.tail
  let ingredients := retained ++ contractum.components ++ tails
  have decodedIngredients :
      decodeRawConfig ingredients =
        decodeRawConfig retained + (decodeCostTerm contractum).components +
          (selected.map
            (fun purse =>
              decodeCostTerm (.purse purse.surface purse.tail)) :
              Multiset (CostTerm String)) := by
    simp only [ingredients, tails, List.append_assoc,
      decodeRawConfig_append, decodeRawConfig_components]
    simp [decodeRawConfig, Function.comp_def, add_assoc]
  have ingredientsDecodedSafe :
      (decodeRawConfig ingredients).BinderSafe := by
    rw [decodedIngredients]
    simpa [retained] using ingredientsSafe
  have ingredientsRawSafe :
      ingredients.Forall (fun term => term.binderSafe = true) :=
    (RawCostConfig.binderSafe_iff_decode ingredients).mpr ingredientsDecodedSafe
  have separated :
      retained.Forall (fun term => term.binderSafe = true) ∧
      contractum.components.Forall
          (fun term => term.binderSafe = true) ∧
      tails.Forall (fun term => term.binderSafe = true) := by
    simpa [ingredients, List.forall_append] using ingredientsRawSafe
  have contractumSafe : contractum.binderSafe = true :=
    RawCostTerm.binderSafeAt_of_components 0 contractum separated.2.1
  have residualRawSafe := residualFor_forall_binderSafe participants selected
    (by simpa [retained] using separated.1) contractumSafe
  exact (RawCostConfig.binderSafe_iff_decode _).mp residualRawSafe

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
