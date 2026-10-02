import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RawScope

/-!
# Whole runtime scope through canonical normalization

These laws include purse locations and keep quotation opaque to surrounding
binders. They provide the closed payload and literal name controls needed to
compare communication before and after the existing raw normalizer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

mutual
  theorem RawCostName.runtimeBinderSafeAt_mono {small large : Nat} {name : RawCostName}
      (safe : name.runtimeBinderSafeAt small = true) (larger : small ≤ large) :
      name.runtimeBinderSafeAt large = true := by
    cases name with
    | bvar index =>
      simp only [RawCostName.runtimeBinderSafeAt, decide_eq_true_eq] at safe ⊢
      omega
    | quote term => exact safe
    | signature signature => rfl

  theorem RawCostProc.runtimeBinderSafeAt_mono {small large : Nat} {process : RawCostProc}
      (safe : process.runtimeBinderSafeAt small = true) (larger : small ≤ large) :
      process.runtimeBinderSafeAt large = true := by
    cases process with
    | nil => rfl
    | par left right =>
      simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true] at safe ⊢
      exact ⟨RawCostProc.runtimeBinderSafeAt_mono safe.1 larger,
        RawCostProc.runtimeBinderSafeAt_mono safe.2 larger⟩
    | send name term =>
      simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true] at safe ⊢
      exact ⟨RawCostName.runtimeBinderSafeAt_mono safe.1 larger,
        RawCostTerm.runtimeBinderSafeAt_mono safe.2 larger⟩
    | recv name term =>
      simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true] at safe ⊢
      exact ⟨RawCostName.runtimeBinderSafeAt_mono safe.1 larger,
        RawCostTerm.runtimeBinderSafeAt_mono safe.2 (Nat.add_le_add_right larger 1)⟩

  theorem RawCostTerm.runtimeBinderSafeAt_mono {small large : Nat} {term : RawCostTerm}
      (safe : term.runtimeBinderSafeAt small = true) (larger : small ≤ large) :
      term.runtimeBinderSafeAt large = true := by
    cases term with
    | nil => rfl
    | signed process signature => exact RawCostProc.runtimeBinderSafeAt_mono safe larger
    | par left right =>
      simp only [RawCostTerm.runtimeBinderSafeAt, Bool.and_eq_true] at safe ⊢
      exact ⟨RawCostTerm.runtimeBinderSafeAt_mono safe.1 larger,
        RawCostTerm.runtimeBinderSafeAt_mono safe.2 larger⟩
    | drop name => exact RawCostName.runtimeBinderSafeAt_mono safe larger
    | purse name stack => exact RawCostName.runtimeBinderSafeAt_mono safe larger
end

mutual
  theorem RawCostName.runtimeBinderSafeAt_liftAbove_eq {scope cutoff : Nat}
      {name : RawCostName} (safe : name.runtimeBinderSafeAt scope = true)
      (larger : scope ≤ cutoff) (amount : Nat) : name.lift amount cutoff = name := by
    cases name with
    | bvar index =>
      simp only [RawCostName.runtimeBinderSafeAt, decide_eq_true_eq] at safe
      simp [RawCostName.lift, show ¬cutoff ≤ index from by omega]
    | quote term => rfl
    | signature signature => rfl

  theorem RawCostProc.runtimeBinderSafeAt_liftAbove_eq {scope cutoff : Nat}
      {process : RawCostProc} (safe : process.runtimeBinderSafeAt scope = true)
      (larger : scope ≤ cutoff) (amount : Nat) : process.lift amount cutoff = process := by
    cases process with
    | nil => rfl
    | par left right =>
      simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true] at safe
      simp only [RawCostProc.lift, RawCostProc.runtimeBinderSafeAt_liftAbove_eq safe.1 larger amount,
        RawCostProc.runtimeBinderSafeAt_liftAbove_eq safe.2 larger amount]
    | send name term =>
      simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true] at safe
      simp only [RawCostProc.lift, RawCostName.runtimeBinderSafeAt_liftAbove_eq safe.1 larger amount,
        RawCostTerm.runtimeBinderSafeAt_liftAbove_eq safe.2 larger amount]
    | recv name term =>
      simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true] at safe
      simp only [RawCostProc.lift, RawCostName.runtimeBinderSafeAt_liftAbove_eq safe.1 larger amount,
        RawCostTerm.runtimeBinderSafeAt_liftAbove_eq safe.2 (Nat.add_le_add_right larger 1) amount]

  theorem RawCostTerm.runtimeBinderSafeAt_liftAbove_eq {scope cutoff : Nat}
      {term : RawCostTerm} (safe : term.runtimeBinderSafeAt scope = true)
      (larger : scope ≤ cutoff) (amount : Nat) : term.lift amount cutoff = term := by
    cases term with
    | nil => rfl
    | signed process signature =>
      simp only [RawCostTerm.lift, RawCostProc.runtimeBinderSafeAt_liftAbove_eq safe larger amount]
    | par left right =>
      simp only [RawCostTerm.runtimeBinderSafeAt, Bool.and_eq_true] at safe
      simp only [RawCostTerm.lift, RawCostTerm.runtimeBinderSafeAt_liftAbove_eq safe.1 larger amount,
        RawCostTerm.runtimeBinderSafeAt_liftAbove_eq safe.2 larger amount]
    | drop name =>
      simp only [RawCostTerm.lift, RawCostName.runtimeBinderSafeAt_liftAbove_eq safe larger amount]
    | purse name stack =>
      simp only [RawCostTerm.lift, RawCostName.runtimeBinderSafeAt_liftAbove_eq safe larger amount]
end

theorem RawCostProc.components_forall_runtimeBinderSafeAt (depth : Nat) :
    ∀ process : RawCostProc, process.runtimeBinderSafeAt depth = true →
      process.components.Forall (fun component => component.runtimeBinderSafeAt depth = true)
  | .nil, _ => by simp
  | .par left right, safe => by
      simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true] at safe
      simp only [RawCostProc.components, List.forall_append]
      exact ⟨RawCostProc.components_forall_runtimeBinderSafeAt depth left safe.1,
        RawCostProc.components_forall_runtimeBinderSafeAt depth right safe.2⟩
  | .send name term, safe => by simpa [RawCostProc.components] using safe
  | .recv name term, safe => by simpa [RawCostProc.components] using safe

theorem RawCostTerm.components_forall_runtimeBinderSafeAt (depth : Nat) :
    ∀ term : RawCostTerm, term.runtimeBinderSafeAt depth = true →
      term.components.Forall (fun component => component.runtimeBinderSafeAt depth = true)
  | .nil, _ => by simp
  | .par left right, safe => by
      simp only [RawCostTerm.runtimeBinderSafeAt, Bool.and_eq_true] at safe
      simp only [RawCostTerm.components, List.forall_append]
      exact ⟨RawCostTerm.components_forall_runtimeBinderSafeAt depth left safe.1,
        RawCostTerm.components_forall_runtimeBinderSafeAt depth right safe.2⟩
  | .signed process signature, safe => by simpa [RawCostTerm.components] using safe
  | .drop name, safe => by simpa [RawCostTerm.components] using safe
  | .purse name stack, safe => by simpa [RawCostTerm.components] using safe

theorem RawCostProc.fromComponents_runtimeBinderSafeAt (depth : Nat) :
    ∀ items : List RawCostProc,
      items.Forall (fun component => component.runtimeBinderSafeAt depth = true) →
      (RawCostProc.fromComponents items).runtimeBinderSafeAt depth = true
  | [], _ => rfl
  | [process], safe => by simpa [RawCostProc.fromComponents] using safe
  | head :: next :: rest, safe => by
      have both := (List.forall_cons _ head (next :: rest)).mp safe
      simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true]
      exact ⟨both.1,
        RawCostProc.fromComponents_runtimeBinderSafeAt depth (next :: rest) both.2⟩

theorem RawCostTerm.fromComponents_runtimeBinderSafeAt (depth : Nat) :
    ∀ items : List RawCostTerm,
      items.Forall (fun component => component.runtimeBinderSafeAt depth = true) →
      (RawCostTerm.fromComponents items).runtimeBinderSafeAt depth = true
  | [], _ => rfl
  | [term], safe => by simpa [RawCostTerm.fromComponents] using safe
  | head :: next :: rest, safe => by
      have both := (List.forall_cons _ head (next :: rest)).mp safe
      simp only [RawCostTerm.runtimeBinderSafeAt, Bool.and_eq_true]
      exact ⟨both.1,
        RawCostTerm.fromComponents_runtimeBinderSafeAt depth (next :: rest) both.2⟩

mutual
  theorem RawCostName.runtimeBinderSafeAt_normalize (depth : Nat) :
      ∀ name : RawCostName, name.runtimeBinderSafeAt depth = true →
      name.normalize.runtimeBinderSafeAt depth = true
    | .bvar index, safe => safe
    | .signature signature, safe => rfl
    | .quote term, safe => by
      have normalizedSafe := RawCostTerm.runtimeBinderSafeAt_normalize 0 term safe
      simp only [RawCostName.normalize]
      generalize normalizedEq : term.normalize = normalized at normalizedSafe ⊢
      cases normalized with
      | nil => rfl
      | signed process signature => exact normalizedSafe
      | par left right => exact normalizedSafe
      | drop name => exact RawCostName.runtimeBinderSafeAt_mono normalizedSafe (Nat.zero_le depth)
      | purse name stack => exact normalizedSafe

  theorem RawCostProc.runtimeBinderSafeAt_normalize (depth : Nat) :
      ∀ process : RawCostProc, process.runtimeBinderSafeAt depth = true →
      process.normalize.runtimeBinderSafeAt depth = true
    | .nil, _ => rfl
    | .par left right, safe => by
      simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true] at safe
      apply RawCostProc.fromComponents_runtimeBinderSafeAt depth
      apply stableKeySort_forall
      simp only [List.forall_append]
      exact ⟨RawCostProc.components_forall_runtimeBinderSafeAt depth left.normalize
          (RawCostProc.runtimeBinderSafeAt_normalize depth left safe.1),
        RawCostProc.components_forall_runtimeBinderSafeAt depth right.normalize
          (RawCostProc.runtimeBinderSafeAt_normalize depth right safe.2)⟩
    | .send name term, safe => by
      simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true] at safe ⊢
      exact ⟨RawCostName.runtimeBinderSafeAt_normalize depth name safe.1,
        RawCostTerm.runtimeBinderSafeAt_normalize depth term safe.2⟩
    | .recv name term, safe => by
      simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true] at safe ⊢
      exact ⟨RawCostName.runtimeBinderSafeAt_normalize depth name safe.1,
        RawCostTerm.runtimeBinderSafeAt_normalize (depth + 1) term safe.2⟩

  theorem RawCostTerm.runtimeBinderSafeAt_normalize (depth : Nat) :
      ∀ term : RawCostTerm, term.runtimeBinderSafeAt depth = true →
      term.normalize.runtimeBinderSafeAt depth = true
    | .nil, _ => rfl
    | .signed process signature, safe =>
      RawCostProc.runtimeBinderSafeAt_normalize depth process safe
    | .par left right, safe => by
      simp only [RawCostTerm.runtimeBinderSafeAt, Bool.and_eq_true] at safe
      apply RawCostTerm.fromComponents_runtimeBinderSafeAt depth
      apply stableKeySort_forall
      simp only [List.forall_append]
      exact ⟨RawCostTerm.components_forall_runtimeBinderSafeAt depth left.normalize
          (RawCostTerm.runtimeBinderSafeAt_normalize depth left safe.1),
        RawCostTerm.components_forall_runtimeBinderSafeAt depth right.normalize
          (RawCostTerm.runtimeBinderSafeAt_normalize depth right safe.2)⟩
    | .drop name, safe => RawCostName.runtimeBinderSafeAt_normalize depth name safe
    | .purse name stack, safe => RawCostName.runtimeBinderSafeAt_normalize depth name safe
end

theorem RawCostName.substitute_closed_identity {name : RawCostName}
    (closed : name.runtimeBinderSafeAt 0 = true) (replacement : RawCostTerm) (depth : Nat) :
    name.substitute replacement depth = name := by
  cases name with
  | bvar index => simp [RawCostName.runtimeBinderSafeAt] at closed
  | quote term => rfl
  | signature signature => rfl

theorem RawCostTerm.substitute_drop_closed_identity {name : RawCostName}
    (closed : name.runtimeBinderSafeAt 0 = true) (replacement : RawCostTerm) (depth : Nat) :
    RawCostTerm.substitute replacement depth (.drop name) = .drop name := by
  cases name with
  | bvar index => simp [RawCostName.runtimeBinderSafeAt] at closed
  | quote term => rfl
  | signature signature => rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
