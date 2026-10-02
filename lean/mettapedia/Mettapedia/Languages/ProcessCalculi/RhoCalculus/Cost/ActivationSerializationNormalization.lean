import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSerializationAdmission

/-!
# Normalization preserves serialized admission

The existing raw normalizer changes binary parallel layout and may eliminate
a quote around a drop. Shared component traversals retain actual accepted
signature witnesses and closed quoted code through these operations. Purse
normalization changes only its fixed nominal index; every ordered singleton
head remains exactly the same literal key.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated.SerializationAdmission

mutual
  theorem NameAdmitted.weaken {scope depth : Nat} {name : RawCostName}
      (image : NameAdmitted scope name) (larger : scope ≤ depth) : NameAdmitted depth name := by
    cases image with
    | bvar bound => exact .bvar (Nat.lt_of_lt_of_le bound larger)
    | quote code => exact .quote code

  theorem CodeAdmitted.weaken {scope depth : Nat} {term : RawCostTerm}
      (image : CodeAdmitted scope term) (larger : scope ≤ depth) : CodeAdmitted depth term := by
    cases image with
    | zero => exact .zero
    | drop name => exact .drop (name.weaken larger)
    | signed process signature => exact .signed (process.weaken larger) signature
    | par first second => exact .par (first.weaken larger) (second.weaken larger)

  theorem ProcAdmitted.weaken {scope depth : Nat} {process : RawCostProc}
      (image : ProcAdmitted scope process) (larger : scope ≤ depth) : ProcAdmitted depth process := by
    cases image with
    | zero => exact .zero
    | send name code => exact .send (name.weaken larger) (code.weaken larger)
    | recv name code => exact .recv (name.weaken larger) (code.weaken (Nat.add_le_add_right larger 1))
    | par first second => exact .par (first.weaken larger) (second.weaken larger)
end

theorem CodeAdmitted.components :
    ∀ {depth : Nat} {term : RawCostTerm},
      CodeAdmitted depth term → term.components.Forall (CodeAdmitted depth) := by
  intro depth term image
  cases term with
  | nil => simp
  | signed process signature =>
      cases image with
      | signed process signature => simpa [RawCostTerm.components] using CodeAdmitted.signed process signature
  | drop name =>
      cases image with
      | drop name => simpa [RawCostTerm.components] using CodeAdmitted.drop name
  | par left right =>
      cases image with
      | par first second =>
          change (left.components ++ right.components).Forall (CodeAdmitted depth)
          exact List.forall_append.mpr ⟨CodeAdmitted.components first, CodeAdmitted.components second⟩
  | purse location stack => cases image

theorem ProcAdmitted.components :
    ∀ {depth : Nat} {process : RawCostProc},
      ProcAdmitted depth process → process.components.Forall (ProcAdmitted depth) := by
  intro depth process image
  cases process with
  | nil => simp
  | send location payload =>
      cases image with
      | send name code => simpa [RawCostProc.components] using ProcAdmitted.send name code
  | recv location body =>
      cases image with
      | recv name code => simpa [RawCostProc.components] using ProcAdmitted.recv name code
  | par left right =>
      cases image with
      | par first second =>
          change (left.components ++ right.components).Forall (ProcAdmitted depth)
          exact List.forall_append.mpr ⟨ProcAdmitted.components first, ProcAdmitted.components second⟩

theorem CodeAdmitted.fromComponents {depth : Nat} {items : List RawCostTerm}
    (images : items.Forall (CodeAdmitted depth)) : CodeAdmitted depth (RawCostTerm.fromComponents items) := by
  induction items with
  | nil => exact .zero
  | cons head tail ih =>
      obtain ⟨first, rest⟩ := (List.forall_cons (CodeAdmitted depth) head tail).mp images
      cases tail with
      | nil => exact first
      | cons next tail => exact .par first (ih rest)

theorem ProcAdmitted.fromComponents {depth : Nat} {items : List RawCostProc}
    (images : items.Forall (ProcAdmitted depth)) : ProcAdmitted depth (RawCostProc.fromComponents items) := by
  induction items with
  | nil => exact .zero
  | cons head tail ih =>
      obtain ⟨first, rest⟩ := (List.forall_cons (ProcAdmitted depth) head tail).mp images
      cases tail with
      | nil => exact first
      | cons next tail => exact .par first (ih rest)

mutual
  theorem NameAdmitted.normalize {depth : Nat} {name : RawCostName}
      (image : NameAdmitted depth name) : NameAdmitted depth name.normalize := by
    cases image with
    | bvar bound => exact .bvar bound
    | @quote _ code body =>
        have normalized := body.normalize
        change NameAdmitted depth (match code.normalize with | .drop name => name | normalized => .quote normalized)
        cases result : code.normalize with
        | nil => exact .quote (result ▸ normalized)
        | signed process signature => exact .quote (result ▸ normalized)
        | par left right => exact .quote (result ▸ normalized)
        | drop name =>
            rw [result] at normalized
            cases normalized with
            | drop closed => exact closed.weaken (Nat.zero_le depth)
        | purse location stack =>
            rw [result] at normalized
            cases normalized

  theorem CodeAdmitted.normalize {depth : Nat} {term : RawCostTerm}
      (image : CodeAdmitted depth term) : CodeAdmitted depth term.normalize := by
    cases image with
    | zero => exact .zero
    | drop name => exact .drop name.normalize
    | signed process signature =>
        change CodeAdmitted depth (.signed _ _)
        rw [signature.normalize_identity]
        exact .signed process.normalize signature
    | par first second =>
        apply CodeAdmitted.fromComponents
        apply stableKeySort_forall
        exact List.forall_append.mpr ⟨first.normalize.components, second.normalize.components⟩

  theorem ProcAdmitted.normalize {depth : Nat} {process : RawCostProc}
      (image : ProcAdmitted depth process) : ProcAdmitted depth process.normalize := by
    cases image with
    | zero => exact .zero
    | send name code => exact .send name.normalize code.normalize
    | recv name code => exact .recv name.normalize code.normalize
    | par first second =>
        apply ProcAdmitted.fromComponents
        apply stableKeySort_forall
        exact List.forall_append.mpr ⟨first.normalize.components, second.normalize.components⟩
end

theorem ConfigAdmitted.components {location : RawCostName} {term : RawCostTerm}
    (image : ConfigAdmitted location term) : term.components.Forall (ConfigAdmitted location) := by
  induction image with
  | code body => exact body.components.imp (fun _ image => .code image)
  | purse stack => simpa [RawCostTerm.components] using ConfigAdmitted.purse (location := location) stack
  | par first second left right => exact List.forall_append.mpr ⟨left, right⟩

theorem ConfigAdmitted.fromComponents {location : RawCostName} {items : List RawCostTerm}
    (images : items.Forall (ConfigAdmitted location)) : ConfigAdmitted location (RawCostTerm.fromComponents items) := by
  induction items with
  | nil => exact .code .zero
  | cons head tail ih =>
      obtain ⟨first, rest⟩ := (List.forall_cons (ConfigAdmitted location) head tail).mp images
      cases tail with
      | nil => exact first
      | cons next tail => exact .par first (ih rest)

theorem ConfigAdmitted.normalize {location : RawCostName} {term : RawCostTerm}
    (image : ConfigAdmitted location term) : ConfigAdmitted location.normalize term.normalize := by
  induction image with
  | code body => exact .code body.normalize
  | purse stack =>
      change ConfigAdmitted _ (.purse _ _)
      rw [stack.normalize_identity]
      exact .purse stack
  | par first second left right =>
      apply ConfigAdmitted.fromComponents
      apply stableKeySort_forall
      exact List.forall_append.mpr ⟨left.components, right.components⟩

theorem ConfigAdmitted.normalizeConfig {location : RawCostName} {term : RawCostTerm}
    (image : ConfigAdmitted location term) :
    term.normalizeConfig.Forall (ConfigAdmitted location.normalize) :=
  stableKeySort_forall _ image.normalize.components

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated.SerializationAdmission
