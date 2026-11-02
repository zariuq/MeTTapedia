import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.SharedRenaming
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualRecovery

/-!
# Contextual inverse matching entirely on shared references

Inverse renaming and forward grafting use the shared-store operations. Forward
verification compares canonical references, not expanded trees. Failed recovery
still returns its canonical store extension, so allocated nodes have an explicit
owner. The specification is the existing exact contextual recovery operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.SharedApplication

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication
open ContextualPatterns

variable {Head : Type} [DecidableEq Head]

def checkForwardR (store : Store Head) (arity : Nat) (indices : List Nat) (body target : Ref) :
    Store Head × Bool :=
  let prepared := variablesR store indices
  match graftR prepared.1 arity prepared.2 body with
  | none => (prepared.1, false)
  | some result => (result.1, decide (result.2 = target))

theorem checkForwardR_spec (store : Store Head) (canonical : Canonical store)
    (arity : Nat) (indices : List Nat) (body target : Ref)
    (validBody : CanonRef store body) (validTarget : CanonRef store target) :
    store <+: (checkForwardR store arity indices body target).1 ∧
      Canonical (checkForwardR store arity indices body target).1 ∧
      ((checkForwardR store arity indices body target).2 = true ↔
        graft arity (indices.map Term.idx) (unfold store body) = some (unfold store target)) := by
  obtain ⟨grows, nextCanonical, arguments, values⟩ := variablesR_spec store canonical indices
  have semantic := graftR_spec (variablesR store indices).1 nextCanonical arity
    (variablesR store indices).2 body (validBody.prefix grows) arguments
  rw [values, unfold_prefix canonical.topo grows validBody.valid] at semantic
  unfold checkForwardR
  dsimp only
  cases applied : graftR (variablesR store indices).1 arity (variablesR store indices).2 body with
  | none =>
    refine ⟨grows, nextCanonical, ?_⟩
    have refused : graft arity (indices.map Term.idx) (unfold store body) = none := by
      simpa [applied] using semantic.symm
    simp [refused]
  | some result =>
    obtain ⟨more, finalCanonical, outputValid⟩ :=
      graftR_canonical nextCanonical (validBody.prefix grows) arguments applied
    refine ⟨grows.trans more, finalCanonical, ?_⟩
    have produced : graft arity (indices.map Term.idx) (unfold store body) =
        some (unfold result.1 result.2) := by simpa [applied] using semantic.symm
    simp only [decide_eq_true_eq, produced, Option.some.injEq]
    rw [← unfold_prefix canonical.topo (grows.trans more) validTarget.valid]
    exact (unfold_eq_iff finalCanonical outputValid (validTarget.prefix (grows.trans more))).symm

def recoverR (store : Store Head) (arity : Nat) (arguments : List (Term Head)) (target : Ref) :
    Store Head × Option Ref :=
  match Recovery.indices? arguments with
  | none => (store, none)
  | some indices =>
      if indices.length = arity ∧ indices.Nodup then
        let inverted := renameR store (fun i => indices.idxOf i) target
        let checked := checkForwardR inverted.1 arity indices inverted.2 target
        (checked.1, if checked.2 then some inverted.2 else none)
      else (store, none)

/-- Reference recovery preserves store validity and agrees exactly with the tree operation. -/
theorem recoverR_spec (store : Store Head) (canonical : Canonical store) (arity : Nat)
    (arguments : List (Term Head)) (target : Ref) (validTarget : CanonRef store target) :
    store <+: (recoverR store arity arguments target).1 ∧
      Canonical (recoverR store arity arguments target).1 ∧
      (∀ body, (recoverR store arity arguments target).2 = some body →
        CanonRef (recoverR store arity arguments target).1 body) ∧
      (recoverR store arity arguments target).2.map (unfold (recoverR store arity arguments target).1) =
        Recovery.recover arity arguments (unfold store target) := by
  cases extracted : Recovery.indices? arguments with
  | none =>
    simp only [recoverR, extracted]
    refine ⟨List.prefix_refl _, canonical, ?_, ?_⟩
    · intro body impossible
      cases impossible
    · simp [Recovery.recover, extracted]
  | some indices =>
    by_cases shape : indices.length = arity ∧ indices.Nodup
    · have args := Recovery.indices?_sound arguments indices extracted
      obtain ⟨grows, inverseCanonical, inverseValid, inverseTree⟩ :=
        renameR_spec store canonical (fun i => indices.idxOf i) target validTarget
      obtain ⟨more, finalCanonical, checkedIff⟩ := checkForwardR_spec
        (renameR store (fun i => indices.idxOf i) target).1 inverseCanonical arity indices
        (renameR store (fun i => indices.idxOf i) target).2 target inverseValid (validTarget.prefix grows)
      let inverted := renameR store (fun i => indices.idxOf i) target
      let checked := checkForwardR inverted.1 arity indices inverted.2 target
      have tree : unfold inverted.1 inverted.2 = Recovery.inverse indices (unfold store target) := inverseTree
      have laterTree : unfold checked.1 inverted.2 = Recovery.inverse indices (unfold store target) :=
        (unfold_prefix inverseCanonical.topo more inverseValid.valid).trans tree
      have exactCheck : checked.2 = true ↔
          graft arity arguments (Recovery.inverse indices (unfold store target)) = some (unfold store target) := by
        change checked.2 = true ↔ _ at checkedIff
        simpa only [← args, inverseTree, Recovery.inverse,
          unfold_prefix canonical.topo grows validTarget.valid] using checkedIff
      simp only [recoverR, extracted, if_pos shape]
      change store <+: checked.1 ∧ Canonical checked.1 ∧
        (∀ body, (if checked.2 then some inverted.2 else none) = some body → CanonRef checked.1 body) ∧
        (if checked.2 then some inverted.2 else none).map (unfold checked.1) = _
      refine ⟨grows.trans more, finalCanonical, ?_, ?_⟩
      · intro body accepted
        split at accepted
        · cases accepted
          exact inverseValid.prefix more
        · cases accepted
      · by_cases accepted : checked.2 = true
        · have forward := exactCheck.mp accepted
          simp [accepted, Recovery.recover, extracted, shape, forward, laterTree]
        · have refused := mt exactCheck.mpr accepted
          simp [accepted, Recovery.recover, extracted, shape, refused]
    · simp only [recoverR, extracted, if_neg shape]
      refine ⟨List.prefix_refl _, canonical, ?_, ?_⟩
      · intro body impossible
        cases impossible
      · simp [Recovery.recover, extracted, shape]

namespace RecoveryControls

theorem argumentStore_canonical : Canonical Controls.argumentStore :=
  (encodeR_spec _ (encodeR_spec [] canonical_nil (.idx 0 : Term Nat)).2.1 Controls.eight).2.1

theorem nested_canonical : Canonical Controls.nested.1 :=
  (encodeR_spec _ argumentStore_canonical _).2.1

theorem nested_valid : CanonRef Controls.nested.1 Controls.nested.2 :=
  (encodeR_spec _ argumentStore_canonical _).2.2.1

theorem shared_recovery_permuted_spine :
    let result := recoverR Controls.stored.1 2 [.idx 1, .idx 0] Controls.stored.2
    result.2.map (unfold result.1) = some (Controls.pair (.idx 1) (.idx 0)) := by decide

theorem shared_recovery_refuses_undeclared_dependency :
    (recoverR Controls.stored.1 1 [.idx 0] Controls.stored.2).2 = none := by decide

theorem shared_recovery_refuses_duplicate_spine :
    (recoverR Controls.stored.1 2 [.idx 0, .idx 0] Controls.stored.2).2 = none := by decide

theorem shared_recovery_under_binder :
    let result := recoverR Controls.nested.1 2 [.idx 1, .idx 0] Controls.nested.2
    result.2.map (unfold result.1) =
      some (.node 1 (.cons 1 (Controls.pair (.idx 2) (.idx 1)) .nil)) := by
  change (recoverR Controls.nested.1 2 [.idx 1, .idx 0] Controls.nested.2).2.map
    (unfold (recoverR Controls.nested.1 2 [.idx 1, .idx 0] Controls.nested.2).1) = _
  rw [(recoverR_spec _ nested_canonical 2 [.idx 1, .idx 0] _ nested_valid).2.2.2]
  rw [show unfold Controls.nested.1 Controls.nested.2 =
    .node 1 (.cons 1 (Controls.pair (.idx 1) (.idx 2)) .nil) from
      encodeR_unfold argumentStore_canonical _]
  decide

end RecoveryControls
end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.SharedApplication
