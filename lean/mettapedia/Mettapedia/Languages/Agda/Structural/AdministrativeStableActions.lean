import Mettapedia.Languages.Agda.Structural.AdministrativeStableCertificates

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.StablePreservation

open Mettapedia.OSLF.Binding
open Statics (RawTm RawTy RawContext RawSub)
open Preservation

def TypedAction {n : Nat} : {s : Srt} → Term sig (scope n) s → Term sig (scope n) s → Type
  | .term, source, target => ∀ Γ A, CoreDerivation (Statics.typed Γ source A) →
      CoreDerivation (Statics.termEqual Γ source target A)
  | .type, source, target => ∀ Γ, CoreDerivation (Statics.formed Γ source) →
      CoreDerivation (Statics.typeEqual Γ source target)
  | .spine, source, target => ∀ Γ A B, Action Γ A source B → SpineEq Γ A source target B
  | .elim, source, target => ∀ Γ A B rest, Action Γ A (cons source rest) B →
      SpineEq Γ A (cons source rest) (cons target rest) B
  | .sort, source, _ => ∀ k, source = set (levelClosed k) → PEmpty
  | .level, source, _ => ∀ k, source = levelClosed k → PEmpty

def StableAction {n : Nat} {s : Srt} (source target : Term sig (scope n) s) : Type :=
  ∀ {m : Nat} (σ : RawSub n m), TypedAction (bind σ source) (bind σ target)

structure BetaCases where
  binding : ∀ {n : Nat} (body : RawTm (n + 1)) (argument : RawTm n) (rest : Spine (scope n)),
    TypedAction (eliminate (lam body) (cons (apply argument) rest)) (eliminate (inst body argument) rest)
  nonbinding : ∀ {n : Nat} (body argument : RawTm n) (rest : Spine (scope n)),
    TypedAction (eliminate (lamNoAbs body) (cons (apply argument) rest)) (eliminate body rest)

noncomputable def rootAction (beta : BetaCases) {n : Nat} {s : Srt}
    {source target : Term sig (scope n) s} (root : Root source target) : TypedAction source target := by
  cases root with
  | beta body argument rest => exact beta.binding body argument rest
  | betaNoAbs body argument rest => exact beta.nonbinding body argument rest
  | eliminateEmpty head => exact (Preservation.eliminateEmpty head).equality
  | eliminateAppend head first second => exact (Preservation.eliminateAppend head first second).equality
  | appendEmpty rest => exact (Preservation.appendEmpty rest).equality
  | appendCons head first second => exact (Preservation.appendCons head first second).equality

noncomputable def stableRoot (beta : BetaCases) {n : Nat} {s : Srt}
    {source target : Term sig (scope n) s} (root : Root source target) : StableAction source target :=
  fun σ => rootAction beta (Root.substitute σ root)

noncomputable def termAt {n m : Nat} {source target : RawTm n}
    (step : Step source target) (action : StableAction source target) (σ : RawSub n m) :
    TermCertificate (bind σ source) (bind σ target) where
  step := Step.substitute σ step
  equality := action σ

noncomputable def typeAt {n m : Nat} {source target : RawTy n}
    (step : Step source target) (action : StableAction source target) (σ : RawSub n m) :
    TypeCertificate (bind σ source) (bind σ target) where
  step := Step.substitute σ step
  equality := action σ

noncomputable def spineAt {n m : Nat} {source target : Spine (scope n)}
    (step : Step source target) (action : StableAction source target) (σ : RawSub n m) :
    SpineCertificate (bind σ source) (bind σ target) where
  step := Step.substitute σ step
  equality := action σ

noncomputable def stableTermAt {n m : Nat} {source target : RawTm n}
    (step : Step source target) (action : StableAction source target) (σ : RawSub n m) :
    StableTermCertificate (bind σ source) (bind σ target) where
  step := Step.substitute σ step
  equality τ Γ A := by
    simp only [Telescope.bind_compose σ τ source, Telescope.bind_compose σ τ target]
    exact action (Telescope.comp σ τ) Γ A

noncomputable def openedTypeAt {n m : Nat} {source target : RawTy n}
    (step : Step source target) (action : StableAction source target) (σ : RawSub n m) :
    TypeCertificate (bind (Telescope.projection (S := sig) .term m) (bind σ source))
      (bind (Telescope.projection (S := sig) .term m) (bind σ target)) where
  step := Step.substitute (Telescope.projection (S := sig) .term m) (Step.substitute σ step)
  equality Γ := by
    simp only [Telescope.bind_compose σ (Telescope.projection (S := sig) .term m) source,
      Telescope.bind_compose σ (Telescope.projection (S := sig) .term m) target]
    exact action (Telescope.comp σ (Telescope.projection (S := sig) .term m)) Γ

def sortAction {n : Nat} {source target : UnivSort (scope n)} (step : Step source target) :
    StableAction source target := by
  intro m σ k same
  have instantiated := Step.substitute σ step
  have changed : Step (set (levelClosed k)) (bind σ target) :=
    (congrArg (fun t : UnivSort (scope m) => Step t (bind σ target)) same).mp instantiated
  exact False.elim ((finiteSet_inert k _).false changed)

def levelAction {n : Nat} {source target : Level (scope n)} (step : Step source target) :
    StableAction source target := by
  intro m σ k same
  have instantiated := Step.substitute σ step
  have changed : Step (levelClosed k) (bind σ target) :=
    (congrArg (fun t : Level (scope m) => Step t (bind σ target)) same).mp instantiated
  exact False.elim ((closedLevel_inert k _).false changed)

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.StablePreservation
