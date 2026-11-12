import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCore

/-!
# Proofs with prepared leaves, and admission as their grade

An effect core says which candidates are prepared: shaped, enabled on fresh outputs, with
solvable information. Permission is a separate predicate on prepared candidates. Read logically,
a prepared candidate is a leaf of a proof, and permission is where the leaf may be used.

The proofs of an effect core are the runs of its proof step, the step that admits every prepared
candidate (`proofStep`). They are paths of prepared candidates.

* `exists_run_iff_permitted`: a proof is the word of a run of the step under an admission
  exactly when every leaf is permitted. Runs are the permitted proofs.
* `PermittedAt`: the permission part of the grade of a proof at a placement, leaf by leaf: the
  placed candidate of each leaf is permitted at the placement the earlier leaves leave.
* `permitted_placed_iff`: for an admission that is a property of similarity classes
  (`Invariant`), a placed proof is permitted exactly when the leafwise grade holds.
* `placed_proof_runs_iff_graded`: **a proof has a placed proof that is a run exactly on its
  grade**: the structural grade of the framing of proofs, and the leafwise permission.

The framing is a contextual interpretation of the proof step. It transports prepared candidates
and asks no permission, so a leaf need not be admitted where it stands alone.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore

universe uO uT uH uOcc uS uF uI uP

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}

/-- The proof step of an effect core: every prepared candidate is admitted. Its runs are the
proofs: paths of prepared candidates. -/
abbrev proofStep (E : EffectCore X O State Firing) : Step X O State Firing :=
  Step.ofEffect E (fun _ _ => True)

variable {E : EffectCore X O State Firing} (allow : E.Admission)

/-- A proof is permitted when every one of its leaves is. -/
def Permitted : ∀ {s : State}, (proofStep E).Run s → Prop
  | _, .nil _ => True
  | _, .cons f admitted rest => allow f ((proofStep E).prepares admitted) ∧ Permitted rest

/-- **Runs are the permitted proofs.** A proof is the word of a run of the step under an
admission exactly when every leaf is permitted. -/
theorem exists_run_iff_permitted : ∀ {s : State} (proof : (proofStep E).Run s),
    (∃ run : (Step.ofEffect E allow).Run s, run.word = proof.word) ↔ Permitted allow proof
  | _, .nil s => ⟨fun _ => trivial, fun _ => ⟨.nil s, rfl⟩⟩
  | _, .cons f admitted rest => by
      have ih := exists_run_iff_permitted rest
      constructor
      · rintro ⟨run, word⟩
        cases run with
        | nil => exact absurd word.symm (List.cons_ne_nil _ _)
        | cons g allowed later =>
            have parts := List.cons.inj word
            have same : g = f := eq_of_heq (Sigma.mk.inj parts.1).2
            subst same
            obtain ⟨_, permitted⟩ := allowed
            exact ⟨permitted, ih.mp ⟨later, parts.2⟩⟩
      · rintro ⟨permitted, later⟩
        obtain ⟨run, word⟩ := ih.mpr later
        exact ⟨.cons f ⟨(proofStep E).prepares admitted, permitted⟩ run,
          congrArg (List.cons _) word⟩

variable {T₀ : Transport.{uO,uT,uH,uOcc,uS,uF,uI} (proofStep E)}
  (I₀ : ContextualRunInterpretation.{uO,uT,uH,uOcc,uS,uF,uI,uP} T₀)

/-- The permission part of the grade of a proof at a placement, leaf by leaf: the placed
candidate of each leaf is permitted. -/
def PermittedAt : ∀ {left right : State}, I₀.Place left right → (proofStep E).Run left → Prop
  | _, _, _, .nil _ => True
  | _, _, place, .cons f admitted rest =>
      (∃ placed : E.Prepares (I₀.candidate place f), allow (I₀.candidate place f) placed) ∧
        PermittedAt (I₀.advance place f admitted) rest

/-- Permission is a property of similarity classes of proofs. -/
def Invariant (T₀ : Transport.{uO,uT,uH,uOcc,uS,uF,uI} (proofStep E)) : Prop :=
  ∀ {s t : State} (one : (proofStep E).Run s) (two : (proofStep E).Run t),
    T₀.Similar one two → (Permitted allow one ↔ Permitted allow two)

/-- **A placed proof is permitted exactly when the leafwise grade holds.** -/
theorem permitted_placed_iff (invariant : Invariant allow T₀) :
    ∀ {left right : State} {place : I₀.Place left right} {proof : (proofStep E).Run left}
      {native : (proofStep E).Run (I₀.pair place).state},
      Places I₀ place proof native → (Permitted allow native ↔ PermittedAt allow I₀ place proof)
  | _, _, _, _, _, .nil _ => Iff.rfl
  | _, _, _, _, _, .cons _ _ tail similar => by
      have later := permitted_placed_iff invariant tail
      have moved := invariant _ _ similar
      constructor
      · rintro ⟨permitted, rest⟩
        exact ⟨⟨_, permitted⟩, later.mp (moved.mpr rest)⟩
      · rintro ⟨⟨_, permitted⟩, rest⟩
        exact ⟨permitted, moved.mp (later.mpr rest)⟩

/-- **Runs are graded proofs, with prepared leaves.** A proof has a placed proof that is
permitted exactly when the placement is in its grade: the structural grade of the framing, and
the leafwise permission. -/
theorem placed_proof_runs_iff_graded (invariant : Invariant allow T₀) {left right : State}
    (place : I₀.Place left right) (proof : (proofStep E).Run left) :
    (∃ native : (proofStep E).Run (I₀.pair place).state,
      Places I₀ place proof native ∧ Permitted allow native) ↔
      I₀.Checks place proof ∧ PermittedAt allow I₀ place proof := by
  constructor
  · rintro ⟨native, placed, permitted⟩
    exact ⟨checks_of_places I₀ placed, (permitted_placed_iff allow I₀ invariant placed).mp permitted⟩
  · rintro ⟨checked, permitted⟩
    obtain ⟨native, placed, _⟩ := placed_run_of_checks I₀ place proof checked
    exact ⟨native, placed, (permitted_placed_iff allow I₀ invariant placed).mpr permitted⟩

/-- The same, with the run of the step under the admission named: a placed proof is the word of
a run exactly on the grade. -/
theorem placed_proof_is_a_run_iff_graded (invariant : Invariant allow T₀) {left right : State}
    (place : I₀.Place left right) (proof : (proofStep E).Run left) :
    (∃ (native : (proofStep E).Run (I₀.pair place).state)
        (run : (Step.ofEffect E allow).Run (I₀.pair place).state),
      Places I₀ place proof native ∧ run.word = native.word) ↔
      I₀.Checks place proof ∧ PermittedAt allow I₀ place proof := by
  rw [← placed_proof_runs_iff_graded allow I₀ invariant place proof]
  constructor
  · rintro ⟨native, run, placed, word⟩
    exact ⟨native, placed, (exists_run_iff_permitted allow native).mp ⟨run, word⟩⟩
  · rintro ⟨native, placed, permitted⟩
    obtain ⟨run, word⟩ := (exists_run_iff_permitted allow native).mpr permitted
    exact ⟨native, run, placed, word⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore
