import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LawfulTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualDiamond

/-!
# The helper transport is lawful

On the canonical declaration frames the frame equivalence is equality, so two contextual morphisms
agree exactly when they are equal (`Frames.contextual_agree_iff`).

* **Guards** (`Helpers.helperGuards`): a helper firing's guards are equations on the names of the
  frame it fires at; they read no occurrence, so their region is empty.
* **Residual coherence** (`Helpers.helperCoherent`): the residual of `f` after `g` carries `f`'s
  target into its own by lifting `g`'s inclusion (`lift`). The residual's target, the frame with
  both helpers, is the amalgamation of the two targets over the state's frame: a solution reads the
  old names and `g`'s helper through `g`'s side and `f`'s helper through `f`'s side
  (`Helpers.amalgam`), and is determined by the two restrictions. Its information is `f`'s carried
  together with `g`'s result knowledge.
* **Lawful** (`Helpers.helperLawful`): settlement is the identity, and isomorphic firings have
  results related by the isomorphism of their targets.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (fire)
open Interface.Frames (Frame)

/-- **Contextual morphisms agree exactly when they are equal.** -/
theorem Frames.contextual_agree_iff {S : Signature} {F G : Frame S}
    {φ ψ : Assignment F.arity G.arity} : (Frames.contextual S).Agree φ ψ ↔ φ = ψ := by
  constructor
  · intro same
    funext name
    have law := same (observe (generator F.arity name))
    change instantiateObservation φ (observe (generator F.arity name)) =
      instantiateObservation ψ (observe (generator F.arity name)) at law
    rw [instantiateObservation_observe, instantiateObservation_observe] at law
    have terms := observe_injective law
    rwa [instantiate_generator, instantiate_generator] at terms
  · rintro rfl
    exact fun _ => rfl

namespace Helpers

variable {S : Signature} {O : Type} [DecidableEq O]

/-- **The guards of a helper firing**: equations on the names of its frame, which read no
occurrence. -/
def helperGuards : (helperStep (S := S) (O := O)).Guards where
  Guard {s} f _ σ _ := (Frames.contextual S).Models (Assignment.compose σ (incl s.frame f.helper)) f.guards
  region _ _ _ := ∅
  holds_iff _ _ _ := Iff.rfl
  respects _ _ σ τ same _ := by
    obtain rfl := Frames.contextual_agree_iff.mp same
    exact Iff.rfl
  inside _ _ _ _ _ _ := Iff.rfl

/-- A solution of the frame with one more helper that reads the old names through `τ` and the
helper through `σ`. -/
def amalgam {F G : Frame S} (helper : MetaArity S) {b : Frame S} (τ : Assignment G.arity b.arity)
    (σ : Assignment (extend F helper).arity b.arity) : Assignment (extend G helper).arity b.arity
  | .inl name => τ name
  | .inr () => σ (.inr ())

theorem amalgam_incl {F G : Frame S} (helper : MetaArity S) {b : Frame S}
    (τ : Assignment G.arity b.arity) (σ : Assignment (extend F helper).arity b.arity) :
    Assignment.compose (amalgam helper τ σ) (incl G helper) = τ := by
  funext name
  exact instantiate_generator (amalgam helper τ σ) (.inl name)

/-- **The amalgamation of `f`'s target with `g`'s result.** -/
theorem amalgam_lift {F G : Frame S} (helper : MetaArity S) {b : Frame S}
    (φ : Assignment F.arity G.arity) (τ : Assignment G.arity b.arity)
    (σ : Assignment (extend F helper).arity b.arity)
    (agree : Assignment.compose σ (incl F helper) = Assignment.compose τ φ) :
    Assignment.compose (amalgam helper τ σ) (lift φ helper) = σ := by
  funext name
  rcases name with name | ⟨⟩
  · have step : instantiate (amalgam helper τ σ) (instantiate (incl G helper) (φ name)) =
        instantiate τ (φ name) := by
      rw [← Assignment.instantiate_compose, amalgam_incl]
    have old : instantiate σ (generator (extend F helper).arity (.inl name)) = instantiate τ (φ name) :=
      congrFun agree name
    rw [instantiate_generator] at old
    exact step.trans old.symm
  · exact instantiate_generator (amalgam helper τ σ) (.inr ())

/-- **Residual coherence of the helper transport.** -/
def helperCoherent : (helperTransport (S := S) (O := O)).Coherent helperGuards where
  carry g admitted f := lift (helperStep.along g admitted) f.helper
  square _ _ f := Frames.Agree.of_eq (compose_lift_incl _ f.helper)
  amalgamate {s} g admitted f b σ τ agree :=
    ⟨amalgam f.helper τ σ,
      Frames.Agree.of_eq (amalgam_lift f.helper (helperStep.along g admitted) τ σ
        (Frames.contextual_agree_iff.mp agree)),
      Frames.Agree.of_eq (amalgam_incl (F := s.frame) f.helper τ σ)⟩
  separated {s} g admitted f b ρ ρ' throughCarry throughExtension := by
    have carried := Frames.contextual_agree_iff.mp throughCarry
    have extended := Frames.contextual_agree_iff.mp throughExtension
    apply Frames.Agree.of_eq
    funext name
    rcases name with name | ⟨⟩
    · have law : instantiate ρ (generator (extend (extend s.frame g.helper) f.helper).arity (.inl name)) =
          instantiate ρ' (generator (extend (extend s.frame g.helper) f.helper).arity (.inl name)) :=
        congrFun extended name
      exact (instantiate_generator ρ _).symm.trans (law.trans (instantiate_generator ρ' _))
    · have law : instantiate ρ (generator (extend (extend s.frame g.helper) f.helper).arity (.inr ())) =
          instantiate ρ' (generator (extend (extend s.frame g.helper) f.helper).arity (.inr ())) :=
        congrFun carried (.inr ())
      exact (instantiate_generator ρ _).symm.trans (law.trans (instantiate_generator ρ' _))
  information {s} g admitted f := by
    have value : instantiate (lift (helperStep.along g admitted) f.helper)
          (instantiate (incl s.frame f.helper) f.value) =
        instantiate (incl (extend s.frame g.helper) f.helper)
          (instantiate (helperStep.along g admitted) f.value) :=
      (Assignment.instantiate_compose _ _ _).symm.trans
        ((congrArg (fun assignment => instantiate assignment f.value)
          (compose_lift_incl (helperStep.along g admitted) f.helper)).trans
          (Assignment.instantiate_compose _ _ _))
    have carried : (Frames.contextual S).applyStore (lift (helperStep.along g admitted) f.helper)
          f.information =
        (Frames.contextual S).applyStore (incl (extend s.frame g.helper) f.helper)
            ((Frames.contextual S).applyStore (helperStep.along g admitted) s.knowledge) ++
          [(observe (fresh (extend s.frame g.helper) f.helper),
            observe (instantiate (incl (extend s.frame g.helper) f.helper)
              (instantiate (helperStep.along g admitted) f.value)))] := by
      unfold Firing.information
      rw [Frames.applyStore_append, Frames.applyStore_applyStore, Frames.applyStore_applyStore]
      congr 1
      · show (Frames.contextual S).applyStore
            (Assignment.compose (lift (helperStep.along g admitted) f.helper) (incl s.frame f.helper))
            s.knowledge =
          (Frames.contextual S).applyStore
            (Assignment.compose (incl (extend s.frame g.helper) f.helper) (helperStep.along g admitted))
            s.knowledge
        rw [compose_lift_incl]
      · show [(observe (instantiate (lift (helperStep.along g admitted) f.helper) (fresh s.frame f.helper)),
            observe (instantiate (lift (helperStep.along g admitted) f.helper)
              (instantiate (incl s.frame f.helper) f.value)))] =
          [(observe (fresh (extend s.frame g.helper) f.helper),
            observe (instantiate (incl (extend s.frame g.helper) f.helper)
              (instantiate (helperStep.along g admitted) f.value)))]
        rw [instantiate_lift_fresh, value]
    have inside : ∀ e, e ∈ (Frames.contextual S).applyStore (incl (extend s.frame g.helper) f.helper)
          ((Frames.contextual S).applyStore (helperStep.along g admitted) s.knowledge) →
        e ∈ (Frames.contextual S).applyStore (incl (extend s.frame g.helper) f.helper) g.information := by
      intro e member
      obtain ⟨e', known, rfl⟩ := List.mem_map.mp member
      refine List.mem_map.mpr ⟨e', ?_, rfl⟩
      rw [along_eq g admitted] at known
      exact List.mem_append_left _ known
    show (Frames.contextual S).Equivalent
        ((Frames.contextual S).applyStore (incl (extend s.frame g.helper) f.helper) g.information ++
          [(observe (fresh (extend s.frame g.helper) f.helper),
            observe (instantiate (incl (extend s.frame g.helper) f.helper)
              (instantiate (helperStep.along g admitted) f.value)))])
        ((Frames.contextual S).applyStore (lift (helperStep.along g admitted) f.helper) f.information ++
          (Frames.contextual S).applyStore (incl (extend s.frame g.helper) f.helper) g.information)
    rw [carried]
    apply Frames.equivalent_of_mem_iff
    intro e
    simp only [List.mem_append]
    constructor
    · rintro (old | told)
      · exact Or.inr old
      · exact Or.inl (Or.inr told)
    · rintro ((known | told) | old)
      · exact Or.inl (inside e known)
      · exact Or.inr told
      · exact Or.inl old
  shapes _ _ _ := Iff.rfl
  guard {s} g admitted f _ ρ _ := by
    show (Frames.contextual S).Models (Assignment.compose ρ (incl (extend s.frame g.helper) f.helper))
        ((Frames.contextual S).applyStore (helperStep.along g admitted) f.guards) ↔
      (Frames.contextual S).Models
        (Assignment.compose (Assignment.compose ρ (lift (helperStep.along g admitted) f.helper))
          (incl s.frame f.helper)) f.guards
    rw [Frames.models_applyStore]
    have assoc : Assignment.compose (Assignment.compose ρ (incl (extend s.frame g.helper) f.helper))
          (helperStep.along g admitted) =
        Assignment.compose (Assignment.compose ρ (lift (helperStep.along g admitted) f.helper))
          (incl s.frame f.helper) :=
      (Assignment.compose_associative _ _ _).symm.trans
        ((congrArg (Assignment.compose ρ) (compose_lift_incl (helperStep.along g admitted) f.helper).symm).trans
          (Assignment.compose_associative _ _ _))
    show (Frames.contextual S).Models (Assignment.compose (Assignment.compose ρ
        (incl (extend s.frame g.helper) f.helper)) (helperStep.along g admitted)) f.guards ↔ _
    rw [assoc]

/-- **The helper transport is lawful.** -/
def helperLawful : (helperTransport (S := S) (O := O)).Lawful helperGuards where
  coherent := helperCoherent
  conservative _ _ _ σ _ := ⟨σ, (Frames.agree_id_right (X := Frames.contextual S) σ).symm⟩
  canonical {s} {f₁ f₂} i _ _ := by
    have selection : f₁.selection = f₂.selection := i.selection
    refine ⟨⟨i.frame, i.information, Equiv.refl O, ?_⟩⟩
    show (fire s.present (f₁.selection.commit (T := Unit))).map (Equiv.refl O).toEmbedding =
      fire s.present (f₂.selection.commit (T := Unit))
    rw [Equiv.refl_toEmbedding, Finset.map_refl, selection]

end Helpers

#print axioms Frames.contextual_agree_iff
#print axioms Helpers.amalgam_lift
#print axioms Helpers.helperGuards
#print axioms Helpers.helperCoherent
#print axioms Helpers.helperLawful

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
