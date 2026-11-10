import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SettlementInstances

/-!
# Helpers minted in the result frame: the same-target form is strictly stronger

A firing may mint helpers in its result frame, as the native step does with the helpers its solver
returns. Its settlement is then an inclusion, and an answer into a frame with no term of a helper's
sort cannot be recovered **in that frame**. Answer coverage (`CoversAnswers`) allows the answer's
frame to be extended; the same-target form does not.

Over a signature with an inhabited sort and an **empty sort** (`twoSorts`, `no_void_term`), the
firing `mint` takes, reads, makes and tells nothing and mints one helper of the empty sort:
* it covers its answers after extending their frames by the helper (`mint_coversAnswers`, through
  `incl_extends`: the inclusion of the frame with one more name is faithful, `incl_faithful`, and
  every morphism lifts along it);
* it does not cover in the strong same-target form (`mint_not_covers`): the answer into the empty
  frame has no extension there.

So the same-target form is a sufficient special case and strictly stronger
(`strong_form_strictly_stronger`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SettlementCoverage.FreshTarget

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface (Frames)
open Interface.Frames (Frame)
open Interface.Helpers (State extend incl lift compose_lift_incl)
open DisequalityFrames (Prestep)
open MeTTaCalculus.OccurrenceCommits (fire)

/-- **Two sorts**: `true` has one constant, `false` has none. -/
abbrev twoSorts : Signature where
  Srt := Bool
  Op s := match s with
    | true => Unit
    | false => Empty
  arity _ := []

/-- The empty frame. -/
abbrev empty : Frame twoSorts := ⟨Empty, fun impossible => impossible.elim⟩

/-- A parameterless helper of the empty sort. -/
abbrev void : MetaArity twoSorts := ([], false)

/-- **The empty sort has no closed term over the empty frame.** -/
theorem no_void_term : Term (signature twoSorts empty.arity) [] false → False
  | .var v => nomatch v
  | .op (.inl o) _ => nomatch o
  | .op (.inr o) _ => o.key.elim

/-- The inclusion of a frame into the frame with one more name, as an extension of declarations. -/
def inclExtension (F : Frame twoSorts) (helper : MetaArity twoSorts) :
    ContextualGuardMatching.Extension F.arity :=
  ⟨F.Names ⊕ Unit, (extend F helper).arity, Sum.inl, Sum.inl_injective, fun _ => rfl⟩

/-- **The inclusion into the frame with one more name is faithful.** -/
theorem incl_faithful (F : Frame twoSorts) (helper : MetaArity twoSorts) :
    Faithful (Frames.contextual twoSorts) (a := F) (b := extend F helper) (incl F helper) :=
  extension_faithful (inclExtension F helper)

/-- **Every morphism lifts along the inclusion**, by the faithful inclusion of its target. -/
theorem incl_extends (F : Frame twoSorts) (helper : MetaArity twoSorts) :
    Extends (Frames.contextual twoSorts) (a := F) (a' := extend F helper) (incl F helper) := by
  intro b σ
  refine ⟨extend b helper, incl b helper, lift σ helper, incl_faithful b helper, fun t => ?_⟩
  show instantiateObservation (Assignment.compose (incl b helper) σ) t =
    instantiateObservation (Assignment.compose (lift σ helper) (incl F helper)) t
  rw [compose_lift_incl]

/-- **The firing that mints a helper of the empty sort in its result**: it takes, reads, makes and
tells nothing; its target is the state's frame, its result frame adds the helper, and its
settlement is the inclusion. -/
def mint : Prestep (Frames.contextual twoSorts) Nat (State twoSorts Nat) (fun _ => Unit) where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection _ := ⟨[], [], []⟩
  target {s} _ := s.frame
  extension {s} _ := (Frames.contextual twoSorts).id s.frame
  information {s} _ :=
    (Frames.contextual twoSorts).applyStore ((Frames.contextual twoSorts).id s.frame) s.knowledge
  transported _ e member := List.mem_map.mpr ⟨e, member, rfl⟩
  Shapes _ := ([] : List Nat).Nodup
  Holds _ _ σ := (Frames.contextual twoSorts).Models σ []
  result {s} _ _ := ⟨extend s.frame void, (Frames.contextual twoSorts).applyStore (incl s.frame void)
    ((Frames.contextual twoSorts).applyStore ((Frames.contextual twoSorts).id s.frame) s.knowledge), s.present⟩
  present_result _ _ := by ext o; simp [fire, Selection.commit]
  settle {s} _ _ := incl s.frame void
  knowledge_result _ _ := rfl

/-- The state at the empty frame. -/
abbrev start : State twoSorts Nat := ⟨empty, [], ∅⟩

theorem mint_admitted : mint.step.Admits (s := start) () :=
  ⟨List.nodup_nil, EvidenceInterface.Controls.enabled_nothing ∅,
    ⟨empty, (Frames.contextual twoSorts).id empty, Frames.models_nil _⟩,
    fun _ σ _ => Frames.models_nil (X := Frames.contextual twoSorts) σ⟩

/-- **Minting covers its answers**, after extending their frames by the helper. -/
theorem mint_coversAnswers : CoversAnswers mint.step.toStep := by
  apply coversAnswers_of_extends
  intro s _ _
  exact incl_extends s.frame void

/-- **Minting does not cover in the strong same-target form**: the answer into the empty frame has
no value there for the helper of the empty sort. -/
theorem mint_not_covers : ¬ CoversSettlement mint.step.toStep := by
  intro covers
  obtain ⟨τ, -, -⟩ := covers (s := start) () mint_admitted (b := empty)
    ((Frames.contextual twoSorts).id empty) (Frames.models_nil _)
  exact no_void_term (τ (.inr ()))

/-- **The same-target form is strictly stronger than answer coverage.** -/
theorem strong_form_strictly_stronger : CoversAnswers mint.step.toStep ∧ ¬ CoversSettlement mint.step.toStep :=
  ⟨mint_coversAnswers, mint_not_covers⟩

#print axioms no_void_term
#print axioms incl_faithful
#print axioms incl_extends
#print axioms mint_coversAnswers
#print axioms mint_not_covers
#print axioms strong_form_strictly_stronger

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SettlementCoverage.FreshTarget
