import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeDeadEquivalence
import Mettapedia.OSLF.Syntax.ContextualRigidTerms

/-!
# Closed row readings descend through native dead-name agreement

A reading uses a real present occurrence, a model of the state's knowledge and the existing
conditional-row matching relation. Its tested syntax has no metavariables; target frames and row
instances remain arbitrary. A dead-name extension preserves and reflects these readings, including
schemas and their latent equations. Models in the larger frame are supplied by fresh generators.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativeClosedReadings

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching (Extension)
open NativeDead

variable {S : Signature} {O : Type} {Γ : Ctx S} {sort : S.Srt}

abbrev closedArity (S : Signature) : Empty → MetaArity S := Empty.elim

/-- Binding syntax with no metavariable declarations. Object binders and result sorts remain. -/
abbrev ClosedTerm (S : Signature) (Γ : Ctx S) (sort : S.Srt) :=
  Term (signature S (closedArity S)) Γ sort

def emptyAssignment {V : Type} (declaration : V → MetaArity S) :
    Assignment (closedArity S) declaration := fun name => nomatch name

def closedAt {V : Type} (declaration : V → MetaArity S) (pattern : ClosedTerm S Γ sort) :
    Term (signature S declaration) Γ sort :=
  instantiate (emptyAssignment declaration) pattern

theorem compose_empty {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}
    (assignment : Assignment source target) :
    Assignment.compose assignment (emptyAssignment source) = emptyAssignment target := by
  funext name
  exact Empty.elim name

theorem closedAt_natural {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}
    (assignment : Assignment source target) (pattern : ClosedTerm S Γ sort) :
    instantiate assignment (closedAt source pattern) = closedAt target pattern := by
  unfold closedAt
  rw [← Assignment.instantiate_compose, compose_empty]

def closedExtension {V : Type} (declaration : V → MetaArity S) : Extension (closedArity S) where
  Names := V
  declarations := declaration
  name := Empty.elim
  injective := by
    intro name
    exact Empty.elim name
  preserves name := Empty.elim name

theorem closedExtension_assignment {V : Type} (declaration : V → MetaArity S) :
    (closedExtension declaration).assignment = emptyAssignment declaration := by
  funext name
  exact Empty.elim name

/-- Embedding closed syntax into a model frame loses no term, binder or constructor. -/
theorem closedAt_injective {V : Type} (declaration : V → MetaArity S) :
    Function.Injective (closedAt declaration (Γ := Γ) (sort := sort)) := by
  intro first second same
  apply (closedExtension declaration).instantiate_injective
  rw [closedExtension_assignment]
  exact same

/-- A closed reading of an actual physical row, with both global knowledge and row-local
conditions interpreted by the existing model and matching relations. -/
def Reads (state : NativeState S O Γ sort) (occurrence : O) (pattern : ClosedTerm S Γ sort) : Prop :=
  occurrence ∈ state.state.present ∧
    ∃ (target : Frames.Frame S) (candidate : Assignment state.state.declarations target.arity),
      ContextualResidual.Models candidate state.state.equations ∧
        ContextualConditionalRows.Matches state.locals state.state.declarations candidate
          (closedAt target.arity pattern) (state.state.rows occurrence)

def readings (state : NativeState S O Γ sort) (occurrence : O) : Set (ClosedTerm S Γ sort) :=
  {pattern | Reads state occurrence pattern}

/-- The actual frame inclusion underlying a dead-name extension. -/
def frameExtension {before after : NativeState S O Γ sort} (embedding : Inclusion before after) :
    Extension before.state.declarations :=
  ⟨after.state.Names, after.state.declarations, embedding.names,
    embedding.names_injective, embedding.names_preserves⟩

theorem frameExtension_assignment {before after : NativeState S O Γ sort}
    (embedding : Inclusion before after) :
    (frameExtension embedding).assignment = embedding.frame := rfl

/-- Carrying a conditional row retains its actual schemas and latent conditions. -/
theorem matches_carried_iff {before after : NativeState S O Γ sort}
    (embedding : Inclusion before after) {target : Frames.Frame S}
    (candidate : Assignment after.state.declarations target.arity)
    (pattern : Term (signature S target.arity) Γ sort)
    (row : ContextualConditionalRows.Row before.locals before.state.declarations Γ sort) :
    ContextualConditionalRows.Matches after.locals after.state.declarations candidate pattern
        (embedding.row row) ↔
      ContextualConditionalRows.Matches before.locals before.state.declarations
        (Assignment.compose candidate embedding.frame) pattern row :=
  (NativeDead.matches_reindexPrivate_iff before.locals after.locals after.state.declarations
    embedding.locals embedding.locals_injective embedding.locals_preserves candidate
    (row.map before.locals before.state.declarations embedding.frame) pattern).trans
      (ContextualConditionalRows.matches_map_iff before.locals before.state.declarations
        embedding.frame candidate pattern row)

theorem deadExtension_reads_iff {before after : NativeState S O Γ sort}
    (extension : DeadExtension before after) (occurrence : O) (pattern : ClosedTerm S Γ sort) :
    Reads after occurrence pattern ↔ Reads before occurrence pattern := by
  constructor
  · rintro ⟨present, target, candidate, model, matched⟩
    refine ⟨?_, target, Assignment.compose candidate extension.frame, ?_, ?_⟩
    · rwa [extension.present] at present
    · apply (ContextualResidual.models_mapProblem extension.frame candidate
        before.state.equations).mp
      intro equation member
      exact model equation (extension.equations.mem_iff.mpr member)
    · rw [extension.rows occurrence] at matched
      exact (matches_carried_iff extension.toInclusion candidate _ _).mp matched
  · rintro ⟨present, target, candidate, model, matched⟩
    let frame := frameExtension extension.toInclusion
    let grown : Frames.Frame S :=
      ⟨frame.Complement ⊕ target.Names,
        ContextualPrefixModels.extended frame.complementDeclarations target.arity⟩
    let lifted : Assignment after.state.declarations grown.arity := frame.liftModel candidate
    have mapped : ContextualResidual.Models lifted
        (ContextualResidual.mapProblem extension.frame before.state.equations) :=
      (ContextualConditionalNaturality.models_liftModel_iff frame candidate
        before.state.equations).mpr model
    refine ⟨?_, grown, lifted, ?_, ?_⟩
    · rwa [extension.present]
    · intro equation member
      exact mapped equation (extension.equations.mem_iff.mp member)
    · rw [extension.rows occurrence]
      apply (matches_carried_iff extension.toInclusion lifted _ _).mpr
      have carried := (ContextualConditionalNaturality.matches_inclusion_iff before.locals
        frame.complementDeclarations candidate (closedAt target.arity pattern)
        (before.state.rows occurrence)).mpr matched
      rw [closedAt_natural] at carried
      rw [← frame.liftModel_square candidate] at carried
      exact carried

theorem deadEquiv_present {first second : NativeState S O Γ sort} (same : DeadEquiv first second) :
    first.state.present = second.state.present := by
  obtain ⟨common, ⟨left⟩, ⟨right⟩⟩ := same
  exact left.present.symm.trans right.present

theorem deadEquiv_reads_iff {first second : NativeState S O Γ sort}
    (same : DeadEquiv first second) (occurrence : O) (pattern : ClosedTerm S Γ sort) :
    Reads first occurrence pattern ↔ Reads second occurrence pattern := by
  obtain ⟨common, ⟨left⟩, ⟨right⟩⟩ := same
  exact (deadExtension_reads_iff left occurrence pattern).symm.trans
    (deadExtension_reads_iff right occurrence pattern)

theorem deadEquiv_readings {first second : NativeState S O Γ sort}
    (same : DeadEquiv first second) (occurrence : O) :
    readings first occurrence = readings second occurrence := by
  ext pattern
  exact deadEquiv_reads_iff same occurrence pattern

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativeClosedReadings
