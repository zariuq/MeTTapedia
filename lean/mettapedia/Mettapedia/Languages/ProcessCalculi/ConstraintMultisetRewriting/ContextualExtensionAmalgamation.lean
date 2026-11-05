import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionSplitting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRealizations

/-!
# Common fresh declaration families for independent matching witnesses

Two injective extensions of one family embed into a common family. The
assignment square fixes their shared declarations and keeps their unused
names separate. This is a logical renaming construction, independent of
physical storage or a runtime snapshot operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching.Extension

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPrefixModels

variable {S : Signature} {V : Type} {declaration : V → MetaArity S}

noncomputable abbrev toSplit (extension : Extension declaration) : Extension extension.declarations where
  Names := Complement extension ⊕ V
  declarations := extended extension.complementDeclarations declaration
  name := extension.splitNames.symm
  injective := extension.splitNames.symm.injective
  preserves := extension.unsplitPreserves

theorem toSplit_assignment (extension : Extension declaration) :
    extension.toSplit.assignment = extension.unsplitAssignment := rfl

noncomputable abbrev amalgamate (first second : Extension declaration) : Extension first.declarations :=
  first.toSplit.trans (second.addUnused first.complementDeclarations)

abbrev includeOther (first second : Extension declaration) : Extension second.declarations :=
  Extension.withLocals first.complementDeclarations second.declarations

theorem amalgamate_square (first second : Extension declaration) :
    Assignment.compose (first.amalgamate second).assignment first.assignment =
      Assignment.compose (first.includeOther second).assignment second.assignment := by
  erw [trans_assignment, toSplit_assignment, ← Assignment.compose_associative, first.unsplit_assignment]
  exact addUnused_square first.complementDeclarations second

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching.Extension

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRealizations

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConditionalRows

variable {S : Signature} {Local Shared Next : Type}
    (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {next : Next → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

theorem Realizes.matches {candidate : Assignment captures next}
    {pattern : Term (signature S next) Γ sort} {row : Row locals captures Γ sort}
    (realized : Realizes locals captures candidate pattern row) : Matches locals captures candidate pattern row := by
  apply (matches_iff locals captures candidate pattern row).mpr
  refine ⟨Extension.identity next, ?_⟩
  have unit : (Extension.identity next).assignment = generator next := rfl
  erw [unit, Assignment.compose_identity_left, instantiate_identity]
  exact realized

theorem matches_extension_iff (extension : Extension next) (candidate : Assignment captures next)
    (pattern : Term (signature S next) Γ sort) (row : Row locals captures Γ sort) :
    Matches locals captures (Assignment.compose extension.assignment candidate)
        (instantiate extension.assignment pattern) row ↔ Matches locals captures candidate pattern row := by
  rw [matches_iff, matches_iff]
  constructor
  · rintro ⟨later, realized⟩
    refine ⟨extension.trans later, ?_⟩
    erw [Extension.trans_assignment, ← Assignment.compose_associative, Assignment.instantiate_compose]
    exact realized
  · rintro ⟨other, realized⟩
    refine ⟨extension.amalgamate other, ?_⟩
    have lifted := realized.future locals captures (extension.includeOther other).assignment
    erw [Assignment.compose_associative, ← Assignment.instantiate_compose, ← extension.amalgamate_square other,
      ← Assignment.compose_associative, Assignment.instantiate_compose] at lifted
    exact lifted

theorem finite_realizations (candidate : Assignment captures next)
    (requests : List (Term (signature S next) Γ sort × Row locals captures Γ sort))
    (matched : ∀ request ∈ requests, Matches locals captures candidate request.1 request.2) :
    ∃ extension : Extension next, ∃ _filler : Assignment locals extension.declarations,
      ∀ request ∈ requests, Realizes locals captures (Assignment.compose extension.assignment candidate)
        (instantiate extension.assignment request.1) request.2 := by
  induction requests with
  | nil =>
      exact ⟨Extension.withLocals locals next,
        (fun name => generator (ContextualSelectionViews.source locals next) (Sum.inl name)),
        fun request member => by cases member⟩
  | cons request rest ih =>
      obtain ⟨extension, filler, tail⟩ := ih (fun later member => matched later (List.mem_cons_of_mem request member))
      have head := (matches_extension_iff locals captures extension candidate request.1 request.2).mpr
        (matched request List.mem_cons_self)
      obtain ⟨later, first⟩ := (matches_iff locals captures _ _ _).mp head
      refine ⟨extension.trans later, Assignment.compose later.assignment filler, ?_⟩
      intro selected member
      erw [Extension.trans_assignment, ← Assignment.compose_associative, Assignment.instantiate_compose]
      rcases List.mem_cons.mp member with rfl | inside
      · exact first
      · exact (tail selected inside).future locals captures later.assignment

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRealizations
