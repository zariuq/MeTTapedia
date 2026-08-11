import Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
import Mettapedia.Languages.Metamath.NIKAuthority

/-!
# Statusful default-NIK frontend for Metamath

Metamath exposes two exact evidence representations for one admitted source
scope: native postfix label lists and ProofGSLT articles.  This module places
both in the common statusful NIK protocol without adding another Metamath
semantics.

The request carrier is an in-memory semantic envelope.  A later textual or
binary codec may refine it, but is not part of this adapter.
-/

namespace Mettapedia.Languages.Metamath.NIKDefault

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
open Mettapedia.GSLT.LanguageDef.ProofGSLT
open Mettapedia.Languages.Metamath.NIKAuthority

/-- The already proved two-evidence Metamath authority family. -/
abbrev Family (scope : SourceScope) := authorityFamily scope

/-- A semantic request envelope.  Its constructors retain the evidence kind,
while malformed syntax and an unknown authority remain distinct cases. -/
inductive Request (scope : SourceScope) where
  | malformed
  | unknownAuthority (name : String)
  | normalLabels (claim : Claim scope) (labels : List String)
  | proofArticle (claim : Claim scope) (article : WireArticle)

/-- Parsing separates malformed input from well-formed but unresolved
authority names. -/
inductive Parsed (scope : SourceScope) where
  | unknownAuthority (name : String)
  | submission (request : TypedSubmission (Family scope))

def frontend (scope : SourceScope) : Frontend (Family scope) (Request scope) where
  Parsed := Parsed scope
  parse
    | .malformed => none
    | .unknownAuthority name => some (.unknownAuthority name)
    | .normalLabels claim labels =>
        some (.submission ⟨.normalLabels, claim, labels⟩)
    | .proofArticle claim article =>
        some (.submission ⟨.proofArticle, claim, article⟩)
  resolve
    | .unknownAuthority _ => none
    | .submission request => some request
  encode := fun ⟨kind, claim, certificate⟩ =>
    match kind with
    | .normalLabels => .normalLabels claim certificate
    | .proofArticle => .proofArticle claim certificate
  resolve_encode := by
    rintro ⟨kind, claim, certificate⟩
    cases kind with
    | normalLabels =>
        exact ⟨.submission ⟨.normalLabels, claim, certificate⟩, rfl, rfl⟩
    | proofArticle =>
        exact ⟨.submission ⟨.proofArticle, claim, certificate⟩, rfl, rfl⟩

def machine (scope : SourceScope) :
    Refinement.Machine (frontend scope) :=
  Refinement.atomic (frontend scope)

@[simp] theorem malformed_status (scope : SourceScope) :
    (frontend scope).run .malformed = .malformed :=
  rfl

@[simp] theorem unknown_authority_status (scope : SourceScope) (name : String) :
    (frontend scope).run (.unknownAuthority name) = .unsupported :=
  rfl

theorem normal_labels_status (scope : SourceScope) (claim : Claim scope)
    (labels : List String) :
    (frontend scope).run (.normalLabels claim labels) =
      if (normalLabelChecker scope).check claim labels then
        .accepted ⟨EvidenceKind.normalLabels, claim⟩
      else
        .rejected ⟨EvidenceKind.normalLabels, claim⟩ := by
  cases checked : (normalLabelChecker scope).check claim labels <;>
    simp [frontend, Frontend.run, checked, TypedSubmission.claim, Family,
      authorityFamily]

theorem proof_article_status (scope : SourceScope) (claim : Claim scope)
    (article : WireArticle) :
    (frontend scope).run (.proofArticle claim article) =
      if (proofArticleChecker scope).check claim article then
        .accepted ⟨EvidenceKind.proofArticle, claim⟩
      else
        .rejected ⟨EvidenceKind.proofArticle, claim⟩ := by
  cases checked : (proofArticleChecker scope).check claim article <;>
    simp [frontend, Frontend.run, checked, TypedSubmission.claim, Family,
      authorityFamily]

/-- Native replay acceptance reaches the common accepted status. -/
theorem accepted_normal_labels (scope : SourceScope) (claim : Claim scope)
    (labels : List String)
    (accepted : (normalLabelChecker scope).check claim labels = true) :
    (frontend scope).run (.normalLabels claim labels) =
      .accepted ⟨EvidenceKind.normalLabels, claim⟩ := by
  simpa [accepted] using normal_labels_status scope claim labels

/-- A failed native replay is rejection, not unsupported input. -/
theorem rejected_normal_labels (scope : SourceScope) (claim : Claim scope)
    (labels : List String)
    (rejected : (normalLabelChecker scope).check claim labels = false) :
    (frontend scope).run (.normalLabels claim labels) =
      .rejected ⟨EvidenceKind.normalLabels, claim⟩ := by
  simpa [rejected] using normal_labels_status scope claim labels

/-- ProofGSLT article acceptance reaches the same common protocol under its
own evidence tag. -/
theorem accepted_proof_article (scope : SourceScope) (claim : Claim scope)
    (article : WireArticle)
    (accepted : (proofArticleChecker scope).check claim article = true) :
    (frontend scope).run (.proofArticle claim article) =
      .accepted ⟨EvidenceKind.proofArticle, claim⟩ := by
  simpa [accepted] using proof_article_status scope claim article

/-- Every declaratively meaningful supported claim has an accepting request
in either selected Metamath evidence fibre. -/
theorem meaning_has_accepted_request (scope : SourceScope)
    (kind : EvidenceKind) (claim : Claim scope)
    (meaningful : Meaning scope claim) :
    ∃ certificate : (Family scope).Certificate kind,
      (frontend scope).run
          ((frontend scope).encode ⟨kind, claim, certificate⟩) =
        .accepted ⟨kind, claim⟩ :=
  (frontend scope).certified_has_accepted_request ⟨kind, claim⟩ meaningful

/-- The statusful adapter preserves the existing exact declarative scope in
both directions. -/
theorem meaning_iff_exists_accepted_request (scope : SourceScope)
    (kind : EvidenceKind) (claim : Claim scope) :
    Meaning scope claim ↔
      ∃ certificate : (Family scope).Certificate kind,
        (frontend scope).run
            ((frontend scope).encode ⟨kind, claim, certificate⟩) =
          .accepted ⟨kind, claim⟩ :=
  (frontend scope).certified_iff_exists_accepted_request ⟨kind, claim⟩

end Mettapedia.Languages.Metamath.NIKDefault
