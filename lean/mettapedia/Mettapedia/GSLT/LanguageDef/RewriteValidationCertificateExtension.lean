import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

/-!
# Transporting rewrite certificates across signature extensions

An accepted rewrite remains accepted when its sort and constructor signature
is enlarged, provided newly introduced constructor labels cannot capture any
schema variable, binder, or context name of the rewrite.  The theorem below
states that boundary directly on structural certificates.  It avoids
re-running the generic validator over an already admitted rewrite and a large
generated signature.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

/-- All names whose meaning could change when constructor labels are added. -/
def schemaNames (rewrite : RewriteRule) : List String :=
  (((LanguageDef.patternFvarNames [] rewrite.left ++
      LanguageDef.patternFvarNames [] rewrite.right ++
      rewrite.premises.flatMap
        (LanguageDef.premiseFvarNames [])).eraseDups) ++
    ((LanguageDef.patternBinderNames rewrite.left ++
      LanguageDef.patternBinderNames rewrite.right ++
      (rewrite.premises.flatMap LanguageDef.premisePatterns).flatMap
        LanguageDef.patternBinderNames ++
      rewrite.premises.flatMap
        LanguageDef.premiseForAllParams).eraseDups) ++
    rewrite.typeContext.map Prod.fst).eraseDups

/-- A Boolean property of the three schema-name sources extends to the exact
capture-sensitive name inventory used by signature embeddings. -/
theorem schemaNames_all_of_components
    (rewrite : RewriteRule) (predicate : String -> Bool)
    (fvars :
      ((LanguageDef.patternFvarNames [] rewrite.left ++
        LanguageDef.patternFvarNames [] rewrite.right ++
        rewrite.premises.flatMap
          (LanguageDef.premiseFvarNames [])).eraseDups).all predicate = true)
    (binders :
      ((LanguageDef.patternBinderNames rewrite.left ++
        LanguageDef.patternBinderNames rewrite.right ++
        (rewrite.premises.flatMap LanguageDef.premisePatterns).flatMap
          LanguageDef.patternBinderNames ++
        rewrite.premises.flatMap
          LanguageDef.premiseForAllParams).eraseDups).all predicate = true)
    (context : rewrite.typeContext.all
      (fun entry => predicate entry.1) = true) :
    (schemaNames rewrite).all predicate = true := by
  apply List.all_eq_true.mpr
  intro name membership
  simp only [schemaNames, List.mem_eraseDups, List.mem_append,
    List.mem_map] at membership
  rcases membership with (fvarMembership | binderMembership) |
      ⟨entry, entryMembership, equality⟩
  · have rawMembership : name ∈
        (LanguageDef.patternFvarNames [] rewrite.left ++
          LanguageDef.patternFvarNames [] rewrite.right ++
          rewrite.premises.flatMap
            (LanguageDef.premiseFvarNames [])) := by
      simpa only [List.mem_append] using fvarMembership
    exact List.all_eq_true.mp fvars name
      (by simpa only [List.mem_eraseDups] using rawMembership)
  · have rawMembership : name ∈
        (LanguageDef.patternBinderNames rewrite.left ++
          LanguageDef.patternBinderNames rewrite.right ++
          (rewrite.premises.flatMap LanguageDef.premisePatterns).flatMap
            LanguageDef.patternBinderNames ++
          rewrite.premises.flatMap
            LanguageDef.premiseForAllParams) := by
      simpa only [List.mem_append] using binderMembership
    exact List.all_eq_true.mp binders name
      (by simpa only [List.mem_eraseDups] using rawMembership)
  · subst name
    exact List.all_eq_true.mp context entry entryMembership

/-- Exact append-only signature relation required to transport one rewrite.
The new labels are explicitly checked against the rewrite's schema namespace;
freshness is therefore evidence, not a naming convention hidden in a tactic. -/
structure ExtendsFor (source target : LanguageDef)
    (rewrite : RewriteRule) where
  addedTypes : List String
  addedSignatures : List (String × Nat)
  addedLabels : List String
  typeNames : target.typeNames = source.typeNames ++ addedTypes
  signatures : constructorSignatures target =
    constructorSignatures source ++ addedSignatures
  labels : constructorLabels target =
    constructorLabels source ++ addedLabels
  avoidsSchema : ∀ name ∈ schemaNames rewrite, name ∉ addedLabels

private theorem fvar_mem_schemaNames (rewrite : RewriteRule)
    (name : String)
    (membership : name ∈
      ((LanguageDef.patternFvarNames [] rewrite.left ++
        LanguageDef.patternFvarNames [] rewrite.right ++
        rewrite.premises.flatMap
          (LanguageDef.premiseFvarNames [])).eraseDups)) :
    name ∈ schemaNames rewrite := by
  have rawMembership : name ∈
      (LanguageDef.patternFvarNames [] rewrite.left ++
        LanguageDef.patternFvarNames [] rewrite.right ++
        rewrite.premises.flatMap
          (LanguageDef.premiseFvarNames [])) := by
    simpa only [List.mem_eraseDups] using membership
  have rawProposition :
      (name ∈ LanguageDef.patternFvarNames [] rewrite.left ∨
        name ∈ LanguageDef.patternFvarNames [] rewrite.right) ∨
      name ∈ rewrite.premises.flatMap
        (LanguageDef.premiseFvarNames []) := by
    simpa only [List.mem_append] using rawMembership
  simp only [schemaNames, List.mem_eraseDups, List.mem_append]
  exact Or.inl (Or.inl rawProposition)

private theorem binder_mem_schemaNames (rewrite : RewriteRule)
    (name : String)
    (membership : name ∈
      ((LanguageDef.patternBinderNames rewrite.left ++
        LanguageDef.patternBinderNames rewrite.right ++
        (rewrite.premises.flatMap LanguageDef.premisePatterns).flatMap
          LanguageDef.patternBinderNames ++
        rewrite.premises.flatMap
          LanguageDef.premiseForAllParams).eraseDups)) :
    name ∈ schemaNames rewrite := by
  have rawMembership : name ∈
      (LanguageDef.patternBinderNames rewrite.left ++
        LanguageDef.patternBinderNames rewrite.right ++
        (rewrite.premises.flatMap LanguageDef.premisePatterns).flatMap
          LanguageDef.patternBinderNames ++
        rewrite.premises.flatMap
          LanguageDef.premiseForAllParams) := by
    simpa only [List.mem_eraseDups] using membership
  have rawProposition :
      ((name ∈ LanguageDef.patternBinderNames rewrite.left ∨
          name ∈ LanguageDef.patternBinderNames rewrite.right) ∨
        name ∈ (rewrite.premises.flatMap
          LanguageDef.premisePatterns).flatMap
            LanguageDef.patternBinderNames) ∨
      name ∈ rewrite.premises.flatMap
        LanguageDef.premiseForAllParams := by
    simpa only [List.mem_append] using rawMembership
  simp only [schemaNames, List.mem_eraseDups, List.mem_append]
  exact Or.inl (Or.inr rawProposition)

private theorem context_mem_schemaNames (rewrite : RewriteRule)
    (entry : String × TypeExpr) (membership : entry ∈ rewrite.typeContext) :
    entry.1 ∈ schemaNames rewrite := by
  simp only [schemaNames, List.mem_eraseDups, List.mem_append,
    List.mem_map]
  exact Or.inr ⟨entry, membership, rfl⟩

/-- Structural rewrite certificates are monotone along capture-free signature
extensions.  Scope and output-binding obligations are independent of the
ambient signature and are transported unchanged. -/
theorem Certificate.extend
    {source target : LanguageDef} {rewrite : RewriteRule}
    (certificate : Certificate source rewrite)
    (extension : ExtendsFor source target rewrite) :
    Certificate target rewrite := by
  refine {
    contextTypes := ?_
    leftDeclared := ?_
    rightDeclared := ?_
    premisesDeclared := ?_
    allPatternsScoped := certificate.allPatternsScoped
    fvarsAvoidConstructors := ?_
    bindersAvoidConstructors := ?_
    contextAvoidsConstructors := ?_
    rightBound := certificate.rightBound }
  · intro entry entryMembership name nameMembership
    rw [extension.typeNames]
    exact List.mem_append_left _
      (certificate.contextTypes entry entryMembership name nameMembership)
  · intro reference referenceMembership
    rw [extension.signatures]
    exact List.mem_append_left _
      (certificate.leftDeclared reference referenceMembership)
  · intro reference referenceMembership
    rw [extension.signatures]
    exact List.mem_append_left _
      (certificate.rightDeclared reference referenceMembership)
  · intro pattern patternMembership reference referenceMembership
    rw [extension.signatures]
    exact List.mem_append_left _
      (certificate.premisesDeclared pattern patternMembership reference
        referenceMembership)
  · intro name nameMembership
    rw [extension.labels]
    simp only [List.mem_append, not_or]
    exact ⟨certificate.fvarsAvoidConstructors name nameMembership,
      extension.avoidsSchema name
        (fvar_mem_schemaNames rewrite name nameMembership)⟩
  · intro name nameMembership
    rw [extension.labels]
    simp only [List.mem_append, not_or]
    exact ⟨certificate.bindersAvoidConstructors name nameMembership,
      extension.avoidsSchema name
        (binder_mem_schemaNames rewrite name nameMembership)⟩
  · intro entry entryMembership
    rw [extension.labels]
    simp only [List.mem_append, not_or]
    exact ⟨certificate.contextAvoidsConstructors entry entryMembership,
      extension.avoidsSchema entry.1
      (context_mem_schemaNames rewrite entry entryMembership)⟩

/-- A capture-free embedding of the finite signature support of one rewrite.
Unlike `ExtendsFor`, this relation permits the target presentation to reorder
or share declarations.  It is the appropriate boundary for validated gluing:
every sort and constructor used by the row must survive in the target, while
every schema name must remain distinct from every target constructor. -/
structure SignatureEmbeddingFor (source target : LanguageDef)
    (rewrite : RewriteRule) where
  typeNames : ∀ name ∈ source.typeNames, name ∈ target.typeNames
  signatures : ∀ signature ∈ constructorSignatures source,
    signature ∈ constructorSignatures target
  avoidsSchema : ∀ name ∈ schemaNames rewrite,
    name ∉ constructorLabels target

/-- Structural certificates transport through a capture-free signature
embedding.  This is the proof-oriented separate-compilation law: validation
may be performed against the row's finite support, then linked into a larger
presentation without re-running the global validator. -/
theorem Certificate.embed
    {source target : LanguageDef} {rewrite : RewriteRule}
    (certificate : Certificate source rewrite)
    (embedding : SignatureEmbeddingFor source target rewrite) :
    Certificate target rewrite := by
  refine {
    contextTypes := ?_
    leftDeclared := ?_
    rightDeclared := ?_
    premisesDeclared := ?_
    allPatternsScoped := certificate.allPatternsScoped
    fvarsAvoidConstructors := ?_
    bindersAvoidConstructors := ?_
    contextAvoidsConstructors := ?_
    rightBound := certificate.rightBound }
  · intro entry entryMembership name nameMembership
    exact embedding.typeNames name
      (certificate.contextTypes entry entryMembership name nameMembership)
  · intro reference referenceMembership
    exact embedding.signatures reference
      (certificate.leftDeclared reference referenceMembership)
  · intro reference referenceMembership
    exact embedding.signatures reference
      (certificate.rightDeclared reference referenceMembership)
  · intro pattern patternMembership reference referenceMembership
    exact embedding.signatures reference
      (certificate.premisesDeclared pattern patternMembership reference
        referenceMembership)
  · intro name nameMembership
    exact embedding.avoidsSchema name
      (fvar_mem_schemaNames rewrite name nameMembership)
  · intro name nameMembership
    exact embedding.avoidsSchema name
      (binder_mem_schemaNames rewrite name nameMembership)
  · intro entry entryMembership
    exact embedding.avoidsSchema entry.1
      (context_mem_schemaNames rewrite entry entryMembership)

#print axioms Certificate.extend
#print axioms Certificate.embed
#print axioms schemaNames_all_of_components

end Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension
