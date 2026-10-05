import Mettapedia.Languages.MM0.Kernel.DeclarationAdmission

/-!
# Preservation of admitted MM0 payloads under signature extension

Only preservation of existing lookups is required. New declarations may add
entries, but may not change the sorts, argument profiles or bodies on which
earlier checks depended. This is one-way preservation: an earlier refusal can
become accepted when a previously absent symbol is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

theorem Context.AdmitsBinder.extendSorts {before after : SortSignature}
    (preserves : ∀ index info, before index = some info → after index = some info)
    {context : Context} {binder : Binder} (admitted : AdmitsBinder before context binder) :
    AdmitsBinder after context binder := by
  cases admitted with
  | bound known allowed => exact .bound (preserves _ _ known) allowed
  | regular known dependencies => exact .regular (preserves _ _ known) dependencies

theorem Context.Extension.extendSorts {before after : SortSignature}
    (preserves : ∀ index info, before index = some info → after index = some info)
    {initial remaining : Context} (admitted : Extension before initial remaining) :
    Extension after initial remaining := by
  induction admitted with
  | nil initial => exact .nil initial
  | cons binder _ ih => exact .cons (binder.extendSorts preserves) ih

theorem Preterm.HasType.extendSignature {before after : TermSignature}
    (preserves : ∀ index declaration, before index = some declaration → after index = some declaration)
    {context remaining : Context} {expression : Preterm} {sort : Nat}
    (typed : HasType before context expression remaining sort) :
    HasType after context expression remaining sort := by
  induction typed with
  | var known => exact .var known
  | term known => exact .term (preserves _ _ known)
  | bound _ known ih => exact .bound ih known
  | regular _ _ ihFunction ihArgument => exact .regular ihFunction ihArgument

theorem Preterm.FitsBinder.extendSignature {before after : TermSignature}
    (preserves : ∀ index declaration, before index = some declaration → after index = some declaration)
    {context : Context} {expression : Preterm} {binder : Binder}
    (typed : FitsBinder before context expression binder) :
    FitsBinder after context expression binder := by
  cases typed with
  | bound known => exact .bound known
  | regular typed => exact .regular (typed.extendSignature preserves)

theorem Preterm.arguments_extendSignature {before after : TermSignature}
    (preserves : ∀ index declaration, before index = some declaration → after index = some declaration)
    {context formal : Context} {arguments : List Preterm}
    (typed : List.Forall₂ (FitsBinder before context) arguments formal) :
    List.Forall₂ (FitsBinder after context) arguments formal := by
  induction typed with
  | nil => exact .nil
  | cons head _ ih => exact .cons (head.extendSignature preserves) ih

theorem Preterm.FreeSpine.extendSignature {before after : TermSignature}
    (preserves : ∀ index declaration, before index = some declaration → after index = some declaration)
    {context : Context} {expression : Preterm} {arguments : List Preterm}
    {freeSets : List (Finset Nat)} {result : Finset Nat}
    (free : FreeSpine before context expression arguments freeSets result) :
    FreeSpine after context expression arguments freeSets result := by
  induction free with
  | var supported => exact .var supported
  | term known typed contributed returned =>
      exact .term (preserves _ _ known) (arguments_extendSignature preserves typed) contributed returned
  | app _ _ ihArgument ihFunction => exact .app ihArgument ihFunction

theorem Preterm.IsStatement.extendSignatures {beforeSorts afterSorts : SortSignature}
    {beforeTerms afterTerms : TermSignature}
    (sorts : ∀ index info, beforeSorts index = some info → afterSorts index = some info)
    (terms : ∀ index declaration, beforeTerms index = some declaration →
      afterTerms index = some declaration)
    {context : Context} {expression : Preterm}
    (statement : IsStatement beforeSorts beforeTerms context expression) :
    IsStatement afterSorts afterTerms context expression := by
  obtain ⟨sort, info, typed, known, provable⟩ := statement
  exact ⟨sort, info, typed.extendSignature terms, sorts _ _ known, provable⟩

theorem TermDecl.Admissible.extendSorts {before after : SortSignature}
    (preserves : ∀ index info, before index = some info → after index = some info)
    {declaration : TermDecl} (admitted : Admissible before declaration) :
    Admissible after declaration := by
  obtain ⟨info, known, notPure⟩ := admitted.result
  exact ⟨admitted.context.extendSorts preserves, ⟨info, preserves _ _ known, notPure⟩,
    admitted.dependencies⟩

theorem Definition.AdmissibleBody.extendSignatures {beforeSorts afterSorts : SortSignature}
    {beforeTerms afterTerms : TermSignature}
    (sorts : ∀ index info, beforeSorts index = some info → afterSorts index = some info)
    (terms : ∀ index declaration, beforeTerms index = some declaration →
      afterTerms index = some declaration)
    {declaration : TermDecl} {body : Body}
    (admitted : AdmissibleBody beforeSorts beforeTerms declaration body) :
    AdmissibleBody afterSorts afterTerms declaration body := by
  refine ⟨?_, admitted.typed.extendSignature terms, ?_⟩
  · intro sort member
    obtain ⟨info, known, notStrict, notFree⟩ := admitted.dummies sort member
    exact ⟨info, sorts _ _ known, notStrict, notFree⟩
  · obtain ⟨freeSet, computed, allowed⟩ := admitted.free
    exact ⟨freeSet, computed.extendSignature terms, allowed⟩

theorem TheoremDecl.Admissible.extendSignatures {beforeSorts afterSorts : SortSignature}
    {beforeTerms afterTerms : TermSignature}
    (sorts : ∀ index info, beforeSorts index = some info → afterSorts index = some info)
    (terms : ∀ index declaration, beforeTerms index = some declaration →
      afterTerms index = some declaration)
    {declaration : TheoremDecl} (admitted : Admissible beforeSorts beforeTerms declaration) :
    Admissible afterSorts afterTerms declaration :=
  ⟨admitted.context.extendSorts sorts,
    fun expression member => (admitted.hypotheses expression member).extendSignatures sorts terms,
    admitted.conclusion.extendSignatures sorts terms⟩

theorem Substitution.Admissible.extendSignature {before after : TermSignature}
    (preserves : ∀ index declaration, before index = some declaration → after index = some declaration)
    {formal target : Context} {arguments : List Preterm}
    (admitted : Admissible before formal target arguments) :
    Admissible after formal target arguments :=
  ⟨Preterm.arguments_extendSignature preserves admitted.typed, admitted.independent⟩

theorem TheoremDecl.Instantiates.extendSignature {before after : TermSignature}
    (preserves : ∀ index declaration, before index = some declaration → after index = some declaration)
    {target : Context} {declaration : TheoremDecl} {arguments : List Preterm}
    {instantiation : TheoremInstance} (instanceProof : Instantiates before target declaration arguments instantiation) :
    Instantiates after target declaration arguments instantiation :=
  ⟨instanceProof.admissible.extendSignature preserves, instanceProof.hypotheses, instanceProof.conclusion⟩

theorem Definition.Unfolds.extendSignatures {beforeTerms afterTerms : TermSignature}
    {beforeDefinitions afterDefinitions : Signature}
    (terms : ∀ index declaration, beforeTerms index = some declaration →
      afterTerms index = some declaration)
    (definitions : ∀ index body, beforeDefinitions index = some body → afterDefinitions index = some body)
    {target : Context} {symbol : Nat} {arguments : List Preterm} {images : List Nat} {result : Preterm}
    (unfolded : Unfolds beforeTerms beforeDefinitions target symbol arguments images result) :
    Unfolds afterTerms afterDefinitions target symbol arguments images result := by
  cases unfolded with
  | intro known defined typed fresh substituted =>
      exact .intro (terms _ _ known) (definitions _ _ defined)
        (Preterm.arguments_extendSignature terms typed) fresh substituted

end Mettapedia.Languages.MM0.Kernel
