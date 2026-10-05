import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.AccountedGeneratedReadout

/-!
# Closed admitted origins in the source account family

A checked closed source origin supplies both a complete source semantic value
and its actual canonical literal key. Ordered words of such origins map into
the existing source-indexed account monoids and into the atomic signature
interpretation. The maps are defined on admitted origins; no arbitrary key
tree is assigned an invented source value.

Closed insertion uses the source clone's simultaneous substitution. Its
stability supports account actions beneath arbitrary target environments,
including marked values. The action here is used only at the process sort.
Open origins and generated mixed-sort contexts require a further comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ClosedOriginAccountInterpretation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open ActivationGenerated
open AccountedGeneratedReadout

/-- An actual closed intrinsic value with the existing reflective admission check. -/
structure Origin where
  term : Term sig [] Srt.pr
  safe : intrinsicQuoteSafe 0 term = true

abbrev OriginWord := FreeMonoid Origin

def admitted (origin : Origin) : rhoCIGSLT.CanonicalCarrier :=
  closedSource origin.term origin.safe

def key (origin : Origin) : AtomicSignatureInterpretation.KeyTree :=
  AtomicSignatureInterpretation.keyOfNat
    (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
      (rhoCIGSLT.canonicalKey (admitted origin)).val.val)

def literalWord : OriginWord →* AtomicSignatureInterpretation.Account := FreeMonoid.map key

def authority (origin : Origin) := Commitments.authority (admitted origin)

theorem authority_annotation (origin : Origin) :
    AtomicSignatureInterpretation.readSignature?
      (AtomicSignatureInterpretation.canonical rhoCIGSLT (admitted origin)) =
        some (literalWord (FreeMonoid.of origin)) := by
  simpa only [literalWord, FreeMonoid.map_of, key, AtomicSignatureInterpretation.canonical] using
    AtomicSignatureInterpretation.readSignature_commitLiteral
      (rhoCIGSLT.canonicalKey (admitted origin)).val.val

theorem authority_positive (origin : Origin) : (authority origin).val.RuntimeValid :=
  Commitments.positive_authority _

theorem authority_decoded (origin : Origin) :
    signature? (AtomicSignatureInterpretation.canonical rhoCIGSLT (admitted origin)) =
      some (authority origin) := Commitments.canonical_decoded _

noncomputable def sourceClass (origin : Origin) : source.substitution.Carrier [] Srt.pr :=
  accounted.observed.hom.raw.map (program origin.term)

noncomputable def closedEnvironment (Γ : Ctx sig) :
    Environment sig source.substitution.Carrier [] Γ := fun _ position => nomatch position

/-- The full source value is inserted by the existing clone, independently of its key. -/
noncomputable def sourceAtom (Γ : Ctx sig) (origin : Origin) :
    source.substitution.Carrier Γ Srt.pr :=
  source.substitution.substitute (closedEnvironment Γ) (sourceClass origin)

noncomputable def sourceWord (Γ : Ctx sig) :
    OriginWord →* SourceAccountSubstitution.Account source Srt.pr Γ :=
  FreeMonoid.map (sourceAtom Γ)

theorem sourceClass_key (origin : Origin) :
    encodeEquationClass (sourceClass origin) =
      (rhoCIGSLT.canonicalKey (admitted origin)).val.val := by
  rw [sourceClass, program_observation, encodeEquationClass_mk]
  exact (closedSource_key origin.term origin.safe).symm

/-- Source equality implies equality of the computed literal key, without a converse assumption. -/
theorem sourceClass_eq_key {first second : Origin}
    (same : sourceClass first = sourceClass second) : key first = key second := by
  have observed := congrArg encodeEquationClass same
  rw [sourceClass_key, sourceClass_key] at observed
  exact congrArg (fun pattern => AtomicSignatureInterpretation.keyOfNat
    (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode pattern)) observed

theorem sourceAtom_empty (origin : Origin) : sourceAtom [] origin = sourceClass origin := by
  unfold sourceAtom
  have empty_identity : closedEnvironment [] =
      (fun _ position => source.substitution.injectVar position) := by
    funext sort position
    nomatch position
  rw [empty_identity, source.substitution.substitute_identity]

/-- Any genuine source substitution fixes the inserted closed source atom. -/
theorem sourceAtom_substitute {Γ Δ : Ctx sig}
    (env : Environment sig source.substitution.Carrier Γ Δ) (origin : Origin) :
    source.substitution.substitute env (sourceAtom Γ origin) = sourceAtom Δ origin := by
  unfold sourceAtom
  rw [source.substitution.substitute_comp]
  congr 1
  funext sort position
  nomatch position

theorem sourceWord_substitute {Γ Δ : Ctx sig}
    (env : Environment sig source.substitution.Carrier Γ Δ) :
    (SourceAccountSubstitution.substitute source Srt.pr env).comp (sourceWord Γ) =
      sourceWord Δ := by
  apply FreeMonoid.hom_eq
  intro origin
  change FreeMonoid.of (source.substitution.substitute env (sourceAtom Γ origin)) =
    FreeMonoid.of (sourceAtom Δ origin)
  exact congrArg FreeMonoid.of (sourceAtom_substitute env origin)

theorem sourceWord_length (Γ : Ctx sig) (word : OriginWord) :
    (sourceWord Γ word).length = word.length := List.length_map _

theorem sourceWord_atom_nonunit (Γ : Ctx sig) (origin : Origin) :
    sourceWord Γ (FreeMonoid.of origin) ≠ 1 := by
  rw [sourceWord, FreeMonoid.map_of]
  exact FreeMonoid.of_ne_one _

theorem literalWord_length (word : OriginWord) :
    (literalWord word).length = word.length := List.length_map _

/-- Apply the origin-indexed account to a full process value in the actual free model. -/
noncomputable def annotate {Γ : Ctx sig} (word : OriginWord)
    (value : accounted.observed.left.substitution.Carrier Γ Srt.pr) :=
  accounted.act (sourceWord Γ word) value

theorem annotate_one {Γ : Ctx sig}
    (value : accounted.observed.left.substitution.Carrier Γ Srt.pr) :
    annotate 1 value = value := by
  unfold annotate
  rw [map_one]
  exact accounted.act_one value

theorem annotate_mul {Γ : Ctx sig} (first second : OriginWord)
    (value : accounted.observed.left.substitution.Carrier Γ Srt.pr) :
    annotate (first * second) value = annotate first (annotate second value) := by
  unfold annotate
  rw [map_mul]
  exact accounted.act_mul _ _ value

theorem annotate_observation {Γ : Ctx sig} (word : OriginWord)
    (value : accounted.observed.left.substitution.Carrier Γ Srt.pr) :
    accounted.observed.hom.raw.map (annotate word value) =
      accounted.observed.hom.raw.map value := accounted.observe_act _ _

/-- Substitution keeps every marked target value; closed account atoms need no erasure. -/
theorem annotate_substitute {Γ Δ : Ctx sig}
    (env : Environment sig accounted.observed.left.substitution.Carrier Γ Δ)
    (word : OriginWord) (value : accounted.observed.left.substitution.Carrier Γ Srt.pr) :
    accounted.observed.left.substitution.substitute env (annotate word value) =
      annotate word (accounted.observed.left.substitution.substitute env value) := by
  unfold annotate
  rw [accounted.act_substitute]
  have stable := congrArg (fun hom => hom word)
    (sourceWord_substitute (fun sort position => accounted.observed.hom.raw.map (env sort position)))
  change SourceAccountSubstitution.substitute source Srt.pr
    (fun sort position => accounted.observed.hom.raw.map (env sort position))
      (sourceWord Γ word) = sourceWord Δ word at stable
  rw [stable]

def readoutOrigin {fuel : Nat} {origin : Pattern} {result : Readout 0 origin}
    (found : readout? fuel 0 origin = some result) : Origin :=
  ⟨result.intrinsic, readout_quoteSafe found⟩

theorem readoutOrigin_key {fuel : Nat} {origin : Pattern} {result : Readout 0 origin}
    (found : readout? fuel 0 origin = some result) :
    key (readoutOrigin found) = AtomicSignatureInterpretation.keyOfNat
      (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode (canonicalize (eraseGenerated origin))) := by
  unfold key admitted readoutOrigin
  rw [readout_source_key found]

theorem readoutOrigin_authority {fuel : Nat} {origin : Pattern} {result : Readout 0 origin}
    (found : readout? fuel 0 origin = some result) :
    authority (readoutOrigin found) = readoutAuthority found := rfl

def zeroOrigin : Origin := ⟨nilP, by decide +kernel⟩

def inputOrigin : Origin := ⟨AccountBindingAlgebra.RhoSourceComparison.input, by decide +kernel⟩

theorem zero_atom_nonunit :
    literalWord (FreeMonoid.of zeroOrigin) ≠ 1 := by
  rw [literalWord, FreeMonoid.map_of]
  exact AtomicSignatureInterpretation.committed_account_nonunit _

/-- Two emissions remain two positions even when they carry the same literal key. -/
theorem repeated_origin_length :
    (literalWord (FreeMonoid.of zeroOrigin * FreeMonoid.of zeroOrigin)).length = 2 := by
  rw [literalWord_length]
  rfl

theorem repeated_origin_not_singleton :
    literalWord (FreeMonoid.of zeroOrigin * FreeMonoid.of zeroOrigin) ≠
      literalWord (FreeMonoid.of zeroOrigin) := by
  intro same
  have lengths := congrArg FreeMonoid.length same
  rw [literalWord_length, literalWord_length] at lengths
  cases lengths

theorem input_origin_key_distinct : key inputOrigin ≠ key zeroOrigin := by
  intro same
  have patterns := Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode_injective (AtomicSignatureInterpretation.keyOfNat_injective same)
  have different : canonicalize (encodeTerm AccountBindingAlgebra.RhoSourceComparison.input) ≠
      canonicalize (encodeTerm nilP) := by decide +kernel
  exact different patterns

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ClosedOriginAccountInterpretation
