import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentFragment
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveCompletedConversion
import Mettapedia.GSLT.Core.ContextualLadder

/-!
# Interpretation data on the admitted context domain

A supplied CwF is a semantic context algebra, not a selected mathematical
host. The attachment contains a map on independently formed contexts and raw
type, term and substitution relations on the existing native syntax. Admission, totality,
substitution stability and constructor agreement are separate predicates.

The structural constructor interface covers identity/composite substitutions,
context extension, weakening and the newest variable. Its strict comparison
of context objects is explicitly a candidate-class restriction. A CwF alone
supplies no Pi, Sigma, identity, universe or constant meanings, so none is
silently included in this interface.

On independently admitted endpoints, semantic conversion invariance is
equivalent to invariance under each completed parallel development. The proof
uses the entirely formed completed conversion relation, not subject expansion
along a raw conversion receipt. It transports any established meaning through
the actual mixed HOL-list/wire projection without choosing that meaning.

Changing a term's native type annotation is a separate requirement on the
raw relations. Under formed type-conversion invariance, that requirement is
equivalent to preserving meanings through the actual native `Typing.conv`
rule, including annotations formed at different cumulative levels.

The empty raw relations provide a negative control: substitution and
conversion stability alone do not interpret even an admitted universe head.
They are not a model. This leaf neither constructs a common native model nor
registers all six draft-critical families; TRACE-004 remains outside its scope.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentInterpretation

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.FormationSensitive
open SharedJudgmentFragment

universe u v w w'

/-- The interpretation domain retains the raw telescope and its independent
formation evidence. Unfinished program requests still use raw telescopes;
they do not acquire an arbitrary semantic context through this interface. -/
structure Context (assembly : Assembly) (n : Nat) where
  raw : Tower.Ctx n
  formed : ContextFormation assembly.rules raw

instance {assembly : Assembly} {n : Nat} :
    CoeOut (Context assembly n) (Tower.Ctx n) := ⟨Context.raw⟩

namespace Context

def nil {assembly : Assembly} : Context assembly 0 := ⟨.nil, .nil⟩

def snoc {assembly : Assembly} {n : Nat} (context : Context assembly n)
    (type : Tower.Tm n) (sortHead : Tower.Head)
    (typing : Typing assembly.rules context.raw type (.head sortHead))
    (universeWitness : assembly.rules.isUniverse sortHead) : Context assembly (n + 1) :=
  ⟨.snoc context.raw type, .snoc context.formed typing universeWitness⟩

def ofJudgment {assembly : Assembly} {n : Nat} {context : Tower.Ctx n}
    {term type : Tower.Tm n} (admitted : Judgment assembly.rules context term type) :
    Context assembly n := ⟨context, admitted.context⟩

@[ext] theorem ext {assembly : Assembly} {n : Nat} {first second : Context assembly n}
    (same : first.raw = second.raw) : first = second := by
  cases first
  cases second
  cases same
  rfl

end Context

/-- Raw relations on one assembly's actual terms in formed contexts. Their
index records which declaration/rule package the external admission laws
must use; no such law is stored here. -/
structure Data (assembly : Assembly) (C : Cwf.{u, v, w, w'}) where
  ctx : {n : Nat} → Context assembly n → C.Ctx
  ty : {n : Nat} → (context : Context assembly n) → Tower.Tm n → C.Ty (ctx context) → Prop
  term : {n : Nat} → (context : Context assembly n) → Tower.Tm n → Tower.Tm n →
    (type : C.Ty (ctx context)) → C.Tm (ctx context) type → Prop
  sub : {n m : Nat} → (source : Context assembly n) → (target : Context assembly m) →
    Sub Tower.Head n m → C.Sub (ctx target) (ctx source) → Prop

variable {assembly : Assembly} {C : Cwf.{u, v, w, w'}}

/-! ## Independent totality and substitution requirements -/

/-- Every actual admitted judgment has an interpreted type and term.
Constructor meaning and coherence are additional requirements, not
consequences of this existential totality statement alone. -/
def AdmittedTotal (interpretation : Data assembly C) : Prop :=
  ∀ (n : Nat) (context : Context assembly n) (term type : Tower.Tm n),
    Judgment assembly.rules context term type →
      ∃ semanticType : C.Ty (interpretation.ctx context),
        interpretation.ty context type semanticType ∧
        ∃ value : C.Tm (interpretation.ctx context) semanticType,
          interpretation.term context term type semanticType value

/-- Both native endpoints are independently formed. A componentwise typed
instantiation alone need not establish formation of its abstract source. -/
def AdmittedSubstitutionsTotal (interpretation : Data assembly C) : Prop :=
  ∀ (n m : Nat) (source : Context assembly n) (target : Context assembly m)
    (sigma : Sub Tower.Head n m),
    ContextFormation assembly.rules target.raw →
    FormationSensitive.CtxMor assembly.rules source target sigma →
      ∃ semantic : C.Sub (interpretation.ctx target) (interpretation.ctx source),
        interpretation.sub source target sigma semantic

def TypeSubstitutionStable (interpretation : Data assembly C) : Prop :=
  ∀ (n m : Nat) (source : Context assembly n) (target : Context assembly m)
    (sigma : Sub Tower.Head n m)
    (semantic : C.Sub (interpretation.ctx target) (interpretation.ctx source))
    (type : Tower.Tm n) (semanticType : C.Ty (interpretation.ctx source)),
    ContextFormation assembly.rules target.raw →
    FormationSensitive.CtxMor assembly.rules source target sigma →
    interpretation.sub source target sigma semantic →
    interpretation.ty source type semanticType →
      interpretation.ty target (subst sigma type) (C.tySub semanticType semantic)

def TermSubstitutionStable (interpretation : Data assembly C) : Prop :=
  ∀ (n m : Nat) (source : Context assembly n) (target : Context assembly m)
    (sigma : Sub Tower.Head n m)
    (semantic : C.Sub (interpretation.ctx target) (interpretation.ctx source))
    (term type : Tower.Tm n) (semanticType : C.Ty (interpretation.ctx source))
    (value : C.Tm (interpretation.ctx source) semanticType),
    ContextFormation assembly.rules target.raw →
    FormationSensitive.CtxMor assembly.rules source target sigma →
    Judgment assembly.rules source term type →
    interpretation.sub source target sigma semantic →
    interpretation.ty source type semanticType →
    interpretation.term source term type semanticType value →
      interpretation.term target (subst sigma term) (subst sigma type)
        (C.tySub semanticType semantic) (C.tmSub value semantic)

def SubstitutionStable (interpretation : Data assembly C) : Prop :=
  TypeSubstitutionStable interpretation ∧ TermSubstitutionStable interpretation

/-! ## Structural constructors available in the supplied CwF -/

/-- Transport of a context index uses the actual identity substitution. -/
def contextTransport {source target : C.Ctx} (equal : source = target) : C.Sub source target := by
  subst target
  exact C.idS source

def SubstitutionConstructors (interpretation : Data assembly C) : Prop :=
  (∀ (n : Nat) (context : Context assembly n), ContextFormation assembly.rules context.raw →
    interpretation.sub context context ids (C.idS (interpretation.ctx context))) ∧
  (∀ (n m k : Nat) (first : Context assembly n) (middle : Context assembly m) (last : Context assembly k)
    (sigma : Sub Tower.Head n m) (tau : Sub Tower.Head m k)
    (semanticSigma : C.Sub (interpretation.ctx middle) (interpretation.ctx first))
    (semanticTau : C.Sub (interpretation.ctx last) (interpretation.ctx middle)),
    interpretation.sub first middle sigma semanticSigma →
    interpretation.sub middle last tau semanticTau →
      interpretation.sub first last (subComp tau sigma) (C.compS semanticSigma semanticTau))

/-- This strict choice of semantic context representatives is an explicit
class restriction. General comparisons by context isomorphism are not
asserted to be strict or ruled out. -/
def StrictComprehension (interpretation : Data assembly C) : Prop :=
  ∀ (n : Nat) (context : Context assembly n) (type : Tower.Tm n) (sortHead : Tower.Head)
    (admitted : Judgment assembly.rules context type (.head sortHead))
    (universeWitness : assembly.rules.isUniverse sortHead),
      ∃ semanticType : C.Ty (interpretation.ctx context),
        interpretation.ty context type semanticType ∧
        interpretation.ctx (.snoc context type sortHead admitted.typing universeWitness) =
          C.ext (interpretation.ctx context) semanticType

/-- Weakening and the newest variable use the CwF's own `wk` and `vz`,
transported along the independently stated strict context comparison. -/
def WeakeningVariableConstructors (interpretation : Data assembly C) : Prop :=
  ∀ (n : Nat) (context : Context assembly n) (type : Tower.Tm n) (sortHead : Tower.Head)
    (admitted : Judgment assembly.rules context type (.head sortHead))
    (universeWitness : assembly.rules.isUniverse sortHead)
    (semanticType : C.Ty (interpretation.ctx context))
    (sameContext : interpretation.ctx
        (.snoc context type sortHead admitted.typing universeWitness) =
      C.ext (interpretation.ctx context) semanticType),
    interpretation.ty context type semanticType →
      let extended := context.snoc type sortHead admitted.typing universeWitness
      let along := contextTransport sameContext
      let weakenedType := C.tySub (C.tySub semanticType (C.wk semanticType)) along
      interpretation.sub context extended (renSub wk)
          (C.compS (C.wk semanticType) along) ∧
        interpretation.ty extended (Ctx.lookup (.snoc context.raw type) 0) weakenedType ∧
        interpretation.term extended (.var 0)
          (Ctx.lookup (.snoc context type) 0) weakenedType (C.tmSub (C.vz semanticType) along)

/-- Exactly the structural constructors above; no dependent type formers,
universe semantics, declaration interpretation or total model are included. -/
def StrictStructuralInterface (interpretation : Data assembly C) : Prop :=
  SubstitutionConstructors interpretation ∧ StrictComprehension interpretation ∧
    WeakeningVariableConstructors interpretation

/-! ## Conversion reduced to wholly admitted parallel developments -/

/-- Predicate invariance on the actual admitted carrier reduces to one
completed parallel development at a time. No raw intermediate is admitted
by reversing a step. -/
theorem invariant_iff_development
    (opacity : OpaqueRelatorExtension.Opacity assembly.declarations)
    {n : Nat} {context : Tower.Ctx n} {type : Tower.Tm n}
    (predicate : FormationSensitiveCompletedConversion.Admitted assembly.declarations context type →
      Prop) :
    (∀ left right, Conv assembly.rules.headEq left.val right.val assembly.rules.computation →
      (predicate left ↔ predicate right)) ↔
    (∀ left right, FormationSensitiveCompletedConversion.Development left right →
      (predicate left ↔ predicate right)) := by
  constructor
  · intro invariant left right developed
    exact invariant left right
      (FormationSensitiveCompletedConversion.conversion_sound opacity (.rel _ _ developed))
  · intro invariant left right converted
    have completed := FormationSensitiveCompletedConversion.conversion_complete
      opacity left right converted
    clear converted
    induction completed with
    | rel first last developed => exact invariant first last developed
    | refl _ => exact Iff.rfl
    | symm _ _ _ inductionHypothesis => exact inductionHypothesis.symm
    | trans _ _ _ _ _ first last => exact first.trans last

def TypeConversionInvariant (interpretation : Data assembly C) : Prop :=
  ∀ (n : Nat) (context : Context assembly n) (sortHead : Tower.Head)
    (left right : FormationSensitiveCompletedConversion.Admitted
      assembly.declarations context (.head sortHead))
    (semanticType : C.Ty (interpretation.ctx context)),
    assembly.rules.isUniverse sortHead →
    Conv assembly.rules.headEq left.val right.val assembly.rules.computation →
      (interpretation.ty context left.val semanticType ↔
        interpretation.ty context right.val semanticType)

def TypeDevelopmentInvariant (interpretation : Data assembly C) : Prop :=
  ∀ (n : Nat) (context : Context assembly n) (sortHead : Tower.Head)
    (left right : FormationSensitiveCompletedConversion.Admitted
      assembly.declarations context (.head sortHead))
    (semanticType : C.Ty (interpretation.ctx context)),
    assembly.rules.isUniverse sortHead →
    FormationSensitiveCompletedConversion.Development left right →
      (interpretation.ty context left.val semanticType ↔
        interpretation.ty context right.val semanticType)

def TermConversionInvariant (interpretation : Data assembly C) : Prop :=
  ∀ (n : Nat) (context : Context assembly n) (type : Tower.Tm n)
    (left right : FormationSensitiveCompletedConversion.Admitted assembly.declarations context type)
    (semanticType : C.Ty (interpretation.ctx context))
    (value : C.Tm (interpretation.ctx context) semanticType),
    Conv assembly.rules.headEq left.val right.val assembly.rules.computation →
      (interpretation.term context left.val type semanticType value ↔
        interpretation.term context right.val type semanticType value)

def TermDevelopmentInvariant (interpretation : Data assembly C) : Prop :=
  ∀ (n : Nat) (context : Context assembly n) (type : Tower.Tm n)
    (left right : FormationSensitiveCompletedConversion.Admitted assembly.declarations context type)
    (semanticType : C.Ty (interpretation.ctx context))
    (value : C.Tm (interpretation.ctx context) semanticType),
    FormationSensitiveCompletedConversion.Development left right →
      (interpretation.term context left.val type semanticType value ↔
        interpretation.term context right.val type semanticType value)

def ConversionInvariant (interpretation : Data assembly C) : Prop :=
  TypeConversionInvariant interpretation ∧ TermConversionInvariant interpretation

def DevelopmentInvariant (interpretation : Data assembly C) : Prop :=
  TypeDevelopmentInvariant interpretation ∧ TermDevelopmentInvariant interpretation

theorem type_conversion_invariant_iff_development_invariant
    (opacity : OpaqueRelatorExtension.Opacity assembly.declarations)
    (interpretation : Data assembly C) :
    TypeConversionInvariant interpretation ↔ TypeDevelopmentInvariant interpretation := by
  constructor
  · intro invariant n context sortHead left right semanticType universeWitness developed
    exact (invariant_iff_development opacity
      (fun term => interpretation.ty context term.val semanticType)).mp
        (fun first last => invariant n context sortHead first last semanticType universeWitness)
          left right developed
  · intro invariant n context sortHead left right semanticType universeWitness converted
    exact (invariant_iff_development opacity
      (fun term => interpretation.ty context term.val semanticType)).mpr
        (fun first last => invariant n context sortHead first last semanticType universeWitness)
          left right converted

theorem term_conversion_invariant_iff_development_invariant
    (opacity : OpaqueRelatorExtension.Opacity assembly.declarations)
    (interpretation : Data assembly C) :
    TermConversionInvariant interpretation ↔ TermDevelopmentInvariant interpretation := by
  constructor
  · intro invariant n context type left right semanticType value developed
    exact (invariant_iff_development opacity
      (fun term => interpretation.term context term.val type semanticType value)).mp
        (fun first last => invariant n context type first last semanticType value) left right developed
  · intro invariant n context type left right semanticType value converted
    exact (invariant_iff_development opacity
      (fun term => interpretation.term context term.val type semanticType value)).mpr
        (fun first last => invariant n context type first last semanticType value) left right converted

theorem conversion_invariant_iff_development_invariant
    (opacity : OpaqueRelatorExtension.Opacity assembly.declarations)
    (interpretation : Data assembly C) :
    ConversionInvariant interpretation ↔ DevelopmentInvariant interpretation :=
  and_congr (type_conversion_invariant_iff_development_invariant opacity interpretation)
    (term_conversion_invariant_iff_development_invariant opacity interpretation)

/-! ## Native type annotations require their own transport law -/

/-- Both judgments and both type meanings are independently supplied. This
law changes the native annotation of the same term; fixed-type conversion
invariance only changes the term while retaining its annotation. The same
semantic type and value are retained, as appropriate to this strict class. -/
def AnnotationTransport (interpretation : Data assembly C) : Prop :=
  ∀ (n : Nat) (context : Context assembly n) (term sourceType targetType : Tower.Tm n)
    (semanticType : C.Ty (interpretation.ctx context))
    (value : C.Tm (interpretation.ctx context) semanticType),
    Judgment assembly.rules context term sourceType →
    Judgment assembly.rules context term targetType →
    interpretation.ty context sourceType semanticType →
    interpretation.ty context targetType semanticType →
    Conv assembly.rules.headEq sourceType targetType assembly.rules.computation →
      (interpretation.term context term sourceType semanticType value ↔
        interpretation.term context term targetType semanticType value)

/-- The semantic obligation for exactly the native conversion rule: a
formed target annotation and native conversion must preserve the existing
type/value meanings. This does not assert totality or constructor meanings. -/
def ConversionRuleSound (interpretation : Data assembly C) : Prop :=
  ∀ (n : Nat) (context : Context assembly n) (term sourceType targetType : Tower.Tm n)
    (sortHead : Tower.Head) (semanticType : C.Ty (interpretation.ctx context))
    (value : C.Tm (interpretation.ctx context) semanticType),
    Judgment assembly.rules context term sourceType →
    Judgment assembly.rules context targetType (.head sortHead) →
    assembly.rules.isUniverse sortHead →
    Conv assembly.rules.headEq sourceType targetType assembly.rules.computation →
    interpretation.ty context sourceType semanticType →
    interpretation.term context term sourceType semanticType value →
      interpretation.ty context targetType semanticType ∧
        interpretation.term context term targetType semanticType value

/-- Native cumulativity places independently formed annotations on one
admitted carrier. No equality of their original displayed levels is needed. -/
theorem type_conversion_meaning_iff (interpretation : Data assembly C)
    (stable : TypeConversionInvariant interpretation)
    {n : Nat} {context : Context assembly n} {sourceType targetType : Tower.Tm n}
    {sourceSort targetSort : Tower.Head}
    (sourceFormed : Judgment assembly.rules context sourceType (.head sourceSort))
    (targetFormed : Judgment assembly.rules context targetType (.head targetSort))
    (sourceUniverse : assembly.rules.isUniverse sourceSort)
    (targetUniverse : assembly.rules.isUniverse targetSort)
    (converted : Conv assembly.rules.headEq sourceType targetType assembly.rules.computation)
    (semanticType : C.Ty (interpretation.ctx context)) :
    interpretation.ty context sourceType semanticType ↔
      interpretation.ty context targetType semanticType := by
  cases sourceUniverse with
  | sort sourceLevel =>
    cases targetUniverse with
    | sort targetLevel =>
      let left : FormationSensitiveCompletedConversion.Admitted assembly.declarations
          context.raw (sortTm (.max sourceLevel targetLevel)) :=
        ⟨sourceType, sourceFormed.context,
          .cumul sourceFormed.typing (fun _ => Nat.le_max_left _ _)⟩
      let right : FormationSensitiveCompletedConversion.Admitted assembly.declarations
          context.raw (sortTm (.max sourceLevel targetLevel)) :=
        ⟨targetType, targetFormed.context,
          .cumul targetFormed.typing (fun _ => Nat.le_max_right _ _)⟩
      exact stable n context (.sort (.max sourceLevel targetLevel))
        left right semanticType (.sort _) converted

/-- The exact native conversion rule supplies the target admission as well
as the independently required semantic meaning transport. -/
theorem interprets_typing_conv (interpretation : Data assembly C)
    (sound : ConversionRuleSound interpretation)
    {n : Nat} {context : Context assembly n} {term sourceType targetType : Tower.Tm n}
    {sortHead : Tower.Head}
    (admitted : Judgment assembly.rules context term sourceType)
    (targetFormed : Judgment assembly.rules context targetType (.head sortHead))
    (targetUniverse : assembly.rules.isUniverse sortHead)
    (converted : Conv assembly.rules.headEq sourceType targetType assembly.rules.computation)
    (semanticType : C.Ty (interpretation.ctx context))
    (value : C.Tm (interpretation.ctx context) semanticType)
    (typeMeaning : interpretation.ty context sourceType semanticType)
    (termMeaning : interpretation.term context term sourceType semanticType value) :
    Judgment assembly.rules context term targetType ∧
      interpretation.ty context targetType semanticType ∧
        interpretation.term context term targetType semanticType value :=
  ⟨⟨admitted.context, .conv admitted.typing targetFormed.typing targetUniverse converted⟩,
    sound n context term sourceType targetType sortHead semanticType value
      admitted targetFormed targetUniverse converted typeMeaning termMeaning⟩

/-- Regularity recovers each annotation's formation; cumulativity and the
completed-conversion theorem supply type-meaning agreement. The remaining
condition is precisely annotation transport, not fixed-type term invariance. -/
theorem conversion_rule_sound_iff_annotation_transport
    (opacity : OpaqueRelatorExtension.Opacity assembly.declarations)
    (interpretation : Data assembly C)
    (stable : TypeDevelopmentInvariant interpretation) :
    ConversionRuleSound interpretation ↔ AnnotationTransport interpretation := by
  constructor
  · intro sound n context term sourceType targetType semanticType value
      sourceAdmitted targetAdmitted sourceMeaning targetMeaning converted
    obtain ⟨sourceSort, sourceUniverse, sourceFormed⟩ :=
      sourceAdmitted.regularity OpaqueRelatorExtension.universes
    obtain ⟨targetSort, targetUniverse, targetFormed⟩ :=
      targetAdmitted.regularity OpaqueRelatorExtension.universes
    constructor
    · intro termMeaning
      exact (sound n context term sourceType targetType targetSort semanticType value
        sourceAdmitted targetFormed targetUniverse converted sourceMeaning termMeaning).2
    · intro termMeaning
      exact (sound n context term targetType sourceType sourceSort semanticType value
        targetAdmitted sourceFormed sourceUniverse converted.symm targetMeaning termMeaning).2
  · intro transport n context term sourceType targetType sortHead semanticType value
      admitted targetFormed targetUniverse converted typeMeaning termMeaning
    obtain ⟨sourceSort, sourceUniverse, sourceFormed⟩ :=
      admitted.regularity OpaqueRelatorExtension.universes
    have targetMeaning := (type_conversion_meaning_iff interpretation
      ((type_conversion_invariant_iff_development_invariant opacity interpretation).mpr stable)
      sourceFormed targetFormed sourceUniverse targetUniverse converted semanticType).mp typeMeaning
    have targetAdmitted : Judgment assembly.rules context term targetType :=
      ⟨admitted.context, .conv admitted.typing targetFormed.typing targetUniverse converted⟩
    exact ⟨targetMeaning, (transport n context term sourceType targetType semanticType value
      admitted targetAdmitted typeMeaning targetMeaning converted).mp termMeaning⟩

/-- Fixed-type conversion and the actual conversion rule are jointly
equivalent to formed completed-development invariance plus the independent
annotation requirement. This is a reduction of obligations, not a model. -/
theorem conversion_and_rule_sound_iff_completed_and_annotation
    (opacity : OpaqueRelatorExtension.Opacity assembly.declarations)
    (interpretation : Data assembly C) :
    (ConversionInvariant interpretation ∧ ConversionRuleSound interpretation) ↔
      (DevelopmentInvariant interpretation ∧ AnnotationTransport interpretation) := by
  constructor
  · rintro ⟨invariant, sound⟩
    have developed :=
      (conversion_invariant_iff_development_invariant opacity interpretation).mp invariant
    exact ⟨developed, (conversion_rule_sound_iff_annotation_transport opacity interpretation
      developed.1).mp sound⟩
  · rintro ⟨developed, transport⟩
    exact ⟨(conversion_invariant_iff_development_invariant opacity interpretation).mpr developed,
      (conversion_rule_sound_iff_annotation_transport opacity interpretation
        developed.1).mpr transport⟩

/-- Conversion can change both the term and its annotation when both end
judgments are independently admitted. The intermediate source term is
retyped by `Typing.conv`, not by subject expansion. -/
theorem transports_term_and_annotation
    (opacity : OpaqueRelatorExtension.Opacity assembly.declarations)
    (interpretation : Data assembly C) (stable : DevelopmentInvariant interpretation)
    (transport : AnnotationTransport interpretation)
    {n : Nat} {context : Context assembly n} {source target sourceType targetType : Tower.Tm n}
    (sourceAdmitted : Judgment assembly.rules context source sourceType)
    (targetAdmitted : Judgment assembly.rules context target targetType)
    (termConversion : Conv assembly.rules.headEq source target assembly.rules.computation)
    (typeConversion : Conv assembly.rules.headEq sourceType targetType assembly.rules.computation)
    (semanticType : C.Ty (interpretation.ctx context))
    (value : C.Tm (interpretation.ctx context) semanticType)
    (typeMeaning : interpretation.ty context sourceType semanticType)
    (termMeaning : interpretation.term context source sourceType semanticType value) :
    interpretation.ty context targetType semanticType ∧
      interpretation.term context target targetType semanticType value := by
  obtain ⟨targetSort, targetUniverse, targetFormed⟩ :=
    targetAdmitted.regularity OpaqueRelatorExtension.universes
  obtain ⟨sourceRetyped, targetMeaning, sourceMeaning⟩ := interprets_typing_conv interpretation
    ((conversion_rule_sound_iff_annotation_transport opacity interpretation stable.1).mpr transport)
    sourceAdmitted targetFormed targetUniverse typeConversion semanticType value typeMeaning termMeaning
  have termStable :=
    (term_conversion_invariant_iff_development_invariant opacity interpretation).mpr stable.2
  exact ⟨targetMeaning, (termStable n context targetType
    ⟨source, sourceRetyped⟩ ⟨target, targetAdmitted⟩ semanticType value termConversion).mp sourceMeaning⟩

theorem term_and_annotation_meaning_iff
    (opacity : OpaqueRelatorExtension.Opacity assembly.declarations)
    (interpretation : Data assembly C) (stable : DevelopmentInvariant interpretation)
    (transport : AnnotationTransport interpretation)
    {n : Nat} {context : Context assembly n} {source target sourceType targetType : Tower.Tm n}
    (sourceAdmitted : Judgment assembly.rules context source sourceType)
    (targetAdmitted : Judgment assembly.rules context target targetType)
    (termConversion : Conv assembly.rules.headEq source target assembly.rules.computation)
    (typeConversion : Conv assembly.rules.headEq sourceType targetType assembly.rules.computation)
    (semanticType : C.Ty (interpretation.ctx context))
    (value : C.Tm (interpretation.ctx context) semanticType) :
    (interpretation.ty context sourceType semanticType ∧
      interpretation.term context source sourceType semanticType value) ↔
    (interpretation.ty context targetType semanticType ∧
      interpretation.term context target targetType semanticType value) := by
  constructor
  · rintro ⟨typeMeaning, termMeaning⟩
    exact transports_term_and_annotation opacity interpretation stable transport
      sourceAdmitted targetAdmitted termConversion typeConversion semanticType value
      typeMeaning termMeaning
  · rintro ⟨typeMeaning, termMeaning⟩
    exact transports_term_and_annotation opacity interpretation stable transport
      targetAdmitted sourceAdmitted termConversion.symm typeConversion.symm semanticType value
      typeMeaning termMeaning

/-! ## The actual mixed projection transports an established meaning -/

/-- Both sides are independently admitted in the common assembly. The
semantic type and value are the same on both sides, not reconstructed by
decoding the projected native term. -/
theorem mixed_projection_meaning_iff (interpretation : Data common C)
    (stable : TermDevelopmentInvariant interpretation) (wire : NativeWireData.Wire)
    (semanticType : C.Ty (interpretation.ctx .nil))
    (value : C.Tm (interpretation.ctx .nil) semanticType) :
    interpretation.term .nil (.snd (HOLNativeRelatorCompatibility.mixedPayload wire))
        NativeWireData.dataType semanticType value ↔
      interpretation.term .nil (NativeWireData.encode wire)
        NativeWireData.dataType semanticType value := by
  obtain ⟨source, target, sourceEq, targetEq, completed⟩ :=
    FormationSensitiveCompletedConversion.Controls.mixed_projection wire
  have invariant := (term_conversion_invariant_iff_development_invariant
    HOLNativeRelatorCompatibility.opacity interpretation).mpr stable
  have agrees := invariant 0 .nil NativeWireData.dataType source target semanticType value
    (FormationSensitiveCompletedConversion.conversion_sound
      HOLNativeRelatorCompatibility.opacity completed)
  simpa only [sourceEq, targetEq] using agrees

/-- An existing meaning of the wire is transported to the newly formed
HOL-list/wire projection. Neither totality nor that wire meaning is assumed
to follow from conversion stability. -/
theorem mixed_projection_transports_meaning (interpretation : Data common C)
    (stable : TermDevelopmentInvariant interpretation) (wire : NativeWireData.Wire)
    (semanticType : C.Ty (interpretation.ctx .nil))
    (value : C.Tm (interpretation.ctx .nil) semanticType)
    (typeMeaning : interpretation.ty .nil NativeWireData.dataType semanticType)
    (wireMeaning : interpretation.term .nil (NativeWireData.encode wire)
      NativeWireData.dataType semanticType value) :
    interpretation.ty .nil NativeWireData.dataType semanticType ∧
      interpretation.term .nil (.snd (HOLNativeRelatorCompatibility.mixedPayload wire))
        NativeWireData.dataType semanticType value :=
  ⟨typeMeaning, (mixed_projection_meaning_iff interpretation stable wire semanticType value).mpr
    wireMeaning⟩

/-! ## Genuine type conversion in the common HOL/wire package -/

namespace Controls

/-- The existing native beta expansion, applied to the actual declared
wire type. It is not a new type former or a semantic interpretation. -/
def betaDataType {n : Nat} : Tower.Tm n :=
  FormationSensitiveCompletedRelatorPreservation.Examples.betaCopy NativeWireData.dataType

theorem beta_data_type_formed {n : Nat} (context : Tower.Ctx n) :
    Typing common.rules context betaDataType (sortTm Tower.zero) := by
  have sortFormed : Typing common.rules context (sortTm Tower.zero)
      (sortTm (.succ Tower.zero)) := .headType (.sort Tower.zero)
  have function : Typing common.rules context (.lam (.var 0))
      (.pi (sortTm Tower.zero) (sortTm Tower.zero)) := by
    apply Typing.lamIntro (u := .sort (.max (.succ Tower.zero) (.succ Tower.zero)))
    · exact .piForm sortFormed (.sort _) (.headType (.sort Tower.zero))
        (.sort _) (.sorts _ _)
    · exact .sort _
    · exact .var 0
  simpa only [betaDataType, FormationSensitiveCompletedRelatorPreservation.Examples.betaCopy,
    sortTm, inst0, subst] using
      Typing.appElim function (HOLNativeRelatorCompatibility.wire_typing
        (NativeWireData.dataType_formed context))

theorem beta_data_type_converts {n : Nat} :
    Conv common.rules.headEq (betaDataType : Tower.Tm n)
      NativeWireData.dataType common.rules.computation :=
  Declaration.Conv.includeSignature NativeIndexedFamilies.IntrinsicRelator.rules
    HOLNativeRelatorCompatibility.signature
    (FormationSensitiveCompletedRelatorPreservation.Examples.betaCopy_converts
      NativeWireData.dataType)

theorem beta_data_type_ne {n : Nat} :
    (betaDataType : Tower.Tm n) ≠ NativeWireData.dataType := by
  intro equal
  cases equal

theorem wire_beta_admitted (wire : NativeWireData.Wire) :
    Judgment common.rules .nil (NativeWireData.encode wire) betaDataType :=
  ⟨.nil, .conv (HOLNativeRelatorCompatibility.mixed_projection_admitted wire).typing
    (beta_data_type_formed .nil) (.sort Tower.zero) beta_data_type_converts.symm⟩

theorem mixed_projection_beta_admitted (wire : NativeWireData.Wire) :
    Judgment common.rules .nil (.snd (HOLNativeRelatorCompatibility.mixedPayload wire))
      betaDataType :=
  ⟨.nil, .conv (.sndElim (HOLNativeRelatorCompatibility.mixed_payload_typed .nil wire))
    (beta_data_type_formed .nil) (.sort Tower.zero) beta_data_type_converts.symm⟩

end Controls

/-- Both terms and both type annotations are actually admitted. This
transports the wire's existing meaning to the mixed projection at a distinct
beta-expanded annotation, with no new semantic type or value chosen. -/
theorem mixed_projection_across_annotation (interpretation : Data common C)
    (stable : DevelopmentInvariant interpretation) (transport : AnnotationTransport interpretation)
    (wire : NativeWireData.Wire) (semanticType : C.Ty (interpretation.ctx .nil))
    (value : C.Tm (interpretation.ctx .nil) semanticType) :
    (interpretation.ty .nil NativeWireData.dataType semanticType ∧
      interpretation.term .nil (NativeWireData.encode wire)
        NativeWireData.dataType semanticType value) ↔
    (interpretation.ty .nil Controls.betaDataType semanticType ∧
      interpretation.term .nil (.snd (HOLNativeRelatorCompatibility.mixedPayload wire))
        Controls.betaDataType semanticType value) := by
  obtain ⟨source, target, sourceEq, targetEq, completed⟩ :=
    FormationSensitiveCompletedConversion.Controls.mixed_projection wire
  have converted := FormationSensitiveCompletedConversion.conversion_sound
    HOLNativeRelatorCompatibility.opacity completed
  rw [sourceEq, targetEq] at converted
  exact term_and_annotation_meaning_iff HOLNativeRelatorCompatibility.opacity
    interpretation stable transport (context := .nil)
    (HOLNativeRelatorCompatibility.mixed_projection_admitted wire)
    (Controls.mixed_projection_beta_admitted wire) converted.symm
    Controls.beta_data_type_converts.symm semanticType value

/-! ## Fixed-type invariance does not transport native annotations -/

/-- A deliberately annotation-sensitive raw relation, not a model. It
retains a supplied semantic type/value but accepts only the literal native
Data annotation. Its type relation and fixed-annotation term relation cannot
detect conversion of the native term. Substitution/totality are not claimed. -/
def annotationSensitiveRaw (context : C.Ctx) (semanticType : C.Ty context)
    (value : C.Tm context semanticType) : Data common C where
  ctx _ := context
  ty _ _ type := type = semanticType
  term _ _ type _ meaning := type = NativeWireData.dataType ∧ HEq meaning value
  sub _ _ _ _ := False

theorem annotation_sensitive_conversion_invariant (context : C.Ctx)
    (semanticType : C.Ty context) (value : C.Tm context semanticType) :
    ConversionInvariant (annotationSensitiveRaw context semanticType value) := by
  constructor
  · intro _ _ _ _ _ _ _ _
    exact Iff.rfl
  · intro _ _ _ _ _ _ _ _
    exact Iff.rfl

theorem annotation_sensitive_wire_meaning (context : C.Ctx)
    (semanticType : C.Ty context) (value : C.Tm context semanticType)
    (wire : NativeWireData.Wire) :
    let interpretation := annotationSensitiveRaw context semanticType value
    interpretation.ty .nil NativeWireData.dataType semanticType ∧
      interpretation.term .nil (NativeWireData.encode wire)
        NativeWireData.dataType semanticType value :=
  ⟨rfl, rfl, HEq.rfl⟩

/-- The rejected annotation is a genuinely formed beta expansion. The
same nonempty wire judgment is admitted at both annotations, and both raw
type meanings hold; only the independent annotation law fails. -/
theorem annotation_sensitive_not_transport (context : C.Ctx)
    (semanticType : C.Ty context) (value : C.Tm context semanticType)
    (wire : NativeWireData.Wire) :
    ¬ AnnotationTransport (annotationSensitiveRaw context semanticType value) := by
  intro transport
  have changed := (transport 0 .nil (NativeWireData.encode wire)
    NativeWireData.dataType Controls.betaDataType semanticType value
    (HOLNativeRelatorCompatibility.mixed_projection_admitted wire)
    (Controls.wire_beta_admitted wire) rfl rfl Controls.beta_data_type_converts.symm).mp
      ⟨rfl, HEq.rfl⟩
  exact Controls.beta_data_type_ne changed.1

theorem fixed_type_invariance_does_not_imply_annotation_transport (context : C.Ctx)
    (semanticType : C.Ty context) (value : C.Tm context semanticType)
    (wire : NativeWireData.Wire) :
    ConversionInvariant (annotationSensitiveRaw context semanticType value) ∧
      ¬ AnnotationTransport (annotationSensitiveRaw context semanticType value) ∧
      ¬ ConversionRuleSound (annotationSensitiveRaw context semanticType value) := by
  have invariant := annotation_sensitive_conversion_invariant context semanticType value
  have notTransport := annotation_sensitive_not_transport context semanticType value wire
  refine ⟨invariant, notTransport, ?_⟩
  intro sound
  exact notTransport ((conversion_rule_sound_iff_annotation_transport
    HOLNativeRelatorCompatibility.opacity _
    ((conversion_invariant_iff_development_invariant HOLNativeRelatorCompatibility.opacity _).mp
      invariant).1).mp sound)

/-- A concrete nonempty instance of the raw-relation control in the
existing set-families CwF. The two-valued section supplies a real semantic
value; this raw relation is still not asserted to be a native model. -/
theorem concrete_annotation_boundary :
    let interpretation := annotationSensitiveRaw (C := familiesCwf)
      Bool (fun _ => Nat) (fun flag : Bool => if flag then 7 else 2)
    interpretation.term .nil (NativeWireData.encode (.natural 7))
        NativeWireData.dataType (fun _ => Nat) (fun flag : Bool => if flag then 7 else 2) ∧
      ConversionInvariant interpretation ∧ ¬ AnnotationTransport interpretation := by
  exact ⟨(annotation_sensitive_wire_meaning (C := familiesCwf)
      Bool (fun _ => Nat) (fun flag : Bool => if flag then 7 else 2) (.natural 7)).2,
    annotation_sensitive_conversion_invariant _ _ _,
    annotation_sensitive_not_transport _ _ _ (.natural 7)⟩

/-! ## Stability does not imply totality: empty raw relations, not a model -/

def emptyRaw (assembly : Assembly) (C : Cwf.{u, v, w, w'}) (context : C.Ctx) :
    Data assembly C where
  ctx _ := context
  ty _ _ _ := False
  term _ _ _ _ _ := False
  sub _ _ _ _ := False

theorem empty_raw_substitution_stable (context : C.Ctx) :
    SubstitutionStable (emptyRaw assembly C context) := by
  constructor
  · intro _ _ _ _ _ _ _ _ _ _ represented
    exact represented.elim
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ represented
    exact represented.elim

theorem empty_raw_conversion_invariant (context : C.Ctx) :
    ConversionInvariant (emptyRaw assembly C context) := by
  constructor
  · intro _ _ _ _ _ _ _ _
    exact Iff.rfl
  · intro _ _ _ _ _ _ _ _
    exact Iff.rfl

/-- The counterexample uses an actual admitted native universe head, not an
empty source language or a made-up Boolean authorization table. -/
theorem empty_raw_not_admitted_total (context : C.Ctx) :
    ¬ AdmittedTotal (emptyRaw assembly C context) := by
  intro total
  have admitted : Judgment assembly.rules .nil (sortTm Tower.zero)
      (sortTm (.succ Tower.zero)) :=
    ⟨.nil, .headType (Tower.HeadTyping.sort Tower.zero)⟩
  obtain ⟨_, typeMeaning, _⟩ := total 0 .nil _ _ admitted
  exact typeMeaning.elim

theorem stability_does_not_imply_totality (context : C.Ctx) :
    SubstitutionStable (emptyRaw assembly C context) ∧
      ConversionInvariant (emptyRaw assembly C context) ∧
      ¬ AdmittedTotal (emptyRaw assembly C context) :=
  ⟨empty_raw_substitution_stable context, empty_raw_conversion_invariant context,
    empty_raw_not_admitted_total context⟩

#print axioms invariant_iff_development
#print axioms conversion_invariant_iff_development_invariant
#print axioms type_conversion_meaning_iff
#print axioms interprets_typing_conv
#print axioms conversion_rule_sound_iff_annotation_transport
#print axioms conversion_and_rule_sound_iff_completed_and_annotation
#print axioms transports_term_and_annotation
#print axioms term_and_annotation_meaning_iff
#print axioms mixed_projection_meaning_iff
#print axioms mixed_projection_transports_meaning
#print axioms mixed_projection_across_annotation
#print axioms fixed_type_invariance_does_not_imply_annotation_transport
#print axioms concrete_annotation_boundary
#print axioms stability_does_not_imply_totality

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentInterpretation
