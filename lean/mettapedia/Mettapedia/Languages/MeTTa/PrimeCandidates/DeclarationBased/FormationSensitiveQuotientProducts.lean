import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientComprehensionSyntax
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeQuotientCwfControls

/-!
# Actual native products and sums in the formed conversion CwF

The operations below construct the native Pi, Sigma, lambda, application,
pair and projection syntax, checked by the formation-sensitive rules. Their
semantic values are the existing conversion classes. Chosen representatives
are compared through actual admitted comprehension maps, never identified
with an original source term. Formation remains valid at all supplied
native levels and under arbitrary declared signatures extending the native
relator rules; opacity is not needed for formation or beta.

This constructs product and sum structure in this particular syntactic CwF.
It does not assert a full native interpretation, a semantic eta principle,
normalization, equality reflection, K/UIP or a selected host.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientProducts

open _root_.CategoryTheory FormationSensitive QuotientComprehensionSyntax
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.GSLT.Core.ContextualLadder.TypeOver (extensionSubstitution)

noncomputable section

variable {signature : Declaration.Signature Tower.Head}

abbrev NativeContext (signature : Declaration.Signature Tower.Head) :=
  Context (OpaqueRelatorExtension.rules signature)

abbrev NativeQContext (signature : Declaration.Signature Tower.Head) :=
  QuotientCwf.QContext (OpaqueRelatorExtension.rules signature)

def universeLevel : (head : Tower.Head) → Tower.IsUniverse head → LevelExpr
  | .sort level, _ => level
  | .legacyGround, member => nomatch member

theorem universeLevel_spec (head : Tower.Head) (member : Tower.IsUniverse head) :
    head = .sort (universeLevel head member) := by
  cases member
  rfl

def nativeLevel {context : NativeContext signature} (type : TypeOver context) : LevelExpr :=
  universeLevel type.level type.universeWitness

theorem nativeLevel_spec {context : NativeContext signature} (type : TypeOver context) :
    type.level = .sort (nativeLevel type) := universeLevel_spec _ _

def nativePi {context : NativeContext signature} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) : TypeOver context where
  code := .pi domain.code codomain.code
  level := .sort (.max (nativeLevel domain) (nativeLevel codomain))
  universeWitness := .sort _
  formed := .piForm domain.formed domain.universeWitness codomain.formed
    codomain.universeWitness (by
      change Tower.Join domain.level codomain.level _
      rw [nativeLevel_spec domain, nativeLevel_spec codomain]
      exact .sorts _ _)

def nativeSigma {context : NativeContext signature} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) : TypeOver context where
  code := .sigma domain.code codomain.code
  level := .sort (.max (nativeLevel domain) (nativeLevel codomain))
  universeWitness := .sort _
  formed := .sigmaForm domain.formed domain.universeWitness codomain.formed
    codomain.universeWitness (by
      change Tower.Join domain.level codomain.level _
      rw [nativeLevel_spec domain, nativeLevel_spec codomain]
      exact .sorts _ _)

def nativeLambda {context : NativeContext signature} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (body : Term (extend context domain) codomain) :
    Term context (nativePi domain codomain) :=
  ⟨.lam body.code, .lamIntro (nativePi domain codomain).formed
    (nativePi domain codomain).universeWitness body.typed⟩

def nativeApplication {context : NativeContext signature} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (function : Term context (nativePi domain codomain)) (argument : Term context domain) :
    Term context (codomain.reindex (nativeSection argument)) where
  code := .app function.code argument.code
  typed := by
    change Typing _ _ _ (subst (nativeSection argument).substitution codomain.code)
    rw [nativeSection_substitution]
    exact .appElim function.typed argument.typed

def nativePair {context : NativeContext signature} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (first : Term context domain)
    (second : Term context (codomain.reindex (nativeSection first))) :
    Term context (nativeSigma domain codomain) where
  code := .pair first.code second.code
  typed := .pairIntro (nativeSigma domain codomain).formed
    (nativeSigma domain codomain).universeWitness first.typed (by
      have typed := second.typed
      change Typing _ _ _ (subst (nativeSection first).substitution codomain.code) at typed
      rw [nativeSection_substitution] at typed
      exact typed)

def nativeFirst {context : NativeContext signature} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (value : Term context (nativeSigma domain codomain)) : Term context domain :=
  ⟨.fst value.code, .fstElim value.typed⟩

def nativeSecond {context : NativeContext signature} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (value : Term context (nativeSigma domain codomain)) :
    Term context (codomain.reindex (nativeSection (nativeFirst value))) where
  code := .snd value.code
  typed := by
    change Typing _ _ _ (subst (nativeSection (nativeFirst value)).substitution codomain.code)
    rw [nativeSection_substitution]
    exact .sndElim value.typed

def pi {context : NativeQContext signature} (domain : QuotientCwf.Ty context)
    (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)) : QuotientCwf.Ty context :=
  QType.mk (nativePi (QuotientCwf.typeRepresentative domain)
    (QuotientCwf.typeRepresentative codomain))

def sigma {context : NativeQContext signature} (domain : QuotientCwf.Ty context)
    (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)) : QuotientCwf.Ty context :=
  QType.mk (nativeSigma (QuotientCwf.typeRepresentative domain)
    (QuotientCwf.typeRepresentative codomain))

def lam {context : NativeQContext signature} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (body : QuotientCwf.Tm (QuotientCwf.ext context domain) codomain) :
    QuotientCwf.Tm context (pi domain codomain) :=
  ⟨QTerm.mk (nativeLambda (chosenTerm body)), rfl⟩

def app {context : NativeQContext signature} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (function : QuotientCwf.Tm context (pi domain codomain))
    (argument : QuotientCwf.Tm context domain) :
    QuotientCwf.Tm context (QuotientCwf.tySub codomain
      (selfExtend (QuotientCwf.cwf (OpaqueRelatorExtension.rules signature)) argument)) :=
  ⟨QTerm.mk (nativeApplication
    (QuotientCwf.termRepresentative _ function.val function.property) (chosenTerm argument)),
    type_at_argument codomain argument⟩

def pair {context : NativeQContext signature} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (first : QuotientCwf.Tm context domain)
    (second : QuotientCwf.Tm context (QuotientCwf.tySub codomain
      (selfExtend (QuotientCwf.cwf (OpaqueRelatorExtension.rules signature)) first))) :
    QuotientCwf.Tm context (sigma domain codomain) :=
  ⟨QTerm.mk (nativePair (chosenTerm first)
    (QuotientCwf.termRepresentative _ second.val
      (second.property.trans (type_at_argument codomain first).symm))), rfl⟩

def fst {context : NativeQContext signature} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (value : QuotientCwf.Tm context (sigma domain codomain)) : QuotientCwf.Tm context domain :=
  ⟨QTerm.mk (nativeFirst (QuotientCwf.termRepresentative _ value.val value.property)),
    QuotientCwf.typeRepresentative_class domain⟩

def snd {context : NativeQContext signature} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (value : QuotientCwf.Tm context (sigma domain codomain)) :
    QuotientCwf.Tm context (QuotientCwf.tySub codomain
      (selfExtend (QuotientCwf.cwf (OpaqueRelatorExtension.rules signature)) (fst value))) :=
  ⟨QTerm.mk (nativeSecond (QuotientCwf.termRepresentative _ value.val value.property)),
    type_at_argument_of_class codomain (fst value)
      (nativeFirst (QuotientCwf.termRepresentative _ value.val value.property)) rfl⟩

def products (signature : Declaration.Signature Tower.Head) :
    PiOperations (QuotientCwf.cwf (OpaqueRelatorExtension.rules signature)) where
  pi := pi
  lam := lam
  app := app

def sums (signature : Declaration.Signature Tower.Head) :
    SigmaOperations (QuotientCwf.cwf (OpaqueRelatorExtension.rules signature)) where
  sigma := sigma
  pair := pair
  fst := fst
  snd := snd

theorem lam_represents {context : NativeQContext signature}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (body : QuotientCwf.Tm (QuotientCwf.ext context domain) codomain) :
    Conv (OpaqueRelatorExtension.rules signature).headEq (chosenTerm (lam body)).code
      (.lam (chosenTerm body).code) (OpaqueRelatorExtension.rules signature).computation :=
  chosenTerm_represents (lam body) (nativeLambda (chosenTerm body)) rfl

theorem app_represents {context : NativeQContext signature}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (function : QuotientCwf.Tm context (pi domain codomain))
    (argument : QuotientCwf.Tm context domain) :
    Conv (OpaqueRelatorExtension.rules signature).headEq (chosenTerm (app function argument)).code
      (.app (chosenTerm function).code (chosenTerm argument).code)
      (OpaqueRelatorExtension.rules signature).computation :=
  chosenTerm_represents (app function argument)
    (nativeApplication (QuotientCwf.termRepresentative _ function.val function.property)
      (chosenTerm argument)) rfl

theorem pair_represents {context : NativeQContext signature}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (first : QuotientCwf.Tm context domain)
    (second : QuotientCwf.Tm context (QuotientCwf.tySub codomain
      (selfExtend (QuotientCwf.cwf (OpaqueRelatorExtension.rules signature)) first))) :
    Conv (OpaqueRelatorExtension.rules signature).headEq (chosenTerm (pair first second)).code
      (.pair (chosenTerm first).code (chosenTerm second).code)
      (OpaqueRelatorExtension.rules signature).computation :=
  chosenTerm_represents (pair first second) (nativePair (chosenTerm first)
    (QuotientCwf.termRepresentative _ second.val
      (second.property.trans (type_at_argument codomain first).symm))) rfl

theorem fst_represents {context : NativeQContext signature}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (value : QuotientCwf.Tm context (sigma domain codomain)) :
    Conv (OpaqueRelatorExtension.rules signature).headEq (chosenTerm (fst value)).code
      (.fst (chosenTerm value).code) (OpaqueRelatorExtension.rules signature).computation :=
  chosenTerm_represents (fst value)
    (nativeFirst (QuotientCwf.termRepresentative _ value.val value.property)) rfl

theorem snd_represents {context : NativeQContext signature}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (value : QuotientCwf.Tm context (sigma domain codomain)) :
    Conv (OpaqueRelatorExtension.rules signature).headEq (chosenTerm (snd value)).code
      (.snd (chosenTerm value).code) (OpaqueRelatorExtension.rules signature).computation :=
  chosenTerm_represents (snd value)
    (nativeSecond (QuotientCwf.termRepresentative _ value.val value.property)) rfl

theorem pi_beta (signature : Declaration.Signature Tower.Head) : PiBeta (products signature) := by
  intro context domain codomain body argument
  apply eq_of_chosen_conversion
  have result := chosenTerm_represents
    (QuotientCwf.tmSub body (selfExtend (QuotientCwf.cwf _) argument))
    ((chosenTerm body).reindex (nativeSection (chosenTerm argument)))
    (term_at_argument body argument)
  rw [show ((chosenTerm body).reindex (nativeSection (chosenTerm argument))).code =
      inst0 (chosenTerm argument).code (chosenTerm body).code by
    change subst (nativeSection (chosenTerm argument)).substitution _ = _
    rw [nativeSection_substitution]; rfl] at result
  exact .trans _ _ _ (app_represents (lam body) argument)
    (.trans _ _ _ (Conv.congApp (lam_represents body) (.refl _))
      (.trans _ _ _ (.rel _ _ (.betaPi _ _)) result.symm))

theorem sigma_fst_beta {context : NativeQContext signature}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (first : QuotientCwf.Tm context domain)
    (second : QuotientCwf.Tm context (QuotientCwf.tySub codomain
      (selfExtend (QuotientCwf.cwf (OpaqueRelatorExtension.rules signature)) first))) :
    fst (pair first second) = first := by
  apply eq_of_chosen_conversion
  exact .trans _ _ _ (fst_represents (pair first second))
    (.trans _ _ _ (Conv.mapCompatible Tm.fst (fun step => .congFst step)
      (pair_represents first second)) (.rel _ _ (.betaSigmaFst _ _)))

theorem sigma_beta (signature : Declaration.Signature Tower.Head) : SigmaBeta (sums signature) := by
  constructor
  · exact sigma_fst_beta
  · intro context domain codomain first second
    apply heq_of_chosen_conversion
    · change QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf _)
        (fst (pair first second))) = _
      exact congrArg (fun argument => QuotientCwf.tySub codomain
        (selfExtend (QuotientCwf.cwf _) argument)) (sigma_fst_beta first second)
    · exact .trans _ _ _ (snd_represents (pair first second))
        (.trans _ _ _ (Conv.mapCompatible Tm.snd (fun step => .congSnd step)
          (pair_represents first second)) (.rel _ _ (.betaSigmaSnd _ _)))

/-- Formation is indexed by the supplied native levels, independently of
the universe level carried by a chosen representative of either class. -/
theorem pi_atUniverse {context : NativeQContext signature}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    {lower upper : LevelExpr} (domainAt : domain.AtUniverse (.sort lower))
    (codomainAt : codomain.AtUniverse (.sort upper)) :
    (pi domain codomain).AtUniverse (.sort (.max lower upper)) := by
  obtain ⟨actualDomain, domainClass, domainLevel⟩ := domainAt
  obtain ⟨actualCodomain, codomainClass, codomainLevel⟩ := codomainAt
  have domainConversion := (QType.mk_eq_iff actualDomain
    (QuotientCwf.typeRepresentative domain)).mp
    (domainClass.trans (QuotientCwf.typeRepresentative_class domain).symm)
  have codomainConversion := (QType.mk_eq_iff actualCodomain
    (QuotientCwf.typeRepresentative codomain)).mp
    (codomainClass.trans (QuotientCwf.typeRepresentative_class codomain).symm)
  let transferred := actualCodomain.reindex
    (extensionComparison actualDomain (QuotientCwf.typeRepresentative domain)
      domainConversion).hom
  refine ⟨nativePi actualDomain transferred, ?_, ?_⟩
  · apply Quotient.sound
    apply Conv.congPi domainConversion
    change Conv _ (subst ids actualCodomain.code) _ _
    rw [subst_ids]
    exact codomainConversion
  · have lowerEq : nativeLevel actualDomain = lower := by
      exact Tower.Head.sort.inj ((nativeLevel_spec actualDomain).symm.trans domainLevel)
    have upperEq : nativeLevel transferred = upper := by
      exact Tower.Head.sort.inj ((nativeLevel_spec transferred).symm.trans codomainLevel)
    change Tower.Head.sort (.max (nativeLevel actualDomain) (nativeLevel transferred)) = _
    rw [lowerEq, upperEq]

theorem sigma_atUniverse {context : NativeQContext signature}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    {lower upper : LevelExpr} (domainAt : domain.AtUniverse (.sort lower))
    (codomainAt : codomain.AtUniverse (.sort upper)) :
    (sigma domain codomain).AtUniverse (.sort (.max lower upper)) := by
  obtain ⟨actualDomain, domainClass, domainLevel⟩ := domainAt
  obtain ⟨actualCodomain, codomainClass, codomainLevel⟩ := codomainAt
  have domainConversion := (QType.mk_eq_iff actualDomain
    (QuotientCwf.typeRepresentative domain)).mp
    (domainClass.trans (QuotientCwf.typeRepresentative_class domain).symm)
  have codomainConversion := (QType.mk_eq_iff actualCodomain
    (QuotientCwf.typeRepresentative codomain)).mp
    (codomainClass.trans (QuotientCwf.typeRepresentative_class codomain).symm)
  let transferred := actualCodomain.reindex
    (extensionComparison actualDomain (QuotientCwf.typeRepresentative domain)
      domainConversion).hom
  refine ⟨nativeSigma actualDomain transferred, ?_, ?_⟩
  · apply Quotient.sound
    apply Conv.congSigma domainConversion
    change Conv _ (subst ids actualCodomain.code) _ _
    rw [subst_ids]
    exact codomainConversion
  · have lowerEq : nativeLevel actualDomain = lower := by
      exact Tower.Head.sort.inj ((nativeLevel_spec actualDomain).symm.trans domainLevel)
    have upperEq : nativeLevel transferred = upper := by
      exact Tower.Head.sort.inj ((nativeLevel_spec transferred).symm.trans codomainLevel)
    change Tower.Head.sort (.max (nativeLevel actualDomain) (nativeLevel transferred)) = _
    rw [lowerEq, upperEq]

theorem pi_formation_substitution (signature : Declaration.Signature Tower.Head) :
    StrictPiFormationSubstitution (products signature) := by
  intro source target morphism domain codomain
  exact ((congrArg (QuotientCwf.tySub (pi domain codomain))
    (QuotientCwf.project_representative morphism)).symm).trans
    (Quotient.sound (Conv.congPi (reindexed_domain_conversion morphism domain)
      (reindexed_codomain_conversion morphism codomain)))

theorem sigma_formation_substitution (signature : Declaration.Signature Tower.Head) :
    StrictSigmaFormationSubstitution (sums signature) := by
  intro source target morphism domain codomain
  exact ((congrArg (QuotientCwf.tySub (sigma domain codomain))
    (QuotientCwf.project_representative morphism)).symm).trans
    (Quotient.sound (Conv.congSigma (reindexed_domain_conversion morphism domain)
      (reindexed_codomain_conversion morphism codomain)))

theorem pi_substitution (signature : Declaration.Signature Tower.Head) :
    StrictPiSubstitution (products signature) := by
  refine ⟨pi_formation_substitution signature, ?_, ?_⟩
  · intro source target morphism domain codomain body
    apply heq_of_chosen_conversion
    · exact pi_formation_substitution signature morphism domain codomain
    · exact .trans _ _ _ (chosenTerm_reindex_represents (lam body) morphism)
        (.trans _ _ _ ((lam_represents body).substitute
          (QuotientCwf.representative morphism).substitution)
          (.trans _ _ _ (Conv.congLam (chosenTerm_lift_reindex_represents morphism body).symm)
            (lam_represents _).symm))
  · intro source target morphism domain codomain function argument reindexedFunction sameFunction
    have functions := chosenTerm_code_eq (heq_value
      (pi_formation_substitution signature morphism domain codomain) sameFunction)
    have functionConversion : Conv _
        (subst (QuotientCwf.representative morphism).substitution (chosenTerm function).code)
        (chosenTerm reindexedFunction).code _ :=
      functions ▸ (chosenTerm_reindex_represents function morphism).symm
    apply heq_of_chosen_conversion
    · exact instantiatedType_substitution morphism codomain argument
    · exact .trans _ _ _ (chosenTerm_reindex_represents (app function argument) morphism)
        (.trans _ _ _ ((app_represents function argument).substitute
          (QuotientCwf.representative morphism).substitution)
          (.trans _ _ _ (Conv.congApp functionConversion
            (chosenTerm_reindex_represents argument morphism).symm)
            (app_represents reindexedFunction _).symm))

theorem fst_substitution {source target : NativeQContext signature}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty target}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext target domain)}
    (value : QuotientCwf.Tm target (sigma domain codomain))
    (reindexedValue : QuotientCwf.Tm source (sigma (QuotientCwf.tySub domain morphism)
      (QuotientCwf.tySub codomain
        (extensionSubstitution (C := QuotientCwf.cwf _) morphism domain))))
    (sameValue : HEq (QuotientCwf.tmSub value morphism) reindexedValue) :
    QuotientCwf.tmSub (fst value) morphism = fst reindexedValue := by
  have values := chosenTerm_code_eq (heq_value
    (sigma_formation_substitution signature morphism domain codomain) sameValue)
  have valueConversion : Conv _
      (subst (QuotientCwf.representative morphism).substitution (chosenTerm value).code)
      (chosenTerm reindexedValue).code _ :=
    values ▸ (chosenTerm_reindex_represents value morphism).symm
  apply eq_of_chosen_conversion
  exact .trans _ _ _ (chosenTerm_reindex_represents (fst value) morphism)
    (.trans _ _ _ ((fst_represents value).substitute
      (QuotientCwf.representative morphism).substitution)
      (.trans _ _ _ (Conv.mapCompatible Tm.fst (fun step => .congFst step) valueConversion)
        (fst_represents reindexedValue).symm))

theorem sigma_substitution (signature : Declaration.Signature Tower.Head) :
    StrictSigmaSubstitution (sums signature) := by
  refine ⟨sigma_formation_substitution signature, ?_, ?_⟩
  · intro source target morphism domain codomain first second reindexedSecond sameSecond
    have seconds := chosenTerm_code_eq (heq_value
      (instantiatedType_substitution morphism codomain first) sameSecond)
    have secondConversion : Conv _
        (subst (QuotientCwf.representative morphism).substitution (chosenTerm second).code)
        (chosenTerm reindexedSecond).code _ :=
      seconds ▸ (chosenTerm_reindex_represents second morphism).symm
    apply heq_of_chosen_conversion
    · exact sigma_formation_substitution signature morphism domain codomain
    · exact .trans _ _ _ (chosenTerm_reindex_represents (pair first second) morphism)
        (.trans _ _ _ ((pair_represents first second).substitute
          (QuotientCwf.representative morphism).substitution)
          (.trans _ _ _ (Conv.congPair
            (chosenTerm_reindex_represents first morphism).symm secondConversion)
            (pair_represents _ reindexedSecond).symm))
  · intro source target morphism domain codomain value reindexedValue sameValue
    have values := chosenTerm_code_eq (heq_value
      (sigma_formation_substitution signature morphism domain codomain) sameValue)
    have valueConversion : Conv _
        (subst (QuotientCwf.representative morphism).substitution (chosenTerm value).code)
        (chosenTerm reindexedValue).code _ :=
      values ▸ (chosenTerm_reindex_represents value morphism).symm
    constructor
    · exact heq_of_eq (fst_substitution morphism value reindexedValue sameValue)
    · apply heq_of_chosen_conversion
      · exact (instantiatedType_substitution morphism codomain (fst value)).trans
          (congrArg (fun argument => QuotientCwf.tySub
            (QuotientCwf.tySub codomain
              (extensionSubstitution (C := QuotientCwf.cwf _) morphism domain))
            (selfExtend (QuotientCwf.cwf _) argument))
              (fst_substitution morphism value reindexedValue sameValue))
      · exact .trans _ _ _ (chosenTerm_reindex_represents (snd value) morphism)
          (.trans _ _ _ ((snd_represents value).substitute
            (QuotientCwf.representative morphism).substitution)
            (.trans _ _ _ (Conv.mapCompatible Tm.snd (fun step => .congSnd step) valueConversion)
              (snd_represents reindexedValue).symm))

namespace Controls

open QuotientCwf.Controls (context wireType result)

def wireBinder : (QuotientCwf.ext context wireType).as ≅
    extend Common.context Common.wireType :=
  extensionComparison (QuotientCwf.typeRepresentative wireType) Common.wireType
    ((QType.mk_eq_iff _ _).mp (QuotientCwf.typeRepresentative_class wireType))

def identityFamily : QuotientCwf.Ty (QuotientCwf.ext context wireType) :=
  QType.mk (ComparisonControls.variableIdentity.reindex wireBinder.hom)

def reflexivityBody : QuotientCwf.Tm (QuotientCwf.ext context wireType) identityFamily :=
  TermFibre.mk (ComparisonControls.variableReflexivity.reindex wireBinder.hom)

theorem displayed_family_is_dependent :
    (ComparisonControls.variableIdentity.reindex wireBinder.hom).code =
      .id NativeWireData.dataType (.var (0 : Fin 1)) (.var (0 : Fin 1)) := by
  change subst ids ComparisonControls.variableIdentity.code = _
  rw [subst_ids]
  rfl

theorem displayed_body_is_native_reflexivity :
    (ComparisonControls.variableReflexivity.reindex wireBinder.hom).code =
      .refl (.var (0 : Fin 1)) := by
  change subst ids (.refl (.var 0)) = _
  rw [subst_ids]
  rfl

def expectedType (wire : NativeWireData.Wire) : TypeOver Common.context :=
  ComparisonControls.variableIdentity.reindex (nativeSection (Common.result wire))

def expectedReflexivity (wire : NativeWireData.Wire) : Term Common.context (expectedType wire) :=
  ComparisonControls.variableReflexivity.reindex (nativeSection (Common.result wire))

theorem expected_type_code (wire : NativeWireData.Wire) :
    (expectedType wire).code =
      .id NativeWireData.dataType (NativeWireData.encode wire) (NativeWireData.encode wire) := by
  change subst (nativeSection (Common.result wire)).substitution
    ComparisonControls.variableIdentity.code = _
  rw [nativeSection_substitution]
  rfl

theorem expected_reflexivity_code (wire : NativeWireData.Wire) :
    (expectedReflexivity wire).code = .refl (NativeWireData.encode wire) := by
  change subst (nativeSection (Common.result wire)).substitution (.refl (.var 0)) = _
  rw [nativeSection_substitution]
  rfl

def argumentAtBinder (wire : NativeWireData.Wire) :
    Term Common.context (QuotientCwf.typeRepresentative wireType) :=
  (Common.result wire).convertType (QuotientCwf.typeRepresentative wireType)
    ((QType.mk_eq_iff _ _).mp (QuotientCwf.typeRepresentative_class wireType)).symm

theorem argumentAtBinder_class (wire : NativeWireData.Wire) :
    QTerm.mk (argumentAtBinder wire) = (result wire).val := by
  apply Quotient.sound
  exact ⟨(QType.mk_eq_iff _ _).mp (QuotientCwf.typeRepresentative_class wireType), .refl _⟩

theorem section_to_wire (wire : NativeWireData.Wire) :
    nativeSection (argumentAtBinder wire) ≫ wireBinder.hom = nativeSection (Common.result wire) := by
  apply Hom.ext
  change subComp (nativeSection (argumentAtBinder wire)).substitution ids = _
  rw [subComp_ids_right, nativeSection_substitution, nativeSection_substitution]
  rfl

/-- The semantic dependent application returns exactly the class of the
native reflexivity proof at the supplied wire, not merely some inhabitant
of an unrelated or constant type. -/
theorem body_instantiation (wire : NativeWireData.Wire) :
    (QuotientCwf.tmSub reflexivityBody
      (selfExtend (QuotientCwf.cwf HOLNativeRelatorCompatibility.rules) (result wire))).val =
      QTerm.mk (expectedReflexivity wire) := by
  have sectionClass := nativeSection_projects_of_class (result wire)
    (argumentAtBinder wire) (argumentAtBinder_class wire)
  exact ((congrArg (QuotientCwf.totalSub reflexivityBody.val) sectionClass).symm).trans
    ((QTerm.reindex_comp (QTerm.mk ComparisonControls.variableReflexivity)
      (nativeSection (argumentAtBinder wire)) wireBinder.hom).symm.trans
        (congrArg (QTerm.reindex (QTerm.mk ComparisonControls.variableReflexivity))
          (section_to_wire wire)))

theorem dependent_application (wire : NativeWireData.Wire) :
    (app (lam reflexivityBody) (result wire)).val = QTerm.mk (expectedReflexivity wire) :=
  (congrArg Subtype.val
    (pi_beta HOLNativeRelatorCompatibility.signature reflexivityBody (result wire))).trans
      (body_instantiation wire)

theorem dependent_application_admitted (wire : NativeWireData.Wire) :
    Judgment HOLNativeRelatorCompatibility.rules Common.context.raw
      (.refl (NativeWireData.encode wire))
      (.id NativeWireData.dataType (NativeWireData.encode wire) (NativeWireData.encode wire)) := by
  have admitted := (expectedReflexivity wire).judgment
  rw [expected_reflexivity_code, expected_type_code] at admitted
  exact admitted

/-- A function whose codomain depends on its input is itself passed as the
argument of another actual native lambda/application. -/
theorem higher_order_identity :
    (app (lam (QuotientCwf.vz (pi wireType identityFamily))) (lam reflexivityBody)).val =
      (lam reflexivityBody).val :=
  (congrArg Subtype.val (pi_beta HOLNativeRelatorCompatibility.signature
    (QuotientCwf.vz (pi wireType identityFamily)) (lam reflexivityBody))).trans
      (selfExtend_value (lam reflexivityBody))

def dependentPair (wire : NativeWireData.Wire) :
    QuotientCwf.Tm context (sigma wireType identityFamily) :=
  pair (result wire) (QuotientCwf.tmSub reflexivityBody
    (selfExtend (QuotientCwf.cwf HOLNativeRelatorCompatibility.rules) (result wire)))

theorem dependent_pair_first (wire : NativeWireData.Wire) :
    fst (dependentPair wire) = result wire := sigma_fst_beta _ _

theorem dependent_pair_second (wire : NativeWireData.Wire) :
    (snd (dependentPair wire)).val = QTerm.mk (expectedReflexivity wire) := by
  have beta := (sigma_beta HOLNativeRelatorCompatibility.signature).2
    (codomain := identityFamily) (result wire)
    (QuotientCwf.tmSub reflexivityBody
      (selfExtend (QuotientCwf.cwf HOLNativeRelatorCompatibility.rules) (result wire)))
  have sameType : QuotientCwf.tySub identityFamily
      (selfExtend (QuotientCwf.cwf HOLNativeRelatorCompatibility.rules)
        (fst (dependentPair wire))) =
      QuotientCwf.tySub identityFamily
        (selfExtend (QuotientCwf.cwf HOLNativeRelatorCompatibility.rules) (result wire)) :=
    congrArg (fun argument => QuotientCwf.tySub identityFamily
      (selfExtend (QuotientCwf.cwf HOLNativeRelatorCompatibility.rules) argument))
        (dependent_pair_first wire)
  exact (heq_value sameType beta).trans (body_instantiation wire)

/-- The constructed dependent sums do not collapse distinct native data. -/
theorem dependent_pairs_seven_not_eight :
    dependentPair (.natural 7) ≠ dependentPair (.natural 8) := by
  intro same
  have firsts := congrArg fst same
  have results : result (.natural 7) = result (.natural 8) :=
    (dependent_pair_first (.natural 7)).symm.trans
      (firsts.trans (dependent_pair_first (.natural 8)))
  exact QuotientCwf.Controls.seven_is_not_eight results

theorem dependent_pi_at_zero :
    (pi wireType identityFamily).AtUniverse (.sort (.max Tower.zero Tower.zero)) :=
  pi_atUniverse (QType.atUniverse_mk Common.wireType)
    (QType.atUniverse_mk (ComparisonControls.variableIdentity.reindex wireBinder.hom))

theorem dependent_sigma_at_zero :
    (sigma wireType identityFamily).AtUniverse (.sort (.max Tower.zero Tower.zero)) :=
  sigma_atUniverse (QType.atUniverse_mk Common.wireType)
    (QType.atUniverse_mk (ComparisonControls.variableIdentity.reindex wireBinder.hom))

end Controls

end

end FormationSensitiveContextual.QuotientProducts
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
