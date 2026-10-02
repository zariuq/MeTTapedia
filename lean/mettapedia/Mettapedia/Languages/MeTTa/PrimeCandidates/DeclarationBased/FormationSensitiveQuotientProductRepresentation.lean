import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientUniverseProducts

/-!
# Native representatives of quotient products and their universe codes

The existing Pi/Sigma operations agree with arbitrary independently formed
native domain and dependent codomain syntax, transported through the actual
canonical comprehension comparison. The corresponding mixed-level codes
agree in the fixed result universe. Neither assertion identifies distinct
raw contexts or guesses an input universe from a chosen representative.

These are constructor comparisons in the same formed conversion CwF. They
do not require a total based-J operation or assert a full native model.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientProductRepresentation

open _root_.CategoryTheory FormationSensitive
open QuotientProducts

noncomputable section

variable {signature : Declaration.Signature Tower.Head}

/-- Choosing representatives for the semantic binder changes neither the
native Pi constructor class nor its actually submitted dependent family. -/
theorem pi_projects {context : NativeContext signature} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    pi (QType.mk domain)
      (QuotientCwf.tySub (QType.mk codomain)
        (QuotientCwf.extPresentation context domain).hom) =
      QType.mk (nativePi domain codomain) := by
  let selected := QuotientCwf.typeRepresentative (QType.mk domain)
  have domainConversion := (QType.mk_eq_iff selected domain).mp
    (QuotientCwf.typeRepresentative_class (QType.mk domain))
  let transferred := codomain.reindex
    (extensionComparison selected domain domainConversion).hom
  have codomainConversion := (QType.mk_eq_iff
    (QuotientCwf.typeRepresentative (QType.mk transferred)) transferred).mp
      (QuotientCwf.typeRepresentative_class (QType.mk transferred))
  apply Quotient.sound
  apply Conv.congPi domainConversion
  change Conv _ _ (subst ids codomain.code) _ at codomainConversion
  rw [subst_ids] at codomainConversion
  exact codomainConversion

theorem sigma_projects {context : NativeContext signature} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    sigma (QType.mk domain)
      (QuotientCwf.tySub (QType.mk codomain)
        (QuotientCwf.extPresentation context domain).hom) =
      QType.mk (nativeSigma domain codomain) := by
  let selected := QuotientCwf.typeRepresentative (QType.mk domain)
  have domainConversion := (QType.mk_eq_iff selected domain).mp
    (QuotientCwf.typeRepresentative_class (QType.mk domain))
  let transferred := codomain.reindex
    (extensionComparison selected domain domainConversion).hom
  have codomainConversion := (QType.mk_eq_iff
    (QuotientCwf.typeRepresentative (QType.mk transferred)) transferred).mp
      (QuotientCwf.typeRepresentative_class (QType.mk transferred))
  apply Quotient.sound
  apply Conv.congSigma domainConversion
  change Conv _ _ (subst ids codomain.code) _ at codomainConversion
  rw [subst_ids] at codomainConversion
  exact codomainConversion

/-- A supplied class equality is transported through comprehension, not
promoted to an equality of the original raw context annotations. -/
theorem pi_projects_of_eq {context : NativeContext signature}
    (domain : TypeOver context) (codomain : TypeOver (extend context domain))
    {semanticDomain : QType context} (same : semanticDomain = QType.mk domain) :
    pi semanticDomain
      (QuotientCwf.tySub (QType.mk codomain)
        ((eqToIso (congrArg
          (QuotientCwf.ext ((quotientProjection _).obj context)) same)).hom ≫
            (QuotientCwf.extPresentation context domain).hom)) =
      QType.mk (nativePi domain codomain) := by
  subst semanticDomain
  simp only [eqToIso_refl, Iso.refl_hom]
  exact (congrArg (fun morphism => pi (QType.mk domain)
    (QuotientCwf.tySub (QType.mk codomain) morphism))
      (Category.id_comp (QuotientCwf.extPresentation context domain).hom)).trans
        (pi_projects domain codomain)

theorem sigma_projects_of_eq {context : NativeContext signature}
    (domain : TypeOver context) (codomain : TypeOver (extend context domain))
    {semanticDomain : QType context} (same : semanticDomain = QType.mk domain) :
    sigma semanticDomain
      (QuotientCwf.tySub (QType.mk codomain)
        ((eqToIso (congrArg
          (QuotientCwf.ext ((quotientProjection _).obj context)) same)).hom ≫
            (QuotientCwf.extPresentation context domain).hom)) =
      QType.mk (nativeSigma domain codomain) := by
  subst semanticDomain
  simp only [eqToIso_refl, Iso.refl_hom]
  exact (congrArg (fun morphism => sigma (QType.mk domain)
    (QuotientCwf.tySub (QType.mk codomain) morphism))
      (Category.id_comp (QuotientCwf.extPresentation context domain).hom)).trans
        (sigma_projects domain codomain)

/-- The supplied level admission constructs an actual universe term. The
incidental level of a different representative is irrelevant. -/
def codeOfType {context : NativeContext signature} (level : LevelExpr Nat)
    (type : TypeOver context) (atLevel : type.level = .sort level) :
    QuotientUniverses.Code ((quotientProjection _).obj context) level :=
  QuotientUniverses.ofFormed level type.code (by
    have formed := type.formed
    rw [atLevel] at formed
    exact formed)

theorem decode_codeOfType {context : NativeContext signature} (level : LevelExpr Nat)
    (type : TypeOver context) (atLevel : type.level = .sort level) :
    QuotientUniverses.decode (codeOfType level type atLevel) = QType.mk type :=
  (QuotientUniverses.decode_ofFormed level type.code _).trans
    ((QType.mk_eq_iff _ _).mpr (.refl _))

/-- The code's decoded binder and the actual submitted native binder are
connected by the existing comparison isomorphism. -/
def codePresentation {context : NativeContext signature} (level : LevelExpr Nat)
    (type : TypeOver context) (atLevel : type.level = .sort level) :
    QuotientCwf.ext ((quotientProjection _).obj context)
      (QuotientUniverses.decode (codeOfType level type atLevel)) ≅
        (quotientProjection _).obj (extend context type) :=
  eqToIso (congrArg (QuotientCwf.ext ((quotientProjection _).obj context))
    (decode_codeOfType level type atLevel)) ≪≫ QuotientCwf.extPresentation context type

theorem nativePi_level {context : NativeContext signature} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) {lower upper : LevelExpr Nat}
    (domainAt : domain.level = .sort lower) (codomainAt : codomain.level = .sort upper) :
    (nativePi domain codomain).level = .sort (.max lower upper) := by
  have lowerEq := LevelTower.Head.sort.inj ((nativeLevel_spec domain).symm.trans domainAt)
  have upperEq := LevelTower.Head.sort.inj ((nativeLevel_spec codomain).symm.trans codomainAt)
  change LevelTower.Head.sort (.max (nativeLevel domain) (nativeLevel codomain)) = _
  rw [lowerEq, upperEq]

theorem nativeSigma_level {context : NativeContext signature} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) {lower upper : LevelExpr Nat}
    (domainAt : domain.level = .sort lower) (codomainAt : codomain.level = .sort upper) :
    (nativeSigma domain codomain).level = .sort (.max lower upper) := by
  have lowerEq := LevelTower.Head.sort.inj ((nativeLevel_spec domain).symm.trans domainAt)
  have upperEq := LevelTower.Head.sort.inj ((nativeLevel_spec codomain).symm.trans codomainAt)
  change LevelTower.Head.sort (.max (nativeLevel domain) (nativeLevel codomain)) = _
  rw [lowerEq, upperEq]

/-- Mixed-level Pi code agreement in the fixed result universe. The
codomain is reindexed through the actual code/binder comparison. -/
theorem piCode_projects {context : NativeContext signature} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) {lower upper : LevelExpr Nat}
    (domainAt : domain.level = .sort lower) (codomainAt : codomain.level = .sort upper) :
    QuotientUniverseProducts.piCode (codeOfType lower domain domainAt)
      (QuotientUniverses.reindex (codeOfType upper codomain codomainAt)
        (codePresentation lower domain domainAt).hom) =
      codeOfType (.max lower upper) (nativePi domain codomain)
        (nativePi_level domain codomain domainAt codomainAt) := by
  apply QuotientUniverses.decode_injective
  rw [QuotientUniverseProducts.decode_piCode, QuotientUniverses.decode_sub,
    decode_codeOfType upper codomain codomainAt]
  exact (pi_projects_of_eq domain codomain (decode_codeOfType lower domain domainAt)).trans
    (decode_codeOfType (.max lower upper) (nativePi domain codomain)
      (nativePi_level domain codomain domainAt codomainAt)).symm

theorem sigmaCode_projects {context : NativeContext signature} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) {lower upper : LevelExpr Nat}
    (domainAt : domain.level = .sort lower) (codomainAt : codomain.level = .sort upper) :
    QuotientUniverseProducts.sigmaCode (codeOfType lower domain domainAt)
      (QuotientUniverses.reindex (codeOfType upper codomain codomainAt)
        (codePresentation lower domain domainAt).hom) =
      codeOfType (.max lower upper) (nativeSigma domain codomain)
        (nativeSigma_level domain codomain domainAt codomainAt) := by
  apply QuotientUniverses.decode_injective
  rw [QuotientUniverseProducts.decode_sigmaCode, QuotientUniverses.decode_sub,
    decode_codeOfType upper codomain codomainAt]
  exact (sigma_projects_of_eq domain codomain (decode_codeOfType lower domain domainAt)).trans
    (decode_codeOfType (.max lower upper) (nativeSigma domain codomain)
      (nativeSigma_level domain codomain domainAt codomainAt)).symm

namespace Controls

/-- A genuinely dependent identity family admitted in a higher universe
than its Data domain. Cumulativity changes its level, not its endpoints. -/
def mixedFamily : TypeOver (extend Common.context Common.wireType) where
  code := ComparisonControls.variableIdentity.code
  level := .sort (.succ Tower.zero)
  universeWitness := .sort _
  formed := .cumul ComparisonControls.variableIdentity.formed (fun _ => Nat.le_succ _)

theorem mixed_family_depends_on_newest :
    mixedFamily.code = .id NativeWireData.dataType (.var (0 : Fin 1)) (.var 0) := rfl

theorem mixed_input_levels_distinct : Common.wireType.level ≠ mixedFamily.level := by
  intro same
  cases same

def mixedPiCode : QuotientUniverses.Code
    ((quotientProjection HOLNativeRelatorCompatibility.rules).obj Common.context)
    (.max Tower.zero (.succ Tower.zero)) :=
  QuotientUniverseProducts.piCode (codeOfType Tower.zero Common.wireType rfl)
    (QuotientUniverses.reindex (codeOfType (.succ Tower.zero) mixedFamily rfl)
      (codePresentation Tower.zero Common.wireType rfl).hom)

def mixedSigmaCode : QuotientUniverses.Code
    ((quotientProjection HOLNativeRelatorCompatibility.rules).obj Common.context)
    (.max Tower.zero (.succ Tower.zero)) :=
  QuotientUniverseProducts.sigmaCode (codeOfType Tower.zero Common.wireType rfl)
    (QuotientUniverses.reindex (codeOfType (.succ Tower.zero) mixedFamily rfl)
      (codePresentation Tower.zero Common.wireType rfl).hom)

theorem mixed_pi_code :
    mixedPiCode = QuotientUniverses.ofFormed (.max Tower.zero (.succ Tower.zero))
      (.pi NativeWireData.dataType (.id NativeWireData.dataType (.var 0) (.var 0)))
      (.piForm Common.wireType.formed (.sort _) mixedFamily.formed (.sort _) (.sorts _ _)) :=
  piCode_projects Common.wireType mixedFamily rfl rfl

theorem mixed_sigma_code :
    mixedSigmaCode = QuotientUniverses.ofFormed (.max Tower.zero (.succ Tower.zero))
      (.sigma NativeWireData.dataType (.id NativeWireData.dataType (.var 0) (.var 0)))
      (.sigmaForm Common.wireType.formed (.sort _) mixedFamily.formed (.sort _) (.sorts _ _)) :=
  sigmaCode_projects Common.wireType mixedFamily rfl rfl

/-- The actual generated product code cannot be reinterpreted as the
unrelated native universe. This uses the same opaque declaration package. -/
theorem mixed_pi_not_universe :
    QuotientUniverses.decode mixedPiCode ≠
      QType.mk (QuotientUniverses.universeType Common.context Tower.zero) := by
  intro same
  have represented := (congrArg QuotientUniverses.decode
    (piCode_projects Common.wireType mixedFamily rfl rfl)).trans
      (decode_codeOfType _ (nativePi Common.wireType mixedFamily) _)
  have boundary := OpaqueRelatorExtension.pi_conversion_boundary HOLNativeRelatorCompatibility.opacity
  exact boundary.headDisjoint ((QType.mk_eq_iff _ _).mp (represented.symm.trans same))

theorem mixed_sigma_not_universe :
    QuotientUniverses.decode mixedSigmaCode ≠
      QType.mk (QuotientUniverses.universeType Common.context Tower.zero) := by
  intro same
  have represented := (congrArg QuotientUniverses.decode
    (sigmaCode_projects Common.wireType mixedFamily rfl rfl)).trans
      (decode_codeOfType _ (nativeSigma Common.wireType mixedFamily) _)
  have boundary := OpaqueRelatorExtension.sigma_conversion_boundary HOLNativeRelatorCompatibility.opacity
  exact boundary.headDisjoint ((QType.mk_eq_iff _ _).mp (represented.symm.trans same))

end Controls

end

#print axioms pi_projects
#print axioms sigma_projects
#print axioms piCode_projects
#print axioms sigmaCode_projects
#print axioms Controls.mixed_pi_code
#print axioms Controls.mixed_sigma_code
#print axioms Controls.mixed_pi_not_universe
#print axioms Controls.mixed_sigma_not_universe

end FormationSensitiveContextual.QuotientProductRepresentation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
