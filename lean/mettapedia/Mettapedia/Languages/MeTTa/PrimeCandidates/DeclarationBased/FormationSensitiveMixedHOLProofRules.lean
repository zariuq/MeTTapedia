import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveMixedListElimination

/-!
# Native HOL proof rules on mixed-environment operands

The operands may use the native List declarations. Formation is derived in
the common environment, rather than obtained by assuming that these operands
were typable in the smaller HOL-only environment. Constants and conversion
equations are transported from that independently constructed environment.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace FormationSensitiveMixedHOLProofRules

open Presentation Presentation.Declaration
open FormationSensitiveHOLProofListIntegration
open FormationSensitiveHOLProofFamily
  (proof implicationFamily universalProposition universalFamily proofType proofName)
open FormationSensitiveHOLUniformList (rawImp)

variable {n : Nat}

theorem proposition_formed (context : Tower.Ctx n) :
    Typing context (.const `HOLUniformList.prop) (sortTm Tower.zero) :=
  proof_typed (FormationSensitiveHOLProofFamily.proposition_formed context)

theorem proofConstant_typed (context : Tower.Ctx n) :
    Typing context (.const proofName) (liftClosed proofType) :=
  proof_typed (FormationSensitiveHOLProofFamily.proofConstant_typed context)

theorem proof_formed {context : Tower.Ctx n} {p : Tower.Tm n}
    (typed : Typing context p (.const `HOLUniformList.prop)) :
    Typing context (proof p) (sortTm Tower.zero) :=
  FormationSensitive.Typing.appElim (proofConstant_typed context) typed

theorem pi_zero {context : Tower.Ctx n} {a : Tower.Tm n} {b : Tower.Tm (n + 1)}
    (domain : Typing context a (sortTm Tower.zero))
    (codomain : Typing (.snoc context a) b (sortTm Tower.zero)) :
    Typing context (.pi a b) (sortTm Tower.zero) := by
  apply FormationSensitive.Typing.cumul
    (.piForm domain (.sort Tower.zero) codomain (.sort Tower.zero)
      (.sorts Tower.zero Tower.zero))
  intro valuation
  simp [LevelExpr.eval, LevelTower.zero]

theorem implication_proposition {context : Tower.Ctx n} {p q : Tower.Tm n}
    (hp : Typing context p (.const `HOLUniformList.prop))
    (hq : Typing context q (.const `HOLUniformList.prop)) :
    Typing context (rawImp p q) (.const `HOLUniformList.prop) := by
  have symbol := proof_typed (FormationSensitiveHOLProofFamily.include_typed
    (FormationSensitiveHOLInterface.closed_typed
      FormationSensitiveHOLUniformList.signature.implication_typed context))
  exact FormationSensitive.Typing.appElim
    (FormationSensitive.Typing.appElim symbol hp) hq

theorem implication_formed {context : Tower.Ctx n} {p q : Tower.Tm n}
    (hp : Typing context p (.const `HOLUniformList.prop))
    (hq : Typing context q (.const `HOLUniformList.prop)) :
    Typing context (implicationFamily p q) (sortTm Tower.zero) :=
  pi_zero (proof_formed hp) (proof_formed hq).weaken

theorem include_conversion {left right : Tower.Tm n}
    (conversion : Conv FormationSensitiveHOLProofFamily.rules.headEq left right
      FormationSensitiveHOLProofFamily.rules.computation) :
    Conv rules.headEq left right rules.computation := by
  simpa only [Tm.mapHead_id] using
    conversion.mapHead (fun head => head) proofMorphism.headEq proofMorphism.computation

theorem implication_conversion (p q : Tower.Tm n) :
    Conv rules.headEq (proof (rawImp p q)) (implicationFamily p q) rules.computation :=
  include_conversion (FormationSensitiveHOLProofFamily.implication_conversion p q)

theorem universal_lambda_conversion (a : Tower.Tm n) (body : Tower.Tm (n + 1)) :
    Conv rules.headEq (proof (universalProposition a (.lam body)))
      (.pi a (proof body)) rules.computation :=
  include_conversion (FormationSensitiveHOLProofFamily.universal_lambda_conversion a body)

theorem universal_proposition {context : Tower.Ctx n} {a predicate : Tower.Tm n}
    (ha : Typing context a (sortTm Tower.zero))
    (hp : Typing context predicate (.pi a (.const `HOLUniformList.prop))) :
    Typing context (universalProposition a predicate) (.const `HOLUniformList.prop) := by
  have symbol : Typing context (.const `HOLUniformList.universal)
      (liftClosed FormationSensitiveHOLUniformList.universalType) :=
    proof_typed (FormationSensitiveHOLProofFamily.include_typed
      (.const (by decide) FormationSensitiveHOLUniformList.universal_type_formed
        (.sort (.max (.succ Tower.zero) Tower.zero))))
  have applied := FormationSensitive.Typing.appElim symbol ha
  have first : Typing context (.app (.const `HOLUniformList.universal) a)
      (.pi (.pi a (.const `HOLUniformList.prop)) (.const `HOLUniformList.prop)) := by
    simpa only [FormationSensitiveHOLUniformList.universalType, liftClosed,
      rename, inst0, subst, subst0, consSub, liftSub,
      liftRen, Fin.cases_zero] using applied
  exact FormationSensitive.Typing.appElim first hp

theorem universal_lambda_proposition {context : Tower.Ctx n} {a : Tower.Tm n}
    {body : Tower.Tm (n + 1)}
    (ha : Typing context a (sortTm Tower.zero))
    (hb : Typing (.snoc context a) body (.const `HOLUniformList.prop)) :
    Typing context (universalProposition a (.lam body)) (.const `HOLUniformList.prop) :=
  universal_proposition ha
    (.lamIntro (pi_zero ha (proposition_formed _)) (.sort Tower.zero) hb)

theorem implication_intro {context : Tower.Ctx n} {p q : Tower.Tm n}
    {body : Tower.Tm (n + 1)}
    (hp : Typing context p (.const `HOLUniformList.prop))
    (hq : Typing context q (.const `HOLUniformList.prop))
    (hb : Typing (.snoc context (proof p)) body (rename wk (proof q))) :
    Typing context (.lam body) (proof (rawImp p q)) :=
  .conv (.lamIntro (implication_formed hp hq) (.sort Tower.zero) hb)
    (proof_formed (implication_proposition hp hq)) (.sort Tower.zero)
    (implication_conversion p q).symm

theorem implication_elim {context : Tower.Ctx n} {p q major minor : Tower.Tm n}
    (hp : Typing context p (.const `HOLUniformList.prop))
    (hq : Typing context q (.const `HOLUniformList.prop))
    (hm : Typing context major (proof (rawImp p q)))
    (ha : Typing context minor (proof p)) :
    Typing context (.app major minor) (proof q) := by
  have converted := FormationSensitive.Typing.conv hm (implication_formed hp hq)
    (.sort Tower.zero) (implication_conversion p q)
  simpa only [implicationFamily, inst0_rename_wk] using
    FormationSensitive.Typing.appElim converted ha

theorem universal_intro {context : Tower.Ctx n} {a : Tower.Tm n}
    {p body : Tower.Tm (n + 1)}
    (ha : Typing context a (sortTm Tower.zero))
    (hp : Typing (.snoc context a) p (.const `HOLUniformList.prop))
    (hb : Typing (.snoc context a) body (proof p)) :
    Typing context (.lam body) (proof (universalProposition a (.lam p))) :=
  .conv (.lamIntro (pi_zero ha (proof_formed hp)) (.sort Tower.zero) hb)
    (proof_formed (universal_lambda_proposition ha hp)) (.sort Tower.zero)
    (universal_lambda_conversion a p).symm

theorem universal_elim {context : Tower.Ctx n} {a major argument : Tower.Tm n}
    {p : Tower.Tm (n + 1)}
    (ha : Typing context a (sortTm Tower.zero))
    (hp : Typing (.snoc context a) p (.const `HOLUniformList.prop))
    (hm : Typing context major (proof (universalProposition a (.lam p))))
    (ht : Typing context argument a) :
    Typing context (.app major argument) (proof (inst0 argument p)) := by
  have converted := FormationSensitive.Typing.conv hm (pi_zero ha (proof_formed hp))
    (.sort Tower.zero) (universal_lambda_conversion a p)
  simpa only [inst0, FormationSensitiveHOLProofFamily.proof_subst] using
    FormationSensitive.Typing.appElim converted ht

namespace Controls

/-- A predicate on actual native lists is admitted without pretending that
its domain was the opaque source sequence declaration. -/
theorem nativeList_predicate_identity {context : Tower.Ctx n}
    {element predicate : Tower.Tm n}
    (elementTyped : Typing context element (sortTm Tower.zero))
    (predicateTyped : Typing context predicate
      (.pi (NativeIndexedFamilies.Intrinsic.listApp element) (.const `HOLUniformList.prop))) :
    Typing context (.lam (.lam (.var 0)))
      (proof (universalProposition (NativeIndexedFamilies.Intrinsic.listApp element)
        (.lam (rawImp (.app (rename wk predicate) (.var 0))
          (.app (rename wk predicate) (.var 0)))))) := by
  have atList : Typing
      (.snoc context (NativeIndexedFamilies.Intrinsic.listApp element))
      (.app (rename wk predicate) (.var 0)) (.const `HOLUniformList.prop) := by
    have applied := FormationSensitive.Typing.appElim
      (predicateTyped.weaken (extension := NativeIndexedFamilies.Intrinsic.listApp element))
      (FormationSensitive.Typing.var 0)
    simpa only [rename, inst0, subst] using applied
  exact universal_intro (FormationSensitiveMixedListElimination.listApp_typed elementTyped)
    (implication_proposition atList atList) (implication_intro atList atList (.var 0))

/-- An unknown predicate application is not one of the two decoder roots.
This concerns root matching, not its entire conversion class. -/
theorem unknown_predicate_not_decoded (predicate : Fin n) (argument target : Tower.Tm n) :
    ¬ FormationSensitiveHOLProofFamily.DecoderStep
      (proof (.app (.var predicate) argument)) target := by
  intro step
  cases step

end Controls

#print axioms proof_formed
#print axioms implication_proposition
#print axioms universal_proposition
#print axioms implication_intro
#print axioms implication_elim
#print axioms universal_intro
#print axioms universal_elim
#print axioms Controls.nativeList_predicate_identity
#print axioms Controls.unknown_predicate_not_decoded

end FormationSensitiveMixedHOLProofRules
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
