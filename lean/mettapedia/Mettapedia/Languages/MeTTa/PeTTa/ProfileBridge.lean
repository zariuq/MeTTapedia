import MeTTailCore
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# PeTTa Core/Spec Profile Bridge

Bridge the runtime-side `MeTTailCore` MeTTaIL syntax used by lowering and the
spec-side `Mettapedia.OSLF` MeTTaIL syntax used by the formal PeTTa semantics.

This file exists so program-level artifact export can be derived from the
formal PeTTa side without guessing about the runtime lowering format.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.ProfileBridge

abbrev CCollType := MeTTailCore.MeTTaIL.Syntax.CollType
abbrev SCollType := Mettapedia.OSLF.MeTTaIL.Syntax.CollType

abbrev CTypeExpr := MeTTailCore.MeTTaIL.Syntax.TypeExpr
abbrev STypeExpr := Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr

abbrev CPattern := MeTTailCore.MeTTaIL.Syntax.Pattern
abbrev SPattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

abbrev CFreshness := MeTTailCore.MeTTaIL.Syntax.FreshnessCondition
abbrev SFreshness := Mettapedia.OSLF.MeTTaIL.Syntax.FreshnessCondition

abbrev CPremise := MeTTailCore.MeTTaIL.Syntax.Premise
abbrev SPremise := Mettapedia.OSLF.MeTTaIL.Syntax.Premise

abbrev CRewriteRule := MeTTailCore.MeTTaIL.Syntax.RewriteRule
abbrev SRewriteRule := Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule

def coreToSpecCollType : CCollType → SCollType
  | .vec => .vec
  | .hashBag => .hashBag
  | .hashSet => .hashSet

def specToCoreCollType : SCollType → CCollType
  | .vec => .vec
  | .hashBag => .hashBag
  | .hashSet => .hashSet

def coreToSpecTypeExpr : CTypeExpr → STypeExpr
  | .base s => .base s
  | .arrow a b => .arrow (coreToSpecTypeExpr a) (coreToSpecTypeExpr b)
  | .multiBinder t => .multiBinder (coreToSpecTypeExpr t)
  | .collection ct t => .collection (coreToSpecCollType ct) (coreToSpecTypeExpr t)

def specToCoreTypeExpr : STypeExpr → CTypeExpr
  | .base s => .base s
  | .arrow a b => .arrow (specToCoreTypeExpr a) (specToCoreTypeExpr b)
  | .multiBinder t => .multiBinder (specToCoreTypeExpr t)
  | .collection ct t => .collection (specToCoreCollType ct) (specToCoreTypeExpr t)

def coreToSpecPattern : CPattern → SPattern
  | .bvar n => .bvar n
  | .fvar x => .fvar x
  | .apply c args => .apply c (args.map coreToSpecPattern)
  | .lambda body => .lambda (coreToSpecPattern body)
  | .multiLambda n body => .multiLambda n (coreToSpecPattern body)
  | .subst body repl => .subst (coreToSpecPattern body) (coreToSpecPattern repl)
  | .collection ct elems rest =>
      .collection (coreToSpecCollType ct) (elems.map coreToSpecPattern) rest

def specToCorePattern : SPattern → CPattern
  | .bvar n => .bvar n
  | .fvar x => .fvar x
  | .apply c args => .apply c (args.map specToCorePattern)
  | .lambda body => .lambda (specToCorePattern body)
  | .multiLambda n body => .multiLambda n (specToCorePattern body)
  | .subst body repl => .subst (specToCorePattern body) (specToCorePattern repl)
  | .collection ct elems rest =>
      .collection (specToCoreCollType ct) (elems.map specToCorePattern) rest

def coreToSpecFreshness (fc : CFreshness) : SFreshness :=
  { varName := fc.varName
    term := coreToSpecPattern fc.term }

def specToCoreFreshness (fc : SFreshness) : CFreshness :=
  { varName := fc.varName
    term := specToCorePattern fc.term }

def coreToSpecPremise : CPremise → SPremise
  | .freshness fc => .freshness (coreToSpecFreshness fc)
  | .congruence a b => .congruence (coreToSpecPattern a) (coreToSpecPattern b)
  | .relationQuery rel args => .relationQuery rel (args.map coreToSpecPattern)

def specToCorePremise : SPremise → CPremise
  | .freshness fc => .freshness (specToCoreFreshness fc)
  | .congruence a b => .congruence (specToCorePattern a) (specToCorePattern b)
  | .relationQuery rel args => .relationQuery rel (args.map specToCorePattern)

def coreToSpecRewriteRule (r : CRewriteRule) : SRewriteRule :=
  { name := r.name
    typeContext := r.typeContext.map (fun (x, t) => (x, coreToSpecTypeExpr t))
    premises := r.premises.map coreToSpecPremise
    left := coreToSpecPattern r.left
    right := coreToSpecPattern r.right }

def specToCoreRewriteRule (r : SRewriteRule) : CRewriteRule :=
  { name := r.name
    typeContext := r.typeContext.map (fun (x, t) => (x, specToCoreTypeExpr t))
    premises := r.premises.map specToCorePremise
    left := specToCorePattern r.left
    right := specToCorePattern r.right }

theorem collType_roundTrip (ct : CCollType) :
    specToCoreCollType (coreToSpecCollType ct) = ct := by
  cases ct <;> rfl

theorem typeExpr_roundTrip (t : CTypeExpr) :
    specToCoreTypeExpr (coreToSpecTypeExpr t) = t := by
  induction t with
  | base s =>
      rfl
  | arrow a b ihA ihB =>
      simp [coreToSpecTypeExpr, specToCoreTypeExpr, ihA, ihB]
  | multiBinder t ih =>
      simp [coreToSpecTypeExpr, specToCoreTypeExpr, ih]
  | collection ct t ih =>
      cases ct <;> simp [coreToSpecTypeExpr, specToCoreTypeExpr, ih, collType_roundTrip]

mutual

theorem pattern_roundTrip : (p : CPattern) →
    specToCorePattern (coreToSpecPattern p) = p
  | .bvar n =>
      by simp [coreToSpecPattern, specToCorePattern]
  | .fvar x =>
      by simp [coreToSpecPattern, specToCorePattern]
  | .apply c args => by
      simp [coreToSpecPattern, specToCorePattern, pattern_list_roundTrip]
  | .lambda body => by
      simp [coreToSpecPattern, specToCorePattern, pattern_roundTrip body]
  | .multiLambda n body => by
      simp [coreToSpecPattern, specToCorePattern, pattern_roundTrip body]
  | .subst body repl => by
      simp [coreToSpecPattern, specToCorePattern, pattern_roundTrip body, pattern_roundTrip repl]
  | .collection ct elems rest => by
      cases ct <;> simp [coreToSpecPattern, specToCorePattern, pattern_list_roundTrip, collType_roundTrip]

theorem pattern_list_roundTrip : (ps : List CPattern) →
    ps.map (specToCorePattern ∘ coreToSpecPattern) = ps
  | [] =>
      rfl
  | p :: ps => by
      simp [Function.comp, pattern_roundTrip p, pattern_list_roundTrip ps]

end

theorem freshness_roundTrip (fc : CFreshness) :
    specToCoreFreshness (coreToSpecFreshness fc) = fc := by
  cases fc
  simp [coreToSpecFreshness, specToCoreFreshness, pattern_roundTrip]

theorem premise_roundTrip (prem : CPremise) :
    specToCorePremise (coreToSpecPremise prem) = prem := by
  cases prem with
  | freshness fc =>
      simp [coreToSpecPremise, specToCorePremise, freshness_roundTrip]
  | congruence a b =>
      simp [coreToSpecPremise, specToCorePremise, pattern_roundTrip]
  | relationQuery rel args =>
      simp [coreToSpecPremise, specToCorePremise, pattern_list_roundTrip]

theorem rewriteRule_roundTrip (r : CRewriteRule) :
    specToCoreRewriteRule (coreToSpecRewriteRule r) = r := by
  cases r with
  | mk name typeContext premises left right =>
      have hTypes :
          typeContext.map
              ((fun x => (x.fst, specToCoreTypeExpr x.snd)) ∘
                fun x => (x.fst, coreToSpecTypeExpr x.snd)) = typeContext := by
        induction typeContext with
        | nil =>
            rfl
        | cons x xs ih =>
            cases x
            simp [Function.comp, typeExpr_roundTrip, ih]
      have hPremises :
          premises.map (specToCorePremise ∘ coreToSpecPremise) = premises := by
        induction premises with
        | nil =>
            rfl
        | cons prem prems ih =>
            simp [Function.comp, premise_roundTrip, ih]
      simp [coreToSpecRewriteRule, specToCoreRewriteRule, hTypes, hPremises,
        pattern_roundTrip]

theorem rewriteRule_list_roundTrip (rs : List CRewriteRule) :
    rs.map (specToCoreRewriteRule ∘ coreToSpecRewriteRule) = rs := by
  induction rs with
  | nil =>
      rfl
  | cons r rs ih =>
      simp [Function.comp, rewriteRule_roundTrip, ih]

end Mettapedia.Languages.MeTTa.PeTTa.ProfileBridge
