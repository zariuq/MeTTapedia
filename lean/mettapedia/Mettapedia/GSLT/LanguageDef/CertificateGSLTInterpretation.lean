import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpen

/-!
# Derivation-valued interpretations of CertificateGSLTs

Exact rule retention is useful but too restrictive: a primitive rule in one
presentation may be implemented by a composite derivation in another.  This
module defines the first non-thin category of CertificateGSLTs.  Its arrows preserve
the common judgment representation and map every admitted source rule
application to a target open derivation with the same ordered premises and
conclusion.

Composition is not proof irrelevance.  It recursively translates the first
open derivation and plugs the translated children into the rule template
provided by the second interpretation.  The category laws therefore follow
from the substitution laws of `OpenDerivation`.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- A judgment-preserving interpretation maps each concrete source rule
application to a target derivation from exactly the same ordered premises.
This is the common-`Pattern` fragment of the eventual syntax-translating
notion; unlike strict rule retention, a rule may map to a multi-node proof. -/
structure Interpretation (source target : Object) where
  onRule :
    ∀ (ruleInstance : RuleInstance) {premises : List Pattern}
      {conclusion : Pattern},
      RuleApplication source.presentation ruleInstance premises conclusion →
        OpenDerivation target.presentation premises conclusion

namespace Interpretation

mutual

/-- Translate an open derivation through a rule interpretation.  Premise
occurrence positions are retained exactly. -/
def mapOpen {source target : Object}
    (interpretation : Interpretation source target)
    {context : List Pattern} {goal : Pattern} :
    OpenDerivation source.presentation context goal →
      OpenDerivation target.presentation context goal
  | .assumption index => .assumption index
  | .byRule ruleInstance application children =>
      (interpretation.onRule ruleInstance application).bind
        (mapOpenList interpretation children)

/-- Translate an ordered vector of open derivations pointwise. -/
def mapOpenList {source target : Object}
    (interpretation : Interpretation source target)
    {context goals : List Pattern} :
    OpenDerivationList source.presentation context goals →
      OpenDerivationList target.presentation context goals
  | .nil => .nil
  | .cons head tail =>
      .cons (mapOpen interpretation head) (mapOpenList interpretation tail)

end

/-- Pointwise construction of an ordered vector commutes with
interpretation. -/
theorem mapOpenList_ofFn {source target : Object}
    (interpretation : Interpretation source target)
    {context goals : List Pattern}
    (entries : (index : Fin goals.length) →
      OpenDerivation source.presentation context (goals.get index)) :
    interpretation.mapOpenList (OpenDerivationList.ofFn goals entries) =
      OpenDerivationList.ofFn goals
        (fun index => interpretation.mapOpen (entries index)) := by
  induction goals with
  | nil => rfl
  | cons goal goals inductionHypothesis =>
      simp only [OpenDerivationList.ofFn, mapOpenList]
      congr
      exact inductionHypothesis (fun index => entries index.succ)

/-- Every interpretation retains premise occurrences as premise occurrences. -/
@[simp] theorem mapOpenList_assumptionEnvironment
    {source target : Object}
    (interpretation : Interpretation source target)
    (context : List Pattern) :
    interpretation.mapOpenList
        (assumptionEnvironment source.presentation context) =
      assumptionEnvironment target.presentation context := by
  rw [assumptionEnvironment, mapOpenList_ofFn]
  rfl

/-- The identity interpretation realizes a primitive rule by itself, with one
distinct hole for each ordered premise occurrence. -/
def id (object : Object) : Interpretation object object where
  onRule := fun ruleInstance _ _ application =>
    .byRule ruleInstance application
      (assumptionEnvironment object.presentation _)

/-- Interpret first into the middle presentation and then recursively
interpret the resulting open proof into the target. -/
def comp {first middle last : Object}
    (earlier : Interpretation first middle)
    (later : Interpretation middle last) :
    Interpretation first last where
  onRule := fun ruleInstance _ _ application =>
    later.mapOpen (earlier.onRule ruleInstance application)

/-- Exact rule retention embeds into derivation-valued interpretation by
using the transported primitive rule as a one-node template. -/
def ofRuleLookupRefines {source target : Object}
    (refines : RuleLookupRefines source.presentation target.presentation) :
    Interpretation source target where
  onRule := fun ruleInstance _ _ application =>
    .byRule ruleInstance (application.transport refines)
      (assumptionEnvironment target.presentation _)

mutual

/-- Interpreting commutes with plugging premise derivations into holes. -/
theorem mapOpen_bind {source target : Object}
    (interpretation : Interpretation source target)
    {sourceContext targetContext : List Pattern} {goal : Pattern}
    (derivation :
      OpenDerivation source.presentation sourceContext goal)
    (environment :
      OpenDerivationList source.presentation targetContext sourceContext) :
    interpretation.mapOpen (derivation.bind environment) =
      (interpretation.mapOpen derivation).bind
        (interpretation.mapOpenList environment) := by
  cases derivation with
  | assumption index =>
      simp only [OpenDerivation.bind, mapOpen]
      exact (mapOpenList_get interpretation environment index).symm
  | byRule ruleInstance application children =>
      simp only [OpenDerivation.bind, mapOpen]
      rw [OpenDerivation.bind_assoc]
      congr 1
      exact mapOpenList_bind interpretation children environment

/-- The same substitution naturality holds pointwise for ordered vectors. -/
theorem mapOpenList_bind {source target : Object}
    (interpretation : Interpretation source target)
    {sourceContext targetContext goals : List Pattern}
    (derivations :
      OpenDerivationList source.presentation sourceContext goals)
    (environment :
      OpenDerivationList source.presentation targetContext sourceContext) :
    interpretation.mapOpenList (derivations.bind environment) =
      (interpretation.mapOpenList derivations).bind
        (interpretation.mapOpenList environment) := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp only [OpenDerivationList.bind, mapOpenList]
      rw [mapOpen_bind interpretation head environment,
        mapOpenList_bind interpretation tail environment]

/-- Translation of ordered vectors commutes with position lookup. -/
theorem mapOpenList_get {source target : Object}
    (interpretation : Interpretation source target)
    {context goals : List Pattern}
    (derivations :
      OpenDerivationList source.presentation context goals)
    (index : Fin goals.length) :
    (interpretation.mapOpenList derivations).get index =
      interpretation.mapOpen (derivations.get index) := by
  cases derivations with
  | nil => exact Fin.elim0 index
  | cons head tail =>
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · rfl
      · exact mapOpenList_get interpretation tail tailIndex

end

mutual

/-- The identity interpretation is extensionally the identity on open
derivations. -/
@[simp] theorem id_mapOpen {object : Object} {context : List Pattern}
    {goal : Pattern}
    (derivation : OpenDerivation object.presentation context goal) :
    (id object).mapOpen derivation = derivation := by
  cases derivation with
  | assumption index => rfl
  | byRule ruleInstance application children =>
      simp only [mapOpen, id]
      change OpenDerivation.byRule ruleInstance application
          ((assumptionEnvironment object.presentation _).bind
            ((id object).mapOpenList children)) =
        OpenDerivation.byRule ruleInstance application children
      rw [id_mapOpenList children,
        OpenDerivationList.assumptionEnvironment_bind]

/-- Identity interpretation on ordered open derivation vectors. -/
@[simp] theorem id_mapOpenList {object : Object}
    {context goals : List Pattern}
    (derivations :
      OpenDerivationList object.presentation context goals) :
    (id object).mapOpenList derivations = derivations := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp only [mapOpenList]
      rw [id_mapOpen head, id_mapOpenList tail]

end

mutual

/-- Recursive translation respects interpretation composition. -/
theorem comp_mapOpen {first middle last : Object}
    (earlier : Interpretation first middle)
    (later : Interpretation middle last)
    {context : List Pattern} {goal : Pattern}
    (derivation :
      OpenDerivation first.presentation context goal) :
    (comp earlier later).mapOpen derivation =
      later.mapOpen (earlier.mapOpen derivation) := by
  cases derivation with
  | assumption index => rfl
  | byRule ruleInstance application children =>
      simp only [mapOpen, comp]
      rw [mapOpen_bind]
      change (later.mapOpen (earlier.onRule ruleInstance application)).bind
          ((comp earlier later).mapOpenList children) =
        (later.mapOpen (earlier.onRule ruleInstance application)).bind
          (later.mapOpenList (earlier.mapOpenList children))
      rw [comp_mapOpenList earlier later children]

/-- Composition is respected pointwise on ordered vectors. -/
theorem comp_mapOpenList {first middle last : Object}
    (earlier : Interpretation first middle)
    (later : Interpretation middle last)
    {context goals : List Pattern}
    (derivations :
      OpenDerivationList first.presentation context goals) :
    (comp earlier later).mapOpenList derivations =
      later.mapOpenList (earlier.mapOpenList derivations) := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp only [mapOpenList]
      rw [comp_mapOpen earlier later head,
        comp_mapOpenList earlier later tail]

end

/-- Interpret a closed derivation by viewing it as an open derivation over the
empty premise context and closing the translated result. -/
def mapDerivation {source target : Object}
    (interpretation : Interpretation source target) {goal : Pattern}
    (derivation : Derivation source.presentation goal) :
    Derivation target.presentation goal :=
  (interpretation.mapOpen
    (OpenDerivation.ofClosed (context := []) derivation)).close

@[simp] theorem id_mapDerivation {object : Object} {goal : Pattern}
    (derivation : Derivation object.presentation goal) :
    (id object).mapDerivation derivation = derivation := by
  simp [mapDerivation]

theorem comp_mapDerivation {first middle last : Object}
    (earlier : Interpretation first middle)
    (later : Interpretation middle last)
    {goal : Pattern} (derivation : Derivation first.presentation goal) :
    (comp earlier later).mapDerivation derivation =
      later.mapDerivation (earlier.mapDerivation derivation) := by
  simp only [mapDerivation, comp_mapOpen]
  rw [OpenDerivation.ofClosed_close]

@[ext] theorem ext {source target : Object}
    (first second : Interpretation source target)
    (equal : ∀ (ruleInstance : RuleInstance) {premises : List Pattern}
      {conclusion : Pattern}
      (application : RuleApplication source.presentation ruleInstance
        premises conclusion),
      first.onRule ruleInstance application =
        second.onRule ruleInstance application) :
    first = second := by
  cases first with
  | mk firstRule =>
      cases second with
      | mk secondRule =>
          congr
          funext ruleInstance premises conclusion application
          exact equal ruleInstance application

end Interpretation

/-! ## The non-thin category of proof presentations -/

instance : Category Object where
  Hom := Interpretation
  id := Interpretation.id
  comp := Interpretation.comp
  id_comp interpretation := by
    apply Interpretation.ext
    intro ruleInstance premises conclusion application
    simp only [Interpretation.comp, Interpretation.mapOpen,
      Interpretation.id]
    rw [Interpretation.mapOpenList_assumptionEnvironment,
      OpenDerivation.bind_assumptionEnvironment]
  comp_id interpretation := by
    apply Interpretation.ext
    intro ruleInstance premises conclusion application
    exact Interpretation.id_mapOpen
      (interpretation.onRule ruleInstance application)
  assoc first second third := by
    apply Interpretation.ext
    intro ruleInstance premises conclusion application
    exact (Interpretation.comp_mapOpen second third
      (first.onRule ruleInstance application)).symm

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
