import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Completeness
import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations

/-!
# The reference relation and the static theory of restriction blocks

Over any calculus with restriction (`BlockLanguage`): the generators of its static theory by their shapes
(`BlockGenerator`), every generator has one (`generator_shape`), and the reference relation's equation steps are the
static theory's (`equationStep_iff`). Extrusion at any member of a bag is an instance of the declared law
(`extrusion_instance_at`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Prenex
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationGenerator EquationInstanceAt DerivedInstance
  extendClosed_closedRoot readsRaw)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.OSLF.MeTTaIL.Match (applyBindings)

variable {language : LanguageDef} {block : Block}

/-! ## The generators by shape -/

variable [laws : BlockLanguage language block]

/-- **The generators of the static theory, by shape**: ν of inaction both ways, extrusion both ways, exchange, the
empty multisets both ways, and the bag laws. -/
inductive BlockGenerator (language : LanguageDef) (block : Block) : Pattern → Pattern → Prop where
  | nil (binder : Option String) :
      BlockGenerator language block (.apply block.restrict [.lambda binder (.apply block.unit [])]) (.apply block.unit [])
  | nilReverse : BlockGenerator language block (.apply block.unit []) (.apply block.restrict [.lambda none (.apply block.unit [])])
  | extrusion (members : List Pattern) (selected : Nat) (binder : Option String) (body : Pattern)
      (inside : selected < members.length) (chosen : members[selected] = .apply block.restrict [.lambda binder body]) :
      BlockGenerator language block (.collection .hashBag members none)
        (.apply block.restrict [.lambda none (.collection .hashBag
          (body :: (members.eraseIdx selected).map (liftBVars 0 1)) none)])
  | extrusionReverse (binder : Option String) (members : List Pattern) (selected : Nat) (originals : List Pattern)
      (inside : selected < members.length) (othersEq : members.eraseIdx selected = originals.map (liftBVars 0 1)) :
      BlockGenerator language block (.apply block.restrict [.lambda binder (.collection .hashBag members none)])
        (.collection .hashBag (.apply block.restrict [.lambda none members[selected]] :: originals) none)
  | exchange (outerBinder innerBinder : Option String) (body : Pattern) :
      BlockGenerator language block (.apply block.restrict [.lambda outerBinder (.apply block.restrict [.lambda innerBinder body])])
        (.apply block.restrict [.lambda none (.apply block.restrict [.lambda none (rename swapInner body)])])
  | emptyUnit (label : String) (listed : label ∈ block.emptyUnits) :
      BlockGenerator language block (.apply label [.collection .hashBag [] none])
        (.apply block.restrict [.lambda none (.apply block.unit [])])
  | emptyUnitReverse (label : String) (listed : label ∈ block.emptyUnits) (binder : Option String) :
      BlockGenerator language block (.apply block.restrict [.lambda binder (.apply block.unit [])])
        (.apply label [.collection .hashBag [] none])
  | derived {source target : Pattern} (derivedInstance : DerivedInstance language source target) :
      BlockGenerator language block source target

omit laws in
/-- **A raw instance of a law of the blocks has a block shape**, read forward: ν of inaction is the only raw one. -/
theorem blockLaw_raw_forward {equation : Equation} {source target : Pattern}
    {initial final : Mettapedia.OSLF.MeTTaIL.Match.Bindings} (law : equation ∈ blockLaws block)
    (raw : readsRaw equation = true) (matched : initial ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern equation.left source)
    (applied : applyBindings final equation.right = target) : BlockGenerator language block source target := by
  rw [mem_blockLaws] at law
  rcases law with rfl | rfl | rfl | ⟨label, listed, rfl⟩
  · obtain ⟨binder, rfl⟩ := restrictionNil_raw matched
    have targetIs : target = .apply block.unit [] := by
      rw [← applied]
      simp [restrictionNilOf, applyBindings]
    rw [targetIs]
    exact .nil binder
  · exact absurd raw (fun same => Bool.false_ne_true same)
  · exact absurd raw (fun same => Bool.false_ne_true same)
  · exact absurd raw (fun same => Bool.false_ne_true same)

omit laws in
/-- **A raw instance of a law of the blocks has a block shape**, read backward. -/
theorem blockLaw_raw_reverse {equation : Equation} {source target : Pattern}
    {initial final : Mettapedia.OSLF.MeTTaIL.Match.Bindings} (law : equation ∈ blockLaws block)
    (raw : readsRaw equation = true) (matched : initial ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern equation.right source)
    (applied : applyBindings final equation.left = target) : BlockGenerator language block source target := by
  rw [mem_blockLaws] at law
  rcases law with rfl | rfl | rfl | ⟨label, listed, rfl⟩
  · rw [restrictionNil_raw_right matched]
    have targetIs : target = .apply block.restrict [.lambda none (.apply block.unit [])] := by
      rw [← applied]
      simp [restrictionNilOf, applyBindings]
    rw [targetIs]
    exact .nilReverse
  · exact absurd raw (fun same => Bool.false_ne_true same)
  · exact absurd raw (fun same => Bool.false_ne_true same)
  · exact absurd raw (fun same => Bool.false_ne_true same)

omit laws in
/-- **An instance of a law of the blocks with binders has a block shape**: exchange, extrusion or an empty
multiset, either way. -/
theorem blockLaw_declared {base : BasePremiseEvaluator} {fuel : Nat} {equation : Equation}
    {orientation : Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution.Orientation} {ambient : Nat} {source target : Pattern}
    (law : equation ∈ blockLaws block) (notRaw : readsRaw equation = false)
    (declared : Mettapedia.GSLT.LanguageDef.EquationSemantics.DeclaredInstanceAt base language fuel ambient equation
      orientation source target) : BlockGenerator language block source target := by
  obtain ⟨spec, captured, final, bound, _, sourceScoped, matched, premises, applied, _⟩ := declared
  rw [mem_blockLaws] at law
  rcases law with rfl | rfl | rfl | ⟨label, listed, rfl⟩
  · exact absurd notRaw (fun same => Bool.noConfusion same)
  · have premisesNil : (restrictionExchangeOf block).premises = [] := rfl
    rw [premisesNil] at premises
    cases premises
    rw [extendClosed_closedRoot] at applied
    cases orientation with
    | forward =>
        obtain ⟨outer, inner, body, rfl, rfl⟩ := exchange_forward_shape bound sourceScoped matched applied
        exact .exchange outer inner body
    | reverse =>
        obtain ⟨outer, inner, body, rfl, rfl⟩ := exchange_reverse_shape bound sourceScoped matched applied
        exact .exchange outer inner body
  · have premisesNil : (scopeExtrusionOf block).premises = [] := rfl
    rw [premisesNil] at premises
    cases premises
    rw [extendClosed_closedRoot] at applied
    cases orientation with
    | forward =>
        obtain ⟨members, selected, binder, body, inside, chosen, rfl, rfl⟩ :=
          extrusion_forward_shape bound sourceScoped matched applied
        exact .extrusion members selected binder body inside chosen
    | reverse =>
        obtain ⟨binder, members, selected, originals, inside, othersEq, rfl, rfl⟩ :=
          extrusion_reverse_shape bound sourceScoped matched applied
        exact .extrusionReverse binder members selected originals inside othersEq
  · have premisesNil : (emptyUnitOf block label).premises = [] := rfl
    rw [premisesNil] at premises
    cases premises
    rw [extendClosed_closedRoot] at applied
    cases orientation with
    | forward =>
        obtain ⟨rfl, rfl⟩ := emptyUnit_forward_shape matched applied
        exact .emptyUnit label listed
    | reverse =>
        obtain ⟨⟨binder, rfl⟩, rfl⟩ := emptyUnit_reverse_shape matched applied
        exact .emptyUnitReverse label listed binder

/-- **Every generator of the static theory has one of the shapes.** -/
theorem generator_shape {base : BasePremiseEvaluator} {source target : Pattern}
    (generator : EquationGenerator base language source target) : BlockGenerator language block source target := by
  rcases generator with ⟨_, equationInstance⟩ | derived
  · cases equationInstance with
    | forward member raw matched _ applied =>
        exact blockLaw_raw_forward (laws.equations ▸ member) raw matched applied
    | reverse member raw matched _ applied =>
        exact blockLaw_raw_reverse (laws.equations ▸ member) raw matched applied
    | declared member notRaw declared => exact blockLaw_declared (laws.equations ▸ member) notRaw declared
  · exact .derived derived

/-! ## The reference relation and the canonical relation agree on π -/

open Mettapedia.OSLF.MeTTaIL.ReferenceStep (AuthoredEquation PremisesValid)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationInstance EquationContextStep
  declaredInstanceAt_iff_applyEquationAt)
open Mettapedia.OSLF.MeTTaIL.Match (applyBindingsScoped applyBindingsScopedList)

include laws in
theorem premises_nil {equation : Equation} (member : equation ∈ language.equations) : equation.premises = [] := by
  rcases laws.equations_mem member with rfl | rfl | rfl | ⟨label, listed, rfl⟩ <;> rfl

include laws in
/-- **An authored instance of the reference relation is an instance of the canonical relation**, for π. -/
theorem authored_iff_instance (relEnv : RelationEnv) (base : BasePremiseEvaluator) {source target : Pattern} :
    AuthoredEquation relEnv language source target ↔ EquationInstance base language source target := by
  constructor
  · intro authored
    cases authored with
    | forward member raw matched premises =>
        rw [premises_nil (block := block) member] at premises
        cases premises
        rcases laws.equations_mem member with rfl | rfl | rfl | ⟨label, listed, rfl⟩
        · exact ⟨0, .forward member raw matched (.nil _) (by simp [restrictionNilOf, applyBindings])⟩
        · exact absurd raw (fun same => Bool.false_ne_true same)
        · exact absurd raw (fun same => Bool.false_ne_true same)
        · exact absurd raw (fun same => Bool.false_ne_true same)
    | reverse member raw matched premises =>
        rw [premises_nil (block := block) member] at premises
        cases premises
        rcases laws.equations_mem member with rfl | rfl | rfl | ⟨label, listed, rfl⟩
        · exact ⟨0, .reverse member raw matched (.nil _)
            (by simp [restrictionNilOf, applyBindings, applyBindingsScoped, applyBindingsScopedList])⟩
        · exact absurd raw (fun same => Bool.false_ne_true same)
        · exact absurd raw (fun same => Bool.false_ne_true same)
        · exact absurd raw (fun same => Bool.false_ne_true same)
    | declared member notRaw applied =>
        exact ⟨0, .declared member notRaw
          ((declaredInstanceAt_iff_applyEquationAt (premises_nil (block := block) member)).mpr applied)⟩
    | premised member _ premised _ => exact absurd (premises_nil (block := block) member) premised
  · rintro ⟨_, equationInstance⟩
    cases equationInstance with
    | forward member raw matched premises applied =>
        rw [premises_nil (block := block) member] at premises
        cases premises
        rcases laws.equations_mem member with rfl | rfl | rfl | ⟨label, listed, rfl⟩
        · rw [← applied]
          have rebuilt := AuthoredEquation.forward (relEnv := relEnv) (witnesses := []) member raw matched (.nil _)
          simpa [restrictionNilOf, applyBindings, applyBindingsScoped, applyBindingsScopedList] using rebuilt
        · exact absurd raw (fun same => Bool.false_ne_true same)
        · exact absurd raw (fun same => Bool.false_ne_true same)
        · exact absurd raw (fun same => Bool.false_ne_true same)
    | reverse member raw matched premises applied =>
        rw [premises_nil (block := block) member] at premises
        cases premises
        rcases laws.equations_mem member with rfl | rfl | rfl | ⟨label, listed, rfl⟩
        · rw [← applied]
          have rebuilt := AuthoredEquation.reverse (relEnv := relEnv) (witnesses := []) member raw matched (.nil _)
          simpa [restrictionNilOf, applyBindings, applyBindingsScoped, applyBindingsScopedList] using rebuilt
        · exact absurd raw (fun same => Bool.false_ne_true same)
        · exact absurd raw (fun same => Bool.false_ne_true same)
        · exact absurd raw (fun same => Bool.false_ne_true same)
    | declared member notRaw declared =>
        exact .declared member notRaw ((declaredInstanceAt_iff_applyEquationAt (premises_nil (block := block) member)).mp declared)

include laws in
/-- **the reference equation steps are its canonical equation steps.** -/
theorem equationStep_iff (relEnv : RelationEnv) (base : BasePremiseEvaluator) {first second : Pattern} :
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.EquationStep relEnv language first second ↔
      EquationContextStep base language first second := by
  constructor
  · rintro ⟨context, generator⟩
    rcases generator with authored | derived
    · exact .inContext context (.inl ((authored_iff_instance (block := block) relEnv base).mp authored))
    · exact .inContext context (.inr derived)
  · rintro ⟨context, generator⟩
    rcases generator with equationInstance | derived
    · exact .inContext context (.inl ((authored_iff_instance (block := block) relEnv base).mpr equationInstance))
    · exact .inContext context (.inr derived)

/-! ## The shapes are instances -/

open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.RuleBinding (arguments? dependencies? occurrenceDeclared sitePattern? occurrenceAt?)
open Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution (Orientation orientedRule applyEquationAt mem_applyEquationAt_iff)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVarsList_eq_map)

omit laws in
/-- **Extrusion at any member of a bag, read through its declaration.** -/
theorem extrusion_instance_at {ambient : Nat} {members : List Pattern} {selected : Nat}
    (inside : selected < members.length) {body : Pattern}
    (chosen : members[selected] = .apply block.restrict [.lambda none body])
    (bodyScoped : body.isWellScopedAt (1 + ambient) = true)
    (othersScoped : (Pattern.collection .hashBag (members.eraseIdx selected) none).isWellScopedAt ambient = true)
    (membersScoped : (Pattern.collection .hashBag members none).isWellScopedAt ambient = true) :
    .apply block.restrict [.lambda none (.collection .hashBag
        (body :: (members.eraseIdx selected).map (liftBVars 0 1)) none)] ∈
      applyEquationAt language ambient (scopeExtrusionOf block) .forward (.collection .hashBag members none) := by
  have liftedScoped : (Pattern.collection .hashBag ((members.eraseIdx selected).map (liftBVars 0 1)) none
      ).isWellScopedAt (1 + ambient) = true := by
    have lifted := Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_isWellScopedAt (cutoff := 0) (shift := 1)
      (ambient := ambient) (pattern := .collection .hashBag (members.eraseIdx selected) none)
      (by simpa using othersScoped)
    simpa [liftBVars, liftBVarsList_eq_map, Nat.add_comm] using lifted
  have liftedList : Pattern.isWellScopedListAt (1 + ambient) ((members.eraseIdx selected).map (liftBVars 0 1)) =
      true := by
    simpa [Pattern.isWellScopedAt] using liftedScoped
  have bodyScoped' : body.isWellScopedAt (ambient + 1) = true := by rwa [Nat.add_comm]
  have liftedList' : Pattern.isWellScopedListAt (ambient + 1) ((members.eraseIdx selected).map (liftBVars 0 1)) =
      true := by
    rwa [Nat.add_comm]
  rw [mem_applyEquationAt_iff]
  refine ⟨rfl, ?_, ?_, _, [("rest", ⟨[], ambient, .collection .hashBag (members.eraseIdx selected) none⟩),
    ("P", ⟨[.base block.name], ambient, body⟩)], rfl, rfl, ?_, ?_⟩
  · exact membersScoped
  · simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, bodyScoped', liftedList']
  · simp only [matchRuleAt, matchRuleWithAt]
    refine mem_matchAtWith_bag.mpr ⟨_, rfl, mem_matchBagAtWith_cons.mpr
      ⟨.apply block.restrict [.lambda none body], selected,
        List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem inside, chosen]),
        [("P", ⟨[.base block.name], ambient, body⟩)], ?_, ?_⟩⟩
    · refine mem_matchAtWith_apply.mpr ⟨_, rfl, mem_matchArgsAtWith_cons.mpr
        ⟨_, [], _, rfl, mem_matchAtWith_lambda.mpr ⟨none, body, rfl, mem_matchAtWith_fvar.mpr ?_⟩,
          mem_matchArgsAtWith_nil.mpr ⟨rfl, rfl⟩⟩⟩
      simp [captureWith?_literal, capture?, orientedRule, scopeExtrusionOf, dependencies?, arguments?,
        occurrenceDeclared, sitePattern?, occurrenceAt?, recoverValue?_one bodyScoped, assign, lookup]
    · refine mem_matchBagAtWith_rest.mpr ?_
      simp [captureRestWith?_literal, captureRest?, capture?, orientedRule, scopeExtrusionOf, dependencies?,
        arguments?, occurrenceDeclared, sitePattern?, occurrenceAt?, recoverValue?_zero othersScoped, assign,
        lookup]
  · simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, orientedRule, scopeExtrusionOf,
      arguments?, dependencies?, occurrenceDeclared, sitePattern?, occurrenceAt?, lookup,
      instantiateValue?_one bodyScoped, instantiateValue?_shift othersScoped, liftBVars, liftBVarsList_eq_map]
end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
