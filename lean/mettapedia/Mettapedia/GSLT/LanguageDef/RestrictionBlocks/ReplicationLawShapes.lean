import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationKeeps
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Substitution

/-!
# The laws of a calculus with replication, by shape

Every instance of a law of a calculus with restriction and replication, read raw or with its binders, and every law
of its bag relates terms of one of a few shapes, one way or the other (`generator_lawShape`): ν of inaction, exchange,
extrusion both ways, an empty named multiset, the five laws of replication (a raw match may leave a tail on a bag),
and the laws of the bag. Each shape keeps the object reading's canonical block (`LawShape.keeps`), and a substitution
of terms that are no abstractions keeps each shape (`LawShape.substituted`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute lift lift_lift substituteList_eq_map)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted (hasType_collection_inversion)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationGenerator EquationInstanceAt DerivedInstance
  extendClosed_closedRoot readsRaw)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator PremisesAt)
open Mettapedia.OSLF.MeTTaIL.Match (applyBindings)

variable {block : ReplicationBlock}

/-- **The shapes of the laws**, one orientation each: ν of inaction, exchange, extrusion both ways, an empty named
multiset, the laws of replication (their bags as a raw match finds them, perhaps with a tail), and the laws of the
bag. -/
inductive LawShape (block : ReplicationBlock) : Pattern → Pattern → Prop where
  | restrictionNil (binder : Option String) :
      LawShape block (.apply block.restrict [.lambda binder (.apply block.unit [])]) (.apply block.unit [])
  | exchange (outerBinder innerBinder : Option String) (body : Pattern) :
      LawShape block (.apply block.restrict [.lambda outerBinder (.apply block.restrict [.lambda innerBinder body])])
        (.apply block.restrict [.lambda none (.apply block.restrict [.lambda none (rename swapInner body)])])
  | extrusion {members : List Pattern} {selected : Nat} (inside : selected < members.length)
      {binder : Option String} {body : Pattern} (chosen : members[selected] = .apply block.restrict [.lambda binder body]) :
      LawShape block (.collection .hashBag members none)
        (.apply block.restrict [.lambda none (.collection .hashBag
          (body :: (members.eraseIdx selected).map (liftBVars 0 1)) none)])
  | extrusionReverse {binder : Option String} {members : List Pattern} {selected : Nat}
      (inside : selected < members.length) {originals : List Pattern}
      (erased : members.eraseIdx selected = originals.map (liftBVars 0 1)) :
      LawShape block (.apply block.restrict [.lambda binder (.collection .hashBag members none)])
        (.collection .hashBag (.apply block.restrict [.lambda none members[selected]] :: originals) none)
  | emptyUnit {label : String} (listed : label ∈ block.emptyUnits) (binder : Option String) :
      LawShape block (.apply label [.collection .hashBag [] none])
        (.apply block.restrict [.lambda binder (.apply block.unit [])])
  | unfold (process : Pattern) (rest : Option String) :
      LawShape block (.collection .hashBag [process, .apply block.replicate [process]] rest)
        (.apply block.replicate [process])
  | unfoldSwap (process : Pattern) (rest : Option String) :
      LawShape block (.collection .hashBag [.apply block.replicate [process], process] rest)
        (.apply block.replicate [process])
  | replicationNil : LawShape block (.apply block.replicate [.apply block.unit []]) (.apply block.unit [])
  | twice (process : Pattern) :
      LawShape block (.apply block.replicate [.apply block.replicate [process]]) (.apply block.replicate [process])
  | par (first second : Pattern) (rest : Option String) (swapped : Bool) :
      LawShape block
        (.apply block.replicate [.collection .hashBag (if swapped then [second, first] else [first, second]) rest])
        (.collection .hashBag [.apply block.replicate [first], .apply block.replicate [second]] none)
  | parReverse (first second : Pattern) (rest : Option String) (swapped : Bool) :
      LawShape block
        (.collection .hashBag (if swapped then [.apply block.replicate [second], .apply block.replicate [first]]
          else [.apply block.replicate [first], .apply block.replicate [second]]) rest)
        (.apply block.replicate [.collection .hashBag [first, second] none])
  | idempotent (process : Pattern) (rest : Option String) :
      LawShape block (.collection .hashBag [.apply block.replicate [process], .apply block.replicate [process]] rest)
        (.apply block.replicate [process])
  | bagPerm {first second : List Pattern} (permutation : first.Perm second) :
      LawShape block (.collection .hashBag first none) (.collection .hashBag second none)
  | flatten (pre inner post : List Pattern) :
      LawShape block (.collection .hashBag (pre ++ .collection .hashBag inner none :: post) none)
        (.collection .hashBag (pre ++ inner ++ post) none)
  | singleton {element : Pattern} (notLambda : ∀ binder body, element ≠ .lambda binder body) :
      LawShape block (.collection .hashBag [element] none) element
  | unitElim (pre post : List Pattern) :
      LawShape block (.collection .hashBag (pre ++ .apply block.unit [] :: post) none)
        (.collection .hashBag (pre ++ post) none)
  | emptyBag : LawShape block (.collection .hashBag [] none) (.apply block.unit [])

/-! ## Each shape keeps the object reading's canonical block -/

/-- **Each shape keeps** pending substitutions, binding restrictions and the object reading's canonical block. -/
theorem LawShape.keeps (multisetFresh : block.replicate ∉ block.multisets) (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) (unitFresh : block.unit ≠ block.restrict)
    (restrictNotEmpty : block.restrict ∉ block.emptyUnits) {source target : Pattern}
    (shape : LawShape block source target) : Keeps block source target := by
  cases shape with
  | restrictionNil binder => exact restrictionNil_keeps unitFresh binder
  | exchange outerBinder innerBinder body => exact exchange_keeps multisetFresh fresh restrictFresh outerBinder innerBinder body
  | extrusion inside chosen => exact extrusion_keeps multisetFresh fresh restrictFresh inside chosen
  | extrusionReverse inside erased => exact extrusion_reverse_keeps multisetFresh fresh restrictFresh inside erased
  | emptyUnit listed binder => exact emptyUnit_keeps fresh unitFresh restrictNotEmpty listed binder
  | unfold process rest => exact unfold_keeps multisetFresh fresh restrictFresh process rest
  | unfoldSwap process rest => exact unfold_keeps_swap multisetFresh fresh restrictFresh process rest
  | replicationNil => exact replicationNil_keeps restrictFresh unitFresh
  | twice process => exact twice_keeps multisetFresh fresh restrictFresh process
  | par first second rest swapped => exact replicationPar_keeps multisetFresh fresh restrictFresh first second rest swapped
  | parReverse first second rest swapped =>
      exact replicationPar_keeps_reverse multisetFresh fresh restrictFresh first second rest swapped
  | idempotent process rest => exact idempotent_keeps multisetFresh fresh restrictFresh process rest
  | bagPerm permutation => exact bagPerm_keeps fresh restrictFresh permutation
  | flatten pre inner post => exact flatten_keeps fresh restrictFresh pre inner post
  | singleton notLambda => exact singleton_keeps fresh restrictFresh notLambda
  | unitElim pre post => exact unitElim_keeps unitFresh pre post
  | emptyBag => exact emptyBag_keeps unitFresh

/-! ## Substitution keeps each shape -/

/-- An assignment of terms that are no abstractions. -/
def NoAbstractions (assignment : Assignment) : Prop := ∀ index binder body, assignment index ≠ .lambda binder body

theorem NoAbstractions.lift {assignment : Assignment} (plain : NoAbstractions assignment) (arity : Nat) :
    NoAbstractions (lift arity assignment) := by
  intro index binder body
  unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
  split
  · exact fun same => Pattern.noConfusion same
  · intro same
    cases assigned : assignment (index - arity) with
    | lambda binder' body' => exact plain _ binder' body' assigned
    | _ => rw [assigned] at same; simp [liftBVars] at same

/-- **A substitution of terms that are no abstractions makes no abstraction of a term that is none.** -/
theorem substitute_notLambda {assignment : Assignment} (plain : NoAbstractions assignment) {pattern : Pattern}
    (notLambda : ∀ binder body, pattern ≠ .lambda binder body) :
    ∀ binder body, substitute assignment pattern ≠ .lambda binder body := by
  intro binder body same
  cases pattern with
  | bvar index => exact plain index binder body same
  | lambda binder' body' => exact notLambda binder' body' rfl
  | fvar => simp [substitute] at same
  | apply => simp [substitute] at same
  | multiLambda => simp [substitute] at same
  | subst => simp [substitute] at same
  | collection => simp [substitute] at same

theorem substitute_replicate (assignment : Assignment) (process : Pattern) :
    substitute assignment (.apply block.replicate [process]) = .apply block.replicate [substitute assignment process] := by
  simp [substitute, substituteList_eq_map]

/-- **Substitution keeps each shape**, the assignment lifted past each binder of the shape. -/
theorem LawShape.substituted (assignment : Assignment) (plain : NoAbstractions assignment) {source target : Pattern}
    (shape : LawShape block source target) :
    LawShape block (substitute assignment source) (substitute assignment target) := by
  cases shape with
  | restrictionNil binder =>
      rw [substitute_restriction (block := block.toBlock), substitute_inaction (block := block.toBlock),
        substitute_inaction (block := block.toBlock)]
      exact .restrictionNil binder
  | exchange outerBinder innerBinder body =>
      rw [substitute_restriction (block := block.toBlock), substitute_restriction (block := block.toBlock),
        substitute_restriction (block := block.toBlock), substitute_restriction (block := block.toBlock), lift_lift,
        substitute_swapInner]
      exact .exchange outerBinder innerBinder _
  | @extrusion members selected inside binder body chosen =>
      rw [substitute_bag, substitute_restriction (block := block.toBlock),
        substitute_bag, List.map_cons, List.map_map]
      have inside' : selected < (members.map (substitute assignment)).length := by simpa using inside
      have chosen' : (members.map (substitute assignment))[selected] =
          .apply block.restrict [.lambda binder (substitute (lift 1 assignment) body)] := by
        rw [List.getElem_map]
        simp only [chosen, substitute_restriction (block := block.toBlock)]
      have shape := LawShape.extrusion (block := block) inside' chosen'
      rw [map_eraseIdx, List.map_map] at shape
      have commute : substitute (lift 1 assignment) ∘ liftBVars 0 1 = liftBVars 0 1 ∘ substitute assignment :=
        funext (substitute_lift_one assignment)
      rw [commute]
      exact shape
  | @extrusionReverse binder members selected inside originals erased =>
      rw [substitute_restriction (block := block.toBlock), substitute_bag,
        substitute_bag, List.map_cons, substitute_restriction (block := block.toBlock)]
      have inside' : selected < (members.map (substitute (lift 1 assignment))).length := by simpa using inside
      have erased' : (members.map (substitute (lift 1 assignment))).eraseIdx selected =
          (originals.map (substitute assignment)).map (liftBVars 0 1) := by
        rw [map_eraseIdx, erased, List.map_map, List.map_map]
        exact List.map_congr_left fun original _ => substitute_lift_one assignment original
      have shape := LawShape.extrusionReverse (block := block) (binder := binder) inside' erased'
      simpa only [List.getElem_map, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_zero] using shape
  | @emptyUnit label listed binder =>
      have emptyIs : substitute assignment (.apply label [.collection .hashBag [] none]) =
          .apply label [.collection .hashBag [] none] := by simp [substitute, substituteList_eq_map]
      rw [emptyIs, substitute_restriction (block := block.toBlock), substitute_inaction (block := block.toBlock)]
      exact .emptyUnit listed binder
  | unfold process rest =>
      simp only [substitute_bag, List.map_cons, List.map_nil, substitute_replicate]
      exact .unfold _ rest
  | unfoldSwap process rest =>
      simp only [substitute_bag, List.map_cons, List.map_nil, substitute_replicate]
      exact .unfoldSwap _ rest
  | replicationNil =>
      simp only [substitute_replicate, substitute_inaction (block := block.toBlock)]
      exact .replicationNil
  | twice process =>
      simp only [substitute_replicate]
      exact .twice _
  | par first second rest swapped =>
      cases swapped <;>
        simp only [substitute_replicate, substitute_bag, List.map_cons, List.map_nil,
          Bool.false_eq_true, if_false, if_true] <;>
        first
          | exact .par (substitute assignment first) (substitute assignment second) rest false
          | exact .par (substitute assignment first) (substitute assignment second) rest true
  | parReverse first second rest swapped =>
      cases swapped <;>
        simp only [substitute_replicate, substitute_bag, List.map_cons, List.map_nil,
          Bool.false_eq_true, if_false, if_true] <;>
        first
          | exact .parReverse (substitute assignment first) (substitute assignment second) rest false
          | exact .parReverse (substitute assignment first) (substitute assignment second) rest true
  | idempotent process rest =>
      simp only [substitute_bag, List.map_cons, List.map_nil, substitute_replicate]
      exact .idempotent _ rest
  | bagPerm permutation =>
      rw [substitute_bag, substitute_bag]
      exact .bagPerm (permutation.map _)
  | flatten pre inner post =>
      rw [substitute_bag, substitute_bag, List.map_append,
        List.map_cons, substitute_bag, List.map_append, List.map_append]
      exact .flatten _ _ _
  | singleton notLambda =>
      rw [substitute_bag, List.map_cons, List.map_nil]
      exact .singleton (substitute_notLambda plain notLambda)
  | unitElim pre post =>
      rw [substitute_bag, substitute_bag, List.map_append,
        List.map_cons, substitute_inaction (block := block.toBlock), List.map_append]
      exact .unitElim _ _
  | emptyBag =>
      rw [substitute_bag, substitute_inaction (block := block.toBlock), List.map_nil]
      exact .emptyBag

/-! ## Every generator has a shape -/

section Language

variable {language : LanguageDef} [laws : ReplicationLanguage language block]

include laws in
theorem replicate_not_multiset : block.replicate ∉ block.multisets := laws.replicateFresh.2.2

include laws in
theorem replicate_ne_restrict : block.replicate ≠ block.restrict := laws.replicateFresh.2.1

include laws in
theorem replicate_not_emptyUnit : block.replicate ∉ block.emptyUnits := fun listed =>
  laws.replicateFresh.2.2 (laws.emptyUnitShape _ listed).1

include laws in
/-- **The unit is no restriction**: it takes no argument, and the restriction takes one. -/
theorem unit_ne_restrict : block.unit ≠ block.restrict := by
  intro same
  obtain ⟨bag, presented, -⟩ := laws.bag
  obtain ⟨unitRule, member, labelIs, -, params⟩ := presented.unitAuthored
  obtain ⟨-, parameterName, restrictParams⟩ := laws.restrictShape unitRule member (labelIs.trans same)
  rw [params] at restrictParams
  cases restrictParams

include laws in
/-- **The laws of a calculus with restriction and replication**, one by one. -/
theorem replicationLaws_cases {equation : Equation} (member : List.Mem equation language.equations) :
    equation = restrictionNilOf block.toBlock ∨ equation = restrictionExchangeOf block.toBlock ∨
      equation = scopeExtrusionOf block.toBlock ∨
      (∃ label ∈ block.emptyUnits, equation = emptyUnitOf block.toBlock label) ∨
      equation = replicationUnfoldOf block ∨ equation = replicationNilOf block ∨
      equation = replicationTwiceOf block ∨ equation = replicationParOf block ∨
      equation = replicationIdempotentOf block := by
  have inLaws : equation ∈ replicationBlockLaws block := laws.equations ▸ member
  rcases mem_replicationBlockLaws.mp inLaws with inBlock | inReplication
  · simp only [blockLaws, List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at inBlock
    rcases inBlock with rfl | rfl | rfl | ⟨label, listed, rfl⟩
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr (.inl ⟨label, listed, rfl⟩)))
  · simp only [replicationLaws, List.mem_cons, List.not_mem_nil, or_false] at inReplication
    rcases inReplication with rfl | rfl | rfl | rfl | rfl
    · exact .inr (.inr (.inr (.inr (.inl rfl))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl)))))))

/-- A raw instance of a law without premises instantiates the other side with the match's bindings. -/
theorem final_of_premises_nil {base : BasePremiseEvaluator} {fuel : Nat}
    {initial final : Mettapedia.OSLF.MeTTaIL.Match.Bindings} {equation : Equation} (none : equation.premises = [])
    (premises : PremisesAt base language fuel initial equation.premises final) : final = initial := by
  rw [none] at premises
  cases premises
  rfl

include laws in
/-- **Every authored instance has a shape**, one way or the other. -/
theorem instance_lawShape {base : BasePremiseEvaluator} {fuel : Nat} {source target : Pattern}
    (equationInstance : EquationInstanceAt base language fuel source target) :
    LawShape block source target ∨ LawShape block target source := by
  cases equationInstance with
  | forward member raw matched premises applied =>
      rcases replicationLaws_cases (block := block) member with
        rfl | rfl | rfl | ⟨label, listed, rfl⟩ | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨binder, rfl⟩ := restrictionNil_raw matched
        have targetIs : target = .apply block.unit [] := by
          rw [← applied]
          simp [restrictionNilOf, applyBindings]
        subst targetIs
        exact .inl (.restrictionNil binder)
      · exact absurd raw (by rw [exchange_raw]; decide)
      · exact absurd raw (by rw [extrusion_raw]; decide)
      · exact absurd raw (by rw [emptyUnit_raw]; decide)
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨process, rfl, rfl⟩ := unfold_forward matched applied
        exact .inr (.unfold process none)
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨rfl, rfl⟩ := nil_forward matched applied
        exact .inl .replicationNil
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨process, rfl, rfl⟩ := twice_forward matched applied
        exact .inl (.twice process)
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨first, second, rest, shape, rfl⟩ := par_forward matched applied
        rcases shape with rfl | rfl
        · exact .inl (.par first second rest false)
        · exact .inl (.par first second rest true)
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨process, rest, rfl, rfl⟩ := idempotent_forward matched applied
        exact .inl (.idempotent process rest)
  | reverse member raw matched premises applied =>
      rcases replicationLaws_cases (block := block) member with
        rfl | rfl | rfl | ⟨label, listed, rfl⟩ | rfl | rfl | rfl | rfl | rfl
      · rw [restrictionNil_raw_right matched]
        have targetIs : target = .apply block.restrict [.lambda none (.apply block.unit [])] := by
          rw [← applied]
          simp [restrictionNilOf, applyBindings]
        subst targetIs
        exact .inr (.restrictionNil none)
      · exact absurd raw (by rw [exchange_raw]; decide)
      · exact absurd raw (by rw [extrusion_raw]; decide)
      · exact absurd raw (by rw [emptyUnit_raw]; decide)
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨process, rest, shape, rfl⟩ := unfold_reverse matched applied
        rcases shape with rfl | rfl
        · exact .inl (.unfold process rest)
        · exact .inl (.unfoldSwap process rest)
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨rfl, rfl⟩ := nil_reverse matched applied
        exact .inr .replicationNil
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨process, rfl, rfl⟩ := twice_reverse matched applied
        exact .inr (.twice process)
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨first, second, rest, shape, rfl⟩ := par_reverse matched applied
        rcases shape with rfl | rfl
        · exact .inl (.parReverse first second rest false)
        · exact .inl (.parReverse first second rest true)
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨process, rfl, rfl⟩ := idempotent_reverse matched applied
        exact .inr (.idempotent process none)
  | @declared equation orientation ambient _ _ member notRaw declared =>
      obtain ⟨spec, captured, final, bound, _, sourceScoped, matched, premises, applied, _⟩ := declared
      rcases replicationLaws_cases (block := block) member with
        rfl | rfl | rfl | ⟨label, listed, rfl⟩ | rfl | rfl | rfl | rfl | rfl
      · exact absurd notRaw (by simp [nil_raw])
      · have premisesNil : (restrictionExchangeOf block.toBlock).premises = [] := rfl
        rw [premisesNil] at premises
        cases premises
        rw [extendClosed_closedRoot] at applied
        cases orientation with
        | forward =>
            obtain ⟨outerBinder, innerBinder, body, rfl, rfl⟩ := exchange_forward_shape bound sourceScoped matched applied
            exact .inl (.exchange outerBinder innerBinder body)
        | reverse =>
            obtain ⟨outerBinder, innerBinder, body, rfl, rfl⟩ := exchange_reverse_shape bound sourceScoped matched applied
            exact .inl (.exchange outerBinder innerBinder body)
      · have premisesNil : (scopeExtrusionOf block.toBlock).premises = [] := rfl
        rw [premisesNil] at premises
        cases premises
        rw [extendClosed_closedRoot] at applied
        cases orientation with
        | forward =>
            obtain ⟨members, selected, binder, body, inside, chosen, rfl, rfl⟩ :=
              extrusion_forward_shape bound sourceScoped matched applied
            exact .inl (.extrusion inside chosen)
        | reverse =>
            obtain ⟨binder, members, selected, originals, inside, erased, rfl, rfl⟩ :=
              extrusion_reverse_shape bound sourceScoped matched applied
            exact .inl (.extrusionReverse inside erased)
      · have premisesNil : (emptyUnitOf block.toBlock label).premises = [] := rfl
        rw [premisesNil] at premises
        cases premises
        rw [extendClosed_closedRoot] at applied
        cases orientation with
        | forward =>
            obtain ⟨rfl, rfl⟩ := emptyUnit_forward_shape matched applied
            exact .inl (.emptyUnit listed none)
        | reverse =>
            obtain ⟨⟨binder, rfl⟩, rfl⟩ := emptyUnit_reverse_shape matched applied
            exact .inr (.emptyUnit listed binder)
      all_goals exact absurd notRaw (by
        rw [Mettapedia.GSLT.LanguageDef.EquationSemantics.readsRaw_of_none rfl]
        decide)

include laws in
/-- **Every law of the bag has a shape.** -/
theorem derived_lawShape {source target : Pattern} (derived : DerivedInstance language source target) :
    LawShape block source target := by
  cases derived with
  | bagPerm _ _ permutation => exact .bagPerm permutation
  | setPerm member typed => exact absurd typed (laws.no_set_rule member)
  | setDedup member typed => exact absurd typed (laws.no_set_rule member)
  | @flatten rule kind algebra pre inner post algebraRule _ _ =>
      obtain ⟨rfl, _⟩ := laws.algebra_shape algebraRule
      exact .flatten pre inner post
  | @singleton rule kind algebra element algebraRule _ sorted =>
      obtain ⟨rfl, _⟩ := laws.algebra_shape algebraRule
      refine .singleton fun binder body equal => ?_
      subst equal
      obtain ⟨free, bound, typed⟩ := sorted
      rcases hasType_collection_inversion typed with ⟨_, typeIs, _⟩ |
        ⟨rule', _, _, member', shape, _, elementsTyped⟩
      · cases typeIs
      · obtain ⟨_, rfl, _⟩ := laws.bare_shape member' shape
        have lambdaTyped := elementsHaveType_iff.mp elementsTyped _ List.mem_cons_self
        cases lambdaTyped
  | @unitElim rule kind algebra unit pre post algebraRule unitIs _ =>
      obtain ⟨rfl, named⟩ := laws.algebra_shape algebraRule
      rw [unitIs, Option.some.injEq] at named
      subst named
      exact .unitElim pre post
  | @emptyUnit rule kind algebra unit algebraRule unitIs _ =>
      obtain ⟨rfl, named⟩ := laws.algebra_shape algebraRule
      rw [unitIs, Option.some.injEq] at named
      subst named
      exact .emptyBag

include laws in
/-- **Every generator of the static theory has a shape**, one way or the other. -/
theorem generator_lawShape {base : BasePremiseEvaluator} {source target : Pattern}
    (generator : EquationGenerator base language source target) :
    LawShape block source target ∨ LawShape block target source := by
  rcases generator with ⟨_, equationInstance⟩ | derived
  · exact instance_lawShape equationInstance
  · exact .inl (derived_lawShape derived)

include laws in
/-- A shape of the language keeps the object reading's canonical block. -/
theorem LawShape.keeps_of {source target : Pattern} (shape : LawShape block source target) : Keeps block source target :=
  shape.keeps (replicate_not_multiset (language := language)) (replicate_not_emptyUnit (language := language))
    (replicate_ne_restrict (language := language)) (unit_ne_restrict (language := language))
    laws.restrict_not_emptyUnit

end Language

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
