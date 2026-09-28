import Mettapedia.OSLF.Syntax.FiniteRulePremiseLists
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Conditional authored rules as ordered constructor frames

The canonical rule interpreter carries an assignment through its premises in
order. A nonrecursive premise supplies evidence and perhaps a new assignment;
a congruence premise additionally requests one recursive reduction. The frames
below separate those requests from the other evidence without discarding the
intermediate assignments, candidate reducts, or repeated requests.

The resulting rule constructor is equivalent to the existing bounded
`ContextualStep.StepAt` relation. It is the source-level shape needed to feed
the finite-premise rule polynomial. The existing `forAll` evaluator currently
returns no results; the equivalence is parameterized by a base evaluator so a
future collection interpreter can supply its evidence without changing the
rule-constructor theorem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CanonicalConditionalRuleFrames

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists

universe u v w

/-- A selected occurrence in an ordered result list. Positions distinguish
two equal values produced along different nondeterministic branches. -/
structure ListedWitness {α : Type u} (values : List α) (value : α) where
  position : Fin values.length
  represents : values.get position = value

namespace ListedWitness

/-- Apply a map to the selected value and the complete result list while
keeping the selected occurrence position unchanged. -/
def map {α : Type u} {β : Type v} {values : List α} {value : α}
    (f : α → β) (witness : ListedWitness values value) :
    ListedWitness (values.map f) (f value) where
  position := ⟨witness.position.1, by simp [witness.position.2]⟩
  represents := by
    change (values.map f)[witness.position.1] = f value
    rw [List.getElem_map]
    exact congrArg f witness.represents

theorem ext {α : Type u} {values : List α} {value : α}
    {first second : ListedWitness values value}
    (positions : first.position = second.position) : first = second := by
  cases first with
  | mk firstPosition firstRepresents =>
    cases second with
    | mk secondPosition secondRepresents =>
      cases positions
      rfl

@[simp] theorem map_position {α : Type u} {β : Type v}
    {values : List α} {value : α} (f : α → β)
    (witness : ListedWitness values value) :
    (witness.map f).position.1 = witness.position.1 := rfl

/-- The identity map leaves the physical result position unchanged. -/
theorem map_id_position {α : Type u} {values : List α} {value : α}
    (witness : ListedWitness values value) :
    (witness.map id).position.1 = witness.position.1 := rfl

/-- Successive value maps and their composite select the same original
position even when either map collapses values. -/
theorem map_comp_position {α : Type u} {β : Type v} {γ : Type w}
    {values : List α} {value : α}
    (f : α → β) (g : β → γ)
    (witness : ListedWitness values value) :
    ((witness.map f).map g).position.1 =
      (witness.map (g ∘ f)).position.1 := rfl

/-- Maps of result values never merge distinct selected occurrences, even
when the value map itself is not injective. -/
theorem map_injective {α : Type u} {β : Type v}
    {values : List α} {value : α} (f : α → β) :
    Function.Injective (map f : ListedWitness values value →
      ListedWitness (values.map f) (f value)) := by
  intro first second equal
  apply ext
  apply Fin.ext
  exact congrArg (fun witness => witness.position.1) equal

/-- Every selected occurrence of a mapped result list comes from the value
at that same position in the original list. This recovers provenance even
when the value map identifies different values. -/
theorem map_has_preimage {α : Type u} {β : Type v}
    {values : List α} {result : β} (f : α → β)
    (selected : ListedWitness (values.map f) result) :
    ∃ (value : α) (original : ListedWitness values value),
      f value = result ∧ original.position.1 = selected.position.1 := by
  let position : Fin values.length :=
    ⟨selected.position.1, by simpa using selected.position.2⟩
  refine ⟨values.get position, ⟨position, rfl⟩, ?_, rfl⟩
  simpa [position] using selected.represents

theorem mem {α : Type u} {values : List α} {value : α}
    (witness : ListedWitness values value) : value ∈ values := by
  rw [← witness.represents]
  exact List.get_mem values witness.position

/-- Forgetting the selected position gives ordinary list membership, and
every membership has at least one position. -/
theorem nonempty_iff_mem {α : Type u} {values : List α} {value : α} :
    Nonempty (ListedWitness values value) ↔ value ∈ values := by
  constructor
  · rintro ⟨witness⟩
    exact witness.mem
  · intro member
    obtain ⟨position, represents⟩ := List.get_of_mem member
    exact ⟨⟨position, represents⟩⟩

/-- Duplicate entries are distinct evidence even when they have the same
value and therefore the same endpoint relation. -/
theorem duplicate_positions_distinct {α : Type u} (value : α) :
    (⟨⟨0, by simp⟩, rfl⟩ : ListedWitness [value, value] value) ≠
      (⟨⟨1, by simp⟩, rfl⟩ : ListedWitness [value, value] value) := by
  intro equal
  have positions := congrArg ListedWitness.position equal
  have impossible := congrArg Fin.val positions
  change (0 : Nat) = 1 at impossible
  exact Nat.zero_ne_one impossible

end ListedWitness

/-- One nonrecursive outcome or one recursive reduction request, together
with the exact assignment transition produced by the authored premise. -/
inductive PremiseFrame (base : BasePremiseEvaluator) (lang : LanguageDef) :
    Bindings → Premise → Bindings → Type where
  | freshness {initial final : Bindings} {condition : FreshnessCondition}
      (valid : ListedWitness (base lang initial (.freshness condition)) final) :
      PremiseFrame base lang initial (.freshness condition) final
  | relationQuery {initial final : Bindings} {relation : String}
      {arguments : List Pattern}
      (valid : ListedWitness
        (base lang initial (.relationQuery relation arguments)) final) :
      PremiseFrame base lang initial (.relationQuery relation arguments) final
  | forAll {initial final : Bindings} {collection parameter : String}
      {body : Premise}
      (valid : ListedWitness
        (base lang initial (.forAll collection parameter body)) final) :
      PremiseFrame base lang initial (.forAll collection parameter body) final
  | congruence {initial final matched : Bindings}
      {source target candidate : Pattern}
      (matchedPattern : ListedWitness (matchPattern target candidate) matched)
      (merges : mergeBindings initial matched = some final) :
      PremiseFrame base lang initial (.congruence source target) final
  | scopedRoot {initial final matched : Bindings}
      {step : ScopedStepPremise} {candidate : Pattern}
      (empty : step.binders = [])
      (matchedPattern : ListedWitness (matchPattern step.target candidate) matched)
      (merges : mergeBindings initial matched = some final) :
      PremiseFrame base lang initial (.scopedStep step) final

namespace PremiseFrame

/-- The recursive child requested by a frame, when it has one. -/
def child? {base : BasePremiseEvaluator} {lang : LanguageDef}
    {initial final : Bindings} {premise : Premise}
    (frame : PremiseFrame base lang initial premise final) :
    Option (Pattern × Pattern) :=
  match frame with
  | .freshness _ | .relationQuery _ | .forAll _ => none
  | .congruence (source := source) (candidate := candidate) _ _ =>
      some (applyBindings initial source, candidate)
  | .scopedRoot (step := step) (candidate := candidate) _ _ _ =>
      some (applyBindings initial step.source, candidate)

/-- All recursive requirements of a frame hold at one common depth. -/
def ValidAt {base : BasePremiseEvaluator} {lang : LanguageDef}
    {initial final : Bindings} {premise : Premise}
    (fuel : Nat) (frame : PremiseFrame base lang initial premise final) : Prop :=
  match frame with
  | .freshness _ | .relationQuery _ | .forAll _ => True
  | .congruence (source := source) (candidate := candidate) _ _ =>
      StepAt base lang fuel (applyBindings initial source) candidate
  | .scopedRoot (step := step) (candidate := candidate) _ _ _ =>
      StepAt base lang fuel (applyBindings initial step.source) candidate

/-- A frame's validity is exactly the satisfaction of the recursively
addressed child, if such a child exists. -/
theorem validAt_iff_children
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    {initial final : Bindings} {premise : Premise}
    (fuel : Nat) (frame : PremiseFrame base lang initial premise final) :
    frame.ValidAt fuel ↔
      ∀ child, child ∈ frame.child?.toList →
        StepAt base lang fuel child.1 child.2 := by
  cases frame <;> simp [ValidAt, child?]

/-- Splitting a canonical premise proof records its exact static outcome and
leaves only the recursive child to discharge. -/
theorem premiseAt_iff_exists_frame
    {base : BasePremiseEvaluator} {lang : LanguageDef} {fuel : Nat}
    {initial final : Bindings} {premise : Premise} :
    PremiseAt base lang fuel initial premise final ↔
      ∃ frame : PremiseFrame base lang initial premise final,
        frame.ValidAt fuel := by
  constructor
  · intro evidence
    cases evidence with
    | freshness valid =>
        obtain ⟨witness⟩ := ListedWitness.nonempty_iff_mem.mpr valid
        exact ⟨.freshness witness, trivial⟩
    | relationQuery valid =>
        obtain ⟨witness⟩ := ListedWitness.nonempty_iff_mem.mpr valid
        exact ⟨.relationQuery witness, trivial⟩
    | forAll valid =>
        obtain ⟨witness⟩ := ListedWitness.nonempty_iff_mem.mpr valid
        exact ⟨.forAll witness, trivial⟩
    | congruence recursive matchedPattern merges =>
        obtain ⟨witness⟩ :=
          ListedWitness.nonempty_iff_mem.mpr matchedPattern
        exact ⟨.congruence witness merges, recursive⟩
    | scopedRoot empty recursive matchedPattern merges =>
        obtain ⟨witness⟩ :=
          ListedWitness.nonempty_iff_mem.mpr matchedPattern
        exact ⟨.scopedRoot empty witness merges, recursive⟩
  · rintro ⟨frame, valid⟩
    cases frame with
    | freshness evidence => exact .freshness evidence.mem
    | relationQuery evidence => exact .relationQuery evidence.mem
    | forAll evidence => exact .forAll evidence.mem
    | congruence matchedPattern merges =>
        exact .congruence valid matchedPattern.mem merges
    | scopedRoot empty matchedPattern merges =>
        exact .scopedRoot empty valid matchedPattern.mem merges

end PremiseFrame

/-- A full ordered premise run, retaining each intermediate assignment.
Recursive requests remain separate children of the rule constructor. -/
inductive PremiseFrames (base : BasePremiseEvaluator) (lang : LanguageDef) :
    Bindings → List Premise → Bindings → Type where
  | nil (bindings : Bindings) : PremiseFrames base lang bindings [] bindings
  | cons {initial middle final : Bindings} {premise : Premise}
      {premises : List Premise}
      (first : PremiseFrame base lang initial premise middle)
      (rest : PremiseFrames base lang middle premises final) :
      PremiseFrames base lang initial (premise :: premises) final

namespace PremiseFrames

/-- Recursive children occur in the same order as their authored premises.
Equal endpoint pairs remain distinct list entries. -/
def children {base : BasePremiseEvaluator} {lang : LanguageDef}
    {initial final : Bindings} {premises : List Premise} :
    PremiseFrames base lang initial premises final → List (Pattern × Pattern)
  | .nil _ => []
  | .cons first rest => first.child?.toList ++ rest.children

/-- All recursive requests in the ordered trace are discharged at one
common contextual depth. -/
def ValidAt {base : BasePremiseEvaluator} {lang : LanguageDef}
    {initial final : Bindings} {premises : List Premise}
    (fuel : Nat) : PremiseFrames base lang initial premises final → Prop
  | .nil _ => True
  | .cons first rest => first.ValidAt fuel ∧ rest.ValidAt fuel

/-- The ordered recursive-child list is complete: satisfying its entries is
equivalent to satisfying the recursive parts of the premise trace. -/
theorem validAt_iff_children
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    {initial final : Bindings} {premises : List Premise}
    (fuel : Nat) (frames : PremiseFrames base lang initial premises final) :
    frames.ValidAt fuel ↔
      ∀ child, child ∈ frames.children →
        StepAt base lang fuel child.1 child.2 := by
  induction frames with
  | nil bindings => simp [ValidAt, children]
  | cons first rest ih =>
      constructor
      · rintro ⟨firstValid, restValid⟩ child member
        rcases List.mem_append.mp member with inFirst | inRest
        · exact (PremiseFrame.validAt_iff_children fuel first).mp
            firstValid child inFirst
        · exact ih.mp restValid child inRest
      · intro allChildren
        constructor
        · apply (PremiseFrame.validAt_iff_children fuel first).mpr
          intro child member
          exact allChildren child (List.mem_append.mpr (Or.inl member))
        · apply ih.mpr
          intro child member
          exact allChildren child (List.mem_append.mpr (Or.inr member))

/-- The canonical ordered premise judgment is exactly a complete frame trace
whose recursive requests are discharged. This also covers repeated premise
occurrences and relation queries that extend the assignment. -/
theorem premisesAt_iff_exists_frames
    {base : BasePremiseEvaluator} {lang : LanguageDef} {fuel : Nat}
    {initial final : Bindings} {premises : List Premise} :
    PremisesAt base lang fuel initial premises final ↔
      ∃ frames : PremiseFrames base lang initial premises final,
        frames.ValidAt fuel := by
  constructor
  · intro evidence
    induction premises generalizing initial final with
    | nil =>
        cases evidence
        exact ⟨.nil initial, trivial⟩
    | cons premise rest ih =>
        cases evidence with
        | cons first tail =>
            obtain ⟨firstFrame, firstValid⟩ :=
              PremiseFrame.premiseAt_iff_exists_frame.mp first
            obtain ⟨restFrames, restValid⟩ := ih tail
            exact ⟨.cons firstFrame restFrames, firstValid, restValid⟩
  · rintro ⟨frames, valid⟩
    induction frames with
    | nil bindings => exact .nil bindings
    | cons first rest ih =>
        exact .cons
          (PremiseFrame.premiseAt_iff_exists_frame.mpr
            ⟨first, valid.1⟩)
          (ih valid.2)

end PremiseFrames

/-- A rule firing shape records the actual authored rule, its match, every
ordered premise outcome, and its resulting target. The only missing data are
recursive firings requested by congruence premises. -/
structure RuleFrame (base : BasePremiseEvaluator) (lang : LanguageDef)
    (source target : Pattern) where
  rule : RewriteRule
  declared : ListedWitness lang.rewrites rule
  initial : Bindings
  matched : ListedWitness (matchPatternForRule lang rule source) initial
  final : Bindings
  premises : PremiseFrames base lang initial rule.premises final
  result : applyBindingsForRule lang rule final = target

namespace RuleFrame

def children {base : BasePremiseEvaluator} {lang : LanguageDef}
    {source target : Pattern} (frame : RuleFrame base lang source target) :
    List (Pattern × Pattern) := frame.premises.children

def ValidAt {base : BasePremiseEvaluator} {lang : LanguageDef}
    {source target : Pattern} (fuel : Nat)
    (frame : RuleFrame base lang source target) : Prop :=
  frame.premises.ValidAt fuel

/-- A constructor is enabled precisely when all its listed recursive
children are valid at the previous depth. -/
theorem validAt_iff_children
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    {source target : Pattern} (fuel : Nat)
    (frame : RuleFrame base lang source target) :
    frame.ValidAt fuel ↔
      ∀ child, child ∈ frame.children →
        StepAt base lang fuel child.1 child.2 :=
  PremiseFrames.validAt_iff_children fuel frame.premises

/-- The bounded canonical rewrite judgment is generated by precisely these
authored constructor shapes and their recursively discharged premises. -/
theorem stepAt_iff_exists_frame
    {base : BasePremiseEvaluator} {lang : LanguageDef} {fuel : Nat}
    {source target : Pattern} :
    StepAt base lang (fuel + 1) source target ↔
      ∃ frame : RuleFrame base lang source target, frame.ValidAt fuel := by
  constructor
  · intro step
    cases step with
    | @rule _ _ _ rule initial final declared matched premises result =>
        obtain ⟨declaredAt⟩ := ListedWitness.nonempty_iff_mem.mpr declared
        obtain ⟨matchedAt⟩ := ListedWitness.nonempty_iff_mem.mpr matched
        obtain ⟨frames, valid⟩ :=
          PremiseFrames.premisesAt_iff_exists_frames.mp premises
        exact ⟨⟨rule, declaredAt, initial, matchedAt, final, frames, result⟩,
          valid⟩
  · rintro ⟨frame, valid⟩
    exact .rule frame.declared.mem frame.matched.mem
      (PremiseFrames.premisesAt_iff_exists_frames.mpr
        ⟨frame.premises, valid⟩) frame.result

end RuleFrame

/-- The bounded judgment index makes a congruence premise point to a strictly
smaller contextual depth. Source and target remain part of the index. -/
abbrev Judgment := Nat × Pattern × Pattern

/-- Compile the exact canonical conditional-rule frames into an ordered,
proof-relevant polynomial. Every recursive congruence occurrence receives its
own list position, while guards and produced assignments live in the shape. -/
def authoredPresentation (base : BasePremiseEvaluator)
    (lang : LanguageDef) : FinitePresentation Unit (fun _ => Judgment) where
  Shape := fun _ judgment =>
    match judgment.1 with
    | 0 => Empty
    | _ + 1 => RuleFrame base lang judgment.2.1 judgment.2.2
  premises := by
    intro _ judgment shape
    cases judgment with
    | mk fuel endpoints =>
        cases fuel with
        | zero => exact nomatch shape
        | succ previous =>
            exact shape.children.map fun endpoints =>
              (previous, endpoints.1, endpoints.2)

/-- An authored rule frame is a genuine constructor of the compiled
polynomial at the next depth, with one address per recursive premise. -/
def authoredShape (base : BasePremiseEvaluator) (lang : LanguageDef)
    (fuel : Nat) {source target : Pattern}
    (frame : RuleFrame base lang source target) :
    (authoredPresentation base lang).Shape ()
      (fuel + 1, source, target) := frame

/-- Constructor validity is exactly validity of the recursive judgments
listed by the canonical authored-premise compiler. -/
theorem authoredShape_valid_iff_children
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    (fuel : Nat) {source target : Pattern}
    (frame : RuleFrame base lang source target) :
    frame.ValidAt fuel ↔
      ∀ child,
        child ∈ (authoredPresentation base lang).premises ()
          (fuel + 1, source, target) (authoredShape base lang fuel frame) →
        StepAt base lang child.1 child.2.1 child.2.2 := by
  rw [RuleFrame.validAt_iff_children]
  simp only [authoredPresentation, authoredShape, List.mem_map]
  constructor
  · intro allChildren child member
    obtain ⟨endpoints, isChild, equal⟩ := member
    cases equal
    exact allChildren endpoints isChild
  · intro allChildren endpoints isChild
    exact allChildren (fuel, endpoints.1, endpoints.2)
      ⟨endpoints, isChild, rfl⟩

/-- The finite rule polynomial and the existing canonical bounded semantics
derive exactly the same endpoint judgments. The polynomial keeps individual
firing trees; `StepAt` is the proposition-valued image of their existence. -/
theorem derivation_nonempty_iff_stepAt
    (base : BasePremiseEvaluator) (lang : LanguageDef) :
    ∀ (fuel : Nat) (source target : Pattern),
      Nonempty ((authoredPresentation base lang).Derivation ()
        (fuel, source, target)) ↔
      StepAt base lang fuel source target := by
  intro fuel
  induction fuel with
  | zero =>
      intro source target
      constructor
      · rintro ⟨tree⟩
        exact Empty.elim
          ((Mettapedia.TypeTheory.IndexedPolynomial.Fix.out
            (authoredPresentation base lang).polynomial tree).1)
      · intro step
        cases step
  | succ previous ih =>
      intro source target
      constructor
      · rintro ⟨tree⟩
        let layer := Mettapedia.TypeTheory.IndexedPolynomial.Fix.out
          (authoredPresentation base lang).polynomial tree
        let shape : RuleFrame base lang source target := layer.1
        let children := layer.2
        apply RuleFrame.stepAt_iff_exists_frame.mpr
        refine ⟨shape, (RuleFrame.validAt_iff_children previous shape).mpr ?_⟩
        intro child member
        have indexedMember :
            (previous, child.1, child.2) ∈
              (authoredPresentation base lang).premises ()
                (previous + 1, source, target) shape := by
          change (previous, child.1, child.2) ∈
            shape.children.map (fun endpoints =>
              (previous, endpoints.1, endpoints.2))
          exact List.mem_map.mpr ⟨child, member, rfl⟩
        obtain ⟨position, positionEq⟩ := List.get_of_mem indexedMember
        have subtree := children position
        change (authoredPresentation base lang).Derivation ()
          (((authoredPresentation base lang).premises ()
            (previous + 1, source, target) shape).get position) at subtree
        rw [positionEq] at subtree
        exact (ih child.1 child.2).mp ⟨subtree⟩
      · intro step
        obtain ⟨shape, valid⟩ := RuleFrame.stepAt_iff_exists_frame.mp step
        refine ⟨.roll shape (fun position => ?_)⟩
        have member :
            ((authoredPresentation base lang).premises ()
              (previous + 1, source, target) shape).get position ∈
              (authoredPresentation base lang).premises ()
                (previous + 1, source, target) shape :=
          List.get_mem _ _
        have recursive :=
          (authoredShape_valid_iff_children previous shape).mp valid
            _ member
        let endpoints := Classical.choose (List.mem_map.mp member)
        have ⟨isChild, indexEq⟩ :=
          Classical.choose_spec (List.mem_map.mp member)
        have recursive' :
            StepAt base lang previous endpoints.1 endpoints.2 := by
          rw [← indexEq] at recursive
          exact recursive
        have subtree := Classical.choice ((ih endpoints.1 endpoints.2).mpr recursive')
        change (authoredPresentation base lang).Derivation ()
          (((authoredPresentation base lang).premises ()
            (previous + 1, source, target) shape).get position)
        rw [← indexEq]
        exact subtree

/-- Forgetting the complete firing tree gives precisely the least canonical
relation, and every least derivation has a retained finite tree witness. -/
theorem derivation_nonempty_iff_step
    (base : BasePremiseEvaluator) (lang : LanguageDef)
    (source target : Pattern) :
    (∃ fuel, Nonempty ((authoredPresentation base lang).Derivation ()
      (fuel, source, target))) ↔
      Step base lang source target := by
  unfold Step
  exact exists_congr fun fuel =>
    derivation_nonempty_iff_stepAt base lang fuel source target

/-- The existing executable bounded interpreter is complete and sound for
inhabitation of the authored constructor tree at the same contextual depth. -/
theorem mem_rewriteAt_iff_derivation
    (base : BasePremiseEvaluator) (lang : LanguageDef)
    (fuel : Nat) (source target : Pattern) :
    target ∈ rewriteAt base lang fuel source ↔
      Nonempty ((authoredPresentation base lang).Derivation ()
        (fuel, source, target)) := by
  exact mem_rewriteAt_iff_stepAt.trans
    (derivation_nonempty_iff_stepAt base lang fuel source target).symm

/-- The current default engine has no collection-quantified premise result.
The frame construction supports such evidence through an explicit base
evaluator, but the default executable profile still needs that interpreter. -/
theorem engine_forAll_has_no_frame
    (relEnv : RelationEnv) (lang : LanguageDef)
    (initial final : Bindings) (collection parameter : String)
    (body : Premise) :
    ¬ Nonempty (PremiseFrame (engineBasePremises relEnv) lang
      initial (.forAll collection parameter body) final) := by
  rintro ⟨frame⟩
  cases frame with
  | forAll valid =>
      have member := valid.mem
      simp [engineBasePremises, premiseStepWithEnv] at member

#print axioms PremiseFrame.premiseAt_iff_exists_frame
#print axioms ListedWitness.duplicate_positions_distinct
#print axioms ListedWitness.map_injective
#print axioms ListedWitness.map_has_preimage
#print axioms PremiseFrames.premisesAt_iff_exists_frames
#print axioms RuleFrame.stepAt_iff_exists_frame
#print axioms authoredShape_valid_iff_children
#print axioms derivation_nonempty_iff_stepAt
#print axioms derivation_nonempty_iff_step
#print axioms mem_rewriteAt_iff_derivation
#print axioms engine_forAll_has_no_frame

end Mettapedia.OSLF.Binding.CanonicalConditionalRuleFrames
