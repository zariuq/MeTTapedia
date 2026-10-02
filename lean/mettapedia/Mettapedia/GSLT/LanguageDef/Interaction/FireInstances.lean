import Mettapedia.GSLT.LanguageDef.Interaction.Fire
import Mettapedia.GSLT.LanguageDef.Interaction.StrengthInstances

/-!
# Available events in CCS and in the ambient calculus

CCS has one rule and it is a base rule, so rewrites fire only at the root of
a parallel composition.  The handshake has one live cut; the cut at either
prefix is inert; and a handshake guarded by a prefix exposes a redex that is
not an available event, because the prefix is not a context in which
rewrites fire.  A parallel composition carried by a bag is a single cut at
which several events may be available: the bundle of events is not a
sub-bundle of the splittings.

The ambient calculus has two congruence rules, one for the content of an
ambient and one for a component of a parallel composition.  Its reductions
are exactly its base rewrites beneath boundaries and parallel compositions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-! ## CCS -/

section CCS

open Mettapedia.Languages.ProcessCalculi.CCS

/-- The one rule of CCS is a base rewrite. -/
theorem ccs_rules_base : ∀ rule ∈ ccsCalc.rewrites, IsBaseRewrite rule := by
  intro rule membership
  obtain rfl := List.mem_singleton.mp membership
  exact isBaseRewrite_of_premises_eq_nil rfl

/-- Every rule of CCS is a base rewrite or a congruence. -/
theorem ccs_firesInContexts : FiresInContexts ccsCalc :=
  fun rule membership => .inl (ccs_rules_base rule membership)

/-- The base rewrites of CCS are headed by parallel composition. -/
theorem ccs_baseRewritesHeaded :
    BaseRewritesHeadedBy ccsCalc [ccsInteractivePresentation.contactHead] :=
  ccsInteractivePresentation.baseRewritesHeadedBy_of_everyRuleIsCut ccs_everyRuleIsCut

/-- The handshake contracts at its root. -/
theorem handshake_baseStep : BaseStep RelationEnv.empty ccsCalc handshake handshakeDone :=
  BaseStep.of_match (rule := ccsSyncRewrite) (List.Mem.head _) rfl (by decide +kernel)
    (by decide +kernel)

/-- The cut of the handshake at its first prefix. -/
def handshakeFirst : Splitting handshake where
  context := .collection .hashBag [] .hole
    [.apply "CCoAct" [nameA, .apply "CAct" [nameA, nil]]] none
  subterm := .apply "CAct" [nameA, nil]
  plugs := rfl

/-- The root cut is an available event. -/
theorem handshakeRoot_fires : (Splitting.root handshake).Fires RelationEnv.empty ccsCalc :=
  ⟨⟨.hole, .hole⟩, handshakeDone, handshake_baseStep⟩

/-- The cut at the first prefix is inert: a prefix alone is not headed by
parallel composition. -/
theorem handshakeFirst_inert : ¬ handshakeFirst.Fires RelationEnv.empty ccsCalc :=
  handshakeFirst.not_fires_of_head ccs_baseRewritesHeaded (by
    intro head membership
    obtain rfl := List.mem_singleton.mp membership
    decide)

/-- **One live cut.**  Of all the ways of cutting the handshake in two,
exactly the cut at the root is an available event. -/
theorem handshake_fires_iff (splitting : Splitting handshake) :
    splitting.Fires RelationEnv.empty ccsCalc ↔ splitting.context = .hole := by
  constructor
  · rintro ⟨⟨residual, reactive⟩, -⟩
    exact (reactive.eq_hole_of_base ccs_rules_base).1
  · intro atRoot
    obtain ⟨context, subterm, plugs⟩ := splitting
    obtain rfl : context = .hole := atRoot
    obtain rfl : subterm = handshake := plugs
    exact handshakeRoot_fires

/-- `a.(a.0 | ~a.(a.0))`: the handshake guarded by a prefix. -/
def guarded : Pattern := .apply "CAct" [nameA, handshake]

/-- The cut of the guarded handshake beneath its prefix. -/
def guardedInner : Splitting guarded where
  context := .apply "CAct" [nameA] .hole []
  subterm := handshake
  plugs := rfl

/-- The cut beneath the prefix exposes a redex. -/
theorem guardedInner_exposesRedex : guardedInner.ExposesRedex ccsCalc :=
  Splitting.exposesRedex_of_fires (splitting := Splitting.root handshake) handshakeRoot_fires

/-- **A redex is not yet an event.**  The cut beneath the prefix exposes a
redex, is not an available event, and the guarded handshake cannot move. -/
theorem guarded_exposed_not_available :
    guardedInner.ExposesRedex ccsCalc ∧ ¬ guardedInner.Fires RelationEnv.empty ccsCalc ∧
      ∀ next, ¬ Step base ccsCalc guarded next := by
  refine ⟨guardedInner_exposesRedex, ?_, ?_⟩
  · rintro ⟨⟨residual, reactive⟩, -⟩
    have atRoot := (reactive.eq_hole_of_base ccs_rules_base).1
    cases atRoot
  · intro next
    apply not_step_of_matchPatternForRule_eq_nil
    intro rule membership
    obtain rfl := List.mem_singleton.mp membership
    decide +kernel

/-- `a.0 | ~a.0 | ~a.(a.0)`: one action and two complementary ones. -/
def contended : Pattern :=
  .collection .hashBag [
    .apply "CAct" [nameA, nil],
    .apply "CCoAct" [nameA, nil],
    .apply "CCoAct" [nameA, .apply "CAct" [nameA, nil]]] none

/-- The action synchronised with the first co-action. -/
def contendedFirst : Pattern :=
  .collection .hashBag [nil, nil, .apply "CCoAct" [nameA, .apply "CAct" [nameA, nil]]] none

/-- The action synchronised with the second co-action. -/
def contendedSecond : Pattern :=
  .collection .hashBag [nil, .apply "CAct" [nameA, nil], .apply "CCoAct" [nameA, nil]] none

/-- **One cut, two events.**  The root cut of the contended composition has
two base contractions with different results.  With a contact carried by a
bag, the events available at a state are not determined by its cuts. -/
theorem contended_one_cut_two_events :
    (Splitting.root contended).FiresTo RelationEnv.empty ccsCalc contendedFirst ∧
      (Splitting.root contended).FiresTo RelationEnv.empty ccsCalc contendedSecond ∧
        contendedFirst ≠ contendedSecond := by
  refine ⟨⟨.hole, contendedFirst, .hole, ?_, rfl⟩, ⟨.hole, contendedSecond, .hole, ?_, rfl⟩,
    by decide⟩
  · exact BaseStep.of_match (rule := ccsSyncRewrite) (List.Mem.head _) rfl (by decide +kernel)
      (by decide +kernel)
  · exact BaseStep.of_match (rule := ccsSyncRewrite) (List.Mem.head _) rfl (by decide +kernel)
      (by decide +kernel)

end CCS

/-! ## The ambient calculus -/

section Ambient

open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile

/-- The rule for a component of a parallel composition. -/
theorem parCongRule_elementCongruence :
    ElementCongruence parCongRule .hashBag "S" "T" "rest" where
  premises := rfl
  left := rfl
  right := rfl
  unordered := by decide
  distinct := by decide

/-- The rule for the content of an ambient. -/
theorem ambCongRule_argumentCongruence :
    ArgumentCongruence ambCongRule "AAmb" ["n"] [] "S" "T" where
  premises := rfl
  left := rfl
  right := rfl
  linear := by decide

/-- Every rule of the ambient calculus is a base rewrite or a congruence. -/
theorem ambient_firesInContexts : FiresInContexts ambientCalc := by
  intro rule membership
  have listed : rule ∈ [openRule, inRule, outRule, parCongRule, ambCongRule] := membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl
  · exact .inl (isBaseRewrite_of_premises_eq_nil rfl)
  · exact .inl (isBaseRewrite_of_premises_eq_nil rfl)
  · exact .inl (isBaseRewrite_of_premises_eq_nil rfl)
  · exact .inr (.inr ⟨_, _, _, _, parCongRule_elementCongruence⟩)
  · exact .inr (.inl ⟨_, _, _, _, _, ambCongRule_argumentCongruence⟩)

/-- The content of an ambient is running: for every name, a reduction of the
content is a reduction of the ambient.  The instance of the argument
congruence at the boundary. -/
theorem ambient_content_runs (name : Pattern) {content reduct : Pattern}
    (inner : Step base ambientCalc content reduct) :
    Step base ambientCalc (amb name content) (amb name reduct) :=
  ambCongRule_argumentCongruence.step (beforeTerms := [name]) (afterTerms := [])
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    rfl rfl inner

/-- A component of a parallel composition is running; its reduct is returned
at the front.  The instance of the element congruence at the bag. -/
theorem ambient_component_runs (before after : List Pattern) {component reduct : Pattern}
    (inner : Step base ambientCalc component reduct) :
    Step base ambientCalc (par (before ++ component :: after) none)
      (par (reduct :: (before ++ after)) none) :=
  parCongRule_elementCongruence.step
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) before after none
    inner

/-- **The reductions of the ambient calculus are its three base rewrites
beneath boundaries and parallel compositions.** -/
theorem ambient_step_iff_exists_firesTo {state next : Pattern} :
    Step base ambientCalc state next ↔
      ∃ splitting : Splitting state, splitting.FiresTo RelationEnv.empty ambientCalc next :=
  step_iff_exists_firesTo ambient_firesInContexts

/-- The dissolution contracts at its root. -/
theorem opening_baseStep :
    BaseStep RelationEnv.empty ambientCalc opening (par [nil, nil] none) :=
  BaseStep.of_match (rule := openRule) (List.Mem.head _) rfl (by decide +kernel)
    (by decide +kernel)

/-- The cut of `b[open a.0 | a[0]]` at the content of the boundary. -/
def openingInsideContent : Splitting openingInside where
  context := .apply "AAmb" [nameB] .hole []
  subterm := opening
  plugs := rfl

/-- The cut of `b[open a.0 | a[0]]` at the name of the boundary. -/
def openingInsideName : Splitting openingInside where
  context := .apply "AAmb" [] .hole [opening]
  subterm := nameB
  plugs := rfl

/-- The boundary is a context in which rewrites fire. -/
theorem boundary_reactive (name : Pattern) :
    Reactive ambientCalc (.apply "AAmb" [name] .hole []) (.apply "AAmb" [name] .hole []) :=
  .argument [name] []
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    ambCongRule_argumentCongruence rfl rfl .hole

/-- The cut at the content is an available event, and its result is the
boundary around the dissolved content. -/
theorem openingInsideContent_firesTo :
    openingInsideContent.FiresTo RelationEnv.empty ambientCalc
      (amb nameB (par [nil, nil] none)) :=
  ⟨_, _, boundary_reactive nameB, opening_baseStep, rfl⟩

/-- The cut at the name is inert: a name is headed neither by parallel
composition nor by the boundary. -/
theorem openingInsideName_inert : ¬ openingInsideName.Fires RelationEnv.empty ambientCalc :=
  openingInsideName.not_fires_of_head ambient_baseRewritesHeaded_family (by
    intro head membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl <;> decide)

end Ambient

end Mettapedia.GSLT.LanguageDef
