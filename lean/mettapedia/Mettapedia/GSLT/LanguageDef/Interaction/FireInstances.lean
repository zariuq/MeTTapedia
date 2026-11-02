import Mettapedia.GSLT.LanguageDef.Interaction.Fire
import Mettapedia.GSLT.LanguageDef.Interaction.StrengthInstances

/-!
# Available events in CCS and in the ambient calculus

CCS has two base rules, the reaction headed by parallel composition and the
silent step headed by the sum, and two rules that say where rewrites fire:
inside a parallel composition and under a restriction. Its reductions are
exactly its base rewrites beneath parallel compositions and restrictions. The
handshake has one live cut; a handshake guarded by a prefix exposes a redex
that is not an available event, because a prefix is not a context in which
rewrites fire; under a restriction the same reaction is available. A parallel
composition carried by a bag is a single cut at which several events may be
available, and with sums the events at one cut may resolve a choice in
different ways.

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
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)

/-- The rule for a component of a parallel composition. -/
theorem ccsParCong_elementCongruence : ElementCongruence ccsParCongRewrite .hashBag "S" "T" "rest" where
  premises := rfl
  left := rfl
  right := rfl
  unordered := by decide
  distinct := by decide

/-- The rule for the body of a restriction. -/
theorem ccsResCong_binderCongruence : BinderCongruence ccsResCongRewrite "CNu" "S" "T" where
  premises := rfl
  left := rfl
  right := rfl
  distinct := by decide
  aligned := by decide +kernel

/-- **Every rule of CCS is a base rewrite or says where rewrites fire**: the reaction and the silent step are base
rewrites, and reduction happens inside a parallel composition and under a restriction. -/
theorem ccs_firesInContexts : FiresInContexts ccsCalc := by
  intro rule membership
  rw [ccsCalc_rewrites] at membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl
  · exact .inl (isBaseRewrite_of_premises_eq_nil rfl)
  · exact .inl (isBaseRewrite_of_premises_eq_nil rfl)
  · exact .inr (.inr (.inl ⟨_, _, _, _, ccsParCong_elementCongruence⟩))
  · exact .inr (.inr (.inr ⟨_, _, _, ccsResCong_binderCongruence⟩))

/-- **The reductions of CCS are its reactions and silent steps beneath parallel compositions and restrictions.** -/
theorem ccs_step_iff_exists_firesTo {state next : Pattern} :
    Step base ccsCalc state next ↔
      ∃ splitting : Splitting state, splitting.FiresTo RelationEnv.empty ccsCalc next :=
  step_iff_exists_firesTo ccs_firesInContexts

/-- The base rewrites of CCS are headed by parallel composition or by the sum. -/
theorem ccs_baseRewritesHeaded :
    BaseRewritesHeadedBy ccsCalc [.collection .hashBag, .constructor "CSum"] :=
  ccs_baseRewritesHeaded_family

/-- A base contraction of CCS is a reaction or a silent step. -/
theorem ccs_base_rule {rule : RewriteRule} (listed : rule ∈ ccsCalc.rewrites) (base : IsBaseRewrite rule) :
    rule = ccsReactRewrite ∨ rule = ccsTauRewrite := by
  rw [ccsCalc_rewrites] at listed
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr rfl
  · exact absurd base (not_isBaseRewrite_of_congruence (List.Mem.head _))
  · exact absurd base (not_isBaseRewrite_of_congruence (List.Mem.head _))

/-- The handshake contracts at its root. -/
theorem handshake_baseStep : BaseStep RelationEnv.empty ccsCalc handshake handshakeDone :=
  BaseStep.of_match (rule := ccsReactRewrite) (List.Mem.head _) rfl (by decide +kernel)
    (by decide +kernel)

/-- The root cut is an available event. -/
theorem handshakeRoot_fires : (Splitting.root handshake).Fires RelationEnv.empty ccsCalc :=
  ⟨⟨.hole, .hole⟩, handshakeDone, handshake_baseStep⟩

/-- No proper subterm of the handshake is matched by a base rule. -/
theorem handshake_proper_unmatched : ∀ sub ∈ subtermsOf handshake, sub ≠ handshake →
    ∀ rule ∈ [ccsReactRewrite, ccsTauRewrite], matchPattern rule.left sub = [] := by
  decide +kernel

/-- **One live cut.** Of all the ways of cutting the handshake in two, exactly the cut at the root is an available
event. -/
theorem handshake_fires_iff (splitting : Splitting handshake) :
    splitting.Fires RelationEnv.empty ccsCalc ↔ splitting.context = .hole := by
  constructor
  · rintro ⟨-, reduct, rule, listed, base, initial, matched, -⟩
    apply splitting.context_eq_hole_of_whole
    by_contra proper
    rw [matchPatternForRule_eq_syntactic] at matched
    have unmatched := handshake_proper_unmatched splitting.subterm splitting.subterm_mem proper rule (by
      rcases ccs_base_rule listed base with rfl | rfl <;> simp)
    rw [unmatched] at matched
    cases matched
  · intro atRoot
    obtain ⟨context, subterm, plugs⟩ := splitting
    obtain rfl : context = .hole := atRoot
    obtain rfl : subterm = handshake := plugs
    exact handshakeRoot_fires

/-- `a.(a.0 | ~a.(a.0))`: the handshake guarded by a prefix. -/
def guarded : Pattern := sum [act nameA handshake]

/-- The cut of the guarded handshake beneath its prefix. -/
def guardedInner : Splitting guarded where
  context := .apply "CSum" [] (.collection .hashBag [] (.apply "CAct" [nameA] .hole []) [] none) []
  subterm := handshake
  plugs := rfl

/-- The cut beneath the prefix exposes a redex. -/
theorem guardedInner_exposesRedex : guardedInner.ExposesRedex ccsCalc :=
  Splitting.exposesRedex_of_fires (splitting := Splitting.root handshake) handshakeRoot_fires

/-- **A redex is not yet an event.** The cut beneath the prefix exposes a redex, is not an available event, and the
guarded handshake cannot move: neither a sum nor a prefix is a context in which rewrites fire. -/
theorem guarded_exposed_not_available :
    guardedInner.ExposesRedex ccsCalc ∧ ¬ guardedInner.Fires RelationEnv.empty ccsCalc ∧
      ∀ next, ¬ Step base ccsCalc guarded next := by
  refine ⟨guardedInner_exposesRedex, ?_, ?_⟩
  · rintro ⟨⟨residual, reactive⟩, -⟩
    cases reactive with
    | argument _ _ listed congruence =>
        rw [ccsCalc_rewrites] at listed
        simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
        rcases listed with rfl | rfl | rfl | rfl
        · exact absurd congruence.left (by simp [ccsReactRewrite])
        · have shape := congruence.left
          simp only [ccsTauRewrite, Pattern.apply.injEq, true_and] at shape
          have member := shape ▸
            List.mem_singleton_self (Pattern.collection .hashBag [.apply "CTau" [.fvar "p"]] (some "m"))
          simp at member
        · exact absurd congruence.left (by simp [ccsParCongRewrite])
        · exact absurd congruence.left (by simp [ccsResCongRewrite])
  · intro next
    apply not_step_of_matchPatternForRule_eq_nil
    intro rule membership
    rw [ccsCalc_rewrites] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl <;> decide +kernel

/-- The cut of the private handshake beneath its restriction. -/
def privateInner : Splitting privateHandshake where
  context := .apply "CNu" [] (.lambda none .hole) []
  subterm := par [sum [act (.bvar 0) nil], sum [coact (.bvar 0) nil]]
  plugs := rfl

/-- **Under a restriction the reaction is an available event**: the body of a restriction is a context in which
rewrites fire. -/
theorem privateInner_firesTo :
    privateInner.FiresTo RelationEnv.empty ccsCalc (nu (par [nil, nil])) :=
  ⟨.apply "CNu" [] (.lambda none .hole) [], par [nil, nil],
    .binder none (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
      ccsResCong_binderCongruence .hole,
    BaseStep.of_match (rule := ccsReactRewrite) (List.Mem.head _) rfl (by decide +kernel)
      (by decide +kernel),
    rfl⟩

/-- `(a.0 + b.0) | ~a.0 | ~b.0`: a choice, and a partner for each summand. -/
def contended : Pattern := par [sum [act nameA nil, act nameB nil], sum [coact nameA nil], sum [coact nameB nil]]

/-- The choice resolved on `a`. -/
def contendedFirst : Pattern := par [nil, nil, sum [coact nameB nil]]

/-- The choice resolved on `b`. -/
def contendedSecond : Pattern := par [nil, nil, sum [coact nameA nil]]

/-- **One cut, two events, and a choice resolved two ways.** The root cut of the contended composition has two base
contractions with different results; each discards the summand the other takes. -/
theorem contended_one_cut_two_events :
    (Splitting.root contended).FiresTo RelationEnv.empty ccsCalc contendedFirst ∧
      (Splitting.root contended).FiresTo RelationEnv.empty ccsCalc contendedSecond ∧
        contendedFirst ≠ contendedSecond := by
  refine ⟨⟨.hole, contendedFirst, .hole, ?_, rfl⟩, ⟨.hole, contendedSecond, .hole, ?_, rfl⟩,
    by decide⟩
  · exact BaseStep.of_match (rule := ccsReactRewrite) (List.Mem.head _) rfl (by decide +kernel)
      (by decide +kernel)
  · exact BaseStep.of_match (rule := ccsReactRewrite) (List.Mem.head _) rfl (by decide +kernel)
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
  · exact .inr (.inr (.inl ⟨_, _, _, _, parCongRule_elementCongruence⟩))
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
