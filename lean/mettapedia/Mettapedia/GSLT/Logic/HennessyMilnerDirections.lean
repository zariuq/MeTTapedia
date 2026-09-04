import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy
import Mettapedia.GSLT.Logic.ContextHML

/-!
# Directions and contexts as labels

The adequacy theorem is stated for a labeled family of steps.  Two label
families arise from any GSLT with an observation set:

* the two *directions* of its step, forward (successors) and backward
  (predecessors), which is what a formula language with both a step-future
  diamond and a step-past box needs; and
* its *minimal contexts*, for the context-decorated Hennessy–Milner logic of
  reactive systems, where `⟨K⟩φ` holds when the term plugged into `K` steps
  to a term satisfying `φ`.

Both are shown to respect the equations, so the generic adequacy theorem
applies.  For contexts this yields the context-decorated adequacy statement
as a theorem: context-labeled bisimilarity coincides with context-HML
equivalence under image-finiteness modulo the equations.  A small canary
records that plain reduction bisimilarity is not the right left-hand side
for that statement: two terms with no reductions at all are reduction
bisimilar, yet one context can separate them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HennessyMilner

universe uAtom

/-! ## The two directions of a step -/

/-- Forward reads successors, backward reads predecessors. -/
inductive Direction where
  | forward
  | backward
  deriving DecidableEq, Repr

variable {S : GSLT}

/-- The step family indexed by direction. -/
def directedStep (S : GSLT) : Direction → S.Term → S.Term → Prop
  | .forward, source, target => S.Step source target
  | .backward, source, target => S.Step target source

/-- The observed GSLT with both directions of its step as labels. -/
def directional (observed : ObservedGSLT.{uAtom} S)
    (observes_resp : ∀ (atom : observed.Atom) {left right : S.Term},
      S.Equiv left right → (observed.observes atom left ↔ observed.observes atom right)) :
    System.{uAtom, 0} S where
  Atom := observed.Atom
  observes := observed.observes
  observes_resp := observes_resp
  Label := Direction
  act := directedStep S
  act_resp_left := by
    intro label left right target equivalent step
    cases label with
    | forward => exact S.rewrites_resp_left equivalent step
    | backward =>
        exact ⟨target, S.rewrites_resp_right step equivalent, S.equations.iseqv.refl target⟩
  act_resp_right := by
    intro label source target target' step equivalent
    cases label with
    | forward => exact S.rewrites_resp_right step equivalent
    | backward =>
        obtain ⟨target'', step', equivalent'⟩ := S.rewrites_resp_left equivalent step
        exact S.rewrites_resp_right step' (S.equations.iseqv.symm equivalent')

@[simp] theorem directional_act_forward (observed : ObservedGSLT.{uAtom} S) (observes_resp)
    (source target : S.Term) :
    (directional observed observes_resp).act .forward source target ↔ S.Step source target :=
  Iff.rfl

@[simp] theorem directional_act_backward (observed : ObservedGSLT.{uAtom} S) (observes_resp)
    (source target : S.Term) :
    (directional observed observes_resp).act .backward source target ↔ S.Step target source :=
  Iff.rfl

/-! ## Minimal contexts as labels -/

/-- Plugging respects the equations: the contexts are congruences for the
equation theory. -/
def PlugRespectsEquiv (S : GSLT) [HasMinimalContexts S] : Prop :=
  ∀ (K : MinimalContext S) {left right : S.Term},
    S.Equiv left right → S.Equiv (K.plug left) (K.plug right)

/-- The observed GSLT with its minimal contexts as labels: the label `K` steps
from `t` to `t'` when `K[t]` steps to `t'`. -/
def contextual [HasMinimalContexts S] (observed : ObservedGSLT.{uAtom} S)
    (observes_resp : ∀ (atom : observed.Atom) {left right : S.Term},
      S.Equiv left right → (observed.observes atom left ↔ observed.observes atom right))
    (plugResp : PlugRespectsEquiv S) :
    System.{uAtom, _} S where
  Atom := observed.Atom
  observes := observed.observes
  observes_resp := observes_resp
  Label := MinimalContext S
  act := fun K source target => S.contextStep source K target
  act_resp_left := by
    intro K left right target equivalent step
    exact S.rewrites_resp_left (plugResp K equivalent) step
  act_resp_right := by
    intro K source target target' step equivalent
    exact S.rewrites_resp_right step equivalent

/-- Context-labeled bisimilarity with no atomic observations. -/
def contextBisimilar [HasMinimalContexts S] (plugResp : PlugRespectsEquiv S)
    (left right : S.Term) : Prop :=
  (contextual (⟨PEmpty, fun atom _ => atom.elim⟩ : ObservedGSLT.{0} S)
    (fun atom => atom.elim) plugResp).Bisimilar left right

/-- Translate context-decorated HML into the labeled adequacy language. -/
def toLabeled [HasMinimalContexts S] :
    HMLFormula S → Formula PEmpty (MinimalContext S)
  | .top => .top
  | .bot => .neg .top
  | .conj left right => .conj (toLabeled left) (toLabeled right)
  | .neg inner => .neg (toLabeled inner)
  | .diamond K inner => .dia K (toLabeled inner)

/-- The translation preserves satisfaction. -/
theorem sat_toLabeled [HasMinimalContexts S] (plugResp : PlugRespectsEquiv S) :
    ∀ (formula : HMLFormula S) (term : S.Term),
      (contextual (⟨PEmpty, fun atom _ => atom.elim⟩ : ObservedGSLT.{0} S)
          (fun atom => atom.elim) plugResp).sat (toLabeled formula) term ↔
        HMLFormula.satisfies S term formula
  | .top, _ => Iff.rfl
  | .bot, _ => by
      simp [toLabeled, System.sat, HMLFormula.satisfies]
  | .conj left right, term =>
      and_congr (sat_toLabeled plugResp left term) (sat_toLabeled plugResp right term)
  | .neg inner, term => not_congr (sat_toLabeled plugResp inner term)
  | .diamond K inner, term =>
      exists_congr fun target => and_congr Iff.rfl (sat_toLabeled plugResp inner target)

/-- Every labeled formula without atoms is the translation of a context-HML
formula. -/
def ofLabeled [HasMinimalContexts S] :
    Formula PEmpty (MinimalContext S) → HMLFormula S
  | .top => .top
  | .atom atom => atom.elim
  | .conj left right => .conj (ofLabeled left) (ofLabeled right)
  | .neg inner => .neg (ofLabeled inner)
  | .dia K inner => .diamond K (ofLabeled inner)

theorem toLabeled_ofLabeled [HasMinimalContexts S] :
    ∀ formula : Formula PEmpty (MinimalContext S),
      toLabeled (ofLabeled formula) = formula
  | .top => rfl
  | .atom atom => atom.elim
  | .conj left right => by
      rw [ofLabeled, toLabeled, toLabeled_ofLabeled left, toLabeled_ofLabeled right]
  | .neg inner => by
      rw [ofLabeled, toLabeled, toLabeled_ofLabeled inner]
  | .dia K inner => by
      rw [ofLabeled, toLabeled, toLabeled_ofLabeled inner]

/-- Context-HML equivalence is logical equivalence of the contextual system. -/
theorem hmlEquiv_iff_logicallyEquivalent [HasMinimalContexts S]
    (plugResp : PlugRespectsEquiv S) (left right : S.Term) :
    HMLFormula.hmlEquiv S left right ↔
      (contextual (⟨PEmpty, fun atom _ => atom.elim⟩ : ObservedGSLT.{0} S)
        (fun atom => atom.elim) plugResp).LogicallyEquivalent left right := by
  constructor
  · intro equivalent formula
    rw [← toLabeled_ofLabeled formula, sat_toLabeled plugResp, sat_toLabeled plugResp]
    exact equivalent _
  · intro equivalent formula
    rw [← sat_toLabeled plugResp, ← sat_toLabeled plugResp]
    exact equivalent _

/-- Context-decorated adequacy, soundness: context-bisimilar terms satisfy the
same context-HML formulas. -/
theorem hmlEquiv_of_contextBisimilar [HasMinimalContexts S] (plugResp : PlugRespectsEquiv S)
    {left right : S.Term} (bisimilar : contextBisimilar plugResp left right) :
    HMLFormula.hmlEquiv S left right :=
  (hmlEquiv_iff_logicallyEquivalent plugResp left right).mpr
    (System.logicallyEquivalent_of_bisimilar _ bisimilar)

/-- Context-decorated adequacy, completeness: under image-finiteness modulo
the equations for every context, context-HML equivalent terms are
context-bisimilar. -/
theorem contextBisimilar_of_hmlEquiv [HasMinimalContexts S] (plugResp : PlugRespectsEquiv S)
    (finite : (contextual (⟨PEmpty, fun atom _ => atom.elim⟩ : ObservedGSLT.{0} S)
      (fun atom => atom.elim) plugResp).ImageFiniteModulo)
    {left right : S.Term} (equivalent : HMLFormula.hmlEquiv S left right) :
    contextBisimilar plugResp left right :=
  System.bisimilar_of_logicallyEquivalent _ finite
    ((hmlEquiv_iff_logicallyEquivalent plugResp left right).mp equivalent)

/-- Context-decorated Hennessy–Milner adequacy. -/
theorem contextBisimilar_iff_hmlEquiv [HasMinimalContexts S] (plugResp : PlugRespectsEquiv S)
    (finite : (contextual (⟨PEmpty, fun atom _ => atom.elim⟩ : ObservedGSLT.{0} S)
      (fun atom => atom.elim) plugResp).ImageFiniteModulo)
    (left right : S.Term) :
    contextBisimilar plugResp left right ↔ HMLFormula.hmlEquiv S left right :=
  ⟨hmlEquiv_of_contextBisimilar plugResp, contextBisimilar_of_hmlEquiv plugResp finite⟩

/-! ## Reduction bisimilarity is not the left-hand side of context adequacy -/

namespace ReductionBisimilarityCanary

/-- Four states: two inert sources, a target reachable only by plugging the
first source into a context, and the sink the target reduces to. -/
inductive State where
  | first
  | second
  | target
  | sink
  deriving DecidableEq, Repr

/-- The only reduction is from the target to the sink. -/
def inertGSLT : GSLT where
  Term := State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source next => source = .target ∧ next = .sink
  rewrites_resp_left := by
    intro _ _ next equal step
    subst equal
    exact ⟨next, step, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ step equal
    subst equal
    exact step

/-- The one nontrivial context sends the first source to the target and fixes
everything else; every context shape is admitted as minimal. -/
def activate : GSLTContext inertGSLT where
  plug := fun state => match state with
    | .first => .target
    | other => other

instance : HasMinimalContexts inertGSLT where
  IsOneHole := fun _ => True
  IsReactive := fun _ => True
  IsMinimal := fun _ => True
  id_oneHole := trivial
  id_reactive := trivial
  id_minimal := trivial
  minimal_reactive := fun _ => trivial
  minimal_oneHole := fun _ => trivial

theorem plugResp : PlugRespectsEquiv inertGSLT := by
  intro K left right equal
  cases equal
  exact rfl

/-- Neither source reduces, so they are reduction bisimilar. -/
theorem first_second_bisimilar : inertGSLT.Bisimilar .first .second := by
  refine ⟨fun left right => (left = .first ∧ right = .second) ∨ (left = .second ∧ right = .first),
    ⟨?_, ?_⟩, Or.inl ⟨rfl, rfl⟩⟩
  · rintro left right (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) _ step
    · exact State.noConfusion step.1
    · exact State.noConfusion step.1
  · rintro left right (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) _ step
    · exact State.noConfusion step.1
    · exact State.noConfusion step.1

/-- Yet the activating context separates them: `⟨activate⟩⊤` holds of the
first source and fails on the second. -/
theorem not_hmlEquiv : ¬ HMLFormula.hmlEquiv inertGSLT .first .second := by
  intro equivalent
  have holds : HMLFormula.satisfies inertGSLT .first
      (.diamond ⟨activate, trivial⟩ .top) :=
    ⟨.sink, ⟨rfl, rfl⟩, trivial⟩
  have fails : ¬ HMLFormula.satisfies inertGSLT .second
      (.diamond ⟨activate, trivial⟩ .top) := by
    rintro ⟨_, step, _⟩
    exact State.noConfusion step.1
  exact fails ((equivalent _).mp holds)

/-- So reduction bisimilarity does not imply context-HML equivalence; the
adequacy statement must use context-labeled bisimilarity. -/
theorem reduction_bisimilarity_insufficient :
    inertGSLT.Bisimilar .first .second ∧ ¬ HMLFormula.hmlEquiv inertGSLT .first .second :=
  ⟨first_second_bisimilar, not_hmlEquiv⟩

/-- The transcription of the paper's adequacy statement with reduction
bisimilarity is refuted. -/
theorem not_adequacy_sound : ¬ GSLT.adequacy_sound inertGSLT :=
  fun sound => not_hmlEquiv (sound first_second_bisimilar)

#print axioms not_adequacy_sound

end ReductionBisimilarityCanary

end Mettapedia.GSLT.HennessyMilner
