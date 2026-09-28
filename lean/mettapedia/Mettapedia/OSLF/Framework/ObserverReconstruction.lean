import Mettapedia.OSLF.Framework.ObserverExtension
import Mettapedia.OSLF.MeTTaIL.ContextualStepClosedSubsystem
import Mettapedia.OSLF.MeTTaIL.OccurringLabels

/-!
# From reading to stepping: the observer's instruments as transitions

`ObserverExtension` proves two facts about the observer's kit at the level of
*matching*: the opening request fires on a term exactly when that term is an
application of the constructor at the declared arity (`openingRule_match_iff`),
and the projection request delivers the argument at its position
(`projectionRule_exposes`).

A bisimulation argument cannot use either of those directly.  Bisimilarity is a
statement about the *step* relation, and a match is not yet a step: between them
stand the rule's premises, the rule's presence in the presentation, and the
substitution that builds the target.  This module crosses that distance, and
crosses it as a law rather than at the two rules of interest.

**What is proved.**  A rule with no premises steps exactly when its left-hand
side matches, in both directions, for any presentation.  The generated
administrative rules have no premises, so the observer's instruments step
precisely when they read.  Applied to the kit, the opening request beside a
term headed by its constructor steps to that constructor's argument bundle, and
the projection request on a bundle steps to the argument at its position.

**And what the converse turns out to be.**  The natural converse — that a step
from `⟨ask c, t⟩` can only be the opening rule, so that *observing a transition*
determines the head — is **false**, and freshness does not repair it.  An
authored rule whose left-hand side is a bag with a tail variable fires on any bag
containing its redex and carries the request along; that is the shape rho's join
rule has.  `Interference.transition_does_not_determine_head` exhibits it on the
smallest presentation with that shape, whose administrative vocabulary is fresh.

What the failure points at is the repair: the observable is the transition's
*target*, not its existence.  Only the opening rule builds a term headed by the
constructor's argument former, and both signs are checked — the absorbing step
reaches no bundle, the opening step reaches exactly the one `opening_step` names.

**How far the general half gets.**  Among the rules the extension *adjoins*, the
request's own opening rule is the only one that can fire beside an authored term,
and when it fires it reads the head: `adjoined_match_forces_head`, for any
presentation.  Lifted to steps, `step_dichotomy` says a transition out of the
instrumented cut either used an authored rule or read the head.  So the
interference is confined to the authored half, exactly.

**The authored half, reduced.**  `OccurringLabels` now supplies the missing law:
substitution introduces no label that occurred neither in the pattern nor in the
values substituted, through the binder elimination of the `subst` case and the
rest-splice of the `collection` case alike.  `argsHeaded_target_source` applies it
here: a target headed by `Args⟨c⟩` forces that label into the rule's right-hand
side or into the bindings the match and the premises produced.

**And the premise-free authored case is closed.**  `OccurringLabels` supplies the
other half too -- matching binds only labels of the term it matched -- so
`authored_premiseFree_target_not_argsHeaded` shows no premise-free authored rule
can build the bundle: its target's labels come from its right-hand side and from
what it matched, and freshness separates both from `Args⟨c⟩`.  The two
well-formedness hypotheses it takes are stated as conditions on the presentation,
which is what they are.

**And the premise-bearing case with it.**  A `relationQuery` premise is the one
place a rule acquires material from outside the term it matched, and what it
acquires is bounded by the row it matched against.  `evaluatorAvoids_of_env`
reduces the whole condition to the relation environment's own rows -- the
built-in relations echo the query's own arguments, so they introduce nothing --
and `PlatformLabels.guard_evaluatorAvoids` discharges that for rho's guard rather
than leaving it standing.

**Congruence premises too, where the question is well posed.**  `stepAt_avoids`
and its two companions are a mutual induction over the step relation and the two
premise relations, so a presentation whose rules cannot write a label never
produces it -- congruence premises included.

**And the boundary is settled, negatively.**  That law does not transfer to the
extension, because the opening rule writes the bundle former -- its whole purpose
-- so `RulesAvoid` is false of the extension by construction.  A congruence
premise of an authored rule can therefore reach an opening rule and carry a
bundle out, and `Smuggling` does exactly that in one step, from a cut whose term
is authored and is not an application of the constructor named.  So the `noSteps`
hypothesis of `authored_target_not_argsHeaded` is **necessary**: dropped, the
conclusion is false.  Rho's join rule satisfies it, its only premise being a
relation query, which is why the argument reaches that presentation.

**The observable, as one statement.**  `reads_head_iff` combines all of it: on a
presentation whose authored rules are tame, an opening request beside a term
reaches that constructor's bundle exactly when the term is an application of the
constructor at the declared arity.  That is `openingRule_match_iff` lifted from
one rule and one match to a whole presentation and its step relation, which is
the level a bisimulation argument works at.

**The bisimulation, and its first step.**  `IsInstrumentBisimulation` is the
notion reconstruction is about: related terms tested by the *same instrument*,
with the bundle former as a barb.  It is deliberately not a reduction
bisimilarity -- every clause names the instrument, and the barbs name what the
instruments are for.  `head_agreement` is its first consequence: related terms are
applications of the same constructor.

**The authored half of the descent's inversion.**  A projection request's response
must be *determined*, not merely matched, and two canaries showed what stands in
the way: a left-hand side that matches everything (`Determinacy`) and one that is
rigid but names an undeclared constructor (`Citation`).  `RigidHeads` and
`LeftHeadsDeclared` exclude exactly those, and with them
`authored_no_match_adjoined_head` proves no authored rule matches a term headed by
an adjoined label at all -- so `instrument_step_is_adjoined` says whatever answers
a request, it is the kit answering, not the presentation.

**And the inversion is whole.**  `adjoined_projection_match_forces` settles which
member of the kit answers -- the opening rule matches on a collection while a
request is an application, the build rule carries a different bracketed prefix,
and the projection rule's own inner bundle former pins the constructor before its
index is consulted, so no condition about colliding labels is needed.
`projection_step_forces` puts the two halves together.

**And what it returned.**  The gap between a lemma that exhibits a binding list
with the delivery property and an inversion that supplies one which merely
matches is closed by `LinearMatch.matchArgsRel_fvars_inversion`: *every* match of
a list of distinct metavariables binds each to the term at its position, binds
nothing else, and binds no name twice.  So
`ObserverExtension.projectionRule_delivers_of_match` applies to the bindings the
inversion actually hands back, and `projection_response` reads: the projection
instrument returns the argument at its position.

Both instruments now deliver from *any* match, not merely from one exhibited
alongside: `ObserverExtension.openingRule_delivers_of_match` is the bag-side
companion, where the pairing of the request against the request is forced because
the alternative would need the term to be the request itself.

**The descent.**  `argument_agreement` assembles them: related terms are
applications of the same constructor and their arguments are related, position by
projectable position.

**Reconstruction.**  `reconstruction` closes it: terms related by an instrument
bisimulation, both readable all the way down, are equal.  `ReadableByKit` names
the fragment the observer can read -- every head an opened constructor of matching
arity, every position of it projectable, hereditarily -- and the limit it encodes
is the kit's, not the argument's: a binder position has no projection rule because
projecting one would hand back an open body whose sort the presentation does not
declare.

What this module still does not do is relate that equality to a larger `=E`; the
fragment's terms are equal on the nose, and an equational theory over them is a
further step.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.ObserverReconstruction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.OccurringLabels
  (labels labelsList bindingLabels premiseLabels labels_applyBindings
    bindingLabels_matchPattern bindingLabels_relationQueryStep
    labelsList_builtinRelationTuples labelsList_applyBindings
    labels_applyRuleBindings bindingLabels_mergeBindings)
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.ObserverExtension

/-! ## A premise-free rule steps exactly when it matches -/

/-- **Matching is stepping, for a rule with no premises.**  Nothing stands
between the two: the premise list is discharged by the empty derivation, and the
target is the substitution the match already produced. -/
theorem step_of_premiseFree_match
    {base : BasePremiseEvaluator} {lang : LanguageDef} {rule : RewriteRule}
    (member : rule ∈ lang.rewrites) (noPremises : rule.premises = [])
    {source : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPatternForRule lang rule source) :
    Step base lang source (applyBindingsForRule lang rule bindings) := by
  refine ⟨1, StepAt.rule member matched ?_ rfl⟩
  rw [noPremises]
  exact PremisesAt.nil bindings

/-- **And stepping is matching**, in the shape inversion gives: a step names the
rule it used, a binding list that matched, and the substitution that built the
target. -/
theorem match_of_step
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    {source target : Pattern} (step : Step base lang source target) :
    ∃ rule ∈ lang.rewrites, ∃ initial ∈ matchPatternForRule lang rule source,
      ∃ fuel final, PremisesAt base lang fuel initial rule.premises final ∧
        applyBindingsForRule lang rule final = target := by
  obtain ⟨fuel, stepAt⟩ := step
  cases stepAt with
  | @rule fuel source target rule initial final member matched premises built =>
      exact ⟨rule, member, initial, matched, fuel, final, premises, built⟩

/-! ## The generated rules are rules of the extension -/

theorem openingRule_mem (lang : LanguageDef) (cut : CollType) (opened : List String)
    {declaration : GrammarRule} (member : declaration ∈ openedRules lang opened) :
    openingRule cut declaration.label declaration.params.length
      ∈ (observerExtension lang cut opened).rewrites := by
  simp only [observerExtension, List.mem_append]
  exact Or.inr (List.mem_flatMap.mpr ⟨declaration, member, by simp [instrumentRules]⟩)

theorem projectionRule_mem (lang : LanguageDef) (cut : CollType) (opened : List String)
    {declaration : GrammarRule} (member : declaration ∈ openedRules lang opened)
    {position : Nat × String} (projectable : position ∈ projectablePositions declaration) :
    projectionRule declaration.label declaration.params.length position.1
      ∈ (observerExtension lang cut opened).rewrites := by
  simp only [observerExtension, List.mem_append]
  refine Or.inr (List.mem_flatMap.mpr ⟨declaration, member, ?_⟩)
  simp only [instrumentRules, List.mem_cons, List.mem_map]
  exact Or.inr (Or.inr ⟨position, projectable, rfl⟩)

/-! ## The instruments as transitions

The two match-level laws become step-level laws by the bridge above.  Nothing is
assumed about the presentation beyond the declaration being opened: the rules are
premise-free by construction, so reading and stepping coincide. -/

/-- **The opening request steps.**  Beside a term headed by its constructor at
the declared arity, the request is a redex of the extension and the transition
delivers that constructor's argument bundle. -/
theorem opening_step (base : BasePremiseEvaluator) (lang : LanguageDef)
    (cut : CollType) (opened : List String)
    {declaration : GrammarRule} (member : declaration ∈ openedRules lang opened)
    {arguments : List Pattern} (length : arguments.length = declaration.params.length) :
    Step base (observerExtension lang cut opened)
      (.collection cut
        [.apply (askLabel declaration.label) [],
          .apply declaration.label arguments] none)
      (.apply (argsLabel declaration.label) arguments) := by
  obtain ⟨bindings, matched, delivered⟩ :=
    openingRule_match_of_headed cut declaration.label declaration.params.length length
  have stepped := step_of_premiseFree_match (base := base)
    (openingRule_mem lang cut opened member) rfl
    (source := .collection cut
      [.apply (askLabel declaration.label) [], .apply declaration.label arguments] none)
    (bindings := bindings)
    (by rw [matchPatternForRule_eq_syntactic]; exact matched)
  rwa [applyBindingsForRule, applyBindingsForRuleUsing_empty,
    applyRuleBindings_openingRule, delivered] at stepped

/-- **And the projection request steps**, to the argument at its position: the
observer learns what the constructor was applied to. -/
theorem projection_step (base : BasePremiseEvaluator) (lang : LanguageDef)
    (cut : CollType) (opened : List String)
    {declaration : GrammarRule} (member : declaration ∈ openedRules lang opened)
    {position : Nat × String} (projectable : position ∈ projectablePositions declaration)
    (bounded : position.1 < declaration.params.length)
    {arguments : List Pattern} (length : arguments.length = declaration.params.length) :
    Step base (observerExtension lang cut opened)
      (.apply (getLabel declaration.label position.1)
        [.apply (argsLabel declaration.label) arguments])
      (arguments[position.1]'(by rw [length]; exact bounded)) := by
  obtain ⟨bindings, matched, delivered⟩ :=
    projectionRule_exposes declaration.label bounded length
  have stepped := step_of_premiseFree_match (base := base)
    (projectionRule_mem lang cut opened member projectable) rfl
    (source := .apply (getLabel declaration.label position.1)
      [.apply (argsLabel declaration.label) arguments])
    (bindings := bindings)
    (by rw [matchPatternForRule_eq_syntactic]; exact matched)
  rwa [applyBindingsForRule, applyBindingsForRuleUsing_empty,
    applyRuleBindings_projectionRule, delivered] at stepped

/-! ## Among the observer's own rules, only one can fire

The interference the canary below exhibits comes entirely from *authored* rules.
Among the rules the extension adjoins, the request's own opening rule is the only
one that can fire beside an authored term — and when it fires it reads the head.
That is proved here at the generality of any presentation, so what the refined
observable still needs is confined to the authored half. -/

/-- **Only the request's own opening rule fires, among the adjoined rules.**  The
build and projection rules ask for an application while the cut is a collection,
so neither matches.  An opening rule for a *different* constructor would have to
read its own request out of the term standing beside the cut, and that term is
headed by an authored operation while the request is not.  What is left is the
opening rule for the constructor the request names, which reads the head. -/
theorem adjoined_match_forces_head
    (lang : LanguageDef) (cut : CollType) (opened : List String)
    (fresh : AdministrativeFresh lang opened)
    {constructor : String} {term : Pattern}
    (authored : HasOperationHead (lang.terms.map GrammarRule.label) term)
    {declaration : GrammarRule} (declMember : declaration ∈ openedRules lang opened)
    {rule : RewriteRule} (ruleMember : rule ∈ instrumentRules cut declaration)
    {bindings : Bindings}
    (matched : bindings ∈ matchPattern rule.left
      (.collection cut [.apply (askLabel constructor) [], term] none)) :
    declaration.label = constructor ∧
      rule = openingRule cut constructor declaration.params.length ∧
      ∃ arguments : List Pattern, term = .apply constructor arguments ∧
        arguments.length = declaration.params.length := by
  have adjoinedAsk : askLabel declaration.label ∈ adjoinedLabels lang opened :=
    List.mem_flatMap.mpr ⟨declaration, declMember, by simp [instrumentLabels]⟩
  rcases instrumentRules_cases cut ruleMember with rfl | rfl | ⟨position, _, rfl⟩
  · have relational := matchPattern_iff_matchRel.mp matched
    have bagMatch := matchRel_collection_noRest_to_bag relational
    cases bagMatch with
    | cons index bounded askMatch restMatch _ =>
        match index, bounded with
        | 0, _ =>
            simp only [List.eraseIdx_zero, List.tail_cons] at restMatch
            have sameAsk : askLabel declaration.label = askLabel constructor :=
              matchRel_apply_head askMatch
            have sameLabel : declaration.label = constructor :=
              askLabel_injective sameAsk
            cases restMatch with
            | cons innerIndex innerBounded constructorMatch tailMatch _ =>
                match innerIndex, innerBounded with
                | 0, _ =>
                    simp only [List.getElem_cons_zero] at constructorMatch
                    cases constructorMatch with
                    | apply argumentsMatch lengths =>
                        refine ⟨sameLabel, by rw [sameLabel], _, by rw [sameLabel], ?_⟩
                        rw [← lengths, argPatterns_length]
        | 1, _ =>
            simp only [List.getElem_cons_succ, List.getElem_cons_zero] at askMatch
            cases askMatch with
            | apply argumentsMatch lengths =>
                exact absurd
                  (show askLabel declaration.label
                      ∈ lang.terms.map GrammarRule.label from authored)
                  (fresh.1 _ adjoinedAsk)
  · have relational := matchPattern_iff_matchRel.mp matched
    cases relational
  · have relational := matchPattern_iff_matchRel.mp matched
    cases relational

/-- **The dichotomy, at the level of steps.**  A transition out of the
instrumented cut either used an authored rule -- the interference the canary
below exhibits -- or used one of the observer's own, and then it read the head.
So the refined observable needs only the authored half, and that is exactly what
remains open. -/
theorem step_dichotomy
    (base : BasePremiseEvaluator) (lang : LanguageDef) (cut : CollType)
    (opened : List String) (fresh : AdministrativeFresh lang opened)
    {constructor : String} {term target : Pattern}
    (authored : HasOperationHead (lang.terms.map GrammarRule.label) term)
    (step : Step base (observerExtension lang cut opened)
      (.collection cut [.apply (askLabel constructor) [], term] none) target) :
    (∃ rule ∈ lang.rewrites, ∃ bindings,
        bindings ∈ matchPatternForRule (observerExtension lang cut opened) rule
          (.collection cut [.apply (askLabel constructor) [], term] none)) ∨
      (∃ declaration ∈ openedRules lang opened, declaration.label = constructor ∧
        ∃ arguments : List Pattern, term = .apply constructor arguments ∧
          arguments.length = declaration.params.length) := by
  obtain ⟨rule, member, bindings, matched, -⟩ := match_of_step step
  simp only [observerExtension, List.mem_append] at member
  rcases member with authoredRule | adjoinedRule
  · exact Or.inl ⟨rule, authoredRule, bindings, matched⟩
  · obtain ⟨declaration, declMember, ruleMember⟩ := List.mem_flatMap.mp adjoinedRule
    rw [matchPatternForRule_eq_syntactic] at matched
    obtain ⟨sameLabel, -, arguments, shape, lengths⟩ :=
      adjoined_match_forces_head lang cut opened fresh authored declMember ruleMember matched
    exact Or.inr ⟨declaration, declMember, sameLabel, arguments, shape, lengths⟩

/-! ## Where an `Args⟨c⟩` target could come from

The authored half of the refined observable asks whether an authored rule can
build a target headed by a constructor's argument former.  A step's target is the
final bindings substituted into the rule's right-hand side, and substitution
introduces no label that was not already in one of those two
(`labels_applyBindings`).  That reduces the question to two facts
about the presentation, and the reduction is proved here. -/

/-- **A target headed by the argument former forces that label into the rule or
into the bindings.**  Nowhere else: substitution invents no labels, through the
binder elimination of the `subst` case and the rest-splice of the `collection`
case alike. -/
theorem argsHeaded_target_source
    {lang : LanguageDef} {rule : RewriteRule} {bindings : Bindings}
    {constructor : String} {arguments : List Pattern}
    (built : applyBindingsForRule lang rule bindings
      = .apply (argsLabel constructor) arguments) :
    argsLabel constructor ∈ labels rule.right ∨
      argsLabel constructor ∈ bindingLabels bindings := by
  have occurs : argsLabel constructor ∈ labels
      (applyBindingsForRule lang rule bindings) := by
    rw [built]; simp
  rw [applyBindingsForRule, applyBindingsForRuleUsing_empty] at occurs
  exact List.mem_append.mp
    (labels_applyRuleBindings rule bindings occurs)

/-- The two administrative labels of one constructor are different, so a request
is never mistaken for the bundle it produces. -/
theorem askLabel_ne_argsLabel (constructor : String) :
    askLabel constructor ≠ argsLabel constructor := by
  simp [askLabel, argsLabel]

/-- A premise-free rule's final bindings are the ones its match produced. -/
theorem premisesAt_nil_eq {base : BasePremiseEvaluator} {lang : LanguageDef}
    {fuel : Nat} {bindings final : Bindings}
    (premises : PremisesAt base lang fuel bindings [] final) : final = bindings := by
  cases premises
  rfl

/-- **No premise-free authored rule builds an argument bundle.**  Its target's
labels come from its right-hand side and from what it matched; the right-hand
side carries only authored labels, what it matched is the request beside an
authored term, and freshness separates all of those from the bundle's former.

The hypotheses are conditions on the presentation, stated for what they are.
Membership in the authored rules is not among them and is not needed: what the
argument uses is that the right-hand side carries only authored labels, so the
statement holds of any rule of that shape.  The
premise-bearing case is deliberately not covered: a `relationQuery` premise draws
on ambient relation data, so for those the corresponding statement is a condition
on that data rather than a theorem about the rule. -/
theorem authored_premiseFree_target_not_argsHeaded
    (base : BasePremiseEvaluator) (lang : LanguageDef) (cut : CollType)
    (opened : List String) (fresh : AdministrativeFresh lang opened)
    {declaration : GrammarRule} (declMember : declaration ∈ openedRules lang opened)
    {constructor : String} (named : declaration.label = constructor)
    {term : Pattern} (termAuthored : labels term ⊆ lang.terms.map GrammarRule.label)
    {rule : RewriteRule} (noPremises : rule.premises = [])
    (rightAuthored : labels rule.right ⊆ lang.terms.map GrammarRule.label)
    {bindings final : Bindings}
    (matched : bindings ∈ matchPatternForRule (observerExtension lang cut opened) rule
      (.collection cut [.apply (askLabel constructor) [], term] none))
    (premises : PremisesAt base (observerExtension lang cut opened) 0 bindings
      rule.premises final)
    {arguments : List Pattern} :
    applyBindingsForRule (observerExtension lang cut opened) rule final
      ≠ .apply (argsLabel constructor) arguments := by
  intro built
  have adjoinedArgs : argsLabel constructor ∈ adjoinedLabels lang opened :=
    List.mem_flatMap.mpr ⟨declaration, declMember, by simp [instrumentLabels, named]⟩
  have notAuthored := fresh.1 _ adjoinedArgs
  have sameBindings : final = bindings := by
    rw [noPremises] at premises
    exact premisesAt_nil_eq premises
  subst sameBindings
  rcases argsHeaded_target_source built with inRight | inBindings
  · exact absurd (rightAuthored inRight) notAuthored
  · rw [matchPatternForRule_eq_syntactic] at matched
    have inSource := bindingLabels_matchPattern matched inBindings
    simp only [Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_collection,
      Mettapedia.OSLF.MeTTaIL.OccurringLabels.labelsList_cons,
      Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_apply] at inSource
    rcases List.mem_append.mp inSource with inRequest | inRest
    · rcases List.mem_cons.mp inRequest with sameLabel | impossible
      · exact absurd sameLabel.symm (askLabel_ne_argsLabel constructor)
      · simp at impossible
    · rcases List.mem_append.mp inRest with inTerm | impossible
      · exact absurd (termAuthored inTerm) notAuthored
      · simp at impossible

/-! ## The premise-bearing case, and the condition it rests on

A premise can introduce bindings the match never produced.  A `congruence`
premise does it by taking a step, a `freshness`, `relationQuery` or `forAll`
premise by consulting the base evaluator -- and a relation environment is ambient
data, so what it may hand back is a condition on the presentation's surroundings
rather than a theorem about its rules.

The condition is stated for what it is, and it forbids **one** label: the bundle
former of the constructor in question.  Forbidding the whole administrative
vocabulary would be wrong, not merely strong -- a rule may perfectly well bind a
metavariable to the opening request standing beside the term, so `Ask⟨c⟩` does
reach the bindings in ordinary use.  What must not reach them is `Args⟨c⟩`. -/

/-- A premise is a congruence premise. -/
def IsCongruence : Premise → Prop
  | .congruence _ _ => True
  | .scopedStep _ => True
  | _ => False

/-- A binding list does not mention a label. -/
def Avoids (forbidden : String) (bindings : Bindings) : Prop :=
  forbidden ∉ bindingLabels bindings

/-- A premise's own patterns do not mention a label. -/
def PremiseAvoids (forbidden : String) (premise : Premise) : Prop :=
  forbidden ∉ premiseLabels premise

/-- **The condition on the surroundings.**  The base evaluator hands back no
occurrence of the forbidden label unless the bindings or the premise already
carried one.  The premise is in the hypothesis because a built-in relation echoes
the query's own arguments back as a tuple, so a query that mentions the label can
recover it without the environment supplying anything. -/
def EvaluatorAvoids (base : BasePremiseEvaluator) (forbidden : String) : Prop :=
  ∀ lang bindings premise result, result ∈ base lang bindings premise →
    Avoids forbidden bindings → PremiseAvoids forbidden premise →
    Avoids forbidden result

/-- **Premises that take no steps introduce no forbidden label.**  Each goes
through the base evaluator, so the condition carries along the list.  Congruence
premises are excluded because they recurse into the step relation, which is a
different induction. -/
theorem premisesAt_avoids {base : BasePremiseEvaluator} {lang : LanguageDef}
    {forbidden : String} (confined : EvaluatorAvoids base forbidden) :
    ∀ {fuel : Nat} {initial : Bindings} {premises : List Premise} {final : Bindings},
      PremisesAt base lang fuel initial premises final →
      (∀ premise ∈ premises, ¬ IsCongruence premise) →
      (∀ premise ∈ premises, PremiseAvoids forbidden premise) →
      Avoids forbidden initial → Avoids forbidden final
  | _, _, _, _, .nil _, _, _, initialAvoids => initialAvoids
  | _, _, _, _, .cons headEvidence restEvidence, noCongruence, clean, initialAvoids => by
      refine premisesAt_avoids confined restEvidence
        (fun p member => noCongruence p (List.mem_cons_of_mem _ member))
        (fun p member => clean p (List.mem_cons_of_mem _ member)) ?_
      have headClean := clean _ (List.mem_cons_self ..)
      cases headEvidence with
      | freshness member => exact confined _ _ _ _ member initialAvoids headClean
      | relationQuery member => exact confined _ _ _ _ member initialAvoids headClean
      | forAll member => exact confined _ _ _ _ member initialAvoids headClean
      | congruence _ _ _ =>
          exact absurd trivial (noCongruence _ (List.mem_cons_self ..))
      | scopedRoot _ _ _ _ =>
          exact absurd trivial (noCongruence _ (List.mem_cons_self ..))

/-- **So an authored rule builds no argument bundle**, premises and all, so long
as its premises take no steps and the surroundings meet the condition.  This
covers rho's join rule, whose only premise is a relation query. -/
theorem authored_target_not_argsHeaded
    (base : BasePremiseEvaluator) (lang : LanguageDef) (cut : CollType)
    (opened : List String) (fresh : AdministrativeFresh lang opened)
    {declaration : GrammarRule} (declMember : declaration ∈ openedRules lang opened)
    {constructor : String} (named : declaration.label = constructor)
    (confined : EvaluatorAvoids base (argsLabel constructor))
    {term : Pattern} (termAuthored : labels term ⊆ lang.terms.map GrammarRule.label)
    {rule : RewriteRule}
    (noSteps : ∀ premise ∈ rule.premises, ¬ IsCongruence premise)
    (cleanPremises : ∀ premise ∈ rule.premises,
      PremiseAvoids (argsLabel constructor) premise)
    (rightAuthored : labels rule.right ⊆ lang.terms.map GrammarRule.label)
    {bindings final : Bindings} {fuel : Nat}
    (matched : bindings ∈ matchPatternForRule (observerExtension lang cut opened) rule
      (.collection cut [.apply (askLabel constructor) [], term] none))
    (premises : PremisesAt base (observerExtension lang cut opened) fuel bindings
      rule.premises final)
    {arguments : List Pattern} :
    applyBindingsForRule (observerExtension lang cut opened) rule final
      ≠ .apply (argsLabel constructor) arguments := by
  intro built
  have adjoinedArgs : argsLabel constructor ∈ adjoinedLabels lang opened :=
    List.mem_flatMap.mpr ⟨declaration, declMember, by simp [instrumentLabels, named]⟩
  have notAuthored := fresh.1 _ adjoinedArgs
  have initialAvoids : Avoids (argsLabel constructor) bindings := by
    intro member
    rw [matchPatternForRule_eq_syntactic] at matched
    have inSource := bindingLabels_matchPattern matched member
    simp only [Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_collection,
      Mettapedia.OSLF.MeTTaIL.OccurringLabels.labelsList_cons,
      Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_apply] at inSource
    rcases List.mem_append.mp inSource with inRequest | inRest
    · rcases List.mem_cons.mp inRequest with sameLabel | impossible
      · exact absurd sameLabel.symm (askLabel_ne_argsLabel constructor)
      · simp at impossible
    · rcases List.mem_append.mp inRest with inTerm | impossible
      · exact absurd (termAuthored inTerm) notAuthored
      · simp at impossible
  have finalAvoids := premisesAt_avoids confined premises noSteps cleanPremises initialAvoids
  rcases argsHeaded_target_source built with inRight | inBindings
  · exact absurd (rightAuthored inRight) notAuthored
  · exact finalAvoids inBindings

/-- **The condition reduces to the relation environment's own rows.**  Freshness
returns the bindings it was given or nothing; congruence and `forAll` return
nothing; and a relation query introduces only what its tuple carried, where the
built-in rows echo the query's own arguments and so introduce nothing the premise
and the bindings did not already have.  What is left to check of a presentation
is therefore its relations, and only its relations. -/
theorem evaluatorAvoids_of_env {env : RelationEnv} {forbidden : String}
    (envRows : ∀ relation arguments tuple,
      tuple ∈ env.tuples relation arguments → forbidden ∉ labelsList tuple) :
    EvaluatorAvoids (engineBasePremises env) forbidden := by
  intro lang bindings premise result member bindingsAvoid premiseAvoid
  cases premise with
  | congruence _ _ => simp [engineBasePremises] at member
  | scopedStep _ => simp [engineBasePremises, premiseStepWithEnv] at member
  | forAll _ _ _ => simp [engineBasePremises, premiseStepWithEnv] at member
  | freshness condition =>
      simp only [engineBasePremises, premiseStepWithEnv] at member
      split at member
      · split at member
        · simp only [List.mem_singleton] at member
          exact member ▸ bindingsAvoid
        · simp at member
      · simp at member
  | relationQuery relation arguments =>
      simp only [engineBasePremises, premiseStepWithEnv] at member
      obtain ⟨tuple, tupleMember, bound⟩ :=
        bindingLabels_relationQueryStep env lang bindings relation arguments member
      intro occurs
      rcases List.mem_append.mp (bound occurs) with inBindings | inTuple
      · exact bindingsAvoid inBindings
      · rcases List.mem_append.mp tupleMember with builtin | fromEnv
        · have echoed := labelsList_builtinRelationTuples lang relation _ builtin inTuple
          rcases List.mem_append.mp
            (labelsList_applyBindings bindings arguments echoed) with inArgs | inBindings
          · exact premiseAvoid inArgs
          · exact bindingsAvoid inBindings
        · exact envRows relation _ tuple fromEnv inTuple

/-! ### Congruence premises, and the step relation with them

A congruence premise takes a step, so closing it means proving the step relation
itself introduces no forbidden label -- which is the general form of everything
above.  The three relations are mutually inductive and the proof is too. -/

/-- A presentation whose rules cannot write the forbidden label: neither in a
right-hand side nor in a premise's own patterns.  For the observer's question
this is freshness, since the label is one the extension adjoined. -/
structure RulesAvoid (lang : LanguageDef) (forbidden : String) : Prop where
  /-- No right-hand side mentions it. -/
  rights : ∀ rule ∈ lang.rewrites, forbidden ∉ labels rule.right
  /-- No premise mentions it. -/
  premises : ∀ rule ∈ lang.rewrites, ∀ premise ∈ rule.premises,
    PremiseAvoids forbidden premise

mutual

/-- **A step introduces no forbidden label.**  Its target is the rule's
right-hand side under the final bindings; the right-hand side does not mention
the label, the match binds only labels of the source, and the premises are
handled by the two statements below. -/
theorem stepAt_avoids {base : BasePremiseEvaluator} {lang : LanguageDef}
    {forbidden : String} (confined : EvaluatorAvoids base forbidden)
    (rules : RulesAvoid lang forbidden) :
    ∀ {fuel : Nat} {source target : Pattern},
      StepAt base lang fuel source target →
      forbidden ∉ labels source → forbidden ∉ labels target
  | _, _, _, .rule ruleMember matched premiseEvidence built, sourceAvoids => by
      subst built
      rw [matchPatternForRule_eq_syntactic] at matched
      have finalAvoids :=
        premisesAt_avoids_full confined rules premiseEvidence
          (rules.premises _ ruleMember)
          (fun occurs => sourceAvoids (bindingLabels_matchPattern matched occurs))
      intro occurs
      rw [applyBindingsForRule, applyBindingsForRuleUsing_empty] at occurs
      rcases List.mem_append.mp (labels_applyRuleBindings _ _ occurs) with inRight | inBindings
      · exact rules.rights _ ruleMember inRight
      · exact finalAvoids inBindings

/-- The premise-list form, congruence premises included. -/
theorem premisesAt_avoids_full {base : BasePremiseEvaluator} {lang : LanguageDef}
    {forbidden : String} (confined : EvaluatorAvoids base forbidden)
    (rules : RulesAvoid lang forbidden) :
    ∀ {fuel : Nat} {initial : Bindings} {premises : List Premise} {final : Bindings},
      PremisesAt base lang fuel initial premises final →
      (∀ premise ∈ premises, PremiseAvoids forbidden premise) →
      Avoids forbidden initial → Avoids forbidden final
  | _, _, _, _, .nil _, _, initialAvoids => initialAvoids
  | _, _, _, _, .cons headEvidence restEvidence, clean, initialAvoids =>
      premisesAt_avoids_full confined rules restEvidence
        (fun p member => clean p (List.mem_cons_of_mem _ member))
        (premiseAt_avoids confined rules headEvidence
          (clean _ (List.mem_cons_self ..)) initialAvoids)

/-- The single-premise form.  Congruence is the case with content: it steps, and
the step is handled by the statement above. -/
theorem premiseAt_avoids {base : BasePremiseEvaluator} {lang : LanguageDef}
    {forbidden : String} (confined : EvaluatorAvoids base forbidden)
    (rules : RulesAvoid lang forbidden) :
    ∀ {fuel : Nat} {initial : Bindings} {premise : Premise} {final : Bindings},
      PremiseAt base lang fuel initial premise final →
      PremiseAvoids forbidden premise →
      Avoids forbidden initial → Avoids forbidden final
  | _, _, _, _, .freshness member, clean, initialAvoids =>
      confined _ _ _ _ member initialAvoids clean
  | _, _, _, _, .relationQuery member, clean, initialAvoids =>
      confined _ _ _ _ member initialAvoids clean
  | _, _, _, _, .forAll member, clean, initialAvoids =>
      confined _ _ _ _ member initialAvoids clean
  | _, _, _, _, .congruence stepEvidence matchEvidence merged, clean, initialAvoids => by
      have candidateAvoids := stepAt_avoids confined rules stepEvidence
        (fun occurs => by
          rcases List.mem_append.mp (labels_applyBindings _ _ occurs) with inSource | inBindings
          · exact clean (List.mem_append_left _ inSource)
          · exact initialAvoids inBindings)
      intro occurs
      rcases List.mem_append.mp
        (bindingLabels_mergeBindings _ _ merged occurs) with inInitial | inPremise
      · exact initialAvoids inInitial
      · exact candidateAvoids (bindingLabels_matchPattern matchEvidence inPremise)
  | _, _, _, _, .scopedRoot _ stepEvidence matchEvidence merged, clean, initialAvoids => by
      have candidateAvoids := stepAt_avoids confined rules stepEvidence
        (fun occurs => by
          rcases List.mem_append.mp (labels_applyBindings _ _ occurs) with inSource | inBindings
          · exact clean (List.mem_append_left _ inSource)
          · exact initialAvoids inBindings)
      intro occurs
      rcases List.mem_append.mp
        (bindingLabels_mergeBindings _ _ merged occurs) with inInitial | inPremise
      · exact initialAvoids inInitial
      · exact candidateAvoids (bindingLabels_matchPattern matchEvidence inPremise)

end

/-- **The authored presentation never builds an argument bundle**, congruence
premises included.  Its rules cannot write the bundle former, so by the law above
no step of the authored theory produces one from a source that has none.

Note what this is *not*.  It is about steps of `lang`, not of
`observerExtension lang cut opened`, and the difference is not an oversight: the
extension's opening rule writes the bundle former -- that is its whole purpose --
so `RulesAvoid` is false of the extension by construction.  A congruence premise
of an authored rule, stepping inside the extension, could therefore reach an
opening rule and carry a bundle back out.  Whether that can actually happen is
open; it is not assumed away here. -/
theorem authored_step_not_argsHeaded
    {base : BasePremiseEvaluator} {lang : LanguageDef} {constructor : String}
    (confined : EvaluatorAvoids base (argsLabel constructor))
    (cited : RulesAvoid lang (argsLabel constructor))
    {fuel : Nat} {source target : Pattern}
    (step : StepAt base lang fuel source target)
    (sourceClean : argsLabel constructor ∉ labels source)
    {arguments : List Pattern} :
    target ≠ .apply (argsLabel constructor) arguments := by
  intro built
  refine stepAt_avoids confined cited step sourceClean ?_
  rw [built]
  simp

/-! ### The condition has content, and is satisfiable

Both signs, so the hypothesis above is neither vacuous nor free. -/

/-- **Positive.**  An evaluator that produces nothing meets the condition, so the
hypothesis is satisfiable.  The worked presentations in this file and in
`ObserverExtension.Gap` use evaluators of that shape. -/
theorem evaluatorAvoids_of_barren {base : BasePremiseEvaluator}
    (barren : ∀ lang bindings premise, base lang bindings premise = [])
    (forbidden : String) : EvaluatorAvoids base forbidden := by
  intro lang bindings premise result member _ _
  rw [barren] at member
  exact absurd member List.not_mem_nil

/-- **Negative.**  An evaluator that hands back a bundle violates it, so the
condition is a real restriction rather than a formality. -/
theorem evaluatorAvoids_fails (constructor : String) :
    ¬ EvaluatorAvoids
      (fun _ _ _ => [[("leaked", .apply (argsLabel constructor) [])]])
      (argsLabel constructor) := by
  intro confined
  have avoided := confined
    { name := "", types := [], terms := [], equations := [], rewrites := [] }
    [] (.relationQuery "r" []) _ (List.mem_cons_self ..)
    (by simp [Avoids, Mettapedia.OSLF.MeTTaIL.OccurringLabels.bindingLabels])
    (by simp [PremiseAvoids, Mettapedia.OSLF.MeTTaIL.OccurringLabels.premiseLabels])
  exact avoided (by
    simp [Mettapedia.OSLF.MeTTaIL.OccurringLabels.bindingLabels,
      Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_apply,
      Mettapedia.OSLF.MeTTaIL.OccurringLabels.labelsList_nil])

/-! ## Observing a transition does not determine the head

The natural converse of `openingRule_match_iff` at the level of steps would be:
a transition out of a request placed beside a term shows the term is headed by
that constructor.  It is false, and not by a technicality that a stronger
freshness condition would remove.

An authored rule whose left-hand side is a bag with a tail variable fires on any
bag containing its redex, carrying everything else along — and an opening request
placed beside such a bag is simply carried.  That is exactly the shape rho's join
rule has (`PlatformPresentation.joinRule`, whose left-hand side is
`.collection .hashBag (receiver :: outputs) (some restVar)`), so this is the case
of interest rather than a pathology.

The canary below is the smallest presentation with that shape, and it settles the
design question the failure raises: the observable must be the transition's
*target*, not its existence.  Only the opening rule builds a term headed by the
constructor's argument former, and both signs of that are checked here. -/

namespace Interference

/-- The one sort. -/
def sortT : String := "T"

def declA : GrammarRule where
  label := "A"
  category := sortT
  params := []
  syntaxPattern := [.terminal "A"]

def declB : GrammarRule where
  label := "B"
  category := sortT
  params := []
  syntaxPattern := [.terminal "B"]

/-- The constructor the observer is given an instrument for. -/
def declC : GrammarRule where
  label := "C"
  category := sortT
  params := []
  syntaxPattern := [.terminal "C"]

/-- **A bag rule with a tail variable**, the shape rho's join rule has: it fires
on any bag containing an `A`, and carries everything else along. -/
def absorbRule : RewriteRule where
  name := "absorb"
  typeContext := [("rest", .collection .hashBag (.base sortT))]
  premises := []
  left := .collection .hashBag [.apply "A" []] (some "rest")
  right := .collection .hashBag [.apply "B" []] (some "rest")

def absorbing : LanguageDef where
  name := "Absorbing"
  types := [TypeDecl.plain sortT]
  terms := [declA, declB, declC]
  equations := []
  rewrites := [absorbRule]

/-- The administrative vocabulary is fresh here, so the failure below is not a
failure of freshness. -/
theorem absorbing_fresh : AdministrativeFresh absorbing ["C"] := by
  decide +kernel

def extended : LanguageDef := observerExtension absorbing .hashBag ["C"]

def askC : Pattern := .apply (askLabel "C") []
def termA : Pattern := .apply "A" []
def termC : Pattern := .apply "C" []

def evaluator : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

/-- **The request beside the wrong term steps anyway.**  The authored rule
absorbs the request into its tail variable. -/
theorem askC_beside_termA_steps :
    rewriteAt evaluator extended 3 (.collection .hashBag [askC, termA] none)
      = [.collection .hashBag [.apply "B" [], askC] none] := by
  decide +kernel

/-- And the term it stepped beside is not an application of the constructor the
request names. -/
theorem termA_not_headed : ¬ ∃ arguments : List Pattern, termA = .apply "C" arguments := by
  rintro ⟨arguments, shape⟩
  simp [termA] at shape

/-- **So a transition does not determine the head.**  Both halves are witnessed:
the instrumented configuration steps, and the term beside the request is headed
by something else. -/
theorem transition_does_not_determine_head :
    (∃ target, target ∈ rewriteAt evaluator extended 3
        (.collection .hashBag [askC, termA] none)) ∧
      ¬ ∃ arguments : List Pattern, termA = .apply "C" arguments := by
  refine ⟨⟨.collection .hashBag [.apply "B" [], askC] none, ?_⟩, termA_not_headed⟩
  rw [askC_beside_termA_steps]
  exact List.Mem.head _

/-! ### The observable the failure points at

What survives is the transition's target.  Only the opening rule builds a term
headed by the constructor's argument former, so *reaching* one is the
observation that reads the head. -/

/-- Is this the bundle the opening rule builds? -/
def isArgsHeaded (constructor : String) : Pattern → Bool
  | .apply label _ => label == argsLabel constructor
  | _ => false

/-- **Negative instance.**  The absorbing step reaches no argument bundle, so the
refined observable is not fooled by the interference above. -/
theorem absorbing_step_reaches_no_bundle :
    (rewriteAt evaluator extended 3
      (.collection .hashBag [askC, termA] none)).any (isArgsHeaded "C") = false := by
  decide +kernel

/-- **Positive instance.**  Beside the term the request names, the step reaches
the bundle. -/
theorem opening_step_reaches_bundle :
    (rewriteAt evaluator extended 3
      (.collection .hashBag [askC, termC] none)).any (isArgsHeaded "C") = true := by
  decide +kernel

/-- And the bundle it reaches is the one `opening_step` names. -/
theorem opening_step_target :
    rewriteAt evaluator extended 3 (.collection .hashBag [askC, termC] none)
      = [.apply (argsLabel "C") []] := by
  decide +kernel

end Interference

/-! ## The observable, as one statement

Everything above combines into the fact a bisimulation argument descends on: on a
presentation whose authored rules are tame, an opening request beside a term
reaches that constructor's bundle exactly when the term is an application of the
constructor at the declared arity.

The tameness conditions are the ones the canaries showed necessary -- no stepping
premises, nothing mentioning the bundle former, right-hand sides citing only
authored constructors -- and rho's join rule meets all three. -/

/-- The conditions on an authored presentation that the two canaries showed are
each needed.  Stated as a structure so an instance is checked once and carried. -/
structure AuthoredRulesTame (lang : LanguageDef) (forbidden : String) : Prop where
  /-- No premise takes a step.  `Smuggling` shows this cannot be dropped. -/
  noSteps : ∀ rule ∈ lang.rewrites, ∀ premise ∈ rule.premises, ¬ IsCongruence premise
  /-- No premise mentions the forbidden label. -/
  clean : ∀ rule ∈ lang.rewrites, ∀ premise ∈ rule.premises,
    PremiseAvoids forbidden premise
  /-- Every right-hand side cites only declared constructors. -/
  rights : ∀ rule ∈ lang.rewrites, labels rule.right ⊆ lang.terms.map GrammarRule.label

/-- **The condition the canary below identifies.**  No authored left-hand side is
a bare metavariable.  Every other shape is already excluded: an `apply` left-hand
side cannot match an adjoined head because freshness separates the labels, and a
`collection`, `lambda`, `multiLambda` or `subst` left-hand side cannot match an
application at all.  Only a variable matches everything. -/
def IsVariable : Pattern → Bool
  | .fvar _ => true
  | _ => false

def RigidHeads (lang : LanguageDef) : Prop :=
  ∀ rule ∈ lang.rewrites, IsVariable rule.left = false

instance (lang : LanguageDef) : Decidable (RigidHeads lang) := by
  unfold RigidHeads; infer_instance

theorem not_fvar_of_rigid {lang : LanguageDef} (rigid : RigidHeads lang)
    {rule : RewriteRule} (member : rule ∈ lang.rewrites) (name : String) :
    rule.left ≠ .fvar name := by
  intro shape
  have := rigid rule member
  rw [shape] at this
  simp [IsVariable] at this

/-- Whether a rule's left-hand side, if it is an application, names a declared
constructor. -/
def LeftHeadDeclared (lang : LanguageDef) (rule : RewriteRule) : Bool :=
  match rule.left with
  | .apply label _ => (lang.terms.map GrammarRule.label).contains label
  | _ => true

/-- **The sixth condition.**  Authored left-hand sides cite only declared
constructors.  `RigidHeads` does not imply it and is not implied by it: a rule
may match on an *application* -- so rigid -- whose head is a label the
presentation never declared, and if that label happens to be one the observer
adjoined, the rule answers the observer's own request.  `Citation` below exhibits
exactly that, with freshness and rigidity both holding. -/
def LeftHeadsDeclared (lang : LanguageDef) : Prop :=
  ∀ rule ∈ lang.rewrites, LeftHeadDeclared lang rule = true

instance (lang : LanguageDef) : Decidable (LeftHeadsDeclared lang) := by
  unfold LeftHeadsDeclared; infer_instance

/-- **Everything a presentation must satisfy for the observer's argument to run on
it.**  Bundled rather than loose: the list reached five, every entry was found by
a canary rather than chosen, and a theorem with five separate preconditions is
easy to misapply by dropping one. -/
structure ObserverSetting (base : BasePremiseEvaluator) (lang : LanguageDef)
    (cut : CollType) (opened : List String) (constructor : String) : Prop where
  /-- The adjoined vocabulary is not already declared. -/
  fresh : AdministrativeFresh lang opened
  /-- The surroundings cannot hand back the bundle former. -/
  confined : EvaluatorAvoids base (argsLabel constructor)
  /-- The authored rules cannot build it either. -/
  tame : AuthoredRulesTame lang (argsLabel constructor)
  /-- No authored left-hand side matches everything. -/
  rigid : RigidHeads lang
  /-- No authored left-hand side names an undeclared constructor. -/
  cited : LeftHeadsDeclared lang
  /-- Declarations sharing a label share an arity. -/
  arities : ∀ first ∈ openedRules lang opened, ∀ second ∈ openedRules lang opened,
    first.label = second.label → first.params.length = second.params.length

/-- **The instrument reads the head, as a transition.**  A request beside a term
reaches the bundle exactly when the term is an application of the constructor at
the declared arity -- the match-level `openingRule_match_iff`, now at the level
the step relation works at, and on a whole presentation rather than one rule. -/
theorem reads_head_iff
    (base : BasePremiseEvaluator) (lang : LanguageDef) (cut : CollType)
    (opened : List String) {constructor : String}
    (setting : ObserverSetting base lang cut opened constructor)
    {declaration : GrammarRule} (declMember : declaration ∈ openedRules lang opened)
    (named : declaration.label = constructor)
    {term : Pattern} (termAuthored : labels term ⊆ lang.terms.map GrammarRule.label)
    (termHeaded : HasOperationHead (lang.terms.map GrammarRule.label) term) :
    (∃ arguments : List Pattern, Step base (observerExtension lang cut opened)
        (.collection cut [.apply (askLabel constructor) [], term] none)
        (.apply (argsLabel constructor) arguments))
      ↔ ∃ arguments : List Pattern, term = .apply constructor arguments ∧
          arguments.length = declaration.params.length := by
  constructor
  · rintro ⟨arguments, step⟩
    obtain ⟨rule, member, bindings, matched, fuel, final, premiseEvidence, built⟩ :=
      match_of_step step
    simp only [observerExtension, List.mem_append] at member
    rcases member with authoredRule | adjoinedRule
    · exact absurd built
        (authored_target_not_argsHeaded base lang cut opened setting.fresh declMember
          named setting.confined termAuthored
          (setting.tame.noSteps rule authoredRule)
          (setting.tame.clean rule authoredRule)
          (setting.tame.rights rule authoredRule) matched premiseEvidence)
    · obtain ⟨innerDeclaration, innerMember, ruleMember⟩ := List.mem_flatMap.mp adjoinedRule
      rw [matchPatternForRule_eq_syntactic] at matched
      obtain ⟨sameLabel, -, witnesses, shape, lengths⟩ :=
        adjoined_match_forces_head lang cut opened setting.fresh termHeaded
          innerMember ruleMember matched
      refine ⟨witnesses, shape, ?_⟩
      rw [lengths]
      exact setting.arities innerDeclaration innerMember declaration declMember
        (by rw [sameLabel, named])
  · rintro ⟨arguments, rfl, lengths⟩
    refine ⟨arguments, ?_⟩
    have stepped := opening_step base lang cut opened declMember (arguments := arguments)
      lengths
    rw [named] at stepped
    exact stepped

/-! ## No authored rule answers an instrument's request

The two conditions the canaries produced buy exactly this, and it is the authored
half of the inversion the descent needs. -/

/-- **An authored rule cannot match a term headed by an adjoined label.**  Its
left-hand side is not a variable, so it does not match everything; if it is an
application then its head is declared, while the request's head is adjoined, and
freshness separates the two; and every other left-hand side shape cannot match an
application at all. -/
theorem authored_no_match_adjoined_head
    (lang : LanguageDef) (opened : List String)
    (fresh : AdministrativeFresh lang opened)
    (rigid : RigidHeads lang) (cited : LeftHeadsDeclared lang)
    {label : String} (adjoined : label ∈ adjoinedLabels lang opened)
    {rule : RewriteRule} (member : rule ∈ lang.rewrites)
    {arguments : List Pattern} {bindings : Bindings} :
    bindings ∉ matchPattern rule.left (.apply label arguments) := by
  intro matched
  have relational := matchPattern_iff_matchRel.mp matched
  have notDeclared := fresh.1 label adjoined
  rcases leftShape : rule.left with _ | name | ⟨head, patternArguments⟩ | _ | _ | _ | _
  · rw [leftShape] at relational; cases relational
  · exact not_fvar_of_rigid rigid member name leftShape
  · have sameHead : head = label := by
      rw [leftShape] at relational
      exact matchRel_apply_head relational
    have declared := cited rule member
    rw [LeftHeadDeclared, leftShape] at declared
    simp only [sameHead, List.contains_iff_mem] at declared
    exact notDeclared declared
  · rw [leftShape] at relational; cases relational
  · rw [leftShape] at relational; cases relational
  · rw [leftShape] at relational; cases relational
  · rw [leftShape] at relational; cases relational

/-- **So a transition out of an instrument's request used one of the observer's
own rules.**  This is the inversion the descent needs on its side: whatever
answers a request, it is the kit answering, not the presentation. -/
theorem instrument_step_is_adjoined
    (base : BasePremiseEvaluator) (lang : LanguageDef) (cut : CollType)
    (opened : List String) (fresh : AdministrativeFresh lang opened)
    (rigid : RigidHeads lang) (cited : LeftHeadsDeclared lang)
    {label : String} (adjoined : label ∈ adjoinedLabels lang opened)
    {arguments : List Pattern} {target : Pattern}
    (step : Step base (observerExtension lang cut opened)
      (.apply label arguments) target) :
    ∃ rule ∈ (openedRules lang opened).flatMap (instrumentRules cut),
      ∃ bindings, bindings ∈ matchPattern rule.left (.apply label arguments) := by
  obtain ⟨rule, member, bindings, matched, -⟩ := match_of_step step
  rw [matchPatternForRule_eq_syntactic] at matched
  simp only [observerExtension, List.mem_append] at member
  rcases member with authoredRule | adjoinedRule
  · exact absurd matched
      (authored_no_match_adjoined_head lang opened fresh rigid cited adjoined authoredRule)
  · exact ⟨rule, adjoinedRule, bindings, matched⟩

/-- **And which member of the kit answers: the projection rule, for that
constructor at that index.**  The opening rule matches on a collection while a
request is an application; the build rule carries a different bracketed prefix;
and the projection rule's own inner bundle former pins the constructor, after
which the index follows.  No condition about colliding labels is needed -- the
inner former settles the constructor before the outer one is consulted. -/
theorem adjoined_projection_match_forces (cut : CollType)
    {constructor : String} {index : Nat} {arguments : List Pattern}
    {declaration : GrammarRule}
    {rule : RewriteRule} (ruleMember : rule ∈ instrumentRules cut declaration)
    {bindings : Bindings}
    (matched : bindings ∈ matchPattern rule.left
      (.apply (getLabel constructor index)
        [.apply (argsLabel constructor) arguments])) :
    declaration.label = constructor ∧
      rule = projectionRule constructor declaration.params.length index := by
  have relational := matchPattern_iff_matchRel.mp matched
  rcases instrumentRules_cases cut ruleMember with rfl | rfl | ⟨position, -, rfl⟩
  · cases relational
  · exact absurd (matchRel_apply_head relational)
      (buildLabel_ne_getLabel declaration.label constructor index)
  · simp only [projectionRule] at relational
    have outerHead : getLabel declaration.label position.1
        = getLabel constructor index := matchRel_apply_head relational
    have argumentsMatch := matchRel_apply_args relational
    cases argumentsMatch with
    | cons innerMatch tailMatch merged =>
        have sameConstructor : declaration.label = constructor :=
          argsLabel_injective (matchRel_apply_head innerMatch)
        subst sameConstructor
        refine ⟨rfl, ?_⟩
        rw [getLabel_index_injective declaration.label outerHead]

/-- **The inversion, whole.**  A transition out of a projection request used the
projection rule for that constructor at that index, and nothing else: not an
authored rule, and not another member of the kit. -/
theorem projection_step_forces
    (base : BasePremiseEvaluator) (lang : LanguageDef) (cut : CollType)
    (opened : List String) (fresh : AdministrativeFresh lang opened)
    (rigid : RigidHeads lang) (cited : LeftHeadsDeclared lang)
    {constructor : String} {index : Nat} {arguments : List Pattern} {target : Pattern}
    (adjoinedGet : getLabel constructor index ∈ adjoinedLabels lang opened)
    (step : Step base (observerExtension lang cut opened)
      (.apply (getLabel constructor index)
        [.apply (argsLabel constructor) arguments]) target) :
    ∃ declaration ∈ openedRules lang opened, declaration.label = constructor ∧
      ∃ bindings, bindings ∈ matchPattern
        (projectionRule constructor declaration.params.length index).left
        (.apply (getLabel constructor index)
          [.apply (argsLabel constructor) arguments]) := by
  obtain ⟨rule, adjoinedRule, bindings, matched⟩ :=
    instrument_step_is_adjoined base lang cut opened fresh rigid cited adjoinedGet step
  obtain ⟨declaration, declMember, ruleMember⟩ := List.mem_flatMap.mp adjoinedRule
  obtain ⟨sameLabel, ruleShape⟩ :=
    adjoined_projection_match_forces cut ruleMember matched
  exact ⟨declaration, declMember, sameLabel, bindings, ruleShape ▸ matched⟩

/-- **The projection instrument returns the argument at its position.**  The
inversion says which rule answered; `projectionRule_delivers_of_match` says what
it handed back, for the bindings the inversion actually supplies rather than for
a binding list exhibited separately.  Together they are the descent step. -/
theorem projection_response
    (base : BasePremiseEvaluator) (lang : LanguageDef) (cut : CollType)
    (opened : List String) {constructor : String}
    (setting : ObserverSetting base lang cut opened constructor)
    {index : Nat} {arguments : List Pattern} {target : Pattern}
    {declaration : GrammarRule} (declMember : declaration ∈ openedRules lang opened)
    (named : declaration.label = constructor)
    (bounded : index < declaration.params.length)
    (length : arguments.length = declaration.params.length)
    (adjoinedGet : getLabel constructor index ∈ adjoinedLabels lang opened)
    (step : Step base (observerExtension lang cut opened)
      (.apply (getLabel constructor index)
        [.apply (argsLabel constructor) arguments]) target) :
    target = arguments[index]'(by rw [length]; exact bounded) := by
  have onlyDeclaration : ∀ other ∈ openedRules lang opened,
      other.label = constructor → other.params.length = declaration.params.length := by
    intro other otherMember otherNamed
    exact setting.arities other otherMember declaration declMember (by rw [otherNamed, named])
  have fresh := setting.fresh
  have rigid := setting.rigid
  have cited := setting.cited
  obtain ⟨rule, member, bindings, matched, fuel, final, premiseEvidence, built⟩ :=
    match_of_step step
  rw [matchPatternForRule_eq_syntactic] at matched
  simp only [observerExtension, List.mem_append] at member
  rcases member with authoredRule | adjoinedRule
  · exact absurd matched
      (authored_no_match_adjoined_head lang opened fresh rigid cited adjoinedGet authoredRule)
  · obtain ⟨inner, innerMember, ruleMember⟩ := List.mem_flatMap.mp adjoinedRule
    obtain ⟨sameLabel, ruleShape⟩ :=
      adjoined_projection_match_forces cut ruleMember matched
    have sameArity : inner.params.length = declaration.params.length :=
      onlyDeclaration inner innerMember sameLabel
    rw [ruleShape] at matched premiseEvidence built
    rw [sameArity] at matched premiseEvidence built
    have sameBindings : final = bindings :=
      premisesAt_nil_eq (by simpa [projectionRule] using premiseEvidence)
    subst sameBindings
    rw [applyBindingsForRule, applyBindingsForRuleUsing_empty] at built
    rw [← built, applyRuleBindings_projectionRule]
    exact projectionRule_delivers_of_match constructor bounded length matched

/-! ## The bisimulation the observer's instruments induce

Reconstruction is a statement about *bisimilarity in the extension*, and the
notion has to be the right one.  Raw reduction bisimilarity will not do: it
matches steps without regard to which instrument produced them, and the whole
content here is that a particular instrument's response reads a particular thing.

So the relation below is tested *by instrument*: related terms, handed the same
instrument, must step together and hand back related results.  That is a
context-labelled notion, with the instruments as the contexts, and it carries its
`Ob` index in the `opened` parameter of every clause.

It also carries barbs.  Without them the matching step could be any step at all,
and the fact that one side reached a bundle would say nothing about the other. -/

/-- The observer's instruments, as contexts. -/
inductive Instrument where
  /-- Ask which constructor a term is. -/
  | ask (constructor : String)
  /-- Read one argument out of a bundle. -/
  | get (constructor : String) (index : Nat)

/-- Placing a term in an instrument. -/
def Instrument.place (cut : CollType) : Instrument → Pattern → Pattern
  | .ask constructor, term =>
      .collection cut [.apply (askLabel constructor) [], term] none
  | .get constructor index, term => .apply (getLabel constructor index) [term]

/-- The barb: is this a bundle of the given constructor? -/
def IsBundle (constructor : String) : Pattern → Prop
  | .apply label _ => label = argsLabel constructor
  | _ => False

theorem isBundle_apply (constructor : String) (arguments : List Pattern) :
    IsBundle constructor (.apply (argsLabel constructor) arguments) := rfl

/-- A barb is a shape: only an application of the bundle former carries it. -/
theorem isBundle_shape {constructor : String} {pattern : Pattern}
    (bundle : IsBundle constructor pattern) :
    ∃ arguments : List Pattern, pattern = .apply (argsLabel constructor) arguments := by
  cases pattern
  case apply label arguments =>
      exact ⟨arguments, by rw [show label = argsLabel constructor from bundle]⟩
  all_goals exact bundle.elim

/-- **The opening instrument returns the bundle of the term's own arguments.**
The companion of `projection_response` on the other instrument: a step out of the
cut that reaches a bundle used the opening rule, and the opening rule delivers the
arguments it read. -/
theorem opening_response
    (base : BasePremiseEvaluator) (lang : LanguageDef) (cut : CollType)
    (opened : List String) {constructor : String}
    (setting : ObserverSetting base lang cut opened constructor)
    {declaration : GrammarRule} (declMember : declaration ∈ openedRules lang opened)
    (named : declaration.label = constructor)
    {arguments : List Pattern} {target : Pattern}
    (length : arguments.length = declaration.params.length)
    (argumentsAuthored :
      labelsList arguments ⊆ lang.terms.map GrammarRule.label)
    (step : Step base (observerExtension lang cut opened)
      (.collection cut
        [.apply (askLabel constructor) [], .apply constructor arguments] none) target)
    (bundle : IsBundle constructor target) :
    target = .apply (argsLabel constructor) arguments := by
  obtain ⟨bundleArguments, bundleShape⟩ := isBundle_shape bundle
  obtain ⟨rule, member, bindings, matched, fuel, final, premiseEvidence, built⟩ :=
    match_of_step step
  rw [matchPatternForRule_eq_syntactic] at matched
  simp only [observerExtension, List.mem_append] at member
  rcases member with authoredRule | adjoinedRule
  · refine absurd (built.trans bundleShape) ?_
    refine authored_target_not_argsHeaded base lang cut opened setting.fresh declMember
      named setting.confined ?_ (setting.tame.noSteps rule authoredRule)
      (setting.tame.clean rule authoredRule) (setting.tame.rights rule authoredRule)
      matched premiseEvidence
    intro label occurs
    simp only [Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_apply] at occurs
    rcases List.mem_cons.mp occurs with rfl | deeper
    · obtain ⟨declared, -⟩ := List.mem_filter.mp declMember
      exact named ▸ List.mem_map_of_mem declared
    · exact argumentsAuthored deeper
  · obtain ⟨inner, innerMember, ruleMember⟩ := List.mem_flatMap.mp adjoinedRule
    obtain ⟨sameLabel, ruleShape, -⟩ :=
      adjoined_match_forces_head lang cut opened setting.fresh
        (by
          show constructor ∈ lang.terms.map GrammarRule.label
          obtain ⟨declared, -⟩ := List.mem_filter.mp declMember
          exact named ▸ List.mem_map_of_mem declared)
        innerMember ruleMember matched
    have sameArity : inner.params.length = declaration.params.length :=
      setting.arities inner innerMember declaration declMember (by rw [sameLabel, named])
    rw [ruleShape, sameArity] at matched premiseEvidence built
    have sameBindings : final = bindings :=
      premisesAt_nil_eq (by simpa [openingRule] using premiseEvidence)
    subst sameBindings
    rw [applyBindingsForRule, applyBindingsForRuleUsing_empty] at built
    rw [← built, applyRuleBindings_openingRule]
    exact openingRule_delivers_of_match cut constructor length matched

/-- **The bisimulation the instruments induce.**  Not a reduction bisimilarity:
every clause names the instrument, and the barb clause names what the instruments
are for. -/
structure IsInstrumentBisimulation (base : BasePremiseEvaluator) (lang : LanguageDef)
    (cut : CollType) (opened : List String) (R : Pattern → Pattern → Prop) : Prop where
  /-- A response on the left is matched on the right, under the same instrument. -/
  forward : ∀ {left right : Pattern}, R left right →
    ∀ (instrument : Instrument) (next : Pattern),
      Step base (observerExtension lang cut opened) (instrument.place cut left) next →
      ∃ matched, Step base (observerExtension lang cut opened)
        (instrument.place cut right) matched ∧ R next matched
  /-- And conversely. -/
  backward : ∀ {left right : Pattern}, R left right →
    ∀ (instrument : Instrument) (next : Pattern),
      Step base (observerExtension lang cut opened) (instrument.place cut right) next →
      ∃ matched, Step base (observerExtension lang cut opened)
        (instrument.place cut left) matched ∧ R matched next
  /-- Related terms are bundles of the same constructor, or neither is. -/
  barbs : ∀ {left right : Pattern}, R left right →
    ∀ constructor, IsBundle constructor left ↔ IsBundle constructor right

/-- **Positive: the notion is inhabited.**  Equality is an instrument
bisimulation, so the definition is not vacuous. -/
theorem isInstrumentBisimulation_eq (base : BasePremiseEvaluator) (lang : LanguageDef)
    (cut : CollType) (opened : List String) :
    IsInstrumentBisimulation base lang cut opened Eq where
  forward := by rintro left right rfl instrument next step; exact ⟨next, step, rfl⟩
  backward := by rintro left right rfl instrument next step; exact ⟨next, step, rfl⟩
  barbs := by rintro left right rfl constructor; exact Iff.rfl

/-- **Negative: it is not the total relation.**  The observer's gap canary has two
inert constructors that no context of the authored theory separates; the opening
request for the first separates them, so relating them is not an instrument
bisimulation.  This is the same separation `ObserverExtension.Gap` exhibits, now
seen as a constraint on the relation rather than on the logic. -/
theorem isInstrumentBisimulation_not_total (base : BasePremiseEvaluator) :
    ¬ IsInstrumentBisimulation base ObserverExtension.Gap.inertPair .hashBag
      ObserverExtension.Gap.opened (fun _ _ => True) := by
  intro bisim
  obtain ⟨matched, stepped, -⟩ :=
    bisim.forward (left := ObserverExtension.Gap.termC)
      (right := ObserverExtension.Gap.termD) trivial (.ask "C") _
      (ObserverExtension.Gap.withC_steps base)
  exact ObserverExtension.Gap.withD_no_step base matched stepped

/-- **Related terms have the same head.**  Ask the left term which constructor it
is; it answers with a bundle.  The right term must answer the same instrument,
and the barb says its answer is a bundle of the same constructor, so by
`reads_head_iff` the right term is an application of that constructor too. -/
theorem head_agreement
    {base : BasePremiseEvaluator} {lang : LanguageDef} {cut : CollType}
    {opened : List String} {R : Pattern → Pattern → Prop}
    (bisim : IsInstrumentBisimulation base lang cut opened R)
    {constructor : String}
    (setting : ObserverSetting base lang cut opened constructor)
    {declaration : GrammarRule} (declMember : declaration ∈ openedRules lang opened)
    (named : declaration.label = constructor)
    {left right : Pattern} (related : R left right)
    (rightAuthored : labels right ⊆ lang.terms.map GrammarRule.label)
    (rightHeaded : HasOperationHead (lang.terms.map GrammarRule.label) right)
    {arguments : List Pattern} (leftShape : left = .apply constructor arguments)
    (leftArity : arguments.length = declaration.params.length) :
    ∃ rightArguments : List Pattern, right = .apply constructor rightArguments ∧
      rightArguments.length = declaration.params.length := by
  subst leftShape
  have asked : Step base (observerExtension lang cut opened)
      ((Instrument.ask constructor).place cut (.apply constructor arguments))
      (.apply (argsLabel constructor) arguments) := by
    have stepped := opening_step base lang cut opened declMember
      (arguments := arguments) leftArity
    rw [named] at stepped
    exact stepped
  obtain ⟨answer, answered, relatedAnswers⟩ :=
    bisim.forward related (.ask constructor) _ asked
  have answerIsBundle : IsBundle constructor answer :=
    (bisim.barbs relatedAnswers constructor).mp (isBundle_apply constructor arguments)
  obtain ⟨answerArguments, answerShape⟩ := isBundle_shape answerIsBundle
  subst answerShape
  exact (reads_head_iff base lang cut opened setting declMember named
    rightAuthored rightHeaded).mp ⟨answerArguments, answered⟩

/-- **Related terms have related arguments.**  Ask both which constructor they
are: by `head_agreement` they answer the same one, and by `opening_response` the
answers are the bundles of their own arguments, related by the bisimulation.  Then
read one position out of both bundles: by `projection_response` the responses are
the arguments at that position, and the bisimulation relates those too.

This is the descent.  Every step of it is a statement about what *any* match
binds, so nothing rests on a binding list exhibited apart from the one the
argument has in hand.

**The position must be projectable.**  A binder position is not, and that is not
an oversight of this proof but of the kit: projecting one would hand back an open
body whose sort the presentation does not declare.  So the descent reaches exactly
the positions the observer can actually read. -/
theorem argument_agreement
    {base : BasePremiseEvaluator} {lang : LanguageDef} {cut : CollType}
    {opened : List String} {R : Pattern → Pattern → Prop}
    (bisim : IsInstrumentBisimulation base lang cut opened R)
    {constructor : String}
    (setting : ObserverSetting base lang cut opened constructor)
    {declaration : GrammarRule} (declMember : declaration ∈ openedRules lang opened)
    (named : declaration.label = constructor)
    {left right : Pattern} (related : R left right)
    (rightAuthored : labels right ⊆ lang.terms.map GrammarRule.label)
    (rightHeaded : HasOperationHead (lang.terms.map GrammarRule.label) right)
    {leftArguments : List Pattern}
    (leftShape : left = .apply constructor leftArguments)
    (leftArity : leftArguments.length = declaration.params.length)
    {position : Nat × String} (projectable : position ∈ projectablePositions declaration)
    (bounded : position.1 < declaration.params.length)
    (adjoinedGet : getLabel constructor position.1 ∈ adjoinedLabels lang opened) :
    ∃ rightArguments : List Pattern, right = .apply constructor rightArguments ∧
      ∃ rightArity : rightArguments.length = declaration.params.length,
        R (leftArguments[position.1]'(by rw [leftArity]; exact bounded))
          (rightArguments[position.1]'(by rw [rightArity]; exact bounded)) := by
  obtain ⟨rightArguments, rightShape, rightArity⟩ :=
    head_agreement bisim setting declMember named related rightAuthored rightHeaded
      leftShape leftArity
  refine ⟨rightArguments, rightShape, rightArity, ?_⟩
  have leftOpens : Step base (observerExtension lang cut opened)
      ((Instrument.ask constructor).place cut left)
      (.apply (argsLabel constructor) leftArguments) := by
    rw [leftShape]
    have stepped := opening_step base lang cut opened declMember
      (arguments := leftArguments) leftArity
    rw [named] at stepped
    exact stepped
  obtain ⟨answer, answered, relatedBundles⟩ :=
    bisim.forward related (.ask constructor) _ leftOpens
  have answerIsBundle : IsBundle constructor answer :=
    (bisim.barbs relatedBundles constructor).mp
      (isBundle_apply constructor leftArguments)
  have rightArgsAuthored : labelsList rightArguments ⊆ lang.terms.map GrammarRule.label := by
    intro label occurs
    exact rightAuthored (by rw [rightShape]; exact List.mem_cons_of_mem _ occurs)
  have answerShape : answer = .apply (argsLabel constructor) rightArguments := by
    refine opening_response base lang cut opened setting declMember named rightArity
      rightArgsAuthored ?_ answerIsBundle
    rw [← rightShape]; exact answered
  rw [answerShape] at relatedBundles
  have leftProjects : Step base (observerExtension lang cut opened)
      ((Instrument.get constructor position.1).place cut
        (.apply (argsLabel constructor) leftArguments))
      (leftArguments[position.1]'(by rw [leftArity]; exact bounded)) := by
    have stepped := projection_step base lang cut opened declMember projectable
      bounded leftArity
    rw [named] at stepped
    exact stepped
  obtain ⟨response, responded, relatedArgs⟩ :=
    bisim.forward relatedBundles (.get constructor position.1) _ leftProjects
  have responseShape := projection_response base lang cut opened setting declMember
    named bounded rightArity adjoinedGet responded
  rw [responseShape] at relatedArgs
  exact relatedArgs

/-! ## Reconstruction, and the fragment the kit can currently reach

`ReadableByKit` below names the terms the observer's present instruments can take
apart: every head an opened constructor of matching arity, every position of it
projectable, hereditarily.  On those terms the descent runs to the leaves and the
induction closes.

**That fragment is narrow, and at present it is empty.**  Two exclusions, both
properties of the kit rather than of the argument:

* Only `apply` nodes are reachable.  The kit opens *declared constructors*, and a
  collection is not a declared constructor -- it is a former of the carrier.  So
  parallel composition is unreadable, and a process calculus whose terms *are*
  bags is therefore entirely outside the fragment.
* A binder position has no projection rule, because projecting one would hand
  back an open body whose sort the presentation does not declare.

Hereditary readability then makes this bite hard: at the one rho setting
instantiated here, a single constructor is opened, so a term of arity at least one
never bottoms out and the fragment has no inhabitants at all.  `reconstruction` is
consequently a theorem about the free `apply`-algebra over the opened signature,
with no instance yet exhibited.

**What is missing is instruments, not proof.**  An opening instrument for the cut
former, reading a bag into a bundle, and an abstraction sort with an instantiation
instrument for binder positions, would each remove one exclusion.  Both are
adjunctions of the same kind the extension already performs.  Until they exist
this theorem should be read as naming what the kit can reach, which is not yet the
calculus. -/

theorem getLabel_mem_adjoinedLabels (lang : LanguageDef) (opened : List String)
    {declaration : GrammarRule} (declMember : declaration ∈ openedRules lang opened)
    {position : Nat × String} (projectable : position ∈ projectablePositions declaration) :
    getLabel declaration.label position.1 ∈ adjoinedLabels lang opened := by
  refine List.mem_flatMap.mpr ⟨declaration, declMember, ?_⟩
  simp only [instrumentLabels, List.mem_cons, List.mem_map]
  exact Or.inr (Or.inr (Or.inr ⟨position, projectable, rfl⟩))

def ReadableHead (lang : LanguageDef) (opened : List String)
    (label : String) (arguments : List Pattern) : Prop :=
  ∃ declaration ∈ openedRules lang opened, declaration.label = label ∧
    declaration.params.length = arguments.length ∧
    ∀ index, index < arguments.length →
      ∃ position ∈ projectablePositions declaration, position.1 = index

mutual
def ReadableByKit (lang : LanguageDef) (opened : List String) : Pattern → Prop
  | .apply label arguments =>
      ReadableHead lang opened label arguments ∧
        ReadableByKitList lang opened arguments
  | _ => False

def ReadableByKitList (lang : LanguageDef) (opened : List String) : List Pattern → Prop
  | [] => True
  | pattern :: rest =>
      ReadableByKit lang opened pattern ∧ ReadableByKitList lang opened rest
end

theorem readableByKitList_mem {lang : LanguageDef} {opened : List String}
    {patterns : List Pattern} (readable : ReadableByKitList lang opened patterns)
    {pattern : Pattern} (member : pattern ∈ patterns) :
    ReadableByKit lang opened pattern := by
  induction patterns with
  | nil => exact absurd member List.not_mem_nil
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | inTail
      · exact readable.1
      · exact ih readable.2 inTail

theorem readableByKit_headed {lang : LanguageDef} {opened : List String}
    {term : Pattern} (readable : ReadableByKit lang opened term) :
    HasOperationHead (lang.terms.map GrammarRule.label) term := by
  cases term
  case apply label arguments =>
      obtain ⟨⟨declaration, declMember, named, -, -⟩, -⟩ := readable
      obtain ⟨declared, -⟩ := List.mem_filter.mp declMember
      exact named ▸ List.mem_map_of_mem declared
  all_goals exact readable.elim

mutual
theorem readableByKit_labels {lang : LanguageDef} {opened : List String} :
    ∀ (term : Pattern), ReadableByKit lang opened term →
      labels term ⊆ lang.terms.map GrammarRule.label
  | .apply label arguments, readable => by
      intro candidate occurs
      simp only [Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_apply] at occurs
      rcases List.mem_cons.mp occurs with rfl | deeper
      · exact readableByKit_headed readable
      · exact readableByKitList_labels arguments readable.2 deeper
  | .bvar _, readable => readable.elim
  | .fvar _, readable => readable.elim
  | .lambda _ _, readable => readable.elim
  | .multiLambda _ _ _, readable => readable.elim
  | .subst _ _, readable => readable.elim
  | .collection _ _ _, readable => readable.elim

theorem readableByKitList_labels {lang : LanguageDef} {opened : List String} :
    ∀ (patterns : List Pattern), ReadableByKitList lang opened patterns →
      labelsList patterns ⊆ lang.terms.map GrammarRule.label
  | [], _ => by simp
  | pattern :: rest, readable => by
      intro candidate occurs
      rcases List.mem_append.mp occurs with inHead | inTail
      · exact readableByKit_labels pattern readable.1 inHead
      · exact readableByKitList_labels rest readable.2 inTail
end

theorem reconstruction
    {base : BasePremiseEvaluator} {lang : LanguageDef} {cut : CollType}
    {opened : List String} {R : Pattern → Pattern → Prop}
    (bisim : IsInstrumentBisimulation base lang cut opened R)
    (settings : ∀ constructor : String,
      ObserverSetting base lang cut opened constructor) :
    ∀ (left right : Pattern), R left right →
      ReadableByKit lang opened left → ReadableByKit lang opened right →
      left = right := by
  intro left
  refine Pattern.inductionOn (motive := fun term => ∀ right, R term right →
    ReadableByKit lang opened term → ReadableByKit lang opened right → term = right)
    left ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intros; rename_i readable _; exact readable.elim
  · intros; rename_i readable _; exact readable.elim
  · intro constructor arguments ih right related leftReadable rightReadable
    obtain ⟨⟨declaration, declMember, named, arity, projectableAll⟩, argsReadable⟩ :=
      leftReadable
    have rightAuthored := readableByKit_labels right rightReadable
    have rightHeaded := readableByKit_headed rightReadable
    have leftArity : arguments.length = declaration.params.length := arity.symm
    obtain ⟨rightArguments, rightShape, rightArity⟩ :=
      head_agreement bisim (settings constructor) declMember named related
        rightAuthored rightHeaded rfl leftArity
    have rightArgsReadable : ReadableByKitList lang opened rightArguments := by
      rw [rightShape] at rightReadable
      exact rightReadable.2
    have componentwise : ∀ index (h₁ : index < arguments.length)
        (h₂ : index < rightArguments.length), arguments[index] = rightArguments[index] := by
      intro index leftBound rightBound
      obtain ⟨position, projectable, positionIndex⟩ := projectableAll index leftBound
      have bounded : position.1 < declaration.params.length := by
        rw [positionIndex, ← leftArity]; exact leftBound
      have adjoinedGet : getLabel constructor position.1 ∈ adjoinedLabels lang opened := by
        have got := getLabel_mem_adjoinedLabels lang opened declMember projectable
        rwa [named] at got
      obtain ⟨otherArguments, otherShape, otherArity, relatedArgs⟩ :=
        argument_agreement bisim (settings constructor) declMember named related
          rightAuthored rightHeaded rfl leftArity projectable bounded adjoinedGet
      have sameArguments : otherArguments = rightArguments := by
        have combined := otherShape.symm.trans rightShape
        injection combined with _ same
      subst sameArguments
      have equalAt := ih (arguments[position.1]'(by rw [leftArity]; exact bounded))
        (List.getElem_mem _) _ relatedArgs
        (readableByKitList_mem argsReadable (List.getElem_mem _))
        (readableByKitList_mem rightArgsReadable (List.getElem_mem _))
      simp only [positionIndex] at equalAt
      exact equalAt
    rw [rightShape]
    refine congrArg (Pattern.apply constructor) ?_
    exact List.ext_getElem (by rw [leftArity, rightArity]) componentwise
  · intros; rename_i readable _; exact readable.elim
  · intros; rename_i readable _; exact readable.elim
  · intros; rename_i readable _; exact readable.elim
  · intros; rename_i readable _; exact readable.elim

/-! ## A congruence premise can smuggle the bundle out

The boundary named above is not hypothetical.  `RulesAvoid` is false of the
extension because the opening rule writes the bundle former, and an authored rule
whose premise takes a step can reach that rule and carry the result out -- from a
cut whose term is perfectly ordinary.

The presentation below does it in one step.  Its single rule is authored, cites
only authored constructors, and its administrative vocabulary is fresh; what it
does is rebuild the bag with a `C` where a `W` stood, and return whatever that
steps to.  Beside an opening request, the rebuilt bag is a redex of the opening
rule, and the bundle comes back out as the rule's own result.

**So the `noSteps` hypothesis of `authored_target_not_argsHeaded` is necessary**,
not a convenience: dropped, the conclusion is false.  Rho's join rule satisfies
it -- its only premise is a relation query -- which is why the observer argument
reaches that presentation. -/

namespace Smuggling

def sortT : String := "T"

def declC : GrammarRule where
  label := "C"
  category := sortT
  params := []
  syntaxPattern := [.terminal "C"]

def declW : GrammarRule where
  label := "W"
  category := sortT
  params := []
  syntaxPattern := [.terminal "W"]

/-- Authored, citing only authored constructors, with a premise that steps. -/
def drainRule : RewriteRule where
  name := "drain"
  typeContext := [("z", .base sortT), ("y", .base sortT)]
  premises := [.congruence (.collection .hashBag [.fvar "z", .apply "C" []] none) (.fvar "y")]
  left := .collection .hashBag [.fvar "z", .apply "W" []] none
  right := .fvar "y"

def carrier : LanguageDef where
  name := "Carrier"
  types := [TypeDecl.plain sortT]
  terms := [declC, declW]
  equations := []
  rewrites := [drainRule]

/-- Freshness holds, so the failure is not a failure of freshness. -/
theorem carrier_fresh : AdministrativeFresh carrier ["C"] := by decide +kernel

def extended : LanguageDef := observerExtension carrier .hashBag ["C"]

def askC : Pattern := .apply (askLabel "C") []
def termW : Pattern := .apply "W" []
def evaluator : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

/-- **The cut steps straight to the bundle**, in one step of the extension. -/
theorem cut_reaches_bundle :
    rewriteAt evaluator extended 4 (.collection .hashBag [askC, termW] none)
      = [.apply (argsLabel "C") []] := by
  decide +kernel

/-- And the term standing beside the request is not an application of the
constructor the request names. -/
theorem termW_not_headed :
    ¬ ∃ arguments : List Pattern, termW = .apply "C" arguments := by
  rintro ⟨arguments, shape⟩
  simp [termW] at shape

/-- **So reaching the bundle does not determine the head either**, once premises
may take steps.  Both halves are witnessed. -/
theorem reaching_bundle_does_not_determine_head :
    (rewriteAt evaluator extended 4 (.collection .hashBag [askC, termW] none)
        = [.apply (argsLabel "C") []]) ∧
      ¬ ∃ arguments : List Pattern, termW = .apply "C" arguments :=
  ⟨cut_reaches_bundle, termW_not_headed⟩

/-- The rule that does it has a congruence premise, which is exactly what
`authored_target_not_argsHeaded` excludes. -/
theorem drainRule_has_congruence :
    ¬ ∀ premise ∈ drainRule.premises, ¬ IsCongruence premise := by
  intro noSteps
  exact noSteps _ (List.mem_cons_self ..) trivial

end Smuggling

/-! ## A projection's response is not determined

The descent from heads to arguments needs more than `head_agreement` gives.
Bisimulation supplies a *matching* step under the projection instrument; the
descent needs that step to *be* the projection, so that what comes back is the
corresponding argument.  It need not be.

An authored rule whose left-hand side is a bare metavariable matches anything at
all, including a projection request, and answers it with whatever it likes.  The
presentation below has one such rule; its administrative vocabulary is fresh; and
the request has two distinct responses.

**The condition this identifies** is that no authored left-hand side is a bare
metavariable.  Nothing weaker will do and nothing stronger is needed: an `apply`
left-hand side cannot match an adjoined head, because freshness separates the
labels; a `collection`, `lambda` or `subst` left-hand side cannot match an
application at all.  Only a variable matches everything.  Rho's rules have
collection left-hand sides, so they satisfy it. -/

namespace Determinacy

def sortT : String := "T"

/-- Unary, so it has a projectable position. -/
def declC : GrammarRule where
  label := "C"
  category := sortT
  params := [.simple "a" (.base sortT)]
  syntaxPattern := [.terminal "C"]

def declW : GrammarRule where
  label := "W"
  category := sortT
  params := []
  syntaxPattern := [.terminal "W"]

def declZ : GrammarRule where
  label := "Z"
  category := sortT
  params := []
  syntaxPattern := [.terminal "Z"]

/-- **A left-hand side that is a bare metavariable.**  It matches every term. -/
def catchAll : RewriteRule where
  name := "catchall"
  typeContext := [("x", .base sortT)]
  premises := []
  left := .fvar "x"
  right := .apply "Z" []

def carrier : LanguageDef where
  name := "Carrier"
  types := [TypeDecl.plain sortT]
  terms := [declC, declW, declZ]
  equations := []
  rewrites := [catchAll]

theorem carrier_fresh : AdministrativeFresh carrier ["C"] := by decide +kernel

def extended : LanguageDef := observerExtension carrier .hashBag ["C"]

def evaluator : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

def bundle : Pattern := .apply (argsLabel "C") [.apply "W" []]

def request : Pattern := .apply (getLabel "C" 0) [bundle]

/-- **Two responses, not one.**  The catch-all answers `Z`; the projection rule
answers the argument `W`. -/
theorem request_has_two_responses :
    rewriteAt evaluator extended 4 request
      = [.apply "Z" [], .apply "W" []] := by
  decide +kernel

/-- **So the response is not determined.**  A bisimulation that matches the
projection instrument may be matched by the catch-all instead, and what comes
back is not the argument. -/
theorem projection_response_not_determined :
    ∃ first second : Pattern, first ≠ second ∧
      first ∈ rewriteAt evaluator extended 4 request ∧
      second ∈ rewriteAt evaluator extended 4 request := by
  refine ⟨.apply "Z" [], .apply "W" [], by decide, ?_, ?_⟩
  · rw [request_has_two_responses]; exact List.Mem.head _
  · rw [request_has_two_responses]; exact List.Mem.tail _ (List.Mem.head _)

/-- And the offending presentation is exactly the one the condition excludes. -/
theorem carrier_not_rigid : ¬ RigidHeads carrier := by decide +kernel

end Determinacy

/-! ## Rigidity alone is not enough

`Determinacy` excluded left-hand sides that match everything.  A left-hand side
can be rigid and still answer the observer's request: it need only be an
application whose head is a label the presentation never declared, and freshness
says nothing about labels a rule *uses*, only about labels a presentation
*declares*.

Below, freshness holds, rigidity holds, and the projection request still has two
responses.  `LeftHeadsDeclared` is what excludes it. -/

namespace Citation

def sortT : String := "T"

def declC : GrammarRule where
  label := "C"
  category := sortT
  params := [.simple "a" (.base sortT)]
  syntaxPattern := [.terminal "C"]

def declW : GrammarRule where
  label := "W"
  category := sortT
  params := []
  syntaxPattern := [.terminal "W"]

def declZ : GrammarRule where
  label := "Z"
  category := sortT
  params := []
  syntaxPattern := [.terminal "Z"]

/-- Rigid -- its left-hand side is an application -- but the application names a
constructor the presentation never declared, and that constructor is the
observer's own projection former. -/
def impostor : RewriteRule where
  name := "impostor"
  typeContext := [("x", .base sortT)]
  premises := []
  left := .apply (getLabel "C" 0) [.fvar "x"]
  right := .apply "Z" []

def carrier : LanguageDef where
  name := "Carrier"
  types := [TypeDecl.plain sortT]
  terms := [declC, declW, declZ]
  equations := []
  rewrites := [impostor]

theorem carrier_fresh : AdministrativeFresh carrier ["C"] := by decide +kernel

theorem carrier_rigid : RigidHeads carrier := by decide +kernel

/-- And yet it is not cited: that is the condition it violates. -/
theorem carrier_not_cited : ¬ LeftHeadsDeclared carrier := by decide +kernel

def extended : LanguageDef := observerExtension carrier .hashBag ["C"]

def evaluator : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

def request : Pattern :=
  .apply (getLabel "C" 0) [.apply (argsLabel "C") [.apply "W" []]]

/-- **Two responses again**, with freshness and rigidity both holding. -/
theorem request_has_two_responses :
    rewriteAt evaluator extended 4 request
      = [.apply "Z" [], .apply "W" []] := by
  decide +kernel

/-- **So rigidity alone does not determine the response.** -/
theorem rigidity_alone_insufficient :
    AdministrativeFresh carrier ["C"] ∧ RigidHeads carrier ∧
      ∃ first second : Pattern, first ≠ second ∧
        first ∈ rewriteAt evaluator extended 4 request ∧
        second ∈ rewriteAt evaluator extended 4 request := by
  refine ⟨carrier_fresh, carrier_rigid, .apply "Z" [], .apply "W" [], by decide, ?_, ?_⟩
  · rw [request_has_two_responses]; exact List.Mem.head _
  · rw [request_has_two_responses]; exact List.Mem.tail _ (List.Mem.head _)

end Citation

end Mettapedia.OSLF.Framework.ObserverReconstruction
