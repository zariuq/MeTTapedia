import Mettapedia.OSLF.Framework.GeneratedModalFamily
import Mettapedia.GSLT.Dynamics.EvidenceWeighting
import Mettapedia.OSLF.Framework.GeneratedScopeRho
import Mettapedia.OSLF.Framework.ObserverBisimilarity
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation

/-!
# The generator, run on two whole presentations

`GeneratedModalFamily` takes a `LanguageDef` to the family of every redex site
it has, with each site's rely parameters, slot count, generated centre and
modality computed from the site.  This module runs it, on the tree's authored
rho and on the generated platform, and reports what it finds.

The two answers differ, and the difference is the point.  The authored rho
presentation fails the presentation-level check: eight of its ten sites mint a
sort slot for a metavariable the rule does not declare.  The generated platform
passes at every one of its twenty-four.  A check that separates two real
presentations is a property of presentations; one that held of everything would
be a formality.

The gate of the first deliverable is then re-run at the platform's own join,
where nothing at all was written by hand: the slot count is the arity plus the
remainder plus the output, the generated centre is the whole cube of that
dimension, and fixing the output slot cuts it to a face by one condition on one
slot.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformModalFamily

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ModalHypercube
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.Framework.GeneratedHypercube
open Mettapedia.OSLF.Framework.GeneratedModalFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation

/-! ## The authored presentation -/

/-- The tree's rho has ten redex sites. -/
theorem rhoCalc_site_count : (redexSites rhoCalc).length = 10 := by decide +kernel

/-- **And it fails the presentation-level check.** -/
theorem rhoCalc_fails_check : allRelyVarsDeclared rhoCalc = false := by decide +kernel

/-- Eight of the ten sites mint a slot for a metavariable the rule does not
declare — which is the defect the generated rule of `GeneratedHypercubeInstances`
was written to isolate, counted here over the whole presentation. -/
theorem rhoCalc_undeclared_count :
    ((redexSites rhoCalc).filter fun site =>
      ! RelyVarsDeclared site.1 site.2).length = 8 := by decide +kernel

/-- So some site of it mints an undeclared slot, by the general theorem rather
than by inspection. -/
theorem rhoCalc_has_undeclared_site :
    ∃ site ∈ redexSites rhoCalc, RelyVarsDeclared site.1 site.2 = false :=
  exists_undeclared_of_not_all rhoCalc_fails_check

/-! ## The generated presentation -/

/-- The platform supporting binary joins has twenty-four redex sites. -/
theorem platform_site_count : (redexSites (rhoPlatform [2])).length = 24 := by
  decide +kernel

/-- **And it passes the check at every one of them.** -/
theorem platform_passes_check : allRelyVarsDeclared (rhoPlatform [2]) = true := by
  decide +kernel

/-- So every site of the platform declares every slot it mints. -/
theorem platform_every_site_declared {site : Site}
    (member : site ∈ redexSites (rhoPlatform [2])) :
    RelyVarsDeclared site.1 site.2 = true :=
  relyVarsDeclared_of_all platform_passes_check member

/-- The two presentations answer the check differently, which is what makes it
a check. -/
theorem check_separates_presentations :
    allRelyVarsDeclared rhoCalc = false ∧ allRelyVarsDeclared (rhoPlatform [2]) = true :=
  ⟨rhoCalc_fails_check, platform_passes_check⟩

/-! ## The gate, at the platform's own join -/

/-- The join of a given arity, at its continuation. -/
def joinSite (arity : Nat) : Site := (joinRule arity, joinPos arity)

theorem joinSite_one_mem : joinSite 1 ∈ redexSites (rhoPlatform [1]) :=
  (mem_redexSites_iff _ _).mpr ⟨joinRule_mem (by decide), by decide⟩

theorem joinSite_two_mem : joinSite 2 ∈ redexSites (rhoPlatform [2]) :=
  (mem_redexSites_iff _ _).mpr ⟨joinRule_mem (by decide), by decide⟩

/-- **Arity one.**  The remainder, one channel and one value, and the output:
four slots. -/
theorem joinSite_one_slotCount : siteSlotCount (joinSite 1) = 4 := by decide

/-- The generated centre is the whole four-cube: the platform authors no
equations, so nothing constrains the assignment. -/
theorem joinSite_one_center_eq_univ :
    siteCenter firstProjection (rhoPlatform [1]) (joinSite 1) = Finset.univ := by
  decide +kernel

theorem joinSite_one_center_card :
    (siteCenter firstProjection (rhoPlatform [1]) (joinSite 1)).card = 16 := by
  decide +kernel

/-- **And fixing the output slot cuts it to a face**, by one condition on one
slot — the gate, at a rule the generator produced from an arity. -/
theorem joinSite_one_face_card :
    (siteFace firstProjection (rhoPlatform [1]) (joinSite 1) .star).card = 8 := by
  decide +kernel

theorem joinSite_one_face_is_face :
    siteFace firstProjection (rhoPlatform [1]) (joinSite 1) .star =
      Finset.univ.filter fun σ =>
        σ (outputIndex (siteRelyVars (joinSite 1))) == .star := by
  decide +kernel

/-- **Arity two.**  The remainder, two channels, two values and the output: six
slots, and the cube grows with the arity rather than being listed. -/
theorem joinSite_two_slotCount : siteSlotCount (joinSite 2) = 6 := by decide

theorem joinSite_two_center_eq_univ :
    siteCenter firstProjection (rhoPlatform [2]) (joinSite 2) = Finset.univ := by
  decide +kernel

theorem joinSite_two_center_card :
    (siteCenter firstProjection (rhoPlatform [2]) (joinSite 2)).card = 64 := by
  decide +kernel

theorem joinSite_two_face_card :
    (siteFace firstProjection (rhoPlatform [2]) (joinSite 2) .star).card = 32 := by
  decide +kernel

/-- **The dimension is read off the arity.**  Two arities, two cubes, and the
slot count is the arity doubled plus two — the remainder and the output. -/
theorem cube_dimension_tracks_arity :
    siteSlotCount (joinSite 1) = 2 * 1 + 2 ∧ siteSlotCount (joinSite 2) = 2 * 2 + 2 :=
  ⟨rfl, rfl⟩

/-! ## The weighting layer, on this presentation

A where-weight reads the binder arity of the rule it matched.  The platform
declares its formers, so the arities are computed from the presentation rather
than supplied beside it, and the weighting separates the formers that bind from
the formers that do not. -/

namespace Weighting

open Mettapedia.GSLT.EvidenceWeighting
open Mettapedia.OSLF.MeTTaIL.Match

/-- The join of any arity binds exactly one name: the continuation's. -/
theorem joinDeclaration_binderArity (label : String) (arity : Nat) :
    binderArity (joinDeclaration label arity) = 1 := by
  simp [binderArity, joinDeclaration, binderCount, List.map_append,
    Function.comp_def]

/-- The output former binds nothing. -/
theorem outDeclaration_binderArity : binderArity outDeclaration = 0 := by decide

/-- Nor does the parallel carrier, nor the terminated process. -/
theorem parDeclaration_binderArity : binderArity parDeclaration = 0 := by decide

theorem stopDeclaration_binderArity : binderArity stopDeclaration = 0 := by decide

/-- **So the where-weight separates the presentation's formers**, on the same
empty match, by an arity each of them declares. -/
theorem byBinderArity_separates_platform (arity : Nat) :
    byBinderArity (joinDeclaration (joinLabel arity) arity) [] ≠
      byBinderArity outDeclaration [] := by
  rw [byBinderArity, byBinderArity, joinDeclaration_binderArity,
    outDeclaration_binderArity]
  exact Nat.one_ne_zero

/-- And no weighting that reads only the match can do it. -/
theorem readsOnlyMatch_blind_on_platform {W : Type*}
    {weigh : GrammarRule → Bindings → W} (blind : ReadsOnlyMatch weigh)
    (arity : Nat) (bindings : Bindings) :
    weigh (joinDeclaration (joinLabel arity) arity) bindings =
      weigh outDeclaration bindings := by
  obtain ⟨underlying, factorisation⟩ := blind
  rw [factorisation, factorisation]

end Weighting

/-! ## The name scope, on this presentation

The generated scope of a reflective calculus is built from a quote, a drop and a
parallel composition.  This presentation declares all three, and the scope's
formers are those declarations rather than a vocabulary that happens to share
their names: `quote_is_declared`, `drop_is_declared` and `par_is_declared` say
so, and the equalities below are definitional. -/

namespace Scope

open Mettapedia.OSLF.Framework.GeneratedScopeRho
open Mettapedia.OSLF.Framework.GeneratedScope (quote par)

/-- The scope's quote is the presentation's. -/
theorem quote_is_platform_quote (process : Pattern) :
    quote process = .apply quoteLabel [process] := rfl

/-- And its drop. -/
theorem drop_is_platform_drop (name : Pattern) :
    drop name = .apply dropLabel [name] := rfl

/-- And its composition is the declared parallel carrier's. -/
theorem par_is_platform_par (left right : Pattern) :
    par left right = .collection .hashBag [left, right] none := rfl

theorem quote_is_declared : quoteDeclaration ∈ (rhoPlatform [2]).terms := by
  simp [rhoPlatform]

theorem drop_is_declared : dropDeclaration ∈ (rhoPlatform [2]).terms := by
  simp [rhoPlatform]

theorem par_is_declared : parDeclaration ∈ (rhoPlatform [2]).terms := by
  simp [rhoPlatform]

/-- The platform's terminated process. -/
def stopTerm : Pattern := .apply stopDeclaration.label []

/-- An atom accepting only it.  It accepts no drop, so the two readings of a
part do not overlap and the descent decides membership. -/
def isStop : Pattern → Bool := fun term => term == stopTerm

theorem isStop_disjoint : AtomsAvoidDrops isStop := by
  intro inner
  simp [isStop, stopTerm, drop, dropLabel]

/-- **Positive.**  The quote of two terminated processes is a name of the
scope. -/
theorem base_in_scope : inScope isStop isStop (quote (par stopTerm stopTerm)) = true := by
  rw [quote, par, inScope] <;> simp [isStop, stopTerm, dropLabel]

/-- **And the coercion works on this presentation**: the quote of that name's
drop beside a terminated process is a name of the scope too. -/
theorem drop_in_scope :
    inScope isStop isStop (quote (par (drop (quote (par stopTerm stopTerm))) stopTerm)) = true := by
  rw [quote, par, drop, inScope]
  · exact Bool.and_eq_true_iff.mpr ⟨base_in_scope, by simp [isStop, stopTerm]⟩
  · intro b isRight
    simp [stopTerm, dropLabel] at isRight

/-- **Negative.**  A declared process that is not a quote is not a name of the
scope. -/
theorem stopTerm_not_in_scope : inScope isStop isStop stopTerm = false := by
  rw [stopTerm, inScope.eq_def]
  split <;> simp_all [stopDeclaration]

/-- **So item four runs on this presentation**: the scope is generated from the
presentation's own three formers, membership is decided by descent, and the two
readings agree at a name the coercion reaches and at a term outside. -/
theorem scope_on_platform :
    generatedScope (fun t => isStop t = true) (fun t => isStop t = true)
        (quote (par (drop (quote (par stopTerm stopTerm))) stopTerm)) ∧
      ¬ generatedScope (fun t => isStop t = true) (fun t => isStop t = true) stopTerm := by
  refine ⟨(inScope_iff isStop_disjoint isStop_disjoint _).mp drop_in_scope, ?_⟩
  intro member
  have decided := (inScope_iff isStop_disjoint isStop_disjoint stopTerm).mpr member
  rw [stopTerm_not_in_scope] at decided
  exact Bool.noConfusion decided

end Scope

/-! ## The observer, on this presentation

The conservativity route of `ObserverExtension` asks that a presentation's rules
call only within the authored vocabulary, and `CallsWithin` refuses a
`relationQuery` premise.  That refusal is correct — a `relationQuery` makes no
recursive call, so the closed-subsystem argument has nothing to say about it —
but it means this presentation cannot reach the observer theorems that way.  It
reaches them the other way: agreement of the two step relations is settled by
computation on the fragment.

**Why the fragment is inert, and why that is a fact about the presentation.**
Both rule families match at a bag, so no term headed by a declared operation is
a redex.  The fragment of authored-headed terms is therefore closed under steps
for the strongest possible reason, and `platform_rewrites_match_collections`
says this of every rule rather than of the terms chosen. -/

namespace Observer

open Mettapedia.OSLF.Framework.ObserverBisimilarity
open Mettapedia.OSLF.Framework.ObserverExtension
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.Framework.KSUnificationSketch

/-- **Every redex of this presentation is a composition.** -/
theorem platform_rewrites_match_collections (arities : List Nat) {rule : RewriteRule}
    (member : rule ∈ (rhoPlatform arities).rewrites) :
    ∃ elements : List Pattern,
      rule.left = .collection .hashBag elements (some restVar) := by
  obtain ⟨arity, -, ruleMember⟩ := List.mem_flatMap.mp member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ruleMember
  rcases ruleMember with rfl | rfl
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- The evaluator. -/
def evaluator : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

/-- The presentation, and the instrument set: the observer may open the output
former. -/
abbrev platform : LanguageDef := rhoPlatform [2]

abbrev opened : List String := [outLabel]

abbrev instrumented : LanguageDef := observerExtension platform .hashBag opened

/-- Two terms headed by declared operations. -/
def stopTerm : Pattern := .apply stopDeclaration.label []

def outTerm : Pattern :=
  .apply outLabel [.apply quoteLabel [stopTerm], stopTerm]

theorem stopTerm_authored : rewriteAt evaluator platform 4 stopTerm = [] := by
  decide +kernel

theorem outTerm_authored : rewriteAt evaluator platform 4 outTerm = [] := by
  decide +kernel

theorem stopTerm_instrumented : rewriteAt evaluator instrumented 4 stopTerm = [] := by
  decide +kernel

theorem outTerm_instrumented : rewriteAt evaluator instrumented 4 outTerm = [] := by
  decide +kernel

/-- **The fragment**: the two terms, on which the two step relations agree
because neither has a successor under either. -/
def fragment :
    AgreeingFragment (computedStep evaluator platform 4)
      (computedStep evaluator instrumented 4) where
  Mem := fun term => term = stopTerm ∨ term = outTerm
  agree := by
    rintro term (rfl | rfl) next <;>
      simp [computedStep, stopTerm_authored, outTerm_authored,
        stopTerm_instrumented, outTerm_instrumented]
  closed := by
    rintro term (rfl | rfl) next step <;>
      simp [computedStep, stopTerm_authored, outTerm_authored] at step

theorem stopTerm_mem : fragment.Mem stopTerm := Or.inl rfl

theorem outTerm_mem : fragment.Mem outTerm := Or.inr rfl

/-- **So bisimilarity is unchanged by the instruments here**, at this instrument
set. -/
theorem bisimilar_unchanged :
    Bisimilar (computedStep evaluator platform 4) stopTerm outTerm ↔
      Bisimilar (computedStep evaluator instrumented 4) stopTerm outTerm :=
  bisimilar_iff fragment stopTerm_mem outTerm_mem

/-- The formula asking whether anything happens. -/
def canStep : OSLFFormula := .dia .top

/-- **And the logic agrees**, for the generator-free forward-only formulas. -/
theorem readings_agree (I : AtomSem) :
    sem (computedStep evaluator platform 4) I canStep outTerm ↔
      sem (computedStep evaluator instrumented 4) I canStep outTerm :=
  sem_agree fragment I canStep rfl rfl outTerm_mem

/-- Neither term steps, so both fail the formula in both readings — which is the
content of the fragment being inert, stated rather than left implicit. -/
theorem neither_steps (I : AtomSem) :
    ¬ sem (computedStep evaluator platform 4) I canStep outTerm := by
  rintro ⟨next, step, -⟩
  simp [computedStep, outTerm_authored] at step

/-- **Adequacy with its instrument index, on this presentation**: a formula
separates two terms of the fragment in the instrumented reading exactly when it
does in the authored one. -/
theorem separates_unchanged (I : AtomSem) :
    (sem (computedStep evaluator platform 4) I canStep outTerm ∧
        ¬ sem (computedStep evaluator platform 4) I canStep stopTerm) ↔
      (sem (computedStep evaluator instrumented 4) I canStep outTerm ∧
        ¬ sem (computedStep evaluator instrumented 4) I canStep stopTerm) :=
  separates_iff fragment I canStep rfl rfl outTerm_mem stopTerm_mem

end Observer

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformModalFamily
