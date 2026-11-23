import Mettapedia.GSLT.Compilation.RootRewritesOnTheStep

/-!
# Authored bag rewrites compiled to takes and makes

A rewrite `{p₁, …, pₘ, ...rest} ~> {q₁, …, qₙ, ...rest}` with first-order
members, no premise and every variable of a `qⱼ` bound by some `pᵢ` is compiled
to the transform rule that takes the `pᵢ` and makes the `qⱼ`. A member of the
bag is one row, and the rest is the frame of the firing.

* **Source semantics**: the language's own one-step reduction at a closed top
  bag (`ContextualStep.Step`), read on the multiset of its members (`BagStep`).
  Inside a member no law is used.
* **Any arrangement**: the reduction does not depend on the order the members
  are written in (`bagStep_iff_arrangement`), and its result is again a closed
  bag (`rewrites_of_step`).
* **On the step**: one reduction for one firing, in both directions, with no
  target outside the image (`stepCorrespondence`, by `Machines.correspondence`).
* **Text**: the program in tcalc notation (`programText`). No theorem here speaks
  about a reader of that text.
* **Observation**: which successor bags are possible. How many matches give one
  successor is not observed (`Controls.equal_occurrences`). The order of the
  rules is no priority (`Controls.race_steps`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.BagRewritesOnTheStep

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Substitution (freeVars)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Mettapedia.OSLF.Framework.PredFiniteSufficient
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax
open RuleSyntax.Presentation.Schematic
open RuleSyntax.Machines
open RootRewritesOnTheStep (encode encode_injective labelCode labelCode_injective lower?
  matchCorrect_of_lower unknowns_lower inst_lower captures exists_bindings)

/-- A closed bag of members. -/
abbrev bag (members : List Pattern) : Pattern := .collection .hashBag members none

/-! ## Members -/

/-- The row patterns of the members of one side. -/
def lowerEach? : List Pattern → Option (List Tm)
  | [] => some []
  | pattern :: patterns =>
      (lower? pattern).bind fun first => (lowerEach? patterns).map fun others => first :: others

theorem matchCorrect_of_lowerEach : ∀ {patterns : List Pattern} {terms : List Tm},
    lowerEach? patterns = some terms → ∀ pattern ∈ patterns, isMatchCorrectAux pattern = true
  | [], _, _ => by simp
  | first :: others, _, lowered => by
      simp only [lowerEach?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨term, firstLowered, terms, othersLowered, _⟩ := lowered
      intro pattern member
      rcases List.mem_cons.mp member with rfl | later
      · exact matchCorrect_of_lower _ _ firstLowered
      · exact matchCorrect_of_lowerEach othersLowered pattern later

theorem unknowns_lowerEach : ∀ {patterns : List Pattern} {terms : List Tm},
    lowerEach? patterns = some terms → terms.flatMap unknowns = (patterns.flatMap freeVars).map labelCode
  | [], _, lowered => by
      simp only [lowerEach?, Option.some.injEq] at lowered
      subst lowered
      rfl
  | first :: others, _, lowered => by
      simp only [lowerEach?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨term, firstLowered, terms, othersLowered, rfl⟩ := lowered
      simp [unknowns_lower _ _ firstLowered, unknowns_lowerEach othersLowered]

theorem inst_lowerEach (θ : ℕ → Expr) (bindings : Bindings) : ∀ {patterns : List Pattern} {terms : List Tm},
    lowerEach? patterns = some terms →
    (∀ name ∈ patterns.flatMap freeVars, θ (labelCode name) = encode (applyBindings bindings (.fvar name))) →
    terms.map (inst θ) = (patterns.map (applyBindings bindings)).map encode
  | [], _, lowered, _ => by
      simp only [lowerEach?, Option.some.injEq] at lowered
      subst lowered
      rfl
  | first :: others, _, lowered, agree => by
      simp only [lowerEach?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨term, firstLowered, terms, othersLowered, rfl⟩ := lowered
      simp only [List.flatMap_cons, List.mem_append] at agree
      simp only [List.map_cons]
      rw [inst_lower θ bindings _ _ firstLowered (fun name member => agree name (.inl member)),
        inst_lowerEach θ bindings othersLowered (fun name member => agree name (.inr member))]

theorem capturesEach (θ : ℕ → Expr) : ∀ {patterns : List Pattern} {terms : List Tm} {sources : List Pattern},
    lowerEach? patterns = some terms → terms.map (inst θ) = sources.map encode →
    ∀ name ∈ patterns.flatMap freeVars, ∃ value, θ (labelCode name) = encode value
  | [], _, _, _, _ => by simp
  | first :: others, _, sources, lowered, met => by
      simp only [lowerEach?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨term, firstLowered, terms, othersLowered, rfl⟩ := lowered
      cases sources with
      | nil => simp at met
      | cons source sources =>
          simp only [List.map_cons, List.cons.injEq] at met
          intro name member
          simp only [List.flatMap_cons, List.mem_append] at member
          rcases member with inFirst | inOthers
          · exact captures θ _ _ source firstLowered met.1 name inFirst
          · exact capturesEach θ othersLowered met.2 name inOthers

/-! ## The matcher at a bag with a rest -/

/-- **Soundness at a bag.** A match divides the members into instances of the
patterns and the bag the rest is bound to. -/
theorem matchBag_sound_instance {rest : String} : ∀ {patterns members : List Pattern} {bindings : Bindings},
    (∀ pattern ∈ patterns, isMatchCorrectAux pattern = true) →
    MatchBagRel patterns (some rest) .hashBag members bindings →
    ∃ remainder, ∀ extended, BindingsExtends bindings extended →
      (patterns.map (applyBindings extended) ++ remainder).Perm members ∧
        applyBindings extended (.fvar rest) = bag remainder
  | [], members, _, _, matched => by
      cases matched
      refine ⟨members, fun extended extends_ => ⟨List.Perm.refl _, ?_⟩⟩
      have found := extends_ rest (bag members) (by simp)
      simp [applyBindings, found]
  | first :: others, members, _, correct, matched => by
      cases matched with
      | cons index bound headMatch tailMatch merged =>
          obtain ⟨remainder, holds⟩ := matchBag_sound_instance
            (fun pattern member => correct pattern (List.mem_cons_of_mem _ member)) tailMatch
          refine ⟨remainder, fun extended extends_ => ?_⟩
          obtain ⟨perm, restBound⟩ := holds extended (extends_trans (extends_right merged) extends_)
          have head := matchRel_correct_of_extends headMatch (correct first List.mem_cons_self)
            (extends_trans (extends_left merged) extends_)
          refine ⟨?_, restBound⟩
          rw [List.map_cons, head, List.cons_append]
          exact (perm.cons _).trans (List.getElem_cons_eraseIdx_perm bound)

/-- **Completeness at a bag, in every arrangement.** Where instances of the
patterns beside a remainder are the members, some match finds those instances
and binds the rest to an arrangement of that remainder. -/
theorem matchBag_complete_instance (bindings : Bindings) (rest : String) :
    ∀ (patterns members remainder : List Pattern),
      (∀ pattern ∈ patterns, isMatchCorrectAux pattern = true) →
      (patterns.map (applyBindings bindings) ++ remainder).Perm members →
      ∃ arranged, arranged.Perm remainder ∧ ∀ chosen,
        patterns.map (applyBindings chosen) = patterns.map (applyBindings bindings) →
        applyBindings chosen (.fvar rest) = bag arranged →
        ∃ found, MatchBagRel patterns (some rest) .hashBag members found ∧
          BindingsValued found (lookupOrFvar chosen) ∧
          ∀ extended, BindingsExtends found extended →
            patterns.map (applyBindings extended) = patterns.map (applyBindings chosen) ∧
              applyBindings extended (.fvar rest) = bag arranged
  | [], members, remainder, _, perm => by
      refine ⟨members, by simpa using perm.symm, fun chosen _ restBound => ?_⟩
      refine ⟨[(rest, bag members)], .nilRest, ?_, fun extended extends_ => ⟨rfl, ?_⟩⟩
      · intro name value member
        simp only [List.mem_singleton, Prod.mk.injEq] at member
        obtain ⟨rfl, rfl⟩ := member
        exact restBound.symm
      · have found := extends_ rest (bag members) (by simp)
        simp [applyBindings, found]
  | first :: others, members, remainder, correct, perm => by
      simp only [List.map_cons, List.cons_append] at perm
      obtain ⟨index, bound, located⟩ := List.getElem_of_mem (perm.subset List.mem_cons_self)
      have tailPerm : (others.map (applyBindings bindings) ++ remainder).Perm (members.eraseIdx index) := by
        have split := perm.trans (List.getElem_cons_eraseIdx_perm bound).symm
        rw [located] at split
        exact split.cons_inv
      obtain ⟨arranged, arrangedPerm, complete⟩ := matchBag_complete_instance bindings rest others _ remainder
        (fun pattern member => correct pattern (List.mem_cons_of_mem _ member)) tailPerm
      refine ⟨arranged, arrangedPerm, fun chosen same restBound => ?_⟩
      simp only [List.map_cons] at same
      obtain ⟨sameFirst, sameOthers⟩ := List.cons.inj same
      obtain ⟨tailBindings, tailMatch, tailValued, tailCovers⟩ := complete chosen sameOthers restBound
      obtain ⟨headBindings, headMatched, headValued⟩ :=
        matchPattern_applyBindings_complete (bs := chosen) (correct first List.mem_cons_self)
      obtain ⟨found, merged, valued⟩ :=
        mergeBindings_some_of_valued headBindings tailBindings (lookupOrFvar chosen) headValued tailValued
      have headMatch : MatchRel first members[index] headBindings := by
        rw [located, ← sameFirst]
        exact matchPattern_sound headMatched
      refine ⟨found, .cons index bound headMatch tailMatch merged, valued, fun extended extends_ => ?_⟩
      obtain ⟨tailSame, restSame⟩ := tailCovers extended (extends_trans (extends_right merged) extends_)
      have head := matchRel_correct_of_extends headMatch (correct first List.mem_cons_self)
        (extends_trans (extends_left merged) extends_)
      refine ⟨?_, restSame⟩
      rw [List.map_cons, List.map_cons, head, located, tailSame, sameFirst]

/-- A right side with the same rest is its members beside what the rest is bound to. -/
theorem applyBindings_withRest {bindings : Bindings} {rest : String} {members remainder : List Pattern}
    (bound : applyBindings bindings (.fvar rest) = bag remainder) :
    applyBindings bindings (.collection .hashBag members (some rest)) =
      bag (members.map (applyBindings bindings) ++ remainder) := by
  cases found : bindings.find? (·.1 == rest) with
  | none => simp [applyBindings, found] at bound
  | some entry =>
      obtain ⟨name, value⟩ := entry
      simp [applyBindings, found] at bound
      subst bound
      simp [applyBindings, found]

/-! ## The compiler -/

/-- Why a language is not compiled by this lowering. -/
inductive Refusal where
  | staticEquations
  | premises (rule : String)
  | movedAcrossBinder (rule : String)
  | notBagRewrite (rule : String)
  | notFirstOrder (rule : String)
  | restInsideMember (rule : String)
  | unboundInResult (rule : String)
  deriving DecidableEq, Repr

/-- The rule that takes one list of rows and makes another. -/
def bagRule (taken made : List Tm) : SRule := ⟨PUnit.unit, ⟨taken, [], [], [], made⟩, []⟩

/-- The transform rule of one authored bag rewrite, or why it has none. -/
def lowerRule (rule : RewriteRule) : Except Refusal SRule :=
  if rule.premises.isEmpty then
    if ruleDepthAligned rule then
      match rule.left, rule.right with
      | .collection .hashBag takes (some rest), .collection .hashBag makes (some rest') =>
          if rest = rest' then
            match lowerEach? takes, lowerEach? makes with
            | some taken, some made =>
                if (takes.flatMap freeVars).contains rest then .error (.restInsideMember rule.name)
                else if (makes.flatMap freeVars).all (fun name => (takes.flatMap freeVars).contains name) then
                  .ok (bagRule taken made)
                else .error (.unboundInResult rule.name)
            | _, _ => .error (.notFirstOrder rule.name)
          else .error (.notBagRewrite rule.name)
      | _, _ => .error (.notBagRewrite rule.name)
    else .error (.movedAcrossBinder rule.name)
  else .error (.premises rule.name)

/-- The transform rules of authored rewrites, in their order. -/
def lowerRules : List RewriteRule → Except Refusal (List SRule)
  | [] => .ok []
  | rule :: rules =>
      match lowerRule rule with
      | .error reason => .error reason
      | .ok lowered =>
          match lowerRules rules with
          | .error reason => .error reason
          | .ok others => .ok (lowered :: others)

/-- **Compile an authored bag language to a transform program.** -/
def compile (language : LanguageDef) : Except Refusal (List SRule) :=
  if language.equations.isEmpty && !language.hasAlgebraDeclarations then lowerRules language.rewrites
  else .error .staticEquations

/-- What a transform rule keeps of the rewrite it comes from. -/
inductive Origin : RewriteRule → SRule → Prop where
  | intro {rule : RewriteRule} (takes makes : List Pattern) (rest : String) (taken made : List Tm)
      (premiseFree : rule.premises = []) (aligned : ruleDepthAligned rule = true)
      (left : rule.left = .collection .hashBag takes (some rest))
      (right : rule.right = .collection .hashBag makes (some rest))
      (restFresh : rest ∉ takes.flatMap freeVars)
      (takesLowered : lowerEach? takes = some taken) (makesLowered : lowerEach? makes = some made)
      (bound : ∀ name ∈ makes.flatMap freeVars, name ∈ takes.flatMap freeVars) :
      Origin rule (bagRule taken made)

theorem lowerRule_origin {rule : RewriteRule} {lowered : SRule} (compiled : lowerRule rule = .ok lowered) :
    Origin rule lowered := by
  unfold lowerRule at compiled
  split at compiled
  · rename_i premiseFree
    split at compiled
    · rename_i aligned
      split at compiled
      · rename_i takes rest makes rest' left right
        split at compiled
        · rename_i sameRest
          subst sameRest
          split at compiled
          · rename_i taken made takesLowered makesLowered
            split at compiled
            · cases compiled
            · rename_i fresh
              split at compiled
              · rename_i bound
                cases compiled
                exact .intro takes makes rest taken made (List.isEmpty_iff.mp premiseFree) aligned left right
                  (fun member => fresh (List.contains_iff_mem.mpr member)) takesLowered makesLowered
                  (fun name member => List.contains_iff_mem.mp (List.all_eq_true.mp bound name member))
              · cases compiled
          · cases compiled
        · cases compiled
      · cases compiled
    · cases compiled
  · cases compiled

theorem lowerRules_origins : ∀ {rules : List RewriteRule} {lowered : List SRule},
    lowerRules rules = .ok lowered → List.Forall₂ Origin rules lowered
  | [], _, compiled => by cases compiled; exact .nil
  | rule :: rules, _, compiled => by
      unfold lowerRules at compiled
      split at compiled
      · cases compiled
      · rename_i first firstLowered
        split at compiled
        · cases compiled
        · rename_i others othersLowered
          cases compiled
          exact .cons (lowerRule_origin firstLowered) (lowerRules_origins othersLowered)

/-- **Coverage.** Every authored rewrite has its rule, in order, and no other rule exists. -/
theorem compile_origins {language : LanguageDef} {program : List SRule}
    (compiled : compile language = .ok program) : List.Forall₂ Origin language.rewrites program := by
  unfold compile at compiled
  split at compiled
  · exact lowerRules_origins compiled
  · cases compiled

theorem exists_lowered {rules : List RewriteRule} {program : List SRule}
    (origins : List.Forall₂ Origin rules program) {rule : RewriteRule} (member : rule ∈ rules) :
    ∃ lowered ∈ program, Origin rule lowered := by
  induction origins with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨lowered, inside, origin⟩ := ih later
        exact ⟨lowered, List.mem_cons_of_mem _ inside, origin⟩

theorem exists_authored {rules : List RewriteRule} {program : List SRule}
    (origins : List.Forall₂ Origin rules program) {lowered : SRule} (member : lowered ∈ program) :
    ∃ rule ∈ rules, Origin rule lowered := by
  induction origins with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨rule, inside, origin⟩ := ih later
        exact ⟨rule, List.mem_cons_of_mem _ inside, origin⟩

theorem compile_plain {language : LanguageDef} {program : List SRule}
    (compiled : compile language = .ok program) : PlainRules language := fun _ member => by
  obtain ⟨_, _, origin⟩ := exists_lowered (compile_origins compiled) member
  cases origin with
  | intro _ _ _ _ _ premiseFree aligned => exact ⟨premiseFree, aligned⟩

theorem compile_fragment {language : LanguageDef} {program : List SRule}
    (compiled : compile language = .ok program) : ∀ rule ∈ program, RangeRestrictedPositive rule := by
  intro lowered member
  obtain ⟨_, _, origin⟩ := exists_authored (compile_origins compiled) member
  cases origin with
  | intro takes makes rest taken made _ _ _ _ _ takesLowered makesLowered bound =>
      refine ⟨rfl, rfl, fun term inWritten x vars => ?_⟩
      have inMade : term ∈ made := by simpa [written, bagRule] using inWritten
      have inUnknowns : x ∈ made.flatMap unknowns :=
        List.mem_flatMap.mpr ⟨term, inMade, mem_unknowns term vars⟩
      rw [unknowns_lowerEach makesLowered] at inUnknowns
      obtain ⟨name, nameMember, rfl⟩ := List.mem_map.mp inUnknowns
      have inTaken : labelCode name ∈ taken.flatMap unknowns := by
        rw [unknowns_lowerEach takesLowered]
        exact List.mem_map.mpr ⟨name, bound name nameMember, rfl⟩
      obtain ⟨term', termTaken, occurs⟩ := List.mem_flatMap.mp inTaken
      exact ⟨term', List.mem_append_left _ termTaken, vars_of_mem_unknowns term' occurs⟩

/-! ## Exactness -/

variable {relEnv : RelationEnv} {language : LanguageDef} {program : List SRule}

/-- The multiset of rows of a bag of members. -/
def rows (members : List Pattern) : Multiset Expr := (members.map encode : List Expr)

theorem exists_sources (list : List Expr) (image : ∀ row ∈ list, ∃ source, encode source = row) :
    ∃ sources : List Pattern, sources.map encode = list := by
  induction list with
  | nil => exact ⟨[], rfl⟩
  | cons row others ih =>
      obtain ⟨source, same⟩ := image row List.mem_cons_self
      obtain ⟨sources, sameOthers⟩ := ih fun row member => image row (List.mem_cons_of_mem _ member)
      exact ⟨source :: sources, by rw [List.map_cons, same, sameOthers]⟩

theorem perm_of_rows_eq {left right : List Pattern} (same : rows left = rows right) : left.Perm right :=
  Multiset.coe_eq_coe.mp (Multiset.map_injective encode_injective (by simpa [rows] using same))

/-- A source reduction of a bag is a rewrite of its rows, and its result is a bag. -/
theorem rewrites_of_step (compiled : compile language = .ok program) {members : List Pattern} {target : Pattern}
    (stepped : Step (engineBasePremises relEnv) language (bag members) target) :
    ∃ after, target = bag after ∧ Rewrites program (rows members) (rows after) := by
  obtain ⟨rule, member, bindings, matched, rfl⟩ := (step_iff_exists_match (compile_plain compiled)).mp stepped
  obtain ⟨lowered, loweredMember, origin⟩ := exists_lowered (compile_origins compiled) member
  cases origin with
  | intro takes makes rest taken made _ _ left right _ takesLowered makesLowered _ =>
      rw [left] at matched
      cases matchPattern_sound matched with
      | collection _ bagMatched =>
          obtain ⟨remainder, holds⟩ := matchBag_sound_instance (matchCorrect_of_lowerEach takesLowered) bagMatched
          obtain ⟨perm, restBound⟩ := holds bindings (extends_refl _)
          refine ⟨makes.map (applyBindings bindings) ++ remainder, by rw [right, applyBindings_withRest restBound], ?_⟩
          let θ : ℕ → Expr :=
            Function.extend labelCode (fun name => encode (applyBindings bindings (.fvar name))) (fun _ => .sym 0)
          have agree : ∀ name, θ (labelCode name) = encode (applyBindings bindings (.fvar name)) :=
            fun name => labelCode_injective.extend_apply _ _ name
          refine ⟨bagRule taken made, loweredMember, θ, rows remainder, ?_,
            fun q inside => absurd inside List.not_mem_nil, fun e inside => absurd inside List.not_mem_nil, ?_⟩
          · change ((taken.map (inst θ) : List Expr) : Multiset Expr) + rows remainder = rows members
            rw [inst_lowerEach θ bindings takesLowered (fun name _ => agree name), rows, rows, Multiset.coe_add,
              ← List.map_append]
            exact Multiset.coe_eq_coe.mpr (perm.map encode)
          · change rows _ = ((made.map (inst θ) : List Expr) : Multiset Expr) + rows remainder
            rw [inst_lowerEach θ bindings makesLowered (fun name _ => agree name), rows, rows, Multiset.coe_add,
              ← List.map_append]

/-- **A rewrite of the rows of a bag is a source reduction, in every arrangement**, and
its result is the rows of a bag. -/
theorem step_of_rewrites (compiled : compile language = .ok program) {members : List Pattern}
    {after : Multiset Expr} (rewrites : Rewrites program (rows members) after) :
    ∃ target, Step (engineBasePremises relEnv) language (bag members) (bag target) ∧ after = rows target := by
  obtain ⟨lowered, loweredMember, θ, restRows, split, -, -, madeIs⟩ := rewrites
  obtain ⟨rule, member, origin⟩ := exists_authored (compile_origins compiled) loweredMember
  cases origin with
  | intro takes makes rest taken made _ _ left right restFresh takesLowered makesLowered bound =>
      change ((taken.map (inst θ) : List Expr) : Multiset Expr) + restRows = rows members at split
      change after = ((made.map (inst θ) : List Expr) : Multiset Expr) + restRows at madeIs
      have rowPerm : (taken.map (inst θ) ++ restRows.toList).Perm (members.map encode) := by
        apply Multiset.coe_eq_coe.mp
        rw [← Multiset.coe_add, Multiset.coe_toList]
        exact split
      have image : ∀ row ∈ taken.map (inst θ) ++ restRows.toList, ∃ source, encode source = row := by
        intro row inside
        obtain ⟨source, _, same⟩ := List.mem_map.mp (rowPerm.subset inside)
        exact ⟨source, same⟩
      obtain ⟨selected, selectedIs⟩ :=
        exists_sources _ fun row inside => image row (List.mem_append_left _ inside)
      obtain ⟨others, othersIs⟩ :=
        exists_sources _ fun row inside => image row (List.mem_append_right _ inside)
      obtain ⟨bindings, agree⟩ :=
        exists_bindings θ (takes.flatMap freeVars) (capturesEach θ takesLowered selectedIs.symm)
      have takenIs := inst_lowerEach θ bindings takesLowered agree
      have selectedInstances : takes.map (applyBindings bindings) = selected :=
        List.map_injective_iff.mpr encode_injective (takenIs.symm.trans selectedIs.symm)
      have sourcePerm : (takes.map (applyBindings bindings) ++ others).Perm members := by
        apply perm_of_rows_eq
        apply Multiset.coe_eq_coe.mpr
        rw [List.map_append, ← takenIs, othersIs]
        exact rowPerm
      obtain ⟨arranged, arrangedPerm, complete⟩ := matchBag_complete_instance bindings rest takes members others
        (matchCorrect_of_lowerEach takesLowered) sourcePerm
      let chosen : Bindings := (rest, bag arranged) :: bindings
      have keeps : ∀ name, name ≠ rest → lookupOrFvar chosen name = lookupOrFvar bindings name := by
        intro name different
        simp [chosen, lookupOrFvar, applyBindings, Ne.symm different]
      have takesSame : takes.map (applyBindings chosen) = takes.map (applyBindings bindings) :=
        List.map_congr_left fun pattern inside =>
          applyBindings_eq_of_agree_isMatchCorrect (matchCorrect_of_lowerEach takesLowered pattern inside)
            fun name occurs => keeps name fun same =>
              restFresh (same ▸ List.mem_flatMap.mpr ⟨pattern, inside, occurs⟩)
      obtain ⟨found, matched, _, covers⟩ :=
        complete chosen takesSame (by simp [chosen, applyBindings])
      obtain ⟨foundTakes, foundRest⟩ := covers found (extends_refl _)
      have foundAgrees : ∀ name ∈ takes.flatMap freeVars, lookupOrFvar found name = lookupOrFvar bindings name := by
        intro name occurs
        obtain ⟨pattern, inside, inPattern⟩ := List.mem_flatMap.mp occurs
        exact applyBindings_injective_isMatchCorrect (matchCorrect_of_lowerEach takesLowered pattern inside)
          (List.map_inj_left.mp (foundTakes.trans takesSame) pattern inside) name inPattern
      have makesSame : makes.map (applyBindings found) = makes.map (applyBindings bindings) :=
        List.map_congr_left fun pattern inside =>
          applyBindings_eq_of_agree_isMatchCorrect (matchCorrect_of_lowerEach makesLowered pattern inside)
            fun name occurs => foundAgrees name (bound name (List.mem_flatMap.mpr ⟨pattern, inside, occurs⟩))
      refine ⟨makes.map (applyBindings bindings) ++ arranged, ?_, ?_⟩
      · refine (step_iff_exists_match (compile_plain compiled)).mpr ⟨rule, member, found, ?_, ?_⟩
        · rw [left]
          exact matchPattern_iff_matchRel.mpr (.collection (by decide) matched)
        · rw [right, applyBindings_withRest foundRest, makesSame]
      · rw [madeIs, inst_lowerEach θ bindings makesLowered (fun name occurs => agree name (bound name occurs)),
          ← Multiset.coe_toList restRows, ← othersIs, rows, Multiset.coe_add, ← List.map_append]
        exact Multiset.coe_eq_coe.mpr ((arrangedPerm.symm.append_left _).map encode)

/-! ## The authored reduction on bags -/

/-- **The authored reduction read on multisets of members**: some arrangement reduces,
by the language's own step, to some arrangement of the result. -/
def BagStep (relEnv : RelationEnv) (language : LanguageDef) (before after : Multiset Pattern) : Prop :=
  ∃ members members' : List Pattern, (members : Multiset Pattern) = before ∧ (members' : Multiset Pattern) = after ∧
    Step (engineBasePremises relEnv) language (bag members) (bag members')

theorem rewrites_of_bagStep (compiled : compile language = .ok program) {before after : Multiset Pattern}
    (stepped : BagStep relEnv language before after) :
    Rewrites program (before.map encode) (after.map encode) := by
  obtain ⟨members, members', rfl, rfl, stepped⟩ := stepped
  obtain ⟨result, same, rewrites⟩ := rewrites_of_step compiled stepped
  simp only [bag, Pattern.collection.injEq, true_and, and_true] at same
  subst same
  simpa [rows] using rewrites

theorem bagStep_of_rewrites (compiled : compile language = .ok program) {before : Multiset Pattern}
    {after : Multiset Expr} (rewrites : Rewrites program (before.map encode) after) :
    ∃ result, BagStep relEnv language before result ∧ after = result.map encode := by
  obtain ⟨members, rfl⟩ := Quot.exists_rep before
  obtain ⟨target, stepped, same⟩ := step_of_rewrites (relEnv := relEnv) compiled (members := members) rewrites
  exact ⟨(target : Multiset Pattern), ⟨members, target, rfl, rfl, stepped⟩, by simpa [rows] using same⟩

/-- **The reduction does not depend on how the bag is written.** -/
theorem bagStep_iff_arrangement (compiled : compile language = .ok program) (members : List Pattern)
    (after : Multiset Pattern) :
    BagStep relEnv language (members : Multiset Pattern) after ↔
      ∃ members' : List Pattern, (members' : Multiset Pattern) = after ∧
        Step (engineBasePremises relEnv) language (bag members) (bag members') := by
  constructor
  · intro stepped
    obtain ⟨target, targetStep, same⟩ :=
      step_of_rewrites (relEnv := relEnv) compiled (members := members) (after := after.map encode)
        (by simpa [rows] using rewrites_of_bagStep compiled stepped)
    exact ⟨target, Multiset.map_injective encode_injective (by simpa [rows] using same.symm), targetStep⟩
  · rintro ⟨members', same, stepped⟩
    exact ⟨members, members', rfl, same, stepped⟩

/-! ## On the step -/

/-- The authored language on bags of members. -/
def sourceSystem (relEnv : RelationEnv) (language : LanguageDef) : GSLT :=
  equalityGSLT (Multiset Pattern) (BagStep relEnv language)

/-- A bag of members is hosted by the bag of their rows. -/
def EncodedAs (source : Multiset Pattern) (hosted : Multiset Expr) : Prop := hosted = source.map encode

/-- The authored bag language and rewriting of its rows. -/
def encodedCorrespondence (relEnv : RelationEnv) (compiled : compile language = .ok program) :
    OperationalCorrespondence (sourceSystem relEnv language) (rewriting program) where
  related := EncodedAs
  readStep := by
    intro source hosted next same stepped
    have isImage : hosted = Multiset.map encode source := same
    subst isImage
    obtain ⟨result, sourceStep, nextIs⟩ := bagStep_of_rewrites (relEnv := relEnv) compiled stepped
    exact Or.inr ⟨result, sourceStep, nextIs⟩
  forward := by
    intro source target hosted same stepped
    have isImage : hosted = Multiset.map encode source := same
    subst isImage
    exact ⟨Multiset.map encode target, (executionPath_nonempty_iff_multiStep (rewriting program) _ _).mpr
      (.step (rewrites_of_bagStep compiled stepped) (.refl _)), rfl⟩

/-- **GSLT bag rewrites to transform.** An authored bag language and the step of its
compiled program, in both directions. -/
def stepCorrespondence {O : Type} [DecidableEq O] [Infinite O] (relEnv : RelationEnv)
    (compiled : compile language = .ok program) :
    OperationalCorrespondence (sourceSystem relEnv language) (stepSystem O program) :=
  (encodedCorrespondence relEnv compiled).comp (correspondence (compile_fragment compiled))

/-! ## The program as text -/

/-- One rule in tcalc notation: its takes and its makes. -/
def ruleText (index : Nat) (rule : SRule) : String :=
  let taken := rule.body.take.map fun term => " " ++ RootRewritesOnTheStep.termText term
  let made := rule.body.produce.map fun term => " " ++ RootRewritesOnTheStep.termText term
  s!"(rule r{index} (take{String.join taken}) (make{String.join made}))"

/-- **The compiled program, started at one bag**: the one-firing step, a row for each
member, and one rule per rewrite. -/
def programText (program : List SRule) (members : List Pattern) : String :=
  let present := members.map fun member => RootRewritesOnTheStep.rowText (encode member)
  let rules := program.zipIdx.map fun (rule, index) => ruleText index rule
  "\n".intercalate (["(step one)"] ++ present ++ rules) ++ "\n"

/-! ## Controls -/

namespace Controls

/-- A token. -/
def token : Pattern := .apply "Token" []
/-- The first winner. -/
def leftWon : Pattern := .apply "Left" []
/-- The second winner. -/
def rightWon : Pattern := .apply "Right" []

/-- A bag rewrite between ground members. -/
def rewrite (name : String) (takes makes : List Pattern) : RewriteRule where
  name := name
  typeContext := []
  premises := []
  left := .collection .hashBag takes (some "rest")
  right := .collection .hashBag makes (some "rest")

/-- A language of those rewrites. -/
def languageOf (rewrites : List RewriteRule) : LanguageDef where
  name := "Tokens"
  types := ["Member"]
  terms := [token, leftWon, rightWon].filterMap fun
    | .apply label _ => some { label := label, category := "Member", params := [], syntaxPattern := [] }
    | _ => none
  equations := []
  rewrites := rewrites

/-- One token becomes `Left`. -/
def spend : LanguageDef := languageOf [rewrite "spend" [token] [leftWon]]
/-- Two rules take the one token. -/
def race : LanguageDef := languageOf [rewrite "left" [token] [leftWon], rewrite "right" [token] [rightWon]]
/-- One rule takes two tokens. -/
def join : LanguageDef := languageOf [rewrite "join" [token, token] [leftWon]]

theorem spend_compiles : ∃ program, compile spend = .ok program := by
  simp [compile, spend, languageOf, rewrite, token, leftWon, rightWon, LanguageDef.hasAlgebraDeclarations, lowerRules,
    lowerRule, lowerEach?, lower?, RootRewritesOnTheStep.lowerList?, freeVars, ruleDepthAligned, depthAligned,
    depthAlignedList, captureDepth, captureDepthList]

theorem race_compiles : ∃ program, compile race = .ok program := by
  simp [compile, race, languageOf, rewrite, token, leftWon, rightWon, LanguageDef.hasAlgebraDeclarations, lowerRules,
    lowerRule, lowerEach?, lower?, RootRewritesOnTheStep.lowerList?, freeVars, ruleDepthAligned, depthAligned,
    depthAlignedList, captureDepth, captureDepthList]

theorem join_compiles : ∃ program, compile join = .ok program := by
  simp [compile, join, languageOf, rewrite, token, leftWon, rightWon, LanguageDef.hasAlgebraDeclarations, lowerRules,
    lowerRule, lowerEach?, lower?, RootRewritesOnTheStep.lowerList?, freeVars, ruleDepthAligned, depthAligned,
    depthAlignedList, captureDepth, captureDepthList]

/-- The engine's successors, one for each match. -/
def successors (language : LanguageDef) (source : Pattern) : List Pattern :=
  language.rewrites.flatMap fun rule =>
    (matchPattern rule.left source).map fun bindings => applyBindings bindings rule.right

theorem step_iff_successor (compiled : compile language = .ok program) (source target : Pattern) :
    Step (engineBasePremises relEnv) language source target ↔ target ∈ successors language source := by
  rw [step_iff_exists_match (compile_plain compiled)]
  simp [successors, List.mem_flatMap, List.mem_map]

/-- **Equal occurrences: two matches, one successor value.** The observer keeps the
one value, and not the two matches. -/
theorem equal_occurrences (target : Pattern) :
    successors spend (bag [token, token]) = [bag [leftWon, token], bag [leftWon, token]] ∧
      (Step (engineBasePremises relEnv) spend (bag [token, token]) target ↔ target = bag [leftWon, token]) := by
  have two : successors spend (bag [token, token]) = [bag [leftWon, token], bag [leftWon, token]] := by
    decide +kernel
  obtain ⟨program, compiled⟩ := spend_compiles
  exact ⟨two, by rw [step_iff_successor compiled, two]; simp⟩

/-- **Overlapping takes: either rule, never both.** The first rule has no priority. -/
theorem race_steps (target : Pattern) :
    Step (engineBasePremises relEnv) race (bag [token]) target ↔
      target = bag [leftWon] ∨ target = bag [rightWon] := by
  have two : successors race (bag [token]) = [bag [leftWon], bag [rightWon]] := by decide +kernel
  obtain ⟨program, compiled⟩ := race_compiles
  rw [step_iff_successor compiled, two]
  simp

/-- **The two takes cannot both commit on the transform step.** Every admitted firing
at one token leaves `Left` alone or `Right` alone. -/
theorem race_firing_exclusive {O : Type} [DecidableEq O] [Infinite O] {program : List SRule}
    (compiled : compile race = .ok program) {s : SState O} (reads : ReadsBag s (rows [token]))
    (g : Firing O E {r | r ∈ program} s.frame) (admitted : (schematicStep O program).Admits (s := s) g) :
    ReadsBag ((schematicStep O program).result g admitted) (rows [leftWon]) ∨
      ReadsBag ((schematicStep O program).result g admitted) (rows [rightWon]) := by
  obtain ⟨after, rewrites, resultReads⟩ := readsBag_backward (compile_fragment compiled) reads g admitted
  obtain ⟨target, stepped, same⟩ := step_of_rewrites (relEnv := RelationEnv.empty) compiled rewrites
  subst same
  rcases (race_steps (bag target)).mp stepped with isLeft | isRight
  · left
    simp only [bag, Pattern.collection.injEq, true_and, and_true] at isLeft
    subst isLeft
    exact resultReads
  · right
    simp only [bag, Pattern.collection.injEq, true_and, and_true] at isRight
    subst isRight
    exact resultReads

/-- **One occurrence cannot fill two takes**, and two equal occurrences can. -/
theorem join_needs_two (target : Pattern) :
    ¬ Step (engineBasePremises relEnv) join (bag [token]) target ∧
      (Step (engineBasePremises relEnv) join (bag [token, token]) target ↔ target = bag [leftWon]) := by
  have none_ : successors join (bag [token]) = [] := by decide +kernel
  have both : successors join (bag [token, token]) = [bag [leftWon], bag [leftWon]] := by decide +kernel
  obtain ⟨program, compiled⟩ := join_compiles
  exact ⟨by rw [step_iff_successor compiled, none_]; simp, by rw [step_iff_successor compiled, both]; simp⟩

/-- A rest that is also a variable of a member is refused: the matcher would equate a
member with the whole frame, which a frame of the step cannot say. -/
theorem rest_inside_member_refused :
    compile (languageOf [rewrite "self" [.fvar "rest"] [token]]) = .error (.restInsideMember "self") := by
  simp [compile, languageOf, rewrite, token, leftWon, rightWon, LanguageDef.hasAlgebraDeclarations, lowerRules,
    lowerRule, lowerEach?, lower?, RootRewritesOnTheStep.lowerList?, freeVars, ruleDepthAligned, depthAligned,
    depthAlignedList, captureDepth, captureDepthList]

end Controls

#print axioms compile_origins
#print axioms bagStep_iff_arrangement
#print axioms stepCorrespondence
#print axioms Controls.equal_occurrences
#print axioms Controls.race_firing_exclusive
#print axioms Controls.join_needs_two
#print axioms Controls.rest_inside_member_refused

end Mettapedia.GSLT.Compilation.BagRewritesOnTheStep
