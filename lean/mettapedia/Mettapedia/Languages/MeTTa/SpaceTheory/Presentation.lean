import Mettapedia.Languages.MeTTa.SpaceTheory.Atoms
import Mettapedia.GSLT.LanguageDef.RootRewriting
import Mettapedia.Languages.MeTTa.SpaceTheory.ConstructorSyntax
import Mettapedia.Languages.MeTTa.SpaceTheory.Assignments
import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.Languages.MeTTa.HE.Spec.Type
import Mettapedia.Languages.MeTTa.PeTTa.Effects
import Mettapedia.GSLT.LanguageDef.LiveModuleEdits
import Mettapedia.GSLT.Equations.Preference
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTa
import Mettapedia.Data.List.OptionMapMReflection

/-!
# Reading a live MeTTa space at a snapshot

A declaration view does not remove declarations from raw matching. HE
and PeTTa need not use the same atoms from that view. In the constructor
vocabulary, function definitions can be open and non-linear. Type
assignments contribute to the static judgment in the same snapshot.
Ready-root rewriting does not itself specify either dialect's evaluation
strategy, type checking of calls, or effects.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.Presentation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.MeTTaIL.Syntax (LanguageDef Pattern RewriteRule Equation TypeExpr)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator PremisesAt)
open Mettapedia.OSLF.MeTTaIL.Match (applyBindings binderFree matchPattern ruleDepthAligned_of_binderFree)
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
open Atoms (Occurrence annotate ofKind ofKind_annotate classify content Content)
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.LiveModuleEdits (Order)
open Mettapedia.GSLT.LanguageDef.DecidableRelations (FirstOrder isFirstOrder_iff)
open Mettapedia.GSLT.LanguageDef.RootRewriting
open ConstructorSyntax (Variables term? terms? ground_term binderFree_term)
open Mettapedia.GSLT.Contracts.ScopedAliasDispatch (moduloRead)

private theorem kind_definition (a : Atom) :
    (classify a).kind = .definition ↔ HE.Space.isEquation a = true := by
  rw [Atoms.definitionKind_iff]
  constructor
  · rintro ⟨lhs, rhs, rfl⟩; rfl
  · unfold HE.Space.isEquation
    split
    · exact fun _ => ⟨_, _, rfl⟩
    · simp

private theorem kind_typed (a : Atom) :
    (classify a).kind = .typed ↔ HE.Space.isTypeAnnotation a = true := by
  rw [Atoms.assignmentKind_iff]
  constructor
  · rintro ⟨subject, type, rfl⟩; rfl
  · unfold HE.Space.isTypeAnnotation
    split
    · exact fun _ => ⟨_, _, rfl⟩
    · simp

/-- HE's existing readers agree with exactly the respective projections,
as lists, including repeated declarations in the raw space. -/
theorem he_readers (s : HE.Space) :
    (ofKind .definition (annotate classify s.atoms)).map Occurrence.atom =
      s.atoms.filter HE.Space.isEquation ∧
    (ofKind .typed (annotate classify s.atoms)).map Occurrence.atom =
      s.atoms.filter HE.Space.isTypeAnnotation := by
  rw [ofKind_annotate, ofKind_annotate]
  exact ⟨List.filter_congr (fun a _ => Bool.eq_iff_iff.mpr
      (by simpa only [decide_eq_true_eq] using kind_definition a)),
    List.filter_congr (fun a _ => Bool.eq_iff_iff.mpr
      (by simpa only [decide_eq_true_eq] using kind_typed a))⟩

/-- Written assignments are exactly the declarations in HE's independent
annotation judgment. The judgement neither invents an intrinsic type nor
uses the undefined-type fallback as an assignment. -/
theorem he_has_written_assignment {atoms types : List Atom} {subject type : Atom}
    (lookup : HE.Spec.Type.AnnotationTypesRel subject atoms types) :
    Assignments.TypeAssignment atoms subject type ↔ type ∈ types := by
  induction lookup with
  | nil => simp [Assignments.TypeAssignment]
  | @hit first tail rest next ih =>
    have headEq : (Content.assignment subject type).syntax =
        .expression [.symbol ":", subject, first] ↔ type = first := by
      simp [Content.syntax]
    simpa only [Assignments.TypeAssignment, Multiset.mem_coe, List.mem_cons, headEq] using
      (or_congr Iff.rfl ih)
  | @skip first tail rest missing next ih =>
    have different := Ne.symm (missing type)
    simpa [Assignments.TypeAssignment, Content.syntax, different] using ih

open PeTTa.SpaceSemantics (Indexes Program index)
open PeTTaPresentation (readEquation readEquation_shape)

private theorem definition_decode_kept (atoms : List Atom) :
    (atoms.filter HE.Space.isEquation).filterMap readEquation = atoms.filterMap readEquation := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
    cases eq : HE.Space.isEquation atom with
    | true =>
      simp only [List.filter_cons, eq, if_true, List.filterMap_cons, ih]
    | false =>
      have no : readEquation atom = none := by
        rw [readEquation_shape]
        split
        · cases eq
        · rfl
      simp [eq, ih, no]

private theorem indexed_views {atoms : List Atom} {p : Program} (indexed : Indexes atoms p) :
    atoms.filterMap readEquation = p.equations ∧
      atoms.filter HE.Space.isTypeAnnotation = p.declarations := by
  induction indexed with
  | nil => exact ⟨rfl, rfl⟩
  | equation head args body tail ih => simp [HE.Space.isTypeAnnotation, ih.1, ih.2]
  | declaration subject ty tail ih =>
    simp [List.filterMap_cons, HE.Space.isTypeAnnotation, ih.1, ih.2]
  | fact atom notRule notType tail ih =>
    have no : readEquation atom = none := by
      rw [readEquation_shape]
      split
      · exact (notRule _ _ _ rfl).elim
      · rfl
    have noType : HE.Space.isTypeAnnotation atom = false := by
      unfold HE.Space.isTypeAnnotation
      split
      · exact (notType _ _ rfl).elim
      · rfl
    simp [no, noType, ih.1, ih.2]

/-- PeTTa still selects just its own usable named `=` atoms. Classifying
an atom as a function definition does not make it a PeTTa call. -/
theorem petta_readers (atoms : List Atom) :
    ((ofKind .definition (annotate classify atoms)).map Occurrence.atom).filterMap readEquation =
      (index atoms).equations ∧
    (ofKind .typed (annotate classify atoms)).map Occurrence.atom = (index atoms).declarations := by
  obtain ⟨rules, types⟩ := indexed_views (PeTTa.SpaceSemantics.index_exact atoms)
  have keep := he_readers (HE.Space.ofList atoms)
  exact ⟨(congrArg (List.filterMap readEquation) keep.1).trans
    ((definition_decode_kept atoms).trans rules), keep.2.trans types⟩

/-! ## A presentation, not a second interpreter -/

structure WrittenEquation where
  preference : Atoms.Preference
  anchor : Pattern
  members : List Pattern

def WrittenEquation.terms (written : WrittenEquation) : List Pattern :=
  written.anchor :: written.members

def WrittenEquation.arrows (written : WrittenEquation) : List (Pattern × Pattern) :=
  match written.preference with
  | .indifferent => []
  | .rightward => Mettapedia.GSLT.Equations.Preference.consecutive written.terms
  | .leftward => Mettapedia.GSLT.Equations.Preference.consecutive written.terms.reverse

structure Contribution where
  rewrites : List RewriteRule := []
  equations : List Equation := []
  written : Option WrittenEquation := none

/-- Only (n-1) generators are needed to identify (n) terms. The spelling
directions control presentation, not the set of terms equated here. -/
def aliasEquations (anchor : Pattern) (members : List Pattern) : List Equation :=
  members.map fun t =>
    { name := "space alias", typeContext := [], premises := []
      left := anchor, right := t }

theorem aliasEquations_connect (base : BasePremiseEvaluator) (language : LanguageDef)
    (anchor : Pattern) (members : List Pattern) (groundAnchor : FirstOrder anchor)
    (groundMembers : ∀ t ∈ members, FirstOrder t)
    (authored : aliasEquations anchor members ⊆ language.equations)
    {x y : Pattern} (hx : x ∈ anchor :: members) (hy : y ∈ anchor :: members) :
    EquationEquiv base language x y := by
  have joined : ∀ t ∈ anchor :: members, EquationEquiv base language anchor t := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | member
    · exact Relation.EqvGen.refl _
    · let eqn : Equation :=
        { name := "space alias", typeContext := [], premises := []
          left := anchor, right := t }
      apply equationInstance_equivalent
      refine ⟨0, EquationInstanceAt.forward (equation := eqn) (initialBindings := [])
        (finalBindings := []) (authored (List.mem_map.mpr ⟨t, member, rfl⟩))
        (readsRaw_of_none rfl) ?_ (.nil []) ?_⟩
      · change [] ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern anchor anchor
        simp [(ground_match groundAnchor).2.2]
      · exact (ground_match (groundMembers t member)).2.1 []
  let e := equationSetoid base language
  exact e.iseqv.trans (e.iseqv.symm (joined x hx)) (joined y hy)

/-- Interpret declarations in a supplied term grammar. Type and subtype
assignments are interpreted by the static judgment on the same atoms,
not as directed rewrites of types. -/
def contributionUsing (definitionTerm equalityTerm : Atom → Option Pattern)
    (equalityTerms : List Atom → Option (List Pattern))
    (definitionContext : Atom → Atom → List (String × TypeExpr) := fun _ _ => []) :
    Content → Option Contribution
  | .data _ | .assignment _ _ | .subtype _ _ => some {}
  | .definition left right => do
    let l ← definitionTerm left
    let t ← definitionTerm right
    let rule : RewriteRule :=
      { name := "space definition", typeContext := definitionContext left right, premises := []
        left := l, right := t }
    return { rewrites := [rule] }
  | .equation pref first next tail => do
    let anchor ← equalityTerm first
    let members ← equalityTerms (next :: tail)
    return { equations := aliasEquations anchor members, written := some ⟨pref, anchor, members⟩ }
  | .directed _ _ => none

def contribution? (vars : Variables) : Content → Option Contribution :=
  contributionUsing (term? vars) (term? .literal) (terms? .literal)

def projections? (atoms : List Atom) (vars : Variables := .literal) : Option (List Contribution) :=
  (atoms.map content).mapM (contribution? vars)

def assemble (order : Order) (core : LanguageDef) (parts : List Contribution) : LanguageDef :=
  let stored := parts.flatMap Contribution.rewrites
  { core with
    rewrites := match order with
      | .front => stored ++ core.rewrites
      | .back => core.rewrites ++ stored
    equations := core.equations ++ parts.flatMap Contribution.equations }

def present? (order : Order) (core : LanguageDef) (atoms : List Atom)
    (vars : Variables := .literal) : Option LanguageDef :=
  (projections? atoms vars).map (assemble order core)

theorem contribution_rule_origin
    {definitionTerm equalityTerm : Atom → Option Pattern}
    {equalityTerms : List Atom → Option (List Pattern)}
    {definitionContext : Atom → Atom → List (String × TypeExpr)}
    {atom : Content} {part : Contribution} {rule : RewriteRule}
    (compiled : contributionUsing definitionTerm equalityTerm equalityTerms definitionContext atom = some part)
    (member : rule ∈ part.rewrites) :
    ∃ lhs rhs, atom = .definition lhs rhs ∧ definitionTerm lhs = some rule.left ∧
      definitionTerm rhs = some rule.right ∧ rule.premises = [] ∧
      rule.typeContext = definitionContext lhs rhs := by
  cases atom with
  | definition lhs rhs =>
    obtain ⟨l, left, rest⟩ := Option.bind_eq_some_iff.mp compiled
    obtain ⟨r, right, output⟩ := Option.bind_eq_some_iff.mp rest
    cases output
    obtain rfl := List.mem_singleton.mp member
    exact ⟨lhs, rhs, rfl, left, right, rfl, rfl⟩
  | equation pref first second rest =>
    obtain ⟨_, _, readRest⟩ := Option.bind_eq_some_iff.mp compiled
    obtain ⟨_, _, output⟩ := Option.bind_eq_some_iff.mp readRest
    cases output
    cases member
  | data | assignment | subtype =>
    cases compiled
    cases member
  | directed => cases compiled

private theorem contribution_rewrite
    {vars : Variables} {atom : Content} {part : Contribution} {rule : RewriteRule}
    (compiled : contribution? vars atom = some part) (member : rule ∈ part.rewrites) :
    ∃ lhs rhs, atom = .definition lhs rhs ∧ term? vars lhs = some rule.left ∧
      term? vars rhs = some rule.right ∧ rule.premises = [] :=
  by
    obtain ⟨l, r, shape, left, right, free, _⟩ :=
      contribution_rule_origin (definitionTerm := term? vars) compiled member
    exact ⟨l, r, shape, left, right, free⟩

private theorem contribution_literal {atom : Content} {p : Contribution}
    (loaded : contribution? .literal atom = some p) :
    ∀ rule ∈ p.rewrites, rule.premises = [] ∧ FirstOrder rule.left ∧ FirstOrder rule.right := by
  intro rule member
  obtain ⟨lhs, rhs, _, left, right, noPremise⟩ := contribution_rewrite loaded member
  exact ⟨noPremise, ground_term lhs left, ground_term rhs right⟩

/-- The ground property is supplied by a successful read, not by a
second test over the materialized rules. Only the fixed base needs its
own separate proof. -/
theorem present_literal (order : Order) (core : LanguageDef) (groundBase : LiteralRoots core)
    (atoms : List Atom) {language : LanguageDef} (loaded : present? order core atoms = some language) :
    LiteralRoots language := by
  obtain ⟨parts, readParts, rfl⟩ := Option.map_eq_some_iff.mp loaded
  have stored : ∀ r ∈ parts.flatMap Contribution.rewrites,
      r.premises = [] ∧ FirstOrder r.left ∧ FirstOrder r.right := by
    intro rule member
    obtain ⟨part, found, used⟩ := List.mem_flatMap.mp member
    obtain ⟨_, _, arrives⟩ := Mettapedia.Data.List.option_mapM_origin
      (contribution? .literal) (atoms.map content) parts readParts part found
    exact contribution_literal arrives rule used
  intro r member
  cases order
  · rcases List.mem_append.mp member with fromStore | fromBase
    · exact stored r fromStore
    · exact groundBase r fromBase
  · rcases List.mem_append.mp member with fromBase | fromStore
    · exact groundBase r fromBase
    · exact stored r fromStore

theorem assemble_aligned (order : Order) (core : LanguageDef)
    (baseAligned : isUnconditionalAligned core = true)
    {definitionTerm equalityTerm : Atom → Option Pattern}
    {equalityTerms : List Atom → Option (List Pattern)}
    {definitionContext : Atom → Atom → List (String × TypeExpr)}
    (aligned : ∀ a p, definitionTerm a = some p → binderFree p = true)
    (atoms : List Atom) {parts : List Contribution}
    (readParts : (atoms.map content).mapM
      (contributionUsing definitionTerm equalityTerm equalityTerms definitionContext) =
      some parts) :
    isUnconditionalAligned (assemble order core parts) = true := by
  have stored : (parts.flatMap Contribution.rewrites).all
      (fun r => r.premises.isEmpty && Mettapedia.OSLF.MeTTaIL.Match.ruleDepthAligned r) = true := by
    apply List.all_eq_true.mpr
    intro rule member
    obtain ⟨part, found, used⟩ := List.mem_flatMap.mp member
    obtain ⟨_, _, computed⟩ := Mettapedia.Data.List.option_mapM_origin
      (contributionUsing definitionTerm equalityTerm equalityTerms definitionContext)
      (atoms.map content) parts readParts part found
    obtain ⟨lhs, rhs, _, left, right, noPremises, _⟩ := contribution_rule_origin computed used
    simp [noPremises, ruleDepthAligned_of_binderFree rule
      (aligned lhs rule.left left) (aligned rhs rule.right right)]
  unfold isUnconditionalAligned at baseAligned
  cases order <;> simp [isUnconditionalAligned, assemble, List.all_append, stored, baseAligned]

/-- The same presentation construction admits metavariables without
introducing binder shifts or changing how equations are generated. -/
theorem present_aligned (order : Order) (core : LanguageDef)
    (baseAligned : isUnconditionalAligned core = true)
    (atoms : List Atom) (vars : Variables) {language : LanguageDef}
    (loaded : present? order core atoms vars = some language) :
    isUnconditionalAligned language = true := by
  obtain ⟨_, readParts, rfl⟩ := Option.map_eq_some_iff.mp loaded
  exact assemble_aligned order core baseAligned (definitionTerm := term? vars)
    (fun a _ h => binderFree_term vars a h) atoms readParts

/-- A space interprets the same atoms by two kinds of judgment:
root rewriting modulo equations and the types the assignments derive.
Raw inspection sees all the atoms, including the written declarations. -/
structure PresentedSpace where
  atoms : List Atom
  language : LanguageDef

def present (order : Order) (core : LanguageDef) (atoms : List Atom) :
    Option PresentedSpace :=
  (present? order core atoms .schematic).map fun language => ⟨atoms, language⟩

def PresentedSpace.theory (space : PresentedSpace) (base : BasePremiseEvaluator) :=
  gsltModuloEquations base space.language

def PresentedSpace.HasType (space : PresentedSpace) (baseType baseSubtype : Atom → Atom → Prop)
    (term type : Atom) : Prop :=
  Assignments.HasType baseType baseSubtype space.atoms term type

theorem core_definitions_included (order : Order) (core : LanguageDef) (atoms : List Atom)
    {space : PresentedSpace} (loaded : present order core atoms = some space) :
    core.rewrites ⊆ space.language.rewrites := by
  obtain ⟨language, built, rfl⟩ := Option.map_eq_some_iff.mp loaded
  obtain ⟨parts, _, rfl⟩ := Option.map_eq_some_iff.mp built
  intro rule member
  cases order
  · exact List.mem_append_right _ member
  · exact List.mem_append_left _ member

/-- Every positive base root rewrite remains a rewrite in the extension.
This does not claim that a new definition preserves bisimilarity, or that
it preserves an answer that depended on *no* definition applying. -/
theorem positive_base_step_preserved (order : Order) (core : LanguageDef) (atoms : List Atom)
    {space : PresentedSpace} (loaded : present order core atoms = some space)
    (baseAligned : isUnconditionalAligned core = true) (base : BasePremiseEvaluator)
    {input output : Pattern} (fired : Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base core input output) :
    (space.theory base).Step input output := by
  have found := (step_iff_mem_rootReducts base core baseAligned _ _).mp fired
  obtain ⟨rule, authored, reduced⟩ := List.mem_flatMap.mp found
  obtain ⟨language, compiled, eq⟩ := Option.map_eq_some_iff.mp loaded
  have aligned : isUnconditionalAligned space.language = true := by
    rw [← eq]
    exact present_aligned order core baseAligned atoms .schematic compiled
  apply step_to_stepModuloEquations
  exact (step_iff_mem_rootReducts base _ aligned _ _).mpr
    (List.mem_flatMap.mpr ⟨rule, core_definitions_included order core atoms loaded authored, reduced⟩)

theorem presented_step_iff (order : Order) (core : LanguageDef) (atoms : List Atom)
    {space : PresentedSpace} (loaded : present order core atoms = some space)
    (baseAligned : isUnconditionalAligned core = true) (base : BasePremiseEvaluator)
    (input output : Pattern) :
    (space.theory base).Step input output ↔
      ∃ rule ∈ space.language.rewrites, ∃ representative σ,
        EquationEquiv base space.language input representative ∧
        σ ∈ matchPattern rule.left representative ∧
        EquationEquiv base space.language (applyBindings σ rule.right) output := by
  obtain ⟨language, compiled, rfl⟩ := Option.map_eq_some_iff.mp loaded
  exact root_instantiation_iff base language (present_aligned order core baseAligned atoms
    .schematic compiled) input output

theorem projections_cons (atom : Atom) (atoms : List Atom) {p ps}
    (head : contribution? .literal (content atom) = some p) (tail : projections? atoms = some ps) :
    projections? (atom :: atoms) = some (p :: ps) := by
  unfold projections? at tail ⊢
  rw [List.map_cons]
  exact Mettapedia.Data.List.option_mapM_cons_of_some (contribution? .literal) head tail

theorem projections_snoc (atoms : List Atom) (atom : Atom) {ps p}
    (past : projections? atoms = some ps) (added : contribution? .literal (content atom) = some p) :
    projections? (atoms ++ [atom]) = some (ps ++ [p]) := by
  unfold projections? at past ⊢
  rw [List.map_append, List.mapM_append]
  change (do
    let old ← (atoms.map content).mapM (contribution? .literal)
    let new ← [content atom].mapM (contribution? .literal)
    pure (old ++ new)) = some (ps ++ [p])
  simp [past, added]

/-- Retraction never makes a well-presented sequence of atoms ill formed.
Each surviving declaration still contributes exactly its own meaning.
This theorem is about choosing occurrences, not a removal algorithm. -/
theorem projections_sublist {before after : List Atom} (kept : after.Sublist before)
    (vars : Variables) {parts : List Contribution}
    (prior : projections? before vars = some parts) :
    ∃ remaining, projections? after vars = some remaining ∧ remaining.Sublist parts := by
  induction kept generalizing parts with
  | slnil =>
    cases prior
    exact ⟨[], rfl, .slnil⟩
  | @cons after before atom _ ih =>
    unfold projections? at prior
    rw [List.map_cons, List.mapM_cons] at prior
    obtain ⟨part, _, tail⟩ := Option.bind_eq_some_iff.mp prior
    obtain ⟨rest, clean, output⟩ := Option.bind_eq_some_iff.mp tail
    cases output
    obtain ⟨remaining, found, included⟩ := ih clean
    exact ⟨remaining, found, .cons part included⟩
  | @cons_cons after before atom _ ih =>
    unfold projections? at prior
    rw [List.map_cons, List.mapM_cons] at prior
    obtain ⟨part, head, tail⟩ := Option.bind_eq_some_iff.mp prior
    obtain ⟨rest, clean, output⟩ := Option.bind_eq_some_iff.mp tail
    cases output
    obtain ⟨remaining, found, included⟩ := ih clean
    refine ⟨part :: remaining, ?_, .cons_cons part included⟩
    unfold projections?
    rw [List.map_cons]
    exact Mettapedia.Data.List.option_mapM_cons_of_some _ head found

theorem present_after_retraction (order : Order) (core : LanguageDef)
    {before after : List Atom} (kept : after.Sublist before)
    {space : PresentedSpace} (prior : present order core before = some space) :
    ∃ remaining, present order core after = some remaining ∧
      remaining.language.rewrites.Sublist space.language.rewrites ∧
      remaining.language.equations.Sublist space.language.equations := by
  obtain ⟨language, built, rfl⟩ := Option.map_eq_some_iff.mp prior
  obtain ⟨parts, read, rfl⟩ := Option.map_eq_some_iff.mp built
  obtain ⟨remaining, extracted, subset⟩ := projections_sublist kept .schematic read
  have definitions := subset.flatMap Contribution.rewrites
  have equations := subset.flatMap Contribution.equations
  refine ⟨⟨after, assemble order core remaining⟩, by simp [present, present?, extracted],
    ?_, List.Sublist.append (List.Sublist.refl _) equations⟩
  cases order
  · exact List.Sublist.append definitions (List.Sublist.refl _)
  · exact List.Sublist.append (List.Sublist.refl _) definitions

/-- Data changes the raw occurrence store but not this rule-and-equation
presentation. A cache of *answers that read data* still needs its own
data protection; it cannot use this compilation fact as justification. -/
theorem data_insertion_leaves_theory (core : LanguageDef) (atoms : List Atom) (atom : Atom)
    {ps} (loaded : projections? atoms = some ps) (ordinary : (classify atom).kind = .data) :
    present? .front core (atom :: atoms) = present? .front core atoms ∧
      present? .back core (atoms ++ [atom]) = present? .back core atoms := by
  have added : contribution? .literal (content atom) = some {} := by
    cases h : content atom <;> simp [Atoms.classify, h, Content.tag] at ordinary
    simp [contribution?, contributionUsing]
  constructor
  · rw [present?, projections_cons atom atoms added loaded, present?, loaded]
    rfl
  · rw [present?, projections_snoc atoms atom loaded added, present?, loaded]
    simp [assemble, List.flatMap_append]

noncomputable def candidates? (base : BasePremiseEvaluator) (order : Order) (core : LanguageDef)
    (atoms : List Atom) (q : Pattern) : Option (List RewriteRule) :=
  (present? order core atoms).map fun l => moduloRead base l RewriteRule.left q l.rewrites

/-- Selected ground-root dispatch, reading from raw atoms. A declined
language view is not evidence of no source behavior. -/
theorem at_snapshot (base : BasePremiseEvaluator) (order : Order) (core : LanguageDef)
    (atoms : List Atom) {l : LanguageDef} (view : present? order core atoms = some l)
    (literal : LiteralRoots l) (q y : Pattern) :
    (∃ picked, candidates? base order core atoms q = some picked ∧
      ∃ r ∈ picked, EquationEquiv base l r.right y) ↔ StepModuloEquations base l q y := by
  rw [candidates?, view, Option.map_some, literal_root_iff base l literal]
  exact ⟨fun ⟨_, same, r, member, result⟩ => by
    cases same
    exact ⟨r, member, result⟩, fun found => ⟨_, rfl, found⟩⟩

theorem he_after_add (base : BasePremiseEvaluator) (core : LanguageDef) (s : HE.Space)
    (a : Atom) {ps p} (view : projections? s.atoms = some ps)
    (added : contribution? .literal (content a) = some p)
    (ready : LiteralRoots (assemble .front core (p :: ps))) (q y : Pattern) :
    (∃ picked, candidates? base .front core (s.add a).atoms q = some picked ∧
      ∃ r ∈ picked, EquationEquiv base (assemble .front core (p :: ps)) r.right y) ↔
      StepModuloEquations base (assemble .front core (p :: ps)) q y :=
  at_snapshot base .front core _
    (by simp [HE.Space.add, present?, projections_cons a s.atoms added view]) ready q y

theorem petta_after_insert (base : BasePremiseEvaluator) (core : LanguageDef)
    (s after : PeTTa.Effects.State) (h : PeTTa.NamedSpaces.Handle) (a : Atom) (atoms : List Atom)
    (reads : s.read h = some atoms) (inserted : PeTTa.Effects.insert s h a = some after)
    {ps p} (view : projections? atoms = some ps) (added : contribution? .literal (content a) = some p)
    (ready : LiteralRoots (assemble .back core (ps ++ [p]))) (q y : Pattern) :
    (∃ picked,
      (after.read h).bind (fun rs => candidates? base .back core rs q) = some picked ∧
      ∃ r ∈ picked, EquationEquiv base (assemble .back core (ps ++ [p])) r.right y) ↔
      StepModuloEquations base (assemble .back core (ps ++ [p])) q y := by
  obtain ⟨old, before, afterRead⟩ := PeTTa.Effects.insert_reads_back inserted
  have same := Option.some.inj (before.symm.trans reads)
  subst old
  rw [afterRead, Option.bind_some]
  exact at_snapshot base .back core _ (by simp [present?, projections_snoc atoms a view added]) ready q y

section Examples

open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)

private def atomCall (h : String) (a : Atom) : Atom := .expression [.symbol h, a]
private def a : Atom := .symbol "A"
private def q : Pattern := .apply "Inspect" [.apply "A" []]
private def ok : Pattern := .apply "OK" []
private def sourceRule : Atom :=
  .expression [.symbol "=", atomCall "Inspect" (atomCall "Next" a), .symbol "OK"]
private def cycle : Atom := .expression [.symbol "=e", a, atomCall "Next" a]
private def core : LanguageDef := .empty "space-presentation"
private def raw : HE.Space := .ofList [sourceRule]
private def rewrite : RewriteRule :=
  { name := "space definition", typeContext := [], premises := [],
    left := .apply "Inspect" [.apply "Next" [.apply "A" []]], right := ok }
private def equality : Equation :=
  { name := "space alias", typeContext := [], premises := [],
    left := .apply "A" [], right := .apply "Next" [.apply "A" []] }
private def earlier : LanguageDef := { core with rewrites := [rewrite] }
private def later : LanguageDef := { earlier with equations := [equality] }

private theorem literal_later : LiteralRoots later := by
  intro r hr
  have same : r = rewrite := by simpa [later, earlier] using hr
  subst r
  exact ⟨rfl, (isFirstOrder_iff _).mp (by decide +kernel),
    (isFirstOrder_iff _).mp (by decide +kernel)⟩

private theorem instanceAtCycle (base : BasePremiseEvaluator) :
    EquationInstanceAt base later 0 equality.left equality.right := by
  apply EquationInstanceAt.forward (equation := equality) (initialBindings := []) (finalBindings := [])
  · exact List.mem_cons_self
  · decide +kernel
  · decide +kernel
  · exact PremisesAt.nil []
  · simp [equality, applyBindings]

private theorem no_entry_earlier (base : BasePremiseEvaluator) :
    ¬ StepModuloEquations base earlier q ok := by
  classical
  have literal : LiteralRoots earlier := literal_later
  rw [literal_root_iff base earlier literal]
  rintro ⟨r, accepted, _⟩
  obtain ⟨member, matching⟩ := List.mem_filter.mp accepted
  have eq := (equationEquiv_iff_eq_of_no_generators
    (base := base) (language := earlier) (by decide +kernel) _ _).mp
      (of_decide_eq_true (p := EquationEquiv base earlier r.left q) matching)
  have atom : r = rewrite := by simpa [earlier] using member
  subst r
  exact (show rewrite.left ≠ q by decide +kernel) eq

/-- Publishing a compound equation can open a previously unavailable rule
without changing a single rewrite declaration. The equation changes a
representative *inside* the call, and is cyclic in the expansion sense. -/
theorem cyclic_alias_opens_next_entry (base : BasePremiseEvaluator) :
    present? .front core raw.atoms = some earlier ∧
    present? .front core (raw.add cycle).atoms = some later ∧
    earlier.rewrites = later.rewrites ∧
    ¬ StepModuloEquations base earlier q ok ∧
    StepModuloEquations base later q ok := by
  refine ⟨rfl, rfl, rfl, no_entry_earlier base, ?_⟩
  have same : EquationEquiv base later q rewrite.left :=
    equationInstance_fill_equivalent (.apply "Inspect" [] .hole []) ⟨0, instanceAtCycle base⟩
  apply (literal_root_iff base later literal_later _ _).mpr
  classical
  exact ⟨rewrite, List.mem_filter.mpr ⟨List.mem_cons_self,
    decide_eq_true ((equationSetoid base later).iseqv.symm same)⟩,
    Relation.EqvGen.refl _⟩

theorem open_definition_and_subtype_are_not_data :
    let openDefinition : Atom := .expression [.symbol "=", .var "p", .symbol "body"]
    let subtypeAssignment : Atom := .expression [.symbol ":<", .symbol "Dog", .symbol "Animal"]
    classify openDefinition = ⟨.definition, none⟩ ∧ classify subtypeAssignment = ⟨.subtype, none⟩ ∧
    readEquation openDefinition = none := by decide +kernel

theorem variadic_preference_is_not_a_rewrite :
    let spell (op : String) := [.expression [.symbol op, .symbol "A", .symbol "B", .symbol "C"]]
    let declared : LanguageDef :=
      { core with equations := aliasEquations (.apply "A" []) [.apply "B" [], .apply "C" []] }
    present? .back core (spell "=e") = some declared ∧
    present? .back core (spell "=e>") = some declared ∧
    present? .back core (spell "=e<") = some declared :=
  ⟨rfl, rfl, rfl⟩

theorem type_assignment_is_not_a_rewrite :
    let subject : Atom := .symbol "A"
    let type : Atom := .symbol "Term"
    let atoms := [(Content.assignment subject type).syntax]
    present? .front core atoms = some core ∧
      Assignments.HasType (fun _ _ => False) (fun _ _ => False) atoms subject type := by
  exact ⟨rfl, Assignments.type_assignment (by simp [Assignments.TypeAssignment])⟩

private def sameHead (x y : Atom) := Atom.expression [.symbol "same", x, y]
private def schematicLhs : Atom := sameHead (.var "x") (.var "x")
private def choice (h : String) : Atom :=
  (Content.definition schematicLhs (atomCall h (.var "x"))).syntax

private def choices : List Atom := [choice "left", choice "right"]
private def openInput (s t : String) : Pattern :=
  .apply "same" [.apply s [], .apply t []]
private def openResult (h : String) : Pattern := .apply h [.apply "A" []]
private def openRule (h : String) : RewriteRule :=
  { name := "space definition", typeContext := [], premises := []
    left := .apply "same" [.fvar "x", .fvar "x"], right := .apply h [.fvar "x"] }

private def openSpace : PresentedSpace :=
  ⟨choices, { core with rewrites := [openRule "left", openRule "right"] }⟩

private def equatedOpen : PresentedSpace :=
  ⟨choices ++ [(Content.equation .indifferent (.symbol "A") (.symbol "B") []).syntax],
    { openSpace.language with equations := aliasEquations (.apply "A" []) [.apply "B" []] }⟩

theorem open_definitions_presented : present .back core choices = some openSpace := rfl

private theorem open_aligned : isUnconditionalAligned openSpace.language = true :=
  present_aligned .back core rfl choices .schematic rfl

theorem open_definitions_preserve_both_alternatives (base : BasePremiseEvaluator) (output : Pattern) :
    (openSpace.theory base).Step (openInput "A" "A") output ↔
      output = openResult "left" ∨ output = openResult "right" := by
  change StepModuloEquations base openSpace.language _ _ ↔ _
  rw [stepModuloEquations_iff_step_of_no_generators (by decide +kernel),
    step_iff_mem_rootReducts base openSpace.language open_aligned]
  have reducts : rootReducts openSpace.language (openInput "A" "A") =
      [openResult "left", openResult "right"] := by decide +kernel
  simp [reducts]

theorem repeated_variable_rejects_different_values (base : BasePremiseEvaluator) (output : Pattern) :
    ¬ (openSpace.theory base).Step (openInput "A" "B") output := by
  change ¬ StepModuloEquations base openSpace.language _ _
  rw [stepModuloEquations_iff_step_of_no_generators (by decide +kernel),
    step_iff_mem_rootReducts base openSpace.language open_aligned]
  have reducts : rootReducts openSpace.language (openInput "A" "B") = [] := by decide +kernel
  simp [reducts]

/-- In the same theory a written equation can make the non-linear pattern
applicable. Nothing is normalized in the source syntax. -/
theorem repeated_variable_can_agree_modulo_equations (base : BasePremiseEvaluator) :
    present .back core equatedOpen.atoms = some equatedOpen ∧
      (equatedOpen.theory base).Step (openInput "A" "B") (openResult "right") := by
  refine ⟨rfl, ?_⟩
  have ab : EquationEquiv base equatedOpen.language (.apply "B" []) (.apply "A" []) :=
    aliasEquations_connect base equatedOpen.language (.apply "A" []) [.apply "B" []]
      (.apply (by simp)) (by simp; exact .apply (by simp))
      (List.Subset.refl _) (by simp) (by simp)
  have inputs := equationEquiv_fill (.apply "same" [.apply "A" []] .hole []) ab
  refine ⟨openInput "A" "A", openResult "right", inputs, ?_, Relation.EqvGen.refl _⟩
  exact (step_iff_mem_rootReducts base equatedOpen.language open_aligned _ _).mpr (by decide +kernel)

/-- An extension is generally a map of presentations, not the identity
as a behavioural morphism. Two previously inert inputs can be bisimilar;
a new definition can distinguish them. -/
theorem identity_extension_need_not_be_bisimilarity_preserving (base : BasePremiseEvaluator) :
    ¬ ∃ m : Mettapedia.GSLT.GSLT.Morphism (gsltModuloEquations base core) (openSpace.theory base),
      m.toFun = id := by
  let source := gsltModuloEquations base core
  let x := openInput "A" "A"
  let y := openInput "A" "B"
  have stuck (a b : Pattern) : ¬ source.Step a b := by
    change ¬ StepModuloEquations base core a b
    rw [stepModuloEquations_iff_step_of_no_generators rfl,
      step_iff_mem_rootReducts base core rfl]
    exact List.not_mem_nil
  let inert : source.Term → source.Term → Prop :=
    fun a b => source.IsNormalForm a ∧ source.IsNormalForm b
  have bisim : source.Bisimilar x y := by
    refine ⟨inert, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro a b neither a' step
      exact (neither.1 ⟨a', step⟩).elim
    · intro a b neither b' step
      exact (neither.2 ⟨b', step⟩).elim
    · rintro ⟨other, step⟩; exact stuck x other step
    · rintro ⟨other, step⟩; exact stuck y other step
  rintro ⟨mapping, identity⟩
  have equal := mapping.preserves_bisim bisim
  rw [identity] at equal
  obtain ⟨_, response, related⟩ := equal
  have fires := (open_definitions_preserve_both_alternatives base _).mpr (Or.inl rfl)
  obtain ⟨after, possible, _⟩ := response.1 related fires
  exact repeated_variable_rejects_different_values base after possible

end Examples

end Mettapedia.Languages.MeTTa.SpaceTheory.Presentation
