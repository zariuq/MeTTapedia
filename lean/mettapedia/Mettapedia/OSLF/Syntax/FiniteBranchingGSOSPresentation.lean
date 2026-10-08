import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSPremises
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.OfMap

/-!
# Natural finite behavior from independent GSOS clauses

A clause has finite positive occurrences, finite negative availability
tests, and one authored target tree. Its complete set of selected premise
assignments is finite because each requested action has finitely many
successors. A finite collection of clauses therefore produces a complete
finite target set for each output action, even with infinitely many actions.

Both directions of the variable-map equation are earned by lifting each
positive occurrence separately. Clause identifiers and their complete
selected inputs remain available as firing receipts; equal target trees
and variable identifications may collapse their extensional outputs.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Premises

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)
open Classical

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}

namespace Pattern

variable {sort : S.Srt} {operator : S.Operator sort}

/-- Enumerate all positive choices, preserving their occurrence positions. -/
def inputs (pattern : Pattern (Actions := Actions) operator) {X : S.Families}
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator) :
    Finset (Input pattern X) :=
  (Finset.univ.pi (fun occurrence =>
    (arguments (pattern.address occurrence).1).2 (pattern.address occurrence).2)).image
    (fun choices => ⟨fun position => (arguments position).1,
      fun occurrence => choices occurrence (Finset.mem_univ occurrence)⟩)

theorem mem_inputs (pattern : Pattern (Actions := Actions) operator) {X : S.Families}
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (input : Input pattern X) :
    input ∈ pattern.inputs arguments ↔
      (∀ position, input.originals position = (arguments position).1) ∧
        ∀ occurrence, input.derivatives occurrence ∈
          (arguments (pattern.address occurrence).1).2 (pattern.address occurrence).2 := by
  constructor
  · intro member
    obtain ⟨choices, supplied, same⟩ := Finset.mem_image.mp member
    subst input
    exact ⟨fun _ => rfl, fun occurrence =>
      (Finset.mem_pi.mp supplied) occurrence (Finset.mem_univ occurrence)⟩
  · rintro ⟨originals, derivatives⟩
    apply Finset.mem_image.mpr
    refine ⟨fun occurrence _ => input.derivatives occurrence, ?_, ?_⟩
    · exact Finset.mem_pi.mpr (fun occurrence _ => derivatives occurrence)
    · cases input with
      | mk sources successors =>
          congr 1
          funext position
          exact (originals position).symm

end Pattern

/-- An ordinary clause with no semantic law in its data. -/
structure Rule {sort : S.Srt} (operator : S.Operator sort) where
  pattern : Pattern (Actions := Actions) operator
  target : S.Term (variableFamily pattern) sort

namespace Rule

variable {sort : S.Srt} {operator : S.Operator sort}

def output (rule : Rule (Actions := Actions) operator) {X : S.Families}
    (input : Input rule.pattern X) : S.Term X sort :=
  S.rename input.assignment rule.target

theorem output_map (rule : Rule (Actions := Actions) operator) {X Y : S.Families}
    (mapping : X ⟶ Y) (input : Input rule.pattern X) :
    rule.output (input.map mapping) = S.rename mapping (rule.output input) :=
  (NaturalConclusion.ofTarget rule.pattern rule.target).naturality mapping input

/-- The finite target set is computed from all actual selected premise inputs. -/
def targets (rule : Rule (Actions := Actions) operator) {X : S.Families}
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator) :
    Finset (S.Term X sort) :=
  if ∀ address ∈ rule.pattern.negative, (arguments address.1).2 address.2 = ∅ then
    (rule.pattern.inputs arguments).image rule.output
  else ∅

theorem mem_targets (rule : Rule (Actions := Actions) operator) {X : S.Families}
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (target : S.Term X sort) :
    target ∈ rule.targets arguments ↔
      ∃ input : Input rule.pattern X, Matches rule.pattern arguments input ∧ rule.output input = target := by
  by_cases negatives : ∀ address ∈ rule.pattern.negative, (arguments address.1).2 address.2 = ∅
  · rw [targets, if_pos negatives, Finset.mem_image]
    constructor
    · rintro ⟨input, member, same⟩
      obtain ⟨originals, derivatives⟩ := (Pattern.mem_inputs _ _ _).mp member
      exact ⟨input, ⟨originals, derivatives, negatives⟩, same⟩
    · rintro ⟨input, matching, same⟩
      exact ⟨input, (Pattern.mem_inputs _ _ _).mpr ⟨matching.1, matching.2.1⟩, same⟩
  · rw [targets, if_neg negatives]
    constructor
    · intro impossible
      exact False.elim (Finset.notMem_empty _ impossible)
    · rintro ⟨input, matching, _⟩
      exact False.elim (negatives matching.2.2)

/-- Complete forward and inverse occurrence lifting gives actual naturality. -/
theorem targets_map (rule : Rule (Actions := Actions) operator) {X Y : S.Families}
    (mapping : X ⟶ Y)
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator) :
    rule.targets (mapArguments mapping arguments) =
      Mettapedia.CategoryTheory.FinitePowerset.map (S.rename mapping) (rule.targets arguments) := by
  apply Finset.ext
  intro target
  rw [mem_targets, Mettapedia.CategoryTheory.FinitePowerset.mem_map]
  constructor
  · rintro ⟨input, matching, same⟩
    obtain ⟨earlier, held, recovered⟩ := matches_lift rule.pattern mapping arguments input matching
    refine ⟨rule.output earlier, (mem_targets _ _ _).mpr ⟨earlier, held, rfl⟩, ?_⟩
    rw [← output_map, recovered]
    exact same
  · rintro ⟨earlierTarget, member, same⟩
    obtain ⟨input, matching, readout⟩ := (mem_targets _ _ _).mp member
    refine ⟨input.map mapping, matches_map rule.pattern mapping arguments input matching, ?_⟩
    rw [output_map, readout]
    exact same

end Rule

/-- A finite set of clauses at each operator and output action. -/
abbrev Presentation (S : Signature.{u}) (Actions : S.Srt → Type u) :=
  (sort : S.Srt) → (operator : S.Operator sort) → Actions sort → Finset (Rule (Actions := Actions) operator)

namespace Presentation

variable (presentation : Presentation S Actions)

def targets {X : S.Families} {sort : S.Srt} (operator : S.Operator sort)
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (action : Actions sort) : Finset (S.Term X sort) :=
  (presentation sort operator action).biUnion (fun rule => rule.targets arguments)

theorem mem_targets {X : S.Families} {sort : S.Srt} (operator : S.Operator sort)
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (action : Actions sort) (target : S.Term X sort) :
    target ∈ targets presentation operator arguments action ↔
      ∃ rule ∈ presentation sort operator action,
        ∃ input : Input rule.pattern X, Matches rule.pattern arguments input ∧ rule.output input = target := by
  simp only [targets, Finset.mem_biUnion, Rule.mem_targets]

theorem targets_map {X Y : S.Families} (mapping : X ⟶ Y) {sort : S.Srt}
    (operator : S.Operator sort)
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (action : Actions sort) :
    targets presentation operator (mapArguments mapping arguments) action =
      Mettapedia.CategoryTheory.FinitePowerset.map (S.rename mapping)
        (targets presentation operator arguments action) := by
  apply Finset.ext
  intro target
  simp only [targets, Finset.mem_biUnion, Rule.targets_map,
    Mettapedia.CategoryTheory.FinitePowerset.mem_map]
  constructor
  · rintro ⟨rule, member, value, held, same⟩
    exact ⟨value, ⟨rule, member, held⟩, same⟩
  · rintro ⟨value, ⟨rule, member, held⟩, same⟩
    exact ⟨rule, member, value, held, same⟩

/-- The actual law is constructed from independently authored matching clauses. -/
def toLaw : Law S Actions where
  app X := fun base sort => ↾(fun layer =>
    match base, layer with
    | .unit, ⟨operator, arguments⟩ => targets presentation operator arguments)
  naturality {X Y} mapping := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro layer
    cases base
    rcases layer with ⟨operator, arguments⟩
    funext action
    exact targets_map presentation mapping operator arguments action

/-- Denotation refers to actual supplied positive choices and negative tests. -/
def Denotes (law : Law S Actions) : Prop :=
  ∀ (X : S.Families) sort (operator : S.Operator sort) arguments action target,
    target ∈ law.app X PUnit.unit sort ⟨operator, arguments⟩ action ↔
      ∃ rule ∈ presentation sort operator action,
        ∃ input : Input rule.pattern X, Matches rule.pattern arguments input ∧ rule.output input = target

theorem toLaw_denotes : Denotes presentation (toLaw presentation) := by
  intro X sort operator arguments action target
  exact mem_targets presentation operator arguments action target

theorem law_unique (candidate : Law S Actions) (denotes : Denotes presentation candidate) :
    candidate = toLaw presentation := by
  apply NatTrans.ext
  funext X base sort
  apply ConcreteCategory.hom_ext
  intro layer
  cases base
  rcases layer with ⟨operator, arguments⟩
  funext action
  apply Finset.ext
  intro target
  exact (denotes X sort operator arguments action target).trans
    (mem_targets presentation operator arguments action target).symm

end Presentation

/-- Clause identifiers can retain duplicate clauses and their complete inputs. -/
structure AuthoredPresentation (S : Signature.{u}) (Actions : S.Srt → Type u) where
  Origin : (sort : S.Srt) → S.Operator sort → Actions sort → Type u
  finite : ∀ sort operator action, Finite (Origin sort operator action)
  rule : ∀ sort operator action, Origin sort operator action → Rule (Actions := Actions) operator

namespace AuthoredPresentation

variable (authored : AuthoredPresentation S Actions)

def readout : Presentation S Actions := fun sort operator action =>
  let _ : Fintype (authored.Origin sort operator action) :=
    @Fintype.ofFinite _ (authored.finite sort operator action)
  Finset.univ.image (authored.rule sort operator action)

/-- Every selected positive occurrence, negative check and authored origin is retained. -/
structure Firing {X : S.Families} {sort : S.Srt} (operator : S.Operator sort)
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (action : Actions sort) where
  origin : authored.Origin sort operator action
  input : Input (authored.rule sort operator action origin).pattern X
  matching : Matches (authored.rule sort operator action origin).pattern arguments input

def Firing.target {X : S.Families} {sort : S.Srt} {operator : S.Operator sort}
    {arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator}
    {action : Actions sort} (firing : authored.Firing operator arguments action) : S.Term X sort :=
  (authored.rule sort operator action firing.origin).output firing.input

theorem mem_targets_iff_firing {X : S.Families} {sort : S.Srt} (operator : S.Operator sort)
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (action : Actions sort) (target : S.Term X sort) :
    target ∈ Presentation.targets authored.readout operator arguments action ↔
      ∃ firing : authored.Firing operator arguments action, firing.target = target := by
  let _ : Fintype (authored.Origin sort operator action) :=
    @Fintype.ofFinite _ (authored.finite sort operator action)
  rw [Presentation.mem_targets]
  constructor
  · rintro ⟨rule, member, input, matching, same⟩
    obtain ⟨origin, _, identified⟩ := Finset.mem_image.mp member
    subst rule
    exact ⟨⟨origin, input, matching⟩, same⟩
  · rintro ⟨firing, same⟩
    exact ⟨_, Finset.mem_image.mpr ⟨firing.origin, Finset.mem_univ _, rfl⟩,
      firing.input, firing.matching, same⟩

end AuthoredPresentation

end Mettapedia.OSLF.FiniteBranching.Premises
