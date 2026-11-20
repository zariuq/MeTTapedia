import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Correspondences

/-!
# Rules that are consumed when they fire and write themselves back

In the exec discipline a rule occurrence is taken from the state when it fires, and a rule that is
to stay makes itself again. Over any frame action and extensions, take the code system in which each
rule of the present step is its own code and, fired, makes one linear occurrence of itself, without
arguments, in its zone (`WritingBack.codes`). A state whose rule identities each hold a rule linearly
(`consuming`), holding exactly the rules of a program `Q` (`Offers`), then steps, with no ambient
program, as the step of `Q` does on the rows and the knowledge.

* `admits_iff`, `result_consuming`: a firing is admitted exactly when its firing of the program is,
  it uses a held occurrence and it makes one new rule identity; its result is the program's, the
  used occurrence replaced by the new one under the same rule.
* `offers_writeBack`: the rules held are again exactly those of `Q`.
* `consumed_closed`, `consumed_lift`: every step is a step of the program, and, with infinitely many
  rule identities, every step of the program is a step.
* **`consumedCorrespondence`**: so the step of `Q` and this step are in operational correspondence,
  each step one step; `consumed_reachable_iff`.
* **`persistent_iff_consumed`**: holding the rules persistently (the code system `ofRules`) and
  holding them linearly, each writing itself back, reach the same properties of the rows and the
  knowledge.
* Control `stuck_of_no_identity`: when every rule identity is held no firing is admitted, because the
  occurrence written back needs a new identity. Over first-order atoms: with one rule identity the
  program fires (`Atoms.program_fires`) and the store does not (`Atoms.store_stuck`); with the
  identities `ℕ` the store fires (`Atoms.store_fires`).
* A limit (`Atoms.new_identity_free`): the identity of the occurrence written back is free data of a
  firing, so over one firing of the program the store has one firing for each new identity, all
  with the program's result on the rows and the knowledge. The correspondence is of transitions,
  not of firings counted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.WritingBack

open Interface (Frames)
open LogicOverTheStep.StepSpan (Succ)
open FragmentsOfTheStep.TransitionMaps (theoryOf)
open _root_.Mettapedia.GSLT.IndexedOperational (OperationalCorrespondence)

section General

universe uO uT uH uE uOcc uR uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- **The code system of rules that write themselves back**: each rule of the present step is its
own code; fired, it makes one linear occurrence of itself, without arguments, in its zone. -/
abbrev codes {Z : Type uZ} (zoneOf : Rule Tm → Z) : Codes Tm (Rule Tm) Z :=
  ⟨fun r => ⟨r.locals, r.body, r.collect, [], [], [⟨r, [], Mode.linear, zoneOf r⟩], [], [], []⟩,
    fun _ _ _ => False, fun _ _ _ => none⟩

/-- Its specs are plain: the one rule each makes has no arguments. -/
theorem plain {Z : Type uZ} (zoneOf : Rule Tm → Z) (r : Rule Tm) :
    ((codes zoneOf).unfold r).Plain :=
  ⟨rfl, rfl, rfl, fun h inside => by
    obtain rfl := List.mem_singleton.mp inside
    rfl, rfl, rfl⟩

variable {O : Type uOcc} {R : Type uR} {Z : Type uZ} {zoneOf : Rule Tm → Z}

/-- **A state holding rules that are consumed**: each identity of `rules` holds the rule `code ρ`
linearly, without arguments, in the zone of that rule. -/
def consuming (zoneOf : Rule Tm → Z) (s : State Tm O) (rules : Finset R) (code : R → Rule Tm) :
    RState Tm O R (Rule Tm) Z :=
  ⟨s, rules, fun ρ => ⟨code ρ, [], Mode.linear, zoneOf (code ρ)⟩⟩

/-- Such a state is closed: its held rules have no arguments. -/
theorem closed_consuming (s : State Tm O) (rules : Finset R) (code : R → Rule Tm) :
    (consuming zoneOf s rules code).Closed :=
  fun _ _ => rfl

/-- States with the same rows and knowledge are equal when they hold the same identities under the
same labels. -/
theorem mk_congr {T : State Tm O} {r₁ r₂ : Finset R} {h₁ h₂ : R → Held Tm (Rule Tm) Z T.frame}
    (rules : r₁ = r₂) (held : ∀ x, h₁ x = h₂ x) :
    (⟨T, r₁, h₁⟩ : RState Tm O R (Rule Tm) Z) = ⟨T, r₂, h₂⟩ := by
  subst rules
  have same : h₁ = h₂ := funext held
  subst same
  rfl

variable (X : Frames Tm Hom) {E : Extensions.{uO, uH, uE} Hom} {P' Q : Program Tm}
  {rules : Finset R} {code : R → Rule Tm}

/-- **A firing, as a firing of a program** that contains the rule it fires. -/
def toProgram {s : State Tm O} (f : RFiring O R E (codes zoneOf) (consuming zoneOf s rules code))
    (member : (consuming zoneOf s rules code).codeOf f.use ∈ P') : Firing O E P' s.frame :=
  ⟨(consuming zoneOf s rules code).codeOf f.use, member, f.ext, f.opening, f.selection, f.seen⟩

section Agreement

variable {s : State Tm O} (f : RFiring O R E (codes zoneOf) (consuming zoneOf s rules code))

/-- **The shapes of the rule occurrences**, with no ambient program: a held occurrence is used, one
new rule identity is made, and nothing is installed, removed or published. -/
theorem ruleShapes_iff :
    f.RuleShapes (∅ : Set (Rule Tm)) ↔
      ∃ ρ ρ', f.use = Use.held ρ ∧ ρ ∈ rules ∧ f.madeRules = [ρ'] ∧ ρ' ∉ rules ∧
        f.installed = [] ∧ f.removedRules = [] ∧ f.published = [] := by
  obtain ⟨use, ext, opening, selection, seen, made, installed, removed, published⟩ := f
  cases use with
  | ambient c =>
      constructor
      · intro shapes
        exact absurd shapes.available (Set.notMem_empty c)
      · rintro ⟨ρ, ρ', use, -⟩
        have impossible : Use.ambient c = Use.held ρ := use
        cases impossible
  | held ρ =>
      constructor
      · intro shapes
        have one : made.length = 1 := shapes.madeLength.symm
        obtain ⟨ρ', rfl⟩ := List.length_eq_one_iff.mp one
        exact ⟨ρ, ρ', rfl, shapes.available, rfl,
          shapes.madeNew ρ' (List.mem_singleton_self ρ'),
          List.length_eq_zero_iff.mp shapes.installed, List.length_eq_zero_iff.mp shapes.removed,
          List.length_eq_zero_iff.mp shapes.published⟩
      · rintro ⟨ρ₁, ρ', use, held, isMade, new, noInstalled, noRemoved, noPublished⟩
        have sameUse : ρ = ρ₁ := Use.held.inj use
        subst sameUse
        have madeList : made = [ρ'] := isMade
        have installedList : installed = [] := noInstalled
        have removedList : removed = [] := noRemoved
        have publishedList : published = [] := noPublished
        subst madeList installedList removedList publishedList
        exact ⟨held, rfl, rfl, List.nodup_singleton ρ', rfl,
          fun x inside => by
            rw [List.mem_singleton.mp inside]
            exact new,
          rfl, List.nodup_nil, fun x inside => absurd inside List.not_mem_nil, rfl⟩

variable [DecidableEq O]

/-- **Admission agrees**: a firing is admitted exactly when its firing of the program is admitted,
it uses a held occurrence, and it makes one new rule identity and nothing else. -/
theorem admits_iff (member : (consuming zoneOf s rules code).codeOf f.use ∈ P') :
    f.Admits X (∅ : Set (Rule Tm)) ↔ (toProgram f member).Admits X s ∧
      ∃ ρ ρ', f.use = Use.held ρ ∧ ρ ∈ rules ∧ f.madeRules = [ρ'] ∧ ρ' ∉ rules ∧
        f.installed = [] ∧ f.removedRules = [] ∧ f.published = [] := by
  rw [f.admits_plain X (closed_consuming s rules code) (plain zoneOf _) ∅, ruleShapes_iff f]
  exact Iff.rfl

/-- **Control: when every rule identity is held, no firing is admitted**: the occurrence written
back needs a new identity. -/
theorem stuck_of_no_identity (full : ∀ ρ : R, ρ ∈ rules) : ¬ f.Admits X (∅ : Set (Rule Tm)) := by
  intro admitted
  have shapes : f.RuleShapes (∅ : Set (Rule Tm)) := admitted.1.2.2
  obtain ⟨-, ρ', -, -, -, new, -⟩ := (ruleShapes_iff f).mp shapes
  exact new (full ρ')

variable [DecidableEq R]

/-- **The result agrees**: the program's result, the used occurrence replaced by the new one under
the same rule. -/
theorem result_consuming (member : (consuming zoneOf s rules code).codeOf f.use ∈ P') {ρ ρ' : R}
    (use : f.use = Use.held ρ) (made : f.madeRules = [ρ']) (noInstalled : f.installed = [])
    (noRemoved : f.removedRules = []) (noPublished : f.published = []) :
    f.result X = consuming zoneOf ((toProgram f member).result X s) (insert ρ' (rules.erase ρ))
      (Function.update code ρ' (code ρ)) := by
  have info : f.information X = (toProgram f member).information X s :=
    f.information_of_plain X (plain zoneOf _)
  have kept : f.kept = rules.erase ρ := f.kept_linear use rfl noRemoved
  have labels : f.madeLabels X = [⟨code ρ, [], Mode.linear, zoneOf (code ρ)⟩] := by
    obtain ⟨u, ext, opening, selection, seen, madeRules, installed, removed, published⟩ := f
    have isUse : u = Use.held ρ := use
    subst isUse
    have isInstalled : installed = [] := noInstalled
    have isPublished : published = [] := noPublished
    subst isInstalled isPublished
    rfl
  unfold RFiring.result
  rw [info, kept, made, labels]
  refine mk_congr ?_ fun x => ?_
  · rw [List.toFinset_cons, List.toFinset_nil, Finset.union_insert, Finset.union_empty]
  · by_cases same : x = ρ'
    · rw [same]
      have left := assign_zip
        (fun y => ((consuming zoneOf s rules code).held y).act X (E.weaken f.ext)) [ρ']
        [(⟨code ρ, [], Mode.linear, zoneOf (code ρ)⟩ : Held Tm (Rule Tm) Z (E.target f.ext))]
        (List.nodup_singleton ρ') rfl (ρ', _) (List.mem_singleton_self _)
      have right : Function.update code ρ' (code ρ) ρ' = code ρ :=
        Function.update_self ρ' (code ρ) code
      exact left.trans (congrArg
        (fun r => (⟨r, [], Mode.linear, zoneOf r⟩ : Held Tm (Rule Tm) Z (E.target f.ext)))
        right.symm)
    · have left := assign_of_not_mem
        (fun y => ((consuming zoneOf s rules code).held y).act X (E.weaken f.ext)) [ρ']
        [(⟨code ρ, [], Mode.linear, zoneOf (code ρ)⟩ : Held Tm (Rule Tm) Z (E.target f.ext))]
        (j := x) (fun inside => same (List.mem_singleton.mp inside))
      have right : Function.update code ρ' (code ρ) x = code x :=
        Function.update_of_ne same (code ρ) code
      exact left.trans (congrArg
        (fun r => (⟨r, [], Mode.linear, zoneOf r⟩ : Held Tm (Rule Tm) Z (E.target f.ext)))
        right.symm)

end Agreement

section Transitions

variable [DecidableEq O] [DecidableEq R]

/-- **Every admitted firing of the program lifts**, along a held occurrence of its rule and a new
rule identity, to an admitted firing with the program's result. -/
theorem lift_admits {s : State Tm O} (g : Firing O E P' s.frame) (admitted : g.Admits X s)
    {ρ ρ' : R} (held : ρ ∈ rules) (fires : code ρ = g.rule) (new : ρ' ∉ rules) :
    ∃ f : RFiring O R E (codes zoneOf) (consuming zoneOf s rules code),
      f.Admits X (∅ : Set (Rule Tm)) ∧
        f.result X = consuming zoneOf (g.result X s) (insert ρ' (rules.erase ρ))
          (Function.update code ρ' (code ρ)) := by
  obtain ⟨r, inP, ext, opening, selection, seen⟩ := g
  have isRule : code ρ = r := fires
  subst isRule
  let f : RFiring O R E (codes zoneOf) (consuming zoneOf s rules code) :=
    ⟨Use.held ρ, ext, opening, selection, seen, [ρ'], [], [], []⟩
  have member : (consuming zoneOf s rules code).codeOf f.use ∈ P' := inP
  have same : toProgram f member = ⟨code ρ, inP, ext, opening, selection, seen⟩ := rfl
  refine ⟨f, (admits_iff X f member).mpr ⟨?_, ρ, ρ', rfl, held, rfl, new, rfl, rfl, rfl⟩, ?_⟩
  · rw [same]
    exact admitted
  · rw [result_consuming X f member rfl rfl rfl rfl rfl, same]

/-- **The rules held are the same after a firing**: the new occurrence holds the rule of the used
one. -/
theorem offers_writeBack (offers : Offers Q rules code) {ρ ρ' : R} (held : ρ ∈ rules)
    (new : ρ' ∉ rules) :
    Offers Q (insert ρ' (rules.erase ρ)) (Function.update code ρ' (code ρ)) := by
  intro r
  rw [offers r]
  constructor
  · rintro ⟨x, inside, rfl⟩
    by_cases same : x = ρ
    · exact ⟨ρ', Finset.mem_insert_self _ _,
        (Function.update_self ρ' (code ρ) code).trans (congrArg code same.symm)⟩
    · have other : x ≠ ρ' := fun isNew => new (isNew ▸ inside)
      exact ⟨x, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨same, inside⟩),
        Function.update_of_ne other (code ρ) code⟩
  · rintro ⟨x, inside, rfl⟩
    rcases Finset.mem_insert.mp inside with isNew | old
    · exact ⟨ρ, held, ((congrArg (Function.update code ρ' (code ρ)) isNew).trans
        (Function.update_self ρ' (code ρ) code)).symm⟩
    · have inRules : x ∈ rules := (Finset.mem_erase.mp old).2
      have other : x ≠ ρ' := fun isNew => new (isNew ▸ inRules)
      exact ⟨x, inRules, (Function.update_of_ne other (code ρ) code).symm⟩

variable (R E) in
/-- **Every step is a step of the program**, the used occurrence replaced by a new one under the
same rule. -/
theorem consumed_closed (offers : Offers Q rules code) {s : State Tm O}
    {u : RState Tm O R (Rule Tm) Z}
    (reached : Succ (rstep X O R E (codes zoneOf) (∅ : Set (Rule Tm))).toStep
      (consuming zoneOf s rules code) u) :
    ∃ (t : State Tm O) (ρ ρ' : R), ρ ∈ rules ∧ ρ' ∉ rules ∧
      u = consuming zoneOf t (insert ρ' (rules.erase ρ)) (Function.update code ρ' (code ρ)) ∧
        Succ (step X O E Q).toStep s t := by
  obtain ⟨f, admitted, rfl⟩ := reached
  have shapes : f.RuleShapes (∅ : Set (Rule Tm)) := admitted.1.2.2
  obtain ⟨ρ, ρ', use, held, made, new, noInstalled, noRemoved, noPublished⟩ :=
    (ruleShapes_iff f).mp shapes
  have member : (consuming zoneOf s rules code).codeOf f.use ∈ Q := by
    rw [use]
    exact (offers _).mpr ⟨ρ, held, rfl⟩
  obtain ⟨programAdmitted, -⟩ := (admits_iff X f member).mp admitted
  exact ⟨(toProgram f member).result X s, ρ, ρ', held, new,
    result_consuming X f member use made noInstalled noRemoved noPublished,
    toProgram f member, programAdmitted, rfl⟩

variable (R E) in
/-- **With infinitely many rule identities, every step of the program is a step**: some held
occurrence of the fired rule is used, and a new identity holds the rule again. -/
theorem consumed_lift [Infinite R] (offers : Offers Q rules code) {s t : State Tm O}
    (moved : Succ (step X O E Q).toStep s t) :
    ∃ ρ ρ' : R, ρ ∈ rules ∧ ρ' ∉ rules ∧
      Succ (rstep X O R E (codes zoneOf) (∅ : Set (Rule Tm))).toStep
        (consuming zoneOf s rules code)
        (consuming zoneOf t (insert ρ' (rules.erase ρ)) (Function.update code ρ' (code ρ))) := by
  obtain ⟨g, admitted, rfl⟩ := moved
  obtain ⟨ρ, held, fires⟩ := (offers g.rule).mp g.member
  obtain ⟨ρ', new⟩ := Infinite.exists_notMem_finset rules
  obtain ⟨f, fAdmitted, result⟩ := lift_admits X (zoneOf := zoneOf) g admitted held fires new
  exact ⟨ρ, ρ', held, new, f, fAdmitted, result⟩

variable (R E) in
/-- **A program and its store of consumed rules that write themselves back, as an operational
correspondence**: a state of the step of the program is related to every state that holds exactly
the program's rules linearly beside it. Each step of one is one step of the other. -/
def consumedCorrespondence [Infinite R] (zones : Rule Tm → Z) (program : Program Tm) :
    OperationalCorrespondence (theoryOf (State Tm O) (Succ (step X O E program).toStep))
      (theoryOf (RState Tm O R (Rule Tm) Z)
        (Succ (rstep X O R E (codes zones) (∅ : Set (Rule Tm))).toStep)) where
  related s u := ∃ (ids : Finset R) (ruleOf : R → Rule Tm),
    Offers program ids ruleOf ∧ u = consuming zones s ids ruleOf
  readStep := by
    rintro origin current next ⟨ids, ruleOf, offers, rfl⟩ moved
    obtain ⟨t, ρ, ρ', held, new, same, step⟩ := consumed_closed R X E offers moved
    exact .inr ⟨t, step, _, _, offers_writeBack offers held new, same⟩
  forward := by
    rintro origin after current ⟨ids, ruleOf, offers, rfl⟩ moved
    obtain ⟨ρ, ρ', held, new, step⟩ := consumed_lift R X E (zoneOf := zones) offers moved
    exact ⟨_, path_of_run (Relation.ReflTransGen.single step), _, _,
      offers_writeBack offers held new, rfl⟩

variable (R E) in
/-- **A property of the rows and the knowledge is reached by the program exactly when it is reached
by its store of consumed rules that write themselves back.** -/
theorem consumed_reachable_iff [Infinite R] (offers : Offers Q rules code) (s : State Tm O)
    (φ : State Tm O → Prop) :
    (∃ t : State Tm O, (theoryOf (State Tm O) (Succ (step X O E Q).toStep)).MultiStep s t ∧ φ t) ↔
      ∃ u : RState Tm O R (Rule Tm) Z,
        (theoryOf (RState Tm O R (Rule Tm) Z)
          (Succ (rstep X O R E (codes zoneOf) (∅ : Set (Rule Tm))).toStep)).MultiStep
          (consuming zoneOf s rules code) u ∧ φ u.toState := by
  refine (consumedCorrespondence R X E zoneOf Q).reachable_iff φ
    (fun u : RState Tm O R (Rule Tm) Z => φ u.toState) ?_ ⟨rules, code, offers, rfl⟩
  rintro origin current ⟨_, _, -, rfl⟩
  exact Iff.rfl

variable (R E) in
/-- **Held persistently, or consumed and written back: the same properties of the rows and the
knowledge are reached.** -/
theorem persistent_iff_consumed [Infinite R] (offers : Offers Q rules code) (zone : R → Z)
    (s : State Tm O) (φ : State Tm O → Prop) :
    (∃ u : RState Tm O R (Rule Tm) Z,
        (theoryOf (RState Tm O R (Rule Tm) Z)
          (Succ (rstep X O R E (ofRules Z) (∅ : Program Tm)).toStep)).MultiStep
          (holding s rules code zone) u ∧ φ u.toState) ↔
      ∃ u : RState Tm O R (Rule Tm) Z,
        (theoryOf (RState Tm O R (Rule Tm) Z)
          (Succ (rstep X O R E (codes zoneOf) (∅ : Set (Rule Tm))).toStep)).MultiStep
          (consuming zoneOf s rules code) u ∧ φ u.toState := by
  have persistent := program_reachable_iff R X E (P := (∅ : Program Tm)) offers zone s φ
  rw [Set.empty_union] at persistent
  exact persistent.symm.trans (consumed_reachable_iff R X E offers s φ)

end Transitions

end General

#print axioms ruleShapes_iff
#print axioms admits_iff
#print axioms stuck_of_no_identity
#print axioms result_consuming
#print axioms lift_admits
#print axioms offers_writeBack
#print axioms consumed_closed
#print axioms consumed_lift
#print axioms consumedCorrespondence
#print axioms consumed_reachable_iff
#print axioms persistent_iff_consumed

namespace Atoms

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open Derived (link)
open Derived.Atoms (tokenFiring token_admitted)

/-- The program of one link, from `1` to `2`. -/
def one : Program Tm := {link (c 1) (c 2)}

/-- The rule identity `0` holds that link. -/
theorem offers_one : Offers one ({0} : Finset ℕ) (fun _ => link (c 1) (c 2)) := by
  intro r
  constructor
  · intro inside
    have same : r = link (c 1) (c 2) := inside
    exact ⟨0, Finset.mem_singleton_self 0, same.symm⟩
  · rintro ⟨_, -, rfl⟩
    exact (Set.mem_singleton (link (c 1) (c 2)) : link (c 1) (c 2) ∈ one)

/-- **The program fires at the token.** -/
theorem program_fires : (tokenFiring (P := one) 2 rfl).Admits X Examples.tokenState :=
  token_admitted 2 _

/-- **Control**: with one rule identity, which is held, the store admits no firing, though the
program fires (`program_fires`). -/
theorem store_stuck
    (f : RFiring ℕ Unit E (codes (fun _ : Rule Tm => ()))
      (consuming (fun _ : Rule Tm => ()) Examples.tokenState {()} (fun _ => link (c 1) (c 2)))) :
    ¬ f.Admits X (∅ : Set (Rule Tm)) :=
  stuck_of_no_identity X f (fun ρ => Finset.mem_singleton.mpr (Subsingleton.elim ρ ()))

/-- **With the rule identities `ℕ` the store fires**, to the program's result, and holds the link
again under a new identity. -/
theorem store_fires :
    ∃ ρ ρ' : ℕ, ρ ∈ ({0} : Finset ℕ) ∧ ρ' ∉ ({0} : Finset ℕ) ∧
      Succ (rstep X ℕ ℕ E (codes (fun _ : Rule Tm => ())) (∅ : Set (Rule Tm))).toStep
        (consuming (fun _ : Rule Tm => ()) Examples.tokenState {0} (fun _ => link (c 1) (c 2)))
        (consuming (fun _ : Rule Tm => ())
          ((tokenFiring (P := one) 2 rfl).result X Examples.tokenState)
          (insert ρ' (({0} : Finset ℕ).erase ρ))
          (Function.update (fun _ => link (c 1) (c 2)) ρ' (link (c 1) (c 2)))) :=
  consumed_lift ℕ X E offers_one ⟨tokenFiring 2 rfl, program_fires, rfl⟩

/-- **The new identity is free data of a firing**: two admitted firings of the store over the one
firing of the program, with the program's result on the rows and the knowledge, that hold the link
again under different identities. Counting the firings of the store does not count the firings of
the program. -/
theorem new_identity_free :
    ∃ f₁ f₂ : RFiring ℕ ℕ E (codes (fun _ : Rule Tm => ()))
        (consuming (fun _ : Rule Tm => ()) Examples.tokenState {0} (fun _ => link (c 1) (c 2))),
      f₁.Admits X (∅ : Set (Rule Tm)) ∧ f₂.Admits X (∅ : Set (Rule Tm)) ∧
        (f₁.result X).toState = (f₂.result X).toState ∧
          (f₁.result X).rules ≠ (f₂.result X).rules := by
  obtain ⟨f₁, admitted₁, result₁⟩ := lift_admits X (zoneOf := fun _ : Rule Tm => ())
    (rules := {0}) (code := fun _ => link (c 1) (c 2)) (tokenFiring (P := one) 2 rfl)
    program_fires (ρ := 0) (ρ' := 1) (Finset.mem_singleton_self 0) rfl (by decide)
  obtain ⟨f₂, admitted₂, result₂⟩ := lift_admits X (zoneOf := fun _ : Rule Tm => ())
    (rules := {0}) (code := fun _ => link (c 1) (c 2)) (tokenFiring (P := one) 2 rfl)
    program_fires (ρ := 0) (ρ' := 2) (Finset.mem_singleton_self 0) rfl (by decide)
  have rules₁ : (f₁.result X).rules = insert 1 (({0} : Finset ℕ).erase 0) :=
    congrArg RState.rules result₁
  have rules₂ : (f₂.result X).rules = insert 2 (({0} : Finset ℕ).erase 0) :=
    congrArg RState.rules result₂
  refine ⟨f₁, f₂, admitted₁, admitted₂,
    (congrArg RState.toState result₁).trans (congrArg RState.toState result₂).symm, ?_⟩
  intro same
  have inside : (1 : ℕ) ∈ insert 2 (({0} : Finset ℕ).erase 0) := by
    rw [← rules₂, ← same, rules₁]
    exact Finset.mem_insert_self _ _
  exact absurd inside (by decide)

#print axioms offers_one
#print axioms program_fires
#print axioms store_stuck
#print axioms store_fires
#print axioms new_identity_free

end Atoms

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.WritingBack
