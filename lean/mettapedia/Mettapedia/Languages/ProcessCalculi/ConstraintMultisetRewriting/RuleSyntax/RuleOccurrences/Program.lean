import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Plain

/-!
# The step of a program is the candidate with part of the program ambient and the rest held

Over any frame action and extensions, take the code system of the rules of the present step
(`ofRules`: each rule is its own code, with no parameters, no rule queries and no made rules). A
state of the present step with finitely many rule identities, each holding a rule persistently and
without arguments, is a state of the candidate (`holding`). Let `P` be the ambient program, and let
the rules held be exactly those of a program `Q` (`Offers`). Then:

* **Firings project** (`toProgram`, `admits_toProgram_iff`): a firing is admitted exactly when its use
  is available (a rule of `P`, or a held occurrence), it makes, installs and removes no rule
  occurrence, and its firing of the program `P ∪ Q` is admitted; its result is the program's result
  with the same rules held (`result_holding`).
* **Firings lift** (`lift_admits`): every admitted firing of `P ∪ Q`, with every available use of its
  rule, gives an admitted firing with that result.
* **`program_eq`**: the transition relation of the candidate between such states is the transition
  relation of `step X O E (P ∪ Q)`, and the candidate never leaves them (`holding_closed`).

**Which form a program takes.**
* *Ambient* (`ambient_eq`, the case `Q = ∅`): for **every** program `P`, finite or not, the present
  step of `P` is the candidate with ambient program `P` at the states that hold no rule.
* *Held* (`held_eq`, the case `P = ∅`): the present step of `Q` is the candidate with no ambient
  program at the states that hold the rules of `Q` persistently. The rules a state holds are finitely
  many, so this form exists exactly for the finite programs (`offers_finite`, `offers_self`): an
  infinite family of rules is offered by the ambient program and by no state.

No firing at such a state makes a rule, since no code of `ofRules` does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)

universe uO uT uH uE uOcc uR uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- **The code system of the rules of the present step**: each rule is its own code, with no
parameters, no rule queries and no made or installed rules; no term denotes a rule. -/
abbrev ofRules (Z : Type uZ) : Codes Tm (Rule Tm) Z :=
  ⟨fun r => Spec.ofRule r, fun _ _ _ => False, fun _ _ _ => none⟩

variable {O : Type uOcc} {R : Type uR} {Z : Type uZ}

/-- **A state of the present step holding rules**: each identity of `rules` holds the rule `code ρ`
persistently, without arguments, in the zone `zone ρ`. -/
def holding (s : State Tm O) (rules : Finset R) (code : R → Rule Tm) (zone : R → Z) :
    RState Tm O R (Rule Tm) Z :=
  ⟨s, rules, fun ρ => ⟨code ρ, [], .persistent, zone ρ⟩⟩

theorem holding_injective {s t : State Tm O} {rules : Finset R} {code : R → Rule Tm} {zone : R → Z}
    (same : holding s rules code zone = holding t rules code zone) : s = t :=
  congrArg RState.toState same

/-- Such a state is closed: its held rules have no arguments. -/
theorem closed_holding (s : State Tm O) (rules : Finset R) (code : R → Rule Tm) (zone : R → Z) :
    (holding s rules code zone).Closed :=
  fun _ _ => rfl

variable (X : Frames Tm Hom) {E : Extensions.{uO, uH, uE} Hom} {P Q P' : Program Tm}
  {rules : Finset R} {code : R → Rule Tm} {zone : R → Z}

/-- **A firing, as a firing of a program** that contains the rule it fires. -/
def toProgram {s : State Tm O} (f : RFiring O R E (ofRules Z) (holding s rules code zone))
    (member : (holding s rules code zone).codeOf f.use ∈ P') : Firing O E P' s.frame :=
  ⟨(holding s rules code zone).codeOf f.use, member, f.ext, f.opening, f.selection, f.seen⟩

section Agreement

variable {s : State Tm O} (f : RFiring O R E (ofRules Z) (holding s rules code zone))
  (member : (holding s rules code zone).codeOf f.use ∈ P')

/-- **The shapes of the rule occurrences**, for a rule of the present step: the use is available, and
no rule occurrence is made, installed or removed. -/
theorem ruleShapes_iff (ambient : Set (Rule Tm)) :
    f.RuleShapes ambient ↔
      (holding s rules code zone).Available ambient f.use ∧ f.madeRules = [] ∧ f.installed = [] ∧
        f.removedRules = [] ∧ f.published = [] := by
  constructor
  · intro shapes
    exact ⟨shapes.available, List.length_eq_zero_iff.mp shapes.madeLength.symm,
      List.length_eq_zero_iff.mp shapes.installed, List.length_eq_zero_iff.mp shapes.removed,
      List.length_eq_zero_iff.mp shapes.published⟩
  · rintro ⟨available, none, noInstalled, noRemoved, noPublished⟩
    refine ⟨available, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨use, ext, opening, selection, seen, made, installed, removed, published⟩ := f
      cases use <;> rfl
    · rw [noInstalled]
      rfl
    · rw [none]
      exact List.nodup_nil
    · rw [none]
      rfl
    · intro ρ inside
      rw [none] at inside
      exact absurd inside List.not_mem_nil
    · rw [noRemoved]
      rfl
    · rw [noRemoved]
      exact List.nodup_nil
    · intro x inside
      rw [noRemoved, List.zip_nil_right] at inside
      exact absurd inside List.not_mem_nil
    · rw [noPublished]
      rfl

variable [DecidableEq O]

/-- **Admission agrees**: a firing is admitted exactly when its firing of the program is admitted,
its use is available, and it makes, installs and removes no rule occurrence. -/
theorem admits_toProgram_iff (ambient : Set (Rule Tm)) :
    f.Admits X ambient ↔ (toProgram f member).Admits X s ∧
      (holding s rules code zone).Available ambient f.use ∧ f.madeRules = [] ∧ f.installed = [] ∧
        f.removedRules = [] ∧ f.published = [] := by
  rw [f.admits_plain X (closed_holding s rules code zone) (Spec.plain_ofRule _) ambient,
    ruleShapes_iff f ambient]
  exact Iff.rfl

variable [DecidableEq R]

/-- **The result agrees**: the program's result, with the same rules held. -/
theorem result_holding (none : f.madeRules = []) (noRemoved : f.removedRules = []) :
    f.result X = holding ((toProgram f member).result X s) rules code zone := by
  have info : f.information X = (toProgram f member).information X s :=
    f.information_of_plain X (Spec.plain_ofRule _)
  have kept : f.kept = rules := by
    obtain ⟨use, ext, opening, selection, seen, made, installed, removed, published⟩ := f
    cases use with
    | ambient c => exact RFiring.kept_ambient _ rfl noRemoved
    | held ρ => exact RFiring.kept_persistent _ rfl rfl noRemoved
  unfold RFiring.result
  rw [info, kept, none, List.toFinset_nil, Finset.union_empty]
  rfl

end Agreement

/-! ## Lifting firings of the program -/

section Lift

variable [DecidableEq O] [DecidableEq R]

/-- **Every admitted firing of the program lifts**, along every available use of its rule, to an
admitted firing with the program's result and the same rules held. -/
theorem lift_admits {s : State Tm O} (g : Firing O E P' s.frame) (admitted : g.Admits X s)
    {ambient : Set (Rule Tm)} {u : Use (Rule Tm) R}
    (available : (holding s rules code zone).Available ambient u)
    (fires : (holding s rules code zone).codeOf u = g.rule) :
    ∃ (f : RFiring O R E (ofRules Z) (holding s rules code zone))
      (member : (holding s rules code zone).codeOf f.use ∈ P'),
      f.use = u ∧ toProgram f member = g ∧ f.Admits X ambient ∧
        f.result X = holding (g.result X s) rules code zone := by
  obtain ⟨r, inP, ext, opening, selection, seen⟩ := g
  subst fires
  let f : RFiring O R E (ofRules Z) (holding s rules code zone) :=
    ⟨u, ext, opening, selection, seen, [], [], [], []⟩
  have same : toProgram f inP = ⟨(holding s rules code zone).codeOf u, inP, ext, opening, selection, seen⟩ :=
    rfl
  refine ⟨f, inP, rfl, same,
    (admits_toProgram_iff X f inP ambient).mpr ⟨?_, available, rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [same]
    exact admitted
  · rw [result_holding X f inP rfl rfl, same]

omit [DecidableEq R] in
/-- **Two admitted firings with the same use and the same firing of the program are equal**: a firing
at such a state is determined by its use and its firing of the program. -/
theorem eq_of_toProgram_eq {s : State Tm O} {ambient : Set (Rule Tm)}
    {f f' : RFiring O R E (ofRules Z) (holding s rules code zone)}
    (admitted : f.Admits X ambient) (admitted' : f'.Admits X ambient) (use : f.use = f'.use)
    (member : (holding s rules code zone).codeOf f.use ∈ P')
    (member' : (holding s rules code zone).codeOf f'.use ∈ P')
    (same : toProgram f member = toProgram f' member') : f = f' := by
  obtain ⟨-, -, none, noInstalled, noRemoved, noPublished⟩ :=
    (admits_toProgram_iff X f member ambient).mp admitted
  obtain ⟨-, -, none', noInstalled', noRemoved', noPublished'⟩ :=
    (admits_toProgram_iff X f' member' ambient).mp admitted'
  obtain ⟨u, ext, opening, selection, seen, made, installed, removed, published⟩ := f
  obtain ⟨u', ext', opening', selection', seen', made', installed', removed', published'⟩ := f'
  simp only at use none noInstalled noRemoved noPublished none' noInstalled' noRemoved' noPublished'
  subst use none noInstalled noRemoved noPublished none' noInstalled' noRemoved' noPublished'
  obtain ⟨-, extSame, openingSame, selectionSame, seenSame⟩ := Firing.mk.inj same
  subst extSame selectionSame seenSame
  have openings : opening = opening' := eq_of_heq openingSame
  subst openings
  rfl

end Lift

/-! ## The transition relations are equal -/

section Transitions

variable [DecidableEq O] [DecidableEq R]

/-- The rules held are exactly those of the program. -/
def Offers (Q : Program Tm) (rules : Finset R) (code : R → Rule Tm) : Prop :=
  ∀ r, r ∈ Q ↔ ∃ ρ ∈ rules, code ρ = r

omit [DecidableEq O] [DecidableEq R] in
/-- An available use fires a rule of the ambient program or of the program held. -/
theorem mem_union_of_available (offers : Offers Q rules code) (s : State Tm O) (zone : R → Z)
    {u : Use (Rule Tm) R} (available : (holding s rules code zone).Available P u) :
    (holding s rules code zone).codeOf u ∈ P ∪ Q := by
  cases u with
  | ambient c => exact Or.inl available
  | held ρ => exact Or.inr ((offers _).mpr ⟨ρ, available, rfl⟩)

omit [DecidableEq O] [DecidableEq R] in
/-- Every rule of the ambient program or of the program held has an available use. -/
theorem available_of_mem (offers : Offers Q rules code) (s : State Tm O) (zone : R → Z)
    {r : Rule Tm} (member : r ∈ P ∪ Q) :
    ∃ u : Use (Rule Tm) R, (holding s rules code zone).Available P u ∧
      (holding s rules code zone).codeOf u = r := by
  rcases member with inP | inQ
  · exact ⟨.ambient r, inP, rfl⟩
  · obtain ⟨ρ, held, holds⟩ := (offers r).mp inQ
    exact ⟨.held ρ, held, holds⟩

variable (R E) in
/-- **The step of a program is the candidate with part of it ambient and the rest held**: with
ambient program `P`, between states that hold exactly the rules of `Q` persistently, the transition
relation is that of `step X O E (P ∪ Q)`. -/
theorem program_eq (offers : Offers Q rules code) (zone : R → Z) (s t : State Tm O) :
    Succ (rstep X O R E (ofRules Z) P).toStep (holding s rules code zone) (holding t rules code zone) ↔
      Succ (step X O E (P ∪ Q)).toStep s t := by
  constructor
  · rintro ⟨f, admitted, reached⟩
    have member := mem_union_of_available offers s zone admitted.1.2.2.available
    obtain ⟨programAdmitted, -, none, -, noRemoved, -⟩ := (admits_toProgram_iff X f member P).mp admitted
    refine ⟨toProgram f member, programAdmitted, ?_⟩
    have result := result_holding X f member none noRemoved
    have same : holding ((toProgram f member).result X s) rules code zone = holding t rules code zone :=
      result.symm.trans reached
    exact holding_injective same
  · rintro ⟨g, admitted, reached⟩
    obtain ⟨u, available, fires⟩ := available_of_mem offers s zone g.member
    obtain ⟨f, -, -, -, fAdmitted, result⟩ := lift_admits X g admitted available fires
    refine ⟨f, fAdmitted, ?_⟩
    show f.result X = holding t rules code zone
    rw [result]
    exact congrArg (fun u => holding u rules code zone) reached

variable (R E) in
/-- **The candidate never leaves the states that hold the program's rules.** -/
theorem holding_closed (offers : Offers Q rules code) (zone : R → Z) {s : State Tm O}
    {u : RState Tm O R (Rule Tm) Z} (reached : Succ (rstep X O R E (ofRules Z) P).toStep
      (holding s rules code zone) u) :
    ∃ t, u = holding t rules code zone ∧ Succ (step X O E (P ∪ Q)).toStep s t := by
  obtain ⟨f, admitted, rfl⟩ := reached
  have member := mem_union_of_available offers s zone admitted.1.2.2.available
  obtain ⟨programAdmitted, -, none, -, noRemoved, -⟩ := (admits_toProgram_iff X f member P).mp admitted
  exact ⟨(toProgram f member).result X s, result_holding X f member none noRemoved,
    toProgram f member, programAdmitted, rfl⟩

/-! ## The two forms -/

omit [DecidableEq O] [DecidableEq R] in
/-- No rule is held by the empty set of identities. -/
theorem offers_empty (code : R → Rule Tm) : Offers (∅ : Program Tm) (∅ : Finset R) code := by
  intro r
  constructor
  · intro inside
    exact absurd inside (Set.notMem_empty r)
  · rintro ⟨ρ, inside, -⟩
    exact absurd inside (Finset.notMem_empty ρ)

omit [DecidableEq O] [DecidableEq R] in
/-- **A finite program is held by identities that are its rules themselves.** -/
theorem offers_self (Q : Finset (Rule Tm)) :
    Offers (↑Q : Program Tm) Q (id : Rule Tm → Rule Tm) := by
  intro r
  constructor
  · intro inside
    exact ⟨r, Finset.mem_coe.mp inside, rfl⟩
  · rintro ⟨ρ, inside, rfl⟩
    exact Finset.mem_coe.mpr inside

omit [DecidableEq O] [DecidableEq R] in
/-- **Only a finite program is held**: the rules a state holds are finitely many. -/
theorem offers_finite (offers : Offers Q rules code) : Q.Finite := by
  apply Set.Finite.subset ((Finset.finite_toSet rules).image code)
  intro r inside
  obtain ⟨ρ, held, holds⟩ := (offers r).mp inside
  exact ⟨ρ, Finset.mem_coe.mpr held, holds⟩

variable (R E) in
/-- **The ambient form**: for every program, finite or not, the present step of `P` is the candidate
with ambient program `P` at the states that hold no rule. -/
theorem ambient_eq (P : Program Tm) (code : R → Rule Tm) (zone : R → Z) (s t : State Tm O) :
    Succ (rstep X O R E (ofRules Z) P).toStep (holding s ∅ code zone) (holding t ∅ code zone) ↔
      Succ (step X O E P).toStep s t := by
  have general := program_eq (P := P) R X E (offers_empty code) zone s t
  rw [Set.union_empty] at general
  exact general

variable (R E) in
/-- **The held form**: the present step of `Q` is the candidate with no ambient program at the states
that hold exactly the rules of `Q` persistently. -/
theorem held_eq (offers : Offers Q rules code) (zone : R → Z) (s t : State Tm O) :
    Succ (rstep X O R E (ofRules Z) (∅ : Set (Rule Tm))).toStep (holding s rules code zone)
        (holding t rules code zone) ↔
      Succ (step X O E Q).toStep s t := by
  have general := program_eq (P := (∅ : Program Tm)) R X E offers zone s t
  rw [Set.empty_union] at general
  exact general

end Transitions

#print axioms ruleShapes_iff
#print axioms admits_toProgram_iff
#print axioms result_holding
#print axioms lift_admits
#print axioms eq_of_toProgram_eq
#print axioms program_eq
#print axioms holding_closed
#print axioms offers_empty
#print axioms offers_self
#print axioms offers_finite
#print axioms ambient_eq
#print axioms held_eq

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
