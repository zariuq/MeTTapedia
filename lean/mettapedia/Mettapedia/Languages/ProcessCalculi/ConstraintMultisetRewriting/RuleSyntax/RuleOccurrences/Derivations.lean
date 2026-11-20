import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Program
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventMultiplicityRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventMultiplicityRealization

/-!
# Occurrences count derivations: over each firing of the program, one firing per use of its rule

With ambient program `P` at a state that holds the rules of `Q` persistently, the admitted firings
project onto the admitted firings of `P ∪ Q` (`project`). The projection is onto
(`project_surjective`), and over one firing of the program there is exactly one admitted firing for
each available use of its rule:

* `fibre_use_injective`: two admitted firings over the same firing of the program with the same use
  are equal;
* `fibre_use_surjective`: every available use of the rule is the use of an admitted firing over it.

So a rule held twice gives the same transitions (`program_eq`) and two derivations of each
(`two_over_one`), and a rule held once gives one.

**When each rule is offered once** (`Once`: the held rules are told apart by their identities, and
none of them is a rule of the ambient program), the projection is a bijection
(`project_bijective`), and the candidate at these states **realizes** the present step of `P ∪ Q`
in the sense of `Interface.EventMultiplicity.Realization` (`realization`): states go to the states
holding the rules, admitted firings correspond one for one with the same rule and selection, and
results correspond. Hence the two event systems are bisimilar with multiplicities
(`bisimilar_program`), and the correspondence composes with every other such bisimulation by
`Bisimulation.trans`. The ambient form (`once_ambient`) and the held form with identities that are
the rules themselves (`once_self`) are instances.

The hypothesis is needed: with one rule held by two identities, two admitted firings have the same
projection (`not_injective_of_twice`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)
open Interface.EventMultiplicity (Realization Bisimilar)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)

universe uO uT uH uE uOcc uR uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O] {R : Type uR} [DecidableEq R] {Z : Type uZ}
  (X : Frames Tm Hom) {E : Extensions.{uO, uH, uE} Hom} {P Q : Program Tm}
  {rules : Finset R} {code : R → Rule Tm}

/-! ## The projection onto the firings of the program -/

omit [DecidableEq R] in
/-- The rule an admitted firing fires belongs to the ambient program or to the program held. -/
theorem member_of_admits (offers : Offers Q rules code) (zone : R → Z) {s : State Tm O}
    {f : RFiring O R E (ofRules Z) (holding s rules code zone)} (admitted : f.Admits X P) :
    (holding s rules code zone).codeOf f.use ∈ P ∪ Q :=
  mem_union_of_available offers s zone admitted.1.2.2.available

/-- **The projection**: an admitted firing, as an admitted firing of the program `P ∪ Q`. -/
def project (offers : Offers Q rules code) (zone : R → Z) (s : State Tm O) :
    {f : RFiring O R E (ofRules Z) (holding s rules code zone) // f.Admits X P} →
      {g : Firing O E (P ∪ Q) s.frame // g.Admits X s} :=
  fun f => ⟨toProgram f.1 (member_of_admits X offers zone f.2),
    ((admits_toProgram_iff X f.1 (member_of_admits X offers zone f.2) P).mp f.2).1⟩

/-- **Every admitted firing of the program is projected onto.** -/
theorem project_surjective (offers : Offers Q rules code) (zone : R → Z) (s : State Tm O) :
    Function.Surjective (project (E := E) (P := P) X offers zone s) := by
  rintro ⟨g, admitted⟩
  obtain ⟨u, available, fires⟩ := available_of_mem (P := P) offers s zone g.member
  obtain ⟨f, member, -, same, fAdmitted, -⟩ := lift_admits X g admitted available fires
  exact ⟨⟨f, fAdmitted⟩, Subtype.ext same⟩

omit [DecidableEq R] in
/-- **One firing per use, at most**: two admitted firings over the same firing of the program with
the same use are equal. -/
theorem fibre_use_injective (offers : Offers Q rules code) (zone : R → Z) {s : State Tm O}
    {f f' : {f : RFiring O R E (ofRules Z) (holding s rules code zone) // f.Admits X P}}
    (same : project X offers zone s f = project X offers zone s f') (use : f.1.use = f'.1.use) :
    f = f' :=
  Subtype.ext (eq_of_toProgram_eq X f.2 f'.2 use _ _ (congrArg Subtype.val same))

/-- **One firing per use, at least**: every available use of the rule of an admitted firing of the
program is the use of an admitted firing over it. -/
theorem fibre_use_surjective (offers : Offers Q rules code) (zone : R → Z) {s : State Tm O}
    (g : {g : Firing O E (P ∪ Q) s.frame // g.Admits X s}) {u : Use (Rule Tm) R}
    (available : (holding s rules code zone).Available P u)
    (fires : (holding s rules code zone).codeOf u = g.1.rule) :
    ∃ f, project X offers zone s f = g ∧ f.1.use = u := by
  obtain ⟨f, member, use, same, fAdmitted, -⟩ := lift_admits X g.1 g.2 available fires
  exact ⟨⟨f, fAdmitted⟩, Subtype.ext same, use⟩

/-- **A rule held by two identities has two derivations of each of its firings**: over every admitted
firing of the program whose rule both identities hold, there are two different admitted firings. -/
theorem two_over_one (offers : Offers Q rules code) (zone : R → Z) {s : State Tm O}
    (g : {g : Firing O E (P ∪ Q) s.frame // g.Admits X s}) {ρ ρ' : R} (held : ρ ∈ rules)
    (held' : ρ' ∈ rules) (different : ρ ≠ ρ') (holds : code ρ = g.1.rule)
    (holds' : code ρ' = g.1.rule) :
    ∃ f f', project X offers zone s f = g ∧ project X offers zone s f' = g ∧ f ≠ f' := by
  obtain ⟨f, lands, use⟩ := fibre_use_surjective X offers zone g (u := .held ρ) held holds
  obtain ⟨f', lands', use'⟩ := fibre_use_surjective X offers zone g (u := .held ρ') held' holds'
  refine ⟨f, f', lands, lands', fun same => different ?_⟩
  have uses : Use.held ρ = (Use.held ρ' : Use (Rule Tm) R) := by
    rw [← use, ← use', same]
  exact Use.held.inj uses

/-! ## Each rule offered once -/

/-- **Each rule is offered once**: no held rule is a rule of the ambient program, and the held rules
are told apart by their identities. -/
def Once (P : Program Tm) (rules : Finset R) (code : R → Rule Tm) : Prop :=
  (∀ ρ ∈ rules, code ρ ∉ P) ∧ ∀ ρ ∈ rules, ∀ ρ' ∈ rules, code ρ = code ρ' → ρ = ρ'

omit [DecidableEq O] [DecidableEq R] in
/-- When each rule is offered once, an available use is determined by the rule it fires. -/
theorem use_unique (once : Once P rules code) (zone : R → Z) (s : State Tm O)
    {u u' : Use (Rule Tm) R} (available : (holding s rules code zone).Available P u)
    (available' : (holding s rules code zone).Available P u')
    (same : (holding s rules code zone).codeOf u = (holding s rules code zone).codeOf u') : u = u' := by
  cases u with
  | ambient c =>
      cases u' with
      | ambient c' => exact congrArg Use.ambient same
      | held ρ' =>
          have inP : code ρ' ∈ P := by
            have rule : c = code ρ' := same
            rw [← rule]
            exact available
          exact absurd inP (once.1 ρ' available')
  | held ρ =>
      cases u' with
      | ambient c' =>
          have inP : code ρ ∈ P := by
            have rule : code ρ = c' := same
            rw [rule]
            exact available'
          exact absurd inP (once.1 ρ available)
      | held ρ' => exact congrArg Use.held (once.2 ρ available ρ' available' same)

omit [DecidableEq O] [DecidableEq R] in
/-- The ambient form offers each rule once. -/
theorem once_ambient (P : Program Tm) (code : R → Rule Tm) : Once P (∅ : Finset R) code :=
  ⟨fun ρ inside => absurd inside (Finset.notMem_empty ρ),
    fun ρ inside => absurd inside (Finset.notMem_empty ρ)⟩

omit [DecidableEq O] [DecidableEq R] in
/-- The held form with identities that are the rules themselves offers each rule once. -/
theorem once_self (Q : Finset (Rule Tm)) : Once (∅ : Program Tm) Q (id : Rule Tm → Rule Tm) :=
  ⟨fun ρ _ inside => absurd inside (Set.notMem_empty ρ), fun _ _ _ _ same => same⟩

/-- **When each rule is offered once, the projection is a bijection.** -/
theorem project_bijective (offers : Offers Q rules code) (once : Once P rules code) (zone : R → Z)
    (s : State Tm O) : Function.Bijective (project (E := E) (P := P) X offers zone s) := by
  refine ⟨fun f f' same => ?_, project_surjective X offers zone s⟩
  have rule : (holding s rules code zone).codeOf f.1.use = (holding s rules code zone).codeOf f'.1.use :=
    congrArg (fun g : {g : Firing O E (P ∪ Q) s.frame // g.Admits X s} => g.1.rule) same
  exact fibre_use_injective X offers zone same
    (use_unique once zone s f.2.1.2.2.available f'.2.1.2.2.available rule)

/-- **The hypothesis is needed**: when two identities hold the rule of an admitted firing of the
program, the projection is not injective. -/
theorem not_injective_of_twice (offers : Offers Q rules code) (zone : R → Z) {s : State Tm O}
    (g : {g : Firing O E (P ∪ Q) s.frame // g.Admits X s}) {ρ ρ' : R} (held : ρ ∈ rules)
    (held' : ρ' ∈ rules) (different : ρ ≠ ρ') (holds : code ρ = g.1.rule)
    (holds' : code ρ' = g.1.rule) :
    ¬ Function.Injective (project (E := E) (P := P) X offers zone s) := by
  intro injective
  obtain ⟨f, f', lands, lands', apart⟩ :=
    two_over_one X offers zone g held held' different holds holds'
  exact apart (injective (lands.trans lands'.symm))

/-! ## The candidate realizes the present step, firing for firing -/

variable (R E) in
/-- **The candidate realizes the present step of `P ∪ Q`** when each rule is offered once: a state
goes to the state holding the rules of `Q`, admitted firings correspond one for one, with the same
rule and the same selection, and results correspond. -/
noncomputable def realization (offers : Offers Q rules code) (once : Once P rules code)
    (zone : R → Z) :
    Realization
      ((step X O E (P ∪ Q)).toStep.eventSystem (Action := Rule Tm × Selection O)
        (fun {_} g => (g.rule, g.selection)))
      ((rstep X O R E (ofRules Z) P).toStep.eventSystem (Action := Rule Tm × Selection O)
        (fun {s'} f => (s'.codeOf f.use, f.selection))) where
  state s := holding s rules code zone
  choices s := (Equiv.ofBijective (project X offers zone s) (project_bijective X offers once zone s)).symm
  actions s choice := by
    have back := Equiv.ofBijective_apply_symm_apply (project X offers zone s)
      (project_bijective X offers once zone s) choice
    exact (congrArg (fun c : {g : Firing O E (P ∪ Q) s.frame // g.Admits X s} =>
      (c.1.rule, c.1.selection)) back).symm
  successors s choice := by
    have back := Equiv.ofBijective_apply_symm_apply (project X offers zone s)
      (project_bijective X offers once zone s) choice
    generalize (Equiv.ofBijective (project X offers zone s)
      (project_bijective X offers once zone s)).symm choice = f at back
    have member := member_of_admits X offers zone f.2
    have none := ((admits_toProgram_iff X f.1 member P).mp f.2).2.2.1
    have noRemoved := ((admits_toProgram_iff X f.1 member P).mp f.2).2.2.2.2.1
    have result := result_holding X f.1 member none noRemoved
    have same : toProgram f.1 member = choice.1 := congrArg Subtype.val back
    show holding (choice.1.result X s) rules code zone = f.1.result X
    rw [result, same]

variable (R E) in
/-- **The present step of `P ∪ Q` and the candidate are bisimilar with multiplicities**, from every
state and the state that holds the rules of `Q`, when each rule is offered once. -/
theorem bisimilar_program (offers : Offers Q rules code) (once : Once P rules code) (zone : R → Z)
    (s : State Tm O) :
    Bisimilar
      ((step X O E (P ∪ Q)).toStep.eventSystem (Action := Rule Tm × Selection O)
        (fun {_} g => (g.rule, g.selection))) s
      ((rstep X O R E (ofRules Z) P).toStep.eventSystem (Action := Rule Tm × Selection O)
        (fun {s'} f => (s'.codeOf f.use, f.selection))) (holding s rules code zone) :=
  (realization R X E offers once zone).bisimilar s

#print axioms project_surjective
#print axioms fibre_use_injective
#print axioms fibre_use_surjective
#print axioms two_over_one
#print axioms use_unique
#print axioms project_bijective
#print axioms not_injective_of_twice
#print axioms realization
#print axioms bisimilar_program

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
