import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Derivations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Derived

/-!
# One occurrence against two: which observer tells them apart

With ambient program `P` at states that hold rules of the present step persistently
(`holding`), compare a state where each rule is offered once with a state where one rule is held by
two identities.

**Over one firing of the program** (`exactly_two`, `exactly_one`): with no ambient program, when
exactly the identities `ρ ≠ ρ'` hold the rule of an admitted firing of the program, exactly two
admitted firings lie over it; when each rule is offered once, exactly one. The two firings reach one
state (`program_eq`). In general (`fibre_occurrences`, `fibre_card`) the admitted firings over an
admitted firing of the program correspond one for one to the identities that hold its rule, so
there are as many of them as occurrences of the rule; `fibre_card_two` and `fibre_card_one` are the
numbers `2` and `1`. This count is taken over one firing of the program, whose opening is fixed, so
it tells one occurrence from two at every frame action.

**Observers.** The candidate is observed as an event system (`Interface.EventMultiplicity.System`)
whose choices are the admitted firings.

* *By the use* (`byUse`: the label of a firing is the occurrence it uses). No bisimulation relates
  a state that does not hold an identity to a state where that identity fires
  (`not_bisimilar_reading_uses`). This observer reads identities, which is more than counting.
* *By rule and selection* (`byRule`: the label is the rule fired and the rows selected).
  * Moving an occurrence to another identity is not observed: two states that each offer each rule
    once are bisimilar (`bisimilar_moved`).
  * **Counting**: when an admitted firing of the program is determined by its rule and its selection,
    a state that offers each rule once and a state where two identities hold the rule of an admitted
    firing are **not** bisimilar (`not_bisimilar_of_twice`).

**The hypothesis has an instance** (`Closed.determined`, `Closed.one_not_two`): over terms without
unknowns, where a firing has no extension and no opening to choose, a firing of a rule without collect query
patterns is determined by its rule and its selection, and the state that holds a link once is not
bisimilar to the state that holds it twice.

**The hypothesis is needed** (`FreeData.free_data`, `FreeData.free_data_same_result`): over
first-order atoms, two admitted firings of one rule with one selection differ in their openings, whose
values off the rule's unknowns are free, and reach one state. There a firing is more than a
derivation, and the state that holds a link once is bisimilar to the state that holds it twice
(`Doubling.one_two_bisimilar`, in the module `Doubling`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)
open Interface.EventMultiplicity (Bisimulation Bisimilar)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)

universe uO uT uH uE uOcc uR uZ

section General

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O] {R : Type uR} [DecidableEq R] {Z : Type uZ}
  (X : Frames Tm Hom) {E : Extensions.{uO, uH, uE} Hom} {P Q : Program Tm}

/-! ## Over one firing of the program -/

/-- **A rule held by exactly two identities has exactly two firings over each of its firings.** -/
theorem exactly_two {rules : Finset R} {code : R → Rule Tm} (offers : Offers Q rules code)
    (zone : R → Z) {s : State Tm O}
    (g : {g : Firing O E ((∅ : Program Tm) ∪ Q) s.frame // g.Admits X s}) {ρ ρ' : R}
    (held : ρ ∈ rules) (held' : ρ' ∈ rules) (different : ρ ≠ ρ') (holds : code ρ = g.1.rule)
    (holds' : code ρ' = g.1.rule)
    (only : ∀ other ∈ rules, code other = g.1.rule → other = ρ ∨ other = ρ') :
    ∃ f f', project X offers zone s f = g ∧ project X offers zone s f' = g ∧ f ≠ f' ∧
      ∀ f'', project X offers zone s f'' = g → f'' = f ∨ f'' = f' := by
  obtain ⟨f, lands, use⟩ := fibre_use_surjective X offers zone g (u := .held ρ) held holds
  obtain ⟨f', lands', use'⟩ := fibre_use_surjective X offers zone g (u := .held ρ') held' holds'
  refine ⟨f, f', lands, lands', ?_, ?_⟩
  · intro same
    have uses : Use.held ρ = (Use.held ρ' : Use (Rule Tm) R) := by
      rw [← use, ← use', same]
    exact different (Use.held.inj uses)
  · intro f'' lands''
    have admitted : f''.1.Admits X (∅ : Program Tm) := f''.2
    have available := admitted.1.2.2.available
    have fires : (holding s rules code zone).codeOf f''.1.use = g.1.rule :=
      congrArg (fun g : {g : Firing O E ((∅ : Program Tm) ∪ Q) s.frame // g.Admits X s} => g.1.rule)
        lands''
    rcases used : f''.1.use with c | other
    · rw [used] at available
      exact absurd available (Set.notMem_empty c)
    · rw [used] at available fires
      rcases only other available fires with isFirst | isSecond
      · refine Or.inl (fibre_use_injective X offers zone (lands''.trans lands.symm) ?_)
        rw [used, isFirst, use]
      · refine Or.inr (fibre_use_injective X offers zone (lands''.trans lands'.symm) ?_)
        rw [used, isSecond, use']

/-- **A rule offered once has exactly one firing over each of its firings.** -/
theorem exactly_one {rules : Finset R} {code : R → Rule Tm} (offers : Offers Q rules code)
    (once : Once P rules code) (zone : R → Z) {s : State Tm O}
    (g : {g : Firing O E (P ∪ Q) s.frame // g.Admits X s}) :
    ∃! f, project X offers zone s f = g :=
  (project_bijective X offers once zone s).existsUnique g

/-- **The firings over a firing of the program are the occurrences that hold its rule**: with no
ambient program, the admitted firings over an admitted firing of the program correspond one for one
to the identities that hold its rule, each firing using its identity. -/
theorem fibre_occurrences {rules : Finset R} {code : R → Rule Tm} (offers : Offers Q rules code)
    (zone : R → Z) {s : State Tm O}
    (g : {g : Firing O E ((∅ : Program Tm) ∪ Q) s.frame // g.Admits X s}) :
    ∃ φ : {ρ : R // ρ ∈ rules ∧ code ρ = g.1.rule} → {f // project X offers zone s f = g},
      Function.Bijective φ ∧ ∀ x, (φ x).1.1.use = Use.held x.1 := by
  have pick : ∀ x : {ρ : R // ρ ∈ rules ∧ code ρ = g.1.rule},
      ∃ f, project X offers zone s f = g ∧ f.1.use = Use.held x.1 :=
    fun x => fibre_use_surjective X offers zone g (u := .held x.1) x.2.1 x.2.2
  choose φ lands uses using pick
  refine ⟨fun x => ⟨φ x, lands x⟩, ⟨?_, ?_⟩, uses⟩
  · intro x y same
    have firings : φ x = φ y := congrArg Subtype.val same
    have held : (Use.held x.1 : Use (Rule Tm) R) = Use.held y.1 := by
      rw [← uses x, ← uses y, firings]
    exact Subtype.ext (Use.held.inj held)
  · rintro ⟨f, landsF⟩
    have admitted : f.1.Admits X (∅ : Program Tm) := f.2
    have available := admitted.1.2.2.available
    have fires : (holding s rules code zone).codeOf f.1.use = g.1.rule :=
      congrArg (fun g : {g : Firing O E ((∅ : Program Tm) ∪ Q) s.frame // g.Admits X s} => g.1.rule)
        landsF
    rcases used : f.1.use with c | ρ
    · rw [used] at available
      exact absurd available (Set.notMem_empty c)
    · rw [used] at available fires
      refine ⟨⟨ρ, available, fires⟩, Subtype.ext ?_⟩
      have sameUse : f.1.use = (φ ⟨ρ, available, fires⟩).1.use := by
        rw [used, uses]
      exact (fibre_use_injective X offers zone
        (landsF.trans (lands ⟨ρ, available, fires⟩).symm) sameUse).symm

/-- **So there are as many firings over a firing of the program as occurrences of its rule.** -/
theorem fibre_card {rules : Finset R} {code : R → Rule Tm} (offers : Offers Q rules code)
    (zone : R → Z) {s : State Tm O}
    (g : {g : Firing O E ((∅ : Program Tm) ∪ Q) s.frame // g.Admits X s}) :
    Nat.card {f // project X offers zone s f = g} =
      Nat.card {ρ : R // ρ ∈ rules ∧ code ρ = g.1.rule} := by
  obtain ⟨φ, bijective, -⟩ := fibre_occurrences X offers zone g
  exact (Nat.card_congr (Equiv.ofBijective φ bijective)).symm

/-- **Held by exactly two identities: two firings over each firing of the program**, as a number. -/
theorem fibre_card_two {rules : Finset R} {code : R → Rule Tm} (offers : Offers Q rules code)
    (zone : R → Z) {s : State Tm O}
    (g : {g : Firing O E ((∅ : Program Tm) ∪ Q) s.frame // g.Admits X s}) {ρ ρ' : R}
    (held : ρ ∈ rules) (held' : ρ' ∈ rules) (different : ρ ≠ ρ') (holds : code ρ = g.1.rule)
    (holds' : code ρ' = g.1.rule)
    (only : ∀ other ∈ rules, code other = g.1.rule → other = ρ ∨ other = ρ') :
    Nat.card {f // project X offers zone s f = g} = 2 := by
  obtain ⟨f, f', lands, lands', apart, all⟩ :=
    exactly_two X offers zone g held held' different holds holds' only
  refine Nat.card_eq_two_iff.mpr ⟨⟨f, lands⟩, ⟨f', lands'⟩,
    fun same => apart (congrArg Subtype.val same), Set.eq_univ_of_forall ?_⟩
  rintro ⟨f'', lands''⟩
  rcases all f'' lands'' with isFirst | isSecond
  · exact Or.inl (Subtype.ext isFirst)
  · exact Or.inr (Subtype.ext isSecond)

/-- **Offered once: one firing over each firing of the program**, as a number. -/
theorem fibre_card_one {rules : Finset R} {code : R → Rule Tm} (offers : Offers Q rules code)
    (once : Once P rules code) (zone : R → Z) {s : State Tm O}
    (g : {g : Firing O E (P ∪ Q) s.frame // g.Admits X s}) :
    Nat.card {f // project X offers zone s f = g} = 1 := by
  obtain ⟨f, lands, unique⟩ := exactly_one X offers once zone g
  have only : Unique {f // project X offers zone s f = g} :=
    ⟨⟨⟨f, lands⟩⟩, fun z => Subtype.ext (unique z.1 z.2)⟩
  exact Nat.card_unique

/-! ## Observers -/

variable (R E Z) in
/-- **The candidate observed by rule and selection**: the label of a firing is the rule it fires and
the rows it selects. -/
abbrev byRule (P : Program Tm) :
    Interface.EventMultiplicity.System (RState Tm O R (Rule Tm) Z) (Rule Tm × Selection O) :=
  (rstep X O R E (ofRules Z) P).toStep.eventSystem (Action := Rule Tm × Selection O)
    (fun {s'} f => (s'.codeOf f.use, f.selection))

variable (R E Z) in
/-- **The candidate observed by the use**: the label of a firing is the occurrence it uses. -/
abbrev byUse (P : Program Tm) :
    Interface.EventMultiplicity.System (RState Tm O R (Rule Tm) Z) (Use (Rule Tm) R) :=
  (rstep X O R E (ofRules Z) P).toStep.eventSystem (Action := Use (Rule Tm) R) (fun {_} f => f.use)

/-- **Reading the use separates** a state that does not hold an identity from a state where that
identity fires. -/
theorem not_bisimilar_reading_uses {rules₁ rules₂ : Finset R} {code₁ code₂ : R → Rule Tm}
    (offers₂ : Offers Q rules₂ code₂) (zone₁ zone₂ : R → Z) {s : State Tm O}
    (g : {g : Firing O E (P ∪ Q) s.frame // g.Admits X s}) {ρ' : R} (held' : ρ' ∈ rules₂)
    (holds' : code₂ ρ' = g.1.rule) (missing : ρ' ∉ rules₁) :
    ¬ Bisimilar (byUse R Z X E P) (holding s rules₁ code₁ zone₁) (byUse R Z X E P)
      (holding s rules₂ code₂ zone₂) := by
  rintro ⟨related, ⟨b⟩, same⟩
  obtain ⟨f₂, -, use⟩ := fibre_use_surjective X offers₂ zone₂ g (u := .held ρ') held' holds'
  obtain ⟨f₁, image⟩ := (b.choices same).surjective f₂
  have act := b.actions same f₁
  rw [image] at act
  have used : f₁.1.use = Use.held ρ' := act.trans use
  have admitted : f₁.1.Admits X P := f₁.2
  have available := admitted.1.2.2.available
  rw [used] at available
  exact missing available

/-- **Moving an occurrence to another identity is not observed** by rule and selection: two states
that each offer each rule once are bisimilar. -/
theorem bisimilar_moved {rules₁ rules₂ : Finset R} {code₁ code₂ : R → Rule Tm}
    (offers₁ : Offers Q rules₁ code₁) (once₁ : Once P rules₁ code₁)
    (offers₂ : Offers Q rules₂ code₂) (once₂ : Once P rules₂ code₂) (zone₁ zone₂ : R → Z)
    (s : State Tm O) :
    Bisimilar (byRule R Z X E P) (holding s rules₁ code₁ zone₁) (byRule R Z X E P)
      (holding s rules₂ code₂ zone₂) :=
  (bisimilar_program R X E offers₁ once₁ zone₁ s).symm.trans
    (bisimilar_program R X E offers₂ once₂ zone₂ s)

/-- **Counting separates one occurrence from two**, when a firing of the program is determined by its
rule and its selection: a state that offers each rule once is not bisimilar, observed by rule and
selection, to a state where two identities hold the rule of an admitted firing. -/
theorem not_bisimilar_of_twice {rules₁ rules₂ : Finset R} {code₁ code₂ : R → Rule Tm}
    (offers₁ : Offers Q rules₁ code₁) (once₁ : Once P rules₁ code₁)
    (offers₂ : Offers Q rules₂ code₂) (zone₁ zone₂ : R → Z) {s : State Tm O}
    (determined : ∀ g g' : {g : Firing O E (P ∪ Q) s.frame // g.Admits X s},
      g.1.rule = g'.1.rule → g.1.selection = g'.1.selection → g = g')
    (g : {g : Firing O E (P ∪ Q) s.frame // g.Admits X s}) {ρ ρ' : R} (held : ρ ∈ rules₂)
    (held' : ρ' ∈ rules₂) (different : ρ ≠ ρ') (holds : code₂ ρ = g.1.rule)
    (holds' : code₂ ρ' = g.1.rule) :
    ¬ Bisimilar (byRule R Z X E P) (holding s rules₁ code₁ zone₁) (byRule R Z X E P)
      (holding s rules₂ code₂ zone₂) := by
  rintro ⟨related, ⟨b⟩, same⟩
  obtain ⟨f, f', lands, lands', apart⟩ :=
    two_over_one X offers₂ zone₂ g held held' different holds holds'
  obtain ⟨h, image⟩ := (b.choices same).surjective f
  obtain ⟨h', image'⟩ := (b.choices same).surjective f'
  have act := b.actions same h
  rw [image] at act
  have act' := b.actions same h'
  rw [image'] at act'
  have labels : ((holding s rules₂ code₂ zone₂).codeOf f.1.use, f.1.selection) =
      ((holding s rules₂ code₂ zone₂).codeOf f'.1.use, f'.1.selection) :=
    (congrArg (fun c : {g : Firing O E (P ∪ Q) s.frame // g.Admits X s} =>
      (c.1.rule, c.1.selection)) lands).trans
      (congrArg (fun c : {g : Firing O E (P ∪ Q) s.frame // g.Admits X s} =>
        (c.1.rule, c.1.selection)) lands').symm
  have left := act.trans (labels.trans act'.symm)
  have projected : project X offers₁ zone₁ s h = project X offers₁ zone₁ s h' :=
    determined _ _ (congrArg Prod.fst left) (congrArg Prod.snd left)
  have equal : h = h' := (project_bijective X offers₁ once₁ zone₁ s).1 projected
  exact apart (image.symm.trans ((congrArg (b.choices same) equal).trans image'))

end General

/-! ## Terms without unknowns: a firing is determined by its rule and its selection -/

namespace Closed

open OneFrame (Terms frames ext)
open Derived (link)

/-- **Terms without unknowns**: there is nothing to instantiate. -/
def action (T : Type uT) : SubstitutionAction T PUnit.{1} where
  E := Eq
  equivalence := eq_equivalence
  apply _ t := t
  identity := PUnit.unit
  compose _ _ := PUnit.unit
  apply_identity _ := rfl
  apply_compose _ _ _ := rfl
  preserves _ := fun same => same

/-- **A firing is determined by its rule and its selection**, for a program whose rules have no
collect patterns. -/
theorem determined {T : Type uT} {O : Type uOcc} [DecidableEq O] {P : Program (Terms T)}
    (noCollect : ∀ r ∈ P, r.collect = []) (s : State (Terms T) O)
    (g g' : {g : Firing O (ext (action T)) P s.frame // g.Admits (frames (action T)) s})
    (rule : g.1.rule = g'.1.rule) (selection : g.1.selection = g'.1.selection) : g = g' := by
  obtain ⟨⟨r, member, e, v, chosen, seen⟩, admitted⟩ := g
  obtain ⟨⟨r', member', e', v', chosen', seen'⟩, admitted'⟩ := g'
  simp only at rule selection
  subst rule selection
  have none : seen = [] := by
    apply List.length_eq_zero_iff.mp
    rw [← admitted.1.2.2.2.2.2.2, noCollect r member]
    rfl
  have none' : seen' = [] := by
    apply List.length_eq_zero_iff.mp
    rw [← admitted'.1.2.2.2.2.2.2, noCollect r member]
    rfl
  subst none none'
  cases e
  cases e'
  cases v
  cases v'
  rfl

/-- A token `1` at row `0`. -/
def token : State (Terms ℕ) ℕ := ⟨PUnit.unit, [], {0}, fun _ => 1⟩

/-- The link from `1` to `2` takes the token and makes row `1`. -/
def tokenFiring {P : Program (Terms ℕ)} (member : link 1 2 ∈ P) :
    Firing ℕ (ext (action ℕ)) P token.frame :=
  ⟨link 1 2, member, PUnit.unit, PUnit.unit, ⟨[0], [], [1]⟩, []⟩

theorem token_admitted {P : Program (Terms ℕ)} (member : link 1 2 ∈ P) :
    (tokenFiring member).Admits (frames (action ℕ)) token := by
  refine ⟨⟨?_, List.nodup_singleton 0, List.nodup_singleton 1, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro b γ h
    exact ⟨PUnit.unit, fun _ _ => rfl, fun _ _ => rfl⟩
  · apply enabled_of <;> simp [tokenFiring, token]
  · refine ⟨PUnit.unit, PUnit.unit, fun e inside => ?_⟩
    have equation : e ∈ [((1 : ℕ), (1 : ℕ))] := inside
    obtain rfl := List.mem_singleton.mp equation
    rfl
  · intro _ σ _
    exact ⟨fun check inside => absurd inside List.not_mem_nil,
      fun q inside => absurd inside List.not_mem_nil⟩

/-- A constant assignment of the link to identities holds exactly the link. -/
theorem offers_link (rules : Finset ℕ) {ρ : ℕ} (inside : ρ ∈ rules) :
    Offers ({link 1 2} : Program (Terms ℕ)) rules (fun _ => link 1 2) := by
  intro r
  constructor
  · intro member
    exact ⟨ρ, inside, (Set.mem_singleton_iff.mp member).symm⟩
  · rintro ⟨_, _, same⟩
    exact Set.mem_singleton_iff.mpr same.symm

/-- **Held once against held twice**: over terms without unknowns, the state that holds the link at
one identity and the state that holds it at two are not bisimilar, observed by rule and selection. -/
theorem one_not_two :
    ¬ Bisimilar
      (byRule ℕ Unit (frames (action ℕ)) (ext (action ℕ)) (∅ : Program (Terms ℕ)))
      (holding token {0} (fun _ => link 1 2) (fun _ => ()))
      (byRule ℕ Unit (frames (action ℕ)) (ext (action ℕ)) (∅ : Program (Terms ℕ)))
      (holding token {0, 1} (fun _ => link 1 2) (fun _ => ())) := by
  have noCollect : ∀ r ∈ ((∅ : Program (Terms ℕ)) ∪ {link 1 2}), r.collect = [] := by
    rintro r (inside | inside)
    · exact absurd inside (Set.notMem_empty r)
    · rw [Set.mem_singleton_iff.mp inside]
      rfl
  exact not_bisimilar_of_twice (frames (action ℕ))
    (offers_link {0} (Finset.mem_singleton_self 0))
    ⟨fun ρ _ inside => absurd inside (Set.notMem_empty _),
      fun ρ inside ρ' inside' _ =>
        (Finset.mem_singleton.mp inside).trans (Finset.mem_singleton.mp inside').symm⟩
    (offers_link {0, 1} (Finset.mem_insert_self 0 {1})) (fun _ => ()) (fun _ => ())
    (determined noCollect token) ⟨tokenFiring (Or.inr rfl), token_admitted _⟩ (ρ := 0) (ρ' := 1)
    (Finset.mem_insert_self 0 {1}) (Finset.mem_insert_of_mem (Finset.mem_singleton_self 1))
    (by decide) rfl rfl

/-- The same two states have the same transitions: both are the present step of the link. -/
theorem one_two_same_transitions (t : State (Terms ℕ) ℕ) :
    Succ (rstep (frames (action ℕ)) ℕ ℕ (ext (action ℕ)) (ofRules Unit) (∅ : Program (Terms ℕ))).toStep
        (holding token {0} (fun _ => link 1 2) (fun _ => ()))
        (holding t {0} (fun _ => link 1 2) (fun _ => ())) ↔
      Succ (rstep (frames (action ℕ)) ℕ ℕ (ext (action ℕ)) (ofRules Unit) (∅ : Program (Terms ℕ))).toStep
        (holding token {0, 1} (fun _ => link 1 2) (fun _ => ()))
        (holding t {0, 1} (fun _ => link 1 2) (fun _ => ())) := by
  rw [program_eq ℕ (frames (action ℕ)) (ext (action ℕ))
      (offers_link {0} (Finset.mem_singleton_self 0)) (fun _ => ()) token t,
    program_eq ℕ (frames (action ℕ)) (ext (action ℕ))
      (offers_link {0, 1} (Finset.mem_insert_self 0 {1})) (fun _ => ()) token t]

/-- The admitted firing of the link at the token, as a firing of the program of the link. -/
abbrev theFiring :
    {g : Firing ℕ (ext (action ℕ)) ((∅ : Program (Terms ℕ)) ∪ {link 1 2}) token.frame //
      g.Admits (frames (action ℕ)) token} :=
  ⟨tokenFiring (Or.inr rfl), token_admitted _⟩

/-- The projection onto the firings of the program, at the state that holds the link at the
identities `0` and `1`. -/
abbrev projectTwice :
    {f : RFiring ℕ ℕ (ext (action ℕ)) (ofRules Unit)
        (holding token {0, 1} (fun _ => link 1 2) (fun _ => ())) //
      f.Admits (frames (action ℕ)) (∅ : Program (Terms ℕ))} →
    {g : Firing ℕ (ext (action ℕ)) ((∅ : Program (Terms ℕ)) ∪ {link 1 2}) token.frame //
      g.Admits (frames (action ℕ)) token} :=
  project (frames (action ℕ)) (offers_link {0, 1} (Finset.mem_insert_self 0 {1})) (fun _ : ℕ => ())
    token

/-- **Exactly two firings over the firing of the link**, at the state that holds it twice: the
instance of `exactly_two`. -/
theorem two_over_token :
    ∃ f f', projectTwice f = theFiring ∧ projectTwice f' = theFiring ∧ f ≠ f' ∧
      ∀ f'', projectTwice f'' = theFiring → f'' = f ∨ f'' = f' :=
  exactly_two (frames (action ℕ)) (offers_link {0, 1} (Finset.mem_insert_self 0 {1}))
    (fun _ : ℕ => ()) theFiring (ρ := 0) (ρ' := 1)
    (Finset.mem_insert_self 0 {1}) (Finset.mem_insert_of_mem (Finset.mem_singleton_self 1))
    (by decide) rfl rfl
    (fun other inside _ => by
      rcases Finset.mem_insert.mp inside with isZero | isOne
      · exact Or.inl isZero
      · exact Or.inr (Finset.mem_singleton.mp isOne))

#print axioms determined
#print axioms token_admitted
#print axioms one_not_two
#print axioms one_two_same_transitions
#print axioms two_over_token

end Closed

/-! ## First-order atoms: a firing is more than a derivation -/

namespace FreeData

open Mettapedia.Logic.LP
open Examples (Tm X E c shift tokenState)
open Derived (link)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- The link from `1` to `2` takes the token and makes row `1`, opened as given. -/
def tokenFiring (opening : Subst atoms) :
    Firing ℕ E ({link (c 1) (c 2)} : Program Tm) tokenState.frame :=
  ⟨link (c 1) (c 2), rfl, PUnit.unit, opening, ⟨[0], [], [1]⟩, []⟩

theorem token_admitted (opening : Subst atoms) : (tokenFiring opening).Admits X tokenState := by
  refine ⟨⟨?_, List.nodup_singleton 0, List.nodup_singleton 1, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · apply Examples.fresh_of_ground action tokenState (tokenFiring opening)
    intro t inside σ
    have terms : t ∈ [c 1, c 2] := inside
    rcases List.mem_cons.mp terms with isTaken | rest
    · rw [isTaken]
      rfl
    · rw [List.mem_singleton.mp rest]
      rfl
  · apply enabled_of <;> simp [tokenFiring, tokenState]
  · refine ⟨PUnit.unit, Subst.id atoms, fun e inside => ?_⟩
    have equation : e ∈ [(c 1, c 1)] := inside
    obtain rfl := List.mem_singleton.mp equation
    rfl
  · intro _ σ _
    exact ⟨fun check inside => absurd inside List.not_mem_nil,
      fun q inside => absurd inside List.not_mem_nil⟩

/-- **Two firings with one rule and one selection**: over first-order atoms the opening is free off
the rule's unknowns, so a firing is not determined by its rule and its selection. -/
theorem free_data :
    ∃ g g' : {g : Firing ℕ E ({link (c 1) (c 2)} : Program Tm) tokenState.frame //
        g.Admits X tokenState},
      g.1.rule = g'.1.rule ∧ g.1.selection = g'.1.selection ∧ g ≠ g' := by
  refine ⟨⟨tokenFiring (Subst.id atoms), token_admitted _⟩, ⟨tokenFiring shift, token_admitted _⟩,
    rfl, rfl, ?_⟩
  intro same
  obtain ⟨-, -, openings, -, -⟩ := Firing.mk.inj (congrArg Subtype.val same)
  have functions : Subst.id atoms = shift := eq_of_heq openings
  have values : (Term.var 0 : Term atoms) = (Term.var 1 : Term atoms) := congrFun functions 0
  exact absurd (Term.var.inj values) (by decide)

/-- The two firings reach the same state. -/
theorem free_data_same_result :
    (tokenFiring (Subst.id atoms)).result X tokenState = (tokenFiring shift).result X tokenState :=
  rfl

#print axioms token_admitted
#print axioms free_data
#print axioms free_data_same_result

end FreeData

#print axioms exactly_two
#print axioms exactly_one
#print axioms fibre_occurrences
#print axioms fibre_card
#print axioms fibre_card_two
#print axioms fibre_card_one
#print axioms not_bisimilar_reading_uses
#print axioms bisimilar_moved
#print axioms not_bisimilar_of_twice

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
