import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Systems

/-!
# Reduction-closed barbed congruence on the step of a program

Fix any family of observations `obs : B → State Tm O → Prop` (the barbs; `MayBarb` is the one
chosen, see `Systems`).

## Definitions

* **A barbed bisimulation** (`Bisimulation`): a symmetric relation on systems that preserves the
  barbs and answers every reduction by a reduction into the relation. **Closed bisimilarity**
  (`Bisimilar`) is the largest one: the behaviour of a system with no context.
* **A candidate** (`Candidate`): a barbed bisimulation closed under every basic context. The right
  side applies the same context with the identities of the added rows chosen afresh for it
  (`Basic.rename`): an observer adds rows, not addresses.
* **Reduction-closed barbed congruence** (`Congruent`): the largest candidate (`candidate_congruent`).
* **Contextual equivalence** (`ContextuallyEquivalent`): under every composite context that applies to
  both systems, the same barbs are reachable; `ContextuallyEquivalentUpTo` lets the right side choose
  the identities of added rows.

## What is proved here, for every frame action, extension and barb family

* **An equivalence relation** (`congruent_equivalence`). Transitivity holds because the right side
  may rename the identities a context adds: the middle system never blocks a context.
* **A congruence for each kind of context**: rules (`Congruent.addRules`), tells (`Congruent.tell`),
  extensions of the frame (`Congruent.extend`), rows up to the choice of their identities
  (`Congruent.addRows`), composite contexts (`Congruent.composite`), running beside another system
  (`Congruent.beside`). The rows closure with the same identities is proved in `Strong`, from the
  laws.
* **Sound for contextual equivalence** (`congruent_contextualUpTo`), and contained in closed
  bisimilarity (`Congruent.bisimilar`); congruent systems move together (`Congruent.moves`).
* **Fewer barbs, a coarser congruence** (`Congruent.of_barbs`).
* **Up to the congruence** (`congruent_of_upTo`): a relation whose reductions are answered up to the
  congruence is contained in it.
* **Replacing part of a program** (`replace_congruent`): when every admitted firing of `P₁` is answered
  at the same state by an admitted firing of `P₂` with a congruent result, and conversely, then
  `P₁ ∪ Q` and `P₂ ∪ Q` are congruent at every state, for every `Q`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence

open Interface (Frames)

universe uO uT uH uE uOcc uB uB'

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

section Definitions

variable (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O] (E : Extensions.{uO, uH, uE} Hom)
  {B : Type uB} (obs : B → State Tm O → Prop)

/-- **A barbed bisimulation**: symmetric, preserving the barbs, closed under reductions. -/
structure Bisimulation (R : System Tm O → System Tm O → Prop) : Prop where
  symm : ∀ {S T : System Tm O}, R S T → R T S
  barbs : ∀ {S T : System Tm O}, R S T → ∀ β, obs β S.state → obs β T.state
  reduces : ∀ {S T : System Tm O}, R S T → ∀ {S' : System Tm O}, Reduces X O E S S' →
    ∃ T', Reduces X O E T T' ∧ R S' T'

/-- **Closed bisimilarity**: the behaviour with no context. -/
def Bisimilar (S T : System Tm O) : Prop := ∃ R, Bisimulation X O E obs R ∧ R S T

/-- **A candidate**: a barbed bisimulation closed under every basic context; at the right side the
identities of added rows are chosen afresh. -/
structure Candidate (R : System Tm O → System Tm O → Prop) : Prop
    extends Bisimulation X O E obs R where
  context : ∀ {S T : System Tm O}, R S T → ∀ c : Basic Tm O E, c.Applies S →
    ∃ π : Equiv.Perm O, (c.rename π).Applies T ∧ R (c.apply X S) ((c.rename π).apply X T)

/-- **Reduction-closed barbed congruence**: related by some candidate. -/
def Congruent (S T : System Tm O) : Prop := ∃ R, Candidate X O E obs R ∧ R S T

/-- Many reductions. -/
def Reaches : System Tm O → System Tm O → Prop := Relation.ReflTransGen (Reduces X O E)

/-- **A barb is reachable.** -/
def Converges (S : System Tm O) (β : B) : Prop := ∃ S', Reaches X O E S S' ∧ obs β S'.state

/-- **Contextual equivalence**: under every composite context that applies to both, the same barbs
are reachable. -/
def ContextuallyEquivalent (S T : System Tm O) : Prop :=
  ∀ C : List (Basic Tm O E), AppliesAll X C S → AppliesAll X C T →
    ∀ β, Converges X O E obs (applyAll X C S) β ↔ Converges X O E obs (applyAll X C T) β

/-- **Contextual equivalence up to the identities of added rows.** -/
def ContextuallyEquivalentUpTo (S T : System Tm O) : Prop :=
  (∀ C : List (Basic Tm O E), AppliesAll X C S → ∃ C', RenamesAll C' C ∧ AppliesAll X C' T ∧
    ∀ β, Converges X O E obs (applyAll X C S) β ↔ Converges X O E obs (applyAll X C' T) β) ∧
  (∀ C : List (Basic Tm O E), AppliesAll X C T → ∃ C', RenamesAll C' C ∧ AppliesAll X C' S ∧
    ∀ β, Converges X O E obs (applyAll X C T) β ↔ Converges X O E obs (applyAll X C' S) β)

end Definitions

section Theory

variable {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {B : Type uB} {obs : B → State Tm O → Prop}

/-- A candidate relates only congruent systems. -/
theorem Candidate.le_congruent {R : System Tm O → System Tm O → Prop}
    (candidate : Candidate X O E obs R) {S T : System Tm O} (related : R S T) :
    Congruent X O E obs S T :=
  ⟨R, candidate, related⟩

/-- **The congruence is itself a candidate**, hence the largest one. -/
theorem candidate_congruent : Candidate X O E obs (Congruent X O E obs) where
  symm := fun ⟨R, candidate, related⟩ => ⟨R, candidate, candidate.symm related⟩
  barbs := fun ⟨_, candidate, related⟩ => candidate.barbs related
  reduces := fun ⟨R, candidate, related⟩ _ moved => by
    obtain ⟨T', moved', related'⟩ := candidate.reduces related moved
    exact ⟨T', moved', R, candidate, related'⟩
  context := fun ⟨R, candidate, related⟩ c applies => by
    obtain ⟨π, applies', related'⟩ := candidate.context related c applies
    exact ⟨π, applies', R, candidate, related'⟩

/-- Equality is a candidate. -/
theorem candidate_eq : Candidate X O E obs (fun S T : System Tm O => S = T) where
  symm := fun same => same.symm
  barbs := fun same β holds => same ▸ holds
  reduces := fun {_ _} same {S'} moved => ⟨S', same ▸ moved, rfl⟩
  context := fun {S _} same c applies => by
    subst same
    exact ⟨1, by rw [Basic.rename_one]; exact applies, by rw [Basic.rename_one]⟩

theorem Congruent.refl (S : System Tm O) : Congruent X O E obs S S :=
  candidate_eq.le_congruent rfl

theorem Congruent.symm {S T : System Tm O} (related : Congruent X O E obs S T) :
    Congruent X O E obs T S :=
  candidate_congruent.symm related

/-- The composite of the congruence with itself is a candidate: a context applying to the left
system is renamed for the middle one, and again for the right one. -/
theorem candidate_comp :
    Candidate X O E obs (fun S U => ∃ T, Congruent X O E obs S T ∧ Congruent X O E obs T U) where
  symm := fun ⟨T, one, two⟩ => ⟨T, two.symm, one.symm⟩
  barbs := fun ⟨_, one, two⟩ β holds =>
    candidate_congruent.barbs two β (candidate_congruent.barbs one β holds)
  reduces := fun ⟨_, one, two⟩ _ moved => by
    obtain ⟨T', movedT, one'⟩ := candidate_congruent.reduces one moved
    obtain ⟨U', movedU, two'⟩ := candidate_congruent.reduces two movedT
    exact ⟨U', movedU, T', one', two'⟩
  context := fun ⟨_, one, two⟩ c applies => by
    obtain ⟨π, appliesT, one'⟩ := candidate_congruent.context one c applies
    obtain ⟨ρ, appliesU, two'⟩ := candidate_congruent.context two (c.rename π) appliesT
    rw [Basic.rename_rename] at appliesU two'
    exact ⟨ρ * π, appliesU, _, one', two'⟩

theorem Congruent.trans {S T U : System Tm O} (one : Congruent X O E obs S T)
    (two : Congruent X O E obs T U) : Congruent X O E obs S U :=
  candidate_comp.le_congruent ⟨T, one, two⟩

/-- **Reduction-closed barbed congruence is an equivalence relation.** -/
theorem congruent_equivalence : Equivalence (Congruent X O E obs) :=
  ⟨Congruent.refl, Congruent.symm, Congruent.trans⟩

/-! ### A congruence for each kind of context -/

/-- **Adding rules.** -/
theorem Congruent.addRules {S T : System Tm O} (related : Congruent X O E obs S T)
    (added : Program Tm) :
    Congruent X O E obs ⟨S.program ∪ added, S.state⟩ ⟨T.program ∪ added, T.state⟩ := by
  obtain ⟨_, -, related'⟩ := candidate_congruent.context related (.rules added)
    (Basic.applies_of_ids_empty rfl S)
  exact related'

/-- **Telling equations.** -/
theorem Congruent.tell {S T : System Tm O} (related : Congruent X O E obs S T)
    (equations : (a : Obj) → EquationStore (Tm a)) :
    Congruent X O E obs ⟨S.program, tellState S.state (equations S.state.frame)⟩
      ⟨T.program, tellState T.state (equations T.state.frame)⟩ := by
  obtain ⟨_, -, related'⟩ := candidate_congruent.context related (.tell equations)
    (Basic.applies_of_ids_empty rfl S)
  exact related'

/-- **Extending the frame.** -/
theorem Congruent.extend {S T : System Tm O} (related : Congruent X O E obs S T)
    (extension : (a : Obj) → E.Ext a) :
    Congruent X O E obs ⟨S.program, extendState X E S.state (extension S.state.frame)⟩
      ⟨T.program, extendState X E T.state (extension T.state.frame)⟩ := by
  obtain ⟨_, -, related'⟩ := candidate_congruent.context related (.extend extension)
    (Basic.applies_of_ids_empty rfl S)
  exact related'

/-- **Adding rows**, with the identities of the new rows chosen afresh at the right side. -/
theorem Congruent.addRows {S T : System Tm O} (related : Congruent X O E obs S T) (ids : Finset O)
    (label : (a : Obj) → O → Tm a) (apart : Disjoint ids S.state.present) :
    ∃ π : Equiv.Perm O, Disjoint (ids.map π.toEmbedding) T.state.present ∧
      Congruent X O E obs ⟨S.program, addRows S.state ids (label S.state.frame)⟩
        ⟨T.program, addRows T.state (ids.map π.toEmbedding) (fun o => label T.state.frame (π.symm o))⟩ :=
  candidate_congruent.context related (.rows ids label) apart

/-- **Composite contexts.** -/
theorem Congruent.composite {S T : System Tm O} (related : Congruent X O E obs S T)
    {C : List (Basic Tm O E)} (applies : AppliesAll X C S) :
    ∃ C', RenamesAll C' C ∧ AppliesAll X C' T ∧
      Congruent X O E obs (applyAll X C S) (applyAll X C' T) := by
  induction applies generalizing T with
  | nil S => exact ⟨[], .nil, .nil T, related⟩
  | @cons c C S first _ ih =>
      obtain ⟨π, firstT, related'⟩ := candidate_congruent.context related c first
      obtain ⟨C', renames, restT, related''⟩ := ih related'
      exact ⟨c.rename π :: C', .cons ⟨π, rfl⟩ renames, .cons firstT restT, related''⟩

/-- **Running beside another system**, its identities chosen afresh at the right side. -/
theorem Congruent.beside {S T : System Tm O} (related : Congruent X O E obs S T)
    (added : Program Tm) (ids : Finset O) (label : (a : Obj) → O → Tm a)
    (knowledge : (a : Obj) → EquationStore (Tm a)) (apart : Disjoint ids S.state.present) :
    ∃ C', RenamesAll C' (beside (E := E) added ids label knowledge) ∧ AppliesAll X C' T ∧
      Congruent X O E obs (applyAll X (beside (E := E) added ids label knowledge) S)
        (applyAll X C' T) :=
  related.composite ((appliesAll_beside_iff X added ids label knowledge S).mpr apart)

/-! ### Soundness, closed behaviour, moves -/

/-- A congruent system answers every run. -/
theorem Congruent.reaches {S T S' : System Tm O} (related : Congruent X O E obs S T)
    (reached : Reaches X O E S S') : ∃ T', Reaches X O E T T' ∧ Congruent X O E obs S' T' := by
  induction reached with
  | refl => exact ⟨T, .refl, related⟩
  | tail _ moved ih =>
      obtain ⟨T₁, reachedT, related₁⟩ := ih
      obtain ⟨T₂, movedT, related₂⟩ := candidate_congruent.reduces related₁ moved
      exact ⟨T₂, reachedT.tail movedT, related₂⟩

/-- A congruent system reaches the same barbs. -/
theorem Congruent.converges {S T : System Tm O} (related : Congruent X O E obs S T) {β : B}
    (converges : Converges X O E obs S β) : Converges X O E obs T β := by
  obtain ⟨S', reached, holds⟩ := converges
  obtain ⟨T', reachedT, related'⟩ := related.reaches reached
  exact ⟨T', reachedT, candidate_congruent.barbs related' β holds⟩

/-- **The congruence is sound for contextual equivalence** (up to the identities of added rows). -/
theorem congruent_contextualUpTo {S T : System Tm O} (related : Congruent X O E obs S T) :
    ContextuallyEquivalentUpTo X O E obs S T := by
  constructor
  · intro C applies
    obtain ⟨C', renames, applies', related'⟩ := related.composite applies
    exact ⟨C', renames, applies', fun _ => ⟨related'.converges, related'.symm.converges⟩⟩
  · intro C applies
    obtain ⟨C', renames, applies', related'⟩ := related.symm.composite applies
    exact ⟨C', renames, applies', fun _ => ⟨related'.converges, related'.symm.converges⟩⟩

/-- **The congruence is contained in closed bisimilarity.** -/
theorem Congruent.bisimilar {S T : System Tm O} (related : Congruent X O E obs S T) :
    Bisimilar X O E obs S T :=
  ⟨Congruent X O E obs, candidate_congruent.toBisimulation, related⟩

/-- **Congruent systems move together.** -/
theorem Congruent.moves {S T : System Tm O} (related : Congruent X O E obs S T)
    (moving : ∃ S', Reduces X O E S S') : ∃ T', Reduces X O E T T' := by
  obtain ⟨S', moved⟩ := moving
  obtain ⟨T', moved', -⟩ := candidate_congruent.reduces related moved
  exact ⟨T', moved'⟩

/-- **Fewer barbs, a coarser congruence**: barbs that are among the given ones give a congruence
containing the given one. -/
theorem Congruent.of_barbs {B' : Type uB'} {obs' : B' → State Tm O → Prop} (translate : B' → B)
    (same : ∀ β s, obs' β s ↔ obs (translate β) s) {S T : System Tm O}
    (related : Congruent X O E obs S T) : Congruent X O E obs' S T := by
  obtain ⟨R, candidate, related⟩ := related
  refine ⟨R, ⟨⟨candidate.symm, fun related β holds => ?_, candidate.reduces⟩, candidate.context⟩,
    related⟩
  exact (same β _).mpr (candidate.barbs related (translate β) ((same β _).mp holds))

/-! ### Up to the congruence -/

/-- A relation up to the congruence. -/
def UpTo (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O] (E : Extensions.{uO, uH, uE} Hom)
    (obs : B → State Tm O → Prop) (R : System Tm O → System Tm O → Prop) (S T : System Tm O) :
    Prop :=
  ∃ S₀ T₀, Congruent X O E obs S S₀ ∧ R S₀ T₀ ∧ Congruent X O E obs T₀ T

/-- **Up to the congruence**: a symmetric relation that preserves the barbs and is closed under
contexts, whose reductions are answered up to the congruence, is contained in the congruence. -/
theorem congruent_of_upTo {R : System Tm O → System Tm O → Prop}
    (symm : ∀ {S T : System Tm O}, R S T → R T S)
    (barbs : ∀ {S T : System Tm O}, R S T → ∀ β, obs β S.state → obs β T.state)
    (reduces : ∀ {S T : System Tm O}, R S T → ∀ {S' : System Tm O}, Reduces X O E S S' →
      ∃ T', Reduces X O E T T' ∧ UpTo X O E obs R S' T')
    (context : ∀ {S T : System Tm O}, R S T → ∀ c : Basic Tm O E, c.Applies S →
      ∃ π : Equiv.Perm O, (c.rename π).Applies T ∧ R (c.apply X S) ((c.rename π).apply X T))
    {S T : System Tm O} (related : R S T) : Congruent X O E obs S T := by
  have candidate : Candidate X O E obs (UpTo X O E obs R) := {
    symm := fun ⟨S₀, T₀, left, r, right⟩ => ⟨T₀, S₀, right.symm, symm r, left.symm⟩
    barbs := fun ⟨_, _, left, r, right⟩ β holds =>
      candidate_congruent.barbs right β (barbs r β (candidate_congruent.barbs left β holds))
    reduces := fun ⟨_, _, left, r, right⟩ _ moved => by
      obtain ⟨S₀', moved₀, left'⟩ := candidate_congruent.reduces left moved
      obtain ⟨T₀', movedT₀, S₁, T₁, one, r', two⟩ := reduces r moved₀
      obtain ⟨T', movedT, right'⟩ := candidate_congruent.reduces right movedT₀
      exact ⟨T', movedT, S₁, T₁, left'.trans one, r', two.trans right'⟩
    context := fun ⟨_, _, left, r, right⟩ c applies => by
      obtain ⟨π₁, applies₀, left'⟩ := candidate_congruent.context left c applies
      obtain ⟨π₂, appliesT₀, r'⟩ := context r (c.rename π₁) applies₀
      obtain ⟨π₃, appliesT, right'⟩ :=
        candidate_congruent.context right ((c.rename π₁).rename π₂) appliesT₀
      rw [Basic.rename_rename] at r'
      rw [Basic.rename_rename, Basic.rename_rename] at right'
      rw [Basic.rename_rename, Basic.rename_rename] at appliesT
      exact ⟨π₃ * (π₂ * π₁), appliesT, _, _, left', r', right'⟩ }
  exact candidate.le_congruent ⟨S, T, Congruent.refl S, related, Congruent.refl T⟩

/-! ### Replacing part of a program -/

/-- A firing of one program, as a firing of another program that contains its rule. -/
def reprogram {P P' : Program Tm} {a : Obj} (f : Firing O E P a) (member : f.rule ∈ P') :
    Firing O E P' a :=
  ⟨f.rule, member, f.ext, f.opening, f.selection, f.seen⟩

theorem admits_reprogram {P P' : Program Tm} {s : State Tm O} (f : Firing O E P s.frame)
    (member : f.rule ∈ P') : (reprogram f member).Admits X s ↔ f.Admits X s :=
  Iff.rfl

theorem result_reprogram {P P' : Program Tm} {s : State Tm O} (f : Firing O E P s.frame)
    (member : f.rule ∈ P') : (reprogram f member).result X s = f.result X s :=
  rfl

variable (X O E obs) in
/-- **One program answers another**: at every state, every admitted firing of `P₁` has an admitted
firing of `P₂` whose result is congruent to its result, beside every program. -/
def Answers (P₁ P₂ : Program Tm) : Prop :=
  ∀ (s : State Tm O) (f : Firing O E P₁ s.frame), f.Admits X s →
    ∃ g : Firing O E P₂ s.frame, g.Admits X s ∧
      ∀ Q : Program Tm, Congruent X O E obs ⟨Q, f.result X s⟩ ⟨Q, g.result X s⟩

/-- A firing of `P₁ ∪ Q` is answered by a firing of `P₂ ∪ Q`. -/
theorem Answers.union {P₁ P₂ : Program Tm} (answers : Answers X O E obs P₁ P₂) (Q : Program Tm)
    (s : State Tm O) (f : Firing O E (P₁ ∪ Q) s.frame) (admitted : f.Admits X s) :
    ∃ g : Firing O E (P₂ ∪ Q) s.frame, g.Admits X s ∧
      ∀ Q' : Program Tm, Congruent X O E obs ⟨Q', f.result X s⟩ ⟨Q', g.result X s⟩ := by
  rcases (Set.mem_union _ _ _).mp f.member with inP | inQ
  · obtain ⟨g, admittedG, related⟩ := answers s (reprogram f inP) admitted
    exact ⟨reprogram g (Or.inl g.member), admittedG, related⟩
  · exact ⟨reprogram f (Or.inr inQ), admitted, fun _ => Congruent.refl _⟩

/-- **Replacing part of a program**: if `P₁` and `P₂` answer each other, then `P₁ ∪ Q` and `P₂ ∪ Q`
are congruent at every state, for every `Q`. -/
theorem replace_congruent {P₁ P₂ : Program Tm} (forward : Answers X O E obs P₁ P₂)
    (backward : Answers X O E obs P₂ P₁) (Q : Program Tm) (s : State Tm O) :
    Congruent X O E obs ⟨P₁ ∪ Q, s⟩ ⟨P₂ ∪ Q, s⟩ := by
  let R : System Tm O → System Tm O → Prop := fun S T => S.state = T.state ∧ ∃ Q : Program Tm,
    (S.program = P₁ ∪ Q ∧ T.program = P₂ ∪ Q) ∨ (S.program = P₂ ∪ Q ∧ T.program = P₁ ∪ Q)
  refine congruent_of_upTo (R := R) ?_ ?_ ?_ ?_ ⟨rfl, Q, .inl ⟨rfl, rfl⟩⟩
  · rintro S T ⟨same, Q, orient⟩
    refine ⟨same.symm, Q, ?_⟩
    rcases orient with ⟨left, right⟩ | ⟨left, right⟩
    · exact .inr ⟨right, left⟩
    · exact .inl ⟨right, left⟩
  · rintro S T ⟨same, -⟩ β holds
    rw [← same]
    exact holds
  · rintro ⟨SP, Ss⟩ ⟨TP, Ts⟩ ⟨same, Q, orient⟩ ⟨S'P, S's⟩ ⟨programSame, f, admitted, reached⟩
    simp only at same programSame
    subst same programSame
    have reached' : f.result X Ss = S's := reached
    subst reached'
    rcases orient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨g, admittedG, related⟩ := forward.union Q Ss f admitted
      exact ⟨⟨P₂ ∪ Q, g.result X Ss⟩, reduces_of_admits g admittedG, ⟨P₁ ∪ Q, g.result X Ss⟩,
        ⟨P₂ ∪ Q, g.result X Ss⟩, related (P₁ ∪ Q), ⟨rfl, Q, .inl ⟨rfl, rfl⟩⟩, Congruent.refl _⟩
    · obtain ⟨g, admittedG, related⟩ := backward.union Q Ss f admitted
      exact ⟨⟨P₁ ∪ Q, g.result X Ss⟩, reduces_of_admits g admittedG, ⟨P₂ ∪ Q, g.result X Ss⟩,
        ⟨P₁ ∪ Q, g.result X Ss⟩, related (P₂ ∪ Q), ⟨rfl, Q, .inr ⟨rfl, rfl⟩⟩, Congruent.refl _⟩
  · rintro ⟨SP, Ss⟩ ⟨TP, Ts⟩ ⟨same, Q, orient⟩ c applies
    simp only at same
    subst same
    refine ⟨1, by rw [Basic.rename_one]; exact applies, ?_⟩
    rw [Basic.rename_one]
    cases c with
    | rows ids label => exact ⟨rfl, Q, orient⟩
    | rules added =>
        refine ⟨rfl, Q ∪ added, ?_⟩
        rcases orient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .inl ⟨Set.union_assoc _ _ _, Set.union_assoc _ _ _⟩
        · exact .inr ⟨Set.union_assoc _ _ _, Set.union_assoc _ _ _⟩
    | tell equations => exact ⟨rfl, Q, orient⟩
    | extend extension => exact ⟨rfl, Q, orient⟩

end Theory

#print axioms candidate_congruent
#print axioms candidate_eq
#print axioms candidate_comp
#print axioms congruent_equivalence
#print axioms Congruent.addRules
#print axioms Congruent.tell
#print axioms Congruent.extend
#print axioms Congruent.addRows
#print axioms Congruent.composite
#print axioms Congruent.beside
#print axioms Congruent.reaches
#print axioms Congruent.converges
#print axioms congruent_contextualUpTo
#print axioms Congruent.bisimilar
#print axioms Congruent.moves
#print axioms Congruent.of_barbs
#print axioms congruent_of_upTo
#print axioms Answers.union
#print axioms replace_congruent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
