import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.FirstHalf

/-!
# Barbed bisimilarity indexed by a set of names: the translation is fully abstract

The calculus's own correctness notion is a barbed bisimilarity parameterized by a set of names
(Meredith and Radestock, 2005, Definitions 4.1 and 4.2): a process shows the barb `x` over `N` when
it has an output on a channel name-equivalent to a name of `N`; an `N`-barbed bisimulation is
symmetric, answers a reduction by a run, and answers a barb over `N` by a run that shows it.

* `SourceBisimulation N`, `SourceBisimilar N`: that definition on closed processes, with the barb read
  on canonical forms (`Barb`), for `N` a set of closed names.
* `StepBisimulation N`, `StepBisimilar N`: the same definition on the step of the program, with the
  output barb `OutBarb` (the tree's may-barb of `c!(Q)`).
* **Full abstraction is the representation** (`fully_abstract_of_represents`): every translation that
  sends each closed process to a state representing it is fully abstract for every set of closed
  names; `fully_abstract` is the case of `encode`, and the single-row translation, which is not
  homomorphic, is fully abstract too (`encodeRow_fully_abstract`). Control: the translation sending
  every process to the empty state is not (`constant_not_fully_abstract`).
* **The reading of the barb.** `Barb` gives a barb to every output `x!(P)`. The 2005 paper's
  Definition 4.1 gives the out-barb to `x[v]`, that is `x!(*v)`, an output whose payload is the drop of
  a name (`LiteralBarb`). The two readings differ: with `@0` observable, `@0!(0)` and `0` are
  separated under the first (`index_matters`) and barbed bisimilar under the second
  (`index_matters_reading`); `@0!(*@0)` shows the literal barb (`literal_barb_exists`). Everything in
  this folder uses the first reading.
* Controls (`index_matters`): with no observable name, `@0!(0)` and `0` are barbed bisimilar (both
  are stuck); with `@0` observable they are not.
* **The tensor preserves co-representation**: two states that represent the same process, each beside
  the same state, are weakly barbed bisimilar (`weaklyBarbedBisimilar_tensor`). It does not preserve
  weak barbed bisimilarity: `not_congruence_represented` (in `Congruence`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction (output input)
open ByInstantiation (sig G Closed read zeroT outputT dropqT)

/-! ## The two bisimilarities -/

/-- **An `N`-barbed bisimulation of the source** (Definition 4.2 of the 2005 paper, weak, with output
barbs on the channels of `N`). -/
structure SourceBisimulation (N : G [] .nm → Prop) (R : RhoProcess → RhoProcess → Prop) : Prop where
  symm : ∀ {P Q}, R P Q → R Q P
  step : ∀ {P Q P'}, R P Q → rhoLanguageDefGSLT.Step P P' →
    ∃ Q', Relation.ReflTransGen rhoLanguageDefGSLT.Step Q Q' ∧ R P' Q'
  barb : ∀ {P Q} (c : G [] .nm), N c → R P Q → Barb P (canonicalize (read c)) →
    ∃ Q', Relation.ReflTransGen rhoLanguageDefGSLT.Step Q Q' ∧ Barb Q' (canonicalize (read c))

/-- **`N`-barbed bisimilarity of the source.** -/
def SourceBisimilar (N : G [] .nm → Prop) (P Q : RhoProcess) : Prop :=
  ∃ R, SourceBisimulation N R ∧ R P Q

/-- **An `N`-barbed bisimulation of the step.** -/
structure StepBisimulation (N : G [] .nm → Prop)
    (R : ByInstantiation.State → ByInstantiation.State → Prop) : Prop where
  symm : ∀ {s t}, R s t → R t s
  moves : ∀ {s t s'}, R s t → Moves s s' → ∃ t', Runs t t' ∧ R s' t'
  barb : ∀ {s t} (c : G [] .nm), N c → R s t → OutBarb c s → ∃ t', Runs t t' ∧ OutBarb c t'

/-- **`N`-barbed bisimilarity of the step.** -/
def StepBisimilar (N : G [] .nm → Prop) (s t : ByInstantiation.State) : Prop :=
  ∃ R, StepBisimulation N R ∧ R s t

/-- A step bisimulation answers runs by runs. -/
theorem StepBisimulation.runs {N : G [] .nm → Prop}
    {R : ByInstantiation.State → ByInstantiation.State → Prop} (bisimulation : StepBisimulation N R)
    {s t s' : ByInstantiation.State} (related : R s t) (run : Runs s s') :
    ∃ t', Runs t t' ∧ R s' t' := by
  induction run with
  | refl => exact ⟨t, .refl, related⟩
  | tail _ last ih =>
      obtain ⟨t₁, run₁, related₁⟩ := ih
      obtain ⟨t', run', related'⟩ := bisimulation.moves related₁ last
      exact ⟨t', run₁.trans run', related'⟩

/-! ## Full abstraction -/

/-- From a source bisimulation, a step bisimulation: states that represent related processes. -/
theorem step_of_source {N : G [] .nm → Prop} (closedN : ∀ c, N c → Closed c)
    {S : RhoProcess → RhoProcess → Prop} (bisimulation : SourceBisimulation N S) :
    StepBisimulation N (fun s t => ∃ P Q, ByInstantiation.Represents s P ∧
      ByInstantiation.Represents t Q ∧ S P Q) where
  symm := fun ⟨P, Q, onS, onT, related⟩ => ⟨Q, P, onT, onS, bisimulation.symm related⟩
  moves := by
    rintro s t s' ⟨P, Q, onS, onT, related⟩ moved
    rcases (ByInstantiation.succ_iff s s').mp moved with comm | admin
    · obtain ⟨P', step, onS'⟩ := ByInstantiation.reflective_calculus_by_instantiation.2.2.2.1 onS comm
      obtain ⟨Q', run, related'⟩ := bisimulation.step related step
      obtain ⟨t', run', onT'⟩ := reaches_complete onT run
      exact ⟨t', run', P', Q', onS', onT', related'⟩
    · exact ⟨t, .refl, P, Q, ByInstantiation.reflective_calculus_by_instantiation.2.2.1 onS admin,
        onT, related⟩
  barb := by
    rintro s t c inN ⟨P, Q, ⟨value, onS⟩, onT, related⟩ shows
    obtain ⟨Q', run, barb'⟩ := bisimulation.barb c inN related (barb_of_outBarb onS shows)
    obtain ⟨t₁, run₁, value₁, onT₁⟩ := reaches_complete onT run
    obtain ⟨t', run₂, shows'⟩ := barb_eventually onT₁ (closedN c inN) barb'
    exact ⟨t', run₁.trans run₂, shows'⟩

/-- From a step bisimulation, a source bisimulation: processes represented by related states. -/
theorem source_of_step {N : G [] .nm → Prop} (closedN : ∀ c, N c → Closed c)
    {T : ByInstantiation.State → ByInstantiation.State → Prop} (bisimulation : StepBisimulation N T) :
    SourceBisimulation N (fun P Q => ∃ s t, ByInstantiation.Represents s P ∧
      ByInstantiation.Represents t Q ∧ T s t) where
  symm := fun ⟨s, t, onS, onT, related⟩ => ⟨t, s, onT, onS, bisimulation.symm related⟩
  step := by
    rintro P Q P' ⟨s, t, onS, onT, related⟩ step
    obtain ⟨s₂, run, onS₂⟩ := reaches_complete onS (.single step)
    obtain ⟨t₂, run', related₂⟩ := bisimulation.runs related run
    obtain ⟨Q', run'', onT₂⟩ := reaches_sound onT run'
    exact ⟨Q', run'', s₂, t₂, onS₂, onT₂, related₂⟩
  barb := by
    rintro P Q c inN ⟨s, t, ⟨value, onS⟩, onT, related⟩ shows
    obtain ⟨s', run, shows'⟩ := barb_eventually onS (closedN c inN) shows
    obtain ⟨t₁, run₁, related₁⟩ := bisimulation.runs related run
    obtain ⟨t', run₂, shows''⟩ := bisimulation.barb c inN related₁ shows'
    obtain ⟨Q', run', value', onT'⟩ := reaches_sound onT (run₁.trans run₂)
    exact ⟨Q', run', barb_of_outBarb onT' shows''⟩

/-- **Every translation that represents is fully abstract.** For every set `N` of closed names, every
map `t` sending each closed process to a state that represents it, and all closed processes `P` and
`Q`: `P` and `Q` are `N`-barbed bisimilar exactly when `t P` and `t Q` are. Nothing of `t` beyond the
representation is used. -/
theorem fully_abstract_of_represents {N : G [] .nm → Prop} (closedN : ∀ c, N c → Closed c)
    (t : RhoProcess → ByInstantiation.State) (represents : ∀ P, ByInstantiation.Represents (t P) P)
    (P Q : RhoProcess) : SourceBisimilar N P Q ↔ StepBisimilar N (t P) (t Q) := by
  constructor
  · rintro ⟨S, bisimulation, related⟩
    exact ⟨_, step_of_source closedN bisimulation, P, Q, represents P, represents Q, related⟩
  · rintro ⟨T, bisimulation, related⟩
    exact ⟨_, source_of_step closedN bisimulation, t P, t Q, represents P, represents Q, related⟩

/-- **The translation is fully abstract for barbed bisimilarity indexed by a set of names**, as every
representing translation is (`fully_abstract_of_represents`). For every set `N` of closed names and
all closed processes `P` and `Q`: `P` and `Q` are `N`-barbed bisimilar (the 2005 paper's
Definition 4.2, on canonical forms, every output read as a barb) exactly when `encode P` and
`encode Q` are `N`-barbed bisimilar states of the step. -/
theorem fully_abstract {N : G [] .nm → Prop} (closedN : ∀ c, N c → Closed c) (P Q : RhoProcess) :
    SourceBisimilar N P Q ↔ StepBisimilar N (encode P) (encode Q) :=
  fully_abstract_of_represents closedN encode encode_represents P Q

/-- **The single-row translation is fully abstract too**, although it is not homomorphic on parallel
composition (`encodeRow_not_homomorphic`). -/
theorem encodeRow_fully_abstract {N : G [] .nm → Prop} (closedN : ∀ c, N c → Closed c)
    (P Q : RhoProcess) : SourceBisimilar N P Q ↔ StepBisimilar N (encodeRow P) (encodeRow Q) :=
  fully_abstract_of_represents closedN encodeRow encodeRow_represents P Q

/-! ## The equivalence and parallel composition -/

/-- **The tensor preserves co-representation**: two states that represent the SAME process `P`, each
put beside the same state that represents `Q`, are weakly barbed bisimilar (both represent `P | Q`).
This is not congruence: two weakly barbed bisimilar states that represent different processes can be
separated by the tensor with a represented state (`not_congruence_represented`, in `Congruence`). -/
theorem weaklyBarbedBisimilar_tensor {s s' t : ByInstantiation.State} {P Q : RhoProcess}
    (onS : ByInstantiation.Represents s P) (onS' : ByInstantiation.Represents s' P)
    (onT : ByInstantiation.Represents t Q) :
    WeaklyBarbedBisimilar (tensor s t) (tensor s' t) := by
  obtain ⟨left, onS⟩ := onS
  obtain ⟨left', onS'⟩ := onS'
  obtain ⟨right, onT⟩ := onT
  exact weaklyBarbedBisimilar_of_represents (P := par P Q)
    ⟨_, tensor_represents onS onT (fromProcess_par P Q)⟩
    ⟨_, tensor_represents onS' onT (fromProcess_par P Q)⟩

/-- **The translation of a parallel composition is equivalent to the tensor of any states that
represent its parts.** -/
theorem encode_par_equivalent {s t : ByInstantiation.State} {P Q : RhoProcess}
    (onS : ByInstantiation.Represents s P) (onT : ByInstantiation.Represents t Q) :
    WeaklyBarbedBisimilar (encode (par P Q)) (tensor s t) := by
  rw [encode_par]
  obtain ⟨left, onS⟩ := onS
  obtain ⟨right, onT⟩ := onT
  obtain ⟨left', onP⟩ := encode_represents P
  obtain ⟨right', onQ⟩ := encode_represents Q
  exact weaklyBarbedBisimilar_of_represents (P := par P Q)
    ⟨_, tensor_represents onP onQ (fromProcess_par P Q)⟩
    ⟨_, tensor_represents onS onT (fromProcess_par P Q)⟩

/-! ## Controls: the index of names matters -/

/-- `@0!(0)` alone has no reduction. -/
theorem outputNil_stuck (P : RhoProcess) : ¬ rhoLanguageDefGSLT.Step outputNil P := by
  intro step
  obtain ⟨rule, residue, source, _⟩ := (CanonicalReaction.publicStep_iff _ _).mp step
  have inside : input rule.inputChannel rule.body ∈ (CanonicalBag.append rule.redex residue).1 := by
    rw [CanonicalBag.append_inventory]
    exact Multiset.mem_add.mpr (.inl (by simp [CanonicalReaction.GroundComm.redex]))
  rw [← source, fromProcess_primes] at inside
  have meaning : canonicalize (read ByInstantiation.outputZero) =
      output (canonicalize (read ByInstantiation.nameZero)) (canonicalize (read (zeroT : G [] .pr))) :=
    ByInstantiation.canonical_outputT _ _
  change _ ∈ ReflectiveCalculus.primes (read ByInstantiation.outputZero) at inside
  rw [ByInstantiation.primes_of_canonical_prime meaning
    (ByInstantiation.prime_output (by decide) meaning), Multiset.mem_singleton] at inside
  simp [input, output] at inside

/-- `@0!(0)` shows the barb on `@0`. -/
theorem outputNil_barb : Barb outputNil (canonicalize (read ByInstantiation.nameZero)) := by
  refine ⟨canonicalize (read (zeroT : G [] .pr)), ?_⟩
  have meaning : canonicalize (read ByInstantiation.outputZero) =
      output (canonicalize (read ByInstantiation.nameZero)) (canonicalize (read (zeroT : G [] .pr))) :=
    ByInstantiation.canonical_outputT _ _
  rw [fromProcess_primes]
  change output _ _ ∈ ReflectiveCalculus.primes (read ByInstantiation.outputZero)
  rw [ByInstantiation.primes_of_canonical_prime meaning
    (ByInstantiation.prime_output (by decide) meaning)]
  exact Multiset.mem_singleton_self _

/-- `0` has no reduction. -/
theorem nil_stuck (P : RhoProcess) : ¬ rhoLanguageDefGSLT.Step nil P := by
  intro step
  obtain ⟨rule, residue, source, _⟩ := (CanonicalReaction.publicStep_iff _ _).mp step
  have inside : input rule.inputChannel rule.body ∈ (CanonicalBag.append rule.redex residue).1 := by
    rw [CanonicalBag.append_inventory]
    exact Multiset.mem_add.mpr (.inl (by simp [CanonicalReaction.GroundComm.redex]))
  rw [← source, fromProcess_primes] at inside
  change _ ∈ ReflectiveCalculus.primes (.apply "PZero" []) at inside
  rw [show ReflectiveCalculus.primes (.apply "PZero" []) = 0 from ReflectiveCalculus.primes_zero] at inside
  exact Multiset.notMem_zero _ inside

/-- **The index of names matters.** With no observable name, `@0!(0)` and `0` are barbed bisimilar
(both are stuck); with `@0` observable, they are not (the first shows the barb, the second never
does). -/
theorem index_matters :
    SourceBisimilar (fun _ => False) outputNil nil ∧
      ¬ SourceBisimilar (· = ByInstantiation.nameZero) outputNil nil := by
  refine ⟨⟨fun P Q => (P = outputNil ∧ Q = nil) ∨ (P = nil ∧ Q = outputNil), ⟨?_, ?_, ?_⟩,
    .inl ⟨rfl, rfl⟩⟩, ?_⟩
  · rintro P Q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact .inr ⟨rfl, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
  · rintro P Q P' (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) step
    · exact (outputNil_stuck _ step).elim
    · exact (nil_stuck _ step).elim
  · intro P Q c never
    exact never.elim
  · rintro ⟨R, bisimulation, related⟩
    obtain ⟨Q', run, payload, member⟩ :=
      bisimulation.barb ByInstantiation.nameZero rfl related outputNil_barb
    exact nil_not_succeeds ByInstantiation.nameZero ⟨Q', run, payload, member⟩

/-! ## Control: a translation that does not represent -/

/-- The empty state has no move. -/
theorem empty_stuck (s : ByInstantiation.State) : ¬ Moves emptyState s := by
  intro move
  have represented : ByInstantiation.RepresentsBy emptyState nil (fun _ => zeroT) :=
    empty_represents (P := nil) primes_zero
  rcases (ByInstantiation.succ_iff _ _).mp move with comm | admin
  · obtain ⟨P', _, step, _⟩ := ByInstantiation.communication_sound represented comm
    exact nil_stuck _ step
  · obtain ⟨_, _, lighter⟩ := ByInstantiation.administration_decreases represented admin
    simp [ByInstantiation.weightOf, emptyState] at lighter

/-- **Control: the constant translation is not fully abstract.** Sending every process to the empty
state relates `@0!(0)` and `0`, which `@0` separates (`index_matters`). -/
theorem constant_not_fully_abstract :
    ¬ (SourceBisimilar (· = ByInstantiation.nameZero) outputNil nil ↔
      StepBisimilar (· = ByInstantiation.nameZero) emptyState emptyState) := by
  intro same
  apply index_matters.2
  refine same.mpr ⟨fun s t => s = emptyState ∧ t = emptyState, ⟨?_, ?_, ?_⟩, rfl, rfl⟩
  · rintro s t ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro s t s' ⟨rfl, rfl⟩ move
    exact (empty_stuck _ move).elim
  · rintro s t c _ ⟨rfl, rfl⟩ barb
    obtain ⟨o, present, _⟩ := barb
    exact absurd present (Finset.notMem_empty o)

/-! ## The out-barb of the 2005 paper, read literally -/

/-- **The literal out-barb**: an output on the channel whose payload is the drop of a name, `x[v]`. -/
def LiteralBarb (P : RhoProcess) (channel : Pattern) : Prop :=
  ∃ v, output channel (.apply "PDrop" [v]) ∈ (fromProcess P).1

/-- An `N`-barbed bisimulation with the literal out-barb. -/
structure LiteralBisimulation (N : G [] .nm → Prop) (R : RhoProcess → RhoProcess → Prop) : Prop where
  symm : ∀ {P Q}, R P Q → R Q P
  step : ∀ {P Q P'}, R P Q → rhoLanguageDefGSLT.Step P P' →
    ∃ Q', Relation.ReflTransGen rhoLanguageDefGSLT.Step Q Q' ∧ R P' Q'
  barb : ∀ {P Q} (c : G [] .nm), N c → R P Q → LiteralBarb P (canonicalize (read c)) →
    ∃ Q', Relation.ReflTransGen rhoLanguageDefGSLT.Step Q Q' ∧ LiteralBarb Q' (canonicalize (read c))

/-- `N`-barbed bisimilarity with the literal out-barb. -/
def LiteralBisimilar (N : G [] .nm → Prop) (P Q : RhoProcess) : Prop :=
  ∃ R, LiteralBisimulation N R ∧ R P Q

theorem outputNil_bag : (fromProcess outputNil).1 =
    {output (canonicalize (read ByInstantiation.nameZero)) (canonicalize (read (zeroT : G [] .pr)))} := by
  have meaning : canonicalize (read ByInstantiation.outputZero) =
      output (canonicalize (read ByInstantiation.nameZero)) (canonicalize (read (zeroT : G [] .pr))) :=
    ByInstantiation.canonical_outputT _ _
  rw [fromProcess_primes]
  exact ByInstantiation.primes_of_canonical_prime meaning (ByInstantiation.prime_output (by decide) meaning)

/-- **`@0!(0)` shows no literal out-barb**: its payload is not a drop. -/
theorem outputNil_no_literal_barb (c : Pattern) : ¬ LiteralBarb outputNil c := by
  rintro ⟨v, member⟩
  rw [outputNil_bag, Multiset.mem_singleton] at member
  have zero : canonicalize (read (zeroT : G [] .pr)) = .apply "PZero" [] := rfl
  rw [zero] at member
  simp [output] at member

theorem nil_no_literal_barb (c : Pattern) : ¬ LiteralBarb nil c := by
  rintro ⟨v, member⟩
  rw [fromProcess_primes] at member
  change _ ∈ ReflectiveCalculus.primes (.apply "PZero" []) at member
  have empty : ReflectiveCalculus.primes (.apply "PZero" []) = 0 := ReflectiveCalculus.primes_zero
  rw [empty] at member
  exact Multiset.notMem_zero _ member

/-- **Under the literal out-barb, `@0!(0)` and `0` are barbed bisimilar with `@0` observable**: the
separation of `index_matters` rests on reading every output as a barb. -/
theorem index_matters_reading :
    ¬ SourceBisimilar (· = ByInstantiation.nameZero) outputNil nil ∧
      LiteralBisimilar (· = ByInstantiation.nameZero) outputNil nil := by
  refine ⟨index_matters.2, fun P Q => (P = outputNil ∧ Q = nil) ∨ (P = nil ∧ Q = outputNil),
    ⟨?_, ?_, ?_⟩, .inl ⟨rfl, rfl⟩⟩
  · rintro P Q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact .inr ⟨rfl, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
  · rintro P Q P' (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) step
    · exact (outputNil_stuck _ step).elim
    · exact (nil_stuck _ step).elim
  · rintro P Q c _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) barb
    · exact (outputNil_no_literal_barb _ barb).elim
    · exact (nil_no_literal_barb _ barb).elim

/-- `@0!(*@0)`, that is `@0[@0]`. -/
def dropOutput : RhoProcess :=
  ByInstantiation.rowProcess (outputT ByInstantiation.nameZero (dropqT zeroT)) (by decide)

/-- **Positive control: `@0[@0]` shows the literal out-barb on `@0`.** -/
theorem literal_barb_exists :
    LiteralBarb dropOutput (canonicalize (read ByInstantiation.nameZero)) := by
  have meaning : canonicalize (read (outputT ByInstantiation.nameZero (dropqT (zeroT : G [] .pr)))) =
      output (canonicalize (read ByInstantiation.nameZero))
        (canonicalize (read (dropqT (zeroT : G [] .pr)))) :=
    ByInstantiation.canonical_outputT _ _
  refine ⟨.apply "NQuote" [.apply "PZero" []], ?_⟩
  rw [fromProcess_primes]
  change _ ∈ ReflectiveCalculus.primes (read (outputT ByInstantiation.nameZero (dropqT (zeroT : G [] .pr))))
  rw [ByInstantiation.primes_of_canonical_prime meaning
    (ByInstantiation.prime_output (by decide) meaning), Multiset.mem_singleton]
  have dropped : canonicalize (read (dropqT (zeroT : G [] .pr))) =
      .apply "PDrop" [.apply "NQuote" [.apply "PZero" []]] := by decide
  rw [dropped]

#print axioms StepBisimulation.runs
#print axioms step_of_source
#print axioms source_of_step
#print axioms fully_abstract_of_represents
#print axioms fully_abstract
#print axioms encodeRow_fully_abstract
#print axioms empty_stuck
#print axioms constant_not_fully_abstract
#print axioms outputNil_no_literal_barb
#print axioms nil_no_literal_barb
#print axioms index_matters_reading
#print axioms literal_barb_exists
#print axioms weaklyBarbedBisimilar_tensor
#print axioms encode_par_equivalent
#print axioms outputNil_stuck
#print axioms nil_stuck
#print axioms index_matters

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
