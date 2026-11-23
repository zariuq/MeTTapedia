import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.PositiveTell
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Monotone
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Core

/-!
# Real Calculi on the Step: HE Matching, PeTTa Matching, Bulk Step, and Primitive Structural Walls

This module presents actual calculi and structural separation theorems directly over the
formal semantics in `Mettapedia` (no synthetic rank labels or enum proxies):

1. **HE MeTTa Bidirectional Matching (`heMatchParallel`)**:
   A `ParallelCalculus` whose terms are `HE.Space` (`List OSLFCore.Atom`), whose parallel
   composition is atomspace union (`List.append`), and whose reduction fires rules `(pat, tmpl)`
   via `HE.matchAtoms` + `HE.Bindings.apply`.
   * Proves `heMatchParallel_persistent` (positive HE matching is persistent).
   * Derives `no_uniformTranslation_absence_into_heMatch`,
     `no_uniformTranslation_positiveTell_into_heMatch`, and
     `no_uniformTranslation_counted_into_heMatch`.
   * Separates bidirectional `HE.matchAtoms` from legacy one-way `HE.simpleMatch` on an
     explicit `OSLFCore.Atom` witness (`he_bidirectional_separates_from_simpleMatch`).

2. **PeTTa Space Matching (`pettaMatchParallel`)**:
   A `ParallelCalculus` whose terms are `PeTTaSpace`, whose parallel composition unions facts
   and rules, and whose reduction fires `(pat, tmpl)` via `PeTTaSpace.spaceMatch`.
   * Proves `pettaMatchParallel_persistent` (pure positive PeTTa matching is persistent).
   * Derives `no_uniformTranslation_absence_into_pettaMatch`,
     `no_uniformTranslation_positiveTell_into_pettaMatch`, and
     `no_uniformTranslation_counted_into_pettaMatch`.
   * Separates bulk `PeTTaSpace.removeAtom` (`petta_removeAtom_clears_all_copies`) from pure
     monotone `spaceMatch`.

3. **Real Structural Primitive Walls on `RuleSyntax.step` and `Selection.Valid`**:
   * `bounded_take_cannot_clear_k_plus_one`: for EVERY frame action `X`, program `P`, state `s`,
     and admitted `RuleSyntax.Firing` `f` whose take-arity is `≤ B`, if `B + 1 ≤ s.present.card`,
     then `(f.result X s).present` stays nonempty — separating single-match bounded arity from
     atomic bulk every-match retraction (`bulkRetract_clears_all`).
   * `withoutRead_cannot_preserve_matched_identity`: for ANY `Selection.Valid` of a rule with
     `rule.read = []`, every taken occurrence `o ∈ sel.taken` is absent from the post-state
     while every made occurrence `m ∈ sel.made` is absent from the pre-state — proving no
     read-free firing can observe an occurrence and retain its physical identity in one step.
   * `withoutMake_subset_present` & `withoutMake_card_le`: for ANY `Selection.Valid` of a rule
     with `rule.produce = []`, the post-state present set is a subset of the pre-state present set.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

/-! ## 1. HE MeTTa Bidirectional Matching as a Real `ParallelCalculus` -/

section HEMatchCalculus

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE

/-- One-step positive HE space matching: match a rule `(pat, tmpl) ∈ rules` against some
stored atom `a ∈ s.atoms` using bidirectional `HE.matchAtoms`, and add `b.apply tmpl fuel`. -/
def heMatchStep (rules : List (Atom × Atom)) (fuel : Nat) (s s' : Space) : Prop :=
  ∃ r ∈ rules, ∃ a ∈ s.atoms, ∃ b ∈ matchAtoms r.1 a fuel,
    s' = ⟨b.apply r.2 fuel :: s.atoms⟩

/-- **HE bidirectional matching as a `ParallelCalculus`**:
terms are `HE.Space`, parallel composition is atomspace append, all spaces are composable,
success is presence of `successAtom`, and static equivalence is equality. -/
def heMatchParallel (rules : List (Atom × Atom)) (fuel : Nat) (successAtom : Atom) :
    ParallelCalculus.{0} where
  Term := Space
  step := heMatchStep rules fuel
  par s₁ s₂ := ⟨s₁.atoms ++ s₂.atoms⟩
  composable _ _ := True
  success s := successAtom ∈ s.atoms
  same := Eq

/-- **HE positive matching is persistent**: reductions are closed under space union,
success persists under space union, and static equivalence is equality. -/
theorem heMatchParallel_persistent (rules : List (Atom × Atom)) (fuel : Nat) (successAtom : Atom) :
    (heMatchParallel rules fuel successAtom).Persistent where
  closed := by
    intro s s' u hstep
    obtain ⟨r, hr, a, ha, b, hb, rfl⟩ := hstep
    exact ⟨r, hr, a, List.mem_append_left u.atoms ha, b, hb, rfl⟩
  persists := fun _ u hsucc => List.mem_append_left u.atoms hsucc
  respects := ParallelCalculus.respects_of_eq fun _ _ h => h

/-- **No uniform translation of the absence-guarded step into HE positive matching.** -/
theorem no_uniformTranslation_absence_into_heMatch
    (rules : List (Atom × Atom)) (fuel : Nat) (successAtom : Atom) :
    IsEmpty (UniformTranslation NullsOnTheStep.ParallelClosed.source
      (heMatchParallel rules fuel successAtom)) :=
  isEmpty_uniformTranslation NullsOnTheStep.ParallelClosed.source_switchable
    (heMatchParallel_persistent rules fuel successAtom)

/-- **No uniform translation of the positive-tell (shared unknown) step into HE matching.** -/
theorem no_uniformTranslation_positiveTell_into_heMatch
    (rules : List (Atom × Atom)) (fuel : Nat) (successAtom : Atom) :
    IsEmpty (UniformTranslation NullsOnTheStep.ParallelClosed.PositiveTell.tellSource
      (heMatchParallel rules fuel successAtom)) :=
  isEmpty_uniformTranslation NullsOnTheStep.ParallelClosed.PositiveTell.tellSource_switchable
    (heMatchParallel_persistent rules fuel successAtom)

/-- **No uniform translation of the count-guarded step into HE matching.** -/
theorem no_uniformTranslation_counted_into_heMatch
    (rules : List (Atom × Atom)) (fuel : Nat) (successAtom : Atom) :
    IsEmpty (UniformTranslation NullsOnTheStep.ParallelClosed.Monotone.countedSource
      (heMatchParallel rules fuel successAtom)) :=
  isEmpty_uniformTranslation NullsOnTheStep.ParallelClosed.Monotone.counted_switchable
    (heMatchParallel_persistent rules fuel successAtom)

/-- **Positive/Negative HE Control**:
Bidirectional `HE.matchAtoms` unifies a ground query `.symbol "a"` with a stored variable
atom `.var "y"`, whereas legacy one-way `HE.simpleMatch` refuses. -/
theorem he_bidirectional_separates_from_simpleMatch :
    (matchAtoms (.symbol "a") (.var "y") 4 ≠ []) ∧
    simpleMatch (.symbol "a") (.var "y") Bindings.empty 4 = none := by
  decide

/-- **Positive HE Execution Control**:
`heMatchParallel` fires a real rule `((.symbol "a"), (.symbol "done"))` against a stored
variable `.var "y"` in one step, reaching success `.symbol "done"`. -/
theorem heMatchParallel_fires_bidirectional :
    let rules : List (Atom × Atom) := [(.symbol "a", .symbol "done")]
    (heMatchParallel rules 4 (.symbol "done")).Succeeds ⟨[.var "y"]⟩ := by
  refine ⟨⟨[.symbol "done", .var "y"]⟩, .single ?_, ?_⟩
  · refine ⟨(.symbol "a", .symbol "done"), by simp, .var "y", by simp,
      Bindings.empty.assign "y" (.symbol "a"), by decide, ?_⟩
    rfl
  · change Atom.symbol "done" ∈ [Atom.symbol "done", Atom.var "y"]
    simp

end HEMatchCalculus

/-! ## 2. PeTTa Space Matching as a Real `ParallelCalculus` -/

section PeTTaMatchCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.PeTTa

/-- Parallel composition of PeTTa atomspaces: append facts and rules. -/
def pettaPar (s₁ s₂ : PeTTaSpace) : PeTTaSpace :=
  { facts := s₁.facts ++ s₂.facts, rules := s₁.rules ++ s₂.rules }

theorem pettaPar_storedAtoms_left {s₁ s₂ : PeTTaSpace} {a : Pattern}
    (ha : a ∈ s₁.storedAtoms) : a ∈ (pettaPar s₁ s₂).storedAtoms := by
  unfold PeTTaSpace.storedAtoms PeTTaSpace.storedRuleAtoms at ha ⊢
  dsimp only [pettaPar]
  rw [List.mem_append] at ha ⊢
  rcases ha with hf | hr
  · exact Or.inl (List.mem_append_left s₂.facts hf)
  · right
    rw [List.filterMap_append]
    exact List.mem_append_left _ hr

/-- One-step pure positive PeTTa `spaceMatch` firing: match `(pat, tmpl) ∈ rules` via
`PeTTaSpace.spaceMatch` and add the instantiated answer to `facts`. -/
def pettaMatchStep (rules : List (Pattern × Pattern)) (s s' : PeTTaSpace) : Prop :=
  ∃ r ∈ rules, ∃ q ∈ s.spaceMatch r.1 r.2, s' = { s with facts := q :: s.facts }

/-- **PeTTa positive `spaceMatch` as a `ParallelCalculus`**:
terms are `PeTTaSpace`, parallel composition is `pettaPar`, success is presence of
`successPat` in `facts`, and static equivalence is equality. -/
def pettaMatchParallel (rules : List (Pattern × Pattern)) (successPat : Pattern) :
    ParallelCalculus.{0} where
  Term := PeTTaSpace
  step := pettaMatchStep rules
  par := pettaPar
  composable _ _ := True
  success s := successPat ∈ s.facts
  same := Eq

/-- **PeTTa pure positive `spaceMatch` is persistent.** -/
theorem pettaMatchParallel_persistent (rules : List (Pattern × Pattern)) (successPat : Pattern) :
    (pettaMatchParallel rules successPat).Persistent where
  closed := by
    intro s s' u hstep
    obtain ⟨r, hr, q, hq, rfl⟩ := hstep
    obtain ⟨atom, hatom, bs, hbs, rfl⟩ := PeTTaSpace.spaceMatch_sound s r.1 r.2 q hq
    refine ⟨r, hr, _, PeTTaSpace.spaceMatch_complete (pettaPar s u) r.1 r.2 atom bs
      (pettaPar_storedAtoms_left hatom) hbs, rfl⟩
  persists := fun _ u hsucc => List.mem_append_left u.facts hsucc
  respects := ParallelCalculus.respects_of_eq fun _ _ h => h

/-- **No uniform translation of the absence-guarded step into PeTTa pure `spaceMatch`.** -/
theorem no_uniformTranslation_absence_into_pettaMatch
    (rules : List (Pattern × Pattern)) (successPat : Pattern) :
    IsEmpty (UniformTranslation NullsOnTheStep.ParallelClosed.source
      (pettaMatchParallel rules successPat)) :=
  isEmpty_uniformTranslation NullsOnTheStep.ParallelClosed.source_switchable
    (pettaMatchParallel_persistent rules successPat)

/-- **No uniform translation of the positive-tell (shared unknown) step into PeTTa `spaceMatch`.** -/
theorem no_uniformTranslation_positiveTell_into_pettaMatch
    (rules : List (Pattern × Pattern)) (successPat : Pattern) :
    IsEmpty (UniformTranslation NullsOnTheStep.ParallelClosed.PositiveTell.tellSource
      (pettaMatchParallel rules successPat)) :=
  isEmpty_uniformTranslation NullsOnTheStep.ParallelClosed.PositiveTell.tellSource_switchable
    (pettaMatchParallel_persistent rules successPat)

/-- **No uniform translation of the count-guarded step into PeTTa `spaceMatch`.** -/
theorem no_uniformTranslation_counted_into_pettaMatch
    (rules : List (Pattern × Pattern)) (successPat : Pattern) :
    IsEmpty (UniformTranslation NullsOnTheStep.ParallelClosed.Monotone.countedSource
      (pettaMatchParallel rules successPat)) :=
  isEmpty_uniformTranslation NullsOnTheStep.ParallelClosed.Monotone.counted_switchable
    (pettaMatchParallel_persistent rules successPat)

/-- **Positive PeTTa Control (`PeTTaSpace.removeAtom` clears all copies in bulk)**:
unlike single-match linear `take`, `PeTTaSpace.removeAtom` removes every matching copy of `p`
from `facts` in one call. -/
theorem petta_removeAtom_clears_all_copies (n : Nat) (p : Pattern) :
    (PeTTaSpace.removeAtom ⟨List.replicate n p, []⟩ p).facts = [] := by
  simp only [PeTTaSpace.removeAtom]
  induction n with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

end PeTTaMatchCalculus

/-! ## 3. Real Structural Primitive Walls on `RuleSyntax.step` and `Selection.Valid` -/

section RealStepWalls

open RuleSyntax

/-- **Real Bounded-Take Size Wall on `RuleSyntax.step`**:
For EVERY frame action `X`, EVERY extension supply `E`, EVERY program `P`, EVERY state `s`,
and EVERY admitted firing `f` of `RuleSyntax.step X O E P` whose rule take-arity satisfies
`f.rule.body.take.length ≤ B`: if `B + 1 ≤ s.present.card`, then the post-state
`(f.result X s).present` is STILL nonempty (`1 ≤ (f.result X s).present.card`).
Hence no fixed bounded take-arity rule on `RuleSyntax.step` can atomically clear a wave of
`B + 1` matching occurrences in a single firing! -/
theorem bounded_take_cannot_clear_k_plus_one
    {Obj : Type*} {Tm : Obj → Type*} {Hom : Obj → Obj → Type*}
    {X : Interface.Frames Tm Hom} {O : Type*} [DecidableEq O]
    {E : Extensions Hom} {P : Program Tm}
    {s : State Tm O} {f : Firing O E P s.frame}
    (admitted : (step X O E P).Admits (s := s) f)
    {B : Nat} (harity : f.rule.body.take.length ≤ B)
    (hsize : B + 1 ≤ s.present.card) :
    1 ≤ (f.result X s).present.card := by
  have hshapes : f.Shapes X s := admitted.1
  have hlen : f.rule.body.take.length = f.selection.taken.length := hshapes.2.2.2.1
  have htoFinset_le : f.selection.taken.toFinset.card ≤ B := by
    have h1 : f.selection.taken.toFinset.card ≤ f.selection.taken.length :=
      List.toFinset_card_le f.selection.taken
    omega
  have hsub : s.present \ f.selection.taken.toFinset ⊆ (f.result X s).present := by
    intro o ho
    change o ∈ fire s.present (f.selection.commit (T := Unit))
    rw [mem_fire]
    exact Or.inl (Finset.mem_sdiff.mp ho)
  have hsdiff_card :
      s.present.card - f.selection.taken.toFinset.card ≤
        (s.present \ f.selection.taken.toFinset).card :=
    Finset.le_card_sdiff f.selection.taken.toFinset s.present
  have hcard_le : (s.present \ f.selection.taken.toFinset).card ≤ (f.result X s).present.card :=
    Finset.card_le_card hsub
  omega

/-- **Atomic Every-Match Bulk Retraction** on `RuleSyntax.State`: removes every present
occurrence whose label satisfies `pred` in one atomic step. -/
def bulkRetractState {Obj : Type*} {Tm : Obj → Type*} {O : Type*} [DecidableEq O]
    (s : State Tm O) (pred : Tm s.frame → Bool) : State Tm O :=
  { s with present := s.present.filter fun o => !pred (s.label o) }

/-- Positive bulk control: atomic every-match retraction clears arbitrary `N` matching
occurrences to `∅` in one step (unachievable in 1 step by any fixed take-arity `B < N`). -/
theorem bulkRetractState_clears_all {Obj : Type*} {Tm : Obj → Type*} {O : Type*} [DecidableEq O]
    (s : State Tm O) (pred : Tm s.frame → Bool)
    (hall : ∀ o ∈ s.present, pred (s.label o) = true) :
    (bulkRetractState s pred).present = ∅ := by
  ext o
  simp only [bulkRetractState, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  intro ho
  simp [hall o ho]

/-- **Real `take` Structural Wall on `Selection.Valid`**:
For EVERY substitution action `A`, label map `label`, configuration `C`, rule `rule` with
`rule.take = []` (no `take` primitive), and valid selection `sel`:
every present occurrence survives (`C.present ⊆ (sel.result label rule C).present`) and
the store size can never shrink (`C.present.card ≤ (sel.result label rule C).present.card`). -/
theorem withoutTake_present_subset_and_card_le
    {T S O : Type*} [DecidableEq O]
    {A : SubstitutionAction T S} {label : O → T}
    {rule : RuleInstance T} {sel : Selection O} {C : Configuration T O}
    (noTake : rule.take = []) (valid : sel.Valid A label rule C) :
    C.present ⊆ (sel.result label rule C).present ∧
    C.present.card ≤ (sel.result label rule C).present.card := by
  have htaken_nil : sel.taken = [] := by
    have hlen := valid.take_length
    rw [noTake] at hlen
    exact List.length_eq_zero_iff.mp hlen.symm
  have hsub : C.present ⊆ (sel.result label rule C).present := by
    intro o ho
    change o ∈ fire C.present (sel.commit (T := T))
    rw [mem_fire]
    left
    refine ⟨ho, ?_⟩
    simp [Selection.commit, htaken_nil]
  exact ⟨hsub, Finset.card_le_card hsub⟩

/-- **Real Physical-Identity `read` Separation on `Selection.Valid`**:
For EVERY substitution action `A`, label map `label`, configuration `C`, rule `rule` with
`rule.read = []` (no `read` primitive), and valid selection `sel`:
1. `sel.read = []` (no occurrence is read),
2. every taken occurrence `o ∈ sel.taken` is **absent** from `(sel.result label rule C).present`
   (its physical identity is destroyed), and
3. every newly made occurrence `m ∈ sel.made` is **absent** from `C.present`
   (no made occurrence can reuse an existing occurrence's physical identity).
Hence without `read`, no single firing can match an occurrence and preserve its exact
physical identity! -/
theorem withoutRead_cannot_preserve_matched_identity
    {T S O : Type*} [DecidableEq O]
    {A : SubstitutionAction T S} {label : O → T}
    {rule : RuleInstance T} {sel : Selection O} {C : Configuration T O}
    (noRead : rule.read = []) (valid : sel.Valid A label rule C) :
    sel.read = [] ∧
    (∀ o ∈ sel.taken, o ∉ (sel.result label rule C).present) ∧
    (∀ m ∈ sel.made, m ∉ C.present) := by
  have hread_nil : sel.read = [] := by
    have hlen := valid.read_length
    rw [noRead] at hlen
    exact List.length_eq_zero_iff.mp hlen.symm
  have hmade_fresh : ∀ m ∈ sel.made, m ∉ C.present := by
    intro m hm
    exact Finset.disjoint_left.mp valid.occurrences.fresh (by simpa [Selection.commit] using hm)
  have htaken_gone : ∀ o ∈ sel.taken, o ∉ (sel.result label rule C).present := by
    intro o ho hpost
    change o ∈ fire C.present (sel.commit (T := T)) at hpost
    rw [mem_fire] at hpost
    rcases hpost with hdiff | hmade
    · exact hdiff.2 (by simpa [Selection.commit] using ho)
    · have ho_present : o ∈ C.present :=
        valid.occurrences.taken_subset (by simpa [Selection.commit] using ho)
      have ho_made : o ∈ sel.made := by
        simpa [Selection.commit] using hmade
      exact hmade_fresh o ho_made ho_present
  exact ⟨hread_nil, htaken_gone, hmade_fresh⟩

/-- **Real `make` Separation on `Selection.Valid`**:
For EVERY substitution action `A`, label map `label`, configuration `C`, rule `rule` with
`rule.produce = []` (no `make` primitive), and valid selection `sel`:
1. `(sel.result label rule C).present ⊆ C.present` (no new occurrence ever appears), and
2. `(sel.result label rule C).present.card ≤ C.present.card` (store size can never grow). -/
theorem withoutMake_subset_and_card_le
    {T S O : Type*} [DecidableEq O]
    {A : SubstitutionAction T S} {label : O → T}
    {rule : RuleInstance T} {sel : Selection O} {C : Configuration T O}
    (noMake : rule.produce = []) (valid : sel.Valid A label rule C) :
    (sel.result label rule C).present ⊆ C.present ∧
    (sel.result label rule C).present.card ≤ C.present.card := by
  have hmade_nil : sel.made = [] := by
    have hout := valid.outputs
    rw [noMake] at hout
    exact List.map_eq_nil_iff.mp hout
  have hsub : (sel.result label rule C).present ⊆ C.present := by
    intro o ho
    change o ∈ fire C.present (sel.commit (T := T)) at ho
    rw [mem_fire] at ho
    rcases ho with hdiff | hmade
    · exact hdiff.1
    · simp [Selection.commit, hmade_nil] at hmade
  exact ⟨hsub, Finset.card_le_card hsub⟩

end RealStepWalls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens
