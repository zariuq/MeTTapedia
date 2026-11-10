import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderIndependence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Reindex
import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy

/-!
# Races as firings: the labelled step and its linear-time / branching-time readouts

The first-order step admits every firing whose selection is enabled and whose information is
solvable. A **program** says which firings are on offer, and under which label:
`offers ℓ f`. Labels are rules (`offers r f := f.rule = r`), rules with sites
(`offers (r, s) f := f.rule = r ∧ f.selection = s`), or the names of a finite alphabet of firings.

* **The labelled step** (`Moves`): `C` moves to `D` under `ℓ` when an offered firing labelled `ℓ` is
  admitted at `C` and `D` is its result. It is a GSLT on configurations with discrete equations
  (`gslt`) and a Hennessy–Milner system without atoms (`system`).
* **Identity and logic** (`Bisimilar`, `Sat`): interleaving bisimilarity and Hennessy–Milner
  satisfaction are those of `HennessyMilner.System`. Bisimilar configurations satisfy the same
  formulas (`sat_iff_of_bisimilar`); when every label offers finitely many firings, formulas
  characterize bisimilarity (`bisimilar_iff_sat`), by the tree's adequacy theorem
  `HennessyMilner.System.logicallyEquivalent_iff_bisimilar`.
* **Traces** (`HasTrace`, `TraceEquivalent`) are the diamond-only formulas, so bisimilar
  configurations have the same traces (`traceEquivalent_of_bisimilar`).
* **The identity respects the knowledge** (`bisimilar_of_sameUpTo`): configurations with the same
  solutions and the same occurrences are bisimilar.

## Ground firings

A firing is ground (`Ground`) when its patterns are the labels of what it selects, it tells and
checks nothing and has no predicate queries. At a configuration whose equations have equal sides
(`Reflexive`), a ground firing is admitted exactly when its commit is enabled
(`Ground.valid_iff`); its result again has reflexive equations. Admission of ground firings is
therefore decided on occurrences alone, for every substitution action.

## The search of a program (`program`, `alternatives`)

A program given by a finite alphabet restricts the step to the firings it offers (`restrict`).
Listing the admitted members of the alphabet at each state gives the alternatives of the search
(`alternatives`), an enumeration when the alphabet has no repetition (`enumeration`). For ground
alphabets the admitted members at a reflexive configuration are the enabled ones
(`next_map_of_ground`), which the search unfolds into (`unfold_of_nil`, `unfold_of_cons`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.GSLT (GSLT)
open Mettapedia.GSLT.HennessyMilner (Formula System)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO uL

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}

/-! ## The labelled step -/

section Labelled

variable (A : SubstitutionAction T S) (label : O → T) (offers : L → Firing T S O → Prop)

/-- **A labelled move**: an offered firing with label `ℓ` is admitted at `C`, and `D` is its
result. -/
def Moves (C : Configuration T O) (ℓ : L) (D : Configuration T O) : Prop :=
  ∃ f, offers ℓ f ∧ f.Valid A label C ∧ D = f.result label C

/-- The step under a program, as a GSLT on configurations with discrete equations. -/
def gslt : GSLT where
  Term := Configuration T O
  equations := ⟨Eq, eq_equivalence⟩
  rewrites C D := ∃ ℓ, Moves A label offers C ℓ D
  rewrites_resp_left := by
    intro C C' D same step
    exact ⟨D, (same : C = C') ▸ step, rfl⟩
  rewrites_resp_right := by
    intro C D D' step same
    exact (same : D = D') ▸ step

/-- **The labelled step as a Hennessy–Milner system**, without atomic observations. -/
def system : System (gslt A label offers) where
  Atom := PEmpty.{1}
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := L
  act ℓ C D := Moves A label offers C ℓ D
  act_resp_left := by
    intro ℓ C C' D same step
    exact ⟨D, (same : C = C') ▸ step, rfl⟩
  act_resp_right := by
    intro ℓ C D D' step same
    exact (same : D = D') ▸ step

/-- **Interleaving bisimilarity** of configurations under a program. -/
def Bisimilar (C D : Configuration T O) : Prop := (system A label offers).Bisimilar C D

/-- Hennessy–Milner satisfaction, with modalities labelled by the program's labels. -/
def Sat (φ : Formula PEmpty.{1} L) (C : Configuration T O) : Prop := (system A label offers).sat φ C

/-- A trace: a word of labels that some run fires. -/
def HasTrace (w : List L) (C : Configuration T O) : Prop :=
  Sat A label offers (Formula.after w .top) C

/-- **Trace equivalence**: the same traces. -/
def TraceEquivalent (C D : Configuration T O) : Prop :=
  ∀ w : List L, HasTrace A label offers w C ↔ HasTrace A label offers w D

variable {A label offers}

theorem sat_top (C : Configuration T O) : Sat A label offers .top C := trivial

theorem sat_conj {φ ψ : Formula PEmpty.{1} L} {C : Configuration T O} :
    Sat A label offers (.conj φ ψ) C ↔ Sat A label offers φ C ∧ Sat A label offers ψ C := Iff.rfl

theorem sat_neg {φ : Formula PEmpty.{1} L} {C : Configuration T O} :
    Sat A label offers (.neg φ) C ↔ ¬ Sat A label offers φ C := Iff.rfl

theorem sat_dia {ℓ : L} {φ : Formula PEmpty.{1} L} {C : Configuration T O} :
    Sat A label offers (.dia ℓ φ) C ↔ ∃ D, Moves A label offers C ℓ D ∧ Sat A label offers φ D :=
  Iff.rfl

theorem hasTrace_nil (C : Configuration T O) : HasTrace A label offers [] C := trivial

theorem hasTrace_cons {ℓ : L} {w : List L} {C : Configuration T O} :
    HasTrace A label offers (ℓ :: w) C ↔ ∃ D, Moves A label offers C ℓ D ∧ HasTrace A label offers w D :=
  Iff.rfl

/-- **Bisimilar configurations satisfy the same formulas.** -/
theorem sat_iff_of_bisimilar {C D : Configuration T O} (bisimilar : Bisimilar A label offers C D)
    (φ : Formula PEmpty.{1} L) : Sat A label offers φ C ↔ Sat A label offers φ D :=
  (system A label offers).logicallyEquivalent_of_bisimilar bisimilar φ

/-- A formula that holds at one configuration and fails at another separates them. -/
theorem not_bisimilar_of_sat {C D : Configuration T O} {φ : Formula PEmpty.{1} L}
    (holds : Sat A label offers φ C) (fails : ¬ Sat A label offers φ D) :
    ¬ Bisimilar A label offers C D :=
  fun bisimilar => fails ((sat_iff_of_bisimilar bisimilar φ).mp holds)

/-- **Bisimilar configurations have the same traces.** -/
theorem traceEquivalent_of_bisimilar {C D : Configuration T O}
    (bisimilar : Bisimilar A label offers C D) : TraceEquivalent A label offers C D :=
  fun _ => sat_iff_of_bisimilar bisimilar _

variable (A label offers)

/-- A program offering finitely many firings under each label is image-finite. -/
theorem imageFiniteModulo (finite : ∀ ℓ, {f | offers ℓ f}.Finite) :
    (system A label offers).ImageFiniteModulo := by
  intro ℓ C
  refine ⟨(fun f => f.result label C) '' {f | offers ℓ f}, (finite ℓ).image _, ?_⟩
  rintro D ⟨f, offered, _, rfl⟩
  exact ⟨f.result label C, ⟨f, offered, rfl⟩, rfl⟩

/-- **Hennessy–Milner characterization**: when each label offers finitely many firings, two
configurations are bisimilar exactly when they satisfy the same formulas. -/
theorem bisimilar_iff_sat (finite : ∀ ℓ, {f | offers ℓ f}.Finite) (C D : Configuration T O) :
    Bisimilar A label offers C D ↔ ∀ φ : Formula PEmpty.{1} L, (Sat A label offers φ C ↔ Sat A label offers φ D) :=
  ((system A label offers).logicallyEquivalent_iff_bisimilar
    (imageFiniteModulo A label offers finite) C D).symm

/-- **The identity respects the knowledge**: configurations with the same solutions and the same
occurrences are bisimilar, for every program. -/
theorem bisimilar_of_sameUpTo {C D : Configuration T O} (same : SameUpTo A C D) :
    Bisimilar A label offers C D := by
  refine ⟨fun C D => SameUpTo A C D, ⟨?_, ?_, ?_⟩, same⟩
  · rintro C D same ℓ C' ⟨f, offered, valid, rfl⟩
    exact ⟨f.result label D, ⟨f, offered, (Firing.valid_congr A label same).mp valid, rfl⟩,
      f.result_congr A label same⟩
  · rintro C D same ℓ D' ⟨f, offered, valid, rfl⟩
    exact ⟨f.result label C, ⟨f, offered, (Firing.valid_congr A label same).mpr valid, rfl⟩,
      f.result_congr A label same⟩
  · intro _ _ _ atom
    exact atom.elim

end Labelled

/-! ## Ground firings -/

section Ground

/-- Every equation of the store has equal sides. -/
def Reflexive (store : EquationStore T) : Prop := ∀ e ∈ store, e.1 = e.2

theorem reflexive_nil : Reflexive ([] : EquationStore T) := fun _ member => by simp at member

theorem reflexive_append {one two : EquationStore T} (first : Reflexive one) (second : Reflexive two) :
    Reflexive (one ++ two) :=
  fun e member => (List.mem_append.mp member).elim (first e) (second e)

omit [DecidableEq O] in
theorem reflexive_equations (label : O → T) :
    ∀ l : List O, Reflexive (Selection.equations label (l.map label) l)
  | [] => fun _ member => by simp [Selection.equations] at member
  | o :: rest => by
      intro e member
      simp only [Selection.equations, List.map_cons, List.zipWith_cons_cons, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact reflexive_equations label rest e member

/-- **Reflexive stores are consistent** under every substitution action. -/
theorem consistent_of_reflexive (A : SubstitutionAction T S) {store : EquationStore T}
    (refl : Reflexive store) : A.Consistent store :=
  ⟨A.identity, fun e member => by
    show A.E (A.apply A.identity e.1) (A.apply A.identity e.2)
    rw [refl e member]
    exact A.equivalence.refl _⟩

/-- **A ground firing**: its patterns are the labels of what it selects; it tells and checks nothing
and has no predicate queries. -/
structure Ground (label : O → T) (f : Firing T S O) : Prop where
  take : f.rule.take = f.selection.taken.map label
  read : f.rule.read = f.selection.read.map label
  tell : f.rule.tell = []
  checks : f.rule.checks = []
  produce : f.selection.made.map label = f.rule.produce
  queries : f.queries = []
  taken_nodup : f.selection.taken.Nodup
  made_nodup : f.selection.made.Nodup

variable {label : O → T} {f : Firing T S O} {C : Configuration T O}

omit [DecidableEq O] in
theorem Ground.reflexive_problem (ground : Ground label f) (refl : Reflexive C.equations) :
    Reflexive (f.selection.problem label f.rule C) := by
  unfold Selection.problem
  rw [ground.take, ground.read, ground.tell]
  exact reflexive_append (reflexive_append (reflexive_append refl (reflexive_equations label _))
    (reflexive_equations label _)) reflexive_nil

/-- The result of a ground firing has reflexive equations. -/
theorem Ground.reflexive_result (ground : Ground label f) (refl : Reflexive C.equations) :
    Reflexive (f.result label C).equations :=
  ground.reflexive_problem refl

/-- **Admission of a ground firing is enabling of its commit**, at a reflexive configuration and for
every substitution action. -/
theorem Ground.valid_iff (A : SubstitutionAction T S) (ground : Ground label f)
    (refl : Reflexive C.equations) :
    f.Valid A label C ↔ Enabled label C.present (f.selection.commit (T := T)) := by
  constructor
  · intro valid
    exact valid.firing.occurrences
  · intro enabled
    refine ⟨⟨ground.taken_nodup, ground.made_nodup, ?_, ?_, ground.produce, enabled,
      consistent_of_reflexive A (ground.reflexive_problem refl), ?_⟩, ?_⟩
    · rw [ground.take, List.length_map]
    · rw [ground.read, List.length_map]
    · intro check member
      rw [ground.checks] at member
      simp at member
    · intro query member
      rw [ground.queries] at member
      simp at member

end Ground

/-! ## The search of a program -/

section Search

universe uOb uTm uHm uSt uF

variable {Obj : Type uOb} {Tm : Obj → Type uTm} {Hom : Obj → Obj → Type uHm}
  {X : Interface.Frames Tm Hom} {State : Type uSt} {Fir : State → Type uF}

/-- **The step restricted to the firings a program keeps.** Admission, results and knowledge are
those of the step. -/
def restrict (P : Interface.Step X O State Fir) (keep : ∀ s, Fir s → Prop) :
    Interface.Step X O State (fun s => {f : Fir s // keep s f}) :=
  P.reindex (fun f => f.val)

variable (A : SubstitutionAction T S) (label : O → T) (alphabet : List (Firing T S O))

/-- The first-order step under a finite alphabet of firings. -/
abbrev program := restrict (AnnotatedRuns.firstOrder A label).toStep (fun _ f => f ∈ alphabet)

/-- **The alternatives of a program**: the admitted members of its alphabet, in alphabet order. -/
noncomputable def alternatives : Search.Alternatives (program A label alphabet) := by
  classical
  exact ⟨fun C => alphabet.filterMap fun f =>
    if h : f ∈ alphabet ∧ f.Valid A label C then some ⟨⟨f, h.1⟩, h.2⟩ else none⟩

theorem map_filterMap_dite {α : Type*} {β : Type*} (p : α → Prop) [DecidablePred p]
    (g : ∀ a, p a → β) (proj : β → α) (hproj : ∀ a h, proj (g a h) = a) :
    ∀ l : List α, (l.filterMap fun a => if h : p a then some (g a h) else none).map proj =
      l.filter (fun a => decide (p a))
  | [] => rfl
  | a :: l => by
      by_cases h : p a
      · simp [h, hproj, map_filterMap_dite p g proj hproj l]
      · simp [h, map_filterMap_dite p g proj hproj l]

/-- **The alternatives enumerate**: every admitted member is listed, and once when the alphabet has
no repetition. -/
noncomputable def enumeration (nodup : alphabet.Nodup) : Search.Enumeration (program A label alphabet) where
  toAlternatives := alternatives A label alphabet
  complete := by
    classical
    rintro C ⟨f, member⟩ admitted
    show _ ∈ alphabet.filterMap _
    refine List.mem_filterMap.mpr ⟨f, member, ?_⟩
    have both : f ∈ alphabet ∧ f.Valid A label C := ⟨member, admitted⟩
    simp only [dif_pos both]
  nodup := by
    classical
    intro C
    show (alphabet.filterMap _).Nodup
    refine nodup.filterMap ?_
    intro a a' g ha ha'
    by_cases h : a ∈ alphabet ∧ a.Valid A label C
    · by_cases h' : a' ∈ alphabet ∧ a'.Valid A label C
      · simp only [dif_pos h, Option.mem_def, Option.some.injEq] at ha
        simp only [dif_pos h', Option.mem_def, Option.some.injEq] at ha'
        have := congrArg (fun x => x.1.1) (ha.trans ha'.symm)
        exact this
      · simp [dif_neg h'] at ha'
    · simp [dif_neg h] at ha

variable {A label alphabet}

/-- **For ground alphabets the alternatives are the enabled members**, at reflexive configurations. -/
theorem next_map_of_ground (ground : ∀ f ∈ alphabet, Ground label f) {C : Configuration T O}
    (refl : Reflexive C.equations) :
    ((alternatives A label alphabet).next C).map (fun g => g.1.1) =
      alphabet.filter (fun f => decide (Enabled label C.present (f.selection.commit (T := T)))) := by
  classical
  refine (map_filterMap_dite (fun f => f ∈ alphabet ∧ f.Valid A label C)
    (fun f h => (⟨⟨f, h.1⟩, h.2⟩ :
      {g : {f : Firing T S O // f ∈ alphabet} // (program A label alphabet).Admits (s := C) g}))
    (fun g => g.1.1) (fun _ _ => rfl) alphabet).trans ?_
  apply List.filter_congr
  intro f member
  rw [decide_eq_decide]
  exact ⟨fun h => ((ground f member).valid_iff A refl).mp h.2,
    fun h => ⟨member, ((ground f member).valid_iff A refl).mpr h⟩⟩

/-- A configuration with no admitted member is an answer of the search. -/
theorem unfold_of_nil {C : Configuration T O}
    (none : ((alternatives A label alphabet).next C).map (fun g => g.1.1) = []) :
    (alternatives A label alphabet).space.unfold C = [.inl C] :=
  Search.Alternatives.space_unfold_of_halted _ (List.map_eq_nil_iff.mp none)

/-- A configuration with admitted members unfolds into their results. -/
theorem unfold_of_cons {C : Configuration T O} {f : Firing T S O} {fs : List (Firing T S O)}
    (some : ((alternatives A label alphabet).next C).map (fun g => g.1.1) = f :: fs) :
    (alternatives A label alphabet).space.unfold C =
      (f :: fs).map fun g => .inr (g.result label C) := by
  have nonempty : (alternatives A label alphabet).next C ≠ [] := by
    intro empty
    rw [empty] at some
    simp at some
  rw [Search.Alternatives.space_unfold_of_ne _ nonempty, ← some, List.map_map]
  rfl

end Search

#print axioms sat_iff_of_bisimilar
#print axioms not_bisimilar_of_sat
#print axioms traceEquivalent_of_bisimilar
#print axioms imageFiniteModulo
#print axioms bisimilar_iff_sat
#print axioms bisimilar_of_sameUpTo
#print axioms consistent_of_reflexive
#print axioms Ground.reflexive_result
#print axioms Ground.valid_iff
#print axioms enumeration
#print axioms next_map_of_ground
#print axioms unfold_of_nil
#print axioms unfold_of_cons

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
