import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchStep

/-!
# Bounded search over the step, up to alikeness

The concrete steps choose fresh identities, so a state usually admits infinitely many firings, alike
up to renaming. A search explores **representatives** (`Representatives`): finitely many admitted
firings at each state, every admitted firing alike to one of them. They exist wherever each state
has finitely many classes of alike firings and admission is decided
(`Representatives.ofClasses`); every enumeration is one (`Enumeration.toRepresentatives`).

* **Every run is similar to a run of representatives** from every isomorphic start
  (`Representatives.exists_similar`), of the same length (`similar_length`).
* Hence the run space of representatives is **sound** (`Representatives.sound`) and **complete up
  to state classes**: every complete run of the step ends in the class of a reported answer at
  every budget longer than it (`Representatives.mem_run_of_complete`), and a budget finishes
  exactly when every run of the step is shorter than it (`Representatives.status_run_space`).
  Finished, the classes it reports are exactly the classes of the ends of complete runs
  (`Representatives.classes_of_finished`).
* Multiplicities are counted per representative, not per run: alike runs collapse.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search

open Interface

universe uO uT uH uOcc uS uF uI

section Classes

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Interface.Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS}
  {Firing : State → Type uF} {P : Interface.Step X O State Firing}
  (T : Interface.Transport.{uO, uT, uH, uOcc, uS, uF, uI} P)

/-- **Representatives of the admitted firings up to alikeness**: finitely many at each state,
every admitted firing alike to one of them. -/
structure Representatives extends Alternatives P where
  covers : ∀ (s : State) (f : Firing s), P.Admits f → ∃ g ∈ next s, T.Alike f g.1

/-- Alikeness at a state, as a setoid. -/
def alikeSetoid (s : State) : Setoid (Firing s) := ⟨T.Alike, T.alike_equivalence s⟩

/-- **Where each state has finitely many classes of alike firings and admission is decided,
representatives exist.** -/
noncomputable def Representatives.ofClasses [∀ (t : State) (f : Firing t), Decidable (P.Admits f)]
    [∀ s, Fintype (Quotient (alikeSetoid T s))] : Representatives T where
  next s := (Finset.univ : Finset (Quotient (alikeSetoid T s))).toList.filterMap fun q =>
    if h : P.Admits q.out then some ⟨q.out, h⟩ else none
  covers s f admitted := by
    let q : Quotient (alikeSetoid T s) := Quotient.mk _ f
    have alike : T.Alike q.out f := Quotient.mk_out (s := alikeSetoid T s) f
    have outAdmitted : P.Admits q.out := (T.admits_alike alike).mpr admitted
    refine ⟨⟨q.out, outAdmitted⟩, ?_, Transport.Alike.symm alike⟩
    rw [List.mem_filterMap]
    exact ⟨q, Finset.mem_toList.mpr (Finset.mem_univ q), dif_pos outAdmitted⟩

variable {T}

/-- **Every enumeration is a set of representatives.** -/
def Enumeration.toRepresentatives (E : Enumeration P) : Representatives T where
  toAlternatives := E.toAlternatives
  covers s f admitted := ⟨⟨f, admitted⟩, E.complete s f admitted, Transport.Alike.refl f⟩

/-- Similar runs have the same length. -/
theorem similar_length : ∀ {s t : State} {r : P.Run s} {r' : P.Run t},
    T.Similar r r' → r.word.length = r'.word.length
  | _, _, .nil _, .nil _, _ => rfl
  | _, _, .cons _ _ _, .cons _ _ _, h => by
      obtain ⟨_, _, rest⟩ := Transport.similar_cons_cons.mp h
      simp [Interface.Step.Run.word, similar_length rest]
  | _, _, .nil _, .cons _ _ _, h => (Transport.not_similar_nil_cons h).elim
  | _, _, .cons _ _ _, .nil _, h => (Transport.not_similar_cons_nil h).elim

/-- A state in the class of a halted state is halted. -/
theorem halted_of_same {t t' : State} (same : T.Same t t') (halted : Halted P t) : Halted P t' := by
  intro f admitted
  obtain ⟨i⟩ := Transport.Same.symm same
  exact halted (T.move i f) ((T.admits_move i f).mpr admitted)

namespace Representatives

variable (R : Representatives T)

theorem halted_iff (s : State) : Halted P s ↔ R.next s = [] := by
  constructor
  · intro halted
    cases h : R.next s with
    | nil => rfl
    | cons g gs => exact absurd g.2 (halted g.1)
  · intro empty f admitted
    obtain ⟨g, member, _⟩ := R.covers s f admitted
    rw [empty] at member
    exact List.not_mem_nil member

/-- **Every run is similar to a run of representatives**, from every isomorphic start. -/
theorem exists_similar : ∀ {s t : State} (_ : T.Iso s t) (r : P.Run s),
    ∃ (r' : P.Run t) (w : List ℕ), R.Path r' w ∧ T.Similar r r'
  | _, t, i, .nil _ => ⟨.nil t, [], .nil t, Transport.similar_nil_nil.mpr ⟨i⟩⟩
  | _, t, i, .cons f admitted rest => by
      have moved : P.Admits (T.move i f) := (T.admits_move i f).mpr admitted
      obtain ⟨g, member, alike⟩ := R.covers t (T.move i f) moved
      obtain ⟨k, get⟩ := List.mem_iff_getElem?.mp member
      obtain ⟨r', w, path, similar⟩ :=
        exists_similar (T.trans (T.result_move i f admitted) (T.result_alike alike moved g.2)) rest
      exact ⟨.cons g.1 g.2 r', k :: w, .cons get path, Transport.similar_cons_cons.mpr ⟨i, alike, similar⟩⟩

/-- **Soundness**: every reported answer is the end of a complete run of the step. -/
theorem sound {s : State} {p : List ℕ × State} (h : p ∈ R.space.Answers (.inr s)) :
    ∃ r : P.Run s, Halted P r.last ∧ r.last = p.2 := by
  obtain ⟨r, _, _, _, last, empty⟩ := (R.item_answer_iff s p.1 p.2).mp h
  exact ⟨r, by rw [last]; exact (R.halted_iff p.2).mpr empty, last⟩

/-- **Completeness up to classes**: every complete run of the step ends in the class of a reported
answer, at an address one longer than the run. -/
theorem complete {s : State} (r : P.Run s) (halted : Halted P r.last) :
    ∃ p ∈ R.space.Answers (.inr s), T.Same r.last p.2 ∧ p.1.length = r.word.length + 1 := by
  obtain ⟨r', w, path, similar⟩ := R.exists_similar (T.refl s) r
  have same := Transport.Similar.same_last similar
  have halted' := halted_of_same same halted
  refine ⟨(w ++ [0], r'.last), ?_, same, ?_⟩
  · exact (R.item_answer_iff s _ _).mpr ⟨r', w, path, rfl, rfl, (R.halted_iff _).mp halted'⟩
  · rw [List.length_append, path.length_eq, similar_length similar]
    rfl

/-- **At every budget longer than a complete run, its class is reported.** -/
theorem mem_run_of_complete {s : State} {n : ℕ} (r : P.Run s) (halted : Halted P r.last)
    (short : r.word.length < n) :
    ∃ p ∈ (R.space.run n (.inr s)).answers, T.Same r.last p.2 := by
  obtain ⟨p, answer, same, length⟩ := R.complete r halted
  exact ⟨p, (R.space.mem_run n _ p.1 p.2).mpr ⟨answer, by omega⟩, same⟩

/-- **A budget finishes exactly when every run of the step is shorter than it.** -/
theorem status_run_space (n : ℕ) (s : State) :
    (R.space.run n (.inr s)).status = .finished ↔ ∀ r : P.Run s, r.word.length < n := by
  rw [Space.status_run_eq_finished_iff]
  constructor
  · intro shallow r
    obtain ⟨r', w, path, similar⟩ := R.exists_similar (T.refl s) r
    have := shallow w r'.last ((R.item_state_iff s w r'.last).mpr ⟨r', path, rfl⟩)
    rw [path.length_eq] at this
    rw [similar_length similar]
    exact this
  · intro short w t state
    obtain ⟨r, path, _⟩ := (R.item_state_iff s w t).mp state
    rw [path.length_eq]
    exact short r

/-- **Finished, the reported classes are exactly the classes of the ends of complete runs.** -/
theorem classes_of_finished {n : ℕ} {s : State}
    (finished : (R.space.run n (.inr s)).status = .finished) (c : T.StateClass) :
    (∃ p ∈ (R.space.run n (.inr s)).answers, Transport.StateClass.mk T p.2 = c) ↔
      ∃ r : P.Run s, Halted P r.last ∧ Transport.StateClass.mk T r.last = c := by
  constructor
  · rintro ⟨p, member, rfl⟩
    obtain ⟨r, halted, last⟩ := R.sound (R.space.run_sound member)
    exact ⟨r, halted, by rw [last]⟩
  · rintro ⟨r, halted, rfl⟩
    have short := (R.status_run_space n s).mp finished r
    obtain ⟨p, member, same⟩ := R.mem_run_of_complete r halted short
    exact ⟨p, member, ((Transport.StateClass.mk_eq_mk_iff T).mpr same).symm⟩

end Representatives

end Classes

#print axioms Representatives.ofClasses
#print axioms Enumeration.toRepresentatives
#print axioms similar_length
#print axioms halted_of_same
#print axioms Representatives.halted_iff
#print axioms Representatives.exists_similar
#print axioms Representatives.sound
#print axioms Representatives.complete
#print axioms Representatives.mem_run_of_complete
#print axioms Representatives.status_run_space
#print axioms Representatives.classes_of_finished

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search
