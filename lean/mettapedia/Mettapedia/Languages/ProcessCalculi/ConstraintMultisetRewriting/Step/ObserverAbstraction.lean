import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObserverFirstOrder

/-!
# Equivalence relative to a record, and which probes it needs

Pointwise equivalence (`Observation.PointwiseEquivalent`) fixes the escaped identities. Relative to a
record, the renamings are its automorphisms instead (`RecordEquivalent`): the same solutions; every
identity that each automorphism fixes is present at both or at neither; and at every solution an
automorphism of the record that keeps the labels up to that solution carries the present
occurrences of one configuration to the other.

* **Respect** (`RecordEquivalent.observes`): every probe modulo the knowledge that the record supports
  observes the same at equivalent configurations. So does every tally inside a set of identities that
  the automorphisms of the record carry to itself (`RecordEquivalent.observesWithin`).
* **Full abstraction for one sighted set** (`recordEquivalent_sighting_iff`): relative to the record
  of one sighted set `W`, two configurations are equivalent exactly when every probe modulo the
  knowledge that the record supports, and every tally inside `W`, observe the same at both. The
  renaming is built inside `W` and outside it separately, each moving only identities on its side.
* **Traces refine it** (`renaming_traceEquiv_recordEquivalent`): trace-equivalent runs of the
  escape-relative transport that renames occurrences end in configurations equivalent relative to the
  start's record.
* **The probes modulo the knowledge are not enough for sighted sets**
  (`AbstractionControls.supported_not_abstract`). After sighting `{5, 6}`, the configurations holding
  `{5, 7}` and `{7, 8}`, all labelled alike, agree on every probe the record supports, and are not
  equivalent relative to it: no automorphism carries `5` outside the sighted set. A tally inside the
  sighted set separates them. For records of references the probes modulo the knowledge suffice
  (`Observation.pointwiseEquivalent_iff_supported`); for sighted sets the probe class must also
  count inside the recorded sets.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

open AnnotatedRuns
open MeTTaCalculus.OccurrenceCommits (regionOf)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO}

section RecordRelative

variable (A : SubstitutionAction T S) (label : O → T) (r : Record O)

/-- **Equivalence relative to a record**: the same solutions; every identity that each automorphism of
the record fixes is present at both configurations or at neither; and at every solution, an
automorphism of the record that keeps the labels up to that solution carries the present occurrences
of the first configuration to those of the second. -/
def RecordEquivalent (C D : Configuration T O) : Prop :=
  A.Equivalent C.equations D.equations ∧
    (∀ o, (∀ π ∈ Record.automorphisms r, π o = o) → (o ∈ C.present ↔ o ∈ D.present)) ∧
    ∀ σ, A.Models σ C.equations → ∃ π ∈ Record.automorphisms r,
      (∀ o, A.Solves σ (label (π o), label o)) ∧ C.present.map π.toEmbedding = D.present

/-- **A tally inside a set of identities**: the number of present rows of a region that lie in the
set, at every solution, as a function of the solution. -/
def ObservesWithin (region : Region A) (W : Finset O) (number : S → ℕ) [DecidableEq O]
    (C : Configuration T O) : Prop :=
  A.Entails C.equations fun σ => (regionOf label C.present (region.test σ) ∩ W).card = number σ

variable {A label r}

/-- Equivalent configurations entail the same properties of their present occurrences, when each
property is kept by the automorphisms of the record that keep the labels up to the solution. -/
theorem RecordEquivalent.entails_iff {C D : Configuration T O} (h : RecordEquivalent A label r C D)
    {property : S → Finset O → Prop}
    (moved : ∀ σ, A.Models σ C.equations → ∀ π : O ≃ O, π ∈ Record.automorphisms r →
      (∀ o, A.Solves σ (label (π o), label o)) →
        (property σ (C.present.map π.toEmbedding) ↔ property σ C.present)) :
    (A.Entails C.equations fun σ => property σ C.present) ↔
      (A.Entails D.equations fun σ => property σ D.present) := by
  obtain ⟨equivalent, -, each⟩ := h
  refine forall_congr' fun σ => ⟨fun asked solvedD => ?_, fun asked solvedC => ?_⟩
  · have solvedC := (equivalent σ).mpr solvedD
    obtain ⟨π, aut, keeps, onto⟩ := each σ solvedC
    rw [← onto]
    exact (moved σ solvedC π aut keeps).mpr (asked solvedC)
  · obtain ⟨π, aut, keeps, onto⟩ := each σ solvedC
    have there := asked ((equivalent σ).mp solvedC)
    rw [← onto] at there
    exact (moved σ solvedC π aut keeps).mp there

/-- **Respect**: every probe modulo the knowledge that the record supports observes the same at
configurations equivalent relative to the record. -/
theorem RecordEquivalent.observes {C D : Configuration T O} (h : RecordEquivalent A label r C D)
    {p : ModuloProbe A O} (supported : p.Supported r) : p.Observes label C ↔ p.Observes label D := by
  cases p with
  | present reference =>
      exact h.2.1 reference fun π aut => ModuloProbe.present.inj (supported π aut)
  | check guard =>
      exact h.entails_iff (property := fun σ P => guard.Holds A σ label P)
        fun σ _ π _ keeps => holds_map_upTo keeps C.present guard
  | ask region seen =>
      refine h.entails_iff (property := fun σ P => regionOf label P (region.test σ) = seen)
        fun σ _ π aut keeps => ?_
      have fixed : seen.map π.toEmbedding = seen := (ModuloProbe.ask.inj (supported π aut)).2
      show regionOf label (C.present.map π.toEmbedding) (region.test σ) = seen ↔
        regionOf label C.present (region.test σ) = seen
      rw [regionOf_map_upTo keeps region C.present]
      constructor
      · intro moved
        exact Finset.map_injective π.toEmbedding (moved.trans fixed.symm)
      · intro unmoved
        rw [unmoved, fixed]
  | tally region number =>
      refine h.entails_iff (property := fun σ P => (regionOf label P (region.test σ)).card = number σ)
        fun σ _ π _ keeps => ?_
      show (regionOf label (C.present.map π.toEmbedding) (region.test σ)).card = number σ ↔
        (regionOf label C.present (region.test σ)).card = number σ
      rw [regionOf_map_upTo keeps region C.present, Finset.card_map]

/-- **Respect for tallies inside a set the automorphisms keep.** -/
theorem RecordEquivalent.observesWithin [DecidableEq O] {C D : Configuration T O}
    (h : RecordEquivalent A label r C D) (region : Region A) {W : Finset O}
    (kept : ∀ π ∈ Record.automorphisms r, W.map π.toEmbedding = W) (number : S → ℕ) :
    ObservesWithin A label region W number C ↔ ObservesWithin A label region W number D := by
  refine h.entails_iff (property := fun σ P => (regionOf label P (region.test σ) ∩ W).card = number σ)
    fun σ _ π aut keeps => ?_
  show (regionOf label (C.present.map π.toEmbedding) (region.test σ) ∩ W).card = number σ ↔
    (regionOf label C.present (region.test σ) ∩ W).card = number σ
  rw [regionOf_map_upTo keeps region C.present]
  conv_lhs => rw [← kept π aut, ← Finset.map_inter, Finset.card_map]

end RecordRelative

/-! ## Full abstraction for one sighted set -/

section OneSighting

variable {A : SubstitutionAction T S} {label : O → T} [DecidableEq O]

omit [DecidableEq O] in
/-- The automorphisms of the record of one sighted set are the renamings that carry the set to
itself. -/
theorem sighting_rename_eq_iff {π : O ≃ O} {W : Finset O} :
    Record.rename π [Record.sighting W] = [Record.sighting W] ↔ W.map π.toEmbedding = W := by
  simp only [Record.rename, List.map_cons, List.map_nil, List.cons.injEq, and_true,
    Record.renameEntry_sighting]
  exact (Finset.map_injective Record.single).eq_iff

omit [DecidableEq O] in
/-- A renaming that moves only identities of a set carries the set to itself. -/
theorem map_eq_self_of_support {π : O ≃ O} {W : Finset O} (outside : ∀ o, o ∉ W → π o = o) :
    W.map π.toEmbedding = W := by
  have sub : W.map π.toEmbedding ⊆ W := by
    intro o member
    obtain ⟨a, inside, rfl⟩ := Finset.mem_map.mp member
    by_contra out
    have back : π (π a) = π a := outside _ out
    have same : π a = a := π.injective back
    exact out (by simpa [same] using inside)
  exact Finset.eq_of_subset_of_card_le sub (by rw [Finset.card_map])

theorem regionOf_inter (P W : Finset O) (region : T → Bool) :
    regionOf label (P ∩ W) region = regionOf label P region ∩ W := by
  ext o
  simp only [regionOf, Finset.mem_filter, Finset.mem_inter]
  tauto

theorem regionOf_sdiff (P W : Finset O) (region : T → Bool) :
    regionOf label (P \ W) region = regionOf label P region \ W := by
  ext o
  simp only [regionOf, Finset.mem_filter, Finset.mem_sdiff]
  tauto

/-- **Full abstraction for one sighted set**: two configurations are equivalent relative to the
record of the sighted set `W` exactly when every probe modulo the knowledge that the record supports,
and every tally inside `W`, observe the same at both. -/
theorem recordEquivalent_sighting_iff (W : Finset O) (C D : Configuration T O) :
    RecordEquivalent A label [Record.sighting W] C D ↔
      (∀ p : ModuloProbe A O, p.Supported [Record.sighting W] → (p.Observes label C ↔ p.Observes label D)) ∧
        ∀ (region : Region A) (number : S → ℕ),
          ObservesWithin A label region W number C ↔ ObservesWithin A label region W number D := by
  constructor
  · intro h
    exact ⟨fun p supported => h.observes supported, fun region number =>
      h.observesWithin region (fun π aut => sighting_rename_eq_iff.mp aut) number⟩
  · rintro ⟨agree, within⟩
    have equation : ∀ e : Equation T,
        (ModuloProbe.check (Check.equal e.1 e.2) : ModuloProbe A O).Supported [Record.sighting W] :=
      fun _ _ _ => rfl
    have equivalent : A.Equivalent C.equations D.equations := by
      intro σ
      constructor
      · intro solved e member
        have atD : (ModuloProbe.check (Check.equal e.1 e.2) : ModuloProbe A O).Observes label D :=
          fun τ solvedτ => solvedτ e member
        exact (agree _ (equation e)).mpr atD σ solved
      · intro solved e member
        have atC : (ModuloProbe.check (Check.equal e.1 e.2) : ModuloProbe A O).Observes label C :=
          fun τ solvedτ => solvedτ e member
        exact (agree _ (equation e)).mp atC σ solved
    refine ⟨equivalent, fun o fixed => agree (.present o) fun π aut =>
      congrArg ModuloProbe.present (fixed π aut), fun σ solved => ?_⟩
    classical
    have solvedD := (equivalent σ).mp solved
    have counts : ∀ t₀ : T,
        (regionOf label C.present ((classRegion A t₀).test σ) ∩ W).card =
            (regionOf label D.present ((classRegion A t₀).test σ) ∩ W).card ∧
          (regionOf label C.present ((classRegion A t₀).test σ)).card =
            (regionOf label D.present ((classRegion A t₀).test σ)).card := by
      intro t₀
      constructor
      · have atC : ObservesWithin A label (classRegion A t₀) W
            (fun τ => (regionOf label C.present ((classRegion A t₀).test τ) ∩ W).card) C := fun _ _ => rfl
        exact ((within _ _).mp atC σ solvedD).symm
      · have atC : (ModuloProbe.tally (classRegion A t₀)
            fun τ => (regionOf label C.present ((classRegion A t₀).test τ)).card).Observes label C :=
          fun _ _ => rfl
        exact ((agree _ fun _ _ => rfl).mp atC σ solvedD).symm
    have inside : (C.present ∩ W).val.map (fun o => Quotient.mk (solutionSetoid A σ) (label o)) =
        (D.present ∩ W).val.map (fun o => Quotient.mk (solutionSetoid A σ) (label o)) := by
      refine Multiset.ext.mpr fun c => ?_
      obtain ⟨t₀, rfl⟩ := Quotient.exists_rep c
      rw [← card_classRegion, ← card_classRegion, regionOf_inter, regionOf_inter]
      exact (counts t₀).1
    have outside : (C.present \ W).val.map (fun o => Quotient.mk (solutionSetoid A σ) (label o)) =
        (D.present \ W).val.map (fun o => Quotient.mk (solutionSetoid A σ) (label o)) := by
      refine Multiset.ext.mpr fun c => ?_
      obtain ⟨t₀, rfl⟩ := Quotient.exists_rep c
      rw [← card_classRegion, ← card_classRegion, regionOf_sdiff, regionOf_sdiff]
      have splitC := Finset.card_sdiff_add_card_inter (regionOf label C.present ((classRegion A t₀).test σ)) W
      have splitD := Finset.card_sdiff_add_card_inter (regionOf label D.present ((classRegion A t₀).test σ)) W
      have same := counts t₀
      omega
    have none : ∀ o ∈ (∅ : Finset O), ∀ P Q : Finset O, o ∈ P ↔ o ∈ Q :=
      fun _ absent => absurd absent (Finset.notMem_empty _)
    obtain ⟨π₁, k₁, onto₁, support₁⟩ := exists_supported_renamingUpTo (solutionSetoid A σ) label ∅
      (P := C.present ∩ W) (Q := D.present ∩ W) (fun o absent => none o absent _ _) inside
    obtain ⟨π₂, k₂, onto₂, support₂⟩ := exists_supported_renamingUpTo (solutionSetoid A σ) label ∅
      (P := C.present \ W) (Q := D.present \ W) (fun o absent => none o absent _ _) outside
    have fix₁ : ∀ o, o ∉ W → π₁ o = o := fun o out =>
      support₁ o (fun member => out (Finset.mem_inter.mp member).2)
        (fun member => out (Finset.mem_inter.mp member).2)
    have fix₂ : ∀ o, o ∈ W → π₂ o = o := fun o inn =>
      support₂ o (fun member => (Finset.mem_sdiff.mp member).2 inn)
        (fun member => (Finset.mem_sdiff.mp member).2 inn)
    refine ⟨π₁.trans π₂, ?_, fun o => (k₁.trans k₂).keeps o, ?_⟩
    · show Record.rename (π₁.trans π₂) [Record.sighting W] = [Record.sighting W]
      rw [sighting_rename_eq_iff, Equiv.trans_toEmbedding, ← Finset.map_map, map_eq_self_of_support fix₁,
        finset_map_eq_self π₂ fix₂]
    · have mapped : ((C.present \ W) ∪ (C.present ∩ W)).map (π₁.trans π₂).toEmbedding =
          (D.present \ W) ∪ (D.present ∩ W) := by
        rw [Equiv.trans_toEmbedding, ← Finset.map_map, Finset.map_union, onto₁,
          finset_map_eq_self (s := C.present \ W) π₁ fun o member => fix₁ o (Finset.mem_sdiff.mp member).2,
          Finset.map_union, onto₂,
          finset_map_eq_self (s := D.present ∩ W) π₂ fun o member => fix₂ o (Finset.mem_inter.mp member).2]
      rwa [Finset.sdiff_union_inter, Finset.sdiff_union_inter] at mapped

end OneSighting

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Transport Escaped)
open Observation (Record RecordEquivalent ObservesWithin ModuloProbe Region)
open MeTTaCalculus.OccurrenceCommits (regionOf)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- **Traces refine equivalence relative to the start's record**: trace-equivalent runs of the
escape-relative transport that renames occurrences end in configurations equivalent relative to the
record the environment held at the start. -/
theorem renaming_traceEquiv_recordEquivalent (A : SubstitutionAction T S) (label : O → T)
    {x : Escaped (firstOrder A label).toStep} {r r' : (renamingEscape A label).step.Run x}
    (equivalent : (renamingEscaping A label).TraceEquiv x r r') :
    RecordEquivalent A label x.record r.last.state r'.last.state := by
  obtain ⟨i, aut, -⟩ := Transport.Escape.traceEquiv_past equivalent
  refine ⟨i.same.1, fun o fixed => ?_, fun σ _ => ⟨i.rename, aut, fun o => ?_, i.same.2⟩⟩
  · have moved := fixed i.rename aut
    rw [← i.same.2]
    show o ∈ r.last.state.present ↔ o ∈ r.last.state.present.map i.rename.toEmbedding
    rw [Finset.mem_map_equiv, ← moved, Equiv.symm_apply_apply, moved]
  · show A.E (A.apply σ (label (i.rename o))) (A.apply σ (label o))
    rw [i.keeps]
    exact A.equivalence.refl _

/-! ## Controls -/

namespace AbstractionControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature)
open EscapeControls (blank)
open Observation.Record (sighting automorphisms)
open Observation.RecordControls (sawTwins)

/-- The substitution action of the controls. -/
abbrev A := ConstraintMultisetRewriting.Controls.A

/-- Occurrences `5` and `7`, both labelled `0`, and no knowledge. -/
def left : Configuration (Term signature) ℕ := ⟨[], {5, 7}⟩

/-- Occurrences `7` and `8`, both labelled `0`, and no knowledge. -/
def right : Configuration (Term signature) ℕ := ⟨[], {7, 8}⟩

theorem models_nil (σ : Subst signature) : A.Models σ [] := fun _ absent => absurd absent List.not_mem_nil

/-- The automorphisms of the record carry the sighted set to itself. -/
theorem kept_of_aut {π : ℕ ≃ ℕ} (aut : π ∈ automorphisms sawTwins) :
    ({5, 6} : Finset ℕ).map π.toEmbedding = {5, 6} := by
  have carried : Observation.Record.rename π [sighting {5, 6}] = [sighting {5, 6}] := aut
  simp only [Observation.Record.rename, List.map_cons, List.map_nil, List.cons.injEq, and_true,
    Observation.Record.renameEntry_sighting] at carried
  exact Finset.map_injective Observation.Record.single carried

/-- An exchange of two identities outside the sighted set is an automorphism of the record. -/
theorem swap_aut_of_outside {a b : ℕ} (outsideA : a ≠ 5 ∧ a ≠ 6) (outsideB : b ≠ 5 ∧ b ≠ 6) :
    Equiv.swap a b ∈ automorphisms sawTwins := by
  refine Observation.Record.rename_eq_self_of_fixes fun o member => ?_
  have inside : o = 5 ∨ o = 6 := by
    have support : Observation.Record.support sawTwins = {5, 6} := by decide
    rw [support] at member
    simpa using member
  refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
  · rintro rfl
    rcases inside with rfl | rfl
    · exact outsideA.1 rfl
    · exact outsideA.2 rfl
  · rintro rfl
    rcases inside with rfl | rfl
    · exact outsideB.1 rfl
    · exact outsideB.2 rfl

/-- A set the record's automorphisms keep either is empty or holds `6`. -/
theorem seen_of_kept {seen : Finset ℕ} (kept : ∀ π ∈ automorphisms sawTwins, seen.map π.toEmbedding = seen) :
    seen = ∅ ∨ 6 ∈ seen := by
  have inside : ∀ o ∈ seen, o = 5 ∨ o = 6 := by
    intro o member
    by_contra outside
    replace outside := not_or.mp outside
    obtain ⟨b, fresh⟩ := Infinite.exists_notMem_finset (insert 5 (insert 6 (insert o seen)))
    simp only [Finset.mem_insert, not_or] at fresh
    have there : Equiv.swap o b o ∈ seen.map (Equiv.swap o b).toEmbedding := Finset.mem_map_of_mem _ member
    rw [kept _ (swap_aut_of_outside outside ⟨fresh.1, fresh.2.1⟩), Equiv.swap_apply_left] at there
    exact fresh.2.2.2 there
  by_cases six : 6 ∈ seen
  · exact Or.inr six
  · refine Or.inl (Finset.eq_empty_of_forall_notMem fun o member => ?_)
    rcases inside o member with rfl | rfl
    · have there : Equiv.swap 5 6 5 ∈ seen.map (Equiv.swap 5 6).toEmbedding := Finset.mem_map_of_mem _ member
      rw [kept _ Observation.RecordControls.sighting_swap.1, Equiv.swap_apply_left] at there
      exact six there
    · exact six member

/-- **Every probe modulo the knowledge that the record supports agrees on `{5, 7}` and `{7, 8}`.** -/
theorem supported_agree (p : ModuloProbe A ℕ) (supported : p.Supported sawTwins) :
    p.Observes blank left ↔ p.Observes blank right := by
  have keeps : ∀ o, blank (Equiv.swap 5 8 o) = blank o := fun _ => rfl
  have moved : left.present.map (Equiv.swap 5 8).toEmbedding = right.present := by decide
  cases p with
  | present reference =>
      have fixed : ∀ π ∈ automorphisms sawTwins, π reference = reference :=
        fun π aut => ModuloProbe.present.inj (supported π aut)
      show reference ∈ ({5, 7} : Finset ℕ) ↔ reference ∈ ({7, 8} : Finset ℕ)
      by_cases five : reference = 5
      · subst five
        have := fixed _ Observation.RecordControls.sighting_swap.1
        rw [Equiv.swap_apply_left] at this
        exact absurd this (by decide)
      by_cases eight : reference = 8
      · subst eight
        have := fixed _ (swap_aut_of_outside (a := 8) (b := 9) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩)
        rw [Equiv.swap_apply_left] at this
        exact absurd this (by decide)
      simp [five, eight]
  | check guard =>
      show A.Entails [] (fun σ => guard.Holds A σ blank left.present) ↔
        A.Entails [] (fun σ => guard.Holds A σ blank right.present)
      rw [← moved]
      exact forall_congr' fun σ => imp_congr_right fun _ => (holds_rename A keeps σ left.present guard).symm
  | tally region number =>
      show A.Entails [] (fun σ => (regionOf blank left.present (region.test σ)).card = number σ) ↔
        A.Entails [] (fun σ => (regionOf blank right.present (region.test σ)).card = number σ)
      rw [← moved]
      refine forall_congr' fun σ => imp_congr_right fun _ => ?_
      dsimp only
      rw [regionOf_rename keeps, Finset.card_map]
  | ask region seen =>
      rcases seen_of_kept (fun π aut => (ModuloProbe.ask.inj (supported π aut)).2) with empty | six
      · subst empty
        show A.Entails [] (fun σ => regionOf blank left.present (region.test σ) = ∅) ↔
          A.Entails [] (fun σ => regionOf blank right.present (region.test σ) = ∅)
        rw [← moved]
        refine forall_congr' fun σ => imp_congr_right fun _ => ?_
        dsimp only
        rw [regionOf_rename keeps, Finset.map_eq_empty]
      · have never : ∀ P : Finset ℕ, 6 ∉ P →
            ¬ A.Entails [] (fun σ => regionOf blank P (region.test σ) = seen) := by
          intro P absent asked
          have held := asked (Subst.id signature) (models_nil _)
          rw [← held] at six
          exact absent (Finset.mem_of_mem_filter _ six)
        exact iff_of_false (never left.present (by decide)) (never right.present (by decide))

/-- **Equivalence relative to the record separates them**: no automorphism of the record carries `5`
outside the sighted set. -/
theorem not_recordEquivalent : ¬ RecordEquivalent A blank sawTwins left right := by
  rintro ⟨-, -, each⟩
  obtain ⟨π, aut, -, onto⟩ := each (Subst.id signature) (models_nil _)
  have five : π 5 ∈ ({5, 6} : Finset ℕ) := by
    rw [← kept_of_aut aut]
    exact Finset.mem_map_of_mem π.toEmbedding (by decide)
  have there : π 5 ∈ right.present := by
    rw [← onto]
    exact Finset.mem_map_of_mem π.toEmbedding (by decide)
  have there' : π 5 = 7 ∨ π 5 = 8 := by simpa [right] using there
  have five' : π 5 = 5 ∨ π 5 = 6 := by simpa using five
  omega

/-- The region of every label. -/
def everything : Region A := ⟨fun _ _ => true, fun _ _ _ _ => rfl⟩

/-- **A tally inside the sighted set separates them**: one present occurrence of `{5, 7}` lies in
`{5, 6}`, none of `{7, 8}`. The automorphisms of the record keep `{5, 6}`. -/
theorem within_separates :
    (∀ π ∈ automorphisms sawTwins, ({5, 6} : Finset ℕ).map π.toEmbedding = {5, 6}) ∧
      ObservesWithin A blank everything {5, 6} (fun _ => 1) left ∧
      ¬ ObservesWithin A blank everything {5, 6} (fun _ => 1) right := by
  refine ⟨fun π aut => kept_of_aut aut, fun σ _ => ?_, fun asked => ?_⟩
  · show (regionOf blank left.present (fun _ => true) ∩ {5, 6}).card = 1
    decide
  have held := asked (Subst.id signature) (models_nil _)
  revert held
  decide

/-- **The probes modulo the knowledge are not fully abstract for sighted sets.** -/
theorem supported_not_abstract :
    (∀ p : ModuloProbe A ℕ, p.Supported sawTwins → (p.Observes blank left ↔ p.Observes blank right)) ∧
      ¬ RecordEquivalent A blank sawTwins left right ∧
      ¬ (ObservesWithin A blank everything {5, 6} (fun _ => 1) left ↔
        ObservesWithin A blank everything {5, 6} (fun _ => 1) right) :=
  ⟨supported_agree, not_recordEquivalent, fun same => within_separates.2.2 (same.mp within_separates.2.1)⟩

end AbstractionControls

#print axioms Observation.RecordEquivalent.entails_iff
#print axioms Observation.RecordEquivalent.observes
#print axioms Observation.RecordEquivalent.observesWithin
#print axioms Observation.recordEquivalent_sighting_iff
#print axioms renaming_traceEquiv_recordEquivalent
#print axioms AbstractionControls.seen_of_kept
#print axioms AbstractionControls.supported_agree
#print axioms AbstractionControls.not_recordEquivalent
#print axioms AbstractionControls.within_separates
#print axioms AbstractionControls.supported_not_abstract

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
