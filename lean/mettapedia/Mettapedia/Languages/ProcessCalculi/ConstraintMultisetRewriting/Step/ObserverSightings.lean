import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObserverAbstraction

/-!
# Full abstraction for records of sighted sets

A record whose entries are sighted sets `W₁, …, Wₖ` (held references are sighted singletons,
`Record.sighting_singleton`) has as automorphisms the renamings that carry every `Wᵢ` to itself
(`sightings_rename_eq_iff`). They preserve the **type** of an identity, the list of the sets it lies
in, so they carry every **atom**, the identities of the union with one type, to itself.

* **Renaming block by block** (`exists_blockwise`): for pairwise disjoint blocks, when two sets
  carry the same bag of classes inside each block and outside all of them, one renaming carries
  the first set to the second and every block to itself, moving only identities of the two sets.
* **Full abstraction** (`recordEquivalent_sightings_iff`): relative to a record of sighted sets, two
  configurations are equivalent exactly when every probe modulo the knowledge that the record
  supports, and every tally inside a set that its automorphisms keep, observe the same at both. The
  renaming is built atom by atom, and outside the union of the sighted sets.
* **The uniform fragment** (`RecordModuloEquivalent`): one automorphism for every solution, keeping
  labels up to what the knowledge entails. It implies the pointwise equivalence and, under a
  principal answer, coincides with it (`recordModuloEquivalent_iff_of_principal`), so it is fully
  abstract there too (`recordModuloEquivalent_sightings_iff_of_principal`). Traces of the transport
  that renames occurrences give it relative to the start's record
  (`AnnotatedRuns.renaming_traceEquiv_recordModuloEquivalent`).

For records of references the supported probes alone are fully abstract
(`Observation.pointwiseEquivalent_iff_supported`); for sighted sets the tallies inside kept sets are
needed (`AnnotatedRuns.AbstractionControls.supported_not_abstract`); for relations they are not enough
(`AnnotatedRuns.RelationControls.relation_not_abstract`): adjacent and opposite occurrences of a
directed 4-cycle agree on all of them, and no automorphism of the cycle relates them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

open AnnotatedRuns
open MeTTaCalculus.OccurrenceCommits (regionOf)

universe uT uS uO uU

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

omit [DecidableEq O] in
/-- A held reference is a sighted singleton. -/
theorem Record.sighting_singleton (o : O) : Record.sighting {o} = Record.reference o := by
  simp only [Record.sighting, Record.reference, Finset.map_singleton]
  rfl

omit [DecidableEq O] in
/-- A renaming that carries a finite set into itself carries it onto itself. -/
theorem map_eq_of_subset {π : O ≃ O} {W : Finset O} (sub : W.map π.toEmbedding ⊆ W) :
    W.map π.toEmbedding = W :=
  Finset.eq_of_subset_of_card_le sub (by rw [Finset.card_map])

/-! ## Renaming block by block -/

section Blocks

variable {U : Type uU} (r : Setoid U) (label : O → U)

/-- The union of a list of blocks. -/
def blocksUnion : List (Finset O) → Finset O
  | [] => ∅
  | B :: rest => B ∪ blocksUnion rest

theorem mem_blocksUnion {o : O} : ∀ {blocks : List (Finset O)}, o ∈ blocksUnion blocks ↔ ∃ B ∈ blocks, o ∈ B
  | [] => by simp [blocksUnion]
  | B :: rest => by
      rw [blocksUnion, Finset.mem_union, mem_blocksUnion]
      simp only [List.mem_cons, exists_eq_or_imp]

theorem sdiff_inter_of_disjoint (P : Finset O) {B B' : Finset O} (apart : Disjoint B B') :
    (P \ B) ∩ B' = P ∩ B' := by
  ext o
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨inside, -⟩, there⟩
    exact ⟨inside, there⟩
  · rintro ⟨inside, there⟩
    exact ⟨⟨inside, fun inB => Finset.disjoint_left.mp apart inB there⟩, there⟩

theorem sdiff_blocksUnion_cons (P B : Finset O) (rest : List (Finset O)) :
    (P \ B) \ blocksUnion rest = P \ blocksUnion (B :: rest) := by
  ext o
  simp only [Finset.mem_sdiff, blocksUnion, Finset.mem_union]
  tauto

/-- **Renaming block by block.** -/
theorem exists_blockwise : ∀ (blocks : List (Finset O)), blocks.Pairwise Disjoint → ∀ {P Q : Finset O},
    (∀ B ∈ blocks, (P ∩ B).val.map (fun o => Quotient.mk r (label o)) =
      (Q ∩ B).val.map (fun o => Quotient.mk r (label o))) →
    (P \ blocksUnion blocks).val.map (fun o => Quotient.mk r (label o)) =
      (Q \ blocksUnion blocks).val.map (fun o => Quotient.mk r (label o)) →
    ∃ π : O ≃ O, RenamingUpTo r label ∅ π ∧ P.map π.toEmbedding = Q ∧
      (∀ o, o ∉ P → o ∉ Q → π o = o) ∧ ∀ B ∈ blocks, B.map π.toEmbedding = B
  | [], _, P, Q, _, outside => by
      simp only [blocksUnion, Finset.sdiff_empty] at outside
      obtain ⟨π, k, onto, support⟩ := exists_supported_renamingUpTo r label ∅
        (fun _ absent => absurd absent (Finset.notMem_empty _)) outside
      exact ⟨π, k, onto, support, fun _ absent => absurd absent List.not_mem_nil⟩
  | B :: rest, apart, P, Q, inside, outside => by
      obtain ⟨headApart, restApart⟩ := List.pairwise_cons.mp apart
      obtain ⟨ρ, kρ, ontoρ, supportρ, keptρ⟩ := exists_blockwise rest restApart (P := P \ B) (Q := Q \ B)
        (fun B' member => by
          rw [sdiff_inter_of_disjoint P (headApart B' member), sdiff_inter_of_disjoint Q (headApart B' member)]
          exact inside B' (List.mem_cons_of_mem _ member))
        (by rw [sdiff_blocksUnion_cons, sdiff_blocksUnion_cons]; exact outside)
      obtain ⟨β, kβ, ontoβ, supportβ⟩ := exists_supported_renamingUpTo r label ∅ (P := P ∩ B) (Q := Q ∩ B)
        (fun _ absent => absurd absent (Finset.notMem_empty _)) (inside B List.mem_cons_self)
      have fixβ : ∀ o, o ∉ B → β o = o := fun o out =>
        supportβ o (fun member => out (Finset.mem_inter.mp member).2)
          (fun member => out (Finset.mem_inter.mp member).2)
      have fixρ : ∀ o, o ∈ B → ρ o = o := fun o inn =>
        supportρ o (fun member => (Finset.mem_sdiff.mp member).2 inn)
          (fun member => (Finset.mem_sdiff.mp member).2 inn)
      refine ⟨β.trans ρ, kβ.trans kρ, ?_, fun o notP notQ => ?_, fun B' member => ?_⟩
      · have mapped : ((P \ B) ∪ (P ∩ B)).map (β.trans ρ).toEmbedding = (Q \ B) ∪ (Q ∩ B) := by
          rw [Equiv.trans_toEmbedding, ← Finset.map_map, Finset.map_union, ontoβ,
            finset_map_eq_self (s := P \ B) β fun o member => fixβ o (Finset.mem_sdiff.mp member).2,
            Finset.map_union, ontoρ,
            finset_map_eq_self (s := Q ∩ B) ρ fun o member => fixρ o (Finset.mem_inter.mp member).2]
        rwa [Finset.sdiff_union_inter, Finset.sdiff_union_inter] at mapped
      · rw [Equiv.trans_apply, supportβ o (fun member => notP (Finset.mem_inter.mp member).1)
          (fun member => notQ (Finset.mem_inter.mp member).1)]
        exact supportρ o (fun member => notP (Finset.mem_sdiff.mp member).1)
          (fun member => notQ (Finset.mem_sdiff.mp member).1)
      · rw [Equiv.trans_toEmbedding, ← Finset.map_map]
        rcases List.mem_cons.mp member with rfl | later
        · rw [map_eq_self_of_support fixβ, finset_map_eq_self ρ fixρ]
        · rw [finset_map_eq_self β fun o inside' => fixβ o fun inB =>
            Finset.disjoint_left.mp (headApart B' later) inB inside', keptρ B' later]

end Blocks

/-! ## Records of sighted sets -/

omit [DecidableEq O] in
/-- **The automorphisms of a record of sighted sets** carry every sighted set to itself. -/
theorem sightings_rename_eq_iff {π : O ≃ O} {Ws : List (Finset O)} :
    Record.rename π (Ws.map Record.sighting) = Ws.map Record.sighting ↔ ∀ W ∈ Ws, W.map π.toEmbedding = W := by
  simp only [Record.rename, List.map_map]
  rw [List.map_inj_left]
  refine forall₂_congr fun W _ => ?_
  rw [Function.comp_apply, Record.renameEntry_sighting]
  exact (Finset.map_injective Record.single).eq_iff

/-- The sets an identity lies in. -/
def sightingType (Ws : List (Finset O)) (o : O) : List Bool := Ws.map fun W => decide (o ∈ W)

/-- **An atom**: the identities of the union of the sighted sets with one type. -/
def atom (Ws : List (Finset O)) (τ : List Bool) : Finset O :=
  (blocksUnion Ws).filter fun o => sightingType Ws o = τ

omit [DecidableEq O] in
theorem kept_mem_iff {π : O ≃ O} {W : Finset O} (kept : W.map π.toEmbedding = W) (o : O) :
    π o ∈ W ↔ o ∈ W := by
  constructor
  · intro there
    rw [← kept] at there
    obtain ⟨a, inside, same⟩ := Finset.mem_map.mp there
    have back : a = o := π.injective same
    rw [back] at inside
    exact inside
  · intro inside
    rw [← kept]
    exact Finset.mem_map_of_mem _ inside

/-- The automorphisms keep the type of every identity. -/
theorem sightingType_aut {π : O ≃ O} {Ws : List (Finset O)} (kept : ∀ W ∈ Ws, W.map π.toEmbedding = W)
    (o : O) : sightingType Ws (π o) = sightingType Ws o := by
  refine List.map_inj_left.mpr fun W member => ?_
  simp only [kept_mem_iff (kept W member) o]

/-- The automorphisms keep the union. -/
theorem blocksUnion_aut {π : O ≃ O} {Ws : List (Finset O)} (kept : ∀ W ∈ Ws, W.map π.toEmbedding = W) :
    (blocksUnion Ws).map π.toEmbedding = blocksUnion Ws := by
  refine map_eq_of_subset fun o member => ?_
  obtain ⟨a, inside, rfl⟩ := Finset.mem_map.mp member
  obtain ⟨W, there, inW⟩ := mem_blocksUnion.mp inside
  exact mem_blocksUnion.mpr ⟨W, there, (kept_mem_iff (kept W there) a).mpr inW⟩

/-- The automorphisms keep every atom. -/
theorem atom_aut {π : O ≃ O} {Ws : List (Finset O)} (kept : ∀ W ∈ Ws, W.map π.toEmbedding = W)
    (τ : List Bool) : (atom Ws τ).map π.toEmbedding = atom Ws τ := by
  refine map_eq_of_subset fun o member => ?_
  obtain ⟨a, inside, rfl⟩ := Finset.mem_map.mp member
  obtain ⟨inUnion, typed⟩ := Finset.mem_filter.mp inside
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · rw [← blocksUnion_aut kept]
    exact Finset.mem_map_of_mem _ inUnion
  · show sightingType Ws (π a) = τ
    rw [sightingType_aut kept, typed]

/-- The atoms, one for each type that occurs. -/
noncomputable def atoms (Ws : List (Finset O)) : List (Finset O) :=
  ((blocksUnion Ws).image (sightingType Ws)).toList.map (atom Ws)

theorem atoms_pairwise (Ws : List (Finset O)) : (atoms Ws).Pairwise Disjoint := by
  refine List.Pairwise.map _ (fun τ τ' different => Finset.disjoint_left.mpr fun o first second => ?_)
    (Finset.nodup_toList _)
  exact different ((Finset.mem_filter.mp first).2.symm.trans (Finset.mem_filter.mp second).2)

theorem blocksUnion_atoms (Ws : List (Finset O)) : blocksUnion (atoms Ws) = blocksUnion Ws := by
  ext o
  rw [mem_blocksUnion]
  constructor
  · rintro ⟨B, member, inside⟩
    obtain ⟨τ, -, rfl⟩ := List.mem_map.mp member
    exact (Finset.mem_filter.mp inside).1
  · intro inside
    refine ⟨atom Ws (sightingType Ws o), List.mem_map.mpr ⟨_, ?_, rfl⟩, Finset.mem_filter.mpr ⟨inside, rfl⟩⟩
    exact Finset.mem_toList.mpr (Finset.mem_image_of_mem _ inside)

/-! ## Full abstraction -/

variable {A : SubstitutionAction T S} {label : O → T}

/-- **Full abstraction for records of sighted sets**: two configurations are equivalent relative to a
record of sighted sets exactly when every probe modulo the knowledge that the record supports, and
every tally inside a set that its automorphisms keep, observe the same at both. -/
theorem recordEquivalent_sightings_iff (Ws : List (Finset O)) (C D : Configuration T O) :
    RecordEquivalent A label (Ws.map Record.sighting) C D ↔
      (∀ p : ModuloProbe A O, p.Supported (Ws.map Record.sighting) →
        (p.Observes label C ↔ p.Observes label D)) ∧
      ∀ W : Finset O, (∀ π ∈ Record.automorphisms (Ws.map Record.sighting), W.map π.toEmbedding = W) →
        ∀ (region : Region A) (number : S → ℕ),
          ObservesWithin A label region W number C ↔ ObservesWithin A label region W number D := by
  constructor
  · intro h
    exact ⟨fun p supported => h.observes supported, fun W kept region number =>
      h.observesWithin region kept number⟩
  · rintro ⟨agree, within⟩
    have keptAtom : ∀ τ, ∀ π ∈ Record.automorphisms (Ws.map Record.sighting),
        (atom Ws τ).map π.toEmbedding = atom Ws τ :=
      fun τ π aut => atom_aut (sightings_rename_eq_iff.mp aut) τ
    have keptUnion : ∀ π ∈ Record.automorphisms (Ws.map Record.sighting),
        (blocksUnion Ws).map π.toEmbedding = blocksUnion Ws :=
      fun π aut => blocksUnion_aut (sightings_rename_eq_iff.mp aut)
    have equation : ∀ e : Equation T,
        (ModuloProbe.check (Check.equal e.1 e.2) : ModuloProbe A O).Supported (Ws.map Record.sighting) :=
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
    have withinCount : ∀ W : Finset O, (∀ π ∈ Record.automorphisms (Ws.map Record.sighting),
        W.map π.toEmbedding = W) → ∀ t₀ : T,
        (regionOf label C.present ((classRegion A t₀).test σ) ∩ W).card =
          (regionOf label D.present ((classRegion A t₀).test σ) ∩ W).card := by
      intro W kept t₀
      have atC : ObservesWithin A label (classRegion A t₀) W
          (fun τ => (regionOf label C.present ((classRegion A t₀).test τ) ∩ W).card) C := fun _ _ => rfl
      exact ((within W kept _ _).mp atC σ solvedD).symm
    have totalCount : ∀ t₀ : T, (regionOf label C.present ((classRegion A t₀).test σ)).card =
        (regionOf label D.present ((classRegion A t₀).test σ)).card := by
      intro t₀
      have atC : (ModuloProbe.tally (classRegion A t₀)
          fun τ => (regionOf label C.present ((classRegion A t₀).test τ)).card).Observes label C :=
        fun _ _ => rfl
      exact ((agree _ fun _ _ => rfl).mp atC σ solvedD).symm
    have inside : ∀ B ∈ atoms Ws,
        (C.present ∩ B).val.map (fun o => Quotient.mk (solutionSetoid A σ) (label o)) =
          (D.present ∩ B).val.map (fun o => Quotient.mk (solutionSetoid A σ) (label o)) := by
      intro B member
      obtain ⟨τ, -, rfl⟩ := List.mem_map.mp member
      refine Multiset.ext.mpr fun c => ?_
      obtain ⟨t₀, rfl⟩ := Quotient.exists_rep c
      rw [← card_classRegion, ← card_classRegion, regionOf_inter, regionOf_inter]
      exact withinCount _ (keptAtom τ) t₀
    have outside : (C.present \ blocksUnion (atoms Ws)).val.map
          (fun o => Quotient.mk (solutionSetoid A σ) (label o)) =
        (D.present \ blocksUnion (atoms Ws)).val.map (fun o => Quotient.mk (solutionSetoid A σ) (label o)) := by
      rw [blocksUnion_atoms]
      refine Multiset.ext.mpr fun c => ?_
      obtain ⟨t₀, rfl⟩ := Quotient.exists_rep c
      rw [← card_classRegion, ← card_classRegion, regionOf_sdiff, regionOf_sdiff]
      have splitC := Finset.card_sdiff_add_card_inter
        (regionOf label C.present ((classRegion A t₀).test σ)) (blocksUnion Ws)
      have splitD := Finset.card_sdiff_add_card_inter
        (regionOf label D.present ((classRegion A t₀).test σ)) (blocksUnion Ws)
      have same := withinCount _ keptUnion t₀
      have total := totalCount t₀
      omega
    obtain ⟨π, k, onto, -, keptAtoms⟩ := exists_blockwise (solutionSetoid A σ) label (atoms Ws)
      (atoms_pairwise Ws) inside outside
    refine ⟨π, sightings_rename_eq_iff.mpr fun W member => map_eq_of_subset fun o mapped => ?_,
      k.keeps, onto⟩
    obtain ⟨a, inW, rfl⟩ := Finset.mem_map.mp mapped
    have inUnion : a ∈ blocksUnion Ws := mem_blocksUnion.mpr ⟨W, member, inW⟩
    have inAtom : a ∈ atom Ws (sightingType Ws a) := Finset.mem_filter.mpr ⟨inUnion, rfl⟩
    have atomMember : atom Ws (sightingType Ws a) ∈ atoms Ws :=
      List.mem_map.mpr ⟨_, Finset.mem_toList.mpr (Finset.mem_image_of_mem _ inUnion), rfl⟩
    have moved : π a ∈ atom Ws (sightingType Ws a) := by
      rw [← keptAtoms _ atomMember]
      exact Finset.mem_map_of_mem _ inAtom
    have typed : sightingType Ws (π a) = sightingType Ws a := (Finset.mem_filter.mp moved).2
    have decided := (List.map_inj_left.mp typed) W member
    simp only [decide_eq_decide] at decided
    exact decided.mpr inW

/-! ## The uniform fragment -/

section Uniform

variable (A : SubstitutionAction T S) (label : O → T) (r : Record O)

/-- **Equivalence modulo the knowledge relative to a record**: one automorphism of the record, keeping
the labels up to what the knowledge entails, carries the first configuration to the second up to the
solutions of its knowledge. The renaming is chosen once, for every solution. -/
def RecordModuloEquivalent (C D : Configuration T O) : Prop :=
  ∃ π ∈ Record.automorphisms r, RenamingUpTo (entailedSetoid A C.equations) label ∅ π ∧
    GuardFreeProcessOrders.SameUpTo A (renameConfiguration π C) D

variable {A label r}

omit [DecidableEq O] in
/-- **The uniform equivalence implies the pointwise one.** -/
theorem RecordModuloEquivalent.recordEquivalent {C D : Configuration T O}
    (h : RecordModuloEquivalent A label r C D) : RecordEquivalent A label r C D := by
  obtain ⟨π, aut, k, same⟩ := h
  refine ⟨same.1, fun o fixed => ?_, fun σ solved => ⟨π, aut, fun o => k.keeps o σ solved, same.2⟩⟩
  rw [← same.2]
  show o ∈ C.present ↔ o ∈ C.present.map π.toEmbedding
  rw [Finset.mem_map_equiv]
  have moved := fixed π aut
  rw [← moved, Equiv.symm_apply_apply, moved]

omit [DecidableEq O] in
/-- **With a principal answer, the pointwise equivalence is uniform**: the automorphism at the
principal answer serves every solution. -/
theorem RecordEquivalent.modulo_of_principal {C D : Configuration T O} {answer : S}
    (principal : A.Principal C.equations answer) (h : RecordEquivalent A label r C D) :
    RecordModuloEquivalent A label r C D := by
  obtain ⟨π, aut, keeps, onto⟩ := h.2.2 answer principal.sound
  have k : RenamingUpTo (solutionSetoid A answer) label ∅ π :=
    ⟨keeps, fun _ absent => absurd absent (Finset.notMem_empty _)⟩
  exact ⟨π, aut, k.weaken (solution_le_entailedSetoid principal), h.1, onto⟩

omit [DecidableEq O] in
/-- **The two agree under a principal answer.** -/
theorem recordModuloEquivalent_iff_of_principal {C D : Configuration T O} {answer : S}
    (principal : A.Principal C.equations answer) :
    RecordModuloEquivalent A label r C D ↔ RecordEquivalent A label r C D :=
  ⟨RecordModuloEquivalent.recordEquivalent, RecordEquivalent.modulo_of_principal principal⟩

/-- **Full abstraction of the uniform equivalence for records of sighted sets, under a principal
answer.** -/
theorem recordModuloEquivalent_sightings_iff_of_principal (Ws : List (Finset O)) {C D : Configuration T O}
    {answer : S} (principal : A.Principal C.equations answer) :
    RecordModuloEquivalent A label (Ws.map Record.sighting) C D ↔
      (∀ p : ModuloProbe A O, p.Supported (Ws.map Record.sighting) →
        (p.Observes label C ↔ p.Observes label D)) ∧
      ∀ W : Finset O, (∀ π ∈ Record.automorphisms (Ws.map Record.sighting), W.map π.toEmbedding = W) →
        ∀ (region : Region A) (number : S → ℕ),
          ObservesWithin A label region W number C ↔ ObservesWithin A label region W number D :=
  (recordModuloEquivalent_iff_of_principal principal).trans (recordEquivalent_sightings_iff Ws C D)

end Uniform

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation


/-! ## Where tallies stop: relations -/

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

section UniformTraces

open Interface (Transport Escaped)

variable {T : Type*} {S : Type*} {O : Type*} [DecidableEq O]

/-- **Traces give the uniform equivalence relative to the start's record**: one automorphism of the
record, keeping labels, relates the ends of trace-equivalent runs of the transport that renames
occurrences. -/
theorem renaming_traceEquiv_recordModuloEquivalent (A : SubstitutionAction T S) (label : O → T)
    {x : Escaped (firstOrder A label).toStep} {r r' : (renamingEscape A label).step.Run x}
    (equivalent : (renamingEscaping A label).TraceEquiv x r r') :
    Observation.RecordModuloEquivalent A label x.record r.last.state r'.last.state := by
  obtain ⟨i, aut, -⟩ := Transport.Escape.traceEquiv_past equivalent
  refine ⟨i.rename, aut, ⟨fun o σ _ => ?_, fun _ absent => absurd absent (Finset.notMem_empty _)⟩, i.same⟩
  show A.E (A.apply σ (label (i.rename o))) (A.apply σ (label o))
  rw [i.keeps]
  exact A.equivalence.refl _

end UniformTraces

namespace RelationControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature)
open EscapeControls (blank)
open Observation (Record RecordEquivalent ObservesWithin ModuloProbe)
open Observation.Record (automorphisms)
open MeTTaCalculus.OccurrenceCommits (regionOf)

/-- The substitution action of the controls. -/
abbrev A := ConstraintMultisetRewriting.Controls.A

/-- The record of the directed cycle `1 → 2 → 3 → 4 → 1`. -/
def cycle : Record ℕ := [{[1, 2], [2, 3], [3, 4], [4, 1]}]

/-- The rotation `1 ↦ 2 ↦ 3 ↦ 4 ↦ 1`. -/
def rotation : ℕ ≃ ℕ := (Equiv.swap 1 2).trans ((Equiv.swap 1 3).trans (Equiv.swap 1 4))

theorem rotation_aut : rotation ∈ automorphisms cycle ∧ rotation 2 = 3 ∧ rotation 3 = 4 ∧ rotation 4 = 1 ∧
    rotation 1 = 2 := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  show Record.rename rotation cycle = cycle
  decide

/-- Adjacent occurrences `1` and `2`, labelled alike, and no knowledge. -/
def adjacent : Configuration (Term signature) ℕ := ⟨[], {1, 2}⟩

/-- Opposite occurrences `1` and `3`, labelled alike, and no knowledge. -/
def opposite : Configuration (Term signature) ℕ := ⟨[], {1, 3}⟩

theorem models_nil (σ : Subst signature) : A.Models σ [] := fun _ absent => absurd absent List.not_mem_nil

/-- A set the automorphisms of the cycle keep holds `2` exactly when it holds `3`. -/
theorem two_iff_three {W : Finset ℕ} (kept : ∀ π ∈ automorphisms cycle, W.map π.toEmbedding = W) :
    2 ∈ W ↔ 3 ∈ W := by
  obtain ⟨aut, two, three, four, one⟩ := rotation_aut
  have step : ∀ o, o ∈ W → rotation o ∈ W := fun o member => by
    rw [← kept _ aut]
    exact Finset.mem_map_of_mem _ member
  constructor
  · intro member
    have := step 2 member
    rwa [two] at this
  · intro member
    have at4 := step 3 member
    rw [three] at at4
    have at1 := step 4 at4
    rw [four] at at1
    have at2 := step 1 at1
    rwa [one] at at2

/-- The exchange of `2` and `3`, which carries `adjacent` to `opposite`. -/
abbrev exchange : ℕ ≃ ℕ := Equiv.swap 2 3

theorem exchange_kept {W : Finset ℕ} (same : 2 ∈ W ↔ 3 ∈ W) : W.map exchange.toEmbedding = W := by
  refine Observation.map_eq_of_subset fun o member => ?_
  obtain ⟨a, inside, rfl⟩ := Finset.mem_map.mp member
  show Equiv.swap 2 3 a ∈ W
  by_cases two : a = 2
  · subst two
    rw [Equiv.swap_apply_left]
    exact same.mp inside
  by_cases three : a = 3
  · subst three
    rw [Equiv.swap_apply_right]
    exact same.mpr inside
  rw [Equiv.swap_apply_of_ne_of_ne two three]
  exact inside

theorem exchanged : adjacent.present.map exchange.toEmbedding = opposite.present := by decide

/-- **Every probe modulo the knowledge that the cycle supports agrees on adjacent and opposite
occurrences.** -/
theorem supported_agree (p : ModuloProbe A ℕ) (supported : p.Supported cycle) :
    p.Observes blank adjacent ↔ p.Observes blank opposite := by
  have keeps : ∀ o, blank (exchange o) = blank o := fun _ => rfl
  cases p with
  | present reference =>
      have fixed : ∀ π ∈ automorphisms cycle, π reference = reference :=
        fun π aut => ModuloProbe.present.inj (supported π aut)
      obtain ⟨aut, two, three, -, -⟩ := rotation_aut
      show reference ∈ ({1, 2} : Finset ℕ) ↔ reference ∈ ({1, 3} : Finset ℕ)
      by_cases isTwo : reference = 2
      · subst isTwo
        exact absurd ((fixed _ aut).symm.trans two) (by decide)
      by_cases isThree : reference = 3
      · subst isThree
        exact absurd ((fixed _ aut).symm.trans three) (by decide)
      simp [isTwo, isThree]
  | check guard =>
      show A.Entails [] (fun σ => guard.Holds A σ blank adjacent.present) ↔
        A.Entails [] (fun σ => guard.Holds A σ blank opposite.present)
      rw [← exchanged]
      exact forall_congr' fun σ => imp_congr_right fun _ => (holds_rename A keeps σ adjacent.present guard).symm
  | tally region number =>
      show A.Entails [] (fun σ => (regionOf blank adjacent.present (region.test σ)).card = number σ) ↔
        A.Entails [] (fun σ => (regionOf blank opposite.present (region.test σ)).card = number σ)
      rw [← exchanged]
      refine forall_congr' fun σ => imp_congr_right fun _ => ?_
      dsimp only
      rw [regionOf_rename keeps, Finset.card_map]
  | ask region seen =>
      have fixed : seen.map exchange.toEmbedding = seen :=
        exchange_kept (two_iff_three fun π aut => (ModuloProbe.ask.inj (supported π aut)).2)
      show A.Entails [] (fun σ => regionOf blank adjacent.present (region.test σ) = seen) ↔
        A.Entails [] (fun σ => regionOf blank opposite.present (region.test σ) = seen)
      rw [← exchanged]
      refine forall_congr' fun σ => imp_congr_right fun _ => ?_
      dsimp only
      rw [regionOf_rename keeps]
      constructor
      · intro unmoved
        rw [unmoved, fixed]
      · intro moved
        exact Finset.map_injective exchange.toEmbedding (moved.trans fixed.symm)

/-- **Every tally inside a set that the cycle's automorphisms keep agrees too.** -/
theorem within_agree (W : Finset ℕ) (kept : ∀ π ∈ automorphisms cycle, W.map π.toEmbedding = W)
    (region : Observation.Region A) (number : Subst signature → ℕ) :
    ObservesWithin A blank region W number adjacent ↔ ObservesWithin A blank region W number opposite := by
  have keeps : ∀ o, blank (exchange o) = blank o := fun _ => rfl
  have fixed : W.map exchange.toEmbedding = W := exchange_kept (two_iff_three kept)
  show A.Entails [] (fun σ => (regionOf blank adjacent.present (region.test σ) ∩ W).card = number σ) ↔
    A.Entails [] (fun σ => (regionOf blank opposite.present (region.test σ) ∩ W).card = number σ)
  rw [← exchanged]
  refine forall_congr' fun σ => imp_congr_right fun _ => ?_
  dsimp only
  rw [regionOf_rename keeps]
  conv_rhs => rw [← fixed, ← Finset.map_inter, Finset.card_map]

/-- **Equivalence relative to the cycle separates them**: an automorphism carries the edge `1 → 2` to
an edge, and no edge joins `1` and `3`. -/
theorem not_recordEquivalent : ¬ RecordEquivalent A blank cycle adjacent opposite := by
  rintro ⟨-, -, each⟩
  obtain ⟨π, aut, -, onto⟩ := each (Subst.id signature) (models_nil _)
  have carried : Observation.Record.rename π cycle = cycle := aut
  have edges : Observation.Record.renameEntry π {[1, 2], [2, 3], [3, 4], [4, 1]} =
      {[1, 2], [2, 3], [3, 4], [4, 1]} := by
    simpa [Observation.Record.rename, cycle] using carried
  have edge : [π 1, π 2] ∈ ({[1, 2], [2, 3], [3, 4], [4, 1]} : Finset (List ℕ)) := by
    rw [← edges]
    exact Finset.mem_map_of_mem (s := ({[1, 2], [2, 3], [3, 4], [4, 1]} : Finset (List ℕ)))
      (Observation.Record.tupleEmbedding π) (a := [1, 2]) (by decide)
  have first : π 1 ∈ opposite.present := by
    rw [← onto]
    exact Finset.mem_map_of_mem π.toEmbedding (by decide)
  have second : π 2 ∈ opposite.present := by
    rw [← onto]
    exact Finset.mem_map_of_mem π.toEmbedding (by decide)
  have apart : π 1 ≠ π 2 := fun same => absurd (π.injective same) (by decide)
  simp only [opposite, Finset.mem_insert, Finset.mem_singleton] at first second
  simp only [Finset.mem_insert, Finset.mem_singleton, List.cons.injEq, and_true] at edge
  omega

/-- **For relations, tallies inside kept sets are not enough**: adjacent and opposite occurrences of
the cycle agree on every probe modulo the knowledge that the cycle supports and on every tally inside
a set its automorphisms keep, and are not equivalent relative to it. A probe class that is fully
abstract for relational records must test relations among the present occurrences. -/
theorem relation_not_abstract :
    (∀ p : ModuloProbe A ℕ, p.Supported cycle → (p.Observes blank adjacent ↔ p.Observes blank opposite)) ∧
      (∀ W : Finset ℕ, (∀ π ∈ automorphisms cycle, W.map π.toEmbedding = W) →
        ∀ region number, ObservesWithin A blank region W number adjacent ↔
          ObservesWithin A blank region W number opposite) ∧
      ¬ RecordEquivalent A blank cycle adjacent opposite :=
  ⟨supported_agree, within_agree, not_recordEquivalent⟩

end RelationControls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

#print axioms Record.sighting_singleton
#print axioms exists_blockwise
#print axioms sightings_rename_eq_iff
#print axioms atom_aut
#print axioms atoms_pairwise
#print axioms blocksUnion_atoms
#print axioms recordEquivalent_sightings_iff
#print axioms RecordModuloEquivalent.recordEquivalent
#print axioms RecordEquivalent.modulo_of_principal
#print axioms recordModuloEquivalent_iff_of_principal
#print axioms recordModuloEquivalent_sightings_iff_of_principal
#print axioms AnnotatedRuns.renaming_traceEquiv_recordModuloEquivalent
#print axioms AnnotatedRuns.RelationControls.rotation_aut
#print axioms AnnotatedRuns.RelationControls.supported_agree
#print axioms AnnotatedRuns.RelationControls.within_agree
#print axioms AnnotatedRuns.RelationControls.not_recordEquivalent
#print axioms AnnotatedRuns.RelationControls.relation_not_abstract

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation
