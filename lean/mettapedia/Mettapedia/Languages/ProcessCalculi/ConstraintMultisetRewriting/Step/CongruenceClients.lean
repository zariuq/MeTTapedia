import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CongruenceParallel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObserverRespect

/-!
# The client-respecting equivalence is preserved by semantic firings

A client relates states through the identities it holds (`Client.escaped`); the client equivalence is
equivalence modulo the knowledge relative to them, and permitted probes respect it
(`Client.respects_modulo`). A firing changes the client too: its queries' sightings join the
client's (`Client.watch`). So preservation is a statement about joint ends, a state with the client
its history left (`JointModuloEquivalent`): one renaming relates the states and the clients.

## Results

* **Probes are equivariant up to the knowledge** (`ModuloProbe.observes_renameConfiguration`): along a
  renaming that keeps labels up to what the knowledge entails, a probe observes at a state what its
  renaming observes at the renamed state; no identity needs to be fixed. With the solutions and the
  occurrences, probes see nothing else (`ModuloProbe.observes_congr`).
* **Respect at joint ends** (`JointModuloEquivalent.respects`): at equivalent joint ends, every probe
  the first client may make has a renaming that the second client may make, and the two observe the
  same. A probe naming only identities fixed by the renaming is its own renaming
  (`Client.respects_modulo`).
* **One renaming for the firing and the results** (`modulo_step_witness`,
  `ModuloEquivalent.semantic_counterpart_witness`): the renaming that moves a semantic firing to its
  counterpart also relates the results.
* **Semantic firings preserve the client equivalence** (`ModuloEquivalent.client_firing` when the
  made identities avoid the other state; `ModuloEquivalent.client_counterpart` with a fresh supply of
  the made labels): from states equivalent for a client, an admitted semantic firing and its
  counterpart lead to equivalent joint ends, with the client having watched each firing. Renaming a
  client that watched a run is watching the renamed run (`Client.watch_rename`).
* **Disjoint parallel composition preserves it** (`Client.respects_tensor`, `CongruenceParallel`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

open AnnotatedRuns
open GuardFreeProcessOrders (SameUpTo)
open MeTTaCalculus.OccurrenceCommits (regionOf)
open Semantic

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO}

/-! ## Renaming sightings and clients -/

section Clients

theorem sighted_rename [DecidableEq O] (π : O ≃ O) :
    ∀ queries : List (PredicateQueryAdmission.Query T S O),
      sighted (queries.map (renameQuery π)) = (sighted queries).map π.toEmbedding
  | [] => (Finset.map_empty _).symm
  | q :: rest => by
      show (renameQuery π q).seen ∪ sighted (rest.map (renameQuery π)) =
        (q.seen ∪ sighted rest).map π.toEmbedding
      rw [sighted_rename π rest, Finset.map_union]
      rfl

theorem runSighted_rename [DecidableEq O] (π : O ≃ O) :
    ∀ w : List (Firing T S O), runSighted (w.map (Firing.rename π)) = (runSighted w).map π.toEmbedding
  | [] => (Finset.map_empty _).symm
  | f :: rest => by
      show sighted (f.queries.map (renameQuery π)) ∪ runSighted (rest.map (Firing.rename π)) =
        (sighted f.queries ∪ runSighted rest).map π.toEmbedding
      rw [sighted_rename, runSighted_rename π rest, Finset.map_union]

/-- **Renaming a client that watched a run is watching the renamed run**, for a renaming that fixes the
client's own identities. -/
theorem Client.watch_rename [DecidableEq O] (c : Client O) {π : O ≃ O}
    (fixes : ∀ o ∈ c.escaped, π o = o) (w : List (Firing T S O)) :
    (c.watch w).rename π = c.watch (w.map (Firing.rename π)) := by
  have same := c.rename_eq_self fixes
  obtain ⟨held, seen, evidence, published⟩ := c
  simp only [Client.rename, Client.mk.injEq] at same
  obtain ⟨heldSame, seenSame, evidenceSame, publishedSame⟩ := same
  show Client.mk (held.map π) ((seen ∪ runSighted w).map π.toEmbedding)
      (evidence.map π.toEmbedding) (published.map π.toEmbedding) =
    Client.mk held (seen ∪ runSighted (w.map (Firing.rename π))) evidence published
  rw [heldSame, evidenceSame, publishedSame, Finset.map_union, seenSame, runSighted_rename]

/-- The escaped identities of a renamed client are the renamed escaped identities. -/
theorem Client.escaped_rename [DecidableEq O] (π : O ≃ O) (c : Client O) :
    (c.rename π).escaped = c.escaped.map π.toEmbedding := by
  obtain ⟨held, seen, evidence, published⟩ := c
  show (held.map π).toFinset ∪ seen.map π.toEmbedding ∪ evidence.map π.toEmbedding ∪
      published.map π.toEmbedding = (held.toFinset ∪ seen ∪ evidence ∪ published).map π.toEmbedding
  rw [toFinset_rename, Finset.map_union, Finset.map_union, Finset.map_union]

end Clients

/-! ## Probes up to the knowledge -/

section Probes

variable {A : SubstitutionAction T S} {label : O → T}

theorem ModuloProbe.names_rename (π : O ≃ O) (p : ModuloProbe A O) :
    (p.rename π).names = p.names.map π.toEmbedding := by
  cases p with
  | present reference => exact (Finset.map_singleton π.toEmbedding reference).symm
  | check guard => exact (Finset.map_empty _).symm
  | ask region seen => rfl
  | tally region number => exact (Finset.map_empty _).symm

/-- **Probes see a configuration only through its solutions and its occurrences.** -/
theorem ModuloProbe.observes_congr (p : ModuloProbe A O) {C D : Configuration T O}
    (same : SameUpTo A C D) : p.Observes label C ↔ p.Observes label D := by
  obtain ⟨equivalent, present⟩ := same
  cases p with
  | present reference =>
      show reference ∈ C.present ↔ reference ∈ D.present
      rw [present]
  | check guard =>
      show (∀ σ, A.Models σ C.equations → _) ↔ (∀ σ, A.Models σ D.equations → _)
      rw [present]
      exact forall_congr' fun σ => imp_congr_left (equivalent σ)
  | ask region seen =>
      show (∀ σ, A.Models σ C.equations → _) ↔ (∀ σ, A.Models σ D.equations → _)
      rw [present]
      exact forall_congr' fun σ => imp_congr_left (equivalent σ)
  | tally region number =>
      show (∀ σ, A.Models σ C.equations → _) ↔ (∀ σ, A.Models σ D.equations → _)
      rw [present]
      exact forall_congr' fun σ => imp_congr_left (equivalent σ)

/-- **Probes are equivariant up to the knowledge**: along a renaming that keeps labels up to what the
knowledge entails, a probe observes at a state what its renaming observes at the renamed state. -/
theorem ModuloProbe.observes_renameConfiguration {C : Configuration T O} {π : O ≃ O}
    (keeps : ∀ o, Entailed A C.equations (label (π o)) (label o)) (p : ModuloProbe A O) :
    p.Observes label C ↔ (p.rename π).Observes label (renameConfiguration π C) := by
  cases p with
  | present reference => exact (Finset.mem_map' π.toEmbedding).symm
  | check guard =>
      exact forall_congr' fun σ => imp_congr_right fun solved =>
        (holds_map_upTo (fun o => keeps o σ solved) C.present guard).symm
  | ask region seen =>
      refine forall_congr' fun σ => imp_congr_right fun solved => ?_
      show regionOf label C.present (region.test σ) = seen ↔
        regionOf label (C.present.map π.toEmbedding) (region.test σ) = seen.map π.toEmbedding
      rw [regionOf_map_upTo (fun o => keeps o σ solved) region C.present]
      exact Finset.map_inj.symm
  | tally region number =>
      refine forall_congr' fun σ => imp_congr_right fun solved => ?_
      show (regionOf label C.present (region.test σ)).card = number σ ↔
        (regionOf label (C.present.map π.toEmbedding) (region.test σ)).card = number σ
      rw [regionOf_map_upTo (fun o => keeps o σ solved) region C.present, Finset.card_map]

/-- **Respect at joint ends**: every probe the first client may make has a renaming the second
client may make, and the two observe the same. -/
theorem JointModuloEquivalent.respects [DecidableEq O] {E : Finset O}
    {x y : Configuration T O × Client O} (h : JointModuloEquivalent A label E x y) :
    ∃ π : O ≃ O, x.2.rename π = y.2 ∧ ∀ p : ModuloProbe A O, p.names ⊆ x.2.escaped →
      (p.rename π).names ⊆ y.2.escaped ∧ (p.Observes label x.1 ↔ (p.rename π).Observes label y.1) := by
  obtain ⟨π, k, same, clients⟩ := h
  refine ⟨π, clients, fun p permitted => ⟨?_, ?_⟩⟩
  · rw [ModuloProbe.names_rename, ← clients, Client.escaped_rename]
    exact Finset.map_subset_map.mpr permitted
  · exact (ModuloProbe.observes_renameConfiguration k.keeps p).trans ((p.rename π).observes_congr same)

end Probes

/-! ## Semantic firings preserve the client equivalence -/

section Firings

variable {A : SubstitutionAction T S} {label : O → T} {E : Finset O}

/-- **One renaming for the firing and the results**: a renaming up to the knowledge that fixes the
made identities moves a semantic firing to one admitted together with it, and relates the results. -/
theorem modulo_step_witness [DecidableEq O] {C D : Configuration T O} {π : O ≃ O}
    (k : RenamingUpTo (entailedSetoid A C.equations) label E π)
    (same : SameUpTo A (renameConfiguration π C) D) {f : Firing T S O}
    (fixesMade : ∀ r ∈ f.selection.made, π r = r) (reads : IsSemantic A f) :
    ((f.rename π).Valid A label D ↔ f.Valid A label C) ∧
      RenamingUpTo (entailedSetoid A (f.result label C).equations) label E π ∧
      SameUpTo A (renameConfiguration π (f.result label C)) ((f.rename π).result label D) := by
  refine ⟨(modulo_step k same fixesMade reads).1,
    k.weaken (entailedSetoid_mono (result_refines f C)), ?_⟩
  have relabelled : SameUpTo A (f.result label C) (f.result (fun o => label (π o)) C) :=
    Firing.result_relabel fun o σ solved => A.equivalence.symm (k.keeps o σ solved)
  have moved := sameUpTo_rename A π relabelled
  rw [← Firing.result_rename_comp] at moved
  exact GuardFreeProcessOrders.SameUpTo.trans A moved ((f.rename π).result_congr A label same)

/-- **Counterparts with their witness**: with a fresh supply of the made labels, an admitted semantic
firing has a renamed counterpart at the other state, and the same renaming relates the results. -/
theorem ModuloEquivalent.semantic_counterpart_witness [DecidableEq O] {C D : Configuration T O}
    (h : ModuloEquivalent A label E C D) {f : Firing T S O} (valid : f.Valid A label C)
    (reads : IsSemantic A f)
    (supply : ∀ r ∈ f.selection.made, ∀ G : Finset O, ∃ o, o ∉ G ∧ label o = label r) :
    ∃ τ : O ≃ O, (f.rename τ).Valid A label D ∧
      RenamingUpTo (entailedSetoid A (f.result label C).equations) label E τ ∧
      SameUpTo A (renameConfiguration τ (f.result label C)) ((f.rename τ).result label D) := by
  classical
  let M := f.selection.made.toFinset.filter (· ∈ D.present)
  let F := C.present ∪ D.present ∪ E ∪ f.names
  have inF_C : ∀ {o}, o ∈ C.present → o ∈ F := fun inC =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ inC))
  have inF_D : ∀ {o}, o ∈ D.present → o ∈ F := fun inD =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ inD))
  have inF_E : ∀ {o}, o ∈ E → o ∈ F := fun inE =>
    Finset.mem_union_left _ (Finset.mem_union_right _ inE)
  have madeNamed : ∀ {o}, o ∈ f.selection.made → o ∈ f.names := fun made => by
    simp [Firing.names, made]
  have madeOfM : ∀ {o}, o ∈ M → o ∈ f.selection.made := fun inM =>
    List.mem_toFinset.mp (Finset.mem_filter.mp inM).1
  have sub : M ⊆ F := fun o inM => inF_D (Finset.mem_filter.mp inM).2
  obtain ⟨ρ, keeps, moved, fixed⟩ := exists_fresh_relabelling M F sub
    fun m inM => supply m (madeOfM inM)
  have freshC : ∀ {r}, r ∈ f.selection.made → r ∉ C.present := fun made => made_fresh valid made
  have fixC : ∀ o ∈ C.present, ρ o = o := fun o inC =>
    fixed o (inF_C inC) fun inM => freshC (madeOfM inM) inC
  have fixE : ∀ o ∈ E, ρ o = o := fun o inE =>
    fixed o (inF_E inE) fun inM =>
      freshC (madeOfM inM) ((h.escaped_iff inE).mpr (Finset.mem_filter.mp inM).2)
  have stays : renameConfiguration ρ C = C := by
    show (⟨C.equations, C.present.map ρ.toEmbedding⟩ : Configuration T O) = C
    rw [finset_map_eq_self ρ fixC]
  have gValid : (f.rename ρ).Valid A label C := by
    have moved := (Firing.valid_rename A keeps f C).mpr valid
    rwa [stays] at moved
  have gResult : (f.rename ρ).result label C = renameConfiguration ρ (f.result label C) := by
    have moved := Firing.result_rename keeps f C
    rwa [stays] at moved
  have gAvoids : ∀ r ∈ (f.rename ρ).selection.made, r ∉ C.present ∧ r ∉ D.present := by
    intro r member
    change r ∈ f.selection.made.map ρ at member
    obtain ⟨r₀, made₀, rfl⟩ := List.mem_map.mp member
    by_cases inD : r₀ ∈ D.present
    · have out := moved r₀ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr made₀, inD⟩)
      exact ⟨fun inC => out (inF_C inC), fun inD' => out (inF_D inD')⟩
    · have same : ρ r₀ = r₀ := fixed r₀
        (Finset.mem_union_right _ (madeNamed made₀)) fun inM => inD (Finset.mem_filter.mp inM).2
      rw [same]
      exact ⟨freshC made₀, inD⟩
  obtain ⟨π, k, same, support⟩ := h.supported
  obtain ⟨admits, kResult, sameResult⟩ := modulo_step_witness k same
    (fun r member => support r (gAvoids r member).1 (gAvoids r member).2) (isSemantic_rename ρ reads)
  have equations : ((f.rename ρ).result label C).equations = (f.result label C).equations :=
    (congrArg Configuration.equations gResult : _).trans rfl
  rw [equations] at kResult
  refine ⟨ρ.trans π, ?_, ⟨fun o => ?_, fun o member => ?_⟩, ?_⟩
  · rw [Firing.rename_trans]
    exact admits.mpr gValid
  · have kept := kResult.keeps (ρ o)
    rwa [keeps o] at kept
  · show π (ρ o) = o
    rw [fixE o member, k.fixes o member]
  · rw [renameConfiguration_trans, ← gResult, Firing.rename_trans]
    exact sameResult

/-- **Semantic firings preserve the client equivalence**, when the made identities avoid the other
state: the joint ends, each client having watched its firing, are equivalent. -/
theorem ModuloEquivalent.client_firing [DecidableEq O] (c : Client O) {C D : Configuration T O}
    (h : ModuloEquivalent A label c.escaped C D) {f : Firing T S O} (valid : f.Valid A label C)
    (reads : IsSemantic A f) (avoids : ∀ r ∈ f.selection.made, r ∉ D.present) :
    ∃ π : O ≃ O, (f.rename π).Valid A label D ∧
      JointModuloEquivalent A label c.escaped (f.result label C, c.watch [f])
        ((f.rename π).result label D, c.watch [f.rename π]) := by
  obtain ⟨π, k, same, support⟩ := h.supported
  obtain ⟨admits, kResult, sameResult⟩ := modulo_step_witness k same
    (fun r member => support r (made_fresh valid member) (avoids r member)) reads
  exact ⟨π, admits.mpr valid, π, kResult, sameResult,
    c.watch_rename (fun o member => k.fixes o member) [f]⟩

/-- **Semantic firings preserve the client equivalence**, given a fresh supply of the made labels. -/
theorem ModuloEquivalent.client_counterpart [DecidableEq O] (c : Client O) {C D : Configuration T O}
    (h : ModuloEquivalent A label c.escaped C D) {f : Firing T S O} (valid : f.Valid A label C)
    (reads : IsSemantic A f)
    (supply : ∀ r ∈ f.selection.made, ∀ G : Finset O, ∃ o, o ∉ G ∧ label o = label r) :
    ∃ τ : O ≃ O, (f.rename τ).Valid A label D ∧
      JointModuloEquivalent A label c.escaped (f.result label C, c.watch [f])
        ((f.rename τ).result label D, c.watch [f.rename τ]) := by
  obtain ⟨τ, admitted, k, same⟩ := h.semantic_counterpart_witness valid reads supply
  exact ⟨τ, admitted, τ, k, same, c.watch_rename (fun o member => k.fixes o member) [f]⟩

end Firings

#print axioms sighted_rename
#print axioms runSighted_rename
#print axioms Client.watch_rename
#print axioms Client.escaped_rename
#print axioms ModuloProbe.names_rename
#print axioms ModuloProbe.observes_congr
#print axioms ModuloProbe.observes_renameConfiguration
#print axioms JointModuloEquivalent.respects
#print axioms modulo_step_witness
#print axioms ModuloEquivalent.semantic_counterpart_witness
#print axioms ModuloEquivalent.client_firing
#print axioms ModuloEquivalent.client_counterpart

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation
