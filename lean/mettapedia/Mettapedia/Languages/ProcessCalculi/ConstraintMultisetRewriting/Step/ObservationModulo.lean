import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObservationViews

/-!
# Rows modulo the knowledge: client-respecting equivalence and full abstraction

Private equivalence (`Observation.PrivatelyEquivalent`) relates rows by a renaming that keeps their
labels syntactically. Clients read labels only through the solutions of the knowledge, so two rows
whose labels the knowledge identifies cannot be told apart, yet private equivalence keeps them apart.
This module compares rows **modulo the knowledge**.

## Renamings up to an equivalence of labels

A **renaming up to `r`** (`RenamingUpTo r label E π`) is a bijection of occurrence identities that
fixes the escaped identities `E` and keeps every label up to the equivalence `r`. Private renamings
are the case where `r` is equality (`RenamingUpTo.of_private`), and a renaming up to `r` is a private
renaming of the classes (`RenamingUpTo.iff_private`). Two present sets are related by one exactly when
they agree on `E` and carry the same bag of classes (`exists_renamingUpTo_iff`); the renaming can be
chosen to move only identities present in one of the sets (`exists_supported_renamingUpTo`).

## Two equivalences of configurations

* **Equivalence modulo the knowledge** (`ModuloEquivalent`): one renaming, keeping labels up to the
  terms that the knowledge entails equal (`entailedSetoid`), carries the first configuration to the
  second, up to the solutions of the knowledge. It is an equivalence (`refl`, `symm`, `trans`),
  contains private equivalence (`PrivatelyEquivalent.modulo`), and is characterized by the solutions,
  the escaped identities present and the bag of entailed classes (`moduloEquivalent_iff`).
* **Pointwise equivalence** (`PointwiseEquivalent`): the same solutions, the same escaped identities
  present, and at every solution a renaming that keeps the labels up to what that solution
  identifies (`solutionSetoid`). The renaming may depend on the solution. Equivalence modulo the
  knowledge implies it (`ModuloEquivalent.pointwise`); the converse holds when the knowledge has a
  principal answer (`PointwiseEquivalent.modulo_of_principal`).

## Probes that read labels through solutions

A **region** (`Region`) is a Boolean test of terms at each solution that gives equal results on terms
the solution identifies. A **probe modulo the knowledge** (`ModuloProbe`) asks whether a held reference
is present, asks a guard at every solution (`Check`: an equation, an absence or a count), asks that a
region holds exactly the identities seen, or **tallies** a region: its number of present rows at every
solution, as a function of the solution.

* **Respect** (`PointwiseEquivalent.observes`, `ModuloEquivalent.observes`, `Client.respects_modulo`):
  a probe that names only escaped identities observes the same at equivalent states. The run layer's
  own probes are instances when their query regions read labels through solutions
  (`ModuloEquivalent.observes_probe`).
* **Full abstraction** (`pointwiseEquivalent_iff_observes`): two configurations are pointwise
  equivalent exactly when every permitted probe agrees on them. Equations recover the solutions,
  held references the escaped identities, and tallies the bag of classes at each solution
  (`card_classRegion`).
* **With a principal answer** (`moduloEquivalent_iff_observes_of_principal`): equivalence modulo the
  knowledge is fully abstract.

## Joint ends

A history leaves a client context. Joint ends are compared by one renaming of the state and the
context (`JointModuloEquivalent`); it is an equivalence that contains joint private equivalence
(`JointEquivalent.modulo`), keeps the number of evidence records (`evidence_card`), and for a common
client whose identities are fixed is equivalence modulo the knowledge (`jointModuloEquivalent_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

open AnnotatedRuns
open GuardFreeProcessOrders (SameUpTo)
open MeTTaCalculus.OccurrenceCommits (regionOf)

universe uT uS uO uU

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-! ## Renamings up to an equivalence of labels -/

section UpTo

variable {U : Type uU}

/-- **A renaming up to an equivalence `r` of labels**, relative to the escaped identities `E`: a
bijection of occurrence identities that keeps every label up to `r` and fixes every identity of
`E`. -/
structure RenamingUpTo (r : Setoid U) (label : O → U) (E : Finset O) (π : O ≃ O) : Prop where
  keeps : ∀ o, r (label (π o)) (label o)
  fixes : ∀ o ∈ E, π o = o

namespace RenamingUpTo

omit [DecidableEq O]

variable {r r' : Setoid U} {label : O → U} {E E' : Finset O} {π ρ : O ≃ O}

theorem refl : RenamingUpTo r label E (Equiv.refl O) :=
  ⟨fun o => r.refl' (label o), fun _ _ => rfl⟩

theorem symm (h : RenamingUpTo r label E π) : RenamingUpTo r label E π.symm := by
  refine ⟨fun o => ?_, fun o member => ?_⟩
  · have kept := h.keeps (π.symm o)
    rw [Equiv.apply_symm_apply] at kept
    exact r.symm' kept
  · rw [Equiv.symm_apply_eq]
    exact (h.fixes o member).symm

theorem trans (h : RenamingUpTo r label E π) (k : RenamingUpTo r label E ρ) :
    RenamingUpTo r label E (π.trans ρ) :=
  ⟨fun o => r.trans' (k.keeps (π o)) (h.keeps o), fun o member => by
    rw [Equiv.trans_apply, h.fixes o member, k.fixes o member]⟩

theorem mono (h : RenamingUpTo r label E π) (fewer : E' ⊆ E) : RenamingUpTo r label E' π :=
  ⟨h.keeps, fun o member => h.fixes o (fewer member)⟩

/-- **A coarser equivalence of labels admits more renamings.** -/
theorem weaken (h : RenamingUpTo r label E π) (coarser : r ≤ r') : RenamingUpTo r' label E π :=
  ⟨fun o => Setoid.le_def.mp coarser (h.keeps o), h.fixes⟩

/-- **A private renaming is a renaming up to every equivalence.** -/
theorem of_private (h : PrivateRenaming label E π) : RenamingUpTo r label E π :=
  ⟨fun o => by rw [h.keeps o], h.fixes⟩

/-- **A renaming up to `r` is a private renaming of the classes.** -/
theorem iff_private :
    RenamingUpTo r label E π ↔ PrivateRenaming (fun o => Quotient.mk r (label o)) E π :=
  ⟨fun h => ⟨fun o => Quotient.sound (h.keeps o), h.fixes⟩,
    fun h => ⟨fun o => Quotient.exact (h.keeps o), h.fixes⟩⟩

/-- An escaped identity is in a renamed set exactly when it is in the set. -/
theorem mem_map_iff (h : RenamingUpTo r label E π) {o : O} (escaped : o ∈ E) (P : Finset O) :
    o ∈ P.map π.toEmbedding ↔ o ∈ P :=
  (iff_private.mp h).mem_map_iff escaped P

end RenamingUpTo

/-- **A private renaming supported on the two sets**: as `exists_private_map`, and the renaming moves
no identity absent from both sets. -/
theorem exists_supported_map {label : O → U} {E : Finset O} :
    ∀ (n : ℕ) {P Q : Finset O}, (P \ Q).card = n → (∀ o ∈ E, o ∈ P ↔ o ∈ Q) →
      P.val.map label = Q.val.map label →
        ∃ π : O ≃ O, PrivateRenaming label E π ∧ P.map π.toEmbedding = Q ∧
          ∀ o, o ∉ P → o ∉ Q → π o = o
  | 0, P, Q, size, _, bags => by
      have sub : P ⊆ Q := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp size)
      have cards : P.card = Q.card := by
        have counted := congrArg Multiset.card bags
        simpa only [Multiset.card_map, Finset.card_val] using counted
      refine ⟨Equiv.refl O, .refl, ?_, fun _ _ _ => rfl⟩
      rw [Equiv.refl_toEmbedding, Finset.map_refl]
      exact Finset.eq_of_subset_of_card_le sub cards.ge
  | n + 1, P, Q, size, escaped, bags => by
      obtain ⟨c, inDiff⟩ := Finset.card_pos.mp (by rw [size]; exact Nat.succ_pos n)
      obtain ⟨inP, notQ⟩ := Finset.mem_sdiff.mp inDiff
      obtain ⟨d, inQ, notP, same⟩ := exists_partner bags inP notQ
      have privateC : c ∉ E := fun escapedC => notQ ((escaped c escapedC).mp inP)
      have privateD : d ∉ E := fun escapedD => notP ((escaped d escapedD).mpr inQ)
      have swapPrivate : PrivateRenaming label E (Equiv.swap c d) :=
        ⟨swap_keeps same, fun o member => Equiv.swap_apply_of_ne_of_ne
          (fun isC => privateC (isC ▸ member)) (fun isD => privateD (isD ▸ member))⟩
      have moved : ∀ o, o ∈ P.map (Equiv.swap c d).toEmbedding ↔ Equiv.swap c d o ∈ P := by
        intro o
        rw [Finset.mem_map_equiv, Equiv.symm_swap]
      have smaller : (P.map (Equiv.swap c d).toEmbedding \ Q).card = n := by
        have diff : P.map (Equiv.swap c d).toEmbedding \ Q = (P \ Q).erase c := by
          ext o
          rw [Finset.mem_sdiff, moved, Finset.mem_erase, Finset.mem_sdiff]
          by_cases isC : o = c
          · subst isC
            rw [Equiv.swap_apply_left]
            exact ⟨fun h => absurd h.1 notP, fun h => absurd rfl h.1⟩
          · by_cases isD : o = d
            · subst isD
              rw [Equiv.swap_apply_right]
              exact ⟨fun h => absurd inQ h.2, fun h => absurd inQ h.2.2⟩
            · rw [Equiv.swap_apply_of_ne_of_ne isC isD]
              exact ⟨fun h => ⟨isC, h⟩, fun h => h.2⟩
        rw [diff, Finset.card_erase_of_mem inDiff, size]
        rfl
      have stillEscaped : ∀ o ∈ E, o ∈ P.map (Equiv.swap c d).toEmbedding ↔ o ∈ Q := by
        intro o member
        rw [moved, swapPrivate.fixes o member]
        exact escaped o member
      have stillBags : (P.map (Equiv.swap c d).toEmbedding).val.map label = Q.val.map label := by
        rw [labels_rename swapPrivate.keeps]
        exact bags
      obtain ⟨ρ, privateρ, onto, support⟩ := exists_supported_map n smaller stillEscaped stillBags
      refine ⟨(Equiv.swap c d).trans ρ, swapPrivate.trans privateρ, ?_, fun o notInP notInQ => ?_⟩
      · rw [Equiv.trans_toEmbedding, ← Finset.map_map, onto]
      · have notC : o ≠ c := fun isC => notInP (isC ▸ inP)
        have notD : o ≠ d := fun isD => notInQ (isD ▸ inQ)
        have fixed : Equiv.swap c d o = o := Equiv.swap_apply_of_ne_of_ne notC notD
        rw [Equiv.trans_apply, fixed]
        exact support o (fun member => notInP (by rwa [moved, fixed] at member)) notInQ

variable (r : Setoid U) (label : O → U) (E : Finset O)

/-- **Two present sets are related by a renaming up to `r`** exactly when they agree on the escaped
identities and carry the same bag of classes; the renaming can be chosen to move only identities
present in one of the sets. -/
theorem exists_supported_renamingUpTo {P Q : Finset O} (escaped : ∀ o ∈ E, o ∈ P ↔ o ∈ Q)
    (bags : P.val.map (fun o => Quotient.mk r (label o)) =
      Q.val.map (fun o => Quotient.mk r (label o))) :
    ∃ π : O ≃ O, RenamingUpTo r label E π ∧ P.map π.toEmbedding = Q ∧
      ∀ o, o ∉ P → o ∉ Q → π o = o := by
  obtain ⟨π, priv, onto, support⟩ := exists_supported_map _ rfl escaped bags
  exact ⟨π, RenamingUpTo.iff_private.mpr priv, onto, support⟩

theorem exists_renamingUpTo_iff (P Q : Finset O) :
    (∃ π : O ≃ O, RenamingUpTo r label E π ∧ P.map π.toEmbedding = Q) ↔
      (∀ o ∈ E, o ∈ P ↔ o ∈ Q) ∧
        P.val.map (fun o => Quotient.mk r (label o)) = Q.val.map (fun o => Quotient.mk r (label o)) := by
  constructor
  · rintro ⟨π, h, onto⟩
    refine ⟨fun o escaped => ?_, ?_⟩
    · rw [← onto]
      exact (h.mem_map_iff escaped P).symm
    · rw [← onto]
      exact (labels_rename (RenamingUpTo.iff_private.mp h).keeps P).symm
  · rintro ⟨escaped, bags⟩
    obtain ⟨π, h, onto, -⟩ := exists_supported_renamingUpTo r label E escaped bags
    exact ⟨π, h, onto⟩

end UpTo

/-! ## What the knowledge identifies -/

section Knowledge

variable (A : SubstitutionAction T S)

/-- **Terms equal at every solution of the knowledge.** -/
def Entailed (K : EquationStore T) (s t : T) : Prop :=
  A.Entails K fun σ => A.Solves σ (s, t)

/-- **The equivalence of terms that the knowledge entails.** -/
def entailedSetoid (K : EquationStore T) : Setoid T where
  r := Entailed A K
  iseqv := ⟨fun _ _ _ => A.equivalence.refl _,
    fun h σ solved => A.equivalence.symm (h σ solved),
    fun h k σ solved => A.equivalence.trans (h σ solved) (k σ solved)⟩

/-- **The equivalence of terms that one solution identifies.** -/
def solutionSetoid (σ : S) : Setoid T where
  r s t := A.Solves σ (s, t)
  iseqv := ⟨fun _ => A.equivalence.refl _, fun h => A.equivalence.symm h,
    fun h k => A.equivalence.trans h k⟩

variable {A}

/-- Stores with the same solutions entail the same equalities. -/
theorem entailedSetoid_congr {K K' : EquationStore T} (same : A.Equivalent K K') :
    entailedSetoid A K = entailedSetoid A K' :=
  Setoid.ext fun _ _ => forall_congr' fun σ => imp_congr_left (same σ)

/-- **A stronger store entails more equalities.** -/
theorem entailedSetoid_mono {K K' : EquationStore T} (refines : A.Refines K' K) :
    entailedSetoid A K ≤ entailedSetoid A K' :=
  Setoid.le_def.mpr fun entailed σ solved => entailed σ (refines σ solved)

/-- What the knowledge entails, each of its solutions identifies. -/
theorem entailedSetoid_le_solution {K : EquationStore T} {σ : S} (solved : A.Models σ K) :
    entailedSetoid A K ≤ solutionSetoid A σ :=
  Setoid.le_def.mpr fun entailed => entailed σ solved

/-- **What a principal answer identifies, the knowledge entails.** -/
theorem solution_le_entailedSetoid {K : EquationStore T} {answer : S}
    (principal : A.Principal K answer) : solutionSetoid A answer ≤ entailedSetoid A K := by
  refine Setoid.le_def.mpr fun {s t} same δ solved => ?_
  obtain ⟨residual, through⟩ := principal.factors δ solved
  have identified : A.E (A.apply answer s) (A.apply answer t) := same
  have later := A.preserves residual identified
  rw [← A.apply_compose, ← A.apply_compose] at later
  exact A.equivalence.trans (through s) (A.equivalence.trans later (A.equivalence.symm (through t)))

theorem entailedSetoid_eq_of_principal {K : EquationStore T} {answer : S}
    (principal : A.Principal K answer) : entailedSetoid A K = solutionSetoid A answer :=
  le_antisymm (entailedSetoid_le_solution principal.sound) (solution_le_entailedSetoid principal)

end Knowledge

/-! ## Equivalence modulo the knowledge -/

section Modulo

variable (A : SubstitutionAction T S) (label : O → T) (E : Finset O)

/-- **Equivalence modulo the knowledge relative to the escaped identities `E`**: a renaming that fixes
`E` and keeps every label up to what the knowledge entails carries the first configuration to the
second, up to the solutions of its knowledge. -/
def ModuloEquivalent (C D : Configuration T O) : Prop :=
  ∃ π : O ≃ O, RenamingUpTo (entailedSetoid A C.equations) label E π ∧
    SameUpTo A (renameConfiguration π C) D

/-- **Pointwise equivalence**: the same solutions, the same escaped identities present, and at every
solution a renaming that fixes `E` and keeps the labels up to what that solution identifies. -/
def PointwiseEquivalent (C D : Configuration T O) : Prop :=
  A.Equivalent C.equations D.equations ∧ (∀ o ∈ E, o ∈ C.present ↔ o ∈ D.present) ∧
    ∀ σ, A.Models σ C.equations → ∃ π : O ≃ O, RenamingUpTo (solutionSetoid A σ) label E π ∧
      C.present.map π.toEmbedding = D.present

namespace ModuloEquivalent

variable {A label E}

omit [DecidableEq O] in
theorem refl (C : Configuration T O) : ModuloEquivalent A label E C C :=
  ⟨Equiv.refl O, .refl, by rw [renameConfiguration_refl]; exact SameUpTo.refl A C⟩

omit [DecidableEq O] in
theorem symm {C D : Configuration T O} (h : ModuloEquivalent A label E C D) :
    ModuloEquivalent A label E D C := by
  obtain ⟨π, k, same⟩ := h
  have equivalent : A.Equivalent C.equations D.equations := same.1
  refine ⟨π.symm, ?_, ?_⟩
  · rw [← entailedSetoid_congr equivalent]
    exact k.symm
  · have back := sameUpTo_rename A π.symm same
    rw [← renameConfiguration_trans, Equiv.self_trans_symm, renameConfiguration_refl] at back
    exact sameUpTo_symm A back

omit [DecidableEq O] in
theorem trans {C D F : Configuration T O} (h : ModuloEquivalent A label E C D)
    (k : ModuloEquivalent A label E D F) : ModuloEquivalent A label E C F := by
  obtain ⟨π, kπ, same⟩ := h
  obtain ⟨ρ, kρ, same'⟩ := k
  have equivalent : A.Equivalent C.equations D.equations := same.1
  rw [← entailedSetoid_congr equivalent] at kρ
  refine ⟨π.trans ρ, kπ.trans kρ, ?_⟩
  rw [renameConfiguration_trans]
  exact GuardFreeProcessOrders.SameUpTo.trans A (sameUpTo_rename A ρ same) same'

omit [DecidableEq O] in
theorem mono {E' : Finset O} {C D : Configuration T O} (h : ModuloEquivalent A label E C D)
    (fewer : E' ⊆ E) : ModuloEquivalent A label E' C D := by
  obtain ⟨π, k, same⟩ := h
  exact ⟨π, k.mono fewer, same⟩

omit [DecidableEq O] in
theorem solutions {C D : Configuration T O} (h : ModuloEquivalent A label E C D) :
    A.Equivalent C.equations D.equations := by
  obtain ⟨π, -, same⟩ := h
  exact same.1

omit [DecidableEq O] in
/-- **Escaped identities are fixed.** -/
theorem escaped_iff {C D : Configuration T O} (h : ModuloEquivalent A label E C D) {o : O}
    (escaped : o ∈ E) : o ∈ C.present ↔ o ∈ D.present := by
  obtain ⟨π, k, same⟩ := h
  rw [← same.2]
  exact (k.mem_map_iff escaped C.present).symm

omit [DecidableEq O] in
/-- **Multiplicity is kept.** -/
theorem card_eq {C D : Configuration T O} (h : ModuloEquivalent A label E C D) :
    C.present.card = D.present.card := by
  obtain ⟨π, -, same⟩ := h
  rw [← same.2]
  exact (Finset.card_map _).symm

end ModuloEquivalent

/-- Equivalence modulo the knowledge as a setoid on configurations. -/
def moduloSetoid : Setoid (Configuration T O) where
  r := ModuloEquivalent A label E
  iseqv := ⟨ModuloEquivalent.refl, ModuloEquivalent.symm, ModuloEquivalent.trans⟩

variable {A label E} in
omit [DecidableEq O] in
/-- **Equivalence modulo the knowledge contains private equivalence.** -/
theorem PrivatelyEquivalent.modulo {C D : Configuration T O}
    (h : PrivatelyEquivalent A label E C D) : ModuloEquivalent A label E C D := by
  obtain ⟨π, priv, same⟩ := h
  exact ⟨π, .of_private priv, same⟩

/-- **The view modulo the knowledge characterizes the equivalence**: the same solutions, the same
escaped identities present, and the same bag of entailed classes of labels. -/
theorem moduloEquivalent_iff (C D : Configuration T O) :
    ModuloEquivalent A label E C D ↔
      A.Equivalent C.equations D.equations ∧ (∀ o ∈ E, o ∈ C.present ↔ o ∈ D.present) ∧
        C.present.val.map (fun o => Quotient.mk (entailedSetoid A C.equations) (label o)) =
          D.present.val.map (fun o => Quotient.mk (entailedSetoid A C.equations) (label o)) := by
  constructor
  · rintro ⟨π, k, same⟩
    exact ⟨same.1, (exists_renamingUpTo_iff _ label E C.present D.present).mp ⟨π, k, same.2⟩⟩
  · rintro ⟨equivalent, view⟩
    obtain ⟨π, k, onto⟩ := (exists_renamingUpTo_iff _ label E C.present D.present).mpr view
    exact ⟨π, k, equivalent, onto⟩

variable {A label E} in
/-- **The renaming can be chosen supported on the present occurrences**: it moves no identity absent
from both states. -/
theorem ModuloEquivalent.supported {C D : Configuration T O} (h : ModuloEquivalent A label E C D) :
    ∃ π : O ≃ O, RenamingUpTo (entailedSetoid A C.equations) label E π ∧
      SameUpTo A (renameConfiguration π C) D ∧ ∀ o, o ∉ C.present → o ∉ D.present → π o = o := by
  obtain ⟨equivalent, escaped, bags⟩ := (moduloEquivalent_iff A label E C D).mp h
  obtain ⟨π, k, onto, support⟩ := exists_supported_renamingUpTo _ label E escaped bags
  exact ⟨π, k, ⟨equivalent, onto⟩, support⟩

/-- **The pointwise view characterizes pointwise equivalence**: the same solutions, the same escaped
identities present, and at every solution the same bag of the classes it identifies. -/
theorem pointwiseEquivalent_iff (C D : Configuration T O) :
    PointwiseEquivalent A label E C D ↔
      A.Equivalent C.equations D.equations ∧ (∀ o ∈ E, o ∈ C.present ↔ o ∈ D.present) ∧
        ∀ σ, A.Models σ C.equations →
          C.present.val.map (fun o => Quotient.mk (solutionSetoid A σ) (label o)) =
            D.present.val.map (fun o => Quotient.mk (solutionSetoid A σ) (label o)) := by
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨escaped, each⟩
    refine ⟨escaped, fun σ solved => ?_⟩
    exact ((exists_renamingUpTo_iff _ label E C.present D.present).mp (each σ solved)).2
  · rintro ⟨escaped, each⟩
    exact ⟨escaped, fun σ solved =>
      (exists_renamingUpTo_iff _ label E C.present D.present).mpr ⟨escaped, each σ solved⟩⟩

namespace PointwiseEquivalent

variable {A label E}

theorem refl (C : Configuration T O) : PointwiseEquivalent A label E C C :=
  (pointwiseEquivalent_iff A label E C C).mpr ⟨fun _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => rfl⟩

theorem symm {C D : Configuration T O} (h : PointwiseEquivalent A label E C D) :
    PointwiseEquivalent A label E D C := by
  obtain ⟨equivalent, escaped, bags⟩ := (pointwiseEquivalent_iff A label E C D).mp h
  exact (pointwiseEquivalent_iff A label E D C).mpr ⟨fun σ => (equivalent σ).symm,
    fun o member => (escaped o member).symm, fun σ solved => (bags σ ((equivalent σ).mpr solved)).symm⟩

theorem trans {C D F : Configuration T O} (h : PointwiseEquivalent A label E C D)
    (k : PointwiseEquivalent A label E D F) : PointwiseEquivalent A label E C F := by
  obtain ⟨equivalent, escaped, bags⟩ := (pointwiseEquivalent_iff A label E C D).mp h
  obtain ⟨equivalent', escaped', bags'⟩ := (pointwiseEquivalent_iff A label E D F).mp k
  exact (pointwiseEquivalent_iff A label E C F).mpr ⟨fun σ => (equivalent σ).trans (equivalent' σ),
    fun o member => (escaped o member).trans (escaped' o member),
    fun σ solved => (bags σ solved).trans (bags' σ ((equivalent σ).mp solved))⟩

omit [DecidableEq O] in
/-- **With a principal answer, pointwise equivalence is equivalence modulo the knowledge**: the
renaming at the principal answer serves every solution. -/
theorem modulo_of_principal {C D : Configuration T O} {answer : S}
    (principal : A.Principal C.equations answer) (h : PointwiseEquivalent A label E C D) :
    ModuloEquivalent A label E C D := by
  obtain ⟨π, k, onto⟩ := h.2.2 answer principal.sound
  exact ⟨π, k.weaken (solution_le_entailedSetoid principal), h.1, onto⟩

end PointwiseEquivalent

variable {A label E} in
omit [DecidableEq O] in
/-- **Equivalence modulo the knowledge is pointwise equivalence with one renaming for every
solution.** -/
theorem ModuloEquivalent.pointwise {C D : Configuration T O} (h : ModuloEquivalent A label E C D) :
    PointwiseEquivalent A label E C D := by
  obtain ⟨π, k, same⟩ := h
  refine ⟨same.1, fun o escaped => ?_, fun σ solved => ⟨π, k.weaken (entailedSetoid_le_solution solved),
    same.2⟩⟩
  rw [← same.2]
  exact (k.mem_map_iff escaped C.present).symm

omit [DecidableEq O] in
/-- **The two equivalences agree when the knowledge has a principal answer.** -/
theorem moduloEquivalent_iff_pointwise {C D : Configuration T O} {answer : S}
    (principal : A.Principal C.equations answer) :
    ModuloEquivalent A label E C D ↔ PointwiseEquivalent A label E C D :=
  ⟨ModuloEquivalent.pointwise, PointwiseEquivalent.modulo_of_principal principal⟩

end Modulo

/-! ## Probes that read labels through solutions -/

/-- **A region that reads labels through the solution**: a Boolean test of terms at each solution
that gives equal results on terms the solution identifies. -/
structure Region (A : SubstitutionAction T S) where
  test : S → T → Bool
  respects : ∀ σ {s t : T}, A.Solves σ (s, t) → test σ s = test σ t

/-- **A probe modulo the knowledge**: whether a held reference is present; a guard asked at every
solution; that a region holds exactly the identities seen, at every solution; or the number of
present rows in a region, at every solution, as a function of the solution. -/
inductive ModuloProbe (A : SubstitutionAction T S) (O : Type uO) where
  | present (reference : O)
  | check (guard : Check T)
  | ask (region : Region A) (seen : Finset O)
  | tally (region : Region A) (number : S → ℕ)

namespace ModuloProbe

variable {A : SubstitutionAction T S}

/-- The identities a probe names: the reference, or the identities the query claims to have seen. -/
def names : ModuloProbe A O → Finset O
  | present reference => {reference}
  | check _ => ∅
  | ask _ seen => seen
  | tally _ _ => ∅

variable (label : O → T)

/-- **What a probe observes at a configuration.** -/
def Observes : ModuloProbe A O → Configuration T O → Prop
  | present reference, C => reference ∈ C.present
  | check guard, C => A.Entails C.equations fun σ => guard.Holds A σ label C.present
  | ask region seen, C => A.Entails C.equations fun σ => regionOf label C.present (region.test σ) = seen
  | tally region number, C =>
      A.Entails C.equations fun σ => (regionOf label C.present (region.test σ)).card = number σ

end ModuloProbe

section Respect

variable {A : SubstitutionAction T S} {label : O → T} {σ : S} {π : O ≃ O}

omit [DecidableEq O] in
/-- **A region's rows follow a renaming that keeps labels up to the solution.** -/
theorem regionOf_map_upTo (keeps : ∀ o, A.Solves σ (label (π o), label o)) (region : Region A)
    (P : Finset O) :
    regionOf label (P.map π.toEmbedding) (region.test σ) =
      (regionOf label P (region.test σ)).map π.toEmbedding := by
  ext o
  simp only [regionOf, Finset.mem_filter, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨⟨a, member, rfl⟩, inside⟩
    exact ⟨a, ⟨member, by rwa [region.respects σ (keeps a)] at inside⟩, rfl⟩
  · rintro ⟨a, ⟨member, inside⟩, rfl⟩
    exact ⟨⟨a, member, rfl⟩, by rwa [region.respects σ (keeps a)]⟩

omit [DecidableEq O] in
/-- **A pattern's matches follow a renaming that keeps labels up to the solution.** -/
theorem matches_map_upTo (keeps : ∀ o, A.Solves σ (label (π o), label o)) (P : Finset O)
    (pattern : T) :
    Check.matches A σ label (P.map π.toEmbedding) pattern =
      (Check.matches A σ label P pattern).map π.toEmbedding := by
  classical
  ext o
  simp only [Check.matches, Finset.mem_filter, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨⟨a, member, rfl⟩, matched⟩
    exact ⟨a, ⟨member, A.equivalence.trans matched (keeps a)⟩, rfl⟩
  · rintro ⟨a, ⟨member, matched⟩, rfl⟩
    exact ⟨⟨a, member, rfl⟩, A.equivalence.trans matched (A.equivalence.symm (keeps a))⟩

omit [DecidableEq O] in
/-- **Guards follow a renaming that keeps labels up to the solution.** -/
theorem holds_map_upTo (keeps : ∀ o, A.Solves σ (label (π o), label o)) (P : Finset O)
    (guard : Check T) :
    guard.Holds A σ label (P.map π.toEmbedding) ↔ guard.Holds A σ label P := by
  cases guard with
  | equal left right => exact Iff.rfl
  | absent pattern =>
      constructor
      · intro absent o member matched
        exact absent _ (Finset.mem_map_of_mem π.toEmbedding member)
          (A.equivalence.trans matched (A.equivalence.symm (keeps o)))
      · intro absent o member matched
        obtain ⟨a, inside, rfl⟩ := Finset.mem_map.mp member
        exact absent a inside (A.equivalence.trans matched (keeps a))
  | count pattern number =>
      show (Check.matches A σ label (P.map π.toEmbedding) pattern).card = number ↔
        (Check.matches A σ label P pattern).card = number
      rw [matches_map_upTo keeps, Finset.card_map]

variable {E : Finset O}

omit [DecidableEq O] in
/-- **Clients respect pointwise equivalence**: a probe that names only escaped identities observes
the same at pointwise equivalent states. -/
theorem PointwiseEquivalent.observes {C D : Configuration T O}
    (h : PointwiseEquivalent A label E C D) {p : ModuloProbe A O} (named : p.names ⊆ E) :
    p.Observes label C ↔ p.Observes label D := by
  obtain ⟨equivalent, escaped, each⟩ := h
  have atSolutions : ∀ {property : S → Finset O → Prop},
      (∀ σ, A.Models σ C.equations → ∀ π : O ≃ O, RenamingUpTo (solutionSetoid A σ) label E π →
        (property σ (C.present.map π.toEmbedding) ↔ property σ C.present)) →
      ((A.Entails C.equations fun σ => property σ C.present) ↔
        (A.Entails D.equations fun σ => property σ D.present)) := by
    intro property moved
    refine forall_congr' fun σ => ⟨fun asked solvedD => ?_, fun asked solvedC => ?_⟩
    · have solvedC := (equivalent σ).mpr solvedD
      obtain ⟨π, k, onto⟩ := each σ solvedC
      rw [← onto]
      exact (moved σ solvedC π k).mpr (asked solvedC)
    · obtain ⟨π, k, onto⟩ := each σ solvedC
      have there := asked ((equivalent σ).mp solvedC)
      rw [← onto] at there
      exact (moved σ solvedC π k).mp there
  cases p with
  | present reference =>
      exact escaped reference (named (Finset.mem_singleton_self reference))
  | check guard =>
      exact atSolutions (property := fun σ P => guard.Holds A σ label P)
        fun σ _ π k => holds_map_upTo k.keeps C.present guard
  | ask region seen =>
      refine atSolutions (property := fun σ P => regionOf label P (region.test σ) = seen)
        fun σ _ π k => ?_
      have fixed : seen.map π.toEmbedding = seen :=
        finset_map_eq_self π fun o member => k.fixes o (named member)
      show regionOf label (C.present.map π.toEmbedding) (region.test σ) = seen ↔
        regionOf label C.present (region.test σ) = seen
      rw [regionOf_map_upTo k.keeps region C.present]
      constructor
      · intro moved
        exact Finset.map_injective π.toEmbedding (moved.trans fixed.symm)
      · intro unmoved
        rw [unmoved, fixed]
  | tally region number =>
      refine atSolutions (property := fun σ P => (regionOf label P (region.test σ)).card = number σ)
        fun σ _ π k => ?_
      show (regionOf label (C.present.map π.toEmbedding) (region.test σ)).card = number σ ↔
        (regionOf label C.present (region.test σ)).card = number σ
      rw [regionOf_map_upTo k.keeps region C.present, Finset.card_map]

omit [DecidableEq O] in
/-- **Clients respect equivalence modulo the knowledge.** -/
theorem ModuloEquivalent.observes {C D : Configuration T O}
    (h : ModuloEquivalent A label E C D) {p : ModuloProbe A O} (named : p.names ⊆ E) :
    p.Observes label C ↔ p.Observes label D :=
  h.pointwise.observes named

omit [DecidableEq O] in
/-- **The run layer's probes, when their query regions read labels through solutions, respect
equivalence modulo the knowledge.** -/
theorem ModuloEquivalent.observes_probe {C D : Configuration T O}
    (h : ModuloEquivalent A label E C D) {p : Probe T S O} (named : p.names ⊆ E)
    (reads : ∀ query, p = .ask query → ∀ σ {s t : T}, A.Solves σ (s, t) →
      query.region σ s = query.region σ t) :
    p.Observes A label C ↔ p.Observes A label D := by
  cases p with
  | present reference =>
      exact h.observes (p := .present reference) named
  | check guard =>
      exact h.observes (p := .check guard) named
  | ask query =>
      exact h.observes (p := .ask ⟨query.region, reads query rfl⟩ query.seen) named

/-- **Every permitted client observes the same at states equivalent modulo the knowledge for it.** -/
theorem Client.respects_modulo (c : Client O) {C D : Configuration T O}
    (h : ModuloEquivalent A label c.escaped C D) {p : ModuloProbe A O} (permitted : p.names ⊆ c.escaped) :
    p.Observes label C ↔ p.Observes label D :=
  h.observes permitted

end Respect

/-! ## Joint ends -/

section Joint

variable (A : SubstitutionAction T S) (label : O → T) (E : Finset O)

/-- **Equivalence of joint ends modulo the knowledge**: a state with the client context its history
left. One renaming, fixing the identities `E` public before the comparison and keeping labels up to
what the first state's knowledge entails, relates the states and the client contexts. -/
def JointModuloEquivalent (x y : Configuration T O × Client O) : Prop :=
  ∃ π : O ≃ O, RenamingUpTo (entailedSetoid A x.1.equations) label E π ∧
    SameUpTo A (renameConfiguration π x.1) y.1 ∧ x.2.rename π = y.2

variable {A label E}

omit [DecidableEq O] in
theorem JointModuloEquivalent.refl (x : Configuration T O × Client O) :
    JointModuloEquivalent A label E x x :=
  ⟨Equiv.refl O, .refl, by rw [renameConfiguration_refl]; exact SameUpTo.refl A x.1,
    Client.rename_refl x.2⟩

omit [DecidableEq O] in
theorem JointModuloEquivalent.symm {x y : Configuration T O × Client O}
    (h : JointModuloEquivalent A label E x y) : JointModuloEquivalent A label E y x := by
  obtain ⟨π, k, same, clients⟩ := h
  have equivalent : A.Equivalent x.1.equations y.1.equations := same.1
  refine ⟨π.symm, ?_, ?_, ?_⟩
  · rw [← entailedSetoid_congr equivalent]
    exact k.symm
  · have back := sameUpTo_rename A π.symm same
    rw [← renameConfiguration_trans, Equiv.self_trans_symm, renameConfiguration_refl] at back
    exact sameUpTo_symm A back
  · rw [← clients, ← Client.rename_trans, Equiv.self_trans_symm, Client.rename_refl]

omit [DecidableEq O] in
theorem JointModuloEquivalent.trans {x y z : Configuration T O × Client O}
    (h : JointModuloEquivalent A label E x y) (k : JointModuloEquivalent A label E y z) :
    JointModuloEquivalent A label E x z := by
  obtain ⟨π, kπ, same, clients⟩ := h
  obtain ⟨ρ, kρ, same', clients'⟩ := k
  have equivalent : A.Equivalent x.1.equations y.1.equations := same.1
  rw [← entailedSetoid_congr equivalent] at kρ
  refine ⟨π.trans ρ, kπ.trans kρ, ?_, ?_⟩
  · rw [renameConfiguration_trans]
    exact GuardFreeProcessOrders.SameUpTo.trans A (sameUpTo_rename A ρ same) same'
  · rw [Client.rename_trans, clients, clients']

omit [DecidableEq O] in
/-- **Joint equivalence modulo the knowledge contains joint private equivalence.** -/
theorem JointEquivalent.modulo {x y : Configuration T O × Client O}
    (h : JointEquivalent A label E x y) : JointModuloEquivalent A label E x y := by
  obtain ⟨π, priv, same, clients⟩ := h
  exact ⟨π, .of_private priv, same, clients⟩

omit [DecidableEq O] in
/-- Joint equivalence forgets the client context to equivalence of the states. -/
theorem JointModuloEquivalent.states {x y : Configuration T O × Client O}
    (h : JointModuloEquivalent A label E x y) : ModuloEquivalent A label E x.1 y.1 := by
  obtain ⟨π, k, same, -⟩ := h
  exact ⟨π, k, same⟩

omit [DecidableEq O] in
/-- **Equivalent joint ends recorded the same number of identities as evidence.** -/
theorem JointModuloEquivalent.evidence_card {x y : Configuration T O × Client O}
    (h : JointModuloEquivalent A label E x y) : x.2.evidence.card = y.2.evidence.card := by
  obtain ⟨π, -, -, clients⟩ := h
  rw [← clients]
  exact (Finset.card_map _).symm

/-- **For one client whose identities are all fixed, joint equivalence modulo the knowledge is
equivalence modulo the knowledge.** -/
theorem jointModuloEquivalent_iff (c : Client O) (fixed : c.escaped ⊆ E) (C D : Configuration T O) :
    JointModuloEquivalent A label E (C, c) (D, c) ↔ ModuloEquivalent A label E C D := by
  constructor
  · rintro ⟨π, k, same, -⟩
    exact ⟨π, k, same⟩
  · rintro ⟨π, k, same⟩
    exact ⟨π, k, same, c.rename_eq_self fun o member => k.fixes o (fixed member)⟩

end Joint

/-! ## Full abstraction -/

section FullAbstraction

variable (A : SubstitutionAction T S)

open Classical in
/-- **The region of terms that a solution identifies with `t₀`.** -/
noncomputable def classRegion (t₀ : T) : Region A :=
  ⟨fun σ t => decide (A.Solves σ (t, t₀)), fun σ {s t} same => by
    rw [decide_eq_decide]
    exact ⟨fun h => A.equivalence.trans (A.equivalence.symm same) h,
      fun h => A.equivalence.trans same h⟩⟩

variable {A}

omit [DecidableEq O] in
/-- **A tally of a class region counts the class in the bag of classes at that solution.** -/
theorem card_classRegion (label : O → T) (σ : S) (t₀ : T) (P : Finset O)
    [DecidableEq (Quotient (solutionSetoid A σ))] :
    (regionOf label P ((classRegion A t₀).test σ)).card =
      Multiset.count (Quotient.mk (solutionSetoid A σ) t₀)
        (P.val.map fun o => Quotient.mk (solutionSetoid A σ) (label o)) := by
  classical
  rw [Multiset.count_map]
  show Multiset.card (P.filter fun o => (classRegion A t₀).test σ (label o) = true).val = _
  rw [Finset.filter_val]
  refine congrArg Multiset.card (Multiset.filter_congr fun o _ => ?_)
  simp only [classRegion, decide_eq_true_eq]
  exact ⟨fun h => Quotient.sound (A.equivalence.symm h), fun h => A.equivalence.symm (Quotient.exact h)⟩

variable (label : O → T) (E : Finset O)

/-- **Agreement of every permitted probe gives pointwise equivalence.** Equations recover the
solutions, held references the escaped identities, and tallies of class regions the bag of classes
at every solution. -/
theorem pointwiseEquivalent_of_observes {C D : Configuration T O}
    (agree : ∀ p : ModuloProbe A O, p.names ⊆ E → (p.Observes label C ↔ p.Observes label D)) :
    PointwiseEquivalent A label E C D := by
  have equation : ∀ e : Equation T, (ModuloProbe.check (Check.equal e.1 e.2) : ModuloProbe A O).names ⊆ E :=
    fun _ => Finset.empty_subset E
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
  have escaped : ∀ o ∈ E, o ∈ C.present ↔ o ∈ D.present := fun o member =>
    agree (.present o) (by simpa [ModuloProbe.names] using member)
  refine (pointwiseEquivalent_iff A label E C D).mpr ⟨equivalent, escaped, fun σ solved => ?_⟩
  classical
  refine Multiset.ext.mpr fun c => ?_
  obtain ⟨t₀, rfl⟩ := Quotient.exists_rep c
  rw [← card_classRegion, ← card_classRegion]
  have atC : (ModuloProbe.tally (classRegion A t₀)
      fun τ => (regionOf label C.present ((classRegion A t₀).test τ)).card).Observes label C :=
    fun _ _ => rfl
  have atD := (agree (.tally (classRegion A t₀)
    fun τ => (regionOf label C.present ((classRegion A t₀).test τ)).card) (Finset.empty_subset E)).mp atC
  exact (atD σ ((equivalent σ).mp solved)).symm

/-- **Full abstraction**: two configurations are pointwise equivalent exactly when every probe that
names only escaped identities observes the same at both. -/
theorem pointwiseEquivalent_iff_observes (C D : Configuration T O) :
    PointwiseEquivalent A label E C D ↔
      ∀ p : ModuloProbe A O, p.names ⊆ E → (p.Observes label C ↔ p.Observes label D) :=
  ⟨fun h _ named => h.observes named, pointwiseEquivalent_of_observes label E⟩

/-- **Full abstraction modulo the knowledge, when the knowledge has a principal answer.** -/
theorem moduloEquivalent_iff_observes_of_principal {C D : Configuration T O} {answer : S}
    (principal : A.Principal C.equations answer) :
    ModuloEquivalent A label E C D ↔
      ∀ p : ModuloProbe A O, p.names ⊆ E → (p.Observes label C ↔ p.Observes label D) :=
  (moduloEquivalent_iff_pointwise A label E principal).trans
    (pointwiseEquivalent_iff_observes label E C D)

end FullAbstraction

#print axioms RenamingUpTo.symm
#print axioms RenamingUpTo.trans
#print axioms RenamingUpTo.iff_private
#print axioms exists_supported_map
#print axioms exists_supported_renamingUpTo
#print axioms exists_renamingUpTo_iff
#print axioms entailedSetoid_congr
#print axioms entailedSetoid_mono
#print axioms solution_le_entailedSetoid
#print axioms entailedSetoid_eq_of_principal
#print axioms ModuloEquivalent.symm
#print axioms ModuloEquivalent.trans
#print axioms ModuloEquivalent.escaped_iff
#print axioms ModuloEquivalent.card_eq
#print axioms moduloSetoid
#print axioms PrivatelyEquivalent.modulo
#print axioms moduloEquivalent_iff
#print axioms ModuloEquivalent.supported
#print axioms pointwiseEquivalent_iff
#print axioms PointwiseEquivalent.symm
#print axioms PointwiseEquivalent.trans
#print axioms PointwiseEquivalent.modulo_of_principal
#print axioms ModuloEquivalent.pointwise
#print axioms moduloEquivalent_iff_pointwise
#print axioms regionOf_map_upTo
#print axioms matches_map_upTo
#print axioms holds_map_upTo
#print axioms PointwiseEquivalent.observes
#print axioms ModuloEquivalent.observes
#print axioms ModuloEquivalent.observes_probe
#print axioms Client.respects_modulo
#print axioms JointModuloEquivalent.symm
#print axioms JointModuloEquivalent.trans
#print axioms JointEquivalent.modulo
#print axioms JointModuloEquivalent.evidence_card
#print axioms jointModuloEquivalent_iff
#print axioms card_classRegion
#print axioms pointwiseEquivalent_of_observes
#print axioms pointwiseEquivalent_iff_observes
#print axioms moduloEquivalent_iff_observes_of_principal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation
