import Mettapedia.Logic.TheoryModel.Basic

/-!
# Universes hosting models

A universe is a class `U` of candidate structures available to host models.
The models of a theory hosted by `U` and the consequences computed in `U` are

* `modelsIn Sat U T = U ∩ models Sat T`;
* `consequencesIn Sat U T = theoryOf Sat (modelsIn Sat U T)`.

A larger universe hosts more models and validates fewer sentences. Every
universe validates at least the consequences computed in the largest universe;
`U` hosts `T` faithfully when it validates exactly those. Faithful hosting is
inherited by larger universes, holds for every theory when every structure has
an elementarily equivalent twin in `U`, and, for decidable satisfaction, holds
as soon as every non-consequence has a countermodel in `U`. The converse
countermodel direction is classical and is isolated in
`countermodel_of_hostsFaithfully`.

A map of structures that preserves and reflects satisfaction embeds one
universe of structures into another; the consequences computed in the target
are then among those computed in the source.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel

open Set

universe uStr uSent uStr'

variable {Str : Type uStr} {Sent : Type uSent} (Sat : Str → Sent → Prop)

/-- The models of `T` hosted by the universe `U`. -/
def modelsIn (U : Set Str) (T : Set Sent) : Set Str :=
  U ∩ models Sat T

/-- The consequences of `T` computed in the universe `U`. -/
def consequencesIn (U : Set Str) (T : Set Sent) : Set Sent :=
  theoryOf Sat (modelsIn Sat U T)

/-- `U` hosts `T` faithfully when the consequences of `T` computed in `U` are
exactly its consequences computed in the largest universe. -/
def HostsFaithfully (U : Set Str) (T : Set Sent) : Prop :=
  consequencesIn Sat U T = theoryOf Sat (models Sat T)

variable {Sat}

theorem modelsIn_univ (T : Set Sent) : modelsIn Sat univ T = models Sat T :=
  univ_inter _

theorem consequencesIn_univ (T : Set Sent) :
    consequencesIn Sat univ T = theoryOf Sat (models Sat T) := by
  rw [consequencesIn, modelsIn_univ]

/-- **A larger universe hosts more models.** -/
theorem modelsIn_mono {U U' : Set Str} (included : U ⊆ U') (T : Set Sent) :
    modelsIn Sat U T ⊆ modelsIn Sat U' T :=
  fun _ member => ⟨included member.1, member.2⟩

/-- A larger universe validates fewer sentences. -/
theorem consequencesIn_anti {U U' : Set Str} (included : U ⊆ U') (T : Set Sent) :
    consequencesIn Sat U' T ⊆ consequencesIn Sat U T :=
  theoryOf_anti (modelsIn_mono included T)

/-- A stronger theory has fewer hosted models in every universe. -/
theorem modelsIn_anti_theory (U : Set Str) {T T' : Set Sent} (included : T ⊆ T') :
    modelsIn Sat U T' ⊆ modelsIn Sat U T :=
  fun _ member => ⟨member.1, models_anti included member.2⟩

/-- Every universe validates the theory itself. -/
theorem subset_consequencesIn (U : Set Str) (T : Set Sent) : T ⊆ consequencesIn Sat U T :=
  fun _ member _ hosted => hosted.2 member

/-- Every universe validates at least the consequences computed in the largest
universe. -/
theorem consequences_subset_consequencesIn (U : Set Str) (T : Set Sent) :
    theoryOf Sat (models Sat T) ⊆ consequencesIn Sat U T :=
  theoryOf_anti fun _ hosted => hosted.2

theorem hostsFaithfully_iff_subset {U : Set Str} {T : Set Sent} :
    HostsFaithfully Sat U T ↔ consequencesIn Sat U T ⊆ theoryOf Sat (models Sat T) :=
  ⟨fun equal => fun _ member => (show HostsFaithfully Sat U T from equal) ▸ member,
    fun included => Subset.antisymm included (consequences_subset_consequencesIn U T)⟩

/-- An unfaithful universe validates a sentence that the theory does not
entail. -/
theorem not_hostsFaithfully_of {U : Set Str} {T : Set Sent} {φ : Sent}
    (validated : φ ∈ consequencesIn Sat U T) (notEntailed : ¬ Entails Sat T φ) :
    ¬ HostsFaithfully Sat U T := by
  intro faithful
  unfold HostsFaithfully at faithful
  rw [faithful] at validated
  exact notEntailed validated

theorem hostsFaithfully_univ (T : Set Sent) : HostsFaithfully Sat univ T :=
  consequencesIn_univ T

/-- **Faithful hosting is inherited by larger universes.** -/
theorem HostsFaithfully.mono {U U' : Set Str} {T : Set Sent}
    (faithful : HostsFaithfully Sat U T) (included : U ⊆ U') : HostsFaithfully Sat U' T :=
  hostsFaithfully_iff_subset.mpr
    (Subset.trans (consequencesIn_anti included T) (hostsFaithfully_iff_subset.mp faithful))

/-- If every structure has an elementarily equivalent twin in `U`, then `U`
hosts every theory faithfully. -/
theorem hostsFaithfully_of_twins {U : Set Str}
    (twin : ∀ m, ∃ m' ∈ U, ∀ φ, Sat m' φ ↔ Sat m φ) (T : Set Sent) :
    HostsFaithfully Sat U T := by
  refine hostsFaithfully_iff_subset.mpr fun φ validated m model => ?_
  obtain ⟨m', hosted, equivalent⟩ := twin m
  have model' : m' ∈ models Sat T := fun ψ member => (equivalent ψ).mpr (model member)
  exact (equivalent φ).mp (validated ⟨hosted, model'⟩)

/-- For decidable satisfaction, a universe containing a countermodel for every
non-consequence hosts the theory faithfully. -/
theorem hostsFaithfully_of_countermodels [∀ m φ, Decidable (Sat m φ)]
    {U : Set Str} {T : Set Sent}
    (countermodel : ∀ ⦃m⦄, m ∈ models Sat T → ∀ ⦃φ⦄, ¬ Sat m φ →
      ∃ m' ∈ modelsIn Sat U T, ¬ Sat m' φ) :
    HostsFaithfully Sat U T := by
  refine hostsFaithfully_iff_subset.mpr fun φ validated m model => ?_
  by_cases holds : Sat m φ
  · exact holds
  · obtain ⟨m', hosted, refuted⟩ := countermodel model holds
    exact (refuted (validated hosted)).elim

open Classical in
/-- Classical converse: a faithful universe contains a countermodel for every
non-consequence. -/
theorem countermodel_of_hostsFaithfully {U : Set Str} {T : Set Sent}
    (faithful : HostsFaithfully Sat U T) {m : Str} (model : m ∈ models Sat T) {φ : Sent}
    (refuted : ¬ Sat m φ) : ∃ m' ∈ modelsIn Sat U T, ¬ Sat m' φ := by
  by_contra none
  apply refuted
  have validated : φ ∈ consequencesIn Sat U T := fun m' hosted =>
    byContradiction fun notSat => none ⟨m', hosted, notSat⟩
  rw [faithful] at validated
  exact validated model

/-! ## Embeddings of universes -/

section Embedding

variable {Str' : Type uStr'} {Sat' : Str' → Sent → Prop}

/-- Along a map of structures preserving and reflecting satisfaction, the
consequences computed in the target universe are among those computed in the
source universe: the target hosts at least the images of the source models. -/
theorem consequences_subset_of_embedding (f : Str → Str')
    (sat_iff : ∀ m φ, Sat' (f m) φ ↔ Sat m φ) (T : Set Sent) :
    theoryOf Sat' (models Sat' T) ⊆ theoryOf Sat (models Sat T) := by
  intro φ validated m model
  exact (sat_iff m φ).mp (validated fun ψ member => (sat_iff m ψ).mpr (model member))

/-- If moreover every target structure is elementarily equivalent to the image of
a source structure, the two universes compute the same consequences. -/
theorem consequences_eq_of_embedding (f : Str → Str')
    (sat_iff : ∀ m φ, Sat' (f m) φ ↔ Sat m φ)
    (twin : ∀ m', ∃ m, ∀ φ, Sat' (f m) φ ↔ Sat' m' φ) (T : Set Sent) :
    theoryOf Sat' (models Sat' T) = theoryOf Sat (models Sat T) := by
  refine Subset.antisymm (consequences_subset_of_embedding f sat_iff T) ?_
  intro φ validated m' model'
  obtain ⟨m, equivalent⟩ := twin m'
  have model : m ∈ models Sat T := fun ψ member =>
    (sat_iff m ψ).mp ((equivalent ψ).mpr (model' member))
  exact (equivalent φ).mp ((sat_iff m φ).mpr (validated model))

end Embedding

end Mettapedia.Logic.TheoryModel
