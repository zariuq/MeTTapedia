import Mettapedia.Logic.Propositions.Views
import Mettapedia.GSLT.Scope.PredicateDescent

/-!
# The views compared

Which view identifies which sentences, and which features of sentences are
thereby features of propositions.

**Order.**  The views form a diamond in the lattice of equivalence relations on
sentences.  The enriched view is the finest of the structured ones and is the
meet of the Fregean and the Russellian view (`ker_enriched_eq_inf`).  The
Fregean view refines the primary intension and the Russellian view refines the
secondary intension (`ker_fregean_le_ker_primary`,
`ker_russellian_le_ker_secondary`).

**What descends.**  A feature of sentences is a feature of the propositions of a
view when it factors through the view, in the sense of
`Mettapedia.GSLT.Core.NonFactorization`.  Being a priori factors through
Fregean propositions and primary intensions (`factors_fregean_aPriori`,
`factors_primary_aPriori`).  Being necessary factors through Russellian
propositions and sets of worlds (`factors_russellian_necessary`,
`factors_secondary_necessary`).  Enriched propositions carry both
(`factors_enriched_aPriori`, `factors_enriched_necessary`), and truth factors
through both intensions (`factors_primary_trueIn`, `factors_secondary_trueIn`).
That being a priori does *not* factor through the Russellian leg, nor necessity
through the Fregean leg, is shown by the examples of this directory.  A feature
that does not factor has two liftings to propositions, its image and its
universal image (`Mettapedia.GSLT.Scope.PredicateDescent`).

**The outcomes Chalmers reports** (*Constructing the World*, 2012, ch. 2 §2).
* Possible-worlds view: "all necessary truths express the same proposition"
  (`Necessary.secondary_eq`), "a proposition that is itself knowable a priori"
  (`secondary_mem_image_aPriori_of_necessary`): it is in the image of the a
  priori sentences.
* Russellian view: names for one thing can be exchanged without changing the
  proposition (`russellian_map_names`), so a true identity expresses the same
  proposition as a self-identity (`russellian_ident_eq_of_trueIn`) and that
  proposition is expressed by an a priori sentence
  (`russellian_ident_mem_image_aPriori`).
* Eliminative view: with no propositions, every thesis about all propositions
  holds vacuously (`eliminative_thesis`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Propositions

open Mettapedia.GSLT.Core.NonFactorization

universe uS uW uD uN uP

namespace Interpretation

variable {S : Type uS} {W : Type uW} {D : Type uD} {N : Type uN} {P : Type uP}
variable (I : Interpretation S W D N P)

/-! ## Factorizations -/

theorem primary_eq_scenarios_comp : I.primary = FregeanProposition.scenarios ∘ I.fregean :=
  funext fun sentence => (I.scenarios_fregean sentence).symm

theorem secondary_eq_worlds_comp (actual : S) :
    I.secondary actual = RussellianProposition.worlds ∘ I.russellian actual :=
  funext fun sentence => (I.worlds_russellian actual sentence).symm

theorem fregean_eq_comp_enriched (actual : S) :
    I.fregean = EnrichedProposition.fregean ∘ I.enriched actual :=
  funext fun sentence => (I.fregean_enriched actual sentence).symm

theorem russellian_eq_comp_enriched (actual : S) :
    I.russellian actual = EnrichedProposition.russellian ∘ I.enriched actual :=
  funext fun sentence => (I.russellian_enriched actual sentence).symm

/-! ## The order of the views -/

theorem ker_enriched_le_ker_fregean (actual : S) :
    Setoid.ker (I.enriched actual) ≤ Setoid.ker I.fregean := by
  intro first second same
  rw [Setoid.ker_def] at same ⊢
  rw [← I.fregean_enriched actual, ← I.fregean_enriched actual, same]

theorem ker_enriched_le_ker_russellian (actual : S) :
    Setoid.ker (I.enriched actual) ≤ Setoid.ker (I.russellian actual) := by
  intro first second same
  rw [Setoid.ker_def] at same ⊢
  rw [← I.russellian_enriched actual, ← I.russellian_enriched actual, same]

theorem ker_fregean_le_ker_primary : Setoid.ker I.fregean ≤ Setoid.ker I.primary := by
  intro first second same
  rw [Setoid.ker_def] at same ⊢
  rw [← I.scenarios_fregean, ← I.scenarios_fregean, same]

theorem ker_russellian_le_ker_secondary (actual : S) :
    Setoid.ker (I.russellian actual) ≤ Setoid.ker (I.secondary actual) := by
  intro first second same
  rw [Setoid.ker_def] at same ⊢
  rw [← I.worlds_russellian, ← I.worlds_russellian, same]

/-- **The enriched view is the meet of the Fregean and the Russellian view**:
two sentences express the same enriched proposition exactly when they express
the same Fregean and the same Russellian proposition. -/
theorem ker_enriched_eq_inf (actual : S) :
    Setoid.ker (I.enriched actual) = Setoid.ker I.fregean ⊓ Setoid.ker (I.russellian actual) := by
  refine le_antisymm
    (le_inf (I.ker_enriched_le_ker_fregean actual) (I.ker_enriched_le_ker_russellian actual)) ?_
  intro first second same
  rw [Setoid.inf_iff_and, Setoid.ker_def, Setoid.ker_def] at same
  rw [Setoid.ker_def]
  apply EnrichedProposition.fregean_russellian_injective
  simp only [I.fregean_enriched, I.russellian_enriched, same.1, same.2]

/-! ## What descends -/

theorem factors_primary_aPriori : Factors I.primary I.APriori :=
  ⟨fun intension => ∀ scenario, scenario ∈ intension, fun _ => rfl⟩

/-- **Being a priori is a feature of Fregean propositions.** -/
theorem factors_fregean_aPriori : Factors I.fregean I.APriori :=
  Factors.of_coarsening (fine := I.fregean) (coarsen := FregeanProposition.scenarios)
    (fun sentence => (I.scenarios_fregean sentence).symm) I.factors_primary_aPriori

theorem factors_enriched_aPriori (actual : S) : Factors (I.enriched actual) I.APriori :=
  Factors.of_coarsening (fine := I.enriched actual) (coarsen := EnrichedProposition.fregean)
    (fun sentence => (I.fregean_enriched actual sentence).symm) I.factors_fregean_aPriori

theorem factors_secondary_necessary (actual : S) :
    Factors (I.secondary actual) (I.Necessary actual) :=
  ⟨fun intension => ∀ world, world ∈ intension, fun _ => rfl⟩

/-- **Being necessary is a feature of Russellian propositions.** -/
theorem factors_russellian_necessary (actual : S) :
    Factors (I.russellian actual) (I.Necessary actual) :=
  Factors.of_coarsening (fine := I.russellian actual) (coarsen := RussellianProposition.worlds)
    (fun sentence => (I.worlds_russellian actual sentence).symm)
    (I.factors_secondary_necessary actual)

theorem factors_enriched_necessary (actual : S) :
    Factors (I.enriched actual) (I.Necessary actual) :=
  Factors.of_coarsening (fine := I.enriched actual) (coarsen := EnrichedProposition.russellian)
    (fun sentence => (I.russellian_enriched actual sentence).symm)
    (I.factors_russellian_necessary actual)

theorem factors_primary_trueIn (actual : S) : Factors I.primary (I.TrueIn actual) :=
  ⟨fun intension => actual ∈ intension, fun _ => rfl⟩

theorem factors_secondary_trueIn (actual : S) :
    Factors (I.secondary actual) (I.TrueIn actual) :=
  ⟨fun intension => I.world actual ∈ intension, fun _ => rfl⟩

/-! ## The possible-worlds view -/

theorem secondary_eq_univ_iff (actual : S) (sentence : Sentence N P) :
    I.secondary actual sentence = Set.univ ↔ I.Necessary actual sentence :=
  Set.eq_univ_iff_forall

/-- **All necessary truths express the same set of worlds.** -/
theorem Necessary.secondary_eq {actual : S} {first second : Sentence N P}
    (firstNecessary : I.Necessary actual first) (secondNecessary : I.Necessary actual second) :
    I.secondary actual first = I.secondary actual second := by
  rw [(I.secondary_eq_univ_iff actual first).mpr firstNecessary,
    (I.secondary_eq_univ_iff actual second).mpr secondNecessary]

/-- **On the possible-worlds view every necessary truth expresses a proposition
that some a priori sentence expresses.** -/
theorem secondary_mem_image_aPriori_of_necessary [Nonempty N] {actual : S}
    {sentence : Sentence N P} (necessary : I.Necessary actual sentence) :
    I.secondary actual sentence ∈ I.secondary actual '' {candidate | I.APriori candidate} :=
  let ⟨name⟩ := ‹Nonempty N›
  ⟨.ident name name, I.aPriori_ident_self name,
    Necessary.secondary_eq I (I.necessary_ident_self actual name) necessary⟩

/-! ## The Russellian view -/

/-- **Names for one thing can be exchanged** without changing the Russellian
proposition. -/
theorem russellian_map_names (actual : S) (rename : N → N)
    (coreferring : ∀ name, I.referent (rename name) actual = I.referent name actual)
    (sentence : Sentence N P) :
    I.russellian actual (Form.map rename id sentence) = I.russellian actual sentence := by
  unfold russellian
  rw [Form.map_map]
  congr 1
  exact funext coreferring

/-- A true identity expresses the same Russellian proposition as a
self-identity. -/
theorem russellian_ident_eq_of_trueIn {actual : S} {left right : N}
    (trueIn : I.TrueIn actual (.ident left right)) :
    I.russellian actual (.ident left right) = I.russellian actual (.ident left left) := by
  have same : I.referent left actual = I.referent right actual := trueIn
  simp only [russellian, Form.map, same]

/-- **On the Russellian view every true identity expresses a proposition that
some a priori sentence expresses.** -/
theorem russellian_ident_mem_image_aPriori {actual : S} {left right : N}
    (trueIn : I.TrueIn actual (.ident left right)) :
    I.russellian actual (.ident left right) ∈
      I.russellian actual '' {candidate | I.APriori candidate} :=
  ⟨.ident left left, I.aPriori_ident_self left, (I.russellian_ident_eq_of_trueIn trueIn).symm⟩

end Interpretation

/-! ## The eliminative view -/

/-- **With no propositions, every thesis about all propositions holds.** -/
theorem eliminative_thesis (thesis : PEmpty.{uS + 1} → Prop) : ∀ proposition, thesis proposition :=
  fun proposition => proposition.elim

end Mettapedia.Logic.Propositions
