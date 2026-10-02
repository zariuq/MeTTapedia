import Mettapedia.Logic.Propositions.Scrutability

/-!
# Changing the space of scenarios

What is a priori, and how finely senses are individuated, depends on which
scenarios are taken to be open.  A reasoner who rules scenarios out has more a
priori truths and coarser senses; a reasoner who admits more scenarios has
fewer a priori truths and finer senses.  The dependence is monotone, and it is
the semantic side of the trade between a weak theory and a large class of
models (`Mettapedia.Logic.TheoryModel`).

* `Interpretation.pullback embed`: the interpretation seen from another
  space of scenarios, each of which is some scenario of the original space.
* Its primary intensions are preimages (`primary_pullback`) and its secondary
  intensions are unchanged (`secondary_pullback`).
* A priori truths and scrutability relations are preserved
  (`APriori.pullback`, `ScrutableFrom.pullback`), and sentences with one sense
  in the larger space have one sense in the smaller
  (`ker_fregean_le_ker_fregean_pullback`).
* When every original scenario is covered, nothing changes
  (`aPriori_pullback_iff`, `ker_fregean_pullback_eq`).

The morning-star example shows that leaving a scenario out makes more a priori
and merges senses (`MorningStar.identity_aPriori_oneBody`,
`MorningStar.fregean_identity_eq_oneBody`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Propositions

universe uS uS' uW uD uN uP

namespace Interpretation

variable {S : Type uS} {S' : Type uS'} {W : Type uW} {D : Type uD} {N : Type uN} {P : Type uP}
variable (I : Interpretation S W D N P)

/-- The interpretation seen from another space of scenarios; `embed` says
which scenario of the original space each new scenario is. -/
def pullback (embed : S' → S) : Interpretation S' W D N P where
  world := fun scenario => I.world (embed scenario)
  referent := fun name scenario => I.referent name (embed scenario)
  property := fun predicate scenario => I.property predicate (embed scenario)

theorem primary_pullback (embed : S' → S) (sentence : Sentence N P) :
    (I.pullback embed).primary sentence = embed ⁻¹' I.primary sentence :=
  rfl

theorem secondary_pullback (embed : S' → S) (actual : S') (sentence : Sentence N P) :
    (I.pullback embed).secondary actual sentence = I.secondary (embed actual) sentence :=
  rfl

/-- **Fewer scenarios, more a priori**: what is a priori stays a priori. -/
theorem APriori.pullback {sentence : Sentence N P} (aPriori : I.APriori sentence)
    (embed : S' → S) : (I.pullback embed).APriori sentence :=
  fun scenario => aPriori (embed scenario)

theorem aPriori_pullback_iff {embed : S' → S} (surjective : Function.Surjective embed)
    (sentence : Sentence N P) : (I.pullback embed).APriori sentence ↔ I.APriori sentence := by
  refine ⟨fun aPriori scenario => ?_, fun aPriori => APriori.pullback I aPriori embed⟩
  obtain ⟨preimage, rfl⟩ := surjective scenario
  exact aPriori preimage

/-- Scrutability relations are preserved. -/
theorem ScrutableFrom.pullback {base : Set (Sentence N P)} {sentence : Sentence N P}
    (scrutable : I.ScrutableFrom base sentence) (embed : S' → S) :
    (I.pullback embed).ScrutableFrom base sentence :=
  (I.pullback embed).scrutableFrom_iff.mpr fun scenario verifies =>
    I.scrutableFrom_iff.mp scrutable (embed scenario) verifies

/-- The Fregean proposition in the new space is the old one with every sense
restricted. -/
theorem fregean_pullback (embed : S' → S) (sentence : Sentence N P) :
    (I.pullback embed).fregean sentence =
      Form.map (fun sense : S → D => sense ∘ embed) (fun sense : S → Set D => sense ∘ embed)
        (I.fregean sentence) := by
  unfold fregean
  rw [Form.map_map]
  rfl

/-- **Fewer scenarios, coarser senses.** -/
theorem ker_fregean_le_ker_fregean_pullback (embed : S' → S) :
    Setoid.ker I.fregean ≤ Setoid.ker (I.pullback embed).fregean := by
  intro first second same
  rw [Setoid.ker_def] at same ⊢
  rw [I.fregean_pullback, I.fregean_pullback, same]

theorem ker_fregean_pullback_eq {embed : S' → S} (surjective : Function.Surjective embed) :
    Setoid.ker (I.pullback embed).fregean = Setoid.ker I.fregean := by
  refine le_antisymm ?_ (I.ker_fregean_le_ker_fregean_pullback embed)
  intro first second same
  rw [Setoid.ker_def] at same ⊢
  rw [I.fregean_pullback, I.fregean_pullback] at same
  exact Form.map_injective surjective.injective_comp_right surjective.injective_comp_right same

end Interpretation

end Mettapedia.Logic.Propositions
