import Mettapedia.Logic.LinearLogic.KnowledgeTensorProofTermsFree
import Mettapedia.Logic.LinearLogic.KnowledgeTensorProofTermsExchange
import Mettapedia.Logic.LinearLogic.KnowledgeTensorProofTermsShape
import Mettapedia.Logic.LinearLogic.KnowledgeTensorControls

/-!
# Controls for proof terms and their structural quotient

The system has two declarations. The teller tells a fact; the asker's guard asks for it.

* `the_admitted_order_is_typed`: the term that fires the teller beside the asker's premises and
  then the asker beside the teller's conclusions proves the sequent of the two.
* `the_exchanged_term_is_not_typed`: the term with the two uses exchanged, each framed by the
  other's atoms, proves nothing from the same source. The exchange of two uses relates a proof
  to a term that is no proof, so it is not sound as an equation of all terms.
* `the_two_orders_are_not_structurally_equal`: and it is not a structural equation.
* `the_admitted_order_has_a_proof_term`, `the_refused_order_has_no_proof_term`: the same two
  facts from the runs.
* `a_proof_and_its_framing_differ`: a proof and the same proof framed by an atom are both typed
  and have one readout, and are different modulo the structural equations. The hypothesis of one
  source in the readout theorem is needed.
* `forgetting_frames_reads_the_word`, `the_framed_uses_of_the_admitted_order`: the two
  interpretations of the admitted order.
* `adding_the_frame_size_is_no_frame_action`: an operation that does not fix the unit is not a
  frame action.
* `where_the_fact_is_known_both_orders_are_proofs`,
  `from_no_knowledge_the_orders_are_not_both_proofs`: where the fact is already known the two
  orders are proofs of one sequent; from no knowledge they are not both proofs, because the
  asker's guard waits for the tell.
* `the_exchanged_term_is_shaped`, `every_shaped_term_of_the_refused_order_is_the_same`: the
  exchanged term has the shape of a proof, and the readout theorem holds for it although it is
  no proof. `the_teller_has_no_shape_from_nothing`: from no atoms a use has no shape.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensorControls.ProofTerms

open KnowledgeTensor KnowledgeTensor.ProofTerm
open Item Decl

/-- The teller beside the asker's premises, then the asker beside the teller's conclusions. -/
def tellerThenAsker : ProofTerm Knowledge Item Decl :=
  .cut (.frame (askTell.premises asker) (.rule teller))
    (.frame (askTell.conclusions teller) (.rule asker))

/-- The two uses exchanged, each framed by the other's atoms. -/
def askerThenTeller : ProofTerm Knowledge Item Decl :=
  .cut (.frame (askTell.premises teller) (.rule asker))
    (.frame (askTell.conclusions asker) (.rule teller))

/-- **The admitted order is a proof.** -/
theorem the_admitted_order_is_typed :
    askTell.Typed tellerThenAsker Set.univ start
      (Set.univ ⊓ askTell.tell teller ⊓ askTell.tell asker) finish := by
  have first := System.Typed.frame (sys := askTell) (askTell.premises asker)
    (System.Typed.rule teller Set.univ True.intro)
  have second := System.Typed.frame (sys := askTell) (askTell.conclusions teller)
    (System.Typed.rule asker (Set.univ ⊓ askTell.tell teller) (fun _ member => member.1.2))
  rw [add_comm (askTell.premises asker)] at second
  have whole := System.Typed.cut first second
  rw [add_comm (askTell.premises teller)] at whole
  exact whole

/-- **The exchanged term is no proof.** -/
theorem the_exchanged_term_is_not_typed :
    ¬ ∃ (known : Knowledge) (after : Multiset Item),
      askTell.Typed askerThenTeller Set.univ start known after :=
  fun ⟨known, after, typed⟩ =>
    asker_first_is_refused ⟨known, after, System.Derives.run typed.derives⟩

/-- **The exchange is not a structural equation.** -/
theorem the_two_orders_are_not_structurally_equal : ¬ Eqv tellerThenAsker askerThenTeller :=
  not_eqv_of_readout_ne fun same => by
    have word : [teller, asker] = [asker, teller] := same
    exact Decl.noConfusion (List.cons.inj word).1

theorem the_admitted_order_has_a_proof_term :
    ∃ p : ProofTerm Knowledge Item Decl,
      askTell.Typed p Set.univ start (Set.univ ⊓ askTell.tell teller ⊓ askTell.tell asker)
        finish ∧ p.readout = [teller, asker] :=
  (System.typed_iff_run _ _ _ _ _).mpr teller_then_asker_runs

theorem the_refused_order_has_no_proof_term :
    ¬ ∃ (p : ProofTerm Knowledge Item Decl) (known : Knowledge) (after : Multiset Item),
      askTell.Typed p Set.univ start known after ∧ p.readout = [asker, teller] := by
  rintro ⟨p, known, after, typed, word⟩
  have run := System.Derives.run typed.derives
  rw [word] at run
  exact asker_first_is_refused ⟨known, after, run⟩

/-- **The admitted order equals its normal form, and any other proof with its readout.** -/
theorem every_proof_of_the_admitted_order_is_the_same {p : ProofTerm Knowledge Item Decl}
    {known : Knowledge} {after : Multiset Item}
    (typed : askTell.Typed p Set.univ start known after) (word : p.readout = [teller, asker]) :
    Eqv p tellerThenAsker :=
  (System.eqv_iff_readout typed the_admitted_order_is_typed).mpr word

theorem the_teller_is_typed :
    askTell.Typed (.rule teller) Set.univ (askTell.premises teller)
      (Set.univ ⊓ askTell.tell teller) (askTell.conclusions teller) :=
  System.Typed.rule teller Set.univ True.intro

theorem the_framed_teller_is_typed :
    askTell.Typed (.frame {a} (.rule teller)) Set.univ (askTell.premises teller + {a})
      (Set.univ ⊓ askTell.tell teller) (askTell.conclusions teller + {a}) :=
  System.Typed.frame {a} the_teller_is_typed

/-- **A proof and its framing have one readout and are different.** -/
theorem a_proof_and_its_framing_differ :
    (ProofTerm.frame ({a} : Multiset Item) (.rule teller) : ProofTerm Knowledge Item Decl).readout =
        (ProofTerm.rule teller : ProofTerm Knowledge Item Decl).readout ∧
      ¬ Eqv (.frame ({a} : Multiset Item) (.rule teller) : ProofTerm Knowledge Item Decl)
        (.rule teller) :=
  ⟨rfl, frame_rule_not_eqv_rule (Multiset.singleton_ne_zero a) teller⟩

/-- Forgetting the frames reads the word. -/
theorem forgetting_frames_reads_the_word {M : Type} [Monoid M] (leaf : Decl → M) :
    eval (FrameMonoid.forget Item M) leaf tellerThenAsker = leaf teller * leaf asker :=
  rfl

/-- The framed uses of the admitted order. -/
theorem the_framed_uses_of_the_admitted_order :
    tellerThenAsker.leaves =
      [(0 + askTell.premises asker, teller), (0 + askTell.conclusions teller, asker)] :=
  rfl

/-- **Adding the size of the frame is no frame action**: it does not fix the unit. -/
theorem adding_the_frame_size_is_no_frame_action :
    ¬ ∃ frames : FrameMonoid Item Nat, ∀ extra x, frames.act extra x = x + Multiset.card extra := by
  rintro ⟨frames, shape⟩
  have law := frames.act_one {a}
  rw [shape, Multiset.card_singleton] at law
  exact absurd law (by decide)

/-- **Where the fact is already known, the two orders are proofs of one sequent.** -/
theorem where_the_fact_is_known_both_orders_are_proofs :
    askTell.Typed (askTell.beside teller asker 0) {true}
        (askTell.premises teller + (askTell.premises asker + 0))
        ({true} ⊓ askTell.tell teller ⊓ askTell.tell asker)
        (askTell.conclusions asker + (askTell.conclusions teller + 0)) ∧
      askTell.Typed (askTell.beside asker teller 0) {true}
        (askTell.premises teller + (askTell.premises asker + 0))
        ({true} ⊓ askTell.tell teller ⊓ askTell.tell asker)
        (askTell.conclusions asker + (askTell.conclusions teller + 0)) :=
  System.exchange_typed teller asker 0 {true} True.intro (fun _ member => member.1)

/-- **From no knowledge the two orders are not both proofs**: the asker's guard waits for the
tell. -/
theorem from_no_knowledge_the_orders_are_not_both_proofs :
    ¬ ((∃ (known : Knowledge) (after : Multiset Item),
          askTell.Typed (askTell.beside teller asker 0) Set.univ
            (askTell.premises teller + (askTell.premises asker + 0)) known after) ∧
        ∃ (known : Knowledge) (after : Multiset Item),
          askTell.Typed (askTell.beside asker teller 0) Set.univ
            (askTell.premises teller + (askTell.premises asker + 0)) known after) := by
  intro both
  have asked := ((System.exchange_typed_iff (sys := askTell) teller asker 0 Set.univ).mp both).2
  have held : (Set.univ ⊓ Set.univ : Set Bool) ≤ {true} := asked
  have impossible : false = true :=
    held (show false ∈ (Set.univ ⊓ Set.univ : Set Bool) from ⟨True.intro, True.intro⟩)
  exact absurd impossible (by decide)

/-- **The exchanged term has the shape of a proof**: its atoms fit; only the guard refuses it. -/
theorem the_exchanged_term_is_shaped :
    askTell.Shaped askerThenTeller Set.univ start
      (Set.univ ⊓ askTell.tell asker ⊓ askTell.tell teller) finish := by
  have first : askTell.Shaped (.frame (askTell.premises teller) (.rule asker)) Set.univ
      (askTell.premises asker + askTell.premises teller) (Set.univ ⊓ askTell.tell asker)
      (askTell.conclusions asker + askTell.premises teller) :=
    System.Typed.frame (askTell.premises teller) (System.Typed.rule asker Set.univ True.intro)
  have second : askTell.Shaped (.frame (askTell.conclusions asker) (.rule teller))
      (Set.univ ⊓ askTell.tell asker) (askTell.premises teller + askTell.conclusions asker)
      (Set.univ ⊓ askTell.tell asker ⊓ askTell.tell teller)
      (askTell.conclusions teller + askTell.conclusions asker) :=
    System.Typed.frame (askTell.conclusions asker)
      (System.Typed.rule teller (Set.univ ⊓ askTell.tell asker) True.intro)
  rw [add_comm (askTell.premises teller)] at second
  have whole := System.Typed.cut first second
  rw [add_comm (askTell.conclusions teller)] at whole
  exact whole

/-- **The readout theorem holds for terms that are no proofs.** Every term with the shape of a
proof from the same atoms and the readout of the refused order is the exchanged term. -/
theorem every_shaped_term_of_the_refused_order_is_the_same {p : ProofTerm Knowledge Item Decl}
    {known known' : Knowledge} {after : Multiset Item}
    (shaped : askTell.Shaped p known start known' after) (word : p.readout = [asker, teller]) :
    Eqv p askerThenTeller :=
  (System.eqv_iff_readout_of_shaped shaped the_exchanged_term_is_shaped).mpr word

/-- **From no atoms a use has no shape.** -/
theorem the_teller_has_no_shape_from_nothing :
    ¬ ∃ (known known' : Knowledge) (after : Multiset Item),
      askTell.Shaped (.rule teller) known 0 known' after := by
  rintro ⟨known, known', after, shaped⟩
  have fits := (System.Run.fits (System.Derives.run shaped.derives)).1
  have small : askTell.unguarded.premises teller ≤ 0 := fits.1
  have empty : askTell.unguarded.premises teller = 0 := Multiset.le_zero.mp small
  have size : Multiset.card (askTell.unguarded.premises teller) = 1 := rfl
  rw [empty] at size
  exact absurd size (by decide)

end Mettapedia.Logic.LinearLogic.KnowledgeTensorControls.ProofTerms
