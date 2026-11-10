import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EscapeObservation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObserverRespect

/-!
# The one-frame instance with renamed occurrences, relative to what the environment recorded

The one-frame transport (`firstOrderTransport`) renames no occurrence. Here its isomorphisms are the
renamings of occurrence identities that keep every label and carry one configuration to the other up
to the solutions of its knowledge (`RenamingIso`), and firings move by renaming
(`renamingTransport`). It contains the one-frame transport (`RenamingIso.ofSame`), is natural
(`renamingNatural`), and its escape data records each sighted set as one relation
(`renamingEscape`).

* **Traces refine what every observer can observe** (`renaming_traceEquiv_equivariant`,
  `renaming_traceEquiv_observes`): trace-equivalent runs end in states related by a renaming that
  carries one end's record to the other's. Every frame probe observes at one end what its renaming
  observes at the other, and every probe the start's record supports observes the same at both.

## Controls (`ObserverControls`)

At `{5, 6}`, both labelled `0`, take one occurrence and sight both.

* **Positive** (`sighting_dissolved`): taking `5` and taking `6` are trace equivalent. The exchange of
  `5` and `6` relates the starts, and the ends, whose records both hold the sighted set `{5, 6}`,
  which the exchange carries to itself (`sighting_dissolved_ends`). This holds also when the record
  already holds that sighted set (`sighted_set_identified`).
* **Negative** (`held_distinguishes`, `pair_distinguishes`, `singleton_distinguishes`): an environment
  that holds a reference to `5`, sighted the ordered pair `(5, 6)`, or sighted `{5}` still tells them
  apart, since every automorphism of its record fixes `5` (`fixed_distinguishes`).
* **Negative** (`onto_other_refused`): at `{5, 6, 7}`, all labelled `0`, after sighting `{5, 6}`, the
  exchange of `6` and `7` is an isomorphism of the configuration and no escape-relative isomorphism
  renames by it: it carries the sighted set onto `{5, 7}`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Frames Transport Escaped FrameProbe RowIsoModulo ofConfiguration)
open Observation (Record querySightings)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO}

/-! ## Renaming firings -/

theorem renameQuery_refl : renameQuery (T := T) (S := S) (Equiv.refl O) = id := by
  funext query
  obtain ⟨region, seen⟩ := query
  simp [renameQuery]

theorem renameQuery_trans (π ρ : O ≃ O) :
    renameQuery (T := T) (S := S) (π.trans ρ) = renameQuery ρ ∘ renameQuery π := by
  funext query
  obtain ⟨region, seen⟩ := query
  simp [renameQuery, Finset.map_map, Equiv.trans_toEmbedding]

theorem Firing.rename_refl (f : Firing T S O) : f.rename (Equiv.refl O) = f := by
  obtain ⟨rule, queries, ⟨taken, read, made⟩⟩ := f
  simp [Firing.rename, renameSelection, renameQuery_refl]

theorem Firing.rename_trans (π ρ : O ≃ O) (f : Firing T S O) :
    f.rename (π.trans ρ) = (f.rename π).rename ρ := by
  obtain ⟨rule, queries, ⟨taken, read, made⟩⟩ := f
  simp [Firing.rename, renameSelection, renameQuery_trans, List.map_map]

/-! ## The transport -/

section Renaming

variable [DecidableEq O] (A : SubstitutionAction T S) (label : O → T)

/-- **An isomorphism of configurations that renames occurrences**: a bijection of occurrence
identities that keeps every label and carries the first configuration to the second, up to the
solutions of its knowledge. -/
structure RenamingIso (C D : Configuration T O) where
  rename : O ≃ O
  keeps : ∀ o, label (rename o) = label o
  same : SameUpTo A (renameConfiguration rename C) D

namespace RenamingIso

variable {A label}

/-- The interface's isomorphism of states, over the identity of the one frame. -/
def toStateIso {C D : Configuration T O} (i : RenamingIso A label C D) : (firstOrder A label).StateIso C D where
  frame := Frames.Iso.refl PUnit.unit
  knowledge := Frames.Equivalent.trans (Frames.Iso.equivalent_refl _) (fun _ σ => i.same.1 σ)
  rename := i.rename
  present := i.same.2

variable (A label) in
def refl (C : Configuration T O) : RenamingIso A label C C :=
  ⟨Equiv.refl O, fun _ => rfl, by rw [Observation.renameConfiguration_refl]; exact SameUpTo.refl A C⟩

def symm {C D : Configuration T O} (i : RenamingIso A label C D) : RenamingIso A label D C where
  rename := i.rename.symm
  keeps o := by
    have kept := i.keeps (i.rename.symm o)
    rw [Equiv.apply_symm_apply] at kept
    exact kept.symm
  same := by
    have back := Observation.sameUpTo_rename A i.rename.symm i.same
    rw [← Observation.renameConfiguration_trans, Equiv.self_trans_symm,
      Observation.renameConfiguration_refl] at back
    exact sameUpTo_symm A back

def trans {C D F : Configuration T O} (i : RenamingIso A label C D) (j : RenamingIso A label D F) :
    RenamingIso A label C F where
  rename := i.rename.trans j.rename
  keeps o := by rw [Equiv.trans_apply, j.keeps, i.keeps]
  same := by
    rw [Observation.renameConfiguration_trans]
    exact GuardFreeProcessOrders.SameUpTo.trans A (Observation.sameUpTo_rename A j.rename i.same) j.same

/-- **The one-frame transport's isomorphisms rename by the identity.** -/
def ofSame {C D : Configuration T O} (same : SameUpTo A C D) : RenamingIso A label C D :=
  ⟨Equiv.refl O, fun _ => rfl, by rw [Observation.renameConfiguration_refl]; exact same⟩

end RenamingIso

/-- **Transport in the one-frame instance, renaming occurrences.** -/
def renamingTransport : Transport (firstOrder A label).toStep where
  Iso C D := RenamingIso A label C D
  toStateIso i := i.toStateIso
  refl C := RenamingIso.refl A label C
  symm i := i.symm
  trans i j := i.trans j
  Alike f f' := f = f'
  alike_equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  selection_alike same := congrArg _ same
  admits_alike same := same ▸ Iff.rfl
  result_alike {C} {f} _ same _ _ := by
    subst same
    exact RenamingIso.refl A label _
  move i f := f.rename i.rename
  move_alike _ _ _ same := congrArg _ same
  move_refl f := Firing.rename_refl f
  move_trans i j f := Firing.rename_trans i.rename j.rename f
  move_symm i f := by
    show (f.rename i.rename).rename i.rename.symm = f
    rw [← Firing.rename_trans, Equiv.self_trans_symm, Firing.rename_refl]
  selection_move _ _ := rfl
  admits_move i f := Observation.valid_renamed i.keeps i.same f
  result_move i f _ := ⟨i.rename, i.keeps, Observation.result_renamed i.keeps i.same f⟩
  residual _ _ f := f
  selection_residual _ _ _ := rfl
  move_residual _ _ _ _ := rfl

/-- **The renaming transport is natural.** -/
theorem renamingNatural : (renamingTransport A label).Natural where
  refl _ := Frames.Agree.refl _
  symm _ := Frames.Agree.refl _
  trans _ _ := fun t => by
    show A.E (A.apply A.identity t) (A.apply (A.compose A.identity A.identity) t)
    simp only [A.apply_compose, A.apply_identity]
    exact A.equivalence.refl _
  result_move _ _ _ := fun t => by
    show A.E (A.apply (A.compose A.identity (A.compose A.identity A.identity)) t)
      (A.apply (A.compose (A.compose A.identity A.identity) A.identity) t)
    simp only [A.apply_compose, A.apply_identity]
    exact A.equivalence.refl _
  result_alike {C} {f} _ same _ _ := by
    subst same
    exact fun t => by
      show A.E (A.apply (A.compose A.identity (A.compose A.identity A.identity)) t)
        (A.apply (A.compose A.identity A.identity) t)
      simp only [A.apply_compose, A.apply_identity]
      exact A.equivalence.refl _
  rename_refl _ := rfl
  rename_symm _ := rfl
  rename_trans _ _ := rfl
  rename_result_move _ _ _ := rfl
  rename_result_alike {C} {f} _ same _ _ := by
    subst same
    rfl

/-- **What clients read and what a firing makes escape, with renamed occurrences**: the labels are
the rows, and a firing makes the environment record each set its predicate queries sighted. -/
def renamingEscape : (renamingTransport A label).Escape where
  row _ o := some (label o)
  row_iso i o := .some (Frames.Carried.of_E (by
    show A.E (A.apply A.identity (label o)) (label (i.rename o))
    rw [A.apply_identity, i.keeps]
    exact A.equivalence.refl _))
  records f := querySightings f.queries
  publishes _ _ := []
  records_move i f := Observation.querySightings_rename i.rename f.queries
  publishes_move _ _ _ := .nil
  records_alike {C} {f} _ same := by
    subst same
    rfl
  publishes_alike {C} {f} _ same _ _ := by
    subst same
    exact .nil

/-- The escape-relative transport of the one-frame instance, renaming occurrences. -/
abbrev renamingEscaping :=
  (renamingTransport A label).escaping (renamingNatural A label) (renamingEscape A label)

/-! ## Traces refine what every observer can observe -/

/-- **An isomorphism that renames occurrences is a row isomorphism modulo the knowledge** that fixes
no identity, with the same renaming. -/
def renamingIso_rowIsoModulo {C D : Configuration T O} (i : RenamingIso A label C D) :
    RowIsoModulo (∅ : Finset O) (ofConfiguration A label C) (ofConfiguration A label D) :=
  Interface.rowIsoModulo_of_renaming A label
    (Observation.RenamingUpTo.of_private ⟨i.keeps, fun _ absent => absurd absent (Finset.notMem_empty _)⟩)
    i.same

/-- **Trace-equivalent runs end in states related by a renaming that carries one end's record to the
other's, and every frame probe observes at one end what its renaming observes at the other.** -/
theorem renaming_traceEquiv_equivariant {x : Escaped (firstOrder A label).toStep}
    {r r' : (renamingEscape A label).step.Run x} (equivalent : (renamingEscaping A label).TraceEquiv x r r') :
    ∃ π : O ≃ O, Record.rename π r.last.record = r'.last.record ∧
      ∀ p : FrameProbe (Frames.ofSubstitution A) PUnit.unit O,
        p.Observes (ofConfiguration A label r.last.state) ↔
          (p.rename π).Observes (ofConfiguration A label r'.last.state) := by
  obtain ⟨i, carried⟩ := Transport.Escape.traceEquiv_record equivalent
  exact ⟨i.rename, carried, (renamingIso_rowIsoModulo A label i).observes_rename_iff⟩

/-- **Traces refine observation by every probe the start's record supports.** -/
theorem renaming_traceEquiv_observes {x : Escaped (firstOrder A label).toStep}
    {r r' : (renamingEscape A label).step.Run x} (equivalent : (renamingEscaping A label).TraceEquiv x r r')
    {p : FrameProbe (Frames.ofSubstitution A) PUnit.unit O} (supported : p.Supported x.record) :
    p.Observes (ofConfiguration A label r.last.state) ↔ p.Observes (ofConfiguration A label r'.last.state) := by
  obtain ⟨i, aut, -⟩ := Transport.Escape.traceEquiv_past equivalent
  exact FrameProbe.observes_iff_of_aut (renamingIso_rowIsoModulo A label i) aut supported

end Renaming

/-! ## Controls -/

namespace ObserverControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature)
open EscapeControls (blank twins seeAll takeFive swapTwins swapTwins_keeps twins_renamed takeFive_valid
  takeSix_valid)
open Observation.Record (sighting reference tuple automorphisms)

/-- The escape-relative transport of the controls. -/
abbrev escaping := renamingEscaping ConstraintMultisetRewriting.Controls.A blank

/-- The start `{5, 6}` with the environment's record `R`. -/
abbrev start (R : Record ℕ) : Escaped (firstOrder ConstraintMultisetRewriting.Controls.A blank).toStep :=
  ⟨twins, [], R⟩

/-- Take `5` and sight `{5, 6}`. -/
abbrev runFive (R : Record ℕ) : (renamingEscape ConstraintMultisetRewriting.Controls.A blank).step.Run (start R) :=
  .cons takeFive takeFive_valid (.nil _)

/-- Take `6` and sight `{5, 6}`. -/
abbrev runSix (R : Record ℕ) : (renamingEscape ConstraintMultisetRewriting.Controls.A blank).step.Run (start R) :=
  .cons (takeFive.rename swapTwins) takeSix_valid (.nil _)

/-- The exchange of `5` and `6`, as an isomorphism of the configuration. -/
def swapIso : RenamingIso ConstraintMultisetRewriting.Controls.A blank twins twins :=
  ⟨swapTwins, swapTwins_keeps, by rw [twins_renamed]; exact SameUpTo.refl _ twins⟩

/-- **The exchange relates the starts whenever it is an automorphism of the record.** -/
def startSwap {R : Record ℕ} (aut : swapTwins ∈ automorphisms R) : escaping.Iso (start R) (start R) :=
  ⟨swapIso, .nil, aut⟩

/-- **Taking `5` and taking `6` are trace equivalent whenever the exchange is an automorphism of the
record.** -/
theorem identified_of_aut {R : Record ℕ} (aut : swapTwins ∈ automorphisms R) :
    escaping.TraceEquiv (start R) (runFive R) (runSix R) :=
  .rel _ _ (.inr (Transport.Similar.single (startSwap aut) takeFive_valid takeSix_valid rfl))

/-- **The obstruction dissolves.** With nothing recorded before, taking `5` and taking `6`, both
sighting `{5, 6}`, are trace equivalent. -/
theorem sighting_dissolved : escaping.TraceEquiv (start []) (runFive []) (runSix []) :=
  identified_of_aut rfl

/-- **Both runs end with the record of the sighted set `{5, 6}`, and the exchange that relates their
ends carries it to itself.** -/
theorem sighting_dissolved_ends :
    (runFive []).last.record = [sighting {5, 6}] ∧ (runSix []).last.record = [sighting {5, 6}] ∧
      ((escaping.result_move (startSwap (R := []) rfl) takeFive takeFive_valid).base.rename = swapTwins) ∧
      swapTwins ∈ automorphisms [sighting ({5, 6} : Finset ℕ)] :=
  ⟨rfl, by decide, rfl, Observation.RecordControls.sighting_swap.1⟩

/-- **Already holding the sighted set changes nothing.** -/
theorem sighted_set_identified :
    escaping.TraceEquiv (start [sighting {5, 6}]) (runFive _) (runSix _) :=
  identified_of_aut Observation.RecordControls.sighting_swap.1

/-- **When every automorphism of the record fixes `5`, the two runs are told apart.** -/
theorem fixed_distinguishes {R : Record ℕ} (fixes : ∀ π ∈ automorphisms R, π 5 = 5) :
    ¬ escaping.TraceEquiv (start R) (runFive R) (runSix R) := by
  intro equivalent
  have similar := equivalent.similar_of_length_le_one (Nat.le_refl _)
  obtain ⟨i, moving, -⟩ := Transport.similar_cons_cons.mp similar
  have fixed : i.base.rename 5 = 5 := fixes _ (Observation.Record.mem_automorphisms.mpr i.record)
  change takeFive.rename i.base.rename = takeFive.rename swapTwins at moving
  have taken := congrArg (fun f : Firing (Term signature) (Subst signature) ℕ => f.selection.taken) moving
  have moved : i.base.rename 5 = 6 := by
    simpa [Firing.rename, renameSelection, takeFive, swapTwins] using taken
  rw [fixed] at moved
  exact absurd moved (by decide)

/-- **Holding a reference to `5` tells them apart.** -/
theorem held_distinguishes :
    ¬ escaping.TraceEquiv (start (Observation.Record.references [5])) (runFive _) (runSix _) :=
  fixed_distinguishes fun _ aut =>
    Observation.Record.references_rename_eq_iff.mp aut 5 (List.mem_singleton_self 5)

/-- **Sighting the ordered pair `(5, 6)` tells them apart.** -/
theorem pair_distinguishes : ¬ escaping.TraceEquiv (start [tuple [5, 6]]) (runFive _) (runSix _) :=
  fixed_distinguishes fun π aut => by
    have carried : Observation.Record.rename π [tuple [5, 6]] = [tuple [5, 6]] := aut
    simp only [Observation.Record.rename, List.map_cons, List.map_nil, List.cons.injEq, and_true,
      Observation.Record.renameEntry_tuple] at carried
    have same : [5, 6].map π = [5, 6] := Finset.singleton_inj.mp carried
    exact (List.cons.inj same).1

/-- **Sighting `{5}` alone tells them apart.** -/
theorem singleton_distinguishes : ¬ escaping.TraceEquiv (start [sighting {5}]) (runFive _) (runSix _) :=
  fixed_distinguishes fun π aut => by
    have carried : Observation.Record.rename π [sighting {5}] = [sighting {5}] := aut
    simp only [Observation.Record.rename, List.map_cons, List.map_nil, List.cons.injEq, and_true,
      Observation.Record.renameEntry_sighting, Finset.map_singleton, Equiv.coe_toEmbedding] at carried
    have same := Finset.map_injective Observation.Record.single carried
    exact Finset.singleton_inj.mp same

/-- Occurrences `5`, `6` and `7`, all labelled `0`, and no knowledge. -/
def triple : Configuration (Term signature) ℕ := ⟨[], {5, 6, 7}⟩

/-- The exchange of `6` and `7`. -/
abbrev swapLate : ℕ ≃ ℕ := Equiv.swap 6 7

/-- **The exchange of `6` and `7` is an isomorphism of the configuration.** -/
def lateIso : RenamingIso ConstraintMultisetRewriting.Controls.A blank triple triple :=
  ⟨swapLate, fun _ => rfl, by
    have renamed : renameConfiguration swapLate triple = triple := by
      show (⟨[], ({5, 6, 7} : Finset ℕ).map swapLate.toEmbedding⟩ : Configuration (Term signature) ℕ) =
        ⟨[], {5, 6, 7}⟩
      congr 1
      decide
    rw [renamed]
    exact SameUpTo.refl _ triple⟩

/-- **A renaming that carries the sighted set onto another set is refused**: after sighting `{5, 6}`,
no escape-relative isomorphism renames by the exchange of `6` and `7`, although it is an
isomorphism of the configuration. -/
theorem onto_other_refused :
    lateIso.rename = swapLate ∧
      ∀ i : escaping.Iso ⟨triple, [], [sighting {5, 6}]⟩ ⟨triple, [], [sighting {5, 6}]⟩,
        i.base.rename ≠ swapLate := by
  refine ⟨rfl, fun i same => ?_⟩
  have carried := i.record
  change Observation.Record.rename i.base.rename [sighting {5, 6}] = [sighting {5, 6}] at carried
  rw [same] at carried
  exact Observation.RecordControls.onto_other_refused.2 carried

end ObserverControls

#print axioms renameQuery_trans
#print axioms Firing.rename_refl
#print axioms Firing.rename_trans
#print axioms renamingTransport
#print axioms renamingNatural
#print axioms renamingEscape
#print axioms renamingIso_rowIsoModulo
#print axioms renaming_traceEquiv_equivariant
#print axioms renaming_traceEquiv_observes
#print axioms ObserverControls.identified_of_aut
#print axioms ObserverControls.sighting_dissolved
#print axioms ObserverControls.sighting_dissolved_ends
#print axioms ObserverControls.sighted_set_identified
#print axioms ObserverControls.fixed_distinguishes
#print axioms ObserverControls.held_distinguishes
#print axioms ObserverControls.pair_distinguishes
#print axioms ObserverControls.singleton_distinguishes
#print axioms ObserverControls.onto_other_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
