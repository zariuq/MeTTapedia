import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiMoleculeRepresentation
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiLeastPartnerControls

/-!
# Controls: representation independence of π molecules

- **Split or merged**: the sender `c<d>` and the receiver `c(y).0` as two molecules, or as one, are saturated bisimilar
  (`split_merged_bisimilar`). Their communication is a cross reaction in the first bag and an internal one in the
  second.
- **Renamed apart**: `(νv) c<v>` and `(νw) c<w>`, which send a restricted name, are saturated bisimilar
  (`renamed_sender_bisimilar`).
- **Negative**: `c<d>` and the inert process denote processes that are not congruent, and they are told apart
  (`Controls.publicOutput_not_inert`); so `c<d>` is not saturated reduction bisimilar to the inert process, a fact
  about π proved through molecules (`output_not_reduction_bisimilar_nil`).
- **Freshness is needed for renaming**: `(νa) (a<d> | b(y).0)` has no internal communication (`apartPair_still`);
  replacing `a` by the used name `b` creates one (`collidedPair_internal`) and is no renaming step
  (`rename_onto_used_name`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners.Controls

open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.GSLT.BagHennessyMilner (SaturatedBisimilarIn)

/-- `c<d>` and `c(y).0` as one molecule. -/
def pairMolecule : Molecule := ⟨∅, {outputCD, listener}⟩

theorem split_denotes :
    BagDenotes {publicOutput, publicListener} (parList [parList [outputCD.1], parList [listener.1]]) :=
  ⟨[publicOutput, publicListener], _, rfl,
    .cons ⟨[], [outputCD], List.nodup_nil, by simp [publicOutput], rfl, rfl⟩
      (.cons ⟨[], [listener], List.nodup_nil, by simp [publicListener], rfl, rfl⟩ .nil), rfl⟩

theorem merged_denotes : BagDenotes {pairMolecule} (parList [parList [outputCD.1, listener.1]]) :=
  ⟨[pairMolecule], _, rfl, .cons ⟨[], [outputCD, listener], List.nodup_nil, by simp [pairMolecule], rfl, rfl⟩ .nil,
    rfl⟩

/-- **Split or merged, the same process**: two molecules and one molecule are saturated bisimilar. -/
theorem split_merged_bisimilar :
    SaturatedBisimilarIn rules (fun _ => True) {publicOutput, publicListener} {pairMolecule} := by
  refine saturatedBisimilar_of_congruent split_denotes merged_denotes ?_
  simp only [parList]
  refine (Congruent.par (Congruent.refl _) (Congruent.nilRight _)).trans ?_
  refine (Congruent.par (Congruent.nilRight _) (Congruent.refl _)).trans (Congruent.nilRight _).symm

/-- `(νw) c<w>` -/
def renamedSender : Molecule := ⟨{"w"}, {⟨.output "c" "w", .output "c" "w"⟩}⟩

theorem sender_renamed :
    (Process.par (.output "c" "v") .nil).substitute "v" "w" = Process.par (.output "c" "w") .nil := by
  rw [Process.substitute_par, Process.substitute_nil, Process.substitute_output]
  decide

/-- **Renamed apart, the same process**: senders of a restricted name differing only in that name are saturated
bisimilar. -/
theorem renamed_sender_bisimilar : SaturatedBisimilarIn rules (fun _ => True) {boundSender} {renamedSender} := by
  refine saturatedBisimilar_of_congruent (firstProcess := parList [nuList ["v"] (parList [.output "c" "v"])])
    (secondProcess := parList [nuList ["w"] (parList [.output "c" "w"])])
    ⟨[boundSender], _, rfl, .cons ⟨["v"], [⟨.output "c" "v", .output "c" "v"⟩], by simp, by simp [boundSender], rfl,
      rfl⟩ .nil, rfl⟩
    ⟨[renamedSender], _, rfl, .cons ⟨["w"], [⟨.output "c" "w", .output "c" "w"⟩], by simp, by simp [renamedSender],
      rfl, rfl⟩ .nil, rfl⟩ ?_
  simp only [parList, nuList]
  refine Congruent.par (Congruent.trans ⟨.alpha_nu "v" "w" _ (by decide)⟩ ?_) (Congruent.refl _)
  rw [sender_renamed]
  exact Congruent.refl _

/-- **A fact about π through molecules**: `c<d>` beside the inert process is not saturated reduction bisimilar to it. -/
theorem output_not_reduction_bisimilar_nil :
    ¬ SaturatedReductionBisimilar (parList [parList [outputCD.1]]) Process.nil := fun bisimilar =>
  publicOutput_not_inert ((saturatedBisimilarIn_iff_reduction
    (first := {publicOutput}) (second := 0)
    ⟨[publicOutput], _, rfl, .cons ⟨[], [outputCD], List.nodup_nil, by simp [publicOutput], rfl, rfl⟩ .nil, rfl⟩
    ⟨[], [], rfl, .nil, rfl⟩).mpr bisimilar)

/-- `(νa) (a<d> | b(y).0)`: the output on the restricted `a`, the input on the public `b`. -/
def apartPair : Molecule := ⟨{"a"}, {⟨.output "a" "d", .output "a" "d"⟩, ⟨.input "b" "y" .nil, .input "b" "y" .nil⟩}⟩

/-- `a` replaced by `b`, a name the molecule already uses. -/
def collidedPair : Molecule := ⟨{"b"}, {⟨.output "b" "d", .output "b" "d"⟩, ⟨.input "b" "y" .nil, .input "b" "y" .nil⟩}⟩

/-- No internal communication: the output is on the restricted `a`, the input on `b`. -/
theorem apartPair_still (result : Molecule) : ¬ Internal apartPair result := by
  intro internal
  cases internal with
  | @comm receiver sender continuation kept lifted components contained fires lifts fresh =>
  obtain ⟨x, payload, -, sends, receives, -, -, -⟩ := fires_receive fires
  have receiverMem : receiver ∈ apartPair.body := Multiset.subset_of_le contained (by simp)
  have senderMem : sender ∈ apartPair.body := Multiset.subset_of_le contained (by simp)
  simp only [apartPair, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at receiverMem senderMem
  rcases receiverMem with rfl | rfl <;> rcases senderMem with rfl | rfl
  · simp [ReceivesOn] at receives
  · simp [ReceivesOn] at receives
  · simp only [ReceivesOn] at receives
    rcases receives with ⟨_, _, shape⟩ | ⟨_, _, shape⟩
    · simp only [Process.input.injEq] at shape
      simp only [Process.output.injEq] at sends
      exact absurd (shape.1.trans sends.1.symm) (by decide)
    · cases shape
  · simp at sends

/-- **Freshness is needed for renaming**: replacing `a` by the used name `b` creates a communication. -/
theorem collidedPair_internal : ∃ result, Internal collidedPair result := by
  have contained : ({⟨.input "b" "y" .nil, .input "b" "y" .nil⟩, ⟨.output "b" "d", .output "b" "d"⟩} :
      Multiset Prime) ≤ collidedPair.body := by
    simp only [collidedPair, Multiset.insert_eq_cons]
    exact (Multiset.cons_swap _ _ _).le
  have lifts : Lifts (Process.nil.substitute "y" "d") ∅ 0 := by rw [Process.substitute_nil]; exact .nil
  exact ⟨_, .comm contained (.input "b" "y" "d" .nil) lifts (Finset.disjoint_empty_left _)⟩

/-- Replacing `a` by `b` is no renaming step: `b` is in use. -/
theorem rename_onto_used_name (renamed : Molecule) (step : Molecule.RenameStep apartPair renamed) :
    renamed.scope ≠ {"b"} := by
  cases step with
  | @rename old new restricted unused fresh =>
  intro same
  have oldIs : old = "a" := by simpa [apartPair] using restricted
  subst oldIs
  have newIs : new = "b" := by simpa [apartPair] using same
  subst newIs
  exact fresh (by decide)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners.Controls
