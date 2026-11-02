import Mettapedia.Logic.TierZero.Kernel

/-!
# An accepted claim becomes a rule without adding theorems

When the MeTTa kernel accepts a claim, it adds the claim's statement to the presentation as a rule
whose formals are the claim's variables (Metamath's and MM0's theorems are used this way, and HOL's
theorems as premise-free rules). The claim was checked with its formals as fresh names. This file
proves that the added rule is **admissible**: it derives nothing new.

* `Derivable.cut`: a judgment derivable from hypotheses that are themselves derivable is derivable.
* A **renaming** of a presentation (`Renaming`) acts on judgments and arguments and commutes with
  rule instances. Fresh names are exactly what makes such a renaming exist: replacing names that
  no rule mentions commutes with every rule instance.
* `Derivable.rename`: derivability is stable under renamings.
* `DerivableWith`: derivability with one more rule, whose instances are the renamings of the
  checked statement `H ⊢ C`.
* `extend_conservative`: if `C` is derivable from `H`, everything derivable with the added rule is
  derivable without it.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero

universe u

variable {P : Presentation.{u}}

/-- Cut: hypotheses that are themselves derivable can be dropped. -/
theorem Derivable.cut {hyps hyps' : List P.J} {j : P.J} (h : Derivable P hyps j)
    (each : ∀ k ∈ hyps, Derivable P hyps' k) : Derivable P hyps' j := by
  induction h with
  | hyp mem => exact each _ mem
  | rule hi _ ih => exact Derivable.rule hi fun p mem notSide => ih p mem notSide

/-- A renaming acts on judgments and arguments and commutes with rule instances and side
conditions. -/
structure Renaming (P : Presentation.{u}) where
  onJ : P.J → P.J
  onA : P.A → P.A
  inst_rename : ∀ r a, P.inst r (onA a) = (P.inst r a).map fun x => (x.1.map onJ, onJ x.2)
  side_rename : ∀ p, P.side (onJ p) = P.side p

/-- Derivability is stable under renamings. -/
theorem Derivable.rename (σ : Renaming P) {hyps : List P.J} {j : P.J} (h : Derivable P hyps j) :
    Derivable P (hyps.map σ.onJ) (σ.onJ j) := by
  induction h with
  | hyp mem => exact Derivable.hyp (List.mem_map_of_mem mem)
  | @rule r a ps c hi _ ih =>
      have hi' : P.inst r (σ.onA a) = some (ps.map σ.onJ, σ.onJ c) := by
        rw [σ.inst_rename, hi]; rfl
      refine Derivable.rule hi' fun p mem notSide => ?_
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp mem
      exact ih q hq (by rw [← σ.side_rename]; exact notSide)

/-- Derivability in the presentation extended by the accepted statement `stmtHyps ⊢ stmtConcl` as a
rule, whose instances are the renamings of the statement. -/
inductive DerivableWith (P : Presentation.{u}) {renamings : Type u} (act : renamings → Renaming P)
    (stmtHyps : List P.J) (stmtConcl : P.J) (hyps : List P.J) : P.J → Prop
  | hyp {j : P.J} : j ∈ hyps → DerivableWith P act stmtHyps stmtConcl hyps j
  | rule {r : P.R} {a : P.A} {ps : List P.J} {c : P.J} :
      P.inst r a = some (ps, c) →
      (∀ p ∈ ps, P.side p = false → DerivableWith P act stmtHyps stmtConcl hyps p) →
      DerivableWith P act stmtHyps stmtConcl hyps c
  | derived (σ : renamings) :
      (∀ p ∈ stmtHyps.map (act σ).onJ, P.side p = false → DerivableWith P act stmtHyps stmtConcl hyps p) →
      DerivableWith P act stmtHyps stmtConcl hyps ((act σ).onJ stmtConcl)

/-- **Conservativity**: if the statement was derivable, the extended presentation derives nothing
new. The statement's hypotheses are judgments, not side conditions (a side condition among a
claim's hypotheses, such as Metamath's distinctness, is checked against the claim's frame, which
this model does not include). -/
theorem extend_conservative {renamings : Type u} {act : renamings → Renaming P}
    {stmtHyps : List P.J} {stmtConcl : P.J} (checked : Derivable P stmtHyps stmtConcl)
    (noSide : ∀ k ∈ stmtHyps, P.side k = false)
    {base : List P.J} {j : P.J} (h : DerivableWith P act stmtHyps stmtConcl base j) :
    Derivable P base j := by
  induction h with
  | hyp mem => exact Derivable.hyp mem
  | rule hi _ ih => exact Derivable.rule hi fun p mem notSide => ih p mem notSide
  | derived σ _ ih =>
      -- the renamed derivation of the statement, with its hypotheses cut by the premises
      refine (Derivable.rename (act σ) checked).cut fun k mem => ?_
      obtain ⟨h0, h0mem, rfl⟩ := List.mem_map.mp mem
      exact ih _ mem (by rw [(act σ).side_rename]; exact noSide h0 h0mem)

namespace Controls

open Mettapedia.Logic.TierZero.Controls

/-- The identity renaming of the two-rule presentation. -/
def idRenaming : Renaming pres where
  onJ := id
  onA := id
  inst_rename r a := by cases r <;> obtain ⟨x, y⟩ := a <;> simp [pres]
  side_rename _ := rfl

/-- From the hypothesis `p`, `q → p` is derivable (`k`, then `mp`). -/
theorem checked_example : Derivable pres [F.atom 0] (F.imp (F.atom 1) (F.atom 0) : pres.J) := by
  refine Derivable.rule (r := Rl.mp) (a := (F.atom 0, F.imp (F.atom 1) (F.atom 0))) rfl ?_
  intro p mem _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact Derivable.rule (r := Rl.k) (a := (F.atom 0, F.atom 1)) rfl (by simp)
  · exact Derivable.hyp (by simp)

/-- Adding `p ⊢ q → p` as a rule changes nothing: a derivation using it, from the base
hypothesis `p`, is a derivation in the original presentation. -/
theorem extension_example : Derivable pres [F.atom 0] (F.imp (F.atom 1) (F.atom 0) : pres.J) := by
  have extended : DerivableWith pres (renamings := PUnit) (fun _ => idRenaming) [F.atom 0]
      (F.imp (F.atom 1) (F.atom 0)) [F.atom 0] (F.imp (F.atom 1) (F.atom 0)) :=
    DerivableWith.derived PUnit.unit fun p mem _ => DerivableWith.hyp (by simpa [idRenaming] using mem)
  exact extend_conservative checked_example (by simp [pres]) extended

end Controls

end Mettapedia.Logic.TierZero
