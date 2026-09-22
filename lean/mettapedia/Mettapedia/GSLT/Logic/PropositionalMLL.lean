import Mathlib.Data.List.Perm.Basic
import Mettapedia.GSLT.Core.GSLT

/-!
# Propositional MLL as a GSLT

Multiplicative fragment only: atom, dual atom, tensor, par, one, bot.
No additives, no exponentials, no first-order structure.

The *logic* is a one-sided sequent calculus (`Derives`). Untyped proof
terms carry a cut-elimination GSLT (`mllCutGSLT`), same shape as
classical `PropositionalCut`. Duality is an involution on formulas.
Typed Hauptsatz (`hauptsatz`) is admissibility of cut on `Derives`, not a
rewrite of `CutStep`. `CutStep` is the principal untyped fragment only.

This is not `SoundCut` and not proofs-as-sessions.

No Foundation. No LanguageDef.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.PropositionalMLL

open Mettapedia.GSLT

inductive Formula where
  | atom : Nat → Formula
  | natom : Nat → Formula
  | tensor : Formula → Formula → Formula
  | par : Formula → Formula → Formula
  | one : Formula
  | bot : Formula
deriving DecidableEq

def dual : Formula → Formula
  | .atom n => .natom n
  | .natom n => .atom n
  | .tensor A B => .par (dual A) (dual B)
  | .par A B => .tensor (dual A) (dual B)
  | .one => .bot
  | .bot => .one

theorem dual_involutive (A : Formula) : dual (dual A) = A := by
  induction A with
  | atom n => rfl
  | natom n => rfl
  | tensor A B ihA ihB => simp [dual, ihA, ihB]
  | par A B ihA ihB => simp [dual, ihA, ihB]
  | one => rfl
  | bot => rfl

inductive DualEq : Formula → Formula → Prop where
  | refl (A : Formula) : DualEq A A
  | symm {A B} : DualEq A B → DualEq B A
  | trans {A B C} : DualEq A B → DualEq B C → DualEq A C
  | tensor {A A' B B'} : DualEq A A' → DualEq B B' →
      DualEq (.tensor A B) (.tensor A' B')
  | par {A A' B B'} : DualEq A A' → DualEq B B' →
      DualEq (.par A B) (.par A' B')
  | dual_dual (A : Formula) : DualEq (dual (dual A)) A

def mllEqGSLT : GSLT where
  Term := Formula
  equations := ⟨DualEq, ⟨DualEq.refl, DualEq.symm, DualEq.trans⟩⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := by
    intro _ _ _ _ step
    exact step.elim
  rewrites_resp_right := by
    intro _ _ _ step _
    exact step.elim

theorem mllEq_no_step (A B : Formula) : ¬ mllEqGSLT.Step A B :=
  fun h => h

theorem dual_dual_eq (A : Formula) : DualEq (dual (dual A)) A :=
  DualEq.dual_dual A

/-! ## One-sided sequent calculus (the logic) -/

inductive Derives : List Formula → Type where
  | ax (n : Nat) : Derives [.atom n, .natom n]
  | one : Derives [.one]
  | bot {Γ} : Derives Γ → Derives (.bot :: Γ)
  | tensor {A B Γ Δ} :
      Derives (A :: Γ) → Derives (B :: Δ) →
        Derives (.tensor A B :: (Γ ++ Δ))
  | par {A B Γ} :
      Derives (A :: B :: Γ) → Derives (.par A B :: Γ)
  | cut {A Γ Δ} :
      Derives (A :: Γ) → Derives (dual A :: Δ) → Derives (Γ ++ Δ)
  | ex {Γ Δ} : Derives Γ → List.Perm Γ Δ → Derives Δ

/-! ## Untyped proofs and cut-elimination -/

inductive Proof where
  | ax : Nat → Proof
  | oneIntro : Proof
  | botIntro : Proof → Proof
  | tensorIntro : Proof → Proof → Proof
  | parIntro : Proof → Proof
  | cut : Formula → Proof → Proof → Proof
deriving DecidableEq

def forget {Γ : List Formula} : Derives Γ → Proof
  | .ax n => .ax n
  | .one => .oneIntro
  | .bot d => .botIntro (forget d)
  | .tensor dp dq => .tensorIntro (forget dp) (forget dq)
  | .par d => .parIntro (forget d)
  | .cut (A := A) dp dn => .cut A (forget dp) (forget dn)
  | .ex d _ => forget d

inductive CutStep : Proof → Proof → Prop where
  | axLeft (n : Nat) (p : Proof) :
      CutStep (.cut (.atom n) (.ax n) p) p
  | axRight (n : Nat) (p : Proof) :
      CutStep (.cut (.natom n) p (.ax n)) p
  | oneBot (p : Proof) :
      CutStep (.cut .one .oneIntro (.botIntro p)) p
  | botOne (p : Proof) :
      CutStep (.cut .bot (.botIntro p) .oneIntro) p
  | tensorPar (A B : Formula) (p q r : Proof) :
      CutStep
        (.cut (.tensor A B) (.tensorIntro p q) (.parIntro r))
        (.cut A p (.cut B q r))
  | parTensor (A B : Formula) (r p q : Proof) :
      CutStep
        (.cut (.par A B) (.parIntro r) (.tensorIntro p q))
        (.cut B (.cut A r p) q)

def mllCutGSLT : GSLT where
  Term := Proof
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := CutStep
  rewrites_resp_left := by
    intro t t' u htt step
    exact ⟨u, htt ▸ step, rfl⟩
  rewrites_resp_right := by
    intro t u u' step huu
    exact huu ▸ step

inductive HasCut : Proof → Prop where
  | atRoot {A p q} : HasCut (.cut A p q)
  | botIntro {p} : HasCut p → HasCut (.botIntro p)
  | tensorIntro_left {p q} : HasCut p → HasCut (.tensorIntro p q)
  | tensorIntro_right {p q} : HasCut q → HasCut (.tensorIntro p q)
  | parIntro {p} : HasCut p → HasCut (.parIntro p)

def CutFree (p : Proof) : Prop := ¬ HasCut p

theorem ax_cutFree (n : Nat) : CutFree (.ax n) := by
  intro h
  cases h

theorem oneIntro_cutFree : CutFree .oneIntro := by
  intro h
  cases h

def Derives.CutFree {Γ : List Formula} : Derives Γ → Prop
  | .ax _ => True
  | .one => True
  | .bot d => Derives.CutFree d
  | .tensor dp dq => Derives.CutFree dp ∧ Derives.CutFree dq
  | .par d => Derives.CutFree d
  | .cut _ _ => False
  | .ex d _ => Derives.CutFree d

theorem forget_cutFree {Γ : List Formula} :
    (d : Derives Γ) → Derives.CutFree d → CutFree (forget d)
  | .ax n, _ => ax_cutFree n
  | .one, _ => oneIntro_cutFree
  | .bot d, hf => by
      intro contra
      cases contra with
      | botIntro hp => exact forget_cutFree d hf hp
  | .tensor dp dq, hf => by
      intro contra
      cases contra with
      | tensorIntro_left hp => exact forget_cutFree dp hf.1 hp
      | tensorIntro_right hq => exact forget_cutFree dq hf.2 hq
  | .par d, hf => by
      intro contra
      cases contra with
      | parIntro hp => exact forget_cutFree d hf hp
  | .cut _ _, hf => hf.elim
  | .ex d _, hf => forget_cutFree d hf

def proofSize : Proof → Nat
  | .ax _ => 1
  | .oneIntro => 1
  | .botIntro p => proofSize p + 1
  | .tensorIntro p q => proofSize p + proofSize q + 1
  | .parIntro p => proofSize p + 1
  | .cut _ p q => proofSize p + proofSize q + 1

theorem proofSize_pos (p : Proof) : 0 < proofSize p := by
  induction p with
  | ax => exact Nat.succ_pos 0
  | oneIntro => exact Nat.succ_pos 0
  | botIntro p ih => exact Nat.succ_pos _
  | tensorIntro p q ihp ihq => exact Nat.add_pos_right _ (Nat.succ_pos 0)
  | parIntro p ih => exact Nat.succ_pos _
  | cut _ p q ihp ihq => exact Nat.add_pos_right _ (Nat.succ_pos 0)

theorem cutStep_decreases {p q : Proof} (h : CutStep p q) :
    proofSize q < proofSize p := by
  cases h with
  | axLeft n r =>
      simp [proofSize]
      omega
  | axRight n r =>
      simp [proofSize]
      omega
  | oneBot r =>
      simp [proofSize]
      omega
  | botOne r =>
      simp [proofSize]
      omega
  | tensorPar A B r s t =>
      simp [proofSize]
      omega
  | parTensor A B r s t =>
      simp [proofSize]
      omega

theorem cutStep_source_hasCut {p q : Proof} (h : CutStep p q) : HasCut p := by
  cases h with
  | axLeft n r => exact HasCut.atRoot
  | axRight n r => exact HasCut.atRoot
  | oneBot r => exact HasCut.atRoot
  | botOne r => exact HasCut.atRoot
  | tensorPar A B r s t => exact HasCut.atRoot
  | parTensor A B r s t => exact HasCut.atRoot

/-! ## Measures for cut elimination

The cut-elimination measure is lexicographic: first the size of the cut
formula, then the total height of the two derivations. Duality preserves
formula size, so the measure is symmetric in the two premises.
-/

def formulaSize : Formula → Nat
  | .atom _ => 1
  | .natom _ => 1
  | .one => 1
  | .bot => 1
  | .tensor A B => formulaSize A + formulaSize B + 1
  | .par A B => formulaSize A + formulaSize B + 1

theorem formulaSize_pos (A : Formula) : 0 < formulaSize A := by
  cases A <;> simp [formulaSize]

theorem formulaSize_dual (A : Formula) : formulaSize (dual A) = formulaSize A := by
  induction A with
  | atom n => rfl
  | natom n => rfl
  | tensor A B ihA ihB => simp [dual, formulaSize, ihA, ihB]
  | par A B ihA ihB => simp [dual, formulaSize, ihA, ihB]
  | one => rfl
  | bot => rfl

def height {Γ : List Formula} : Derives Γ → Nat
  | .ax _ => 0
  | .one => 0
  | .bot d => height d + 1
  | .tensor dp dq => height dp + height dq + 1
  | .par d => height d + 1
  | .cut dp dn => height dp + height dn + 1
  | .ex d _ => height d + 1

@[simp] theorem cutFree_ex {Γ Δ : List Formula} (d : Derives Γ) (p : Γ.Perm Δ) :
    (Derives.ex d p).CutFree ↔ d.CutFree :=
  Iff.rfl

@[simp] theorem cutFree_bot {Γ : List Formula} (d : Derives Γ) :
    (Derives.bot d).CutFree ↔ d.CutFree :=
  Iff.rfl

@[simp] theorem cutFree_tensor {A B : Formula} {Γ Δ : List Formula}
    (dp : Derives (A :: Γ)) (dq : Derives (B :: Δ)) :
    (Derives.tensor dp dq).CutFree ↔ (dp.CutFree ∧ dq.CutFree) :=
  Iff.rfl

@[simp] theorem cutFree_par {A B : Formula} {Γ : List Formula}
    (d : Derives (A :: B :: Γ)) :
    (Derives.par d).CutFree ↔ d.CutFree :=
  Iff.rfl

@[simp] theorem cutFree_cut {A : Formula} {Γ Δ : List Formula}
    (dp : Derives (A :: Γ)) (dn : Derives (dual A :: Δ)) :
    (Derives.cut dp dn).CutFree ↔ False :=
  Iff.rfl

/-! ## Permutation plumbing

Sequents are lists with an explicit exchange rule, so cut elimination is
stated up to permutation: the cut formula need not be at the head of the
derived sequent. These two lemmas are the only decompositions used.
-/

/-- A permuted cons either matches the head or hides the formula in the tail. -/
theorem perm_cons_split {p A : Formula} {L Γ : List Formula}
    (h : (p :: L).Perm (A :: Γ)) :
    (p = A ∧ L.Perm Γ) ∨ (∃ L', L.Perm (A :: L') ∧ Γ.Perm (p :: L')) := by
  by_cases hpa : p = A
  · subst hpa
    exact Or.inl ⟨rfl, h.cons_inv⟩
  · have hmem : A ∈ p :: L := (h.mem_iff).2 (by simp)
    have hmemL : A ∈ L := by
      rcases List.mem_cons.1 hmem with heq | hmem'
      · exact absurd heq.symm hpa
      · exact hmem'
    have hL : L.Perm (A :: L.erase A) := List.perm_cons_erase hmemL
    have h1 : (p :: L).Perm (p :: A :: L.erase A) := hL.cons p
    have h2 : (p :: A :: L.erase A).Perm (A :: p :: L.erase A) :=
      List.Perm.swap A p (L.erase A)
    have h3 : (A :: Γ).Perm (A :: (p :: L.erase A)) :=
      h.symm.trans (h1.trans h2)
    exact Or.inr ⟨L.erase A, hL, h3.cons_inv⟩

/-- A formula permuted out of a concatenation comes from one side of it. -/
theorem perm_append_cons_split {A : Formula} {Γ₁ Γ₂ L : List Formula}
    (h : (Γ₁ ++ Γ₂).Perm (A :: L)) :
    (∃ Γ₁', Γ₁.Perm (A :: Γ₁') ∧ L.Perm (Γ₁' ++ Γ₂)) ∨
      (∃ Γ₂', Γ₂.Perm (A :: Γ₂') ∧ L.Perm (Γ₁ ++ Γ₂')) := by
  have hmem : A ∈ Γ₁ ++ Γ₂ := (h.mem_iff).2 (by simp)
  rcases List.mem_append.1 hmem with h1 | h2
  · refine Or.inl ⟨Γ₁.erase A, List.perm_cons_erase h1, ?_⟩
    have hp : (Γ₁ ++ Γ₂).Perm ((A :: Γ₁.erase A) ++ Γ₂) :=
      (List.perm_cons_erase h1).append_right Γ₂
    exact ((h.symm.trans hp).cons_inv)
  · refine Or.inr ⟨Γ₂.erase A, List.perm_cons_erase h2, ?_⟩
    have hp : (Γ₁ ++ Γ₂).Perm (Γ₁ ++ (A :: Γ₂.erase A)) :=
      (List.perm_cons_erase h2).append_left Γ₁
    have hmid : (Γ₁ ++ (A :: Γ₂.erase A)).Perm (A :: (Γ₁ ++ Γ₂.erase A)) :=
      List.perm_middle
    exact ((h.symm.trans (hp.trans hmid)).cons_inv)

theorem perm_swap (a b : Formula) : List.Perm [a, b] [b, a] :=
  List.Perm.swap b a []

theorem perm_cycle3 (x y z : Formula) :
    List.Perm [x, y, z] [y, z, x] :=
  (List.Perm.swap y x [z]).trans (List.Perm.cons y (List.Perm.swap z x []))

/-! ## Cut elimination for the units

A `bot` in a cut-free derivation is introduced by the `bot` rule, so it can be
deleted: that is the cut against `one`. Dually, a `one` can be replaced by any
derivation of `⊢ ⊥, Γ₀`: that is the cut against `bot`. Both are structural
inductions on the derivation, with no measure.
-/

theorem bot_inversion : ∀ {Δ' : List Formula} (d : Derives Δ'), d.CutFree →
    ∀ (Δ : List Formula), Δ'.Perm (Formula.bot :: Δ) →
      ∃ d' : Derives Δ, d'.CutFree := by
  intro Δ' d
  induction d with
  | ax n =>
      intro _ Δ h
      have hmem : Formula.bot ∈ [Formula.atom n, Formula.natom n] :=
        (h.mem_iff).2 (by simp)
      simp at hmem
  | one =>
      intro _ Δ h
      have hmem : Formula.bot ∈ [Formula.one] := (h.mem_iff).2 (by simp)
      simp at hmem
  | @bot Γ f ih =>
      intro hcf Δ h
      exact ⟨Derives.ex f h.cons_inv, hcf⟩
  | @tensor A B Γ₁ Γ₂ f₁ f₂ ih₁ ih₂ =>
      intro hcf Δ h
      obtain ⟨hcf₁, hcf₂⟩ := hcf
      rcases perm_cons_split h with ⟨heq, -⟩ | ⟨L', hL', hΔ⟩
      · exact Formula.noConfusion heq
      · rcases perm_append_cons_split hL' with ⟨Γ₁', hΓ₁, hL⟩ | ⟨Γ₂', hΓ₂, hL⟩
        · have hA : (A :: Γ₁).Perm (Formula.bot :: A :: Γ₁') :=
            (hΓ₁.cons A).trans (List.Perm.swap Formula.bot A Γ₁')
          obtain ⟨g₁, hg₁⟩ := ih₁ hcf₁ (A :: Γ₁') hA
          exact ⟨Derives.ex (Derives.tensor g₁ f₂)
            ((hL.symm.cons (Formula.tensor A B)).trans hΔ.symm), hg₁, hcf₂⟩
        · have hB : (B :: Γ₂).Perm (Formula.bot :: B :: Γ₂') :=
            (hΓ₂.cons B).trans (List.Perm.swap Formula.bot B Γ₂')
          obtain ⟨g₂, hg₂⟩ := ih₂ hcf₂ (B :: Γ₂') hB
          exact ⟨Derives.ex (Derives.tensor f₁ g₂)
            ((hL.symm.cons (Formula.tensor A B)).trans hΔ.symm), hcf₁, hg₂⟩
  | @par A B Γ₁ f ih =>
      intro hcf Δ h
      rcases perm_cons_split h with ⟨heq, -⟩ | ⟨L', hL', hΔ⟩
      · exact Formula.noConfusion heq
      · have hAB : (A :: B :: Γ₁).Perm (Formula.bot :: A :: B :: L') :=
          (((hL'.cons B).trans (List.Perm.swap Formula.bot B L')).cons A).trans
            (List.Perm.swap Formula.bot A (B :: L'))
        obtain ⟨g, hg⟩ := ih hcf (A :: B :: L') hAB
        exact ⟨Derives.ex (Derives.par g) hΔ.symm, hg⟩
  | @cut A Γ₁ Γ₂ f₁ f₂ ih₁ ih₂ =>
      intro hcf Δ h
      exact False.elim hcf
  | @ex Γ₁ Γ₂ f q ih =>
      intro hcf Δ h
      exact ih hcf Δ (q.trans h)

theorem one_cut : ∀ {Δ' : List Formula} (d : Derives Δ'), d.CutFree →
    ∀ (Δ Γ₀ : List Formula) (e : Derives Γ₀), e.CutFree →
      Δ'.Perm (Formula.one :: Δ) →
      ∃ d' : Derives (Γ₀ ++ Δ), d'.CutFree := by
  intro Δ' d
  induction d with
  | ax n =>
      intro _ Δ Γ₀ e _ h
      have hmem : Formula.one ∈ [Formula.atom n, Formula.natom n] :=
        (h.mem_iff).2 (by simp)
      simp at hmem
  | one =>
      intro _ Δ Γ₀ e hcfe h
      have hp : (Γ₀ ++ ([] : List Formula)).Perm (Γ₀ ++ Δ) :=
        List.Perm.append_left Γ₀ h.cons_inv
      rw [List.append_nil] at hp
      exact ⟨Derives.ex e hp, hcfe⟩
  | @bot Γ₁ f ih =>
      intro hcf Δ Γ₀ e hcfe h
      rcases perm_cons_split h with ⟨heq, -⟩ | ⟨L', hL', hΔ⟩
      · exact Formula.noConfusion heq
      · obtain ⟨g, hg⟩ := ih hcf L' Γ₀ e hcfe hL'
        exact ⟨Derives.ex (Derives.bot g)
          (List.perm_middle.symm.trans (List.Perm.append_left Γ₀ hΔ.symm)), hg⟩
  | @tensor A B Γ₁ Γ₂ f₁ f₂ ih₁ ih₂ =>
      intro hcf Δ Γ₀ e hcfe h
      obtain ⟨hcf₁, hcf₂⟩ := hcf
      rcases perm_cons_split h with ⟨heq, -⟩ | ⟨L', hL', hΔ⟩
      · exact Formula.noConfusion heq
      · rcases perm_append_cons_split hL' with ⟨Γ₁', hΓ₁, hL⟩ | ⟨Γ₂', hΓ₂, hL⟩
        · have hA : (A :: Γ₁).Perm (Formula.one :: A :: Γ₁') :=
            (hΓ₁.cons A).trans (List.Perm.swap Formula.one A Γ₁')
          obtain ⟨g₁, hg₁⟩ := ih₁ hcf₁ (A :: Γ₁') Γ₀ e hcfe hA
          have hperm :
              (Formula.tensor A B :: ((Γ₀ ++ Γ₁') ++ Γ₂)).Perm (Γ₀ ++ Δ) := by
            rw [List.append_assoc]
            exact ((List.Perm.append_left Γ₀ hL.symm).cons (Formula.tensor A B)).trans
              (List.perm_middle.symm.trans (List.Perm.append_left Γ₀ hΔ.symm))
          exact ⟨Derives.ex
            (Derives.tensor (Derives.ex g₁ List.perm_middle) f₂) hperm, hg₁, hcf₂⟩
        · have hB : (B :: Γ₂).Perm (Formula.one :: B :: Γ₂') :=
            (hΓ₂.cons B).trans (List.Perm.swap Formula.one B Γ₂')
          obtain ⟨g₂, hg₂⟩ := ih₂ hcf₂ (B :: Γ₂') Γ₀ e hcfe hB
          have hswap : (Γ₁ ++ (Γ₀ ++ Γ₂')).Perm (Γ₀ ++ (Γ₁ ++ Γ₂')) := by
            rw [← List.append_assoc, ← List.append_assoc]
            exact List.Perm.append_right Γ₂' List.perm_append_comm
          have hperm :
              (Formula.tensor A B :: (Γ₁ ++ (Γ₀ ++ Γ₂'))).Perm (Γ₀ ++ Δ) :=
            (hswap.cons (Formula.tensor A B)).trans
              (((List.Perm.append_left Γ₀ hL.symm).cons (Formula.tensor A B)).trans
                (List.perm_middle.symm.trans (List.Perm.append_left Γ₀ hΔ.symm)))
          exact ⟨Derives.ex
            (Derives.tensor f₁ (Derives.ex g₂ List.perm_middle)) hperm, hcf₁, hg₂⟩
  | @par A B Γ₁ f ih =>
      intro hcf Δ Γ₀ e hcfe h
      rcases perm_cons_split h with ⟨heq, -⟩ | ⟨L', hL', hΔ⟩
      · exact Formula.noConfusion heq
      · have hAB : (A :: B :: Γ₁).Perm (Formula.one :: A :: B :: L') :=
          (((hL'.cons B).trans (List.Perm.swap Formula.one B L')).cons A).trans
            (List.Perm.swap Formula.one A (B :: L'))
        obtain ⟨g, hg⟩ := ih hcf (A :: B :: L') Γ₀ e hcfe hAB
        exact ⟨Derives.ex
          (Derives.par
            (Derives.ex (Derives.ex g List.perm_middle) (List.perm_middle.cons A)))
          (List.perm_middle.symm.trans (List.Perm.append_left Γ₀ hΔ.symm)), hg⟩
  | @cut A Γ₁ Γ₂ f₁ f₂ ih₁ ih₂ =>
      intro hcf Δ Γ₀ e hcfe h
      exact False.elim hcf
  | @ex Γ₁ Γ₂ f q ih =>
      intro hcf Δ Γ₀ e hcfe h
      exact ih hcf Δ Γ₀ e hcfe (q.trans h)

/-- The ability to eliminate a cut on one fixed formula. -/
abbrev CutAbility (X : Formula) : Prop :=
  ∀ (Λ₁ Λ₂ Γ Δ : List Formula) (x : Derives Λ₁) (y : Derives Λ₂),
    x.CutFree → y.CutFree → Λ₁.Perm (X :: Γ) → Λ₂.Perm (dual X :: Δ) →
    ∃ d : Derives (Γ ++ Δ), d.CutFree

/-- Moving the middle block of a triple concatenation past the last one. -/
theorem perm_append_mid (X Y Z : List Formula) :
    ((X ++ Y) ++ Z).Perm ((X ++ Z) ++ Y) := by
  have h1 : ((X ++ Y) ++ Z) = X ++ (Y ++ Z) := List.append_assoc X Y Z
  have h2 : (X ++ (Y ++ Z)).Perm (X ++ (Z ++ Y)) :=
    (List.perm_append_comm).append_left X
  have h3 : (X ++ (Z ++ Y)) = (X ++ Z) ++ Y := (List.append_assoc X Z Y).symm
  exact h1 ▸ h3 ▸ h2

theorem tensorCut {B C : Formula} (cutB : CutAbility B) (cutC : CutAbility C)
    {Γ₁ Γ₂ : List Formula} (e₁ : Derives (B :: Γ₁)) (e₂ : Derives (C :: Γ₂))
    (cfe₁ : e₁.CutFree) (cfe₂ : e₂.CutFree) :
    ∀ {Δ' : List Formula} (d₂ : Derives Δ'), d₂.CutFree →
      ∀ (Δ : List Formula), Δ'.Perm (Formula.par (dual B) (dual C) :: Δ) →
        ∃ d : Derives ((Γ₁ ++ Γ₂) ++ Δ), d.CutFree := by
  intro Δ' d₂
  induction d₂ with
  | ax n =>
      intro _ Δ h
      have hmem : Formula.par (dual B) (dual C) ∈ [Formula.atom n, Formula.natom n] :=
        (h.mem_iff).2 (by simp)
      simp at hmem
  | one =>
      intro _ Δ h
      have hmem : Formula.par (dual B) (dual C) ∈ [Formula.one] :=
        (h.mem_iff).2 (by simp)
      simp at hmem
  | @bot G f ih =>
      intro hcf Δ h
      have hcf' : Derives.CutFree f := hcf
      rcases perm_cons_split h with ⟨heq, _⟩ | ⟨L', hG, hΔ⟩
      · exact Formula.noConfusion heq
      · obtain ⟨d, hd⟩ := ih hcf' L' hG
        have h1 : ((Γ₁ ++ Γ₂) ++ Δ).Perm ((Γ₁ ++ Γ₂) ++ (Formula.bot :: L')) :=
          hΔ.append_left (Γ₁ ++ Γ₂)
        have h2 : ((Γ₁ ++ Γ₂) ++ (Formula.bot :: L')).Perm
            (Formula.bot :: ((Γ₁ ++ Γ₂) ++ L')) := List.perm_middle
        exact ⟨Derives.ex (Derives.bot d) (h1.trans h2).symm, hd⟩
  | @tensor P Q Ga Gb f₁ f₂ ih₁ ih₂ =>
      intro hcf Δ h
      have hc : Derives.CutFree f₁ ∧ Derives.CutFree f₂ := hcf
      rcases perm_cons_split h with ⟨heq, _⟩ | ⟨L', hGab, hΔ⟩
      · exact Formula.noConfusion heq
      · have h1 : ((Γ₁ ++ Γ₂) ++ Δ).Perm
            ((Γ₁ ++ Γ₂) ++ (Formula.tensor P Q :: L')) := hΔ.append_left (Γ₁ ++ Γ₂)
        have h2 : ((Γ₁ ++ Γ₂) ++ (Formula.tensor P Q :: L')).Perm
            (Formula.tensor P Q :: ((Γ₁ ++ Γ₂) ++ L')) := List.perm_middle
        rcases perm_append_cons_split hGab with ⟨Ga', hGa, hL⟩ | ⟨Gb', hGb, hL⟩
        · have hc1 : (P :: Ga).Perm (P :: Formula.par (dual B) (dual C) :: Ga') :=
            hGa.cons P
          have hc2 : (P :: Formula.par (dual B) (dual C) :: Ga').Perm
              (Formula.par (dual B) (dual C) :: P :: Ga') :=
            List.Perm.swap (Formula.par (dual B) (dual C)) P Ga'
          obtain ⟨d, hd⟩ := ih₁ hc.1 (P :: Ga') (hc1.trans hc2)
          have hm : ((Γ₁ ++ Γ₂) ++ (P :: Ga')).Perm (P :: ((Γ₁ ++ Γ₂) ++ Ga')) :=
            List.perm_middle
          have h3 : (Formula.tensor P Q :: ((Γ₁ ++ Γ₂) ++ L')).Perm
              (Formula.tensor P Q :: (((Γ₁ ++ Γ₂) ++ Ga') ++ Gb)) := by
            refine List.Perm.cons _ ?_
            have hx : ((Γ₁ ++ Γ₂) ++ L').Perm ((Γ₁ ++ Γ₂) ++ (Ga' ++ Gb)) :=
              hL.append_left _
            simpa [List.append_assoc] using hx
          exact ⟨Derives.ex (Derives.tensor (Derives.ex d hm) f₂)
            ((h1.trans h2).trans h3).symm, ⟨hd, hc.2⟩⟩
        · have hc1 : (Q :: Gb).Perm (Q :: Formula.par (dual B) (dual C) :: Gb') :=
            hGb.cons Q
          have hc2 : (Q :: Formula.par (dual B) (dual C) :: Gb').Perm
              (Formula.par (dual B) (dual C) :: Q :: Gb') :=
            List.Perm.swap (Formula.par (dual B) (dual C)) Q Gb'
          obtain ⟨d, hd⟩ := ih₂ hc.2 (Q :: Gb') (hc1.trans hc2)
          have hm : ((Γ₁ ++ Γ₂) ++ (Q :: Gb')).Perm (Q :: ((Γ₁ ++ Γ₂) ++ Gb')) :=
            List.perm_middle
          have h3 : (Formula.tensor P Q :: ((Γ₁ ++ Γ₂) ++ L')).Perm
              (Formula.tensor P Q :: (Ga ++ ((Γ₁ ++ Γ₂) ++ Gb'))) := by
            refine List.Perm.cons _ ?_
            have hx : ((Γ₁ ++ Γ₂) ++ L').Perm ((Γ₁ ++ Γ₂) ++ (Ga ++ Gb')) :=
              hL.append_left _
            refine hx.trans ?_
            have hy : (((Γ₁ ++ Γ₂) ++ Ga) ++ Gb').Perm ((Ga ++ (Γ₁ ++ Γ₂)) ++ Gb') :=
              List.perm_append_comm.append_right Gb'
            simpa [List.append_assoc] using hy
          exact ⟨Derives.ex (Derives.tensor f₁ (Derives.ex d hm))
            ((h1.trans h2).trans h3).symm, ⟨hc.1, hd⟩⟩
  | @par P Q G f ih =>
      intro hcf Δ h
      have hcf' : Derives.CutFree f := hcf
      rcases perm_cons_split h with ⟨heq, hG⟩ | ⟨L', hG, hΔ⟩
      · injection heq with hP hQ
        subst hP
        subst hQ
        obtain ⟨d, hd⟩ :=
          cutB (B :: Γ₁) (dual B :: dual C :: G) Γ₁ (dual C :: G) e₁ f cfe₁ hcf'
            (List.Perm.refl _) (List.Perm.refl _)
        have hm : (Γ₁ ++ (dual C :: G)).Perm (dual C :: (Γ₁ ++ G)) := List.perm_middle
        obtain ⟨d'', hd''⟩ :=
          cutC (C :: Γ₂) (dual C :: (Γ₁ ++ G)) Γ₂ (Γ₁ ++ G) e₂ (Derives.ex d hm) cfe₂ hd
            (List.Perm.refl _) (List.Perm.refl _)
        have hp : (Γ₂ ++ (Γ₁ ++ G)).Perm ((Γ₁ ++ Γ₂) ++ Δ) := by
          have h1 : ((Γ₂ ++ Γ₁) ++ G).Perm ((Γ₁ ++ Γ₂) ++ G) :=
            List.perm_append_comm.append_right G
          have h2 : ((Γ₁ ++ Γ₂) ++ G).Perm ((Γ₁ ++ Γ₂) ++ Δ) := hG.append_left _
          simpa [List.append_assoc] using h1.trans h2
        exact ⟨Derives.ex d'' hp, hd''⟩
      · have hp1 : (P :: Q :: G).Perm
            (P :: Q :: Formula.par (dual B) (dual C) :: L') := (hG.cons Q).cons P
        have hp2 : (P :: Q :: Formula.par (dual B) (dual C) :: L').Perm
            (P :: Formula.par (dual B) (dual C) :: Q :: L') :=
          List.Perm.cons P (List.Perm.swap (Formula.par (dual B) (dual C)) Q L')
        have hp3 : (P :: Formula.par (dual B) (dual C) :: Q :: L').Perm
            (Formula.par (dual B) (dual C) :: P :: Q :: L') :=
          List.Perm.swap (Formula.par (dual B) (dual C)) P (Q :: L')
        obtain ⟨d, hd⟩ := ih hcf' (P :: Q :: L') ((hp1.trans hp2).trans hp3)
        have hm1 : ((Γ₁ ++ Γ₂) ++ (P :: Q :: L')).Perm
            (P :: ((Γ₁ ++ Γ₂) ++ (Q :: L'))) := List.perm_middle
        have hm2 : (P :: ((Γ₁ ++ Γ₂) ++ (Q :: L'))).Perm
            (P :: Q :: ((Γ₁ ++ Γ₂) ++ L')) :=
          List.Perm.cons P List.perm_middle
        have h1 : ((Γ₁ ++ Γ₂) ++ Δ).Perm ((Γ₁ ++ Γ₂) ++ (Formula.par P Q :: L')) :=
          hΔ.append_left (Γ₁ ++ Γ₂)
        have h2 : ((Γ₁ ++ Γ₂) ++ (Formula.par P Q :: L')).Perm
            (Formula.par P Q :: ((Γ₁ ++ Γ₂) ++ L')) := List.perm_middle
        exact ⟨Derives.ex (Derives.par (Derives.ex d (hm1.trans hm2)))
          (h1.trans h2).symm, hd⟩
  | @cut A' G' D' f₁ f₂ ih₁ ih₂ =>
      intro hcf
      exact False.elim hcf
  | @ex G D f q ih =>
      intro hcf Δ h
      have hcf' : Derives.CutFree f := hcf
      exact ih hcf' Δ (q.trans h)

theorem parCut {B C : Formula} (cutB : CutAbility B) (cutC : CutAbility C)
    {Γ₀ : List Formula} (e : Derives (B :: C :: Γ₀)) (cfe : e.CutFree) :
    ∀ {Δ' : List Formula} (d₂ : Derives Δ'), d₂.CutFree →
      ∀ (Δ : List Formula), Δ'.Perm (Formula.tensor (dual B) (dual C) :: Δ) →
        ∃ d : Derives (Γ₀ ++ Δ), d.CutFree := by
  intro Δ' d₂
  induction d₂ with
  | ax n =>
      intro _ Δ h
      have hmem : Formula.tensor (dual B) (dual C) ∈ [Formula.atom n, Formula.natom n] :=
        (h.mem_iff).2 (by simp)
      simp at hmem
  | one =>
      intro _ Δ h
      have hmem : Formula.tensor (dual B) (dual C) ∈ [Formula.one] :=
        (h.mem_iff).2 (by simp)
      simp at hmem
  | @bot L f ih =>
      intro hcf Δ h
      rcases perm_cons_split h with ⟨heq, _⟩ | ⟨L', hL, hΔ⟩
      · simp at heq
      · obtain ⟨g, hg⟩ := ih hcf L' hL
        exact ⟨Derives.ex (Derives.bot g)
          (((hΔ.append_left Γ₀).trans List.perm_middle).symm), hg⟩
  | @tensor P Q L₁ L₂ f₁ f₂ ih₁ ih₂ =>
      intro hcf Δ h
      rcases perm_cons_split h with ⟨heq, hperm⟩ | ⟨L', hL, hΔ⟩
      · injection heq with hP hQ
        subst hP
        subst hQ
        obtain ⟨g, hg⟩ := cutB (B :: C :: Γ₀) (dual B :: L₁) (C :: Γ₀) L₁ e f₁ cfe hcf.1
          (List.Perm.refl _) (List.Perm.refl _)
        obtain ⟨g2, hg2⟩ := cutC ((C :: Γ₀) ++ L₁) (dual C :: L₂) (Γ₀ ++ L₁) L₂ g f₂ hg hcf.2
          (List.Perm.refl _) (List.Perm.refl _)
        have hp : ((Γ₀ ++ L₁) ++ L₂).Perm (Γ₀ ++ Δ) := by
          have hassoc : ((Γ₀ ++ L₁) ++ L₂) = Γ₀ ++ (L₁ ++ L₂) := List.append_assoc _ _ _
          rw [hassoc]
          exact hperm.append_left Γ₀
        exact ⟨Derives.ex g2 hp, hg2⟩
      · rcases perm_append_cons_split hL with ⟨L₁', hL₁, hL'⟩ | ⟨L₂', hL₂, hL'⟩
        · have hrec : (P :: L₁).Perm (Formula.tensor (dual B) (dual C) :: P :: L₁') :=
            (List.Perm.cons P hL₁).trans
              (List.Perm.swap (Formula.tensor (dual B) (dual C)) P L₁')
          obtain ⟨g, hg⟩ := ih₁ hcf.1 (P :: L₁') hrec
          have hp : (Formula.tensor P Q :: ((Γ₀ ++ L₁') ++ L₂)).Perm (Γ₀ ++ Δ) := by
            have hassoc : ((Γ₀ ++ L₁') ++ L₂) = Γ₀ ++ (L₁' ++ L₂) := List.append_assoc _ _ _
            rw [hassoc]
            exact (((hΔ.trans (hL'.cons (Formula.tensor P Q))).append_left Γ₀).trans
              List.perm_middle).symm
          exact ⟨Derives.ex (Derives.tensor (Derives.ex g List.perm_middle) f₂) hp,
            ⟨hg, hcf.2⟩⟩
        · have hrec : (Q :: L₂).Perm (Formula.tensor (dual B) (dual C) :: Q :: L₂') :=
            (List.Perm.cons Q hL₂).trans
              (List.Perm.swap (Formula.tensor (dual B) (dual C)) Q L₂')
          obtain ⟨g, hg⟩ := ih₂ hcf.2 (Q :: L₂') hrec
          have hmid : (L₁ ++ (Γ₀ ++ L₂')).Perm (Γ₀ ++ (L₁ ++ L₂')) := by
            simp only [← List.append_assoc]
            exact List.perm_append_comm.append_right L₂'
          have hp : (Formula.tensor P Q :: (L₁ ++ (Γ₀ ++ L₂'))).Perm (Γ₀ ++ Δ) :=
            (List.Perm.cons (Formula.tensor P Q) hmid).trans
              (((hΔ.trans (hL'.cons (Formula.tensor P Q))).append_left Γ₀).trans
                List.perm_middle).symm
          exact ⟨Derives.ex (Derives.tensor f₁ (Derives.ex g List.perm_middle)) hp,
            ⟨hcf.1, hg⟩⟩
  | @par P Q L f ih =>
      intro hcf Δ h
      rcases perm_cons_split h with ⟨heq, _⟩ | ⟨L', hL, hΔ⟩
      · simp at heq
      · have hrec : (P :: Q :: L).Perm
            (Formula.tensor (dual B) (dual C) :: P :: Q :: L') :=
          (List.Perm.cons P ((List.Perm.cons Q hL).trans
              (List.Perm.swap (Formula.tensor (dual B) (dual C)) Q L'))).trans
            (List.Perm.swap (Formula.tensor (dual B) (dual C)) P (Q :: L'))
        obtain ⟨g, hg⟩ := ih hcf (P :: Q :: L') hrec
        exact ⟨Derives.ex
          (Derives.par
            (Derives.ex g (List.perm_middle.trans (List.Perm.cons P List.perm_middle))))
          (((hΔ.append_left Γ₀).trans List.perm_middle).symm), hg⟩
  | @cut A L₁ L₂ dp dn ih₁ ih₂ =>
      intro hcf
      exact False.elim hcf
  | @ex L₁ L₂ f q ih =>
      intro hcf Δ h
      exact ih hcf Δ (q.trans h)

/-! ## Cut admissibility

Lexicographic induction: the cut formula shrinks in the principal cases, and
the height of the left derivation shrinks when the cut formula sits in the
context of its last rule. The right-hand analysis is `tensorCut`, `parCut`,
`bot_inversion` and `one_cut`.
-/

theorem cutAdmissible :
    ∀ (n : Nat) (A : Formula), formulaSize A ≤ n →
      ∀ (hgt : Nat) (Λ₁ Λ₂ Γ Δ : List Formula)
        (d₁ : Derives Λ₁) (d₂ : Derives Λ₂),
        height d₁ ≤ hgt → d₁.CutFree → d₂.CutFree →
        Λ₁.Perm (A :: Γ) → Λ₂.Perm (dual A :: Δ) →
        ∃ d : Derives (Γ ++ Δ), d.CutFree := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
    intro A hA hgt
    induction hgt using Nat.strongRecOn with
    | _ hgt ihh =>
      intro Λ₁ Λ₂ Γ Δ d₁ d₂ hh cf₁ cf₂ p₁ p₂
      cases d₁ with
      | cut dp dn => exact False.elim cf₁
      | @ex Λ₀ _ e q =>
          have hlt : height e < hgt := by
            simp only [height] at hh
            omega
          exact ihh (height e) hlt Λ₀ Λ₂ Γ Δ e d₂ (Nat.le_refl _) cf₁ cf₂
            (q.trans p₁) p₂
      | ax m =>
          have hmem : A ∈ [Formula.atom m, Formula.natom m] :=
            (p₁.mem_iff).2 (by simp)
          have hΓ : Γ.Perm [dual A] := by
            rcases List.mem_cons.1 hmem with rfl | hmem'
            · exact (p₁.cons_inv).symm
            · have hA' : A = Formula.natom m := by simpa using hmem'
              subst hA'
              have hsw : ([Formula.atom m, Formula.natom m]).Perm
                  [Formula.natom m, Formula.atom m] := perm_swap _ _
              exact ((hsw.symm.trans p₁).cons_inv).symm
          have h1 : (Γ ++ Δ).Perm ([dual A] ++ Δ) := hΓ.append_right Δ
          have hperm : Λ₂.Perm (Γ ++ Δ) := p₂.trans (by simpa using h1.symm)
          exact ⟨Derives.ex d₂ hperm, cf₂⟩
      | one =>
          have hA1 : A = Formula.one := by
            have hmem : A ∈ [Formula.one] := (p₁.mem_iff).2 (by simp)
            simpa using hmem
          subst hA1
          have hΓ : ([] : List Formula).Perm Γ := p₁.cons_inv
          obtain ⟨d', hd'⟩ := bot_inversion d₂ cf₂ Δ p₂
          have hp : (Γ ++ Δ).Perm (([] : List Formula) ++ Δ) :=
            hΓ.symm.append_right Δ
          have hperm : Δ.Perm (Γ ++ Δ) := by simpa using hp.symm
          exact ⟨Derives.ex d' hperm, hd'⟩
      | @bot Γ₀ e =>
          rcases perm_cons_split p₁ with ⟨heq, hΓ⟩ | ⟨L', hL', hΓ⟩
          · subst heq
            obtain ⟨d', hd'⟩ := one_cut d₂ cf₂ Δ Γ₀ e cf₁ p₂
            exact ⟨Derives.ex d' (hΓ.append_right Δ), hd'⟩
          · have hlt : height e < hgt := by
              simp only [height] at hh
              omega
            obtain ⟨d', hd'⟩ :=
              ihh (height e) hlt Γ₀ Λ₂ L' Δ e d₂ (Nat.le_refl _) cf₁ cf₂ hL' p₂
            exact ⟨Derives.ex (Derives.bot d') (hΓ.append_right Δ).symm, hd'⟩
      | @tensor P Q Γ₁ Γ₂ e₁ e₂ =>
          rcases perm_cons_split p₁ with ⟨heq, hΓ⟩ | ⟨L', hL', hΓ⟩
          · subst heq
            have hszP : formulaSize P < n := by
              have := formulaSize_pos Q
              simp only [formulaSize] at hA
              omega
            have hszQ : formulaSize Q < n := by
              have := formulaSize_pos P
              simp only [formulaSize] at hA
              omega
            have hP : CutAbility P := by
              intro Λa Λb Γa Δa x y cfx cfy px py
              exact ihn (formulaSize P) hszP P (Nat.le_refl _) (height x)
                Λa Λb Γa Δa x y (Nat.le_refl _) cfx cfy px py
            have hQ : CutAbility Q := by
              intro Λa Λb Γa Δa x y cfx cfy px py
              exact ihn (formulaSize Q) hszQ Q (Nat.le_refl _) (height x)
                Λa Λb Γa Δa x y (Nat.le_refl _) cfx cfy px py
            obtain ⟨d', hd'⟩ := tensorCut hP hQ e₁ e₂ cf₁.1 cf₁.2 d₂ cf₂ Δ p₂
            exact ⟨Derives.ex d' (hΓ.append_right Δ), hd'⟩
          · rcases perm_append_cons_split hL' with ⟨Γ₁', hΓ₁, hL⟩ | ⟨Γ₂', hΓ₂, hL⟩
            · have hstep : (P :: Γ₁).Perm (A :: P :: Γ₁') :=
                (hΓ₁.cons P).trans (List.Perm.swap A P Γ₁')
              have hlt : height e₁ < hgt := by
                simp only [height] at hh
                omega
              obtain ⟨d', hd'⟩ :=
                ihh (height e₁) hlt (P :: Γ₁) Λ₂ (P :: Γ₁') Δ e₁ d₂
                  (Nat.le_refl _) cf₁.1 cf₂ hstep p₂
              have hmid : ((Γ₁' ++ Δ) ++ Γ₂).Perm ((Γ₁' ++ Γ₂) ++ Δ) :=
                perm_append_mid Γ₁' Δ Γ₂
              have hcons :
                  (Formula.tensor P Q :: ((Γ₁' ++ Δ) ++ Γ₂)).Perm
                    (Formula.tensor P Q :: ((Γ₁' ++ Γ₂) ++ Δ)) :=
                hmid.cons _
              have htail :
                  (Formula.tensor P Q :: (Γ₁' ++ Γ₂)).Perm
                    (Formula.tensor P Q :: L') :=
                (hL.symm).cons _
              have hperm :
                  (Formula.tensor P Q :: ((Γ₁' ++ Δ) ++ Γ₂)).Perm (Γ ++ Δ) :=
                hcons.trans
                  ((htail.append_right Δ).trans (hΓ.symm.append_right Δ))
              exact ⟨Derives.ex (Derives.tensor d' e₂) hperm, hd', cf₁.2⟩
            · have hstep : (Q :: Γ₂).Perm (A :: Q :: Γ₂') :=
                (hΓ₂.cons Q).trans (List.Perm.swap A Q Γ₂')
              have hlt : height e₂ < hgt := by
                simp only [height] at hh
                omega
              obtain ⟨d', hd'⟩ :=
                ihh (height e₂) hlt (Q :: Γ₂) Λ₂ (Q :: Γ₂') Δ e₂ d₂
                  (Nat.le_refl _) cf₁.2 cf₂ hstep p₂
              have htail :
                  (Formula.tensor P Q :: (Γ₁ ++ Γ₂')).Perm
                    (Formula.tensor P Q :: L') :=
                (hL.symm).cons _
              have hperm :
                  (Formula.tensor P Q :: (Γ₁ ++ (Γ₂' ++ Δ))).Perm (Γ ++ Δ) := by
                rw [(List.append_assoc Γ₁ Γ₂' Δ).symm]
                exact (htail.append_right Δ).trans (hΓ.symm.append_right Δ)
              exact ⟨Derives.ex (Derives.tensor e₁ d') hperm, cf₁.1, hd'⟩
      | @par P Q Γ₀ e =>
          rcases perm_cons_split p₁ with ⟨heq, hΓ⟩ | ⟨L', hL', hΓ⟩
          · subst heq
            have hszP : formulaSize P < n := by
              have := formulaSize_pos Q
              simp only [formulaSize] at hA
              omega
            have hszQ : formulaSize Q < n := by
              have := formulaSize_pos P
              simp only [formulaSize] at hA
              omega
            have hP : CutAbility P := by
              intro Λa Λb Γa Δa x y cfx cfy px py
              exact ihn (formulaSize P) hszP P (Nat.le_refl _) (height x)
                Λa Λb Γa Δa x y (Nat.le_refl _) cfx cfy px py
            have hQ : CutAbility Q := by
              intro Λa Λb Γa Δa x y cfx cfy px py
              exact ihn (formulaSize Q) hszQ Q (Nat.le_refl _) (height x)
                Λa Λb Γa Δa x y (Nat.le_refl _) cfx cfy px py
            obtain ⟨d', hd'⟩ := parCut hP hQ e cf₁ d₂ cf₂ Δ p₂
            exact ⟨Derives.ex d' (hΓ.append_right Δ), hd'⟩
          · have hlt : height e < hgt := by
              simp only [height] at hh
              omega
            have hstep : (P :: Q :: Γ₀).Perm (A :: P :: Q :: L') := by
              have h1 : (P :: Q :: Γ₀).Perm (P :: Q :: A :: L') :=
                (hL'.cons Q).cons P
              have h2 : (P :: Q :: A :: L').Perm (P :: A :: Q :: L') :=
                (List.Perm.swap A Q L').cons P
              have h3 : (P :: A :: Q :: L').Perm (A :: P :: Q :: L') :=
                List.Perm.swap A P (Q :: L')
              exact h1.trans (h2.trans h3)
            obtain ⟨d', hd'⟩ :=
              ihh (height e) hlt (P :: Q :: Γ₀) Λ₂ (P :: Q :: L') Δ e d₂
                (Nat.le_refl _) cf₁ cf₂ hstep p₂
            exact ⟨Derives.ex (Derives.par d') (hΓ.append_right Δ).symm, hd'⟩

/-- Cut is admissible on every formula. -/
theorem cutAbility (A : Formula) : CutAbility A := by
  intro Λ₁ Λ₂ Γ Δ x y cfx cfy px py
  exact cutAdmissible (formulaSize A) A (Nat.le_refl _) (height x)
    Λ₁ Λ₂ Γ Δ x y (Nat.le_refl _) cfx cfy px py

/-- **Hauptsatz.** Every derivation has a cut-free derivation of the same
sequent. -/
theorem hauptsatz : ∀ {Γ : List Formula}, Derives Γ →
    ∃ d' : Derives Γ, d'.CutFree := by
  intro Γ d
  induction d with
  | ax n => exact ⟨Derives.ax n, trivial⟩
  | one => exact ⟨Derives.one, trivial⟩
  | @bot Γ₀ e ih =>
      obtain ⟨e', he⟩ := ih
      exact ⟨Derives.bot e', he⟩
  | @tensor P Q Γ₁ Γ₂ e₁ e₂ ih₁ ih₂ =>
      obtain ⟨a, ha⟩ := ih₁
      obtain ⟨b, hb⟩ := ih₂
      exact ⟨Derives.tensor a b, ha, hb⟩
  | @par P Q Γ₀ e ih =>
      obtain ⟨e', he⟩ := ih
      exact ⟨Derives.par e', he⟩
  | @cut A Γ₁ Γ₂ e₁ e₂ ih₁ ih₂ =>
      obtain ⟨a, ha⟩ := ih₁
      obtain ⟨b, hb⟩ := ih₂
      exact cutAbility A (A :: Γ₁) (dual A :: Γ₂) Γ₁ Γ₂ a b ha hb
        (List.Perm.refl _) (List.Perm.refl _)
  | @ex Γ₁ Γ₂ e q ih =>
      obtain ⟨e', he⟩ := ih
      exact ⟨Derives.ex e' q, he⟩

/-! ## Worked identity cut -/

def axSwap : Derives [.natom 0, .atom 0] :=
  Derives.ex (Derives.ax 0)
    (List.Perm.swap (Formula.natom 0) (Formula.atom 0) [])

/-- Cut of an axiom against its swap. Result sequent is `[natom 0, atom 0]`. -/
def idCut : Derives [.natom 0, .atom 0] :=
  Derives.cut (A := .atom 0) (Derives.ax 0) axSwap

theorem idCut_forgets :
    forget idCut = .cut (.atom 0) (.ax 0) (.ax 0) := by
  simp [idCut, axSwap, forget]

theorem idCut_is_redex :
    CutStep (.cut (.atom 0) (.ax 0) (.ax 0)) (.ax 0) :=
  CutStep.axLeft 0 (.ax 0)

theorem idCut_not_cutFree : ¬ Derives.CutFree idCut :=
  fun h => h

/-! ## Identity expansion: `⊢ A, A⊥` for every formula -/

def identity : (A : Formula) → Derives [A, dual A]
  | .atom n => Derives.ax n
  | .natom n =>
      Derives.ex (Derives.ax n) (perm_swap (.atom n) (.natom n))
  | .one =>
      Derives.ex (Derives.bot Derives.one) (perm_swap .bot .one)
  | .bot => Derives.bot Derives.one
  | .tensor A B =>
      let t :=
        Derives.tensor (A := A) (B := B) (identity A) (identity B)
      let rotated := Derives.ex t (perm_cycle3 (.tensor A B) (dual A) (dual B))
      let p := Derives.par (A := dual A) (B := dual B) rotated
      Derives.ex p (perm_swap (.par (dual A) (dual B)) (.tensor A B))
  | .par A B =>
      let idA := Derives.ex (identity A) (perm_swap A (dual A))
      let idB := Derives.ex (identity B) (perm_swap B (dual B))
      let t :=
        Derives.tensor (A := dual A) (B := dual B) idA idB
      let rotated :=
        Derives.ex t (perm_cycle3 (.tensor (dual A) (dual B)) A B)
      Derives.par (A := A) (B := B) rotated

theorem identity_atom : forget (identity (.atom 0)) = .ax 0 :=
  rfl

/-- Identity expansion never introduces a cut. -/
theorem identity_is_cutFree (A : Formula) : (identity A).CutFree := by
  induction A with
  | atom n => trivial
  | natom n => trivial
  | one => trivial
  | bot => trivial
  | tensor A B ihA ihB =>
      simp [identity]
      exact ⟨ihA, ihB⟩
  | par A B ihA ihB =>
      simp [identity]
      exact ⟨ihA, ihB⟩

/-! ## Identity is admissible as a cut -/

/-- Cutting `identity A` (`⊢ A, A⊥`) against `⊢ A⊥, Δ` on `A` returns
`⊢ A⊥, Δ`. That is the right premise, so cut-elimination of this cut is
`hauptsatz` of that premise; the identity expansion is not used. -/
theorem identity_cut_admissible (A : Formula) {Δ : List Formula}
    (d : Derives (dual A :: Δ)) :
    ∃ d' : Derives (dual A :: Δ), d'.CutFree :=
  hauptsatz d

/-- The useful identity cut: `⊢ A, Γ` against `identity (A⊥)` returns
`⊢ Γ, A`, cut-free. Duality identifies `A⊥⊥` with `A`. -/
theorem identity_cut_admissible_swap (A : Formula) {Γ : List Formula}
    (d : Derives (A :: Γ)) :
    ∃ d' : Derives (Γ ++ [A]), d'.CutFree := by
  have h := hauptsatz (Derives.cut (A := A) d (identity (dual A)))
  rw [dual_involutive] at h
  exact h

/-! ## A principal cut that really reduces -/

/-- `⊢ A ⊗ B, A⊥, B⊥` by tensoring two identity expansions. -/
def canaryTensor (A B : Formula) :
    Derives (.tensor A B :: ([dual A] ++ [dual B])) :=
  Derives.tensor (identity A) (identity B)

/-- `⊢ (A ⊗ B)⊥, A ⊗ B`, with the par rule last, so the dual of the cut
formula is introduced principally. -/
def canaryPar (A B : Formula) :
    Derives (dual (.tensor A B) :: [.tensor A B]) :=
  Derives.par (A := dual A) (B := dual B)
    (Derives.ex (canaryTensor A B)
      (perm_cycle3 (.tensor A B) (dual A) (dual B)))

/-- A typed cut whose premises introduce the cut formula and its dual
principally: a genuine tensor/par redex, not an axiom cut. -/
def canaryCut (A B : Formula) :
    Derives (([dual A] ++ [dual B]) ++ [.tensor A B]) :=
  Derives.cut (A := .tensor A B) (canaryTensor A B) (canaryPar A B)

theorem canaryCut_not_cutFree (A B : Formula) : ¬ (canaryCut A B).CutFree :=
  fun h => h

theorem canaryCut_reduces (A B : Formula) :
    CutStep (forget (canaryCut A B))
      (.cut A (forget (identity A))
        (.cut B (forget (identity B))
          (.tensorIntro (forget (identity A)) (forget (identity B))))) := by
  have h := CutStep.tensorPar A B (forget (identity A)) (forget (identity B))
    (Proof.tensorIntro (forget (identity A)) (forget (identity B)))
  simpa [canaryCut, canaryTensor, canaryPar, forget] using h

theorem canaryCut_hauptsatz (A B : Formula) :
    ∃ d' : Derives (([dual A] ++ [dual B]) ++ [.tensor A B]), d'.CutFree :=
  hauptsatz (canaryCut A B)

/-- The dual principal step fires too: a par against a tensor. -/
theorem parTensor_example :
    CutStep
      (.cut (.par (.atom 0) (.atom 1)) (.parIntro (.ax 0))
        (.tensorIntro (.ax 0) (.ax 1)))
      (.cut (.atom 1) (.cut (.atom 0) (.ax 0) (.ax 0)) (.ax 1)) :=
  CutStep.parTensor (.atom 0) (.atom 1) (.ax 0) (.ax 0) (.ax 1)

/-- The unit steps are symmetric as well. -/
theorem botOne_example :
    CutStep (.cut .bot (.botIntro (.ax 0)) .oneIntro) (.ax 0) :=
  CutStep.botOne (.ax 0)

#print axioms dual_involutive
#print axioms mllEq_no_step
#print axioms forget_cutFree
#print axioms cutStep_decreases
#print axioms idCut_is_redex
#print axioms identity
#print axioms identity_is_cutFree
#print axioms bot_inversion
#print axioms one_cut
#print axioms tensorCut
#print axioms parCut
#print axioms cutAdmissible
#print axioms hauptsatz
#print axioms identity_cut_admissible
#print axioms identity_cut_admissible_swap
#print axioms canaryCut_reduces

end Mettapedia.GSLT.Logic.PropositionalMLL
