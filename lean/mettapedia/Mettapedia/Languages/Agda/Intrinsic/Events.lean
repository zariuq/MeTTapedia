import Mettapedia.Languages.Agda.Intrinsic.Comparison

/-!
# Constructing retained Agda firing trees

Each function here supplies a constructor of the generic indexed rule
polynomial. Ordered child positions and the local binder contexts survive.
The helpers for zero or one premise do not choose witnesses from propositions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Intrinsic.Authored

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution

def valuation {Γ : Ctx sig} (b c : Tm (.term :: Γ))
    (a0 a1 a2 a3 a4 a5 : Tm Γ) : Val Γ
  | ⟨0, _⟩ => b
  | ⟨1, _⟩ => c
  | ⟨2, _⟩ => a0
  | ⟨3, _⟩ => a1
  | ⟨4, _⟩ => a2
  | ⟨5, _⟩ => a3
  | ⟨6, _⟩ => a4
  | ⟨7, _⟩ => a5
  | ⟨_ + 8, h⟩ => by simp [metas] at h

def noPremise {Γ : Ctx sig} (i : Fin rules.length)
    (empty : (rules.get i).premises.length = 0) (v : Val Γ) :
    Tree rules algebra (conclusionJudgment rules algebra (occurrence i v)) :=
  .roll ⟨occurrence i v, rfl⟩ fun p =>
    False.elim (by have h := p.isLt; change p.val < (rules.get i).premises.length at h; omega)

def onePremise {Γ : Ctx sig} (i : Fin rules.length)
    (one : (rules.get i).premises.length = 1) (v : Val Γ)
    (child : Tree rules algebra
      (childJudgment rules algebra (occurrence i v) ⟨0, by change 0 < (rules.get i).premises.length; omega⟩)) :
    Tree rules algebra (conclusionJudgment rules algebra (occurrence i v)) :=
  .roll ⟨occurrence i v, rfl⟩ fun p => by
    have equal : p = ⟨0, by change 0 < (rules.get i).premises.length; omega⟩ := by
      apply Fin.ext
      change p.val = 0
      have h := p.isLt
      change p.val < (rules.get i).premises.length at h
      omega
    exact equal ▸ child

def beta_event {Γ : Ctx sig} (v : Val Γ)
    : Tree rules algebra (judgment (app (lam (v 0)) (v 2)) (inst (v 0) (v 2))) := by
  rw [← beta_conclusion v]
  exact noPremise ⟨0, by decide⟩ rfl v

def first_event {Γ : Ctx sig} (v : Val Γ)
    : Tree rules algebra (judgment (fst (pair (v 2) (v 3))) (v 2)) := by
  rw [← first_conclusion v]
  exact noPremise ⟨1, by decide⟩ rfl v

def second_event {Γ : Ctx sig} (v : Val Γ)
    : Tree rules algebra (judgment (snd (pair (v 2) (v 3))) (v 3)) := by
  rw [← second_conclusion v]
  exact noPremise ⟨2, by decide⟩ rfl v

def annotation_event {Γ : Ctx sig} (v : Val Γ)
    : Tree rules algebra (judgment (ann (v 2) (v 3)) (v 2)) := by
  rw [← annotation_conclusion v]
  exact noPremise ⟨3, by decide⟩ rfl v

def successor_event {Γ : Ctx sig} (v : Val Γ)
    : Tree rules algebra (judgment (app natSuc (v 2)) (suc (v 2))) := by
  rw [← successor_conclusion v]
  exact noPremise ⟨4, by decide⟩ rfl v

def recZero_event {Γ : Ctx sig} (v : Val Γ)
    : Tree rules algebra (judgment (natrec (v 2) (v 3) (v 4) (v 5) zero) (v 4)) := by
  rw [← recZero_conclusion v]
  exact noPremise ⟨5, by decide⟩ rfl v

def recSuc_event {Γ : Ctx sig} (v : Val Γ)
    : Tree rules algebra (judgment (natrec (v 2) (v 3) (v 4) (v 5) (suc (v 6))) (app (app (v 5) (v 6)) (natrec (v 2) (v 3) (v 4) (v 5) (v 6)))) := by
  rw [← recSuc_conclusion v]
  exact noPremise ⟨6, by decide⟩ rfl v

def piCong0_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 2) (v 3)))
    : Tree rules algebra (judgment (pi (v 2) (v 0)) (pi (v 3) (v 0))) := by
  rw [← piCong0_conclusion v]
  apply onePremise ⟨7, by decide⟩ rfl v
  rw [piCong0_child]
  exact child

def piCong1_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 0) (v 1)))
    : Tree rules algebra (judgment (pi (v 4) (v 0)) (pi (v 4) (v 1))) := by
  rw [← piCong1_conclusion v]
  apply onePremise ⟨8, by decide⟩ rfl v
  rw [piCong1_child]
  exact child

def lamCong0_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 0) (v 1)))
    : Tree rules algebra (judgment (lam (v 0)) (lam (v 1))) := by
  rw [← lamCong0_conclusion v]
  apply onePremise ⟨9, by decide⟩ rfl v
  rw [lamCong0_child]
  exact child

def appCong0_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 2) (v 3)))
    : Tree rules algebra (judgment (app (v 2) (v 4)) (app (v 3) (v 4))) := by
  rw [← appCong0_conclusion v]
  apply onePremise ⟨10, by decide⟩ rfl v
  rw [appCong0_child]
  exact child

def appCong1_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 2) (v 3)))
    : Tree rules algebra (judgment (app (v 4) (v 2)) (app (v 4) (v 3))) := by
  rw [← appCong1_conclusion v]
  apply onePremise ⟨11, by decide⟩ rfl v
  rw [appCong1_child]
  exact child

def annCong0_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 2) (v 3)))
    : Tree rules algebra (judgment (ann (v 2) (v 4)) (ann (v 3) (v 4))) := by
  rw [← annCong0_conclusion v]
  apply onePremise ⟨12, by decide⟩ rfl v
  rw [annCong0_child]
  exact child

def annCong1_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 2) (v 3)))
    : Tree rules algebra (judgment (ann (v 4) (v 2)) (ann (v 4) (v 3))) := by
  rw [← annCong1_conclusion v]
  apply onePremise ⟨13, by decide⟩ rfl v
  rw [annCong1_child]
  exact child

def sigmaCong0_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 2) (v 3)))
    : Tree rules algebra (judgment (sigma (v 2) (v 0)) (sigma (v 3) (v 0))) := by
  rw [← sigmaCong0_conclusion v]
  apply onePremise ⟨14, by decide⟩ rfl v
  rw [sigmaCong0_child]
  exact child

def sigmaCong1_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 0) (v 1)))
    : Tree rules algebra (judgment (sigma (v 4) (v 0)) (sigma (v 4) (v 1))) := by
  rw [← sigmaCong1_conclusion v]
  apply onePremise ⟨15, by decide⟩ rfl v
  rw [sigmaCong1_child]
  exact child

def pairCong0_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 2) (v 3)))
    : Tree rules algebra (judgment (pair (v 2) (v 4)) (pair (v 3) (v 4))) := by
  rw [← pairCong0_conclusion v]
  apply onePremise ⟨16, by decide⟩ rfl v
  rw [pairCong0_child]
  exact child

def pairCong1_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 2) (v 3)))
    : Tree rules algebra (judgment (pair (v 4) (v 2)) (pair (v 4) (v 3))) := by
  rw [← pairCong1_conclusion v]
  apply onePremise ⟨17, by decide⟩ rfl v
  rw [pairCong1_child]
  exact child

def fstCong0_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 2) (v 3)))
    : Tree rules algebra (judgment (fst (v 2)) (fst (v 3))) := by
  rw [← fstCong0_conclusion v]
  apply onePremise ⟨18, by decide⟩ rfl v
  rw [fstCong0_child]
  exact child

def sndCong0_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 2) (v 3)))
    : Tree rules algebra (judgment (snd (v 2)) (snd (v 3))) := by
  rw [← sndCong0_conclusion v]
  apply onePremise ⟨19, by decide⟩ rfl v
  rw [sndCong0_child]
  exact child

def sucCong0_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 2) (v 3)))
    : Tree rules algebra (judgment (suc (v 2)) (suc (v 3))) := by
  rw [← sucCong0_conclusion v]
  apply onePremise ⟨20, by decide⟩ rfl v
  rw [sucCong0_child]
  exact child

def natrecCong0_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 2) (v 3)))
    : Tree rules algebra (judgment (natrec (v 2) (v 4) (v 5) (v 6) (v 7)) (natrec (v 3) (v 4) (v 5) (v 6) (v 7))) := by
  rw [← natrecCong0_conclusion v]
  apply onePremise ⟨21, by decide⟩ rfl v
  rw [natrecCong0_child]
  exact child

def natrecCong1_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 2) (v 3)))
    : Tree rules algebra (judgment (natrec (v 4) (v 2) (v 5) (v 6) (v 7)) (natrec (v 4) (v 3) (v 5) (v 6) (v 7))) := by
  rw [← natrecCong1_conclusion v]
  apply onePremise ⟨22, by decide⟩ rfl v
  rw [natrecCong1_child]
  exact child

def natrecCong2_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 2) (v 3)))
    : Tree rules algebra (judgment (natrec (v 4) (v 5) (v 2) (v 6) (v 7)) (natrec (v 4) (v 5) (v 3) (v 6) (v 7))) := by
  rw [← natrecCong2_conclusion v]
  apply onePremise ⟨23, by decide⟩ rfl v
  rw [natrecCong2_child]
  exact child

def natrecCong3_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 2) (v 3)))
    : Tree rules algebra (judgment (natrec (v 4) (v 5) (v 6) (v 2) (v 7)) (natrec (v 4) (v 5) (v 6) (v 3) (v 7))) := by
  rw [← natrecCong3_conclusion v]
  apply onePremise ⟨24, by decide⟩ rfl v
  rw [natrecCong3_child]
  exact child

def natrecCong4_event {Γ : Ctx sig} (v : Val Γ)
    (child : Tree rules algebra (judgment (v 2) (v 3)))
    : Tree rules algebra (judgment (natrec (v 4) (v 5) (v 6) (v 7) (v 2)) (natrec (v 4) (v 5) (v 6) (v 7) (v 3))) := by
  rw [← natrecCong4_conclusion v]
  apply onePremise ⟨25, by decide⟩ rfl v
  rw [natrecCong4_child]
  exact child

end Mettapedia.Languages.Agda.Intrinsic.Authored
