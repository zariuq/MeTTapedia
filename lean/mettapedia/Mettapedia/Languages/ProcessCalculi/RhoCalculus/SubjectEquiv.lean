import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Types
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax

private theorem struct_apply_cong_single {f : String} {p q : Pattern}
    (hpq : StructuralCongruence p q) :
    StructuralCongruence (.apply f [p]) (.apply f [q]) := by
  refine StructuralCongruence.apply_cong f [p] [q] rfl ?_
  intro i h₁ h₂
  have hi : i = 0 := by
    have hlt : i < 1 := by simpa using h₁
    simpa using hlt
  subst hi
  simpa using hpq

/-- Name equivalence is realized by structural congruence on the underlying
pattern representation. -/
theorem nameEquiv_implies_struct {n m : Pattern} :
    NameEquiv n m → StructuralCongruence n m := by
  intro h
  induction h with
  | quote_drop n =>
      exact StructuralCongruence.quote_drop n
  | refl n =>
      exact StructuralCongruence.refl n
  | struct_equiv p q hpq =>
      exact struct_apply_cong_single hpq
  | symm x y hxy ih =>
      exact StructuralCongruence.symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact StructuralCongruence.trans _ _ _ ihxy ihyz

/-- Process residual equivalence: structural congruence plus matched
drop-of-quote collapse, closed under process contexts. -/
inductive ProcResidualEquiv : Pattern → Pattern → Prop where
  | struct {p q : Pattern} :
      StructuralCongruence p q →
      ProcResidualEquiv p q
  | refl (p : Pattern) :
      ProcResidualEquiv p p
  | symm {p q : Pattern} :
      ProcResidualEquiv p q →
      ProcResidualEquiv q p
  | trans {p q r : Pattern} :
      ProcResidualEquiv p q →
      ProcResidualEquiv q r →
      ProcResidualEquiv p r
  | unquote (p : Pattern) :
      ProcResidualEquiv (.apply "PDrop" [.apply "NQuote" [p]]) p
  | lambda_cong (nm : Option String) {p q : Pattern} :
      ProcResidualEquiv p q →
      ProcResidualEquiv (.lambda nm p) (.lambda nm q)
  | multiLambda_cong (n : Nat) (nms : List String) {p q : Pattern} :
      ProcResidualEquiv p q →
      ProcResidualEquiv (.multiLambda n nms p) (.multiLambda n nms q)
  | apply_cong (f : String) (args₁ args₂ : List Pattern) :
      (args₁.length = args₂.length) →
      (∀ i h₁ h₂, ProcResidualEquiv (args₁.get ⟨i, h₁⟩) (args₂.get ⟨i, h₂⟩)) →
      ProcResidualEquiv (.apply f args₁) (.apply f args₂)
  | collection_cong (ct : CollType) (elems₁ elems₂ : List Pattern) (g : Option String) :
      (elems₁.length = elems₂.length) →
      (∀ i h₁ h₂, ProcResidualEquiv (elems₁.get ⟨i, h₁⟩) (elems₂.get ⟨i, h₂⟩)) →
      ProcResidualEquiv (.collection ct elems₁ g) (.collection ct elems₂ g)
  | subst_cong {p₁ p₂ a₁ a₂ : Pattern} :
      ProcResidualEquiv p₁ p₂ →
      ProcResidualEquiv a₁ a₂ →
      ProcResidualEquiv (.subst p₁ a₁) (.subst p₂ a₂)

theorem ProcResidualEquiv.of_nameEquiv {n m : Pattern} :
    NameEquiv n m → ProcResidualEquiv n m :=
  fun h => ProcResidualEquiv.struct (nameEquiv_implies_struct h)

theorem procResidualEquiv_equivalence : Equivalence ProcResidualEquiv where
  refl := ProcResidualEquiv.refl
  symm := ProcResidualEquiv.symm
  trans := ProcResidualEquiv.trans

/-- Sort-indexed subject equivalence for the strict-core ρ-calculus. -/
def TypeSubjectEquiv (sort : String) : Pattern → Pattern → Prop :=
  if sort = "Proc" then ProcResidualEquiv
  else if sort = "Name" then NameEquiv
  else fun _ _ => False

theorem TypeSubjectEquiv.refl {sort : String} {p : Pattern}
    (hsort : sort = "Proc" ∨ sort = "Name") :
    TypeSubjectEquiv sort p p := by
  rcases hsort with rfl | rfl
  · simpa [TypeSubjectEquiv] using (ProcResidualEquiv.refl p)
  · simpa [TypeSubjectEquiv] using (NameEquiv.refl p)

theorem TypeSubjectEquiv.of_proc {p q : Pattern}
    (hpq : ProcResidualEquiv p q) :
    TypeSubjectEquiv "Proc" p q := by
  simpa [TypeSubjectEquiv] using hpq

theorem TypeSubjectEquiv.of_name {n m : Pattern}
    (hnm : NameEquiv n m) :
    TypeSubjectEquiv "Name" n m := by
  simpa [TypeSubjectEquiv] using hnm

/-- Process predicates that ignore residual-equivalent representatives. -/
def ProcPredRespectsResidualEquiv (φ : ProcPred) : Prop :=
  ∀ {p q : Pattern}, ProcResidualEquiv p q → φ p → φ q

/-- Name predicates that ignore name-equivalent representatives. -/
def NamePredRespectsNameEquiv (α : NamePred) : Prop :=
  ∀ {n m : Pattern}, NameEquiv n m → α n → α m

/-- Sort-indexed saturation for subject predicates. -/
def PredRespectsTypeSubjectEquiv (sort : String) (pred : Pattern → Prop) : Prop :=
  if sort = "Proc" then ProcPredRespectsResidualEquiv pred
  else if sort = "Name" then NamePredRespectsNameEquiv pred
  else False

/-- Saturation closure of a process predicate under residual equivalence. -/
def saturateProcPred (φ : ProcPred) : ProcPred :=
  fun p => ∃ q, ProcResidualEquiv p q ∧ φ q

/-- Saturation closure of a name predicate under name equivalence. -/
def saturateNamePred (α : NamePred) : NamePred :=
  fun n => ∃ m, NameEquiv n m ∧ α m

theorem saturateProcPred_respectsResidualEquiv (φ : ProcPred) :
    ProcPredRespectsResidualEquiv (saturateProcPred φ) := by
  intro p q hpq hp
  rcases hp with ⟨r, hpr, hr⟩
  exact ⟨r, ProcResidualEquiv.trans (ProcResidualEquiv.symm hpq) hpr, hr⟩

theorem saturateNamePred_respectsNameEquiv (α : NamePred) :
    NamePredRespectsNameEquiv (saturateNamePred α) := by
  intro n m hnm hn
  rcases hn with ⟨k, hmk, hk⟩
  exact ⟨k, NameEquiv.trans _ _ _ (NameEquiv.symm _ _ hnm) hmk, hk⟩

theorem mem_saturateProcPred_self {φ : ProcPred} {p : Pattern}
    (hp : φ p) : saturateProcPred φ p := by
  exact ⟨p, ProcResidualEquiv.refl p, hp⟩

theorem mem_saturateNamePred_self {α : NamePred} {n : Pattern}
    (hn : α n) : saturateNamePred α n := by
  exact ⟨n, NameEquiv.refl n, hn⟩

theorem saturateProcPred_iff_of_respects {φ : ProcPred}
    (hφ : ProcPredRespectsResidualEquiv φ) (p : Pattern) :
    saturateProcPred φ p ↔ φ p := by
  constructor
  · intro hp
    rcases hp with ⟨q, hpq, hq⟩
    exact hφ (ProcResidualEquiv.symm hpq) hq
  · intro hp
    exact mem_saturateProcPred_self hp

theorem saturateNamePred_iff_of_respects {α : NamePred}
    (hα : NamePredRespectsNameEquiv α) (n : Pattern) :
    saturateNamePred α n ↔ α n := by
  constructor
  · intro hn
    rcases hn with ⟨m, hnm, hm⟩
    exact hα (NameEquiv.symm _ _ hnm) hm
  · intro hn
    exact mem_saturateNamePred_self hn

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
