import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectCongruence
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchRecursor
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSetSteps

/-!
# Proofs by induction in the object package: addition is commutative

The addition of the object package recurses on its second summand: `add t zero` computes to
`t`, and `add a (suc b)` to `suc (add a b)` (`cadd_zero`, `cadd_suc`, the two root steps as
equalities of the judgment). So `add n zero` is `n` by computation, and reflexivity proves it
(`add_zero_identity`). With zero on the left nothing computes at a variable, and the statement
needs induction.

**`zero_add_identity`: a term of type `Π (n : num). Id num (add zero n) n`.** It is the
recursor of the numbers (`numRec_typed`, the typing rule of `num-rec` at any typed motive,
methods and number) at the family of identity types (`zeroAddFamily`): reflexivity at zero,
converted along `add zero zero ≡ zero`, and at a successor the congruence of the induction
hypothesis under the successor (`cong_suc`, derived from the identity eliminator), converted
along `add zero (suc k) ≡ suc (add zero k)`.

Two more inductions follow, each over a variable first number:

* `suc_add_identity : Π (a b : num). Id num (add (suc a) b) (suc (add a b))`, by induction on
  `b`: both sides compute to the successor of `a` at zero, and the step is the congruence of
  the hypothesis under the successor;
* **`add_comm_identity : Π (a b : num). Id num (add a b) (add b a)`: addition is
  commutative.** By induction on `b`. The base is the first induction turned round by
  symmetry. The step joins the congruence of the hypothesis under the successor with the
  second induction turned round, by transitivity.

Symmetry, transitivity and congruence of identity proofs are the terms of
`ObjectCongruence.lean`, derived from the identity eliminator. Nothing is added to the
judgment.

The object package is the package with the full metatheory of the candidate (strong
normalization, coherence of annotations, consistency), so these proofs are covered by all of
it.

Positive examples: the statements at numerals (`zero_add_identity_one`,
`add_comm_identity_one_two`), and the mirror statement of the first by reflexivity alone
(`add_zero_identity`). Negative example: no closed term is an identity proof that zero is one
(`zero_not_identical_to_one`), relative to `CofinalInaccessibles`: in the set tower the
successor of a number is not the number.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Annotated
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetTraceProofDecoding (mem_truthCode)

universe u

namespace CodeModel

section ZeroAdd

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-! ## The rules used -/

/-- A number plus zero is the number, in the judgment. -/
theorem cadd_zero {t : CTm Tower.Head n} (ht : CTyped objectChurch Γ t cnum) :
    CEqual objectChurch Γ (cadd t czero) t cnum :=
  .rootAdmitted (caddZero_step t) (caddZero_admits ht) (cadd_typed ht czero_typed) ht

/-- A number plus a successor is the successor of the sum, in the judgment. -/
theorem cadd_suc {a b : CTm Tower.Head n} (ha : CTyped objectChurch Γ a cnum)
    (hb : CTyped objectChurch Γ b cnum) :
    CEqual objectChurch Γ (cadd a (csuc b)) (csuc (cadd a b)) cnum :=
  .rootAdmitted (caddSuc_step a b) (caddSuc_admits ha hb) (cadd_typed ha (csuc_typed hb))
    (csuc_typed (cadd_typed ha hb))

/-- **The typing rule of the recursor of the numbers**: at a typed motive, value at zero, step
and number, `num-rec P z s q` has the type `P q`. -/
theorem numRec_typed {P z s q : CTm Tower.Head n}
    (hP : CTyped objectChurch Γ P (.pi cnum cU0)) (hz : CTyped objectChurch Γ z (.app P czero))
    (hs : CTyped objectChurch Γ s
      (.pi cnum (.pi (.app (P.rename wk) (.var 0))
        (.app ((P.rename wk).rename wk) (csuc (.var 1))))))
    (hq : CTyped objectChurch Γ q cnum) : CTyped objectChurch Γ (cRecApp P z s q) (.app P q) :=
  cRecSpine_typed.substitute (σ := fun i => [q, s, z, P].getD i.val P)
    (fun j => match j with
      | ⟨0, _⟩ => hq
      | ⟨1, _⟩ => hs
      | ⟨2, _⟩ => hz
      | ⟨3, _⟩ => hP)

/-! ## The mirror statement, by computation -/

/-- Positive: **a number plus zero is identical to the number, by reflexivity**: addition
computes on its second summand. -/
theorem add_zero_identity :
    CTyped objectChurch Γ (.lam cnum (.refl (.var 0)))
      (.pi cnum (.id cnum (cadd (.var 0) czero) (.var 0))) := by
  have body : CTyped objectChurch (.snoc Γ cnum) (.id cnum (cadd (.var 0) czero) (.var 0)) cU0 :=
    cidT cnum_typed (cadd_typed (.var 0) czero_typed) (.var 0)
  have computed : CEqual objectChurch (.snoc Γ cnum) (.id cnum (.var 0) (.var 0))
      (.id cnum (cadd (.var 0) czero) (.var 0)) cU0 :=
    .idCong (.refl cnum_typed) (.sort _) (.symm (cadd_zero (.var 0))) (.refl (.var 0))
  exact .lamIntro cnum_typed (.sort _) (cpiT cnum_typed body) (.sort _)
    (.conv (.reflIntro (.var 0)) computed (.sort _))

/-! ## The proof by induction -/

/-- The statement as a family over the numbers: zero plus the number is identical to the
number. -/
abbrev zeroAddFamily : CTm Tower.Head n := .lam cnum (.id cnum (cadd czero (.var 0)) (.var 0))

theorem zeroAddBody_typed :
    CTyped objectChurch (.snoc Γ cnum) (.id cnum (cadd czero (.var 0)) (.var 0)) cU0 :=
  cidT cnum_typed (cadd_typed czero_typed (.var 0)) (.var 0)

/-- The family is a motive of the recursor. -/
theorem zeroAddFamily_typed : CTyped objectChurch Γ zeroAddFamily (.pi cnum cU0) :=
  .lamIntro cnum_typed (.sort _) (cpiT (craise cnum_typed) cU0_typed) (.sort _)
    zeroAddBody_typed

/-- The family at a number is the identity type of zero plus the number and the number. -/
theorem zeroAddFamily_at {t : CTm Tower.Head n} (ht : CTyped objectChurch Γ t cnum) :
    CEqual objectChurch Γ (.app zeroAddFamily t) (.id cnum (cadd czero t) t) cU0 :=
  .betaPi (A := cnum) (B := cU0) (body := .id cnum (cadd czero (.var 0)) (.var 0)) (a := t)
    (cpiT (craise cnum_typed) cU0_typed) (.sort _) zeroAddBody_typed ht

/-- **The base**: reflexivity at zero, since zero plus zero computes to zero. -/
theorem zeroAddBase_typed : CTyped objectChurch Γ (.refl czero) (.app zeroAddFamily czero) := by
  have computed : CEqual objectChurch Γ (.id cnum (cadd czero czero) czero)
      (.id cnum czero czero) cU0 :=
    .idCong (.refl cnum_typed) (.sort _) (cadd_zero czero_typed) (.refl czero_typed)
  exact .conv (.reflIntro czero_typed)
    (.symm (.trans (zeroAddFamily_at czero_typed) computed)) (.sort _)

/-- The step over a number and the induction hypothesis: the congruence of the hypothesis
under the successor. -/
abbrev zeroAddStepBody : CTm Tower.Head (n + 2) :=
  congOf cnum cnum (.const sucN) (cadd czero (.var 1)) (.var 1) (.var 0)

/-- **The step**: from an identity proof for a number, an identity proof for its successor. -/
theorem zeroAddStepBody_typed :
    CTyped objectChurch (.snoc (.snoc Γ cnum) (.app zeroAddFamily (.var 0))) zeroAddStepBody
      (.app zeroAddFamily (csuc (.var 1))) := by
  have number : CTyped objectChurch (.snoc (.snoc Γ cnum) (.app zeroAddFamily (.var 0)))
      (.var 1) cnum := .var 1
  have hypothesis : CTyped objectChurch (.snoc (.snoc Γ cnum) (.app zeroAddFamily (.var 0)))
      (.var 0) (.id cnum (cadd czero (.var 1)) (.var 1)) :=
    .conv (.var 0) (zeroAddFamily_at number) (.sort _)
  have congruent := cong_suc (cadd_typed czero_typed number) number hypothesis
  have computed : CEqual objectChurch (.snoc (.snoc Γ cnum) (.app zeroAddFamily (.var 0)))
      (.id cnum (cadd czero (csuc (.var 1))) (csuc (.var 1)))
      (.id cnum (csuc (cadd czero (.var 1))) (csuc (.var 1))) cU0 :=
    .idCong (.refl cnum_typed) (.sort _) (cadd_suc czero_typed number)
      (.refl (csuc_typed number))
  exact .conv congruent
    (.symm (.trans (zeroAddFamily_at (csuc_typed number)) computed)) (.sort _)

/-- The step as a term. -/
abbrev zeroAddStep : CTm Tower.Head n :=
  .lam cnum (.lam (.app zeroAddFamily (.var 0)) zeroAddStepBody)

theorem zeroAddStep_typed :
    CTyped objectChurch Γ zeroAddStep
      (.pi cnum (.pi (.app zeroAddFamily (.var 0)) (.app zeroAddFamily (csuc (.var 1))))) := by
  have hypType : CTyped objectChurch (.snoc Γ cnum) (.app zeroAddFamily (.var 0)) cU0 :=
    .appElim (B := cU0) zeroAddFamily_typed (.var 0)
  have goalType : CTyped objectChurch (.snoc (.snoc Γ cnum) (.app zeroAddFamily (.var 0)))
      (.app zeroAddFamily (csuc (.var 1))) cU0 :=
    .appElim (B := cU0) zeroAddFamily_typed (csuc_typed (.var 1))
  have inner : CTyped objectChurch (.snoc Γ cnum)
      (.pi (.app zeroAddFamily (.var 0)) (.app zeroAddFamily (csuc (.var 1)))) cU0 :=
    cpiT hypType goalType
  exact .lamIntro cnum_typed (.sort _) (cpiT cnum_typed inner) (.sort _)
    (.lamIntro hypType (.sort _) inner (.sort _) zeroAddStepBody_typed)

/-- The proof by induction, as a term. -/
abbrev zeroAddProof : CTm Tower.Head n :=
  .lam cnum (cRecApp zeroAddFamily (.refl czero) zeroAddStep (.var 0))

/-- **A proof by induction in the object package: zero plus a number is identical to the
number.** -/
theorem zero_add_identity :
    CTyped objectChurch Γ zeroAddProof (.pi cnum (.id cnum (cadd czero (.var 0)) (.var 0))) :=
  .lamIntro cnum_typed (.sort _) (cpiT cnum_typed zeroAddBody_typed) (.sort _)
    (.conv (numRec_typed zeroAddFamily_typed zeroAddBase_typed zeroAddStep_typed (.var 0))
      (zeroAddFamily_at (.var 0)) (.sort _))

/-- Positive: the proof at the numeral one. -/
theorem zero_add_identity_one :
    CTyped objectChurch .nil (.app zeroAddProof (csuc czero))
      (.id cnum (cadd czero (csuc czero)) (csuc czero)) :=
  .appElim zero_add_identity (csuc_typed czero_typed)

end ZeroAdd

section Commutativity

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The successor is a congruence of the judgment's equality. -/
theorem csuc_cong {a b : CTm Tower.Head n} (equal : CEqual objectChurch Γ a b cnum) :
    CEqual objectChurch Γ (csuc a) (csuc b) cnum :=
  .appCong (B := cnum) (.refl csucConst_typed) equal

/-! ## The successor of a number plus a number -/

/-- The statement for a variable `a`, as a family over the numbers `b`: the successor of `a`
plus `b` is identical to the successor of `a` plus `b`. -/
abbrev sucAddFamily (i : Fin n) : CTm Tower.Head n :=
  .lam cnum (.id cnum (cadd (csuc (.var i.succ)) (.var 0)) (csuc (cadd (.var i.succ) (.var 0))))

theorem sucAddBody_typed {i : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum) :
    CTyped objectChurch (.snoc Γ cnum)
      (.id cnum (cadd (csuc (.var i.succ)) (.var 0)) (csuc (cadd (.var i.succ) (.var 0)))) cU0 :=
  cidT cnum_typed (cadd_typed (csuc_typed (CTyped.weaken ha)) (.var 0))
    (csuc_typed (cadd_typed (CTyped.weaken ha) (.var 0)))

theorem sucAddFamily_typed {i : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum) :
    CTyped objectChurch Γ (sucAddFamily i) (.pi cnum cU0) :=
  .lamIntro cnum_typed (.sort _) (cpiT (craise cnum_typed) cU0_typed) (.sort _)
    (sucAddBody_typed ha)

theorem sucAddFamily_at {i : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum)
    {t : CTm Tower.Head n} (ht : CTyped objectChurch Γ t cnum) :
    CEqual objectChurch Γ (.app (sucAddFamily i) t)
      (.id cnum (cadd (csuc (.var i)) t) (csuc (cadd (.var i) t))) cU0 :=
  .betaPi (A := cnum) (B := cU0)
    (body := .id cnum (cadd (csuc (.var i.succ)) (.var 0)) (csuc (cadd (.var i.succ) (.var 0))))
    (a := t) (cpiT (craise cnum_typed) cU0_typed) (.sort _) (sucAddBody_typed ha) ht

/-- The base: both sides compute to the successor of `a`. -/
theorem sucAddBase_typed {i : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum) :
    CTyped objectChurch Γ (.refl (csuc (.var i))) (.app (sucAddFamily i) czero) := by
  have computed : CEqual objectChurch Γ
      (.id cnum (cadd (csuc (.var i)) czero) (csuc (cadd (.var i) czero)))
      (.id cnum (csuc (.var i)) (csuc (.var i))) cU0 :=
    .idCong (.refl cnum_typed) (.sort _) (cadd_zero (csuc_typed ha)) (csuc_cong (cadd_zero ha))
  exact .conv (.reflIntro (csuc_typed ha))
    (.symm (.trans (sucAddFamily_at ha czero_typed) computed)) (.sort _)

/-- The step over a number and the induction hypothesis. -/
abbrev sucAddStepBody (i : Fin n) : CTm Tower.Head (n + 2) :=
  congOf cnum cnum (.const sucN) (cadd (csuc (.var i.succ.succ)) (.var 1))
    (csuc (cadd (.var i.succ.succ) (.var 1))) (.var 0)

theorem sucAddStepBody_typed {i : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum) :
    CTyped objectChurch (.snoc (.snoc Γ cnum) (.app (sucAddFamily i.succ) (.var 0)))
      (sucAddStepBody i) (.app (sucAddFamily i.succ.succ) (csuc (.var 1))) := by
  have first : CTyped objectChurch (.snoc (.snoc Γ cnum) (.app (sucAddFamily i.succ) (.var 0)))
      (.var i.succ.succ) cnum := CTyped.weaken (CTyped.weaken ha)
  have number : CTyped objectChurch (.snoc (.snoc Γ cnum) (.app (sucAddFamily i.succ) (.var 0)))
      (.var 1) cnum := .var 1
  have hypothesis : CTyped objectChurch
      (.snoc (.snoc Γ cnum) (.app (sucAddFamily i.succ) (.var 0))) (.var 0)
      (.id cnum (cadd (csuc (.var i.succ.succ)) (.var 1))
        (csuc (cadd (.var i.succ.succ) (.var 1)))) :=
    .conv (.var 0) (sucAddFamily_at first number) (.sort _)
  have congruent := cong_suc (cadd_typed (csuc_typed first) number)
    (csuc_typed (cadd_typed first number)) hypothesis
  have computed : CEqual objectChurch
      (.snoc (.snoc Γ cnum) (.app (sucAddFamily i.succ) (.var 0)))
      (.id cnum (cadd (csuc (.var i.succ.succ)) (csuc (.var 1)))
        (csuc (cadd (.var i.succ.succ) (csuc (.var 1)))))
      (.id cnum (csuc (cadd (csuc (.var i.succ.succ)) (.var 1)))
        (csuc (csuc (cadd (.var i.succ.succ) (.var 1))))) cU0 :=
    .idCong (.refl cnum_typed) (.sort _) (cadd_suc (csuc_typed first) number)
      (csuc_cong (cadd_suc first number))
  exact .conv congruent
    (.symm (.trans (sucAddFamily_at first (csuc_typed number)) computed)) (.sort _)

abbrev sucAddStep (i : Fin n) : CTm Tower.Head n :=
  .lam cnum (.lam (.app (sucAddFamily i.succ) (.var 0)) (sucAddStepBody i))

theorem sucAddStep_typed {i : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum) :
    CTyped objectChurch Γ (sucAddStep i)
      (.pi cnum (.pi (.app (sucAddFamily i.succ) (.var 0))
        (.app (sucAddFamily i.succ.succ) (csuc (.var 1))))) := by
  have first : CTyped objectChurch (.snoc Γ cnum) (.var i.succ) cnum := CTyped.weaken ha
  have hypType : CTyped objectChurch (.snoc Γ cnum) (.app (sucAddFamily i.succ) (.var 0)) cU0 :=
    .appElim (B := cU0) (sucAddFamily_typed first) (.var 0)
  have goalType : CTyped objectChurch
      (.snoc (.snoc Γ cnum) (.app (sucAddFamily i.succ) (.var 0)))
      (.app (sucAddFamily i.succ.succ) (csuc (.var 1))) cU0 :=
    .appElim (B := cU0) (sucAddFamily_typed (CTyped.weaken first)) (csuc_typed (.var 1))
  have inner := cpiT hypType goalType
  exact .lamIntro cnum_typed (.sort _) (cpiT cnum_typed inner) (.sort _)
    (.lamIntro hypType (.sort _) inner (.sort _) (sucAddStepBody_typed ha))

/-- The proof, as a term: for `a` and `b`, the recursor on `b`. -/
abbrev sucAddProof : CTm Tower.Head n :=
  .lam cnum (.lam cnum
    (cRecApp (sucAddFamily 1) (.refl (csuc (.var 1))) (sucAddStep 1) (.var 0)))

/-- **The successor of a number plus a number is identical to the successor of their sum**,
by induction on the second number. -/
theorem suc_add_identity :
    CTyped objectChurch Γ sucAddProof
      (.pi cnum (.pi cnum
        (.id cnum (cadd (csuc (.var 1)) (.var 0)) (csuc (cadd (.var 1) (.var 0)))))) := by
  have first : CTyped objectChurch (.snoc (.snoc Γ cnum) cnum) (.var 1) cnum := .var 1
  have body : CTyped objectChurch (.snoc (.snoc Γ cnum) cnum)
      (cRecApp (sucAddFamily 1) (.refl (csuc (.var 1))) (sucAddStep 1) (.var 0))
      (.id cnum (cadd (csuc (.var 1)) (.var 0)) (csuc (cadd (.var 1) (.var 0)))) :=
    .conv (numRec_typed (sucAddFamily_typed first) (sucAddBase_typed first)
      (sucAddStep_typed first) (.var 0)) (sucAddFamily_at first (.var 0)) (.sort _)
  have inner : CTyped objectChurch (.snoc Γ cnum)
      (.pi cnum (.id cnum (cadd (csuc (.var 1)) (.var 0)) (csuc (cadd (.var 1) (.var 0))))) cU0 :=
    cpiT cnum_typed (cidT cnum_typed (cadd_typed (csuc_typed (.var 1)) (.var 0))
      (csuc_typed (cadd_typed (.var 1) (.var 0))))
  exact .lamIntro cnum_typed (.sort _) (cpiT cnum_typed inner) (.sort _)
    (.lamIntro cnum_typed (.sort _) inner (.sort _) body)

/-! ## Addition is commutative -/

/-- The statement for a variable `a`, as a family over the numbers `b`: `a` plus `b` is
identical to `b` plus `a`. -/
abbrev commFamily (i : Fin n) : CTm Tower.Head n :=
  .lam cnum (.id cnum (cadd (.var i.succ) (.var 0)) (cadd (.var 0) (.var i.succ)))

theorem commBody_typed {i : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum) :
    CTyped objectChurch (.snoc Γ cnum)
      (.id cnum (cadd (.var i.succ) (.var 0)) (cadd (.var 0) (.var i.succ))) cU0 :=
  cidT cnum_typed (cadd_typed (CTyped.weaken ha) (.var 0)) (cadd_typed (.var 0) (CTyped.weaken ha))

theorem commFamily_typed {i : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum) :
    CTyped objectChurch Γ (commFamily i) (.pi cnum cU0) :=
  .lamIntro cnum_typed (.sort _) (cpiT (craise cnum_typed) cU0_typed) (.sort _)
    (commBody_typed ha)

theorem commFamily_at {i : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum)
    {t : CTm Tower.Head n} (ht : CTyped objectChurch Γ t cnum) :
    CEqual objectChurch Γ (.app (commFamily i) t)
      (.id cnum (cadd (.var i) t) (cadd t (.var i))) cU0 :=
  .betaPi (A := cnum) (B := cU0)
    (body := .id cnum (cadd (.var i.succ) (.var 0)) (cadd (.var 0) (.var i.succ)))
    (a := t) (cpiT (craise cnum_typed) cU0_typed) (.sort _) (commBody_typed ha) ht

/-- The base: `a` plus zero computes to `a`, and zero plus `a` is identical to `a` by the
first induction; symmetry turns it round. -/
abbrev commBase (i : Fin n) : CTm Tower.Head n :=
  symOf cnum (cadd czero (.var i)) (.var i) (.app zeroAddProof (.var i))

theorem commBase_typed {i : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum) :
    CTyped objectChurch Γ (commBase i) (.app (commFamily i) czero) := by
  have zeroAdd : CTyped objectChurch Γ (.app zeroAddProof (.var i))
      (.id cnum (cadd czero (.var i)) (.var i)) := .appElim zero_add_identity ha
  have turned := sym_typed cnum_typed (cadd_typed czero_typed ha) ha zeroAdd
  have computed : CEqual objectChurch Γ (.id cnum (cadd (.var i) czero) (cadd czero (.var i)))
      (.id cnum (.var i) (cadd czero (.var i))) cU0 :=
    .idCong (.refl cnum_typed) (.sort _) (cadd_zero ha) (.refl (cadd_typed czero_typed ha))
  exact .conv turned (.symm (.trans (commFamily_at ha czero_typed) computed)) (.sort _)

/-- The step over a number `k` and the induction hypothesis: the congruence of the hypothesis
under the successor, then the successor moved out of the sum on the other side. -/
abbrev commStepBody (i : Fin n) : CTm Tower.Head (n + 2) :=
  transOf cnum (csuc (cadd (.var i.succ.succ) (.var 1))) (csuc (cadd (.var 1) (.var i.succ.succ)))
    (cadd (csuc (.var 1)) (.var i.succ.succ))
    (congOf cnum cnum (.const sucN) (cadd (.var i.succ.succ) (.var 1))
      (cadd (.var 1) (.var i.succ.succ)) (.var 0))
    (symOf cnum (cadd (csuc (.var 1)) (.var i.succ.succ))
      (csuc (cadd (.var 1) (.var i.succ.succ)))
      (.app (.app sucAddProof (.var 1)) (.var i.succ.succ)))

theorem commStepBody_typed {i : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum) :
    CTyped objectChurch (.snoc (.snoc Γ cnum) (.app (commFamily i.succ) (.var 0)))
      (commStepBody i) (.app (commFamily i.succ.succ) (csuc (.var 1))) := by
  have first : CTyped objectChurch (.snoc (.snoc Γ cnum) (.app (commFamily i.succ) (.var 0)))
      (.var i.succ.succ) cnum := CTyped.weaken (CTyped.weaken ha)
  have number : CTyped objectChurch (.snoc (.snoc Γ cnum) (.app (commFamily i.succ) (.var 0)))
      (.var 1) cnum := .var 1
  have hypothesis : CTyped objectChurch
      (.snoc (.snoc Γ cnum) (.app (commFamily i.succ) (.var 0))) (.var 0)
      (.id cnum (cadd (.var i.succ.succ) (.var 1)) (cadd (.var 1) (.var i.succ.succ))) :=
    .conv (.var 0) (commFamily_at first number) (.sort _)
  have congruent := cong_suc (cadd_typed first number) (cadd_typed number first) hypothesis
  have moved : CTyped objectChurch (.snoc (.snoc Γ cnum) (.app (commFamily i.succ) (.var 0)))
      (.app (.app sucAddProof (.var 1)) (.var i.succ.succ))
      (.id cnum (cadd (csuc (.var 1)) (.var i.succ.succ))
        (csuc (cadd (.var 1) (.var i.succ.succ)))) :=
    .appElim (.appElim suc_add_identity number) first
  have turned := sym_typed cnum_typed (cadd_typed (csuc_typed number) first)
    (csuc_typed (cadd_typed number first)) moved
  have joined := trans_typed cnum_typed (csuc_typed (cadd_typed first number))
    (csuc_typed (cadd_typed number first)) (cadd_typed (csuc_typed number) first) congruent turned
  have computed : CEqual objectChurch (.snoc (.snoc Γ cnum) (.app (commFamily i.succ) (.var 0)))
      (.id cnum (cadd (.var i.succ.succ) (csuc (.var 1))) (cadd (csuc (.var 1)) (.var i.succ.succ)))
      (.id cnum (csuc (cadd (.var i.succ.succ) (.var 1)))
        (cadd (csuc (.var 1)) (.var i.succ.succ))) cU0 :=
    .idCong (.refl cnum_typed) (.sort _) (cadd_suc first number)
      (.refl (cadd_typed (csuc_typed number) first))
  exact .conv joined (.symm (.trans (commFamily_at first (csuc_typed number)) computed))
    (.sort _)

abbrev commStep (i : Fin n) : CTm Tower.Head n :=
  .lam cnum (.lam (.app (commFamily i.succ) (.var 0)) (commStepBody i))

theorem commStep_typed {i : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum) :
    CTyped objectChurch Γ (commStep i)
      (.pi cnum (.pi (.app (commFamily i.succ) (.var 0))
        (.app (commFamily i.succ.succ) (csuc (.var 1))))) := by
  have first : CTyped objectChurch (.snoc Γ cnum) (.var i.succ) cnum := CTyped.weaken ha
  have hypType : CTyped objectChurch (.snoc Γ cnum) (.app (commFamily i.succ) (.var 0)) cU0 :=
    .appElim (B := cU0) (commFamily_typed first) (.var 0)
  have goalType : CTyped objectChurch (.snoc (.snoc Γ cnum) (.app (commFamily i.succ) (.var 0)))
      (.app (commFamily i.succ.succ) (csuc (.var 1))) cU0 :=
    .appElim (B := cU0) (commFamily_typed (CTyped.weaken first)) (csuc_typed (.var 1))
  have inner := cpiT hypType goalType
  exact .lamIntro cnum_typed (.sort _) (cpiT cnum_typed inner) (.sort _)
    (.lamIntro hypType (.sort _) inner (.sort _) (commStepBody_typed ha))

/-- The proof, as a term. -/
abbrev addCommProof : CTm Tower.Head n :=
  .lam cnum (.lam cnum (cRecApp (commFamily 1) (commBase 1) (commStep 1) (.var 0)))

/-- **Addition is commutative**, by induction, in the judgment of the object package: a
closed term of type `Π (a b : num). Id num (add a b) (add b a)`. The base uses the first
induction (zero plus a number) and symmetry; the step uses congruence under the successor,
the second induction (the successor of a number plus a number), symmetry and transitivity. -/
theorem add_comm_identity :
    CTyped objectChurch Γ addCommProof
      (.pi cnum (.pi cnum (.id cnum (cadd (.var 1) (.var 0)) (cadd (.var 0) (.var 1))))) := by
  have first : CTyped objectChurch (.snoc (.snoc Γ cnum) cnum) (.var 1) cnum := .var 1
  have body : CTyped objectChurch (.snoc (.snoc Γ cnum) cnum)
      (cRecApp (commFamily 1) (commBase 1) (commStep 1) (.var 0))
      (.id cnum (cadd (.var 1) (.var 0)) (cadd (.var 0) (.var 1))) :=
    .conv (numRec_typed (commFamily_typed first) (commBase_typed first) (commStep_typed first)
      (.var 0)) (commFamily_at first (.var 0)) (.sort _)
  have inner : CTyped objectChurch (.snoc Γ cnum)
      (.pi cnum (.id cnum (cadd (.var 1) (.var 0)) (cadd (.var 0) (.var 1)))) cU0 :=
    cpiT cnum_typed (cidT cnum_typed (cadd_typed (.var 1) (.var 0)) (cadd_typed (.var 0) (.var 1)))
  exact .lamIntro cnum_typed (.sort _) (cpiT cnum_typed inner) (.sort _)
    (.lamIntro cnum_typed (.sort _) inner (.sort _) body)

/-- Positive: the proof at the numerals one and two. -/
theorem add_comm_identity_one_two :
    CTyped objectChurch .nil (.app (.app addCommProof (csuc czero)) (csuc (csuc czero)))
      (.id cnum (cadd (csuc czero) (csuc (csuc czero))) (cadd (csuc (csuc czero)) (csuc czero))) := by
  have atOne : CTyped objectChurch .nil (.app addCommProof (csuc czero))
      (.pi cnum (.id cnum (cadd (csuc czero) (.var 0)) (cadd (.var 0) (csuc czero)))) :=
    .appElim add_comm_identity (csuc_typed czero_typed)
  exact .appElim atOne (csuc_typed (csuc_typed czero_typed))

end Commutativity

/-- Negative: **no closed term is an identity proof that zero is one**, relative to
`CofinalInaccessibles`: in the set tower the successor of a number contains the number, and no
set contains itself. -/
theorem zero_not_identical_to_one (h : CofinalInaccessibles.{u}) (t : CTm Tower.Head 0) :
    ¬ CTyped objectChurch .nil t (.id cnum czero (csuc czero)) := fun typed => by
  have member := objectChurch_sound_tower h typed Fin.elim0 (sat_nil _ _ _)
  have same : ev (objHeads h) (objectSetConsts h) czero Fin.elim0 =
      ev (objHeads h) (objectSetConsts h) (csuc czero) Fin.elim0 :=
    ((mem_truthCode _ _).mp member).2
  have zeroNumber := objectChurch_sound_tower h (czero_typed (Γ := .nil)) Fin.elim0
    (sat_nil _ _ _)
  have successor : ev (objHeads h) (objectSetConsts h) (csuc czero) Fin.elim0 =
      insert (ev (objHeads h) (objectSetConsts h) czero Fin.elim0)
        (ev (objHeads h) (objectSetConsts h) czero Fin.elim0) :=
    suc_apply h (by rw [← setConst_num h]; exact zeroNumber)
  rw [successor] at same
  have inside : ev (objHeads h) (objectSetConsts h) czero Fin.elim0 ∈
      insert (ev (objHeads h) (objectSetConsts h) czero Fin.elim0)
        (ev (objHeads h) (objectSetConsts h) czero Fin.elim0) :=
    ZFSet.mem_insert _ _
  rw [← same] at inside
  exact ZFSet.mem_irrefl _ inside

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
