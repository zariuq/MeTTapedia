import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipSentences
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastModalities

/-!
# Hereditary finiteness as a core sentence of set theory

A past modality of the membership language ranges over the hereditarily finite sets containing a set, and a quantifier
over the type over all hereditarily finite sets. To state them as core sentences, hereditary finiteness is written in
the logic of the sets itself, with no constant beyond membership:

- **Built sets** (`hfFormula y`): every predicate holding of the empty sets and of every set adjoining to a set it
  holds of a new member it holds of (`buildClosed`) holds of `y`. It is an impredicative definition over the
  predicates. A new member is not a member already, so building counts members.
- **It means hereditary finiteness** (`denote_hfFormula`): in the model of the sets, it holds of exactly the
  hereditarily finite sets.
- **It is its own induction principle**: a proof that a property is closed under building proves the property of
  every set the sentence holds of.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Ty Ctx Var Term ClosedFormula HenkinModel weaken rename subst instantiate Subst Rename)
open Mettapedia.Logic.HOL.ImpredicativeConnectives (truth falsity conjunctionFormula disjunctionFormula
  existentialInline)
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol model member)

variable {Γ : Ctx Unit}

/-! ## The sentence -/

/-- `z` is empty. -/
def emptyCore (z : Term Symbol Γ setTy) : Term Symbol Γ .prop := .all (σ := setTy) (negCore (member (.var .vz) (weaken z)))

/-- `z` has the members of `a` and the set `b`. -/
def adjoins (z a b : Term Symbol Γ setTy) : Term Symbol Γ .prop :=
  .all (σ := setTy) (iffCore (member (.var .vz) (weaken z))
    (disjunctionFormula (member (.var .vz) (weaken a)) (sameMembers (.var .vz) (weaken b))))

/-- **One building step**: if `p` holds of `a` and of `b`, `b` is not a member of `a`, and `z` adjoins `b` to `a`, then
`p` holds of `z`. -/
def buildStep (p : Term Symbol Γ predTy) (a b z : Term Symbol Γ setTy) : Term Symbol Γ .prop :=
  .imp (.app p a) (.imp (.app p b) (.imp (negCore (member b a)) (.imp (adjoins z a b) (.app p z))))

/-- **Closed under building**: a predicate holding of the empty sets and of every set adjoining to a set `a` it holds
of a set `b` it holds of, when `b` is not a member of `a`. -/
def buildClosed (p : Term Symbol Γ predTy) : Term Symbol Γ .prop :=
  conjunctionFormula
    (.all (σ := setTy) (.imp (emptyCore (.var .vz)) (.app (weaken p) (.var .vz))))
    (.all (σ := setTy) (.all (σ := setTy) (.all (σ := setTy)
      (buildStep (weaken (weaken (weaken p))) (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)))))

/-- **Hereditarily finite**: every predicate closed under building holds of `y`. -/
def hfFormula (y : Term Symbol Γ setTy) : Term Symbol Γ .prop :=
  .all (σ := predTy) (.imp (buildClosed (.var .vz)) (.app (.var .vz) (weaken y)))

/-! ## What it means -/

variable (valuation : model.{0}.Valuation Γ)

theorem denote_emptyCore (z : Term Symbol Γ setTy) :
    (model.denote (emptyCore z) valuation).down ↔ ∀ c, c ∉ setValue z valuation := by
  change (∀ c : ZFSet.{0}, True → (model.denote (negCore (member (.var .vz) (weaken z)))
    (model.extend (σ := setTy) valuation c)).down) ↔ _
  simp only [true_implies, denote_negCore, denote_member, setValue_weaken_set, setValue_newest]

theorem denote_adjoins (z a b : Term Symbol Γ setTy) :
    (model.denote (adjoins z a b) valuation).down ↔
      ∀ c, c ∈ setValue z valuation ↔ c ∈ setValue a valuation ∨ c = setValue b valuation := by
  change (∀ c : ZFSet.{0}, True → (model.denote (iffCore (member (.var .vz) (weaken z))
    (disjunctionFormula (member (.var .vz) (weaken a)) (sameMembers (.var .vz) (weaken b))))
      (model.extend (σ := setTy) valuation c)).down) ↔ _
  simp only [true_implies, denote_iffCore, denote_disjunctionFormula, denote_member, denote_sameMembers,
    setValue_newest, setValue_weaken_set]

/-- What closure under building says of a predicate. -/
def BuildClosed (P : ZFSet.{0} → Prop) : Prop :=
  (∀ z, (∀ c, c ∉ z) → P z) ∧ ∀ a b z, P a → P b → b ∉ a → (∀ c, c ∈ z ↔ c ∈ a ∨ c = b) → P z

theorem denote_weaken3 {σ₁ σ₂ σ₃ τ : Ty Unit} (p : Term Symbol Γ τ) (first : Ty.denote model.{0}.Carrier σ₁)
    (second : Ty.denote model.{0}.Carrier σ₂) (third : Ty.denote model.{0}.Carrier σ₃) :
    model.denote (weaken (σ := σ₃) (weaken (σ := σ₂) (weaken (σ := σ₁) p)))
        (model.extend (model.extend (model.extend valuation first) second) third) =
      model.denote p valuation := by
  rw [Mettapedia.Logic.HOL.Soundness.denote_weaken, Mettapedia.Logic.HOL.Soundness.denote_weaken,
    Mettapedia.Logic.HOL.Soundness.denote_weaken]

theorem denote_buildClosed (p : Term Symbol Γ predTy) :
    (model.denote (buildClosed p) valuation).down ↔ BuildClosed fun w => (model.denote p valuation w).down := by
  rw [buildClosed, denote_conjunctionFormula]
  apply and_congr
  · change (∀ z : ZFSet.{0}, True → (model.denote (emptyCore (.var .vz)) (model.extend (σ := setTy) valuation z)).down →
      (model.denote (weaken p) (model.extend (σ := setTy) valuation z) z).down) ↔ _
    simp only [true_implies, denote_emptyCore, setValue_newest]
    exact forall_congr' fun z => imp_congr_right fun _ =>
      Iff.of_eq (congrArg (fun f => (f z).down)
        (Mettapedia.Logic.HOL.Soundness.denote_weaken (σ := setTy) model p valuation z))
  · change (∀ a : ZFSet.{0}, True → ∀ b : ZFSet.{0}, True → ∀ z : ZFSet.{0}, True →
      (model.denote (weaken (weaken (weaken p)))
        (model.extend (σ := setTy) (model.extend (σ := setTy) (model.extend (σ := setTy) valuation a) b) z) a).down →
      (model.denote (weaken (weaken (weaken p)))
        (model.extend (σ := setTy) (model.extend (σ := setTy) (model.extend (σ := setTy) valuation a) b) z) b).down →
      (model.denote (negCore (member (.var (.vs .vz)) (.var (.vs (.vs .vz)))))
        (model.extend (σ := setTy) (model.extend (σ := setTy) (model.extend (σ := setTy) valuation a) b) z)).down →
      (model.denote (adjoins (.var .vz) (.var (.vs (.vs .vz))) (.var (.vs .vz)))
        (model.extend (σ := setTy) (model.extend (σ := setTy) (model.extend (σ := setTy) valuation a) b) z)).down →
      (model.denote (weaken (weaken (weaken p)))
        (model.extend (σ := setTy) (model.extend (σ := setTy) (model.extend (σ := setTy) valuation a) b) z) z).down) ↔ _
    simp only [true_implies, denote_adjoins, denote_negCore, denote_member]
    have weakened : ∀ (a b z w : ZFSet.{0}), (model.denote (weaken (weaken (weaken p)))
        (model.extend (σ := setTy) (model.extend (σ := setTy) (model.extend (σ := setTy) valuation a) b) z) w).down ↔
          (model.denote p valuation w).down :=
      fun a b z w => Iff.of_eq (congrArg (fun f => (f w).down)
        (denote_weaken3 (σ₁ := setTy) (σ₂ := setTy) (σ₃ := setTy) valuation p a b z))
    constructor
    · intro every a b z pa pb fresh same
      exact (weakened a b z z).mp (every a b z ((weakened a b z a).mpr pa) ((weakened a b z b).mpr pb) fresh same)
    · intro every a b z pa pb fresh same
      exact (weakened a b z z).mpr (every a b z ((weakened a b z a).mp pa) ((weakened a b z b).mp pb) fresh same)

theorem buildClosed_isHFSet : BuildClosed IsHFSet := by
  refine ⟨fun z empty => ⟨zero, zero_hf, ?_⟩, fun a b z ha hb _ same => ?_⟩
  · apply ZFSet.ext
    intro c
    simp only [zero, zfOf_set, mem_zfOfList]
    exact ⟨fun ⟨_, found, _⟩ => absurd found List.not_mem_nil, fun inside => absurd inside (empty c)⟩
  · have zEq : z = insert b a := ZFSet.ext fun c => by
      rw [same c, ZFSet.mem_insert_iff]
      exact or_comm
    rw [zEq]
    exact isHFSet_insert hb ha

theorem buildClosed_of_isHFSet {P : ZFSet.{0} → Prop} (closed : BuildClosed P) :
    ∀ {term : Pattern}, IsHF term → P (zfOf term) := by
  intro term holds
  induction holds with
  | atom atom => exact absurd atom (membership_pure _)
  | @members values all ih =>
    induction values with
    | nil =>
      apply closed.1
      intro c inside
      simp only [zfOf_set, mem_zfOfList] at inside
      obtain ⟨_, found, _⟩ := inside
      exact List.not_mem_nil found
    | cons value values tailIh =>
      have tail := tailIh (fun other found => all other (List.mem_cons_of_mem _ found))
        (fun other found => ih other (List.mem_cons_of_mem _ found))
      rw [zfOf_cons_set]
      by_cases old : zfOf value ∈ zfOf (set values)
      · have same : insert (zfOf value) (zfOf (set values)) = zfOf (set values) := ZFSet.ext fun c => by
          rw [ZFSet.mem_insert_iff]
          exact ⟨fun found => found.elim (fun eq => eq ▸ old) id, Or.inr⟩
        rw [same]
        exact tail
      · apply closed.2 _ (zfOf value) _ tail (ih value List.mem_cons_self) old
        intro c
        rw [ZFSet.mem_insert_iff]
        exact or_comm

/-- **The sentence means hereditary finiteness.** -/
theorem denote_hfFormula (y : Term Symbol Γ setTy) :
    (model.denote (hfFormula y) valuation).down ↔ IsHFSet (setValue y valuation) := by
  change (∀ predicate, _ → (model.denote (buildClosed (.var .vz)) (model.extend (σ := predTy) valuation predicate)).down →
    (predicate (model.denote (weaken y) (model.extend (σ := predTy) valuation predicate))).down) ↔ _
  constructor
  · intro every
    have := every (fun w => .up (IsHFSet w)) trivial
      ((denote_buildClosed _ (.var .vz)).mpr buildClosed_isHFSet)
    exact (congrArg IsHFSet (Mettapedia.Logic.HOL.Soundness.denote_weaken (σ := predTy) model y valuation
      (fun w => .up (IsHFSet w)))).mp this
  · rintro ⟨term, holds, same⟩ predicate _ closed
    have built := buildClosed_of_isHFSet ((denote_buildClosed _ (.var .vz)).mp closed) holds
    exact (congrArg (fun w => (predicate w).down)
      ((Mettapedia.Logic.HOL.Soundness.denote_weaken (σ := predTy) model y valuation predicate).trans same.symm)).mpr
      built

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
