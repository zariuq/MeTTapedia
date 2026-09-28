import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.Basic

/-!
# Models of the `set:` profile and source-level controls

A proof modulo the stored equations is sound in every Henkin model of those
equations.  A model of the equations and of the assumed facts in which a
statement fails therefore shows that no proof of the statement exists from
those facts, whatever the proof term.

* In the numbers, the source proof of `zero-add` is sound, and a wrong
  conclusion has no proof.
* In the numbers extended by one integer chain, the equations of `add`,
  reflexivity and substitution hold but `zero-add` fails: the induction
  assumption cannot be dropped.
* In the numbers with `add` revised to `add n (suc m) = suc (suc (add n m))`,
  all three assumed facts hold and `zero-add` fails: a proof checked against
  the earlier definition does not survive the revision.
* Conversion articles preserve denotation, so an article relating
  `add zero (suc k)` to `suc (suc (add zero k))` does not exist.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.Models

open Mettapedia.Logic Mettapedia.Logic.HOL
open SetProfile

/-- An interpretation of the vocabulary: numbers, sets, and the operations the
developments use.  Separation, replacement and choice are interpreted
trivially; no statement below mentions them. -/
structure Interpretation where
  Num : Type 1
  Sets : Type 1
  zero : Num
  suc : Num → Num
  add : Num → Num → Num
  pow : Num → Sets → Sets
  member : Sets → Sets → Prop
  empty : Sets
  union : Sets → Sets
  power : Sets → Sets
  universeOf : Sets → Sets

namespace Interpretation

variable (I : Interpretation)

@[reducible] def carrier : SetBase → Type 1
  | .set => I.Sets
  | .num => I.Num

def constDen : {type : HOL.Ty SetBase} → SetConst type → Ty.denote.{0, 0} I.carrier type
  | _, .falsum => ULift.up False
  | _, .member => fun left right => ULift.up (I.member left right)
  | _, .empty => I.empty
  | _, .union => I.union
  | _, .power => I.power
  | _, .separation => fun set _ => set
  | _, .replacement => fun set _ => set
  | _, .epsilon => fun _ => I.empty
  | _, .universeOf => I.universeOf
  | _, .zero => I.zero
  | _, .suc => I.suc
  | _, .add => I.add
  | _, .pow => I.pow

/-- The standard Henkin model of the interpretation. -/
abbrev model : HenkinModel.{0, 0, 0} SetBase SetConst :=
  HenkinModel.standard.{0, 0, 0} I.carrier I.constDen

/-- The laws of the stored equations of `add` and `pow`. -/
structure Lawful : Prop where
  add_zero : ∀ x, I.add x I.zero = x
  add_suc : ∀ x y, I.add x (I.suc y) = I.suc (I.add x y)
  pow_zero : ∀ s, I.pow I.zero s = s
  pow_suc : ∀ count s, I.pow (I.suc count) s = I.power (I.pow count s)

/-- Induction over the numbers of the interpretation. -/
def Inductive : Prop :=
  ∀ P : I.Num → Prop, P I.zero → (∀ v, P v → P (I.suc v)) → ∀ x, P x

end Interpretation

/-- The valuation of the empty context. -/
def emptyValuation (M : HenkinModel.{0, 0, 0} SetBase SetConst) : HenkinModel.Valuation M [] :=
  fun v => nomatch v

theorem emptyValuation_admissible (M : HenkinModel.{0, 0, 0} SetBase SetConst) :
    HenkinModel.ValuationAdmissible M (emptyValuation M) :=
  fun v => nomatch v

theorem equationsHold {I : Interpretation} (lawful : I.Lawful) :
    Soundness.EquationsHold I.model sourceEquations := by
  intro equation listed ρ
  simp only [sourceEquations, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl
  · exact lawful.add_zero (ρ .vz)
  · exact lawful.add_suc (ρ (.vs .vz)) (ρ .vz)
  · exact lawful.pow_zero (ρ .vz)
  · exact lawful.pow_suc (ρ (.vs .vz)) (ρ .vz)

/-- A lawful interpretation is also a model of the equations with `Falsum`
defined: `Falsum` is read as falsity, the denotation of `∀p. p`. -/
theorem definedEquationsHold {I : Interpretation} (lawful : I.Lawful) :
    Soundness.EquationsHold I.model definedEquations := by
  intro equation listed ρ
  rcases List.mem_cons.mp listed with rfl | listed
  · exact congrArg ULift.up (propext ⟨False.elim, fun holds => holds (ULift.up False) trivial⟩)
  · exact equationsHold lawful equation listed ρ

theorem refl_holds (I : Interpretation) :
    (HenkinModel.denote I.model reflAxiom (emptyValuation I.model)).down :=
  fun _ _ => rfl

theorem subst_holds (I : Interpretation) :
    (HenkinModel.denote I.model substAxiom (emptyValuation I.model)).down := by
  intro predicate _ left _ right _ same holds
  have same' : left = right := same
  subst same'
  exact holds

theorem induction_holds {I : Interpretation} (inductive_ : I.Inductive) :
    (HenkinModel.denote I.model inductionAxiom (emptyValuation I.model)).down := by
  intro predicate _ base step x _
  exact inductive_ (fun y => (predicate y).down) base
    (fun v holds => step v trivial holds) x

/-- A proof modulo the equations from facts that hold is sound. -/
theorem proof_sound (I : Interpretation) {equations : List (DefiningEquation SetConst)}
    {assumptions : List (Formula SetConst [])} {statement : Formula SetConst []}
    (proof : ProofSyntaxModulo equations assumptions statement)
    (hold : Soundness.EquationsHold I.model equations)
    (facts : ∀ fact ∈ assumptions,
      (HenkinModel.denote I.model fact (emptyValuation I.model)).down) :
    (HenkinModel.denote I.model statement (emptyValuation I.model)).down :=
  Soundness.proofSyntaxModulo_sound proof hold (emptyValuation_admissible I.model) facts

theorem facts_hold {I : Interpretation} (inductive_ : I.Inductive) :
    ∀ fact ∈ zeroAddAssumptions, (HenkinModel.denote I.model fact (emptyValuation I.model)).down := by
  intro fact listed
  simp only [zeroAddAssumptions, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl
  · exact induction_holds inductive_
  · exact refl_holds I
  · exact subst_holds I

/-! ## The numbers -/

/-- The numbers, with sets interpreted by a single point. -/
abbrev naturals : Interpretation where
  Num := ULift.{1} ℕ
  Sets := PUnit.{2}
  zero := ⟨0⟩
  suc := fun number => ⟨number.down + 1⟩
  add := fun left right => ⟨left.down + right.down⟩
  pow := fun _ set => set
  member := fun _ _ => True
  empty := PUnit.unit
  union := id
  power := id
  universeOf := id

theorem naturals_lawful : naturals.Lawful where
  add_zero _ := rfl
  add_suc _ _ := rfl
  pow_zero _ := rfl
  pow_suc _ _ := rfl

theorem naturals_inductive : naturals.Inductive := by
  intro predicate base step x
  obtain ⟨number⟩ := x
  induction number with
  | zero => exact base
  | succ number ih => exact step ⟨number⟩ ih

/-- Positive control: the source proof of `zero-add` is sound in the numbers. -/
theorem zeroAdd_holds :
    (HenkinModel.denote naturals.model zeroAddStatement (emptyValuation naturals.model)).down :=
  proof_sound naturals zeroAddProof (equationsHold naturals_lawful) (facts_hold naturals_inductive)

/-- `∀ k. add k zero = suc k`, a wrong conclusion. -/
def wrongStatement : Formula SetConst [] :=
  .all (σ := numTy) (.eq (addT (.var .vz) zeroT) (sucT (.var .vz)))

/-- Wrong conclusion: no proof modulo the equations from the three assumed facts. -/
theorem no_wrong_conclusion :
    ¬ Nonempty (ProofSyntaxModulo sourceEquations zeroAddAssumptions wrongStatement) := by
  rintro ⟨proof⟩
  have holds := proof_sound naturals proof (equationsHold naturals_lawful)
    (facts_hold naturals_inductive)
  have atZero : (⟨0 + 0⟩ : ULift.{1} ℕ) = ⟨0 + 1⟩ := holds ⟨0⟩ trivial
  exact absurd (congrArg ULift.down atZero) (by decide)

/-! ## Induction cannot be dropped -/

/-- The successor of the numbers extended by one integer chain. -/
def chainSuc : ULift.{1} (ℕ ⊕ ℤ) → ULift.{1} (ℕ ⊕ ℤ)
  | ⟨.inl number⟩ => ⟨.inl (number + 1)⟩
  | ⟨.inr point⟩ => ⟨.inr (point + 1)⟩

/-- Addition that satisfies both equations of `add` and moves the chain. -/
def chainAdd (left : ULift.{1} (ℕ ⊕ ℤ)) : ULift.{1} (ℕ ⊕ ℤ) → ULift.{1} (ℕ ⊕ ℤ)
  | ⟨.inl number⟩ => chainSuc^[number] left
  | ⟨.inr point⟩ => ⟨.inr (point + 1)⟩

/-- The numbers followed by an integer chain on which `add zero` shifts. -/
abbrev chain : Interpretation where
  Num := ULift.{1} (ℕ ⊕ ℤ)
  Sets := PUnit.{2}
  zero := ⟨.inl 0⟩
  suc := chainSuc
  add := chainAdd
  pow := fun _ set => set
  member := fun _ _ => True
  empty := PUnit.unit
  union := id
  power := id
  universeOf := id

theorem chain_lawful : chain.Lawful where
  add_zero _ := rfl
  add_suc left right := by
    obtain ⟨right⟩ := right
    cases right with
    | inl number =>
        change chainSuc^[number + 1] left = chainSuc (chainSuc^[number] left)
        exact Function.iterate_succ_apply' chainSuc number left
    | inr point =>
        change (⟨.inr (point + 1 + 1)⟩ : ULift.{1} (ℕ ⊕ ℤ)) = ⟨.inr (point + 1 + 1)⟩
        rfl
  pow_zero _ := rfl
  pow_suc _ _ := rfl

/-- Dropped assumption: without induction, reflexivity and substitution do not
prove `zero-add` modulo the equations of `add`. -/
theorem induction_needed :
    ¬ Nonempty (ProofSyntaxModulo sourceEquations [reflAxiom, substAxiom] zeroAddStatement) := by
  rintro ⟨proof⟩
  have holds := proof_sound chain proof (equationsHold chain_lawful) (by
    intro fact listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl
    · exact refl_holds chain
    · exact subst_holds chain)
  have atChain : (⟨.inr (0 + 1)⟩ : ULift.{1} (ℕ ⊕ ℤ)) = ⟨.inr 0⟩ := holds ⟨.inr 0⟩ trivial
  exact absurd (congrArg ULift.down atChain) (by decide)

/-! ## Revised support -/

/-- `add n (suc m) = suc (suc (add n m))`: a revision of the successor equation. -/
def addSucTwiceEquation : DefiningEquation SetConst where
  context := [numTy, numTy]
  type := numTy
  left := addT (.var (.vs .vz)) (sucT (.var .vz))
  right := sucT (sucT (addT (.var (.vs .vz)) (.var .vz)))

def revisedEquations : List (DefiningEquation SetConst) :=
  [addZeroEquation, addSucTwiceEquation, powZeroEquation, powSucEquation]

/-- The numbers, with the revised addition `add n m = n + 2 m`. -/
abbrev doubling : Interpretation where
  Num := ULift.{1} ℕ
  Sets := PUnit.{2}
  zero := ⟨0⟩
  suc := fun number => ⟨number.down + 1⟩
  add := fun left right => ⟨left.down + 2 * right.down⟩
  pow := fun _ set => set
  member := fun _ _ => True
  empty := PUnit.unit
  union := id
  power := id
  universeOf := id

theorem doubling_revised : Soundness.EquationsHold doubling.model revisedEquations := by
  intro equation listed ρ
  simp only [revisedEquations, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl
  · change (⟨ULift.down (ρ .vz) + 2 * 0⟩ : ULift.{1} ℕ) = ρ .vz
    rfl
  · change (⟨ULift.down (ρ (.vs .vz)) + 2 * (ULift.down (ρ .vz) + 1)⟩ : ULift.{1} ℕ) =
      ⟨ULift.down (ρ (.vs .vz)) + 2 * ULift.down (ρ .vz) + 1 + 1⟩
    rfl
  · exact (rfl : doubling.pow doubling.zero (ρ .vz) = ρ .vz)
  · exact (rfl : doubling.pow (doubling.suc (ρ (.vs .vz))) (ρ .vz) =
      doubling.power (doubling.pow (ρ (.vs .vz)) (ρ .vz)))

theorem doubling_inductive : doubling.Inductive := by
  intro predicate base step x
  obtain ⟨number⟩ := x
  induction number with
  | zero => exact base
  | succ number ih => exact step ⟨number⟩ ih

/-- Stale support: after revising the successor equation of `add`, the three
assumed facts do not prove `zero-add` modulo the revised equations. -/
theorem revision_invalidates :
    ¬ Nonempty (ProofSyntaxModulo revisedEquations zeroAddAssumptions zeroAddStatement) := by
  rintro ⟨proof⟩
  have holds := proof_sound doubling proof doubling_revised (facts_hold doubling_inductive)
  have atOne : (⟨0 + 2 * 1⟩ : ULift.{1} ℕ) = ⟨1⟩ := holds ⟨1⟩ trivial
  exact absurd (congrArg ULift.down atOne) (by decide)

/-! ## Conversion articles -/

/-- Altered conversion data: no article relates `add zero (suc k)` and
`suc (suc (add zero k))`, since articles preserve denotation. -/
theorem no_altered_article :
    ¬ CoreConversion sourceEquations (Γ := [numTy]) (addT zeroT (sucT (.var .vz)))
      (sucT (sucT (addT zeroT (.var .vz)))) := by
  intro conversion
  have denotes := Soundness.coreConversion_denote naturals.model (equationsHold naturals_lawful)
    conversion (HenkinModel.extend naturals.model (σ := numTy) (emptyValuation naturals.model)
      (⟨0⟩ : ULift.{1} ℕ))
  have atZero : (⟨0 + (0 + 1)⟩ : ULift.{1} ℕ) = ⟨0 + 0 + 1 + 1⟩ := denotes
  exact absurd (congrArg ULift.down atZero) (by decide)

/-! ## Axiom audit -/

#print axioms zeroAdd_holds
#print axioms no_wrong_conclusion
#print axioms induction_needed
#print axioms revision_invalidates
#print axioms no_altered_article

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.Models
