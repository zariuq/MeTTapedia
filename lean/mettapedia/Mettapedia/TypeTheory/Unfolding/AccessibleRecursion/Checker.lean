import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Controls
import Mettapedia.GSLT.Logic.ObserverBubble

/-!
# The carved checker and its authority for the strong variant

A carved certificate is a finitely branching tree whose nodes record one rule
instance each (`CarvedWitness`).  Replay checks at each node that the recorded
premises and conclusion are exactly those of the instance, that a hypothesis
belongs to its list, and that a carved conversion step is a beta conversion,
decided by computing normal forms.  No node is ever checked by unfolding the
recursor: every unfolding in a carved certificate is a propositional
unfolding node, used through transports.

* The replay interface covers the carved rules exactly (`carvedInterface`).
* The carved checker is an exact authority for the carved variant
  (`carvedChecker_authority`).
* **Reflection at the trust boundary** (`strongChecker_authority`): for
  derivability of codes and for propositional equalities, the *strong*
  judgment holds exactly when the carved checker accepts some certificate.
  The strong variant's definitional equality, which may diverge, never has to
  be decided.
* The carved checker refuses every certificate for the definitional
  unfolding of the positive control (`checker_rejects_definitional_unfolding`),
  and accepts some certificate for its goal (`checker_accepts_positive`).

The link to observer-indexed bubbles: carved definitional equality has a
fragment decision whose fragment is every term (`carvedConvDecision`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Unfolding.AccessibleRecursion

open Mettapedia.Logic
open Mettapedia.TypeTheory.Unfolding
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.ObserverBubble
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT

deriving instance DecidableEq for Var
deriving instance DecidableEq for Term
deriving instance DecidableEq for Judgment

variable (A P : Ty)

/-- The data of one carved rule instance. -/
inductive CarvedWitness : Type
  | hyp (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (goal : Tm A P Γ prop)
  | impIntro (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (premise conclusion : Tm A P Γ prop)
  | impElim (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (premise conclusion : Tm A P Γ prop)
  | allIntro (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (σ : Ty)
      (quantifier : Var (signature A P) (quantTy σ)) (body : Tm A P Γ (.arr σ prop))
  | allElim (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (σ : Ty)
      (quantifier : Var (signature A P) (quantTy σ)) (body : Tm A P Γ (.arr σ prop))
      (witnessTerm : Tm A P Γ σ)
  | convert (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (source target : Tm A P Γ prop)
  | equalOfConv (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (T : Ty) (left right : Tm A P Γ T)
  | equalSymm (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (T : Ty) (left right : Tm A P Γ T)
  | equalTrans (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (T : Ty) (left middle right : Tm A P Γ T)
  | equalApp (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (T T' : Ty)
      (function function' : Tm A P Γ (.arr T T')) (argument argument' : Tm A P Γ T)
  | equalLam (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (T T' : Ty) (body body' : Tm A P (T :: Γ) T')
  | transport (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (T : Ty) (motive : Tm A P (T :: Γ) prop)
      (left right : Tm A P Γ T)
  | unfoldEqual (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (R : Tm A P Γ (relTy A))
      (F : Tm A P Γ (stepTy A P)) (point : Tm A P Γ A)
  | beta (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (T : Ty) (left right : Tm A P Γ T)
  | symm (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (T : Ty) (left right : Tm A P Γ T)
  | trans (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (T : Ty) (left middle right : Tm A P Γ T)
  | app (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (T T' : Ty)
      (function function' : Tm A P Γ (.arr T T')) (argument argument' : Tm A P Γ T)
  | lam (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (T T' : Ty) (body body' : Tm A P (T :: Γ) T')

variable {A P}

namespace CarvedWitness

/-- The premises of the recorded instance. -/
def premises : CarvedWitness A P → List (Judgment A P)
  | .hyp .. => []
  | .impIntro Γ hyps premise conclusion => [.holds Γ (premise :: hyps) conclusion]
  | .impElim Γ hyps premise conclusion => [.holds Γ hyps (imp premise conclusion), .holds Γ hyps premise]
  | .allIntro Γ hyps σ _ body => [.holds (σ :: Γ) (wkHyps hyps) (.app (wk body) (.var .zero))]
  | .allElim Γ hyps _ quantifier body _ => [.holds Γ hyps (all quantifier body)]
  | .convert Γ hyps source target => [.holds Γ hyps source, .conv Γ hyps prop source target]
  | .equalOfConv Γ hyps T left right => [.conv Γ hyps T left right]
  | .equalSymm Γ hyps T left right => [.equal Γ hyps T left right]
  | .equalTrans Γ hyps T left middle right =>
      [.equal Γ hyps T left middle, .equal Γ hyps T middle right]
  | .equalApp Γ hyps T T' function function' argument argument' =>
      [.equal Γ hyps (.arr T T') function function', .equal Γ hyps T argument argument']
  | .equalLam Γ hyps T T' body body' => [.equal (T :: Γ) (wkHyps hyps) T' body body']
  | .transport Γ hyps T motive left right =>
      [.equal Γ hyps T left right, .holds Γ hyps (inst motive left)]
  | .unfoldEqual Γ hyps R F point => [.holds Γ hyps (accCode R point), .holds Γ hyps (respCode R F)]
  | .beta .. => []
  | .symm Γ hyps T left right => [.conv Γ hyps T left right]
  | .trans Γ hyps T left middle right => [.conv Γ hyps T left middle, .conv Γ hyps T middle right]
  | .app Γ hyps T T' function function' argument argument' =>
      [.conv Γ hyps (.arr T T') function function', .conv Γ hyps T argument argument']
  | .lam Γ hyps T T' body body' => [.conv (T :: Γ) (wkHyps hyps) T' body body']

/-- The conclusion of the recorded instance. -/
def conclusion : CarvedWitness A P → Judgment A P
  | .hyp Γ hyps goal => .holds Γ hyps goal
  | .impIntro Γ hyps premise conclusion => .holds Γ hyps (imp premise conclusion)
  | .impElim Γ hyps _ conclusion => .holds Γ hyps conclusion
  | .allIntro Γ hyps _ quantifier body => .holds Γ hyps (all quantifier body)
  | .allElim Γ hyps _ _ body witnessTerm => .holds Γ hyps (.app body witnessTerm)
  | .convert Γ hyps _ target => .holds Γ hyps target
  | .equalOfConv Γ hyps T left right => .equal Γ hyps T left right
  | .equalSymm Γ hyps T left right => .equal Γ hyps T right left
  | .equalTrans Γ hyps T left _ right => .equal Γ hyps T left right
  | .equalApp Γ hyps _ T' function function' argument argument' =>
      .equal Γ hyps T' (.app function argument) (.app function' argument')
  | .equalLam Γ hyps T T' body body' => .equal Γ hyps (.arr T T') (.lam body) (.lam body')
  | .transport Γ hyps _ motive _ right => .holds Γ hyps (inst motive right)
  | .unfoldEqual Γ hyps R F point => .equal Γ hyps P (recTerm R F point) (unfoldTerm R F point)
  | .beta Γ hyps T left right => .conv Γ hyps T left right
  | .symm Γ hyps T left right => .conv Γ hyps T right left
  | .trans Γ hyps T left _ right => .conv Γ hyps T left right
  | .app Γ hyps _ T' function function' argument argument' =>
      .conv Γ hyps T' (.app function argument) (.app function' argument')
  | .lam Γ hyps T T' body body' => .conv Γ hyps (.arr T T') (.lam body) (.lam body')

/-- The side condition of the recorded instance: membership of a hypothesis,
and beta conversion decided by normalization. -/
def sideCondition : CarvedWitness A P → Bool
  | .hyp _ hyps goal => decide (goal ∈ hyps)
  | .beta _ _ _ left right => decideCarvedConv left right
  | _ => true

/-- A witness whose side condition holds records a carved rule instance. -/
theorem instance_of_sideCondition (witness : CarvedWitness A P)
    (side : witness.sideCondition = true) :
    (unfoldingSplit A P).carved witness.premises witness.conclusion := by
  cases witness with
  | hyp Γ hyps goal => exact Or.inl (SharedRule.hyp (of_decide_eq_true side))
  | impIntro Γ hyps premise conclusion => exact Or.inl (SharedRule.impIntro premise conclusion)
  | impElim Γ hyps premise conclusion => exact Or.inl (SharedRule.impElim premise conclusion)
  | allIntro Γ hyps σ quantifier body => exact Or.inl (SharedRule.allIntro quantifier body)
  | allElim Γ hyps σ quantifier body witnessTerm =>
      exact Or.inl (SharedRule.allElim quantifier body witnessTerm)
  | convert Γ hyps source target => exact Or.inl (SharedRule.convert source target)
  | equalOfConv Γ hyps T left right => exact Or.inl (SharedRule.equalOfConv left right)
  | equalSymm Γ hyps T left right => exact Or.inl (SharedRule.equalSymm left right)
  | equalTrans Γ hyps T left middle right =>
      exact Or.inl (SharedRule.equalTrans left middle right)
  | equalApp Γ hyps T T' function function' argument argument' =>
      exact Or.inl (SharedRule.equalApp function function' argument argument')
  | equalLam Γ hyps T T' body body' => exact Or.inl (SharedRule.equalLam body body')
  | transport Γ hyps T motive left right => exact Or.inl (SharedRule.transport motive left right)
  | unfoldEqual Γ hyps R F point => exact Or.inl (SharedRule.unfoldEqual R F point rfl)
  | beta Γ hyps T left right =>
      exact Or.inr (ConvRule.beta left right
        (carved_conv_iff.mp ((decideCarvedConv_iff (hyps := hyps)).mp side)))
  | symm Γ hyps T left right => exact Or.inr (ConvRule.symm left right)
  | trans Γ hyps T left middle right => exact Or.inr (ConvRule.trans left middle right)
  | app Γ hyps T T' function function' argument argument' =>
      exact Or.inr (ConvRule.app function function' argument argument')
  | lam Γ hyps T T' body body' => exact Or.inr (ConvRule.lam body body')

/-- Every carved rule instance is recorded by a witness whose side condition
holds. -/
theorem exists_of_instance {premises : List (Judgment A P)} {conclusion : Judgment A P}
    (rule : (unfoldingSplit A P).carved premises conclusion) :
    ∃ witness : CarvedWitness A P, witness.sideCondition = true ∧
      witness.premises = premises ∧ witness.conclusion = conclusion := by
  rcases rule with rule | rule
  · cases rule with
    | @hyp Γ hyps goal member => exact ⟨.hyp Γ hyps goal, decide_eq_true member, rfl, rfl⟩
    | @impIntro Γ hyps premise conclusion =>
        exact ⟨.impIntro Γ hyps premise conclusion, rfl, rfl, rfl⟩
    | @impElim Γ hyps premise conclusion =>
        exact ⟨.impElim Γ hyps premise conclusion, rfl, rfl, rfl⟩
    | @allIntro Γ hyps σ quantifier body =>
        exact ⟨.allIntro Γ hyps σ quantifier body, rfl, rfl, rfl⟩
    | @allElim Γ hyps σ quantifier body witnessTerm =>
        exact ⟨.allElim Γ hyps σ quantifier body witnessTerm, rfl, rfl, rfl⟩
    | @convert Γ hyps source target => exact ⟨.convert Γ hyps source target, rfl, rfl, rfl⟩
    | @equalOfConv Γ hyps T left right => exact ⟨.equalOfConv Γ hyps T left right, rfl, rfl, rfl⟩
    | @equalSymm Γ hyps T left right => exact ⟨.equalSymm Γ hyps T left right, rfl, rfl, rfl⟩
    | @equalTrans Γ hyps T left middle right =>
        exact ⟨.equalTrans Γ hyps T left middle right, rfl, rfl, rfl⟩
    | @equalApp Γ hyps T T' function function' argument argument' =>
        exact ⟨.equalApp Γ hyps T T' function function' argument argument', rfl, rfl, rfl⟩
    | @equalLam Γ hyps T T' body body' => exact ⟨.equalLam Γ hyps T T' body body', rfl, rfl, rfl⟩
    | @transport Γ hyps T motive left right =>
        exact ⟨.transport Γ hyps T motive left right, rfl, rfl, rfl⟩
    | @unfoldEqual Γ hyps R F point _ => exact ⟨.unfoldEqual Γ hyps R F point, rfl, rfl, rfl⟩
  · cases rule with
    | @beta Γ hyps T left right convertible =>
        exact ⟨.beta Γ hyps T left right,
          (decideCarvedConv_iff (hyps := hyps)).mpr (carved_conv_iff.mpr convertible), rfl, rfl⟩
    | @symm Γ hyps T left right => exact ⟨.symm Γ hyps T left right, rfl, rfl, rfl⟩
    | @trans Γ hyps T left middle right => exact ⟨.trans Γ hyps T left middle right, rfl, rfl, rfl⟩
    | @app Γ hyps T T' function function' argument argument' =>
        exact ⟨.app Γ hyps T T' function function' argument argument', rfl, rfl, rfl⟩
    | @lam Γ hyps T T' body body' => exact ⟨.lam Γ hyps T T' body body', rfl, rfl, rfl⟩

end CarvedWitness

variable (A P)

/-- The replay interface of the carved rules. -/
def carvedInterface : RuleWitness.{0, 0} (unfoldingSplit A P).carved where
  W := CarvedWitness A P
  isInstance witness premises conclusion :=
    witness.sideCondition && decide (witness.premises = premises) &&
      decide (witness.conclusion = conclusion)
  sound := by
    intro witness premises conclusion accepted
    simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
    obtain ⟨⟨side, premisesEq⟩, conclusionEq⟩ := accepted
    subst premisesEq
    subst conclusionEq
    exact witness.instance_of_sideCondition side
  complete := by
    intro premises conclusion rule
    obtain ⟨witness, side, premisesEq, conclusionEq⟩ := CarvedWitness.exists_of_instance rule
    exact ⟨witness, by simp [side, premisesEq, conclusionEq]⟩

/-- **The carved checker**: replay of carved certificates. -/
abbrev carvedChecker : Checker (Judgment A P) (Derivation (Judgment A P) (CarvedWitness A P)) :=
  (unfoldingSplit A P).carvedChecker (carvedInterface A P)

variable {A P}

/-- The carved checker is an exact authority for the carved variant. -/
theorem carvedChecker_authority : (carvedChecker A P).Authority (Carved A P) :=
  (unfoldingSplit A P).carvedChecker_authority (carvedInterface A P)

/-- **Reflection at the trust boundary.**  On judgments read as themselves,
the strong judgment holds exactly when the carved checker accepts some
certificate. -/
theorem strongChecker_authority :
    ((unfoldingSplit A P).fixedChecker (carvedInterface A P)).Authority
      (fun claim => Strong A P claim.1) :=
  (unfoldingSplit A P).strongChecker_authority (carvedInterface A P) shared_reflects conv_reflects
    unfold_reflects

/-- A code is strongly derivable exactly when the carved checker accepts some
certificate for it. -/
theorem strong_holds_iff_accepted {Γ : List Ty} {hyps : List (Tm A P Γ prop)}
    {goal : Tm A P Γ prop} :
    Strong A P (.holds Γ hyps goal) ↔
      ∃ certificate, (carvedChecker A P).check (.holds Γ hyps goal) certificate = true :=
  (strongChecker_authority (A := A) (P := P)).meaning_iff_exists_certificate
    ⟨.holds Γ hyps goal, rfl⟩

/-- **The carved checker refuses the definitional unfolding** of the positive
control: no certificate for it is accepted. -/
theorem checker_rejects_definitional_unfolding (certificate : Derivation (Judgment A P) (CarvedWitness A P)) :
    (carvedChecker A P).check
      (.conv (positiveContext A P) positiveHyps P positiveRec positiveUnfold) certificate = false := by
  cases accepted : (carvedChecker A P).check
    (.conv (positiveContext A P) positiveHyps P positiveRec positiveUnfold) certificate with
  | false => rfl
  | true =>
      exact absurd (carvedChecker_authority.sound _ certificate accepted) positive_carved_not_conv

/-- The carved checker accepts some certificate for the positive control's
goal, whose strong derivation unfolds definitionally. -/
theorem checker_accepts_positive :
    ∃ certificate, (carvedChecker A P).check
      (.holds (positiveContext A P) positiveHyps (.app positivePredicate positiveUnfold))
      certificate = true :=
  strong_holds_iff_accepted.mp positive_strong

/-! ## The observer-indexed link -/

/-- Carved definitional equality has a fragment decision whose fragment is
every term. -/
def carvedConvDecision (Γ : List Ty) (hyps : List (Tm A P Γ prop)) (T : Ty) :
    FragmentDecision (fun left right : Tm A P Γ T => Carved A P (.conv Γ hyps T left right)) where
  Fragment := fun _ => True
  fragmentDecidable := fun _ => instDecidableTrue
  answer left right _ _ := decideCarvedConv left right
  answer_exact _ _ _ _ := decideCarvedConv_iff

/-- The verdict of the carved decision is exact on every pair of terms. -/
theorem carvedConvDecision_exact {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T : Ty}
    (left right : Tm A P Γ T) :
    ((carvedConvDecision Γ hyps T).verdict left right).asBool = some true ↔
      Carved A P (.conv Γ hyps T left right) :=
  (carvedConvDecision Γ hyps T).verdict_asBool_true_iff trivial trivial

end Mettapedia.TypeTheory.Unfolding.AccessibleRecursion
