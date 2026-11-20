import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerSyntaxEval
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CallAbstraction

/-!
# The limit of recursive families, and why typed syntax needs an earlier carrier

A family declared by structural recursion on its index (`DeclaresRecursion`, with a universe as
result) is defined at each constructor of the index by a right-hand side typed in the **earlier
stage** `R₀`, the package before the family. Two facts make this a limit:

* **A constant the package does not declare occurs in no derivable judgment** (`free_of_undeclared`),
  so every right-hand side is free of the family (`body_free`): the family refers to itself only
  through the recursive calls the equation supplies, on the fields of the index's constructor.
* **At a constructor without fields there is no recursive call**: the family at that index steps to a
  term free of the family (`nullary_unfolds`).

So at a nullary index such as `tnum`, the family is a type the earlier stage already has. A
constructor whose arguments sit at the index of its result, `add : exp tnum → exp tnum → exp tnum`,
needs a type that refers to itself at that index; a recursive family on the index alone cannot write
one, and the earlier stage must already contain it. In this model that is a simple inductive type,
the only self-referential case of the logical relation. The typed-syntax package takes exactly that
route: the untyped expressions `raw`, then the typing relation, and `exp t = Σ (r : raw). typed r t`,
where `exp tnum` has two different constructors, `lit` and `add` (`lit_two_ne_three`, `lit_ne_add`).

**Control**: the naive right-hand side at `tnum`, a Boolean tag choosing between a literal and a pair
of expressions at the same index, is typed in no stage that does not declare the family
(`naive_not_typed`), so no declaration by recursion on the index has it as its unfolding.
**Non-vacuity**: the package's value type `val` is such a family, and the theorem applies to it
(`val_tnum_unfolds`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType applyClosed)
open TowerNumbersModel (num zero succ numRec ctors u)
open TowerVectorsModel (unit tt U0 numC unitC)

namespace TowerSyntaxLimit

variable {Head : Type}

/-! ## Constants of derivable judgments are declared -/

/-- What a judgment says about the constant `f`: its subjects do not mention `f`. -/
def StatementFree (f : DeclName) : Statement Head → Prop
  | .typing _ t _ => ConstFree f t
  | .equality _ a b _ => ConstFree f a ∧ ConstFree f b
  | .sub _ _ _ => True

/-- **A constant the package does not declare occurs in no typed term**, and in neither side of a
derivable equality. -/
theorem free_of_undeclared {R : Rules Head} {f : DeclName} (undeclared : R.constantType f = none)
    {st : Statement Head} (derivation : Derivable R st) : StatementFree f st := by
  induction derivation with
  | headType _ => trivial
  | var _ => trivial
  | const declared _ _ _ =>
      show _ ≠ f
      rintro rfl
      rw [undeclared] at declared
      cases declared
  | piForm _ _ _ _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | sigmaForm _ _ _ _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | lamIntro _ _ _ _ ihBody => exact ihBody
  | appElim _ _ ihF ihA => exact ⟨ihF, ihA⟩
  | pairIntro _ _ _ _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | fstElim _ ih => exact ih
  | sndElim _ ih => exact ih
  | idForm _ _ _ _ ihA iha ihb => exact ⟨ihA, iha, ihb⟩
  | reflIntro _ ih => exact ih
  | sub _ _ ihT _ => exact ihT
  | conv _ _ _ ihT _ => exact ihT
  | refl _ ih => exact ⟨ih, ih⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | convEq _ _ _ ih _ => exact ih
  | subEq _ _ ihE _ => exact ihE
  | headEq _ _ _ _ _ => exact ⟨trivial, trivial⟩
  | piCong _ _ _ _ _ ihA ihB => exact ⟨⟨ihA.1, ihB.1⟩, ⟨ihA.2, ihB.2⟩⟩
  | sigmaCong _ _ _ _ _ ihA ihB => exact ⟨⟨ihA.1, ihB.1⟩, ⟨ihA.2, ihB.2⟩⟩
  | idCong _ _ _ _ ihA iha ihb => exact ⟨⟨ihA.1, iha.1, ihb.1⟩, ⟨ihA.2, iha.2, ihb.2⟩⟩
  | lamCong _ _ _ _ ihBody => exact ⟨ihBody.1, ihBody.2⟩
  | appCong _ _ ihF ihA => exact ⟨⟨ihF.1, ihA.1⟩, ⟨ihF.2, ihA.2⟩⟩
  | pairCong _ _ _ _ _ ihA ihB => exact ⟨⟨ihA.1, ihB.1⟩, ⟨ihA.2, ihB.2⟩⟩
  | fstCong _ ih => exact ⟨ih.1, ih.2⟩
  | sndCong _ ih => exact ⟨ih.1, ih.2⟩
  | reflCong _ ih => exact ⟨ih.1, ih.2⟩
  | betaPi _ _ _ _ _ ihBody ihA => exact ⟨⟨ihBody, ihA⟩, ConstFree.inst0 ihA ihBody⟩
  | betaFst _ _ _ _ _ ihA ihB => exact ⟨⟨ihA, ihB⟩, ihA⟩
  | betaSnd _ _ _ _ _ ihA ihB => exact ⟨⟨ihA, ihB⟩, ihB⟩
  | root _ _ _ ihL ihR => exact ⟨ihL, ihR⟩
  | etaPi _ _ _ ihF ihG _ => exact ⟨ihF, ihG⟩
  | etaSigma _ _ _ _ ihP ihQ _ _ => exact ⟨ihP, ihQ⟩
  | subEqual _ _ _ => trivial
  | subUniv _ => trivial
  | subPi _ _ _ _ _ _ _ _ _ _ _ => trivial
  | subSigma _ _ _ _ _ _ _ _ _ _ => trivial
  | subTrans _ _ _ _ => trivial

/-- A term typed in a package that does not declare `f` does not mention `f`. -/
theorem typed_free {R : Rules Head} {f : DeclName} (undeclared : R.constantType f = none) {n : Nat}
    {Γ : Ctx Head n} {t A : Tm Head n} (typing : Typed R Γ t A) : ConstFree f t :=
  free_of_undeclared undeclared typing

/-! ## The unfolding of a recursive family -/

/-- The match of a constructor without fields only uses the arguments. -/
theorem matchSub_nullary_free {f : DeclName} {s m : Nat} :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m), (∀ i, ConstFree f (σ i)) →
      ∀ i, ConstFree f (matchSub s 0 ([] : List (Tm Head m)) d σ i)
  | 0, _, free, i => free i.succ
  | d + 1, σ, free, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact free 0
      · exact matchSub_nullary_free d (tailSub σ) (fun j => free j.succ) j

variable {L : Type} [LevelOrder L] {S : Setting Head L} {R₀ : Rules Head} {f T : DeclName}
  {ctors : List (DeclName × List (Field Head))} {e : (i : Nat) → Tm Head i} {s d : Nat}
  {C : Tm Head (s + 1 + d)}
  {body : (k : DeclName) → (fields : List (Field Head)) →
    Tm Head (s + fields.length + d + (recPositions fields).length)}

/-- **Every right-hand side of a recursive family is free of the family**, when its earlier stage
does not declare it: the family occurs in an unfolding only through the recursive calls substituted
for the hypotheses, which are calls on the fields of the index's constructor. -/
theorem body_free (decl : DeclaresRecursion S R₀ f T ctors e s d C body)
    (undeclared : R₀.constantType f = none) {k : DeclName} {fields : List (Field Head)}
    (mem : (k, fields) ∈ ctors) : ConstFree f (body k fields) :=
  typed_free undeclared (decl.bodyTyped mem)

/-- **The incumbent's limit, at a nullary index**: let `f` be declared by structural recursion over
an earlier stage that does not declare it. At a constructor `k` of the index type without fields,
the application of `f` at arguments free of `f` steps to a term free of `f`: the family at `k` is
defined without reference to itself. -/
theorem nullary_unfolds (decl : DeclaresRecursion S R₀ f T ctors e s d C body)
    (undeclared : R₀.constantType f = none) {k : DeclName} (mem : (k, []) ∈ ctors) {m : Nat}
    (σ : Sub Head (s + 1 + d) m) (free : ∀ i, ConstFree f (σ i)) :
    ∃ r, S.R.computation.step
        (applyClosed (ofEntries e (s + 1 + d)) (replaceScrut s (appSpine (.const k) []) d σ) (.const f)) r ∧
      ConstFree f r := by
  refine ⟨_, decl.rule mem σ [] rfl, ?_⟩
  have hyp : ConstFree f (Presentation.subst (hypSub f e s d []) (body k [])) :=
    ConstFree.subst (body_free decl undeclared mem) (fun _ => trivial)
  exact ConstFree.subst hyp (matchSub_nullary_free d σ free)

end TowerSyntaxLimit

/-! ## In the typed-syntax package -/

namespace TowerSyntaxModel

open TowerSyntaxLimit

variable (lv : LevelExpr Nat)

/-- The family a naive declaration would define. -/
def expNaive : DeclName := .mkSimple "exp-naive"

/-- **The naive self-referential right-hand side** at `tnum`: `Σ (b : bool). bool-rec (λ _. U0) num
(Σ (D tnum) (D tnum)) b`, a literal or a pair of expressions at the same index. -/
def naiveBody {n : Nat} : Tm Tower.Head n :=
  .sigma boolC (boolRecC (.lam U0) numC
    (.sigma (.app (.const expNaive) tnumC) (.app (.const expNaive) tnumC)) (.var 0))

/-- **Control: the naive right-hand side is typed in no stage that does not declare the family**, at
any type and in any context, so no recursive family on the index alone has it as its unfolding. -/
theorem naive_not_typed {R₀ : Rules Tower.Head} (undeclared : R₀.constantType expNaive = none)
    {n : Nat} {Γ : Ctx Tower.Head n} {A : Tm Tower.Head n} : ¬ Typed R₀ Γ naiveBody A := by
  intro typing
  have free : ConstFree expNaive (naiveBody : Tm Tower.Head n) := typed_free undeclared typing
  obtain ⟨-, ⟨⟨-, ⟨⟨self, -⟩, -⟩⟩, -⟩⟩ := free
  exact self rfl

/-- The stage before the value type does not declare it. -/
theorem baseStage_val : (baseStage lv).constantType val = none := by
  change (if val ∈ baseNames then constantType lv val else none) = none
  exact if_neg (by decide)

/-- **Non-vacuity**: the package's value type is a recursive family on the object types, and at
`tnum` it steps to a term free of it. -/
theorem val_tnum_unfolds (valuation : Nat → Nat) {m : Nat} (σ : Sub Tower.Head (0 + 1 + 0) m)
    (free : ∀ i, ConstFree val (σ i)) :
    ∃ r, (setting lv valuation).R.computation.step
        (applyClosed (ofEntries tyEntries (0 + 1 + 0)) (replaceScrut 0 (appSpine (.const tnum) []) 0 σ)
          (.const val)) r ∧
      ConstFree val r :=
  nullary_unfolds (declaresVal lv valuation (laws lv valuation)) (baseStage_val lv) mem_tnum σ free

end TowerSyntaxModel

#print axioms TowerSyntaxLimit.free_of_undeclared
#print axioms TowerSyntaxLimit.typed_free
#print axioms TowerSyntaxLimit.body_free
#print axioms TowerSyntaxLimit.nullary_unfolds
#print axioms TowerSyntaxModel.naive_not_typed
#print axioms TowerSyntaxModel.val_tnum_unfolds

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
