import Mettapedia.Logic.HOL.ProofSyntaxStructural

/-!
# Distinct finite numerals from retained Peano laws

Constructor tags use finite successor numerals. Separation and injectivity
proofs, rather than a semantic assumption about the carrier, supply their
inequality. The proof builder works in any context and retains all premises.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.NaturalNumeralProofs

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {number : Ty Base}
  (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))

def separation : Formula Const Γ :=
  .all (.not (.eq (.app (weaken successor) (.var .vz)) (weaken zero)))

def injectivity : Formula Const Γ :=
  .all (.all (.eq
    (.eq (.app (weaken (weaken successor)) (.var (.vs .vz)))
      (.app (weaken (weaken successor)) (.var .vz)))
    (.eq (.var (.vs .vz)) (.var .vz))))

def numeral : Nat → Term Const Γ number
  | 0 => zero
  | n + 1 => .app successor (numeral n)

theorem subst_numeral (images : Subst Const Γ Ξ) (n : Nat) :
    subst images (numeral zero successor n) =
      numeral (subst images zero) (subst images successor) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [numeral, subst, ih]

variable {assumptions : List (Formula Const Γ)}

@[simp] private theorem single_weaken (value : Term Const Γ number)
    {type : Ty Base} (term : Term Const Γ type) :
    subst (Subst.single value) (weaken term) = term :=
  instantiate_weaken value term

def successorNeZero (value : Term Const Γ number)
    (law : ProofSyntax Const assumptions (separation zero successor)) :
    ProofSyntax Const assumptions (.not (.eq (.app successor value) zero)) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE value law)
  simp [instantiate, subst, Subst.single]

theorem successorNeZero_free (value : Term Const Γ number)
    (law : ProofSyntax Const assumptions (separation zero successor))
    (free : law.FunctionExtensionalityFree) :
    (successorNeZero zero successor value law).FunctionExtensionalityFree := by
  unfold successorNeZero
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact free

def successorEquality (first second : Term Const Γ number)
    (law : ProofSyntax Const assumptions (injectivity successor)) :
    ProofSyntax Const assumptions (.eq (.eq (.app successor first) (.app successor second))
      (.eq first second)) := by
  have outer := ProofSyntax.allE first law
  have inner : ProofSyntax Const assumptions (.all (.eq
      (.eq (.app (weaken successor) (weaken first)) (.app (weaken successor) (.var .vz)))
      (.eq (weaken first) (.var .vz)))) := by
    apply ProofSyntax.castIndices rfl ?_ outer
    simp [instantiate, subst, Subst.single, Subst.lift]
    rfl
  apply ProofSyntax.castIndices rfl ?_ (.allE second inner)
  simp [instantiate, subst, Subst.single]

theorem successorEquality_free (first second : Term Const Γ number)
    (law : ProofSyntax Const assumptions (injectivity successor))
    (free : law.FunctionExtensionalityFree) :
    (successorEquality successor first second law).FunctionExtensionalityFree := by
  unfold successorEquality
  repeat apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact free

def unequal
    (apart : ProofSyntax Const assumptions (separation zero successor))
    (cancel : ProofSyntax Const assumptions (injectivity successor)) :
    (first second : Nat) → first ≠ second →
      ProofSyntax Const assumptions (.not (.eq (numeral zero successor first) (numeral zero successor second)))
  | 0, 0, different => (different rfl).elim
  | first + 1, 0, _ => successorNeZero zero successor (numeral zero successor first) apart
  | 0, second + 1, _ =>
      .notI (.notE
        ((successorNeZero zero successor (numeral zero successor second) apart).prepend _)
        (.eqSymm (.hyp ⟨0, by simp⟩)))
  | first + 1, second + 1, different =>
      .notI (.notE
        ((unequal apart cancel first second (fun same => different (congrArg Nat.succ same))).prepend _)
        (.impE (.eqPropEL ((successorEquality successor (numeral zero successor first)
          (numeral zero successor second) cancel).prepend _)) (.hyp ⟨0, by simp⟩)))

theorem unequal_free
    (apart : ProofSyntax Const assumptions (separation zero successor))
    (cancel : ProofSyntax Const assumptions (injectivity successor))
    (apartFree : apart.FunctionExtensionalityFree) (cancelFree : cancel.FunctionExtensionalityFree) :
    ∀ (first second : Nat) (different : first ≠ second),
      (unequal zero successor apart cancel first second different).FunctionExtensionalityFree := by
  intro first
  induction first with
  | zero =>
      intro second different
      cases second with
      | zero => exact (different rfl).elim
      | succ second =>
          simp only [unequal, ProofSyntax.FunctionExtensionalityFree,
            ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono, and_true]
          exact successorNeZero_free zero successor _ apart apartFree
  | succ first ih =>
      intro second different
      cases second with
      | zero => exact successorNeZero_free zero successor _ apart apartFree
      | succ second =>
          simp only [unequal, ProofSyntax.FunctionExtensionalityFree,
            ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono, and_true]
          exact ⟨ih second _, successorEquality_free successor _ _ cancel cancelFree⟩

/-- Without separation, a constant successor has a retained equality proof
between the first two numerals. Closure alone does not establish distinctness. -/
def collapsedSuccessor : Term Const Γ (number ⇒ number) := .lam (weaken zero)

def collapsedNumerals : ProofSyntax Const assumptions
    (.eq (numeral zero (collapsedSuccessor zero) 1) (numeral zero (collapsedSuccessor zero) 0)) := by
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.beta zero (weaken zero))
  simp [numeral, collapsedSuccessor, instantiate]

theorem collapsedNumerals_free :
    (collapsedNumerals zero (assumptions := assumptions)).FunctionExtensionalityFree := by
  unfold collapsedNumerals
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

#print axioms successorNeZero_free
#print axioms successorEquality_free
#print axioms unequal_free
#print axioms collapsedNumerals
#print axioms collapsedNumerals_free

end Mettapedia.Logic.HOL.NaturalNumeralProofs
