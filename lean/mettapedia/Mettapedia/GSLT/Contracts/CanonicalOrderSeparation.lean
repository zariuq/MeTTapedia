import Mettapedia.GSLT.Contracts.CanonicalSuccessorClasses
import Mettapedia.Logic.LP.Substitution
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Prod.Lex

/-!
# Presentation orders and reduction orders have different laws

Parallel contents are a bag of already selected semantic keys. An
injective code into any linear order serializes that bag; a score with
ties is fine as a first coordinate if the last coordinate is faithful.
No stability under substitution is required of the serialization.

For rewriting, a decreasing relation must instead be well-founded
and preserved by the allowed instantiations and contexts. In
particular a strict substitution-stable relation cannot compare two
distinct unifiable terms. It cannot be a total order on all open terms.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.CanonicalOrderSeparation

open Mettapedia.GSLT.Contracts.CanonicalSuccessorClasses (NormalForms Modulo)

section Presentation

variable {Key Code Rank : Type*}

/-- Use a linear order on codes, not a globally installed order on
terms. Tied semantic ranks may be completed by a faithful code. -/
def word [LinearOrder Code] (code : Key → Code) (faithful : Function.Injective code)
    (bag : Multiset Key) : List Key := by
  let rel := fun a b => code a ≤ code b
  letI : DecidableRel rel := fun a b => inferInstanceAs (Decidable (code a ≤ code b))
  letI : IsTrans Key rel := ⟨fun _ _ _ first second => le_trans first second⟩
  let _ : Std.Antisymm rel := ⟨fun _ _ first second => faithful (le_antisymm first second)⟩
  letI : Std.Total rel := ⟨fun a b => le_total (code a) (code b)⟩
  exact bag.sort rel

theorem bag_of_word [LinearOrder Code] (code : Key → Code) (faithful : Function.Injective code)
    (bag : Multiset Key) : (word code faithful bag : Multiset Key) = bag := by
  simp only [word, Multiset.sort_eq]

theorem word_sorted [LinearOrder Code] (code : Key → Code) (faithful : Function.Injective code)
    (bag : Multiset Key) :
    (word code faithful bag).Pairwise (fun a b => code a ≤ code b) := by
  simp only [word, Multiset.pairwise_sort]

theorem word_eq_iff [LinearOrder Code] (code : Key → Code) (faithful : Function.Injective code)
    {left right : Multiset Key} :
    word code faithful left = word code faithful right ↔ left = right := by
  refine ⟨fun same => ?_, congrArg (word code faithful)⟩
  have bags := congrArg (fun list : List Key => (list : Multiset Key)) same
  simpa only [bag_of_word] using bags

theorem word_eq_of_sorted [LinearOrder Code] (code : Key → Code) (faithful : Function.Injective code)
    {bag : Multiset Key} {listed : List Key}
    (represents : (listed : Multiset Key) = bag)
    (sorted : listed.Pairwise (fun a b => code a ≤ code b)) :
    word code faithful bag = listed := by
  let rel : Key → Key → Prop := fun a b => code a ≤ code b
  let _ : Std.Antisymm rel := ⟨fun _ _ first second => faithful (le_antisymm first second)⟩
  have perm := Multiset.coe_eq_coe.mp ((bag_of_word code faithful bag).trans represents.symm)
  exact perm.eq_of_pairwise' (r := rel) (word_sorted code faithful bag) sorted

def rankedCode (rank : Key → Rank) (tie : Key → Code) (key : Key) : Rank ×ₗ Code :=
  toLex (rank key, tie key)

theorem rankedCode_injective (rank : Key → Rank) {tie : Key → Code}
    (faithful : Function.Injective tie) : Function.Injective (rankedCode rank tie) :=
  fun _ _ same => faithful (congrArg (fun key : Rank ×ₗ Code => (ofLex key).2) same)

/-- Reserialized results depend on the bag, not the previous sort.
The pointwise operation can identify entries and need not be
monotone for either presentation order. Multiplicities are retained. -/
theorem rescore_after_map {New NewCode : Type*} [LinearOrder Code] [LinearOrder NewCode]
    (first : Key → Code) (firstFaithful : Function.Injective first)
    (second : New → NewCode) (secondFaithful : Function.Injective second)
    (changeKey : Key → New) (bag : Multiset Key) :
    word second secondFaithful (((word first firstFaithful bag).map changeKey : List New) : Multiset New) =
      word second secondFaithful (bag.map changeKey) := by
  congr 1
  have mapped := congrArg (Multiset.map changeKey) (bag_of_word first firstFaithful bag)
  exact mapped

/-- Skipping the resort is valid uniformly precisely when the map
preserves the selected comparison. Testing bags of two entries
already detects every failure of that fast path. -/
theorem map_preserves_word_iff {New NewCode : Type*} [LinearOrder Code] [LinearOrder NewCode]
    (first : Key → Code) (firstFaithful : Function.Injective first)
    (second : New → NewCode) (secondFaithful : Function.Injective second)
    (changeKey : Key → New) :
    (∀ bag : Multiset Key, (word first firstFaithful bag).map changeKey =
      word second secondFaithful (bag.map changeKey)) ↔
      ∀ a b, first a ≤ first b → second (changeKey a) ≤ second (changeKey b) := by
  constructor
  · intro skipsSort a b ordered
    let pair : Multiset Key := ([a, b] : List Key)
    have firstPair : word first firstFaithful pair = [a, b] :=
      word_eq_of_sorted first firstFaithful rfl (List.pairwise_pair.mpr ordered)
    have after := word_sorted second secondFaithful (pair.map changeKey)
    rw [← skipsSort pair, firstPair] at after
    exact (List.pairwise_pair (R := fun x y => second x ≤ second y)).mp after
  · intro monotone bag
    apply (word_eq_of_sorted second secondFaithful ?_ ?_).symm
    · exact congrArg (Multiset.map changeKey) (bag_of_word first firstFaithful bag)
    · exact List.Pairwise.map changeKey monotone (word_sorted first firstFaithful bag)

end Presentation

section Substitution

variable {Term Inst : Type*}

def Stable (act : Inst → Term → Term) (relation : Term → Term → Prop) : Prop :=
  ∀ inst {left right}, relation left right → relation (act inst left) (act inst right)

/-- This is the normal-form law useful across a substitution boundary.
The equation relation survives substitution; the order of the
serialized children does not have to survive it. -/
theorem normalize_after_act_iff {equations : Setoid Term} (forms : NormalForms equations)
    (act : Inst → Term → Term) :
    (∀ inst t, forms.normal (act inst (forms.normal t)) = forms.normal (act inst t)) ↔
      Stable act equations.r := by
  constructor
  · intro commutes inst first second same
    have equal : forms.normal (act inst first) = forms.normal (act inst second) := by
      rw [← commutes inst first, ← commutes inst second, forms.same same]
    exact forms.key_eq_iff.mp (Subtype.ext equal)
  · intro stable inst t
    exact forms.same (stable inst (forms.sound t))

theorem incomparable_if_equal_instance (act : Inst → Term → Term) (relation : Term → Term → Prop)
    (stable : Stable act relation) (irrefl : ∀ term, ¬ relation term term)
    {left right : Term} (inst : Inst) (same : act inst left = act inst right) :
    ¬ relation left right ∧ ¬ relation right left :=
  ⟨fun before => irrefl _ (same ▸ stable inst before),
    fun after => irrefl _ (same ▸ stable inst after)⟩

/-- Using a non-strict comparison does not make a substitution-stable
linear order possible when a renaming can exchange two open terms. -/
theorem no_antisymmetric_total_stable_order_on_swapped_terms
    (act : Inst → Term → Term) (relation : Term → Term → Prop)
    (stable : Stable act relation)
    (antisymmetric : ∀ ⦃a b⦄, relation a b → relation b a → a = b)
    {a b : Term} (different : a ≠ b)
    (inst : Inst) (first : act inst a = b) (second : act inst b = a) :
    ¬ (relation a b ∨ relation b a) := by
  rintro (ab | ba)
  · have opposite := stable inst ab
    rw [first, second] at opposite
    exact different (antisymmetric ab opposite)
  · have opposite := stable inst ba
    rw [first, second] at opposite
    exact different (antisymmetric opposite ba)

open Mettapedia.Logic in
/-- The strict variable condition is not specific to one ordering:
totality on open first-order terms is impossible for any stable
strict order as soon as two variables can be identified. -/
theorem no_total_stable_open_order {σ : LP.LPSignature} (x y : σ.vars) (distinct : x ≠ y)
    (relation : LP.Term σ → LP.Term σ → Prop)
    (stable : Stable (fun inst : LP.Subst σ => inst.applyTerm) relation)
    (irrefl : ∀ t, ¬ relation t t) :
    ¬ ∀ a b, a ≠ b → relation a b ∨ relation b a := by
  intro totalExceptEqual
  have separate : (LP.Term.var x : LP.Term σ) ≠ LP.Term.var y := fun same =>
    distinct (LP.Term.var.inj same)
  have incomparable := incomparable_if_equal_instance (fun inst : LP.Subst σ => inst.applyTerm)
    relation stable irrefl (left := LP.Term.var x) (right := LP.Term.var y)
    (fun _ => LP.Term.var x) rfl
  exact (totalExceptEqual _ _ separate).elim incomparable.1 incomparable.2

end Substitution

/-! ## An orientation contract independent of a particular ordering -/

section Orientation

variable {Term Inst Frame : Type*}

inductive ContextualInstance (rules : Term → Term → Prop) (act : Inst → Term → Term)
    (plug : Frame → Term → Term) : Term → Term → Prop where
  | step {lhs rhs : Term} (declared : rules lhs rhs) (inst : Inst) (frame : Frame) :
      ContextualInstance rules act plug (plug frame (act inst lhs)) (plug frame (act inst rhs))

/-- The backend can use any certified decreasing relation. This
licenses termination of the oriented equations, not confluence or
coherence of the separate transition rules. -/
theorem oriented_rules_terminate (rules rel : Term → Term → Prop)
    (act : Inst → Term → Term) (plug : Frame → Term → Term)
    (founded : WellFounded rel) (substitution : Stable act rel)
    (context : ∀ frame {a b}, rel a b → rel (plug frame a) (plug frame b))
    (orients : ∀ {lhs rhs}, rules lhs rhs → rel rhs lhs) :
    WellFounded (fun tgt src => ContextualInstance rules act plug src tgt) := by
  apply Subrelation.wf _ founded
  intro tgt src edge
  cases edge with
  | step declared inst frame => exact context frame (substitution inst (orients declared))

end Orientation

/-- For rewriting modulo equations, compare equation keys. The
representative changes at the two ends cannot repair a failure to
decrease in this order. -/
theorem modulo_terminates_from_key_order {Term : Type*} {equations : Setoid Term}
    (forms : NormalForms equations) (raw : Term → Term → Type*)
    {less : forms.Key → forms.Key → Prop} (founded : WellFounded less)
    (decreases : ∀ {source target}, Nonempty (raw source target) →
      less (forms.key target) (forms.key source)) :
    WellFounded (fun target source => Modulo (equations := equations) raw source target) := by
  apply Subrelation.wf _ (InvImage.wf forms.key founded)
  rintro target source ⟨witness⟩
  change less (forms.key target) (forms.key source)
  rw [← forms.key_eq_iff.mpr witness.targetEquation, forms.key_eq_iff.mpr witness.sourceEquation]
  exact decreases ⟨witness.receipt⟩

namespace Controls

/-- A partial comparison can be well-behaved while an ad-hoc fallback
on its incomparable pairs creates a cycle. -/
private def partialRank (left right : Nat) : Bool := left == 2 && right == 0

private def fallback (left right : Nat) : Bool :=
  if partialRank left right then true
  else if partialRank right left then false else decide (left < right)

theorem pairwise_fallback_can_cycle :
    (∀ {a b c : Nat}, partialRank a b = true → partialRank b c = true → partialRank a c = true) ∧
      fallback 2 0 = true ∧ fallback 0 1 = true ∧ fallback 1 2 = true ∧ fallback 0 2 = false := by
  refine ⟨?_, by decide⟩
  intro a b c ab bc
  simp [partialRank] at ab bc
  omega

private abbrev reverseCode := OrderDual Nat
private def reversed (n : Nat) : reverseCode := n
private theorem reversed_injective : Function.Injective reversed := fun _ _ same => same

theorem different_order_same_bag :
    let bag : Multiset Nat := ([1, 2, 1] : List Nat)
    word id Function.injective_id bag = [1, 1, 2] ∧
      word reversed reversed_injective bag = [2, 1, 1] := by
  dsimp only
  constructor
  · exact word_eq_of_sorted id Function.injective_id (by decide) (by decide)
  · exact word_eq_of_sorted reversed reversed_injective (by decide) (by decide)

end Controls

#print axioms word_eq_iff
#print axioms rescore_after_map
#print axioms map_preserves_word_iff
#print axioms normalize_after_act_iff
#print axioms no_total_stable_open_order
#print axioms no_antisymmetric_total_stable_order_on_swapped_terms
#print axioms oriented_rules_terminate
#print axioms modulo_terminates_from_key_order
#print axioms Controls.pairwise_fallback_can_cycle
#print axioms Controls.different_order_same_bag

end Mettapedia.GSLT.Contracts.CanonicalOrderSeparation
