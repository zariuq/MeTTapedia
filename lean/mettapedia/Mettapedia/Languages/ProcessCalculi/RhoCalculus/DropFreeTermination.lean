import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReflectiveReplication
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MultiStep

/-!
# Drop is essential for replication: bounded reduction without active drops

This is the negative control for `ReflectiveReplication`.  There, the code
`D(x) | P` represents the diagonal composite of `X ↦ X | P`, so replication is
a fixed point and runs forever.  Here, a fragment of the canonical Lean rho
that contains every drop-free pattern is shown to have **no** infinite
reduction sequence, and no fixed point of `X ↦ X | P` up to reduction when `P`
has an active prefix.  By the contrapositive of the diagonal step, no code of
the fragment represents that diagonal composite: without drop, a received code
can only be compared as a channel, never run.

**Measures.**  A pattern is read at a depth `d`.  The argument of a quote sits
two levels deeper, the payload of an output one level deeper (communication
will quote it), and the argument of a drop two levels shallower (when the
drop sits at depth at least 2).  Every other position keeps the depth.  With
these rules:

* `activity d p` counts output and input prefixes at depth 0;
* `unguarded d p` counts drops at depth below 2.

Both are invariant under structural congruence, including `@(*n) ≡ n`
(`activity_sc`, `unguarded_sc`), because a quote-drop pair shifts depth by
`+2 - 2`.

**The fragment.**  `CodeInert p` holds when `p` has no unguarded drop at any
depth, and no activity at any depth `≥ 1`: quoted code and payloads stay
inert.  Every drop-free pattern is code-inert (`codeInert_of_dropFree`), and
the fragment is closed under structural congruence (`codeInert_of_sc`).

**Substitution** (`substProc_weights`).  Communication substitutes the quote
of the normalised payload.  Into a pattern without unguarded drops, a quote of
a payload inert at every depth `≥ 2` adds no activity and no unguarded drop:
every collapsing drop sits at depth `≥ 2`, where the payload is inert.

**Main theorem** (`reduces_codeInert`), for the canonical relation `Reduces`
(COMM, closed under structural congruence and parallel contexts) on all
patterns.  A reduction step of a code-inert pattern stays code-inert and
lowers `activity 0` by at least two.  Hence:

* `reducesN_codeInert`, `reducesN_length_le`: `n` steps from `P` need
  `2 * n ≤ activity 0 P`;
* `no_infinite_reduction`: no infinite reduction sequence starts in the
  fragment;
* `not_reduces_beside`, `not_reduces_to_beside`: no code-inert `X` reduces, in
  any positive number of steps, to a term congruent to `X | P` when `P` has an
  active prefix;
* `not_represents_of_codeInert`: the contrapositive of the diagonal step; no
  code-inert code represents the diagonal composite that the duplicator
  represents;
* `replicate_not_codeInert`, `drop_is_essential`: the reflective replicator
  lies outside the fragment, in contrast with `replicate_unfold`;
* controls: `ping` is drop-free, communicates once, and has activity 2
  (`ping_reduces`, `ping_activity`), so the fragment contains genuine
  reductions; `replicate_sendZero_contrast` is the concrete instance.

The payload position sits one level deeper than its output, and a quote two:
this offset is what keeps a substituted payload, which lands inside a quote,
inert while the payload itself is counted once, at its output.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.DropFreeTermination

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReflectiveReplication

/-! ## Depth-indexed measures -/

/-- The depth of argument `i` of a constructor `f` read at depth `d`. -/
def argDepth (f : String) (d i : Nat) : Nat :=
  if f = "NQuote" then d + 2
  else if f = "PDrop" then (if 2 ≤ d then d - 2 else d)
  else if f = "POutput" then (if i = 1 then d + 1 else d)
  else d

mutual
/-- The sum of a node weight over a pattern read at depth `d`. -/
def weight (node : String → Nat → Nat) : Nat → Pattern → Nat
  | _, .bvar _ => 0
  | _, .fvar _ => 0
  | d, .apply f args => node f d + weightArgs node f d 0 args
  | d, .lambda _ body => weight node d body
  | d, .multiLambda _ _ body => weight node d body
  | d, .subst body repl => weight node d body + weight node d repl
  | d, .collection _ elems _ => weightList node d elems

/-- The weight of the arguments of `f`, from position `i` on. -/
def weightArgs (node : String → Nat → Nat) : String → Nat → Nat → List Pattern → Nat
  | _, _, _, [] => 0
  | f, d, i, p :: ps => weight node (argDepth f d i) p + weightArgs node f d (i + 1) ps

/-- The weight of the elements of a collection, all at depth `d`. -/
def weightList (node : String → Nat → Nat) : Nat → List Pattern → Nat
  | _, [] => 0
  | d, p :: ps => weight node d p + weightList node d ps
end

/-- Communication prefixes at depth 0. -/
def activityNode (f : String) (d : Nat) : Nat :=
  if f = "POutput" ∨ f = "PInput" then (if d = 0 then 1 else 0) else 0

/-- Drops at depth below 2. -/
def dropNode (f : String) (d : Nat) : Nat :=
  if f = "PDrop" then (if d < 2 then 1 else 0) else 0

/-- **Activity**: output and input prefixes at depth 0. -/
abbrev activity : Nat → Pattern → Nat := weight activityNode

/-- **Unguarded drops**: drops at depth below 2. -/
abbrev unguarded : Nat → Pattern → Nat := weight dropNode

/-! Internal lemmas are stated for `weight activityNode` and `weight dropNode`,
which `activity` and `unguarded` abbreviate.  Constructor names are compared
by deciding string equality, never by a classical case split. -/

/-! ### Computation rules -/

section Rules

variable (node : String → Nat → Nat)

theorem activityNode_output (d : Nat) : activityNode "POutput" d = if d = 0 then 1 else 0 :=
  if_pos (Or.inl rfl)

theorem activityNode_input (d : Nat) : activityNode "PInput" d = if d = 0 then 1 else 0 :=
  if_pos (Or.inr rfl)

theorem activityNode_other {f : String} (notPrefix : ¬ (f = "POutput" ∨ f = "PInput"))
    (d : Nat) : activityNode f d = 0 :=
  if_neg notPrefix

theorem activityNode_deep (f : String) {d : Nat} (deep : 1 ≤ d) : activityNode f d = 0 := by
  unfold activityNode
  rw [if_neg (show ¬ d = 0 by omega)]
  split_ifs <;> rfl

theorem activityNode_output_top : activityNode "POutput" 0 = 1 := by
  rw [activityNode_output, if_pos rfl]

theorem activityNode_input_top : activityNode "PInput" 0 = 1 := by
  rw [activityNode_input, if_pos rfl]

theorem dropNode_drop (d : Nat) : dropNode "PDrop" d = if d < 2 then 1 else 0 :=
  if_pos rfl

theorem dropNode_other {f : String} (notDrop : f ≠ "PDrop") (d : Nat) : dropNode f d = 0 :=
  if_neg notDrop

theorem argDepth_NQuote (d i : Nat) : argDepth "NQuote" d i = d + 2 :=
  if_pos rfl

theorem argDepth_PDrop (d i : Nat) :
    argDepth "PDrop" d i = if 2 ≤ d then d - 2 else d := by
  unfold argDepth
  rw [if_neg (show ¬ ("PDrop" = "NQuote") by decide), if_pos rfl]

theorem argDepth_POutput_zero (d : Nat) : argDepth "POutput" d 0 = d := by
  unfold argDepth
  rw [if_neg (show ¬ ("POutput" = "NQuote") by decide),
    if_neg (show ¬ ("POutput" = "PDrop") by decide), if_pos rfl,
    if_neg (show ¬ ((0 : Nat) = 1) by decide)]

theorem argDepth_POutput_one (d : Nat) : argDepth "POutput" d 1 = d + 1 := by
  unfold argDepth
  rw [if_neg (show ¬ ("POutput" = "NQuote") by decide),
    if_neg (show ¬ ("POutput" = "PDrop") by decide), if_pos rfl, if_pos rfl]

theorem argDepth_PInput (d i : Nat) : argDepth "PInput" d i = d := by
  unfold argDepth
  rw [if_neg (show ¬ ("PInput" = "NQuote") by decide),
    if_neg (show ¬ ("PInput" = "PDrop") by decide),
    if_neg (show ¬ ("PInput" = "POutput") by decide)]

theorem weightList_append (d : Nat) (first second : List Pattern) :
    weightList node d (first ++ second) = weightList node d first + weightList node d second := by
  induction first with
  | nil => simp [weightList]
  | cons p ps ih =>
      simp only [List.cons_append, weightList, ih]
      omega

theorem weightList_eq_sum (d : Nat) (elems : List Pattern) :
    weightList node d elems = (elems.map (weight node d)).sum := by
  induction elems with
  | nil => simp [weightList]
  | cons p ps ih => simp [weightList, ih]

theorem weight_mem_le {d : Nat} {elems : List Pattern} {p : Pattern} (member : p ∈ elems) :
    weight node d p ≤ weightList node d elems := by
  induction elems with
  | nil => simp at member
  | cons head tail ih =>
      simp only [weightList]
      rcases List.mem_cons.mp member with rfl | inTail
      · omega
      · have := ih inTail
        omega

end Rules

/-! ## Invariance under structural congruence -/

/-- The node weights that a quote-drop pair and the empty process do not
see: quotes and `0` weigh nothing, and a drop weighs nothing at depth `≥ 2`. -/
structure NodeLaws (node : String → Nat → Nat) : Prop where
  quote : ∀ d, node "NQuote" d = 0
  zero : ∀ d, node "PZero" d = 0
  guardedDrop : ∀ d, node "PDrop" (d + 2) = 0

theorem activityNode_laws : NodeLaws activityNode :=
  ⟨fun d => activityNode_other (by decide) d, fun d => activityNode_other (by decide) d,
    fun d => activityNode_other (by decide) (d + 2)⟩

theorem dropNode_laws : NodeLaws dropNode :=
  ⟨fun d => dropNode_other (by decide) d, fun d => dropNode_other (by decide) d,
    fun d => by rw [dropNode_drop, if_neg (by omega)]⟩

section Invariance

variable {node : String → Nat → Nat}

private theorem weightList_of_pointwise {ps qs : List Pattern} (length : ps.length = qs.length)
    (pointwise : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      ∀ d, weight node d (ps.get ⟨i, h₁⟩) = weight node d (qs.get ⟨i, h₂⟩)) (d : Nat) :
    weightList node d ps = weightList node d qs := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil => rfl
      | cons _ _ => exact (Nat.succ_ne_zero _ length.symm).elim
  | cons p ps ih =>
      cases qs with
      | nil => exact (Nat.succ_ne_zero _ length).elim
      | cons q qs =>
          have head : weight node d p = weight node d q :=
            pointwise 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) d
          have tail : weightList node d ps = weightList node d qs :=
            ih (Nat.succ.inj length) fun i h₁ h₂ =>
              pointwise (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          show weight node d p + weightList node d ps = weight node d q + weightList node d qs
          rw [head, tail]

private theorem weightArgs_of_pointwise (f : String) {ps qs : List Pattern}
    (length : ps.length = qs.length)
    (pointwise : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      ∀ d, weight node d (ps.get ⟨i, h₁⟩) = weight node d (qs.get ⟨i, h₂⟩)) (d i : Nat) :
    weightArgs node f d i ps = weightArgs node f d i qs := by
  induction ps generalizing qs i with
  | nil =>
      cases qs with
      | nil => rfl
      | cons _ _ => exact (Nat.succ_ne_zero _ length.symm).elim
  | cons p ps ih =>
      cases qs with
      | nil => exact (Nat.succ_ne_zero _ length).elim
      | cons q qs =>
          have head : weight node (argDepth f d i) p = weight node (argDepth f d i) q :=
            pointwise 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (argDepth f d i)
          have tail : weightArgs node f d (i + 1) ps = weightArgs node f d (i + 1) qs :=
            ih (Nat.succ.inj length) (fun j h₁ h₂ =>
              pointwise (j + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)) (i + 1)
          show weight node (argDepth f d i) p + weightArgs node f d (i + 1) ps =
            weight node (argDepth f d i) q + weightArgs node f d (i + 1) qs
          rw [head, tail]

/-- **Structural congruence preserves every weight obeying the node laws**, at
every depth. -/
theorem weight_sc (laws : NodeLaws node) {left right : Pattern} (congruent : left ≡ right) :
    ∀ d, weight node d left = weight node d right := by
  induction congruent with
  | alpha _ _ equal => subst equal; intro d; rfl
  | refl _ => intro d; rfl
  | symm _ _ _ ih => intro d; exact (ih d).symm
  | trans _ _ _ _ _ first second => intro d; exact (first d).trans (second d)
  | par_singleton p => intro d; simp only [weight, weightList, Nat.add_zero]
  | par_nil_left p =>
      intro d
      simp only [weight, weightList, weightArgs, laws.zero, Nat.add_zero, Nat.zero_add]
  | par_nil_right p =>
      intro d
      simp only [weight, weightList, weightArgs, laws.zero, Nat.add_zero]
  | par_comm p q => intro d; simp only [weight, weightList]; omega
  | par_assoc p q r => intro d; simp only [weight, weightList]; omega
  | par_cong ps qs length _ ih =>
      intro d
      simp only [weight]
      exact weightList_of_pointwise length ih d
  | par_flatten ps qs =>
      intro d
      simp only [weight, weightList_append, weightList]
      omega
  | par_perm _ _ perm =>
      intro d
      simp only [weight, weightList_eq_sum]
      exact (perm.map _).sum_eq
  | set_perm _ _ perm =>
      intro d
      simp only [weight, weightList_eq_sum]
      exact (perm.map _).sum_eq
  | set_cong _ _ length _ ih =>
      intro d
      simp only [weight]
      exact weightList_of_pointwise length ih d
  | lambda_cong _ _ _ _ ih => intro d; simp only [weight]; exact ih d
  | apply_cong f _ _ length _ ih =>
      intro d
      simp only [weight]
      rw [weightArgs_of_pointwise f length ih d 0]
  | collection_general_cong _ _ _ _ length _ ih =>
      intro d
      simp only [weight]
      exact weightList_of_pointwise length ih d
  | multiLambda_cong _ _ _ _ _ ih => intro d; simp only [weight]; exact ih d
  | subst_cong _ _ _ _ _ _ ih₁ ih₂ => intro d; simp only [weight]; rw [ih₁ d, ih₂ d]
  | quote_drop n =>
      intro d
      simp only [weight, weightArgs, argDepth_NQuote, argDepth_PDrop, laws.quote,
        laws.guardedDrop, if_pos (show 2 ≤ d + 2 by omega), Nat.add_sub_cancel, Nat.add_zero,
        Nat.zero_add]
  | par_empty => intro d; simp only [weight, weightList, weightArgs, laws.zero]

end Invariance

theorem activity_sc {left right : Pattern} (congruent : left ≡ right) (d : Nat) :
    activity d left = activity d right :=
  weight_sc activityNode_laws congruent d

theorem unguarded_sc {left right : Pattern} (congruent : left ≡ right) (d : Nat) :
    unguarded d left = unguarded d right :=
  weight_sc dropNode_laws congruent d

/-- Normalisation is structural congruence, so it keeps both measures. -/
theorem activity_normalizeProc (q : Pattern) (d : Nat) :
    weight activityNode d (semanticNormalizeProc q) = weight activityNode d q :=
  weight_sc activityNode_laws (normalizeProc_sc q) d

theorem unguarded_normalizeProc (q : Pattern) (d : Nat) :
    weight dropNode d (semanticNormalizeProc q) = weight dropNode d q :=
  weight_sc dropNode_laws (normalizeProc_sc q) d

theorem activity_normalizeName (n : Pattern) (d : Nat) :
    weight activityNode d (semanticNormalizeName n) = weight activityNode d n :=
  weight_sc activityNode_laws (normalizeName_sc n) d

theorem unguarded_normalizeName (n : Pattern) (d : Nat) :
    weight dropNode d (semanticNormalizeName n) = weight dropNode d n :=
  weight_sc dropNode_laws (normalizeName_sc n) d

/-! ## The fragment -/

/-- **Code-inert patterns**: no unguarded drop at any depth, and no activity
at any depth `≥ 1`. -/
def CodeInert (p : Pattern) : Prop :=
  (∀ d, weight dropNode d p = 0) ∧ (∀ d, 1 ≤ d → weight activityNode d p = 0)

/-- The fragment is closed under structural congruence. -/
theorem codeInert_of_sc {left right : Pattern} (congruent : left ≡ right)
    (inert : CodeInert left) : CodeInert right :=
  ⟨fun d => by rw [← weight_sc dropNode_laws congruent d]; exact inert.1 d,
    fun d deep => by rw [← weight_sc activityNode_laws congruent d]; exact inert.2 d deep⟩

mutual
/-- Whether a pattern contains a drop anywhere. -/
def hasDrop : Pattern → Bool
  | .bvar _ => false
  | .fvar _ => false
  | .apply f args => f == "PDrop" || hasDropList args
  | .lambda _ body => hasDrop body
  | .multiLambda _ _ body => hasDrop body
  | .subst body repl => hasDrop body || hasDrop repl
  | .collection _ elems _ => hasDropList elems

/-- Whether some element of a list contains a drop. -/
def hasDropList : List Pattern → Bool
  | [] => false
  | p :: ps => hasDrop p || hasDropList ps
end

/-- Away from drops, arguments are read at least as deep as their node. -/
theorem le_argDepth {f : String} (notDrop : f ≠ "PDrop") (d i : Nat) : d ≤ argDepth f d i := by
  unfold argDepth
  split_ifs <;> omega

mutual
/-- A drop-free pattern has no unguarded drop, at any depth. -/
theorem unguarded_of_dropFree : ∀ (p : Pattern), hasDrop p = false →
    ∀ d, weight dropNode d p = 0
  | .bvar _, _, _ => rfl
  | .fvar _, _, _ => rfl
  | .apply f args, free, d => by
      simp only [hasDrop, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at free
      simp only [weight]
      rw [dropNode_other free.1 d]
      simpa using unguardedArgs_of_dropFree args free.2 f d 0
  | .lambda _ body, free, d => by
      simp only [hasDrop] at free
      simpa [weight] using unguarded_of_dropFree body free d
  | .multiLambda _ _ body, free, d => by
      simp only [hasDrop] at free
      simpa [weight] using unguarded_of_dropFree body free d
  | .subst body repl, free, d => by
      simp only [hasDrop, Bool.or_eq_false_iff] at free
      simp only [weight]
      rw [unguarded_of_dropFree body free.1 d, unguarded_of_dropFree repl free.2 d]
  | .collection _ elems _, free, d => by
      simp only [hasDrop] at free
      simpa [weight] using unguardedList_of_dropFree elems free d

theorem unguardedArgs_of_dropFree : ∀ (args : List Pattern), hasDropList args = false →
    ∀ f d i, weightArgs dropNode f d i args = 0
  | [], _, _, _, _ => rfl
  | p :: ps, free, f, d, i => by
      simp only [hasDropList, Bool.or_eq_false_iff] at free
      simp only [weightArgs]
      rw [unguarded_of_dropFree p free.1, unguardedArgs_of_dropFree ps free.2]

theorem unguardedList_of_dropFree : ∀ (elems : List Pattern), hasDropList elems = false →
    ∀ d, weightList dropNode d elems = 0
  | [], _, _ => rfl
  | p :: ps, free, d => by
      simp only [hasDropList, Bool.or_eq_false_iff] at free
      simp only [weightList]
      rw [unguarded_of_dropFree p free.1, unguardedList_of_dropFree ps free.2]
end

mutual
/-- A drop-free pattern has no activity at any depth `≥ 1`: depths only grow
away from drops. -/
theorem activity_of_dropFree : ∀ (p : Pattern), hasDrop p = false →
    ∀ d, 1 ≤ d → weight activityNode d p = 0
  | .bvar _, _, _, _ => rfl
  | .fvar _, _, _, _ => rfl
  | .apply f args, free, d, deep => by
      simp only [hasDrop, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at free
      simp only [weight]
      rw [activityNode_deep f deep]
      simpa using activityArgs_of_dropFree args free.2 f free.1 d deep 0
  | .lambda _ body, free, d, deep => by
      simp only [hasDrop] at free
      simpa [weight] using activity_of_dropFree body free d deep
  | .multiLambda _ _ body, free, d, deep => by
      simp only [hasDrop] at free
      simpa [weight] using activity_of_dropFree body free d deep
  | .subst body repl, free, d, deep => by
      simp only [hasDrop, Bool.or_eq_false_iff] at free
      simp only [weight]
      rw [activity_of_dropFree body free.1 d deep, activity_of_dropFree repl free.2 d deep]
  | .collection _ elems _, free, d, deep => by
      simp only [hasDrop] at free
      simpa [weight] using activityList_of_dropFree elems free d deep

theorem activityArgs_of_dropFree : ∀ (args : List Pattern), hasDropList args = false →
    ∀ f, f ≠ "PDrop" → ∀ d, 1 ≤ d → ∀ i, weightArgs activityNode f d i args = 0
  | [], _, _, _, _, _, _ => rfl
  | p :: ps, free, f, notDrop, d, deep, i => by
      simp only [hasDropList, Bool.or_eq_false_iff] at free
      simp only [weightArgs]
      rw [activity_of_dropFree p free.1 _ (le_trans deep (le_argDepth notDrop d i)),
        activityArgs_of_dropFree ps free.2 f notDrop d deep]

theorem activityList_of_dropFree : ∀ (elems : List Pattern), hasDropList elems = false →
    ∀ d, 1 ≤ d → weightList activityNode d elems = 0
  | [], _, _, _ => rfl
  | p :: ps, free, d, deep => by
      simp only [hasDropList, Bool.or_eq_false_iff] at free
      simp only [weightList]
      rw [activity_of_dropFree p free.1 d deep, activityList_of_dropFree ps free.2 d deep]
end

/-- **Every drop-free pattern is code-inert.** -/
theorem codeInert_of_dropFree {p : Pattern} (free : hasDrop p = false) : CodeInert p :=
  ⟨unguarded_of_dropFree p free, activity_of_dropFree p free⟩


/-! ## Substitution keeps quoted code inert -/

/-- A name substitution with an inert replacement adds no weight. -/
theorem substName_weight_le {node : String → Nat → Nat} (laws : NodeLaws node) {k : Nat}
    {replacement : Pattern} (inertReplacement : ∀ d, weight node d replacement = 0)
    (name : Pattern) (d : Nat) :
    weight node d (semanticSubstName k replacement name) ≤ weight node d name := by
  rw [substName_eq]
  split_ifs
  · rw [inertReplacement d]
    exact Nat.zero_le _
  · rw [weight_sc laws (normalizeName_sc name) d]

/-- The weight of a quote. -/
theorem weight_quote {node : String → Nat → Nat} (laws : NodeLaws node) (d : Nat) (q : Pattern) :
    weight node d (.apply "NQuote" [q]) = weight node (d + 2) q := by
  simp only [weight, weightArgs, argDepth_NQuote, laws.quote, Nat.add_zero, Nat.zero_add]

/-- The weight of a drop. -/
theorem weight_drop (node : String → Nat → Nat) (d : Nat) (name : Pattern) :
    weight node d (.apply "PDrop" [name]) =
      node "PDrop" d + weight node (if 2 ≤ d then d - 2 else d) name := by
  simp only [weight, weightArgs, argDepth_PDrop, Nat.add_zero]

/-- The weight of an output: its payload one level deeper. -/
theorem weight_output (node : String → Nat → Nat) (d : Nat) (channel payload : Pattern) :
    weight node d (.apply "POutput" [channel, payload]) =
      node "POutput" d + weight node d channel + weight node (d + 1) payload := by
  simp only [weight, weightArgs, Nat.zero_add, argDepth_POutput_zero, argDepth_POutput_one,
    Nat.add_zero]
  omega

/-- The weight of an input with a binder. -/
theorem weight_input (node : String → Nat → Nat) (d : Nat) (channel body : Pattern) :
    weight node d (.apply "PInput" [channel, .lambda none body]) =
      node "PInput" d + weight node d channel + weight node d body := by
  simp only [weight, weightArgs, argDepth_PInput, Nat.add_zero]
  omega

/-- **Substitution lemma.**  Substituting the quote of a payload that is inert
at every depth `≥ 2` into a pattern without unguarded drops adds no activity
and creates no unguarded drop. -/
theorem substProc_weights {q : Pattern}
    (inertPayload : ∀ e, 2 ≤ e → weight activityNode e q = 0 ∧ weight dropNode e q = 0) :
    ∀ k body d, weight dropNode d body = 0 →
      weight activityNode d (semanticSubstProc k (.apply "NQuote" [q]) body) ≤
          weight activityNode d body ∧
        weight dropNode d (semanticSubstProc k (.apply "NQuote" [q]) body) = 0 := by
  have quoteActivity : ∀ d, weight activityNode d (.apply "NQuote" [q]) = 0 := fun d => by
    rw [weight_quote activityNode_laws]
    exact (inertPayload (d + 2) (by omega)).1
  have quoteDrops : ∀ d, weight dropNode d (.apply "NQuote" [q]) = 0 := fun d => by
    rw [weight_quote dropNode_laws]
    exact (inertPayload (d + 2) (by omega)).2
  intro k body
  refine semanticSubstProc.induct (.apply "NQuote" [q])
    (fun k body => ∀ d, weight dropNode d body = 0 →
      weight activityNode d (semanticSubstProc k (.apply "NQuote" [q]) body) ≤
          weight activityNode d body ∧
        weight dropNode d (semanticSubstProc k (.apply "NQuote" [q]) body) = 0)
    (fun k elems => ∀ d, weightList dropNode d elems = 0 →
      weightList activityNode d (semanticSubstProcList k (.apply "NQuote" [q]) elems) ≤
          weightList activityNode d elems ∧
        weightList dropNode d (semanticSubstProcList k (.apply "NQuote" [q]) elems) = 0)
    ?bvarHit ?bvarMiss ?fvar ?quote ?dropFires ?dropStays ?output ?input ?lambda ?multiLambda
    ?subst ?collection ?other ?nil ?cons k body
  case bvarHit =>
    intro k n hit d _
    rw [semanticSubstProc.eq_1, if_pos hit]
    exact ⟨by rw [quoteActivity d]; exact Nat.zero_le _, quoteDrops d⟩
  case bvarMiss =>
    intro k n miss d drops
    rw [semanticSubstProc.eq_1, if_neg miss]
    exact ⟨le_refl _, drops⟩
  case fvar =>
    intro k x d drops
    rw [semanticSubstProc.eq_2]
    exact ⟨le_refl _, drops⟩
  case quote =>
    intro k p d drops
    rw [semanticSubstProc.eq_3]
    exact ⟨le_refl _, drops⟩
  case dropFires =>
    intro k name p fired d drops
    rw [semanticSubstProc.eq_4, fired]
    simp only
    have isReplacement := substNameMark_eq k (.apply "NQuote" [q]) name
    rw [fired] at isReplacement
    split_ifs at isReplacement with hit
    · -- the collapse sits at depth at least two, where the payload is inert
      have sameQuote : Pattern.apply "NQuote" [p] = .apply "NQuote" [q] :=
        (Prod.mk.inj isReplacement).1
      have samePayload : p = q := by
        injection sameQuote with _ args
        injection args
      subst samePayload
      rw [weight_drop] at drops
      have deep : 2 ≤ d := by
        by_contra shallow
        rw [dropNode_drop, if_pos (show d < 2 by omega)] at drops
        omega
      exact ⟨by rw [(inertPayload d deep).1]; exact Nat.zero_le _, (inertPayload d deep).2⟩
    · exact absurd (Prod.mk.inj isReplacement).2 (fun same => Bool.noConfusion same)
  case dropStays =>
    intro k name name' matched marked notFired d drops
    have nameIs : name' = semanticSubstName k (.apply "NQuote" [q]) name := by
      unfold semanticSubstName
      rw [marked]
    rw [semanticSubstProc.eq_4, marked]
    dsimp only
    split
    · rename_i p
      exact absurd rfl (notFired p rfl)
    · rw [nameIs]
      simp only [weight_drop] at drops ⊢
      have nameDrops := substName_weight_le dropNode_laws quoteDrops name
        (if 2 ≤ d then d - 2 else d) (k := k)
      have nameActivity := substName_weight_le activityNode_laws quoteActivity name
        (if 2 ≤ d then d - 2 else d) (k := k)
      constructor <;> omega
  case output =>
    intro k n payload ih d drops
    rw [semanticSubstProc.eq_5, weight_output, weight_output]
    rw [weight_output] at drops
    rw [weight_output]
    have payloadResult := ih (d + 1) (by omega)
    have nameDrops := substName_weight_le dropNode_laws quoteDrops n d (k := k)
    have nameActivity := substName_weight_le activityNode_laws quoteActivity n d (k := k)
    constructor <;> omega
  case input =>
    intro k n inputBody ih d drops
    rw [semanticSubstProc.eq_6, weight_input, weight_input]
    rw [weight_input] at drops
    rw [weight_input]
    have bodyResult := ih d (by omega)
    have nameDrops := substName_weight_le dropNode_laws quoteDrops n d (k := k)
    have nameActivity := substName_weight_le activityNode_laws quoteActivity n d (k := k)
    constructor <;> omega
  case lambda =>
    intro k nm lambdaBody ih d drops
    rw [semanticSubstProc.eq_7]
    simp only [weight] at drops ⊢
    exact ih d drops
  case multiLambda =>
    intro k n nms lambdaBody ih d drops
    rw [semanticSubstProc.eq_8]
    simp only [weight] at drops ⊢
    exact ih d drops
  case subst =>
    intro k substBody repl ihBody ihRepl d drops
    rw [semanticSubstProc.eq_9]
    simp only [weight] at drops ⊢
    have bodyResult := ihBody d (by omega)
    have replResult := ihRepl d (by omega)
    constructor <;> omega
  case collection =>
    intro k ct elems rest ih d drops
    rw [semanticSubstProc.eq_10]
    simp only [weight] at drops ⊢
    exact ih d drops
  case other =>
    intro k p notBvar notFvar notQuote notDrop notOutput notInput notLambda notMulti notSubst
      notCollection d drops
    rw [semanticSubstProc.eq_11 k _ p notBvar notFvar notQuote notDrop notOutput notInput
      notLambda notMulti notSubst notCollection]
    exact ⟨le_refl _, drops⟩
  case nil =>
    intro k d _
    rw [semanticSubstProcList.eq_1]
    exact ⟨le_refl _, rfl⟩
  case cons =>
    intro k p ps ihHead ihTail d drops
    rw [semanticSubstProcList.eq_2]
    simp only [weightList] at drops ⊢
    have headResult := ihHead d (by omega)
    have tailResult := ihTail d (by omega)
    constructor <;> omega


/-! ## One communication lowers activity by two -/

/-- The weight of a bag with two leading elements. -/
theorem weight_par_two_append (node : String → Nat → Nat) (d : Nat) (first second : Pattern)
    (rest : List Pattern) :
    weight node d (par ([first, second] ++ rest)) =
      weight node d first + weight node d second + weightList node d rest := by
  simp only [weight, List.cons_append, List.nil_append, weightList]
  omega

/-- The weight of a bag with one leading element. -/
theorem weight_par_cons (node : String → Nat → Nat) (d : Nat) (first : Pattern)
    (rest : List Pattern) :
    weight node d (par ([first] ++ rest)) = weight node d first + weightList node d rest := by
  simp only [weight, List.cons_append, List.nil_append, weightList]

/-- **The COMM step.**  A code-inert redex communicates to a code-inert result,
and loses at least the two prefixes that met. -/
theorem comm_codeInert {channel payload body : Pattern} {rest : List Pattern}
    (inert : CodeInert (par ([.apply "POutput" [channel, payload],
      .apply "PInput" [channel, .lambda none body]] ++ rest))) :
    CodeInert (par ([semanticCommSubst body payload] ++ rest)) ∧
      weight activityNode 0 (par ([semanticCommSubst body payload] ++ rest)) + 2 ≤
        weight activityNode 0 (par ([.apply "POutput" [channel, payload],
          .apply "PInput" [channel, .lambda none body]] ++ rest)) := by
  obtain ⟨noDrops, noLatent⟩ := inert
  simp only [weight_par_two_append, weight_output, weight_input] at noDrops noLatent
  -- the quoted payload is inert at every depth `≥ 2`
  have inertPayload : ∀ e, 2 ≤ e →
      weight activityNode e (semanticNormalizeProc payload) = 0 ∧
        weight dropNode e (semanticNormalizeProc payload) = 0 := by
    intro e deep
    rw [activity_normalizeProc, unguarded_normalizeProc]
    have latent := noLatent (e - 1) (by omega)
    have drops := noDrops (e - 1)
    rw [show e - 1 + 1 = e by omega] at latent drops
    constructor <;> omega
  have substituted := fun d (bodyDrops : weight dropNode d body = 0) =>
    substProc_weights inertPayload 0 body d bodyDrops
  unfold semanticCommSubst
  refine ⟨⟨fun d => ?_, fun d deep => ?_⟩, ?_⟩
  · have drops := noDrops d
    have result := substituted d (by omega)
    rw [weight_par_cons]
    omega
  · have latent := noLatent d deep
    have drops := noDrops d
    have result := substituted d (by omega)
    rw [weight_par_cons]
    omega
  · have drops := noDrops 0
    have result := substituted 0 (by omega)
    rw [weight_par_cons, weight_par_two_append, weight_output, weight_input,
      activityNode_output_top, activityNode_input_top]
    omega

/-- A component of a bag is code-inert when the bag is. -/
theorem codeInert_of_mem {elems : List Pattern} {p : Pattern} (member : p ∈ elems)
    (inert : CodeInert (par elems)) : CodeInert p :=
  ⟨fun d => Nat.eq_zero_of_le_zero ((weight_mem_le dropNode member).trans (inert.1 d).le),
    fun d deep => Nat.eq_zero_of_le_zero
      ((weight_mem_le activityNode member).trans (inert.2 d deep).le)⟩

/-- **Main theorem.**  A reduction step of a code-inert pattern stays
code-inert and lowers the activity at depth 0 by at least two. -/
theorem reduces_codeInert {source target : Pattern} (step : source ⇝ target) :
    CodeInert source →
      CodeInert target ∧ weight activityNode 0 target + 2 ≤ weight activityNode 0 source := by
  induction step with
  | comm => exact comm_codeInert
  | equiv before _ after ih =>
      intro inert
      obtain ⟨inertTarget, decrease⟩ := ih (codeInert_of_sc before inert)
      refine ⟨codeInert_of_sc after inertTarget, ?_⟩
      rw [← weight_sc activityNode_laws after 0, weight_sc activityNode_laws before 0]
      exact decrease
  | @par p q rest _ ih =>
      intro inert
      have inertHead : CodeInert p := codeInert_of_mem (List.mem_cons_self) inert
      obtain ⟨inertStep, decrease⟩ := ih inertHead
      obtain ⟨noDrops, noLatent⟩ := inert
      simp only [weight, weightList] at noDrops noLatent ⊢
      refine ⟨⟨fun d => ?_, fun d deep => ?_⟩, by omega⟩
      · have := noDrops d
        have := inertStep.1 d
        simp only [weight, weightList]
        omega
      · have := noLatent d deep
        have := inertStep.2 d deep
        simp only [weight, weightList]
        omega
  | @par_any p q before after _ ih =>
      intro inert
      have inertMiddle : CodeInert p :=
        codeInert_of_mem (by simp) inert
      obtain ⟨inertStep, decrease⟩ := ih inertMiddle
      obtain ⟨noDrops, noLatent⟩ := inert
      simp only [weight, weightList_append, weightList] at noDrops noLatent ⊢
      refine ⟨⟨fun d => ?_, fun d deep => ?_⟩, by omega⟩
      · have := noDrops d
        have := inertStep.1 d
        simp only [weight, weightList_append, weightList]
        omega
      · have := noLatent d deep
        have := inertStep.2 d deep
        simp only [weight, weightList_append, weightList]
        omega

/-! ## Consequences -/

/-- **Bounded runs.**  `n` reduction steps from a code-inert pattern stay
code-inert and consume twice `n` of its activity. -/
theorem reducesN_codeInert {n : Nat} {source target : Pattern} (steps : source ⇝[n] target) :
    CodeInert source →
      CodeInert target ∧ weight activityNode 0 target + 2 * n ≤ weight activityNode 0 source := by
  induction steps with
  | zero p => exact fun inert => ⟨inert, by omega⟩
  | succ first _ ih =>
      intro inert
      obtain ⟨inertMiddle, decreaseFirst⟩ := reduces_codeInert first inert
      obtain ⟨inertTarget, decreaseRest⟩ := ih inertMiddle
      exact ⟨inertTarget, by omega⟩

/-- **Every reduction sequence is bounded by the activity**: `n` steps from a
code-inert pattern need `2 * n ≤ activity 0 P`. -/
theorem reducesN_length_le {n : Nat} {source target : Pattern} (steps : source ⇝[n] target)
    (inert : CodeInert source) : 2 * n ≤ activity 0 source := by
  have := (reducesN_codeInert steps inert).2
  change 2 * n ≤ weight activityNode 0 source
  omega

/-- **No infinite reduction sequence starts in the fragment.** -/
theorem no_infinite_reduction {source : Pattern} (inert : CodeInert source) :
    ¬ ∃ sequence : Nat → Pattern, sequence 0 = source ∧
      ∀ n, Nonempty (sequence n ⇝ sequence (n + 1)) := by
  rintro ⟨sequence, start, steps⟩
  have bound : ∀ n, CodeInert (sequence n) ∧
      weight activityNode 0 (sequence n) + 2 * n ≤ weight activityNode 0 source := by
    intro n
    induction n with
    | zero => exact ⟨start ▸ inert, by rw [start]; omega⟩
    | succ n ih =>
        obtain ⟨step⟩ := steps n
        obtain ⟨inertNext, decrease⟩ := reduces_codeInert step ih.1
        exact ⟨inertNext, by omega⟩
  have := (bound (weight activityNode 0 source + 1)).2
  omega

/-- The activity of a parallel pair adds. -/
theorem weight_par_pair (node : String → Nat → Nat) (d : Nat) (first second : Pattern) :
    weight node d (par [first, second]) = weight node d first + weight node d second := by
  simp only [weight, weightList]
  omega

/-- **No fixed point of `X ↦ X | P` in the fragment.**  If `P` has an active
prefix, no code-inert `X` reduces in a positive number of steps to a pattern
congruent to `X | P`. -/
theorem not_reduces_beside {n : Nat} {X Y P : Pattern} (inert : CodeInert X)
    (active : 1 ≤ activity 0 P) (steps : X ⇝[n + 1] Y) (congruent : Y ≡ par [X, P]) :
    False := by
  have decrease := (reducesN_codeInert steps inert).2
  rw [weight_sc activityNode_laws congruent 0, weight_par_pair] at decrease
  change 1 ≤ weight activityNode 0 P at active
  omega

/-- The one-step form, which is the shape of the diagonal fixed point. -/
theorem not_reduces_to_beside {X P : Pattern} (inert : CodeInert X)
    (active : 1 ≤ activity 0 P) : ¬ Nonempty (X ⇝ par [X, P]) := by
  rintro ⟨step⟩
  exact not_reduces_beside inert active (.succ step (.zero _)) (StructuralCongruence.refl _)

/-! ## The reflective replicator lies outside the fragment -/

/-- The duplicator has an unguarded drop: the body `*y` runs at depth 0. -/
theorem one_le_unguarded_duplicator (x : Pattern) : 1 ≤ unguarded 0 (duplicator x) := by
  change 1 ≤ weight dropNode 0 (duplicator x)
  have runningDrop : weight dropNode 0 (.apply "PDrop" [.bvar 0]) = 1 := by
    rw [weight_drop, dropNode_drop, if_pos (show 0 < 2 by decide)]
    rfl
  unfold duplicator duplicatorBody
  rw [weight_input, weight_par_pair, runningDrop]
  omega

/-- **The replicator is not code-inert.** -/
theorem replicate_not_codeInert (x P : Pattern) : ¬ CodeInert (replicate x P) := by
  intro inert
  have duplicatorInert : CodeInert (duplicator x) :=
    codeInert_of_mem (elems := [.apply "POutput" [x, par [duplicator x, P]], duplicator x])
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) inert
  have := one_le_unguarded_duplicator x
  change 1 ≤ weight dropNode 0 (duplicator x) at this
  rw [duplicatorInert.1 0] at this
  omega

/-- **Drop is essential.**  With drop, the replicator is a fixed point of
`X ↦ X | P` up to one step; in the code-inert fragment, which contains every
drop-free pattern, no pattern is, once `P` has an active prefix. -/
theorem drop_is_essential {x : Pattern} (inertChannel : ChannelInert x) {P : Pattern}
    (active : 1 ≤ activity 0 P) :
    Nonempty (replicate x P ⇝ par [replicate x P, P]) ∧ ¬ CodeInert (replicate x P) ∧
      ∀ X, CodeInert X → ¬ Nonempty (X ⇝ par [X, P]) :=
  ⟨replicate_unfold inertChannel P, replicate_not_codeInert x P,
    fun _ inert => not_reduces_to_beside inert active⟩

/-- **The Lawvere contrapositive in the fragment.**  No code-inert code
represents the diagonal composite of `X ↦ X | P` over a code-inert channel:
its diagonal fixed point would be a code-inert fixed point. -/
theorem not_represents_of_codeInert {x code P : Pattern} (inertChannel : CodeInert x)
    (inertCode : CodeInert code) (active : 1 ≤ activity 0 P) :
    ¬ Mettapedia.Logic.Diagonal.RepresentsBy (run x) ReducesTo code
      (Mettapedia.Logic.Diagonal.diagonalComposite (run x) (beside P)) := by
  intro represents
  have fixed := Mettapedia.Logic.Diagonal.diagonal (run x) ReducesTo (beside P) represents
  have inertRun : CodeInert (run x code code) := by
    obtain ⟨channelDrops, channelLatent⟩ := inertChannel
    obtain ⟨codeDrops, codeLatent⟩ := inertCode
    refine ⟨fun d => ?_, fun d deep => ?_⟩
    · unfold run
      rw [weight_par_pair, weight_output, channelDrops d, codeDrops d, codeDrops (d + 1),
        dropNode_other (show "POutput" ≠ "PDrop" by decide)]
    · unfold run
      rw [weight_par_pair, weight_output, channelLatent d deep, codeLatent d deep,
        codeLatent (d + 1) (by omega), activityNode_deep _ deep]
  exact not_reduces_to_beside inertRun active fixed

/-- A concrete drop-free active process: `@0!(0)`. -/
def sendZero : Pattern := .apply "POutput" [atZero, .apply "PZero" []]

theorem sendZero_dropFree : hasDrop sendZero = false := rfl

/-- The empty process weighs nothing. -/
theorem weight_zeroProcess {node : String → Nat → Nat} (laws : NodeLaws node) (d : Nat) :
    weight node d (.apply "PZero" []) = 0 := by
  simp only [weight, weightArgs, laws.zero]

/-- The name `@0` weighs nothing. -/
theorem weight_atZero {node : String → Nat → Nat} (laws : NodeLaws node) (d : Nat) :
    weight node d atZero = 0 := by
  unfold atZero
  rw [weight_quote laws, weight_zeroProcess laws]

theorem sendZero_active : 1 ≤ activity 0 sendZero := by
  change 1 ≤ weight activityNode 0 sendZero
  unfold sendZero
  rw [weight_output, activityNode_output_top]
  omega

/-- **Instance.**  Replicating `@0!(0)` on `@0` runs forever, while no
drop-free pattern reduces to itself beside `@0!(0)`. -/
theorem replicate_sendZero_contrast :
    Nonempty (replicate atZero sendZero ⇝ par [replicate atZero sendZero, sendZero]) ∧
      ∀ X, hasDrop X = false → ¬ Nonempty (X ⇝ par [X, sendZero]) :=
  ⟨replicate_unfold atZero_channelInert sendZero,
    fun _ free => not_reduces_to_beside (codeInert_of_dropFree free) sendZero_active⟩

/-- **Positive control**: a drop-free communication,
`@0!(0) | for (y ← @0) 0`. -/
def ping : Pattern :=
  par [sendZero, .apply "PInput" [atZero, .lambda none (.apply "PZero" [])]]

theorem ping_dropFree : hasDrop ping = false := rfl

/-- The drop-free fragment contains genuine reductions: `ping` communicates. -/
theorem ping_reduces :
    Nonempty (ping ⇝ par [semanticCommSubst (.apply "PZero" []) (.apply "PZero" [])]) :=
  ⟨Reduces.comm (n := atZero) (q := .apply "PZero" []) (p := .apply "PZero" []) (rest := [])⟩

/-- Its activity is two, so the bound allows exactly the one step it takes. -/
theorem ping_activity : activity 0 ping = 2 := by
  change weight activityNode 0 ping = 2
  unfold ping sendZero
  rw [weight_par_pair, weight_output, weight_input, activityNode_output_top,
    activityNode_input_top, weight_atZero activityNode_laws, weight_zeroProcess activityNode_laws,
    weight_zeroProcess activityNode_laws]

theorem ping_one_step {n : Nat} {target : Pattern} (steps : ping ⇝[n] target) : n ≤ 1 := by
  have := reducesN_length_le steps (codeInert_of_dropFree ping_dropFree)
  rw [ping_activity] at this
  omega

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.DropFreeTermination
