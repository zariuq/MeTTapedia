import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DropFreeTermination
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PayloadQuoteBoundary

/-!
# Where value and code observers meet: quote, drop and substitution in rho

In the canonical Lean rho, a process can be observed in two ways.

* A **code observer** reads a process itself, up to structural congruence:
  an output payload is such a position, because communication quotes the
  payload and a receiver may compare the quote as a channel.
* A **value observer** reads only the name a payload becomes, up to
  structural congruence of names.

**Positive: structural congruence passes through quote, drop and
substitution.**
* Communication realises the retraction `drop ∘ quote ≈ id`
  (`drop_quote_retraction`).
* Quote and drop preserve structural congruence (`quote_sc`, `drop_sc`).
* Substituting the quotes of two congruent processes gives congruent results,
  in every body, including where a bound drop collapses to the substituted
  process (`substProc_quote_sc`).
* Hence communication preserves congruence of payloads
  (`commSubst_payload_sc`), and a communication step with a payload has a
  congruent counterpart with any congruent payload (`comm_payload_sc`).

**Negative control: the value equality is strictly coarser, and payload
positions do not preserve it.**
* `0` and `*@0` send congruent names, since `@(*@0) ≡ @0` is the quote-drop law
  (`values_equal`), but they are not congruent processes: `*@0` has a drop at
  depth 0, which the congruence-invariant measure `unguarded` counts
  (`codes_distinct`).  Quotation does not reflect congruence.
* Placed in the payload position of `@0!(□)`, the two become `@0!(0)` and
  `@0!(*@0)`, which are not congruent (`outputs_not_sc`): the payload position
  is a code position.  So no relation that contains the value equality and is
  preserved by payload positions is contained in structural congruence
  (`value_equality_not_preserved`).

This is the real-rho counterpart, at the level of structural congruence, of
the collapse proved in the quoted-channel calculus: once a code position is
admitted, the equality it preserves is the code equality.  It concerns
structural congruence, not a bisimilarity over the full calculus.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuoteMeetingPoint

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReflectiveReplication
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DropFreeTermination

private theorem sc_trans {a b c : Pattern} (first : a ≡ b) (second : b ≡ c) : a ≡ c :=
  StructuralCongruence.trans _ _ _ first second

private theorem sc_symm {a b : Pattern} (h : a ≡ b) : b ≡ a :=
  StructuralCongruence.symm _ _ h

/-- **The code/behaviour retraction of rho**: a received quote, dropped, is
the process that was sent, up to structural congruence.  Communication
realises `drop ∘ quote ≈ id`. -/
theorem drop_quote_retraction (process : Pattern) :
    semanticCommSubst (.apply "PDrop" [.bvar 0]) process ≡ process := by
  have collapses :
      semanticCommSubst (.apply "PDrop" [.bvar 0]) process = semanticNormalizeProc process := rfl
  rw [collapses]
  exact normalizeProc_sc process

/-- **Quote preserves structural congruence.** -/
theorem quote_sc {a a' : Pattern} (congruent : a ≡ a') :
    StructuralCongruence (.apply "NQuote" [a]) (.apply "NQuote" [a']) := by
  refine StructuralCongruence.apply_cong "NQuote" [a] [a'] rfl ?_
  intro i h₁ _
  match i, h₁ with
  | 0, _ => exact congruent
  | n + 1, h₁ => exact absurd (Nat.lt_of_succ_lt_succ h₁) (Nat.not_lt_zero n)

/-- **Drop preserves structural congruence.** -/
theorem drop_sc {n n' : Pattern} (congruent : n ≡ n') :
    StructuralCongruence (.apply "PDrop" [n]) (.apply "PDrop" [n']) := by
  refine StructuralCongruence.apply_cong "PDrop" [n] [n'] rfl ?_
  intro i h₁ _
  match i, h₁ with
  | 0, _ => exact congruent
  | m + 1, h₁ => exact absurd (Nat.lt_of_succ_lt_succ h₁) (Nat.not_lt_zero m)

private theorem sc_apply_two (f : String) {a a' b b' : Pattern} (ha : a ≡ a') (hb : b ≡ b') :
    StructuralCongruence (.apply f [a, b]) (.apply f [a', b']) := by
  refine StructuralCongruence.apply_cong f [a, b] [a', b'] rfl ?_
  intro i h₁ _
  match i, h₁ with
  | 0, _ => exact ha
  | 1, _ => exact hb
  | n + 2, h₁ =>
      exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h₁)) (Nat.not_lt_zero n)

/-- A collapsing drop, in closed form: the substituted quote's process where
the normalised name is the bound name, the normalised drop elsewhere. -/
theorem substProc_drop_quote (k : Nat) (a name : Pattern) :
    semanticSubstProc k (.apply "NQuote" [a]) (.apply "PDrop" [name]) =
      if semanticNormalizeName name = .bvar k then a
      else .apply "PDrop" [semanticNormalizeName name] := by
  rw [semanticSubstProc.eq_4, substNameMark_eq]
  split_ifs
  · rfl
  · dsimp only
    split
    · contradiction
    · rfl

/-- Name substitution by a quote, in closed form. -/
theorem substName_quote_sc {a a' : Pattern} (congruent : a ≡ a') (k : Nat) (name : Pattern) :
    semanticSubstName k (.apply "NQuote" [a]) name ≡
      semanticSubstName k (.apply "NQuote" [a']) name := by
  rw [substName_eq, substName_eq]
  split_ifs
  · exact quote_sc congruent
  · exact .refl _

/-- **Substitution respects structural congruence of the substituted
process**, in every body and every list of bodies. -/
theorem substProc_quote_sc {a a' : Pattern} (congruent : a ≡ a') :
    (∀ k body, semanticSubstProc k (.apply "NQuote" [a]) body ≡
      semanticSubstProc k (.apply "NQuote" [a']) body) ∧
    (∀ k bodies, ListCongruent (semanticSubstProcList k (.apply "NQuote" [a]) bodies)
      (semanticSubstProcList k (.apply "NQuote" [a']) bodies)) := by
  refine semanticSubstProc.mutual_induct (.apply "NQuote" [a])
    (fun k body => semanticSubstProc k (.apply "NQuote" [a]) body ≡
      semanticSubstProc k (.apply "NQuote" [a']) body)
    (fun k bodies => ListCongruent (semanticSubstProcList k (.apply "NQuote" [a]) bodies)
      (semanticSubstProcList k (.apply "NQuote" [a']) bodies))
    ?boundHit ?boundMiss ?free ?quote ?dropMatched ?dropUnmatched ?output ?input ?lambda
    ?multiLambda ?subst ?collection ?other ?nil ?cons
  case boundHit =>
    intro k n hit
    rw [semanticSubstProc.eq_1, semanticSubstProc.eq_1, if_pos hit, if_pos hit]
    exact quote_sc congruent
  case boundMiss =>
    intro k n miss
    rw [semanticSubstProc.eq_1, semanticSubstProc.eq_1, if_neg miss, if_neg miss]
    exact .refl _
  case free =>
    intro k x
    rw [semanticSubstProc.eq_2, semanticSubstProc.eq_2]
    exact .refl _
  case quote =>
    intro k p
    rw [semanticSubstProc.eq_3, semanticSubstProc.eq_3]
    exact .refl _
  case dropMatched =>
    intro k name _ _
    rw [substProc_drop_quote, substProc_drop_quote]
    split_ifs
    · exact congruent
    · exact .refl _
  case dropUnmatched =>
    intro k name _ _ _ _
    rw [substProc_drop_quote, substProc_drop_quote]
    split_ifs
    · exact congruent
    · exact .refl _
  case output =>
    intro k n q ih
    rw [semanticSubstProc.eq_5, semanticSubstProc.eq_5]
    exact sc_apply_two "POutput" (substName_quote_sc congruent k n) ih
  case input =>
    intro k n body ih
    rw [semanticSubstProc.eq_6, semanticSubstProc.eq_6]
    exact sc_apply_two "PInput" (substName_quote_sc congruent k n)
      (StructuralCongruence.lambda_cong none _ _ ih)
  case lambda =>
    intro k nm body ih
    rw [semanticSubstProc.eq_7, semanticSubstProc.eq_7]
    exact StructuralCongruence.lambda_cong nm _ _ ih
  case multiLambda =>
    intro k n nms body ih
    rw [semanticSubstProc.eq_8, semanticSubstProc.eq_8]
    exact StructuralCongruence.multiLambda_cong n nms _ _ ih
  case subst =>
    intro k body repl ihBody ihRepl
    rw [semanticSubstProc.eq_9, semanticSubstProc.eq_9]
    exact StructuralCongruence.subst_cong _ _ _ _ ihBody ihRepl
  case collection =>
    intro k ct elems rest ih
    rw [semanticSubstProc.eq_10, semanticSubstProc.eq_10]
    exact StructuralCongruence.collection_general_cong ct _ _ rest ih.1 ih.2
  case other =>
    intro k p notBvar notFvar notQuote notDrop notOutput notInput notLambda notMulti notSubst
      notCollection
    rw [semanticSubstProc.eq_11 k _ p notBvar notFvar notQuote notDrop notOutput notInput
      notLambda notMulti notSubst notCollection,
      semanticSubstProc.eq_11 k _ p notBvar notFvar notQuote notDrop notOutput notInput
      notLambda notMulti notSubst notCollection]
    exact .refl _
  case nil =>
    intro k
    rw [semanticSubstProcList.eq_1, semanticSubstProcList.eq_1]
    exact ⟨rfl, fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)⟩
  case cons =>
    intro k p ps ihHead ihTail
    rw [semanticSubstProcList.eq_2, semanticSubstProcList.eq_2]
    refine ⟨congrArg Nat.succ ihTail.1, ?_⟩
    intro i h₁ h₂
    match i, h₁, h₂ with
    | 0, _, _ => exact ihHead
    | n + 1, h₁, h₂ =>
        exact ihTail.2 n (Nat.lt_of_succ_lt_succ h₁) (Nat.lt_of_succ_lt_succ h₂)

/-- **Communication preserves congruence of payloads.** -/
theorem commSubst_payload_sc {q q' : Pattern} (congruent : q ≡ q') (body : Pattern) :
    semanticCommSubst body q ≡ semanticCommSubst body q' :=
  (substProc_quote_sc (sc_trans (normalizeProc_sc q)
    (sc_trans congruent (sc_symm (normalizeProc_sc q'))))).1 0 body

/-- **A communication with a payload has a congruent counterpart with any
congruent payload**: the sources are congruent and so are the reducts. -/
theorem comm_payload_sc {channel q q' body : Pattern} {rest : List Pattern}
    (congruent : q ≡ q') :
    (par ([.apply "POutput" [channel, q], .apply "PInput" [channel, .lambda none body]] ++ rest) ≡
        par ([.apply "POutput" [channel, q'], .apply "PInput" [channel, .lambda none body]] ++
          rest)) ∧
      Nonempty (par ([.apply "POutput" [channel, q], .apply "PInput" [channel, .lambda none body]]
          ++ rest) ⇝ par ([semanticCommSubst body q] ++ rest)) ∧
      Nonempty (par ([.apply "POutput" [channel, q'], .apply "PInput" [channel, .lambda none body]]
          ++ rest) ⇝ par ([semanticCommSubst body q'] ++ rest)) ∧
      (par ([semanticCommSubst body q] ++ rest) ≡ par ([semanticCommSubst body q'] ++ rest)) := by
  refine ⟨?_, ⟨Reduces.comm⟩, ⟨Reduces.comm⟩, ?_⟩
  · refine StructuralCongruence.par_cong _ _ (by simp) ?_
    intro i h₁ h₂
    match i, h₁, h₂ with
    | 0, _, _ => exact sc_apply_two "POutput" (.refl channel) congruent
    | 1, _, _ => exact .refl _
    | n + 2, _, _ => exact .refl _
  · refine StructuralCongruence.par_cong _ _ (by simp) ?_
    intro i h₁ h₂
    match i, h₁, h₂ with
    | 0, _, _ => exact commSubst_payload_sc congruent body
    | n + 1, _, _ => exact .refl _

/-! ## Negative control: value equality against code equality -/

/-- The empty process `0`. -/
def zero : Pattern := .apply "PZero" []

/-- The name `@0`. -/
def atZeroName : Pattern := .apply "NQuote" [zero]

/-- The process `*@0`. -/
def dropAtZero : Pattern := .apply "PDrop" [atZeroName]

/-- **Value observers identify `0` and `*@0`**: the names they become are
congruent, by the quote-drop law. -/
theorem values_equal :
    StructuralCongruence (.apply "NQuote" [dropAtZero]) (.apply "NQuote" [zero]) :=
  StructuralCongruence.quote_drop atZeroName

theorem unguarded_zero : unguarded 0 zero = 0 := rfl

theorem unguarded_dropAtZero : unguarded 0 dropAtZero = 1 := rfl

/-- **Code observers separate them**: `0` and `*@0` are not congruent
processes.  Quotation does not reflect congruence. -/
theorem codes_distinct : ¬ (zero ≡ dropAtZero) := by
  intro congruent
  have same := unguarded_sc congruent 0
  rw [unguarded_zero, unguarded_dropAtZero] at same
  exact absurd same (by decide)

/-- The payload context `@0!(□)`. -/
def sendOnZero (payload : Pattern) : Pattern := .apply "POutput" [atZeroName, payload]

theorem unguarded_sendOnZero_zero : unguarded 0 (sendOnZero zero) = 0 := rfl

theorem unguarded_sendOnZero_drop : unguarded 0 (sendOnZero dropAtZero) = 1 := rfl

/-- **The payload position is a code position**: `@0!(0)` and `@0!(*@0)` are
not congruent, although their payloads send congruent names. -/
theorem outputs_not_sc : ¬ (sendOnZero zero ≡ sendOnZero dropAtZero) := by
  intro congruent
  have same := unguarded_sc congruent 0
  rw [unguarded_sendOnZero_zero, unguarded_sendOnZero_drop] at same
  exact absurd same (by decide)

/-- **The value equality is not preserved by payload positions into code
equality**: no relation that relates processes sending congruent names and is
carried by the payload context into structural congruence exists. -/
theorem value_equality_not_preserved :
    ¬ ∀ first second : Pattern,
        StructuralCongruence (.apply "NQuote" [first]) (.apply "NQuote" [second]) →
          sendOnZero first ≡ sendOnZero second := fun preserved =>
  outputs_not_sc (preserved zero dropAtZero (sc_symm values_equal))

/-- **Congruence itself is preserved by the payload context.** -/
theorem code_equality_preserved {first second : Pattern} (congruent : first ≡ second) :
    sendOnZero first ≡ sendOnZero second :=
  sc_apply_two "POutput" (.refl atZeroName) congruent

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuoteMeetingPoint
