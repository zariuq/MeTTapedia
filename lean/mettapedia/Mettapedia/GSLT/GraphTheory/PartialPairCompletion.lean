import Mettapedia.GSLT.GraphTheory.PartialPairCompletionStages

/-!
# Canonical completion of a partial pair

Bucciarelli–Salibra §2.3 Definition 4's limit uses Mathlib's existing
`DirectLimit` of the actual canonical-successor stages. Every finite limit
input lifts to one stage and becomes defined at its successor. Coding is
independent of representatives and injective on full finite inputs.
This construction does not establish the weak-product interpretation or
theory-intersection results.
-/

namespace Mettapedia.GSLT.GraphTheory.PartialPair.Completion

open Mettapedia.GSLT.Core CompletionStages

abbrev Carrier (pair : PartialPair) :=
  DirectLimit (fun n => (stage pair n).Carrier) (fun _ _ h => inclusion pair h)

def embed (pair : PartialPair) (n : Nat) : (stage pair n).Carrier ↪ Carrier pair where
  toFun token := ⟦⟨n, token⟩⟧
  inj' := DirectLimit.mk_injective (fun _ _ h => inclusion pair h)
    (fun _ _ h => (inclusion pair h).injective) n

theorem embed_inclusion (pair : PartialPair) {n m : Nat} (h : n ≤ m)
    (token : (stage pair n).Carrier) :
    embed pair m (inclusion pair h token) = embed pair n token := by
  exact DirectLimit.mk_apply (f := fun _ _ h => inclusion pair h) n m token h

theorem inclusion_embed (pair : PartialPair) {n m : Nat} (h : n ≤ m) :
    (inclusion pair h).trans (embed pair m) = embed pair n := by
  ext token
  exact embed_inclusion pair h token

theorem support_embed (pair : PartialPair) {n m : Nat} (h : n ≤ m)
    (support : Finset (stage pair n).Carrier) :
    (support.map (inclusion pair h)).map (embed pair m) = support.map (embed pair n) := by
  rw [Finset.map_map, inclusion_embed pair h]

theorem align_values (pair : PartialPair) {n m k : Nat} (h : n ≤ k) (h' : m ≤ k)
    (first : (stage pair n).Carrier) (second : (stage pair m).Carrier)
    (hValues : embed pair n first = embed pair m second) :
    inclusion pair h first = inclusion pair h' second := by
  apply (embed pair k).injective
  rw [embed_inclusion pair h, embed_inclusion pair h']
  exact hValues

theorem align_supports (pair : PartialPair) {n m k : Nat} (h : n ≤ k) (h' : m ≤ k)
    (first : Finset (stage pair n).Carrier) (second : Finset (stage pair m).Carrier)
    (hSupports : first.map (embed pair n) = second.map (embed pair m)) :
    first.map (inclusion pair h) = second.map (inclusion pair h') := by
  apply Finset.map_injective (embed pair k)
  rw [support_embed pair h, support_embed pair h']
  exact hSupports

/-- A finite support and its output have representatives in one common stage. -/
theorem common_stage (pair : PartialPair) (support : Finset (Carrier pair))
    (output : Carrier pair) :
    ∃ (n : Nat) (oldSupport : Finset (stage pair n).Carrier) (oldOutput : (stage pair n).Carrier),
      oldSupport.map (embed pair n) = support ∧ embed pair n oldOutput = output := by
  classical
  induction support using Finset.induction_on with
  | empty =>
      obtain ⟨n, token, hToken⟩ := DirectLimit.exists_eq_mk
        (fun _ _ h => inclusion pair h) output
      exact ⟨n, ∅, token, Finset.map_empty _, hToken.symm⟩
  | @insert token support hNotMember ih =>
      obtain ⟨n, oldSupport, oldOutput, hSupport, hOutput⟩ := ih
      obtain ⟨m, newToken, hToken⟩ := DirectLimit.exists_eq_mk
        (fun _ _ h => inclusion pair h) token
      let k := max n m
      have hn : n ≤ k := Nat.le_max_left _ _
      have hm : m ≤ k := Nat.le_max_right _ _
      refine ⟨k, insert (inclusion pair hm newToken) (oldSupport.map (inclusion pair hn)),
        inclusion pair hn oldOutput, ?_, ?_⟩
      · rw [Finset.map_insert, embed_inclusion pair hm, support_embed pair hn, hSupport]
        exact congrArg (fun t => insert t support) hToken.symm
      · exact (embed_inclusion pair hn oldOutput).trans hOutput

/-- A code is witnessed by actual defined stage coding of the full input. -/
def CodeRelation (pair : PartialPair) (support : Finset (Carrier pair))
    (output token : Carrier pair) : Prop :=
  ∃ (n : Nat) (oldSupport : Finset (stage pair n).Carrier)
      (oldOutput oldToken : (stage pair n).Carrier),
    oldSupport.map (embed pair n) = support ∧ embed pair n oldOutput = output ∧
      (stage pair n).coding.code (oldSupport, oldOutput) = some oldToken ∧
        embed pair n oldToken = token

theorem codeRelation_exists (pair : PartialPair) (support : Finset (Carrier pair))
    (output : Carrier pair) : ∃ token, CodeRelation pair support output token := by
  obtain ⟨n, oldSupport, oldOutput, hSupport, hOutput⟩ := common_stage pair support output
  obtain ⟨token, hCode⟩ := input_defined_next pair n oldSupport oldOutput
  refine ⟨embed pair (n + 1) token, n + 1,
    oldSupport.map (inclusion pair (Nat.le_succ n)),
    inclusion pair (Nat.le_succ n) oldOutput, token, ?_, ?_, hCode, rfl⟩
  · exact (support_embed pair (Nat.le_succ n) oldSupport).trans hSupport
  · exact (embed_inclusion pair (Nat.le_succ n) oldOutput).trans hOutput

/-- Different representatives of one full input give the same limit output. -/
theorem codeRelation_unique (pair : PartialPair) {support : Finset (Carrier pair)}
    {output first second : Carrier pair} (hFirst : CodeRelation pair support output first)
    (hSecond : CodeRelation pair support output second) : first = second := by
  obtain ⟨n, a, x, token, hA, hX, hCode, hToken⟩ := hFirst
  obtain ⟨m, b, y, other, hB, hY, hOtherCode, hOther⟩ := hSecond
  let k := max n m
  have hn : n ≤ k := Nat.le_max_left _ _
  have hm : m ≤ k := Nat.le_max_right _ _
  have hSupport := align_supports pair hn hm a b (hA.trans hB.symm)
  have hOutput := align_values pair hn hm x y (hX.trans hY.symm)
  have hCode₁ := (code_old_output_iff pair hn a x token).mpr hCode
  have hCode₂ := (code_old_output_iff pair hm b y other).mpr hOtherCode
  rw [hSupport, hOutput] at hCode₁
  have hCodes := Option.some.inj (hCode₁.symm.trans hCode₂)
  calc
    first = embed pair k (inclusion pair hn token) :=
      hToken.symm.trans (embed_inclusion pair hn token).symm
    _ = embed pair k (inclusion pair hm other) := congrArg (embed pair k) hCodes
    _ = second := (embed_inclusion pair hm other).trans hOther

/-- Equal coded outputs force equality of the entire limit inputs. -/
theorem codeRelation_injective (pair : PartialPair)
    {firstSupport secondSupport : Finset (Carrier pair)} {firstOutput secondOutput token : Carrier pair}
    (hFirst : CodeRelation pair firstSupport firstOutput token)
    (hSecond : CodeRelation pair secondSupport secondOutput token) :
    (firstSupport, firstOutput) = (secondSupport, secondOutput) := by
  obtain ⟨n, a, x, first, hA, hX, hCode, hFirstToken⟩ := hFirst
  obtain ⟨m, b, y, second, hB, hY, hOtherCode, hSecondToken⟩ := hSecond
  let k := max n m
  have hn : n ≤ k := Nat.le_max_left _ _
  have hm : m ≤ k := Nat.le_max_right _ _
  have hTokens := align_values pair hn hm first second (hFirstToken.trans hSecondToken.symm)
  have hCode₁ := (code_old_output_iff pair hn a x first).mpr hCode
  have hCode₂ := (code_old_output_iff pair hm b y second).mpr hOtherCode
  rw [hTokens] at hCode₁
  have hInputs := (stage pair k).coding.injective hCode₁ hCode₂
  obtain ⟨hSupport, hOutput⟩ := Prod.ext_iff.mp hInputs
  apply Prod.ext
  · calc
      firstSupport = (a.map (inclusion pair hn)).map (embed pair k) :=
        hA.symm.trans (support_embed pair hn a).symm
      _ = (b.map (inclusion pair hm)).map (embed pair k) :=
        congrArg (Finset.map (embed pair k)) hSupport
      _ = secondSupport := (support_embed pair hm b).trans hB
  · calc
      firstOutput = embed pair k (inclusion pair hn x) :=
        hX.symm.trans (embed_inclusion pair hn x).symm
      _ = embed pair k (inclusion pair hm y) := congrArg (embed pair k) hOutput
      _ = secondOutput := (embed_inclusion pair hm y).trans hY

/-- Representative choice occurs only after existence and independence. -/
noncomputable def code (pair : PartialPair) (input : Finset (Carrier pair) × Carrier pair) :
    Carrier pair := Classical.choose (codeRelation_exists pair input.1 input.2)

theorem code_spec (pair : PartialPair) (input : Finset (Carrier pair) × Carrier pair) :
    CodeRelation pair input.1 input.2 (code pair input) :=
  Classical.choose_spec (codeRelation_exists pair input.1 input.2)

theorem code_eq_iff (pair : PartialPair) (input : Finset (Carrier pair) × Carrier pair)
    (token : Carrier pair) : code pair input = token ↔ CodeRelation pair input.1 input.2 token := by
  constructor
  · intro h; rw [← h]; exact code_spec pair input
  · exact codeRelation_unique pair (code_spec pair input)

theorem code_injective (pair : PartialPair) : Function.Injective (code pair) := by
  intro first second h
  have hFirst := code_spec pair first
  have hSecond := code_spec pair second
  rw [← h] at hSecond
  exact codeRelation_injective pair hFirst hSecond

noncomputable def graphModel (pair : PartialPair) : GraphModel where
  web := {
    carrier := Carrier pair
    decEq := Classical.decEq _
    infinite := Infinite.of_injective (embed pair 0) (embed pair 0).injective
  }
  coding := {
    code := code pair
    injective := code_injective pair
  }

/-- Every existing defined code, not only base-stage codes, is preserved. -/
theorem code_preserves_stage (pair : PartialPair) (n : Nat)
    (support : Finset (stage pair n).Carrier) (output token : (stage pair n).Carrier)
    (h : (stage pair n).coding.code (support, output) = some token) :
    code pair (support.map (embed pair n), embed pair n output) = embed pair n token := by
  apply (code_eq_iff pair _ _).mpr
  exact ⟨n, support, output, token, rfl, rfl, h, rfl⟩

/-- Completion extends the original partial pair's actual coding. -/
theorem code_preserves_original (pair : PartialPair) (support : Finset pair.Carrier)
    (output token : pair.Carrier) (h : pair.coding.code (support, output) = some token) :
    code pair (support.map (embed pair 0), embed pair 0 output) = embed pair 0 token :=
  code_preserves_stage pair 0 support output token h

/-- Source-defined outputs in a given stage are preserved and reflected:
later filling cannot manufacture a code impersonating one of its old tokens. -/
theorem code_stage_output_iff (pair : PartialPair) (n : Nat)
    (support : Finset (stage pair n).Carrier) (output token : (stage pair n).Carrier) :
    code pair (support.map (embed pair n), embed pair n output) = embed pair n token ↔
      (stage pair n).coding.code (support, output) = some token := by
  constructor
  · intro h
    obtain ⟨m, a, x, oldToken, hSupport, hOutput, hCode, hToken⟩ :=
      (code_eq_iff pair _ _).mp h
    let k := max m n
    have hm : m ≤ k := Nat.le_max_left _ _
    have hn : n ≤ k := Nat.le_max_right _ _
    have hSupports := align_supports pair hm hn a support hSupport
    have hOutputs := align_values pair hm hn x output hOutput
    have hTokens := align_values pair hm hn oldToken token hToken
    have hLater := (code_old_output_iff pair hm a x oldToken).mpr hCode
    rw [hSupports, hOutputs, hTokens] at hLater
    exact (code_old_output_iff pair hn support output token).mp hLater
  · exact code_preserves_stage pair n support output token

/-- A missing full stage input is represented by its actual successor token. -/
theorem code_fills_stage_missing (pair : PartialPair) (n : Nat)
    (support : Finset (stage pair n).Carrier) (output : (stage pair n).Carrier)
    (h : (stage pair n).coding.code (support, output) = none) :
    code pair (support.map (embed pair n), embed pair n output) =
      embed pair (n + 1) (Sum.inr ⟨(support, output), h⟩) := by
  have hStage := CompletionStep.code_fills_missing (stage pair n) support output h
  have hLimit := code_preserves_stage pair (n + 1)
    (support.map Function.Embedding.inl) (Sum.inl output) (Sum.inr ⟨(support, output), h⟩) hStage
  have hSupport : (support.map Function.Embedding.inl).map (embed pair (n + 1)) =
      support.map (embed pair n) := by
    exact (congrArg (fun f : (stage pair n).Carrier ↪ (stage pair (n + 1)).Carrier =>
      (support.map f).map (embed pair (n + 1))) (inclusion_next pair n)).symm.trans
        (support_embed pair (Nat.le_succ n) support)
  have hOutput : embed pair (n + 1) (Sum.inl output) = embed pair n output := by
    exact (congrArg (fun f : (stage pair n).Carrier ↪ (stage pair (n + 1)).Carrier =>
      embed pair (n + 1) (f output)) (inclusion_next pair n)).symm.trans
        (embed_inclusion pair (Nat.le_succ n) output)
  exact (congrArg (code pair) (Prod.ext hSupport.symm hOutput.symm)).trans hLimit

end Mettapedia.GSLT.GraphTheory.PartialPair.Completion
