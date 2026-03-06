import Algorithms.MeTTa.Simple.Backend.SpaceIndex

namespace Algorithms.MeTTa.Simple.Backend.SpaceIndexContracts

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple.Backend.SpaceIndex

theorem candidateSelfFacts_fvar
    (v : View) (x : String) :
    candidateSelfFacts v (.fvar x) = v.selfFacts := rfl

theorem candidateSelfFacts_comma
    (v : View) (lhs rhs : Pattern) :
    candidateSelfFacts v (.apply "," [lhs, rhs]) = v.selfFacts := rfl

theorem candidateSelfFacts_dollar_head
    (v : View) (ctor : String) (args : List Pattern)
    (hStarts : ctor.startsWith "$" = true)
    (hNotComma : ctor ≠ ",") :
    candidateSelfFacts v (.apply ctor args) = v.selfFacts := by
  cases args with
  | nil =>
      simp [candidateSelfFacts, hStarts]
  | cons a as =>
      cases as with
      | nil =>
          simp [candidateSelfFacts, hStarts]
      | cons b bs =>
          simp [candidateSelfFacts, hStarts, hNotComma]

theorem candidateSelfFacts_apply_structural
    (v : View) (ctor : String) (args : List Pattern)
    (hStarts : ctor.startsWith "$" = false)
    (hNotComma : ctor ≠ ",") :
    candidateSelfFacts v (.apply ctor args) =
      let headFacts := headFactsFor v ctor args.length
      if headFacts.isEmpty then v.selfFacts else headFacts ++ v.nonApplyFacts := by
  simp [candidateSelfFacts, hStarts, hNotComma, headFactsFor]

theorem candidateSelfFacts_nonApply
    (v : View) (pat : Pattern)
    (hNonApply : ∀ ctor args, pat ≠ .apply ctor args) :
    candidateSelfFacts v pat = v.selfFacts := by
  cases pat <;> simp [candidateSelfFacts]
  case apply ctor args =>
    exfalso
    exact hNonApply ctor args rfl

theorem no_false_negative_fvar
    (v : View) (x : String) (fact : Pattern)
    (hMem : fact ∈ v.selfFacts) :
    fact ∈ candidateSelfFacts v (.fvar x) := by
  simpa [candidateSelfFacts_fvar] using hMem

theorem no_false_negative_comma
    (v : View) (lhs rhs fact : Pattern)
    (hMem : fact ∈ v.selfFacts) :
    fact ∈ candidateSelfFacts v (.apply "," [lhs, rhs]) := by
  simpa [candidateSelfFacts_comma] using hMem

theorem no_false_negative_dollar_head
    (v : View) (ctor : String) (args : List Pattern) (fact : Pattern)
    (hStarts : ctor.startsWith "$" = true)
    (hNotComma : ctor ≠ ",")
    (hMem : fact ∈ v.selfFacts) :
    fact ∈ candidateSelfFacts v (.apply ctor args) := by
  simpa [candidateSelfFacts_dollar_head, hStarts, hNotComma] using hMem

theorem no_false_negative_nonApply
    (v : View) (pat fact : Pattern)
    (hNonApply : ∀ ctor args, pat ≠ .apply ctor args)
    (hMem : fact ∈ v.selfFacts) :
    fact ∈ candidateSelfFacts v pat := by
  simpa [candidateSelfFacts_nonApply, hNonApply] using hMem

theorem no_false_negative_apply_head_bucket
    (v : View) (ctor : String) (args : List Pattern) (fact : Pattern)
    (hStarts : ctor.startsWith "$" = false)
    (hNotComma : ctor ≠ ",")
    (hHead : fact ∈ headFactsFor v ctor args.length) :
    fact ∈ candidateSelfFacts v (.apply ctor args) := by
  have hHeadNonempty : (headFactsFor v ctor args.length).isEmpty = false := by
    cases hE : (headFactsFor v ctor args.length).isEmpty with
    | true =>
        have : headFactsFor v ctor args.length = [] := (List.isEmpty_iff.mp hE)
        simp [this] at hHead
    | false =>
        simp
  simp [candidateSelfFacts_apply_structural, hStarts, hNotComma, hHeadNonempty]
  exact Or.inl hHead

theorem no_false_negative_apply_fallback
    (v : View) (ctor : String) (args : List Pattern) (fact : Pattern)
    (hStarts : ctor.startsWith "$" = false)
    (hNotComma : ctor ≠ ",")
    (hHeadEmpty : headFactsFor v ctor args.length = [])
    (hMem : fact ∈ v.selfFacts) :
    fact ∈ candidateSelfFacts v (.apply ctor args) := by
  simp [candidateSelfFacts_apply_structural, hStarts, hNotComma, hHeadEmpty] at hMem ⊢
  exact hMem

theorem candidateSelfTypeEntries_fvar
    (v : View) (x : String) :
    candidateSelfTypeEntries v (.fvar x) = v.typeFacts := rfl

theorem candidateSelfTypeEntries_bvar
    (v : View) (n : Nat) :
    candidateSelfTypeEntries v (.bvar n) = v.typeFacts := rfl

theorem candidateSelfTypeEntries_nonApply
    (v : View) (x : Pattern)
    (hNonApply : ∀ ctor args, x ≠ .apply ctor args) :
    candidateSelfTypeEntries v x = v.typeFacts := by
  cases x <;> simp [candidateSelfTypeEntries]
  case apply ctor args =>
    exfalso
    exact hNonApply ctor args rfl

theorem no_false_negative_type_nonApply
    (v : View) (x lhs ty : Pattern)
    (hNonApply : ∀ ctor args, x ≠ .apply ctor args)
    (hMem : (lhs, ty) ∈ v.typeFacts) :
    (lhs, ty) ∈ candidateSelfTypeEntries v x := by
  simpa [candidateSelfTypeEntries_nonApply, hNonApply] using hMem

theorem candidateSelfTypeEntries_apply_structural
    (v : View) (ctor : String) (args : List Pattern) :
    candidateSelfTypeEntries v (.apply ctor args) =
      let indexed := typeHeadFactsFor v ctor args.length
      if indexed.isEmpty then v.typeFacts else indexed ++ v.typeFactsNonApplyHead := by
  simp [candidateSelfTypeEntries, typeHeadFactsFor]

theorem no_false_negative_type_apply_head_bucket
    (v : View) (ctor : String) (args : List Pattern) (lhs ty : Pattern)
    (hHead : (lhs, ty) ∈ typeHeadFactsFor v ctor args.length) :
    (lhs, ty) ∈ candidateSelfTypeEntries v (.apply ctor args) := by
  have hHeadNonempty : (typeHeadFactsFor v ctor args.length).isEmpty = false := by
    cases hE : (typeHeadFactsFor v ctor args.length).isEmpty with
    | true =>
        have : typeHeadFactsFor v ctor args.length = [] := (List.isEmpty_iff.mp hE)
        simp [this] at hHead
    | false =>
        simp
  simp [candidateSelfTypeEntries_apply_structural, hHeadNonempty]
  exact Or.inl hHead

theorem no_false_negative_type_apply_fallback
    (v : View) (ctor : String) (args : List Pattern) (lhs ty : Pattern)
    (hHeadEmpty : typeHeadFactsFor v ctor args.length = [])
    (hMem : (lhs, ty) ∈ v.typeFacts) :
    (lhs, ty) ∈ candidateSelfTypeEntries v (.apply ctor args) := by
  simp [candidateSelfTypeEntries_apply_structural, hHeadEmpty] at hMem ⊢
  exact hMem

end Algorithms.MeTTa.Simple.Backend.SpaceIndexContracts
