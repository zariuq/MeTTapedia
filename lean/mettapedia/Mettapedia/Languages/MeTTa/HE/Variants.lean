import Mettapedia.Languages.MeTTa.HE.SeveralDeclarations

/-!
# Variants of HE

HE exists in more than one reading: the text of its authors, their implementation, the profiles that
follow either, and edits proposed to them. A **variant** records, for each point where the readings
part, which rule is taken. Every field has the rule of the authors' text as its default, so

* the authors' text is the variant with no edits (`asSpecified`);
* a proposed edit is a variant that overrides one field (`proposed`);
* an earlier state of the dialect, or a reading kept for comparison, is another override
  (`before2024`, `promising`).

A further point of difference becomes a further field with its default, and the variants already
named keep their meaning.

Today one point is recorded: a call with several fitting declarations
(`SeveralDeclarations`).

* `Variant.answers`: the answers of a call under a variant.
* `Variant.OrderFree`: the answers depend only on which declarations fit.
* `proposed_orderFree`, `promising_orderFree`: the two edited variants are order-free.
* `asSpecified_not_orderFree`, `before2024_not_orderFree`: the authors' text is not (the order of
  the declarations decides), and the earlier rule is not either (a repeated declaration repeats
  answers).
* `answers_eq_asSpecified_of_agree`: on a call whose fitting declarations run it one way and
  accept the same results, the specified, the proposed and the promise variants answer alike. An
  edit therefore changes only calls on which the declarations disagree.

Not recorded yet: the point where the authors' implementation departs from their text (it keeps
the first binding of a fitting declaration where the text keeps all).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.Variants

open SeveralDeclarations

/-- The rules for a call with several fitting declarations. -/
inductive DeclarationRule where
  /-- The first fitting declaration decides (the authors' text since July 2024). -/
  | firstFit
  /-- One run for each declaration (the dialect before July 2024). -/
  | perDeclaration
  /-- One run for each way; a result is kept when some declaration accepts it. -/
  | alternatives
  /-- One run for each way; a result is kept when every declaration accepts it. -/
  | promises
  deriving DecidableEq, Repr

/-- **A variant of HE**: the rule taken at each recorded point. The defaults are the authors'
text. -/
structure Variant where
  /-- A call with several fitting declarations. -/
  declarations : DeclarationRule := .firstFit
  deriving DecidableEq, Repr

/-- HE as its authors specify it: no edit. -/
def asSpecified : Variant := {}

/-- HE before July 2024. -/
def before2024 : Variant := { declarations := .perDeclaration }

/-- HE with the edit proposed for a call with several fitting declarations. -/
def proposed : Variant := { declarations := .alternatives }

/-- HE with declarations read as promises, kept for comparison. -/
def promising : Variant := { declarations := .promises }

section Answers

variable {Way Ans : Type} [DecidableEq Way] [DecidableEq Ans]

/-- The answers of a call under a variant. -/
def Variant.answers (v : Variant) (run : Way → Multiset Ans) (ds : List (Fitting Way Ans)) :
    Multiset Ans :=
  match v.declarations with
  | .firstFit => firstFit run ds
  | .perDeclaration => perDeclaration run ds
  | .alternatives => alternatives run ds
  | .promises => promises run ds

end Answers

/-- **Order-free**: the answers depend only on which declarations fit, not on their order or on
repeated declarations. -/
def Variant.OrderFree (v : Variant) : Prop :=
  ∀ (Way Ans : Type) [DecidableEq Way] [DecidableEq Ans] (run : Way → Multiset Ans)
    (ds ds' : List (Fitting Way Ans)), (∀ d, d ∈ ds ↔ d ∈ ds') →
      v.answers run ds = v.answers run ds'

theorem proposed_orderFree : proposed.OrderFree := fun _ _ _ _ run _ _ same =>
  alternatives_congr run same

theorem promising_orderFree : promising.OrderFree := fun _ _ _ _ run _ _ same =>
  promises_congr run same

/-- The authors' text is not order-free: two orders of the same two declarations answer
differently. -/
theorem asSpecified_not_orderFree : ¬ asSpecified.OrderFree := fun orderFree => by
  have same := orderFree Controls.HowRun Controls.Result Controls.pickRun
    [Controls.pickNumber, Controls.pickNat] [Controls.pickNat, Controls.pickNumber]
    (fun d => by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact or_comm)
  have first := Controls.pick_today_depends_on_order.1
  have second := Controls.pick_today_depends_on_order.2
  have clash : ({Controls.Result.zero} : Multiset Controls.Result) = {Controls.Result.z} := by
    rw [← first, ← second]
    exact same
  exact absurd clash (by decide)

/-- The earlier rule is not order-free either: a repeated declaration repeats the answers. -/
theorem before2024_not_orderFree : ¬ before2024.OrderFree := fun orderFree => by
  have same := orderFree Controls.HowRun Controls.Result Controls.gRun
    [Controls.gNumber] [Controls.gNumber, Controls.gNumber]
    (fun d => by simp)
  exact absurd same (by decide)

section Agreement

variable {Way Ans : Type} [DecidableEq Way] [DecidableEq Ans]

/-- **An edit changes only calls on which the declarations disagree.** When the fitting
declarations run the call one way and accept the same results, the proposed and the promise
variants answer as the authors' text does. -/
theorem answers_eq_asSpecified_of_agree (run : Way → Multiset Ans) (d₀ : Fitting Way Ans)
    (rest : List (Fitting Way Ans)) (oneWay : ∀ d ∈ d₀ :: rest, d.way = d₀.way)
    (agree : ∀ d ∈ d₀ :: rest, ∀ a ∈ run d₀.way, d.accepts a = d₀.accepts a) :
    proposed.answers run (d₀ :: rest) = asSpecified.answers run (d₀ :: rest) ∧
      promising.answers run (d₀ :: rest) = asSpecified.answers run (d₀ :: rest) :=
  ⟨alternatives_eq_firstFit_of_agree run d₀ rest oneWay agree,
    promises_eq_firstFit_of_agree run d₀ rest oneWay agree⟩

end Agreement

#print axioms proposed_orderFree
#print axioms asSpecified_not_orderFree
#print axioms before2024_not_orderFree
#print axioms answers_eq_asSpecified_of_agree

end Mettapedia.Languages.MeTTa.HE.Variants
