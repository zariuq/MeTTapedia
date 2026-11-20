import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Tables
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Firings

/-!
# Tables of rows with unknowns: one row former per function, and range restriction

Over the rows with unknowns of the presentation (`Presentation.Schematic.Tm`: symbols, names,
application and code), a function is named by a symbol `f`, and its table's row at arguments
`t₁ … tₙ` and value `v` is the symbol applied to them, `f t₁ … tₙ v` (`rows`, `groundRow`): one row
former per function. Rows of the store that are not table rows start with other symbols.

## Range restriction

A rule with conditions **binds** an unknown (`Binds`) when its rule binds it by matching or the value
pattern of one of its conditions mentions it. It is **range restricted** (`RangeRestrictedWith`) when
every unknown it tells, asks or makes is bound so; its conditions are **well moded** (`WellModed`)
when every argument of a condition uses only unknowns bound by matching or by the value of an earlier
condition.

* `rangeRestricted_tableRule_iff`: **the table read is range restricted exactly when every unknown the
  rule tells, asks or makes is bound by matching or occurs in a condition**, value or argument.
* `rangeRestricted_tableRule`: so a range-restricted rule with conditions has a range-restricted table
  read; with no collect query and only equation checks it is in the presentation's fragment
  (`fragment_tableRule`), where the presentation (`Schematic.generated_possibility`) and the context
  rule (`Schematic.fires_beside`) hold for the table reads. The converse fails for an unknown that only
  an argument mentions (`Evaluation.argumentOnly`): the table read enumerates the table there.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open Presentation.Schematic (Tm SRule RowFunction RowConstant rowSig args2 toTerm Bound written
  RangeRestricted RangeRestrictedPositive isGuard mem_vars_app_cases mem_vars_head mem_vars_tail
  mem_vars_var not_mem_vars_const applyTerm_toTerm)

/-! ## Spines -/

/-- **A term applied to arguments**, from the left: `h t₁ … tₙ`. -/
def spine : Tm → List Tm → Tm
  | h, [] => h
  | h, t :: ts => spine (Term.app RowFunction.app (args2 h t)) ts

/-- **A ground row applied to ground arguments.** -/
def groundSpine : Expr → List Expr → Expr
  | h, [] => h
  | h, a :: as => groundSpine (.app h a) as

theorem toTerm_groundSpine : ∀ (h : Expr) (as : List Expr),
    toTerm (groundSpine h as) = spine (toTerm h) (as.map toTerm)
  | _, [] => rfl
  | h, a :: as => toTerm_groundSpine (.app h a) as

/-- **The instance of a spine** is the ground spine of the instances. -/
theorem inst_spine (θ : ℕ → Expr) : ∀ (h : Tm) (ts : List Tm),
    Presentation.Schematic.inst θ (spine h ts) = groundSpine (Presentation.Schematic.inst θ h)
      (ts.map (Presentation.Schematic.inst θ))
  | _, [] => rfl
  | h, t :: ts => inst_spine θ (Term.app RowFunction.app (args2 h t)) ts

/-- **A ground spine determines its head and its arguments**, for arguments of one length. -/
theorem groundSpine_inj : ∀ {h h' : Expr} {xs ys : List Expr}, xs.length = ys.length →
    groundSpine h xs = groundSpine h' ys → h = h' ∧ xs = ys
  | _, _, [], [], _, same => ⟨same, rfl⟩
  | _, _, [], _ :: _, lengths, _ => by simp at lengths
  | _, _, _ :: _, [], lengths, _ => by simp at lengths
  | _, _, x :: xs, y :: ys, lengths, same => by
      obtain ⟨heads, rest⟩ := groundSpine_inj (Nat.succ.inj lengths) same
      obtain ⟨rfl, rfl⟩ := Expr.app.inj heads
      exact ⟨rfl, by rw [rest]⟩

/-- **The leftmost symbol of a row.** -/
def spineHead : Expr → Expr
  | .app f _ => spineHead f
  | e => e

theorem spineHead_groundSpine : ∀ (h : Expr) (xs : List Expr), spineHead (groundSpine h xs) = spineHead h
  | _, [] => rfl
  | h, x :: xs => (spineHead_groundSpine (.app h x) xs).trans rfl

/-- **The unknowns of a spine** are those of its head and of its arguments. -/
theorem mem_vars_spine {x : ℕ} : ∀ (h : Tm) (ts : List Tm),
    x ∈ (spine h ts).freeVars ↔ x ∈ h.freeVars ∨ ∃ t ∈ ts, x ∈ t.freeVars
  | h, [] => by simp [spine]
  | h, t :: ts => by
      rw [spine, mem_vars_spine _ ts]
      constructor
      · rintro (inApp | ⟨u, member, inU⟩)
        · rcases mem_vars_app_cases inApp with inH | inT
          · exact .inl inH
          · exact .inr ⟨t, List.mem_cons_self, inT⟩
        · exact .inr ⟨u, List.mem_cons_of_mem _ member, inU⟩
      · rintro (inH | ⟨u, member, inU⟩)
        · exact .inl (mem_vars_head inH)
        · rcases List.mem_cons.mp member with rfl | later
          · exact .inl (mem_vars_tail inU)
          · exact .inr ⟨u, later, inU⟩

/-! ## The tables -/

/-- **The tables of rows with unknowns**: the row of function `f` at arguments `t₁ … tₙ` and value `v`
is `f t₁ … tₙ v`. -/
def rows : Tabulation ℕ Tm := ⟨fun f args v => spine (.const (.sym f)) (args ++ [v])⟩

/-- **The ground row** of function `f` at ground arguments and a ground value. -/
def groundRow (f : ℕ) (args : List Expr) (v : Expr) : Expr := groundSpine (.sym f) (args ++ [v])

theorem toTerm_groundRow (f : ℕ) (args : List Expr) (v : Expr) :
    toTerm (groundRow f args v) = rows.row f (args.map toTerm) (toTerm v) := by
  rw [groundRow, toTerm_groundSpine, List.map_append]
  rfl

/-- **Ground rows are fixed points**: every substitution fixes them. -/
theorem fixed_toTerm (e : Expr) : Fixed Presentation.Schematic.A (toTerm e) := fun σ => applyTerm_toTerm σ e

/-- **The ground graph of an interpretation on ground rows**, as terms. -/
def groundGraph (I : Interpretation ℕ Expr) : Set Tm :=
  {t | ∃ f args v, I f args = some v ∧ t = toTerm (groundRow f args v)}

theorem fixed_groundGraph (I : Interpretation ℕ Expr) : ∀ t ∈ groundGraph I, Fixed Presentation.Schematic.A t := by
  rintro t ⟨f, args, v, -, rfl⟩
  exact fixed_toTerm _

/-- The unknowns of a call row are those of its arguments and of its value. -/
theorem mem_vars_callRow {x : ℕ} (c : Condition ℕ Tm) :
    x ∈ (callRow rows c).freeVars ↔ (∃ t ∈ c.arguments, x ∈ t.freeVars) ∨ x ∈ c.value.freeVars := by
  show x ∈ (spine (.const (.sym c.name)) (c.arguments ++ [c.value])).freeVars ↔ _
  rw [mem_vars_spine]
  constructor
  · rintro (inHead | ⟨t, member, inT⟩)
    · exact absurd inHead not_mem_vars_const
    · rcases List.mem_append.mp member with argument | value
      · exact .inl ⟨t, argument, inT⟩
      · rw [List.mem_singleton.mp value] at inT
        exact .inr inT
  · rintro (⟨t, member, inT⟩ | inValue)
    · exact .inr ⟨t, List.mem_append_left _ member, inT⟩
    · exact .inr ⟨c.value, List.mem_append_right _ (List.mem_singleton_self _), inValue⟩

/-! ## Range restriction -/

namespace RuleWithCondition

variable (ρ : RuleWithCondition ℕ Tm)

/-- **The unknowns a rule with conditions binds**: by matching, or as the value of a condition. -/
def Binds (x : ℕ) : Prop := Bound ρ.rule x ∨ ∃ c ∈ ρ.conditions, x ∈ c.value.freeVars

/-- **A range-restricted rule with conditions**: every unknown it tells, asks or makes is bound by
matching or by the value of a condition. -/
def RangeRestrictedWith : Prop := ∀ t ∈ written ρ.rule, ∀ x ∈ t.freeVars, ρ.Binds x

/-- The conditions are well moded after the given bound terms. -/
def WellModedAfter : List Tm → List (Condition ℕ Tm) → Prop
  | _, [] => True
  | bound, c :: cs => (∀ t ∈ c.arguments, ∀ x ∈ t.freeVars, ∃ u ∈ bound, x ∈ u.freeVars) ∧
      WellModedAfter (bound ++ [c.value]) cs

/-- **Well-moded conditions**: each argument uses only unknowns of the take and read patterns or of
the value patterns of earlier conditions. -/
def WellModed : Prop := WellModedAfter (ρ.rule.body.take ++ ρ.rule.body.read) ρ.conditions

instance (x : ℕ) : Decidable (ρ.Binds x) := by
  unfold Binds
  infer_instance

instance : Decidable ρ.RangeRestrictedWith := by
  unfold RangeRestrictedWith
  infer_instance

instance decidableWellModedAfter : ∀ (bound : List Tm) (cs : List (Condition ℕ Tm)),
    Decidable (WellModedAfter bound cs)
  | _, [] => isTrue trivial
  | bound, c :: cs =>
      have : Decidable (WellModedAfter (bound ++ [c.value]) cs) := decidableWellModedAfter _ cs
      inferInstanceAs (Decidable (_ ∧ _))

instance : Decidable ρ.WellModed := decidableWellModedAfter _ _

/-- The table read writes what the rule writes. -/
theorem written_tableRule : written (ρ.tableRule rows) = written ρ.rule := rfl

/-- **What the table read binds**: what the rule binds by matching, and the unknowns of the conditions,
in arguments and values. -/
theorem bound_tableRule_iff (x : ℕ) :
    Bound (ρ.tableRule rows) x ↔ Bound ρ.rule x ∨
      ∃ c ∈ ρ.conditions, (∃ t ∈ c.arguments, x ∈ t.freeVars) ∨ x ∈ c.value.freeVars := by
  constructor
  · rintro ⟨t, member, inT⟩
    rcases List.mem_append.mp member with take | read
    · exact .inl ⟨t, List.mem_append_left _ take, inT⟩
    · rw [tableRule_read] at read
      rcases List.mem_append.mp read with read | call
      · exact .inl ⟨t, List.mem_append_right _ read, inT⟩
      · obtain ⟨c, inC, rfl⟩ := List.mem_map.mp call
        exact .inr ⟨c, inC, (mem_vars_callRow c).mp inT⟩
  · rintro (⟨t, member, inT⟩ | ⟨c, inC, inCall⟩)
    · rcases List.mem_append.mp member with take | read
      · exact ⟨t, List.mem_append_left _ take, inT⟩
      · refine ⟨t, List.mem_append_right _ ?_, inT⟩
        rw [tableRule_read]
        exact List.mem_append_left _ read
    · refine ⟨callRow rows c, List.mem_append_right _ ?_, (mem_vars_callRow c).mpr inCall⟩
      rw [tableRule_read]
      exact List.mem_append_right _ (List.mem_map_of_mem inC)

/-- **The table read is range restricted exactly when every unknown the rule tells, asks or makes is
bound by matching or occurs in a condition.** -/
theorem rangeRestricted_tableRule_iff :
    RangeRestricted (ρ.tableRule rows) ↔ ∀ t ∈ written ρ.rule, ∀ x ∈ t.freeVars, Bound ρ.rule x ∨
      ∃ c ∈ ρ.conditions, (∃ t ∈ c.arguments, x ∈ t.freeVars) ∨ x ∈ c.value.freeVars := by
  unfold RangeRestricted
  rw [written_tableRule]
  exact forall₂_congr fun t _ => forall₂_congr fun x _ => bound_tableRule_iff ρ x

/-- **A range-restricted rule with conditions has a range-restricted table read.** -/
theorem rangeRestricted_tableRule (restricted : ρ.RangeRestrictedWith) :
    RangeRestricted (ρ.tableRule rows) := by
  rw [rangeRestricted_tableRule_iff]
  intro t member x inT
  rcases restricted t member x inT with bound | ⟨c, inC, inValue⟩
  · exact .inl bound
  · exact .inr ⟨c, inC, .inr inValue⟩

/-- **The table read is in the presentation's fragment** when the rule has no collect query, only equation
checks, and is range restricted with its conditions. -/
theorem fragment_tableRule (noCollect : ρ.rule.collect = []) (guards : ρ.rule.body.checks.all isGuard = true)
    (restricted : ρ.RangeRestrictedWith) : RangeRestrictedPositive (ρ.tableRule rows) :=
  ⟨noCollect, guards, ρ.rangeRestricted_tableRule restricted⟩

end RuleWithCondition

#print axioms toTerm_groundSpine
#print axioms inst_spine
#print axioms groundSpine_inj
#print axioms spineHead_groundSpine
#print axioms mem_vars_spine
#print axioms toTerm_groundRow
#print axioms fixed_groundGraph
#print axioms mem_vars_callRow
#print axioms RuleWithCondition.bound_tableRule_iff
#print axioms RuleWithCondition.rangeRestricted_tableRule_iff
#print axioms RuleWithCondition.rangeRestricted_tableRule
#print axioms RuleWithCondition.fragment_tableRule

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions
