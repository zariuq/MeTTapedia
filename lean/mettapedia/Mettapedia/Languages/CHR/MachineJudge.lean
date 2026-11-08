import Mettapedia.Languages.CHR.MachineSearchPhase

/-! What a search decision means. A chosen selection is pending, fresh and
passes its guards; an exhausted search rejected every pending selection as
already fired or failing its guards; a fault comes from a pending fresh
selection whose guards fault. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

/-- A selection that a propagating rule already fired from. -/
def Stale (occurrence : At) (history : List CHR.Key) (selection : Environment × List Pick) : Prop :=
  occurrence.body.propagation ∧ (⟨occurrence.rule, ids selection.2⟩ : CHR.Key) ∈ history

theorem judge_some (occurrence : At) (history : List CHR.Key) :
    ∀ (selections : List (Environment × List Pick)) (environment : Environment) (picks : List Pick),
      judge occurrence history selections = .ok (some (environment, picks)) →
      (environment, picks) ∈ selections ∧ ¬ Stale occurrence history (environment, picks) ∧
        guardsEval environment occurrence.body.guards = .ok true
  | [], _, _, decided => by simp [judge] at decided
  | (first, firstPicks) :: rest, environment, picks, decided => by
    by_cases stale : occurrence.body.propagation ∧ (⟨occurrence.rule, ids firstPicks⟩ : CHR.Key) ∈ history
    · simp only [judge, stale] at decided
      obtain ⟨member, fresh, guarded⟩ := judge_some occurrence history rest environment picks decided
      exact ⟨List.mem_cons_of_mem _ member, fresh, guarded⟩
    · simp only [judge, stale, if_false] at decided
      cases guarded : guardsEval first occurrence.body.guards with
      | error reason => simp [guarded] at decided
      | ok holds =>
        cases holds with
        | true =>
          simp only [guarded, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at decided
          obtain ⟨rfl, rfl⟩ := decided
          exact ⟨List.mem_cons_self, stale, guarded⟩
        | false =>
          simp only [guarded] at decided
          obtain ⟨member, fresh, guardedLater⟩ := judge_some occurrence history rest environment picks decided
          exact ⟨List.mem_cons_of_mem _ member, fresh, guardedLater⟩

theorem judge_none (occurrence : At) (history : List CHR.Key) :
    ∀ (selections : List (Environment × List Pick)),
      judge occurrence history selections = .ok none →
      ∀ selection ∈ selections, Stale occurrence history selection ∨
        guardsEval selection.1 occurrence.body.guards = .ok false
  | [], _ => by simp
  | (first, firstPicks) :: rest, decided => by
    intro selection member
    by_cases stale : occurrence.body.propagation ∧ (⟨occurrence.rule, ids firstPicks⟩ : CHR.Key) ∈ history
    · simp only [judge, stale] at decided
      rcases List.mem_cons.mp member with rfl | later
      · exact .inl stale
      · exact judge_none occurrence history rest decided selection later
    · simp only [judge, stale, if_false] at decided
      cases guarded : guardsEval first occurrence.body.guards with
      | error reason => simp [guarded] at decided
      | ok holds =>
        cases holds with
        | true => simp [guarded] at decided
        | false =>
          simp only [guarded] at decided
          rcases List.mem_cons.mp member with rfl | later
          · exact .inr guarded
          · exact judge_none occurrence history rest decided selection later

theorem judge_error (occurrence : At) (history : List CHR.Key) :
    ∀ (selections : List (Environment × List Pick)) (reason : ArithmeticFault),
      judge occurrence history selections = .error reason →
      ∃ selection ∈ selections, ¬ Stale occurrence history selection ∧
        guardsEval selection.1 occurrence.body.guards = .error reason
  | [], _, decided => by simp [judge] at decided
  | (first, firstPicks) :: rest, reason, decided => by
    by_cases stale : occurrence.body.propagation ∧ (⟨occurrence.rule, ids firstPicks⟩ : CHR.Key) ∈ history
    · simp only [judge, stale] at decided
      obtain ⟨selection, member, fresh, guarded⟩ := judge_error occurrence history rest reason decided
      exact ⟨selection, List.mem_cons_of_mem _ member, fresh, guarded⟩
    · simp only [judge, stale, if_false] at decided
      cases guarded : guardsEval first occurrence.body.guards with
      | error actual =>
        simp only [guarded, Except.error.injEq] at decided
        subst decided
        exact ⟨(first, firstPicks), List.mem_cons_self, stale, guarded⟩
      | ok holds =>
        cases holds with
        | true => simp [guarded] at decided
        | false =>
          simp only [guarded] at decided
          obtain ⟨selection, member, fresh, guardedLater⟩ := judge_error occurrence history rest reason decided
          exact ⟨selection, List.mem_cons_of_mem _ member, fresh, guardedLater⟩

#print axioms judge_some
#print axioms judge_none
#print axioms judge_error

end Mettapedia.Languages.CHR.Machine
