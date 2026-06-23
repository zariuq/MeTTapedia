import Mettapedia.UniversalAI.BayesianAgents

namespace Mettapedia.UniversalAI.BayesianAgents

open scoped Classical

namespace CoreCompat

abbrev CoreHistElem : Type := Core.HistElem Action Percept
abbrev CoreHistory : Type := Core.History Action Percept

def histElemToCore : HistElem → CoreHistElem
  | HistElem.act a => Core.HistElem.act a
  | HistElem.per x => Core.HistElem.per x

def histElemFromCore : CoreHistElem → HistElem
  | Core.HistElem.act a => HistElem.act a
  | Core.HistElem.per x => HistElem.per x

@[simp] theorem histElemFromCore_toCore (e : HistElem) :
    histElemFromCore (histElemToCore e) = e := by
  cases e <;> rfl

@[simp] theorem histElemToCore_fromCore (e : CoreHistElem) :
    histElemToCore (histElemFromCore e) = e := by
  cases e <;> rfl

@[simp] theorem histElemFromCore_comp_toCore : histElemFromCore ∘ histElemToCore = id := by
  funext e
  cases e <;> rfl

@[simp] theorem histElemToCore_comp_fromCore : histElemToCore ∘ histElemFromCore = id := by
  funext e
  cases e <;> rfl

def historyToCore : History → CoreHistory :=
  List.map histElemToCore

def historyFromCore : CoreHistory → History :=
  List.map histElemFromCore

@[simp] theorem historyFromCore_toCore (h : History) :
    historyFromCore (historyToCore h) = h := by
  simp [historyToCore, historyFromCore, List.map_map]

@[simp] theorem historyToCore_fromCore (h : CoreHistory) :
    historyToCore (historyFromCore h) = h := by
  simp [historyToCore, historyFromCore, List.map_map]

theorem wellFormed_historyToCore (h : History) :
    Core.History.wellFormed (Action := Action) (Percept := Percept) (historyToCore h) =
      History.wellFormed h := by
  classical
  -- `wellFormed` drops two elements at a time in the `act :: per :: rest` case,
  -- so we use strong induction on length.
  refine Nat.strong_induction_on (p := fun n => ∀ h : History, h.length = n →
      Core.History.wellFormed (Action := Action) (Percept := Percept) (historyToCore h) =
        History.wellFormed h) h.length ?_ h rfl
  intro n ih h hn
  cases h with
  | nil =>
      simp [historyToCore, Core.History.wellFormed, History.wellFormed] at hn ⊢
  | cons hd tl =>
      cases tl with
      | nil =>
          cases hd <;>
            simp [historyToCore, histElemToCore, Core.History.wellFormed, History.wellFormed] at hn ⊢
      | cons hd2 tl2 =>
          cases hd <;> cases hd2 <;>
            simp [historyToCore, histElemToCore, Core.History.wellFormed, History.wellFormed] at hn ⊢
          -- Remaining case: `act :: per :: tl2`
          have hlt : tl2.length < n := by
            have : tl2.length < tl2.length + 2 :=
              Nat.lt_succ_of_lt (Nat.lt_succ_self tl2.length)
            exact Nat.lt_of_lt_of_eq this hn
          -- Apply IH to `tl2`.
          have ht2 :
              Core.History.wellFormed (Action := Action) (Percept := Percept) (historyToCore tl2) =
                History.wellFormed tl2 := by
            exact ih tl2.length hlt tl2 rfl
          simpa [historyToCore] using ht2

theorem wellFormed_historyFromCore (h : CoreHistory) :
    History.wellFormed (historyFromCore h) =
      Core.History.wellFormed (Action := Action) (Percept := Percept) h := by
  -- use `historyToCore_fromCore` and `wellFormed_historyToCore`
  have := wellFormed_historyToCore (h := historyFromCore h)
  -- `historyToCore (historyFromCore h) = h`
  simpa [historyToCore_fromCore] using this.symm

def environmentToCore (μ : Environment) : Core.Environment Action Percept where
  prob := fun h x => μ.prob (historyFromCore h) x
  prob_le_one := fun h hw => by
    have hwOld : History.wellFormed (historyFromCore h) = true := by
      have hwCore : Core.History.wellFormed (Action := Action) (Percept := Percept) h = true := by
        simpa using hw
      -- rewrite wellFormed along the conversion
      simpa [wellFormed_historyFromCore] using hwCore
    have htsum : (∑' x : Percept, μ.prob (historyFromCore h) x) ≤ 1 :=
      μ.prob_le_one (historyFromCore h) hwOld
    simpa [tsum_fintype] using htsum

def agentToCore (π : Agent) : Core.Agent Action Percept where
  policy := fun h a => π.policy (historyFromCore h) a
  policy_sum_one := fun h hw => by
    have hwOld : History.wellFormed (historyFromCore h) = true := by
      have hwCore : Core.History.wellFormed (Action := Action) (Percept := Percept) h = true := by
        simpa using hw
      simpa [wellFormed_historyFromCore] using hwCore
    have htsum : (∑' a : Action, π.policy (historyFromCore h) a) = 1 :=
      π.policy_sum_one (historyFromCore h) hwOld
    simpa [tsum_fintype] using htsum

end CoreCompat

end Mettapedia.UniversalAI.BayesianAgents
