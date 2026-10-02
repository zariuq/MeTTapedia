import Mettapedia.Languages.VibeITP.Presentation.Meaning
import Mettapedia.Languages.VibeITP.Presentation.TermShape

/-!
# Well-formedness preservation by successful kernel operations

Successful shifting, bound-variable substitution and second-order
instantiation preserve the kernel's word bounds and declared application
arities. Argument traversals preserve both well-formedness and list length.
The substitution profile supplies exactly as many well-formed arguments as
the specified argument count, so its default lookup branch is never used.
The structural `TermShape` profile is preserved as well, including on terms
whose bound-variable indices or literal lengths exceed formation bounds.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.Languages.VibeITP.Spec

mutual
theorem shift_wellFormed (sig : Sig) (amount cutoff : Nat) (t u : Term)
    (ht : WellFormed sig t = true) (hop : shift sig amount cutoff t = some u) :
    WellFormed sig u = true := by
  cases t with
  | bvar b =>
      simp only [shift] at hop
      split at hop
      · simp only [Option.some.injEq] at hop
        subst u
        exact ht
      · split at hop
        · rename_i hbound
          simp only [Option.some.injEq] at hop
          subst u
          simpa only [WellFormed, decide_eq_true_eq] using hbound
        · simp at hop
  | lit bytes =>
      simp only [shift, Option.some.injEq] at hop
      subst u
      exact ht
  | app s args =>
      simp only [shift] at hop
      split at hop
      · simp only [Option.some.injEq] at hop
        subst u
        exact ht
      · rw [shiftArgs_eq] at hop
        obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hop
        cases hs : sig s with
        | none => simp [WellFormed, hs] at ht
        | some info =>
            have hw : args.length = info.arity ∧ WellFormedList sig args = true := by
              simpa only [WellFormed, hs, Bool.and_eq_true, decide_eq_true_eq] using ht
            have hout := shiftList_wellFormed_length sig amount cutoff
              ((bindersOf sig s).drop 0) args us hw.2 hus
            simpa only [WellFormed, hs, Bool.and_eq_true, decide_eq_true_eq] using
              And.intro (hout.2.trans hw.1) hout.1
termination_by sizeOf t

theorem shiftList_wellFormed_length (sig : Sig) (amount cutoff : Nat)
    (bs : List Nat) (ts us : List Term) (hts : WellFormedList sig ts = true)
    (hop : shiftList sig amount cutoff bs ts = some us) :
    WellFormedList sig us = true ∧ us.length = ts.length := by
  cases ts with
  | nil =>
      simp only [shiftList, Option.some.injEq] at hop
      subst us
      exact ⟨rfl, rfl⟩
  | cons t ts =>
      have hw : WellFormed sig t = true ∧ WellFormedList sig ts = true := by
        simpa only [WellFormedList, Bool.and_eq_true] using hts
      simp only [shiftList] at hop
      split at hop
      · split at hop
        · rename_i u us' hu hus
          simp only [Option.some.injEq] at hop
          subst us
          have hwu := shift_wellFormed sig amount (cutoff + bs.headD 0) t u hw.1 hu
          have hws := shiftList_wellFormed_length sig amount cutoff bs.tail ts us' hw.2 hus
          exact ⟨by simpa only [WellFormedList, Bool.and_eq_true] using And.intro hwu hws.1,
            by simpa only [List.length_cons] using congrArg Nat.succ hws.2⟩
        · simp at hop
      · simp at hop
termination_by sizeOf ts
end

theorem shiftList_wellFormed (sig : Sig) (amount cutoff : Nat)
    (bs : List Nat) (ts us : List Term) (hts : WellFormedList sig ts = true)
    (hop : shiftList sig amount cutoff bs ts = some us) :
    WellFormedList sig us = true :=
  (shiftList_wellFormed_length sig amount cutoff bs ts us hts hop).1

private theorem operations_getD_wellFormed (sig : Sig) :
    ∀ (args : List Term) (i : Nat), WellFormedList sig args = true →
      i < args.length → WellFormed sig (args.getD i (.bvar 0)) = true
  | [], _, _, hi => by simp at hi
  | a :: as, 0, hw, _ => by
      simp only [WellFormedList, Bool.and_eq_true] at hw
      simpa only [List.getD_cons_zero] using hw.1
  | a :: as, i + 1, hw, hi => by
      simp only [WellFormedList, Bool.and_eq_true] at hw
      simp only [List.getD_cons_succ]
      exact operations_getD_wellFormed sig as i hw.2 (by simpa using hi)

mutual
theorem subst_wellFormed (sig : Sig) (numArgs : Nat) (args : List Term)
    (offset : Nat) (t u : Term) (hlen : args.length = numArgs)
    (hargs : WellFormedList sig args = true) (ht : WellFormed sig t = true)
    (hop : substGo sig numArgs args offset t = some u) : WellFormed sig u = true := by
  cases t with
  | bvar b =>
      simp only [substGo] at hop
      split at hop
      · simp only [Option.some.injEq] at hop
        subst u
        exact ht
      · split at hop
        · rename_i hindex
          have hi : numArgs - 1 - (b - offset) < args.length := by omega
          exact shift_wellFormed sig offset 0 _ u
            (operations_getD_wellFormed sig args _ hargs hi) hop
        · split at hop
          · rename_i hbound
            simp only [Option.some.injEq] at hop
            subst u
            simpa only [WellFormed, decide_eq_true_eq] using hbound
          · simp at hop
  | lit bytes =>
      simp only [substGo, Option.some.injEq] at hop
      subst u
      exact ht
  | app s ts =>
      simp only [substGo] at hop
      split at hop
      · simp only [Option.some.injEq] at hop
        subst u
        exact ht
      · rw [substGoArgs_eq] at hop
        obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hop
        cases hs : sig s with
        | none => simp [WellFormed, hs] at ht
        | some info =>
            have hw : ts.length = info.arity ∧ WellFormedList sig ts = true := by
              simpa only [WellFormed, hs, Bool.and_eq_true, decide_eq_true_eq] using ht
            have hout := substList_wellFormed_length sig numArgs args offset
              ((bindersOf sig s).drop 0) ts us hlen hargs hw.2 hus
            simpa only [WellFormed, hs, Bool.and_eq_true, decide_eq_true_eq] using
              And.intro (hout.2.trans hw.1) hout.1
termination_by sizeOf t

theorem substList_wellFormed_length (sig : Sig) (numArgs : Nat) (args : List Term)
    (offset : Nat) (bs : List Nat) (ts us : List Term) (hlen : args.length = numArgs)
    (hargs : WellFormedList sig args = true) (hts : WellFormedList sig ts = true)
    (hop : substList sig numArgs args offset bs ts = some us) :
    WellFormedList sig us = true ∧ us.length = ts.length := by
  cases ts with
  | nil =>
      simp only [substList, Option.some.injEq] at hop
      subst us
      exact ⟨rfl, rfl⟩
  | cons t ts =>
      have hw : WellFormed sig t = true ∧ WellFormedList sig ts = true := by
        simpa only [WellFormedList, Bool.and_eq_true] using hts
      simp only [substList] at hop
      split at hop
      · split at hop
        · rename_i u us' hu hus
          simp only [Option.some.injEq] at hop
          subst us
          have hwu := subst_wellFormed sig numArgs args (offset + bs.headD 0) t u
            hlen hargs hw.1 hu
          have hws := substList_wellFormed_length sig numArgs args offset bs.tail ts us'
            hlen hargs hw.2 hus
          exact ⟨by simpa only [WellFormedList, Bool.and_eq_true] using And.intro hwu hws.1,
            by simpa only [List.length_cons] using congrArg Nat.succ hws.2⟩
        · simp at hop
      · simp at hop
termination_by sizeOf ts
end

theorem substList_wellFormed (sig : Sig) (numArgs : Nat) (args : List Term)
    (offset : Nat) (bs : List Nat) (ts us : List Term) (hlen : args.length = numArgs)
    (hargs : WellFormedList sig args = true) (hts : WellFormedList sig ts = true)
    (hop : substList sig numArgs args offset bs ts = some us) :
    WellFormedList sig us = true :=
  (substList_wellFormed_length sig numArgs args offset bs ts us hlen hargs hts hop).1

theorem substBVars_wellFormed (sig : Sig) (numArgs : Nat) (args : List Term)
    (body result : Term) (offset : Nat) (hlen : args.length = numArgs)
    (hargs : WellFormedList sig args = true) (hbody : WellFormed sig body = true)
    (hop : substBVars sig numArgs args body offset = some result) :
    WellFormed sig result = true := by
  simp only [substBVars] at hop
  split at hop
  · simp only [Option.some.injEq] at hop
    subst result
    exact hbody
  · exact subst_wellFormed sig numArgs args offset body result hlen hargs hbody hop

mutual
theorem inst_wellFormed (sig : Sig) (F : SymId) (arity : Nat) (value : Term)
    (offset : Nat) (t u : Term) (hvalue : WellFormed sig value = true)
    (hF : IsFvarOf sig F arity) (ht : WellFormed sig t = true)
    (hop : instGo sig F arity value offset t = some u) : WellFormed sig u = true := by
  cases t with
  | bvar b =>
      simp only [instGo, Option.some.injEq] at hop
      subst u
      exact ht
  | lit bytes =>
      simp only [instGo, Option.some.injEq] at hop
      subst u
      exact ht
  | app s ts =>
      simp only [instGo] at hop
      split at hop
      · simp only [Option.some.injEq] at hop
        subst u
        exact ht
      · cases hs : sig s with
        | none => simp [WellFormed, hs] at ht
        | some info =>
            have hw : ts.length = info.arity ∧ WellFormedList sig ts = true := by
              simpa only [WellFormed, hs, Bool.and_eq_true, decide_eq_true_eq] using ht
            rw [instArgs_eq] at hop
            simp only [List.drop_zero] at hop
            cases hus : instList sig F arity value offset (bindersOf sig s) ts with
            | none => simp [hus] at hop
            | some us =>
                have hout := instList_wellFormed_length sig F arity value offset
                  (bindersOf sig s) ts us hvalue hF hw.2 hus
                by_cases hsid : s = F
                · subst s
                  simp only [hus] at hop
                  cases hvop : shift sig offset arity value with
                  | none => simp [hvop] at hop
                  | some value' =>
                      simp only [hvop] at hop
                      have hv := shift_wellFormed sig offset arity value value' hvalue hvop
                      have harity : info.arity = arity := by
                        simpa only [symArity, hs] using hF.2.2
                      exact substBVars_wellFormed sig arity us value' u 0
                        (hout.2.trans (hw.1.trans harity)) hout.1 hv hop
                · simp only [hus, if_neg hsid, Option.some.injEq] at hop
                  subst u
                  simpa only [WellFormed, hs, Bool.and_eq_true, decide_eq_true_eq] using
                    And.intro (hout.2.trans hw.1) hout.1
termination_by sizeOf t

theorem instList_wellFormed_length (sig : Sig) (F : SymId) (arity : Nat) (value : Term)
    (offset : Nat) (bs : List Nat) (ts us : List Term) (hvalue : WellFormed sig value = true)
    (hF : IsFvarOf sig F arity) (hts : WellFormedList sig ts = true)
    (hop : instList sig F arity value offset bs ts = some us) :
    WellFormedList sig us = true ∧ us.length = ts.length := by
  cases ts with
  | nil =>
      simp only [instList, Option.some.injEq] at hop
      subst us
      exact ⟨rfl, rfl⟩
  | cons t ts =>
      have hw : WellFormed sig t = true ∧ WellFormedList sig ts = true := by
        simpa only [WellFormedList, Bool.and_eq_true] using hts
      simp only [instList] at hop
      split at hop
      · split at hop
        · rename_i u us' hu hus
          simp only [Option.some.injEq] at hop
          subst us
          have hwu := inst_wellFormed sig F arity value (offset + bs.headD 0) t u
            hvalue hF hw.1 hu
          have hws := instList_wellFormed_length sig F arity value offset bs.tail ts us'
            hvalue hF hw.2 hus
          exact ⟨by simpa only [WellFormedList, Bool.and_eq_true] using And.intro hwu hws.1,
            by simpa only [List.length_cons] using congrArg Nat.succ hws.2⟩
        · simp at hop
      · simp at hop
termination_by sizeOf ts
end

theorem instList_wellFormed (sig : Sig) (F : SymId) (arity : Nat) (value : Term)
    (offset : Nat) (bs : List Nat) (ts us : List Term) (hvalue : WellFormed sig value = true)
    (hF : IsFvarOf sig F arity) (hts : WellFormedList sig ts = true)
    (hop : instList sig F arity value offset bs ts = some us) :
    WellFormedList sig us = true :=
  (instList_wellFormed_length sig F arity value offset bs ts us hvalue hF hts hop).1

mutual
theorem shift_termShape (sig : Sig) (amount cutoff : Nat) (t u : Term)
    (ht : TermShape sig t) (hop : shift sig amount cutoff t = some u) : TermShape sig u := by
  cases t with
  | bvar b =>
      simp only [shift] at hop
      split at hop
      · simp only [Option.some.injEq] at hop
        subst u
        exact ht
      · split at hop
        · simp only [Option.some.injEq] at hop
          subst u
          exact .bvar _
        · simp at hop
  | lit bytes =>
      simp only [shift, Option.some.injEq] at hop
      subst u
      exact ht
  | app s args =>
      simp only [shift] at hop
      split at hop
      · simp only [Option.some.injEq] at hop
        subst u
        exact ht
      · rw [shiftArgs_eq] at hop
        obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hop
        obtain ⟨info, hs, hlen, hargs⟩ := TermShape.app_iff.mp ht
        have hout := shiftList_termShape_length sig amount cutoff
          ((bindersOf sig s).drop 0) args us hargs hus
        exact .app hs (hout.2.trans hlen) hout.1
termination_by sizeOf t

theorem shiftList_termShape_length (sig : Sig) (amount cutoff : Nat)
    (bs : List Nat) (ts us : List Term) (hts : TermShapeList sig ts)
    (hop : shiftList sig amount cutoff bs ts = some us) :
    TermShapeList sig us ∧ us.length = ts.length := by
  cases ts with
  | nil =>
      simp only [shiftList, Option.some.injEq] at hop
      subst us
      exact ⟨.nil, rfl⟩
  | cons t ts =>
      obtain ⟨ht, hts⟩ := TermShapeList.cons_iff.mp hts
      simp only [shiftList] at hop
      split at hop
      · split at hop
        · rename_i u us' hu hus
          simp only [Option.some.injEq] at hop
          subst us
          have hwu := shift_termShape sig amount (cutoff + bs.headD 0) t u ht hu
          have hws := shiftList_termShape_length sig amount cutoff bs.tail ts us' hts hus
          exact ⟨.cons hwu hws.1,
            by simpa only [List.length_cons] using congrArg Nat.succ hws.2⟩
        · simp at hop
      · simp at hop
termination_by sizeOf ts
end

theorem shiftList_termShape (sig : Sig) (amount cutoff : Nat)
    (bs : List Nat) (ts us : List Term) (hts : TermShapeList sig ts)
    (hop : shiftList sig amount cutoff bs ts = some us) : TermShapeList sig us :=
  (shiftList_termShape_length sig amount cutoff bs ts us hts hop).1

private theorem operations_getD_termShape (sig : Sig) :
    ∀ (args : List Term) (i : Nat), TermShapeList sig args →
      i < args.length → TermShape sig (args.getD i (.bvar 0))
  | [], _, _, hi => by simp at hi
  | a :: as, 0, hw, _ => by
      obtain ⟨ha, _⟩ := TermShapeList.cons_iff.mp hw
      simpa only [List.getD_cons_zero] using ha
  | a :: as, i + 1, hw, hi => by
      obtain ⟨_, htail⟩ := TermShapeList.cons_iff.mp hw
      simp only [List.getD_cons_succ]
      exact operations_getD_termShape sig as i htail (by simpa using hi)

mutual
theorem subst_termShape (sig : Sig) (numArgs : Nat) (args : List Term)
    (offset : Nat) (t u : Term) (hlen : args.length = numArgs)
    (hargs : TermShapeList sig args) (ht : TermShape sig t)
    (hop : substGo sig numArgs args offset t = some u) : TermShape sig u := by
  cases t with
  | bvar b =>
      simp only [substGo] at hop
      split at hop
      · simp only [Option.some.injEq] at hop
        subst u
        exact ht
      · split at hop
        · have hi : numArgs - 1 - (b - offset) < args.length := by omega
          exact shift_termShape sig offset 0 _ u
            (operations_getD_termShape sig args _ hargs hi) hop
        · split at hop
          · simp only [Option.some.injEq] at hop
            subst u
            exact .bvar _
          · simp at hop
  | lit bytes =>
      simp only [substGo, Option.some.injEq] at hop
      subst u
      exact ht
  | app s ts =>
      simp only [substGo] at hop
      split at hop
      · simp only [Option.some.injEq] at hop
        subst u
        exact ht
      · rw [substGoArgs_eq] at hop
        obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hop
        obtain ⟨info, hs, htslen, hts⟩ := TermShape.app_iff.mp ht
        have hout := substList_termShape_length sig numArgs args offset
          ((bindersOf sig s).drop 0) ts us hlen hargs hts hus
        exact .app hs (hout.2.trans htslen) hout.1
termination_by sizeOf t

theorem substList_termShape_length (sig : Sig) (numArgs : Nat) (args : List Term)
    (offset : Nat) (bs : List Nat) (ts us : List Term) (hlen : args.length = numArgs)
    (hargs : TermShapeList sig args) (hts : TermShapeList sig ts)
    (hop : substList sig numArgs args offset bs ts = some us) :
    TermShapeList sig us ∧ us.length = ts.length := by
  cases ts with
  | nil =>
      simp only [substList, Option.some.injEq] at hop
      subst us
      exact ⟨.nil, rfl⟩
  | cons t ts =>
      obtain ⟨ht, hts⟩ := TermShapeList.cons_iff.mp hts
      simp only [substList] at hop
      split at hop
      · split at hop
        · rename_i u us' hu hus
          simp only [Option.some.injEq] at hop
          subst us
          have hwu := subst_termShape sig numArgs args (offset + bs.headD 0) t u
            hlen hargs ht hu
          have hws := substList_termShape_length sig numArgs args offset bs.tail ts us'
            hlen hargs hts hus
          exact ⟨.cons hwu hws.1,
            by simpa only [List.length_cons] using congrArg Nat.succ hws.2⟩
        · simp at hop
      · simp at hop
termination_by sizeOf ts
end

theorem substList_termShape (sig : Sig) (numArgs : Nat) (args : List Term)
    (offset : Nat) (bs : List Nat) (ts us : List Term) (hlen : args.length = numArgs)
    (hargs : TermShapeList sig args) (hts : TermShapeList sig ts)
    (hop : substList sig numArgs args offset bs ts = some us) : TermShapeList sig us :=
  (substList_termShape_length sig numArgs args offset bs ts us hlen hargs hts hop).1

theorem substBVars_termShape (sig : Sig) (numArgs : Nat) (args : List Term)
    (body result : Term) (offset : Nat) (hlen : args.length = numArgs)
    (hargs : TermShapeList sig args) (hbody : TermShape sig body)
    (hop : substBVars sig numArgs args body offset = some result) : TermShape sig result := by
  simp only [substBVars] at hop
  split at hop
  · simp only [Option.some.injEq] at hop
    subst result
    exact hbody
  · exact subst_termShape sig numArgs args offset body result hlen hargs hbody hop

mutual
theorem inst_termShape (sig : Sig) (F : SymId) (arity : Nat) (value : Term)
    (offset : Nat) (t u : Term) (hvalue : TermShape sig value)
    (hF : IsFvarOf sig F arity) (ht : TermShape sig t)
    (hop : instGo sig F arity value offset t = some u) : TermShape sig u := by
  cases t with
  | bvar b =>
      simp only [instGo, Option.some.injEq] at hop
      subst u
      exact ht
  | lit bytes =>
      simp only [instGo, Option.some.injEq] at hop
      subst u
      exact ht
  | app s ts =>
      simp only [instGo] at hop
      split at hop
      · simp only [Option.some.injEq] at hop
        subst u
        exact ht
      · obtain ⟨info, hs, htslen, hts⟩ := TermShape.app_iff.mp ht
        rw [instArgs_eq] at hop
        simp only [List.drop_zero] at hop
        cases hus : instList sig F arity value offset (bindersOf sig s) ts with
        | none => simp [hus] at hop
        | some us =>
            have hout := instList_termShape_length sig F arity value offset
              (bindersOf sig s) ts us hvalue hF hts hus
            by_cases hsid : s = F
            · subst s
              simp only [hus] at hop
              cases hvop : shift sig offset arity value with
              | none => simp [hvop] at hop
              | some value' =>
                  simp only [hvop] at hop
                  have hv := shift_termShape sig offset arity value value' hvalue hvop
                  have harity : info.arity = arity := by
                    simpa only [symArity, hs] using hF.2.2
                  exact substBVars_termShape sig arity us value' u 0
                    (hout.2.trans (htslen.trans harity)) hout.1 hv hop
            · simp only [hus, if_neg hsid, Option.some.injEq] at hop
              subst u
              exact .app hs (hout.2.trans htslen) hout.1
termination_by sizeOf t

theorem instList_termShape_length (sig : Sig) (F : SymId) (arity : Nat) (value : Term)
    (offset : Nat) (bs : List Nat) (ts us : List Term) (hvalue : TermShape sig value)
    (hF : IsFvarOf sig F arity) (hts : TermShapeList sig ts)
    (hop : instList sig F arity value offset bs ts = some us) :
    TermShapeList sig us ∧ us.length = ts.length := by
  cases ts with
  | nil =>
      simp only [instList, Option.some.injEq] at hop
      subst us
      exact ⟨.nil, rfl⟩
  | cons t ts =>
      obtain ⟨ht, hts⟩ := TermShapeList.cons_iff.mp hts
      simp only [instList] at hop
      split at hop
      · split at hop
        · rename_i u us' hu hus
          simp only [Option.some.injEq] at hop
          subst us
          have hwu := inst_termShape sig F arity value (offset + bs.headD 0) t u
            hvalue hF ht hu
          have hws := instList_termShape_length sig F arity value offset bs.tail ts us'
            hvalue hF hts hus
          exact ⟨.cons hwu hws.1,
            by simpa only [List.length_cons] using congrArg Nat.succ hws.2⟩
        · simp at hop
      · simp at hop
termination_by sizeOf ts
end

theorem instList_termShape (sig : Sig) (F : SymId) (arity : Nat) (value : Term)
    (offset : Nat) (bs : List Nat) (ts us : List Term) (hvalue : TermShape sig value)
    (hF : IsFvarOf sig F arity) (hts : TermShapeList sig ts)
    (hop : instList sig F arity value offset bs ts = some us) : TermShapeList sig us :=
  (instList_termShape_length sig F arity value offset bs ts us hvalue hF hts hop).1

end Mettapedia.Languages.VibeITP.Presentation
