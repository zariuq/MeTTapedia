import Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslateStableCommonPreservation
import Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslateStableCommon

/-!
# Validated HE↔PeTTa Roundtrip Theorems

Late validated-fragment roundtrip proofs extracted from
`HEPeTTaTranslate.lean` so they can be checked separately under tighter
resource limits.
-/

namespace Mettapedia.Languages.MeTTa.Translation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

private theorem translatePeTTa_notForbidden_of_headSource_aux
    (a : Atom) (s : Nat) (h : isValidatedPeTTaHeadSource a = true) :
    isForbiddenHeadSymbol (translatePeTTa a s).1 = false := by
  cases a with
  | var _ => simp [translatePeTTa, isForbiddenHeadSymbol]
  | symbol c => simpa [translatePeTTa] using headSourcePeTTaSymbol_notForbidden_aux c h
  | grounded _ => simp [translatePeTTa, isForbiddenHeadSymbol]
  | expression es =>
      cases es with
      | nil => simp [translatePeTTa, isForbiddenHeadSymbol]
      | cons hd args =>
          cases hd with
          | symbol c =>
              by_cases hprogn : c = "progn"
              · subst hprogn
                cases args with
                | nil =>
                    simp [translatePeTTa, translatePeTTa.translatePeTTaProgn, isForbiddenHeadSymbol]
                | cons x xs =>
                    cases xs with
                    | nil =>
                        have hx : isValidatedPeTTaHeadSource x = true := by
                          simpa [isValidatedPeTTaHeadSource, isValidatedPeTTaPrognHeadArgs] using h
                        simpa [translatePeTTa, translatePeTTa.translatePeTTaProgn] using
                          translatePeTTa_notForbidden_of_headSource_aux x s hx
                    | cons _ _ =>
                        simp [translatePeTTa, translatePeTTa.translatePeTTaProgn,
                          freshVar, isForbiddenHeadSymbol]
              · by_cases hprog1 : c = "prog1"
                · subst hprog1
                  cases args with
                  | nil =>
                      simp [translatePeTTa, translatePeTTa.translatePeTTaProg1, isForbiddenHeadSymbol]
                  | cons x xs =>
                      cases xs with
                      | nil =>
                          have hx : isValidatedPeTTaHeadSource x = true := by
                            simpa [isValidatedPeTTaHeadSource, isValidatedPeTTaProg1HeadArgs] using h
                          simpa [translatePeTTa, translatePeTTa.translatePeTTaProg1] using
                            translatePeTTa_notForbidden_of_headSource_aux x s hx
                      | cons _ _ =>
                          simp [translatePeTTa, translatePeTTa.translatePeTTaProg1,
                            freshVar, isForbiddenHeadSymbol]
                · by_cases hfoldall : c = "foldall"
                  · subst hfoldall
                    cases args with
                    | nil => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                    | cons _ rest =>
                        cases rest with
                        | nil => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                        | cons _ rest =>
                            cases rest with
                            | nil => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                            | cons _ rest =>
                                cases rest with
                                | nil => simp [translatePeTTa, isForbiddenHeadSymbol]
                                | cons _ _ =>
                                    simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                  · by_cases hlt : c = "@<"
                    · subst hlt
                      cases args with
                      | nil => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                      | cons _ rest =>
                          cases rest with
                          | nil => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                          | cons _ rest =>
                              cases rest with
                              | nil => simp [translatePeTTa, isForbiddenHeadSymbol]
                              | cons _ _ =>
                                  simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                    · by_cases hgt : c = "@>"
                      · subst hgt
                        cases args with
                        | nil => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                        | cons _ rest =>
                            cases rest with
                            | nil => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                            | cons _ rest =>
                                cases rest with
                                | nil => simp [translatePeTTa, isForbiddenHeadSymbol]
                                | cons _ _ =>
                                    simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                      · simp [translatePeTTa, translatePeTTa.translatePeTTaList, hprogn,
                          hprog1, hfoldall, hlt, hgt, isForbiddenHeadSymbol]
          | var _ =>
              simp [translatePeTTa, translatePeTTa.translatePeTTaList, isForbiddenHeadSymbol]
          | grounded _ =>
              simp [translatePeTTa, translatePeTTa.translatePeTTaList, isForbiddenHeadSymbol]
          | expression _ =>
              simp [translatePeTTa, translatePeTTa.translatePeTTaList, isForbiddenHeadSymbol]

private theorem sizeOf_tail_lt_cons_atom (x : Atom) (xs : List Atom) :
    sizeOf xs < sizeOf (x :: xs) := by
  simp_wf

private theorem sizeOf_args_lt_expression_cons (hd : Atom) (args : List Atom) :
    sizeOf args < sizeOf (Atom.expression (hd :: args)) := by
  simp_wf

private theorem sizeOf_mem_lt_expression_cons
    (x hd : Atom) (args : List Atom) (hx : x ∈ hd :: args) :
    sizeOf x < sizeOf (Atom.expression (hd :: args)) := by
  have h1 : sizeOf x < sizeOf (hd :: args) := List.sizeOf_lt_of_mem hx
  have h2 : sizeOf (hd :: args) < sizeOf (Atom.expression (hd :: args)) := by
    simp_wf
  exact lt_trans h1 h2

private theorem translatePeTTaProgn_preserves_stableCommonForm_with
    (bound : Nat)
    (step : ∀ (a : Atom) (s : Nat),
      isValidatedPeTTaSource a = true →
      sizeOf a < bound →
      isStableCommonForm (translatePeTTa a s).1 = true)
    (args : List Atom) (s : Nat) (h : isValidatedPeTTaList args = true)
    (hbound : ∀ {a : Atom}, a ∈ args → sizeOf a < bound) :
    isStableCommonForm (translatePeTTa.translatePeTTaProgn args s).1 = true := by
  induction args generalizing s with
  | nil =>
      simp [translatePeTTa.translatePeTTaProgn, isStableCommonForm]
  | cons x xs ih =>
      cases xs with
      | nil =>
          have hxsrc : isValidatedPeTTaSource x = true := by
            simpa [isValidatedPeTTaList, Bool.and_eq_true] using h
          have hx := step x s hxsrc (hbound (by simp))
          simpa [translatePeTTa.translatePeTTaProgn] using hx
      | cons y ys =>
          have hvalid : isValidatedPeTTaList (x :: y :: ys) = true := by
            simpa using h
          simp [isValidatedPeTTaList, Bool.and_eq_true] at hvalid
          have hx := step x (freshVar "discard" s).2 hvalid.1 (hbound (by simp))
          have htailvalid : isValidatedPeTTaList (y :: ys) = true := by
            simpa [isValidatedPeTTaList, Bool.and_eq_true] using hvalid.2
          have hrest :=
            ih (translatePeTTa x (freshVar "discard" s).2).2 htailvalid (by
              intro a ha
              exact hbound (by simp [ha]))
          have hhead : isStableCommonHead (.symbol "let") = true := by
            simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
          have hcons :=
            stableCommonForm_cons_of_head (.symbol "let")
              [(freshVar "discard" s).1,
               (translatePeTTa x (freshVar "discard" s).2).1,
               (translatePeTTa.translatePeTTaProgn (y :: ys)
                  (translatePeTTa x (freshVar "discard" s).2).2).1] hhead
          have hbody :
              isStableCommonForm
                (.expression
                  [.symbol "let",
                   (freshVar "discard" s).1,
                   (translatePeTTa x (freshVar "discard" s).2).1,
                   (translatePeTTa.translatePeTTaProgn (y :: ys)
                      (translatePeTTa x (freshVar "discard" s).2).2).1]) = true := by
            rw [hcons]
            have hx' : isStableCommonForm (translatePeTTa x (s + 1)).1 = true := by
              simpa [freshVar] using hx
            simpa [freshVar, isStableCommonList, isStableCommonForm] using
              And.intro hx' hrest
          simpa [translatePeTTa.translatePeTTaProgn, freshVar] using hbody

private theorem translatePeTTaProg1Rest_preserves_stableCommonForm_with
    (bound : Nat)
    (step : ∀ (a : Atom) (s : Nat),
      isValidatedPeTTaSource a = true →
      sizeOf a < bound →
      isStableCommonForm (translatePeTTa a s).1 = true)
    (args : List Atom) (resultVar : Atom) (s : Nat)
    (hresult : isStableCommonForm resultVar = true)
    (h : isValidatedPeTTaList args = true)
    (hbound : ∀ {a : Atom}, a ∈ args → sizeOf a < bound) :
    isStableCommonForm (translatePeTTa.translatePeTTaProg1Rest args resultVar s).1 = true := by
  induction args generalizing resultVar s with
  | nil =>
      simpa [translatePeTTa.translatePeTTaProg1Rest] using hresult
  | cons x xs ih =>
      simp [isValidatedPeTTaList, Bool.and_eq_true] at h
      have hx := step x (freshVar "discard" s).2 h.1 (hbound (by simp))
      have hrest :=
        ih _ (translatePeTTa x (freshVar "discard" s).2).2 hresult h.2 (by
          intro a ha
          exact hbound (by simp [ha]))
      have hhead : isStableCommonHead (.symbol "let") = true := by
        simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
      have hcons :=
        stableCommonForm_cons_of_head (.symbol "let")
          [(freshVar "discard" s).1,
           (translatePeTTa x (freshVar "discard" s).2).1,
           (translatePeTTa.translatePeTTaProg1Rest xs resultVar
             (translatePeTTa x (freshVar "discard" s).2).2).1] hhead
      have hbody :
          isStableCommonForm
            (.expression
              [.symbol "let",
               (freshVar "discard" s).1,
               (translatePeTTa x (freshVar "discard" s).2).1,
               (translatePeTTa.translatePeTTaProg1Rest xs resultVar
                 (translatePeTTa x (freshVar "discard" s).2).2).1]) = true := by
        rw [hcons]
        have hx' : isStableCommonForm (translatePeTTa x (s + 1)).1 = true := by
          simpa [freshVar] using hx
        simpa [freshVar, isStableCommonList, isStableCommonForm] using
          And.intro hx' hrest
      simpa [translatePeTTa.translatePeTTaProg1Rest, freshVar] using hbody

private theorem translatePeTTaProg1_preserves_stableCommonForm_with
    (bound : Nat)
    (step : ∀ (a : Atom) (s : Nat),
      isValidatedPeTTaSource a = true →
      sizeOf a < bound →
      isStableCommonForm (translatePeTTa a s).1 = true)
    (args : List Atom) (s : Nat) (h : isValidatedPeTTaList args = true)
    (hbound : ∀ {a : Atom}, a ∈ args → sizeOf a < bound) :
    isStableCommonForm (translatePeTTa.translatePeTTaProg1 args s).1 = true := by
  induction args generalizing s with
  | nil =>
      simp [translatePeTTa.translatePeTTaProg1, isStableCommonForm]
  | cons x xs ih =>
      cases xs with
      | nil =>
          have hxsrc : isValidatedPeTTaSource x = true := by
            simpa [isValidatedPeTTaList, Bool.and_eq_true] using h
          have hx := step x s hxsrc (hbound (by simp))
          simpa [translatePeTTa.translatePeTTaProg1] using hx
      | cons y ys =>
          have hvalid : isValidatedPeTTaList (x :: y :: ys) = true := by
            simpa using h
          simp [isValidatedPeTTaList, Bool.and_eq_true] at hvalid
          have hresult : isStableCommonForm (freshVar "result" s).1 = true := by
            simp [freshVar, isStableCommonForm]
          have hx := step x (freshVar "result" s).2 hvalid.1 (hbound (by simp))
          have htailvalid : isValidatedPeTTaList (y :: ys) = true := by
            simpa [isValidatedPeTTaList, Bool.and_eq_true] using hvalid.2
          have htailbound : ∀ {a : Atom}, a ∈ (y :: ys) → sizeOf a < bound := by
            intro a ha
            exact hbound (by simp [ha])
          have hrest :=
            translatePeTTaProg1Rest_preserves_stableCommonForm_with bound step
              (y :: ys) (freshVar "result" s).1
              (translatePeTTa x (freshVar "result" s).2).2 hresult htailvalid htailbound
          have hhead : isStableCommonHead (.symbol "let") = true := by
            simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
          have hcons :=
            stableCommonForm_cons_of_head (.symbol "let")
              [(freshVar "result" s).1,
               (translatePeTTa x (freshVar "result" s).2).1,
               (translatePeTTa.translatePeTTaProg1Rest (y :: ys)
                  (freshVar "result" s).1
                  (translatePeTTa x (freshVar "result" s).2).2).1] hhead
          have hbody :
              isStableCommonForm
                (.expression
                  [.symbol "let",
                   (freshVar "result" s).1,
                   (translatePeTTa x (freshVar "result" s).2).1,
                   (translatePeTTa.translatePeTTaProg1Rest (y :: ys)
                      (freshVar "result" s).1
                      (translatePeTTa x (freshVar "result" s).2).2).1]) = true := by
            rw [hcons]
            have hx' : isStableCommonForm (translatePeTTa x (s + 1)).1 = true := by
              simpa [freshVar] using hx
            simpa [freshVar, isStableCommonList, isStableCommonForm, hresult] using
              And.intro hx' hrest
          simpa [translatePeTTa.translatePeTTaProg1, freshVar] using hbody

mutual

private theorem translatePeTTa_preserves_stableCommonForm_aux
    (a : Atom) (s : Nat) (h : isValidatedPeTTaSource a = true) :
    isStableCommonForm (translatePeTTa a s).1 = true := by
  cases a with
  | var _ => simp [translatePeTTa, isStableCommonForm]
  | symbol _ => simp [translatePeTTa, isStableCommonForm]
  | grounded _ => simp [translatePeTTa, isStableCommonForm]
  | expression es =>
      cases es with
      | nil =>
          simp [translatePeTTa, translatePeTTa.translatePeTTaList,
            isStableCommonForm, isStableCommonExpr]
      | cons hd args =>
          cases hd with
          | symbol c =>
              by_cases hprogn : c = "progn"
              · subst hprogn
                have hargs : isValidatedPeTTaList args = true := by
                  simpa [isValidatedPeTTaSource] using h
                have hbound :
                    ∀ {a : Atom}, a ∈ args →
                      sizeOf a < sizeOf (Atom.expression (.symbol "progn" :: args)) := by
                  intro a ha
                  exact sizeOf_mem_lt_expression_cons a (.symbol "progn") args (by simp [ha])
                have hprognForm :
                    isStableCommonForm (translatePeTTa.translatePeTTaProgn args s).1 = true :=
                  translatePeTTaProgn_preserves_stableCommonForm_with
                    (sizeOf (Atom.expression (.symbol "progn" :: args)))
                    (fun a s ha hsmall => by
                      have _ : sizeOf a < sizeOf (Atom.expression (.symbol "progn" :: args)) := hsmall
                      exact translatePeTTa_preserves_stableCommonForm_aux a s ha)
                    args s hargs hbound
                simpa [translatePeTTa] using hprognForm
              · by_cases hprog1 : c = "prog1"
                · subst hprog1
                  have hargs : isValidatedPeTTaList args = true := by
                    simpa [isValidatedPeTTaSource, hprogn] using h
                  have hbound :
                      ∀ {a : Atom}, a ∈ args →
                        sizeOf a < sizeOf (Atom.expression (.symbol "prog1" :: args)) := by
                    intro a ha
                    exact sizeOf_mem_lt_expression_cons a (.symbol "prog1") args (by simp [ha])
                  have hprog1Form :
                      isStableCommonForm (translatePeTTa.translatePeTTaProg1 args s).1 = true :=
                    translatePeTTaProg1_preserves_stableCommonForm_with
                      (sizeOf (Atom.expression (.symbol "prog1" :: args)))
                      (fun a s ha hsmall => by
                        have _ : sizeOf a < sizeOf (Atom.expression (.symbol "prog1" :: args)) := hsmall
                        exact translatePeTTa_preserves_stableCommonForm_aux a s ha)
                      args s hargs hbound
                  simpa [translatePeTTa] using hprog1Form
                · by_cases hfoldall : c = "foldall"
                  · subst hfoldall
                    cases args with
                    | nil => simp [isValidatedPeTTaSource] at h
                    | cons agg rest =>
                        cases rest with
                        | nil => simp [isValidatedPeTTaSource] at h
                        | cons goal rest =>
                            cases rest with
                            | nil => simp [isValidatedPeTTaSource] at h
                            | cons init rest =>
                                cases rest with
                                | nil =>
                                    have hparts :
                                        (isFirstOrderReducerAtom agg = true ∧
                                          isValidatedPeTTaSource goal = true) ∧
                                            isValidatedPeTTaSource init = true := by
                                      simpa [isValidatedPeTTaSource, Bool.and_eq_true] using h
                                    have hgoal :=
                                      translatePeTTa_preserves_stableCommonForm_aux goal s hparts.1.2
                                    have hinit :=
                                      translatePeTTa_preserves_stableCommonForm_aux init
                                        (translatePeTTa goal s).2 hparts.2
                                    exact translatePeTTa_foldall_preserves_stableCommonForm
                                      agg goal init s hparts.1.1 hgoal hinit
                                | cons _ _ => simp [isValidatedPeTTaSource] at h
                  · by_cases hlt : c = "@<"
                    · subst hlt
                      cases args with
                      | nil => simp [isValidatedPeTTaSource] at h
                      | cons a rest =>
                          cases rest with
                          | nil => simp [isValidatedPeTTaSource] at h
                          | cons b rest =>
                              cases rest with
                              | nil =>
                                  have hpair :
                                      isValidatedPeTTaSource a = true ∧
                                        isValidatedPeTTaSource b = true := by
                                    simpa [isValidatedPeTTaSource, Bool.and_eq_true] using h
                                  have ha :=
                                    translatePeTTa_preserves_stableCommonForm_aux a s hpair.1
                                  have hb :=
                                    translatePeTTa_preserves_stableCommonForm_aux b
                                      (translatePeTTa a s).2 hpair.2
                                  simp [translatePeTTa, isStableCommonForm, isStableCommonExpr,
                                    isStableCommonHead, isForbiddenHeadSymbol,
                                    isStableCommonList, ha, hb]
                              | cons _ _ => simp [isValidatedPeTTaSource] at h
                    · by_cases hgt : c = "@>"
                      · subst hgt
                        cases args with
                        | nil => simp [isValidatedPeTTaSource] at h
                        | cons a rest =>
                            cases rest with
                            | nil => simp [isValidatedPeTTaSource] at h
                            | cons b rest =>
                                cases rest with
                                | nil =>
                                    have hpair :
                                        isValidatedPeTTaSource a = true ∧
                                          isValidatedPeTTaSource b = true := by
                                      simpa [isValidatedPeTTaSource, Bool.and_eq_true] using h
                                    have ha :=
                                      translatePeTTa_preserves_stableCommonForm_aux a s hpair.1
                                    have hb :=
                                      translatePeTTa_preserves_stableCommonForm_aux b
                                        (translatePeTTa a s).2 hpair.2
                                    simp [translatePeTTa, isStableCommonForm, isStableCommonExpr,
                                      isStableCommonHead, isForbiddenHeadSymbol,
                                      isStableCommonList, ha, hb]
                                | cons _ _ => simp [isValidatedPeTTaSource] at h
                      · have hchain : c ≠ "chain" := by
                          intro hc
                          subst hc
                          simp [isValidatedPeTTaSource] at h
                        have hcollapse : c ≠ "collapse-bind" := by
                          intro hc
                          subst hc
                          simp [isValidatedPeTTaSource] at h
                        have hsuperpose : c ≠ "superpose-bind" := by
                          intro hc
                          subst hc
                          simp [isValidatedPeTTaSource] at h
                        have hswitch : c ≠ "switch" := by
                          intro hc
                          subst hc
                          simp [isValidatedPeTTaSource] at h
                        have hswitchm : c ≠ "switch-minimal" := by
                          intro hc
                          subst hc
                          simp [isValidatedPeTTaSource] at h
                        have hatomsubst : c ≠ "atom-subst" := by
                          intro hc
                          subst hc
                          simp [isValidatedPeTTaSource] at h
                        have hnop : c ≠ "nop" := by
                          intro hc
                          subst hc
                          simp [isValidatedPeTTaSource] at h
                        have hfunction : c ≠ "function" := by
                          intro hc
                          subst hc
                          simp [isValidatedPeTTaSource] at h
                        have hparts :
                            isValidatedPeTTaHeadSource (.symbol c) = true ∧
                              isValidatedPeTTaList args = true := by
                          simpa [isValidatedPeTTaSource, isValidatedPeTTaHeadSource,
                            Bool.and_eq_true, hchain, hcollapse, hsuperpose, hswitch,
                            hswitchm, hatomsubst, hnop, hfunction, hprogn, hprog1,
                            hfoldall, hlt, hgt] using h
                        have htail :
                            isStableCommonList (translatePeTTa.translatePeTTaList args s).1 = true :=
                          translatePeTTaList_preserves_stableCommonList_aux args s hparts.2
                        have hnot : isForbiddenHeadSymbol (.symbol c) = false :=
                          headSourcePeTTaSymbol_notForbidden_aux c hparts.1
                        have hhead : isStableCommonHead (.symbol c) = true := by
                          simpa [isStableCommonHead, isStableCommonForm] using hnot
                        have hcons :=
                          stableCommonForm_cons_of_head (.symbol c)
                            (translatePeTTa.translatePeTTaList args s).1 hhead
                        have hbody :
                            isStableCommonForm
                              (.expression
                                (.symbol c :: (translatePeTTa.translatePeTTaList args s).1)) = true := by
                          rw [hcons]
                          exact htail
                        simpa [translatePeTTa, translatePeTTa.translatePeTTaList,
                          hprogn, hprog1, hfoldall, hlt, hgt] using hbody
          | var _ =>
              have hargs : isValidatedPeTTaList args = true := by
                simpa [isValidatedPeTTaSource, isValidatedPeTTaHeadSource] using h
              have htail := translatePeTTaList_preserves_stableCommonList_aux args s hargs
              simp [translatePeTTa, translatePeTTa.translatePeTTaList, isStableCommonForm,
                isStableCommonExpr, isStableCommonHead, isForbiddenHeadSymbol,
                isStableCommonList, htail]
          | grounded _ =>
              have hargs : isValidatedPeTTaList args = true := by
                simpa [isValidatedPeTTaSource, isValidatedPeTTaHeadSource] using h
              have htail := translatePeTTaList_preserves_stableCommonList_aux args s hargs
              simp [translatePeTTa, translatePeTTa.translatePeTTaList, isStableCommonForm,
                isStableCommonExpr, isStableCommonHead, isForbiddenHeadSymbol,
                isStableCommonList, htail]
          | expression es' =>
              have hparts :
                  isValidatedPeTTaHeadSource (.expression es') = true ∧
                    isValidatedPeTTaList args = true := by
                simpa [isValidatedPeTTaSource] using h
              have hhdsrc :=
                validatedPeTTaSource_of_headSource_aux (.expression es') hparts.1
              have hhdform :=
                translatePeTTa_preserves_stableCommonForm_aux (.expression es') s hhdsrc
              have hhdnot :=
                translatePeTTa_notForbidden_of_headSource_aux (.expression es') s hparts.1
              have hhd : isStableCommonHead (translatePeTTa (.expression es') s).1 = true := by
                simpa [isStableCommonHead] using
                  stableCommonHead_of_stableCommonForm _ hhdform hhdnot
              have htail :=
                translatePeTTaList_preserves_stableCommonList_aux args
                  (translatePeTTa (.expression es') s).2 hparts.2
              have hcons :=
                stableCommonForm_cons_of_head (translatePeTTa (.expression es') s).1
                  (translatePeTTa.translatePeTTaList args (translatePeTTa (.expression es') s).2).1
                  hhd
              have hbody :
                  isStableCommonForm
                    (.expression
                      ((translatePeTTa (.expression es') s).1 ::
                        (translatePeTTa.translatePeTTaList args
                          (translatePeTTa (.expression es') s).2).1)) = true := by
                rw [hcons]
                exact htail
              simpa [translatePeTTa, translatePeTTa.translatePeTTaList] using hbody
  termination_by sizeOf a
  decreasing_by
    all_goals
      subst_vars
      try simpa using hsmall
      try
        have hmem := List.sizeOf_lt_of_mem hxInArgs
        omega
      simp_wf
      try omega

private theorem translatePeTTaList_preserves_stableCommonList_aux
    (xs : List Atom) (s : Nat) (h : isValidatedPeTTaList xs = true) :
    isStableCommonList (translatePeTTa.translatePeTTaList xs s).1 = true := by
  cases xs with
  | nil => simp [translatePeTTa.translatePeTTaList, isStableCommonList]
  | cons x xs =>
      simp [isValidatedPeTTaList, Bool.and_eq_true] at h
      have hx : isStableCommonForm (translatePeTTa x s).1 = true :=
        translatePeTTa_preserves_stableCommonForm_aux x s h.1
      have hxs :
          isStableCommonList (translatePeTTa.translatePeTTaList xs (translatePeTTa x s).2).1 = true :=
        translatePeTTaList_preserves_stableCommonList_aux xs (translatePeTTa x s).2 h.2
      simp [translatePeTTa.translatePeTTaList, isStableCommonList, hx, hxs]
  termination_by sizeOf xs
  decreasing_by
    all_goals
      subst_vars
      try simpa using hsmall
      try
        have hmem := List.sizeOf_lt_of_mem hxInArgs
        omega
      simp_wf
      try omega
end

/-- Validated PeTTa inputs translate into the stable common fragment. -/
theorem translatePeTTa_preserves_stableCommonForm (a : Atom) (s : Nat)
    (h : isValidatedPeTTaSource a = true) :
    isStableCommonForm (translatePeTTa a s).1 = true :=
  translatePeTTa_preserves_stableCommonForm_aux a s h

/-- Corrected PeTTa→HE→PeTTa fixed-point theorem on the validated PeTTa fragment. -/
theorem translatePeTTa_roundtrip_fixedPoint_of_validatedPeTTaSource (a : Atom) (s : Nat)
    (h : isValidatedPeTTaSource a = true) :
    let (he, s1) := translatePeTTa a s
    let (petta2, s2) := translateHE he s1
    let (he2, _) := translatePeTTa petta2 s2
    he2 = he := by
  let hs : isStableCommonForm (translatePeTTa a s).1 = true :=
    translatePeTTa_preserves_stableCommonForm a s h
  have hhe : translateHE (translatePeTTa a s).1 (translatePeTTa a s).2 =
      ((translatePeTTa a s).1, (translatePeTTa a s).2) :=
    translateHE_id_of_stableCommonForm (translatePeTTa a s).1 (translatePeTTa a s).2 hs
  have hpe : translatePeTTa (translatePeTTa a s).1 (translatePeTTa a s).2 =
      ((translatePeTTa a s).1, (translatePeTTa a s).2) :=
    translatePeTTa_id_of_stableCommonForm (translatePeTTa a s).1 (translatePeTTa a s).2 hs
  simpa [hs, hhe, hpe]

/-- Corrected HE→PeTTa→HE fixed-point theorem on the validated HE fragment. -/
theorem translateHE_roundtrip_fixedPoint_of_validatedHESource (a : Atom) (s : Nat)
    (h : isValidatedHESource a = true) :
    let (petta, s1) := translateHE a s
    let (he2, s2) := translatePeTTa petta s1
    let (petta2, _) := translateHE he2 s2
    petta2 = petta := by
  let hs : isStableCommonForm (translateHE a s).1 = true :=
    translateHE_preserves_stableCommonForm a s h
  have hpe : translatePeTTa (translateHE a s).1 (translateHE a s).2 =
      ((translateHE a s).1, (translateHE a s).2) :=
    translatePeTTa_id_of_stableCommonForm (translateHE a s).1 (translateHE a s).2 hs
  have hhe : translateHE (translateHE a s).1 (translateHE a s).2 =
      ((translateHE a s).1, (translateHE a s).2) :=
    translateHE_id_of_stableCommonForm (translateHE a s).1 (translateHE a s).2 hs
  simpa [hs, hpe, hhe]




end Mettapedia.Languages.MeTTa.Translation
