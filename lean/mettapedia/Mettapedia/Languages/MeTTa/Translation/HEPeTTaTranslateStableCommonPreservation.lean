import Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslateStableCommonHelpers

/-!
# HE Stable-Common Preservation

HE-side stable-common preservation theorems extracted from
`HEPeTTaTranslate.lean` so they can be checked separately under tighter
resource limits.
-/

namespace Mettapedia.Languages.MeTTa.Translation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

set_option maxHeartbeats 800000

mutual

private theorem translateHE_preserves_stableCommonForm_aux
    (a : Atom) (s : Nat) (h : isValidatedHESource a = true) :
    isStableCommonForm (translateHE a s).1 = true := by
  cases a with
  | var _ => simp [translateHE, isStableCommonForm]
  | symbol _ => simp [translateHE, isStableCommonForm]
  | grounded _ => simp [translateHE, isStableCommonForm]
  | expression es =>
    cases es with
    | nil => simp [translateHE, translateHE.translateHEList, isStableCommonForm, isStableCommonExpr]
    | cons hd args =>
      cases hd with
      | symbol c =>
        by_cases hchain : c = "chain"
        · subst hchain
          cases args with
          | nil => simp [isValidatedHESource] at h
          | cons e rest =>
            cases rest with
            | nil => simp [isValidatedHESource] at h
            | cons v rest =>
              cases rest with
              | nil => simp [isValidatedHESource] at h
              | cons body rest =>
                cases rest with
                | nil =>
                  simp [isValidatedHESource, Bool.and_eq_true] at h
                  have he := translateHE_preserves_stableCommonForm_aux e s h.1.1
                  have hv := stableCommon_of_heBinderAtom v h.1.2
                  have hbody :=
                    translateHE_preserves_stableCommonForm_aux body (translateHE e s).2 h.2
                  simp [translateHE, isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                    isForbiddenHeadSymbol, isStableCommonList, he, hv, hbody]
                | cons _ _ => simp [isValidatedHESource] at h
        · by_cases hcollapse : c = "collapse-bind"
          · subst hcollapse
            cases args with
            | nil => simp [isValidatedHESource] at h
            | cons inner rest =>
              cases rest with
              | nil =>
                have hinner :=
                  translateHE_preserves_stableCommonForm_aux inner s
                    (by simpa [isValidatedHESource] using h)
                simp [translateHE, isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                  isForbiddenHeadSymbol, isStableCommonList, hinner]
              | cons _ _ => simp [isValidatedHESource] at h
          · by_cases hsuperpose : c = "superpose-bind"
            · subst hsuperpose
              cases args with
              | nil => simp [isValidatedHESource] at h
              | cons inner rest =>
                cases rest with
                | nil =>
                  have hinner :=
                    translateHE_preserves_stableCommonForm_aux inner s
                      (by simpa [isValidatedHESource] using h)
                  simp [translateHE, isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                    isForbiddenHeadSymbol, isStableCommonList, hinner]
                | cons _ _ => simp [isValidatedHESource] at h
            · by_cases hswitch : c = "switch"
              · subst hswitch
                cases args with
                | nil => simp [isValidatedHESource] at h
                | cons scrut branches =>
                  simp [isValidatedHESource, Bool.and_eq_true] at h
                  have hscrut := translateHE_preserves_stableCommonForm_aux scrut s h.1
                  have hbranches :=
                    translateHEList_preserves_stableCommonList_aux branches (translateHE scrut s).2 h.2
                  simp [translateHE, isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                    isForbiddenHeadSymbol, isStableCommonList, hscrut, hbranches]
              · by_cases hswitchm : c = "switch-minimal"
                · subst hswitchm
                  cases args with
                  | nil => simp [isValidatedHESource] at h
                  | cons scrut branches =>
                    simp [isValidatedHESource, Bool.and_eq_true] at h
                    have hscrut := translateHE_preserves_stableCommonForm_aux scrut s h.1
                    have hbranches :=
                      translateHEList_preserves_stableCommonList_aux branches (translateHE scrut s).2 h.2
                    simp [translateHE, isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                      isForbiddenHeadSymbol, isStableCommonList, hscrut, hbranches]
                · by_cases hatomsubst : c = "atom-subst"
                  · subst hatomsubst
                    cases args with
                    | nil => simp [isValidatedHESource] at h
                    | cons atom rest =>
                      cases rest with
                      | nil => simp [isValidatedHESource] at h
                      | cons v rest =>
                        cases rest with
                        | nil => simp [isValidatedHESource] at h
                        | cons tmpl rest =>
                          cases rest with
                          | nil =>
                            simp [isValidatedHESource, Bool.and_eq_true] at h
                            have hatom :=
                              translateHE_preserves_stableCommonForm_aux atom s h.1.1
                            have hv := stableCommon_of_heBinderAtom v h.1.2
                            have htmpl :=
                              translateHE_preserves_stableCommonForm_aux tmpl (translateHE atom s).2 h.2
                            simp [translateHE, isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                              isForbiddenHeadSymbol, isStableCommonList, hatom, hv, htmpl]
                          | cons _ _ => simp [isValidatedHESource] at h
                  · by_cases hnop : c = "nop"
                    · subst hnop
                      cases args with
                      | nil => simp [isValidatedHESource] at h
                      | cons x rest =>
                        cases rest with
                        | nil =>
                          have hx :=
                            translateHE_preserves_stableCommonForm_aux x (freshVar "discard" s).2
                              (by simpa [isValidatedHESource] using h)
                          have hx' : isStableCommonForm (translateHE x (s + 1)).1 = true := by
                            simpa [freshVar] using hx
                          simp [translateHE, freshVar, isStableCommonForm, isStableCommonExpr,
                            isStableCommonHead, isForbiddenHeadSymbol, isStableCommonList, hx']
                        | cons _ _ => simp [isValidatedHESource] at h
                    · by_cases hfunction : c = "function"
                      · subst hfunction
                        cases args with
                        | nil => simp [isValidatedHESource] at h
                        | cons x rest =>
                          cases rest with
                          | nil =>
                            cases x with
                            | expression es' =>
                              cases es' with
                              | nil => simp [isValidatedHESource] at h
                              | cons hd' tail' =>
                                cases hd' with
                                | symbol c' =>
                                  by_cases hreturn : c' = "return"
                                  · subst hreturn
                                    cases tail' with
                                    | nil => simp [isValidatedHESource] at h
                                    | cons inner rest' =>
                                      cases rest' with
                                      | nil =>
                                        simpa [translateHE, isValidatedHESource] using
                                          translateHE_preserves_stableCommonForm_aux inner s
                                            (by simpa [isValidatedHESource] using h)
                                      | cons _ _ => simp [isValidatedHESource] at h
                                  · simp [isValidatedHESource, hreturn] at h
                                | var _ => simp [isValidatedHESource] at h
                                | grounded _ => simp [isValidatedHESource] at h
                                | expression _ => simp [isValidatedHESource] at h
                            | var _ => simp [isValidatedHESource] at h
                            | symbol _ => simp [isValidatedHESource] at h
                            | grounded _ => simp [isValidatedHESource] at h
                          | cons _ _ => simp [isValidatedHESource] at h
                      · by_cases hfoldall : c = "foldall"
                        · subst hfoldall
                          simp [isValidatedHESource] at h
                        · by_cases hprogn : c = "progn"
                          · subst hprogn
                            have hfalse : False := by
                              simpa [isValidatedHESource] using h
                            exact False.elim hfalse
                          · by_cases hprog1 : c = "prog1"
                            · subst hprog1
                              have hfalse : False := by
                                simpa [isValidatedHESource] using h
                              exact False.elim hfalse
                            · by_cases hlt : c = "@<"
                              · subst hlt
                                have hfalse : False := by
                                  simpa [isValidatedHESource] using h
                                exact False.elim hfalse
                              · by_cases hgt : c = "@>"
                                · subst hgt
                                  have hfalse : False := by
                                    simpa [isValidatedHESource] using h
                                  exact False.elim hfalse
                                · have hpair :
                                      isValidatedHEHeadSource (.symbol c) = true ∧
                                        isValidatedHEList args = true := by
                                    simpa [isValidatedHESource, isValidatedHEHeadSource,
                                      Bool.and_eq_true, hchain, hcollapse, hsuperpose, hswitch,
                                      hswitchm, hatomsubst, hnop, hfunction, hfoldall, hprogn,
                                      hprog1, hlt, hgt] using h
                                  have hargs : isValidatedHEList args = true := hpair.2
                                  have htail :
                                      isStableCommonList (translateHE.translateHEList args s).1 = true :=
                                    translateHEList_preserves_stableCommonList_aux args s hargs
                                  have hhead : isStableCommonHead (.symbol c) = true := by
                                    simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol,
                                      hchain, hcollapse, hsuperpose, hswitch, hswitchm, hatomsubst,
                                      hnop, hfunction, hprogn, hprog1, hfoldall, hlt, hgt]
                                  have hcons :=
                                    stableCommonForm_cons_of_head (.symbol c)
                                      (translateHE.translateHEList args s).1 hhead
                                  have hbody :
                                      isStableCommonForm
                                        (Atom.expression
                                          (.symbol c :: (translateHE.translateHEList args s).1)) = true := by
                                    rw [hcons]
                                    exact htail
                                  simpa [translateHE, translateHE.translateHEList, hchain,
                                    hcollapse, hsuperpose, hswitch, hswitchm, hatomsubst, hnop,
                                    hfunction, hfoldall, hprogn, hprog1, hlt, hgt] using hbody
      | var v =>
        have hargs : isValidatedHEList args = true := by
          simpa [isValidatedHESource, isValidatedHEHeadSource] using h
        have htail := translateHEList_preserves_stableCommonList_aux args s hargs
        simpa [translateHE, translateHE.translateHEList, isStableCommonForm, isStableCommonExpr,
          isStableCommonHead, isForbiddenHeadSymbol, isStableCommonList, htail]
      | grounded g =>
        have hargs : isValidatedHEList args = true := by
          simpa [isValidatedHESource, isValidatedHEHeadSource] using h
        have htail := translateHEList_preserves_stableCommonList_aux args s hargs
        simpa [translateHE, translateHE.translateHEList, isStableCommonForm, isStableCommonExpr,
          isStableCommonHead, isForbiddenHeadSymbol, isStableCommonList, htail]
      | expression es' =>
        have hparts :
            isValidatedHEHeadSource (.expression es') = true ∧ isValidatedHEList args = true := by
          simpa [isValidatedHESource] using h
        have hhead :=
          translateHE_preserves_stableCommonHead_aux (.expression es') s hparts.1
        have htail :=
          translateHEList_preserves_stableCommonList_aux args (translateHE (.expression es') s).2 hparts.2
        have hcons :=
          stableCommonForm_cons_of_head (translateHE (.expression es') s).1
            (translateHE.translateHEList args (translateHE (.expression es') s).2).1 hhead
        have hbody :
            isStableCommonForm
              (Atom.expression
                ((translateHE (.expression es') s).1 ::
                  (translateHE.translateHEList args (translateHE (.expression es') s).2).1)) = true := by
          rw [hcons]
          exact htail
        simpa [translateHE, translateHE.translateHEList] using hbody

private theorem validatedHESource_of_headSource_aux
    (a : Atom) (h : isValidatedHEHeadSource a = true) :
    isValidatedHESource a = true := by
  cases a with
  | var _ => simp [isValidatedHEHeadSource, isValidatedHESource]
  | symbol _ => simp [isValidatedHESource]
  | grounded _ => simp [isValidatedHEHeadSource, isValidatedHESource]
  | expression es =>
      cases es with
      | nil => simp [isValidatedHEHeadSource, isValidatedHESource]
      | cons hd args =>
          cases hd with
          | symbol c =>
              by_cases hfunction : c = "function"
              · subst hfunction
                cases args with
                | nil => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                | cons ret rest =>
                    cases rest with
                    | nil =>
                        cases ret with
                        | expression esx =>
                            cases esx with
                            | nil => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                            | cons hdx tailx =>
                                cases hdx with
                                | symbol c' =>
                                    by_cases hreturn : c' = "return"
                                    · subst hreturn
                                      cases tailx with
                                      | nil => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                                      | cons inner restx =>
                                          cases restx with
                                          | nil =>
                                              have hinner : isValidatedHEHeadSource inner = true := by
                                                simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                                              simpa [isValidatedHESource] using
                                                validatedHESource_of_headSource_aux inner hinner
                                          | cons _ _ => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                                    · simp [isValidatedHEHeadSource, isValidatedHESource, hreturn] at h
                                | var _ => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                                | grounded _ => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                                | expression _ => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                        | var _ => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                        | symbol _ => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                        | grounded _ => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                    | cons _ _ => simp [isValidatedHEHeadSource, isValidatedHESource] at h
              · simpa [isValidatedHEHeadSource, hfunction] using h
          | var _ => simpa [isValidatedHEHeadSource] using h
          | grounded _ => simpa [isValidatedHEHeadSource] using h
          | expression _ => simpa [isValidatedHEHeadSource] using h

private theorem headSourceSymbol_notForbidden_aux
    (c : String) (h : isValidatedHEHeadSource (.symbol c) = true) :
    isForbiddenHeadSymbol (.symbol c) = false := by
  by_cases hchain : c = "chain"
  · subst hchain
    have hfalse : False := by
      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
    exact False.elim hfalse
  · by_cases hcollapse : c = "collapse-bind"
    · subst hcollapse
      have hfalse : False := by
        simpa [isValidatedHEHeadSource, isValidatedHESource] using h
      exact False.elim hfalse
    · by_cases hsuperpose : c = "superpose-bind"
      · subst hsuperpose
        have hfalse : False := by
          simpa [isValidatedHEHeadSource, isValidatedHESource] using h
        exact False.elim hfalse
      · by_cases hswitch : c = "switch"
        · subst hswitch
          have hfalse : False := by
            simpa [isValidatedHEHeadSource, isValidatedHESource] using h
          exact False.elim hfalse
        · by_cases hswitchm : c = "switch-minimal"
          · subst hswitchm
            have hfalse : False := by
              simpa [isValidatedHEHeadSource, isValidatedHESource] using h
            exact False.elim hfalse
          · by_cases hatomsubst : c = "atom-subst"
            · subst hatomsubst
              have hfalse : False := by
                simpa [isValidatedHEHeadSource, isValidatedHESource] using h
              exact False.elim hfalse
            · by_cases hnop : c = "nop"
              · subst hnop
                have hfalse : False := by
                  simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                exact False.elim hfalse
              · by_cases hfunction : c = "function"
                · subst hfunction
                  have hfalse : False := by
                    simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                  exact False.elim hfalse
                · by_cases hprogn : c = "progn"
                  · subst hprogn
                    have hfalse : False := by
                      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                    exact False.elim hfalse
                  · by_cases hprog1 : c = "prog1"
                    · subst hprog1
                      have hfalse : False := by
                        simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                      exact False.elim hfalse
                    · by_cases hfoldall : c = "foldall"
                      · subst hfoldall
                        have hfalse : False := by
                          simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                        exact False.elim hfalse
                      · by_cases hlt : c = "@<"
                        · subst hlt
                          have hfalse : False := by
                            simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                          exact False.elim hfalse
                        · by_cases hgt : c = "@>"
                          · subst hgt
                            have hfalse : False := by
                              simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                            exact False.elim hfalse
                          · simp [isForbiddenHeadSymbol, hchain, hcollapse, hsuperpose, hswitch,
                              hswitchm, hatomsubst, hnop, hfunction, hprogn, hprog1, hfoldall,
                              hlt, hgt]

private theorem translateHE_notForbidden_of_headSymbolExpr_aux
    (c : String) (args : List Atom) (s : Nat)
    (h : isValidatedHEHeadSource (.expression (.symbol c :: args)) = true) :
    isForbiddenHeadSymbol (translateHE (.expression (.symbol c :: args)) s).1 = false := by
  by_cases hchain : c = "chain"
  · subst hchain
    cases args with
    | nil =>
        have hfalse : False := by
          simpa [isValidatedHEHeadSource, isValidatedHESource] using h
        exact False.elim hfalse
    | cons e rest =>
        cases rest with
        | nil =>
            have hfalse : False := by
              simpa [isValidatedHEHeadSource, isValidatedHESource] using h
            exact False.elim hfalse
        | cons v rest =>
            cases rest with
            | nil =>
                have hfalse : False := by
                  simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                exact False.elim hfalse
            | cons body rest =>
                cases rest with
                | nil => simp [translateHE, isForbiddenHeadSymbol]
                | cons _ _ =>
                    have hfalse : False := by
                      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                    exact False.elim hfalse
  · by_cases hcollapse : c = "collapse-bind"
    · subst hcollapse
      cases args with
      | nil =>
          have hfalse : False := by
            simpa [isValidatedHEHeadSource, isValidatedHESource] using h
          exact False.elim hfalse
      | cons inner rest =>
          cases rest with
          | nil => simp [translateHE, isForbiddenHeadSymbol]
          | cons _ _ =>
              have hfalse : False := by
                simpa [isValidatedHEHeadSource, isValidatedHESource] using h
              exact False.elim hfalse
    · by_cases hsuperpose : c = "superpose-bind"
      · subst hsuperpose
        cases args with
        | nil =>
            have hfalse : False := by
              simpa [isValidatedHEHeadSource, isValidatedHESource] using h
            exact False.elim hfalse
        | cons inner rest =>
            cases rest with
            | nil => simp [translateHE, isForbiddenHeadSymbol]
            | cons _ _ =>
                have hfalse : False := by
                  simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                exact False.elim hfalse
      · by_cases hswitch : c = "switch"
        · subst hswitch
          cases args with
          | nil =>
              have hfalse : False := by
                simpa [isValidatedHEHeadSource, isValidatedHESource] using h
              exact False.elim hfalse
          | cons scrut branches =>
              simp [translateHE, isForbiddenHeadSymbol]
        · by_cases hswitchm : c = "switch-minimal"
          · subst hswitchm
            cases args with
            | nil =>
                have hfalse : False := by
                  simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                exact False.elim hfalse
            | cons scrut branches =>
                simp [translateHE, isForbiddenHeadSymbol]
          · by_cases hatomsubst : c = "atom-subst"
            · subst hatomsubst
              cases args with
              | nil =>
                  have hfalse : False := by
                    simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                  exact False.elim hfalse
              | cons atom rest =>
                  cases rest with
                  | nil =>
                      have hfalse : False := by
                        simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                      exact False.elim hfalse
                  | cons v rest =>
                      cases rest with
                      | nil =>
                          have hfalse : False := by
                            simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                          exact False.elim hfalse
                      | cons tmpl rest =>
                          cases rest with
                          | nil => simp [translateHE, isForbiddenHeadSymbol]
                          | cons _ _ =>
                              have hfalse : False := by
                                simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                              exact False.elim hfalse
            · by_cases hnop : c = "nop"
              · subst hnop
                cases args with
                | nil =>
                    have hfalse : False := by
                      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                    exact False.elim hfalse
                | cons x rest =>
                    cases rest with
                    | nil => simp [translateHE, isForbiddenHeadSymbol]
                    | cons _ _ =>
                        have hfalse : False := by
                          simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                        exact False.elim hfalse
              · by_cases hfunction : c = "function"
                · subst hfunction
                  cases args with
                  | nil =>
                      have hfalse : False := by
                        simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                      exact False.elim hfalse
                  | cons ret rest =>
                      cases rest with
                      | nil =>
                          cases ret with
                          | expression esx =>
                              cases esx with
                              | nil =>
                                  have hfalse : False := by
                                    simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                                  exact False.elim hfalse
                              | cons hdx tailx =>
                                  cases hdx with
                                  | symbol c' =>
                                      by_cases hreturn : c' = "return"
                                      · subst hreturn
                                        cases tailx with
                                        | nil =>
                                            have hfalse : False := by
                                              simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                                            exact False.elim hfalse
                                        | cons inner restx =>
                                            cases restx with
                                            | nil =>
                                                have hinner : isValidatedHEHeadSource inner = true := by
                                                  simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                                                simpa [translateHE] using
                                                  translateHE_notForbidden_of_headSource_aux inner s hinner
                                            | cons _ _ =>
                                                have hfalse : False := by
                                                  simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                                                exact False.elim hfalse
                                      · have hfalse : False := by
                                          simpa [isValidatedHEHeadSource, isValidatedHESource, hreturn] using h
                                        exact False.elim hfalse
                                  | var _ =>
                                      have hfalse : False := by
                                        simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                                      exact False.elim hfalse
                                  | grounded _ =>
                                      have hfalse : False := by
                                        simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                                      exact False.elim hfalse
                                  | expression _ =>
                                      have hfalse : False := by
                                        simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                                      exact False.elim hfalse
                          | var _ =>
                              have hfalse : False := by
                                simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                              exact False.elim hfalse
                          | symbol _ =>
                              have hfalse : False := by
                                simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                              exact False.elim hfalse
                          | grounded _ =>
                              have hfalse : False := by
                                simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                              exact False.elim hfalse
                      | cons _ _ =>
                          have hfalse : False := by
                            simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                          exact False.elim hfalse
                · have hprogn : c ≠ "progn" := by
                    intro hc
                    subst hc
                    have hfalse : False := by
                      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                    exact hfalse
                  have hprog1 : c ≠ "prog1" := by
                    intro hc
                    subst hc
                    have hfalse : False := by
                      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                    exact hfalse
                  have hfoldall : c ≠ "foldall" := by
                    intro hc
                    subst hc
                    have hfalse : False := by
                      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                    exact hfalse
                  have hlt : c ≠ "@<" := by
                    intro hc
                    subst hc
                    have hfalse : False := by
                      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                    exact hfalse
                  have hgt : c ≠ "@>" := by
                    intro hc
                    subst hc
                    have hfalse : False := by
                      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                    exact hfalse
                  simp [translateHE, isForbiddenHeadSymbol, hchain, hcollapse, hsuperpose,
                    hswitch, hswitchm, hatomsubst, hnop, hfunction, hprogn, hprog1,
                    hfoldall, hlt, hgt]

private theorem translateHE_notForbidden_of_headSource_aux
    (a : Atom) (s : Nat) (h : isValidatedHEHeadSource a = true) :
    isForbiddenHeadSymbol (translateHE a s).1 = false := by
  cases a with
  | var _ => simp [translateHE, isForbiddenHeadSymbol]
  | symbol c => simpa [translateHE] using headSourceSymbol_notForbidden_aux c h
  | grounded _ => simp [translateHE, isForbiddenHeadSymbol]
  | expression es =>
      cases es with
      | nil => simp [translateHE, isForbiddenHeadSymbol]
      | cons hd args =>
          cases hd with
          | symbol c => simpa using translateHE_notForbidden_of_headSymbolExpr_aux c args s h
          | var _ => simp [translateHE, isForbiddenHeadSymbol]
          | grounded _ => simp [translateHE, isForbiddenHeadSymbol]
          | expression _ => simp [translateHE, isForbiddenHeadSymbol]

private theorem translateHE_preserves_stableCommonHead_aux
    (a : Atom) (s : Nat) (h : isValidatedHEHeadSource a = true) :
    isStableCommonHead (translateHE a s).1 = true := by
  have hsrc := validatedHESource_of_headSource_aux a h
  have hform := translateHE_preserves_stableCommonForm_aux a s hsrc
  have hnot := translateHE_notForbidden_of_headSource_aux a s h
  simp [isStableCommonHead, hform, hnot]

private theorem translateHEList_preserves_stableCommonList_aux
    (xs : List Atom) (s : Nat) (h : isValidatedHEList xs = true) :
    isStableCommonList (translateHE.translateHEList xs s).1 = true := by
  cases xs with
  | nil => simp [translateHE.translateHEList, isStableCommonList]
  | cons x xs =>
    simp [isValidatedHEList, Bool.and_eq_true] at h
    have hx : isStableCommonForm (translateHE x s).1 = true :=
      translateHE_preserves_stableCommonForm_aux x s h.1
    have hxs :
        isStableCommonList (translateHE.translateHEList xs (translateHE x s).2).1 = true :=
      translateHEList_preserves_stableCommonList_aux xs (translateHE x s).2 h.2
    simp [translateHE.translateHEList, isStableCommonList, hx, hxs]
end

theorem translateHE_preserves_stableCommonForm (a : Atom) (s : Nat)
    (h : isValidatedHESource a = true) :
    isStableCommonForm (translateHE a s).1 = true :=
  translateHE_preserves_stableCommonForm_aux a s h





end Mettapedia.Languages.MeTTa.Translation
