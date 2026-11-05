import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedResidual

/-!
# Patterns that quote guards: alpha-unification on closed forms

The executable COMM refuses a pattern that contains a guard, so two inputs
whose patterns quote alpha-equivalent guards never meet
(`NominalControls.guard_quoting_partners_refused`). A pattern that quotes a
guard binds names inside the quotation, and unifying two such patterns must
compare them up to those bound names, which is the problem nominal
unification solves.

On the closed form every bound name is a code, and codes are compared as
constants. This module proves the bridge that reduces the problem to
first-order unification: closing commutes with a substitution of closed
values that captures nothing (`closeIn_psubst_closed`). Hence such a
substitution unifies two patterns up to alpha exactly when it unifies their
closed forms as first-order terms (`alphaEq_psubst_iff`).

A first-order unifier of closed forms can bind a pattern variable to a code
that a quoted guard binds, which no value can denote: the variable would
escape its scope. Such a pair has no capture-free unifier at all
(`NominalControls.escaping_code_has_no_unifier`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm
  (psubst pvars PSubst)

/-! ## Closed values -/

/-- Binding variables an environment does not bind changes nothing. -/
theorem abstractAt_of_unbound (env : List (List String)) (v : Pattern) :
    ∀ depth, (∀ w ∈ pvars v, lookupBound env w = none) → abstractAt env depth v = v := by
  induction v using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ depth,
      (∀ w ∈ pvars q, lookupBound env w = none) → abstractAt env depth q = q) with
  | bvar n => intro _ _; rfl
  | fvar x => intro _ unbound; simp [abstractAt, unbound x (by simp [pvars])]
  | apply c args ih =>
      intro depth unbound
      have each : ∀ q ∈ args, ∀ d, abstractAt env d q = q := fun q member d =>
        ih q member d fun w occurs => unbound w (mem_pvars_apply_of member occurs)
      simp only [abstractAt]
      congr 1
      split
      · match args with
        | [] => rfl
        | [p] => simp [abstractFor, each p (by simp)]
        | [p, q] => simp [abstractFor, each p (by simp), each q (by simp)]
        | t :: x :: k :: rest =>
            simp only [abstractFor, abstractList_eq_map]
            rw [each x (by simp), each k (by simp)]
            congr 3
            conv_rhs => rw [← List.map_id rest]
            exact List.map_congr_left fun q member => each q (by simp [member]) depth
      · rw [abstractList_eq_map]
        conv_rhs => rw [← List.map_id args]
        exact List.map_congr_left fun q member => each q member depth
  | lambda nm body ih =>
      intro depth unbound
      simp [abstractAt, ih depth fun w occurs => unbound w (by simpa [pvars] using occurs)]
  | multiLambda n nms body ih =>
      intro depth unbound
      simp [abstractAt, ih depth fun w occurs => unbound w (by simpa [pvars] using occurs)]
  | subst body repl ihb ihr =>
      intro depth unbound
      simp [abstractAt, ihb depth fun w occurs => unbound w (by simp [pvars, occurs]),
        ihr depth fun w occurs => unbound w (by simp [pvars, occurs])]
  | collection ct elems rest ih =>
      intro depth unbound
      simp only [abstractAt, abstractList_eq_map]
      congr 1
      conv_rhs => rw [← List.map_id elems]
      exact List.map_congr_left fun q member =>
        ih q member depth fun w occurs => unbound w (mem_pvars_collection_of member occurs)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member depth unbound
      rcases List.mem_cons.mp member with rfl | later
      · exact head depth unbound
      · exact tail q later depth unbound

/-- A closed form whose free names an environment does not bind is closed in it. -/
theorem closeIn_of_closed {env : List (List String)} {g : Pattern} (closed : close g = g)
    (unbound : ∀ w ∈ pvars g, lookupBound env w = none) : closeIn env g = g := by
  have split := closeIn_append g [] env
  simp only [List.nil_append, List.length_nil] at split
  rw [split]
  show abstractAt env 0 (close g) = g
  rw [closed]
  exact abstractAt_of_unbound env g 0 unbound

/-- A substitution captures nothing in `t`, below the frames `env`: each value
is a closed form, and neither a substituted variable nor a name of its value is
bound by a guard of `t` or by `env`. -/
def CaptureFree (s : PSubst) (t : Pattern) (env : List (List String)) : Prop :=
  ∀ v ∈ pvars t, ∀ g, s v = some g → close g = g ∧ v ∉ binders t ∧ (∀ f ∈ env, v ∉ f) ∧
    ∀ w ∈ pvars g, w ∉ binders t ∧ ∀ f ∈ env, w ∉ f

/-- **Closing commutes with a capture-free substitution of closed values.**
Patterns may quote guards: a guard binds the variables of its own pattern,
which a capture-free substitution never moves. -/
theorem closeIn_psubst_closed (s : PSubst) (t : Pattern) (calcT : calcTerm t = true) :
    ∀ env : List (List String), CaptureFree s t env →
      closeIn env (psubst s t) = psubst s (closeIn env t) := by
  induction t using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, calcTerm q = true →
      ∀ env : List (List String), CaptureFree s q env →
        closeIn env (psubst s q) = psubst s (closeIn env q)) with
  | bvar n => simp [calcTerm] at calcT
  | fvar v =>
      intro env capture
      cases sv : s v with
      | none =>
          cases found : lookupBound env v with
          | none => simp [psubst, sv, closeIn, found]
          | some position => simp [psubst, sv, closeIn, found, boundCode]
      | some g =>
          obtain ⟨closed, _, vOut, gOut⟩ := capture v (by simp [pvars]) g sv
          have vFree : lookupBound env v = none := lookupBound_none_of_not_mem vOut
          simp only [psubst, sv, Option.getD_some, closeIn, vFree]
          exact closeIn_of_closed closed fun w occurs =>
            lookupBound_none_of_not_mem (gOut w occurs).2
  | apply c args ih =>
      intro env capture
      simp only [calcTerm, calcList_iff] at calcT
      have captureArg : ∀ q ∈ args, (∀ w ∈ binders q, w ∈ binders (.apply c args)) →
          CaptureFree s q env := by
        intro q member sub v occurs g sv
        obtain ⟨closed, vNot, vEnv, gNot⟩ := capture v (mem_pvars_apply_of member occurs) g sv
        exact ⟨closed, fun bound => vNot (sub v bound), vEnv,
          fun w occurs' => ⟨fun bound => (gNot w occurs').1 (sub w bound), (gNot w occurs').2⟩⟩
      rw [show psubst s (.apply c args) = .apply c (args.map (psubst s)) by
        simp [psubst, psubstList_eq_map]]
      rw [closeIn_apply, closeIn_apply]
      simp only [psubst, psubstList_eq_map]
      by_cases guard : c = "MFor"
      · subst guard
        simp only [if_true]
        by_cases short : args.length < 3
        · rcases closeFor_cases env (args.map (psubst s)) with ⟨_, eq⟩ | ⟨_, _, _, _, same, _⟩
          · rcases closeFor_cases env args with ⟨_, eq'⟩ | ⟨_, _, _, _, rfl, _⟩
            · rw [eq, eq', List.map_map, List.map_map]
              congr 1
              apply List.map_congr_left
              intro q member
              exact ih q member (calcT q member) env (captureArg q member fun w bound => by
                rw [binders_apply, if_pos rfl, bindersFor_short _ short]
                exact List.mem_flatMap.mpr ⟨q, member, bound⟩)
            · exact absurd short (by simp)
          · have := congrArg List.length same; simp at this; omega
        · match args, short with
          | [_], h => simp at h
          | [_, _], h => simp at h
          | t :: x :: k :: rest, _ =>
              have bindersIs : binders (.apply "MFor" (t :: x :: k :: rest)) =
                  pvars t ++ binders x ++ binders k ++ rest.flatMap binders := by
                rw [binders_apply, if_pos rfl, bindersFor_cons3]
              have tFixed : psubst s t = t := psubst_of_none s t fun v occurs => by
                cases sv : s v with
                | none => rfl
                | some g =>
                    exfalso
                    obtain ⟨_, vNot, _, _⟩ := capture v (mem_pvars_apply_of (by simp) occurs) g sv
                    exact vNot (by rw [bindersIs]; simp [occurs])
              simp only [List.map_cons]
              rw [tFixed, closeFor_cons3, closeFor_cons3]
              simp only [List.map_cons]
              have patternFixed : psubst s (closeIn [frame t] t) = closeIn [frame t] t :=
                Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm.psubst_of_pvars_nil
                  s _ (pvars_closed_pattern t)
              rw [patternFixed]
              congr 1
              refine List.cons_eq_cons.mpr ⟨rfl, ?_⟩
              refine List.cons_eq_cons.mpr ⟨ih x (by simp) (calcT x (by simp)) env
                (captureArg x (by simp) fun w bound => by rw [bindersIs]; simp [bound]), ?_⟩
              refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
              · apply ih k (by simp) (calcT k (by simp)) (frame t :: env)
                intro v occurs g sv
                obtain ⟨closed, vNot, vEnv, gNot⟩ :=
                  capture v (mem_pvars_apply_of (by simp) occurs) g sv
                refine ⟨closed, fun bound => vNot (by rw [bindersIs]; simp [bound]), ?_, ?_⟩
                · intro f member
                  rcases List.mem_cons.mp member with rfl | later
                  · exact fun inFrame => vNot (by rw [bindersIs]; simp [frame_subset t v inFrame])
                  · exact vEnv f later
                · intro w occurs'
                  refine ⟨fun bound => (gNot w occurs').1 (by rw [bindersIs]; simp [bound]), ?_⟩
                  intro f member
                  rcases List.mem_cons.mp member with rfl | later
                  · exact fun inFrame => (gNot w occurs').1 (by rw [bindersIs]; simp [frame_subset t w inFrame])
                  · exact (gNot w occurs').2 f later
              · simp only [List.map_map]
                apply List.map_congr_left
                intro q member
                exact ih q (by simp [member]) (calcT q (by simp [member])) env
                  (captureArg q (by simp [member]) fun w bound => by
                    rw [bindersIs]
                    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, member, bound⟩))
      · simp only [guard, if_false, List.map_map]
        congr 1
        apply List.map_congr_left
        intro q member
        exact ih q member (calcT q member) env (captureArg q member fun w bound => by
          rw [binders_apply, if_neg guard]
          exact List.mem_flatMap.mpr ⟨q, member, bound⟩)
  | lambda nm body ih => simp [calcTerm] at calcT
  | multiLambda n nms body ih => simp [calcTerm] at calcT
  | subst body repl ihb ihr => simp [calcTerm] at calcT
  | collection ct elems rest ih =>
      intro env capture
      simp only [calcTerm, Bool.and_eq_true, Option.isNone_iff_eq_none, calcList_iff] at calcT
      obtain ⟨rfl, calcT⟩ := calcT
      simp only [psubst, psubstList_eq_map, closeIn, closeList_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q member
      apply ih q member (calcT q member) env
      intro v occurs g sv
      obtain ⟨closed, vNot, vEnv, gNot⟩ := capture v (mem_pvars_collection_of member occurs) g sv
      have sub : ∀ w ∈ binders q, w ∈ binders (.collection ct elems none) := fun w bound => by
        simp only [binders, bindersList_eq_flatMap]
        exact List.mem_flatMap.mpr ⟨q, member, bound⟩
      exact ⟨closed, fun bound => vNot (sub v bound), vEnv,
        fun w occurs' => ⟨fun bound => (gNot w occurs').1 (sub w bound), (gNot w occurs').2⟩⟩
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member calcQ env capture
      rcases List.mem_cons.mp member with rfl | later
      · exact head calcQ env capture
      · exact tail q later calcQ env capture

/-- **Alpha-unification is first-order unification of closed forms.** A
capture-free substitution of closed values unifies two calculus patterns up
to alpha exactly when it unifies their closed forms, on which a bound name is
a code compared as a constant. Patterns may quote guards. -/
theorem alphaEq_psubst_iff (s : PSubst) {t u : Pattern} (calcT : calcTerm t = true)
    (calcU : calcTerm u = true) (captureT : CaptureFree s t []) (captureU : CaptureFree s u []) :
    AlphaEq (psubst s t) (psubst s u) ↔ psubst s (close t) = psubst s (close u) := by
  unfold AlphaEq close
  rw [closeIn_psubst_closed s t calcT [] captureT, closeIn_psubst_closed s u calcU [] captureU]

/-! ## The first-order unifier of the closed forms -/

mutual
/-- Every code refers to a guard of the term: below `depth` enclosing guards,
a code bound `d` guards out, with `d < depth`, is bound. A guard's pattern is
closed in its own frame alone. -/
def codesBound (depth : ℕ) : Pattern → Bool
  | .bvar c => decide ((Nat.unpair c).1 < depth)
  | .fvar _ => true
  | .apply c args => if c = "MFor" then codesBoundFor depth args else codesBoundList depth args
  | .lambda _ body => codesBound depth body
  | .multiLambda _ _ body => codesBound depth body
  | .subst body repl => codesBound depth body && codesBound depth repl
  | .collection _ elems _ => codesBoundList depth elems
def codesBoundList (depth : ℕ) : List Pattern → Bool
  | [] => true
  | p :: ps => codesBound depth p && codesBoundList depth ps
def codesBoundFor (depth : ℕ) : List Pattern → Bool
  | [] => true
  | [p] => codesBound depth p
  | [p, q] => codesBound depth p && codesBound depth q
  | t :: x :: k :: rest =>
      codesBound 1 t && codesBound depth x && codesBound (depth + 1) k && codesBoundList depth rest
end

theorem codesBoundList_iff (depth : ℕ) (ps : List Pattern) :
    codesBoundList depth ps = true ↔ ∀ p ∈ ps, codesBound depth p = true := by
  induction ps with
  | nil => simp [codesBoundList]
  | cons p ps ih => simp [codesBoundList, ih]

/-- A free code survives substitution: substitution replaces variables and
keeps every code. -/
theorem codesBound_of_psubst (s : PSubst) (g : Pattern) :
    ∀ depth, codesBound depth (psubst s g) = true → codesBound depth g = true := by
  induction g using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ depth,
      codesBound depth (psubst s q) = true → codesBound depth q = true) with
  | bvar n => intro depth h; simpa [psubst] using h
  | fvar x => intro _ _; rfl
  | apply c args ih =>
      intro depth h
      simp only [psubst, psubstList_eq_map, codesBound] at h ⊢
      by_cases guard : c = "MFor"
      · simp only [guard, if_true] at h ⊢
        match args, h with
        | [], _ => rfl
        | [p], h =>
            simp only [List.map_cons, List.map_nil, codesBoundFor] at h ⊢
            exact ih p (by simp) depth h
        | [p, q], h =>
            simp only [List.map_cons, List.map_nil, codesBoundFor, Bool.and_eq_true] at h ⊢
            exact ⟨ih p (by simp) depth h.1, ih q (by simp) depth h.2⟩
        | t :: x :: k :: rest, h =>
            simp only [List.map_cons, codesBoundFor, Bool.and_eq_true, codesBoundList_iff,
              List.mem_map] at h ⊢
            refine ⟨⟨⟨ih t (by simp) 1 h.1.1.1, ih x (by simp) depth h.1.1.2⟩,
              ih k (by simp) (depth + 1) h.1.2⟩, ?_⟩
            intro q member
            exact ih q (by simp [member]) depth (h.2 _ ⟨q, member, rfl⟩)
      · simp only [guard, if_false, codesBoundList_iff, List.mem_map] at h ⊢
        intro q member
        exact ih q member depth (h _ ⟨q, member, rfl⟩)
  | lambda nm body ih => intro depth h; exact ih depth (by simpa [psubst, codesBound] using h)
  | multiLambda n nms body ih => intro depth h; exact ih depth (by simpa [psubst, codesBound] using h)
  | subst body repl ihb ihr =>
      intro depth h
      simp only [psubst, codesBound, Bool.and_eq_true] at h ⊢
      exact ⟨ihb depth h.1, ihr depth h.2⟩
  | collection ct elems rest ih =>
      intro depth h
      simp only [psubst, psubstList_eq_map, codesBound, codesBoundList_iff, List.mem_map] at h ⊢
      intro q member
      exact ih q member depth (h _ ⟨q, member, rfl⟩)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member depth h
      rcases List.mem_cons.mp member with rfl | later
      · exact head depth h
      · exact tail q later depth h

/-- **The unifier of the closed forms is principal among capture-free
alpha-unifiers.** A capture-free substitution that unifies two patterns up to
alpha unifies their closed forms, so the first-order unifier of the closed
forms exists and the substitution absorbs it. -/
theorem alpha_unifier_absorbs (s : PSubst) {t u : Pattern} (calcT : calcTerm t = true)
    (calcU : calcTerm u = true) (captureT : CaptureFree s t []) (captureU : CaptureFree s u [])
    (alpha : AlphaEq (psubst s t) (psubst s u)) :
    ∃ bs, unify (close t) (close u) = some bs ∧ ∀ p, psubst s (psubst bs.lookup p) = psubst s p := by
  have closed := (alphaEq_psubst_iff s calcT calcU captureT captureU).mp alpha
  obtain ⟨bs, found⟩ := unify_complete ⟨s, closed⟩
  exact ⟨bs, found, unify_most_general found s closed⟩

/-- **An escaping code rules out every capture-free alpha-unifier.** When the
unifier of the closed forms binds a variable to a value with a free code, a
code that a quoted guard binds, no capture-free substitution whose values
have no free code unifies the two patterns up to alpha. -/
theorem no_alpha_unifier_of_escaping {t u : Pattern} (calcT : calcTerm t = true)
    (calcU : calcTerm u = true) {bs : Bindings} (found : unify (close t) (close u) = some bs)
    {v : String} {g : Pattern} (bound : bs.lookup v = some g) (escapes : codesBound 0 g = false)
    (s : PSubst) (captureT : CaptureFree s t []) (captureU : CaptureFree s u [])
    (codeFree : ∀ w h, s w = some h → codesBound 0 h = true) :
    ¬ AlphaEq (psubst s t) (psubst s u) := by
  intro alpha
  have closed := (alphaEq_psubst_iff s calcT calcU captureT captureU).mp alpha
  have absorbs := unify_most_general found s closed (.fvar v)
  simp only [psubst, bound, Option.getD_some] at absorbs
  have readOff : codesBound 0 (psubst s g) = true := by
    rw [absorbs]
    cases sv : s v with
    | none => rfl
    | some h => exact codeFree v h sv
  have := codesBound_of_psubst s g 0 readOff
  rw [escapes] at this
  cases this

/-! ## Controls -/

namespace NominalControls

/-- A quoted guard that binds `y`, and its alpha-variant binding `z`. -/
def quotedY : Pattern := tProc (pFor (.fvar "y") demoChan (.fvar "y"))
def quotedZ : Pattern := tProc (pFor (.fvar "z") demoChan (.fvar "z"))

/-- Two inputs whose patterns quote alpha-equivalent guards. -/
def quotingPartners : Proc := par (pFor quotedY demoChan pZero) (pFor quotedZ demoChan pZero)

/-- **The executable refuses patterns that quote guards.** The two patterns
are alpha-equivalent, so the empty substitution unifies them up to alpha,
yet no COMM fires. -/
theorem guard_quoting_partners_refused :
    AlphaEq quotedY quotedZ ∧ cstep quotingPartners = [] := by
  constructor <;> decide +kernel

/-- The same pair, by the bridge: the closed forms are equal as first-order terms. -/
theorem guard_quoting_closed_forms_equal : close quotedY = close quotedZ := by decide +kernel

/-- A quoted guard whose continuation mentions the outer pattern variable `X`. -/
def quotedX : Pattern := tProc (pFor (.fvar "y") demoChan (.fvar "X"))

/-- First-order unification of the closed forms succeeds, binding `X` to the
code of the name the quoted guard binds. -/
theorem escaping_code_unifier :
    unify (close quotedX) (close quotedZ) = some [("X", .bvar (Nat.pair 0 0))] := by
  decide +kernel

/-- **An escaping code has no capture-free unifier.** No substitution of closed
values without free codes unifies the two patterns up to alpha: `X` would have
to denote the name bound inside the quotation. -/
theorem escaping_code_has_no_unifier (s : PSubst) (captureX : CaptureFree s quotedX [])
    (captureZ : CaptureFree s quotedZ []) (codeFree : ∀ v g, s v = some g → codesBound 0 g = true) :
    ¬ AlphaEq (psubst s quotedX) (psubst s quotedZ) :=
  no_alpha_unifier_of_escaping (by decide +kernel) (by decide +kernel) escaping_code_unifier
    (v := "X") (g := .bvar (Nat.pair 0 0)) (by decide +kernel) (by simp [codesBound]) s captureX captureZ
    codeFree

end NominalControls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected
