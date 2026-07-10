import Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp
import Mettapedia.GSLT.LanguageDef.LFEngineShiftSim

/-!
# MeTTa self-interpreter encoding frontier

This module is the Stage-2(b) encoding layer for the verified MeTTa
self-interpreter.  It connects ordinary `MeTTaIL` terms and base rewrite
declarations to the data representation consumed by
`Corpus.SelfInterp.pMI`.

Semantic sources: the target reference semantics is LeaTTa/MOPS-style
deterministic rewriting as exposed here by `MeTTaIL.oneStep` and
`MeTTaIL.eval`; the matching boundary is the same first-order matching shape
tracked by the HE `DeclMatchSpec` work.

Fragment v1: the deterministic MOPS core needed by the equality-rule corpus
entries -- `(= lhs rhs)` equalities, first-order `$`-variable matching,
leftmost reduction, fuel-bounded normalization.

Excluded here: `superpose`/`collapse` nondeterminism, grounded guest
operations, spaces/state.  The finite entry-04 immutable fact-table query is
handled in `Corpus.SelfInterp`; it is not part of this generic base-rewrite
encoding.

Integrity: this file contains only computable definitions and kernel-reduced
examples.  Unsupported syntax returns `none`; it is never silently projected
into the core fragment.
-/

namespace Mettapedia.GSLT.LanguageDef.MIEvalEncoding

open MeTTaIL

open Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp

/-! ## Guest syntax builders used by examples -/

def gCon0 (s : String) : AST := .sexp (.id s) []
def gApp (s : String) (args : List AST) : AST := .sexp (.id s) args
def gVar (v : String) : AST := .var (.base v)
def gRw (name : String) (lhs rhs : AST) : RewriteDecl :=
  { name := name, rw := .base lhs rhs }

def gZ : AST := gCon0 "Z"
def gS (n : AST) : AST := gApp "S" [n]
def gAdd (x y : AST) : AST := gApp "add" [x, y]
def gNil : AST := gCon0 "Nil"
def gCons (x xs : AST) : AST := gApp "Cons" [x, xs]
def gListAppend (x y : AST) : AST := gApp "listAppend" [x, y]
def gRev (x : AST) : AST := gApp "rev" [x]

def gOne : AST := gS gZ
def gTwo : AST := gS gOne
def gThree : AST := gS gTwo

def gList012 : AST := gCons gZ (gCons gOne (gCons gTwo gNil))
def gList210 : AST := gCons gTwo (gCons gOne (gCons gZ gNil))

/-! ## Total fragment encoders -/

mutual
  def encAST? : AST -> Option AST
    | .var (.base v) => some (MIVar v)
    | .var (.qualified _ _) => none
    | .sexp (.id s) [] => some (MISym s)
    | .sexp (.id s) args =>
        match encASTList? args with
        | some encodedArgs => some (MIApp s encodedArgs)
        | none => none
    | .sexp _ _ => none
    | .subst _ _ _ => none

  def encASTList? : List AST -> Option AST
    | [] => some MINil
    | t :: ts =>
        match encAST? t, encASTList? ts with
        | some encodedT, some encodedTs => some (MICons encodedT encodedTs)
        | _, _ => none
end

def encRewriteDecl? (rd : RewriteDecl) : Option AST :=
  match rd.rw with
  | .base lhs rhs =>
      match encAST? lhs, encAST? rhs with
      | some encodedLhs, some encodedRhs => some (MIRule encodedLhs encodedRhs)
      | _, _ => none
  | .ctx _ _ => none

def encRules? : List RewriteDecl -> Option AST
  | [] => some MIRNil
  | rd :: rest =>
      match encRewriteDecl? rd, encRules? rest with
      | some encodedRule, some encodedRest => some (MIRCons encodedRule encodedRest)
      | _, _ => none

def encBinds? : List (String × AST) -> Option AST
  | [] => some MIBNil
  | (v, t) :: rest =>
      match encAST? t, encBinds? rest with
      | some encodedTerm, some encodedRest =>
          some (MIBCons (con0 v) encodedTerm encodedRest)
      | _, _ => none

def lookupEncoded? (v : String) : List (String × AST) -> Option AST
  | [] => none
  | (w, t) :: rest =>
      if v == w then encAST? t else lookupEncoded? v rest

def inCoreAST (t : AST) : Bool := (encAST? t).isSome
def inCoreRewriteDecl (rd : RewriteDecl) : Bool := (encRewriteDecl? rd).isSome
def inCoreRules (rws : List RewriteDecl) : Bool := (encRules? rws).isSome

mutual
  def noQueryAST : AST → Bool
    | .var (.base _) => true
    | .var (.qualified _ _) => false
    | .sexp (.id _) [] => true
    | .sexp (.id h) args@(_ :: _) =>
        ((h == "match") == false) && noQueryASTList args
    | .sexp _ _ => false
    | .subst _ _ _ => false

  def noQueryASTList : List AST → Bool
    | [] => true
    | t :: ts => noQueryAST t && noQueryASTList ts
end

def BindsNoQuery : List (String × AST) → Prop
  | [] => True
  | (_, t) :: rest => noQueryAST t = true ∧ BindsNoQuery rest

def RewriteDeclPreservesNoQuery (rd : RewriteDecl) : Prop :=
  match rd.rw with
  | .base _ rhs => noQueryAST rhs = true
  | .ctx _ _ => True

def RulesPreserveNoQuery : List RewriteDecl → Prop
  | [] => True
  | rd :: rest => RewriteDeclPreservesNoQuery rd ∧ RulesPreserveNoQuery rest

theorem bool_and_left_true_mi {a b : Bool} (h : a && b = true) : a = true := by
  cases a <;> cases b <;> simp at h ⊢

theorem bool_and_right_true_mi {a b : Bool} (h : a && b = true) : b = true := by
  cases a <;> cases b <;> simp at h ⊢

theorem noQueryASTList_of_noQueryAST_sexp (l : Label) (args : List AST)
    (hno : noQueryAST (.sexp l args) = true) :
    noQueryASTList args = true := by
  cases l with
  | id h =>
      cases args with
      | nil => simp [noQueryASTList]
      | cons a rest =>
          have hno' :
              (((h == "match") == false) &&
                noQueryASTList (a :: rest)) = true := by
            simpa [noQueryAST] using hno
          cases hhead : ((h == "match") == false) <;> simp [hhead] at hno'
          exact hno'
  | wild =>
      simp only [noQueryAST] at hno
      cases hno
  | listE c =>
      simp only [noQueryAST] at hno
      cases hno
  | listCons c =>
      simp only [noQueryAST] at hno
      cases hno
  | listOne c =>
      simp only [noQueryAST] at hno
      cases hno

theorem mivar_ne_miapp (ident h : String) (encodedArgs : AST) :
    MIVar ident ≠ MIApp h encodedArgs := by
  intro hterm
  simp only [MIVar, MIApp, app] at hterm
  injection hterm with hlabel _hargs
  injection hlabel with hstr
  have hneq : ("MIVar" : String) ≠ "MIApp" := by decide
  exact hneq hstr

theorem misym_ne_miapp (s h : String) (encodedArgs : AST) :
    MISym s ≠ MIApp h encodedArgs := by
  intro hterm
  simp only [MISym, MIApp, app] at hterm
  injection hterm with hlabel _hargs
  injection hlabel with hstr
  have hneq : ("MISym" : String) ≠ "MIApp" := by decide
  exact hneq hstr

theorem encAST_noQuery_miapp_head_ne
    (term : AST) (headName : String) (encodedArgs : AST)
    (hterm : encAST? term = some (MIApp headName encodedArgs))
    (hno : noQueryAST term = true) :
    (headName == "match") = false := by
  cases term with
  | var path =>
      cases path with
      | base ident =>
          simp only [encAST?] at hterm
          injection hterm with hterm'
          exact False.elim
            (mivar_ne_miapp ident headName encodedArgs hterm')
      | qualified ident rest =>
          simp only [encAST?] at hterm
          cases hterm
  | sexp label args =>
      cases label with
      | id s =>
          cases args with
          | nil =>
              simp only [encAST?] at hterm
              injection hterm with hterm'
              exact False.elim
                (misym_ne_miapp s headName encodedArgs hterm')
          | cons a rest =>
              cases hargs : encASTList? (a :: rest) with
              | none =>
                  simp only [encAST?, hargs] at hterm
                  cases hterm
              | some encodedArgs' =>
                  simp only [encAST?, hargs] at hterm
                  cases hterm
                  have hnoApp :
                      (((headName == "match") == false) &&
                        noQueryASTList (a :: rest)) = true := by
                    simpa [noQueryAST] using hno
                  cases hm : (headName == "match") with
                  | false => rfl
                  | true => simp [hm] at hnoApp
      | wild =>
          simp only [encAST?] at hterm
          cases hterm
      | listE c =>
          simp only [encAST?] at hterm
          cases hterm
      | listCons c =>
          simp only [encAST?] at hterm
          cases hterm
      | listOne c =>
          simp only [encAST?] at hterm
          cases hterm
  | subst body repl v =>
      simp [encAST?] at hterm

theorem noQueryAST_inst_var_base (v : String) :
    ∀ (bs : List (String × AST)),
      BindsNoQuery bs →
      noQueryAST (AST.inst bs (.var (.base v))) = true
  | [], _ => by
      simp [AST.inst, noQueryAST]
  | (w, t) :: rest, hbs => by
      obtain ⟨ht, hrest⟩ := hbs
      cases hcmp : (w == v) with
      | false =>
          simpa [AST.inst, List.find?, hcmp] using
            noQueryAST_inst_var_base v rest hrest
      | true =>
          simp [AST.inst, List.find?, hcmp, ht]

mutual
  theorem noQueryAST_inst_preserves :
      ∀ (term : AST) (bs : List (String × AST)),
        noQueryAST term = true →
        BindsNoQuery bs →
        noQueryAST (AST.inst bs term) = true
    | .var (.base v), bs, _hno, hbs => by
        exact noQueryAST_inst_var_base v bs hbs
    | .var (.qualified _ _), _bs, hno, _hbs => by
        simp only [noQueryAST] at hno
        cases hno
    | .sexp (.id h) [], _bs, _hno, _hbs => by
        simp [AST.inst, AST.instList, noQueryAST]
    | .sexp (.id h) (a :: rest), bs, hno, hbs => by
        have hno' :
            (((h == "match") == false) &&
              noQueryASTList (a :: rest)) = true := by
          simpa [noQueryAST] using hno
        have hh : ((h == "match") == false) = true := by
          cases hhead : ((h == "match") == false) <;> simp [hhead] at hno' ⊢
        have hargs : noQueryASTList (a :: rest) = true := by
          cases hhead : ((h == "match") == false) <;> simp [hhead] at hno'
          exact hno'
        have hargsInst :=
          noQueryASTList_inst_preserves (a :: rest) bs hargs hbs
        simpa [AST.inst, AST.instList, noQueryAST, hh, hargsInst]
    | .sexp .wild _, _bs, hno, _hbs => by
        simp only [noQueryAST] at hno
        cases hno
    | .sexp (.listE _) _, _bs, hno, _hbs => by
        simp only [noQueryAST] at hno
        cases hno
    | .sexp (.listCons _) _, _bs, hno, _hbs => by
        simp only [noQueryAST] at hno
        cases hno
    | .sexp (.listOne _) _, _bs, hno, _hbs => by
        simp only [noQueryAST] at hno
        cases hno
    | .subst _ _ _, _bs, hno, _hbs => by
        simp only [noQueryAST] at hno
        cases hno

  theorem noQueryASTList_inst_preserves :
      ∀ (terms : List AST) (bs : List (String × AST)),
        noQueryASTList terms = true →
        BindsNoQuery bs →
        noQueryASTList (AST.instList bs terms) = true
    | [], _bs, _hno, _hbs => by
        simp [AST.instList, noQueryASTList]
    | t :: ts, bs, hno, hbs => by
        have hno' : (noQueryAST t && noQueryASTList ts) = true := by
          simpa [noQueryASTList] using hno
        have ht : noQueryAST t = true := by
          cases ht : noQueryAST t <;> simp [ht] at hno' ⊢
        have hts : noQueryASTList ts = true := by
          cases ht : noQueryAST t <;> simp [ht] at hno'
          exact hno'
        have htInst := noQueryAST_inst_preserves t bs ht hbs
        have htsInst := noQueryASTList_inst_preserves ts bs hts hbs
        simp [AST.instList, noQueryASTList, htInst, htsInst]
end

mutual
  theorem matchPat_preserves_noQueryBindings :
      ∀ (pat term : AST) (bs bsOut : List (String × AST)),
        noQueryAST term = true →
        BindsNoQuery bs →
        AST.matchPat pat term bs = some bsOut →
        BindsNoQuery bsOut
    | .var (.base v), term, bs, bsOut, hterm, hbs, hmatch => by
        simp only [AST.matchPat] at hmatch
        cases hfind : List.find? (fun b : String × AST => b.fst == v) bs with
        | none =>
            simp only [hfind] at hmatch
            cases hmatch
            exact ⟨hterm, hbs⟩
        | some pair =>
            rcases pair with ⟨_, old⟩
            simp only [hfind] at hmatch
            cases hcmp : (old == term) with
            | false =>
                simp only [hcmp, Bool.false_eq_true, if_false] at hmatch
                cases hmatch
            | true =>
                simp only [hcmp, if_true] at hmatch
                cases hmatch
                exact hbs
    | .var (.qualified ident rest), term, bs, bsOut, _hterm, hbs, hmatch => by
        simp only [AST.matchPat] at hmatch
        cases hcmp : (AST.var (.qualified ident rest) == term) with
        | false =>
            simp only [hcmp, Bool.false_eq_true, if_false] at hmatch
            cases hmatch
        | true =>
            simp only [hcmp, if_true] at hmatch
            cases hmatch
            exact hbs
    | .sexp l ps, .sexp m ts, bs, bsOut, hterm, hbs, hmatch => by
        simp only [AST.matchPat] at hmatch
        cases hcmp : (l == m) with
        | false =>
            simp only [hcmp, Bool.false_eq_true, if_false] at hmatch
            cases hmatch
        | true =>
            simp only [hcmp, if_true] at hmatch
            have hts : noQueryASTList ts = true :=
              noQueryASTList_of_noQueryAST_sexp m ts hterm
            exact matchPatList_preserves_noQueryBindings ps ts bs bsOut
              hts hbs hmatch
    | .sexp _ _, .var _, _bs, _bsOut, _hterm, _hbs, hmatch => by
        simp [AST.matchPat, BEq.beq, AST.beq] at hmatch
    | .sexp _ _, .subst _ _ _, _bs, _bsOut, hterm, _hbs, _hmatch => by
        simp only [noQueryAST] at hterm
        cases hterm
    | .subst _ _ _, .subst _ _ _, _bs, _bsOut, hterm, _hbs, _hmatch => by
        simp only [noQueryAST] at hterm
        cases hterm
    | .subst _ _ _, .var _, _bs, _bsOut, _hterm, _hbs, hmatch => by
        simp [AST.matchPat, BEq.beq, AST.beq] at hmatch
    | .subst _ _ _, .sexp _ _, _bs, _bsOut, _hterm, _hbs, hmatch => by
        simp [AST.matchPat, BEq.beq, AST.beq] at hmatch

  theorem matchPatList_preserves_noQueryBindings :
      ∀ (pats terms : List AST) (bs bsOut : List (String × AST)),
        noQueryASTList terms = true →
        BindsNoQuery bs →
        AST.matchPatList pats terms bs = some bsOut →
        BindsNoQuery bsOut
    | [], [], bs, bsOut, _hterms, hbs, hmatch => by
        simp only [AST.matchPatList] at hmatch
        cases hmatch
        exact hbs
    | [], _ :: _, _bs, _bsOut, _hterms, _hbs, hmatch => by
        simp only [AST.matchPatList] at hmatch
        cases hmatch
    | _ :: _, [], _bs, _bsOut, _hterms, _hbs, hmatch => by
        simp only [AST.matchPatList] at hmatch
        cases hmatch
    | p :: ps, t :: ts, bs, bsOut, hterms, hbs, hmatch => by
        have hterms' : noQueryAST t && noQueryASTList ts = true := by
          simpa [noQueryASTList] using hterms
        have ht : noQueryAST t = true := by
          cases ht : noQueryAST t <;> simp [ht] at hterms' ⊢
        have hts : noQueryASTList ts = true := by
          cases ht : noQueryAST t <;> simp [ht] at hterms'
          exact hterms'
        simp only [AST.matchPatList] at hmatch
        cases hhead : AST.matchPat p t bs with
        | none =>
            simp only [hhead, Option.bind_none] at hmatch
            cases hmatch
        | some bsMid =>
            simp only [hhead, Option.bind_some] at hmatch
            have hmid :=
              matchPat_preserves_noQueryBindings p t bs bsMid ht hbs
                hhead
            exact matchPatList_preserves_noQueryBindings ps ts bsMid
              bsOut hts hmid hmatch
end

def pOf (rws : List RewriteDecl) : Presentation := .mk [] [] [] rws []

def rootBaseStep? : List RewriteDecl → AST → Option AST
  | [], _ => none
  | rd :: rest, term =>
      match rd.rw with
      | .base lhs rhs =>
          match AST.matchPat lhs term [] with
          | some bs => some (AST.inst bs rhs)
          | none => rootBaseStep? rest term
      | .ctx _ _ => rootBaseStep? rest term

mutual
  def astFuel : AST → Nat
    | .var _ => 1
    | .sexp _ args => astListFuel args + 1
    | .subst base repl _ => astFuel base + astFuel repl + 1

  def astListFuel : List AST → Nat
    | [] => 1
    | t :: ts => astFuel t + astListFuel ts + 1
end

mutual
  def stepBaseStepFuel? (rws : List RewriteDecl) : Nat → AST → Option AST
    | 0, _ => none
    | fuel + 1, term =>
        match rootBaseStep? rws term with
        | some out => some out
        | none =>
            match term with
            | .sexp (.id h) args =>
                match argsBaseStepFuel? rws fuel args with
                | some argsOut => some (.sexp (.id h) argsOut)
                | none => none
            | _ => none

  def argsBaseStepFuel? (rws : List RewriteDecl) : Nat → List AST → Option (List AST)
    | 0, _ => none
    | _ + 1, [] => none
    | fuel + 1, t :: ts =>
        match stepBaseStepFuel? rws fuel t with
        | some tOut => some (tOut :: ts)
        | none =>
            match argsBaseStepFuel? rws fuel ts with
            | some tsOut => some (t :: tsOut)
            | none => none
end

def stepBaseStep? (rws : List RewriteDecl) (term : AST) : Option AST :=
  stepBaseStepFuel? rws (astFuel term + 1) term

def argsBaseStep? (rws : List RewriteDecl) (args : List AST) :
    Option (List AST) :=
  argsBaseStepFuel? rws (astListFuel args + 1) args

theorem argsBaseStepFuel?_cons_some_nonempty
    (rws : List RewriteDecl) (fuel : Nat) (t : AST) (ts out : List AST)
    (h : argsBaseStepFuel? rws fuel (t :: ts) = some out) :
    ∃ u us, out = u :: us := by
  cases fuel with
  | zero =>
      simp only [argsBaseStepFuel?] at h
      cases h
  | succ fuel =>
      simp only [argsBaseStepFuel?] at h
      cases hstep : stepBaseStepFuel? rws fuel t with
      | some tOut =>
          simp only [hstep] at h
          cases h
          exact ⟨tOut, ts, rfl⟩
      | none =>
          simp only [hstep] at h
          cases hrest : argsBaseStepFuel? rws fuel ts with
          | none =>
              simp only [hrest] at h
              cases h
          | some tsOut =>
              simp only [hrest] at h
              cases h
              exact ⟨t, tsOut, rfl⟩

theorem rootBaseStep?_preserves_noQuery :
    ∀ (rws : List RewriteDecl) (term out : AST),
      RulesPreserveNoQuery rws →
      rootBaseStep? rws term = some out →
      noQueryAST term = true →
      noQueryAST out = true
  | [], _term, _out, _hR, hstep, _hterm => by
      simp only [rootBaseStep?] at hstep
      cases hstep
  | rd :: rest, term, out, hR, hstep, hterm => by
      obtain ⟨hrd, hrest⟩ := hR
      cases hrw : rd.rw with
      | base lhs rhs =>
          simp only [rootBaseStep?, hrw] at hstep
          cases hmatch : AST.matchPat lhs term [] with
          | some bs =>
              simp only [hmatch] at hstep
              cases hstep
              have hbs : BindsNoQuery bs :=
                matchPat_preserves_noQueryBindings lhs term [] bs
                  hterm trivial hmatch
              have hrhs : noQueryAST rhs = true := by
                simpa [RewriteDeclPreservesNoQuery, hrw] using hrd
              exact noQueryAST_inst_preserves rhs bs hrhs hbs
          | none =>
              simp only [hmatch] at hstep
              exact rootBaseStep?_preserves_noQuery rest term out
                hrest hstep hterm
      | ctx _ _ =>
          simp only [rootBaseStep?, hrw] at hstep
          exact rootBaseStep?_preserves_noQuery rest term out
            hrest hstep hterm

mutual
  theorem stepBaseStepFuel?_preserves_noQuery :
      ∀ (rws : List RewriteDecl) (fuel : Nat) (term out : AST),
        RulesPreserveNoQuery rws →
        stepBaseStepFuel? rws fuel term = some out →
        noQueryAST term = true →
        noQueryAST out = true
    | _rws, 0, _term, _out, _hR, hstep, _hterm => by
        simp only [stepBaseStepFuel?] at hstep
        cases hstep
    | rws, fuel + 1, term, out, hR, hstep, hterm => by
        simp only [stepBaseStepFuel?] at hstep
        cases hroot : rootBaseStep? rws term with
        | some rootOut =>
            simp only [hroot] at hstep
            cases hstep
            exact rootBaseStep?_preserves_noQuery rws term out
              hR hroot hterm
        | none =>
            simp only [hroot] at hstep
            cases term with
            | var _ =>
                cases hstep
            | subst _ _ _ =>
                cases hstep
            | sexp l args =>
                cases l with
                | id h =>
                    cases hargs : argsBaseStepFuel? rws fuel args with
                    | none =>
                        simp only [hargs] at hstep
                        cases hstep
                    | some argsOut =>
                        simp only [hargs] at hstep
                        cases hstep
                        have hargsNo : noQueryASTList args = true :=
                          noQueryASTList_of_noQueryAST_sexp (.id h) args hterm
                        have hargsOutNo :
                            noQueryASTList argsOut = true :=
                          argsBaseStepFuel?_preserves_noQuery rws fuel args
                            argsOut hR hargs hargsNo
                        cases args with
                        | nil =>
                            cases fuel with
                            | zero =>
                                simp only [argsBaseStepFuel?] at hargs
                                cases hargs
                            | succ fuel' =>
                                simp only [argsBaseStepFuel?] at hargs
                                cases hargs
                        | cons a rest =>
                            have hterm' :
                                (((h == "match") == false) &&
                                  noQueryASTList (a :: rest)) = true := by
                              simpa [noQueryAST] using hterm
                            have hhead :
                                ((h == "match") == false) = true := by
                              cases hhead : ((h == "match") == false) <;>
                                simp [hhead] at hterm' ⊢
                            obtain ⟨u, us, hout⟩ :=
                              argsBaseStepFuel?_cons_some_nonempty rws fuel
                                a rest argsOut hargs
                            subst argsOut
                            simp [noQueryAST, hhead, hargsOutNo]
                | wild =>
                    cases hstep
                | listE _ =>
                    cases hstep
                | listCons _ =>
                    cases hstep
                | listOne _ =>
                    cases hstep

  theorem argsBaseStepFuel?_preserves_noQuery :
      ∀ (rws : List RewriteDecl) (fuel : Nat) (terms out : List AST),
        RulesPreserveNoQuery rws →
        argsBaseStepFuel? rws fuel terms = some out →
        noQueryASTList terms = true →
        noQueryASTList out = true
    | _rws, 0, _terms, _out, _hR, hstep, _hterms => by
        simp only [argsBaseStepFuel?] at hstep
        cases hstep
    | _rws, _fuel + 1, [], _out, _hR, hstep, _hterms => by
        simp only [argsBaseStepFuel?] at hstep
        cases hstep
    | rws, fuel + 1, t :: ts, out, hR, hstep, hterms => by
        simp only [argsBaseStepFuel?] at hstep
        have hterms' :
            (noQueryAST t && noQueryASTList ts) = true := by
          simpa [noQueryASTList] using hterms
        have ht : noQueryAST t = true := by
          cases ht : noQueryAST t <;> simp [ht] at hterms' ⊢
        have hts : noQueryASTList ts = true := by
          cases ht : noQueryAST t <;> simp [ht] at hterms'
          exact hterms'
        cases hhead : stepBaseStepFuel? rws fuel t with
        | some tOut =>
            simp only [hhead] at hstep
            cases hstep
            have htOut :
                noQueryAST tOut = true :=
              stepBaseStepFuel?_preserves_noQuery rws fuel t tOut
                hR hhead ht
            simp [noQueryASTList, htOut, hts]
        | none =>
            simp only [hhead] at hstep
            cases hrest : argsBaseStepFuel? rws fuel ts with
            | none =>
                simp only [hrest] at hstep
                cases hstep
            | some tsOut =>
                simp only [hrest] at hstep
                cases hstep
                have htsOut :
                    noQueryASTList tsOut = true :=
                  argsBaseStepFuel?_preserves_noQuery rws fuel ts tsOut
                    hR hrest hts
                simp [noQueryASTList, ht, htsOut]
end

def referenceEval (rws : List RewriteDecl) (fuel : Nat) (term : AST) : AST :=
  eval (pOf rws) fuel term

def interpCall? (rws : List RewriteDecl) (term : AST) (guestFuel : Nat) : Option AST :=
  match encRules? rws, encAST? term with
  | some encodedRules, some encodedTerm =>
      some (miEval encodedRules encodedTerm (fuel guestFuel))
  | _, _ => none

def interpEval? (rws : List RewriteDecl) (term : AST)
    (guestFuel hostFuel : Nat) : Option AST :=
  match interpCall? rws term guestFuel with
  | some call => some (eval pMI hostFuel call)
  | none => none

inductive SourceInterpVerdict where
  | done (term : AST)
  | exhausted (term : AST)

def sourceInterpVerdict (rws : List RewriteDecl) : Nat → AST → SourceInterpVerdict
  | 0, term => .exhausted term
  | fuel + 1, term =>
      match stepBaseStep? rws term with
      | some next => sourceInterpVerdict rws fuel next
      | none => .done term

def MatchesInterp (host : AST) : SourceInterpVerdict → Prop
  | .done term =>
      ∃ encodedTerm, encAST? term = some encodedTerm ∧
        host = MIDone encodedTerm
  | .exhausted term =>
      ∃ encodedTerm, encAST? term = some encodedTerm ∧
        host = MIExhausted encodedTerm

/-! ## Structural induction for nested guest syntax -/

mutual
  theorem ast_list_ind_ast
      (P : AST -> Prop) (Q : List AST -> Prop)
      (hVar : forall p, P (.var p))
      (hSexp : forall l args, Q args -> P (.sexp l args))
      (hSubst : forall b r v, P b -> P r -> P (.subst b r v))
      (hNil : Q [])
      (hCons : forall a as, P a -> Q as -> Q (a :: as)) :
      forall t, P t
    | .var p => hVar p
    | .sexp l args =>
        hSexp l args
          (ast_list_ind_list P Q hVar hSexp hSubst hNil hCons args)
    | .subst b r v =>
        hSubst b r v
          (ast_list_ind_ast P Q hVar hSexp hSubst hNil hCons b)
          (ast_list_ind_ast P Q hVar hSexp hSubst hNil hCons r)

  theorem ast_list_ind_list
      (P : AST -> Prop) (Q : List AST -> Prop)
      (hVar : forall p, P (.var p))
      (hSexp : forall l args, Q args -> P (.sexp l args))
      (hSubst : forall b r v, P b -> P r -> P (.subst b r v))
      (hNil : Q [])
      (hCons : forall a as, P a -> Q as -> Q (a :: as)) :
      forall ts, Q ts
    | [] => hNil
    | a :: as =>
        hCons a as
          (ast_list_ind_ast P Q hVar hSexp hSubst hNil hCons a)
          (ast_list_ind_list P Q hVar hSexp hSubst hNil hCons as)
end

theorem ast_list_ind
    (P : AST -> Prop) (Q : List AST -> Prop)
    (hVar : forall p, P (.var p))
    (hSexp : forall l args, Q args -> P (.sexp l args))
    (hSubst : forall b r v, P b -> P r -> P (.subst b r v))
    (hNil : Q [])
    (hCons : forall a as, P a -> Q as -> Q (a :: as)) :
    (forall t, P t) /\ (forall ts, Q ts) := by
  exact
    ⟨ ast_list_ind_ast P Q hVar hSexp hSubst hNil hCons
    , ast_list_ind_list P Q hVar hSexp hSubst hNil hCons ⟩

/-! ## First symbolic dispatch facts for the simulation frontier -/

theorem os_MIBNil_none :
    oneStep pMI MIBNil = none := by
  rfl

theorem os_miMatch_var_data (vName term bs : AST) :
    oneStep pMI (miMatch (app "MIVar" [vName]) term bs) =
      some (miMatchVar vName term bs) := by
  rfl

theorem os_miMatchVar (v term bs : AST) :
    oneStep pMI (miMatchVar v term bs) =
      some (miMatchVarK v term bs (miLookup v bs)) := by
  rfl

theorem os_miLookup_nil_data (vName : AST) :
    oneStep pMI (miLookup vName MIBNil) = some MINone := by
  rfl

theorem label_id_beq (a b : String) :
    (Label.id a == Label.id b) = (a == b) := by
  rfl

@[simp] private theorem label_id_beq_raw (a b : String) :
    instBEqLabel.beq (Label.id a) (Label.id b) = (a == b) := by
  rfl

@[simp] private theorem dottedPath_base_beq_raw (a b : String) :
    instBEqDottedPath.beq (DottedPath.base a) (DottedPath.base b) = (a == b) := by
  rfl

private theorem string_beq_self_mi (s : String) : (s == s) = true :=
  beq_iff_eq.mpr rfl

theorem string_beq_symm_mi (v w : String) : (v == w) = (w == v) := by
  by_cases h : v = w
  · subst w
    rw [string_beq_self_mi v]
  · have hwv : w ≠ v := by
      intro hwv
      exact h hwv.symm
    rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr hwv]

private theorem dottedPath_beq_self_mi : ∀ p : DottedPath, (p == p) = true
  | .base s => by
      change (s == s) = true
      exact string_beq_self_mi s
  | .qualified s rest => by
      change ((s == s) && (rest == rest)) = true
      rw [string_beq_self_mi s, dottedPath_beq_self_mi rest]
      rfl

mutual
  private theorem cat_beq_self_mi : ∀ c : Cat, (c == c) = true
    | .idCat s => by
        change (s == s) = true
        exact string_beq_self_mi s
    | .listOf c => by
        change (c == c) = true
        exact cat_beq_self_mi c
    | .arrow a b => by
        change ((a == a) && (b == b)) = true
        rw [cat_beq_self_mi a, cat_beq_self_mi b]
        rfl
    | .prod cs => by
        change Cat.beqList cs cs = true
        exact cat_beqList_self_mi cs

  private theorem cat_beqList_self_mi : ∀ cs : List Cat, Cat.beqList cs cs = true
    | [] => rfl
    | c :: cs => by
        change ((c == c) && Cat.beqList cs cs) = true
        rw [cat_beq_self_mi c, cat_beqList_self_mi cs]
        rfl
end

private theorem label_beq_self_mi : ∀ l : Label, (l == l) = true
  | .id s => by
      change (s == s) = true
      exact string_beq_self_mi s
  | .wild => rfl
  | .listE c => by
      change (c == c) = true
      exact cat_beq_self_mi c
  | .listCons c => by
      change (c == c) = true
      exact cat_beq_self_mi c
  | .listOne c => by
      change (c == c) = true
      exact cat_beq_self_mi c

mutual
  theorem beq_ast_self : ∀ t : AST, (t == t) = true
    | .var p => by
        change (p == p) = true
        exact dottedPath_beq_self_mi p
    | .sexp l args => by
        change ((l == l) && AST.beqList args args) = true
        rw [label_beq_self_mi l, beq_ast_list_self args]
        rfl
    | .subst b r v => by
        change ((b == b) && (r == r) && (v == v)) = true
        rw [beq_ast_self b, beq_ast_self r, dottedPath_beq_self_mi v]
        rfl

  private theorem beq_ast_list_self : ∀ ts : List AST, AST.beqList ts ts = true
    | [] => rfl
    | t :: ts => by
        change ((t == t) && AST.beqList ts ts) = true
        rw [beq_ast_self t, beq_ast_list_self ts]
        rfl
end

mutual
  private theorem cat_beq_true_eq_mi : ∀ a b : Cat, (a == b) = true → a = b
    | .idCat a, .idCat b, h => by
        change (a == b) = true at h
        exact congrArg Cat.idCat (beq_iff_eq.mp h)
    | .listOf a, .listOf b, h => by
        change (a == b) = true at h
        exact congrArg Cat.listOf (cat_beq_true_eq_mi a b h)
    | .arrow a b, .arrow c d, h => by
        change ((a == c) && (b == d)) = true at h
        simp only [Bool.and_eq_true] at h
        have hac := cat_beq_true_eq_mi a c h.1
        have hbd := cat_beq_true_eq_mi b d h.2
        subst c
        subst d
        rfl
    | .prod as, .prod bs, h => by
        change Cat.beqList as bs = true at h
        exact congrArg Cat.prod (cat_beqList_true_eq_mi as bs h)
    | .idCat _, .listOf _, h => by change false = true at h; cases h
    | .idCat _, .arrow _ _, h => by change false = true at h; cases h
    | .idCat _, .prod _, h => by change false = true at h; cases h
    | .listOf _, .idCat _, h => by change false = true at h; cases h
    | .listOf _, .arrow _ _, h => by change false = true at h; cases h
    | .listOf _, .prod _, h => by change false = true at h; cases h
    | .arrow _ _, .idCat _, h => by change false = true at h; cases h
    | .arrow _ _, .listOf _, h => by change false = true at h; cases h
    | .arrow _ _, .prod _, h => by change false = true at h; cases h
    | .prod _, .idCat _, h => by change false = true at h; cases h
    | .prod _, .listOf _, h => by change false = true at h; cases h
    | .prod _, .arrow _ _, h => by change false = true at h; cases h

  private theorem cat_beqList_true_eq_mi :
      ∀ as bs : List Cat, Cat.beqList as bs = true → as = bs
    | [], [], _ => rfl
    | [], _ :: _, h => by change false = true at h; cases h
    | _ :: _, [], h => by change false = true at h; cases h
    | a :: as, b :: bs, h => by
        change ((a == b) && Cat.beqList as bs) = true at h
        simp only [Bool.and_eq_true] at h
        have hab := cat_beq_true_eq_mi a b h.1
        have htail := cat_beqList_true_eq_mi as bs h.2
        subst b
        subst bs
        rfl
end

private theorem dottedPath_beq_true_eq_mi :
    ∀ a b : DottedPath, (a == b) = true → a = b
  | .base a, .base b, h => by
      change (a == b) = true at h
      exact congrArg DottedPath.base (beq_iff_eq.mp h)
  | .base _, .qualified _ _, h => by change false = true at h; cases h
  | .qualified _ _, .base _, h => by change false = true at h; cases h
  | .qualified a as, .qualified b bs, h => by
      change ((a == b) && (as == bs)) = true at h
      simp only [Bool.and_eq_true] at h
      have hab : a = b := beq_iff_eq.mp h.1
      have htail := dottedPath_beq_true_eq_mi as bs h.2
      subst b
      subst bs
      rfl

private theorem label_beq_true_eq_mi :
    ∀ a b : Label, (a == b) = true → a = b
  | .id a, .id b, h => by
      change (a == b) = true at h
      exact congrArg Label.id (beq_iff_eq.mp h)
  | .id _, .wild, h => by change false = true at h; cases h
  | .id _, .listE _, h => by change false = true at h; cases h
  | .id _, .listCons _, h => by change false = true at h; cases h
  | .id _, .listOne _, h => by change false = true at h; cases h
  | .wild, .id _, h => by change false = true at h; cases h
  | .wild, .wild, _ => rfl
  | .wild, .listE _, h => by change false = true at h; cases h
  | .wild, .listCons _, h => by change false = true at h; cases h
  | .wild, .listOne _, h => by change false = true at h; cases h
  | .listE a, .id _, h => by change false = true at h; cases h
  | .listE _, .wild, h => by change false = true at h; cases h
  | .listE a, .listE b, h => by
      change (a == b) = true at h
      exact congrArg Label.listE (cat_beq_true_eq_mi a b h)
  | .listE _, .listCons _, h => by change false = true at h; cases h
  | .listE _, .listOne _, h => by change false = true at h; cases h
  | .listCons a, .id _, h => by change false = true at h; cases h
  | .listCons _, .wild, h => by change false = true at h; cases h
  | .listCons _, .listE _, h => by change false = true at h; cases h
  | .listCons a, .listCons b, h => by
      change (a == b) = true at h
      exact congrArg Label.listCons (cat_beq_true_eq_mi a b h)
  | .listCons _, .listOne _, h => by change false = true at h; cases h
  | .listOne a, .id _, h => by change false = true at h; cases h
  | .listOne _, .wild, h => by change false = true at h; cases h
  | .listOne _, .listE _, h => by change false = true at h; cases h
  | .listOne _, .listCons _, h => by change false = true at h; cases h
  | .listOne a, .listOne b, h => by
      change (a == b) = true at h
      exact congrArg Label.listOne (cat_beq_true_eq_mi a b h)

mutual
  theorem ast_beq_true_eq_mi : ∀ a b : AST, (a == b) = true → a = b
    | .var p, .var q, h => by
        change (p == q) = true at h
        exact congrArg AST.var (dottedPath_beq_true_eq_mi p q h)
    | .var _, .sexp _ _, h => by change false = true at h; cases h
    | .var _, .subst _ _ _, h => by change false = true at h; cases h
    | .sexp _ _, .var _, h => by change false = true at h; cases h
    | .sexp l as, .sexp m bs, h => by
        change ((l == m) && AST.beqList as bs) = true at h
        simp only [Bool.and_eq_true] at h
        have hlm := label_beq_true_eq_mi l m h.1
        have habs := ast_beqList_true_eq_mi as bs h.2
        subst m
        subst bs
        rfl
    | .sexp _ _, .subst _ _ _, h => by change false = true at h; cases h
    | .subst _ _ _, .var _, h => by change false = true at h; cases h
    | .subst _ _ _, .sexp _ _, h => by change false = true at h; cases h
    | .subst b r v, .subst b' r' v', h => by
        change (((b == b') && (r == r')) && (v == v')) = true at h
        simp only [Bool.and_eq_true] at h
        have hbb := ast_beq_true_eq_mi b b' h.1.1
        have hrr := ast_beq_true_eq_mi r r' h.1.2
        have hvv := dottedPath_beq_true_eq_mi v v' h.2
        subst b'
        subst r'
        subst v'
        rfl

  theorem ast_beqList_true_eq_mi :
      ∀ as bs : List AST, AST.beqList as bs = true → as = bs
    | [], [], _ => rfl
    | [], _ :: _, h => by change false = true at h; cases h
    | _ :: _, [], h => by change false = true at h; cases h
    | a :: as, b :: bs, h => by
        change ((a == b) && AST.beqList as bs) = true at h
        simp only [Bool.and_eq_true] at h
        have hab := ast_beq_true_eq_mi a b h.1
        have htail := ast_beqList_true_eq_mi as bs h.2
        subst b
        subst bs
        rfl
end

theorem beq_con0 (x s : String) :
    (con0 x == con0 s) = (x == s) := by
  simp only [con0, BEq.beq, AST.beq, AST.beqList, Bool.and_true]
  rfl

theorem beq_con0_self (s : String) :
    (con0 s == con0 s) = true := by
  rw [beq_con0]
  exact beq_iff_eq.mpr rfl

theorem match_con0_MIBNil_MIBCons_none (v : String) (t rest : AST)
    (bs : List (String × AST)) :
    AST.matchPat (con0 "MIBNil")
      (AST.sexp (Label.id "MIBCons") [con0 v, t, rest]) bs = none := by
  have e_nil_cons : (("MIBNil" : String) == "MIBCons") = false := by decide
  simp only [con0, AST.matchPat, label_id_beq, e_nil_cons]
  rfl

theorem match_con0_MINone_MISome_none (term : AST)
    (bs : List (String × AST)) :
    AST.matchPat (con0 "MINone") (MISome term) bs = none := by
  have e_none_some : (("MINone" : String) == "MISome") = false := by decide
  simp only [con0, MISome, app, AST.matchPat, label_id_beq, e_none_some]
  rfl

theorem apply_miLookup_nil_on_cons (v : String) (t rest : AST) :
    applyBaseRewrite (rw "lookup-nil" (miLookup vV MIBNil) MINone)
      (miLookup (con0 v) (MIBCons (con0 v) t rest)) = none := by
  have e_lookup : (("mi-lookup" : String) == "mi-lookup") = true := by decide
  simp only [applyBaseRewrite, rw, miLookup, MIBNil, MIBCons, MINone, app, pv, vV,
    AST.matchPat, AST.matchPatList, label_id_beq, e_lookup,
    List.find?_nil, Option.bind_some, if_pos]
  rw [match_con0_MIBNil_MIBCons_none v t rest [("v", con0 v)]]
  rfl

theorem apply_miLookup_nil_on_any_cons (q w : String) (t rest : AST) :
    applyBaseRewrite (rw "lookup-nil" (miLookup vV MIBNil) MINone)
      (miLookup (con0 q) (MIBCons (con0 w) t rest)) = none := by
  have e_lookup : (("mi-lookup" : String) == "mi-lookup") = true := by decide
  simp only [applyBaseRewrite, rw, miLookup, MIBNil, MIBCons, MINone, app, pv, vV,
    AST.matchPat, AST.matchPatList, label_id_beq, e_lookup,
    List.find?_nil, Option.bind_some, if_pos]
  rw [match_con0_MIBNil_MIBCons_none w t rest [("v", con0 q)]]
  rfl

theorem apply_miLookup_hit_named (v : String) (t rest : AST) :
    applyBaseRewrite (rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT))
      (miLookup (con0 v) (MIBCons (con0 v) t rest)) = some (MISome t) := by
  have e_lookup : (("mi-lookup" : String) == "mi-lookup") = true := by decide
  have e_cons : (("MIBCons" : String) == "MIBCons") = true := by decide
  have e_v_v : (("v" : String) == "v") = true := by decide
  have e_v_t : (("v" : String) == "t") = false := by decide
  have e_t_t : (("t" : String) == "t") = true := by decide
  have e_t_rest : (("t" : String) == "rest") = false := by decide
  have e_v_rest : (("v" : String) == "rest") = false := by decide
  have e_rest_t : (("rest" : String) == "t") = false := by decide
  have e_same : (con0 v == con0 v) = true := beq_con0_self v
  simp only [applyBaseRewrite, rw, miLookup, MIBCons, MISome, app, pv, vV, vT, vRest,
    AST.matchPat, AST.matchPatList, AST.inst, AST.instList, List.find?,
    label_id_beq, e_lookup, e_cons, e_v_v, e_v_t, e_t_t, e_t_rest, e_v_rest,
    e_rest_t, e_same, Option.bind_some, Option.map_some, if_pos]

theorem apply_miLookup_hit_on_distinct_head (v w : String)
    (hvw : (v == w) = false) (t rest : AST) :
    applyBaseRewrite (rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT))
      (miLookup (con0 v) (MIBCons (con0 w) t rest)) = none := by
  have e_lookup : (("mi-lookup" : String) == "mi-lookup") = true := by decide
  have e_cons : (("MIBCons" : String) == "MIBCons") = true := by decide
  have e_v_v : (("v" : String) == "v") = true := by decide
  have e_diff : (con0 v == con0 w) = false := by
    rw [beq_con0, hvw]
  simp only [applyBaseRewrite, rw, miLookup, MIBCons, MISome, app, pv, vV, vT,
    vRest, AST.matchPat, AST.matchPatList, AST.inst, AST.instList, List.find?,
    label_id_beq, e_lookup, e_cons, e_v_v, e_diff, Option.bind_some,
    Bool.false_eq_true, if_false, if_true, Option.bind_none, Option.map_none]

theorem apply_miLookup_miss_named (v w : String) (t rest : AST) :
    applyBaseRewrite (rw "lookup-miss" (miLookup vV (MIBCons vW vT vRest))
        (miLookup vV vRest))
      (miLookup (con0 v) (MIBCons (con0 w) t rest)) =
        some (miLookup (con0 v) rest) := by
  have e_lookup : (("mi-lookup" : String) == "mi-lookup") = true := by decide
  have e_cons : (("MIBCons" : String) == "MIBCons") = true := by decide
  have e_v_v : (("v" : String) == "v") = true := by decide
  have e_v_w : (("v" : String) == "w") = false := by decide
  have e_w_t : (("w" : String) == "t") = false := by decide
  have e_v_t : (("v" : String) == "t") = false := by decide
  have e_t_rest : (("t" : String) == "rest") = false := by decide
  have e_w_rest : (("w" : String) == "rest") = false := by decide
  have e_v_rest : (("v" : String) == "rest") = false := by decide
  have e_rest_rest : (("rest" : String) == "rest") = true := by decide
  have e_rest_v : (("rest" : String) == "v") = false := by decide
  have e_t_v : (("t" : String) == "v") = false := by decide
  have e_w_v : (("w" : String) == "v") = false := by decide
  simp only [applyBaseRewrite, rw, miLookup, MIBCons, app, pv, vV, vW, vT,
    vRest, AST.matchPat, AST.matchPatList, AST.inst, AST.instList, List.find?,
    label_id_beq, e_lookup, e_cons, e_v_v, e_v_w, e_w_t, e_v_t,
    e_t_rest, e_w_rest, e_v_rest, e_rest_rest, e_rest_v, e_t_v, e_w_v,
    Option.bind_some, Option.map_some, if_pos]

theorem miRules_lookup_prefix :
    miRules =
      rw "lookup-nil" (miLookup vV MIBNil) MINone ::
      rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT) ::
      List.drop 2 miRules := by
  rfl

theorem miRules_lookup_prefix3 :
    miRules =
      rw "lookup-nil" (miLookup vV MIBNil) MINone ::
      rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT) ::
      rw "lookup-miss" (miLookup vV (MIBCons vW vT vRest)) (miLookup vV vRest) ::
      List.drop 3 miRules := by
  rfl

theorem baseReducts_miLookup_hit_named_head (v : String) (t rest : AST) :
    ∃ tail, baseReducts pMI (miLookup (con0 v) (MIBCons (con0 v) t rest)) =
      MISome t :: tail := by
  let target := miLookup (con0 v) (MIBCons (con0 v) t rest)
  refine ⟨(List.drop 2 miRules).filterMap (fun rd => applyBaseRewrite rd target), ?_⟩
  change miRules.filterMap (fun rd => applyBaseRewrite rd target) =
    MISome t :: (List.drop 2 miRules).filterMap (fun rd => applyBaseRewrite rd target)
  rw [miRules_lookup_prefix]
  simp [target, apply_miLookup_nil_on_cons, apply_miLookup_hit_named]

theorem os_miLookup_hit_named (v : String) (t rest : AST) :
    oneStep pMI (miLookup (con0 v) (MIBCons (con0 v) t rest)) =
      some (MISome t) := by
  obtain ⟨tail, hhead⟩ := baseReducts_miLookup_hit_named_head v t rest
  change (match baseReducts pMI (miLookup (con0 v) (MIBCons (con0 v) t rest)) with
    | r :: _ => some r
    | [] => (oneStepList pMI [con0 v, MIBCons (con0 v) t rest]).map
        (fun args' => AST.sexp (Label.id "mi-lookup") args')) = some (MISome t)
  rw [hhead]

theorem miLookup_hit_named_eval (v : String) (t rest : AST) :
    eval pMI 1 (miLookup (con0 v) (MIBCons (con0 v) t rest)) = MISome t := by
  simp [eval, os_miLookup_hit_named]

theorem baseReducts_miLookup_miss_named_head (v w : String)
    (hvw : (v == w) = false) (t rest : AST) :
    ∃ tail, baseReducts pMI (miLookup (con0 v) (MIBCons (con0 w) t rest)) =
      miLookup (con0 v) rest :: tail := by
  let target := miLookup (con0 v) (MIBCons (con0 w) t rest)
  refine ⟨(List.drop 3 miRules).filterMap (fun rd => applyBaseRewrite rd target), ?_⟩
  change miRules.filterMap (fun rd => applyBaseRewrite rd target) =
    miLookup (con0 v) rest ::
      (List.drop 3 miRules).filterMap (fun rd => applyBaseRewrite rd target)
  rw [miRules_lookup_prefix3]
  simp [target, apply_miLookup_nil_on_any_cons, apply_miLookup_hit_on_distinct_head,
    apply_miLookup_miss_named, hvw]

theorem os_miLookup_miss_named (v w : String)
    (hvw : (v == w) = false) (t rest : AST) :
    oneStep pMI (miLookup (con0 v) (MIBCons (con0 w) t rest)) =
      some (miLookup (con0 v) rest) := by
  obtain ⟨tail, hhead⟩ := baseReducts_miLookup_miss_named_head v w hvw t rest
  change (match baseReducts pMI (miLookup (con0 v) (MIBCons (con0 w) t rest)) with
    | r :: _ => some r
    | [] => (oneStepList pMI [con0 v, MIBCons (con0 w) t rest]).map
        (fun args' => AST.sexp (Label.id "mi-lookup") args')) =
      some (miLookup (con0 v) rest)
  rw [hhead]

theorem miLookup_miss_named_eval (v w : String)
    (hvw : (v == w) = false) (t rest : AST) :
    eval pMI 1 (miLookup (con0 v) (MIBCons (con0 w) t rest)) =
      miLookup (con0 v) rest := by
  simp [eval, os_miLookup_miss_named, hvw]

theorem miLookup_miss_then_hit_eval (v w : String)
    (hvw : (v == w) = false) (head target rest : AST) :
    eval pMI 2
        (miLookup (con0 v)
          (MIBCons (con0 w) head (MIBCons (con0 v) target rest))) =
      MISome target := by
  simp [eval, os_miLookup_miss_named, os_miLookup_hit_named, hvw]

theorem oneStepList_matchVarK_lookup_nil (vName term : AST)
    (hv : IsNormal pMI vName) (hterm : IsNormal pMI term) :
    oneStepList pMI [vName, term, MIBNil, miLookup vName MIBNil] =
      some [vName, term, MIBNil, MINone] := by
  simp only [IsNormal] at hv hterm
  simp only [oneStepList, hv, hterm, os_MIBNil_none, os_miLookup_nil_data]
  rfl

theorem base_miMatchVarK_lookup_nil_raw (vName term : AST) :
    baseReducts pMI
      (.sexp (.id "mi-match-varK") [vName, term, MIBNil, miLookup vName MIBNil]) = [] := by
  rfl

theorem os_miMatchVarK_lookup_nil (vName term : AST)
    (hv : IsNormal pMI vName) (hterm : IsNormal pMI term) :
    oneStep pMI (miMatchVarK vName term MIBNil (miLookup vName MIBNil)) =
      some (miMatchVarK vName term MIBNil MINone) := by
  rw [oneStep.eq_def]
  simp only [miMatchVarK, app]
  rw [base_miMatchVarK_lookup_nil_raw]
  rw [oneStepList_matchVarK_lookup_nil vName term hv hterm]
  rfl

theorem os_miMatchVarK_none_data (vName term : AST) :
    oneStep pMI (miMatchVarK vName term MIBNil MINone) =
      some (MIMatchOk (MIBCons vName term MIBNil)) := by
  rfl

theorem miMatch_var_nil_data_sim (vName encodedTerm : AST)
    (hv : IsNormal pMI vName) (hterm : IsNormal pMI encodedTerm) :
    eval pMI 4 (miMatch (app "MIVar" [vName]) encodedTerm MIBNil) =
      MIMatchOk (MIBCons vName encodedTerm MIBNil) := by
  simp only [eval, os_miMatch_var_data, os_miMatchVar,
    os_miMatchVarK_lookup_nil, os_miMatchVarK_none_data, hv, hterm]

/-! ## Normality of encoded guest data -/

theorem matchPat_nonempty_to_nil (l m : Label) (p : AST) (ps : List AST)
    (bnds : List (String × AST)) :
    AST.matchPat (.sexp l (p :: ps)) (.sexp m []) bnds = none := by
  simp [AST.matchPat, AST.matchPatList]

theorem applyBaseRewrite_nonempty_lhs_con0 (name : String) (l : Label) (p : AST)
    (ps : List AST) (rhs : AST) (s : String) :
    applyBaseRewrite { name := name, rw := .base (.sexp l (p :: ps)) rhs }
      (.sexp (.id s) []) = none := by
  simp [applyBaseRewrite, matchPat_nonempty_to_nil]

theorem baseReducts_con0_pMI_raw (s : String) :
    baseReducts pMI (.sexp (.id s) []) = [] := by
  change miRules.filterMap (fun rd => applyBaseRewrite rd (.sexp (.id s) [])) = []
  simp only [miRules, List.filterMap_cons, List.filterMap_nil,
    applyBaseRewrite_nonempty_lhs_con0, rw, miLookup, miMatchVar, miMatchVarK,
    miMatchList, miMatchListK, miMatch, miSubst, miSubstVarK, miSubstList,
    miQueryRoot, miQueryRootK, miRoot, miRootTable, miRootK, miStepArgs,
    miStepArgsK, miStepArgsRestK, miStep, miStepRootK, miStepAppK, miEval,
    miEvalK, miRun, miDecodeVerdict, miDecode, app]

theorem baseReducts_con0_pMI (s : String) :
    baseReducts pMI (con0 s) = [] := by
  exact baseReducts_con0_pMI_raw s

theorem normal_con0 (s : String) :
    IsNormal pMI (con0 s) := by
  simp only [IsNormal, con0]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_con0_pMI_raw]
  rfl

theorem baseReducts_FS_pMI_raw (t : AST) :
    baseReducts pMI (.sexp (.id "FS") [t]) = [] := by
  rfl

theorem normal_FZ :
    IsNormal pMI FZ := by
  simpa [FZ] using normal_con0 "FZ"

theorem normal_FS (t : AST) (ht : IsNormal pMI t) :
    IsNormal pMI (FS t) := by
  simp only [IsNormal] at ht ⊢
  simp only [FS, app]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_FS_pMI_raw]
  simp only [oneStepList, ht, Option.map_none]

theorem normal_fuel :
    ∀ n : Nat, IsNormal pMI (fuel n)
  | 0 => by
      simpa [fuel] using normal_FZ
  | n + 1 => by
      simpa [fuel] using normal_FS (fuel n) (normal_fuel n)

theorem normal_MINil :
    IsNormal pMI MINil :=
  normal_con0 "MINil"

theorem normal_MIBNil :
    IsNormal pMI MIBNil := by
  exact os_MIBNil_none

theorem baseReducts_MISome_pMI_raw (t : AST) :
    baseReducts pMI (.sexp (.id "MISome") [t]) = [] := by
  rfl

theorem normal_MISome (t : AST) (ht : IsNormal pMI t) :
    IsNormal pMI (MISome t) := by
  simp only [IsNormal] at ht ⊢
  simp only [MISome, app]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_MISome_pMI_raw]
  simp only [oneStepList, ht]
  rfl

theorem normal_MIMatchFail :
    IsNormal pMI MIMatchFail :=
  normal_con0 "MIMatchFail"

theorem baseReducts_MIMatchOk_pMI_raw (bs : AST) :
    baseReducts pMI (.sexp (.id "MIMatchOk") [bs]) = [] := by
  rfl

theorem normal_MIMatchOk (bs : AST) (hbs : IsNormal pMI bs) :
    IsNormal pMI (MIMatchOk bs) := by
  simp only [IsNormal] at hbs ⊢
  simp only [MIMatchOk, app]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_MIMatchOk_pMI_raw]
  simp only [oneStepList, hbs]
  rfl

theorem baseReducts_MIVar_pMI_raw (v : String) :
    baseReducts pMI (.sexp (.id "MIVar") [con0 v]) = [] := by
  rfl

theorem normal_MIVar (v : String) :
    IsNormal pMI (MIVar v) := by
  have hv := normal_con0 v
  simp only [IsNormal] at hv ⊢
  simp only [MIVar, app]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_MIVar_pMI_raw]
  simp only [oneStepList, hv]
  rfl

theorem baseReducts_MISym_pMI_raw (s : String) :
    baseReducts pMI (.sexp (.id "MISym") [con0 s]) = [] := by
  rfl

theorem normal_MISym (s : String) :
    IsNormal pMI (MISym s) := by
  have hname := normal_con0 s
  simp only [IsNormal] at hname ⊢
  simp only [MISym, app]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_MISym_pMI_raw]
  simp only [oneStepList, hname]
  rfl

theorem baseReducts_MICons_pMI_raw (x xs : AST) :
    baseReducts pMI (.sexp (.id "MICons") [x, xs]) = [] := by
  rfl

theorem normal_MICons (x xs : AST)
    (hx : IsNormal pMI x) (hxs : IsNormal pMI xs) :
    IsNormal pMI (MICons x xs) := by
  simp only [IsNormal] at hx hxs ⊢
  simp only [MICons, app]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_MICons_pMI_raw]
  simp only [oneStepList, hx, hxs]
  rfl

theorem baseReducts_MIBCons_pMI_raw (v t rest : AST) :
    baseReducts pMI (.sexp (.id "MIBCons") [v, t, rest]) = [] := by
  rfl

theorem normal_MIBCons (v t rest : AST)
    (hv : IsNormal pMI v) (ht : IsNormal pMI t) (hrest : IsNormal pMI rest) :
    IsNormal pMI (MIBCons v t rest) := by
  simp only [IsNormal] at hv ht hrest ⊢
  simp only [MIBCons, app]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_MIBCons_pMI_raw]
  simp only [oneStepList, hv, ht, hrest]
  rfl

theorem baseReducts_MIApp_pMI_raw (s : String) (args : AST) :
    baseReducts pMI (.sexp (.id "MIApp") [con0 s, args]) = [] := by
  rfl

theorem normal_MIApp (s : String) (args : AST)
    (hargs : IsNormal pMI args) :
    IsNormal pMI (MIApp s args) := by
  have hname := normal_con0 s
  simp only [IsNormal] at hname hargs ⊢
  simp only [MIApp, app]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_MIApp_pMI_raw]
  simp only [oneStepList, hname, hargs]
  rfl

theorem normal_MIRNil :
    IsNormal pMI MIRNil :=
  normal_con0 "MIRNil"

theorem baseReducts_MIRule_pMI_raw (lhs rhs : AST) :
    baseReducts pMI (.sexp (.id "MIRule") [lhs, rhs]) = [] := by
  rfl

theorem normal_MIRule (lhs rhs : AST)
    (hlhs : IsNormal pMI lhs) (hrhs : IsNormal pMI rhs) :
    IsNormal pMI (MIRule lhs rhs) := by
  simp only [IsNormal] at hlhs hrhs ⊢
  simp only [MIRule, app]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_MIRule_pMI_raw]
  simp only [oneStepList, hlhs, hrhs]
  rfl

theorem baseReducts_MIFact_pMI_raw (fact : AST) :
    baseReducts pMI (.sexp (.id "MIFact") [fact]) = [] := by
  rfl

theorem normal_MIFact (fact : AST) (hfact : IsNormal pMI fact) :
    IsNormal pMI (MIFact fact) := by
  simp only [IsNormal] at hfact ⊢
  simp only [MIFact, app]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_MIFact_pMI_raw]
  simp only [oneStepList, hfact]
  rfl

theorem baseReducts_MIRCons_pMI_raw (r rest : AST) :
    baseReducts pMI (.sexp (.id "MIRCons") [r, rest]) = [] := by
  rfl

theorem normal_MIRCons (r rest : AST)
    (hr : IsNormal pMI r) (hrest : IsNormal pMI rest) :
    IsNormal pMI (MIRCons r rest) := by
  simp only [IsNormal] at hr hrest ⊢
  simp only [MIRCons, app]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_MIRCons_pMI_raw]
  simp only [oneStepList, hr, hrest]
  rfl

theorem baseReducts_MIRootStep_pMI_raw (t : AST) :
    baseReducts pMI (.sexp (.id "MIRootStep") [t]) = [] := by
  rfl

theorem normal_MIRootStep (t : AST) (ht : IsNormal pMI t) :
    IsNormal pMI (MIRootStep t) := by
  simp only [IsNormal] at ht ⊢
  simp only [MIRootStep, app]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_MIRootStep_pMI_raw]
  simp only [oneStepList, ht]
  rfl

theorem normal_MINoRoot :
    IsNormal pMI MINoRoot :=
  normal_con0 "MINoRoot"

theorem baseReducts_MIStep_pMI_raw (t : AST) :
    baseReducts pMI (.sexp (.id "MIStep") [t]) = [] := by
  rfl

theorem normal_MIStep (t : AST) (ht : IsNormal pMI t) :
    IsNormal pMI (MIStep t) := by
  simp only [IsNormal] at ht ⊢
  simp only [MIStep, app]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_MIStep_pMI_raw]
  simp only [oneStepList, ht]
  rfl

theorem normal_MINoStep :
    IsNormal pMI MINoStep :=
  normal_con0 "MINoStep"

theorem baseReducts_MIArgsStep_pMI_raw (args : AST) :
    baseReducts pMI (.sexp (.id "MIArgsStep") [args]) = [] := by
  rfl

theorem normal_MIArgsStep (args : AST) (hargs : IsNormal pMI args) :
    IsNormal pMI (MIArgsStep args) := by
  simp only [IsNormal] at hargs ⊢
  simp only [MIArgsStep, app]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_MIArgsStep_pMI_raw]
  simp only [oneStepList, hargs]
  rfl

theorem normal_MINoArgsStep :
    IsNormal pMI MINoArgsStep :=
  normal_con0 "MINoArgsStep"

theorem baseReducts_MIDone_pMI_raw (t : AST) :
    baseReducts pMI (.sexp (.id "MIDone") [t]) = [] := by
  rfl

theorem normal_MIDone (t : AST) (ht : IsNormal pMI t) :
    IsNormal pMI (MIDone t) := by
  simp only [IsNormal] at ht ⊢
  simp only [MIDone, app]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_MIDone_pMI_raw]
  simp only [oneStepList, ht]
  rfl

theorem baseReducts_MIExhausted_pMI_raw (t : AST) :
    baseReducts pMI (.sexp (.id "MIExhausted") [t]) = [] := by
  rfl

theorem normal_MIExhausted (t : AST) (ht : IsNormal pMI t) :
    IsNormal pMI (MIExhausted t) := by
  simp only [IsNormal] at ht ⊢
  simp only [MIExhausted, app]
  rw [oneStep.eq_def]
  simp only
  rw [baseReducts_MIExhausted_pMI_raw]
  simp only [oneStepList, ht]
  rfl

mutual
  theorem encAST?_some_normal : ∀ (t encoded : AST),
      encAST? t = some encoded → IsNormal pMI encoded
    | .var (.base v), encoded, h => by
        cases h
        exact normal_MIVar v
    | .var (.qualified _ _), _, h => by
        cases h
    | .sexp (.id s) [], encoded, h => by
        cases h
        exact normal_MISym s
    | .sexp (.id s) (a :: args), encoded, h => by
        simp only [encAST?] at h
        cases hargs : encASTList? (a :: args) with
        | none => simp [hargs] at h
        | some encodedArgs =>
            simp [hargs] at h
            cases h
            exact normal_MIApp s encodedArgs
              (encASTList?_some_normal (a :: args) encodedArgs hargs)
    | .sexp .wild _, _, h => by
        cases h
    | .sexp (.listE _) _, _, h => by
        cases h
    | .sexp (.listCons _) _, _, h => by
        cases h
    | .sexp (.listOne _) _, _, h => by
        cases h
    | .subst _ _ _, _, h => by
        cases h

  theorem encASTList?_some_normal : ∀ (ts : List AST) (encoded : AST),
      encASTList? ts = some encoded → IsNormal pMI encoded
    | [], encoded, h => by
        cases h
        exact normal_MINil
    | t :: ts, encoded, h => by
        simp only [encASTList?] at h
        cases ht : encAST? t with
        | none => simp [ht] at h
        | some encodedT =>
            cases hts : encASTList? ts with
            | none => simp [ht, hts] at h
            | some encodedTs =>
                simp [ht, hts] at h
                cases h
                exact normal_MICons encodedT encodedTs
                  (encAST?_some_normal t encodedT ht)
                  (encASTList?_some_normal ts encodedTs hts)
end

theorem encBinds?_some_normal : ∀ (bs : List (String × AST)) (encoded : AST),
    encBinds? bs = some encoded → IsNormal pMI encoded
  | [], encoded, h => by
      cases h
      exact normal_MIBNil
  | (v, t) :: rest, encoded, h => by
      simp only [encBinds?] at h
      cases ht : encAST? t with
      | none => simp [ht] at h
      | some encodedTerm =>
          cases hrest : encBinds? rest with
          | none => simp [ht, hrest] at h
          | some encodedRest =>
              simp [ht, hrest] at h
              cases h
              exact normal_MIBCons (con0 v) encodedTerm encodedRest
                (normal_con0 v)
                (encAST?_some_normal t encodedTerm ht)
                (encBinds?_some_normal rest encodedRest hrest)

theorem encRewriteDecl?_some_normal (rd : RewriteDecl) (encoded : AST) :
    encRewriteDecl? rd = some encoded → IsNormal pMI encoded := by
  unfold encRewriteDecl?
  cases rd.rw with
  | base lhs rhs =>
      cases hlhs : encAST? lhs with
      | none =>
          simp [hlhs]
      | some encodedLhs =>
          cases hrhs : encAST? rhs with
          | none =>
              simp [hlhs, hrhs]
          | some encodedRhs =>
              intro h
              simp [hlhs, hrhs] at h
              cases h
              exact normal_MIRule encodedLhs encodedRhs
                (encAST?_some_normal lhs encodedLhs hlhs)
                (encAST?_some_normal rhs encodedRhs hrhs)
  | ctx _ _ =>
      simp

theorem encRules?_some_normal : ∀ (rws : List RewriteDecl) (encoded : AST),
    encRules? rws = some encoded → IsNormal pMI encoded
  | [], encoded, h => by
      cases h
      exact normal_MIRNil
  | rd :: rest, encoded, h => by
      simp only [encRules?] at h
      cases hrd : encRewriteDecl? rd with
      | none =>
          simp [hrd] at h
      | some encodedRule =>
          cases hrest : encRules? rest with
          | none =>
              simp [hrd, hrest] at h
          | some encodedRest =>
              simp [hrd, hrest] at h
              cases h
              exact normal_MIRCons encodedRule encodedRest
                (encRewriteDecl?_some_normal rd encodedRule hrd)
                (encRules?_some_normal rest encodedRest hrest)

mutual
  def decodeEncodedAST? : AST → Option AST
    | .sexp (.id "MIVar") [.sexp (.id v) []] =>
        some (.var (.base v))
    | .sexp (.id "MISym") [.sexp (.id s) []] =>
        some (.sexp (.id s) [])
    | .sexp (.id "MIApp") [.sexp (.id h) [], args] =>
        match decodeEncodedASTList? args with
        | some decodedArgs => some (.sexp (.id h) decodedArgs)
        | none => none
    | _ => none

  def decodeEncodedASTList? : AST → Option (List AST)
    | .sexp (.id "MINil") [] => some []
    | .sexp (.id "MICons") [x, xs] =>
        match decodeEncodedAST? x, decodeEncodedASTList? xs with
        | some decodedX, some decodedXs => some (decodedX :: decodedXs)
        | _, _ => none
    | _ => none
end

mutual
  theorem decodeEncodedAST?_encAST? :
      ∀ (t encoded : AST),
        encAST? t = some encoded →
        decodeEncodedAST? encoded = some t
    | .var (.base v), encoded, h => by
        cases h
        rfl
    | .var (.qualified _ _), _, h => by
        cases h
    | .sexp (.id s) [], encoded, h => by
        cases h
        rfl
    | .sexp (.id s) (a :: args), encoded, h => by
        simp only [encAST?] at h
        cases hargs : encASTList? (a :: args) with
        | none =>
            simp [hargs] at h
        | some encodedArgs =>
            simp [hargs] at h
            cases h
            have hdec := decodeEncodedASTList?_encASTList? (a :: args)
              encodedArgs hargs
            simp only [decodeEncodedAST?, MIApp, app, con0, hdec]
    | .sexp .wild _, _, h => by
        cases h
    | .sexp (.listE _) _, _, h => by
        cases h
    | .sexp (.listCons _) _, _, h => by
        cases h
    | .sexp (.listOne _) _, _, h => by
        cases h
    | .subst _ _ _, _, h => by
        cases h

  theorem decodeEncodedASTList?_encASTList? :
      ∀ (ts : List AST) (encoded : AST),
        encASTList? ts = some encoded →
        decodeEncodedASTList? encoded = some ts
    | [], encoded, h => by
        cases h
        rfl
    | t :: ts, encoded, h => by
        simp only [encASTList?] at h
        cases ht : encAST? t with
        | none =>
            simp [ht] at h
        | some encodedT =>
            cases hts : encASTList? ts with
            | none =>
                simp [ht, hts] at h
            | some encodedTs =>
                simp [ht, hts] at h
                cases h
                have hdecT := decodeEncodedAST?_encAST? t encodedT ht
                have hdecTs := decodeEncodedASTList?_encASTList? ts encodedTs hts
                simp only [decodeEncodedASTList?, MICons, app, hdecT, hdecTs]
end

theorem encAST?_inj (a b encoded : AST)
    (ha : encAST? a = some encoded) (hb : encAST? b = some encoded) :
    a = b := by
  have hda := decodeEncodedAST?_encAST? a encoded ha
  have hdb := decodeEncodedAST?_encAST? b encoded hb
  rw [hda] at hdb
  cases hdb
  rfl

theorem ast_beq_false_symm_mi (a b : AST)
    (h : (a == b) = false) :
    (b == a) = false := by
  cases hba : (b == a) with
  | false => rfl
  | true =>
      have hEq := ast_beq_true_eq_mi b a hba
      subst b
      rw [beq_ast_self a] at h
      cases h

theorem encAST?_beq_false_of_beq_false (a b encodedA encodedB : AST)
    (ha : encAST? a = some encodedA) (hb : encAST? b = some encodedB)
    (hbeq : (a == b) = false) :
    (encodedA == encodedB) = false := by
  cases henc : (encodedA == encodedB) with
  | false => rfl
  | true =>
      have hEncodedEq := ast_beq_true_eq_mi encodedA encodedB henc
      subst encodedB
      have hSourceEq := encAST?_inj a b encodedA ha hb
      subst b
      rw [beq_ast_self a] at hbeq
      cases hbeq

theorem encAST?_eq_of_beq_true (a b encodedA encodedB : AST)
    (ha : encAST? a = some encodedA) (hb : encAST? b = some encodedB)
    (hbeq : (a == b) = true) :
    encodedA = encodedB := by
  have hab := ast_beq_true_eq_mi a b hbeq
  subst b
  rw [ha] at hb
  cases hb
  rfl

theorem encAST?_beq_true_of_beq_true (a b encodedA encodedB : AST)
    (ha : encAST? a = some encodedA) (hb : encAST? b = some encodedB)
    (hbeq : (a == b) = true) :
    (encodedA == encodedB) = true := by
  have henc := encAST?_eq_of_beq_true a b encodedA encodedB ha hb hbeq
  subst encodedB
  exact beq_ast_self encodedA

theorem lookupEncoded?_eq_find?_encAST? (v : String) :
    ∀ (bs : List (String × AST)),
      lookupEncoded? v bs =
        match List.find? (fun b : String × AST => b.fst == v) bs with
        | some (_, term) => encAST? term
        | none => none
  | [] => by
      rfl
  | (w, t) :: rest => by
      by_cases hvw : (v == w) = true
      · have hwv : (w == v) = true := by
          simpa [string_beq_symm_mi v w] using hvw
        simp only [lookupEncoded?, List.find?, hvw, hwv, ↓reduceIte]
      · have hvwFalse : (v == w) = false := by
          cases hcmp : (v == w) <;> simp [hcmp] at hvw ⊢
        have hwvFalse : (w == v) = false := by
          simpa [← string_beq_symm_mi v w] using hvwFalse
        have ih := lookupEncoded?_eq_find?_encAST? v rest
        simp only [lookupEncoded?, List.find?, hvwFalse, hwvFalse,
          Bool.false_eq_true, ↓reduceIte, ih]

theorem encAST?_some_of_find?_encBinds? (v : String) :
    ∀ (bs : List (String × AST)) (encodedBs : AST) (w : String) (old : AST),
      List.find? (fun b : String × AST => b.fst == v) bs = some (w, old) →
      encBinds? bs = some encodedBs →
      ∃ encodedOld, encAST? old = some encodedOld
  | [], _, _, _, hfind, _ => by
      simp only [List.find?_nil] at hfind
      cases hfind
  | (u, t) :: rest, encodedBs, w, old, hfind, hbs => by
      by_cases huv : (u == v) = true
      · simp only [List.find?, huv] at hfind
        cases hfind
        simp only [encBinds?] at hbs
        cases ht : encAST? t with
        | none => simp [ht] at hbs
        | some encodedT => exact ⟨encodedT, rfl⟩
      · have huvFalse : (u == v) = false := by
          cases hcmp : (u == v) <;> simp [hcmp] at huv ⊢
        simp only [List.find?, huvFalse] at hfind
        simp only [encBinds?] at hbs
        cases ht : encAST? t with
        | none => simp [ht] at hbs
        | some _ =>
            cases hrest : encBinds? rest with
            | none => simp [ht, hrest] at hbs
            | some encodedRest =>
                exact encAST?_some_of_find?_encBinds? v rest encodedRest
                  w old hfind hrest

mutual
  theorem matchPat_preserves_encBinds? :
      ∀ (pat term encodedPat encodedTerm encodedBs : AST)
        (bs bsOut : List (String × AST)),
        encAST? pat = some encodedPat →
        encAST? term = some encodedTerm →
        encBinds? bs = some encodedBs →
        AST.matchPat pat term bs = some bsOut →
        ∃ encodedOut, encBinds? bsOut = some encodedOut
    | .var (.base v), term, _, encodedTerm, encodedBs, bs, bsOut,
        hpat, hterm, hbs, hmatch => by
        simp only [encAST?] at hpat
        cases hpat
        simp only [AST.matchPat] at hmatch
        cases hfind : List.find? (fun b : String × AST => b.fst == v) bs with
        | none =>
            simp only [hfind] at hmatch
            cases hmatch
            exact ⟨MIBCons (con0 v) encodedTerm encodedBs, by
              simp only [encBinds?, hterm, hbs]⟩
        | some pair =>
            rcases pair with ⟨_, old⟩
            simp only [hfind] at hmatch
            by_cases hold : (old == term) = true
            · simp only [hold, if_true] at hmatch
              cases hmatch
              exact ⟨encodedBs, hbs⟩
            · have holdFalse : (old == term) = false := by
                cases hcmp : (old == term) <;> simp [hcmp] at hold ⊢
              simp only [holdFalse, Bool.false_eq_true, if_false] at hmatch
              cases hmatch
    | .var (.qualified _ _), _, _, _, _, _, _, hpat, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .subst _ _ _, _, _, _, _, _, _, hpat, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.id s) pats, term, _, encodedTerm, encodedBs, bs, bsOut,
        hpat, hterm, hbs, hmatch => by
        cases pats with
        | nil =>
            simp only [encAST?] at hpat
            cases hpat
            cases term with
            | var p =>
                cases p with
                | base v =>
                    simp only [encAST?] at hterm
                    cases hterm
                    simp [AST.matchPat] at hmatch
                    have hEq := ast_beq_true_eq_mi
                      (AST.sexp (Label.id s) []) (AST.var (.base v)) hmatch.1
                    cases hEq
                | qualified _ _ =>
                    simp only [encAST?] at hterm
                    cases hterm
            | subst _ _ _ =>
                simp only [encAST?] at hterm
                cases hterm
            | sexp l terms =>
                cases l with
                | id t =>
                    cases terms with
                    | nil =>
                        simp only [encAST?] at hterm
                        cases hterm
                        simp only [AST.matchPat, AST.matchPatList, label_id_beq] at hmatch
                        by_cases hst : (s == t) = true
                        · simp only [hst, if_true] at hmatch
                          exact matchPatList_preserves_encBinds? [] [] MINil MINil
                            encodedBs bs bsOut rfl rfl hbs hmatch
                        · have hstFalse : (s == t) = false := by
                            cases hcmp : (s == t) <;> simp [hcmp] at hst ⊢
                          simp only [hstFalse, Bool.false_eq_true, if_false] at hmatch
                          cases hmatch
                    | cons tHead tTail =>
                        change
                          (match encASTList? (tHead :: tTail) with
                          | some encodedArgs => some (MIApp t encodedArgs)
                          | none => none) = some encodedTerm at hterm
                        cases hterms : encASTList? (tHead :: tTail) with
                        | none =>
                            rw [hterms] at hterm
                            cases hterm
                        | some encodedTerms =>
                            rw [hterms] at hterm
                            cases hterm
                            simp only [AST.matchPat, label_id_beq] at hmatch
                            by_cases hst : (s == t) = true
                            · simp only [hst, if_true] at hmatch
                              exact matchPatList_preserves_encBinds? []
                                (tHead :: tTail) MINil encodedTerms encodedBs
                                bs bsOut rfl hterms hbs hmatch
                            · have hstFalse : (s == t) = false := by
                                cases hcmp : (s == t) <;> simp [hcmp] at hst ⊢
                              simp only [hstFalse, Bool.false_eq_true, if_false] at hmatch
                              cases hmatch
                | wild =>
                    simp only [encAST?] at hterm
                    cases hterm
                | listE _ =>
                    simp only [encAST?] at hterm
                    cases hterm
                | listCons _ =>
                    simp only [encAST?] at hterm
                    cases hterm
                | listOne _ =>
                    simp only [encAST?] at hterm
                    cases hterm
        | cons pHead pTail =>
            simp only [encAST?] at hpat
            cases hpats : encASTList? (pHead :: pTail) with
            | none =>
                simp [hpats] at hpat
            | some encodedPats =>
                simp [hpats] at hpat
                cases hpat
                cases term with
                | var p =>
                    cases p with
                    | base v =>
                        simp only [encAST?] at hterm
                        cases hterm
                        simp [AST.matchPat] at hmatch
                        have hEq := ast_beq_true_eq_mi
                          (AST.sexp (Label.id s) (pHead :: pTail))
                          (AST.var (.base v)) hmatch.1
                        cases hEq
                    | qualified _ _ =>
                        simp only [encAST?] at hterm
                        cases hterm
                | subst _ _ _ =>
                    simp only [encAST?] at hterm
                    cases hterm
                | sexp l terms =>
                    cases l with
                    | id t =>
                        cases terms with
                        | nil =>
                            simp only [encAST?] at hterm
                            cases hterm
                            simp only [AST.matchPat, AST.matchPatList, label_id_beq] at hmatch
                            by_cases hst : (s == t) = true
                            · simp only [hst, if_true] at hmatch
                              exact matchPatList_preserves_encBinds?
                                (pHead :: pTail) [] encodedPats MINil
                                encodedBs bs bsOut hpats rfl hbs hmatch
                            · have hstFalse : (s == t) = false := by
                                cases hcmp : (s == t) <;> simp [hcmp] at hst ⊢
                              simp only [hstFalse, Bool.false_eq_true, if_false] at hmatch
                              cases hmatch
                        | cons tHead tTail =>
                            change
                              (match encASTList? (tHead :: tTail) with
                              | some encodedArgs => some (MIApp t encodedArgs)
                              | none => none) = some encodedTerm at hterm
                            cases hterms : encASTList? (tHead :: tTail) with
                            | none =>
                                rw [hterms] at hterm
                                cases hterm
                            | some encodedTerms =>
                                rw [hterms] at hterm
                                cases hterm
                                simp only [AST.matchPat, label_id_beq] at hmatch
                                by_cases hst : (s == t) = true
                                · simp only [hst, if_true] at hmatch
                                  exact matchPatList_preserves_encBinds?
                                    (pHead :: pTail) (tHead :: tTail)
                                    encodedPats encodedTerms encodedBs bs bsOut
                                    hpats hterms hbs hmatch
                                · have hstFalse : (s == t) = false := by
                                    cases hcmp : (s == t) <;> simp [hcmp] at hst ⊢
                                  simp only [hstFalse, Bool.false_eq_true, if_false] at hmatch
                                  cases hmatch
                    | wild =>
                        simp only [encAST?] at hterm
                        cases hterm
                    | listE _ =>
                        simp only [encAST?] at hterm
                        cases hterm
                    | listCons _ =>
                        simp only [encAST?] at hterm
                        cases hterm
                    | listOne _ =>
                        simp only [encAST?] at hterm
                        cases hterm
    | .sexp (.wild) _, _, _, _, _, _, _, hpat, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.listE _) _, _, _, _, _, _, _, hpat, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.listCons _) _, _, _, _, _, _, _, hpat, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.listOne _) _, _, _, _, _, _, _, hpat, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat

  theorem matchPatList_preserves_encBinds? :
      ∀ (pats terms : List AST) (encodedPats encodedTerms encodedBs : AST)
        (bs bsOut : List (String × AST)),
        encASTList? pats = some encodedPats →
        encASTList? terms = some encodedTerms →
        encBinds? bs = some encodedBs →
        AST.matchPatList pats terms bs = some bsOut →
        ∃ encodedOut, encBinds? bsOut = some encodedOut
    | [], [], _, _, encodedBs, bs, bsOut, hpats, hterms, hbs, hmatch => by
        simp only [encASTList?] at hpats hterms
        cases hpats
        cases hterms
        simp only [AST.matchPatList] at hmatch
        cases hmatch
        exact ⟨encodedBs, hbs⟩
    | [], _ :: _, _, _, _, _, _, _, _, _, hmatch => by
        simp only [AST.matchPatList] at hmatch
        cases hmatch
    | _ :: _, [], _, _, _, _, _, _, _, _, hmatch => by
        simp only [AST.matchPatList] at hmatch
        cases hmatch
    | p :: ps, t :: ts, encodedPats, encodedTerms, encodedBs, bs, bsOut,
        hpats, hterms, hbs, hmatch => by
        simp only [encASTList?] at hpats hterms
        cases hp : encAST? p with
        | none =>
            simp [hp] at hpats
        | some encodedP =>
            cases hps : encASTList? ps with
            | none =>
                simp [hp, hps] at hpats
            | some encodedPs =>
                simp [hp, hps] at hpats
                cases hpats
                cases ht : encAST? t with
                | none =>
                    simp [ht] at hterms
                | some encodedT =>
                    cases hts : encASTList? ts with
                    | none =>
                        simp [ht, hts] at hterms
                    | some encodedTs =>
                        simp [ht, hts] at hterms
                        cases hterms
                        cases hhead : AST.matchPat p t bs with
                        | none =>
                            simp only [AST.matchPatList, hhead, Option.bind_none] at hmatch
                            cases hmatch
                        | some bsMid =>
                            simp only [AST.matchPatList, hhead, Option.bind_some] at hmatch
                            obtain ⟨encodedMid, hmid⟩ :=
                              matchPat_preserves_encBinds? p t encodedP encodedT encodedBs
                                bs bsMid hp ht hbs hhead
                            exact matchPatList_preserves_encBinds? ps ts encodedPs
                              encodedTs encodedMid bsMid bsOut hps hts hmid hmatch
end

theorem encAST?_inst_var_lookupEncoded (v : String) :
    ∀ (bs : List (String × AST)) (encodedBs : AST),
      encBinds? bs = some encodedBs →
      encAST? (AST.inst bs (.var (.base v))) =
        some
          (match lookupEncoded? v bs with
          | some encodedTerm => encodedTerm
          | none => MIVar v)
  | [], encodedBs, henc => by
      simp only [encBinds?] at henc
      cases henc
      rfl
  | (w, t) :: rest, encodedBs, henc => by
      simp only [encBinds?] at henc
      cases ht : encAST? t with
      | none =>
          simp [ht] at henc
      | some encodedTerm =>
          cases hrest : encBinds? rest with
          | none =>
              simp [ht, hrest] at henc
          | some encodedRest =>
              simp [ht, hrest] at henc
              cases henc
              by_cases hwv : w = v
              · subst w
                simp only [AST.inst, lookupEncoded?, List.find?, string_beq_self_mi,
                  ht, ↓reduceIte]
              · have hfind : (w == v) = false := beq_eq_false_iff_ne.mpr hwv
                have hlookup : (v == w) = false := by
                  rw [string_beq_symm_mi, hfind]
                simp only [AST.inst, lookupEncoded?, List.find?, hfind, hlookup,
                  Bool.false_eq_true, ↓reduceIte]
                exact encAST?_inst_var_lookupEncoded v rest encodedRest hrest

theorem miLookup_encBinds_eval (v : String) :
    ∀ (bs : List (String × AST)) (encodedBs : AST),
      encBinds? bs = some encodedBs →
      eval pMI (bs.length + 1) (miLookup (con0 v) encodedBs) =
        match lookupEncoded? v bs with
        | some encodedTerm => MISome encodedTerm
        | none => MINone
  | [], encodedBs, henc => by
      simp only [encBinds?] at henc
      cases henc
      simp only [lookupEncoded?, List.length_nil, eval, os_miLookup_nil_data]
  | (w, t) :: rest, encodedBs, henc => by
      simp only [encBinds?] at henc
      cases ht : encAST? t with
      | none =>
          simp [ht] at henc
      | some encodedTerm =>
          cases hrest : encBinds? rest with
          | none =>
              simp [ht, hrest] at henc
          | some encodedRest =>
              simp [ht, hrest] at henc
              cases henc
              by_cases hvw : (v == w) = true
              · have hvw_eq : v = w := beq_iff_eq.mp hvw
                subst w
                have hvv : (v == v) = true := string_beq_self_mi v
                have hsome : IsNormal pMI (MISome encodedTerm) :=
                  normal_MISome encodedTerm (encAST?_some_normal t encodedTerm ht)
                simp only [lookupEncoded?, hvv, ht, List.length_cons, eval,
                  os_miLookup_hit_named]
                exact eval_fixed_of_normal pMI (MISome encodedTerm) hsome rest.length
              · have hvw_false : (v == w) = false := by
                  cases hcmp : (v == w) <;> simp [hcmp] at hvw ⊢
                have ih := miLookup_encBinds_eval v rest encodedRest hrest
                simp only [lookupEncoded?, hvw_false, List.length_cons, eval,
                  os_miLookup_miss_named, ih, Bool.false_eq_true, if_false]

theorem oneStepList_matchVarK_lookup_hit_named (v : String) (term rest : AST)
    (hterm : IsNormal pMI term) (hrest : IsNormal pMI rest) :
    oneStepList pMI
        [ con0 v
        , term
        , MIBCons (con0 v) term rest
        , miLookup (con0 v) (MIBCons (con0 v) term rest) ] =
      some
        [ con0 v
        , term
        , MIBCons (con0 v) term rest
        , MISome term ] := by
  have hv : IsNormal pMI (con0 v) := normal_con0 v
  have hbs : IsNormal pMI (MIBCons (con0 v) term rest) :=
    normal_MIBCons (con0 v) term rest hv hterm hrest
  simp only [IsNormal] at hv hterm hbs
  simp only [oneStepList, hv, hterm, hbs, os_miLookup_hit_named]
  rfl

theorem base_miMatchVarK_lookup_hit_named_raw (v : String) (term rest : AST) :
    baseReducts pMI
      (.sexp (.id "mi-match-varK")
        [con0 v, term, MIBCons (con0 v) term rest,
          miLookup (con0 v) (MIBCons (con0 v) term rest)]) = [] := by
  rfl

theorem os_miMatchVarK_lookup_hit_named (v : String) (term rest : AST)
    (hterm : IsNormal pMI term) (hrest : IsNormal pMI rest) :
    oneStep pMI
        (miMatchVarK (con0 v) term (MIBCons (con0 v) term rest)
          (miLookup (con0 v) (MIBCons (con0 v) term rest))) =
      some (miMatchVarK (con0 v) term (MIBCons (con0 v) term rest) (MISome term)) := by
  rw [oneStep.eq_def]
  simp only [miMatchVarK, app]
  rw [base_miMatchVarK_lookup_hit_named_raw]
  rw [oneStepList_matchVarK_lookup_hit_named v term rest hterm hrest]
  rfl

theorem apply_miMatchVarK_none_on_some_named (v : String) (term rest : AST) :
    applyBaseRewrite
        (rw "match-var-none" (miMatchVarK vV vTerm vBs MINone)
          (MIMatchOk (MIBCons vV vTerm vBs)))
        (miMatchVarK (con0 v) term (MIBCons (con0 v) term rest) (MISome term)) =
      none := by
  have e_mvk : (("mi-match-varK" : String) == "mi-match-varK") = true := by decide
  have e_v_term : (("v" : String) == "term") = false := by decide
  have e_term_bs : (("term" : String) == "bs") = false := by decide
  have e_v_bs : (("v" : String) == "bs") = false := by decide
  simp only [applyBaseRewrite, rw, miMatchVarK, MIBCons, MINone, MISome,
    MIMatchOk, app, pv, vV, vTerm, vBs, AST.matchPat, AST.matchPatList,
    AST.inst, AST.instList, List.find?, label_id_beq, e_mvk,
    e_v_term, e_term_bs, e_v_bs, Option.bind_some, if_pos]
  have e_none_some : (("MINone" : String) == "MISome") = false := by decide
  simp only [con0, AST.matchPat, label_id_beq, e_none_some, Option.bind_none,
    Option.map_none, Bool.false_eq_true, if_false]

theorem apply_miMatchVarK_same_named (v : String) (term rest : AST) :
    applyBaseRewrite
        (rw "match-var-same" (miMatchVarK vV vTerm vBs (MISome vTerm))
          (MIMatchOk vBs))
        (miMatchVarK (con0 v) term (MIBCons (con0 v) term rest) (MISome term)) =
      some (MIMatchOk (MIBCons (con0 v) term rest)) := by
  have e_mvk : (("mi-match-varK" : String) == "mi-match-varK") = true := by decide
  have e_some : (("MISome" : String) == "MISome") = true := by decide
  have e_v_term : (("v" : String) == "term") = false := by decide
  have e_term_bs : (("term" : String) == "bs") = false := by decide
  have e_v_bs : (("v" : String) == "bs") = false := by decide
  have e_bs_term : (("bs" : String) == "term") = false := by decide
  have e_term_term : (("term" : String) == "term") = true := by decide
  have e_bs_bs : (("bs" : String) == "bs") = true := by decide
  have e_same : (term == term) = true := beq_ast_self term
  simp only [applyBaseRewrite, rw, miMatchVarK, MIBCons, MISome, MIMatchOk,
    app, pv, vV, vTerm, vBs, AST.matchPat, AST.matchPatList, AST.inst,
    AST.instList, List.find?, label_id_beq, e_mvk, e_some,
    e_v_term, e_term_bs, e_v_bs, e_bs_term, e_term_term, e_bs_bs, e_same,
    Option.bind_some, Option.map_some, if_pos]

theorem apply_miMatchVarK_same_on_beq_named (v : String) (term old bs : AST)
    (heq : (term == old) = true) :
    applyBaseRewrite
        (rw "match-var-same" (miMatchVarK vV vTerm vBs (MISome vTerm))
          (MIMatchOk vBs))
        (miMatchVarK (con0 v) term bs (MISome old)) =
      some (MIMatchOk bs) := by
  have e_mvk : (("mi-match-varK" : String) == "mi-match-varK") = true := by decide
  have e_some : (("MISome" : String) == "MISome") = true := by decide
  have e_v_term : (("v" : String) == "term") = false := by decide
  have e_term_bs : (("term" : String) == "bs") = false := by decide
  have e_v_bs : (("v" : String) == "bs") = false := by decide
  have e_bs_term : (("bs" : String) == "term") = false := by decide
  have e_term_term : (("term" : String) == "term") = true := by decide
  have e_bs_bs : (("bs" : String) == "bs") = true := by decide
  simp only [applyBaseRewrite, rw, miMatchVarK, MISome, MIMatchOk,
    app, pv, vV, vTerm, vBs, AST.matchPat, AST.matchPatList, AST.inst,
    AST.instList, List.find?, label_id_beq, e_mvk, e_some,
    e_v_term, e_term_bs, e_v_bs, e_bs_term, e_term_term, e_bs_bs, heq,
    Option.bind_some, Option.map_some, if_pos]

theorem apply_miMatchVarK_same_on_distinct_named (v : String) (term old rest : AST)
    (hneq : (term == old) = false) :
    applyBaseRewrite
        (rw "match-var-same" (miMatchVarK vV vTerm vBs (MISome vTerm))
          (MIMatchOk vBs))
        (miMatchVarK (con0 v) term (MIBCons (con0 v) old rest) (MISome old)) =
      none := by
  have e_mvk : (("mi-match-varK" : String) == "mi-match-varK") = true := by decide
  have e_some : (("MISome" : String) == "MISome") = true := by decide
  have e_v_term : (("v" : String) == "term") = false := by decide
  have e_term_bs : (("term" : String) == "bs") = false := by decide
  have e_v_bs : (("v" : String) == "bs") = false := by decide
  have e_bs_term : (("bs" : String) == "term") = false := by decide
  have e_term_term : (("term" : String) == "term") = true := by decide
  simp only [applyBaseRewrite, rw, miMatchVarK, MIBCons, MISome, MIMatchOk,
    app, pv, vV, vTerm, vBs, AST.matchPat, AST.matchPatList, AST.inst,
    AST.instList, List.find?, label_id_beq, e_mvk, e_some, e_v_term,
    e_term_bs, e_v_bs, e_bs_term, e_term_term, hneq, Option.bind_some,
    Bool.false_eq_true, if_true, if_false, Option.bind_none, Option.map_none]

theorem apply_miMatchVarK_same_on_distinct_general (v : String) (term old bs : AST)
    (hneq : (term == old) = false) :
    applyBaseRewrite
        (rw "match-var-same" (miMatchVarK vV vTerm vBs (MISome vTerm))
          (MIMatchOk vBs))
        (miMatchVarK (con0 v) term bs (MISome old)) =
      none := by
  have e_mvk : (("mi-match-varK" : String) == "mi-match-varK") = true := by decide
  have e_some : (("MISome" : String) == "MISome") = true := by decide
  have e_v_term : (("v" : String) == "term") = false := by decide
  have e_term_bs : (("term" : String) == "bs") = false := by decide
  have e_v_bs : (("v" : String) == "bs") = false := by decide
  have e_bs_term : (("bs" : String) == "term") = false := by decide
  have e_term_term : (("term" : String) == "term") = true := by decide
  simp only [applyBaseRewrite, rw, miMatchVarK, MISome, MIMatchOk,
    app, pv, vV, vTerm, vBs, AST.matchPat, AST.matchPatList, AST.inst,
    AST.instList, List.find?, label_id_beq, e_mvk, e_some, e_v_term,
    e_term_bs, e_v_bs, e_bs_term, e_term_term, hneq, Option.bind_some,
    Bool.false_eq_true, if_true, if_false, Option.bind_none, Option.map_none]

theorem apply_miMatchVarK_diff_named (v : String) (term old rest : AST) :
    applyBaseRewrite
        (rw "match-var-diff" (miMatchVarK vV vTerm vBs (MISome vOld)) MIMatchFail)
        (miMatchVarK (con0 v) term (MIBCons (con0 v) old rest) (MISome old)) =
      some MIMatchFail := by
  have e_mvk : (("mi-match-varK" : String) == "mi-match-varK") = true := by decide
  have e_some : (("MISome" : String) == "MISome") = true := by decide
  have e_v_term : (("v" : String) == "term") = false := by decide
  have e_term_bs : (("term" : String) == "bs") = false := by decide
  have e_v_bs : (("v" : String) == "bs") = false := by decide
  have e_v_old : (("v" : String) == "old") = false := by decide
  have e_bs_old : (("bs" : String) == "old") = false := by decide
  have e_term_old : (("term" : String) == "old") = false := by decide
  simp only [applyBaseRewrite, rw, miMatchVarK, MIBCons, MISome, MIMatchFail,
    app, pv, vV, vTerm, vBs, vOld, AST.matchPat, AST.matchPatList,
    List.find?, label_id_beq, e_mvk, e_some, e_v_term, e_term_bs, e_v_bs,
    e_v_old, e_bs_old, e_term_old, Option.bind_some, Option.map_some,
    if_pos]
  rfl

theorem apply_miMatchVarK_diff_general (v : String) (term old bs : AST) :
    applyBaseRewrite
        (rw "match-var-diff" (miMatchVarK vV vTerm vBs (MISome vOld)) MIMatchFail)
        (miMatchVarK (con0 v) term bs (MISome old)) =
      some MIMatchFail := by
  have e_mvk : (("mi-match-varK" : String) == "mi-match-varK") = true := by decide
  have e_some : (("MISome" : String) == "MISome") = true := by decide
  have e_v_term : (("v" : String) == "term") = false := by decide
  have e_term_bs : (("term" : String) == "bs") = false := by decide
  have e_v_bs : (("v" : String) == "bs") = false := by decide
  have e_v_old : (("v" : String) == "old") = false := by decide
  have e_bs_old : (("bs" : String) == "old") = false := by decide
  have e_term_old : (("term" : String) == "old") = false := by decide
  simp only [applyBaseRewrite, rw, miMatchVarK, MISome, MIMatchFail,
    app, pv, vV, vTerm, vBs, vOld, AST.matchPat, AST.matchPatList,
    List.find?, label_id_beq, e_mvk, e_some, e_v_term, e_term_bs, e_v_bs,
    e_v_old, e_bs_old, e_term_old, Option.bind_some, Option.map_some,
    if_pos]
  rfl

theorem apply_lookup_nil_on_matchVarK_same_named (v : String) (term rest : AST) :
    applyBaseRewrite (rw "lookup-nil" (miLookup vV MIBNil) MINone)
        (miMatchVarK (con0 v) term (MIBCons (con0 v) term rest) (MISome term)) =
      none := by
  rfl

theorem apply_lookup_hit_on_matchVarK_same_named (v : String) (term rest : AST) :
    applyBaseRewrite (rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT))
        (miMatchVarK (con0 v) term (MIBCons (con0 v) term rest) (MISome term)) =
      none := by
  rfl

theorem apply_lookup_miss_on_matchVarK_same_named (v : String) (term rest : AST) :
    applyBaseRewrite
        (rw "lookup-miss" (miLookup vV (MIBCons vW vT vRest)) (miLookup vV vRest))
        (miMatchVarK (con0 v) term (MIBCons (con0 v) term rest) (MISome term)) =
      none := by
  rfl

theorem apply_matchVar_on_matchVarK_same_named (v : String) (term rest : AST) :
    applyBaseRewrite
        (rw "match-var" (miMatchVar vV vTerm vBs)
          (miMatchVarK vV vTerm vBs (miLookup vV vBs)))
        (miMatchVarK (con0 v) term (MIBCons (con0 v) term rest) (MISome term)) =
      none := by
  rfl

theorem apply_lookup_nil_on_matchVarK_diff_named (v : String) (term old rest : AST) :
    applyBaseRewrite (rw "lookup-nil" (miLookup vV MIBNil) MINone)
        (miMatchVarK (con0 v) term (MIBCons (con0 v) old rest) (MISome old)) =
      none := by
  rfl

theorem apply_lookup_hit_on_matchVarK_diff_named (v : String) (term old rest : AST) :
    applyBaseRewrite (rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT))
        (miMatchVarK (con0 v) term (MIBCons (con0 v) old rest) (MISome old)) =
      none := by
  rfl

theorem apply_lookup_miss_on_matchVarK_diff_named (v : String) (term old rest : AST) :
    applyBaseRewrite
        (rw "lookup-miss" (miLookup vV (MIBCons vW vT vRest)) (miLookup vV vRest))
        (miMatchVarK (con0 v) term (MIBCons (con0 v) old rest) (MISome old)) =
      none := by
  rfl

theorem apply_matchVar_on_matchVarK_diff_named (v : String) (term old rest : AST) :
    applyBaseRewrite
        (rw "match-var" (miMatchVar vV vTerm vBs)
          (miMatchVarK vV vTerm vBs (miLookup vV vBs)))
        (miMatchVarK (con0 v) term (MIBCons (con0 v) old rest) (MISome old)) =
      none := by
  rfl

theorem apply_miMatchVarK_none_on_some_diff_named (v : String) (term old rest : AST) :
    applyBaseRewrite
        (rw "match-var-none" (miMatchVarK vV vTerm vBs MINone)
          (MIMatchOk (MIBCons vV vTerm vBs)))
        (miMatchVarK (con0 v) term (MIBCons (con0 v) old rest) (MISome old)) =
      none := by
  have e_mvk : (("mi-match-varK" : String) == "mi-match-varK") = true := by decide
  have e_v_term : (("v" : String) == "term") = false := by decide
  have e_term_bs : (("term" : String) == "bs") = false := by decide
  have e_v_bs : (("v" : String) == "bs") = false := by decide
  simp only [applyBaseRewrite, rw, miMatchVarK, MIBCons, MINone, MISome,
    MIMatchOk, app, pv, vV, vTerm, vBs, AST.matchPat, AST.matchPatList,
    AST.inst, AST.instList, List.find?, label_id_beq, e_mvk,
    e_v_term, e_term_bs, e_v_bs, Option.bind_some, if_pos]
  have e_none_some : (("MINone" : String) == "MISome") = false := by decide
  simp only [con0, AST.matchPat, label_id_beq, e_none_some, Option.bind_none,
    Option.map_none, Bool.false_eq_true, if_false]

theorem os_miMatchVarK_none_general (vName term bs : AST) :
    oneStep pMI (miMatchVarK vName term bs MINone) =
      some (MIMatchOk (MIBCons vName term bs)) := by
  rfl

theorem apply_lookup_nil_on_matchVarK_some_general (v : String) (term old bs : AST) :
    applyBaseRewrite (rw "lookup-nil" (miLookup vV MIBNil) MINone)
        (miMatchVarK (con0 v) term bs (MISome old)) =
      none := by
  rfl

theorem apply_lookup_hit_on_matchVarK_some_general (v : String) (term old bs : AST) :
    applyBaseRewrite (rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT))
        (miMatchVarK (con0 v) term bs (MISome old)) =
      none := by
  rfl

theorem apply_lookup_miss_on_matchVarK_some_general (v : String) (term old bs : AST) :
    applyBaseRewrite
        (rw "lookup-miss" (miLookup vV (MIBCons vW vT vRest)) (miLookup vV vRest))
        (miMatchVarK (con0 v) term bs (MISome old)) =
      none := by
  rfl

theorem apply_matchVar_on_matchVarK_some_general (v : String) (term old bs : AST) :
    applyBaseRewrite
        (rw "match-var" (miMatchVar vV vTerm vBs)
          (miMatchVarK vV vTerm vBs (miLookup vV vBs)))
        (miMatchVarK (con0 v) term bs (MISome old)) =
      none := by
  rfl

theorem apply_miMatchVarK_none_on_some_general (v : String) (term old bs : AST) :
    applyBaseRewrite
        (rw "match-var-none" (miMatchVarK vV vTerm vBs MINone)
          (MIMatchOk (MIBCons vV vTerm vBs)))
        (miMatchVarK (con0 v) term bs (MISome old)) =
      none := by
  have e_mvk : (("mi-match-varK" : String) == "mi-match-varK") = true := by decide
  have e_v_term : (("v" : String) == "term") = false := by decide
  have e_term_bs : (("term" : String) == "bs") = false := by decide
  have e_v_bs : (("v" : String) == "bs") = false := by decide
  simp only [applyBaseRewrite, rw, miMatchVarK, MINone, MISome, MIMatchOk,
    app, pv, vV, vTerm, vBs, AST.matchPat, AST.matchPatList,
    AST.inst, AST.instList, List.find?, label_id_beq, e_mvk,
    e_v_term, e_term_bs, e_v_bs, Option.bind_some, if_pos]
  have e_none_some : (("MINone" : String) == "MISome") = false := by decide
  simp only [con0, AST.matchPat, label_id_beq, e_none_some, Option.bind_none,
    Option.map_none, Bool.false_eq_true, if_false]

theorem miRules_matchVarK_same_prefix :
    miRules =
      rw "lookup-nil" (miLookup vV MIBNil) MINone ::
      rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT) ::
      rw "lookup-miss" (miLookup vV (MIBCons vW vT vRest)) (miLookup vV vRest) ::
      rw "match-var" (miMatchVar vV vTerm vBs) (miMatchVarK vV vTerm vBs (miLookup vV vBs)) ::
      rw "match-var-none" (miMatchVarK vV vTerm vBs MINone)
        (MIMatchOk (MIBCons vV vTerm vBs)) ::
      rw "match-var-same" (miMatchVarK vV vTerm vBs (MISome vTerm))
        (MIMatchOk vBs) ::
      List.drop 6 miRules := by
  rfl

theorem baseReducts_miMatchVarK_same_named_head (v : String) (term rest : AST) :
    ∃ tail,
      baseReducts pMI
          (miMatchVarK (con0 v) term (MIBCons (con0 v) term rest) (MISome term)) =
        MIMatchOk (MIBCons (con0 v) term rest) :: tail := by
  let target := miMatchVarK (con0 v) term (MIBCons (con0 v) term rest) (MISome term)
  refine ⟨(List.drop 6 miRules).filterMap (fun rd => applyBaseRewrite rd target), ?_⟩
  change miRules.filterMap (fun rd => applyBaseRewrite rd target) =
    MIMatchOk (MIBCons (con0 v) term rest) ::
      (List.drop 6 miRules).filterMap (fun rd => applyBaseRewrite rd target)
  rw [miRules_matchVarK_same_prefix]
  dsimp only [target]
  simp only [List.filterMap_cons, apply_lookup_nil_on_matchVarK_same_named,
    apply_lookup_hit_on_matchVarK_same_named, apply_lookup_miss_on_matchVarK_same_named,
    apply_matchVar_on_matchVarK_same_named, apply_miMatchVarK_none_on_some_named,
    apply_miMatchVarK_same_named, List.drop]

theorem miRules_matchVarK_diff_prefix :
    miRules =
      rw "lookup-nil" (miLookup vV MIBNil) MINone ::
      rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT) ::
      rw "lookup-miss" (miLookup vV (MIBCons vW vT vRest)) (miLookup vV vRest) ::
      rw "match-var" (miMatchVar vV vTerm vBs) (miMatchVarK vV vTerm vBs (miLookup vV vBs)) ::
      rw "match-var-none" (miMatchVarK vV vTerm vBs MINone)
        (MIMatchOk (MIBCons vV vTerm vBs)) ::
      rw "match-var-same" (miMatchVarK vV vTerm vBs (MISome vTerm))
        (MIMatchOk vBs) ::
      rw "match-var-diff" (miMatchVarK vV vTerm vBs (MISome vOld)) MIMatchFail ::
      List.drop 7 miRules := by
  rfl

theorem baseReducts_miMatchVarK_diff_named_head (v : String) (term old rest : AST)
    (hneq : (term == old) = false) :
    ∃ tail,
      baseReducts pMI
          (miMatchVarK (con0 v) term (MIBCons (con0 v) old rest) (MISome old)) =
        MIMatchFail :: tail := by
  let target := miMatchVarK (con0 v) term (MIBCons (con0 v) old rest) (MISome old)
  refine ⟨(List.drop 7 miRules).filterMap (fun rd => applyBaseRewrite rd target), ?_⟩
  change miRules.filterMap (fun rd => applyBaseRewrite rd target) =
    MIMatchFail ::
      (List.drop 7 miRules).filterMap (fun rd => applyBaseRewrite rd target)
  rw [miRules_matchVarK_diff_prefix]
  dsimp only [target]
  simp only [List.filterMap_cons, apply_lookup_nil_on_matchVarK_diff_named,
    apply_lookup_hit_on_matchVarK_diff_named, apply_lookup_miss_on_matchVarK_diff_named,
    apply_matchVar_on_matchVarK_diff_named, apply_miMatchVarK_none_on_some_diff_named,
    apply_miMatchVarK_same_on_distinct_named, apply_miMatchVarK_diff_named, hneq,
    List.drop]

theorem os_miMatchVarK_same_named (v : String) (term rest : AST) :
    oneStep pMI
        (miMatchVarK (con0 v) term (MIBCons (con0 v) term rest) (MISome term)) =
      some (MIMatchOk (MIBCons (con0 v) term rest)) := by
  obtain ⟨tail, hhead⟩ := baseReducts_miMatchVarK_same_named_head v term rest
  change (match
      baseReducts pMI
        (miMatchVarK (con0 v) term (MIBCons (con0 v) term rest) (MISome term)) with
    | r :: _ => some r
    | [] =>
      (oneStepList pMI [con0 v, term, MIBCons (con0 v) term rest, MISome term]).map
        (fun args' => AST.sexp (Label.id "mi-match-varK") args')) =
      some (MIMatchOk (MIBCons (con0 v) term rest))
  rw [hhead]

theorem os_miMatchVarK_diff_named (v : String) (term old rest : AST)
    (hneq : (term == old) = false) :
    oneStep pMI
        (miMatchVarK (con0 v) term (MIBCons (con0 v) old rest) (MISome old)) =
      some MIMatchFail := by
  obtain ⟨tail, hhead⟩ := baseReducts_miMatchVarK_diff_named_head v term old rest hneq
  change (match
      baseReducts pMI
        (miMatchVarK (con0 v) term (MIBCons (con0 v) old rest) (MISome old)) with
    | r :: _ => some r
    | [] =>
      (oneStepList pMI [con0 v, term, MIBCons (con0 v) old rest, MISome old]).map
        (fun args' => AST.sexp (Label.id "mi-match-varK") args')) =
      some MIMatchFail
  rw [hhead]

theorem baseReducts_miMatchVarK_same_on_beq_head (v : String) (term old bs : AST)
    (heq : (term == old) = true) :
    ∃ tail,
      baseReducts pMI (miMatchVarK (con0 v) term bs (MISome old)) =
        MIMatchOk bs :: tail := by
  let target := miMatchVarK (con0 v) term bs (MISome old)
  refine ⟨(List.drop 6 miRules).filterMap (fun rd => applyBaseRewrite rd target), ?_⟩
  change miRules.filterMap (fun rd => applyBaseRewrite rd target) =
    MIMatchOk bs :: (List.drop 6 miRules).filterMap (fun rd => applyBaseRewrite rd target)
  rw [miRules_matchVarK_same_prefix]
  dsimp only [target]
  simp only [List.filterMap_cons, apply_lookup_nil_on_matchVarK_some_general,
    apply_lookup_hit_on_matchVarK_some_general, apply_lookup_miss_on_matchVarK_some_general,
    apply_matchVar_on_matchVarK_some_general, apply_miMatchVarK_none_on_some_general,
    apply_miMatchVarK_same_on_beq_named, heq, List.drop]

theorem os_miMatchVarK_same_on_beq_named (v : String) (term old bs : AST)
    (heq : (term == old) = true) :
    oneStep pMI (miMatchVarK (con0 v) term bs (MISome old)) =
      some (MIMatchOk bs) := by
  obtain ⟨tail, hhead⟩ := baseReducts_miMatchVarK_same_on_beq_head v term old bs heq
  change (match baseReducts pMI (miMatchVarK (con0 v) term bs (MISome old)) with
    | r :: _ => some r
    | [] =>
      (oneStepList pMI [con0 v, term, bs, MISome old]).map
        (fun args' => AST.sexp (Label.id "mi-match-varK") args')) =
      some (MIMatchOk bs)
  rw [hhead]

theorem baseReducts_miMatchVarK_diff_general_head (v : String) (term old bs : AST)
    (hneq : (term == old) = false) :
    ∃ tail,
      baseReducts pMI (miMatchVarK (con0 v) term bs (MISome old)) =
        MIMatchFail :: tail := by
  let target := miMatchVarK (con0 v) term bs (MISome old)
  refine ⟨(List.drop 7 miRules).filterMap (fun rd => applyBaseRewrite rd target), ?_⟩
  change miRules.filterMap (fun rd => applyBaseRewrite rd target) =
    MIMatchFail :: (List.drop 7 miRules).filterMap (fun rd => applyBaseRewrite rd target)
  rw [miRules_matchVarK_diff_prefix]
  dsimp only [target]
  simp only [List.filterMap_cons, apply_lookup_nil_on_matchVarK_some_general,
    apply_lookup_hit_on_matchVarK_some_general, apply_lookup_miss_on_matchVarK_some_general,
    apply_matchVar_on_matchVarK_some_general, apply_miMatchVarK_none_on_some_general,
    apply_miMatchVarK_same_on_distinct_general, apply_miMatchVarK_diff_general, hneq,
    List.drop]

theorem os_miMatchVarK_diff_general (v : String) (term old bs : AST)
    (hneq : (term == old) = false) :
    oneStep pMI (miMatchVarK (con0 v) term bs (MISome old)) =
      some MIMatchFail := by
  obtain ⟨tail, hhead⟩ := baseReducts_miMatchVarK_diff_general_head v term old bs hneq
  change (match baseReducts pMI (miMatchVarK (con0 v) term bs (MISome old)) with
    | r :: _ => some r
    | [] =>
      (oneStepList pMI [con0 v, term, bs, MISome old]).map
        (fun args' => AST.sexp (Label.id "mi-match-varK") args')) =
      some MIMatchFail
  rw [hhead]

theorem base_miMatchVarK_lookup_arg_raw (v : String) (term bs tail : AST) :
    baseReducts pMI
      (.sexp (.id "mi-match-varK") [con0 v, term, bs, miLookup (con0 v) tail]) = [] := by
  rfl

theorem os_miMatchVarK_bs_lookup_arg_step (v : String)
    (term bs bs' tail : AST)
    (hterm : IsNormal pMI term)
    (hstep : oneStep pMI bs = some bs') :
    oneStep pMI
        (miMatchVarK (con0 v) term bs (miLookup (con0 v) tail)) =
      some (miMatchVarK (con0 v) term bs' (miLookup (con0 v) tail)) := by
  have hv : IsNormal pMI (con0 v) := normal_con0 v
  rw [oneStep.eq_def]
  simp only [miMatchVarK, app]
  rw [base_miMatchVarK_lookup_arg_raw]
  simp only [IsNormal] at hv hterm
  simp only [oneStepList, hv, hterm, hstep, Option.map_some]

theorem os_miMatchVarK_term_lookup_arg_step (v : String)
    (term term' bs tail : AST)
    (hstep : oneStep pMI term = some term') :
    oneStep pMI
        (miMatchVarK (con0 v) term bs (miLookup (con0 v) tail)) =
      some (miMatchVarK (con0 v) term' bs (miLookup (con0 v) tail)) := by
  have hv : IsNormal pMI (con0 v) := normal_con0 v
  rw [oneStep.eq_def]
  simp only [miMatchVarK, app]
  rw [base_miMatchVarK_lookup_arg_raw]
  simp only [IsNormal] at hv
  simp only [oneStepList, hv, hstep, Option.map_some]

theorem os_miMatchVarK_lookup_nil_arg (v : String) (term bs : AST)
    (hterm : IsNormal pMI term) (hbs : IsNormal pMI bs) :
    oneStep pMI (miMatchVarK (con0 v) term bs (miLookup (con0 v) MIBNil)) =
      some (miMatchVarK (con0 v) term bs MINone) := by
  have hv : IsNormal pMI (con0 v) := normal_con0 v
  rw [oneStep.eq_def]
  simp only [miMatchVarK, app]
  rw [base_miMatchVarK_lookup_arg_raw]
  simp only [IsNormal] at hv hterm hbs
  simp only [oneStepList, hv, hterm, hbs, os_miLookup_nil_data]
  rfl

theorem os_miMatchVarK_lookup_hit_arg (v : String) (term bs old rest : AST)
    (hterm : IsNormal pMI term) (hbs : IsNormal pMI bs) :
    oneStep pMI
        (miMatchVarK (con0 v) term bs
          (miLookup (con0 v) (MIBCons (con0 v) old rest))) =
      some (miMatchVarK (con0 v) term bs (MISome old)) := by
  have hv : IsNormal pMI (con0 v) := normal_con0 v
  rw [oneStep.eq_def]
  simp only [miMatchVarK, app]
  rw [base_miMatchVarK_lookup_arg_raw]
  simp only [IsNormal] at hv hterm hbs
  simp only [oneStepList, hv, hterm, hbs, os_miLookup_hit_named]
  rfl

theorem os_miMatchVarK_lookup_miss_arg (v w : String) (term bs old rest : AST)
    (hvw : (v == w) = false) (hterm : IsNormal pMI term) (hbs : IsNormal pMI bs) :
    oneStep pMI
        (miMatchVarK (con0 v) term bs
          (miLookup (con0 v) (MIBCons (con0 w) old rest))) =
      some (miMatchVarK (con0 v) term bs (miLookup (con0 v) rest)) := by
  have hv : IsNormal pMI (con0 v) := normal_con0 v
  rw [oneStep.eq_def]
  simp only [miMatchVarK, app]
  rw [base_miMatchVarK_lookup_arg_raw]
  simp only [IsNormal] at hv hterm hbs
  simp only [oneStepList, hv, hterm, hbs, os_miLookup_miss_named, hvw]
  rfl

theorem miMatchVarK_lookup_encBinds_eval (v : String) (term wholeBs : AST)
    (hterm : IsNormal pMI term) (hwhole : IsNormal pMI wholeBs) :
    ∀ (bs : List (String × AST)) (encodedTail : AST),
      encBinds? bs = some encodedTail →
      eval pMI (bs.length + 2)
          (miMatchVarK (con0 v) term wholeBs (miLookup (con0 v) encodedTail)) =
        match lookupEncoded? v bs with
        | some old =>
            if (term == old) = true then MIMatchOk wholeBs else MIMatchFail
        | none => MIMatchOk (MIBCons (con0 v) term wholeBs)
  | [], encodedTail, henc => by
      simp only [encBinds?] at henc
      cases henc
      simp only [lookupEncoded?, List.length_nil, eval,
        os_miMatchVarK_lookup_nil_arg, os_miMatchVarK_none_general, hterm, hwhole]
  | (w, t) :: rest, encodedTail, henc => by
      simp only [encBinds?] at henc
      cases ht : encAST? t with
      | none =>
          simp [ht] at henc
      | some encodedTerm =>
          cases hrest : encBinds? rest with
          | none =>
              simp [ht, hrest] at henc
          | some encodedRest =>
              simp [ht, hrest] at henc
              cases henc
              by_cases hvw : (v == w) = true
              · have hvw_eq : v = w := beq_iff_eq.mp hvw
                subst w
                have hvv : (v == v) = true := string_beq_self_mi v
                simp only [lookupEncoded?, hvv, ht, List.length_cons, eval,
                  os_miMatchVarK_lookup_hit_arg, hterm, hwhole]
                by_cases hsame : (term == encodedTerm) = true
                · have hres : IsNormal pMI (MIMatchOk wholeBs) :=
                    normal_MIMatchOk wholeBs hwhole
                  simp only [hsame, os_miMatchVarK_same_on_beq_named]
                  simpa [eval, hsame, if_true] using
                    eval_fixed_of_normal pMI (MIMatchOk wholeBs) hres rest.length
                · have hdiff : (term == encodedTerm) = false := by
                    cases hcmp : (term == encodedTerm) <;> simp [hcmp] at hsame ⊢
                  simp only [hdiff, os_miMatchVarK_diff_general]
                  simpa [eval, hdiff, Bool.false_eq_true, if_false] using
                    eval_fixed_of_normal pMI MIMatchFail normal_MIMatchFail rest.length
              · have hvw_false : (v == w) = false := by
                  cases hcmp : (v == w) <;> simp [hcmp] at hvw ⊢
                have ih := miMatchVarK_lookup_encBinds_eval v term wholeBs hterm hwhole
                  rest encodedRest hrest
                simpa [lookupEncoded?, hvw_false, List.length_cons, eval,
                  os_miMatchVarK_lookup_miss_arg, hterm, hwhole,
                  Bool.false_eq_true, if_false] using ih

theorem miMatch_var_encodedBinds_sim (v : String) (term encodedBs : AST)
    (hterm : IsNormal pMI term) :
    ∀ (bs : List (String × AST)),
      encBinds? bs = some encodedBs →
      eval pMI (bs.length + 4) (miMatch (MIVar v) term encodedBs) =
        match lookupEncoded? v bs with
        | some old =>
            if (term == old) = true then MIMatchOk encodedBs else MIMatchFail
        | none => MIMatchOk (MIBCons (con0 v) term encodedBs)
  | bs, henc => by
      have hbs : IsNormal pMI encodedBs := encBinds?_some_normal bs encodedBs henc
      simp only [eval, MIVar, os_miMatch_var_data, os_miMatchVar]
      exact miMatchVarK_lookup_encBinds_eval v term encodedBs hterm hbs bs encodedBs henc

theorem os_miMatchList_nil_ok (bs : AST) :
    oneStep pMI (miMatchList MINil MINil bs) = some (MIMatchOk bs) := by
  rfl

theorem os_miMatchList_nil_cons_fail (t ts bs : AST) :
    oneStep pMI (miMatchList MINil (MICons t ts) bs) = some MIMatchFail := by
  rfl

theorem os_miMatchList_cons_ok (p ps t ts bs : AST) :
    oneStep pMI (miMatchList (MICons p ps) (MICons t ts) bs) =
      some (miMatchListK ps ts (miMatch p t bs)) := by
  rfl

theorem os_miMatchList_cons_nil_fail (p ps bs : AST) :
    oneStep pMI (miMatchList (MICons p ps) MINil bs) = some MIMatchFail := by
  rfl

theorem os_miMatchListK_ok (ps ts bs : AST) :
    oneStep pMI (miMatchListK ps ts (MIMatchOk bs)) =
      some (miMatchList ps ts bs) := by
  rfl

theorem os_miMatchListK_fail (ps ts : AST) :
    oneStep pMI (miMatchListK ps ts MIMatchFail) = some MIMatchFail := by
  rfl

theorem miMatchList_nil_nil_sim (bs : AST) :
    eval pMI 1 (miMatchList MINil MINil bs) = MIMatchOk bs := by
  simp only [eval, os_miMatchList_nil_ok]

theorem miMatchList_nil_cons_fail_sim (t ts bs : AST) :
    eval pMI 1 (miMatchList MINil (MICons t ts) bs) = MIMatchFail := by
  simp only [eval, os_miMatchList_nil_cons_fail]

theorem miMatchList_cons_nil_fail_sim (p ps bs : AST) :
    eval pMI 1 (miMatchList (MICons p ps) MINil bs) = MIMatchFail := by
  simp only [eval, os_miMatchList_cons_nil_fail]

theorem miMatchListK_fail_sim (ps ts : AST) :
    eval pMI 1 (miMatchListK ps ts MIMatchFail) = MIMatchFail := by
  simp only [eval, os_miMatchListK_fail]

theorem miMatchListK_ok_sim (ps ts bs : AST) :
    eval pMI 1 (miMatchListK ps ts (MIMatchOk bs)) = miMatchList ps ts bs := by
  simp only [eval, os_miMatchListK_ok]

inductive MatchActiveShape : AST → Prop where
  | match (pat term bs : AST) : MatchActiveShape (miMatch pat term bs)
  | matchVar (v term bs : AST) : MatchActiveShape (miMatchVar v term bs)
  | matchVarK (v term bs r : AST) : MatchActiveShape (miMatchVarK v term bs r)
  | matchList (ps ts bs : AST) : MatchActiveShape (miMatchList ps ts bs)
  | matchListK (ps ts r : AST) : MatchActiveShape (miMatchListK ps ts r)

theorem match_active_fuel_one_mi {t : AST} (ht : MatchActiveShape t) :
    ∀ k, k < 1 → MatchActiveShape (eval pMI k t) := by
  intro k hk
  cases k with
  | zero =>
      simpa only [eval] using ht
  | succ k =>
      exact False.elim
        (Nat.not_lt_zero k (Nat.succ_lt_succ_iff.mp hk))

theorem baseReducts_miMatchListK_active_raw (ps ts r : AST)
    (hactive : MatchActiveShape r) :
    baseReducts pMI (miMatchListK ps ts r) = [] := by
  cases hactive <;> rfl

theorem os_miMatchListK_active_step (ps ts r r' : AST)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI ts)
    (hactive : MatchActiveShape r)
    (hstep : oneStep pMI r = some r') :
    oneStep pMI (miMatchListK ps ts r) = some (miMatchListK ps ts r') := by
  rw [oneStep.eq_def]
  change (match baseReducts pMI (miMatchListK ps ts r) with
    | q :: _ => some q
    | [] => (oneStepList pMI [ps, ts, r]).map
        (fun args' => AST.sexp (Label.id "mi-match-listK") args')) =
      some (miMatchListK ps ts r')
  rw [baseReducts_miMatchListK_active_raw ps ts r hactive]
  simp only [IsNormal] at hps hts
  simp only [oneStepList, hps, hts, hstep, Option.map_some]
  rfl

theorem os_miMatchListK_tail_active_step (ps ts ts' r : AST)
    (hps : IsNormal pMI ps)
    (hactive : MatchActiveShape r)
    (hstep : oneStep pMI ts = some ts') :
    oneStep pMI (miMatchListK ps ts r) =
      some (miMatchListK ps ts' r) := by
  rw [oneStep.eq_def]
  change (match baseReducts pMI (miMatchListK ps ts r) with
    | q :: _ => some q
    | [] => (oneStepList pMI [ps, ts, r]).map
        (fun args' => AST.sexp (Label.id "mi-match-listK") args')) =
      some (miMatchListK ps ts' r)
  rw [baseReducts_miMatchListK_active_raw ps ts r hactive]
  simp only [IsNormal] at hps
  simp only [oneStepList, hps, hstep, Option.map_some]
  rfl

theorem miMatchList_cons_head_step_eval (p ps t ts bs r' : AST)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI ts)
    (hstep : oneStep pMI (miMatch p t bs) = some r') :
    eval pMI 2 (miMatchList (MICons p ps) (MICons t ts) bs) =
      miMatchListK ps ts r' := by
  simp only [eval, os_miMatchList_cons_ok,
    os_miMatchListK_active_step ps ts (miMatch p t bs) r' hps hts
      (MatchActiveShape.match p t bs) hstep]

theorem miMatchList_cons_head_ok_step_eval (p ps t ts bs bs2 : AST)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI ts)
    (hstep : oneStep pMI (miMatch p t bs) = some (MIMatchOk bs2)) :
    eval pMI 3 (miMatchList (MICons p ps) (MICons t ts) bs) =
      miMatchList ps ts bs2 := by
  simp only [eval, os_miMatchList_cons_ok,
    os_miMatchListK_active_step ps ts (miMatch p t bs) (MIMatchOk bs2)
      hps hts (MatchActiveShape.match p t bs) hstep,
    os_miMatchListK_ok]

theorem miMatchList_cons_head_fail_step_eval (p ps t ts bs : AST)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI ts)
    (hstep : oneStep pMI (miMatch p t bs) = some MIMatchFail) :
    eval pMI 3 (miMatchList (MICons p ps) (MICons t ts) bs) = MIMatchFail := by
  simp only [eval, os_miMatchList_cons_ok,
    os_miMatchListK_active_step ps ts (miMatch p t bs) MIMatchFail
      hps hts (MatchActiveShape.match p t bs) hstep,
    os_miMatchListK_fail]

theorem cong_eval_match_active_mi (F : AST → AST)
    (hcong : ∀ s s', MatchActiveShape s →
      oneStep pMI s = some s' → oneStep pMI (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pMI N s = v → IsNormal pMI v →
      (∀ k, k < N → MatchActiveShape (eval pMI k s)) →
      ∃ M, eval pMI M (F s) = F v := by
  intro N
  induction N with
  | zero =>
      intro s v hs _ _
      simp only [eval] at hs
      subst hs
      exact ⟨0, rfl⟩
  | succ n ih =>
      intro s v hs hv hactive
      simp only [eval] at hs
      cases hstep : oneStep pMI s with
      | none =>
          rw [hstep] at hs
          subst hs
          exact ⟨0, rfl⟩
      | some s' =>
          rw [hstep] at hs
          have hsActive : MatchActiveShape s := by
            have h0 := hactive 0 (Nat.zero_lt_succ n)
            simpa only [eval] using h0
          have hactive' : ∀ k, k < n → MatchActiveShape (eval pMI k s') := by
            intro k hk
            have hk' : Nat.succ k < Nat.succ n := Nat.succ_lt_succ hk
            have hnext := hactive (Nat.succ k) hk'
            have heval : eval pMI (Nat.succ k) s = eval pMI k s' := by
              simp only [eval, hstep]
            simpa only [heval] using hnext
          obtain ⟨M, hM⟩ := ih hs hv hactive'
          refine ⟨M + 1, ?_⟩
          simp only [eval, hcong s s' hsActive hstep]
          exact hM

theorem cong_eval_match_active_with_guard_mi (F : AST → AST)
    (hwrap : ∀ s, MatchActiveShape s → MatchActiveShape (F s))
    (hcong : ∀ s s', MatchActiveShape s →
      oneStep pMI s = some s' → oneStep pMI (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pMI N s = v →
      (∀ k, k < N → MatchActiveShape (eval pMI k s)) →
        ∃ M, eval pMI M (F s) = F v ∧
          ∀ k, k < M → MatchActiveShape (eval pMI k (F s)) := by
  intro N
  induction N with
  | zero =>
      intro s v hs _
      simp only [eval] at hs
      subst hs
      exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
  | succ n ih =>
      intro s v hs hactive
      simp only [eval] at hs
      cases hstep : oneStep pMI s with
      | none =>
          rw [hstep] at hs
          subst hs
          exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
      | some s' =>
          rw [hstep] at hs
          have hsActive : MatchActiveShape s := by
            have h0 := hactive 0 (Nat.zero_lt_succ n)
            simpa only [eval] using h0
          have hactive' : ∀ k, k < n → MatchActiveShape (eval pMI k s') := by
            intro k hk
            have hk' : Nat.succ k < Nat.succ n := Nat.succ_lt_succ hk
            have hnext := hactive (Nat.succ k) hk'
            have heval : eval pMI (Nat.succ k) s = eval pMI k s' := by
              simp only [eval, hstep]
            simpa only [heval] using hnext
          obtain ⟨M, hM, hMactive⟩ := ih hs hactive'
          refine ⟨M + 1, ?_, ?_⟩
          · simp only [eval, hcong s s' hsActive hstep]
            exact hM
          · intro k hk
            cases k with
            | zero =>
                simpa only [eval] using hwrap s hsActive
            | succ k =>
                have hkM : k < M := by
                  exact Nat.succ_lt_succ_iff.mp (by
                    simpa [Nat.succ_eq_add_one] using hk)
                have htotal :
                    eval pMI (Nat.succ k) (F s) = eval pMI k (F s') := by
                  simp only [eval, hcong s s' hsActive hstep]
                rw [htotal]
                exact hMactive k hkM

theorem cong_eval_to_match_active_with_guard_mi (F : AST → AST)
    (hwrap : ∀ s, MatchActiveShape (F s))
    (hcong : ∀ s s', oneStep pMI s = some s' →
      oneStep pMI (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pMI N s = v → IsNormal pMI v →
      ∃ M, eval pMI M (F s) = F v ∧
        ∀ k, k < M → MatchActiveShape (eval pMI k (F s)) := by
  intro N
  induction N with
  | zero =>
      intro s v hs _
      simp only [eval] at hs
      subst hs
      exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
  | succ n ih =>
      intro s v hs hv
      simp only [eval] at hs
      cases hstep : oneStep pMI s with
      | none =>
          rw [hstep] at hs
          subst hs
          exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
      | some s' =>
          rw [hstep] at hs
          obtain ⟨M, hM, hMactive⟩ := ih hs hv
          refine ⟨M + 1, ?_, ?_⟩
          · simp only [eval, hcong s s' hstep]
            exact hM
          · intro k hk
            cases k with
            | zero =>
                simpa only [eval] using hwrap s
            | succ k =>
                have hkM : k < M := by
                  exact Nat.succ_lt_succ_iff.mp (by
                    simpa [Nat.succ_eq_add_one] using hk)
                have htotal :
                    eval pMI (Nat.succ k) (F s) = eval pMI k (F s') := by
                  simp only [eval, hcong s s' hstep]
                rw [htotal]
                exact hMactive k hkM

theorem miMatchListK_tail_active_eval_of (ps ts ts' r : AST)
    (tailFuel : Nat)
    (hps : IsNormal pMI ps)
    (hactive : MatchActiveShape r)
    (htail : eval pMI tailFuel ts = ts')
    (hts' : IsNormal pMI ts') :
    ∃ N,
      eval pMI N (miMatchListK ps ts r) =
        miMatchListK ps ts' r ∧
      ∀ k, k < N →
        MatchActiveShape (eval pMI k (miMatchListK ps ts r)) := by
  let F : AST → AST := fun z => miMatchListK ps z r
  exact cong_eval_to_match_active_with_guard_mi F
    (fun z => MatchActiveShape.matchListK ps z r)
    (fun s s' hstep =>
      os_miMatchListK_tail_active_step ps s s' r hps hactive hstep)
    tailFuel htail hts'

theorem miMatchList_cons_eval_of_match_ok (p ps t ts bs bs2 out : AST)
    (headFuel tailFuel : Nat)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI ts)
    (hbs2 : IsNormal pMI bs2)
    (hhead : eval pMI headFuel (miMatch p t bs) = MIMatchOk bs2)
    (hheadActive : ∀ k, k < headFuel →
      MatchActiveShape (eval pMI k (miMatch p t bs)))
    (htail : eval pMI tailFuel (miMatchList ps ts bs2) = out) :
    ∃ N, eval pMI N (miMatchList (MICons p ps) (MICons t ts) bs) = out := by
  let F : AST → AST := fun z => miMatchListK ps ts z
  have hdispatch :
      eval pMI 1 (miMatchList (MICons p ps) (MICons t ts) bs) =
        F (miMatch p t bs) := by
    simp only [F, eval, os_miMatchList_cons_ok]
  obtain ⟨Mhead, hheadCtx⟩ :=
    cong_eval_match_active_mi F
      (fun s s' hactive hstep =>
        os_miMatchListK_active_step ps ts s s' hps hts hactive hstep)
      headFuel hhead (normal_MIMatchOk bs2 hbs2) hheadActive
  have hpre := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI 1 Mhead
    (miMatchList (MICons p ps) (MICons t ts) bs)
    (F (miMatch p t bs))
    (F (MIMatchOk bs2))
    hdispatch hheadCtx
  have hok : eval pMI 1 (F (MIMatchOk bs2)) = miMatchList ps ts bs2 := by
    simp only [F, eval, os_miMatchListK_ok]
  have hpre2 := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI (1 + Mhead) 1
    (miMatchList (MICons p ps) (MICons t ts) bs)
    (F (MIMatchOk bs2))
    (miMatchList ps ts bs2)
    hpre hok
  have htotal := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI ((1 + Mhead) + 1) tailFuel
    (miMatchList (MICons p ps) (MICons t ts) bs)
    (miMatchList ps ts bs2)
    out
    hpre2 htail
  exact ⟨((1 + Mhead) + 1) + tailFuel, htotal⟩

theorem miMatchList_cons_first_result_of_match_ok (p ps t ts bs bs2 out : AST)
    (headFuel tailFuel : Nat)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI ts)
    (hhead : eval pMI headFuel (miMatch p t bs) = MIMatchOk bs2)
    (hheadActive : ∀ k, k < headFuel →
      MatchActiveShape (eval pMI k (miMatch p t bs)))
    (htail : eval pMI tailFuel (miMatchList ps ts bs2) = out)
    (htailActive : ∀ k, k < tailFuel →
      MatchActiveShape (eval pMI k (miMatchList ps ts bs2)))
    (hout : IsNormal pMI out) :
    ∃ N,
      eval pMI N (miMatchList (MICons p ps) (MICons t ts) bs) = out ∧
      (∀ k, k < N →
        MatchActiveShape
          (eval pMI k (miMatchList (MICons p ps) (MICons t ts) bs))) ∧
      IsNormal pMI out := by
  let F : AST → AST := fun z => miMatchListK ps ts z
  have hdispatch :
      eval pMI 1 (miMatchList (MICons p ps) (MICons t ts) bs) =
        F (miMatch p t bs) := by
    simp only [F, eval, os_miMatchList_cons_ok]
  obtain ⟨Mhead, hheadCtx, hheadCtxActive⟩ :=
    cong_eval_match_active_with_guard_mi F
      (fun s hs => MatchActiveShape.matchListK ps ts s)
      (fun s s' hactive hstep =>
        os_miMatchListK_active_step ps ts s s' hps hts hactive hstep)
      headFuel hhead hheadActive
  have hpre := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI 1 Mhead
    (miMatchList (MICons p ps) (MICons t ts) bs)
    (F (miMatch p t bs))
    (F (MIMatchOk bs2))
    hdispatch hheadCtx
  have hok : eval pMI 1 (F (MIMatchOk bs2)) = miMatchList ps ts bs2 := by
    simp only [F, eval, os_miMatchListK_ok]
  have hpre2 := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI (1 + Mhead) 1
    (miMatchList (MICons p ps) (MICons t ts) bs)
    (F (MIMatchOk bs2))
    (miMatchList ps ts bs2)
    hpre hok
  have htotal := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI ((1 + Mhead) + 1) tailFuel
    (miMatchList (MICons p ps) (MICons t ts) bs)
    (miMatchList ps ts bs2)
    out
    hpre2 htail
  refine ⟨((1 + Mhead) + 1) + tailFuel, htotal, ?_, hout⟩
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp only [eval]
    exact MatchActiveShape.matchList (MICons p ps) (MICons t ts) bs
  · by_cases hkCtx : k < 1 + Mhead
    · let j := k - 1
      have hj : j < Mhead := by omega
      have hk_eq : k = 1 + j := by omega
      have hshift :
          eval pMI k (miMatchList (MICons p ps) (MICons t ts) bs) =
            eval pMI j (F (miMatch p t bs)) := by
        have hraw := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI 1 j
          (miMatchList (MICons p ps) (MICons t ts) bs)
          (F (miMatch p t bs))
          (eval pMI j (F (miMatch p t bs)))
          hdispatch rfl
        simpa [hk_eq] using hraw
      rw [hshift]
      exact hheadCtxActive j hj
    · by_cases hkOk : k = 1 + Mhead
      · subst k
        rw [hpre]
        exact MatchActiveShape.matchListK ps ts (MIMatchOk bs2)
      · let j := k - ((1 + Mhead) + 1)
        have hj : j < tailFuel := by omega
        have hk_eq : k = ((1 + Mhead) + 1) + j := by omega
        have hshift :
            eval pMI k (miMatchList (MICons p ps) (MICons t ts) bs) =
              eval pMI j (miMatchList ps ts bs2) := by
          have hraw := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI
            ((1 + Mhead) + 1) j
            (miMatchList (MICons p ps) (MICons t ts) bs)
            (miMatchList ps ts bs2)
            (eval pMI j (miMatchList ps ts bs2))
            hpre2 rfl
          simpa [hk_eq] using hraw
        rw [hshift]
        exact htailActive j hj

theorem miMatchList_cons_active_result_of_match_ok (p ps t ts bs bs2 out : AST)
    (headFuel tailFuel : Nat)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI ts)
    (hhead : eval pMI headFuel (miMatch p t bs) = MIMatchOk bs2)
    (hheadActive : ∀ k, k < headFuel →
      MatchActiveShape (eval pMI k (miMatch p t bs)))
    (htail : eval pMI tailFuel (miMatchList ps ts bs2) = out)
    (htailActive : ∀ k, k < tailFuel →
      MatchActiveShape (eval pMI k (miMatchList ps ts bs2))) :
    ∃ N,
      eval pMI N (miMatchList (MICons p ps) (MICons t ts) bs) = out ∧
      (∀ k, k < N →
        MatchActiveShape
          (eval pMI k (miMatchList (MICons p ps) (MICons t ts) bs))) := by
  let F : AST → AST := fun z => miMatchListK ps ts z
  have hdispatch :
      eval pMI 1 (miMatchList (MICons p ps) (MICons t ts) bs) =
        F (miMatch p t bs) := by
    simp only [F, eval, os_miMatchList_cons_ok]
  obtain ⟨Mhead, hheadCtx, hheadCtxActive⟩ :=
    cong_eval_match_active_with_guard_mi F
      (fun s hs => MatchActiveShape.matchListK ps ts s)
      (fun s s' hactive hstep =>
        os_miMatchListK_active_step ps ts s s' hps hts hactive hstep)
      headFuel hhead hheadActive
  have hpre := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI 1 Mhead
    (miMatchList (MICons p ps) (MICons t ts) bs)
    (F (miMatch p t bs))
    (F (MIMatchOk bs2))
    hdispatch hheadCtx
  have hok : eval pMI 1 (F (MIMatchOk bs2)) = miMatchList ps ts bs2 := by
    simp only [F, eval, os_miMatchListK_ok]
  have hpre2 := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI (1 + Mhead) 1
    (miMatchList (MICons p ps) (MICons t ts) bs)
    (F (MIMatchOk bs2))
    (miMatchList ps ts bs2)
    hpre hok
  have htotal := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI ((1 + Mhead) + 1) tailFuel
    (miMatchList (MICons p ps) (MICons t ts) bs)
    (miMatchList ps ts bs2)
    out
    hpre2 htail
  refine ⟨((1 + Mhead) + 1) + tailFuel, htotal, ?_⟩
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp only [eval]
    exact MatchActiveShape.matchList (MICons p ps) (MICons t ts) bs
  · by_cases hkCtx : k < 1 + Mhead
    · let j := k - 1
      have hj : j < Mhead := by omega
      have hk_eq : k = 1 + j := by omega
      have hshift :
          eval pMI k (miMatchList (MICons p ps) (MICons t ts) bs) =
            eval pMI j (F (miMatch p t bs)) := by
        have hraw := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI 1 j
          (miMatchList (MICons p ps) (MICons t ts) bs)
          (F (miMatch p t bs))
          (eval pMI j (F (miMatch p t bs)))
          hdispatch rfl
        simpa [hk_eq] using hraw
      rw [hshift]
      exact hheadCtxActive j hj
    · by_cases hkOk : k = 1 + Mhead
      · subst k
        rw [hpre]
        exact MatchActiveShape.matchListK ps ts (MIMatchOk bs2)
      · let j := k - ((1 + Mhead) + 1)
        have hj : j < tailFuel := by omega
        have hk_eq : k = ((1 + Mhead) + 1) + j := by omega
        have hshift :
            eval pMI k (miMatchList (MICons p ps) (MICons t ts) bs) =
              eval pMI j (miMatchList ps ts bs2) := by
          have hraw := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI
            ((1 + Mhead) + 1) j
            (miMatchList (MICons p ps) (MICons t ts) bs)
            (miMatchList ps ts bs2)
            (eval pMI j (miMatchList ps ts bs2))
            hpre2 rfl
          simpa [hk_eq] using hraw
        rw [hshift]
        exact htailActive j hj

theorem miMatchList_cons_eval_of_match_fail (p ps t ts bs : AST)
    (headFuel : Nat)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI ts)
    (hhead : eval pMI headFuel (miMatch p t bs) = MIMatchFail)
    (hheadActive : ∀ k, k < headFuel →
      MatchActiveShape (eval pMI k (miMatch p t bs))) :
    ∃ N, eval pMI N (miMatchList (MICons p ps) (MICons t ts) bs) =
      MIMatchFail := by
  let F : AST → AST := fun z => miMatchListK ps ts z
  have hdispatch :
      eval pMI 1 (miMatchList (MICons p ps) (MICons t ts) bs) =
        F (miMatch p t bs) := by
    simp only [F, eval, os_miMatchList_cons_ok]
  obtain ⟨Mhead, hheadCtx⟩ :=
    cong_eval_match_active_mi F
      (fun s s' hactive hstep =>
        os_miMatchListK_active_step ps ts s s' hps hts hactive hstep)
      headFuel hhead normal_MIMatchFail hheadActive
  have hpre := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI 1 Mhead
    (miMatchList (MICons p ps) (MICons t ts) bs)
    (F (miMatch p t bs))
    (F MIMatchFail)
    hdispatch hheadCtx
  have hfail : eval pMI 1 (F MIMatchFail) = MIMatchFail := by
    simp only [F, eval, os_miMatchListK_fail]
  have htotal := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI (1 + Mhead) 1
    (miMatchList (MICons p ps) (MICons t ts) bs)
    (F MIMatchFail)
    MIMatchFail
    hpre hfail
  exact ⟨(1 + Mhead) + 1, htotal⟩

theorem miMatchList_cons_first_result_of_match_fail (p ps t ts bs : AST)
    (headFuel : Nat)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI ts)
    (hhead : eval pMI headFuel (miMatch p t bs) = MIMatchFail)
    (hheadActive : ∀ k, k < headFuel →
      MatchActiveShape (eval pMI k (miMatch p t bs))) :
    ∃ N,
      eval pMI N (miMatchList (MICons p ps) (MICons t ts) bs) =
        MIMatchFail ∧
      (∀ k, k < N →
        MatchActiveShape
          (eval pMI k (miMatchList (MICons p ps) (MICons t ts) bs))) ∧
      IsNormal pMI MIMatchFail := by
  let F : AST → AST := fun z => miMatchListK ps ts z
  have hdispatch :
      eval pMI 1 (miMatchList (MICons p ps) (MICons t ts) bs) =
        F (miMatch p t bs) := by
    simp only [F, eval, os_miMatchList_cons_ok]
  obtain ⟨Mhead, hheadCtx, hheadCtxActive⟩ :=
    cong_eval_match_active_with_guard_mi F
      (fun s hs => MatchActiveShape.matchListK ps ts s)
      (fun s s' hactive hstep =>
        os_miMatchListK_active_step ps ts s s' hps hts hactive hstep)
      headFuel hhead hheadActive
  have hpre := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI 1 Mhead
    (miMatchList (MICons p ps) (MICons t ts) bs)
    (F (miMatch p t bs))
    (F MIMatchFail)
    hdispatch hheadCtx
  have hfail : eval pMI 1 (F MIMatchFail) = MIMatchFail := by
    simp only [F, eval, os_miMatchListK_fail]
  have htotal := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI (1 + Mhead) 1
    (miMatchList (MICons p ps) (MICons t ts) bs)
    (F MIMatchFail)
    MIMatchFail
    hpre hfail
  refine ⟨(1 + Mhead) + 1, htotal, ?_, normal_MIMatchFail⟩
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp only [eval]
    exact MatchActiveShape.matchList (MICons p ps) (MICons t ts) bs
  · by_cases hkCtx : k < 1 + Mhead
    · let j := k - 1
      have hj : j < Mhead := by omega
      have hk_eq : k = 1 + j := by omega
      have hshift :
          eval pMI k (miMatchList (MICons p ps) (MICons t ts) bs) =
            eval pMI j (F (miMatch p t bs)) := by
        have hraw := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI 1 j
          (miMatchList (MICons p ps) (MICons t ts) bs)
          (F (miMatch p t bs))
          (eval pMI j (F (miMatch p t bs)))
          hdispatch rfl
        simpa [hk_eq] using hraw
      rw [hshift]
      exact hheadCtxActive j hj
    · have hkFail : k = 1 + Mhead := by omega
      subst k
      rw [hpre]
      exact MatchActiveShape.matchListK ps ts MIMatchFail

theorem miMatch_active_guard_one (pat term bs : AST) :
    ∀ k, k < 1 → MatchActiveShape (eval pMI k (miMatch pat term bs)) := by
  intro k hk
  have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
  subst k
  simp only [eval]
  exact MatchActiveShape.match pat term bs

theorem miMatchList_active_guard_one (ps ts bs : AST) :
    ∀ k, k < 1 → MatchActiveShape (eval pMI k (miMatchList ps ts bs)) := by
  intro k hk
  have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
  subst k
  simp only [eval]
  exact MatchActiveShape.matchList ps ts bs

theorem miMatchList_nil_source_some_first_result
    (terms : List AST) (encodedTerms encodedBs encodedOut : AST)
    (bs bsOut : List (String × AST))
    (hterms : encASTList? terms = some encodedTerms)
    (hbs : encBinds? bs = some encodedBs)
    (hmatch : AST.matchPatList [] terms bs = some bsOut)
    (hout : encBinds? bsOut = some encodedOut) :
    ∃ N,
      eval pMI N (miMatchList MINil encodedTerms encodedBs) =
        MIMatchOk encodedOut ∧
      (∀ k, k < N →
        MatchActiveShape (eval pMI k (miMatchList MINil encodedTerms encodedBs))) ∧
      IsNormal pMI (MIMatchOk encodedOut) := by
  cases terms with
  | nil =>
      simp only [encASTList?] at hterms
      cases hterms
      simp only [AST.matchPatList] at hmatch
      cases hmatch
      rw [hbs] at hout
      cases hout
      exact ⟨1, miMatchList_nil_nil_sim encodedBs,
        miMatchList_active_guard_one MINil MINil encodedBs,
        normal_MIMatchOk encodedBs (encBinds?_some_normal bs encodedBs hbs)⟩
  | cons _ _ =>
      simp only [AST.matchPatList] at hmatch
      cases hmatch

theorem miMatchList_nil_source_none_first_result
    (terms : List AST) (encodedTerms encodedBs : AST)
    (bs : List (String × AST))
    (hterms : encASTList? terms = some encodedTerms)
    (_hbs : encBinds? bs = some encodedBs)
    (hmatch : AST.matchPatList [] terms bs = none) :
    ∃ N,
      eval pMI N (miMatchList MINil encodedTerms encodedBs) =
        MIMatchFail ∧
      (∀ k, k < N →
        MatchActiveShape (eval pMI k (miMatchList MINil encodedTerms encodedBs))) ∧
      IsNormal pMI MIMatchFail := by
  cases terms with
  | nil =>
      simp only [AST.matchPatList] at hmatch
      cases hmatch
  | cons t ts =>
      simp only [encASTList?] at hterms
      cases ht : encAST? t with
      | none =>
          simp [ht] at hterms
      | some encodedT =>
          cases hts : encASTList? ts with
          | none =>
              simp [ht, hts] at hterms
          | some encodedTs =>
              simp [ht, hts] at hterms
              cases hterms
              exact ⟨1, miMatchList_nil_cons_fail_sim encodedT encodedTs encodedBs,
                miMatchList_active_guard_one MINil (MICons encodedT encodedTs)
                  encodedBs,
                normal_MIMatchFail⟩

theorem miMatchList_cons_source_nil_first_result
    (pats : List AST) (encodedPats encodedBs : AST)
    (bs : List (String × AST))
    (hpats : encASTList? pats = some encodedPats)
    (_hbs : encBinds? bs = some encodedBs)
    (hmatch : AST.matchPatList pats [] bs = none) :
    ∃ N,
      eval pMI N (miMatchList encodedPats MINil encodedBs) =
        MIMatchFail ∧
      (∀ k, k < N →
        MatchActiveShape (eval pMI k (miMatchList encodedPats MINil encodedBs))) ∧
      IsNormal pMI MIMatchFail := by
  cases pats with
  | nil =>
      simp only [AST.matchPatList] at hmatch
      cases hmatch
  | cons p ps =>
      simp only [encASTList?] at hpats
      cases hp : encAST? p with
      | none =>
          simp [hp] at hpats
      | some encodedP =>
          cases hps : encASTList? ps with
          | none =>
              simp [hp, hps] at hpats
          | some encodedPs =>
              simp [hp, hps] at hpats
              cases hpats
              exact ⟨1, miMatchList_cons_nil_fail_sim encodedP encodedPs encodedBs,
                miMatchList_active_guard_one (MICons encodedP encodedPs) MINil
                  encodedBs,
                normal_MIMatchFail⟩

def miMatchVarResult (v : String) (term wholeBs : AST)
    (bs : List (String × AST)) : AST :=
  match lookupEncoded? v bs with
  | some old => if (term == old) = true then MIMatchOk wholeBs else MIMatchFail
  | none => MIMatchOk (MIBCons (con0 v) term wholeBs)

theorem miMatchVarResult_of_matchPat_var_some (v : String)
    (term encodedTerm encodedBs encodedOut : AST)
    (bs bsOut : List (String × AST))
    (hterm : encAST? term = some encodedTerm)
    (hbs : encBinds? bs = some encodedBs)
    (hmatch : AST.matchPat (.var (.base v)) term bs = some bsOut)
    (hout : encBinds? bsOut = some encodedOut) :
    miMatchVarResult v encodedTerm encodedBs bs = MIMatchOk encodedOut := by
  simp only [miMatchVarResult]
  rw [lookupEncoded?_eq_find?_encAST? v bs]
  cases hfind : List.find? (fun b : String × AST => b.fst == v) bs with
  | none =>
      simp only [AST.matchPat, hfind] at hmatch
      cases hmatch
      simp only [encBinds?, hterm, hbs] at hout
      cases hout
      rfl
  | some pair =>
      rcases pair with ⟨_, old⟩
      simp only [AST.matchPat, hfind] at hmatch
      by_cases holdTerm : (old == term) = true
      · simp only [holdTerm, if_true] at hmatch
        cases hmatch
        rw [hbs] at hout
        cases hout
        have hencOld : encAST? old = some encodedTerm := by
          have holdEq := ast_beq_true_eq_mi old term holdTerm
          subst term
          exact hterm
        simp only [hencOld, beq_ast_self encodedTerm, if_true]
      · have holdTermFalse : (old == term) = false := by
          cases hcmp : (old == term) <;> simp [hcmp] at holdTerm ⊢
        simp only [holdTermFalse, Bool.false_eq_true, if_false] at hmatch
        cases hmatch

theorem miMatchVarResult_of_matchPat_var_none (v : String)
    (term encodedTerm encodedBs : AST)
    (bs : List (String × AST))
    (hterm : encAST? term = some encodedTerm)
    (hbs : encBinds? bs = some encodedBs)
    (hmatch : AST.matchPat (.var (.base v)) term bs = none) :
    miMatchVarResult v encodedTerm encodedBs bs = MIMatchFail := by
  simp only [miMatchVarResult]
  rw [lookupEncoded?_eq_find?_encAST? v bs]
  cases hfind : List.find? (fun b : String × AST => b.fst == v) bs with
  | none =>
      simp only [AST.matchPat, hfind] at hmatch
      cases hmatch
  | some pair =>
      rcases pair with ⟨w, old⟩
      simp only [AST.matchPat, hfind] at hmatch
      by_cases holdTerm : (old == term) = true
      · simp only [holdTerm, if_true] at hmatch
        cases hmatch
      · have holdTermFalse : (old == term) = false := by
          cases hcmp : (old == term) <;> simp [hcmp] at holdTerm ⊢
        obtain ⟨encodedOld, hencOld⟩ :=
          encAST?_some_of_find?_encBinds? v bs encodedBs w old hfind hbs
        have htermOldFalse : (term == old) = false :=
          ast_beq_false_symm_mi old term holdTermFalse
        have hencFalse : (encodedTerm == encodedOld) = false :=
          encAST?_beq_false_of_beq_false term old encodedTerm encodedOld
            hterm hencOld htermOldFalse
        simp only [hencOld, hencFalse, Bool.false_eq_true, if_false]

theorem normal_miMatchVarResult (v : String) (term wholeBs : AST)
    (hterm : IsNormal pMI term) (hwhole : IsNormal pMI wholeBs)
    (bs : List (String × AST)) :
    IsNormal pMI (miMatchVarResult v term wholeBs bs) := by
  cases hlookup : lookupEncoded? v bs with
  | none =>
      simp only [miMatchVarResult, hlookup]
      exact normal_MIMatchOk (MIBCons (con0 v) term wholeBs)
        (normal_MIBCons (con0 v) term wholeBs (normal_con0 v) hterm hwhole)
  | some old =>
      by_cases hsame : (term == old) = true
      · simp only [miMatchVarResult, hlookup, hsame, if_true]
        exact normal_MIMatchOk wholeBs hwhole
      · have hdiff : (term == old) = false := by
          cases hcmp : (term == old) <;> simp [hcmp] at hsame ⊢
        simp only [miMatchVarResult, hlookup, hdiff, Bool.false_eq_true, if_false]
        exact normal_MIMatchFail

theorem miMatchVarK_lookup_encBinds_first_result (v : String) (term wholeBs : AST)
    (hterm : IsNormal pMI term) (hwhole : IsNormal pMI wholeBs) :
    ∀ (bs : List (String × AST)) (encodedTail : AST),
      encBinds? bs = some encodedTail →
      ∃ N,
        eval pMI N
            (miMatchVarK (con0 v) term wholeBs (miLookup (con0 v) encodedTail)) =
          miMatchVarResult v term wholeBs bs ∧
        (∀ k, k < N →
          MatchActiveShape
            (eval pMI k
              (miMatchVarK (con0 v) term wholeBs
                (miLookup (con0 v) encodedTail)))) ∧
        IsNormal pMI (miMatchVarResult v term wholeBs bs)
  | [], encodedTail, henc => by
      simp only [encBinds?] at henc
      cases henc
      refine ⟨2, ?_, ?_, normal_miMatchVarResult v term wholeBs hterm hwhole []⟩
      · simp only [miMatchVarResult, lookupEncoded?, eval,
          os_miMatchVarK_lookup_nil_arg, os_miMatchVarK_none_general,
          hterm, hwhole]
      · intro k hk
        have hkcases : k = 0 ∨ k = 1 := by omega
        rcases hkcases with rfl | rfl
        · simp only [eval]
          exact MatchActiveShape.matchVarK (con0 v) term wholeBs
            (miLookup (con0 v) MIBNil)
        · simp only [eval, os_miMatchVarK_lookup_nil_arg, hterm, hwhole]
          exact MatchActiveShape.matchVarK (con0 v) term wholeBs MINone
  | (w, t) :: rest, encodedTail, henc => by
      simp only [encBinds?] at henc
      cases ht : encAST? t with
      | none =>
          simp [ht] at henc
      | some encodedTerm =>
          cases hrest : encBinds? rest with
          | none =>
              simp [ht, hrest] at henc
          | some encodedRest =>
              simp [ht, hrest] at henc
              cases henc
              by_cases hvw : (v == w) = true
              · have hvw_eq : v = w := beq_iff_eq.mp hvw
                subst w
                have hvv : (v == v) = true := string_beq_self_mi v
                refine ⟨2, ?_, ?_,
                  normal_miMatchVarResult v term wholeBs hterm hwhole
                    ((v, t) :: rest)⟩
                · simp only [miMatchVarResult, lookupEncoded?, hvv, ht, if_true, eval,
                    os_miMatchVarK_lookup_hit_arg, hterm, hwhole]
                  by_cases hsame : (term == encodedTerm) = true
                  · simp only [hsame, if_true, os_miMatchVarK_same_on_beq_named]
                  · have hdiff : (term == encodedTerm) = false := by
                      cases hcmp : (term == encodedTerm) <;> simp [hcmp] at hsame ⊢
                    simp only [hdiff, Bool.false_eq_true, if_false,
                      os_miMatchVarK_diff_general]
                · intro k hk
                  have hkcases : k = 0 ∨ k = 1 := by omega
                  rcases hkcases with rfl | rfl
                  · simp only [eval]
                    exact MatchActiveShape.matchVarK (con0 v) term wholeBs
                      (miLookup (con0 v) (MIBCons (con0 v) encodedTerm encodedRest))
                  · simp only [eval, os_miMatchVarK_lookup_hit_arg, hterm, hwhole]
                    exact MatchActiveShape.matchVarK (con0 v) term wholeBs
                      (MISome encodedTerm)
              · have hvw_false : (v == w) = false := by
                  cases hcmp : (v == w) <;> simp [hcmp] at hvw ⊢
                obtain ⟨Nrest, hrestEval, hrestActive, hrestNorm⟩ :=
                  miMatchVarK_lookup_encBinds_first_result v term wholeBs hterm hwhole
                    rest encodedRest hrest
                refine ⟨Nat.succ Nrest, ?_, ?_, ?_⟩
                · simp only [eval, os_miMatchVarK_lookup_miss_arg, hterm, hwhole,
                    hvw_false]
                  simpa only [miMatchVarResult, lookupEncoded?, hvw_false,
                    Bool.false_eq_true, if_false] using hrestEval
                · intro k hk
                  cases k with
                  | zero =>
                      simp only [eval]
                      exact MatchActiveShape.matchVarK (con0 v) term wholeBs
                        (miLookup (con0 v) (MIBCons (con0 w) encodedTerm encodedRest))
                  | succ j =>
                      have hj : j < Nrest := Nat.succ_lt_succ_iff.mp hk
                      have hactive := hrestActive j hj
                      simpa only [eval, os_miMatchVarK_lookup_miss_arg, hterm,
                        hwhole, hvw_false] using hactive
                · simpa only [miMatchVarResult, lookupEncoded?, hvw_false,
                    Bool.false_eq_true, if_false] using hrestNorm

theorem miMatch_var_encodedBinds_first_result (v : String) (term encodedBs : AST)
    (hterm : IsNormal pMI term) :
    ∀ (bs : List (String × AST)),
      encBinds? bs = some encodedBs →
      ∃ N,
        eval pMI N (miMatch (MIVar v) term encodedBs) =
          miMatchVarResult v term encodedBs bs ∧
        (∀ k, k < N →
          MatchActiveShape (eval pMI k (miMatch (MIVar v) term encodedBs))) ∧
        IsNormal pMI (miMatchVarResult v term encodedBs bs)
  | bs, henc => by
      have hbs : IsNormal pMI encodedBs := encBinds?_some_normal bs encodedBs henc
      obtain ⟨Ninner, hinnerEval, hinnerActive, hinnerNorm⟩ :=
        miMatchVarK_lookup_encBinds_first_result v term encodedBs hterm hbs
          bs encodedBs henc
      refine ⟨Nat.succ (Nat.succ Ninner), ?_, ?_, hinnerNorm⟩
      · simp only [eval, MIVar, os_miMatch_var_data, os_miMatchVar]
        exact hinnerEval
      · intro k hk
        cases k with
        | zero =>
            simp only [eval]
            exact MatchActiveShape.match (MIVar v) term encodedBs
        | succ k =>
            cases k with
            | zero =>
                simp only [eval, MIVar, os_miMatch_var_data]
                exact MatchActiveShape.matchVar (con0 v) term encodedBs
            | succ j =>
                have hj : j < Ninner := by omega
                have hactive := hinnerActive j hj
                simpa only [eval, MIVar, os_miMatch_var_data, os_miMatchVar]
                  using hactive

theorem miMatch_var_source_some_first_result (v : String)
    (term encodedTerm encodedBs encodedOut : AST)
    (bs bsOut : List (String × AST))
    (hterm : encAST? term = some encodedTerm)
    (hbs : encBinds? bs = some encodedBs)
    (hmatch : AST.matchPat (.var (.base v)) term bs = some bsOut)
    (hout : encBinds? bsOut = some encodedOut) :
    ∃ N,
      eval pMI N (miMatch (MIVar v) encodedTerm encodedBs) =
        MIMatchOk encodedOut ∧
      (∀ k, k < N →
        MatchActiveShape (eval pMI k (miMatch (MIVar v) encodedTerm encodedBs))) ∧
      IsNormal pMI (MIMatchOk encodedOut) := by
  obtain ⟨N, hEval, hActive, _⟩ :=
    miMatch_var_encodedBinds_first_result v encodedTerm encodedBs
      (encAST?_some_normal term encodedTerm hterm) bs hbs
  have hResult :=
    miMatchVarResult_of_matchPat_var_some v term encodedTerm encodedBs
      encodedOut bs bsOut hterm hbs hmatch hout
  refine ⟨N, ?_, hActive, normal_MIMatchOk encodedOut ?_⟩
  · simpa only [hResult] using hEval
  · exact encBinds?_some_normal bsOut encodedOut hout

theorem miMatch_var_source_none_first_result (v : String)
    (term encodedTerm encodedBs : AST)
    (bs : List (String × AST))
    (hterm : encAST? term = some encodedTerm)
    (hbs : encBinds? bs = some encodedBs)
    (hmatch : AST.matchPat (.var (.base v)) term bs = none) :
    ∃ N,
      eval pMI N (miMatch (MIVar v) encodedTerm encodedBs) =
        MIMatchFail ∧
      (∀ k, k < N →
        MatchActiveShape (eval pMI k (miMatch (MIVar v) encodedTerm encodedBs))) ∧
      IsNormal pMI MIMatchFail := by
  obtain ⟨N, hEval, hActive, _⟩ :=
    miMatch_var_encodedBinds_first_result v encodedTerm encodedBs
      (encAST?_some_normal term encodedTerm hterm) bs hbs
  have hResult :=
    miMatchVarResult_of_matchPat_var_none v term encodedTerm encodedBs
      bs hterm hbs hmatch
  exact ⟨N, by simpa only [hResult] using hEval, hActive, normal_MIMatchFail⟩

theorem miMatchList_cons_var_eval_of_tail (v : String)
    (ps ts term encodedBs bs2 out : AST) (bs : List (String × AST))
    (tailFuel : Nat)
    (henc : encBinds? bs = some encodedBs)
    (hterm : IsNormal pMI term) (hps : IsNormal pMI ps)
    (hts : IsNormal pMI ts) (hbs2 : IsNormal pMI bs2)
    (hresult : miMatchVarResult v term encodedBs bs = MIMatchOk bs2)
    (htail : eval pMI tailFuel (miMatchList ps ts bs2) = out) :
    ∃ N,
      eval pMI N (miMatchList (MICons (MIVar v) ps) (MICons term ts) encodedBs) =
        out := by
  obtain ⟨Nhead, hhead, hactive, _⟩ :=
    miMatch_var_encodedBinds_first_result v term encodedBs hterm bs henc
  have hheadOk :
      eval pMI Nhead (miMatch (MIVar v) term encodedBs) = MIMatchOk bs2 := by
    simpa only [hresult] using hhead
  exact miMatchList_cons_eval_of_match_ok (MIVar v) ps term ts encodedBs bs2 out
    Nhead tailFuel hps hts hbs2 hheadOk hactive htail

theorem miMatchList_cons_var_fail (v : String)
    (ps ts term encodedBs : AST) (bs : List (String × AST))
    (henc : encBinds? bs = some encodedBs)
    (hterm : IsNormal pMI term) (hps : IsNormal pMI ps)
    (hts : IsNormal pMI ts)
    (hresult : miMatchVarResult v term encodedBs bs = MIMatchFail) :
    ∃ N,
      eval pMI N (miMatchList (MICons (MIVar v) ps) (MICons term ts) encodedBs) =
        MIMatchFail := by
  obtain ⟨Nhead, hhead, hactive, _⟩ :=
    miMatch_var_encodedBinds_first_result v term encodedBs hterm bs henc
  have hheadFail :
      eval pMI Nhead (miMatch (MIVar v) term encodedBs) = MIMatchFail := by
    simpa only [hresult] using hhead
  exact miMatchList_cons_eval_of_match_fail (MIVar v) ps term ts encodedBs
    Nhead hps hts hheadFail hactive

theorem miMatchList_cons_var_source_some_eval_of_tail (v : String)
    (ps ts term encodedTerm encodedBs encodedOut out : AST)
    (bs bsOut : List (String × AST)) (tailFuel : Nat)
    (hterm : encAST? term = some encodedTerm)
    (hbs : encBinds? bs = some encodedBs)
    (hmatch : AST.matchPat (.var (.base v)) term bs = some bsOut)
    (hout : encBinds? bsOut = some encodedOut)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI ts)
    (htail : eval pMI tailFuel (miMatchList ps ts encodedOut) = out) :
    ∃ N,
      eval pMI N
          (miMatchList (MICons (MIVar v) ps) (MICons encodedTerm ts) encodedBs) =
        out := by
  have hresult :=
    miMatchVarResult_of_matchPat_var_some v term encodedTerm encodedBs
      encodedOut bs bsOut hterm hbs hmatch hout
  exact miMatchList_cons_var_eval_of_tail v ps ts encodedTerm encodedBs
    encodedOut out bs tailFuel hbs
    (encAST?_some_normal term encodedTerm hterm) hps hts
    (encBinds?_some_normal bsOut encodedOut hout) hresult htail

theorem miMatchList_cons_var_source_none_fail (v : String)
    (ps ts term encodedTerm encodedBs : AST)
    (bs : List (String × AST))
    (hterm : encAST? term = some encodedTerm)
    (hbs : encBinds? bs = some encodedBs)
    (hmatch : AST.matchPat (.var (.base v)) term bs = none)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI ts) :
    ∃ N,
      eval pMI N
          (miMatchList (MICons (MIVar v) ps) (MICons encodedTerm ts) encodedBs) =
        MIMatchFail := by
  have hresult :=
    miMatchVarResult_of_matchPat_var_none v term encodedTerm encodedBs
      bs hterm hbs hmatch
  exact miMatchList_cons_var_fail v ps ts encodedTerm encodedBs bs hbs
    (encAST?_some_normal term encodedTerm hterm) hps hts hresult

theorem apply_miMatch_sym_same_named (s : String) (bs : AST) :
    applyBaseRewrite
        (rw "match-sym-same" (miMatch (app "MISym" [vV]) (app "MISym" [vV]) vBs)
          (MIMatchOk vBs))
        (miMatch (MISym s) (MISym s) bs) = some (MIMatchOk bs) := by
  have e_match : (("mi-match" : String) == "mi-match") = true := by decide
  have e_misym : (("MISym" : String) == "MISym") = true := by decide
  have e_v_v : (("v" : String) == "v") = true := by decide
  have e_v_bs : (("v" : String) == "bs") = false := by decide
  have e_bs_bs : (("bs" : String) == "bs") = true := by decide
  have e_same : (con0 s == con0 s) = true := beq_con0_self s
  simp only [applyBaseRewrite, rw, miMatch, MISym, MIMatchOk, app, pv, vV, vBs,
    AST.matchPat, AST.matchPatList, AST.inst, AST.instList, List.find?,
    label_id_beq, e_match, e_misym, e_v_v, e_v_bs, e_bs_bs, e_same,
    Option.bind_some, Option.map_some, if_pos]

theorem apply_miMatch_app_same_named (h : String) (args args2 bs : AST) :
    applyBaseRewrite
        (rw "match-app-same"
          (miMatch (app "MIApp" [vH, vArgs]) (app "MIApp" [vH, vArgs2]) vBs)
          (miMatchList vArgs vArgs2 vBs))
        (miMatch (MIApp h args) (MIApp h args2) bs) =
      some (miMatchList args args2 bs) := by
  have e_match : (("mi-match" : String) == "mi-match") = true := by decide
  have e_miapp : (("MIApp" : String) == "MIApp") = true := by decide
  have e_h_h : (("h" : String) == "h") = true := by decide
  have e_h_args : (("h" : String) == "args") = false := by decide
  have e_args_h : (("args" : String) == "h") = false := by decide
  have e_args_args : (("args" : String) == "args") = true := by decide
  have e_args_args2 : (("args" : String) == "args2") = false := by decide
  have e_h_args2 : (("h" : String) == "args2") = false := by decide
  have e_args2_bs : (("args2" : String) == "bs") = false := by decide
  have e_args_bs : (("args" : String) == "bs") = false := by decide
  have e_h_bs : (("h" : String) == "bs") = false := by decide
  have e_bs_args : (("bs" : String) == "args") = false := by decide
  have e_args2_args : (("args2" : String) == "args") = false := by decide
  have e_bs_args2 : (("bs" : String) == "args2") = false := by decide
  have e_args2_args2 : (("args2" : String) == "args2") = true := by decide
  have e_bs_bs : (("bs" : String) == "bs") = true := by decide
  have e_same : (con0 h == con0 h) = true := beq_con0_self h
  simp only [applyBaseRewrite, rw, miMatch, MIApp, miMatchList, app, pv, vH,
    vArgs, vArgs2, vBs, AST.matchPat, AST.matchPatList, AST.inst,
    AST.instList, List.find?, label_id_beq, e_match, e_miapp, e_h_h,
    e_h_args, e_args_h, e_args_args, e_args_args2, e_h_args2, e_args2_bs,
    e_args_bs, e_h_bs, e_bs_args, e_args2_args, e_bs_args2, e_args2_args2,
    e_bs_bs, e_same, Option.bind_some, Option.map_some, if_pos]

theorem apply_miMatch_sym_same_on_distinct_named (s t : String) (bs : AST)
    (hst : (s == t) = false) :
    applyBaseRewrite
        (rw "match-sym-same" (miMatch (app "MISym" [vV]) (app "MISym" [vV]) vBs)
          (MIMatchOk vBs))
        (miMatch (MISym s) (MISym t) bs) = none := by
  have e_match : (("mi-match" : String) == "mi-match") = true := by decide
  have e_misym : (("MISym" : String) == "MISym") = true := by decide
  have e_v_v : (("v" : String) == "v") = true := by decide
  have e_v_bs : (("v" : String) == "bs") = false := by decide
  have e_diff : (con0 s == con0 t) = false := by
    rw [beq_con0, hst]
  simp only [applyBaseRewrite, rw, miMatch, MISym, MIMatchOk, app, pv, vV, vBs,
    AST.matchPat, AST.matchPatList, AST.inst, AST.instList, List.find?,
    label_id_beq, e_match, e_misym, e_v_v, e_diff,
    Option.bind_some, Bool.false_eq_true, if_true, if_false,
    Option.bind_none, Option.map_none]

theorem apply_miMatch_sym_fail_named (s : String) (term bs : AST) :
    applyBaseRewrite
        (rw "match-sym-fail" (miMatch (app "MISym" [vV]) vTerm vBs) MIMatchFail)
        (miMatch (MISym s) term bs) = some MIMatchFail := by
  have e_match : (("mi-match" : String) == "mi-match") = true := by decide
  have e_misym : (("MISym" : String) == "MISym") = true := by decide
  have e_v_term : (("v" : String) == "term") = false := by decide
  have e_v_bs : (("v" : String) == "bs") = false := by decide
  have e_term_bs : (("term" : String) == "bs") = false := by decide
  simp only [applyBaseRewrite, rw, miMatch, MISym, MIMatchFail, app, pv, vV,
    vTerm, vBs, AST.matchPat, AST.matchPatList, List.find?, label_id_beq,
    e_match, e_misym, e_v_term, e_v_bs, e_term_bs,
    Option.bind_some, Option.map_some, if_pos]
  rfl

theorem apply_miMatch_app_same_on_distinct_named (h k : String)
    (args args2 bs : AST) (hhk : (h == k) = false) :
    applyBaseRewrite
        (rw "match-app-same"
          (miMatch (app "MIApp" [vH, vArgs]) (app "MIApp" [vH, vArgs2]) vBs)
          (miMatchList vArgs vArgs2 vBs))
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
  have e_match : (("mi-match" : String) == "mi-match") = true := by decide
  have e_miapp : (("MIApp" : String) == "MIApp") = true := by decide
  have e_h_h : (("h" : String) == "h") = true := by decide
  have e_h_args : (("h" : String) == "args") = false := by decide
  have e_args_h : (("args" : String) == "h") = false := by decide
  have e_args_args : (("args" : String) == "args") = true := by decide
  have e_args_args2 : (("args" : String) == "args2") = false := by decide
  have e_h_args2 : (("h" : String) == "args2") = false := by decide
  have e_diff : (con0 h == con0 k) = false := by
    rw [beq_con0, hhk]
  simp only [applyBaseRewrite, rw, miMatch, MIApp, miMatchList, app, pv, vH,
    vArgs, vArgs2, vBs, AST.matchPat, AST.matchPatList, AST.inst,
    AST.instList, List.find?, label_id_beq, e_match, e_miapp, e_h_h,
    e_h_args, e_args_h, e_diff, Option.bind_some, Bool.false_eq_true,
    if_true, if_false, Option.bind_none, Option.map_none]

theorem apply_miMatch_app_fail_named (h : String) (args term bs : AST) :
    applyBaseRewrite
        (rw "match-app-fail" (miMatch (app "MIApp" [vH, vArgs]) vTerm vBs) MIMatchFail)
        (miMatch (MIApp h args) term bs) = some MIMatchFail := by
  have e_match : (("mi-match" : String) == "mi-match") = true := by decide
  have e_miapp : (("MIApp" : String) == "MIApp") = true := by decide
  have e_h_args : (("h" : String) == "args") = false := by decide
  have e_h_term : (("h" : String) == "term") = false := by decide
  have e_args_term : (("args" : String) == "term") = false := by decide
  have e_h_bs : (("h" : String) == "bs") = false := by decide
  have e_args_bs : (("args" : String) == "bs") = false := by decide
  have e_term_bs : (("term" : String) == "bs") = false := by decide
  simp only [applyBaseRewrite, rw, miMatch, MIApp, MIMatchFail, app, pv, vH,
    vArgs, vTerm, vBs, AST.matchPat, AST.matchPatList, List.find?,
    label_id_beq, e_match, e_miapp, e_h_args, e_h_term, e_args_term, e_h_bs,
    e_args_bs, e_term_bs, Option.bind_some, Option.map_some, if_pos]
  rfl

theorem miRules_match_sym_same_prefix :
    miRules =
      rw "lookup-nil" (miLookup vV MIBNil) MINone ::
      rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT) ::
      rw "lookup-miss" (miLookup vV (MIBCons vW vT vRest)) (miLookup vV vRest) ::
      rw "match-var" (miMatchVar vV vTerm vBs) (miMatchVarK vV vTerm vBs (miLookup vV vBs)) ::
      rw "match-var-none" (miMatchVarK vV vTerm vBs MINone)
        (MIMatchOk (MIBCons vV vTerm vBs)) ::
      rw "match-var-same" (miMatchVarK vV vTerm vBs (MISome vTerm))
        (MIMatchOk vBs) ::
      rw "match-var-diff" (miMatchVarK vV vTerm vBs (MISome vOld)) MIMatchFail ::
      rw "match-list-nil-ok" (miMatchList MINil MINil vBs) (MIMatchOk vBs) ::
      rw "match-list-nil-fail" (miMatchList MINil vTs vBs) MIMatchFail ::
      rw "match-list-cons" (miMatchList (MICons vP vPs) (MICons vT vTs) vBs)
        (miMatchListK vPs vTs (miMatch vP vT vBs)) ::
      rw "match-list-cons-fail" (miMatchList (MICons vP vPs) vTs vBs) MIMatchFail ::
      rw "match-listK-ok" (miMatchListK vPs vTs (MIMatchOk vBs2))
        (miMatchList vPs vTs vBs2) ::
      rw "match-listK-fail" (miMatchListK vPs vTs MIMatchFail) MIMatchFail ::
      rw "match-var-pattern" (miMatch (app "MIVar" [vV]) vTerm vBs)
        (miMatchVar vV vTerm vBs) ::
      rw "match-sym-same" (miMatch (app "MISym" [vV]) (app "MISym" [vV]) vBs)
        (MIMatchOk vBs) ::
      List.drop 15 miRules := by
  rfl

theorem baseReducts_miMatch_sym_same_named_head (s : String) (bs : AST) :
    ∃ tail,
      baseReducts pMI (miMatch (MISym s) (MISym s) bs) =
        MIMatchOk bs :: tail := by
  let target := miMatch (MISym s) (MISym s) bs
  refine ⟨(List.drop 15 miRules).filterMap (fun rd => applyBaseRewrite rd target), ?_⟩
  change miRules.filterMap (fun rd => applyBaseRewrite rd target) =
    MIMatchOk bs :: (List.drop 15 miRules).filterMap (fun rd => applyBaseRewrite rd target)
  rw [miRules_match_sym_same_prefix]
  dsimp only [target]
  have h_lookup_nil :
      applyBaseRewrite (rw "lookup-nil" (miLookup vV MIBNil) MINone)
        (miMatch (MISym s) (MISym s) bs) = none := by
    rfl
  have h_lookup_hit :
      applyBaseRewrite (rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT))
        (miMatch (MISym s) (MISym s) bs) = none := by
    rfl
  have h_lookup_miss :
      applyBaseRewrite
        (rw "lookup-miss" (miLookup vV (MIBCons vW vT vRest)) (miLookup vV vRest))
        (miMatch (MISym s) (MISym s) bs) = none := by
    rfl
  have h_match_var :
      applyBaseRewrite
        (rw "match-var" (miMatchVar vV vTerm vBs)
          (miMatchVarK vV vTerm vBs (miLookup vV vBs)))
        (miMatch (MISym s) (MISym s) bs) = none := by
    rfl
  have h_match_var_none :
      applyBaseRewrite
        (rw "match-var-none" (miMatchVarK vV vTerm vBs MINone)
          (MIMatchOk (MIBCons vV vTerm vBs)))
        (miMatch (MISym s) (MISym s) bs) = none := by
    rfl
  have h_match_var_same :
      applyBaseRewrite
        (rw "match-var-same" (miMatchVarK vV vTerm vBs (MISome vTerm))
          (MIMatchOk vBs))
        (miMatch (MISym s) (MISym s) bs) = none := by
    rfl
  have h_match_var_diff :
      applyBaseRewrite
        (rw "match-var-diff" (miMatchVarK vV vTerm vBs (MISome vOld)) MIMatchFail)
        (miMatch (MISym s) (MISym s) bs) = none := by
    rfl
  have h_list_nil_ok :
      applyBaseRewrite (rw "match-list-nil-ok" (miMatchList MINil MINil vBs) (MIMatchOk vBs))
        (miMatch (MISym s) (MISym s) bs) = none := by
    rfl
  have h_list_nil_fail :
      applyBaseRewrite (rw "match-list-nil-fail" (miMatchList MINil vTs vBs) MIMatchFail)
        (miMatch (MISym s) (MISym s) bs) = none := by
    rfl
  have h_list_cons :
      applyBaseRewrite
        (rw "match-list-cons" (miMatchList (MICons vP vPs) (MICons vT vTs) vBs)
          (miMatchListK vPs vTs (miMatch vP vT vBs)))
        (miMatch (MISym s) (MISym s) bs) = none := by
    rfl
  have h_list_cons_fail :
      applyBaseRewrite (rw "match-list-cons-fail" (miMatchList (MICons vP vPs) vTs vBs) MIMatchFail)
        (miMatch (MISym s) (MISym s) bs) = none := by
    rfl
  have h_listK_ok :
      applyBaseRewrite
        (rw "match-listK-ok" (miMatchListK vPs vTs (MIMatchOk vBs2))
          (miMatchList vPs vTs vBs2))
        (miMatch (MISym s) (MISym s) bs) = none := by
    rfl
  have h_listK_fail :
      applyBaseRewrite (rw "match-listK-fail" (miMatchListK vPs vTs MIMatchFail) MIMatchFail)
        (miMatch (MISym s) (MISym s) bs) = none := by
    rfl
  have h_match_var_pattern :
      applyBaseRewrite
        (rw "match-var-pattern" (miMatch (app "MIVar" [vV]) vTerm vBs)
          (miMatchVar vV vTerm vBs))
        (miMatch (MISym s) (MISym s) bs) = none := by
    rfl
  simp only [List.filterMap_cons, h_lookup_nil, h_lookup_hit, h_lookup_miss,
    h_match_var, h_match_var_none, h_match_var_same, h_match_var_diff,
    h_list_nil_ok, h_list_nil_fail, h_list_cons, h_list_cons_fail,
    h_listK_ok, h_listK_fail, h_match_var_pattern,
    apply_miMatch_sym_same_named, List.drop]

theorem os_miMatch_sym_same_named (s : String) (bs : AST) :
    oneStep pMI (miMatch (MISym s) (MISym s) bs) =
      some (MIMatchOk bs) := by
  obtain ⟨tail, hhead⟩ := baseReducts_miMatch_sym_same_named_head s bs
  change (match baseReducts pMI (miMatch (MISym s) (MISym s) bs) with
    | r :: _ => some r
    | [] =>
      (oneStepList pMI [MISym s, MISym s, bs]).map
        (fun args' => AST.sexp (Label.id "mi-match") args')) =
      some (MIMatchOk bs)
  rw [hhead]

theorem miMatch_sym_same_named_sim (s : String) (bs : AST) :
    eval pMI 1 (miMatch (MISym s) (MISym s) bs) = MIMatchOk bs := by
  simp only [eval, os_miMatch_sym_same_named]

theorem miRules_match_app_same_prefix :
    miRules =
      rw "lookup-nil" (miLookup vV MIBNil) MINone ::
      rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT) ::
      rw "lookup-miss" (miLookup vV (MIBCons vW vT vRest)) (miLookup vV vRest) ::
      rw "match-var" (miMatchVar vV vTerm vBs) (miMatchVarK vV vTerm vBs (miLookup vV vBs)) ::
      rw "match-var-none" (miMatchVarK vV vTerm vBs MINone)
        (MIMatchOk (MIBCons vV vTerm vBs)) ::
      rw "match-var-same" (miMatchVarK vV vTerm vBs (MISome vTerm))
        (MIMatchOk vBs) ::
      rw "match-var-diff" (miMatchVarK vV vTerm vBs (MISome vOld)) MIMatchFail ::
      rw "match-list-nil-ok" (miMatchList MINil MINil vBs) (MIMatchOk vBs) ::
      rw "match-list-nil-fail" (miMatchList MINil vTs vBs) MIMatchFail ::
      rw "match-list-cons" (miMatchList (MICons vP vPs) (MICons vT vTs) vBs)
        (miMatchListK vPs vTs (miMatch vP vT vBs)) ::
      rw "match-list-cons-fail" (miMatchList (MICons vP vPs) vTs vBs) MIMatchFail ::
      rw "match-listK-ok" (miMatchListK vPs vTs (MIMatchOk vBs2))
        (miMatchList vPs vTs vBs2) ::
      rw "match-listK-fail" (miMatchListK vPs vTs MIMatchFail) MIMatchFail ::
      rw "match-var-pattern" (miMatch (app "MIVar" [vV]) vTerm vBs)
        (miMatchVar vV vTerm vBs) ::
      rw "match-sym-same" (miMatch (app "MISym" [vV]) (app "MISym" [vV]) vBs)
        (MIMatchOk vBs) ::
      rw "match-sym-fail" (miMatch (app "MISym" [vV]) vTerm vBs) MIMatchFail ::
      rw "match-app-same" (miMatch (app "MIApp" [vH, vArgs]) (app "MIApp" [vH, vArgs2]) vBs)
        (miMatchList vArgs vArgs2 vBs) ::
      List.drop 17 miRules := by
  rfl

theorem baseReducts_miMatch_app_same_named_head (h : String) (args args2 bs : AST) :
    ∃ tail,
      baseReducts pMI (miMatch (MIApp h args) (MIApp h args2) bs) =
        miMatchList args args2 bs :: tail := by
  let target := miMatch (MIApp h args) (MIApp h args2) bs
  refine ⟨(List.drop 17 miRules).filterMap (fun rd => applyBaseRewrite rd target), ?_⟩
  change miRules.filterMap (fun rd => applyBaseRewrite rd target) =
    miMatchList args args2 bs ::
      (List.drop 17 miRules).filterMap (fun rd => applyBaseRewrite rd target)
  rw [miRules_match_app_same_prefix]
  dsimp only [target]
  have h_lookup_nil :
      applyBaseRewrite (rw "lookup-nil" (miLookup vV MIBNil) MINone)
        (miMatch (MIApp h args) (MIApp h args2) bs) = none := by
    rfl
  have h_lookup_hit :
      applyBaseRewrite (rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT))
        (miMatch (MIApp h args) (MIApp h args2) bs) = none := by
    rfl
  have h_lookup_miss :
      applyBaseRewrite
        (rw "lookup-miss" (miLookup vV (MIBCons vW vT vRest)) (miLookup vV vRest))
        (miMatch (MIApp h args) (MIApp h args2) bs) = none := by
    rfl
  have h_match_var :
      applyBaseRewrite
        (rw "match-var" (miMatchVar vV vTerm vBs)
          (miMatchVarK vV vTerm vBs (miLookup vV vBs)))
        (miMatch (MIApp h args) (MIApp h args2) bs) = none := by
    rfl
  have h_match_var_none :
      applyBaseRewrite
        (rw "match-var-none" (miMatchVarK vV vTerm vBs MINone)
          (MIMatchOk (MIBCons vV vTerm vBs)))
        (miMatch (MIApp h args) (MIApp h args2) bs) = none := by
    rfl
  have h_match_var_same :
      applyBaseRewrite
        (rw "match-var-same" (miMatchVarK vV vTerm vBs (MISome vTerm))
          (MIMatchOk vBs))
        (miMatch (MIApp h args) (MIApp h args2) bs) = none := by
    rfl
  have h_match_var_diff :
      applyBaseRewrite
        (rw "match-var-diff" (miMatchVarK vV vTerm vBs (MISome vOld)) MIMatchFail)
        (miMatch (MIApp h args) (MIApp h args2) bs) = none := by
    rfl
  have h_list_nil_ok :
      applyBaseRewrite (rw "match-list-nil-ok" (miMatchList MINil MINil vBs) (MIMatchOk vBs))
        (miMatch (MIApp h args) (MIApp h args2) bs) = none := by
    rfl
  have h_list_nil_fail :
      applyBaseRewrite (rw "match-list-nil-fail" (miMatchList MINil vTs vBs) MIMatchFail)
        (miMatch (MIApp h args) (MIApp h args2) bs) = none := by
    rfl
  have h_list_cons :
      applyBaseRewrite
        (rw "match-list-cons" (miMatchList (MICons vP vPs) (MICons vT vTs) vBs)
          (miMatchListK vPs vTs (miMatch vP vT vBs)))
        (miMatch (MIApp h args) (MIApp h args2) bs) = none := by
    rfl
  have h_list_cons_fail :
      applyBaseRewrite (rw "match-list-cons-fail" (miMatchList (MICons vP vPs) vTs vBs) MIMatchFail)
        (miMatch (MIApp h args) (MIApp h args2) bs) = none := by
    rfl
  have h_listK_ok :
      applyBaseRewrite
        (rw "match-listK-ok" (miMatchListK vPs vTs (MIMatchOk vBs2))
          (miMatchList vPs vTs vBs2))
        (miMatch (MIApp h args) (MIApp h args2) bs) = none := by
    rfl
  have h_listK_fail :
      applyBaseRewrite (rw "match-listK-fail" (miMatchListK vPs vTs MIMatchFail) MIMatchFail)
        (miMatch (MIApp h args) (MIApp h args2) bs) = none := by
    rfl
  have h_match_var_pattern :
      applyBaseRewrite
        (rw "match-var-pattern" (miMatch (app "MIVar" [vV]) vTerm vBs)
          (miMatchVar vV vTerm vBs))
        (miMatch (MIApp h args) (MIApp h args2) bs) = none := by
    rfl
  have h_match_sym_same :
      applyBaseRewrite
        (rw "match-sym-same" (miMatch (app "MISym" [vV]) (app "MISym" [vV]) vBs)
          (MIMatchOk vBs))
        (miMatch (MIApp h args) (MIApp h args2) bs) = none := by
    rfl
  have h_match_sym_fail :
      applyBaseRewrite (rw "match-sym-fail" (miMatch (app "MISym" [vV]) vTerm vBs) MIMatchFail)
        (miMatch (MIApp h args) (MIApp h args2) bs) = none := by
    rfl
  simp only [List.filterMap_cons, h_lookup_nil, h_lookup_hit, h_lookup_miss,
    h_match_var, h_match_var_none, h_match_var_same, h_match_var_diff,
    h_list_nil_ok, h_list_nil_fail, h_list_cons, h_list_cons_fail,
    h_listK_ok, h_listK_fail, h_match_var_pattern, h_match_sym_same,
    h_match_sym_fail, apply_miMatch_app_same_named, List.drop]

theorem os_miMatch_app_same_named (h : String) (args args2 bs : AST) :
    oneStep pMI (miMatch (MIApp h args) (MIApp h args2) bs) =
      some (miMatchList args args2 bs) := by
  obtain ⟨tail, hhead⟩ := baseReducts_miMatch_app_same_named_head h args args2 bs
  change (match baseReducts pMI (miMatch (MIApp h args) (MIApp h args2) bs) with
    | r :: _ => some r
    | [] =>
      (oneStepList pMI [MIApp h args, MIApp h args2, bs]).map
        (fun args' => AST.sexp (Label.id "mi-match") args')) =
      some (miMatchList args args2 bs)
  rw [hhead]

theorem miMatch_app_same_named_sim (h : String) (args args2 bs : AST) :
    eval pMI 1 (miMatch (MIApp h args) (MIApp h args2) bs) =
      miMatchList args args2 bs := by
  simp only [eval, os_miMatch_app_same_named]

theorem miMatch_app_same_eval_of_list (h : String) (args args2 bs out : AST)
    (listFuel : Nat)
    (hlist : eval pMI listFuel (miMatchList args args2 bs) = out) :
    ∃ N, eval pMI N (miMatch (MIApp h args) (MIApp h args2) bs) = out := by
  have hdispatch :
      eval pMI 1 (miMatch (MIApp h args) (MIApp h args2) bs) =
        miMatchList args args2 bs :=
    miMatch_app_same_named_sim h args args2 bs
  have htotal := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI 1 listFuel
    (miMatch (MIApp h args) (MIApp h args2) bs)
    (miMatchList args args2 bs)
    out
    hdispatch hlist
  exact ⟨1 + listFuel, htotal⟩

theorem miMatch_app_same_first_result_of_list (h : String)
    (args args2 bs out : AST) (listFuel : Nat)
    (hlist : eval pMI listFuel (miMatchList args args2 bs) = out)
    (hlistActive : ∀ k, k < listFuel →
      MatchActiveShape (eval pMI k (miMatchList args args2 bs)))
    (hout : IsNormal pMI out) :
    ∃ N,
      eval pMI N (miMatch (MIApp h args) (MIApp h args2) bs) = out ∧
      (∀ k, k < N →
        MatchActiveShape (eval pMI k (miMatch (MIApp h args) (MIApp h args2) bs))) ∧
      IsNormal pMI out := by
  refine ⟨Nat.succ listFuel, ?_, ?_, hout⟩
  · simp only [eval, os_miMatch_app_same_named]
    exact hlist
  · intro k hk
    cases k with
    | zero =>
        simp only [eval]
        exact MatchActiveShape.match (MIApp h args) (MIApp h args2) bs
    | succ j =>
        have hj : j < listFuel := Nat.succ_lt_succ_iff.mp hk
        have hactive := hlistActive j hj
        simpa only [eval, os_miMatch_app_same_named] using hactive

theorem miMatch_app_same_active_result_of_list (h : String)
    (args args2 bs out : AST) (listFuel : Nat)
    (hlist : eval pMI listFuel (miMatchList args args2 bs) = out)
    (hlistActive : ∀ k, k < listFuel →
      MatchActiveShape (eval pMI k (miMatchList args args2 bs))) :
    ∃ N,
      eval pMI N (miMatch (MIApp h args) (MIApp h args2) bs) = out ∧
      (∀ k, k < N →
        MatchActiveShape
          (eval pMI k (miMatch (MIApp h args) (MIApp h args2) bs))) := by
  refine ⟨Nat.succ listFuel, ?_, ?_⟩
  · simp only [eval, os_miMatch_app_same_named]
    exact hlist
  · intro k hk
    cases k with
    | zero =>
        simp only [eval]
        exact MatchActiveShape.match (MIApp h args) (MIApp h args2) bs
    | succ j =>
        have hj : j < listFuel := Nat.succ_lt_succ_iff.mp hk
        have hactive := hlistActive j hj
        simpa only [eval, os_miMatch_app_same_named] using hactive

theorem miMatch_app_source_same_first_result_of_list (h : String)
    (pats terms : List AST) (encodedPats encodedTerms encodedBs out : AST)
    (listFuel : Nat)
    (_hpats : encASTList? pats = some encodedPats)
    (_hterms : encASTList? terms = some encodedTerms)
    (hlist : eval pMI listFuel
        (miMatchList encodedPats encodedTerms encodedBs) = out)
    (hlistActive : ∀ k, k < listFuel →
      MatchActiveShape
        (eval pMI k (miMatchList encodedPats encodedTerms encodedBs)))
    (hout : IsNormal pMI out) :
    ∃ N,
      eval pMI N
          (miMatch (MIApp h encodedPats) (MIApp h encodedTerms) encodedBs) =
        out ∧
      (∀ k, k < N →
        MatchActiveShape
          (eval pMI k
            (miMatch (MIApp h encodedPats) (MIApp h encodedTerms) encodedBs))) ∧
      IsNormal pMI out :=
  miMatch_app_same_first_result_of_list h encodedPats encodedTerms encodedBs out
    listFuel hlist hlistActive hout

theorem miRules_match_sym_fail_prefix :
    miRules =
      rw "lookup-nil" (miLookup vV MIBNil) MINone ::
      rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT) ::
      rw "lookup-miss" (miLookup vV (MIBCons vW vT vRest)) (miLookup vV vRest) ::
      rw "match-var" (miMatchVar vV vTerm vBs) (miMatchVarK vV vTerm vBs (miLookup vV vBs)) ::
      rw "match-var-none" (miMatchVarK vV vTerm vBs MINone)
        (MIMatchOk (MIBCons vV vTerm vBs)) ::
      rw "match-var-same" (miMatchVarK vV vTerm vBs (MISome vTerm))
        (MIMatchOk vBs) ::
      rw "match-var-diff" (miMatchVarK vV vTerm vBs (MISome vOld)) MIMatchFail ::
      rw "match-list-nil-ok" (miMatchList MINil MINil vBs) (MIMatchOk vBs) ::
      rw "match-list-nil-fail" (miMatchList MINil vTs vBs) MIMatchFail ::
      rw "match-list-cons" (miMatchList (MICons vP vPs) (MICons vT vTs) vBs)
        (miMatchListK vPs vTs (miMatch vP vT vBs)) ::
      rw "match-list-cons-fail" (miMatchList (MICons vP vPs) vTs vBs) MIMatchFail ::
      rw "match-listK-ok" (miMatchListK vPs vTs (MIMatchOk vBs2))
        (miMatchList vPs vTs vBs2) ::
      rw "match-listK-fail" (miMatchListK vPs vTs MIMatchFail) MIMatchFail ::
      rw "match-var-pattern" (miMatch (app "MIVar" [vV]) vTerm vBs)
        (miMatchVar vV vTerm vBs) ::
      rw "match-sym-same" (miMatch (app "MISym" [vV]) (app "MISym" [vV]) vBs)
        (MIMatchOk vBs) ::
      rw "match-sym-fail" (miMatch (app "MISym" [vV]) vTerm vBs) MIMatchFail ::
      List.drop 16 miRules := by
  rfl

theorem baseReducts_miMatch_sym_diff_named_head (s t : String) (bs : AST)
    (hst : (s == t) = false) :
    ∃ tail,
      baseReducts pMI (miMatch (MISym s) (MISym t) bs) =
        MIMatchFail :: tail := by
  let target := miMatch (MISym s) (MISym t) bs
  refine ⟨(List.drop 16 miRules).filterMap (fun rd => applyBaseRewrite rd target), ?_⟩
  change miRules.filterMap (fun rd => applyBaseRewrite rd target) =
    MIMatchFail :: (List.drop 16 miRules).filterMap (fun rd => applyBaseRewrite rd target)
  rw [miRules_match_sym_fail_prefix]
  dsimp only [target]
  have h_lookup_nil :
      applyBaseRewrite (rw "lookup-nil" (miLookup vV MIBNil) MINone)
        (miMatch (MISym s) (MISym t) bs) = none := by
    rfl
  have h_lookup_hit :
      applyBaseRewrite (rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT))
        (miMatch (MISym s) (MISym t) bs) = none := by
    rfl
  have h_lookup_miss :
      applyBaseRewrite
        (rw "lookup-miss" (miLookup vV (MIBCons vW vT vRest)) (miLookup vV vRest))
        (miMatch (MISym s) (MISym t) bs) = none := by
    rfl
  have h_match_var :
      applyBaseRewrite
        (rw "match-var" (miMatchVar vV vTerm vBs)
          (miMatchVarK vV vTerm vBs (miLookup vV vBs)))
        (miMatch (MISym s) (MISym t) bs) = none := by
    rfl
  have h_match_var_none :
      applyBaseRewrite
        (rw "match-var-none" (miMatchVarK vV vTerm vBs MINone)
          (MIMatchOk (MIBCons vV vTerm vBs)))
        (miMatch (MISym s) (MISym t) bs) = none := by
    rfl
  have h_match_var_same :
      applyBaseRewrite
        (rw "match-var-same" (miMatchVarK vV vTerm vBs (MISome vTerm))
          (MIMatchOk vBs))
        (miMatch (MISym s) (MISym t) bs) = none := by
    rfl
  have h_match_var_diff :
      applyBaseRewrite
        (rw "match-var-diff" (miMatchVarK vV vTerm vBs (MISome vOld)) MIMatchFail)
        (miMatch (MISym s) (MISym t) bs) = none := by
    rfl
  have h_list_nil_ok :
      applyBaseRewrite (rw "match-list-nil-ok" (miMatchList MINil MINil vBs) (MIMatchOk vBs))
        (miMatch (MISym s) (MISym t) bs) = none := by
    rfl
  have h_list_nil_fail :
      applyBaseRewrite (rw "match-list-nil-fail" (miMatchList MINil vTs vBs) MIMatchFail)
        (miMatch (MISym s) (MISym t) bs) = none := by
    rfl
  have h_list_cons :
      applyBaseRewrite
        (rw "match-list-cons" (miMatchList (MICons vP vPs) (MICons vT vTs) vBs)
          (miMatchListK vPs vTs (miMatch vP vT vBs)))
        (miMatch (MISym s) (MISym t) bs) = none := by
    rfl
  have h_list_cons_fail :
      applyBaseRewrite (rw "match-list-cons-fail" (miMatchList (MICons vP vPs) vTs vBs) MIMatchFail)
        (miMatch (MISym s) (MISym t) bs) = none := by
    rfl
  have h_listK_ok :
      applyBaseRewrite
        (rw "match-listK-ok" (miMatchListK vPs vTs (MIMatchOk vBs2))
          (miMatchList vPs vTs vBs2))
        (miMatch (MISym s) (MISym t) bs) = none := by
    rfl
  have h_listK_fail :
      applyBaseRewrite (rw "match-listK-fail" (miMatchListK vPs vTs MIMatchFail) MIMatchFail)
        (miMatch (MISym s) (MISym t) bs) = none := by
    rfl
  have h_match_var_pattern :
      applyBaseRewrite
        (rw "match-var-pattern" (miMatch (app "MIVar" [vV]) vTerm vBs)
          (miMatchVar vV vTerm vBs))
        (miMatch (MISym s) (MISym t) bs) = none := by
    rfl
  simp only [List.filterMap_cons, h_lookup_nil, h_lookup_hit, h_lookup_miss,
    h_match_var, h_match_var_none, h_match_var_same, h_match_var_diff,
    h_list_nil_ok, h_list_nil_fail, h_list_cons, h_list_cons_fail,
    h_listK_ok, h_listK_fail, h_match_var_pattern,
    apply_miMatch_sym_same_on_distinct_named, hst, apply_miMatch_sym_fail_named,
    List.drop]

theorem os_miMatch_sym_diff_named (s t : String) (bs : AST)
    (hst : (s == t) = false) :
    oneStep pMI (miMatch (MISym s) (MISym t) bs) = some MIMatchFail := by
  obtain ⟨tail, hhead⟩ := baseReducts_miMatch_sym_diff_named_head s t bs hst
  change (match baseReducts pMI (miMatch (MISym s) (MISym t) bs) with
    | r :: _ => some r
    | [] =>
      (oneStepList pMI [MISym s, MISym t, bs]).map
        (fun args' => AST.sexp (Label.id "mi-match") args')) =
      some MIMatchFail
  rw [hhead]

theorem miMatch_sym_diff_named_sim (s t : String) (bs : AST)
    (hst : (s == t) = false) :
    eval pMI 1 (miMatch (MISym s) (MISym t) bs) = MIMatchFail := by
  simp only [eval, os_miMatch_sym_diff_named, hst]

theorem miMatchList_cons_sym_same_eval_of_tail (s : String)
    (ps ts bs out : AST) (tailFuel : Nat)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI ts)
    (hbs : IsNormal pMI bs)
    (htail : eval pMI tailFuel (miMatchList ps ts bs) = out) :
    ∃ N,
      eval pMI N (miMatchList (MICons (MISym s) ps) (MICons (MISym s) ts) bs) =
        out := by
  exact miMatchList_cons_eval_of_match_ok (MISym s) ps (MISym s) ts bs bs out
    1 tailFuel hps hts hbs (miMatch_sym_same_named_sim s bs)
    (miMatch_active_guard_one (MISym s) (MISym s) bs) htail

theorem miMatchList_cons_sym_diff_named_fail (s t : String)
    (ps ts bs : AST) (hst : (s == t) = false)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI ts) :
    ∃ N,
      eval pMI N (miMatchList (MICons (MISym s) ps) (MICons (MISym t) ts) bs) =
        MIMatchFail := by
  exact miMatchList_cons_eval_of_match_fail (MISym s) ps (MISym t) ts bs
    1 hps hts (miMatch_sym_diff_named_sim s t bs hst)
    (miMatch_active_guard_one (MISym s) (MISym t) bs)

theorem miRules_match_app_fail_prefix :
    miRules =
      rw "lookup-nil" (miLookup vV MIBNil) MINone ::
      rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT) ::
      rw "lookup-miss" (miLookup vV (MIBCons vW vT vRest)) (miLookup vV vRest) ::
      rw "match-var" (miMatchVar vV vTerm vBs) (miMatchVarK vV vTerm vBs (miLookup vV vBs)) ::
      rw "match-var-none" (miMatchVarK vV vTerm vBs MINone)
        (MIMatchOk (MIBCons vV vTerm vBs)) ::
      rw "match-var-same" (miMatchVarK vV vTerm vBs (MISome vTerm))
        (MIMatchOk vBs) ::
      rw "match-var-diff" (miMatchVarK vV vTerm vBs (MISome vOld)) MIMatchFail ::
      rw "match-list-nil-ok" (miMatchList MINil MINil vBs) (MIMatchOk vBs) ::
      rw "match-list-nil-fail" (miMatchList MINil vTs vBs) MIMatchFail ::
      rw "match-list-cons" (miMatchList (MICons vP vPs) (MICons vT vTs) vBs)
        (miMatchListK vPs vTs (miMatch vP vT vBs)) ::
      rw "match-list-cons-fail" (miMatchList (MICons vP vPs) vTs vBs) MIMatchFail ::
      rw "match-listK-ok" (miMatchListK vPs vTs (MIMatchOk vBs2))
        (miMatchList vPs vTs vBs2) ::
      rw "match-listK-fail" (miMatchListK vPs vTs MIMatchFail) MIMatchFail ::
      rw "match-var-pattern" (miMatch (app "MIVar" [vV]) vTerm vBs)
        (miMatchVar vV vTerm vBs) ::
      rw "match-sym-same" (miMatch (app "MISym" [vV]) (app "MISym" [vV]) vBs)
        (MIMatchOk vBs) ::
      rw "match-sym-fail" (miMatch (app "MISym" [vV]) vTerm vBs) MIMatchFail ::
      rw "match-app-same" (miMatch (app "MIApp" [vH, vArgs]) (app "MIApp" [vH, vArgs2]) vBs)
        (miMatchList vArgs vArgs2 vBs) ::
      rw "match-app-fail" (miMatch (app "MIApp" [vH, vArgs]) vTerm vBs) MIMatchFail ::
      List.drop 18 miRules := by
  rfl

theorem baseReducts_miMatch_app_diff_named_head (h k : String)
    (args args2 bs : AST) (hhk : (h == k) = false) :
    ∃ tail,
      baseReducts pMI (miMatch (MIApp h args) (MIApp k args2) bs) =
        MIMatchFail :: tail := by
  let target := miMatch (MIApp h args) (MIApp k args2) bs
  refine ⟨(List.drop 18 miRules).filterMap (fun rd => applyBaseRewrite rd target), ?_⟩
  change miRules.filterMap (fun rd => applyBaseRewrite rd target) =
    MIMatchFail :: (List.drop 18 miRules).filterMap (fun rd => applyBaseRewrite rd target)
  rw [miRules_match_app_fail_prefix]
  dsimp only [target]
  have h_lookup_nil :
      applyBaseRewrite (rw "lookup-nil" (miLookup vV MIBNil) MINone)
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
    rfl
  have h_lookup_hit :
      applyBaseRewrite (rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT))
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
    rfl
  have h_lookup_miss :
      applyBaseRewrite
        (rw "lookup-miss" (miLookup vV (MIBCons vW vT vRest)) (miLookup vV vRest))
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
    rfl
  have h_match_var :
      applyBaseRewrite
        (rw "match-var" (miMatchVar vV vTerm vBs)
          (miMatchVarK vV vTerm vBs (miLookup vV vBs)))
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
    rfl
  have h_match_var_none :
      applyBaseRewrite
        (rw "match-var-none" (miMatchVarK vV vTerm vBs MINone)
          (MIMatchOk (MIBCons vV vTerm vBs)))
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
    rfl
  have h_match_var_same :
      applyBaseRewrite
        (rw "match-var-same" (miMatchVarK vV vTerm vBs (MISome vTerm))
          (MIMatchOk vBs))
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
    rfl
  have h_match_var_diff :
      applyBaseRewrite
        (rw "match-var-diff" (miMatchVarK vV vTerm vBs (MISome vOld)) MIMatchFail)
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
    rfl
  have h_list_nil_ok :
      applyBaseRewrite (rw "match-list-nil-ok" (miMatchList MINil MINil vBs) (MIMatchOk vBs))
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
    rfl
  have h_list_nil_fail :
      applyBaseRewrite (rw "match-list-nil-fail" (miMatchList MINil vTs vBs) MIMatchFail)
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
    rfl
  have h_list_cons :
      applyBaseRewrite
        (rw "match-list-cons" (miMatchList (MICons vP vPs) (MICons vT vTs) vBs)
          (miMatchListK vPs vTs (miMatch vP vT vBs)))
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
    rfl
  have h_list_cons_fail :
      applyBaseRewrite (rw "match-list-cons-fail" (miMatchList (MICons vP vPs) vTs vBs) MIMatchFail)
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
    rfl
  have h_listK_ok :
      applyBaseRewrite
        (rw "match-listK-ok" (miMatchListK vPs vTs (MIMatchOk vBs2))
          (miMatchList vPs vTs vBs2))
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
    rfl
  have h_listK_fail :
      applyBaseRewrite (rw "match-listK-fail" (miMatchListK vPs vTs MIMatchFail) MIMatchFail)
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
    rfl
  have h_match_var_pattern :
      applyBaseRewrite
        (rw "match-var-pattern" (miMatch (app "MIVar" [vV]) vTerm vBs)
          (miMatchVar vV vTerm vBs))
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
    rfl
  have h_match_sym_same :
      applyBaseRewrite
        (rw "match-sym-same" (miMatch (app "MISym" [vV]) (app "MISym" [vV]) vBs)
          (MIMatchOk vBs))
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
    rfl
  have h_match_sym_fail :
      applyBaseRewrite (rw "match-sym-fail" (miMatch (app "MISym" [vV]) vTerm vBs) MIMatchFail)
        (miMatch (MIApp h args) (MIApp k args2) bs) = none := by
    rfl
  simp only [List.filterMap_cons, h_lookup_nil, h_lookup_hit, h_lookup_miss,
    h_match_var, h_match_var_none, h_match_var_same, h_match_var_diff,
    h_list_nil_ok, h_list_nil_fail, h_list_cons, h_list_cons_fail,
    h_listK_ok, h_listK_fail, h_match_var_pattern, h_match_sym_same,
    h_match_sym_fail, apply_miMatch_app_same_on_distinct_named, hhk,
    apply_miMatch_app_fail_named, List.drop]

theorem os_miMatch_app_diff_named (h k : String) (args args2 bs : AST)
    (hhk : (h == k) = false) :
    oneStep pMI (miMatch (MIApp h args) (MIApp k args2) bs) = some MIMatchFail := by
  obtain ⟨tail, hhead⟩ := baseReducts_miMatch_app_diff_named_head h k args args2 bs hhk
  change (match baseReducts pMI (miMatch (MIApp h args) (MIApp k args2) bs) with
    | r :: _ => some r
    | [] =>
      (oneStepList pMI [MIApp h args, MIApp k args2, bs]).map
        (fun args' => AST.sexp (Label.id "mi-match") args')) =
      some MIMatchFail
  rw [hhead]

theorem miMatch_app_diff_named_sim (h k : String) (args args2 bs : AST)
    (hhk : (h == k) = false) :
    eval pMI 1 (miMatch (MIApp h args) (MIApp k args2) bs) = MIMatchFail := by
  simp only [eval, os_miMatch_app_diff_named, hhk]

theorem os_miMatch_sym_app_fail (s h : String) (args bs : AST) :
    oneStep pMI (miMatch (MISym s) (MIApp h args) bs) = some MIMatchFail := by
  rfl

theorem os_miMatch_app_sym_fail (h s : String) (args bs : AST) :
    oneStep pMI (miMatch (MIApp h args) (MISym s) bs) = some MIMatchFail := by
  rfl

theorem miMatch_sym_app_fail_sim (s h : String) (args bs : AST) :
    eval pMI 1 (miMatch (MISym s) (MIApp h args) bs) = MIMatchFail := by
  simp only [eval, os_miMatch_sym_app_fail]

theorem miMatch_app_sym_fail_sim (h s : String) (args bs : AST) :
    eval pMI 1 (miMatch (MIApp h args) (MISym s) bs) = MIMatchFail := by
  simp only [eval, os_miMatch_app_sym_fail]

theorem miMatch_sym_var_fail_sim (s v : String) (bs : AST) :
    eval pMI 1 (miMatch (MISym s) (MIVar v) bs) = MIMatchFail := by
  rfl

theorem miMatch_app_var_fail_sim (h v : String) (args bs : AST) :
    eval pMI 1 (miMatch (MIApp h args) (MIVar v) bs) = MIMatchFail := by
  rfl

theorem miMatch_app_source_diff_head_first_result (h k : String)
    (pats terms : List AST) (encodedPats encodedTerms encodedBs : AST)
    (_hpats : encASTList? pats = some encodedPats)
    (_hterms : encASTList? terms = some encodedTerms)
    (hhk : (h == k) = false) :
    ∃ N,
      eval pMI N
          (miMatch (MIApp h encodedPats) (MIApp k encodedTerms) encodedBs) =
        MIMatchFail ∧
      (∀ j, j < N →
        MatchActiveShape
          (eval pMI j
            (miMatch (MIApp h encodedPats) (MIApp k encodedTerms) encodedBs))) ∧
      IsNormal pMI MIMatchFail :=
  ⟨1, miMatch_app_diff_named_sim h k encodedPats encodedTerms encodedBs hhk,
    miMatch_active_guard_one (MIApp h encodedPats) (MIApp k encodedTerms)
      encodedBs,
    normal_MIMatchFail⟩

theorem miMatch_app_source_var_fail_first_result (h v : String)
    (pats : List AST) (encodedPats encodedBs : AST)
    (_hpats : encASTList? pats = some encodedPats) :
    ∃ N,
      eval pMI N (miMatch (MIApp h encodedPats) (MIVar v) encodedBs) =
        MIMatchFail ∧
      (∀ j, j < N →
        MatchActiveShape
          (eval pMI j (miMatch (MIApp h encodedPats) (MIVar v) encodedBs))) ∧
      IsNormal pMI MIMatchFail :=
  ⟨1, miMatch_app_var_fail_sim h v encodedPats encodedBs,
    miMatch_active_guard_one (MIApp h encodedPats) (MIVar v) encodedBs,
    normal_MIMatchFail⟩

theorem miMatch_app_source_sym_fail_first_result (h s : String)
    (pats : List AST) (encodedPats encodedBs : AST)
    (_hpats : encASTList? pats = some encodedPats) :
    ∃ N,
      eval pMI N (miMatch (MIApp h encodedPats) (MISym s) encodedBs) =
        MIMatchFail ∧
      (∀ j, j < N →
        MatchActiveShape
          (eval pMI j (miMatch (MIApp h encodedPats) (MISym s) encodedBs))) ∧
      IsNormal pMI MIMatchFail :=
  ⟨1, miMatch_app_sym_fail_sim h s encodedPats encodedBs,
    miMatch_active_guard_one (MIApp h encodedPats) (MISym s) encodedBs,
    normal_MIMatchFail⟩

theorem miMatch_sym_raw_app_fail_first_result (s h : String)
    (rawArgs bs : AST) :
    ∃ N,
      eval pMI N (miMatch (MISym s) (MIApp h rawArgs) bs) =
        MIMatchFail ∧
      (∀ j, j < N →
        MatchActiveShape
          (eval pMI j (miMatch (MISym s) (MIApp h rawArgs) bs))) ∧
      IsNormal pMI MIMatchFail :=
  ⟨1, miMatch_sym_app_fail_sim s h rawArgs bs,
    miMatch_active_guard_one (MISym s) (MIApp h rawArgs) bs,
    normal_MIMatchFail⟩

theorem miMatch_app_raw_diff_head_first_result (h k : String)
    (pats rawArgs bs : AST) (hhk : (h == k) = false) :
    ∃ N,
      eval pMI N (miMatch (MIApp h pats) (MIApp k rawArgs) bs) =
        MIMatchFail ∧
      (∀ j, j < N →
        MatchActiveShape
          (eval pMI j (miMatch (MIApp h pats) (MIApp k rawArgs) bs))) ∧
      IsNormal pMI MIMatchFail :=
  ⟨1, miMatch_app_diff_named_sim h k pats rawArgs bs hhk,
    miMatch_active_guard_one (MIApp h pats) (MIApp k rawArgs) bs,
    normal_MIMatchFail⟩

theorem miMatch_app_raw_same_head_fail_of_list (h : String)
    (pats rawArgs rawBinds : AST)
    (listFuel : Nat)
    (hlist :
      eval pMI listFuel (miMatchList pats rawArgs rawBinds) =
        MIMatchFail)
    (hlistActive : ∀ k, k < listFuel →
      MatchActiveShape
        (eval pMI k (miMatchList pats rawArgs rawBinds))) :
    ∃ N,
      eval pMI N (miMatch (MIApp h pats) (MIApp h rawArgs) rawBinds) =
        MIMatchFail ∧
      (∀ k, k < N →
        MatchActiveShape
          (eval pMI k
            (miMatch (MIApp h pats) (MIApp h rawArgs) rawBinds))) ∧
      IsNormal pMI MIMatchFail :=
  miMatch_app_same_first_result_of_list h pats rawArgs rawBinds MIMatchFail
    listFuel hlist hlistActive normal_MIMatchFail

theorem miMatch_sym_source_some_first_result (s : String)
    (term encodedTerm encodedBs encodedOut : AST)
    (bs bsOut : List (String × AST))
    (hterm : encAST? term = some encodedTerm)
    (hbs : encBinds? bs = some encodedBs)
    (hmatch : AST.matchPat (.sexp (.id s) []) term bs = some bsOut)
    (hout : encBinds? bsOut = some encodedOut) :
    ∃ N,
      eval pMI N (miMatch (MISym s) encodedTerm encodedBs) =
        MIMatchOk encodedOut ∧
      (∀ k, k < N →
        MatchActiveShape (eval pMI k (miMatch (MISym s) encodedTerm encodedBs))) ∧
      IsNormal pMI (MIMatchOk encodedOut) := by
  cases term with
  | var p =>
      cases p with
      | base _ =>
          simp only [encAST?] at hterm
          cases hterm
          simp only [AST.matchPat] at hmatch
          cases hmatch
      | qualified _ _ =>
          simp only [encAST?] at hterm
          cases hterm
  | subst _ _ _ =>
      simp only [encAST?] at hterm
      cases hterm
  | sexp l args =>
      cases l with
      | id t =>
          cases args with
          | nil =>
              simp only [encAST?] at hterm
              cases hterm
              simp only [AST.matchPat, AST.matchPatList, label_id_beq] at hmatch
              by_cases hst : (s == t) = true
              · have hEq : s = t := beq_iff_eq.mp hst
                subst t
                have hss : (s == s) = true := beq_iff_eq.mpr rfl
                simp only [hss, if_true] at hmatch
                cases hmatch
                rw [hbs] at hout
                cases hout
                refine ⟨1, ?_,
                  miMatch_active_guard_one (MISym s) (MISym s) encodedBs,
                  normal_MIMatchOk encodedBs
                    (encBinds?_some_normal bs encodedBs hbs)⟩
                exact miMatch_sym_same_named_sim s encodedBs
              · have hstFalse : (s == t) = false := by
                  cases hcmp : (s == t) <;> simp [hcmp] at hst ⊢
                simp only [hstFalse, Bool.false_eq_true, if_false] at hmatch
                cases hmatch
          | cons a rest =>
              simp only [encAST?] at hterm
              cases hargs : encASTList? (a :: rest) with
              | none => simp [hargs] at hterm
              | some _ =>
                  simp [hargs] at hterm
                  simp only [AST.matchPat, label_id_beq] at hmatch
                  by_cases hst : (s == t) = true
                  · simp only [hst, if_true] at hmatch
                    simp only [AST.matchPatList] at hmatch
                    cases hmatch
                  · have hstFalse : (s == t) = false := by
                      cases hcmp : (s == t) <;> simp [hcmp] at hst ⊢
                    simp only [hstFalse, Bool.false_eq_true, if_false] at hmatch
                    cases hmatch
      | wild =>
          simp only [encAST?] at hterm
          cases hterm
      | listE _ =>
          simp only [encAST?] at hterm
          cases hterm
      | listCons _ =>
          simp only [encAST?] at hterm
          cases hterm
      | listOne _ =>
          simp only [encAST?] at hterm
          cases hterm

theorem miMatch_sym_source_none_first_result (s : String)
    (term encodedTerm encodedBs : AST)
    (bs : List (String × AST))
    (hterm : encAST? term = some encodedTerm)
    (_hbs : encBinds? bs = some encodedBs)
    (hmatch : AST.matchPat (.sexp (.id s) []) term bs = none) :
    ∃ N,
      eval pMI N (miMatch (MISym s) encodedTerm encodedBs) = MIMatchFail ∧
      (∀ k, k < N →
        MatchActiveShape (eval pMI k (miMatch (MISym s) encodedTerm encodedBs))) ∧
      IsNormal pMI MIMatchFail := by
  cases term with
  | var p =>
      cases p with
      | base v =>
          simp only [encAST?] at hterm
          cases hterm
          exact ⟨1, miMatch_sym_var_fail_sim s v encodedBs,
            miMatch_active_guard_one (MISym s) (MIVar v) encodedBs,
            normal_MIMatchFail⟩
      | qualified _ _ =>
          simp only [encAST?] at hterm
          cases hterm
  | subst _ _ _ =>
      simp only [encAST?] at hterm
      cases hterm
  | sexp l args =>
      cases l with
      | id t =>
          cases args with
          | nil =>
              simp only [encAST?] at hterm
              cases hterm
              simp only [AST.matchPat, AST.matchPatList, label_id_beq] at hmatch
              by_cases hst : (s == t) = true
              · have hEq : s = t := beq_iff_eq.mp hst
                subst t
                have hss : (s == s) = true := beq_iff_eq.mpr rfl
                simp only [hss, if_true] at hmatch
                cases hmatch
              · have hstFalse : (s == t) = false := by
                  cases hcmp : (s == t) <;> simp [hcmp] at hst ⊢
                exact ⟨1, miMatch_sym_diff_named_sim s t encodedBs hstFalse,
                  miMatch_active_guard_one (MISym s) (MISym t) encodedBs,
                  normal_MIMatchFail⟩
          | cons a rest =>
              simp only [encAST?] at hterm
              cases hargs : encASTList? (a :: rest) with
              | none => simp [hargs] at hterm
              | some encodedArgs =>
                  simp [hargs] at hterm
                  cases hterm
                  exact ⟨1, miMatch_sym_app_fail_sim s t encodedArgs encodedBs,
                    miMatch_active_guard_one (MISym s)
                      (MIApp t encodedArgs) encodedBs,
                    normal_MIMatchFail⟩
      | wild =>
          simp only [encAST?] at hterm
          cases hterm
      | listE _ =>
          simp only [encAST?] at hterm
          cases hterm
      | listCons _ =>
          simp only [encAST?] at hterm
          cases hterm
      | listOne _ =>
          simp only [encAST?] at hterm
          cases hterm

mutual
  theorem miMatch_source_some_first_result :
      ∀ (pat term encodedPat encodedTerm encodedBs encodedOut : AST)
        (bs bsOut : List (String × AST)),
        encAST? pat = some encodedPat →
        encAST? term = some encodedTerm →
        encBinds? bs = some encodedBs →
        AST.matchPat pat term bs = some bsOut →
        encBinds? bsOut = some encodedOut →
        ∃ N,
          eval pMI N (miMatch encodedPat encodedTerm encodedBs) =
            MIMatchOk encodedOut ∧
          (∀ k, k < N →
            MatchActiveShape
              (eval pMI k (miMatch encodedPat encodedTerm encodedBs))) ∧
          IsNormal pMI (MIMatchOk encodedOut)
    | .var (.base v), term, _, encodedTerm, encodedBs, encodedOut, bs, bsOut,
        hpat, hterm, hbs, hmatch, hout => by
        simp only [encAST?] at hpat
        cases hpat
        exact miMatch_var_source_some_first_result v term encodedTerm encodedBs
          encodedOut bs bsOut hterm hbs hmatch hout
    | .var (.qualified _ _), _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .subst _ _ _, _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.id s) [], term, _, encodedTerm, encodedBs, encodedOut, bs, bsOut,
        hpat, hterm, hbs, hmatch, hout => by
        simp only [encAST?] at hpat
        cases hpat
        exact miMatch_sym_source_some_first_result s term encodedTerm encodedBs
          encodedOut bs bsOut hterm hbs hmatch hout
    | .sexp (.id s) (pHead :: pTail), term, _, encodedTerm, encodedBs,
        encodedOut, bs, bsOut, hpat, hterm, hbs, hmatch, hout => by
        simp only [encAST?] at hpat
        cases hpats : encASTList? (pHead :: pTail) with
        | none =>
            simp [hpats] at hpat
        | some encodedPats =>
            simp [hpats] at hpat
            cases hpat
            cases term with
            | var p =>
                cases p with
                | base v =>
                    simp only [encAST?] at hterm
                    cases hterm
                    simp [AST.matchPat] at hmatch
                    have hEq := ast_beq_true_eq_mi
                      (AST.sexp (Label.id s) (pHead :: pTail))
                      (AST.var (.base v)) hmatch.1
                    cases hEq
                | qualified _ _ =>
                    simp only [encAST?] at hterm
                    cases hterm
            | subst _ _ _ =>
                simp only [encAST?] at hterm
                cases hterm
            | sexp l terms =>
                cases l with
                | id t =>
                    cases terms with
                    | nil =>
                        simp only [encAST?] at hterm
                        cases hterm
                        simp only [AST.matchPat, AST.matchPatList, label_id_beq] at hmatch
                        by_cases hst : (s == t) = true
                        · simp only [hst, if_true] at hmatch
                          cases hmatch
                        · have hstFalse : (s == t) = false := by
                            cases hcmp : (s == t) <;> simp [hcmp] at hst ⊢
                          simp only [hstFalse, Bool.false_eq_true, if_false] at hmatch
                          cases hmatch
                    | cons tHead tTail =>
                        change
                          (match encASTList? (tHead :: tTail) with
                          | some encodedArgs => some (MIApp t encodedArgs)
                          | none => none) = some encodedTerm at hterm
                        cases hterms : encASTList? (tHead :: tTail) with
                        | none =>
                            rw [hterms] at hterm
                            cases hterm
                        | some encodedTerms =>
                            rw [hterms] at hterm
                            cases hterm
                            simp only [AST.matchPat, label_id_beq] at hmatch
                            by_cases hst : (s == t) = true
                            · simp only [hst, if_true] at hmatch
                              have hEq : s = t := beq_iff_eq.mp hst
                              subst t
                              obtain ⟨Nlist, hlist, hlistActive, hlistNorm⟩ :=
                                miMatchList_source_some_first_result
                                  (pHead :: pTail) (tHead :: tTail)
                                  encodedPats encodedTerms encodedBs encodedOut
                                  bs bsOut hpats hterms hbs hmatch hout
                              exact miMatch_app_source_same_first_result_of_list s
                                (pHead :: pTail) (tHead :: tTail)
                                encodedPats encodedTerms encodedBs
                                (MIMatchOk encodedOut) Nlist hpats hterms
                                hlist hlistActive hlistNorm
                            · have hstFalse : (s == t) = false := by
                                cases hcmp : (s == t) <;> simp [hcmp] at hst ⊢
                              simp only [hstFalse, Bool.false_eq_true, if_false] at hmatch
                              cases hmatch
                | wild =>
                    simp only [encAST?] at hterm
                    cases hterm
                | listE _ =>
                    simp only [encAST?] at hterm
                    cases hterm
                | listCons _ =>
                    simp only [encAST?] at hterm
                    cases hterm
                | listOne _ =>
                    simp only [encAST?] at hterm
                    cases hterm
    | .sexp (.wild) _, _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.listE _) _, _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.listCons _) _, _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.listOne _) _, _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat

  theorem miMatch_source_none_first_result :
      ∀ (pat term encodedPat encodedTerm encodedBs : AST)
        (bs : List (String × AST)),
        encAST? pat = some encodedPat →
        encAST? term = some encodedTerm →
        encBinds? bs = some encodedBs →
        AST.matchPat pat term bs = none →
        ∃ N,
          eval pMI N (miMatch encodedPat encodedTerm encodedBs) =
            MIMatchFail ∧
          (∀ k, k < N →
            MatchActiveShape
              (eval pMI k (miMatch encodedPat encodedTerm encodedBs))) ∧
          IsNormal pMI MIMatchFail
    | .var (.base v), term, _, encodedTerm, encodedBs, bs,
        hpat, hterm, hbs, hmatch => by
        simp only [encAST?] at hpat
        cases hpat
        exact miMatch_var_source_none_first_result v term encodedTerm encodedBs
          bs hterm hbs hmatch
    | .var (.qualified _ _), _, _, _, _, _, hpat, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .subst _ _ _, _, _, _, _, _, hpat, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.id s) [], term, _, encodedTerm, encodedBs, bs,
        hpat, hterm, hbs, hmatch => by
        simp only [encAST?] at hpat
        cases hpat
        exact miMatch_sym_source_none_first_result s term encodedTerm encodedBs
          bs hterm hbs hmatch
    | .sexp (.id s) (pHead :: pTail), term, _, encodedTerm, encodedBs, bs,
        hpat, hterm, hbs, hmatch => by
        simp only [encAST?] at hpat
        cases hpats : encASTList? (pHead :: pTail) with
        | none =>
            simp [hpats] at hpat
        | some encodedPats =>
            simp [hpats] at hpat
            cases hpat
            cases term with
            | var p =>
                cases p with
                | base v =>
                    simp only [encAST?] at hterm
                    cases hterm
                    exact miMatch_app_source_var_fail_first_result s v
                      (pHead :: pTail) encodedPats encodedBs hpats
                | qualified _ _ =>
                    simp only [encAST?] at hterm
                    cases hterm
            | subst _ _ _ =>
                simp only [encAST?] at hterm
                cases hterm
            | sexp l terms =>
                cases l with
                | id t =>
                    cases terms with
                    | nil =>
                        simp only [encAST?] at hterm
                        cases hterm
                        exact miMatch_app_source_sym_fail_first_result s t
                          (pHead :: pTail) encodedPats encodedBs hpats
                    | cons tHead tTail =>
                        change
                          (match encASTList? (tHead :: tTail) with
                          | some encodedArgs => some (MIApp t encodedArgs)
                          | none => none) = some encodedTerm at hterm
                        cases hterms : encASTList? (tHead :: tTail) with
                        | none =>
                            rw [hterms] at hterm
                            cases hterm
                        | some encodedTerms =>
                            rw [hterms] at hterm
                            cases hterm
                            simp only [AST.matchPat, label_id_beq] at hmatch
                            by_cases hst : (s == t) = true
                            · simp only [hst, if_true] at hmatch
                              have hEq : s = t := beq_iff_eq.mp hst
                              subst t
                              obtain ⟨Nlist, hlist, hlistActive, hlistNorm⟩ :=
                                miMatchList_source_none_first_result
                                  (pHead :: pTail) (tHead :: tTail)
                                  encodedPats encodedTerms encodedBs bs
                                  hpats hterms hbs hmatch
                              exact miMatch_app_source_same_first_result_of_list s
                                (pHead :: pTail) (tHead :: tTail)
                                encodedPats encodedTerms encodedBs
                                MIMatchFail Nlist hpats hterms
                                hlist hlistActive hlistNorm
                            · have hstFalse : (s == t) = false := by
                                cases hcmp : (s == t) <;> simp [hcmp] at hst ⊢
                              exact miMatch_app_source_diff_head_first_result s t
                                (pHead :: pTail) (tHead :: tTail)
                                encodedPats encodedTerms encodedBs hpats hterms hstFalse
                | wild =>
                    simp only [encAST?] at hterm
                    cases hterm
                | listE _ =>
                    simp only [encAST?] at hterm
                    cases hterm
                | listCons _ =>
                    simp only [encAST?] at hterm
                    cases hterm
                | listOne _ =>
                    simp only [encAST?] at hterm
                    cases hterm
    | .sexp (.wild) _, _, _, _, _, _, hpat, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.listE _) _, _, _, _, _, _, hpat, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.listCons _) _, _, _, _, _, _, hpat, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.listOne _) _, _, _, _, _, _, hpat, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat

  theorem miMatchList_source_some_first_result :
      ∀ (pats terms : List AST)
        (encodedPats encodedTerms encodedBs encodedOut : AST)
        (bs bsOut : List (String × AST)),
        encASTList? pats = some encodedPats →
        encASTList? terms = some encodedTerms →
        encBinds? bs = some encodedBs →
        AST.matchPatList pats terms bs = some bsOut →
        encBinds? bsOut = some encodedOut →
        ∃ N,
          eval pMI N (miMatchList encodedPats encodedTerms encodedBs) =
            MIMatchOk encodedOut ∧
          (∀ k, k < N →
            MatchActiveShape
              (eval pMI k (miMatchList encodedPats encodedTerms encodedBs))) ∧
          IsNormal pMI (MIMatchOk encodedOut)
    | [], terms, encodedPats, encodedTerms, encodedBs, encodedOut, bs, bsOut,
        hpats, hterms, hbs, hmatch, hout => by
        simp only [encASTList?] at hpats
        cases hpats
        exact miMatchList_nil_source_some_first_result terms encodedTerms
          encodedBs encodedOut bs bsOut hterms hbs hmatch hout
    | p :: ps, [], encodedPats, _, encodedBs, encodedOut, bs, bsOut,
        hpats, hterms, hbs, hmatch, _hout => by
        simp only [AST.matchPatList] at hmatch
        cases hmatch
    | p :: ps, t :: ts, encodedPats, encodedTerms, encodedBs, encodedOut,
        bs, bsOut, hpats, hterms, hbs, hmatch, hout => by
        simp only [encASTList?] at hpats hterms
        cases hp : encAST? p with
        | none =>
            simp [hp] at hpats
        | some encodedP =>
            cases hps : encASTList? ps with
            | none =>
                simp [hp, hps] at hpats
            | some encodedPs =>
                simp [hp, hps] at hpats
                cases hpats
                cases ht : encAST? t with
                | none =>
                    simp [ht] at hterms
                | some encodedT =>
                    cases hts : encASTList? ts with
                    | none =>
                        simp [ht, hts] at hterms
                    | some encodedTs =>
                        simp [ht, hts] at hterms
                        cases hterms
                        cases hhead : AST.matchPat p t bs with
                        | none =>
                            simp only [AST.matchPatList, hhead, Option.bind_none] at hmatch
                            cases hmatch
                        | some bsMid =>
                            simp only [AST.matchPatList, hhead, Option.bind_some] at hmatch
                            obtain ⟨encodedMid, hmid⟩ :=
                              matchPat_preserves_encBinds? p t encodedP encodedT encodedBs
                                bs bsMid hp ht hbs hhead
                            obtain ⟨Nhead, hheadEval, hheadActive, _hheadNorm⟩ :=
                              miMatch_source_some_first_result p t encodedP encodedT
                                encodedBs encodedMid bs bsMid hp ht hbs hhead hmid
                            obtain ⟨Ntail, htailEval, htailActive, htailNorm⟩ :=
                              miMatchList_source_some_first_result ps ts encodedPs
                                encodedTs encodedMid encodedOut bsMid bsOut hps hts
                                hmid hmatch hout
                            exact miMatchList_cons_first_result_of_match_ok encodedP
                              encodedPs encodedT encodedTs encodedBs encodedMid
                              (MIMatchOk encodedOut) Nhead Ntail
                              (encASTList?_some_normal ps encodedPs hps)
                              (encASTList?_some_normal ts encodedTs hts)
                              hheadEval hheadActive htailEval htailActive htailNorm

  theorem miMatchList_source_none_first_result :
      ∀ (pats terms : List AST)
        (encodedPats encodedTerms encodedBs : AST)
        (bs : List (String × AST)),
        encASTList? pats = some encodedPats →
        encASTList? terms = some encodedTerms →
        encBinds? bs = some encodedBs →
        AST.matchPatList pats terms bs = none →
        ∃ N,
          eval pMI N (miMatchList encodedPats encodedTerms encodedBs) =
            MIMatchFail ∧
          (∀ k, k < N →
            MatchActiveShape
              (eval pMI k (miMatchList encodedPats encodedTerms encodedBs))) ∧
          IsNormal pMI MIMatchFail
    | [], terms, encodedPats, encodedTerms, encodedBs, bs,
        hpats, hterms, hbs, hmatch => by
        simp only [encASTList?] at hpats
        cases hpats
        exact miMatchList_nil_source_none_first_result terms encodedTerms
          encodedBs bs hterms hbs hmatch
    | p :: ps, [], encodedPats, _, encodedBs, bs,
        hpats, _hterms, hbs, hmatch => by
        simp only [encASTList?] at _hterms
        cases _hterms
        exact miMatchList_cons_source_nil_first_result (p :: ps)
          encodedPats encodedBs bs hpats hbs hmatch
    | p :: ps, t :: ts, encodedPats, encodedTerms, encodedBs, bs,
        hpats, hterms, hbs, hmatch => by
        simp only [encASTList?] at hpats hterms
        cases hp : encAST? p with
        | none =>
            simp [hp] at hpats
        | some encodedP =>
            cases hps : encASTList? ps with
            | none =>
                simp [hp, hps] at hpats
            | some encodedPs =>
                simp [hp, hps] at hpats
                cases hpats
                cases ht : encAST? t with
                | none =>
                    simp [ht] at hterms
                | some encodedT =>
                    cases hts : encASTList? ts with
                    | none =>
                        simp [ht, hts] at hterms
                    | some encodedTs =>
                        simp [ht, hts] at hterms
                        cases hterms
                        cases hhead : AST.matchPat p t bs with
                        | none =>
                            simp only [AST.matchPatList, hhead, Option.bind_none] at hmatch
                            obtain ⟨Nhead, hheadEval, hheadActive, _⟩ :=
                              miMatch_source_none_first_result p t encodedP encodedT
                                encodedBs bs hp ht hbs hhead
                            exact miMatchList_cons_first_result_of_match_fail encodedP
                              encodedPs encodedT encodedTs encodedBs Nhead
                              (encASTList?_some_normal ps encodedPs hps)
                              (encASTList?_some_normal ts encodedTs hts)
                              hheadEval hheadActive
                        | some bsMid =>
                            simp only [AST.matchPatList, hhead, Option.bind_some] at hmatch
                            obtain ⟨encodedMid, hmid⟩ :=
                              matchPat_preserves_encBinds? p t encodedP encodedT encodedBs
                                bs bsMid hp ht hbs hhead
                            obtain ⟨Nhead, hheadEval, hheadActive, _hheadNorm⟩ :=
                              miMatch_source_some_first_result p t encodedP encodedT
                                encodedBs encodedMid bs bsMid hp ht hbs hhead hmid
                            obtain ⟨Ntail, htailEval, htailActive, htailNorm⟩ :=
                              miMatchList_source_none_first_result ps ts encodedPs
                                encodedTs encodedMid bsMid hps hts hmid hmatch
                            exact miMatchList_cons_first_result_of_match_ok encodedP
                              encodedPs encodedT encodedTs encodedBs encodedMid
                              MIMatchFail Nhead Ntail
                              (encASTList?_some_normal ps encodedPs hps)
                              (encASTList?_some_normal ts encodedTs hts)
                              hheadEval hheadActive htailEval htailActive htailNorm
end

theorem os_miSubst_var_named (v : String) (bs : AST) :
    oneStep pMI (miSubst bs (MIVar v)) =
      some (miSubstVarK (MIVar v) (miLookup (con0 v) bs)) := by
  rfl

theorem os_miSubstVarK_some (orig t : AST) :
    oneStep pMI (miSubstVarK orig (MISome t)) = some t := by
  rfl

theorem os_miSubstVarK_none (orig : AST) :
    oneStep pMI (miSubstVarK orig MINone) = some orig := by
  rfl

theorem base_miSubstVarK_lookup_arg_raw (orig : AST) (v : String) (tail : AST) :
    baseReducts pMI
      (.sexp (.id "mi-subst-varK") [orig, miLookup (con0 v) tail]) = [] := by
  rfl

theorem os_miSubstVarK_lookup_nil_arg (orig : AST) (v : String)
    (horig : IsNormal pMI orig) :
    oneStep pMI (miSubstVarK orig (miLookup (con0 v) MIBNil)) =
      some (miSubstVarK orig MINone) := by
  rw [oneStep.eq_def]
  simp only [miSubstVarK, app]
  rw [base_miSubstVarK_lookup_arg_raw]
  simp only [IsNormal] at horig
  simp only [oneStepList, horig, os_miLookup_nil_data]
  rfl

theorem os_miSubstVarK_lookup_hit_arg (orig : AST) (v : String) (old rest : AST)
    (horig : IsNormal pMI orig) :
    oneStep pMI
        (miSubstVarK orig (miLookup (con0 v) (MIBCons (con0 v) old rest))) =
      some (miSubstVarK orig (MISome old)) := by
  rw [oneStep.eq_def]
  simp only [miSubstVarK, app]
  rw [base_miSubstVarK_lookup_arg_raw]
  simp only [IsNormal] at horig
  simp only [oneStepList, horig, os_miLookup_hit_named]
  rfl

theorem os_miSubstVarK_lookup_miss_arg (orig : AST) (v w : String) (old rest : AST)
    (hvw : (v == w) = false) (horig : IsNormal pMI orig) :
    oneStep pMI
        (miSubstVarK orig (miLookup (con0 v) (MIBCons (con0 w) old rest))) =
      some (miSubstVarK orig (miLookup (con0 v) rest)) := by
  rw [oneStep.eq_def]
  simp only [miSubstVarK, app]
  rw [base_miSubstVarK_lookup_arg_raw]
  simp only [IsNormal] at horig
  simp only [oneStepList, horig, os_miLookup_miss_named, hvw]
  rfl

theorem miSubstVarK_lookup_encBinds_eval (v : String) (orig : AST)
    (horig : IsNormal pMI orig) :
    ∀ (bs : List (String × AST)) (encodedBs : AST),
      encBinds? bs = some encodedBs →
      eval pMI (bs.length + 2)
          (miSubstVarK orig (miLookup (con0 v) encodedBs)) =
        match lookupEncoded? v bs with
        | some encodedTerm => encodedTerm
        | none => orig
  | [], encodedBs, henc => by
      simp only [encBinds?] at henc
      cases henc
      simp only [lookupEncoded?, List.length_nil, eval,
        os_miSubstVarK_lookup_nil_arg, os_miSubstVarK_none, horig]
  | (w, t) :: rest, encodedBs, henc => by
      simp only [encBinds?] at henc
      cases ht : encAST? t with
      | none =>
          simp [ht] at henc
      | some encodedTerm =>
          cases hrest : encBinds? rest with
          | none =>
              simp [ht, hrest] at henc
          | some encodedRest =>
              simp [ht, hrest] at henc
              cases henc
              by_cases hvw : (v == w) = true
              · have hvw_eq : v = w := beq_iff_eq.mp hvw
                subst w
                have hvv : (v == v) = true := string_beq_self_mi v
                have hterm : IsNormal pMI encodedTerm :=
                  encAST?_some_normal t encodedTerm ht
                simp only [lookupEncoded?, hvv, ht, List.length_cons, eval,
                  os_miSubstVarK_lookup_hit_arg, horig]
                simp only [os_miSubstVarK_some]
                simpa [eval] using
                  eval_fixed_of_normal pMI encodedTerm hterm rest.length
              · have hvw_false : (v == w) = false := by
                  cases hcmp : (v == w) <;> simp [hcmp] at hvw ⊢
                have ih := miSubstVarK_lookup_encBinds_eval v orig horig rest encodedRest hrest
                simpa [lookupEncoded?, hvw_false, List.length_cons, eval,
                  os_miSubstVarK_lookup_miss_arg, horig, Bool.false_eq_true,
                  if_false] using ih

theorem miSubst_var_encodedBinds_sim (v : String) (encodedBs : AST) :
    ∀ (bs : List (String × AST)),
      encBinds? bs = some encodedBs →
      eval pMI (bs.length + 3) (miSubst encodedBs (MIVar v)) =
        match lookupEncoded? v bs with
        | some encodedTerm => encodedTerm
        | none => MIVar v
  | bs, henc => by
      simp only [eval, os_miSubst_var_named]
      exact miSubstVarK_lookup_encBinds_eval v (MIVar v) (normal_MIVar v) bs encodedBs henc

theorem os_miSubst_sym_named (s : String) (bs : AST) :
    oneStep pMI (miSubst bs (MISym s)) = some (MISym s) := by
  rfl

theorem miSubst_sym_named_sim (s : String) (encodedBs : AST) :
    eval pMI 1 (miSubst encodedBs (MISym s)) = MISym s := by
  simp only [eval, os_miSubst_sym_named]

theorem os_miSubst_app_named (h : String) (args bs : AST) :
    oneStep pMI (miSubst bs (MIApp h args)) =
      some (MIApp h (miSubstList bs args)) := by
  rfl

theorem miSubst_app_dispatch_eval (h : String) (args bs : AST) :
    eval pMI 1 (miSubst bs (MIApp h args)) =
      MIApp h (miSubstList bs args) := by
  simp only [eval, os_miSubst_app_named]

theorem os_miSubstList_nil (bs : AST) :
    oneStep pMI (miSubstList bs MINil) = some MINil := by
  rfl

theorem miSubstList_nil_sim (bs : AST) :
    eval pMI 1 (miSubstList bs MINil) = MINil := by
  simp only [eval, os_miSubstList_nil]

theorem os_miSubstList_cons (bs x xs : AST) :
    oneStep pMI (miSubstList bs (MICons x xs)) =
      some (MICons (miSubst bs x) (miSubstList bs xs)) := by
  rfl

theorem miSubstList_cons_dispatch_eval (bs x xs : AST) :
    eval pMI 1 (miSubstList bs (MICons x xs)) =
      MICons (miSubst bs x) (miSubstList bs xs) := by
  simp only [eval, os_miSubstList_cons]

theorem os_MIApp_substList_nil_arg (h : String) (bs : AST) :
    oneStep pMI (MIApp h (miSubstList bs MINil)) = some (MIApp h MINil) := by
  have hh : IsNormal pMI (con0 h) := normal_con0 h
  simp only [IsNormal] at hh
  rw [oneStep.eq_def]
  simp only [MIApp, app]
  rw [baseReducts_MIApp_pMI_raw]
  simp only [oneStepList, hh, os_miSubstList_nil]
  rfl

theorem miSubst_app_nil_args_sim (h : String) (bs : AST) :
    eval pMI 2 (miSubst bs (MIApp h MINil)) = MIApp h MINil := by
  simp only [eval, os_miSubst_app_named, os_MIApp_substList_nil_arg]

theorem eval_trans_mi (a b : Nat) (t u w : AST) :
    eval pMI a t = u → eval pMI b u = w → eval pMI (a + b) t = w := by
  exact Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pMI a b t u w

theorem eval_add_eq_eval_mi (a b : Nat) (t u : AST)
    (h : eval pMI a t = u) :
    eval pMI (a + b) t = eval pMI b u := by
  exact eval_trans_mi a b t u (eval pMI b u) h rfl

theorem match_active_append_mi (a b : Nat) {start mid : AST}
    (hprefix : eval pMI a start = mid)
    (hfirst : ∀ k, k < a → MatchActiveShape (eval pMI k start))
    (hsecond : ∀ k, k < b → MatchActiveShape (eval pMI k mid)) :
    ∀ k, k < a + b → MatchActiveShape (eval pMI k start) := by
  intro k hk
  by_cases hklt : k < a
  · exact hfirst k hklt
  · have _hle : a ≤ k := Nat.le_of_not_gt hklt
    let j := k - a
    have hkj : k = a + j := by omega
    have hj : j < b := by omega
    have heval : eval pMI k start = eval pMI j mid := by
      rw [hkj]
      exact eval_add_eq_eval_mi a j start mid hprefix
    rw [heval]
    exact hsecond j hj

theorem miMatchList_cons_tail_active_result_of_match_ok
    (p ps t rawTs encodedTs bs bs2 out : AST)
    (rawTailFuel headFuel tailFuel : Nat)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI encodedTs)
    (hrawTail : eval pMI rawTailFuel rawTs = encodedTs)
    (hhead : eval pMI headFuel (miMatch p t bs) = MIMatchOk bs2)
    (hheadActive : ∀ k, k < headFuel →
      MatchActiveShape (eval pMI k (miMatch p t bs)))
    (htail : eval pMI tailFuel (miMatchList ps encodedTs bs2) = out)
    (htailActive : ∀ k, k < tailFuel →
      MatchActiveShape (eval pMI k (miMatchList ps encodedTs bs2))) :
    ∃ N,
      eval pMI N (miMatchList (MICons p ps) (MICons t rawTs) bs) = out ∧
      (∀ k, k < N →
        MatchActiveShape
          (eval pMI k (miMatchList (MICons p ps) (MICons t rawTs) bs))) := by
  let r : AST := miMatch p t bs
  let Kraw : AST := miMatchListK ps rawTs r
  let Kenc : AST := miMatchListK ps encodedTs r
  have hdispatch :
      eval pMI 1 (miMatchList (MICons p ps) (MICons t rawTs) bs) =
        Kraw := by
    simp only [Kraw, r, eval, os_miMatchList_cons_ok]
  obtain ⟨tailCtxFuel, htailCtx, htailCtxActive⟩ :=
    miMatchListK_tail_active_eval_of ps rawTs encodedTs r
      rawTailFuel hps (MatchActiveShape.match p t bs) hrawTail hts
  have hpre1 := eval_trans_mi 1 tailCtxFuel
    (miMatchList (MICons p ps) (MICons t rawTs) bs)
    Kraw Kenc hdispatch (by simpa [Kraw, Kenc] using htailCtx)
  have hpre1Active :
      ∀ k, k < 1 + tailCtxFuel →
        MatchActiveShape
          (eval pMI k (miMatchList (MICons p ps) (MICons t rawTs) bs)) := by
    apply match_active_append_mi 1 tailCtxFuel hdispatch
    · exact match_active_fuel_one_mi
        (MatchActiveShape.matchList (MICons p ps) (MICons t rawTs) bs)
    · simpa [Kraw] using htailCtxActive
  let F : AST → AST := fun z => miMatchListK ps encodedTs z
  obtain ⟨headCtxFuel, hheadCtx, hheadCtxActive⟩ :=
    cong_eval_match_active_with_guard_mi F
      (fun s hs => MatchActiveShape.matchListK ps encodedTs s)
      (fun s s' hactive hstep =>
        os_miMatchListK_active_step ps encodedTs s s' hps hts
          hactive hstep)
      headFuel hhead hheadActive
  have hpre2 := eval_trans_mi (1 + tailCtxFuel) headCtxFuel
    (miMatchList (MICons p ps) (MICons t rawTs) bs)
    Kenc (F (MIMatchOk bs2))
    hpre1 (by simpa [F, Kenc, r] using hheadCtx)
  have hpre2Active :
      ∀ k, k < (1 + tailCtxFuel) + headCtxFuel →
        MatchActiveShape
          (eval pMI k (miMatchList (MICons p ps) (MICons t rawTs) bs)) := by
    apply match_active_append_mi (1 + tailCtxFuel) headCtxFuel
      hpre1 hpre1Active
    simpa [F, Kenc, r] using hheadCtxActive
  have hok : eval pMI 1 (F (MIMatchOk bs2)) =
      miMatchList ps encodedTs bs2 := by
    simp only [F, eval, os_miMatchListK_ok]
  have hpre3 := eval_trans_mi ((1 + tailCtxFuel) + headCtxFuel) 1
    (miMatchList (MICons p ps) (MICons t rawTs) bs)
    (F (MIMatchOk bs2))
    (miMatchList ps encodedTs bs2)
    hpre2 hok
  have hpre3Active :
      ∀ k, k < ((1 + tailCtxFuel) + headCtxFuel) + 1 →
        MatchActiveShape
          (eval pMI k (miMatchList (MICons p ps) (MICons t rawTs) bs)) := by
    apply match_active_append_mi ((1 + tailCtxFuel) + headCtxFuel) 1
      hpre2 hpre2Active
    exact match_active_fuel_one_mi
      (MatchActiveShape.matchListK ps encodedTs (MIMatchOk bs2))
  have htotal := eval_trans_mi (((1 + tailCtxFuel) + headCtxFuel) + 1)
    tailFuel
    (miMatchList (MICons p ps) (MICons t rawTs) bs)
    (miMatchList ps encodedTs bs2)
    out hpre3 htail
  refine ⟨(((1 + tailCtxFuel) + headCtxFuel) + 1) + tailFuel,
    htotal, ?_⟩
  apply match_active_append_mi (((1 + tailCtxFuel) + headCtxFuel) + 1)
    tailFuel hpre3 hpre3Active htailActive

theorem miMatchList_cons_tail_first_result_of_match_fail
    (p ps t rawTs encodedTs bs : AST)
    (rawTailFuel headFuel : Nat)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI encodedTs)
    (hrawTail : eval pMI rawTailFuel rawTs = encodedTs)
    (hhead : eval pMI headFuel (miMatch p t bs) = MIMatchFail)
    (hheadActive : ∀ k, k < headFuel →
      MatchActiveShape (eval pMI k (miMatch p t bs))) :
    ∃ N,
      eval pMI N (miMatchList (MICons p ps) (MICons t rawTs) bs) =
        MIMatchFail ∧
      (∀ k, k < N →
        MatchActiveShape
          (eval pMI k (miMatchList (MICons p ps) (MICons t rawTs) bs))) ∧
      IsNormal pMI MIMatchFail := by
  let r : AST := miMatch p t bs
  let Kraw : AST := miMatchListK ps rawTs r
  let Kenc : AST := miMatchListK ps encodedTs r
  have hdispatch :
      eval pMI 1 (miMatchList (MICons p ps) (MICons t rawTs) bs) =
        Kraw := by
    simp only [Kraw, r, eval, os_miMatchList_cons_ok]
  obtain ⟨tailCtxFuel, htailCtx, htailCtxActive⟩ :=
    miMatchListK_tail_active_eval_of ps rawTs encodedTs r
      rawTailFuel hps (MatchActiveShape.match p t bs) hrawTail hts
  have hpre1 := eval_trans_mi 1 tailCtxFuel
    (miMatchList (MICons p ps) (MICons t rawTs) bs)
    Kraw Kenc hdispatch (by simpa [Kraw, Kenc] using htailCtx)
  have hpre1Active :
      ∀ k, k < 1 + tailCtxFuel →
        MatchActiveShape
          (eval pMI k (miMatchList (MICons p ps) (MICons t rawTs) bs)) := by
    apply match_active_append_mi 1 tailCtxFuel hdispatch
    · exact match_active_fuel_one_mi
        (MatchActiveShape.matchList (MICons p ps) (MICons t rawTs) bs)
    · simpa [Kraw] using htailCtxActive
  let F : AST → AST := fun z => miMatchListK ps encodedTs z
  obtain ⟨headCtxFuel, hheadCtx, hheadCtxActive⟩ :=
    cong_eval_match_active_with_guard_mi F
      (fun s hs => MatchActiveShape.matchListK ps encodedTs s)
      (fun s s' hactive hstep =>
        os_miMatchListK_active_step ps encodedTs s s' hps hts
          hactive hstep)
      headFuel hhead hheadActive
  have hpre2 := eval_trans_mi (1 + tailCtxFuel) headCtxFuel
    (miMatchList (MICons p ps) (MICons t rawTs) bs)
    Kenc (F MIMatchFail)
    hpre1 (by simpa [F, Kenc, r] using hheadCtx)
  have hpre2Active :
      ∀ k, k < (1 + tailCtxFuel) + headCtxFuel →
        MatchActiveShape
          (eval pMI k (miMatchList (MICons p ps) (MICons t rawTs) bs)) := by
    apply match_active_append_mi (1 + tailCtxFuel) headCtxFuel
      hpre1 hpre1Active
    simpa [F, Kenc, r] using hheadCtxActive
  have hfail : eval pMI 1 (F MIMatchFail) = MIMatchFail := by
    simp only [F, eval, os_miMatchListK_fail]
  have htotal := eval_trans_mi ((1 + tailCtxFuel) + headCtxFuel) 1
    (miMatchList (MICons p ps) (MICons t rawTs) bs)
    (F MIMatchFail) MIMatchFail hpre2 hfail
  refine ⟨((1 + tailCtxFuel) + headCtxFuel) + 1, htotal, ?_,
    normal_MIMatchFail⟩
  apply match_active_append_mi ((1 + tailCtxFuel) + headCtxFuel) 1
    hpre2 hpre2Active
  exact match_active_fuel_one_mi
    (MatchActiveShape.matchListK ps encodedTs MIMatchFail)

theorem eval_stable_mi {t : AST} (h : IsNormal pMI t) :
    ∀ N, eval pMI N t = t
  | 0 => rfl
  | n + 1 => by
      simp only [IsNormal] at h
      simp only [eval, h]

theorem eval_normal_unique_mi {s u v : AST} {N M : Nat}
    (hN : eval pMI N s = u) (hu : IsNormal pMI u)
    (hM : eval pMI M s = v) (hv : IsNormal pMI v) : u = v := by
  by_cases hle : N ≤ M
  · have hdecomp : M = N + (M - N) := by omega
    have hstable : eval pMI (M - N) u = u :=
      eval_stable_mi hu (M - N)
    have hM' : eval pMI M s = u := by
      rw [hdecomp]
      exact eval_trans_mi N (M - N) s u u hN hstable
    rw [hM'] at hM
    exact hM
  · have hle' : M ≤ N := Nat.le_of_not_ge hle
    have hdecomp : N = M + (N - M) := by omega
    have hstable : eval pMI (N - M) v = v :=
      eval_stable_mi hv (N - M)
    have hN' : eval pMI N s = v := by
      rw [hdecomp]
      exact eval_trans_mi M (N - M) s v v hM hstable
    rw [hN'] at hN
    exact hN.symm

theorem cong_eval_mi (F : AST → AST)
    (hcong : ∀ s s', oneStep pMI s = some s' → oneStep pMI (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pMI N s = v → IsNormal pMI v →
      ∃ M, eval pMI M (F s) = F v := by
  intro N
  induction N with
  | zero =>
      intro s v hs _
      simp only [eval] at hs
      subst hs
      exact ⟨0, rfl⟩
  | succ n ih =>
      intro s v hs hv
      simp only [eval] at hs
      cases hstep : oneStep pMI s with
      | none =>
          rw [hstep] at hs
          subst hs
          exact ⟨0, rfl⟩
      | some s' =>
          rw [hstep] at hs
          obtain ⟨M, hM⟩ := ih hs hv
          refine ⟨M + 1, ?_⟩
          simp only [eval, hcong s s' hstep]
          exact hM

theorem os_MICons_head_step (x x' xs : AST)
    (hstep : oneStep pMI x = some x') :
    oneStep pMI (MICons x xs) = some (MICons x' xs) := by
  rw [oneStep.eq_def]
  simp only [MICons, app]
  rw [baseReducts_MICons_pMI_raw]
  simp only [oneStepList, hstep, Option.map_some]

theorem os_MICons_tail_step (x xs xs' : AST)
    (hx : IsNormal pMI x) (hstep : oneStep pMI xs = some xs') :
    oneStep pMI (MICons x xs) = some (MICons x xs') := by
  rw [oneStep.eq_def]
  simp only [MICons, app]
  rw [baseReducts_MICons_pMI_raw]
  simp only [IsNormal] at hx
  simp only [oneStepList, hx, hstep, Option.map_some]

theorem os_MIBCons_term_step (v t t' rest : AST)
    (hv : IsNormal pMI v) (hstep : oneStep pMI t = some t') :
    oneStep pMI (MIBCons v t rest) = some (MIBCons v t' rest) := by
  rw [oneStep.eq_def]
  simp only [MIBCons, app]
  rw [baseReducts_MIBCons_pMI_raw]
  simp only [IsNormal] at hv
  simp only [oneStepList, hv, hstep, Option.map_some]

theorem os_MIBCons_rest_step (v t rest rest' : AST)
    (hv : IsNormal pMI v) (ht : IsNormal pMI t)
    (hstep : oneStep pMI rest = some rest') :
    oneStep pMI (MIBCons v t rest) = some (MIBCons v t rest') := by
  rw [oneStep.eq_def]
  simp only [MIBCons, app]
  rw [baseReducts_MIBCons_pMI_raw]
  simp only [IsNormal] at hv ht
  simp only [oneStepList, hv, ht, hstep, Option.map_some]

theorem normal_MIBCons_term {v t rest : AST}
    (hcons : IsNormal pMI (MIBCons v t rest)) :
    IsNormal pMI t := by
  simp only [IsNormal] at hcons ⊢
  cases ht : oneStep pMI t with
  | none => rfl
  | some t' =>
      have hv : IsNormal pMI v := by
        simp only [IsNormal]
        cases hvStep : oneStep pMI v with
        | none => rfl
        | some v' =>
            rw [oneStep.eq_def] at hcons
            simp only [MIBCons, app] at hcons
            rw [baseReducts_MIBCons_pMI_raw] at hcons
            simp only [oneStepList, hvStep, Option.map_some] at hcons
            cases hcons
      have hstep := os_MIBCons_term_step v t t' rest hv ht
      rw [hcons] at hstep
      cases hstep

theorem normal_MIBCons_rest {v t rest : AST}
    (hcons : IsNormal pMI (MIBCons v t rest)) :
    IsNormal pMI rest := by
  simp only [IsNormal] at hcons ⊢
  cases hrest : oneStep pMI rest with
  | none => rfl
  | some rest' =>
      have hv : IsNormal pMI v := by
        simp only [IsNormal]
        cases hvStep : oneStep pMI v with
        | none => rfl
        | some v' =>
            rw [oneStep.eq_def] at hcons
            simp only [MIBCons, app] at hcons
            rw [baseReducts_MIBCons_pMI_raw] at hcons
            simp only [oneStepList, hvStep, Option.map_some] at hcons
            cases hcons
      have ht : IsNormal pMI t := normal_MIBCons_term (by
        simp only [IsNormal]
        exact hcons)
      have hstep := os_MIBCons_rest_step v t rest rest' hv ht hrest
      rw [hcons] at hstep
      cases hstep

theorem os_MIApp_args_step (h : String) (args args' : AST)
    (hstep : oneStep pMI args = some args') :
    oneStep pMI (MIApp h args) = some (MIApp h args') := by
  have hname : IsNormal pMI (con0 h) := normal_con0 h
  rw [oneStep.eq_def]
  simp only [MIApp, app]
  rw [baseReducts_MIApp_pMI_raw]
  simp only [IsNormal] at hname
  simp only [oneStepList, hname, hstep, Option.map_some]

theorem normal_MICons_head {x xs : AST}
    (hcons : IsNormal pMI (MICons x xs)) :
    IsNormal pMI x := by
  simp only [IsNormal] at hcons ⊢
  cases hx : oneStep pMI x with
  | none => rfl
  | some x' =>
      have hstep := os_MICons_head_step x x' xs hx
      rw [hcons] at hstep
      cases hstep

theorem normal_MICons_tail {x xs : AST}
    (hcons : IsNormal pMI (MICons x xs)) :
    IsNormal pMI xs := by
  simp only [IsNormal] at hcons ⊢
  cases hxs : oneStep pMI xs with
  | none => rfl
  | some xs' =>
      have hx : IsNormal pMI x := normal_MICons_head hcons
      have hstep := os_MICons_tail_step x xs xs' hx hxs
      rw [hcons] at hstep
      cases hstep

theorem normal_MIApp_args {h : String} {args : AST}
    (happ : IsNormal pMI (MIApp h args)) :
    IsNormal pMI args := by
  simp only [IsNormal] at happ ⊢
  cases hargs : oneStep pMI args with
  | none => rfl
  | some args' =>
      have hstep := os_MIApp_args_step h args args' hargs
      rw [happ] at hstep
      cases hstep

theorem miCons_head_eval_of (x x' xs : AST) (fuel : Nat)
    (hhead : eval pMI fuel x = x')
    (hx' : IsNormal pMI x') :
    ∃ N, eval pMI N (MICons x xs) = MICons x' xs := by
  exact cong_eval_mi (fun z => MICons z xs)
    (fun s s' hstep => os_MICons_head_step s s' xs hstep)
    fuel hhead hx'

theorem miCons_tail_eval_of (x xs xs' : AST) (fuel : Nat)
    (hx : IsNormal pMI x)
    (htail : eval pMI fuel xs = xs')
    (hxs' : IsNormal pMI xs') :
    ∃ N, eval pMI N (MICons x xs) = MICons x xs' := by
  exact cong_eval_mi (fun z => MICons x z)
    (fun s s' hstep => os_MICons_tail_step x s s' hx hstep)
    fuel htail hxs'

theorem miBCons_term_eval_of (v t t' rest : AST) (fuel : Nat)
    (hv : IsNormal pMI v)
    (hterm : eval pMI fuel t = t')
    (ht' : IsNormal pMI t') :
    ∃ N, eval pMI N (MIBCons v t rest) = MIBCons v t' rest := by
  exact cong_eval_mi (fun z => MIBCons v z rest)
    (fun s s' hstep => os_MIBCons_term_step v s s' rest hv hstep)
    fuel hterm ht'

theorem miBCons_rest_eval_of (v t rest rest' : AST) (fuel : Nat)
    (hv : IsNormal pMI v) (ht : IsNormal pMI t)
    (hrest : eval pMI fuel rest = rest')
    (hrest' : IsNormal pMI rest') :
    ∃ N, eval pMI N (MIBCons v t rest) = MIBCons v t rest' := by
  exact cong_eval_mi (fun z => MIBCons v t z)
    (fun s s' hstep => os_MIBCons_rest_step v t s s' hv ht hstep)
    fuel hrest hrest'

theorem miBCons_eval_of (v rawTerm encodedTerm rawRest encodedRest : AST)
    (termFuel restFuel : Nat)
    (hv : IsNormal pMI v)
    (hterm : eval pMI termFuel rawTerm = encodedTerm)
    (htermNorm : IsNormal pMI encodedTerm)
    (hrest : eval pMI restFuel rawRest = encodedRest)
    (hrestNorm : IsNormal pMI encodedRest) :
    ∃ N,
      eval pMI N (MIBCons v rawTerm rawRest) =
        MIBCons v encodedTerm encodedRest := by
  obtain ⟨Mterm, htermCtx⟩ :=
    miBCons_term_eval_of v rawTerm encodedTerm rawRest termFuel hv
      hterm htermNorm
  obtain ⟨Mrest, hrestCtx⟩ :=
    miBCons_rest_eval_of v encodedTerm rawRest encodedRest restFuel hv
      htermNorm hrest hrestNorm
  have htotal := eval_trans_mi Mterm Mrest
    (MIBCons v rawTerm rawRest)
    (MIBCons v encodedTerm rawRest)
    (MIBCons v encodedTerm encodedRest)
    htermCtx hrestCtx
  exact ⟨Mterm + Mrest, htotal⟩

theorem miApp_args_eval_of (h : String) (args args' : AST) (fuel : Nat)
    (hargs : eval pMI fuel args = args')
    (hargs' : IsNormal pMI args') :
    ∃ N, eval pMI N (MIApp h args) = MIApp h args' := by
  exact cong_eval_mi (fun z => MIApp h z)
    (fun s s' hstep => os_MIApp_args_step h s s' hstep)
    fuel hargs hargs'

theorem miSubstList_cons_eval_of (bs x xs headOut tailOut : AST)
    (headFuel tailFuel : Nat)
    (hhead : eval pMI headFuel (miSubst bs x) = headOut)
    (hheadNorm : IsNormal pMI headOut)
    (htail : eval pMI tailFuel (miSubstList bs xs) = tailOut)
    (htailNorm : IsNormal pMI tailOut) :
    ∃ N, eval pMI N (miSubstList bs (MICons x xs)) = MICons headOut tailOut := by
  have hdispatch :
      eval pMI 1 (miSubstList bs (MICons x xs)) =
        MICons (miSubst bs x) (miSubstList bs xs) :=
    miSubstList_cons_dispatch_eval bs x xs
  obtain ⟨Mhead, hheadCtx⟩ :=
    cong_eval_mi (fun z => MICons z (miSubstList bs xs))
      (fun s s' hstep => os_MICons_head_step s s' (miSubstList bs xs) hstep)
      headFuel hhead hheadNorm
  obtain ⟨Mtail, htailCtx⟩ :=
    cong_eval_mi (fun z => MICons headOut z)
      (fun s s' hstep => os_MICons_tail_step headOut s s' hheadNorm hstep)
      tailFuel htail htailNorm
  have hpre := eval_trans_mi 1 Mhead
    (miSubstList bs (MICons x xs))
    (MICons (miSubst bs x) (miSubstList bs xs))
    (MICons headOut (miSubstList bs xs))
    hdispatch hheadCtx
  have htotal := eval_trans_mi (1 + Mhead) Mtail
    (miSubstList bs (MICons x xs))
    (MICons headOut (miSubstList bs xs))
    (MICons headOut tailOut)
    hpre htailCtx
  exact ⟨(1 + Mhead) + Mtail, htotal⟩

theorem miSubst_app_eval_of (h : String) (bs args argsOut : AST)
    (argFuel : Nat)
    (hargs : eval pMI argFuel (miSubstList bs args) = argsOut)
    (hargsNorm : IsNormal pMI argsOut) :
    ∃ N, eval pMI N (miSubst bs (MIApp h args)) = MIApp h argsOut := by
  have hdispatch :
      eval pMI 1 (miSubst bs (MIApp h args)) =
        MIApp h (miSubstList bs args) :=
    miSubst_app_dispatch_eval h args bs
  obtain ⟨Margs, hargsCtx⟩ :=
    cong_eval_mi (fun z => MIApp h z)
      (fun s s' hstep => os_MIApp_args_step h s s' hstep)
      argFuel hargs hargsNorm
  have htotal := eval_trans_mi 1 Margs
    (miSubst bs (MIApp h args))
    (MIApp h (miSubstList bs args))
    (MIApp h argsOut)
    hdispatch hargsCtx
  exact ⟨1 + Margs, htotal⟩

mutual
  theorem miSubst_encAST_inst_eval :
      ∀ (term encodedTerm : AST),
        encAST? term = some encodedTerm →
        ∀ (bs : List (String × AST)) (encodedBs : AST),
          encBinds? bs = some encodedBs →
          ∃ (encodedOut : AST) (N : Nat),
            encAST? (AST.inst bs term) = some encodedOut ∧
            eval pMI N (miSubst encodedBs encodedTerm) = encodedOut ∧
            IsNormal pMI encodedOut
    | .var (.base v), encodedTerm, henc => by
        cases henc
        intro bs encodedBs hbs
        let out : AST :=
          match lookupEncoded? v bs with
          | some encodedTerm => encodedTerm
          | none => MIVar v
        have hout : encAST? (AST.inst bs (.var (.base v))) = some out := by
          simpa only [out] using encAST?_inst_var_lookupEncoded v bs encodedBs hbs
        refine ⟨out, bs.length + 3, hout, ?_, ?_⟩
        · simpa only [out] using miSubst_var_encodedBinds_sim v encodedBs bs hbs
        · exact encAST?_some_normal (AST.inst bs (.var (.base v))) out hout
    | .var (.qualified _ _), _, henc => by
        cases henc
    | .sexp (.id s) [], encodedTerm, henc => by
        cases henc
        intro bs encodedBs hbs
        refine ⟨MISym s, 1, ?_, ?_, normal_MISym s⟩
        · rfl
        · exact miSubst_sym_named_sim s encodedBs
    | .sexp (.id s) (a :: args), encodedTerm, henc => by
        simp only [encAST?] at henc
        cases hargs : encASTList? (a :: args) with
        | none =>
            simp [hargs] at henc
        | some encodedArgs =>
            simp [hargs] at henc
            cases henc
            intro bs encodedBs hbs
            obtain ⟨argsOut, argFuel, hargsOut, hargsEval, hargsNorm⟩ :=
              miSubstList_encASTList_inst_eval (a :: args) encodedArgs hargs
                bs encodedBs hbs
            obtain ⟨N, hN⟩ :=
              miSubst_app_eval_of s encodedBs encodedArgs argsOut
                argFuel hargsEval hargsNorm
            refine ⟨MIApp s argsOut, N, ?_, hN, normal_MIApp s argsOut hargsNorm⟩
            have hargsOut' :
                encASTList? (AST.inst bs a :: AST.instList bs args) = some argsOut := by
              simpa only [AST.instList] using hargsOut
            simp only [AST.inst, AST.instList, encAST?, hargsOut']
    | .sexp .wild _, _, henc => by
        cases henc
    | .sexp (.listE _) _, _, henc => by
        cases henc
    | .sexp (.listCons _) _, _, henc => by
        cases henc
    | .sexp (.listOne _) _, _, henc => by
        cases henc
    | .subst _ _ _, _, henc => by
        cases henc

  theorem miSubstList_encASTList_inst_eval :
      ∀ (terms : List AST) (encodedTerms : AST),
        encASTList? terms = some encodedTerms →
        ∀ (bs : List (String × AST)) (encodedBs : AST),
          encBinds? bs = some encodedBs →
          ∃ (encodedOut : AST) (N : Nat),
            encASTList? (AST.instList bs terms) = some encodedOut ∧
            eval pMI N (miSubstList encodedBs encodedTerms) = encodedOut ∧
            IsNormal pMI encodedOut
    | [], encodedTerms, henc => by
        cases henc
        intro bs encodedBs hbs
        refine ⟨MINil, 1, ?_, ?_, normal_MINil⟩
        · rfl
        · exact miSubstList_nil_sim encodedBs
    | t :: ts, encodedTerms, henc => by
        simp only [encASTList?] at henc
        cases ht : encAST? t with
        | none =>
            simp [ht] at henc
        | some encodedT =>
            cases hts : encASTList? ts with
            | none =>
                simp [ht, hts] at henc
            | some encodedTs =>
                simp [ht, hts] at henc
                cases henc
                intro bs encodedBs hbs
                obtain ⟨headOut, headFuel, hheadOut, hheadEval, hheadNorm⟩ :=
                  miSubst_encAST_inst_eval t encodedT ht bs encodedBs hbs
                obtain ⟨tailOut, tailFuel, htailOut, htailEval, htailNorm⟩ :=
                  miSubstList_encASTList_inst_eval ts encodedTs hts bs encodedBs hbs
                obtain ⟨N, hN⟩ :=
                  miSubstList_cons_eval_of encodedBs encodedT encodedTs
                    headOut tailOut headFuel tailFuel
                    hheadEval hheadNorm htailEval htailNorm
                refine ⟨MICons headOut tailOut, N, ?_, hN,
                  normal_MICons headOut tailOut hheadNorm htailNorm⟩
                simp only [AST.instList, encASTList?, hheadOut, htailOut]
end

/-! ## Root and step dispatch facts for the simulation frontier -/

theorem os_miRootTable_nil (term : AST) :
    oneStep pMI (miRootTable MIRNil term) = some MINoRoot := by
  rfl

theorem miRootTable_nil_sim (term : AST) :
    eval pMI 1 (miRootTable MIRNil term) = MINoRoot := by
  simp only [eval, os_miRootTable_nil]

theorem os_miRootTable_fact_skip (fact rest term : AST) :
    oneStep pMI (miRootTable (MIRCons (MIFact fact) rest) term) =
      some (miRootTable rest term) := by
  rfl

theorem os_miRootTable_rule_cons (lhs rhs rest term : AST) :
    oneStep pMI (miRootTable (MIRCons (MIRule lhs rhs) rest) term) =
      some (miRootK rest term rhs (miMatch lhs term MIBNil)) := by
  rfl

theorem os_miRootK_ok (rest term rhs bs : AST) :
    oneStep pMI (miRootK rest term rhs (MIMatchOk bs)) =
      some (MIRootStep (miSubst bs rhs)) := by
  rfl

theorem os_miRootK_fail (rest term rhs : AST) :
    oneStep pMI (miRootK rest term rhs MIMatchFail) =
      some (miRootTable rest term) := by
  rfl

theorem os_MIRootStep_arg_step (t t' : AST)
    (hstep : oneStep pMI t = some t') :
    oneStep pMI (MIRootStep t) = some (MIRootStep t') := by
  rw [oneStep.eq_def]
  simp only [MIRootStep, app]
  rw [baseReducts_MIRootStep_pMI_raw]
  simp only [oneStepList, hstep, Option.map_some]

theorem os_miRoot_misubst_default (rules bs rhs : AST) :
    oneStep pMI (miRoot rules (miSubst bs rhs)) =
      some (miRootTable rules (miSubst bs rhs)) := by
  rfl

theorem os_miRoot_misubstVarK_default (rules orig arg : AST) :
    oneStep pMI (miRoot rules (miSubstVarK orig arg)) =
      some (miRootTable rules (miSubstVarK orig arg)) := by
  rfl

theorem baseReducts_miRootK_active_raw (rest term rhs r : AST)
    (hactive : MatchActiveShape r) :
    baseReducts pMI (miRootK rest term rhs r) = [] := by
  cases hactive <;> rfl

theorem os_miRootK_active_step (rest term rhs r r' : AST)
    (hrest : IsNormal pMI rest) (hterm : IsNormal pMI term)
    (hrhs : IsNormal pMI rhs)
    (hactive : MatchActiveShape r)
    (hstep : oneStep pMI r = some r') :
    oneStep pMI (miRootK rest term rhs r) =
      some (miRootK rest term rhs r') := by
  rw [oneStep.eq_def]
  change
    (match baseReducts pMI (miRootK rest term rhs r) with
    | q :: _ => some q
    | [] => (oneStepList pMI [rest, term, rhs, r]).map
        (fun args' => AST.sexp (Label.id "mi-rootK") args')) =
      some (miRootK rest term rhs r')
  rw [baseReducts_miRootK_active_raw rest term rhs r hactive]
  simp only [IsNormal] at hrest hterm hrhs
  simp only [oneStepList, hrest, hterm, hrhs, hstep, Option.map_some]
  rfl

theorem miRootK_eval_of_match_ok_raw (rest term lhs rhs bs : AST)
    (matchFuel : Nat)
    (hrest : IsNormal pMI rest) (hterm : IsNormal pMI term)
    (hrhs : IsNormal pMI rhs) (hbs : IsNormal pMI bs)
    (hmatch : eval pMI matchFuel (miMatch lhs term MIBNil) = MIMatchOk bs)
    (hactive : ∀ k, k < matchFuel →
      MatchActiveShape (eval pMI k (miMatch lhs term MIBNil))) :
    ∃ N,
      eval pMI N (miRootK rest term rhs (miMatch lhs term MIBNil)) =
        MIRootStep (miSubst bs rhs) := by
  let F : AST → AST := fun z => miRootK rest term rhs z
  obtain ⟨Mmatch, hmatchCtx⟩ :=
    cong_eval_match_active_mi F
      (fun s s' hactiveStep hstep =>
        os_miRootK_active_step rest term rhs s s'
          hrest hterm hrhs hactiveStep hstep)
      matchFuel hmatch (normal_MIMatchOk bs hbs) hactive
  have hok :
      eval pMI 1 (F (MIMatchOk bs)) =
        MIRootStep (miSubst bs rhs) := by
    simp only [F, eval, os_miRootK_ok]
  have htotal := eval_trans_mi Mmatch 1
    (miRootK rest term rhs (miMatch lhs term MIBNil))
    (F (MIMatchOk bs))
    (MIRootStep (miSubst bs rhs))
    hmatchCtx hok
  exact ⟨Mmatch + 1, htotal⟩

theorem miRootK_eval_of_match_ok (rest term lhs rhs bs out : AST)
    (matchFuel substFuel : Nat)
    (hrest : IsNormal pMI rest) (hterm : IsNormal pMI term)
    (hrhs : IsNormal pMI rhs) (hbs : IsNormal pMI bs)
    (hmatch : eval pMI matchFuel (miMatch lhs term MIBNil) = MIMatchOk bs)
    (hactive : ∀ k, k < matchFuel →
      MatchActiveShape (eval pMI k (miMatch lhs term MIBNil)))
    (hsubst : eval pMI substFuel (miSubst bs rhs) = out)
    (hout : IsNormal pMI out) :
    ∃ N,
      eval pMI N (miRootK rest term rhs (miMatch lhs term MIBNil)) =
        MIRootStep out := by
  let F : AST → AST := fun z => miRootK rest term rhs z
  obtain ⟨Mmatch, hmatchCtx⟩ :=
    cong_eval_match_active_mi F
      (fun s s' hactiveStep hstep =>
        os_miRootK_active_step rest term rhs s s'
          hrest hterm hrhs hactiveStep hstep)
      matchFuel hmatch (normal_MIMatchOk bs hbs) hactive
  have hok : eval pMI 1 (F (MIMatchOk bs)) =
      MIRootStep (miSubst bs rhs) := by
    simp only [F, eval, os_miRootK_ok]
  obtain ⟨Msubst, hsubstCtx⟩ :=
    cong_eval_mi (fun z => MIRootStep z)
      (fun s s' hstep => os_MIRootStep_arg_step s s' hstep)
      substFuel hsubst hout
  have hpre := eval_trans_mi Mmatch 1
    (miRootK rest term rhs (miMatch lhs term MIBNil))
    (F (MIMatchOk bs))
    (MIRootStep (miSubst bs rhs))
    hmatchCtx hok
  have htotal := eval_trans_mi (Mmatch + 1) Msubst
    (miRootK rest term rhs (miMatch lhs term MIBNil))
    (MIRootStep (miSubst bs rhs))
    (MIRootStep out)
    hpre hsubstCtx
  exact ⟨(Mmatch + 1) + Msubst, htotal⟩

theorem miRootK_eval_of_match_fail (rest term lhs rhs : AST)
    (matchFuel : Nat)
    (hrest : IsNormal pMI rest) (hterm : IsNormal pMI term)
    (hrhs : IsNormal pMI rhs)
    (hmatch : eval pMI matchFuel (miMatch lhs term MIBNil) = MIMatchFail)
    (hactive : ∀ k, k < matchFuel →
      MatchActiveShape (eval pMI k (miMatch lhs term MIBNil))) :
    ∃ N,
      eval pMI N (miRootK rest term rhs (miMatch lhs term MIBNil)) =
        miRootTable rest term := by
  let F : AST → AST := fun z => miRootK rest term rhs z
  obtain ⟨Mmatch, hmatchCtx⟩ :=
    cong_eval_match_active_mi F
      (fun s s' hactiveStep hstep =>
        os_miRootK_active_step rest term rhs s s'
          hrest hterm hrhs hactiveStep hstep)
      matchFuel hmatch normal_MIMatchFail hactive
  have hfail : eval pMI 1 (F MIMatchFail) = miRootTable rest term := by
    simp only [F, eval, os_miRootK_fail]
  have htotal := eval_trans_mi Mmatch 1
    (miRootK rest term rhs (miMatch lhs term MIBNil))
    (F MIMatchFail)
    (miRootTable rest term)
    hmatchCtx hfail
  exact ⟨Mmatch + 1, htotal⟩

theorem miRootTable_rule_source_some_sim
    (lhs rhs term encodedLhs encodedRhs encodedTerm encodedRest : AST)
    (rest : List RewriteDecl) (bs : List (String × AST))
    (hlhs : encAST? lhs = some encodedLhs)
    (hrhs : encAST? rhs = some encodedRhs)
    (hterm : encAST? term = some encodedTerm)
    (hrest : encRules? rest = some encodedRest)
    (hmatch : AST.matchPat lhs term [] = some bs) :
    ∃ (encodedOut : AST) (N : Nat),
      encAST? (AST.inst bs rhs) = some encodedOut ∧
      eval pMI N
          (miRootTable
            (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
            encodedTerm) =
        MIRootStep encodedOut ∧
      IsNormal pMI (MIRootStep encodedOut) := by
  obtain ⟨encodedBs, hbs⟩ :=
    matchPat_preserves_encBinds? lhs term encodedLhs encodedTerm MIBNil
      [] bs hlhs hterm rfl hmatch
  obtain ⟨Nmatch, hmatchEval, hactive, _hmatchNorm⟩ :=
    miMatch_source_some_first_result lhs term encodedLhs encodedTerm
      MIBNil encodedBs [] bs hlhs hterm rfl hmatch hbs
  obtain ⟨encodedOut, Nsubst, hout, hsubstEval, houtNorm⟩ :=
    miSubst_encAST_inst_eval rhs encodedRhs hrhs bs encodedBs hbs
  obtain ⟨NrootK, hrootK⟩ :=
    miRootK_eval_of_match_ok encodedRest encodedTerm encodedLhs encodedRhs
      encodedBs encodedOut Nmatch Nsubst
      (encRules?_some_normal rest encodedRest hrest)
      (encAST?_some_normal term encodedTerm hterm)
      (encAST?_some_normal rhs encodedRhs hrhs)
      (encBinds?_some_normal bs encodedBs hbs)
      hmatchEval hactive hsubstEval houtNorm
  have hdispatch :
      eval pMI 1
          (miRootTable
            (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
            encodedTerm) =
        miRootK encodedRest encodedTerm encodedRhs
          (miMatch encodedLhs encodedTerm MIBNil) := by
    simp only [eval, os_miRootTable_rule_cons]
  have htotal := eval_trans_mi 1 NrootK
    (miRootTable (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
      encodedTerm)
    (miRootK encodedRest encodedTerm encodedRhs
      (miMatch encodedLhs encodedTerm MIBNil))
    (MIRootStep encodedOut)
    hdispatch hrootK
  exact ⟨encodedOut, 1 + NrootK, hout, htotal,
    normal_MIRootStep encodedOut houtNorm⟩

theorem miRootTable_rule_source_none_eval_of_rest
    (lhs rhs term encodedLhs encodedRhs encodedTerm encodedRest restOut : AST)
    (rest : List RewriteDecl) (restFuel : Nat)
    (hlhs : encAST? lhs = some encodedLhs)
    (hrhs : encAST? rhs = some encodedRhs)
    (hterm : encAST? term = some encodedTerm)
    (hrest : encRules? rest = some encodedRest)
    (hmatch : AST.matchPat lhs term [] = none)
    (hrestEval : eval pMI restFuel (miRootTable encodedRest encodedTerm) = restOut) :
    ∃ N,
      eval pMI N
          (miRootTable
            (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
            encodedTerm) =
        restOut := by
  obtain ⟨Nmatch, hmatchEval, hactive, _hmatchNorm⟩ :=
    miMatch_source_none_first_result lhs term encodedLhs encodedTerm
      MIBNil [] hlhs hterm rfl hmatch
  obtain ⟨NrootK, hrootK⟩ :=
    miRootK_eval_of_match_fail encodedRest encodedTerm encodedLhs encodedRhs
      Nmatch
      (encRules?_some_normal rest encodedRest hrest)
      (encAST?_some_normal term encodedTerm hterm)
      (encAST?_some_normal rhs encodedRhs hrhs)
      hmatchEval hactive
  have hdispatch :
      eval pMI 1
          (miRootTable
            (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
            encodedTerm) =
        miRootK encodedRest encodedTerm encodedRhs
          (miMatch encodedLhs encodedTerm MIBNil) := by
    simp only [eval, os_miRootTable_rule_cons]
  have hpre := eval_trans_mi 1 NrootK
    (miRootTable (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
      encodedTerm)
    (miRootK encodedRest encodedTerm encodedRhs
      (miMatch encodedLhs encodedTerm MIBNil))
    (miRootTable encodedRest encodedTerm)
    hdispatch hrootK
  have htotal := eval_trans_mi (1 + NrootK) restFuel
    (miRootTable (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
      encodedTerm)
    (miRootTable encodedRest encodedTerm)
    restOut
    hpre hrestEval
  exact ⟨(1 + NrootK) + restFuel, htotal⟩

theorem miRootTable_rule_source_some_raw_sim
    (lhs rhs term encodedLhs encodedRhs encodedTerm encodedRest : AST)
    (rest : List RewriteDecl) (bs : List (String × AST))
    (hlhs : encAST? lhs = some encodedLhs)
    (hrhs : encAST? rhs = some encodedRhs)
    (hterm : encAST? term = some encodedTerm)
    (hrest : encRules? rest = some encodedRest)
    (hmatch : AST.matchPat lhs term [] = some bs) :
    ∃ (encodedBs : AST) (N : Nat),
      encBinds? bs = some encodedBs ∧
      eval pMI N
          (miRootTable
            (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
            encodedTerm) =
        MIRootStep (miSubst encodedBs encodedRhs) ∧
      IsNormal pMI encodedBs := by
  obtain ⟨encodedBs, hbs⟩ :=
    matchPat_preserves_encBinds? lhs term encodedLhs encodedTerm MIBNil
      [] bs hlhs hterm rfl hmatch
  obtain ⟨Nmatch, hmatchEval, hactive, _hmatchNorm⟩ :=
    miMatch_source_some_first_result lhs term encodedLhs encodedTerm
      MIBNil encodedBs [] bs hlhs hterm rfl hmatch hbs
  obtain ⟨NrootK, hrootK⟩ :=
    miRootK_eval_of_match_ok_raw encodedRest encodedTerm encodedLhs encodedRhs
      encodedBs Nmatch
      (encRules?_some_normal rest encodedRest hrest)
      (encAST?_some_normal term encodedTerm hterm)
      (encAST?_some_normal rhs encodedRhs hrhs)
      (encBinds?_some_normal bs encodedBs hbs)
      hmatchEval hactive
  have hdispatch :
      eval pMI 1
          (miRootTable
            (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
            encodedTerm) =
        miRootK encodedRest encodedTerm encodedRhs
          (miMatch encodedLhs encodedTerm MIBNil) := by
    simp only [eval, os_miRootTable_rule_cons]
  have htotal := eval_trans_mi 1 NrootK
    (miRootTable (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
      encodedTerm)
    (miRootK encodedRest encodedTerm encodedRhs
      (miMatch encodedLhs encodedTerm MIBNil))
    (MIRootStep (miSubst encodedBs encodedRhs))
    hdispatch hrootK
  exact ⟨encodedBs, 1 + NrootK, hbs, htotal,
    encBinds?_some_normal bs encodedBs hbs⟩

theorem miRootTable_source_sim :
    ∀ (rws : List RewriteDecl) (term encodedRules encodedTerm : AST),
      encRules? rws = some encodedRules →
      encAST? term = some encodedTerm →
      match rootBaseStep? rws term with
      | some out =>
          ∃ (encodedOut : AST) (N : Nat),
            encAST? out = some encodedOut ∧
            eval pMI N (miRootTable encodedRules encodedTerm) =
              MIRootStep encodedOut ∧
            IsNormal pMI (MIRootStep encodedOut)
      | none =>
          ∃ N, eval pMI N (miRootTable encodedRules encodedTerm) = MINoRoot
  | [], term, encodedRules, encodedTerm, hrules, _hterm => by
      cases hrules
      simp only [rootBaseStep?]
      exact ⟨1, miRootTable_nil_sim encodedTerm⟩
  | rd :: rest, term, encodedRules, encodedTerm, hrules, hterm => by
      cases hrdRw : rd.rw with
      | ctx _ _ =>
          simp only [encRules?, encRewriteDecl?, hrdRw] at hrules
          cases hrules
      | base lhs rhs =>
          simp only [encRules?, encRewriteDecl?, hrdRw] at hrules
          cases hlhs : encAST? lhs with
          | none =>
              simp [hlhs] at hrules
          | some encodedLhs =>
              cases hrhs : encAST? rhs with
              | none =>
                  simp [hlhs, hrhs] at hrules
              | some encodedRhs =>
                  cases hrest : encRules? rest with
                  | none =>
                      simp [hlhs, hrhs, hrest] at hrules
                  | some encodedRest =>
                      simp [hlhs, hrhs, hrest] at hrules
                      cases hrules
                      cases hmatch : AST.matchPat lhs term [] with
                      | some bs =>
                          simp only [rootBaseStep?, hrdRw, hmatch]
                          exact miRootTable_rule_source_some_sim lhs rhs term
                            encodedLhs encodedRhs encodedTerm encodedRest
                            rest bs hlhs hrhs hterm hrest hmatch
                      | none =>
                          have htail :=
                            miRootTable_source_sim rest term encodedRest
                              encodedTerm hrest hterm
                          simp only [rootBaseStep?, hrdRw, hmatch]
                          cases htailMatch : rootBaseStep? rest term with
                          | some out =>
                              simp only [htailMatch] at htail
                              obtain ⟨encodedOut, Ntail, hout, htailEval,
                                htailNorm⟩ := htail
                              obtain ⟨N, hN⟩ :=
                                miRootTable_rule_source_none_eval_of_rest
                                  lhs rhs term encodedLhs encodedRhs
                                  encodedTerm encodedRest
                                  (MIRootStep encodedOut) rest Ntail
                                  hlhs hrhs hterm hrest hmatch htailEval
                              exact ⟨encodedOut, N, hout, hN, htailNorm⟩
                          | none =>
                              simp only [htailMatch] at htail
                              obtain ⟨Ntail, htailEval⟩ := htail
                              obtain ⟨N, hN⟩ :=
                                miRootTable_rule_source_none_eval_of_rest
                                  lhs rhs term encodedLhs encodedRhs
                                  encodedTerm encodedRest MINoRoot rest Ntail
                                  hlhs hrhs hterm hrest hmatch htailEval
                              exact ⟨N, hN⟩

theorem apply_root_match_self_on_app_head_ne (rules args : AST) (headName : String)
    (hhead : (headName == "match") = false) :
    applyBaseRewrite
      (rw "root-match-self"
        (miRoot vRules
          (MIApp "match"
            (MICons (MISym "Self") (MICons vP (MICons vT MINil)))))
        (miQueryRoot vRules vP vT))
      (miRoot rules (MIApp headName args)) = none := by
  have hmh : ("match" == headName) = false := by
    simpa [string_beq_symm_mi headName "match"] using hhead
  have hroot : ("mi-root" == "mi-root") = true := beq_iff_eq.mpr rfl
  have happ : ("MIApp" == "MIApp") = true := beq_iff_eq.mpr rfl
  simp only [applyBaseRewrite, rw, miRoot, MIApp, app,
    AST.matchPat, AST.matchPatList, label_id_beq, hroot, happ, if_true]
  cases hvr : AST.matchPat vRules rules [] with
  | none =>
      rfl
  | some bs =>
      simp only [Option.bind_some]
      cases hheadMatch : AST.matchPat (con0 "match") (con0 headName) bs with
      | none =>
          simp only [Option.bind_none, Option.map_none]
      | some bs2 =>
          exfalso
          change AST.matchPat (.sexp (.id "match") [])
            (.sexp (.id headName) []) bs = some bs2 at hheadMatch
          simp only [AST.matchPat, AST.matchPatList, label_id_beq, hmh,
            Bool.false_eq_true, if_false] at hheadMatch
          cases hheadMatch

theorem miRules_root_default_ne_prefix :
    miRules =
      List.take 30 miRules ++
      [ rw "root-match-self"
          (miRoot vRules
            (MIApp "match"
              (MICons (MISym "Self") (MICons vP (MICons vT MINil)))))
          (miQueryRoot vRules vP vT)
      , rw "root-default" (miRoot vRules vTerm) (miRootTable vRules vTerm) ] ++
      List.drop 32 miRules := by
  rfl

theorem baseReducts_miRoot_default_app_head_ne (rules args : AST)
    (headName : String) (hhead : (headName == "match") = false) :
    ∃ tail,
      baseReducts pMI (miRoot rules (MIApp headName args)) =
        miRootTable rules (MIApp headName args) :: tail := by
  let target := miRoot rules (MIApp headName args)
  refine ⟨(List.drop 32 miRules).filterMap (fun rd => applyBaseRewrite rd target), ?_⟩
  change miRules.filterMap (fun rd => applyBaseRewrite rd target) =
    miRootTable rules (MIApp headName args) ::
      (List.drop 32 miRules).filterMap (fun rd => applyBaseRewrite rd target)
  rw [miRules_root_default_ne_prefix]
  have hpre :
      (List.take 30 miRules).filterMap (fun rd => applyBaseRewrite rd target) = [] := by
    rfl
  have hspecial :
      applyBaseRewrite
        (rw "root-match-self"
          (miRoot vRules
            (MIApp "match"
              (MICons (MISym "Self") (MICons vP (MICons vT MINil)))))
          (miQueryRoot vRules vP vT))
        target = none := by
    dsimp only [target]
    exact apply_root_match_self_on_app_head_ne rules args headName hhead
  have hdefault :
      applyBaseRewrite
        (rw "root-default" (miRoot vRules vTerm) (miRootTable vRules vTerm))
        target = some (miRootTable rules (MIApp headName args)) := by
    rfl
  have hdrop :
      List.drop 32
        (List.take 30 miRules ++
          [ rw "root-match-self"
              (miRoot vRules
                (MIApp "match"
                  (MICons (MISym "Self") (MICons vP (MICons vT MINil)))))
              (miQueryRoot vRules vP vT)
          , rw "root-default" (miRoot vRules vTerm) (miRootTable vRules vTerm) ] ++
          List.drop 32 miRules) = List.drop 32 miRules := by
    rfl
  simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
    hpre, hspecial, hdefault, hdrop, List.nil_append]
  rfl

theorem os_miRoot_default_var (rules : AST) (v : String) :
    oneStep pMI (miRoot rules (MIVar v)) =
      some (miRootTable rules (MIVar v)) := by
  rfl

theorem os_miRoot_default_sym (rules : AST) (s : String) :
    oneStep pMI (miRoot rules (MISym s)) =
      some (miRootTable rules (MISym s)) := by
  rfl

theorem os_miRoot_default_app_head_ne (rules args : AST) (headName : String)
    (hhead : (headName == "match") = false) :
    oneStep pMI (miRoot rules (MIApp headName args)) =
      some (miRootTable rules (MIApp headName args)) := by
  obtain ⟨tail, hbase⟩ :=
    baseReducts_miRoot_default_app_head_ne rules args headName hhead
  change
    (match baseReducts pMI (miRoot rules (MIApp headName args)) with
    | r :: _ => some r
    | [] =>
        (oneStepList pMI [rules, MIApp headName args]).map
          (fun args' => AST.sexp (Label.id "mi-root") args')) =
      some (miRootTable rules (MIApp headName args))
  rw [hbase]

theorem miRoot_eval_of_rootTable_source_sim
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hroot : oneStep pMI (miRoot encodedRules encodedTerm) =
      some (miRootTable encodedRules encodedTerm)) :
    match rootBaseStep? rws term with
    | some out =>
        ∃ (encodedOut : AST) (N : Nat),
          encAST? out = some encodedOut ∧
          eval pMI N (miRoot encodedRules encodedTerm) =
            MIRootStep encodedOut ∧
          IsNormal pMI (MIRootStep encodedOut)
    | none =>
        ∃ N, eval pMI N (miRoot encodedRules encodedTerm) = MINoRoot := by
  have hdispatch :
      eval pMI 1 (miRoot encodedRules encodedTerm) =
        miRootTable encodedRules encodedTerm := by
    simp only [eval, hroot]
  have htable := miRootTable_source_sim rws term encodedRules encodedTerm
    hrules hterm
  cases hcase : rootBaseStep? rws term with
  | some out =>
      simp only [hcase] at htable ⊢
      obtain ⟨encodedOut, Ntable, hout, htableEval, hnorm⟩ := htable
      have htotal := eval_trans_mi 1 Ntable
        (miRoot encodedRules encodedTerm)
        (miRootTable encodedRules encodedTerm)
        (MIRootStep encodedOut)
        hdispatch htableEval
      exact ⟨encodedOut, 1 + Ntable, hout, htotal, hnorm⟩
  | none =>
      simp only [hcase] at htable ⊢
      obtain ⟨Ntable, htableEval⟩ := htable
      have htotal := eval_trans_mi 1 Ntable
        (miRoot encodedRules encodedTerm)
        (miRootTable encodedRules encodedTerm)
        MINoRoot
        hdispatch htableEval
      exact ⟨1 + Ntable, htotal⟩

theorem miRoot_source_sim_var (rws : List RewriteDecl)
    (v : String) (encodedRules : AST)
    (hrules : encRules? rws = some encodedRules) :
    match rootBaseStep? rws (.var (.base v)) with
    | some out =>
        ∃ (encodedOut : AST) (N : Nat),
          encAST? out = some encodedOut ∧
          eval pMI N (miRoot encodedRules (MIVar v)) =
            MIRootStep encodedOut ∧
          IsNormal pMI (MIRootStep encodedOut)
    | none =>
        ∃ N, eval pMI N (miRoot encodedRules (MIVar v)) = MINoRoot :=
  miRoot_eval_of_rootTable_source_sim rws (.var (.base v)) encodedRules
    (MIVar v) hrules rfl (os_miRoot_default_var encodedRules v)

theorem miRoot_source_sim_sym (rws : List RewriteDecl)
    (s : String) (encodedRules : AST)
    (hrules : encRules? rws = some encodedRules) :
    match rootBaseStep? rws (.sexp (.id s) []) with
    | some out =>
        ∃ (encodedOut : AST) (N : Nat),
          encAST? out = some encodedOut ∧
          eval pMI N (miRoot encodedRules (MISym s)) =
            MIRootStep encodedOut ∧
          IsNormal pMI (MIRootStep encodedOut)
    | none =>
        ∃ N, eval pMI N (miRoot encodedRules (MISym s)) = MINoRoot :=
  miRoot_eval_of_rootTable_source_sim rws (.sexp (.id s) []) encodedRules
    (MISym s) hrules rfl (os_miRoot_default_sym encodedRules s)

theorem miRoot_source_sim_app_head_ne (rws : List RewriteDecl)
    (headName : String) (a : AST) (rest : List AST)
    (encodedRules encodedArgs : AST)
    (hrules : encRules? rws = some encodedRules)
    (hargs : encASTList? (a :: rest) = some encodedArgs)
    (hhead : (headName == "match") = false) :
    match rootBaseStep? rws (.sexp (.id headName) (a :: rest)) with
    | some out =>
        ∃ (encodedOut : AST) (N : Nat),
          encAST? out = some encodedOut ∧
          eval pMI N (miRoot encodedRules (MIApp headName encodedArgs)) =
            MIRootStep encodedOut ∧
          IsNormal pMI (MIRootStep encodedOut)
    | none =>
        ∃ N,
          eval pMI N (miRoot encodedRules (MIApp headName encodedArgs)) =
            MINoRoot := by
  have hterm :
      encAST? (.sexp (.id headName) (a :: rest)) =
        some (MIApp headName encodedArgs) := by
    simp only [encAST?, hargs]
  exact miRoot_eval_of_rootTable_source_sim rws
    (.sexp (.id headName) (a :: rest)) encodedRules
    (MIApp headName encodedArgs) hrules hterm
    (os_miRoot_default_app_head_ne encodedRules encodedArgs headName hhead)

theorem os_miStep_dispatch (rules term : AST) :
    oneStep pMI (miStep rules term) =
      some (miStepRootK rules term (miRoot rules term)) := by
  rfl

theorem os_miStepRootK_root_step (rules term next : AST) :
    oneStep pMI (miStepRootK rules term (MIRootStep next)) =
      some (MIStep next) := by
  rfl

theorem os_miStepRootK_app_no_root (rules args : AST) (h : String) :
    oneStep pMI (miStepRootK rules (MIApp h args) MINoRoot) =
      some (miStepAppK (con0 h) (miStepArgs rules args)) := by
  rfl

theorem os_miStepRootK_var_no_root (rules : AST) (v : String) :
    oneStep pMI (miStepRootK rules (MIVar v) MINoRoot) =
      some MINoStep := by
  rfl

theorem os_miStepRootK_sym_no_root (rules : AST) (s : String) :
    oneStep pMI (miStepRootK rules (MISym s) MINoRoot) =
      some MINoStep := by
  rfl

theorem os_miStepArgs_nil (rules : AST) :
    oneStep pMI (miStepArgs rules MINil) = some MINoArgsStep := by
  rfl

theorem os_miStepArgs_cons (rules x xs : AST) :
    oneStep pMI (miStepArgs rules (MICons x xs)) =
      some (miStepArgsK rules x xs (miStep rules x)) := by
  rfl

theorem os_miStepArgsK_step (rules x xs next : AST) :
    oneStep pMI (miStepArgsK rules x xs (MIStep next)) =
      some (MIArgsStep (MICons next xs)) := by
  rfl

theorem os_miStepArgsK_none (rules x xs : AST) :
    oneStep pMI (miStepArgsK rules x xs MINoStep) =
      some (miStepArgsRestK x (miStepArgs rules xs)) := by
  rfl

theorem os_miStepArgsRestK_step (x xs : AST) :
    oneStep pMI (miStepArgsRestK x (MIArgsStep xs)) =
      some (MIArgsStep (MICons x xs)) := by
  rfl

theorem os_miStepArgsRestK_none (x : AST) :
    oneStep pMI (miStepArgsRestK x MINoArgsStep) =
      some MINoArgsStep := by
  rfl

theorem os_miStepAppK_args (h args : AST) :
    oneStep pMI (miStepAppK h (MIArgsStep args)) =
      some (MIStep (app "MIApp" [h, args])) := by
  rfl

theorem os_miStepAppK_args_named (h : String) (args : AST) :
    oneStep pMI (miStepAppK (con0 h) (MIArgsStep args)) =
      some (MIStep (MIApp h args)) := by
  rfl

theorem os_miStepAppK_none (h : AST) :
    oneStep pMI (miStepAppK h MINoArgsStep) = some MINoStep := by
  rfl

theorem os_miEval_zero (rules term : AST) :
    oneStep pMI (miEval rules term FZ) = some (MIExhausted term) := by
  rfl

theorem os_miEval_succ (rules term fuelArg : AST) :
    oneStep pMI (miEval rules term (FS fuelArg)) =
      some (miEvalK rules term fuelArg (miStep rules term)) := by
  rfl

theorem os_miEvalK_step (rules term fuelArg next : AST) :
    oneStep pMI (miEvalK rules term fuelArg (MIStep next)) =
      some (miEval rules next fuelArg) := by
  rfl

theorem os_miEvalK_done (rules term fuelArg : AST) :
    oneStep pMI (miEvalK rules term fuelArg MINoStep) =
      some (MIDone term) := by
  rfl

theorem os_MIStep_arg_step (t t' : AST)
    (hstep : oneStep pMI t = some t') :
    oneStep pMI (MIStep t) = some (MIStep t') := by
  rw [oneStep.eq_def]
  simp only [MIStep, app]
  rw [baseReducts_MIStep_pMI_raw]
  simp only [oneStepList, hstep, Option.map_some]

theorem os_MIArgsStep_arg_step (args args' : AST)
    (hstep : oneStep pMI args = some args') :
    oneStep pMI (MIArgsStep args) = some (MIArgsStep args') := by
  rw [oneStep.eq_def]
  simp only [MIArgsStep, app]
  rw [baseReducts_MIArgsStep_pMI_raw]
  simp only [oneStepList, hstep, Option.map_some]

theorem os_MIDone_arg_step (term term' : AST)
    (hstep : oneStep pMI term = some term') :
    oneStep pMI (MIDone term) = some (MIDone term') := by
  rw [oneStep.eq_def]
  simp only [MIDone, app]
  rw [baseReducts_MIDone_pMI_raw]
  simp only [oneStepList, hstep, Option.map_some]

theorem os_MIExhausted_arg_step (term term' : AST)
    (hstep : oneStep pMI term = some term') :
    oneStep pMI (MIExhausted term) = some (MIExhausted term') := by
  rw [oneStep.eq_def]
  simp only [MIExhausted, app]
  rw [baseReducts_MIExhausted_pMI_raw]
  simp only [oneStepList, hstep, Option.map_some]

theorem miStepRootK_root_step_sim (rules term next : AST) :
    eval pMI 1 (miStepRootK rules term (MIRootStep next)) =
      MIStep next := by
  simp only [eval, os_miStepRootK_root_step]

theorem miStepRootK_app_no_root_sim (rules args : AST) (h : String) :
    eval pMI 1 (miStepRootK rules (MIApp h args) MINoRoot) =
      miStepAppK (con0 h) (miStepArgs rules args) := by
  simp only [eval, os_miStepRootK_app_no_root]

theorem miStepRootK_var_no_root_sim (rules : AST) (v : String) :
    eval pMI 1 (miStepRootK rules (MIVar v) MINoRoot) = MINoStep := by
  simp only [eval, os_miStepRootK_var_no_root]

theorem miStepRootK_sym_no_root_sim (rules : AST) (s : String) :
    eval pMI 1 (miStepRootK rules (MISym s) MINoRoot) = MINoStep := by
  simp only [eval, os_miStepRootK_sym_no_root]

theorem miStepArgs_nil_sim (rules : AST) :
    eval pMI 1 (miStepArgs rules MINil) = MINoArgsStep := by
  simp only [eval, os_miStepArgs_nil]

theorem miStepArgsK_step_sim (rules x xs next : AST) :
    eval pMI 1 (miStepArgsK rules x xs (MIStep next)) =
      MIArgsStep (MICons next xs) := by
  simp only [eval, os_miStepArgsK_step]

theorem miStepArgsK_none_sim (rules x xs : AST) :
    eval pMI 1 (miStepArgsK rules x xs MINoStep) =
      miStepArgsRestK x (miStepArgs rules xs) := by
  simp only [eval, os_miStepArgsK_none]

theorem miStepArgsRestK_step_sim (x xs : AST) :
    eval pMI 1 (miStepArgsRestK x (MIArgsStep xs)) =
      MIArgsStep (MICons x xs) := by
  simp only [eval, os_miStepArgsRestK_step]

theorem miStepArgsRestK_none_sim (x : AST) :
    eval pMI 1 (miStepArgsRestK x MINoArgsStep) =
      MINoArgsStep := by
  simp only [eval, os_miStepArgsRestK_none]

theorem miStepAppK_args_named_sim (h : String) (args : AST) :
    eval pMI 1 (miStepAppK (con0 h) (MIArgsStep args)) =
      MIStep (MIApp h args) := by
  simp only [eval, os_miStepAppK_args_named]

theorem miStepAppK_none_sim (h : AST) :
    eval pMI 1 (miStepAppK h MINoArgsStep) = MINoStep := by
  simp only [eval, os_miStepAppK_none]

inductive RootActiveShape : AST → Prop where
  | root (rules term : AST) : RootActiveShape (miRoot rules term)
  | rootTable (rules term : AST) : RootActiveShape (miRootTable rules term)
  | rootK (rest term rhs r : AST) : RootActiveShape (miRootK rest term rhs r)

inductive ArgsActiveShape : AST → Prop where
  | args (rules args : AST) : ArgsActiveShape (miStepArgs rules args)
  | argsK (rules x xs r : AST) : ArgsActiveShape (miStepArgsK rules x xs r)
  | argsRestK (x r : AST) : ArgsActiveShape (miStepArgsRestK x r)

inductive StepActiveShape : AST → Prop where
  | step (rules term : AST) : StepActiveShape (miStep rules term)
  | rootK (rules term r : AST) : StepActiveShape (miStepRootK rules term r)
  | appK (h r : AST) : StepActiveShape (miStepAppK h r)

def StepRawSome (encodedRules encodedTerm out : AST) : Prop :=
  ∃ (rawNext encodedOut : AST) (stepFuel normFuel : Nat),
    encAST? out = some encodedOut ∧
    eval pMI stepFuel (miStep encodedRules encodedTerm) = MIStep rawNext ∧
    (∀ k, k < stepFuel →
      StepActiveShape (eval pMI k (miStep encodedRules encodedTerm))) ∧
    eval pMI normFuel rawNext = encodedOut ∧
    IsNormal pMI encodedOut

def StepRawNone (encodedRules encodedTerm : AST) : Prop :=
  ∃ stepFuel,
    eval pMI stepFuel (miStep encodedRules encodedTerm) = MINoStep ∧
    ∀ k, k < stepFuel →
      StepActiveShape (eval pMI k (miStep encodedRules encodedTerm))

def ArgsRawSome (encodedRules encodedArgs : AST) (out : List AST) : Prop :=
  ∃ (rawArgs encodedOut : AST) (argsFuel normFuel : Nat),
    encASTList? out = some encodedOut ∧
    eval pMI argsFuel (miStepArgs encodedRules encodedArgs) =
      MIArgsStep rawArgs ∧
    (∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs encodedRules encodedArgs))) ∧
    eval pMI normFuel rawArgs = encodedOut ∧
    IsNormal pMI encodedOut

def ArgsRawNone (encodedRules encodedArgs : AST) : Prop :=
  ∃ argsFuel,
    eval pMI argsFuel (miStepArgs encodedRules encodedArgs) = MINoArgsStep ∧
    ∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs encodedRules encodedArgs))

mutual
  inductive RawTermPayload : AST → AST → Prop where
    | encoded (encodedTerm : AST) :
        RawTermPayload encodedTerm encodedTerm
    | substInst {template encodedTemplate encodedBs encodedOut : AST}
        {bs : List (String × AST)} {fuel : Nat}
        (htemplate : encAST? template = some encodedTemplate)
        (hbs : encBinds? bs = some encodedBs)
        (hinst : encAST? (AST.inst bs template) = some encodedOut)
        (hsubst : eval pMI fuel (miSubst encodedBs encodedTemplate) =
          encodedOut)
        (hout : IsNormal pMI encodedOut) :
        RawTermPayload (miSubst encodedBs encodedTemplate) encodedOut
    | app (h : String) {rawArgs encodedArgs : AST}
        (hargs : RawArgsPayload rawArgs encodedArgs) :
        RawTermPayload (MIApp h rawArgs) (MIApp h encodedArgs)

  inductive RawArgsPayload : AST → AST → Prop where
    | encoded (encodedArgs : AST) :
        RawArgsPayload encodedArgs encodedArgs
    | consHead {rawHead encodedHead encodedTail : AST}
        (hhead : RawTermPayload rawHead encodedHead) :
        RawArgsPayload (MICons rawHead encodedTail)
          (MICons encodedHead encodedTail)
    | consTail {encodedHead rawTail encodedTail : AST}
        (htail : RawArgsPayload rawTail encodedTail) :
        RawArgsPayload (MICons encodedHead rawTail)
          (MICons encodedHead encodedTail)
end

inductive RawBindsPayload : AST → AST → Prop where
  | nil : RawBindsPayload MIBNil MIBNil
  | cons (v : String) {rawTerm encodedTerm rawRest encodedRest : AST}
      (hterm : RawTermPayload rawTerm encodedTerm)
      (hrest : RawBindsPayload rawRest encodedRest) :
      RawBindsPayload
        (MIBCons (con0 v) rawTerm rawRest)
        (MIBCons (con0 v) encodedTerm encodedRest)

inductive RawBindsFor : List (String × AST) → AST → AST → Prop where
  | nil : RawBindsFor [] MIBNil MIBNil
  | cons (v : String) {term rawTerm encodedTerm rawRest encodedRest : AST}
      {rest : List (String × AST)}
      (henc : encAST? term = some encodedTerm)
      (hterm : RawTermPayload rawTerm encodedTerm)
      (hrest : RawBindsFor rest rawRest encodedRest) :
      RawBindsFor ((v, term) :: rest)
        (MIBCons (con0 v) rawTerm rawRest)
        (MIBCons (con0 v) encodedTerm encodedRest)

theorem MICons_ne_MINil (x xs : AST) : MICons x xs ≠ MINil := by
  intro h
  unfold MICons MINil app con0 at h
  injection h with _hlabel hargs
  cases hargs

theorem rawArgsPayload_nil_eq_aux {rawArgs encodedArgs : AST}
    (h : RawArgsPayload rawArgs encodedArgs)
    (heq : encodedArgs = MINil) :
    rawArgs = MINil := by
  cases h with
  | encoded _ =>
      exact heq
  | consHead _hhead =>
      exfalso
      exact MICons_ne_MINil _ _ heq
  | consTail _htail =>
      exfalso
      exact MICons_ne_MINil _ _ heq

theorem rawArgsPayload_nil_eq {rawArgs : AST}
    (h : RawArgsPayload rawArgs MINil) :
    rawArgs = MINil :=
  rawArgsPayload_nil_eq_aux h rfl

def StepRawSomePayload (encodedRules encodedTerm out : AST) : Prop :=
  ∃ (rawNext encodedOut : AST) (stepFuel normFuel : Nat),
    encAST? out = some encodedOut ∧
    eval pMI stepFuel (miStep encodedRules encodedTerm) = MIStep rawNext ∧
    (∀ k, k < stepFuel →
      StepActiveShape (eval pMI k (miStep encodedRules encodedTerm))) ∧
    eval pMI normFuel rawNext = encodedOut ∧
    IsNormal pMI encodedOut ∧
    RawTermPayload rawNext encodedOut

def ArgsRawSomePayload (encodedRules encodedArgs : AST)
    (out : List AST) : Prop :=
  ∃ (rawArgs encodedOut : AST) (argsFuel normFuel : Nat),
    encASTList? out = some encodedOut ∧
    eval pMI argsFuel (miStepArgs encodedRules encodedArgs) =
      MIArgsStep rawArgs ∧
    (∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs encodedRules encodedArgs))) ∧
    eval pMI normFuel rawArgs = encodedOut ∧
    IsNormal pMI encodedOut ∧
    RawArgsPayload rawArgs encodedOut

def RawMatchFailResult (call : AST) : Prop :=
  ∃ fuel,
    eval pMI fuel call = MIMatchFail ∧
    (∀ k, k < fuel →
      MatchActiveShape (eval pMI k call)) ∧
    IsNormal pMI MIMatchFail

def RawMatchSomeOrFailResult
    (call : AST) (bsOut : List (String × AST)) : Prop :=
  RawMatchFailResult call ∨
    ∃ (rawOut encodedOut : AST) (fuel : Nat),
      encBinds? bsOut = some encodedOut ∧
      RawBindsFor bsOut rawOut encodedOut ∧
      eval pMI fuel call = MIMatchOk rawOut ∧
      ∀ k, k < fuel →
        MatchActiveShape (eval pMI k call)

inductive RawPayloadFor (rws : List RewriteDecl) (encodedRules : AST) :
    AST → AST → AST → Prop where
  | encoded {term encodedTerm : AST}
      (hterm : encAST? term = some encodedTerm)
      (hnorm : IsNormal pMI encodedTerm) :
      RawPayloadFor rws encodedRules term encodedTerm encodedTerm
  | grammar {term rawTerm encodedTerm : AST}
      (hterm : encAST? term = some encodedTerm)
      (hshape : RawTermPayload rawTerm encodedTerm)
      (hroot : rootBaseStep? rws term = none) :
      RawPayloadFor rws encodedRules term rawTerm encodedTerm

theorem stepRawSomePayload_to_rawSome
    {encodedRules encodedTerm out : AST}
    (h : StepRawSomePayload encodedRules encodedTerm out) :
    StepRawSome encodedRules encodedTerm out := by
  unfold StepRawSomePayload at h
  obtain ⟨rawNext, encodedOut, stepFuel, normFuel, hout, hstep,
    hactive, hnorm, houtNorm, _hshape⟩ := h
  exact ⟨rawNext, encodedOut, stepFuel, normFuel, hout, hstep, hactive,
    hnorm, houtNorm⟩

theorem argsRawSomePayload_to_rawSome
    {encodedRules encodedArgs : AST} {out : List AST}
    (h : ArgsRawSomePayload encodedRules encodedArgs out) :
    ArgsRawSome encodedRules encodedArgs out := by
  unfold ArgsRawSomePayload at h
  obtain ⟨rawArgs, encodedOut, argsFuel, normFuel, hout, hstep,
    hactive, hnorm, houtNorm, _hshape⟩ := h
  exact ⟨rawArgs, encodedOut, argsFuel, normFuel, hout, hstep, hactive,
    hnorm, houtNorm⟩

theorem rawPayloadFor_of_term_payload
    (rws : List RewriteDecl) (encodedRules term rawTerm encodedTerm : AST)
    (hterm : encAST? term = some encodedTerm)
    (hshape : RawTermPayload rawTerm encodedTerm)
    (hroot : rootBaseStep? rws term = none) :
    RawPayloadFor rws encodedRules term rawTerm encodedTerm :=
  RawPayloadFor.grammar hterm hshape hroot

theorem rawPayloadFor_term_encoding
    {rws : List RewriteDecl} {encodedRules term rawTerm encodedTerm : AST}
    (hpayload : RawPayloadFor rws encodedRules term rawTerm encodedTerm) :
    encAST? term = some encodedTerm := by
  cases hpayload with
  | encoded hterm _hnorm => exact hterm
  | grammar hterm _hshape _hroot => exact hterm

theorem rawPayloadFor_term_payload
    {rws : List RewriteDecl} {encodedRules term rawTerm encodedTerm : AST}
    (hpayload : RawPayloadFor rws encodedRules term rawTerm encodedTerm) :
    RawTermPayload rawTerm encodedTerm := by
  cases hpayload with
  | encoded _hterm _hnorm => exact RawTermPayload.encoded _
  | grammar _hterm hshape _hroot => exact hshape

theorem rawPayloadFor_encoded_or_root_none
    {rws : List RewriteDecl} {encodedRules term rawTerm encodedTerm : AST}
    (hpayload : RawPayloadFor rws encodedRules term rawTerm encodedTerm) :
    rawTerm = encodedTerm ∨ rootBaseStep? rws term = none := by
  cases hpayload with
  | encoded _hterm _hnorm => exact Or.inl rfl
  | grammar _hterm _hshape hroot => exact Or.inr hroot

mutual
  theorem rawTermPayload_eval_of_normal
      {rawTerm encodedTerm : AST}
      (hpayload : RawTermPayload rawTerm encodedTerm)
      (hnorm : IsNormal pMI encodedTerm) :
      ∃ fuel, eval pMI fuel rawTerm = encodedTerm := by
    match hpayload with
    | RawTermPayload.encoded _ =>
        exact ⟨0, rfl⟩
    | @RawTermPayload.substInst _ _ _ _ _ _ _ _ _ hsubst _hout =>
        exact ⟨_, hsubst⟩
    | @RawTermPayload.app h rawArgs encodedArgs hargs =>
        have hargsNorm : IsNormal pMI encodedArgs :=
          normal_MIApp_args hnorm
        obtain ⟨argsFuel, hargsEval⟩ :=
          rawArgsPayload_eval_of_normal hargs hargsNorm
        exact miApp_args_eval_of h rawArgs encodedArgs argsFuel
          hargsEval hargsNorm

  theorem rawArgsPayload_eval_of_normal
      {rawArgs encodedArgs : AST}
      (hpayload : RawArgsPayload rawArgs encodedArgs)
      (hnorm : IsNormal pMI encodedArgs) :
      ∃ fuel, eval pMI fuel rawArgs = encodedArgs := by
    match hpayload with
    | RawArgsPayload.encoded _ =>
        exact ⟨0, rfl⟩
    | @RawArgsPayload.consHead rawHead encodedHead encodedTail hhead =>
        have hheadNorm : IsNormal pMI encodedHead :=
          normal_MICons_head hnorm
        obtain ⟨headFuel, hheadEval⟩ :=
          rawTermPayload_eval_of_normal hhead hheadNorm
        exact miCons_head_eval_of rawHead encodedHead encodedTail
          headFuel hheadEval hheadNorm
    | @RawArgsPayload.consTail encodedHead rawTail encodedTail htail =>
        have hheadNorm : IsNormal pMI encodedHead :=
          normal_MICons_head hnorm
        have htailNorm : IsNormal pMI encodedTail :=
          normal_MICons_tail hnorm
        obtain ⟨tailFuel, htailEval⟩ :=
          rawArgsPayload_eval_of_normal htail htailNorm
        exact miCons_tail_eval_of encodedHead rawTail encodedTail
          tailFuel hheadNorm htailEval htailNorm
end

theorem rawBindsPayload_eval_of_normal
    {rawBinds encodedBinds : AST}
    (hpayload : RawBindsPayload rawBinds encodedBinds)
    (hnorm : IsNormal pMI encodedBinds) :
    ∃ fuel, eval pMI fuel rawBinds = encodedBinds := by
  cases hpayload with
  | nil =>
      exact ⟨0, rfl⟩
  | @cons v rawTerm encodedTerm rawRest encodedRest hterm hrest =>
      have htermNorm : IsNormal pMI encodedTerm :=
        normal_MIBCons_term hnorm
      have hrestNorm : IsNormal pMI encodedRest :=
        normal_MIBCons_rest hnorm
      obtain ⟨termFuel, htermEval⟩ :=
        rawTermPayload_eval_of_normal hterm htermNorm
      obtain ⟨restFuel, hrestEval⟩ :=
        rawBindsPayload_eval_of_normal hrest hrestNorm
      exact miBCons_eval_of (con0 v) rawTerm encodedTerm rawRest
        encodedRest termFuel restFuel (normal_con0 v) htermEval
        htermNorm hrestEval hrestNorm

theorem rawTermPayload_normal_unique
    {rawTerm encodedA encodedB : AST}
    (ha : RawTermPayload rawTerm encodedA)
    (hAnorm : IsNormal pMI encodedA)
    (hb : RawTermPayload rawTerm encodedB)
    (hBnorm : IsNormal pMI encodedB) :
    encodedA = encodedB := by
  obtain ⟨fuelA, hA⟩ :=
    rawTermPayload_eval_of_normal ha hAnorm
  obtain ⟨fuelB, hB⟩ :=
    rawTermPayload_eval_of_normal hb hBnorm
  exact eval_normal_unique_mi hA hAnorm hB hBnorm

theorem rawTermPayload_beq_true_encoded_eq
    {rawA rawB encodedA encodedB : AST}
    (hbeq : (rawA == rawB) = true)
    (ha : RawTermPayload rawA encodedA)
    (hAnorm : IsNormal pMI encodedA)
    (hb : RawTermPayload rawB encodedB)
    (hBnorm : IsNormal pMI encodedB) :
    encodedA = encodedB := by
  have hrawEq : rawA = rawB := ast_beq_true_eq_mi rawA rawB hbeq
  subst rawB
  exact rawTermPayload_normal_unique ha hAnorm hb hBnorm

theorem rawBindsPayload_refl_of_encBinds? :
    ∀ (bs : List (String × AST)) (encodedBinds : AST),
      encBinds? bs = some encodedBinds →
      RawBindsPayload encodedBinds encodedBinds
  | [], encodedBinds, hbs => by
      simp only [encBinds?] at hbs
      cases hbs
      exact RawBindsPayload.nil
  | (v, t) :: rest, encodedBinds, hbs => by
      simp only [encBinds?] at hbs
      cases ht : encAST? t with
      | none =>
          simp [ht] at hbs
      | some encodedTerm =>
          cases hrest : encBinds? rest with
          | none =>
              simp [ht, hrest] at hbs
          | some encodedRest =>
              simp [ht, hrest] at hbs
              cases hbs
              exact RawBindsPayload.cons v
                (RawTermPayload.encoded encodedTerm)
                (rawBindsPayload_refl_of_encBinds? rest encodedRest hrest)

theorem rawBindsFor_payload
    {bs : List (String × AST)} {rawBinds encodedBinds : AST}
    (hpayload : RawBindsFor bs rawBinds encodedBinds) :
    RawBindsPayload rawBinds encodedBinds := by
  cases hpayload with
  | nil =>
      exact RawBindsPayload.nil
  | cons v _henc hterm hrest =>
      exact RawBindsPayload.cons v hterm
        (rawBindsFor_payload hrest)

theorem rawBindsFor_encoding
    {bs : List (String × AST)} {rawBinds encodedBinds : AST}
    (hpayload : RawBindsFor bs rawBinds encodedBinds) :
    encBinds? bs = some encodedBinds := by
  cases hpayload with
  | nil =>
      rfl
  | @cons v term rawTerm encodedTerm rawRest encodedRest rest henc _hterm hrest =>
      have hrestEnc : encBinds? rest = some encodedRest :=
        rawBindsFor_encoding hrest
      simp only [encBinds?, henc, hrestEnc]

theorem rawBindsFor_refl_of_encBinds? :
    ∀ (bs : List (String × AST)) (encodedBinds : AST),
      encBinds? bs = some encodedBinds →
      RawBindsFor bs encodedBinds encodedBinds
  | [], encodedBinds, hbs => by
      simp only [encBinds?] at hbs
      cases hbs
      exact RawBindsFor.nil
  | (v, t) :: rest, encodedBinds, hbs => by
      simp only [encBinds?] at hbs
      cases ht : encAST? t with
      | none =>
          simp [ht] at hbs
      | some encodedTerm =>
          cases hrest : encBinds? rest with
          | none =>
              simp [ht, hrest] at hbs
          | some encodedRest =>
              simp [ht, hrest] at hbs
              cases hbs
              exact RawBindsFor.cons v ht
                (RawTermPayload.encoded encodedTerm)
                (rawBindsFor_refl_of_encBinds? rest encodedRest hrest)

theorem rawBindsFor_lookup_some (v : String) :
    ∀ {bs : List (String × AST)} {rawBinds encodedBinds : AST}
      {w : String} {term : AST},
      RawBindsFor bs rawBinds encodedBinds →
      List.find? (fun b : String × AST => b.fst == v) bs =
        some (w, term) →
      ∃ (rawTerm encodedTerm : AST) (fuel : Nat),
        encAST? term = some encodedTerm ∧
        RawTermPayload rawTerm encodedTerm ∧
        eval pMI fuel (miLookup (con0 v) rawBinds) = MISome rawTerm ∧
        IsNormal pMI encodedTerm
  | bs, rawBinds, encodedBinds, w, term, hpayload, hfind => by
      induction hpayload generalizing w term with
      | nil =>
          simp only [List.find?] at hfind
          cases hfind
      | @cons w0 term0 rawTerm0 encodedTerm0 rawRest encodedRest rest
          henc hterm hrest ih =>
          simp only [List.find?] at hfind
          by_cases hwv : (w0 == v) = true
          · simp only [hwv] at hfind
            cases hfind
            have hwvEq : w0 = v := beq_iff_eq.mp hwv
            subst w0
            exact ⟨rawTerm0, encodedTerm0, 1, henc, hterm,
              miLookup_hit_named_eval v rawTerm0 rawRest,
              encAST?_some_normal term0 encodedTerm0 henc⟩
          · have hwvFalse : (w0 == v) = false := by
              cases hcmp : (w0 == v) <;> simp [hcmp] at hwv ⊢
            simp only [hwvFalse] at hfind
            obtain ⟨rawTerm, encodedTerm, fuel, hencOld, hpayloadOld,
              hlookupRest, hnormOld⟩ :=
              ih (w := w) (term := term) hfind
            have hvwFalse : (v == w0) = false := by
              simpa [string_beq_symm_mi v w0] using hwvFalse
            have hmiss :
                eval pMI 1
                    (miLookup (con0 v)
                      (MIBCons (con0 w0) rawTerm0 rawRest)) =
                  miLookup (con0 v) rawRest :=
              miLookup_miss_named_eval v w0 hvwFalse rawTerm0 rawRest
            have htotal := eval_trans_mi 1 fuel
              (miLookup (con0 v) (MIBCons (con0 w0) rawTerm0 rawRest))
              (miLookup (con0 v) rawRest)
              (MISome rawTerm) hmiss hlookupRest
            exact ⟨rawTerm, encodedTerm, 1 + fuel, hencOld,
              hpayloadOld, htotal, hnormOld⟩

theorem rawBindsFor_lookup_none (v : String) :
    ∀ {bs : List (String × AST)} {rawBinds encodedBinds : AST},
      RawBindsFor bs rawBinds encodedBinds →
      List.find? (fun b : String × AST => b.fst == v) bs = none →
      ∃ fuel, eval pMI fuel (miLookup (con0 v) rawBinds) = MINone
  | bs, rawBinds, encodedBinds, hpayload, hfind => by
      induction hpayload with
      | nil =>
          exact ⟨1, by simp only [eval, os_miLookup_nil_data]⟩
      | @cons w0 term0 rawTerm0 encodedTerm0 rawRest encodedRest rest
          henc hterm hrest ih =>
          simp only [List.find?] at hfind
          by_cases hwv : (w0 == v) = true
          · simp only [hwv] at hfind
            cases hfind
          · have hwvFalse : (w0 == v) = false := by
              cases hcmp : (w0 == v) <;> simp [hcmp] at hwv ⊢
            simp only [hwvFalse] at hfind
            obtain ⟨fuel, hlookupRest⟩ := ih hfind
            have hvwFalse : (v == w0) = false := by
              simpa [string_beq_symm_mi v w0] using hwvFalse
            have hmiss :
                eval pMI 1
                    (miLookup (con0 v)
                      (MIBCons (con0 w0) rawTerm0 rawRest)) =
                  miLookup (con0 v) rawRest :=
              miLookup_miss_named_eval v w0 hvwFalse rawTerm0 rawRest
            have htotal := eval_trans_mi 1 fuel
              (miLookup (con0 v) (MIBCons (con0 w0) rawTerm0 rawRest))
              (miLookup (con0 v) rawRest)
              MINone hmiss hlookupRest
            exact ⟨1 + fuel, htotal⟩

theorem miMatchVarK_lookup_rawBindsFor_none_first_result (v : String)
    (term wholeBs : AST)
    (hterm : IsNormal pMI term) (hwhole : IsNormal pMI wholeBs) :
    ∀ {bs : List (String × AST)} {rawBinds encodedBinds : AST},
      RawBindsFor bs rawBinds encodedBinds →
      List.find? (fun b : String × AST => b.fst == v) bs = none →
      ∃ fuel,
        eval pMI fuel
          (miMatchVarK (con0 v) term wholeBs
            (miLookup (con0 v) rawBinds)) =
          miMatchVarK (con0 v) term wholeBs MINone ∧
        (∀ k, k < fuel →
          MatchActiveShape
            (eval pMI k
              (miMatchVarK (con0 v) term wholeBs
                (miLookup (con0 v) rawBinds)))) := by
  intro bs rawBinds encodedBinds hpayload hfind
  induction hpayload with
  | nil =>
      refine ⟨1, ?_, ?_⟩
      · simp only [eval, os_miMatchVarK_lookup_nil_arg, hterm, hwhole]
      · exact match_active_fuel_one_mi
          (MatchActiveShape.matchVarK (con0 v) term wholeBs
            (miLookup (con0 v) MIBNil))
  | @cons w0 term0 rawTerm0 encodedTerm0 rawRest encodedRest rest
      henc hrawTerm hrest ih =>
      simp only [List.find?] at hfind
      by_cases hwv : (w0 == v) = true
      · simp only [hwv] at hfind
        cases hfind
      · have hwvFalse : (w0 == v) = false := by
          cases hcmp : (w0 == v) <;> simp [hcmp] at hwv ⊢
        simp only [hwvFalse] at hfind
        have hvwFalse : (v == w0) = false := by
          simpa [string_beq_symm_mi v w0] using hwvFalse
        have hmiss :
            eval pMI 1
              (miMatchVarK (con0 v) term wholeBs
                (miLookup (con0 v)
                  (MIBCons (con0 w0) rawTerm0 rawRest))) =
              miMatchVarK (con0 v) term wholeBs
                (miLookup (con0 v) rawRest) := by
          simp only [eval, os_miMatchVarK_lookup_miss_arg,
            hvwFalse, hterm, hwhole]
        obtain ⟨tailFuel, htail, htailActive⟩ := ih hfind
        have htotal := eval_trans_mi 1 tailFuel
          (miMatchVarK (con0 v) term wholeBs
            (miLookup (con0 v)
              (MIBCons (con0 w0) rawTerm0 rawRest)))
          (miMatchVarK (con0 v) term wholeBs
            (miLookup (con0 v) rawRest))
          (miMatchVarK (con0 v) term wholeBs MINone)
          hmiss htail
        refine ⟨1 + tailFuel, htotal, ?_⟩
        apply match_active_append_mi 1 tailFuel hmiss
        · exact match_active_fuel_one_mi
            (MatchActiveShape.matchVarK (con0 v) term wholeBs
              (miLookup (con0 v)
                (MIBCons (con0 w0) rawTerm0 rawRest)))
        · exact htailActive

theorem miMatchVarK_lookup_rawBindsFor_some_first_result (v : String)
    (term wholeBs : AST)
    (hterm : IsNormal pMI term) (hwhole : IsNormal pMI wholeBs) :
    ∀ {bs : List (String × AST)} {rawBinds encodedBinds : AST}
      {w : String} {sourceTerm : AST},
      RawBindsFor bs rawBinds encodedBinds →
      List.find? (fun b : String × AST => b.fst == v) bs =
        some (w, sourceTerm) →
      ∃ (rawOld encodedOld : AST) (fuel : Nat),
        encAST? sourceTerm = some encodedOld ∧
        RawTermPayload rawOld encodedOld ∧
        eval pMI fuel
          (miMatchVarK (con0 v) term wholeBs
            (miLookup (con0 v) rawBinds)) =
          miMatchVarK (con0 v) term wholeBs (MISome rawOld) ∧
        (∀ k, k < fuel →
          MatchActiveShape
            (eval pMI k
              (miMatchVarK (con0 v) term wholeBs
                (miLookup (con0 v) rawBinds)))) ∧
        IsNormal pMI encodedOld := by
  intro bs rawBinds encodedBinds w sourceTerm hpayload hfind
  induction hpayload generalizing w sourceTerm with
  | nil =>
      simp only [List.find?] at hfind
      cases hfind
  | @cons w0 term0 rawTerm0 encodedTerm0 rawRest encodedRest rest
      henc hrawTerm hrest ih =>
      simp only [List.find?] at hfind
      by_cases hwv : (w0 == v) = true
      · simp only [hwv] at hfind
        cases hfind
        refine ⟨rawTerm0, encodedTerm0, 1, henc, hrawTerm, ?_, ?_,
          encAST?_some_normal term0 encodedTerm0 henc⟩
        · have hwvEq : w0 = v := beq_iff_eq.mp hwv
          subst w0
          simp only [eval, os_miMatchVarK_lookup_hit_arg, hterm, hwhole]
        · exact match_active_fuel_one_mi
            (MatchActiveShape.matchVarK (con0 v) term wholeBs
              (miLookup (con0 v)
                (MIBCons (con0 w0) rawTerm0 rawRest)))
      · have hwvFalse : (w0 == v) = false := by
          cases hcmp : (w0 == v) <;> simp [hcmp] at hwv ⊢
        simp only [hwvFalse] at hfind
        have hvwFalse : (v == w0) = false := by
          simpa [string_beq_symm_mi v w0] using hwvFalse
        have hmiss :
            eval pMI 1
              (miMatchVarK (con0 v) term wholeBs
                (miLookup (con0 v)
                  (MIBCons (con0 w0) rawTerm0 rawRest))) =
              miMatchVarK (con0 v) term wholeBs
                (miLookup (con0 v) rawRest) := by
          simp only [eval, os_miMatchVarK_lookup_miss_arg,
            hvwFalse, hterm, hwhole]
        obtain ⟨rawOld, encodedOld, tailFuel, holdEnc, hrawOld,
          htail, htailActive, holdNorm⟩ := ih hfind
        have htotal := eval_trans_mi 1 tailFuel
          (miMatchVarK (con0 v) term wholeBs
            (miLookup (con0 v)
              (MIBCons (con0 w0) rawTerm0 rawRest)))
          (miMatchVarK (con0 v) term wholeBs
            (miLookup (con0 v) rawRest))
          (miMatchVarK (con0 v) term wholeBs (MISome rawOld))
          hmiss htail
        refine ⟨rawOld, encodedOld, 1 + tailFuel, holdEnc, hrawOld,
          htotal, ?_, holdNorm⟩
        apply match_active_append_mi 1 tailFuel hmiss
        · exact match_active_fuel_one_mi
            (MatchActiveShape.matchVarK (con0 v) term wholeBs
              (miLookup (con0 v)
                (MIBCons (con0 w0) rawTerm0 rawRest)))
        · exact htailActive

theorem matchPat_var_none_find?_some_beq_false
    (v : String) (term : AST) (bs : List (String × AST))
    (hmatch : AST.matchPat (.var (.base v)) term bs = none) :
    ∃ (w : String) (old : AST),
      List.find? (fun b : String × AST => b.fst == v) bs =
        some (w, old) ∧
      (old == term) = false := by
  simp only [AST.matchPat] at hmatch
  cases hfind : List.find? (fun b : String × AST => b.fst == v) bs with
  | none =>
      simp only [hfind] at hmatch
      cases hmatch
  | some pair =>
      rcases pair with ⟨w, old⟩
      simp only [hfind] at hmatch
      by_cases hold : (old == term) = true
      · simp only [hold, if_true] at hmatch
        cases hmatch
      · have holdFalse : (old == term) = false := by
          cases hcmp : (old == term) <;> simp [hcmp] at hold ⊢
        exact ⟨w, old, rfl, holdFalse⟩

theorem rawBindsFor_var_none_lookup_conflict
    (v : String) (term encodedTerm rawBinds encodedBinds : AST)
    (bs : List (String × AST))
    (hterm : encAST? term = some encodedTerm)
    (hpayload : RawBindsFor bs rawBinds encodedBinds)
    (hmatch : AST.matchPat (.var (.base v)) term bs = none) :
    ∃ (w : String) (old rawOld encodedOld : AST) (fuel : Nat),
      List.find? (fun b : String × AST => b.fst == v) bs =
        some (w, old) ∧
      encAST? old = some encodedOld ∧
      RawTermPayload rawOld encodedOld ∧
      eval pMI fuel (miLookup (con0 v) rawBinds) = MISome rawOld ∧
      IsNormal pMI encodedOld ∧
      (encodedTerm == rawOld) = false := by
  obtain ⟨w, old, hfind, holdNe⟩ :=
    matchPat_var_none_find?_some_beq_false v term bs hmatch
  obtain ⟨rawOld, encodedOld, fuel, holdEnc, hrawOld,
    hlookup, holdNorm⟩ :=
    rawBindsFor_lookup_some v (w := w) (term := old) hpayload hfind
  have hencodedNorm : IsNormal pMI encodedTerm :=
    encAST?_some_normal term encodedTerm hterm
  have hneq : (encodedTerm == rawOld) = false := by
    cases hcmp : (encodedTerm == rawOld) with
    | false => rfl
    | true =>
        have hrawEq : rawOld = encodedTerm := by
          exact (ast_beq_true_eq_mi encodedTerm rawOld hcmp).symm
        subst rawOld
        have hencEq : encodedOld = encodedTerm :=
          rawTermPayload_normal_unique hrawOld holdNorm
            (RawTermPayload.encoded encodedTerm) hencodedNorm
        subst encodedOld
        have holdEq : old = term :=
          encAST?_inj old term encodedTerm holdEnc hterm
        subst old
        have hself : (term == term) = true := beq_ast_self term
        simp only [hself] at holdNe
        exact holdNe
  exact ⟨w, old, rawOld, encodedOld, fuel, hfind, holdEnc, hrawOld,
    hlookup, holdNorm, hneq⟩

theorem miMatchVarK_rawBindsFor_var_none_eval
    (v : String) :
    ∀ {bs : List (String × AST)}
      {rawLookup encodedLookup term encodedTerm wholeBs : AST},
      encAST? term = some encodedTerm →
      IsNormal pMI wholeBs →
      RawBindsFor bs rawLookup encodedLookup →
      AST.matchPat (.var (.base v)) term bs = none →
      ∃ fuel,
        eval pMI fuel
          (miMatchVarK (con0 v) encodedTerm wholeBs
            (miLookup (con0 v) rawLookup)) =
          MIMatchFail
  | bs, rawLookup, encodedLookup, term, encodedTerm, wholeBs,
      hterm, hwhole, hpayload, hmatch => by
      induction hpayload generalizing term encodedTerm wholeBs with
      | nil =>
          simp only [AST.matchPat, List.find?] at hmatch
          cases hmatch
      | @cons w0 term0 rawTerm0 encodedTerm0 rawRest encodedRest rest
          henc hrawTerm hrest ih =>
          simp only [AST.matchPat, List.find?] at hmatch
          by_cases hwv : (w0 == v) = true
          · simp only [hwv] at hmatch
            by_cases hold : (term0 == term) = true
            · simp only [hold, if_true] at hmatch
              cases hmatch
            · have holdFalse : (term0 == term) = false := by
                cases hcmp : (term0 == term) <;> simp [hcmp] at hold ⊢
              have hneq : (encodedTerm == rawTerm0) = false := by
                cases hcmp : (encodedTerm == rawTerm0) with
                | false => rfl
                | true =>
                    have hrawEq : rawTerm0 = encodedTerm :=
                      (ast_beq_true_eq_mi encodedTerm rawTerm0 hcmp).symm
                    subst rawTerm0
                    have hencodedTermNorm : IsNormal pMI encodedTerm :=
                      encAST?_some_normal term encodedTerm hterm
                    have hencEq : encodedTerm0 = encodedTerm :=
                      rawTermPayload_normal_unique hrawTerm
                        (encAST?_some_normal term0 encodedTerm0 henc)
                        (RawTermPayload.encoded encodedTerm)
                        hencodedTermNorm
                    subst encodedTerm0
                    have hsourceEq : term0 = term :=
                      encAST?_inj term0 term encodedTerm henc hterm
                    subst term0
                    have hself : (term == term) = true := beq_ast_self term
                    simp only [hself] at holdFalse
                    exact holdFalse
              have hwvEq : w0 = v := beq_iff_eq.mp hwv
              subst w0
              have hlookupStep :
                  eval pMI 1
                    (miMatchVarK (con0 v) encodedTerm wholeBs
                      (miLookup (con0 v)
                        (MIBCons (con0 v) rawTerm0 rawRest))) =
                    miMatchVarK (con0 v) encodedTerm wholeBs
                      (MISome rawTerm0) := by
                simp only [eval,
                  os_miMatchVarK_lookup_hit_arg, hwhole,
                  encAST?_some_normal term encodedTerm hterm]
              have hdiff :
                  eval pMI 1
                    (miMatchVarK (con0 v) encodedTerm wholeBs
                      (MISome rawTerm0)) =
                    MIMatchFail := by
                simp only [eval, os_miMatchVarK_diff_general, hneq]
              exact ⟨2, eval_trans_mi 1 1
                (miMatchVarK (con0 v) encodedTerm wholeBs
                  (miLookup (con0 v)
                    (MIBCons (con0 v) rawTerm0 rawRest)))
                (miMatchVarK (con0 v) encodedTerm wholeBs
                  (MISome rawTerm0))
                MIMatchFail hlookupStep hdiff⟩
          · have hwvFalse : (w0 == v) = false := by
              cases hcmp : (w0 == v) <;> simp [hcmp] at hwv ⊢
            simp only [hwvFalse] at hmatch
            have hmatchRest :
                AST.matchPat (.var (.base v)) term rest = none := by
              simp only [AST.matchPat]
              cases hfindRest :
                  List.find? (fun b : String × AST => b.fst == v) rest with
              | none =>
                  simp only [hfindRest] at hmatch
                  cases hmatch
              | some pair =>
                  rcases pair with ⟨wOld, old⟩
                  simp only [hfindRest] at hmatch
                  by_cases hold : (old == term) = true
                  · simp only [hold, if_true] at hmatch
                    cases hmatch
                  · have holdFalse : (old == term) = false := by
                      cases hcmp : (old == term) <;> simp [hcmp] at hold ⊢
                    simp only [holdFalse, Bool.false_eq_true, if_false]
            obtain ⟨tailFuel, htail⟩ :=
              ih (term := term) (encodedTerm := encodedTerm)
                (wholeBs := wholeBs) hterm hwhole hmatchRest
            have hvwFalse : (v == w0) = false := by
              simpa [string_beq_symm_mi v w0] using hwvFalse
            have hmiss :
                eval pMI 1
                  (miMatchVarK (con0 v) encodedTerm wholeBs
                    (miLookup (con0 v)
                      (MIBCons (con0 w0) rawTerm0 rawRest))) =
                  miMatchVarK (con0 v) encodedTerm wholeBs
                    (miLookup (con0 v) rawRest) := by
              simp only [eval, os_miMatchVarK_lookup_miss_arg,
                hvwFalse, hwhole, encAST?_some_normal term encodedTerm hterm]
            exact ⟨1 + tailFuel, eval_trans_mi 1 tailFuel
              (miMatchVarK (con0 v) encodedTerm wholeBs
                (miLookup (con0 v)
                  (MIBCons (con0 w0) rawTerm0 rawRest)))
              (miMatchVarK (con0 v) encodedTerm wholeBs
                (miLookup (con0 v) rawRest))
              MIMatchFail hmiss htail⟩

theorem miMatchVarK_rawBindsFor_var_some_or_fail_first_result
    (v : String) {bs : List (String × AST)}
    {rawBinds encodedBinds sourceTerm encodedTerm : AST}
    {bsOut : List (String × AST)}
    (hterm : encAST? sourceTerm = some encodedTerm)
    (hpayload : RawBindsFor bs rawBinds encodedBinds)
    (hmatch : AST.matchPat (.var (.base v)) sourceTerm bs = some bsOut) :
    RawMatchSomeOrFailResult
      (miMatchVarK (con0 v) encodedTerm encodedBinds
        (miLookup (con0 v) rawBinds))
      bsOut := by
  have hbs : encBinds? bs = some encodedBinds :=
    rawBindsFor_encoding hpayload
  have htermNorm : IsNormal pMI encodedTerm :=
    encAST?_some_normal sourceTerm encodedTerm hterm
  have hbindsNorm : IsNormal pMI encodedBinds :=
    encBinds?_some_normal bs encodedBinds hbs
  simp only [AST.matchPat] at hmatch
  cases hfind : List.find? (fun b : String × AST => b.fst == v) bs with
  | none =>
      simp only [hfind] at hmatch
      cases hmatch
      obtain ⟨lookupFuel, hlookup, hlookupActive⟩ :=
        miMatchVarK_lookup_rawBindsFor_none_first_result v encodedTerm
          encodedBinds htermNorm hbindsNorm hpayload hfind
      have hfire :
          eval pMI 1
            (miMatchVarK (con0 v) encodedTerm encodedBinds MINone) =
          MIMatchOk (MIBCons (con0 v) encodedTerm encodedBinds) := by
        simp only [eval, os_miMatchVarK_none_general]
      have htotal := eval_trans_mi lookupFuel 1
        (miMatchVarK (con0 v) encodedTerm encodedBinds
          (miLookup (con0 v) rawBinds))
        (miMatchVarK (con0 v) encodedTerm encodedBinds MINone)
        (MIMatchOk (MIBCons (con0 v) encodedTerm encodedBinds))
        hlookup hfire
      right
      refine ⟨MIBCons (con0 v) encodedTerm encodedBinds,
        MIBCons (con0 v) encodedTerm encodedBinds,
        lookupFuel + 1, ?_, ?_, htotal, ?_⟩
      · simp only [encBinds?, hterm, hbs]
      · exact RawBindsFor.cons v hterm
          (RawTermPayload.encoded encodedTerm)
          (rawBindsFor_refl_of_encBinds? bs encodedBinds hbs)
      · apply match_active_append_mi lookupFuel 1 hlookup
        · exact hlookupActive
        · exact match_active_fuel_one_mi
            (MatchActiveShape.matchVarK (con0 v) encodedTerm encodedBinds
              MINone)
  | some pair =>
      rcases pair with ⟨w, old⟩
      simp only [hfind] at hmatch
      by_cases hold : (old == sourceTerm) = true
      · simp only [hold, if_true] at hmatch
        cases hmatch
        obtain ⟨rawOld, encodedOld, lookupFuel, holdEnc, hrawOld,
          hlookup, hlookupActive, _holdNorm⟩ :=
          miMatchVarK_lookup_rawBindsFor_some_first_result v
            encodedTerm encodedBinds htermNorm hbindsNorm hpayload hfind
        by_cases hsame : (encodedTerm == rawOld) = true
        · have hfire :
              eval pMI 1
                (miMatchVarK (con0 v) encodedTerm encodedBinds
                  (MISome rawOld)) =
              MIMatchOk encodedBinds := by
            simp only [eval, os_miMatchVarK_same_on_beq_named, hsame]
          have htotal := eval_trans_mi lookupFuel 1
            (miMatchVarK (con0 v) encodedTerm encodedBinds
              (miLookup (con0 v) rawBinds))
            (miMatchVarK (con0 v) encodedTerm encodedBinds
              (MISome rawOld))
            (MIMatchOk encodedBinds) hlookup hfire
          right
          refine ⟨encodedBinds, encodedBinds, lookupFuel + 1,
            hbs, ?_, htotal, ?_⟩
          · exact rawBindsFor_refl_of_encBinds? bs encodedBinds hbs
          · apply match_active_append_mi lookupFuel 1 hlookup
            · exact hlookupActive
            · exact match_active_fuel_one_mi
                (MatchActiveShape.matchVarK (con0 v) encodedTerm encodedBinds
                  (MISome rawOld))
        · have hdiff : (encodedTerm == rawOld) = false := by
            cases hcmp : (encodedTerm == rawOld) <;>
              simp [hcmp] at hsame ⊢
          have hfire :
              eval pMI 1
                (miMatchVarK (con0 v) encodedTerm encodedBinds
                  (MISome rawOld)) =
              MIMatchFail := by
            simp only [eval, os_miMatchVarK_diff_general, hdiff]
          have htotal := eval_trans_mi lookupFuel 1
            (miMatchVarK (con0 v) encodedTerm encodedBinds
              (miLookup (con0 v) rawBinds))
            (miMatchVarK (con0 v) encodedTerm encodedBinds
              (MISome rawOld))
            MIMatchFail hlookup hfire
          left
          refine ⟨lookupFuel + 1, htotal, ?_, normal_MIMatchFail⟩
          apply match_active_append_mi lookupFuel 1 hlookup
          · exact hlookupActive
          · exact match_active_fuel_one_mi
              (MatchActiveShape.matchVarK (con0 v) encodedTerm encodedBinds
                (MISome rawOld))
      · have holdFalse : (old == sourceTerm) = false := by
          cases hcmp : (old == sourceTerm) <;> simp [hcmp] at hold ⊢
        simp only [holdFalse, Bool.false_eq_true, if_false] at hmatch
        cases hmatch

theorem miMatchVarK_rawBindsFor_var_none_first_result
    (v : String) :
    ∀ {bs : List (String × AST)}
      {rawLookup encodedLookup term encodedTerm wholeBs : AST},
      encAST? term = some encodedTerm →
      IsNormal pMI wholeBs →
      RawBindsFor bs rawLookup encodedLookup →
      AST.matchPat (.var (.base v)) term bs = none →
      ∃ fuel,
        eval pMI fuel
          (miMatchVarK (con0 v) encodedTerm wholeBs
            (miLookup (con0 v) rawLookup)) =
          MIMatchFail ∧
        (∀ k, k < fuel →
          MatchActiveShape
            (eval pMI k
              (miMatchVarK (con0 v) encodedTerm wholeBs
                (miLookup (con0 v) rawLookup)))) ∧
        IsNormal pMI MIMatchFail
  | bs, rawLookup, encodedLookup, term, encodedTerm, wholeBs,
      hterm, hwhole, hpayload, hmatch => by
      induction hpayload generalizing term encodedTerm wholeBs with
      | nil =>
          simp only [AST.matchPat, List.find?] at hmatch
          cases hmatch
      | @cons w0 term0 rawTerm0 encodedTerm0 rawRest encodedRest rest
          henc hrawTerm hrest ih =>
          simp only [AST.matchPat, List.find?] at hmatch
          by_cases hwv : (w0 == v) = true
          · simp only [hwv] at hmatch
            by_cases hold : (term0 == term) = true
            · simp only [hold, if_true] at hmatch
              cases hmatch
            · have holdFalse : (term0 == term) = false := by
                cases hcmp : (term0 == term) <;> simp [hcmp] at hold ⊢
              have hneq : (encodedTerm == rawTerm0) = false := by
                cases hcmp : (encodedTerm == rawTerm0) with
                | false => rfl
                | true =>
                    have hrawEq : rawTerm0 = encodedTerm :=
                      (ast_beq_true_eq_mi encodedTerm rawTerm0 hcmp).symm
                    subst rawTerm0
                    have hencodedTermNorm : IsNormal pMI encodedTerm :=
                      encAST?_some_normal term encodedTerm hterm
                    have hencEq : encodedTerm0 = encodedTerm :=
                      rawTermPayload_normal_unique hrawTerm
                        (encAST?_some_normal term0 encodedTerm0 henc)
                        (RawTermPayload.encoded encodedTerm)
                        hencodedTermNorm
                    subst encodedTerm0
                    have hsourceEq : term0 = term :=
                      encAST?_inj term0 term encodedTerm henc hterm
                    subst term0
                    have hself : (term == term) = true := beq_ast_self term
                    simp only [hself] at holdFalse
                    exact holdFalse
              have hwvEq : w0 = v := beq_iff_eq.mp hwv
              subst w0
              have hlookupStep :
                  eval pMI 1
                    (miMatchVarK (con0 v) encodedTerm wholeBs
                      (miLookup (con0 v)
                        (MIBCons (con0 v) rawTerm0 rawRest))) =
                    miMatchVarK (con0 v) encodedTerm wholeBs
                      (MISome rawTerm0) := by
                simp only [eval,
                  os_miMatchVarK_lookup_hit_arg, hwhole,
                  encAST?_some_normal term encodedTerm hterm]
              have hdiff :
                  eval pMI 1
                    (miMatchVarK (con0 v) encodedTerm wholeBs
                      (MISome rawTerm0)) =
                    MIMatchFail := by
                simp only [eval, os_miMatchVarK_diff_general, hneq]
              have htotal := eval_trans_mi 1 1
                (miMatchVarK (con0 v) encodedTerm wholeBs
                  (miLookup (con0 v)
                    (MIBCons (con0 v) rawTerm0 rawRest)))
                (miMatchVarK (con0 v) encodedTerm wholeBs
                  (MISome rawTerm0))
                MIMatchFail hlookupStep hdiff
              refine ⟨2, htotal, ?_, normal_MIMatchFail⟩
              intro k hk
              have hkcases : k = 0 ∨ k = 1 := by omega
              rcases hkcases with rfl | rfl
              · simp only [eval]
                exact MatchActiveShape.matchVarK (con0 v) encodedTerm wholeBs
                  (miLookup (con0 v)
                    (MIBCons (con0 v) rawTerm0 rawRest))
              · simp only [eval, os_miMatchVarK_lookup_hit_arg, hwhole,
                  encAST?_some_normal term encodedTerm hterm]
                exact MatchActiveShape.matchVarK (con0 v) encodedTerm wholeBs
                  (MISome rawTerm0)
          · have hwvFalse : (w0 == v) = false := by
              cases hcmp : (w0 == v) <;> simp [hcmp] at hwv ⊢
            simp only [hwvFalse] at hmatch
            have hmatchRest :
                AST.matchPat (.var (.base v)) term rest = none := by
              simp only [AST.matchPat]
              cases hfindRest :
                  List.find? (fun b : String × AST => b.fst == v) rest with
              | none =>
                  simp only [hfindRest] at hmatch
                  cases hmatch
              | some pair =>
                  rcases pair with ⟨wOld, old⟩
                  simp only [hfindRest] at hmatch
                  by_cases hold : (old == term) = true
                  · simp only [hold, if_true] at hmatch
                    cases hmatch
                  · have holdFalse : (old == term) = false := by
                      cases hcmp : (old == term) <;> simp [hcmp] at hold ⊢
                    simp only [holdFalse, Bool.false_eq_true, if_false]
            obtain ⟨tailFuel, htail, htailActive, htailNorm⟩ :=
              ih (term := term) (encodedTerm := encodedTerm)
                (wholeBs := wholeBs) hterm hwhole hmatchRest
            have hvwFalse : (v == w0) = false := by
              simpa [string_beq_symm_mi v w0] using hwvFalse
            have hmiss :
                eval pMI 1
                  (miMatchVarK (con0 v) encodedTerm wholeBs
                    (miLookup (con0 v)
                      (MIBCons (con0 w0) rawTerm0 rawRest))) =
                  miMatchVarK (con0 v) encodedTerm wholeBs
                    (miLookup (con0 v) rawRest) := by
              simp only [eval, os_miMatchVarK_lookup_miss_arg,
                hvwFalse, hwhole, encAST?_some_normal term encodedTerm hterm]
            have htotal := eval_trans_mi 1 tailFuel
              (miMatchVarK (con0 v) encodedTerm wholeBs
                (miLookup (con0 v)
                  (MIBCons (con0 w0) rawTerm0 rawRest)))
              (miMatchVarK (con0 v) encodedTerm wholeBs
                (miLookup (con0 v) rawRest))
              MIMatchFail hmiss htail
            refine ⟨1 + tailFuel, htotal, ?_, htailNorm⟩
            apply match_active_append_mi 1 tailFuel hmiss
            · exact match_active_fuel_one_mi
                (MatchActiveShape.matchVarK (con0 v) encodedTerm wholeBs
                  (miLookup (con0 v)
                    (MIBCons (con0 w0) rawTerm0 rawRest)))
            · exact htailActive

theorem miMatchVarK_rawBindsFor_var_none_eval_raw_whole
    (v : String) {bs : List (String × AST)}
    {rawBinds encodedBinds term encodedTerm : AST}
    (hterm : encAST? term = some encodedTerm)
    (hpayload : RawBindsFor bs rawBinds encodedBinds)
    (hmatch : AST.matchPat (.var (.base v)) term bs = none) :
    ∃ fuel,
      eval pMI fuel
        (miMatchVarK (con0 v) encodedTerm rawBinds
          (miLookup (con0 v) rawBinds)) =
        MIMatchFail := by
  have hbs : encBinds? bs = some encodedBinds :=
    rawBindsFor_encoding hpayload
  have hencodedBinds : IsNormal pMI encodedBinds :=
    encBinds?_some_normal bs encodedBinds hbs
  obtain ⟨bindFuel, hbindsEval⟩ :=
    rawBindsPayload_eval_of_normal
      (rawBindsFor_payload hpayload) hencodedBinds
  obtain ⟨ctxFuel, hctx⟩ :=
    cong_eval_mi
      (fun z => miMatchVarK (con0 v) encodedTerm z
        (miLookup (con0 v) rawBinds))
      (fun s s' hstep =>
        os_miMatchVarK_bs_lookup_arg_step v encodedTerm s s'
          rawBinds (encAST?_some_normal term encodedTerm hterm) hstep)
      bindFuel hbindsEval hencodedBinds
  obtain ⟨tailFuel, htail⟩ :=
    miMatchVarK_rawBindsFor_var_none_eval v hterm hencodedBinds
      hpayload hmatch
  exact ⟨ctxFuel + tailFuel,
    eval_trans_mi ctxFuel tailFuel
      (miMatchVarK (con0 v) encodedTerm rawBinds
        (miLookup (con0 v) rawBinds))
      (miMatchVarK (con0 v) encodedTerm encodedBinds
        (miLookup (con0 v) rawBinds))
      MIMatchFail hctx htail⟩

theorem miMatchVarK_rawBindsFor_var_none_first_result_raw_whole
    (v : String) {bs : List (String × AST)}
    {rawBinds encodedBinds term encodedTerm : AST}
    (hterm : encAST? term = some encodedTerm)
    (hpayload : RawBindsFor bs rawBinds encodedBinds)
    (hmatch : AST.matchPat (.var (.base v)) term bs = none) :
    ∃ fuel,
      eval pMI fuel
        (miMatchVarK (con0 v) encodedTerm rawBinds
          (miLookup (con0 v) rawBinds)) =
        MIMatchFail ∧
      (∀ k, k < fuel →
        MatchActiveShape
          (eval pMI k
            (miMatchVarK (con0 v) encodedTerm rawBinds
              (miLookup (con0 v) rawBinds)))) ∧
      IsNormal pMI MIMatchFail := by
  have hbs : encBinds? bs = some encodedBinds :=
    rawBindsFor_encoding hpayload
  have hencodedBinds : IsNormal pMI encodedBinds :=
    encBinds?_some_normal bs encodedBinds hbs
  obtain ⟨bindFuel, hbindsEval⟩ :=
    rawBindsPayload_eval_of_normal
      (rawBindsFor_payload hpayload) hencodedBinds
  let F : AST → AST :=
    fun z => miMatchVarK (con0 v) encodedTerm z
      (miLookup (con0 v) rawBinds)
  obtain ⟨ctxFuel, hctx, hctxActive⟩ :=
    cong_eval_to_match_active_with_guard_mi F
      (fun z => MatchActiveShape.matchVarK (con0 v) encodedTerm z
        (miLookup (con0 v) rawBinds))
      (fun s s' hstep =>
        os_miMatchVarK_bs_lookup_arg_step v encodedTerm s s'
          rawBinds (encAST?_some_normal term encodedTerm hterm) hstep)
      bindFuel hbindsEval hencodedBinds
  obtain ⟨tailFuel, htail, htailActive, htailNorm⟩ :=
    miMatchVarK_rawBindsFor_var_none_first_result v hterm
      hencodedBinds hpayload hmatch
  have htotal := eval_trans_mi ctxFuel tailFuel
    (miMatchVarK (con0 v) encodedTerm rawBinds
      (miLookup (con0 v) rawBinds))
    (miMatchVarK (con0 v) encodedTerm encodedBinds
      (miLookup (con0 v) rawBinds))
    MIMatchFail
    (by simpa only [F] using hctx) htail
  refine ⟨ctxFuel + tailFuel, htotal, ?_, htailNorm⟩
  apply match_active_append_mi ctxFuel tailFuel
    (by simpa only [F] using hctx)
  · simpa only [F] using hctxActive
  · exact htailActive

theorem miMatch_var_rawBindsFor_source_none_eval
    (v : String) {bs : List (String × AST)}
    {rawBinds encodedBinds term encodedTerm : AST}
    (hterm : encAST? term = some encodedTerm)
    (hpayload : RawBindsFor bs rawBinds encodedBinds)
    (hmatch : AST.matchPat (.var (.base v)) term bs = none) :
    ∃ fuel,
      eval pMI fuel (miMatch (MIVar v) encodedTerm rawBinds) =
        MIMatchFail := by
  obtain ⟨tailFuel, htail⟩ :=
    miMatchVarK_rawBindsFor_var_none_eval_raw_whole v hterm
      hpayload hmatch
  have hdispatch :
      eval pMI 2 (miMatch (MIVar v) encodedTerm rawBinds) =
        miMatchVarK (con0 v) encodedTerm rawBinds
          (miLookup (con0 v) rawBinds) := by
    simp only [eval, MIVar, os_miMatch_var_data, os_miMatchVar]
  exact ⟨2 + tailFuel,
    eval_trans_mi 2 tailFuel
      (miMatch (MIVar v) encodedTerm rawBinds)
      (miMatchVarK (con0 v) encodedTerm rawBinds
        (miLookup (con0 v) rawBinds))
      MIMatchFail hdispatch htail⟩

theorem miMatch_var_rawBindsFor_source_none_first_result
    (v : String) {bs : List (String × AST)}
    {rawBinds encodedBinds term encodedTerm : AST}
    (hterm : encAST? term = some encodedTerm)
    (hpayload : RawBindsFor bs rawBinds encodedBinds)
    (hmatch : AST.matchPat (.var (.base v)) term bs = none) :
    ∃ fuel,
      eval pMI fuel (miMatch (MIVar v) encodedTerm rawBinds) =
        MIMatchFail ∧
      (∀ k, k < fuel →
        MatchActiveShape
          (eval pMI k (miMatch (MIVar v) encodedTerm rawBinds))) ∧
      IsNormal pMI MIMatchFail := by
  obtain ⟨tailFuel, htail, htailActive, htailNorm⟩ :=
    miMatchVarK_rawBindsFor_var_none_first_result_raw_whole v
      hterm hpayload hmatch
  have hdispatch :
      eval pMI 2 (miMatch (MIVar v) encodedTerm rawBinds) =
        miMatchVarK (con0 v) encodedTerm rawBinds
          (miLookup (con0 v) rawBinds) := by
    simp only [eval, MIVar, os_miMatch_var_data, os_miMatchVar]
  have htotal := eval_trans_mi 2 tailFuel
    (miMatch (MIVar v) encodedTerm rawBinds)
    (miMatchVarK (con0 v) encodedTerm rawBinds
      (miLookup (con0 v) rawBinds))
    MIMatchFail hdispatch htail
  refine ⟨2 + tailFuel, htotal, ?_, htailNorm⟩
  apply match_active_append_mi 2 tailFuel hdispatch
  · intro k hk
    have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with rfl | rfl
    · simp only [eval]
      exact MatchActiveShape.match (MIVar v) encodedTerm rawBinds
    · simp only [eval, MIVar, os_miMatch_var_data]
      exact MatchActiveShape.matchVar (con0 v) encodedTerm rawBinds
  · exact htailActive

theorem miMatchVarK_rawPayload_source_some_or_fail_first_result
    (v : String) {bs : List (String × AST)}
    {rawTerm encodedTerm rawBinds encodedBinds term : AST}
    {bsOut : List (String × AST)}
    (hterm : encAST? term = some encodedTerm)
    (hrawTerm : RawTermPayload rawTerm encodedTerm)
    (hpayload : RawBindsFor bs rawBinds encodedBinds)
    (hmatch : AST.matchPat (.var (.base v)) term bs = some bsOut) :
    RawMatchSomeOrFailResult
      (miMatchVarK (con0 v) rawTerm rawBinds
        (miLookup (con0 v) rawBinds))
      bsOut := by
  have hencodedTerm : IsNormal pMI encodedTerm :=
    encAST?_some_normal term encodedTerm hterm
  obtain ⟨termFuel, htermEval⟩ :=
    rawTermPayload_eval_of_normal hrawTerm hencodedTerm
  let Fterm : AST → AST :=
    fun z => miMatchVarK (con0 v) z rawBinds
      (miLookup (con0 v) rawBinds)
  obtain ⟨termCtxFuel, htermCtx, htermCtxActive⟩ :=
    cong_eval_to_match_active_with_guard_mi Fterm
      (fun z => MatchActiveShape.matchVarK (con0 v) z rawBinds
        (miLookup (con0 v) rawBinds))
      (fun s s' hstep =>
        os_miMatchVarK_term_lookup_arg_step v s s' rawBinds rawBinds
          hstep)
      termFuel htermEval hencodedTerm
  have hbs : encBinds? bs = some encodedBinds :=
    rawBindsFor_encoding hpayload
  have hencodedBinds : IsNormal pMI encodedBinds :=
    encBinds?_some_normal bs encodedBinds hbs
  obtain ⟨bindFuel, hbindsEval⟩ :=
    rawBindsPayload_eval_of_normal
      (rawBindsFor_payload hpayload) hencodedBinds
  let Fbind : AST → AST :=
    fun z => miMatchVarK (con0 v) encodedTerm z
      (miLookup (con0 v) rawBinds)
  obtain ⟨bindCtxFuel, hbindCtx, hbindCtxActive⟩ :=
    cong_eval_to_match_active_with_guard_mi Fbind
      (fun z => MatchActiveShape.matchVarK (con0 v) encodedTerm z
        (miLookup (con0 v) rawBinds))
      (fun s s' hstep =>
        os_miMatchVarK_bs_lookup_arg_step v encodedTerm s s'
          rawBinds hencodedTerm hstep)
      bindFuel hbindsEval hencodedBinds
  have hprefix := eval_trans_mi termCtxFuel bindCtxFuel
    (miMatchVarK (con0 v) rawTerm rawBinds
      (miLookup (con0 v) rawBinds))
    (miMatchVarK (con0 v) encodedTerm rawBinds
      (miLookup (con0 v) rawBinds))
    (miMatchVarK (con0 v) encodedTerm encodedBinds
      (miLookup (con0 v) rawBinds))
    (by simpa only [Fterm] using htermCtx)
    (by simpa only [Fbind] using hbindCtx)
  have hprefixActive :
      ∀ k, k < termCtxFuel + bindCtxFuel →
        MatchActiveShape
          (eval pMI k
            (miMatchVarK (con0 v) rawTerm rawBinds
              (miLookup (con0 v) rawBinds))) := by
    apply match_active_append_mi termCtxFuel bindCtxFuel
      (by simpa only [Fterm] using htermCtx)
    · simpa only [Fterm] using htermCtxActive
    · simpa only [Fbind] using hbindCtxActive
  have htail :=
    miMatchVarK_rawBindsFor_var_some_or_fail_first_result v hterm
      hpayload hmatch
  cases htail with
  | inl hfail =>
      unfold RawMatchFailResult at hfail
      obtain ⟨tailFuel, htail, htailActive, htailNorm⟩ := hfail
      have htotal := eval_trans_mi (termCtxFuel + bindCtxFuel) tailFuel
        (miMatchVarK (con0 v) rawTerm rawBinds
          (miLookup (con0 v) rawBinds))
        (miMatchVarK (con0 v) encodedTerm encodedBinds
          (miLookup (con0 v) rawBinds))
        MIMatchFail hprefix htail
      left
      refine ⟨termCtxFuel + bindCtxFuel + tailFuel, htotal, ?_,
        htailNorm⟩
      apply match_active_append_mi (termCtxFuel + bindCtxFuel) tailFuel
        hprefix hprefixActive htailActive
  | inr hsome =>
      obtain ⟨rawOut, encodedOut, tailFuel, hout, houtPayload,
        htail, htailActive⟩ := hsome
      have htotal := eval_trans_mi (termCtxFuel + bindCtxFuel) tailFuel
        (miMatchVarK (con0 v) rawTerm rawBinds
          (miLookup (con0 v) rawBinds))
        (miMatchVarK (con0 v) encodedTerm encodedBinds
          (miLookup (con0 v) rawBinds))
        (MIMatchOk rawOut) hprefix htail
      right
      refine ⟨rawOut, encodedOut, termCtxFuel + bindCtxFuel + tailFuel,
        hout, houtPayload, htotal, ?_⟩
      apply match_active_append_mi (termCtxFuel + bindCtxFuel) tailFuel
        hprefix hprefixActive htailActive

theorem miMatch_var_rawPayload_source_some_or_fail_first_result
    (v : String) {bs : List (String × AST)}
    {rawTerm encodedTerm rawBinds encodedBinds term : AST}
    {bsOut : List (String × AST)}
    (hterm : encAST? term = some encodedTerm)
    (hrawTerm : RawTermPayload rawTerm encodedTerm)
    (hpayload : RawBindsFor bs rawBinds encodedBinds)
    (hmatch : AST.matchPat (.var (.base v)) term bs = some bsOut) :
    RawMatchSomeOrFailResult
      (miMatch (MIVar v) rawTerm rawBinds) bsOut := by
  have hdispatch :
      eval pMI 2 (miMatch (MIVar v) rawTerm rawBinds) =
        miMatchVarK (con0 v) rawTerm rawBinds
          (miLookup (con0 v) rawBinds) := by
    simp only [eval, MIVar, os_miMatch_var_data, os_miMatchVar]
  have htail :=
    miMatchVarK_rawPayload_source_some_or_fail_first_result v
      hterm hrawTerm hpayload hmatch
  cases htail with
  | inl hfail =>
      unfold RawMatchFailResult at hfail
      obtain ⟨tailFuel, htail, htailActive, htailNorm⟩ := hfail
      have htotal := eval_trans_mi 2 tailFuel
        (miMatch (MIVar v) rawTerm rawBinds)
        (miMatchVarK (con0 v) rawTerm rawBinds
          (miLookup (con0 v) rawBinds))
        MIMatchFail hdispatch htail
      left
      refine ⟨2 + tailFuel, htotal, ?_, htailNorm⟩
      apply match_active_append_mi 2 tailFuel hdispatch
      · intro k hk
        have hkcases : k = 0 ∨ k = 1 := by omega
        rcases hkcases with rfl | rfl
        · simp only [eval]
          exact MatchActiveShape.match (MIVar v) rawTerm rawBinds
        · simp only [eval, MIVar, os_miMatch_var_data]
          exact MatchActiveShape.matchVar (con0 v) rawTerm rawBinds
      · exact htailActive
  | inr hsome =>
      obtain ⟨rawOut, encodedOut, tailFuel, hout, houtPayload,
        htail, htailActive⟩ := hsome
      have htotal := eval_trans_mi 2 tailFuel
        (miMatch (MIVar v) rawTerm rawBinds)
        (miMatchVarK (con0 v) rawTerm rawBinds
          (miLookup (con0 v) rawBinds))
        (MIMatchOk rawOut) hdispatch htail
      right
      refine ⟨rawOut, encodedOut, 2 + tailFuel, hout, houtPayload,
        htotal, ?_⟩
      apply match_active_append_mi 2 tailFuel hdispatch
      · intro k hk
        have hkcases : k = 0 ∨ k = 1 := by omega
        rcases hkcases with rfl | rfl
        · simp only [eval]
          exact MatchActiveShape.match (MIVar v) rawTerm rawBinds
        · simp only [eval, MIVar, os_miMatch_var_data]
          exact MatchActiveShape.matchVar (con0 v) rawTerm rawBinds
      · exact htailActive

theorem miMatchVarK_rawPayload_source_none_first_result
    (v : String) {bs : List (String × AST)}
    {rawTerm encodedTerm rawBinds encodedBinds term : AST}
    (hterm : encAST? term = some encodedTerm)
    (hrawTerm : RawTermPayload rawTerm encodedTerm)
    (hpayload : RawBindsFor bs rawBinds encodedBinds)
    (hmatch : AST.matchPat (.var (.base v)) term bs = none) :
    ∃ fuel,
      eval pMI fuel
        (miMatchVarK (con0 v) rawTerm rawBinds
          (miLookup (con0 v) rawBinds)) =
        MIMatchFail ∧
      (∀ k, k < fuel →
        MatchActiveShape
          (eval pMI k
            (miMatchVarK (con0 v) rawTerm rawBinds
              (miLookup (con0 v) rawBinds)))) ∧
      IsNormal pMI MIMatchFail := by
  have hencodedTerm : IsNormal pMI encodedTerm :=
    encAST?_some_normal term encodedTerm hterm
  obtain ⟨termFuel, htermEval⟩ :=
    rawTermPayload_eval_of_normal hrawTerm hencodedTerm
  let F : AST → AST :=
    fun z => miMatchVarK (con0 v) z rawBinds
      (miLookup (con0 v) rawBinds)
  obtain ⟨ctxFuel, hctx, hctxActive⟩ :=
    cong_eval_to_match_active_with_guard_mi F
      (fun z => MatchActiveShape.matchVarK (con0 v) z rawBinds
        (miLookup (con0 v) rawBinds))
      (fun s s' hstep =>
        os_miMatchVarK_term_lookup_arg_step v s s' rawBinds rawBinds
          hstep)
      termFuel htermEval hencodedTerm
  obtain ⟨tailFuel, htail, htailActive, htailNorm⟩ :=
    miMatchVarK_rawBindsFor_var_none_first_result_raw_whole v
      hterm hpayload hmatch
  have htotal := eval_trans_mi ctxFuel tailFuel
    (miMatchVarK (con0 v) rawTerm rawBinds
      (miLookup (con0 v) rawBinds))
    (miMatchVarK (con0 v) encodedTerm rawBinds
      (miLookup (con0 v) rawBinds))
    MIMatchFail
    (by simpa only [F] using hctx) htail
  refine ⟨ctxFuel + tailFuel, htotal, ?_, htailNorm⟩
  apply match_active_append_mi ctxFuel tailFuel
    (by simpa only [F] using hctx)
  · simpa only [F] using hctxActive
  · exact htailActive

theorem miMatch_var_rawPayload_source_none_first_result
    (v : String) {bs : List (String × AST)}
    {rawTerm encodedTerm rawBinds encodedBinds term : AST}
    (hterm : encAST? term = some encodedTerm)
    (hrawTerm : RawTermPayload rawTerm encodedTerm)
    (hpayload : RawBindsFor bs rawBinds encodedBinds)
    (hmatch : AST.matchPat (.var (.base v)) term bs = none) :
    ∃ fuel,
      eval pMI fuel (miMatch (MIVar v) rawTerm rawBinds) =
        MIMatchFail ∧
      (∀ k, k < fuel →
        MatchActiveShape
          (eval pMI k (miMatch (MIVar v) rawTerm rawBinds))) ∧
      IsNormal pMI MIMatchFail := by
  obtain ⟨tailFuel, htail, htailActive, htailNorm⟩ :=
    miMatchVarK_rawPayload_source_none_first_result v hterm hrawTerm
      hpayload hmatch
  have hdispatch :
      eval pMI 2 (miMatch (MIVar v) rawTerm rawBinds) =
        miMatchVarK (con0 v) rawTerm rawBinds
          (miLookup (con0 v) rawBinds) := by
    simp only [eval, MIVar, os_miMatch_var_data, os_miMatchVar]
  have htotal := eval_trans_mi 2 tailFuel
    (miMatch (MIVar v) rawTerm rawBinds)
    (miMatchVarK (con0 v) rawTerm rawBinds
      (miLookup (con0 v) rawBinds))
    MIMatchFail hdispatch htail
  refine ⟨2 + tailFuel, htotal, ?_, htailNorm⟩
  apply match_active_append_mi 2 tailFuel hdispatch
  · intro k hk
    have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with rfl | rfl
    · simp only [eval]
      exact MatchActiveShape.match (MIVar v) rawTerm rawBinds
    · simp only [eval, MIVar, os_miMatch_var_data]
      exact MatchActiveShape.matchVar (con0 v) rawTerm rawBinds
  · exact htailActive

theorem miMatchList_nil_raw_source_none_first_result
    {terms : List AST} {encodedTerms rawArgs rawBinds : AST}
    {bs : List (String × AST)}
    (hterms : encASTList? terms = some encodedTerms)
    (hargs : RawArgsPayload rawArgs encodedTerms)
    (hmatch : AST.matchPatList [] terms bs = none) :
    RawMatchFailResult (miMatchList MINil rawArgs rawBinds) := by
  cases terms with
  | nil =>
      simp only [AST.matchPatList] at hmatch
      cases hmatch
  | cons t ts =>
      simp only [encASTList?] at hterms
      cases ht : encAST? t with
      | none =>
          simp [ht] at hterms
      | some encodedT =>
          cases hts : encASTList? ts with
          | none =>
              simp [ht, hts] at hterms
          | some encodedTs =>
              simp [ht, hts] at hterms
              cases hterms
              cases hargs with
              | encoded _ =>
                  exact ⟨1,
                    miMatchList_nil_cons_fail_sim encodedT encodedTs rawBinds,
                    miMatchList_active_guard_one MINil
                      (MICons encodedT encodedTs) rawBinds,
                    normal_MIMatchFail⟩
              | consHead hhead =>
                  exact ⟨1,
                    miMatchList_nil_cons_fail_sim _ _ rawBinds,
                    miMatchList_active_guard_one MINil _ rawBinds,
                    normal_MIMatchFail⟩
              | consTail htail =>
                  exact ⟨1,
                    miMatchList_nil_cons_fail_sim _ _ rawBinds,
                    miMatchList_active_guard_one MINil _ rawBinds,
                    normal_MIMatchFail⟩

theorem miMatchList_cons_nil_raw_source_none_first_result
    {pats : List AST} {encodedPats rawArgs rawBinds : AST}
    {bs : List (String × AST)}
    (hpats : encASTList? pats = some encodedPats)
    (hargs : RawArgsPayload rawArgs MINil)
    (hmatch : AST.matchPatList pats [] bs = none) :
    RawMatchFailResult (miMatchList encodedPats rawArgs rawBinds) := by
  have hrawArgs : rawArgs = MINil := rawArgsPayload_nil_eq hargs
  subst rawArgs
  cases pats with
  | nil =>
      simp only [AST.matchPatList] at hmatch
      cases hmatch
  | cons p ps =>
      simp only [encASTList?] at hpats
      cases hp : encAST? p with
      | none =>
          simp [hp] at hpats
      | some encodedP =>
          cases hps : encASTList? ps with
          | none =>
              simp [hp, hps] at hpats
          | some encodedPs =>
              simp [hp, hps] at hpats
              cases hpats
              exact ⟨1,
                miMatchList_cons_nil_fail_sim encodedP encodedPs rawBinds,
                miMatchList_active_guard_one
                  (MICons encodedP encodedPs) MINil rawBinds,
                normal_MIMatchFail⟩

theorem miMatch_sym_rawPayload_source_none_first_result
    (s : String) {term encodedTerm rawTerm rawBinds : AST}
    {bs : List (String × AST)}
    (hterm : encAST? term = some encodedTerm)
    (hrawTerm : RawTermPayload rawTerm encodedTerm)
    (hmatch : AST.matchPat (.sexp (.id s) []) term bs = none) :
    RawMatchFailResult (miMatch (MISym s) rawTerm rawBinds) := by
  cases hrawTerm with
  | encoded _ =>
      cases term with
      | var p =>
          cases p with
          | base v =>
              simp only [encAST?] at hterm
              cases hterm
              exact ⟨1, miMatch_sym_var_fail_sim s v rawBinds,
                miMatch_active_guard_one (MISym s) (MIVar v) rawBinds,
                normal_MIMatchFail⟩
          | qualified _ _ =>
              simp only [encAST?] at hterm
              cases hterm
      | subst _ _ _ =>
          simp only [encAST?] at hterm
          cases hterm
      | sexp l args =>
          cases l with
          | id t =>
              cases args with
              | nil =>
                  simp only [encAST?] at hterm
                  cases hterm
                  simp only [AST.matchPat, AST.matchPatList, label_id_beq] at hmatch
                  by_cases hst : (s == t) = true
                  · have hEq : s = t := beq_iff_eq.mp hst
                    subst t
                    have hss : (s == s) = true := beq_iff_eq.mpr rfl
                    simp only [hss, if_true] at hmatch
                    cases hmatch
                  · have hstFalse : (s == t) = false := by
                      cases hcmp : (s == t) <;> simp [hcmp] at hst ⊢
                    exact ⟨1, miMatch_sym_diff_named_sim s t rawBinds hstFalse,
                      miMatch_active_guard_one (MISym s) (MISym t) rawBinds,
                      normal_MIMatchFail⟩
              | cons a rest =>
                  simp only [encAST?] at hterm
                  cases hargs : encASTList? (a :: rest) with
                  | none =>
                      simp [hargs] at hterm
                  | some encodedArgs =>
                      simp [hargs] at hterm
                      cases hterm
                      exact miMatch_sym_raw_app_fail_first_result s t
                        encodedArgs rawBinds
          | wild =>
              simp only [encAST?] at hterm
              cases hterm
          | listE _ =>
              simp only [encAST?] at hterm
              cases hterm
          | listCons _ =>
              simp only [encAST?] at hterm
              cases hterm
          | listOne _ =>
              simp only [encAST?] at hterm
              cases hterm
  | substInst _htemplate _hbs _hinst _hsubst _hout =>
      exact ⟨1, by rfl,
        miMatch_active_guard_one (MISym s) _ rawBinds,
        normal_MIMatchFail⟩
  | app h _hargs =>
      exact miMatch_sym_raw_app_fail_first_result s h _ rawBinds

theorem miMatch_sym_rawPayload_source_some_or_fail_first_result
    (s : String) {term encodedTerm rawTerm rawBinds encodedBinds : AST}
    {bs bsOut : List (String × AST)}
    (hterm : encAST? term = some encodedTerm)
    (hrawTerm : RawTermPayload rawTerm encodedTerm)
    (hpayload : RawBindsFor bs rawBinds encodedBinds)
    (hmatch : AST.matchPat (.sexp (.id s) []) term bs = some bsOut) :
    RawMatchSomeOrFailResult
      (miMatch (MISym s) rawTerm rawBinds) bsOut := by
  cases hrawTerm with
  | encoded _ =>
      cases term with
      | var p =>
          cases p with
          | base _ =>
              simp only [encAST?] at hterm
              cases hterm
              simp only [AST.matchPat] at hmatch
              cases hmatch
          | qualified _ _ =>
              simp only [encAST?] at hterm
              cases hterm
      | subst _ _ _ =>
          simp only [encAST?] at hterm
          cases hterm
      | sexp l args =>
          cases l with
          | id t =>
              cases args with
              | nil =>
                  simp only [encAST?] at hterm
                  cases hterm
                  simp only [AST.matchPat, AST.matchPatList, label_id_beq] at hmatch
                  by_cases hst : (s == t) = true
                  · have hEq : s = t := beq_iff_eq.mp hst
                    subst t
                    have hss : (s == s) = true := beq_iff_eq.mpr rfl
                    simp only [hss, if_true] at hmatch
                    cases hmatch
                    right
                    refine ⟨rawBinds, encodedBinds, 1,
                      rawBindsFor_encoding hpayload, hpayload, ?_, ?_⟩
                    · exact miMatch_sym_same_named_sim s rawBinds
                    · exact match_active_fuel_one_mi
                        (MatchActiveShape.match (MISym s) (MISym s) rawBinds)
                  · have hstFalse : (s == t) = false := by
                      cases hcmp : (s == t) <;> simp [hcmp] at hst ⊢
                    simp only [hstFalse, Bool.false_eq_true, if_false] at hmatch
                    cases hmatch
              | cons a rest =>
                  simp only [encAST?] at hterm
                  cases hargs : encASTList? (a :: rest) with
                  | none =>
                      simp [hargs] at hterm
                  | some _ =>
                      simp [hargs] at hterm
                      simp only [AST.matchPat, label_id_beq] at hmatch
                      by_cases hst : (s == t) = true
                      · simp only [hst, if_true] at hmatch
                        simp only [AST.matchPatList] at hmatch
                        cases hmatch
                      · have hstFalse : (s == t) = false := by
                          cases hcmp : (s == t) <;> simp [hcmp] at hst ⊢
                        simp only [hstFalse, Bool.false_eq_true, if_false] at hmatch
                        cases hmatch
          | wild =>
              simp only [encAST?] at hterm
              cases hterm
          | listE _ =>
              simp only [encAST?] at hterm
              cases hterm
          | listCons _ =>
              simp only [encAST?] at hterm
              cases hterm
          | listOne _ =>
              simp only [encAST?] at hterm
              cases hterm
  | substInst _htemplate _hbs _hinst _hsubst _hout =>
      left
      exact ⟨1, by rfl,
        miMatch_active_guard_one (MISym s) _ rawBinds,
        normal_MIMatchFail⟩
  | app h _hargs =>
      left
      exact miMatch_sym_raw_app_fail_first_result s h _ rawBinds

theorem miMatchList_nil_raw_source_some_or_fail_first_result
    {terms : List AST} {encodedTerms rawArgs rawBinds encodedBinds : AST}
    {bs bsOut : List (String × AST)}
    (hterms : encASTList? terms = some encodedTerms)
    (hargs : RawArgsPayload rawArgs encodedTerms)
    (hpayload : RawBindsFor bs rawBinds encodedBinds)
    (hmatch : AST.matchPatList [] terms bs = some bsOut) :
    RawMatchSomeOrFailResult
      (miMatchList MINil rawArgs rawBinds) bsOut := by
  cases terms with
  | nil =>
      simp only [encASTList?] at hterms
      cases hterms
      have hrawArgs : rawArgs = MINil := rawArgsPayload_nil_eq hargs
      subst rawArgs
      simp only [AST.matchPatList] at hmatch
      cases hmatch
      right
      refine ⟨rawBinds, encodedBinds, 1,
        rawBindsFor_encoding hpayload, hpayload, ?_, ?_⟩
      · exact miMatchList_nil_nil_sim rawBinds
      · exact miMatchList_active_guard_one MINil MINil rawBinds
  | cons _ _ =>
      simp only [AST.matchPatList] at hmatch
      cases hmatch

theorem miMatch_app_raw_same_head_some_or_fail_of_list (h : String)
    (pats rawArgs rawBinds : AST) {bsOut : List (String × AST)}
    (hlist :
      RawMatchSomeOrFailResult
        (miMatchList pats rawArgs rawBinds) bsOut) :
    RawMatchSomeOrFailResult
      (miMatch (MIApp h pats) (MIApp h rawArgs) rawBinds) bsOut := by
  cases hlist with
  | inl hfail =>
      unfold RawMatchFailResult at hfail
      obtain ⟨listFuel, hlistEval, hlistActive, _hlistNorm⟩ := hfail
      left
      exact miMatch_app_raw_same_head_fail_of_list h pats rawArgs rawBinds
        listFuel hlistEval hlistActive
  | inr hsome =>
      obtain ⟨rawOut, encodedOut, listFuel, hout, houtPayload,
        hlistEval, hlistActive⟩ := hsome
      obtain ⟨appFuel, happEval, happActive⟩ :=
        miMatch_app_same_active_result_of_list h pats rawArgs rawBinds
          (MIMatchOk rawOut) listFuel hlistEval hlistActive
      right
      exact ⟨rawOut, encodedOut, appFuel, hout, houtPayload,
        happEval, happActive⟩

theorem miMatchList_cons_raw_normal_tail_some_or_fail
    (p ps rawT encodedTs rawBinds : AST)
    {bsMid bsOut : List (String × AST)}
    (hps : IsNormal pMI ps) (hts : IsNormal pMI encodedTs)
    (hhead :
      RawMatchSomeOrFailResult (miMatch p rawT rawBinds) bsMid)
    (htail :
      ∀ {rawMid encodedMid : AST},
        encBinds? bsMid = some encodedMid →
        RawBindsFor bsMid rawMid encodedMid →
        RawMatchSomeOrFailResult
          (miMatchList ps encodedTs rawMid) bsOut) :
    RawMatchSomeOrFailResult
      (miMatchList (MICons p ps) (MICons rawT encodedTs) rawBinds)
      bsOut := by
  cases hhead with
  | inl hfail =>
      unfold RawMatchFailResult at hfail
      obtain ⟨headFuel, hheadEval, hheadActive, _hheadNorm⟩ := hfail
      left
      exact miMatchList_cons_first_result_of_match_fail p ps rawT
        encodedTs rawBinds headFuel hps hts hheadEval hheadActive
  | inr hsome =>
      obtain ⟨rawMid, encodedMid, headFuel, hmid, hmidPayload,
        hheadEval, hheadActive⟩ := hsome
      have htailResult := htail hmid hmidPayload
      cases htailResult with
      | inl htailFail =>
          unfold RawMatchFailResult at htailFail
          obtain ⟨tailFuel, htailEval, htailActive, _htailNorm⟩ :=
            htailFail
          obtain ⟨fuel, htotal, hactive⟩ :=
            miMatchList_cons_active_result_of_match_ok p ps rawT
              encodedTs rawBinds rawMid MIMatchFail headFuel tailFuel
              hps hts hheadEval hheadActive htailEval htailActive
          left
          exact ⟨fuel, htotal, hactive, normal_MIMatchFail⟩
      | inr htailSome =>
          obtain ⟨rawOut, encodedOut, tailFuel, hout, houtPayload,
            htailEval, htailActive⟩ := htailSome
          obtain ⟨fuel, htotal, hactive⟩ :=
            miMatchList_cons_active_result_of_match_ok p ps rawT
              encodedTs rawBinds rawMid (MIMatchOk rawOut)
              headFuel tailFuel hps hts hheadEval hheadActive
              htailEval htailActive
          right
          exact ⟨rawOut, encodedOut, fuel, hout, houtPayload,
            htotal, hactive⟩

theorem miMatchList_cons_raw_tail_some_or_fail
    (p ps rawT rawTs encodedTs rawBinds : AST)
    {bsMid bsOut : List (String × AST)}
    (rawTailFuel : Nat)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI encodedTs)
    (hrawTail : eval pMI rawTailFuel rawTs = encodedTs)
    (hhead :
      RawMatchSomeOrFailResult (miMatch p rawT rawBinds) bsMid)
    (htail :
      ∀ {rawMid encodedMid : AST},
        encBinds? bsMid = some encodedMid →
        RawBindsFor bsMid rawMid encodedMid →
        RawMatchSomeOrFailResult
          (miMatchList ps encodedTs rawMid) bsOut) :
    RawMatchSomeOrFailResult
      (miMatchList (MICons p ps) (MICons rawT rawTs) rawBinds)
      bsOut := by
  cases hhead with
  | inl hfail =>
      unfold RawMatchFailResult at hfail
      obtain ⟨headFuel, hheadEval, hheadActive, _hheadNorm⟩ := hfail
      left
      exact miMatchList_cons_tail_first_result_of_match_fail p ps rawT
        rawTs encodedTs rawBinds rawTailFuel headFuel hps hts
        hrawTail hheadEval hheadActive
  | inr hsome =>
      obtain ⟨rawMid, encodedMid, headFuel, hmid, hmidPayload,
        hheadEval, hheadActive⟩ := hsome
      have htailResult := htail hmid hmidPayload
      cases htailResult with
      | inl htailFail =>
          unfold RawMatchFailResult at htailFail
          obtain ⟨tailFuel, htailEval, htailActive, _htailNorm⟩ :=
            htailFail
          obtain ⟨fuel, htotal, hactive⟩ :=
            miMatchList_cons_tail_active_result_of_match_ok p ps rawT
              rawTs encodedTs rawBinds rawMid MIMatchFail rawTailFuel
              headFuel tailFuel hps hts hrawTail hheadEval
              hheadActive htailEval htailActive
          left
          exact ⟨fuel, htotal, hactive, normal_MIMatchFail⟩
      | inr htailSome =>
          obtain ⟨rawOut, encodedOut, tailFuel, hout, houtPayload,
            htailEval, htailActive⟩ := htailSome
          obtain ⟨fuel, htotal, hactive⟩ :=
            miMatchList_cons_tail_active_result_of_match_ok p ps rawT
              rawTs encodedTs rawBinds rawMid (MIMatchOk rawOut)
              rawTailFuel headFuel tailFuel hps hts hrawTail hheadEval
              hheadActive htailEval htailActive
          right
          exact ⟨rawOut, encodedOut, fuel, hout, houtPayload,
            htotal, hactive⟩

theorem miMatchList_cons_raw_normal_tail_none
    (p ps rawT encodedTs rawBinds : AST)
    {bsMid : List (String × AST)}
    (hps : IsNormal pMI ps) (hts : IsNormal pMI encodedTs)
    (hhead :
      RawMatchSomeOrFailResult (miMatch p rawT rawBinds) bsMid)
    (htail :
      ∀ {rawMid encodedMid : AST},
        encBinds? bsMid = some encodedMid →
        RawBindsFor bsMid rawMid encodedMid →
        RawMatchFailResult (miMatchList ps encodedTs rawMid)) :
    RawMatchFailResult
      (miMatchList (MICons p ps) (MICons rawT encodedTs) rawBinds) := by
  cases hhead with
  | inl hfail =>
      unfold RawMatchFailResult at hfail
      obtain ⟨headFuel, hheadEval, hheadActive, _hheadNorm⟩ := hfail
      exact miMatchList_cons_first_result_of_match_fail p ps rawT
        encodedTs rawBinds headFuel hps hts hheadEval hheadActive
  | inr hsome =>
      obtain ⟨rawMid, encodedMid, headFuel, hmid, hmidPayload,
        hheadEval, hheadActive⟩ := hsome
      have htailFail := htail hmid hmidPayload
      unfold RawMatchFailResult at htailFail
      obtain ⟨tailFuel, htailEval, htailActive, _htailNorm⟩ :=
        htailFail
      obtain ⟨fuel, htotal, hactive⟩ :=
        miMatchList_cons_active_result_of_match_ok p ps rawT
          encodedTs rawBinds rawMid MIMatchFail headFuel tailFuel
          hps hts hheadEval hheadActive htailEval htailActive
      exact ⟨fuel, htotal, hactive, normal_MIMatchFail⟩

theorem miMatchList_cons_raw_tail_none
    (p ps rawT rawTs encodedTs rawBinds : AST)
    {bsMid : List (String × AST)}
    (rawTailFuel : Nat)
    (hps : IsNormal pMI ps) (hts : IsNormal pMI encodedTs)
    (hrawTail : eval pMI rawTailFuel rawTs = encodedTs)
    (hhead :
      RawMatchSomeOrFailResult (miMatch p rawT rawBinds) bsMid)
    (htail :
      ∀ {rawMid encodedMid : AST},
        encBinds? bsMid = some encodedMid →
        RawBindsFor bsMid rawMid encodedMid →
        RawMatchFailResult (miMatchList ps encodedTs rawMid)) :
    RawMatchFailResult
      (miMatchList (MICons p ps) (MICons rawT rawTs) rawBinds) := by
  cases hhead with
  | inl hfail =>
      unfold RawMatchFailResult at hfail
      obtain ⟨headFuel, hheadEval, hheadActive, _hheadNorm⟩ := hfail
      exact miMatchList_cons_tail_first_result_of_match_fail p ps rawT
        rawTs encodedTs rawBinds rawTailFuel headFuel hps hts
        hrawTail hheadEval hheadActive
  | inr hsome =>
      obtain ⟨rawMid, encodedMid, headFuel, hmid, hmidPayload,
        hheadEval, hheadActive⟩ := hsome
      have htailFail := htail hmid hmidPayload
      unfold RawMatchFailResult at htailFail
      obtain ⟨tailFuel, htailEval, htailActive, _htailNorm⟩ :=
        htailFail
      obtain ⟨fuel, htotal, hactive⟩ :=
        miMatchList_cons_tail_active_result_of_match_ok p ps rawT
          rawTs encodedTs rawBinds rawMid MIMatchFail rawTailFuel
          headFuel tailFuel hps hts hrawTail hheadEval hheadActive
          htailEval htailActive
      exact ⟨fuel, htotal, hactive, normal_MIMatchFail⟩

theorem miMatch_app_rawPayload_mivar_fail_first_result_aux
    (s v : String) (pats rawTerm rawBinds target : AST)
    (htarget : target = MIVar v)
    (hrawTerm : RawTermPayload rawTerm target) :
    RawMatchFailResult (miMatch (MIApp s pats) rawTerm rawBinds) := by
  cases hrawTerm with
  | encoded _ =>
      cases htarget
      exact ⟨1, miMatch_app_var_fail_sim s v pats rawBinds,
        miMatch_active_guard_one (MIApp s pats) (MIVar v) rawBinds,
        normal_MIMatchFail⟩
  | substInst _htemplate _hbs _hinst _hsubst _hout =>
      exact ⟨1, by rfl,
        miMatch_active_guard_one (MIApp s pats) _ rawBinds,
        normal_MIMatchFail⟩
  | app h hargs =>
      exfalso
      exact mivar_ne_miapp v h _ htarget.symm

theorem miMatch_app_rawPayload_mivar_fail_first_result
    (s v : String) (pats rawTerm rawBinds : AST)
    (hrawTerm : RawTermPayload rawTerm (MIVar v)) :
    RawMatchFailResult (miMatch (MIApp s pats) rawTerm rawBinds) :=
  miMatch_app_rawPayload_mivar_fail_first_result_aux s v pats rawTerm
    rawBinds (MIVar v) rfl hrawTerm

theorem miMatch_app_rawPayload_misym_fail_first_result_aux
    (s t : String) (pats rawTerm rawBinds target : AST)
    (htarget : target = MISym t)
    (hrawTerm : RawTermPayload rawTerm target) :
    RawMatchFailResult (miMatch (MIApp s pats) rawTerm rawBinds) := by
  cases hrawTerm with
  | encoded _ =>
      cases htarget
      exact ⟨1, miMatch_app_sym_fail_sim s t pats rawBinds,
        miMatch_active_guard_one (MIApp s pats) (MISym t) rawBinds,
        normal_MIMatchFail⟩
  | substInst _htemplate _hbs _hinst _hsubst _hout =>
      exact ⟨1, by rfl,
        miMatch_active_guard_one (MIApp s pats) _ rawBinds,
        normal_MIMatchFail⟩
  | app h hargs =>
      exfalso
      exact misym_ne_miapp t h _ htarget.symm

theorem miMatch_app_rawPayload_misym_fail_first_result
    (s t : String) (pats rawTerm rawBinds : AST)
    (hrawTerm : RawTermPayload rawTerm (MISym t)) :
    RawMatchFailResult (miMatch (MIApp s pats) rawTerm rawBinds) :=
  miMatch_app_rawPayload_misym_fail_first_result_aux s t pats rawTerm
    rawBinds (MISym t) rfl hrawTerm

mutual
  theorem miMatch_rawPayload_source_some_or_fail_first_result :
      ∀ (pat term encodedPat encodedTerm rawTerm rawBinds
          encodedBinds : AST)
        (bs bsOut : List (String × AST)),
        encAST? pat = some encodedPat →
        encAST? term = some encodedTerm →
        RawTermPayload rawTerm encodedTerm →
        RawBindsFor bs rawBinds encodedBinds →
        AST.matchPat pat term bs = some bsOut →
        RawMatchSomeOrFailResult
          (miMatch encodedPat rawTerm rawBinds) bsOut
    | .var (.base v), term, _, encodedTerm, rawTerm, rawBinds,
        encodedBinds, bs, bsOut, hpat, hterm, hrawTerm, hpayload,
        hmatch => by
        simp only [encAST?] at hpat
        cases hpat
        exact miMatch_var_rawPayload_source_some_or_fail_first_result v
          hterm hrawTerm hpayload hmatch
    | .var (.qualified _ _), _, _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .subst _ _ _, _, _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.id s) [], term, _, encodedTerm, rawTerm, rawBinds,
        encodedBinds, bs, bsOut, hpat, hterm, hrawTerm, hpayload,
        hmatch => by
        simp only [encAST?] at hpat
        cases hpat
        exact miMatch_sym_rawPayload_source_some_or_fail_first_result s
          hterm hrawTerm hpayload hmatch
    | .sexp (.id s) (pHead :: pTail), term, _, encodedTerm, rawTerm,
        rawBinds, encodedBinds, bs, bsOut, hpat, hterm, hrawTerm,
        hpayload, hmatch => by
        simp only [encAST?] at hpat
        cases hpats : encASTList? (pHead :: pTail) with
        | none =>
            simp [hpats] at hpat
        | some encodedPats =>
            simp [hpats] at hpat
            cases hpat
            cases term with
            | var p =>
                cases p with
                | base v =>
                    simp only [encAST?] at hterm
                    cases hterm
                    simp [AST.matchPat] at hmatch
                    have hEq := ast_beq_true_eq_mi
                      (AST.sexp (Label.id s) (pHead :: pTail))
                      (AST.var (.base v)) hmatch.1
                    cases hEq
                | qualified _ _ =>
                    simp only [encAST?] at hterm
                    cases hterm
            | subst _ _ _ =>
                simp only [encAST?] at hterm
                cases hterm
            | sexp l terms =>
                cases l with
                | id t =>
                    cases terms with
                    | nil =>
                        simp only [encAST?] at hterm
                        cases hterm
                        simp only [AST.matchPat, AST.matchPatList,
                          label_id_beq] at hmatch
                        by_cases hst : (s == t) = true
                        · simp only [hst, if_true] at hmatch
                          cases hmatch
                        · have hstFalse : (s == t) = false := by
                            cases hcmp : (s == t) <;>
                              simp [hcmp] at hst ⊢
                          simp only [hstFalse, Bool.false_eq_true,
                            if_false] at hmatch
                          cases hmatch
                    | cons tHead tTail =>
                        change
                          (match encASTList? (tHead :: tTail) with
                          | some encodedArgs => some (MIApp t encodedArgs)
                          | none => none) = some encodedTerm at hterm
                        cases hterms : encASTList? (tHead :: tTail) with
                        | none =>
                            rw [hterms] at hterm
                            cases hterm
                        | some encodedTerms =>
                            rw [hterms] at hterm
                            cases hterm
                            simp only [AST.matchPat, label_id_beq] at hmatch
                            by_cases hst : (s == t) = true
                            · simp only [hst, if_true] at hmatch
                              have hEq : s = t := beq_iff_eq.mp hst
                              subst t
                              cases hrawTerm with
                              | encoded _ =>
                                  have hlist :=
                                    miMatchList_rawPayload_source_some_or_fail_first_result
                                      (pHead :: pTail) (tHead :: tTail)
                                      encodedPats encodedTerms encodedTerms
                                      rawBinds encodedBinds bs bsOut
                                      hpats hterms
                                      (RawArgsPayload.encoded encodedTerms)
                                      hpayload hmatch
                                  exact miMatch_app_raw_same_head_some_or_fail_of_list
                                    s encodedPats encodedTerms rawBinds hlist
                              | substInst _htemplate _hbs _hinst _hsubst _hout =>
                                  left
                                  exact ⟨1, by rfl,
                                    miMatch_active_guard_one
                                      (MIApp s encodedPats) _ rawBinds,
                                    normal_MIMatchFail⟩
                              | app h hargs =>
                                  have hlist :=
                                    miMatchList_rawPayload_source_some_or_fail_first_result
                                      (pHead :: pTail) (tHead :: tTail)
                                      encodedPats encodedTerms _ rawBinds
                                      encodedBinds bs bsOut hpats hterms
                                      hargs hpayload hmatch
                                  exact miMatch_app_raw_same_head_some_or_fail_of_list
                                    s encodedPats _ rawBinds hlist
                            · have hstFalse : (s == t) = false := by
                                cases hcmp : (s == t) <;>
                                  simp [hcmp] at hst ⊢
                              simp only [hstFalse, Bool.false_eq_true,
                                if_false] at hmatch
                              cases hmatch
                | wild =>
                    simp only [encAST?] at hterm
                    cases hterm
                | listE _ =>
                    simp only [encAST?] at hterm
                    cases hterm
                | listCons _ =>
                    simp only [encAST?] at hterm
                    cases hterm
                | listOne _ =>
                    simp only [encAST?] at hterm
                    cases hterm
    | .sexp (.wild) _, _, _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.listE _) _, _, _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.listCons _) _, _, _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.listOne _) _, _, _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat

  theorem miMatchList_rawPayload_source_some_or_fail_first_result :
      ∀ (pats terms : List AST)
        (encodedPats encodedTerms rawArgs rawBinds encodedBinds : AST)
        (bs bsOut : List (String × AST)),
        encASTList? pats = some encodedPats →
        encASTList? terms = some encodedTerms →
        RawArgsPayload rawArgs encodedTerms →
        RawBindsFor bs rawBinds encodedBinds →
        AST.matchPatList pats terms bs = some bsOut →
        RawMatchSomeOrFailResult
          (miMatchList encodedPats rawArgs rawBinds) bsOut
    | [], terms, encodedPats, encodedTerms, rawArgs, rawBinds,
        encodedBinds, bs, bsOut, hpats, hterms, hargs, hpayload,
        hmatch => by
        simp only [encASTList?] at hpats
        cases hpats
        exact miMatchList_nil_raw_source_some_or_fail_first_result
          hterms hargs hpayload hmatch
    | p :: ps, [], encodedPats, _, rawArgs, rawBinds, encodedBinds,
        bs, bsOut, hpats, hterms, hargs, hpayload, hmatch => by
        simp only [AST.matchPatList] at hmatch
        cases hmatch
    | p :: ps, t :: ts, encodedPats, encodedTerms, rawArgs, rawBinds,
        encodedBinds, bs, bsOut, hpats, hterms, hargs, hpayload,
        hmatch => by
        simp only [encASTList?] at hpats hterms
        cases hp : encAST? p with
        | none =>
            simp [hp] at hpats
        | some encodedP =>
            cases hps : encASTList? ps with
            | none =>
                simp [hp, hps] at hpats
            | some encodedPs =>
                simp [hp, hps] at hpats
                cases hpats
                cases ht : encAST? t with
                | none =>
                    simp [ht] at hterms
                | some encodedT =>
                    cases hts : encASTList? ts with
                    | none =>
                        simp [ht, hts] at hterms
                    | some encodedTs =>
                        simp [ht, hts] at hterms
                        cases hterms
                        cases hhead : AST.matchPat p t bs with
                        | none =>
                            simp only [AST.matchPatList, hhead,
                              Option.bind_none] at hmatch
                            cases hmatch
                        | some bsMid =>
                            simp only [AST.matchPatList, hhead,
                              Option.bind_some] at hmatch
                            have hpsNorm : IsNormal pMI encodedPs :=
                              encASTList?_some_normal ps encodedPs hps
                            have htsNorm : IsNormal pMI encodedTs :=
                              encASTList?_some_normal ts encodedTs hts
                            cases hargs with
                            | encoded _ =>
                                have hheadRaw :=
                                  miMatch_rawPayload_source_some_or_fail_first_result
                                    p t encodedP encodedT encodedT rawBinds
                                    encodedBinds bs bsMid hp ht
                                    (RawTermPayload.encoded encodedT)
                                    hpayload hhead
                                exact
                                  miMatchList_cons_raw_normal_tail_some_or_fail
                                    encodedP encodedPs encodedT encodedTs
                                    rawBinds hpsNorm htsNorm hheadRaw
                                    (by
                                      intro rawMid encodedMid hmid hmidPayload
                                      exact
                                        miMatchList_rawPayload_source_some_or_fail_first_result
                                          ps ts encodedPs encodedTs encodedTs
                                          rawMid encodedMid bsMid bsOut
                                          hps hts
                                          (RawArgsPayload.encoded encodedTs)
                                          hmidPayload hmatch)
                            | consHead hheadPayload =>
                                have hheadRaw :=
                                  miMatch_rawPayload_source_some_or_fail_first_result
                                    p t encodedP encodedT _ rawBinds
                                    encodedBinds bs bsMid hp ht
                                    hheadPayload hpayload hhead
                                exact
                                  miMatchList_cons_raw_normal_tail_some_or_fail
                                    encodedP encodedPs _ encodedTs rawBinds
                                    hpsNorm htsNorm hheadRaw
                                    (by
                                      intro rawMid encodedMid hmid hmidPayload
                                      exact
                                        miMatchList_rawPayload_source_some_or_fail_first_result
                                          ps ts encodedPs encodedTs encodedTs
                                          rawMid encodedMid bsMid bsOut
                                          hps hts
                                          (RawArgsPayload.encoded encodedTs)
                                          hmidPayload hmatch)
                            | consTail htailPayload =>
                                obtain ⟨rawTailFuel, hrawTailEval⟩ :=
                                  rawArgsPayload_eval_of_normal htailPayload
                                    htsNorm
                                have hheadRaw :=
                                  miMatch_rawPayload_source_some_or_fail_first_result
                                    p t encodedP encodedT encodedT rawBinds
                                    encodedBinds bs bsMid hp ht
                                    (RawTermPayload.encoded encodedT)
                                    hpayload hhead
                                exact
                                  miMatchList_cons_raw_tail_some_or_fail
                                    encodedP encodedPs encodedT _ encodedTs
                                    rawBinds rawTailFuel hpsNorm htsNorm
                                    hrawTailEval hheadRaw
                                    (by
                                      intro rawMid encodedMid hmid hmidPayload
                                      exact
                                        miMatchList_rawPayload_source_some_or_fail_first_result
                                          ps ts encodedPs encodedTs encodedTs
                                          rawMid encodedMid bsMid bsOut
                                          hps hts
                                          (RawArgsPayload.encoded encodedTs)
                                          hmidPayload hmatch)
end

mutual
  theorem miMatch_rawPayload_source_none_first_result_general :
      ∀ (pat term encodedPat encodedTerm rawTerm rawBinds
          encodedBinds : AST)
        (bs : List (String × AST)),
        encAST? pat = some encodedPat →
        encAST? term = some encodedTerm →
        RawTermPayload rawTerm encodedTerm →
        RawBindsFor bs rawBinds encodedBinds →
        AST.matchPat pat term bs = none →
        RawMatchFailResult (miMatch encodedPat rawTerm rawBinds)
    | .var (.base v), term, _, encodedTerm, rawTerm, rawBinds,
        encodedBinds, bs, hpat, hterm, hrawTerm, hpayload, hmatch => by
        simp only [encAST?] at hpat
        cases hpat
        exact miMatch_var_rawPayload_source_none_first_result v
          hterm hrawTerm hpayload hmatch
    | .var (.qualified _ _), _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .subst _ _ _, _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.id s) [], term, _, encodedTerm, rawTerm, rawBinds,
        encodedBinds, bs, hpat, hterm, hrawTerm, _hpayload, hmatch => by
        simp only [encAST?] at hpat
        cases hpat
        exact miMatch_sym_rawPayload_source_none_first_result s
          hterm hrawTerm hmatch
    | .sexp (.id s) (pHead :: pTail), term, _, encodedTerm, rawTerm,
        rawBinds, encodedBinds, bs, hpat, hterm, hrawTerm, hpayload,
        hmatch => by
        simp only [encAST?] at hpat
        cases hpats : encASTList? (pHead :: pTail) with
        | none =>
            simp [hpats] at hpat
        | some encodedPats =>
            simp [hpats] at hpat
            cases hpat
            cases term with
            | var p =>
                cases p with
                | base v =>
                    simp only [encAST?] at hterm
                    cases hterm
                    exact miMatch_app_rawPayload_mivar_fail_first_result
                      s v encodedPats rawTerm rawBinds hrawTerm
                | qualified _ _ =>
                    simp only [encAST?] at hterm
                    cases hterm
            | subst _ _ _ =>
                simp only [encAST?] at hterm
                cases hterm
            | sexp l terms =>
                cases l with
                | id t =>
                    cases terms with
                    | nil =>
                        simp only [encAST?] at hterm
                        cases hterm
                        exact miMatch_app_rawPayload_misym_fail_first_result
                          s t encodedPats rawTerm rawBinds hrawTerm
                    | cons tHead tTail =>
                        change
                          (match encASTList? (tHead :: tTail) with
                          | some encodedArgs => some (MIApp t encodedArgs)
                          | none => none) = some encodedTerm at hterm
                        cases hterms : encASTList? (tHead :: tTail) with
                        | none =>
                            rw [hterms] at hterm
                            cases hterm
                        | some encodedTerms =>
                            rw [hterms] at hterm
                            cases hterm
                            simp only [AST.matchPat, label_id_beq] at hmatch
                            by_cases hst : (s == t) = true
                            · simp only [hst, if_true] at hmatch
                              have hEq : s = t := beq_iff_eq.mp hst
                              subst t
                              cases hrawTerm with
                              | encoded _ =>
                                  have hlist :=
                                    miMatchList_rawPayload_source_none_first_result_general
                                      (pHead :: pTail) (tHead :: tTail)
                                      encodedPats encodedTerms encodedTerms
                                      rawBinds encodedBinds bs hpats hterms
                                      (RawArgsPayload.encoded encodedTerms)
                                      hpayload hmatch
                                  unfold RawMatchFailResult at hlist
                                  obtain ⟨listFuel, hlistEval, hlistActive,
                                    _hlistNorm⟩ := hlist
                                  exact
                                    miMatch_app_raw_same_head_fail_of_list s
                                      encodedPats encodedTerms rawBinds
                                      listFuel hlistEval hlistActive
                              | substInst _htemplate _hbs _hinst _hsubst _hout =>
                                  exact ⟨1, by rfl,
                                    miMatch_active_guard_one
                                      (MIApp s encodedPats) _ rawBinds,
                                    normal_MIMatchFail⟩
                              | app h hargs =>
                                  have hlist :=
                                    miMatchList_rawPayload_source_none_first_result_general
                                      (pHead :: pTail) (tHead :: tTail)
                                      encodedPats encodedTerms _ rawBinds
                                      encodedBinds bs hpats hterms hargs
                                      hpayload hmatch
                                  unfold RawMatchFailResult at hlist
                                  obtain ⟨listFuel, hlistEval, hlistActive,
                                    _hlistNorm⟩ := hlist
                                  exact
                                    miMatch_app_raw_same_head_fail_of_list s
                                      encodedPats _ rawBinds listFuel
                                      hlistEval hlistActive
                            · have hstFalse : (s == t) = false := by
                                cases hcmp : (s == t) <;>
                                  simp [hcmp] at hst ⊢
                              cases hrawTerm with
                              | encoded _ =>
                                  exact miMatch_app_raw_diff_head_first_result
                                    s t encodedPats encodedTerms rawBinds
                                    hstFalse
                              | substInst _htemplate _hbs _hinst _hsubst _hout =>
                                  exact ⟨1, by rfl,
                                    miMatch_active_guard_one
                                      (MIApp s encodedPats) _ rawBinds,
                                    normal_MIMatchFail⟩
                              | app h hargs =>
                                  exact miMatch_app_raw_diff_head_first_result
                                    s t encodedPats _ rawBinds hstFalse
                | wild =>
                    simp only [encAST?] at hterm
                    cases hterm
                | listE _ =>
                    simp only [encAST?] at hterm
                    cases hterm
                | listCons _ =>
                    simp only [encAST?] at hterm
                    cases hterm
                | listOne _ =>
                    simp only [encAST?] at hterm
                    cases hterm
    | .sexp (.wild) _, _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.listE _) _, _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.listCons _) _, _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat
    | .sexp (.listOne _) _, _, _, _, _, _, _, _, hpat, _, _, _, _ => by
        simp only [encAST?] at hpat
        cases hpat

  theorem miMatchList_rawPayload_source_none_first_result_general :
      ∀ (pats terms : List AST)
        (encodedPats encodedTerms rawArgs rawBinds encodedBinds : AST)
        (bs : List (String × AST)),
        encASTList? pats = some encodedPats →
        encASTList? terms = some encodedTerms →
        RawArgsPayload rawArgs encodedTerms →
        RawBindsFor bs rawBinds encodedBinds →
        AST.matchPatList pats terms bs = none →
        RawMatchFailResult
          (miMatchList encodedPats rawArgs rawBinds)
    | [], terms, encodedPats, encodedTerms, rawArgs, rawBinds,
        encodedBinds, bs, hpats, hterms, hargs, _hpayload, hmatch => by
        simp only [encASTList?] at hpats
        cases hpats
        exact miMatchList_nil_raw_source_none_first_result
          hterms hargs hmatch
    | p :: ps, [], encodedPats, _, rawArgs, rawBinds, encodedBinds,
        bs, hpats, hterms, hargs, _hpayload, hmatch => by
        simp only [encASTList?] at hterms
        cases hterms
        exact miMatchList_cons_nil_raw_source_none_first_result
          hpats hargs hmatch
    | p :: ps, t :: ts, encodedPats, encodedTerms, rawArgs, rawBinds,
        encodedBinds, bs, hpats, hterms, hargs, hpayload, hmatch => by
        simp only [encASTList?] at hpats hterms
        cases hp : encAST? p with
        | none =>
            simp [hp] at hpats
        | some encodedP =>
            cases hps : encASTList? ps with
            | none =>
                simp [hp, hps] at hpats
            | some encodedPs =>
                simp [hp, hps] at hpats
                cases hpats
                cases ht : encAST? t with
                | none =>
                    simp [ht] at hterms
                | some encodedT =>
                    cases hts : encASTList? ts with
                    | none =>
                        simp [ht, hts] at hterms
                    | some encodedTs =>
                        simp [ht, hts] at hterms
                        cases hterms
                        have hpsNorm : IsNormal pMI encodedPs :=
                          encASTList?_some_normal ps encodedPs hps
                        have htsNorm : IsNormal pMI encodedTs :=
                          encASTList?_some_normal ts encodedTs hts
                        cases hhead : AST.matchPat p t bs with
                        | none =>
                            simp only [AST.matchPatList, hhead,
                              Option.bind_none] at hmatch
                            cases hargs with
                            | encoded _ =>
                                have hheadFail :=
                                  miMatch_rawPayload_source_none_first_result_general
                                    p t encodedP encodedT encodedT rawBinds
                                    encodedBinds bs hp ht
                                    (RawTermPayload.encoded encodedT)
                                    hpayload hhead
                                unfold RawMatchFailResult at hheadFail
                                obtain ⟨headFuel, hheadEval, hheadActive,
                                  _hheadNorm⟩ := hheadFail
                                exact miMatchList_cons_first_result_of_match_fail
                                  encodedP encodedPs encodedT encodedTs
                                  rawBinds headFuel hpsNorm htsNorm
                                  hheadEval hheadActive
                            | consHead hheadPayload =>
                                have hheadFail :=
                                  miMatch_rawPayload_source_none_first_result_general
                                    p t encodedP encodedT _ rawBinds
                                    encodedBinds bs hp ht hheadPayload
                                    hpayload hhead
                                unfold RawMatchFailResult at hheadFail
                                obtain ⟨headFuel, hheadEval, hheadActive,
                                  _hheadNorm⟩ := hheadFail
                                exact miMatchList_cons_first_result_of_match_fail
                                  encodedP encodedPs _ encodedTs rawBinds
                                  headFuel hpsNorm htsNorm hheadEval
                                  hheadActive
                            | consTail htailPayload =>
                                obtain ⟨rawTailFuel, hrawTailEval⟩ :=
                                  rawArgsPayload_eval_of_normal htailPayload
                                    htsNorm
                                have hheadFail :=
                                  miMatch_rawPayload_source_none_first_result_general
                                    p t encodedP encodedT encodedT rawBinds
                                    encodedBinds bs hp ht
                                    (RawTermPayload.encoded encodedT)
                                    hpayload hhead
                                unfold RawMatchFailResult at hheadFail
                                obtain ⟨headFuel, hheadEval, hheadActive,
                                  _hheadNorm⟩ := hheadFail
                                exact miMatchList_cons_tail_first_result_of_match_fail
                                  encodedP encodedPs encodedT _ encodedTs
                                  rawBinds rawTailFuel headFuel hpsNorm
                                  htsNorm hrawTailEval hheadEval hheadActive
                        | some bsMid =>
                            simp only [AST.matchPatList, hhead,
                              Option.bind_some] at hmatch
                            cases hargs with
                            | encoded _ =>
                                have hheadRaw :=
                                  miMatch_rawPayload_source_some_or_fail_first_result
                                    p t encodedP encodedT encodedT rawBinds
                                    encodedBinds bs bsMid hp ht
                                    (RawTermPayload.encoded encodedT)
                                    hpayload hhead
                                exact
                                  miMatchList_cons_raw_normal_tail_none
                                    encodedP encodedPs encodedT encodedTs
                                    rawBinds hpsNorm htsNorm hheadRaw
                                    (by
                                      intro rawMid encodedMid hmid hmidPayload
                                      exact
                                        miMatchList_rawPayload_source_none_first_result_general
                                          ps ts encodedPs encodedTs encodedTs
                                          rawMid encodedMid bsMid hps hts
                                          (RawArgsPayload.encoded encodedTs)
                                          hmidPayload hmatch)
                            | consHead hheadPayload =>
                                have hheadRaw :=
                                  miMatch_rawPayload_source_some_or_fail_first_result
                                    p t encodedP encodedT _ rawBinds
                                    encodedBinds bs bsMid hp ht
                                    hheadPayload hpayload hhead
                                exact
                                  miMatchList_cons_raw_normal_tail_none
                                    encodedP encodedPs _ encodedTs rawBinds
                                    hpsNorm htsNorm hheadRaw
                                    (by
                                      intro rawMid encodedMid hmid hmidPayload
                                      exact
                                        miMatchList_rawPayload_source_none_first_result_general
                                          ps ts encodedPs encodedTs encodedTs
                                          rawMid encodedMid bsMid hps hts
                                          (RawArgsPayload.encoded encodedTs)
                                          hmidPayload hmatch)
                            | consTail htailPayload =>
                                obtain ⟨rawTailFuel, hrawTailEval⟩ :=
                                  rawArgsPayload_eval_of_normal htailPayload
                                    htsNorm
                                have hheadRaw :=
                                  miMatch_rawPayload_source_some_or_fail_first_result
                                    p t encodedP encodedT encodedT rawBinds
                                    encodedBinds bs bsMid hp ht
                                    (RawTermPayload.encoded encodedT)
                                    hpayload hhead
                                exact
                                  miMatchList_cons_raw_tail_none
                                    encodedP encodedPs encodedT _ encodedTs
                                    rawBinds rawTailFuel hpsNorm htsNorm
                                    hrawTailEval hheadRaw
                                    (by
                                      intro rawMid encodedMid hmid hmidPayload
                                      exact
                                        miMatchList_rawPayload_source_none_first_result_general
                                          ps ts encodedPs encodedTs encodedTs
                                          rawMid encodedMid bsMid hps hts
                                          (RawArgsPayload.encoded encodedTs)
                                          hmidPayload hmatch)
end

def StepPreservesNoQuery (rws : List RewriteDecl) : Prop :=
  ∀ {term out : AST},
    stepBaseStep? rws term = some out →
    noQueryAST term = true →
    noQueryAST out = true

def StepProducesRootStable (rws : List RewriteDecl) : Prop :=
  ∀ {term out : AST},
    stepBaseStep? rws term = some out →
    rootBaseStep? rws out = none

def SourceTraceRootStable (rws : List RewriteDecl) : Nat → AST → Prop
  | 0, _term => True
  | n + 1, term =>
      match stepBaseStep? rws term with
      | some out =>
          rootBaseStep? rws out = none ∧
            SourceTraceRootStable rws n out
      | none => True

theorem sourceTraceRootStable_of_stepProduces
    (rws : List RewriteDecl)
    (hrootStable : StepProducesRootStable rws) :
    ∀ (n : Nat) (term : AST), SourceTraceRootStable rws n term := by
  intro n
  induction n with
  | zero =>
      intro term
      simp only [SourceTraceRootStable]
  | succ n ih =>
      intro term
      simp only [SourceTraceRootStable]
      cases hstep : stepBaseStep? rws term with
      | none =>
          trivial
      | some out =>
          exact ⟨hrootStable hstep, ih out⟩

theorem StepPreservesNoQuery_of_RulesPreserveNoQuery
    (rws : List RewriteDecl) (hR : RulesPreserveNoQuery rws) :
    StepPreservesNoQuery rws := by
  intro term out hstep hterm
  exact stepBaseStepFuel?_preserves_noQuery rws (astFuel term + 1)
    term out hR hstep hterm

def RawStepSimHyp (rws : List RewriteDecl) (encodedRules : AST) : Prop :=
  encRules? rws = some encodedRules →
  ∀ (term rawTerm encodedTerm : AST),
    RawPayloadFor rws encodedRules term rawTerm encodedTerm →
    encAST? term = some encodedTerm →
    IsNormal pMI encodedTerm →
    noQueryAST term = true →
    match stepBaseStep? rws term with
    | some out => StepRawSomePayload encodedRules rawTerm out
    | none => StepRawNone encodedRules rawTerm

def RawPayloadStepLiftHyp (rws : List RewriteDecl)
    (encodedRules : AST) : Prop :=
  encRules? rws = some encodedRules →
  ∀ (term rawTerm encodedTerm : AST),
    RawPayloadFor rws encodedRules term rawTerm encodedTerm →
    encAST? term = some encodedTerm →
    IsNormal pMI encodedTerm →
    noQueryAST term = true →
    match stepBaseStep? rws term with
    | some out => StepRawSomePayload encodedRules rawTerm out
    | none => StepRawNone encodedRules rawTerm

def RawPayloadAppStepLiftHyp (rws : List RewriteDecl)
    (encodedRules : AST) : Prop :=
  encRules? rws = some encodedRules →
  ∀ (term : AST) (h : String) (rawArgs encodedArgs : AST),
    encAST? term = some (MIApp h encodedArgs) →
    noQueryAST term = true →
    rootBaseStep? rws term = none →
    RawArgsPayload rawArgs encodedArgs →
    IsNormal pMI encodedArgs →
    match stepBaseStep? rws term with
    | some out => StepRawSomePayload encodedRules (MIApp h rawArgs) out
    | none => StepRawNone encodedRules (MIApp h rawArgs)

theorem rawPayloadFor_closed_step_some
    (rws : List RewriteDecl) (term out encodedRules rawTerm
      encodedTerm : AST)
    (_hpayload : RawPayloadFor rws encodedRules term rawTerm
      encodedTerm)
    (_hsource : stepBaseStep? rws term = some out)
    (hrootOut : rootBaseStep? rws out = none)
    (hrawStep : StepRawSomePayload encodedRules rawTerm out) :
    ∃ rawNext encodedOut normFuel,
      encAST? out = some encodedOut ∧
      eval pMI normFuel rawNext = encodedOut ∧
      IsNormal pMI encodedOut ∧
      RawPayloadFor rws encodedRules out rawNext encodedOut := by
  unfold StepRawSomePayload at hrawStep
  obtain ⟨rawNext, encodedOut, _stepFuel, normFuel, hout, _hstep,
    _hactive, hnorm, houtNorm, hshape⟩ := hrawStep
  exact
    ⟨rawNext, encodedOut, normFuel, hout, hnorm, houtNorm,
      RawPayloadFor.grammar hout hshape hrootOut⟩

theorem rawTermPayload_closed_step_some
    (encodedRules rawTerm out : AST)
    (hrawStep : StepRawSomePayload encodedRules rawTerm out) :
    ∃ rawNext encodedOut normFuel,
      encAST? out = some encodedOut ∧
      eval pMI normFuel rawNext = encodedOut ∧
      IsNormal pMI encodedOut ∧
      RawTermPayload rawNext encodedOut := by
  unfold StepRawSomePayload at hrawStep
  obtain ⟨rawNext, encodedOut, _stepFuel, normFuel, hout, _hstep,
    _hactive, hnorm, houtNorm, hshape⟩ := hrawStep
  exact ⟨rawNext, encodedOut, normFuel, hout, hnorm, houtNorm, hshape⟩

theorem step_active_fuel_one_mi {t : AST} (ht : StepActiveShape t) :
    ∀ k, k < 1 → StepActiveShape (eval pMI k t) := by
  intro k hk
  cases k with
  | zero =>
      simpa only [eval] using ht
  | succ k =>
      exact False.elim
        (Nat.not_lt_zero k (Nat.succ_lt_succ_iff.mp hk))

theorem args_active_fuel_one_mi {t : AST} (ht : ArgsActiveShape t) :
    ∀ k, k < 1 → ArgsActiveShape (eval pMI k t) := by
  intro k hk
  cases k with
  | zero =>
      simpa only [eval] using ht
  | succ k =>
      exact False.elim
        (Nat.not_lt_zero k (Nat.succ_lt_succ_iff.mp hk))

theorem miStepArgs_nil_active_sim (rules : AST) :
    eval pMI 1 (miStepArgs rules MINil) = MINoArgsStep ∧
      ∀ k, k < 1 →
        ArgsActiveShape (eval pMI k (miStepArgs rules MINil)) := by
  constructor
  · exact miStepArgs_nil_sim rules
  · exact args_active_fuel_one_mi (ArgsActiveShape.args rules MINil)

theorem miStepArgs_cons_active_sim (rules x xs : AST) :
    eval pMI 1 (miStepArgs rules (MICons x xs)) =
      miStepArgsK rules x xs (miStep rules x) ∧
      ∀ k, k < 1 →
        ArgsActiveShape
          (eval pMI k (miStepArgs rules (MICons x xs))) := by
  constructor
  · simp only [eval, os_miStepArgs_cons]
  · exact args_active_fuel_one_mi
      (ArgsActiveShape.args rules (MICons x xs))

theorem miStepArgsK_step_active_sim (rules x xs next : AST) :
    eval pMI 1 (miStepArgsK rules x xs (MIStep next)) =
      MIArgsStep (MICons next xs) ∧
      ∀ k, k < 1 →
        ArgsActiveShape
          (eval pMI k (miStepArgsK rules x xs (MIStep next))) := by
  constructor
  · exact miStepArgsK_step_sim rules x xs next
  · exact args_active_fuel_one_mi
      (ArgsActiveShape.argsK rules x xs (MIStep next))

theorem miStepArgsK_none_active_sim (rules x xs : AST) :
    eval pMI 1 (miStepArgsK rules x xs MINoStep) =
      miStepArgsRestK x (miStepArgs rules xs) ∧
      ∀ k, k < 1 →
        ArgsActiveShape
          (eval pMI k (miStepArgsK rules x xs MINoStep)) := by
  constructor
  · exact miStepArgsK_none_sim rules x xs
  · exact args_active_fuel_one_mi
      (ArgsActiveShape.argsK rules x xs MINoStep)

theorem miStepArgsRestK_step_active_sim (x xs : AST) :
    eval pMI 1 (miStepArgsRestK x (MIArgsStep xs)) =
      MIArgsStep (MICons x xs) ∧
      ∀ k, k < 1 →
        ArgsActiveShape
          (eval pMI k (miStepArgsRestK x (MIArgsStep xs))) := by
  constructor
  · exact miStepArgsRestK_step_sim x xs
  · exact args_active_fuel_one_mi
      (ArgsActiveShape.argsRestK x (MIArgsStep xs))

theorem miStepArgsRestK_none_active_sim (x : AST) :
    eval pMI 1 (miStepArgsRestK x MINoArgsStep) = MINoArgsStep ∧
      ∀ k, k < 1 →
        ArgsActiveShape
          (eval pMI k (miStepArgsRestK x MINoArgsStep)) := by
  constructor
  · exact miStepArgsRestK_none_sim x
  · exact args_active_fuel_one_mi
      (ArgsActiveShape.argsRestK x MINoArgsStep)

theorem root_active_append_mi (a b : Nat) {start mid : AST}
    (hprefix : eval pMI a start = mid)
    (hfirst : ∀ k, k < a → RootActiveShape (eval pMI k start))
    (hsecond : ∀ k, k < b → RootActiveShape (eval pMI k mid)) :
    ∀ k, k < a + b → RootActiveShape (eval pMI k start) := by
  intro k hk
  by_cases hklt : k < a
  · exact hfirst k hklt
  · have hle : a ≤ k := Nat.le_of_not_gt hklt
    let j := k - a
    have hkj : k = a + j := by omega
    have hj : j < b := by omega
    have heval : eval pMI k start = eval pMI j mid := by
      rw [hkj]
      exact eval_add_eq_eval_mi a j start mid hprefix
    rw [heval]
    exact hsecond j hj

theorem args_active_append_mi (a b : Nat) {start mid : AST}
    (hprefix : eval pMI a start = mid)
    (hfirst : ∀ k, k < a → ArgsActiveShape (eval pMI k start))
    (hsecond : ∀ k, k < b → ArgsActiveShape (eval pMI k mid)) :
    ∀ k, k < a + b → ArgsActiveShape (eval pMI k start) := by
  intro k hk
  by_cases hklt : k < a
  · exact hfirst k hklt
  · have _hle : a ≤ k := Nat.le_of_not_gt hklt
    let j := k - a
    have hkj : k = a + j := by omega
    have hj : j < b := by omega
    have heval : eval pMI k start = eval pMI j mid := by
      rw [hkj]
      exact eval_add_eq_eval_mi a j start mid hprefix
    rw [heval]
    exact hsecond j hj

theorem step_active_append_mi (a b : Nat) {start mid : AST}
    (hprefix : eval pMI a start = mid)
    (hfirst : ∀ k, k < a → StepActiveShape (eval pMI k start))
    (hsecond : ∀ k, k < b → StepActiveShape (eval pMI k mid)) :
    ∀ k, k < a + b → StepActiveShape (eval pMI k start) := by
  intro k hk
  by_cases hklt : k < a
  · exact hfirst k hklt
  · have _hle : a ≤ k := Nat.le_of_not_gt hklt
    let j := k - a
    have hkj : k = a + j := by omega
    have hj : j < b := by omega
    have heval : eval pMI k start = eval pMI j mid := by
      rw [hkj]
      exact eval_add_eq_eval_mi a j start mid hprefix
    rw [heval]
    exact hsecond j hj

theorem cong_eval_to_step_active_with_guard_mi (F : AST → AST)
    (hwrap : ∀ s, StepActiveShape (F s))
    (hcong : ∀ s s', oneStep pMI s = some s' →
      oneStep pMI (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pMI N s = v → IsNormal pMI v →
      ∃ M, eval pMI M (F s) = F v ∧
        ∀ k, k < M → StepActiveShape (eval pMI k (F s)) := by
  intro N
  induction N with
  | zero =>
      intro s v hs _
      simp only [eval] at hs
      subst hs
      exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
  | succ n ih =>
      intro s v hs hv
      simp only [eval] at hs
      cases hstep : oneStep pMI s with
      | none =>
          rw [hstep] at hs
          subst hs
          exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
      | some s' =>
          rw [hstep] at hs
          obtain ⟨M, hM, hMactive⟩ := ih hs hv
          refine ⟨M + 1, ?_, ?_⟩
          · simp only [eval, hcong s s' hstep]
            exact hM
          · intro k hk
            cases k with
            | zero =>
                simpa only [eval] using hwrap s
            | succ k =>
                have hkM : k < M := by
                  exact Nat.succ_lt_succ_iff.mp (by
                    simpa [Nat.succ_eq_add_one] using hk)
                have htotal :
                    eval pMI (Nat.succ k) (F s) = eval pMI k (F s') := by
                  simp only [eval, hcong s s' hstep]
                rw [htotal]
                exact hMactive k hkM

theorem baseReducts_miEvalK_step_active_raw
    (rules term fuelArg r : AST) (hactive : StepActiveShape r) :
    baseReducts pMI (miEvalK rules term fuelArg r) = [] := by
  cases hactive <;> rfl

theorem os_miEvalK_active_step (rules term fuelArg r r' : AST)
    (hrules : IsNormal pMI rules) (hterm : IsNormal pMI term)
    (hfuel : IsNormal pMI fuelArg)
    (hactive : StepActiveShape r)
    (hstep : oneStep pMI r = some r') :
    oneStep pMI (miEvalK rules term fuelArg r) =
      some (miEvalK rules term fuelArg r') := by
  rw [oneStep.eq_def]
  change
    (match baseReducts pMI (miEvalK rules term fuelArg r) with
    | q :: _ => some q
    | [] => (oneStepList pMI [rules, term, fuelArg, r]).map
        (fun args' => AST.sexp (Label.id "mi-evalK") args')) =
      some (miEvalK rules term fuelArg r')
  rw [baseReducts_miEvalK_step_active_raw rules term fuelArg r hactive]
  simp only [IsNormal] at hrules hterm hfuel
  simp only [oneStepList, hrules, hterm, hfuel, hstep, Option.map_some]
  rfl

theorem os_miEvalK_term_step_active (rules term term' fuelArg r : AST)
    (hrules : IsNormal pMI rules)
    (hactive : StepActiveShape r)
    (hstep : oneStep pMI term = some term') :
    oneStep pMI (miEvalK rules term fuelArg r) =
      some (miEvalK rules term' fuelArg r) := by
  rw [oneStep.eq_def]
  change
    (match baseReducts pMI (miEvalK rules term fuelArg r) with
    | q :: _ => some q
    | [] => (oneStepList pMI [rules, term, fuelArg, r]).map
        (fun args' => AST.sexp (Label.id "mi-evalK") args')) =
      some (miEvalK rules term' fuelArg r)
  rw [baseReducts_miEvalK_step_active_raw rules term fuelArg r hactive]
  simp only [IsNormal] at hrules
  simp only [oneStepList, hrules, hstep, Option.map_some]
  rfl

theorem cong_eval_step_active_fuel_mi (F : AST → AST)
    (hcong : ∀ s s', StepActiveShape s →
      oneStep pMI s = some s' → oneStep pMI (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pMI N s = v →
      (∀ k, k < N → StepActiveShape (eval pMI k s)) →
      ∃ M, eval pMI M (F s) = F v := by
  intro N
  induction N with
  | zero =>
      intro s v hs _
      simp only [eval] at hs
      subst hs
      exact ⟨0, rfl⟩
  | succ n ih =>
      intro s v hs hactive
      simp only [eval] at hs
      cases hstep : oneStep pMI s with
      | none =>
          rw [hstep] at hs
          subst hs
          exact ⟨0, rfl⟩
      | some s' =>
          rw [hstep] at hs
          have hsActive : StepActiveShape s := by
            have h0 := hactive 0 (Nat.zero_lt_succ n)
            simpa only [eval] using h0
          have hactive' : ∀ k, k < n →
              StepActiveShape (eval pMI k s') := by
            intro k hk
            have hk' : Nat.succ k < Nat.succ n := Nat.succ_lt_succ hk
            have hnext := hactive (Nat.succ k) hk'
            have heval : eval pMI (Nat.succ k) s = eval pMI k s' := by
              simp only [eval, hstep]
            simpa only [heval] using hnext
          obtain ⟨M, hM⟩ := ih hs hactive'
          refine ⟨M + 1, ?_⟩
          simp only [eval, hcong s s' hsActive hstep]
          exact hM

theorem miEvalK_eval_of_step_active_step
    (rules term fuelArg r rawNext : AST) (stepFuel : Nat)
    (hrules : IsNormal pMI rules) (hterm : IsNormal pMI term)
    (hfuel : IsNormal pMI fuelArg)
    (hstep : eval pMI stepFuel r = MIStep rawNext)
    (hactive : ∀ k, k < stepFuel →
      StepActiveShape (eval pMI k r)) :
    ∃ N,
      eval pMI N (miEvalK rules term fuelArg r) =
        miEval rules rawNext fuelArg := by
  let F : AST → AST := fun z => miEvalK rules term fuelArg z
  obtain ⟨Mstep, hstepCtx⟩ :=
    cong_eval_step_active_fuel_mi F
      (fun s s' hsActive hs =>
        os_miEvalK_active_step rules term fuelArg s s'
          hrules hterm hfuel hsActive hs)
      stepFuel hstep hactive
  have hfire :
      eval pMI 1 (F (MIStep rawNext)) =
        miEval rules rawNext fuelArg := by
    simp only [F, eval, os_miEvalK_step]
  have htotal := eval_trans_mi Mstep 1
    (miEvalK rules term fuelArg r)
    (F (MIStep rawNext))
    (miEval rules rawNext fuelArg)
    hstepCtx hfire
  exact ⟨Mstep + 1, htotal⟩

theorem miEvalK_eval_of_step_active_none
    (rules term fuelArg r : AST) (stepFuel : Nat)
    (hrules : IsNormal pMI rules) (hterm : IsNormal pMI term)
    (hfuel : IsNormal pMI fuelArg)
    (hstep : eval pMI stepFuel r = MINoStep)
    (hactive : ∀ k, k < stepFuel →
      StepActiveShape (eval pMI k r)) :
    ∃ N,
      eval pMI N (miEvalK rules term fuelArg r) =
        MIDone term := by
  let F : AST → AST := fun z => miEvalK rules term fuelArg z
  obtain ⟨Mstep, hstepCtx⟩ :=
    cong_eval_step_active_fuel_mi F
      (fun s s' hsActive hs =>
        os_miEvalK_active_step rules term fuelArg s s'
          hrules hterm hfuel hsActive hs)
      stepFuel hstep hactive
  have hfire : eval pMI 1 (F MINoStep) = MIDone term := by
    simp only [F, eval, os_miEvalK_done]
  have htotal := eval_trans_mi Mstep 1
    (miEvalK rules term fuelArg r)
    (F MINoStep)
    (MIDone term)
    hstepCtx hfire
  exact ⟨Mstep + 1, htotal⟩

theorem miEval_succ_eval_of_step_active_step
    (rules term fuelArg rawNext : AST) (stepFuel : Nat)
    (hrules : IsNormal pMI rules) (hterm : IsNormal pMI term)
    (hfuel : IsNormal pMI fuelArg)
    (hstep : eval pMI stepFuel (miStep rules term) = MIStep rawNext)
    (hactive : ∀ k, k < stepFuel →
      StepActiveShape (eval pMI k (miStep rules term))) :
    ∃ N,
      eval pMI N (miEval rules term (FS fuelArg)) =
        miEval rules rawNext fuelArg := by
  obtain ⟨M, hK⟩ :=
    miEvalK_eval_of_step_active_step rules term fuelArg
      (miStep rules term) rawNext stepFuel hrules hterm hfuel hstep
      hactive
  have hdispatch :
      eval pMI 1 (miEval rules term (FS fuelArg)) =
        miEvalK rules term fuelArg (miStep rules term) := by
    simp only [eval, os_miEval_succ]
  have htotal := eval_trans_mi 1 M
    (miEval rules term (FS fuelArg))
    (miEvalK rules term fuelArg (miStep rules term))
    (miEval rules rawNext fuelArg)
    hdispatch hK
  exact ⟨1 + M, htotal⟩

theorem miEval_succ_eval_of_step_active_none
    (rules term fuelArg : AST) (stepFuel : Nat)
    (hrules : IsNormal pMI rules) (hterm : IsNormal pMI term)
    (hfuel : IsNormal pMI fuelArg)
    (hstep : eval pMI stepFuel (miStep rules term) = MINoStep)
    (hactive : ∀ k, k < stepFuel →
      StepActiveShape (eval pMI k (miStep rules term))) :
    ∃ N,
      eval pMI N (miEval rules term (FS fuelArg)) =
        MIDone term := by
  obtain ⟨M, hK⟩ :=
    miEvalK_eval_of_step_active_none rules term fuelArg
      (miStep rules term) stepFuel hrules hterm hfuel hstep hactive
  have hdispatch :
      eval pMI 1 (miEval rules term (FS fuelArg)) =
        miEvalK rules term fuelArg (miStep rules term) := by
    simp only [eval, os_miEval_succ]
  have htotal := eval_trans_mi 1 M
    (miEval rules term (FS fuelArg))
    (miEvalK rules term fuelArg (miStep rules term))
    (MIDone term)
    hdispatch hK
  exact ⟨1 + M, htotal⟩

theorem miEvalK_eval_of_term_eval_active
    (rules rawTerm encodedTerm fuelArg r : AST) (termFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hactive : StepActiveShape r)
    (hterm : eval pMI termFuel rawTerm = encodedTerm)
    (hencoded : IsNormal pMI encodedTerm) :
    ∃ N,
      eval pMI N (miEvalK rules rawTerm fuelArg r) =
        miEvalK rules encodedTerm fuelArg r := by
  exact cong_eval_mi (fun z => miEvalK rules z fuelArg r)
    (fun s s' hstep =>
      os_miEvalK_term_step_active rules s s' fuelArg r
        hrules hactive hstep)
    termFuel hterm hencoded

theorem miEval_succ_eval_to_evalK_of_raw_term
    (rules rawTerm encodedTerm fuelArg : AST) (termFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hterm : eval pMI termFuel rawTerm = encodedTerm)
    (hencoded : IsNormal pMI encodedTerm) :
    ∃ N,
      eval pMI N (miEval rules rawTerm (FS fuelArg)) =
        miEvalK rules encodedTerm fuelArg (miStep rules rawTerm) := by
  have hdispatch :
      eval pMI 1 (miEval rules rawTerm (FS fuelArg)) =
        miEvalK rules rawTerm fuelArg (miStep rules rawTerm) := by
    simp only [eval, os_miEval_succ]
  obtain ⟨M, hM⟩ :=
    miEvalK_eval_of_term_eval_active rules rawTerm encodedTerm fuelArg
      (miStep rules rawTerm) termFuel hrules
      (StepActiveShape.step rules rawTerm) hterm hencoded
  have htotal := eval_trans_mi 1 M
    (miEval rules rawTerm (FS fuelArg))
    (miEvalK rules rawTerm fuelArg (miStep rules rawTerm))
    (miEvalK rules encodedTerm fuelArg (miStep rules rawTerm))
    hdispatch hM
  exact ⟨1 + M, htotal⟩

theorem miEval_succ_eval_of_raw_term_step_active_step
    (rules rawTerm encodedTerm fuelArg rawNext : AST)
    (termFuel stepFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hfuel : IsNormal pMI fuelArg)
    (hterm : eval pMI termFuel rawTerm = encodedTerm)
    (hencoded : IsNormal pMI encodedTerm)
    (hstep : eval pMI stepFuel (miStep rules rawTerm) = MIStep rawNext)
    (hactive : ∀ k, k < stepFuel →
      StepActiveShape (eval pMI k (miStep rules rawTerm))) :
    ∃ N,
      eval pMI N (miEval rules rawTerm (FS fuelArg)) =
        miEval rules rawNext fuelArg := by
  obtain ⟨Mterm, htermCtx⟩ :=
    miEval_succ_eval_to_evalK_of_raw_term rules rawTerm encodedTerm
      fuelArg termFuel hrules hterm hencoded
  obtain ⟨Mstep, hstepCtx⟩ :=
    miEvalK_eval_of_step_active_step rules encodedTerm fuelArg
      (miStep rules rawTerm) rawNext stepFuel
      hrules hencoded hfuel hstep hactive
  have htotal := eval_trans_mi Mterm Mstep
    (miEval rules rawTerm (FS fuelArg))
    (miEvalK rules encodedTerm fuelArg (miStep rules rawTerm))
    (miEval rules rawNext fuelArg)
    htermCtx hstepCtx
  exact ⟨Mterm + Mstep, htotal⟩

theorem miEval_succ_eval_of_raw_term_step_active_none
    (rules rawTerm encodedTerm fuelArg : AST)
    (termFuel stepFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hfuel : IsNormal pMI fuelArg)
    (hterm : eval pMI termFuel rawTerm = encodedTerm)
    (hencoded : IsNormal pMI encodedTerm)
    (hstep : eval pMI stepFuel (miStep rules rawTerm) = MINoStep)
    (hactive : ∀ k, k < stepFuel →
      StepActiveShape (eval pMI k (miStep rules rawTerm))) :
    ∃ N,
      eval pMI N (miEval rules rawTerm (FS fuelArg)) =
        MIDone encodedTerm := by
  obtain ⟨Mterm, htermCtx⟩ :=
    miEval_succ_eval_to_evalK_of_raw_term rules rawTerm encodedTerm
      fuelArg termFuel hrules hterm hencoded
  obtain ⟨Mstep, hstepCtx⟩ :=
    miEvalK_eval_of_step_active_none rules encodedTerm fuelArg
      (miStep rules rawTerm) stepFuel
      hrules hencoded hfuel hstep hactive
  have htotal := eval_trans_mi Mterm Mstep
    (miEval rules rawTerm (FS fuelArg))
    (miEvalK rules encodedTerm fuelArg (miStep rules rawTerm))
    (MIDone encodedTerm)
    htermCtx hstepCtx
  exact ⟨Mterm + Mstep, htotal⟩

theorem miEval_succ_eval_of_raw_term_raw_step_some
    (rules rawTerm encodedTerm fuelArg out : AST) (termFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hfuel : IsNormal pMI fuelArg)
    (hterm : eval pMI termFuel rawTerm = encodedTerm)
    (hencoded : IsNormal pMI encodedTerm)
    (hraw : StepRawSome rules rawTerm out) :
    ∃ (rawNext encodedOut : AST) (N normFuel : Nat),
      encAST? out = some encodedOut ∧
      eval pMI N (miEval rules rawTerm (FS fuelArg)) =
        miEval rules rawNext fuelArg ∧
      eval pMI normFuel rawNext = encodedOut ∧
      IsNormal pMI encodedOut := by
  unfold StepRawSome at hraw
  obtain ⟨rawNext, encodedOut, stepFuel, normFuel, hout, hstep,
    hactive, hnorm, houtNorm⟩ := hraw
  obtain ⟨N, hEval⟩ :=
    miEval_succ_eval_of_raw_term_step_active_step rules rawTerm
      encodedTerm fuelArg rawNext termFuel stepFuel
      hrules hfuel hterm hencoded hstep hactive
  exact ⟨rawNext, encodedOut, N, normFuel, hout, hEval, hnorm, houtNorm⟩

theorem miEval_succ_eval_of_raw_term_raw_step_none
    (rules rawTerm encodedTerm fuelArg : AST) (termFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hfuel : IsNormal pMI fuelArg)
    (hterm : eval pMI termFuel rawTerm = encodedTerm)
    (hencoded : IsNormal pMI encodedTerm)
    (hraw : StepRawNone rules rawTerm) :
    ∃ N,
      eval pMI N (miEval rules rawTerm (FS fuelArg)) =
        MIDone encodedTerm := by
  unfold StepRawNone at hraw
  obtain ⟨stepFuel, hstep, hactive⟩ := hraw
  exact miEval_succ_eval_of_raw_term_step_active_none rules rawTerm
    encodedTerm fuelArg termFuel stepFuel
    hrules hfuel hterm hencoded hstep hactive

theorem miEval_succ_eval_of_raw_step_some
    (rules term fuelArg out : AST)
    (hrules : IsNormal pMI rules) (hterm : IsNormal pMI term)
    (hfuel : IsNormal pMI fuelArg)
    (hraw : StepRawSome rules term out) :
    ∃ (rawNext encodedOut : AST) (N normFuel : Nat),
      encAST? out = some encodedOut ∧
      eval pMI N (miEval rules term (FS fuelArg)) =
        miEval rules rawNext fuelArg ∧
      eval pMI normFuel rawNext = encodedOut ∧
      IsNormal pMI encodedOut := by
  unfold StepRawSome at hraw
  obtain ⟨rawNext, encodedOut, stepFuel, normFuel, hout, hstep,
    hactive, hnorm, houtNorm⟩ := hraw
  obtain ⟨N, hEval⟩ :=
    miEval_succ_eval_of_step_active_step rules term fuelArg rawNext
      stepFuel hrules hterm hfuel hstep hactive
  exact ⟨rawNext, encodedOut, N, normFuel, hout, hEval, hnorm, houtNorm⟩

theorem miEval_succ_eval_of_raw_step_none
    (rules term fuelArg : AST)
    (hrules : IsNormal pMI rules) (hterm : IsNormal pMI term)
    (hfuel : IsNormal pMI fuelArg)
    (hraw : StepRawNone rules term) :
    ∃ N,
      eval pMI N (miEval rules term (FS fuelArg)) =
        MIDone term := by
  unfold StepRawNone at hraw
  obtain ⟨stepFuel, hstep, hactive⟩ := hraw
  exact miEval_succ_eval_of_step_active_none rules term fuelArg
    stepFuel hrules hterm hfuel hstep hactive

theorem baseReducts_miStepArgsK_step_active_raw
    (rules x xs r : AST) (hactive : StepActiveShape r) :
    baseReducts pMI (miStepArgsK rules x xs r) = [] := by
  cases hactive <;> rfl

theorem os_miStepArgsK_active_step (rules x xs r r' : AST)
    (hrules : IsNormal pMI rules) (hx : IsNormal pMI x)
    (hxs : IsNormal pMI xs) (hactive : StepActiveShape r)
    (hstep : oneStep pMI r = some r') :
    oneStep pMI (miStepArgsK rules x xs r) =
      some (miStepArgsK rules x xs r') := by
  rw [oneStep.eq_def]
  change
    (match baseReducts pMI (miStepArgsK rules x xs r) with
    | q :: _ => some q
    | [] => (oneStepList pMI [rules, x, xs, r]).map
        (fun args' => AST.sexp (Label.id "mi-step-argsK") args')) =
      some (miStepArgsK rules x xs r')
  rw [baseReducts_miStepArgsK_step_active_raw rules x xs r hactive]
  simp only [IsNormal] at hrules hx hxs
  simp only [oneStepList, hrules, hx, hxs, hstep, Option.map_some]
  rfl

theorem baseReducts_miStepArgsRestK_active_raw
    (x r : AST) (hactive : ArgsActiveShape r) :
    baseReducts pMI (miStepArgsRestK x r) = [] := by
  cases hactive <;> rfl

theorem os_miStepArgsRestK_active_step (x r r' : AST)
    (hx : IsNormal pMI x) (hactive : ArgsActiveShape r)
    (hstep : oneStep pMI r = some r') :
    oneStep pMI (miStepArgsRestK x r) =
      some (miStepArgsRestK x r') := by
  rw [oneStep.eq_def]
  change
    (match baseReducts pMI (miStepArgsRestK x r) with
    | q :: _ => some q
    | [] => (oneStepList pMI [x, r]).map
        (fun args' => AST.sexp (Label.id "mi-step-args-restK") args')) =
      some (miStepArgsRestK x r')
  rw [baseReducts_miStepArgsRestK_active_raw x r hactive]
  simp only [IsNormal] at hx
  simp only [oneStepList, hx, hstep, Option.map_some]
  rfl

theorem baseReducts_miStepAppK_active_raw (h r : AST)
    (hactive : ArgsActiveShape r) :
    baseReducts pMI (miStepAppK h r) = [] := by
  cases hactive <;> rfl

theorem os_miStepAppK_active_step (h r r' : AST)
    (hh : IsNormal pMI h)
    (hactive : ArgsActiveShape r)
    (hstep : oneStep pMI r = some r') :
    oneStep pMI (miStepAppK h r) = some (miStepAppK h r') := by
  rw [oneStep.eq_def]
  change
    (match baseReducts pMI (miStepAppK h r) with
    | q :: _ => some q
    | [] => (oneStepList pMI [h, r]).map
        (fun args' => AST.sexp (Label.id "mi-step-appK") args')) =
      some (miStepAppK h r')
  rw [baseReducts_miStepAppK_active_raw h r hactive]
  simp only [IsNormal] at hh
  simp only [oneStepList, hh, hstep, Option.map_some]
  rfl

theorem cong_eval_args_active_fuel_mi (F : AST → AST)
    (hcong : ∀ s s', ArgsActiveShape s →
      oneStep pMI s = some s' → oneStep pMI (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pMI N s = v →
      (∀ k, k < N → ArgsActiveShape (eval pMI k s)) →
      ∃ M, eval pMI M (F s) = F v := by
  intro N
  induction N with
  | zero =>
      intro s v hs _
      simp only [eval] at hs
      subst hs
      exact ⟨0, rfl⟩
  | succ n ih =>
      intro s v hs hactive
      simp only [eval] at hs
      cases hstep : oneStep pMI s with
      | none =>
          rw [hstep] at hs
          subst hs
          exact ⟨0, rfl⟩
      | some s' =>
          rw [hstep] at hs
          have hsActive : ArgsActiveShape s := by
            have h0 := hactive 0 (Nat.zero_lt_succ n)
            simpa only [eval] using h0
          have hactive' : ∀ k, k < n →
              ArgsActiveShape (eval pMI k s') := by
            intro k hk
            have hk' : Nat.succ k < Nat.succ n := Nat.succ_lt_succ hk
            have hnext := hactive (Nat.succ k) hk'
            have heval : eval pMI (Nat.succ k) s = eval pMI k s' := by
              simp only [eval, hstep]
            simpa only [heval] using hnext
          obtain ⟨M, hM⟩ := ih hs hactive'
          refine ⟨M + 1, ?_⟩
          simp only [eval, hcong s s' hsActive hstep]
          exact hM

theorem cong_eval_args_active_with_guard_mi (F : AST → AST)
    (hwrap : ∀ s, ArgsActiveShape s → ArgsActiveShape (F s))
    (hcong : ∀ s s', ArgsActiveShape s →
      oneStep pMI s = some s' → oneStep pMI (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pMI N s = v →
      (∀ k, k < N → ArgsActiveShape (eval pMI k s)) →
        ∃ M, eval pMI M (F s) = F v ∧
          ∀ k, k < M → ArgsActiveShape (eval pMI k (F s)) := by
  intro N
  induction N with
  | zero =>
      intro s v hs _
      simp only [eval] at hs
      subst hs
      exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
  | succ n ih =>
      intro s v hs hactive
      simp only [eval] at hs
      cases hstep : oneStep pMI s with
      | none =>
          rw [hstep] at hs
          subst hs
          exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
      | some s' =>
          rw [hstep] at hs
          have hsActive : ArgsActiveShape s := by
            have h0 := hactive 0 (Nat.zero_lt_succ n)
            simpa only [eval] using h0
          have hactive' : ∀ k, k < n →
              ArgsActiveShape (eval pMI k s') := by
            intro k hk
            have hk' : Nat.succ k < Nat.succ n := Nat.succ_lt_succ hk
            have hnext := hactive (Nat.succ k) hk'
            have heval : eval pMI (Nat.succ k) s = eval pMI k s' := by
              simp only [eval, hstep]
            simpa only [heval] using hnext
          obtain ⟨M, hM, hMactive⟩ := ih hs hactive'
          refine ⟨M + 1, ?_, ?_⟩
          · simp only [eval, hcong s s' hsActive hstep]
            exact hM
          · intro k hk
            cases k with
            | zero =>
                simpa only [eval] using hwrap s hsActive
            | succ k =>
                have hkM : k < M := by
                  exact Nat.succ_lt_succ_iff.mp (by
                    simpa [Nat.succ_eq_add_one] using hk)
                have htotal :
                    eval pMI (Nat.succ k) (F s) = eval pMI k (F s') := by
                  simp only [eval, hcong s s' hsActive hstep]
                rw [htotal]
                exact hMactive k hkM

theorem cong_eval_args_to_step_active_with_guard_mi (F : AST → AST)
    (hwrap : ∀ s, ArgsActiveShape s → StepActiveShape (F s))
    (hcong : ∀ s s', ArgsActiveShape s →
      oneStep pMI s = some s' → oneStep pMI (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pMI N s = v →
      (∀ k, k < N → ArgsActiveShape (eval pMI k s)) →
        ∃ M, eval pMI M (F s) = F v ∧
          ∀ k, k < M → StepActiveShape (eval pMI k (F s)) := by
  intro N
  induction N with
  | zero =>
      intro s v hs _
      simp only [eval] at hs
      subst hs
      exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
  | succ n ih =>
      intro s v hs hactive
      simp only [eval] at hs
      cases hstep : oneStep pMI s with
      | none =>
          rw [hstep] at hs
          subst hs
          exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
      | some s' =>
          rw [hstep] at hs
          have hsActive : ArgsActiveShape s := by
            have h0 := hactive 0 (Nat.zero_lt_succ n)
            simpa only [eval] using h0
          have hactive' : ∀ k, k < n →
              ArgsActiveShape (eval pMI k s') := by
            intro k hk
            have hk' : Nat.succ k < Nat.succ n := Nat.succ_lt_succ hk
            have hnext := hactive (Nat.succ k) hk'
            have heval : eval pMI (Nat.succ k) s = eval pMI k s' := by
              simp only [eval, hstep]
            simpa only [heval] using hnext
          obtain ⟨M, hM, hMactive⟩ := ih hs hactive'
          refine ⟨M + 1, ?_, ?_⟩
          · simp only [eval, hcong s s' hsActive hstep]
            exact hM
          · intro k hk
            cases k with
            | zero =>
                simpa only [eval] using hwrap s hsActive
            | succ k =>
                have hkM : k < M := by
                  exact Nat.succ_lt_succ_iff.mp (by
                    simpa [Nat.succ_eq_add_one] using hk)
                have htotal :
                    eval pMI (Nat.succ k) (F s) = eval pMI k (F s') := by
                  simp only [eval, hcong s s' hsActive hstep]
                rw [htotal]
                exact hMactive k hkM

theorem cong_eval_step_to_args_active_with_guard_mi (F : AST → AST)
    (hwrap : ∀ s, StepActiveShape s → ArgsActiveShape (F s))
    (hcong : ∀ s s', StepActiveShape s →
      oneStep pMI s = some s' → oneStep pMI (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pMI N s = v →
      (∀ k, k < N → StepActiveShape (eval pMI k s)) →
        ∃ M, eval pMI M (F s) = F v ∧
          ∀ k, k < M → ArgsActiveShape (eval pMI k (F s)) := by
  intro N
  induction N with
  | zero =>
      intro s v hs _
      simp only [eval] at hs
      subst hs
      exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
  | succ n ih =>
      intro s v hs hactive
      simp only [eval] at hs
      cases hstep : oneStep pMI s with
      | none =>
          rw [hstep] at hs
          subst hs
          exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
      | some s' =>
          rw [hstep] at hs
          have hsActive : StepActiveShape s := by
            have h0 := hactive 0 (Nat.zero_lt_succ n)
            simpa only [eval] using h0
          have hactive' : ∀ k, k < n →
              StepActiveShape (eval pMI k s') := by
            intro k hk
            have hk' : Nat.succ k < Nat.succ n := Nat.succ_lt_succ hk
            have hnext := hactive (Nat.succ k) hk'
            have heval : eval pMI (Nat.succ k) s = eval pMI k s' := by
              simp only [eval, hstep]
            simpa only [heval] using hnext
          obtain ⟨M, hM, hMactive⟩ := ih hs hactive'
          refine ⟨M + 1, ?_, ?_⟩
          · simp only [eval, hcong s s' hsActive hstep]
            exact hM
          · intro k hk
            cases k with
            | zero =>
                simpa only [eval] using hwrap s hsActive
            | succ k =>
                have hkM : k < M := by
                  exact Nat.succ_lt_succ_iff.mp (by
                    simpa [Nat.succ_eq_add_one] using hk)
                have htotal :
                    eval pMI (Nat.succ k) (F s) = eval pMI k (F s') := by
                  simp only [eval, hcong s s' hsActive hstep]
                rw [htotal]
                exact hMactive k hkM

theorem miStepAppK_eval_of_args_active_step_named (h : String)
    (r argsOut : AST) (argsFuel : Nat)
    (hargs : eval pMI argsFuel r = MIArgsStep argsOut)
    (hactive : ∀ k, k < argsFuel → ArgsActiveShape (eval pMI k r)) :
    ∃ N, eval pMI N (miStepAppK (con0 h) r) =
      MIStep (MIApp h argsOut) := by
  let F : AST → AST := fun z => miStepAppK (con0 h) z
  obtain ⟨Margs, hargsCtx⟩ :=
    cong_eval_args_active_fuel_mi F
      (fun s s' hactiveStep hstep =>
        os_miStepAppK_active_step (con0 h) s s'
          (normal_con0 h) hactiveStep hstep)
      argsFuel hargs hactive
  have hfire :
      eval pMI 1 (F (MIArgsStep argsOut)) =
        MIStep (MIApp h argsOut) := by
    simp only [F, eval, os_miStepAppK_args_named]
  have htotal := eval_trans_mi Margs 1
    (miStepAppK (con0 h) r)
    (F (MIArgsStep argsOut))
    (MIStep (MIApp h argsOut))
    hargsCtx hfire
  exact ⟨Margs + 1, htotal⟩

theorem miStepAppK_eval_of_args_active_none_named (h : String)
    (r : AST) (argsFuel : Nat)
    (hargs : eval pMI argsFuel r = MINoArgsStep)
    (hactive : ∀ k, k < argsFuel → ArgsActiveShape (eval pMI k r)) :
    ∃ N, eval pMI N (miStepAppK (con0 h) r) = MINoStep := by
  let F : AST → AST := fun z => miStepAppK (con0 h) z
  obtain ⟨Margs, hargsCtx⟩ :=
    cong_eval_args_active_fuel_mi F
      (fun s s' hactiveStep hstep =>
        os_miStepAppK_active_step (con0 h) s s'
          (normal_con0 h) hactiveStep hstep)
      argsFuel hargs hactive
  have hfire : eval pMI 1 (F MINoArgsStep) = MINoStep := by
    simp only [F, eval, os_miStepAppK_none]
  have htotal := eval_trans_mi Margs 1
    (miStepAppK (con0 h) r)
    (F MINoArgsStep)
    MINoStep
    hargsCtx hfire
  exact ⟨Margs + 1, htotal⟩

theorem miStepAppK_eval_of_args_active_step_named_with_guard (h : String)
    (r argsOut : AST) (argsFuel : Nat)
    (hargs : eval pMI argsFuel r = MIArgsStep argsOut)
    (hactive : ∀ k, k < argsFuel → ArgsActiveShape (eval pMI k r)) :
    ∃ N,
      eval pMI N (miStepAppK (con0 h) r) =
        MIStep (MIApp h argsOut) ∧
      ∀ k, k < N →
        StepActiveShape (eval pMI k (miStepAppK (con0 h) r)) := by
  let F : AST → AST := fun z => miStepAppK (con0 h) z
  obtain ⟨Margs, hargsCtx, hargsCtxActive⟩ :=
    cong_eval_args_to_step_active_with_guard_mi F
      (fun s _hs => StepActiveShape.appK (con0 h) s)
      (fun s s' hactiveStep hstep =>
        os_miStepAppK_active_step (con0 h) s s'
          (normal_con0 h) hactiveStep hstep)
      argsFuel hargs hactive
  have hfire :
      eval pMI 1 (F (MIArgsStep argsOut)) =
        MIStep (MIApp h argsOut) := by
    simp only [F, eval, os_miStepAppK_args_named]
  have htotal := eval_trans_mi Margs 1
    (miStepAppK (con0 h) r)
    (F (MIArgsStep argsOut))
    (MIStep (MIApp h argsOut))
    hargsCtx hfire
  refine ⟨Margs + 1, htotal, ?_⟩
  intro k hk
  by_cases hlt : k < Margs
  · exact hargsCtxActive k hlt
  · have hk_ge : Margs ≤ k := Nat.le_of_not_gt hlt
    have hk_le : k ≤ Margs := Nat.le_of_lt_succ hk
    have hk_eq : k = Margs := Nat.le_antisymm hk_le hk_ge
    subst k
    change StepActiveShape (eval pMI Margs (F r))
    rw [hargsCtx]
    exact StepActiveShape.appK (con0 h) (MIArgsStep argsOut)

theorem miStepAppK_eval_of_args_active_none_named_with_guard (h : String)
    (r : AST) (argsFuel : Nat)
    (hargs : eval pMI argsFuel r = MINoArgsStep)
    (hactive : ∀ k, k < argsFuel → ArgsActiveShape (eval pMI k r)) :
    ∃ N,
      eval pMI N (miStepAppK (con0 h) r) = MINoStep ∧
      ∀ k, k < N →
        StepActiveShape (eval pMI k (miStepAppK (con0 h) r)) := by
  let F : AST → AST := fun z => miStepAppK (con0 h) z
  obtain ⟨Margs, hargsCtx, hargsCtxActive⟩ :=
    cong_eval_args_to_step_active_with_guard_mi F
      (fun s _hs => StepActiveShape.appK (con0 h) s)
      (fun s s' hactiveStep hstep =>
        os_miStepAppK_active_step (con0 h) s s'
          (normal_con0 h) hactiveStep hstep)
      argsFuel hargs hactive
  have hfire : eval pMI 1 (F MINoArgsStep) = MINoStep := by
    simp only [F, eval, os_miStepAppK_none]
  have htotal := eval_trans_mi Margs 1
    (miStepAppK (con0 h) r)
    (F MINoArgsStep)
    MINoStep
    hargsCtx hfire
  refine ⟨Margs + 1, htotal, ?_⟩
  intro k hk
  by_cases hlt : k < Margs
  · exact hargsCtxActive k hlt
  · have hk_ge : Margs ≤ k := Nat.le_of_not_gt hlt
    have hk_le : k ≤ Margs := Nat.le_of_lt_succ hk
    have hk_eq : k = Margs := Nat.le_antisymm hk_le hk_ge
    subst k
    change StepActiveShape (eval pMI Margs (F r))
    rw [hargsCtx]
    exact StepActiveShape.appK (con0 h) MINoArgsStep

theorem miStepArgsK_eval_of_head_step_active
    (rules x xs next : AST) (headFuel : Nat)
    (hrules : IsNormal pMI rules) (hx : IsNormal pMI x)
    (hxs : IsNormal pMI xs)
    (hhead : eval pMI headFuel (miStep rules x) = MIStep next)
    (hheadActive : ∀ k, k < headFuel →
      StepActiveShape (eval pMI k (miStep rules x))) :
    ∃ N,
      eval pMI N (miStepArgsK rules x xs (miStep rules x)) =
        MIArgsStep (MICons next xs) ∧
      ∀ k, k < N →
        ArgsActiveShape
          (eval pMI k (miStepArgsK rules x xs (miStep rules x))) := by
  let F : AST → AST := fun z => miStepArgsK rules x xs z
  obtain ⟨Mhead, hheadCtx, hheadCtxActive⟩ :=
    cong_eval_step_to_args_active_with_guard_mi F
      (fun s _hs => ArgsActiveShape.argsK rules x xs s)
      (fun s s' hactiveStep hstep =>
        os_miStepArgsK_active_step rules x xs s s'
          hrules hx hxs hactiveStep hstep)
      headFuel hhead hheadActive
  have hfire :
      eval pMI 1 (F (MIStep next)) = MIArgsStep (MICons next xs) := by
    simp only [F, eval, os_miStepArgsK_step]
  have htotal := eval_trans_mi Mhead 1
    (miStepArgsK rules x xs (miStep rules x))
    (F (MIStep next))
    (MIArgsStep (MICons next xs))
    hheadCtx hfire
  refine ⟨Mhead + 1, htotal, ?_⟩
  intro k hk
  by_cases hlt : k < Mhead
  · exact hheadCtxActive k hlt
  · have hk_ge : Mhead ≤ k := Nat.le_of_not_gt hlt
    have hk_le : k ≤ Mhead := Nat.le_of_lt_succ hk
    have hk_eq : k = Mhead := Nat.le_antisymm hk_le hk_ge
    subst k
    change ArgsActiveShape (eval pMI Mhead (F (miStep rules x)))
    rw [hheadCtx]
    exact ArgsActiveShape.argsK rules x xs (MIStep next)

theorem miStepArgsK_eval_of_head_none_rest_step_active
    (rules x xs xsOut : AST) (headFuel restFuel : Nat)
    (hrules : IsNormal pMI rules) (hx : IsNormal pMI x)
    (hxs : IsNormal pMI xs)
    (hhead : eval pMI headFuel (miStep rules x) = MINoStep)
    (hheadActive : ∀ k, k < headFuel →
      StepActiveShape (eval pMI k (miStep rules x)))
    (hrest : eval pMI restFuel (miStepArgs rules xs) =
      MIArgsStep xsOut)
    (hrestActive : ∀ k, k < restFuel →
      ArgsActiveShape (eval pMI k (miStepArgs rules xs))) :
    ∃ N,
      eval pMI N (miStepArgsK rules x xs (miStep rules x)) =
        MIArgsStep (MICons x xsOut) ∧
      ∀ k, k < N →
        ArgsActiveShape
          (eval pMI k (miStepArgsK rules x xs (miStep rules x))) := by
  let F : AST → AST := fun z => miStepArgsK rules x xs z
  obtain ⟨Mhead, hheadCtx, hheadCtxActive⟩ :=
    cong_eval_step_to_args_active_with_guard_mi F
      (fun s _hs => ArgsActiveShape.argsK rules x xs s)
      (fun s s' hactiveStep hstep =>
        os_miStepArgsK_active_step rules x xs s s'
          hrules hx hxs hactiveStep hstep)
      headFuel hhead hheadActive
  let G : AST → AST := fun z => miStepArgsRestK x z
  have hnone :
      eval pMI 1 (F MINoStep) = G (miStepArgs rules xs) := by
    simp only [F, G, eval, os_miStepArgsK_none]
  obtain ⟨Mrest, hrestCtx, hrestCtxActive⟩ :=
    cong_eval_args_active_with_guard_mi G
      (fun s _hs => ArgsActiveShape.argsRestK x s)
      (fun s s' hactiveArgs hstep =>
        os_miStepArgsRestK_active_step x s s' hx hactiveArgs hstep)
      restFuel hrest hrestActive
  have hrestFire :
      eval pMI 1 (G (MIArgsStep xsOut)) =
        MIArgsStep (MICons x xsOut) := by
    simp only [G, eval, os_miStepArgsRestK_step]
  have htailCtx := eval_trans_mi 1 Mrest
    (F MINoStep)
    (G (miStepArgs rules xs))
    (G (MIArgsStep xsOut))
    hnone hrestCtx
  have htail := eval_trans_mi (1 + Mrest) 1
    (F MINoStep)
    (G (MIArgsStep xsOut))
    (MIArgsStep (MICons x xsOut))
    htailCtx hrestFire
  have htailActive :
      ∀ k, k < 1 + Mrest + 1 →
        ArgsActiveShape (eval pMI k (F MINoStep)) := by
    intro k hk
    cases k with
    | zero =>
        simpa only [eval, F] using ArgsActiveShape.argsK rules x xs MINoStep
    | succ k =>
        by_cases hlt : k < Mrest
        · have heval :
            eval pMI (Nat.succ k) (F MINoStep) =
              eval pMI k (G (miStepArgs rules xs)) := by
              simp only [F, G, eval, os_miStepArgsK_none]
          rw [heval]
          exact hrestCtxActive k hlt
        · have hk_le : k ≤ Mrest := by omega
          have hk_ge : Mrest ≤ k := Nat.le_of_not_gt hlt
          have hk_eq : k = Mrest := Nat.le_antisymm hk_le hk_ge
          subst k
          have heval :
              eval pMI (Nat.succ Mrest) (F MINoStep) =
                G (MIArgsStep xsOut) := by
            simp only [F, G, eval, os_miStepArgsK_none]
            exact hrestCtx
          rw [heval]
          exact ArgsActiveShape.argsRestK x (MIArgsStep xsOut)
  have htotal := eval_trans_mi Mhead (1 + Mrest + 1)
    (miStepArgsK rules x xs (miStep rules x))
    (F MINoStep)
    (MIArgsStep (MICons x xsOut))
    hheadCtx htail
  exact ⟨Mhead + (1 + Mrest + 1), htotal,
    args_active_append_mi Mhead (1 + Mrest + 1)
      hheadCtx hheadCtxActive htailActive⟩

theorem miStepArgsK_eval_of_head_none_rest_none_active
    (rules x xs : AST) (headFuel restFuel : Nat)
    (hrules : IsNormal pMI rules) (hx : IsNormal pMI x)
    (hxs : IsNormal pMI xs)
    (hhead : eval pMI headFuel (miStep rules x) = MINoStep)
    (hheadActive : ∀ k, k < headFuel →
      StepActiveShape (eval pMI k (miStep rules x)))
    (hrest : eval pMI restFuel (miStepArgs rules xs) = MINoArgsStep)
    (hrestActive : ∀ k, k < restFuel →
      ArgsActiveShape (eval pMI k (miStepArgs rules xs))) :
    ∃ N,
      eval pMI N (miStepArgsK rules x xs (miStep rules x)) =
        MINoArgsStep ∧
      ∀ k, k < N →
        ArgsActiveShape
          (eval pMI k (miStepArgsK rules x xs (miStep rules x))) := by
  let F : AST → AST := fun z => miStepArgsK rules x xs z
  obtain ⟨Mhead, hheadCtx, hheadCtxActive⟩ :=
    cong_eval_step_to_args_active_with_guard_mi F
      (fun s _hs => ArgsActiveShape.argsK rules x xs s)
      (fun s s' hactiveStep hstep =>
        os_miStepArgsK_active_step rules x xs s s'
          hrules hx hxs hactiveStep hstep)
      headFuel hhead hheadActive
  let G : AST → AST := fun z => miStepArgsRestK x z
  have hnone :
      eval pMI 1 (F MINoStep) = G (miStepArgs rules xs) := by
    simp only [F, G, eval, os_miStepArgsK_none]
  obtain ⟨Mrest, hrestCtx, hrestCtxActive⟩ :=
    cong_eval_args_active_with_guard_mi G
      (fun s _hs => ArgsActiveShape.argsRestK x s)
      (fun s s' hactiveArgs hstep =>
        os_miStepArgsRestK_active_step x s s' hx hactiveArgs hstep)
      restFuel hrest hrestActive
  have hrestFire :
      eval pMI 1 (G MINoArgsStep) = MINoArgsStep := by
    simp only [G, eval, os_miStepArgsRestK_none]
  have htailCtx := eval_trans_mi 1 Mrest
    (F MINoStep)
    (G (miStepArgs rules xs))
    (G MINoArgsStep)
    hnone hrestCtx
  have htail := eval_trans_mi (1 + Mrest) 1
    (F MINoStep)
    (G MINoArgsStep)
    MINoArgsStep
    htailCtx hrestFire
  have htailActive :
      ∀ k, k < 1 + Mrest + 1 →
        ArgsActiveShape (eval pMI k (F MINoStep)) := by
    intro k hk
    cases k with
    | zero =>
        simpa only [eval, F] using ArgsActiveShape.argsK rules x xs MINoStep
    | succ k =>
        by_cases hlt : k < Mrest
        · have heval :
            eval pMI (Nat.succ k) (F MINoStep) =
              eval pMI k (G (miStepArgs rules xs)) := by
              simp only [F, G, eval, os_miStepArgsK_none]
          rw [heval]
          exact hrestCtxActive k hlt
        · have hk_le : k ≤ Mrest := by omega
          have hk_ge : Mrest ≤ k := Nat.le_of_not_gt hlt
          have hk_eq : k = Mrest := Nat.le_antisymm hk_le hk_ge
          subst k
          have heval :
              eval pMI (Nat.succ Mrest) (F MINoStep) =
                G MINoArgsStep := by
            simp only [F, G, eval, os_miStepArgsK_none]
            exact hrestCtx
          rw [heval]
          exact ArgsActiveShape.argsRestK x MINoArgsStep
  have htotal := eval_trans_mi Mhead (1 + Mrest + 1)
    (miStepArgsK rules x xs (miStep rules x))
    (F MINoStep)
    MINoArgsStep
    hheadCtx htail
  exact ⟨Mhead + (1 + Mrest + 1), htotal,
    args_active_append_mi Mhead (1 + Mrest + 1)
      hheadCtx hheadCtxActive htailActive⟩

theorem miStepArgs_cons_eval_of_head_step_active
    (rules x xs next : AST) (headFuel : Nat)
    (hrules : IsNormal pMI rules) (hx : IsNormal pMI x)
    (hxs : IsNormal pMI xs)
    (hhead : eval pMI headFuel (miStep rules x) = MIStep next)
    (hheadActive : ∀ k, k < headFuel →
      StepActiveShape (eval pMI k (miStep rules x))) :
    ∃ N,
      eval pMI N (miStepArgs rules (MICons x xs)) =
        MIArgsStep (MICons next xs) ∧
      ∀ k, k < N →
        ArgsActiveShape
          (eval pMI k (miStepArgs rules (MICons x xs))) := by
  obtain ⟨M, hK, hKActive⟩ :=
    miStepArgsK_eval_of_head_step_active rules x xs next headFuel
      hrules hx hxs hhead hheadActive
  have hdispatch :
      eval pMI 1 (miStepArgs rules (MICons x xs)) =
        miStepArgsK rules x xs (miStep rules x) := by
    simp only [eval, os_miStepArgs_cons]
  have htotal := eval_trans_mi 1 M
    (miStepArgs rules (MICons x xs))
    (miStepArgsK rules x xs (miStep rules x))
    (MIArgsStep (MICons next xs))
    hdispatch hK
  exact ⟨1 + M, htotal,
    args_active_append_mi 1 M hdispatch
      (miStepArgs_cons_active_sim rules x xs).2 hKActive⟩

theorem miStepArgs_cons_eval_of_head_none_rest_step_active
    (rules x xs xsOut : AST) (headFuel restFuel : Nat)
    (hrules : IsNormal pMI rules) (hx : IsNormal pMI x)
    (hxs : IsNormal pMI xs)
    (hhead : eval pMI headFuel (miStep rules x) = MINoStep)
    (hheadActive : ∀ k, k < headFuel →
      StepActiveShape (eval pMI k (miStep rules x)))
    (hrest : eval pMI restFuel (miStepArgs rules xs) =
      MIArgsStep xsOut)
    (hrestActive : ∀ k, k < restFuel →
      ArgsActiveShape (eval pMI k (miStepArgs rules xs))) :
    ∃ N,
      eval pMI N (miStepArgs rules (MICons x xs)) =
        MIArgsStep (MICons x xsOut) ∧
      ∀ k, k < N →
        ArgsActiveShape
          (eval pMI k (miStepArgs rules (MICons x xs))) := by
  obtain ⟨M, hK, hKActive⟩ :=
    miStepArgsK_eval_of_head_none_rest_step_active
      rules x xs xsOut headFuel restFuel
      hrules hx hxs hhead hheadActive hrest hrestActive
  have hdispatch :
      eval pMI 1 (miStepArgs rules (MICons x xs)) =
        miStepArgsK rules x xs (miStep rules x) := by
    simp only [eval, os_miStepArgs_cons]
  have htotal := eval_trans_mi 1 M
    (miStepArgs rules (MICons x xs))
    (miStepArgsK rules x xs (miStep rules x))
    (MIArgsStep (MICons x xsOut))
    hdispatch hK
  exact ⟨1 + M, htotal,
    args_active_append_mi 1 M hdispatch
      (miStepArgs_cons_active_sim rules x xs).2 hKActive⟩

theorem miStepArgs_cons_eval_of_head_none_rest_none_active
    (rules x xs : AST) (headFuel restFuel : Nat)
    (hrules : IsNormal pMI rules) (hx : IsNormal pMI x)
    (hxs : IsNormal pMI xs)
    (hhead : eval pMI headFuel (miStep rules x) = MINoStep)
    (hheadActive : ∀ k, k < headFuel →
      StepActiveShape (eval pMI k (miStep rules x)))
    (hrest : eval pMI restFuel (miStepArgs rules xs) = MINoArgsStep)
    (hrestActive : ∀ k, k < restFuel →
      ArgsActiveShape (eval pMI k (miStepArgs rules xs))) :
    ∃ N,
      eval pMI N (miStepArgs rules (MICons x xs)) =
        MINoArgsStep ∧
      ∀ k, k < N →
        ArgsActiveShape
          (eval pMI k (miStepArgs rules (MICons x xs))) := by
  obtain ⟨M, hK, hKActive⟩ :=
    miStepArgsK_eval_of_head_none_rest_none_active
      rules x xs headFuel restFuel
      hrules hx hxs hhead hheadActive hrest hrestActive
  have hdispatch :
      eval pMI 1 (miStepArgs rules (MICons x xs)) =
        miStepArgsK rules x xs (miStep rules x) := by
    simp only [eval, os_miStepArgs_cons]
  have htotal := eval_trans_mi 1 M
    (miStepArgs rules (MICons x xs))
    (miStepArgsK rules x xs (miStep rules x))
    MINoArgsStep
    hdispatch hK
  exact ⟨1 + M, htotal,
    args_active_append_mi 1 M hdispatch
      (miStepArgs_cons_active_sim rules x xs).2 hKActive⟩

theorem baseReducts_miStepRootK_active_mivar_raw (rules r : AST) (v : String)
    (hactive : RootActiveShape r) :
    baseReducts pMI (miStepRootK rules (MIVar v) r) = [] := by
  cases hactive <;> rfl

theorem baseReducts_miStepRootK_active_misym_raw (rules r : AST) (s : String)
    (hactive : RootActiveShape r) :
    baseReducts pMI (miStepRootK rules (MISym s) r) = [] := by
  cases hactive <;> rfl

theorem baseReducts_miStepRootK_active_miapp_raw (rules args r : AST) (h : String)
    (hactive : RootActiveShape r) :
    baseReducts pMI (miStepRootK rules (MIApp h args) r) = [] := by
  cases hactive <;> rfl

theorem baseReducts_miStepRootK_active_misubst_raw
    (rules bs rhs r : AST)
    (hactive : RootActiveShape r) :
    baseReducts pMI (miStepRootK rules (miSubst bs rhs) r) = [] := by
  cases hactive <;> rfl

theorem baseReducts_miStepRootK_active_misubstVarK_raw
    (rules orig arg r : AST)
    (hactive : RootActiveShape r) :
    baseReducts pMI (miStepRootK rules (miSubstVarK orig arg) r) = [] := by
  cases hactive <;> rfl

theorem os_miStepRootK_active_step_mivar (rules r r' : AST) (v : String)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r)
    (hstep : oneStep pMI r = some r') :
    oneStep pMI (miStepRootK rules (MIVar v) r) =
      some (miStepRootK rules (MIVar v) r') := by
  rw [oneStep.eq_def]
  change
    (match baseReducts pMI (miStepRootK rules (MIVar v) r) with
    | q :: _ => some q
    | [] => (oneStepList pMI [rules, MIVar v, r]).map
        (fun args' => AST.sexp (Label.id "mi-step-rootK") args')) =
      some (miStepRootK rules (MIVar v) r')
  rw [baseReducts_miStepRootK_active_mivar_raw rules r v hactive]
  have hv : IsNormal pMI (MIVar v) := normal_MIVar v
  simp only [IsNormal] at hrules hv
  simp only [oneStepList, hrules, hv, hstep, Option.map_some]
  rfl

theorem os_miStepRootK_active_step_misym (rules r r' : AST) (s : String)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r)
    (hstep : oneStep pMI r = some r') :
    oneStep pMI (miStepRootK rules (MISym s) r) =
      some (miStepRootK rules (MISym s) r') := by
  rw [oneStep.eq_def]
  change
    (match baseReducts pMI (miStepRootK rules (MISym s) r) with
    | q :: _ => some q
    | [] => (oneStepList pMI [rules, MISym s, r]).map
        (fun args' => AST.sexp (Label.id "mi-step-rootK") args')) =
      some (miStepRootK rules (MISym s) r')
  rw [baseReducts_miStepRootK_active_misym_raw rules r s hactive]
  have hs : IsNormal pMI (MISym s) := normal_MISym s
  simp only [IsNormal] at hrules hs
  simp only [oneStepList, hrules, hs, hstep, Option.map_some]
  rfl

theorem os_miStepRootK_active_step_miapp (rules args r r' : AST) (h : String)
    (hrules : IsNormal pMI rules) (hargs : IsNormal pMI args)
    (hactive : RootActiveShape r)
    (hstep : oneStep pMI r = some r') :
    oneStep pMI (miStepRootK rules (MIApp h args) r) =
      some (miStepRootK rules (MIApp h args) r') := by
  rw [oneStep.eq_def]
  change
    (match baseReducts pMI (miStepRootK rules (MIApp h args) r) with
    | q :: _ => some q
    | [] => (oneStepList pMI [rules, MIApp h args, r]).map
        (fun args' => AST.sexp (Label.id "mi-step-rootK") args')) =
      some (miStepRootK rules (MIApp h args) r')
  rw [baseReducts_miStepRootK_active_miapp_raw rules args r h hactive]
  have ht : IsNormal pMI (MIApp h args) := normal_MIApp h args hargs
  simp only [IsNormal] at hrules ht
  simp only [oneStepList, hrules, ht, hstep, Option.map_some]
  rfl

theorem os_miStepRootK_active_misubst_term_step
    (rules bs rhs next r : AST)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r)
    (hstep : oneStep pMI (miSubst bs rhs) = some next) :
    oneStep pMI (miStepRootK rules (miSubst bs rhs) r) =
      some (miStepRootK rules next r) := by
  rw [oneStep.eq_def]
  change
    (match baseReducts pMI (miStepRootK rules (miSubst bs rhs) r) with
    | q :: _ => some q
    | [] => (oneStepList pMI [rules, miSubst bs rhs, r]).map
        (fun args' => AST.sexp (Label.id "mi-step-rootK") args')) =
      some (miStepRootK rules next r)
  rw [baseReducts_miStepRootK_active_misubst_raw rules bs rhs r hactive]
  simp only [IsNormal] at hrules
  simp only [oneStepList, hrules, hstep, Option.map_some]
  rfl

theorem os_miStepRootK_active_misubstVarK_term_step
    (rules orig arg next r : AST)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r)
    (hstep : oneStep pMI (miSubstVarK orig arg) = some next) :
    oneStep pMI (miStepRootK rules (miSubstVarK orig arg) r) =
      some (miStepRootK rules next r) := by
  rw [oneStep.eq_def]
  change
    (match
      baseReducts pMI (miStepRootK rules (miSubstVarK orig arg) r)
    with
    | q :: _ => some q
    | [] => (oneStepList pMI [rules, miSubstVarK orig arg, r]).map
        (fun args' => AST.sexp (Label.id "mi-step-rootK") args')) =
      some (miStepRootK rules next r)
  rw [baseReducts_miStepRootK_active_misubstVarK_raw
    rules orig arg r hactive]
  simp only [IsNormal] at hrules
  simp only [oneStepList, hrules, hstep, Option.map_some]
  rfl

theorem miStepRootK_active_misubst_var_dispatch_eval
    (rules bs r : AST) (v : String)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r) :
    eval pMI 1 (miStepRootK rules (miSubst bs (MIVar v)) r) =
      miStepRootK rules (miSubstVarK (MIVar v) (miLookup (con0 v) bs)) r := by
  simp only [eval,
    os_miStepRootK_active_misubst_term_step rules bs (MIVar v)
      (miSubstVarK (MIVar v) (miLookup (con0 v) bs)) r hrules hactive
      (os_miSubst_var_named v bs)]

theorem miStepRootK_active_misubst_sym_dispatch_eval
    (rules bs r : AST) (s : String)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r) :
    eval pMI 1 (miStepRootK rules (miSubst bs (MISym s)) r) =
      miStepRootK rules (MISym s) r := by
  simp only [eval,
    os_miStepRootK_active_misubst_term_step rules bs (MISym s)
      (MISym s) r hrules hactive (os_miSubst_sym_named s bs)]

theorem miStepRootK_active_misubst_app_dispatch_eval
    (rules bs args r : AST) (h : String)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r) :
    eval pMI 1 (miStepRootK rules (miSubst bs (MIApp h args)) r) =
      miStepRootK rules (MIApp h (miSubstList bs args)) r := by
  simp only [eval,
    os_miStepRootK_active_misubst_term_step rules bs (MIApp h args)
      (MIApp h (miSubstList bs args)) r hrules hactive
      (os_miSubst_app_named h args bs)]

theorem os_miStepRootK_active_miapp_args_step
    (rules args args' r : AST) (h : String)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r)
    (hstep : oneStep pMI args = some args') :
    oneStep pMI (miStepRootK rules (MIApp h args) r) =
      some (miStepRootK rules (MIApp h args') r) := by
  rw [oneStep.eq_def]
  change
    (match baseReducts pMI (miStepRootK rules (MIApp h args) r) with
    | q :: _ => some q
    | [] => (oneStepList pMI [rules, MIApp h args, r]).map
        (fun args' => AST.sexp (Label.id "mi-step-rootK") args')) =
      some (miStepRootK rules (MIApp h args') r)
  rw [baseReducts_miStepRootK_active_miapp_raw rules args r h hactive]
  have htermStep : oneStep pMI (MIApp h args) = some (MIApp h args') :=
    os_MIApp_args_step h args args' hstep
  simp only [IsNormal] at hrules
  simp only [oneStepList, hrules, htermStep, Option.map_some]
  rfl

theorem miStepRootK_active_miapp_args_eval_of
    (rules args encodedArgs r : AST) (h : String) (fuel : Nat)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r)
    (hargs : eval pMI fuel args = encodedArgs)
    (hargsNorm : IsNormal pMI encodedArgs) :
    ∃ N, eval pMI N (miStepRootK rules (MIApp h args) r) =
      miStepRootK rules (MIApp h encodedArgs) r := by
  exact cong_eval_mi (fun z => miStepRootK rules (MIApp h z) r)
    (fun s s' hstep =>
      os_miStepRootK_active_miapp_args_step rules s s' r h
        hrules hactive hstep)
    fuel hargs hargsNorm

theorem miStepRootK_active_miapp_args_eval_of_with_guard
    (rules args encodedArgs r : AST) (h : String) (fuel : Nat)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r)
    (hargs : eval pMI fuel args = encodedArgs)
    (hargsNorm : IsNormal pMI encodedArgs) :
    ∃ N, eval pMI N (miStepRootK rules (MIApp h args) r) =
        miStepRootK rules (MIApp h encodedArgs) r ∧
      ∀ k, k < N →
        StepActiveShape
          (eval pMI k (miStepRootK rules (MIApp h args) r)) := by
  exact cong_eval_to_step_active_with_guard_mi
    (fun z => miStepRootK rules (MIApp h z) r)
    (fun z => StepActiveShape.rootK rules (MIApp h z) r)
    (fun s s' hstep =>
      os_miStepRootK_active_miapp_args_step rules s s' r h
        hrules hactive hstep)
    fuel hargs hargsNorm

theorem miStepRootK_active_misubst_app_args_eval_of
    (rules bs args encodedArgs r : AST) (h : String) (fuel : Nat)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r)
    (hargs : eval pMI fuel (miSubstList bs args) = encodedArgs)
    (hargsNorm : IsNormal pMI encodedArgs) :
    ∃ N, eval pMI N (miStepRootK rules (miSubst bs (MIApp h args)) r) =
      miStepRootK rules (MIApp h encodedArgs) r := by
  obtain ⟨M, hM⟩ :=
    miStepRootK_active_miapp_args_eval_of rules (miSubstList bs args)
      encodedArgs r h fuel hrules hactive hargs hargsNorm
  have hdispatch :=
    miStepRootK_active_misubst_app_dispatch_eval rules bs args r h
      hrules hactive
  refine ⟨1 + M, ?_⟩
  exact eval_trans_mi 1 M
    (miStepRootK rules (miSubst bs (MIApp h args)) r)
    (miStepRootK rules (MIApp h (miSubstList bs args)) r)
    (miStepRootK rules (MIApp h encodedArgs) r) hdispatch hM

theorem miStepRootK_active_misubst_app_args_eval_of_with_guard
    (rules bs args encodedArgs r : AST) (h : String) (fuel : Nat)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r)
    (hargs : eval pMI fuel (miSubstList bs args) = encodedArgs)
    (hargsNorm : IsNormal pMI encodedArgs) :
    ∃ N, eval pMI N (miStepRootK rules (miSubst bs (MIApp h args)) r) =
        miStepRootK rules (MIApp h encodedArgs) r ∧
      ∀ k, k < N →
        StepActiveShape
          (eval pMI k
            (miStepRootK rules (miSubst bs (MIApp h args)) r)) := by
  obtain ⟨M, hM, hMActive⟩ :=
    miStepRootK_active_miapp_args_eval_of_with_guard rules
      (miSubstList bs args) encodedArgs r h fuel hrules hactive
      hargs hargsNorm
  have hdispatch :=
    miStepRootK_active_misubst_app_dispatch_eval rules bs args r h
      hrules hactive
  refine ⟨1 + M, ?_, ?_⟩
  · exact eval_trans_mi 1 M
      (miStepRootK rules (miSubst bs (MIApp h args)) r)
      (miStepRootK rules (MIApp h (miSubstList bs args)) r)
      (miStepRootK rules (MIApp h encodedArgs) r) hdispatch hM
  · apply step_active_append_mi 1 M hdispatch
    · exact step_active_fuel_one_mi
        (StepActiveShape.rootK rules (miSubst bs (MIApp h args)) r)
    · exact hMActive

theorem miStepRootK_active_misubstVarK_some_eval
    (rules orig t r : AST)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r) :
    eval pMI 1 (miStepRootK rules (miSubstVarK orig (MISome t)) r) =
      miStepRootK rules t r := by
  simp only [eval,
    os_miStepRootK_active_misubstVarK_term_step rules orig (MISome t)
      t r hrules hactive (os_miSubstVarK_some orig t)]

theorem miStepRootK_active_misubstVarK_none_eval
    (rules orig r : AST)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r) :
    eval pMI 1 (miStepRootK rules (miSubstVarK orig MINone) r) =
      miStepRootK rules orig r := by
  simp only [eval,
    os_miStepRootK_active_misubstVarK_term_step rules orig MINone
      orig r hrules hactive (os_miSubstVarK_none orig)]

theorem miStepRootK_active_misubstVarK_lookup_nil_eval
    (rules orig r : AST) (v : String)
    (hrules : IsNormal pMI rules)
    (horig : IsNormal pMI orig)
    (hactive : RootActiveShape r) :
    eval pMI 2
        (miStepRootK rules
          (miSubstVarK orig (miLookup (con0 v) MIBNil)) r) =
      miStepRootK rules orig r := by
  have hfirst :
      eval pMI 1
          (miStepRootK rules
            (miSubstVarK orig (miLookup (con0 v) MIBNil)) r) =
        miStepRootK rules (miSubstVarK orig MINone) r := by
    simp only [eval,
      os_miStepRootK_active_misubstVarK_term_step rules orig
        (miLookup (con0 v) MIBNil) (miSubstVarK orig MINone) r
        hrules hactive (os_miSubstVarK_lookup_nil_arg orig v horig)]
  have hsecond :=
    miStepRootK_active_misubstVarK_none_eval rules orig r hrules hactive
  exact eval_trans_mi 1 1
    (miStepRootK rules (miSubstVarK orig (miLookup (con0 v) MIBNil)) r)
    (miStepRootK rules (miSubstVarK orig MINone) r)
    (miStepRootK rules orig r) hfirst hsecond

theorem miStepRootK_active_misubstVarK_lookup_hit_eval
    (rules orig old rest r : AST) (v : String)
    (hrules : IsNormal pMI rules)
    (horig : IsNormal pMI orig)
    (hactive : RootActiveShape r) :
    eval pMI 2
        (miStepRootK rules
          (miSubstVarK orig
            (miLookup (con0 v) (MIBCons (con0 v) old rest))) r) =
      miStepRootK rules old r := by
  have hfirst :
      eval pMI 1
          (miStepRootK rules
            (miSubstVarK orig
              (miLookup (con0 v) (MIBCons (con0 v) old rest))) r) =
        miStepRootK rules (miSubstVarK orig (MISome old)) r := by
    simp only [eval,
      os_miStepRootK_active_misubstVarK_term_step rules orig
        (miLookup (con0 v) (MIBCons (con0 v) old rest))
        (miSubstVarK orig (MISome old)) r hrules hactive
        (os_miSubstVarK_lookup_hit_arg orig v old rest horig)]
  have hsecond :=
    miStepRootK_active_misubstVarK_some_eval rules orig old r
      hrules hactive
  exact eval_trans_mi 1 1
    (miStepRootK rules
      (miSubstVarK orig
        (miLookup (con0 v) (MIBCons (con0 v) old rest))) r)
    (miStepRootK rules (miSubstVarK orig (MISome old)) r)
    (miStepRootK rules old r) hfirst hsecond

theorem miStepRootK_active_misubstVarK_lookup_miss_eval
    (rules orig old rest r : AST) (v w : String)
    (hrules : IsNormal pMI rules)
    (horig : IsNormal pMI orig)
    (hactive : RootActiveShape r)
    (hvw : (v == w) = false) :
    eval pMI 1
        (miStepRootK rules
          (miSubstVarK orig
            (miLookup (con0 v) (MIBCons (con0 w) old rest))) r) =
      miStepRootK rules (miSubstVarK orig (miLookup (con0 v) rest)) r := by
  simp only [eval,
    os_miStepRootK_active_misubstVarK_term_step rules orig
      (miLookup (con0 v) (MIBCons (con0 w) old rest))
      (miSubstVarK orig (miLookup (con0 v) rest)) r hrules hactive
      (os_miSubstVarK_lookup_miss_arg orig v w old rest hvw horig)]

theorem miStepRootK_active_misubstVarK_lookup_encBinds_eval
    (rules orig r : AST) (v : String)
    (hrules : IsNormal pMI rules)
    (horig : IsNormal pMI orig)
    (hactive : RootActiveShape r) :
    ∀ (bs : List (String × AST)) (encodedBs : AST),
      encBinds? bs = some encodedBs →
      ∃ N,
        eval pMI N
            (miStepRootK rules
              (miSubstVarK orig (miLookup (con0 v) encodedBs)) r) =
          match lookupEncoded? v bs with
          | some encodedTerm => miStepRootK rules encodedTerm r
          | none => miStepRootK rules orig r
  | [], encodedBs, henc => by
      simp only [encBinds?] at henc
      cases henc
      refine ⟨2, ?_⟩
      simp only [lookupEncoded?]
      exact miStepRootK_active_misubstVarK_lookup_nil_eval rules orig r v
        hrules horig hactive
  | (w, t) :: rest, encodedBs, henc => by
      simp only [encBinds?] at henc
      cases ht : encAST? t with
      | none =>
          simp [ht] at henc
      | some encodedTerm =>
          cases hrest : encBinds? rest with
          | none =>
              simp [ht, hrest] at henc
          | some encodedRest =>
              simp [ht, hrest] at henc
              cases henc
              by_cases hvw : (v == w) = true
              · have hvw_eq : v = w := beq_iff_eq.mp hvw
                subst w
                have hvv : (v == v) = true := beq_iff_eq.mpr rfl
                refine ⟨2, ?_⟩
                simp only [lookupEncoded?, hvv, ht]
                exact miStepRootK_active_misubstVarK_lookup_hit_eval
                  rules orig encodedTerm encodedRest r v hrules horig hactive
              · have hvw_false : (v == w) = false := by
                  cases hcmp : (v == w) <;> simp [hcmp] at hvw ⊢
                obtain ⟨M, hM⟩ :=
                  miStepRootK_active_misubstVarK_lookup_encBinds_eval
                    rules orig r v hrules horig hactive rest encodedRest hrest
                have hfirst :
                    eval pMI 1
                        (miStepRootK rules
                          (miSubstVarK orig
                            (miLookup (con0 v)
                              (MIBCons (con0 w) encodedTerm encodedRest))) r) =
                      miStepRootK rules
                        (miSubstVarK orig (miLookup (con0 v) encodedRest)) r :=
                  miStepRootK_active_misubstVarK_lookup_miss_eval
                    rules orig encodedTerm encodedRest r v w hrules horig hactive
                    hvw_false
                refine ⟨1 + M, ?_⟩
                have htotal := eval_trans_mi 1 M
                  (miStepRootK rules
                    (miSubstVarK orig
                      (miLookup (con0 v)
                        (MIBCons (con0 w) encodedTerm encodedRest))) r)
                  (miStepRootK rules
                    (miSubstVarK orig (miLookup (con0 v) encodedRest)) r)
                  (match lookupEncoded? v rest with
                    | some encodedTerm => miStepRootK rules encodedTerm r
                    | none => miStepRootK rules orig r)
                  hfirst hM
                simpa [lookupEncoded?, hvw_false, ht] using htotal

theorem miStepRootK_active_misubstVarK_lookup_encBinds_eval_with_guard
    (rules orig r : AST) (v : String)
    (hrules : IsNormal pMI rules)
    (horig : IsNormal pMI orig)
    (hactive : RootActiveShape r) :
    ∀ (bs : List (String × AST)) (encodedBs : AST),
      encBinds? bs = some encodedBs →
      ∃ N,
        eval pMI N
            (miStepRootK rules
              (miSubstVarK orig (miLookup (con0 v) encodedBs)) r) =
          (match lookupEncoded? v bs with
          | some encodedTerm => miStepRootK rules encodedTerm r
          | none => miStepRootK rules orig r) ∧
        ∀ k, k < N →
          StepActiveShape
            (eval pMI k
              (miStepRootK rules
                (miSubstVarK orig (miLookup (con0 v) encodedBs)) r))
  | [], encodedBs, henc => by
      simp only [encBinds?] at henc
      cases henc
      have hfirst :
          eval pMI 1
              (miStepRootK rules
                (miSubstVarK orig (miLookup (con0 v) MIBNil)) r) =
            miStepRootK rules (miSubstVarK orig MINone) r := by
        simp only [eval,
          os_miStepRootK_active_misubstVarK_term_step rules orig
            (miLookup (con0 v) MIBNil) (miSubstVarK orig MINone) r
            hrules hactive (os_miSubstVarK_lookup_nil_arg orig v horig)]
      have hsecond :=
        miStepRootK_active_misubstVarK_none_eval rules orig r
          hrules hactive
      refine ⟨2, ?_, ?_⟩
      · simpa only [lookupEncoded?] using eval_trans_mi 1 1
          (miStepRootK rules
            (miSubstVarK orig (miLookup (con0 v) MIBNil)) r)
          (miStepRootK rules (miSubstVarK orig MINone) r)
          (miStepRootK rules orig r) hfirst hsecond
      · apply step_active_append_mi 1 1 hfirst
        · exact step_active_fuel_one_mi
            (StepActiveShape.rootK rules
              (miSubstVarK orig (miLookup (con0 v) MIBNil)) r)
        · exact step_active_fuel_one_mi
            (StepActiveShape.rootK rules (miSubstVarK orig MINone) r)
  | (w, t) :: rest, encodedBs, henc => by
      simp only [encBinds?] at henc
      cases ht : encAST? t with
      | none =>
          simp [ht] at henc
      | some encodedTerm =>
          cases hrest : encBinds? rest with
          | none =>
              simp [ht, hrest] at henc
          | some encodedRest =>
              simp [ht, hrest] at henc
              cases henc
              by_cases hvw : (v == w) = true
              · have hvw_eq : v = w := beq_iff_eq.mp hvw
                subst w
                have hvv : (v == v) = true := beq_iff_eq.mpr rfl
                have hfirst :
                    eval pMI 1
                        (miStepRootK rules
                          (miSubstVarK orig
                            (miLookup (con0 v)
                              (MIBCons (con0 v) encodedTerm encodedRest)))
                          r) =
                      miStepRootK rules
                        (miSubstVarK orig (MISome encodedTerm)) r := by
                  simp only [eval,
                    os_miStepRootK_active_misubstVarK_term_step rules orig
                      (miLookup (con0 v)
                        (MIBCons (con0 v) encodedTerm encodedRest))
                      (miSubstVarK orig (MISome encodedTerm)) r
                      hrules hactive
                      (os_miSubstVarK_lookup_hit_arg orig v encodedTerm
                        encodedRest horig)]
                have hsecond :=
                  miStepRootK_active_misubstVarK_some_eval rules orig
                    encodedTerm r hrules hactive
                refine ⟨2, ?_, ?_⟩
                · simp only [lookupEncoded?, hvv, ht]
                  exact eval_trans_mi 1 1
                    (miStepRootK rules
                      (miSubstVarK orig
                        (miLookup (con0 v)
                          (MIBCons (con0 v) encodedTerm encodedRest))) r)
                    (miStepRootK rules
                      (miSubstVarK orig (MISome encodedTerm)) r)
                    (miStepRootK rules encodedTerm r) hfirst hsecond
                · apply step_active_append_mi 1 1 hfirst
                  · exact step_active_fuel_one_mi
                      (StepActiveShape.rootK rules
                        (miSubstVarK orig
                          (miLookup (con0 v)
                            (MIBCons (con0 v) encodedTerm encodedRest))) r)
                  · exact step_active_fuel_one_mi
                      (StepActiveShape.rootK rules
                        (miSubstVarK orig (MISome encodedTerm)) r)
              · have hvw_false : (v == w) = false := by
                  cases hcmp : (v == w) <;> simp [hcmp] at hvw ⊢
                obtain ⟨M, hM, hMActive⟩ :=
                  miStepRootK_active_misubstVarK_lookup_encBinds_eval_with_guard
                    rules orig r v hrules horig hactive rest encodedRest hrest
                have hfirst :
                    eval pMI 1
                        (miStepRootK rules
                          (miSubstVarK orig
                            (miLookup (con0 v)
                              (MIBCons (con0 w) encodedTerm encodedRest)))
                          r) =
                      miStepRootK rules
                        (miSubstVarK orig (miLookup (con0 v) encodedRest))
                        r :=
                  miStepRootK_active_misubstVarK_lookup_miss_eval
                    rules orig encodedTerm encodedRest r v w hrules horig
                    hactive hvw_false
                refine ⟨1 + M, ?_, ?_⟩
                · have htotal := eval_trans_mi 1 M
                    (miStepRootK rules
                      (miSubstVarK orig
                        (miLookup (con0 v)
                          (MIBCons (con0 w) encodedTerm encodedRest))) r)
                    (miStepRootK rules
                      (miSubstVarK orig (miLookup (con0 v) encodedRest)) r)
                    (match lookupEncoded? v rest with
                      | some encodedTerm => miStepRootK rules encodedTerm r
                      | none => miStepRootK rules orig r)
                    hfirst hM
                  simpa [lookupEncoded?, hvw_false, ht] using htotal
                · apply step_active_append_mi 1 M hfirst
                  · exact step_active_fuel_one_mi
                      (StepActiveShape.rootK rules
                        (miSubstVarK orig
                          (miLookup (con0 v)
                            (MIBCons (con0 w) encodedTerm encodedRest))) r)
                  · exact hMActive

theorem miStepRootK_active_misubst_var_encBinds_eval
    (rules encodedBs r : AST) (v : String)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r) :
    ∀ (bs : List (String × AST)),
      encBinds? bs = some encodedBs →
      ∃ N,
        eval pMI N (miStepRootK rules (miSubst encodedBs (MIVar v)) r) =
          match lookupEncoded? v bs with
          | some encodedTerm => miStepRootK rules encodedTerm r
          | none => miStepRootK rules (MIVar v) r := by
  intro bs hbs
  obtain ⟨M, hM⟩ :=
    miStepRootK_active_misubstVarK_lookup_encBinds_eval rules (MIVar v) r v
      hrules (normal_MIVar v) hactive bs encodedBs hbs
  have hdispatch :=
    miStepRootK_active_misubst_var_dispatch_eval rules encodedBs r v
      hrules hactive
  refine ⟨1 + M, ?_⟩
  exact eval_trans_mi 1 M
    (miStepRootK rules (miSubst encodedBs (MIVar v)) r)
    (miStepRootK rules
      (miSubstVarK (MIVar v) (miLookup (con0 v) encodedBs)) r)
    (match lookupEncoded? v bs with
      | some encodedTerm => miStepRootK rules encodedTerm r
      | none => miStepRootK rules (MIVar v) r)
    hdispatch hM

theorem miStepRootK_active_misubst_var_encBinds_eval_with_guard
    (rules encodedBs r : AST) (v : String)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r) :
    ∀ (bs : List (String × AST)),
      encBinds? bs = some encodedBs →
      ∃ N,
        eval pMI N (miStepRootK rules (miSubst encodedBs (MIVar v)) r) =
          (match lookupEncoded? v bs with
          | some encodedTerm => miStepRootK rules encodedTerm r
          | none => miStepRootK rules (MIVar v) r) ∧
        ∀ k, k < N →
          StepActiveShape
            (eval pMI k
              (miStepRootK rules (miSubst encodedBs (MIVar v)) r)) := by
  intro bs hbs
  obtain ⟨M, hM, hMActive⟩ :=
    miStepRootK_active_misubstVarK_lookup_encBinds_eval_with_guard
      rules (MIVar v) r v hrules (normal_MIVar v) hactive bs encodedBs hbs
  have hdispatch :=
    miStepRootK_active_misubst_var_dispatch_eval rules encodedBs r v
      hrules hactive
  refine ⟨1 + M, ?_, ?_⟩
  · exact eval_trans_mi 1 M
      (miStepRootK rules (miSubst encodedBs (MIVar v)) r)
      (miStepRootK rules
        (miSubstVarK (MIVar v) (miLookup (con0 v) encodedBs)) r)
      (match lookupEncoded? v bs with
      | some encodedTerm => miStepRootK rules encodedTerm r
      | none => miStepRootK rules (MIVar v) r)
      hdispatch hM
  · apply step_active_append_mi 1 M hdispatch
    · exact step_active_fuel_one_mi
        (StepActiveShape.rootK rules (miSubst encodedBs (MIVar v)) r)
    · exact hMActive

theorem miStepRootK_active_misubst_encAST_inst_eval
    (rules r : AST)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r) :
    ∀ (term encodedTerm : AST),
      encAST? term = some encodedTerm →
      ∀ (bs : List (String × AST)) (encodedBs : AST),
        encBinds? bs = some encodedBs →
        ∃ (encodedOut : AST) (N : Nat),
          encAST? (AST.inst bs term) = some encodedOut ∧
          eval pMI N (miStepRootK rules (miSubst encodedBs encodedTerm) r) =
            miStepRootK rules encodedOut r ∧
          IsNormal pMI encodedOut
  | .var (.base v), encodedTerm, henc => by
      cases henc
      intro bs encodedBs hbs
      let out : AST :=
        match lookupEncoded? v bs with
        | some encodedTerm => encodedTerm
        | none => MIVar v
      have hout0 := encAST?_inst_var_lookupEncoded v bs encodedBs hbs
      have hout : encAST? (AST.inst bs (.var (.base v))) = some out := by
        cases hlookup : lookupEncoded? v bs <;>
          simp [out, hlookup] at hout0 ⊢
        · exact hout0
        · exact hout0
      obtain ⟨N, hN⟩ :=
        miStepRootK_active_misubst_var_encBinds_eval rules encodedBs r v
          hrules hactive bs hbs
      refine ⟨out, N, hout, ?_, ?_⟩
      · cases hlookup : lookupEncoded? v bs <;> simp [out, hlookup] at hN ⊢
        · exact hN
        · exact hN
      · exact encAST?_some_normal (AST.inst bs (.var (.base v))) out hout
  | .var (.qualified _ _), _, henc => by
      cases henc
  | .sexp (.id s) [], encodedTerm, henc => by
      cases henc
      intro bs encodedBs _hbs
      refine ⟨MISym s, 1, ?_, ?_, normal_MISym s⟩
      · rfl
      · exact miStepRootK_active_misubst_sym_dispatch_eval rules
          encodedBs r s hrules hactive
  | .sexp (.id s) (a :: args), encodedTerm, henc => by
      simp only [encAST?] at henc
      cases hargs : encASTList? (a :: args) with
      | none =>
          simp [hargs] at henc
      | some encodedArgs =>
          simp [hargs] at henc
          cases henc
          intro bs encodedBs hbs
          obtain ⟨argsOut, argFuel, hargsOut, hargsEval, hargsNorm⟩ :=
            miSubstList_encASTList_inst_eval (a :: args) encodedArgs hargs
              bs encodedBs hbs
          obtain ⟨N, hN⟩ :=
            miStepRootK_active_misubst_app_args_eval_of rules encodedBs
              encodedArgs argsOut r s argFuel hrules hactive hargsEval
              hargsNorm
          refine ⟨MIApp s argsOut, N, ?_, hN, ?_⟩
          · have hargsOut' :
                encASTList? (AST.inst bs a :: AST.instList bs args) =
                  some argsOut := by
              simpa only [AST.instList] using hargsOut
            simp only [AST.inst, AST.instList, encAST?, hargsOut']
          · exact normal_MIApp s argsOut hargsNorm
  | .sexp .wild _, _, henc => by
      cases henc
  | .sexp (.listE _) _, _, henc => by
      cases henc
  | .sexp (.listCons _) _, _, henc => by
      cases henc
  | .sexp (.listOne _) _, _, henc => by
      cases henc
  | .subst _ _ _, _, henc => by
      cases henc

theorem miStepRootK_active_misubst_encAST_inst_eval_with_guard
    (rules r : AST)
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r) :
    ∀ (term encodedTerm : AST),
      encAST? term = some encodedTerm →
      ∀ (bs : List (String × AST)) (encodedBs : AST),
        encBinds? bs = some encodedBs →
        ∃ (encodedOut : AST) (N : Nat),
          encAST? (AST.inst bs term) = some encodedOut ∧
          eval pMI N
              (miStepRootK rules (miSubst encodedBs encodedTerm) r) =
            miStepRootK rules encodedOut r ∧
          (∀ k, k < N →
            StepActiveShape
              (eval pMI k
                (miStepRootK rules (miSubst encodedBs encodedTerm) r))) ∧
          IsNormal pMI encodedOut
  | .var (.base v), encodedTerm, henc => by
      cases henc
      intro bs encodedBs hbs
      let out : AST :=
        match lookupEncoded? v bs with
        | some encodedTerm => encodedTerm
        | none => MIVar v
      have hout0 := encAST?_inst_var_lookupEncoded v bs encodedBs hbs
      have hout : encAST? (AST.inst bs (.var (.base v))) = some out := by
        cases hlookup : lookupEncoded? v bs <;>
          simp [out, hlookup] at hout0 ⊢
        · exact hout0
        · exact hout0
      obtain ⟨N, hN, hNActive⟩ :=
        miStepRootK_active_misubst_var_encBinds_eval_with_guard
          rules encodedBs r v hrules hactive bs hbs
      refine ⟨out, N, hout, ?_, ?_, ?_⟩
      · cases hlookup : lookupEncoded? v bs <;>
          simp [out, hlookup] at hN ⊢
        · exact hN
        · exact hN
      · simpa [out] using hNActive
      · exact encAST?_some_normal (AST.inst bs (.var (.base v))) out hout
  | .var (.qualified _ _), _, henc => by
      cases henc
  | .sexp (.id s) [], encodedTerm, henc => by
      cases henc
      intro bs encodedBs _hbs
      refine ⟨MISym s, 1, ?_, ?_, ?_, normal_MISym s⟩
      · rfl
      · exact miStepRootK_active_misubst_sym_dispatch_eval rules
          encodedBs r s hrules hactive
      · exact step_active_fuel_one_mi
          (StepActiveShape.rootK rules (miSubst encodedBs (MISym s)) r)
  | .sexp (.id s) (a :: args), encodedTerm, henc => by
      simp only [encAST?] at henc
      cases hargs : encASTList? (a :: args) with
      | none =>
          simp [hargs] at henc
      | some encodedArgs =>
          simp [hargs] at henc
          cases henc
          intro bs encodedBs hbs
          obtain ⟨argsOut, argFuel, hargsOut, hargsEval, hargsNorm⟩ :=
            miSubstList_encASTList_inst_eval (a :: args) encodedArgs hargs
              bs encodedBs hbs
          obtain ⟨N, hN, hNActive⟩ :=
            miStepRootK_active_misubst_app_args_eval_of_with_guard rules
              encodedBs encodedArgs argsOut r s argFuel hrules hactive
              hargsEval hargsNorm
          refine ⟨MIApp s argsOut, N, ?_, hN, hNActive, ?_⟩
          · have hargsOut' :
                encASTList? (AST.inst bs a :: AST.instList bs args) =
                  some argsOut := by
              simpa only [AST.instList] using hargsOut
            simp only [AST.inst, AST.instList, encAST?, hargsOut']
          · exact normal_MIApp s argsOut hargsNorm
  | .sexp .wild _, _, henc => by
      cases henc
  | .sexp (.listE _) _, _, henc => by
      cases henc
  | .sexp (.listCons _) _, _, henc => by
      cases henc
  | .sexp (.listOne _) _, _, henc => by
      cases henc
  | .subst _ _ _, _, henc => by
      cases henc

theorem miStepRootK_active_misubst_substInst_eval
    (rules r template encodedTemplate encodedBs encodedOut : AST)
    (bs : List (String × AST))
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r)
    (htemplate : encAST? template = some encodedTemplate)
    (hbs : encBinds? bs = some encodedBs)
    (hinst : encAST? (AST.inst bs template) = some encodedOut) :
    ∃ N,
      eval pMI N
          (miStepRootK rules (miSubst encodedBs encodedTemplate) r) =
        miStepRootK rules encodedOut r := by
  obtain ⟨encodedOut', N, hinst', hctx, _houtNorm⟩ :=
    miStepRootK_active_misubst_encAST_inst_eval rules r hrules hactive
      template encodedTemplate htemplate bs encodedBs hbs
  rw [hinst] at hinst'
  cases hinst'
  exact ⟨N, hctx⟩

theorem miStepRootK_active_misubst_substInst_eval_with_guard
    (rules r template encodedTemplate encodedBs encodedOut : AST)
    (bs : List (String × AST))
    (hrules : IsNormal pMI rules)
    (hactive : RootActiveShape r)
    (htemplate : encAST? template = some encodedTemplate)
    (hbs : encBinds? bs = some encodedBs)
    (hinst : encAST? (AST.inst bs template) = some encodedOut) :
    ∃ N,
      eval pMI N
          (miStepRootK rules (miSubst encodedBs encodedTemplate) r) =
        miStepRootK rules encodedOut r ∧
      ∀ k, k < N →
        StepActiveShape
          (eval pMI k
            (miStepRootK rules (miSubst encodedBs encodedTemplate) r)) := by
  obtain ⟨encodedOut', N, hinst', hctx, hactiveCtx, _houtNorm⟩ :=
    miStepRootK_active_misubst_encAST_inst_eval_with_guard rules r
      hrules hactive template encodedTemplate htemplate bs encodedBs hbs
  rw [hinst] at hinst'
  cases hinst'
  exact ⟨N, hctx, hactiveCtx⟩

theorem cong_eval_root_active_mi (F : AST → AST)
    (hcong : ∀ s s', RootActiveShape s →
      oneStep pMI s = some s' → oneStep pMI (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pMI N s = v → IsNormal pMI v →
      (∀ k, k < N → RootActiveShape (eval pMI k s)) →
      ∃ M, eval pMI M (F s) = F v := by
  intro N
  induction N with
  | zero =>
      intro s v hs _ _
      simp only [eval] at hs
      subst hs
      exact ⟨0, rfl⟩
  | succ n ih =>
      intro s v hs hv hactive
      simp only [eval] at hs
      cases hstep : oneStep pMI s with
      | none =>
          rw [hstep] at hs
          subst hs
          exact ⟨0, rfl⟩
      | some s' =>
          rw [hstep] at hs
          have hsActive : RootActiveShape s := by
            have h0 := hactive 0 (Nat.zero_lt_succ n)
            simpa only [eval] using h0
          have hactive' : ∀ k, k < n →
              RootActiveShape (eval pMI k s') := by
            intro k hk
            have hk' : Nat.succ k < Nat.succ n := Nat.succ_lt_succ hk
            have hnext := hactive (Nat.succ k) hk'
            have heval : eval pMI (Nat.succ k) s = eval pMI k s' := by
              simp only [eval, hstep]
            simpa only [heval] using hnext
          obtain ⟨M, hM⟩ := ih hs hv hactive'
          refine ⟨M + 1, ?_⟩
          simp only [eval, hcong s s' hsActive hstep]
          exact hM

theorem cong_eval_root_active_fuel_mi (F : AST → AST)
    (hcong : ∀ s s', RootActiveShape s →
      oneStep pMI s = some s' → oneStep pMI (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pMI N s = v →
      (∀ k, k < N → RootActiveShape (eval pMI k s)) →
      ∃ M, eval pMI M (F s) = F v := by
  intro N
  induction N with
  | zero =>
      intro s v hs _
      simp only [eval] at hs
      subst hs
      exact ⟨0, rfl⟩
  | succ n ih =>
      intro s v hs hactive
      simp only [eval] at hs
      cases hstep : oneStep pMI s with
      | none =>
          rw [hstep] at hs
          subst hs
          exact ⟨0, rfl⟩
      | some s' =>
          rw [hstep] at hs
          have hsActive : RootActiveShape s := by
            have h0 := hactive 0 (Nat.zero_lt_succ n)
            simpa only [eval] using h0
          have hactive' : ∀ k, k < n →
              RootActiveShape (eval pMI k s') := by
            intro k hk
            have hk' : Nat.succ k < Nat.succ n := Nat.succ_lt_succ hk
            have hnext := hactive (Nat.succ k) hk'
            have heval : eval pMI (Nat.succ k) s = eval pMI k s' := by
              simp only [eval, hstep]
            simpa only [heval] using hnext
          obtain ⟨M, hM⟩ := ih hs hactive'
          refine ⟨M + 1, ?_⟩
          simp only [eval, hcong s s' hsActive hstep]
          exact hM

theorem cong_eval_root_to_step_active_with_guard_mi (F : AST → AST)
    (hwrap : ∀ s, RootActiveShape s → StepActiveShape (F s))
    (hcong : ∀ s s', RootActiveShape s →
      oneStep pMI s = some s' → oneStep pMI (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pMI N s = v →
      (∀ k, k < N → RootActiveShape (eval pMI k s)) →
        ∃ M, eval pMI M (F s) = F v ∧
          ∀ k, k < M → StepActiveShape (eval pMI k (F s)) := by
  intro N
  induction N with
  | zero =>
      intro s v hs _
      simp only [eval] at hs
      subst hs
      exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
  | succ n ih =>
      intro s v hs hactive
      simp only [eval] at hs
      cases hstep : oneStep pMI s with
      | none =>
          rw [hstep] at hs
          subst hs
          exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
      | some s' =>
          rw [hstep] at hs
          have hsActive : RootActiveShape s := by
            have h0 := hactive 0 (Nat.zero_lt_succ n)
            simpa only [eval] using h0
          have hactive' : ∀ k, k < n →
              RootActiveShape (eval pMI k s') := by
            intro k hk
            have hk' : Nat.succ k < Nat.succ n := Nat.succ_lt_succ hk
            have hnext := hactive (Nat.succ k) hk'
            have heval : eval pMI (Nat.succ k) s = eval pMI k s' := by
              simp only [eval, hstep]
            simpa only [heval] using hnext
          obtain ⟨M, hM, hMactive⟩ := ih hs hactive'
          refine ⟨M + 1, ?_, ?_⟩
          · simp only [eval, hcong s s' hsActive hstep]
            exact hM
          · intro k hk
            cases k with
            | zero =>
                simpa only [eval] using hwrap s hsActive
            | succ k =>
                have hkM : k < M := by
                  exact Nat.succ_lt_succ_iff.mp (by
                    simpa [Nat.succ_eq_add_one] using hk)
                have htotal :
                    eval pMI (Nat.succ k) (F s) = eval pMI k (F s') := by
                  simp only [eval, hcong s s' hsActive hstep]
                rw [htotal]
                exact hMactive k hkM

theorem cong_eval_match_to_root_active_with_guard_mi (F : AST → AST)
    (hwrap : ∀ s, MatchActiveShape s → RootActiveShape (F s))
    (hcong : ∀ s s', MatchActiveShape s →
      oneStep pMI s = some s' → oneStep pMI (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pMI N s = v →
      (∀ k, k < N → MatchActiveShape (eval pMI k s)) →
        ∃ M, eval pMI M (F s) = F v ∧
          ∀ k, k < M → RootActiveShape (eval pMI k (F s)) := by
  intro N
  induction N with
  | zero =>
      intro s v hs _
      simp only [eval] at hs
      subst hs
      exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
  | succ n ih =>
      intro s v hs hactive
      simp only [eval] at hs
      cases hstep : oneStep pMI s with
      | none =>
          rw [hstep] at hs
          subst hs
          exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
      | some s' =>
          rw [hstep] at hs
          have hsActive : MatchActiveShape s := by
            have h0 := hactive 0 (Nat.zero_lt_succ n)
            simpa only [eval] using h0
          have hactive' : ∀ k, k < n →
              MatchActiveShape (eval pMI k s') := by
            intro k hk
            have hk' : Nat.succ k < Nat.succ n := Nat.succ_lt_succ hk
            have hnext := hactive (Nat.succ k) hk'
            have heval : eval pMI (Nat.succ k) s = eval pMI k s' := by
              simp only [eval, hstep]
            simpa only [heval] using hnext
          obtain ⟨M, hM, hMactive⟩ := ih hs hactive'
          refine ⟨M + 1, ?_, ?_⟩
          · simp only [eval, hcong s s' hsActive hstep]
            exact hM
          · intro k hk
            cases k with
            | zero =>
                simpa only [eval] using hwrap s hsActive
            | succ k =>
                have hkM : k < M := by
                  exact Nat.succ_lt_succ_iff.mp (by
                    simpa [Nat.succ_eq_add_one] using hk)
                have htotal :
                    eval pMI (Nat.succ k) (F s) = eval pMI k (F s') := by
                  simp only [eval, hcong s s' hsActive hstep]
                rw [htotal]
                exact hMactive k hkM

theorem os_miRootK_active_term_step (rest term term' rhs r : AST)
    (hrest : IsNormal pMI rest) (hactive : MatchActiveShape r)
    (hstep : oneStep pMI term = some term') :
    oneStep pMI (miRootK rest term rhs r) =
      some (miRootK rest term' rhs r) := by
  rw [oneStep.eq_def]
  change
    (match baseReducts pMI (miRootK rest term rhs r) with
    | q :: _ => some q
    | [] => (oneStepList pMI [rest, term, rhs, r]).map
        (fun args' => AST.sexp (Label.id "mi-rootK") args')) =
      some (miRootK rest term' rhs r)
  rw [baseReducts_miRootK_active_raw rest term rhs r hactive]
  simp only [IsNormal] at hrest
  simp only [oneStepList, hrest, hstep, Option.map_some]
  rfl

theorem cong_eval_to_root_active_with_guard_mi (F : AST → AST)
    (hwrap : ∀ s, RootActiveShape (F s))
    (hcong : ∀ s s', oneStep pMI s = some s' →
      oneStep pMI (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pMI N s = v → IsNormal pMI v →
      ∃ M, eval pMI M (F s) = F v ∧
        ∀ k, k < M → RootActiveShape (eval pMI k (F s)) := by
  intro N
  induction N with
  | zero =>
      intro s v hs _
      simp only [eval] at hs
      subst hs
      exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
  | succ n ih =>
      intro s v hs hv
      simp only [eval] at hs
      cases hstep : oneStep pMI s with
      | none =>
          rw [hstep] at hs
          subst hs
          exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
      | some s' =>
          rw [hstep] at hs
          obtain ⟨M, hM, hMactive⟩ := ih hs hv
          refine ⟨M + 1, ?_, ?_⟩
          · simp only [eval, hcong s s' hstep]
            exact hM
          · intro k hk
            cases k with
            | zero =>
                simpa only [eval] using hwrap s
            | succ k =>
                have hkM : k < M := by
                  exact Nat.succ_lt_succ_iff.mp (by
                    simpa [Nat.succ_eq_add_one] using hk)
                have htotal :
                    eval pMI (Nat.succ k) (F s) = eval pMI k (F s') := by
                  simp only [eval, hcong s s' hstep]
                rw [htotal]
                exact hMactive k hkM

theorem miRootK_active_term_eval_of (rest term termOut rhs r : AST)
    (fuel : Nat)
    (hrest : IsNormal pMI rest)
    (hactive : MatchActiveShape r)
    (hterm : eval pMI fuel term = termOut)
    (hout : IsNormal pMI termOut) :
    ∃ N,
      eval pMI N (miRootK rest term rhs r) = miRootK rest termOut rhs r ∧
      ∀ k, k < N →
        RootActiveShape (eval pMI k (miRootK rest term rhs r)) := by
  exact cong_eval_to_root_active_with_guard_mi
    (fun z => miRootK rest z rhs r)
    (fun z => RootActiveShape.rootK rest z rhs r)
    (fun s s' hstep =>
      os_miRootK_active_term_step rest s s' rhs r hrest hactive hstep)
    fuel hterm hout

theorem miRootK_eval_of_match_fail_active_any (rest term rhs r : AST)
    (matchFuel : Nat)
    (hrest : IsNormal pMI rest) (hterm : IsNormal pMI term)
    (hrhs : IsNormal pMI rhs)
    (hmatch : eval pMI matchFuel r = MIMatchFail)
    (hactive : ∀ k, k < matchFuel →
      MatchActiveShape (eval pMI k r)) :
    ∃ N,
      eval pMI N (miRootK rest term rhs r) = miRootTable rest term ∧
      ∀ k, k < N →
        RootActiveShape (eval pMI k (miRootK rest term rhs r)) := by
  let F : AST → AST := fun z => miRootK rest term rhs z
  obtain ⟨Mmatch, hmatchCtx, hmatchCtxActive⟩ :=
    cong_eval_match_to_root_active_with_guard_mi F
      (fun s _hs => RootActiveShape.rootK rest term rhs s)
      (fun s s' hactiveStep hstep =>
        os_miRootK_active_step rest term rhs s s'
          hrest hterm hrhs hactiveStep hstep)
      matchFuel hmatch hactive
  have hfail : eval pMI 1 (F MIMatchFail) = miRootTable rest term := by
    simp only [F, eval, os_miRootK_fail]
  have htotal := eval_trans_mi Mmatch 1
    (miRootK rest term rhs r)
    (F MIMatchFail)
    (miRootTable rest term)
    hmatchCtx hfail
  refine ⟨Mmatch + 1, htotal, ?_⟩
  intro k hk
  by_cases hlt : k < Mmatch
  · exact hmatchCtxActive k hlt
  · have hk_ge : Mmatch ≤ k := Nat.le_of_not_gt hlt
    have hk_le : k ≤ Mmatch := Nat.le_of_lt_succ hk
    have hk_eq : k = Mmatch := Nat.le_antisymm hk_le hk_ge
    subst k
    change RootActiveShape (eval pMI Mmatch (F r))
    rw [hmatchCtx]
    exact RootActiveShape.rootK rest term rhs MIMatchFail

theorem miRootK_eval_of_match_ok_raw_active (rest term lhs rhs bs : AST)
    (matchFuel : Nat)
    (hrest : IsNormal pMI rest) (hterm : IsNormal pMI term)
    (hrhs : IsNormal pMI rhs)
    (hmatch : eval pMI matchFuel (miMatch lhs term MIBNil) = MIMatchOk bs)
    (hactive : ∀ k, k < matchFuel →
      MatchActiveShape (eval pMI k (miMatch lhs term MIBNil))) :
    ∃ N,
      eval pMI N (miRootK rest term rhs (miMatch lhs term MIBNil)) =
        MIRootStep (miSubst bs rhs) ∧
      ∀ k, k < N →
        RootActiveShape
          (eval pMI k (miRootK rest term rhs (miMatch lhs term MIBNil))) := by
  let F : AST → AST := fun z => miRootK rest term rhs z
  obtain ⟨Mmatch, hmatchCtx, hmatchCtxActive⟩ :=
    cong_eval_match_to_root_active_with_guard_mi F
      (fun s _hs => RootActiveShape.rootK rest term rhs s)
      (fun s s' hactiveStep hstep =>
        os_miRootK_active_step rest term rhs s s'
          hrest hterm hrhs hactiveStep hstep)
      matchFuel hmatch hactive
  have hok :
      eval pMI 1 (F (MIMatchOk bs)) =
        MIRootStep (miSubst bs rhs) := by
    simp only [F, eval, os_miRootK_ok]
  have htotal := eval_trans_mi Mmatch 1
    (miRootK rest term rhs (miMatch lhs term MIBNil))
    (F (MIMatchOk bs))
    (MIRootStep (miSubst bs rhs))
    hmatchCtx hok
  refine ⟨Mmatch + 1, htotal, ?_⟩
  intro k hk
  by_cases hlt : k < Mmatch
  · exact hmatchCtxActive k hlt
  · have hk_ge : Mmatch ≤ k := Nat.le_of_not_gt hlt
    have hk_le : k ≤ Mmatch := Nat.le_of_lt_succ hk
    have hk_eq : k = Mmatch := Nat.le_antisymm hk_le hk_ge
    subst k
    change RootActiveShape (eval pMI Mmatch (F (miMatch lhs term MIBNil)))
    rw [hmatchCtx]
    exact RootActiveShape.rootK rest term rhs (MIMatchOk bs)

theorem miRootK_eval_of_match_fail_active (rest term lhs rhs : AST)
    (matchFuel : Nat)
    (hrest : IsNormal pMI rest) (hterm : IsNormal pMI term)
    (hrhs : IsNormal pMI rhs)
    (hmatch : eval pMI matchFuel (miMatch lhs term MIBNil) = MIMatchFail)
    (hactive : ∀ k, k < matchFuel →
      MatchActiveShape (eval pMI k (miMatch lhs term MIBNil))) :
    ∃ N,
      eval pMI N (miRootK rest term rhs (miMatch lhs term MIBNil)) =
        miRootTable rest term ∧
      ∀ k, k < N →
        RootActiveShape
          (eval pMI k (miRootK rest term rhs (miMatch lhs term MIBNil))) := by
  let F : AST → AST := fun z => miRootK rest term rhs z
  obtain ⟨Mmatch, hmatchCtx, hmatchCtxActive⟩ :=
    cong_eval_match_to_root_active_with_guard_mi F
      (fun s _hs => RootActiveShape.rootK rest term rhs s)
      (fun s s' hactiveStep hstep =>
        os_miRootK_active_step rest term rhs s s'
          hrest hterm hrhs hactiveStep hstep)
      matchFuel hmatch hactive
  have hfail :
      eval pMI 1 (F MIMatchFail) =
        miRootTable rest term := by
    simp only [F, eval, os_miRootK_fail]
  have htotal := eval_trans_mi Mmatch 1
    (miRootK rest term rhs (miMatch lhs term MIBNil))
    (F MIMatchFail)
    (miRootTable rest term)
    hmatchCtx hfail
  refine ⟨Mmatch + 1, htotal, ?_⟩
  intro k hk
  by_cases hlt : k < Mmatch
  · exact hmatchCtxActive k hlt
  · have hk_ge : Mmatch ≤ k := Nat.le_of_not_gt hlt
    have hk_le : k ≤ Mmatch := Nat.le_of_lt_succ hk
    have hk_eq : k = Mmatch := Nat.le_antisymm hk_le hk_ge
    subst k
    change RootActiveShape (eval pMI Mmatch (F (miMatch lhs term MIBNil)))
    rw [hmatchCtx]
    exact RootActiveShape.rootK rest term rhs MIMatchFail

theorem miRootTable_rule_source_some_raw_active_sim
    (lhs rhs term encodedLhs encodedRhs encodedTerm encodedRest : AST)
    (rest : List RewriteDecl) (bs : List (String × AST))
    (hlhs : encAST? lhs = some encodedLhs)
    (hrhs : encAST? rhs = some encodedRhs)
    (hterm : encAST? term = some encodedTerm)
    (hrest : encRules? rest = some encodedRest)
    (hmatch : AST.matchPat lhs term [] = some bs) :
    ∃ (encodedBs : AST) (N : Nat),
      encBinds? bs = some encodedBs ∧
      eval pMI N
          (miRootTable
            (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
            encodedTerm) =
        MIRootStep (miSubst encodedBs encodedRhs) ∧
      (∀ k, k < N →
        RootActiveShape
          (eval pMI k
            (miRootTable
              (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
              encodedTerm))) ∧
      IsNormal pMI encodedBs := by
  obtain ⟨encodedBs, hbs⟩ :=
    matchPat_preserves_encBinds? lhs term encodedLhs encodedTerm MIBNil
      [] bs hlhs hterm rfl hmatch
  obtain ⟨Nmatch, hmatchEval, hactive, _hmatchNorm⟩ :=
    miMatch_source_some_first_result lhs term encodedLhs encodedTerm
      MIBNil encodedBs [] bs hlhs hterm rfl hmatch hbs
  obtain ⟨NrootK, hrootK, hrootKActive⟩ :=
    miRootK_eval_of_match_ok_raw_active encodedRest encodedTerm encodedLhs
      encodedRhs encodedBs Nmatch
      (encRules?_some_normal rest encodedRest hrest)
      (encAST?_some_normal term encodedTerm hterm)
      (encAST?_some_normal rhs encodedRhs hrhs)
      hmatchEval hactive
  let start :=
    miRootTable (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
      encodedTerm
  let next := miRootK encodedRest encodedTerm encodedRhs
    (miMatch encodedLhs encodedTerm MIBNil)
  have hdispatch : eval pMI 1 start = next := by
    simp only [start, next, eval, os_miRootTable_rule_cons]
  have htotal := eval_trans_mi 1 NrootK
    start next (MIRootStep (miSubst encodedBs encodedRhs))
    hdispatch hrootK
  refine ⟨encodedBs, 1 + NrootK, hbs, htotal, ?_,
    encBinds?_some_normal bs encodedBs hbs⟩
  intro k hk
  cases k with
  | zero =>
      simp only [eval]
      exact RootActiveShape.rootTable
        (MIRCons (MIRule encodedLhs encodedRhs) encodedRest) encodedTerm
  | succ k =>
      have hkRoot : k < NrootK := by
        exact Nat.succ_lt_succ_iff.mp (by
          simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using hk)
      have hsucc : eval pMI (Nat.succ k) start = eval pMI k next := by
        simp only [start, next, eval, os_miRootTable_rule_cons]
      rw [hsucc]
      exact hrootKActive k hkRoot

theorem miRootTable_rule_source_some_raw_active_sim_payload
    (lhs rhs term encodedLhs encodedRhs encodedTerm encodedRest : AST)
    (rest : List RewriteDecl) (bs : List (String × AST))
    (hlhs : encAST? lhs = some encodedLhs)
    (hrhs : encAST? rhs = some encodedRhs)
    (hterm : encAST? term = some encodedTerm)
    (hrest : encRules? rest = some encodedRest)
    (hmatch : AST.matchPat lhs term [] = some bs) :
    ∃ (encodedBs encodedOut : AST) (rootFuel substFuel : Nat),
      encBinds? bs = some encodedBs ∧
      encAST? (AST.inst bs rhs) = some encodedOut ∧
      eval pMI rootFuel
          (miRootTable
            (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
            encodedTerm) =
        MIRootStep (miSubst encodedBs encodedRhs) ∧
      (∀ k, k < rootFuel →
        RootActiveShape
          (eval pMI k
            (miRootTable
              (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
              encodedTerm))) ∧
      eval pMI substFuel (miSubst encodedBs encodedRhs) = encodedOut ∧
      IsNormal pMI encodedOut ∧
      RawTermPayload (miSubst encodedBs encodedRhs) encodedOut := by
  obtain ⟨encodedBs, rootFuel, hbs, hroot, hrootActive,
    _hbsNorm⟩ :=
    miRootTable_rule_source_some_raw_active_sim lhs rhs term encodedLhs
      encodedRhs encodedTerm encodedRest rest bs hlhs hrhs hterm hrest
      hmatch
  obtain ⟨encodedOut, substFuel, hout, hsubst, houtNorm⟩ :=
    miSubst_encAST_inst_eval rhs encodedRhs hrhs bs encodedBs hbs
  exact ⟨encodedBs, encodedOut, rootFuel, substFuel, hbs, hout, hroot,
    hrootActive, hsubst, houtNorm,
    RawTermPayload.substInst hrhs hbs hout hsubst houtNorm⟩

theorem miRootTable_rule_source_none_active_eval_of_rest
    (lhs rhs term encodedLhs encodedRhs encodedTerm encodedRest restOut : AST)
    (rest : List RewriteDecl) (restFuel : Nat)
    (hlhs : encAST? lhs = some encodedLhs)
    (hrhs : encAST? rhs = some encodedRhs)
    (hterm : encAST? term = some encodedTerm)
    (hrest : encRules? rest = some encodedRest)
    (hmatch : AST.matchPat lhs term [] = none)
    (hrestEval : eval pMI restFuel (miRootTable encodedRest encodedTerm) = restOut)
    (hrestActive : ∀ k, k < restFuel →
      RootActiveShape (eval pMI k (miRootTable encodedRest encodedTerm))) :
    ∃ N,
      eval pMI N
          (miRootTable
            (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
            encodedTerm) =
        restOut ∧
      ∀ k, k < N →
        RootActiveShape
          (eval pMI k
            (miRootTable
              (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
              encodedTerm)) := by
  obtain ⟨Nmatch, hmatchEval, hactive, _hmatchNorm⟩ :=
    miMatch_source_none_first_result lhs term encodedLhs encodedTerm
      MIBNil [] hlhs hterm rfl hmatch
  obtain ⟨NrootK, hrootK, hrootKActive⟩ :=
    miRootK_eval_of_match_fail_active encodedRest encodedTerm encodedLhs
      encodedRhs Nmatch
      (encRules?_some_normal rest encodedRest hrest)
      (encAST?_some_normal term encodedTerm hterm)
      (encAST?_some_normal rhs encodedRhs hrhs)
      hmatchEval hactive
  let start :=
    miRootTable (MIRCons (MIRule encodedLhs encodedRhs) encodedRest)
      encodedTerm
  let next := miRootK encodedRest encodedTerm encodedRhs
    (miMatch encodedLhs encodedTerm MIBNil)
  let restStart := miRootTable encodedRest encodedTerm
  have hdispatch : eval pMI 1 start = next := by
    simp only [start, next, eval, os_miRootTable_rule_cons]
  have hpre := eval_trans_mi 1 NrootK start next restStart
    hdispatch hrootK
  have htotal := eval_trans_mi (1 + NrootK) restFuel
    start restStart restOut hpre hrestEval
  refine ⟨(1 + NrootK) + restFuel, htotal, ?_⟩
  exact root_active_append_mi (1 + NrootK) restFuel hpre
    (by
      intro k hk
      cases k with
      | zero =>
          simp only [eval]
          exact RootActiveShape.rootTable
            (MIRCons (MIRule encodedLhs encodedRhs) encodedRest) encodedTerm
      | succ k =>
          have hkRoot : k < NrootK := by omega
          have hsucc : eval pMI (Nat.succ k) start = eval pMI k next := by
            simp only [start, next, eval, os_miRootTable_rule_cons]
          rw [hsucc]
          exact hrootKActive k hkRoot)
    (by
      intro k hk
      simpa only [restStart] using hrestActive k hk)

def RootTableRawActiveSome
    (encodedRules encodedTerm out : AST) : Prop :=
  ∃ (rawNext encodedOut : AST) (rootFuel substFuel : Nat),
    encAST? out = some encodedOut ∧
    eval pMI rootFuel (miRootTable encodedRules encodedTerm) =
      MIRootStep rawNext ∧
    (∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRootTable encodedRules encodedTerm))) ∧
    eval pMI substFuel rawNext = encodedOut ∧
    IsNormal pMI encodedOut

def RootTableRawActiveSomePayload
    (encodedRules encodedTerm out : AST) : Prop :=
  ∃ (rawNext encodedOut : AST) (rootFuel substFuel : Nat),
    encAST? out = some encodedOut ∧
    eval pMI rootFuel (miRootTable encodedRules encodedTerm) =
      MIRootStep rawNext ∧
    (∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRootTable encodedRules encodedTerm))) ∧
    eval pMI substFuel rawNext = encodedOut ∧
    IsNormal pMI encodedOut ∧
    RawTermPayload rawNext encodedOut

def RootTableRawActiveNone
    (encodedRules encodedTerm : AST) : Prop :=
  ∃ rootFuel,
    eval pMI rootFuel (miRootTable encodedRules encodedTerm) =
      MINoRoot ∧
    ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRootTable encodedRules encodedTerm))

theorem miMatch_encoded_misubst_source_none_fail
    (lhs term encodedLhs rawBs rawRhs : AST)
    (hlhs : encAST? lhs = some encodedLhs)
    (hmatch : AST.matchPat lhs term [] = none) :
    ∃ N,
      eval pMI N (miMatch encodedLhs (miSubst rawBs rawRhs) MIBNil) =
        MIMatchFail ∧
      ∀ k, k < N →
        MatchActiveShape
          (eval pMI k
            (miMatch encodedLhs (miSubst rawBs rawRhs) MIBNil)) := by
  cases lhs with
  | var path =>
      cases path with
      | base v =>
          simp only [encAST?] at hlhs
          cases hlhs
          simp [AST.matchPat] at hmatch
      | qualified _ _ =>
          simp only [encAST?] at hlhs
          cases hlhs
  | sexp label args =>
      cases label with
      | id s =>
          cases args with
          | nil =>
              simp only [encAST?] at hlhs
              cases hlhs
              exact ⟨1, rfl,
                miMatch_active_guard_one (MISym s)
                  (miSubst rawBs rawRhs) MIBNil⟩
          | cons a rest =>
              cases hargs : encASTList? (a :: rest) with
              | none =>
                  simp only [encAST?, hargs] at hlhs
                  cases hlhs
              | some encodedArgs =>
                  simp only [encAST?, hargs] at hlhs
                  cases hlhs
                  exact ⟨1, rfl,
                    miMatch_active_guard_one (MIApp s encodedArgs)
                      (miSubst rawBs rawRhs) MIBNil⟩
      | wild =>
          simp only [encAST?] at hlhs
          cases hlhs
      | listE _ =>
          simp only [encAST?] at hlhs
          cases hlhs
      | listCons _ =>
          simp only [encAST?] at hlhs
          cases hlhs
      | listOne _ =>
          simp only [encAST?] at hlhs
          cases hlhs
  | subst _ _ _ =>
      simp only [encAST?] at hlhs
      cases hlhs

theorem miRootTable_source_raw_active_spec :
    ∀ (rws : List RewriteDecl) (term encodedRules encodedTerm : AST),
      encRules? rws = some encodedRules →
      encAST? term = some encodedTerm →
      (∀ out, rootBaseStep? rws term = some out →
        RootTableRawActiveSome encodedRules encodedTerm out) ∧
      (rootBaseStep? rws term = none →
        RootTableRawActiveNone encodedRules encodedTerm)
  | [], term, encodedRules, encodedTerm, hrules, _hterm => by
      cases hrules
      constructor
      · intro out hcase
        simp only [rootBaseStep?] at hcase
        exact nomatch hcase
      · intro _hcase
        unfold RootTableRawActiveNone
        refine ⟨1, miRootTable_nil_sim encodedTerm, ?_⟩
        intro k hk
        cases k with
        | zero =>
            simp only [eval]
            exact RootActiveShape.rootTable MIRNil encodedTerm
        | succ n =>
            have hn : n < 0 := Nat.succ_lt_succ_iff.mp hk
            exact False.elim (Nat.not_lt_zero n hn)
  | rd :: rest, term, encodedRules, encodedTerm, hrules, hterm => by
      cases hrdRw : rd.rw with
      | ctx _ _ =>
          simp only [encRules?, encRewriteDecl?, hrdRw] at hrules
          cases hrules
      | base lhs rhs =>
          simp only [encRules?, encRewriteDecl?, hrdRw] at hrules
          cases hlhs : encAST? lhs with
          | none =>
              simp [hlhs] at hrules
          | some encodedLhs =>
              cases hrhs : encAST? rhs with
              | none =>
                  simp [hlhs, hrhs] at hrules
              | some encodedRhs =>
                  cases hrest : encRules? rest with
                  | none =>
                      simp [hlhs, hrhs, hrest] at hrules
                  | some encodedRest =>
                      simp [hlhs, hrhs, hrest] at hrules
                      cases hrules
                      cases hmatch : AST.matchPat lhs term [] with
                      | some bs =>
                          constructor
                          · intro out hcase
                            simp only [rootBaseStep?, hrdRw, hmatch] at hcase
                            cases hcase
                            unfold RootTableRawActiveSome
                            obtain ⟨encodedBs, Nroot, hbs, hroot,
                              hrootActive, _hbsNorm⟩ :=
                              miRootTable_rule_source_some_raw_active_sim
                                lhs rhs term encodedLhs encodedRhs
                                encodedTerm encodedRest rest bs
                                hlhs hrhs hterm hrest hmatch
                            obtain ⟨encodedOut, Nsubst, hout, hsubst,
                              houtNorm⟩ :=
                              miSubst_encAST_inst_eval rhs encodedRhs hrhs
                                bs encodedBs hbs
                            exact ⟨miSubst encodedBs encodedRhs, encodedOut,
                              Nroot, Nsubst, hout, hroot, hrootActive, hsubst,
                              houtNorm⟩
                          · intro hcase
                            simp only [rootBaseStep?, hrdRw, hmatch] at hcase
                            exact nomatch hcase
                      | none =>
                          have htail :=
                            miRootTable_source_raw_active_spec rest term
                              encodedRest encodedTerm hrest hterm
                          constructor
                          · intro out hcase

                            simp only [rootBaseStep?, hrdRw, hmatch] at hcase
                            have htailSome := htail.1 out hcase
                            unfold RootTableRawActiveSome at htailSome ⊢
                            obtain ⟨rawNext, encodedOut, NtailRoot,
                              NtailSubst, hout, htailEval, htailActive,
                              hsubst, houtNorm⟩ := htailSome
                            obtain ⟨Nroot, hroot, hrootActive⟩ :=
                              miRootTable_rule_source_none_active_eval_of_rest
                                lhs rhs term encodedLhs encodedRhs
                                encodedTerm encodedRest
                                (MIRootStep rawNext) rest NtailRoot
                                hlhs hrhs hterm hrest hmatch htailEval
                                htailActive
                            exact ⟨rawNext, encodedOut, Nroot, NtailSubst,
                              hout, hroot, hrootActive, hsubst, houtNorm⟩
                          · intro hcase
                            simp only [rootBaseStep?, hrdRw, hmatch] at hcase
                            have htailNone := htail.2 hcase
                            unfold RootTableRawActiveNone at htailNone ⊢
                            obtain ⟨NtailRoot, htailEval, htailActive⟩ :=
                              htailNone
                            obtain ⟨Nroot, hroot, hrootActive⟩ :=
                              miRootTable_rule_source_none_active_eval_of_rest
                                lhs rhs term encodedLhs encodedRhs
                                encodedTerm encodedRest MINoRoot rest
                                NtailRoot hlhs hrhs hterm hrest hmatch
                              htailEval htailActive
                            exact ⟨Nroot, hroot, hrootActive⟩

theorem miRootTable_source_raw_active_spec_payload :
    ∀ (rws : List RewriteDecl) (term encodedRules encodedTerm : AST),
      encRules? rws = some encodedRules →
      encAST? term = some encodedTerm →
      (∀ out, rootBaseStep? rws term = some out →
        RootTableRawActiveSomePayload encodedRules encodedTerm out) ∧
      (rootBaseStep? rws term = none →
        RootTableRawActiveNone encodedRules encodedTerm)
  | [], term, encodedRules, encodedTerm, hrules, _hterm => by
      cases hrules
      constructor
      · intro out hcase
        simp only [rootBaseStep?] at hcase
        exact nomatch hcase
      · intro _hcase
        unfold RootTableRawActiveNone
        refine ⟨1, miRootTable_nil_sim encodedTerm, ?_⟩
        intro k hk
        cases k with
        | zero =>
            simp only [eval]
            exact RootActiveShape.rootTable MIRNil encodedTerm
        | succ n =>
            have hn : n < 0 := Nat.succ_lt_succ_iff.mp hk
            exact False.elim (Nat.not_lt_zero n hn)
  | rd :: rest, term, encodedRules, encodedTerm, hrules, hterm => by
      cases hrdRw : rd.rw with
      | ctx _ _ =>
          simp only [encRules?, encRewriteDecl?, hrdRw] at hrules
          cases hrules
      | base lhs rhs =>
          simp only [encRules?, encRewriteDecl?, hrdRw] at hrules
          cases hlhs : encAST? lhs with
          | none =>
              simp [hlhs] at hrules
          | some encodedLhs =>
              cases hrhs : encAST? rhs with
              | none =>
                  simp [hlhs, hrhs] at hrules
              | some encodedRhs =>
                  cases hrest : encRules? rest with
                  | none =>
                      simp [hlhs, hrhs, hrest] at hrules
                  | some encodedRest =>
                      simp [hlhs, hrhs, hrest] at hrules
                      cases hrules
                      cases hmatch : AST.matchPat lhs term [] with
                      | some bs =>
                          constructor
                          · intro out hcase
                            simp only [rootBaseStep?, hrdRw, hmatch] at hcase
                            cases hcase
                            unfold RootTableRawActiveSomePayload
                            obtain ⟨encodedBs, encodedOut, Nroot,
                              Nsubst, _hbs, hout, hroot, hrootActive,
                              hsubst, houtNorm, hpayload⟩ :=
                              miRootTable_rule_source_some_raw_active_sim_payload
                                lhs rhs term encodedLhs encodedRhs
                                encodedTerm encodedRest rest bs
                                hlhs hrhs hterm hrest hmatch
                            exact ⟨miSubst encodedBs encodedRhs, encodedOut,
                              Nroot, Nsubst, hout, hroot, hrootActive, hsubst,
                              houtNorm, hpayload⟩
                          · intro hcase
                            simp only [rootBaseStep?, hrdRw, hmatch] at hcase
                            exact nomatch hcase
                      | none =>
                          have htail :=
                            miRootTable_source_raw_active_spec_payload rest
                              term encodedRest encodedTerm hrest hterm
                          constructor
                          · intro out hcase
                            simp only [rootBaseStep?, hrdRw, hmatch] at hcase
                            have htailSome := htail.1 out hcase
                            unfold RootTableRawActiveSomePayload at htailSome ⊢
                            obtain ⟨rawNext, encodedOut, NtailRoot,
                              NtailSubst, hout, htailEval, htailActive,
                              hsubst, houtNorm, hpayload⟩ := htailSome
                            obtain ⟨Nroot, hroot, hrootActive⟩ :=
                              miRootTable_rule_source_none_active_eval_of_rest
                                lhs rhs term encodedLhs encodedRhs
                                encodedTerm encodedRest
                                (MIRootStep rawNext) rest NtailRoot
                                hlhs hrhs hterm hrest hmatch htailEval
                                htailActive
                            exact ⟨rawNext, encodedOut, Nroot, NtailSubst,
                              hout, hroot, hrootActive, hsubst, houtNorm,
                              hpayload⟩
                          · intro hcase
                            simp only [rootBaseStep?, hrdRw, hmatch] at hcase
                            have htailNone := htail.2 hcase
                            unfold RootTableRawActiveNone at htailNone ⊢
                            obtain ⟨NtailRoot, htailEval, htailActive⟩ :=
                              htailNone
                            obtain ⟨Nroot, hroot, hrootActive⟩ :=
                              miRootTable_rule_source_none_active_eval_of_rest
                                lhs rhs term encodedLhs encodedRhs
                                encodedTerm encodedRest MINoRoot rest
                                NtailRoot hlhs hrhs hterm hrest hmatch
                                htailEval htailActive
                            exact ⟨Nroot, hroot, hrootActive⟩

theorem miRootTable_source_raw_active_sim
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm) :
    match rootBaseStep? rws term with
    | some out =>
        ∃ (rawNext encodedOut : AST) (rootFuel substFuel : Nat),
          encAST? out = some encodedOut ∧
          eval pMI rootFuel (miRootTable encodedRules encodedTerm) =
            MIRootStep rawNext ∧
          (∀ k, k < rootFuel →
            RootActiveShape
              (eval pMI k (miRootTable encodedRules encodedTerm))) ∧
          eval pMI substFuel rawNext = encodedOut ∧
          IsNormal pMI encodedOut
    | none =>
        ∃ rootFuel,
          eval pMI rootFuel (miRootTable encodedRules encodedTerm) =
            MINoRoot ∧
          ∀ k, k < rootFuel →
            RootActiveShape
              (eval pMI k (miRootTable encodedRules encodedTerm)) := by
  have hspec :=
    miRootTable_source_raw_active_spec rws term encodedRules encodedTerm
      hrules hterm
  cases hcase : rootBaseStep? rws term with
  | some out =>
      simpa only [hcase, RootTableRawActiveSome] using hspec.1 out hcase
  | none =>
      simpa only [hcase, RootTableRawActiveNone] using hspec.2 hcase

theorem miRootTable_misubst_source_none_active
    (rws : List RewriteDecl) (term encodedRules encodedTerm rawBs rawRhs : AST)
    (rawFuel : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hroot : rootBaseStep? rws term = none)
    (hraw : eval pMI rawFuel (miSubst rawBs rawRhs) = encodedTerm)
    (hencoded : IsNormal pMI encodedTerm) :
    RootTableRawActiveNone encodedRules (miSubst rawBs rawRhs) := by
  cases rws with
  | nil =>
      simp only [encRules?] at hrules
      cases hrules
      unfold RootTableRawActiveNone
      refine ⟨1, ?_, ?_⟩
      · exact miRootTable_nil_sim (miSubst rawBs rawRhs)
      · intro k hk
        cases k with
        | zero =>
            simp only [eval]
            exact RootActiveShape.rootTable MIRNil (miSubst rawBs rawRhs)
        | succ n =>
            have hn : n < 0 := Nat.succ_lt_succ_iff.mp hk
            exact False.elim (Nat.not_lt_zero n hn)
  | cons rd rest =>
      cases hrdRw : rd.rw with
      | ctx _ _ =>
          simp only [encRules?, encRewriteDecl?, hrdRw] at hrules
          cases hrules
      | base lhs rhs =>
          simp only [encRules?, encRewriteDecl?, hrdRw] at hrules
          cases hlhs : encAST? lhs with
          | none =>
              simp [hlhs] at hrules
          | some encodedLhs =>
              cases hrhs : encAST? rhs with
              | none =>
                  simp [hlhs, hrhs] at hrules
              | some encodedRhs =>
                  cases hrest : encRules? rest with
                  | none =>
                      simp [hlhs, hrhs, hrest] at hrules
                  | some encodedRest =>
                      simp [hlhs, hrhs, hrest] at hrules
                      cases hrules
                      cases hmatch : AST.matchPat lhs term [] with
                      | some _bs =>
                          simp only [rootBaseStep?, hrdRw, hmatch] at hroot
                          cases hroot
                      | none =>
                          have htailRoot :
                              rootBaseStep? rest term = none := by
                            simpa only [rootBaseStep?, hrdRw, hmatch] using
                              hroot
                          have hrestEncoded :=
                            miRootTable_source_raw_active_sim rest term
                              encodedRest encodedTerm hrest hterm
                          simp only [htailRoot] at hrestEncoded
                          obtain ⟨restFuel, hrestEval, hrestActive⟩ :=
                            hrestEncoded
                          obtain ⟨matchFuel, hmatchEval, hmatchActive⟩ :=
                            miMatch_encoded_misubst_source_none_fail lhs
                              term encodedLhs rawBs rawRhs hlhs hmatch
                          let rawTerm := miSubst rawBs rawRhs
                          let start :=
                            miRootTable
                              (MIRCons (MIRule encodedLhs encodedRhs)
                                encodedRest)
                              rawTerm
                          let afterDispatch :=
                            miRootK encodedRest rawTerm encodedRhs
                              (miMatch encodedLhs rawTerm MIBNil)
                          let afterTerm :=
                            miRootK encodedRest encodedTerm encodedRhs
                              (miMatch encodedLhs rawTerm MIBNil)
                          have hdispatch :
                              eval pMI 1 start = afterDispatch := by
                            simp only [start, afterDispatch, eval,
                              os_miRootTable_rule_cons]
                          obtain ⟨termFuel, htermEval, htermActive⟩ :=
                            miRootK_active_term_eval_of encodedRest rawTerm
                              encodedTerm encodedRhs
                              (miMatch encodedLhs rawTerm MIBNil)
                              rawFuel
                              (encRules?_some_normal rest encodedRest hrest)
                              (MatchActiveShape.match encodedLhs rawTerm
                                MIBNil)
                              hraw hencoded
                          have htermEval' :
                              eval pMI termFuel afterDispatch = afterTerm := by
                            simpa only [afterDispatch, afterTerm, rawTerm]
                              using htermEval
                          obtain ⟨matchKFuel, hmatchK, hmatchKActive⟩ :=
                            miRootK_eval_of_match_fail_active_any
                              encodedRest encodedTerm encodedRhs
                              (miMatch encodedLhs rawTerm MIBNil)
                              matchFuel
                              (encRules?_some_normal rest encodedRest hrest)
                              hencoded
                              (encAST?_some_normal rhs encodedRhs hrhs)
                              hmatchEval hmatchActive
                          have htotal1 := eval_trans_mi 1 termFuel start
                            afterDispatch afterTerm hdispatch htermEval'
                          have htotal2 :=
                            eval_trans_mi (1 + termFuel) matchKFuel
                              start afterTerm
                              (miRootTable encodedRest encodedTerm)
                              htotal1 hmatchK
                          have htotal3 :=
                            eval_trans_mi ((1 + termFuel) + matchKFuel)
                              restFuel start
                              (miRootTable encodedRest encodedTerm)
                              MINoRoot htotal2 hrestEval
                          unfold RootTableRawActiveNone
                          refine
                            ⟨((1 + termFuel) + matchKFuel) + restFuel,
                              htotal3, ?_⟩
                          apply root_active_append_mi
                            ((1 + termFuel) + matchKFuel) restFuel htotal2
                          · apply root_active_append_mi (1 + termFuel)
                              matchKFuel htotal1
                            · apply root_active_append_mi 1 termFuel
                                hdispatch
                              · intro k hk
                                cases k with
                                | zero =>
                                    simp only [eval, start]
                                    exact RootActiveShape.rootTable
                                      (MIRCons
                                        (MIRule encodedLhs encodedRhs)
                                        encodedRest)
                                      rawTerm
                                | succ n =>
                                    have hn : n < 0 :=
                                      Nat.succ_lt_succ_iff.mp hk
                                    exact False.elim (Nat.not_lt_zero n hn)
                              · simpa only [afterDispatch] using htermActive
                            · simpa only [afterTerm] using hmatchKActive
                          · simpa using hrestActive

theorem miRoot_misubst_source_none_active
    (rws : List RewriteDecl) (term encodedRules encodedTerm rawBs rawRhs : AST)
    (rawFuel : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hroot : rootBaseStep? rws term = none)
    (hraw : eval pMI rawFuel (miSubst rawBs rawRhs) = encodedTerm)
    (hencoded : IsNormal pMI encodedTerm) :
    ∃ rootFuel,
      eval pMI rootFuel (miRoot encodedRules (miSubst rawBs rawRhs)) =
        MINoRoot ∧
      ∀ k, k < rootFuel →
        RootActiveShape
          (eval pMI k (miRoot encodedRules (miSubst rawBs rawRhs))) := by
  have htableNone :=
    miRootTable_misubst_source_none_active rws term encodedRules
      encodedTerm rawBs rawRhs rawFuel hrules hterm hroot hraw hencoded
  unfold RootTableRawActiveNone at htableNone
  obtain ⟨tableFuel, htable, htableActive⟩ :=
    htableNone
  have hdispatch :
      eval pMI 1 (miRoot encodedRules (miSubst rawBs rawRhs)) =
        miRootTable encodedRules (miSubst rawBs rawRhs) := by
    simp only [eval, os_miRoot_misubst_default]
  have htotal := eval_trans_mi 1 tableFuel
    (miRoot encodedRules (miSubst rawBs rawRhs))
    (miRootTable encodedRules (miSubst rawBs rawRhs))
    MINoRoot hdispatch htable
  refine ⟨1 + tableFuel, htotal, ?_⟩
  apply root_active_append_mi 1 tableFuel hdispatch
  · intro k hk
    cases k with
    | zero =>
        simp only [eval]
        exact RootActiveShape.root encodedRules (miSubst rawBs rawRhs)
    | succ n =>
        have hn : n < 0 := Nat.succ_lt_succ_iff.mp hk
        exact False.elim (Nat.not_lt_zero n hn)
  · exact htableActive

theorem miRootTable_rawPayload_source_none_active
    (rws : List RewriteDecl) (term encodedRules encodedTerm rawTerm : AST)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hroot : rootBaseStep? rws term = none)
    (hraw : RawTermPayload rawTerm encodedTerm)
    (hencoded : IsNormal pMI encodedTerm) :
    RootTableRawActiveNone encodedRules rawTerm := by
  obtain ⟨rawFuel, hrawEval⟩ :=
    rawTermPayload_eval_of_normal hraw hencoded
  cases rws with
  | nil =>
      simp only [encRules?] at hrules
      cases hrules
      unfold RootTableRawActiveNone
      refine ⟨1, ?_, ?_⟩
      · exact miRootTable_nil_sim rawTerm
      · intro k hk
        cases k with
        | zero =>
            simp only [eval]
            exact RootActiveShape.rootTable MIRNil rawTerm
        | succ n =>
            have hn : n < 0 := Nat.succ_lt_succ_iff.mp hk
            exact False.elim (Nat.not_lt_zero n hn)
  | cons rd rest =>
      cases hrdRw : rd.rw with
      | ctx _ _ =>
          simp only [encRules?, encRewriteDecl?, hrdRw] at hrules
          cases hrules
      | base lhs rhs =>
          simp only [encRules?, encRewriteDecl?, hrdRw] at hrules
          cases hlhs : encAST? lhs with
          | none =>
              simp [hlhs] at hrules
          | some encodedLhs =>
              cases hrhs : encAST? rhs with
              | none =>
                  simp [hlhs, hrhs] at hrules
              | some encodedRhs =>
                  cases hrest : encRules? rest with
                  | none =>
                      simp [hlhs, hrhs, hrest] at hrules
                  | some encodedRest =>
                      simp [hlhs, hrhs, hrest] at hrules
                      cases hrules
                      cases hmatch : AST.matchPat lhs term [] with
                      | some _bs =>
                          simp only [rootBaseStep?, hrdRw, hmatch] at hroot
                          cases hroot
                      | none =>
                          have htailRoot :
                              rootBaseStep? rest term = none := by
                            simpa only [rootBaseStep?, hrdRw, hmatch] using
                              hroot
                          have hrestEncoded :=
                            miRootTable_source_raw_active_sim rest term
                              encodedRest encodedTerm hrest hterm
                          simp only [htailRoot] at hrestEncoded
                          obtain ⟨restFuel, hrestEval, hrestActive⟩ :=
                            hrestEncoded
                          have hmatchRaw :=
                            miMatch_rawPayload_source_none_first_result_general
                              lhs term encodedLhs encodedTerm rawTerm MIBNil
                              MIBNil [] hlhs hterm hraw RawBindsFor.nil
                              hmatch
                          unfold RawMatchFailResult at hmatchRaw
                          obtain ⟨matchFuel, hmatchEval, hmatchActive,
                            _hmatchNorm⟩ := hmatchRaw
                          let start :=
                            miRootTable
                              (MIRCons (MIRule encodedLhs encodedRhs)
                                encodedRest)
                              rawTerm
                          let afterDispatch :=
                            miRootK encodedRest rawTerm encodedRhs
                              (miMatch encodedLhs rawTerm MIBNil)
                          let afterTerm :=
                            miRootK encodedRest encodedTerm encodedRhs
                              (miMatch encodedLhs rawTerm MIBNil)
                          have hdispatch :
                              eval pMI 1 start = afterDispatch := by
                            simp only [start, afterDispatch, eval,
                              os_miRootTable_rule_cons]
                          obtain ⟨termFuel, htermEval, htermActive⟩ :=
                            miRootK_active_term_eval_of encodedRest rawTerm
                              encodedTerm encodedRhs
                              (miMatch encodedLhs rawTerm MIBNil)
                              rawFuel
                              (encRules?_some_normal rest encodedRest hrest)
                              (MatchActiveShape.match encodedLhs rawTerm
                                MIBNil)
                              hrawEval hencoded
                          have htermEval' :
                              eval pMI termFuel afterDispatch = afterTerm := by
                            simpa only [afterDispatch, afterTerm] using
                              htermEval
                          obtain ⟨matchKFuel, hmatchK, hmatchKActive⟩ :=
                            miRootK_eval_of_match_fail_active_any
                              encodedRest encodedTerm encodedRhs
                              (miMatch encodedLhs rawTerm MIBNil)
                              matchFuel
                              (encRules?_some_normal rest encodedRest hrest)
                              hencoded
                              (encAST?_some_normal rhs encodedRhs hrhs)
                              hmatchEval hmatchActive
                          have htotal1 := eval_trans_mi 1 termFuel start
                            afterDispatch afterTerm hdispatch htermEval'
                          have htotal2 :=
                            eval_trans_mi (1 + termFuel) matchKFuel
                              start afterTerm
                              (miRootTable encodedRest encodedTerm)
                              htotal1 hmatchK
                          have htotal3 :=
                            eval_trans_mi ((1 + termFuel) + matchKFuel)
                              restFuel start
                              (miRootTable encodedRest encodedTerm)
                              MINoRoot htotal2 hrestEval
                          unfold RootTableRawActiveNone
                          refine
                            ⟨((1 + termFuel) + matchKFuel) + restFuel,
                              htotal3, ?_⟩
                          apply root_active_append_mi
                            ((1 + termFuel) + matchKFuel) restFuel htotal2
                          · apply root_active_append_mi (1 + termFuel)
                              matchKFuel htotal1
                            · apply root_active_append_mi 1 termFuel
                                hdispatch
                              · intro k hk
                                cases k with
                                | zero =>
                                    simp only [eval, start]
                                    exact RootActiveShape.rootTable
                                      (MIRCons
                                        (MIRule encodedLhs encodedRhs)
                                        encodedRest)
                                      rawTerm
                                | succ n =>
                                    have hn : n < 0 :=
                                      Nat.succ_lt_succ_iff.mp hk
                                    exact False.elim (Nat.not_lt_zero n hn)
                              · simpa only [afterDispatch] using htermActive
                            · simpa only [afterTerm] using hmatchKActive
                          · simpa using hrestActive

theorem miRootTable_source_raw_active_sim_payload
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm) :
    match rootBaseStep? rws term with
    | some out =>
        ∃ (rawNext encodedOut : AST) (rootFuel substFuel : Nat),
          encAST? out = some encodedOut ∧
          eval pMI rootFuel (miRootTable encodedRules encodedTerm) =
            MIRootStep rawNext ∧
          (∀ k, k < rootFuel →
            RootActiveShape
              (eval pMI k (miRootTable encodedRules encodedTerm))) ∧
          eval pMI substFuel rawNext = encodedOut ∧
          IsNormal pMI encodedOut ∧
          RawTermPayload rawNext encodedOut
    | none =>
        ∃ rootFuel,
          eval pMI rootFuel (miRootTable encodedRules encodedTerm) =
            MINoRoot ∧
          ∀ k, k < rootFuel →
            RootActiveShape
              (eval pMI k (miRootTable encodedRules encodedTerm)) := by
  have hspec :=
    miRootTable_source_raw_active_spec_payload rws term encodedRules
      encodedTerm hrules hterm
  cases hcase : rootBaseStep? rws term with
  | some out =>
      simpa only [hcase, RootTableRawActiveSomePayload] using
        hspec.1 out hcase
  | none =>
      simpa only [hcase, RootTableRawActiveNone] using hspec.2 hcase

theorem miRoot_eval_of_rootTable_source_raw_active_sim
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hdispatch : oneStep pMI (miRoot encodedRules encodedTerm) =
      some (miRootTable encodedRules encodedTerm)) :
    match rootBaseStep? rws term with
    | some out =>
        ∃ (rawNext encodedOut : AST) (rootFuel substFuel : Nat),
          encAST? out = some encodedOut ∧
          eval pMI rootFuel (miRoot encodedRules encodedTerm) =
            MIRootStep rawNext ∧
          (∀ k, k < rootFuel →
            RootActiveShape
              (eval pMI k (miRoot encodedRules encodedTerm))) ∧
          eval pMI substFuel rawNext = encodedOut ∧
          IsNormal pMI encodedOut
    | none =>
        ∃ rootFuel,
          eval pMI rootFuel (miRoot encodedRules encodedTerm) = MINoRoot ∧
          ∀ k, k < rootFuel →
            RootActiveShape
              (eval pMI k (miRoot encodedRules encodedTerm)) := by
  have htable :=
    miRootTable_source_raw_active_sim rws term encodedRules encodedTerm
      hrules hterm
  cases hcase : rootBaseStep? rws term with
  | some out =>
      simp only [hcase] at htable ⊢
      obtain ⟨rawNext, encodedOut, Ntable, Nsubst, hout, htableEval,
        htableActive, hsubst, houtNorm⟩ := htable
      have hrootDispatch :
          eval pMI 1 (miRoot encodedRules encodedTerm) =
            miRootTable encodedRules encodedTerm := by
        simp only [eval, hdispatch]
      have htotal := eval_trans_mi 1 Ntable
        (miRoot encodedRules encodedTerm)
        (miRootTable encodedRules encodedTerm)
        (MIRootStep rawNext)
        hrootDispatch htableEval
      refine ⟨rawNext, encodedOut, 1 + Ntable, Nsubst, hout, htotal,
        ?_, hsubst, houtNorm⟩
      intro k hk
      cases k with
      | zero =>
          simp only [eval]
          exact RootActiveShape.root encodedRules encodedTerm
      | succ k =>
          have hkTable : k < Ntable := by omega
          have hsucc :
              eval pMI (Nat.succ k) (miRoot encodedRules encodedTerm) =
                eval pMI k (miRootTable encodedRules encodedTerm) := by
            simp only [eval, hdispatch]
          rw [hsucc]
          exact htableActive k hkTable
  | none =>
      simp only [hcase] at htable ⊢
      obtain ⟨Ntable, htableEval, htableActive⟩ := htable
      have hrootDispatch :
          eval pMI 1 (miRoot encodedRules encodedTerm) =
            miRootTable encodedRules encodedTerm := by
        simp only [eval, hdispatch]
      have htotal := eval_trans_mi 1 Ntable
        (miRoot encodedRules encodedTerm)
        (miRootTable encodedRules encodedTerm)
        MINoRoot
        hrootDispatch htableEval
      refine ⟨1 + Ntable, htotal, ?_⟩
      intro k hk
      cases k with
      | zero =>
          simp only [eval]
          exact RootActiveShape.root encodedRules encodedTerm
      | succ k =>
          have hkTable : k < Ntable := by omega
          have hsucc :
              eval pMI (Nat.succ k) (miRoot encodedRules encodedTerm) =
                eval pMI k (miRootTable encodedRules encodedTerm) := by
            simp only [eval, hdispatch]
          rw [hsucc]
          exact htableActive k hkTable

theorem miRoot_eval_of_rootTable_source_raw_active_sim_payload
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hdispatch : oneStep pMI (miRoot encodedRules encodedTerm) =
      some (miRootTable encodedRules encodedTerm)) :
    match rootBaseStep? rws term with
    | some out =>
        ∃ (rawNext encodedOut : AST) (rootFuel substFuel : Nat),
          encAST? out = some encodedOut ∧
          eval pMI rootFuel (miRoot encodedRules encodedTerm) =
            MIRootStep rawNext ∧
          (∀ k, k < rootFuel →
            RootActiveShape
              (eval pMI k (miRoot encodedRules encodedTerm))) ∧
          eval pMI substFuel rawNext = encodedOut ∧
          IsNormal pMI encodedOut ∧
          RawTermPayload rawNext encodedOut
    | none =>
        ∃ rootFuel,
          eval pMI rootFuel (miRoot encodedRules encodedTerm) = MINoRoot ∧
          ∀ k, k < rootFuel →
            RootActiveShape
              (eval pMI k (miRoot encodedRules encodedTerm)) := by
  have htable :=
    miRootTable_source_raw_active_sim_payload rws term encodedRules
      encodedTerm hrules hterm
  cases hcase : rootBaseStep? rws term with
  | some out =>
      simp only [hcase] at htable ⊢
      obtain ⟨rawNext, encodedOut, Ntable, Nsubst, hout, htableEval,
        htableActive, hsubst, houtNorm, hpayload⟩ := htable
      have hrootDispatch :
          eval pMI 1 (miRoot encodedRules encodedTerm) =
            miRootTable encodedRules encodedTerm := by
        simp only [eval, hdispatch]
      have htotal := eval_trans_mi 1 Ntable
        (miRoot encodedRules encodedTerm)
        (miRootTable encodedRules encodedTerm)
        (MIRootStep rawNext)
        hrootDispatch htableEval
      refine ⟨rawNext, encodedOut, 1 + Ntable, Nsubst, hout, htotal,
        ?_, hsubst, houtNorm, hpayload⟩
      intro k hk
      cases k with
      | zero =>
          simp only [eval]
          exact RootActiveShape.root encodedRules encodedTerm
      | succ k =>
          have hkTable : k < Ntable := by omega
          have hsucc :
              eval pMI (Nat.succ k) (miRoot encodedRules encodedTerm) =
                eval pMI k (miRootTable encodedRules encodedTerm) := by
            simp only [eval, hdispatch]
          rw [hsucc]
          exact htableActive k hkTable
  | none =>
      simp only [hcase] at htable ⊢
      obtain ⟨Ntable, htableEval, htableActive⟩ := htable
      have hrootDispatch :
          eval pMI 1 (miRoot encodedRules encodedTerm) =
            miRootTable encodedRules encodedTerm := by
        simp only [eval, hdispatch]
      have htotal := eval_trans_mi 1 Ntable
        (miRoot encodedRules encodedTerm)
        (miRootTable encodedRules encodedTerm)
        MINoRoot
        hrootDispatch htableEval
      refine ⟨1 + Ntable, htotal, ?_⟩
      intro k hk
      cases k with
      | zero =>
          simp only [eval]
          exact RootActiveShape.root encodedRules encodedTerm
      | succ k =>
          have hkTable : k < Ntable := by omega
          have hsucc :
              eval pMI (Nat.succ k) (miRoot encodedRules encodedTerm) =
                eval pMI k (miRootTable encodedRules encodedTerm) := by
            simp only [eval, hdispatch]
          rw [hsucc]
          exact htableActive k hkTable

theorem miRoot_source_raw_active_sim_var (rws : List RewriteDecl)
    (v : String) (encodedRules : AST)
    (hrules : encRules? rws = some encodedRules) :
    match rootBaseStep? rws (.var (.base v)) with
    | some out =>
        ∃ (rawNext encodedOut : AST) (rootFuel substFuel : Nat),
          encAST? out = some encodedOut ∧
          eval pMI rootFuel (miRoot encodedRules (MIVar v)) =
            MIRootStep rawNext ∧
          (∀ k, k < rootFuel →
            RootActiveShape (eval pMI k (miRoot encodedRules (MIVar v)))) ∧
          eval pMI substFuel rawNext = encodedOut ∧
          IsNormal pMI encodedOut
    | none =>
        ∃ rootFuel,
          eval pMI rootFuel (miRoot encodedRules (MIVar v)) = MINoRoot ∧
          ∀ k, k < rootFuel →
            RootActiveShape (eval pMI k (miRoot encodedRules (MIVar v))) :=
  miRoot_eval_of_rootTable_source_raw_active_sim rws (.var (.base v))
    encodedRules (MIVar v) hrules rfl
    (os_miRoot_default_var encodedRules v)

theorem miRoot_source_raw_active_sim_var_payload (rws : List RewriteDecl)
    (v : String) (encodedRules : AST)
    (hrules : encRules? rws = some encodedRules) :
    match rootBaseStep? rws (.var (.base v)) with
    | some out =>
        ∃ (rawNext encodedOut : AST) (rootFuel substFuel : Nat),
          encAST? out = some encodedOut ∧
          eval pMI rootFuel (miRoot encodedRules (MIVar v)) =
            MIRootStep rawNext ∧
          (∀ k, k < rootFuel →
            RootActiveShape (eval pMI k (miRoot encodedRules (MIVar v)))) ∧
          eval pMI substFuel rawNext = encodedOut ∧
          IsNormal pMI encodedOut ∧
          RawTermPayload rawNext encodedOut
    | none =>
        ∃ rootFuel,
          eval pMI rootFuel (miRoot encodedRules (MIVar v)) = MINoRoot ∧
          ∀ k, k < rootFuel →
            RootActiveShape (eval pMI k (miRoot encodedRules (MIVar v))) :=
  miRoot_eval_of_rootTable_source_raw_active_sim_payload rws
    (.var (.base v)) encodedRules (MIVar v) hrules rfl
    (os_miRoot_default_var encodedRules v)

theorem miRoot_source_raw_active_sim_sym (rws : List RewriteDecl)
    (s : String) (encodedRules : AST)
    (hrules : encRules? rws = some encodedRules) :
    match rootBaseStep? rws (.sexp (.id s) []) with
    | some out =>
        ∃ (rawNext encodedOut : AST) (rootFuel substFuel : Nat),
          encAST? out = some encodedOut ∧
          eval pMI rootFuel (miRoot encodedRules (MISym s)) =
            MIRootStep rawNext ∧
          (∀ k, k < rootFuel →
            RootActiveShape (eval pMI k (miRoot encodedRules (MISym s)))) ∧
          eval pMI substFuel rawNext = encodedOut ∧
          IsNormal pMI encodedOut
    | none =>
        ∃ rootFuel,
          eval pMI rootFuel (miRoot encodedRules (MISym s)) = MINoRoot ∧
          ∀ k, k < rootFuel →
            RootActiveShape (eval pMI k (miRoot encodedRules (MISym s))) :=
  miRoot_eval_of_rootTable_source_raw_active_sim rws (.sexp (.id s) [])
    encodedRules (MISym s) hrules rfl
    (os_miRoot_default_sym encodedRules s)

theorem miRoot_source_raw_active_sim_sym_payload (rws : List RewriteDecl)
    (s : String) (encodedRules : AST)
    (hrules : encRules? rws = some encodedRules) :
    match rootBaseStep? rws (.sexp (.id s) []) with
    | some out =>
        ∃ (rawNext encodedOut : AST) (rootFuel substFuel : Nat),
          encAST? out = some encodedOut ∧
          eval pMI rootFuel (miRoot encodedRules (MISym s)) =
            MIRootStep rawNext ∧
          (∀ k, k < rootFuel →
            RootActiveShape (eval pMI k (miRoot encodedRules (MISym s)))) ∧
          eval pMI substFuel rawNext = encodedOut ∧
          IsNormal pMI encodedOut ∧
          RawTermPayload rawNext encodedOut
    | none =>
        ∃ rootFuel,
          eval pMI rootFuel (miRoot encodedRules (MISym s)) = MINoRoot ∧
          ∀ k, k < rootFuel →
            RootActiveShape (eval pMI k (miRoot encodedRules (MISym s))) :=
  miRoot_eval_of_rootTable_source_raw_active_sim_payload rws
    (.sexp (.id s) []) encodedRules (MISym s) hrules rfl
    (os_miRoot_default_sym encodedRules s)

theorem miRoot_source_raw_active_sim_app_head_ne (rws : List RewriteDecl)
    (headName : String) (a : AST) (rest : List AST)
    (encodedRules encodedArgs : AST)
    (hrules : encRules? rws = some encodedRules)
    (hargs : encASTList? (a :: rest) = some encodedArgs)
    (hhead : (headName == "match") = false) :
    match rootBaseStep? rws (.sexp (.id headName) (a :: rest)) with
    | some out =>
        ∃ (rawNext encodedOut : AST) (rootFuel substFuel : Nat),
          encAST? out = some encodedOut ∧
          eval pMI rootFuel
              (miRoot encodedRules (MIApp headName encodedArgs)) =
            MIRootStep rawNext ∧
          (∀ k, k < rootFuel →
            RootActiveShape
              (eval pMI k
                (miRoot encodedRules (MIApp headName encodedArgs)))) ∧
          eval pMI substFuel rawNext = encodedOut ∧
          IsNormal pMI encodedOut
    | none =>
        ∃ rootFuel,
          eval pMI rootFuel
              (miRoot encodedRules (MIApp headName encodedArgs)) =
            MINoRoot ∧
          ∀ k, k < rootFuel →
            RootActiveShape
              (eval pMI k
                (miRoot encodedRules (MIApp headName encodedArgs))) := by
  have hterm :
      encAST? (.sexp (.id headName) (a :: rest)) =
        some (MIApp headName encodedArgs) := by
    simp only [encAST?, hargs]
  exact miRoot_eval_of_rootTable_source_raw_active_sim rws
    (.sexp (.id headName) (a :: rest)) encodedRules
    (MIApp headName encodedArgs) hrules hterm
    (os_miRoot_default_app_head_ne encodedRules encodedArgs headName hhead)

theorem miRoot_source_raw_active_sim_app_head_ne_payload
    (rws : List RewriteDecl)
    (headName : String) (a : AST) (rest : List AST)
    (encodedRules encodedArgs : AST)
    (hrules : encRules? rws = some encodedRules)
    (hargs : encASTList? (a :: rest) = some encodedArgs)
    (hhead : (headName == "match") = false) :
    match rootBaseStep? rws (.sexp (.id headName) (a :: rest)) with
    | some out =>
        ∃ (rawNext encodedOut : AST) (rootFuel substFuel : Nat),
          encAST? out = some encodedOut ∧
          eval pMI rootFuel
              (miRoot encodedRules (MIApp headName encodedArgs)) =
            MIRootStep rawNext ∧
          (∀ k, k < rootFuel →
            RootActiveShape
              (eval pMI k
                (miRoot encodedRules (MIApp headName encodedArgs)))) ∧
          eval pMI substFuel rawNext = encodedOut ∧
          IsNormal pMI encodedOut ∧
          RawTermPayload rawNext encodedOut
    | none =>
        ∃ rootFuel,
          eval pMI rootFuel
              (miRoot encodedRules (MIApp headName encodedArgs)) =
            MINoRoot ∧
          ∀ k, k < rootFuel →
            RootActiveShape
              (eval pMI k
                (miRoot encodedRules (MIApp headName encodedArgs))) := by
  have hterm :
      encAST? (.sexp (.id headName) (a :: rest)) =
        some (MIApp headName encodedArgs) := by
    simp only [encAST?, hargs]
  exact miRoot_eval_of_rootTable_source_raw_active_sim_payload rws
    (.sexp (.id headName) (a :: rest)) encodedRules
    (MIApp headName encodedArgs) hrules hterm
    (os_miRoot_default_app_head_ne encodedRules encodedArgs headName hhead)

theorem miStepRootK_eval_of_root_active_mivar (rules next : AST) (v : String)
    (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MIVar v)) = MIRootStep next)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIVar v)))) :
    ∃ N,
      eval pMI N (miStepRootK rules (MIVar v) (miRoot rules (MIVar v))) =
        MIStep next := by
  let F : AST → AST := fun z => miStepRootK rules (MIVar v) z
  obtain ⟨Mroot, hrootCtx⟩ :=
    cong_eval_root_active_fuel_mi F
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_mivar rules z z' v
          hrules hactiveStep hstep)
      rootFuel hroot hactive
  have hfire : eval pMI 1 (F (MIRootStep next)) = MIStep next := by
    simp only [F, eval, os_miStepRootK_root_step]
  have htotal := eval_trans_mi Mroot 1
    (miStepRootK rules (MIVar v) (miRoot rules (MIVar v)))
    (F (MIRootStep next))
    (MIStep next)
    hrootCtx hfire
  exact ⟨Mroot + 1, htotal⟩

theorem miStepRootK_eval_of_root_active_misym (rules next : AST) (s : String)
    (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MISym s)) = MIRootStep next)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MISym s)))) :
    ∃ N,
      eval pMI N (miStepRootK rules (MISym s) (miRoot rules (MISym s))) =
        MIStep next := by
  let F : AST → AST := fun z => miStepRootK rules (MISym s) z
  obtain ⟨Mroot, hrootCtx⟩ :=
    cong_eval_root_active_fuel_mi F
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_misym rules z z' s
          hrules hactiveStep hstep)
      rootFuel hroot hactive
  have hfire : eval pMI 1 (F (MIRootStep next)) = MIStep next := by
    simp only [F, eval, os_miStepRootK_root_step]
  have htotal := eval_trans_mi Mroot 1
    (miStepRootK rules (MISym s) (miRoot rules (MISym s)))
    (F (MIRootStep next))
    (MIStep next)
    hrootCtx hfire
  exact ⟨Mroot + 1, htotal⟩

theorem miStepRootK_eval_of_root_active_miapp (rules args next : AST)
    (h : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules) (hargs : IsNormal pMI args)
    (hroot : eval pMI rootFuel (miRoot rules (MIApp h args)) =
      MIRootStep next)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIApp h args)))) :
    ∃ N,
      eval pMI N
          (miStepRootK rules (MIApp h args) (miRoot rules (MIApp h args))) =
        MIStep next := by
  let F : AST → AST := fun z => miStepRootK rules (MIApp h args) z
  obtain ⟨Mroot, hrootCtx⟩ :=
    cong_eval_root_active_fuel_mi F
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_miapp rules args z z' h
          hrules hargs hactiveStep hstep)
      rootFuel hroot hactive
  have hfire : eval pMI 1 (F (MIRootStep next)) = MIStep next := by
    simp only [F, eval, os_miStepRootK_root_step]
  have htotal := eval_trans_mi Mroot 1
    (miStepRootK rules (MIApp h args) (miRoot rules (MIApp h args)))
    (F (MIRootStep next))
    (MIStep next)
    hrootCtx hfire
  exact ⟨Mroot + 1, htotal⟩

theorem miStep_eval_of_root_active_mivar (rules next : AST) (v : String)
    (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MIVar v)) = MIRootStep next)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIVar v)))) :
    ∃ N, eval pMI N (miStep rules (MIVar v)) = MIStep next := by
  obtain ⟨Mroot, hrootK⟩ :=
    miStepRootK_eval_of_root_active_mivar rules next v rootFuel
      hrules hroot hactive
  have hdispatch :
      eval pMI 1 (miStep rules (MIVar v)) =
        miStepRootK rules (MIVar v) (miRoot rules (MIVar v)) := by
    simp only [eval, os_miStep_dispatch]
  have htotal := eval_trans_mi 1 Mroot
    (miStep rules (MIVar v))
    (miStepRootK rules (MIVar v) (miRoot rules (MIVar v)))
    (MIStep next)
    hdispatch hrootK
  exact ⟨1 + Mroot, htotal⟩

theorem miStep_eval_of_root_active_misym (rules next : AST) (s : String)
    (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MISym s)) = MIRootStep next)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MISym s)))) :
    ∃ N, eval pMI N (miStep rules (MISym s)) = MIStep next := by
  obtain ⟨Mroot, hrootK⟩ :=
    miStepRootK_eval_of_root_active_misym rules next s rootFuel
      hrules hroot hactive
  have hdispatch :
      eval pMI 1 (miStep rules (MISym s)) =
        miStepRootK rules (MISym s) (miRoot rules (MISym s)) := by
    simp only [eval, os_miStep_dispatch]
  have htotal := eval_trans_mi 1 Mroot
    (miStep rules (MISym s))
    (miStepRootK rules (MISym s) (miRoot rules (MISym s)))
    (MIStep next)
    hdispatch hrootK
  exact ⟨1 + Mroot, htotal⟩

theorem miStep_eval_of_root_active_miapp (rules args next : AST)
    (h : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules) (hargs : IsNormal pMI args)
    (hroot : eval pMI rootFuel (miRoot rules (MIApp h args)) =
      MIRootStep next)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIApp h args)))) :
    ∃ N, eval pMI N (miStep rules (MIApp h args)) = MIStep next := by
  obtain ⟨Mroot, hrootK⟩ :=
    miStepRootK_eval_of_root_active_miapp rules args next h rootFuel
      hrules hargs hroot hactive
  have hdispatch :
      eval pMI 1 (miStep rules (MIApp h args)) =
        miStepRootK rules (MIApp h args) (miRoot rules (MIApp h args)) := by
    simp only [eval, os_miStep_dispatch]
  have htotal := eval_trans_mi 1 Mroot
    (miStep rules (MIApp h args))
    (miStepRootK rules (MIApp h args) (miRoot rules (MIApp h args)))
    (MIStep next)
    hdispatch hrootK
  exact ⟨1 + Mroot, htotal⟩

theorem miStepRootK_eval_of_root_active_mivar_with_guard
    (rules next : AST) (v : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MIVar v)) =
      MIRootStep next)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIVar v)))) :
    ∃ N,
      eval pMI N (miStepRootK rules (MIVar v) (miRoot rules (MIVar v))) =
        MIStep next ∧
      ∀ k, k < N →
        StepActiveShape
          (eval pMI k
            (miStepRootK rules (MIVar v) (miRoot rules (MIVar v)))) := by
  let F : AST → AST := fun z => miStepRootK rules (MIVar v) z
  obtain ⟨Mroot, hrootCtx, hrootCtxActive⟩ :=
    cong_eval_root_to_step_active_with_guard_mi F
      (fun s _hs => StepActiveShape.rootK rules (MIVar v) s)
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_mivar rules z z' v
          hrules hactiveStep hstep)
      rootFuel hroot hactive
  have hfire : eval pMI 1 (F (MIRootStep next)) = MIStep next := by
    simp only [F, eval, os_miStepRootK_root_step]
  have htotal := eval_trans_mi Mroot 1
    (miStepRootK rules (MIVar v) (miRoot rules (MIVar v)))
    (F (MIRootStep next))
    (MIStep next)
    hrootCtx hfire
  refine ⟨Mroot + 1, htotal, ?_⟩
  intro k hk
  by_cases hlt : k < Mroot
  · exact hrootCtxActive k hlt
  · have hk_ge : Mroot ≤ k := Nat.le_of_not_gt hlt
    have hk_le : k ≤ Mroot := Nat.le_of_lt_succ hk
    have hk_eq : k = Mroot := Nat.le_antisymm hk_le hk_ge
    subst k
    change StepActiveShape (eval pMI Mroot (F (miRoot rules (MIVar v))))
    rw [hrootCtx]
    exact StepActiveShape.rootK rules (MIVar v) (MIRootStep next)

theorem miStepRootK_eval_of_root_active_misym_with_guard
    (rules next : AST) (s : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MISym s)) =
      MIRootStep next)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MISym s)))) :
    ∃ N,
      eval pMI N (miStepRootK rules (MISym s) (miRoot rules (MISym s))) =
        MIStep next ∧
      ∀ k, k < N →
        StepActiveShape
          (eval pMI k
            (miStepRootK rules (MISym s) (miRoot rules (MISym s)))) := by
  let F : AST → AST := fun z => miStepRootK rules (MISym s) z
  obtain ⟨Mroot, hrootCtx, hrootCtxActive⟩ :=
    cong_eval_root_to_step_active_with_guard_mi F
      (fun z _hz => StepActiveShape.rootK rules (MISym s) z)
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_misym rules z z' s
          hrules hactiveStep hstep)
      rootFuel hroot hactive
  have hfire : eval pMI 1 (F (MIRootStep next)) = MIStep next := by
    simp only [F, eval, os_miStepRootK_root_step]
  have htotal := eval_trans_mi Mroot 1
    (miStepRootK rules (MISym s) (miRoot rules (MISym s)))
    (F (MIRootStep next))
    (MIStep next)
    hrootCtx hfire
  refine ⟨Mroot + 1, htotal, ?_⟩
  intro k hk
  by_cases hlt : k < Mroot
  · exact hrootCtxActive k hlt
  · have hk_ge : Mroot ≤ k := Nat.le_of_not_gt hlt
    have hk_le : k ≤ Mroot := Nat.le_of_lt_succ hk
    have hk_eq : k = Mroot := Nat.le_antisymm hk_le hk_ge
    subst k
    change StepActiveShape (eval pMI Mroot (F (miRoot rules (MISym s))))
    rw [hrootCtx]
    exact StepActiveShape.rootK rules (MISym s) (MIRootStep next)

theorem miStepRootK_eval_of_root_active_miapp_with_guard
    (rules args next : AST) (h : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules) (hargs : IsNormal pMI args)
    (hroot : eval pMI rootFuel (miRoot rules (MIApp h args)) =
      MIRootStep next)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIApp h args)))) :
    ∃ N,
      eval pMI N
          (miStepRootK rules (MIApp h args) (miRoot rules (MIApp h args))) =
        MIStep next ∧
      ∀ k, k < N →
        StepActiveShape
          (eval pMI k
            (miStepRootK rules (MIApp h args) (miRoot rules (MIApp h args)))) := by
  let F : AST → AST := fun z => miStepRootK rules (MIApp h args) z
  obtain ⟨Mroot, hrootCtx, hrootCtxActive⟩ :=
    cong_eval_root_to_step_active_with_guard_mi F
      (fun z _hz => StepActiveShape.rootK rules (MIApp h args) z)
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_miapp rules args z z' h
          hrules hargs hactiveStep hstep)
      rootFuel hroot hactive
  have hfire : eval pMI 1 (F (MIRootStep next)) = MIStep next := by
    simp only [F, eval, os_miStepRootK_root_step]
  have htotal := eval_trans_mi Mroot 1
    (miStepRootK rules (MIApp h args) (miRoot rules (MIApp h args)))
    (F (MIRootStep next))
    (MIStep next)
    hrootCtx hfire
  refine ⟨Mroot + 1, htotal, ?_⟩
  intro k hk
  by_cases hlt : k < Mroot
  · exact hrootCtxActive k hlt
  · have hk_ge : Mroot ≤ k := Nat.le_of_not_gt hlt
    have hk_le : k ≤ Mroot := Nat.le_of_lt_succ hk
    have hk_eq : k = Mroot := Nat.le_antisymm hk_le hk_ge
    subst k
    change
      StepActiveShape (eval pMI Mroot (F (miRoot rules (MIApp h args))))
    rw [hrootCtx]
    exact StepActiveShape.rootK rules (MIApp h args) (MIRootStep next)

theorem miStep_eval_of_rootK_active_with_dispatch
    (rules term out : AST) (rootKFuel : Nat)
    (hrootK :
      eval pMI rootKFuel (miStepRootK rules term (miRoot rules term)) = out)
    (hrootKActive : ∀ k, k < rootKFuel →
      StepActiveShape
        (eval pMI k (miStepRootK rules term (miRoot rules term)))) :
    ∃ N,
      eval pMI N (miStep rules term) = out ∧
      ∀ k, k < N → StepActiveShape (eval pMI k (miStep rules term)) := by
  have hdispatch :
      eval pMI 1 (miStep rules term) =
        miStepRootK rules term (miRoot rules term) := by
    simp only [eval, os_miStep_dispatch]
  have htotal := eval_trans_mi 1 rootKFuel
    (miStep rules term)
    (miStepRootK rules term (miRoot rules term))
    out
    hdispatch hrootK
  exact ⟨1 + rootKFuel, htotal,
    step_active_append_mi 1 rootKFuel hdispatch
      (step_active_fuel_one_mi (StepActiveShape.step rules term))
      hrootKActive⟩

theorem miStep_eval_of_root_active_mivar_with_guard
    (rules next : AST) (v : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MIVar v)) = MIRootStep next)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIVar v)))) :
    ∃ N,
      eval pMI N (miStep rules (MIVar v)) = MIStep next ∧
      ∀ k, k < N → StepActiveShape (eval pMI k (miStep rules (MIVar v))) := by
  obtain ⟨Mroot, hrootK, hrootKActive⟩ :=
    miStepRootK_eval_of_root_active_mivar_with_guard rules next v
      rootFuel hrules hroot hactive
  exact miStep_eval_of_rootK_active_with_dispatch rules (MIVar v)
    (MIStep next) Mroot hrootK hrootKActive

theorem miStep_eval_of_root_active_misym_with_guard
    (rules next : AST) (s : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MISym s)) = MIRootStep next)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MISym s)))) :
    ∃ N,
      eval pMI N (miStep rules (MISym s)) = MIStep next ∧
      ∀ k, k < N → StepActiveShape (eval pMI k (miStep rules (MISym s))) := by
  obtain ⟨Mroot, hrootK, hrootKActive⟩ :=
    miStepRootK_eval_of_root_active_misym_with_guard rules next s
      rootFuel hrules hroot hactive
  exact miStep_eval_of_rootK_active_with_dispatch rules (MISym s)
    (MIStep next) Mroot hrootK hrootKActive

theorem miStep_eval_of_root_active_miapp_with_guard
    (rules args next : AST) (h : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules) (hargs : IsNormal pMI args)
    (hroot : eval pMI rootFuel (miRoot rules (MIApp h args)) =
      MIRootStep next)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIApp h args)))) :
    ∃ N,
      eval pMI N (miStep rules (MIApp h args)) = MIStep next ∧
      ∀ k, k < N →
        StepActiveShape (eval pMI k (miStep rules (MIApp h args))) := by
  obtain ⟨Mroot, hrootK, hrootKActive⟩ :=
    miStepRootK_eval_of_root_active_miapp_with_guard rules args next h
      rootFuel hrules hargs hroot hactive
  exact miStep_eval_of_rootK_active_with_dispatch rules (MIApp h args)
    (MIStep next) Mroot hrootK hrootKActive

theorem miStep_eval_of_root_active_normalized_mivar
    (rules rawNext encodedOut : AST) (v : String)
    (rootFuel substFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MIVar v)) =
      MIRootStep rawNext)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIVar v))))
    (hsubst : eval pMI substFuel rawNext = encodedOut)
    (hout : IsNormal pMI encodedOut) :
    ∃ N, eval pMI N (miStep rules (MIVar v)) = MIStep encodedOut := by
  obtain ⟨Nstep, hstep⟩ :=
    miStep_eval_of_root_active_mivar rules rawNext v rootFuel
      hrules hroot hactive
  obtain ⟨Msubst, hsubstCtx⟩ :=
    cong_eval_mi (fun z => MIStep z)
      (fun s s' hstep => os_MIStep_arg_step s s' hstep)
      substFuel hsubst hout
  have htotal := eval_trans_mi Nstep Msubst
    (miStep rules (MIVar v))
    (MIStep rawNext)
    (MIStep encodedOut)
    hstep hsubstCtx
  exact ⟨Nstep + Msubst, htotal⟩

theorem miStep_eval_of_root_active_normalized_misym
    (rules rawNext encodedOut : AST) (s : String)
    (rootFuel substFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MISym s)) =
      MIRootStep rawNext)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MISym s))))
    (hsubst : eval pMI substFuel rawNext = encodedOut)
    (hout : IsNormal pMI encodedOut) :
    ∃ N, eval pMI N (miStep rules (MISym s)) = MIStep encodedOut := by
  obtain ⟨Nstep, hstep⟩ :=
    miStep_eval_of_root_active_misym rules rawNext s rootFuel
      hrules hroot hactive
  obtain ⟨Msubst, hsubstCtx⟩ :=
    cong_eval_mi (fun z => MIStep z)
      (fun s s' hstep => os_MIStep_arg_step s s' hstep)
      substFuel hsubst hout
  have htotal := eval_trans_mi Nstep Msubst
    (miStep rules (MISym s))
    (MIStep rawNext)
    (MIStep encodedOut)
    hstep hsubstCtx
  exact ⟨Nstep + Msubst, htotal⟩

theorem miStep_eval_of_root_active_normalized_miapp
    (rules args rawNext encodedOut : AST) (h : String)
    (rootFuel substFuel : Nat)
    (hrules : IsNormal pMI rules) (hargs : IsNormal pMI args)
    (hroot : eval pMI rootFuel (miRoot rules (MIApp h args)) =
      MIRootStep rawNext)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIApp h args))))
    (hsubst : eval pMI substFuel rawNext = encodedOut)
    (hout : IsNormal pMI encodedOut) :
    ∃ N, eval pMI N (miStep rules (MIApp h args)) = MIStep encodedOut := by
  obtain ⟨Nstep, hstep⟩ :=
    miStep_eval_of_root_active_miapp rules args rawNext h rootFuel
      hrules hargs hroot hactive
  obtain ⟨Msubst, hsubstCtx⟩ :=
    cong_eval_mi (fun z => MIStep z)
      (fun s s' hstep => os_MIStep_arg_step s s' hstep)
      substFuel hsubst hout
  have htotal := eval_trans_mi Nstep Msubst
    (miStep rules (MIApp h args))
    (MIStep rawNext)
    (MIStep encodedOut)
    hstep hsubstCtx
  exact ⟨Nstep + Msubst, htotal⟩

theorem miStepRootK_eval_of_root_none_active_mivar
    (rules : AST) (v : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MIVar v)) = MINoRoot)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIVar v)))) :
    ∃ N,
      eval pMI N (miStepRootK rules (MIVar v) (miRoot rules (MIVar v))) =
        MINoStep := by
  let F : AST → AST := fun z => miStepRootK rules (MIVar v) z
  obtain ⟨Mroot, hrootCtx⟩ :=
    cong_eval_root_active_fuel_mi F
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_mivar rules z z' v
          hrules hactiveStep hstep)
      rootFuel hroot hactive
  have hfire : eval pMI 1 (F MINoRoot) = MINoStep := by
    simp only [F, eval, os_miStepRootK_var_no_root]
  have htotal := eval_trans_mi Mroot 1
    (miStepRootK rules (MIVar v) (miRoot rules (MIVar v)))
    (F MINoRoot)
    MINoStep
    hrootCtx hfire
  exact ⟨Mroot + 1, htotal⟩

theorem miStepRootK_eval_of_root_none_active_misym
    (rules : AST) (s : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MISym s)) = MINoRoot)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MISym s)))) :
    ∃ N,
      eval pMI N (miStepRootK rules (MISym s) (miRoot rules (MISym s))) =
        MINoStep := by
  let F : AST → AST := fun z => miStepRootK rules (MISym s) z
  obtain ⟨Mroot, hrootCtx⟩ :=
    cong_eval_root_active_fuel_mi F
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_misym rules z z' s
          hrules hactiveStep hstep)
      rootFuel hroot hactive
  have hfire : eval pMI 1 (F MINoRoot) = MINoStep := by
    simp only [F, eval, os_miStepRootK_sym_no_root]
  have htotal := eval_trans_mi Mroot 1
    (miStepRootK rules (MISym s) (miRoot rules (MISym s)))
    (F MINoRoot)
    MINoStep
    hrootCtx hfire
  exact ⟨Mroot + 1, htotal⟩

theorem miStepRootK_eval_of_root_none_active_miapp_args_step
    (rules args argsOut : AST) (h : String)
    (rootFuel argsFuel : Nat)
    (hrules : IsNormal pMI rules) (hargsNorm : IsNormal pMI args)
    (hroot : eval pMI rootFuel (miRoot rules (MIApp h args)) = MINoRoot)
    (hrootActive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIApp h args))))
    (hargs : eval pMI argsFuel (miStepArgs rules args) =
      MIArgsStep argsOut)
    (hargsActive : ∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs rules args))) :
    ∃ N,
      eval pMI N
          (miStepRootK rules (MIApp h args)
            (miRoot rules (MIApp h args))) =
        MIStep (MIApp h argsOut) := by
  let F : AST → AST := fun z => miStepRootK rules (MIApp h args) z
  obtain ⟨Mroot, hrootCtx⟩ :=
    cong_eval_root_active_fuel_mi F
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_miapp rules args z z' h
          hrules hargsNorm hactiveStep hstep)
      rootFuel hroot hrootActive
  have hfire :
      eval pMI 1 (F MINoRoot) =
        miStepAppK (con0 h) (miStepArgs rules args) := by
    simp only [F, eval, os_miStepRootK_app_no_root]
  obtain ⟨Mapp, happ⟩ :=
    miStepAppK_eval_of_args_active_step_named h (miStepArgs rules args)
      argsOut argsFuel hargs hargsActive
  have htail := eval_trans_mi 1 Mapp
    (F MINoRoot)
    (miStepAppK (con0 h) (miStepArgs rules args))
    (MIStep (MIApp h argsOut))
    hfire happ
  have htotal := eval_trans_mi Mroot (1 + Mapp)
    (miStepRootK rules (MIApp h args) (miRoot rules (MIApp h args)))
    (F MINoRoot)
    (MIStep (MIApp h argsOut))
    hrootCtx htail
  exact ⟨Mroot + (1 + Mapp), htotal⟩

theorem miStepRootK_eval_of_root_none_active_miapp_args_none
    (rules args : AST) (h : String)
    (rootFuel argsFuel : Nat)
    (hrules : IsNormal pMI rules) (hargsNorm : IsNormal pMI args)
    (hroot : eval pMI rootFuel (miRoot rules (MIApp h args)) = MINoRoot)
    (hrootActive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIApp h args))))
    (hargs : eval pMI argsFuel (miStepArgs rules args) = MINoArgsStep)
    (hargsActive : ∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs rules args))) :
    ∃ N,
      eval pMI N
          (miStepRootK rules (MIApp h args)
            (miRoot rules (MIApp h args))) =
        MINoStep := by
  let F : AST → AST := fun z => miStepRootK rules (MIApp h args) z
  obtain ⟨Mroot, hrootCtx⟩ :=
    cong_eval_root_active_fuel_mi F
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_miapp rules args z z' h
          hrules hargsNorm hactiveStep hstep)
      rootFuel hroot hrootActive
  have hfire :
      eval pMI 1 (F MINoRoot) =
        miStepAppK (con0 h) (miStepArgs rules args) := by
    simp only [F, eval, os_miStepRootK_app_no_root]
  obtain ⟨Mapp, happ⟩ :=
    miStepAppK_eval_of_args_active_none_named h (miStepArgs rules args)
      argsFuel hargs hargsActive
  have htail := eval_trans_mi 1 Mapp
    (F MINoRoot)
    (miStepAppK (con0 h) (miStepArgs rules args))
    MINoStep
    hfire happ
  have htotal := eval_trans_mi Mroot (1 + Mapp)
    (miStepRootK rules (MIApp h args) (miRoot rules (MIApp h args)))
    (F MINoRoot)
    MINoStep
    hrootCtx htail
  exact ⟨Mroot + (1 + Mapp), htotal⟩

theorem miStep_eval_of_root_none_active_mivar
    (rules : AST) (v : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MIVar v)) = MINoRoot)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIVar v)))) :
    ∃ N, eval pMI N (miStep rules (MIVar v)) = MINoStep := by
  obtain ⟨Mroot, hrootK⟩ :=
    miStepRootK_eval_of_root_none_active_mivar rules v rootFuel
      hrules hroot hactive
  have hdispatch :
      eval pMI 1 (miStep rules (MIVar v)) =
        miStepRootK rules (MIVar v) (miRoot rules (MIVar v)) := by
    simp only [eval, os_miStep_dispatch]
  have htotal := eval_trans_mi 1 Mroot
    (miStep rules (MIVar v))
    (miStepRootK rules (MIVar v) (miRoot rules (MIVar v)))
    MINoStep
    hdispatch hrootK
  exact ⟨1 + Mroot, htotal⟩

theorem miStep_eval_of_root_none_active_misym
    (rules : AST) (s : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MISym s)) = MINoRoot)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MISym s)))) :
    ∃ N, eval pMI N (miStep rules (MISym s)) = MINoStep := by
  obtain ⟨Mroot, hrootK⟩ :=
    miStepRootK_eval_of_root_none_active_misym rules s rootFuel
      hrules hroot hactive
  have hdispatch :
      eval pMI 1 (miStep rules (MISym s)) =
        miStepRootK rules (MISym s) (miRoot rules (MISym s)) := by
    simp only [eval, os_miStep_dispatch]
  have htotal := eval_trans_mi 1 Mroot
    (miStep rules (MISym s))
    (miStepRootK rules (MISym s) (miRoot rules (MISym s)))
    MINoStep
    hdispatch hrootK
  exact ⟨1 + Mroot, htotal⟩

theorem miStep_eval_of_root_none_active_miapp_args_step
    (rules args argsOut : AST) (h : String)
    (rootFuel argsFuel : Nat)
    (hrules : IsNormal pMI rules) (hargsNorm : IsNormal pMI args)
    (hroot : eval pMI rootFuel (miRoot rules (MIApp h args)) = MINoRoot)
    (hrootActive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIApp h args))))
    (hargs : eval pMI argsFuel (miStepArgs rules args) =
      MIArgsStep argsOut)
    (hargsActive : ∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs rules args))) :
    ∃ N, eval pMI N (miStep rules (MIApp h args)) =
      MIStep (MIApp h argsOut) := by
  obtain ⟨Mroot, hrootK⟩ :=
    miStepRootK_eval_of_root_none_active_miapp_args_step
      rules args argsOut h rootFuel argsFuel hrules hargsNorm
      hroot hrootActive hargs hargsActive
  have hdispatch :
      eval pMI 1 (miStep rules (MIApp h args)) =
        miStepRootK rules (MIApp h args) (miRoot rules (MIApp h args)) := by
    simp only [eval, os_miStep_dispatch]
  have htotal := eval_trans_mi 1 Mroot
    (miStep rules (MIApp h args))
    (miStepRootK rules (MIApp h args) (miRoot rules (MIApp h args)))
    (MIStep (MIApp h argsOut))
    hdispatch hrootK
  exact ⟨1 + Mroot, htotal⟩

theorem miStep_eval_of_root_none_active_miapp_args_none
    (rules args : AST) (h : String)
    (rootFuel argsFuel : Nat)
    (hrules : IsNormal pMI rules) (hargsNorm : IsNormal pMI args)
    (hroot : eval pMI rootFuel (miRoot rules (MIApp h args)) = MINoRoot)
    (hrootActive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIApp h args))))
    (hargs : eval pMI argsFuel (miStepArgs rules args) = MINoArgsStep)
    (hargsActive : ∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs rules args))) :
    ∃ N, eval pMI N (miStep rules (MIApp h args)) = MINoStep := by
  obtain ⟨Mroot, hrootK⟩ :=
    miStepRootK_eval_of_root_none_active_miapp_args_none
      rules args h rootFuel argsFuel hrules hargsNorm
      hroot hrootActive hargs hargsActive
  have hdispatch :
      eval pMI 1 (miStep rules (MIApp h args)) =
        miStepRootK rules (MIApp h args) (miRoot rules (MIApp h args)) := by
    simp only [eval, os_miStep_dispatch]
  have htotal := eval_trans_mi 1 Mroot
    (miStep rules (MIApp h args))
    (miStepRootK rules (MIApp h args) (miRoot rules (MIApp h args)))
    MINoStep
    hdispatch hrootK
  exact ⟨1 + Mroot, htotal⟩

theorem miStepRootK_eval_of_root_none_active_mivar_with_guard
    (rules : AST) (v : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MIVar v)) = MINoRoot)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIVar v)))) :
    ∃ N,
      eval pMI N (miStepRootK rules (MIVar v) (miRoot rules (MIVar v))) =
        MINoStep ∧
      ∀ k, k < N →
        StepActiveShape
          (eval pMI k
            (miStepRootK rules (MIVar v) (miRoot rules (MIVar v)))) := by
  let F : AST → AST := fun z => miStepRootK rules (MIVar v) z
  obtain ⟨Mroot, hrootCtx, hrootCtxActive⟩ :=
    cong_eval_root_to_step_active_with_guard_mi F
      (fun z _hz => StepActiveShape.rootK rules (MIVar v) z)
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_mivar rules z z' v
          hrules hactiveStep hstep)
      rootFuel hroot hactive
  have hfire : eval pMI 1 (F MINoRoot) = MINoStep := by
    simp only [F, eval, os_miStepRootK_var_no_root]
  have htotal := eval_trans_mi Mroot 1
    (miStepRootK rules (MIVar v) (miRoot rules (MIVar v)))
    (F MINoRoot)
    MINoStep
    hrootCtx hfire
  refine ⟨Mroot + 1, htotal, ?_⟩
  intro k hk
  by_cases hlt : k < Mroot
  · exact hrootCtxActive k hlt
  · have hk_ge : Mroot ≤ k := Nat.le_of_not_gt hlt
    have hk_le : k ≤ Mroot := Nat.le_of_lt_succ hk
    have hk_eq : k = Mroot := Nat.le_antisymm hk_le hk_ge
    subst k
    change
      StepActiveShape
        (eval pMI Mroot
          (F (miRoot rules (MIVar v))))
    rw [hrootCtx]
    exact StepActiveShape.rootK rules (MIVar v) MINoRoot

theorem miStepRootK_eval_of_root_none_active_misym_with_guard
    (rules : AST) (s : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MISym s)) = MINoRoot)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MISym s)))) :
    ∃ N,
      eval pMI N (miStepRootK rules (MISym s) (miRoot rules (MISym s))) =
        MINoStep ∧
      ∀ k, k < N →
        StepActiveShape
          (eval pMI k
            (miStepRootK rules (MISym s) (miRoot rules (MISym s)))) := by
  let F : AST → AST := fun z => miStepRootK rules (MISym s) z
  obtain ⟨Mroot, hrootCtx, hrootCtxActive⟩ :=
    cong_eval_root_to_step_active_with_guard_mi F
      (fun z _hz => StepActiveShape.rootK rules (MISym s) z)
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_misym rules z z' s
          hrules hactiveStep hstep)
      rootFuel hroot hactive
  have hfire : eval pMI 1 (F MINoRoot) = MINoStep := by
    simp only [F, eval, os_miStepRootK_sym_no_root]
  have htotal := eval_trans_mi Mroot 1
    (miStepRootK rules (MISym s) (miRoot rules (MISym s)))
    (F MINoRoot)
    MINoStep
    hrootCtx hfire
  refine ⟨Mroot + 1, htotal, ?_⟩
  intro k hk
  by_cases hlt : k < Mroot
  · exact hrootCtxActive k hlt
  · have hk_ge : Mroot ≤ k := Nat.le_of_not_gt hlt
    have hk_le : k ≤ Mroot := Nat.le_of_lt_succ hk
    have hk_eq : k = Mroot := Nat.le_antisymm hk_le hk_ge
    subst k
    change
      StepActiveShape
        (eval pMI Mroot
          (F (miRoot rules (MISym s))))
    rw [hrootCtx]
    exact StepActiveShape.rootK rules (MISym s) MINoRoot

theorem miStepRootK_eval_of_root_none_active_miapp_args_step_with_guard
    (rules args argsOut : AST) (h : String)
    (rootFuel argsFuel : Nat)
    (hrules : IsNormal pMI rules) (hargsNorm : IsNormal pMI args)
    (hroot : eval pMI rootFuel (miRoot rules (MIApp h args)) = MINoRoot)
    (hrootActive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIApp h args))))
    (hargs : eval pMI argsFuel (miStepArgs rules args) =
      MIArgsStep argsOut)
    (hargsActive : ∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs rules args))) :
    ∃ N,
      eval pMI N
          (miStepRootK rules (MIApp h args)
            (miRoot rules (MIApp h args))) =
        MIStep (MIApp h argsOut) ∧
      ∀ k, k < N →
        StepActiveShape
          (eval pMI k
            (miStepRootK rules (MIApp h args)
              (miRoot rules (MIApp h args)))) := by
  let F : AST → AST := fun z => miStepRootK rules (MIApp h args) z
  let G : AST := miStepAppK (con0 h) (miStepArgs rules args)
  obtain ⟨Mroot, hrootCtx, hrootCtxActive⟩ :=
    cong_eval_root_to_step_active_with_guard_mi F
      (fun z _hz => StepActiveShape.rootK rules (MIApp h args) z)
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_miapp rules args z z' h
          hrules hargsNorm hactiveStep hstep)
      rootFuel hroot hrootActive
  have hfire : eval pMI 1 (F MINoRoot) = G := by
    simp only [F, G, eval, os_miStepRootK_app_no_root]
  obtain ⟨Mapp, happ, happActive⟩ :=
    miStepAppK_eval_of_args_active_step_named_with_guard h
      (miStepArgs rules args) argsOut argsFuel hargs hargsActive
  have htail := eval_trans_mi 1 Mapp
    (F MINoRoot)
    G
    (MIStep (MIApp h argsOut))
    hfire happ
  have htailActive :
      ∀ k, k < 1 + Mapp →
        StepActiveShape (eval pMI k (F MINoRoot)) := by
    intro k hk
    cases k with
    | zero =>
        simpa only [eval, F] using
          StepActiveShape.rootK rules (MIApp h args) MINoRoot
    | succ k =>
        have hkM : k < Mapp := by
          omega
        have heval :
            eval pMI (Nat.succ k) (F MINoRoot) = eval pMI k G := by
          simp only [F, G, eval, os_miStepRootK_app_no_root]
        rw [heval]
        exact happActive k hkM
  have htotal := eval_trans_mi Mroot (1 + Mapp)
    (miStepRootK rules (MIApp h args) (miRoot rules (MIApp h args)))
    (F MINoRoot)
    (MIStep (MIApp h argsOut))
    hrootCtx htail
  exact ⟨Mroot + (1 + Mapp), htotal,
    step_active_append_mi Mroot (1 + Mapp) hrootCtx
      hrootCtxActive htailActive⟩

theorem miStepRootK_eval_of_root_none_active_miapp_args_none_with_guard
    (rules args : AST) (h : String)
    (rootFuel argsFuel : Nat)
    (hrules : IsNormal pMI rules) (hargsNorm : IsNormal pMI args)
    (hroot : eval pMI rootFuel (miRoot rules (MIApp h args)) = MINoRoot)
    (hrootActive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIApp h args))))
    (hargs : eval pMI argsFuel (miStepArgs rules args) = MINoArgsStep)
    (hargsActive : ∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs rules args))) :
    ∃ N,
      eval pMI N
          (miStepRootK rules (MIApp h args)
            (miRoot rules (MIApp h args))) =
        MINoStep ∧
      ∀ k, k < N →
        StepActiveShape
          (eval pMI k
            (miStepRootK rules (MIApp h args)
              (miRoot rules (MIApp h args)))) := by
  let F : AST → AST := fun z => miStepRootK rules (MIApp h args) z
  let G : AST := miStepAppK (con0 h) (miStepArgs rules args)
  obtain ⟨Mroot, hrootCtx, hrootCtxActive⟩ :=
    cong_eval_root_to_step_active_with_guard_mi F
      (fun z _hz => StepActiveShape.rootK rules (MIApp h args) z)
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_miapp rules args z z' h
          hrules hargsNorm hactiveStep hstep)
      rootFuel hroot hrootActive
  have hfire : eval pMI 1 (F MINoRoot) = G := by
    simp only [F, G, eval, os_miStepRootK_app_no_root]
  obtain ⟨Mapp, happ, happActive⟩ :=
    miStepAppK_eval_of_args_active_none_named_with_guard h
      (miStepArgs rules args) argsFuel hargs hargsActive
  have htail := eval_trans_mi 1 Mapp
    (F MINoRoot)
    G
    MINoStep
    hfire happ
  have htailActive :
      ∀ k, k < 1 + Mapp →
        StepActiveShape (eval pMI k (F MINoRoot)) := by
    intro k hk
    cases k with
    | zero =>
        simpa only [eval, F] using
          StepActiveShape.rootK rules (MIApp h args) MINoRoot
    | succ k =>
        have hkM : k < Mapp := by
          omega
        have heval :
            eval pMI (Nat.succ k) (F MINoRoot) = eval pMI k G := by
          simp only [F, G, eval, os_miStepRootK_app_no_root]
        rw [heval]
        exact happActive k hkM
  have htotal := eval_trans_mi Mroot (1 + Mapp)
    (miStepRootK rules (MIApp h args) (miRoot rules (MIApp h args)))
    (F MINoRoot)
    MINoStep
    hrootCtx htail
  exact ⟨Mroot + (1 + Mapp), htotal,
    step_active_append_mi Mroot (1 + Mapp) hrootCtx
      hrootCtxActive htailActive⟩

theorem miStepRootK_eval_of_any_root_none_active_mivar_with_guard
    (rules root : AST) (v : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel root = MINoRoot)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k root)) :
    ∃ N,
      eval pMI N (miStepRootK rules (MIVar v) root) = MINoStep ∧
      ∀ k, k < N →
        StepActiveShape
          (eval pMI k (miStepRootK rules (MIVar v) root)) := by
  let F : AST → AST := fun z => miStepRootK rules (MIVar v) z
  obtain ⟨Mroot, hrootCtx, hrootCtxActive⟩ :=
    cong_eval_root_to_step_active_with_guard_mi F
      (fun z _hz => StepActiveShape.rootK rules (MIVar v) z)
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_mivar rules z z' v
          hrules hactiveStep hstep)
      rootFuel hroot hactive
  have hfire : eval pMI 1 (F MINoRoot) = MINoStep := by
    simp only [F, eval, os_miStepRootK_var_no_root]
  have htotal := eval_trans_mi Mroot 1
    (miStepRootK rules (MIVar v) root)
    (F MINoRoot)
    MINoStep
    hrootCtx hfire
  refine ⟨Mroot + 1, htotal, ?_⟩
  intro k hk
  by_cases hlt : k < Mroot
  · exact hrootCtxActive k hlt
  · have hk_ge : Mroot ≤ k := Nat.le_of_not_gt hlt
    have hk_le : k ≤ Mroot := Nat.le_of_lt_succ hk
    have hk_eq : k = Mroot := Nat.le_antisymm hk_le hk_ge
    subst k
    change StepActiveShape (eval pMI Mroot (F root))
    rw [hrootCtx]
    exact StepActiveShape.rootK rules (MIVar v) MINoRoot

theorem miStepRootK_eval_of_any_root_none_active_misym_with_guard
    (rules root : AST) (s : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel root = MINoRoot)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k root)) :
    ∃ N,
      eval pMI N (miStepRootK rules (MISym s) root) = MINoStep ∧
      ∀ k, k < N →
        StepActiveShape
          (eval pMI k (miStepRootK rules (MISym s) root)) := by
  let F : AST → AST := fun z => miStepRootK rules (MISym s) z
  obtain ⟨Mroot, hrootCtx, hrootCtxActive⟩ :=
    cong_eval_root_to_step_active_with_guard_mi F
      (fun z _hz => StepActiveShape.rootK rules (MISym s) z)
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_misym rules z z' s
          hrules hactiveStep hstep)
      rootFuel hroot hactive
  have hfire : eval pMI 1 (F MINoRoot) = MINoStep := by
    simp only [F, eval, os_miStepRootK_sym_no_root]
  have htotal := eval_trans_mi Mroot 1
    (miStepRootK rules (MISym s) root)
    (F MINoRoot)
    MINoStep
    hrootCtx hfire
  refine ⟨Mroot + 1, htotal, ?_⟩
  intro k hk
  by_cases hlt : k < Mroot
  · exact hrootCtxActive k hlt
  · have hk_ge : Mroot ≤ k := Nat.le_of_not_gt hlt
    have hk_le : k ≤ Mroot := Nat.le_of_lt_succ hk
    have hk_eq : k = Mroot := Nat.le_antisymm hk_le hk_ge
    subst k
    change StepActiveShape (eval pMI Mroot (F root))
    rw [hrootCtx]
    exact StepActiveShape.rootK rules (MISym s) MINoRoot

theorem miStepRootK_eval_of_any_root_none_active_miapp_args_step_with_guard
    (rules args argsOut root : AST) (h : String)
    (rootFuel argsFuel : Nat)
    (hrules : IsNormal pMI rules) (hargsNorm : IsNormal pMI args)
    (hroot : eval pMI rootFuel root = MINoRoot)
    (hrootActive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k root))
    (hargs : eval pMI argsFuel (miStepArgs rules args) =
      MIArgsStep argsOut)
    (hargsActive : ∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs rules args))) :
    ∃ N,
      eval pMI N (miStepRootK rules (MIApp h args) root) =
        MIStep (MIApp h argsOut) ∧
      ∀ k, k < N →
        StepActiveShape
          (eval pMI k (miStepRootK rules (MIApp h args) root)) := by
  let F : AST → AST := fun z => miStepRootK rules (MIApp h args) z
  let G : AST := miStepAppK (con0 h) (miStepArgs rules args)
  obtain ⟨Mroot, hrootCtx, hrootCtxActive⟩ :=
    cong_eval_root_to_step_active_with_guard_mi F
      (fun z _hz => StepActiveShape.rootK rules (MIApp h args) z)
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_miapp rules args z z' h
          hrules hargsNorm hactiveStep hstep)
      rootFuel hroot hrootActive
  have hfire : eval pMI 1 (F MINoRoot) = G := by
    simp only [F, G, eval, os_miStepRootK_app_no_root]
  obtain ⟨Mapp, happ, happActive⟩ :=
    miStepAppK_eval_of_args_active_step_named_with_guard h
      (miStepArgs rules args) argsOut argsFuel hargs hargsActive
  have htail := eval_trans_mi 1 Mapp
    (F MINoRoot)
    G
    (MIStep (MIApp h argsOut))
    hfire happ
  have htailActive :
      ∀ k, k < 1 + Mapp →
        StepActiveShape (eval pMI k (F MINoRoot)) := by
    intro k hk
    cases k with
    | zero =>
        simpa only [eval, F] using
          StepActiveShape.rootK rules (MIApp h args) MINoRoot
    | succ k =>
        have hkM : k < Mapp := by
          omega
        have heval :
            eval pMI (Nat.succ k) (F MINoRoot) = eval pMI k G := by
          simp only [F, G, eval, os_miStepRootK_app_no_root]
        rw [heval]
        exact happActive k hkM
  have htotal := eval_trans_mi Mroot (1 + Mapp)
    (miStepRootK rules (MIApp h args) root)
    (F MINoRoot)
    (MIStep (MIApp h argsOut))
    hrootCtx htail
  exact ⟨Mroot + (1 + Mapp), htotal,
    step_active_append_mi Mroot (1 + Mapp) hrootCtx
      hrootCtxActive htailActive⟩

theorem miStepRootK_eval_of_any_root_none_active_miapp_args_none_with_guard
    (rules args root : AST) (h : String)
    (rootFuel argsFuel : Nat)
    (hrules : IsNormal pMI rules) (hargsNorm : IsNormal pMI args)
    (hroot : eval pMI rootFuel root = MINoRoot)
    (hrootActive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k root))
    (hargs : eval pMI argsFuel (miStepArgs rules args) = MINoArgsStep)
    (hargsActive : ∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs rules args))) :
    ∃ N,
      eval pMI N (miStepRootK rules (MIApp h args) root) = MINoStep ∧
      ∀ k, k < N →
        StepActiveShape
          (eval pMI k (miStepRootK rules (MIApp h args) root)) := by
  let F : AST → AST := fun z => miStepRootK rules (MIApp h args) z
  let G : AST := miStepAppK (con0 h) (miStepArgs rules args)
  obtain ⟨Mroot, hrootCtx, hrootCtxActive⟩ :=
    cong_eval_root_to_step_active_with_guard_mi F
      (fun z _hz => StepActiveShape.rootK rules (MIApp h args) z)
      (fun z z' hactiveStep hstep =>
        os_miStepRootK_active_step_miapp rules args z z' h
          hrules hargsNorm hactiveStep hstep)
      rootFuel hroot hrootActive
  have hfire : eval pMI 1 (F MINoRoot) = G := by
    simp only [F, G, eval, os_miStepRootK_app_no_root]
  obtain ⟨Mapp, happ, happActive⟩ :=
    miStepAppK_eval_of_args_active_none_named_with_guard h
      (miStepArgs rules args) argsFuel hargs hargsActive
  have htail := eval_trans_mi 1 Mapp
    (F MINoRoot)
    G
    MINoStep
    hfire happ
  have htailActive :
      ∀ k, k < 1 + Mapp →
        StepActiveShape (eval pMI k (F MINoRoot)) := by
    intro k hk
    cases k with
    | zero =>
        simpa only [eval, F] using
          StepActiveShape.rootK rules (MIApp h args) MINoRoot
    | succ k =>
        have hkM : k < Mapp := by
          omega
        have heval :
            eval pMI (Nat.succ k) (F MINoRoot) = eval pMI k G := by
          simp only [F, G, eval, os_miStepRootK_app_no_root]
        rw [heval]
        exact happActive k hkM
  have htotal := eval_trans_mi Mroot (1 + Mapp)
    (miStepRootK rules (MIApp h args) root)
    (F MINoRoot)
    MINoStep
    hrootCtx htail
  exact ⟨Mroot + (1 + Mapp), htotal,
    step_active_append_mi Mroot (1 + Mapp) hrootCtx
      hrootCtxActive htailActive⟩

theorem miStep_misubst_substInst_root_none_mivar_rawnone
    (rws : List RewriteDecl)
    (term encodedRules template encodedTemplate encodedBs : AST)
    (bs : List (String × AST)) (v : String) (substFuel : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some (MIVar v))
    (hroot : rootBaseStep? rws term = none)
    (htemplate : encAST? template = some encodedTemplate)
    (hbs : encBinds? bs = some encodedBs)
    (hinst : encAST? (AST.inst bs template) = some (MIVar v))
    (hsubst :
      eval pMI substFuel (miSubst encodedBs encodedTemplate) = MIVar v) :
    StepRawNone encodedRules (miSubst encodedBs encodedTemplate) := by
  let rawTerm := miSubst encodedBs encodedTemplate
  obtain ⟨rootFuel, hrootEval, hrootActive⟩ :=
    miRoot_misubst_source_none_active rws term encodedRules (MIVar v)
      encodedBs encodedTemplate substFuel hrules hterm hroot hsubst
      (normal_MIVar v)
  obtain ⟨ctxFuel, hctx, hctxActive⟩ :=
    miStepRootK_active_misubst_substInst_eval_with_guard encodedRules
      (miRoot encodedRules rawTerm) template encodedTemplate encodedBs
      (MIVar v) bs (encRules?_some_normal rws encodedRules hrules)
      (RootActiveShape.root encodedRules rawTerm) htemplate hbs hinst
  obtain ⟨tailFuel, htail, htailActive⟩ :=
    miStepRootK_eval_of_any_root_none_active_mivar_with_guard encodedRules
      (miRoot encodedRules rawTerm) v rootFuel
      (encRules?_some_normal rws encodedRules hrules) hrootEval hrootActive
  have hdispatch :
      eval pMI 1 (miStep encodedRules rawTerm) =
        miStepRootK encodedRules rawTerm (miRoot encodedRules rawTerm) := by
    simp only [eval, os_miStep_dispatch]
  have hprefix := eval_trans_mi 1 ctxFuel
    (miStep encodedRules rawTerm)
    (miStepRootK encodedRules rawTerm (miRoot encodedRules rawTerm))
    (miStepRootK encodedRules (MIVar v) (miRoot encodedRules rawTerm))
    hdispatch hctx
  have htotal := eval_trans_mi (1 + ctxFuel) tailFuel
    (miStep encodedRules rawTerm)
    (miStepRootK encodedRules (MIVar v) (miRoot encodedRules rawTerm))
    MINoStep hprefix htail
  unfold StepRawNone
  refine ⟨(1 + ctxFuel) + tailFuel, htotal, ?_⟩
  apply step_active_append_mi (1 + ctxFuel) tailFuel hprefix
  · apply step_active_append_mi 1 ctxFuel hdispatch
    · exact step_active_fuel_one_mi (StepActiveShape.step encodedRules rawTerm)
    · exact hctxActive
  · exact htailActive

theorem miStep_misubst_substInst_root_none_misym_rawnone
    (rws : List RewriteDecl)
    (term encodedRules template encodedTemplate encodedBs : AST)
    (bs : List (String × AST)) (s : String) (substFuel : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some (MISym s))
    (hroot : rootBaseStep? rws term = none)
    (htemplate : encAST? template = some encodedTemplate)
    (hbs : encBinds? bs = some encodedBs)
    (hinst : encAST? (AST.inst bs template) = some (MISym s))
    (hsubst :
      eval pMI substFuel (miSubst encodedBs encodedTemplate) = MISym s) :
    StepRawNone encodedRules (miSubst encodedBs encodedTemplate) := by
  let rawTerm := miSubst encodedBs encodedTemplate
  obtain ⟨rootFuel, hrootEval, hrootActive⟩ :=
    miRoot_misubst_source_none_active rws term encodedRules (MISym s)
      encodedBs encodedTemplate substFuel hrules hterm hroot hsubst
      (normal_MISym s)
  obtain ⟨ctxFuel, hctx, hctxActive⟩ :=
    miStepRootK_active_misubst_substInst_eval_with_guard encodedRules
      (miRoot encodedRules rawTerm) template encodedTemplate encodedBs
      (MISym s) bs (encRules?_some_normal rws encodedRules hrules)
      (RootActiveShape.root encodedRules rawTerm) htemplate hbs hinst
  obtain ⟨tailFuel, htail, htailActive⟩ :=
    miStepRootK_eval_of_any_root_none_active_misym_with_guard encodedRules
      (miRoot encodedRules rawTerm) s rootFuel
      (encRules?_some_normal rws encodedRules hrules) hrootEval hrootActive
  have hdispatch :
      eval pMI 1 (miStep encodedRules rawTerm) =
        miStepRootK encodedRules rawTerm (miRoot encodedRules rawTerm) := by
    simp only [eval, os_miStep_dispatch]
  have hprefix := eval_trans_mi 1 ctxFuel
    (miStep encodedRules rawTerm)
    (miStepRootK encodedRules rawTerm (miRoot encodedRules rawTerm))
    (miStepRootK encodedRules (MISym s) (miRoot encodedRules rawTerm))
    hdispatch hctx
  have htotal := eval_trans_mi (1 + ctxFuel) tailFuel
    (miStep encodedRules rawTerm)
    (miStepRootK encodedRules (MISym s) (miRoot encodedRules rawTerm))
    MINoStep hprefix htail
  unfold StepRawNone
  refine ⟨(1 + ctxFuel) + tailFuel, htotal, ?_⟩
  apply step_active_append_mi (1 + ctxFuel) tailFuel hprefix
  · apply step_active_append_mi 1 ctxFuel hdispatch
    · exact step_active_fuel_one_mi (StepActiveShape.step encodedRules rawTerm)
    · exact hctxActive
  · exact htailActive

theorem miStep_misubst_substInst_root_none_miapp_args_rawsome_payload
    (rws : List RewriteDecl)
    (term encodedRules template encodedTemplate encodedBs encodedArgs : AST)
    (bs : List (String × AST)) (headName : String)
    (argOutHead : AST) (argOutRest : List AST) (substFuel : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some (MIApp headName encodedArgs))
    (hroot : rootBaseStep? rws term = none)
    (htemplate : encAST? template = some encodedTemplate)
    (hbs : encBinds? bs = some encodedBs)
    (hinst :
      encAST? (AST.inst bs template) = some (MIApp headName encodedArgs))
    (hsubst : eval pMI substFuel
        (miSubst encodedBs encodedTemplate) =
      MIApp headName encodedArgs)
    (hargs : ArgsRawSomePayload encodedRules encodedArgs
      (argOutHead :: argOutRest)) :
    StepRawSomePayload encodedRules (miSubst encodedBs encodedTemplate)
      (.sexp (.id headName) (argOutHead :: argOutRest)) := by
  let rawTerm := miSubst encodedBs encodedTemplate
  have hencodedNorm :
      IsNormal pMI (MIApp headName encodedArgs) :=
    encAST?_some_normal term (MIApp headName encodedArgs) hterm
  have hargsNorm : IsNormal pMI encodedArgs :=
    normal_MIApp_args hencodedNorm
  obtain ⟨rootFuel, hrootEval, hrootActive⟩ :=
    miRoot_misubst_source_none_active rws term encodedRules
      (MIApp headName encodedArgs) encodedBs encodedTemplate substFuel
      hrules hterm hroot hsubst hencodedNorm
  obtain ⟨ctxFuel, hctx, hctxActive⟩ :=
    miStepRootK_active_misubst_substInst_eval_with_guard encodedRules
      (miRoot encodedRules rawTerm) template encodedTemplate encodedBs
      (MIApp headName encodedArgs) bs
      (encRules?_some_normal rws encodedRules hrules)
      (RootActiveShape.root encodedRules rawTerm) htemplate hbs hinst
  unfold ArgsRawSomePayload at hargs
  obtain ⟨rawArgs, encodedArgsOut, argsFuel, normFuel, hargsOutEnc,
    hargsEval, hargsActive, hnorm, hargsOutNorm, hpayload⟩ := hargs
  obtain ⟨tailFuel, htail, htailActive⟩ :=
    miStepRootK_eval_of_any_root_none_active_miapp_args_step_with_guard
      encodedRules encodedArgs rawArgs (miRoot encodedRules rawTerm)
      headName rootFuel argsFuel
      (encRules?_some_normal rws encodedRules hrules)
      hargsNorm hrootEval hrootActive hargsEval hargsActive
  have hdispatch :
      eval pMI 1 (miStep encodedRules rawTerm) =
        miStepRootK encodedRules rawTerm (miRoot encodedRules rawTerm) := by
    simp only [eval, os_miStep_dispatch]
  have hprefix := eval_trans_mi 1 ctxFuel
    (miStep encodedRules rawTerm)
    (miStepRootK encodedRules rawTerm (miRoot encodedRules rawTerm))
    (miStepRootK encodedRules (MIApp headName encodedArgs)
      (miRoot encodedRules rawTerm))
    hdispatch hctx
  have hstep := eval_trans_mi (1 + ctxFuel) tailFuel
    (miStep encodedRules rawTerm)
    (miStepRootK encodedRules (MIApp headName encodedArgs)
      (miRoot encodedRules rawTerm))
    (MIStep (MIApp headName rawArgs)) hprefix htail
  have hstepActive :
      ∀ k, k < (1 + ctxFuel) + tailFuel →
        StepActiveShape (eval pMI k (miStep encodedRules rawTerm)) := by
    apply step_active_append_mi (1 + ctxFuel) tailFuel hprefix
    · apply step_active_append_mi 1 ctxFuel hdispatch
      · exact step_active_fuel_one_mi
          (StepActiveShape.step encodedRules rawTerm)
      · exact hctxActive
    · exact htailActive
  obtain ⟨normStepFuel, hnormStep⟩ :=
    miApp_args_eval_of headName rawArgs encodedArgsOut normFuel hnorm
      hargsOutNorm
  unfold StepRawSomePayload
  refine ⟨MIApp headName rawArgs, MIApp headName encodedArgsOut,
    (1 + ctxFuel) + tailFuel, normStepFuel, ?_, hstep, hstepActive,
    hnormStep, ?_, ?_⟩
  · simp only [encAST?, hargsOutEnc]
  · exact normal_MIApp headName encodedArgsOut hargsOutNorm
  · exact RawTermPayload.app headName hpayload

theorem miStep_misubst_substInst_root_none_miapp_args_rawnone
    (rws : List RewriteDecl)
    (term encodedRules template encodedTemplate encodedBs encodedArgs : AST)
    (bs : List (String × AST)) (headName : String) (substFuel : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some (MIApp headName encodedArgs))
    (hroot : rootBaseStep? rws term = none)
    (htemplate : encAST? template = some encodedTemplate)
    (hbs : encBinds? bs = some encodedBs)
    (hinst :
      encAST? (AST.inst bs template) = some (MIApp headName encodedArgs))
    (hsubst : eval pMI substFuel
        (miSubst encodedBs encodedTemplate) =
      MIApp headName encodedArgs)
    (hargs : ArgsRawNone encodedRules encodedArgs) :
    StepRawNone encodedRules (miSubst encodedBs encodedTemplate) := by
  let rawTerm := miSubst encodedBs encodedTemplate
  have hencodedNorm :
      IsNormal pMI (MIApp headName encodedArgs) :=
    encAST?_some_normal term (MIApp headName encodedArgs) hterm
  have hargsNorm : IsNormal pMI encodedArgs :=
    normal_MIApp_args hencodedNorm
  obtain ⟨rootFuel, hrootEval, hrootActive⟩ :=
    miRoot_misubst_source_none_active rws term encodedRules
      (MIApp headName encodedArgs) encodedBs encodedTemplate substFuel
      hrules hterm hroot hsubst hencodedNorm
  obtain ⟨ctxFuel, hctx, hctxActive⟩ :=
    miStepRootK_active_misubst_substInst_eval_with_guard encodedRules
      (miRoot encodedRules rawTerm) template encodedTemplate encodedBs
      (MIApp headName encodedArgs) bs
      (encRules?_some_normal rws encodedRules hrules)
      (RootActiveShape.root encodedRules rawTerm) htemplate hbs hinst
  unfold ArgsRawNone at hargs
  obtain ⟨argsFuel, hargsEval, hargsActive⟩ := hargs
  obtain ⟨tailFuel, htail, htailActive⟩ :=
    miStepRootK_eval_of_any_root_none_active_miapp_args_none_with_guard
      encodedRules encodedArgs (miRoot encodedRules rawTerm) headName
      rootFuel argsFuel
      (encRules?_some_normal rws encodedRules hrules)
      hargsNorm hrootEval hrootActive hargsEval hargsActive
  have hdispatch :
      eval pMI 1 (miStep encodedRules rawTerm) =
        miStepRootK encodedRules rawTerm (miRoot encodedRules rawTerm) := by
    simp only [eval, os_miStep_dispatch]
  have hprefix := eval_trans_mi 1 ctxFuel
    (miStep encodedRules rawTerm)
    (miStepRootK encodedRules rawTerm (miRoot encodedRules rawTerm))
    (miStepRootK encodedRules (MIApp headName encodedArgs)
      (miRoot encodedRules rawTerm))
    hdispatch hctx
  have htotal := eval_trans_mi (1 + ctxFuel) tailFuel
    (miStep encodedRules rawTerm)
    (miStepRootK encodedRules (MIApp headName encodedArgs)
      (miRoot encodedRules rawTerm))
    MINoStep hprefix htail
  unfold StepRawNone
  refine ⟨(1 + ctxFuel) + tailFuel, htotal, ?_⟩
  apply step_active_append_mi (1 + ctxFuel) tailFuel hprefix
  · apply step_active_append_mi 1 ctxFuel hdispatch
    · exact step_active_fuel_one_mi
        (StepActiveShape.step encodedRules rawTerm)
    · exact hctxActive
  · exact htailActive

theorem miRoot_rawPayload_app_source_none_active
    (rws : List RewriteDecl)
    (term encodedRules rawArgs encodedArgs : AST)
    (headName : String)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some (MIApp headName encodedArgs))
    (hroot : rootBaseStep? rws term = none)
    (hhead : (headName == "match") = false)
    (hargsPayload : RawArgsPayload rawArgs encodedArgs) :
    ∃ rootFuel,
      eval pMI rootFuel
          (miRoot encodedRules (MIApp headName rawArgs)) =
        MINoRoot ∧
      ∀ k, k < rootFuel →
        RootActiveShape
          (eval pMI k
            (miRoot encodedRules (MIApp headName rawArgs))) := by
  have hencodedNorm : IsNormal pMI (MIApp headName encodedArgs) :=
    encAST?_some_normal term (MIApp headName encodedArgs) hterm
  have htable :=
    miRootTable_rawPayload_source_none_active rws term encodedRules
      (MIApp headName encodedArgs) (MIApp headName rawArgs)
      hrules hterm hroot (RawTermPayload.app headName hargsPayload)
      hencodedNorm
  unfold RootTableRawActiveNone at htable
  obtain ⟨tableFuel, htableEval, htableActive⟩ := htable
  have hdispatch :
      eval pMI 1 (miRoot encodedRules (MIApp headName rawArgs)) =
        miRootTable encodedRules (MIApp headName rawArgs) := by
    simp only [eval, os_miRoot_default_app_head_ne, hhead]
  have htotal := eval_trans_mi 1 tableFuel
    (miRoot encodedRules (MIApp headName rawArgs))
    (miRootTable encodedRules (MIApp headName rawArgs))
    MINoRoot hdispatch htableEval
  refine ⟨1 + tableFuel, htotal, ?_⟩
  apply root_active_append_mi 1 tableFuel hdispatch
  · intro k hk
    cases k with
    | zero =>
        simp only [eval]
        exact RootActiveShape.root encodedRules (MIApp headName rawArgs)
    | succ n =>
        have hn : n < 0 := Nat.succ_lt_succ_iff.mp hk
        exact False.elim (Nat.not_lt_zero n hn)
  · exact htableActive

theorem miStep_rawPayload_app_root_none_args_rawsome_with_guard_payload
    (rws : List RewriteDecl)
    (term encodedRules rawArgs encodedArgs : AST)
    (argOutHead : AST) (argOutRest : List AST)
    (headName : String)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some (MIApp headName encodedArgs))
    (hroot : rootBaseStep? rws term = none)
    (hhead : (headName == "match") = false)
    (hargsPayload : RawArgsPayload rawArgs encodedArgs)
    (hargs : ArgsRawSomePayload encodedRules encodedArgs
      (argOutHead :: argOutRest)) :
    StepRawSomePayload encodedRules (MIApp headName rawArgs)
      (.sexp (.id headName) (argOutHead :: argOutRest)) := by
  have hencodedNorm : IsNormal pMI (MIApp headName encodedArgs) :=
    encAST?_some_normal term (MIApp headName encodedArgs) hterm
  have hargsNorm : IsNormal pMI encodedArgs :=
    normal_MIApp_args hencodedNorm
  obtain ⟨rootFuel, hrootEval, hrootActive⟩ :=
    miRoot_rawPayload_app_source_none_active rws term encodedRules
      rawArgs encodedArgs headName hrules hterm hroot hhead
      hargsPayload
  obtain ⟨argsNormFuel, hargsNormEval⟩ :=
    rawArgsPayload_eval_of_normal hargsPayload hargsNorm
  obtain ⟨ctxFuel, hctx, hctxActive⟩ :=
    miStepRootK_active_miapp_args_eval_of_with_guard encodedRules
      rawArgs encodedArgs (miRoot encodedRules (MIApp headName rawArgs))
      headName argsNormFuel
      (encRules?_some_normal rws encodedRules hrules)
      (RootActiveShape.root encodedRules (MIApp headName rawArgs))
      hargsNormEval hargsNorm
  unfold ArgsRawSomePayload at hargs
  obtain ⟨rawArgsOut, encodedArgsOut, argsFuel, normFuel,
    hargsOutEnc, hargsEval, hargsActive, hnorm, hargsOutNorm,
    hpayload⟩ := hargs
  obtain ⟨tailFuel, htail, htailActive⟩ :=
    miStepRootK_eval_of_any_root_none_active_miapp_args_step_with_guard
      encodedRules encodedArgs rawArgsOut
      (miRoot encodedRules (MIApp headName rawArgs)) headName
      rootFuel argsFuel
      (encRules?_some_normal rws encodedRules hrules)
      hargsNorm hrootEval hrootActive hargsEval hargsActive
  have hdispatch :
      eval pMI 1 (miStep encodedRules (MIApp headName rawArgs)) =
        miStepRootK encodedRules (MIApp headName rawArgs)
          (miRoot encodedRules (MIApp headName rawArgs)) := by
    simp only [eval, os_miStep_dispatch]
  have hprefix := eval_trans_mi 1 ctxFuel
    (miStep encodedRules (MIApp headName rawArgs))
    (miStepRootK encodedRules (MIApp headName rawArgs)
      (miRoot encodedRules (MIApp headName rawArgs)))
    (miStepRootK encodedRules (MIApp headName encodedArgs)
      (miRoot encodedRules (MIApp headName rawArgs)))
    hdispatch hctx
  have hstep := eval_trans_mi (1 + ctxFuel) tailFuel
    (miStep encodedRules (MIApp headName rawArgs))
    (miStepRootK encodedRules (MIApp headName encodedArgs)
      (miRoot encodedRules (MIApp headName rawArgs)))
    (MIStep (MIApp headName rawArgsOut)) hprefix htail
  have hstepActive :
      ∀ k, k < (1 + ctxFuel) + tailFuel →
        StepActiveShape
          (eval pMI k (miStep encodedRules (MIApp headName rawArgs))) := by
    apply step_active_append_mi (1 + ctxFuel) tailFuel hprefix
    · apply step_active_append_mi 1 ctxFuel hdispatch
      · exact step_active_fuel_one_mi
          (StepActiveShape.step encodedRules (MIApp headName rawArgs))
      · exact hctxActive
    · exact htailActive
  obtain ⟨normStepFuel, hnormStep⟩ :=
    miApp_args_eval_of headName rawArgsOut encodedArgsOut normFuel hnorm
      hargsOutNorm
  unfold StepRawSomePayload
  refine ⟨MIApp headName rawArgsOut, MIApp headName encodedArgsOut,
    (1 + ctxFuel) + tailFuel, normStepFuel, ?_, hstep, hstepActive,
    hnormStep, ?_, ?_⟩
  · simp only [encAST?, hargsOutEnc]
  · exact normal_MIApp headName encodedArgsOut hargsOutNorm
  · exact RawTermPayload.app headName hpayload

theorem miStep_rawPayload_app_root_none_args_rawnone_with_guard
    (rws : List RewriteDecl)
    (term encodedRules rawArgs encodedArgs : AST)
    (headName : String)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some (MIApp headName encodedArgs))
    (hroot : rootBaseStep? rws term = none)
    (hhead : (headName == "match") = false)
    (hargsPayload : RawArgsPayload rawArgs encodedArgs)
    (hargs : ArgsRawNone encodedRules encodedArgs) :
    StepRawNone encodedRules (MIApp headName rawArgs) := by
  have hencodedNorm : IsNormal pMI (MIApp headName encodedArgs) :=
    encAST?_some_normal term (MIApp headName encodedArgs) hterm
  have hargsNorm : IsNormal pMI encodedArgs :=
    normal_MIApp_args hencodedNorm
  obtain ⟨rootFuel, hrootEval, hrootActive⟩ :=
    miRoot_rawPayload_app_source_none_active rws term encodedRules
      rawArgs encodedArgs headName hrules hterm hroot hhead
      hargsPayload
  obtain ⟨argsNormFuel, hargsNormEval⟩ :=
    rawArgsPayload_eval_of_normal hargsPayload hargsNorm
  obtain ⟨ctxFuel, hctx, hctxActive⟩ :=
    miStepRootK_active_miapp_args_eval_of_with_guard encodedRules
      rawArgs encodedArgs (miRoot encodedRules (MIApp headName rawArgs))
      headName argsNormFuel
      (encRules?_some_normal rws encodedRules hrules)
      (RootActiveShape.root encodedRules (MIApp headName rawArgs))
      hargsNormEval hargsNorm
  unfold ArgsRawNone at hargs
  obtain ⟨argsFuel, hargsEval, hargsActive⟩ := hargs
  obtain ⟨tailFuel, htail, htailActive⟩ :=
    miStepRootK_eval_of_any_root_none_active_miapp_args_none_with_guard
      encodedRules encodedArgs
      (miRoot encodedRules (MIApp headName rawArgs)) headName
      rootFuel argsFuel
      (encRules?_some_normal rws encodedRules hrules)
      hargsNorm hrootEval hrootActive hargsEval hargsActive
  have hdispatch :
      eval pMI 1 (miStep encodedRules (MIApp headName rawArgs)) =
        miStepRootK encodedRules (MIApp headName rawArgs)
          (miRoot encodedRules (MIApp headName rawArgs)) := by
    simp only [eval, os_miStep_dispatch]
  have hprefix := eval_trans_mi 1 ctxFuel
    (miStep encodedRules (MIApp headName rawArgs))
    (miStepRootK encodedRules (MIApp headName rawArgs)
      (miRoot encodedRules (MIApp headName rawArgs)))
    (miStepRootK encodedRules (MIApp headName encodedArgs)
      (miRoot encodedRules (MIApp headName rawArgs)))
    hdispatch hctx
  have htotal := eval_trans_mi (1 + ctxFuel) tailFuel
    (miStep encodedRules (MIApp headName rawArgs))
    (miStepRootK encodedRules (MIApp headName encodedArgs)
      (miRoot encodedRules (MIApp headName rawArgs)))
    MINoStep hprefix htail
  unfold StepRawNone
  refine ⟨(1 + ctxFuel) + tailFuel, htotal, ?_⟩
  apply step_active_append_mi (1 + ctxFuel) tailFuel hprefix
  · apply step_active_append_mi 1 ctxFuel hdispatch
    · exact step_active_fuel_one_mi
        (StepActiveShape.step encodedRules (MIApp headName rawArgs))
    · exact hctxActive
  · exact htailActive

theorem miStep_eval_of_root_none_active_mivar_with_guard
    (rules : AST) (v : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MIVar v)) = MINoRoot)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIVar v)))) :
    ∃ N, eval pMI N (miStep rules (MIVar v)) = MINoStep ∧
      ∀ k, k < N →
        StepActiveShape (eval pMI k (miStep rules (MIVar v))) := by
  obtain ⟨Mroot, hrootK, hrootKActive⟩ :=
    miStepRootK_eval_of_root_none_active_mivar_with_guard
      rules v rootFuel hrules hroot hactive
  exact miStep_eval_of_rootK_active_with_dispatch rules (MIVar v)
    MINoStep Mroot hrootK hrootKActive

theorem miStep_eval_of_root_none_active_misym_with_guard
    (rules : AST) (s : String) (rootFuel : Nat)
    (hrules : IsNormal pMI rules)
    (hroot : eval pMI rootFuel (miRoot rules (MISym s)) = MINoRoot)
    (hactive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MISym s)))) :
    ∃ N, eval pMI N (miStep rules (MISym s)) = MINoStep ∧
      ∀ k, k < N →
        StepActiveShape (eval pMI k (miStep rules (MISym s))) := by
  obtain ⟨Mroot, hrootK, hrootKActive⟩ :=
    miStepRootK_eval_of_root_none_active_misym_with_guard
      rules s rootFuel hrules hroot hactive
  exact miStep_eval_of_rootK_active_with_dispatch rules (MISym s)
    MINoStep Mroot hrootK hrootKActive

theorem miStep_eval_of_root_none_active_miapp_args_step_with_guard
    (rules args argsOut : AST) (h : String)
    (rootFuel argsFuel : Nat)
    (hrules : IsNormal pMI rules) (hargsNorm : IsNormal pMI args)
    (hroot : eval pMI rootFuel (miRoot rules (MIApp h args)) = MINoRoot)
    (hrootActive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIApp h args))))
    (hargs : eval pMI argsFuel (miStepArgs rules args) =
      MIArgsStep argsOut)
    (hargsActive : ∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs rules args))) :
    ∃ N, eval pMI N (miStep rules (MIApp h args)) =
        MIStep (MIApp h argsOut) ∧
      ∀ k, k < N →
        StepActiveShape (eval pMI k (miStep rules (MIApp h args))) := by
  obtain ⟨Mroot, hrootK, hrootKActive⟩ :=
    miStepRootK_eval_of_root_none_active_miapp_args_step_with_guard
      rules args argsOut h rootFuel argsFuel hrules hargsNorm
      hroot hrootActive hargs hargsActive
  exact miStep_eval_of_rootK_active_with_dispatch rules (MIApp h args)
    (MIStep (MIApp h argsOut)) Mroot hrootK hrootKActive

theorem miStep_eval_of_root_none_active_miapp_args_none_with_guard
    (rules args : AST) (h : String)
    (rootFuel argsFuel : Nat)
    (hrules : IsNormal pMI rules) (hargsNorm : IsNormal pMI args)
    (hroot : eval pMI rootFuel (miRoot rules (MIApp h args)) = MINoRoot)
    (hrootActive : ∀ k, k < rootFuel →
      RootActiveShape (eval pMI k (miRoot rules (MIApp h args))))
    (hargs : eval pMI argsFuel (miStepArgs rules args) = MINoArgsStep)
    (hargsActive : ∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs rules args))) :
    ∃ N, eval pMI N (miStep rules (MIApp h args)) = MINoStep ∧
      ∀ k, k < N →
        StepActiveShape (eval pMI k (miStep rules (MIApp h args))) := by
  obtain ⟨Mroot, hrootK, hrootKActive⟩ :=
    miStepRootK_eval_of_root_none_active_miapp_args_none_with_guard
      rules args h rootFuel argsFuel hrules hargsNorm
      hroot hrootActive hargs hargsActive
  exact miStep_eval_of_rootK_active_with_dispatch rules (MIApp h args)
    MINoStep Mroot hrootK hrootKActive

theorem miStep_source_root_some_sim_var (rws : List RewriteDecl)
    (v : String) (encodedRules out : AST)
    (hrules : encRules? rws = some encodedRules)
    (hcase : rootBaseStep? rws (.var (.base v)) = some out) :
    ∃ (encodedOut : AST) (N : Nat),
      encAST? out = some encodedOut ∧
      eval pMI N (miStep encodedRules (MIVar v)) = MIStep encodedOut ∧
      IsNormal pMI (MIStep encodedOut) := by
  have hroot := miRoot_source_raw_active_sim_var rws v encodedRules hrules
  simp only [hcase] at hroot
  obtain ⟨rawNext, encodedOut, rootFuel, substFuel, hout, hrootEval,
    hrootActive, hsubst, houtNorm⟩ := hroot
  obtain ⟨Nstep, hstep⟩ :=
    miStep_eval_of_root_active_normalized_mivar encodedRules rawNext
      encodedOut v rootFuel substFuel
      (encRules?_some_normal rws encodedRules hrules)
      hrootEval hrootActive hsubst houtNorm
  exact ⟨encodedOut, Nstep, hout, hstep, normal_MIStep encodedOut houtNorm⟩

theorem miStep_source_root_some_sim_sym (rws : List RewriteDecl)
    (s : String) (encodedRules out : AST)
    (hrules : encRules? rws = some encodedRules)
    (hcase : rootBaseStep? rws (.sexp (.id s) []) = some out) :
    ∃ (encodedOut : AST) (N : Nat),
      encAST? out = some encodedOut ∧
      eval pMI N (miStep encodedRules (MISym s)) = MIStep encodedOut ∧
      IsNormal pMI (MIStep encodedOut) := by
  have hroot := miRoot_source_raw_active_sim_sym rws s encodedRules hrules
  simp only [hcase] at hroot
  obtain ⟨rawNext, encodedOut, rootFuel, substFuel, hout, hrootEval,
    hrootActive, hsubst, houtNorm⟩ := hroot
  obtain ⟨Nstep, hstep⟩ :=
    miStep_eval_of_root_active_normalized_misym encodedRules rawNext
      encodedOut s rootFuel substFuel
      (encRules?_some_normal rws encodedRules hrules)
      hrootEval hrootActive hsubst houtNorm
  exact ⟨encodedOut, Nstep, hout, hstep, normal_MIStep encodedOut houtNorm⟩

theorem miStep_source_root_some_sim_app_head_ne (rws : List RewriteDecl)
    (headName : String) (a : AST) (rest : List AST)
    (encodedRules encodedArgs out : AST)
    (hrules : encRules? rws = some encodedRules)
    (hargs : encASTList? (a :: rest) = some encodedArgs)
    (hhead : (headName == "match") = false)
    (hcase : rootBaseStep? rws (.sexp (.id headName) (a :: rest)) =
      some out) :
    ∃ (encodedOut : AST) (N : Nat),
      encAST? out = some encodedOut ∧
      eval pMI N (miStep encodedRules (MIApp headName encodedArgs)) =
        MIStep encodedOut ∧
      IsNormal pMI (MIStep encodedOut) := by
  have hroot :=
    miRoot_source_raw_active_sim_app_head_ne rws headName a rest
      encodedRules encodedArgs hrules hargs hhead
  simp only [hcase] at hroot
  obtain ⟨rawNext, encodedOut, rootFuel, substFuel, hout, hrootEval,
    hrootActive, hsubst, houtNorm⟩ := hroot
  obtain ⟨Nstep, hstep⟩ :=
    miStep_eval_of_root_active_normalized_miapp encodedRules encodedArgs
      rawNext encodedOut headName rootFuel substFuel
      (encRules?_some_normal rws encodedRules hrules)
      (encASTList?_some_normal (a :: rest) encodedArgs hargs)
      hrootEval hrootActive hsubst houtNorm
  exact ⟨encodedOut, Nstep, hout, hstep, normal_MIStep encodedOut houtNorm⟩

theorem miStep_source_root_none_sim_var (rws : List RewriteDecl)
    (v : String) (encodedRules : AST)
    (hrules : encRules? rws = some encodedRules)
    (hcase : rootBaseStep? rws (.var (.base v)) = none) :
    ∃ N, eval pMI N (miStep encodedRules (MIVar v)) = MINoStep := by
  have hroot := miRoot_source_raw_active_sim_var rws v encodedRules hrules
  simp only [hcase] at hroot
  obtain ⟨rootFuel, hrootEval, hrootActive⟩ := hroot
  exact miStep_eval_of_root_none_active_mivar encodedRules v rootFuel
    (encRules?_some_normal rws encodedRules hrules)
    hrootEval hrootActive

theorem miStep_source_root_none_sim_sym (rws : List RewriteDecl)
    (s : String) (encodedRules : AST)
    (hrules : encRules? rws = some encodedRules)
    (hcase : rootBaseStep? rws (.sexp (.id s) []) = none) :
    ∃ N, eval pMI N (miStep encodedRules (MISym s)) = MINoStep := by
  have hroot := miRoot_source_raw_active_sim_sym rws s encodedRules hrules
  simp only [hcase] at hroot
  obtain ⟨rootFuel, hrootEval, hrootActive⟩ := hroot
  exact miStep_eval_of_root_none_active_misym encodedRules s rootFuel
    (encRules?_some_normal rws encodedRules hrules)
    hrootEval hrootActive

theorem miStep_source_root_none_app_args_step_sim (rws : List RewriteDecl)
    (headName : String) (a : AST) (rest : List AST)
    (encodedRules encodedArgs argsOut : AST) (argsFuel : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hargsEnc : encASTList? (a :: rest) = some encodedArgs)
    (hhead : (headName == "match") = false)
    (hcase : rootBaseStep? rws (.sexp (.id headName) (a :: rest)) = none)
    (hargs : eval pMI argsFuel (miStepArgs encodedRules encodedArgs) =
      MIArgsStep argsOut)
    (hargsActive : ∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs encodedRules encodedArgs))) :
    ∃ N,
      eval pMI N (miStep encodedRules (MIApp headName encodedArgs)) =
        MIStep (MIApp headName argsOut) := by
  have hroot :=
    miRoot_source_raw_active_sim_app_head_ne rws headName a rest
      encodedRules encodedArgs hrules hargsEnc hhead
  simp only [hcase] at hroot
  obtain ⟨rootFuel, hrootEval, hrootActive⟩ := hroot
  exact miStep_eval_of_root_none_active_miapp_args_step
    encodedRules encodedArgs argsOut headName rootFuel argsFuel
    (encRules?_some_normal rws encodedRules hrules)
    (encASTList?_some_normal (a :: rest) encodedArgs hargsEnc)
    hrootEval hrootActive hargs hargsActive

theorem miStep_source_root_none_app_args_none_sim (rws : List RewriteDecl)
    (headName : String) (a : AST) (rest : List AST)
    (encodedRules encodedArgs : AST) (argsFuel : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hargsEnc : encASTList? (a :: rest) = some encodedArgs)
    (hhead : (headName == "match") = false)
    (hcase : rootBaseStep? rws (.sexp (.id headName) (a :: rest)) = none)
    (hargs : eval pMI argsFuel (miStepArgs encodedRules encodedArgs) =
      MINoArgsStep)
    (hargsActive : ∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs encodedRules encodedArgs))) :
    ∃ N,
      eval pMI N (miStep encodedRules (MIApp headName encodedArgs)) =
        MINoStep := by
  have hroot :=
    miRoot_source_raw_active_sim_app_head_ne rws headName a rest
      encodedRules encodedArgs hrules hargsEnc hhead
  simp only [hcase] at hroot
  obtain ⟨rootFuel, hrootEval, hrootActive⟩ := hroot
  exact miStep_eval_of_root_none_active_miapp_args_none
    encodedRules encodedArgs headName rootFuel argsFuel
    (encRules?_some_normal rws encodedRules hrules)
    (encASTList?_some_normal (a :: rest) encodedArgs hargsEnc)
    hrootEval hrootActive hargs hargsActive

theorem miStep_source_root_some_raw_active_sim_var (rws : List RewriteDecl)
    (v : String) (encodedRules out : AST)
    (hrules : encRules? rws = some encodedRules)
    (hcase : rootBaseStep? rws (.var (.base v)) = some out) :
    ∃ (rawNext encodedOut : AST) (N substFuel : Nat),
      encAST? out = some encodedOut ∧
      eval pMI N (miStep encodedRules (MIVar v)) = MIStep rawNext ∧
      (∀ k, k < N →
        StepActiveShape (eval pMI k (miStep encodedRules (MIVar v)))) ∧
      eval pMI substFuel rawNext = encodedOut ∧
      IsNormal pMI encodedOut := by
  have hroot := miRoot_source_raw_active_sim_var rws v encodedRules hrules
  simp only [hcase] at hroot
  obtain ⟨rawNext, encodedOut, rootFuel, substFuel, hout, hrootEval,
    hrootActive, hsubst, houtNorm⟩ := hroot
  obtain ⟨Nstep, hstep, hstepActive⟩ :=
    miStep_eval_of_root_active_mivar_with_guard encodedRules rawNext v
      rootFuel
      (encRules?_some_normal rws encodedRules hrules)
      hrootEval hrootActive
  exact ⟨rawNext, encodedOut, Nstep, substFuel, hout, hstep,
    hstepActive, hsubst, houtNorm⟩

theorem miStep_source_root_some_raw_active_sim_sym (rws : List RewriteDecl)
    (s : String) (encodedRules out : AST)
    (hrules : encRules? rws = some encodedRules)
    (hcase : rootBaseStep? rws (.sexp (.id s) []) = some out) :
    ∃ (rawNext encodedOut : AST) (N substFuel : Nat),
      encAST? out = some encodedOut ∧
      eval pMI N (miStep encodedRules (MISym s)) = MIStep rawNext ∧
      (∀ k, k < N →
        StepActiveShape (eval pMI k (miStep encodedRules (MISym s)))) ∧
      eval pMI substFuel rawNext = encodedOut ∧
      IsNormal pMI encodedOut := by
  have hroot := miRoot_source_raw_active_sim_sym rws s encodedRules hrules
  simp only [hcase] at hroot
  obtain ⟨rawNext, encodedOut, rootFuel, substFuel, hout, hrootEval,
    hrootActive, hsubst, houtNorm⟩ := hroot
  obtain ⟨Nstep, hstep, hstepActive⟩ :=
    miStep_eval_of_root_active_misym_with_guard encodedRules rawNext s
      rootFuel
      (encRules?_some_normal rws encodedRules hrules)
      hrootEval hrootActive
  exact ⟨rawNext, encodedOut, Nstep, substFuel, hout, hstep,
    hstepActive, hsubst, houtNorm⟩

theorem miStep_source_root_some_raw_active_sim_app_head_ne
    (rws : List RewriteDecl)
    (headName : String) (a : AST) (rest : List AST)
    (encodedRules encodedArgs out : AST)
    (hrules : encRules? rws = some encodedRules)
    (hargs : encASTList? (a :: rest) = some encodedArgs)
    (hhead : (headName == "match") = false)
    (hcase : rootBaseStep? rws (.sexp (.id headName) (a :: rest)) =
      some out) :
    ∃ (rawNext encodedOut : AST) (N substFuel : Nat),
      encAST? out = some encodedOut ∧
      eval pMI N (miStep encodedRules (MIApp headName encodedArgs)) =
        MIStep rawNext ∧
      (∀ k, k < N →
        StepActiveShape
          (eval pMI k (miStep encodedRules (MIApp headName encodedArgs)))) ∧
      eval pMI substFuel rawNext = encodedOut ∧
      IsNormal pMI encodedOut := by
  have hroot :=
    miRoot_source_raw_active_sim_app_head_ne rws headName a rest
      encodedRules encodedArgs hrules hargs hhead
  simp only [hcase] at hroot
  obtain ⟨rawNext, encodedOut, rootFuel, substFuel, hout, hrootEval,
    hrootActive, hsubst, houtNorm⟩ := hroot
  obtain ⟨Nstep, hstep, hstepActive⟩ :=
    miStep_eval_of_root_active_miapp_with_guard encodedRules encodedArgs
      rawNext headName rootFuel
      (encRules?_some_normal rws encodedRules hrules)
      (encASTList?_some_normal (a :: rest) encodedArgs hargs)
      hrootEval hrootActive
  exact ⟨rawNext, encodedOut, Nstep, substFuel, hout, hstep,
    hstepActive, hsubst, houtNorm⟩

theorem miStep_source_root_none_sim_var_with_guard (rws : List RewriteDecl)
    (v : String) (encodedRules : AST)
    (hrules : encRules? rws = some encodedRules)
    (hcase : rootBaseStep? rws (.var (.base v)) = none) :
    ∃ N, eval pMI N (miStep encodedRules (MIVar v)) = MINoStep ∧
      ∀ k, k < N →
        StepActiveShape (eval pMI k (miStep encodedRules (MIVar v))) := by
  have hroot := miRoot_source_raw_active_sim_var rws v encodedRules hrules
  simp only [hcase] at hroot
  obtain ⟨rootFuel, hrootEval, hrootActive⟩ := hroot
  exact miStep_eval_of_root_none_active_mivar_with_guard encodedRules v
    rootFuel
    (encRules?_some_normal rws encodedRules hrules)
    hrootEval hrootActive

theorem miStep_source_root_none_sim_sym_with_guard (rws : List RewriteDecl)
    (s : String) (encodedRules : AST)
    (hrules : encRules? rws = some encodedRules)
    (hcase : rootBaseStep? rws (.sexp (.id s) []) = none) :
    ∃ N, eval pMI N (miStep encodedRules (MISym s)) = MINoStep ∧
      ∀ k, k < N →
        StepActiveShape (eval pMI k (miStep encodedRules (MISym s))) := by
  have hroot := miRoot_source_raw_active_sim_sym rws s encodedRules hrules
  simp only [hcase] at hroot
  obtain ⟨rootFuel, hrootEval, hrootActive⟩ := hroot
  exact miStep_eval_of_root_none_active_misym_with_guard encodedRules s
    rootFuel
    (encRules?_some_normal rws encodedRules hrules)
    hrootEval hrootActive

theorem miStep_source_root_none_app_args_step_sim_with_guard
    (rws : List RewriteDecl)
    (headName : String) (a : AST) (rest : List AST)
    (encodedRules encodedArgs argsOut : AST) (argsFuel : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hargsEnc : encASTList? (a :: rest) = some encodedArgs)
    (hhead : (headName == "match") = false)
    (hcase : rootBaseStep? rws (.sexp (.id headName) (a :: rest)) = none)
    (hargs : eval pMI argsFuel (miStepArgs encodedRules encodedArgs) =
      MIArgsStep argsOut)
    (hargsActive : ∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs encodedRules encodedArgs))) :
    ∃ N,
      eval pMI N (miStep encodedRules (MIApp headName encodedArgs)) =
        MIStep (MIApp headName argsOut) ∧
      ∀ k, k < N →
        StepActiveShape
          (eval pMI k (miStep encodedRules (MIApp headName encodedArgs))) := by
  have hroot :=
    miRoot_source_raw_active_sim_app_head_ne rws headName a rest
      encodedRules encodedArgs hrules hargsEnc hhead
  simp only [hcase] at hroot
  obtain ⟨rootFuel, hrootEval, hrootActive⟩ := hroot
  exact miStep_eval_of_root_none_active_miapp_args_step_with_guard
    encodedRules encodedArgs argsOut headName rootFuel argsFuel
    (encRules?_some_normal rws encodedRules hrules)
    (encASTList?_some_normal (a :: rest) encodedArgs hargsEnc)
    hrootEval hrootActive hargs hargsActive

theorem miStep_source_root_none_app_args_none_sim_with_guard
    (rws : List RewriteDecl)
    (headName : String) (a : AST) (rest : List AST)
    (encodedRules encodedArgs : AST) (argsFuel : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hargsEnc : encASTList? (a :: rest) = some encodedArgs)
    (hhead : (headName == "match") = false)
    (hcase : rootBaseStep? rws (.sexp (.id headName) (a :: rest)) = none)
    (hargs : eval pMI argsFuel (miStepArgs encodedRules encodedArgs) =
      MINoArgsStep)
    (hargsActive : ∀ k, k < argsFuel →
      ArgsActiveShape (eval pMI k (miStepArgs encodedRules encodedArgs))) :
    ∃ N,
      eval pMI N (miStep encodedRules (MIApp headName encodedArgs)) =
        MINoStep ∧
      ∀ k, k < N →
        StepActiveShape
          (eval pMI k (miStep encodedRules (MIApp headName encodedArgs))) := by
  have hroot :=
    miRoot_source_raw_active_sim_app_head_ne rws headName a rest
      encodedRules encodedArgs hrules hargsEnc hhead
  simp only [hcase] at hroot
  obtain ⟨rootFuel, hrootEval, hrootActive⟩ := hroot
  exact miStep_eval_of_root_none_active_miapp_args_none_with_guard
    encodedRules encodedArgs headName rootFuel argsFuel
    (encRules?_some_normal rws encodedRules hrules)
    (encASTList?_some_normal (a :: rest) encodedArgs hargsEnc)
    hrootEval hrootActive hargs hargsActive

theorem miStep_source_root_some_rawsome_var (rws : List RewriteDecl)
    (v : String) (encodedRules out : AST)
    (hrules : encRules? rws = some encodedRules)
    (hcase : rootBaseStep? rws (.var (.base v)) = some out) :
    StepRawSome encodedRules (MIVar v) out := by
  simpa [StepRawSome] using
    miStep_source_root_some_raw_active_sim_var rws v encodedRules out
      hrules hcase

theorem miStep_source_root_some_rawsome_sym (rws : List RewriteDecl)
    (s : String) (encodedRules out : AST)
    (hrules : encRules? rws = some encodedRules)
    (hcase : rootBaseStep? rws (.sexp (.id s) []) = some out) :
    StepRawSome encodedRules (MISym s) out := by
  simpa [StepRawSome] using
    miStep_source_root_some_raw_active_sim_sym rws s encodedRules out
      hrules hcase

theorem miStep_source_root_some_rawsome_app_head_ne
    (rws : List RewriteDecl)
    (headName : String) (a : AST) (rest : List AST)
    (encodedRules encodedArgs out : AST)
    (hrules : encRules? rws = some encodedRules)
    (hargs : encASTList? (a :: rest) = some encodedArgs)
    (hhead : (headName == "match") = false)
    (hcase : rootBaseStep? rws (.sexp (.id headName) (a :: rest)) =
      some out) :
    StepRawSome encodedRules (MIApp headName encodedArgs) out := by
  simpa [StepRawSome] using
    miStep_source_root_some_raw_active_sim_app_head_ne rws headName a rest
      encodedRules encodedArgs out hrules hargs hhead hcase

theorem miStep_source_root_some_rawsome_var_payload
    (rws : List RewriteDecl)
    (v : String) (encodedRules out : AST)
    (hrules : encRules? rws = some encodedRules)
    (hcase : rootBaseStep? rws (.var (.base v)) = some out) :
    StepRawSomePayload encodedRules (MIVar v) out := by
  have hroot :=
    miRoot_source_raw_active_sim_var_payload rws v encodedRules hrules
  simp only [hcase] at hroot
  obtain ⟨rawNext, encodedOut, rootFuel, substFuel, hout, hrootEval,
    hrootActive, hsubst, houtNorm, hpayload⟩ := hroot
  obtain ⟨Nstep, hstep, hstepActive⟩ :=
    miStep_eval_of_root_active_mivar_with_guard encodedRules rawNext v
      rootFuel
      (encRules?_some_normal rws encodedRules hrules)
      hrootEval hrootActive
  unfold StepRawSomePayload
  exact ⟨rawNext, encodedOut, Nstep, substFuel, hout, hstep,
    hstepActive, hsubst, houtNorm, hpayload⟩

theorem miStep_source_root_some_rawsome_sym_payload
    (rws : List RewriteDecl)
    (s : String) (encodedRules out : AST)
    (hrules : encRules? rws = some encodedRules)
    (hcase : rootBaseStep? rws (.sexp (.id s) []) = some out) :
    StepRawSomePayload encodedRules (MISym s) out := by
  have hroot :=
    miRoot_source_raw_active_sim_sym_payload rws s encodedRules hrules
  simp only [hcase] at hroot
  obtain ⟨rawNext, encodedOut, rootFuel, substFuel, hout, hrootEval,
    hrootActive, hsubst, houtNorm, hpayload⟩ := hroot
  obtain ⟨Nstep, hstep, hstepActive⟩ :=
    miStep_eval_of_root_active_misym_with_guard encodedRules rawNext s
      rootFuel
      (encRules?_some_normal rws encodedRules hrules)
      hrootEval hrootActive
  unfold StepRawSomePayload
  exact ⟨rawNext, encodedOut, Nstep, substFuel, hout, hstep,
    hstepActive, hsubst, houtNorm, hpayload⟩

theorem miStep_source_root_some_rawsome_app_head_ne_payload
    (rws : List RewriteDecl)
    (headName : String) (a : AST) (rest : List AST)
    (encodedRules encodedArgs out : AST)
    (hrules : encRules? rws = some encodedRules)
    (hargs : encASTList? (a :: rest) = some encodedArgs)
    (hhead : (headName == "match") = false)
    (hcase : rootBaseStep? rws (.sexp (.id headName) (a :: rest)) =
      some out) :
    StepRawSomePayload encodedRules (MIApp headName encodedArgs) out := by
  have hroot :=
    miRoot_source_raw_active_sim_app_head_ne_payload rws headName a rest
      encodedRules encodedArgs hrules hargs hhead
  simp only [hcase] at hroot
  obtain ⟨rawNext, encodedOut, rootFuel, substFuel, hout, hrootEval,
    hrootActive, hsubst, houtNorm, hpayload⟩ := hroot
  obtain ⟨Nstep, hstep, hstepActive⟩ :=
    miStep_eval_of_root_active_miapp_with_guard encodedRules encodedArgs
      rawNext headName rootFuel
      (encRules?_some_normal rws encodedRules hrules)
      (encASTList?_some_normal (a :: rest) encodedArgs hargs)
      hrootEval hrootActive
  unfold StepRawSomePayload
  exact ⟨rawNext, encodedOut, Nstep, substFuel, hout, hstep,
    hstepActive, hsubst, houtNorm, hpayload⟩

theorem miStep_source_root_none_rawnone_var (rws : List RewriteDecl)
    (v : String) (encodedRules : AST)
    (hrules : encRules? rws = some encodedRules)
    (hcase : rootBaseStep? rws (.var (.base v)) = none) :
    StepRawNone encodedRules (MIVar v) := by
  simpa [StepRawNone] using
    miStep_source_root_none_sim_var_with_guard rws v encodedRules hrules hcase

theorem miStep_source_root_none_rawnone_sym (rws : List RewriteDecl)
    (s : String) (encodedRules : AST)
    (hrules : encRules? rws = some encodedRules)
    (hcase : rootBaseStep? rws (.sexp (.id s) []) = none) :
    StepRawNone encodedRules (MISym s) := by
  simpa [StepRawNone] using
    miStep_source_root_none_sim_sym_with_guard rws s encodedRules hrules hcase

theorem miStepArgs_source_nil_rawnone (encodedRules : AST) :
    ArgsRawNone encodedRules MINil := by
  unfold ArgsRawNone
  obtain ⟨hnil, hactive⟩ := miStepArgs_nil_active_sim encodedRules
  exact ⟨1, hnil, hactive⟩

theorem miStepArgs_source_cons_of_head_rawsome
    (encodedRules encodedT encodedTs : AST) (tOut : AST) (ts : List AST)
    (hrulesNorm : IsNormal pMI encodedRules)
    (htNorm : IsNormal pMI encodedT)
    (hts : encASTList? ts = some encodedTs)
    (hhead : StepRawSome encodedRules encodedT tOut) :
    ArgsRawSome encodedRules (MICons encodedT encodedTs) (tOut :: ts) := by
  unfold StepRawSome at hhead
  obtain ⟨rawNext, encodedOut, stepFuel, normFuel, hout, hstep,
    hstepActive, hnorm, houtNorm⟩ := hhead
  obtain ⟨argsFuel, hargs, hargsActive⟩ :=
    miStepArgs_cons_eval_of_head_step_active encodedRules encodedT
      encodedTs rawNext stepFuel hrulesNorm htNorm
      (encASTList?_some_normal ts encodedTs hts)
      hstep hstepActive
  obtain ⟨normArgsFuel, hnormArgs⟩ :=
    miCons_head_eval_of rawNext encodedOut encodedTs normFuel hnorm
      houtNorm
  unfold ArgsRawSome
  refine ⟨MICons rawNext encodedTs, MICons encodedOut encodedTs,
    argsFuel, normArgsFuel, ?_, hargs, hargsActive, hnormArgs, ?_⟩
  · simp only [encASTList?, hout, hts]
  · exact normal_MICons encodedOut encodedTs houtNorm
      (encASTList?_some_normal ts encodedTs hts)

theorem miStepArgs_source_cons_of_head_rawsome_payload
    (encodedRules encodedT encodedTs : AST) (tOut : AST) (ts : List AST)
    (hrulesNorm : IsNormal pMI encodedRules)
    (htNorm : IsNormal pMI encodedT)
    (hts : encASTList? ts = some encodedTs)
    (hhead : StepRawSomePayload encodedRules encodedT tOut) :
    ArgsRawSomePayload encodedRules (MICons encodedT encodedTs)
      (tOut :: ts) := by
  unfold StepRawSomePayload at hhead
  obtain ⟨rawNext, encodedOut, stepFuel, normFuel, hout, hstep,
    hstepActive, hnorm, houtNorm, hpayload⟩ := hhead
  obtain ⟨argsFuel, hargs, hargsActive⟩ :=
    miStepArgs_cons_eval_of_head_step_active encodedRules encodedT
      encodedTs rawNext stepFuel hrulesNorm htNorm
      (encASTList?_some_normal ts encodedTs hts)
      hstep hstepActive
  obtain ⟨normArgsFuel, hnormArgs⟩ :=
    miCons_head_eval_of rawNext encodedOut encodedTs normFuel hnorm
      houtNorm
  unfold ArgsRawSomePayload
  refine ⟨MICons rawNext encodedTs, MICons encodedOut encodedTs,
    argsFuel, normArgsFuel, ?_, hargs, hargsActive, hnormArgs, ?_, ?_⟩
  · simp only [encASTList?, hout, hts]
  · exact normal_MICons encodedOut encodedTs houtNorm
      (encASTList?_some_normal ts encodedTs hts)
  · exact RawArgsPayload.consHead hpayload

theorem miStepArgs_source_cons_of_head_rawnone_rest_rawsome
    (encodedRules encodedT encodedTs : AST) (t : AST)
    (tailOut : List AST)
    (hrulesNorm : IsNormal pMI encodedRules)
    (htNorm : IsNormal pMI encodedT)
    (htailNorm : IsNormal pMI encodedTs)
    (ht : encAST? t = some encodedT)
    (hhead : StepRawNone encodedRules encodedT)
    (hrest : ArgsRawSome encodedRules encodedTs tailOut) :
    ArgsRawSome encodedRules (MICons encodedT encodedTs) (t :: tailOut) := by
  unfold StepRawNone at hhead
  unfold ArgsRawSome at hrest
  obtain ⟨headFuel, hheadEval, hheadActive⟩ := hhead
  obtain ⟨rawTail, encodedTailOut, restFuel, normFuel, htailOut,
    hrestEval, hrestActive, hnorm, htailOutNorm⟩ := hrest
  obtain ⟨argsFuel, hargs, hargsActive⟩ :=
    miStepArgs_cons_eval_of_head_none_rest_step_active
      encodedRules encodedT encodedTs rawTail headFuel restFuel
      hrulesNorm htNorm htailNorm hheadEval hheadActive
      hrestEval hrestActive
  obtain ⟨normArgsFuel, hnormArgs⟩ :=
    miCons_tail_eval_of encodedT rawTail encodedTailOut normFuel
      htNorm hnorm htailOutNorm
  unfold ArgsRawSome
  refine ⟨MICons encodedT rawTail, MICons encodedT encodedTailOut,
    argsFuel, normArgsFuel, ?_, hargs, hargsActive, hnormArgs, ?_⟩
  · simp only [encASTList?, ht, htailOut]
  · exact normal_MICons encodedT encodedTailOut htNorm htailOutNorm

theorem miStepArgs_source_cons_of_head_rawnone_rest_rawsome_payload
    (encodedRules encodedT encodedTs : AST) (t : AST)
    (tailOut : List AST)
    (hrulesNorm : IsNormal pMI encodedRules)
    (htNorm : IsNormal pMI encodedT)
    (htailNorm : IsNormal pMI encodedTs)
    (ht : encAST? t = some encodedT)
    (hhead : StepRawNone encodedRules encodedT)
    (hrest : ArgsRawSomePayload encodedRules encodedTs tailOut) :
    ArgsRawSomePayload encodedRules (MICons encodedT encodedTs)
      (t :: tailOut) := by
  unfold StepRawNone at hhead
  unfold ArgsRawSomePayload at hrest
  obtain ⟨headFuel, hheadEval, hheadActive⟩ := hhead
  obtain ⟨rawTail, encodedTailOut, restFuel, normFuel, htailOut,
    hrestEval, hrestActive, hnorm, htailOutNorm, hpayload⟩ := hrest
  obtain ⟨argsFuel, hargs, hargsActive⟩ :=
    miStepArgs_cons_eval_of_head_none_rest_step_active
      encodedRules encodedT encodedTs rawTail headFuel restFuel
      hrulesNorm htNorm htailNorm hheadEval hheadActive
      hrestEval hrestActive
  obtain ⟨normArgsFuel, hnormArgs⟩ :=
    miCons_tail_eval_of encodedT rawTail encodedTailOut normFuel
      htNorm hnorm htailOutNorm
  unfold ArgsRawSomePayload
  refine ⟨MICons encodedT rawTail, MICons encodedT encodedTailOut,
    argsFuel, normArgsFuel, ?_, hargs, hargsActive, hnormArgs, ?_, ?_⟩
  · simp only [encASTList?, ht, htailOut]
  · exact normal_MICons encodedT encodedTailOut htNorm htailOutNorm
  · exact RawArgsPayload.consTail hpayload

theorem miStepArgs_source_cons_of_head_rawnone_rest_rawnone
    (encodedRules encodedT encodedTs : AST)
    (hrulesNorm : IsNormal pMI encodedRules)
    (htNorm : IsNormal pMI encodedT)
    (htailNorm : IsNormal pMI encodedTs)
    (hhead : StepRawNone encodedRules encodedT)
    (hrest : ArgsRawNone encodedRules encodedTs) :
    ArgsRawNone encodedRules (MICons encodedT encodedTs) := by
  unfold StepRawNone at hhead
  unfold ArgsRawNone at hrest
  obtain ⟨headFuel, hheadEval, hheadActive⟩ := hhead
  obtain ⟨restFuel, hrestEval, hrestActive⟩ := hrest
  obtain ⟨argsFuel, hargs, hargsActive⟩ :=
    miStepArgs_cons_eval_of_head_none_rest_none_active
      encodedRules encodedT encodedTs headFuel restFuel
      hrulesNorm htNorm htailNorm hheadEval hheadActive
      hrestEval hrestActive
  exact ⟨argsFuel, hargs, hargsActive⟩

theorem miStep_source_root_none_app_args_rawsome_with_guard
    (rws : List RewriteDecl)
    (headName : String) (a : AST) (rest : List AST)
    (argOutHead : AST) (argOutRest : List AST)
    (encodedRules encodedArgs : AST)
    (hrules : encRules? rws = some encodedRules)
    (hargsEnc : encASTList? (a :: rest) = some encodedArgs)
    (hhead : (headName == "match") = false)
    (hcase : rootBaseStep? rws (.sexp (.id headName) (a :: rest)) = none)
    (hargs : ArgsRawSome encodedRules encodedArgs (argOutHead :: argOutRest)) :
    StepRawSome encodedRules (MIApp headName encodedArgs)
      (.sexp (.id headName) (argOutHead :: argOutRest)) := by
  unfold ArgsRawSome at hargs
  obtain ⟨rawArgs, encodedArgsOut, argsFuel, normFuel, hargsOutEnc,
    hargsEval, hargsActive, hnorm, hargsOutNorm⟩ := hargs
  obtain ⟨stepFuel, hstep, hstepActive⟩ :=
    miStep_source_root_none_app_args_step_sim_with_guard rws headName
      a rest encodedRules encodedArgs rawArgs argsFuel hrules hargsEnc
      hhead hcase hargsEval hargsActive
  obtain ⟨normStepFuel, hnormStep⟩ :=
    miApp_args_eval_of headName rawArgs encodedArgsOut normFuel hnorm
      hargsOutNorm
  unfold StepRawSome
  refine ⟨MIApp headName rawArgs, MIApp headName encodedArgsOut,
    stepFuel, normStepFuel, ?_, hstep, hstepActive, hnormStep, ?_⟩
  · simp only [encAST?, hargsOutEnc]
  · exact normal_MIApp headName encodedArgsOut hargsOutNorm

theorem miStep_source_root_none_app_args_rawsome_with_guard_payload
    (rws : List RewriteDecl)
    (headName : String) (a : AST) (rest : List AST)
    (argOutHead : AST) (argOutRest : List AST)
    (encodedRules encodedArgs : AST)
    (hrules : encRules? rws = some encodedRules)
    (hargsEnc : encASTList? (a :: rest) = some encodedArgs)
    (hhead : (headName == "match") = false)
    (hcase : rootBaseStep? rws (.sexp (.id headName) (a :: rest)) = none)
    (hargs : ArgsRawSomePayload encodedRules encodedArgs
      (argOutHead :: argOutRest)) :
    StepRawSomePayload encodedRules (MIApp headName encodedArgs)
      (.sexp (.id headName) (argOutHead :: argOutRest)) := by
  unfold ArgsRawSomePayload at hargs
  obtain ⟨rawArgs, encodedArgsOut, argsFuel, normFuel, hargsOutEnc,
    hargsEval, hargsActive, hnorm, hargsOutNorm, hpayload⟩ := hargs
  obtain ⟨stepFuel, hstep, hstepActive⟩ :=
    miStep_source_root_none_app_args_step_sim_with_guard rws headName
      a rest encodedRules encodedArgs rawArgs argsFuel hrules hargsEnc
      hhead hcase hargsEval hargsActive
  obtain ⟨normStepFuel, hnormStep⟩ :=
    miApp_args_eval_of headName rawArgs encodedArgsOut normFuel hnorm
      hargsOutNorm
  unfold StepRawSomePayload
  refine ⟨MIApp headName rawArgs, MIApp headName encodedArgsOut,
    stepFuel, normStepFuel, ?_, hstep, hstepActive, hnormStep, ?_, ?_⟩
  · simp only [encAST?, hargsOutEnc]
  · exact normal_MIApp headName encodedArgsOut hargsOutNorm
  · exact RawTermPayload.app headName hpayload

theorem miStep_source_root_none_app_args_rawnone_with_guard
    (rws : List RewriteDecl)
    (headName : String) (a : AST) (rest : List AST)
    (encodedRules encodedArgs : AST)
    (hrules : encRules? rws = some encodedRules)
    (hargsEnc : encASTList? (a :: rest) = some encodedArgs)
    (hhead : (headName == "match") = false)
    (hcase : rootBaseStep? rws (.sexp (.id headName) (a :: rest)) = none)
    (hargs : ArgsRawNone encodedRules encodedArgs) :
    StepRawNone encodedRules (MIApp headName encodedArgs) := by
  unfold ArgsRawNone at hargs
  obtain ⟨argsFuel, hargsEval, hargsActive⟩ := hargs
  simpa [StepRawNone] using
    miStep_source_root_none_app_args_none_sim_with_guard rws headName
      a rest encodedRules encodedArgs argsFuel hrules hargsEnc hhead
      hcase hargsEval hargsActive

theorem step_argsBaseStepFuel_source_raw_active_sim :
    ∀ fuel,
      (∀ (rws : List RewriteDecl) (term encodedRules encodedTerm : AST),
        encRules? rws = some encodedRules →
        encAST? term = some encodedTerm →
        noQueryAST term = true →
        astFuel term < fuel →
        match stepBaseStepFuel? rws fuel term with
        | some out => StepRawSome encodedRules encodedTerm out
        | none => StepRawNone encodedRules encodedTerm) ∧
      (∀ (rws : List RewriteDecl) (args : List AST)
          (encodedRules encodedArgs : AST),
        encRules? rws = some encodedRules →
        encASTList? args = some encodedArgs →
        noQueryASTList args = true →
        astListFuel args < fuel →
        match argsBaseStepFuel? rws fuel args with
        | some out => ArgsRawSome encodedRules encodedArgs out
        | none => ArgsRawNone encodedRules encodedArgs) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro rws term encodedRules encodedTerm hrules hterm hno hfuel
        exact False.elim (Nat.not_lt_zero _ hfuel)
      · intro rws args encodedRules encodedArgs hrules hargs hno hfuel
        exact False.elim (Nat.not_lt_zero _ hfuel)
  | succ fuel ih =>
      constructor
      · intro rws term encodedRules encodedTerm hrules hterm hno hfuel
        cases term with
        | var path =>
            cases path with
            | base v =>
                simp only [encAST?] at hterm
                cases hterm
                cases hcase : rootBaseStep? rws (.var (.base v)) with
                | some out =>
                    simpa [stepBaseStepFuel?, hcase] using
                      miStep_source_root_some_rawsome_var rws v
                        encodedRules out hrules hcase
                | none =>
                    simpa [stepBaseStepFuel?, hcase] using
                      miStep_source_root_none_rawnone_var rws v
                        encodedRules hrules hcase
            | qualified ident rest =>
                simp only [encAST?] at hterm
                cases hterm
        | sexp label args =>
            cases label with
            | id headName =>
                cases args with
                | nil =>
                    simp only [encAST?] at hterm
                    cases hterm
                    cases hcase :
                        rootBaseStep? rws (.sexp (.id headName) []) with
                    | some out =>
                        simpa [stepBaseStepFuel?, hcase] using
                          miStep_source_root_some_rawsome_sym rws headName
                            encodedRules out hrules hcase
                    | none =>
                        have hargsNil :
                            argsBaseStepFuel? rws fuel [] = none := by
                          cases fuel <;> simp [argsBaseStepFuel?]
                        simpa [stepBaseStepFuel?, hcase, hargsNil] using
                          miStep_source_root_none_rawnone_sym rws headName
                            encodedRules hrules hcase
                | cons a rest =>
                    cases hargsEnc : encASTList? (a :: rest) with
                    | none =>
                        simp only [encAST?, hargsEnc] at hterm
                        cases hterm
                    | some encodedArgs =>
                        simp only [encAST?, hargsEnc] at hterm
                        cases hterm
                        have hnoApp :
                            (((headName == "match") == false) &&
                              noQueryASTList (a :: rest)) = true := by
                          simpa only [noQueryAST] using hno
                        have hheadB :
                            ((headName == "match") == false) = true := by
                          cases hm : ((headName == "match") == false) <;>
                            simp [hm] at hnoApp ⊢
                        have hhead :
                            (headName == "match") = false := by
                          cases hhm : (headName == "match") <;>
                            simp [hhm] at hheadB ⊢
                        have hnoArgs :
                            noQueryASTList (a :: rest) = true := by
                          cases hm : ((headName == "match") == false)
                          · simp [hm] at hnoApp
                          · simpa [hm] using hnoApp
                        have hargsFuel : astListFuel (a :: rest) < fuel := by
                          simp only [astFuel] at hfuel
                          omega
                        cases hroot :
                            rootBaseStep? rws
                              (.sexp (.id headName) (a :: rest)) with
                        | some out =>
                            simpa [stepBaseStepFuel?, hroot] using
                              miStep_source_root_some_rawsome_app_head_ne
                                rws headName a rest encodedRules encodedArgs
                                out hrules hargsEnc hhead hroot
                        | none =>
                            have hargsSim := ih.2 rws (a :: rest)
                              encodedRules encodedArgs hrules hargsEnc
                              hnoArgs hargsFuel
                            cases hargsStep :
                                argsBaseStepFuel? rws fuel (a :: rest) with
                            | some argsOut =>
                                have hargsSome :
                                    ArgsRawSome encodedRules encodedArgs
                                      argsOut := by
                                  simpa [hargsStep] using hargsSim
                                rcases
                                  argsBaseStepFuel?_cons_some_nonempty
                                    rws fuel a rest argsOut hargsStep with
                                  ⟨argOutHead, argOutRest, rfl⟩
                                simpa [stepBaseStepFuel?, hroot, hargsStep] using
                                  miStep_source_root_none_app_args_rawsome_with_guard
                                    rws headName a rest argOutHead argOutRest
                                    encodedRules encodedArgs hrules hargsEnc
                                    hhead hroot hargsSome
                            | none =>
                                have hargsNone :
                                    ArgsRawNone encodedRules encodedArgs := by
                                  simpa [hargsStep] using hargsSim
                                simpa [stepBaseStepFuel?, hroot, hargsStep] using
                                  miStep_source_root_none_app_args_rawnone_with_guard
                                    rws headName a rest encodedRules
                                    encodedArgs hrules hargsEnc hhead hroot
                                    hargsNone
            | wild =>
                simp only [encAST?] at hterm
                cases hterm
            | listE c =>
                simp only [encAST?] at hterm
                cases hterm
            | listCons c =>
                simp only [encAST?] at hterm
                cases hterm
            | listOne c =>
                simp only [encAST?] at hterm
                cases hterm
        | subst body repl v =>
            simp only [encAST?] at hterm
            cases hterm
      · intro rws args encodedRules encodedArgs hrules hargs hno hfuel
        cases args with
        | nil =>
            simp only [encASTList?] at hargs
            cases hargs
            simpa [argsBaseStepFuel?] using
              miStepArgs_source_nil_rawnone encodedRules
        | cons t ts =>
            cases htEnc : encAST? t with
            | none =>
                simp only [encASTList?, htEnc] at hargs
                cases hargs
            | some encodedT =>
                cases htsEnc : encASTList? ts with
                | none =>
                    simp only [encASTList?, htEnc, htsEnc] at hargs
                    cases hargs
                | some encodedTs =>
                    simp only [encASTList?, htEnc, htsEnc] at hargs
                    cases hargs
                    have hnoCons :
                        noQueryAST t && noQueryASTList ts = true := by
                      simpa [noQueryASTList] using hno
                    have htNo : noQueryAST t = true := by
                      cases ht : noQueryAST t <;>
                        simp [ht] at hnoCons ⊢
                    have htsNo : noQueryASTList ts = true := by
                      cases ht : noQueryAST t
                      · simp [ht] at hnoCons
                      · simpa [ht] using hnoCons
                    have htFuel : astFuel t < fuel := by
                      simp only [astListFuel] at hfuel
                      omega
                    have htsFuel : astListFuel ts < fuel := by
                      simp only [astListFuel] at hfuel
                      omega
                    have hheadSim := ih.1 rws t encodedRules encodedT
                      hrules htEnc htNo htFuel
                    cases hstep : stepBaseStepFuel? rws fuel t with
                    | some tOut =>
                        have hheadSome :
                            StepRawSome encodedRules encodedT tOut := by
                          simpa [hstep] using hheadSim
                        simpa [argsBaseStepFuel?, hstep] using
                          miStepArgs_source_cons_of_head_rawsome
                            encodedRules encodedT encodedTs tOut ts
                            (encRules?_some_normal rws encodedRules hrules)
                            (encAST?_some_normal t encodedT htEnc)
                            htsEnc hheadSome
                    | none =>
                        have hheadNone :
                            StepRawNone encodedRules encodedT := by
                          simpa [hstep] using hheadSim
                        have hrestSim := ih.2 rws ts encodedRules
                          encodedTs hrules htsEnc htsNo htsFuel
                        cases htail :
                            argsBaseStepFuel? rws fuel ts with
                        | some tailOut =>
                            have htailSome :
                                ArgsRawSome encodedRules encodedTs
                                  tailOut := by
                              simpa [htail] using hrestSim
                            simpa [argsBaseStepFuel?, hstep, htail] using
                              miStepArgs_source_cons_of_head_rawnone_rest_rawsome
                                encodedRules encodedT encodedTs t tailOut
                                (encRules?_some_normal rws encodedRules hrules)
                                (encAST?_some_normal t encodedT htEnc)
                                (encASTList?_some_normal ts encodedTs htsEnc)
                                htEnc hheadNone htailSome
                        | none =>
                            have htailNone :
                                ArgsRawNone encodedRules encodedTs := by
                              simpa [htail] using hrestSim
                            simpa [argsBaseStepFuel?, hstep, htail] using
                              miStepArgs_source_cons_of_head_rawnone_rest_rawnone
                                encodedRules encodedT encodedTs
                                (encRules?_some_normal rws encodedRules hrules)
                                (encAST?_some_normal t encodedT htEnc)
                                (encASTList?_some_normal ts encodedTs htsEnc)
                                hheadNone htailNone

theorem step_argsBaseStepFuel_source_raw_active_payload_sim :
    ∀ fuel,
      (∀ (rws : List RewriteDecl) (term encodedRules encodedTerm : AST),
        encRules? rws = some encodedRules →
        encAST? term = some encodedTerm →
        noQueryAST term = true →
        astFuel term < fuel →
        match stepBaseStepFuel? rws fuel term with
        | some out => StepRawSomePayload encodedRules encodedTerm out
        | none => StepRawNone encodedRules encodedTerm) ∧
      (∀ (rws : List RewriteDecl) (args : List AST)
          (encodedRules encodedArgs : AST),
        encRules? rws = some encodedRules →
        encASTList? args = some encodedArgs →
        noQueryASTList args = true →
        astListFuel args < fuel →
        match argsBaseStepFuel? rws fuel args with
        | some out => ArgsRawSomePayload encodedRules encodedArgs out
        | none => ArgsRawNone encodedRules encodedArgs) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro rws term encodedRules encodedTerm hrules hterm hno hfuel
        exact False.elim (Nat.not_lt_zero _ hfuel)
      · intro rws args encodedRules encodedArgs hrules hargs hno hfuel
        exact False.elim (Nat.not_lt_zero _ hfuel)
  | succ fuel ih =>
      constructor
      · intro rws term encodedRules encodedTerm hrules hterm hno hfuel
        cases term with
        | var path =>
            cases path with
            | base v =>
                simp only [encAST?] at hterm
                cases hterm
                cases hcase : rootBaseStep? rws (.var (.base v)) with
                | some out =>
                    simpa [stepBaseStepFuel?, hcase] using
                      miStep_source_root_some_rawsome_var_payload rws v
                        encodedRules out hrules hcase
                | none =>
                    simpa [stepBaseStepFuel?, hcase] using
                      miStep_source_root_none_rawnone_var rws v
                        encodedRules hrules hcase
            | qualified ident rest =>
                simp only [encAST?] at hterm
                cases hterm
        | sexp label args =>
            cases label with
            | id headName =>
                cases args with
                | nil =>
                    simp only [encAST?] at hterm
                    cases hterm
                    cases hcase :
                        rootBaseStep? rws (.sexp (.id headName) []) with
                    | some out =>
                        simpa [stepBaseStepFuel?, hcase] using
                          miStep_source_root_some_rawsome_sym_payload rws
                            headName encodedRules out hrules hcase
                    | none =>
                        have hargsNil :
                            argsBaseStepFuel? rws fuel [] = none := by
                          cases fuel <;> simp [argsBaseStepFuel?]
                        simpa [stepBaseStepFuel?, hcase, hargsNil] using
                          miStep_source_root_none_rawnone_sym rws headName
                            encodedRules hrules hcase
                | cons a rest =>
                    cases hargsEnc : encASTList? (a :: rest) with
                    | none =>
                        simp only [encAST?, hargsEnc] at hterm
                        cases hterm
                    | some encodedArgs =>
                        simp only [encAST?, hargsEnc] at hterm
                        cases hterm
                        have hnoApp :
                            (((headName == "match") == false) &&
                              noQueryASTList (a :: rest)) = true := by
                          simpa only [noQueryAST] using hno
                        have hheadB :
                            ((headName == "match") == false) = true := by
                          cases hm : ((headName == "match") == false) <;>
                            simp [hm] at hnoApp ⊢
                        have hhead :
                            (headName == "match") = false := by
                          cases hhm : (headName == "match") <;>
                            simp [hhm] at hheadB ⊢
                        have hnoArgs :
                            noQueryASTList (a :: rest) = true := by
                          cases hm : ((headName == "match") == false)
                          · simp [hm] at hnoApp
                          · simpa [hm] using hnoApp
                        have hargsFuel : astListFuel (a :: rest) < fuel := by
                          simp only [astFuel] at hfuel
                          omega
                        cases hroot :
                            rootBaseStep? rws
                              (.sexp (.id headName) (a :: rest)) with
                        | some out =>
                            simpa [stepBaseStepFuel?, hroot] using
                              miStep_source_root_some_rawsome_app_head_ne_payload
                                rws headName a rest encodedRules encodedArgs
                                out hrules hargsEnc hhead hroot
                        | none =>
                            have hargsSim := ih.2 rws (a :: rest)
                              encodedRules encodedArgs hrules hargsEnc
                              hnoArgs hargsFuel
                            cases hargsStep :
                                argsBaseStepFuel? rws fuel (a :: rest) with
                            | some argsOut =>
                                have hargsSome :
                                    ArgsRawSomePayload encodedRules encodedArgs
                                      argsOut := by
                                  simpa [hargsStep] using hargsSim
                                rcases
                                  argsBaseStepFuel?_cons_some_nonempty
                                    rws fuel a rest argsOut hargsStep with
                                  ⟨argOutHead, argOutRest, rfl⟩
                                simpa [stepBaseStepFuel?, hroot, hargsStep] using
                                  miStep_source_root_none_app_args_rawsome_with_guard_payload
                                    rws headName a rest argOutHead argOutRest
                                    encodedRules encodedArgs hrules hargsEnc
                                    hhead hroot hargsSome
                            | none =>
                                have hargsNone :
                                    ArgsRawNone encodedRules encodedArgs := by
                                  simpa [hargsStep] using hargsSim
                                simpa [stepBaseStepFuel?, hroot, hargsStep] using
                                  miStep_source_root_none_app_args_rawnone_with_guard
                                    rws headName a rest encodedRules
                                    encodedArgs hrules hargsEnc hhead hroot
                                    hargsNone
            | wild =>
                simp only [encAST?] at hterm
                cases hterm
            | listE c =>
                simp only [encAST?] at hterm
                cases hterm
            | listCons c =>
                simp only [encAST?] at hterm
                cases hterm
            | listOne c =>
                simp only [encAST?] at hterm
                cases hterm
        | subst body repl v =>
            simp only [encAST?] at hterm
            cases hterm
      · intro rws args encodedRules encodedArgs hrules hargs hno hfuel
        cases args with
        | nil =>
            simp only [encASTList?] at hargs
            cases hargs
            simpa [argsBaseStepFuel?] using
              miStepArgs_source_nil_rawnone encodedRules
        | cons t ts =>
            cases htEnc : encAST? t with
            | none =>
                simp only [encASTList?, htEnc] at hargs
                cases hargs
            | some encodedT =>
                cases htsEnc : encASTList? ts with
                | none =>
                    simp only [encASTList?, htEnc, htsEnc] at hargs
                    cases hargs
                | some encodedTs =>
                    simp only [encASTList?, htEnc, htsEnc] at hargs
                    cases hargs
                    have hnoCons :
                        noQueryAST t && noQueryASTList ts = true := by
                      simpa [noQueryASTList] using hno
                    have htNo : noQueryAST t = true := by
                      cases ht : noQueryAST t <;>
                        simp [ht] at hnoCons ⊢
                    have htsNo : noQueryASTList ts = true := by
                      cases ht : noQueryAST t
                      · simp [ht] at hnoCons
                      · simpa [ht] using hnoCons
                    have htFuel : astFuel t < fuel := by
                      simp only [astListFuel] at hfuel
                      omega
                    have htsFuel : astListFuel ts < fuel := by
                      simp only [astListFuel] at hfuel
                      omega
                    have hheadSim := ih.1 rws t encodedRules encodedT
                      hrules htEnc htNo htFuel
                    cases hstep : stepBaseStepFuel? rws fuel t with
                    | some tOut =>
                        have hheadSome :
                            StepRawSomePayload encodedRules encodedT
                              tOut := by
                          simpa [hstep] using hheadSim
                        simpa [argsBaseStepFuel?, hstep] using
                          miStepArgs_source_cons_of_head_rawsome_payload
                            encodedRules encodedT encodedTs tOut ts
                            (encRules?_some_normal rws encodedRules hrules)
                            (encAST?_some_normal t encodedT htEnc)
                            htsEnc hheadSome
                    | none =>
                        have hheadNone :
                            StepRawNone encodedRules encodedT := by
                          simpa [hstep] using hheadSim
                        have hrestSim := ih.2 rws ts encodedRules
                          encodedTs hrules htsEnc htsNo htsFuel
                        cases htail :
                            argsBaseStepFuel? rws fuel ts with
                        | some tailOut =>
                            have htailSome :
                                ArgsRawSomePayload encodedRules encodedTs
                                  tailOut := by
                              simpa [htail] using hrestSim
                            simpa [argsBaseStepFuel?, hstep, htail] using
                              miStepArgs_source_cons_of_head_rawnone_rest_rawsome_payload
                                encodedRules encodedT encodedTs t tailOut
                                (encRules?_some_normal rws encodedRules hrules)
                                (encAST?_some_normal t encodedT htEnc)
                                (encASTList?_some_normal ts encodedTs htsEnc)
                                htEnc hheadNone htailSome
                        | none =>
                            have htailNone :
                                ArgsRawNone encodedRules encodedTs := by
                              simpa [htail] using hrestSim
                            simpa [argsBaseStepFuel?, hstep, htail] using
                              miStepArgs_source_cons_of_head_rawnone_rest_rawnone
                                encodedRules encodedT encodedTs
                                (encRules?_some_normal rws encodedRules hrules)
                                (encAST?_some_normal t encodedT htEnc)
                                (encASTList?_some_normal ts encodedTs htsEnc)
                                hheadNone htailNone

theorem stepBaseStep_source_raw_active_sim
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true) :
    match stepBaseStep? rws term with
    | some out => StepRawSome encodedRules encodedTerm out
    | none => StepRawNone encodedRules encodedTerm := by
  have hsim :=
    (step_argsBaseStepFuel_source_raw_active_sim (astFuel term + 1)).1
      rws term encodedRules encodedTerm hrules hterm hno
      (Nat.lt_succ_self (astFuel term))
  simpa [stepBaseStep?] using hsim

theorem stepBaseStep_source_raw_active_payload_sim
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true) :
    match stepBaseStep? rws term with
    | some out => StepRawSomePayload encodedRules encodedTerm out
    | none => StepRawNone encodedRules encodedTerm := by
  have hsim :=
    (step_argsBaseStepFuel_source_raw_active_payload_sim
      (astFuel term + 1)).1
      rws term encodedRules encodedTerm hrules hterm hno
      (Nat.lt_succ_self (astFuel term))
  simpa [stepBaseStep?] using hsim

theorem rawStepSim_encoded_payload
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true) :
    match stepBaseStep? rws term with
    | some out => StepRawSomePayload encodedRules encodedTerm out
    | none => StepRawNone encodedRules encodedTerm :=
  stepBaseStep_source_raw_active_payload_sim rws term encodedRules encodedTerm
    hrules hterm hno

theorem rawStepSimHyp_of_payload_step_lift
    (rws : List RewriteDecl) (encodedRules : AST)
    (hlift : RawPayloadStepLiftHyp rws encodedRules) :
    RawStepSimHyp rws encodedRules :=
  hlift

theorem argsBaseStep_source_raw_active_sim
    (rws : List RewriteDecl) (args : List AST)
    (encodedRules encodedArgs : AST)
    (hrules : encRules? rws = some encodedRules)
    (hargs : encASTList? args = some encodedArgs)
    (hno : noQueryASTList args = true) :
    match argsBaseStep? rws args with
    | some out => ArgsRawSome encodedRules encodedArgs out
    | none => ArgsRawNone encodedRules encodedArgs := by
  have hsim :=
    (step_argsBaseStepFuel_source_raw_active_sim (astListFuel args + 1)).2
      rws args encodedRules encodedArgs hrules hargs hno
      (Nat.lt_succ_self (astListFuel args))
  simpa [argsBaseStep?] using hsim

theorem argsBaseStep_source_raw_active_payload_sim
    (rws : List RewriteDecl) (args : List AST)
    (encodedRules encodedArgs : AST)
    (hrules : encRules? rws = some encodedRules)
    (hargs : encASTList? args = some encodedArgs)
    (hno : noQueryASTList args = true) :
    match argsBaseStep? rws args with
    | some out => ArgsRawSomePayload encodedRules encodedArgs out
    | none => ArgsRawNone encodedRules encodedArgs := by
  have hsim :=
    (step_argsBaseStepFuel_source_raw_active_payload_sim
      (astListFuel args + 1)).2
      rws args encodedRules encodedArgs hrules hargs hno
      (Nat.lt_succ_self (astListFuel args))
  simpa [argsBaseStep?] using hsim

theorem rawStepSim_substInst_root_none
    (rws : List RewriteDecl)
    (term encodedRules template encodedTemplate encodedBs encodedOut : AST)
    (bs : List (String × AST)) (substFuel : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedOut)
    (hno : noQueryAST term = true)
    (hroot : rootBaseStep? rws term = none)
    (htemplate : encAST? template = some encodedTemplate)
    (hbs : encBinds? bs = some encodedBs)
    (hinst : encAST? (AST.inst bs template) = some encodedOut)
    (hsubst :
      eval pMI substFuel (miSubst encodedBs encodedTemplate) =
        encodedOut)
    (_hencoded : IsNormal pMI encodedOut) :
    match stepBaseStep? rws term with
    | some out =>
        StepRawSomePayload encodedRules
          (miSubst encodedBs encodedTemplate) out
    | none =>
        StepRawNone encodedRules (miSubst encodedBs encodedTemplate) := by
  cases term with
  | var path =>
      cases path with
      | base v =>
          simp only [encAST?] at hterm
          cases hterm
          have hsource :
              stepBaseStep? rws (.var (.base v)) = none := by
            simp [stepBaseStep?, stepBaseStepFuel?, hroot]
          rw [hsource]
          exact miStep_misubst_substInst_root_none_mivar_rawnone
            rws (.var (.base v)) encodedRules template encodedTemplate
            encodedBs bs v substFuel hrules rfl hroot htemplate hbs
            hinst hsubst
      | qualified ident rest =>
          simp only [encAST?] at hterm
          cases hterm
  | sexp label args =>
      cases label with
      | id headName =>
          cases args with
          | nil =>
              simp only [encAST?] at hterm
              cases hterm
              have hsource :
                  stepBaseStep? rws (.sexp (.id headName) []) = none := by
                simp [stepBaseStep?, stepBaseStepFuel?, astFuel,
                  astListFuel, argsBaseStepFuel?, hroot]
              rw [hsource]
              exact miStep_misubst_substInst_root_none_misym_rawnone
                rws (.sexp (.id headName) []) encodedRules template
                encodedTemplate encodedBs bs headName substFuel hrules rfl
                hroot htemplate hbs hinst hsubst
          | cons a rest =>
              cases hargsEnc : encASTList? (a :: rest) with
              | none =>
                  simp only [encAST?, hargsEnc] at hterm
                  cases hterm
              | some encodedArgs =>
                  simp only [encAST?, hargsEnc] at hterm
                  cases hterm
                  have hnoApp :
                      (((headName == "match") == false) &&
                        noQueryASTList (a :: rest)) = true := by
                    simpa only [noQueryAST] using hno
                  have hnoArgs :
                      noQueryASTList (a :: rest) = true := by
                    cases hm : ((headName == "match") == false)
                    · simp [hm] at hnoApp
                    · simpa [hm] using hnoApp
                  have hargsSim :=
                    argsBaseStep_source_raw_active_payload_sim rws
                      (a :: rest) encodedRules encodedArgs hrules hargsEnc
                      hnoArgs
                  cases hargsStep : argsBaseStep? rws (a :: rest) with
                  | some argsOut =>
                      have hargsSome :
                          ArgsRawSomePayload encodedRules encodedArgs
                            argsOut := by
                        simpa [hargsStep] using hargsSim
                      rcases
                        argsBaseStepFuel?_cons_some_nonempty rws
                          (astListFuel (a :: rest) + 1) a rest argsOut
                          (by simpa [argsBaseStep?] using hargsStep) with
                        ⟨argOutHead, argOutRest, rfl⟩
                      have hargsFuelStep :
                          argsBaseStepFuel? rws
                              (astListFuel (a :: rest) + 1)
                              (a :: rest) =
                            some (argOutHead :: argOutRest) := by
                        simpa [argsBaseStep?] using hargsStep
                      have hsource :
                          stepBaseStep? rws
                              (.sexp (.id headName) (a :: rest)) =
                            some (.sexp (.id headName)
                              (argOutHead :: argOutRest)) := by
                        simp [stepBaseStep?, stepBaseStepFuel?,
                          astFuel, hroot, hargsFuelStep]
                      rw [hsource]
                      exact
                        miStep_misubst_substInst_root_none_miapp_args_rawsome_payload
                          rws (.sexp (.id headName) (a :: rest))
                          encodedRules template encodedTemplate encodedBs
                          encodedArgs bs headName argOutHead argOutRest
                          substFuel hrules
                          (by simp only [encAST?, hargsEnc]) hroot
                          htemplate hbs hinst hsubst hargsSome
                  | none =>
                      have hargsNone :
                          ArgsRawNone encodedRules encodedArgs := by
                        simpa [hargsStep] using hargsSim
                      have hargsFuelStep :
                          argsBaseStepFuel? rws
                              (astListFuel (a :: rest) + 1)
                              (a :: rest) = none := by
                        simpa [argsBaseStep?] using hargsStep
                      have hsource :
                          stepBaseStep? rws
                              (.sexp (.id headName) (a :: rest)) = none := by
                        simp [stepBaseStep?, stepBaseStepFuel?,
                          astFuel, hroot, hargsFuelStep]
                      rw [hsource]
                      exact
                        miStep_misubst_substInst_root_none_miapp_args_rawnone
                          rws (.sexp (.id headName) (a :: rest))
                          encodedRules template encodedTemplate encodedBs
                          encodedArgs bs headName substFuel hrules
                          (by simp only [encAST?, hargsEnc]) hroot
                          htemplate hbs hinst hsubst hargsNone
      | wild =>
          simp only [encAST?] at hterm
          cases hterm
      | listE c =>
          simp only [encAST?] at hterm
          cases hterm
      | listCons c =>
          simp only [encAST?] at hterm
          cases hterm
      | listOne c =>
          simp only [encAST?] at hterm
          cases hterm
  | subst body repl v =>
      simp only [encAST?] at hterm
      cases hterm

theorem rawPayloadAppStepLift_of_rawArgs
    (rws : List RewriteDecl) (encodedRules : AST) :
    RawPayloadAppStepLiftHyp rws encodedRules := by
  intro hrules term h rawArgs encodedArgs hterm hno hroot hargsPayload
    _hargsNorm
  cases term with
  | var path =>
      cases path with
      | base v =>
          simp only [encAST?] at hterm
          injection hterm with hterm'
          exact False.elim (mivar_ne_miapp v h encodedArgs hterm')
      | qualified _ _ =>
          simp only [encAST?] at hterm
          cases hterm
  | subst _ _ _ =>
      simp only [encAST?] at hterm
      cases hterm
  | sexp label args =>
      cases label with
      | id headName =>
          cases args with
          | nil =>
              simp only [encAST?] at hterm
              injection hterm with hterm'
              exact False.elim
                (misym_ne_miapp headName h encodedArgs hterm')
          | cons a rest =>
              cases hargsEnc : encASTList? (a :: rest) with
              | none =>
                  simp only [encAST?, hargsEnc] at hterm
                  cases hterm
              | some encodedArgsSource =>
                  simp only [encAST?, hargsEnc] at hterm
                  cases hterm
                  have htermApp :
                      encAST? (.sexp (.id h) (a :: rest)) =
                        some (MIApp h encodedArgs) := by
                    simp [encAST?, hargsEnc]
                  have hnoApp :
                      (((h == "match") == false) &&
                        noQueryASTList (a :: rest)) = true := by
                    simpa only [noQueryAST] using hno
                  have hheadB :
                      ((h == "match") == false) = true := by
                    cases hm : ((h == "match") == false) <;>
                      simp [hm] at hnoApp ⊢
                  have hhead : (h == "match") = false := by
                    cases hhm : (h == "match") <;>
                      simp [hhm] at hheadB ⊢
                  have hnoArgs :
                      noQueryASTList (a :: rest) = true := by
                    cases hm : ((h == "match") == false)
                    · simp [hm] at hnoApp
                    · simpa [hm] using hnoApp
                  have hargsSim :=
                    argsBaseStep_source_raw_active_payload_sim rws
                      (a :: rest) encodedRules encodedArgs hrules
                      hargsEnc hnoArgs
                  cases hargsStep : argsBaseStep? rws (a :: rest) with
                  | some argsOut =>
                      have hargsSome :
                          ArgsRawSomePayload encodedRules encodedArgs
                            argsOut := by
                        simpa [hargsStep] using hargsSim
                      have hargsStepFuel :
                          argsBaseStepFuel? rws
                              (astListFuel (a :: rest) + 1)
                              (a :: rest) =
                            some argsOut := by
                        simpa [argsBaseStep?] using hargsStep
                      rcases
                        argsBaseStepFuel?_cons_some_nonempty rws
                          (astListFuel (a :: rest) + 1) a rest argsOut
                          hargsStepFuel with
                        ⟨argOutHead, argOutRest, hargsOutEq⟩
                      subst argsOut
                      have hsource :
                          stepBaseStep? rws (.sexp (.id h) (a :: rest)) =
                            some
                              (.sexp (.id h) (argOutHead :: argOutRest)) := by
                        simp [stepBaseStep?, stepBaseStepFuel?, astFuel,
                          hroot, hargsStepFuel]
                      rw [hsource]
                      exact
                        miStep_rawPayload_app_root_none_args_rawsome_with_guard_payload
                          rws (.sexp (.id h) (a :: rest))
                          encodedRules rawArgs encodedArgs
                          argOutHead argOutRest h hrules htermApp
                          hroot hhead hargsPayload hargsSome
                  | none =>
                      have hargsNone :
                          ArgsRawNone encodedRules encodedArgs := by
                        simpa [hargsStep] using hargsSim
                      have hargsStepFuel :
                          argsBaseStepFuel? rws
                              (astListFuel (a :: rest) + 1)
                              (a :: rest) = none := by
                        simpa [argsBaseStep?] using hargsStep
                      have hsource :
                          stepBaseStep? rws (.sexp (.id h) (a :: rest)) =
                            none := by
                        simp [stepBaseStep?, stepBaseStepFuel?, astFuel,
                          hroot, hargsStepFuel]
                      rw [hsource]
                      exact
                        miStep_rawPayload_app_root_none_args_rawnone_with_guard
                          rws (.sexp (.id h) (a :: rest)) encodedRules
                          rawArgs encodedArgs h hrules htermApp hroot hhead
                          hargsPayload hargsNone
      | wild =>
          simp only [encAST?] at hterm
          cases hterm
      | listE _ =>
          simp only [encAST?] at hterm
          cases hterm
      | listCons _ =>
          simp only [encAST?] at hterm
          cases hterm
      | listOne _ =>
          simp only [encAST?] at hterm
          cases hterm

theorem rawStepSimHyp_of_substInst_app_lifts
    (rws : List RewriteDecl)
    (encodedRules : AST)
    (happLift : RawPayloadAppStepLiftHyp rws encodedRules) :
    RawStepSimHyp rws encodedRules := by
  intro hrules
  intro term rawTerm encodedTerm hpayload hterm hencoded hno
  cases hpayload with
  | encoded _hterm _hnorm =>
      exact rawStepSim_encoded_payload rws term encodedRules _
        hrules hterm hno
  | grammar _hterm hshape hroot =>
      cases hshape with
      | encoded _ =>
          exact rawStepSim_encoded_payload rws term encodedRules _
            hrules hterm hno
      | substInst htemplate hbs hinst hsubstEval _hout =>
          exact
            rawStepSim_substInst_root_none rws term encodedRules _ _ _
              _ _ _ hrules hterm hno hroot htemplate hbs hinst
              hsubstEval hencoded
      | app h hargs =>
          exact happLift hrules term h _ _ hterm hno hroot hargs
            (normal_MIApp_args hencoded)

theorem rawPayloadStepLiftHyp_of_app_lift
    (rws : List RewriteDecl)
    (encodedRules : AST)
    (happLift : RawPayloadAppStepLiftHyp rws encodedRules) :
    RawPayloadStepLiftHyp rws encodedRules :=
  rawStepSimHyp_of_substInst_app_lifts rws encodedRules happLift

theorem rawPayloadAppStepLift_theorem
    (rws : List RewriteDecl) (encodedRules : AST) :
    RawPayloadAppStepLiftHyp rws encodedRules :=
  rawPayloadAppStepLift_of_rawArgs rws encodedRules

theorem rawStepSimHyp_of_rawPayloadGrammar
    (rws : List RewriteDecl) (encodedRules : AST) :
    RawStepSimHyp rws encodedRules :=
  rawStepSimHyp_of_substInst_app_lifts rws encodedRules
    (rawPayloadAppStepLift_theorem rws encodedRules)

theorem rawPayloadStepLiftHyp_of_rawPayloadGrammar
    (rws : List RewriteDecl) (encodedRules : AST) :
    RawPayloadStepLiftHyp rws encodedRules :=
  rawStepSimHyp_of_rawPayloadGrammar rws encodedRules

theorem miEval_succ_eval_of_source_step_some
    (rws : List RewriteDecl) (term out encodedRules encodedTerm fuelArg : AST)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true)
    (hfuel : IsNormal pMI fuelArg)
    (hsource : stepBaseStep? rws term = some out) :
    ∃ (rawNext encodedOut : AST) (N normFuel : Nat),
      encAST? out = some encodedOut ∧
      eval pMI N (miEval encodedRules encodedTerm (FS fuelArg)) =
        miEval encodedRules rawNext fuelArg ∧
      eval pMI normFuel rawNext = encodedOut ∧
      IsNormal pMI encodedOut := by
  have hsim :=
    stepBaseStep_source_raw_active_sim rws term encodedRules encodedTerm
      hrules hterm hno
  rw [hsource] at hsim
  exact miEval_succ_eval_of_raw_step_some encodedRules encodedTerm fuelArg out
    (encRules?_some_normal rws encodedRules hrules)
    (encAST?_some_normal term encodedTerm hterm)
    hfuel hsim

theorem miEval_succ_eval_of_source_step_none
    (rws : List RewriteDecl) (term encodedRules encodedTerm fuelArg : AST)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true)
    (hfuel : IsNormal pMI fuelArg)
    (hsource : stepBaseStep? rws term = none) :
    ∃ N,
      eval pMI N (miEval encodedRules encodedTerm (FS fuelArg)) =
        MIDone encodedTerm := by
  have hsim :=
    stepBaseStep_source_raw_active_sim rws term encodedRules encodedTerm
      hrules hterm hno
  rw [hsource] at hsim
  exact miEval_succ_eval_of_raw_step_none encodedRules encodedTerm fuelArg
    (encRules?_some_normal rws encodedRules hrules)
    (encAST?_some_normal term encodedTerm hterm)
    hfuel hsim

theorem miEval_succ_eval_of_source_step_some_fuel
    (rws : List RewriteDecl) (term out encodedRules encodedTerm : AST)
    (n : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true)
    (hsource : stepBaseStep? rws term = some out) :
    ∃ (rawNext encodedOut : AST) (N normFuel : Nat),
      encAST? out = some encodedOut ∧
      eval pMI N (miEval encodedRules encodedTerm (fuel (n + 1))) =
        miEval encodedRules rawNext (fuel n) ∧
      eval pMI normFuel rawNext = encodedOut ∧
      IsNormal pMI encodedOut := by
  simpa [fuel] using
    miEval_succ_eval_of_source_step_some rws term out encodedRules
      encodedTerm (fuel n) hrules hterm hno (normal_fuel n) hsource

theorem miEval_succ_eval_of_source_step_none_fuel
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (n : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true)
    (hsource : stepBaseStep? rws term = none) :
    ∃ N,
      eval pMI N (miEval encodedRules encodedTerm (fuel (n + 1))) =
        MIDone encodedTerm := by
  simpa [fuel] using
    miEval_succ_eval_of_source_step_none rws term encodedRules encodedTerm
      (fuel n) hrules hterm hno (normal_fuel n) hsource

theorem miEval_zero_matches_sourceInterp
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (hterm : encAST? term = some encodedTerm) :
    ∃ N host,
      eval pMI N (miEval encodedRules encodedTerm (fuel 0)) = host ∧
      MatchesInterp host (sourceInterpVerdict rws 0 term) := by
  refine ⟨1, MIExhausted encodedTerm, ?_, ?_⟩
  · simp only [fuel, eval, os_miEval_zero]
  · simp only [sourceInterpVerdict, MatchesInterp]
    exact ⟨encodedTerm, hterm, rfl⟩

theorem MIDone_eval_of (term out : AST) (fuel : Nat)
    (hterm : eval pMI fuel term = out)
    (hout : IsNormal pMI out) :
    ∃ N, eval pMI N (MIDone term) = MIDone out := by
  exact cong_eval_mi (fun z => MIDone z)
    (fun s s' hstep => os_MIDone_arg_step s s' hstep)
    fuel hterm hout

theorem MIExhausted_eval_of (term out : AST) (fuel : Nat)
    (hterm : eval pMI fuel term = out)
    (hout : IsNormal pMI out) :
    ∃ N, eval pMI N (MIExhausted term) = MIExhausted out := by
  exact cong_eval_mi (fun z => MIExhausted z)
    (fun s s' hstep => os_MIExhausted_arg_step s s' hstep)
    fuel hterm hout

theorem miEval_zero_matches_sourceInterp_raw
    (rws : List RewriteDecl) (term encodedRules rawTerm encodedTerm : AST)
    (normFuel : Nat)
    (hterm : encAST? term = some encodedTerm)
    (hraw : eval pMI normFuel rawTerm = encodedTerm)
    (hrawNorm : IsNormal pMI encodedTerm) :
    ∃ N host,
      eval pMI N (miEval encodedRules rawTerm (fuel 0)) = host ∧
      MatchesInterp host (sourceInterpVerdict rws 0 term) := by
  obtain ⟨M, hM⟩ :=
    MIExhausted_eval_of rawTerm encodedTerm normFuel hraw hrawNorm
  have hdispatch :
      eval pMI 1 (miEval encodedRules rawTerm (fuel 0)) =
        MIExhausted rawTerm := by
    simp only [fuel, eval, os_miEval_zero]
  have htotal := eval_trans_mi 1 M
    (miEval encodedRules rawTerm (fuel 0))
    (MIExhausted rawTerm)
    (MIExhausted encodedTerm)
    hdispatch hM
  refine ⟨1 + M, MIExhausted encodedTerm, htotal, ?_⟩
  simp only [sourceInterpVerdict, MatchesInterp]
  exact ⟨encodedTerm, hterm, rfl⟩

theorem miEval_succ_none_matches_sourceInterp
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (n : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true)
    (hsource : stepBaseStep? rws term = none) :
    ∃ N host,
      eval pMI N (miEval encodedRules encodedTerm (fuel (n + 1))) = host ∧
      MatchesInterp host (sourceInterpVerdict rws (n + 1) term) := by
  obtain ⟨N, hN⟩ :=
    miEval_succ_eval_of_source_step_none_fuel rws term encodedRules
      encodedTerm n hrules hterm hno hsource
  refine ⟨N, MIDone encodedTerm, hN, ?_⟩
  simp only [sourceInterpVerdict, hsource, MatchesInterp]
  exact ⟨encodedTerm, hterm, rfl⟩

theorem miEval_succ_some_reaches_sourceInterp_tail
    (rws : List RewriteDecl) (term out encodedRules encodedTerm : AST)
    (n : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true)
    (hsource : stepBaseStep? rws term = some out) :
    ∃ (rawNext encodedOut : AST) (N normFuel : Nat),
      encAST? out = some encodedOut ∧
      eval pMI N (miEval encodedRules encodedTerm (fuel (n + 1))) =
        miEval encodedRules rawNext (fuel n) ∧
      eval pMI normFuel rawNext = encodedOut ∧
      IsNormal pMI encodedOut ∧
      sourceInterpVerdict rws (n + 1) term =
        sourceInterpVerdict rws n out := by
  obtain ⟨rawNext, encodedOut, N, normFuel, hout, hEval, hnorm, houtNorm⟩ :=
    miEval_succ_eval_of_source_step_some_fuel rws term out encodedRules
      encodedTerm n hrules hterm hno hsource
  refine ⟨rawNext, encodedOut, N, normFuel, hout, hEval, hnorm, houtNorm, ?_⟩
  simp only [sourceInterpVerdict, hsource]

theorem miEval_succ_none_matches_sourceInterp_raw_step
    (rws : List RewriteDecl) (term encodedRules rawTerm encodedTerm : AST)
    (n termFuel : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hrawTerm : eval pMI termFuel rawTerm = encodedTerm)
    (hsource : stepBaseStep? rws term = none)
    (hrawStep : StepRawNone encodedRules rawTerm) :
    ∃ N host,
      eval pMI N (miEval encodedRules rawTerm (fuel (n + 1))) = host ∧
      MatchesInterp host (sourceInterpVerdict rws (n + 1) term) := by
  obtain ⟨N, hN⟩ :=
    miEval_succ_eval_of_raw_term_raw_step_none encodedRules rawTerm
      encodedTerm (fuel n) termFuel
      (encRules?_some_normal rws encodedRules hrules)
      (normal_fuel n) hrawTerm
      (encAST?_some_normal term encodedTerm hterm) hrawStep
  refine ⟨N, MIDone encodedTerm, ?_, ?_⟩
  · simpa [fuel] using hN
  · simp only [sourceInterpVerdict, hsource, MatchesInterp]
    exact ⟨encodedTerm, hterm, rfl⟩

theorem miEval_succ_some_reaches_sourceInterp_tail_raw_step
    (rws : List RewriteDecl) (term out encodedRules rawTerm encodedTerm : AST)
    (n termFuel : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hrawTerm : eval pMI termFuel rawTerm = encodedTerm)
    (hsource : stepBaseStep? rws term = some out)
    (hrawStep : StepRawSome encodedRules rawTerm out) :
    ∃ (rawNext encodedOut : AST) (N normFuel : Nat),
      encAST? out = some encodedOut ∧
      eval pMI N (miEval encodedRules rawTerm (fuel (n + 1))) =
        miEval encodedRules rawNext (fuel n) ∧
      eval pMI normFuel rawNext = encodedOut ∧
      IsNormal pMI encodedOut ∧
      sourceInterpVerdict rws (n + 1) term =
        sourceInterpVerdict rws n out := by
  obtain ⟨rawNext, encodedOut, N, normFuel, hout, hEval,
    hnorm, houtNorm⟩ :=
    miEval_succ_eval_of_raw_term_raw_step_some encodedRules rawTerm
      encodedTerm (fuel n) out termFuel
      (encRules?_some_normal rws encodedRules hrules)
      (normal_fuel n) hrawTerm
      (encAST?_some_normal term encodedTerm hterm) hrawStep
  refine ⟨rawNext, encodedOut, N, normFuel, hout, ?_, hnorm, houtNorm, ?_⟩
  · simpa [fuel] using hEval
  · simp only [sourceInterpVerdict, hsource]

theorem miEval_one_step_some_matches_sourceInterp
    (rws : List RewriteDecl) (term out encodedRules encodedTerm : AST)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true)
    (hsource : stepBaseStep? rws term = some out) :
    ∃ N host,
      eval pMI N (miEval encodedRules encodedTerm (fuel 1)) = host ∧
      MatchesInterp host (sourceInterpVerdict rws 1 term) := by
  obtain ⟨rawNext, encodedOut, Nstep, normFuel, hout, hstep,
    hraw, houtNorm, htail⟩ :=
    miEval_succ_some_reaches_sourceInterp_tail rws term out encodedRules
      encodedTerm 0 hrules hterm hno hsource
  obtain ⟨Ntail, host, htailEval, hmatch⟩ :=
    miEval_zero_matches_sourceInterp_raw rws out encodedRules rawNext
      encodedOut normFuel hout hraw houtNorm
  have htotal := eval_trans_mi Nstep Ntail
    (miEval encodedRules encodedTerm (fuel 1))
    (miEval encodedRules rawNext (fuel 0))
    host hstep htailEval
  refine ⟨Nstep + Ntail, host, htotal, ?_⟩
  simpa only [htail] using hmatch

theorem miEval_one_matches_sourceInterp
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true) :
    ∃ N host,
      eval pMI N (miEval encodedRules encodedTerm (fuel 1)) = host ∧
      MatchesInterp host (sourceInterpVerdict rws 1 term) := by
  cases hsource : stepBaseStep? rws term with
  | some out =>
      exact miEval_one_step_some_matches_sourceInterp rws term out
        encodedRules encodedTerm hrules hterm hno hsource
  | none =>
      exact miEval_succ_none_matches_sourceInterp rws term encodedRules
        encodedTerm 0 hrules hterm hno hsource

theorem miEval_matches_sourceInterp_raw_of_raw_step_sim
    (rws : List RewriteDecl) (term encodedRules rawTerm encodedTerm : AST)
    (n : Nat)
    (hpayload : RawPayloadFor rws encodedRules term rawTerm encodedTerm)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hencoded : IsNormal pMI encodedTerm)
    (hno : noQueryAST term = true)
    (hpres : StepPreservesNoQuery rws)
    (htraceRoot : SourceTraceRootStable rws n term)
    (hrawSim : RawStepSimHyp rws encodedRules) :
    ∃ N host,
      eval pMI N (miEval encodedRules rawTerm (fuel n)) = host ∧
      MatchesInterp host (sourceInterpVerdict rws n term) := by
  induction n generalizing term rawTerm encodedTerm with
  | zero =>
      obtain ⟨termFuel, hrawTerm⟩ :=
        rawTermPayload_eval_of_normal
          (rawPayloadFor_term_payload hpayload) hencoded
      exact miEval_zero_matches_sourceInterp_raw rws term encodedRules
        rawTerm encodedTerm termFuel hterm hrawTerm hencoded
  | succ n ih =>
      obtain ⟨termFuel, hrawTerm⟩ :=
        rawTermPayload_eval_of_normal
          (rawPayloadFor_term_payload hpayload) hencoded
      have hrawCase :=
        hrawSim hrules term rawTerm encodedTerm hpayload hterm hencoded hno
      cases hsource : stepBaseStep? rws term with
      | none =>
          have hrawStep : StepRawNone encodedRules rawTerm := by
            simpa [hsource] using hrawCase
          exact miEval_succ_none_matches_sourceInterp_raw_step rws term
            encodedRules rawTerm encodedTerm n termFuel hrules hterm
            hrawTerm hsource hrawStep
      | some out =>
          have htraceOut :
              rootBaseStep? rws out = none ∧
                SourceTraceRootStable rws n out := by
            simpa [SourceTraceRootStable, hsource] using htraceRoot
          have hrawStep : StepRawSomePayload encodedRules rawTerm out := by
            simpa [hsource] using hrawCase
          unfold StepRawSomePayload at hrawStep
          obtain ⟨rawNext, encodedOut, stepFuel, normFuel, hout, hstepRaw,
            hstepActive, hrawNext, houtNorm, hshapeNext⟩ := hrawStep
          obtain ⟨Nstep, hstep⟩ :=
            miEval_succ_eval_of_raw_term_step_active_step encodedRules
              rawTerm encodedTerm (fuel n) rawNext termFuel stepFuel
              (encRules?_some_normal rws encodedRules hrules)
              (normal_fuel n) hrawTerm hencoded hstepRaw hstepActive
          have htail :
              sourceInterpVerdict rws (n + 1) term =
                sourceInterpVerdict rws n out := by
            simp only [sourceInterpVerdict, hsource]
          have hpayloadNext :
              RawPayloadFor rws encodedRules out rawNext encodedOut :=
            RawPayloadFor.grammar hout hshapeNext htraceOut.1
          have hnoOut : noQueryAST out = true := hpres hsource hno
          obtain ⟨Ntail, host, htailEval, hmatch⟩ :=
            ih out rawNext encodedOut hpayloadNext hout houtNorm hnoOut
              htraceOut.2
          have htotal := eval_trans_mi Nstep Ntail
            (miEval encodedRules rawTerm (fuel (n + 1)))
            (miEval encodedRules rawNext (fuel n))
            host hstep htailEval
          refine ⟨Nstep + Ntail, host, htotal, ?_⟩
          simpa only [htail] using hmatch

theorem miEval_matches_sourceInterp_of_raw_step_sim
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (n : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true)
    (hpres : StepPreservesNoQuery rws)
    (htraceRoot : SourceTraceRootStable rws n term)
    (hrawSim : RawStepSimHyp rws encodedRules) :
    ∃ N host,
      eval pMI N (miEval encodedRules encodedTerm (fuel n)) = host ∧
      MatchesInterp host (sourceInterpVerdict rws n term) := by
  exact miEval_matches_sourceInterp_raw_of_raw_step_sim rws term encodedRules
    encodedTerm encodedTerm n
    (RawPayloadFor.encoded hterm
      (encAST?_some_normal term encodedTerm hterm))
    hrules hterm (encAST?_some_normal term encodedTerm hterm) hno hpres
    htraceRoot hrawSim

theorem miEval_matches_sourceInterp_of_payload_step_lift
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (n : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true)
    (hpres : StepPreservesNoQuery rws)
    (htraceRoot : SourceTraceRootStable rws n term)
    (hlift : RawPayloadStepLiftHyp rws encodedRules) :
    ∃ N host,
      eval pMI N (miEval encodedRules encodedTerm (fuel n)) = host ∧
      MatchesInterp host (sourceInterpVerdict rws n term) := by
  exact miEval_matches_sourceInterp_of_raw_step_sim rws term encodedRules
    encodedTerm n hrules hterm hno hpres htraceRoot
    (rawStepSimHyp_of_payload_step_lift rws encodedRules hlift)

theorem miEval_matches_sourceInterp_of_substInst_app_lifts
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (n : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true)
    (hpres : StepPreservesNoQuery rws)
    (htraceRoot : SourceTraceRootStable rws n term)
    (happLift : RawPayloadAppStepLiftHyp rws encodedRules) :
    ∃ N host,
      eval pMI N (miEval encodedRules encodedTerm (fuel n)) = host ∧
      MatchesInterp host (sourceInterpVerdict rws n term) := by
  exact miEval_matches_sourceInterp_of_raw_step_sim rws term encodedRules
    encodedTerm n hrules hterm hno hpres htraceRoot
    (rawStepSimHyp_of_substInst_app_lifts rws encodedRules happLift)

theorem interp_sim
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (n : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true)
    (hpres : StepPreservesNoQuery rws)
    (htraceRoot : SourceTraceRootStable rws n term) :
    ∃ N host,
      eval pMI N (miEval encodedRules encodedTerm (fuel n)) = host ∧
      MatchesInterp host (sourceInterpVerdict rws n term) := by
  exact miEval_matches_sourceInterp_of_raw_step_sim rws term encodedRules
    encodedTerm n hrules hterm hno hpres htraceRoot
    (rawStepSimHyp_of_rawPayloadGrammar rws encodedRules)

theorem interp_sim_of_step_produces_root_stable
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (n : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true)
    (hpres : StepPreservesNoQuery rws)
    (hrootStable : StepProducesRootStable rws) :
    ∃ N host,
      eval pMI N (miEval encodedRules encodedTerm (fuel n)) = host ∧
      MatchesInterp host (sourceInterpVerdict rws n term) := by
  exact interp_sim rws term encodedRules encodedTerm n hrules hterm hno
    hpres (sourceTraceRootStable_of_stepProduces rws hrootStable n term)

theorem interp_sim_of_rules_preserve_no_query
    (rws : List RewriteDecl) (term encodedRules encodedTerm : AST)
    (n : Nat)
    (hrules : encRules? rws = some encodedRules)
    (hterm : encAST? term = some encodedTerm)
    (hno : noQueryAST term = true)
    (hrulesNoQuery : RulesPreserveNoQuery rws)
    (hrootStable : StepProducesRootStable rws) :
    ∃ N host,
      eval pMI N (miEval encodedRules encodedTerm (fuel n)) = host ∧
      MatchesInterp host (sourceInterpVerdict rws n term) := by
  exact interp_sim_of_step_produces_root_stable rws term encodedRules
    encodedTerm n hrules hterm hno
    (StepPreservesNoQuery_of_RulesPreserveNoQuery rws hrulesNoQuery)
    hrootStable

theorem miStepRootK_eval_of_root_step (rules term next out : AST)
    (fuel : Nat)
    (hnext : eval pMI fuel next = out)
    (hout : IsNormal pMI out) :
    ∃ N,
      eval pMI N (miStepRootK rules term (MIRootStep next)) =
        MIStep out := by
  have hdispatch :
      eval pMI 1 (miStepRootK rules term (MIRootStep next)) =
        MIStep next :=
    miStepRootK_root_step_sim rules term next
  obtain ⟨Mnext, hnextCtx⟩ :=
    cong_eval_mi (fun z => MIStep z)
      (fun s s' hstep => os_MIStep_arg_step s s' hstep)
      fuel hnext hout
  have htotal := eval_trans_mi 1 Mnext
    (miStepRootK rules term (MIRootStep next))
    (MIStep next)
    (MIStep out)
    hdispatch hnextCtx
  exact ⟨1 + Mnext, htotal⟩

theorem miStepAppK_args_named_eval_of_args (h : String)
    (args argsOut : AST) (fuel : Nat)
    (hargs : eval pMI fuel args = argsOut)
    (hargsNorm : IsNormal pMI argsOut) :
    ∃ N,
      eval pMI N (miStepAppK (con0 h) (MIArgsStep args)) =
        MIStep (MIApp h argsOut) := by
  have hdispatch :
      eval pMI 1 (miStepAppK (con0 h) (MIArgsStep args)) =
        MIStep (MIApp h args) :=
    miStepAppK_args_named_sim h args
  obtain ⟨Margs, hargsCtx⟩ :=
    cong_eval_mi (fun z => MIStep (MIApp h z))
      (fun s s' hstep =>
        os_MIStep_arg_step (MIApp h s) (MIApp h s')
          (os_MIApp_args_step h s s' hstep))
      fuel hargs hargsNorm
  have htotal := eval_trans_mi 1 Margs
    (miStepAppK (con0 h) (MIArgsStep args))
    (MIStep (MIApp h args))
    (MIStep (MIApp h argsOut))
    hdispatch hargsCtx
  exact ⟨1 + Margs, htotal⟩

theorem miMatch_var_existing_same_named_sim (v : String) (term rest : AST)
    (hterm : IsNormal pMI term) (hrest : IsNormal pMI rest) :
    eval pMI 4 (miMatch (MIVar v) term (MIBCons (con0 v) term rest)) =
      MIMatchOk (MIBCons (con0 v) term rest) := by
  simp only [eval, MIVar, os_miMatch_var_data, os_miMatchVar,
    os_miMatchVarK_lookup_hit_named, os_miMatchVarK_same_named, hterm, hrest]

theorem miMatch_var_existing_source_beq_true_sim (v : String)
    (term old encodedTerm encodedOld rest : AST)
    (hterm : encAST? term = some encodedTerm)
    (hold : encAST? old = some encodedOld)
    (hbeq : (old == term) = true)
    (hrest : IsNormal pMI rest) :
    eval pMI 4
        (miMatch (MIVar v) encodedTerm (MIBCons (con0 v) encodedOld rest)) =
      MIMatchOk (MIBCons (con0 v) encodedOld rest) := by
  have henc := encAST?_eq_of_beq_true old term encodedOld encodedTerm hold hterm hbeq
  subst encodedOld
  exact miMatch_var_existing_same_named_sim v encodedTerm rest
    (encAST?_some_normal term encodedTerm hterm) hrest

theorem oneStepList_matchVarK_lookup_hit_old_named (v : String) (term old rest : AST)
    (hterm : IsNormal pMI term) (hold : IsNormal pMI old) (hrest : IsNormal pMI rest) :
    oneStepList pMI
        [ con0 v
        , term
        , MIBCons (con0 v) old rest
        , miLookup (con0 v) (MIBCons (con0 v) old rest) ] =
      some
        [ con0 v
        , term
        , MIBCons (con0 v) old rest
        , MISome old ] := by
  have hv : IsNormal pMI (con0 v) := normal_con0 v
  have hbs : IsNormal pMI (MIBCons (con0 v) old rest) :=
    normal_MIBCons (con0 v) old rest hv hold hrest
  simp only [IsNormal] at hv hterm hbs
  simp only [oneStepList, hv, hterm, hbs, os_miLookup_hit_named]
  rfl

theorem base_miMatchVarK_lookup_hit_old_named_raw (v : String) (term old rest : AST) :
    baseReducts pMI
      (.sexp (.id "mi-match-varK")
        [con0 v, term, MIBCons (con0 v) old rest,
          miLookup (con0 v) (MIBCons (con0 v) old rest)]) = [] := by
  rfl

theorem os_miMatchVarK_lookup_hit_old_named (v : String) (term old rest : AST)
    (hterm : IsNormal pMI term) (hold : IsNormal pMI old) (hrest : IsNormal pMI rest) :
    oneStep pMI
        (miMatchVarK (con0 v) term (MIBCons (con0 v) old rest)
          (miLookup (con0 v) (MIBCons (con0 v) old rest))) =
      some (miMatchVarK (con0 v) term (MIBCons (con0 v) old rest) (MISome old)) := by
  rw [oneStep.eq_def]
  simp only [miMatchVarK, app]
  rw [base_miMatchVarK_lookup_hit_old_named_raw]
  rw [oneStepList_matchVarK_lookup_hit_old_named v term old rest hterm hold hrest]
  rfl

theorem miMatch_var_existing_diff_named_sim (v : String) (term old rest : AST)
    (hneq : (term == old) = false)
    (hterm : IsNormal pMI term) (hold : IsNormal pMI old) (hrest : IsNormal pMI rest) :
    eval pMI 4 (miMatch (MIVar v) term (MIBCons (con0 v) old rest)) =
      MIMatchFail := by
  simp only [eval, MIVar, os_miMatch_var_data, os_miMatchVar,
    os_miMatchVarK_lookup_hit_old_named, os_miMatchVarK_diff_named,
    hneq, hterm, hold, hrest]

theorem miMatch_var_existing_source_beq_false_sim (v : String)
    (term old encodedTerm encodedOld rest : AST)
    (hterm : encAST? term = some encodedTerm)
    (hold : encAST? old = some encodedOld)
    (hbeq : (old == term) = false)
    (hrest : IsNormal pMI rest) :
    eval pMI 4
        (miMatch (MIVar v) encodedTerm (MIBCons (con0 v) encodedOld rest)) =
      MIMatchFail := by
  have htermOld : (term == old) = false :=
    ast_beq_false_symm_mi old term hbeq
  have hencFalse : (encodedTerm == encodedOld) = false :=
    encAST?_beq_false_of_beq_false term old encodedTerm encodedOld
      hterm hold htermOld
  exact miMatch_var_existing_diff_named_sim v encodedTerm encodedOld rest hencFalse
    (encAST?_some_normal term encodedTerm hterm)
    (encAST?_some_normal old encodedOld hold)
    hrest

theorem miMatch_var_existing_diff_symbol_canary :
    eval pMI 4 (miMatch (MIVar "fresh") miOne
        (MIBCons (con0 "fresh") miTwo MIBNil)) =
      MIMatchFail := by
  rfl

theorem miMatch_var_nil_named_sim (v : String) (encodedTerm : AST)
    (hterm : IsNormal pMI encodedTerm) :
    eval pMI 4 (miMatch (MIVar v) encodedTerm MIBNil) =
      MIMatchOk (MIBCons (con0 v) encodedTerm MIBNil) := by
  exact miMatch_var_nil_data_sim (con0 v) encodedTerm (normal_con0 v) hterm

theorem miMatch_var_nil_encoded_sim (v : String) (term encodedTerm : AST)
    (henc : encAST? term = some encodedTerm) :
    eval pMI 4 (miMatch (MIVar v) encodedTerm MIBNil) =
      MIMatchOk (MIBCons (con0 v) encodedTerm MIBNil) := by
  exact miMatch_var_nil_named_sim v encodedTerm
    (encAST?_some_normal term encodedTerm henc)

/-! ## Positive and negative fragment examples -/

def addDecls : List RewriteDecl :=
  [ gRw "add-z" (gAdd gZ (gVar "n")) (gVar "n")
  , gRw "add-s" (gAdd (gS (gVar "m")) (gVar "n"))
      (gS (gAdd (gVar "m") (gVar "n"))) ]

def gKick2 (x y : AST) : AST := gApp "Kick" [x, y]

def kickLastDecls : List RewriteDecl :=
  [ gRw "add-z" (gAdd gZ (gVar "n")) (gVar "n")
  , gRw "add-s" (gAdd (gS (gVar "m")) (gVar "n"))
      (gS (gAdd (gVar "m") (gVar "n")))
  , gRw "kick-add2" (gKick2 (gVar "m") (gVar "n"))
      (gAdd (gVar "m") (gVar "n")) ]

def rulesKickLast : AST :=
  MIRCons
    (MIRule (miAdd miZ (MIVar "n")) (MIVar "n"))
    (MIRCons
      (MIRule (miAdd (miS (MIVar "m")) (MIVar "n"))
        (miS (miAdd (MIVar "m") (MIVar "n"))))
      (MIRCons
        (MIRule
          (MIApp "Kick" (MICons (MIVar "m")
            (MICons (MIVar "n") MINil)))
          (miAdd (MIVar "m") (MIVar "n")))
        MIRNil))

def revDecls : List RewriteDecl :=
  [ gRw "append-nil"
      (gListAppend gNil (gVar "ys"))
      (gVar "ys")
  , gRw "append-cons"
      (gListAppend (gCons (gVar "x") (gVar "xs")) (gVar "ys"))
      (gCons (gVar "x") (gListAppend (gVar "xs") (gVar "ys")))
  , gRw "rev-nil"
      (gRev gNil)
      gNil
  , gRw "rev-cons"
      (gRev (gCons (gVar "x") (gVar "xs")))
      (gListAppend (gRev (gVar "xs")) (gCons (gVar "x") gNil))
  ]

theorem encRules_addDecls :
    encRules? addDecls = some rulesAdd := by
  rfl

theorem encRules_kickLastDecls :
    encRules? kickLastDecls = some rulesKickLast := by
  rfl

theorem encRules_revDecls :
    encRules? revDecls = some rulesRev := by
  rfl

theorem rulesPreserveNoQuery_addDecls :
    RulesPreserveNoQuery addDecls := by
  unfold addDecls RulesPreserveNoQuery
  constructor
  · change noQueryAST (gVar "n") = true
    simp [gVar, noQueryAST]
  constructor
  · change noQueryAST (gS (gAdd (gVar "m") (gVar "n"))) = true
    simp [gS, gAdd, gVar, gApp, noQueryAST, noQueryASTList]
  · trivial

theorem stepPreservesNoQuery_addDecls :
    StepPreservesNoQuery addDecls := by
  exact StepPreservesNoQuery_of_RulesPreserveNoQuery addDecls
    rulesPreserveNoQuery_addDecls

theorem rulesPreserveNoQuery_kickLastDecls :
    RulesPreserveNoQuery kickLastDecls := by
  unfold kickLastDecls RulesPreserveNoQuery
  constructor
  · change noQueryAST (gVar "n") = true
    simp [gVar, noQueryAST]
  constructor
  · change noQueryAST (gS (gAdd (gVar "m") (gVar "n"))) = true
    simp [gS, gAdd, gVar, gApp, noQueryAST, noQueryASTList]
  constructor
  · change noQueryAST (gAdd (gVar "m") (gVar "n")) = true
    simp [gAdd, gVar, gApp, noQueryAST, noQueryASTList]
  · trivial

theorem stepPreservesNoQuery_kickLastDecls :
    StepPreservesNoQuery kickLastDecls := by
  exact StepPreservesNoQuery_of_RulesPreserveNoQuery kickLastDecls
    rulesPreserveNoQuery_kickLastDecls

theorem rulesPreserveNoQuery_revDecls :
    RulesPreserveNoQuery revDecls := by
  unfold revDecls RulesPreserveNoQuery
  constructor
  · change noQueryAST (gVar "ys") = true
    simp [gVar, noQueryAST]
  constructor
  · change noQueryAST
      (gCons (gVar "x") (gListAppend (gVar "xs") (gVar "ys"))) = true
    simp [gCons, gListAppend, gVar, gApp, noQueryAST, noQueryASTList]
  constructor
  · change noQueryAST gNil = true
    simp [gNil, gCon0, noQueryAST]
  constructor
  · change noQueryAST
      (gListAppend (gRev (gVar "xs")) (gCons (gVar "x") gNil)) = true
    simp [gListAppend, gRev, gCons, gVar, gNil, gCon0, gApp, noQueryAST,
      noQueryASTList]
  · trivial

theorem stepPreservesNoQuery_revDecls :
    StepPreservesNoQuery revDecls := by
  exact StepPreservesNoQuery_of_RulesPreserveNoQuery revDecls
    rulesPreserveNoQuery_revDecls

theorem encAST_add_2_1 :
    encAST? (gAdd gTwo gOne) = some (miAdd miTwo miOne) := by
  rfl

theorem encAST_rev_involution_012 :
    encAST? (gRev (gRev gList012)) = some (miRev (miRev miList012)) := by
  rfl

theorem interpCall_add_2_1 :
    interpCall? addDecls (gAdd gTwo gOne) 10 =
      some (miEval rulesAdd (miAdd miTwo miOne) (fuel 10)) := by
  rfl

theorem interpCall_rev_involution_012 :
    interpCall? revDecls (gRev (gRev gList012)) 40 =
      some (miEval rulesRev (miRev (miRev miList012)) (fuel 40)) := by
  rfl

theorem noQueryAST_accepts_add_2_1 :
    noQueryAST (gAdd gTwo gOne) = true := by
  unfold gAdd gTwo gOne gS gZ gCon0 gApp
  simp only [noQueryAST, noQueryASTList]
  decide

theorem noQueryAST_accepts_kick_last_z_one :
    noQueryAST (gKick2 gZ gOne) = true := by
  unfold gKick2 gOne gS gZ gCon0 gApp
  simp only [noQueryAST, noQueryASTList]
  decide

theorem noQueryAST_accepts_rev_involution_012 :
    noQueryAST (gRev (gRev gList012)) = true := by
  unfold gRev gList012 gCons gNil gTwo gOne gS gZ gCon0 gApp
  simp only [noQueryAST, noQueryASTList]
  decide

theorem noQueryAST_rejects_match_app :
    noQueryAST (.sexp (.id "match") [gOne]) = false := by
  unfold gOne gS gZ gCon0
  simp only [noQueryAST, noQueryASTList]
  decide

theorem noQueryAST_match_app_precondition_bites :
    ¬ (noQueryAST (.sexp (.id "match") [gOne]) = true) := by
  rw [noQueryAST_rejects_match_app]
  simp

def sourceRevExposeRoot_0 : AST :=
  gListAppend (gRev gNil) gNil

def sourceRevExposeRoot_1 : AST :=
  gListAppend gNil gNil

theorem sourceRevExposeRoot_step_0 :
    stepBaseStep? revDecls sourceRevExposeRoot_0 =
      some sourceRevExposeRoot_1 := by
  rfl

theorem sourceRevExposeRoot_root_some_1 :
    rootBaseStep? revDecls sourceRevExposeRoot_1 = some gNil := by
  rfl

theorem revDecls_not_stepProducesRootStable :
    ¬ StepProducesRootStable revDecls := by
  intro hstable
  have hroot :=
    hstable sourceRevExposeRoot_step_0
  rw [sourceRevExposeRoot_root_some_1] at hroot
  simp at hroot

def sourceRevInv_0 : AST := gRev (gRev gList012)
def sourceRevInv_1 : AST :=
  gRev (gListAppend (gRev (gCons gOne (gCons gTwo gNil)))
    (gCons gZ gNil))
def sourceRevInv_2 : AST :=
  gRev (gListAppend
    (gListAppend (gRev (gCons gTwo gNil)) (gCons gOne gNil))
    (gCons gZ gNil))
def sourceRevInv_3 : AST :=
  gRev (gListAppend
    (gListAppend
      (gListAppend (gRev gNil) (gCons gTwo gNil))
      (gCons gOne gNil))
    (gCons gZ gNil))
def sourceRevInv_4 : AST :=
  gRev (gListAppend
    (gListAppend
      (gListAppend gNil (gCons gTwo gNil))
      (gCons gOne gNil))
    (gCons gZ gNil))
def sourceRevInv_5 : AST :=
  gRev (gListAppend
    (gListAppend (gCons gTwo gNil) (gCons gOne gNil))
    (gCons gZ gNil))
def sourceRevInv_6 : AST :=
  gRev (gListAppend
    (gCons gTwo (gListAppend gNil (gCons gOne gNil)))
    (gCons gZ gNil))
def sourceRevInv_7 : AST :=
  gRev (gCons gTwo
    (gListAppend
      (gListAppend gNil (gCons gOne gNil))
      (gCons gZ gNil)))
def sourceRevInv_8 : AST :=
  gListAppend
    (gRev (gListAppend
      (gListAppend gNil (gCons gOne gNil))
      (gCons gZ gNil)))
    (gCons gTwo gNil)

theorem sourceRevInv_step_0 :
    stepBaseStep? revDecls sourceRevInv_0 = some sourceRevInv_1 := by
  rfl

theorem sourceRevInv_step_1 :
    stepBaseStep? revDecls sourceRevInv_1 = some sourceRevInv_2 := by
  rfl

theorem sourceRevInv_step_2 :
    stepBaseStep? revDecls sourceRevInv_2 = some sourceRevInv_3 := by
  rfl

theorem sourceRevInv_step_3 :
    stepBaseStep? revDecls sourceRevInv_3 = some sourceRevInv_4 := by
  rfl

theorem sourceRevInv_step_4 :
    stepBaseStep? revDecls sourceRevInv_4 = some sourceRevInv_5 := by
  rfl

theorem sourceRevInv_step_5 :
    stepBaseStep? revDecls sourceRevInv_5 = some sourceRevInv_6 := by
  rfl

theorem sourceRevInv_step_6 :
    stepBaseStep? revDecls sourceRevInv_6 = some sourceRevInv_7 := by
  rfl

theorem sourceRevInv_root_7 :
    rootBaseStep? revDecls sourceRevInv_7 = some sourceRevInv_8 := by
  rfl

theorem sourceTraceRootStable_rev_involution_012_40_fails :
    ¬ SourceTraceRootStable revDecls 40 sourceRevInv_0 := by
  intro h
  unfold SourceTraceRootStable at h
  rw [sourceRevInv_step_0] at h
  have h1 := h.2
  unfold SourceTraceRootStable at h1
  rw [sourceRevInv_step_1] at h1
  have h2 := h1.2
  unfold SourceTraceRootStable at h2
  rw [sourceRevInv_step_2] at h2
  have h3 := h2.2
  unfold SourceTraceRootStable at h3
  rw [sourceRevInv_step_3] at h3
  have h4 := h3.2
  unfold SourceTraceRootStable at h4
  rw [sourceRevInv_step_4] at h4
  have h5 := h4.2
  unfold SourceTraceRootStable at h5
  rw [sourceRevInv_step_5] at h5
  have h6 := h5.2
  unfold SourceTraceRootStable at h6
  rw [sourceRevInv_step_6] at h6
  have hroot := h6.1
  rw [sourceRevInv_root_7] at hroot
  contradiction

theorem sourceInterpVerdict_rev_involution_012 :
    sourceInterpVerdict revDecls 40 (gRev (gRev gList012)) =
      SourceInterpVerdict.done gList012 := by
  rfl

theorem miEval_rev_involution_012_matches_sourceInterp :
    ∃ N host,
      eval pMI N (miEval rulesRev (miRev (miRev miList012)) (fuel 40)) =
        host ∧
      MatchesInterp host
        (sourceInterpVerdict revDecls 40 (gRev (gRev gList012))) := by
  refine ⟨12000, MIDone miList012, ?_, ?_⟩
  · exact self_rev_involution_eval_012
  · rw [sourceInterpVerdict_rev_involution_012]
    unfold MatchesInterp
    exact ⟨miList012, rfl, rfl⟩

theorem encAST_add_1_1 :
    encAST? (gAdd gOne gOne) = some (miAdd miOne miOne) := by
  rfl

theorem interpCall_add_1_1 :
    interpCall? addDecls (gAdd gOne gOne) 10 =
      some (miEval rulesAdd (miAdd miOne miOne) (fuel 10)) := by
  rfl

theorem noQueryAST_accepts_add_1_1 :
    noQueryAST (gAdd gOne gOne) = true := by
  unfold gAdd gOne gS gZ gCon0 gApp
  simp only [noQueryAST, noQueryASTList]
  decide

def sourceAdd11_0 : AST := gAdd gOne gOne
def sourceAdd11_1 : AST := gS (gAdd gZ gOne)
def sourceAdd11_2 : AST := gS gOne

theorem sourceAdd11_step_0 :
    stepBaseStep? addDecls sourceAdd11_0 = some sourceAdd11_1 := by
  rfl

theorem sourceAdd11_root_none_1 :
    rootBaseStep? addDecls sourceAdd11_1 = none := by
  rfl

theorem sourceAdd11_step_1 :
    stepBaseStep? addDecls sourceAdd11_1 = some sourceAdd11_2 := by
  rfl

theorem sourceAdd11_root_none_2 :
    rootBaseStep? addDecls sourceAdd11_2 = none := by
  rfl

theorem sourceAdd11_step_done :
    stepBaseStep? addDecls sourceAdd11_2 = none := by
  rfl

theorem sourceTraceRootStable_add_1_1_10 :
    SourceTraceRootStable addDecls 10 sourceAdd11_0 := by
  unfold SourceTraceRootStable
  rw [sourceAdd11_step_0]
  constructor
  · exact sourceAdd11_root_none_1
  unfold SourceTraceRootStable
  rw [sourceAdd11_step_1]
  constructor
  · exact sourceAdd11_root_none_2
  unfold SourceTraceRootStable
  rw [sourceAdd11_step_done]
  trivial

theorem miEval_add_1_1_matches_sourceInterp_by_interp_sim :
    ∃ N host,
      eval pMI N (miEval rulesAdd (miAdd miOne miOne) (fuel 10)) = host ∧
      MatchesInterp host (sourceInterpVerdict addDecls 10 (gAdd gOne gOne)) := by
  exact interp_sim addDecls (gAdd gOne gOne) rulesAdd
    (miAdd miOne miOne) 10 encRules_addDecls encAST_add_1_1
    noQueryAST_accepts_add_1_1 stepPreservesNoQuery_addDecls
    sourceTraceRootStable_add_1_1_10

theorem sourceInterpVerdict_add_1_1 :
    sourceInterpVerdict addDecls 10 (gAdd gOne gOne) =
      SourceInterpVerdict.done (gS gOne) := by
  simp only [sourceInterpVerdict,
    show stepBaseStep? addDecls (gAdd gOne gOne) = some sourceAdd11_1 by rfl,
    show stepBaseStep? addDecls sourceAdd11_1 = some sourceAdd11_2 by rfl,
    show stepBaseStep? addDecls sourceAdd11_2 = none by rfl]
  rfl

def sourceAdd21_0 : AST := gAdd gTwo gOne
def sourceAdd21_1 : AST := gS (gAdd gOne gOne)
def sourceAdd21_2 : AST := gS (gS (gAdd gZ gOne))
def sourceAdd21_3 : AST := gS (gS gOne)

theorem sourceAdd21_step_0 :
    stepBaseStep? addDecls sourceAdd21_0 = some sourceAdd21_1 := by
  rfl

theorem sourceAdd21_root_none_1 :
    rootBaseStep? addDecls sourceAdd21_1 = none := by
  rfl

theorem sourceAdd21_step_1 :
    stepBaseStep? addDecls sourceAdd21_1 = some sourceAdd21_2 := by
  rfl

theorem sourceAdd21_root_none_2 :
    rootBaseStep? addDecls sourceAdd21_2 = none := by
  rfl

theorem sourceAdd21_step_2 :
    stepBaseStep? addDecls sourceAdd21_2 = some sourceAdd21_3 := by
  rfl

theorem sourceAdd21_root_none_3 :
    rootBaseStep? addDecls sourceAdd21_3 = none := by
  rfl

theorem sourceAdd21_step_done :
    stepBaseStep? addDecls sourceAdd21_3 = none := by
  rfl

theorem sourceTraceRootStable_add_2_1_10 :
    SourceTraceRootStable addDecls 10 sourceAdd21_0 := by
  unfold SourceTraceRootStable
  rw [sourceAdd21_step_0]
  constructor
  · exact sourceAdd21_root_none_1
  unfold SourceTraceRootStable
  rw [sourceAdd21_step_1]
  constructor
  · exact sourceAdd21_root_none_2
  unfold SourceTraceRootStable
  rw [sourceAdd21_step_2]
  constructor
  · exact sourceAdd21_root_none_3
  unfold SourceTraceRootStable
  rw [sourceAdd21_step_done]
  trivial

theorem miEval_add_2_1_matches_sourceInterp_of_payload_step_lift
    (hlift : RawPayloadStepLiftHyp addDecls rulesAdd) :
    ∃ N host,
      eval pMI N (miEval rulesAdd (miAdd miTwo miOne) (fuel 10)) = host ∧
      MatchesInterp host (sourceInterpVerdict addDecls 10 (gAdd gTwo gOne)) := by
  exact miEval_matches_sourceInterp_of_payload_step_lift addDecls
    (gAdd gTwo gOne) rulesAdd (miAdd miTwo miOne) 10
    encRules_addDecls encAST_add_2_1 noQueryAST_accepts_add_2_1
    stepPreservesNoQuery_addDecls sourceTraceRootStable_add_2_1_10 hlift

theorem miEval_add_2_1_matches_sourceInterp_by_interp_sim :
    ∃ N host,
      eval pMI N (miEval rulesAdd (miAdd miTwo miOne) (fuel 10)) = host ∧
      MatchesInterp host (sourceInterpVerdict addDecls 10 (gAdd gTwo gOne)) := by
  exact interp_sim addDecls (gAdd gTwo gOne) rulesAdd
    (miAdd miTwo miOne) 10 encRules_addDecls encAST_add_2_1
    noQueryAST_accepts_add_2_1 stepPreservesNoQuery_addDecls
    sourceTraceRootStable_add_2_1_10

theorem sourceInterpVerdict_add_2_1 :
    sourceInterpVerdict addDecls 10 (gAdd gTwo gOne) =
      SourceInterpVerdict.done (gS (gS gOne)) := by
  simp only [sourceInterpVerdict,
    show stepBaseStep? addDecls (gAdd gTwo gOne) = some sourceAdd21_1 by rfl,
    show stepBaseStep? addDecls sourceAdd21_1 = some sourceAdd21_2 by rfl,
    show stepBaseStep? addDecls sourceAdd21_2 = some (gS (gS gOne)) by rfl,
    show stepBaseStep? addDecls (gS (gS gOne)) = none by rfl]

set_option maxRecDepth 10000 in
theorem miEval_add_2_1_done :
    eval pMI 500 (miEval rulesAdd (miAdd miTwo miOne) (fuel 10)) =
      MIDone miThree := by
  rfl

theorem miEval_add_2_1_matches_sourceInterp :
    ∃ N host,
      eval pMI N (miEval rulesAdd (miAdd miTwo miOne) (fuel 10)) = host ∧
      MatchesInterp host (sourceInterpVerdict addDecls 10 (gAdd gTwo gOne)) := by
  refine ⟨500, MIDone miThree, miEval_add_2_1_done, ?_⟩
  rw [sourceInterpVerdict_add_2_1]
  unfold MatchesInterp
  exact ⟨miThree, rfl, rfl⟩

def rawAdd11PayloadBinds : AST :=
  MIBCons (con0 "m") miZ (MIBCons (con0 "n") miOne MIBNil)

def rawAdd11Payload : AST :=
  miSubst rawAdd11PayloadBinds
    (miS (miAdd (MIVar "m") (MIVar "n")))

theorem rawAdd11Payload_eval_source_successor :
    eval pMI 80 rawAdd11Payload = miS (miAdd miZ miOne) := by
  rfl

theorem rawAdd11Payload_shape :
    RawTermPayload rawAdd11Payload (miS (miAdd miZ miOne)) := by
  exact RawTermPayload.substInst
    (template := gS (gAdd (gVar "m") (gVar "n")))
    (encodedTemplate := miS (miAdd (MIVar "m") (MIVar "n")))
    (encodedBs := rawAdd11PayloadBinds)
    (bs := [("m", gZ), ("n", gOne)])
    rfl rfl rfl rawAdd11Payload_eval_source_successor
    (encAST?_some_normal (gS (gAdd gZ gOne))
      (miS (miAdd miZ miOne)) rfl)

theorem rawAdd11Payload_source_root_none :
    rootBaseStep? addDecls (gS (gAdd gZ gOne)) = none := by
  rfl

theorem rawAdd11Payload_payload_for :
    RawPayloadFor addDecls rulesAdd (gS (gAdd gZ gOne))
      rawAdd11Payload (miS (miAdd miZ miOne)) := by
  exact RawPayloadFor.grammar rfl rawAdd11Payload_shape
    rawAdd11Payload_source_root_none

theorem rawAdd11Payload_source_next_step :
    stepBaseStep? addDecls (gS (gAdd gZ gOne)) = some (gS gOne) := by
  rfl

theorem rawAdd11Payload_step_reaches_next_successor :
    eval pMI 120 (miStep rulesAdd rawAdd11Payload) =
      MIStep (miS miOne) := by
  rfl

theorem rawAdd11Payload_root_stable_step_boundary :
    RawPayloadFor addDecls rulesAdd (gS (gAdd gZ gOne))
        rawAdd11Payload (miS (miAdd miZ miOne)) ∧
      stepBaseStep? addDecls (gS (gAdd gZ gOne)) = some (gS gOne) ∧
      eval pMI 120 (miStep rulesAdd rawAdd11Payload) =
        MIStep (miS miOne) := by
  exact ⟨rawAdd11Payload_payload_for,
    rawAdd11Payload_source_next_step,
    rawAdd11Payload_step_reaches_next_successor⟩

def rawAddZPayload : AST :=
  miSubst rawAdd11PayloadBinds
    (miAdd (MIVar "m") (MIVar "n"))

theorem rawAddZPayload_eval_source_add_z :
    eval pMI 80 rawAddZPayload = miAdd miZ miOne := by
  rfl

theorem rawAddZPayload_shape :
    RawTermPayload rawAddZPayload (miAdd miZ miOne) := by
  exact RawTermPayload.substInst
    (template := gAdd (gVar "m") (gVar "n"))
    (encodedTemplate := miAdd (MIVar "m") (MIVar "n"))
    (encodedBs := rawAdd11PayloadBinds)
    (bs := [("m", gZ), ("n", gOne)])
    rfl rfl rfl rawAddZPayload_eval_source_add_z
    (encAST?_some_normal (gAdd gZ gOne) (miAdd miZ miOne) rfl)

theorem rawAddZPayload_source_root_some :
    rootBaseStep? addDecls (gAdd gZ gOne) = some gOne := by
  rfl

theorem rawAddZPayload_source_not_root_stable :
    rootBaseStep? addDecls (gAdd gZ gOne) ≠ none := by
  rw [rawAddZPayload_source_root_some]
  simp

theorem rawAddZPayload_raw_ne_encoded :
    rawAddZPayload ≠ miAdd miZ miOne := by
  intro h
  unfold rawAddZPayload miSubst miAdd MIApp app at h
  injection h with hlabel _hargs
  injection hlabel with hstr
  simp at hstr

theorem rawAddZPayload_not_rawPayloadFor :
    ¬ RawPayloadFor addDecls rulesAdd (gAdd gZ gOne)
      rawAddZPayload (miAdd miZ miOne) := by
  intro h
  have hcase := rawPayloadFor_encoded_or_root_none h
  cases hcase with
  | inl heq => exact rawAddZPayload_raw_ne_encoded heq
  | inr hroot =>
      rw [rawAddZPayload_source_root_some] at hroot
      simp at hroot

theorem encodedAddZ_step_reaches_successor :
    eval pMI 40 (miStep rulesAdd (miAdd miZ miOne)) =
      MIStep miOne := by
  rfl

theorem rawAddZPayload_step_is_none :
    eval pMI 120 (miStep rulesAdd rawAddZPayload) = MINoStep := by
  rfl

theorem sourceInterpVerdict_add_z_one_one :
    sourceInterpVerdict addDecls 1 (gAdd gZ gOne) =
      SourceInterpVerdict.exhausted gOne := by
  rfl

theorem miEval_rawAddZPayload_fuel_one_stops_before_root :
    eval pMI 200 (miEval rulesAdd rawAddZPayload (fuel 1)) =
      MIDone (miAdd miZ miOne) := by
  rfl

theorem rawAddZPayload_fuel_one_not_source_match :
    ¬ MatchesInterp (MIDone (miAdd miZ miOne))
        (sourceInterpVerdict addDecls 1 (gAdd gZ gOne)) := by
  rw [sourceInterpVerdict_add_z_one_one]
  unfold MatchesInterp
  intro h
  rcases h with ⟨encodedTerm, henc, hhost⟩
  simp only [gOne, gS, gZ, gCon0, gApp, encAST?, encASTList?] at henc
  cases henc
  unfold MIDone MIExhausted app at hhost
  injection hhost with hlabel _hargs
  injection hlabel with hstr
  simp at hstr

theorem rawAddZPayload_root_guard_is_necessary :
    RawTermPayload rawAddZPayload (miAdd miZ miOne) ∧
      rootBaseStep? addDecls (gAdd gZ gOne) = some gOne ∧
      eval pMI 40 (miStep rulesAdd (miAdd miZ miOne)) =
        MIStep miOne ∧
      eval pMI 120 (miStep rulesAdd rawAddZPayload) = MINoStep := by
  exact ⟨rawAddZPayload_shape, rawAddZPayload_source_root_some,
    encodedAddZ_step_reaches_successor, rawAddZPayload_step_is_none⟩

theorem sourceInterpVerdict_kick_last_z_one_2 :
    sourceInterpVerdict kickLastDecls 2 (gKick2 gZ gOne) =
      SourceInterpVerdict.exhausted gOne := by
  rfl

theorem miEval_kick_last_z_one_fuel_two_stops_before_source :
    eval pMI 500
        (miEval rulesKickLast
          (MIApp "Kick" (MICons miZ (MICons miOne MINil)))
          (fuel 2)) =
      MIDone (miAdd miZ miOne) := by
  rfl

theorem kick_last_z_one_fuel_two_not_source_match :
    ¬ MatchesInterp (MIDone (miAdd miZ miOne))
        (sourceInterpVerdict kickLastDecls 2 (gKick2 gZ gOne)) := by
  rw [sourceInterpVerdict_kick_last_z_one_2]
  unfold MatchesInterp
  intro h
  rcases h with ⟨encodedTerm, henc, hhost⟩
  simp only [gOne, gS, gZ, gCon0, gApp, encAST?, encASTList?] at henc
  cases henc
  unfold MIDone MIExhausted app at hhost
  injection hhost with hlabel _hargs
  injection hlabel with hstr
  simp at hstr

def rawVarPayloadBinds : AST :=
  MIBCons (con0 "n") miOne MIBNil

def rawVarPayload : AST :=
  miSubst rawVarPayloadBinds (MIVar "n")

theorem rawVarPayload_eval_source_normal :
    eval pMI 20 rawVarPayload = miOne := by
  rfl

theorem rawVarPayload_shape :
    RawTermPayload rawVarPayload miOne := by
  exact RawTermPayload.substInst
    (template := gVar "n")
    (encodedTemplate := MIVar "n")
    (encodedBs := rawVarPayloadBinds)
    (bs := [("n", gOne)])
    rfl rfl rfl rawVarPayload_eval_source_normal
    (encAST?_some_normal gOne miOne rfl)

theorem rawVarPayload_source_root_none :
    rootBaseStep? addDecls gOne = none := by
  rfl

theorem rawVarPayload_payload_for :
    RawPayloadFor addDecls rulesAdd gOne rawVarPayload miOne := by
  exact RawPayloadFor.grammar rfl rawVarPayload_shape
    rawVarPayload_source_root_none

theorem rawVarPayload_step_is_none :
    eval pMI 40 (miStep rulesAdd rawVarPayload) = MINoStep := by
  rfl

theorem miMatch_accepts_fresh_var_name :
    eval pMI 20 (miMatch (MIVar "fresh") miOne MIBNil) =
      MIMatchOk (MIBCons (con0 "fresh") miOne MIBNil) := by
  rfl

theorem encBinds_fresh_one :
    encBinds? [("fresh", gOne)] =
      some (MIBCons (con0 "fresh") miOne MIBNil) := by
  rfl

theorem matchPat_fresh_var :
    AST.matchPat (gVar "fresh") gOne [] = some [("fresh", gOne)] := by
  rfl

theorem matchPat_fresh_var_encoded :
    (AST.matchPat (gVar "fresh") gOne []).bind encBinds? =
      some (MIBCons (con0 "fresh") miOne MIBNil) := by
  rfl

theorem reference_inst_fresh_var :
    AST.inst [("fresh", gOne)] (gVar "fresh") = gOne := by
  rfl

theorem miSubst_fresh_var :
    eval pMI 30 (miSubst (MIBCons (con0 "fresh") miOne MIBNil) (MIVar "fresh")) =
      miOne := by
  rfl

theorem miSubst_fresh_app :
    eval pMI 80
        (miSubst (MIBCons (con0 "fresh") miOne MIBNil) (miS (MIVar "fresh"))) =
      miS miOne := by
  rfl

theorem encAST_rejects_non_id_label :
    encAST? (.sexp .wild []) = none := by
  rfl

theorem encAST_rejects_subst :
    encAST? (.subst gZ gOne (.base "x")) = none := by
  rfl

def ctxDecl : RewriteDecl :=
  { name := "ctx"
  , rw := .ctx { src := .base "src", tgt := .base "tgt" } (.base gZ gOne) }

theorem encRewriteDecl_rejects_ctx :
    encRewriteDecl? ctxDecl = none := by
  rfl

end Mettapedia.GSLT.LanguageDef.MIEvalEncoding
