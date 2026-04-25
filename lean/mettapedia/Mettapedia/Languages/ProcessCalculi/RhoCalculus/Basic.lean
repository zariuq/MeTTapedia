import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Types
import Mathlib

/-!
# Rho calculus executable model

This file is the Mettapedia home for the executable rho model used by CeTTa
RhoCalc development.  The filename `Basic.lean` follows the usual Lean
convention for an entry module; it is not naming a separate calculus.  The model
lives beside the existing Pattern/OSLF formalization rather than forming a
separate project.  It keeps a small, direct syntax for executable small-step
tests, including arbitrary joins, persistent joins, checked substitution,
quote/fresh discipline, structural congruence examples, and reaction-index
soundness facts.

The larger `RhoCalculus` files remain the canonical OSLF/MeTTaIL Pattern
formalization.  This module is a compact bridge-oriented operational model for
runtime correspondence work.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Basic

inductive Name : Type where
  | free : String -> Name
  | var : Nat -> Name
  | fresh : Nat -> Name
  deriving Repr

inductive Data : Type where
  | atom : String -> Data
  | var : Nat -> Data
  | tuple : List Data -> Data
  | name : Name -> Data
  deriving Repr

inductive Pat : Type where
  | wild : Pat
  | bind : Nat -> Pat
  | atom : String -> Pat
  | tuple : List Pat -> Pat
  deriving Repr

structure JoinClause where
  channel : Name
  pattern : Pat
  deriving Repr

inductive Proc : Type where
  | nil : Proc
  | par : List Proc -> Proc
  | send : Name -> Data -> Proc
  | recv : Name -> Pat -> Proc -> Proc
  | contract : Name -> Pat -> Proc -> Proc
  | join : List JoinClause -> Proc -> Proc
  | pjoin : List JoinClause -> Proc -> Proc
  | join2 : Name -> Pat -> Name -> Pat -> Proc -> Proc
  | pjoin2 : Name -> Pat -> Name -> Pat -> Proc -> Proc
  | quote : Proc -> Proc
  | drop : Proc -> Proc
  | fresh : Nat -> Proc -> Proc
  deriving Repr

def nameEq : Name -> Name -> Bool
  | Name.free a, Name.free b => a == b
  | Name.var a, Name.var b => a == b
  | Name.fresh a, Name.fresh b => a == b
  | _, _ => false

mutual
def dataEq : Data -> Data -> Bool
  | Data.atom a, Data.atom b => a == b
  | Data.var a, Data.var b => a == b
  | Data.tuple xs, Data.tuple ys => dataListEq xs ys
  | Data.name a, Data.name b => nameEq a b
  | _, _ => false

def dataListEq : List Data -> List Data -> Bool
  | [], [] => true
  | x :: xs, y :: ys => dataEq x y && dataListEq xs ys
  | _, _ => false
end

abbrev Subst := List (Nat × Data)

def lookup (x : Nat) : Subst -> Option Data
  | [] => none
  | (y, d) :: rest => if x = y then some d else lookup x rest

def eraseVar (x : Nat) : Subst -> Subst
  | [] => []
  | (y, d) :: rest =>
      if x = y then eraseVar x rest else (y, d) :: eraseVar x rest

def extendConsistent (x : Nat) (d : Data) (s : Subst) : Option Subst :=
  match lookup x s with
  | none => some ((x, d) :: s)
  | some old => if dataEq old d then some s else none

def mergeSubst : Subst -> Subst -> Option Subst
  | [], s => some s
  | (x, d) :: rest, s => do
      let s' <- extendConsistent x d s
      mergeSubst rest s'

def patVars : Pat -> List Nat
  | Pat.wild => []
  | Pat.bind x => [x]
  | Pat.atom _ => []
  | Pat.tuple ps => ps.foldr (fun p acc => patVars p ++ acc) []

def joinClauseVars (clause : JoinClause) : List Nat :=
  patVars clause.pattern

def joinClausesVars : List JoinClause -> List Nat
  | [] => []
  | clause :: rest => joinClauseVars clause ++ joinClausesVars rest

def eraseVars (xs : List Nat) (s : Subst) : Subst :=
  xs.foldl (fun acc x => eraseVar x acc) s

def substName (s : Subst) : Name -> Name
  | Name.free n => Name.free n
  | Name.fresh n => Name.fresh n
  | Name.var x =>
      match lookup x s with
      | some (Data.name n) => n
      | _ => Name.var x

def substData (s : Subst) : Data -> Data
  | Data.atom a => Data.atom a
  | Data.var x =>
      match lookup x s with
      | some d => d
      | none => Data.var x
  | Data.tuple xs => Data.tuple (xs.map (substData s))
  | Data.name n => Data.name (substName s n)

def substJoinClause (s : Subst) (clause : JoinClause) : JoinClause :=
  { channel := substName s clause.channel, pattern := clause.pattern }

def substJoinClauses (s : Subst) : List JoinClause -> List JoinClause
  | [] => []
  | clause :: rest => substJoinClause s clause :: substJoinClauses s rest

def substProc (s : Subst) : Proc -> Proc
  | Proc.nil => Proc.nil
  | Proc.par ps => Proc.par (ps.map (substProc s))
  | Proc.send ch data => Proc.send (substName s ch) (substData s data)
  | Proc.recv ch pat body =>
      Proc.recv (substName s ch) pat (substProc (eraseVars (patVars pat) s) body)
  | Proc.contract ch pat body =>
      Proc.contract (substName s ch) pat (substProc (eraseVars (patVars pat) s) body)
  | Proc.join clauses body =>
      Proc.join (substJoinClauses s clauses)
        (substProc (eraseVars (joinClausesVars clauses) s) body)
  | Proc.pjoin clauses body =>
      Proc.pjoin (substJoinClauses s clauses)
        (substProc (eraseVars (joinClausesVars clauses) s) body)
  | Proc.join2 c1 p1 c2 p2 body =>
      let s' := eraseVars (patVars p2) (eraseVars (patVars p1) s)
      Proc.join2 (substName s c1) p1 (substName s c2) p2 (substProc s' body)
  | Proc.pjoin2 c1 p1 c2 p2 body =>
      let s' := eraseVars (patVars p2) (eraseVars (patVars p1) s)
      Proc.pjoin2 (substName s c1) p1 (substName s c2) p2 (substProc s' body)
  | Proc.quote p => Proc.quote p
  | Proc.drop p => Proc.drop (substProc s p)
  | Proc.fresh x body => Proc.fresh x (substProc (eraseVar x s) body)

mutual
def matchPat : Pat -> Data -> Option Subst
  | Pat.wild, _ => some []
  | Pat.bind x, d => some [(x, d)]
  | Pat.atom a, Data.atom b => if a = b then some [] else none
  | Pat.tuple ps, Data.tuple ds => matchPats ps ds
  | _, _ => none

def matchPats : List Pat -> List Data -> Option Subst
  | [], [] => some []
  | p :: ps, d :: ds => do
      let left <- matchPat p d
      let right <- matchPats ps ds
      mergeSubst left right
  | _, _ => none
end

def matchJoinMessages : List JoinClause -> List (Name × Data) -> Option Subst
  | [], [] => some []
  | clause :: clauses, (channel, message) :: messages =>
      if nameEq clause.channel channel then do
        let left <- matchPat clause.pattern message
        let right <- matchJoinMessages clauses messages
        mergeSubst left right
      else
        none
  | _, _ => none

def nameWF (ctx : List Nat) : Name -> Bool
  | Name.free _ => true
  | Name.var x => ctx.contains x
  | Name.fresh _ => true

mutual
def dataWF (ctx : List Nat) : Data -> Bool
  | Data.atom _ => true
  | Data.var x => ctx.contains x
  | Data.tuple xs => dataListWF ctx xs
  | Data.name n => nameWF ctx n

def dataListWF (ctx : List Nat) : List Data -> Bool
  | [] => true
  | x :: xs => dataWF ctx x && dataListWF ctx xs
end

mutual
def patWF : Pat -> Bool
  | Pat.wild => true
  | Pat.bind _ => true
  | Pat.atom _ => true
  | Pat.tuple ps => patListWF ps

def patListWF : List Pat -> Bool
  | [] => true
  | p :: ps => patWF p && patListWF ps
end

def joinClauseWF (ctx : List Nat) (clause : JoinClause) : Bool :=
  nameWF ctx clause.channel && patWF clause.pattern

def joinClausesWF (ctx : List Nat) : List JoinClause -> Bool
  | [] => true
  | clause :: rest => joinClauseWF ctx clause && joinClausesWF ctx rest

def joinBodyCtx (clauses : List JoinClause) (ctx : List Nat) : List Nat :=
  joinClausesVars clauses ++ ctx

mutual
def procWF (ctx : List Nat) : Proc -> Bool
  | Proc.nil => true
  | Proc.par ps => procListWF ctx ps
  | Proc.send ch data => nameWF ctx ch && dataWF ctx data
  | Proc.recv ch pat body =>
      nameWF ctx ch && patWF pat && procWF (patVars pat ++ ctx) body
  | Proc.contract ch pat body =>
      nameWF ctx ch && patWF pat && procWF (patVars pat ++ ctx) body
  | Proc.join clauses body =>
      joinClausesWF ctx clauses && procWF (joinBodyCtx clauses ctx) body
  | Proc.pjoin clauses body =>
      joinClausesWF ctx clauses && procWF (joinBodyCtx clauses ctx) body
  | Proc.join2 c1 p1 c2 p2 body =>
      nameWF ctx c1 && patWF p1 && nameWF ctx c2 && patWF p2 &&
        procWF (patVars p1 ++ patVars p2 ++ ctx) body
  | Proc.pjoin2 c1 p1 c2 p2 body =>
      nameWF ctx c1 && patWF p1 && nameWF ctx c2 && patWF p2 &&
        procWF (patVars p1 ++ patVars p2 ++ ctx) body
  | Proc.quote p => procWF ctx p
  | Proc.drop (Proc.quote p) => procWF ctx p
  | Proc.drop _ => false
  | Proc.fresh x body => procWF (x :: ctx) body

def procListWF (ctx : List Nat) : List Proc -> Bool
  | [] => true
  | p :: ps => procWF ctx p && procListWF ctx ps
end

def checkedSubstProc (s : Subst) (body : Proc) : Option Proc :=
  let result := substProc s body
  if procWF [] result then some result else none

theorem checkedSubstProc_wf {s : Subst} {body result : Proc} :
    checkedSubstProc s body = some result ->
    procWF [] result = true := by
  intro h
  unfold checkedSubstProc at h
  by_cases hwf : procWF [] (substProc s body) = true
  · simp [hwf] at h
    cases h
    exact hwf
  · simp [hwf] at h

def joinBodyAfterMessages
    (clauses : List JoinClause) (messages : List (Name × Data))
    (body : Proc) : Option Proc := do
  let s <- matchJoinMessages clauses messages
  checkedSubstProc s body

theorem matchJoinMessages_length
    {clauses : List JoinClause} {messages : List (Name × Data)}
    {s : Subst} :
    matchJoinMessages clauses messages = some s ->
    messages.length = clauses.length := by
  induction clauses generalizing messages s with
  | nil =>
      cases messages with
      | nil =>
          intro _h
          rfl
      | cons message messages =>
          intro h
          simp [matchJoinMessages] at h
  | cons clause clauses ih =>
      cases messages with
      | nil =>
          intro h
          simp [matchJoinMessages] at h
      | cons message messages =>
          intro h
          by_cases hname : nameEq clause.channel message.1 = true
          · simp [matchJoinMessages, hname] at h
            cases hpat : matchPat clause.pattern message.2 with
            | none =>
                simp [hpat] at h
            | some left =>
                cases hrest : matchJoinMessages clauses messages with
                | none =>
                    simp [hpat, hrest] at h
                | some right =>
                    cases hmerge : mergeSubst left right with
                    | none =>
                        simp [hpat, hrest, hmerge] at h
                    | some merged =>
                        have hlen := ih hrest
                        simp [hpat, hrest, hmerge] at h
                        simp [hlen]
          · simp [matchJoinMessages, hname] at h

theorem joinBodyAfterMessages_wf
    {clauses : List JoinClause} {messages : List (Name × Data)}
    {body result : Proc} :
    joinBodyAfterMessages clauses messages body = some result ->
    procWF [] result = true := by
  intro h
  unfold joinBodyAfterMessages at h
  cases hmatch : matchJoinMessages clauses messages with
  | none =>
      simp [hmatch] at h
  | some s =>
      exact checkedSubstProc_wf (by
        simpa [hmatch] using h)

theorem joinBodyAfterMessages_length
    {clauses : List JoinClause} {messages : List (Name × Data)}
    {body result : Proc} :
    joinBodyAfterMessages clauses messages body = some result ->
    messages.length = clauses.length := by
  intro h
  unfold joinBodyAfterMessages at h
  cases hmatch : matchJoinMessages clauses messages with
  | none =>
      simp [hmatch] at h
  | some s =>
      exact matchJoinMessages_length hmatch

inductive Step : Proc -> Proc -> Prop where
  | dropQuote :
      Step (Proc.drop (Proc.quote p)) p
  | recvComm :
      matchPat pat msg = some s ->
      checkedSubstProc s body = some result ->
      Step (Proc.par [Proc.send ch msg, Proc.recv ch pat body]) result
  | recvCommSwap :
      matchPat pat msg = some s ->
      checkedSubstProc s body = some result ->
      Step (Proc.par [Proc.recv ch pat body, Proc.send ch msg]) result
  | contractComm :
      matchPat pat msg = some s ->
      checkedSubstProc s body = some result ->
      Step (Proc.par [Proc.send ch msg, Proc.contract ch pat body])
        (Proc.par [Proc.contract ch pat body, result])
  | join2Comm :
      matchPat p1 d1 = some s1 ->
      matchPat p2 d2 = some s2 ->
      mergeSubst s1 s2 = some s ->
      checkedSubstProc s body = some result ->
      Step (Proc.par [Proc.send c1 d1, Proc.send c2 d2, Proc.join2 c1 p1 c2 p2 body])
        result
  | pjoin2Comm :
      matchPat p1 d1 = some s1 ->
      matchPat p2 d2 = some s2 ->
      mergeSubst s1 s2 = some s ->
      checkedSubstProc s body = some result ->
      Step (Proc.par [Proc.send c1 d1, Proc.send c2 d2, Proc.pjoin2 c1 p1 c2 p2 body])
        (Proc.par [Proc.pjoin2 c1 p1 c2 p2 body, result])
  | joinComm :
      joinBodyAfterMessages clauses messages body = some result ->
      Step
        (Proc.par ((messages.map (fun m => Proc.send m.1 m.2)) ++
          [Proc.join clauses body]))
        result
  | pjoinComm :
      joinBodyAfterMessages clauses messages body = some result ->
      Step
        (Proc.par ((messages.map (fun m => Proc.send m.1 m.2)) ++
          [Proc.pjoin clauses body]))
        (Proc.par [Proc.pjoin clauses body, result])

theorem procListWF_append_single_right
    {ctx : List Nat} {components : List Proc} {last : Proc} :
    procListWF ctx (components ++ [last]) = true ->
    procWF ctx last = true := by
  intro h
  induction components with
  | nil =>
      simpa [procListWF] using h
  | cons component rest ih =>
      simp [procListWF] at h
      exact ih h.2

theorem Step_preserves_wf {p q : Proc} :
    Step p q -> procWF [] p = true -> procWF [] q = true := by
  intro hstep hp
  cases hstep with
  | dropQuote =>
      simpa [procWF] using hp
  | recvComm hmatch hcheck =>
      exact checkedSubstProc_wf hcheck
  | recvCommSwap hmatch hcheck =>
      exact checkedSubstProc_wf hcheck
  | contractComm hmatch hcheck =>
      have hresult := checkedSubstProc_wf hcheck
      simp [procWF, procListWF] at hp
      simp [procWF, procListWF, hp, hresult]
  | join2Comm hmatch1 hmatch2 hmerge hcheck =>
      exact checkedSubstProc_wf hcheck
  | pjoin2Comm hmatch1 hmatch2 hmerge hcheck =>
      have hresult := checkedSubstProc_wf hcheck
      simp [procWF, procListWF] at hp
      simp [procWF, procListWF, hp, hresult]
  | joinComm hbody =>
      exact joinBodyAfterMessages_wf hbody
  | pjoinComm hbody =>
      have hresult := joinBodyAfterMessages_wf hbody
      have hpjoin := procListWF_append_single_right hp
      simp [procWF, procListWF, hresult]
      simpa [procWF] using hpjoin

def firstStep : Proc -> Option Proc
  | Proc.drop (Proc.quote p) => some p
  | Proc.par [Proc.send ch msg, Proc.recv ch' pat body] =>
      if nameEq ch ch' then
        matchPat pat msg >>= fun s => checkedSubstProc s body
      else
        none
  | Proc.par [Proc.recv ch pat body, Proc.send ch' msg] =>
      if nameEq ch ch' then
        matchPat pat msg >>= fun s => checkedSubstProc s body
      else
        none
  | Proc.par [Proc.send ch msg, Proc.contract ch' pat body] =>
      if nameEq ch ch' then
        matchPat pat msg >>= fun s =>
          (checkedSubstProc s body).map
            (fun result => Proc.par [Proc.contract ch pat body, result])
      else
        none
  | Proc.par [Proc.send c1 d1, Proc.send c2 d2, Proc.join2 c1' p1 c2' p2 body] =>
      if nameEq c1 c1' && nameEq c2 c2' then
        match matchPat p1 d1, matchPat p2 d2 with
        | some s1, some s2 => mergeSubst s1 s2 >>= fun s => checkedSubstProc s body
        | _, _ => none
      else
        none
  | Proc.par [Proc.send c1 d1, Proc.send c2 d2, Proc.pjoin2 c1' p1 c2' p2 body] =>
      if nameEq c1 c1' && nameEq c2 c2' then
        match matchPat p1 d1, matchPat p2 d2 with
        | some s1, some s2 =>
            mergeSubst s1 s2 >>= fun s =>
              (checkedSubstProc s body).map
                (fun result => Proc.par [Proc.pjoin2 c1' p1 c2' p2 body, result])
        | _, _ => none
      else
        none
  | _ => none

mutual
def patEq : Pat -> Pat -> Bool
  | Pat.wild, Pat.wild => true
  | Pat.bind a, Pat.bind b => a == b
  | Pat.atom a, Pat.atom b => a == b
  | Pat.tuple xs, Pat.tuple ys => patListEq xs ys
  | _, _ => false

def patListEq : List Pat -> List Pat -> Bool
  | [], [] => true
  | x :: xs, y :: ys => patEq x y && patListEq xs ys
  | _, _ => false
end

mutual
def joinClauseEq (a b : JoinClause) : Bool :=
  nameEq a.channel b.channel && patEq a.pattern b.pattern

def joinClauseListEq : List JoinClause -> List JoinClause -> Bool
  | [], [] => true
  | x :: xs, y :: ys => joinClauseEq x y && joinClauseListEq xs ys
  | _, _ => false
end

mutual
def procEq : Proc -> Proc -> Bool
  | Proc.nil, Proc.nil => true
  | Proc.par xs, Proc.par ys => procListEq xs ys
  | Proc.send c d, Proc.send c' d' => nameEq c c' && dataEq d d'
  | Proc.recv c p b, Proc.recv c' p' b' =>
      nameEq c c' && patEq p p' && procEq b b'
  | Proc.contract c p b, Proc.contract c' p' b' =>
      nameEq c c' && patEq p p' && procEq b b'
  | Proc.join clauses b, Proc.join clauses' b' =>
      joinClauseListEq clauses clauses' && procEq b b'
  | Proc.pjoin clauses b, Proc.pjoin clauses' b' =>
      joinClauseListEq clauses clauses' && procEq b b'
  | Proc.join2 c1 p1 c2 p2 b, Proc.join2 c1' p1' c2' p2' b' =>
      nameEq c1 c1' && patEq p1 p1' && nameEq c2 c2' &&
        patEq p2 p2' && procEq b b'
  | Proc.pjoin2 c1 p1 c2 p2 b, Proc.pjoin2 c1' p1' c2' p2' b' =>
      nameEq c1 c1' && patEq p1 p1' && nameEq c2 c2' &&
        patEq p2 p2' && procEq b b'
  | Proc.quote p, Proc.quote q => procEq p q
  | Proc.drop p, Proc.drop q => procEq p q
  | Proc.fresh x p, Proc.fresh y q => x == y && procEq p q
  | _, _ => false

def procListEq : List Proc -> List Proc -> Bool
  | [], [] => true
  | x :: xs, y :: ys => procEq x y && procListEq xs ys
  | _, _ => false
end

def optionProcEq : Option Proc -> Option Proc -> Bool
  | none, none => true
  | some p, some q => procEq p q
  | _, _ => false

theorem nameEq_true {a b : Name} : nameEq a b = true -> a = b := by
  intro h
  cases a <;> cases b <;> simp [nameEq] at h
  · cases h
    rfl
  · cases h
    rfl
  · cases h
    rfl

theorem firstStep_sound : ∀ {p q : Proc}, firstStep p = some q -> Step p q
  | Proc.drop (Proc.quote p), q, h => by
      simp [firstStep] at h
      cases h
      exact Step.dropQuote
  | Proc.par [Proc.send ch msg, Proc.recv ch' pat body], q, h => by
      by_cases hname : nameEq ch ch' = true
      case pos =>
        cases hmatch : matchPat pat msg with
        | none =>
            simp [firstStep, hname, hmatch] at h
        | some s =>
            cases hcheck : checkedSubstProc s body with
            | none =>
                simp [firstStep, hname, hmatch, hcheck] at h
            | some result =>
                simp [firstStep, hname, hmatch, hcheck] at h
                cases h
                cases nameEq_true hname
                exact Step.recvComm hmatch hcheck
      case neg =>
        simp [firstStep, hname] at h
  | Proc.par [Proc.recv ch pat body, Proc.send ch' msg], q, h => by
      by_cases hname : nameEq ch ch' = true
      case pos =>
        cases hmatch : matchPat pat msg with
        | none =>
            simp [firstStep, hname, hmatch] at h
        | some s =>
            cases hcheck : checkedSubstProc s body with
            | none =>
                simp [firstStep, hname, hmatch, hcheck] at h
            | some result =>
                simp [firstStep, hname, hmatch, hcheck] at h
                cases h
                cases nameEq_true hname
                exact Step.recvCommSwap hmatch hcheck
      case neg =>
        simp [firstStep, hname] at h
  | Proc.par [Proc.send ch msg, Proc.contract ch' pat body], q, h => by
      by_cases hname : nameEq ch ch' = true
      case pos =>
        cases hmatch : matchPat pat msg with
        | none =>
            simp [firstStep, hname, hmatch] at h
        | some s =>
            cases hcheck : checkedSubstProc s body with
            | none =>
                simp [firstStep, hname, hmatch, hcheck] at h
            | some result =>
                simp [firstStep, hname, hmatch, hcheck] at h
                cases h
                cases nameEq_true hname
                exact Step.contractComm hmatch hcheck
      case neg =>
        simp [firstStep, hname] at h
  | Proc.par [Proc.send c1 d1, Proc.send c2 d2, Proc.join2 c1' p1 c2' p2 body], q, h => by
      by_cases hnames : (nameEq c1 c1' && nameEq c2 c2') = true
      case pos =>
        have hpair : nameEq c1 c1' = true ∧ nameEq c2 c2' = true := by
          simp at hnames
          exact hnames
        have hc1 : c1 = c1' := nameEq_true hpair.1
        have hc2 : c2 = c2' := nameEq_true hpair.2
        cases hmatch1 : matchPat p1 d1 with
        | none =>
            simp [firstStep, hnames, hmatch1] at h
        | some s1 =>
            cases hmatch2 : matchPat p2 d2 with
            | none =>
                simp [firstStep, hnames, hmatch1, hmatch2] at h
            | some s2 =>
                cases hmerge : mergeSubst s1 s2 with
                | none =>
                    simp [firstStep, hnames, hmatch1, hmatch2, hmerge] at h
                | some s =>
                    cases hcheck : checkedSubstProc s body with
                    | none =>
                        simp [firstStep, hnames, hmatch1, hmatch2, hmerge, hcheck] at h
                    | some result =>
                        simp [firstStep, hnames, hmatch1, hmatch2, hmerge, hcheck] at h
                        cases h
                        cases hc1
                        cases hc2
                        exact Step.join2Comm hmatch1 hmatch2 hmerge hcheck
      case neg =>
        simp [firstStep, hnames] at h
  | Proc.par [Proc.send c1 d1, Proc.send c2 d2, Proc.pjoin2 c1' p1 c2' p2 body], q, h => by
      by_cases hnames : (nameEq c1 c1' && nameEq c2 c2') = true
      case pos =>
        have hpair : nameEq c1 c1' = true ∧ nameEq c2 c2' = true := by
          simp at hnames
          exact hnames
        have hc1 : c1 = c1' := nameEq_true hpair.1
        have hc2 : c2 = c2' := nameEq_true hpair.2
        cases hmatch1 : matchPat p1 d1 with
        | none =>
            simp [firstStep, hnames, hmatch1] at h
        | some s1 =>
            cases hmatch2 : matchPat p2 d2 with
            | none =>
                simp [firstStep, hnames, hmatch1, hmatch2] at h
            | some s2 =>
                cases hmerge : mergeSubst s1 s2 with
                | none =>
                    simp [firstStep, hnames, hmatch1, hmatch2, hmerge] at h
                | some s =>
                    cases hcheck : checkedSubstProc s body with
                    | none =>
                        simp [firstStep, hnames, hmatch1, hmatch2, hmerge, hcheck] at h
                    | some result =>
                        simp [firstStep, hnames, hmatch1, hmatch2, hmerge, hcheck] at h
                        cases h
                        cases hc1
                        cases hc2
                        exact Step.pjoin2Comm hmatch1 hmatch2 hmerge hcheck
      case neg =>
        simp [firstStep, hnames] at h
  | Proc.nil, _, h => by
      simp [firstStep] at h
  | Proc.send _ _, _, h => by
      simp [firstStep] at h
  | Proc.recv _ _ _, _, h => by
      simp [firstStep] at h
  | Proc.contract _ _ _, _, h => by
      simp [firstStep] at h
  | Proc.join _ _, _, h => by
      simp [firstStep] at h
  | Proc.pjoin _ _, _, h => by
      simp [firstStep] at h
  | Proc.join2 _ _ _ _ _, _, h => by
      simp [firstStep] at h
  | Proc.pjoin2 _ _ _ _ _, _, h => by
      simp [firstStep] at h
  | Proc.quote _, _, h => by
      simp [firstStep] at h
  | Proc.drop p, _, h => by
      cases p <;> simp [firstStep] at h
      case quote p =>
        cases h
        exact Step.dropQuote
  | Proc.fresh _ _, _, h => by
      simp [firstStep] at h
  | Proc.par [], _, h => by
      simp [firstStep] at h
  | Proc.par [_], _, h => by
      simp [firstStep] at h
  | Proc.par [p1, p2], q, h => by
      cases p1 <;> cases p2 <;> simp [firstStep] at h
      case send.recv ch msg ch' pat body =>
        by_cases hname : nameEq ch ch' = true
        case pos =>
          cases hmatch : matchPat pat msg with
          | none =>
              simp [hname, hmatch] at h
          | some s =>
              cases hcheck : checkedSubstProc s body with
              | none =>
                  simp [hname, hmatch, hcheck] at h
              | some result =>
                  simp [hname, hmatch, hcheck] at h
                  cases h
                  cases nameEq_true hname
                  exact Step.recvComm hmatch hcheck
        case neg =>
          simp [hname] at h
      case recv.send ch pat body ch' msg =>
        by_cases hname : nameEq ch ch' = true
        case pos =>
          cases hmatch : matchPat pat msg with
          | none =>
              simp [hname, hmatch] at h
          | some s =>
              cases hcheck : checkedSubstProc s body with
              | none =>
                  simp [hname, hmatch, hcheck] at h
              | some result =>
                  simp [hname, hmatch, hcheck] at h
                  cases h
                  cases nameEq_true hname
                  exact Step.recvCommSwap hmatch hcheck
        case neg =>
          simp [hname] at h
      case send.contract ch msg ch' pat body =>
        by_cases hname : nameEq ch ch' = true
        case pos =>
          cases hmatch : matchPat pat msg with
          | none =>
              simp [hname, hmatch] at h
          | some s =>
              cases hcheck : checkedSubstProc s body with
              | none =>
                  simp [hname, hmatch, hcheck] at h
              | some result =>
                  simp [hname, hmatch, hcheck] at h
                  cases h
                  cases nameEq_true hname
                  exact Step.contractComm hmatch hcheck
        case neg =>
          simp [hname] at h
  | Proc.par [p1, p2, p3], q, h => by
      cases p1 <;> cases p2 <;> cases p3 <;> simp [firstStep] at h
      case send.send.join2 c1 d1 c2 d2 j1 pat1 j2 pat2 body =>
        rcases h with ⟨⟨hname1, hname2⟩, hrest⟩
        have hc1 := nameEq_true hname1
        have hc2 := nameEq_true hname2
        cases hmatch1 : matchPat pat1 d1 with
        | none =>
            simp [hmatch1] at hrest
        | some s1 =>
            cases hmatch2 : matchPat pat2 d2 with
            | none =>
                simp [hmatch1, hmatch2] at hrest
            | some s2 =>
                cases hmerge : mergeSubst s1 s2 with
                | none =>
                    simp [hmatch1, hmatch2, hmerge] at hrest
                | some s =>
                    cases hcheck : checkedSubstProc s body with
                    | none =>
                        simp [hmatch1, hmatch2, hmerge, hcheck] at hrest
                    | some result =>
                        simp [hmatch1, hmatch2, hmerge, hcheck] at hrest
                        cases hrest
                        cases hc1
                        cases hc2
                        exact Step.join2Comm hmatch1 hmatch2 hmerge hcheck
      case send.send.pjoin2 c1 d1 c2 d2 j1 pat1 j2 pat2 body =>
        rcases h with ⟨⟨hname1, hname2⟩, hrest⟩
        have hc1 := nameEq_true hname1
        have hc2 := nameEq_true hname2
        cases hmatch1 : matchPat pat1 d1 with
        | none =>
            simp [hmatch1] at hrest
        | some s1 =>
            cases hmatch2 : matchPat pat2 d2 with
            | none =>
                simp [hmatch1, hmatch2] at hrest
            | some s2 =>
                cases hmerge : mergeSubst s1 s2 with
                | none =>
                    simp [hmatch1, hmatch2, hmerge] at hrest
                | some s =>
                    cases hcheck : checkedSubstProc s body with
                    | none =>
                        simp [hmatch1, hmatch2, hmerge, hcheck] at hrest
                    | some result =>
                        simp [hmatch1, hmatch2, hmerge, hcheck] at hrest
                        cases hrest
                        cases hc1
                        cases hc2
                        exact Step.pjoin2Comm hmatch1 hmatch2 hmerge hcheck
  | Proc.par (_ :: _ :: _ :: _ :: _), _, h => by
      simp [firstStep] at h

inductive StructuralCongruence : Proc -> Proc -> Prop where
  | refl (p : Proc) : StructuralCongruence p p
  | symm (p q : Proc) :
      StructuralCongruence p q ->
      StructuralCongruence q p
  | trans (p q r : Proc) :
      StructuralCongruence p q ->
      StructuralCongruence q r ->
      StructuralCongruence p r
  | alpha (p q : Proc) :
      p = q ->
      StructuralCongruence p q
  | par_singleton (p : Proc) :
      StructuralCongruence (Proc.par [p]) p
  | par_nil_left (p : Proc) :
      StructuralCongruence (Proc.par [Proc.nil, p]) p
  | par_nil_right (p : Proc) :
      StructuralCongruence (Proc.par [p, Proc.nil]) p
  | par_perm (xs ys : List Proc) :
      xs.Perm ys ->
      StructuralCongruence (Proc.par xs) (Proc.par ys)
  | par_cong (xs ys : List Proc) :
      xs.length = ys.length ->
      (∀ i hx hy, StructuralCongruence (xs.get ⟨i, hx⟩) (ys.get ⟨i, hy⟩)) ->
      StructuralCongruence (Proc.par xs) (Proc.par ys)
  | par_flatten (before nested after : List Proc) :
      StructuralCongruence
        (Proc.par (before ++ [Proc.par nested] ++ after))
        (Proc.par (before ++ nested ++ after))

theorem StructuralCongruence_equivalence : Equivalence StructuralCongruence where
  refl := StructuralCongruence.refl
  symm := StructuralCongruence.symm _ _
  trans := StructuralCongruence.trans _ _ _

theorem par_comm_sc (p q : Proc) :
    StructuralCongruence (Proc.par [p, q]) (Proc.par [q, p]) := by
  exact StructuralCongruence.par_perm [p, q] [q, p] (by
    simpa using (List.Perm.symm (List.Perm.swap p q [])))

theorem par_nil_left_sc (p : Proc) :
    StructuralCongruence (Proc.par [Proc.nil, p]) p :=
  StructuralCongruence.par_nil_left p

theorem par_nil_right_sc (p : Proc) :
    StructuralCongruence (Proc.par [p, Proc.nil]) p :=
  StructuralCongruence.par_nil_right p

theorem par_flatten_two_sc (p q r : Proc) :
    StructuralCongruence (Proc.par [p, Proc.par [q, r]]) (Proc.par [p, q, r]) := by
  simpa using StructuralCongruence.par_flatten [p] [q, r] []

theorem par_assoc_sc (p q r : Proc) :
    StructuralCongruence
      (Proc.par [Proc.par [p, q], r])
      (Proc.par [p, Proc.par [q, r]]) := by
  exact StructuralCongruence.trans _ _ _
    (by simpa using StructuralCongruence.par_flatten [] [p, q] [r])
    (by
      apply StructuralCongruence.symm
      simpa using StructuralCongruence.par_flatten [p] [q, r] [])

inductive EvalContext : Type where
  | hole : EvalContext
  | par (before after : List Proc) : EvalContext
  deriving Repr

def fillEvalContext : EvalContext -> Proc -> Proc
  | .hole, p => p
  | .par before after, p => Proc.par (before ++ [p] ++ after)

theorem fillEvalContext_hole (p : Proc) :
    fillEvalContext .hole p = p := by
  rfl

inductive StepClosed : Proc -> Proc -> Prop where
  | core {p q : Proc} :
      Step p q ->
      StepClosed p q
  | context {k : EvalContext} {p q : Proc} :
      StepClosed p q ->
      StepClosed (fillEvalContext k p) (fillEvalContext k q)
  | struct {p p' q q' : Proc} :
      StructuralCongruence p p' ->
      StepClosed p' q' ->
      StructuralCongruence q' q ->
      StepClosed p q

theorem fillEvalContext_preserves_step
    (k : EvalContext) {p q : Proc} :
    Step p q -> StepClosed (fillEvalContext k p) (fillEvalContext k q) := by
  intro h
  exact StepClosed.context (StepClosed.core h)

theorem firstStep_closed_sound {p q : Proc} :
    firstStep p = some q -> StepClosed p q := by
  intro h
  exact StepClosed.core (firstStep_sound h)

def runSteps : Nat -> Proc -> Proc
  | 0, p => p
  | n + 1, p =>
      match firstStep p with
      | none => p
      | some q => runSteps n q

theorem runSteps_stuck {p : Proc} (h : firstStep p = none) :
    forall n, runSteps n p = p := by
  intro n
  cases n with
  | zero => rfl
  | succ n => simp [runSteps, h]

theorem runSteps_slice_resume
    (m n : Nat) (p : Proc) :
    runSteps (m + n) p =
      runSteps n (runSteps m p) := by
  induction m generalizing p with
  | zero =>
      simp [runSteps]
  | succ m ih =>
      cases hstep : firstStep p with
      | none =>
          simp [Nat.succ_add, runSteps, hstep, runSteps_stuck hstep]
      | some q =>
          simpa [Nat.succ_add, runSteps, hstep] using ih q

def sendCandidates : List Proc -> List (Name × Data)
  | [] => []
  | Proc.send channel data :: rest =>
      (channel, data) :: sendCandidates rest
  | _ :: rest => sendCandidates rest

def indexedSendCandidates (target : Name) :
    List Proc -> List (Name × Data)
  | [] => []
  | Proc.send channel data :: rest =>
      if nameEq target channel then
        (channel, data) :: indexedSendCandidates target rest
      else
        indexedSendCandidates target rest
  | _ :: rest => indexedSendCandidates target rest

theorem indexedSendCandidates_sound
    {target : Name} {candidate : Name × Data} :
    forall {components : List Proc},
      candidate ∈ indexedSendCandidates target components ->
      candidate ∈ sendCandidates components := by
  intro components
  induction components with
  | nil =>
      intro h
      simp [indexedSendCandidates] at h
  | cons component rest ih =>
      intro h
      cases component <;>
        simp [indexedSendCandidates, sendCandidates] at h ⊢
      case send channel data =>
        by_cases hname : nameEq target channel
        · simp [hname] at h ⊢
          cases h with
          | inl hhead => exact Or.inl hhead
          | inr htail => exact Or.inr (ih htail)
        · simp [hname] at h ⊢
          exact Or.inr (ih h)
      all_goals exact ih h

theorem indexedSendCandidates_complete
    {target channel : Name} {data : Data}
    (hname : nameEq target channel = true) :
    forall {components : List Proc},
      (channel, data) ∈ sendCandidates components ->
      (channel, data) ∈ indexedSendCandidates target components := by
  intro components
  induction components with
  | nil =>
      intro h
      simp [sendCandidates] at h
  | cons component rest ih =>
      intro h
      cases component <;>
        simp [indexedSendCandidates, sendCandidates] at h ⊢
      case send candidateChannel candidateData =>
        by_cases htarget : nameEq target candidateChannel
        · simp [htarget] at h ⊢
          cases h with
          | inl hhead => exact Or.inl hhead
          | inr htail => exact Or.inr (ih htail)
        · simp [htarget] at h ⊢
          cases h with
          | inl hhead =>
              rcases hhead with ⟨hchannel, _hdata⟩
              cases hchannel
              exact False.elim (htarget hname)
          | inr htail => exact ih htail
      all_goals exact ih h

def removeFirstIndexedSend (target : Name) :
    List Proc -> List Proc
  | [] => []
  | Proc.send channel data :: rest =>
      if nameEq target channel then
        rest
      else
        Proc.send channel data :: removeFirstIndexedSend target rest
  | component :: rest => component :: removeFirstIndexedSend target rest

def removeIndexedSends (targets : List Name) (components : List Proc) : List Proc :=
  targets.foldl (fun acc target => removeFirstIndexedSend target acc) components

def removeFirstMatchedSend (target : Name) (message : Data) :
    List Proc -> List Proc
  | [] => []
  | Proc.send channel data :: rest =>
      if nameEq target channel && dataEq message data then
        rest
      else
        Proc.send channel data :: removeFirstMatchedSend target message rest
  | component :: rest => component :: removeFirstMatchedSend target message rest

def removeMatchedMessages (messages : List (Name × Data))
    (components : List Proc) : List Proc :=
  messages.foldl
    (fun acc message => removeFirstMatchedSend message.1 message.2 acc)
    components

theorem sendCandidates_removeFirstIndexedSend_sound
    {target : Name} {candidate : Name × Data} :
    forall {components : List Proc},
      candidate ∈ sendCandidates (removeFirstIndexedSend target components) ->
      candidate ∈ sendCandidates components := by
  intro components
  induction components with
  | nil =>
      intro h
      simp [removeFirstIndexedSend, sendCandidates] at h
  | cons component rest ih =>
      intro h
      cases component <;>
        simp [removeFirstIndexedSend, sendCandidates] at h ⊢
      case send channel data =>
        by_cases hname : nameEq target channel
        · simp [hname] at h ⊢
          exact Or.inr h
        · simp [hname, sendCandidates] at h ⊢
          cases h with
          | inl hhead => exact Or.inl hhead
          | inr htail => exact Or.inr (ih htail)
      all_goals exact ih h

theorem sendCandidates_removeFirstMatchedSend_sound
    {target : Name} {message : Data} {candidate : Name × Data} :
    forall {components : List Proc},
      candidate ∈ sendCandidates
        (removeFirstMatchedSend target message components) ->
      candidate ∈ sendCandidates components := by
  intro components
  induction components with
  | nil =>
      intro h
      simp [removeFirstMatchedSend, sendCandidates] at h
  | cons component rest ih =>
      intro h
      cases component
      case send channel data =>
        by_cases hmatch : nameEq target channel && dataEq message data
        · have htail : candidate ∈ sendCandidates rest := by
            simpa [removeFirstMatchedSend, hmatch] using h
          simpa [sendCandidates] using
            (Or.inr htail :
              candidate = (channel, data) ∨
                candidate ∈ sendCandidates rest)
        · have h' :
              candidate = (channel, data) ∨
                candidate ∈ sendCandidates
                  (removeFirstMatchedSend target message rest) := by
            simpa [removeFirstMatchedSend, sendCandidates, hmatch] using h
          cases h' with
          | inl hhead =>
              simpa [sendCandidates] using
                (Or.inl hhead :
                  candidate = (channel, data) ∨
                    candidate ∈ sendCandidates rest)
          | inr htail =>
              simpa [sendCandidates] using
                (Or.inr (ih htail) :
                  candidate = (channel, data) ∨
                    candidate ∈ sendCandidates rest)
      all_goals
        exact ih (by
          simpa [removeFirstMatchedSend, sendCandidates] using h)

theorem indexedSendCandidates_removeFirstIndexedSend_sound
    {target : Name} {candidate : Name × Data} :
    forall {components : List Proc},
      candidate ∈ indexedSendCandidates target
        (removeFirstIndexedSend target components) ->
      candidate ∈ indexedSendCandidates target components := by
  intro components
  induction components with
  | nil =>
      intro h
      simp [removeFirstIndexedSend, indexedSendCandidates] at h
  | cons component rest ih =>
      intro h
      cases component <;>
        simp [removeFirstIndexedSend, indexedSendCandidates] at h ⊢
      case send channel data =>
        by_cases hname : nameEq target channel
        · simp [hname] at h ⊢
          exact Or.inr h
        · simp [hname, indexedSendCandidates] at h ⊢
          exact ih h
      all_goals exact ih h

theorem indexedSendCandidates_removeFirst_head
    {target channel : Name} {data : Data} {rest : List Proc}
    (hname : nameEq target channel = true) :
    indexedSendCandidates target
      (removeFirstIndexedSend target (Proc.send channel data :: rest)) =
    indexedSendCandidates target rest := by
  simp [removeFirstIndexedSend, hname]

theorem sendCandidates_removeIndexedSends_sound
    {targets : List Name} {candidate : Name × Data} :
    forall {components : List Proc},
      candidate ∈ sendCandidates (removeIndexedSends targets components) ->
      candidate ∈ sendCandidates components := by
  induction targets generalizing candidate with
  | nil =>
      intro components h
      simpa [removeIndexedSends] using h
  | cons target rest ih =>
      intro components h
      have htail :
          candidate ∈ sendCandidates
            (removeFirstIndexedSend target components) := by
        exact ih h
      exact sendCandidates_removeFirstIndexedSend_sound htail

theorem sendCandidates_removeMatchedMessages_sound
    {messages : List (Name × Data)} {candidate : Name × Data} :
    forall {components : List Proc},
      candidate ∈ sendCandidates (removeMatchedMessages messages components) ->
      candidate ∈ sendCandidates components := by
  induction messages generalizing candidate with
  | nil =>
      intro components h
      simpa [removeMatchedMessages] using h
  | cons message rest ih =>
      intro components h
      have htail :
          candidate ∈ sendCandidates
            (removeFirstMatchedSend message.1 message.2 components) := by
        exact ih h
      exact sendCandidates_removeFirstMatchedSend_sound htail

def indexedJoinCandidateSets : List JoinClause -> List Proc -> List (List (Name × Data))
  | [], _ => []
  | clause :: rest, components =>
      indexedSendCandidates clause.channel components ::
        indexedJoinCandidateSets rest components

theorem indexedJoinCandidateSets_length
    (clauses : List JoinClause) (components : List Proc) :
    (indexedJoinCandidateSets clauses components).length = clauses.length := by
  induction clauses with
  | nil => rfl
  | cons clause rest ih =>
      simp [indexedJoinCandidateSets, ih]

theorem indexedJoinCandidateSets_sound
    {clauses : List JoinClause} {components : List Proc}
    {candidateSet : List (Name × Data)} {candidate : Name × Data} :
    candidateSet ∈ indexedJoinCandidateSets clauses components ->
    candidate ∈ candidateSet ->
    candidate ∈ sendCandidates components := by
  intro hset hcandidate
  induction clauses with
  | nil =>
      simp [indexedJoinCandidateSets] at hset
  | cons clause rest ih =>
      simp [indexedJoinCandidateSets] at hset
      cases hset with
      | inl hhead =>
          cases hhead
          exact indexedSendCandidates_sound hcandidate
      | inr htail =>
          exact ih htail

theorem indexedJoinCandidateSets_clause_complete
    {clause : JoinClause} {clauses : List JoinClause}
    {components : List Proc} {channel : Name} {data : Data}
    (hname : nameEq clause.channel channel = true) :
    (channel, data) ∈ sendCandidates components ->
    ∃ candidateSet,
      candidateSet ∈ indexedJoinCandidateSets (clause :: clauses) components ∧
        (channel, data) ∈ candidateSet := by
  intro hcandidate
  refine ⟨indexedSendCandidates clause.channel components, ?_, ?_⟩
  · simp [indexedJoinCandidateSets]
  · exact indexedSendCandidates_complete hname hcandidate

theorem indexedJoinCandidateSets_clause_complete_any
    {clause : JoinClause} {clauses : List JoinClause}
    {components : List Proc} {channel : Name} {data : Data}
    (hclause : clause ∈ clauses)
    (hname : nameEq clause.channel channel = true)
    (hcandidate : (channel, data) ∈ sendCandidates components) :
    ∃ candidateSet,
      candidateSet ∈ indexedJoinCandidateSets clauses components ∧
        (channel, data) ∈ candidateSet := by
  induction clauses with
  | nil =>
      simp at hclause
  | cons head rest ih =>
      simp at hclause
      cases hclause with
      | inl hhead =>
          cases hhead
          refine ⟨indexedSendCandidates clause.channel components, ?_, ?_⟩
          · simp [indexedJoinCandidateSets]
          · exact indexedSendCandidates_complete hname hcandidate
      | inr htail =>
          rcases ih htail with ⟨candidateSet, hset, hmember⟩
          refine ⟨candidateSet, ?_, hmember⟩
          simp [indexedJoinCandidateSets, hset]

theorem indexedJoinCandidateSets_removeFirst_sound
    {clauses : List JoinClause} {components : List Proc}
    {target : Name} {candidateSet : List (Name × Data)}
    {candidate : Name × Data} :
    candidateSet ∈ indexedJoinCandidateSets clauses
      (removeFirstIndexedSend target components) ->
    candidate ∈ candidateSet ->
    candidate ∈ sendCandidates components := by
  intro hset hcandidate
  exact sendCandidates_removeFirstIndexedSend_sound
    (indexedJoinCandidateSets_sound hset hcandidate)

theorem indexedJoinCandidateSets_removeIndexedSends_sound
    {clauses : List JoinClause} {components : List Proc}
    {targets : List Name} {candidateSet : List (Name × Data)}
    {candidate : Name × Data} :
    candidateSet ∈ indexedJoinCandidateSets clauses
      (removeIndexedSends targets components) ->
    candidate ∈ candidateSet ->
    candidate ∈ sendCandidates components := by
  intro hset hcandidate
  exact sendCandidates_removeIndexedSends_sound
    (indexedJoinCandidateSets_sound hset hcandidate)

theorem indexedJoinCandidateSets_removeMatchedMessages_sound
    {clauses : List JoinClause} {components : List Proc}
    {messages : List (Name × Data)} {candidateSet : List (Name × Data)}
    {candidate : Name × Data} :
    candidateSet ∈ indexedJoinCandidateSets clauses
      (removeMatchedMessages messages components) ->
    candidate ∈ candidateSet ->
    candidate ∈ sendCandidates components := by
  intro hset hcandidate
  exact sendCandidates_removeMatchedMessages_sound
    (indexedJoinCandidateSets_sound hset hcandidate)

def everyJoinClauseCandidateCovered
    (clauses : List JoinClause) (components : List Proc) : Prop :=
  ∀ clause, clause ∈ clauses ->
    ∀ channel data,
      nameEq clause.channel channel = true ->
      (channel, data) ∈ sendCandidates components ->
      ∃ candidateSet,
        candidateSet ∈ indexedJoinCandidateSets clauses components ∧
          (channel, data) ∈ candidateSet

theorem indexedJoinCandidateSets_arbitrary_clause_complete
    (clauses : List JoinClause) (components : List Proc) :
    everyJoinClauseCandidateCovered clauses components := by
  intro clause hclause channel data hname hcandidate
  exact indexedJoinCandidateSets_clause_complete_any hclause hname hcandidate

inductive Feature : Type where
  | nil
  | par
  | send
  | recv
  | fresh
  | quote
  | drop
  | subst
  | alpha
  | structCong
  | contextClosure
  | pattern
  | join
  | persistence
  deriving Repr, DecidableEq

abbrev FeatureSet := Feature -> Prop

def FeatureSet.Subset (a b : FeatureSet) : Prop :=
  forall f, a f -> b f

infix:50 " ⊆f " => FeatureSet.Subset

inductive OperationalSeed : Feature -> Prop where
  | nil : OperationalSeed Feature.nil
  | par : OperationalSeed Feature.par
  | send : OperationalSeed Feature.send
  | recv : OperationalSeed Feature.recv
  | fresh : OperationalSeed Feature.fresh
  | quote : OperationalSeed Feature.quote
  | drop : OperationalSeed Feature.drop

inductive OperationalDependency : Feature -> Feature -> Prop where
  | recvNeedsPattern : OperationalDependency Feature.recv Feature.pattern
  | recvNeedsSubst : OperationalDependency Feature.recv Feature.subst
  | freshNeedsSubst : OperationalDependency Feature.fresh Feature.subst
  | freshNeedsAlpha : OperationalDependency Feature.fresh Feature.alpha
  | parNeedsStructCong : OperationalDependency Feature.par Feature.structCong
  | parNeedsContextClosure : OperationalDependency Feature.par Feature.contextClosure
  | structCongNeedsNil : OperationalDependency Feature.structCong Feature.nil
  | structCongNeedsPar : OperationalDependency Feature.structCong Feature.par
  | contextClosureNeedsPar : OperationalDependency Feature.contextClosure Feature.par

inductive MandatoryFeature : Feature -> Prop where
  | seed {f : Feature} : OperationalSeed f -> MandatoryFeature f
  | dependency {f g : Feature} :
      MandatoryFeature f ->
      OperationalDependency f g ->
      MandatoryFeature g

def OperationallyClosed (s : FeatureSet) : Prop :=
  (forall f, OperationalSeed f -> s f) /\
  (forall {f g}, s f -> OperationalDependency f g -> s g)

def RhoMinimum : FeatureSet :=
  MandatoryFeature

def RhoImplemented : FeatureSet :=
  fun f => MandatoryFeature f \/ f = Feature.join \/ f = Feature.persistence

theorem rhoMinimum_closed : OperationallyClosed RhoMinimum := by
  constructor
  · intro f h
    exact MandatoryFeature.seed h
  · intro f g hf hdep
    exact MandatoryFeature.dependency hf hdep

theorem rhoMinimum_least
    (s : FeatureSet) (hs : OperationallyClosed s) :
    RhoMinimum ⊆f s := by
  intro f hf
  induction hf with
  | seed hseed =>
      exact hs.1 _ hseed
  | dependency hf hdep ih =>
      exact hs.2 ih hdep

theorem rhoMinimum_subset_implemented :
    RhoMinimum ⊆f RhoImplemented := by
  intro f hf
  exact Or.inl hf

theorem join_not_mandatory :
    Not (RhoMinimum Feature.join) := by
  intro h
  cases h with
  | seed hseed =>
      cases hseed
  | dependency _ hdep =>
      cases hdep

theorem persistence_not_mandatory :
    Not (RhoMinimum Feature.persistence) := by
  intro h
  cases h with
  | seed hseed =>
      cases hseed
  | dependency _ hdep =>
      cases hdep

inductive NameSort : Type where
  | invalid
  | free
  | fresh
  | bound
  deriving Repr, DecidableEq

def nameSort (ctx : List Nat) : Name -> NameSort
  | Name.free _ => NameSort.free
  | Name.fresh _ => NameSort.fresh
  | Name.var x => if ctx.contains x then NameSort.bound else NameSort.invalid

def nameSortDirect : NameSort -> Bool
  | NameSort.free => true
  | NameSort.fresh => true
  | _ => false

def nameIndexable (ctx : List Nat) (name : Name) : Bool :=
  nameSortDirect (nameSort ctx name)

theorem nameSort_direct_wf {ctx : List Nat} {name : Name} :
    nameSortDirect (nameSort ctx name) = true -> nameWF ctx name = true := by
  intro h
  cases name with
  | free s =>
      rfl
  | fresh n =>
      rfl
  | var x =>
      by_cases hmem : x ∈ ctx
      · simp [nameSort, nameSortDirect, hmem] at h ⊢
      · simp [nameSort, nameSortDirect, hmem] at h

theorem nameIndexable_wf {ctx : List Nat} {name : Name} :
    nameIndexable ctx name = true -> nameWF ctx name = true := by
  intro h
  exact nameSort_direct_wf h

inductive NameTerm : Type where
  | direct : Name -> NameTerm
  | quotedProc : Proc -> NameTerm
  deriving Repr

inductive NameTermSort : Type where
  | invalid
  | free
  | fresh
  | bound
  | quotedProc
  deriving Repr, DecidableEq

def nameTermSort (ctx : List Nat) : NameTerm -> NameTermSort
  | NameTerm.direct name =>
      match nameSort ctx name with
      | NameSort.free => NameTermSort.free
      | NameSort.fresh => NameTermSort.fresh
      | NameSort.bound => NameTermSort.bound
      | NameSort.invalid => NameTermSort.invalid
  | NameTerm.quotedProc proc =>
      if procWF ctx proc then NameTermSort.quotedProc else NameTermSort.invalid

def nameTermDirectIndexable : NameTermSort -> Bool
  | NameTermSort.free => true
  | NameTermSort.fresh => true
  | _ => false

def nameTermIndexable (ctx : List Nat) (name : NameTerm) : Bool :=
  nameTermDirectIndexable (nameTermSort ctx name)

theorem nameTermIndexable_wf {ctx : List Nat} {name : Name} :
    nameTermIndexable ctx (NameTerm.direct name) = true ->
    nameWF ctx name = true := by
  intro h
  cases name with
  | free s =>
      rfl
  | fresh n =>
      rfl
  | var x =>
      by_cases hmem : x ∈ ctx
      · simp [nameWF, hmem]
      · simp [nameTermIndexable, nameTermDirectIndexable, nameTermSort,
              nameSort, hmem] at h

theorem boundName_wf_not_indexable {ctx : List Nat} {x : Nat}
    (hmem : x ∈ ctx) :
    nameWF ctx (Name.var x) = true /\
    nameIndexable ctx (Name.var x) = false := by
  constructor <;> simp [nameWF, nameIndexable, nameSort, nameSortDirect, hmem]

theorem quotedProc_wf_not_indexable {ctx : List Nat} {p : Proc}
    (hp : procWF ctx p = true) :
    nameTermSort ctx (NameTerm.quotedProc p) = NameTermSort.quotedProc /\
    nameTermIndexable ctx (NameTerm.quotedProc p) = false := by
  constructor <;>
    simp [nameTermSort, nameTermIndexable, nameTermDirectIndexable, hp]

theorem quotedProc_invalid_when_proc_invalid {ctx : List Nat} {p : Proc}
    (hp : procWF ctx p = false) :
    nameTermSort ctx (NameTerm.quotedProc p) = NameTermSort.invalid := by
  simp [nameTermSort, hp]

def ch : Name := Name.free "ch"
def left : Name := Name.free "left"
def right : Name := Name.free "right"
def out : Name := Name.free "out"
def freshOne : Name := Name.fresh 1
def hello : Data := Data.atom "hello"
def firstMsg : Data := Data.atom "first"
def secondMsg : Data := Data.atom "second"
def pingBody : Proc := Proc.send out (Data.var 0)
def pingProc : Proc := Proc.par [Proc.send ch hello, Proc.recv ch (Pat.bind 0) pingBody]

example :
    StepClosed
      (fillEvalContext
        (EvalContext.par [Proc.send left firstMsg] [Proc.send right secondMsg])
        pingProc)
      (fillEvalContext
        (EvalContext.par [Proc.send left firstMsg] [Proc.send right secondMsg])
        (substProc [(0, hello)] pingBody)) := by
  apply fillEvalContext_preserves_step
  exact Step.recvComm
    (ch := ch) (msg := hello) (pat := Pat.bind 0)
    (body := pingBody) (s := [(0, hello)]) rfl
    (by simp [checkedSubstProc, pingBody, out, hello, substProc,
              substName, substData, lookup, procWF, dataWF, nameWF])

example :
    StepClosed
      (Proc.par [Proc.recv ch (Pat.bind 0) pingBody, Proc.send ch hello])
      (substProc [(0, hello)] pingBody) := by
  exact StepClosed.core
    (Step.recvCommSwap
      (ch := ch) (msg := hello) (pat := Pat.bind 0)
      (body := pingBody) (s := [(0, hello)]) rfl
      (by simp [checkedSubstProc, pingBody, out, hello, substProc,
                substName, substData, lookup, procWF, dataWF, nameWF]))

theorem nameEq_fresh_not_free (n : Nat) (s : String) :
    nameEq (Name.fresh n) (Name.free s) = false := by
  rfl

theorem nameEq_fresh_self (n : Nat) :
    nameEq (Name.fresh n) (Name.fresh n) = true := by
  simp [nameEq]

theorem substName_fresh_opaque (s : Subst) (n : Nat) :
    substName s (Name.fresh n) = Name.fresh n := by
  rfl

theorem substProc_quote_opaque (s : Subst) (p : Proc) :
    substProc s (Proc.quote p) = Proc.quote p := by
  simp [substProc]

theorem substProc_drop_quote_opaque (s : Subst) (p : Proc) :
    substProc s (Proc.drop (Proc.quote p)) = Proc.drop (Proc.quote p) := by
  simp [substProc]

example : optionProcEq (firstStep pingProc) (some (Proc.send out hello)) = true := by
  native_decide

example :
    optionProcEq (firstStep (Proc.drop (Proc.quote (Proc.send out hello))))
      (some (Proc.send out hello)) = true := rfl

example :
    matchPat (Pat.tuple [Pat.bind 0, Pat.bind 0])
      (Data.tuple [Data.atom "same", Data.atom "different"]) = none := rfl

example :
    substProc [(0, Data.atom "ok")]
      (Proc.quote (Proc.send out (Data.var 0))) =
    Proc.quote (Proc.send out (Data.var 0)) := by
  simp [substProc]

example :
    substProc [(0, Data.atom "ok")]
      (Proc.drop (Proc.quote (Proc.send out (Data.var 0)))) =
    Proc.drop (Proc.quote (Proc.send out (Data.var 0))) := by
  simp [substProc]

example :
    optionProcEq
      (checkedSubstProc [(0, Data.name out)]
        (Proc.send (Name.var 0) hello))
      (some (Proc.send out hello)) = true := by
  native_decide

example :
    optionProcEq
      (checkedSubstProc [(0, Data.atom "not-name")]
        (Proc.send (Name.var 0) hello))
      none = true := by
  native_decide

example :
    optionProcEq
      (joinBodyAfterMessages
        [{ channel := ch, pattern := Pat.bind 0 }]
        [(ch, Data.name out)]
        (Proc.send (Name.var 0) hello))
      (some (Proc.send out hello)) = true := by
  native_decide

example :
    optionProcEq
      (joinBodyAfterMessages
        [{ channel := ch, pattern := Pat.bind 0 }]
        [(ch, Data.atom "not-name")]
        (Proc.send (Name.var 0) hello))
      none = true := by
  native_decide

example :
    procWF [] (Proc.send (Name.var 0) hello) = false := rfl

example :
    procWF [] (Proc.fresh 0 (Proc.send (Name.var 0) hello)) = true := rfl

example :
    procWF [] (Proc.send freshOne hello) = true := rfl

example :
    nameSort [] (Name.free "rho:fresh:1") = NameSort.free := rfl

example :
    nameSort [] freshOne = NameSort.fresh := rfl

example :
    nameEq (Name.free "rho:fresh:1") freshOne = false := rfl

example :
    nameTermSort [] (NameTerm.quotedProc
      (Proc.recv ch (Pat.bind 0) (Proc.send out (Data.var 0)))) =
    NameTermSort.quotedProc := by
  native_decide

example :
    nameTermSort [] (NameTerm.quotedProc
      (Proc.send out (Data.var 0))) =
    NameTermSort.invalid := by
  native_decide

example :
    nameTermIndexable [] (NameTerm.quotedProc
      (Proc.recv ch (Pat.bind 0) (Proc.send out (Data.var 0)))) = false := by
  native_decide

example :
    nameIndexable [] freshOne = true := rfl

example :
    nameIndexable [] (Name.free "ch") = true := rfl

example :
    nameIndexable [] (Name.var 0) = false := rfl

example :
    firstStep
      (Proc.par
        [Proc.send freshOne hello,
         Proc.recv (Name.free "rho:fresh:1") (Pat.bind 0) (Proc.send out (Data.var 0))]) =
    none := rfl

example :
    procWF [] (Proc.drop (Proc.quote (Proc.send out hello))) = true := rfl

example :
    procWF [] (Proc.drop (Proc.send out hello)) = false := rfl

def persistentProc : Proc :=
  Proc.par [Proc.send ch hello, Proc.contract ch (Pat.bind 0) (Proc.send out (Data.var 0))]

example :
    optionProcEq (firstStep persistentProc)
      (some (Proc.par [Proc.contract ch (Pat.bind 0) (Proc.send out (Data.var 0)),
                       Proc.send out hello])) = true := by
  native_decide

def joinProc : Proc :=
  Proc.par
    [Proc.send left (Data.atom "knife"),
     Proc.send right (Data.atom "spoon"),
     Proc.join2 left (Pat.bind 0) right (Pat.bind 1)
       (Proc.send out (Data.tuple [Data.var 0, Data.var 1]))]

example :
    optionProcEq (firstStep joinProc)
      (some (Proc.send out (Data.tuple [Data.atom "knife", Data.atom "spoon"]))) = true := by
  native_decide

def sameChannelJoinProc : Proc :=
  Proc.par
    [Proc.send ch firstMsg,
     Proc.send ch secondMsg,
     Proc.join2 ch (Pat.bind 0) ch (Pat.bind 1)
       (Proc.send out (Data.tuple [Data.var 0, Data.var 1]))]

example :
    optionProcEq (firstStep sameChannelJoinProc)
      (some (Proc.send out (Data.tuple [firstMsg, secondMsg]))) = true := by
  native_decide

def sameChannelJoinClauses : List JoinClause :=
  [{ channel := ch, pattern := Pat.bind 0 },
   { channel := ch, pattern := Pat.bind 1 }]

example :
    joinClausesWF [] sameChannelJoinClauses = true := rfl

example :
    joinBodyCtx sameChannelJoinClauses [] = [0, 1] := by
  simp [joinBodyCtx, sameChannelJoinClauses, joinClausesVars, joinClauseVars, patVars]

example :
    matchJoinMessages sameChannelJoinClauses
      [(ch, firstMsg), (ch, secondMsg)] =
    some [(0, firstMsg), (1, secondMsg)] := by
  rfl

example :
    optionProcEq
      (joinBodyAfterMessages sameChannelJoinClauses
        [(ch, firstMsg), (ch, secondMsg)]
        (Proc.send out (Data.tuple [Data.var 0, Data.var 1])))
      (some (Proc.send out (Data.tuple [firstMsg, secondMsg]))) = true := by
  native_decide

theorem sameChannelJoinBodyAfterMessages :
    joinBodyAfterMessages sameChannelJoinClauses
      [(ch, firstMsg), (ch, secondMsg)]
      (Proc.send out (Data.tuple [Data.var 0, Data.var 1])) =
    some (Proc.send out (Data.tuple [firstMsg, secondMsg])) := by
  simp [joinBodyAfterMessages, sameChannelJoinClauses, matchJoinMessages,
    matchPat,
    checkedSubstProc, substProc, substData, substName, lookup, mergeSubst,
    extendConsistent, nameEq, procWF, dataWF, nameWF,
    dataListWF, ch, out, firstMsg, secondMsg]

def sameChannelArbitraryJoinProc : Proc :=
  Proc.par
    ([Proc.send ch firstMsg, Proc.send ch secondMsg] ++
      [Proc.join sameChannelJoinClauses
        (Proc.send out (Data.tuple [Data.var 0, Data.var 1]))])

example :
    Step sameChannelArbitraryJoinProc
      (Proc.send out (Data.tuple [firstMsg, secondMsg])) := by
  simpa [sameChannelArbitraryJoinProc] using
    (Step.joinComm
      (clauses := sameChannelJoinClauses)
      (messages := [(ch, firstMsg), (ch, secondMsg)])
      (body := Proc.send out (Data.tuple [Data.var 0, Data.var 1]))
      sameChannelJoinBodyAfterMessages)

def sameChannelArbitraryPJoinProc : Proc :=
  Proc.par
    ([Proc.send ch firstMsg, Proc.send ch secondMsg] ++
      [Proc.pjoin sameChannelJoinClauses
        (Proc.send out (Data.tuple [Data.var 0, Data.var 1]))])

example :
    Step sameChannelArbitraryPJoinProc
      (Proc.par
        [Proc.pjoin sameChannelJoinClauses
          (Proc.send out (Data.tuple [Data.var 0, Data.var 1])),
         Proc.send out (Data.tuple [firstMsg, secondMsg])]) := by
  simpa [sameChannelArbitraryPJoinProc] using
    (Step.pjoinComm
      (clauses := sameChannelJoinClauses)
      (messages := [(ch, firstMsg), (ch, secondMsg)])
      (body := Proc.send out (Data.tuple [Data.var 0, Data.var 1]))
      sameChannelJoinBodyAfterMessages)

example :
    procWF [] sameChannelArbitraryJoinProc = true := by
  native_decide

example :
    procWF [] sameChannelArbitraryPJoinProc = true := by
  native_decide

example :
    procWF [] (Proc.send out (Data.tuple [firstMsg, secondMsg])) = true := by
  native_decide

example :
    procWF []
      (Proc.par
        [Proc.pjoin sameChannelJoinClauses
          (Proc.send out (Data.tuple [Data.var 0, Data.var 1])),
         Proc.send out (Data.tuple [firstMsg, secondMsg])]) = true := by
  apply Step_preserves_wf
  · exact Step.pjoinComm
      (clauses := sameChannelJoinClauses)
      (messages := [(ch, firstMsg), (ch, secondMsg)])
      (body := Proc.send out (Data.tuple [Data.var 0, Data.var 1]))
      (result := Proc.send out (Data.tuple [firstMsg, secondMsg]))
      sameChannelJoinBodyAfterMessages
  · native_decide

def sameChannelComponents : List Proc :=
  [Proc.send ch firstMsg, Proc.send ch secondMsg, Proc.send out hello]

example :
    sendCandidates (removeIndexedSends [ch, ch] sameChannelComponents) =
    [(out, hello)] := rfl

example :
    sendCandidates
      (removeMatchedMessages [(ch, firstMsg), (ch, secondMsg)]
        sameChannelComponents) =
    [(out, hello)] := rfl

def duplicateSamePayloadComponents : List Proc :=
  [Proc.send ch hello, Proc.send ch hello, Proc.send out firstMsg]

example :
    sendCandidates
      (removeMatchedMessages [(ch, hello), (ch, hello)]
        duplicateSamePayloadComponents) =
    [(out, firstMsg)] := rfl

def twoJoinClauses : List JoinClause :=
  [{ channel := left, pattern := Pat.bind 0 },
   { channel := right, pattern := Pat.bind 1 }]

example :
    joinClausesWF [] twoJoinClauses = true := rfl

example :
    joinBodyCtx twoJoinClauses [] = [0, 1] := by
  simp [joinBodyCtx, twoJoinClauses, joinClausesVars, joinClauseVars, patVars]

example :
    matchJoinMessages twoJoinClauses
      [(left, Data.atom "knife"), (right, Data.atom "spoon")] =
    some [(0, Data.atom "knife"), (1, Data.atom "spoon")] := by
  rfl

example :
    matchJoinMessages
      [{ channel := left, pattern := Pat.bind 0 },
       { channel := right, pattern := Pat.bind 0 }]
      [(left, Data.atom "knife"), (right, Data.atom "spoon")] = none := by
  rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Basic
