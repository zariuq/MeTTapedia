import Mathlib.Logic.Relation
import MeTTaIL.Semantics.Eval
import Mettapedia.GSLT.LanguageDef.LFEngineUniversal
import Mettapedia.GSLT.LanguageDef.LFEngineShiftSim

/-!
# SelfMeTTa 03: soundness of the SelfMeTTa 02 witness checker

This is the Lean twin of `MettaKernel/Curriculum/SelfMeTTa/02_minimal_metta_languagedef.metta`.
It models the 02 guest data and checker clause-for-clause, encodes each guest rule as a premise-free
MeTTaIL rewrite, and proves that an accepted witness step is a genuine member of the certified
MeTTaIL base-rewrite semantics.

Scope: the same v1 root-rewrite fragment as 02: first-order `MSym`/`MApp`/`MVar` terms, finite rule
tables, recorded substitutions, deterministic witness traces, and root normality (`baseReducts = []`).
This does not claim contextual `oneStep` normality; 02's normal-form checker also asks only whether a
listed rule applies at the current root.  The Lean-twin correspondence to the `.metta` file is
by-construction plus the existing CeTTa/PeTTa/LeaTTa differential gate; mechanical extraction is future
work.

Integrity: no placeholder proof terms, no VM-backed proof-by-evaluation, and no wanted-theorem stubs.
-/

namespace Mettapedia.GSLT.SelfMeTTa.MinimalMeTTaWitness

open MeTTaIL

/-! ## Guest data and the 02 checker -/

inductive GName where
  | symZ
  | symS
  | symAdd
  | symNil
  | symSnoc
  | symCons
  | symAppend
  | symCalChain
  | symChain0
  | symChain1
  | symChain2
  | symChain3
  | symChain4
  | symChain5
  | symStuck
  | symA
  | symB
  | symC
  | varX
  | varY
  | varXS
  | varYS
  | ruleAddZ
  | ruleAddS
  | ruleAppendNil
  | ruleAppendSnoc
  | ruleChain0
  | ruleChain1
  | ruleChain2
  | ruleChain3
  | ruleChain4
deriving Repr, DecidableEq, BEq

def GName.text : GName → String
  | .symZ => "Z"
  | .symS => "S"
  | .symAdd => "Add"
  | .symNil => "Nil"
  | .symSnoc => "Snoc"
  | .symCons => "Cons"
  | .symAppend => "Append"
  | .symCalChain => "CalChain"
  | .symChain0 => "Chain0"
  | .symChain1 => "Chain1"
  | .symChain2 => "Chain2"
  | .symChain3 => "Chain3"
  | .symChain4 => "Chain4"
  | .symChain5 => "Chain5"
  | .symStuck => "Stuck"
  | .symA => "A"
  | .symB => "B"
  | .symC => "C"
  | .varX => "x"
  | .varY => "y"
  | .varXS => "xs"
  | .varYS => "ys"
  | .ruleAddZ => "add_z"
  | .ruleAddS => "add_s"
  | .ruleAppendNil => "append_nil"
  | .ruleAppendSnoc => "append_snoc"
  | .ruleChain0 => "chain_0"
  | .ruleChain1 => "chain_1"
  | .ruleChain2 => "chain_2"
  | .ruleChain3 => "chain_3"
  | .ruleChain4 => "chain_4"

theorem GName.text_injective {a b : GName} (h : a.text = b.text) : a = b := by
  cases a <;> cases b <;> first | rfl | contradiction

theorem GName.text_beq_eq (a b : GName) : (a.text == b.text) = (a == b) := by
  cases a <;> cases b <;> rfl

theorem GName.text_beq_self (a : GName) : (a.text == a.text) = true := by
  cases a <;> rfl

theorem GName.beq_self (a : GName) : (a == a) = true := by
  cases a <;> rfl

theorem GName.beq_false_of_ne {a b : GName} (h : a ≠ b) : (a == b) = false := by
  cases a <;> cases b <;> first | contradiction | rfl

theorem GName.text_beq_MApp_false (a : GName) : (a.text == "MApp") = false := by
  cases a <;> rfl

theorem GName.MApp_beq_text_false (a : GName) : ("MApp" == a.text) = false := by
  cases a <;> rfl

theorem label_id_text_beq_self (a : GName) :
    (Label.id a.text == Label.id a.text) = true := by
  change (a.text == a.text) = true
  exact GName.text_beq_self a

theorem label_id_text_beq_false_of_ne {a b : GName} (h : a ≠ b) :
    (Label.id a.text == Label.id b.text) = false := by
  change (a.text == b.text) = false
  rw [GName.text_beq_eq, GName.beq_false_of_ne h]

theorem label_id_text_MApp_false (a : GName) :
    (Label.id a.text == Label.id "MApp") = false := by
  change (a.text == "MApp") = false
  exact GName.text_beq_MApp_false a

theorem label_id_MApp_text_false (a : GName) :
    (Label.id "MApp" == Label.id a.text) = false := by
  change ("MApp" == a.text) = false
  exact GName.MApp_beq_text_false a

inductive GTerm where
  | sym : GName → GTerm
  | app : GTerm → GTerm → GTerm
  | var : GName → GTerm
deriving Repr, DecidableEq

structure GuestRule where
  name : GName
  lhs : GTerm
  rhs : GTerm
deriving Repr, DecidableEq

abbrev Sigma := List (GName × GTerm)

structure EvalStep where
  expr : GTerm
  sigma : Sigma
  ruleName : GName
  expr' : GTerm
deriving Repr, DecidableEq

inductive Trace where
  | nil
  | cons : EvalStep → Trace → Trace
deriving Repr, DecidableEq

inductive CheckError where
  | noRule
  | nonMatchingLhs
  | wrongSigma
  | unboundRhsVar
  | wrongRhs
  | skippedStep
  | finalNotNormal
  | fuelExhausted
deriving Repr, DecidableEq

inductive CheckResult where
  | ok : GTerm → CheckResult
  | err : CheckError → CheckResult
deriving Repr, DecidableEq

def lookupRule (name : GName) : List GuestRule → Option GuestRule
  | [] => none
  | r :: rs => if r.name = name then some r else lookupRule name rs

def lookupSigma (name : GName) (sigma : Sigma) : Option GTerm :=
  (sigma.find? (fun b => b.1 == name)).map Prod.snd

def bindSigma (name : GName) (term : GTerm) (sigma : Sigma) : Option Sigma :=
  match sigma.find? (fun b => b.1 == name) with
  | none => some ((name, term) :: sigma)
  | some (_, old) => if old = term then some sigma else none

def matchTerm (pat term : GTerm) (sigma : Sigma) : Option Sigma :=
  match pat with
  | .var name => bindSigma name term sigma
  | .sym lhs =>
      match term with
      | .sym rhs => if lhs = rhs then some sigma else none
      | _ => none
  | .app pf pa =>
      match term with
      | .app tf ta =>
          match matchTerm pf tf sigma with
          | some sigma1 => matchTerm pa ta sigma1
          | none => none
      | _ => none

def instTerm (term : GTerm) (sigma : Sigma) : Option GTerm :=
  match term with
  | .sym name => some (.sym name)
  | .var name => lookupSigma name sigma
  | .app f a =>
      match instTerm f sigma, instTerm a sigma with
      | some f', some a' => some (.app f' a')
      | _, _ => none

def ruleApplies (term : GTerm) (rule : GuestRule) : Bool :=
  (matchTerm rule.lhs term []).isSome

def hasRedex : List GuestRule → GTerm → Bool
  | [], _ => false
  | r :: rs, term => if ruleApplies term r then true else hasRedex rs term

def checkNormal (rules : List GuestRule) (term : GTerm) : Bool :=
  !(hasRedex rules term)

def checkStep (rules : List GuestRule) (step : EvalStep) : CheckResult :=
  match lookupRule step.ruleName rules with
  | none => .err .noRule
  | some r =>
      match matchTerm r.lhs step.expr [] with
      | none => .err .nonMatchingLhs
      | some actualSigma =>
          if actualSigma = step.sigma then
            match instTerm r.rhs step.sigma with
            | none => .err .unboundRhsVar
            | some rhs =>
                if step.expr' = rhs then .ok step.expr' else .err .wrongRhs
          else
            .err .wrongSigma

def traceFits : Nat → Trace → Bool
  | _, .nil => true
  | 0, .cons _ _ => false
  | fuel + 1, .cons _ rest => traceFits fuel rest

def checkTrace (rules : List GuestRule) (current : GTerm) (trace : Trace)
    (final : GTerm) : CheckResult :=
  match trace with
  | .nil =>
      if current = final then
        if checkNormal rules final then .ok final else .err .finalNotNormal
      else
        .err .skippedStep
  | .cons step rest =>
      if current = step.expr then
        match checkStep rules step with
        | .ok next => checkTrace rules next rest final
        | .err e => .err e
      else
        .err .skippedStep

def checkNormalize (rules : List GuestRule) (start : GTerm) (fuel : Nat)
    (trace : Trace) (final : GTerm) : CheckResult :=
  if traceFits fuel trace then checkTrace rules start trace final else .err .fuelExhausted

/-! ## Encoding into certified MeTTaIL rewrites -/

def enc : GTerm → AST
  | .sym s => .sexp (.id s.text) []
  | .app f a => .sexp (.id "MApp") [enc f, enc a]
  | .var x => .var (.base x.text)

def encSigma (sigma : Sigma) : List (String × AST) :=
  sigma.map (fun b => (b.1.text, enc b.2))

def encRule (rule : GuestRule) : RewriteDecl :=
  { name := rule.name.text, rw := .base (enc rule.lhs) (enc rule.rhs) }

def encPresentation (rules : List GuestRule) : Presentation :=
  .mk [] [] [] (rules.map encRule) []

def BaseNormal (p : Presentation) (term : AST) : Prop :=
  baseReducts p term = []

/-! ## Encoding and matcher alignment -/

theorem enc_injective : ∀ {a b : GTerm}, enc a = enc b → a = b := by
  intro a
  induction a with
  | sym s =>
      intro b h
      cases b with
      | sym t =>
          simp only [enc] at h
          injection h with hlabel hargs
          injection hlabel with hs
          exact congrArg GTerm.sym (GName.text_injective hs)
      | app f x =>
          simp only [enc] at h
          injection h with hlabel hargs
          cases hargs
      | var x =>
          simp only [enc] at h
          injection h
  | app af aa ihf iha =>
      intro b h
      cases b with
      | sym t =>
          simp only [enc] at h
          injection h with hlabel hargs
          cases hargs
      | app bf ba =>
          simp only [enc] at h
          injection h with hlabel hargs
          injection hargs with hf htail
          injection htail with ha hnil
          exact congrArg₂ GTerm.app (ihf hf) (iha ha)
      | var x =>
          simp only [enc] at h
          injection h
  | var x =>
      intro b h
      cases b with
      | sym t =>
          simp only [enc] at h
          injection h
      | app f a =>
          simp only [enc] at h
          injection h
      | var y =>
          simp only [enc] at h
          injection h with hp
          injection hp with hy
          exact congrArg GTerm.var (GName.text_injective hy)

theorem enc_beq_self : ∀ term : GTerm, (enc term == enc term) = true := by
  intro term
  induction term with
  | sym s =>
      change ((s.text == s.text) && true) = true
      rw [GName.text_beq_self]
      rfl
  | app f a ihf iha =>
      change (("MApp" == "MApp") && ((enc f == enc f) && ((enc a == enc a) && true))) =
        true
      rw [ihf, iha]
      rfl
  | var x =>
      change (x.text == x.text) = true
      exact GName.text_beq_self x

theorem enc_beq_false_of_ne : ∀ {a b : GTerm}, a ≠ b → (enc a == enc b) = false := by
  intro a
  induction a with
  | sym s =>
      intro b hne
      cases b with
      | sym t =>
          have hst : s ≠ t := by
            intro h
            exact hne (congrArg GTerm.sym h)
          change ((s.text == t.text) && true) = false
          rw [GName.text_beq_eq, GName.beq_false_of_ne hst]
          rfl
      | app f x =>
          change ((s.text == "MApp") && AST.beqList [] [enc f, enc x]) = false
          rw [GName.text_beq_MApp_false s]
          rfl
      | var x =>
          rfl
  | app af aa ihf iha =>
      intro b hne
      cases b with
      | sym t =>
          change (("MApp" == t.text) && AST.beqList [enc af, enc aa] []) = false
          rw [GName.MApp_beq_text_false t]
          rfl
      | app bf ba =>
          by_cases hf : af = bf
          · have ha : aa ≠ ba := by
              intro ha
              exact hne (congrArg₂ GTerm.app hf ha)
            subst bf
            change (("MApp" == "MApp") &&
                ((enc af == enc af) && ((enc aa == enc ba) && true))) = false
            rw [enc_beq_self af, iha ha]
            rfl
          · have hfirst := ihf hf
            change (("MApp" == "MApp") &&
                ((enc af == enc bf) && ((enc aa == enc ba) && true))) = false
            rw [hfirst]
            rfl
      | var x =>
          rfl
  | var x =>
      intro b hne
      cases b with
      | sym t =>
          rfl
      | app f a =>
          rfl
      | var y =>
          have hxy : x ≠ y := by
            intro h
            exact hne (congrArg GTerm.var h)
          change (x.text == y.text) = false
          rw [GName.text_beq_eq, GName.beq_false_of_ne hxy]

theorem findEncSigma (name : GName) :
    ∀ sigma : Sigma,
      (encSigma sigma).find? (fun b => b.1 == name.text) =
        (sigma.find? (fun b => b.1 == name)).map (fun b => (b.1.text, enc b.2))
  := by
  intro sigma
  induction sigma with
  | nil => rfl
  | cons b rest ih =>
      rcases b with ⟨x, t⟩
      by_cases h : x = name
      · subst x
        simp only [encSigma, List.map_cons, List.find?, GName.text_beq_self,
          GName.beq_self, Option.map]
      · have htext : (x.text == name.text) = false := by
          rw [GName.text_beq_eq]
          exact GName.beq_false_of_ne h
        have hname : (x == name) = false := GName.beq_false_of_ne h
        simp only [encSigma, List.map_cons, List.find?, htext, hname, Option.map] at ih ⊢
        exact ih

theorem bindSigma_matchPat (name : GName) (term : GTerm) (sigma : Sigma) :
    AST.matchPat (.var (.base name.text)) (enc term) (encSigma sigma) =
      (bindSigma name term sigma).map encSigma := by
  unfold bindSigma
  simp only [AST.matchPat, findEncSigma]
  cases hfind : sigma.find? (fun b => b.1 == name) with
  | none =>
      simp [encSigma]
  | some b =>
      rcases b with ⟨foundName, old⟩
      by_cases hold : old = term
      · subst old
        simp [encSigma, enc_beq_self]
      · have hbeq : (enc old == enc term) = false :=
          enc_beq_false_of_ne hold
        simp [hold, hbeq]

theorem matchTerm_matchPat :
    ∀ (pat term : GTerm) (sigma : Sigma),
      AST.matchPat (enc pat) (enc term) (encSigma sigma) =
        (matchTerm pat term sigma).map encSigma := by
  intro pat
  induction pat with
  | sym lhs =>
      intro term sigma
      cases term with
      | sym rhs =>
          by_cases h : lhs = rhs
          · subst lhs
            change (if (Label.id rhs.text == Label.id rhs.text) = true then
                AST.matchPatList [] [] (encSigma sigma) else none) =
              Option.map encSigma (if rhs = rhs then some sigma else none)
            rw [label_id_text_beq_self rhs]
            change some (encSigma sigma) = Option.map encSigma
              (if rhs = rhs then some sigma else none)
            rw [if_pos rfl]
            rfl
          · have hlabel := label_id_text_beq_false_of_ne h
            change (if (Label.id lhs.text == Label.id rhs.text) = true then
                AST.matchPatList [] [] (encSigma sigma) else none) =
              Option.map encSigma (if lhs = rhs then some sigma else none)
            rw [hlabel, if_neg h]
            rfl
      | app f a =>
          have hlabel := label_id_text_MApp_false lhs
          change (if (Label.id lhs.text == Label.id "MApp") = true then
              AST.matchPatList [] [enc f, enc a] (encSigma sigma) else none) = none
          rw [hlabel]
          rfl
      | var x =>
          have hbeq :
              (AST.sexp (Label.id lhs.text) [] == AST.var (DottedPath.base x.text)) = false := by
            rfl
          change (if (AST.sexp (Label.id lhs.text) [] ==
              AST.var (DottedPath.base x.text)) = true then some (encSigma sigma) else none) = none
          rw [hbeq]
          rfl
  | app pf pa ihf iha =>
      intro term sigma
      cases term with
      | sym rhs =>
          have hlabel := label_id_MApp_text_false rhs
          change (if (Label.id "MApp" == Label.id rhs.text) = true then
              AST.matchPatList [enc pf, enc pa] [] (encSigma sigma) else none) = none
          rw [hlabel]
          rfl
      | app tf ta =>
          change (if (Label.id "MApp" == Label.id "MApp") = true then
              AST.matchPatList [enc pf, enc pa] [enc tf, enc ta] (encSigma sigma) else none) =
            Option.map encSigma
              (match matchTerm pf tf sigma with
              | some sigma1 => matchTerm pa ta sigma1
              | none => none)
          rw [show (Label.id "MApp" == Label.id "MApp") = true by rfl]
          change ((enc pf).matchPat (enc tf) (encSigma sigma)).bind
              (fun bnds => AST.matchPatList [enc pa] [enc ta] bnds) =
            Option.map encSigma
              (match matchTerm pf tf sigma with
              | some sigma1 => matchTerm pa ta sigma1
              | none => none)
          rw [ihf tf sigma]
          cases hmf : matchTerm pf tf sigma with
          | none => rfl
          | some sigma1 =>
              change AST.matchPatList [enc pa] [enc ta] (encSigma sigma1) =
                Option.map encSigma (matchTerm pa ta sigma1)
              change ((enc pa).matchPat (enc ta) (encSigma sigma1)).bind
                  (fun bnds => AST.matchPatList [] [] bnds) =
                Option.map encSigma (matchTerm pa ta sigma1)
              rw [iha ta sigma1]
              cases matchTerm pa ta sigma1 <;> rfl
      | var x =>
          have hbeq :
              (AST.sexp (Label.id "MApp") [enc pf, enc pa] ==
                AST.var (DottedPath.base x.text)) = false := by
            rfl
          change (if (AST.sexp (Label.id "MApp") [enc pf, enc pa] ==
              AST.var (DottedPath.base x.text)) = true then some (encSigma sigma) else none) = none
          rw [hbeq]
          rfl
  | var name =>
      intro term sigma
      change AST.matchPat (.var (.base name.text)) (enc term) (encSigma sigma) =
        Option.map encSigma (bindSigma name term sigma)
      exact bindSigma_matchPat name term sigma

theorem lookupSigma_inst (name : GName) (sigma : Sigma) (term : GTerm)
    (h : lookupSigma name sigma = some term) :
    AST.inst (encSigma sigma) (.var (.base name.text)) = enc term := by
  unfold lookupSigma at h
  cases hfind : sigma.find? (fun b => b.1 == name) with
  | none =>
      simp [hfind] at h
  | some b =>
      rcases b with ⟨foundName, old⟩
      have hold : old = term := by
        simpa [hfind] using h
      subst term
      simp [AST.inst, findEncSigma, hfind]

theorem instTerm_inst :
    ∀ {term : GTerm} {sigma : Sigma} {out : GTerm},
      instTerm term sigma = some out → AST.inst (encSigma sigma) (enc term) = enc out := by
  intro term
  induction term with
  | sym s =>
      intro sigma out h
      simp [instTerm] at h
      subst h
      rfl
  | var name =>
      intro sigma out h
      exact lookupSigma_inst name sigma out h
  | app f a ihf iha =>
      intro sigma out h
      simp only [instTerm] at h
      cases hf : instTerm f sigma with
      | none => simp [hf] at h
      | some f' =>
          cases ha : instTerm a sigma with
          | none => simp [hf, ha] at h
          | some a' =>
              simp [hf, ha] at h
              subst h
              simp [enc, AST.inst, AST.instList, ihf hf, iha ha]

/-! ## S1: accepted steps are genuine base rewrites -/

theorem lookupRule_mem {name : GName} {rules : List GuestRule} {rule : GuestRule}
    (h : lookupRule name rules = some rule) : rule ∈ rules := by
  induction rules with
  | nil => simp [lookupRule] at h
  | cons r rs ih =>
      unfold lookupRule at h
      by_cases hr : r.name = name
      · simp [hr] at h
        cases h
        exact List.mem_cons_self
      · simp [hr] at h
        exact List.mem_cons_of_mem _ (ih h)

theorem applyBaseRewrite_encRule {rule : GuestRule} {term : GTerm} {sigma : Sigma}
    {out : GTerm}
    (hm : matchTerm rule.lhs term [] = some sigma)
    (hi : instTerm rule.rhs sigma = some out) :
    applyBaseRewrite (encRule rule) (enc term) = some (enc out) := by
  simp only [applyBaseRewrite, encRule]
  have hmatch := matchTerm_matchPat rule.lhs term []
  simp [encSigma] at hmatch
  rw [hmatch]
  simp [hm, instTerm_inst hi]

theorem mem_baseReducts_of_checked_parts {rules : List GuestRule} {rule : GuestRule}
    {term out : GTerm} {sigma : Sigma}
    (hmem : rule ∈ rules)
    (hm : matchTerm rule.lhs term [] = some sigma)
    (hi : instTerm rule.rhs sigma = some out) :
    enc out ∈ baseReducts (encPresentation rules) (enc term) := by
  simp only [baseReducts, encPresentation, Presentation.rewrites, List.mem_filterMap]
  exact ⟨encRule rule, List.mem_map.mpr ⟨rule, hmem, rfl⟩, applyBaseRewrite_encRule hm hi⟩

theorem reduces_of_checked_parts {rules : List GuestRule} {rule : GuestRule}
    {term out : GTerm} {sigma : Sigma}
    (hmem : rule ∈ rules)
    (hm : matchTerm rule.lhs term [] = some sigma)
    (hi : instTerm rule.rhs sigma = some out) :
    Reduces (encPresentation rules) (enc term) (enc out) := by
  have hmem' : encRule rule ∈ (encPresentation rules).rewrites := by
    simp only [encPresentation, Presentation.rewrites]
    exact List.mem_map.mpr ⟨rule, hmem, rfl⟩
  have hmatch0 := matchTerm_matchPat rule.lhs term []
  simp [encSigma, hm] at hmatch0
  have hmatch :
      AST.matchPat (encRule rule).rw.conclusion.1 (enc term) [] = some (encSigma sigma) := by
    simpa [encRule, Rewrite.conclusion, encSigma] using hmatch0
  have hprem :
      PremisesHold (encPresentation rules) (encRule rule).rw.premises
        (encSigma sigma) (encSigma sigma) := by
    simpa [encRule, Rewrite.premises] using
      (PremisesHold.nil (p := encPresentation rules) (bnds := encSigma sigma))
  have hinst :
      enc out = AST.inst (encSigma sigma) (encRule rule).rw.conclusion.2 := by
    simpa [encRule, Rewrite.conclusion] using Eq.symm (instTerm_inst hi)
  exact Reduces.step (encRule rule) (encSigma sigma) (encSigma sigma)
    hmem' hmatch hprem hinst

theorem S1_step_sound {rules : List GuestRule} {step : EvalStep}
    (h : checkStep rules step = .ok step.expr') :
    enc step.expr' ∈ baseReducts (encPresentation rules) (enc step.expr) ∧
      Reduces (encPresentation rules) (enc step.expr) (enc step.expr') := by
  unfold checkStep at h
  cases hlookup : lookupRule step.ruleName rules with
  | none => simp [hlookup] at h
  | some rule =>
      cases hm : matchTerm rule.lhs step.expr [] with
      | none => simp [hlookup, hm] at h
      | some actualSigma =>
          by_cases hsigma : actualSigma = step.sigma
          · cases hi : instTerm rule.rhs step.sigma with
            | none => simp [hlookup, hm, hsigma, hi] at h
            | some rhs =>
                by_cases hrhs : step.expr' = rhs
                ·
                  simp [hlookup, hm, hsigma, hi] at h
                  have hmem : rule ∈ rules := lookupRule_mem hlookup
                  have hbase : enc step.expr' ∈
                      baseReducts (encPresentation rules) (enc step.expr) := by
                    rw [hrhs]
                    exact mem_baseReducts_of_checked_parts hmem (by simpa [hsigma] using hm) hi
                  have hred : Reduces (encPresentation rules) (enc step.expr) (enc step.expr') := by
                    rw [hrhs]
                    exact reduces_of_checked_parts hmem (by simpa [hsigma] using hm) hi
                  exact ⟨hbase, hred⟩
                · simp [hlookup, hm, hsigma, hi, hrhs] at h
          · simp [hlookup, hm, hsigma] at h

/-! ## S2: the checker's root-normality verdict means no base rule applies -/

theorem applyBaseRewrite_encRule_none_of_no_match (rule : GuestRule) (term : GTerm)
    (h : matchTerm rule.lhs term [] = none) :
    applyBaseRewrite (encRule rule) (enc term) = none := by
  simp only [applyBaseRewrite, encRule]
  have hmatch := matchTerm_matchPat rule.lhs term []
  simp [encSigma] at hmatch
  rw [hmatch]
  simp [h]

theorem S2_normality {rules : List GuestRule} {term : GTerm}
    (h : checkNormal rules term = true) :
    BaseNormal (encPresentation rules) (enc term) := by
  unfold checkNormal at h
  induction rules with
  | nil =>
      rfl
  | cons r rs ih =>
      unfold hasRedex at h
      cases hm : matchTerm r.lhs term [] with
      | some sigma =>
          simp [ruleApplies, hm] at h
      | none =>
          simp [ruleApplies, hm] at h
          have hrs : checkNormal rs term = true := by
            unfold checkNormal
            simpa using h
          have ih' := ih hrs
          unfold BaseNormal at ih' ⊢
          have hnone := applyBaseRewrite_encRule_none_of_no_match r term hm
          simp only [encPresentation, Presentation.rewrites, baseReducts] at ih' ⊢
          simp [hnone, ih']

/-! ## S3: accepted traces are finite certified rewrite derivations -/

def EncReduces (rules : List GuestRule) : AST → AST → Prop :=
  Reduces (encPresentation rules)

theorem checkStep_ok_eq_expr' {rules : List GuestRule} {step : EvalStep} {out : GTerm}
    (h : checkStep rules step = .ok out) :
    out = step.expr' := by
  unfold checkStep at h
  cases hlookup : lookupRule step.ruleName rules with
  | none => simp [hlookup] at h
  | some rule =>
      cases hm : matchTerm rule.lhs step.expr [] with
      | none => simp [hlookup, hm] at h
      | some actualSigma =>
          by_cases hsigma : actualSigma = step.sigma
          · cases hi : instTerm rule.rhs step.sigma with
            | none => simp [hlookup, hm, hsigma, hi] at h
            | some rhs =>
                by_cases hrhs : step.expr' = rhs
                · simp [hlookup, hm, hsigma, hi, hrhs] at h
                  cases h
                  exact Eq.symm hrhs
                · simp [hlookup, hm, hsigma, hi, hrhs] at h
          · simp [hlookup, hm, hsigma] at h

theorem S3_trace_sound {rules : List GuestRule} {current final : GTerm} {trace : Trace}
    (h : checkTrace rules current trace final = .ok final) :
    Relation.ReflTransGen (EncReduces rules) (enc current) (enc final) ∧
      BaseNormal (encPresentation rules) (enc final) := by
  induction trace generalizing current with
  | nil =>
      unfold checkTrace at h
      by_cases hcf : current = final
      · subst current
        by_cases hn : checkNormal rules final = true
        · simp [hn] at h
          exact ⟨Relation.ReflTransGen.refl, S2_normality hn⟩
        · simp [hn] at h
      · simp [hcf] at h
  | cons step rest ih =>
      unfold checkTrace at h
      by_cases hc : current = step.expr
      · subst current
        cases hs : checkStep rules step with
        | err e => simp [hs] at h
        | ok next =>
            have hnext : next = step.expr' := checkStep_ok_eq_expr' hs
            subst next
            have hs1 := S1_step_sound (rules := rules) (step := step) hs
            simp [hs] at h
            obtain ⟨hrest, hnorm⟩ := ih h
            exact ⟨Relation.ReflTransGen.head hs1.2 hrest, hnorm⟩
      · simp [hc] at h

theorem S3_normalize_sound {rules : List GuestRule} {start final : GTerm} {fuel : Nat}
    {trace : Trace}
    (h : checkNormalize rules start fuel trace final = .ok final) :
    Relation.ReflTransGen (EncReduces rules) (enc start) (enc final) ∧
      BaseNormal (encPresentation rules) (enc final) := by
  unfold checkNormalize at h
  cases hf : traceFits fuel trace with
  | false =>
      simp [hf] at h
  | true =>
      simp [hf] at h
      exact S3_trace_sound h

/-! ## S4: the 02 calibration corpus as kernel-checked instances -/

def mz : GTerm := .sym .symZ
def ms (n : GTerm) : GTerm := .app (.sym .symS) n
def madd (x y : GTerm) : GTerm := .app (.app (.sym .symAdd) x) y

def mnil : GTerm := .sym .symNil
def msnoc (xs x : GTerm) : GTerm := .app (.app (.sym .symSnoc) xs) x
def mcons (x xs : GTerm) : GTerm := .app (.app (.sym .symCons) x) xs
def mappend (xs ys : GTerm) : GTerm := .app (.app (.sym .symAppend) xs) ys

def mchainCall (state : GTerm) : GTerm := .app (.sym .symCalChain) state
def mchain0 : GTerm := mchainCall (.sym .symChain0)
def mchain1 : GTerm := mchainCall (.sym .symChain1)
def mchain2 : GTerm := mchainCall (.sym .symChain2)
def mchain3 : GTerm := mchainCall (.sym .symChain3)
def mchain4 : GTerm := mchainCall (.sym .symChain4)
def mchain5 : GTerm := .sym .symChain5

def mstuck : GTerm := .app (.sym .symStuck) (.sym .symA)

def sig1 (x : GName) (tx : GTerm) : Sigma := [(x, tx)]
def sig2 (x : GName) (tx : GTerm) (y : GName) (ty : GTerm) : Sigma := [(y, ty), (x, tx)]
def sig3 (x : GName) (tx : GTerm) (y : GName) (ty : GTerm) (z : GName) (tz : GTerm) :
    Sigma := [(z, tz), (y, ty), (x, tx)]

def addRules : List GuestRule :=
  [ { name := .ruleAddZ, lhs := madd (.var .varX) mz, rhs := .var .varX },
    { name := .ruleAddS, lhs := madd (.var .varX) (ms (.var .varY)),
      rhs := madd (ms (.var .varX)) (.var .varY) } ]

def appendRules : List GuestRule :=
  [ { name := .ruleAppendNil, lhs := mappend mnil (.var .varYS), rhs := .var .varYS },
    { name := .ruleAppendSnoc, lhs := mappend (msnoc (.var .varXS) (.var .varX)) (.var .varYS),
      rhs := mappend (.var .varXS) (mcons (.var .varX) (.var .varYS)) } ]

def chainRules : List GuestRule :=
  [ { name := .ruleChain0, lhs := mchain0, rhs := mchain1 },
    { name := .ruleChain1, lhs := mchain1, rhs := mchain2 },
    { name := .ruleChain2, lhs := mchain2, rhs := mchain3 },
    { name := .ruleChain3, lhs := mchain3, rhs := mchain4 },
    { name := .ruleChain4, lhs := mchain4, rhs := mchain5 } ]

def stuckRules : List GuestRule := []

def addStart : GTerm := madd mz (ms (ms mz))
def addMid1 : GTerm := madd (ms mz) (ms mz)
def addMid2 : GTerm := madd (ms (ms mz)) mz
def addFinal : GTerm := ms (ms mz)
def addTrace : Trace :=
  .cons { expr := addStart, sigma := sig2 .varX mz .varY (ms mz), ruleName := .ruleAddS,
          expr' := addMid1 }
  (.cons { expr := addMid1, sigma := sig2 .varX (ms mz) .varY mz, ruleName := .ruleAddS,
           expr' := addMid2 }
  (.cons { expr := addMid2, sigma := sig1 .varX (ms (ms mz)), ruleName := .ruleAddZ,
           expr' := addFinal }
   .nil))

def appendStart : GTerm :=
  mappend (msnoc (msnoc mnil (.sym .symA)) (.sym .symB)) (mcons (.sym .symC) mnil)
def appendMid1 : GTerm :=
  mappend (msnoc mnil (.sym .symA)) (mcons (.sym .symB) (mcons (.sym .symC) mnil))
def appendMid2 : GTerm :=
  mappend mnil (mcons (.sym .symA) (mcons (.sym .symB) (mcons (.sym .symC) mnil)))
def appendFinal : GTerm := mcons (.sym .symA) (mcons (.sym .symB) (mcons (.sym .symC) mnil))
def appendTrace : Trace :=
  .cons { expr := appendStart,
          sigma := sig3 .varXS (msnoc mnil (.sym .symA)) .varX (.sym .symB) .varYS
            (mcons (.sym .symC) mnil),
          ruleName := .ruleAppendSnoc, expr' := appendMid1 }
  (.cons { expr := appendMid1,
           sigma := sig3 .varXS mnil .varX (.sym .symA) .varYS
             (mcons (.sym .symB) (mcons (.sym .symC) mnil)),
           ruleName := .ruleAppendSnoc, expr' := appendMid2 }
  (.cons { expr := appendMid2, sigma := sig1 .varYS appendFinal,
           ruleName := .ruleAppendNil, expr' := appendFinal }
   .nil))

def chainTrace : Trace :=
  .cons { expr := mchain0, sigma := [], ruleName := .ruleChain0, expr' := mchain1 }
  (.cons { expr := mchain1, sigma := [], ruleName := .ruleChain1, expr' := mchain2 }
  (.cons { expr := mchain2, sigma := [], ruleName := .ruleChain2, expr' := mchain3 }
  (.cons { expr := mchain3, sigma := [], ruleName := .ruleChain3, expr' := mchain4 }
  (.cons { expr := mchain4, sigma := [], ruleName := .ruleChain4, expr' := mchain5 }
   .nil))))

theorem S4_peano_add_checked :
    checkTrace addRules addStart addTrace addFinal = .ok addFinal := by rfl

theorem S4_peano_add_sound :
    Relation.ReflTransGen (EncReduces addRules) (enc addStart) (enc addFinal) ∧
      BaseNormal (encPresentation addRules) (enc addFinal) :=
  S3_trace_sound S4_peano_add_checked

theorem S4_snoc_append_checked :
    checkTrace appendRules appendStart appendTrace appendFinal = .ok appendFinal := by rfl

theorem S4_snoc_append_sound :
    Relation.ReflTransGen (EncReduces appendRules) (enc appendStart) (enc appendFinal) ∧
      BaseNormal (encPresentation appendRules) (enc appendFinal) :=
  S3_trace_sound S4_snoc_append_checked

theorem S4_five_step_chain_checked :
    checkTrace chainRules mchain0 chainTrace mchain5 = .ok mchain5 := by rfl

theorem S4_five_step_chain_sound :
    Relation.ReflTransGen (EncReduces chainRules) (enc mchain0) (enc mchain5) ∧
      BaseNormal (encPresentation chainRules) (enc mchain5) :=
  S3_trace_sound S4_five_step_chain_checked

theorem S4_stuck_checked :
    checkTrace stuckRules mstuck .nil mstuck = .ok mstuck := by rfl

theorem S4_stuck_sound :
    Relation.ReflTransGen (EncReduces stuckRules) (enc mstuck) (enc mstuck) ∧
      BaseNormal (encPresentation stuckRules) (enc mstuck) :=
  S3_trace_sound S4_stuck_checked

end Mettapedia.GSLT.SelfMeTTa.MinimalMeTTaWitness
