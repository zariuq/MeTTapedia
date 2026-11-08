import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TrustedVersions

/-!
# Programs of several heads: the chain hypotheses from the analysis

`TrustedVersions.machine_eq_protocol` runs a program of several heads on the
machine (`return_class`, `checks_return`), every activation owing a class, and
proves it the protocol's run under `ChainHyps`. This module reads `ChainHyps`
off the analysis of the right-hand sides, for every program, so that no program
needs its own proof.

* **Outcomes** (`Expr.evalOut`). A head's right-hand side gives, in a tail
  position, its calls to heads, itself or another, as outcomes
  `(head, arguments)`; the branches of an `if`, the body of a `let` and the arms
  of a `case` are tail positions, and everything else is evaluated, the oracle
  answering its calls. Read through the program's oracle, the outcomes are the
  right-hand side's values (`evalOut_answers`, `stepsOf_answers`), so the
  program's protocol runs each head's equations as `TrustedVersions` reads them.
* **The analysis** (`ProgramAccepted`). Each head reads the facts of its formals;
  a typed head's formals and range are its row's, and every typed head whose
  range the analysis does not prove owes one class `range₀`. Every equation has
  linear patterns and makes its calls at their callees' formals (`CallsOK`);
  calls into untyped heads stand in tail positions only (`TailOut`); a head
  whose range is proved calls typed heads only and has its range
  (`HasType`).
* **The chain hypotheses** (`program_chainHyps`). An activation's arguments meet
  its head's entry facts, it owes its head's class or `range₀`
  (`ProgramAct`), and every call outside a tail position is made at its
  callee's entry facts. Outcomes read the oracle at those calls only
  (`evalOut_congr`), and tail calls are made at their callees' entry facts
  (`evalOut_tails`), when the oracle's answers at the typed heads meet their
  facts: the analysis reads the oracle through `sanitize`, which answers the
  typed heads' calls only, and an expression whose calls go to typed heads reads
  nothing else (`eval_sanitize`).
* **The machine is the protocol** (`program_machine_eq_protocol`), at every fuel,
  for every call of a head at its entry facts.

Controls: the counter `cnt`, owing `Number` and calling itself in a tail
position, and its untyped caller `top`, are accepted (`Controls.cnt_accepted`,
`Controls.cnt_machine`); a tail call to a typed head whose argument an untyped
helper computes is made where the callee's entry fact fails, and the analysis
rejects it (`Controls.untyped_argument_breaks`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Outcomes of a right-hand side -/

namespace Expr

mutual
/-- **The outcomes of a right-hand side of the head `h`**: in a tail position, a
call to a head, itself or another, is the outcome `(head, arguments)`; the
branches of an `if`, the body of a `let` and the arms of a `case` are tail
positions; everything else is evaluated, the oracle answering its calls. -/
def evalOut (E : Env) (O : Oracle) (h : String) (ρ : List (String × Atom)) :
    Expr → Multiset (Atom ⊕ (String × List Atom))
  | .var x => (eval E O ρ (.var x)).map .inl
  | .const a => (eval E O ρ (.const a)).map .inl
  | .ctor c args => (eval E O ρ (.ctor c args)).map .inl
  | .self args => (evalAll E O ρ args).map fun ws => .inr (h, ws)
  | .prim op args => (eval E O ρ (.prim op args)).map .inl
  | .call f args => (eval E O ρ (.call f args)).map .inl
  | .enter f args => (evalAll E O ρ args).map fun ws => .inr (f, ws)
  | .letE p v b => (eval E O ρ v).bind fun w =>
      match Pat.matchUnder ρ p w with
      | some ρ' => evalOut E O h ρ' b
      | none => 0
  | .ifE c t e => (eval E O ρ c).bind fun w =>
      if w = truth then evalOut E O h ρ t else evalOut E O h ρ e
  | .empty => 0
  | .caseE k ps bs => (eval E O ρ k).bind fun w => evalOutArms E O h ρ w ps bs
  | .matchE src p t => (eval E O ρ (.matchE src p t)).map .inl

/-- The outcomes of the arms of a `case` at the key's value `w`: the first arm
whose pattern matches. -/
def evalOutArms (E : Env) (O : Oracle) (h : String) (ρ : List (String × Atom)) (w : Atom) :
    List Pat → List Expr → Multiset (Atom ⊕ (String × List Atom))
  | p :: ps, b :: bs => match Pat.matchUnder ρ p w with
    | some ρ' => evalOut E O h ρ' b
    | none => evalOutArms E O h ρ w ps bs
  | _, _ => 0
end

end Expr

/-- The oracle a head's equations read in a program whose heads the oracle `P`
answers: a call to itself is `P h`, a call to another head `P f`. -/
def oracleOf (P : String → List Atom → Multiset Atom) (h : String) : Oracle := ⟨P h, P⟩

theorem singleton_bind_inl (m : Multiset Atom) (P : String → List Atom → Multiset Atom) :
    (m.map (Sum.inl : Atom → Atom ⊕ (String × List Atom))).bind (outcomeAnswers P) = m := by
  rw [Multiset.bind_map]
  simp only [outcomeAnswers]
  rw [Multiset.bind_singleton, Multiset.map_id']

mutual
/-- **The outcomes, the oracle answering their calls, are the values**: a head's
right-hand side read as outcomes and then answered by the program's oracle is
the same right-hand side evaluated with that oracle. -/
theorem evalOut_answers (E : Env) (P : String → List Atom → Multiset Atom) (h : String) :
    ∀ (ρ : List (String × Atom)) (e : Expr),
      (Expr.evalOut E (oracleOf P h) h ρ e).bind (outcomeAnswers P) =
        Expr.eval E (oracleOf P h) ρ e
  | ρ, .var x => by rw [Expr.evalOut, singleton_bind_inl]
  | ρ, .const a => by rw [Expr.evalOut, singleton_bind_inl]
  | ρ, .ctor c args => by rw [Expr.evalOut, singleton_bind_inl]
  | ρ, .self args => by
      rw [Expr.evalOut, Multiset.bind_map, Expr.eval]
      rfl
  | ρ, .prim op args => by rw [Expr.evalOut, singleton_bind_inl]
  | ρ, .call f args => by rw [Expr.evalOut, singleton_bind_inl]
  | ρ, .enter f args => by
      rw [Expr.evalOut, Multiset.bind_map, Expr.eval]
      rfl
  | ρ, .letE p v b => by
      rw [Expr.evalOut, Multiset.bind_assoc, Expr.eval]
      refine Multiset.bind_congr fun w _ => ?_
      cases Pat.matchUnder ρ p w with
      | some ρ' => exact evalOut_answers E P h ρ' b
      | none => exact Multiset.zero_bind _
  | ρ, .ifE c t e => by
      rw [Expr.evalOut, Multiset.bind_assoc, Expr.eval]
      refine Multiset.bind_congr fun w _ => ?_
      split
      · exact evalOut_answers E P h ρ t
      · exact evalOut_answers E P h ρ e
  | ρ, .empty => by rw [Expr.evalOut, Expr.eval, Multiset.zero_bind]
  | ρ, .caseE k ps bs => by
      rw [Expr.evalOut, Multiset.bind_assoc, Expr.eval]
      exact Multiset.bind_congr fun w _ => evalOutArms_answers E P h ρ w ps bs
  | ρ, .matchE src p t => by rw [Expr.evalOut, singleton_bind_inl]

/-- The arms of a `case`. -/
theorem evalOutArms_answers (E : Env) (P : String → List Atom → Multiset Atom) (h : String)
    (ρ : List (String × Atom)) (w : Atom) :
    ∀ (ps : List Pat) (bs : List Expr),
      (Expr.evalOutArms E (oracleOf P h) h ρ w ps bs).bind (outcomeAnswers P) =
        Expr.evalArms E (oracleOf P h) ρ w ps bs
  | p :: ps, b :: bs => by
      rw [Expr.evalOutArms, Expr.evalArms]
      cases Pat.matchUnder ρ p w with
      | some ρ' => exact evalOut_answers E P h ρ' b
      | none => exact evalOutArms_answers E P h ρ w ps bs
  | [], _ => by simp [Expr.evalOutArms, Expr.evalArms]
  | _ :: _, [] => by simp [Expr.evalOutArms, Expr.evalArms]
end

/-! ## Calls into typed heads -/

mutual
/-- **Every call goes to a typed head**: each `.enter f` names a head that
`typed` marks, and a call to itself occurs only where `selfTyped`. -/
def CallsTyped (typed : String → Bool) (selfTyped : Bool) : Expr → Prop
  | .var _ => True
  | .const _ => True
  | .ctor _ args => CallsTypedAll typed selfTyped args
  | .self args => selfTyped = true ∧ CallsTypedAll typed selfTyped args
  | .prim _ args => CallsTypedAll typed selfTyped args
  | .call _ args => CallsTypedAll typed selfTyped args
  | .enter f args => typed f = true ∧ CallsTypedAll typed selfTyped args
  | .letE _ v b => CallsTyped typed selfTyped v ∧ CallsTyped typed selfTyped b
  | .ifE c t e => CallsTyped typed selfTyped c ∧ CallsTyped typed selfTyped t ∧
      CallsTyped typed selfTyped e
  | .empty => True
  | .caseE k _ bs => CallsTyped typed selfTyped k ∧ CallsTypedAll typed selfTyped bs
  | .matchE src _ t => CallsTyped typed selfTyped src ∧ CallsTyped typed selfTyped t

/-- Every call of every element goes to a typed head. -/
def CallsTypedAll (typed : String → Bool) (selfTyped : Bool) : List Expr → Prop
  | [] => True
  | e :: es => CallsTyped typed selfTyped e ∧ CallsTypedAll typed selfTyped es
end

theorem callsTypedAll_iff (typed : String → Bool) (selfTyped : Bool) :
    ∀ es : List Expr, CallsTypedAll typed selfTyped es ↔ ∀ e ∈ es, CallsTyped typed selfTyped e
  | [] => by simp [CallsTypedAll]
  | e :: es => by simp [CallsTypedAll, callsTypedAll_iff typed selfTyped es]

/-- The oracle that answers only the typed heads' calls. -/
def sanitize (typed : String → Bool) (selfTyped : Bool) (O : Oracle) : Oracle :=
  ⟨fun ws => if selfTyped = true then O.self ws else 0,
    fun f ws => if typed f = true then O.enter f ws else 0⟩

mutual
/-- **An expression whose calls go to typed heads reads the oracle there only.** -/
theorem eval_sanitize (E : Env) (typed : String → Bool) (selfTyped : Bool) (O : Oracle) :
    ∀ (e : Expr) (ρ : List (String × Atom)), CallsTyped typed selfTyped e →
      e.eval E O ρ = e.eval E (sanitize typed selfTyped O) ρ
  | .var _, _, _ => rfl
  | .const _, _, _ => rfl
  | .ctor _ args, ρ, h => by
      simp only [Expr.eval]; rw [evalAll_sanitize E typed selfTyped O args ρ h]
  | .self args, ρ, ⟨hs, h⟩ => by
      simp only [Expr.eval]
      rw [evalAll_sanitize E typed selfTyped O args ρ h]
      simp [sanitize, hs]
  | .prim _ args, ρ, h => by
      simp only [Expr.eval]; rw [evalAll_sanitize E typed selfTyped O args ρ h]
  | .call _ args, ρ, h => by
      simp only [Expr.eval]; rw [evalAll_sanitize E typed selfTyped O args ρ h]
  | .enter f args, ρ, ⟨hf, h⟩ => by
      simp only [Expr.eval]
      rw [evalAll_sanitize E typed selfTyped O args ρ h]
      simp [sanitize, hf]
  | .letE p v b, ρ, ⟨hv, hb⟩ => by
      simp only [Expr.eval]
      rw [eval_sanitize E typed selfTyped O v ρ hv]
      refine Multiset.bind_congr fun w _ => ?_
      split
      · next ρ' _ => exact eval_sanitize E typed selfTyped O b ρ' hb
      · rfl
  | .ifE c t e, ρ, ⟨hc, ht, he⟩ => by
      simp only [Expr.eval]
      rw [eval_sanitize E typed selfTyped O c ρ hc, eval_sanitize E typed selfTyped O t ρ ht,
        eval_sanitize E typed selfTyped O e ρ he]
  | .empty, _, _ => rfl
  | .caseE k ps bs, ρ, ⟨hk, hbs⟩ => by
      simp only [Expr.eval]
      rw [eval_sanitize E typed selfTyped O k ρ hk]
      exact Multiset.bind_congr fun w _ => evalArms_sanitize E typed selfTyped O w ps bs ρ hbs
  | .matchE src p t, ρ, ⟨hs, ht⟩ => by
      simp only [Expr.eval]
      rw [eval_sanitize E typed selfTyped O src ρ hs]
      refine Multiset.bind_congr fun sp _ => Multiset.bind_congr fun row _ => ?_
      split
      · next ρ' _ => exact eval_sanitize E typed selfTyped O t ρ' ht
      · rfl

/-- The list version. -/
theorem evalAll_sanitize (E : Env) (typed : String → Bool) (selfTyped : Bool) (O : Oracle) :
    ∀ (es : List Expr) (ρ : List (String × Atom)), CallsTypedAll typed selfTyped es →
      Expr.evalAll E O ρ es = Expr.evalAll E (sanitize typed selfTyped O) ρ es
  | [], _, _ => rfl
  | e :: es, ρ, ⟨he, hes⟩ => by
      simp only [Expr.evalAll]
      rw [eval_sanitize E typed selfTyped O e ρ he, evalAll_sanitize E typed selfTyped O es ρ hes]

/-- The arms of a `case`. -/
theorem evalArms_sanitize (E : Env) (typed : String → Bool) (selfTyped : Bool) (O : Oracle)
    (w : Atom) : ∀ (ps : List Pat) (bs : List Expr) (ρ : List (String × Atom)),
      CallsTypedAll typed selfTyped bs →
        Expr.evalArms E O ρ w ps bs = Expr.evalArms E (sanitize typed selfTyped O) ρ w ps bs
  | p :: ps, b :: bs, ρ, ⟨hb, hbs⟩ => by
      simp only [Expr.evalArms]
      split
      · next ρ' _ => exact eval_sanitize E typed selfTyped O b ρ' hb
      · exact evalArms_sanitize E typed selfTyped O w ps bs ρ hbs
  | [], _, _, _ => by simp [Expr.evalArms]
  | _ :: _, [], _, _ => by simp [Expr.evalArms]
end

/-- **Tail positions of a head's right-hand side**: calls to heads, typed or not,
may stand in tail positions; everything outside a tail position calls typed
heads only. -/
inductive TailOut (typed : String → Bool) (selfTyped : Bool) : Expr → Prop
  | plain {e : Expr} : CallsTyped typed selfTyped e → TailOut typed selfTyped e
  | self {args : List Expr} : CallsTypedAll typed selfTyped args →
      TailOut typed selfTyped (.self args)
  | enter {f : String} {args : List Expr} : CallsTypedAll typed selfTyped args →
      TailOut typed selfTyped (.enter f args)
  | letE {p : Pat} {v b : Expr} : CallsTyped typed selfTyped v → TailOut typed selfTyped b →
      TailOut typed selfTyped (.letE p v b)
  | ifE {c t e : Expr} : CallsTyped typed selfTyped c → TailOut typed selfTyped t →
      TailOut typed selfTyped e → TailOut typed selfTyped (.ifE c t e)
  | caseE {k : Expr} {ps : List Pat} {bs : List Expr} : CallsTyped typed selfTyped k →
      (∀ b ∈ bs, TailOut typed selfTyped b) → TailOut typed selfTyped (.caseE k ps bs)


/-! ## What the analysis gives of outcomes -/

section Outcomes

variable {Γ : Decls} {grounded : String → Bool} {res : String → Ty Empty}
  {ent : String → List (Ty Empty)} {Φ : String → Ty Empty → Prop} {R : Ty Empty}
  {As : List (Ty String)} {E : Env} {typed : String → Bool} {selfTyped : Bool}

/-- **Two oracles that agree on the typed heads' calls the analysis makes give
the same values** of an expression whose calls go to typed heads, when the
second answers those calls with values meeting their facts. -/
theorem eval_typed_congr (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E) {O O' : Oracle}
    (hO : OracleOK Γ grounded res ent As R (sanitize typed selfTyped O'))
    (agree : OracleAgree Γ grounded ent As (sanitize typed selfTyped O')
      (sanitize typed selfTyped O))
    {e : Expr} (he : CallsTyped typed selfTyped e) {ρ : List (String × Atom)}
    (facts : MeetsFacts Γ grounded Φ ρ) (calls : CallsOK Γ res ent Φ R As e) :
    e.eval E O ρ = e.eval E O' ρ := by
  rw [eval_sanitize E typed selfTyped O e ρ he, eval_sanitize E typed selfTyped O' e ρ he]
  exact (eval_congr hΓ hE hO agree e ρ facts calls).symm

theorem evalAll_typed_congr (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E) {O O' : Oracle}
    (hO : OracleOK Γ grounded res ent As R (sanitize typed selfTyped O'))
    (agree : OracleAgree Γ grounded ent As (sanitize typed selfTyped O')
      (sanitize typed selfTyped O))
    {args : List Expr} (hargs : CallsTypedAll typed selfTyped args) {ρ : List (String × Atom)}
    (facts : MeetsFacts Γ grounded Φ ρ) (calls : ∀ e ∈ args, CallsOK Γ res ent Φ R As e) :
    Expr.evalAll E O ρ args = Expr.evalAll E O' ρ args :=
  Expr.evalAll_congr args fun e member =>
    eval_typed_congr hΓ hE hO agree ((callsTypedAll_iff typed selfTyped args).mp hargs e member)
      facts (calls e member)

theorem TailOut.callsTyped_of_value {e : Expr} (tail : TailOut typed selfTyped e)
    (value : ∀ args, e ≠ .self args) (valueEnter : ∀ f args, e ≠ .enter f args)
    (valueLet : ∀ p v b, e ≠ .letE p v b) (valueIf : ∀ c t f, e ≠ .ifE c t f)
    (valueCase : ∀ k ps bs, e ≠ .caseE k ps bs) : CallsTyped typed selfTyped e := by
  cases tail with
  | plain h => exact h
  | self _ => exact absurd rfl (value _)
  | enter _ => exact absurd rfl (valueEnter _ _)
  | letE _ _ => exact absurd rfl (valueLet _ _ _)
  | ifE _ _ _ => exact absurd rfl (valueIf _ _ _)
  | caseE _ _ => exact absurd rfl (valueCase _ _ _)

theorem TailOut.args_self {args : List Expr} (tail : TailOut typed selfTyped (.self args)) :
    CallsTypedAll typed selfTyped args := by
  cases tail with
  | plain h => exact h.2
  | self h => exact h

theorem TailOut.args_enter {f : String} {args : List Expr}
    (tail : TailOut typed selfTyped (.enter f args)) : CallsTypedAll typed selfTyped args := by
  cases tail with
  | plain h => exact h.2
  | enter h => exact h

theorem TailOut.letE_inv {p : Pat} {v b : Expr} (tail : TailOut typed selfTyped (.letE p v b)) :
    CallsTyped typed selfTyped v ∧ TailOut typed selfTyped b := by
  cases tail with
  | plain h => exact ⟨h.1, .plain h.2⟩
  | letE hv hb => exact ⟨hv, hb⟩

theorem TailOut.ifE_inv {c t f : Expr} (tail : TailOut typed selfTyped (.ifE c t f)) :
    CallsTyped typed selfTyped c ∧ TailOut typed selfTyped t ∧ TailOut typed selfTyped f := by
  cases tail with
  | plain h => exact ⟨h.1, .plain h.2.1, .plain h.2.2⟩
  | ifE hc ht hf => exact ⟨hc, ht, hf⟩

theorem TailOut.caseE_inv {k : Expr} {ps : List Pat} {bs : List Expr}
    (tail : TailOut typed selfTyped (.caseE k ps bs)) :
    CallsTyped typed selfTyped k ∧ ∀ b ∈ bs, TailOut typed selfTyped b := by
  cases tail with
  | plain h =>
      exact ⟨h.1, fun b member => .plain ((callsTypedAll_iff typed selfTyped bs).mp h.2 b member)⟩
  | caseE hk hbs => exact ⟨hk, hbs⟩

/-- The outcomes of an expression evaluated as a value are its values. -/
theorem evalOut_value (O : Oracle) (h : String) (ρ : List (String × Atom)) {e : Expr}
    (value : ∀ args, e ≠ .self args) (valueEnter : ∀ f args, e ≠ .enter f args)
    (valueLet : ∀ p v b, e ≠ .letE p v b) (valueIf : ∀ c t f, e ≠ .ifE c t f)
    (valueCase : ∀ k ps bs, e ≠ .caseE k ps bs) :
    e.evalOut E O h ρ = (e.eval E O ρ).map .inl := by
  cases e with
  | self args => exact absurd rfl (value args)
  | enter f args => exact absurd rfl (valueEnter f args)
  | letE p v b => exact absurd rfl (valueLet p v b)
  | ifE c t f => exact absurd rfl (valueIf c t f)
  | caseE k ps bs => exact absurd rfl (valueCase k ps bs)
  | empty => simp [Expr.evalOut, Expr.eval]
  | var _ => rfl
  | const _ => rfl
  | ctor _ _ => rfl
  | prim _ _ => rfl
  | call _ _ => rfl
  | matchE _ _ _ => rfl

mutual
/-- **The outcomes read the oracle at the calls the analysis checks only.** -/
theorem evalOut_congr (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E) {O O' : Oracle}
    (hO : OracleOK Γ grounded res ent As R (sanitize typed selfTyped O'))
    (agree : OracleAgree Γ grounded ent As (sanitize typed selfTyped O')
      (sanitize typed selfTyped O)) (h : String) :
    ∀ (e : Expr) (ρ : List (String × Atom)), TailOut typed selfTyped e →
      MeetsFacts Γ grounded Φ ρ → CallsOK Γ res ent Φ R As e →
        e.evalOut E O h ρ = e.evalOut E O' h ρ
  | .self args, ρ, tail, facts, calls => by
      cases calls with
      | self hargs _ =>
          simp only [Expr.evalOut]
          rw [evalAll_typed_congr hΓ hE hO agree tail.args_self facts hargs]
  | .enter f args, ρ, tail, facts, calls => by
      cases calls with
      | enter hargs _ =>
          simp only [Expr.evalOut]
          rw [evalAll_typed_congr hΓ hE hO agree tail.args_enter facts hargs]
  | .letE p v b, ρ, tail, facts, calls => by
      obtain ⟨hv, hb⟩ := tail.letE_inv
      cases calls with
      | letE cv cb =>
          simp only [Expr.evalOut]
          rw [eval_typed_congr hΓ hE hO agree hv facts cv]
          refine Multiset.bind_congr fun w _ => ?_
          split
          · next ρ' hm =>
              exact evalOut_congr hΓ hE hO agree h b ρ' hb
                (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) cb
          · rfl
  | .ifE c t f, ρ, tail, facts, calls => by
      obtain ⟨hc, ht, hf⟩ := tail.ifE_inv
      cases calls with
      | ifE cc ct cf =>
          simp only [Expr.evalOut]
          rw [eval_typed_congr hΓ hE hO agree hc facts cc,
            evalOut_congr hΓ hE hO agree h t ρ ht facts ct,
            evalOut_congr hΓ hE hO agree h f ρ hf facts cf]
  | .caseE k ps bs, ρ, tail, facts, calls => by
      obtain ⟨hk, hbs⟩ := tail.caseE_inv
      cases calls with
      | caseE ck cbs =>
          simp only [Expr.evalOut]
          rw [eval_typed_congr hΓ hE hO agree hk facts ck]
          exact Multiset.bind_congr fun w _ =>
            evalOutArms_congr hΓ hE hO agree h w ps bs ρ hbs facts cbs
  | .empty, _, _, _, _ => rfl
  | .var x, ρ, tail, facts, calls => by
      rw [evalOut_value O h ρ (by simp) (by simp) (by simp) (by simp) (by simp),
        evalOut_value O' h ρ (by simp) (by simp) (by simp) (by simp) (by simp),
        eval_typed_congr hΓ hE hO agree (tail.callsTyped_of_value (by simp) (by simp) (by simp)
          (by simp) (by simp)) facts calls]
  | .const a, ρ, tail, facts, calls => by
      rw [evalOut_value O h ρ (by simp) (by simp) (by simp) (by simp) (by simp),
        evalOut_value O' h ρ (by simp) (by simp) (by simp) (by simp) (by simp),
        eval_typed_congr hΓ hE hO agree (tail.callsTyped_of_value (by simp) (by simp) (by simp)
          (by simp) (by simp)) facts calls]
  | .ctor c args, ρ, tail, facts, calls => by
      rw [evalOut_value O h ρ (by simp) (by simp) (by simp) (by simp) (by simp),
        evalOut_value O' h ρ (by simp) (by simp) (by simp) (by simp) (by simp),
        eval_typed_congr hΓ hE hO agree (tail.callsTyped_of_value (by simp) (by simp) (by simp)
          (by simp) (by simp)) facts calls]
  | .prim op args, ρ, tail, facts, calls => by
      rw [evalOut_value O h ρ (by simp) (by simp) (by simp) (by simp) (by simp),
        evalOut_value O' h ρ (by simp) (by simp) (by simp) (by simp) (by simp),
        eval_typed_congr hΓ hE hO agree (tail.callsTyped_of_value (by simp) (by simp) (by simp)
          (by simp) (by simp)) facts calls]
  | .call f args, ρ, tail, facts, calls => by
      rw [evalOut_value O h ρ (by simp) (by simp) (by simp) (by simp) (by simp),
        evalOut_value O' h ρ (by simp) (by simp) (by simp) (by simp) (by simp),
        eval_typed_congr hΓ hE hO agree (tail.callsTyped_of_value (by simp) (by simp) (by simp)
          (by simp) (by simp)) facts calls]
  | .matchE src p t, ρ, tail, facts, calls => by
      rw [evalOut_value O h ρ (by simp) (by simp) (by simp) (by simp) (by simp),
        evalOut_value O' h ρ (by simp) (by simp) (by simp) (by simp) (by simp),
        eval_typed_congr hΓ hE hO agree (tail.callsTyped_of_value (by simp) (by simp) (by simp)
          (by simp) (by simp)) facts calls]

/-- The arms of a `case`. -/
theorem evalOutArms_congr (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E) {O O' : Oracle}
    (hO : OracleOK Γ grounded res ent As R (sanitize typed selfTyped O'))
    (agree : OracleAgree Γ grounded ent As (sanitize typed selfTyped O')
      (sanitize typed selfTyped O)) (h : String) (w : Atom) :
    ∀ (ps : List Pat) (bs : List Expr) (ρ : List (String × Atom)),
      (∀ b ∈ bs, TailOut typed selfTyped b) → MeetsFacts Γ grounded Φ ρ →
      (∀ b ∈ bs, CallsOK Γ res ent Φ R As b) →
        Expr.evalOutArms E O h ρ w ps bs = Expr.evalOutArms E O' h ρ w ps bs
  | p :: ps, b :: bs, ρ, tails, facts, calls => by
      simp only [Expr.evalOutArms]
      split
      · next ρ' hm =>
          exact evalOut_congr hΓ hE hO agree h b ρ' (tails b (by simp))
            (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) (calls b (by simp))
      · exact evalOutArms_congr hΓ hE hO agree h w ps bs ρ (fun b' m => tails b' (by simp [m]))
          facts fun b' m => calls b' (by simp [m])
  | [], _, _, _, _, _ => by simp [Expr.evalOutArms]
  | _ :: _, [], _, _, _, _ => by simp [Expr.evalOutArms]
end

mutual
/-- **Every call in a tail position is made at its callee's entry facts**: a
call to itself at the formals, a call to another head at that head's. -/
theorem evalOut_tails (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E) {O : Oracle}
    (hO : OracleOK Γ grounded res ent As R (sanitize typed selfTyped O)) (h : String) :
    ∀ (e : Expr) (ρ : List (String × Atom)), TailOut typed selfTyped e →
      MeetsFacts Γ grounded Φ ρ → CallsOK Γ res ent Φ R As e →
        ∀ g ws, (.inr (g, ws) : Atom ⊕ (String × List Atom)) ∈ e.evalOut E O h ρ →
          (g = h ∧ EntryPoly Γ grounded As ws) ∨ EntryFacts Γ grounded (ent g) ws
  | .self args, ρ, tail, facts, calls, g, ws, member => by
      cases calls with
      | self hargs typedArgs =>
          simp only [Expr.evalOut, Multiset.mem_map] at member
          obtain ⟨ws', inArgs, same⟩ := member
          cases same
          left
          refine ⟨rfl, ?_⟩
          rw [evalAll_sanitize E typed selfTyped O args ρ tail.args_self] at inArgs
          exact forall₂_compose typedArgs (Expr.evalAll_mem E _ ρ args ws inArgs)
            fun A e w he hA hw hg => by
              obtain ⟨τ, hτ⟩ := hA hg
              exact ⟨τ, List.forall_iff_forall_mem.mp
                (evalAll_sound hΓ hE hO args ρ facts) e he (A.bind τ) hτ (hargs e he) w hw⟩
  | .enter f args, ρ, tail, facts, calls, g, ws, member => by
      cases calls with
      | enter hargs typedArgs =>
          simp only [Expr.evalOut, Multiset.mem_map] at member
          obtain ⟨ws', inArgs, same⟩ := member
          cases same
          right
          rw [evalAll_sanitize E typed selfTyped O args ρ tail.args_enter] at inArgs
          exact forall₂_compose typedArgs (Expr.evalAll_mem E _ ρ args ws inArgs)
            fun A e w he hA hw hg => List.forall_iff_forall_mem.mp
              (evalAll_sound hΓ hE hO args ρ facts) e he A (hA hg) (hargs e he) w hw
  | .letE p v b, ρ, tail, facts, calls, g, ws, member => by
      obtain ⟨_, hb⟩ := tail.letE_inv
      cases calls with
      | letE _ cb =>
          simp only [Expr.evalOut, Multiset.mem_bind] at member
          obtain ⟨w, _, member⟩ := member
          split at member
          · next ρ' hm =>
              exact evalOut_tails hΓ hE hO h b ρ' hb
                (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) cb g ws member
          · exact absurd member (Multiset.notMem_zero _)
  | .ifE c t f, ρ, tail, facts, calls, g, ws, member => by
      obtain ⟨_, ht, hf⟩ := tail.ifE_inv
      cases calls with
      | ifE _ ct cf =>
          simp only [Expr.evalOut, Multiset.mem_bind] at member
          obtain ⟨w, _, member⟩ := member
          split at member
          · exact evalOut_tails hΓ hE hO h t ρ ht facts ct g ws member
          · exact evalOut_tails hΓ hE hO h f ρ hf facts cf g ws member
  | .caseE k ps bs, ρ, tail, facts, calls, g, ws, member => by
      obtain ⟨_, hbs⟩ := tail.caseE_inv
      cases calls with
      | caseE _ cbs =>
          simp only [Expr.evalOut, Multiset.mem_bind] at member
          obtain ⟨w, _, member⟩ := member
          exact evalOutArms_tails hΓ hE hO h w ps bs ρ hbs facts cbs g ws member
  | .empty, _, _, _, _, _, _, member => by simp [Expr.evalOut] at member
  | .var _, _, _, _, _, _, _, member => by simp [Expr.evalOut] at member
  | .const _, _, _, _, _, _, _, member => by simp [Expr.evalOut] at member
  | .ctor _ _, _, _, _, _, _, _, member => by simp [Expr.evalOut] at member
  | .prim _ _, _, _, _, _, _, _, member => by simp [Expr.evalOut] at member
  | .call _ _, _, _, _, _, _, _, member => by simp [Expr.evalOut] at member
  | .matchE _ _ _, _, _, _, _, _, _, member => by simp [Expr.evalOut] at member

/-- The arms of a `case`. -/
theorem evalOutArms_tails (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E) {O : Oracle}
    (hO : OracleOK Γ grounded res ent As R (sanitize typed selfTyped O)) (h : String) (w : Atom) :
    ∀ (ps : List Pat) (bs : List Expr) (ρ : List (String × Atom)),
      (∀ b ∈ bs, TailOut typed selfTyped b) → MeetsFacts Γ grounded Φ ρ →
      (∀ b ∈ bs, CallsOK Γ res ent Φ R As b) →
        ∀ g ws, (.inr (g, ws) : Atom ⊕ (String × List Atom)) ∈ Expr.evalOutArms E O h ρ w ps bs →
          (g = h ∧ EntryPoly Γ grounded As ws) ∨ EntryFacts Γ grounded (ent g) ws
  | p :: ps, b :: bs, ρ, tails, facts, calls, g, ws, member => by
      simp only [Expr.evalOutArms] at member
      split at member
      · next ρ' hm =>
          exact evalOut_tails hΓ hE hO h b ρ' (tails b (by simp))
            (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) (calls b (by simp)) g ws member
      · exact evalOutArms_tails hΓ hE hO h w ps bs ρ (fun b' m => tails b' (by simp [m])) facts
          (fun b' m => calls b' (by simp [m])) g ws member
  | [], _, _, _, _, _, _, _, member => by simp [Expr.evalOutArms] at member
  | _ :: _, [], _, _, _, _, _, _, member => by simp [Expr.evalOutArms] at member
end

end Outcomes


/-! ## A program of several heads -/

section Program

variable (rows : String → Option (List (Ty Empty) × Ty Empty))

/-- Whether a head is typed: it has a closed row. -/
def typedHead (h : String) : Bool := (rows h).isSome

/-- A typed head's row as its protocol reads it; none for an untyped head. -/
def sigOf (h : String) : Option (Ty String) :=
  (rows h).map fun row => arrow (row.1.map Ty.lift) row.2.lift

variable (proves : String → Bool)

/-- **The class an activation of a head owes** (`checks_return`): a typed head's
range where the analysis does not prove it; none for a head whose range it
proves and for an untyped head. -/
def oweOf (h : String) (_ : List Atom) : Option (Ty Empty) :=
  match rows h with
  | some (_, R) => if proves h then none else some R
  | none => none

variable (E : Env) (eqs : String → List Equation)

/-- **The outcomes of a head's equations** at arguments: each equation whose
patterns match gives the outcomes of its right-hand side. -/
def stepsOf (h : String) (P : String → List Atom → Multiset Atom) (vs : List Atom) :
    Multiset (Atom ⊕ (String × List Atom)) :=
  (eqs h : Multiset Equation).bind fun eq =>
    match Pat.matchAll eq.pats vs with
    | some ρ => eq.rhs.evalOut E (oracleOf P h) h ρ
    | none => 0

/-- **A head's outcomes, the program's oracle answering them, are its
equations' answers** with that oracle: the protocol of the program runs every
head's equations as `TrustedVersions` reads them. -/
theorem stepsOf_answers (h : String) (P : String → List Atom → Multiset Atom) (vs : List Atom) :
    (stepsOf E eqs h P vs).bind (outcomeAnswers P) = equationsBody E (eqs h) (oracleOf P h) vs := by
  unfold stepsOf equationsBody
  rw [Multiset.bind_assoc]
  refine Multiset.bind_congr fun eq _ => ?_
  cases Pat.matchAll eq.pats vs with
  | some ρ => exact evalOut_answers E P h ρ eq.rhs
  | none => exact Multiset.zero_bind _

variable (Γ : Decls) (grounded : String → Bool)
variable (res : String → Ty Empty) (ent : String → List (Ty Empty))

/-- **A program the analysis accepts**, every head reading the facts of its
formals `ent h`, its range `res h` where typed, and the program's ranges and
formals at its calls:
* a typed head's formals and range are its row's, its range is guarded, and every
  head that owes a class owes `range₀`;
* a head whose range the analysis proves is typed;
* every equation has linear patterns, calls itself at its formals and other heads
  at theirs (`CallsOK`), and calls untyped heads in tail positions only
  (`TailOut`);
* a head whose range is proved calls typed heads only, and its right-hand sides
  have its range (`HasType`). -/
structure ProgramAccepted (range₀ : Ty Empty) : Prop where
  entRows : ∀ h As R, rows h = some (As, R) → ent h = As
  resRows : ∀ h As R, rows h = some (As, R) → res h = R
  guarded : ∀ h As R, rows h = some (As, R) → ResultGuarded R.lift
  owing : ∀ h As R, rows h = some (As, R) → proves h = false → R = range₀
  provesTyped : ∀ h, proves h = true → typedHead rows h = true
  linear : ∀ h, ∀ eq ∈ eqs h, (Pat.varsAll eq.pats).Nodup
  calls : ∀ h, ∀ eq ∈ eqs h,
    CallsOK Γ res ent (eqFacts Γ (ent h) eq) (res h) ((ent h).map Ty.lift) eq.rhs
  tail : ∀ h, ∀ eq ∈ eqs h, TailOut (typedHead rows) (typedHead rows h) eq.rhs
  proven : ∀ h, proves h = true → ∀ eq ∈ eqs h, CallsTyped (typedHead rows) true eq.rhs ∧
    HasType Γ res (eqFacts Γ (ent h) eq) (res h) eq.rhs (res h)

/-- **The activations of a program's run**: the arguments meet the head's entry
facts, an activation of a head that owes a class owes that class, and every
activation owes `range₀` or nothing. -/
def ProgramAct (range₀ : Ty Empty) (o : Option (Ty Empty)) (h : String) (vs : List Atom) : Prop :=
  EntryFacts Γ grounded (ent h) vs ∧ (∀ R, oweOf rows proves h vs = some R → o = some R) ∧
    (o = none ∨ o = some range₀)

end Program

section ProgramSoundness

variable {rows : String → Option (List (Ty Empty) × Ty Empty)} {proves : String → Bool}
  {E : Env} {eqs : String → List Equation} {Γ : Decls} {grounded : String → Bool}
  {res : String → Ty Empty} {ent : String → List (Ty Empty)} {range₀ : Ty Empty}

theorem oweOf_some {h : String} {vs : List Atom} {R : Ty Empty}
    (owes : oweOf rows proves h vs = some R) :
    ∃ As, rows h = some (As, R) ∧ proves h = false := by
  unfold oweOf at owes
  split at owes
  · next As R' hrow =>
      split_ifs at owes with hp
      cases owes
      exact ⟨As, hrow, by simpa using hp⟩
  · cases owes

theorem oweOf_none_of_typed {h : String} {vs : List Atom} {As : List (Ty Empty)} {R : Ty Empty}
    (hrow : rows h = some (As, R)) (owes : oweOf rows proves h vs = none) : proves h = true := by
  unfold oweOf at owes
  rw [hrow] at owes
  by_contra hp
  simp [hp] at owes

/-- A typed head's protocol at its entry facts checks once at its range. -/
theorem checksAt_row (acc : ProgramAccepted rows proves eqs Γ res ent range₀) {h : String}
    {As : List (Ty Empty)} {R : Ty Empty} (hrow : rows h = some (As, R)) {ws : List Atom}
    (entry : EntryFacts Γ grounded (ent h) ws) :
    ChecksAt Γ grounded (arrow (As.map Ty.lift) R.lift) ws R := by
  rw [acc.entRows h As R hrow] at entry
  exact checksAt_closed (acc.guarded h As R hrow) (argCount_of_entryFacts entry)

/-- **An oracle whose answers meet their facts, read at the typed heads only,
meets what the analysis assumes of oracles.** -/
theorem oracleOK_sanitize (acc : ProgramAccepted rows proves eqs Γ res ent range₀)
    {P : String → List Atom → Multiset Atom} (meets : AnswersMeet Γ grounded (sigOf rows) P)
    (h : String) :
    OracleOK Γ grounded res ent ((ent h).map Ty.lift) (res h)
      (sanitize (typedHead rows) (typedHead rows h) (oracleOf P h)) where
  self ws entry r member := by
    simp only [sanitize, oracleOf] at member
    split_ifs at member with typedH
    · obtain ⟨⟨As, R⟩, hrow⟩ := Option.isSome_iff_exists.mp typedH
      rw [acc.resRows h As R hrow]
      have entry' := (entryPoly_lift_iff _ _ (ent h) ws).mp entry
      exact meets h ws _ R (by simp [sigOf, hrow]) (checksAt_row acc hrow entry') r member
    · exact absurd member (Multiset.notMem_zero r)
  enter f ws entry r member := by
    simp only [sanitize, oracleOf] at member
    split_ifs at member with typedF
    · obtain ⟨⟨As, R⟩, hrow⟩ := Option.isSome_iff_exists.mp typedF
      rw [acc.resRows f As R hrow]
      exact meets f ws _ R (by simp [sigOf, hrow]) (checksAt_row acc hrow entry) r member
    · exact absurd member (Multiset.notMem_zero r)

/-- Two oracles that agree at every call meeting its callee's entry facts agree
where the analysis reads them. -/
theorem oracleAgree_sanitize {P Q : String → List Atom → Multiset Atom} (h : String)
    (same : ∀ g ws, EntryFacts Γ grounded (ent g) ws → P g ws = Q g ws) :
    OracleAgree Γ grounded ent ((ent h).map Ty.lift)
      (sanitize (typedHead rows) (typedHead rows h) (oracleOf P h))
      (sanitize (typedHead rows) (typedHead rows h) (oracleOf Q h)) :=
  ⟨fun ws entry => by
      simp only [sanitize, oracleOf]
      rw [same h ws ((entryPoly_lift_iff _ _ (ent h) ws).mp entry)],
    fun f ws entry => by
      simp only [sanitize, oracleOf]
      rw [same f ws entry]⟩

/-- **The analysis gives the hypotheses of the chain theorem** for every
program it accepts: activations owe their head's class or `range₀`, a head
whose range is proved keeps each answer once, the outcomes read the oracle at
calls meeting their callees' entry facts only, and every call, in a tail
position or not, starts or continues an activation. -/
theorem program_chainHyps (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E)
    (acc : ProgramAccepted rows proves eqs Γ res ent range₀) :
    ChainHyps Γ grounded (sigOf rows) (oweOf rows proves) (stepsOf E eqs)
      (fun _ _ g ws => EntryFacts Γ grounded (ent g) ws)
      (ProgramAct rows proves Γ grounded ent range₀) where
  owes o h vs R act owes := by
    obtain ⟨As, hrow, _⟩ := oweOf_some owes
    exact ⟨act.2.1 R owes, _, by simp [sigOf, hrow], checksAt_row acc hrow act.1⟩
  proven o h vs T act owes sig P meets := by
    obtain ⟨⟨As, R⟩, hrow, rfl⟩ : ∃ row, rows h = some row ∧
        arrow (row.1.map Ty.lift) row.2.lift = T := by
      simpa [sigOf] using sig
    have provesH := oweOf_none_of_typed hrow owes
    rw [chainCall_closed, argCount_of_entryFacts (acc.entRows h As R hrow ▸ act.1), one_nsmul]
    simp only [if_pos (acc.guarded h As R hrow)]
    have answers : ∀ r ∈ (stepsOf E eqs h P vs).bind (outcomeAnswers P),
        Holds Γ grounded r R := by
      intro r member
      rw [stepsOf_answers] at member
      unfold equationsBody at member
      obtain ⟨eq, eqMember, member⟩ := Multiset.mem_bind.mp member
      split at member
      · next ρ hm =>
          obtain ⟨typedCalls, hasType⟩ := acc.proven h provesH eq eqMember
          rw [eval_sanitize E (typedHead rows) true (oracleOf P h) eq.rhs ρ typedCalls] at member
          have typedH : typedHead rows h = true := by simp [typedHead, hrow]
          rw [← typedH] at member
          have facts := eqFacts_sound hΓ (acc.linear h eq eqMember) hm act.1
          have sound := eval_sound hΓ hE (oracleOK_sanitize acc meets h) eq.rhs ρ facts (res h)
            hasType (acc.calls h eq eqMember) r member
          rwa [acc.resRows h As R hrow] at sound
      · exact absurd member (Multiset.notMem_zero r)
    refine (Multiset.bind_congr (g := fun r => ({r} : Multiset Atom)) fun r member => ?_).trans ?_
    · rw [(answers r member).guardCount, one_nsmul]
    · rw [Multiset.bind_singleton, Multiset.map_id']
  congr o h vs act P Q meets same := by
    unfold stepsOf
    refine Multiset.bind_congr fun eq eqMember => ?_
    split
    · next ρ hm =>
        have facts := eqFacts_sound hΓ (acc.linear h eq eqMember) hm act.1
        exact evalOut_congr hΓ hE (oracleOK_sanitize acc meets h)
          (oracleAgree_sanitize h fun g ws entry => (same g ws entry).symm) h eq.rhs ρ
          (acc.tail h eq eqMember) facts (acc.calls h eq eqMember)
    · rfl
  nonTail o h vs g ws act entry := by
    refine ⟨entry, fun R owes => owes, ?_⟩
    cases owesG : oweOf rows proves g ws with
    | none => exact Or.inl rfl
    | some R =>
        obtain ⟨As, hrow, notProved⟩ := oweOf_some owesG
        exact Or.inr (by rw [acc.owing g As R hrow notProved])
  tail o h vs P act meets g ws member := by
    unfold stepsOf at member
    obtain ⟨eq, eqMember, member⟩ := Multiset.mem_bind.mp member
    split at member
    · next ρ hm =>
        have facts := eqFacts_sound hΓ (acc.linear h eq eqMember) hm act.1
        have entry := evalOut_tails hΓ hE (oracleOK_sanitize acc meets h) h eq.rhs ρ
          (acc.tail h eq eqMember) facts (acc.calls h eq eqMember) g ws member
        have entryG : EntryFacts Γ grounded (ent g) ws := by
          rcases entry with ⟨rfl, poly⟩ | facts'
          · exact (entryPoly_lift_iff _ _ (ent g) ws).mp poly
          · exact facts'
        refine ⟨entryG, fun R owes => ?_, ?_⟩
        · obtain ⟨As, hrow, notProved⟩ := oweOf_some owes
          rcases act.2.2 with rfl | rfl
          · simpa using owes
          · rw [acc.owing g As R hrow notProved]
            rfl
        · rcases act.2.2 with rfl | rfl
          · cases owesG : oweOf rows proves g ws with
            | none => exact Or.inl (by simp)
            | some R =>
                obtain ⟨As, hrow, notProved⟩ := oweOf_some owesG
                exact Or.inr (by simp [acc.owing g As R hrow notProved])
          · exact Or.inr rfl
    · exact absurd member (Multiset.notMem_zero _)

/-- **The machine runs every accepted program as its protocol does**
(`return_class`, `checks_return`), at every fuel: a call of a head at its entry
facts, from the evaluator or outside a tail position, owing its head's class,
answers the protocol's answers, every call checking its own result. -/
theorem program_machine_eq_protocol (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E)
    (acc : ProgramAccepted rows proves eqs Γ res ent range₀) (n : ℕ) (h : String)
    (vs : List Atom) (entry : EntryFacts Γ grounded (ent h) vs) :
    machineRunS Γ grounded (oweOf rows proves) (stepsOf E eqs) n (oweOf rows proves h vs) h vs =
      protocolRunS Γ grounded (sigOf rows) (stepsOf E eqs) n h vs := by
  refine machine_call_eq_protocol hΓ (program_chainHyps hΓ hE acc) ⟨entry, fun R owes => owes, ?_⟩ n
  cases owesH : oweOf rows proves h vs with
  | none => exact Or.inl rfl
  | some R =>
      obtain ⟨As, hrow, notProved⟩ := oweOf_some owesH
      exact Or.inr (by rw [acc.owing h As R hrow notProved])

end ProgramSoundness


/-! ## Controls -/

namespace Controls

/-- `%Undefined%`. -/
def undefinedTy : Ty Empty := .sym "%Undefined%"

/-- `(: cnt (-> Number %Undefined% Number))`; `top` is untyped. -/
def cntRows : String → Option (List (Ty Empty) × Ty Empty)
  | "cnt" => some ([.sym "Number", undefinedTy], .sym "Number")
  | _ => none

/-- The formals each head reads. -/
def cntEnt : String → List (Ty Empty)
  | "cnt" => [.sym "Number", undefinedTy]
  | _ => []

/-- The ranges; only `cnt`'s is read. -/
def cntRes : String → Ty Empty := fun _ => .sym "Number"

/-- `(= (cnt $n $acc) (if (== $n 0) $acc (cnt (- $n 1) (+ $acc 1))))` and
`(= (top) (+ 1 (cnt 3 0)))`. -/
def cntEqs : String → List Equation
  | "cnt" => [⟨[.var "n", .var "acc"], .ifE (.prim "==" [.var "n", .const (num 0)]) (.var "acc")
      (.self [.prim "-" [.var "n", .const (num 1)], .prim "+" [.var "acc", .const (num 1)]])⟩]
  | "top" => [⟨[], .prim "+" [.const (num 1), .enter "cnt" [.const (num 3), .const (num 0)]]⟩]
  | _ => []

/-- No range is proved: `cnt` returns `$acc`, which its formal does not check. -/
def noProof : String → Bool := fun _ => false

theorem cntRows_some {h : String} {As : List (Ty Empty)} {R : Ty Empty}
    (hrow : cntRows h = some (As, R)) :
    h = "cnt" ∧ As = [.sym "Number", undefinedTy] ∧ R = .sym "Number" := by
  unfold cntRows at hrow
  split at hrow
  · cases hrow
    exact ⟨rfl, rfl, rfl⟩
  · cases hrow

theorem undefined_unchecked : demand (undefinedTy : Ty Empty).lift ≠ .guarded := by
  simp [demand, undefinedTy, Ty.lift, Unchecked]

/-- **The counter and its caller are accepted**: `cnt` calls itself in a tail
position at a number, `top` calls the typed `cnt` outside a tail position at a
number, and `cnt` owes `Number`. -/
theorem cnt_accepted :
    ProgramAccepted cntRows noProof cntEqs decls cntRes cntEnt (.sym "Number") where
  entRows h As R hrow := by
    obtain ⟨rfl, rfl, rfl⟩ := cntRows_some hrow
    rfl
  resRows h As R hrow := by
    obtain ⟨rfl, rfl, rfl⟩ := cntRows_some hrow
    rfl
  guarded h As R hrow := by
    obtain ⟨rfl, rfl, rfl⟩ := cntRows_some hrow
    exact number_guarded
  owing h As R hrow _ := (cntRows_some hrow).2.2
  provesTyped h hp := by simp [noProof] at hp
  linear h eq member := by
    unfold cntEqs at member
    split at member
    · simp only [List.mem_singleton] at member
      subst member
      decide
    · simp only [List.mem_singleton] at member
      subst member
      decide
    · simp at member
  calls h eq member := by
    unfold cntEqs at member
    split at member
    · simp only [List.mem_singleton] at member
      subst member
      refine .ifE (.prim fun e he => ?_) .var (CallsOK.selfGuarded (fun e he => ?_) ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact .var
        · exact .const
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> refine .prim fun e' he' => ?_ <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he' <;>
          rcases he' with rfl | rfl <;> first | exact .var | exact .const
      · exact .cons (fun _ => .prim rfl) (.cons (fun hg => absurd hg undefined_unchecked) .nil)
    · simp only [List.mem_singleton] at member
      subst member
      refine .prim fun e he => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact .const
      · refine .enter (fun e' he' => ?_) ?_
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
          rcases he' with rfl | rfl <;> exact .const
        · exact .cons (fun _ => .const (count_int decls 3))
            (.cons (fun hg => absurd hg undefined_unchecked) .nil)
    · simp at member
  tail h eq member := by
    unfold cntEqs at member
    split at member
    · simp only [List.mem_singleton] at member
      subst member
      exact .ifE (by simp [CallsTyped, CallsTypedAll]) (.plain trivial)
        (.self (by simp [CallsTyped, CallsTypedAll]))
    · simp only [List.mem_singleton] at member
      subst member
      exact .plain (by simp [CallsTyped, CallsTypedAll, typedHead, cntRows])
    · simp at member
  proven h hp := by simp [noProof] at hp

/-- **The machine runs the counter's caller as its protocol does**, at every
fuel, by the analysis alone. -/
theorem cnt_machine (grounded : String → Bool) (n : ℕ) :
    machineRunS decls grounded (oweOf cntRows noProof) (stepsOf env cntEqs) n
        (oweOf cntRows noProof "top" []) "top" [] =
      protocolRunS decls grounded (sigOf cntRows) (stepsOf env cntEqs) n "top" [] :=
  program_machine_eq_protocol decls_functional (env_ok grounded cntRes) cnt_accepted n "top" []
    (by simp [cntEnt, EntryFacts])

/-- `(: g (-> Number Number))`; `helper` and `f` are untyped. -/
def argRows : String → Option (List (Ty Empty) × Ty Empty)
  | "g" => some ([.sym "Number"], .sym "Number")
  | _ => none

/-- `(= (g $x) 5)`, `(= (helper) "s")` and `(= (f) (g (helper)))`. -/
def argEqs : String → List Equation
  | "g" => [⟨[.var "x"], .const (num 5)⟩]
  | "helper" => [⟨[], .const (str "s")⟩]
  | "f" => [⟨[], .enter "g" [.enter "helper" []]⟩]
  | _ => []

/-- **A call into an untyped head outside a tail position breaks the entry
facts**: `f`'s tail call to the typed `g` takes its argument from the untyped
`helper`, which may answer `"s"` while every typed head's answers meet their
facts, so the call is made where `g`'s entry fact fails; the analysis rejects
`f`'s right-hand side. -/
theorem untyped_argument_breaks (grounded : String → Bool) :
    ∃ P : String → List Atom → Multiset Atom, AnswersMeet decls grounded (sigOf argRows) P ∧
      (.inr ("g", [str "s"]) : Atom ⊕ (String × List Atom)) ∈ stepsOf env argEqs "f" P [] ∧
      ¬ EntryFacts decls grounded [.sym "Number"] [str "s"] ∧
      ¬ TailOut (typedHead argRows) (typedHead argRows "f") (.enter "g" [.enter "helper" []]) := by
  refine ⟨fun h _ => if h = "helper" then {str "s"} else 0, ?_, ?_, ?_, ?_⟩
  · intro g ws T R sig _ r member
    by_cases helper : g = "helper"
    · subst helper
      simp [sigOf, argRows] at sig
    · simp [helper] at member
  · simp [stepsOf, argEqs, Pat.matchAll, Expr.evalOut, Expr.evalAll, Expr.eval, oracleOf]
  · intro entry
    cases entry with
    | cons fact _ =>
        have holds := fact (by simp [demand, Ty.lift, Unchecked])
        unfold Holds at holds
        rw [if_neg (by simp [MetaName]), count_class decls (g := .string "s") rfl] at holds
        simp at holds
  · intro tail
    cases tail with
    | plain h => simp [CallsTyped, CallsTypedAll, typedHead, argRows] at h
    | enter h => simp [CallsTyped, CallsTypedAll, typedHead, argRows] at h

end Controls


end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls
