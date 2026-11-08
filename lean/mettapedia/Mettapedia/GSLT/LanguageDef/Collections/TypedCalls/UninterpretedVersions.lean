import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Polymorphic
import Mettapedia.Logic.LP.UnificationRestriction

/-!
# Uninterpreted versions from the analysis
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Atoms as first-order terms -/

namespace UnifyAtoms

/-- The leaves of atoms: symbols and grounded values. -/
inductive Leaf where
  | sym (s : String)
  | gnd (g : GroundedValue)
  deriving DecidableEq

/-- Atoms as first-order terms: leaves are constants, variables are named by
strings, and an expression of `n` elements applies the function symbol `n`. -/
abbrev sig : Mettapedia.Logic.LP.LPSignature where
  constants := Leaf
  vars := String
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := ℕ
  functionArity := fun n => n

instance : DecidableEq sig.vars := inferInstanceAs (DecidableEq String)
instance : DecidableEq sig.constants := inferInstanceAs (DecidableEq Leaf)
instance : DecidableEq sig.functionSymbols := inferInstanceAs (DecidableEq ℕ)

open Mettapedia.Logic.LP (Term Subst)

/-- An atom as a term. -/
def encode : Atom → Term sig
  | .var x => .var x
  | .symbol s => .const (.sym s)
  | .grounded g => .const (.gnd g)
  | .expression es => .app (f := (es.length : ℕ)) fun i => encode (es.get i)
termination_by a => sizeOf a
decreasing_by
  have := List.sizeOf_lt_of_mem (List.get_mem es i)
  simp only [Atom.expression.sizeOf_spec]
  omega

/-- A term as an atom. -/
def decode : Term sig → Atom
  | .var x => .var x
  | .const (.sym s) => .symbol s
  | .const (.gnd g) => .grounded g
  | .app n children => .expression (List.ofFn fun i : Fin n => decode (children i))

theorem encode_expression (es : List Atom) :
    encode (.expression es) = .app (f := (es.length : ℕ)) fun i => encode (es.get i) := by
  rw [encode]

theorem decode_encode (a : Atom) : decode (encode a) = a := by
  induction a using Atom.rec (motive_2 := fun es => ∀ a ∈ es, decode (encode a) = a) with
  | var _ => rw [encode]; rfl
  | symbol _ => rw [encode]; rfl
  | grounded _ => rw [encode]; rfl
  | expression es ih =>
      rw [encode_expression]
      show Atom.expression (List.ofFn fun i : Fin es.length => decode (encode (es.get i))) = _
      congr 1
      apply List.ext_get (by simp)
      intro n h₁ h₂
      simp only [List.get_ofFn]
      exact ih _ (List.get_mem es _)
  | nil a member => cases member
  | cons head tail headIh tailIh a member =>
      rcases List.mem_cons.mp member with rfl | member
      · exact headIh
      · exact tailIh a member

theorem substL_eq_map (θ : String → Atom) : ∀ es : List Atom, substL θ es = es.map (substA θ)
  | [] => by rw [substL]; rfl
  | e :: es => by rw [substL, substL_eq_map θ es]; rfl

/-- **Substitution commutes with the encoding**: a term substitution applied to
an atom's term is, read back, the atom's instance under the read-back
substitution. -/
theorem decode_applyTerm (θ : Subst sig) (a : Atom) :
    decode (θ.applyTerm (encode a)) = substA (fun x => decode (θ x)) a := by
  induction a using Atom.rec (motive_2 := fun es => ∀ a ∈ es,
      decode (θ.applyTerm (encode a)) = substA (fun x => decode (θ x)) a) with
  | var _ => rw [encode, substA]; rfl
  | symbol _ => rw [encode, substA]; rfl
  | grounded _ => rw [encode, substA]; rfl
  | expression es ih =>
      rw [encode_expression, substA, substL_eq_map]
      show Atom.expression (List.ofFn fun i : Fin es.length =>
        decode (θ.applyTerm (encode (es.get i)))) = _
      congr 1
      apply List.ext_get (by simp)
      intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_ofFn, List.getElem_map]
      exact ih _ (List.getElem_mem _)
  | nil a member => cases member
  | cons head tail headIh tailIh a member =>
      rcases List.mem_cons.mp member with rfl | member
      · exact headIh
      · exact tailIh a member

variable (Γ : Decls)

/-- A leaf the declarations do not interpret: a symbol with no row, or a
grounded value. -/
def Undeclared : Leaf → Prop
  | .sym s => Γ s = []
  | .gnd _ => True

instance : DecidablePred (Undeclared Γ) := fun leaf => by
  cases leaf <;> unfold Undeclared <;> infer_instance

open Mettapedia.Logic.LP.UnificationRestriction (Respect)

variable {Γ}

theorem safeAll_of_uninterp {es : List Atom} (h : Uninterp Γ (.expression es)) :
    SafeAll Γ Atom.var es := by
  cases es with
  | nil => trivial
  | cons e es => exact ⟨h.2.1, h.2.2⟩

theorem uninterp_of_all : ∀ {es : List Atom}, (∀ a ∈ es, Uninterp Γ a) → Uninterp Γ (.expression es)
  | [], _ => trivial
  | e :: es, each => by
      refine ⟨?_, each e (by simp), ?_⟩
      · rw [substA_var_self]
        cases e with
        | var _ => trivial
        | _ => exact headFree_of_safe (each _ (by simp)) (by simp)
      · have rest : ∀ a ∈ es, Uninterp Γ a := fun a member => each a (by simp [member])
        clear each
        induction es with
        | nil => trivial
        | cons e' es' ih => exact ⟨rest e' (by simp), ih fun a member => rest a (by simp [member])⟩

/-- **An uninterpreted atom's term has undeclared leaves only.** -/
theorem respect_encode (a : Atom) (h : Uninterp Γ a) : Respect (Undeclared Γ) (encode a) := by
  induction a using Atom.rec (motive_2 := fun es => SafeAll Γ Atom.var es →
      ∀ a ∈ es, Respect (Undeclared Γ) (encode a)) with
  | var _ => rw [encode]; trivial
  | symbol s => rw [encode]; exact h
  | grounded _ => rw [encode]; trivial
  | expression es ih =>
      rw [encode_expression]
      intro i
      exact ih (safeAll_of_uninterp h) _ (List.get_mem es i)
  | nil _ a member => cases member
  | cons head tail headIh tailIh safe a member =>
      rcases List.mem_cons.mp member with rfl | member
      · exact headIh safe.1
      · exact tailIh safe.2 a member

/-- **A term with undeclared leaves only reads back as an uninterpreted atom.** -/
theorem uninterp_decode : ∀ t : Term sig, Respect (Undeclared Γ) t → Uninterp Γ (decode t)
  | .var _, _ => trivial
  | .const (.sym _), h => h
  | .const (.gnd _), _ => trivial
  | .app n children, h => by
      show Uninterp Γ (.expression (List.ofFn fun i : Fin n => decode (children i)))
      apply uninterp_of_all
      intro a member
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
      exact uninterp_decode (children i) (h i)

open Mettapedia.Logic.LP (unifyTotal)

/-- **Two-way unification of two atoms**: the most general unifier of their
terms, binding the variables of both. -/
def unify (p v : Atom) : Option (Subst sig) := unifyTotal [(encode p, encode v)]

/-- A substitution of terms, read back as one of atoms. -/
def readBack (θ : Subst sig) : String → Atom := fun x => decode (θ x)

/-- **A unifier leaves both atoms the same instance.** -/
theorem unify_instance {p v : Atom} {θ : Subst sig} (h : unify p v = some θ) :
    substA (readBack θ) p = substA (readBack θ) v := by
  have sound := Mettapedia.Logic.LP.unifyTotal_sound _ θ h (encode p, encode v) (by simp)
  unfold readBack
  rw [← decode_applyTerm, ← decode_applyTerm]
  exact congrArg decode sound

/-- **Unifying uninterpreted atoms binds uninterpreted values**: the most general
unifier introduces no leaf its inputs lack. -/
theorem unify_uninterp {p v : Atom} {θ : Subst sig} (h : unify p v = some θ)
    (hp : Uninterp Γ p) (hv : Uninterp Γ v) : ∀ x, Uninterp Γ (readBack θ x) := by
  intro x
  apply uninterp_decode
  refine Mettapedia.Logic.LP.UnificationRestriction.unifyTotal_respects (σ := sig)
    (Undeclared Γ) (Leaf.gnd (.int 0)) trivial [(encode p, encode v)] θ h ?_ x
  intro equation member
  rw [List.mem_singleton] at member
  subst member
  exact ⟨respect_encode p hp, respect_encode v hv⟩

end UnifyAtoms

/-! ## Patterns as atoms and as right-hand sides -/

namespace Pat

mutual
/-- A pattern as an atom: its variables are the atom's. -/
def toAtom : Pat → Atom
  | .var x => .var x
  | .const a => a
  | .ctor c ps => .expression (.symbol c :: toAtoms ps)

/-- Patterns as atoms. -/
def toAtoms : List Pat → List Atom
  | [] => []
  | p :: ps => toAtom p :: toAtoms ps
end

mutual
/-- A pattern as a right-hand side: the term that builds it. -/
def toExpr : Pat → Expr
  | .var x => .var x
  | .const a => .const a
  | .ctor c ps => .ctor c (toExprs ps)

/-- Patterns as right-hand sides. -/
def toExprs : List Pat → List Expr
  | [] => []
  | p :: ps => toExpr p :: toExprs ps
end

mutual
/-- Every constant of the pattern is a ground atom. -/
def GroundConsts : Pat → Prop
  | .var _ => True
  | .const a => substA Atom.var a = a ∧ ∀ θ : String → Atom, substA θ a = a
  | .ctor _ ps => GroundConstsAll ps

/-- Every constant of the patterns is a ground atom. -/
def GroundConstsAll : List Pat → Prop
  | [] => True
  | p :: ps => GroundConsts p ∧ GroundConstsAll ps
end

mutual
/-- **A pattern evaluated as a right-hand side is its instance** under bindings
of its variables. -/
theorem eval_toExpr (E : Env) (O : Oracle) (ρ : List (String × Atom)) (θ : String → Atom) :
    ∀ p : Pat, GroundConsts p → (∀ x ∈ vars p, ρ.lookup x = some (θ x)) →
      (toExpr p).eval E O ρ = {substA θ (toAtom p)}
  | .var x, _, bound => by
      simp only [toExpr, toAtom, Expr.eval, substA, bound x (by simp [vars])]
  | .const a, ⟨_, ground⟩, _ => by
      simp only [toExpr, toAtom, Expr.eval, ground θ]
  | .ctor c ps, ground, bound => by
      simp only [toExpr, toAtom, Expr.eval, substA, substL]
      rw [evalAll_toExprs E O ρ θ ps ground fun x member => bound x (by simpa [vars] using member)]
      simp

/-- The list version. -/
theorem evalAll_toExprs (E : Env) (O : Oracle) (ρ : List (String × Atom)) (θ : String → Atom) :
    ∀ ps : List Pat, GroundConstsAll ps → (∀ x ∈ varsAll ps, ρ.lookup x = some (θ x)) →
      Expr.evalAll E O ρ (toExprs ps) = {substL θ (toAtoms ps)}
  | [], _, _ => by simp [toExprs, toAtoms, Expr.evalAll, substL]
  | p :: ps, ⟨gp, gps⟩, bound => by
      simp only [toExprs, toAtoms, Expr.evalAll, substL]
      rw [eval_toExpr E O ρ θ p gp fun x member => bound x (by simp [varsAll, member]),
        evalAll_toExprs E O ρ θ ps gps fun x member => bound x (by simp [varsAll, member])]
      simp
end

end Pat

/-! ## Right-hand sides that return the argument's pattern -/

/-- **A right-hand side that returns a pattern** (`contract_returns_argument`,
`contract_returns_pattern`): the pattern itself, or a `let`, an `if`, a `case`
or a `match` whose every tail returns it, or `(empty)`. -/
inductive ReturnsPat (pe : Expr) : Expr → Prop
  | refl : ReturnsPat pe pe
  | letE {q : Pat} {v b : Expr} : ReturnsPat pe b → ReturnsPat pe (.letE q v b)
  | ifE {c t e : Expr} : ReturnsPat pe t → ReturnsPat pe e → ReturnsPat pe (.ifE c t e)
  | empty : ReturnsPat pe .empty
  | caseE {k : Expr} {ps : List Pat} {bs : List Expr} : (∀ b ∈ bs, ReturnsPat pe b) →
      ReturnsPat pe (.caseE k ps bs)
  | matchE {src : Expr} {q : Pat} {t : Expr} : ReturnsPat pe t → ReturnsPat pe (.matchE src q t)

/-- Bindings that keep every binding of others. -/
def Keeps (ρ ρ' : List (String × Atom)) : Prop := ∀ x w, ρ.lookup x = some w → ρ'.lookup x = some w

theorem Keeps.refl (ρ : List (String × Atom)) : Keeps ρ ρ := fun _ _ h => h

theorem Keeps.trans {ρ ρ' ρ'' : List (String × Atom)} (h : Keeps ρ ρ') (h' : Keeps ρ' ρ'') :
    Keeps ρ ρ'' := fun x w hx => h' x w (h x w hx)

theorem Keeps.matchUnder {ρ ρ' : List (String × Atom)} {q : Pat} {w : Atom}
    (h : Pat.matchUnder ρ q w = some ρ') : Keeps ρ ρ' :=
  fun _ _ hx => Pat.matchUnder_lookup h hx

theorem evalArms_returns {value : Atom} (E : Env) (O : Oracle) (ρ₀ : List (String × Atom))
    (w : Atom) : ∀ (ps : List Pat) (bs : List Expr),
      (∀ b ∈ bs, ∀ ρ, Keeps ρ₀ ρ → ∀ r ∈ b.eval E O ρ, r = value) →
      ∀ ρ, Keeps ρ₀ ρ → ∀ r ∈ Expr.evalArms E O ρ w ps bs, r = value
  | p :: ps, b :: bs, each, ρ, keeps, r, member => by
      simp only [Expr.evalArms] at member
      split at member
      · next ρ' hm => exact each b (by simp) ρ' (keeps.trans (Keeps.matchUnder hm)) r member
      · exact evalArms_returns E O ρ₀ w ps bs (fun b' m => each b' (by simp [m])) ρ keeps r member
  | [], _, _, _, _, r, member => by simp [Expr.evalArms] at member
  | _ :: _, [], _, _, _, r, member => by simp [Expr.evalArms] at member

/-- **Every answer of a right-hand side that returns a pattern is the pattern's
value**, whatever the oracle answers, when the pattern has one value under every
extension of the bindings. -/
theorem eval_returns {pe e : Expr} {value : Atom} (E : Env) (O : Oracle)
    (ρ₀ : List (String × Atom)) (fixed : ∀ ρ', Keeps ρ₀ ρ' → pe.eval E O ρ' = {value})
    (returns : ReturnsPat pe e) :
    ∀ ρ, Keeps ρ₀ ρ → ∀ r ∈ e.eval E O ρ, r = value := by
  induction returns with
  | refl =>
      intro ρ keeps r member
      rw [fixed ρ keeps, Multiset.mem_singleton] at member
      exact member
  | @letE q v b _ ih =>
      intro ρ keeps r member
      simp only [Expr.eval, Multiset.mem_bind] at member
      obtain ⟨w, _, member⟩ := member
      split at member
      · next ρ' hm => exact ih ρ' (keeps.trans (Keeps.matchUnder hm)) r member
      · exact absurd member (Multiset.notMem_zero r)
  | ifE _ _ iht ihe =>
      intro ρ keeps r member
      simp only [Expr.eval, Multiset.mem_bind] at member
      obtain ⟨w, _, member⟩ := member
      split at member
      · exact iht ρ keeps r member
      · exact ihe ρ keeps r member
  | empty =>
      intro ρ _ r member
      simp [Expr.eval] at member
  | @caseE k ps bs returns ih =>
      intro ρ keeps r member
      simp only [Expr.eval, Multiset.mem_bind] at member
      obtain ⟨w, _, member⟩ := member
      exact evalArms_returns E O ρ₀ w ps bs ih ρ keeps r member
  | @matchE src q t _ ih =>
      intro ρ keeps r member
      simp only [Expr.eval, Multiset.mem_bind] at member
      obtain ⟨sp, _, row, _, member⟩ := member
      split at member
      · next ρ' hm => exact ih ρ' (keeps.trans (Keeps.matchUnder hm)) r member
      · exact absurd member (Multiset.notMem_zero r)


/-! ## Calls to itself at uninterpreted arguments -/

section Calls

variable (Γ : Decls) (res : String → Ty Empty) (ent : String → List (Ty Empty))

/-- **The calls of a right-hand side of a relation with an uninterpreted
parameter**: a part without calls to itself makes its other calls as `CallsOK`
checks; a call to itself has closed arguments without calls to itself, typed at
the closed formals, and at the uninterpreted parameter a variable bound to an
uninterpreted value, one of `Ψ`; `let`, `if` and `case` combine such parts. -/
inductive UnintCalls (Φ : String → Ty Empty → Prop) (R : Ty Empty) (pre post : List (Ty Empty))
    (Ψ : List String) : Expr → Prop
  | plain {e : Expr} : NoSelf e → CallsOK Γ res ent Φ R [] e → UnintCalls Φ R pre post Ψ e
  | self {us ws : List Expr} {w : String} :
      (∀ e ∈ us ++ ws, NoSelf e ∧ CallsOK Γ res ent Φ R [] e) →
      List.Forall₂ (fun A e => demand A.lift = .guarded → HasType Γ res Φ R e A) pre us →
      w ∈ Ψ →
      List.Forall₂ (fun A e => demand A.lift = .guarded → HasType Γ res Φ R e A) post ws →
      UnintCalls Φ R pre post Ψ (.self (us ++ .var w :: ws))
  | letE {p : Pat} {v b : Expr} : UnintCalls Φ R pre post Ψ v → UnintCalls Φ R pre post Ψ b →
      UnintCalls Φ R pre post Ψ (.letE p v b)
  | ifE {c t e : Expr} : UnintCalls Φ R pre post Ψ c → UnintCalls Φ R pre post Ψ t →
      UnintCalls Φ R pre post Ψ e → UnintCalls Φ R pre post Ψ (.ifE c t e)
  | caseE {k : Expr} {ps : List Pat} {bs : List Expr} : UnintCalls Φ R pre post Ψ k →
      (∀ b ∈ bs, UnintCalls Φ R pre post Ψ b) → UnintCalls Φ R pre post Ψ (.caseE k ps bs)

end Calls

section CallsSoundness

variable {Γ : Decls} {grounded : String → Bool} {res : String → Ty Empty}
  {ent : String → List (Ty Empty)} {Φ : String → Ty Empty → Prop} {R : Ty Empty}
  {pre post : List (Ty Empty)} {Ψ : List String} {E : Env}

theorem mem_evalAll_append (E : Env) (O : Oracle) (ρ : List (String × Atom)) :
    ∀ (es₁ es₂ : List Expr) (vs : List Atom), vs ∈ Expr.evalAll E O ρ (es₁ ++ es₂) →
      ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧ vs₁ ∈ Expr.evalAll E O ρ es₁ ∧ vs₂ ∈ Expr.evalAll E O ρ es₂
  | [], es₂, vs, member => ⟨[], vs, rfl, by simp [Expr.evalAll], member⟩
  | e :: es₁, es₂, vs, member => by
      simp only [List.cons_append, Expr.evalAll, Multiset.mem_bind, Multiset.mem_map] at member
      obtain ⟨v, hv, vs', hvs', rfl⟩ := member
      obtain ⟨vs₁, vs₂, rfl, h₁, h₂⟩ := mem_evalAll_append E O ρ es₁ es₂ vs' hvs'
      refine ⟨v :: vs₁, vs₂, rfl, ?_, h₂⟩
      simp only [Expr.evalAll, Multiset.mem_bind, Multiset.mem_map]
      exact ⟨v, hv, vs₁, h₁, rfl⟩

/-- The oracle that calls nothing of itself, with the callees' versions. -/
theorem oracleOK_noSelf (enP enV : String → List Atom → Multiset Atom)
    (enAgree : ∀ f ws, EntryFacts Γ grounded (ent f) ws → enP f ws = enV f ws)
    (enRes : ∀ f ws, EntryFacts Γ grounded (ent f) ws → ∀ r ∈ enV f ws, Holds Γ grounded r (res f)) :
    OracleOK Γ grounded res ent [] R ⟨fun _ => 0, enP⟩ where
  self _ _ r member := absurd member (Multiset.notMem_zero r)
  enter f ws entry r member := enRes f ws entry r (by rw [← enAgree f ws entry]; exact member)

/-- **A part without calls to itself has the same values under the protocol's
and the version's oracles.** -/
theorem eval_plain_congr (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E)
    {o o' : List Atom → Multiset Atom} {enP enV : String → List Atom → Multiset Atom}
    (enAgree : ∀ f ws, EntryFacts Γ grounded (ent f) ws → enP f ws = enV f ws)
    (enRes : ∀ f ws, EntryFacts Γ grounded (ent f) ws → ∀ r ∈ enV f ws, Holds Γ grounded r (res f))
    {e : Expr} (noSelf : NoSelf e) (calls : CallsOK Γ res ent Φ R [] e)
    {ρ : List (String × Atom)} (facts : MeetsFacts Γ grounded Φ ρ) :
    e.eval E ⟨o, enP⟩ ρ = e.eval E ⟨o', enV⟩ ρ := by
  rw [eval_noSelf E enP o (fun _ => 0) e ρ noSelf, eval_noSelf E enV o' (fun _ => 0) e ρ noSelf]
  exact eval_congr hΓ hE (O' := ⟨fun _ => 0, enV⟩) (oracleOK_noSelf enP enV enAgree enRes)
    ⟨fun _ _ => rfl, enAgree⟩ e ρ facts calls

theorem evalArms_unint_congr {O O' : Oracle} {P : List (String × Atom) → Prop}
    (w : Atom) (keep : ∀ ρ ρ' q, P ρ → Pat.matchUnder ρ q w = some ρ' → P ρ') :
    ∀ (ps : List Pat) (bs : List Expr) (ρ : List (String × Atom)), P ρ →
      (∀ b ∈ bs, ∀ ρ', P ρ' → b.eval E O ρ' = b.eval E O' ρ') →
      Expr.evalArms E O ρ w ps bs = Expr.evalArms E O' ρ w ps bs
  | p :: ps, b :: bs, ρ, hρ, hbs => by
      simp only [Expr.evalArms]
      split
      · next ρ' hm => exact hbs b (by simp) ρ' (keep ρ ρ' p hρ hm)
      · exact evalArms_unint_congr w keep ps bs ρ hρ fun b' m => hbs b' (by simp [m])
  | [], _, _, _, _ => by simp [Expr.evalArms]
  | _ :: _, [], _, _, _ => by simp [Expr.evalArms]

/-- **The calls to itself are made at uninterpreted arguments only**, so the
protocol's and the version's oracles, which agree there, give the same values. -/
theorem eval_unint_congr (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E)
    {o o' : List Atom → Multiset Atom} {enP enV : String → List Atom → Multiset Atom}
    (enAgree : ∀ f ws, EntryFacts Γ grounded (ent f) ws → enP f ws = enV f ws)
    (enRes : ∀ f ws, EntryFacts Γ grounded (ent f) ws → ∀ r ∈ enV f ws, Holds Γ grounded r (res f))
    (agree : ∀ ws, UnintEntry Γ grounded pre post ws → o ws = o' ws) {e : Expr}
    (calls : UnintCalls Γ res ent Φ R pre post Ψ e) :
    ∀ ρ, MeetsFacts Γ grounded Φ ρ → (∀ w ∈ Ψ, ∃ a, ρ.lookup w = some a ∧ Uninterp Γ a) →
      e.eval E ⟨o, enP⟩ ρ = e.eval E ⟨o', enV⟩ ρ := by
  induction calls with
  | plain noSelf callsOK =>
      intro ρ facts _
      exact eval_plain_congr hΓ hE enAgree enRes noSelf callsOK facts
  | @self us ws w parts typedPre named typedPost =>
      intro ρ facts unint
      have argsSame : Expr.evalAll E ⟨o, enP⟩ ρ (us ++ .var w :: ws) =
          Expr.evalAll E ⟨o', enV⟩ ρ (us ++ .var w :: ws) := by
        apply Expr.evalAll_congr
        intro e member
        rcases List.mem_append.mp member with member | member
        · exact eval_plain_congr hΓ hE enAgree enRes (parts e (by simp [member])).1
            (parts e (by simp [member])).2 facts
        · rcases List.mem_cons.mp member with rfl | member
          · rfl
          · exact eval_plain_congr hΓ hE enAgree enRes (parts e (by simp [member])).1
              (parts e (by simp [member])).2 facts
      simp only [Expr.eval]
      rw [argsSame]
      refine Multiset.bind_congr fun vs member => agree vs ?_
      have noSelfArgs : NoSelfAll (us ++ .var w :: ws) := by
        rw [noSelfAll_iff]
        intro e member
        rcases List.mem_append.mp member with member | member
        · exact (parts e (by simp [member])).1
        · rcases List.mem_cons.mp member with rfl | member
          · trivial
          · exact (parts e (by simp [member])).1
      rw [evalAll_noSelf E enV o' (fun _ => 0) _ ρ noSelfArgs] at member
      obtain ⟨vs₁, rest, rfl, h₁, hrest⟩ := mem_evalAll_append E _ ρ us (.var w :: ws) vs member
      simp only [Expr.evalAll, Multiset.mem_bind, Multiset.mem_map] at hrest
      obtain ⟨a, ha, vs₂, h₂, rfl⟩ := hrest
      obtain ⟨a', lookup, unintA⟩ := unint w named
      simp only [Expr.eval, lookup, Multiset.mem_singleton] at ha
      subst a
      have hO := oracleOK_noSelf (Γ := Γ) (grounded := grounded) (R := R) enV enV
        (fun _ _ _ => rfl) enRes
      have sound := evalAll_sound hΓ hE (Φ := Φ) hO us ρ facts
      have sound₂ := evalAll_sound hΓ hE (Φ := Φ) hO ws ρ facts
      refine ⟨vs₁, a', vs₂, rfl, typedPre.length_eq.trans
        (List.Forall₂.length_eq (Expr.evalAll_mem E _ ρ us vs₁ h₁)), ?_, unintA, ?_⟩
      · exact forall₂_compose typedPre (Expr.evalAll_mem E _ ρ us vs₁ h₁)
          fun A e v he hA hv hg => List.forall_iff_forall_mem.mp sound e he A (hA hg)
            (parts e (by simp [he])).2 v hv
      · exact forall₂_compose typedPost (Expr.evalAll_mem E _ ρ ws vs₂ h₂)
          fun A e v he hA hv hg => List.forall_iff_forall_mem.mp sound₂ e he A (hA hg)
            (parts e (by simp [he])).2 v hv
  | letE _ _ ihv ihb =>
      intro ρ facts unint
      simp only [Expr.eval]
      rw [ihv ρ facts unint]
      refine Multiset.bind_congr fun w _ => ?_
      split
      · next ρ' hm =>
          exact ihb ρ' (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) fun x member => by
            obtain ⟨a, lookup, ua⟩ := unint x member
            exact ⟨a, Pat.matchUnder_lookup hm lookup, ua⟩
      · rfl
  | ifE _ _ _ ihc iht ihe =>
      intro ρ facts unint
      simp only [Expr.eval]
      rw [ihc ρ facts unint, iht ρ facts unint, ihe ρ facts unint]
  | @caseE k ps bs _ _ ihk ihbs =>
      intro ρ facts unint
      simp only [Expr.eval]
      rw [ihk ρ facts unint]
      refine Multiset.bind_congr fun w _ => ?_
      exact evalArms_unint_congr (P := fun ρ => MeetsFacts Γ grounded Φ ρ ∧
          ∀ w ∈ Ψ, ∃ a, ρ.lookup w = some a ∧ Uninterp Γ a) w
        (fun ρ ρ' q hρ hm => ⟨hρ.1.extend fun x w hx => Pat.matchUnder_lookup hm hx,
          fun x member => by
            obtain ⟨a, lookup, ua⟩ := hρ.2 x member
            exact ⟨a, Pat.matchUnder_lookup hm lookup, ua⟩⟩)
        ps bs ρ ⟨facts, unint⟩ fun b member ρ' hρ' => ihbs b member ρ' hρ'.1 hρ'.2

end CallsSoundness


end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls
