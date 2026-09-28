import Mettapedia.GSLT.Parsing.CanonicalGrammar
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Typing

/-!
# Morphisms of canonical terms, admitted as deterministic equations

A morphism interprets canonical terms by a deterministic-equation program.
Its head takes a policy and a canonical value, and the program has exactly one
equation of the head for each form a canonical value takes and each policy:
a node by its name and number of children, a literal by its text.  A node's
value pattern binds the node's children to variables; a policy pattern is a
variable (every policy) or one policy's symbol.  The loader admits the
program only with a descent certificate.

Then a call of the head on a canonical term of a declared form selects that
form's one equation for the policy, and no equation of another form can take
the call: there is no fallback (`select_form`, `select_unique`); the call is
that equation's right side under the match (`apply_form`); and it ends
(`morphism_ends`). Under a typing of the program whose argument sorts hold
the policy and the canonical value, the call returns a value of the result
sort (`morphism_returns`), for the canonical value of every derivation
(`canon_returns`).  The last section carries this through for a recursive
morphism on a checked grammar.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.CanonicalMorphism

open Mettapedia.GSLT.Parsing.CanonicalGrammar
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

mutual

/-- A canonical term as a value: a node is the expression
`(bnf name children…)`, a text a literal atom, and the list inside a list node
a list value. -/
def encode : CanonicalTerm → Term
  | .node name cs => .expr (.sym "bnf" :: .sym name :: encodeList cs)
  | .text s => .lit s
  | .seq es => .list (encodeList es)

/-- A list of canonical terms as values. -/
def encodeList : List CanonicalTerm → List Term
  | [] => []
  | c :: cs => encode c :: encodeList cs

end

theorem encodeList_length : ∀ cs : List CanonicalTerm, (encodeList cs).length = cs.length
  | [] => rfl
  | _ :: cs => by simp [encodeList, encodeList_length cs]

/-- The forms a morphism interprets. -/
inductive Form where
  | node (name : String) (arity : Nat)
  | literal (text : String)
  deriving DecidableEq, Repr

/-- The form of a canonical term: a node's name and number of children, or a
literal's text.  The list inside a list node is interpreted with its node. -/
def formOf : CanonicalTerm → Option Form
  | .node name cs => some (.node name cs.length)
  | .text s => some (.literal s)
  | .seq _ => none

/-- A value pattern interprets a form: a node's pattern names it and binds each
child to a variable; a literal's pattern is its text. -/
inductive Interprets : Term → Form → Prop where
  | node (name : String) (xs : List String) :
      Interprets (.expr (.sym "bnf" :: .sym name :: xs.map .var)) (.node name xs.length)
  | literal (s : String) : Interprets (.lit s) (.literal s)

/-- A policy pattern takes a policy: a variable takes every policy, a symbol
its own. -/
inductive Takes : Term → String → Prop where
  | every (p s : String) : Takes (.var p) s
  | own (s : String) : Takes (.sym s) s

/-- A morphism of head `f` admitted against a list of forms.  The program
descends; every equation of the head takes a policy pattern and a value
pattern interpreting a declared form; every declared form has an equation for
every policy; and two equations of the head interpreting one form for one
policy are one equation. -/
structure Admitted (P : Program) (V : Vocabulary) (c : Certificate) (f : String)
    (forms : List Form) : Prop where
  descends : Descends P V c
  shape : ∀ e ∈ P, e.head = f → ∃ pol val φ, e.params = [pol, val] ∧
    ((∃ p, pol = .var p) ∨ ∃ s, pol = .sym s) ∧ Interprets val φ ∧ φ ∈ forms
  covers : ∀ φ ∈ forms, ∀ s, ∃ e ∈ P, e.head = f ∧
    ∃ pol val, e.params = [pol, val] ∧ Takes pol s ∧ Interprets val φ
  one_each : ∀ e₁ ∈ P, ∀ e₂ ∈ P, e₁.head = f → e₂.head = f →
    ∀ s pol₁ val₁ pol₂ val₂ φ, e₁.params = [pol₁, val₁] → e₂.params = [pol₂, val₂] →
      Takes pol₁ s → Takes pol₂ s → Interprets val₁ φ → Interprets val₂ φ → e₁ = e₂

/-! ## Matching values against form patterns -/

theorem matchTerms_vars : ∀ (xs : List String) (vs : List Term), xs.length = vs.length →
    ∃ σ, matchTerms (xs.map .var) vs = some σ
  | [], [], _ => ⟨[], rfl⟩
  | x :: xs, v :: vs, h => by
    obtain ⟨σ, hσ⟩ := matchTerms_vars xs vs (Nat.succ.inj h)
    refine ⟨[(x, v)] ++ σ, ?_⟩
    show matchTerms (.var x :: xs.map .var) (v :: vs) = _
    rw [matchTerms, matchTerm, hσ]
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

/-- A value pattern of a form matches the value of every term of that form. -/
theorem interprets_match {val : Term} {φ : Form} (hi : Interprets val φ) {c : CanonicalTerm}
    (hc : formOf c = some φ) : ∃ σ, matchTerm val (encode c) = some σ := by
  cases hi with
  | node name xs =>
    cases c with
    | node name' cs =>
      simp only [formOf, Option.some.injEq, Form.node.injEq] at hc
      obtain ⟨rfl, hlen⟩ := hc
      obtain ⟨σ, hσ⟩ := matchTerms_vars xs (encodeList cs) (by rw [encodeList_length, hlen])
      exact ⟨[] ++ ([] ++ σ), by simp [encode, matchTerm, matchTerms, hσ]⟩
    | text s => simp [formOf] at hc
    | seq es => simp [formOf] at hc
  | literal s =>
    cases c with
    | node _ _ => simp [formOf] at hc
    | text s' =>
      simp only [formOf, Option.some.injEq, Form.literal.injEq] at hc
      subst hc
      exact ⟨[], by simp [encode, matchTerm]⟩
    | seq es => simp [formOf] at hc

/-- A value pattern of a form matches only values of terms of that form. -/
theorem match_interprets {val : Term} {φ : Form} (hi : Interprets val φ) {c : CanonicalTerm}
    {σ : Env} (hm : matchTerm val (encode c) = some σ) : formOf c = some φ := by
  cases hi with
  | node name xs =>
    obtain ⟨vs, hv, hms⟩ := matchTerm_expr hm
    obtain ⟨v₁, vs₁, _, _, rfl, h₁, hms₁, _⟩ := matchTerms_cons hms
    obtain ⟨v₂, vs₂, _, _, rfl, h₂, hms₂, _⟩ := matchTerms_cons hms₁
    obtain ⟨rfl, _⟩ := matchTerm_sym h₁
    obtain ⟨rfl, _⟩ := matchTerm_sym h₂
    have hlen := matchTerms_length hms₂
    cases c with
    | node name' cs =>
      simp only [encode, Term.expr.injEq, List.cons.injEq, Term.sym.injEq, true_and] at hv
      obtain ⟨rfl, rfl⟩ := hv
      simp only [List.length_map, encodeList_length] at hlen
      simp [formOf, hlen]
    | text _ => simp [encode] at hv
    | seq _ => simp [encode] at hv
  | literal s =>
    obtain ⟨hv, _⟩ := matchTerm_lit hm
    cases c with
    | node _ _ => simp [encode] at hv
    | text s' =>
      simp only [encode, Term.lit.injEq] at hv
      simp [formOf, hv]
    | seq _ => simp [encode] at hv

theorem takes_match {pol : Term} {s : String} (h : Takes pol s) :
    ∃ σ, matchTerm pol (.sym s) = some σ := by
  cases h with
  | every p => exact ⟨_, rfl⟩
  | own => exact ⟨[], by simp [matchTerm]⟩

theorem match_takes {pol : Term} (hp : (∃ p, pol = .var p) ∨ ∃ s', pol = .sym s')
    {s : String} {σ : Env} (hm : matchTerm pol (.sym s) = some σ) : Takes pol s := by
  rcases hp with ⟨p, rfl⟩ | ⟨s', rfl⟩
  · exact .every p s
  · simp only [matchTerm] at hm
    split at hm
    · rename_i h
      subst h
      exact .own _
    · cases hm

/-! ## Dispatch -/

variable {P : Program} {V : Vocabulary} {c : Certificate} {f : String} {forms : List Form}

/-- An equation of the head takes a call on a term exactly when it interprets
the term's form for the call's policy. -/
theorem takes_call (adm : Admitted P V c f forms) {e : Equation} (he : e ∈ P) (hf : e.head = f)
    {s : String} {t : CanonicalTerm} {σ : Env}
    (hm : matchTerms e.params [.sym s, encode t] = some σ) :
    ∃ pol val φ, e.params = [pol, val] ∧ Takes pol s ∧ Interprets val φ ∧ formOf t = some φ := by
  obtain ⟨pol, val, φ, hps, hpol, hval, _⟩ := adm.shape e he hf
  rw [hps] at hm
  obtain ⟨v₁, vs₁, _, _, hvs, h₁, hms₁, _⟩ := matchTerms_cons hm
  obtain ⟨v₂, vs₂, _, _, hvs₂, h₂, _, _⟩ := matchTerms_cons hms₁
  simp only [List.cons.injEq] at hvs hvs₂
  obtain ⟨rfl, rfl⟩ := hvs
  obtain ⟨rfl, _⟩ := hvs₂
  exact ⟨pol, val, φ, hps, match_takes hpol h₁, hval, match_interprets hval h₂⟩

/-- A call of the head on a term of a declared form selects an equation that
interprets that form for the call's policy: no equation of another form takes
it. -/
theorem select_form (adm : Admitted P V c f forms) {t : CanonicalTerm} {φ : Form}
    (hφ : formOf t = some φ) (hmem : φ ∈ forms) (s : String) :
    ∃ e σ, P.select f [.sym s, encode t] = some (e, σ) ∧ e ∈ P ∧ e.head = f ∧
      ∃ pol val, e.params = [pol, val] ∧ Takes pol s ∧ Interprets val φ := by
  -- the covering equation takes the call, so the selection finds one
  obtain ⟨e₀, he₀, hf₀, pol₀, val₀, hps₀, hpol₀, hval₀⟩ := adm.covers φ hmem s
  obtain ⟨σp, hσp⟩ := takes_match hpol₀
  obtain ⟨σv, hσv⟩ := interprets_match hval₀ hφ
  have hsome : (P.select f [.sym s, encode t]).isSome := by
    unfold Program.select
    refine List.findSome?_isSome_iff.2 ⟨e₀, he₀, ?_⟩
    rw [if_pos ⟨hf₀, by rw [hps₀]; rfl⟩, hps₀]
    simp [matchTerms, hσp, hσv]
  obtain ⟨⟨e, σ⟩, hsel⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨e', he', hfe⟩ := List.exists_of_findSome?_eq_some hsel
  split at hfe
  · rename_i hcond
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hfe
    obtain ⟨σ', hm, rfl, rfl⟩ := hfe
    obtain ⟨pol, val, φ', hps, hpol, hval, hφ'⟩ := takes_call adm he' hcond.1 hm
    rw [hφ] at hφ'
    cases hφ'
    exact ⟨e', σ', hsel, he', hcond.1, pol, val, hps, hpol, hval⟩
  · cases hfe

/-- The equation a call selects is the form's one equation for the policy. -/
theorem select_unique (adm : Admitted P V c f forms) {t : CanonicalTerm} {φ : Form}
    (hφ : formOf t = some φ) (hmem : φ ∈ forms) (s : String) {e₀ : Equation} (he₀ : e₀ ∈ P)
    (hf₀ : e₀.head = f) {pol₀ val₀ : Term} (hps₀ : e₀.params = [pol₀, val₀])
    (hpol₀ : Takes pol₀ s) (hval₀ : Interprets val₀ φ) :
    ∃ σ, P.select f [.sym s, encode t] = some (e₀, σ) := by
  obtain ⟨e, σ, hsel, he, hf, pol, val, hps, hpol, hval⟩ := select_form adm hφ hmem s
  obtain rfl := adm.one_each e he e₀ he₀ hf hf₀ s pol val pol₀ val₀ φ hps hps₀ hpol hpol₀ hval hval₀
  exact ⟨σ, hsel⟩

/-- A call of the head on a term of a declared form is the right side of the
equation it selects, under the match. -/
theorem apply_form (adm : Admitted P V c f forms) (H : Host) (n : Nat) {t : CanonicalTerm}
    {φ : Form} (hφ : formOf t = some φ) (hmem : φ ∈ forms) (s : String) :
    ∃ e σ, P.select f [.sym s, encode t] = some (e, σ) ∧
      (∃ pol val, e.params = [pol, val] ∧ Takes pol s ∧ Interprets val φ) ∧
      apply P H n f [.sym s, encode t] = eval P H n σ e.body := by
  obtain ⟨e, σ, hsel, he, hf, hshape⟩ := select_form adm hφ hmem s
  refine ⟨e, σ, hsel, hshape, ?_⟩
  obtain ⟨pol, val, hps, _, _⟩ := hshape
  have hdef : P.definesAt f [Term.sym s, encode t].length = true := by
    unfold Program.definesAt
    refine List.any_eq_true.2 ⟨e, he, ?_⟩
    rw [hf, hps]
    show (f == f && (2 == 2)) = true
    rw [CanonicalGrammar.string_beq_self]
    rfl
  simp only [apply, applyWith, hdef, if_true, hsel]

/-- Under an admitted morphism and a host that keeps the vocabulary's promises,
a call of the head on any canonical term ends. -/
theorem morphism_ends (adm : Admitted P V c f forms) {H : Host} (hK : Keeps V H) (s : String)
    (t : CanonicalTerm) : ∃ n, apply P H n f [.sym s, encode t] ≠ .exhausted :=
  apply_terminates adm.descends hK f _

/-! ## The forms of a grammar's canonical values -/

section GrammarForms

variable {G : Grammar} {C : Classification} {L : String → Option (ListForm × String)}

/-- The arguments a constructor delivers from value position `i` over `k`
value positions: one for every position that does not extend the previous
one. -/
def countArgs (C : Classification) (p : Production) : Nat → Nat → Nat
  | _, 0 => 0
  | i, k + 1 => (if C.action p i = .extend then 0 else 1) + countArgs C p (i + 1) k

/-- The number of arguments of a constructor production. -/
def arity (C : Classification) (p : Production) : Nat :=
  countArgs C p 0 (values p.rhs).length

/-- Children deliver one argument per value position that does not extend. -/
theorem delivers_length {p : Production} :
    ∀ {i : Nat} {rest : List Sym} {kids : List Tree} {args : List CanonicalTerm},
      Delivers G C p i rest kids args → C.action p i ≠ .extend →
      args.length = countArgs C p i (values rest).length := by
  intro i rest kids args h
  induction h with
  | nil i =>
    intro _
    rfl
  | fixed i t rest kids args _ ih =>
    intro hne
    rw [values_fixed]
    exact ih hne
  | value i v hv rest hnext k w k? hw kids args _ ih =>
    intro hne
    have := ih hnext
    simp only [values_value hv, List.length_cons, countArgs, if_neg hne]
    omega
  | extended i v hv hr rest hext k w k? hw kh es key hh hnext kids args _ ih =>
    intro hne
    have := ih hnext
    simp only [values_value hv, values_value (x := .rule hr) rfl, List.length_cons, countArgs,
      if_neg hne, if_pos hext, show i + 1 + 1 = i + 2 from rfl]
    omega

/-- The forms a grammar's canonical values take: a constructor by its name
and number of arguments, a literal by its text, a token class and a list
rule's key as nodes of one child, and the text a list of a fixed body lists. -/
inductive GrammarForm (G : Grammar) (C : Classification) : Form → Prop where
  | constructor (p : Production) (hp : p ∈ G.productions) (n : String)
      (hk : C.kind p = .constructor n) : GrammarForm G C (.node n (arity C p))
  | literal (p : Production) (hp : p ∈ G.productions) (s : String)
      (hk : C.kind p = .literal s) : GrammarForm G C (.literal s)
  | token (p : Production) (hp : p ∈ G.productions) (cls : String)
      (hc : Sym.token cls ∈ p.rhs) : GrammarForm G C (.node cls 1)
  | list (p : Production) (hp : p ∈ G.productions) (key : String)
      (text : Option (Bool × String)) (hk : C.kind p = .list key text) :
      GrammarForm G C (.node key 1)
  | element (p : Production) (hp : p ∈ G.productions) (key : String) (right : Bool)
      (t : String) (hk : C.kind p = .list key (some (right, t))) : GrammarForm G C (.literal t)

theorem tpath_token_end {n : String} {chain : List Production} {cls : String}
    (h : TPath G C L n chain (.token cls)) : ∃ p ∈ G.productions, Sym.token cls ∈ p.rhs := by
  generalize he : End.token cls = e at h
  induction h with
  | stop => cases he
  | token t ht _ _ _ hv =>
    cases he
    exact ⟨t, ht, by rw [hv]; exact List.mem_singleton_self _⟩
  | list => cases he
  | step _ _ _ _ _ _ _ _ _ _ ih => exact ih he

/-- The value of a derivation at a list rule is a node of the rule's key. -/
theorem list_canon_form (hwf : WellFormed G C L) {m : String} {f : ListForm} {key : String}
    (hL : L m = some (f, key)) {sub : List Tok} {x : Tree} (hd : Derives G m sub x)
    {w : CanonicalTerm} {k? : Option String} (hw : finishTree G C x = some (w, k?)) :
    formOf (named k? w) = some (.node key 1) ∧ GrammarForm G C (.node key 1) := by
  obtain ⟨q, kids, hq, rfl, rfl, hitems⟩ := derives_inv hd
  obtain ⟨es, rfl, rfl, _⟩ := list_shape hwf hq hL hitems hw
  obtain ⟨text, hk⟩ := rule_kind_list hwf hL hq rfl
  exact ⟨rfl, .list q hq key text hk⟩

/-- Every canonical value of a derivation has a form the grammar declares. -/
theorem canon_form (hwf : WellFormed G C L) {n : String} {toks : List Tok} {t : Tree}
    (hd : Derives G n toks t) {cv : CanonicalTerm} (hc : canon G C t = some cv) :
    ∃ φ, formOf cv = some φ ∧ GrammarForm G C φ := by
  obtain ⟨v, k, hv, _⟩ := finishes hwf hd
  simp only [canon, hv, Option.map_some, Option.some.injEq] at hc
  subst hc
  cases hLn : L n with
  | some fk =>
    obtain ⟨f, key⟩ := fk
    exact ⟨_, (list_canon_form hwf hLn hd hv).1, (list_canon_form hwf hLn hd hv).2⟩
  | none =>
    obtain ⟨chain, e, x, hp, _, hx, _, _, hf⟩ := path_of_derives hwf hd hLn
    rw [hf] at hv
    obtain ⟨⟨w, k'⟩, hw, hvk⟩ := Option.map_eq_some_iff.1 hv
    simp only [Prod.mk.injEq] at hvk
    obtain ⟨rfl, rfl⟩ := hvk
    cases e with
    | production q =>
      obtain ⟨hq, hL, hk⟩ := hp.production_end
      obtain ⟨sub, kids, rfl, hitems⟩ := hx
      rw [finishTree_node hwf hq] at hw
      cases hd' : deliverKids G C q 0 [] kids with
      | none =>
        rw [hd'] at hw
        cases hw
      | some vals =>
        rw [hd'] at hw
        cases hkq : C.kind q with
        | transparent => exact absurd hkq hk
        | literal s =>
          simp only [hkq, finish, Option.map_some, Option.some.injEq, Prod.mk.injEq, Kind.key?] at hw
          obtain ⟨rfl, rfl⟩ := hw
          exact ⟨_, rfl, .literal q hq s hkq⟩
        | constructor cn =>
          simp only [hkq, finish, Option.map_some, Option.some.injEq, Prod.mk.injEq, Kind.key?] at hw
          obtain ⟨rfl, rfl⟩ := hw
          have hne : C.action q 0 ≠ .extend := by
            intro h
            rcases hwf.constructor q hq cn hkq 0 with h' | ⟨_, j, hj, _⟩
            · rw [h] at h'
              cases h'
            · omega
          obtain ⟨args, hargs, hdl⟩ := delivers_walk hwf hq hkq q.rhs.length q.rhs
            (Nat.le_refl _) 0 [] sub kids (by simp) rfl hne (items_finishing hwf hitems) [] vals hd'
          simp only [List.nil_append] at hargs
          subst hargs
          refine ⟨_, rfl, ?_⟩
          have hlen := delivers_length hdl hne
          rw [hlen]
          exact .constructor q hq cn hkq
        | list key text =>
          have := hwf.list q hq key text hkq
          rw [hL] at this
          cases this
    | token cls =>
      obtain ⟨s, rfl⟩ := hx
      rw [finishTree_leaf] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      obtain ⟨p, hp', hmem⟩ := tpath_token_end hp
      exact ⟨_, rfl, .token p hp' cls hmem⟩
    | list m =>
      obtain ⟨hm, _⟩ := hp.list_end
      obtain ⟨⟨f, key⟩, hfk⟩ := Option.isSome_iff_exists.1 hm
      obtain ⟨sub, hdx⟩ := hx
      obtain ⟨h1, h2⟩ := list_canon_form hwf hfk hdx hw
      exact ⟨_, by simpa [named] using h1, h2⟩

end GrammarForms

/-- A morphism admitted against the forms a grammar declares takes a call on
the canonical value of any derivation by the one equation of that value's
form for the call's policy, and the call ends. -/
theorem select_canon {P : Program} {V : Vocabulary} {c : Certificate} {f : String}
    {forms : List Form} (adm : Admitted P V c f forms) {G : Grammar} {C : Classification}
    {L : String → Option (ListForm × String)}
    (hforms : ∀ φ, GrammarForm G C φ → φ ∈ forms) (hwf : WellFormed G C L) {n : String}
    {toks : List Tok} {t : Tree} (hd : Derives G n toks t) {cv : CanonicalTerm}
    (hc : canon G C t = some cv) (s : String) :
    ∃ e σ φ, P.select f [.sym s, encode cv] = some (e, σ) ∧ formOf cv = some φ ∧
      ∃ pol val, e.params = [pol, val] ∧ Takes pol s ∧ Interprets val φ := by
  obtain ⟨φ, hφ, hgf⟩ := canon_form hwf hd hc
  obtain ⟨e, σ, hsel, _, _, hshape⟩ := select_form adm hφ (hforms φ hgf) s
  exact ⟨e, σ, φ, hsel, hφ, hshape⟩

/-- A well-typed admitted morphism returns a value of its result sort on a
policy and a canonical value of its argument sorts. -/
theorem morphism_returns {P : Program} {V : Vocabulary} {c : Certificate} {f : String}
    {forms : List Form} (adm : Admitted P V c f forms) {H : Host} (hK : Keeps V H)
    {T : Typing} (hT : WellTyped T P H) {pol arg target : T.sorts}
    (hsig : T.sig f 2 = some ([pol, arg], target)) {s : String} (hpol : T.holds pol (.sym s))
    {t : CanonicalTerm} (hcanon : T.holds arg (encode t)) :
    ∃ n v, apply P H n f [.sym s, encode t] = .value v ∧ T.holds target v :=
  apply_returns adm.descends hK hT hsig (.cons hpol (.cons hcanon .nil))

/-- A well-typed admitted morphism returns a value of its result sort on the
canonical value of every derivation, when its canonical argument sort holds the
canonical values of derivations.  For a recursive morphism that sort is the
sort of those values, and the hypothesis is shown by induction on derivations. -/
theorem canon_returns {P : Program} {V : Vocabulary} {c : Certificate} {f : String}
    {forms : List Form} (adm : Admitted P V c f forms) {H : Host} (hK : Keeps V H)
    {T : Typing} (hT : WellTyped T P H) {pol arg target : T.sorts}
    (hsig : T.sig f 2 = some ([pol, arg], target)) {s : String} (hpol : T.holds pol (.sym s))
    {G : Grammar} {C : Classification}
    (hcanon : ∀ {n' : String} {toks' : List Tok} {t' : Tree} {cv' : CanonicalTerm},
      Derives G n' toks' t' → canon G C t' = some cv' → T.holds arg (encode cv'))
    {n : String} {toks : List Tok} {t : Tree} (hd : Derives G n toks t) {cv : CanonicalTerm}
    (hc : canon G C t = some cv) :
    ∃ k v, apply P H k f [.sym s, encode cv] = .value v ∧ T.holds target v :=
  morphism_returns adm hK hT hsig hpol (hcanon hd hc)

/-- The same, when the canonical argument sort holds every canonical value of a
form the grammar declares, whatever its children. -/
theorem canon_returns_of_forms {P : Program} {V : Vocabulary} {c : Certificate} {f : String}
    {forms : List Form} (adm : Admitted P V c f forms) {H : Host} (hK : Keeps V H)
    {T : Typing} (hT : WellTyped T P H) {pol arg target : T.sorts}
    (hsig : T.sig f 2 = some ([pol, arg], target)) {s : String} (hpol : T.holds pol (.sym s))
    {G : Grammar} {C : Classification} {L : String → Option (ListForm × String)}
    (hwf : WellFormed G C L)
    (hcanon : ∀ cv φ, formOf cv = some φ → GrammarForm G C φ → T.holds arg (encode cv))
    {n : String} {toks : List Tok} {t : Tree} (hd : Derives G n toks t) {cv : CanonicalTerm}
    (hc : canon G C t = some cv) :
    ∃ k v, apply P H k f [.sym s, encode cv] = .value v ∧ T.holds target v :=
  canon_returns adm hK hT hsig hpol (fun hd' hc' => by
    obtain ⟨φ, hφ, hgf⟩ := canon_form hwf hd' hc'
    exact hcanon _ φ hφ hgf) hd hc

/-! ## A morphism on sums, end to end

The sums grammar of the canonical-grammar examples, checked well formed and
settled, with a recursive morphism to trees: a number is a leaf over its
lexeme, a sum the `plus` of its operands' trees.  The morphism is admitted with
a descent certificate on its value position and well typed with an argument
sort of canonical sums, which every derivation's value has.  So it returns a
tree on the canonical value of every derivation.  Without its sum equation the
morphism is not admitted. -/

namespace MorphismExamples

open Mettapedia.GSLT.Parsing.CanonicalGrammar
open Mettapedia.GSLT.Parsing.CanonicalGrammar.Examples
open Mettapedia.GSLT.Parsing.CanonicalGrammar.WellFormedExamples
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.DeterministicEquations.Typing
open Mettapedia.GSLT.LanguageDef.DeterministicEquations.TypingExamples (noPrimitives)

/-! ### The canonical values of sums -/

/-- The canonical values of sums: a number token, or a sum node of two. -/
inductive IsSum : CanonicalTerm → Prop where
  | num (s : String) : IsSum (.node "NUM" [.text s])
  | add (a b : CanonicalTerm) (ha : IsSum a) (hb : IsSum b) : IsSum (.node "S" [a, b])

theorem sums_finish {n : String} {toks : List Tok} {t : Tree} (hd : Derives sums n toks t) :
    ∀ {v : CanonicalTerm} {k : Option String},
      finishTree sums sumsMarked t = some (v, k) → IsSum v ∧ k = none := by
  refine Derives.induction_with
    (fun _ _ t => ∀ {v : CanonicalTerm} {k : Option String},
      finishTree sums sumsMarked t = some (v, k) → IsSum v ∧ k = none) ?_ hd
  intro p hp toks kids _ hw v k h
  simp only [sums, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · change ItemsWith sums _ [.token "NUM"] toks kids at hw
    cases hw with
    | token cls s _ rest toks' kids' hrest =>
      cases hrest
      rw [finishTree_node sums_wellFormed (p := sumNum) (by decide), deliverKids_cons,
        finishTree_leaf] at h
      change some (CanonicalTerm.node "NUM" [.text s], (none : Option String)) = some (v, k) at h
      cases h
      exact ⟨.num s, rfl⟩
  · change ItemsWith sums _ [.rule "S", .fixed "+", .rule "S"] toks kids at hw
    cases hw with
    | rule _ sub₁ t₁ _ ih₁ rest toks₁ kids₁ hrest =>
      cases hrest with
      | fixed _ _ toks₂ kids₂ hrest =>
        cases hrest with
        | rule _ sub₂ t₂ _ ih₂ rest toks₃ kids₃ hrest =>
          cases hrest
          have ha0 : sumsMarked.action sumAdd 0 = .arg := rfl
          have ha1 : sumsMarked.action sumAdd 1 = .arg := rfl
          have hk : sumsMarked.kind sumAdd = .constructor "S" := rfl
          have hdel : ∀ (vals : List CanonicalTerm) (w : CanonicalTerm),
              deliver none .arg vals w = some (vals ++ [w]) := fun _ _ => rfl
          rw [finishTree_node sums_wellFormed (p := sumAdd) (by decide)] at h
          cases h₁ : finishTree sums sumsMarked t₁ with
          | none => simp only [deliverKids_cons, h₁, reduceCtorEq] at h
          | some r₁ =>
            obtain ⟨v₁, k₁⟩ := r₁
            obtain ⟨hv₁, rfl⟩ := ih₁ h₁
            cases h₂ : finishTree sums sumsMarked t₂ with
            | none =>
              simp only [deliverKids_cons, h₁, h₂, ha0, hdel, Nat.zero_add, reduceCtorEq] at h
            | some r₂ =>
              obtain ⟨v₂, k₂⟩ := r₂
              obtain ⟨hv₂, rfl⟩ := ih₂ h₂
              simp only [deliverKids_cons, deliverKids_nil, h₁, h₂, ha0, ha1, hdel, hk,
                Nat.zero_add, List.nil_append, List.singleton_append, finish, Kind.key?,
                Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨.add v₁ v₂ hv₁ hv₂, rfl⟩

/-- Every canonical value of a sum is a canonical sum. -/
theorem sums_canon {n : String} {toks : List Tok} {t : Tree} (hd : Derives sums n toks t)
    {cv : CanonicalTerm} (hc : canon sums sumsMarked t = some cv) : IsSum cv := by
  unfold canon at hc
  cases hf : finishTree sums sumsMarked t with
  | none => rw [hf] at hc; cases hc
  | some r =>
    obtain ⟨v, k⟩ := r
    obtain ⟨hv, rfl⟩ := sums_finish hd hf
    rw [hf] at hc
    cases hc
    exact hv

/-! ### A morphism from sums to trees -/

/-- `(sum-tree $p (bnf NUM $x)) = (leaf $x)` and
`(sum-tree $p (bnf S $a $b)) = (plus (sum-tree $p $a) (sum-tree $p $b))`. -/
def sumNumEq : Equation :=
  ⟨"sum-tree-num", "sum-tree", [.var "p", .expr [.sym "bnf", .sym "NUM", .var "x"]],
    .expr [.sym "leaf", .var "x"]⟩
def sumAddEq : Equation :=
  ⟨"sum-tree-add", "sum-tree", [.var "p", .expr [.sym "bnf", .sym "S", .var "a", .var "b"]],
    .expr [.sym "plus", .expr [.sym "sum-tree", .var "p", .var "a"],
      .expr [.sym "sum-tree", .var "p", .var "b"]]⟩
def sumTree : Program := [sumNumEq, sumAddEq]

def sumForms : List Form := [.node "NUM" 1, .node "S" 2]

/-- No primitives are classified. -/
def noVocabulary : Vocabulary := ⟨fun _ _ => .none⟩

/-- The call descends on its value, position 1. -/
def sumCertificate : Certificate :=
  ⟨[⟨fun f n => if f = "sum-tree" ∧ n = 2 then [1] else [], fun _ _ => 0⟩]⟩

theorem strip_var (x : String) : strip sumTree noVocabulary (.var x) = .var x := by
  rw [strip]
  rfl

theorem carried_var (x : String) : carried sumTree noVocabulary [] (.var x) = some x := by
  unfold carried
  rw [strip_var]
  rfl

theorem cost_var {x : String} (hx : x = "a" ∨ x = "b") :
    cost sumTree noVocabulary sumAddEq.params [1] [] (.var x) [] = some (0, [x]) := by
  rw [cost]
  rcases hx with rfl | rfl <;> rfl

/-- The caller's pattern at the measured position. -/
abbrev sumPattern : Term := .expr [.sym "bnf", .sym "S", .var "a", .var "b"]

theorem weigh_call {x : String} (hx : x = "a" ∨ x = "b") :
    weigh sumTree noVocabulary sumAddEq.params [1] [1] ⟨"sum-tree", [.var "p", .var x], []⟩ =
      some ((0 : Int) - ((overhead sumPattern + 1 : Nat) : Int)) := by
  have hrange : (List.range 2).filter (fun j => ([1] : List Nat).contains j) = [1] := rfl
  have hslack : slack sumAddEq.params [1] [x] = overhead sumPattern + 1 := by
    rcases hx with rfl | rfl <;> rfl
  unfold weigh
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, hrange,
    List.filter_cons, List.filter_nil, List.getD_cons_succ, List.getD_cons_zero, carried_var,
    Option.isSome_some, Bool.not_true, if_true, Bool.false_eq_true, ite_false,
    List.cons_append, List.nil_append, costAt, cost_var hx, hslack]
  rfl

theorem decides_call {x : String} (hx : x = "a" ∨ x = "b") :
    decides sumTree noVocabulary sumAddEq ⟨"sum-tree", [.var "p", .var x], []⟩
      sumCertificate.levels = true := by
  have hle : (0 : Int) - ((overhead sumPattern + 1 : Nat) : Int) + ((0 : Nat) : Int) -
      ((0 : Nat) : Int) ≤ -1 := by
    have := Int.natCast_nonneg (overhead sumPattern)
    omega
  show (match weigh sumTree noVocabulary sumAddEq.params [1] [1]
      ⟨"sum-tree", [.var "p", .var x], []⟩ with
    | none => false
    | some w =>
      if w + ((0 : Nat) : Int) - ((0 : Nat) : Int) ≤ -1 then true
      else if w + ((0 : Nat) : Int) - ((0 : Nat) : Int) ≤ 0 then
        decides sumTree noVocabulary sumAddEq ⟨"sum-tree", [.var "p", .var x], []⟩ []
      else false) = true
  rw [weigh_call hx]
  exact if_pos hle

theorem sumTree_descends : Descends sumTree noVocabulary sumCertificate := by
  refine ⟨by unfold LeftLinear; decide, ?_, ?_⟩
  · intro l hl e he i hi
    simp only [sumCertificate, List.mem_singleton] at hl
    subst hl
    simp only [sumTree, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · obtain rfl : i = 1 := List.mem_singleton.1 hi
      exact ⟨_, rfl, rfl⟩
    · obtain rfl : i = 1 := List.mem_singleton.1 hi
      exact ⟨_, rfl, rfl⟩
  · intro e he s hs
    simp only [sumTree, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · have hnone : sites sumTree noVocabulary [] sumNumEq.body = [] := rfl
      rw [hnone] at hs
      cases hs
    · have htwo : sites sumTree noVocabulary [] sumAddEq.body =
          [⟨"sum-tree", [.var "p", .var "a"], []⟩, ⟨"sum-tree", [.var "p", .var "b"], []⟩] := rfl
      rw [htwo] at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact decides_call (.inl rfl)
      · exact decides_call (.inr rfl)

theorem noPrimitives_keeps : Keeps noVocabulary noPrimitives where
  unclassified _ _ _ := rfl
  handled _ _ h := absurd rfl h
  atom _ _ _ h := by cases h
  preserving _ _ _ h := by cases h

/-- The form a value pattern interprets. -/
def patternForm : Term → Option Form
  | .expr (.sym "bnf" :: .sym name :: rest) => some (.node name rest.length)
  | .lit s => some (.literal s)
  | _ => none

theorem interprets_form {val : Term} {φ : Form} (h : Interprets val φ) :
    patternForm val = some φ := by
  cases h with
  | node name xs =>
    show some (Form.node name (xs.map Term.var).length) = some (Form.node name xs.length)
    rw [List.length_map]
  | literal s => rfl

theorem sumTree_admitted : Admitted sumTree noVocabulary sumCertificate "sum-tree" sumForms where
  descends := sumTree_descends
  shape := by
    intro e he _
    simp only [sumTree, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨_, _, _, rfl, .inl ⟨"p", rfl⟩, .node "NUM" ["x"], by decide⟩
    · exact ⟨_, _, _, rfl, .inl ⟨"p", rfl⟩, .node "S" ["a", "b"], by decide⟩
  covers := by
    intro φ hφ s
    simp only [sumForms, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl
    · exact ⟨sumNumEq, List.mem_cons_self, rfl, _, _, rfl, .every "p" s, .node "NUM" ["x"]⟩
    · exact ⟨sumAddEq, List.mem_cons_of_mem _ List.mem_cons_self, rfl, _, _, rfl, .every "p" s,
        .node "S" ["a", "b"]⟩
  one_each := by
    intro e₁ he₁ e₂ he₂ _ _ s pol₁ val₁ pol₂ val₂ φ hp₁ hp₂ _ _ hi₁ hi₂
    have hf₁ := interprets_form hi₁
    have hf₂ := interprets_form hi₂
    simp only [sumTree, List.mem_cons, List.not_mem_nil, or_false] at he₁ he₂
    rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl
    · rfl
    · cases hp₁
      cases hp₂
      rw [← hf₂] at hf₁
      exact absurd hf₁ (by decide)
    · cases hp₁
      cases hp₂
      rw [← hf₂] at hf₁
      exact absurd hf₁ (by decide)
    · rfl

/-! ### Its typing -/

/-- The sorts of the morphism: policies, canonical sums, texts and trees. -/
inductive MSort where
  | policy | canonical | text | tree
  deriving DecidableEq

/-- Trees of leaves over texts. -/
inductive IsTree : Term → Prop where
  | leaf (s : String) : IsTree (.expr [.sym "leaf", .lit s])
  | plus (a b : Term) (ha : IsTree a) (hb : IsTree b) : IsTree (.expr [.sym "plus", a, b])

def mHolds : MSort → Term → Prop
  | .policy, v => ∃ s, v = .sym s
  | .canonical, v => ∃ cv, IsSum cv ∧ v = encode cv
  | .text, v => ∃ s, v = .lit s
  | .tree, v => IsTree v

abbrev sumTyping : Typing where
  sorts := MSort
  holds := mHolds
  sig f n :=
    if f = "sum-tree" ∧ n = 2 then some ([.policy, .canonical], .tree)
    else if f = "leaf" ∧ n = 1 then some ([.text], .tree)
    else if f = "plus" ∧ n = 2 then some ([.tree, .tree], .tree)
    else none

theorem sumTyping_sig {f : String} {n : Nat} {Ss : List MSort} {S : MSort}
    (h : sumTyping.sig f n = some (Ss, S)) :
    (f = "sum-tree" ∧ n = 2 ∧ Ss = [.policy, .canonical] ∧ S = .tree) ∨
    (f = "leaf" ∧ n = 1 ∧ Ss = [.text] ∧ S = .tree) ∨
    (f = "plus" ∧ n = 2 ∧ Ss = [.tree, .tree] ∧ S = .tree) := by
  change (if f = "sum-tree" ∧ n = 2 then some ([MSort.policy, .canonical], MSort.tree)
    else if f = "leaf" ∧ n = 1 then some ([MSort.text], MSort.tree)
    else if f = "plus" ∧ n = 2 then some ([MSort.tree, .tree], MSort.tree) else none) =
      some (Ss, S) at h
  by_cases h₁ : f = "sum-tree" ∧ n = 2
  · rw [if_pos h₁] at h
    cases h
    exact .inl ⟨h₁.1, h₁.2, rfl, rfl⟩
  · rw [if_neg h₁] at h
    by_cases h₂ : f = "leaf" ∧ n = 1
    · rw [if_pos h₂] at h
      cases h
      exact .inr (.inl ⟨h₂.1, h₂.2, rfl, rfl⟩)
    · rw [if_neg h₂] at h
      by_cases h₃ : f = "plus" ∧ n = 2
      · rw [if_pos h₃] at h
        cases h
        exact .inr (.inr ⟨h₃.1, h₃.2, rfl, rfl⟩)
      · rw [if_neg h₃] at h
        cases h

theorem sumTree_wellTyped : WellTyped sumTyping sumTree noPrimitives where
  covers := by
    intro f Ss S vs hsig hvs hdef
    rcases sumTyping_sig hsig with ⟨rfl, _, rfl, rfl⟩ | ⟨rfl, hn, rfl, rfl⟩ | ⟨rfl, hn, rfl, rfl⟩
    · cases hvs with
      | cons h₁ hrest =>
        cases hrest with
        | cons h₂ hnil =>
          cases hnil
          obtain ⟨s, rfl⟩ := h₁
          obtain ⟨cv, hcv, rfl⟩ := h₂
          cases hcv with
          | num s' => rfl
          | add a b _ _ => rfl
    · rw [hn] at hdef
      exact absurd hdef (by decide)
    · rw [hn] at hdef
      exact absurd hdef (by decide)
  bodies := by
    intro e he Ss S hsig
    simp only [sumTree, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · rcases sumTyping_sig hsig with ⟨_, _, rfl, rfl⟩ | ⟨hf, _⟩ | ⟨hf, _⟩
      · refine ⟨[("x", .text), ("p", .policy)], ?_, ?_⟩
        · exact HasType.call (T := sumTyping) _ "leaf" _ [.text] .tree (by decide) rfl
            (HasTypes.cons (T := sumTyping) _ _ _ .text []
              (HasType.var (T := sumTyping) _ "x" .text rfl) (HasTypes.nil (T := sumTyping) _))
        · intro vs σ hvs hm y S' hy
          cases hvs with
          | cons h₁ hrest =>
            cases hrest with
            | cons h₂ hnil =>
              cases hnil
              obtain ⟨s, rfl⟩ := h₁
              obtain ⟨cv, hcv, rfl⟩ := h₂
              cases hcv with
              | num s' =>
                have hσ : matchTerms sumNumEq.params [.sym s, encode (.node "NUM" [.text s'])] =
                    some [("p", .sym s), ("x", .lit s')] := rfl
                rw [hσ] at hm
                cases hm
                by_cases hx : "x" = y
                · subst hx
                  cases hy
                  exact ⟨.lit s', rfl, s', rfl⟩
                · by_cases hp : "p" = y
                  · subst hp
                    cases hy
                    exact ⟨.sym s, rfl, s, rfl⟩
                  · rw [Ctx.lookup_cons_ne (T := sumTyping) _ _ hx,
                      Ctx.lookup_cons_ne (T := sumTyping) _ _ hp] at hy
                    cases hy
              | add a b _ _ =>
                have hσ : matchTerms sumNumEq.params [.sym s, encode (.node "S" [a, b])] = none :=
                  rfl
                rw [hσ] at hm
                cases hm
      · exact absurd hf (by decide)
      · exact absurd hf (by decide)
    · rcases sumTyping_sig hsig with ⟨_, _, rfl, rfl⟩ | ⟨hf, _⟩ | ⟨hf, _⟩
      · refine ⟨[("a", .canonical), ("b", .canonical), ("p", .policy)], ?_, ?_⟩
        · refine HasType.call (T := sumTyping) _ "plus" _ [.tree, .tree] .tree (by decide) rfl
            (HasTypes.cons (T := sumTyping) _ _ _ .tree [.tree] ?_
              (HasTypes.cons (T := sumTyping) _ _ _ .tree [] ?_ (HasTypes.nil (T := sumTyping) _)))
          · exact HasType.call (T := sumTyping) _ "sum-tree" _ [.policy, .canonical] .tree
              (by decide) rfl
              (HasTypes.cons (T := sumTyping) _ _ _ .policy [.canonical]
                (HasType.var (T := sumTyping) _ "p" .policy rfl)
                (HasTypes.cons (T := sumTyping) _ _ _ .canonical []
                  (HasType.var (T := sumTyping) _ "a" .canonical rfl)
                  (HasTypes.nil (T := sumTyping) _)))
          · exact HasType.call (T := sumTyping) _ "sum-tree" _ [.policy, .canonical] .tree
              (by decide) rfl
              (HasTypes.cons (T := sumTyping) _ _ _ .policy [.canonical]
                (HasType.var (T := sumTyping) _ "p" .policy rfl)
                (HasTypes.cons (T := sumTyping) _ _ _ .canonical []
                  (HasType.var (T := sumTyping) _ "b" .canonical rfl)
                  (HasTypes.nil (T := sumTyping) _)))
        · intro vs σ hvs hm y S' hy
          cases hvs with
          | cons h₁ hrest =>
            cases hrest with
            | cons h₂ hnil =>
              cases hnil
              obtain ⟨s, rfl⟩ := h₁
              obtain ⟨cv, hcv, rfl⟩ := h₂
              cases hcv with
              | num s' =>
                have hσ : matchTerms sumAddEq.params [.sym s, encode (.node "NUM" [.text s'])] =
                    none := rfl
                rw [hσ] at hm
                cases hm
              | add a b ha hb =>
                have hσ : matchTerms sumAddEq.params [.sym s, encode (.node "S" [a, b])] =
                    some [("p", .sym s), ("a", encode a), ("b", encode b)] := rfl
                rw [hσ] at hm
                cases hm
                by_cases hya : "a" = y
                · subst hya
                  cases hy
                  exact ⟨encode a, rfl, a, ha, rfl⟩
                · by_cases hyb : "b" = y
                  · subst hyb
                    cases hy
                    exact ⟨encode b, rfl, b, hb, rfl⟩
                  · by_cases hyp : "p" = y
                    · subst hyp
                      cases hy
                      exact ⟨.sym s, rfl, s, rfl⟩
                    · rw [Ctx.lookup_cons_ne (T := sumTyping) _ _ hya,
                        Ctx.lookup_cons_ne (T := sumTyping) _ _ hyb,
                        Ctx.lookup_cons_ne (T := sumTyping) _ _ hyp] at hy
                      cases hy
      · exact absurd hf (by decide)
      · exact absurd hf (by decide)
  arity := by
    intro f n Ss S hsig hdef
    rcases sumTyping_sig hsig with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
    · exact absurd hdef (by decide)
    · decide
    · decide
  host := by
    intro f Ss S vs hsig hvs hnd
    rcases sumTyping_sig hsig with ⟨rfl, _, rfl, rfl⟩ | ⟨rfl, _, rfl, rfl⟩ | ⟨rfl, _, rfl, rfl⟩
    · exact absurd hnd (by decide)
    · cases hvs with
      | cons h₁ hnil =>
        cases hnil
        obtain ⟨s, rfl⟩ := h₁
        exact .inl ⟨rfl, .leaf s⟩
    · cases hvs with
      | cons h₁ hrest =>
        cases hrest with
        | cons h₂ hnil =>
          cases hnil
          exact .inl ⟨rfl, .plus _ _ h₁ h₂⟩

/-! ### The morphism on every sum -/

/-- The sum-tree morphism returns a tree on the canonical value of every
derivation of a sum. -/
theorem sum_tree_returns {n : String} {toks : List Tok} {t : Tree} (hd : Derives sums n toks t)
    {cv : CanonicalTerm} (hc : canon sums sumsMarked t = some cv) (s : String) :
    ∃ k v, apply sumTree noPrimitives k "sum-tree" [.sym s, encode cv] = .value v ∧ IsTree v :=
  canon_returns sumTree_admitted noPrimitives_keeps sumTree_wellTyped
    (pol := MSort.policy) (arg := .canonical) (target := .tree) rfl ⟨s, rfl⟩
    (fun hd' hc' => ⟨_, sums_canon hd' hc', rfl⟩) hd hc

theorem sum_tree_one_plus_two :
    apply sumTree noPrimitives 10 "sum-tree"
      [.sym "p", encode (.node "S" [.node "NUM" [.text "1"], .node "NUM" [.text "2"]])] =
      .value (.expr [.sym "plus", .expr [.sym "leaf", .lit "1"], .expr [.sym "leaf", .lit "2"]]) := by
  rfl

/-- Without the sum equation the morphism does not cover the grammar's forms. -/
theorem numbers_only_not_admitted (c : Certificate) :
    ¬ Admitted [sumNumEq] noVocabulary c "sum-tree" sumForms := by
  intro adm
  obtain ⟨e, he, _, pol, val, hp, _, hi⟩ := adm.covers (.node "S" 2) (by decide) "p"
  obtain rfl : e = sumNumEq := List.mem_singleton.1 he
  cases hp
  exact absurd (interprets_form hi) (by decide)

end MorphismExamples

end Mettapedia.GSLT.Parsing.CanonicalMorphism
