import Mathlib.Tactic

/-!
# One render per request: the value route and the text route

A provider request is a JSON value. The codec turns a request into its wire
body, or refuses it.

* The text route renders the request; the codec parses that text, refusing
  a repeated key, encodes it and renders the body; the caller parses the
  body back, adjusts it, and renders the result. That is three renders and
  two parses of the prompt's bytes.
* The value route holds the request to the parser's contract (no repeated
  key), has the codec encode the value, adjusts the body and renders it
  once.

Invariants proved here, for a codec whose renders parse back to canonical
values and whose bodies are canonical for canonical requests:
* on every canonical request the two routes answer alike: the same bytes,
  or the same refusal;
* on every request with a repeated key both refuse it alike;
* the hold accepts exactly what the codec's parser accepts.

Two counterexamples mark the hypotheses:
* a value route without the hold accepts a request with a repeated key,
  which the text route refuses;
* on a request that is not canonical (a number spelled `1e2`) the routes
  differ, because the text route's second parse respells it.

This is an abstract contract, not a refinement proof of `lib/llm.metta` or
`src/provider_request_cetta.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.RequestEncodingRoutes

/-- A codec and the two parsers the text route uses. -/
structure Codec (V T E : Type) where
  render : V → T
  /-- The codec's parser: it refuses a repeated key. -/
  parseUnique : T → Except E V
  /-- The caller's parser: a repeated key keeps its last value, and numbers
  are respelled canonically. -/
  parseLast : T → V
  encode : V → Except E V
  adjust : V → Except E V
  Distinct : V → Prop
  Canonical : V → Prop
  ambiguous : E
  distinctDecidable : DecidablePred Distinct
  unique_round : ∀ v, Distinct v → parseUnique (render v) = .ok v
  unique_refuses : ∀ v, ¬ Distinct v → parseUnique (render v) = .error ambiguous
  last_round : ∀ v, Canonical v → parseLast (render v) = v
  canonical_distinct : ∀ v, Canonical v → Distinct v
  encode_canonical : ∀ v w, Canonical v → encode v = .ok w → Canonical w

variable {V T E : Type} (c : Codec V T E)

def Codec.hold (v : V) : Except E V :=
  @ite _ (c.Distinct v) (c.distinctDecidable v) (.ok v) (.error c.ambiguous)

/-- Render, parse, encode, render the body, parse it back, adjust, render. -/
def Codec.textRoute (req : V) : Except E T := do
  let v ← c.parseUnique (c.render req)
  let body ← c.encode v
  let final ← c.adjust (c.parseLast (c.render body))
  pure (c.render final)

/-- Hold, encode, adjust, render once. -/
def Codec.valueRoute (req : V) : Except E T := do
  let v ← c.hold req
  let body ← c.encode v
  let final ← c.adjust body
  pure (c.render final)

/-- The hold accepts exactly what the codec's parser accepts from the
request's rendering, and answers the same value. -/
theorem hold_is_parse (v : V) : c.hold v = c.parseUnique (c.render v) := by
  unfold Codec.hold
  by_cases h : c.Distinct v
  · rw [@if_pos _ (c.distinctDecidable v) h, c.unique_round v h]
  · rw [@if_neg _ (c.distinctDecidable v) h, c.unique_refuses v h]

/-- On a canonical request the value route answers what the text route
answers: the same rendered body, or the same refusal. -/
theorem routes_agree_canonical (req : V) (hreq : c.Canonical req) :
    c.valueRoute req = c.textRoute req := by
  unfold Codec.valueRoute Codec.textRoute
  rw [hold_is_parse, c.unique_round req (c.canonical_distinct req hreq)]
  simp only [bind, Except.bind]
  cases henc : c.encode req with
  | error e => rfl
  | ok body => simp only [c.last_round body (c.encode_canonical req body hreq henc)]

/-- A request with a repeated key: both routes refuse it as ambiguous. -/
theorem routes_agree_repeated (req : V) (hreq : ¬ c.Distinct req) :
    c.valueRoute req = .error c.ambiguous ∧ c.textRoute req = .error c.ambiguous := by
  unfold Codec.valueRoute Codec.textRoute
  rw [hold_is_parse, c.unique_refuses req hreq]
  exact ⟨rfl, rfl⟩

/-! ## Counterexample: a value route without the hold -/

def Codec.unheldRoute (req : V) : Except E T := do
  let body ← c.encode req
  let final ← c.adjust body
  pure (c.render final)

/-- Whenever the codec's encoder would take a request with a repeated key,
the route without the hold answers a body where the text route refuses. -/
theorem unheld_accepts_repeated (req body final : V) (hreq : ¬ c.Distinct req)
    (henc : c.encode req = .ok body) (hadj : c.adjust body = .ok final) :
    c.unheldRoute req = .ok (c.render final) ∧ c.textRoute req = .error c.ambiguous := by
  refine ⟨?_, (routes_agree_repeated c req hreq).2⟩
  simp [Codec.unheldRoute, henc, hadj, bind, Except.bind, pure, Except.pure]

/-- A toy codec over key lists, whose encoder takes any list. -/
def keys : Codec (List ℕ) (List ℕ) Unit where
  render := id
  parseUnique := fun t => if t.Nodup then .ok t else .error ()
  parseLast := fun t => t.dedup
  encode := fun v => .ok v
  adjust := fun v => .ok v
  Distinct := List.Nodup
  Canonical := List.Nodup
  ambiguous := ()
  distinctDecidable := fun v => List.nodupDecidable v
  unique_round := fun v h => by simp [h]
  unique_refuses := fun v h => by simp [h]
  last_round := fun v h => List.dedup_eq_self.mpr h
  canonical_distinct := fun _ h => h
  encode_canonical := fun v w h e => by simp only [Except.ok.injEq] at e; exact e ▸ h

theorem keys_unheld_differs :
    keys.unheldRoute [1, 1] = .ok [1, 1] ∧ keys.textRoute [1, 1] = .error () := by
  constructor <;> decide

/-! ## Counterexample: a request that is not canonical -/

/-- A toy codec over numbers with a spelling: `true` is the canonical one.
The codec's parser keeps a spelling; the caller's parser respells. -/
def spelled : Codec (ℕ × Bool) (ℕ × Bool) Unit where
  render := id
  parseUnique := fun t => .ok t
  parseLast := fun t => (t.1, true)
  encode := fun v => .ok v
  adjust := fun v => .ok v
  Distinct := fun _ => True
  Canonical := fun v => v.2 = true
  ambiguous := ()
  distinctDecidable := fun _ => instDecidableTrue
  unique_round := fun _ _ => rfl
  unique_refuses := fun _ h => absurd trivial h
  last_round := fun v h => by cases v; simp_all
  canonical_distinct := fun _ _ => trivial
  encode_canonical := fun v w h e => by simp only [Except.ok.injEq] at e; exact e ▸ h

theorem spelled_routes_differ :
    spelled.valueRoute (100, false) = .ok (100, false) ∧
      spelled.textRoute (100, false) = .ok (100, true) := by
  constructor <;> rfl

end Mettapedia.Protocols.Agents.RequestEncodingRoutes
