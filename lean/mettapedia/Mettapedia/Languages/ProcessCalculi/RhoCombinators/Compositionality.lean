/-
# Compositionality: the translation of a context does not depend on its body

§2 asks for compositionality alongside linearity: `⟦C[P]⟧ = ⟦C⟧[⟦P⟧]`. With the
translation built and its slot accounting explicit, the statement can be made
precisely — and the precision is the content, because `translate` carries two
parameters that a naive reading of the equation hides.

A source term's translation depends on where it sits: on the **proxies** its
enclosing inputs allocated, and on the **slot offset** available to it. So a
context's translation cannot be a term with a hole in it; it is a term with a
*function* in it, applied to the proxies and offset the hole sits at.

`translateContext` is that, and `translate_fill` is the law:

```
    translate (C[P]) proxies offset
      = translateContext C proxies offset P.slotsUsed
          (fun proxies' offset' => translate P proxies' offset')
```

The context's translation mentions the body in exactly two ways: through the
plug, and through `P.slotsUsed` — the body's slot footprint, which the enclosing
`par` needs in order to place its right-hand side in a disjoint range. Nothing
else about the body reaches the context, and `fill_slotsUsed` is the bookkeeping
that makes the footprint compose.

## Why the footprint has to appear

`translate (par p q) offset` compiles `q` at `offset + p.slotsUsed`, so a
context with the hole on the left genuinely needs to know how many slots the
body will use. That is not an artefact: it is the price of allocating without an
occurrence check, and the earlier turns' range discipline is where it came
from. A formulation that hid it would be a weaker theorem pretending to be the
expected one.

## What compositionality is for

`translate_fill_congr` is the consequence that matters: **two bodies with the
same translation and the same slot footprint are interchangeable in every
context.** That is the substitutivity property a full-abstraction argument needs,
and it follows from the law without further work.

Full abstraction itself is **not** proved here, and remains gated on the
comparison between this calculus's parallel-structural congruence and the
draft's least congruence with its separate name equivalence.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Translation

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## Source contexts -/

/-- A one-hole context over source processes.  The hole sits in a process
position: under a parallel composition, under an output's body, or under an
input's body — where it acquires a proxy. -/
inductive SrcContext where
  | hole : SrcContext
  | parLeft : SrcContext → Src → SrcContext
  | parRight : Src → SrcContext → SrcContext
  | outBody : SrcName → SrcContext → SrcContext
  | inpBody : SrcName → SrcContext → SrcContext

namespace SrcContext

/-- Filling the hole. -/
def fill : SrcContext → Src → Src
  | hole, body => body
  | parLeft ctx right, body => .par (ctx.fill body) right
  | parRight left ctx, body => .par left (ctx.fill body)
  | outBody name ctx, body => .out name (ctx.fill body)
  | inpBody name ctx, body => .inp name (ctx.fill body)

/-- The slot footprint of a filled context, as a function of the body's. -/
def slotsUsed : SrcContext → ℕ → ℕ
  | hole, bodySlots => bodySlots
  | parLeft ctx right, bodySlots => ctx.slotsUsed bodySlots + right.slotsUsed
  | parRight left ctx, bodySlots => left.slotsUsed + ctx.slotsUsed bodySlots
  | outBody name ctx, bodySlots => name.slotsUsed + ctx.slotsUsed bodySlots
  | inpBody name ctx, bodySlots => 5 + name.slotsUsed + ctx.slotsUsed bodySlots

/-- **The footprint composes.**  A filled context uses the slots the context
uses, given what the body uses. -/
theorem fill_slotsUsed :
    ∀ (ctx : SrcContext) (body : Src),
      (ctx.fill body).slotsUsed = ctx.slotsUsed body.slotsUsed
  | hole, _ => rfl
  | parLeft ctx right, body => by
      simp only [fill, slotsUsed, Src.slotsUsed, fill_slotsUsed ctx body]
  | parRight left ctx, body => by
      simp only [fill, slotsUsed, Src.slotsUsed, fill_slotsUsed ctx body]
  | outBody name ctx, body => by
      simp only [fill, slotsUsed, Src.slotsUsed, fill_slotsUsed ctx body]
  | inpBody name ctx, body => by
      simp only [fill, slotsUsed, Src.slotsUsed, fill_slotsUsed ctx body]

end SrcContext

/-! ## The translation of a context -/

/-- **A context's translation.**  The hole is a function of the proxies and
offset it sits at, because that is what a source term's translation depends on.
The body's slot footprint is a separate parameter: a parallel composition needs
it to place its right-hand side in a disjoint range. -/
def translateContext (s : Comb) :
    SrcContext → List Comb → ℕ → ℕ → (List Comb → ℕ → Comb) → Comb
  | .hole, proxies, offset, _, plug => plug proxies offset
  | .parLeft ctx right, proxies, offset, bodySlots, plug =>
      par (translateContext s ctx proxies offset bodySlots plug)
        (translate s proxies right (offset + ctx.slotsUsed bodySlots))
  | .parRight left ctx, proxies, offset, bodySlots, plug =>
      par (translate s proxies left offset)
        (translateContext s ctx proxies (offset + left.slotsUsed) bodySlots plug)
  | .outBody name ctx, proxies, offset, bodySlots, plug =>
      mm (translateName s proxies name offset)
        (translateContext s ctx proxies (offset + name.slotsUsed) bodySlots plug)
  | .inpBody name ctx, proxies, offset, bodySlots, plug =>
      par (dd (translateName s proxies name (offset + 5)) (slot s offset)
            (slot s (offset + 1)))
        (par (gate (slot s offset) (slot s (offset + 2)) (slot s (offset + 3))
              (translateContext s ctx (slot s (offset + 4) :: proxies)
                (offset + 5 + name.slotsUsed) bodySlots plug))
          (fw (slot s (offset + 1)) (slot s (offset + 4))))

/-! ## Compositionality -/

/-- **`⟦C[P]⟧ = ⟦C⟧[⟦P⟧]`.**  The translation of a filled context is the
context's translation with the body's translation plugged in at the proxies and
offset the hole sits at.  The body reaches the context in exactly two ways —
through the plug, and through its slot footprint. -/
theorem translate_fill (s : Comb) :
    ∀ (ctx : SrcContext) (proxies : List Comb) (body : Src) (offset : ℕ),
      translate s proxies (ctx.fill body) offset
        = translateContext s ctx proxies offset body.slotsUsed
            (fun proxies' offset' => translate s proxies' body offset')
  | .hole, _, _, _ => rfl
  | .parLeft ctx right, proxies, body, offset => by
      simp only [SrcContext.fill, translate, translateContext,
        translate_fill s ctx proxies body offset, SrcContext.fill_slotsUsed]
  | .parRight left ctx, proxies, body, offset => by
      simp only [SrcContext.fill, translate, translateContext,
        translate_fill s ctx proxies body (offset + left.slotsUsed)]
  | .outBody name ctx, proxies, body, offset => by
      simp only [SrcContext.fill, translate, translateContext,
        translate_fill s ctx proxies body (offset + name.slotsUsed)]
  | .inpBody name ctx, proxies, body, offset => by
      simp only [SrcContext.fill, translate, translateContext,
        translate_fill s ctx (slot s (offset + 4) :: proxies) body
          (offset + 5 + name.slotsUsed)]

/-! ## Substitutivity -/

/-- **Two bodies with the same translation and the same slot footprint are
interchangeable in every context.**  This is the property compositionality
exists to give, and the one a full-abstraction argument needs. -/
theorem translate_fill_congr (s : Comb) (ctx : SrcContext) (proxies : List Comb)
    (first second : Src) (offset : ℕ)
    (hslots : first.slotsUsed = second.slotsUsed)
    (htranslate : ∀ (proxies' : List Comb) (offset' : ℕ),
      translate s proxies' first offset' = translate s proxies' second offset') :
    translate s proxies (ctx.fill first) offset
      = translate s proxies (ctx.fill second) offset := by
  rw [translate_fill s ctx proxies first offset,
    translate_fill s ctx proxies second offset, hslots]
  congr 1
  funext proxies' offset'
  exact htranslate proxies' offset'

/-- The footprint hypothesis is not incidental: a filled context's own footprint
is determined by the body's, so two bodies with different footprints place the
surrounding code differently. -/
theorem fill_slotsUsed_congr (ctx : SrcContext) (first second : Src)
    (hslots : first.slotsUsed = second.slotsUsed) :
    (ctx.fill first).slotsUsed = (ctx.fill second).slotsUsed := by
  rw [SrcContext.fill_slotsUsed, SrcContext.fill_slotsUsed, hslots]

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
