/-
# The translation, and its atom count

The lane's §2 headline is that the reflective encoding is **linear in the atom
count of the source** while prefix distribution is exponential. Until now that
was arithmetic over two recurrences in `Blowup.lean` — a statement about two
counting functions, not about a compiler. The scope review said so plainly:
*"there is not yet a general encoding whose measured output is proved to have
those counts."*

This file supplies the compiler and the measurement.

`Src` is reflective rho with de Bruijn-indexed bound names: nil, parallel
composition, output, input, and drop, with names being either a quotation or a
bound index. `translate` compiles it.

## Why the count comes out linear

The mechanism is the one the draft identifies and `gate_releases` proves: an
input's continuation is **stored as a name**, not distributed through the body.
So the body contributes *nothing* to the enclosing soup's atom count — a `qq`
holding an arbitrarily large quotation is one atom. An input therefore costs a
fixed five atoms whatever its body:

```
    dd    split the arriving name             1
    gate  hold and release the continuation   3
    fw    deliver the name to the body        1
```

and `storedAtoms_translate_le` is the consequence: `atoms (translate P) ≤ 5 · |P|`,
by structural induction, with no multiplicative factor anywhere because nothing
nests.

That is the whole content of the linearity claim, and it is why it is a theorem
about the *mechanism* rather than about a particular encoding of occurrences.

## What the count means

A count alone would be worth little, so `translate_inp_releases` gives it
meaning: supplied with a message at the input's subject, the translation of an
input **releases the body and delivers the received name to the body's proxy**.
It composes from `gate_releases`, the duplicator, and a forwarder.

## The affine boundary, stated

One forwarder delivers the received name to one proxy, so the translation is
correct as it stands when a bound name is used **at most once** in its body.
Several uses contend for one message, which is the duplication problem — and it
is the same boundary `compileSkeleton_linear` draws, resolved the same way, by a
distributor. That composition is not performed here.

Full simulation — that the translation preserves the source's reduction under
substitution — is **not** proved. What is proved is the size law, the release
mechanism, and the separation below.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Blowup
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Gate
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.NameGrowth

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## The source -/

mutual

/-- Reflective rho: names are quotations, bound names are de Bruijn indices. -/
inductive Src where
  | nil : Src
  | par : Src → Src → Src
  | out : SrcName → Src → Src
  | inp : SrcName → Src → Src
  | drop : SrcName → Src

/-- A source name: a quotation, or a name bound by an enclosing input. -/
inductive SrcName where
  | quote : Src → SrcName
  | bvar : ℕ → SrcName

end

mutual

def Src.size : Src → ℕ
  | Src.nil => 1
  | Src.par p q => 1 + p.size + q.size
  | Src.out n p => 1 + n.size + p.size
  | Src.inp n p => 1 + n.size + p.size
  | Src.drop n => 1 + n.size

def SrcName.size : SrcName → ℕ
  | SrcName.quote p => 1 + p.size
  | SrcName.bvar _ => 1

end

mutual

theorem Src.one_le_size : ∀ p : Src, 1 ≤ p.size
  | Src.nil => le_refl _
  | Src.par p q => by simp only [Src.size]; omega
  | Src.out n p => by simp only [Src.size]; omega
  | Src.inp n p => by simp only [Src.size]; omega
  | Src.drop n => by simp only [Src.size]; omega

theorem SrcName.one_le_size : ∀ n : SrcName, 1 ≤ n.size
  | SrcName.quote p => by simp only [SrcName.size]; omega
  | SrcName.bvar _ => le_refl _

end

/-! ## Slot accounting -/

mutual

/-- How many slots a translated term reserves: five per input. -/
def Src.slotsUsed : Src → ℕ
  | Src.nil => 0
  | Src.par p q => p.slotsUsed + q.slotsUsed
  | Src.out n p => n.slotsUsed + p.slotsUsed
  | Src.inp n p => 5 + n.slotsUsed + p.slotsUsed
  | Src.drop n => n.slotsUsed

def SrcName.slotsUsed : SrcName → ℕ
  | SrcName.quote p => p.slotsUsed
  | SrcName.bvar _ => 0

end

/-! ## The translation -/

mutual

/-- **The translation.**  An input becomes a duplicator, a gate holding the
translated body as a stored name, and a forwarder delivering the received name
to the body's proxy.  The body is a name, so it adds nothing to this soup. -/
def translate (s : Comb) (proxies : List Comb) : Src → ℕ → Comb
  | .nil, _ => nil
  | .par p q, offset =>
      par (translate s proxies p offset)
        (translate s proxies q (offset + p.slotsUsed))
  | .out n p, offset =>
      mm (translateName s proxies n offset)
        (translate s proxies p (offset + n.slotsUsed))
  | .drop n, offset => ev (translateName s proxies n offset)
  | .inp n p, offset =>
      par (dd (translateName s proxies n (offset + 5)) (slot s offset)
            (slot s (offset + 1)))
        (par (gate (slot s offset) (slot s (offset + 2)) (slot s (offset + 3))
              (translate s (slot s (offset + 4) :: proxies) p
                (offset + 5 + n.slotsUsed)))
          (fw (slot s (offset + 1)) (slot s (offset + 4))))

/-- A source name becomes a target name: a quotation becomes the translated
process, a bound index becomes the proxy its binder allocated. -/
def translateName (s : Comb) (proxies : List Comb) : SrcName → ℕ → Comb
  | .quote p, offset => translate s proxies p offset
  | .bvar index, _ => proxies.getD index nil

end

/-! ## Counting stored code

`atomCount` counts the atoms of a soup — the ones that can react *now*.  It does
not count a continuation held inside a `qq` or a payload carried by a message,
because those are names rather than running atoms.  That distinction is the
mechanism, and it deserves both measures.

`storedAtoms` is the hereditary count: it descends into a stored continuation
and into a message's payload, so it counts every atom the program will ever run.
It is the measure the published comparison uses.
-/

/-- Every atom the program will ever run: the soup's own, plus those held in
stored continuations and message payloads. -/
def storedAtoms : Comb → ℕ
  | nil => 0
  | par p q => storedAtoms p + storedAtoms q
  | qq _ p => 1 + storedAtoms p
  | mm _ p => 1 + storedAtoms p
  | _ => 1

/-! ## The size law -/

/-- **The translation is linear in the source.**  Five atoms per input, one per
output and per drop, and the body counted once — never multiplied, because a
body is *stored* rather than distributed through the enclosing soup. -/
theorem storedAtoms_translate_le (s : Comb) :
    ∀ (proxies : List Comb) (p : Src) (offset : ℕ),
      storedAtoms (translate s proxies p offset) ≤ 5 * p.size
  | _, .nil, _ => by simp [storedAtoms, translate, Src.size]
  | proxies, .par p q, offset => by
      have ihp := storedAtoms_translate_le s proxies p offset
      have ihq := storedAtoms_translate_le s proxies q (offset + p.slotsUsed)
      simp only [storedAtoms, translate, Src.size] at ihp ihq ⊢
      omega
  | proxies, .out n p, offset => by
      have ihp := storedAtoms_translate_le s proxies p (offset + n.slotsUsed)
      have hn := SrcName.one_le_size n
      simp only [storedAtoms, translate, Src.size] at ihp ⊢
      omega
  | proxies, .drop n, offset => by
      have hn := SrcName.one_le_size n
      have hp := Src.one_le_size
      simp only [storedAtoms, translate, Src.size]
      omega
  | proxies, .inp n p, offset => by
      have ihp := storedAtoms_translate_le s (slot s (offset + 4) :: proxies) p
        (offset + 5 + n.slotsUsed)
      have hn := SrcName.one_le_size n
      simp only [storedAtoms, translate, gate, Src.size] at ihp ⊢
      omega

/-! ## What the count means: an input releases its body -/

/-- **The translation of an input releases the body and delivers the received
name.**  Supplied with a message at the input's subject, the soup reaches the
translated body running beside a message carrying the received name at the
body's proxy.  This is the mechanism the size law is about: the body travels as
stored code, and the received name reaches it through a forwarder. -/
theorem translate_inp_releases (_s subject trigger split store run proxy body value : Comb) :
    Reaches
      (par (par (dd subject trigger split) (par (gate trigger store run body)
          (fw split proxy))) (mm subject value))
      (par body (mm proxy value)) := by
  have ac : ∀ u v : Comb, components u = components v → Cong u v :=
    fun _ _ h => cong_of_components h
  -- split the arriving name to the gate's trigger and to the forwarder
  refine Reaches.trans (Reaches.congruent (ac _
    (par (par (dd subject trigger split) (mm subject value))
      (par (gate trigger store run body) (fw split proxy)))
    (by simp only [components, gate]; ac_rfl))) ?_
  refine Reaches.trans (Reaches.parLeft _
    (Reaches.single (StepMinus.duplicate trigger split value (Cong.refl subject)))) ?_
  -- release the body
  refine Reaches.trans (Reaches.congruent (ac _
    (par (par (gate trigger store run body) (mm trigger value))
      (par (mm split value) (fw split proxy)))
    (by simp only [components, gate]; ac_rfl))) ?_
  refine Reaches.trans (Reaches.parLeft _
    (gate_releases trigger store run body value)) ?_
  -- deliver the received name to the proxy
  refine Reaches.trans (Reaches.congruent (ac _
    (par (par (fw split proxy) (mm split value)) body)
    (by simp only [components]; ac_rfl))) ?_
  refine Reaches.trans (Reaches.parLeft _
    (Reaches.single (StepMinus.forward proxy value (Cong.refl split)))) ?_
  exact Reaches.congruent (ac _ _ (by simp only [components]; ac_rfl))

/-! ## The separation, as a statement about the compiler -/

/-- `d` nested inputs, each body the next. -/
def nestedInputs : ℕ → Src
  | 0 => .nil
  | d + 1 => .inp (.quote .nil) (nestedInputs d)

theorem size_nestedInputs : ∀ d : ℕ, (nestedInputs d).size = 3 * d + 1
  | 0 => rfl
  | d + 1 => by
      have ih := size_nestedInputs d
      simp only [nestedInputs, Src.size, SrcName.size] at ih ⊢
      omega

/-- **The running soup of nested inputs is five atoms, whatever the depth.**
This is the mechanism in its sharpest form: every body is held as a name, so the
soup that can react now does not grow with nesting at all. -/
theorem atomCount_translate_nestedInputs (s : Comb) :
    ∀ (proxies : List Comb) (d : ℕ) (offset : ℕ),
      atomCount (translate s proxies (nestedInputs (d + 1)) offset) = 5
  | _, _, _ => by
      simp [atomCount, translate, nestedInputs, gate, componentList]

/-- **And the total, counting stored code, is linear in the depth.**  Five atoms
per input, hereditarily — the measure the published comparison uses. -/
theorem storedAtoms_translate_nestedInputs (s : Comb) :
    ∀ (proxies : List Comb) (d : ℕ) (offset : ℕ),
      storedAtoms (translate s proxies (nestedInputs d) offset) = 5 * d
  | _, 0, _ => by simp [storedAtoms, translate, nestedInputs]
  | proxies, d + 1, offset => by
      have ih := storedAtoms_translate_nestedInputs s
        (slot s (offset + 4) :: proxies) d (offset + 5 + 0)
      simp only [nestedInputs, translate, storedAtoms, gate,
        SrcName.slotsUsed, Src.slotsUsed] at ih ⊢
      omega

/-- **The separation, now about the compiler rather than about two
recurrences.**  On the nested-input family the translation emits `5 * d` atoms
in total while prefix distribution needs `(3 ^ d + 1) / 2`;
`two_mul_distributedAtoms` is the division-free form of the second, and
`reflective_lt_distributed` the crossover.  The middle conjunct is the reason:
the soup that runs at any moment is five atoms, independent of `d`, because the
bodies are stored rather than pushed through one another. -/
theorem translation_linear_distribution_exponential (s : Comb)
    (proxies : List Comb) (d : ℕ) :
    storedAtoms (translate s proxies (nestedInputs d) 0) = 5 * d
      ∧ atomCount (translate s proxies (nestedInputs (d + 1)) 0) = 5
      ∧ 2 * distributedAtoms d = 3 ^ d + 1 :=
  ⟨storedAtoms_translate_nestedInputs s proxies d 0,
    atomCount_translate_nestedInputs s proxies d 0,
    two_mul_distributedAtoms d⟩

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
