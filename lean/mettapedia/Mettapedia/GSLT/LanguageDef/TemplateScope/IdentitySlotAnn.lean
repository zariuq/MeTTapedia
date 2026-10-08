import Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotRelation
import Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFresh
import Mettapedia.GSLT.LanguageDef.TemplateScope.QuotePatternEmbed

/-!
# Template scope: the slot model and the identity model, statically related

Rule M and lexical fresh each have two elaborations: the slot model's
(`elabMS`, `elabLF`: names are slots `(owner, spelling)`, a `let` that
introduces names and a `new` block are activations) and the identity model's
(`elabMId`, `elabLFId`: names are binder identities, every binder is allocated
in its frame).  Both elaborations of one profile take the same decisions: which
names a lambda owns, which names a `let` introduces, which names a `new` block
declares.  `Ann` records those decisions (an annotated text); `Ann.slotOf` and
`Ann.idOf` are the two elaborations of an annotated text.

The main result, `rel_ann`, relates `slotOf` and `idOf` by `IdSlot.Rel` in the
setting `SC` (sealed code related through `codeOf` and `codeI`), on every
well-formed annotated text: the identity of every name a lambda owns is apart
from every frame-allocated name of its body that is live, and the reserved
names of pending activations are distinct.

## The conditions

* A pattern quotation is code. A hole is an outer name, so the free-name claim
  is the same claim as for any pattern. A binder of the code, and a free
  parameter of the code, is named inside the code and related by `CodeRel`.
* No `new` block with names on the matched spine of a pattern.
* The identity of every name a lambda owns is its frame's head, a `new` at the
  frame's body, or a pattern that is not an activation (`KeyOK`).
* The resolution environment and the owners a scope writes are scope owners:
  not a binder of code, and not a free parameter of code.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

namespace IdSlot

variable {S : Type u} {X : Type v}

/-! ## Annotated text -/

/-- Authored text with an elaboration's decisions recorded: the names each
lambda owns with their identities, the names each `let` introduces (`letA`,
nonempty), the names each `new` block declares. -/
inductive Ann (S : Type u) (X : Type v) where
  | sym (s : S)
  | fn (F : S)
  | sv (y : X)
  | par (z : X)
  | lam (z : X) (own : List X) (key : X → SlotId X) (body : Ann S X)
  | app (f a : Ann S X)
  | quote (c : Src S X)
  | pquote (c : Src S X)
  | letP (p w b : Ann S X)
  | letA (y₀ : X) (ys : List X) (p w b : Ann S X)
  | alt (t₁ t₂ : Ann S X)
  | new (ys : List X) (body : Ann S X)

namespace Ann

/-- The spellings written, outside sealed code. -/
def names : Ann S X → List X
  | .sv y => [y]
  | .lam _ _ _ b => names b
  | .app f a => names f ++ names a
  | .pquote c => Src.names c
  | .letP p w b => names p ++ names w ++ names b
  | .letA _ _ p w b => names p ++ names w ++ names b
  | .alt t₁ t₂ => names t₁ ++ names t₂
  | .new _ b => names b
  | _ => []

/-- The `new` blocks with names are off the matched spine. -/
def NewFree : Ann S X → Prop
  | .app f a => NewFree f ∧ NewFree a
  | .pquote _ => True
  | .letP p _ _ => NewFree p
  | .letA _ _ p _ _ => NewFree p
  | .new [] b => NewFree b
  | .new (_ :: _) _ => False
  | _ => True

/-- A `let` that introduces names sits at the relative position (a `new` block
is not a position of its own). -/
def LetAAt : Ann S X → Owner → Prop
  | .new _ b, P => LetAAt b P
  | .letA _ _ _ _ _, [] => True
  | .app f _, 0 :: P => LetAAt f P
  | .app _ a, 1 :: P => LetAAt a P
  | .letP p _ _, 0 :: P => LetAAt p P
  | .letP _ w _, 1 :: P => LetAAt w P
  | .letP _ _ b, 2 :: P => LetAAt b P
  | .letA _ _ p _ _, 0 :: P => LetAAt p P
  | .letA _ _ _ w _, 1 :: P => LetAAt w P
  | .letA _ _ _ _ b, 2 :: P => LetAAt b P
  | .alt t _, 0 :: P => LetAAt t P
  | .alt _ u, 1 :: P => LetAAt u P
  | _, _ => False

end Ann

/-- **An admissible identity for a name a frame owns**, the frame's body being
`b` at `F`: the frame's head, a `new` at the frame's body, or a pattern of the
body that is not an activation. -/
def KeyOK (F : Owner) (b : Ann S X) (k : SlotId X) : Prop :=
  k.intro = .head ∨ (k.intro = .new ∧ k.site = F) ∨
    (k.intro = .pat ∧ ∃ P, k.site = F ++ P ∧ ¬ b.LetAAt P)

namespace Ann

variable [DecidableEq X]

/-- **Well-formed annotated text** at the identity position `pos`: patterns
without `new` blocks on their spine, admissible identities for every lambda's
own names, and, for a pattern quotation, one `CodeRel` between the two
elaborations. A hole is a free name of that code. A binder of the code and a
free parameter of the code are named inside it, so the relation's one map
sends both, and neither is a free name of the sealed quotation. -/
def WF : Owner → Ann S X → Prop
  | pos, .lam _ own key b =>
      (∀ y ∈ own, (key y).spell = y ∧ (key y).frame = pos ++ [0] ∧ KeyOK (pos ++ [0]) b (key y)) ∧
        WF (pos ++ [0]) b
  | pos, .app f a => WF (pos ++ [0]) f ∧ WF (pos ++ [1]) a
  | _, .pquote c =>
      ∀ (env : REnv X) (envI : IEnv X),
        (∀ y, codeBound (env y) = false) → (∀ y, env y ≠ codeFreeParam) →
        CodeRel (R₁ := fun (_ : Slot X) => True) (R₂ := fun (_ : BId X) => True)
          codeQ (fun _ => True) (codeMapHoles env envI)
          (sealParams (codeAt (some env) [] [] [] c))
          (sealParams (codeIAt (some envI) [] [] [] c))
  | pos, .letP p w b => p.NewFree ∧ WF (pos ++ [0]) p ∧ WF (pos ++ [1]) w ∧ WF (pos ++ [2]) b
  | pos, .letA _ _ p w b => p.NewFree ∧ WF (pos ++ [0]) p ∧ WF (pos ++ [1]) w ∧ WF (pos ++ [2]) b
  | pos, .alt t₁ t₂ => WF (pos ++ [0]) t₁ ∧ WF (pos ++ [1]) t₂
  | pos, .new _ b => WF pos b
  | _, _ => True

/-- Annotated text whose holes are outer names. A pattern quotation is open
when every free name of its sealed elaboration is the surrounding scope's
slot of a spelling written in the code. Code binders are not free names. -/
def Open : Ann S X → Prop
  | .lam _ _ _ b => Open b
  | .app f a => Open f ∧ Open a
  | .pquote c =>
      ∀ (env : REnv X) (n : Nm (Slot X)),
        n ∈ freeNames (sealParams (codeAt (some env) [] [] [] c)) →
        ∃ y ∈ Src.names c, n = .src (env y, y)
  | .letP p w b => Open p ∧ Open w ∧ Open b
  | .letA _ _ p w b => Open p ∧ Open w ∧ Open b
  | .alt t₁ t₂ => Open t₁ ∧ Open t₂
  | .new _ b => Open b
  | _ => True

theorem Open.of_WF {pos : Owner} {t : Ann S X} (h : t.WF pos) : t.Open := by
  induction t generalizing pos with
  | pquote c =>
      intro env n hn
      rw [freeNames_sealParams] at hn
      exact mem_freeNames_codeAt env [] [] [] c n hn
  | lam _ _ _ _ ih =>
      simp only [WF] at h
      exact ih h.2
  | app _ _ ihf iha =>
      simp only [WF] at h
      exact ⟨ihf h.1, iha h.2⟩
  | letP _ _ _ ihp ihw ihb =>
      simp only [WF] at h
      exact ⟨ihp h.2.1, ihw h.2.2.1, ihb h.2.2.2⟩
  | letA _ _ _ _ _ ihp ihw ihb =>
      simp only [WF] at h
      exact ⟨ihp h.2.1, ihw h.2.2.1, ihb h.2.2.2⟩
  | alt _ _ ih₁ ih₂ =>
      simp only [WF] at h
      exact ⟨ih₁ h.1, ih₂ h.2⟩
  | new _ _ ih =>
      simp only [WF] at h
      exact ih h
  | sym _ => trivial
  | fn _ => trivial
  | sv _ => trivial
  | par _ => trivial
  | quote _ => trivial

/-- Parameters of authored text not bound by one of its lambdas. -/
def srcFreePars : Src S X → List X
  | .par z => [z]
  | .lam z _ b => (srcFreePars b).filter fun z' => decide (z' ≠ z)
  | .form z b => (srcFreePars b).filter fun z' => decide (z' ≠ z)
  | .app f a => srcFreePars f ++ srcFreePars a
  | .pquote c => srcFreePars c
  | .letS p w b _ => srcFreePars p ++ srcFreePars w ++ srcFreePars b
  | .unify p w b => srcFreePars p ++ srcFreePars w ++ srcFreePars b
  | .alt t₁ t₂ => srcFreePars t₁ ++ srcFreePars t₂
  | .new _ b => srcFreePars b
  | _ => []

/-- Parameters not bound in the text, outside sealed code. -/
def freePars : Ann S X → List X
  | .par z => [z]
  | .lam z _ _ b => (freePars b).filter fun z' => decide (z' ≠ z)
  | .app f a => freePars f ++ freePars a
  | .pquote c => srcFreePars c
  | .letP p w b => freePars p ++ freePars w ++ freePars b
  | .letA _ _ p w b => freePars p ++ freePars w ++ freePars b
  | .alt t₁ t₂ => freePars t₁ ++ freePars t₂
  | .new _ b => freePars b
  | _ => []

/-! ## The two elaborations of annotated text -/

/-- **The slot model**: names are slots; a lambda owns its names as slots of its
body's position; a `let` that introduces names and a `new` block are
activations. -/
def slotOf (env : REnv X) (pos : Owner) : Ann S X → Tm S (Slot X)
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => slotVar env y
  | .par z => .pvar (parName z)
  | .lam z own _ b =>
      .lam (parName z) (own.map fun y => (pos ++ [0], y))
        (slotOf (env.update own (pos ++ [0])) (pos ++ [0]) b)
  | .app f a => .app (slotOf env (pos ++ [0]) f) (slotOf env (pos ++ [1]) a)
  | .quote c => .quote (codeOf c)
  | .pquote c => .pquote (sealParams (codeAt (some env) [] [] [] c))
  | .letP p w b =>
      .letP (slotOf env (pos ++ [0]) p) (slotOf env (pos ++ [1]) w) (slotOf env (pos ++ [2]) b)
  | .letA y₀ ys p w b =>
      .app
        (.lam (letParam (pos ++ [2]) y₀) ((y₀ :: ys).map fun y => (pos ++ [2], y))
          (.letP (slotOf (env.update (y₀ :: ys) (pos ++ [2])) (pos ++ [0]) p)
            (.pvar (letParam (pos ++ [2]) y₀))
            (slotOf (env.update (y₀ :: ys) (pos ++ [2])) (pos ++ [2]) b)))
        (slotOf env (pos ++ [1]) w)
  | .alt t₁ t₂ => .alt (slotOf env (pos ++ [0]) t₁) (slotOf env (pos ++ [1]) t₂)
  | .new [] b => slotOf env (pos ++ [0]) b
  | .new (y₀ :: ys) b =>
      newBlock pos y₀ ys (slotOf (env.update (y₀ :: ys) (pos ++ [0])) (pos ++ [0]) b)

/-- **The identity model**: names are binder identities; every binder is
allocated in its frame (`fr`), and a lambda's own list is its frame's slots
that occur in its body. -/
def idOf (env : IEnv X) (pv : X → Owner) (fr pos : Owner) : Ann S X → Tm S (BId X)
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => iVar (env y)
  | .par z => .pvar (.src (.par z (pv z)))
  | .lam z own key b =>
      .lam (.src (.par z pos))
        (frameSlots (pos ++ [0]) (idOf (env.set own key) (pvSet pv z pos) (pos ++ [0]) (pos ++ [0]) b))
        (idOf (env.set own key) (pvSet pv z pos) (pos ++ [0]) (pos ++ [0]) b)
  | .app f a => .app (idOf env pv fr (pos ++ [0]) f) (idOf env pv fr (pos ++ [1]) a)
  | .quote c => .quote (codeI c)
  | .pquote c => .pquote (sealParams (codeIAt (some env) [] [] [] c))
  | .letP p w b =>
      .letP (idOf env pv fr (pos ++ [0]) p) (idOf env pv fr (pos ++ [1]) w)
        (idOf env pv fr (pos ++ [2]) b)
  | .letA y₀ ys p w b =>
      .letP (idOf (env.set (y₀ :: ys) fun y => ⟨y, fr, pos, .pat⟩) pv fr (pos ++ [0]) p)
        (idOf env pv fr (pos ++ [1]) w)
        (idOf (env.set (y₀ :: ys) fun y => ⟨y, fr, pos, .pat⟩) pv fr (pos ++ [2]) b)
  | .alt t₁ t₂ => .alt (idOf env pv fr (pos ++ [0]) t₁) (idOf env pv fr (pos ++ [1]) t₂)
  | .new ys b => idOf (env.set ys fun y => ⟨y, fr, pos, .new⟩) pv fr pos b

end Ann

/-! ## The setting -/

/-- A free parameter of code, on the slot side. -/
def codeFreeS : Nm (Slot X) → Bool
  | .src (o, _) => decide (o = codeFreeParam)
  | .inst _ n => codeFreeS n

/-- A free parameter of code, on the identity side. -/
def codeFreeI : Nm (BId X) → Bool
  | .src (.code _ o) => decide (o = codeFreeParam)
  | .inst _ n => codeFreeI n
  | _ => false

/-- The owner written on a slot name. -/
def ownerS : Nm (Slot X) → Owner
  | .src (o, _) => o
  | .inst _ n => ownerS n

/-- The owner written on a name of code. A slot or a scope parameter has none. -/
def ownerI : Nm (BId X) → Owner
  | .src (.code _ o) => o
  | .inst _ n => ownerI n
  | _ => []

/-- The spelling of a slot name. -/
def spellS : Nm (Slot X) → X
  | .src (_, y) => y
  | .inst _ n => spellS n

/-- The spelling of an identity. -/
def spellI : Nm (BId X) → X
  | .src (.slot k) => k.spell
  | .src (.par z _) => z
  | .src (.code y _) => y
  | .inst _ n => spellI n

/-- A name of the code: a binder, or a free parameter. An activation copy is not. -/
def codeParamS : Nm (Slot X) → Prop
  | .src (o, _) => codeBound o = true ∨ o = codeFreeParam
  | .inst _ _ => False

/-- The same on the identity side. A slot or a scope parameter is not. -/
def codeParamI : Nm (BId X) → Prop
  | .src (.code _ o) => codeBound o = true ∨ o = codeFreeParam
  | _ => False

/-- Holes that `matchCode` treats alike. Two free parameters of code agree by
spelling. Two scope holes agree without a spelling. A free parameter of code
and a scope hole do not. -/
def holeMatch (n₁ : Nm (Slot X)) (n₂ : Nm (BId X)) : Prop :=
  (codeFreeS n₁ = true ∧ codeFreeI n₂ = true ∧ spellS n₁ = spellI n₂) ∨
    (codeFreeS n₁ = false ∧ codeFreeI n₂ = false)

/-- Whether a slot name is a hole, copying the code-identity equation on
constructors and recurring under an activation. `CodeId.hole` recurses the
same way, so an activation copy of a binder stays a binder. -/
def holeRecS : Nm (Slot X) → Bool
  | .src (o, _) => !codeBound o
  | .inst _ n => holeRecS n

/-- The same for an identity. A slot and a scope parameter are holes. -/
def holeRecI : Nm (BId X) → Bool
  | .src (.code _ o) => !codeBound o
  | .src _ => true
  | .inst _ n => holeRecI n

/-- `CodeId.hole` on a slot is the hole bit `holeRecS` uses. -/
theorem slotHole_eq_holeRecS : ∀ n : Nm (Slot X), slotHole n = holeRecS n
  | .src _ => rfl
  | .inst _ n => slotHole_eq_holeRecS n

/-- `CodeId.hole` on an identity is the hole bit `holeRecI` uses. -/
theorem bIdHole_eq_holeRecI : ∀ n : Nm (BId X), bIdHole n = holeRecI n
  | .src (.code _ _) => rfl
  | .src (.slot _) => rfl
  | .src (.par _ _) => rfl
  | .inst _ n => bIdHole_eq_holeRecI n

theorem hole_eq_holeRecS [DecidableEq X] (n : Nm (Slot X)) :
    CodeId.hole n = holeRecS n :=
  slotHole_eq_holeRecS n

theorem hole_eq_holeRecI [DecidableEq X] (n : Nm (BId X)) :
    CodeId.hole n = holeRecI n :=
  bIdHole_eq_holeRecI n

/-- An activation copy keeps the hole bit, on both models. -/
theorem hole_instL [DecidableEq X] (ρ : Path) (n : Nm (Slot X)) :
    CodeId.hole (.inst ρ n) = CodeId.hole n := rfl

theorem hole_instI [DecidableEq X] (ρ : Path) (n : Nm (BId X)) :
    CodeId.hole (.inst ρ n) = CodeId.hole n := rfl

/-- Store names are holes together, or binders of code together. -/
def scVarHole (n₁ : Nm (Slot X)) (n₂ : Nm (BId X)) : Prop :=
  holeRecS n₁ = holeRecI n₂

/-- Parameters of code share an owner. Parameters of the scope are neither. -/
def scParOK (x₁ : Nm (Slot X)) (x₂ : Nm (BId X)) : Prop :=
  (codeParamS x₁ ∧ codeParamI x₂ ∧ ownerS x₁ = ownerI x₂) ∨
    (¬ codeParamS x₁ ∧ ¬ codeParamI x₂)

/-- Written as a source name, rather than as an activation copy.
`CodeId.same` does not look through a copy, so two binders `matchCode` may
enter are both originals or both copies. -/
def actSrcS : Nm (Slot X) → Bool
  | .src _ => true
  | .inst _ _ => false

/-- The same on the identity side. -/
def actSrcI : Nm (BId X) → Bool
  | .src _ => true
  | .inst _ _ => false

/-- A scope binder is a hole at any own lists. A free parameter of code is a
hole that owns nothing and agrees by spelling. A binder of code is not a hole,
owns nothing, and shares an owner. The two names are both originals or both
activation copies. -/
def scBare (x₁ : Nm (Slot X)) (own₁ : List (Slot X)) (x₂ : Nm (BId X))
    (own₂ : List (BId X)) : Prop :=
  (holeRecS x₁ = true ∧ holeRecI x₂ = true ∧ holeMatch x₁ x₂ ∧
      ((codeFreeS x₁ = true ∧ codeFreeI x₂ = true) → own₁ = [] ∧ own₂ = []) ∧
      actSrcS x₁ = actSrcI x₂) ∨
    (holeRecS x₁ = false ∧ holeRecI x₂ = false ∧ own₁ = [] ∧ own₂ = [] ∧
      ownerS x₁ = ownerI x₂ ∧ actSrcS x₁ = actSrcI x₂)

/-- `matchCode` enters a lambda when both binders are binders of code, and when
both are free parameters of code with one spelling. A scope hole is not entered. -/
def scEnter (x₁ : Nm (Slot X)) (x₂ : Nm (BId X)) : Prop :=
  (holeRecS x₁ = false ∧ holeRecI x₂ = false) ∨
    (codeFreeS x₁ = true ∧ codeFreeI x₂ = true ∧ spellS x₁ = spellI x₂)

/-- A free parameter of code is a hole: its owner is not a binder. -/
theorem holeRecS_of_codeFree {n : Nm (Slot X)} (h : codeFreeS n = true) :
    holeRecS n = true := by
  induction n with
  | src s =>
      obtain ⟨o, _⟩ := s
      rw [codeFreeS] at h
      rw [holeRecS, of_decide_eq_true h]
      rfl
  | inst _ n ih =>
      rw [codeFreeS] at h
      rw [holeRecS]
      exact ih h

/-- Second-side names that are holes together, or binders of code together. -/
def scPreserve (a b : Nm (BId X)) : Prop :=
  holeRecI a = holeRecI b

/-- An own list excluded by `True` is empty. -/
theorem list_eq_nil_of_not_true {α : Type*} {l : List α} (h : ∀ s ∈ l, ¬ True) : l = [] := by
  cases l with
  | nil => rfl
  | cons s _ => exact absurd trivial (h s List.mem_cons_self)

theorem scEnter_nil {x₁ : Nm (Slot X)} {own₁ : List (Slot X)} {x₂ : Nm (BId X)}
    {own₂ : List (BId X)} (hb : scBare x₁ own₁ x₂ own₂) (he : scEnter x₁ x₂) :
    own₁ = [] ∧ own₂ = [] := by
  rcases he with ⟨hL, _⟩ | ⟨hf₁, hf₂, _⟩
  · rcases hb with ⟨hl, _, _, _, _⟩ | ⟨_, _, e₁, e₂, _, _⟩
    · rw [hL] at hl
      exact absurd hl Bool.false_ne_true
    · exact ⟨e₁, e₂⟩
  · rcases hb with ⟨_, _, hm, hown, _⟩ | ⟨hlS, _, _, _, _, _⟩
    · rcases hm with ⟨_, _, _⟩ | ⟨hc, _⟩
      · exact hown ⟨hf₁, hf₂⟩
      · rw [hf₁] at hc
        exact absurd hc Bool.false_ne_true.symm
    · rw [holeRecS_of_codeFree hf₁] at hlS
      exact absurd hlS Bool.false_ne_true.symm

theorem sc_varHole_instL {n : Nm (Slot X)} {m : Nm (BId X)} (ρ : Path)
    (h : scVarHole n m) : scVarHole (.inst ρ n) m := h

theorem sc_varHole_rename {n : Nm (Slot X)} {m m' : Nm (BId X)}
    (h : scVarHole n m) (p : scPreserve m m') : scVarHole n m' := h.trans p

/-- `codeMapHoles` preserves the hole bit. -/
theorem scVarHole_map [DecidableEq X] (env : REnv X) (envI : IEnv X) :
    ∀ n, scVarHole n (codeMapHoles env envI n)
  | .inst _ n => scVarHole_map env envI n
  | .src (o, y) => by
      by_cases hb : codeBound o = true ∨ o = codeFreeParam
      · rw [codeMapHoles_owned hb, scVarHole, holeRecS, holeRecI]
      · by_cases he : o = env y
        · have hB : codeBound o = false := by
            cases hco : codeBound o
            · rfl
            · exact absurd (Or.inl hco) hb
          simp only [codeMapHoles, if_neg hb, if_pos he, scVarHole, holeRecS, holeRecI]
          rw [hB]
          rfl
        · simp only [codeMapHoles, if_neg hb, if_neg he, scVarHole, holeRecS, holeRecI]

/-- `codeMapHoles` sends parameters of code to parameters of the same owner,
and every other name to a name that is not a parameter of code. -/
theorem scParOK_map [DecidableEq X] (env : REnv X) (envI : IEnv X) :
    ∀ x, scParOK x (codeMapHoles env envI x)
  | .inst _ _ => Or.inr ⟨fun h => h.elim, fun h => h.elim⟩
  | .src (o, y) => by
      by_cases hb : codeBound o = true ∨ o = codeFreeParam
      · rw [codeMapHoles_owned hb]
        exact Or.inl ⟨hb, hb, rfl⟩
      · by_cases he : o = env y
        · simp only [codeMapHoles, if_neg hb, if_pos he]
          exact Or.inr ⟨fun h => hb h, fun h => h.elim⟩
        · simp only [codeMapHoles, if_neg hb, if_neg he]
          exact Or.inr ⟨fun h => hb h, fun h => hb h⟩

/-- An activation copy of a related binder pair stays related. Both sides gain
one copy, so `CodeId.same` still refuses both or accepts both. -/
theorem scBare_inst {ρ : Path} {x : Nm (Slot X)} {m : Nm (BId X)}
    {own₁ : List (Slot X)} {own₂ : List (BId X)} (h : scBare x own₁ m own₂) :
    scBare (.inst ρ x) own₁ (.inst ρ m) own₂ := by
  rcases h with ⟨hS, hI, hm, hown, _⟩ | ⟨hS, hI, e₁, e₂, ho, _⟩
  · refine Or.inl ⟨?_, ?_, ?_, ?_, rfl⟩
    · rw [holeRecS]; exact hS
    · rw [holeRecI]; exact hI
    · rcases hm with ⟨a, b, c⟩ | ⟨a, b⟩
      · exact Or.inl ⟨by rw [codeFreeS]; exact a, by rw [codeFreeI]; exact b,
          by rw [spellS, spellI]; exact c⟩
      · exact Or.inr ⟨by rw [codeFreeS]; exact a, by rw [codeFreeI]; exact b⟩
    · intro hcf
      rw [codeFreeS, codeFreeI] at hcf
      exact hown hcf
  · refine Or.inr ⟨?_, ?_, e₁, e₂, ?_, rfl⟩
    · rw [holeRecS]; exact hS
    · rw [holeRecI]; exact hI
    · rw [ownerS, ownerI]; exact ho

/-- Own lists that `True` excludes are empty, and `codeMapHoles` sends a binder
to a binder `scBare` accepts. -/
theorem scBare_map [DecidableEq X] (env : REnv X) (envI : IEnv X) {x : Nm (Slot X)}
    {own₁ : List (Slot X)} {own₂ : List (BId X)} (h₁ : ∀ s ∈ own₁, ¬ True)
    (h₂ : ∀ s ∈ own₂, ¬ True) : scBare x own₁ (codeMapHoles env envI x) own₂ := by
  have e₁ : own₁ = [] := list_eq_nil_of_not_true h₁
  have e₂ : own₂ = [] := list_eq_nil_of_not_true h₂
  induction x with
  | inst ρ n ih =>
      simpa [codeMapHoles] using scBare_inst (ρ := ρ) ih
  | src s =>
      obtain ⟨o, y⟩ := s
      by_cases hb : codeBound o = true ∨ o = codeFreeParam
      · rw [codeMapHoles_owned hb]
        rcases hb with hb | hf
        · exact Or.inr ⟨by rw [holeRecS, hb]; rfl, by rw [holeRecI, hb]; rfl, e₁, e₂, rfl, rfl⟩
        · refine Or.inl ⟨?_, ?_, Or.inl ⟨?_, ?_, rfl⟩, fun _ => ⟨e₁, e₂⟩, rfl⟩
          · rw [holeRecS, hf]; rfl
          · rw [holeRecI, hf]; rfl
          · rw [codeFreeS, hf]; rfl
          · rw [codeFreeI, hf]; rfl
      · have hB : codeBound o = false := by
          cases hco : codeBound o
          · rfl
          · exact absurd (Or.inl hco) hb
        have hF : o ≠ codeFreeParam := fun h => hb (Or.inr h)
        by_cases he : o = env y
        · simp only [codeMapHoles, if_neg hb, if_pos he]
          refine Or.inl ⟨?_, rfl, Or.inr ⟨?_, rfl⟩, fun hcf => ?_, rfl⟩
          · rw [holeRecS, hB]; rfl
          · rw [codeFreeS]; exact decide_eq_false hF
          · rw [codeFreeS] at hcf
            exact absurd ((decide_eq_false hF).symm.trans hcf.1) Bool.false_ne_true
        · simp only [codeMapHoles, if_neg hb, if_neg he]
          refine Or.inl ⟨?_, ?_, Or.inr ⟨?_, ?_⟩, fun hcf => ?_, rfl⟩
          · rw [holeRecS, hB]; rfl
          · rw [holeRecI, hB]; rfl
          · rw [codeFreeS]; exact decide_eq_false hF
          · rw [codeFreeI]; exact decide_eq_false hF
          · rw [codeFreeS] at hcf
            exact absurd ((decide_eq_false hF).symm.trans hcf.1) Bool.false_ne_true

/-- A scope parameter is a hole on both sides, so the lambda may carry any own
lists and `matchCode` does not enter it. -/
theorem scBare_scope {z : X} {pos : Owner} {own₁ : List (Slot X)} {own₂ : List (BId X)} :
    scBare (parName z) own₁ (.src (.par z pos)) own₂ := by
  refine Or.inl ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩, fun h => ?_, rfl⟩
  have hc : codeFreeS (parName z) = false := rfl
  exact absurd (hc.symm.trans h.1) Bool.false_ne_true

theorem scParOK_scope {z : X} {pos : Owner} :
    scParOK (parName z) (.src (.par z pos)) := by
  refine Or.inr ⟨?_, fun h => h.elim⟩
  intro h
  rcases h with h | h
  · simp [codeBound] at h
  · simp [codeFreeParam] at h

/-- The slot model's code names in the identity model. A query-root hole
`.src ([], y)` is the head slot of that spelling: sealed code and the body's
`$` share that one cell. Every other owner is a code name, so the map stays
injective. Binders of code are never at owner `[]`. -/
def codeFwd : Nm (Slot X) → Nm (BId X)
  | .src ([], y) => .src (.slot ⟨y, [], [], .head⟩)
  | .src ((n :: o), y) => .src (.code y (n :: o))
  | .inst ρ n => .inst ρ (codeFwd n)

/-- The identity model's code names in the slot model. -/
def codeBack : Nm (BId X) → Nm (Slot X)
  | .src (.code y o) => .src (o, y)
  | .src (.slot k) => .src ([], k.spell)
  | .src (.par z _) => .src ([], z)
  | .inst ρ n => .inst ρ (codeBack n)

theorem codeBack_codeFwd : ∀ n : Nm (Slot X), codeBack (codeFwd n) = n
  | .src ([], _) => rfl
  | .src ((_ :: _), _) => rfl
  | .inst _ n => by simp only [codeFwd, codeBack, codeBack_codeFwd n]

theorem codeFwd_injective : Function.Injective (codeFwd : Nm (Slot X) → Nm (BId X)) :=
  Function.LeftInverse.injective codeBack_codeFwd

theorem codeFwd_root (y : X) :
    codeFwd (.src ([], y)) = .src (.slot ⟨y, [], [], .head⟩) := rfl

theorem codeFwd_cons (n : ℕ) (o : List ℕ) (y : X) :
    codeFwd (.src (n :: o, y)) = .src (.code y (n :: o)) := rfl

theorem codeFwd_ne_nil {o : Owner} {y : X} (h : o ≠ []) :
    codeFwd (.src (o, y)) = .src (.code y o) := by
  cases o with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem codeBinder_ne_nil (pos : Owner) : codeBinder pos ≠ [] :=
  List.cons_ne_nil 9 (1 :: pos)

theorem codeFreeParam_ne_nil : (codeFreeParam : Owner) ≠ [] :=
  List.cons_ne_nil 9 []

theorem owner_code_ne_nil {o : Owner}
    (h : codeBound o = true ∨ o = codeFreeParam) : o ≠ [] := by
  rcases h with hb | rfl
  · intro e
    subst e
    simp [codeBound] at hb
  · exact codeFreeParam_ne_nil

/-- **The setting of the two models**: sealed code is related through the two
code maps; the query's own slots (owner `[]`) and identities (frame `[]`) are
the names no binder owns. Holes agree by recurring under an activation. A binder
of code, and a free parameter of code, owns nothing; those are the names
`matchCode` may enter. A scope hole is not entered, at any own lists. -/
def SC [DecidableEq X] : Setting S (Slot X) (BId X) where
  Q c₁ c₂ := ∃ s : Src S X, c₁ = codeOf s ∧ c₂ = codeI s
  root₁ s := s.1 = []
  root₂ b := ∃ k : SlotId X, b = .slot k ∧ k.frame = []
  varHole := scVarHole
  parOK := scParOK
  bareLam := scBare
  enterLam := scEnter
  enter_nil := scEnter_nil
  preserve := scPreserve
  preserve_refl _ := rfl
  preserve_inst _ _ := rfl
  varHole_instL := sc_varHole_instL
  varHole_rename := sc_varHole_rename
  codeMap := codeFwd
  codeMap_inj := codeFwd_injective

variable [DecidableEq X]

/-- Whether matching code can enter this text. A lambda's own result is stable.
A `let` that introduces names, and a `new` block that declares names, are
pending activations. -/
def annOK : Ann S X → Bool
  | .app f a => annOK f && annOK a
  | .letP p w b => annOK p && annOK w && annOK b
  | .letA _ _ _ _ _ => false
  | .alt t u => annOK t && annOK u
  | .new [] b => annOK b
  | .new (_ :: _) _ => false
  | .lam _ _ _ _ => true
  | _ => true

/-- The name map inside a binder at owner `o` declaring `ys` with identities
`k`. -/
def bindν (ν : Nm (Slot X) → Nm (BId X)) (o : Owner) (ys : List X) (k : X → SlotId X) :
    Nm (Slot X) → Nm (BId X)
  | .src (o', y) => if o' = o ∧ y ∈ ys then .src (.slot (k y)) else ν (.src (o', y))
  | .inst ρ n => ν (.inst ρ n)

theorem ownKey_map_src {o o' : Owner} {ys : List X} {y : X} :
    ownKey (ys.map fun y => (o, y)) (.src (o', y) : Nm (Slot X)) = decide (o' = o ∧ y ∈ ys) := by
  simp only [ownKey, List.contains_eq_mem, List.mem_map, Prod.mk.injEq]
  by_cases h : o' = o ∧ y ∈ ys
  · rw [decide_eq_true h]
    exact decide_eq_true ⟨y, h.2, h.1.symm, rfl⟩
  · rw [decide_eq_false h]
    apply decide_eq_false
    rintro ⟨y', hy', ho, rfl⟩
    exact h ⟨ho.symm, hy'⟩

theorem bindν_off {ν : Nm (Slot X) → Nm (BId X)} {o : Owner} {ys : List X} {k : X → SlotId X}
    {n : Nm (Slot X)} (h : ownKey (ys.map fun y => (o, y)) n = false) : bindν ν o ys k n = ν n := by
  cases n with
  | src s =>
      obtain ⟨o', y⟩ := s
      rw [ownKey_map_src, decide_eq_false_iff_not] at h
      simp only [bindν, if_neg h]
  | inst ρ n => rfl

theorem bindν_on {ν : Nm (Slot X) → Nm (BId X)} {o : Owner} {ys : List X} {k : X → SlotId X}
    {y : X} (h : y ∈ ys) : bindν ν o ys k (.src (o, y)) = .src (.slot (k y)) := by
  simp [bindν, h]

theorem bindν_not_mem {ν : Nm (Slot X) → Nm (BId X)} {o o' : Owner} {ys : List X}
    {k : X → SlotId X} {y : X} (h : y ∉ ys) : bindν ν o ys k (.src (o', y)) = ν (.src (o', y)) := by
  simp only [bindν]
  rw [if_neg (fun h' => h h'.2)]

/-! ## Free names and parameters of the slot model -/

namespace Ann

theorem update_of_mem {env : REnv X} {ys : List X} {o : Owner} {y : X} (h : y ∈ ys) :
    env.update ys o y = o := by
  simp [REnv.update, h]

theorem update_of_not_mem {env : REnv X} {ys : List X} {o : Owner} {y : X} (h : y ∉ ys) :
    env.update ys o y = env y := by
  simp [REnv.update, h]

/-- **Free names of the slot model**: occurrences of the environment's slots
of spellings written in open text.  A pattern quotation is sealed, so the
claim is stated for open text. -/
theorem freeNames_slotOf : ∀ (t : Ann S X) (env : REnv X) (pos : Owner) (n : Nm (Slot X)),
    t.Open → n ∈ freeNames (t.slotOf env pos) → ∃ y ∈ t.names, n = .src (env y, y)
  | .sym _, _, _, _, _, h => by simp [slotOf, freeNames] at h
  | .fn _, _, _, _, _, h => by simp [slotOf, freeNames] at h
  | .sv y, env, _, n, _, h => by
      simp only [slotOf, slotVar, freeNames, List.mem_singleton] at h
      exact ⟨y, by simp [names], h⟩
  | .par _, _, _, _, _, h => by simp [slotOf, freeNames] at h
  | .lam _ own _ b, env, _, n, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeNames, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨y, hy, rfl⟩ := freeNames_slotOf b _ _ n hopen h.1
      by_cases hyo : y ∈ own
      · rw [update_of_mem hyo, ownKey_map_src, decide_eq_false_iff_not] at h
        exact absurd ⟨rfl, hyo⟩ h.2
      · exact ⟨y, hy, by rw [update_of_not_mem hyo]⟩
  | .app f a, env, _, n, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeNames, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf f _ _ n hopen.1 h
        exact ⟨y, by simp [names, hy], rfl⟩
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf a _ _ n hopen.2 h
        exact ⟨y, by simp [names, hy], rfl⟩
  | .quote _, _, _, _, _, h => by simp [slotOf, freeNames] at h
  | .pquote c, env, _, n, hopen, h => by
      simp only [slotOf, freeNames] at h
      obtain ⟨y, hy, rfl⟩ := hopen env n h
      exact ⟨y, by simpa [names] using hy, rfl⟩
  | .letP p w b, env, _, n, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeNames, List.mem_append] at h
      rcases h with (h | h) | h
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf p _ _ n hopen.1 h
        exact ⟨y, by simp [names, hy], rfl⟩
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf w _ _ n hopen.2.1 h
        exact ⟨y, by simp [names, hy], rfl⟩
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf b _ _ n hopen.2.2 h
        exact ⟨y, by simp [names, hy], rfl⟩
  | .letA y₀ ys p w b, env, _, n, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeNames, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.not_mem_nil, or_false] at h
      rcases h with ⟨h | h, ho⟩ | h
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf p _ _ n hopen.1 h
        by_cases hyo : y ∈ y₀ :: ys
        · rw [update_of_mem hyo, ownKey_map_src, decide_eq_false_iff_not] at ho
          exact absurd ⟨rfl, hyo⟩ ho
        · exact ⟨y, by simp [names, hy], by rw [update_of_not_mem hyo]⟩
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf b _ _ n hopen.2.2 h
        by_cases hyo : y ∈ y₀ :: ys
        · rw [update_of_mem hyo, ownKey_map_src, decide_eq_false_iff_not] at ho
          exact absurd ⟨rfl, hyo⟩ ho
        · exact ⟨y, by simp [names, hy], by rw [update_of_not_mem hyo]⟩
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf w _ _ n hopen.2.1 h
        exact ⟨y, by simp [names, hy], rfl⟩
  | .alt t₁ t₂, env, _, n, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeNames, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf t₁ _ _ n hopen.1 h
        exact ⟨y, by simp [names, hy], rfl⟩
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf t₂ _ _ n hopen.2 h
        exact ⟨y, by simp [names, hy], rfl⟩
  | .new [] b, env, _, n, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf] at h
      obtain ⟨y, hy, rfl⟩ := freeNames_slotOf b _ _ n hopen h
      exact ⟨y, by simp [names, hy], rfl⟩
  | .new (y₀ :: ys) b, env, _, n, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, newBlock, freeNames, List.mem_append, List.mem_filter,
        Bool.not_eq_eq_eq_not, Bool.not_true, List.not_mem_nil] at h
      obtain ⟨h, ho⟩ | ⟨⟨⟩, _⟩ := h
      obtain ⟨y, hy, rfl⟩ := freeNames_slotOf b _ _ n hopen h
      by_cases hyo : y ∈ y₀ :: ys
      · rw [update_of_mem hyo, ownKey_map_src, decide_eq_false_iff_not] at ho
        exact absurd ⟨rfl, hyo⟩ ho
      · exact ⟨y, by simp [names, hy], by rw [update_of_not_mem hyo]⟩

/-- **Free parameters of the slot model** are written parameters, by spelling. -/
theorem freeParams_slotOf : ∀ (t : Ann S X) (env : REnv X) (pos : Owner) (x : Nm (Slot X)),
    t.Open → x ∈ freeParams (t.slotOf env pos) → ∃ z ∈ t.freePars, x = .src ([], z)
  | .sym _, _, _, _, _, h => by simp [slotOf, freeParams] at h
  | .fn _, _, _, _, _, h => by simp [slotOf, freeParams] at h
  | .sv _, _, _, _, _, h => by simp [slotOf, slotVar, freeParams] at h
  | .par z, _, _, x, _, h => by
      simp only [slotOf, freeParams, List.mem_singleton] at h
      exact ⟨z, by simp [freePars], h⟩
  | .lam _ _ _ b, _, _, x, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeParams, List.mem_filter, decide_eq_true_eq] at h
      obtain ⟨z', hz', rfl⟩ := freeParams_slotOf b _ _ x hopen h.1
      refine ⟨z', ?_, rfl⟩
      simp only [freePars, List.mem_filter, decide_eq_true_eq]
      exact ⟨hz', fun e => h.2 (by rw [e]; rfl)⟩
  | .app f a, _, _, x, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeParams, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf f _ _ x hopen.1 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf a _ _ x hopen.2 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
  | .quote _, _, _, _, _, h => by simp [slotOf, freeParams] at h
  | .pquote _, _, _, _, _, h => by
      simp only [slotOf, freeParams] at h
      rw [freeParams_sealParams] at h
      simp at h
  | .letP p w b, _, _, x, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeParams, List.mem_append] at h
      rcases h with (h | h) | h
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf p _ _ x hopen.1 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf w _ _ x hopen.2.1 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf b _ _ x hopen.2.2 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
  | .letA _ _ p w b, _, _, x, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeParams, List.mem_append, List.mem_filter, decide_eq_true_eq,
        List.mem_singleton] at h
      rcases h with ⟨(h | h) | h, hne⟩ | h
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf p _ _ x hopen.1 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
      · exact absurd h hne
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf b _ _ x hopen.2.2 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf w _ _ x hopen.2.1 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
  | .alt t₁ t₂, _, _, x, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeParams, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf t₁ _ _ x hopen.1 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf t₂ _ _ x hopen.2 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
  | .new [] b, _, _, x, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf] at h
      obtain ⟨z, hz, rfl⟩ := freeParams_slotOf b _ _ x hopen h
      exact ⟨z, by simp [freePars, hz], rfl⟩
  | .new (_ :: _) b, _, _, x, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, newBlock, freeParams, List.mem_append, List.mem_filter,
        decide_eq_true_eq, List.mem_singleton] at h
      rcases h with ⟨h, _⟩ | ⟨h, hne⟩
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf b _ _ x hopen h
        exact ⟨z, by simp [freePars, hz], rfl⟩
      · exact absurd h hne

end Ann

/-! ## Frame slots -/

omit [DecidableEq X] in
theorem mem_vars_of_mem_freeNames {Y : Type v} [DecidableEq Y] {n : Nm Y} :
    ∀ {t : Tm S Y}, n ∈ freeNames t → n ∈ Tm.vars t
  | .sym _, h => by simp [freeNames] at h
  | .fn _, h => by simp [freeNames] at h
  | .var _, h => by simpa [freeNames, Tm.vars] using h
  | .pvar _, h => by simp [freeNames] at h
  | .lam _ _ b, h => by
      simp only [freeNames, List.mem_filter] at h
      exact mem_vars_of_mem_freeNames (t := b) h.1
  | .app f a, h => by
      simp only [freeNames, List.mem_append] at h
      simp only [Tm.vars, List.mem_append]
      rcases h with h | h
      · exact Or.inl (mem_vars_of_mem_freeNames h)
      · exact Or.inr (mem_vars_of_mem_freeNames h)
  | .quote _, h => by simp [freeNames] at h
  | .pquote c, h => by
      simp only [freeNames] at h
      exact mem_vars_of_mem_freeNames (t := c) h
  | .letP p w b, h => by
      simp only [freeNames, List.mem_append] at h
      simp only [Tm.vars, List.mem_append]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (mem_vars_of_mem_freeNames h))
      · exact Or.inl (Or.inr (mem_vars_of_mem_freeNames h))
      · exact Or.inr (mem_vars_of_mem_freeNames h)
  | .alt t₁ t₂, h => by
      simp only [freeNames, List.mem_append] at h
      simp only [Tm.vars, List.mem_append]
      rcases h with h | h
      · exact Or.inl (mem_vars_of_mem_freeNames h)
      · exact Or.inr (mem_vars_of_mem_freeNames h)

theorem slot_mem_frameSlots {F : Owner} {b : Tm S (BId X)} {k : SlotId X}
    (h : (.src (.slot k) : Nm (BId X)) ∈ Tm.vars b) (hk : k.frame = F) :
    BId.slot k ∈ frameSlots F b := by
  unfold frameSlots
  rw [List.mem_eraseDups]
  exact List.mem_filterMap.2 ⟨_, h, by simp [frameSlotOf, hk]⟩

theorem frame_of_mem_frameSlots {F : Owner} {b : Tm S (BId X)} {x : BId X}
    (h : x ∈ frameSlots F b) : ∃ k : SlotId X, x = .slot k ∧ k.frame = F := by
  unfold frameSlots at h
  rw [List.mem_eraseDups] at h
  obtain ⟨n, _, hn⟩ := List.mem_filterMap.1 h
  cases n with
  | src b =>
      cases b with
      | slot k =>
          by_cases hk : k.frame = F
          · simp only [frameSlotOf, if_pos hk, Option.some.injEq] at hn
            exact ⟨k, hn.symm, hk⟩
          · simp [frameSlotOf, hk] at hn
      | par _ _ => simp [frameSlotOf] at hn
      | code _ => simp [frameSlotOf] at hn
  | inst _ _ => simp [frameSlotOf] at hn

theorem ownKey_frameSlots {F : Owner} {b : Tm S (BId X)} {k : SlotId X}
    (h : (.src (.slot k) : Nm (BId X)) ∈ freeNames b) (hk : k.frame = F) :
    ownKey (frameSlots F b) (.src (.slot k) : Nm (BId X)) = true := by
  simp only [ownKey, List.contains_eq_mem, decide_eq_true_eq]
  exact slot_mem_frameSlots (mem_vars_of_mem_freeNames h) hk

theorem ownKey_frameSlots_false {F : Owner} {b : Tm S (BId X)} {k : SlotId X}
    (hk : k.frame ≠ F) : ownKey (frameSlots F b) (.src (.slot k) : Nm (BId X)) = false := by
  simp only [ownKey, List.contains_eq_mem, decide_eq_false_iff_not]
  intro hm
  obtain ⟨k', hk', hF⟩ := frame_of_mem_frameSlots hm
  cases hk'
  exact hk hF

theorem ownKey_map_true {o : Owner} {ys : List X} {n : Nm (Slot X)}
    (h : ownKey (ys.map fun y => (o, y)) n = true) : ∃ y ∈ ys, n = .src (o, y) := by
  cases n with
  | src s =>
      obtain ⟨o', y⟩ := s
      rw [ownKey_map_src, decide_eq_true_iff] at h
      obtain ⟨rfl, hy⟩ := h
      exact ⟨y, hy, rfl⟩
  | inst _ _ => simp [ownKey] at h

/-! ## Reserved names -/

/-- **The reserved names of a related pair**, at the frame `fr` and the identity
position `pos` of the text `t`: distinct, each a slot of the frame made inside
`t` by an activation (a `let` that introduces names, at a position where `t`
has one, or a `new` block), each free on the identity side; one made by a `new`
at `pos` itself is spelled unlike every free name of the slot side. -/
structure ResOK (fr pos : Owner) (t : Ann S X) (t₁ : Tm S (Slot X)) (t₂ : Tm S (BId X))
    (Res : List (Nm (BId X))) : Prop where
  nodup : Res.Nodup
  shape : ∀ m ∈ Res, ∃ k : SlotId X, m = .src (.slot k) ∧ k.frame = fr ∧ k.intro ≠ .head ∧
    ∃ q, k.site = pos ++ q ∧ (k.intro = .pat → t.LetAAt q)
  free : ∀ m ∈ Res, m ∈ freeNames t₂
  news : ∀ k : SlotId X, (.src (.slot k) : Nm (BId X)) ∈ Res → k.intro = .new → k.site = pos →
    ∀ n ∈ freeNames t₁, spellS n ≠ k.spell

theorem ResOK.nil {fr pos : Owner} {t : Ann S X} {t₁ : Tm S (Slot X)} {t₂ : Tm S (BId X)} :
    ResOK fr pos t t₁ t₂ [] :=
  ⟨List.nodup_nil, (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h)⟩

omit [DecidableEq X] in
theorem site_child_ne {pos q q' : Owner} {i j : ℕ} (hij : i ≠ j) :
    pos ++ [i] ++ q ≠ pos ++ [j] ++ q' := by
  intro h
  rw [List.append_assoc, List.append_assoc] at h
  have := List.append_cancel_left h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at this
  exact hij this.1

omit [DecidableEq X] in
theorem site_child_ne_self {pos q : Owner} {i : ℕ} : pos ++ [i] ++ q ≠ pos := by
  intro h
  have := congrArg List.length h
  simp at this

/-- The site of a reserved name of a child. -/
theorem ResOK.site {fr pos : Owner} {i : ℕ} {t : Ann S X} {t₁ : Tm S (Slot X)}
    {t₂ : Tm S (BId X)} {R : List (Nm (BId X))} (h : ResOK fr (pos ++ [i]) t t₁ t₂ R) :
    ∀ m ∈ R, ∃ k : SlotId X, m = .src (.slot k) ∧ ∃ q, k.site = pos ++ [i] ++ q := by
  intro m hm
  obtain ⟨k, hk, -, -, q, hq, -⟩ := h.shape m hm
  exact ⟨k, hk, q, hq⟩

/-- Reserved names of two different children are apart. -/
theorem ResOK.apart {fr pos : Owner} {i j : ℕ} (hij : i ≠ j) {t u : Ann S X}
    {t₁ u₁ : Tm S (Slot X)} {t₂ u₂ : Tm S (BId X)} {R R' : List (Nm (BId X))}
    (h : ResOK fr (pos ++ [i]) t t₁ t₂ R) (h' : ResOK fr (pos ++ [j]) u u₁ u₂ R') :
    ∀ m ∈ R, m ∉ R' := by
  intro m hm hm'
  obtain ⟨k, rfl, q, hq⟩ := h.site m hm
  obtain ⟨k', hk', q', hq'⟩ := h'.site _ hm'
  injection hk' with hk'
  injection hk' with hk'
  subst hk'
  exact site_child_ne hij (hq.symm.trans hq')

/-- The shape of a child's reserved name, seen from the parent. -/
theorem ResOK.lift {fr pos : Owner} {i : ℕ} {t c : Ann S X} {t₁ : Tm S (Slot X)}
    {t₂ : Tm S (BId X)} {R : List (Nm (BId X))} (h : ResOK fr (pos ++ [i]) c t₁ t₂ R)
    (hlet : ∀ q, c.LetAAt q → t.LetAAt (i :: q)) :
    ∀ m ∈ R, ∃ k : SlotId X, m = .src (.slot k) ∧ k.frame = fr ∧ k.intro ≠ .head ∧
      ∃ q, k.site = pos ++ q ∧ (k.intro = .pat → t.LetAAt q) := by
  intro m hm
  obtain ⟨k, hk, hf, hh, q, hq, hp⟩ := h.shape m hm
  exact ⟨k, hk, hf, hh, i :: q, by rw [hq]; simp, fun e => hlet q (hp e)⟩

/-- A child's reserved names are not at the parent's position. -/
theorem ResOK.news_child {fr pos : Owner} {i : ℕ} {c : Ann S X} {t₁ : Tm S (Slot X)}
    {t₂ : Tm S (BId X)} {R : List (Nm (BId X))} (h : ResOK fr (pos ++ [i]) c t₁ t₂ R)
    {k : SlotId X} (hk : (.src (.slot k) : Nm (BId X)) ∈ R) : k.site ≠ pos := by
  obtain ⟨k', hk', q, hq⟩ := h.site _ hk
  injection hk' with hk'
  injection hk' with hk'
  subst hk'
  rw [hq]
  exact site_child_ne_self

/-! ## The conditions of a frame -/

/-- **The conditions of a frame**: the body of a lambda (or of a clause), with
the frame's own names at owner `O` on the slot side and at frame `F` on the
identity side, satisfies the side conditions of `Rel.lam`. -/
theorem frame_conds {own : List X} {O F : Owner} {key : X → SlotId X}
    {νb μb : Nm (Slot X) → Nm (BId X)} {b : Ann S X} {env' : REnv X} {b₂ : Tm S (BId X)}
    {Rb : List (Nm (BId X))} {ok : Bool}
    (hrel : Rel SC νb μb .code Rb ok (b.slotOf env' O) b₂)
    (hres : ResOK F F b (b.slotOf env' O) b₂ Rb)
    (hO : ∀ y ∈ b.names, y ∈ own → env' y = O)
    (hνown : ∀ y ∈ own, νb (.src (O, y)) = .src (.slot (key y)))
    (hout : ∀ y ∈ b.names, y ∉ own →
      ∃ k : SlotId X, νb (.src (env' y, y)) = .src (.slot k) ∧ k.frame ≠ F)
    (hkey : ∀ y ∈ own, (key y).spell = y ∧ (key y).frame = F ∧ KeyOK F b (key y))
    (hopen : b.Open) :
    (∀ n ∈ freeNames (b.slotOf env' O),
      ownKey (frameSlots F b₂) (νb n) = ownKey (own.map fun y => (O, y)) n) ∧
    (∀ m ∈ Rb, ownKey (frameSlots F b₂) m = true) ∧
    (∀ n ∈ freeNames (b.slotOf env' O), ∀ n' ∈ freeNames (b.slotOf env' O),
      ownKey (own.map fun y => (O, y)) n = true → ownKey (own.map fun y => (O, y)) n' = true →
        νb n = νb n' → n = n') ∧
    (∀ n ∈ freeNames (b.slotOf env' O), ownKey (own.map fun y => (O, y)) n = true → νb n ∉ Rb) := by
  have hown_iff : ∀ y ∈ b.names,
      ownKey (own.map fun y => (O, y)) (.src (env' y, y)) = decide (y ∈ own) := by
    intro y hy
    rw [ownKey_map_src]
    by_cases h : y ∈ own
    · rw [hO y hy h]; simp [h]
    · simp [h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨y, hy, rfl⟩ := Ann.freeNames_slotOf b env' O n hopen hn
    rw [hown_iff y hy]
    by_cases h : y ∈ own
    · have hm := hrel.mem_freeNames hn
      rw [hO y hy h, hνown y h] at hm ⊢
      rw [decide_eq_true h]
      exact ownKey_frameSlots hm (hkey y h).2.1
    · obtain ⟨k, hk, hkF⟩ := hout y hy h
      rw [hk, decide_eq_false h]
      exact ownKey_frameSlots_false hkF
  · intro m hm
    obtain ⟨k, rfl, hkF, -, -⟩ := hres.shape m hm
    exact ownKey_frameSlots (hres.free _ hm) hkF
  · intro n hn n' hn' ho ho' he
    obtain ⟨y, hy, rfl⟩ := Ann.freeNames_slotOf b env' O n hopen hn
    obtain ⟨y', hy', rfl⟩ := Ann.freeNames_slotOf b env' O n' hopen hn'
    rw [hown_iff y hy, decide_eq_true_iff] at ho
    rw [hown_iff y' hy', decide_eq_true_iff] at ho'
    rw [hO y hy ho, hO y' hy' ho', hνown y ho, hνown y' ho'] at he
    rw [hO y hy ho, hO y' hy' ho']
    have hkk : key y = key y' := by
      injection he with he
      injection he
    have hyy : y = y' := by rw [← (hkey y ho).1, ← (hkey y' ho').1, hkk]
    rw [hyy]
  · intro n hn ho hmem
    obtain ⟨y, hy, rfl⟩ := Ann.freeNames_slotOf b env' O n hopen hn
    rw [hown_iff y hy, decide_eq_true_iff] at ho
    have hmem' : (.src (.slot (key y)) : Nm (BId X)) ∈ Rb := by
      rw [hO y hy ho, hνown y ho] at hmem
      exact hmem
    obtain ⟨k, hk, -, hkh, q, hq, hpat⟩ := hres.shape _ hmem'
    have hkk : key y = k := by
      injection hk with hk
      injection hk
    subst hkk
    rcases (hkey y ho).2.2 with hh | ⟨hn', hs⟩ | ⟨hp, P, hP, hnot⟩
    · exact hkh hh
    · exact hres.news (key y) hmem' hn' hs _ hn (by simp [spellS, (hkey y ho).1])
    · rw [hP] at hq
      have hPq : P = q := List.append_cancel_left hq
      subst hPq
      exact hnot (hpat hp)

/-! ## Combining reserved names -/

omit [DecidableEq X] in
theorem nodup_append_of {α : Type*} {l₁ l₂ : List α} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hd : ∀ a ∈ l₁, a ∉ l₂) : (l₁ ++ l₂).Nodup :=
  List.nodup_append.2 ⟨h₁, h₂, fun a ha _ hb e => hd a ha (e ▸ hb)⟩

/-- Two children. -/
theorem ResOK.two {fr pos : Owner} {i j : ℕ} (hij : i ≠ j) {t c d : Ann S X}
    {t₁ c₁ d₁ : Tm S (Slot X)} {t₂ c₂ d₂ : Tm S (BId X)} {R R' : List (Nm (BId X))}
    (hc : ResOK fr (pos ++ [i]) c c₁ c₂ R) (hd : ResOK fr (pos ++ [j]) d d₁ d₂ R')
    (hlc : ∀ q, c.LetAAt q → t.LetAAt (i :: q)) (hld : ∀ q, d.LetAAt q → t.LetAAt (j :: q))
    (hfc : ∀ m ∈ freeNames c₂, m ∈ freeNames t₂) (hfd : ∀ m ∈ freeNames d₂, m ∈ freeNames t₂) :
    ResOK fr pos t t₁ t₂ (R ++ R') where
  nodup := nodup_append_of hc.nodup hd.nodup (hc.apart hij hd)
  shape m hm := by
    rcases List.mem_append.1 hm with h | h
    · exact hc.lift hlc m h
    · exact hd.lift hld m h
  free m hm := by
    rcases List.mem_append.1 hm with h | h
    · exact hfc m (hc.free m h)
    · exact hfd m (hd.free m h)
  news k hk _ hs := by
    rcases List.mem_append.1 hk with h | h
    · exact absurd hs (hc.news_child h)
    · exact absurd hs (hd.news_child h)

/-- Three children. -/
theorem ResOK.three {fr pos : Owner} {t c d e : Ann S X}
    {t₁ c₁ d₁ e₁ : Tm S (Slot X)} {t₂ c₂ d₂ e₂ : Tm S (BId X)} {R R' R'' : List (Nm (BId X))}
    (hc : ResOK fr (pos ++ [0]) c c₁ c₂ R) (hd : ResOK fr (pos ++ [1]) d d₁ d₂ R')
    (he : ResOK fr (pos ++ [2]) e e₁ e₂ R'')
    (hlc : ∀ q, c.LetAAt q → t.LetAAt (0 :: q)) (hld : ∀ q, d.LetAAt q → t.LetAAt (1 :: q))
    (hle : ∀ q, e.LetAAt q → t.LetAAt (2 :: q))
    (hfc : ∀ m ∈ freeNames c₂, m ∈ freeNames t₂) (hfd : ∀ m ∈ freeNames d₂, m ∈ freeNames t₂)
    (hfe : ∀ m ∈ freeNames e₂, m ∈ freeNames t₂) :
    ResOK fr pos t t₁ t₂ (R ++ R' ++ R'') where
  nodup := nodup_append_of (nodup_append_of hc.nodup hd.nodup (hc.apart (by decide) hd)) he.nodup
    (fun m hm => by
      rcases List.mem_append.1 hm with h | h
      · exact hc.apart (by decide) he m h
      · exact hd.apart (by decide) he m h)
  shape m hm := by
    rcases List.mem_append.1 hm with h | h
    · rcases List.mem_append.1 h with h | h
      · exact hc.lift hlc m h
      · exact hd.lift hld m h
    · exact he.lift hle m h
  free m hm := by
    rcases List.mem_append.1 hm with h | h
    · rcases List.mem_append.1 h with h | h
      · exact hfc m (hc.free m h)
      · exact hfd m (hd.free m h)
    · exact hfe m (he.free m h)
  news k hk _ hs := by
    rcases List.mem_append.1 hk with h | h
    · rcases List.mem_append.1 h with h | h
      · exact absurd hs (hc.news_child h)
      · exact absurd hs (hd.news_child h)
    · exact absurd hs (he.news_child h)

/-! ## Activations -/

/-- **A `let` that introduces names**: an activation on the slot side, a plain
`let` on the identity side, whose introduced identities are reserved until the
activation runs. -/
theorem rel_letA_of {k : Kd} (hk : k ≠ .val) {ν μ : Nm (Slot X) → Nm (BId X)} {O : Owner}
    (hO : O ≠ []) {y₀ : X} {ys : List X} {fr pos : Owner} {ℓ : Nm (Slot X)}
    {t p w b : Ann S X} {t₁ p₁ w₁ b₁ : Tm S (Slot X)} {p₂ w₂ b₂ : Tm S (BId X)}
    {Rp Rw Rb : List (Nm (BId X))} {ow op ob : Bool}
    (hℓp : ℓ ∉ freeParams p₁) (hℓb : ℓ ∉ freeParams b₁)
    (hw : Rel SC ν μ .code Rw ow w₁ w₂)
    (hp : Rel SC (bindν ν O (y₀ :: ys) fun y => ⟨y, fr, pos, .pat⟩) μ .pat Rp op p₁ p₂)
    (hb : Rel SC (bindν ν O (y₀ :: ys) fun y => ⟨y, fr, pos, .pat⟩) μ .code Rb ob b₁ b₂)
    (hrp : ResOK fr (pos ++ [0]) p p₁ p₂ Rp) (hrw : ResOK fr (pos ++ [1]) w w₁ w₂ Rw)
    (hrb : ResOK fr (pos ++ [2]) b b₁ b₂ Rb)
    (hl : t.LetAAt []) (hl0 : ∀ q, p.LetAAt q → t.LetAAt (0 :: q))
    (hl1 : ∀ q, w.LetAAt q → t.LetAAt (1 :: q)) (hl2 : ∀ q, b.LetAAt q → t.LetAAt (2 :: q)) :
    ∃ Res, Rel SC ν μ k Res false
        (.app (.lam ℓ ((y₀ :: ys).map fun y => (O, y)) (.letP p₁ (.pvar ℓ) b₁)) w₁)
        (.letP p₂ w₂ b₂) ∧
      ResOK fr pos t t₁ (.letP p₂ w₂ b₂) Res := by
  have hRh : ∀ m ∈ ((((freeNames p₁ ++ freeNames b₁).filter
      fun n => ownKey ((y₀ :: ys).map fun y => (O, y)) n).map
        (bindν ν O (y₀ :: ys) fun y => ⟨y, fr, pos, .pat⟩)).dedup),
      ∃ n ∈ freeNames p₁ ++ freeNames b₁, ∃ y ∈ y₀ :: ys,
        n = .src (O, y) ∧ m = .src (.slot ⟨y, fr, pos, .pat⟩) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hm)
    obtain ⟨hn, ho⟩ := List.mem_filter.1 hn
    obtain ⟨y, hy, rfl⟩ := ownKey_map_true ho
    exact ⟨_, hn, y, hy, rfl, bindν_on hy⟩
  refine ⟨((((freeNames p₁ ++ freeNames b₁).filter
      fun n => ownKey ((y₀ :: ys).map fun y => (O, y)) n).map
        (bindν ν O (y₀ :: ys) fun y => ⟨y, fr, pos, .pat⟩)).dedup) ++ Rw ++ Rp ++ Rb, ?_, ?_⟩
  · refine .letAct hk (fun n hn => bindν_off hn) ?_ hℓp hℓb hw hp hb ?_ ?_
    · intro s hs h
      obtain ⟨y, _, rfl⟩ := List.mem_map.1 hs
      exact hO h
    · intro n hn ho
      exact List.mem_dedup.2 (List.mem_map.2 ⟨n, List.mem_filter.2 ⟨hn, ho⟩, rfl⟩)
    · intro n _ n' _ ho ho' he
      obtain ⟨y, hy, rfl⟩ := ownKey_map_true ho
      obtain ⟨y', hy', rfl⟩ := ownKey_map_true ho'
      rw [bindν_on hy, bindν_on hy'] at he
      injection he with he
      injection he with he
      injection he with he
      rw [he]
  · have hsite : ∀ m ∈ ((((freeNames p₁ ++ freeNames b₁).filter
        fun n => ownKey ((y₀ :: ys).map fun y => (O, y)) n).map
          (bindν ν O (y₀ :: ys) fun y => ⟨y, fr, pos, .pat⟩)).dedup),
        ∀ i (R : List (Nm (BId X))) (c : Ann S X) (c₁ : Tm S (Slot X)) (c₂ : Tm S (BId X)),
          ResOK fr (pos ++ [i]) c c₁ c₂ R → m ∉ R := by
      intro m hm i R c c₁ c₂ hR hmR
      obtain ⟨_, _, y, _, _, rfl⟩ := hRh m hm
      obtain ⟨k', hk', q, hq⟩ := hR.site _ hmR
      injection hk' with hk'
      injection hk' with hk'
      subst hk'
      exact site_child_ne_self hq.symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine nodup_append_of (nodup_append_of (nodup_append_of (List.nodup_dedup _) hrw.nodup
        (fun m hm => hsite m hm 1 _ _ _ _ hrw)) hrp.nodup ?_) hrb.nodup ?_
      · intro m hm
        rcases List.mem_append.1 hm with h | h
        · exact hsite m h 0 _ _ _ _ hrp
        · exact hrw.apart (by decide) hrp m h
      · intro m hm
        rcases List.mem_append.1 hm with h | h
        · rcases List.mem_append.1 h with h | h
          · exact hsite m h 2 _ _ _ _ hrb
          · exact hrw.apart (by decide) hrb m h
        · exact hrp.apart (by decide) hrb m h
    · intro m hm
      rcases List.mem_append.1 hm with h | h
      · rcases List.mem_append.1 h with h | h
        · rcases List.mem_append.1 h with h | h
          · obtain ⟨_, _, y, _, _, rfl⟩ := hRh m h
            exact ⟨_, rfl, rfl, by simp, [], by simp, fun _ => hl⟩
          · exact hrw.lift hl1 m h
        · exact hrp.lift hl0 m h
      · exact hrb.lift hl2 m h
    · intro m hm
      simp only [freeNames, List.mem_append]
      rcases List.mem_append.1 hm with h | h
      · rcases List.mem_append.1 h with h | h
        · rcases List.mem_append.1 h with h | h
          · obtain ⟨n, hn, y, hy, rfl, rfl⟩ := hRh m h
            rcases List.mem_append.1 hn with hn | hn
            · have := hp.mem_freeNames hn
              rw [bindν_on hy] at this
              exact Or.inl (Or.inl this)
            · have := hb.mem_freeNames hn
              rw [bindν_on hy] at this
              exact Or.inr this
          · exact Or.inl (Or.inr (hrw.free m h))
        · exact Or.inl (Or.inl (hrp.free m h))
      · exact Or.inr (hrb.free m h)
    · intro k hk hn hs
      rcases List.mem_append.1 hk with h | h
      · rcases List.mem_append.1 h with h | h
        · rcases List.mem_append.1 h with h | h
          · obtain ⟨_, _, y, _, _, he⟩ := hRh _ h
            injection he with he
            injection he with he
            subst he
            cases hn
          · exact absurd hs (hrw.news_child h)
        · exact absurd hs (hrp.news_child h)
      · exact absurd hs (hrb.news_child h)

/-- **A `new` block**: an activation on the slot side, nothing on the identity
side, whose declared identities are reserved until the activation runs. -/
theorem rel_new_of {ν μ : Nm (Slot X) → Nm (BId X)} {O : Owner} (hO : O ≠ []) {y₀ : X}
    {ys : List X} {fr pos : Owner} {ℓ : Nm (Slot X)} {t b : Ann S X} {b₁ : Tm S (Slot X)}
    {b₂ : Tm S (BId X)} {Rb : List (Nm (BId X))} {ob : Bool}
    (hℓ : ℓ ∉ freeParams b₁)
    (hb : Rel SC (bindν ν O (y₀ :: ys) fun y => ⟨y, fr, pos, .new⟩) μ .code Rb ob b₁ b₂)
    (hrb : ResOK fr pos b b₁ b₂ Rb) (hl : ∀ q, b.LetAAt q → t.LetAAt q)
    (hfree : ∀ n ∈ freeNames b₁, ownKey ((y₀ :: ys).map fun y => (O, y)) n = false →
      spellS n ∉ y₀ :: ys) :
    ∃ Res, Rel SC ν μ .code Res false
        (.app (.lam ℓ ((y₀ :: ys).map fun y => (O, y)) b₁) (.lam ℓ [] (.pvar ℓ))) b₂ ∧
      ResOK fr pos t (.app (.lam ℓ ((y₀ :: ys).map fun y => (O, y)) b₁) (.lam ℓ [] (.pvar ℓ)))
        b₂ Res := by
  have hRh : ∀ m ∈ (((freeNames b₁).filter
      fun n => ownKey ((y₀ :: ys).map fun y => (O, y)) n).map
        (bindν ν O (y₀ :: ys) fun y => ⟨y, fr, pos, .new⟩)).dedup,
      ∃ n ∈ freeNames b₁, ∃ y ∈ y₀ :: ys,
        n = .src (O, y) ∧ m = .src (.slot ⟨y, fr, pos, .new⟩) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hm)
    obtain ⟨hn, ho⟩ := List.mem_filter.1 hn
    obtain ⟨y, hy, rfl⟩ := ownKey_map_true ho
    exact ⟨_, hn, y, hy, rfl, bindν_on hy⟩
  refine ⟨(((freeNames b₁).filter
      fun n => ownKey ((y₀ :: ys).map fun y => (O, y)) n).map
        (bindν ν O (y₀ :: ys) fun y => ⟨y, fr, pos, .new⟩)).dedup ++ Rb, ?_, ?_⟩
  · refine .newAct (fun n hn => bindν_off hn) ?_ hℓ hb ?_ ?_
    · intro s hs h
      obtain ⟨y, _, rfl⟩ := List.mem_map.1 hs
      exact hO h
    · intro n hn ho
      exact List.mem_dedup.2 (List.mem_map.2 ⟨n, List.mem_filter.2 ⟨hn, ho⟩, rfl⟩)
    · intro n _ n' _ ho ho' he
      obtain ⟨y, hy, rfl⟩ := ownKey_map_true ho
      obtain ⟨y', hy', rfl⟩ := ownKey_map_true ho'
      rw [bindν_on hy, bindν_on hy'] at he
      injection he with he
      injection he with he
      injection he with he
      rw [he]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · refine nodup_append_of (List.nodup_dedup _) hrb.nodup ?_
      intro m hm hmb
      obtain ⟨n, hn, y, _, rfl, rfl⟩ := hRh m hm
      exact hrb.news _ hmb rfl rfl _ hn rfl
    · intro m hm
      rcases List.mem_append.1 hm with h | h
      · obtain ⟨_, _, y, _, _, rfl⟩ := hRh m h
        exact ⟨_, rfl, rfl, by simp, [], by simp, fun h => by cases h⟩
      · obtain ⟨k, hk, hf, hh, q, hq, hp⟩ := hrb.shape m h
        exact ⟨k, hk, hf, hh, q, hq, fun e => hl q (hp e)⟩
    · intro m hm
      rcases List.mem_append.1 hm with h | h
      · obtain ⟨n, hn, y, hy, rfl, rfl⟩ := hRh m h
        have := hb.mem_freeNames hn
        rwa [bindν_on hy] at this
      · exact hrb.free m h
    · intro k hk hi hs n hn
      simp only [freeNames, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.not_mem_nil] at hn
      obtain ⟨hn, ho⟩ | ⟨⟨⟩, _⟩ := hn
      rcases List.mem_append.1 hk with h | h
      · obtain ⟨_, _, y, hy, _, he⟩ := hRh _ h
        injection he with he
        injection he with he
        subst he
        intro e
        exact hfree n hn ho (e ▸ hy)
      · exact hrb.news k h hi hs n hn

omit [DecidableEq X] in
theorem ne_of_prefix {a b : Owner} (h : a <+: b) (i : ℕ) : a ≠ b ++ [i] := by
  intro e
  have := h.length_le
  rw [e] at this
  simp at this
  omega

/-! ## Scope owners -/

/-- An owner a scope may write: not a binder of code, and not a free parameter
of code. -/
def scopeOwner (o : Owner) : Prop :=
  codeBound o = false ∧ o ≠ codeFreeParam

/-- Every extension of `o` is a scope owner. -/
def headSafe (o : Owner) : Prop :=
  ∀ xs, scopeOwner (o ++ xs)

/-- The three owners written under a scope position. -/
def PosSafe (pos : Owner) : Prop :=
  headSafe (pos ++ [0]) ∧ headSafe (pos ++ [1]) ∧ headSafe (pos ++ [2])

omit [DecidableEq X] in
theorem codeBound_of_head {a : ℕ} (ha : a ≠ 9) (xs : List ℕ) : codeBound (a :: xs) = false := by
  unfold codeBound
  split
  · next h =>
      injection h with ha'
      exact absurd ha' ha
  · rfl

omit [DecidableEq X] in
theorem headSafe_cons {a : ℕ} (ha : a ≠ 9) (o : Owner) : headSafe (a :: o) := by
  intro xs
  refine ⟨codeBound_of_head ha (o ++ xs), ?_⟩
  intro h
  simp only [codeFreeParam] at h
  injection h with ha'
  exact ha ha'

omit [DecidableEq X] in
theorem headSafe.append {o xs : Owner} (h : headSafe o) : headSafe (o ++ xs) := by
  intro ys
  simpa [List.append_assoc] using h (xs ++ ys)

omit [DecidableEq X] in
theorem headSafe.owner {o : Owner} (h : headSafe o) : scopeOwner o := by
  simpa [List.append_nil] using h []

theorem scopeOwner_update {env : REnv X} {ys : List X} {o : Owner}
    (h : ∀ y, scopeOwner (env y)) (ho : scopeOwner o) :
    ∀ y, scopeOwner (REnv.update env ys o y) := by
  intro y
  simp only [REnv.update]
  split
  · exact ho
  · exact h y

omit [DecidableEq X] in
theorem PosSafe.zero {pos : Owner} (h : PosSafe pos) : PosSafe (pos ++ [0]) :=
  ⟨headSafe.append (xs := [0]) h.1, headSafe.append (xs := [1]) h.1,
    headSafe.append (xs := [2]) h.1⟩

omit [DecidableEq X] in
theorem PosSafe.one {pos : Owner} (h : PosSafe pos) : PosSafe (pos ++ [1]) :=
  ⟨headSafe.append (xs := [0]) h.2.1, headSafe.append (xs := [1]) h.2.1,
    headSafe.append (xs := [2]) h.2.1⟩

omit [DecidableEq X] in
theorem PosSafe.two {pos : Owner} (h : PosSafe pos) : PosSafe (pos ++ [2]) :=
  ⟨headSafe.append (xs := [0]) h.2.2, headSafe.append (xs := [1]) h.2.2,
    headSafe.append (xs := [2]) h.2.2⟩

omit [DecidableEq X] in
theorem scopeOwners_nil : ∀ _ : X, scopeOwner ([] : Owner) :=
  fun _ => ⟨rfl, by decide⟩

omit [DecidableEq X] in
theorem scopeOwners_five : ∀ _ : X, scopeOwner ([5] : Owner) :=
  fun _ => ⟨rfl, by decide⟩

omit [DecidableEq X] in
theorem PosSafe.root : PosSafe ([] : Owner) :=
  ⟨headSafe_cons (by decide) [], headSafe_cons (by decide) [], headSafe_cons (by decide) []⟩

omit [DecidableEq X] in
theorem PosSafe.clause : PosSafe ([5] : Owner) :=
  ⟨headSafe_cons (by decide) [0], headSafe_cons (by decide) [1], headSafe_cons (by decide) [2]⟩

/-! ## The static relation -/

/-- **The two elaborations of well-formed annotated text are related.**  When
each spelling's slot is sent to its identity, the identities belong to the
enclosing frames, and each free parameter is sent to its binder, the slot
model's term and the identity model's term are related by `Rel`, as a pattern
(`k = .pat`, for text without `new` blocks on its spine) or as code, with
reserved names satisfying `ResOK`. A pattern quotation is related as code:
its holes are the outer slots, and its binders travel by `CodeRel`. The
resolution environment and the owners written at `posS` are scope owners. -/
theorem rel_ann (t : Ann S X) : ∀ {k : Kd} {env : REnv X} {posS : Owner} {envI : IEnv X}
    {pv : X → Owner} {fr posI : Owner} {ν μ : Nm (Slot X) → Nm (BId X)},
    t.WF posI → k ≠ .val → (k = .pat → t.NewFree) →
    (∀ y ∈ t.names, ν (.src (env y, y)) = .src (.slot (envI y))) →
    (∀ y ∈ t.names, (envI y).spell = y ∧ (envI y).frame <+: fr) → fr <+: posI →
    (∀ z ∈ t.freePars, μ (.src ([], z)) = .src (.par z (pv z))) →
    (∀ y, scopeOwner (env y)) → PosSafe posS →
    ∃ Res, Rel SC ν μ k Res (annOK t) (t.slotOf env posS) (t.idOf envI pv fr posI) ∧
      ResOK fr posI t (t.slotOf env posS) (t.idOf envI pv fr posI) Res := by
  induction t with
  | sym s =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      exact ⟨[], .sym s, .nil⟩
  | fn F =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      exact ⟨[], .fn F, .nil⟩
  | sv y =>
      intro k env posS envI pv fr posI ν μ _ _ _ hν _ _ _ hE _
      refine ⟨[], ?_, .nil⟩
      show Rel SC ν μ k [] true (.var (.src (env y, y))) (.var (.src (.slot (envI y))))
      rw [← hν y (by simp [Ann.names])]
      exact .var (.src (env y, y)) <| by
        rw [hν y (by simp [Ann.names])]
        simp only [SC, scVarHole, holeRecS, holeRecI, (hE y).1]
        decide
  | par z =>
      intro k env posS envI pv fr posI ν μ _ _ _ _ _ _ hμ _ _
      refine ⟨[], ?_, .nil⟩
      show Rel SC ν μ k [] true (.pvar (.src ([], z))) (.pvar (.src (.par z (pv z))))
      rw [← hμ z (by simp [Ann.freePars])]
      exact .pvar (.src ([], z)) <| by
        rw [hμ z (by simp [Ann.freePars])]
        exact scParOK_scope
  | quote c =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      exact ⟨[], .quote ⟨c, rfl, rfl⟩, .nil⟩
  | pquote c =>
      intro _ env _ envI _ _ _ ν _ hwf _ _ hν _ _ _ hE _
      simp only [Ann.slotOf, Ann.idOf]
      have hB : ∀ y, codeBound (env y) = false := fun y => (hE y).1
      have hF : ∀ y, env y ≠ codeFreeParam := fun y => (hE y).2
      have hbody : Rel SC (codeMapHoles env envI) (codeMapHoles env envI) .code [] true
          (sealParams (codeAt (some env) [] [] [] c))
          (sealParams (codeIAt (some envI) [] [] [] c)) :=
        Rel.of_codeRel (C := SC) (fun {_ _} h => h) (scVarHole_map env envI)
          (scParOK_map env envI) (fun {_ _ _} h₁ h₂ => scBare_map env envI h₁ h₂)
          (hwf env envI hB hF) .code (by decide)
      refine ⟨[], .pquote (hbody.congr ?hnames ?hparams) (hbody.shape_of rfl) rfl, ResOK.nil⟩
      · intro n hn
        rw [freeNames_sealParams] at hn
        obtain ⟨y, hy, rfl⟩ := mem_freeNames_codeAt env [] [] [] c n hn
        rw [codeMapHoles_hole (hB y) (hF y), hν y (by simpa [Ann.names] using hy)]
      · intro x hx
        rw [freeParams_sealParams] at hx
        cases hx
  | lam z own key b ih =>
      intro _ env posS envI pv fr posI ν μ hwf _ _ hν hI hfr hμ hE hP
      simp only [Ann.WF] at hwf
      obtain ⟨hkeys, hwfb⟩ := hwf
      have hνb : ∀ y ∈ b.names, bindν ν (posS ++ [0]) own key
          (.src (env.update own (posS ++ [0]) y, y)) = .src (.slot (envI.set own key y)) := by
        intro y hy
        by_cases hyo : y ∈ own
        · rw [Ann.update_of_mem hyo, bindν_on hyo, IEnv.set_of_mem hyo]
        · rw [Ann.update_of_not_mem hyo, bindν_not_mem hyo, IEnv.set_of_not_mem hyo]
          exact hν y hy
      have hIb : ∀ y ∈ b.names, (envI.set own key y).spell = y ∧
          (envI.set own key y).frame <+: posI ++ [0] := by
        intro y hy
        by_cases hyo : y ∈ own
        · rw [IEnv.set_of_mem hyo, (hkeys y hyo).2.1]
          exact ⟨(hkeys y hyo).1, List.prefix_refl _⟩
        · rw [IEnv.set_of_not_mem hyo]
          exact ⟨(hI y hy).1, ((hI y hy).2.trans hfr).trans (List.prefix_append _ _)⟩
      have hμb : ∀ z' ∈ b.freePars, Function.update μ (parName z) (.src (.par z posI))
          (.src ([], z')) = .src (.par z' (pvSet pv z posI z')) := by
        intro z' hz'
        by_cases hzz : z' = z
        · subst hzz
          simp [pvSet, parName]
        · have hne : (.src ([], z') : Nm (Slot X)) ≠ parName z := by
            simp [parName, hzz]
          rw [Function.update_of_ne hne]
          simp only [pvSet, if_neg hzz]
          exact hμ z' (by simp [Ann.freePars, hz', hzz])
      obtain ⟨Rb, hrel, hres⟩ := ih (k := .code) (env := env.update own (posS ++ [0]))
        (posS := posS ++ [0]) (envI := envI.set own key) (pv := pvSet pv z posI)
        (fr := posI ++ [0]) (posI := posI ++ [0]) (ν := bindν ν (posS ++ [0]) own key)
        (μ := Function.update μ (parName z) (.src (.par z posI))) hwfb (by decide)
        (fun h => by cases h) hνb hIb (List.prefix_refl _) hμb
        (scopeOwner_update hE (headSafe.owner hP.1)) hP.zero
      obtain ⟨hown, hresb, hinj, hdisj⟩ := frame_conds (key := key) hrel hres
        (fun y _ hy => Ann.update_of_mem hy) (fun y hy => bindν_on hy)
        (fun y hy hyo => ⟨envI y, by rw [Ann.update_of_not_mem hyo, bindν_not_mem hyo]; exact hν y hy,
          ne_of_prefix ((hI y hy).2.trans hfr) 0⟩) hkeys (Ann.Open.of_WF hwfb)
      refine ⟨[], ?_, .nil⟩
      simp only [Ann.slotOf, Ann.idOf]
      refine .lam (νb := bindν ν (posS ++ [0]) own key)
        (μb := Function.update μ (parName z) (.src (.par z posI)))
        (fun n hn => bindν_off hn) (fun x hx => Function.update_of_ne hx _ _)
        (Function.update_self _ _ _) ?_ ?_ hrel hown hresb hinj hdisj hres.nodup ?_
        scBare_scope
        (by
          intro hent
          simp only [SC, scEnter, holeRecS, holeRecI, codeFreeS, codeFreeI, parName,
            codeBound, codeFreeParam] at hent
          rcases hent with hent | hent
          · exact absurd hent.1 Bool.false_ne_true.symm
          · exact absurd hent.1 Bool.false_ne_true)
      · intro s hs h
        obtain ⟨y, _, rfl⟩ := List.mem_map.1 hs
        exact (by simp : posS ++ [0] ≠ []) h
      · intro s hs h
        obtain ⟨k', rfl, hkF⟩ := frame_of_mem_frameSlots hs
        obtain ⟨k'', hk'', hk0⟩ := h
        injection hk'' with hk''
        subst hk''
        rw [hkF] at hk0
        simp at hk0
      · intro x hx hne
        obtain ⟨z', hz', rfl⟩ := Ann.freeParams_slotOf b _ _ x (Ann.Open.of_WF hwfb) hx
        have hzz : z' ≠ z := fun e => hne (by rw [e]; rfl)
        rw [hμ z' (by simp [Ann.freePars, hz', hzz])]
        intro e
        injection e with e
        injection e with e
        exact hzz e
  | app f a ihf iha =>
      intro k env posS envI pv fr posI ν μ hwf hk hpat hν hI hfr hμ hE hP
      simp only [Ann.WF] at hwf
      obtain ⟨hwf₁, hwf₂⟩ := hwf
      obtain ⟨R₁, h₁, hr₁⟩ := ihf (posS := posS ++ [0]) hwf₁ hk
        (fun e => by have := hpat e; simp only [Ann.NewFree] at this; exact this.1)
        (fun y hy => hν y (by simp [Ann.names, hy])) (fun y hy => hI y (by simp [Ann.names, hy]))
        (hfr.trans (List.prefix_append _ _)) (fun z hz => hμ z (by simp [Ann.freePars, hz]))
        hE hP.zero
      obtain ⟨R₂, h₂, hr₂⟩ := iha (posS := posS ++ [1]) hwf₂ hk
        (fun e => by have := hpat e; simp only [Ann.NewFree] at this; exact this.2)
        (fun y hy => hν y (by simp [Ann.names, hy])) (fun y hy => hI y (by simp [Ann.names, hy]))
        (hfr.trans (List.prefix_append _ _)) (fun z hz => hμ z (by simp [Ann.freePars, hz]))
        hE hP.one
      simp only [Ann.slotOf, Ann.idOf]
      exact ⟨R₁ ++ R₂, .app h₁ h₂, ResOK.two (by decide) hr₁ hr₂ (fun _ h => h) (fun _ h => h)
        (fun m hm => by simp [freeNames, hm]) (fun m hm => by simp [freeNames, hm])⟩
  | letP p w b ihp ihw ihb =>
      intro k env posS envI pv fr posI ν μ hwf hk _ hν hI hfr hμ hE hP
      simp only [Ann.WF] at hwf
      obtain ⟨hnf, hwp, hww, hwb⟩ := hwf
      have hpre : ∀ i, fr <+: posI ++ [i] := fun i => hfr.trans (List.prefix_append _ _)
      obtain ⟨Rp, hp, hrp⟩ := ihp (k := .pat) (posS := posS ++ [0]) hwp (by decide) (fun _ => hnf)
        (fun y hy => hν y (by simp [Ann.names, hy])) (fun y hy => hI y (by simp [Ann.names, hy]))
        (hpre 0) (fun z hz => hμ z (by simp [Ann.freePars, hz])) hE hP.zero
      obtain ⟨Rw, hw, hrw⟩ := ihw (k := .code) (posS := posS ++ [1]) hww (by decide)
        (fun h => by cases h)
        (fun y hy => hν y (by simp [Ann.names, hy])) (fun y hy => hI y (by simp [Ann.names, hy]))
        (hpre 1) (fun z hz => hμ z (by simp [Ann.freePars, hz])) hE hP.one
      obtain ⟨Rb, hb, hrb⟩ := ihb (k := .code) (posS := posS ++ [2]) hwb (by decide)
        (fun h => by cases h)
        (fun y hy => hν y (by simp [Ann.names, hy])) (fun y hy => hI y (by simp [Ann.names, hy]))
        (hpre 2) (fun z hz => hμ z (by simp [Ann.freePars, hz])) hE hP.two
      simp only [Ann.slotOf, Ann.idOf]
      exact ⟨Rp ++ Rw ++ Rb, .letP hk hp hw hb, ResOK.three hrp hrw hrb (fun _ h => h)
        (fun _ h => h) (fun _ h => h) (fun m hm => by simp [freeNames, hm])
        (fun m hm => by simp [freeNames, hm]) (fun m hm => by simp [freeNames, hm])⟩
  | letA y₀ ys p w b ihp ihw ihb =>
      intro k env posS envI pv fr posI ν μ hwf hk _ hν hI hfr hμ hE hP
      simp only [Ann.WF] at hwf
      obtain ⟨hnf, hwp, hww, hwb⟩ := hwf
      have hpre : ∀ i, fr <+: posI ++ [i] := fun i => hfr.trans (List.prefix_append _ _)
      have hν' : ∀ y ∈ p.names ++ b.names,
          bindν ν (posS ++ [2]) (y₀ :: ys) (fun y => ⟨y, fr, posI, .pat⟩)
            (.src (env.update (y₀ :: ys) (posS ++ [2]) y, y)) =
          .src (.slot (envI.set (y₀ :: ys) (fun y => ⟨y, fr, posI, .pat⟩) y)) := by
        intro y hy
        by_cases hyo : y ∈ y₀ :: ys
        · rw [Ann.update_of_mem hyo, bindν_on hyo, IEnv.set_of_mem hyo]
        · rw [Ann.update_of_not_mem hyo, bindν_not_mem hyo, IEnv.set_of_not_mem hyo]
          exact hν y (by simp only [List.mem_append] at hy; simp [Ann.names]; tauto)
      have hI' : ∀ y ∈ p.names ++ b.names,
          (envI.set (y₀ :: ys) (fun y => ⟨y, fr, posI, .pat⟩) y).spell = y ∧
          (envI.set (y₀ :: ys) (fun y => ⟨y, fr, posI, .pat⟩) y).frame <+: fr := by
        intro y hy
        by_cases hyo : y ∈ y₀ :: ys
        · rw [IEnv.set_of_mem hyo]
          exact ⟨rfl, List.prefix_refl _⟩
        · rw [IEnv.set_of_not_mem hyo]
          exact hI y (by simp only [List.mem_append] at hy; simp [Ann.names]; tauto)
      obtain ⟨Rp, hp, hrp⟩ := ihp (k := .pat) (posS := posS ++ [0])
        (env := env.update (y₀ :: ys) (posS ++ [2]))
        (envI := envI.set (y₀ :: ys) fun y => ⟨y, fr, posI, .pat⟩) (pv := pv) (fr := fr)
        (posI := posI ++ [0]) (ν := bindν ν (posS ++ [2]) (y₀ :: ys) fun y => ⟨y, fr, posI, .pat⟩)
        (μ := μ) hwp (by decide) (fun _ => hnf) (fun y hy => hν' y (List.mem_append_left _ hy))
        (fun y hy => hI' y (List.mem_append_left _ hy)) (hpre 0)
        (fun z hz => hμ z (by simp [Ann.freePars, hz]))
        (scopeOwner_update hE (headSafe.owner hP.2.2)) hP.zero
      obtain ⟨Rw, hw, hrw⟩ := ihw (k := .code) (posS := posS ++ [1]) (env := env) (envI := envI)
        (pv := pv) (fr := fr) (posI := posI ++ [1]) (ν := ν) (μ := μ) hww (by decide)
        (fun h => by cases h)
        (fun y hy => hν y (by simp [Ann.names, hy])) (fun y hy => hI y (by simp [Ann.names, hy]))
        (hpre 1) (fun z hz => hμ z (by simp [Ann.freePars, hz])) hE hP.one
      obtain ⟨Rb, hb, hrb⟩ := ihb (k := .code) (posS := posS ++ [2])
        (env := env.update (y₀ :: ys) (posS ++ [2]))
        (envI := envI.set (y₀ :: ys) fun y => ⟨y, fr, posI, .pat⟩) (pv := pv) (fr := fr)
        (posI := posI ++ [2]) (ν := bindν ν (posS ++ [2]) (y₀ :: ys) fun y => ⟨y, fr, posI, .pat⟩)
        (μ := μ) hwb (by decide) (fun h => by cases h)
        (fun y hy => hν' y (List.mem_append_right _ hy))
        (fun y hy => hI' y (List.mem_append_right _ hy)) (hpre 2)
        (fun z hz => hμ z (by simp [Ann.freePars, hz]))
        (scopeOwner_update hE (headSafe.owner hP.2.2)) hP.two
      simp only [Ann.slotOf, Ann.idOf]
      exact rel_letA_of hk (by simp)
        (fun h => by
          obtain ⟨z, _, hz⟩ := Ann.freeParams_slotOf p _ _ _ (Ann.Open.of_WF hwp) h
          simp [letParam] at hz)
        (fun h => by
          obtain ⟨z, _, hz⟩ := Ann.freeParams_slotOf b _ _ _ (Ann.Open.of_WF hwb) h
          simp [letParam] at hz)
        hw hp hb hrp hrw hrb trivial (fun _ h => h) (fun _ h => h) (fun _ h => h)
  | alt t₁ t₂ ih₁ ih₂ =>
      intro k env posS envI pv fr posI ν μ hwf hk _ hν hI hfr hμ hE hP
      simp only [Ann.WF] at hwf
      obtain ⟨hw₁, hw₂⟩ := hwf
      obtain ⟨R₁, h₁, hr₁⟩ := ih₁ (k := .code) (posS := posS ++ [0]) hw₁ (by decide)
        (fun h => by cases h)
        (fun y hy => hν y (by simp [Ann.names, hy])) (fun y hy => hI y (by simp [Ann.names, hy]))
        (hfr.trans (List.prefix_append _ _)) (fun z hz => hμ z (by simp [Ann.freePars, hz]))
        hE hP.zero
      obtain ⟨R₂, h₂, hr₂⟩ := ih₂ (k := .code) (posS := posS ++ [1]) hw₂ (by decide)
        (fun h => by cases h)
        (fun y hy => hν y (by simp [Ann.names, hy])) (fun y hy => hI y (by simp [Ann.names, hy]))
        (hfr.trans (List.prefix_append _ _)) (fun z hz => hμ z (by simp [Ann.freePars, hz]))
        hE hP.one
      simp only [Ann.slotOf, Ann.idOf]
      exact ⟨R₁ ++ R₂, .alt hk h₁ h₂, ResOK.two (by decide) hr₁ hr₂ (fun _ h => h) (fun _ h => h)
        (fun m hm => by simp [freeNames, hm]) (fun m hm => by simp [freeNames, hm])⟩
  | new ys b ih =>
      intro k env posS envI pv fr posI ν μ hwf hk hpat hν hI hfr hμ hE hP
      simp only [Ann.WF] at hwf
      cases ys with
      | nil =>
          obtain ⟨R, h, hr⟩ := ih (k := k) (posS := posS ++ [0]) (env := env) (envI := envI)
            (pv := pv) (fr := fr) (posI := posI) (ν := ν) (μ := μ) hwf hk
            (fun e => by have := hpat e; simpa [Ann.NewFree] using this)
            (fun y hy => hν y (by simpa [Ann.names] using hy))
            (fun y hy => hI y (by simpa [Ann.names] using hy)) hfr
            (fun z hz => hμ z (by simpa [Ann.freePars] using hz)) hE hP.zero
          simp only [Ann.slotOf, Ann.idOf, IEnv.set_nil]
          exact ⟨R, h, hr.nodup, fun m hm => hr.shape m hm, hr.free, hr.news⟩
      | cons y₀ ys =>
          have hkc : k = .code := by
            cases k with
            | val => exact absurd rfl hk
            | pat =>
                have := hpat rfl
                simp [Ann.NewFree] at this
            | code => rfl
          subst hkc
          have hν' : ∀ y ∈ b.names,
              bindν ν (posS ++ [0]) (y₀ :: ys) (fun y => ⟨y, fr, posI, .new⟩)
                (.src (env.update (y₀ :: ys) (posS ++ [0]) y, y)) =
              .src (.slot (envI.set (y₀ :: ys) (fun y => ⟨y, fr, posI, .new⟩) y)) := by
            intro y hy
            by_cases hyo : y ∈ y₀ :: ys
            · rw [Ann.update_of_mem hyo, bindν_on hyo, IEnv.set_of_mem hyo]
            · rw [Ann.update_of_not_mem hyo, bindν_not_mem hyo, IEnv.set_of_not_mem hyo]
              exact hν y (by simpa [Ann.names] using hy)
          have hI' : ∀ y ∈ b.names,
              (envI.set (y₀ :: ys) (fun y => ⟨y, fr, posI, .new⟩) y).spell = y ∧
              (envI.set (y₀ :: ys) (fun y => ⟨y, fr, posI, .new⟩) y).frame <+: fr := by
            intro y hy
            by_cases hyo : y ∈ y₀ :: ys
            · rw [IEnv.set_of_mem hyo]
              exact ⟨rfl, List.prefix_refl _⟩
            · rw [IEnv.set_of_not_mem hyo]
              exact hI y (by simpa [Ann.names] using hy)
          obtain ⟨Rb, hb, hrb⟩ := ih (k := .code) (posS := posS ++ [0])
            (env := env.update (y₀ :: ys) (posS ++ [0]))
            (envI := envI.set (y₀ :: ys) fun y => ⟨y, fr, posI, .new⟩) (pv := pv) (fr := fr)
            (posI := posI) (ν := bindν ν (posS ++ [0]) (y₀ :: ys) fun y => ⟨y, fr, posI, .new⟩)
            (μ := μ) hwf (by decide) (fun h => by cases h) hν' hI' hfr
            (fun z hz => hμ z (by simpa [Ann.freePars] using hz))
            (scopeOwner_update hE (headSafe.owner hP.1)) hP.zero
          simp only [Ann.slotOf, Ann.idOf, newBlock]
          exact rel_new_of (by simp)
            (fun h => by
              obtain ⟨z, _, hz⟩ := Ann.freeParams_slotOf b _ _ _ (Ann.Open.of_WF hwf) h
              simp [newParam] at hz)
            hb hrb (fun _ h => h)
            (fun n hn ho => by
              obtain ⟨y, _, rfl⟩ := Ann.freeNames_slotOf b _ _ n (Ann.Open.of_WF hwf) hn
              by_cases hyo : y ∈ y₀ :: ys
              · rw [Ann.update_of_mem hyo, ownKey_map_src, decide_eq_false_iff_not] at ho
                exact absurd ⟨rfl, hyo⟩ ho
              · simpa [spellS] using hyo)

end IdSlot

end Mettapedia.GSLT.LanguageDef.TemplateScope
