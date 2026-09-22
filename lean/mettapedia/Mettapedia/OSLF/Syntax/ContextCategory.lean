import Mettapedia.OSLF.Syntax.ContextualSplitting
import Mathlib.CategoryTheory.Category.Basic

/-!
# Contexts compose: the category of one-hole contexts

A one-hole context is a shape with a hole of one sort producing a term of
another.  Read that way it is a morphism -- from the hole it has to the sort it
makes -- and the reading is exact: the bare hole is an identity, plugging one
context into another's hole is composition, and the two identity laws and
associativity hold on the nose.

This is the law the splitting development was missing.  Without composition a
cut is a point and the collection of cuts is a set; with it, cuts form a
structure, and "where something happens" becomes a place one can move around in
rather than a label.  Plugging a term into a hole is then the action of that
structure on terms, and that action is functorial -- plugging into a composite
is plugging twice, which is the statement that nesting is associative and that
nothing is lost or duplicated at a seam.

The laws are not new work.  Identity is `bind_id` and associativity is
`bind_comp`, read on contexts instead of on substitutions, which is the same
phenomenon a second time: substitution is a monoid and one-hole contexts are the
part of it that keeps exactly one variable free to be replaced.
-/

namespace Mettapedia.OSLF.Binding

open CategoryTheory

set_option autoImplicit false

variable {S : Signature}

namespace ContextCat

/-- An object: a sort, in the role of the type of a hole. -/
structure Hole (S : Signature) (_Γ : Ctx S) where
  /-- The sort a hole of this kind accepts. -/
  sort : S.Srt

/-- The substitution that replaces the hole by `L` and shifts everything else
past the new hole. -/
def holeSub {Γ : Ctx S} {c d : S.Srt} (L : Term S (d :: Γ) c) :
    Sub S (c :: Γ) (d :: Γ)
  | _, .zero => L
  | _, .succ w => Term.var (.succ w)

/-- **Plugging a context into a context's hole.**  The result still has one hole,
now of the inner context's sort. -/
def comp {Γ : Ctx S} {c d s : S.Srt} (K : Term S (c :: Γ) s) (L : Term S (d :: Γ) c) :
    Term S (d :: Γ) s :=
  bind (holeSub L) K

/-- The bare hole is a right unit: plugging the hole into `K`'s hole is `K`. -/
theorem comp_hole {Γ : Ctx S} {c s : S.Srt} (K : Term S (c :: Γ) s) :
    comp K (Term.var (Var.zero : Var (c :: Γ) c)) = K := by
  have h : holeSub (Term.var (Var.zero : Var (c :: Γ) c))
      = (fun _ v => Term.var v : Sub S (c :: Γ) (c :: Γ)) := by
    funext s v
    cases v with
    | zero => rfl
    | succ _ => rfl
  rw [comp, h, bind_id]

/-- The bare hole is a left unit: plugging `L` into the hole is `L`. -/
theorem hole_comp {Γ : Ctx S} {c d : S.Srt} (L : Term S (d :: Γ) c) :
    comp (Term.var (Var.zero : Var (c :: Γ) c)) L = L := rfl

/-- **Nesting is associative.** -/
theorem comp_assoc {Γ : Ctx S} {b c d s : S.Srt}
    (K : Term S (c :: Γ) s) (L : Term S (b :: Γ) c) (M : Term S (d :: Γ) b) :
    comp (comp K L) M = comp K (comp L M) := by
  have h : (fun (t : S.Srt) (v : Var (c :: Γ) t) => bind (holeSub M) (holeSub L t v))
      = holeSub (comp L M) := by
    funext t v
    cases v with
    | zero => rfl
    | succ _ => rfl
  rw [comp, comp, bind_comp, h]
  rfl

/-- **The category of one-hole contexts.**  Objects are holes; a morphism from a
hole of sort `c` to a hole of sort `s` is a context with a `c`-hole producing an
`s`; the identity is the bare hole and composition is nesting. -/
instance contextCategory (S : Signature) (Γ : Ctx S) : Category (Hole S Γ) where
  Hom c s := Term S (c.sort :: Γ) s.sort
  id c := Term.var (Var.zero : Var (c.sort :: Γ) c.sort)
  comp f g := ContextCat.comp g f
  id_comp f := comp_hole f
  comp_id f := hole_comp f
  assoc f g h := (comp_assoc h g f).symm

/-! ## Plugging is the action of that category on terms

Substituting a term into the hole is functorial: plugging into a composite is
plugging twice, in the order the composite nests.  Stated directly rather than
packaged as a functor into `Type`, because this Mathlib bundles `Type`'s homs in
a structure and the packaging needs its own adaptation; nothing mathematical is
missing. -/

/-- Plugging a term into the hole of a context. -/
def act {Γ : Ctx S} {c s : Hole S Γ} (f : c ⟶ s) (t : Term S Γ c.sort) :
    Term S Γ s.sort :=
  inst f t

/-- Plugging into the bare hole returns the term. -/
theorem act_id {Γ : Ctx S} (c : Hole S Γ) : act (𝟙 c) = id := by
  funext t
  exact inst_hole t

/-- **Plugging into a composite is plugging twice.** -/
theorem act_comp {Γ : Ctx S} {a b c : Hole S Γ} (f : a ⟶ b) (g : b ⟶ c) :
    act (f ≫ g) = fun t => act g (act f t) := by
  funext t
  show inst (ContextCat.comp g f) t = inst g (inst f t)
  have h : (fun (r : S.Srt) (v : Var (b.sort :: Γ) r) =>
      bind (extend t) (holeSub f r v)) = extend (inst f t) := by
    funext r v
    cases v with
    | zero => rfl
    | succ _ => rfl
  show bind (extend t) (bind (holeSub f) g) = _
  rw [bind_comp, h]
  rfl

/-- **Plugging into a composite is plugging twice**, stated without categorical
notation so it can be used as a rewrite anywhere a cut is enlarged. -/
theorem inst_comp {Γ : Ctx S} {a b c : S.Srt} (K : Term S (b :: Γ) c)
    (L : Term S (a :: Γ) b) (t : Term S Γ a) :
    inst (comp K L) t = inst K (inst L t) := by
  have h : (fun (r : S.Srt) (v : Var (b :: Γ) r) =>
      bind (extend t) (holeSub L r v)) = extend (inst L t) := by
    funext r v
    cases v with
    | zero => rfl
    | succ _ => rfl
  show bind (extend t) (bind (holeSub L) K) = _
  rw [bind_comp, h]
  rfl

/-! ## Splittings compose

A splitting is a cut with a term in it.  Cutting the term again refines the cut,
and the term the refined splitting reconstructs is the one the original did: the
place got finer, the state did not change. -/

/-- Refine a splitting by cutting its subterm side again. -/
def Splitting.refine {Γ : Ctx S} {s : S.Srt} (Sp : Splitting S Γ s)
    (Sp' : Splitting S Γ Sp.carrier) : Splitting S Γ s where
  carrier := Sp'.carrier
  ctxt := ContextCat.comp Sp.ctxt Sp'.ctxt
  redex := Sp'.redex

/-- **Refining a cut does not change the state it reconstructs**, provided the
inner cut reconstructs the outer one's subterm. -/
theorem plug_refine {Γ : Ctx S} {s : S.Srt} (Sp : Splitting S Γ s)
    (Sp' : Splitting S Γ Sp.carrier) (h : plug Sp' = Sp.redex) :
    plug (Splitting.refine Sp Sp') = plug Sp := by
  show inst (ContextCat.comp Sp.ctxt Sp'.ctxt) Sp'.redex = inst Sp.ctxt Sp.redex
  have := act_comp (Γ := Γ) (a := ⟨Sp'.carrier⟩) (b := ⟨Sp.carrier⟩) (c := ⟨s⟩)
    Sp'.ctxt Sp.ctxt
  have h2 : inst (ContextCat.comp Sp.ctxt Sp'.ctxt) Sp'.redex
      = inst Sp.ctxt (inst Sp'.ctxt Sp'.redex) := congrFun this Sp'.redex
  rw [h2, show inst Sp'.ctxt Sp'.redex = plug Sp' from rfl, h]

/-- Refining by the trivial cut changes nothing. -/
theorem refine_trivial {Γ : Ctx S} {s : S.Srt} (Sp : Splitting S Γ s) :
    Splitting.refine Sp ⟨Sp.carrier, Term.var Var.zero, Sp.redex⟩ = Sp := by
  cases Sp with
  | mk carrier ctxt redex =>
      show (⟨carrier, ContextCat.comp ctxt (Term.var Var.zero), redex⟩ :
        Splitting S Γ s) = ⟨carrier, ctxt, redex⟩
      rw [comp_hole]

end ContextCat

end Mettapedia.OSLF.Binding
