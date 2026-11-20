import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ElaborationHygiene

/-!
# Text read with the elements of every tuple kept

`Elaboration.View` reads a tuple whose head is a symbol as a call with its arguments, and any other
tuple as one text (`View.other`). A call through a function variable, `($f a)`, is such a tuple: to say
how its arguments are passed, the reading must keep them.

`HView` is `View` with the elements of those tuples kept (`HView.other o elements`: the head first; no
elements for the empty tuple). `hview` reads text; forgetting the kept elements gives `view`
(`forget_hview`), so every reading here refines the one the elaboration uses.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration

/-- Text as the elaboration reads it, with the elements of a tuple whose head is not a symbol kept. -/
inductive HView where
  | holdMark (orig inside : MData)
  | runMark (orig : MData) (inner : HView)
  | var (orig : MData) (name : Name mkeys)
  | symbol (orig : MData) (name : String)
  | call (orig : MData) (head : String) (args : List HView)
  | inert (orig : MData)
  | other (orig : MData) (elements : List HView)

/-- The text a view was read from. -/
def HView.orig : HView → MData
  | .holdMark o _ => o
  | .runMark o _ => o
  | .var o _ => o
  | .symbol o _ => o
  | .call o _ _ => o
  | .inert o => o
  | .other o _ => o

mutual
/-- Read text at the empty context, keeping the elements of every tuple. -/
def hviewAt {Δ : Ctx MSig} {s : Unit} (t : Term (signature MSig (fam mkeys)) Δ s) (h : Δ = []) : HView :=
  match t with
  | .op (.inl .hold) (.cons u .nil) => .holdMark (atTop h t) (atTop ((List.nil_append Δ).trans h) u)
  | .op (.inl .run) (.cons u .nil) => .runMark (atTop h t) (hviewAt u ((List.nil_append Δ).trans h))
  | .op (.inl (.tup _)) args =>
      match hviewArgsAt args h with
      | .symbol _ f :: rest => .call (atTop h t) f rest
      | elements => .other (atTop h t) elements
  | .op (.inl (.sym f)) _ => .symbol (atTop h t) f
  | .op (.inr (.mk x)) _ => .var (atTop h t) x
  | _ => .inert (atTop h t)

/-- Read the elements of a tuple; elements under binders are not positions. -/
def hviewArgsAt {as : List (List Unit × Unit)} {Δ : Ctx MSig}
    (args : Args (signature MSig (fam mkeys)) as Δ) (h : Δ = []) : List HView :=
  match args with
  | .nil => []
  | .cons (bs := bs) hd tl =>
      if hb : bs = [] then hviewAt hd (by subst hb; exact h) :: hviewArgsAt tl h else hviewArgsAt tl h
end

/-- Read text, keeping the elements of every tuple. -/
def hview (t : MData) : HView := hviewAt t rfl

/-! ## Forgetting the kept elements -/

/-- The elaboration's view of a reading: the kept elements are forgotten. -/
def HView.forget : HView → View
  | .holdMark o u => .holdMark o u
  | .runMark o inner => .runMark o inner.forget
  | .var o x => .var o x
  | .symbol o f => .symbol o f
  | .call o f args => .call o f (forgetAll args)
  | .inert o => .inert o
  | .other o _ => .other o
where
  /-- Forget in every argument. -/
  forgetAll : List HView → List View
    | [] => []
    | a :: rest => a.forget :: forgetAll rest

theorem HView.forget_orig : ∀ v : HView, v.forget.orig = v.orig
  | .holdMark _ _ => rfl
  | .runMark _ _ => rfl
  | .var _ _ => rfl
  | .symbol _ _ => rfl
  | .call _ _ _ => rfl
  | .inert _ => rfl
  | .other _ _ => rfl

/-! The reading of a term, one constructor at a time (by definition). -/

theorem hviewAt_hold {Δ : Ctx MSig} (u : Term (signature MSig (fam mkeys)) ([] ++ Δ) ()) (h : Δ = []) :
    hviewAt (Term.op (Sum.inl MOp.hold) (Args.cons u Args.nil) : Term (signature MSig (fam mkeys)) Δ ()) h =
      .holdMark (atTop h (.op (.inl .hold) (.cons u .nil))) (atTop ((List.nil_append Δ).trans h) u) := rfl

theorem hviewAt_run {Δ : Ctx MSig} (u : Term (signature MSig (fam mkeys)) ([] ++ Δ) ()) (h : Δ = []) :
    hviewAt (Term.op (Sum.inl MOp.run) (Args.cons u Args.nil) : Term (signature MSig (fam mkeys)) Δ ()) h =
      .runMark (atTop h (.op (.inl .run) (.cons u .nil))) (hviewAt u ((List.nil_append Δ).trans h)) := rfl

theorem hviewAt_tup {Δ : Ctx MSig} (n : ℕ) (args : Args (signature MSig (fam mkeys)) (MOp.arity (MOp.tup n)) Δ)
    (h : Δ = []) :
    hviewAt (Term.op (Sum.inl (MOp.tup n)) args : Term (signature MSig (fam mkeys)) Δ ()) h =
      (match hviewArgsAt args h with
       | .symbol _ f :: rest => .call (atTop h (.op (.inl (.tup n)) args)) f rest
       | elements => .other (atTop h (.op (.inl (.tup n)) args)) elements) := rfl

theorem hviewAt_sym {Δ : Ctx MSig} (f : String) (args : Args (signature MSig (fam mkeys)) (MOp.arity (MOp.sym f)) Δ)
    (h : Δ = []) :
    hviewAt (Term.op (Sum.inl (MOp.sym f)) args : Term (signature MSig (fam mkeys)) Δ ()) h =
      .symbol (atTop h (.op (.inl (.sym f)) args)) f := rfl

theorem hviewAt_num {Δ : Ctx MSig} (k : Int) (args : Args (signature MSig (fam mkeys)) (MOp.arity (MOp.num k)) Δ)
    (h : Δ = []) :
    hviewAt (Term.op (Sum.inl (MOp.num k)) args : Term (signature MSig (fam mkeys)) Δ ()) h =
      .inert (atTop h (.op (.inl (.num k)) args)) := rfl

theorem hviewAt_lam {Δ : Ctx MSig} (args : Args (signature MSig (fam mkeys)) (MOp.arity MOp.lam) Δ) (h : Δ = []) :
    hviewAt (Term.op (Sum.inl MOp.lam) args : Term (signature MSig (fam mkeys)) Δ ()) h =
      .inert (atTop h (.op (.inl .lam) args)) := rfl

theorem hviewAt_name {Δ : Ctx MSig} (x : Name mkeys)
    (args : Args (signature MSig (fam mkeys)) ((fam mkeys x).1.map fun sort => ([], sort)) Δ) (h : Δ = []) :
    hviewAt (Term.op (Sum.inr (.mk x)) args : Term (signature MSig (fam mkeys)) Δ ()) h =
      .var (atTop h (.op (.inr (.mk x)) args)) x := rfl

theorem hviewAt_var {Δ : Ctx MSig} (v : Var Δ ()) (h : Δ = []) :
    hviewAt (Term.var v : Term (signature MSig (fam mkeys)) Δ ()) h = .inert (atTop h (.var v)) := rfl

theorem hviewArgsAt_nil {Δ : Ctx MSig} (h : Δ = []) :
    hviewArgsAt (Args.nil : Args (signature MSig (fam mkeys)) [] Δ) h = [] := rfl

theorem hviewArgsAt_cons {as : List (List Unit × Unit)} {bs : List Unit} {Δ : Ctx MSig}
    (hd : Term (signature MSig (fam mkeys)) (bs ++ Δ) ()) (tl : Args (signature MSig (fam mkeys)) as Δ)
    (h : Δ = []) :
    hviewArgsAt (Args.cons (bs := bs) (s := ()) hd tl) h =
      if hb : bs = [] then hviewAt hd (by subst hb; exact h) :: hviewArgsAt tl h else hviewArgsAt tl h := rfl

/-- The tuple clause of the two readings, compared on any list of elements. -/
theorem forget_tuple (o : MData) : ∀ elements : List HView,
    (match elements with
      | .symbol _ f :: rest => HView.call o f rest
      | elements => HView.other o elements).forget =
    (match HView.forget.forgetAll elements with
      | .symbol _ f :: rest => View.call o f rest
      | _ => View.other o)
  | [] => rfl
  | .holdMark _ _ :: _ => rfl
  | .runMark _ _ :: _ => rfl
  | .var _ _ :: _ => rfl
  | .symbol _ _ :: _ => rfl
  | .call _ _ _ :: _ => rfl
  | .inert _ :: _ => rfl
  | .other _ _ :: _ => rfl

mutual
/-- **Forgetting the kept elements gives the elaboration's view.** -/
theorem forget_hviewAt : ∀ {Δ : Ctx MSig} {s : Unit} (t : Term (signature MSig (fam mkeys)) Δ s) (h : Δ = []),
    (hviewAt t h).forget = viewAt t h
  | _, (), .op (.inl .hold) (.cons u .nil), h => rfl
  | _, (), .op (.inl .run) (.cons u .nil), h => by
      rw [hviewAt_run, ElaborationHygiene.viewAt_run]
      simp only [HView.forget]
      rw [forget_hviewAt u ((List.nil_append _).trans h)]
  | _, (), .op (.inl (.tup n)) args, h => by
      rw [hviewAt_tup, ElaborationHygiene.viewAt_tup, forget_tuple, forgetAll_hviewArgsAt args h]
      rfl
  | _, (), .op (.inl (.sym f)) args, h => rfl
  | _, (), .op (.inl (.num k)) args, h => rfl
  | _, (), .op (.inl .lam) args, h => rfl
  | _, (), .op (.inr (.mk x)) args, h => rfl
  | _, (), .var v, h => rfl

theorem forgetAll_hviewArgsAt : ∀ {as : List (List Unit × Unit)} {Δ : Ctx MSig}
    (args : Args (signature MSig (fam mkeys)) as Δ) (h : Δ = []),
    HView.forget.forgetAll (hviewArgsAt args h) = viewArgsAt args h
  | _, _, .nil, h => rfl
  | _, _, .cons (bs := bs) (s := ()) hd tl, h => by
      rw [hviewArgsAt_cons, ElaborationHygiene.viewArgsAt_cons]
      split
      · simp only [HView.forget.forgetAll]
        rw [forget_hviewAt hd _, forgetAll_hviewArgsAt tl h]
      · exact forgetAll_hviewArgsAt tl h
end

/-- **`view` is `hview` with the kept elements forgotten.** -/
theorem forget_hview (t : MData) : (hview t).forget = view t := forget_hviewAt t rfl

#print axioms forget_hview

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables
