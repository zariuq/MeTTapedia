/-
# Gauthier minimal-to-org embedding

This file supplies the GSLT-morphism seed requested for the OEIS language family: the six-operator
`minimal` table embeds into the scalar `org` table by interpreting `suc`/`pred` through `addi`/`diff`
with `one`, and by preserving the scalar loop shape.  The theorem is semantic: the table-driven E1
evaluator agrees after translation for all fuel, scalar configurations, and stores.
-/

import Mettapedia.GSLT.LanguageDef.Gauthier.E1

namespace Mettapedia.GSLT.LanguageDef.GauthierEmbedding

open Mettapedia.GSLT.LanguageDef.GauthierE1

/-- The generated minimal grammar.  Every inhabitant is arity-correct by construction. -/
inductive MinimalTerm where
  | zero
  | x
  | y
  | suc : MinimalTerm -> MinimalTerm
  | pred : MinimalTerm -> MinimalTerm
  | loop : MinimalTerm -> MinimalTerm -> MinimalTerm -> MinimalTerm
  deriving Repr

namespace MinimalTerm

/-- Minimal syntax as table-indexed E1 `Prog`. -/
def toMinimalProg : MinimalTerm -> Prog
  | .zero => Minimal.z
  | .x => Minimal.X
  | .y => Minimal.Y
  | .suc a => Minimal.suc a.toMinimalProg
  | .pred a => Minimal.pred a.toMinimalProg
  | .loop f n x0 => Minimal.loop f.toMinimalProg n.toMinimalProg x0.toMinimalProg

/-- The embedding into the scalar `org` table. -/
def toOrgProg : MinimalTerm -> Prog
  | .zero => Org.z
  | .x => Org.X
  | .y => Org.Y
  | .suc a => Org.addi a.toOrgProg Org.o
  | .pred a => Org.diff a.toOrgProg Org.o
  | .loop f n x0 => Org.loop f.toOrgProg n.toOrgProg x0.toOrgProg

set_option linter.unusedSimpArgs false

theorem toMinimal_wellFormed : forall t : MinimalTerm, WellFormed minimalSignature (toMinimalProg t)
  | .zero => .node (e := entry "zero" 0 0 .zero) rfl rfl (by intro c hc; cases hc)
  | .x => .node (e := entry "x" 0 0 .x) rfl rfl (by intro c hc; cases hc)
  | .y => .node (e := entry "y" 0 0 .y) rfl rfl (by intro c hc; cases hc)
  | .suc a => .node (e := entry "suc" 1 0 .suc) rfl rfl (by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact toMinimal_wellFormed a
      · cases hc')
  | .pred a => .node (e := entry "pred" 1 0 .pred) rfl rfl (by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact toMinimal_wellFormed a
      · cases hc')
  | .loop f n x0 => .node (e := entry "loop" 3 1 .loop) rfl rfl (by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact toMinimal_wellFormed f
      · rcases List.mem_cons.mp hc' with rfl | hc''
        · exact toMinimal_wellFormed n
        · rcases List.mem_cons.mp hc'' with rfl | hc'''
          · exact toMinimal_wellFormed x0
          · cases hc''')

theorem toOrg_wellFormed : forall t : MinimalTerm, WellFormed orgE1Signature (toOrgProg t)
  | .zero => .node (e := entry "zero" 0 0 .zero) rfl rfl (by intro c hc; cases hc)
  | .x => .node (e := entry "x" 0 0 .x) rfl rfl (by intro c hc; cases hc)
  | .y => .node (e := entry "y" 0 0 .y) rfl rfl (by intro c hc; cases hc)
  | .suc a => .node (e := entry "addi" 2 0 .addi) rfl rfl (by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact toOrg_wellFormed a
      · rcases List.mem_cons.mp hc' with rfl | hc''
        · exact .node (e := entry "one" 0 0 .one) rfl rfl (by intro c hc; cases hc)
        · cases hc'')
  | .pred a => .node (e := entry "diff" 2 0 .diff) rfl rfl (by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact toOrg_wellFormed a
      · rcases List.mem_cons.mp hc' with rfl | hc''
        · exact .node (e := entry "one" 0 0 .one) rfl rfl (by intro c hc; cases hc)
        · cases hc'')
  | .loop f n x0 => .node (e := entry "loop" 3 1 .loop) rfl rfl (by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact toOrg_wellFormed f
      · rcases List.mem_cons.mp hc' with rfl | hc''
        · exact toOrg_wellFormed n
        · rcases List.mem_cons.mp hc'' with rfl | hc'''
          · exact toOrg_wellFormed x0
          · cases hc''')

mutual

theorem eval_embedding :
    forall (fuel : Nat) (t : MinimalTerm) (cfg : Config) (st : Store),
      eval fuel orgE1Signature t.toOrgProg cfg st =
        eval fuel minimalSignature t.toMinimalProg cfg st
  | 0, _, _, _ => by simp [eval]
  | fuel + 1, .zero, _, _ => by
      simp [toOrgProg, toMinimalProg, Org.z, Minimal.z, eval, orgE1Signature, minimalSignature,
        entryAt, listGet?, entry]
  | fuel + 1, .x, _, _ => by
      simp [toOrgProg, toMinimalProg, Org.X, Minimal.X, eval, orgE1Signature, minimalSignature,
        entryAt, listGet?, entry]
  | fuel + 1, .y, _, _ => by
      simp [toOrgProg, toMinimalProg, Org.Y, Minimal.Y, eval, orgE1Signature, minimalSignature,
        entryAt, listGet?, entry]
  | fuel + 1, .suc a, cfg, st => by
      simp [toOrgProg, toMinimalProg, Org.addi, Org.o, Minimal.suc, eval, orgE1Signature,
        minimalSignature, entryAt, listGet?, entry]
      have ha := eval_embedding fuel a cfg st
      simp [orgE1Signature, minimalSignature, entry] at ha
      rw [ha]
      cases h : eval fuel minimalSignature a.toMinimalProg cfg st with
      | none =>
          have hLit := h
          simp [minimalSignature, entry] at hLit
          rw [hLit]
          rfl
      | some ra =>
          have hLit := h
          simp [minimalSignature, entry] at hLit
          rw [hLit]
          cases fuel with
          | zero => simp [eval] at h
          | succ fuel' => simp [eval, orgE1Signature, entryAt, listGet?, entry]
  | fuel + 1, .pred a, cfg, st => by
      simp [toOrgProg, toMinimalProg, Org.diff, Org.o, Minimal.pred, eval, orgE1Signature,
        minimalSignature, entryAt, listGet?, entry]
      have ha := eval_embedding fuel a cfg st
      simp [orgE1Signature, minimalSignature, entry] at ha
      rw [ha]
      cases h : eval fuel minimalSignature a.toMinimalProg cfg st with
      | none =>
          have hLit := h
          simp [minimalSignature, entry] at hLit
          rw [hLit]
          rfl
      | some ra =>
          have hLit := h
          simp [minimalSignature, entry] at hLit
          rw [hLit]
          cases fuel with
          | zero => simp [eval] at h
          | succ fuel' => simp [eval, orgE1Signature, entryAt, listGet?, entry]
  | fuel + 1, .loop f n x0, cfg, st => by
      simp [toOrgProg, toMinimalProg, Org.loop, Minimal.loop, eval, orgE1Signature,
        minimalSignature, entryAt, listGet?, entry]
      have hnEq := eval_embedding fuel n cfg st
      simp [orgE1Signature, minimalSignature, entry] at hnEq
      rw [hnEq]
      cases hn : eval fuel minimalSignature n.toMinimalProg cfg st with
      | none =>
          have hnLit := hn
          simp [minimalSignature, entry] at hnLit
          rw [hnLit]
          rfl
      | some rn =>
          have hnLit := hn
          simp [minimalSignature, entry] at hnLit
          rw [hnLit]
          simp
          have hxEq := eval_embedding fuel x0 cfg rn.2
          simp [orgE1Signature, minimalSignature, entry] at hxEq
          rw [hxEq]
          cases hx : eval fuel minimalSignature x0.toMinimalProg cfg rn.2 with
          | none =>
              have hxLit := hx
              simp [minimalSignature, entry] at hxLit
              rw [hxLit]
              rfl
          | some rx0 =>
              have hxLit := hx
              simp [minimalSignature, entry] at hxLit
              rw [hxLit]
              have hloop := loop_embedding fuel f rn.1.toNat rx0.1 1 rx0.1 rx0.2
              simp [orgE1Signature, minimalSignature, entry] at hloop
              simpa using hloop

theorem loop_embedding :
    forall (fuel : Nat) (f : MinimalTerm) (k : Nat) (x1 x2 x3 : Int) (st : Store),
      loopIter fuel orgE1Signature f.toOrgProg k x1 x2 x3 st =
        loopIter fuel minimalSignature f.toMinimalProg k x1 x2 x3 st
  | 0, _, _, _, _, _, _ => by simp [loopIter]
  | fuel + 1, _, 0, _, _, _, _ => by simp [loopIter]
  | fuel + 1, f, k + 1, x1, x2, x3, st => by
      simp [loopIter]
      rw [eval_embedding fuel f { x := x1, y := x2, z := x3 } st]
      cases h : eval fuel minimalSignature f.toMinimalProg { x := x1, y := x2, z := x3 } st with
      | none => simp [h]
      | some rf =>
          simp [h, loop_embedding fuel f k rf.1 (x2 + 1) x3 rf.2]

end

theorem term_embedding (fuel : Nat) (t : MinimalTerm) (k : Int) :
    term fuel orgE1Signature t.toOrgProg k =
      term fuel minimalSignature t.toMinimalProg k := by
  simp [term, termWithStore, eval_embedding fuel t (seed k) Store.zero]

end MinimalTerm

/-- Translate a raw minimal-table program when it has the expected table shape. -/
def embedMinimal : Prog -> Option Prog
  | .node 0 [] => some Org.z
  | .node 1 [] => some Org.X
  | .node 2 [] => some Org.Y
  | .node 3 [a] => do
      let a' <- embedMinimal a
      some (Org.addi a' Org.o)
  | .node 4 [a] => do
      let a' <- embedMinimal a
      some (Org.diff a' Org.o)
  | .node 5 [f, n, x0] => do
      let f' <- embedMinimal f
      let n' <- embedMinimal n
      let x0' <- embedMinimal x0
      some (Org.loop f' n' x0')
  | _ => none

def doubleTerm : MinimalTerm :=
  .loop (.suc .x) .x .x

example : WellFormed minimalSignature doubleTerm.toMinimalProg :=
  MinimalTerm.toMinimal_wellFormed doubleTerm

example : WellFormed orgE1Signature doubleTerm.toOrgProg :=
  MinimalTerm.toOrg_wellFormed doubleTerm

example : embedMinimal (Minimal.loop (Minimal.suc Minimal.X) Minimal.X Minimal.X) =
    some doubleTerm.toOrgProg := rfl

example (fuel : Nat) (k : Int) :
    term fuel orgE1Signature doubleTerm.toOrgProg k =
      term fuel minimalSignature doubleTerm.toMinimalProg k :=
  MinimalTerm.term_embedding fuel doubleTerm k

#eval seqPrefix 400 orgE1Signature doubleTerm.toOrgProg 8
#eval seqPrefix 400 minimalSignature doubleTerm.toMinimalProg 8

end Mettapedia.GSLT.LanguageDef.GauthierEmbedding
