import Mettapedia.OSLF.Framework.GauthierOEISPruningSoundness

/-!
# Gauthier OEIS Mod-k Residue Pruning

This file adds a certified residue abstraction for the Gauthier OEIS E1
evaluator.  The modulus is configurable; the `k = 2` instance is the parity
base case, while larger `k` refine search pruning with more residue classes.
-/

namespace Mettapedia.OSLF.Framework.GauthierOEISModKPruning

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierProperties
open Mettapedia.OSLF.Framework.GauthierOEISNativeTypes
open Mettapedia.OSLF.Framework.GauthierOEISPruningSoundness
open Mettapedia.OSLF.PresheafNativeType

/-- Integer congruence modulo `k`.  For `k = 0` this degenerates to equality;
the measurement/pruning use sites use positive moduli. -/
def ModEq (k : Nat) (v r : Int) : Prop :=
  ∃ q : Int, v - r = (Int.ofNat k) * q

theorem ModEq.refl (k : Nat) (v : Int) : ModEq k v v := by
  exact ⟨0, by ring⟩

/-- A mod-k abstract value is an over-approximation of possible residues. -/
structure ResidueInfo (k : Nat) where
  denote : Int -> Prop

namespace ResidueInfo

def top (k : Nat) : ResidueInfo k :=
  ⟨fun _ => True⟩

def exact (k : Nat) (r : Int) : ResidueInfo k :=
  ⟨fun v => ModEq k v r⟩

def join {k : Nat} (a b : ResidueInfo k) : ResidueInfo k :=
  ⟨fun v => a.denote v ∨ b.denote v⟩

def add {k : Nat} (a b : ResidueInfo k) : ResidueInfo k :=
  ⟨fun v => ∃ va vb, a.denote va ∧ b.denote vb ∧ ModEq k v (va + vb)⟩

def diff {k : Nat} (a b : ResidueInfo k) : ResidueInfo k :=
  ⟨fun v => ∃ va vb, a.denote va ∧ b.denote vb ∧ ModEq k v (va - vb)⟩

def mult {k : Nat} (a b : ResidueInfo k) : ResidueInfo k :=
  ⟨fun v => ∃ va vb, a.denote va ∧ b.denote vb ∧ ModEq k v (va * vb)⟩

theorem exact_self (k : Nat) (r : Int) : (exact k r).denote r :=
  ModEq.refl k r

theorem add_sound {k : Nat} {a b : ResidueInfo k} {va vb : Int}
    (ha : a.denote va) (hb : b.denote vb) : (add a b).denote (va + vb) :=
  ⟨va, vb, ha, hb, ModEq.refl k (va + vb)⟩

theorem diff_sound {k : Nat} {a b : ResidueInfo k} {va vb : Int}
    (ha : a.denote va) (hb : b.denote vb) : (diff a b).denote (va - vb) :=
  ⟨va, vb, ha, hb, ModEq.refl k (va - vb)⟩

theorem mult_sound {k : Nat} {a b : ResidueInfo k} {va vb : Int}
    (ha : a.denote va) (hb : b.denote vb) : (mult a b).denote (va * vb) :=
  ⟨va, vb, ha, hb, ModEq.refl k (va * vb)⟩

end ResidueInfo

/-- Kleene closure for `loop` over `(accumulator, loopCounter)`. -/
inductive LoopReach (k : Nat) (init : Int -> Prop)
    (step : Int -> Int -> Int -> Prop) : Int -> Int -> Prop where
  | base {x y : Int} : init x -> ModEq k y 1 -> LoopReach k init step x y
  | step {x y x' y' : Int} :
      LoopReach k init step x y ->
      step x y x' ->
      ModEq k y' (y + 1) ->
      LoopReach k init step x' y'

/-- Kleene closure for `loop2` over the two exposed accumulators. -/
inductive Loop2Reach (initX initY : Int -> Prop)
    (step : Int -> Int -> Int -> Int -> Prop) : Int -> Int -> Prop where
  | base {x y : Int} : initX x -> initY y -> Loop2Reach initX initY step x y
  | step {x y x' y' : Int} :
      Loop2Reach initX initY step x y ->
      step x y x' y' ->
      Loop2Reach initX initY step x' y'

def loopResidue {k : Nat} (init : ResidueInfo k)
    (step : Int -> Int -> Int -> Prop) : ResidueInfo k :=
  ⟨fun v => ∃ y, LoopReach k init.denote step v y⟩

def loop2Residue {k : Nat} (initX initY : ResidueInfo k)
    (step : Int -> Int -> Int -> Int -> Prop) : ResidueInfo k :=
  ⟨fun v => ∃ y, Loop2Reach initX.denote initY.denote step v y⟩

/-- Fuel-bounded mod-k analyzer, table-driven against `orgE1Signature`.
Division, modulo, comprehension, and store/tape operations conservatively
return top; arithmetic, conditionals, and loops use residue transfer. -/
def modkAnalyzeFuel (k : Nat) : Nat -> ResidueInfo k -> ResidueInfo k -> Prog -> ResidueInfo k
  | 0, _, _, _ => ResidueInfo.top k
  | fuel + 1, xVal, yVal, .node id ch =>
      match entryAt orgE1Signature id with
      | none => ResidueInfo.top k
      | some e =>
          match e.prim, ch with
          | .zero, [] => ResidueInfo.exact k 0
          | .one, [] => ResidueInfo.exact k 1
          | .two, [] => ResidueInfo.exact k 2
          | .addi, [a, b] =>
              (modkAnalyzeFuel k fuel xVal yVal a).add
                (modkAnalyzeFuel k fuel xVal yVal b)
          | .diff, [a, b] =>
              (modkAnalyzeFuel k fuel xVal yVal a).diff
                (modkAnalyzeFuel k fuel xVal yVal b)
          | .mult, [a, b] =>
              (modkAnalyzeFuel k fuel xVal yVal a).mult
                (modkAnalyzeFuel k fuel xVal yVal b)
          | .cond, [_, t, e'] =>
              (modkAnalyzeFuel k fuel xVal yVal t).join
                (modkAnalyzeFuel k fuel xVal yVal e')
          | .loop, [body, _, init] =>
              let initial := modkAnalyzeFuel k fuel xVal yVal init
              let step := fun x y x' =>
                (modkAnalyzeFuel k fuel (ResidueInfo.exact k x) (ResidueInfo.exact k y) body).denote x'
              loopResidue initial step
          | .loop2, [f, g, _, a, b] =>
              let initialX := modkAnalyzeFuel k fuel xVal yVal a
              let initialY := modkAnalyzeFuel k fuel xVal yVal b
              let step := fun x y x' y' =>
                (modkAnalyzeFuel k fuel (ResidueInfo.exact k x) (ResidueInfo.exact k y) f).denote x' ∧
                  (modkAnalyzeFuel k fuel (ResidueInfo.exact k x) (ResidueInfo.exact k y) g).denote y'
              loop2Residue initialX initialY step
          | .x, [] => xVal
          | .y, [] => yVal
          | _, _ => ResidueInfo.top k

def modkAnalyzeWith (k : Nat) (xVal yVal : ResidueInfo k) (p : Prog) : ResidueInfo k :=
  modkAnalyzeFuel k (progHeight p + 1) xVal yVal p

/-- Observation-specific analysis: the OEIS input `n` is known, so `x` is
specialized to that concrete residue and `y` starts at zero. -/
def certifiedModKAnalysis (k : Nat) (n : Int) (p : Prog) : ResidueInfo k :=
  modkAnalyzeWith k (ResidueInfo.exact k n) (ResidueInfo.exact k 0) p

theorem loopIter_modk_sound {k fuelA : Nat} {body : Prog} {init : ResidueInfo k}
    (ih :
      ∀ (p : Prog) (evalFuel : Nat) (xVal yVal : ResidueInfo k) (cfg : Config)
        (st st' : Store) (v : Int),
        xVal.denote cfg.x ->
        yVal.denote cfg.y ->
        eval evalFuel orgE1Signature p cfg st = some (v, st') ->
        (modkAnalyzeFuel k fuelA xVal yVal p).denote v) :
    let step := fun x y x' =>
      (modkAnalyzeFuel k fuelA (ResidueInfo.exact k x) (ResidueInfo.exact k y) body).denote x'
    ∀ evalFuel count x y z st st' v,
      LoopReach k init.denote step x y ->
      loopIter evalFuel orgE1Signature body count x y z st = some (v, st') ->
      (loopResidue init step).denote v
  | 0, count, x, y, z, st, st', v, hreach, heval => by
      simp [loopIter] at heval
  | evalFuel + 1, count, x, y, z, st, st', v, hreach, heval => by
      cases count with
      | zero =>
          simp [loopIter] at heval
          rcases heval with ⟨hv, _hst⟩
          subst v
          exact ⟨y, hreach⟩
      | succ count =>
          simp [loopIter] at heval
          cases hbody : eval evalFuel orgE1Signature body { x := x, y := y, z := z } st with
          | none =>
              simp [hbody] at heval
          | some rb =>
              simp [hbody] at heval
              have hbodyAbs :
                  (modkAnalyzeFuel k fuelA (ResidueInfo.exact k x)
                    (ResidueInfo.exact k y) body).denote rb.1 :=
                ih body evalFuel (ResidueInfo.exact k x) (ResidueInfo.exact k y)
                  { x := x, y := y, z := z } st rb.2 rb.1
                  (ResidueInfo.exact_self k x)
                  (ResidueInfo.exact_self k y) hbody
              have hreach' :
                  LoopReach k init.denote
                    (fun x y x' =>
                      (modkAnalyzeFuel k fuelA (ResidueInfo.exact k x)
                        (ResidueInfo.exact k y) body).denote x')
                    rb.1 (y + 1) :=
                LoopReach.step hreach hbodyAbs (ModEq.refl k (y + 1))
              exact loopIter_modk_sound ih evalFuel count rb.1 (y + 1) z rb.2 st' v
                hreach' heval

theorem loop2Iter_modk_sound {k fuelA : Nat} {f g : Prog} {initX initY : ResidueInfo k}
    (ih :
      ∀ (p : Prog) (evalFuel : Nat) (xVal yVal : ResidueInfo k) (cfg : Config)
        (st st' : Store) (v : Int),
        xVal.denote cfg.x ->
        yVal.denote cfg.y ->
        eval evalFuel orgE1Signature p cfg st = some (v, st') ->
        (modkAnalyzeFuel k fuelA xVal yVal p).denote v) :
    let step := fun x y x' y' =>
      (modkAnalyzeFuel k fuelA (ResidueInfo.exact k x) (ResidueInfo.exact k y) f).denote x' ∧
        (modkAnalyzeFuel k fuelA (ResidueInfo.exact k x) (ResidueInfo.exact k y) g).denote y'
    ∀ evalFuel count x y z st st' v,
      Loop2Reach initX.denote initY.denote step x y ->
      loop2Iter evalFuel orgE1Signature f g count x y z st = some (v, st') ->
      (loop2Residue initX initY step).denote v
  | 0, count, x, y, z, st, st', v, hreach, heval => by
      simp [loop2Iter] at heval
  | evalFuel + 1, count, x, y, z, st, st', v, hreach, heval => by
      cases count with
      | zero =>
          simp [loop2Iter] at heval
          rcases heval with ⟨hv, _hst⟩
          subst v
          exact ⟨y, hreach⟩
      | succ count =>
          simp [loop2Iter] at heval
          cases hf : eval evalFuel orgE1Signature f { x := x, y := y, z := z } st with
          | none =>
              simp [hf] at heval
          | some rf =>
              simp [hf] at heval
              cases hg : eval evalFuel orgE1Signature g { x := x, y := y, z := z } rf.2 with
              | none =>
                  simp [hg] at heval
              | some rg =>
                  simp [hg] at heval
                  have hfAbs :
                      (modkAnalyzeFuel k fuelA (ResidueInfo.exact k x)
                        (ResidueInfo.exact k y) f).denote rf.1 :=
                    ih f evalFuel (ResidueInfo.exact k x) (ResidueInfo.exact k y)
                      { x := x, y := y, z := z } st rf.2 rf.1
                      (ResidueInfo.exact_self k x)
                      (ResidueInfo.exact_self k y) hf
                  have hgAbs :
                      (modkAnalyzeFuel k fuelA (ResidueInfo.exact k x)
                        (ResidueInfo.exact k y) g).denote rg.1 :=
                    ih g evalFuel (ResidueInfo.exact k x) (ResidueInfo.exact k y)
                      { x := x, y := y, z := z } rf.2 rg.2 rg.1
                      (ResidueInfo.exact_self k x)
                      (ResidueInfo.exact_self k y) hg
                  have hreach' :
                      Loop2Reach initX.denote initY.denote
                        (fun x y x' y' =>
                          (modkAnalyzeFuel k fuelA (ResidueInfo.exact k x)
                            (ResidueInfo.exact k y) f).denote x' ∧
                            (modkAnalyzeFuel k fuelA (ResidueInfo.exact k x)
                              (ResidueInfo.exact k y) g).denote y')
                        rf.1 rg.1 :=
                    Loop2Reach.step hreach ⟨hfAbs, hgAbs⟩
                  exact loop2Iter_modk_sound ih evalFuel count rf.1 rg.1 (z + 1) rg.2 st' v
                    hreach' heval

theorem modkAnalyzeFuel_sound (k : Nat) :
    ∀ fuelA (p : Prog) (evalFuel : Nat) (xVal yVal : ResidueInfo k) (cfg : Config)
      (st st' : Store) (v : Int),
      xVal.denote cfg.x ->
      yVal.denote cfg.y ->
      eval evalFuel orgE1Signature p cfg st = some (v, st') ->
      (modkAnalyzeFuel k fuelA xVal yVal p).denote v
  | 0, p, evalFuel, xVal, yVal, cfg, st, st', v, hx, hy, heval => by
      simp [modkAnalyzeFuel, ResidueInfo.top]
  | fuelA + 1, .node id ch, evalFuel, xVal, yVal, cfg, st, st', v, hx, hy, heval => by
      cases evalFuel with
      | zero =>
          simp [eval] at heval
      | succ evalFuel =>
          simp only [eval] at heval
          unfold modkAnalyzeFuel
          cases hentry : entryAt orgE1Signature id with
          | none =>
              simp [hentry] at heval
          | some e =>
              simp [hentry] at heval ⊢
              cases e with
              | mk name arity hoArity prim =>
                  cases prim with
                  | zero =>
                      cases ch with
                      | nil =>
                          simp [ResidueInfo.exact] at heval ⊢
                          rcases heval with ⟨hv, _hst⟩
                          subst v
                          exact ModEq.refl k 0
                      | cons _ _ =>
                          trivial
                  | one =>
                      cases ch with
                      | nil =>
                          simp [ResidueInfo.exact] at heval ⊢
                          rcases heval with ⟨hv, _hst⟩
                          subst v
                          exact ModEq.refl k 1
                      | cons _ _ =>
                          trivial
                  | two =>
                      cases ch with
                      | nil =>
                          simp [ResidueInfo.exact] at heval ⊢
                          rcases heval with ⟨hv, _hst⟩
                          subst v
                          exact ModEq.refl k 2
                      | cons _ _ =>
                          trivial
                  | suc =>
                      trivial
                  | pred =>
                      trivial
                  | addi =>
                      cases ch with
                      | nil => trivial
                      | cons a rest =>
                          cases rest with
                          | nil => trivial
                          | cons b rest =>
                              cases rest with
                              | nil =>
                                  simp at heval
                                  cases ha : eval evalFuel orgE1Signature a cfg st with
                                  | none => simp [ha] at heval
                                  | some ra =>
                                      simp [ha] at heval
                                      cases hb : eval evalFuel orgE1Signature b cfg ra.2 with
                                      | none => simp [hb] at heval
                                      | some rb =>
                                          simp [hb] at heval
                                          rcases heval with ⟨hv, _hst⟩
                                          subst v
                                          exact ResidueInfo.add_sound
                                            (modkAnalyzeFuel_sound k fuelA a evalFuel xVal yVal
                                              cfg st ra.2 ra.1 hx hy ha)
                                            (modkAnalyzeFuel_sound k fuelA b evalFuel xVal yVal
                                              cfg ra.2 rb.2 rb.1 hx hy hb)
                              | cons _ _ => trivial
                  | diff =>
                      cases ch with
                      | nil => trivial
                      | cons a rest =>
                          cases rest with
                          | nil => trivial
                          | cons b rest =>
                              cases rest with
                              | nil =>
                                  simp at heval
                                  cases ha : eval evalFuel orgE1Signature a cfg st with
                                  | none => simp [ha] at heval
                                  | some ra =>
                                      simp [ha] at heval
                                      cases hb : eval evalFuel orgE1Signature b cfg ra.2 with
                                      | none => simp [hb] at heval
                                      | some rb =>
                                          simp [hb] at heval
                                          rcases heval with ⟨hv, _hst⟩
                                          subst v
                                          exact ResidueInfo.diff_sound
                                            (modkAnalyzeFuel_sound k fuelA a evalFuel xVal yVal
                                              cfg st ra.2 ra.1 hx hy ha)
                                            (modkAnalyzeFuel_sound k fuelA b evalFuel xVal yVal
                                              cfg ra.2 rb.2 rb.1 hx hy hb)
                              | cons _ _ => trivial
                  | mult =>
                      cases ch with
                      | nil => trivial
                      | cons a rest =>
                          cases rest with
                          | nil => trivial
                          | cons b rest =>
                              cases rest with
                              | nil =>
                                  simp at heval
                                  cases ha : eval evalFuel orgE1Signature a cfg st with
                                  | none => simp [ha] at heval
                                  | some ra =>
                                      simp [ha] at heval
                                      cases hb : eval evalFuel orgE1Signature b cfg ra.2 with
                                      | none => simp [hb] at heval
                                      | some rb =>
                                          simp [hb] at heval
                                          rcases heval with ⟨hv, _hst⟩
                                          subst v
                                          exact ResidueInfo.mult_sound
                                            (modkAnalyzeFuel_sound k fuelA a evalFuel xVal yVal
                                              cfg st ra.2 ra.1 hx hy ha)
                                            (modkAnalyzeFuel_sound k fuelA b evalFuel xVal yVal
                                              cfg ra.2 rb.2 rb.1 hx hy hb)
                              | cons _ _ => trivial
                  | divi =>
                      trivial
                  | modu =>
                      trivial
                  | cond =>
                      cases ch with
                      | nil => trivial
                      | cons c rest =>
                          cases rest with
                          | nil => trivial
                          | cons t rest =>
                              cases rest with
                              | nil => trivial
                              | cons e' rest =>
                                  cases rest with
                                  | nil =>
                                      simp at heval
                                      cases hcnd : eval evalFuel orgE1Signature c cfg st with
                                      | none => simp [hcnd] at heval
                                      | some rc =>
                                          simp [hcnd] at heval
                                          by_cases hle : rc.1 ≤ 0
                                          · rw [if_pos hle] at heval
                                            exact Or.inl
                                              (modkAnalyzeFuel_sound k fuelA t evalFuel xVal yVal
                                                cfg rc.2 st' v hx hy heval)
                                          · rw [if_neg hle] at heval
                                            exact Or.inr
                                              (modkAnalyzeFuel_sound k fuelA e' evalFuel xVal yVal
                                                cfg rc.2 st' v hx hy heval)
                                  | cons _ _ => trivial
                  | loop =>
                      cases ch with
                      | nil => trivial
                      | cons body rest =>
                          cases rest with
                          | nil => trivial
                          | cons count rest =>
                              cases rest with
                              | nil => trivial
                              | cons init rest =>
                                  cases rest with
                                  | nil =>
                                      simp at heval
                                      cases hn : eval evalFuel orgE1Signature count cfg st with
                                      | none => simp [hn] at heval
                                      | some rn =>
                                          simp [hn] at heval
                                          cases hi : eval evalFuel orgE1Signature init cfg rn.2 with
                                          | none => simp [hi] at heval
                                          | some ri =>
                                              simp [hi] at heval
                                              let initial := modkAnalyzeFuel k fuelA xVal yVal init
                                              let step := fun x y x' =>
                                                (modkAnalyzeFuel k fuelA (ResidueInfo.exact k x)
                                                  (ResidueInfo.exact k y) body).denote x'
                                              have hinit : initial.denote ri.1 :=
                                                modkAnalyzeFuel_sound k fuelA init evalFuel xVal yVal
                                                  cfg rn.2 ri.2 ri.1 hx hy hi
                                              have hreach : LoopReach k initial.denote step ri.1 1 :=
                                                LoopReach.base hinit (ModEq.refl k 1)
                                              exact loopIter_modk_sound
                                                (k := k) (fuelA := fuelA) (body := body) (init := initial)
                                                (modkAnalyzeFuel_sound k fuelA)
                                                evalFuel rn.1.toNat ri.1 1 ri.1 ri.2 st' v
                                                hreach heval
                                  | cons _ _ => trivial
                  | loop2 =>
                      cases ch with
                      | nil => trivial
                      | cons f rest =>
                          cases rest with
                          | nil => trivial
                          | cons g rest =>
                              cases rest with
                              | nil => trivial
                              | cons count rest =>
                                  cases rest with
                                  | nil => trivial
                                  | cons a rest =>
                                      cases rest with
                                      | nil => trivial
                                      | cons b rest =>
                                          cases rest with
                                          | nil =>
                                              simp at heval
                                              cases hn : eval evalFuel orgE1Signature count cfg st with
                                              | none => simp [hn] at heval
                                              | some rn =>
                                                  simp [hn] at heval
                                                  cases ha : eval evalFuel orgE1Signature a cfg rn.2 with
                                                  | none => simp [ha] at heval
                                                  | some ra =>
                                                      simp [ha] at heval
                                                      cases hb : eval evalFuel orgE1Signature b cfg ra.2 with
                                                      | none => simp [hb] at heval
                                                      | some rb =>
                                                          simp [hb] at heval
                                                          let initialX := modkAnalyzeFuel k fuelA xVal yVal a
                                                          let initialY := modkAnalyzeFuel k fuelA xVal yVal b
                                                          let step := fun x y x' y' =>
                                                            (modkAnalyzeFuel k fuelA (ResidueInfo.exact k x)
                                                              (ResidueInfo.exact k y) f).denote x' ∧
                                                              (modkAnalyzeFuel k fuelA (ResidueInfo.exact k x)
                                                                (ResidueInfo.exact k y) g).denote y'
                                                          have hinitX : initialX.denote ra.1 :=
                                                            modkAnalyzeFuel_sound k fuelA a evalFuel xVal yVal
                                                              cfg rn.2 ra.2 ra.1 hx hy ha
                                                          have hinitY : initialY.denote rb.1 :=
                                                            modkAnalyzeFuel_sound k fuelA b evalFuel xVal yVal
                                                              cfg ra.2 rb.2 rb.1 hx hy hb
                                                          have hreach : Loop2Reach initialX.denote initialY.denote step ra.1 rb.1 :=
                                                            Loop2Reach.base hinitX hinitY
                                                          exact loop2Iter_modk_sound
                                                            (k := k) (fuelA := fuelA) (f := f) (g := g)
                                                            (initX := initialX) (initY := initialY)
                                                            (modkAnalyzeFuel_sound k fuelA)
                                                            evalFuel rn.1.toNat ra.1 rb.1 1 rb.2 st' v
                                                            hreach heval
                                          | cons _ _ => trivial
                  | compr =>
                      trivial
                  | loope =>
                      trivial
                  | x =>
                      cases ch with
                      | nil =>
                          simp at heval
                          rcases heval with ⟨hv, _hst⟩
                          subst v
                          exact hx
                      | cons _ _ =>
                          trivial
                  | y =>
                      cases ch with
                      | nil =>
                          simp at heval
                          rcases heval with ⟨hv, _hst⟩
                          subst v
                          exact hy
                      | cons _ _ =>
                          trivial
                  | z =>
                      trivial
                  | array =>
                      trivial
                  | assign =>
                      trivial
                  | next =>
                      trivial
                  | prev =>
                      trivial
                  | write =>
                      trivial
                  | read =>
                      trivial

theorem certified_modk_sound {k : Nat} {p : Prog} {fuel : Nat} {n v : Int} {st' : Store}
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    (certifiedModKAnalysis k n p).denote v := by
  unfold certifiedModKAnalysis modkAnalyzeWith
  exact modkAnalyzeFuel_sound k (progHeight p + 1) p fuel
    (ResidueInfo.exact k n) (ResidueInfo.exact k 0) (seed n) Store.zero st' v
    (ResidueInfo.exact_self k n) (ResidueInfo.exact_self k 0) heval

def ModKCompatible (k : Nat) (p : Prog) (obs : ObservedTerm) : Prop :=
  (certifiedModKAnalysis k obs.seedValue p).denote obs.value

def ModKIncompatible (k : Nat) (p : Prog) (target : List ObservedTerm) : Prop :=
  ∃ obs, obs ∈ target ∧ ¬ ModKCompatible k p obs

/-- Mod-k pruning is admissible: excluding an observed target residue proves the
candidate cannot reproduce that target. -/
theorem certified_modk_pruning_admissible {k : Nat} {p : Prog} {target : List ObservedTerm}
    (hbad : ModKIncompatible k p target) :
    ¬ Reproduces p target := by
  intro hrep
  rcases hbad with ⟨obs, hmem, hobs⟩
  rcases hrep obs hmem with ⟨fuel, st', heval⟩
  exact hobs (certified_modk_sound (k := k) heval)

/-- Native type of certified mod-k observations. -/
def modKNativeType (k : Nat) : ConstructorNativeType gauthierOEIS where
  sort := signNativeType.sort
  pred := fun pat =>
    ∃ p n v, pat = evalObsPattern p v ∧ (certifiedModKAnalysis k n p).denote v

theorem modKNativeType_sound {k : Nat} {p : Prog} {fuel : Nat} {n v : Int} {st' : Store}
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    (modKNativeType k).pred (evalObsPattern p v) := by
  exact ⟨p, n, v, rfl, certified_modk_sound (k := k) heval⟩

/-! ## Non-vacuity canaries -/

def twoProg : Prog := .node 2 []
def observedTwoAt0 : ObservedTerm := { n := 0, value := 2 }
def twoTarget : List ObservedTerm := [observedTwoAt0]

theorem zero_mod3_incompatible_with_one_observation :
    ¬ ModKCompatible 3 zeroProg observedOneAt0 := by
  intro h
  simp [ModKCompatible, certifiedModKAnalysis, modkAnalyzeWith, zeroProg,
    observedOneAt0, ObservedTerm.seedValue, modkAnalyzeFuel, ResidueInfo.exact,
    ModEq, progHeight, orgE1Signature, entryAt, listGet?, entry] at h
  rcases h with ⟨q, hq⟩
  omega

theorem one_mod3_compatible_with_one_observation :
    ModKCompatible 3 oneProg observedOneAt0 := by
  simp [ModKCompatible, certifiedModKAnalysis, modkAnalyzeWith, oneProg,
    observedOneAt0, ObservedTerm.seedValue, modkAnalyzeFuel, ResidueInfo.exact,
    ModEq, progHeight, orgE1Signature, entryAt, listGet?, entry]

theorem two_mod3_incompatible_with_one_observation :
    ¬ ModKCompatible 3 twoProg observedOneAt0 := by
  intro h
  simp [ModKCompatible, certifiedModKAnalysis, modkAnalyzeWith, twoProg,
    observedOneAt0, ObservedTerm.seedValue, modkAnalyzeFuel, ResidueInfo.exact,
    ModEq, progHeight, orgE1Signature, entryAt, listGet?, entry] at h
  rcases h with ⟨q, hq⟩
  omega

example : ModKIncompatible 3 zeroProg oneTarget := by
  refine ⟨observedOneAt0, by simp [oneTarget], ?_⟩
  exact zero_mod3_incompatible_with_one_observation

example : ¬ Reproduces zeroProg oneTarget :=
  certified_modk_pruning_admissible
    (k := 3) (p := zeroProg) (target := oneTarget)
    (by
      refine ⟨observedOneAt0, by simp [oneTarget], ?_⟩
      exact zero_mod3_incompatible_with_one_observation)

example : ¬ ModKIncompatible 3 oneProg oneTarget := by
  intro hbad
  rcases hbad with ⟨obs, hmem, hobs⟩
  simp [oneTarget] at hmem
  subst obs
  exact hobs one_mod3_compatible_with_one_observation

example : Reproduces oneProg oneTarget := by
  intro obs hmem
  simp [oneTarget] at hmem
  subst obs
  refine ⟨1, Store.zero, ?_⟩
  simp [oneProg, observedOneAt0, ObservedTerm.seedValue, eval, orgE1Signature,
    entryAt, listGet?, entry, seed]

example : ModKIncompatible 3 twoProg oneTarget := by
  refine ⟨observedOneAt0, by simp [oneTarget], ?_⟩
  exact two_mod3_incompatible_with_one_observation

end Mettapedia.OSLF.Framework.GauthierOEISModKPruning
