import Mettapedia.GSLT.Readers.Rho.Correspondence
import Mettapedia.GSLT.Readers.Megalodon.Record

/-!
# Reading the reference's printing of a rho process gives back that process

`Correspondence.lean` proves that the readers' tree check accepts exactly the derivations of the
`.module` rows. This file ties those rows to the reference itself: it states the strict-core
processes the reference runs, with variables by spelling as its mrho syntax writes them (`RName`,
`RProc`, `RProcs`: one type per phrase sort of the grammar), its printer token by token (the mrho
printer of `rhocalc_syntax.c`, which prints programs and residuals alike), and proves that the check
accepts the printing of every such process with that process's own tree (`RProc.reads`,
`RProc.checks`).

A variable is printed as `$` and its name; the reader reads exactly the names of at least one
printable byte other than `"`, `(`, `)` and `;` (`varName`, `inSort_var`). The reference also
accepts other bytes in a name (a known gap of the lexical layer, refused by the reader).

The printer lemmas `printItems_lit`, `printItems_nt`, `printItems_tok`, `printItems_nil` and
`printTree_node` hold for every grammar; they are taken from the Megalodon reader's record file.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.Readers.Rho.Record

open Mettapedia.GSLT.Readers.SLR
open Mettapedia.GSLT.Readers.TreeCheck
open Mettapedia.GSLT.Readers.TokenProfile (codes ByteSet)
open Mettapedia.GSLT.Readers.TokenProfileV2
open Mettapedia.GSLT.Readers.Rho.Correspondence
open Mettapedia.GSLT.Readers.Rho
open Mettapedia.GSLT.Readers.GrammarCorrespondence
open Mettapedia.GSLT.Readers.Megalodon.Record (printItems_lit printItems_nt printItems_tok printItems_nil
  printTree_node)

/-! ## The reference's processes, with variables by spelling -/

mutual
  /-- A name: a quoted process, or a variable (written `$` and its name). -/
  inductive RName where
    | quote (p : RProc)
    | var (x : String)
  /-- A strict-core process: nil, a parallel composition of any number of components, a send of a
  process on a name, a receive on a name binding a variable in its body, and a drop of a name. -/
  inductive RProc where
    | nil
    | par (ps : RProcs)
    | send (n : RName) (p : RProc)
    | recv (n : RName) (x : String) (p : RProc)
    | drop (n : RName)
  /-- The components of a parallel composition, in order. -/
  inductive RProcs where
    | nil
    | cons (p : RProc) (ps : RProcs)
end

/-! ## The mrho printer, token by token -/

mutual
  def RName.toks : RName → List String
    | .quote p => ["(", "rho:quote"] ++ p.toks ++ [")"]
    | .var x => ["$" ++ x]
  def RProc.toks : RProc → List String
    | .nil => ["rho:nil"]
    | .par ps => ["(", "rho:par"] ++ ps.toks
    | .send n p => ["(", "rho:send"] ++ n.toks ++ p.toks ++ [")"]
    | .recv n x p => ["(", "rho:recv"] ++ n.toks ++ ["$" ++ x] ++ p.toks ++ [")"]
    | .drop n => ["(", "rho:drop"] ++ n.toks ++ [")"]
  def RProcs.toks : RProcs → List String
    | .nil => [")"]
    | .cons p ps => p.toks ++ ps.toks
end

/-- A byte the reader allows in a variable's name. -/
def varByte (n : Nat) : Bool :=
  33 ≤ n && n ≤ 126 && n != 34 && n != 40 && n != 41 && n != 59

/-- A variable's name the reader reads: at least one byte, every byte allowed. -/
def varName (x : String) : Bool := !x.toList.isEmpty && x.toList.all (fun c => varByte c.toNat)

mutual
  /-- Every variable of a name is readable. -/
  def RName.plain : RName → Bool
    | .quote p => p.plain
    | .var x => varName x
  def RProc.plain : RProc → Bool
    | .nil => true
    | .par ps => ps.plain
    | .send n p => n.plain && p.plain
    | .recv n x p => n.plain && varName x && p.plain
    | .drop n => n.plain
  def RProcs.plain : RProcs → Bool
    | .nil => true
    | .cons p ps => p.plain && ps.plain
end

/-! ## The reader's trees of the reference's processes -/

mutual
  def RName.tree : RName → Tree
    | .quote p => .node "name_quote" [p.tree]
    | .var x => .node "name_var" [.leaf "var_tok" ("$" ++ x)]
  def RProc.tree : RProc → Tree
    | .nil => .node "proc_nil" []
    | .par ps => .node "proc_par" [ps.tree]
    | .send n p => .node "proc_send" [n.tree, p.tree]
    | .recv n x p => .node "proc_recv" [n.tree, .leaf "var_tok" ("$" ++ x), p.tree]
    | .drop n => .node "proc_drop" [n.tree]
  def RProcs.tree : RProcs → Tree
    | .nil => .node "procs_end" []
    | .cons p ps => .node "procs_more" [p.tree, ps.tree]
end

/-! ## The grammar's rows for these objects -/

/-- The grammar the readers check against. -/
abbrev G : Grammar := setting.grammar

theorem tokenSorts_G : G.tokenSorts = ["var_tok"] := by decide +kernel

private abbrev l (s : String) : Sym := .lit s
private abbrev n (s : String) : Sym := .nt s

theorem prod_name_quote :
    G.prodOf? "name_quote" = some ⟨"name_quote", "rho_name", [l "(", l "rho:quote", n "rho_proc", l ")"]⟩ := by
  decide +kernel
theorem prod_name_var : G.prodOf? "name_var" = some ⟨"name_var", "rho_name", [.tok "var_tok"]⟩ := by
  decide +kernel
theorem prod_proc_nil : G.prodOf? "proc_nil" = some ⟨"proc_nil", "rho_proc", [l "rho:nil"]⟩ := by
  decide +kernel
theorem prod_proc_par :
    G.prodOf? "proc_par" = some ⟨"proc_par", "rho_proc", [l "(", l "rho:par", n "rho_procs"]⟩ := by
  decide +kernel
theorem prod_proc_send : G.prodOf? "proc_send" =
    some ⟨"proc_send", "rho_proc", [l "(", l "rho:send", n "rho_name", n "rho_proc", l ")"]⟩ := by
  decide +kernel
theorem prod_proc_recv : G.prodOf? "proc_recv" =
    some ⟨"proc_recv", "rho_proc", [l "(", l "rho:recv", n "rho_name", .tok "var_tok", n "rho_proc", l ")"]⟩ := by
  decide +kernel
theorem prod_proc_drop :
    G.prodOf? "proc_drop" = some ⟨"proc_drop", "rho_proc", [l "(", l "rho:drop", n "rho_name", l ")"]⟩ := by
  decide +kernel
theorem prod_procs_end : G.prodOf? "procs_end" = some ⟨"procs_end", "rho_procs", [l ")"]⟩ := by
  decide +kernel
theorem prod_procs_more : G.prodOf? "procs_more" =
    some ⟨"procs_more", "rho_procs", [n "rho_proc", n "rho_procs"]⟩ := by
  decide +kernel

/-! ## A printed variable is a token of its sort -/

theorem var_class : profile.classOf? "var_tok" = some ⟨"var_tok", .points [36],
    .minus (.range 33 126) (.points [34, 40, 41, 59]), ["$"], none⟩ := by
  decide +kernel

theorem inSort_var (x : String) (hx : varName x = true) : G.inSort "var_tok" ("$" ++ x) = true := by
  simp only [varName, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at hx
  obtain ⟨hne, hall⟩ := hx
  simp only [G, setting, Setting.grammar, Correspondence.inSort, Profile.tokenHasSort, var_class,
    codes, String.toList_append]
  have hdollar : "$".toList = ['$'] := rfl
  rw [hdollar]
  simp only [List.cons_append, List.nil_append, List.map_cons, TokenClass.has]
  have hexc : (codes "$" :: List.map codes []).contains ('$'.toNat :: List.map Char.toNat x.toList) =
      false := by
    cases hl : x.toList with
    | nil => exact absurd hl hne
    | cons c cs => simp [codes]
  have hrest : (List.map Char.toNat x.toList).all
      ((ByteSet.range 33 126).minus (ByteSet.points [34, 40, 41, 59])).contains = true := by
    rw [List.all_eq_true]
    intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨c, hc, rfl⟩ := hb
    have := hall c hc
    simp only [varByte, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
    simp [ByteSet.contains, ByteSet.members]
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h34⟩, h40⟩, h41⟩, h59⟩ := this
    exact ⟨⟨c.toNat - 33, by omega, by omega⟩, h34, h40, h41, h59⟩
  have hfirst : (ByteSet.points [36]).contains '$'.toNat = true := by decide
  simp only [hexc, hrest, hfirst, Bool.not_false, Bool.and_true]

/-! ## Completeness: the reference's printing of a process is read as that process -/

mutual
  theorem RName.reads : ∀ (m : RName), m.plain = true →
      ∃ lb ks, m.tree = .node lb ks ∧ printTree G (.node lb ks) = some ("rho_name", m.toks)
    | .quote p, h => by
      obtain ⟨lp, kp, hp, hpp⟩ := RProc.reads p (by simpa [RName.plain] using h)
      refine ⟨"name_quote", [p.tree], by simp [RName.tree], ?_⟩
      rw [printTree_node _ _ _ _ prod_name_quote, hp, printItems_lit, printItems_lit,
        printItems_nt _ _ _ _ _ _ _ hpp, printItems_lit, printItems_nil]
      simp [RName.toks]
    | .var x, h => by
      refine ⟨"name_var", [.leaf "var_tok" ("$" ++ x)], by simp [RName.tree], ?_⟩
      rw [printTree_node _ _ _ _ prod_name_var,
        printItems_tok _ _ _ _ _ (by rw [tokenSorts_G]; decide) (inSort_var x (by simpa [RName.plain] using h)),
        printItems_nil]
      simp [RName.toks]
  theorem RProc.reads : ∀ (p : RProc), p.plain = true →
      ∃ lb ks, p.tree = .node lb ks ∧ printTree G (.node lb ks) = some ("rho_proc", p.toks)
    | .nil, _ => ⟨"proc_nil", [], by simp [RProc.tree], by decide +kernel⟩
    | .par ps, h => by
      obtain ⟨ls, kss, hs, hps⟩ := RProcs.reads ps (by simpa [RProc.plain] using h)
      refine ⟨"proc_par", [ps.tree], by simp [RProc.tree], ?_⟩
      rw [printTree_node _ _ _ _ prod_proc_par, hs, printItems_lit, printItems_lit,
        printItems_nt _ _ _ _ _ _ _ hps, printItems_nil]
      simp [RProc.toks]
    | .send m q, h => by
      simp only [RProc.plain, Bool.and_eq_true] at h
      obtain ⟨lm, km, hm, hpm⟩ := RName.reads m h.1
      obtain ⟨lq, kq, hq, hpq⟩ := RProc.reads q h.2
      refine ⟨"proc_send", [m.tree, q.tree], by simp [RProc.tree], ?_⟩
      rw [printTree_node _ _ _ _ prod_proc_send, hm, hq, printItems_lit, printItems_lit,
        printItems_nt _ _ _ _ _ _ _ hpm, printItems_nt _ _ _ _ _ _ _ hpq, printItems_lit, printItems_nil]
      simp [RProc.toks]
    | .recv m x q, h => by
      simp only [RProc.plain, Bool.and_eq_true] at h
      obtain ⟨lm, km, hm, hpm⟩ := RName.reads m h.1.1
      obtain ⟨lq, kq, hq, hpq⟩ := RProc.reads q h.2
      refine ⟨"proc_recv", [m.tree, .leaf "var_tok" ("$" ++ x), q.tree], by simp [RProc.tree], ?_⟩
      rw [printTree_node _ _ _ _ prod_proc_recv, hm, hq, printItems_lit, printItems_lit,
        printItems_nt _ _ _ _ _ _ _ hpm,
        printItems_tok _ _ _ _ _ (by rw [tokenSorts_G]; decide) (inSort_var x h.1.2),
        printItems_nt _ _ _ _ _ _ _ hpq, printItems_lit, printItems_nil]
      simp [RProc.toks]
    | .drop m, h => by
      obtain ⟨lm, km, hm, hpm⟩ := RName.reads m (by simpa [RProc.plain] using h)
      refine ⟨"proc_drop", [m.tree], by simp [RProc.tree], ?_⟩
      rw [printTree_node _ _ _ _ prod_proc_drop, hm, printItems_lit, printItems_lit,
        printItems_nt _ _ _ _ _ _ _ hpm, printItems_lit, printItems_nil]
      simp [RProc.toks]
  theorem RProcs.reads : ∀ (ps : RProcs), ps.plain = true →
      ∃ lb ks, ps.tree = .node lb ks ∧ printTree G (.node lb ks) = some ("rho_procs", ps.toks)
    | .nil, _ => ⟨"procs_end", [], by simp [RProcs.tree], by decide +kernel⟩
    | .cons p ps, h => by
      simp only [RProcs.plain, Bool.and_eq_true] at h
      obtain ⟨lp, kp, hp, hpp⟩ := RProc.reads p h.1
      obtain ⟨ls, kss, hs, hps⟩ := RProcs.reads ps h.2
      refine ⟨"procs_more", [p.tree, ps.tree], by simp [RProcs.tree], ?_⟩
      rw [printTree_node _ _ _ _ prod_procs_more, hp, hs,
        printItems_nt _ _ _ _ _ _ _ hpp, printItems_nt _ _ _ _ _ _ _ hps, printItems_nil]
      simp [RProcs.toks]
end

/-- The check the engines run accepts the reference's printing of every process at its sort, with
the process's own tree. -/
theorem RProc.checks (p : RProc) (hp : p.plain = true) : check G "rho_proc" p.toks p.tree = true := by
  obtain ⟨lb, ks, h, hpr⟩ := RProc.reads p hp
  simp [check, h, hpr]

/-- A residual line of the reference is a checked item: the item row wraps one process. -/
theorem RProc.checks_item (p : RProc) (hp : p.plain = true) :
    check G "rho_item" p.toks (.node "item_proc" [p.tree]) = true := by
  obtain ⟨lb, ks, h, hpr⟩ := RProc.reads p hp
  have hitem : G.prodOf? "item_proc" = some ⟨"item_proc", "rho_item", [n "rho_proc"]⟩ := by
    decide +kernel
  have : printTree G (.node "item_proc" [p.tree]) = some ("rho_item", p.toks) := by
    rw [printTree_node _ _ _ _ hitem, h, printItems_nt _ _ _ _ _ _ _ hpr, printItems_nil]
    simp
  simp [check, this]

/-! ## Controls -/

/-- The reference's first example, `core_comm_run.mrho`, as data. -/
def coreComm : RProc :=
  .par (.cons (.send (.quote .nil) .nil)
    (.cons (.recv (.quote .nil) "x" (.drop (.var "x"))) .nil))

theorem coreComm_toks : coreComm.toks =
    ["(", "rho:par", "(", "rho:send", "(", "rho:quote", "rho:nil", ")", "rho:nil", ")", "(", "rho:recv",
      "(", "rho:quote", "rho:nil", ")", "$x", "(", "rho:drop", "$x", ")", ")", ")"] := by
  decide +kernel

theorem coreComm_checks : check G "rho_item" coreComm.toks (.node "item_proc" [coreComm.tree]) = true :=
  RProc.checks_item coreComm (by decide +kernel)

/-- Negative control: a variable named with a `;` is not read (the reference ends the token at the
`;`, which begins a comment). -/
theorem semicolon_name_refused : varName "x;c" = false := by decide +kernel

end Mettapedia.GSLT.Readers.Rho.Record
