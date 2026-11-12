import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.MatchBuild

/-!
# The printer: decision programs as C over the reference implementation's states

`printFile` writes one C file that defines the interface the specializer's drivers read
(`tcs_compiled[]`, `tcs_ncompiled`, `tcs_count`, `tcs_head_keys_differ`): for each rule, the
program `specialize` returns, printed instruction by instruction, or the generic route when it
returns none. It is the unverified part of the route from a rule to C, and it is meant to stay
small: every instruction prints as a fixed snippet.

* registers are a C array `R`; the slot each use selected is `A[u]`;
* a refusal is `return tcs_refuse(r, REASON, GUARD)`; inside a scan, a failed test of the body
  moves to the next row;
* the wrapper adds what the Lean model leaves to the host: the hand-off to the generic route
  when the frame has variables, live disequations or an open-head row (`tcs_ground_state`), a
  parameter is not ground, a firing asks for its locals, the names would overflow 32 bits, or a
  selected or scanned row is a stored schema; and the head index: a count scans the bucket of
  its value's head, a scan whose body starts by taking an application apart scans that symbol's
  bucket (a row of another head fails the body's first test).

`fault` plants one bug in the printed code, so that the differential can show it catches it:
`1` an equality test of the match code always passes; `2` a count passes when it finds too few;
`3` the takes leave before the guards are decided.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Printer

/-- **Why a scan may visit one bucket.** When a scan's body starts by taking the scanned register
apart as `f` with `len` arguments, a row passes the body only if its label is such an
application; rows of any other head fail, so the printed loop visits the bucket of `f` only. -/
theorem scan_bucket_sound (names : Nat) (rs : Regs) (src f len dst : Nat) (rest : List MInstr)
    (l : Tm) (h : (MInstr.run names (.getApp src f len dst :: rest) (rs.write src l)).isSome = true) :
    ∃ vs, l = .app f vs ∧ vs.length = len := by
  obtain ⟨rs', hrun⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨rs₁, h1, -⟩ := MInstr.run_cons_some hrun
  obtain ⟨vs, hv, hl, -⟩ := getApp_some h1
  rw [Regs.write_same] at hv
  exact ⟨vs, hv, hl⟩

/-- A C string literal. -/
def cString (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun ch =>
    if ch = '\n' then "\\n\"\n  \""
    else if ch = '"' then "\\\""
    else if ch = '\\' then "\\\\"
    else if ch.toNat < 32 then "\\" ++ toString (ch.toNat / 64) ++ toString ((ch.toNat / 8) % 8) ++
      toString (ch.toNat % 8)
    else ch.toString) ++ "\""

def indexIn (t : Tm) : List Tm → Nat
  | [] => 0
  | u :: us => if u = t then 0 else indexIn t us + 1

def constsOfM : MInstr → List Tm
  | .eqConst _ t => [t]
  | _ => []

def constsOf : Instr → List Tm
  | .loadConst _ t => [t]
  | .test m _ => constsOfM m
  | .scanNone _ body _ => body.flatMap constsOfM
  | _ => []

def dedup (l : List Tm) : List Tm :=
  l.foldl (fun acc t => if acc.contains t then acc else acc ++ [t]) []

def regsOfM : MInstr → List Nat
  | .getApp src _ len dst => src :: (List.range len).map (dst + ·)
  | .eqReg a b => [a, b]
  | .eqConst a _ => [a]
  | .eqFresh a _ => [a]

def regsOf : Instr → List Nat
  | .loadParam d _ => [d]
  | .loadConst d _ => [d]
  | .loadFresh d _ => [d]
  | .mkApp d _ args => d :: args
  | .lookup _ d => [d]
  | .test m _ => regsOfM m
  | .countEq v _ _ => [v]
  | .scanNone src body _ => src :: body.flatMap regsOfM
  | .add v => [v]
  | _ => []

def nregs (P : Prog) : Nat := ((P.checks ++ P.commit).flatMap regsOf).foldl max 0 + 1

def reasonC : Reason → String
  | .shapes => "TR_SHAPES, 0"
  | .fits => "TR_FITS, 0"
  | .unsolvable => "TR_UNSOLVABLE, 0"
  | .guard i => "TR_GUARD, " ++ toString i

def codeC (v : Int) : String :=
  if v = -9223372036854775808 then "INT64_MIN" else "INT64_C(" ++ toString v ++ ")"

/-- A closed term, interned at link time. -/
partial def termC (pfx : String) : Tm → String
  | .app f [] => "tr_app(c, " ++ pfx ++ "_S[" ++ toString f ++ "], NULL)"
  | .app f args => "tr_app(c, " ++ pfx ++ "_S[" ++ toString f ++ "], (tr_term[]){" ++
      ", ".intercalate (args.map (termC pfx)) ++ "})"
  | .code v => "tr_code(c, " ++ codeC v ++ ")"
  | .name n => "tr_name(c, " ++ toString n ++ ")"
  | _ => "TR_NONE"

def reg (r : Nat) : String := "R[" ++ toString r ++ "]"

/-- A match instruction; `onFail` is the statement a failed test runs. -/
def mInstrC (pfx : String) (consts : List Tm) (fault : Nat) (onFail ind : String) : MInstr → String
  | .getApp src f len dst =>
      ind ++ "if (ND(c, " ++ reg src ++ ")->kind != TR_APP || ND(c, " ++ reg src ++ ")->val != " ++ pfx ++
        "_S[" ++ toString f ++ "]) " ++ onFail ++ "\n" ++
      String.join ((List.range len).map fun i =>
        ind ++ reg (dst + i) ++ " = ARG(c, " ++ reg src ++ ", " ++ toString i ++ ");\n")
  | .eqReg a b =>
      if fault = 1 then ind ++ "/* planted fault 1: no equality test */\n"
      else ind ++ "if (" ++ reg a ++ " != " ++ reg b ++ ") " ++ onFail ++ "\n"
  | .eqConst a t => ind ++ "if (" ++ reg a ++ " != " ++ pfx ++ "_K[" ++ toString (indexIn t consts) ++ "]) " ++
      onFail ++ "\n"
  | .eqFresh a j => ind ++ "if (" ++ reg a ++ " != tr_name(c, s->nnames + " ++ toString j ++ ")) " ++
      onFail ++ "\n"

/-- An instruction of a rule `ri`. -/
def instrC (pfx : String) (consts : List Tm) (fault : Nat) (generic : String) : Instr → String
  | .loadParam d k => "  " ++ reg d ++ " = p[" ++ toString k ++ "];\n"
  | .loadConst d t => "  " ++ reg d ++ " = " ++ pfx ++ "_K[" ++ toString (indexIn t consts) ++ "];\n"
  | .loadFresh d j => "  " ++ reg d ++ " = tr_name(c, s->nnames + " ++ toString j ++ ");\n"
  | .mkApp d f args =>
      if args.isEmpty then "  " ++ reg d ++ " = tr_app(c, " ++ pfx ++ "_S[" ++ toString f ++ "], NULL);\n"
      else "  {\n    tr_term a_[" ++ toString args.length ++ "] = {" ++ ", ".intercalate (args.map reg) ++
        "};\n    " ++ reg d ++ " = tr_app(c, " ++ pfx ++ "_S[" ++ toString f ++ "], a_);\n  }\n"
  | .needName k => "  if (s->nnames <= " ++ toString k ++ "u) return tcs_refuse(r, TR_SHAPES, 0);\n"
  | .paramMinted k => "  if (tcs_maxname(c, p[" ++ toString k ++ "]) > s->nnames) return tcs_refuse(r, TR_SHAPES, 0);\n"
  | .occNonzero u => "  if (!o[" ++ toString u ++ "]) return tcs_refuse(r, TR_SHAPES, 0);\n"
  | .occDistinct u v why => "  if (o[" ++ toString u ++ "] == o[" ++ toString v ++ "]) return tcs_refuse(r, " ++
      reasonC why ++ ");\n"
  | .lookup u d =>
      "  A[" ++ toString u ++ "] = find_slot(s, o[" ++ toString u ++ "]);\n" ++
      "  if (A[" ++ toString u ++ "] == NIL) return tcs_refuse(r, TR_FITS, 0);\n" ++
      "  if (s->sl[A[" ++ toString u ++ "]].schema) return " ++ generic ++ ";\n" ++
      "  " ++ reg d ++ " = s->sl[A[" ++ toString u ++ "]].label;\n"
  | .test m why => mInstrC pfx consts fault ("return tcs_refuse(r, " ++ reasonC why ++ ");") "  " m
  | .countEq v n why =>
      "  {\n    size_t n_ = 0;\n" ++
      "    for (uint32_t i_ = tcs_bucket_first(s, head_key(s, " ++ reg v ++ ")); i_ != NIL; i_ = s->sl[i_].hnext) {\n" ++
      "      if (s->sl[i_].schema) return " ++ generic ++ ";\n" ++
      "      if (s->sl[i_].label == " ++ reg v ++ ") n_++;\n    }\n" ++
      "    if (n_ " ++ (if fault = 2 then ">" else "!=") ++ " " ++ toString n ++ ") return tcs_refuse(r, " ++
        reasonC why ++ ");\n  }\n"
  | .scanNone src body why =>
      let header := match body with
        | .getApp s' f _ _ :: _ =>
            if s' = src then
              "for (uint32_t i_ = tcs_bucket_first(s, tcs_app_key(" ++ pfx ++ "_S[" ++ toString f ++
                "])); i_ != NIL; i_ = s->sl[i_].hnext)"
            else "for (uint32_t i_ = s->first; i_ != NIL; i_ = s->sl[i_].next)"
        | _ => "for (uint32_t i_ = s->first; i_ != NIL; i_ = s->sl[i_].next)"
      "  " ++ header ++ " {\n" ++
      "    if (s->sl[i_].schema) return " ++ generic ++ ";\n" ++
      "    " ++ reg src ++ " = s->sl[i_].label;\n    do {\n" ++
      String.join (body.map (mInstrC pfx consts fault "break;" "      ")) ++
      "      return tcs_refuse(r, " ++ reasonC why ++ ");\n    } while (0);\n  }\n"
  | .fail why => "  return tcs_refuse(r, " ++ reasonC why ++ ");\n"
  | .remove u => "  remove_occ(s, A[" ++ toString u ++ "]);\n"
  | .mint k => "  s->nnames += " ++ toString k ++ ";\n"
  | .add v => "  {\n    tr_occ id_ = s->next_id++;\n    add_occ(s, id_, " ++ reg v ++
      ", 0);\n    if (r->made) r->made[nm_++] = id_;\n  }\n"

/-- The function of rule `ri` of the theory with prefix `pfx`. -/
def ruleC (pfx : String) (consts : List Tm) (fault : Nat) (ri : Nat) (name : String) (R : Rule) : String :=
  let fn := pfx ++ "_r" ++ toString ri
  let sig := "static tr_verdict " ++ fn ++
    "(tr_state *s, const tr_term *p, const tr_occ *o, tr_result *r, bool commit) {\n"
  let generic := pfx ++ "_generic(" ++ toString ri ++ ", s, p, o, r, commit)"
  match specialize R with
  | none => "/* rule " ++ name ++ ": outside the specialized class */\n" ++ sig ++ "  return " ++ generic ++
      ";\n}\n\n"
  | some P =>
      let isGuard : Instr → Bool := fun i => match i with
        | .scanNone _ _ (.guard _) => true
        | .countEq _ _ (.guard _) => true
        | .test _ (.guard _) => true
        | .fail (.guard _) => true
        | _ => false
      let removes := P.commit.filter fun i => match i with | .remove _ => true | _ => false
      let checks := if fault = 3 then P.checks.takeWhile (fun i => !isGuard i) ++ removes ++
          P.checks.dropWhile (fun i => !isGuard i)
        else P.checks
      let late := if fault = 3 then P.commit.filter fun i => match i with | .remove _ => false | _ => true
        else P.commit
      "/* rule " ++ name ++ ": the verified program, " ++ toString P.checks.length ++ " checks and " ++
        toString P.commit.length ++ " commit instructions */\n" ++ sig ++
      "  tr_ctx *c = s->ctx;\n  tr_result scratch = {0};\n  if (!r) r = &scratch;\n  (void)p;\n  (void)o;\n" ++
      "  if (c != " ++ pfx ++ "_ctx) {\n    fputs(\"tcs: theory " ++ pfx ++
        " is not linked to this context\\n\", stderr);\n    abort();\n  }\n" ++
      "  if (!tcs_ground_state(s) || (commit && r->locals) || (uint64_t)s->nnames + " ++ toString R.fresh ++
        " > UINT32_MAX" ++
        String.join ((List.range R.nparams).map fun k => " || !tcs_ground_param(c, p[" ++ toString k ++ "])") ++
        ")\n    return " ++ generic ++ ";\n" ++
      "  tcs_count.fast++;\n  r->verdict = TR_REFUSED;\n  r->reason = TR_OK;\n  r->guard = 0;\n" ++
      "  tr_term R[" ++ toString (nregs P) ++ "];\n  (void)R;\n" ++
      "  uint32_t A[" ++ toString (max R.uses.length 1) ++ "];\n  (void)A;\n" ++
      "  size_t nm_ = 0;\n  (void)nm_;\n" ++
      String.join (checks.map (instrC pfx consts fault generic)) ++
      "  r->verdict = TR_ADMITTED;\n  r->first_name = s->nnames;\n  if (!commit) return TR_ADMITTED;\n" ++
      String.join (late.map (instrC pfx consts fault generic)) ++
      "  return TR_ADMITTED;\n}\n\n"

/-- One theory: its globals, its generic route, its rules, its link and its table. -/
def theoryC (fault : Nat) (syms : List (Nat × String × Nat)) (ti : Nat) (thIndex : Nat)
    (thName : String) (rules : List (String × Rule)) : String × String :=
  let pfx := "tcs" ++ toString ti
  let consts := dedup (rules.flatMap fun nr => match specialize nr.2 with
    | some P => (P.checks ++ P.commit).flatMap constsOf
    | none => [])
  let nsyms := (syms.map (·.1)).foldl max 0 + 1
  let globals :=
    "/* ==== theory " ++ thName ++ " ==== */\n" ++
    "static uint32_t " ++ pfx ++ "_S[" ++ toString nsyms ++ "];\n" ++
    "static tr_term " ++ pfx ++ "_K[" ++ toString (consts.length + 1) ++ "];\n" ++
    "static tr_ctx *" ++ pfx ++ "_ctx;\nstatic tcs_theory *" ++ pfx ++ "_th;\nstatic int " ++ pfx ++
      "_nth;\nstatic tcs_instance " ++ pfx ++ "_inst;\n" ++
    "static const tcs_theory *" ++ pfx ++ "_schemas(void) { return " ++ pfx ++ "_th ? &" ++ pfx ++ "_th[" ++
      toString thIndex ++ "] : NULL; }\n" ++
    "static tr_verdict " ++ pfx ++
      "_generic(size_t rule, tr_state *s, const tr_term *p, const tr_occ *o, tr_result *r, bool commit) {\n" ++
    "  if (s->ctx != " ++ pfx ++ "_ctx) {\n    fputs(\"tcs: theory " ++ pfx ++
      " is not linked to this context\\n\", stderr);\n    abort();\n  }\n" ++
    "  tcs_count.generic++;\n  const tr_firing *f = tcs_instance_of(&" ++ pfx ++ "_inst, s->ctx, &" ++ pfx ++
      "_th[" ++ toString thIndex ++ "].rules[rule], p, o);\n" ++
    "  return commit ? tr_fire(s, f, r) : tr_admits(s, f, r);\n}\n\n"
  let fns := String.join ((rules.zipIdx).map fun (nr, ri) => ruleC pfx consts fault ri nr.1 nr.2)
  let link :=
    "static bool " ++ pfx ++ "_link(tr_ctx *c) {\n  char err[256];\n  if (" ++ pfx ++ "_th) tcs_free(" ++ pfx ++
      "_th, " ++ pfx ++ "_nth);\n  " ++ pfx ++ "_th = NULL;\n  " ++ pfx ++ "_nth = tcs_read(c, tcs_text, &" ++
      pfx ++ "_th, err, sizeof err);\n" ++
    "  if (" ++ pfx ++ "_nth <= " ++ toString thIndex ++ ") {\n    fprintf(stderr, \"tcs: theory " ++ thName ++
      ": %s\\n\", err);\n    return false;\n  }\n  " ++ pfx ++ "_ctx = c;\n  (void)" ++ pfx ++ "_S;\n  (void)" ++
      pfx ++ "_K;\n" ++
    String.join (syms.map fun (id, nm, ar) => "  " ++ pfx ++ "_S[" ++ toString id ++ "] = tr_symbol(c, " ++
      cString nm ++ ", " ++ toString ar ++ ");\n") ++
    String.join ((consts.zipIdx).map fun (t, j) => "  " ++ pfx ++ "_K[" ++ toString j ++ "] = " ++
      termC pfx t ++ ";\n") ++
    "  return true;\n}\n"
  let table :=
    "static const tcs_compiled_rule " ++ pfx ++ "_rules[] = {\n" ++
    String.join ((rules.zipIdx).map fun (nr, ri) =>
      "  {" ++ cString nr.1 ++ ", " ++ pfx ++ "_r" ++ toString ri ++ ", " ++
        (if (specialize nr.2).isSome then "true" else "false") ++ ", " ++ toString nr.2.nparams ++ ", " ++
        toString nr.2.takes.length ++ ", " ++ toString nr.2.reads.length ++ "},\n") ++
    (if rules.isEmpty then "  {\"\", NULL, false, 0, 0, 0},\n" else "") ++ "};\n\n"
  (globals ++ fns ++ link ++ table,
   "  {" ++ cString thName ++ ", " ++ pfx ++ "_link, " ++ pfx ++ "_schemas, " ++ toString rules.length ++ ", " ++
     pfx ++ "_rules},\n")

/-- The C file for the theories of one rule file. -/
def printFile (fault : Nat) (source text : String) (syms : List (Nat × String × Nat))
    (theories : List (String × List (String × Rule))) : String :=
  let parts := (theories.zipIdx).map fun (th, ti) => theoryC fault syms ti ti th.1 th.2
  "/* Generated by the verified specializer (SpecializedAdmission.specialize) from " ++ source ++
    (if fault = 0 then "" else " WITH PLANTED PRINTER FAULT " ++ toString fault) ++
    ".  Do not edit. */\n#include \"tcs_inside.h\"\n\ntcs_counts tcs_count;\n" ++
  "size_t tcs_head_keys_differ(tr_ctx *c) { return tcs_inside_selfcheck(c); }\n\n" ++
  "static const char tcs_text[] =\n  " ++ cString text ++ ";\n\n" ++
  String.join (parts.map (·.1)) ++
  "const tcs_compiled_theory tcs_compiled[] = {\n" ++ String.join (parts.map (·.2)) ++
  "};\nconst size_t tcs_ncompiled = " ++ toString theories.length ++ ";\n"

/-- How many rules of the theories `specialize` takes. -/
def specializedCount (theories : List (String × List (String × Rule))) : Nat × Nat :=
  (theories.foldl (fun acc th => acc + (th.2.filter fun nr => (specialize nr.2).isSome).length) 0,
   theories.foldl (fun acc th => acc + th.2.length) 0)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Printer
