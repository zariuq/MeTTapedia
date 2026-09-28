import Mettapedia.OSLF.MeTTaIL.Syntax

namespace Mettapedia.OSLF.MeTTaIL.Canonical

open Mettapedia.OSLF.MeTTaIL.Syntax

inductive CanonicalEvalPolicy where
  | rewrite
  | fold
  | hostCodeOnly
deriving DecidableEq, Repr

namespace CanonicalEvalPolicy

/-- Stable canonical spelling, independent of the partial debug formatter. -/
def serialize : CanonicalEvalPolicy → String
  | .rewrite => "Mettapedia.OSLF.MeTTaIL.Canonical.CanonicalEvalPolicy.rewrite"
  | .fold => "Mettapedia.OSLF.MeTTaIL.Canonical.CanonicalEvalPolicy.fold"
  | .hostCodeOnly => "Mettapedia.OSLF.MeTTaIL.Canonical.CanonicalEvalPolicy.hostCodeOnly"

@[simp] theorem serialize_rewrite :
    serialize .rewrite = "Mettapedia.OSLF.MeTTaIL.Canonical.CanonicalEvalPolicy.rewrite" := rfl

@[simp] theorem serialize_fold :
    serialize .fold = "Mettapedia.OSLF.MeTTaIL.Canonical.CanonicalEvalPolicy.fold" := rfl

@[simp] theorem serialize_hostCodeOnly :
    serialize .hostCodeOnly = "Mettapedia.OSLF.MeTTaIL.Canonical.CanonicalEvalPolicy.hostCodeOnly" := rfl

theorem serialize_injective : Function.Injective serialize := by
  intro left right equalSpelling
  cases left <;> cases right <;> revert equalSpelling <;> decide +kernel

end CanonicalEvalPolicy

private def quote (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

private def renderCollType : CollType → String
  | .vec => "Vec"
  | .hashBag => "HashBag"
  | .hashSet => "HashSet"

private def renderCarrierTypeDecl (typeDecl : TypeDecl) : String :=
  match typeDecl.carrier with
  | .ast => typeDecl.name
  | .tokenLabel => s!"![label] as {typeDecl.name}"
  | .tokenRaw => s!"![raw] as {typeDecl.name}"
  | .tokenProof => s!"![proofTok] as {typeDecl.name}"
  | .tokenPath => s!"![path] as {typeDecl.name}"
  | .builtinInt => s!"![i64] as {typeDecl.name}"
  | .builtinString => s!"![str] as {typeDecl.name}"
  | .builtinBool => s!"![bool] as {typeDecl.name}"

def renderTypeExpr : TypeExpr → String
  | .base n => n
  | .arrow d c => s!"[{renderTypeExpr d}->{renderTypeExpr c}]"
  | .multiBinder t => s!"{renderTypeExpr t}*"
  | .collection ct t => s!"{renderCollType ct}({renderTypeExpr t})"

mutual
private def renderSyntaxOp : SyntaxPatternOp → String
  | .var name => name
  | .sep collection separator none => s!"*sep({collection},{quote separator})"
  | .sep _ separator (some source) => s!"{renderSyntaxOp source}.*sep({quote separator})"
  | .zip left right => s!"*zip({left},{right})"
  | .map source params body =>
      let renderedParams := String.intercalate "," params
      let renderedBody := String.intercalate " " (body.map renderSyntaxItem)
      s!"*map({renderSyntaxOp source},|{renderedParams}|{renderedBody})"
  | .opt inner =>
      let renderedInner := String.intercalate " " (inner.map renderSyntaxItem)
      s!"*opt({renderedInner})"

private def renderSyntaxItem : SyntaxItem → String
  | .terminal t => quote t
  | .nonTerminal n => n
  | .separator s => quote s
  | .delimiter l r => s!"delim({quote l},{quote r})"
  | .op op => renderSyntaxOp op
end

private def renderTermParam : TermParam → String
  | .simple n t => s!"{n}:{renderTypeExpr t}"
  | .abstractionNamed binder? n t =>
      let binder := binder?.getD "x"
      s!"^{binder}.{n}:{renderTypeExpr t}"
  | .multiAbstractionNamed binders n t =>
      let binderText :=
        if binders.isEmpty then "xs" else String.intercalate "," binders
      s!"^[{binderText}].{n}:{renderTypeExpr t}"

private def renderRuleContext (ctx : List (String × TypeExpr)) (premises : List Premise) : String :=
  let typeCtx :=
    ctx.map (fun (n, t) => s!"{n}:{renderTypeExpr t}")
  let premiseCtx := premises.map Premise.renderJson
  let blocks :=
    (if typeCtx.isEmpty then [] else [String.intercalate "," typeCtx]) ++
    (if premiseCtx.isEmpty then [] else [String.intercalate "," premiseCtx])
  if blocks.isEmpty then
    ""
  else
    String.intercalate " | " blocks ++ " "

/-- Preserve the authored binding contract in canonical rule identity. -/
private def renderPatternSite : RulePatternSite → String
  | .left => "left"
  | .right => "right"
  | .premise index quantifiers argument =>
      s!"premise({index},{quantifiers},{argument})"

private def renderBindingType : TypeExpr → String
  | .base name => "base(" ++ quote name ++ ")"
  | .arrow domain codomain =>
      "arrow(" ++ renderBindingType domain ++ "," ++ renderBindingType codomain ++ ")"
  | .multiBinder inner => "multi(" ++ renderBindingType inner ++ ")"
  | .collection kind inner =>
      "collection(" ++ renderCollType kind ++ "," ++ renderBindingType inner ++ ")"

private def renderRuleBindings : Option RuleBindingSpec → String
  | none => ""
  | some spec =>
      let dependencies := spec.dependencies.map fun (name, types) =>
        quote name ++ ":[" ++ String.intercalate "," (types.map renderBindingType) ++ "]"
      let occurrences := spec.occurrences.map fun row =>
        quote row.name ++ "@" ++ renderPatternSite row.site ++ "[" ++
          String.intercalate "," (row.path.map toString) ++ "](" ++
          String.intercalate "," (row.arguments.map Pattern.renderJson) ++ ")"
      " {bindings:[" ++ String.intercalate "," dependencies ++ "]|[" ++
        String.intercalate "," occurrences ++ "]}"

/-- Lean-side verbose canonical rendering. Preserves full authored details
    (parameter names, types, syntax patterns, declaration order).
    NOT the same as Rust's zone1_shared_core, which sorts and projects. -/
def verboseCanonical (lang : LanguageDef) : String :=
  Id.run do
    let mut out := ""
    out := out ++ s!"name:{lang.name}\n"
    out := out ++ "options:\n"
    out := out ++ "types:\n"
    for t in lang.types do
      out := out ++ s!"  {renderCarrierTypeDecl t}\n"
    out := out ++ "terms:\n"
    for term in lang.terms do
      let ctx :=
        if term.params.isEmpty then ""
        else String.intercalate "," (term.params.map renderTermParam)
      let synpat := String.intercalate " " (term.syntaxPattern.map renderSyntaxItem)
      out := out ++ s!"  {term.label} . {ctx}|-{synpat}:{term.category}\n"
    out := out ++ "equations:\n"
    for eqn in lang.equations do
      out := out ++ s!"  {eqn.name} . {renderRuleContext eqn.typeContext eqn.premises}|-{eqn.left.renderJson}={eqn.right.renderJson}{renderRuleBindings eqn.bindings}\n"
    out := out ++ "rewrites:\n"
    for rw in lang.rewrites do
      out := out ++ s!"  {rw.name} . {renderRuleContext rw.typeContext rw.premises}|-{rw.left.renderJson}~>{rw.right.renderJson}{renderRuleBindings rw.bindings}\n"
    return out

/-- Render a term in Zone-1 shared-core format: label/category/arity/shape only.
    Matches Rust's render_term_zone1 in canonical.rs:147. -/
private def renderTermZone1Shared (rule : GrammarRule) : String :=
  let arity := rule.params.length
  let shape := String.intercalate "," (rule.params.map fun
    | .simple _ _ => "arg"
    | .abstractionNamed _ _ _ => "lam"
    | .multiAbstractionNamed _ _ _ => "mlam")
  s!"{rule.label} . <{arity}:{shape}>|-<syntax>:{rule.category}"

/-- Zone-1 shared-core canonical rendering.
    Declarations are sorted alphabetically by name and term details are
    projected to label/category/arity/shape.  Runtime configuration is a
    separate extension and therefore absent from this language identity. -/
def zone1SharedCore (lang : LanguageDef) : String :=
  Id.run do
    let mut out := ""
    out := out ++ s!"name:{lang.name}\n"
    -- Types: sorted by name (matches Rust sort_by_key)
    let sortedTypes := lang.types.toArray.qsort (fun a b => a.name < b.name) |>.toList
    out := out ++ "types:\n"
    for t in sortedTypes do
      out := out ++ s!"  {renderCarrierTypeDecl t}\n"
    -- Terms: sorted by label, projected to arity/shape (matches Rust render_term_zone1)
    let sortedTerms := lang.terms.toArray.qsort (fun a b => a.label < b.label) |>.toList
    out := out ++ "terms:\n"
    for term in sortedTerms do
      out := out ++ s!"  {renderTermZone1Shared term}\n"
    -- Equations: sorted by name
    let sortedEqs := lang.equations.toArray.qsort (fun a b => a.name < b.name) |>.toList
    out := out ++ "equations:\n"
    for eqn in sortedEqs do
      out := out ++ s!"  {eqn.name} . {renderRuleContext eqn.typeContext eqn.premises}|-{eqn.left.renderJson}={eqn.right.renderJson}{renderRuleBindings eqn.bindings}\n"
    -- Rewrites: sorted by name
    let sortedRws := lang.rewrites.toArray.qsort (fun a b => a.name < b.name) |>.toList
    out := out ++ "rewrites:\n"
    for rw in sortedRws do
      out := out ++ s!"  {rw.name} . {renderRuleContext rw.typeContext rw.premises}|-{rw.left.renderJson}~>{rw.right.renderJson}{renderRuleBindings rw.bindings}\n"
    return out

private def termPolicy : Option TermEvalPolicy → CanonicalEvalPolicy
  | some .fold => .fold
  | some .oracle => .hostCodeOnly
  | _ => .rewrite

def zone2WithEvalPolicy (lang : LanguageDef) : String :=
  Id.run do
    let mut out := zone1SharedCore lang
    out := out ++ "term-policies:\n"
    for term in lang.terms do
      out := out ++ s!"  {term.label}={(termPolicy term.evalPolicy?).serialize}\n"
    return out

/-! ## Canonical rendering congruence

The following theorem assumes equality of sorted record arrays; it does not
prove sorting invariant under permutation. A full order-independence theorem
must establish that sorting law, using the duplicate-free keys exposed by
structural validation. -/

/-- Equal names and sorted structural contents yield equal Zone-1 renderings. -/
theorem zone1SharedCore_determined_by_sorted_content
    (lang1 lang2 : LanguageDef)
    (hname : lang1.name = lang2.name)
    (htypes : lang1.types.toArray.qsort (fun a b => a.name < b.name) =
              lang2.types.toArray.qsort (fun a b => a.name < b.name))
    (hterms : lang1.terms.toArray.qsort (fun a b => a.label < b.label) =
              lang2.terms.toArray.qsort (fun a b => a.label < b.label))
    (heqs : lang1.equations.toArray.qsort (fun a b => a.name < b.name) =
            lang2.equations.toArray.qsort (fun a b => a.name < b.name))
    (hrws : lang1.rewrites.toArray.qsort (fun a b => a.name < b.name) =
            lang2.rewrites.toArray.qsort (fun a b => a.name < b.name)) :
  zone1SharedCore lang1 = zone1SharedCore lang2 := by
  simp only [zone1SharedCore]
  rw [hname, htypes, hterms, heqs, hrws]

end Mettapedia.OSLF.MeTTaIL.Canonical
