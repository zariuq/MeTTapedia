#!/usr/bin/env python3
import json
import os
import subprocess
import sys
from pathlib import Path

GF_LD = '/home/zar/.local/gf-extract/usr/lib'

def ensure_runtime_libs():
    cur = os.environ.get('LD_LIBRARY_PATH', '')
    parts = [x for x in cur.split(':') if x]
    if GF_LD in parts:
        return
    new_parts = [GF_LD] + parts
    env = os.environ.copy()
    env['LD_LIBRARY_PATH'] = ':'.join(new_parts)
    os.execvpe(sys.executable, [sys.executable, __file__, *sys.argv[1:]], env)

ensure_runtime_libs()

GF_BIN = Path('/home/zar/claude/lean-projects/mettapedia/Mettapedia/Languages/GF/SUMO/eng/gf')
GF_LIB = Path('/home/zar/claude/gf-rgl')
PGF_PY_EGG = Path('/home/zar/.local/gf-extract/usr/local/lib/python3.12/dist-packages/pgf-1.1-py3.12-linux-x86_64.egg')
ROOT = Path('/home/zar/claude/lean-projects/algorithms/gf_fragments')
GENERATED = ROOT / 'generated'
JSON_EXPORT_DIR = ROOT / 'json_export'
PGF_PATH = ROOT / 'PaperAmbiguity.pgf'
METTAPEDIA_GENERATED = Path('/home/zar/claude/lean-projects/mettapedia/Mettapedia/Languages/GF/Generated')
LEAN_WITNESS_OUT = METTAPEDIA_GENERATED / 'PaperAmbiguityPGFWitnesses.lean'
ALGORITHMS_GENERATED = Path('/home/zar/claude/lean-projects/algorithms/Algorithms/GF/Generated')
LEAN_IR_OUT = ALGORITHMS_GENERATED / 'PaperAmbiguityIR.lean'
JSON_WITNESSES_OUT = GENERATED / 'paper_ambiguity_parse_witnesses.json'
JSON_GRAMMAR_OUT = GENERATED / 'PaperAmbiguity.gf.json'

# The cross-language witness fragment currently uses parseable present-tense
# surfaces in both languages. The tiny Czech concrete exposes `TPast` with a
# non-parseable marker string, so `TPres` is the honest common denominator until
# Czech past morphology is normalized in the fragment.
SURFACES = [
    ('PaperAmbiguityEng', 'englishTelescope', 'John sees the man with the telescope'),
    ('PaperAmbiguityEng', 'englishAnna', 'Anna dresses the baby in the crib'),
    ('PaperAmbiguityCze', 'czechTelescope', 'Jan vidí muže s teleskopem'),
    ('PaperAmbiguityCze', 'czechAnna', 'Anna obléká dítě v kolébkě'),
]


def ensure_dirs():
    GENERATED.mkdir(parents=True, exist_ok=True)
    JSON_EXPORT_DIR.mkdir(parents=True, exist_ok=True)
    METTAPEDIA_GENERATED.mkdir(parents=True, exist_ok=True)
    ALGORITHMS_GENERATED.mkdir(parents=True, exist_ok=True)


def gf_path_arg() -> str:
    paths = [
        '.',
        str(GF_LIB / 'src/abstract'),
        str(GF_LIB / 'src/common'),
        str(GF_LIB / 'src/prelude'),
        str(GF_LIB / 'src/api'),
        str(GF_LIB / 'src/english'),
        str(GF_LIB / 'src/czech'),
    ]
    return ':'.join(paths)


def run_gf_json_export():
    cmd = [
        str(GF_BIN),
        '--output-format=json',
        f'--output-dir={JSON_EXPORT_DIR}',
        f'--path={gf_path_arg()}',
        '--make',
        'PaperAmbiguityEng.gf',
        'PaperAmbiguityCze.gf',
    ]
    subprocess.run(cmd, cwd=ROOT, check=True, env=os.environ.copy())
    src = JSON_EXPORT_DIR / 'PaperAmbiguity.json'
    JSON_GRAMMAR_OUT.write_text(src.read_text())


def load_pgf_module():
    sys.path.insert(0, str(PGF_PY_EGG))
    import pgf  # type: ignore
    return pgf


def tokenize_surface(surface: str) -> list[str]:
    toks = []
    curr = []
    for ch in surface:
        if ch.isalnum() or ch in "'_":
            curr.append(ch.lower())
        else:
            if curr:
                toks.append(''.join(curr))
                curr = []
    if curr:
        toks.append(''.join(curr))
    return toks


def export_expr(expr, fun_sigs):
    fun, args = expr.unpack()
    return {
        'fun': fun,
        'cat': fun_sigs[fun]['cat'],
        'args': [export_expr(arg, fun_sigs) for arg in args],
    }


def collect_leaf_refs(tree, acc, path=()):
    if not tree['args']:
        acc.append((path, tree['fun']))
    else:
        for i, arg in enumerate(tree['args']):
            collect_leaf_refs(arg, acc, path + (i,))


def collect_bracket_leaves(node, acc):
    if isinstance(node, str):
        return
    child_tokens = []
    for child in node.children:
        if isinstance(child, str):
            child_tokens.extend(tokenize_surface(child))
        else:
            collect_bracket_leaves(child, acc)
    if child_tokens:
        acc.append((node.fun, child_tokens))


def set_tokens_at_path(tree, path, tokens):
    if not path:
        tree['tokens'] = tokens
        return
    set_tokens_at_path(tree['args'][path[0]], path[1:], tokens)


def fill_zero_tokens(tree):
    if 'tokens' not in tree:
        tree['tokens'] = []
    for arg in tree['args']:
        fill_zero_tokens(arg)


def synth_tokens(tree):
    if not tree['args']:
        return tree['tokens']
    out = []
    for arg in tree['args']:
        out.extend(synth_tokens(arg))
    tree['tokens'] = out
    return out


def export_annotated_expr(expr, concr, fun_sigs):
    tree = export_expr(expr, fun_sigs)
    leaf_refs = []
    collect_leaf_refs(tree, leaf_refs)
    bracket_leaves = []
    for bracket in concr.bracketedLinearize(expr):
        collect_bracket_leaves(bracket, bracket_leaves)
    idx = 0
    for path, fun in leaf_refs:
        if idx < len(bracket_leaves) and bracket_leaves[idx][0] == fun:
            set_tokens_at_path(tree, path, bracket_leaves[idx][1])
            idx += 1
        else:
            set_tokens_at_path(tree, path, [])
    fill_zero_tokens(tree)
    synth_tokens(tree)
    tree['surface'] = concr.linearize(expr)
    return tree


def export_plain_tree(tree):
    return {'fun': tree['fun'], 'args': [export_plain_tree(arg) for arg in tree['args']]}


def collect_functions(tree, out):
    out.add(tree['fun'])
    for arg in tree['args']:
        collect_functions(arg, out)


def parse_witnesses(grammar_json):
    pgf = load_pgf_module()
    pgf_obj = pgf.readPGF(str(PGF_PATH))
    witness_entries = []
    used = set()
    fun_sigs = grammar_json['abstract']['funs']
    for lang, label, surface in SURFACES:
        concr = pgf_obj.languages[lang]
        parses = []
        for prob, expr in concr.parse(surface):
            tree = export_annotated_expr(expr, concr, fun_sigs)
            parses.append({'prob': prob, 'tree': tree})
            collect_functions(tree, used)
        witness_entries.append({
            'label': label,
            'language': lang,
            'surface': surface,
            'parseCount': len(parses),
            'parses': parses,
        })
    bundle = {
        'grammar': 'PaperAmbiguity',
        'witnesses': witness_entries,
        'usedFunctions': sorted(used),
    }
    JSON_WITNESSES_OUT.write_text(json.dumps(bundle, ensure_ascii=False, indent=2) + '\n')
    return bundle


def lean_str(s: str) -> str:
    return json.dumps(s, ensure_ascii=False)


def render_tree(tree, indent=''):
    if not tree['args']:
        return f'.node {lean_str(tree["fun"])} []'
    child_indent = indent + '  '
    rendered_children = ',\n'.join(child_indent + render_tree(arg, child_indent) for arg in tree['args'])
    return f'.node {lean_str(tree["fun"])} [\n{rendered_children}\n{indent}]'


def render_abstract_node(tree, indent=''):
    fname = tree['fun']
    const = f'FunctionSig.{fname}'
    if not tree['args']:
        return f'.leaf {lean_str(fname)} (FunctionSig.resultCategory {const}.type)'
    child_indent = indent + '  '
    rendered_children = ',\n'.join(child_indent + render_abstract_node(arg, child_indent) for arg in tree['args'])
    return f'.apply {const} [\n{rendered_children}\n{indent}]'


def render_witness_def(entry):
    lines = []
    lines.append(f'def {entry["label"]}Surface : String := {lean_str(entry["surface"])}')
    lines.append(f'def {entry["label"]}Language : String := {lean_str(entry["language"])}')
    for idx, parse in enumerate(entry['parses'], start=1):
        plain_tree = export_plain_tree(parse['tree'])
        lines.append(f'def {entry["label"]}Parse{idx} : ExportedTree :=')
        lines.append('  ' + render_tree(plain_tree, '  '))
        lines.append(f'def {entry["label"]}AbstractNode{idx} : AbstractNode :=')
        lines.append('  ' + render_abstract_node(plain_tree, '  '))
        lines.append(f'def {entry["label"]}Prob{idx} : Float := {parse["prob"]}')
    parse_names = ', '.join(f'{entry["label"]}Parse{i}' for i in range(1, len(entry['parses']) + 1))
    abs_names = ', '.join(f'{entry["label"]}AbstractNode{i}' for i in range(1, len(entry['parses']) + 1))
    lines.append(f'def {entry["label"]}Parses : List ExportedTree := [{parse_names}]')
    lines.append(f'def {entry["label"]}Recovered : List AbstractNode := [{abs_names}]')
    return '\n'.join(lines)


def write_witness_lean(bundle):
    entries = []
    for entry in bundle['witnesses']:
        entries.append(render_witness_def(entry))
    used_funs = ', '.join(lean_str(f) for f in bundle['usedFunctions'])
    content = f'''import Mettapedia.Languages.GF.Abstract
import Mettapedia.Languages.GF.PGFWitnessIR

namespace Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses

open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.PGFWitnessIR

{'\n\n'.join(entries)}

def allWitnessParses : List (String × String × String × List ExportedTree) := [
  ({lean_str('englishTelescope')}, englishTelescopeLanguage, englishTelescopeSurface, englishTelescopeParses),
  ({lean_str('englishAnna')}, englishAnnaLanguage, englishAnnaSurface, englishAnnaParses),
  ({lean_str('czechTelescope')}, czechTelescopeLanguage, czechTelescopeSurface, czechTelescopeParses),
  ({lean_str('czechAnna')}, czechAnnaLanguage, czechAnnaSurface, czechAnnaParses)
]

def usedFunctions : List String := [{used_funs}]

def grammarName : String := {lean_str(bundle['grammar'])}

end Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses
'''
    LEAN_WITNESS_OUT.write_text(content)


def semexpr_const(tree):
    if not tree['args']:
        return {'kind': 'node', 'fun': tree['fun'], 'args': []}
    return {'kind': 'node', 'fun': tree['fun'], 'args': [semexpr_const(arg) for arg in tree['args']]}


def semexpr_from_children(tree, child_refs):
    args = []
    for idx, arg in enumerate(tree['args']):
        if idx in child_refs:
            args.append({'kind': 'ref', 'index': child_refs[idx]})
        else:
            args.append(semexpr_const(arg))
    return {'kind': 'node', 'fun': tree['fun'], 'args': args}


def render_semexpr(expr, indent=''):
    if expr['kind'] == 'ref':
        return f'.ref {expr["index"]}'
    if not expr['args']:
        return f'.node {lean_str(expr["fun"])} []'
    child_indent = indent + '  '
    children = ',\n'.join(child_indent + render_semexpr(arg, child_indent) for arg in expr['args'])
    return f'.node {lean_str(expr["fun"])} [\n{children}\n{indent}]'


def unique_cat(label, parse_idx, path, cat):
    suffix = '_'.join(str(i) for i in path) if path else 'root'
    return f'{cat}__{label}__p{parse_idx}__{suffix}'


def compile_tree(tree, label, parse_idx, path, is_root=False):
    positive_children = []
    rules = []
    child_sem_slots = {}
    for idx, child in enumerate(tree['args']):
        compiled = compile_tree(child, label, parse_idx, path + [idx], False)
        rules.extend(compiled['rules'])
        if compiled['cat'] is not None:
            child_sem_slots[idx] = len(positive_children)
            positive_children.append(compiled)
    if len(tree['tokens']) == 0:
        return {
            'cat': None,
            'sem': semexpr_const(tree),
            'rules': rules,
            'expected': export_plain_tree(tree),
        }

    cat = tree['cat'] if is_root else unique_cat(label, parse_idx, path, tree['cat'])
    sem = semexpr_from_children(tree, child_sem_slots)
    if not tree['args']:
        if len(tree['tokens']) != 1:
            raise ValueError(f'Nonterminal leaf {tree["fun"]} has token yield {tree["tokens"]}')
        rules.append({
            'lhs': cat,
            'rhs': {'kind': 'terminal', 'token': tree['tokens'][0]},
            'funName': tree['fun'],
            'sem': semexpr_const(tree),
        })
    elif len(positive_children) == 1:
        rules.append({
            'lhs': cat,
            'rhs': {'kind': 'unary', 'cat': positive_children[0]['cat']},
            'funName': tree['fun'],
            'sem': sem,
        })
    elif len(positive_children) == 2:
        rules.append({
            'lhs': cat,
            'rhs': {'kind': 'binary', 'left': positive_children[0]['cat'], 'right': positive_children[1]['cat']},
            'funName': tree['fun'],
            'sem': sem,
        })
    else:
        raise ValueError(f'Cannot normalize {tree["fun"]}: {len(positive_children)} positive children')

    return {
        'cat': cat,
        'sem': sem,
        'rules': rules,
        'expected': export_plain_tree(tree),
    }


def render_rule(rule):
    rhs = rule['rhs']
    if rhs['kind'] == 'terminal':
        rhs_rendered = f'.terminal {lean_str(rhs["token"])}'
    elif rhs['kind'] == 'unary':
        rhs_rendered = f'.unary {lean_str(rhs["cat"])}'
    else:
        rhs_rendered = f'.binary {lean_str(rhs["left"])} {lean_str(rhs["right"])}'
    return f'''  {{ lhs := {lean_str(rule["lhs"])}, rhs := {rhs_rendered}, funName := {lean_str(rule["funName"])}, sem := {render_semexpr(rule["sem"], '  ')} }}'''


def render_exported_tree_alg(tree, indent=''):
    if not tree['args']:
        return f'.node {lean_str(tree["fun"])} []'
    child_indent = indent + '  '
    rendered_children = ',\n'.join(child_indent + render_exported_tree_alg(arg, child_indent) for arg in tree['args'])
    return f'.node {lean_str(tree["fun"])} [\n{rendered_children}\n{indent}]'


def render_array_trees(name, trees):
    rendered = ',\n'.join('  ' + render_exported_tree_alg(t, '  ') for t in trees)
    return f'''def {name} : Array ExportedTree := #[\n{rendered}\n]'''


def build_language_ir(bundle, language, surface_specs):
    grammar_rules = []
    witness_defs = []
    for label, surface_name in surface_specs:
        entry = next(w for w in bundle['witnesses'] if w['label'] == label)
        expected_trees = []
        for idx, parse in enumerate(entry['parses'], start=1):
            compiled = compile_tree(parse['tree'], label, idx, [], True)
            grammar_rules.extend(compiled['rules'])
            expected_trees.append(compiled['expected'])
        witness_defs.append((label, surface_name, entry['surface'], expected_trees))
    return grammar_rules, witness_defs


def render_grammar(name, language, rules):
    rendered_rules = ',\n'.join(render_rule(rule) for rule in rules)
    return f'''def {name} : NormalizedGrammar :=
  {{ language := {lean_str(language)}, startCats := #[{lean_str('S')}], productions := #[\n{rendered_rules}\n  ] }}'''


def write_algorithms_ir(bundle):
    english_rules, english_defs = build_language_ir(bundle, 'PaperAmbiguityEng', [
        ('englishTelescope', 'englishTelescopeSurface'),
        ('englishAnna', 'englishAnnaSurface'),
    ])
    czech_rules, czech_defs = build_language_ir(bundle, 'PaperAmbiguityCze', [
        ('czechTelescope', 'czechTelescopeSurface'),
        ('czechAnna', 'czechAnnaSurface'),
    ])

    parts = [
        'import Algorithms.GF.CYK\n',
        'namespace Algorithms.GF.Generated.PaperAmbiguityIR\n\n',
        'open Algorithms.GF.CompiledIR\n',
        'open Algorithms.GF.Tokenize\n',
        'open Algorithms.GF.CYK\n\n',
        render_grammar('englishGrammar', 'PaperAmbiguityEng', english_rules), '\n\n',
        render_grammar('czechGrammar', 'PaperAmbiguityCze', czech_rules), '\n\n',
    ]

    for label, surface_name, surface, expected in english_defs:
        parts.append(f'def {surface_name} : String := {lean_str(surface)}\n')
        parts.append(f'def {label}Tokens : Array Tok := tokenize {surface_name}\n')
        parts.append(render_array_trees(f'{label}Expected', expected))
        parts.append('\n')
        parts.append(f'def {label}Parsed : Array Parsed := parsesForStart englishGrammar {label}Tokens\n')
        parts.append(f'def {label}Recovered : Array ExportedTree := {label}Parsed.map Parsed.recovered\n\n')

    for label, surface_name, surface, expected in czech_defs:
        parts.append(f'def {surface_name} : String := {lean_str(surface)}\n')
        parts.append(f'def {label}Tokens : Array Tok := tokenize {surface_name}\n')
        parts.append(render_array_trees(f'{label}Expected', expected))
        parts.append('\n')
        parts.append(f'def {label}Parsed : Array Parsed := parsesForStart czechGrammar {label}Tokens\n')
        parts.append(f'def {label}Recovered : Array ExportedTree := {label}Parsed.map Parsed.recovered\n\n')

    parts.append('end Algorithms.GF.Generated.PaperAmbiguityIR\n')
    LEAN_IR_OUT.write_text(''.join(parts))


def main():
    ensure_dirs()
    run_gf_json_export()
    grammar_json = json.loads(JSON_GRAMMAR_OUT.read_text())
    bundle = parse_witnesses(grammar_json)
    write_witness_lean(bundle)
    write_algorithms_ir(bundle)
    print(JSON_WITNESSES_OUT)
    print(JSON_GRAMMAR_OUT)
    print(LEAN_WITNESS_OUT)
    print(LEAN_IR_OUT)


if __name__ == '__main__':
    main()
