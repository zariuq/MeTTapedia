#!/usr/bin/env python3
import json
import subprocess
from pathlib import Path

ROOT = Path('/home/zar/claude/lean-projects/algorithms/gf_fragments')
GENERATED = ROOT / 'generated'
METTAPEDIA = Path('/home/zar/claude/lean-projects/mettapedia')
LEAN_SCOPE_SCRIPT = METTAPEDIA / 'scripts' / 'export_gf_project_core_names.lean'
OUT = GENERATED / 'project_core_manifest.json'

GF_RGL = Path('/home/zar/claude/gf-rgl')


def run_scope_export() -> tuple[list[str], list[str]]:
    cmd = [
        'bash',
        '-lc',
        (
            f'cd {METTAPEDIA} && '
            'ulimit -v 6291456 && '
            f'lake env lean --run {LEAN_SCOPE_SCRIPT}'
        ),
    ]
    out = subprocess.check_output(cmd, text=True)
    core: list[str] = []
    core_plus_symbol: list[str] = []
    for line in out.splitlines():
        if line.startswith('gf_scope.project_core.name='):
            core.append(line.split('=', 1)[1])
        elif line.startswith('gf_scope.project_core_plus_symbol.name='):
            core_plus_symbol.append(line.split('=', 1)[1])
    if not core or not core_plus_symbol:
        raise RuntimeError('failed to recover project-core name sets from Lean exporter')
    return core, core_plus_symbol


def build_manifest(core: list[str], core_plus_symbol: list[str]) -> dict:
    core_gf_native = [name for name in core if name != 'the_Det']
    return {
        'scope': {
            'name': 'RGL Simple Semantic Core',
            'projectCoreCount': len(core),
            'projectCoreGFNativeCount': len(core_gf_native),
            'projectCorePlusSymbolCount': len(core_plus_symbol),
            'projectCoreFunctions': core,
            'projectCoreGFNativeFunctions': core_gf_native,
            'projectCorePlusSymbolFunctions': core_plus_symbol,
        },
        'gfSourceOfTruth': {
            'root': str(GF_RGL),
            'englishGrammar': str(GF_RGL / 'src' / 'english' / 'GrammarEng.gf'),
            'czechGrammar': str(GF_RGL / 'src' / 'czech' / 'GrammarCze.gf'),
        },
        'concreteFamilyModules': {
            'english': [
                'AdjectiveEng.gf', 'AdverbEng.gf', 'ConjunctionEng.gf', 'GrammarEng.gf',
                'IdiomEng.gf', 'NounEng.gf', 'NumeralEng.gf', 'PhraseEng.gf',
                'QuestionEng.gf', 'RelativeEng.gf', 'SentenceEng.gf', 'StructuralEng.gf',
                'SymbolEng.gf', 'TenseEng.gf', 'TextEng.gf', 'VerbEng.gf',
            ],
            'czech': [
                'AdjectiveCze.gf', 'AdverbCze.gf', 'ConjunctionCze.gf', 'GrammarCze.gf',
                'IdiomCze.gf', 'NounCze.gf', 'NumeralCze.gf', 'PhraseCze.gf',
                'QuestionCze.gf', 'RelativeCze.gf', 'SentenceCze.gf', 'StructuralCze.gf',
                'SymbolCze.gf', 'TenseCze.gf', 'TextCze.gf', 'VerbCze.gf',
            ],
        },
    }


def main() -> None:
    GENERATED.mkdir(parents=True, exist_ok=True)
    core, core_plus_symbol = run_scope_export()
    manifest = build_manifest(core, core_plus_symbol)
    OUT.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
    print(f'wrote {OUT}')
    print(f'projectCore={len(core)} projectCorePlusSymbol={len(core_plus_symbol)}')


if __name__ == '__main__':
    main()
