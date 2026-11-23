"""Untrusted source-data adapter: structured HOL closure to existing HOLR.

Every source result is followed by the replay format's independent sequent
comparison. This code proposes requests and never decides HOL inference.
"""

import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import sys


def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, list) else value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stream-tools', type=Path, required=True)
    parser.add_argument('--source-tools', type=Path, required=True)
    parser.add_argument('--prefix', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--changed-root', action='store_true')
    parser.add_argument('--extra-axiom', action='store_true')
    parser.add_argument('--controls-dir', type=Path,
                        help='emit both corrupted controls from the same decoded proof graph')
    args = parser.parse_args()
    if args.controls_dir and (args.changed_root or args.extra_axiom):
        raise ValueError('combined controls cannot also select an individual mutation')
    sys.path.insert(0, str(args.stream_tools.resolve()))
    from holr import Stream
    sys.path.insert(0, str(args.source_tools.resolve()))
    from hol_light_prepare_export_v1 import group_type_definitions
    from hol_light_proof_export_v1 import inspect_closure

    roots = [json.loads(row) for row in args.prefix.with_suffix('.roots.jsonl').read_text().splitlines()]
    accounting = inspect_closure(args.prefix, [row['name'] for row in roots])
    def events():
        with args.prefix.with_suffix('.nodes.jsonl').open() as source:
            yield from group_type_definitions(json.loads(row) for row in source)

    signature = json.loads(args.prefix.with_suffix('.signature.json').read_text())
    introduced_types, introduced_constants = set(), set()
    for node in events():
        if node['rule'] == 'TYPE_DEFINITION_PAIR':
            introduced_types.add(node['arguments'][1])
            introduced_constants.update(node['arguments'][2:4])
        elif node['rule'] == 'DEFINITION':
            introduced_constants.add(node['arguments'][1])

    stream = Stream(policy=1)
    types, terms, theorems = {}, {}, {}

    def octets(name):
        return name.encode('latin1')

    def ty(value):
        tag, name, *rest = value
        if tag == 'var' and not rest:
            children = ()
            key = (tag, name)
        elif tag == 'op' and len(rest) == 1:
            children = tuple(map(ty, rest[0]))
            key = (tag, name, children)
        else:
            raise ValueError('unrecognized source type')
        if key not in types:
            if tag == 'var' and not rest:
                result = stream.tyvar(octets(name))
            else:
                result = stream.tyapp(octets(name), *children)
            types[key] = result
        return types[key]

    def tm(value):
        tag, first, second = value
        if tag in ('var', 'const'):
            first_id, second_id = first, ty(second)
        elif tag in ('app', 'abs'):
            first_id, second_id = tm(first), tm(second)
        else:
            raise ValueError('unrecognized source term')
        key = (tag, first_id, second_id)
        if key not in terms:
            if tag in ('var', 'const'):
                result = (stream.var if tag == 'var' else stream.const)(octets(first), second_id)
            else:
                result = (stream.comb if tag == 'app' else stream.abs)(first_id, second_id)
            terms[key] = result
        return terms[key]

    def expected(identifier, claim):
        stream.expect_alpha(identifier, [tm(term) for term in claim['hypotheses']], tm(claim['conclusion']))

    for name, arity in signature['types']:
        if name not in {'bool', 'fun'} | introduced_types:
            stream.new_type(octets(name), arity)
    for name, schema in signature['constants']:
        if name != '=' and name not in introduced_constants:
            stream.new_constant(octets(name), ty(schema))

    rules = Counter()
    for node in events():
        identifier, rule, arguments = node['id'], node['rule'], node['arguments']
        if identifier in theorems:
            raise ValueError('duplicate source address')
        rules[rule] += 1
        if rule in ('REFL', 'BETA', 'ASSUME', 'AXIOM'):
            method = {'REFL': stream.refl, 'BETA': stream.beta,
                      'ASSUME': stream.assume, 'AXIOM': stream.new_axiom}[rule]
            result = method(tm(arguments[0]))
        elif rule in ('TRANS', 'MK_COMB', 'EQ_MP', 'DEDUCT_ANTISYM_RULE'):
            method = {'TRANS': stream.trans, 'MK_COMB': stream.mk_comb,
                      'EQ_MP': stream.eq_mp, 'DEDUCT_ANTISYM_RULE': stream.deduct}[rule]
            result = method(theorems[arguments[0]], theorems[arguments[1]])
        elif rule == 'ABS':
            result = stream.abs_rule(tm(arguments[1]), theorems[arguments[0]])
        elif rule in ('INST', 'INST_TYPE'):
            convert = tm if rule == 'INST' else ty
            pairs = [(convert(replacement), convert(variable)) for replacement, variable in arguments[1]]
            method = stream.inst if rule == 'INST' else stream.inst_type
            result = method(pairs, theorems[arguments[0]])
        elif rule == 'DEFINITION':
            equation, name, schema = arguments
            # The source trace retains the resulting Const equation. The
            # original kernel request uses the same name/type as a variable.
            request = ['app', ['app', equation[1][1], ['var', name, schema]], equation[2]]
            result = stream.new_definition(tm(request))
        elif rule == 'TYPE_DEFINITION_PAIR':
            parent, type_name, abstract, represent = arguments
            first, second = stream.new_typedef(octets(type_name), octets(abstract),
                                               octets(represent), theorems[parent])
            theorems[identifier], theorems[node['mate']] = first, second
            expected(first, node['theorems'][0])
            expected(second, node['theorems'][1])
            continue
        else:
            raise ValueError(f'unrecognized source rule: {rule}')
        theorems[identifier] = result
        expected(result, node['theorem'])

    if len(theorems) != accounting['nodes']:
        raise ValueError('incomplete source replay')
    for root in roots:
        result = theorems[root['id']]
        stream.label(result, octets(root['name']))
        stream.emit(result)
    if args.changed_root or args.extra_axiom:
        constant_names = {name for name, _ in signature['constants']}
        probe_name = 'F' if 'F' in constant_names else 'T'
        if probe_name not in constant_names:
            raise ValueError('negative controls need a declared Boolean constant')
        probe = ['const', probe_name, ['op', 'bool', []]]
        if args.changed_root:
            stream.expect_alpha(theorems[roots[0]['id']], [], tm(probe))
        if args.extra_axiom:
            stream.new_axiom(tm(probe))
    stream.write(args.output)
    output_records = stream.records
    controls = {}
    if args.controls_dir:
        args.controls_dir.mkdir(parents=True, exist_ok=True)
        constant_names = {name for name, _ in signature['constants']}
        probe_name = 'F' if 'F' in constant_names else 'T'
        if probe_name not in constant_names:
            raise ValueError('negative controls need a declared Boolean constant')
        probe_id = tm(['const', probe_name, ['op', 'bool', []]])
        base_length, base_records = len(stream.buf), stream.records
        stream.expect_alpha(theorems[roots[0]['id']], [], probe_id)
        changed = args.controls_dir / 'changed-root.holr'
        stream.write(changed)
        controls['changed-root'] = str(changed)
        # EXPECT creates no identifiers; restore exactly the shared prefix.
        del stream.buf[base_length:]
        stream.records = base_records
        stream.new_axiom(probe_id)
        extra = args.controls_dir / 'extra-axiom.holr'
        stream.write(extra)
        controls['extra-axiom'] = str(extra)
    print(json.dumps({'source_nodes': len(theorems), 'source_roots': roots,
                      'wire_records': output_records, 'wire_bytes': args.output.stat().st_size,
                      'source_axioms': accounting['axiom_nodes'],
                      'rules': dict(rules), 'controls': controls,
                      'proofs_checked_by_adapter': False}, sort_keys=True))


if __name__ == '__main__':
    main()
