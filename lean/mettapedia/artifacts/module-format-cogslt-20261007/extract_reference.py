"""Build a standalone reference from pinned, verbatim upstream definitions.

Only the unused CanonicalModuleValue::fingerprint method is omitted from
module.rs. Every admission function and its resource-accounting dependencies
are copied verbatim. The original files and hashes remain beside the harness.
This is an extracted decoder comparison, not a build of the complete runtime.
"""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent
upstream = root / 'upstream'
manifest = json.loads((upstream / 'manifest.json').read_text())
for name, evidence in manifest.items():
    assert hashlib.sha256((upstream / name).read_bytes()).hexdigest() == evidence['sha256']

extractions = {}
def block(source, marker, derive=False):
    start = source.index(marker)
    if derive:
        before = source[:start].rstrip()
        line_start = before.rfind('\n') + 1
        if before[line_start:].startswith('#[derive('):
            start = line_start
    first_line_end = source.index('\n', start)
    if source[start:first_line_end].endswith('{}'):
        end = first_line_end + 1
    else:
        end = re.search(r'^}\n', source[first_line_end:], re.M).end() + first_line_end
    result = source[start:end]
    extractions[marker] = {'sha256': hashlib.sha256(result.encode()).hexdigest(),
                           'bytes': len(result.encode())}
    return result

canonical = (upstream / 'canonical.rs').read_text()
canonical_markers = [
    'pub enum RhoValue {', 'impl Clone for RhoValue {', 'impl PartialEq for RhoValue {',
    'impl Eq for RhoValue {}', 'impl fmt::Debug for RhoValue {', 'impl Drop for RhoValue {',
    'fn detach_rho_children(', 'pub fn admit_canonical_value(', 'fn admit_canonical_value_impl(',
    'fn account_canonical_bytes(', 'pub(crate) fn account_canonical_string(',
    'pub struct ValueDecodeError {', 'impl ValueDecodeError {',
    'impl fmt::Display for ValueDecodeError {']
canonical_output = 'use std::collections::BTreeMap;\nuse std::fmt;\n'
canonical_output += '\n'.join(re.findall(r'^pub const MAX_CANONICAL_.*;$', canonical, re.M)) + '\n'
canonical_output += '\n'.join(block(canonical, marker, derive=True) for marker in canonical_markers)
(root / 'reference_canonical.rs').write_text(canonical_output)

resolve = (upstream / 'resolve.rs').read_text()
resolve_markers = ['pub enum ModuleRef {', 'impl ModuleRef {', 'impl fmt::Display for ModuleRef {',
                   'pub enum ResolveError {', 'impl fmt::Display for ResolveError {']
(root / 'reference_resolve.rs').write_text('use std::fmt;\n' +
    '\n'.join(block(resolve, marker, derive=True) for marker in resolve_markers))

parse = (upstream / 'parse.rs').read_text()
(root / 'reference_parse.rs').write_text(re.search(
    r'^pub const MAX_DDL_STRUCTURAL_DEPTH:.*;$', parse, re.M).group(0) + '\n')

module = (upstream / 'module.rs').read_text()
omitted = '    pub fn fingerprint(&self) -> [u8; 32] {\n        self.to_rho_value().fingerprint()\n    }\n'
assert module.count(omitted) == 1
(root / 'reference_module.rs').write_text(module.replace(omitted, ''))
(root / 'extraction_manifest.json').write_text(json.dumps({
    'verbatim_blocks': extractions,
    'sole_module_omission': 'CanonicalModuleValue::fingerprint (unused in these tests)',
    'upstream_module_tests_preserved': 3,
    'resource_admission': 'verbatim upstream implementation, no stub or bypass',
    'scope': 'extracted module decoder; not the full crate or language/2 interpreter'}, indent=2) + '\n')
print('Extracted pinned decoder, actual resource admission, reference parser and upstream tests.')
