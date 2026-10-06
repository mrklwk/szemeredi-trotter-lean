#!/usr/bin/env python3
"""Lexical source precheck only. Comparator establishes semantic statement equality.

Print JSON to stdout. Write a report only when --report PATH is supplied.
"""
from pathlib import Path
import argparse,json,re

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--report", type=Path, metavar="PATH",
                    help="also write JSON to this explicit destination; default: stdout only")
args=parser.parse_args()
root=Path(__file__).resolve().parent.parent
lean=root
paths=[p for p in lean.rglob('*.lean') if '.lake' not in p.parts]
for p in paths:
 assert not p.is_symlink(),p
 text=p.read_text()
 assert text.splitlines()[0]=='module',p
 assert len(text.splitlines())<=10000,p
 if p.name!='Challenge.lean':assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text),p
challenge=(lean/'Challenge.lean').read_text();solution=(lean/'Solution.lean').read_text()
assert len(challenge.encode())<=100*1024 and len(challenge.splitlines())<=1000
assert len(re.findall(r'\bsorry\b',challenge))==4
assert all(x.startswith('Mathlib.') for x in re.findall(r'^public import (\S+)',challenge,re.M))
config=json.loads((lean/'comparator.json').read_text())
assert set(config)=={'challenge_module','solution_module','theorem_names','permitted_axioms'}
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
for n in config['theorem_names']:
 short=n.rsplit('.',1)[1]
 pattern=rf'theorem {short} (.*?) := by'
 c=re.search(pattern,challenge,re.S);s=re.search(pattern,solution,re.S)
 assert c and s and c[1]==s[1],n
seen=set()
def visit(name):
 if name in seen:return
 seen.add(name);path=lean/Path(name.replace('.','/')).with_suffix('.lean')
 if path.is_file():
  for dependency in re.findall(r'^(?:public )?import (\S+)',path.read_text(),re.M):visit(dependency)
visit('Solution');assert 'Challenge' not in seen
result={'lean_sources':len(paths),'module_headers':True,'line_limits':True,'challenge_lines':len(challenge.splitlines()),'challenge_bytes':len(challenge.encode()),'challenge_specification_holes':4,'solution_imports_challenge':False,'statement_headers_textually_identical':True,'statement_check_kind':'lexical regex comparison only',
        'semantic_statement_comparison':'not performed; run the official Comparator',
        'scope':'Lexical source structure only; no elaboration, proof, build or Comparator claim'}
report=json.dumps(result,indent=2)+'\n'
if args.report is not None:
 args.report.parent.mkdir(parents=True,exist_ok=True)
 args.report.write_text(report)
print(report,end='')
