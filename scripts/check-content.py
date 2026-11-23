#!/usr/bin/env python3
"""Check rendered math, chapter navigation, and local links without a browser."""
from html.parser import HTMLParser
import argparse
from pathlib import Path
from public_files import is_public
import json
import re
import subprocess
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--explanation', type=Path, help='Also check a proposed, rendered explanation before acceptance')
parser.add_argument('--index', type=Path, help='Alternate docs/index.json to validate against')
parser.add_argument('--doc', action='append', default=[], help='Override a rendered book chapter as SOURCE=HTML')
args = parser.parse_args()

def label(path):
    return str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else path.name

class Content(HTMLParser):
    def __init__(self, path):
        super().__init__(); self.path=path; self.math=[]; self.links=[]; self.ids=set(); self.current=None
    def handle_starttag(self,tag,attrs):
        a=dict(attrs)
        if 'data-math' in a: self.current=[]
        if tag=='a': self.links.append(a.get('href',''))
        if 'id' in a: self.ids.add(a['id'])
    def handle_endtag(self,tag):
        if self.current is not None and tag in ('span','div'):
            self.math.append({'file':label(self.path), 'tex':''.join(self.current)})
            self.current=None
    def handle_data(self,text):
        if self.current is not None: self.current.append(text)

index=json.loads((args.index or (ROOT/'docs/index.json')).read_text())
pages={p['id']:p for p in index['pages']}
doc_overrides={}
for spec in args.doc:
    source, sep, html_path = spec.partition('=')
    if not sep:
        raise SystemExit(f'Invalid --doc argument (expected SOURCE=HTML): {spec}')
    doc_overrides[source] = Path(html_path).resolve()

page_files = {}
overridden_targets = set()
for p in index['pages']:
    default_target = (ROOT / p['content']).resolve()
    if p['source'] in doc_overrides:
        page_files[p['id']] = doc_overrides[p['source']]
        overridden_targets.add(default_target)
    else:
        page_files[p['id']] = default_target
if index.get('overview', {}).get('source') in doc_overrides:
    overridden_targets.add((ROOT / index['overview']['content']).resolve())

files = [p.resolve() for p in (ROOT/'assets/atlas').glob('*/*.html')]
files += [p.resolve() for p in (ROOT/'docs').glob('*.html') if p.resolve() not in overridden_targets]
files += [(ROOT/'index.html').resolve()]
for html_path in doc_overrides.values():
    if html_path not in files:
        files.append(html_path)
if args.explanation:
    files.append(args.explanation.resolve())

REPOSITORY='https://github.com/hodge-computer/sextics/blob/main/'
shown={p['source']:page_files[p['id']] for p in index['pages']}
for source, html_path in doc_overrides.items():
    shown[source] = html_path
shown.update({f'data/{s.parent.name}/solution.md':s.resolve() for s in (ROOT/'assets/atlas').glob('*/solution.html')})
contents={}
for p in files:
    c=Content(p);c.feed(p.read_text());contents[p]=c
errors=[];math=[]
for p,c in contents.items():
    math.extend(c.math)
    for link in c.links:
        if link.startswith(REPOSITORY):
            # The website shows these sources on its own pages; their anchors
            # must name headings there as well as on GitHub.
            source,_,anchor=unquote(link[len(REPOSITORY):]).partition('#')
            page=shown.get(source)
            if anchor and page is not None and page in contents and anchor not in contents[page].ids:
                errors.append(f'{label(p)}: missing heading #{anchor} in {source}')
            continue
        if link.startswith(('http://','https://','mailto:')):continue
        if link.startswith('#technical-information/'):
            parts=link[1:].split('/');page=pages.get(parts[1])
            if not page: errors.append(f'{p.name}: unknown chapter {link}')
            elif len(parts)>2 and '/'.join(parts[2:]) not in contents[page_files[parts[1]]].ids:errors.append(f'{p.name}: missing chapter heading {link}')
        elif link.startswith('#') or not link:continue
        elif not is_public(link.split('#')[0].lstrip('/')) or not (ROOT/link.split('#')[0].lstrip('/')).is_file():errors.append(f'{p.name}: missing local link {link}')
for p in (ROOT/'assets/atlas').glob('*/record.json'):
    record=json.loads(p.read_text())
    for name in ('F','A','D'):
        if name in record and record[name].get('latex'):math.append({'file':str(p.relative_to(ROOT))+':'+name,'tex':record[name]['latex']})
    for tex in record.get('displayDefinitions',[]):math.append({'file':str(p.relative_to(ROOT))+':definition','tex':tex})
node=r'''
const fs=require('fs'),katex=require('./assets/vendor/katex.min.js');const formulas=JSON.parse(fs.readFileSync(0,'utf8'));let errors=[];
for(const f of formulas){try{katex.renderToString(f.tex,{throwOnError:true,strict:'error',trust:false});}catch(e){errors.push(`${f.file}: ${e.message}`);}}
if(errors.length){console.error(errors.join('\n'));process.exit(1);}console.log(`Rendered ${formulas.length} formulas with bundled KaTeX.`);
'''
result=subprocess.run(['node','-e',node],input=json.dumps(math),text=True,cwd=ROOT,capture_output=True)
if result.returncode:errors.append(result.stderr)
if errors:raise SystemExit('\n'.join(errors))
print(result.stdout.strip())
print(f'Checked local links and chapter routes in {len(files)} HTML files.')
