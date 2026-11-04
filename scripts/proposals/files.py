"""Enumerate the current proof files for local verification."""
import re


def proof_files(folder):
    return sorted(p.name for p in folder.iterdir()
                  if p.is_file() and (p.name in ('proof.json', 'solution.md', 'witness.json')
                                      or re.fullmatch(r'[A-Z][A-Za-z0-9_]*\.lean', p.name)))
