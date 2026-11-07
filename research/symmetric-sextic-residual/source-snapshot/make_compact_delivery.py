#!/usr/bin/env python3
"""Keep sources readable while retaining the large archive as verified parts."""
from pathlib import Path
import hashlib,json,os,shutil,zipfile

ROOT=Path(__file__).resolve().parents[1]
PARTS=ROOT/'checkpoint_archive_parts'


def digest(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda:f.read(8*1024**2),b''):h.update(b)
    return h.hexdigest()


def main():
    name='symmetric_sextic_contact_repair_20261106'
    original=ROOT/(name+'.zip')
    manifest=json.loads((PARTS/'parts_manifest.json').read_text())
    results=json.loads((PARTS/'upload_result.json').read_text())['results']
    assert len(results)==len(manifest['parts'])==6
    for part,result in zip(manifest['parts'],results):
        assert result['status']=='succeeded' and result['local_metadata_applied']
        assert part['file_name']==result['file_name']
        part.pop('local_path',None)
        part['library_file_id']=result['library_file_id']
        part['download_url']='https://chatgpt.com/library?file_id='+result['library_file_id']+'&account_id=personal'
    directory=ROOT/'delivery_compact';directory.mkdir(exist_ok=True)
    package=directory/name
    assert not package.exists(),'Use a fresh compact package directory'
    omitted=[]
    with zipfile.ZipFile(original) as archive:
        for item in archive.infolist():
            if item.filename.endswith('.hcf') and item.file_size>=64*1024**2:
                omitted.append({'file':item.filename,'bytes':item.file_size});continue
            archive.extract(item,directory)
    assert len(omitted)==2
    manifest['large_checkpoint_files_omitted_from_compact_package']=omitted
    (package/'parts_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    shutil.copy2(PARTS/'join_checkpoint_archive.py',package/'join_checkpoint_archive.py')
    shutil.copy2(Path(__file__),package/'make_compact_delivery.py')
    lines=[
        'COMPLETE CHECKPOINT ARCHIVE DOWNLOADS',
        '====================================',
        'The mathematical proof remains unfinished. These files preserve research and solver state.',
        '',
        'The compact ZIP includes all source code, reports, tests, and native-state sidecars.',
        'The two large polynomial checkpoints are in the complete archive, split into six parts.',
        'All six parts were saved successfully. Their concatenation exactly reproduces the',
        'previously CRC-checked complete ZIP; each part has its own SHA256 below.',
        '',
        'Download every part into one directory. Then run the included helper:',
        '  python3 join_checkpoint_archive.py --parts-dir /path/to/downloads',
        '',
        'The helper checks every part and the assembled ZIP before accepting the result.',
        'It uses bounded memory and refuses to overwrite an existing output.',
        '',
        'Complete ZIP bytes: '+str(manifest['complete_archive_bytes']),
        'Complete ZIP SHA256: '+manifest['complete_archive_sha256'],
        ''
    ]
    for i,part in enumerate(manifest['parts'],1):
        lines += [f'{i}. '+part['file_name'],
                  '   Bytes: '+str(part['bytes']),
                  '   SHA256: '+part['sha256'],
                  '   '+part['download_url'],'']
    (package/'CHECKPOINT_DOWNLOADS.txt').write_text('\n'.join(lines)+'\n')
    note=(
        'COMPACT DELIVERY WITH COMPLETE ARCHIVE PARTS\n'
        '===========================================\n'
        'This compact ZIP omits only the two large .hcf polynomial checkpoint files.\n'
        'All source code, reports, validation evidence and native-state sidecars remain here.\n'
        'The complete 1.48 GB ZIP is preserved in six verified download parts.\n'
        'Open CHECKPOINT_DOWNLOADS.txt for saved download links and restoration instructions.\n'
        'Use join_checkpoint_archive.py with parts_manifest.json to verify and assemble it.\n'
        'Statements below that checkpoints are included refer to that complete archive.\n'
        'The target theorem remains unproved and no full source trace has been evaluated.\n\n')
    for relative in ['README.txt','research_blocker/README.txt']:
        p=package/relative;p.write_text(note+p.read_text())
    files={str(p.relative_to(package)):digest(p) for p in sorted(package.rglob('*'))
           if p.is_file() and p.name!='PACKAGE_SHA256.json'}
    (package/'PACKAGE_SHA256.json').write_text(json.dumps(files,indent=2)+'\n')
    output=directory/(name+'.zip')
    with zipfile.ZipFile(output,'x',zipfile.ZIP_DEFLATED,compresslevel=3) as z:
        for p in sorted(package.rglob('*')):
            if p.is_file():z.write(p,str(p.relative_to(directory)))
    with zipfile.ZipFile(output) as z:assert z.testzip() is None
    full_alias=ROOT/(name+'_full.zip')
    if not full_alias.exists():os.link(original,full_alias)
    receipt={'status':'PASS','compact_zip':str(output),'bytes':output.stat().st_size,
             'sha256':digest(output),'compact_CRC_check_passed':True,
             'large_data_saved_in_verified_parts':True,'part_count':6,
             'full_archive_sha256':manifest['complete_archive_sha256'],
             'full_certificate_proved':False}
    (PARTS/'compact_delivery_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()
