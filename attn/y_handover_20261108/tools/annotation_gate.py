#!/usr/bin/env python3
# PR annotation gate — spec-faithful to 注释规范卡-M波-20261025 §一/§三/§四/§六,
# 融合工艺白皮书 v1.3 §8.2 (comment-face confession literals), cw-ci-sop v2.4.2/v2.4.3.
# Usage: annotation_gate.py <file.v> ...   → JSON per file + RETROFIT list on stdout.
import sys, json, os, re

BANNED_JARGON = [
    r'\bwave\b', r'\bbatch\b', r'\bseat\b', r'\bcampaign\b', r'\bdispatch\b',
    r'\bhandover\b', r'\blanding\b', r'\bretrofit\b', r'\bledger\b', r'\bwash\b',
    r'\bborn\b', r'\bgate\b',
]
CONFESSION = [r'\bAxiom\b', r'\bAxioms\b', r'\bAdmitted\b', r'\badmit\b', r'\bAbort\b',
              r'\bParameter\b', r'\bConjecture\b', r'\bclassic\b', r'\bexcluded_middle\b',
              r'\bHypothesis\b']
ATTRIBUTION = [r'\buser\b', r'\bdecree\b', r'\bAI\b', r'\bcolleague\b', r'\bmaster\b', r'\bowner\b']
PRAISE = [r'\btrivial\b', r'\bobvious\b', r'\bhack\b', r'\bworkaround\b']
FIELDS = ['Mission.', 'Dependencies.', 'References.', 'Constructivity.', 'Build.']


def classify(text):
    n = len(text)
    depth = 0
    instr = False
    kinds = []
    i = 0
    while i < n:
        c = text[i]
        if instr:
            if c == '\\' and i + 1 < n:
                kinds.append('s')
                kinds.append('s')
                i += 2
                continue
            kinds.append('s')
            if c == '"':
                instr = False
            i += 1
            continue
        if c == '"':
            instr = True
            kinds.append('s')
            i += 1
            continue
        if c == '(' and i + 1 < n and text[i + 1] == '*':
            depth += 1
            kinds.append('c')
            kinds.append('c')
            i += 2
            continue
        if c == '*' and i + 1 < n and text[i + 1] == ')' and depth > 0:
            depth -= 1
            kinds.append('c')
            kinds.append('c')
            i += 2
            continue
        kinds.append('c' if depth > 0 else 'x')
        i += 1
    return kinds


def line_ranges(text, kinds):
    """per line: dominant kind + exact CJK positions by kind"""
    lines = text.split('\n')
    out = []
    pos = 0
    for ln in lines:
        seg = kinds[pos:pos + len(ln)]
        out.append(seg)
        pos += len(ln) + 1
    return lines, out


def scan(path):
    text = open(path, encoding='utf-8').read()
    kinds = classify(text)
    lines, lk = line_ranges(text, kinds)
    retrofit = []

    def face_hits(line, kindset, patterns, tag):
        hits = []
        for pat in patterns:
            for m in re.finditer(pat, line):
                hits.append((tag, pat, m.start()))
        return hits

    cjk_c = cjk_s = cjk_x = 0
    for idx, (ln, seg) in enumerate(zip(lines, lk), 1):
        for ch, k in zip(ln, seg):
            if '\u4e00' <= ch <= '\u9fff' or ch in '，。；：「」·—（）':
                if k == 'c':
                    cjk_c += 1
                elif k == 's':
                    cjk_s += 1
                else:
                    cjk_x += 1
        # confession/jargon/attribution/praise in COMMENT face only (spec scope)
        if 'c' in seg:
            for tag, pat, _ in face_hits(ln, None, BANNED_JARGON, 'jargon'):
                if any(seg[m.start()] == 'c' for m in re.finditer(pat, ln) if m.start() < len(seg)):
                    pass
            for pat in BANNED_JARGON:
                for m in re.finditer(pat, ln):
                    if m.start() < len(seg) and seg[m.start()] == 'c':
                        retrofit.append({'line': idx, 'kind': 'jargon', 'face': 'comment', 'text': ln.strip()[:110], 'what': pat})
                        break
            for pat in CONFESSION:
                for m in re.finditer(pat, ln):
                    if m.start() < len(seg) and seg[m.start()] == 'c':
                        retrofit.append({'line': idx, 'kind': 'confession', 'face': 'comment', 'text': ln.strip()[:110], 'what': pat})
                        break
            for pat in ATTRIBUTION:
                for m in re.finditer(pat, ln):
                    if m.start() < len(seg) and seg[m.start()] == 'c':
                        retrofit.append({'line': idx, 'kind': 'attribution', 'face': 'comment', 'text': ln.strip()[:110], 'what': pat})
                        break
            for pat in PRAISE:
                for m in re.finditer(pat, ln):
                    if m.start() < len(seg) and seg[m.start()] == 'c':
                        retrofit.append({'line': idx, 'kind': 'praise', 'face': 'comment', 'text': ln.strip()[:110], 'what': pat})
                        break
        # date stamps anywhere
        if re.search(r'2026[01][0-9][0-9][0-9]|2026-1[01]-[0-9][0-9]', ln):
            retrofit.append({'line': idx, 'kind': 'datestamp', 'face': 'any', 'text': ln.strip()[:110], 'what': 'date'})
        # Chinese punctuation anywhere
        if re.search(r'[，。；：「」]', ln):
            retrofit.append({'line': idx, 'kind': 'cjk_punct', 'face': 'any', 'text': ln.strip()[:110], 'what': 'punct'})
        # .(* trap: period directly followed by comment open
        if re.search(r'\.\(\*', ln):
            retrofit.append({'line': idx, 'kind': 'dot_paren', 'face': 'any', 'text': ln.strip()[:110], 'what': '.(*'})

    head = '\n'.join(lines[:45])
    fields = [f for f in FIELDS if f in head]
    banner_ok = bool(re.search(r'\(\*\s*[^*]+\s*—\s*.+\.\s*\*\)', head)) or bool(re.search(r'^\(\*.*\*\)', lines[0] if lines else ''))
    out = {
        'file': os.path.basename(path),
        'cjk_comment': cjk_c, 'cjk_string': cjk_s, 'cjk_code': cjk_x,
        'fields': len(fields), 'fields_missing': [f for f in FIELDS if f not in fields],
        'retrofit': retrofit,
    }
    return out


if __name__ == '__main__':
    results = [scan(p) for p in sys.argv[1:]]
    clean = [r for r in results if not r['retrofit'] and r['cjk_comment'] == 0 and r['cjk_string'] == 0 and r['cjk_code'] == 0 and r['fields'] == 5]
    print(json.dumps({
        'total': len(results),
        'clean': len(clean),
        'retrofit_files': sum(1 for r in results if r['retrofit'] or r['fields'] < 5 or r['cjk_comment'] or r['cjk_string'] or r['cjk_code']),
        'results': results,
    }, ensure_ascii=False, indent=1))
