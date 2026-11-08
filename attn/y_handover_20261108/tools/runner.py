#!/usr/bin/env python3
# gamma W1/W2 mechanical runner — chain/furnace/pa/md5 subcommands, JSON on stdout
import sys, json, os, subprocess, hashlib, re

COQ = '/Users/apple/Desktop/mac93_install_work/opam93/rocq93/bin'
GUARD = '/Users/apple/Desktop/ConstructiveWorld/cpu_guard.sh'
SB = '/Users/apple/Desktop/y-gamma-sprint-20261108'


def sh(cmd):
    return subprocess.run(cmd, capture_output=True, text=True)


def topo_of(deptext):
    raw = {}
    for line in deptext.split('\n'):
        if ':' not in line:
            continue
        tgt, srcs = line.split(':', 1)
        m = re.search(r'([A-Za-z0-9_]+)[.]vo', tgt)
        if not m:
            continue
        deps = set(re.findall(r'([A-Za-z0-9_]+)[.]vo', srcs))
        deps.discard(m.group(1))
        deps.discard('rocqworker')
        raw[m.group(1)] = deps
    names = set(raw)
    for k in raw:
        raw[k] = raw[k] & names
    order, done = [], set()
    while len(order) < len(names):
        prog = False
        for n in sorted(names - done):
            if raw[n] <= done:
                order.append(n)
                done.add(n)
                prog = True
        if not prog:
            return order, sorted(names - done)
    return order, []


def chain(segdir, root, stems, tag):
    logdir = SB + '/logs'
    os.makedirs(logdir, exist_ok=True)
    prev = os.getcwd()
    os.chdir(segdir)
    try:
        p = sh([COQ + '/coqdep', '-Q', '.', ''] + [s + '.v' for s in stems])
        order, cyc = topo_of(p.stdout)
        res, first_red = [], ''
        for m in order:
            logf = logdir + '/' + tag + '_' + m + '.log'
            r = sh(['bash', GUARD, '-MaxWaitSec', '120', '--', COQ + '/coqc',
                    '-native-compiler', 'no', '-q', '-Q', '.', '', '-Q', root, '', m + '.v'])
            with open(logf, 'w') as f:
                f.write(r.stdout + r.stderr)
            res.append({'module': m, 'rc': r.returncode})
            if r.returncode != 0:
                first_red = m
                break
        ok = (first_red == '') and len(order) == len(set(stems)) and not cyc
        print(json.dumps({'tag': tag, 'order': order, 'cycle': cyc, 'results': res,
                          'allRc0': ok, 'firstRed': first_red}))
    finally:
        os.chdir(prev)


def furnace(segdir, root, modules, tag):
    logdir = SB + '/logs'
    os.makedirs(logdir, exist_ok=True)
    logf = logdir + '/' + tag + '.log'
    prev = os.getcwd()
    os.chdir(segdir)
    try:
        r = sh(['bash', GUARD, '-MaxWaitSec', '1800', '--', COQ + '/coqchk', '-o',
                '-bytecode-compiler', 'yes', '-Q', '.', '', '-Q', root, ''] + list(modules))
        with open(logf, 'w') as f:
            f.write(r.stdout + r.stderr)
    finally:
        os.chdir(prev)
    with open(logf, encoding='utf-8', errors='replace') as f:
        t = f.read()
    errs = [ln.strip() for ln in t.split('\n') if ('Error' in ln or 'Anomaly' in ln)][:8]
    verdicts = [ln.strip() for ln in t.split('\n')
                if ('Modules were successfully checked' in ln or 'Axioms: <none>' in ln)]
    print(json.dumps({'tag': tag, 'exitCode': r.returncode, 'log': logf,
                      'checked': t.count('Modules were successfully checked'),
                      'axiomsNone': t.count('Axioms: <none>'),
                      'libs': t.count('Checking library'),
                      'errors': errs, 'verdictLines': verdicts[:4]}))


def pa(segdir, root, modules, tag):
    logdir = SB + '/logs'
    os.makedirs(logdir, exist_ok=True)
    prev = os.getcwd()
    os.chdir(segdir)
    rows = []
    try:
        drvdir = segdir + '/_pa'
        os.makedirs(drvdir, exist_ok=True)
        for m in modules:
            with open(m + '.v', encoding='utf-8') as f:
                text = f.read()
            names = [x.group(1) for x in re.finditer(
                r'^[ \t]*(?:Theorem|Corollary|Lemma|Proposition|Fact|Remark)[ \t]+([A-Za-z0-9_]+)',
                text, re.M)]
            drv = drvdir + '/_pa_' + m + '.v'
            with open(drv, 'w', encoding='utf-8') as f:
                f.write('Require Import ' + m + '.\n')
                for nm in names:
                    f.write('Print Assumptions ' + nm + '.\n')
            logf = logdir + '/' + tag + '_pa_' + m + '.log'
            r = sh(['bash', GUARD, '-MaxWaitSec', '300', '--', COQ + '/coqc', '-q',
                    '-Q', '.', '', '-Q', root, '', drv])
            with open(logf, 'w') as f:
                f.write(r.stdout + r.stderr)
            t = r.stdout + r.stderr
            closed = t.count('Closed under the global context')
            axblocks = len(re.findall(r'Axioms:', t))
            rows.append({'module': m, 'expected': len(names), 'closed': closed,
                         'axiomBlocks': axblocks, 'rc': r.returncode,
                         'ok': r.returncode == 0 and closed == len(names) and axblocks == 0,
                         'log': logf})
    finally:
        os.chdir(prev)
    print(json.dumps(rows))


def md5rows(wdir, ledger):
    rows = []
    for m in sorted(ledger):
        p = os.path.join(wdir, m + '.v')
        if os.path.exists(p):
            with open(p, 'rb') as f:
                cur = hashlib.md5(f.read()).hexdigest()
        else:
            cur = 'MISSING'
        rows.append({'module': m, 'ledger': ledger[m], 'current': cur, 'match': cur == ledger[m]})
    print(json.dumps(rows))


def plan(segdir, stems):
    prev = os.getcwd()
    os.chdir(segdir)
    try:
        p = sh([COQ + '/coqdep', '-Q', '.', ''] + [s + '.v' for s in stems])
        order, cyc = topo_of(p.stdout)
        print(json.dumps({'order': order, 'cycle': cyc}))
    finally:
        os.chdir(prev)


C1LEDGER = {
    'GaC1_RB01_RealLeB': '22470409944f16e332af1e32c7028b71',
    'GaC1_RB02_RealLeToLeB': '8ed1b2ef191231fa3d2ec333d9b7982a',
    'GaC1_RB03_LogLeLinearB': 'd984f5fb92ec739966f8ae1fcf7e29b6',
    'G1_PYTH': '3f7d512f6ea54942f658edae68be33eb',
    'GaC1_04_QRealBridge': '3877697234c743d65f8c6ba1d3682ceb',
    'GaC1_01_LogMono': 'b869f9b15e038a09b91248f67e67c02b',
    'GaC1_14_SeriesCauchy': 'c54fe0d7da089bd60db738030fa1cac8',
    'GaC1_02_LogPowBridge': '1424bacc00a0ce89f78252c340d37f48',
    'GaC1_03_LogTelescope': '4f1003113a47fda2b0d33835c55627f4',
    'GaC1_15_PowSeriesConv': 'b0e11ada230abbe519e1a4ab21e6a67e',
    'GaC1_05_RealPowRoot': 'afd6f88db0ff40a54dc108867949e4df',
    'GaC1_16_CExpNorm': 'dd9e9ec564a8a2df7ad22620c0f535d7',
    'GaC1_06_RealPowOrder': '4a7cfe2a7c86a772b400aed5f326bddd',
    'GaC1_17_TwoPiPeriod': '75c78183ed1b2161dc86d3ad8d51bb45',
    'GaC1_Iface_Real': '19e8e3f9ea0310e52eabebc305d3db67',
    'GaC1_Iface_Cx': '77a93b81992253b68719dd3a42c44c8a',
    'CxRealPairCore': 'dfcead7dd41b418439c1fc2d65da5284',
    'CxRealPairExpLog': '728c7a34d25ee64020ec52471c92eb0b',
}

C3LEDGER = {
    'GaC3_P04_CauchyRect': '64183d270854756d112e0dfdac167671',
    'GaC3_P04_CauchyRect_cert': '8bf0823b1e5e6b0ca92fb63272703e1e',
    'GaC3_V01_VdCSecond_a': '6e5db9781b06cfebd867ab9848c9cad2',
    'GaC3_V01_VdCSecond_b': '02bd957edc112aba75e26b63246434c6',
}

cmd = sys.argv[1]
if cmd == 'plan':
    plan(sys.argv[2], sys.argv[3].split(','))
elif cmd == 'chain':
    chain(sys.argv[2], sys.argv[3], sys.argv[4].split(','), sys.argv[5])
elif cmd == 'furnace':
    furnace(sys.argv[2], sys.argv[3], sys.argv[4].split(','), sys.argv[5])
elif cmd == 'pa':
    pa(sys.argv[2], sys.argv[3], sys.argv[4].split(','), sys.argv[5])
elif cmd == 'md5c1':
    md5rows(sys.argv[2], C1LEDGER)
elif cmd == 'md5c3':
    md5rows(sys.argv[2], C3LEDGER)
else:
    print(json.dumps({'error': 'unknown cmd ' + cmd}))
    sys.exit(2)
