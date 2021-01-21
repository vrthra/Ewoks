import Abstract as A
import Infra as I
import random
import os
import json

MAX_LIMIT = 10000

def fuzz_grammar(mgrammar):
    start = mgrammar['[start]']
    grammar = mgrammar['[grammar]']
    gf = A.LimitFuzzer(grammar)
    results = []
    for i in range(MAX_LIMIT):
        e = gf.fuzz(key=start)
        results.append(e)
    gf.reset_cost()
    return list(set(results))

def fuzz_it(fname):
    with open(fname) as f:
        w = f.read()
        bug_grammar = json.loads(w)

    fuzz_vals = fuzz_grammar(bug_grammar)
    FUZZ_LIMIT = 100
    if len(fuzz_vals) > FUZZ_LIMIT:
        fuzz_vals = random.sample(fuzz_vals, FUZZ_LIMIT)
    print(len(fuzz_vals))
    results = []
    for f in fuzz_vals:
        r = I._predicate(f)
        print(r, repr(f))
        results.append(r)
    return results

def main(gf_fbjson, bug_fn, pred, results_dir='fuzzing'):
    I.DOCKER = bug_fn.split('.')[-1]
    meta, tree, name = I.load_grammar(gf_fbjson, bug_fn, pred)
    global MY_PREDICATE
    os.system('mkdir -p %s' % results_dir)
    I.LOG_NAME = "./%s/%s.log.json" % (results_dir, name)
    A.NAME = name
    os.system('rm -f %s' % I.LOG_NAME)

    A.KEY = 'test'
    assert I._predicate(A.tree_to_string(tree)) == A.PRes.success
    assert I._predicate('') == A.PRes.failed

    A.KEY = 'fuzz'
    with open('./results/%s.json' % os.path.basename(bug_fn)) as f:
        j = json.load(fp=f)
        min_s = j['min_s']
        abs_s = j['abs_s']
        abs_t = j['abs_t']

    results = fuzz_it('./results/%s_atleast_one_fault_g.json' % os.path.basename(bug_fn))
    # Atleast
    print('Fuzz Atleast Total:', len(results))
    print('Fuzz Atleast Valid:', len([r for r in  results if r != A.PRes.invalid]))
    print('Fuzz Atleast Success:', len([r for r in  results if r == A.PRes.success]))

    results = fuzz_it('./results/%s_neg_fault_g.json' % os.path.basename(bug_fn))
    print('Fuzz NoFault Total:', len(results))
    print('Fuzz NoFault Valid:', len([r for r in  results if r != A.PRes.invalid]))
    print('Fuzz NoFault Success:', len([r for r in  results if r == A.PRes.success]))

