#! /usr/bin/env python3
# Chars in Mini String
# Visible Nonterminals
# Invisible Nonterminals
# Context Sensitive
# Remaining Chars
# Executions
import json
import sys
import json
import Abstract as A

from os import listdir
from os.path import isfile, join

def table1(args):
    rows = []
    mypath = 'results'
    if not args:
        args = [join(mypath, f) for f in listdir(mypath) if isfile(join(mypath, f))]
    args = sorted(args)
    for a in args:
        try:
            if '.log.' in a: continue
            if '/fuzz_' in a: continue
            if '/reduce_' in a: continue
            if '/recognize_' in a: continue
            with open(a) as f:
                j = json.load(fp=f)
            r = table1_row(j, a)
            rows.append(r)
        except FileNotFoundError as f:
            #print('Not found: ', a)
            continue
    return rows

def table1(args):
    # Fuzz Total: 2
    # Fuzz Valid: 2
    # Fuzz Success: 2
    rows = []
    mypath = 'results'
    if not args:
        args = [join(mypath, f) for f in listdir(mypath) if isfile(join(mypath, f))]
    args = sorted(args)
    for a in args:
        try:
            if '/fuzz_' not in a: continue
            total_f_a, valid_f_a, success_f_a = 0, 0, 0
            total_f_n, valid_f_n, success_f_n = 0, 0, 0
            with open(a) as f:
                for l in f.readlines():
                    if 'Fuzz Atleast Total:' in l:
                        total_f_a = int(l[len('Fuzz Atleast Total: '):])
                    elif 'Fuzz Atleast Valid:' in l:
                        valid_f_a = int(l[len('Fuzz Atleast Valid: '):])
                    elif 'Fuzz Atleast Success:' in l:
                        success_f_a = int(l[len('Fuzz Atleast Success: '):])
                    elif 'Fuzz NoFault Total:' in l:
                        total_f_n = int(l[len('Fuzz NoFault Total: '):])
                    elif 'Fuzz NoFault Valid:' in l:
                        valid_f_n = int(l[len('Fuzz NoFault Valid: '):])
                    elif 'Fuzz NoFault Success:' in l:
                        success_f_n = int(l[len('Fuzz NoFault Success: '):])

                    else:
                        pass
            hdr = a.replace('fuzz_','').replace('.log', '').replace('results/','')
            rows.append([hdr, total_f_a, valid_f_a, success_f_a, total_f_n, valid_f_n, success_f_n])
        except FileNotFoundError as f:
            #print('Not found: ', a)
            continue
    return rows

if __name__ == '__main__':
    import sys

#    print('{0:>15} {1:>20} {2:>10} {3:>10} {4:>20} {5:>10} {6:>10}'.format('', 'Chars in MinString','Visible','Invisible','Context Sensitive','Remaining','Executions') )
#    rows = table1(sys.argv[1:])
#    for r in rows:
#        print('{0:>15} {1:>20} {2:>10} {3:>10} {4:>20} {5:>10} {6:>10}'.format(*r))
        #print(','.join([str(s) for s in r]))

if __name__ == '__main__':
    print('{0:<20} | {1:>10}% of {2:>10} | {3:>10}% of {4:>10}'.format('Bug','xx.x','F','xx.x','not F') )
    rows = table1(sys.argv[1:])
    for (hdr, total_f_a, valid_f_a, success_f_a, total_f_n, valid_f_n, success_f_n) in rows:
        print('{0:<20} | {1:>10}% of {2:>10} | {3:>10}% of {4:>10}'.format(hdr,
            (100.0*success_f_a/valid_f_a), valid_f_a,
            (100.0*success_f_n/valid_f_n), valid_f_n
            ) )
