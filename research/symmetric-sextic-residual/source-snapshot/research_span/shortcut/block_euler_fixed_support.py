#!/usr/bin/env python3
"""Complete equivariant linear test for powers of a fixed block-Euler support.

This preserves G=7F and A=e3(X)e3(Y).  The two equations are
N(G)=A D and D div(N)-N(D)=0 modulo G.  S3 x S3 equivariance and the
required Y parity are complete for the invariant Y-even denominator D.
No conclusion in characteristic zero is inferred merely from modular failure.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import json
import resource
import time
from flint import nmod_mpoly_ctx, nmod_mat

HERE = Path(__file__).resolve().parent
WEIGHTS = (3, 1, 2, 1, 2, 3)
NAMES = ('r', 'p', 'q', 'P', 'Q', 'R')


def weighted_monomials(degree, weights=WEIGHTS):
    if len(weights) == 1:
        if degree % weights[0] == 0:
            yield (degree // weights[0],)
    else:
        for i in range(degree // weights[0] + 1):
            for rest in weighted_monomials(degree-i*weights[0], weights[1:]):
                yield (i,) + rest


def y_parity(e):
    return (e[3]+e[5]) % 2


def polynomial_data(prime):
    ctx = nmod_mpoly_ctx.get(NAMES, prime, 'lex')
    r,p,q,P,Q,R = ctx.gens()
    zero = ctx.constant(0)
    one = ctx.constant(1)
    def newton6(p,q,r):
        return p**6-6*p**4*q+9*p**2*q**2-2*q**3+6*p**3*r-12*p*q*r+3*r**2
    G = 7*(newton6(p,q,r)+newton6(P,Q,R))+5*q**2*Q+10*q*Q**2
    A = r*R
    fields = [
        (0,0,(q,3*one,2*p,zero,zero,zero),zero),
        (0,1,(3*r,p,2*q,zero,zero,zero),3*one),
        (0,2,(p*r,p**2-2*q,p*q-3*r,zero,zero,zero),2*p),
        (1,0,(zero,zero,zero,3*one,2*P,Q),zero),
        (1,1,(zero,zero,zero,P,2*Q,3*R),3*one),
        (1,2,(zero,zero,zero,P**2-2*Q,P*Q-3*R,P*R),2*P),
    ]
    return ctx,G,A,fields


def act(field,poly):
    return sum((field[i]*poly.derivative(i) for i in range(6)), poly.context().constant(0))


def encode(poly):
    return [[list(map(int,e)),int(c)] for e,c in sorted(poly.to_dict().items())]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--prime',type=int,default=37)
    ap.add_argument('--power',type=int,default=2)
    ap.add_argument('--memory-mib',type=int,default=1536)
    ap.add_argument('--slope',type=int,default=0,
                    help='support is E_X(G)+slope E_Y(G); slope zero is the X support')
    args = ap.parse_args()
    if args.power not in (1,2,3,4):
        raise ValueError('This bounded test permits powers 1 through 4 only.')
    if args.slope == 1:
        raise ValueError('The slope-one support is 6G and is illegal.')
    started = time.monotonic()
    ctx,G,A,fields = polynomial_data(args.prime)
    zero = ctx.constant(0)
    ex = fields[1][2]
    ey = fields[4][2]
    support = act(ex,G) + args.slope*act(ey,G)
    D = support**args.power
    degree = 6*args.power
    rows1 = [e for e in weighted_monomials(degree+6) if y_parity(e)==1]
    rows2 = [e for e in weighted_monomials(2*degree) if y_parity(e)==1 and e[0]<2]
    index1 = {e:i for i,e in enumerate(rows1)}
    index2 = {e:len(rows1)+i for i,e in enumerate(rows2)}
    basis = [(block,k,e,v,div) for block,k,v,div in fields
             for e in weighted_monomials(degree+1-k)
             if y_parity(e)==(1 if block==0 else k%2)]
    name = 'block_euler_s'+str(args.slope).replace('-','m')+'_power'+str(args.power)+'_p'+str(args.prime)
    estimate = (len(rows1)+len(rows2))*(len(basis)+1)*8
    if estimate > args.memory_mib*1024**2*0.8:
        skipped = {'status':'SKIPPED_MEMORY_BOUND','prime':args.prime,
                   'support_power':args.power,'support_slope':args.slope,
                   'numerator_columns':len(basis),'first_rows':len(rows1),
                   'second_rows':len(rows2),'raw_matrix_bytes':estimate,
                   'memory_cap_mib':args.memory_mib,'full_certificate_proved':False}
        (HERE/(name+'.json')).write_text(json.dumps(skipped,indent=2)+'\n')
        print(json.dumps(skipped),flush=True)
        return
    resource.setrlimit(resource.RLIMIT_AS,(args.memory_mib*1024**2,args.memory_mib*1024**2))
    M = nmod_mat(len(rows1)+len(rows2), len(basis)+1, args.prime)
    first_actions = [act(v,G) for _,_,v,_ in fields]
    d_actions = [act(v,D) for _,_,v,_ in fields]
    for j,(block,k,e,v,div) in enumerate(basis):
        m = ctx.from_dict({e:1})
        slot = block*3+k
        first = m*first_actions[slot]
        divN = act(v,m) + m*div
        second = divmod(D*divN - m*d_actions[slot], G)[1]
        for f,c in first.to_dict().items():
            M[index1[f],j] = int(c)
        for f,c in second.to_dict().items():
            M[index2[f],j] = int(c)
        if j and j%400 == 0:
            print(json.dumps({'stage':'columns','done':j,'total':len(basis),
                              'seconds':time.monotonic()-started}),flush=True)
    for e,c in (A*D).to_dict().items():
        M[index1[e],len(basis)] = int(c)
    built = time.monotonic()
    print(json.dumps({'stage':'matrix','rows':M.nrows(),'columns':M.ncols(),
                      'seconds':built-started}),flush=True)
    rr,rank = M.rref(inplace=True)
    pivots = [next(j for j in range(rr.ncols()) if rr[i,j]) for i in range(rank)]
    consistent = len(basis) not in pivots
    solution = None
    if consistent:
        coeffs = [0]*len(basis)
        for i,j in enumerate(pivots):
            coeffs[j] = int(rr[i,len(basis)])
        vector = [zero for _ in range(6)]
        divergence = zero
        for coefficient,(_,_,e,v,div) in zip(coeffs,basis):
            if not coefficient:
                continue
            m = coefficient*ctx.from_dict({e:1})
            vector = [a+m*b for a,b in zip(vector,v)]
            divergence += act(v,m)+m*div
        assert act(vector,G) == A*D
        assert not divmod(D*divergence-act(vector,D),G)[1]
        solution = {'basis_coefficients':[[i,c] for i,c in enumerate(coeffs) if c],
                    'field':[encode(p) for p in vector], 'divergence':encode(divergence)}
    record = {
        'status':'CONSISTENT_MOD_PRIME' if consistent else 'INCONSISTENT_MOD_PRIME',
        'prime':args.prime,'support_slope':args.slope,'support_power':args.power,
        'denominator_degree':degree,'variables':NAMES,'weights':WEIGHTS,
        'G':encode(G),'A':encode(A),'support':encode(support),'D':encode(D),
        'numerator_columns':len(basis),'first_rows':len(rows1),'second_rows':len(rows2),
        'coefficient_rank':rank if consistent else rank-1,'augmented_rank':rank,
        'basis':[[b,k,list(e)] for b,k,e,_,_ in basis],
        'solution':solution,'matrix_build_seconds':built-started,
        'elimination_seconds':time.monotonic()-built,'seconds':time.monotonic()-started,
        'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'memory_cap_mib':args.memory_mib,'raw_matrix_bytes':estimate,
        'script_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope':'Complete normalized polynomial numerator module for this fixed invariant Y-even D. Modular result only; failure is not by itself a characteristic-zero nonexistence theorem.',
        'full_certificate_proved':False,
    }
    (HERE/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({k:v for k,v in record.items() if k not in
                     ('G','A','support','D','basis','solution')}),flush=True)


if __name__ == '__main__':
    main()
