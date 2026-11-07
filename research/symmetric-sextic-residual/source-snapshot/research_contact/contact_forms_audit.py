#!/usr/bin/env python3
"""Independent symbolic and exact-arithmetic audit of contact source circuits."""
from pathlib import Path
from fractions import Fraction as F
import hashlib, json, random, sys
import contact_forms_circuit as B
import contact_forms_global_residue as G
sys.path.insert(0,str(B.OLD/'python_deps'))
import sympy as sp

HERE=Path(__file__).resolve().parent

def literal_poly(encoded,values,variables):
    return sum(sp.Rational(values[t['coefficient_node']].numerator,values[t['coefficient_node']].denominator)*
               sp.prod(x**e for x,e in zip(variables,t['exponent'])) for t in encoded)

def audit():
    qa,ha,qr,hr,qs,hs,qK,hK=sp.symbols('qa ha qr hr qs hs qK hK')
    un=qa*hr-ha*qr;vn=qa*hs-ha*qs;zn=qr*hs-qs*hr;J=qK*ha-qa*hK
    assert sp.expand(un*qs-vn*qr+zn*qa)==0
    assert sp.expand(un*hs-vn*hr+zn*ha)==0
    assert sp.expand(un*(hK*qs-qK*hs)-vn*(hK*qr-qK*hr)-J*zn)==0
    a,b,c,d,e,da,db,dc,dd,de,w=sp.symbols('a b c d e da db dc dd de w')
    cubic=w**3+a*w*w+b*w+c;h=w*w+d*w+e;g=sp.diff(cubic,w)
    numerator=sp.expand(g*g*(dd*w+de)-g*h*(2*da*w+db)-
        (g*sp.diff(h,w)-h*sp.diff(g,w))*(da*w*w+db*w+dc))
    reduced=sp.rem(numerator,cubic,w)
    n1,n2=sp.expand(reduced).coeff(w,1),sp.expand(reduced).coeff(w,2)
    alpha,beta,v,F0,L0=sp.symbols('alpha beta v F0 L0')
    point={d:beta+a,e:beta**2+a*beta+b,c:F0-beta**3-a*beta**2-b*beta,
           dc:-da*beta**2-db*beta-(3*beta**2+2*a*beta+b)*v-alpha*L0,
           dd:da+v,de:beta*da+db+(2*beta+a)*v}
    remainder1=-6*F0*(beta*da+db+(3*beta+2*a)*v)-2*alpha*(3*beta**2+3*a*beta+2*b)*L0
    remainder2=-3*F0*(da+3*v)-alpha*(a+3*beta)*L0
    assert sp.expand(n1.subs(point,simultaneous=True)-remainder1)==0
    assert sp.expand(n2.subs(point,simultaneous=True)-remainder2)==0

    frame=B.build();base_path=HERE/'contact_target_circuit.json'
    if not base_path.exists():base_path=B.OLD/'symmetric_norm_contact_circuit.json'
    base=json.loads(base_path.read_text())
    av,bv,cv,dv,u,rv,sv,al,x=sp.symbols('av bv cv dv u rv sv al x')
    ambient=(av,bv,cv,dv);rng=random.Random(271828);checks=[]
    for trial in range(3):
        env={name:F(rng.randrange(-2,3)) for name in base['parameter_order']}
        env.update(lam=F(trial+1),r=F(2),s=F(trial+1),alpha=F(3))
        env['mu0'],env['mu1']=F(1),F(1,4)
        values=B.N.evaluate_circuit(frame,env)
        ambient_polys={name:literal_poly(base['polynomials'][name],values,ambient)
                       for name in ('Q1','Q2','A','B')}
        qfun=ambient_polys['Q2'].subs(dict(zip(ambient,(1,rv,al,sv*al))),simultaneous=True)
        hfun=(ambient_polys['A']+ambient_polys['B']).subs(dict(zip(ambient,(1,rv,al,sv*al))),simultaneous=True)
        bfun=-ambient_polys['Q1'].subs(dict(zip(ambient,(1,rv,al,sv*al))),simultaneous=True)
        values_at={rv:sp.Rational(env['r']),sv:sp.Rational(env['s']),al:sp.Rational(env['alpha'])}
        qrr,qss,qaa=[sp.diff(qfun,t).subs(values_at) for t in (rv,sv,al)]
        hrr,hss,haa=[sp.diff(hfun,t).subs(values_at) for t in (rv,sv,al)]
        brr,bss,baa=[sp.diff(bfun,t).subs(values_at) for t in (rv,sv,al)]
        uu=qaa*hrr-haa*qrr;vv=qaa*hss-haa*qss;zz=qrr*hss-qss*hrr
        yy=baa*zz+uu*bss-vv*brr;betaval=bfun.subs(values_at);alphaval=values_at[al]
        for name,expected in [('u',uu),('v',vv),('z',zz),('y',yy)]:
            assert sp.Rational(values[frame['current_numerator_nodes'][name]])==expected
        actualG=literal_poly(base['polynomials']['G'],values,ambient+(u,))
        targetbar=sp.Rational(2,1)*bv*dv*(av**2+ambient_polys['Q1'])*(cv**2+env['lam']**2*ambient_polys['Q1'])/sp.Rational(values[base['ell_node']])**2
        assert sp.expand(literal_poly(frame['source_after_u_elimination'],values,ambient)-targetbar)==0
        chart=sp.Poly(sp.expand(actualG.subs({av:1,bv:rv,cv:al,dv:sv*al,u:w},simultaneous=True)),w,al)
        coeff=[]
        for power in (2,1,0):
            raw=sp.expand(chart.as_expr()).coeff(w,power)
            block=sum(sp.expand(raw).coeff(al,2*j)*x**j for j in range(4))
            coeff.append(block)
        aa,bb,cc=[f.subs(values_at) for f in coeff]
        ras=[(uu*sp.diff(f,sv)-vv*sp.diff(f,rv)).subs(values_at) for f in coeff]
        dots=[-2*x*zz*sp.diff(f,x)-alphaval*rf for f,rf in zip((aa,bb,cc),ras)]
        aq,bq=aa.subs(x,alphaval**2),bb.subs(x,alphaval**2)
        dq=betaval+aq;eq=betaval**2+aq*betaval+bq
        a_motion=ras[0].subs(x,alphaval**2)+2*alphaval*zz*sp.diff(aa,x).subs(x,alphaval**2)
        b_motion=ras[1].subs(x,alphaval**2)+2*alphaval*zz*sp.diff(bb,x).subs(x,alphaval**2)
        d_dot=-alphaval*(yy+a_motion)
        e_dot=-alphaval*((2*betaval+aq)*yy+betaval*a_motion+b_motion)
        substitution={a:aa,b:bb,c:cc,d:dq,e:eq,da:dots[0],db:dots[1],dc:dots[2],dd:d_dot,de:e_dot}
        for i,ni in [(1,n1),(2,n2)]:
            independent=sp.expand(ni.subs(substitution,simultaneous=True))
            quotient,remainder=sp.div(independent,x-alphaval**2,x)
            assert sp.expand(literal_poly(frame[f'P{i}'],values,(x,))-quotient)==0
            assert sp.Rational(values[frame['remainder_nodes'][i-1]])==remainder
        checks.append({'trial':trial,'partial_and_current_numerator_checks':True,
                       'exact_protected_source_binding':True,'both_polynomial_divisions':True})

    # Independently match every full-incidence coefficient to the exact root
    # certificate's polynomial system, including the independent g2 variables.
    import contact_certify as C
    glob=G.build();fullchecks=[]
    for trial in range(2):
        env={name:F(rng.randrange(-2,3)) for name in glob['contact_variable_order']}
        env.update(lam=F(1),r=F(2+trial),s=F(1),alpha=F(3-trial))
        values=B.N.evaluate_circuit({'nodes':glob['scalar_nodes'],'linear_solves':[]},env)
        point=[env[name] for name in glob['contact_variable_order']]+[env['r'],env['alpha']]
        for polynomial,node in zip(C.POLYS,glob['incidence_equation_nodes']):
            assert C.value(polynomial,point)==values[node]
        fullchecks.append({'trial':trial,'all_46_literal_equations_match_root_system':True})
    receipt={'status':'PASS','universal_Cramer_wedge_and_two_annihilator_identities':True,
        'universal_two_source_remainder_ideal_identities':True,
        'remainder_identity_formulas':{'N1_at_alpha_squared':str(remainder1),'N2_at_alpha_squared':str(remainder2)},
        'exact_rational_source_circuit_replays':checks,'exact_full_incidence_replays':fullchecks,
        'source_trace_proved':False,'full_certificate_proved':False,
        'source_circuit_sha256':hashlib.sha256((HERE/'contact_forms_residue_system.json').read_bytes()).hexdigest(),
        'global_residue_circuit_sha256':hashlib.sha256((HERE/'contact_forms_global_residue.json').read_bytes()).hexdigest(),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (HERE/'contact_forms_audit_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':audit()
