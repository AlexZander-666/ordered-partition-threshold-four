"""Effective whole-strip check. All numerical comparisons below are rational."""
import json
import math
import sys
from fractions import Fraction as Q
from pathlib import Path
N=int(sys.argv[1]) if len(sys.argv)>1 else 288
assert N>96
EPS=Q(1,10)
b0,b1=Q(2121320,10**7),Q(2121321,10**7)
assert 200*b0**2<9<200*b1**2
def expminus(x):
    assert x>=0
    return 1/sum(x**i/math.factorial(i) for i in range(21))
def check(label,cm,q1,q4):
    assert all(x>=0 for x in (cm,q1,q4))
    assert cm<Q(2,5),(label,"sample",float(cm))
    assert q1*q1+cm*cm<1,(label,"short",float(q1),float(cm))
    assert q4*q4+cm*cm<1,(label,"four",float(q4),float(cm))
    return max(q1*q1+cm*cm,q4*q4+cm*cm)
def disk_radius(h,r):
    u=Q(3,10)+r*h; W=1+u*h
    assert h*W<1
    size=(6+4*u*h+(u*h)**2)*u*u+u*(W**4+1)+(W**2+W**6/15)/(2*(1-h*W))
    assert size<4*r,(h,r,size)
    return size
def tiny():
    disk_radius(Q(1,32),Q(1,2));disk_radius(Q(1,10),Q(3,5))
    worst=(Q(0),-1)
    for i in range(256):
        l,h=EPS*i/256,EPS*(i+1)/256
        r=Q(1,2) if h<=Q(1,32) else Q(3,5); u=Q(3,10)+r*h
        B=r+u*u/(2*(1-u*h))
        low,high=b0-B*h,b1+B*h
        assert low>0
        assert h*(1+u*h)/3<1
        S=4*low-(4*high)**3*h*h/6
        short=Q(7,10)-3*high*h
        assert min(short,S)>0
        denmax=(1+u*h)**3+h/2
        denmin=(1-u*h)**3-h/2
        assert denmin>0
        amp=denmax/denmin
        # ne>=3 and ne>=N*l.  C=3/2 via circle minimum >1.
        T=amp*expminus(2*low*max(Q(3),N*l))
        assert (1-h**4/24)*Q(81,24)*Q(3,10)-13*h**4/24>1
        R=Q(3,2)*denmax*h*h/6 # Cauchy bound divided by epsilon
        E=R*h
        cm=T+E
        short_error=(2*T+2*E)/short
        four_error=(12*high*T+cm*(4*high)**2*h/2+2*R)/S
        val=check(("small",i),cm,short_error,four_error)
        worst=max(worst,(val,i))
    h=Q(3,N);r=Q(1,2) if h<=Q(1,32) else Q(3,5); u=Q(3,10)+r*h
    B=r+u*u/(2*(1-u*h));D=(3+3*u*h+(u*h)**2)*u+Q(1,2)
    loss=3*b1+h*(b1+(3+h)*B+D/(1-D*h))
    assert D*h<1 and loss<Q(3,4)
    return worst,loss
def compact():
    base=Path(__file__).resolve().parent
    rows=json.loads((base/'dominance.json').read_text())
    unit=10**12; last=Q(1,32); worst=(Q(0),-1)
    assert Q(81,24)*Q(3,10)*Q(116,125)-13*(1-Q(116,125))>Q(1,300)
    for i,(lo,hi,R,L) in enumerate(rows):
        l,h=Q(lo),Q(hi); assert l==last and h>l;last=h
        if h<=EPS:continue
        def geom(box):
            x,y,r,m=box; a=math.isqrt(x*x+y*y)
            return [Q(t,unit) for t in (x,y,r,a-r,a+1+r)]
        x,y,r,Rl,Ru=geom(R);X,Y,s,Ll,Lu=geom(L)
        lam,lamlo=Ru/Ll,Rl/Lu
        assert 0<lamlo<lam<1 and 0<h*Ru/3<1 and x-y-2*r>0
        power=lam**N
        dlow=l**3*(Ll**3-h/2)/6
        dhigh=h**3*(Ru**3+h/2)/6
        assert dlow>0
        A=(Ru**3+h/2)/(Ll**3-h/2)
        T=A*power
        E=450*dhigh*(h*Ru/3)**N
        cm=T+E
        if R[3]==1:
            xl,yl=x-r,y-r
            assert min(xl,yl)>0
            short=yl/Ru
            f=4*xl*yl*(x-y-2*r)*(x+y-2*r)/Ru**4
            assert min(short,f)>0
            phi=4*(abs(X+Y)+2*s)/(Y-X-2*s)
            assert Y-X-2*s>0
            # |1+cos4theta|/sin4theta=(x-y)(x+y)/(2xy).
            main=(x-y+2*r)*(x+y+2*r)/(2*xl*yl)
            short_err=(2*T+2*E)/short
            four_err=cm*main+(T*((1-lamlo**4)+phi)+2*E)/f
        else:
            assert R[3]==2 and y==0
            # |G'(zeta)| <= 5 Im zeta, cos theta>1/2.
            DS=max(5*h*Ru,Q(5,2)*(h*Ru)**2/(l*(x-y-2*r)))
            short_err=four_err=2*DS*(power/dlow+450*(h*Ru/3)**N)
        score=check(("compact",i),cm,short_err,four_err)
        worst=max(worst,(score,i))
    assert last==Q(1143,1000)
    return worst
if __name__=='__main__':
    (sm,i),loss=tiny(); (co,j)=compact()
    print(f'PASS n>={N}, 256 small-epsilon cells and the applicable original compact cells, all four shifts')
    print(f'worst small sum of squares {float(sm):.9f} cell {i}; compact {float(co):.9f} cell {j}')
    print(f'far endpoint loss {float(loss):.9f} < 3/4')
