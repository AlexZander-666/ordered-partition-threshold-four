"""Independent exact small checks and inequalities for the radius-three contour."""
from fractions import Fraction as Q
from math import factorial, comb
from itertools import combinations
from functools import cache

def exp_enclosure(v):
    assert 0<=v<=3
    p=sum(v**i/factorial(i) for i in range(21))
    return p,p+2*v**21/factorial(21)

def critical_sign(x):
    a,b=exp_enclosure(x)
    c=1+x+x*x/2
    return c/b-1+x**3/12, c/a-1+x**3/12

def moment(y):
    # E[U^2 exp(yU)], U has density 4(1-u)^3.
    return sum(Q(24*factorial(2+i),factorial(i+6))*y**i/factorial(i)
               for i in range(21))+2*y**21/factorial(21)

def checked_rows():
    rows=[[1]]
    for n in range(1,10):
        p=[0]*(n//4+1)
        for a in range(1,n+1):
            for i,c in enumerate(rows[n-a]):
                p[i+int(a>=4)]+=comb(n,a)*c
        rows.append(p)
    @cache
    def brute(labels):
        if not labels:return (1,)
        ans=[0]*(len(labels)//4+1)
        for a in range(1,len(labels)+1):
            for first in combinations(labels,a):
                rest=tuple(x for x in labels if x not in first)
                for i,c in enumerate(brute(rest)):
                    ans[i+int(a>=4)]+=c
        return tuple(ans)
    for n,p in enumerate(rows):
        assert tuple(p)==brute(tuple(range(n)))
    return rows

if __name__=='__main__':
    lo,hi=Q(947,1000),Q(948,1000)
    assert critical_sign(lo)[1]<0<critical_sign(hi)[0]
    assert 1-hi**3/12>Q(116,125)
    assert 2*hi**3<Q(1143,1000)**4
    assert exp_enclosure(Q(3))[1]<40
    assert Q(24,81)*(2+Q(1,40))-Q(3,10)==Q(3,10)
    for y,b in [(Q(1),Q(1,8)),(Q(2),Q(1,5)),(Q(3),Q(3,10))]:
        assert moment(y)<b
    assert Q(116,125)*Q(81,24)*Q(3,10)>13*Q(9,125)
    assert Q(10,7)**2>2 and Q(7,5)**2<2
    assert sum(Q(63,50)**i/factorial(i) for i in range(6))>Q(100,29)
    T=Q(29,100)
    assert (3*T)**2<1-T*T and ((1+Q(10,7))*T)**2<1-T*T
    assert Q(9,10)/Q(7,5)<Q(3,4)
    print('Critical point, contour, fourth-step cancellation and final phase endpoint: PASS')
    for n,p in enumerate(checked_rows()):
        if n in (4,5,8,9):print(f'O[{n},4] ascending coefficients = {p}')
