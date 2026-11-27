"""Generate centers heuristically, verify all closed epsilon bins with integer interval arithmetic."""
import cmath
import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

UNIT = 10**12
CUT = 28
FAC = math.factorial

def up(x):
    return -((-x.numerator) // x.denominator)

def normhi(z):
    return math.isqrt(z[0]**2+z[1]**2)+1

def normlo(z):
    return math.isqrt(z[0]**2+z[1]**2)

def approx(e, start):
    q=1-e**4/24
    w=start
    for i in range(100):
        # evaluation in the scaled coordinate avoids destructive cancellation near zero
        c=[-e**h/FAC(h)+(24*e**(h-4)/FAC(h) if h>=4 else 0) for h in range(CUT)]
        c[0]=1.
        val=sum(a*w**h for h,a in enumerate(c))
        grad=sum(h*a*w**(h-1) for h,a in enumerate(c) if h)
        if abs(grad)<1e-14:break
        if abs(val)<1e-14:break
        w-=val/grad
    return complex(w.real, abs(w.imag))

def coefficients(e):
    return [F(1) if h==0 else ((24*e**(h-4) if h>=4 else F(0))-e**h)/FAC(h) for h in range(CUT+1)]

def jets(e,c):
    # Gaussian rationals exact, round once at the end. |c| <= 2 and e<=6/5.
    # Derivatives m<=2 of both series beyond h=28: individually <= first term
    # times 2 since e*|c|/(h+1-m)<1/10.
    ca,cb=c
    co=coefficients(e)
    out=[]
    for m in range(3):
        x,y=F(0),F(0)
        for h in range(CUT,m-1,-1):
            x,y=x*ca-y*cb+co[h]*F(FAC(h),FAC(h-m)),x*cb+y*ca
        tail=2*(24*e**(CUT+1-4)+e**(CUT+1))*2**(CUT+1-m)/FAC(CUT+1-m)
        z=(int(x*UNIT),int(y*UNIT))
        out.append((F(max(0,normlo(z)-2),UNIT)-tail,F(normhi(z)+2,UNIT)+tail))
    return out

def posder(degree,e,W,m):
    # Majorize d^m/dw^m [w^degree E(exp(U e w))] on |w|<=W,
    # where E[U^a]=24 a!/(a+4)! if degree=4; U=1 if degree=0.
    val=F(0)
    for a in range(min(m,degree)+1):
        b=m-a
        coeff=F(math.comb(m,a)*FAC(degree),FAC(degree-a))*W**(degree-a)*e**b
        total=F(0)
        for l in range(21):
            moment=F(24*FAC(b+l),FAC(b+l+4)) if degree else F(1)
            total+=moment*(W*e)**l/FAC(l)
        total+=2*(W*e)**21/FAC(21)
        val+=coeff*total
    return val

def expupper(v):
    return sum(v**i/FAC(i) for i in range(14))+2*v**14/FAC(14)

def certified(lo,hi,box,side):
    ca,cb,rad,mode=box
    R=F(rad,UNIT); c=F(ca,UNIT),F(cb,UNIT)
    low=F(normlo((ca,cb)),UNIT); high=F(normhi((ca,cb)),UNIT)
    if not (0<R and high+R<=2 and F(0)<lo<=hi<=F(6,5)):return False
    if side=="right" and not (high+R<1 and c[0]-c[1]>2*R):return False
    if side=="left" and not (1<low-R and c[0]+R<0):return False
    if mode==1 and not c[1]>R:return False
    if mode==2 and not (side=="right" and c[1]==0):return False
    if mode not in (1,2):return False
    W=high+R
    mid=(lo+hi)/2
    j=jets(mid,c)
    p=(hi-lo)/2*W*expupper(hi*W)*(1+W**4/5)
    rem=posder(0,hi,W,mode+1)+posder(4,hi,W,mode+1)
    err=sum(j[h][1]*R**h/FAC(h) for h in range(mode))+rem*R**(mode+1)/FAC(mode+1)+p
    return err<j[mode][0]*R**mode/FAC(mode)

def candidates(mid,side):
    w=approx(mid,complex(.82,.35) if side=="right" else complex(-.72,.85))
    if side=="right" and w.imag<.20:
        for rh in [.15,.125,.10,.075]:
            base=complex(.83,0)
            yield [int(base.real*UNIT),0,int(rh*UNIT),2]
    lim=min(w.imag*.9, abs(abs(w)-1)*.98,
            (w.real-w.imag)*.48 if side=="right" else -w.real*.9)
    for f in [.7,.4,.9,.2]:
        yield [int(w.real*UNIT),int(w.imag*UNIT),int(lim*f*UNIT),1]

def create(lo,hi,out):
    boxes=[]
    for side in ["right","left"]:
        hit=next((box for box in candidates(float((lo+hi)/2),side)
                  if certified(lo,hi,box,side)),None)
        if hit is None:
            if hi-lo<F(1,10**7):raise ValueError((lo,hi,side))
            mid=(lo+hi)/2
            create(lo,mid,out)
            create(mid,hi,out)
            return
        boxes.append(hit)
    out.append([str(lo),str(hi),*boxes])

def main():
    file=Path(__file__).with_name('dominance.json')
    if '--generate' in sys.argv:
        rows=[]
        create(F(1,32),F(1143,1000),rows)
        file.write_text(json.dumps(rows,indent=1)+'\n')
    rows=json.loads(file.read_text())
    end=F(1,32)
    for low,high,right,left in rows:
        low,high=F(low),F(high)
        assert low==end and high>low
        assert certified(low,high,right,'right') and certified(low,high,left,'left')
        end=high
    assert end==F(1143,1000)
    print(f'{len(rows)} closed bins; {sum(row[2][3]==2 for row in rows)} conjugation-symmetric two-zero right disks; all exact disk tests passed')

if __name__=='__main__':main()
