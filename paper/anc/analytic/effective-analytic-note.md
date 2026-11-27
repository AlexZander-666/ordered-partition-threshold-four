# Effective four-pole interlacing from rank 288

Let $O_n(t)$ count ordered partitions of $[n]$, with one mark $t$ for each block having at least four elements. For $n\ge288$ and $1\le h\le4$, $O_n$ and $O_{n+h}$ have only simple negative zeros and strictly interlace. When their degrees agree the old row has the leftmost zero. At a unit degree increase the new row does. This statement is the effective extension of the enclosed proof.md. It uses that proof's four-pole classification and its 17 exact disk certificates. The new assertion reduces the remaining finite question to old ranks below 288.

Chengyi Fang, Theorem 1 and Section 8 of the threshold-four unordered-partition preprint, also uses a fourth-shift cancellation at a true old-row zero in the unordered model. The effective estimates below use the meromorphic denominator of ordered blocks and its four physical poles. The original conjecture distinguishes the order on blocks. [Fang](https://hexagonmath.org/pdf/2611.01129v1) · [Original ordered question](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#set-partitions-and-trees)

## A pointwise sign test

Use $e=(24(1-q))^{1/4}$, $q=-t/(1-t)$, the two true upper poles $\zeta=e w$, $\eta=e v$ and their arguments $\theta,\phi$, and write $R=|\zeta|$, $\lambda=|w|/|v|$, $A=|G'_q(\zeta)|/|G'_q(\eta)|$. Put $T\ge A\lambda^{n+1}$ and $E\ge|E_n|,|E_{n+h}|$, where the normalized row is $S_n=-\cos\psi-A\lambda^{n+1}\cos\chi+E_n$. At $S_n=0$, $|\cos\psi|\le c=T+E$. For each shift a sufficient test is
$$
c<2/5,\qquad c^2+L_h^2<1,\qquad
|S_{n+h}-\sin\psi\sin(h\theta)|\le L_h\sin(h\theta).
$$
Indeed $|\sin\psi|>L_h$ and $\sin(h\theta)>0$. For $h\le3$ the absolute error is at most $2T+2E$. At $h=4$ adding the old zero gives an upper bound
$$
c|1+\cos4\theta|+T\big(1-\lambda^4+|4\phi-3\pi|\big)+2E.
$$
This uses the *same* pair of secondary phases at the true old root. The real cosine identity at the odd multiple $3\pi$ gives the cancellation. At the cell touching the critical point the direct bound $2T+2E$ for the fourth shift is more convenient.

## Small parameters through one tenth

Write $H(z)=\mathbb E e^{Uz}$ with $U$ of density $4(1-u)^3$ on $[0,1]$. In the scaled variable the denominator is $2-e^{ew}+w^4H(ew)$. For $0<e\le H_0$, its root belonging to $\omega^4=-1$ lies within $r e^2$ of $\omega-3\omega^2 e/10$. Use $(H_0,r)=(1/32,1/2)$ and $(1/10,3/5)$. To check this, on the disk boundary put $W=1+uH_0$, $u=.3+rH_0$. Compare to $4\omega^3(w-\omega+.3\omega^2e)$. The constant and linear-in-$e$ terms cancel. The quartic remainder, the displacement in $e(w^5/5-w)$, and the exponential remainder divided by $e^2$ have sum bounded by
$$
(6+4uH_0+(uH_0)^2)u^2 + u(W^4+1)
   + \frac{W^2+W^6/15}{2(1-H_0W)}<4r.
$$
Here $\mathbb E U=1/5$, $\mathbb E U^2=1/15$ and $\exp(t)\le(1-t)^{-1}$ for $0\le t<1$. Rouché applies to each disjoint disk. For the two upper disks the labeled quadrants agree with the global classification. The two upper ratios are $w/\omega=1+d$ with $|d+.3\omega e|<r e^2$, $|d|\le u e$. Hence the error in $\log(1+d)+.3\omega e$ is bounded by $B e^2$, where $B=r+u^2/(2(1-uH_0))$. The log series used here stays on the principal branch.

The verifier divides $[0,1/10]$ into 256 closed equal cells $[l,h]$ with the split at $1/32$ exactly on a cell boundary. Use $u=.3+rh$ and the same monotone expression for $B$ with $H_0=h$. Put $b=3/(10\sqrt2)$, $L=.2121320-Bh$, $U_1=.2121321+Bh$. Then
$$
4Le\le \pi-4\theta\le4U_1e,\quad
|4\phi-3\pi|\le4U_1e,\quad 2Le\le-\log\lambda\le2U_1e .
$$
Thus $\sin4\theta/e\ge S=4L-(4U_1)^3h^2/6$, and $\sin(a\theta)\ge .7-3U_1h$ for integers $1\le a\le3$. With $M=(1+uh)^3+h/2$, $m=(1-uh)^3-h/2>0$ we may take
$$
 T=(M/m)\left(\sum_{a=0}^{20}
      (2L\max(3,288l))^a/a!\right)^{-1}.
$$
Here $ne\ge 3$ and $n\ge288$. The circle $|z|=3$ has $|G_q(z)|>1$ by the enclosed circle estimate. Its error is at most $(3/2)|G'_q(\zeta)|(R/3)^{n+1}$, where $|G'_q(ew)|=e^3|w^3-e/2|/6$. Set $P=(3/2)Mh^2/6$, so every contour error is bounded by $Pe$ and $E=Ph$ works. The fourth relative error is bounded by
$$
 L_4=\frac{12 U_1T+c(4U_1)^2h/2+2P}{S}.
$$
This follows from $1-\lambda^4\le-4\log\lambda$ and $1+\cos4\theta\le (4U_1e)^2/2$. The shift $a\le3$ uses $(2T+2E)/(.7-3U_1h)$. Every denominator and both squared tests are verified with fractions.

## The compact pole boxes and the critical double pole

Use the enclosed disk pairs for the remaining parameters, in the scaled $w$ plane. On each bin $[l,h]$ let the right and left centers be $(x,y),(X,Y)$ with radii $r,s$. Let $R_l,R_u,L_l,L_u$ bound the two moduli, obtained with integer square roots and outward rounding. Use $\Lambda=R_u/L_l<1$, $\lambda_0=R_l/L_u>0$, $d_-=l^3(L_l^3-h/2)/6$, $d_+=h^3(R_u^3+h/2)/6$. The physical residue norm satisfies $|G'_q(\eta)|\ge d_->0$ and $|G'_q(\zeta)|\le d_+$. The global contour estimate gives $|G_q(z)|>1/300$ on $|z|=3$ because $q>116/125$. We use
$$
T=\frac{R_u^3+h/2}{L_l^3-h/2}\Lambda^{288},\qquad
E=450d_+(hR_u/3)^{288}.
$$
All weights at larger row indices also satisfy these bounds. The ratio used for $T$ cancels $e^3/6$ at the same physical parameter.

In each simple upper right disk put $x_l=x-r$, $y_l=y-r$. Since $0<\theta<\pi/4$, $\sin(a\theta)\ge\sin\theta\ge y_l/R_u$ for $1\le a\le3$. Further,
$$
\sin4\theta\ge f=4x_ly_l(x-y-2r)(x+y-2r)/R_u^4,\qquad
\frac{1+\cos4\theta}{\sin4\theta}\le\frac{(x-y+2r)(x+y+2r)}{2x_ly_l}.
$$
For the upper-left angle, $|4\phi-3\pi|\le4(|X+Y|+2s)/(Y-X-2s)$ using $|\arctan t|\le |t|$. Substitute these bounds and $1-\lambda^4\le1-\lambda_0^4$ into the preceding fourth-shift test. The first of the 17 original bins lies wholly within the small-parameter argument. Sixteen overlapping compact bins are used.

The last right disk contains the two conjugates and touches the real axis. Set $\zeta=x_0+i y_0$, with $0<y_0<6/5$, $0<x_0<6/5$. The imaginary part of $G_q(\zeta)=0$ gives
$$
\Re G'_q(\zeta)=(y_0\cot y_0-1)(1+x_0+x_0^2/2-y_0^2/6)+y_0^2/3 .
$$
Since $\sin y_0-y_0\cos y_0=\int_0^{y_0}t\sin t\,dt\le y_0^3/3$ and $\sin y_0\ge3y_0/4$, the absolute real part is at most $5y_0^2/3$ (the bracket lies in $(0,3)$). The imaginary part from $\zeta^3/6-2(1-q)$ has absolute value at most $y_0$ since $(3x_0^2+y_0^2)/6<1$. In particular $|G'_q(\zeta)|\le5y_0$. For $a\le3$, $|G'_q(\zeta)|/\sin(a\theta)\le5hR_u$. For $a=4$ use $\cos\theta>1/2$ and $\cos2\theta\ge(x_0-y_0)/R$ to get the upper bound $5(hR_u)^2/[2l(x-y-2r)]$. If $D$ is the larger of these two bounds, use the direct relative error
$$
2D\big(\Lambda^{288}/d_-+450(hR_u/3)^{288}\big)
$$
for all four shifts. This uniform inequality permits $q$ arbitrarily close to $q_c$ from above.

## Traversal and orientation

At $e=3/n\le1/96$ the normalized derivative factor at the right pole is
$G'_q(ew)/(e^3\omega^3/6)=(1+d)^3-e/(2\omega^3)$. It is within $D e$ of one where $D=(3+3uh+u^2h^2)u+1/2$, $h=3/288$. Thus $|\beta-3\pi/4|\le De/(1-Dh)$, and the far endpoint phase exceeds $(n/4+1)\pi-.671$, where $n/4$ denotes real division. In particular it exceeds the last strip endpoint $(\lfloor n/4\rfloor+1)\pi-\pi/4$, including when $4\mid n$. At the critical double pole the phase tends to $\pi/2$ by the local expansion in the enclosed proof. On the interval between these endpoints one has $ne\ge3$. Continuity of the primary phase traverses all $\lfloor n/4\rfloor$ strips. The test $c<2/5<\cos(\pi/4)$ gives an old zero inside each strip. Degree gives their simplicity and exhaustiveness. The shifted sign at each such root and positivity at $t=0$ give the new roots in the successive intervals, with a final root to the left when the degree rises. The change $t=-q/(1-q)$ reverses orientation. This argument does not rely on the alternative large-rank extreme-root seam construction.

Run **boxes.py**, **arithmetic.py**, then **certificate.py** using Python 3. The certificate uses exact fractions. The reported worst squared tests are approximately .987357440 and .064608115 and the endpoint loss is less than .671. This effective extension has separate review status from the earlier non-effective paper and separate mathematical scope from the Lean corner-component archive. The independently generated finite certificate covers all 1,152 comparisons with old rank 0 through 287. It contains 10,512 rational single-root brackets for rows up to rank 291, with SHA-256 343ad2743d899a44475a69588f0810ab9c5786f7249a21995e3c1894a3ed520c. Combined with the tail proved above it yields the all-sizes assertion on paper with finite exact computation. The formal Lean audit of that combined assertion is a separate task.
