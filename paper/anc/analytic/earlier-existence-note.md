# Four poles for ordered partitions with blocks of size at least four

Research draft and component audit, 27 November 2026. The two finite certificates are exact rational arithmetic. The all-large-ranks argument below is a paper result pending peer review and Lean formalization. The primary proof below counts all roots directly by phase. A separate check below recovers the same root count using the existing all-threshold extreme-root theorem.

**Proposition.** There exists an integer $N$ such that, for $n\ge N$ and $h=1,2,3,4$, the two ordered-partition rows $O_{n,4}$ and $O_{n+h,4}$ have simple negative roots and strictly interlace. At equal degree the leftmost root belongs to the old row, and at an increase of one it belongs to the new row. The leading estimates in this version establish existence of $N$; no numerical value of $N$ has been certified. A uniform six-row window is impossible by the degree difference at $4m+3$ and $4m+8$.

## Original combinatorics and prior work

In an ordered set partition of $[n]$ the blocks themselves have a linear order. Mark each block of size at least four with $t$. Removing the first block of size $a$ gives $O_0=1$ and
$$
O_n(t)=\sum_{a=1}^n {n\choose a}t^{[a\ge4]}O_{n-a}(t).
$$
Thus the degree is $\lfloor n/4\rfloor$, the constant term is positive (all singletons), and the leading coefficient is positive (choose that many 4-blocks plus any leftover singletons). For example $O_4=74+t$, $O_5=530+11t$, and $O_8=521640+24125t+70t^2$. The recurrence and an independent calculation choosing actual subsets of labels as the successive blocks agree through $n=9$. [Original ordered conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#set-partitions-and-trees)

Chengyi Fang's 26 November 2026 Theorem 1 treats the **unordered** threshold-four model, whose EGF is exponential in the marked block series. The theorem gives eventual shifts one through four for that model, and uses a limiting edge count to index the bulk oscillations. We use a related counting principle here. The ordinary reciprocal of the marked block series for ordered blocks yields a meromorphic EGF and the four-pole calculation below. Its fourth row has 75 objects in total, while the unordered fourth row has 15. The prior project proofs for ordered thresholds 2 and 3 and the all-threshold fixed-prefix theorem are used as background. [Fang's preprint, Theorem 1 and Section 8](https://hexagonmath.org/pdf/2611.01129v1)

## The physical poles

Set $P_i(z)=\sum_{a=0}^i z^a/a!$, $q=-t/(1-t)$, $\delta=1-q$ and $\epsilon=(24\delta)^{1/4}$. For $t<0$ one has $0<q<1$ and
$$
 O_n(t)/n!=(1-q)[z^n]G_q(z)^{-1},\quad
 G_q(z)=q e^z+2(1-q)-P_3(z).
$$
At its zeros $G'_q(z)=z^3/6-2\delta$. The real critical point $x$ solves $q=P_2(x)e^{-x}$, a strictly decreasing function from $+\infty$ to $0$ (its derivative is $-x^2 e^{-x}/2$). The minimum value of $G_q$ is $-2J(x)$ where $J(x)=P_2(x)e^{-x}-1+x^3/12$. Its derivative is $x^2(1/4-e^{-x}/2)$. Consequently $J$ has exactly one strictly positive zero $\alpha$. Rational exponential bounds give $947/1000<\alpha<948/1000$. Set $q_c=1-\alpha^3/12>116/125$ and $\epsilon_c=(2\alpha^3)^{1/4}<1143/1000$. For $q_c<q<1$ the minimum is strictly positive. At $q_c$ the only real zero is the positive double zero $\alpha$, with $G''_{q_c}(\alpha)=\alpha^2/2>0$.

There are exactly four zeros, with multiplicity, in $|z|<3$ for $q_c\le q\le1$. To prove this let $U$ have density $4(1-u)^3$ on $(0,1)$ and put $H(z)=\mathbb E e^{Uz}$. Then
$$
G_q(z)=qz^4H(z)/24+\delta(2-P_3(z)).
$$
For $|\Im z|\le3$ the quantity $e^{-i\Im z/2}H(z)$ has strictly positive real part, since $3<\pi$. On $|z|=3$ also $\Re H(z)>3/10$. Indeed for $x=\Re z\le0$ use $\cos v\ge1-v^2/2$,
$$
 \Re H(z)\ge\mathbb E e^{-3U}-(9/2)\mathbb E U^2
 =\frac{24}{81}(2+e^{-3})-\frac3{10}>\frac3{10}.
$$
For $0\le x\le3$, use $1+x/5-(9-x^2)\mathbb E[U^2e^{xU}]/2$. The moments at $x=1,2,3$ are strictly below $1/8,1/5,3/10$, respectively, by positive rational Taylor sums with geometric remainders. Splitting at 1 and 2 gives the claimed bound. Since $13(1-q)<(81/24)(3/10)q$, Rouché's theorem counts four zeros and gives a uniform positive lower bound for $|G_q|$ on the circle. The real part of $G_q(iy)$ is $\delta+y^2/2-q(1-\cos y)>0$ for $q<1$. Thus no zero crosses the imaginary axis. The four fourth-root expansions below give two roots in each half-plane near $q=1$. This count persists on $[q_c,1)$. On the open oscillatory interval each pair consists of two nonreal conjugates, so all poles are simple. At the critical value the left-hand conjugate pair remains simple.

Denote the poles in the upper half-plane by $\zeta$ (right) and $\eta$ (left). These are continuous and analytic for $q_c<q<1$ by simplicity and uniqueness in their quadrants. The following strict separation applies throughout this interval:
$$
 |\zeta|<\epsilon<|\eta|,\qquad 0<\arg\zeta<\pi/4.
$$
Here is the certificate and its analytic endpoint.

* On $0<e=\epsilon\le1/32$ put $w=z/e$. The scaled function is $F_e(w)=2-e^{ew}+w^4H(ew)$. For each $\omega^4=-1$ its corresponding zero satisfies $|w-(\omega-3\omega^2 e/10)|<e^2$. On this disk boundary write $w=\omega-3\omega^2 e/10+v$ with $|v|=e^2$. Then $|w-\omega|\le e/3$ and $|w|\le1.011$. In $F_e(w)=1+w^4+e(w^5/5-w)+R$ the two first-order terms at $\omega$ cancel. Compare with $4\omega^3 v$: the remainder of $w^4$ after its linearization has size at most $(6+4|w-\omega|+|w-\omega|^2)e^2/9<0.68e^2$; the variation of the linear-in-$e$ term is at most $(|w| \mathbin{\vee}1)^4 e|w-\omega|+e|w-\omega|<0.69e^2$. The exponential remainder satisfies $|R|\le e^2 e^{e|w|}(|w|^2+|w|^6/15)/2<0.58e^2$ using $\mathbb E U^2=1/15$. Their sum is below $4e^2$. The disks are disjoint. For the right upper center $\omega=e^{i\pi/4}$, its squared modulus is $1-3\sqrt2 e/10+9e^2/100$, and the real part exceeds the imaginary part by $3e/10$. The left upper center has the opposite linear term in its squared modulus. A disk error of $e^2$ preserves these strict inequalities.
* The closed parameter range $[1/32,1143/1000]$ is covered by the 17 rational bins in **dominance.json**, verified by **boxes.py**. There are two disks in each bin. The left upper disk lies in the upper left quadrant and outside $|w|=1$. The right upper disk lies inside $|w|=1$ and $\Re w>\Im w$. The final right disk is centered on the real axis and contains two zeros counting multiplicity. Its identification on the oscillatory side follows from the real-axis exclusion and the four-zero count. Each disk in $w$ maps inside $|z|<3$.
* For a disk of radius $R$ and rational center $c$, compare $F_e$ with $F_{e_0}^{(\ell)}(c)(w-c)^\ell/\ell!$, $\ell=1,2$ and $e_0$ the bin midpoint. The verifier sums the lower jets using rational Gaussian arithmetic through degree 28. The coefficient for $h>0$ is $(-e^h+\mathbf1_{h\ge4}24e^{h-4})/h!$. For each jet through order two the tail is bounded by twice its first absolute majorizing term at $|w|\le2$, since consecutive ratios are below $1/10$. On $|w|\le W=|c|_{\rm upper}+R$, the parameter derivative is bounded by $W e^{eW}(1+W^4/5)$. The Taylor remainder in the disk uses the next $w$ derivative bound from the Leibniz rule on $w^4H(ew)$ and $e^{ew}$. Bounds for $\mathbb E[U^b e^{eW U}]$ sum through degree 20, using $\mathbb E U^a=24a!/(a+4)!$. Every parameter bin certifies the strict Rouché inequality for both disks. Decimal Newton iteration only proposes disks in generation mode. Replay uses the stored integers.

## Signs on the non-extreme part of the oscillatory interval

Set $R=|\zeta|$, $\theta=\arg\zeta$, $\phi=\arg\eta$, $\lambda=R/|\eta|$, $\beta=\arg G'_q(\zeta)$, $\gamma=\arg G'_q(\eta)$, and $\psi=(n+1)\theta+\beta$, $\chi=(n+1)\phi+\gamma$. The principal $\beta$ is continuous in $(0,\pi)$ because $\Im G'_q(\zeta)=R^3\sin(3\theta)/6>0$. The choice of $\gamma$ modulo $2\pi$ has no effect. With $A=|G'_q(\zeta)|/|G'_q(\eta)|$ and the positive normalization $S_n=|G'_q(\zeta)| R^{n+1}[z^n]G_q^{-1}/2$, the four residues and the contour give
$$
 S_n=-\cos\psi-A\lambda^{n+1}\cos\chi+E_n,\qquad
 |E_n|\le C |G'_q(\zeta)|(R/3)^{n+1}.
$$
The factor $C$ can be taken as $3/(2\min|G_q|)$ on the common contour.

We claim that there are constants $B,N_1$ such that, on the portion $q_c<q<1$, $n\ge N_1$, $n\epsilon\ge B$, the absolute error $|S_n+\cos\psi|<1/3$. At any true old-row zero there, $\operatorname{sgn}S_{n+h}=\operatorname{sgn}\sin\psi$ for all four shifts.

First fix a sufficiently small $e_0>0$. On $\epsilon\ge e_0$ modulus separation is uniform by the disks and compactness, including the left pair at $q_c$. The inequality at the merged right pair follows there from the same double disk, and $R<1.143$. At the double point, put $Y=\Im\zeta$. Taylor expansion of $G_q$ at $(q_c,\alpha)$ gives $\Re\zeta-\alpha=O(Y^2)$, $q-q_c=O(Y^2)$ and $G'_q(\zeta)=i(\alpha^2/2)Y+O(Y^2)$. For instance solve $q=(P_3(z)-2)/(e^z-2)$ near $\alpha$: this analytic map has a nondegenerate real quadratic critical point, so the two simple inverse branches have convergent square-root expansions in $q-q_c$. Consequently $|G'_q(\zeta)|/\sin(h\theta)$ stays bounded for $1\le h\le4$. The secondary and contour errors in both $S_n$ and $S_{n+h}$ are each $o(\sin(h\theta))$ uniformly. At $S_n=0$ expand $\cos(\psi+h\theta)$, use $\sin(h\theta)>0$ and $|\sin\psi|\to1$ uniformly.

For $e=\epsilon\downarrow0$, the four disks give, with $b=3/(10\sqrt2)$,
$$
 \theta=\pi/4-be+O(e^2),\quad
 \phi=3\pi/4-be+O(e^2),\quad
 \lambda=1-2be+O(e^2),\quad \beta=3\pi/4+O(e).
$$
Indeed $G'_q(ew)=e^3(w^3/6-e/12)$, so $A\to1$. Shrinking $e_0$ bounds $\lambda^{n+1}\le\exp(-bne)$ and $|G'_q(\zeta)|\le C'e^3$. For $h=1,2,3$, $\sin(h\theta)$ stays bounded away from zero; taking $B$ large controls both errors. For $h=4$ the old-zero calculation must keep the left pair signed. Add $S_n$ to $S_{n+4}$. The absolute secondary contribution is bounded by
$$
 A\lambda^{n+1}\bigl(|1-\lambda^4|+|4\phi-3\pi|\bigr)
 \le C''e\exp(-bne).
$$
The main contribution is $\sin\psi\sin(4\theta)-(1+\cos(4\theta))\cos\psi$. Here $\sin(4\theta)/e\to4b>0$ and $1+\cos(4\theta)=O(e^2)$. Once $B$ is large, at a zero $|\cos\psi|<1/3$ and $|\sin\psi|\ge\sqrt{8/9}$. The two contour errors divided by $e$ go uniformly to zero as $n\to\infty$. Choose $e_0$ small, then $B$ large, then $N_1$ large to get strict sign for all four shifts. An absolute-value estimate on the two whole left-pair terms separately loses the needed factor $e$ at shift four.

## A fixed endpoint counts all the roots

The preceding small-$e$ calculation has sufficient margin at the explicit cutoff $ne=3$. Thus the index matching against an external finite-prefix theorem can be dispensed with entirely. Here are the uniform estimates, including the worst fourth shift.

As $e\downarrow0$, $\log\lambda/e\to-2b$, so for all $ne\ge3$,
$$
 \limsup_{e\downarrow0}\ \sup_{n e\ge3} A\lambda^{n+1}\le T=e^{-6b}<29/100 .
$$
Indeed $\log\lambda<0$ there, so replace $n$ by the real lower bound $3/e$. Uniformly on this region, the contour errors at both $n$ and $n+h$ are $o(e)$. At old roots we have $\limsup|\cos\psi|\le T$ and $\liminf|\sin\psi|\ge\sqrt{1-T^2}$. For $h=1,2,3$, compare $-\cos(\psi+h\theta)$ with the error at the new row. The unwanted total divided by $\sin(h\theta)$ has upper limit $T(1+\sqrt2)$ for $h=1,3$, and $T$ for $h=2$. For $h=4$ use the signed addition:
$$
 \frac{|1-\lambda^4|}{\sin4\theta}\to2,\qquad
 \frac{|4\phi-3\pi|}{\sin4\theta}\to1,\qquad
 \frac{1+\cos4\theta}{\sin4\theta}\to0 .
$$
The normalized unwanted part has upper limit $3T$. Both $T(1+\sqrt2)$ and $3T$ are strictly less than $\sqrt{1-T^2}$. Thus there is an $e_0>0$ such that throughout $0<e\le e_0$, $ne\ge3$, all the true-root signs hold and $|S_n+\cos\psi|<1/3$. On $e_0\le e\le e_c$ the compact argument gives the same conclusions for sufficiently large $n$. The strict numerical margins use only $\sqrt2<10/7$, hence $6b>63/50$; the degree-five positive Taylor sum of $\exp(63/50)$ exceeds $100/29$.

For each sufficiently large $n=4d+r$ stop at $q_*=1-(3/n)^4/24$. At $q_c$ the limiting phase is $\pi/2$. At $q_*$ the phase is
$$
 \psi=(d+1+r/4)\pi-3b+O(1/n).
$$
Since $3b<\pi/4$, the worst case $r=0$ still reaches the last upper boundary $(d+1)\pi-\pi/4$. The phase is continuous and crosses in order all $d$ disjoint strips
$$
[i\pi+\pi/4,(i+1)\pi-\pi/4],\qquad i=1,\ldots,d.
$$
Use the first upper endpoint after the preceding strip, and its last preceding lower endpoint. The values at these two points differ in sign because $|S_n+\cos\psi|<1/3$. Degree gives exactly one zero in each strip, of multiplicity one, and exhausts every complex zero. At old zero number $i$ in increasing $q$, the new row has sign $(-1)^i$ since $\sin\psi$ does. At $q=0$ it is positive. These signs give one new root before the first old root and one in each succeeding gap. If the degree rises to $d+1$, the sign near $q=1$ is $(-1)^{d+1}$ by positivity of the leading coefficient and provides the last new root. At equal degree the preceding $d$ intervals already exhaust the new row. Finally $t$ decreases as $q$ increases, giving the orientations in the proposition. No sign assertion on $0<ne<3$ is needed once the degree has been exhausted.

## Independent check of the absolute index from the reciprocal-edge limit

Fix an integer $K\ge2$ so large that $K\pi/b>B$. For $n=4d+r$ with $0\le r<4$ take the seam $Y_*=(K+r/4)\pi$, where $Y=bn\epsilon$. The lower-$q$ phase tends to $\pi/2$ at $q_c$. The phase at the seam is
$$
 \psi=(d+1+r/4)\pi-Y_*+O_K(1/n)=(d-K+1)\pi+O_K(1/n).
$$
The error uses $n\epsilon^2=O_K(1/n)$ there. By continuity (without monotonicity), the phase traverses all the disjoint strips $[i\pi+\pi/4,(i+1)\pi-\pi/4]$ for $1\le i\le d-K$. One can use the first upper endpoint after the preceding strip and the last lower endpoint before it. The normalized error $<1/3$ forces an old zero in each strip. Its $\sin\psi$ sign is $(-1)^i$ on the entire chosen subinterval in the $i$th strip.

Beyond the seam there are at least $K$ distinct simple old roots. To check the absolute index rather than only a local density, use the exact reciprocal scale from the formal all-threshold edge theorem. At the seam
$$
 S_{4,d}/t=-24(6d/5)^4\,\epsilon^4/(24-\epsilon^4)\longrightarrow-4Y_*^4.
$$
For each section $F_r(w)=\sum w^h/(4h+r)!$ one has, at $w=-4Y^4$,
$$
\begin{aligned}
F_0&=\cosh Y\cos Y,&F_1&=(\sinh Y\cos Y+\cosh Y\sin Y)/(2Y),\\
F_2&=\sinh Y\sin Y/(2Y^2),&
F_3&=(\cosh Y\sin Y-\sinh Y\cos Y)/(4Y^3).
\end{aligned}
$$
These identities follow from the four multisections at $(1+i)Y$. In increasing positive $Y$, $F_0$ has one zero at each $(i+1/2)\pi$, $F_2$ at each $(i+1)\pi$, $F_1$ one in $((i+1/2)\pi,(i+1)\pi)$ and $F_3$ one in $((i+1)\pi,(i+3/2)\pi)$, for $i=0,1,\ldots$. For the latter two use $\tan Y=\mp\tanh Y$; on positive tangent intervals for $F_3$, $\sec^2Y-\operatorname{sech}^2Y>0$ for $Y>0$. The apparent root at zero cancels. There are exactly $K$ zeros strictly before $Y_*$ in each of the four cases. In particular no limiting zero is exactly at the seam. The already checked convergence of the indexed largest-modulus original roots therefore places $K$ roots in $q>q_*$, since $S_{4,d}/t$ increases toward zero there. Degree $d$ forces all strip roots and these $K$ extreme roots to be the complete list, each of multiplicity one. This works for every large rank independently.

At the first $d-K$ roots in increasing $q$, the new row has sign $(-1)^i$ by the four-residue estimate. For the remaining $K$ old roots the pre-existing true-row extreme theorem **original_rank_window** gives the required order relative to the $K+1$ extreme roots of the new row. Indeed if an old root is number $u$ from the negative left, counted starting at one, the new row has exactly $u-1$ roots to its left at equal degree, and exactly $u$ at a unit degree rise. Its $(K+1)$st root is to the right of that old root in both cases. All other new roots are still farther right by the strict modulus cutoff and by the large-row real-rootedness just established. Starting at $-\infty$ with the sign of the leading term yields $(-1)^{d+1-u}=(-1)^i$ in both cases. With $O_{n+h}(0)>0$, there is one new root before the first old root in increasing $q$, and one between each consecutive pair. At a degree increase the positive leading coefficient gives the remaining new root past the last old root. The orientation in the proposition follows after reversing $q$ to $t$.

## Status and a follow-up test

The four-pole count, uniform modulus separation and signed four-step cancellation cover the whole oscillatory range necessary to count all roots of every sufficiently large ordered row. The remaining all-sizes question is an effective onset and the ranks below it. The direct cutoff proof above permits an effective onset in principle: make the corner Taylor bounds and the compact $|G'|/\sin(h\theta)$ bound quantitative, and derive the required $n$ from the margin at the seam. The 17-bin certificate checks only pole separation and angles, not all these large-$n$ error inequalities. The four small example rows do not certify an all-sizes theorem. No verdict from an external reviewer is attached to this new proposition.
