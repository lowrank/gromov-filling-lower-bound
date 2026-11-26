# A sharp pair-weight inequality for Züst's continuum form

For every interior angular distance profile, the total weight in Züst's continuum two-form is at most $`\pi^2/2`$. Equality holds exactly for the profiles of the open round hemisphere. This answers Question 2 in the 2021 arXiv version of Züst's paper. The deficit is the sum of two squared operator norms. In particular it charges every odd Fourier mode above the first in the sine of the profile. [Züst, §5, Question 2](https://arxiv.org/pdf/2104.04498) · [Separate test of the planar comass](issue163_zust_angles.md)

Let $`F(a)`$ be 1-Lipschitz in the angular label, with $`F(a+\pi)=-F(a)`$ and $`\|F\|_\infty\lt\pi/2`$. In the notation of the paper its distance profile is $`f=\pi/2-F`$. Write $`x_a=\sin F(a)=\cos f(a)`$. For $`\delta=b-a`$ the pair coefficient is

~~~math
 p_{ab}=
 \frac{1-(x_a^2+x_b^2-2x_ax_b\cos\delta)/\sin^2\delta}
 {(1-x_a^2)(1-x_b^2)} .
~~~

The numerator is nonnegative. Indeed $`|F_a-F_b|\le\delta`$ and $`|F_a+F_b|\le\pi-\delta`$ for $`0\lt\delta\lt\pi`$. After multiplication by $`\sin^2\delta`$ the numerator factors as $`[\cos(F_a-F_b)-\cos\delta][\cos(F_a+F_b)+\cos\delta]`$. The coefficient is symmetric in its two labels and separately $`\pi`$-periodic. With probability measure $`d\mu=da/(2\pi)`$ on the full circle and $`\widehat x_j=\int x_a e^{-ija}\,d\mu(a)`$, set

~~~math
 P=\iint p_{ab}\,d\mu(a)d\mu(b)
   =\frac{2}{\pi^2}\int_0^\pi\int_a^\pi p_{ab}\,db\,da .
~~~

Then

~~~math
 \boxed{P+2\sum_{|j|\ge3} (|j|-1)|\widehat x_j|^2\ \le\ 1.}
~~~

All even coefficients vanish. The factor 2 is sharp, including when tested on any one higher odd mode at small amplitude. In particular the conjectured total-weight bound and its equality case hold without a discretization or an optimization.

## An exact sum of squares

On $`L^2(S^1,d\mu)`$ let $`H`$ be the circular Hilbert transform with Fourier multiplier $`-i\,\mathrm{sgn}(j)`$ and zero constant mode. Thus $`H^*=-H`$ and $`H^2=-I+1\otimes1`$. Its principal-value convolution kernel in probability normalization is $`\cot((a-b)/2)`$. These formulas also follow by summing the positive and negative geometric Fourier series with a radial factor and letting that factor increase to one. Denote multiplication by $`g`$ by $`M_g`$. Put

~~~math
 m=(1-x^2)^{-1/2},\qquad t=xm,\qquad A=\int m^2\,d\mu,\qquad e=m/\sqrt A .
~~~

An even function below is one fixed by the half-turn $`a\mapsto a+\pi`$. Let $`E`$ be the orthogonal projection onto the even functions orthogonal to $`e`$. Define

~~~math
 B=M_t H M_m-M_m H M_t=M_m[M_x,H]M_m,\qquad
 N=M_m H M_m-M_t H M_t .
~~~

The first operator is self-adjoint and exchanges the even and odd subspaces. Its kernel is $`m_am_b(x_a-x_b)\cot((a-b)/2)`$. It is Hilbert–Schmidt, since the Lipschitz difference cancels the pole and $`m`$ is bounded. The second operator is skew-adjoint. The exact identity is

~~~math
 \boxed{1-P=\|Ne\|_2^2+\|BE\|_{\rm HS}^2 .}
~~~

First split the squared length in the numerator of the coefficient as

~~~math
 \frac{x_a^2+x_b^2-2x_ax_b\cos\delta}{\sin^2\delta}
 =\frac{(x_a-x_b)^2}{4\sin^2(\delta/2)}
 +\frac{(x_a+x_b)^2}{4\cos^2(\delta/2)} .
~~~

The two terms have equal integrals after multiplication by $`m_a^2m_b^2`$, by shifting $`b`$ through a half-turn. Use $`\csc^2=1+\cot^2`$, $`\int xm^2=0`$ and $`x^2m^2=m^2-1`$. The part with the cotangent is the squared kernel norm, giving

~~~math
 P=A-\tfrac12\|B\|_{\rm HS}^2
  =A-\|Be\|_2^2-\|BE\|_{\rm HS}^2 .
~~~

The second equality uses the two adjoint parity blocks of $`B`$, which have the same Hilbert–Schmidt norm.

It remains to find $`\|Be\|^2`$. Write $`u=m+t`$, $`v=m-t`$, so $`uv=1`$. The operator $`K=M_u H M_v=N+B`$ is similar to $`H`$, and $`K^2=-I+u\otimes v`$. Here $`u\otimes v`$ takes $`g`$ to $`u\langle v,g\rangle`$, using the real inner product or its complexification. Taking the self-adjoint part gives

~~~math
 B^2+N^2=-I+\tfrac12(u\otimes v+v\otimes u).
~~~

Since $`\langle u,e\rangle=\langle v,e\rangle=\sqrt A`$, evaluation at $`e`$ yields $`\|Be\|^2-\|Ne\|^2=A-1`$. Substitution proves the identity.

## Higher harmonics and equality

Let $`E_0`$ project onto the mean-zero even functions. The operator $`M_{1/m}`$ is a contraction and maps the range of $`E_0`$ into the range of $`E`$. Therefore

~~~math
 \|BE\|_{\rm HS}^2\ge
 \|M_{1/m} B E M_{1/m} E_0\|_{\rm HS}^2
 =\|[M_x,H]E_0\|_{\rm HS}^2
 =2\sum_{|j|\ge3}(|j|-1)|\widehat x_j|^2 .
~~~

For the last equality use the Fourier basis. An input of nonzero even frequency $`k`$ and an output of odd frequency $`k+j`$ give a squared matrix entry of $`4|\widehat x_j|^2`$ when their signs differ and zero otherwise. There are $`(|j|-1)/2`$ such inputs for each odd $`j`$. This proves the stated quantitative inequality.

If $`P=1`$, only the first harmonics survive. Thus $`x_a=R\cos(a-a_0)`$, with $`0\le R\lt1`$, which is the round profile at latitude $`\arccos R`$. Conversely for this profile the coefficient factors as $`p_{ab}=g_a g_b`$ with $`g_a=\sqrt{1-R^2}/(1-R^2\cos^2(a-a_0))`$. The tangent substitution on a quadrant gives $`\int g\,d\mu=1`$, and hence $`P=1`$.

For the sharp coefficient take $`x=\varepsilon\cos(ja)`$ with fixed odd $`j\ge3`$. At sufficiently small amplitude $`F=\arcsin x`$ is admissible. With $`v_0=\cos(ja)`$, one has $`m=1+O(\varepsilon^2)`$, $`e=1+O(\varepsilon^2)`$, $`Ne=O(\varepsilon^2)`$ and $`B=\varepsilon[M_{v_0},H]+O_{\rm HS}(\varepsilon^3)`$. The last estimate follows by multiplying the fixed Hilbert–Schmidt commutator by $`m`$ on each side. The projection $`E`$ differs from $`E_0`$ in operator norm by $`O(\varepsilon^2)`$. The sum of squares therefore gives $`1-P=2\sum_{|k|\ge3}(|k|-1)|\widehat x_k|^2+O(\varepsilon^4)`$.

## Consequence for actual fillings

On a filling take the antipodal half-distance differences $`F_a`$. Write $`D(x)=2\sum_{|j|\ge3}(|j|-1)|\widehat{\sin F(x)}_j|^2`$ at each surface point. Then, in every genus,

~~~math
 \mathrm{Area}(M)\ge4+\int_M D(x)\,dA(x).
~~~

To include possible boundary-valued profiles, first replace $`F_a`$ by $`F_a^{(r)}=\arcsin(r\sin F_a)`$ for $`0\lt r\lt1`$. This scalar map has Lipschitz constant at most one. Its boundary loop is exactly the round latitude with horizontal radius $`r`$. The normalized Züst form has action $`2\pi(1-\sqrt{1-r^2})`$ on that loop by Stokes and its round tangential density one. On the filling each determinant of two coordinate gradients has magnitude at most one. The normalized evaluation is thus bounded above by $`(\pi/2)P\le(\pi/2)(1-r^2 D(x))`$. Integration followed by $`r\uparrow1`$ gives the result. The direct Stokes argument integrates the bounded pairwise coefficients on each two-coordinate plane at fixed $`r\lt1`$. [Züst, §§3.2–3.4](https://arxiv.org/pdf/2104.04498)

For example, at the threefold profile $`F(a)=\arcsin(\cos 3a)/3`$, the third and ninth harmonics alone bound the raw planar comass by **1.012162476543**, below the $`2\pi/6.15`$ target budget, for every choice of the gradients there. For positive odd $`k`$ the complex coefficient at $`3k`$ is $`3\sqrt3/[\pi(9k^2-1)]`$. This follows by twice integrating $`\sin(\pi/6-u/3)\cos(ku)`$ by parts on $`[0,\pi]`$. Keeping 25 positive frequencies gives **1.003267952375**. In contrast, a profile approaching a single boundary triangle can lose little in these linear Fourier modes and still give a large planar evaluation. The next note computes this limit and tests candidate changes to the kernel. [Analytic comass test](issue163_zust_angles.md) · [Rational replay](issue163_zust_check.py)
