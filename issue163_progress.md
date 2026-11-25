# Progress on circle filling area

For every compact connected orientable Riemannian surface whose single boundary component is an isometrically embedded intrinsic circle of length $2\pi$,
$$
 \mathrm{Area}(M)\ge \frac{316186938521718142086885116509}{511999948800000000000000000000}\pi^2
 >6.095000609501857507 .
$$
This raises the previous displayed constant by $0.003812479712800058$. The November 25 note gave $6.082181436172889493\ldots$. The conjectural lower bound is $2\pi$. The new finite proof rechecks all 214,058 matrices with integer arithmetic. [Proof and replay](issue163_free_field.md)

| Construction | Certified area lower bound |
|---|---:|
| Annular Fourier correction on the original transported field | $6.086380541911894628$ |
| Signed coefficients and scalar reweighting at 112 anchor pairs | $6.091181885431729436$ |
| Optimal nonnegative endpoint lift for that field at 224 pairs | $6.091181920033558876$ |
| Lift plus two rotated Fourier shell corrections | $6.091188129789057449$ |
| Joint changes to the four finite levels | **$6.095000609501857507$** |

The 224-point construction uses signed changes in 65 endpoint coefficients, three positive increments after doubling, and an average of two Fourier corrections supported away from those increments. The integer replays check the five archived input hashes, the finite extension on 214,058 terminal cells, all 1,898,400 rooted children at 224, and the additional Fourier action. The transported finite theorem supplies the original coverage and PSD certificates. The Lean development verifies the earlier Fourier result. [Combined proof and replay](issue163_combined.md) · [Signed field](issue163_reweighted_field.md) · [Earlier Lean development](https://github.com/lowrank/gromov-filling-lower-bound)

Two saturated profiles rule out further gains at every subsequent doubling with the same inheritance and absolute edgewise trace charges. This includes signed increments, since replacing each by its absolute value preserves those charges and weakly increases the boundary action. The fixed shell-density rule for that construction has an upper bound of $6.091188129791$. At 112 points, any real rescaling of the final signed update from the three-coefficient checkpoint gives at most $6.091183831488$ with independent diagonal PSD bounds. These are ceilings on specified constructions. The full filling-area problem remains open. [Dyadic optimality proof](issue163_dyadic_lift.md) · [Coefficient ceilings](issue163_reweight_ceiling.md)

## Progress toward 6.15

A geometric comparison reaches **$6.155019283$** in every genus when the orientation double cover of the antipodal quotient admits a compatible hyperelliptic involution of singular-value ratio at most $1.6$. The same argument gives **$2\pi$** if every angle-distorted region has singular-value ratio at most $3$ and the two exchanged area densities differ by a factor of at least $4$. On paired flat collars, spreading a fixed twist uniformly minimizes the cost among all shear interpolations. The proof reduces the numerical test to one scalar variable. Finding a sufficiently inexpensive involution on every smaller filling remains open. [Proof, collar experiment and exact inequalities](issue163_symmetry.md)

A geometric genus-reduction estimate reaches **$6.16$** for fillings admitting a disjoint system of curves that cuts the genus to at most one, with total cut length at most $2$ and each curve at distance at least $1.54$ from the external boundary. At depth $\pi/2$ it yields the sharp **$2\pi$** for any cut lengths. At arbitrary depths the estimate still gives $6.15$ when $\sum_j\ell_j^2\le\pi(2\pi-6.15)$. Finding a sufficiently inexpensive cut system in every putative smaller filling is open. [Proof, cap costs and intrinsic cut criterion](issue163_genus_reduction.md)

Recomputing the 224-point diagonal witnesses for all **666 arbitrary signed endpoint coefficients** gives a certified method ceiling of $6.137425468261$. Even the less restrictive independent planar-gradient model has ceiling $6.147258810636$. Both allow the parent to be scaled and include the prior Fourier correction. A separate test on the genuine hemisphere gives $6.145994304998$ for arbitrary calibrated changes supported only on the endpoint bands from 448 onward. Coordinated changes from 224 onward have the weaker geometric ceiling $6.168642868649$. [Endpoint proofs and exact replays](issue163_endpoint_limits.md)

A closed interior Fourier correction now has raw boundary action at least $6.22035659546\ldots$. Its comass is at most one on the hemisphere, on every zero-output profile, and on two explicit off-hemisphere families throughout radii $1$ to $100$. A rotating family joining two explicit profiles forces the full independent-gradient comass above $491$ for every permitted choice of cutoffs. This rules out the proposed $1.0114$ certificate for that primitive. [Interior construction and transition obstruction](issue163_interior_candidate.md#a-rotating-path-obstruction)

In the continuum, a rotating family of folded triangle profiles puts an upper bound of $5.786100794611$ on the single gnomonic Fourier coordinate with arbitrary target density under independent planar tests. A Lorentz-equivariant center which also uses a scalar normalization has the analytic ceiling $6.07098103\ldots$ under those tests. These calculations identify explicit profiles against which to check other interior corrections. [Continuum tests and replay](issue163_continuum_tests.md)

The five hash-pinned finite inputs are included in the branch directory named **issue163_inputs**. From the branch root run the small symmetry test and the all-genus finite certificate with

~~~sh
python3 issue163_symmetry.py
node issue163_free_field.cjs issue163_inputs
~~~
