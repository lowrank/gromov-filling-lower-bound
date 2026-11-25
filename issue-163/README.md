# Progress on circle filling area

For every compact connected orientable Riemannian surface whose single boundary component is an isometrically embedded intrinsic circle of length $2\pi$,

```math
 \mathrm{Area}(M)\ge \frac{737877064811692678202731938521}{1194666547200000000000000000000}\pi^2+2^{-1372}
 >6.095889052386098292 .
```

The bisected-gap calibration gives the displayed multiple of $\pi^2$. The term $2^{-1372}$ comes from the Dirichlet energy forced by the full family of antipodal distances. The decimal remains $6.095889052386098292$ to 18 places when rounded down. The same argument bounds the improvement from every uniform angular split of this field by $2\times10^{-25}$. The unconditional $6.15$ target remains open. [Energy proof and exact replay](issue163_angular_energy.md) · [Bisected-gap proof](issue163_midpoint.md)

There are smooth disks passing all 112 sampled antipodal tests with an unsampled pair at distance below $\pi-0.0116$. For 15 equally spaced tests the construction already has area below $6.15$. This gives a geometric example of the information lost by sampling. [Construction and area calculation](issue163_sampled_disk.md) · [Repairing finite-test fillings](issue163_sampling.md)

| Construction | Certified area lower bound |
|---|---:|
| Annular Fourier correction on the original transported field | $6.086380541911894628$ |
| Signed coefficients and scalar reweighting at 112 anchor pairs | $6.091181885431729436$ |
| Optimal nonnegative endpoint lift for that field at 224 pairs | $6.091181920033558876$ |
| Lift plus two rotated Fourier shell corrections | $6.091188129789057449$ |
| Joint changes to the four finite levels | $6.095000609501857507$ |
| Closed correction on each boundary gap and its two halves | $6.095889052386098292$ |
| Full antipodal traces and angular difference energy | Exact bisected-gap bound plus $2^{-1372}$ |

The 224-point construction uses signed changes in 65 endpoint coefficients, three positive increments after doubling, and an average of two Fourier corrections supported away from those increments. The integer replays check the five archived input hashes, the finite extension on 214,058 terminal cells, all 1,898,400 rooted children at 224, and the additional Fourier action. The transported finite theorem supplies the original coverage and PSD certificates. The Lean development verifies the earlier Fourier result. [Combined proof and replay](issue163_combined.md) · [Signed field](issue163_reweighted_field.md) · [Earlier Lean development](https://github.com/lowrank/gromov-filling-lower-bound)

Two saturated profiles rule out further gains at every subsequent doubling with the same inheritance and absolute edgewise trace charges. This includes signed increments, since replacing each by its absolute value preserves those charges and weakly increases the boundary action. The fixed shell-density rule for that construction has an upper bound of $6.091188129791$. At 112 points, any real rescaling of the final signed update from the three-coefficient checkpoint gives at most $6.091183831488$ with independent diagonal PSD bounds. These are ceilings on specified constructions. The full filling-area problem remains open. [Dyadic optimality proof](issue163_dyadic_lift.md) · [Coefficient ceilings](issue163_reweight_ceiling.md)

## Progress toward 6.15

A geometric comparison reaches **$6.155019283$** in every genus when the orientation double cover of the antipodal quotient admits a compatible hyperelliptic involution of singular-value ratio at most $1.6$. The same argument gives **$2\pi$** if every angle-distorted region has singular-value ratio at most $3$ and the two exchanged area densities differ by a factor of at least $4$. On paired flat collars, spreading a fixed twist uniformly minimizes the cost among all shear interpolations. The proof reduces the numerical test to one scalar variable. Finding a sufficiently inexpensive involution on every smaller filling remains open. [Proof, collar experiment and exact inequalities](issue163_symmetry.md)

A geometric genus-reduction estimate reaches **$6.16$** for fillings admitting a disjoint system of curves that cuts the genus to at most one, with total cut length at most $2$ and each curve at distance at least $1.54$ from the external boundary. At depth $\pi/2$ it yields the sharp **$2\pi$** for any cut lengths. At arbitrary depths the estimate still gives $6.15$ when $\sum_j\ell_j^2\le\pi(2\pi-6.15)$. Finding a sufficiently inexpensive cut system in every putative smaller filling is open. [Proof, cap costs and intrinsic cut criterion](issue163_genus_reduction.md)

Recomputing the 224-point diagonal witnesses for all **666 arbitrary signed endpoint coefficients** gives a certified method ceiling of $6.137425468261$. Even the less restrictive independent planar-gradient model has ceiling $6.147258810636$. Both allow the parent to be scaled and include the prior Fourier correction. A separate test on the genuine hemisphere gives $6.145994304998$ for arbitrary calibrated changes supported only on the endpoint bands from 448 onward. Coordinated changes from 224 onward have the weaker geometric ceiling $6.168642868649$. [Endpoint proofs and exact replays](issue163_endpoint_limits.md)

A closed interior Fourier correction now has raw boundary action at least $6.22035659546\ldots$. Its comass is at most one on the hemisphere, on every zero-output profile, and on two explicit off-hemisphere families throughout radii $1$ to $100$. A rotating family joining two explicit profiles forces the full independent-gradient comass above $491$ for every permitted choice of cutoffs. This rules out the proposed $1.0114$ certificate for that primitive. [Interior construction and transition obstruction](issue163_interior_candidate.md#a-rotating-path-obstruction)

In the continuum, a rotating family of folded triangle profiles puts an upper bound of $5.786100794611$ on the single gnomonic Fourier coordinate with arbitrary target density under independent planar tests. A Lorentz-equivariant center which also uses a scalar normalization has the analytic ceiling $6.07098103\ldots$ under those tests. These calculations identify explicit profiles against which to check other interior corrections. [Continuum tests and replay](issue163_continuum_tests.md)

The five hash-pinned finite inputs are included in [issue163_inputs](issue163_inputs/). From the repository root, enter this directory with <code>cd issue-163</code>. The first two commands check the angular and disk calculations. The last two replay the underlying matrix certificates.

~~~sh
node issue163_angular_energy.cjs issue163_inputs
node issue163_sampled_disk.cjs
node issue163_midpoint.cjs issue163_inputs
node issue163_free_field.cjs issue163_inputs
~~~
