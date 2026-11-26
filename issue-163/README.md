# Progress on circle filling area

For every compact connected orientable Riemannian surface whose single boundary component is an isometrically embedded intrinsic circle of length $2\pi$,

```math
 \mathrm{Area}(M)\ge \frac{4900807299305452903120181318626856678763424416160470713006969}
 {7934171039896083567183835951925211702220800000000000000000000}\pi^2
 >6.096292737690900167 .
```

Averaging the 112-pair grid over its rotations forces the region with a high anchor to have more than 1.491567 times the area required by the adjacent-pair projection. The unused trace from the previous 58 matrix checks then gives the displayed bound. The underlying signed correction uses the prescribed flux of the other distance coordinates along each high anchor's levels. [Compulsory area and new bound](issue163_anchor_occupation.md) · [Signed correction and integer replay](issue163_anchor.md)

Two of the comass comparisons would require different values for the same gradient vector to attain their separate bounds. Charging the resulting squared error gave the previous bound of 6.095910645232136335 with twelve matrix witnesses. Any filling below $6.15$ must also have weighted root mean square directional imbalance below $0.132362$. A small quadrature gives about $0.156$ on the round hemisphere. A uniform lower estimate for this imbalance on putative smaller fillings remains open. [Proof, exact replay and hemisphere test](issue163_comass_residual.md)

Along the levels of one distance coordinate, other coordinates with the same boundary increment must have equal integrated transverse derivatives. The published near-maximizer gives approximately 0.159 and 1.000 for two such derivatives. Two corrections exploiting this discrepancy give raw comass at most **0.9909 throughout a neighborhood of every grid anchor**, below the 0.99120137 budget needed globally for 6.15. Moving the scalar profile farther into the same cell restores a limiting value above 0.999701. [Slice identity, local theorem and obstruction](issue163_slice_comass.md)

Every filling has more than **1.303938** area within distance 0.22 of its boundary. On this metric collar a trace-weighted RMS directional imbalance of 0.30 would give area above **6.155949**. On the round hemisphere a small quadrature gives 0.3296–0.3318. The all-genus collar area estimate follows by cutting and capping level sets. The uniform lower bound on directional imbalance is open. [Proof and four collar tests](issue163_metric_collars.md)

The earlier detour comparison retains at least 95 percent of the earlier diagonal penalty for excess length of antipodal routes. In a filling of area below $6.15$, pairs for which both anchors are farther than $\pi/2$ from the point can carry less than $0.879853$ percent of the diagonal weight for the clipped profile. [Distance comparison](issue163_detour_comparison.md)

On one current matrix the semidefinite relaxation admits a value above $0.9999998$, while planar gradients give at most $0.9997999$. In a neighboring chamber an explicit planar test survives even when routes through the test patch are arbitrarily close to shortest for every boundary label. It keeps global rescaling of this calibration below $6.09774$. The same construction realizes the continuum obstruction to the proposed form with action $6.22$ on genuine fillings. [Planar comparison](issue163_planar_comass.md) · [Short routes and tests on actual fillings](issue163_short_routes.md)

A separate shortest-path obstruction applies in every positive genus. For each fixed anchor the squared gradient of its antipodal distance difference must drop below $1/2+\eta$ on a set of positive area for every $`\eta\gt 0`$. Conversely, any finite admissible profile and planar gradients can be approximated on a small patch with arbitrarily small added area. Together these results distinguish an impossible global occupation from a permissible local test. [Geometric proofs](issue163_gradient_constraints.md)

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
| Planar phase comparison on the mandatory adjacent-anchor regions | $6.095906676681434095$ |
| Separate chamber gains with the detour penalty retained | $6.095909909027119498$ |
| Shared gradient vector in the planar comass comparisons | $6.095910645232136335$ |
| Signed correction using the levels of each high anchor | $6.096286779581369797$ |
| High-anchor area forced by rotation over the metric collar | **$6.096292737690900167$** |

The 224-point construction uses signed changes in 65 endpoint coefficients, three positive increments after doubling, and an average of two Fourier corrections supported away from those increments. The integer replays check the five archived input hashes, the finite extension on 214,058 terminal cells, all 1,898,400 rooted children at 224, and the additional Fourier action. The transported finite theorem supplies the original coverage and PSD certificates. The Lean development verifies the earlier Fourier result. [Combined proof and replay](issue163_combined.md) · [Signed field](issue163_reweighted_field.md) · [Earlier Lean development](https://github.com/lowrank/gromov-filling-lower-bound)

Two saturated profiles rule out further gains at every subsequent doubling with the same inheritance and absolute edgewise trace charges. This includes signed increments, since replacing each by its absolute value preserves those charges and weakly increases the boundary action. The fixed shell-density rule for that construction has an upper bound of $6.091188129791$. At 112 points, any real rescaling of the final signed update from the three-coefficient checkpoint gives at most $6.091183831488$ with independent diagonal PSD bounds. These are ceilings on specified constructions. The full filling-area problem remains open. [Dyadic optimality proof](issue163_dyadic_lift.md) · [Coefficient ceilings](issue163_reweight_ceiling.md)

## Progress toward 6.15

The total pair weight of Züst's continuum form is at most $`\pi^2/2`$, with equality precisely on open-hemisphere profiles. A Hilbert-transform sum of squares proves the estimate in Question 2 of the 2021 paper and charges every higher odd Fourier mode of the sine profile. For the threefold triangular profile it bounds the raw planar comass by 1.003268. [Proof of the sharp weight and Fourier deficit](issue163_zust_mass.md)

An explicit profile with two perpendicular gradient groups makes the original form's raw comass tend to 1.103708. Even arbitrary signed symmetric weights depending on the inferred angle between the two gradients have a certified area ceiling of **5.843897829067**. A change depending also on the external label separation has action above 6.170387 and passes every round profile and the limiting test. A 32-by-32 rational calculation detects excessive comass at a finite width. [Analytic obstruction, modified form and finite test](issue163_zust_angles.md)

Even arbitrary closed comass-one changes at both shallow and deep distance profiles have boundary action at most **6.148325785606** if the normalized free field is kept at profile depths between $`h=\pi/112`$ and $`10h`$. Keeping it through $`12h`$ lowers the ceiling to **6.141013708383**. A calibration reaching 6.15 must gain at least **0.008986291617** on one explicit cylinder in that band. Two loop integrals of its primitive suffice to test this requirement. [Comparison surface and three depth tests](issue163_middle_band.md)

Two explicit planar profiles put a ceiling of **6.097700344081** on every nonnegative mixture of one-anchor tents through width $`38h`$, even with arbitrary nonnegative rescaling of the bisected-gap field. At the original scale, allowing all real widths through $`\pi`$ gives **6.098884806758**. Signed coefficients and corrections depending jointly on several coordinates can be tested on the same profiles. [Proof and two-profile replay](issue163_anchor_cone.md)

A flat comparison surface puts an upper bound of **6.107523028** on the action of any closed planar-comass-one calibration that agrees with the normalized free field outside the adjacent-anchor regions of the 112-pair grid. Widening the aligned gaps fourfold still gives a ceiling of **6.142450184**. Using twice the original gap width at every rotation gives **6.145244034**. The proof integrates an explicit field over small polygons. [Support conditions, comparison surfaces and exact check](issue163_flat_collar.md)

A geometric comparison reaches **$6.155019283$** in every genus when the orientation double cover of the antipodal quotient admits a compatible hyperelliptic involution of singular-value ratio at most $1.6$. The same argument gives **$2\pi$** if every angle-distorted region has singular-value ratio at most $3$ and the two exchanged area densities differ by a factor of at least $4$. On paired flat collars, spreading a fixed twist uniformly minimizes the cost among all shear interpolations. The proof reduces the numerical test to one scalar variable. Finding a sufficiently inexpensive involution on every smaller filling remains open. [Proof, collar experiment and exact inequalities](issue163_symmetry.md)

A geometric genus-reduction estimate reaches **$6.16$** for fillings admitting a disjoint system of curves that cuts the genus to at most one, with total cut length at most $2$ and each curve at distance at least $1.54$ from the external boundary. At depth $\pi/2$ it yields the sharp **$2\pi$** for any cut lengths. At arbitrary depths the estimate still gives $6.15$ when $`\sum_j\ell_j^2\le\pi(2\pi-6.15)`$. For an interior homological systole the two cut copies can be capped independently. Thin spherical lunes can retain the needed distances even at shallow depth. Finding a sufficiently inexpensive cut system in every putative smaller filling is open. [Proof, cap costs and intrinsic cut criterion](issue163_genus_reduction.md)

Recomputing the 224-point diagonal witnesses for all **666 arbitrary signed endpoint coefficients** gives a certified method ceiling of $6.137425468261$. Even the less restrictive independent planar-gradient model has ceiling $6.147258810636$. Both allow the parent to be scaled and include the prior Fourier correction. A separate test on the genuine hemisphere gives $6.145994304998$ for arbitrary calibrated changes supported only on the endpoint bands from 448 onward. Coordinated changes from 224 onward have the weaker geometric ceiling $6.168642868649$. [Endpoint proofs and exact replays](issue163_endpoint_limits.md)

A closed interior Fourier correction now has raw boundary action at least $6.22035659546\ldots$. Its comass is at most one on the hemisphere, on every zero-output profile, and on two explicit off-hemisphere families throughout radii $1$ to $100$. A rotating family joining two explicit profiles forces the full independent-gradient comass above $491$ for every permitted choice of cutoffs. This rules out the proposed $1.0114$ certificate for that primitive. [Interior construction and transition obstruction](issue163_interior_candidate.md#a-rotating-path-obstruction)

In the continuum, a rotating family of folded triangle profiles puts an upper bound of $5.786100794611$ on the single gnomonic Fourier coordinate with arbitrary target density under independent planar tests. A Lorentz-equivariant center which also uses a scalar normalization has the analytic ceiling $6.07098103\ldots$ under those tests. These calculations identify explicit profiles against which to check other interior corrections. [Continuum tests and replay](issue163_continuum_tests.md)

The five hash-pinned finite inputs are included in [issue163_inputs](issue163_inputs/). From the repository root, enter this directory with <code>cd issue-163</code>. The first command verifies the new lower bound. The second checks the continuum comparisons. The next two check the middle-depth requirement and the ceilings on nonnegative corrections.

~~~sh
node issue163_anchor.cjs issue163_inputs
python3 issue163_zust_check.py
node issue163_middle_band.cjs issue163_inputs
node issue163_anchor_cone.cjs issue163_inputs
node issue163_planar_comass.cjs issue163_inputs
node issue163_comass_residual.cjs
node issue163_flat_collar.cjs issue163_inputs
node issue163_angular_energy.cjs issue163_inputs
node issue163_sampled_disk.cjs
node issue163_midpoint.cjs issue163_inputs
node issue163_free_field.cjs issue163_inputs
~~~
