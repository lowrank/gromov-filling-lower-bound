# Progress on circle filling area

For every compact connected orientable Riemannian surface whose single boundary component is an isometrically embedded intrinsic circle of length $2\pi$,
$$
 \operatorname{Area}(M)\ge \frac{617166391098385050}{10^{18}}\pi^2
 >6.091188129789057449 .
$$
The November 25 note gave $6.082181436172889493\ldots$. The improvement in the certified constant exceeds $0.009006693616167956$. The new inequality applies in every genus. The conjectural lower bound is $2\pi$.

| Construction | Certified area lower bound |
|---|---:|
| Annular Fourier correction on the original transported field | $6.086380541911894628$ |
| Signed coefficients and scalar reweighting at 112 anchor pairs | $6.091181885431729436$ |
| Optimal nonnegative endpoint lift for that field at 224 pairs | $6.091181920033558876$ |
| Lift plus two rotated Fourier shell corrections | **$6.091188129789057449$** |

The last construction uses signed changes in 65 endpoint coefficients, three positive increments after doubling, and an average of two Fourier corrections supported away from those increments. The integer replays check the five archived input hashes, the finite extension on 214,058 terminal cells, all 1,898,400 rooted children at 224, and the additional Fourier action. The transported finite theorem supplies the original coverage and PSD certificates. The Lean development verifies the earlier Fourier result. [Combined proof and replay](issue163_combined.md) · [Signed field](issue163_reweighted_field.md) · [Earlier Lean development](https://github.com/lowrank/gromov-filling-lower-bound)

Two saturated profiles rule out further gains at every subsequent doubling with the same inheritance and absolute edgewise trace charges. This includes signed increments, since replacing each by its absolute value preserves those charges and weakly increases the boundary action. The fixed shell-density rule for the last row has an upper bound of $6.091188129791$. At 112 points, any real rescaling of the final signed update from the three-coefficient checkpoint gives at most $6.091183831488$ with independent diagonal PSD bounds. These are ceilings on specified constructions. The full filling-area problem remains open. [Dyadic optimality proof](issue163_dyadic_lift.md) · [Coefficient ceilings](issue163_reweight_ceiling.md)

One open calculation is to allow signed coefficient changes at 224 points and solve for new PSD diagonals on the two saturated profiles. A signed perturbation can cancel an existing matrix entry. The fixed rule charges its absolute value edge by edge and loses this cancellation. A certificate using it would also have to check every other rooted profile and its boundary action.
