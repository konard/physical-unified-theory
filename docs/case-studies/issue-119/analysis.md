# Argument audit and proof obligations

The paper’s four-dimensional conclusion depends on constructing the continuum state and evolution, proving finite-clock states exist, and identifying closed gluing with exact limits of finite cuts. The classical bound and the open gluing estimate can be checked without those later steps. The dependency order below follows what each result uses.

| Paper scope | Independently checked consequence or test | Acceptance criterion for the physical claim |
| --- | --- | --- |
| §2, (2.4)–(2.17), JT with a massless scalar | The same clock probability can occur for infinitely many orthogonal states. A positive weight bounded away from zero gives an unbounded diagonal trace. | Derive the canonical pairs, boundary charge, matter zero-mode split and unitary evolution for the prescribed cap data. Compare the resulting clock and corner observables with (2.4) and (2.15). |
| §3 and Appendices A–B, constrained BF, null constraints, edge modes and matching | The Raychaudhuri reduction gives the cap clock, and its affine normalization and classical moment bound check. The shear-free spherical example saturates the bound. | Define the invertible tetrad sector and orientations. Derive the boundary and corner variations, prove constraint propagation for declared regularity and corner compatibility, and build the reduced symplectic form, brackets and Hamiltonian. Check matching by composing two classical solutions and comparing their reduced observables and symplectic data. |
| §4.1–4.2, observable algebra and GNS | The open Hilbert-space gluing identity has a Lean proof for any Hilbert basis and normalizable states. | Give a nontrivial continuum representation of the algebraic relations (4.2), positive state, fixed-area sectors, implementable boosts, unitary time translations and the area-band rank-one construction needed for (4.17). Verify every operator equality on a declared domain. |
| §4.3 and Appendix C, area and clock | The scalar resolvent bound checks in both kernels. The form-domain counterexample shows why finite-cut bounds require a separate continuum argument. | Construct (4.24)–(4.27) with specified regulators, prove monotone closed-form convergence on a useful domain and prove strong commutation with the area projections. Compare the two caps when both enter the diamond restriction. |
| §4.4, open gluing and selected graviton channel | The Hilbert-space bound (4.29)–(4.30), finite-cut norm error (4.31), fixed-area radial absolute convergence and the divergence of the harmonic coefficient (4.34) are checked. A bounded experiment reproduces the distinct cutoff behavior. | Recover the actual transition operators from the reduced action, prove admissible cut independence and determine which amplitude families permit a uniform continuum or combined angular and radial limit. |
| §5.1, allowed states | Finite cutoffs alone do not preserve nonzero weight on the form domain. | For the specified preparation, prove nonzero $P_M\Omega$ or construct a nonzero vector in the clock form domain by other means. For the limit in (5.19), prove $P_M\Omega=\Omega$. |
| §5.2 and Appendix D.2–D.3, finite dimension and spectra | Bounded open gluing with divergent closed trace is checked on an explicit Hilbert space. The sign contradiction (5.38) and trace bound (D.47) are valid with their respective convergence and positivity assumptions. The boost suppression factor checks in both kernels. | Establish an exact uncut amplitude and its convergence from the cofinal closed cuts independently of trace finiteness. Control the graviton estimate and the sign for the specified preparation beyond fixed-order perturbation. Alternatively prove a positive replica limit in the same net. Derive the area multiplicities and AdS heat trace afterwards. |
| §5.3 and Appendix D.1, entropy | The Gibbs identity at finite rank and the pure-gravity arithmetic $q=257/302$ giving $106/45$ in the fixed-mass convention check. The external one-loop coefficient agrees in that convention. | Establish the finite trace first. Prove the large-area limit of the clock moment and spectral count. Compare the graviton and ghost determinants with the same zero modes, boundary conditions, renormalization convention, ensemble and orders of limits. |
| §5.4, topology and null states | The proposed topology identification is a Gram-matrix and product-state completeness argument conditional on closed gluing. | Define the admissible fillings and physical norm, establish the tensor-product gluing and convergence, and verify the norm of the alleged null combination. Check the two-sided correlators in the specified boundary state before extrapolating. |
| §6, classical and one-loop Einstein equations | Lean checks the finite covariance contraction given the second variation of a smooth family of classical solutions. | Prove existence and smooth dependence of the characteristic solution map, the field-redefinition identities and the semiclassical expansion. Construct the reduced causal propagator and renormalized coincident quadratic source and verify the Bianchi and retarded identities. |
| Appendix E, Lorentzian and Euclidean amplitude axioms | The equivalence is conditional on positivity, band-restricted finiteness and specified properties of the analytically continued cylinder. | Construct the exact closed functional with all condition 5 pairings finite before claiming the first-order theory realizes the axioms. Check the analytic continuation, Euclidean reflection positivity, norm equality and trace correspondence on a common domain. |

## Classical clock and the JT control

In JT, the metric is locally AdS₂ under the stated conditions. For a positive AdS length the expression in (2.4c) increases with the proper width. The matter flux instead changes the dilaton through (2.5). With fixed corner dilaton and a fixed normalized matter vector, choose a normalized cap wavefunction $h$ with an absolutely continuous clock density on a finite interval. The cumulative distribution $F(u)=\int_0^u|h(v)|^2\,dv$ sends that clock measure to the uniform law on $[0,1]$. Multiplying $h$ by $e^{2\pi i n F(u)}$ leaves the clock probabilities unchanged. Orthogonality follows from the Fourier integral in (2.14). The positive constant boost weight therefore gives a diagonal lower bound independent of the clock cutoff. This checks the mechanism in the two-dimensional example, conditional on its proposed Hilbert representation. [JT calculation (2.4)](https://arxiv.org/html/2611.34924v1#S2.E4) · [JT states (2.14)](https://arxiv.org/html/2611.34924v1#S2.E14) · [JT trace (2.17)](https://arxiv.org/html/2611.34924v1#S2.E17)

One can derive the clock directly from the null geodesic. For the right
generator $\dot\tau=\dot\sigma$, the conformal metric gives
$\ddot\sigma+2\tan\sigma\,\dot\sigma^2=0$, where dots denote affine
derivatives. The normalization at the tip sets $\dot\sigma=\cos^2\sigma/L_{\mathrm{AdS}}$.
Therefore $u=L_{\mathrm{AdS}}\tan\sigma$ and integrating the spatial line
element gives $\lambda=L_{\mathrm{AdS}}\operatorname{arsinh}(\tan\sigma)$.
With $x=w/(2L_{\mathrm{AdS}})$, the cap-normalized reading divided by
$L_{\mathrm{AdS}}$ is
$x\int_\epsilon^1 \cosh(xz)/\cosh(\epsilon x)\,dz$.
For $z\ge\epsilon>0$ the logarithmic derivative of the integrand is
$z\tanh(xz)-\epsilon\tanh(\epsilon x)\ge0$. Its positivity and the
prefactor $x$ imply strict increase for $x\ge0$. On this fixed geometry, the
null component of the dilaton equation gives $\Phi''=-\varphi'^2$. Twice
integrating with matched initial dilaton and slope gives (2.5), and a constant
scalar gradient $j$ gives the explicit change $-j^2 u_*^2/2$.
[Metric and cap clock (2.3)–(2.4)](https://arxiv.org/html/2611.34924v1#S2.E4) · [Null constraint (2.5)](https://arxiv.org/html/2611.34924v1#S2.E5)

The scalar matter terms in (2.7) determine the quoted zero-mode momentum.
For the joint constant shift $S\varphi_i=S\varphi_0=1$ with $S\pi_\varphi=0$,
the contraction of $\delta\Theta$ with $S$ is $-\delta p_1$, where
$p_1=\int_{\Sigma_0}\pi_\varphi\,dx+\sum_i\int_\epsilon^1\partial_v\varphi_i\,dv$.
The endpoint expression in (2.11) follows from the fundamental theorem of
calculus. The cap average of $\varphi_0$ against a unit-integral weight changes
at rate one under $S$, so it is conjugate to $p_1$. For a shift of only a
corner rapidity $\Gamma_i$, the analogous contraction is
$-\delta\mathscr K_i$. A compactly supported generator shift
$X_f\varphi_i=f/2$ gives
$\Omega(X_f,Y)=-\int f\,\partial_v(Y\varphi_i)\,dv=-Yj_i(f)$ by integration
by parts. This fixes the classical bracket of two currents on the same
generator to $\frac12\int f g'\,dv$, with zero bracket across the two
generators. The calculation uses the cap symplectic potential and the
support condition on the shifts. Deriving the complete potential from the
action and constructing the evolution on the full Hilbert representation
remain separate acceptance checks. [Symplectic potential (2.6)–(2.7)](https://arxiv.org/html/2611.34924v1#S2.E7) · [Current and zero mode (2.10)–(2.11)](https://arxiv.org/html/2611.34924v1#S2.E10)

### JT clock momentum at fixed matter and corner charges

In the paper's global coordinates, the nonzero Christoffel symbols are
$\Gamma^\sigma_{\tau\tau}=\Gamma^\sigma_{\sigma\sigma}
=\Gamma^\tau_{\tau\sigma}=\Gamma^\tau_{\sigma\tau}=\tan\sigma$.
For $f=h(\tau)\sec\sigma$ with $h''=-h$, the covariant Hessian has diagonal
entries $-f\sec^2\sigma,f\sec^2\sigma$ and zero mixed entries. For
$f=\tan\sigma$, the same formula follows from
$\partial_\sigma f=\sec^2\sigma$ and
$\partial_\sigma^2 f=2\tan\sigma\sec^2\sigma$.
These solve (2.8).
The value and gradient at $(\tau,\sigma)=(0,0)$ uniquely determine a solution
on the connected diamond. Along a smooth curve (2.8) gives a linear
first-order system for $(f,\nabla f)$, which has a unique solution for its
initial data. The three displayed solutions supply independent initial data.
The two corner conditions at $(0,\pm\sigma_S)$ set the coefficients of
$\cos\tau\sec\sigma$ and $\tan\sigma$ to zero for $\sigma_S>0$.
Thus $\Delta\Phi=c\sin\tau\sec\sigma$ is the full homogeneous freedom with
matter and both corner charges fixed. [Dilaton equation (2.8)](https://arxiv.org/html/2611.34924v1#S2.E8)

For the tetrad in (2.9), the torsion-free connection is
$\omega^{01}=\tan\sigma\,d\tau$. The constraint gives
$\Delta Y_0=-c\sin\tau\tan\sigma/L_{\mathrm{AdS}}$ and
$\Delta Y_1=-c\cos\tau/L_{\mathrm{AdS}}$.
Under a displacement at fixed contour coordinates, varying the pulled-back
tetrad produces derivatives $d(\delta\tau)$ and $d(\delta\sigma)$.
Substitute the shifts into
$\Delta Y_\mu\delta e^\mu+\Delta\Phi\,\delta\omega^{01}$.
The $d(\delta\tau)$ terms cancel, and the $\delta\sigma\,d\tau$ terms
combine using $\sec^2\sigma-\tan^2\sigma=1$. What remains is

$$
c\sin\tau\sec\sigma\,\delta\sigma\,d\tau
-c\cos\tau\sec\sigma\tan\sigma\,\delta\sigma\,d\sigma
-c\cos\tau\sec\sigma\,d(\delta\sigma)
=-c\,d(\cos\tau\sec\sigma\,\delta\sigma).
$$

The contributions at the cap joins cancel when the displacements match.
The two outer corners have $\tau=0$ and displacements $\pm\delta\sigma_S$,
so the integrated change is $-2c\sec\sigma_S\,\delta\sigma_S$.
The spatial length obeys $dw=2L_{\mathrm{AdS}}\sec\sigma_S\,d\sigma_S$.
Consequently $\Delta p_{u_*}=-c/[L_{\mathrm{AdS}}(du_*/dw)]$, and the
positive derivative for $w>0$ makes this shift range over $\mathbb R$.
This verifies the gravitational momentum variation in (2.9c–d) for the
specified contour. [First-order variation (2.9)](https://arxiv.org/html/2611.34924v1#S2.E9)

The clock Hilbert space in (2.13a) supports the positive multiplication
operator $u_*$. On $C_c^\infty(0,\infty)$ the formal translation generator
$-i\hbar\,d/du_*$ has deficiency indices $(1,0)$. With $\hbar>0$, the two
adjoint equations at $+i$ and $-i$ give $e^{-u_*/\hbar}$ and
$e^{u_*/\hbar}$ respectively, and only the first is square integrable.
Thus the classical momentum calculation cannot be used to generate a
unitary group of additive clock translations on this Hilbert space.
Unitary evolution in the paper's physical time requires its own
Hamiltonian and domain. [Clock representation (2.13)](https://arxiv.org/html/2611.34924v1#S2.E13)

### Four-dimensional focusing and area

For an expanding generator in vacuum, write $p=\partial_u\rho>0$, $v=\rho/\rho_S$ and $D=(\partial_v\bar q)^{AB}(\partial_v\bar q)_{AB}\ge 0$ using the induced positive transverse metric to raise indices. Substitution into (3.25f) divides by $p^2/\rho_S$ and gives $\partial_v\log p=-vD/8$. Integration from the cap gives $p=p_\epsilon e^{-\Xi}$ with $\Xi(v)=\frac18\int_\epsilon^v tD(t)\,dt$. Integrating $du/dv=\rho_S/p$ then gives the clock (3.27). Under $u\mapsto\alpha u+\beta$, the cap slope divides by $\alpha$ and the elapsed affine parameter multiplies by it. The proof requires the expanding branch, a positive cap radius fraction and absence of a caustic on the segment. [Raychaudhuri (3.25)](https://arxiv.org/html/2611.34924v1#S3.E25) · [Integrated clock (3.26)–(3.28)](https://arxiv.org/html/2611.34924v1#S3.E26)

Since $e^\Xi\ge1$, averaging $u_*(y)$ as in (3.28) gives $(1-\epsilon)A/a\le \bar u_*$, where $a=\int\rho_S d\Omega$. Cauchy–Schwarz with the round reference measure of mass $4\pi$ gives $a^2\le 4\pi A$. A reading $\bar u_*\le L$ implies $A\le 4\pi L^2/(1-\epsilon)^2$. For $\Xi=0$ and constant $\rho_S=r>0$, $a=4\pi r$, $A=4\pi r^2$ and $L=(1-\epsilon)r$ attain equality. [Area bound (5.21)](https://arxiv.org/html/2611.34924v1#S5.E21)

The operator bound can also be derived on any positive fixed-area sector
where the displayed density and focusing operators exist. Assume that the
vector field $y\mapsto\widehat\rho_S(y)\psi$ is strongly measurable on a
dense common domain and that (4.25) holds there as
$\int\|\widehat\rho_S(y)\psi\|^2d\Omega=A\|\psi\|^2$. The vector integral
$\widehat a\psi=\int\widehat\rho_S(y)\psi\,d\Omega$ satisfies
$\|\widehat a\psi\|^2\le4\pi A\|\psi\|^2$ by the triangle inequality
and scalar Cauchy–Schwarz, so it extends to a bounded positive operator
with $\widehat a^2\le4\pi A I$. For a vector in the clock form domain, the
spectral bound $e^{\widehat\Xi_y(v)}\ge I$ in (4.27) and the density
normalization applied to $\widehat a^{-1/2}\psi$ give

$$
Q[\psi]\ge (1-\epsilon) A\|\widehat a^{-1/2}\psi\|^2
\ge (1-\epsilon)\sqrt{A/(4\pi)}\|\psi\|^2.
$$

The second inequality uses spectral calculus on the positive support of
$\widehat a$. This proof also works with the nonnegative bounded focusing
cutoff of (C.11) and requires no commutation among the individual density
and focusing operators. The upper bound $e^{\Xi_*}I$ for that cutoff gives
the other side of (C.11), so the cutoff form norm is equivalent to the
complete graph norm of $\widehat a^{-1/2}$. Increasing the cutoff raises the
form, by spectral calculus for each fixed focusing operator and monotone
integration over $y$ and $v$. If the limiting clock form is closed, its spectral projection
onto $[0,L]$ within the closure of its form domain vanishes whenever the
scalar lower bound exceeds $L$. A direct integral of these sector bounds
gives (5.21d) if the clock projections act fiberwise in the area spectral
decomposition. This conclusion still requires the area decomposition, the
exact normalized density, and a nonzero surviving clock domain to describe
nontrivial states. [Ordered clock (4.25)–(4.27)](https://arxiv.org/html/2611.34924v1#S4.E25) · [Cutoff domain (C.11)](https://arxiv.org/html/2611.34924v1#A3.E11)

## Cutoffs and the continuum clock

For real $x\ge0$ and $L>0$, $x[L/(L+x)]^2\le L/4$ follows from $L(L-x)^2\ge0$. Applying it to a positive self-adjoint operator with a spectral resolution bounds the clock form energy of a resolvent-smoothed unit vector. Markov’s inequality then gives the probability bound (5.17). If the limit form is only densely defined on a proper closed subspace $M$, the spectral theorem on $M$ gives $\lim_{L\to\infty}L(L+A)^{-1}P_M\Omega=P_M\Omega$, where $A$ is its positive operator. Equation (C.13) already contains this projection. The necessary and sufficient condition for a nonzero projection at some finite threshold is $P_M\Omega\ne0$. For (5.19) the required limit projection weight is one. [Clock probability (5.17)–(5.19)](https://arxiv.org/html/2611.34924v1#S5.E17) · [Resolvent limit (C.13)](https://arxiv.org/html/2611.34924v1#A3.E13)

For a countermodel take $Q_n[\psi]=n\|\psi\|^2$ on any nonzero Hilbert space. Each form has full domain and every positive cutoff has positive normalized resolvent overlap. Their increasing limit has domain $\{0\}$. For any fixed $L>0$, the actual overlap is $L/(L+n)\to0$. Taking $L\to\infty$ first gives one for every fixed $n$, which illustrates why the order matters. This example tests the sufficiency of the cutoff and domain reasoning. To rule it out for the proposed theory one must exploit properties of its state and clock operators. Equation (5.16) compares an exact operator expression with a classical Wigner tail and is identified as heuristic in its footnote. Finiteness of the classical clock on each smooth cone and its order-by-order expansion give no uniform operator bound as the cutoff is removed. [Heuristic tail step (5.16)](https://arxiv.org/html/2611.34924v1#S5.E16)

A sufficient estimate for the stronger clock claim is $\sup_n Q_n[\Omega]\le M<\infty$ for the normalized preparation $\Omega$. Against each cutoff spectral measure, $1-L/(L+x)=x/(L+x)\le x/L$, so the resolvent deficit is bounded by $M/L$ uniformly in $n$. The finite spectral-sum version is checked in Lean. Passing to the form limit then gives unit weight as $L\to\infty$. If the first moment diverges, a uniform law for spectral tails still suffices: for any $K>0$ the deficit is bounded by $K/L+\mu_n((K,\infty))$. The corresponding acceptance test is tightness of the actual cutoff spectral measures in the specified preparation. [Clock resolvent (5.7)](https://arxiv.org/html/2611.34924v1#S5.E7) · [Resolvent limit (C.13)](https://arxiv.org/html/2611.34924v1#A3.E13)

### Recovering the projection weight from cutoff spectral windows

Assume the strong resolvent limit in (C.13) exists. For a normalized
preparation $\Omega$, write $m_n(K)=\mu_n([0,K])$ for the probability of
a finite reading up to $K$ at regulator $n$, and write
$r_n(L)=\int L/(L+x)\,d\mu_n(x)$. For $L>0$ and $K\ge 0$, put
$b=L/(L+K)$. On $[0,K]$ the integrand lies between $b$ and $1$. On
$(K,\infty)$ it lies between $0$ and $b$. Integration gives

$$
b\,m_n(K)\le r_n(L)\le m_n(K)+b(1-m_n(K)).
$$

Let $r(L)=\lim_n r_n(L)$ and $p=\lim_{L\to\infty}r(L)=\|P_M\Omega\|^2$.
For fixed $K$, the lower bound gives $\limsup_n m_n(K)\le r(L)/b$.
Taking $L\to\infty$ at fixed $K$ gives $\limsup_n m_n(K)\le p$.
For fixed $L$, the upper bound gives $\liminf_n m_n(K)\ge r(L)-b$.
Taking $K\to\infty$ first then $L\to\infty$ gives the reverse bound on
the limiting lower mass. Hence

$$
p=\lim_{K\to\infty}\liminf_n m_n(K)
 =\lim_{K\to\infty}\limsup_n m_n(K).
$$

The finite-clock survival claim is equivalent to finding one bounded window
whose probability has positive lower limit as the regulator is removed.
The unit-weight claim is equivalent to asymptotic tightness. These tests
use the spectral probabilities of the cutoff clock in the actual
preparation and need no first-moment or commutation assumption. Rocq checks
the two pointwise bounds, including the window endpoint. Establishing the
strong resolvent limit and the spectral probabilities for the gravitational
preparation remains part of the clock acceptance criterion.
[Clock overlap (5.7)](https://arxiv.org/html/2611.34924v1#S5.E7) · [Resolvent limit (C.13)](https://arxiv.org/html/2611.34924v1#A3.E13) · [Rocq theorem](../../../rocq/theories/Unification/NullCone.v)

### A commuting radial clock with the benchmark covariance

If the independent configuration modes of (4.32) are expanded in an orthonormal radial basis with variance $1/(2sk)$, their product Gaussian is almost surely outside the square-summable configuration space. To see this, for coefficients $q_k$ and $t>0$, $\mathbb E e^{-t\sum_{k=1}^N q_k^2}=\prod_{k=1}^N(1+t/(sk))^{-1/2}\to0$, since the logarithm of the reciprocal diverges harmonically. Dominated convergence then forces $e^{-t\sum_{k\ge1}q_k^2}=0$ almost surely. This concerns the illustrated mode normalization and product state. Equation (4.32) is a benchmark choice and does not identify the general preparation of §5.1. A proof using other mode widths or a distribution-space topology must specify them and still establish the operator form-domain estimate. [Radial state (4.32)](https://arxiv.org/html/2611.34924v1#S4.E32) · [Fixed-area form analysis](https://arxiv.org/html/2611.34924v1#A3.SS2)

The benchmark variance in (4.32) also permits a test with the shear gradient
included. Choose a radial clock on one generator, fix its corner radius
$r>0$, set the second polarization to zero, and use independent real
coordinates $q_k$ with variances $1/(2sk)$. Let $0<\epsilon<v_0<1$ and
$d=v_0-\epsilon$. On $[\epsilon,v_0]$ take the normalized modes
$e_k(v)=\sqrt{2/d}\sin(k\pi(v-\epsilon)/d)$ and extend them by zero.
They are continuous and have square-integrable weak derivatives. Write
$z_N(v)=\sum_{k=1}^N q_k e_k(v)$ and
$\Xi_N(v)=\frac14\int_\epsilon^v w|\partial_w z_N(w)|^2\,dw$.
Orthogonality of the derivative cosines on the full subinterval gives, for
$v\ge v_0$,

$$
\Xi_N(v)\ge F_N:=a\sum_{k=1}^N k^2q_k^2,
\qquad a=\frac{\epsilon\pi^2}{4d^2}>0.
$$

Thus the single-generator clock $T_N=r\int_\epsilon^1 e^{\Xi_N(v)}\,dv$
is at least $c e^{F_N}$, with $c=r(1-v_0)>0$. Consider the product Gaussian
measure $\mu$ on the coordinates, multiplication by $T_N$ on $L^2(\mu)$,
and the normalized constant vector $1$. Completing the square in the
one-dimensional Gaussian integral gives
$\mathbb E e^{-a k^2q_k^2}=(1+a k/s)^{-1/2}$. Independence and the pointwise
resolvent bound therefore give

$$
0<\left\langle 1,\frac{L}{L+T_N}1\right\rangle
\le \frac{L}{c}\prod_{k=1}^N(1+a k/s)^{-1/2}
\le \frac{L}{c\sqrt{1+aN/s}}.
$$

Each cutoff has a dense form domain. The lower bounds $F_N$ are increasing,
and dominated convergence applied to $e^{-F_N}$ shows that
$F_N\to\infty$ almost surely. Hence $T_N\to\infty$ almost surely, the
resolvents converge strongly to zero, and the vectors with
$\sup_N\int T_N |\psi|^2\,d\mu<\infty$ form only the zero subspace.
These conclusions use the monotonicity of $F_N$. The derivative cross terms
on incomplete subintervals need not make $T_N$ itself monotone.

Rocq checks the scalar resolvent inequality used in this argument. The
bounded experiment evaluates the product in logarithms. This
commuting model uses the variance of (4.32) and the one-polarization
focusing formula from (4.22). The paper uses (4.32) for a selected
amplitude and requires a full two-polarization preparation, reduced
symplectic form and area-density operators for (5.16). The test establishes
that this variance law alone cannot justify a smooth-profile tail argument
for a clock with radial gradient energy.
[Shear form (4.22)](https://arxiv.org/html/2611.34924v1#S4.E22) · [Benchmark covariance (4.32)](https://arxiv.org/html/2611.34924v1#S4.E32)

## Gluing and finite closed traces

For a Hilbert basis $(e_i)$ and fixed vectors $x,y$, Parseval gives $\langle x,y\rangle=\sum_i\langle x,e_i\rangle\langle e_i,y\rangle$. Cauchy–Schwarz bounds the sum of the absolute values by $\|x\|\|y\|$. With normalizable endpoint states and unitary evolutions, one can absorb the evolutions into $x,y$. An orthogonal cut projection is a contraction. None of these inequalities bounds a trace by a fixed pair of Hilbert norms when the endpoints themselves are being summed. [Open gluing (4.29)–(4.30)](https://arxiv.org/html/2611.34924v1#S4.E29)

The Lean countermodel uses $\ell^2(\mathbb N;\mathbb C)$, the canonical basis, identity evolution and $W=cI$ for $0<c\le1$. Constant bounded clock and area can make the clock projection the identity and the boost weight a positive scalar. All absolute open sums for $W$ obey the open gluing bound. On the projection $P_N$ onto the first $N$ coordinates, $\operatorname{Tr}(P_NWP_N)=Nc$. The finite replica ratio is $Nc^2/(Nc)^2=1/N$ and vanishes in the limit. This falsifies the proposed inference if it uses just the abstract open gluing and weight conditions. It leaves open what the actual gravitational amplitude, matching and positivity conditions imply. The paper’s own JT example also has this abstract behavior. [Weight bounds (5.30)](https://arxiv.org/html/2611.34924v1#S5.E30) · [JT trace (2.17)](https://arxiv.org/html/2611.34924v1#S2.E17)

There are two proposed paths to a finite trace.

1. The boost argument uses a positive uncut $Z[X]$ and nonpositive $Z_P[X]$ for all nonempty finite unions of basis cycles. If the closed-cut net converges to $Z[X]$, the sign contradiction is rigorous. The appeal to (4.29) in §5.2 needs an independent identification of this net with the uncut amplitude. It also needs positivity of the exact uncut value using controlled remainders for the graviton correlator. The leading mismatch $4r/(1+r)^2$, $r=e^\eta>0$, is strictly below one for $r\ne1$ because its deficit is $(r-1)^2/(r+1)^2$. This checks the leading suppression. The scale estimate in (D.36) still needs to control the full state and regulator removals in the argument for the sign. [Boost (5.29)](https://arxiv.org/html/2611.34924v1#S5.E29) · [Sign comparison (5.37)–(5.38)](https://arxiv.org/html/2611.34924v1#S5.E38) · [Remainder (D.36)](https://arxiv.org/html/2611.34924v1#A4.E36)
2. The replica argument is valid if the exact normalized replica ratios for $0\le W\le I$ have a positive limit. At replica number two, $\operatorname{Tr}(W_P^2)\le Z_P$, so a lower bound $p>0$ on the ratio gives $Z_P\le1/p$. An eventual lower bound along cofinal cuts suffices for the trace. The regulated integrals in (D.48)–(D.49) and the one-loop mode count give evidence for the calculation. The missing step is to show that they compute the same limit as the exact operator traces. For example, multiplication by a positive bounded scalar on $L^2([0,1])$ has a finite integral of the multiplier and infinite operator trace in the Fourier basis. A continuous-labelled regulated integral must account for that distinction. [Exact conditional bound (D.47)](https://arxiv.org/html/2611.34924v1#A4.E47) · [Regulated expression (D.48)–(D.49)](https://arxiv.org/html/2611.34924v1#A4.E48)

There is also a direct construction target for the uncut preparation. If it yields a normalizable vector on the two copies of the cut, with the exact coefficients implied by (D.22), test it against $(C_b e_i/\|C_b e_i\|)\otimes e_i^*$. These vectors are orthonormal because the second factors are orthonormal. Bessel’s inequality bounds the sum of the squared coefficients $\|C_b e_i\|^2$ by the squared norm of the uncut vector. Lean checks that a uniform positive lower bound on those coefficients is impossible for any normalizable vector with infinitely many such channels. Constructing the normalizable vector independently and proving its coefficients therefore suffices for the finite trace under (5.30). [Positive lower weight (5.30)](https://arxiv.org/html/2611.34924v1#S5.E30) · [Sewn vector (D.22)](https://arxiv.org/html/2611.34924v1#A4.E22)

### Test for a normal limit of sewn preparations

Let $F$ range over finite sets of cut basis labels and let $Z_F=\sum_{i\in F}\|C_b e_i\|^2>0$.
For another finite set $S$, let $Q_S$ project the conjugate copy onto the span of the $e_i^*$ with $i\in S$.
Orthogonality on that copy in (D.22) gives the exact identity

$$
\langle\Psi_F,(I\otimes Q_S)\Psi_F\rangle
=\frac{\sum_{i\in F\cap S}\|C_b e_i\|^2}{Z_F}.
$$

If $Z_F$ diverges, the expectation goes to zero for every fixed $S$.
The projections $I\otimes Q_S$ increase strongly to the identity, so every normal state on the two-copy Hilbert space must assign them probabilities with supremum one.
The cutoff state expectations therefore cannot converge on all bounded operators to a normal state when $Z_F$ diverges. In the other direction, if $Z=\sup_F Z_F$ is positive and finite, the squared norm of any omitted part of the unnormalized sum is the sum of its weights. The sums form a Cauchy net and their normalizations converge in Hilbert norm.

This gives an exact acceptance test for the (D.22) approximation. Show the two-copy limit has a normal state with matching finite-window probabilities, or give a uniform positive lower bound for the probability of one fixed finite window along the cofinal cuts. In the latter case a probability lower bound $p>0$ gives $Z_F\le\sum_{i\in S}\|C_b e_i\|^2/p$ on those cuts. In the constant-weight countermodel a window of $m$ labels has probability $m/N$ once the cut contains it, even though every cutoff state has norm one. Applying the test to gravity requires the exact $C_b$, the identified cut basis and the stated limit or probability estimate. [Sewn vector (D.22)](https://arxiv.org/html/2611.34924v1#A4.E22)

The AdS argument uses cancellation of a centred area projection against a boundary heat weight on the joint cut. If the heat trace diverges and the area probability is strictly between zero and one, nonzero positive and negative summands each have divergent mass. Grouping all area labels over each energy vector gives zero. General finite projections also expose each sign separately. Obtaining unconditional summation from the same closed amplitude therefore has to be justified at this joint cut. Once the heat trace is finite, (5.46) follows because each state below the energy threshold contributes at least $e^{-\beta\Lambda}$. The same positive weight argument converts a finite closed trace and (5.30) to a dimension bound for the diamond. [Joint cut and AdS bounds (5.44)–(5.46)](https://arxiv.org/html/2611.34924v1#S5.E44)

Appendix E starts from amplitudes with positivity, composition and factorization. Condition 5 additionally assumes that all allowed closures in bounded spectral bands have finite amplitudes. Section E.3 uses the earlier finiteness argument when asserting the gravitational realization. A conditional equivalence with the Euclidean construction cannot furnish the missing gravitational closed traces. [Appendix E.1](https://arxiv.org/html/2611.34924v1#A5.SS1) · [Gravitational realization (E.15)](https://arxiv.org/html/2611.34924v1#A5.E15)

## Radial series and semiclassical expansion

In the benchmark at fixed $s>0$, the connected two-point contribution from independent Gaussian modes is diagonal in the mode index. Acting on the Gaussian vacuum, $q_k^2$ has a vacuum component and a two-quantum component of norm $\sqrt{2}(\Delta q_k)^2$. Removing the vacuum term and applying the time shift leaves $2(\Delta q_k)^4 e^{-2ik/s}$. Its absolute value is $1/(2s^2k^2)$. The full radial sum converges and truncating after $N$ terms incurs absolute tail at most $1/(2s^2N)$, using $\sum_{k>N}k^{-2}\le\int_N^\infty x^{-2}dx$. The dilogarithm series gives (4.33), including on the unit circle by absolute convergence at order two. [Benchmark and mode sum (4.32)–(4.33)](https://arxiv.org/html/2611.34924v1#S4.E32) · [NIST DLMF §25.12](https://dlmf.nist.gov/25.12)

Put $t=1/s$. The coefficient of $t^3$ in the finite sum is $-i\sum_{k=1}^N1/k$. The exact sum also has no finite third-order Taylor coefficient at $t=0^+$ after the quadratic term. Its imaginary part divided by $t^2$ tends to zero by dominated convergence. For $0<t<1/4$, choose $N=\lfloor1/(2t)\rfloor$. The first $N$ terms of the imaginary part divided by $t^3$ are at most $-(5/6)\sum_{k=1}^N1/k$, since $\sin x\ge (5/6)x$ on $[0,1]$. The remaining contribution has magnitude at most $1/(2tN)\le2$. The quotient therefore tends to minus infinity. This separates the finite-coupling convergence from an expansion at vanishing coupling, within the selected channel. [Taylor coefficient (4.34)](https://arxiv.org/html/2611.34924v1#S4.E34)

The case study also uses a one-oscillator check on the Weyl step. In units $\hbar=1$, the oscillator vacuum has a positive Wigner density $\pi^{-1}e^{-q^2-p^2}$, and $Q^2+P^2$ has eigenvalue one on it. With $x=q^2+p^2$, the Wigner expectation of $x$ is one. For $f_L(x)=x/(L+x)$, the supporting tangent at $x=1$ has deficit $L(x-1)^2/[(L+1)^2(L+x)]$. Integrating gives a strictly smaller Wigner average of $f_L(x)$ than the exact quantum average $f_L(1)$. Both tend to zero as $L$ grows. This shows explicitly why applying a nonlinear spectral function and taking an ordinary positive Wigner average cannot be interchanged by positivity of the Wigner function alone. An operator estimate for (5.16) could still use more specific properties of its clock. [Weyl resolvent comparison (5.9)–(5.16)](https://arxiv.org/html/2611.34924v1#S5.E9)

## Reduced observables, entropy and backreaction

For §4.2, the pure-state GNS representation is irreducible if a pure state on the required nontrivial C*-algebra has been constructed. Identifying its fixed-area subspace with the stated Fock and edge-mode space, and implementing the correct boosts, nonlinear deformations and unitary evolution, are additional obligations. For example, the algebraic time-translation law alone allows the translations on $\ell^2(\mathbb R)$ with counting measure, where $T(t)e_x=e_{x+t}$ and $\|(T(t)-I)e_0\|=\sqrt{2}$ for every nonzero $t$. Thus the continuity needed for the spectral filters has to be established on the intended representation. With that representation, first compare transition amplitudes on overlapping matched cuts. The norm error bound for finitely many inserted contractions in (4.31) can then control cutoff restoration for fixed external states. [Algebraic relations (4.2)](https://arxiv.org/html/2611.34924v1#S4.E2) · [Area-band construction](https://arxiv.org/html/2611.34924v1#S4.E13) · [Several cuts (4.31)](https://arxiv.org/html/2611.34924v1#S4.E31) · [Continuity axiom (E.3)](https://arxiv.org/html/2611.34924v1#A5.E3)

For §5.3, normalized weights $p_i=e^{-s_i}/Z$ on a nonempty finite spectrum give $-\sum_i p_i\log p_i=\sum_i p_i s_i+\log Z$. This identity supplies neither the growth of $Z$ nor the identification of the saddle area. The paper obtains the growth in (5.58) from a limiting clock moment. The one-loop estimate (5.67) uses a conical-curvature contribution at a marginal surface, with the $S^2$ scalar-curvature integral $8\pi$. Combining that estimate with the area integration and fixed-mass change of variables gives the quoted $106/45$. Sen’s pure-gravity $C_{\mathrm{local}}=212/45$ multiplies $\log a$ for the ensemble summing over angular momenta at fixed mass, where area is proportional to $a^2$ in four dimensions. It agrees after converting to $\log A$. Fixing a component of angular momentum or restricting to rotational singlets uses a different coefficient. Matching this one coefficient leaves the exact spectral growth and full reduced/constraint determinant equality unresolved. [Entropy identity (5.50)](https://arxiv.org/html/2611.34924v1#S5.E50) · [Count and determinant (5.58), (5.67)–(5.69)](https://arxiv.org/html/2611.34924v1#S5.E67) · [Sen (1.1)–(1.5)](https://arxiv.org/html/1205.0971#S1)

For §6, differentiating $E[g(\phi)]=0$ twice in a smooth classical solution family gives $E^{(1)}[g_{IJ}]=-2E^{(2)}[g_I,g_J]$ with the paper’s normalization of the quadratic term. Contracting this identity with $\Sigma^{IJ}/2$ gives the finite covariance identity without further field equations. A full result needs a gauge-compatible classical solution and propagator, a distributional state with the stated singularity structure, and a renormalization prescription for (6.14) that makes the coincident source well-defined and conserved. Checking the free two-point kernel at separated points gives an intermediate test. Once the quadratic source is constructed, apply the linearized Bianchi identity and compare the retarded solution with the derivative of the characteristic evolution. [Backreaction (6.11)–(6.16)](https://arxiv.org/html/2611.34924v1#S6.E11) · [Hollands and Wald on local Wick products](https://arxiv.org/abs/gr-qc/0103074)
