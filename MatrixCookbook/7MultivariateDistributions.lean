module

set_option doc.verso true

/-!
# Multivariate Distributions

## Cauchy
-/

@[expose] public section

namespace MatrixCookbook

/--
> The density function for a Cauchy distributed vector $`\mathbf{t}\in\mathbb{R}^{P\times 1}`, is given by

  $$`p(\mathbf{t}|\boldsymbol{\mu},\mathbf{\Sigma}) = \pi^{-P/2}\frac{\Gamma(\frac{1+P}{2})}{\Gamma(1/2)}\frac{\det(\mathbf{\Sigma})^{-1/2}}{\big[1+(\mathbf{t}-\boldsymbol{\mu})^{\mathsf{T}}\mathbf{\Sigma}^{-1}(\mathbf{t}-\boldsymbol{\mu})\big]^{(1+P)/2}} \tag{335}`
-/
theorem eq_335 : (sorry : Prop) := sorry

/-!
> where $`\boldsymbol{\mu}` is the location, $`\mathbf{\Sigma}` is positive definite, and $`\Gamma` denotes the gamma function. The Cauchy distribution is a special case of the Student-t distribution.

## Dirichlet

> The Dirichlet distribution is a kind of “inverse” distribution compared to the multinomial distribution on the bounded continuous variate $`\mathbf{x} = [x_1, \ldots, x_P]` \[16, p. 44\]

  $$`p(\mathbf{x}|\boldsymbol{\alpha}) = \frac{\Gamma\left(\sum_p^P\alpha_p\right)}{\prod_p^P\Gamma(\alpha_p)}\prod_p^P x_p^{\alpha_p-1}`

## Normal

> The normal distribution is also known as a Gaussian distribution. See sec. 8.

## Normal-Inverse Gamma

## Gaussian

> See sec. 8.

## Multinomial

> If the vector $`\mathbf{n}` contains counts, i.e. $`(\mathbf{n})_i \in 0, 1, 2, ...`, then the discrete multinomial disitrbution for $`\mathbf{n}` is given by

  $$`P(\mathbf{n}|\mathbf{a}, n) = \frac{n!}{n_1!\ldots n_d!}\prod_i^d a_i^{n_i}, \qquad \sum_i^d n_i = n \tag{336}`

  where $`a_i` are probabilities, i.e. $`0 \le a_i \le 1` and $`\sum_i a_i = 1`.

## Student's t

> The density of a Student-t distributed vector $`\mathbf{t}\in\mathbb{R}^{P\times 1}`, is given by

  $$`p(\mathbf{t}|\boldsymbol{\mu},\mathbf{\Sigma},\nu) = (\pi\nu)^{-P/2}\frac{\Gamma(\frac{\nu+P}{2})}{\Gamma(\nu/2)}\frac{\det(\mathbf{\Sigma})^{-1/2}}{\big[1+\nu^{-1}(\mathbf{t}-\boldsymbol{\mu})^{\mathsf{T}}\mathbf{\Sigma}^{-1}(\mathbf{t}-\boldsymbol{\mu})\big]^{(\nu+P)/2}} \tag{337}`

  where $`\boldsymbol{\mu}` is the location, the scale matrix $`\mathbf{\Sigma}` is symmetric, positive definite, $`\nu` is the degrees of freedom, and $`\Gamma` denotes the gamma function. For $`\nu = 1`, the Student-t distribution becomes the Cauchy distribution (see sec 7.1).

### Mean

> $$`\mathrm{E}(\mathbf{t}) = \boldsymbol{\mu}, \qquad \nu > 1 \tag{338}`

### Variance

> $$`\operatorname{cov}(\mathbf{t}) = \frac{\nu}{\nu-2}\mathbf{\Sigma}, \qquad \nu > 2 \tag{339}`

### Mode

> The notion _mode_ meaning the position of the most probable value

  $$`\operatorname{mode}(\mathbf{t}) = \boldsymbol{\mu} \tag{340}`

### Full Matrix Version

> If instead of a vector $`\mathbf{t}\in\mathbb{R}^{P\times 1}` one has a matrix $`\mathbf{T}\in\mathbb{R}^{P\times N}`, then the Student-t distribution for $`\mathbf{T}` is

  $$`\begin{aligned} p(\mathbf{T}|\mathbf{M},\mathbf{\Omega},\mathbf{\Sigma},\nu) &= \pi^{-NP/2}\prod_{p=1}^P\frac{\Gamma\left[(\nu+P-p+1)/2\right]}{\Gamma\left[(\nu-p+1)/2\right]}\times \\ &\qquad \nu\det(\mathbf{\Omega})^{-\nu/2}\det(\mathbf{\Sigma})^{-N/2}\times \\ &\qquad \det\left[\mathbf{\Omega}^{-1}+(\mathbf{T}-\mathbf{M})\mathbf{\Sigma}^{-1}(\mathbf{T}-\mathbf{M})^{\mathsf{T}}\right]^{-(\nu+P)/2} \end{aligned} \tag{341}`

  where $`\mathbf{M}` is the location, $`\mathbf{\Omega}` is the rescaling matrix, $`\mathbf{\Sigma}` is positive definite, $`\nu` is the degrees of freedom, and $`\Gamma` denotes the gamma function.

## Wishart

> The central Wishart distribution for $`\mathbf{M}\in\mathbb{R}^{P\times P}`, $`\mathbf{M}` is positive definite, where $`m` can be regarded as a degree of freedom parameter \[16, equation 3.8.1\] \[8, section 2.5\],\[11\]

  $$`\begin{aligned} p(\mathbf{M}|\mathbf{\Sigma},m) &= \frac{1}{2^{mP/2}\pi^{P(P-1)/4}\prod_p^P\Gamma[\frac{1}{2}(m+1-p)]}\times \\ &\qquad \det(\mathbf{\Sigma})^{-m/2}\det(\mathbf{M})^{(m-P-1)/2}\times \\ &\qquad \exp\left[-\frac{1}{2}\operatorname{Tr}(\mathbf{\Sigma}^{-1}\mathbf{M})\right] \end{aligned} \tag{342}`

### Mean

> $$`E(\mathbf{M}) = \mathbf{m}\mathbf{\Sigma} \tag{343}`

## Wishart, Inverse

> The (normal) Inverse Wishart distribution for $`\mathbf{M}\in\mathbb{R}^{P\times P}`, $`\mathbf{M}` is positive definite, where $`m` can be regarded as a degree of freedom parameter \[11\]

  $$`\begin{aligned} p(\mathbf{M}|\mathbf{\Sigma},m) &= \frac{1}{2^{mP/2}\pi^{P(P-1)/4}\prod_p^P\Gamma[\frac{1}{2}(m+1-p)]}\times \\ &\qquad \det(\mathbf{\Sigma})^{m/2}\det(\mathbf{M})^{-(m-P-1)/2}\times \\ &\qquad \exp\left[-\frac{1}{2}\operatorname{Tr}(\mathbf{\Sigma}\mathbf{M}^{-1})\right] \end{aligned} \tag{344}`

### Mean
-/

/--
> $$`E(\mathbf{M}) = \mathbf{\Sigma}\frac{1}{m-P-1} \tag{345}`
-/
theorem eq_345 : (sorry : Prop) := sorry

end MatrixCookbook
