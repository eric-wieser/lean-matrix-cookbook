module

set_option doc.verso true

/-!
# Gaussians

## Basics

### Density and normalization
-/

public section

namespace MatrixCookbook

/--
> The density of $`\mathbf{x}\sim\mathcal{N}(\mathbf{m},\mathbf{\Sigma})` is

  $$`p(\mathbf{x}) = \frac{1}{\sqrt{\det(2\pi\mathbf{\Sigma})}}\exp\left[-\frac{1}{2}(\mathbf{x}-\mathbf{m})^T\mathbf{\Sigma}^{-1}(\mathbf{x}-\mathbf{m})\right] \tag{346}`
-/
theorem eq_346 : (sorry : Prop) := sorry

/-!
> Note that if $`\mathbf{x}` is $`d`-dimensional, then $`\det(2\pi\mathbf{\Sigma}) = (2\pi)^d\det(\mathbf{\Sigma})`.

  Integration and normalization

  $$`\begin{aligned} \int\exp\left[-\frac{1}{2}(\mathbf{x}-\mathbf{m})^T\mathbf{\Sigma}^{-1}(\mathbf{x}-\mathbf{m})\right]d\mathbf{x} &= \sqrt{\det(2\pi\mathbf{\Sigma})} \\ \int\exp\left[-\frac{1}{2}\mathbf{x}^T\mathbf{\Sigma}^{-1}\mathbf{x}+\mathbf{m}^T\mathbf{\Sigma}^{-1}\mathbf{x}\right]d\mathbf{x} &= \sqrt{\det(2\pi\mathbf{\Sigma})}\exp\left[\frac{1}{2}\mathbf{m}^T\mathbf{\Sigma}^{-1}\mathbf{m}\right] \\ \int\exp\left[-\frac{1}{2}\mathbf{x}^T\mathbf{A}\mathbf{x}+\mathbf{c}^T\mathbf{x}\right]d\mathbf{x} &= \sqrt{\det(2\pi\mathbf{A}^{-1})}\exp\left[\frac{1}{2}\mathbf{c}^T\mathbf{A}^{-T}\mathbf{c}\right] \end{aligned}`

  If $`\mathbf{X} = [\mathbf{x}_1\mathbf{x}_2...\mathbf{x}_n]` and $`\mathbf{C} = [\mathbf{c}_1\mathbf{c}_2...\mathbf{c}_n]`, then

  $$`\int\exp\left[-\frac{1}{2}\operatorname{Tr}(\mathbf{X}^T\mathbf{A}\mathbf{X})+\operatorname{Tr}(\mathbf{C}^T\mathbf{X})\right]d\mathbf{X} = \sqrt{\det(2\pi\mathbf{A}^{-1})}^n\exp\left[\frac{1}{2}\operatorname{Tr}(\mathbf{C}^T\mathbf{A}^{-1}\mathbf{C})\right]`

  The derivatives of the density are

  $$`\frac{\partial p(\mathbf{x})}{\partial\mathbf{x}} = -p(\mathbf{x})\mathbf{\Sigma}^{-1}(\mathbf{x}-\mathbf{m}) \tag{347}`

  $$`\frac{\partial^2 p}{\partial\mathbf{x}\partial\mathbf{x}^T} = p(\mathbf{x})\Big(\mathbf{\Sigma}^{-1}(\mathbf{x}-\mathbf{m})(\mathbf{x}-\mathbf{m})^T\mathbf{\Sigma}^{-1}-\mathbf{\Sigma}^{-1}\Big) \tag{348}`

### Marginal Distribution

> Assume $`\mathbf{x}\sim\mathcal{N}_{\mathbf{x}}(\mu,\Sigma)` where

  $$`\mathbf{x} = \begin{bmatrix} \mathbf{x}_a \\ \mathbf{x}_b \end{bmatrix} \qquad \boldsymbol{\mu} = \begin{bmatrix} \boldsymbol{\mu}_a \\ \boldsymbol{\mu}_b \end{bmatrix} \qquad \mathbf{\Sigma} = \begin{bmatrix} \mathbf{\Sigma}_a & \mathbf{\Sigma}_c \\ \mathbf{\Sigma}_c^T & \mathbf{\Sigma}_b \end{bmatrix} \tag{349}`

  then

  $$`p(\mathbf{x}_a) = \mathcal{N}_{\mathbf{x}_a}(\boldsymbol{\mu}_a,\mathbf{\Sigma}_a) \tag{350}`

  $$`p(\mathbf{x}_b) = \mathcal{N}_{\mathbf{x}_b}(\boldsymbol{\mu}_b,\mathbf{\Sigma}_b) \tag{351}`

### Conditional Distribution

> Assume $`\mathbf{x}\sim\mathcal{N}_{\mathbf{x}}(\mu,\Sigma)` where

  $$`\mathbf{x} = \begin{bmatrix} \mathbf{x}_a \\ \mathbf{x}_b \end{bmatrix} \qquad \boldsymbol{\mu} = \begin{bmatrix} \boldsymbol{\mu}_a \\ \boldsymbol{\mu}_b \end{bmatrix} \qquad \mathbf{\Sigma} = \begin{bmatrix} \mathbf{\Sigma}_a & \mathbf{\Sigma}_c \\ \mathbf{\Sigma}_c^T & \mathbf{\Sigma}_b \end{bmatrix} \tag{352}`

  then

  $$`p(\mathbf{x}_a|\mathbf{x}_b) = \mathcal{N}_{\mathbf{x}_a}(\hat{\mu}_a,\hat{\mathbf{\Sigma}}_a) \qquad \left\{\begin{array}{lcl} \hat{\boldsymbol{\mu}}_a & = & \boldsymbol{\mu}_a+\mathbf{\Sigma}_c\mathbf{\Sigma}_b^{-1}(\mathbf{x}_b-\boldsymbol{\mu}_b) \\ \hat{\mathbf{\Sigma}}_a & = & \mathbf{\Sigma}_a-\mathbf{\Sigma}_c\mathbf{\Sigma}_b^{-1}\mathbf{\Sigma}_c^T \end{array}\right. \tag{353}`

  $$`p(\mathbf{x}_b|\mathbf{x}_a) = \mathcal{N}_{\mathbf{x}_b}(\hat{\mu}_b,\hat{\mathbf{\Sigma}}_b) \qquad \left\{\begin{array}{lcl} \hat{\boldsymbol{\mu}}_b & = & \boldsymbol{\mu}_b+\mathbf{\Sigma}_c^T\mathbf{\Sigma}_a^{-1}(\mathbf{x}_a-\boldsymbol{\mu}_a) \\ \hat{\mathbf{\Sigma}}_b & = & \mathbf{\Sigma}_b-\mathbf{\Sigma}_c^T\mathbf{\Sigma}_a^{-1}\mathbf{\Sigma}_c \end{array}\right. \tag{354}`

  Note, that the covariance matrices are the Schur complement of the block matrix, see 9.1.5 for details.

### Linear combination

> Assume $`\mathbf{x}\sim\mathcal{N}(\mathbf{m}_x,\mathbf{\Sigma}_x)` and $`\mathbf{y}\sim\mathcal{N}(\mathbf{m}_y,\mathbf{\Sigma}_y)` then

  $$`\mathbf{A}\mathbf{x}+\mathbf{B}\mathbf{y}+\mathbf{c}\sim\mathcal{N}(\mathbf{A}\mathbf{m}_x+\mathbf{B}\mathbf{m}_y+\mathbf{c},\mathbf{A}\mathbf{\Sigma}_x\mathbf{A}^T+\mathbf{B}\mathbf{\Sigma}_y\mathbf{B}^T) \tag{355}`

### Rearranging Means

> $$`\mathcal{N}_{\mathbf{A}\mathbf{x}}[\mathbf{m},\mathbf{\Sigma}] = \frac{\sqrt{\det(2\pi(\mathbf{A}^T\mathbf{\Sigma}^{-1}\mathbf{A})^{-1})}}{\sqrt{\det(2\pi\mathbf{\Sigma})}}\mathcal{N}_{\mathbf{x}}[\mathbf{A}^{-1}\mathbf{m},(\mathbf{A}^T\mathbf{\Sigma}^{-1}\mathbf{A})^{-1}] \tag{356}`

  If $`\mathbf{A}` is square and invertible, it simplifies to

  $$`\mathcal{N}_{\mathbf{A}\mathbf{x}}[\mathbf{m},\mathbf{\Sigma}] = \frac{1}{|\det(\mathbf{A})|}\mathcal{N}_{\mathbf{x}}[\mathbf{A}^{-1}\mathbf{m},(\mathbf{A}^T\mathbf{\Sigma}^{-1}\mathbf{A})^{-1}] \tag{357}`

### Rearranging into squared form

> If $`\mathbf{A}` is symmetric, then

  $$`\begin{aligned} -\frac{1}{2}\mathbf{x}^T\mathbf{A}\mathbf{x}+\mathbf{b}^T\mathbf{x} &= -\frac{1}{2}(\mathbf{x}-\mathbf{A}^{-1}\mathbf{b})^T\mathbf{A}(\mathbf{x}-\mathbf{A}^{-1}\mathbf{b})+\frac{1}{2}\mathbf{b}^T\mathbf{A}^{-1}\mathbf{b} \\ -\frac{1}{2}\operatorname{Tr}(\mathbf{X}^T\mathbf{A}\mathbf{X})+\operatorname{Tr}(\mathbf{B}^T\mathbf{X}) &= -\frac{1}{2}\operatorname{Tr}[(\mathbf{X}-\mathbf{A}^{-1}\mathbf{B})^T\mathbf{A}(\mathbf{X}-\mathbf{A}^{-1}\mathbf{B})]+\frac{1}{2}\operatorname{Tr}(\mathbf{B}^T\mathbf{A}^{-1}\mathbf{B}) \end{aligned}`

### Sum of two squared forms

> In vector formulation (assuming $`\mathbf{\Sigma}_1, \mathbf{\Sigma}_2` are symmetric)

  $$`-\frac{1}{2}(\mathbf{x}-\mathbf{m}_1)^T\mathbf{\Sigma}_1^{-1}(\mathbf{x}-\mathbf{m}_1) \tag{358}`

  $$`-\frac{1}{2}(\mathbf{x}-\mathbf{m}_2)^T\mathbf{\Sigma}_2^{-1}(\mathbf{x}-\mathbf{m}_2) \tag{359}`

  $$`= -\frac{1}{2}(\mathbf{x}-\mathbf{m}_c)^T\mathbf{\Sigma}_c^{-1}(\mathbf{x}-\mathbf{m}_c)+C \tag{360}`

  $$`\mathbf{\Sigma}_c^{-1} = \mathbf{\Sigma}_1^{-1}+\mathbf{\Sigma}_2^{-1} \tag{361}`

  $$`\mathbf{m}_c = (\mathbf{\Sigma}_1^{-1}+\mathbf{\Sigma}_2^{-1})^{-1}(\mathbf{\Sigma}_1^{-1}\mathbf{m}_1+\mathbf{\Sigma}_2^{-1}\mathbf{m}_2) \tag{362}`

  $$`C = \frac{1}{2}(\mathbf{m}_1^T\mathbf{\Sigma}_1^{-1}+\mathbf{m}_2^T\mathbf{\Sigma}_2^{-1})(\mathbf{\Sigma}_1^{-1}+\mathbf{\Sigma}_2^{-1})^{-1}(\mathbf{\Sigma}_1^{-1}\mathbf{m}_1+\mathbf{\Sigma}_2^{-1}\mathbf{m}_2) \tag{363}`

  $$`-\frac{1}{2}\Big(\mathbf{m}_1^T\mathbf{\Sigma}_1^{-1}\mathbf{m}_1+\mathbf{m}_2^T\mathbf{\Sigma}_2^{-1}\mathbf{m}_2\Big) \tag{364}`

  In a trace formulation (assuming $`\mathbf{\Sigma}_1, \mathbf{\Sigma}_2` are symmetric)

  $$`-\frac{1}{2}\operatorname{Tr}((\mathbf{X}-\mathbf{M}_1)^T\mathbf{\Sigma}_1^{-1}(\mathbf{X}-\mathbf{M}_1)) \tag{365}`

  $$`-\frac{1}{2}\operatorname{Tr}((\mathbf{X}-\mathbf{M}_2)^T\mathbf{\Sigma}_2^{-1}(\mathbf{X}-\mathbf{M}_2)) \tag{366}`

  $$`= -\frac{1}{2}\operatorname{Tr}[(\mathbf{X}-\mathbf{M}_c)^T\mathbf{\Sigma}_c^{-1}(\mathbf{X}-\mathbf{M}_c)]+C \tag{367}`

  $$`\mathbf{\Sigma}_c^{-1} = \mathbf{\Sigma}_1^{-1}+\mathbf{\Sigma}_2^{-1} \tag{368}`

  $$`\mathbf{M}_c = (\mathbf{\Sigma}_1^{-1}+\mathbf{\Sigma}_2^{-1})^{-1}(\mathbf{\Sigma}_1^{-1}\mathbf{M}_1+\mathbf{\Sigma}_2^{-1}\mathbf{M}_2) \tag{369}`

  $$`\begin{aligned} C &= \frac{1}{2}\operatorname{Tr}\Big[(\mathbf{\Sigma}_1^{-1}\mathbf{M}_1+\mathbf{\Sigma}_2^{-1}\mathbf{M}_2)^T(\mathbf{\Sigma}_1^{-1}+\mathbf{\Sigma}_2^{-1})^{-1}(\mathbf{\Sigma}_1^{-1}\mathbf{M}_1+\mathbf{\Sigma}_2^{-1}\mathbf{M}_2)\Big] \\ &\quad -\frac{1}{2}\operatorname{Tr}(\mathbf{M}_1^T\mathbf{\Sigma}_1^{-1}\mathbf{M}_1+\mathbf{M}_2^T\mathbf{\Sigma}_2^{-1}\mathbf{M}_2) \end{aligned} \tag{370}`

### Product of gaussian densities

> Let $`\mathcal{N}_{\mathbf{x}}(\mathbf{m},\mathbf{\Sigma})` denote a density of $`\mathbf{x}`, then

  $$`\mathcal{N}_{\mathbf{x}}(\mathbf{m}_1,\mathbf{\Sigma}_1)\cdot\mathcal{N}_{\mathbf{x}}(\mathbf{m}_2,\mathbf{\Sigma}_2) = c_c\mathcal{N}_{\mathbf{x}}(\mathbf{m}_c,\mathbf{\Sigma}_c) \tag{371}`

  $$`\begin{aligned} c_c &= \mathcal{N}_{\mathbf{m}_1}(\mathbf{m}_2,(\mathbf{\Sigma}_1+\mathbf{\Sigma}_2)) \\ &= \frac{1}{\sqrt{\det(2\pi(\mathbf{\Sigma}_1+\mathbf{\Sigma}_2))}}\exp\left[-\frac{1}{2}(\mathbf{m}_1-\mathbf{m}_2)^T(\mathbf{\Sigma}_1+\mathbf{\Sigma}_2)^{-1}(\mathbf{m}_1-\mathbf{m}_2)\right] \\ \mathbf{m}_c &= (\mathbf{\Sigma}_1^{-1}+\mathbf{\Sigma}_2^{-1})^{-1}(\mathbf{\Sigma}_1^{-1}\mathbf{m}_1+\mathbf{\Sigma}_2^{-1}\mathbf{m}_2) \\ \mathbf{\Sigma}_c &= (\mathbf{\Sigma}_1^{-1}+\mathbf{\Sigma}_2^{-1})^{-1} \end{aligned}`

  but note that the product is not normalized as a density of $`\mathbf{x}`.

## Moments

### Mean and covariance of linear forms

> First and second moments. Assume $`\mathbf{x}\sim\mathcal{N}(\mathbf{m},\mathbf{\Sigma})`

  $$`E(\mathbf{x}) = \mathbf{m} \tag{372}`

  $$`\operatorname{Cov}(\mathbf{x},\mathbf{x}) = \operatorname{Var}(\mathbf{x}) = \mathbf{\Sigma} = E(\mathbf{x}\mathbf{x}^T)-E(\mathbf{x})E(\mathbf{x}^T) = E(\mathbf{x}\mathbf{x}^T)-\mathbf{m}\mathbf{m}^T \tag{373}`

  As for any other distribution is holds for gaussians that

  $$`E[\mathbf{A}\mathbf{x}] = \mathbf{A}E[\mathbf{x}] \tag{374}`

  $$`\operatorname{Var}[\mathbf{A}\mathbf{x}] = \mathbf{A}\operatorname{Var}[\mathbf{x}]\mathbf{A}^T \tag{375}`

  $$`\operatorname{Cov}[\mathbf{A}\mathbf{x},\mathbf{B}\mathbf{y}] = \mathbf{A}\operatorname{Cov}[\mathbf{x},\mathbf{y}]\mathbf{B}^T \tag{376}`

### Mean and variance of square forms

> Mean and variance of square forms: Assume $`\mathbf{x}\sim\mathcal{N}(\mathbf{m},\mathbf{\Sigma})`

  $$`E(\mathbf{x}\mathbf{x}^T) = \mathbf{\Sigma}+\mathbf{m}\mathbf{m}^T \tag{377}`

  $$`E[\mathbf{x}^T\mathbf{A}\mathbf{x}] = \operatorname{Tr}(\mathbf{A}\mathbf{\Sigma})+\mathbf{m}^T\mathbf{A}\mathbf{m} \tag{378}`

  $$`\begin{aligned} \operatorname{Var}(\mathbf{x}^T\mathbf{A}\mathbf{x}) &= \operatorname{Tr}[\mathbf{A}\mathbf{\Sigma}(\mathbf{A}+\mathbf{A}^T)\mathbf{\Sigma}]+... \\ &\quad +\mathbf{m}^T(\mathbf{A}+\mathbf{A}^T)\mathbf{\Sigma}(\mathbf{A}+\mathbf{A}^T)\mathbf{m} \end{aligned} \tag{379}`

  $$`E[(\mathbf{x}-\mathbf{m}')^T\mathbf{A}(\mathbf{x}-\mathbf{m}')] = (\mathbf{m}-\mathbf{m}')^T\mathbf{A}(\mathbf{m}-\mathbf{m}')+\operatorname{Tr}(\mathbf{A}\mathbf{\Sigma}) \tag{380}`

  If $`\mathbf{\Sigma} = \sigma^2\mathbf{I}` and $`\mathbf{A}` is symmetric, then

  $$`\operatorname{Var}(\mathbf{x}^T\mathbf{A}\mathbf{x}) = 2\sigma^4\operatorname{Tr}(\mathbf{A}^2)+4\sigma^2\mathbf{m}^T\mathbf{A}^2\mathbf{m} \tag{381}`

  Assume $`\mathbf{x}\sim\mathcal{N}(\mathbf{0},\sigma^2\mathbf{I})` and $`\mathbf{A}` and $`\mathbf{B}` to be symmetric, then

  $$`\operatorname{Cov}(\mathbf{x}^T\mathbf{A}\mathbf{x},\mathbf{x}^T\mathbf{B}\mathbf{x}) = 2\sigma^4\operatorname{Tr}(\mathbf{A}\mathbf{B}) \tag{382}`

### Cubic forms

> Assume $`\mathbf{x}` to be a stochastic vector with independent coordinates, mean $`\mathbf{m}` and covariance $`\mathbf{M}`

  $$`\begin{aligned} E[\mathbf{x}\mathbf{b}^T\mathbf{x}\mathbf{x}^T] &= \mathbf{m}\mathbf{b}^T(\mathbf{M}+\mathbf{m}\mathbf{m}^T)+(\mathbf{M}+\mathbf{m}\mathbf{m}^T)\mathbf{b}\mathbf{m}^T \\ &\quad +\mathbf{b}^T\mathbf{m}(\mathbf{M}-\mathbf{m}\mathbf{m}^T) \end{aligned} \tag{383}`

### Mean of Quartic Forms

> $$`\begin{aligned} E[\mathbf{x}\mathbf{x}^T\mathbf{x}\mathbf{x}^T] &= 2(\mathbf{\Sigma}+\mathbf{m}\mathbf{m}^T)^2+\mathbf{m}^T\mathbf{m}(\mathbf{\Sigma}-\mathbf{m}\mathbf{m}^T) \\ &\quad +\operatorname{Tr}(\mathbf{\Sigma})(\mathbf{\Sigma}+\mathbf{m}\mathbf{m}^T) \\ E[\mathbf{x}\mathbf{x}^T\mathbf{A}\mathbf{x}\mathbf{x}^T] &= (\mathbf{\Sigma}+\mathbf{m}\mathbf{m}^T)(\mathbf{A}+\mathbf{A}^T)(\mathbf{\Sigma}+\mathbf{m}\mathbf{m}^T) \\ &\quad +\mathbf{m}^T\mathbf{A}\mathbf{m}(\mathbf{\Sigma}-\mathbf{m}\mathbf{m}^T)+\operatorname{Tr}[\mathbf{A}\mathbf{\Sigma}](\mathbf{\Sigma}+\mathbf{m}\mathbf{m}^T) \\ E[\mathbf{x}^T\mathbf{x}\mathbf{x}^T\mathbf{x}] &= 2\operatorname{Tr}(\mathbf{\Sigma}^2)+4\mathbf{m}^T\mathbf{\Sigma}\mathbf{m}+(\operatorname{Tr}(\mathbf{\Sigma})+\mathbf{m}^T\mathbf{m})^2 \\ E[\mathbf{x}^T\mathbf{A}\mathbf{x}\mathbf{x}^T\mathbf{B}\mathbf{x}] &= \operatorname{Tr}[\mathbf{A}\mathbf{\Sigma}(\mathbf{B}+\mathbf{B}^T)\mathbf{\Sigma}]+\mathbf{m}^T(\mathbf{A}+\mathbf{A}^T)\mathbf{\Sigma}(\mathbf{B}+\mathbf{B}^T)\mathbf{m} \\ &\quad +(\operatorname{Tr}(\mathbf{A}\mathbf{\Sigma})+\mathbf{m}^T\mathbf{A}\mathbf{m})(\operatorname{Tr}(\mathbf{B}\mathbf{\Sigma})+\mathbf{m}^T\mathbf{B}\mathbf{m}) \end{aligned}`

  $$`\begin{aligned} & E[\mathbf{a}^T\mathbf{x}\mathbf{b}^T\mathbf{x}\mathbf{c}^T\mathbf{x}\mathbf{d}^T\mathbf{x}] \\ = {} & (\mathbf{a}^T(\mathbf{\Sigma}+\mathbf{m}\mathbf{m}^T)\mathbf{b})(\mathbf{c}^T(\mathbf{\Sigma}+\mathbf{m}\mathbf{m}^T)\mathbf{d}) \\ & +(\mathbf{a}^T(\mathbf{\Sigma}+\mathbf{m}\mathbf{m}^T)\mathbf{c})(\mathbf{b}^T(\mathbf{\Sigma}+\mathbf{m}\mathbf{m}^T)\mathbf{d}) \\ & +(\mathbf{a}^T(\mathbf{\Sigma}+\mathbf{m}\mathbf{m}^T)\mathbf{d})(\mathbf{b}^T(\mathbf{\Sigma}+\mathbf{m}\mathbf{m}^T)\mathbf{c})-2\mathbf{a}^T\mathbf{m}\mathbf{b}^T\mathbf{m}\mathbf{c}^T\mathbf{m}\mathbf{d}^T\mathbf{m} \end{aligned}`

  $$`\begin{aligned} & E[(\mathbf{A}\mathbf{x}+\mathbf{a})(\mathbf{B}\mathbf{x}+\mathbf{b})^T(\mathbf{C}\mathbf{x}+\mathbf{c})(\mathbf{D}\mathbf{x}+\mathbf{d})^T] \\ = {} & [\mathbf{A}\mathbf{\Sigma}\mathbf{B}^T+(\mathbf{A}\mathbf{m}+\mathbf{a})(\mathbf{B}\mathbf{m}+\mathbf{b})^T][\mathbf{C}\mathbf{\Sigma}\mathbf{D}^T+(\mathbf{C}\mathbf{m}+\mathbf{c})(\mathbf{D}\mathbf{m}+\mathbf{d})^T] \\ & +[\mathbf{A}\mathbf{\Sigma}\mathbf{C}^T+(\mathbf{A}\mathbf{m}+\mathbf{a})(\mathbf{C}\mathbf{m}+\mathbf{c})^T][\mathbf{B}\mathbf{\Sigma}\mathbf{D}^T+(\mathbf{B}\mathbf{m}+\mathbf{b})(\mathbf{D}\mathbf{m}+\mathbf{d})^T] \\ & +(\mathbf{B}\mathbf{m}+\mathbf{b})^T(\mathbf{C}\mathbf{m}+\mathbf{c})[\mathbf{A}\mathbf{\Sigma}\mathbf{D}^T-(\mathbf{A}\mathbf{m}+\mathbf{a})(\mathbf{D}\mathbf{m}+\mathbf{d})^T] \\ & +\operatorname{Tr}(\mathbf{B}\mathbf{\Sigma}\mathbf{C}^T)[\mathbf{A}\mathbf{\Sigma}\mathbf{D}^T+(\mathbf{A}\mathbf{m}+\mathbf{a})(\mathbf{D}\mathbf{m}+\mathbf{d})^T] \end{aligned}`

  $$`\begin{aligned} & E[(\mathbf{A}\mathbf{x}+\mathbf{a})^T(\mathbf{B}\mathbf{x}+\mathbf{b})(\mathbf{C}\mathbf{x}+\mathbf{c})^T(\mathbf{D}\mathbf{x}+\mathbf{d})] \\ = {} & \operatorname{Tr}[\mathbf{A}\mathbf{\Sigma}(\mathbf{C}^T\mathbf{D}+\mathbf{D}^T\mathbf{C})\mathbf{\Sigma}\mathbf{B}^T] \\ & +[(\mathbf{A}\mathbf{m}+\mathbf{a})^T\mathbf{B}+(\mathbf{B}\mathbf{m}+\mathbf{b})^T\mathbf{A}]\mathbf{\Sigma}[\mathbf{C}^T(\mathbf{D}\mathbf{m}+\mathbf{d})+\mathbf{D}^T(\mathbf{C}\mathbf{m}+\mathbf{c})] \\ & +[\operatorname{Tr}(\mathbf{A}\mathbf{\Sigma}\mathbf{B}^T)+(\mathbf{A}\mathbf{m}+\mathbf{a})^T(\mathbf{B}\mathbf{m}+\mathbf{b})][\operatorname{Tr}(\mathbf{C}\mathbf{\Sigma}\mathbf{D}^T)+(\mathbf{C}\mathbf{m}+\mathbf{c})^T(\mathbf{D}\mathbf{m}+\mathbf{d})] \end{aligned}`

  See \[7\].

### Moments

> $$`E[\mathbf{x}] = \sum_k\rho_k\mathbf{m}_k \tag{384}`

  $$`\operatorname{Cov}(\mathbf{x}) = \sum_k\sum_{k'}\rho_k\rho_{k'}(\mathbf{\Sigma}_k+\mathbf{m}_k\mathbf{m}_k^T-\mathbf{m}_k\mathbf{m}_{k'}^T) \tag{385}`

## Miscellaneous

### Whitening

> Assume $`\mathbf{x}\sim\mathcal{N}(\mathbf{m},\mathbf{\Sigma})` then

  $$`\mathbf{z} = \mathbf{\Sigma}^{-1/2}(\mathbf{x}-\mathbf{m})\sim\mathcal{N}(\mathbf{0},\mathbf{I}) \tag{386}`

  Conversely having $`\mathbf{z}\sim\mathcal{N}(\mathbf{0},\mathbf{I})` one can generate data $`\mathbf{x}\sim\mathcal{N}(\mathbf{m},\mathbf{\Sigma})` by setting

  $$`\mathbf{x} = \mathbf{\Sigma}^{1/2}\mathbf{z}+\mathbf{m}\sim\mathcal{N}(\mathbf{m},\mathbf{\Sigma}) \tag{387}`

  Note that $`\mathbf{\Sigma}^{1/2}` means the matrix which fulfils $`\mathbf{\Sigma}^{1/2}\mathbf{\Sigma}^{1/2} = \mathbf{\Sigma}`, and that it exists and is unique since $`\mathbf{\Sigma}` is positive definite.

### The Chi-Square connection

> Assume $`\mathbf{x}\sim\mathcal{N}(\mathbf{m},\mathbf{\Sigma})` and $`\mathbf{x}` to be $`n` dimensional, then

  $$`z = (\mathbf{x}-\mathbf{m})^T\mathbf{\Sigma}^{-1}(\mathbf{x}-\mathbf{m})\sim\chi_n^2 \tag{388}`

  where $`\chi_n^2` denotes the Chi square distribution with $`n` degrees of freedom.

### Entropy

> Entropy of a $`D`-dimensional gaussian

  $$`H(\mathbf{x}) = -\int\mathcal{N}(\mathbf{m},\mathbf{\Sigma})\ln\mathcal{N}(\mathbf{m},\mathbf{\Sigma})d\mathbf{x} = \ln\sqrt{\det(2\pi\mathbf{\Sigma})}+\frac{D}{2} \tag{389}`

## Mixture of Gaussians

### Density

> The variable $`\mathbf{x}` is distributed as a mixture of gaussians if it has the density

  $$`p(\mathbf{x}) = \sum_{k=1}^K\rho_k\frac{1}{\sqrt{\det(2\pi\mathbf{\Sigma}_k)}}\exp\left[-\frac{1}{2}(\mathbf{x}-\mathbf{m}_k)^T\mathbf{\Sigma}_k^{-1}(\mathbf{x}-\mathbf{m}_k)\right] \tag{390}`

  where $`\rho_k` sum to 1 and the $`\mathbf{\Sigma}_k` all are positive definite.

### Derivatives

> Defining $`p(\mathbf{s}) = \sum_k\rho_k\mathcal{N}_{\mathbf{s}}(\boldsymbol{\mu}_k,\mathbf{\Sigma}_k)` one get

  $$`\frac{\partial\ln p(\mathbf{s})}{\partial\rho_j} = \frac{\rho_j\mathcal{N}_{\mathbf{s}}(\boldsymbol{\mu}_j,\mathbf{\Sigma}_j)}{\sum_k\rho_k\mathcal{N}_{\mathbf{s}}(\boldsymbol{\mu}_k,\mathbf{\Sigma}_k)}\frac{\partial}{\partial\rho_j}\ln[\rho_j\mathcal{N}_{\mathbf{s}}(\boldsymbol{\mu}_j,\mathbf{\Sigma}_j)] \tag{391}`

  $$`= \frac{\rho_j\mathcal{N}_{\mathbf{s}}(\boldsymbol{\mu}_j,\mathbf{\Sigma}_j)}{\sum_k\rho_k\mathcal{N}_{\mathbf{s}}(\boldsymbol{\mu}_k,\mathbf{\Sigma}_k)}\frac{1}{\rho_j} \tag{392}`

  $$`\frac{\partial\ln p(\mathbf{s})}{\partial\boldsymbol{\mu}_j} = \frac{\rho_j\mathcal{N}_{\mathbf{s}}(\boldsymbol{\mu}_j,\mathbf{\Sigma}_j)}{\sum_k\rho_k\mathcal{N}_{\mathbf{s}}(\boldsymbol{\mu}_k,\mathbf{\Sigma}_k)}\frac{\partial}{\partial\boldsymbol{\mu}_j}\ln[\rho_j\mathcal{N}_{\mathbf{s}}(\boldsymbol{\mu}_j,\mathbf{\Sigma}_j)] \tag{393}`

  $$`= \frac{\rho_j\mathcal{N}_{\mathbf{s}}(\boldsymbol{\mu}_j,\mathbf{\Sigma}_j)}{\sum_k\rho_k\mathcal{N}_{\mathbf{s}}(\boldsymbol{\mu}_k,\mathbf{\Sigma}_k)}\left[\mathbf{\Sigma}_j^{-1}(\mathbf{s}-\boldsymbol{\mu}_j)\right] \tag{394}`

  $$`\frac{\partial\ln p(\mathbf{s})}{\partial\mathbf{\Sigma}_j} = \frac{\rho_j\mathcal{N}_{\mathbf{s}}(\boldsymbol{\mu}_j,\mathbf{\Sigma}_j)}{\sum_k\rho_k\mathcal{N}_{\mathbf{s}}(\boldsymbol{\mu}_k,\mathbf{\Sigma}_k)}\frac{\partial}{\partial\mathbf{\Sigma}_j}\ln[\rho_j\mathcal{N}_{\mathbf{s}}(\boldsymbol{\mu}_j,\mathbf{\Sigma}_j)] \tag{395}`
-/

/--
> $$`= \frac{\rho_j\mathcal{N}_{\mathbf{s}}(\boldsymbol{\mu}_j,\mathbf{\Sigma}_j)}{\sum_k\rho_k\mathcal{N}_{\mathbf{s}}(\boldsymbol{\mu}_k,\mathbf{\Sigma}_k)}\frac{1}{2}\left[-\mathbf{\Sigma}_j^{-1}+\mathbf{\Sigma}_j^{-1}(\mathbf{s}-\boldsymbol{\mu}_j)(\mathbf{s}-\boldsymbol{\mu}_j)^T\mathbf{\Sigma}_j^{-1}\right] \tag{396}`
-/
theorem eq_396 : (sorry : Prop) := sorry

/-!
> But $`\rho_k` and $`\mathbf{\Sigma}_k` needs to be constrained.
-/

end MatrixCookbook
