module

set_option doc.verso true

/-!
# Statistics and Probability

## Definition of Moments

> Assume $`\mathbf{x}\in\mathbb{R}^{n\times 1}` is a random variable

### Mean
-/

public section

namespace MatrixCookbook

/--
> The vector of means, $`\mathbf{m}`, is defined by

  $$`(\mathbf{m})_i = \langle x_i\rangle \tag{303}`
-/
theorem eq_303 : (sorry : Prop) := sorry

/-!
### Covariance

> The matrix of covariance $`\mathbf{M}` is defined by

  $$`(\mathbf{M})_{ij} = \langle(x_i-\langle x_i\rangle)(x_j-\langle x_j\rangle)\rangle \tag{304}`

  or alternatively as

  $$`\mathbf{M} = \langle(\mathbf{x}-\mathbf{m})(\mathbf{x}-\mathbf{m})^T\rangle \tag{305}`

### Third moments

> The matrix of third centralized moments – in some contexts referred to as coskewness – is defined using the notation

  $$`m_{ijk}^{(3)} = \langle(x_i-\langle x_i\rangle)(x_j-\langle x_j\rangle)(x_k-\langle x_k\rangle)\rangle \tag{306}`

  as

  $$`\mathbf{M}_3 = \Big[m_{::1}^{(3)}m_{::2}^{(3)}...m_{::n}^{(3)}\Big] \tag{307}`

  where ':' denotes all elements within the given index. $`\mathbf{M}_3` can alternatively be expressed as

  $$`\mathbf{M}_3 = \langle(\mathbf{x}-\mathbf{m})(\mathbf{x}-\mathbf{m})^T\otimes(\mathbf{x}-\mathbf{m})^T\rangle \tag{308}`

### Fourth moments

> The matrix of fourth centralized moments – in some contexts referred to as cokurtosis – is defined using the notation

  $$`m_{ijkl}^{(4)} = \langle(x_i-\langle x_i\rangle)(x_j-\langle x_j\rangle)(x_k-\langle x_k\rangle)(x_l-\langle x_l\rangle)\rangle \tag{309}`

  as

  $$`\mathbf{M}_4 = \Big[m_{::11}^{(4)}m_{::21}^{(4)}...m_{::n1}^{(4)}|m_{::12}^{(4)}m_{::22}^{(4)}...m_{::n2}^{(4)}|...|m_{::1n}^{(4)}m_{::2n}^{(4)}...m_{::nn}^{(4)}\Big] \tag{310}`

  or alternatively as

  $$`\mathbf{M}_4 = \langle(\mathbf{x}-\mathbf{m})(\mathbf{x}-\mathbf{m})^T\otimes(\mathbf{x}-\mathbf{m})^T\otimes(\mathbf{x}-\mathbf{m})^T\rangle \tag{311}`

## Expectation of Linear Combinations

### Linear Forms

> Assume $`\mathbf{X}` and $`\mathbf{x}` to be a matrix and a vector of random variables. Then (see See \[26\])

  $$`E[\mathbf{A}\mathbf{X}\mathbf{B}+\mathbf{C}] = \mathbf{A}E[\mathbf{X}]\mathbf{B} + \mathbf{C} \tag{312}`

  $$`\operatorname{Var}[\mathbf{A}\mathbf{x}] = \mathbf{A}\operatorname{Var}[\mathbf{x}]\mathbf{A}^T \tag{313}`

  $$`\operatorname{Cov}[\mathbf{A}\mathbf{x},\mathbf{B}\mathbf{y}] = \mathbf{A}\operatorname{Cov}[\mathbf{x},\mathbf{y}]\mathbf{B}^T \tag{314}`

  Assume $`\mathbf{x}` to be a stochastic vector with mean $`\mathbf{m}`, then (see \[7\])

  $$`E[\mathbf{A}\mathbf{x}+\mathbf{b}] = \mathbf{A}\mathbf{m} + \mathbf{b} \tag{315}`

  $$`E[\mathbf{A}\mathbf{x}] = \mathbf{A}\mathbf{m} \tag{316}`

  $$`E[\mathbf{x}+\mathbf{b}] = \mathbf{m} + \mathbf{b} \tag{317}`

### Quadratic Forms

> Assume $`\mathbf{A}` is symmetric, $`\mathbf{c} = E[\mathbf{x}]` and $`\mathbf{\Sigma} = \operatorname{Var}[\mathbf{x}]`. Assume also that all coordinates $`x_i` are independent, have the same central moments $`\mu_1, \mu_2, \mu_3, \mu_4` and denote $`\mathbf{a} = \operatorname{diag}(\mathbf{A})`. Then (See \[26\])

  $$`E[\mathbf{x}^T\mathbf{A}\mathbf{x}] = \operatorname{Tr}(\mathbf{A}\mathbf{\Sigma}) + \mathbf{c}^T\mathbf{A}\mathbf{c} \tag{318}`

  $$`\operatorname{Var}[\mathbf{x}^T\mathbf{A}\mathbf{x}] = 2\mu_2^2\operatorname{Tr}(\mathbf{A}^2) + 4\mu_2\mathbf{c}^T\mathbf{A}^2\mathbf{c} + 4\mu_3\mathbf{c}^T\mathbf{A}\mathbf{a} + (\mu_4-3\mu_2^2)\mathbf{a}^T\mathbf{a} \tag{319}`

  Also, assume $`\mathbf{x}` to be a stochastic vector with mean $`\mathbf{m}`, and covariance $`\mathbf{M}`. Then (see \[7\])

  $$`E[(\mathbf{A}\mathbf{x}+\mathbf{a})(\mathbf{B}\mathbf{x}+\mathbf{b})^T] = \mathbf{A}\mathbf{M}\mathbf{B}^T + (\mathbf{A}\mathbf{m}+\mathbf{a})(\mathbf{B}\mathbf{m}+\mathbf{b})^T \tag{320}`

  $$`E[\mathbf{x}\mathbf{x}^T] = \mathbf{M} + \mathbf{m}\mathbf{m}^T \tag{321}`

  $$`E[\mathbf{x}\mathbf{a}^T\mathbf{x}] = (\mathbf{M}+\mathbf{m}\mathbf{m}^T)\mathbf{a} \tag{322}`

  $$`E[\mathbf{x}^T\mathbf{a}\mathbf{x}^T] = \mathbf{a}^T(\mathbf{M}+\mathbf{m}\mathbf{m}^T) \tag{323}`

  $$`E[(\mathbf{A}\mathbf{x})(\mathbf{A}\mathbf{x})^T] = \mathbf{A}(\mathbf{M}+\mathbf{m}\mathbf{m}^T)\mathbf{A}^T \tag{324}`

  $$`E[(\mathbf{x}+\mathbf{a})(\mathbf{x}+\mathbf{a})^T] = \mathbf{M} + (\mathbf{m}+\mathbf{a})(\mathbf{m}+\mathbf{a})^T \tag{325}`

  $$`E[(\mathbf{A}\mathbf{x}+\mathbf{a})^T(\mathbf{B}\mathbf{x}+\mathbf{b})] = \operatorname{Tr}(\mathbf{A}\mathbf{M}\mathbf{B}^T) + (\mathbf{A}\mathbf{m}+\mathbf{a})^T(\mathbf{B}\mathbf{m}+\mathbf{b}) \tag{326}`

  $$`E[\mathbf{x}^T\mathbf{x}] = \operatorname{Tr}(\mathbf{M}) + \mathbf{m}^T\mathbf{m} \tag{327}`

  $$`E[\mathbf{x}^T\mathbf{A}\mathbf{x}] = \operatorname{Tr}(\mathbf{A}\mathbf{M}) + \mathbf{m}^T\mathbf{A}\mathbf{m} \tag{328}`

  $$`E[(\mathbf{A}\mathbf{x})^T(\mathbf{A}\mathbf{x})] = \operatorname{Tr}(\mathbf{A}\mathbf{M}\mathbf{A}^T) + (\mathbf{A}\mathbf{m})^T(\mathbf{A}\mathbf{m}) \tag{329}`

  $$`E[(\mathbf{x}+\mathbf{a})^T(\mathbf{x}+\mathbf{a})] = \operatorname{Tr}(\mathbf{M}) + (\mathbf{m}+\mathbf{a})^T(\mathbf{m}+\mathbf{a}) \tag{330}`

  See \[7\].

### Cubic Forms

> Assume $`\mathbf{x}` to be a stochastic vector with independent coordinates, mean $`\mathbf{m}`, covariance $`\mathbf{M}` and central moments $`\mathbf{v}_3 = E[(\mathbf{x}-\mathbf{m})^3]`. Then (see \[7\])

  $$`\begin{aligned} E[(\mathbf{A}\mathbf{x}+\mathbf{a})(\mathbf{B}\mathbf{x}+\mathbf{b})^T(\mathbf{C}\mathbf{x}+\mathbf{c})] &= \mathbf{A}\operatorname{diag}(\mathbf{B}^T\mathbf{C})\mathbf{v}_3 \\ &\quad + \operatorname{Tr}(\mathbf{B}\mathbf{M}\mathbf{C}^T)(\mathbf{A}\mathbf{m}+\mathbf{a}) \\ &\quad + \mathbf{A}\mathbf{M}\mathbf{C}^T(\mathbf{B}\mathbf{m}+\mathbf{b}) \\ &\quad + (\mathbf{A}\mathbf{M}\mathbf{B}^T+(\mathbf{A}\mathbf{m}+\mathbf{a})(\mathbf{B}\mathbf{m}+\mathbf{b})^T)(\mathbf{C}\mathbf{m}+\mathbf{c}) \\ E[\mathbf{x}\mathbf{x}^T\mathbf{x}] &= \mathbf{v}_3 + 2\mathbf{M}\mathbf{m} + (\operatorname{Tr}(\mathbf{M})+\mathbf{m}^T\mathbf{m})\mathbf{m} \\ E[(\mathbf{A}\mathbf{x}+\mathbf{a})(\mathbf{A}\mathbf{x}+\mathbf{a})^T(\mathbf{A}\mathbf{x}+\mathbf{a})] &= \mathbf{A}\operatorname{diag}(\mathbf{A}^T\mathbf{A})\mathbf{v}_3 \\ &\quad + [2\mathbf{A}\mathbf{M}\mathbf{A}^T + (\mathbf{A}\mathbf{x}+\mathbf{a})(\mathbf{A}\mathbf{x}+\mathbf{a})^T](\mathbf{A}\mathbf{m}+\mathbf{a}) \\ &\quad + \operatorname{Tr}(\mathbf{A}\mathbf{M}\mathbf{A}^T)(\mathbf{A}\mathbf{m}+\mathbf{a}) \\ E[(\mathbf{A}\mathbf{x}+\mathbf{a})\mathbf{b}^T(\mathbf{C}\mathbf{x}+\mathbf{c})(\mathbf{D}\mathbf{x}+\mathbf{d})^T] &= (\mathbf{A}\mathbf{x}+\mathbf{a})\mathbf{b}^T(\mathbf{C}\mathbf{M}\mathbf{D}^T+(\mathbf{C}\mathbf{m}+\mathbf{c})(\mathbf{D}\mathbf{m}+\mathbf{d})^T) \\ &\quad + (\mathbf{A}\mathbf{M}\mathbf{C}^T+(\mathbf{A}\mathbf{m}+\mathbf{a})(\mathbf{C}\mathbf{m}+\mathbf{c})^T)\mathbf{b}(\mathbf{D}\mathbf{m}+\mathbf{d})^T \\ &\quad + \mathbf{b}^T(\mathbf{C}\mathbf{m}+\mathbf{c})(\mathbf{A}\mathbf{M}\mathbf{D}^T-(\mathbf{A}\mathbf{m}+\mathbf{a})(\mathbf{D}\mathbf{m}+\mathbf{d})^T) \end{aligned}`

## Weighted Scalar Variable

> Assume $`\mathbf{x}\in\mathbb{R}^{n\times 1}` is a random variable, $`\mathbf{w}\in\mathbb{R}^{n\times 1}` is a vector of constants and $`y` is the linear combination $`y = \mathbf{w}^T\mathbf{x}`. Assume further that $`\mathbf{m}, \mathbf{M}_2, \mathbf{M}_3, \mathbf{M}_4` denotes the mean, covariance, and central third and fourth moment matrix of the variable $`\mathbf{x}`. Then it holds that

  $$`\langle y\rangle = \mathbf{w}^T\mathbf{m} \tag{331}`

  $$`\langle(y-\langle y\rangle)^2\rangle = \mathbf{w}^T\mathbf{M}_2\mathbf{w} \tag{332}`

  $$`\langle(y-\langle y\rangle)^3\rangle = \mathbf{w}^T\mathbf{M}_3\mathbf{w}\otimes\mathbf{w} \tag{333}`
-/

/--
> $$`\langle(y-\langle y\rangle)^4\rangle = \mathbf{w}^T\mathbf{M}_4\mathbf{w}\otimes\mathbf{w}\otimes\mathbf{w} \tag{334}`
-/
theorem eq_334 : (sorry : Prop) := sorry

end MatrixCookbook
