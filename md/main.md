

\section{Notation and Nomenclature}
A Matrix
$\mathbf{A}_{i j} \quad$ Matrix indexed for some purpose
$\mathbf{A}_{i} \quad$ Matrix indexed for some purpose
$\mathbf{A}^{i j} \quad$ Matrix indexed for some purpose
$\mathbf{A}^{n} \quad$ Matrix indexed for some purpose or
The n.th power of a square matrix
$\mathbf{A}^{-1}$ The inverse matrix of the matrix $\mathbf{A}$
$\mathbf{A}^{+} \quad$ The pseudo inverse matrix of the matrix $\mathbf{A}$ (see Sec. 3.6
$\mathbf{A}^{1 / 2} \quad$ The square root of a matrix (if unique), not elementwise
$(\mathbf{A})_{i j} \quad$ The $(i, j)$.th entry of the matrix $\mathbf{A}$
$A_{i j} \quad$ The $(i, j)$.th entry of the matrix $\mathbf{A}$
$[\mathbf{A}]_{i j} \quad$ The $i j$-submatrix, i.e. $\mathbf{A}$ with i.th row and j.th column deleted
a Vector (column-vector)
$\mathbf{a}_{i} \quad$ Vector indexed for some purpose
$a_{i} \quad$ The i.th element of the vector $\mathbf{a}$
a Scalar
$\Re z \quad$ Real part of a scalar
$\Re \mathbf{z} \quad$ Real part of a vector
$\Re \mathbf{Z} \quad$ Real part of a matrix
$\Im z \quad$ Imaginary part of a scalar
Sz Imaginary part of a vector
SZ Imaginary part of a matrix
$\operatorname{det}(\mathbf{A}) \quad$ Determinant of $\mathbf{A}$
$\operatorname{Tr}(\mathbf{A}) \quad$ Trace of the matrix $\mathbf{A}$
$\operatorname{diag}(\mathbf{A}) \quad$ Diagonal matrix of the matrix $\mathbf{A}$, i.e. $(\operatorname{diag}(\mathbf{A}))_{i j}=\delta_{i j} A_{i j}$
$\operatorname{eig}(\mathbf{A}) \quad$ Eigenvalues of the matrix $\mathbf{A}$
$\operatorname{vec}(\mathbf{A})$ The vector-version of the matrix $\mathbf{A}$ (see Sec. 10.2.2)
sup Supremum of a set
$\|\mathbf{A}\|$ Matrix norm (subscript if any denotes what norm)
$\mathbf{A}^{T} \quad$ Transposed matrix
$\mathbf{A}^{-T} \quad$ The inverse of the transposed and vice versa, $\mathbf{A}^{-T}=\left(\mathbf{A}^{-1}\right)^{T}=\left(\mathbf{A}^{T}\right)^{-1}$.
$\mathbf{A}^{*} \quad$ Complex conjugated matrix
$\mathbf{A}^{H} \quad$ Transposed and complex conjugated matrix (Hermitian)

$\mathbf{A} \circ \mathbf{B}$ Hadamard (elementwise) product

$\mathbf{A} \otimes \mathbf{B} \quad$ Kronecker product

0 The null matrix. Zero in all entries.

I The identity matrix

$\mathbf{J}^{i j}$ The single-entry matrix, 1 at $(i, j)$ and zero elsewhere

$\boldsymbol{\Sigma} \quad$ A positive definite matrix

$\Lambda$ A diagonal matrix 

\section{Basics}

$$
\begin{aligned}
(\mathbf{A B})^{-1} & =\mathbf{B}^{-1} \mathbf{A}^{-1} \\
(\mathbf{A B C} \ldots)^{-1} & =\ldots \mathbf{C}^{-1} \mathbf{B}^{-1} \mathbf{A}^{-1} \\
\left(\mathbf{A}^{T}\right)^{-1} & =\left(\mathbf{A}^{-1}\right)^{T} \\
(\mathbf{A}+\mathbf{B})^{T} & =\mathbf{A}^{T}+\mathbf{B}^{T} \\
(\mathbf{A B})^{T} & =\mathbf{B}^{T} \mathbf{A}^{T} \\
(\mathbf{A B C} \ldots)^{T} & =\ldots \mathbf{C}^{T} \mathbf{B}^{T} \mathbf{A}^{T} \\
\left(\mathbf{A}^{H}\right)^{-1} & =\left(\mathbf{A}^{-1}\right)^{H} \\
(\mathbf{A}+\mathbf{B})^{H} & =\mathbf{A}^{H}+\mathbf{B}^{H} \\
(\mathbf{A B})^{H} & =\mathbf{B}^{H} \mathbf{A}^{H} \\
(\mathbf{A B C} \ldots)^{H} & =\ldots \mathbf{C}^{H} \mathbf{B}^{H} \mathbf{A}^{H}
\end{aligned}
$$

\subsection{Trace}

$$
\begin{aligned}
\operatorname{Tr}(\mathbf{A}) & =\sum_{i} A_{i i} \\
\operatorname{Tr}(\mathbf{A}) & =\sum_{i} \lambda_{i}, \quad \lambda_{i}=\operatorname{eig}(\mathbf{A}) \\
\operatorname{Tr}(\mathbf{A}) & =\operatorname{Tr}\left(\mathbf{A}^{T}\right) \\
\operatorname{Tr}(\mathbf{A B}) & =\operatorname{Tr}(\mathbf{B} \mathbf{A}) \\
\operatorname{Tr}(\mathbf{A}+\mathbf{B}) & =\operatorname{Tr}(\mathbf{A})+\operatorname{Tr}(\mathbf{B}) \\
\operatorname{Tr}(\mathbf{A B C}) & =\operatorname{Tr}(\mathbf{B C A})=\operatorname{Tr}(\mathbf{C A B}) \\
\mathbf{a}^{T} \mathbf{a} & =\operatorname{Tr}\left(\mathbf{a a}^{T}\right)
\end{aligned}
$$

\subsection{Determinant}

Let $\mathbf{A}$ be an $n \times n$ matrix.

$$
\begin{aligned}
\operatorname{det}(\mathbf{A}) & =\prod_{i} \lambda_{i} \quad \lambda_{i}=\operatorname{eig}(\mathbf{A}) \\
\operatorname{det}(c \mathbf{A}) & =c^{n} \operatorname{det}(\mathbf{A}), \quad \text { if } \mathbf{A} \in \mathbb{R}^{n \times n} \\
\operatorname{det}\left(\mathbf{A}^{T}\right) & =\operatorname{det}(\mathbf{A}) \\
\operatorname{det}(\mathbf{A B}) & =\operatorname{det}(\mathbf{A}) \operatorname{det}(\mathbf{B}) \\
\operatorname{det}\left(\mathbf{A}^{-1}\right) & =1 / \operatorname{det}(\mathbf{A}) \\
\operatorname{det}\left(\mathbf{A}^{n}\right) & =\operatorname{det}(\mathbf{A})^{n} \\
\operatorname{det}\left(\mathbf{I}+\mathbf{u v}^{T}\right) & =1+\mathbf{u}^{T} \mathbf{v}
\end{aligned}
$$

For $n=2$ :

$$
\operatorname{det}(\mathbf{I}+\mathbf{A})=1+\operatorname{det}(\mathbf{A})+\operatorname{Tr}(\mathbf{A})
$$

For $n=3$ :

$$
\operatorname{det}(\mathbf{I}+\mathbf{A})=1+\operatorname{det}(\mathbf{A})+\operatorname{Tr}(\mathbf{A})+\frac{1}{2} \operatorname{Tr}(\mathbf{A})^{2}-\frac{1}{2} \operatorname{Tr}\left(\mathbf{A}^{2}\right)
$$

For $n=4$ :

$$
\begin{aligned}
\operatorname{det}(\mathbf{I}+\mathbf{A})= & 1+\operatorname{det}(\mathbf{A})+\operatorname{Tr}(\mathbf{A})+\frac{1}{2} \\
& +\operatorname{Tr}(\mathbf{A})^{2}-\frac{1}{2} \operatorname{Tr}\left(\mathbf{A}^{2}\right) \\
& +\frac{1}{6} \operatorname{Tr}(\mathbf{A})^{3}-\frac{1}{2} \operatorname{Tr}(\mathbf{A}) \operatorname{Tr}\left(\mathbf{A}^{2}\right)+\frac{1}{3} \operatorname{Tr}\left(\mathbf{A}^{3}\right)
\end{aligned}
$$

For small $\varepsilon$, the following approximation holds

$$
\operatorname{det}(\mathbf{I}+\varepsilon \mathbf{A}) \cong 1+\operatorname{det}(\mathbf{A})+\varepsilon \operatorname{Tr}(\mathbf{A})+\frac{1}{2} \varepsilon^{2} \operatorname{Tr}(\mathbf{A})^{2}-\frac{1}{2} \varepsilon^{2} \operatorname{Tr}\left(\mathbf{A}^{2}\right)
$$

\subsection{The Special Case $2 \times 2$}

Consider the matrix $\mathbf{A}$

$$
\mathbf{A}=\left[\begin{array}{ll}
A_{11} & A_{12} \\
A_{21} & A_{22}
\end{array}\right]
$$

Determinant and trace

$$
\begin{gathered}
\operatorname{det}(\mathbf{A})=A_{11} A_{22}-A_{12} A_{21} \\
\operatorname{Tr}(\mathbf{A})=A_{11}+A_{22}
\end{gathered}
$$

Eigenvalues

$$
\begin{array}{cl}
\lambda_{1}=\frac{\operatorname{Tr}(\mathbf{A})+\sqrt{\operatorname{Tr}(\mathbf{A})^{2}-4 \operatorname{det}(\mathbf{A})}}{2} & \lambda_{2}=\frac{\operatorname{Tr}(\mathbf{A})-\sqrt{\operatorname{Tr}(\mathbf{A})^{2}-4 \operatorname{det}(\mathbf{A})}}{2} \\
\lambda_{1}+\lambda_{2}=\operatorname{Tr}(\mathbf{A}) & \lambda_{1} \lambda_{2}=\operatorname{det}(\mathbf{A})
\end{array}
$$$$
\lambda^{2}-\lambda \cdot \operatorname{Tr}(\mathbf{A})+\operatorname{det}(\mathbf{A})=0
$$

Eigenvectors

$$
\mathbf{v}_{1} \propto\left[\begin{array}{c}
A_{12} \\
\lambda_{1}-A_{11}
\end{array}\right] \quad \mathbf{v}_{2} \propto\left[\begin{array}{c}
A_{12} \\
\lambda_{2}-A_{11}
\end{array}\right]
$$

Inverse

$$
\mathbf{A}^{-1}=\frac{1}{\operatorname{det}(\mathbf{A})}\left[\begin{array}{cc}
A_{22} & -A_{12} \\
-A_{21} & A_{11}
\end{array}\right]
$$



\section{Derivatives}

This section is covering differentiation of a number of expressions with respect to a matrix $\mathbf{X}$. Note that it is always assumed that $\mathbf{X}$ has no special structure, i.e. that the elements of $\mathbf{X}$ are independent (e.g. not symmetric, Toeplitz, positive definite). See section 2.8 for differentiation of structured matrices. The basic assumptions can be written in a formula as

$$
\frac{\partial X_{k l}}{\partial X_{i j}}=\delta_{i k} \delta_{l j}
$$

that is for e.g. vector forms,

$$
\left[\frac{\partial \mathbf{x}}{\partial y}\right]_{i}=\frac{\partial x_{i}}{\partial y} \quad\left[\frac{\partial x}{\partial \mathbf{y}}\right]_{i}=\frac{\partial x}{\partial y_{i}} \quad\left[\frac{\partial \mathbf{x}}{\partial \mathbf{y}}\right]_{i j}=\frac{\partial x_{i}}{\partial y_{j}}
$$

The following rules are general and very useful when deriving the differential of an expression ([19]):

$$
\begin{array}{rlr}
\partial \mathbf{A} & =0 \\
\partial(\alpha \mathbf{X}) & =\alpha \partial \mathbf{X} \\
\partial(\mathbf{X}+\mathbf{Y}) & =\partial \mathbf{X}+\partial \mathbf{Y} \\
\partial(\operatorname{Tr}(\mathbf{X})) & =\operatorname{Tr}(\partial \mathbf{X}) \\
\partial(\mathbf{X} \mathbf{Y}) & =(\partial \mathbf{X}) \mathbf{Y}+\mathbf{X}(\partial \mathbf{Y}) \\
\partial(\mathbf{X} \circ \mathbf{Y}) & =(\partial \mathbf{X}) \circ \mathbf{Y}+\mathbf{X} \circ(\partial \mathbf{Y}) \\
\partial(\mathbf{X} \otimes \mathbf{Y}) & =(\partial \mathbf{X}) \otimes \mathbf{Y}+\mathbf{X} \otimes(\partial \mathbf{Y}) \\
\partial\left(\mathbf{X}^{-1}\right) & =-\mathbf{X}^{-1}(\partial \mathbf{X}) \mathbf{X}^{-1} \\
\partial(\operatorname{det}(\mathbf{X})) & =\operatorname{Tr}(\operatorname{adj}(\mathbf{X}) \partial \mathbf{X}) \\
\partial(\operatorname{det}(\mathbf{X})) & =\operatorname{det}(\mathbf{X}) \operatorname{Tr}\left(\mathbf{X}^{-1} \partial \mathbf{X}\right) \\
\partial(\ln (\operatorname{det}(\mathbf{X}))) & =\operatorname{Tr}\left(\mathbf{X}^{-1} \partial \mathbf{X}\right) \\
\partial \mathbf{X}^{T} & =(\partial \mathbf{X})^{T} \\
\partial \mathbf{X}^{H} & =(\partial \mathbf{X})^{H}
\end{array}
$$

\subsection{Derivatives of a Determinant}

\subsubsection{General form}

$$
\begin{aligned}
& \frac{\partial \operatorname{det}(\mathbf{Y})}{\partial x}=\operatorname{det}(\mathbf{Y}) \operatorname{Tr}\left[\mathbf{Y}^{-1} \frac{\partial \mathbf{Y}}{\partial x}\right] \\
& \sum_{k} \frac{\partial \operatorname{det}(\mathbf{X})}{\partial X_{i k}} X_{j k}=\delta_{i j} \operatorname{det}(\mathbf{X}) \\
& \frac{\partial^{2} \operatorname{det}(\mathbf{Y})}{\partial x^{2}}=\operatorname{det}(\mathbf{Y})\left[\operatorname{Tr}\left[\mathbf{Y}^{-1} \frac{\partial \frac{\partial \mathbf{Y}}{\partial x}}{\partial x}\right]\right. \\
& +\operatorname{Tr}\left[\mathbf{Y}^{-1} \frac{\partial \mathbf{Y}}{\partial x}\right] \operatorname{Tr}\left[\mathbf{Y}^{-1} \frac{\partial \mathbf{Y}}{\partial x}\right] \\
& \left.-\operatorname{Tr}\left[\left(\mathbf{Y}^{-1} \frac{\partial \mathbf{Y}}{\partial x}\right)\left(\mathbf{Y}^{-1} \frac{\partial \mathbf{Y}}{\partial x}\right)\right]\right]
\end{aligned}
$$



\subsubsection{Linear forms}

$$
\begin{aligned}
\frac{\partial \operatorname{det}(\mathbf{X})}{\partial \mathbf{X}} & =\operatorname{det}(\mathbf{X})\left(\mathbf{X}^{-1}\right)^{T} \\
\sum_{k} \frac{\partial \operatorname{det}(\mathbf{X})}{\partial X_{i k}} X_{j k} & =\delta_{i j} \operatorname{det}(\mathbf{X}) \\
\frac{\partial \operatorname{det}(\mathbf{A} \mathbf{X B})}{\partial \mathbf{X}} & =\operatorname{det}(\mathbf{A X B})\left(\mathbf{X}^{-1}\right)^{T}=\operatorname{det}(\mathbf{A} \mathbf{X B})\left(\mathbf{X}^{T}\right)^{-1}
\end{aligned}
$$

\subsubsection{Square forms}

If $\mathbf{X}$ is square and invertible, then

$$
\frac{\partial \operatorname{det}\left(\mathbf{X}^{T} \mathbf{A} \mathbf{X}\right)}{\partial \mathbf{X}}=2 \operatorname{det}\left(\mathbf{X}^{T} \mathbf{A} \mathbf{X}\right) \mathbf{X}^{-T}
$$

If $\mathbf{X}$ is not square but $\mathbf{A}$ is symmetric, then

$$
\frac{\partial \operatorname{det}\left(\mathbf{X}^{T} \mathbf{A} \mathbf{X}\right)}{\partial \mathbf{X}}=2 \operatorname{det}\left(\mathbf{X}^{T} \mathbf{A} \mathbf{X}\right) \mathbf{A} \mathbf{X}\left(\mathbf{X}^{T} \mathbf{A} \mathbf{X}\right)^{-1}
$$

If $\mathbf{X}$ is not square and $\mathbf{A}$ is not symmetric, then

$$
\frac{\partial \operatorname{det}\left(\mathbf{X}^{T} \mathbf{A X}\right)}{\partial \mathbf{X}}=\operatorname{det}\left(\mathbf{X}^{T} \mathbf{A} \mathbf{X}\right)\left(\mathbf{A} \mathbf{X}\left(\mathbf{X}^{T} \mathbf{A} \mathbf{X}\right)^{-1}+\mathbf{A}^{T} \mathbf{X}\left(\mathbf{X}^{T} \mathbf{A}^{T} \mathbf{X}\right)^{-1}\right)
$$

\subsubsection{Other nonlinear forms}

Some special cases are (See 9, 7])

$$
\begin{aligned}
\frac{\partial \ln \operatorname{det}\left(\mathbf{X}^{T} \mathbf{X}\right) \mid}{\partial \mathbf{X}} & =2\left(\mathbf{X}^{+}\right)^{T} \\
\frac{\partial \ln \operatorname{det}\left(\mathbf{X}^{T} \mathbf{X}\right)}{\partial \mathbf{X}^{+}} & =-2 \mathbf{X}^{T} \\
\frac{\partial \ln |\operatorname{det}(\mathbf{X})|}{\partial \mathbf{X}} & =\left(\mathbf{X}^{-1}\right)^{T}=\left(\mathbf{X}^{T}\right)^{-1} \\
\frac{\partial \operatorname{det}\left(\mathbf{X}^{k}\right)}{\partial \mathbf{X}} & =k \operatorname{det}\left(\mathbf{X}^{k}\right) \mathbf{X}^{-T}
\end{aligned}
$$

\subsection{Derivatives of an Inverse}

From [27] we have the basic identity

$$
\frac{\partial \mathbf{Y}^{-1}}{\partial x}=-\mathbf{Y}^{-1} \frac{\partial \mathbf{Y}}{\partial x} \mathbf{Y}^{-1}
$$

from which it follows

$$
\begin{aligned}
\frac{\partial\left(\mathbf{X}^{-1}\right)_{k l}}{\partial X_{i j}} & =-\left(\mathbf{X}^{-1}\right)_{k i}\left(\mathbf{X}^{-1}\right)_{j l} \\
\frac{\partial \mathbf{a}^{T} \mathbf{X}^{-1} \mathbf{b}}{\partial \mathbf{X}} & =-\mathbf{X}^{-T} \mathbf{a} \mathbf{b}^{T} \mathbf{X}^{-T} \\
\frac{\partial \operatorname{det}\left(\mathbf{X}^{-1}\right)}{\partial \mathbf{X}} & =-\operatorname{det}\left(\mathbf{X}^{-1}\right)\left(\mathbf{X}^{-1}\right)^{T} \\
\frac{\partial \operatorname{Tr}\left(\mathbf{A} \mathbf{X}^{-1} \mathbf{B}\right)}{\partial \mathbf{X}} & =-\left(\mathbf{X}^{-1} \mathbf{B} \mathbf{A} \mathbf{X}^{-1}\right)^{T} \\
\frac{\partial \operatorname{Tr}\left((\mathbf{X}+\mathbf{A})^{-1}\right)}{\partial \mathbf{X}} & =-\left((\mathbf{X}+\mathbf{A})^{-1}(\mathbf{X}+\mathbf{A})^{-1}\right)^{T}
\end{aligned}
$$

From 32 we have the following result: Let $\mathbf{A}$ be an $n \times n$ invertible square matrix, $\mathbf{W}$ be the inverse of $\mathbf{A}$, and $J(\mathbf{A})$ is an $n \times n$-variate and differentiable function with respect to $\mathbf{A}$, then the partial differentials of $J$ with respect to $\mathbf{A}$ and W satisfy

$$
\frac{\partial J}{\partial \mathbf{A}}=-\mathbf{A}^{-T} \frac{\partial J}{\partial \mathbf{W}} \mathbf{A}^{-T}
$$

\subsection{Derivatives of Eigenvalues}

$$
\begin{aligned}
& \frac{\partial}{\partial \mathbf{X}} \sum \operatorname{eig}(\mathbf{X})=\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}(\mathbf{X})=\mathbf{I} \\
& \frac{\partial}{\partial \mathbf{X}} \prod \operatorname{eig}(\mathbf{X})=\frac{\partial}{\partial \mathbf{X}} \operatorname{det}(\mathbf{X})=\operatorname{det}(\mathbf{X}) \mathbf{X}^{-T}
\end{aligned}
$$

If $\mathbf{A}$ is real and symmetric, $\lambda_{i}$ and $\mathbf{v}_{i}$ are distinct eigenvalues and eigenvectors of $\mathbf{A}$ (see 276$)$ with $\mathbf{v}_{i}^{T} \mathbf{v}_{i}=1$, then 33

$$
\begin{aligned}
& \partial \lambda_{i}=\mathbf{v}_{i}^{T} \partial(\mathbf{A}) \mathbf{v}_{i} \\
& \partial \mathbf{v}_{i}=\left(\lambda_{i} \mathbf{I}-\mathbf{A}\right)^{+} \partial(\mathbf{A}) \mathbf{v}_{i}
\end{aligned}
$$

\subsection{Derivatives of Matrices, Vectors and Scalar Forms}

\subsubsection{First Order}

$$
\begin{aligned}
& \frac{\partial \mathbf{x}^{T} \mathbf{a}}{\partial \mathbf{x}}=\frac{\partial \mathbf{a}^{T} \mathbf{x}}{\partial \mathbf{x}}=\mathbf{a} \\
& \frac{\partial \mathbf{a}^{T} \mathbf{X} \mathbf{b}}{\partial \mathbf{X}}=\mathbf{a b}^{T} \\
& \frac{\partial \mathbf{a}^{T} \mathbf{X}^{T} \mathbf{b}}{\partial \mathbf{X}}=\mathbf{b a}^{T} \\
& \frac{\partial \mathbf{a}^{T} \mathbf{X} \mathbf{a}}{\partial \mathbf{X}}=\frac{\partial \mathbf{a}^{T} \mathbf{X}^{T} \mathbf{a}}{\partial \mathbf{X}}=\mathbf{a a}^{T} \\
& \frac{\partial \mathbf{X}}{\partial X_{i j}}=\mathbf{J}^{i j} \\
& \frac{\partial(\mathbf{X} \mathbf{A})_{i j}}{\partial X_{m n}}=\delta_{i m}(\mathbf{A})_{n j}=\left(\mathbf{J}^{m n} \mathbf{A}\right)_{i j} \\
& \frac{\partial\left(\mathbf{X}^{T} \mathbf{A}\right)_{i j}}{\partial X_{m n}}=\delta_{i n}(\mathbf{A})_{m j}=\left(\mathbf{J}^{n m} \mathbf{A}\right)_{i j}
\end{aligned}
$$



\subsubsection{Second Order}

$$
\begin{aligned}
\frac{\partial}{\partial X_{i j}} \sum_{k l m n} X_{k l} X_{m n} & =2 \sum_{k l} X_{k l} \\
\frac{\partial \mathbf{b}^{T} \mathbf{X}^{T} \mathbf{X} \mathbf{c}}{\partial \mathbf{X}} & =\mathbf{X}\left(\mathbf{b} \mathbf{c}^{T}+\mathbf{c b}^{T}\right) \\
\frac{\partial(\mathbf{B} \mathbf{x}+\mathbf{b})^{T} \mathbf{C}(\mathbf{D x}+\mathbf{d})}{\partial \mathbf{x}} & =\mathbf{B}^{T} \mathbf{C}(\mathbf{D} \mathbf{x}+\mathbf{d})+\mathbf{D}^{T} \mathbf{C}^{T}(\mathbf{B x}+\mathbf{b}) \\
\frac{\partial\left(\mathbf{X}^{T} \mathbf{B} \mathbf{X}\right)_{k l}}{\partial X_{i j}} & =\delta_{l j}\left(\mathbf{X}^{T} \mathbf{B}\right)_{k i}+\delta_{k j}(\mathbf{B} \mathbf{X})_{i l} \\
\frac{\partial\left(\mathbf{X}^{T} \mathbf{B X}\right)}{\partial X_{i j}} & =\mathbf{X}^{T} \mathbf{B} \mathbf{J}^{i j}+\mathbf{J}^{j i} \mathbf{B X} \quad\left(\mathbf{J}^{i j}\right)_{k l}=\delta_{i k} \delta_{j l}
\end{aligned}
$$

See Sec 9.7 for useful properties of the Single-entry matrix $\mathbf{J}^{i j}$

$$
\begin{aligned}
\frac{\partial \mathbf{x}^{T} \mathbf{B} \mathbf{x}}{\partial \mathbf{x}} & =\left(\mathbf{B}+\mathbf{B}^{T}\right) \mathbf{x} \\
\frac{\partial \mathbf{b}^{T} \mathbf{X}^{T} \mathbf{D} \mathbf{X} \mathbf{c}}{\partial \mathbf{X}} & =\mathbf{D}^{T} \mathbf{X} \mathbf{b ^ { T }} \mathbf{c}^{T}+\mathbf{D} \mathbf{X} \mathbf{c b}^{T} \\
\frac{\partial}{\partial \mathbf{X}}(\mathbf{X} \mathbf{b}+\mathbf{c})^{T} \mathbf{D}(\mathbf{X} \mathbf{b}+\mathbf{c}) & =\left(\mathbf{D}+\mathbf{D}^{T}\right)(\mathbf{X} \mathbf{b}+\mathbf{c}) \mathbf{b}^{T}
\end{aligned}
$$

Assume $\mathbf{W}$ is symmetric, then

$$
\begin{aligned}
\frac{\partial}{\partial \mathbf{s}}(\mathbf{x}-\mathbf{A} \mathbf{s})^{T} \mathbf{W}(\mathbf{x}-\mathbf{A} \mathbf{s}) & =-2 \mathbf{A}^{T} \mathbf{W}(\mathbf{x}-\mathbf{A} \mathbf{s}) \\
\frac{\partial}{\partial \mathbf{x}}(\mathbf{x}-\mathbf{s})^{T} \mathbf{W}(\mathbf{x}-\mathbf{s}) & =2 \mathbf{W}(\mathbf{x}-\mathbf{s}) \\
\frac{\partial}{\partial \mathbf{s}}(\mathbf{x}-\mathbf{s})^{T} \mathbf{W}(\mathbf{x}-\mathbf{s}) & =-2 \mathbf{W}(\mathbf{x}-\mathbf{s}) \\
\frac{\partial}{\partial \mathbf{x}}(\mathbf{x}-\mathbf{A} \mathbf{s})^{T} \mathbf{W}(\mathbf{x}-\mathbf{A} \mathbf{s}) & =2 \mathbf{W}(\mathbf{x}-\mathbf{A} \mathbf{s}) \\
\frac{\partial}{\partial \mathbf{A}}(\mathbf{x}-\mathbf{A} \mathbf{s})^{T} \mathbf{W}(\mathbf{x}-\mathbf{A} \mathbf{s}) & =-2 \mathbf{W}(\mathbf{x}-\mathbf{A} \mathbf{s}) \mathbf{s}^{T}
\end{aligned}
$$

As a case with complex values the following holds

$$
\frac{\partial\left(a-\mathbf{x}^{H} \mathbf{b}\right)^{2}}{\partial \mathbf{x}}=-2 \mathbf{b}\left(a-\mathbf{x}^{H} \mathbf{b}\right)^{*}
$$

This formula is also known from the LMS algorithm 14

\subsubsection{Higher-order and non-linear}

$$
\frac{\partial\left(\mathbf{X}^{n}\right)_{k l}}{\partial X_{i j}}=\sum_{r=0}^{n-1}\left(\mathbf{X}^{r} \mathbf{J}^{i j} \mathbf{X}^{n-1-r}\right)_{k l}
$$

For proof of the above, see B.1.3

$$
\frac{\partial}{\partial \mathbf{X}} \mathbf{a}^{T} \mathbf{X}^{n} \mathbf{b}=\sum_{r=0}^{n-1}\left(\mathbf{X}^{r}\right)^{T} \mathbf{a b}^{T}\left(\mathbf{X}^{n-1-r}\right)^{T}
$$



$$
\begin{aligned}
\frac{\partial}{\partial \mathbf{X}} \mathbf{a}^{T}\left(\mathbf{X}^{n}\right)^{T} \mathbf{X}^{n} \mathbf{b}=\sum_{r=0}^{n-1}[ & \mathbf{X}^{n-1-r} \mathbf{a b ^ { T }}\left(\mathbf{X}^{n}\right)^{T} \mathbf{X}^{r} \\
& \left.+\left(\mathbf{X}^{r}\right)^{T} \mathbf{X}^{n} \mathbf{a} \mathbf{b}^{T}\left(\mathbf{X}^{n-1-r}\right)^{T}\right]
\end{aligned}
$$

See B.1.3 for a proof.

Assume $\mathbf{s}$ and $\mathbf{r}$ are functions of $\mathbf{x}$, i.e. $\mathbf{s}=\mathbf{s}(\mathbf{x}), \mathbf{r}=\mathbf{r}(\mathbf{x})$, and that $\mathbf{A}$ is a constant, then

$$
\begin{aligned}
\frac{\partial}{\partial \mathbf{x}} \mathbf{s}^{T} \mathbf{A} \mathbf{r} & =\left[\frac{\partial \mathbf{s}}{\partial \mathbf{x}}\right]^{T} \mathbf{A} \mathbf{r}+\left[\frac{\partial \mathbf{r}}{\partial \mathbf{x}}\right]^{T} \mathbf{A}^{T} \mathbf{s} \\
\frac{\partial}{\partial \mathbf{x}} \frac{(\mathbf{A} \mathbf{x})^{T}(\mathbf{A} \mathbf{x})}{(\mathbf{B} \mathbf{x})^{T}(\mathbf{B} \mathbf{x})} & =\frac{\partial}{\partial \mathbf{x}} \frac{\mathbf{x}^{T} \mathbf{A}^{T} \mathbf{A} \mathbf{x}}{\mathbf{x}^{T} \mathbf{B}^{T} \mathbf{B} \mathbf{x}} \\
& =2 \frac{\mathbf{A}^{T} \mathbf{A} \mathbf{x}}{\mathbf{x}^{T} \mathbf{B B} \mathbf{x}}-2 \frac{\mathbf{x}^{T} \mathbf{A}^{T} \mathbf{A} \mathbf{x} \mathbf{B}^{T} \mathbf{B} \mathbf{x}}{\left(\mathbf{x}^{T} \mathbf{B}^{T} \mathbf{B} \mathbf{x}\right)^{2}}
\end{aligned}
$$

\subsubsection{Gradient and Hessian}

Using the above we have for the gradient and the Hessian

$$
\begin{aligned}
f & =\mathbf{x}^{T} \mathbf{A} \mathbf{x}+\mathbf{b}^{T} \mathbf{x} \\
\nabla_{\mathbf{x}} f=\frac{\partial f}{\partial \mathbf{x}} & =\left(\mathbf{A}+\mathbf{A}^{T}\right) \mathbf{x}+\mathbf{b} \\
\frac{\partial^{2} f}{\partial \mathbf{x} \partial \mathbf{x}^{T}} & =\mathbf{A}+\mathbf{A}^{T}
\end{aligned}
$$

\subsection{Derivatives of Traces}

Assume $F(\mathbf{X})$ to be a differentiable function of each of the elements of $X$. It then holds that

$$
\frac{\partial \operatorname{Tr}(F(\mathbf{X}))}{\partial \mathbf{X}}=f(\mathbf{X})^{T}
$$

where $f(\cdot)$ is the scalar derivative of $F(\cdot)$.

\subsubsection{First Order}

$$
\begin{aligned}
\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}(\mathbf{X}) & =\mathbf{I} \\
\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}(\mathbf{X} \mathbf{A}) & =\mathbf{A}^{T} \\
\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}(\mathbf{A X B}) & =\mathbf{A}^{T} \mathbf{B}^{T} \\
\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{A} \mathbf{X}^{T} \mathbf{B}\right) & =\mathbf{B} \mathbf{A} \\
\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{X}^{T} \mathbf{A}\right) & =\mathbf{A} \\
\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{A} \mathbf{X}^{T}\right) & =\mathbf{A} \\
\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}(\mathbf{A} \otimes \mathbf{X}) & =\operatorname{Tr}(\mathbf{A}) \mathbf{I}
\end{aligned}
$$



\subsubsection{Second Order}

$$
\begin{aligned}
& \frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{X}^{2}\right)=2 \mathbf{X}^{T} \\
& \frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{X}^{2} \mathbf{B}\right)=(\mathbf{X B}+\mathbf{B} \mathbf{X})^{T} \\
& \frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{X}^{T} \mathbf{B} \mathbf{X}\right)=\mathbf{B} \mathbf{X}+\mathbf{B}^{T} \mathbf{X} \\
& \frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{B X X}^{T}\right)=\mathbf{B} \mathbf{X}+\mathbf{B}^{T} \mathbf{X} \\
& \frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{X X}^{T} \mathbf{B}\right)=\mathbf{B X}+\mathbf{B}^{T} \mathbf{X} \\
& \frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{X B} \mathbf{X}^{T}\right)=\mathbf{X B}^{T}+\mathbf{X B} \\
& \frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{B X}^{T} \mathbf{X}\right)=\mathbf{X B}^{T}+\mathbf{X B} \\
& \frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{X}^{T} \mathbf{X B}\right)=\mathbf{X B}^{T}+\mathbf{X B} \\
& \frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}(\mathbf{A} \mathbf{X} \mathbf{X})=\mathbf{A}^{T} \mathbf{X}^{T} \mathbf{B}^{T}+\mathbf{B}^{T} \mathbf{X}^{T} \mathbf{A}^{T} \\
& \frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{X}^{T} \mathbf{X}\right)=\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{X X}^{T}\right)=2 \mathbf{X} \\
& \frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{B}^{T} \mathbf{X}^{T} \mathbf{C X B}\right)=\mathbf{C}^{T} \mathbf{X B B} \mathbf{B}^{T}+\mathbf{C X B B}^{T} \\
& \frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left[\mathbf{X}^{T} \mathbf{B} \mathbf{X} \mathbf{C}\right]=\mathbf{B} \mathbf{X} \mathbf{C}+\mathbf{B}^{T} \mathbf{X} \mathbf{C}^{T} \\
& \frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{A X B} \mathbf{X}^{T} \mathbf{C}\right)=\mathbf{A}^{T} \mathbf{C}^{T} \mathbf{X} \mathbf{B}^{T}+\mathbf{C A X B} \\
& \frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left[(\mathbf{A X B}+\mathbf{C})(\mathbf{A X B}+\mathbf{C})^{T}\right]=2 \mathbf{A}^{T}(\mathbf{A X B}+\mathbf{C}) \mathbf{B}^{T} \\
& \frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}(\mathbf{X} \otimes \mathbf{X})=\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}(\mathbf{X}) \operatorname{Tr}(\mathbf{X})=2 \operatorname{Tr}(\mathbf{X}) \mathbf{I}
\end{aligned}
$$

See 7.

\subsubsection{Higher Order}

$$
\begin{aligned}
\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{X}^{k}\right)= & k\left(\mathbf{X}^{k-1}\right)^{T} \\
\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{A} \mathbf{X}^{k}\right)= & \sum_{r=0}^{k-1}\left(\mathbf{X}^{r} \mathbf{A} \mathbf{X}^{k-r-1}\right)^{T} \\
\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left[\mathbf{B}^{T} \mathbf{X}^{T} \mathbf{C X X} \mathbf{X}^{T} \mathbf{C X B}\right]= & \mathbf{C X} \mathbf{X}^{T} \mathbf{C X B B}^{T} \\
& +\mathbf{C}^{T} \mathbf{X B B}^{T} \mathbf{X}^{T} \mathbf{C}^{T} \mathbf{X} \\
& +\mathbf{C X B B}^{T} \mathbf{X}^{T} \mathbf{C X} \\
& +\mathbf{C}^{T} \mathbf{X X}^{T} \mathbf{C}^{T} \mathbf{X B} \mathbf{B}^{T}
\end{aligned}
$$



\subsubsection{Other}

$$
\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{A} \mathbf{X}^{-1} \mathbf{B}\right)=-\left(\mathbf{X}^{-1} \mathbf{B} \mathbf{A} \mathbf{X}^{-1}\right)^{T}=-\mathbf{X}^{-T} \mathbf{A}^{T} \mathbf{B}^{T} \mathbf{X}^{-T}
$$

Assume $\mathbf{B}$ and $\mathbf{C}$ to be symmetric, then

$$
\begin{aligned}
\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left[\left(\mathbf{X}^{T} \mathbf{C X}\right)^{-1} \mathbf{A}\right]= & -\left(\mathbf{C X}\left(\mathbf{X}^{T} \mathbf{C X}\right)^{-1}\right)\left(\mathbf{A}+\mathbf{A}^{T}\right)\left(\mathbf{X}^{T} \mathbf{C X}\right)^{-1} \\
\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left[\left(\mathbf{X}^{T} \mathbf{C X}\right)^{-1}\left(\mathbf{X}^{T} \mathbf{B} \mathbf{X}\right)\right]= & -2 \mathbf{C X}\left(\mathbf{X}^{T} \mathbf{C X}\right)^{-1} \mathbf{X}^{T} \mathbf{B} \mathbf{X}\left(\mathbf{X}^{T} \mathbf{C X}\right)^{-1} \\
& +2 \mathbf{B} \mathbf{X}\left(\mathbf{X}^{T} \mathbf{C X}\right)^{-1} \\
\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left[\left(\mathbf{A}+\mathbf{X}^{T} \mathbf{C X}\right)^{-1}\left(\mathbf{X}^{T} \mathbf{B} \mathbf{X}\right)\right]= & -2 \mathbf{C X}\left(\mathbf{A}+\mathbf{X}^{T} \mathbf{C X}\right)^{-1} \mathbf{X}^{T} \mathbf{B X}\left(\mathbf{A}+\mathbf{X}^{T} \mathbf{C X}\right)^{-1} \\
& +2 \mathbf{B} \mathbf{X}\left(\mathbf{A}+\mathbf{X}^{T} \mathbf{C X}\right)^{-1}
\end{aligned}
$$

See [7].

$$
\frac{\partial \operatorname{Tr}(\sin (\mathbf{X}))}{\partial \mathbf{X}}=\cos (\mathbf{X})^{T}
$$

\subsection{Derivatives of vector norms}

\subsubsection{Two-norm}

$$
\begin{gathered}
\frac{\partial}{\partial \mathbf{x}}\|\mathbf{x}-\mathbf{a}\|_{2}=\frac{\mathbf{x}-\mathbf{a}}{\|\mathbf{x}-\mathbf{a}\|_{2}} \\
\frac{\partial}{\partial \mathbf{x}} \frac{\mathbf{x}-\mathbf{a}}{\|\mathbf{x}-\mathbf{a}\|_{2}}=\frac{\mathbf{I}}{\|\mathbf{x}-\mathbf{a}\|_{2}}-\frac{(\mathbf{x}-\mathbf{a})(\mathbf{x}-\mathbf{a})^{T}}{\|\mathbf{x}-\mathbf{a}\|_{2}^{3}} \\
\frac{\partial\|\mathbf{x}\|_{2}^{2}}{\partial \mathbf{x}}=\frac{\partial\left\|\mathbf{x}^{T} \mathbf{x}\right\|_{2}}{\partial \mathbf{x}}=2 \mathbf{x}
\end{gathered}
$$

\subsection{Derivatives of matrix norms}

For more on matrix norms, see Sec. 10.4

\subsubsection{Frobenius norm}

$$
\frac{\partial}{\partial \mathbf{X}}\|\mathbf{X}\|_{\mathrm{F}}^{2}=\frac{\partial}{\partial \mathbf{X}} \operatorname{Tr}\left(\mathbf{X} \mathbf{X}^{H}\right)=2 \mathbf{X}
$$

See (248). Note that this is also a special case of the result in equation 119 .

\subsection{Derivatives of Structured Matrices}

Assume that the matrix $\mathbf{A}$ has some structure, i.e. symmetric, toeplitz, etc. In that case the derivatives of the previous section does not apply in general. Instead, consider the following general rule for differentiating a scalar function $f(\mathbf{A})$

$$
\frac{d f}{d A_{i j}}=\sum_{k l} \frac{\partial f}{\partial A_{k l}} \frac{\partial A_{k l}}{\partial A_{i j}}=\operatorname{Tr}\left[\left[\frac{\partial f}{\partial \mathbf{A}}\right]^{T} \frac{\partial \mathbf{A}}{\partial A_{i j}}\right]
$$

The matrix differentiated with respect to itself is in this document referred to as the structure matrix of $\mathbf{A}$ and is defined simply by

$$
\frac{\partial \mathbf{A}}{\partial A_{i j}}=\mathbf{S}^{i j}
$$

If $\mathbf{A}$ has no special structure we have simply $\mathbf{S}^{i j}=\mathbf{J}^{i j}$, that is, the structure matrix is simply the single-entry matrix. Many structures have a representation in singleentry matrices, see Sec. 9.7.6 for more examples of structure matrices.

\subsubsection{The Chain Rule}

Sometimes the objective is to find the derivative of a matrix which is a function of another matrix. Let $\mathbf{U}=f(\mathbf{X})$, the goal is to find the derivative of the function $g(\mathbf{U})$ with respect to $\mathbf{X}$ :

$$
\frac{\partial g(\mathbf{U})}{\partial \mathbf{X}}=\frac{\partial g(f(\mathbf{X}))}{\partial \mathbf{X}}
$$

Then the Chain Rule can then be written the following way:

$$
\frac{\partial g(\mathbf{U})}{\partial \mathbf{X}}=\frac{\partial g(\mathbf{U})}{\partial x_{i j}}=\sum_{k=1}^{M} \sum_{l=1}^{N} \frac{\partial g(\mathbf{U})}{\partial u_{k l}} \frac{\partial u_{k l}}{\partial x_{i j}}
$$

Using matrix notation, this can be written as:

$$
\frac{\partial g(\mathbf{U})}{\partial X_{i j}}=\operatorname{Tr}\left[\left(\frac{\partial g(\mathbf{U})}{\partial \mathbf{U}}\right)^{T} \frac{\partial \mathbf{U}}{\partial X_{i j}}\right]
$$

\subsubsection{Symmetric}

If $\mathbf{A}$ is symmetric, then $\mathbf{S}^{i j}=\mathbf{J}^{i j}+\mathbf{J}^{j i}-\mathbf{J}^{i j} \mathbf{J}^{i j}$ and therefore

$$
\frac{d f}{d \mathbf{A}}=\left[\frac{\partial f}{\partial \mathbf{A}}\right]+\left[\frac{\partial f}{\partial \mathbf{A}}\right]^{T}-\operatorname{diag}\left[\frac{\partial f}{\partial \mathbf{A}}\right]
$$

That is, e.g., ([5]):

$$
\begin{aligned}
\frac{\partial \operatorname{Tr}(\mathbf{A} \mathbf{X})}{\partial \mathbf{X}} & \left.=\mathbf{A}+\mathbf{A}^{T}-(\mathbf{A} \circ \mathbf{I}), \text { see } 142\right) \\
\frac{\partial \operatorname{det}(\mathbf{X})}{\partial \mathbf{X}} & =\operatorname{det}(\mathbf{X})\left(2 \mathbf{X}^{-1}-\left(\mathbf{X}^{-1} \circ \mathbf{I}\right)\right) \\
\frac{\partial \ln \operatorname{det}(\mathbf{X})}{\partial \mathbf{X}} & =2 \mathbf{X}^{-1}-\left(\mathbf{X}^{-1} \circ \mathbf{I}\right)
\end{aligned}
$$

\subsubsection{Diagonal}

If $\mathbf{X}$ is diagonal, then $([19)$ :

$$
\frac{\partial \operatorname{Tr}(\mathbf{A})}{\partial \mathbf{X}}=\mathbf{A} \circ \mathbf{I}
$$



\subsubsection{Toeplitz}

Like symmetric matrices and diagonal matrices also Toeplitz matrices has a special structure which should be taken into account when the derivative with respect to a matrix with Toeplitz structure.

$$
\begin{aligned}
& \frac{\partial \operatorname{Tr}(\mathbf{A} \mathbf{T})}{\partial \mathbf{T}} \\
& =\frac{\partial \operatorname{Tr}(\mathbf{T A})}{\partial \mathbf{T}} \\
& =\left[\begin{array}{ccccc}
\operatorname{Tr}(\mathbf{A}) & \operatorname{Tr}\left(\left[\mathbf{A}^{T}\right]_{n 1}\right) & \operatorname{Tr}\left(\left[\left[\mathbf{A}^{T}\right]_{1 n}\right]_{n-1,2}\right) & \cdots & A_{n 1} \\
\left.\operatorname{Tr}\left(\left[\mathbf{A}^{T}\right]_{1 n}\right)\right) & \operatorname{Tr}(\mathbf{A}) & \ddots & \ddots & \vdots \\
\operatorname{Tr}\left(\left[\left[\mathbf{A}^{T}\right]_{1 n}\right]_{2, n-1}\right) & \ddots & \ddots & \ddots & \operatorname{Tr}\left(\left[\left[\mathbf{A}^{T}\right]_{1 n}\right]_{n-1,2}\right) \\
\vdots & \ddots & \ddots & \ddots & \operatorname{Tr}\left(\left[\mathbf{A}^{T}\right]_{n 1}\right)
\end{array}\right] \\
& \equiv \boldsymbol{\alpha}(\mathbf{A})
\end{aligned}
$$

As it can be seen, the derivative $\boldsymbol{\alpha}(\mathbf{A})$ also has a Toeplitz structure. Each value in the diagonal is the sum of all the diagonal valued in $\mathbf{A}$, the values in the diagonals next to the main diagonal equal the sum of the diagonal next to the main diagonal in $\mathbf{A}^{T}$. This result is only valid for the unconstrained Toeplitz matrix. If the Toeplitz matrix also is symmetric, the same derivative yields

$$
\frac{\partial \operatorname{Tr}(\mathbf{A} \mathbf{T})}{\partial \mathbf{T}}=\frac{\partial \operatorname{Tr}(\mathbf{T} \mathbf{A})}{\partial \mathbf{T}}=\boldsymbol{\alpha}(\mathbf{A})+\boldsymbol{\alpha}(\mathbf{A})^{T}-\boldsymbol{\alpha}(\mathbf{A}) \circ \mathbf{I}
$$



\section{Inverses}

\subsection{Basic}

\subsubsection{Definition}

The inverse $\mathbf{A}^{-1}$ of a matrix $\mathbf{A} \in \mathbb{C}^{n \times n}$ is defined such that

$$
\mathbf{A A}^{-1}=\mathbf{A}^{-1} \mathbf{A}=\mathbf{I}
$$

where $\mathbf{I}$ is the $n \times n$ identity matrix. If $\mathbf{A}^{-1}$ exists, $\mathbf{A}$ is said to be nonsingular. Otherwise, $\mathbf{A}$ is said to be singular (see e.g. [12]).

\subsubsection{Cofactors and Adjoint}

The submatrix of a matrix $\mathbf{A}$, denoted by $[\mathbf{A}]_{i j}$ is a $(n-1) \times(n-1)$ matrix obtained by deleting the $i$ th row and the $j$ th column of $\mathbf{A}$. The $(i, j)$ cofactor of a matrix is defined as

$$
\operatorname{cof}(\mathbf{A}, i, j)=(-1)^{i+j} \operatorname{det}\left([\mathbf{A}]_{i j}\right)
$$

The matrix of cofactors can be created from the cofactors

$$
\operatorname{cof}(\mathbf{A})=\left[\begin{array}{ccc}
\operatorname{cof}(\mathbf{A}, 1,1) & \cdots & \operatorname{cof}(\mathbf{A}, 1, n) \\
\vdots & \operatorname{cof}(\mathbf{A}, i, j) & \vdots \\
\operatorname{cof}(\mathbf{A}, n, 1) & \cdots & \operatorname{cof}(\mathbf{A}, n, n)
\end{array}\right]
$$

The adjoint matrix is the transpose of the cofactor matrix

$$
\operatorname{adj}(\mathbf{A})=(\operatorname{cof}(\mathbf{A}))^{T}
$$

\subsubsection{Determinant}

The determinant of a matrix $\mathbf{A} \in \mathbb{C}^{n \times n}$ is defined as (see [12])

$$
\begin{aligned}
\operatorname{det}(\mathbf{A}) & =\sum_{j=1}^{n}(-1)^{j+1} A_{1 j} \operatorname{det}\left([\mathbf{A}]_{1 j}\right) \\
& =\sum_{j=1}^{n} A_{1 j} \operatorname{cof}(\mathbf{A}, 1, j) .
\end{aligned}
$$

\subsubsection{Construction}

The inverse matrix can be constructed, using the adjoint matrix, by

$$
\mathbf{A}^{-1}=\frac{1}{\operatorname{det}(\mathbf{A})} \cdot \operatorname{adj}(\mathbf{A})
$$

For the case of $2 \times 2$ matrices, see section 1.3 

\subsubsection{Condition number}

The condition number of a matrix $c(\mathbf{A})$ is the ratio between the largest and the smallest singular value of a matrix (see Section 5.3 on singular values),

$$
c(\mathbf{A})=\frac{d_{+}}{d_{-}}
$$

The condition number can be used to measure how singular a matrix is. If the condition number is large, it indicates that the matrix is nearly singular. The condition number can also be estimated from the matrix norms. Here

$$
c(\mathbf{A})=\|\mathbf{A}\| \cdot\left\|\mathbf{A}^{-1}\right\|
$$

where $\|\cdot\|$ is a norm such as e.g the 1-norm, the 2 -norm, the $\infty$-norm or the Frobenius norm (see Sec 10.4 for more on matrix norms).

The 2-norm of $\mathbf{A}$ equals $\sqrt{\left(\max \left(\operatorname{eig}\left(\mathbf{A}^{H} \mathbf{A}\right)\right)\right)}$ 12, p.57]. For a symmetric matrix, this reduces to $\|\mathbf{A}\|_{2}=\max (|\operatorname{eig}(\mathbf{A})|)$ [12, p.394]. If the matrix is symmetric and positive definite, $\|\mathbf{A}\|_{2}=\max (\operatorname{eig}(\mathbf{A}))$. The condition number based on the 2 -norm thus reduces to

$$
\|\mathbf{A}\|_{2}\left\|\mathbf{A}^{-1}\right\|_{2}=\max (\operatorname{eig}(\mathbf{A})) \max \left(\operatorname{eig}\left(\mathbf{A}^{-1}\right)\right)=\frac{\max (\operatorname{eig}(\mathbf{A}))}{\min (\operatorname{eig}(\mathbf{A}))}
$$

\subsection{Exact Relations}

\subsubsection{Basic}

$$
(\mathbf{A B})^{-1}=\mathbf{B}^{-1} \mathbf{A}^{-1}
$$

\subsubsection{The Woodbury identity}

The Woodbury identity comes in many variants. The latter of the two can be found in 12

$$
\begin{aligned}
\left(\mathbf{A}+\mathbf{C B C}^{T}\right)^{-1} & =\mathbf{A}^{-1}-\mathbf{A}^{-1} \mathbf{C}\left(\mathbf{B}^{-1}+\mathbf{C}^{T} \mathbf{A}^{-1} \mathbf{C}\right)^{-1} \mathbf{C}^{T} \mathbf{A}^{-1} \\
(\mathbf{A}+\mathbf{U B V})^{-1} & =\mathbf{A}^{-1}-\mathbf{A}^{-1} \mathbf{U}\left(\mathbf{B}^{-1}+\mathbf{V A}^{-1} \mathbf{U}\right)^{-1} \mathbf{V} \mathbf{A}^{-1}
\end{aligned}
$$

If $\mathbf{P}, \mathbf{R}$ are positive definite, then (see $[30]$

$$
\left(\mathbf{P}^{-1}+\mathbf{B}^{T} \mathbf{R}^{-1} \mathbf{B}\right)^{-1} \mathbf{B}^{T} \mathbf{R}^{-1}=\mathbf{P B}^{T}\left(\mathbf{B} \mathbf{P} \mathbf{B}^{T}+\mathbf{R}\right)^{-1}
$$

\subsubsection{The Kailath Variant}

$$
(\mathbf{A}+\mathbf{B C})^{-1}=\mathbf{A}^{-1}-\mathbf{A}^{-1} \mathbf{B}\left(\mathbf{I}+\mathbf{C A}^{-1} \mathbf{B}\right)^{-1} \mathbf{C A}^{-1}
$$

See [4, page 153].

\subsubsection{Sherman-Morrison}

$$
\left(\mathbf{A}+\mathbf{b} \mathbf{c}^{T}\right)^{-1}=\mathbf{A}^{-1}-\frac{\mathbf{A}^{-1} \mathbf{b} \mathbf{c}^{T} \mathbf{A}^{-1}}{1+\mathbf{c}^{T} \mathbf{A}^{-1} \mathbf{b}}
$$



\subsubsection{The Searle Set of Identities}

The following set of identities, can be found in [25, page 151],

$$
\begin{aligned}
\left(\mathbf{I}+\mathbf{A}^{-1}\right)^{-1} & =\mathbf{A}(\mathbf{A}+\mathbf{I})^{-1} \\
\left(\mathbf{A}+\mathbf{B B}^{T}\right)^{-1} \mathbf{B} & =\mathbf{A}^{-1} \mathbf{B}\left(\mathbf{I}+\mathbf{B}^{T} \mathbf{A}^{-1} \mathbf{B}\right)^{-1} \\
\left(\mathbf{A}^{-1}+\mathbf{B}^{-1}\right)^{-1} & =\mathbf{A}(\mathbf{A}+\mathbf{B})^{-1} \mathbf{B}=\mathbf{B}(\mathbf{A}+\mathbf{B})^{-1} \mathbf{A} \\
\mathbf{A}-\mathbf{A}(\mathbf{A}+\mathbf{B})^{-1} \mathbf{A} & =\mathbf{B}-\mathbf{B}(\mathbf{A}+\mathbf{B})^{-1} \mathbf{B} \\
\mathbf{A}^{-1}+\mathbf{B}^{-1} & =\mathbf{A}^{-1}(\mathbf{A}+\mathbf{B}) \mathbf{B}^{-1} \\
(\mathbf{I}+\mathbf{A B})^{-1} & =\mathbf{I}-\mathbf{A}(\mathbf{I}+\mathbf{B} \mathbf{A})^{-1} \mathbf{B} \\
(\mathbf{I}+\mathbf{A B})^{-1} \mathbf{A} & =\mathbf{A}(\mathbf{I}+\mathbf{B} \mathbf{A})^{-1}
\end{aligned}
$$

\subsubsection{Rank-1 update of inverse of inner product}

Denote $\mathbf{A}=\left(\mathbf{X}^{T} \mathbf{X}\right)^{-1}$ and that $\mathbf{X}$ is extended to include a new column vector in the end $\tilde{\mathbf{X}}=\left[\begin{array}{ll}\mathbf{X} & \mathbf{v}\end{array}\right]$. Then 34

$$
\left(\tilde{\mathbf{X}}^{T} \tilde{\mathbf{X}}\right)^{-1}=\left[\begin{array}{cc}
\mathbf{A}+\frac{\mathbf{A} \mathbf{X}^{T} \mathbf{v v}^{T} \mathbf{X} \mathbf{A}^{T}}{\mathbf{v}^{T} \mathbf{v}-\mathbf{v}^{T} \mathbf{X A}^{T} \mathbf{A} \mathbf{X}^{T} \mathbf{v}} & \frac{-\mathbf{A} \mathbf{X}^{T} \mathbf{v}}{\mathbf{v}^{T} \mathbf{v}-\mathbf{v}^{T} \mathbf{X} \mathbf{A} \mathbf{X}^{T} \mathbf{v}} \\
\frac{-\mathbf{v}^{T} \mathbf{X} \mathbf{A}^{T}}{\mathbf{v}^{T} \mathbf{v}-\mathbf{v}^{T} \mathbf{X} \mathbf{A X} \mathbf{X}^{T} \mathbf{v}} & \frac{1}{\mathbf{v}^{T} \mathbf{v}-\mathbf{v}^{T} \mathbf{X A X} \mathbf{X}^{T} \mathbf{v}}
\end{array}\right]
$$

\subsubsection{Rank-1 update of Moore-Penrose Inverse}

The following is a rank-1 update for the Moore-Penrose pseudo-inverse of real valued matrices and proof can be found in [18. The matrix $\mathbf{G}$ is defined below:

$$
\left(\mathbf{A}+\mathbf{c d}^{T}\right)^{+}=\mathbf{A}^{+}+\mathbf{G}
$$

Using the the notation

$$
\begin{aligned}
\beta & =1+\mathbf{d}^{T} \mathbf{A}^{+} \mathbf{c} \\
\mathbf{v} & =\mathbf{A}^{+} \mathbf{c} \\
\mathbf{n} & =\left(\mathbf{A}^{+}\right)^{T} \mathbf{d} \\
\mathbf{w} & =\left(\mathbf{I}-\mathbf{A} \mathbf{A}^{+}\right) \mathbf{c} \\
\mathbf{m} & =\left(\mathbf{I}-\mathbf{A}^{+} \mathbf{A}\right)^{T} \mathbf{d}
\end{aligned}
$$

the solution is given as six different cases, depending on the entities $\|\mathbf{w}\|$, $\|\mathbf{m}\|$, and $\beta$. Please note, that for any (column) vector $\mathbf{v}$ it holds that $\mathbf{v}^{+}=$ $\mathbf{v}^{T}\left(\mathbf{v}^{T} \mathbf{v}\right)^{-1}=\frac{\mathbf{v}^{T}}{\|\mathbf{v}\|^{2}}$. The solution is:

Case 1 of $6:$ If $\|\mathbf{w}\| \neq 0$ and $\|\mathbf{m}\| \neq 0$. Then

$$
\begin{aligned}
\mathbf{G} & =-\mathbf{v} \mathbf{w}^{+}-\left(\mathbf{m}^{+}\right)^{T} \mathbf{n}^{T}+\beta\left(\mathbf{m}^{+}\right)^{T} \mathbf{w}^{+} \\
& =-\frac{1}{\|\mathbf{w}\|^{2}} \mathbf{v} \mathbf{w}^{T}-\frac{1}{\|\mathbf{m}\|^{2}} \mathbf{m} \mathbf{n}^{T}+\frac{\beta}{\|\mathbf{m}\|\left\|^{2}\right\| \mathbf{w} \|^{2}} \mathbf{m} \mathbf{w}^{T}
\end{aligned}
$$

Case 2 of 6 : If $\|\mathbf{w}\|=0$ and $\|\mathbf{m}\| \neq 0$ and $\beta=0$. Then

$$
\begin{aligned}
\mathbf{G} & =-\mathbf{v} \mathbf{v}^{+} \mathbf{A}^{+}-\left(\mathbf{m}^{+}\right)^{T} \mathbf{n}^{T} \\
& =-\frac{1}{\|\mathbf{v}\|^{2}} \mathbf{v} \mathbf{v}^{T} \mathbf{A}^{+}-\frac{1}{\|\mathbf{m}\|^{2}} \mathbf{m} \mathbf{n}^{T}
\end{aligned}
$$

Petersen \& Pedersen, The Matrix Cookbook, Version: November 15, 2012, Page 19 Case 3 of 6 : If $\|\mathbf{w}\|=0$ and $\beta \neq 0$. Then

$$
\mathbf{G}=\frac{1}{\beta} \mathbf{m v}^{T} \mathbf{A}^{+}-\frac{\beta}{\|\mathbf{v}\|^{2}\|\mathbf{m}\|^{2}+|\beta|^{2}}\left(\frac{\|\mathbf{v}\|^{2}}{\beta} \mathbf{m}+\mathbf{v}\right)\left(\frac{\|\mathbf{m}\|^{2}}{\beta}\left(\mathbf{A}^{+}\right)^{T} \mathbf{v}+\mathbf{n}\right)^{T}
$$

Case 4 of 6 : If $\|\mathbf{w}\| \neq 0$ and $\|\mathbf{m}\|=0$ and $\beta=0$. Then

$$
\begin{aligned}
\mathbf{G} & =-\mathbf{A}^{+} \mathbf{n} \mathbf{n}^{+}-\mathbf{v} \mathbf{w}^{+} \\
& =-\frac{1}{\|\mathbf{n}\|^{2}} \mathbf{A}^{+} \mathbf{n} \mathbf{n}^{T}-\frac{1}{\|\mathbf{w}\|^{2}} \mathbf{v} \mathbf{w}^{T}
\end{aligned}
$$

Case 5 of 6 : If $\|\mathbf{m}\|=0$ and $\beta \neq 0$. Then

$$
\mathbf{G}=\frac{1}{\beta} \mathbf{A}^{+} \mathbf{n} \mathbf{w}^{T}-\frac{\beta}{\|\mathbf{n}\|^{2}\|\mathbf{w}\|^{2}+|\beta|^{2}}\left(\frac{\|\mathbf{w}\|^{2}}{\beta} \mathbf{A}^{+} \mathbf{n}+\mathbf{v}\right)\left(\frac{\|\mathbf{n}\|^{2}}{\beta} \mathbf{w}+\mathbf{n}\right)^{T}
$$

Case 6 of 6 : If $\|\mathbf{w}\|=0$ and $\|\mathbf{m}\|=0$ and $\beta=0$. Then

$$
\begin{aligned}
\mathbf{G} & =-\mathbf{v} \mathbf{v}^{+} \mathbf{A}^{+}-\mathbf{A}^{+} \mathbf{n} \mathbf{n}^{+}+\mathbf{v}^{+} \mathbf{A}^{+} \mathbf{n} \mathbf{v} \mathbf{n}^{+} \\
& =-\frac{1}{\|\mathbf{v}\|^{2}} \mathbf{v} \mathbf{v}^{T} \mathbf{A}^{+}-\frac{1}{\|\mathbf{n}\|^{2}} \mathbf{A}^{+} \mathbf{n} \mathbf{n}^{T}+\frac{\mathbf{v}^{T} \mathbf{A}^{+} \mathbf{n}}{\|\mathbf{v}\|^{2}\|\mathbf{n}\|^{2}} \mathbf{v} \mathbf{n}^{T}
\end{aligned}
$$

\subsection{Implication on Inverses}

$$
\text { If }(\mathbf{A}+\mathbf{B})^{-1}=\mathbf{A}^{-1}+\mathbf{B}^{-1} \text { then } \mathbf{A B}^{-1} \mathbf{A}=\mathbf{B} \mathbf{A}^{-1} \mathbf{B}
$$

See 25$]$

\subsubsection{A PosDef identity}

Assume $\mathbf{P}, \mathbf{R}$ to be positive definite and invertible, then

$$
\left(\mathbf{P}^{-1}+\mathbf{B}^{T} \mathbf{R}^{-1} \mathbf{B}\right)^{-1} \mathbf{B}^{T} \mathbf{R}^{-1}=\mathbf{P B}^{T}\left(\mathbf{B} \mathbf{P} \mathbf{B}^{T}+\mathbf{R}\right)^{-1}
$$

See 30

\subsection{Approximations}

The following identity is known as the Neuman series of a matrix, which holds when $\left|\lambda_{i}\right|<1$ for all eigenvalues $\lambda_{i}$

$$
(\mathbf{I}-\mathbf{A})^{-1}=\sum_{n=0}^{\infty} \mathbf{A}^{n}
$$

which is equivalent to

$$
(\mathbf{I}+\mathbf{A})^{-1}=\sum_{n=0}^{\infty}(-1)^{n} \mathbf{A}^{n}
$$

When $\left|\lambda_{i}\right|<1$ for all eigenvalues $\lambda_{i}$, it holds that $\mathbf{A} \rightarrow 0$ for $n \rightarrow \infty$, and the following approximations holds

$$
\begin{aligned}
& (\mathbf{I}-\mathbf{A})^{-1} \cong \mathbf{I}+\mathbf{A}+\mathbf{A}^{2} \\
& (\mathbf{I}+\mathbf{A})^{-1} \cong \mathbf{I}-\mathbf{A}+\mathbf{A}^{2}
\end{aligned}
$$

The following approximation is from 22 and holds when $\mathbf{A}$ large and symmetric

$$
\mathbf{A}-\mathbf{A}(\mathbf{I}+\mathbf{A})^{-1} \mathbf{A} \cong \mathbf{I}-\mathbf{A}^{-1}
$$

If $\sigma^{2}$ is small compared to $\mathbf{Q}$ and $\mathbf{M}$ then

$$
\left(\mathbf{Q}+\sigma^{2} \mathbf{M}\right)^{-1} \cong \mathbf{Q}^{-1}-\sigma^{2} \mathbf{Q}^{-1} \mathbf{M} \mathbf{Q}^{-1}
$$

Proof:

$$
\begin{aligned}
\left(\mathbf{Q}+\sigma^{2} \mathbf{M}\right)^{-1} & = \\
\left(\mathbf{Q Q}^{-1} \mathbf{Q}+\sigma^{2} \mathbf{M} \mathbf{Q}^{-1} \mathbf{Q}\right)^{-1} & = \\
\left(\left(\mathbf{I}+\sigma^{2} \mathbf{M} \mathbf{Q}^{-1}\right) \mathbf{Q}\right)^{-1} & = \\
\mathbf{Q}^{-1}\left(\mathbf{I}+\sigma^{2} \mathbf{M} \mathbf{Q}^{-1}\right)^{-1} &
\end{aligned}
$$

This can be rewritten using the Taylor expansion:

$$
\begin{aligned}
\mathbf{Q}^{-1}\left(\mathbf{I}+\sigma^{2} \mathbf{M} \mathbf{Q}^{-1}\right)^{-1} & = \\
\mathbf{Q}^{-1}\left(\mathbf{I}-\sigma^{2} \mathbf{M} \mathbf{Q}^{-1}+\left(\sigma^{2} \mathbf{M} \mathbf{Q}^{-1}\right)^{2}-\ldots\right) & \cong \mathbf{Q}^{-1}-\sigma^{2} \mathbf{Q}^{-1} \mathbf{M} \mathbf{Q}^{-1}
\end{aligned}
$$

\subsection{Generalized Inverse}

\subsubsection{Definition}

A generalized inverse matrix of the matrix $\mathbf{A}$ is any matrix $\mathbf{A}^{-}$such that (see 26]

$$
\mathbf{A} \mathbf{A}^{-} \mathbf{A}=\mathbf{A}
$$

The matrix $\mathbf{A}^{-}$is not unique.

\subsection{Pseudo Inverse}

\subsubsection{Definition}

The pseudo inverse (or Moore-Penrose inverse) of a matrix $\mathbf{A}$ is the matrix $\mathbf{A}^{+}$ that fulfils

$\begin{aligned} \text { I } & \mathbf{A} \mathbf{A}^{+} \mathbf{A}=\mathbf{A} \\ \text { II } & \mathbf{A}^{+} \mathbf{A} \mathbf{A}^{+}=\mathbf{A}^{+} \\ \text {III } & \mathbf{A A}^{+} \text {symmetric } \\ \text { IV } & \mathbf{A}^{+} \mathbf{A} \text { symmetric }\end{aligned}$

The matrix $\mathbf{A}^{+}$is unique and does always exist. Note that in case of complex matrices, the symmetric condition is substituted by a condition of being Hermitian. 

\subsubsection{Properties}

Assume $\mathbf{A}^{+}$to be the pseudo-inverse of $\mathbf{A}$, then (See [3 for some of them)

$$
\begin{aligned}
\left(\mathbf{A}^{+}\right)^{+} & =\mathbf{A} \\
\left(\mathbf{A}^{T}\right)^{+} & =\left(\mathbf{A}^{+}\right)^{T} \\
\left(\mathbf{A}^{H}\right)^{+} & =\left(\mathbf{A}^{+}\right)^{H} \\
\left(\mathbf{A}^{*}\right)^{+} & =\left(A^{+}\right)^{*} \\
\left(\mathbf{A}^{+} \mathbf{A}\right) \mathbf{A}^{H} & =\mathbf{A}^{H} \\
\left(\mathbf{A}^{+} \mathbf{A}\right) \mathbf{A}^{T} & \neq \mathbf{A}^{T} \\
(c \mathbf{A})^{+} & =(1 / c) \mathbf{A}^{+} \\
\mathbf{A}^{+} & =\left(\mathbf{A}^{T} \mathbf{A}\right)^{+} \mathbf{A}^{T} \\
\mathbf{A}^{+} & =\mathbf{A}^{T}\left(\mathbf{A} \mathbf{A}^{T}\right)^{+} \\
\left(\mathbf{A}^{T} \mathbf{A}\right)^{+} & =\mathbf{A}^{+}\left(\mathbf{A}^{T}\right)^{+} \\
\left(\mathbf{A}^{T}\right)^{+} & =\left(\mathbf{A}^{T}\right)^{+} \mathbf{A}^{+} \\
\mathbf{A}^{+} & =\left(\mathbf{A}^{H} \mathbf{A}\right)^{+} \mathbf{A}^{H} \\
\mathbf{A}^{+} & =\mathbf{A}^{H}\left(\mathbf{A} \mathbf{A}^{H}\right)^{+} \\
\left(\mathbf{A}^{H} \mathbf{A}\right)^{+} & =\mathbf{A}^{+}\left(\mathbf{A}^{H}\right)^{+} \\
\left(\mathbf{A}^{H}\right)^{+} & =\left(\mathbf{A}^{H}\right)^{+} \mathbf{A}^{+} \\
(\mathbf{A B})^{+} & =\left(\mathbf{A}^{+} \mathbf{A} \mathbf{B}\right)^{+}\left(\mathbf{A B B} \mathbf{B}^{+}\right)+ \\
f\left(\mathbf{A}^{H} \mathbf{A}\right)-f(0) \mathbf{I} & =\mathbf{A}^{+}\left[f\left(\mathbf{A} \mathbf{A}^{H}\right)-f(0) \mathbf{I}\right] \mathbf{A} \\
f\left(\mathbf{A} \mathbf{A}^{H}\right)-f(0) \mathbf{I} & =\mathbf{A}^{H}\left[f\left(\mathbf{A}^{H} \mathbf{A}\right)-f(0) \mathbf{I}\right] \mathbf{A}
\end{aligned}
$$

where $\mathbf{A} \in \mathbb{C}^{n \times m}$.

Assume A to have full rank, then

$$
\begin{array}{rlr}
\left(\mathbf{A A}^{+}\right)\left(\mathbf{A A}^{+}\right) & =\mathbf{A A}^{+} & \\
\left(\mathbf{A}^{+} \mathbf{A}\right)\left(\mathbf{A}^{+} \mathbf{A}\right) & =\mathbf{A}^{+} \mathbf{A} \\
\operatorname{Tr}\left(\mathbf{A A}^{+}\right) & =\operatorname{rank}\left(\mathbf{A} \mathbf{A}^{+}\right) & (\text {See }[26]) \\
\operatorname{Tr}\left(\mathbf{A}^{+} \mathbf{A}\right) & =\operatorname{rank}\left(\mathbf{A}^{+} \mathbf{A}\right) & (\text { See }[26)
\end{array}
$$

For two matrices it hold that

$$
\begin{aligned}
(\mathbf{A B})^{+} & =\left(\mathbf{A}^{+} \mathbf{A B}\right)^{+}\left(\mathbf{A B B}^{+}\right)^{+} \\
(\mathbf{A} \otimes \mathbf{B})^{+} & =\mathbf{A}^{+} \otimes \mathbf{B}^{+}
\end{aligned}
$$

\subsubsection{Construction}

Assume that A has full rank, then

$$
\begin{array}{lllll}
\mathbf{A} n \times n & \text { Square } & \operatorname{rank}(\mathbf{A})=n & \Rightarrow & \mathbf{A}^{+}=\mathbf{A}^{-1} \\
\mathbf{A} n \times m & \text { Broad } & \operatorname{rank}(\mathbf{A})=n & \Rightarrow & \mathbf{A}^{+}=\mathbf{A}^{T}\left(\mathbf{A} \mathbf{A}^{T}\right)^{-1} \\
\mathbf{A} n \times m & \text { Tall } & \operatorname{rank}(\mathbf{A})=m & \Rightarrow & \mathbf{A}^{+}=\left(\mathbf{A}^{T} \mathbf{A}\right)^{-1} \mathbf{A}^{T}
\end{array}
$$

The so-called "broad version" is also known as right inverse and the "tall version" as the left inverse. Assume $\mathbf{A}$ does not have full rank, i.e. $\mathbf{A}$ is $n \times m$ and $\operatorname{rank}(\mathbf{A})=r<$ $\min (n, m)$. The pseudo inverse $\mathbf{A}^{+}$can be constructed from the singular value decomposition $\mathbf{A}=\mathbf{U D V}^{T}$, by

$$
\mathbf{A}^{+}=\mathbf{V}_{r} \mathbf{D}_{r}^{-1} \mathbf{U}_{r}^{T}
$$

where $\mathbf{U}_{r}, \mathbf{D}_{r}$, and $\mathbf{V}_{r}$ are the matrices with the degenerated rows and columns deleted. A different way is this: There do always exist two matrices $\mathbf{C} n \times r$ and $\mathbf{D} r \times m$ of rank $r$, such that $\mathbf{A}=\mathbf{C D}$. Using these matrices it holds that

$$
\mathbf{A}^{+}=\mathbf{D}^{T}\left(\mathbf{D D}^{T}\right)^{-1}\left(\mathbf{C}^{T} \mathbf{C}\right)^{-1} \mathbf{C}^{T}
$$

See $[3]$ 

\section{Complex Matrices}

The complex scalar product $r=p q$ can be written as

$$
\left[\begin{array}{c}
\Re r \\
\Im r
\end{array}\right]=\left[\begin{array}{cc}
\Re p & -\Im p \\
\Im p & \Re p
\end{array}\right]\left[\begin{array}{l}
\Re q \\
\Im q
\end{array}\right]
$$

\subsection{Complex Derivatives}

In order to differentiate an expression $f(z)$ with respect to a complex $z$, the Cauchy-Riemann equations have to be satisfied ([7]):

$$
\frac{d f(z)}{d z}=\frac{\partial \Re(f(z))}{\partial \Re z}+i \frac{\partial \Im(f(z))}{\partial \Re z}
$$

and

$$
\frac{d f(z)}{d z}=-i \frac{\partial \Re(f(z))}{\partial \Im z}+\frac{\partial \Im(f(z))}{\partial \Im z}
$$

or in a more compact form:

$$
\frac{\partial f(z)}{\partial \Im z}=i \frac{\partial f(z)}{\partial \Re z}
$$

A complex function that satisfies the Cauchy-Riemann equations for points in a region $\mathrm{R}$ is said yo be analytic in this region $\mathrm{R}$. In general, expressions involving complex conjugate or conjugate transpose do not satisfy the Cauchy-Riemann equations. In order to avoid this problem, a more generalized definition of complex derivative is used ([24, [6]):

- Generalized Complex Derivative:

$$
\frac{d f(z)}{d z}=\frac{1}{2}\left(\frac{\partial f(z)}{\partial \Re z}-i \frac{\partial f(z)}{\partial \Im z}\right) .
$$

- Conjugate Complex Derivative

$$
\frac{d f(z)}{d z^{*}}=\frac{1}{2}\left(\frac{\partial f(z)}{\partial \Re z}+i \frac{\partial f(z)}{\partial \Im z}\right) .
$$

The Generalized Complex Derivative equals the normal derivative, when $f$ is an analytic function. For a non-analytic function such as $f(z)=z^{*}$, the derivative equals zero. The Conjugate Complex Derivative equals zero, when $f$ is an analytic function. The Conjugate Complex Derivative has e.g been used by [21] when deriving a complex gradient.

Notice:

$$
\frac{d f(z)}{d z} \neq \frac{\partial f(z)}{\partial \Re z}+i \frac{\partial f(z)}{\partial \Im z} .
$$

- Complex Gradient Vector: If $f$ is a real function of a complex vector $\mathbf{z}$, then the complex gradient vector is given by ([14, p. 798])

$$
\begin{aligned}
\nabla f(\mathbf{z}) & =2 \frac{d f(\mathbf{z})}{d \mathbf{z}^{*}} \\
& =\frac{\partial f(\mathbf{z})}{\partial \Re \mathbf{z}}+i \frac{\partial f(\mathbf{z})}{\partial \Im \mathbf{z}} .
\end{aligned}
$$

- Complex Gradient Matrix: If $f$ is a real function of a complex matrix $\mathbf{Z}$, then the complex gradient matrix is given by $([2])$

$$
\begin{aligned}
\nabla f(\mathbf{Z}) & =2 \frac{d f(\mathbf{Z})}{d \mathbf{Z}^{*}} \\
& =\frac{\partial f(\mathbf{Z})}{\partial \Re \mathbf{Z}}+i \frac{\partial f(\mathbf{Z})}{\partial \Im \mathbf{Z}} .
\end{aligned}
$$

These expressions can be used for gradient descent algorithms.

\subsubsection{The Chain Rule for complex numbers}

The chain rule is a little more complicated when the function of a complex $u=f(x)$ is non-analytic. For a non-analytic function, the following chain rule can be applied $([7])$

$$
\begin{aligned}
\frac{\partial g(u)}{\partial x} & =\frac{\partial g}{\partial u} \frac{\partial u}{\partial x}+\frac{\partial g}{\partial u^{*}} \frac{\partial u^{*}}{\partial x} \\
& =\frac{\partial g}{\partial u} \frac{\partial u}{\partial x}+\left(\frac{\partial g^{*}}{\partial u}\right)^{*} \frac{\partial u^{*}}{\partial x}
\end{aligned}
$$

Notice, if the function is analytic, the second term reduces to zero, and the function is reduced to the normal well-known chain rule. For the matrix derivative of a scalar function $g(\mathbf{U})$, the chain rule can be written the following way:

$$
\frac{\partial g(\mathbf{U})}{\partial \mathbf{X}}=\frac{\operatorname{Tr}\left(\left(\frac{\partial g(\mathbf{U})}{\partial \mathbf{U}}\right)^{T} \partial \mathbf{U}\right)}{\partial \mathbf{X}}+\frac{\operatorname{Tr}\left(\left(\frac{\partial g(\mathbf{U})}{\partial \mathbf{U}^{*}}\right)^{T} \partial \mathbf{U}^{*}\right)}{\partial \mathbf{X}} .
$$

\subsubsection{Complex Derivatives of Traces}

If the derivatives involve complex numbers, the conjugate transpose is often involved. The most useful way to show complex derivative is to show the derivative with respect to the real and the imaginary part separately. An easy example is:

$$
\begin{aligned}
& \frac{\partial \operatorname{Tr}\left(\mathbf{X}^{*}\right)}{\partial \Re \mathbf{X}}=\frac{\partial \operatorname{Tr}\left(\mathbf{X}^{H}\right)}{\partial \Re \mathbf{X}}=\mathbf{I} \\
& i \frac{\partial \operatorname{Tr}\left(\mathbf{X}^{*}\right)}{\partial \Im \mathbf{X}}=i \frac{\partial \operatorname{Tr}\left(\mathbf{X}^{H}\right)}{\partial \Im \mathbf{X}}=\mathbf{I}
\end{aligned}
$$

Since the two results have the same sign, the conjugate complex derivative 230 should be used.

$$
\begin{aligned}
\frac{\partial \operatorname{Tr}(\mathbf{X})}{\partial \Re \mathbf{X}} & =\frac{\partial \operatorname{Tr}\left(\mathbf{X}^{T}\right)}{\partial \Re \mathbf{X}}=\mathbf{I} \\
i \frac{\partial \operatorname{Tr}(\mathbf{X})}{\partial \Im \mathbf{X}} & =i \frac{\partial \operatorname{Tr}\left(\mathbf{X}^{T}\right)}{\partial \Im \mathbf{X}}=-\mathbf{I}
\end{aligned}
$$

Here, the two results have different signs, and the generalized complex derivative (229) should be used. Hereby, it can be seen that 100 holds even if $\mathbf{X}$ is a complex number.

$$
\begin{aligned}
\frac{\partial \operatorname{Tr}\left(\mathbf{A} \mathbf{X}^{H}\right)}{\partial \Re \mathbf{X}} & =\mathbf{A} \\
i \frac{\partial \operatorname{Tr}\left(\mathbf{A} \mathbf{X}^{H}\right)}{\partial \Im \mathbf{X}} & =\mathbf{A}
\end{aligned}
$$



$$
\begin{gathered}
\frac{\partial \operatorname{Tr}\left(\mathbf{A} \mathbf{X}^{*}\right)}{\partial \Re \mathbf{X}}=\mathbf{A}^{T} \\
i \frac{\partial \operatorname{Tr}\left(\mathbf{A} \mathbf{X}^{*}\right)}{\partial \Im \mathbf{X}}=\mathbf{A}^{T} \\
\frac{\partial \operatorname{Tr}\left(\mathbf{X X}^{H}\right)}{\partial \Re \mathbf{X}}=\frac{\partial \operatorname{Tr}\left(\mathbf{X}^{H} \mathbf{X}\right)}{\partial \Re \mathbf{X}}=2 \Re \mathbf{X} \\
i \frac{\partial \operatorname{Tr}\left(\mathbf{X} \mathbf{X}^{H}\right)}{\partial \Im \mathbf{X}}=i \frac{\partial \operatorname{Tr}\left(\mathbf{X}^{H} \mathbf{X}\right)}{\partial \Im \mathbf{X}}=i 2 \Im \mathbf{X}
\end{gathered}
$$

By inserting 244 and 245 in 229 and 230 , it can be seen that

$$
\begin{aligned}
\frac{\partial \operatorname{Tr}\left(\mathbf{X X}^{H}\right)}{\partial \mathbf{X}} & =\mathbf{X}^{*} \\
\frac{\partial \operatorname{Tr}\left(\mathbf{X} \mathbf{X}^{H}\right)}{\partial \mathbf{X}^{*}} & =\mathbf{X}
\end{aligned}
$$

Since the function $\operatorname{Tr}\left(\mathbf{X} \mathbf{X}^{H}\right)$ is a real function of the complex matrix $\mathbf{X}$, the complex gradient matrix 233 is given by

$$
\nabla \operatorname{Tr}\left(\mathbf{X X}^{H}\right)=2 \frac{\partial \operatorname{Tr}\left(\mathbf{X} \mathbf{X}^{H}\right)}{\partial \mathbf{X}^{*}}=2 \mathbf{X}
$$

\subsubsection{Complex Derivative Involving Determinants}

Here, a calculation example is provided. The objective is to find the derivative of $\operatorname{det}\left(\mathbf{X}^{H} \mathbf{A X}\right)$ with respect to $\mathbf{X} \in \mathbb{C}^{m \times n}$. The derivative is found with respect to the real part and the imaginary part of $\mathbf{X}$, by use of $(42)$ and $(37), \operatorname{det}\left(\mathbf{X}^{H} \mathbf{A X}\right)$ can be calculated as (see App. B.1.4 for details)

$$
\begin{aligned}
\frac{\partial \operatorname{det}\left(\mathbf{X}^{H} \mathbf{A} \mathbf{X}\right)}{\partial \mathbf{X}} & =\frac{1}{2}\left(\frac{\partial \operatorname{det}\left(\mathbf{X}^{H} \mathbf{A} \mathbf{X}\right)}{\partial \Re \mathbf{X}}-i \frac{\partial \operatorname{det}\left(\mathbf{X}^{H} \mathbf{A} \mathbf{X}\right)}{\partial \Im \mathbf{X}}\right) \\
& =\operatorname{det}\left(\mathbf{X}^{H} \mathbf{A} \mathbf{X}\right)\left(\left(\mathbf{X}^{H} \mathbf{A} \mathbf{X}\right)^{-1} \mathbf{X}^{H} \mathbf{A}\right)^{T}
\end{aligned}
$$

and the complex conjugate derivative yields

$$
\begin{aligned}
\frac{\partial \operatorname{det}\left(\mathbf{X}^{H} \mathbf{A} \mathbf{X}\right)}{\partial \mathbf{X}^{*}} & =\frac{1}{2}\left(\frac{\partial \operatorname{det}\left(\mathbf{X}^{H} \mathbf{A} \mathbf{X}\right)}{\partial \Re \mathbf{X}}+i \frac{\partial \operatorname{det}\left(\mathbf{X}^{H} \mathbf{A} \mathbf{X}\right)}{\partial \Im \mathbf{X}}\right) \\
& =\operatorname{det}\left(\mathbf{X}^{H} \mathbf{A} \mathbf{X}\right) \mathbf{A} \mathbf{X}\left(\mathbf{X}^{H} \mathbf{A} \mathbf{X}\right)^{-1}
\end{aligned}
$$

\subsection{Higher order and non-linear derivatives}

$$
\begin{aligned}
\frac{\partial}{\partial \mathbf{x}} \frac{(\mathbf{A} \mathbf{x})^{H}(\mathbf{A} \mathbf{x})}{(\mathbf{B} \mathbf{x})^{H}(\mathbf{B} \mathbf{x})} & =\frac{\partial}{\partial \mathbf{x}} \frac{\mathbf{x}^{H} \mathbf{A}^{H} \mathbf{A} \mathbf{x}}{\mathbf{x}^{H} \mathbf{B}^{H} \mathbf{B} \mathbf{x}} \\
& =2 \frac{\mathbf{A}^{H} \mathbf{A} \mathbf{x}}{\mathbf{x}^{H} \mathbf{B} \mathbf{B} \mathbf{x}}-2 \frac{\mathbf{x}^{H} \mathbf{A}^{H} \mathbf{A} \mathbf{x} \mathbf{B}^{H} \mathbf{B} \mathbf{x}}{\left(\mathbf{x}^{H} \mathbf{B}^{H} \mathbf{B} \mathbf{x}\right)^{2}}
\end{aligned}
$$



\subsection{Inverse of complex sum}

Given real matrices $\mathbf{A}, \mathbf{B}$ find the inverse of the complex sum $\mathbf{A}+i \mathbf{B}$. Form the auxiliary matrices

$$
\begin{aligned}
& \mathbf{E}=\mathbf{A}+t \mathbf{B} \\
& \mathbf{F}=\mathbf{B}-t \mathbf{A},
\end{aligned}
$$

and find a value of $t$ such that $\mathbf{E}^{-1}$ exists. Then

$$
\begin{aligned}
(\mathbf{A}+i \mathbf{B})^{-1}= & (1-i t)(\mathbf{E}+i \mathbf{F})^{-1} \\
= & (1-i t)\left(\left(\mathbf{E}+\mathbf{F} \mathbf{E}^{-1} \mathbf{F}\right)^{-1}-i\left(\mathbf{E}+\mathbf{F} \mathbf{E}^{-1} \mathbf{F}\right)^{-1} \mathbf{F E}^{-1}\right)\left(25 \mathbf{E}^{-1} \mathbf{F}\right)^{-1}\left(\mathbf{I}-i \mathbf{F} \mathbf{E}^{-1}\right) \\
= & (1-i t)\left(\mathbf{E}+\mathbf{F} \mathbf{E}^{-1}\right. \\
= & \left(\mathbf{E}+\mathbf{F} \mathbf{E}^{-1} \mathbf{F}\right)^{-1}\left(\left(\mathbf{I}-t \mathbf{F} \mathbf{E}^{-1}\right)-i\left(t \mathbf{I}+\mathbf{F} \mathbf{E}^{-1}\right)\right) \\
= & \left(\mathbf{E}+\mathbf{F} \mathbf{E}^{-1} \mathbf{F}\right)^{-1}\left(\mathbf{I}-t \mathbf{F} \mathbf{E}^{-1}\right) \\
& -i\left(\mathbf{E}+\mathbf{F} \mathbf{E}^{-1} \mathbf{F}\right)^{-1}\left(t \mathbf{I}+\mathbf{F} \mathbf{E}^{-1}\right)
\end{aligned}
$$



\section{Solutions and Decompositions}

\subsection{Solutions to linear equations}

\subsubsection{Simple Linear Regression}

Assume we have data $\left(x_{n}, y_{n}\right)$ for $n=1, \ldots, N$ and are seeking the parameters $a, b \in \mathbb{R}$ such that $y_{i} \cong a x_{i}+b$. With a least squares error function, the optimal values for $a, b$ can be expressed using the notation

$$
\mathbf{x}=\left(x_{1}, \ldots, x_{N}\right)^{T} \quad \mathbf{y}=\left(y_{1}, \ldots, y_{N}\right)^{T} \quad \mathbf{1}=(1, \ldots, 1)^{T} \in \mathbb{R}^{N \times 1}
$$

and

$$
\begin{array}{lll}
R_{x x}=\mathbf{x}^{T} \mathbf{x} & R_{x 1}=\mathbf{x}^{T} \mathbf{1} & R_{11}=\mathbf{1}^{T} \mathbf{1} \\
R_{y x}=\mathbf{y}^{T} \mathbf{x} & R_{y 1}=\mathbf{y}^{T} \mathbf{1} &
\end{array}
$$

as

$$
\left[\begin{array}{l}
a \\
b
\end{array}\right]=\left[\begin{array}{ll}
R_{x x} & R_{x 1} \\
R_{x 1} & R_{11}
\end{array}\right]^{-1}\left[\begin{array}{c}
R_{x, y} \\
R_{y 1}
\end{array}\right]
$$

\subsubsection{Existence in Linear Systems}

Assume $\mathbf{A}$ is $n \times m$ and consider the linear system

$$
\mathbf{A x}=\mathbf{b}
$$

Construct the augmented matrix $\mathbf{B}=\left[\begin{array}{ll}\mathbf{A} & \mathbf{b}\end{array}\right]$ then

$$
\begin{array}{ll}
\text { Condition } & \text { Solution } \\
\operatorname{rank}(\mathbf{A})=\operatorname{rank}(\mathbf{B})=m & \text { Unique solution } \mathbf{x} \\
\operatorname{rank}(\mathbf{A})=\operatorname{rank}(\mathbf{B})<m & \text { Many solutions } \mathbf{x} \\
\operatorname{rank}(\mathbf{A})<\operatorname{rank}(\mathbf{B}) & \text { No solutions } \mathbf{x}
\end{array}
$$

\subsubsection{Standard Square}

Assume $\mathbf{A}$ is square and invertible, then

$$
\mathbf{A x}=\mathbf{b} \quad \Rightarrow \quad \mathbf{x}=\mathbf{A}^{-1} \mathbf{b}
$$

\subsubsection{Degenerated Square}

Assume $\mathbf{A}$ is $n \times n$ but of rank $r<n$. In that case, the system $\mathbf{A x}=\mathbf{b}$ is solved by

$$
\mathbf{x}=\mathbf{A}^{+} \mathbf{b}
$$

where $\mathbf{A}^{+}$is the pseudo-inverse of the rank-deficient matrix, constructed as described in section 3.6 .3 

\subsubsection{Cramer's rule}

The equation

$$
\mathbf{A x}=\mathbf{b}
$$

where $\mathbf{A}$ is square has exactly one solution $\mathbf{x}$ if the $i$ th element in $x$ can be found as

$$
x_{i}=\frac{\operatorname{det} \mathbf{B}}{\operatorname{det} \mathbf{A}},
$$

where $\mathbf{B}$ equals $\mathbf{A}$, but the $i$ th column in $\mathbf{A}$ has been substituted by $\mathbf{b}$.

\subsubsection{Over-determined Rectangular}

Assume A to be $n \times m, n>m$ (tall) and $\operatorname{rank}(\mathbf{A})=m$, then

$$
\mathbf{A} \mathbf{x}=\mathbf{b} \quad \Rightarrow \quad \mathbf{x}=\left(\mathbf{A}^{T} \mathbf{A}\right)^{-1} \mathbf{A}^{T} \mathbf{b}=\mathbf{A}^{+} \mathbf{b}
$$

that is if there exists a solution $\mathrm{x}$ at all! If there is no solution the following can be useful:

$$
\mathbf{A} \mathbf{x}=\mathbf{b} \quad \Rightarrow \quad \mathbf{x}_{\min }=\mathbf{A}^{+} \mathbf{b}
$$

Now $\mathbf{x}_{\text {min }}$ is the vector $\mathbf{x}$ which minimizes $\|\mathbf{A} \mathbf{x}-\mathbf{b}\|^{2}$, i.e. the vector which is "least wrong". The matrix $\mathbf{A}^{+}$is the pseudo-inverse of $\mathbf{A}$. See [3.

\subsubsection{Under-determined Rectangular}

Assume $\mathbf{A}$ is $n \times m$ and $n<m$ ("broad") and $\operatorname{rank}(\mathbf{A})=n$.

$$
\mathbf{A} \mathbf{x}=\mathbf{b} \quad \Rightarrow \quad \mathbf{x}_{\min }=\mathbf{A}^{T}\left(\mathbf{A} \mathbf{A}^{T}\right)^{-1} \mathbf{b}
$$

The equation have many solutions $\mathbf{x}$. But $\mathbf{x}_{\min }$ is the solution which minimizes $\|\mathbf{A} \mathbf{x}-\mathbf{b}\|^{2}$ and also the solution with the smallest norm $\|\mathbf{x}\|^{2}$. The same holds for a matrix version: Assume $\mathbf{A}$ is $n \times m, \mathbf{X}$ is $m \times n$ and $\mathbf{B}$ is $n \times n$, then

$$
\mathbf{A X}=\mathbf{B} \quad \Rightarrow \quad \mathbf{X}_{\min }=\mathbf{A}^{+} \mathbf{B}
$$

The equation have many solutions $\mathbf{X}$. But $\mathbf{X}_{\min }$ is the solution which minimizes $\|\mathbf{A X}-\mathbf{B}\|^{2}$ and also the solution with the smallest norm $\|\mathbf{X}\|^{2}$. See [3.

Similar but different: Assume $\mathbf{A}$ is square $n \times n$ and the matrices $\mathbf{B}_{0}, \mathbf{B}_{1}$ are $n \times N$, where $N>n$, then if $\mathbf{B}_{0}$ has maximal rank

$$
\mathbf{A B}_{0}=\mathbf{B}_{1} \quad \Rightarrow \quad \mathbf{A}_{\min }=\mathbf{B}_{1} \mathbf{B}_{0}^{T}\left(\mathbf{B}_{0} \mathbf{B}_{0}^{T}\right)^{-1}
$$

where $\mathbf{A}_{\min }$ denotes the matrix which is optimal in a least square sense. An interpretation is that $\mathbf{A}$ is the linear approximation which maps the columns vectors of $\mathbf{B}_{0}$ into the columns vectors of $\mathbf{B}_{1}$.

\subsubsection{Linear form and zeros}

$$
\mathbf{A x}=\mathbf{0}, \quad \forall \mathbf{x} \quad \Rightarrow \quad \mathbf{A}=\mathbf{0}
$$

\subsubsection{Square form and zeros}

If $\mathbf{A}$ is symmetric, then

$$
\mathrm{x}^{T} \mathbf{A} \mathbf{x}=\mathbf{0}, \quad \forall \mathrm{x} \quad \Rightarrow \quad \mathbf{A}=\mathbf{0}
$$

5.1.10 The Lyapunov Equation

$$
\begin{aligned}
\mathbf{A X}+\mathbf{X B} & =\mathbf{C} \\
\operatorname{vec}(\mathbf{X}) & =\left(\mathbf{I} \otimes \mathbf{A}+\mathbf{B}^{T} \otimes \mathbf{I}\right)^{-1} \operatorname{vec}(\mathbf{C})
\end{aligned}
$$

Sec 10.2 .1 and 10.2 .2 for details on the Kronecker product and the vec operator.

\subsubsection{Encapsulating Sum}

$$
\begin{aligned}
\sum_{n} \mathbf{A}_{n} \mathbf{X B}_{n} & =\mathbf{C} \\
\operatorname{vec}(\mathbf{X}) & =\left(\sum_{n} \mathbf{B}_{n}^{T} \otimes \mathbf{A}_{n}\right)^{-1} \operatorname{vec}(\mathbf{C})
\end{aligned}
$$

See Sec 10.2.1 and 10.2.2 for details on the Kronecker product and the vec operator.

\subsection{Eigenvalues and Eigenvectors}

\subsubsection{Definition}

The eigenvectors $\mathbf{v}_{i}$ and eigenvalues $\lambda_{i}$ are the ones satisfying

$$
\mathbf{A v}_{i}=\lambda_{i} \mathbf{v}_{i}
$$

\subsubsection{Decompositions}

For matrices $\mathbf{A}$ with as many distinct eigenvalues as dimensions, the following holds, where the columns of $\mathbf{V}$ are the eigenvectors and $(\mathbf{D})_{i j}=\delta_{i j} \lambda_{i}$,

$$
\mathbf{A V}=\mathbf{V D}
$$

For defective matrices $\mathbf{A}$, which is matrices which has fewer distinct eigenvalues than dimensions, the following decomposition called Jordan canonical form, holds

$$
\mathbf{A V}=\mathbf{V J}
$$

where $\mathbf{J}$ is a block diagonal matrix with the blocks $\mathbf{J}_{i}=\lambda_{i} \mathbf{I}+\mathbf{N}$. The matrices $\mathbf{J}_{i}$ have dimensionality as the number of identical eigenvalues equal to $\lambda_{i}$, and $\mathbf{N}$ is square matrix of same size with 1 on the super diagonal and zero elsewhere.

It also holds that for all matrices $\mathbf{A}$ there exists matrices $\mathbf{V}$ and $\mathbf{R}$ such that

$$
\mathbf{A V}=\mathbf{V R}
$$

where $\mathbf{R}$ is upper triangular with the eigenvalues $\lambda_{i}$ on its diagonal.

\subsubsection{General Properties}

Assume that $\mathbf{A} \in \mathbb{R}^{n \times m}$ and $\mathbf{B} \in \mathbb{R}^{m \times n}$,

$$
\begin{aligned}
\operatorname{eig}(\mathbf{A B}) & =\operatorname{eig}(\mathbf{B A}) \\
\operatorname{rank}(\mathbf{A})=r & \Rightarrow \text { At most } r \text { non-zero } \lambda_{i}
\end{aligned}
$$



\subsubsection{Symmetric}

Assume $\mathbf{A}$ is symmetric, then

$$
\begin{aligned}
\mathbf{V} \mathbf{V}^{T} & =\mathbf{I} \quad \text { (i.e. } \mathbf{V} \text { is orthogonal) } \\
\lambda_{i} & \in \mathbb{R} \quad\left(\text { i.e. } \lambda_{i}\right. \text { is real) } \\
\operatorname{Tr}\left(\mathbf{A}^{p}\right) & =\sum_{i} \lambda_{i}^{p} \\
\operatorname{eig}(\mathbf{I}+c \mathbf{A}) & =1+c \lambda_{i} \\
\operatorname{eig}(\mathbf{A}-c \mathbf{I}) & =\lambda_{i}-c \\
\operatorname{eig}\left(\mathbf{A}^{-1}\right) & =\lambda_{i}^{-1}
\end{aligned}
$$

For a symmetric, positive matrix $\mathbf{A}$,

$$
\operatorname{eig}\left(\mathbf{A}^{T} \mathbf{A}\right)=\operatorname{eig}\left(\mathbf{A A}^{T}\right)=\operatorname{eig}(\mathbf{A}) \circ \operatorname{eig}(\mathbf{A})
$$

\subsubsection{Characteristic polynomial}

The characteristic polynomial for the matrix $\mathbf{A}$ is

$$
\begin{aligned}
0 & =\operatorname{det}(\mathbf{A}-\lambda \mathbf{I}) \\
& =\lambda^{n}-g_{1} \lambda^{n-1}+g_{2} \lambda^{n-2}-\ldots+(-1)^{n} g_{n}
\end{aligned}
$$

Note that the coefficients $g_{j}$ for $j=1, \ldots, n$ are the $n$ invariants under rotation of $\mathbf{A}$. Thus, $g_{j}$ is the sum of the determinants of all the sub-matrices of $\mathbf{A}$ taken $j$ rows and columns at a time. That is, $g_{1}$ is the trace of $\mathbf{A}$, and $g_{2}$ is the sum of the determinants of the $n(n-1) / 2$ sub-matrices that can be formed from $\mathbf{A}$ by deleting all but two rows and columns, and so on - see [17.

\subsection{Singular Value Decomposition}

Any $n \times m$ matrix $\mathbf{A}$ can be written as

$$
\mathbf{A}=\mathbf{U D V}^{T}
$$

where

$$
\begin{array}{ll}
\mathbf{U}=\text { eigenvectors of } \mathbf{A} \mathbf{A}^{T} & n \times n \\
\mathbf{D}=\sqrt{\operatorname{diag}\left(\operatorname{eig}\left(\mathbf{A A}^{T}\right)\right)} & n \times m \\
\mathbf{V}=\text { eigenvectors of } \mathbf{A}^{T} \mathbf{A} & m \times m
\end{array}
$$

\subsubsection{Symmetric Square decomposed into squares}

Assume $\mathbf{A}$ to be $n \times n$ and symmetric. Then

$$
[\mathbf{A}]=[\mathbf{V}][\mathbf{D}]\left[\mathbf{V}^{T}\right]
$$

where $\mathbf{D}$ is diagonal with the eigenvalues of $\mathbf{A}$, and $\mathbf{V}$ is orthogonal and the eigenvectors of $\mathbf{A}$.

\subsubsection{Square decomposed into squares}

Assume $\mathbf{A} \in \mathbb{R}^{n \times n}$. Then

$$
[\mathbf{A}]=[\mathbf{V}][\mathbf{D}]\left[\mathbf{U}^{T}\right]
$$

where $\mathbf{D}$ is diagonal with the square root of the eigenvalues of $\mathbf{A} \mathbf{A}^{T}, \mathbf{V}$ is the eigenvectors of $\mathbf{A} \mathbf{A}^{T}$ and $\mathbf{U}^{T}$ is the eigenvectors of $\mathbf{A}^{T} \mathbf{A}$. 

\subsubsection{Square decomposed into rectangular}

Assume $\mathbf{V}_{*} \mathbf{D}_{*} \mathbf{U}_{*}^{T}=\mathbf{0}$ then we can expand the SVD of $\mathbf{A}$ into

$$
[\mathbf{A}]=\left[\mathbf{V} \mid \mathbf{V}_{*}\right]\left[\begin{array}{c|c}
\mathbf{D} & \mathbf{0} \\
\hline \mathbf{0} & \mathbf{D}_{*}
\end{array}\right]\left[\begin{array}{l}
\mathbf{U}^{T} \\
\hline \mathbf{U}_{*}^{T}
\end{array}\right]
$$

where the SVD of $\mathbf{A}$ is $\mathbf{A}=\mathbf{V D U}^{T}$.

\subsubsection{Rectangular decomposition I}

Assume $\mathbf{A}$ is $n \times m, \mathbf{V}$ is $n \times n, \mathbf{D}$ is $n \times n, \mathbf{U}^{T}$ is $n \times m$

$$
\mathbf{A} \quad]=[\mathbf{V}][\mathbf{D}]\left[\mathbf{U}^{T}\right]
$$

where $\mathbf{D}$ is diagonal with the square root of the eigenvalues of $\mathbf{A} \mathbf{A}^{T}, \mathbf{V}$ is the eigenvectors of $\mathbf{A} \mathbf{A}^{T}$ and $\mathbf{U}^{T}$ is the eigenvectors of $\mathbf{A}^{T} \mathbf{A}$.

\subsubsection{Rectangular decomposition II}

Assume $\mathbf{A}$ is $n \times m, \mathbf{V}$ is $n \times m, \mathbf{D}$ is $m \times m, \mathbf{U}^{T}$ is $m \times m$

![](https://cdn.mathpix.com/cropped/2023_03_18_f0df469e0efa0d384ef8g-32.jpg?height=156&width=784&top_left_y=1241&top_left_x=636)

\subsubsection{Rectangular decomposition III}

Assume $\mathbf{A}$ is $n \times m, \mathbf{V}$ is $n \times n, \mathbf{D}$ is $n \times m, \mathbf{U}^{T}$ is $m \times m$

![](https://cdn.mathpix.com/cropped/2023_03_18_f0df469e0efa0d384ef8g-32.jpg?height=150&width=721&top_left_y=1547&top_left_x=673)

where $\mathbf{D}$ is diagonal with the square root of the eigenvalues of $\mathbf{A} \mathbf{A}^{T}, \mathbf{V}$ is the eigenvectors of $\mathbf{A} \mathbf{A}^{T}$ and $\mathbf{U}^{T}$ is the eigenvectors of $\mathbf{A}^{T} \mathbf{A}$.

\subsection{Triangular Decomposition}

\subsection{LU decomposition}

Assume $\mathbf{A}$ is a square matrix with non-zero leading principal minors, then

$$
\mathbf{A}=\mathbf{L U}
$$

where $\mathbf{L}$ is a unique unit lower triangular matrix and $\mathbf{U}$ is a unique upper triangular matrix.

\subsubsection{Cholesky-decomposition}

Assume $\mathbf{A}$ is a symmetric positive definite square matrix, then

$$
\mathbf{A}=\mathbf{U}^{T} \mathbf{U}=\mathbf{L L}^{T}
$$

where $\mathbf{U}$ is a unique upper triangular matrix and $\mathbf{L}$ is a lower triangular matrix. 

\subsection{LDM decomposition}

Assume $\mathbf{A}$ is a square matrix with non-zero leading principal minors ${ }^{1}$ then

$$
\mathbf{A}=\mathbf{L D M}^{T}
$$

where $\mathbf{L}, \mathbf{M}$ are unique unit lower triangular matrices and $\mathbf{D}$ is a unique diagonal matrix.

\subsection{LDL decompositions}

The LDL decomposition are special cases of the LDM decomposition. Assume $\mathbf{A}$ is a non-singular symmetric definite square matrix, then

$$
\mathbf{A}=\mathbf{L D L}^{T}=\mathbf{L}^{T} \mathbf{D} \mathbf{L}
$$

where $\mathbf{L}$ is a unit lower triangular matrix and $\mathbf{D}$ is a diagonal matrix. If $\mathbf{A}$ is also positive definite, then $\mathbf{D}$ has strictly positive diagonal entries.

${ }^{1}$ If the matrix that corresponds to a principal minor is a quadratic upper-left part of the larger matrix (i.e., it consists of matrix elements in rows and columns from 1 to $\mathrm{k}$ ), then the principal minor is called a leading principal minor. For an $\mathrm{n}$ times $\mathrm{n}$ square matrix, there are n leading principal minors. 31 

\section{Statistics and Probability}

\subsection{Definition of Moments}

Assume $\mathbf{x} \in \mathbb{R}^{n \times 1}$ is a random variable

\subsubsection{Mean}

The vector of means, $\mathbf{m}$, is defined by

$$
(\mathbf{m})_{i}=\left\langle x_{i}\right\rangle
$$

\subsubsection{Covariance}

The matrix of covariance $\mathbf{M}$ is defined by

$$
(\mathbf{M})_{i j}=\left\langle\left(x_{i}-\left\langle x_{i}\right\rangle\right)\left(x_{j}-\left\langle x_{j}\right\rangle\right)\right\rangle
$$

or alternatively as

$$
\mathbf{M}=\left\langle(\mathbf{x}-\mathbf{m})(\mathbf{x}-\mathbf{m})^{T}\right\rangle
$$

\subsubsection{Third moments}

The matrix of third centralized moments - in some contexts referred to as coskewness - is defined using the notation

$$
m_{i j k}^{(3)}=\left\langle\left(x_{i}-\left\langle x_{i}\right\rangle\right)\left(x_{j}-\left\langle x_{j}\right\rangle\right)\left(x_{k}-\left\langle x_{k}\right\rangle\right)\right\rangle
$$

as

$$
\mathbf{M}_{3}=\left[m_{:: 1}^{(3)} m_{:: 2}^{(3)} \ldots m_{:: n}^{(3)}\right]
$$

where ':' denotes all elements within the given index. $\mathbf{M}_{3}$ can alternatively be expressed as

$$
\mathbf{M}_{3}=\left\langle(\mathbf{x}-\mathbf{m})(\mathbf{x}-\mathbf{m})^{T} \otimes(\mathbf{x}-\mathbf{m})^{T}\right\rangle
$$

\subsubsection{Fourth moments}

The matrix of fourth centralized moments - in some contexts referred to as cokurtosis - is defined using the notation

$$
m_{i j k l}^{(4)}=\left\langle\left(x_{i}-\left\langle x_{i}\right\rangle\right)\left(x_{j}-\left\langle x_{j}\right\rangle\right)\left(x_{k}-\left\langle x_{k}\right\rangle\right)\left(x_{l}-\left\langle x_{l}\right\rangle\right)\right\rangle
$$

as

$$
\mathbf{M}_{4}=\left[m_{:: 11}^{(4)} m_{:: 21}^{(4)} \ldots m_{:: n 1}^{(4)}\left|m_{:: 12}^{(4)} m_{:: 22}^{(4)} \ldots m_{:: n 2}^{(4)}\right| \ldots \mid m_{:: 1 n}^{(4)} m_{:: 2 n}^{(4)} \ldots m_{:: n n}^{(4)}\right]
$$

or alternatively as

$$
\mathbf{M}_{4}=\left\langle(\mathbf{x}-\mathbf{m})(\mathbf{x}-\mathbf{m})^{T} \otimes(\mathbf{x}-\mathbf{m})^{T} \otimes(\mathbf{x}-\mathbf{m})^{T}\right\rangle
$$



\subsection{Expectation of Linear Combinations}

\subsubsection{Linear Forms}

Assume $\mathbf{X}$ and $\mathbf{x}$ to be a matrix and a vector of random variables. Then (see See 26$]$

$$
\begin{aligned}
E[\mathbf{A X B}+\mathbf{C}] & =\mathbf{A} E[\mathbf{X}] \mathbf{B}+\mathbf{C} \\
\operatorname{Var}[\mathbf{A} \mathbf{x}] & =\mathbf{A} \operatorname{Var}[\mathbf{x}] \mathbf{A}^{T} \\
\operatorname{Cov}[\mathbf{A} \mathbf{x}, \mathbf{B} \mathbf{y}] & =\mathbf{A} \operatorname{Cov}[\mathbf{x}, \mathbf{y}] \mathbf{B}^{T}
\end{aligned}
$$

Assume $\mathbf{x}$ to be a stochastic vector with mean $\mathbf{m}$, then (see [7)

$$
\begin{aligned}
E[\mathbf{A} \mathbf{x}+\mathbf{b}] & =\mathbf{A} \mathbf{m}+\mathbf{b} \\
E[\mathbf{A} \mathbf{x}] & =\mathbf{A} \mathbf{m} \\
E[\mathbf{x}+\mathbf{b}] & =\mathbf{m}+\mathbf{b}
\end{aligned}
$$

\subsubsection{Quadratic Forms}

Assume $\mathbf{A}$ is symmetric, $\mathbf{c}=E[\mathbf{x}]$ and $\boldsymbol{\Sigma}=\operatorname{Var}[\mathbf{x}]$. Assume also that all coordinates $x_{i}$ are independent, have the same central moments $\mu_{1}, \mu_{2}, \mu_{3}, \mu_{4}$ and denote $\mathbf{a}=\operatorname{diag}(\mathbf{A})$. Then $($ See $[26]$

$$
\begin{aligned}
E\left[\mathbf{x}^{T} \mathbf{A} \mathbf{x}\right] & =\operatorname{Tr}(\mathbf{A} \boldsymbol{\Sigma})+\mathbf{c}^{T} \mathbf{A} \mathbf{c} \\
\operatorname{Var}\left[\mathbf{x}^{T} \mathbf{A} \mathbf{x}\right] & =2 \mu_{2}^{2} \operatorname{Tr}\left(\mathbf{A}^{2}\right)+4 \mu_{2} \mathbf{c}^{T} \mathbf{A}^{2} \mathbf{c}+4 \mu_{3} \mathbf{c}^{T} \mathbf{A} \mathbf{a}+\left(\mu_{4}-3 \mu_{2}^{2}\right) \mathbf{a}^{T} \mathbf{a}
\end{aligned}
$$

Also, assume $\mathbf{x}$ to be a stochastic vector with mean $\mathbf{m}$, and covariance $\mathbf{M}$. Then $(\sec [7)$

$$
\begin{aligned}
E\left[(\mathbf{A} \mathbf{x}+\mathbf{a})(\mathbf{B} \mathbf{x}+\mathbf{b})^{T}\right] & =\mathbf{A} \mathbf{M B} \mathbf{B}^{T}+(\mathbf{A} \mathbf{m}+\mathbf{a})(\mathbf{B} \mathbf{m}+\mathbf{b})^{T} \\
E\left[\mathbf{x} \mathbf{x}^{T}\right] & =\mathbf{M}+\mathbf{m}^{T} \\
E\left[\mathbf{\mathbf { x } ^ { T } \mathbf { x } ]}\right. & =\left(\mathbf{M}+\mathbf{m}^{T}\right) \mathbf{a} \\
E\left[\mathbf{x}^{T} \mathbf{a} \mathbf{x}^{T}\right] & =\mathbf{a}^{T}\left(\mathbf{M}+\mathbf{m} \mathbf{m}^{T}\right) \\
E\left[(\mathbf{A} \mathbf{x})(\mathbf{A} \mathbf{x})^{T}\right] & =\mathbf{A}\left(\mathbf{M}+\mathbf{m m}^{T}\right) \mathbf{A}^{T} \\
E\left[(\mathbf{x}+\mathbf{a})(\mathbf{x}+\mathbf{a})^{T}\right] & =\mathbf{M}+(\mathbf{m}+\mathbf{a})(\mathbf{m}+\mathbf{a})^{T} \\
E\left[(\mathbf{A} \mathbf{x}+\mathbf{a})^{T}(\mathbf{B} \mathbf{x}+\mathbf{b})\right] & =\operatorname{Tr}\left(\mathbf{A} \mathbf{M} \mathbf{B}^{T}\right)+(\mathbf{A} \mathbf{m}+\mathbf{a})^{T}(\mathbf{B} \mathbf{m}+\mathbf{b}) \\
E\left[\mathbf{x}^{T} \mathbf{x}\right] & =\operatorname{Tr}(\mathbf{M})+\mathbf{m}^{T} \mathbf{m} \\
E\left[\mathbf{x}^{T} \mathbf{A} \mathbf{x}\right] & =\operatorname{Tr}(\mathbf{A} \mathbf{M})+\mathbf{m}^{T} \mathbf{A} \mathbf{m} \\
E\left[(\mathbf{A} \mathbf{x})^{T}(\mathbf{A} \mathbf{x})\right] & =\operatorname{Tr}\left(\mathbf{A} \mathbf{M} \mathbf{A}^{T}\right)+(\mathbf{A} \mathbf{m})^{T}(\mathbf{A} \mathbf{m}) \\
E\left[(\mathbf{x}+\mathbf{a})^{T}(\mathbf{x}+\mathbf{a})\right] & =\operatorname{Tr}(\mathbf{M})+(\mathbf{m}+\mathbf{a})^{T}(\mathbf{m}+\mathbf{a})
\end{aligned}
$$

See 7. 

\subsubsection{Cubic Forms}

Assume $\mathbf{x}$ to be a stochastic vector with independent coordinates, mean $\mathbf{m}$, covariance $\mathbf{M}$ and central moments $\mathbf{v}_{3}=E\left[(\mathbf{x}-\mathbf{m})^{3}\right]$. Then $($ see $[7])$

$$
\begin{aligned}
& E\left[(\mathbf{A} \mathbf{x}+\mathbf{a})(\mathbf{B} \mathbf{x}+\mathbf{b})^{T}(\mathbf{C x}+\mathbf{c})\right]=\mathbf{A d i a g}\left(\mathbf{B}^{T} \mathbf{C}\right) \mathbf{v}_{3} \\
& +\operatorname{Tr}\left(\mathbf{B M C} \mathbf{C}^{T}\right)(\mathbf{A m}+\mathbf{a}) \\
& +\mathbf{A M C}^{T}(\mathbf{B m}+\mathbf{b}) \\
& +\left(\mathbf{A M B}^{T}+(\mathbf{A m}+\mathbf{a})(\mathbf{B m}+\mathbf{b})^{T}\right)(\mathbf{C m}+\mathbf{c}) \\
& E\left[\mathbf{x x}^{T} \mathbf{x}\right]=\mathbf{v}_{3}+2 \mathbf{M} \mathbf{m}+\left(\operatorname{Tr}(\mathbf{M})+\mathbf{m}^{T} \mathbf{m}\right) \mathbf{m} \\
& E\left[(\mathbf{A} \mathbf{x}+\mathbf{a})(\mathbf{A} \mathbf{x}+\mathbf{a})^{T}(\mathbf{A} \mathbf{x}+\mathbf{a})\right]=\mathbf{A} \operatorname{diag}\left(\mathbf{A}^{T} \mathbf{A}\right) \mathbf{v}_{3} \\
& +\left[2 \mathbf{A M A} \mathbf{A}^{T}+(\mathbf{A x}+\mathbf{a})(\mathbf{A} \mathbf{x}+\mathbf{a})^{T}\right](\mathbf{A} \mathbf{m}+\mathbf{a}) \\
& +\operatorname{Tr}\left(\mathbf{A M A} \mathbf{A}^{T}\right)(\mathbf{A m}+\mathbf{a}) \\
& E\left[(\mathbf{A x}+\mathbf{a}) \mathbf{b}^{T}(\mathbf{C x}+\mathbf{c})(\mathbf{D x}+\mathbf{d})^{T}\right]=(\mathbf{A x}+\mathbf{a}) \mathbf{b}^{T}\left(\mathbf{C M D}^{T}+(\mathbf{C m}+\mathbf{c})(\mathbf{D m}+\mathbf{d})^{T}\right) \\
& +\left(\mathbf{A M C} \mathbf{C}^{T}+(\mathbf{A m}+\mathbf{a})(\mathbf{C m}+\mathbf{c})^{T}\right) \mathbf{b}(\mathbf{D m}+\mathbf{d})^{T} \\
& +\mathbf{b}^{T}(\mathbf{C m}+\mathbf{c})\left(\mathbf{A M D}{ }^{T}-(\mathbf{A m}+\mathbf{a})(\mathbf{D m}+\mathbf{d})^{T}\right)
\end{aligned}
$$

\subsection{Weighted Scalar Variable}

Assume $\mathbf{x} \in \mathbb{R}^{n \times 1}$ is a random variable, $\mathbf{w} \in \mathbb{R}^{n \times 1}$ is a vector of constants and $y$ is the linear combination $y=\mathbf{w}^{T} \mathbf{x}$. Assume further that $\mathbf{m}, \mathbf{M}_{2}, \mathbf{M}_{3}, \mathbf{M}_{4}$ denotes the mean, covariance, and central third and fourth moment matrix of the variable $\mathbf{x}$. Then it holds that

$$
\begin{aligned}
\langle y\rangle & =\mathbf{w}^{T} \mathbf{m} \\
\left\langle(y-\langle y\rangle)^{2}\right\rangle & =\mathbf{w}^{T} \mathbf{M}_{2} \mathbf{w} \\
\left\langle(y-\langle y\rangle)^{3}\right\rangle & =\mathbf{w}^{T} \mathbf{M}_{3} \mathbf{w} \otimes \mathbf{w} \\
\left\langle(y-\langle y\rangle)^{4}\right\rangle & =\mathbf{w}^{T} \mathbf{M}_{4} \mathbf{w} \otimes \mathbf{w} \otimes \mathbf{w}
\end{aligned}
$$



\section{Multivariate Distributions}

\subsection{Cauchy}

The density function for a Cauchy distributed vector $\mathbf{t} \in \mathbb{R}^{P \times 1}$, is given by

$$
p(\mathbf{t} \mid \boldsymbol{\mu}, \boldsymbol{\Sigma})=\pi^{-P / 2} \frac{\Gamma\left(\frac{1+P}{2}\right)}{\Gamma(1 / 2)} \frac{\operatorname{det}(\boldsymbol{\Sigma})^{-1 / 2}}{\left[1+(\mathbf{t}-\boldsymbol{\mu})^{\top} \boldsymbol{\Sigma}^{-1}(\mathbf{t}-\boldsymbol{\mu})\right]^{(1+P) / 2}}
$$

where $\boldsymbol{\mu}$ is the location, $\boldsymbol{\Sigma}$ is positive definite, and $\Gamma$ denotes the gamma function. The Cauchy distribution is a special case of the Student-t distribution.

\subsection{Dirichlet}

The Dirichlet distribution is a kind of "inverse" distribution compared to the multinomial distribution on the bounded continuous variate $\mathbf{x}=\left[x_{1}, \ldots, x_{P}\right]$ [16, p. 44]

$$
p(\mathbf{x} \mid \boldsymbol{\alpha})=\frac{\Gamma\left(\sum_{p}^{P} \alpha_{p}\right)}{\prod_{p}^{P} \Gamma\left(\alpha_{p}\right)} \prod_{p}^{P} x_{p}^{\alpha_{p}-1}
$$

\subsection{Normal}

The normal distribution is also known as a Gaussian distribution. See sec. 8

\subsection{Normal-Inverse Gamma}

\subsection{Gaussian}

See sec. 8

\subsection{Multinomial}

If the vector $\mathbf{n}$ contains counts, i.e. $(\mathbf{n})_{i} \in 0,1,2, \ldots$, then the discrete multinomial disitrbution for $\mathbf{n}$ is given by

$$
P(\mathbf{n} \mid \mathbf{a}, n)=\frac{n !}{n_{1} ! \ldots n_{d} !} \prod_{i}^{d} a_{i}^{n_{i}}, \quad \sum_{i}^{d} n_{i}=n
$$

where $a_{i}$ are probabilities, i.e. $0 \leq a_{i} \leq 1$ and $\sum_{i} a_{i}=1$.

\subsection{Student's t}

The density of a Student-t distributed vector $\mathbf{t} \in \mathbb{R}^{P \times 1}$, is given by

$$
p(\mathbf{t} \mid \boldsymbol{\mu}, \boldsymbol{\Sigma}, \nu)=(\pi \nu)^{-P / 2} \frac{\Gamma\left(\frac{\nu+P}{2}\right)}{\Gamma(\nu / 2)} \frac{\operatorname{det}(\boldsymbol{\Sigma})^{-1 / 2}}{\left[1+\nu^{-1}(\mathbf{t}-\boldsymbol{\mu})^{\top} \boldsymbol{\Sigma}^{-1}(\mathbf{t}-\boldsymbol{\mu})\right]^{(\nu+P) / 2}}
$$

where $\boldsymbol{\mu}$ is the location, the scale matrix $\boldsymbol{\Sigma}$ is symmetric, positive definite, $\nu$ is the degrees of freedom, and $\Gamma$ denotes the gamma function. For $\nu=1$, the Student-t distribution becomes the Cauchy distribution (see sec 7.1). 

\subsubsection{Mean}

$$
\mathrm{E}(\mathbf{t})=\boldsymbol{\mu}, \quad \nu>1
$$

\subsubsection{Variance}

$$
\operatorname{cov}(\mathbf{t})=\frac{\nu}{\nu-2} \boldsymbol{\Sigma}, \quad \nu>2
$$

\subsubsection{Mode}

The notion mode meaning the position of the most probable value

$$
\operatorname{mode}(\mathbf{t})=\boldsymbol{\mu}
$$

\subsubsection{Full Matrix Version}

If instead of a vector $\mathbf{t} \in \mathbb{R}^{P \times 1}$ one has a matrix $\mathbf{T} \in \mathbb{R}^{P \times N}$, then the Student-t distribution for $\mathbf{T}$ is

$$
\begin{aligned}
& p(\mathbf{T} \mid \mathbf{M}, \boldsymbol{\Omega}, \boldsymbol{\Sigma}, \nu)= \pi^{-N P / 2} \prod_{p=1}^{P} \frac{\Gamma[(\nu+P-p+1) / 2]}{\Gamma[(\nu-p+1) / 2]} \times \\
& \nu \operatorname{det}(\boldsymbol{\Omega})^{-\nu / 2} \operatorname{det}(\boldsymbol{\Sigma})^{-N / 2} \times \\
& \operatorname{det}\left[\boldsymbol{\Omega}^{-1}+(\mathbf{T}-\mathbf{M}) \boldsymbol{\Sigma}^{-1}(\mathbf{T}-\mathbf{M})^{\boldsymbol{\top}}\right]^{-(\nu+P) / 2}(341)
\end{aligned}
$$

where $\mathbf{M}$ is the location, $\boldsymbol{\Omega}$ is the rescaling matrix, $\boldsymbol{\Sigma}$ is positive definite, $\nu$ is the degrees of freedom, and $\Gamma$ denotes the gamma function.

\section{$7.8 \quad$ Wishart}

The central Wishart distribution for $\mathbf{M} \in \mathbb{R}^{P \times P}, \mathbf{M}$ is positive definite, where $m$ can be regarded as a degree of freedom parameter [16, equation 3.8.1] [8, section 2.5$],[11$

$$
\begin{aligned}
& p(\mathbf{M} \mid \boldsymbol{\Sigma}, m)= \frac{1}{2^{m P / 2} \pi^{P(P-1) / 4} \prod_{p}^{P} \Gamma\left[\frac{1}{2}(m+1-p)\right]} \times \\
& \operatorname{det}(\boldsymbol{\Sigma})^{-m / 2} \operatorname{det}(\mathbf{M})^{(m-P-1) / 2} \times \\
& \exp \left[-\frac{1}{2} \operatorname{Tr}\left(\boldsymbol{\Sigma}^{-1} \mathbf{M}\right)\right]
\end{aligned}
$$

\subsubsection{Mean}

$$
E(\mathbf{M})=\mathbf{m} \boldsymbol{\Sigma}
$$



\subsection{Wishart, Inverse}

The (normal) Inverse Wishart distribution for $\mathbf{M} \in \mathbb{R}^{P \times P}, \mathbf{M}$ is positive definite, where $m$ can be regarded as a degree of freedom parameter [11]

$$
\begin{gathered}
p(\mathbf{M} \mid \boldsymbol{\Sigma}, m)=\frac{1}{2^{m P / 2} \pi^{P(P-1) / 4} \prod_{p}^{P} \Gamma\left[\frac{1}{2}(m+1-p)\right]} \times \\
\operatorname{det}(\boldsymbol{\Sigma})^{m / 2} \operatorname{det}(\mathbf{M})^{-(m-P-1) / 2} \times \\
\exp \left[-\frac{1}{2} \operatorname{Tr}\left(\boldsymbol{\Sigma} \mathbf{M}^{-1}\right)\right]
\end{gathered}
$$

\subsubsection{Mean}

$$
E(\mathbf{M})=\boldsymbol{\Sigma} \frac{1}{m-P-1}
$$

