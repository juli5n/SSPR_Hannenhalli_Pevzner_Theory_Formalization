# Project submission LeanCourse25
This Project is submitted by Leo Bergmann and Julian Kemp

# Building Documentation
You can build the documentation with:
```
lake build SSPRHannenhalliPevznerTheory:docs
```
If you are on unix, you can also probably use the Makefile:
```
make docs                       # Build documentation
make open_doc                   # Open documentation
make build_and_open_doc         # Build & open documentation
```

# Project Topic
This project formalizes foundational concepts regarding the sorting of signed permutations by reversals (SSPR), a core problem in bioinformatics for analyzing genome rearrangements (Hannenhalli-Pevzner theory).


We have focused on formalizing parts of the paper "Transforming cabbage into turnip“ by Hannenhalli and Pevzner (Journal of the ACM, Vol. 46, No. 1, January 1999, pp. 1–27)".
We have chosen this paper, since this theory by Hannenhalli and Pevzner laid the fundament for the SSPR field.
The paper is freely available [here](https://dl.acm.org/doi/10.1145/300515.300516). 

A signed permutation is just like a regular permutation, but each element 
is associated with a sign (+ or -). For example a signed permutation 
could be something like $(+1, -2, +4, +3)$.

A reversal $\rho(i,j)$ with $1 \leq i \leq j \leq n$ for a permutation of size n is the permutation 
$$
\begin{pmatrix}
1 & \dots & i-1 & i & i+1 & \dots & j-1 & j & j+1 & \dots & n \\
1 & \dots & i-1 & j & j-1 & \dots & i+1 & i & j+1 & \dots & n \\
\end{pmatrix}
$$
Composing a reversal $\rho(i,j)$ with an (unsigned) permutation π has the effect of 
reversing the order of the elements
$π_i, ...,π_j$. The notion of a reversal is extended to signed permutations through the following:
A reversal applied to a signed permutation applies the reversal to the underlying unsigned permutation
and flipping all of the signs of the affected segment.

For example the reversal $\rho(2,4)$ applied to the signed 
permutation $(+1, -2, +4, +3)$
yields the signed permutation $(+1, -3, -4, +3)$. 

The reversal distance $d(π)$ of a (signed) permutation π is the minimum
number of reversals needed to "sort it" (i.e. turn it into
the identity permutation). 

For studying the problem of sorting a (signed) permutation it has
proven useful to associate multiple graphs with a (signed) permutation:
the so called breakpoint graph, the interleaving graph and the overlap graph.

The major result of the paper "Transforming cabbage into turnip" is the following duality theorem, which states that the reversal
distance of a permutation can be accurately described
by some properties of the graphs mentioned above:

$$
d(\pi) = \begin{cases} 
b(\pi) - c(\pi) + h(\pi) + 1, & \text{if } \pi \text{ is a fortress} \\
b(\pi) - c(\pi) + h(\pi), & \text{otherwise.}
\end{cases}
$$

where $b(\pi)$ is the number of "black" edges in the breakpoint graph, $c(\pi)$ is the size
of a maximum cycle decomposition of the breakpoint graph and $h(\pi)$ is the number of hurdles, which
are specific components in the interleaving graph.

# Progress
What we have formalized so far includes:

* Signed Permutations
* Reversals
* Signed Permutations are sortable (i.e. there always exists a sequence or reversals that transforms them to the identity permutation)
* Formalized the mapping from a signed permutation of size n to an unsigned permutation of size 2n (i.e. their unsigned representation)
* Defined what property an unsigned permutation needs to have to be
considered an image of the above injective transformation, i.e.
the unsigned permutation $\pi$ has to have even size $2n$ and for every $i \in \{1,\dots,n\}$ the elements ${\pi}_i$ and ${\pi}_{i+1}$ must be consecutive
* Defined the reversal distance of a signed permutation
* Defined the function `toggleLSB` which flips the LSB of a natural number
* Proved that if for every $i \in \{1,\dots,n\}$ ${\pi}_i$ and ${\pi}_{i+1}$
are consecutive, then it also holds for all $i \in \{1,\dots,n\}$, that
the minimum of ${\pi}_i$ and ${\pi}_{i+1}$ is even (proving this required suprising effort)
* Proved the theorem UnsignedRepresentationOfSP.map_toggleLSB, which states that 
for an unsigned representation $\pi$ of a signed permutation it holds that 
$\pi(toggleLSB(i)) = toggleLSB\pi(i)$
* Defined the inverse function for the mapping between signed permutations and
their unsigned representations (incomplete)
* Defined scalar multiplication of reversals with unsigned permutations, signed permutations and unsigned representations of signed permutations
* Defined the breakpoint graph of a signed permutation
* Defined the cycle graph of a permutation
* Defined cycle decompositions of a graph and the size of a maximal one
* Proved that the size of a maximum cycle decomposition is bounded by the edge degree of a graph divided by 3 (each cycle has at least 3 edges)
* Defined the interleaving graph of a permutation
* Proved that the degree of a node in the breakpoint graph of a permutation 
is at most 2
* Created notation for $b(\pi)$ and $c(\pi)$
* Started proving that the black edge degree equals the gray edge degree of a node
in the breakpoint graph of a permutation (this is incomplete and uses sorry)

# Recommended Literature

* **Transforming cabbage into turnip** by Sridhar Hannenhalli and Pavel A. Pevzner. [Link](https://doi.org/10.1145/300515.300516)
* **A very elementary presentation of the Hannenhalli–Pevzner theory** by Anne Bergeron. [Link](https://doi.org/10.1016/j.dam.2004.04.010) <- This paper is particularly easy to understand and gives an introduction to the Hannenhalli-Pevzner theory
* **Sorting Signed Permutations by Reversals in Nearly-Linear Time** by Bartłomiej Dudek, Paweł Gawrychowski, Tatiana Starikovskaya. [Link](https://doi.org/10.48550/arXiv.2308.15928)
* **A Faster and Simpler Algorithm for Sorting Signed Permutations by Reversals** by Haim Kaplan, Ron Shamir, and Robert E. Tarjan. [Link](https://doi.org/10.1137/S0097539798334207)


# Remark: AI usage
We have used Prompt-Based AI (via prompts) for naming suggestions, questions about lean functionality and help with lean proofs (usually by prompting the AI with the current lean goal state and asking for how one could possibly continue)