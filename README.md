# Entropy and singularity of spectral and pivotal sets in planar percolation

Yitzchak Shmalo, Einstein Institute of Mathematics, The Hebrew University of Jerusalem

The spectral sample and the pivotal set of a percolation crossing have the same one- and two-point inclusion probabilities under the uniform product measure. For crossings of rectangles in critical bond percolation on the square lattice, and in site percolation on the triangular lattice with critical or inhomogeneous near-critical parameters, the Shannon entropies of both sets are comparable to the total influence, which is of order R²α₄(R). This answers Question 1 in Section 11 of C. Garban, G. Pete and O. Schramm, *The Fourier spectrum of critical percolation* (Acta Math. 205 (2010), 19–104), and proves both bounds of Conjecture 8 in G. Kalai, *Three puzzles on mathematics, computation, and games* (Proc. ICM 2018) for these crossings. The spectral bound is the percolation case of the Fourier entropy–influence conjecture of Friedgut and Kalai. The proof encodes a random set by the dyadic cells it occupies and bounds the expected number of occupied cells at each scale by arm estimates.

For square crossings in critical site percolation on the triangular lattice, the laws of the spectral sample and the pivotal set are asymptotically mutually singular, which answers the discrete case of Question 5 in Section 11 of the same paper. A pivotal set never contains an elementary triangular face, while a large spectral sample contains such faces with positive density. The positive density comes from an exact coercivity inequality on the six-cycle that survives conditioning on the exterior. The paper also determines the cost of low face density, the order of the minimal expected symmetric difference over couplings, and the thinning scale at which the face detector fails. The nonempty overlap of the two laws lies between R^(−11/12+o(1)) and R^(−1/2+o(1)), and equals R^(−11/12+o(1)) if the Garban–Pete–Schramm bound on small spectral samples holds for pivotal sets as well.

## Files

- `paper/main.pdf`: the paper
- `paper/main.tex`: LaTeX source
- `lean/SixCycle.lean`: a Lean 4 and Mathlib proof of Lemma 7.2 and Proposition 7.3, the six-cycle coercivity inequality with its optimal constant (8 − √53)/16. To check it, run `lake exe cache get` and then `lake build` in `lean/` (Lean v4.33.1, Mathlib v4.33.1; the exact Mathlib revision is pinned in `lean/lake-manifest.json`). `lean/SixCycle.out` is the output of `lake env lean SixCycle.lean`: there is no `sorry`, and every theorem depends on `propext`, `Classical.choice` and `Quot.sound` at most.
- `computations/sixcycle.py`: recomputes the matrices and eigenvalues of Section 7.2 and writes an exact LDLᵀ certificate for the odd block to `sixcycle.json` (needs NumPy)

## Citation

Y. Shmalo, *Entropy and singularity of spectral and pivotal sets in planar percolation*, 2026. arXiv:2609.15388. https://github.com/yspennstate/percolation-crossing-entropy
