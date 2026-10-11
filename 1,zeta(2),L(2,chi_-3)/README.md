# 1,zeta(2),L(2,chi_-3)

A Lean 4 formalization of the linear independence of $1$, $\zeta(2)$, and $L(2,\chi_{-3})$ over $\mathbb{Q}$. In particular, $L(2,\chi_{-3})$ is irrational. The formalization follows Calegari, Dimitrov, and Tang, [*The linear independence of 1, zeta(2), and L(2, chi_-3)*](https://arxiv.org/abs/2408.15403v2).

Statement: [Comparator/Statement.lean](Comparator/Statement.lean); proof: [Proof/Main.lean](Proof/Main.lean), `DirichletL.mainTheorem`. Build (Lean 4.24.0): `lake exe cache get && lake build`.
Comparator: with [landrun `5ed4a3d`](https://github.com/Zouuup/landrun/tree/5ed4a3db3a4ad930d577215c6b9abaa19df7f99f) on `PATH`, run `bash Comparator/check.sh` (builds and runs the [official comparator](https://github.com/leanprover/comparator), with matching Lean versions).
