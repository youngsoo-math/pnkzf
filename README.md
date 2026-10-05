# pnkzf

A fast C program to compute the exact **zero forcing number** $Z(P(n,k))$ of the generalized Petersen graph $P(n,k)$.

## Background

- **Generalized Petersen Graph $P(n,k)$**: A 3-regular graph on $2n$ vertices ($n > 2k, k \ge 2$) consisting of an outer $n$-cycle ($u_i$), an inner skip-$k$ cycle ($v_i$), and spokes connecting $u_i \sim v_i$.
- **Zero Forcing**: Given an initial set of black vertices, a black vertex with exactly one white neighbor forces that neighbor to turn black. A *forcing set* eventually colors all $2n$ vertices black; $Z(G)$ is the minimum size of a forcing set.

## Build

```bash
clang -O3 -march=native -o pnkzf pnkzf.c -lm
```

## Usage

```bash
./pnkzf <k> <n>
```

> **Note**: Parameters are ordered `k` then `n`, requiring $k \ge 2$, $n > 2k$, and $2n < 128$.

### Example: Petersen Graph $P(5,2)$

```text
$ ./pnkzf 2 5
P(5,2): 10 vertices (3-regular). Computing Z(P(5,2))...
s = 6 WORKS (1 candidates, 0s).
s = 5 WORKS (1 candidates, 0s).
s = 4 fails (88 candidates, 0s).

Z(P(5,2)) = 5
zero forcing set: { u0 u1 u2 u3 u4 }
(total time: 0s)
```

Outer vertices are labeled `u0`..`u{n-1}`, and inner vertices `v0`..`v{n-1}`.

## How It Works

- **Top-Down Search**: Tests candidate sizes downwards from the known upper bound $s = 2k + 2$. The first size that fails proves the previous size was optimal ($Z(P(n,k)) = s + 1$).
- **Symmetry Pruning**:
  - *Rotation*: Fixes $u_0 \in S$ if $S$ contains an outer vertex, or $v_0 \in S$ if $S$ is purely inner vertices.
  - *Reflection*: Skips candidate sets whose reflection across the $u_0/v_0$ axis is lexicographically smaller.
- **Event-Driven Simulation**: Uses a stack of active vertices to simulate color propagation locally rather than rescanning all vertices.

## Configuration

- `MAXV` in `pnkzf.c` defines the maximum vertex count (default `128`, supporting $n \le 63$).
