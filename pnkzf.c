/* pnkzf.c — the zero forcing number of the generalized Petersen graph P(n,k)
 * ============================================================================
 *
 * Background
 * ----------
 * P(n,k) is the generalized Petersen graph on 2n vertices:
 *   - an OUTER n-cycle, u_0, u_1, ..., u_{n-1}
 *   - an INNER "skip-k" n-cycle, v_0, v_1, ..., v_{n-1} (v_i ~ v_{i+k},
 * v_{i-k}, mod n)
 *   - SPOKES joining the two rings u_i ~ v_i
 *
 * Zero forcing on a graph works like this:
 *   1. Paint some set S of vertices black; everything else stays white.
 *   2. Color-change rule: if a black vertex has EXACTLY ONE white
 *      neighbor, that neighbor turns black too ("the black vertex forces
 *      its white neighbor").
 *   3. Repeat step 2 until no more forces are possible.
 * S is called a FORCING SET if this process ends with every vertex black.
 * The zero forcing number Z(G) is the size of the smallest forcing set.
 *
 * What this program does
 * -----------------------
 * It computes Z(P(n,k)) exactly, by brute force:
 *
 *     for s = 2k+2, 2k+1, 2k, ..., 3: does ANY size-s set force P(n,k)?
 *
 * For each s, it tries size-s subsets one at a time, running the
 * forcing simulation on each, and stops as soon as it finds one that works.
 * Using the dihedral symmetry, we assume u_0 is black, or if not, v_0 is black,
 * and check only one of two sets related by reflection.
 *
 * Vertices are numbered u_i = i, v_i = n+i. A set of black vertices is an
 * int array with one 0/1 flag per vertex. Arrays are sized for up to
 * MAXV = 128 vertices, so n is at most 63.
 *
 * Build:  clang -O3 -march=native -o pnkzf pnkzf.c
 * Usage:  ./pnkzf k n
 */

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define MAXV 128 // maximum number of vertices N = 2n

/* ---- the graph -------------------------------------------------------- */

static int k, n;         // P(n,k) parameters
static int N;            // number of vertices = 2n
static int s;            // candidate forcing-set size, 3 <= s <= 2k+2
static int nbr[MAXV][3]; // nbr[v][0..2] = the three neighbors of vertex v
static int refl[MAXV];   // refl[v] = mirror of vertex v across the u_0/v_0 axis

/* Build the neighbor lists for P(n,k).
 * Outer vertex i  is index i; it connects to outer i-1, i+1 and spoke n+i.
 * Inner vertex i  is index n+i; it connects to inner n+(i-k), n+(i+k) and
 * spoke i. (i-1, i+1, i-k, i+k are taken mod n)                      */
static void build_graph(void) {
  N = 2 * n;

  for (int i = 0; i < n; i++) {
    /* outer neighbors of outer vertex u_i: its two neighbors on the outer
     * n-cycle and its spoke partner v_i (index n+i). */
    nbr[i][0] = (i + n - 1) % n;
    nbr[i][1] = (i + 1) % n;
    nbr[i][2] = n + i;

    /* inner neighbors of inner vertex v_i: its two "skip-k" cycle neighbors
     * and its spoke partner u_i (index i). */
    nbr[n + i][0] = n + (i + n - k) % n;
    nbr[n + i][1] = n + (i + k) % n;
    nbr[n + i][2] = i;

    /* Reflection:
     * refl[i] is the index of u_{-i}
     * refl[n+i] is the index of v_{-i}. */
    int mirror = (n - i) % n;
    refl[i] = mirror;
    refl[n + i] = n + mirror;
  }
}

/* ---- the zero forcing simulation --------------------------------------- */

/* We use a stack to keep track of all vertices to be checked instead of
 * checking every vertex at every stage.
 * Initially, all vertices of the input set need to be checked. They are all
 * pushed into the stack. But later, when a white vertex y turns black, only y
 * and its neighbors need to be re-checked. So we push y and its black neighbors
 * onto the stack. Each force pushes at most 4 entries (y and its 3 neighbors),
 * and there are fewer than N forces, so the stack never holds more than 4N
 * entries.
 */

static int black[MAXV]; // black[v] = 1 if vertex v is black
static int recheck_stack[4 * MAXV];

static int is_forcing_set(const int *set, int size) {
  for (int v = 0; v < N; v++) // clear black set = empty
    black[v] = 0;

  int top = 0; // the index of the top of the stack (recheck_stack)

  /* initialize black set from input set and push them into the stack. */
  for (int i = 0; i < size; i++) {
    black[set[i]] = 1;
    recheck_stack[top++] = set[i];
  }
  int nblack = size; // number of black vertices so far, if nblack == N, the
                     // input set is a zero forcing set

  while (top) {
    int x = recheck_stack[--top];

    /* x can force only if exactly 2 of its 3 neighbors are black. */
    int a = nbr[x][0], b = nbr[x][1], c = nbr[x][2];
    if (black[a] + black[b] + black[c] != 2)
      continue;                                // no coloring
    int y = !black[a] ? a : !black[b] ? b : c; // the one white neighbor

    black[y] = 1; // x forces y
    if (++nblack == N)
      return 1; // done early

    recheck_stack[top++] = y;
    for (int j = 0; j < 3; j++) {
      int z = nbr[y][j];
      if (black[z])
        recheck_stack[top++] = z;
    }
  }
  return nblack == N;
}

/* ---- brute-force search over candidate sets, with progress reporting -- */

static int chosen[MAXV]; // the s vertex indices of the current candidate zero
                         // forcing set, in increasing order
static long long nsets_generated = 0; // candidates the enumeration produced
static int found = 0;                 // 1 once a zero forcing set is found
static int zfset[MAXV]; // stores the zero forcing set if found, for printing

/* n choose r = n! / (r! (n-r)!), via the Gamma function: Gamma(m+1) = m!
   approximate calculations for progress report */
static long double n_choose_r(int nn, int rr) {
  if (rr < 0 || rr > nn)
    return 0.0L;
  return tgammal(nn + 1) / (tgammal(rr + 1) * tgammal(nn - rr + 1));
}

static long double total_candidates; /* for the progress percentage */
static time_t last_progress_print = 0;

static void print_progress_line(void) {
  double pct =
      total_candidates > 0
          ? (double)((long double)nsets_generated / total_candidates * 100.0L)
          : 0.0;
  printf("\r  %lld (%.1f%%)...", nsets_generated, pct); // overwrite the line.
  fflush(stdout); // make sure the line is printed.
}

/* Print a progress line, but no more than once a second.*/
static void maybe_print_progress(void) {
  time_t now = time(NULL);
  if (now - last_progress_print < 1)
    return; /* already printed within the last second */
  last_progress_print = now;
  print_progress_line();
}

/* Test the candidate set currently sitting in chosen[0..s-1]. */
static void try_current_candidate(void) {
  nsets_generated++;                // increase count for statistics.
  if (!(nsets_generated & 0xFFFFF)) // print progress every ~1M candidates.
    maybe_print_progress();

  /* The reflection of chosen[], sorted increasingly (insertion sort). */
  int mirrored[MAXV];
  for (int i = 0; i < s; i++) {
    int v = refl[chosen[i]];
    int j = i;
    while (j > 0 && mirrored[j - 1] > v) {
      mirrored[j] = mirrored[j - 1];
      j--;
    }
    mirrored[j] = v;
  }

  /* Test only one of the reflexive pairs of candidate sets: skip chosen[]
   * if its reflection comes first in lexicographic order. */
  for (int i = 0; i < s; i++) {
    if (mirrored[i] < chosen[i])
      return;
    if (mirrored[i] > chosen[i])
      break;
  }

  if (is_forcing_set(chosen, s)) {
    found = 1;
    for (int i = 0; i < s; i++)
      zfset[i] = chosen[i]; // store the zero forcing set.
  }
}

/* Enumerate increasing index sequences chosen[depth..s-1] from [start, N),
 * stopping the moment a forcing set is found.
 * The vertex set chosen[] of size s is built recursively in increasing
 * order chosen[0] < chosen[1] < ...< chosen[s-1]
 * chosen[i] is the index of the i-th black vertex of the candidate zero forcing
 * set. */
static void enumerate(int start, int depth) {
  if (found)
    return;
  if (depth == s) {
    try_current_candidate(); // candidate zero forcing set built. Test it.
    return;
  }
  for (int x = start; x < N && !found; x++) {
    chosen[depth] = x;
    enumerate(x + 1, depth + 1);
  }
}

/* Run the full two-branch, rotation-reduced search over chosen[]. */
static void run_search(void) {
  /* Rotation-reduced search count: If S contains an outer vertex, fix it to u0
   and choose s-1 vertices from remaining 2n-1 = N-1 vertices. Or if S contains
   inner vertices only, fix one to v0 and choose s-1 vertices from remaining n-1
   inner vertices. Reflection reduces the actual simulation count by a factor of
   almost 2 */
  total_candidates = n_choose_r(N - 1, s - 1) + n_choose_r(n - 1, s - 1);

  chosen[0] = 0;                     // case: some outer vertex is u_0
  enumerate(chosen[0] + 1, 0 + 1);   // build vertex set recursively and check
  if (!found) {                      // if no solution found, try the other case
    chosen[0] = n;                   // case: no outer vertex, so v_0 is in
    enumerate(chosen[0] + 1, 0 + 1); // build vertex set recursively and check
  }
}

/* Clear the per-s search counters before trying a new candidate size. */
static void reset_search_state(void) {
  found = 0;
  nsets_generated = 0;
  last_progress_print = 0;
}

/* Print the one-time graph banner. */
static void print_graph_info(void) {
  printf("P(%d,%d): %d vertices (3-regular). Computing Z(P(%d,%d))...\n", n, k,
         N, n, k);
}

/* Print the first `count` vertices of zfset[] as u_i/v_i labels. */
static void print_zf_set(int count) {
  printf("{ ");
  for (int i = 0; i < count; i++) {
    int v = zfset[i];
    if (v < n)
      printf("u%d ", v);
    else
      printf("v%d ", v - n);
  }
  printf("}");
}

/* ---- main function ------------------------------------------- */

int main(int argc, char **argv) {
  if (argc != 3) {
    printf("usage: %s k n\n", argv[0]);
    printf("  computes the zero forcing number Z(P(n,k))\n");
    return 1;
  }
  k = atoi(argv[1]);
  n = atoi(argv[2]);

  if (k < 2) {
    printf("k must be at least 2\n");
    return 1;
  }
  if (n <= 2 * k) {
    printf("need n > 2k for P(n,k) to make sense (got n=%d, k=%d)\n", n, k);
    return 1;
  }
  if (2 * n >= MAXV) {
    printf("n too large: need 2n < %d\n", MAXV);
    return 1;
  }

  build_graph();
  print_graph_info();

  int max_s = 2 * k + 2; /* known upper bound: Z(P(n,k)) never exceeds 2k+2 */
  int best_s = -1;       /* smallest s confirmed to work so far */
  time_t total_start = time(NULL);
  for (s = max_s; s >= 3; s--) {
    reset_search_state();

    time_t search_start_time = time(NULL);
    run_search();
    long elapsed = (long)(time(NULL) - search_start_time);

    print_progress_line();
    printf("\n");
    printf("s = %d %s (%lld candidates, %lds).\n", s, found ? "WORKS" : "fails",
           nsets_generated, elapsed);

    if (!found)
      break;    // forcing set not found. no more testing needed.
    best_s = s; // update the best s found so far
  }
  long total_elapsed = (long)(time(NULL) - total_start);

  /* Z(P(n,k)) <= 2k+2 is a theorem, so s = 2k+2 must work. If it didn't,
   * the simulation or the search has a bug. */
  if (best_s < 0) {
    printf("\nBUG: no forcing set of size %d found, but Z(P(n,k)) <= 2k+2 "
           "always holds\n",
           max_s);
    return 1;
  }

  printf("\nZ(P(%d,%d)) = %d\n", n, k, best_s);
  printf("zero forcing set: ");
  print_zf_set(best_s);
  printf("\n(total time: %lds)\n", total_elapsed);
  return 0;
}
