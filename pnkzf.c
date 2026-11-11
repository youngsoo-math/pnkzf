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
 * Usage:  ./pnkzf k n [checkpoint_file]
 *
 * With a checkpoint file, the search position is saved there every few
 * minutes and a restarted run resumes from it (see "checkpointing" below).
 */

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#include <io.h>      // _commit
#include <windows.h> // MoveFileExA
#else
#include <unistd.h> // fsync
#endif

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
static int best_s = -1; // smallest s confirmed to work so far

static int resuming = 0;    // 1 while fast-forwarding to a checkpointed candidate
static int resume_at[MAXV]; // that candidate: the next one to test
static time_t search_start_time; // when this run started searching size s
static long search_secs_before;  // seconds spent on size s before a restart

/* n choose r = n! / (r! (n-r)!), via the Gamma function: Gamma(m+1) = m!
   approximate calculations for progress report */
static long double n_choose_r(int nn, int rr) {
  if (rr < 0 || rr > nn)
    return 0.0L;
  return tgammal(nn + 1) / (tgammal(rr + 1) * tgammal(nn - rr + 1));
}

/* Rotation-reduced candidate count for sets of the given size: If S contains
 an outer vertex, fix it to u0 and choose size-1 vertices from remaining 2n-1 =
 N-1 vertices. Or if S contains inner vertices only, fix one to v0 and choose
 size-1 vertices from remaining n-1 inner vertices. */
static long double count_candidates(int size) {
  return n_choose_r(N - 1, size - 1) + n_choose_r(n - 1, size - 1);
}

static long double total_candidates; /* for the progress percentage */
static time_t last_progress_print = 0;

static void print_progress_line(long long count, long double total) {
  double pct =
      total > 0 ? (double)((long double)count / total * 100.0L) : 0.0;
  printf("\r  %lld (%.1f%%)...", count, pct); // overwrite the line.
  fflush(stdout); // make sure the line is printed.
}

/* Print a progress line, but no more than once a second.*/
static void maybe_print_progress(void) {
  time_t now = time(NULL);
  if (now - last_progress_print < 1)
    return; /* already printed within the last second */
  last_progress_print = now;
  print_progress_line(nsets_generated, total_candidates);
}

/* Print the final progress line and the verdict for one candidate size. */
static void print_s_result(int size, int works, long long count, long secs) {
  print_progress_line(count, count_candidates(size));
  printf("\n");
  printf("s = %d %s (%lld candidates, %lds).\n", size, works ? "WORKS" : "fails",
         count, secs);
}

static void maybe_save_checkpoint(void); // see "checkpointing" below

/* Test the candidate set currently sitting in chosen[0..s-1]. */
static void try_current_candidate(void) {
  nsets_generated++;                  // increase count for statistics.
  if (!(nsets_generated & 0xFFFFF)) { // every ~1M candidates:
    maybe_print_progress();           //   progress line, at most once a second
    maybe_save_checkpoint();          //   checkpoint, every few minutes
  }

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
 * set.
 * When resuming from a checkpoint, each level starts at resume_at[depth]
 * instead, which skips straight to the checkpointed candidate; from there on
 * the enumeration continues normally. */
static void enumerate(int start, int depth) {
  if (found)
    return;
  if (depth == s) {
    resuming = 0;            // reached the checkpointed candidate (if any)
    try_current_candidate(); // candidate zero forcing set built. Test it.
    return;
  }
  for (int x = resuming ? resume_at[depth] : start; x < N && !found; x++) {
    chosen[depth] = x;
    enumerate(x + 1, depth + 1);
  }
}

/* Run the full two-branch, rotation-reduced search over chosen[]. */
static void run_search(void) {
  /* Rotation-reduced search count, see count_candidates(). Reflection reduces
   the actual simulation count by a factor of almost 2 */
  total_candidates = count_candidates(s);

  if (!(resuming && resume_at[0] == n)) { // checkpoint not already past it
    chosen[0] = 0;                        // case: some outer vertex is u_0
    enumerate(chosen[0] + 1, 0 + 1); // build vertex set recursively and check
  }
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

/* ---- checkpointing ------------------------------------------------------ */

/* A run for large n can take weeks. Given a checkpoint file, the program saves
 * its state there every CHECKPOINT_SECONDS and after each finished size s. If
 * the file exists at start-up, the run resumes from it: it re-prints the sizes
 * s already finished and continues the interrupted search from the saved
 * candidate, so a restart loses at most CHECKPOINT_SECONDS of work.
 * The file is plain text, for example:
 *
 *   pnkzf-checkpoint 1
 *   k 5
 *   n 55
 *   finished 1                         number of sizes s already decided,
 *   s 12 1 1 0                         each: s, works (1/0), candidates, seconds
 *   zfset 0 1 2 3 4 5 6 7 8 9 10 11    forcing set of the smallest working s
 *   current 11 2147483648 3600         size being searched, candidates done,
 *   chosen 0 1 2 3 4 5 6 7 9 40 77     seconds so far; next candidate to test
 *   end
 *
 * zfset is present once some s has worked, current/chosen while a search is
 * in progress. */

#ifndef CHECKPOINT_SECONDS
#define CHECKPOINT_SECONDS 300
#endif

static const char *checkpoint_path = NULL; // NULL: no checkpointing
static time_t last_checkpoint_save = 0;

/* The sizes s decided so far, in search order (s = 2k+2, 2k+1, ...). */
static int nfinished = 0;
static int finished_s[MAXV], finished_works[MAXV];
static long long finished_count[MAXV];
static long finished_secs[MAXV];

static long long resume_count; // candidates done in the resumed search
static long resume_secs;       // seconds spent on the resumed search

/* Write the checkpoint to a temporary file, flush it to disk, then swap it in
 * for the old one, so a crash or power cut during a save never leaves a
 * damaged checkpoint behind. in_search: also record the position in the
 * current search. */
static void save_checkpoint(int in_search) {
  char tmp[4096];
  snprintf(tmp, sizeof tmp, "%s.tmp", checkpoint_path);
  last_checkpoint_save = time(NULL);

  FILE *f = fopen(tmp, "w");
  if (!f) {
    fprintf(stderr, "warning: cannot write checkpoint %s\n", tmp);
    return;
  }
  fprintf(f, "pnkzf-checkpoint 1\nk %d\nn %d\nfinished %d\n", k, n, nfinished);
  for (int i = 0; i < nfinished; i++)
    fprintf(f, "s %d %d %lld %ld\n", finished_s[i], finished_works[i],
            finished_count[i], finished_secs[i]);
  if (best_s > 0) {
    fprintf(f, "zfset");
    for (int i = 0; i < best_s; i++)
      fprintf(f, " %d", zfset[i]);
    fprintf(f, "\n");
  }
  if (in_search) {
    /* Called right before chosen[] is tested, after nsets_generated already
     * counted it, so the candidates done are one fewer. */
    long secs = search_secs_before + (long)(time(NULL) - search_start_time);
    fprintf(f, "current %d %lld %ld\nchosen", s, nsets_generated - 1, secs);
    for (int i = 0; i < s; i++)
      fprintf(f, " %d", chosen[i]);
    fprintf(f, "\n");
  }
  fprintf(f, "end\n");

  int ok = fflush(f) == 0 && !ferror(f);
#ifdef _WIN32
  ok = ok && _commit(_fileno(f)) == 0;
  ok = (fclose(f) == 0) && ok;
  ok = ok && MoveFileExA(tmp, checkpoint_path,
                         MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH);
#else
  ok = ok && fsync(fileno(f)) == 0;
  ok = (fclose(f) == 0) && ok;
  ok = ok && rename(tmp, checkpoint_path) == 0;
#endif
  if (!ok)
    fprintf(stderr, "warning: saving checkpoint %s failed\n", checkpoint_path);
}

static void maybe_save_checkpoint(void) {
  if (checkpoint_path &&
      time(NULL) - last_checkpoint_save >= CHECKPOINT_SECONDS)
    save_checkpoint(1);
}

/* Is v[0..len-1] a valid candidate: strictly increasing vertex indices, with
 * v[0] = u_0, or v[0] = v_0 and only inner vertices (the two search cases)? */
static int valid_candidate(const int *v, int len) {
  if (len < 1 || (v[0] != 0 && v[0] != n))
    return 0;
  for (int i = 1; i < len; i++)
    if (v[i] <= v[i - 1] || v[i] >= N)
      return 0;
  return 1;
}

/* Restore the state written by save_checkpoint(). Returns 0 if there is no
 * checkpoint file yet, 1 if one was loaded. A damaged checkpoint, or one from
 * a different P(n,k), stops the program instead of silently starting over. */
static int load_checkpoint(void) {
  FILE *f = fopen(checkpoint_path, "r");
  if (!f)
    return 0;

  int max_s = 2 * k + 2;
  int version, ck, cn, has_zfset = 0;
  char word[16] = "";
  int ok = fscanf(f, " pnkzf-checkpoint %d k %d n %d finished %d", &version,
                  &ck, &cn, &nfinished) == 4 &&
           version == 1 && ck == k && cn == n && nfinished >= 0 &&
           nfinished <= max_s - 2;

  /* Finished sizes must be 2k+2, 2k+1, ... in order, and all but the last
   * must have worked (the search stops at the first size that fails). */
  for (int i = 0; ok && i < nfinished; i++) {
    ok = fscanf(f, " s %d %d %lld %ld", &finished_s[i], &finished_works[i],
                &finished_count[i], &finished_secs[i]) == 4 &&
         finished_s[i] == max_s - i &&
         (finished_works[i] == 1 || (finished_works[i] == 0 && i == nfinished - 1));
    if (ok && finished_works[i])
      best_s = finished_s[i];
  }

  ok = ok && fscanf(f, " %15s", word) == 1;
  if (ok && strcmp(word, "zfset") == 0) {
    has_zfset = 1;
    for (int i = 0; ok && i < best_s; i++)
      ok = fscanf(f, "%d", &zfset[i]) == 1 && zfset[i] >= 0 && zfset[i] < N;
    ok = ok && fscanf(f, " %15s", word) == 1;
  }
  ok = ok && has_zfset == (best_s > 0);

  if (ok && strcmp(word, "current") == 0) {
    int cur_s;
    ok = fscanf(f, "%d %lld %ld chosen", &cur_s, &resume_count, &resume_secs) ==
             3 &&
         cur_s == max_s - nfinished && cur_s >= 3 && resume_count >= 0 &&
         (nfinished == 0 || finished_works[nfinished - 1]);
    for (int i = 0; ok && i < cur_s; i++)
      ok = fscanf(f, "%d", &resume_at[i]) == 1;
    ok = ok && valid_candidate(resume_at, cur_s) &&
         fscanf(f, " %15s", word) == 1;
    resuming = ok;
  }
  ok = ok && strcmp(word, "end") == 0;
  fclose(f);

  if (!ok) {
    printf("checkpoint file %s is damaged or belongs to another P(n,k); "
           "move it away to start this run over\n",
           checkpoint_path);
    exit(1);
  }
  return 1;
}

/* ---- main function ------------------------------------------- */

int main(int argc, char **argv) {
  if (argc != 3 && argc != 4) {
    printf("usage: %s k n [checkpoint_file]\n", argv[0]);
    printf("  computes the zero forcing number Z(P(n,k))\n");
    printf("  with checkpoint_file, saves progress there and resumes from it\n");
    return 1;
  }
  k = atoi(argv[1]);
  n = atoi(argv[2]);
  if (argc == 4)
    checkpoint_path = argv[3];

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
  long earlier_secs = 0; /* time spent before a restart */
  if (checkpoint_path && load_checkpoint()) {
    earlier_secs = resuming ? resume_secs : 0;
    for (int i = 0; i < nfinished; i++)
      earlier_secs += finished_secs[i];
    printf("(resumed from checkpoint after %lds of earlier work)\n",
           earlier_secs);
    for (int i = 0; i < nfinished; i++) // what the earlier run(s) found
      print_s_result(finished_s[i], finished_works[i], finished_count[i],
                     finished_secs[i]);
  }

  /* Done already if the checkpoint's last size failed. */
  int done = nfinished > 0 && !finished_works[nfinished - 1];
  time_t total_start = time(NULL);
  for (s = max_s - nfinished; !done && s >= 3; s--) {
    reset_search_state();
    search_secs_before = 0;
    if (resuming) { // continue the search the checkpoint was saved in
      nsets_generated = resume_count;
      search_secs_before = resume_secs;
    }

    search_start_time = time(NULL);
    run_search();
    long elapsed = search_secs_before + (long)(time(NULL) - search_start_time);

    print_s_result(s, found, nsets_generated, elapsed);

    finished_s[nfinished] = s;
    finished_works[nfinished] = found;
    finished_count[nfinished] = nsets_generated;
    finished_secs[nfinished] = elapsed;
    nfinished++;
    if (found)
      best_s = s; // update the best s found so far
    if (checkpoint_path)
      save_checkpoint(0);

    if (!found)
      break; // forcing set not found. no more testing needed.
  }
  long total_elapsed = earlier_secs + (long)(time(NULL) - total_start);

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
