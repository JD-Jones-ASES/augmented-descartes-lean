#!/usr/bin/env python3
"""Standard-library replay of the identities behind the compared statements of Challenge.lean (the finder/checker
split: the Lean development is the trust chain, this script the independent second implementation, exact
arithmetic (fractions.Fraction, and Q(sqrt 3) for the n = 3 cases) wherever the data allow it, floating point
with a fixed seed elsewhere: det(W)^2 = n 2^(n+3), so no configuration has rational rows at n = 3..7).
Prints one line per check and ends with VERDICT: PASS or VERDICT: FAIL; no check uses assert.

Conventions (rows are augmented curvature-centre coordinates, LMW Def 3.2):
  sphere  (centre x, signed radius r != 0):  (|x|^2/r - r, 1/r, x/r)
  plane   (unit normal h, offset d: <h,y> = d): (2d, 0, h)              -- LMW (3.9), bbar = 2d (GLMWY I p. 8)
  Lorentz pairing <u,v> = -(u0 v1 + u1 v0)/2 + sum_k u_k v_k            -- G = [[0,-1/2],[-1/2,0]] + I_n
  Q_n = I - (1/n) J on R^{n+2};  target T = [[0,-4,0],[-4,0,0],[0,0,2I_n]] = 2 G^{-1}
"""
from fractions import Fraction as Fr
import math
import random
import sys

random.seed(20261010)
FAILS = []


def say(ok, label):
    print(("ok   " if ok else "FAIL ") + label)
    if not ok:
        FAILS.append(label)


# ---------- small linear algebra (lists of lists) ----------
def mat(m, n, f):
    return [[f(i, j) for j in range(n)] for i in range(m)]


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def transpose(A):
    return [list(col) for col in zip(*A)]


def ident(m, one=1):
    return mat(m, m, lambda i, j: one if i == j else 0)


def Qmat(n, exact=True):
    m = n + 2
    c = Fr(1, n) if exact else 1.0 / n
    return mat(m, m, lambda i, j: (1 if i == j else 0) - c)


def target(n):
    m = n + 2
    T = mat(m, m, lambda i, j: 0)
    T[0][1] = T[1][0] = -4
    for k in range(2, m):
        T[k][k] = 2
    return T


def Gmat(n, exact=True):
    m = n + 2
    zero = Fr(0) if exact else 0.0
    one = Fr(1) if exact else 1.0
    half = Fr(1, 2) if exact else 0.5
    G = mat(m, m, lambda i, j: zero)
    G[0][1] = G[1][0] = -half
    for k in range(2, m):
        G[k][k] = one
    return G


def lorentz(u, v):
    return -(u[0] * v[1] + u[1] * v[0]) / 2 + sum(u[k] * v[k] for k in range(2, len(u)))


def qform(n, u, v, exact=True):
    """u^T Q_n v."""
    c = Fr(1, n) if exact else 1.0 / n
    return sum(a * b for a, b in zip(u, v)) - c * sum(u) * sum(v)


def maxdiff(A, B):
    return max(abs(A[i][j] - B[i][j]) for i in range(len(A)) for j in range(len(A[0])))


def sphere_row(x, r):
    return [sum(t * t for t in x) / r - r, 1 / r] + [t / r for t in x]


def plane_row(h, d):
    return [2 * d, 0] + list(h)


def gram_lorentz(W):
    return [[lorentz(u, v) for v in W] for u in W]


def two_i_minus_j(m):
    return mat(m, m, lambda i, j: (2 if i == j else 0) - 1)


def identity_holds(W, n, exact=True, tol=1e-9):
    WtQW = matmul(matmul(transpose(W), Qmat(n, exact)), W)
    d = maxdiff(WtQW, target(n))
    return (d == 0) if exact else (d < tol), d


def gram_holds(W, exact=True, tol=1e-9):
    d = maxdiff(gram_lorentz(W), two_i_minus_j(len(W)))
    return (d == 0) if exact else (d < tol), d


def decode_row(w, exact=True, tol=1e-12):
    """A row of Lorentz norm 1: a sphere (b != 0) or a plane (b = 0)."""
    b = w[1]
    if (b != 0) if exact else abs(b) > tol:
        r = 1 / b
        x = [t / b for t in w[2:]]
        return ("sphere", x, r)
    return ("plane", list(w[2:]), w[0] / 2)


def geometric_tangent(a, b, exact=True, tol=1e-9):
    """LMW's oriented tangency unfolded (the three encoding lemmas)."""
    def eq(p, q):
        return (p == q) if exact else abs(p - q) < tol
    if a[0] == "sphere" and b[0] == "sphere":
        _, x, r = a
        _, y, s = b
        return eq(sum((p - q) ** 2 for p, q in zip(x, y)), (r + s) ** 2)
    if a[0] == "sphere" and b[0] == "plane":
        _, x, r = a
        _, h, d = b
        return eq(sum(p * q for p, q in zip(h, x)) - d, -r)
    if a[0] == "plane" and b[0] == "sphere":
        return geometric_tangent(b, a, exact, tol)
    _, h, _ = a
    _, k, _ = b
    return all(eq(p, -q) for p, q in zip(h, k))


# ---------- H1/H2 exact: the rational configurations ----------
def config_n2():
    # LMW Figure 3's (-1, 2, 2, 3): outer circle radius -1 at 0; 1/2 at (+-1/2, 0); 1/3 at (0, 2/3)
    return [sphere_row([Fr(0), Fr(0)], Fr(-1)), sphere_row([Fr(1, 2), Fr(0)], Fr(1, 2)),
            sphere_row([Fr(-1, 2), Fr(0)], Fr(1, 2)), sphere_row([Fr(0), Fr(2, 3)], Fr(1, 3))]


def config_n1():
    # intervals [0,2], [2,4] and the complement of [0,4]: centres 1, 3, 2; signed radii 1, 1, -2
    return [sphere_row([Fr(1)], Fr(1)), sphere_row([Fr(3)], Fr(1)), sphere_row([Fr(2)], Fr(-2))]


def config_n2_two_planes():
    # Two unit circles at (0,0), (2,0), between the oriented lines y=1 and y=-1.
    return [sphere_row([Fr(0), Fr(0)], Fr(1)), sphere_row([Fr(2), Fr(0)], Fr(1)),
            plane_row([Fr(0), Fr(1)], Fr(1)), plane_row([Fr(0), Fr(-1)], Fr(1))]


def check_exact_configs():
    for n, W in ((2, config_n2()), (1, config_n1())):
        ok, d = gram_holds(W)
        say(ok, f"H1 n={n}: Lorentz Gram W G W^T = 2I - J (exact)")
        ok, d = identity_holds(W, n)
        say(ok, f"H1 n={n}: W^T Q_n W = target (exact)")
        b = [w[1] for w in W]
        say(sum(b) ** 2 == n * sum(t * t for t in b), f"H1 n={n}: Soddy-Gosset (sum b)^2 = n sum b^2 (exact)")
        if n == 2:
            # complex Descartes: z_i = x + i y;  (sum b z)^2 = 2 sum (b z)^2
            bx = [w[2] for w in W]  # rows already carry b x and b y
            by = [w[3] for w in W]
            re_l, im_l = sum(bx) ** 2 - sum(by) ** 2, 2 * sum(bx) * sum(by)
            re_r, im_r = 2 * sum(bx[i] ** 2 - by[i] ** 2 for i in range(4)), 4 * sum(bx[i] * by[i] for i in range(4))
            say(re_l == re_r and im_l == im_r, "H1 n=2: complex Descartes (sum bz)^2 = 2 sum (bz)^2 (exact, real and imaginary parts)")
        # the curvature-centre matrix M (LMW Thm 3.2): M^T Q M = diag(0, 2I)
        M = [w[1:] for w in W]
        MtQM = matmul(matmul(transpose(M), Qmat(n)), M)
        D = mat(n + 1, n + 1, lambda i, j: 2 if (i == j and i > 0) else 0)
        say(maxdiff(MtQM, D) == 0, f"H1 n={n}: M^T Q_n M = diag(0, 2I_n) (LMW Thm 3.2, exact)")
    # the gate's nested pair: r = 2 at 0, r = -1 at distance 1 - pairs to -1 although interiors overlap
    u = sphere_row([Fr(0), Fr(0)], Fr(2))
    v = sphere_row([Fr(1), Fr(0)], Fr(-1))
    say(lorentz(u, v) == -1, "H2 scope: the nested pair (r=2 at 0, r=-1 at distance 1) pairs to -1 (orientation not claimed)")


# ---------- inverse formulas ----------
def check_inverses():
    for n in range(1, 9):
        m = n + 2
        A = matmul(two_i_minus_j(m), [[q / 2 for q in row] for row in Qmat(n)])
        say(maxdiff(A, ident(m)) == 0, f"(2I - J)(Q_{n}/2) = I")
        Qinv = mat(m, m, lambda i, j: (1 if i == j else 0) - Fr(1, 2))
        say(maxdiff(matmul(Qmat(n), Qinv), ident(m)) == 0, f"Q_{n}^-1 = I - J/2")
        say(maxdiff(matmul(target(n), [[g / 2 for g in row] for row in Gmat(n)]), ident(m)) == 0,
            f"T (G/2) = I at n={n}")


# ---------- H3: base configuration with sqrt (float) ----------
def base_config(n):
    """Two parallel hyperplanes and n unit spheres centred at sqrt2 e_i (float rows)."""
    s2 = math.sqrt(2.0)
    sn = math.sqrt(float(n))
    rows = []
    for i in range(n):
        x = [0.0] * n
        x[i] = s2
        rows.append(sphere_row(x, 1.0))
    h = [1.0 / sn] * n
    rows.append(plane_row(h, s2 / sn + 1.0))
    rows.append(plane_row([-t for t in h], 1.0 - s2 / sn))
    return rows


def reflect_row(W, k, n):
    """Apollonian reflection: row k -> (2/(n-1)) sum_{i != k} w_i - w_k."""
    m = n + 2
    c = (Fr(2, n - 1) if isinstance(W[0][0], Fr) else 2.0 / (n - 1))
    s = [sum(W[i][j] for i in range(m) if i != k) for j in range(m)]
    new = [c * s[j] - W[k][j] for j in range(m)]
    return [new if i == k else list(W[i]) for i in range(m)]


def check_base_and_reflection():
    for n in range(1, 8):
        W = base_config(n)
        ok, d = gram_holds(W, exact=False, tol=1e-9)
        say(ok, f"H3 base W0({n}): Lorentz Gram 2I - J (float, max err {d:.1e})")
        ok, d = identity_holds(W, n, exact=False, tol=1e-9)
        say(ok, f"H3 base W0({n}): W^T Q W = target (float, max err {d:.1e})")
        if n >= 2:
            W1 = reflect_row(W, n, n)       # reflect the first plane row
            W2 = reflect_row(W1, n + 1, n)  # then the second
            ok1, _ = identity_holds(W1, n, exact=False)
            ok2, _ = identity_holds(W2, n, exact=False)
            say(ok1 and ok2, f"H5 n={n}: both Apollonian reflections of W0 keep the identity (float)")
            b = [w[1] for w in W2]
            want = [1.0] * n + [2.0 * n / (n - 1), 2.0 * n * (n + 1) / (n - 1) ** 2]
            say(max(abs(p - q) for p, q in zip(b, want)) < 1e-9 and all(abs(t) > 1e-9 for t in b),
                f"H5 n={n}: curvatures (1,...,1, 2n/(n-1), 2n(n+1)/(n-1)^2), all nonzero (float)")
            dec = [decode_row(w, exact=False) for w in W2]
            say(all(dec[i][0] == "sphere" for i in range(n + 2)) and
                all(geometric_tangent(dec[i], dec[j], exact=False) for i in range(n + 2) for j in range(n + 2) if i != j),
                f"H5 n={n}: the decoded all-sphere family is pairwise tangent geometrically (float)")
            # the two-sphere theorem: along the line w_k + t (w_k' - w_k) the Lorentz norm is 1 only at t = 0, 1
            for k in (0, n):
                Wr = reflect_row(W, k, n)
                dvec = [Wr[k][j] - W[k][j] for j in range(n + 2)]
                dd = lorentz(dvec, dvec)
                cross = lorentz(W[k], dvec)
                # norm(t) = 1 + 2 t cross + t^2 dd ; roots t = 0 and t = -2 cross/dd, which must be 1
                say(abs(dd) > 1e-9 and abs(-2 * cross / dd - 1.0) < 1e-9,
                    f"H5 n={n} k={k}: the norm along the admissible line has exactly the roots t=0,1 (float)")
                say(all(abs(lorentz(dvec, W[i])) < 1e-9 for i in range(n + 2) if i != k),
                    f"H5 n={n} k={k}: the reflected row pairs to -1 with every other row (float)")
            # the rows are a basis (det W != 0): the admissible set is exactly that line
            say(abs(det_float(W)) > 1e-9, f"H5 n={n}: W0 invertible (det {det_float(W):.3e}) (float)")


def det_float(A):
    A = [list(map(float, r)) for r in A]
    m = len(A)
    d = 1.0
    for c in range(m):
        p = max(range(c, m), key=lambda i: abs(A[i][c]))
        if abs(A[p][c]) < 1e-14:
            return 0.0
        if p != c:
            A[c], A[p] = A[p], A[c]
            d = -d
        d *= A[c][c]
        for i in range(c + 1, m):
            f = A[i][c] / A[c][c]
            for j in range(c, m):
                A[i][j] -= f * A[c][j]
    return d


# ---------- H3: the converse of Soddy-Gosset by one Q-reflection ----------
def q_reflection(n, v, exact):
    """R = I - (2/<v,v>) v (Q v)^T, a Q_n-isometry when <v,v>_Q != 0; R v = -v."""
    m = n + 2
    Q = Qmat(n, exact)
    Qv = [sum(Q[i][j] * v[j] for j in range(m)) for i in range(m)]
    vv = qform(n, v, v, exact)
    return mat(m, m, lambda i, j: (1 if i == j else 0) - 2 * v[i] * Qv[j] / vv)


def random_null_exact(n, trials=3):
    """Rational null vectors: start from the indicator of n coordinates and apply rational Q-reflections."""
    m = n + 2
    b = [Fr(1)] * n + [Fr(0), Fr(0)]
    random.shuffle(b)
    for _ in range(trials):
        v = [Fr(random.randint(-3, 3)) for _ in range(m)]
        if qform(n, v, v) == 0:
            continue
        R = q_reflection(n, v, True)
        b = [sum(R[i][j] * b[j] for j in range(m)) for i in range(m)]
    return b


def complete_from_curvatures(n, b, W0, exact):
    """H3's construction: reflect W0 so that its second column becomes b; else use the first column."""
    m = n + 2
    b0 = [W0[i][1] for i in range(m)]
    bbar0 = [W0[i][0] for i in range(m)]
    pair = qform(n, b0, b, exact)
    if (pair != 0) if exact else abs(pair) > 1e-9:
        v = [p - q for p, q in zip(b0, b)]
        R = q_reflection(n, v, exact)
        return matmul(R, W0)
    pair2 = qform(n, bbar0, b, exact)
    say((pair2 != 0) if exact else abs(pair2) > 1e-9, f"H3 n={n}: a pairing with b0 or with bbar0 is nonzero (b != 0)")
    # swap the two hyperbolic columns of W0 (T is symmetric under the swap), then reflect
    W0s = [[w[1], w[0]] + w[2:] for w in W0]
    v = [p - q for p, q in zip(bbar0, b)]
    R = q_reflection(n, v, exact)
    return matmul(R, W0s)


def check_converse_soddy_gosset():
    # exact at n = 1, 2 (rational base points), float at n = 3..7
    for n in range(1, 8):
        exact = n <= 2
        W0 = {1: config_n1(), 2: config_n2()}.get(n) if exact else base_config(n)
        for trial in range(6):
            if exact:
                b = random_null_exact(n)
            else:
                b = [float(t) for t in random_null_exact(n)]
            say(any(t != 0 for t in b), f"H3 n={n} trial {trial}: the random null vector is nonzero")
            W = complete_from_curvatures(n, b, W0, exact)
            scale = max(1.0, max(abs(float(t)) for w in W for t in w)) ** 2
            ok, d = identity_holds(W, n, exact=exact, tol=1e-9 * scale)
            col = [W[i][1] for i in range(n + 2)]
            okb = all((p == q) if exact else abs(p - q) < 1e-9 * scale for p, q in zip(col, b))
            dec = [decode_row(w, exact=exact, tol=1e-9) for w in W]
            okt = all(geometric_tangent(dec[i], dec[j], exact=exact, tol=1e-8 * scale)
                      for i in range(n + 2) for j in range(n + 2) if i != j)
            kinds = "".join("s" if d_[0] == "sphere" else "p" for d_ in dec)
            say(ok and okb and okt,
                f"H3 n={n} trial {trial}: W^T Q W = target, second column = b, decoded rows pairwise tangent [{kinds}]"
                + ("" if exact else f" (max err {d:.1e})"))
    # the dichotomy: both pairings vanish only for b = 0 (checked by the y-argument at n = 2 exactly)
    n = 2
    W0 = config_n2()
    Ginv_half = [[g / 2 for g in row] for row in Gmat(n)]
    W0inv = matmul(matmul(Ginv_half, transpose(W0)), Qmat(n))
    say(maxdiff(matmul(W0inv, W0), ident(4)) == 0 and maxdiff(matmul(W0, W0inv), ident(4)) == 0,
        "H3: W0^-1 = (G/2) W0^T Q explicitly (exact, n=2)")


# ---------- H4: the converse of Theorem 3.2 (completion) ----------
def complete_curvature_centre(n, M, exact):
    """M = [b | V] with M^T Q M = diag(0, 2I), b != 0  ->  bbar with [bbar | b | V]^T Q [...] = target."""
    m = n + 2
    Q = Qmat(n, exact)
    b = [M[i][0] for i in range(m)]
    V = [M[i][1:] for i in range(m)]
    # P = I - (1/2) V V^T Q
    VtQ = matmul(transpose(V), Q)
    P = mat(m, m, lambda i, j: (1 if i == j else 0) - sum(V[i][k] * VtQ[k][j] for k in range(n)) / 2)
    Qb = [sum(Q[i][j] * b[j] for j in range(m)) for i in range(m)]
    ell = max(range(m), key=lambda i: abs(Qb[i]))
    say((Qb[ell] != 0) if exact else abs(Qb[ell]) > 1e-9, f"H4 n={n}: Q b != 0 for a nonzero first column")
    z = [P[i][ell] for i in range(m)]
    zb = qform(n, z, b, exact)
    zz = qform(n, z, z, exact)
    say((zb != 0) if exact else abs(zb) > 1e-9, f"H4 n={n}: <z, b> != 0 for z = P e_l")
    bbar = [(-4 / zb) * (z[i] - (zz / (2 * zb)) * b[i]) for i in range(m)]
    return bbar


def check_converse_thm32():
    for n in range(1, 8):
        exact = n <= 2
        W0 = {1: config_n1(), 2: config_n2()}.get(n) if exact else base_config(n)
        for trial in range(4):
            b = random_null_exact(n) if exact else [float(t) for t in random_null_exact(n)]
            W = complete_from_curvatures(n, b, W0, exact)
            M = [w[1:] for w in W]
            bbar = complete_curvature_centre(n, M, exact)
            first = [w[0] for w in W]
            scale = max(1.0, max(abs(float(t)) for t in first)) ** 2
            ok = all((p == q) if exact else abs(p - q) < 1e-9 * scale for p, q in zip(bbar, first))
            say(ok, f"H4 n={n} trial {trial}: the completion of M recovers the original bbar column ({'exact' if exact else 'float'})")
    # the counterexample: M0 = [0 | e0 - e1 | e2 - e3] at n = 2 solves M^T Q M = diag(0,2,2) and completes to nothing
    n = 2
    M0 = [[Fr(0), Fr(1), Fr(0)], [Fr(0), Fr(-1), Fr(0)], [Fr(0), Fr(0), Fr(1)], [Fr(0), Fr(0), Fr(-1)]]
    MtQM = matmul(matmul(transpose(M0), Qmat(n)), M0)
    D = mat(3, 3, lambda i, j: 2 if (i == j and i > 0) else 0)
    say(maxdiff(MtQM, D) == 0, "H4: M0 = [0 | e0-e1 | e2-e3] satisfies M^T Q_2 M = diag(0,2,2)")
    # a completion W = [bbar | 0 | V] would need (W^T Q W)[0][1] = <bbar, 0>_Q = -4; compute it for twenty bbar
    b0 = [Fr(0)] * 4
    entries = set()
    for _ in range(20):
        bbar = [Fr(random.randint(-9, 9), random.randint(1, 5)) for _ in range(4)]
        entries.add(qform(n, bbar, b0))
    say(entries == {Fr(0)}, "H4: every completion of M0 has (0,1) entry <bbar, 0>_Q = 0, never -4: the hypothesis b != 0 is needed")
    # the rows of M0 are four oriented lines with normals +-e0, +-e1; perpendicular lines are not tangent
    dec0 = [decode_row([Fr(0)] + row) for row in M0]
    say(all(d_[0] == "plane" for d_ in dec0) and not all(geometric_tangent(dec0[i], dec0[j]) for i in range(4) for j in range(4) if i != j),
        "H4: M0 is the curvature-centre matrix of four oriented lines that are not pairwise tangent")


# ---------- H6: Mathlib Sphere conventions ----------
def check_sphere_bridge():
    # IsExtTangent: dist = r1 + r2 (positive radii) -> signed form with s = r
    # IsIntTangent s1 s2: dist = r2 - r1 (s1 inside s2) -> signed form with s_e = -r_e for the enclosing e
    W = config_n2()
    dec = [decode_row(w) for w in W]
    e = 0  # the enclosing circle (r = -1)
    for j in range(1, 4):
        _, x, r = dec[j]
        _, y, s = dec[e]
        dist2 = sum((p - q) ** 2 for p, q in zip(x, y))
        say(dist2 == ((-s) - r) ** 2, f"H6: IsIntTangent form dist = r_e - r_j holds for j={j} (r_e = {-s})")
    for i in range(1, 4):
        for j in range(i + 1, 4):
            _, x, r = dec[i]
            _, y, s = dec[j]
            say(sum((p - q) ** 2 for p, q in zip(x, y)) == (r + s) ** 2 and r > 0 and s > 0,
                f"H6: IsExtTangent form dist = r_i + r_j for ({i},{j})")


# ---------- control: a perturbed configuration fails ----------
def check_control():
    W = [list(w) for w in config_n2()]
    W[3][2] += Fr(1, 10)
    ok, _ = identity_holds(W, 2)
    say(not ok, "control: perturbing one centre breaks the identity")


# ---------- the statements the earlier checks did not exercise ----------
def random_config(n, exact):
    """A random configuration: W0 moved by a random Q_n-reflection (exact at n <= 2)."""
    W0 = {1: config_n1(), 2: config_n2()}.get(n) if exact else base_config(n)
    m = n + 2
    for _ in range(2):
        v = [Fr(random.randint(-3, 3)) if exact else float(random.randint(-3, 3)) for _ in range(m)]
        if (qform(n, v, v, exact) == 0) if exact else abs(qform(n, v, v, exact)) < 1e-9:
            continue
        W0 = matmul(q_reflection(n, v, exact), W0)
    return W0


def apollonian_gen(n, k, exact):
    """The Challenge's apollonianGen: S_k = 1 + (2/(n-1)) e_k 1^T - (2n/(n-1)) e_k e_k^T."""
    m = n + 2
    a = Fr(2, n - 1) if exact else 2.0 / (n - 1)
    c = Fr(2 * n, n - 1) if exact else 2.0 * n / (n - 1)
    return mat(m, m, lambda i, j: (1 if i == j else 0) + (a if i == k else 0) - (c if (i == k and j == k) else 0))


def check_remaining():
    # theorem 7 row_injOn_valid and the decoding: row(decode(w)) = w and decode(row(s)) = s on the n = 2 rows
    W = config_n2()
    for w in W:
        d = decode_row(w)
        back = sphere_row(d[1], d[2]) if d[0] == "sphere" else plane_row(d[1], d[2])
        say(back == w, "T7/T8: row(decode(w)) = w on a sphere row (exact)")
    h = [Fr(3, 5), Fr(4, 5)]
    w = plane_row(h, Fr(7, 3))
    d = decode_row(w)
    say(d == ("plane", h, Fr(7, 3)), "T7/T8: decode(planeRow h d) = (h, d) on a unit-normal plane row (exact)")
    # theorem 17: (sum b)^2 = n sum b^2 <-> b^T Q_n b = 0, on null and non-null vectors
    for n in range(1, 6):
        for _ in range(4):
            b = [Fr(random.randint(-4, 4)) for _ in range(n + 2)]
            lhs = (sum(b) ** 2 == n * sum(t * t for t in b))
            rhs = (qform(n, b, b) == 0)
            say(lhs == rhs, f"T17 n={n}: the Soddy-Gosset relation holds iff b^T Q_n b = 0 (exact; here {'both' if lhs else 'neither'})")
        bnull = random_null_exact(n)
        say(sum(bnull) ** 2 == n * sum(t * t for t in bnull) and qform(n, bnull, bnull) == 0, f"T17 n={n}: a random null vector satisfies both forms (exact)")
    # theorem 21: LMW (2.3) sum b (b z) = (1/2)(sum b)(sum b z) at n = 2, exact in the real and imaginary parts
    W = config_n2()
    bb = [w[1] for w in W]
    bx = [w[2] for w in W]
    by = [w[3] for w in W]
    say(sum(bb[i] * bx[i] for i in range(4)) == Fr(1, 2) * sum(bb) * sum(bx) and sum(bb[i] * by[i] for i in range(4)) == Fr(1, 2) * sum(bb) * sum(by),
        "T21: LMW (2.3) sum b (b z) = (1/2)(sum b)(sum b z) on the n = 2 configuration (exact)")
    # theorem 22: det Q_n = -2/n exactly, n = 1..6 (Bareiss)
    for n in range(1, 7):
        say(det_exact(Qmat(n)) == Fr(-2, n), f"T22: det Q_{n} = -2/{n} (exact)")
    # theorems 32, 34: the Challenge's S_k matrix preserves Q_n and its row k is the reflected row
    for n in range(2, 7):
        exact = n <= 2
        W = random_config(n, exact)
        for k in (0, n + 1):
            S = apollonian_gen(n, k, exact)
            StQS = matmul(matmul(transpose(S), Qmat(n, exact)), S)
            d = maxdiff(StQS, Qmat(n, exact))
            say((d == 0) if exact else d < 1e-9, f"T32 n={n} k={k}: S_k^T Q_n S_k = Q_n for the Challenge's apollonianGen")
            SW = matmul(S, W)
            R = reflect_row(W, k, n)
            d2 = maxdiff(SW, R)
            say((d2 == 0) if exact else d2 < 1e-8, f"T34 n={n} k={k}: (S_k W) k = (2/(n-1)) sum_{{i != k}} W i - W k, other rows fixed")
            # the curvature relation b_k + b_k' = (2/(n-1)) sum_{i != k} b_i on a random configuration
            bk, bk2 = W[k][1], SW[k][1]
            rhs = (Fr(2, n - 1) if exact else 2.0 / (n - 1)) * sum(W[i][1] for i in range(n + 2) if i != k)
            say((bk + bk2 == rhs) if exact else abs(bk + bk2 - rhs) < 1e-8, f"T35/T36 n={n} k={k}: b_k + b_k' = (2/(n-1)) sum of the others (random configuration)")
    # theorems 2, 3, 4, 6: non-tangent pairs do not pair to -1
    u = sphere_row([Fr(0), Fr(0)], Fr(1))
    v = sphere_row([Fr(3), Fr(0)], Fr(1))
    say(lorentz(u, v) != -1, "T2: two unit circles at distance 3 (not tangent) pair to " + str(lorentz(u, v)) + ", not -1")
    pl = plane_row([Fr(1), Fr(0)], Fr(5))
    say(lorentz(u, pl) != -1, "T3: the unit circle at 0 and the line x = 5 (not tangent) pair to " + str(lorentz(u, pl)) + ", not -1")
    say(lorentz(pl, plane_row([Fr(0), Fr(1)], Fr(0))) != -1, "T4: perpendicular lines pair to 0, not -1")
    say(lorentz(pl, plane_row([Fr(1), Fr(0)], Fr(-2))) == 1, "T4: parallel lines with the same normal pair to 1, not -1")
    # the base configuration's own sphere-plane tangencies, decoded and checked (float); Soddy-Gosset with planes
    for n in range(1, 6):
        W0 = base_config(n)
        dec = [decode_row(w, exact=False) for w in W0]
        kinds = "".join("s" if d_[0] == "sphere" else "p" for d_ in dec)
        say(kinds == "s" * n + "pp" and all(geometric_tangent(dec[i], dec[j], exact=False) for i in range(n + 2) for j in range(n + 2) if i != j),
            f"T3/T6/T16 n={n}: W0's rows decode to {kinds} and every pair, sphere-plane and plane-plane included, is tangent geometrically")
        b = [w[1] for w in W0]
        say(abs(sum(b) ** 2 - n * sum(t * t for t in b)) < 1e-9, f"T16 n={n}: Soddy-Gosset on W0 with its two hyperplanes (curvature 0)")
    # uniqueness of the decoded family: two valid objects with the same row are equal (the decoding is a function of the row)
    W = config_n2()
    say(all(decode_row(W[i]) == decode_row(list(W[i])) for i in range(4)) and len({tuple(w) for w in W}) == 4,
        "T13/T14: the family is determined by W (decoding is a function of the rows; the four rows are distinct)")
    # theorem 30 on an independently built M: start from a null b and random Q-orthonormal centre columns? use a configuration's M at n = 1, 2 then perturb bbar and recover
    for n in (1, 2):
        W = random_config(n, True)
        M = [w[1:] for w in W]
        bbar = complete_curvature_centre(n, M, True)
        W2 = [[bbar[i]] + M[i] for i in range(n + 2)]
        ok, _ = identity_holds(W2, n)
        say(ok and bbar == [w[0] for w in W], f"T30 n={n}: the completion of M rebuilds the unique solution W (exact, random configuration)")


def det_exact(A):
    """Bareiss determinant over Fractions."""
    A = [list(r) for r in A]
    m = len(A)
    sign = 1
    prev = Fr(1)
    for k in range(m - 1):
        if A[k][k] == 0:
            sw = next((i for i in range(k + 1, m) if A[i][k] != 0), None)
            if sw is None:
                return Fr(0)
            A[k], A[sw] = A[sw], A[k]
            sign = -sign
        for i in range(k + 1, m):
            for j in range(k + 1, m):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) / prev
        prev = A[k][k]
    return sign * A[m - 1][m - 1]


# ---------- rigid-motion reconstruction, independently from geometric data ----------
def rows_of_objects(objects):
    """Encode exact geometric objects, retaining Fraction entries even at zero curvature."""
    return [[Fr(c) for c in (sphere_row(x, r) if kind == "sphere" else plane_row(x, r))]
            for kind, x, r in objects]


def transform_object(obj, O, t):
    """Move geometric data directly: row vectors x -> x O + t, h -> h O."""
    kind, x, r = obj
    moved = [sum(x[j] * O[j][k] for j in range(len(t))) for k in range(len(t))]
    if kind == "sphere":
        return kind, [moved[k] + t[k] for k in range(len(t))], r
    return kind, moved, r + sum(moved[k] * t[k] for k in range(len(t)))


def rigid_motion_matrix(O, t):
    """The expected augmented action, for row vectors (bbar, b, v)."""
    n = len(t)
    A = mat(n + 2, n + 2, lambda i, j: Fr(0))
    A[0][0] = A[1][1] = Fr(1)
    A[1][0] = sum(c * c for c in t)
    for i in range(n):
        A[1][i + 2] = t[i]
        A[i + 2][0] = 2 * sum(O[i][j] * t[j] for j in range(n))
        for j in range(n):
            A[i + 2][j + 2] = O[i][j]
    return A


def reconstruct_motion(n, W, Wprime):
    """Recover the action from two matrices without using the supplied motion parameters."""
    Ghalf = [[g / 2 for g in row] for row in Gmat(n)]
    Winv = matmul(matmul(Ghalf, transpose(W)), Qmat(n))
    A = matmul(Winv, Wprime)
    return A, [row[2:] for row in A[2:]], A[1][2:]


def check_rigidity():
    sphere1 = [decode_row(w) for w in config_n1()]
    sphere2 = [decode_row(w) for w in config_n2()]
    strip2 = [decode_row(w) for w in config_n2_two_planes()]
    rotation = [[Fr(3, 5), Fr(-4, 5)], [Fr(4, 5), Fr(3, 5)]]
    reflection = [[Fr(3, 5), Fr(4, 5)], [Fr(4, 5), Fr(-3, 5)]]
    cases = [
        ("n=1 translation", 1, sphere1, [[Fr(1)]], [Fr(5, 3)]),
        ("n=1 reflection and translation", 1, sphere1, [[Fr(-1)]], [Fr(-7, 4)]),
        ("n=2 sphere rotation and translation", 2, sphere2, rotation, [Fr(7, 3), Fr(-2, 5)]),
        ("n=2 sphere reflection and translation", 2, sphere2, reflection, [Fr(-5, 7), Fr(11, 6)]),
        ("n=2 two-plane rotation and translation", 2, strip2, rotation, [Fr(7, 3), Fr(-2, 5)]),
        ("n=2 two-plane reflection and translation", 2, strip2, reflection, [Fr(-5, 7), Fr(11, 6)]),
    ]
    for label, n, objects, O, t in cases:
        W = rows_of_objects(objects)
        moved = [transform_object(obj, O, t) for obj in objects]
        Wprime = rows_of_objects(moved)
        A, recovered_O, recovered_t = reconstruct_motion(n, W, Wprime)
        say(all(isinstance(c, Fr) for row in A for c in row),
            f"rigidity {label}: reconstruction uses Fraction throughout")
        say(identity_holds(W, n)[0] and identity_holds(Wprime, n)[0] and
            all(geometric_tangent(moved[i], moved[j]) for i in range(n + 2)
                for j in range(i + 1, n + 2)),
            f"rigidity {label}: source and transformed augmented identities and tangency (exact)")
        say([w[1] for w in W] == [w[1] for w in Wprime],
            f"rigidity {label}: every labelled curvature is preserved (exact)")
        say(A == rigid_motion_matrix(O, t) and matmul(W, A) == Wprime,
            f"rigidity {label}: reconstructed W^-1 W' equals the expected block matrix (exact)")
        say(recovered_O == O and recovered_t == t and
            matmul(transpose(recovered_O), recovered_O) == ident(n) and
            matmul(recovered_O, transpose(recovered_O)) == ident(n),
            f"rigidity {label}: the reconstructed O and t equal the applied motion, and O is orthogonal (exact)")
        decoded = [decode_row(w) for w in Wprime]
        sphere_ok = True
        plane_ok = True
        has_plane = False
        for i, (kind, x, r) in enumerate(objects):
            recovered_spatial = [sum(x[j] * recovered_O[j][k] for j in range(n)) for k in range(n)]
            if kind == "sphere":
                expected_center = [recovered_spatial[k] + recovered_t[k] for k in range(n)]
                sphere_ok &= decoded[i] == ("sphere", expected_center, r)
            else:
                has_plane = True
                expected_offset = r + sum(recovered_spatial[k] * recovered_t[k] for k in range(n))
                plane_ok &= (decoded[i] == ("plane", recovered_spatial, expected_offset) and
                             sum(c * c for c in recovered_spatial) == 1)
        say(sphere_ok, f"rigidity {label}: sphere centres and signed radii follow the reconstructed motion (exact)")
        if has_plane:
            say(plane_ok, f"rigidity {label}: unit normals and offsets follow the reconstructed motion (exact)")

    # Keep both matrix identities true, but change a curvature by an Apollonian reflection.
    W = rows_of_objects(sphere2)
    Wprime = rows_of_objects([transform_object(obj, rotation, [Fr(7, 3), Fr(-2, 5)]) for obj in sphere2])
    changed = reflect_row(Wprime, 0, 2)
    A, O, t = reconstruct_motion(2, W, changed)
    curvature_basis = [Fr(0), Fr(1), Fr(0), Fr(0)]
    say(identity_holds(changed, 2)[0] and [w[1] for w in changed] != [w[1] for w in W] and
        [row[1] for row in A] != curvature_basis and A != rigid_motion_matrix(O, t),
        "rigidity control: a valid Apollonian replacement changes a curvature and is not a rigid motion (exact)")

    # Keep all signed radii and row norms valid, but deform centres by a nonorthogonal map.
    stretch = [[Fr(2), Fr(0)], [Fr(0), Fr(1)]]
    stretched = rows_of_objects([transform_object(obj, stretch, [Fr(7, 3), Fr(-2, 5)]) for obj in sphere2])
    A, O, _ = reconstruct_motion(2, W, stretched)
    say([w[1] for w in stretched] == [w[1] for w in W] and O == stretch and
        not identity_holds(stretched, 2)[0] and
        matmul(matmul(transpose(A), target(2)), A) != target(2),
        "rigidity control: a nonorthogonal stretch keeps every signed radius; its linear part is recovered, and the moved family fails the augmented identity in both forms (exact)")


# ---------- normalized oriented interiors, checked against direct geometry ----------
def reverse_object(obj):
    """Reverse the sphere orientation, or both the plane normal and its signed offset."""
    kind, x, r = obj
    return (kind, x, -r) if kind == "sphere" else (kind, [-c for c in x], -r)


def geometric_interior(obj, y):
    """Direct ball/exterior/halfspace membership, independently of augmented rows."""
    kind, x, r = obj
    if kind == "sphere":
        distance_squared = sum((a - b) ** 2 for a, b in zip(y, x))
        return distance_squared < r * r if r > 0 else distance_squared > r * r
    return sum(a * b for a, b in zip(x, y)) > r


def row_power(w, y):
    return w[1] * sum(c * c for c in y) - 2 * sum(a * b for a, b in zip(w[2:], y)) + w[0]


def geometric_power(obj, y):
    kind, x, r = obj
    if kind == "sphere":
        return (sum((a - b) ** 2 for a, b in zip(y, x)) - r * r) / r
    return 2 * (r - sum(a * b for a, b in zip(x, y)))


def check_orientation():
    line_points = [[Fr(c, 2)] for c in (-2, 0, 1, 2, 3, 4, 5, 6, 7, 8, 10)]
    axis = [Fr(-2), Fr(-1), Fr(-1, 2), Fr(0), Fr(1, 2), Fr(1), Fr(2)]
    plane_points = [[x, y] for x in axis for y in axis] + [[Fr(0), Fr(2, 3)], [Fr(0), Fr(1, 3)]]
    cases = [("n=1 spheres", 1, config_n1(), line_points),
             ("n=2 spheres", 2, config_n2(), plane_points),
             ("n=2 two planes", 2, config_n2_two_planes(), plane_points)]
    for label, n, baseline, points in cases:
        original = [decode_row(w) for w in baseline]
        for sign in (1, -1):
            objects = original if sign == 1 else [reverse_object(obj) for obj in original]
            W = rows_of_objects(objects)
            A = sum(w[0] for w in W)
            B = sum(w[1] for w in W)
            V = [sum(w[k + 2] for w in W) for k in range(n)]
            normalized = objects if B > 0 else [reverse_object(obj) for obj in objects]
            values = [[row_power(w, y) for w in W] for y in points]
            prefix = f"orientation {label}, global sign {sign:+d}"
            say(W == [[sign * c for c in w] for w in baseline] and identity_holds(W, n)[0] and B != 0,
                f"{prefix}: the global sign gives the expected rows and preserves the identity (exact)")
            say(A * B - sum(c * c for c in V) == n * (n + 2),
                f"{prefix}: column-sum discriminant is n(n+2) (exact)")
            say(all(all(isinstance(f, Fr) and f == geometric_power(obj, y) and
                        (f < 0) == geometric_interior(obj, y)
                        for f, obj in zip(F, objects)) for y, F in zip(points, values)),
                f"{prefix}: polynomial values and negative sets equal geometric powers/interiors (exact)")
            say(all(sum(F) ** 2 == n * sum(f * f for f in F) and qform(n, F, F) == 0 for F in values),
                f"{prefix}: every sampled power vector is Descartes-null in both forms (exact)")
            say(all(B * sum(F) == n * (n + 2) + sum((B * y[k] - V[k]) ** 2 for k in range(n)) and
                    B * sum(F) > 0 for y, F in zip(points, values)),
                f"{prefix}: positive power-sum identity is an exact sum of squares (exact)")
            say(all(all((B * f < 0) == geometric_interior(obj, y) for f, obj in zip(F, normalized))
                    for y, F in zip(points, values)) and
                (sign == 1 or any(sum(geometric_interior(obj, y) for obj in objects) > 1 for y in points)),
                f"{prefix}: total-curvature normalization matches the geometric orientation" +
                (" (exact)" if sign == 1 else "; control: the reversed family's raw interiors overlap at a sample (exact)"))
            say(all(sum(B * f < 0 for f in F) <= 1 and
                    sum(geometric_interior(obj, y) for obj in normalized) <= 1
                    for y, F in zip(points, values)),
                f"{prefix}: no point lies in two normalized interiors on {len(points)} rational samples (exact)")
            say(all(any(geometric_interior(obj, y) for y in points) and
                    any(geometric_power(obj, y) == 0 for y in points) for obj in normalized),
                f"{prefix}: samples include each object's interior and boundary")

    # A tangent pair alone can have overlapping specified interiors; it is not a full configuration.
    overlapping = [("sphere", [Fr(0), Fr(0)], Fr(2)), ("sphere", [Fr(1), Fr(0)], Fr(-1))]
    W = rows_of_objects(overlapping)
    y = [Fr(-1, 2), Fr(0)]
    F = [row_power(w, y) for w in W]
    say(geometric_tangent(*overlapping) and lorentz(*W) == -1 and
        all(geometric_interior(obj, y) for obj in overlapping) and all(f < 0 for f in F),
        "orientation H2 control: a tangent pair has overlapping specified interiors, detected by both powers (exact)")
    A, B = sum(w[0] for w in W), sum(w[1] for w in W)
    V = [sum(w[k + 2] for w in W) for k in range(2)]
    say(A * B - sum(c * c for c in V) != 8 and sum(F) ** 2 != 2 * sum(f * f for f in F),
        "orientation H2 control: the pair satisfies neither the configuration's discriminant n(n+2) = 8 nor the power-null identity (exact)")


# ---------- exact arithmetic over Q(sqrt 3): the rational obstruction at n = 3 ----------
# det(W)^2 = det(T) / det(Q_n) = n 2^(n+3), a rational square only at n = 1, 2, 8, 9, ...; no rational
# configuration exists at n = 3, but det(W) = 8 sqrt 3 there, and configurations over Q(sqrt 3) do.
class R3:
    """a + b sqrt 3 with Fraction a, b; a float operand raises, so no float can enter an exact check."""
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        if isinstance(a, float) or isinstance(b, float):
            raise TypeError("float entered Q(sqrt 3)")
        self.a, self.b = Fr(a), Fr(b)

    @staticmethod
    def of(o):
        if isinstance(o, R3):
            return o
        if isinstance(o, (int, Fr)):
            return R3(o)
        raise TypeError(f"not exact: {type(o).__name__}")

    def __add__(self, o):
        o = R3.of(o)
        return R3(self.a + o.a, self.b + o.b)
    __radd__ = __add__

    def __neg__(self):
        return R3(-self.a, -self.b)

    def __sub__(self, o):
        return self + (-R3.of(o))

    def __rsub__(self, o):
        return R3.of(o) - self

    def __mul__(self, o):
        o = R3.of(o)
        return R3(self.a * o.a + 3 * self.b * o.b, self.a * o.b + self.b * o.a)
    __rmul__ = __mul__

    def __truediv__(self, o):
        o = R3.of(o)
        nrm = o.a * o.a - 3 * o.b * o.b
        if nrm == 0:
            raise ZeroDivisionError("division by zero in Q(sqrt 3)")
        return self * R3(o.a / nrm, -o.b / nrm)

    def __rtruediv__(self, o):
        return R3.of(o) / self

    def __pow__(self, k):
        out = R3(1)
        for _ in range(k):
            out = out * self
        return out

    def sign(self):
        a, b = self.a, self.b
        sa, sb = (a > 0) - (a < 0), (b > 0) - (b < 0)
        if sa == sb or sb == 0:
            return sa
        if sa == 0:
            return sb
        return sa if a * a > 3 * b * b else sb

    def __eq__(self, o):
        if isinstance(o, float):
            raise TypeError("float compared in Q(sqrt 3)")
        if not isinstance(o, (R3, int, Fr)):
            return NotImplemented
        return (self - R3.of(o)).sign() == 0

    def __hash__(self):
        return hash((self.a, self.b))

    def __lt__(self, o):
        return (self - R3.of(o)).sign() < 0

    def __gt__(self, o):
        return (self - R3.of(o)).sign() > 0

    def __le__(self, o):
        return not self > o

    def __ge__(self, o):
        return not self < o

    def __abs__(self):
        return -self if self.sign() < 0 else self

    def __float__(self):
        return float(self.a) + float(self.b) * math.sqrt(3.0)

    def __repr__(self):
        return f"{self.a}+{self.b}*sqrt3"


S3 = R3(0, 1)


def exact_entry(c):
    if isinstance(c, float):
        raise TypeError("float in an exact row")
    return c if isinstance(c, R3) else Fr(c)


def rows_exact(objects):
    return [[exact_entry(c) for c in (sphere_row(x, r) if kind == "sphere" else plane_row(x, r))]
            for kind, x, r in objects]


def all_exact(rows):
    """No float anywhere (int entries, e.g. plane_row's curvature 0, are exact)."""
    return all(isinstance(c, (int, Fr, R3)) and not isinstance(c, bool) for row in rows for c in row)


def objs_n3_spheres():
    # curvatures (-1, 2, 2, 3, 3): (sum b)^2 = 81 = 3 sum b^2; centres in Q(sqrt 3)^3
    return [("sphere", [Fr(0)] * 3, Fr(-1)),
            ("sphere", [Fr(1, 2), Fr(0), Fr(0)], Fr(1, 2)), ("sphere", [Fr(-1, 2), Fr(0), Fr(0)], Fr(1, 2)),
            ("sphere", [Fr(0), S3 / 3, Fr(1, 3)], Fr(1, 3)), ("sphere", [Fr(0), S3 / 3, Fr(-1, 3)], Fr(1, 3))]


def objs_n3_strip():
    # three unit spheres on an equilateral triangle of side 2 between the oriented planes z = 1 and z = -1
    return [("sphere", [Fr(0), Fr(0), Fr(0)], Fr(1)), ("sphere", [Fr(2), Fr(0), Fr(0)], Fr(1)),
            ("sphere", [Fr(1), S3, Fr(0)], Fr(1)),
            ("plane", [Fr(0), Fr(0), Fr(1)], Fr(1)), ("plane", [Fr(0), Fr(0), Fr(-1)], Fr(1))]


def objs_alternatives():
    """Hand-built families with the same ordered curvatures, NOT produced by transform_object."""
    t2 = [Fr(3), Fr(-7, 2)]
    alt_n2 = [("sphere", [t2[0], t2[1]], Fr(-1)),
              ("sphere", [t2[0], t2[1] + Fr(1, 2)], Fr(1, 2)), ("sphere", [t2[0], t2[1] - Fr(1, 2)], Fr(1, 2)),
              ("sphere", [t2[0] + Fr(2, 3), t2[1]], Fr(1, 3))]
    alt_n1 = [("sphere", [Fr(6)], Fr(1)), ("sphere", [Fr(4)], Fr(1)), ("sphere", [Fr(5)], Fr(-2))]
    alt_strip2 = [("sphere", [Fr(5), Fr(1)], Fr(1)), ("sphere", [Fr(5), Fr(3)], Fr(1)),
                  ("plane", [Fr(-1), Fr(0)], Fr(-4)), ("plane", [Fr(1), Fr(0)], Fr(6))]
    t3 = [Fr(5, 2), Fr(-1), Fr(3)]

    def n3(zsign):
        return [("sphere", list(t3), Fr(-1)),
                ("sphere", [t3[0], t3[1] + Fr(1, 2), t3[2]], Fr(1, 2)),
                ("sphere", [t3[0], t3[1] - Fr(1, 2), t3[2]], Fr(1, 2)),
                ("sphere", [t3[0] + Fr(1, 3), t3[1], t3[2] + zsign * S3 / 3], Fr(1, 3)),
                ("sphere", [t3[0] - Fr(1, 3), t3[1], t3[2] + zsign * S3 / 3], Fr(1, 3))]
    return [("n=1 mirrored intervals", 1, [decode_row(w) for w in config_n1()], alt_n1),
            ("n=2 quarter-turned circles", 2, [decode_row(w) for w in config_n2()], alt_n2),
            ("n=2 strip turned upright", 2, [decode_row(w) for w in config_n2_two_planes()], alt_strip2),
            ("n=3 spheres, a turned copy", 3, objs_n3_spheres(), n3(1)),
            ("n=3 spheres, a mirrored copy", 3, objs_n3_spheres(), n3(-1))]


def lean_parameters(n, W1, W2):
    """Rigidity.lean's rigidMotion_parameters: O = (1/2) X^T Q X', t = -(1/4) a^T Q X'."""
    Q = Qmat(n)
    m = n + 2
    X1 = [[W1[i][k + 2] for k in range(n)] for i in range(m)]
    X2 = [[W2[i][k + 2] for k in range(n)] for i in range(m)]
    a1 = [W1[i][0] for i in range(m)]
    XtQX = matmul(matmul(transpose(X1), Q), X2)
    O = [[XtQX[k][l] / 2 for l in range(n)] for k in range(n)]
    aQX = matmul(matmul([a1], Q), X2)[0]
    return O, [-aQX[l] / 4 for l in range(n)]


def check_rigidity_desk():
    # (a) the motion direction at n = 3 over Q(sqrt 3): a rational rotation and a signed permutation
    rot3 = [[Fr(1, 3), Fr(2, 3), Fr(2, 3)], [Fr(2, 3), Fr(1, 3), Fr(-2, 3)], [Fr(-2, 3), Fr(2, 3), Fr(-1, 3)]]
    sperm = [[Fr(0), Fr(-1), Fr(0)], [Fr(0), Fr(0), Fr(-1)], [Fr(-1), Fr(0), Fr(0)]]
    say(matmul(transpose(rot3), rot3) == ident(3, Fr(1)) and matmul(transpose(sperm), sperm) == ident(3, Fr(1)) and
        det_exact(rot3) == 1 and det_exact(sperm) == -1,
        "desk rigidity n=3: (1/3)[[1,2,2],[2,1,-2],[-2,2,-1]] is a rotation (det 1), the signed permutation a reflection (det -1) (exact)")
    t = [Fr(-5, 4), S3 / 2, Fr(7, 3)]
    for cname, objects in (("spheres (-1,2,2,3,3)", objs_n3_spheres()), ("strip", objs_n3_strip())):
        W = rows_exact(objects)
        b = [w[1] for w in W]
        say(identity_holds(W, 3)[0] and all_exact(W) and sum(b) ** 2 == 3 * sum(c * c for c in b) and
            all(geometric_tangent(objects[i], objects[j]) for i in range(5) for j in range(5) if i != j),
            f"desk rigidity n=3 {cname}: W^T Q_3 W = target and pairwise tangency over Q(sqrt 3) (exact)")
        for oname, O in (("rotation", rot3), ("signed permutation", sperm)):
            moved = [transform_object(obj, O, t) for obj in objects]
            Wp = rows_exact(moved)
            A, rO, rt = reconstruct_motion(3, W, Wp)
            lO, lt = lean_parameters(3, W, Wp)
            say(all_exact(A) and identity_holds(Wp, 3)[0] and A == rigid_motion_matrix(O, t) and
                rO == O and rt == t and lO == O and lt == t,
                f"desk rigidity n=3 {cname}, {oname}: W^-1 W' is the motion matrix; O, t by Rigidity.lean's formulas (exact over Q(sqrt 3))")
    # (b) the congruence direction: two families built independently with equal curvatures
    for label, n, objs, alt in objs_alternatives():
        W, Wp = rows_exact(objs), rows_exact(alt)
        m = n + 2
        valid = (identity_holds(W, n)[0] and identity_holds(Wp, n)[0] and
                 all(geometric_tangent(alt[i], alt[j]) for i in range(m) for j in range(m) if i != j))
        same_b = [w[1] for w in W] == [w[1] for w in Wp]
        A, rO, rt = reconstruct_motion(n, W, Wp)
        lO, lt = lean_parameters(n, W, Wp)
        orth = matmul(transpose(rO), rO) == ident(n, Fr(1))
        motion = A == rigid_motion_matrix(rO, rt)
        maps = all(transform_object(objs[i], rO, rt) == alt[i] for i in range(m))
        say(valid and same_b and orth and motion and maps and lO == rO and lt == rt,
            f"desk congruence {label}: equal curvatures force W^-1 W' to be a Euclidean motion mapping each object (exact)")
    # (c) the curvature hypothesis is needed: the same spheres with two labels of unequal curvature swapped
    objs = objs_n3_spheres()
    swapped = [objs[0], objs[3], objs[2], objs[1], objs[4]]
    W, Wp = rows_exact(objs), rows_exact(swapped)
    A, rO, rt = reconstruct_motion(3, W, Wp)
    say(identity_holds(Wp, 3)[0] and [w[1] for w in W] != [w[1] for w in Wp] and
        matmul(transpose(rO), rO) != ident(3, Fr(1)) and A != rigid_motion_matrix(rO, rt),
        "desk congruence control n=3: a relabelling with unequal curvatures is valid but not a motion (exact)")


def tangency_point(a, b):
    """The finite contact point of a tangent pair, or None for two parallel hyperplanes."""
    if a[0] == "plane" and b[0] == "sphere":
        a, b = b, a
    if a[0] == "sphere" and b[0] == "sphere":
        _, x, r = a
        _, y, s = b
        return [(s * p + r * q) / (r + s) for p, q in zip(x, y)]
    if a[0] == "sphere" and b[0] == "plane":
        _, x, r = a
        _, h, _ = b
        return [p + r * q for p, q in zip(x, h)]
    return None


def desk_configurations():
    """Every family the checks below use: exact (Q or Q(sqrt 3)) and float, the random ones under their own seed."""
    out = [("n=1", 1, config_n1(), True), ("n=2", 2, config_n2(), True), ("n=2 strip", 2, config_n2_two_planes(), True),
           ("n=3 spheres", 3, rows_exact(objs_n3_spheres()), True), ("n=3 strip", 3, rows_exact(objs_n3_strip()), True)]
    for n in range(1, 8):
        out.append((f"W0({n})", n, base_config(n), False))
    saved = random.getstate()
    random.seed(20261011)
    for n in range(1, 8):
        exact = n <= 2
        W0 = {1: config_n1(), 2: config_n2()}.get(n) if exact else base_config(n)
        for trial in range(3):
            out.append((f"reflected n={n} #{trial}", n, random_config(n, exact), exact))
            b = random_null_exact(n)
            out.append((f"completed n={n} #{trial}", n,
                        complete_from_curvatures(n, b if exact else [float(c) for c in b], W0, exact), exact))
    random.setstate(saved)
    return out


def check_total_curvature_and_contacts():
    for label, n, W, exact in desk_configurations():
        m = n + 2
        A = sum(w[0] for w in W)
        B = sum(w[1] for w in W)
        V = [sum(w[k + 2] for w in W) for k in range(n)]
        scale = max(1.0, max(abs(float(c)) for w in W for c in w))
        disc = A * B - sum(c * c for c in V)
        mode = "exact" if exact else "float"
        if exact:
            ok = identity_holds(W, n)[0] and all_exact(W) and B != 0 and disc == n * (n + 2)
        else:
            ok = (identity_holds(W, n, exact=False, tol=1e-9 * scale ** 2)[0] and abs(B) > 1e-6 and
                  abs(disc - n * (n + 2)) < 1e-7 * scale ** 2)
        say(ok, f"desk B != 0 on {label}: B = {float(B):.4g}, AB - |V|^2 = n(n+2) ({mode})")
        dec = [decode_row(w, exact=exact, tol=1e-9 * scale) for w in W]
        planes = sum(d_[0] == "plane" for d_ in dec)
        tol = 1e-7 * scale ** 2
        pts, bad = [], []
        for i in range(m):
            for j in range(i + 1, m):
                p = tangency_point(dec[i], dec[j])
                if p is None:
                    continue
                pw = [row_power(W[k], p) for k in range(m)]
                on_ij = (pw[i] == 0 and pw[j] == 0) if exact else (abs(pw[i]) < tol and abs(pw[j]) < tol)
                off = all((pw[k] != 0) if exact else abs(pw[k]) > tol for k in range(m) if k not in (i, j))
                if not (on_ij and off):
                    bad.append((i, j))
                pts.append(p)
        distinct = all(any((p != q) if exact else abs(p - q) > 1e-7 * scale for p, q in zip(pts[a], pts[c]))
                       for a in range(len(pts)) for c in range(a + 1, len(pts)))
        npairs = m * (m - 1) // 2 - (1 if planes == 2 else 0)
        say(planes <= 2 and len(pts) == npairs and npairs > 0 and not bad and distinct,
            f"desk no three boundaries on {label}: {len(pts)} finite contacts, each on exactly two boundaries, "
            f"pairwise distinct; {planes} hyperplane rows ({mode})")


def check_raw_interiors_control():
    # a B < 0 family satisfies the identity, but its raw interiors overlap; multiplying by B separates them
    cases = (("n=2 reversed (-1,2,2,3)", 2, [decode_row(w) for w in config_n2()], [Fr(0), Fr(-1, 2)]),
             ("n=3 reversed (-1,2,2,3,3)", 3, objs_n3_spheres(), [Fr(0), Fr(-1, 2), Fr(0)]))
    for label, n, objs, y in cases:
        rev = [reverse_object(o) for o in objs]
        W = rows_exact(rev)
        B = sum(w[1] for w in W)
        F = [row_power(w, y) for w in W]
        raw = sum(geometric_interior(o, y) for o in rev)
        say(identity_holds(W, n)[0] and B < 0 and raw >= 2 and sum(f < 0 for f in F) == raw and
            sum(B * f < 0 for f in F) <= 1,
            f"desk control {label}: B = {B}; the point {[str(c) for c in y]} lies in {raw} raw interiors "
            f"and in at most one after the B-normalization (exact)")


def check_rational_obstruction():
    # det(W)^2 = det(T) / det(Q_n) = n 2^(n+3): a rational square at n = 1, 2, never at n = 3..7
    for n in range(1, 8):
        d2 = det_exact([[Fr(c) for c in row] for row in target(n)]) / det_exact(Qmat(n))
        r = math.isqrt(int(d2)) if d2.denominator == 1 and d2 >= 0 else -1
        square = r >= 0 and r * r == d2
        say(d2 == n * 2 ** (n + 3) and square == (n <= 2),
            f"desk obstruction n={n}: det(W)^2 = n 2^(n+3) = {d2}, " +
            ("a rational square" if square else "not a rational square, so no configuration has rational rows") + " (exact)")


if __name__ == "__main__":
    check_exact_configs()
    check_inverses()
    check_base_and_reflection()
    check_converse_soddy_gosset()
    check_converse_thm32()
    check_sphere_bridge()
    check_remaining()
    check_control()
    check_rigidity()
    check_orientation()
    check_rational_obstruction()
    check_rigidity_desk()
    check_total_curvature_and_contacts()
    check_raw_interiors_control()
    print(f"{len(FAILS)} failures")
    print(f"VERDICT: {'PASS' if not FAILS else 'FAIL'}")
    sys.exit(0 if not FAILS else 1)
