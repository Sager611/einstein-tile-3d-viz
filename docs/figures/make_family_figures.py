"""Paper-ready figures for the three Lean-proven warp families of Chair44.

Each family is Phi_s(x) = x + s V(x),  V(x) = sum_{R in SO(3,Z)} cos(2 pi k.Rx) R^{-1} e,
with every 0 < s <= 1e-9 a proved, rigid, non-periodic tile, and distinct s non-congruent
(lean/ChairWarp/FamilyFinal.lean, Congruence.lean). Everything drawn here is computed from that
exact formula; only the displacement is magnified (by the factor printed in each figure).

Run:  pip install -r requirements.txt && python3 make_family_figures.py  ->  family-{A,B,C}.{pdf,svg,png},
families-overview.{pdf,svg,png}
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from pathlib import Path

import matplotlib as mpl
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.cm import ScalarMappable
from matplotlib.colors import BoundaryNorm, ListedColormap, TwoSlopeNorm
from matplotlib.lines import Line2D
from mpl_toolkits.mplot3d.art3d import Line3DCollection, Poly3DCollection

OUT = Path(__file__).resolve().parent

mpl.rcParams.update({
    "font.family": "serif",
    "font.serif": ["STIX Two Text", "STIXGeneral", "Times New Roman", "DejaVu Serif"],
    "mathtext.fontset": "stix",
    "font.size": 8.5,
    "axes.linewidth": 0.6,
    "xtick.major.width": 0.6,
    "ytick.major.width": 0.6,
    "savefig.dpi": 300,
    "svg.fonttype": "none",
    "pdf.fonttype": 42,
})

# ---------------------------------------------------------------------------------------------
# Exact field


def rotations() -> np.ndarray:
    """The 24 proper rotations of the cube as 3x3 integer matrices."""
    mats = []
    for perm in itertools.permutations(range(3)):
        for signs in itertools.product((-1, 1), repeat=3):
            m = np.zeros((3, 3), dtype=int)
            for i in range(3):
                m[i, perm[i]] = signs[i]
            if round(np.linalg.det(m)) == 1:
                mats.append(m)
    if len(mats) != 24:
        raise RuntimeError(f"expected 24 rotations, got {len(mats)}")
    return np.array(mats)


R24 = rotations()


@dataclass(frozen=True)
class Family:
    name: str
    k: tuple[float, float, float]
    e: tuple[int, int, int]
    max_scale: float  # displayed scale at full magnification (same as the web explorer)
    cert: tuple[float, float, float]
    theorem: str

    def field(self, x: np.ndarray) -> np.ndarray:
        """V(x) for points x of shape (..., 3)."""
        k = np.array(self.k)
        e = np.array(self.e, dtype=float)
        out = np.zeros_like(x, dtype=float)
        for r in R24:
            phase = 2 * np.pi * (x @ r.T) @ k
            out += np.cos(phase)[..., None] * (r.T @ e)  # R^{-1} = R^T
        return out

    @property
    def magnification(self) -> float:
        return self.max_scale / 1e-9


FAMILIES = [
    Family("A", (1, 0.5, 0.5), (1, 1, 0), 0.8 / 36, (0.75, 0.5, 0.0), "familyA"),
    Family("B", (0, 2, 1), (1, 0, 0), 0.8 / 96, (0.125, 0.25, 0.0), "familyB"),
    Family("C", (1.5, 1.5, 1), (1, 0, 0), 0.8 / 72, (0.25, 0.5, 0.0), "familyC"),
]

CELLS = [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0)]
CORNERS = np.array([[0, 0, 0], [2, 0, 0], [0, 2, 0], [0, 0, 2]], dtype=float)

def check_families() -> None:
    """Exact certificate values (Lean `famX_cert`) and fixed grid points (Lean `equivariant_fixes_grid`)."""
    grid = np.array(list(itertools.product(range(-1, 3), repeat=3)), dtype=float)
    for fam in FAMILIES:
        v = fam.field(np.array(fam.cert))
        if not np.allclose(v, [0, 0, -4], atol=1e-12):
            raise RuntimeError(f"family {fam.name}: certificate value {v} != (0, 0, -4)")
        if np.abs(fam.field(grid)).max() >= 1e-12:
            raise RuntimeError(f"family {fam.name}: field does not vanish on the integer grid")


check_families()

CMAP = mpl.colormaps["RdBu_r"]
RED = "#c81e1e"
INK = "#111827"

# ---------------------------------------------------------------------------------------------
# Geometry


def panels(n: int):
    """Exterior unit panels of the Chair44 carrier: (origin, du, dv, outward normal)."""
    cells = set(CELLS)
    for c in CELLS:
        for axis in range(3):
            for sign in (1, -1):
                nb = list(c)
                nb[axis] += sign
                if tuple(nb) in cells:
                    continue
                a, b = [i for i in range(3) if i != axis]
                o = np.array(c, dtype=float)
                o[axis] += 1 if sign > 0 else 0
                du = np.zeros(3); du[a] = 1
                dv = np.zeros(3); dv[b] = 1
                nrm = np.zeros(3); nrm[axis] = sign
                yield o, du, dv, nrm


def warped_quads(fam: Family, scale: float, n: int = 28):
    """Warped surface quads plus the signed normal displacement at each quad centre."""
    quads, heights = [], []
    t = np.linspace(0, 1, n + 1)
    for o, du, dv, nrm in panels(n):
        uu, vv = np.meshgrid(t, t, indexing="ij")
        p = o + uu[..., None] * du + vv[..., None] * dv
        q = p + scale * fam.field(p)
        tc = (t[:-1] + t[1:]) / 2
        cu, cv = np.meshgrid(tc, tc, indexing="ij")
        centre = o + cu[..., None] * du + cv[..., None] * dv
        h = fam.field(centre) @ nrm
        for i in range(n):
            for j in range(n):
                quads.append([q[i, j], q[i + 1, j], q[i + 1, j + 1], q[i, j + 1]])
                heights.append(h[i, j])
    return np.array(quads), np.array(heights)


def carrier_edges():
    """Edges of the flat Chair44 carrier (boundary edges of exterior panels, deduplicated)."""
    count: dict[tuple, int] = {}
    normals: dict[tuple, set] = {}
    for o, du, dv, nrm in panels(1):
        corners = [o, o + du, o + du + dv, o + dv]
        for i in range(4):
            a, b = tuple(corners[i]), tuple(corners[(i + 1) % 4])
            key = tuple(sorted((a, b)))
            count[key] = count.get(key, 0) + 1
            normals.setdefault(key, set()).add(tuple(nrm))
    # keep edges where the surface folds (two different normals) or the panel boundary is open
    return [np.array(k) for k, ns in normals.items() if len(ns) > 1]


# ---------------------------------------------------------------------------------------------
# Panels


def draw_face(ax, fam: Family, norm):
    n = 241
    t = np.linspace(0, 1, n)
    xx, yy = np.meshgrid(t, t, indexing="xy")
    p = np.stack([xx, yy, np.zeros_like(xx)], axis=-1)
    v = fam.field(p)
    ax.imshow(-v[..., 2], origin="lower", extent=(0, 1, 0, 1), cmap=CMAP, norm=norm, interpolation="bilinear")
    ax.contour(xx, yy, -v[..., 2], levels=[0], colors=INK, linewidths=0.4, alpha=0.55)
    ax.scatter([0, 1, 1, 0], [0, 0, 1, 1], s=26, c=INK, edgecolors="white", linewidths=0.9, zorder=5, clip_on=False)
    cx, cy, _ = fam.cert
    ax.scatter([cx], [cy], s=48, marker="o", facecolors="none", edgecolors=RED, linewidths=1.3, zorder=6)
    ax.scatter([cx], [cy], s=9, c=RED, zorder=7)
    ax.annotate(r"$V=(0,0,-4)$", (cx, cy), xytext=(8, 8), textcoords="offset points", color=RED, fontsize=7.5,
                bbox=dict(boxstyle="round,pad=0.15", fc="white", ec="none", alpha=0.85))
    ax.set_xlim(0, 1); ax.set_ylim(0, 1)
    ax.set_xticks([0, 0.5, 1]); ax.set_yticks([0, 0.5, 1])
    ax.set_xlabel(r"$x$", labelpad=1); ax.set_ylabel(r"$y$", labelpad=1)
    ax.set_aspect("equal")
    ax.tick_params(length=2, pad=1.5)


def draw_tile(ax, fam: Family, norm, scale: float, n: int = 26):
    ax.computed_zorder = False  # surface, then ghost, then markers on top (as in the web explorer)
    quads, heights = warped_quads(fam, scale, n)
    # outward displacement colour, Lambert-shaded
    nrm = np.cross(quads[:, 1] - quads[:, 0], quads[:, 3] - quads[:, 0])
    nrm /= np.linalg.norm(nrm, axis=1, keepdims=True)
    light = np.array([0.35, -0.55, 0.76]); light /= np.linalg.norm(light)
    shade = 0.55 + 0.45 * np.clip(np.abs(nrm @ light), 0, 1)
    rgba = CMAP(norm(heights))
    rgba[:, :3] *= shade[:, None]
    coll = Poly3DCollection(quads, facecolors=rgba, edgecolors=rgba, linewidths=0.12)
    coll.set_zorder(1)
    ax.add_collection3d(coll)
    ghost = Line3DCollection(carrier_edges(), colors=INK, linewidths=0.55, linestyles=(0, (2.2, 1.6)), alpha=0.5)
    ghost.set_zorder(2)
    ax.add_collection3d(ghost)
    ax.scatter(*CORNERS.T, s=22, c=INK, edgecolors="white", linewidths=0.8, depthshade=False, zorder=10)
    base = np.array(fam.cert)
    tip = base + scale * fam.field(base)
    ax.plot(*np.stack([base, tip]).T, color=RED, linewidth=1.4, zorder=11)
    ax.scatter(*tip, s=16, c=RED, depthshade=False, zorder=12)
    ax.scatter(*base, s=16, c="white", edgecolors=RED, linewidths=0.9, depthshade=False, zorder=12)
    ax.scatter(*base, s=150, facecolors="none", edgecolors=RED, linewidths=1.0, depthshade=False, zorder=12)
    ax.view_init(elev=-24, azim=38)
    lim = (-0.12, 2.12)
    ax.set_xlim(lim); ax.set_ylim(lim); ax.set_zlim(lim)
    ax.set_box_aspect((1, 1, 1), zoom=1.28)
    ax.set_axis_off()


def draw_profile(ax, fam: Family, scale_full: float):
    """Section of the bottom face y = cert_y, z = 0 (two unit cells, x in [0,2])."""
    x = np.linspace(0, 2, 801)
    y0 = fam.cert[1]
    p = np.stack([x, np.full_like(x, y0), np.zeros_like(x)], axis=-1)
    v = fam.field(p)
    amps = [0.25, 0.5, 0.75, 1.0]
    cols = mpl.colormaps["Greys"](np.linspace(0.45, 0.95, len(amps)))
    ax.axhline(0, color=INK, lw=0.8, ls=(0, (3, 2)))
    for a, c in zip(amps, cols):
        q = p + a * scale_full * v
        ax.plot(q[:, 0], q[:, 2], color=c, lw=1.0)
        cx = fam.cert[0]
        ax.scatter([cx + 0], [-4 * a * scale_full], s=10, c=RED, zorder=5)
    ax.fill_between([0, 2], [0, 0], [0.25, 0.25], color="#e5e7eb", alpha=0.6, lw=0)
    ax.text(1.0, 0.13, "Chair44", ha="center", va="center", fontsize=7, color="#4b5563")
    ax.set_xlim(0, 2)
    top = 0.25
    bottom = -1.3 * 4 * scale_full
    ax.set_ylim(bottom, top)
    ax.set_xticks([0, 1, 2])
    ax.set_yticks([])
    ax.set_xlabel(r"$x$", labelpad=1)
    ax.spines[["top", "right", "left"]].set_visible(False)
    ax.tick_params(length=2, pad=1.5)
    sm = ScalarMappable(cmap=ListedColormap(cols), norm=BoundaryNorm([0.125, 0.375, 0.625, 0.875, 1.125], len(amps)))
    return sm, amps


# ---------------------------------------------------------------------------------------------


def frac_str(v: float) -> str:
    """Integer or half-integer as TeX."""
    if v % 1 == 0:
        return f"{v:.0f}"
    return rf"\frac{{{2 * v:.0f}}}{{2}}"


def sci_tex(value: float) -> str:
    """2.2e7 -> 2.2\\cdot10^{7}."""
    exponent = np.floor(np.log10(value))
    mantissa = value / 10.0 ** exponent
    return rf"{mantissa:.1f}\cdot10^{{{exponent:.0f}}}"


def k_str(k: tuple[float, float, float]) -> str:
    return "(" + ",".join(frac_str(v) for v in k) + ")"


def family_figure(fam: Family):
    vmax = 8.0
    norm = TwoSlopeNorm(vmin=-vmax, vcenter=0, vmax=vmax)
    fig = plt.figure(figsize=(7.0, 2.95))
    gs = fig.add_gridspec(1, 3, width_ratios=[1, 1.35, 1.1], wspace=0.22, left=0.05, right=0.985, top=0.80, bottom=0.27)
    ax_a = fig.add_subplot(gs[0])
    ax_b = fig.add_subplot(gs[1], projection="3d")
    ax_c = fig.add_subplot(gs[2])
    draw_face(ax_a, fam, norm)
    draw_tile(ax_b, fam, norm, fam.max_scale)
    sm, amps = draw_profile(ax_c, fam, fam.max_scale)

    fig.suptitle(
        rf"Family {fam.name}:  $\Phi_s(x)=x+s\sum_{{R\in\mathrm{{SO}}(3,\mathbb{{Z}})}}\cos(2\pi\,k\cdot Rx)\,R^{{-1}}e$,"
        rf"  $k={k_str(fam.k)}$,  $e=({','.join(map(str, fam.e))})$,  $0<s\leq10^{{-9}}$",
        fontsize=9, y=0.975,
    )
    for ax, label in ((ax_a, "a"), (ax_c, "c")):
        ax.text(-0.2, 1.035, rf"$\mathbf{{({label})}}$", transform=ax.transAxes, fontsize=9, ha="left", va="bottom")
    ax_b.text2D(-0.06, 1.03, r"$\mathbf{(b)}$", transform=ax_b.transAxes, fontsize=9, va="bottom")
    ax_a.set_title(r"face $z=0$:  $V=(V\cdot n)\,n$", fontsize=8, pad=3)
    ax_b.text2D(0.55, 1.03, rf"$\Phi_s(Q)$, displacement $\times{sci_tex(fam.magnification)}$",
                transform=ax_b.transAxes, ha="center", va="bottom", fontsize=8)
    ax_c.set_title(rf"section $y={fam.cert[1]:g}$, $z=0$: one tile per $s$", fontsize=8, pad=3)

    cax = fig.add_axes((0.08, 0.125, 0.22, 0.022))
    cb = fig.colorbar(ScalarMappable(norm=norm, cmap=CMAP), cax=cax, orientation="horizontal")
    cb.set_ticks([-8, 0, 8]); cb.set_ticklabels(["in", "0", "out"])
    cb.ax.tick_params(length=1.5, pad=1, labelsize=7); cb.outline.set_linewidth(0.4)
    lax = fig.add_axes((0.68, 0.125, 0.22, 0.022))
    lb = fig.colorbar(sm, cax=lax, orientation="horizontal")
    lb.set_ticks([0.25, 0.5, 0.75, 1.0]); lb.set_ticklabels([r"$\frac{1}{4}$", r"$\frac{1}{2}$", r"$\frac{3}{4}$", "1"])
    lb.ax.tick_params(length=1.5, pad=1, labelsize=7); lb.outline.set_linewidth(0.4)
    lax.text(1.04, 0.5, r"$s/10^{-9}$", transform=lax.transAxes, va="center", fontsize=7)

    # legend for markers (shared symbols)
    handles = [
        Line2D([], [], ls="none", marker="o", ms=4.5, mfc=INK, mec="white", label="fixed corners"),
        Line2D([], [], ls="none", marker="o", ms=4, mfc=RED, mec=RED, label=r"certificate: pushed out by $4s$"),
        Line2D([], [], color=INK, lw=0.8, ls=(0, (3, 2)), label=r"Chair44 ($s=0$)"),
    ]
    fig.legend(handles=handles, loc="lower center", bbox_to_anchor=(0.5, 0.0), ncol=3, frameon=False, fontsize=7,
               handletextpad=0.3, columnspacing=1.2)
    for ext in ("pdf", "svg", "png"):
        fig.savefig(OUT / f"family-{fam.name}.{ext}")
    plt.close(fig)


def overview_figure():
    vmax = 8.0
    norm = TwoSlopeNorm(vmin=-vmax, vcenter=0, vmax=vmax)
    fig = plt.figure(figsize=(7.0, 2.6))
    for i, fam in enumerate(FAMILIES):
        ax = fig.add_subplot(1, 3, i + 1, projection="3d")
        draw_tile(ax, fam, norm, fam.max_scale)
        ax.text2D(0.5, 0.98, rf"$\mathbf{{{fam.name}}}$:  $k={k_str(fam.k)}$, $e=({','.join(map(str, fam.e))})$",
                  transform=ax.transAxes, ha="center", fontsize=8.5)
    fig.subplots_adjust(left=0.0, right=1.0, top=0.95, bottom=0.08, wspace=0.0)
    cax = fig.add_axes((0.38, 0.06, 0.24, 0.025))
    cb = fig.colorbar(ScalarMappable(norm=norm, cmap=CMAP), cax=cax, orientation="horizontal")
    cb.set_ticks([-8, 0, 8]); cb.set_ticklabels(["in", "0", "out"])
    cb.ax.tick_params(length=1.5, pad=1, labelsize=7); cb.outline.set_linewidth(0.4)
    for ext in ("pdf", "svg", "png"):
        fig.savefig(OUT / f"families-overview.{ext}")
    plt.close(fig)


if __name__ == "__main__":
    for fam in FAMILIES:
        family_figure(fam)
    overview_figure()
    print("wrote", sorted(p.name for p in OUT.glob("famil*")))
