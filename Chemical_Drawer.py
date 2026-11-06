#!/usr/bin/env python3
"""
Skeletal - a lightweight ChemDraw-style 2D chemical structure editor.

Pure Python 3 + tkinter (standard library only, no extra packages).

Drawing style: "ACS Document 1996" with the line width doubled
    Chain angle      120 deg
    Bond spacing     18 % of bond length
    Fixed length     0.508 cm  (14.4 pt)
    Bold width       0.071 cm  (2.0 pt)
    Line width       0.021 cm  (0.6 pt)  x 2  ->  1.2 pt
    Margin width     0.056 cm  (1.6 pt)
    Hash spacing     0.088 cm  (2.5 pt)
    Atom labels      Arial 10 pt
    Captions         Arial 10 pt

All geometry is stored in points (1/72 inch), so exported SVG is true size
and can be dropped straight into a manuscript at 100 %.

Run:   python skeletal.py [drawing.json]

Mouse
    Left click / drag      use the current tool
    Right or middle drag   pan
    Wheel                  scroll (Shift+wheel: horizontal, Ctrl+wheel: zoom)

Hotkeys while hovering an atom (any tool)
    C N O S P F H I        set element      L -> Cl     B -> Br
    + / -                  change charge
Hotkeys while hovering a bond
    1 2 3                  set bond order
Del / Backspace            delete hovered object (or the selection)
"""

import json
import math
import re
import sys
from collections import deque

import tkinter as tk
import tkinter.font as tkfont
from tkinter import filedialog, messagebox, simpledialog

APP_NAME = "ChemDraw"


# --------------------------------------------------------------------------
# Style: ACS Document 1996, double line width.  All lengths in points.
# --------------------------------------------------------------------------
class Style:
    NAME = "ACS Document 1996 (double line width)"
    LINE_MULTIPLIER = 2.0
    BOND_LENGTH = 14.4              # 0.508 cm
    CHAIN_ANGLE = 120.0             # degrees
    BOND_SPACING = 0.18             # fraction of bond length
    LINE_WIDTH = 0.6 * LINE_MULTIPLIER   # 0.021 cm, doubled -> 1.2 pt
    BOLD_WIDTH = 2.0                # 0.071 cm
    MARGIN = 1.6                    # 0.056 cm  (gap between label and bond)
    HASH_SPACING = 2.5              # 0.088 cm
    WEDGE_WIDTH = 1.5 * BOLD_WIDTH  # width of the wide end of a wedge
    FONT = "Arial"
    FONT_SIZE = 10.0
    CAPTION_SIZE = 10.0
    SUB_SCALE = 0.75                # subscript / superscript size
    SUB_DROP = 0.25                 # subscript baseline shift (x font size)
    SUP_RISE = 0.42                 # superscript baseline shift
    CAP_HEIGHT = 0.716              # Arial cap height (x font size)
    ARROW_HEAD_LEN = 7.2
    ARROW_HEAD_WIDTH = 4.8
    ANGLE_SNAP = 15.0               # degrees, like ChemDraw "fixed angles"


S = Style


# --------------------------------------------------------------------------
# Chemistry data
# --------------------------------------------------------------------------
VALENCE = {
    "H": (1,), "B": (3,), "C": (4,), "N": (3, 5), "O": (2,), "F": (1,),
    "Si": (4,), "P": (3, 5), "S": (2, 4, 6), "Cl": (1,), "Br": (1,),
    "I": (1,), "Se": (2, 4, 6), "Li": (1,), "Na": (1,), "K": (1,), "Mg": (2,),
}
GROUP_15_16 = {"N", "P", "O", "S", "Se"}

MASS = {
    "H": 1.008, "Li": 6.94, "B": 10.81, "C": 12.011, "N": 14.007,
    "O": 15.999, "F": 18.998, "Na": 22.990, "Mg": 24.305, "Al": 26.982,
    "Si": 28.085, "P": 30.974, "S": 32.06, "Cl": 35.45, "K": 39.098,
    "Ca": 40.078, "Fe": 55.845, "Cu": 63.546, "Zn": 65.38, "Se": 78.971,
    "Br": 79.904, "Pd": 106.42, "Sn": 118.71, "I": 126.904, "Pt": 195.08,
}

ABBREVIATIONS = {
    "Me": {"C": 1, "H": 3}, "Et": {"C": 2, "H": 5}, "Pr": {"C": 3, "H": 7},
    "iPr": {"C": 3, "H": 7}, "Bu": {"C": 4, "H": 9}, "nBu": {"C": 4, "H": 9},
    "tBu": {"C": 4, "H": 9}, "Ph": {"C": 6, "H": 5}, "Bn": {"C": 7, "H": 7},
    "Ac": {"C": 2, "H": 3, "O": 1}, "Bz": {"C": 7, "H": 5, "O": 1},
    "Boc": {"C": 5, "H": 9, "O": 2}, "Cbz": {"C": 8, "H": 7, "O": 2},
    "Ts": {"C": 7, "H": 7, "O": 2, "S": 1}, "Ms": {"C": 1, "H": 3, "O": 2, "S": 1},
    "Tf": {"C": 1, "F": 3, "O": 2, "S": 1}, "TMS": {"C": 3, "H": 9, "Si": 1},
    "TBS": {"C": 6, "H": 15, "Si": 1}, "Piv": {"C": 5, "H": 9, "O": 1},
    "Cy": {"C": 6, "H": 11},
}
_LABEL_TOKEN = re.compile(
    "(" + "|".join(sorted(ABBREVIATIONS, key=len, reverse=True))
    + r"|[A-Z][a-z]?)(\d*)")

ELEMENT_HOTKEYS = {"c": "C", "n": "N", "o": "O", "s": "S", "p": "P",
                   "f": "F", "l": "Cl", "b": "Br", "i": "I", "h": "H"}


def implicit_h(el, bond_sum, charge):
    vals = VALENCE.get(el)
    if not vals:
        return 0
    for v in vals:
        if el in GROUP_15_16:
            target = v + charge
        elif el == "B":
            target = v - charge
        else:
            target = v - abs(charge)
        if target >= bond_sum:
            return target - bond_sum
    return 0


def charge_text(ch):
    if not ch:
        return ""
    sign = "+" if ch > 0 else "−"
    return sign if abs(ch) == 1 else f"{abs(ch)}{sign}"


def label_formula(label):
    """Parse a text label such as 'CO2Et' or 'NHBoc' into element counts."""
    counts, pos, label = {}, 0, label.strip()
    while pos < len(label):
        m = _LABEL_TOKEN.match(label, pos)
        if not m:
            return None
        tok, num = m.group(1), m.group(2)
        n = int(num) if num else 1
        if tok in ABBREVIATIONS:
            frag = ABBREVIATIONS[tok]
        elif tok in MASS:
            frag = {tok: 1}
        else:
            return None
        for k, v in frag.items():
            counts[k] = counts.get(k, 0) + v * n
        pos = m.end()
    return counts


def hill_formula(counts):
    sub = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")
    keys = sorted(k for k, v in counts.items() if v > 0)
    if "C" in keys:
        order = ["C"] + (["H"] if "H" in keys else []) + [k for k in keys if k not in ("C", "H")]
    else:
        order = keys
    return "".join(k + (str(counts[k]).translate(sub) if counts[k] > 1 else "") for k in order)


# --------------------------------------------------------------------------
# Geometry helpers
# --------------------------------------------------------------------------
def snap_dir(dx, dy, step=S.ANGLE_SNAP):
    ang = round(math.degrees(math.atan2(dy, dx)) / step) * step
    r = math.radians(ang)
    return math.cos(r), math.sin(r)


def dist_seg(px, py, x1, y1, x2, y2):
    dx, dy = x2 - x1, y2 - y1
    l2 = dx * dx + dy * dy
    if l2 < 1e-12:
        return math.hypot(px - x1, py - y1)
    t = max(0.0, min(1.0, ((px - x1) * dx + (py - y1) * dy) / l2))
    return math.hypot(px - x1 - t * dx, py - y1 - t * dy)


def _box_interval(p, q, box):
    """Liang-Barsky: parameter interval of segment p->q inside box."""
    x0, y0, x1, y1 = box
    dx, dy = q[0] - p[0], q[1] - p[1]
    t0, t1 = 0.0, 1.0
    for pk, qk in ((-dx, p[0] - x0), (dx, x1 - p[0]), (-dy, p[1] - y0), (dy, y1 - p[1])):
        if abs(pk) < 1e-12:
            if qk < 0:
                return None
        else:
            r = qk / pk
            if pk < 0:
                t0 = max(t0, r)
            else:
                t1 = min(t1, r)
    return (t0, t1) if t0 <= t1 else None


def clip_segment(p, q, box_a, box_b):
    """Trim segment so it starts outside box_a (around p) and ends outside box_b."""
    ta, tb = 0.0, 1.0
    if box_a:     # offset lines may start just outside the label box: clip any crossing
        iv = _box_interval(p, q, box_a)
        if iv and iv[0] < 0.5:
            ta = iv[1]
    if box_b:
        iv = _box_interval(p, q, box_b)
        if iv and iv[1] > 0.5:
            tb = iv[0]
    if tb - ta < 1e-6:
        return None
    dx, dy = q[0] - p[0], q[1] - p[1]
    return (p[0] + dx * ta, p[1] + dy * ta), (p[0] + dx * tb, p[1] + dy * tb)


def smallest_ring(adj, a, b, maxlen=8):
    """Atoms of the smallest ring containing bond a-b (None if acyclic)."""
    prev, dist = {b: None}, {b: 1}
    q = deque([b])
    while q:
        u = q.popleft()
        if u == a:
            break
        if dist[u] >= maxlen:
            continue
        for v, _ in adj[u]:
            if u == b and v == a:
                continue
            if v not in prev:
                prev[v], dist[v] = u, dist[u] + 1
                q.append(v)
    if a not in prev:
        return None
    path, u = [], a
    while u is not None:
        path.append(u)
        u = prev[u]
    return path


# --------------------------------------------------------------------------
# Document model
# --------------------------------------------------------------------------
class Doc:
    def __init__(self):
        self.clear()

    def clear(self):
        self.atoms, self.bonds, self.texts, self.arrows = {}, {}, {}, {}
        self.nid = 1

    def _id(self):
        i = self.nid
        self.nid += 1
        return i

    def add_atom(self, x, y, el="C"):
        i = self._id()
        self.atoms[i] = {"x": x, "y": y, "el": el, "charge": 0, "label": None}
        return i

    def add_bond(self, a, b, order=1, stereo=None):
        if a == b:
            return None
        existing = self.bond_between(a, b)
        if existing:
            return existing
        i = self._id()
        self.bonds[i] = {"a": a, "b": b, "order": order, "stereo": stereo, "pos": "auto"}
        return i

    def add_text(self, x, y, s):
        i = self._id()
        self.texts[i] = {"x": x, "y": y, "s": s}
        return i

    def add_arrow(self, x1, y1, x2, y2):
        i = self._id()
        self.arrows[i] = {"x1": x1, "y1": y1, "x2": x2, "y2": y2}
        return i

    def bond_between(self, a, b):
        for i, bd in self.bonds.items():
            if (bd["a"] == a and bd["b"] == b) or (bd["a"] == b and bd["b"] == a):
                return i
        return None

    def adjacency(self):
        adj = {i: [] for i in self.atoms}
        for i, b in self.bonds.items():
            adj[b["a"]].append((b["b"], i))
            adj[b["b"]].append((b["a"], i))
        return adj

    def degree(self, a):
        return sum(1 for b in self.bonds.values() if a in (b["a"], b["b"]))

    def bond_sum(self, a, adj):
        return sum(self.bonds[bid]["order"] for _, bid in adj[a])

    def delete_atom(self, a):
        for i in [i for i, b in self.bonds.items() if a in (b["a"], b["b"])]:
            del self.bonds[i]
        self.atoms.pop(a, None)

    def delete_bond(self, i):
        b = self.bonds.pop(i, None)
        if not b:
            return
        for a in (b["a"], b["b"]):          # drop orphaned plain carbons
            at = self.atoms.get(a)
            if at and at["el"] == "C" and not at["label"] and not at["charge"] \
                    and self.degree(a) == 0:
                del self.atoms[a]

    def dumps(self):
        return json.dumps({"format": "skeletal", "version": 1, "style": S.NAME,
                           "nid": self.nid, "atoms": self.atoms, "bonds": self.bonds,
                           "texts": self.texts, "arrows": self.arrows}, sort_keys=True)

    def loads(self, s):
        d = json.loads(s)
        conv = lambda m: {int(k): v for k, v in (m or {}).items()}
        self.atoms, self.bonds = conv(d.get("atoms")), conv(d.get("bonds"))
        self.texts, self.arrows = conv(d.get("texts")), conv(d.get("arrows"))
        ids = list(self.atoms) + list(self.bonds) + list(self.texts) + list(self.arrows)
        self.nid = max([d.get("nid", 1)] + [i + 1 for i in ids])


# --------------------------------------------------------------------------
# Rendering: document -> device independent primitives (points)
#   ("line", x1, y1, x2, y2, width, cap)
#   ("poly", [(x, y), ...])                filled black
#   ("polyline", [(x, y), ...], width)
#   ("text", x, baseline_y, string, size)
# --------------------------------------------------------------------------
class Measurer:
    REF = 200  # measure at 200 px for precision, then scale

    def __init__(self, root):
        self.font = tkfont.Font(root=root, family=S.FONT, size=-self.REF)
        self.cache = {}

    def width(self, s, size):
        w = self.cache.get(s)
        if w is None:
            w = self.cache[s] = self.font.measure(s)
        return w * size / self.REF


class Renderer:
    def __init__(self, measurer):
        self.M = measurer

    def build(self, doc):
        adj = doc.adjacency()
        prims, boxes = [], {}
        for aid in doc.atoms:
            runs, box = self.atom_label(doc, aid, adj)
            prims.extend(runs)
            if box:
                boxes[aid] = (box[0] - S.MARGIN, box[1] - S.MARGIN,
                              box[2] + S.MARGIN, box[3] + S.MARGIN)
        for bid in doc.bonds:
            prims.extend(self.bond(doc, bid, adj, boxes))
        for t in doc.texts.values():
            prims.append(("text", t["x"], t["y"], t["s"], S.CAPTION_SIZE))
        for ar in doc.arrows.values():
            prims.extend(self.arrow(ar))
        return prims

    # ---- atom labels --------------------------------------------------
    def atom_label(self, doc, aid, adj):
        a = doc.atoms[aid]
        el, ch, lab = a["el"], a.get("charge", 0) or 0, a.get("label")
        nbs = adj[aid]
        fs, ss = S.FONT_SIZE, S.FONT_SIZE * S.SUB_SCALE
        sx = sum(doc.atoms[n]["x"] - a["x"] for n, _ in nbs)
        bonds_right = bool(nbs) and sx > 0.05 * S.BOND_LENGTH

        if lab:
            # split into groups ("O", "Me", "CO2" -> "C", "O2") so the label can
            # be mirrored when the bond arrives from the right: OMe -> MeO,
            # CO2Et -> EtO2C, NHBoc -> BocHN, CF3 -> F3C (as ChemDraw does)
            tokens = re.findall(r"[a-z]?[A-Z][a-z]*\d*|.", lab)
            if bonds_right and len(tokens) > 1:
                tokens = tokens[::-1]
                attach = len(tokens) - 1
            else:
                attach = 0
            chars, anchor = [], 0
            for ti, tok in enumerate(tokens):
                if ti == attach:
                    caps = [j for j, c in enumerate(tok) if c.isupper()]
                    anchor = len(chars) + (caps[0] if caps else 0)
                chars += [(c, "sub" if c.isdigit() else "n") for c in tok]
            span = (anchor, anchor + 1)
        elif el != "C" or not nbs:
            h = implicit_h(el, doc.bond_sum(aid, adj), ch)
            hs = ([("H", "n")] + ([(str(h), "sub")] if h > 1 else [])) if h else []
            if bonds_right and hs:
                chars, span = hs + [(el, "n")], (len(hs), len(hs) + 1)
            else:
                chars, span = [(el, "n")] + hs, (0, 1)
        else:
            if ch:   # charged, unlabelled carbon: small charge sign beside the vertex
                o = 0.22 * S.BOND_LENGTH
                return [("text", a["x"] + 0.4 * o, a["y"] - o, charge_text(ch), ss)], None
            return [], None

        if ch:
            chars.append((charge_text(ch), "sup"))

        base = a["y"] + S.CAP_HEIGHT * fs / 2
        x, laid = 0.0, []
        for s, k in chars:
            size = fs if k == "n" else ss
            w = self.M.width(s, size)
            laid.append((x, s, size, k, w))
            x += w
        i0, i1 = span
        cx = (laid[i0][0] + laid[i1 - 1][0] + laid[i1 - 1][4]) / 2
        shift = a["x"] - cx

        runs = []
        for x0, s, size, k, _ in laid:
            if runs and runs[-1][3] == k:
                runs[-1][1] += s
            else:
                runs.append([x0 + shift, s, size, k])
        prims, has_sub, has_sup = [], False, False
        for x0, s, size, k in runs:
            if k == "sub":
                y, has_sub = base + S.SUB_DROP * fs, True
            elif k == "sup":
                y, has_sup = base - S.SUP_RISE * fs, True
            else:
                y = base
            prims.append(("text", x0, y, s, size))
        y0 = base - S.CAP_HEIGHT * fs
        if has_sup:
            y0 = min(y0, base - S.SUP_RISE * fs - S.CAP_HEIGHT * ss)
        y1 = base + (S.SUB_DROP * fs if has_sub else 0.0)
        return prims, (shift, y0, shift + x, y1)

    # ---- bonds ----------------------------------------------------------
    def bond(self, doc, bid, adj, boxes):
        b = doc.bonds[bid]
        ia, ib = b["a"], b["b"]
        A, B = doc.atoms[ia], doc.atoms[ib]
        p, q = (A["x"], A["y"]), (B["x"], B["y"])
        dx, dy = q[0] - p[0], q[1] - p[1]
        L = math.hypot(dx, dy)
        if L < 1e-6:
            return []
        ux, uy = dx / L, dy / L
        nx, ny = -uy, ux
        box_a, box_b = boxes.get(ia), boxes.get(ib)
        lw = S.LINE_WIDTH
        out = []

        def line(p1, q1, w=lw, cap="round"):
            seg = clip_segment(p1, q1, box_a, box_b)
            if seg:
                (x1, y1), (x2, y2) = seg
                out.append(("line", x1, y1, x2, y2, w, cap))

        order, stereo = b["order"], b.get("stereo")
        if order == 1 and stereo in ("wedge", "hash", "bold", "wavy"):
            seg = clip_segment(p, q, box_a, box_b)
            if not seg:
                return out
            (x1, y1), (x2, y2) = seg
            sl = math.hypot(x2 - x1, y2 - y1)
            hw = S.WEDGE_WIDTH / 2
            if stereo == "wedge":
                out.append(("poly", [(x1, y1), (x2 + nx * hw, y2 + ny * hw),
                                     (x2 - nx * hw, y2 - ny * hw)]))
            elif stereo == "hash":
                n = max(2, int(sl / S.HASH_SPACING))
                for i in range(1, n + 1):
                    t = i / n
                    cx, cy = x1 + (x2 - x1) * t, y1 + (y2 - y1) * t
                    h = max(hw * t, lw / 2)
                    out.append(("line", cx - nx * h, cy - ny * h, cx + nx * h, cy + ny * h, lw, "butt"))
            elif stereo == "bold":
                out.append(("line", x1, y1, x2, y2, S.BOLD_WIDTH, "round"))
            else:  # wavy
                amp = 0.09 * S.BOND_LENGTH
                periods = max(2, round(sl / (0.28 * S.BOND_LENGTH)))
                steps = periods * 16
                pts = []
                for i in range(steps + 1):
                    t = i / steps
                    off = amp * math.sin(2 * math.pi * periods * t)
                    pts.append((x1 + (x2 - x1) * t + nx * off, y1 + (y2 - y1) * t + ny * off))
                out.append(("polyline", pts, lw))
            return out

        s = S.BOND_LENGTH * S.BOND_SPACING
        if order == 2:
            side = {"center": 0, "plus": 1, "minus": -1}.get(b.get("pos", "auto"))
            if side is None:
                side = self.auto_side(doc, ia, ib, adj, boxes, p, (nx, ny))
            if side == 0:       # centred double bond
                o = s / 2
                for sg in (1, -1):
                    m = (nx * sg, ny * sg)
                    ta = 0.0 if box_a else self.trim(doc, adj, ia, ib, (ux, uy), m, o)
                    tb = 0.0 if box_b else self.trim(doc, adj, ib, ia, (-ux, -uy), m, o)
                    line((p[0] + m[0] * o + ux * ta, p[1] + m[1] * o + uy * ta),
                         (q[0] + m[0] * o - ux * tb, q[1] + m[1] * o - uy * tb))
            else:               # offset double bond (ring / chain)
                line(p, q)
                m = (nx * side, ny * side)
                ta = self.trim(doc, adj, ia, ib, (ux, uy), m, s)
                tb = self.trim(doc, adj, ib, ia, (-ux, -uy), m, s)
                p2 = (p[0] + m[0] * s + ux * ta, p[1] + m[1] * s + uy * ta)
                q2 = (q[0] + m[0] * s - ux * tb, q[1] + m[1] * s - uy * tb)
                if (q2[0] - p2[0]) * ux + (q2[1] - p2[1]) * uy > 0.5:
                    line(p2, q2)
        elif order == 3:
            line(p, q)
            for sg in (1, -1):
                line((p[0] + nx * s * sg, p[1] + ny * s * sg), (q[0] + nx * s * sg, q[1] + ny * s * sg))
        else:
            line(p, q)
        return out

    def auto_side(self, doc, ia, ib, adj, boxes, p, n):
        # double bond to a terminal labelled atom (C=O, C=N, C=S): centred
        for x in (ia, ib):
            if len(adj[x]) == 1 and x in boxes:
                return 0
        ring = smallest_ring(adj, ia, ib)
        if ring:
            cx = sum(doc.atoms[i]["x"] for i in ring) / len(ring)
            cy = sum(doc.atoms[i]["y"] for i in ring) / len(ring)
            v = (cx - p[0]) * n[0] + (cy - p[1]) * n[1]
            if abs(v) > 1e-6:
                return 1 if v > 0 else -1
        score = 0
        for x, o in ((ia, ib), (ib, ia)):
            X = doc.atoms[x]
            for nb, _ in adj[x]:
                if nb == o:
                    continue
                v = (doc.atoms[nb]["x"] - X["x"]) * n[0] + (doc.atoms[nb]["y"] - X["y"]) * n[1]
                score += (v > 1e-6) - (v < -1e-6)
        return (score > 0) - (score < 0)

    def trim(self, doc, adj, x, other, d, m, off):
        """How far to shorten an offset line so it meets the neighbouring bond."""
        X, best = doc.atoms[x], None
        for nb, _ in adj[x]:
            if nb == other:
                continue
            vx, vy = doc.atoms[nb]["x"] - X["x"], doc.atoms[nb]["y"] - X["y"]
            l = math.hypot(vx, vy)
            if l < 1e-6:
                continue
            vx, vy = vx / l, vy / l
            if vx * m[0] + vy * m[1] <= 1e-3:
                continue
            ang = math.acos(max(-1.0, min(1.0, vx * d[0] + vy * d[1])))
            if best is None or ang < best:
                best = ang
        if best is None or best < 1e-3:
            return 0.0
        return min(off / math.tan(best / 2), 0.45 * S.BOND_LENGTH)

    # ---- arrows ---------------------------------------------------------
    def arrow(self, ar):
        x1, y1, x2, y2 = ar["x1"], ar["y1"], ar["x2"], ar["y2"]
        L = math.hypot(x2 - x1, y2 - y1)
        if L < 1e-6:
            return []
        ux, uy = (x2 - x1) / L, (y2 - y1) / L
        nx, ny = -uy, ux
        hl = min(S.ARROW_HEAD_LEN, 0.6 * L)
        hw = S.ARROW_HEAD_WIDTH * hl / S.ARROW_HEAD_LEN / 2
        bx, by = x2 - ux * hl, y2 - uy * hl
        sx, sy = x2 - ux * hl * 0.75, y2 - uy * hl * 0.75
        return [("line", x1, y1, sx, sy, S.LINE_WIDTH, "butt"),
                ("poly", [(x2, y2), (bx + nx * hw, by + ny * hw), (sx, sy), (bx - nx * hw, by - ny * hw)])]


def prims_bbox(prims, M):
    xs, ys = [], []
    for p in prims:
        k = p[0]
        if k == "line":
            w = p[5] / 2
            xs += [p[1] - w, p[1] + w, p[3] - w, p[3] + w]
            ys += [p[2] - w, p[2] + w, p[4] - w, p[4] + w]
        elif k in ("poly", "polyline"):
            for x, y in p[1]:
                xs.append(x)
                ys.append(y)
        elif k == "text":
            _, x, y, s, size = p
            xs += [x, x + M.width(s, size)]
            ys += [y - S.CAP_HEIGHT * size * 1.05, y + 0.22 * size]
    if not xs:
        return None
    return min(xs), min(ys), max(xs), max(ys)


def to_svg(prims, M, pad=4.0):
    bb = prims_bbox(prims, M) or (0, 0, 10, 10)
    x0, y0 = bb[0] - pad, bb[1] - pad
    w, h = bb[2] - bb[0] + 2 * pad, bb[3] - bb[1] + 2 * pad
    f = lambda v: ("%.3f" % v).rstrip("0").rstrip(".")
    esc = lambda s: s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    out = ['<?xml version="1.0" encoding="UTF-8"?>',
           f'<!-- {APP_NAME}: {S.NAME} -->',
           f'<svg xmlns="http://www.w3.org/2000/svg" width="{f(w)}pt" height="{f(h)}pt" '
           f'viewBox="{f(x0)} {f(y0)} {f(w)} {f(h)}">',
           '<g fill="none" stroke="#000">']
    for p in prims:
        k = p[0]
        if k == "line":
            _, x1, y1, x2, y2, lw, cap = p
            out.append(f'<line x1="{f(x1)}" y1="{f(y1)}" x2="{f(x2)}" y2="{f(y2)}" '
                       f'stroke-width="{f(lw)}" stroke-linecap="{cap}"/>')
        elif k == "poly":
            pts = " ".join(f"{f(x)},{f(y)}" for x, y in p[1])
            out.append(f'<polygon points="{pts}" fill="#000" stroke="none"/>')
        elif k == "polyline":
            pts = " ".join(f"{f(x)},{f(y)}" for x, y in p[1])
            out.append(f'<polyline points="{pts}" stroke-width="{f(p[2])}" '
                       'stroke-linecap="round" stroke-linejoin="round"/>')
        elif k == "text":
            _, x, y, s, size = p
            out.append(f'<text x="{f(x)}" y="{f(y)}" font-family="{S.FONT}, Helvetica, sans-serif" '
                       f'font-size="{f(size)}" fill="#000" stroke="none">{esc(s)}</text>')
    out += ["</g>", "</svg>", ""]
    return "\n".join(out)


def formula_of(doc, ids):
    adj = doc.adjacency()
    counts, unknown, charge = {}, False, 0
    for i in ids:
        a = doc.atoms[i]
        charge += a.get("charge", 0) or 0
        if a.get("label"):
            frag = label_formula(a["label"])
            if frag is None:
                unknown = True
                continue
        else:
            frag = {a["el"]: 1}
            h = implicit_h(a["el"], doc.bond_sum(i, adj), a.get("charge", 0) or 0)
            if h:
                frag["H"] = frag.get("H", 0) + h
        for k, v in frag.items():
            counts[k] = counts.get(k, 0) + v
    return counts, unknown, charge


# --------------------------------------------------------------------------
# Application
# --------------------------------------------------------------------------
BOND_TOOLS = {"single": (1, None), "double": (2, None), "triple": (3, None),
              "wedge": (1, "wedge"), "hash": (1, "hash"), "bold": (1, "bold"),
              "wavy": (1, "wavy")}

HINTS = {
    "select": "Select: click or drag a box to select (Shift adds); drag a selection to move it; Del deletes.",
    "erase": "Eraser: click an atom, bond, caption or arrow to delete it.",
    "text": "Text: click an atom to set a label (N, OMe, CO2Et, Ph...); click empty space for a caption.",
    "arrow": "Arrow: drag to draw a reaction arrow (15° snapping); click for a default arrow.",
    "charge+": "Click an atom to increase its charge.",
    "charge-": "Click an atom to decrease its charge.",
}
BOND_HINT = ("Bond: drag to draw (15° snap); click an atom to extend a chain; "
             "click empty space for a new bond; click a bond to change it (double: cycles position).")
RING_HINT = "Ring: click empty space to place, an atom to share a vertex, a bond to fuse."
ATOM_HINT = "Atom: click an atom to change its element, or empty space to place a lone atom."


class App:
    def __init__(self, root):
        self.root = root
        self.doc = Doc()
        self.M = Measurer(root)
        self.R = Renderer(self.M)
        self.undo_stack, self.redo_stack = [], []
        self.path, self.dirty = None, False
        self.tool = tk.StringVar(value="single")
        self.selection, self.hover, self.drag = set(), None, None
        self.prims, self.fonts = [], {}
        self.base_zoom = root.winfo_fpixels("1i") / 72.0
        self.zoom = self.base_zoom * 2.5
        self.ox, self.oy = 80.0, 80.0
        self._pan = None
        self.build_ui()
        self.on_tool()
        self.changed()

    # ---- UI construction ---------------------------------------------
    def build_ui(self):
        r = self.root
        menu = tk.Menu(r)
        fm = tk.Menu(menu, tearoff=0)
        fm.add_command(label="New", accelerator="Ctrl+N", command=self.cmd_new)
        fm.add_command(label="Open…", accelerator="Ctrl+O", command=self.cmd_open)
        fm.add_command(label="Save", accelerator="Ctrl+S", command=self.cmd_save)
        fm.add_command(label="Save As…", accelerator="Ctrl+Shift+S", command=self.cmd_save_as)
        fm.add_separator()
        fm.add_command(label="Export SVG…", accelerator="Ctrl+E", command=self.cmd_export_svg)
        fm.add_separator()
        fm.add_command(label="Exit", command=self.cmd_exit)
        menu.add_cascade(label="File", menu=fm)

        em = tk.Menu(menu, tearoff=0)
        em.add_command(label="Undo", accelerator="Ctrl+Z", command=self.cmd_undo)
        em.add_command(label="Redo", accelerator="Ctrl+Y", command=self.cmd_redo)
        em.add_separator()
        em.add_command(label="Select All", accelerator="Ctrl+A", command=self.cmd_select_all)
        em.add_command(label="Delete Selection", accelerator="Del", command=self.delete_selection)
        em.add_separator()
        em.add_command(label="Flip Horizontal", command=lambda: self.transform(lambda x, y: (-x, y)))
        em.add_command(label="Flip Vertical", command=lambda: self.transform(lambda x, y: (x, -y)))
        em.add_command(label="Rotate 30° Clockwise", command=lambda: self.rotate(30))
        em.add_command(label="Rotate 30° Anticlockwise", command=lambda: self.rotate(-30))
        menu.add_cascade(label="Edit", menu=em)

        vm = tk.Menu(menu, tearoff=0)
        vm.add_command(label="Zoom In", accelerator="Ctrl+=", command=lambda: self.zoom_at(1.25))
        vm.add_command(label="Zoom Out", accelerator="Ctrl+-", command=lambda: self.zoom_at(1 / 1.25))
        vm.add_command(label="Actual Size", accelerator="Ctrl+0", command=self.cmd_actual_size)
        vm.add_command(label="Fit to Window", accelerator="Ctrl+F", command=self.cmd_fit)
        menu.add_cascade(label="View", menu=vm)

        hm = tk.Menu(menu, tearoff=0)
        hm.add_command(label="Shortcuts", command=self.cmd_help)
        hm.add_command(label="Drawing Style", command=self.cmd_style_info)
        menu.add_cascade(label="Help", menu=hm)
        r.config(menu=menu)

        bar = tk.Frame(r, bd=1, relief="sunken")
        bar.pack(side="bottom", fill="x")
        self.status = tk.StringVar()
        self.info = tk.StringVar()
        tk.Label(bar, textvariable=self.status, anchor="w").pack(side="left", padx=6)
        tk.Label(bar, textvariable=self.info, anchor="e").pack(side="right", padx=6)

        main = tk.Frame(r)
        main.pack(fill="both", expand=True)
        panel = tk.Frame(main, padx=5, pady=4)
        panel.pack(side="left", fill="y")

        def section(title):
            tk.Label(panel, text=title, anchor="w", font=("Segoe UI", 9, "bold")).pack(fill="x", pady=(6, 1))
            f = tk.Frame(panel)
            f.pack(fill="x")
            return f

        def buttons(frame, items, cols, width):
            for i, (label, value) in enumerate(items):
                tk.Radiobutton(frame, text=label, variable=self.tool, value=value, indicatoron=0,
                               width=width, pady=3, command=self.on_tool
                               ).grid(row=i // cols, column=i % cols, sticky="ew", padx=1, pady=1)

        buttons(section("Tools"), [("Select", "select"), ("Eraser", "erase"),
                                   ("Text", "text"), ("Arrow", "arrow")], 2, 9)
        buttons(section("Bonds"), [("Single", "single"), ("Double", "double"),
                                   ("Triple", "triple"), ("Wedge", "wedge"),
                                   ("Hashed", "hash"), ("Bold", "bold"),
                                   ("Wavy", "wavy")], 2, 9)
        buttons(section("Rings"), [("3", "ring3"), ("4", "ring4"), ("5", "ring5"),
                                   ("6", "ring6"), ("7", "ring7"), ("8", "ring8")], 3, 5)
        tk.Radiobutton(panel, text="Benzene", variable=self.tool, value="benzene", indicatoron=0,
                       pady=3, command=self.on_tool).pack(fill="x", padx=1, pady=1)
        buttons(section("Atoms"), [(e, "el:" + e) for e in
                                   ("C", "H", "N", "O", "S", "P", "F", "Cl", "Br", "I", "B", "Si")], 4, 3)
        buttons(section("Charge"), [("+", "charge+"), ("−", "charge-")], 2, 9)
        tk.Label(panel, justify="left", fg="#555", font=("Segoe UI", 8),
                 text=f"\nACS 1996, 2× line\nbond {S.BOND_LENGTH:g} pt\n"
                      f"line {S.LINE_WIDTH:g} pt\nbold {S.BOLD_WIDTH:g} pt\n"
                      f"{S.FONT} {S.FONT_SIZE:g} pt").pack(fill="x", side="bottom")

        self.canvas = c = tk.Canvas(main, bg="white", highlightthickness=0,
                                    width=1000, height=700, cursor="crosshair")
        c.pack(side="left", fill="both", expand=True)
        c.bind("<ButtonPress-1>", self.on_press)
        c.bind("<B1-Motion>", self.on_drag)
        c.bind("<ButtonRelease-1>", self.on_release)
        c.bind("<Motion>", self.on_motion)
        c.bind("<Leave>", lambda e: self.set_hover(None))
        c.bind("<Enter>", lambda e: c.focus_set())
        for n in (2, 3):
            c.bind(f"<ButtonPress-{n}>", self.pan_start)
            c.bind(f"<B{n}-Motion>", self.pan_move)
        c.bind("<MouseWheel>", self.on_wheel)
        c.bind("<Button-4>", self.on_wheel)
        c.bind("<Button-5>", self.on_wheel)
        c.bind("<Configure>", lambda e: self.redraw())

        r.bind("<Key>", self.on_key)

        def ctrl(keys, fn):
            for k in keys:
                r.bind(f"<Control-{k}>", lambda e: (fn(), "break")[1])
        ctrl(("n", "N"), self.cmd_new)
        ctrl(("o", "O"), self.cmd_open)
        ctrl(("s",), self.cmd_save)
        r.bind("<Control-Shift-S>", lambda e: (self.cmd_save_as(), "break")[1])
        ctrl(("e", "E"), self.cmd_export_svg)
        ctrl(("z", "Z"), self.cmd_undo)
        ctrl(("y", "Y"), self.cmd_redo)
        ctrl(("a", "A"), self.cmd_select_all)
        ctrl(("f", "F"), self.cmd_fit)
        ctrl(("equal", "plus"), lambda: self.zoom_at(1.25))
        ctrl(("minus",), lambda: self.zoom_at(1 / 1.25))
        ctrl(("0",), self.cmd_actual_size)
        r.protocol("WM_DELETE_WINDOW", self.cmd_exit)

    def on_tool(self):
        t = self.tool.get()
        if t in BOND_TOOLS:
            self.status.set(BOND_HINT)
        elif t.startswith("ring") or t == "benzene":
            self.status.set(RING_HINT)
        elif t.startswith("el:"):
            self.status.set(ATOM_HINT)
        else:
            self.status.set(HINTS.get(t, ""))
        self.canvas.configure(cursor="arrow" if t == "select" else "crosshair")

    def update_title(self):
        name = self.path.replace("\\", "/").split("/")[-1] if self.path else "Untitled"
        self.root.title(f"{APP_NAME} — {name}{' *' if self.dirty else ''}")

    # ---- coordinates / view -------------------------------------------
    def w2s(self, x, y):
        return x * self.zoom + self.ox, y * self.zoom + self.oy

    def s2w(self, x, y):
        return (x - self.ox) / self.zoom, (y - self.oy) / self.zoom

    def zoom_at(self, factor, sx=None, sy=None):
        if sx is None:
            sx, sy = self.canvas.winfo_width() / 2, self.canvas.winfo_height() / 2
        wx, wy = self.s2w(sx, sy)
        self.zoom = max(0.3, min(30.0, self.zoom * factor))
        self.ox, self.oy = sx - wx * self.zoom, sy - wy * self.zoom
        self.redraw()

    def cmd_actual_size(self):
        self.zoom_at(self.base_zoom / self.zoom)

    def cmd_fit(self):
        bb = prims_bbox(self.prims, self.M)
        if not bb:
            return
        cw, ch = max(self.canvas.winfo_width(), 50), max(self.canvas.winfo_height(), 50)
        w, h = max(bb[2] - bb[0], 1.0), max(bb[3] - bb[1], 1.0)
        self.zoom = max(0.3, min(12.0, min(cw / w, ch / h) * 0.8))
        self.ox = cw / 2 - (bb[0] + bb[2]) / 2 * self.zoom
        self.oy = ch / 2 - (bb[1] + bb[3]) / 2 * self.zoom
        self.redraw()

    def pan_start(self, e):
        self._pan = (e.x, e.y, self.ox, self.oy)

    def pan_move(self, e):
        if self._pan:
            x, y, ox, oy = self._pan
            self.ox, self.oy = ox + e.x - x, oy + e.y - y
            self.redraw()

    def on_wheel(self, e):
        delta = e.delta if e.delta else (120 if getattr(e, "num", 0) == 4 else -120)
        if e.state & 0x4:
            self.zoom_at(1.15 if delta > 0 else 1 / 1.15, e.x, e.y)
            return
        if e.state & 0x1:
            self.ox += delta / 120 * 40
        else:
            self.oy += delta / 120 * 40
        self.redraw()

    # ---- drawing on the canvas ----------------------------------------
    def font(self, px):
        px = max(1, int(round(px)))
        f = self.fonts.get(px)
        if f is None:
            fo = tkfont.Font(root=self.root, family=S.FONT, size=-px)
            f = self.fonts[px] = (fo, fo.metrics("ascent"))
        return f

    def changed(self):
        d = self.doc
        pools = {"atom": d.atoms, "text": d.texts, "arrow": d.arrows}
        self.selection = {(k, i) for k, i in self.selection if i in pools[k]}
        if self.hover and self.hover[1] not in {**pools, "bond": d.bonds}[self.hover[0]]:
            self.hover = None
        self.prims = self.R.build(d)
        self.update_info()
        self.update_title()
        self.redraw()

    def redraw(self):
        self.canvas.delete("all")
        self.draw_highlights()
        for p in self.prims:
            self.draw_prim(p)
        self.draw_previews()

    def draw_prim(self, p, color="black"):
        c, z, k = self.canvas, self.zoom, p[0]
        if k == "line":
            _, x1, y1, x2, y2, w, cap = p
            c.create_line(*self.w2s(x1, y1), *self.w2s(x2, y2), fill=color, width=max(1.0, w * z),
                          capstyle=tk.ROUND if cap == "round" else tk.BUTT)
        elif k == "poly":
            c.create_polygon(*[v for xy in p[1] for v in self.w2s(*xy)], fill=color, outline="")
        elif k == "polyline":
            c.create_line(*[v for xy in p[1] for v in self.w2s(*xy)], fill=color,
                          width=max(1.0, p[2] * z), capstyle=tk.ROUND, joinstyle=tk.ROUND)
        elif k == "text":
            _, x, y, s, size = p
            fo, asc = self.font(size * z)
            sx, sy = self.w2s(x, y)
            c.create_text(sx, sy - asc, text=s, anchor="nw", font=fo, fill=color)

    def draw_highlights(self):
        c, z, L, d = self.canvas, self.zoom, S.BOND_LENGTH, self.doc
        SEL, HOV = "#b8d4ff", "#ffd9a0"
        sel_atoms = {i for k, i in self.selection if k == "atom"}

        def mark(kind, i, color):
            if kind == "atom":
                a = d.atoms[i]
                x, y = self.w2s(a["x"], a["y"])
                r = 0.3 * L * z
                c.create_oval(x - r, y - r, x + r, y + r, fill=color, outline="")
            elif kind == "bond":
                b = d.bonds[i]
                A, B = d.atoms[b["a"]], d.atoms[b["b"]]
                c.create_line(*self.w2s(A["x"], A["y"]), *self.w2s(B["x"], B["y"]),
                              fill=color, width=0.45 * L * z, capstyle=tk.ROUND)
            elif kind == "text":
                x0, y0, x1, y1 = self.text_bbox(d.texts[i])
                c.create_rectangle(*self.w2s(x0 - 1, y0 - 1), *self.w2s(x1 + 1, y1 + 1), fill=color, outline="")
            elif kind == "arrow":
                ar = d.arrows[i]
                c.create_line(*self.w2s(ar["x1"], ar["y1"]), *self.w2s(ar["x2"], ar["y2"]),
                              fill=color, width=0.4 * L * z, capstyle=tk.ROUND)

        for i, b in d.bonds.items():
            if b["a"] in sel_atoms and b["b"] in sel_atoms:
                mark("bond", i, SEL)
        for k, i in self.selection:
            mark(k, i, SEL)
        if self.hover:
            mark(self.hover[0], self.hover[1], HOV)

    def draw_previews(self):
        d = self.drag
        if not d:
            return
        c = self.canvas
        if d.get("preview"):
            (x1, y1), (x2, y2) = d["preview"]
            if self.tool.get() == "arrow":
                for p in self.R.arrow({"x1": x1, "y1": y1, "x2": x2, "y2": y2}):
                    self.draw_prim(p, "#7a7a7a")
            else:
                c.create_line(*self.w2s(x1, y1), *self.w2s(x2, y2), fill="#7a7a7a",
                              width=max(1.0, S.LINE_WIDTH * self.zoom), capstyle=tk.ROUND)
        if d.get("band"):
            x1, y1, x2, y2 = d["band"]
            c.create_rectangle(*self.w2s(x1, y1), *self.w2s(x2, y2), outline="#3a7bd5", dash=(4, 3))

    def update_info(self):
        sel = [i for k, i in self.selection if k == "atom"]
        ids = sel or list(self.doc.atoms)
        if not ids:
            self.info.set(S.NAME)
            return
        counts, unknown, charge = formula_of(self.doc, ids)
        mw = sum(MASS[e] * n for e, n in counts.items() if e in MASS)
        txt = f"{'Selection' if sel else 'Drawing'}: {hill_formula(counts)}{charge_text(charge)}   MW {mw:.2f}"
        if unknown:
            txt += "  (some labels not recognised)"
        self.info.set(txt + "     |  " + S.NAME)

    # ---- hit testing ----------------------------------------------------
    def text_bbox(self, t):
        w = self.M.width(t["s"], S.CAPTION_SIZE)
        return (t["x"], t["y"] - S.CAP_HEIGHT * S.CAPTION_SIZE - 1,
                t["x"] + w, t["y"] + 0.25 * S.CAPTION_SIZE)

    def hit(self, wx, wy):
        d, L, z = self.doc, S.BOND_LENGTH, self.zoom
        best, bd = None, max(0.28 * L, 5 / z)
        for i, a in d.atoms.items():
            dist = math.hypot(a["x"] - wx, a["y"] - wy)
            if dist < bd:
                best, bd = ("atom", i), dist
        if best:
            return best
        bd = max(0.22 * L, 4 / z)
        for i, b in d.bonds.items():
            A, B = d.atoms[b["a"]], d.atoms[b["b"]]
            dist = dist_seg(wx, wy, A["x"], A["y"], B["x"], B["y"])
            if dist < bd:
                best, bd = ("bond", i), dist
        if best:
            return best
        for i, t in d.texts.items():
            x0, y0, x1, y1 = self.text_bbox(t)
            if x0 - 1 <= wx <= x1 + 1 and y0 - 1 <= wy <= y1 + 1:
                return ("text", i)
        for i, ar in d.arrows.items():
            if dist_seg(wx, wy, ar["x1"], ar["y1"], ar["x2"], ar["y2"]) < max(0.25 * L, 4 / z):
                return ("arrow", i)
        return None

    def atom_near(self, x, y, exclude=(), tol=None):
        tol = tol if tol is not None else 0.3 * S.BOND_LENGTH
        best, bd = None, tol
        for i, a in self.doc.atoms.items():
            if i in exclude:
                continue
            dist = math.hypot(a["x"] - x, a["y"] - y)
            if dist < bd:
                best, bd = i, dist
        return best

    def set_hover(self, h):
        if h != self.hover:
            self.hover = h
            self.redraw()

    # ---- undo / editing ---------------------------------------------------
    def push_undo(self, state):
        self.undo_stack.append(state)
        del self.undo_stack[:-300]
        self.redo_stack.clear()
        self.dirty = True

    def edit(self, fn, *args):
        """Run a document mutation; record an undo step only if something changed."""
        before = self.doc.dumps()
        fn(*args)
        if self.doc.dumps() != before:
            self.push_undo(before)
        self.changed()

    def cmd_undo(self):
        if self.undo_stack:
            self.redo_stack.append(self.doc.dumps())
            self.doc.loads(self.undo_stack.pop())
            self.dirty = True
            self.changed()

    def cmd_redo(self):
        if self.redo_stack:
            self.undo_stack.append(self.doc.dumps())
            self.doc.loads(self.redo_stack.pop())
            self.dirty = True
            self.changed()

    # ---- mouse handling -----------------------------------------------
    def on_motion(self, e):
        self.set_hover(self.hit(*self.s2w(e.x, e.y)))

    def on_press(self, e):
        wx, wy = self.s2w(e.x, e.y)
        t = self.hit(wx, wy)
        self.drag = {"sx": e.x, "sy": e.y, "wx": wx, "wy": wy, "target": t,
                     "moved": False, "shift": bool(e.state & 0x1)}
        if self.tool.get() == "select":
            if t:
                objs = self.objs_for(t)
                if not objs <= self.selection:
                    self.selection = (self.selection | objs) if self.drag["shift"] else set(objs)
                self.drag["mode"] = "move"
            else:
                if not self.drag["shift"]:
                    self.selection = set()
                self.drag["mode"] = "band"
            self.update_info()
            self.redraw()

    def objs_for(self, t):
        if t[0] == "bond":
            b = self.doc.bonds[t[1]]
            return {("atom", b["a"]), ("atom", b["b"])}
        return {t}

    def on_drag(self, e):
        d = self.drag
        if not d:
            return
        if not d["moved"] and math.hypot(e.x - d["sx"], e.y - d["sy"]) < 4:
            return
        d["moved"] = True
        wx, wy = self.s2w(e.x, e.y)
        tool, t, L = self.tool.get(), d["target"], S.BOND_LENGTH
        if tool == "select":
            if d["mode"] == "move":
                if "before" not in d:
                    d["before"], d["last"] = self.doc.dumps(), (d["wx"], d["wy"])
                dx, dy = wx - d["last"][0], wy - d["last"][1]
                d["last"] = (wx, wy)
                self.move_selection(dx, dy)
                self.changed()
            else:
                d["band"] = (d["wx"], d["wy"], wx, wy)
                self.redraw()
        elif tool in BOND_TOOLS:
            if t and t[0] == "atom":
                a = self.doc.atoms[t[1]]
                start, exclude = (a["x"], a["y"]), {t[1]}
            else:
                start, exclude = (d["wx"], d["wy"]), set()
            end_atom = self.atom_near(wx, wy, exclude=exclude)
            if end_atom:
                ea = self.doc.atoms[end_atom]
                end = (ea["x"], ea["y"])
            else:
                ux, uy = snap_dir(wx - start[0], wy - start[1])
                end = (start[0] + L * ux, start[1] + L * uy)
            d["preview"], d["end_atom"] = (start, end), end_atom
            self.redraw()
        elif tool == "arrow":
            dist = math.hypot(wx - d["wx"], wy - d["wy"])
            ux, uy = snap_dir(wx - d["wx"], wy - d["wy"])
            d["preview"] = ((d["wx"], d["wy"]), (d["wx"] + ux * dist, d["wy"] + uy * dist))
            self.redraw()

    def on_release(self, e):
        d, self.drag = self.drag, None
        if not d:
            return
        tool, t = self.tool.get(), d["target"]
        if tool == "select":
            if d.get("band"):
                x1, y1, x2, y2 = d["band"]
                found = self.objects_in_rect(min(x1, x2), min(y1, y2), max(x1, x2), max(y1, y2))
                self.selection = (self.selection | found) if d["shift"] else found
            elif d.get("before") is not None and self.doc.dumps() != d["before"]:
                self.push_undo(d["before"])
            self.changed()
        elif tool in BOND_TOOLS:
            self.edit(self.bond_action, d, tool)
        elif tool.startswith("ring") or tool == "benzene":
            self.edit(self.ring_action, d, tool)
        elif tool.startswith("el:"):
            self.edit(self.element_action, d, tool[3:])
        elif tool in ("charge+", "charge-"):
            if t and t[0] == "atom":
                a = self.doc.atoms[t[1]]
                self.edit(lambda: a.update(charge=(a.get("charge", 0) or 0) + (1 if tool == "charge+" else -1)))
        elif tool == "erase":
            self.edit(self.erase_action, t)
        elif tool == "text":
            self.text_action(d)
        elif tool == "arrow":
            self.edit(self.arrow_action, d)

    # ---- tool actions -----------------------------------------------------
    def connect(self, a, b, tool):
        existing = self.doc.bond_between(a, b)
        if existing:
            self.modify_bond(existing, tool)
        else:
            self.doc.add_bond(a, b, *BOND_TOOLS[tool])

    def bond_action(self, d, tool):
        doc, L, t = self.doc, S.BOND_LENGTH, d["target"]
        if d["moved"] and d.get("preview"):
            (x1, y1), (x2, y2) = d["preview"]
            a = t[1] if t and t[0] == "atom" else (self.atom_near(x1, y1) or doc.add_atom(x1, y1))
            b = d.get("end_atom") or self.atom_near(x2, y2, exclude={a}) or doc.add_atom(x2, y2)
            self.connect(a, b, tool)
        elif t and t[0] == "atom":
            ux, uy = self.sprout_dir(t[1])
            A = doc.atoms[t[1]]
            x, y = A["x"] + L * ux, A["y"] + L * uy
            b = self.atom_near(x, y, exclude={t[1]}) or doc.add_atom(x, y)
            self.connect(t[1], b, tool)
        elif t and t[0] == "bond":
            self.modify_bond(t[1], tool)
        elif not t:
            r = math.radians(-30)
            a = doc.add_atom(d["wx"], d["wy"])
            b = doc.add_atom(d["wx"] + L * math.cos(r), d["wy"] + L * math.sin(r))
            doc.add_bond(a, b, *BOND_TOOLS[tool])

    def modify_bond(self, bid, tool):
        b = self.doc.bonds[bid]
        if tool == "single":
            if b.get("stereo"):
                b["stereo"] = None
            else:
                b["order"] = {1: 2, 2: 3}.get(b["order"], 1)
        elif tool == "double":
            if b["order"] == 2:
                cycle = ["auto", "center", "plus", "minus"]
                b["pos"] = cycle[(cycle.index(b.get("pos", "auto")) + 1) % 4]
            else:
                b["order"], b["stereo"] = 2, None
        elif tool == "triple":
            b["order"], b["stereo"] = 3, None
        else:
            if b.get("stereo") == tool and b["order"] == 1:
                b["a"], b["b"] = b["b"], b["a"]       # flip wedge direction
            else:
                b["order"], b["stereo"] = 1, tool

    def sprout_dir(self, aid):
        """Direction for a new bond: 120 deg zig-zag, or bisect the largest gap."""
        doc = self.doc
        adj = doc.adjacency()
        A = doc.atoms[aid]
        vecs = []
        for nb, _ in adj[aid]:
            B = doc.atoms[nb]
            dx, dy = B["x"] - A["x"], B["y"] - A["y"]
            l = math.hypot(dx, dy)
            if l > 1e-6:
                vecs.append((dx / l, dy / l, nb))
        if not vecs:
            r = math.radians(-30)
            return math.cos(r), math.sin(r)
        if len(vecs) == 1:
            vx, vy, nb = vecs[0]
            a0, ca = math.atan2(vy, vx), math.radians(S.CHAIN_ANGLE)
            cands = [(math.cos(a0 + s * ca), math.sin(a0 + s * ca)) for s in (1, -1)]
            N = doc.atoms[nb]
            others = [doc.atoms[m] for m, _ in adj[nb] if m != aid]
            if others:   # keep the chain zig-zagging (trans)
                side = lambda px, py: (-vx) * (py - N["y"]) - (-vy) * (px - N["x"])
                ref = sum(side(o["x"], o["y"]) for o in others)
                if abs(ref) > 1e-6:
                    for cx, cy in cands:
                        if side(A["x"] + cx, A["y"] + cy) * ref < 0:
                            return cx, cy
            return max(cands, key=lambda c: (round(c[0], 3), -c[1]))
        angs = sorted(math.atan2(vy, vx) for vx, vy, _ in vecs)
        best_gap, best = -1.0, 0.0
        for i, a in enumerate(angs):
            nxt = angs[(i + 1) % len(angs)] + (2 * math.pi if i == len(angs) - 1 else 0)
            if nxt - a > best_gap:
                best_gap, best = nxt - a, a + (nxt - a) / 2
        return math.cos(best), math.sin(best)

    def ring_action(self, d, tool):
        n = 6 if tool == "benzene" else int(tool[4:])
        doc, t, L = self.doc, d["target"], S.BOND_LENGTH
        adj = doc.adjacency()
        step = 2 * math.pi / n
        ids = [None] * n
        if t and t[0] == "bond":
            bd = doc.bonds[t[1]]
            a, b = bd["a"], bd["b"]
            P, Q = doc.atoms[a], doc.atoms[b]
            dx, dy = Q["x"] - P["x"], Q["y"] - P["y"]
            lb = math.hypot(dx, dy)
            if lb < 1e-6:
                return
            ux, uy = dx / lb, dy / lb
            nx, ny = -uy, ux
            score = 0
            for X, other in ((a, b), (b, a)):
                XA = doc.atoms[X]
                for nb, _ in adj[X]:
                    if nb != other:
                        v = (doc.atoms[nb]["x"] - XA["x"]) * nx + (doc.atoms[nb]["y"] - XA["y"]) * ny
                        score += (v > 1e-6) - (v < -1e-6)
            mx, my = (P["x"] + Q["x"]) / 2, (P["y"] + Q["y"]) / 2
            if score:
                side = -1 if score > 0 else 1
            else:
                side = 1 if (d["wx"] - mx) * nx + (d["wy"] - my) * ny >= 0 else -1
            R = lb / (2 * math.sin(math.pi / n))
            ap = lb / (2 * math.tan(math.pi / n))
            cx, cy = mx + nx * side * ap, my + ny * side * ap
            th0 = math.atan2(P["y"] - cy, P["x"] - cx)
            vp = lambda k, st: (cx + R * math.cos(th0 + k * st), cy + R * math.sin(th0 + k * st))
            if math.dist(vp(1, step), (Q["x"], Q["y"])) > math.dist(vp(1, -step), (Q["x"], Q["y"])):
                step = -step
            ids[0], ids[1] = a, b
        elif t and t[0] == "atom":
            a = t[1]
            A = doc.atoms[a]
            if len(adj[a]) == 1:   # hang the ring straight off the chain end
                B = doc.atoms[adj[a][0][0]]
                dx, dy = A["x"] - B["x"], A["y"] - B["y"]
                l = math.hypot(dx, dy) or 1.0
                ux, uy = dx / l, dy / l
            else:
                ux, uy = self.sprout_dir(a)
            R = L / (2 * math.sin(math.pi / n))
            cx, cy = A["x"] + ux * R, A["y"] + uy * R
            th0 = math.atan2(A["y"] - cy, A["x"] - cx)
            ids[0] = a
        else:
            R = L / (2 * math.sin(math.pi / n))
            cx, cy, th0 = d["wx"], d["wy"], -math.pi / 2
        for k in range(n):
            if ids[k] is None:
                x, y = cx + R * math.cos(th0 + k * step), cy + R * math.sin(th0 + k * step)
                used = {i for i in ids if i}
                ids[k] = self.atom_near(x, y, exclude=used, tol=0.25 * L) or doc.add_atom(x, y)
        for k in range(n):
            doc.add_bond(ids[k], ids[(k + 1) % n])
        if tool == "benzene":
            self.kekulize_ring(ids)

    def kekulize_ring(self, ids):
        doc, n = self.doc, len(ids)
        rb = [doc.bond_between(ids[k], ids[(k + 1) % n]) for k in range(n)]
        if None in rb:
            return
        rset = set(rb)

        def outside_double(atom):
            return any(b["order"] >= 2 for i, b in doc.bonds.items()
                       if i not in rset and atom in (b["a"], b["b"]))
        best = None
        for parity in (0, 1):
            conf = 0
            for k in range(n):
                bd = doc.bonds[rb[k]]
                if k % 2 == parity:
                    conf += outside_double(bd["a"]) + outside_double(bd["b"])
                elif bd["order"] >= 2:
                    conf += 1
            if best is None or conf < best[0]:
                best = (conf, parity)
        for k in range(n):
            bd = doc.bonds[rb[k]]
            if k % 2 == best[1] and not (outside_double(bd["a"]) or outside_double(bd["b"])):
                bd["order"], bd["stereo"] = 2, None

    def element_action(self, d, el):
        t = d["target"]
        if t and t[0] == "atom":
            self.doc.atoms[t[1]].update(el=el, label=None)
        elif not t:
            self.doc.add_atom(d["wx"], d["wy"], el)

    def erase_action(self, t):
        if not t:
            return
        k, i = t
        if k == "atom":
            self.doc.delete_atom(i)
        elif k == "bond":
            self.doc.delete_bond(i)
        elif k == "text":
            self.doc.texts.pop(i, None)
        elif k == "arrow":
            self.doc.arrows.pop(i, None)

    def text_action(self, d):
        t, doc = d["target"], self.doc
        if t and t[0] == "atom":
            a = doc.atoms[t[1]]
            s = simpledialog.askstring("Atom label", "Element or label (e.g. N, OMe, CO2Et, Ph, NHBoc).\n"
                                       "Leave empty for carbon:",
                                       initialvalue=a["label"] or a["el"], parent=self.root)
            if s is None:
                return
            s = s.strip()

            def apply():
                if not s:
                    a.update(el="C", label=None)
                elif s in VALENCE or s in MASS:
                    a.update(el=s, label=None)
                else:
                    a["label"] = s
            self.edit(apply)
        elif t and t[0] == "text":
            txt = doc.texts[t[1]]
            s = simpledialog.askstring("Caption", "Text (empty deletes):", initialvalue=txt["s"], parent=self.root)
            if s is not None:
                self.edit(lambda: txt.update(s=s) if s.strip() else doc.texts.pop(t[1], None))
        elif not t:
            s = simpledialog.askstring("Caption", "Text:", parent=self.root)
            if s and s.strip():
                self.edit(lambda: doc.add_text(d["wx"], d["wy"], s))

    def arrow_action(self, d):
        if d["moved"] and d.get("preview"):
            (x1, y1), (x2, y2) = d["preview"]
        else:
            x1, y1 = d["wx"], d["wy"]
            x2, y2 = x1 + 3 * S.BOND_LENGTH, y1
        if math.hypot(x2 - x1, y2 - y1) > 2:
            self.doc.add_arrow(x1, y1, x2, y2)

    # ---- selection ------------------------------------------------------
    def objects_in_rect(self, x0, y0, x1, y1):
        inside = lambda x, y: x0 <= x <= x1 and y0 <= y <= y1
        d, found = self.doc, set()
        found |= {("atom", i) for i, a in d.atoms.items() if inside(a["x"], a["y"])}
        found |= {("text", i) for i, t in d.texts.items() if inside(t["x"], t["y"])}
        found |= {("arrow", i) for i, a in d.arrows.items()
                  if inside(a["x1"], a["y1"]) and inside(a["x2"], a["y2"])}
        return found

    def move_selection(self, dx, dy):
        d = self.doc
        for k, i in self.selection:
            if k == "atom":
                d.atoms[i]["x"] += dx
                d.atoms[i]["y"] += dy
            elif k == "text":
                d.texts[i]["x"] += dx
                d.texts[i]["y"] += dy
            elif k == "arrow":
                ar = d.arrows[i]
                ar["x1"] += dx; ar["y1"] += dy; ar["x2"] += dx; ar["y2"] += dy

    def cmd_select_all(self):
        d = self.doc
        self.selection = ({("atom", i) for i in d.atoms} | {("text", i) for i in d.texts}
                          | {("arrow", i) for i in d.arrows})
        self.changed()

    def delete_selection(self):
        if not self.selection:
            return
        sel = set(self.selection)

        def apply():
            for k, i in sel:
                if k == "atom":
                    self.doc.delete_atom(i)
                elif k == "text":
                    self.doc.texts.pop(i, None)
                elif k == "arrow":
                    self.doc.arrows.pop(i, None)
        self.selection = set()
        self.edit(apply)

    def transform(self, fn):
        d = self.doc
        sel = self.selection or ({("atom", i) for i in d.atoms} | {("text", i) for i in d.texts}
                                 | {("arrow", i) for i in d.arrows})
        pts = []
        for k, i in sel:
            if k == "atom":
                pts.append((d.atoms[i]["x"], d.atoms[i]["y"]))
            elif k == "text":
                pts.append((d.texts[i]["x"], d.texts[i]["y"]))
            elif k == "arrow":
                ar = d.arrows[i]
                pts += [(ar["x1"], ar["y1"]), (ar["x2"], ar["y2"])]
        if not pts:
            return
        cx = sum(p[0] for p in pts) / len(pts)
        cy = sum(p[1] for p in pts) / len(pts)

        def tf(x, y):
            nx, ny = fn(x - cx, y - cy)
            return nx + cx, ny + cy

        def apply():
            for k, i in sel:
                if k == "atom":
                    a = d.atoms[i]
                    a["x"], a["y"] = tf(a["x"], a["y"])
                elif k == "text":
                    t = d.texts[i]
                    t["x"], t["y"] = tf(t["x"], t["y"])
                elif k == "arrow":
                    ar = d.arrows[i]
                    ar["x1"], ar["y1"] = tf(ar["x1"], ar["y1"])
                    ar["x2"], ar["y2"] = tf(ar["x2"], ar["y2"])
        self.edit(apply)

    def rotate(self, deg):
        r = math.radians(deg)
        c, s = math.cos(r), math.sin(r)
        self.transform(lambda x, y: (x * c - y * s, x * s + y * c))

    # ---- keyboard -------------------------------------------------------
    def on_key(self, e):
        if e.state & 0x4 or isinstance(e.widget, tk.Entry):
            return
        ks, ch, h = e.keysym, e.char, self.hover
        if ks in ("Delete", "BackSpace"):
            if self.selection:
                self.delete_selection()
            elif h:
                self.edit(self.erase_action, h)
            return "break"
        if ks == "Escape":
            self.selection, self.drag = set(), None
            self.changed()
            return
        if not h or not ch:
            return
        if h[0] == "atom":
            a = self.doc.atoms[h[1]]
            if ch.lower() in ELEMENT_HOTKEYS:
                el = ELEMENT_HOTKEYS[ch.lower()]
                self.edit(lambda: a.update(el=el, label=None))
            elif ch in "+=":
                self.edit(lambda: a.update(charge=(a.get("charge", 0) or 0) + 1))
            elif ch == "-":
                self.edit(lambda: a.update(charge=(a.get("charge", 0) or 0) - 1))
        elif h[0] == "bond" and ch in "123":
            b = self.doc.bonds[h[1]]
            self.edit(lambda: b.update(order=int(ch), stereo=None))

    # ---- files ------------------------------------------------------------
    def confirm_discard(self):
        if not self.dirty:
            return True
        r = messagebox.askyesnocancel(APP_NAME, "Save changes to the current drawing?", parent=self.root)
        if r is None:
            return False
        return self.cmd_save() if r else True

    def cmd_new(self):
        if not self.confirm_discard():
            return
        self.doc.clear()
        self.undo_stack.clear()
        self.redo_stack.clear()
        self.path, self.dirty, self.selection = None, False, set()
        self.changed()

    def open_path(self, path):
        try:
            with open(path, "r", encoding="utf-8") as fh:
                self.doc.loads(fh.read())
        except (OSError, ValueError, KeyError) as exc:
            messagebox.showerror(APP_NAME, f"Could not open {path}:\n{exc}", parent=self.root)
            return
        self.undo_stack.clear()
        self.redo_stack.clear()
        self.path, self.dirty, self.selection = path, False, set()
        self.changed()
        self.root.after(50, self.cmd_fit)

    def cmd_open(self):
        if not self.confirm_discard():
            return
        path = filedialog.askopenfilename(parent=self.root, filetypes=[
            ("Skeletal drawing", "*.json"), ("All files", "*.*")])
        if path:
            self.open_path(path)

    def cmd_save(self):
        if not self.path:
            return self.cmd_save_as()
        try:
            with open(self.path, "w", encoding="utf-8") as fh:
                fh.write(self.doc.dumps())
        except OSError as exc:
            messagebox.showerror(APP_NAME, f"Could not save:\n{exc}", parent=self.root)
            return False
        self.dirty = False
        self.update_title()
        return True

    def cmd_save_as(self):
        path = filedialog.asksaveasfilename(parent=self.root, defaultextension=".json",
                                            filetypes=[("Skeletal drawing", "*.json")])
        if not path:
            return False
        self.path = path
        return self.cmd_save()

    def cmd_export_svg(self):
        path = filedialog.asksaveasfilename(parent=self.root, defaultextension=".svg",
                                            filetypes=[("SVG image", "*.svg")])
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(to_svg(self.prims, self.M))
        except OSError as exc:
            messagebox.showerror(APP_NAME, f"Could not export:\n{exc}", parent=self.root)

    def cmd_exit(self):
        if self.confirm_discard():
            self.root.destroy()

    def cmd_help(self):
        messagebox.showinfo(APP_NAME + " shortcuts", __doc__.split("Mouse", 1)[1].join(["Mouse", ""]),
                            parent=self.root)

    def cmd_style_info(self):
        messagebox.showinfo("Drawing style", (
            f"{S.NAME}\n\n"
            f"Chain angle\t{S.CHAIN_ANGLE:g}°\n"
            f"Bond length\t{S.BOND_LENGTH:g} pt (0.508 cm)\n"
            f"Bond spacing\t{S.BOND_SPACING * 100:g} % of length\n"
            f"Line width\t{S.LINE_WIDTH:g} pt (ACS 0.6 pt × {S.LINE_MULTIPLIER:g})\n"
            f"Bold width\t{S.BOLD_WIDTH:g} pt\n"
            f"Margin width\t{S.MARGIN:g} pt\n"
            f"Hash spacing\t{S.HASH_SPACING:g} pt\n"
            f"Labels\t\t{S.FONT} {S.FONT_SIZE:g} pt"), parent=self.root)


def main():
    try:   # crisp rendering on high-DPI Windows displays
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    root = tk.Tk()
    root.geometry("1250x820")
    app = App(root)
    if len(sys.argv) > 1:
        app.open_path(sys.argv[1])
    root.mainloop()


if __name__ == "__main__":
    main()
