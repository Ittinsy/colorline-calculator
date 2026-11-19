import argparse, json, math, os, re, shutil, subprocess, sys, tempfile, time
from PIL import Image, ImageDraw, ImageFont
import colorline_solver as cs

PALETTE = {
    1: ((255, 156, 132), (196, 34, 18), (74, 5, 0)),
    2: ((255, 234, 166), (226, 161, 58), (110, 66, 4)),
    3: ((164, 255, 148), (31, 189, 31), (6, 68, 10)),
    4: ((147, 160, 255), (36, 36, 194), (8, 8, 78)),
    5: ((255, 166, 242), (208, 44, 180), (86, 10, 74)),
    6: ((166, 250, 255), (30, 178, 200), (4, 64, 74)),
    7: ((255, 255, 255), (214, 214, 214), (102, 102, 102)),
}
BOUNCE = (36, 32, 28, 32, 36, 40)
STEP_MS, FRAME_MS, REFRESH_MS, BOUNCE_MS = 48, 31, 200, 60
SPAWN_SIZES = (28, 32, 36, 40)
CLEAR_SIZES = (36, 32, 28, 0)


def lerp(a, b, t):
    return tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))


def make_master(colors, d):
    ss = 3
    n = int(d * ss * 1.3)
    R = d * ss / 2.0
    cx = cy = n / 2.0
    shadow = Image.new("RGBA", (n, n), (0, 0, 0, 0))
    ImageDraw.Draw(shadow).ellipse(
        [cx + 0.12 * R - 0.98 * R, cy + 0.16 * R - 0.94 * R, cx + 0.12 * R + 0.98 * R, cy + 0.16 * R + 0.94 * R],
        fill=(0, 0, 0, 77))
    ball = Image.new("RGBA", (n, n), (0, 0, 0, 0))
    px = ball.load()
    hi, mid, lo = colors
    c0x, c0y, r0 = -0.36, -0.42, 0.08
    dx, dy, dr = -0.05 - c0x, -0.05 - c0y, 1.05 - r0
    a = dx * dx + dy * dy - dr * dr
    cr, sr = math.cos(0.6), math.sin(0.6)
    for y in range(int(cy - R) - 1, int(cy + R) + 2):
        v = (y + 0.5 - cy) / R
        for x in range(int(cx - R) - 1, int(cx + R) + 2):
            u = (x + 0.5 - cx) / R
            if u * u + v * v > 1:
                continue
            qx, qy = u - c0x, v - c0y
            b = qx * dx + qy * dy + r0 * dr
            c = qx * qx + qy * qy - r0 * r0
            disc = b * b - a * c
            t = 1.0
            if disc >= 0:
                s = math.sqrt(disc)
                best = None
                for tt in ((b + s) / a, (b - s) / a):
                    if r0 + tt * dr >= 0 and (best is None or tt > best):
                        best = tt
                t = 0.0 if best is None else min(1.0, max(0.0, best))
            col = lerp(hi, mid, t / 0.42) if t < 0.42 else lerp(mid, lo, (t - 0.42) / 0.58)
            hx, hy = u + 0.38, v + 0.44
            ex = hx * cr - hy * sr
            ey = hx * sr + hy * cr
            if (ex / 0.22) ** 2 + (ey / 0.13) ** 2 <= 1:
                col = lerp(col, (255, 255, 255), 0.5)
            px[x, y] = col + (255,)
    img = Image.alpha_composite(shadow, ball)
    return img.resize((n // ss, n // ss), Image.LANCZOS)


def load_font(size, mono=False):
    names = ("consolab.ttf", "DejaVuSansMono-Bold.ttf", "cour.ttf") if mono else ("arial.ttf", "DejaVuSans.ttf", "Helvetica.ttc")
    for name in names:
        try:
            return ImageFont.truetype(name, size)
        except OSError:
            pass
    try:
        return ImageFont.load_default(size)
    except TypeError:
        return ImageFont.load_default()


class Renderer:
    def __init__(self, cell):
        self.cell = cell
        self.m = max(8, cell // 5)
        self.bw = cell * 9
        self.ph = int(cell * 2.0)
        w = self.bw + 2 * self.m
        h = self.bw + 3 * self.m + self.ph
        self.W = w + (w % 2)
        self.H = h + (h % 2)
        self.py = self.m * 2 + self.bw
        self.nw = int(self.bw * 0.485)
        self.font = load_font(max(12, int(cell * 0.42)))
        self.led = load_font(max(14, int(cell * 0.62)), True)
        d = int(cell * 0.8)
        self.master = {c: make_master(PALETTE[c], d) for c in PALETTE}
        self.cache = {}
        self.base = self.make_base()

    def sprite(self, color, size):
        key = (color, size)
        sp = self.cache.get(key)
        if sp is None:
            m = self.master[color]
            f = size / 40.0
            sp = m.resize((max(1, round(m.width * f)), max(1, round(m.height * f))), Image.LANCZOS) if size != 40 else m
            self.cache[key] = sp
        return sp

    def make_base(self):
        im = Image.new("RGB", (self.W, self.H), (240, 240, 240))
        dr = ImageDraw.Draw(im)
        m, cell, bw = self.m, self.cell, self.bw
        dr.rectangle([m, m, m + bw, m + bw], fill=(143, 142, 128))
        lw = max(1, cell // 40)
        for k in range(1, 9):
            p = k * cell
            dr.line([m + p, m, m + p, m + bw], fill=(0, 0, 0), width=lw)
            dr.line([m, m + p, m + bw, m + p], fill=(0, 0, 0), width=lw)
        dr.rectangle([m, m, m + bw, m + bw], outline=(0, 0, 0), width=lw * 2)
        dr.rectangle([m, self.py, m + self.nw, self.py + self.ph], fill=(236, 236, 236))
        dr.text((m + cell // 6, self.py + cell // 8), "NEXT:", fill=(0, 0, 0), font=self.font)
        top = self.py + int(cell * 0.62)
        pad = max(2, cell // 20)
        self.nbox = (m + pad, top, m + self.nw - pad, self.py + self.ph - pad)
        dr.rectangle(self.nbox, fill=(143, 142, 128), outline=(128, 128, 128))
        self.lx0 = m + int(bw * 0.515)
        self.lx1 = m + bw
        gap = max(4, cell // 8)
        lh = (self.ph - gap) // 2
        self.led_boxes = [(self.lx0, self.py, self.lx1, self.py + lh), (self.lx0, self.py + lh + gap, self.lx1, self.py + 2 * lh + gap)]
        for b in self.led_boxes:
            dr.rectangle(b, fill=(0, 0, 0), outline=(128, 128, 128))
        return im

    def center(self, i):
        r, c = divmod(i, 9)
        return self.m + c * self.cell + self.cell // 2, self.m + r * self.cell + self.cell // 2

    def put(self, im, sp, cx, cy):
        im.paste(sp, (cx - sp.width // 2, cy - sp.height // 2), sp)

    def render(self, board, nx, score, step, ov, fl, sel):
        im = self.base.copy()
        dr = ImageDraw.Draw(im)
        for i in range(81):
            v = board[i]
            if not v:
                continue
            if i in ov:
                size = ov[i]
            elif sel is not None and sel[0] == i:
                size = sel[1]
            else:
                size = 40
            if size > 0:
                cx, cy = self.center(i)
                self.put(im, self.sprite(v, size), cx, cy)
        if fl is not None:
            cx, cy = self.center(fl[0])
            self.put(im, self.sprite(fl[1], 40), cx, cy)
        x0, y0, x1, y1 = self.nbox
        seg = (x1 - x0) / 3.0
        for k, v in enumerate(nx):
            if v:
                self.put(im, self.sprite(v, 40), int(x0 + seg * (k + 0.5)), (y0 + y1) // 2)
        for box, text, col in ((self.led_boxes[0], str(step), (255, 0, 0)), (self.led_boxes[1], str(score), (0, 255, 0))):
            tw = dr.textlength(text, font=self.led)
            th = self.led.size
            dr.text((box[2] - 8 - tw, (box[1] + box[3]) // 2 - th * 0.6), text, fill=col, font=self.led)
        return im


class VGame(cs.Game):
    def find_path(self, frm, to):
        dist = [-1] * 81
        dist[to] = 0
        q = [to]
        for x in q:
            for n in self.nbr(x):
                if not self.b[n] and dist[n] < 0:
                    dist[n] = dist[x] + 1
                    q.append(n)
        around = self.nbr(frm)
        want = -1
        for n in around:
            if dist[n] >= 0 and (want < 0 or dist[n] < want):
                want = dist[n]
        cur = frm
        path = []
        while True:
            around = self.nbr(cur)
            if path:
                want = dist[cur] - 1
            if want < 0:
                return None
            step = [n for n in around if dist[n] == want][0]
            path.append(step)
            if step == to:
                return path
            cur = step

    def spawn_cells(self, colors, src, dst):
        placed = []
        n = 0
        if self.hard and self.tab[self.rnd(10)] == 1:
            self.b[src] = colors[0]
            placed.append(src)
            n = 1
            free = [x for x in self.nbr(dst) if not self.b[x]]
            if free:
                p = free[self.rnd(len(free))]
                self.b[p] = colors[1]
                placed.append(p)
                n = 2
        while n < 3:
            if colors[n]:
                empty = [i for i in range(81) if not self.b[i]]
                if not empty:
                    break
                p = empty[self.rnd(len(empty))]
                self.b[p] = colors[n]
                placed.append(p)
            n += 1
        return placed

    def animate(self, frm, to, pre, base, per):
        segs = []

        def add(dur, ov=None, fl=None, sel=None):
            segs.append([dur, bytes(self.b), self.score, ov or {}, fl, sel])

        old_nx = self.nx[:]
        color = self.b[frm]
        k = 0
        t = 0
        while t < pre:
            d = min(BOUNCE_MS, pre - t)
            add(d, sel=(frm, BOUNCE[k % len(BOUNCE)]))
            t += d
            k += 1
        path = self.find_path(frm, to)
        self.b[frm] = 0
        self.b[to] = color
        hit = self.line_at(to) is not None
        self.b[to] = 0
        self.b[frm] = color
        fresh = None
        if not hit:
            fresh = self.colors(3)
        for p in path:
            add(STEP_MS, ov={frm: 0}, fl=(p, color))
        move = STEP_MS * len(path)
        self.b[frm] = 0
        self.b[to] = color
        cells = self.line_at(to)
        if cells:
            for s in CLEAR_SIZES:
                add(FRAME_MS, ov={c: s for c in cells})
                move += FRAME_MS
            for c in cells:
                self.b[c] = 0
            n = len(cells)
            self.score += 5 * (n - 4) * (n - 3) // 2 + 5
            alive = True
        else:
            placed = self.spawn_cells(old_nx[:], frm, to)
            for s in SPAWN_SIZES:
                add(FRAME_MS, ov={p: s for p in placed})
                move += FRAME_MS
            for p in placed:
                if self.b[p]:
                    cs_ = self.line_at(p)
                    if cs_:
                        for s in CLEAR_SIZES:
                            add(FRAME_MS, ov={c: s for c in cs_})
                            move += FRAME_MS
                        for c in cs_:
                            self.b[c] = 0
            alive = any(v == 0 for v in self.b)
        budget = base + per * len(path)
        total_move = max(move, REFRESH_MS) if fresh else move
        over = total_move - budget
        idle = budget - move
        if idle > 0:
            add(idle)
        out = []
        pos = 0
        flip = pre + REFRESH_MS
        for seg in segs:
            dur = seg[0]
            if fresh is None:
                out.append((dur, seg[1], tuple(old_nx), seg[2], seg[3], seg[4], seg[5]))
            elif pos + dur <= flip:
                out.append((dur, seg[1], tuple(old_nx), seg[2], seg[3], seg[4], seg[5]))
            elif pos >= flip:
                out.append((dur, seg[1], tuple(fresh), seg[2], seg[3], seg[4], seg[5]))
            else:
                a_ = flip - pos
                out.append((a_, seg[1], tuple(old_nx), seg[2], seg[3], seg[4], seg[5]))
                out.append((dur - a_, seg[1], tuple(fresh), seg[2], seg[3], seg[4], seg[5]))
            pos += dur
        if fresh is not None:
            self.nx = fresh
        return out, alive, over, per * len(path)


def solve(seed, hard, target):
    cache = "colorline_%s_seed%d_target%d.moves.json" % ("hard" if hard else "normal", seed, target)
    if os.path.exists(cache):
        with open(cache) as f:
            moves = [tuple(m) for m in json.load(f)]
        ok, score, _ = cs.verify(seed, hard, moves, target)
        if ok:
            print("loaded cache", cache, "moves", len(moves), "score", score)
            return moves
    compiler = cs.find_compiler()
    if not compiler:
        sys.exit("no C++ compiler found")
    exe = cs.build(compiler, tempfile.mkdtemp(prefix="colorline_"))
    for w in (20, 50, 100, 200, 400, 800):
        print("solving width", w, flush=True)
        moves = cs.run(exe, seed, w, target, 2 if hard else 1)
        if not moves:
            continue
        ok, score, _ = cs.verify(seed, hard, moves, target)
        if ok:
            with open(cache, "w") as f:
                json.dump(moves, f)
            print("solved moves", len(moves), "score", score)
            return moves
    sys.exit("solver failed")


def main():
    speed = 1.0
    rest = []
    for tok in sys.argv[1:]:
        m = re.fullmatch(r"-(\d+(?:\.\d+)?)", tok)
        if m:
            speed = float(m.group(1))
        else:
            rest.append(tok)
    ap = argparse.ArgumentParser()
    ap.add_argument("seed", nargs="?", type=int)
    ap.add_argument("target", nargs="?", type=int)
    ap.add_argument("mode", nargs="?")
    ap.add_argument("--fps", type=int, default=30)
    ap.add_argument("--cell", type=int, default=64)
    ap.add_argument("--crf", type=int, default=20)
    ap.add_argument("--preset", default="medium")
    ap.add_argument("--codec", choices=["h264", "h265"], default="h264")
    ap.add_argument("--pre", type=int, default=40)
    ap.add_argument("--base", type=int, default=600)
    ap.add_argument("--per", type=int, default=55)
    ap.add_argument("--tail", type=float, default=3.0)
    ap.add_argument("--out")
    a = ap.parse_args(rest)
    if speed <= 0:
        sys.exit("speed must be positive")
    seed = a.seed if a.seed is not None else int(input("seed: "))
    target = a.target if a.target is not None else int(input("target: "))
    mode = a.mode if a.mode is not None else input("mode (n/h): ")
    hard = mode.strip().lower().startswith("h")

    ffmpeg = shutil.which("ffmpeg")
    if not ffmpeg:
        sys.exit("ffmpeg not found")

    moves = solve(seed, hard, target)
    out = a.out or "colorline_%s_seed%d_target%d_x%s.mp4" % ("hard" if hard else "normal", seed, target, ("%g" % speed))

    rd = Renderer(a.cell)
    if a.codec == "h264":
        codec = ["-c:v", "libx264", "-preset", a.preset, "-tune", "animation"]
    else:
        codec = ["-c:v", "libx265", "-preset", a.preset, "-tag:v", "hvc1", "-x265-params", "log-level=error"]
    cmd = [ffmpeg, "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgb24",
           "-s", "%dx%d" % (rd.W, rd.H), "-r", str(a.fps), "-i", "-"] + codec + \
          ["-crf", str(a.crf), "-g", str(a.fps * 10), "-pix_fmt", "yuv420p", "-movflags", "+faststart", out]
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE)

    frame_ms = 1000.0 / a.fps * speed
    state = {"next": 0.0, "n": 0}

    def play(dur, board, nx, score, step, ov, fl, sel, end):
        img = None
        data = None
        while state["next"] < end:
            if data is None:
                data = rd.render(board, nx, score, step, ov, fl, sel).tobytes()
            proc.stdin.write(data)
            state["n"] += 1
            state["next"] += frame_ms
        return data

    g = VGame(seed, hard)
    total = len(moves)
    clock = 0.0
    last = None
    clock += 1000.0
    last = play(1000, g.b, tuple(g.nx), 0, 0, {}, None, None, clock)
    over_max = 0
    over_n = 0
    need_base = 0
    t0 = time.time()
    for k, (f, t) in enumerate(moves, 1):
        segs, alive, over, perlen = g.animate(f, t, a.pre, a.base, a.per)
        if over > 0:
            over_n += 1
        over_max = max(over_max, over)
        need_base = max(need_base, a.base + over)
        for dur, board, nx, score, ov, fl, sel in segs:
            if dur <= 0:
                continue
            clock += dur
            data = play(dur, board, nx, score, k, ov, fl, sel, clock)
            if data is not None:
                last = data
        if k % 200 == 0:
            print("rendered %d / %d  %.0fs" % (k, total, time.time() - t0), flush=True)
        if not alive:
            break
    if last is None:
        last = rd.render(g.b, g.nx, g.score, total, {}, None, None).tobytes()
    for _ in range(int(a.fps * a.tail)):
        proc.stdin.write(last)
        state["n"] += 1
    proc.stdin.close()
    proc.wait()
    ok, score, _ = cs.verify(seed, hard, moves, target)
    print("final score", g.score, "verify", ok, score)
    print("video %.1f min, %s, %.2f MB" % (state["n"] / a.fps / 60.0, out, os.path.getsize(out) / 1048576))
    if over_n:
        print("WARNING: %d steps need more time than base/per allow (worst +%d ms); safe base with per=%d: %d" %
              (over_n, over_max, a.per, need_base))
    else:
        print("timing check: every step fits within base=%d per=%d" % (a.base, a.per))


if __name__ == "__main__":
    main()
