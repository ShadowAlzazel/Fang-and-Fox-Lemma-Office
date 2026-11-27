"""Figures for the A127752 page (Kumi-San). Writes a_of_n.svg and parity.svg.
Pure Python, no dependencies. Values come from the recursion r, which the Lean file
proves equal to the row sums of the inverse triangle (a127752_eq_r)."""
def r(n): return 1 if n == 0 else (3 if n % 2 == 0 else r(n // 2) + 3)
def nu2(x):
    c = 0
    while x % 2 == 0: x //= 2; c += 1
    return c
P = "var(--petal,#cf5428)"; L = "var(--line,#2563b8)"; M = "var(--muted,#586275)"; R = "var(--rule,#d8dde7)"; I = "var(--ink,#1b2230)"
FONT = 'font-family="IBM Plex Mono,monospace"'

def fig_a(N=128, W=720, H=280):
    x0, y0, top = 40, H - 40, 16
    ymax = 22
    bw = (W - x0 - 10) / N
    sy = lambda v: y0 - (y0 - top) * v / ymax
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" role="img" aria-label="a(n) for n = 0 to {N-1}">']
    for v in range(0, ymax + 1, 3):
        out.append(f'<line x1="{x0}" x2="{W-10}" y1="{sy(v):.1f}" y2="{sy(v):.1f}" style="stroke:{R}" stroke-width="0.6"/>')
        out.append(f'<text x="{x0-6}" y="{sy(v)+4:.1f}" text-anchor="end" font-size="10" {FONT} style="fill:{M}">{v}</text>')
    for n in range(N):
        a = r(n); col = P if a % 2 else L
        x = x0 + n * bw
        out.append(f'<rect x="{x+0.6:.2f}" y="{sy(a):.2f}" width="{bw-1.2:.2f}" height="{y0-sy(a):.2f}" style="fill:{col}"><title>a({n}) = {a}, ν₂({n+1}) = {nu2(n+1)}</title></rect>')
    k = 0
    while 2 ** k - 1 < N:
        n = 2 ** k - 1; x = x0 + (n + 0.5) * bw
        out.append(f'<text x="{x:.1f}" y="{y0+14}" text-anchor="middle" font-size="9.5" {FONT} style="fill:{M}">{n}</text>')
        k += 1
    out.append(f'<text x="{(x0+W)/2}" y="{H-6}" text-anchor="middle" font-size="10.5" {FONT} style="fill:{M}">n (ticks at n = 2^k − 1, where a(n) = 3k + 1)</text>')
    out.append(f'<rect x="{W-200}" y="{top}" width="10" height="10" style="fill:{P}"/><text x="{W-185}" y="{top+9}" font-size="10.5" {FONT} style="fill:{I}">a(n) odd</text>')
    out.append(f'<rect x="{W-110}" y="{top}" width="10" height="10" style="fill:{L}"/><text x="{W-95}" y="{top+9}" font-size="10.5" {FONT} style="fill:{I}">a(n) even</text>')
    out.append('</svg>')
    return "\n".join(out)

def fig_parity(N=64, W=720):
    x0 = 150; cw = (W - x0 - 6) / N; ch = 22
    rows = [("a(n) mod 2", lambda n: r(n) % 2),
            ("ν₂(2(n+1)) mod 2", lambda n: nu2(2 * (n + 1)) % 2),
            ("kneading", None)]
    H = 30 + ch * len(rows) + 30
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" role="img" aria-label="parity of a(n) against the period-doubling sequence">']
    for i, (lab, f) in enumerate(rows):
        y = 20 + i * (ch + 4)
        out.append(f'<text x="{x0-8}" y="{y+15}" text-anchor="end" font-size="11" {FONT} style="fill:{I}">{lab}</text>')
        for n in range(N):
            bit = (r(n) % 2) if f is None else f(n)
            x = x0 + n * cw
            if f is None:
                out.append(f'<text x="{x+cw/2:.1f}" y="{y+15}" text-anchor="middle" font-size="10" {FONT} style="fill:{P if bit else L}">{"R" if bit else "L"}</text>')
            else:
                out.append(f'<rect x="{x+0.5:.2f}" y="{y}" width="{cw-1:.2f}" height="{ch}" rx="1.5" style="fill:{P if bit else L}"><title>n = {n}: {bit}</title></rect>')
    y = 20 + len(rows) * (ch + 4) + 14
    for n in range(0, N, 8):
        out.append(f'<text x="{x0+(n+0.5)*cw:.1f}" y="{y}" text-anchor="middle" font-size="9.5" {FONT} style="fill:{M}">{n}</text>')
    out.append('</svg>')
    return "\n".join(out)

assert all(r(n) % 2 == nu2(2 * (n + 1)) % 2 for n in range(4096))
open("a_of_n.svg", "w").write(fig_a())
open("parity.svg", "w").write(fig_parity())
print("wrote a_of_n.svg, parity.svg")
