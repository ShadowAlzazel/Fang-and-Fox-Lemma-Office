"""Figure: w = 1 - 1/rho for the first 100 zeta zeros (and conjugates). Run in the mpmath venv:
   python figures/make_figure.py   (from results/li-criterion/)"""
from mpmath import mp, zetazero, mpc
import csv
mp.dps = 20
N = 100
rows = []
for k in range(1, N+1):
    r = zetazero(k)
    w = 1 - 1/r
    rows.append((k, float(r.real), float(r.imag), float(w.real), float(w.imag), float(abs(w))))
with open('figures/zeta_zeros_on_circle.csv', 'w', newline='') as f:
    wr = csv.writer(f); wr.writerow(['k', 're_rho', 'im_rho', 're_w', 'im_w', 'abs_w'])
    for r in rows: wr.writerow([r[0]] + [f'{x:.12f}' for x in r[1:]])
print('max | |w|-1 | =', max(abs(r[5]-1) for r in rows))

# left panel: full unit circle
cx, cy, R = 215, 250, 160
P = lambda x, y: (cx + R*x, cy - R*y)
dots = ''.join(f'<circle cx="{P(r[3], s*r[4])[0]:.1f}" cy="{P(r[3], s*r[4])[1]:.1f}" r="2.4" class="dot"/>' for r in rows for s in (1, -1))
rho = mpc(0.85, 2.5)  # SCHEMATIC off-line point, not a zero
w = 1 - 1/rho
ghost = [w, w.conjugate(), 1/w, 1/w.conjugate()]
gh = ''.join(f'<circle cx="{P(float(g.real), float(g.imag))[0]:.1f}" cy="{P(float(g.real), float(g.imag))[1]:.1f}" r="4" class="gh"/>' for g in ghost)
# zoom box around w = 1
th = 0.075
bx0, bx1 = P(1 - 0.02, th*1.1)[0], P(1 + 0.02, 0)[0]
by0, by1 = P(1, th*1.1)[1], P(1, -th*1.1)[1]

# right panel: zoom (x-1, y) scaled by S, centered at (560, 250)
S = 2000.0
zx, zy = 575, 250
Z = lambda x, y: (zx + S*(x-1), zy - S*y)
import math
arc = ' '.join(f'{Z(math.cos(t), math.sin(t))[0]:.1f},{Z(math.cos(t), math.sin(t))[1]:.1f}' for t in [i*th*1.1/60 - th*1.1 + 0 for i in range(0, 121)] if False) or \
      ' '.join(f'{Z(math.cos(t), math.sin(t))[0]:.1f},{Z(math.cos(t), math.sin(t))[1]:.1f}' for t in [(-th*1.1 + 2*th*1.1*i/120) for i in range(121)])
zdots = ''.join(f'<circle cx="{Z(r[3], s*r[4])[0]:.1f}" cy="{Z(r[3], s*r[4])[1]:.1f}" r="2.4" class="dot"/>' for r in rows for s in (1, -1))
svg = f'''<svg viewBox="0 0 720 470" xmlns="http://www.w3.org/2000/svg" role="img" aria-label="The first 100 zeta zeros, sent by w = 1 - 1/rho, lie exactly on the unit circle with their conjugates, all within a short arc near w = 1; a schematic off-line zero would land off the circle in a pair w and 1 over w-bar">
<style>.ax{{stroke:var(--muted,#586275);stroke-width:1}}.tk{{font:11px 'IBM Plex Mono',monospace;fill:var(--muted,#586275)}}.ci{{fill:none;stroke:var(--line,#2563b8);stroke-width:1.8}}.dot{{fill:var(--petal,#cf5428)}}.gh{{fill:none;stroke:var(--muted,#586275);stroke-width:1.3;stroke-dasharray:3 3}}.lg{{font:12px 'Instrument Sans',sans-serif;fill:var(--ink,#1b2230)}}.bx{{fill:none;stroke:var(--muted,#586275);stroke-width:.8;stroke-dasharray:4 3}}</style>
<text x="20" y="22" class="lg"><tspan fill="var(--line,#2563b8)">&#9679;</tspan> unit circle |w| = 1, the image of Re &#961; = 1/2</text>
<text x="20" y="40" class="lg"><tspan fill="var(--petal,#cf5428)">&#9679;</tspan> w = 1 &#8722; 1/&#961; for the first 100 zeros and their conjugates</text>
<text x="20" y="58" class="lg"><tspan fill="var(--muted,#586275)">&#9675;</tspan> dashed: where a schematic off-line zero (0.85 + 2.5i, not a real zero) would land: w, conj(w), 1/w, 1/conj(w)</text>
<line x1="40" x2="390" y1="{cy}" y2="{cy}" class="ax"/><line x1="{cx}" x2="{cx}" y1="75" y2="430" class="ax"/>
<circle cx="{cx}" cy="{cy}" r="{R}" class="ci"/>
<text x="{cx+R+16}" y="{cy+36}" class="tk">1</text><text x="{cx-R-14}" y="{cy+14}" class="tk">-1</text><text x="{cx+6}" y="{cy-R-6}" class="tk">i</text><text x="{cx+6}" y="{cy+R+16}" class="tk">-i</text>
{dots}{gh}
<rect x="{bx0:.1f}" y="{by0:.1f}" width="{bx1-bx0:.1f}" height="{by1-by0:.1f}" class="bx"/>
<text x="{cx}" y="452" class="tk" text-anchor="middle">the whole circle</text>
<polyline points="{arc}" class="ci"/>
{zdots}
<text x="{zx-70}" y="{zy-S*th*1.1-10:.0f}" class="tk">zoom &#215;2000, both axes, at w = 1</text>
<text x="{zx}" y="452" class="tk" text-anchor="middle">all 200 points sit on the arc (|&#952;| &lt; 0.075)</text>
</svg>'''
open('figures/unit_circle.svg', 'w').write(svg)
