#!/bin/bash
# Lean 4 + Mathlib for Left to Solve work: Lean v4.33.1, formal-conjectures pin 9097e2f.
# Installs to /opt/lean (formal-conjectures checkout at /opt/lean/fc). Never fails the session start.
L=/opt/lean
mkdir -p "$L" && cd "$L" || exit 0
export PATH="$HOME/.elan/bin:$PATH"
if ! command -v elan >/dev/null; then
  curl -sSfL -o elan-init.sh https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    && sh elan-init.sh -y --default-toolchain none --no-modify-path || true
fi
grep -q 'elan/bin' "$HOME/.bashrc" 2>/dev/null || echo 'export PATH="$HOME/.elan/bin:$PATH"' >> "$HOME/.bashrc"
if [ ! -x lean-4.33.1-linux/bin/lean ]; then
  pip install -q zstandard || true
  curl -sSfL -o lean.tar.zst https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst \
    && python3 -c "import zstandard as z,tarfile as t; t.open(fileobj=z.ZstdDecompressor().stream_reader(open('lean.tar.zst','rb')),mode='r|').extractall('.')"
  rm -f lean.tar.zst
fi
elan toolchain list 2>/dev/null | grep -q v4.33.1 || elan toolchain link leanprover/lean4:v4.33.1 "$L/lean-4.33.1-linux" || true
[ -d fc/.git ] || git clone -q --filter=blob:none --no-checkout https://github.com/google-deepmind/formal-conjectures fc || true
(cd fc && git fetch -q --depth 1 origin 9097e2f90e66d2f6244209cb1c07f7120d17ec53 \
  && git checkout -q 9097e2f90e66d2f6244209cb1c07f7120d17ec53 && timeout 2400 lake exe cache get > /dev/null 2>&1) || true
exit 0
