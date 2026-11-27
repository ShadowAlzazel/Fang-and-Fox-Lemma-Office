from fractions import Fraction as F
import sys
# Numerical check of OEIS A127752 and its mod-2 conjecture (Kumi-San).
# Usage: python3 check.py [N]   (N = size of the exact inverse, default 300)
import os, urllib.request
BFILE = '/tmp/b127752.txt'
if not os.path.exists(BFILE):
    urllib.request.urlretrieve('https://oeis.org/A127752/b127752.txt', BFILE)
b={}
for l in open(BFILE):
    l=l.split()
    if len(l)==2 and l[0].isdigit(): b[int(l[0])]=int(l[1])
def A(n,k): return F(1,3*n+1) if k<=n<=2*k else F(0)
N=int(sys.argv[1]) if len(sys.argv)>1 else 300
# exact inverse by forward substitution: B = A^{-1}, lower triangular
B=[[F(0)]*N for _ in range(N)]
for j in range(N):
    for i in range(j,N):
        s=F(1 if i==j else 0)-sum(A(i,k)*B[k][j] for k in range(j,i))
        B[i][j]=s/A(i,i)
# verify A*B = I
for i in range(N):
    for j in range(N):
        assert sum(A(i,k)*B[k][j] for k in range(N))==(1 if i==j else 0)
rows=[sum(B[i]) for i in range(N)]
assert all(r.denominator==1 for r in rows)
def r(n): return 1 if n==0 else (3 if n%2==0 else r(n//2)+3)
def nu2(x):
    c=0
    while x%2==0: x//=2;c+=1
    return c
A035263=lambda n: nu2(2*n)%2
print("matrix-inverse N=%d: row sums == recurrence:"%N, all(rows[i]==r(i) for i in range(N)))
print("b-file (%d terms) == recurrence:"%len(b), all(b[i]==r(i) for i in b))
print("conjecture a(n) mod 2 == A035263(n+1) for n<10^6:", all(r(n)%2==A035263(n+1) for n in range(10**6)))
print("Black Swan form 1-(nu2(n+1) mod 2):", all(r(n)%2==1-nu2(n+1)%2 for n in range(10**6)))
print("block sums: sum_{ceil(n/2)<=k<=n} a(k) == 3n+1 for n<2000:", all(sum(r(k) for k in range((n+1)//2,n+1))==3*n+1 for n in range(2000)))
print("closed form:", all(r(n)==(3*nu2(n+1)+1 if (n+1)&n==0 else 3*nu2(n+1)+3) for n in range(10**6)))
