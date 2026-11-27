from mpmath import *
mp.dps=20
xi=lambda s: s*(s-1)*pi**(-s/2)*gamma(s/2)*zeta(s)/2
def dlog(s): return diff(xi,s)/xi(s)
B=-(dlog(mpf(1)+mpf("1e-8"))+dlog(mpf(1)-mpf("1e-8")))/2
print("B",B, "lambda1", 1+euler/2-log(4*pi)/2)
N=300
zs=[zetazero(k) for k in range(1,N+1)]
s=mpf(3)
S=B+sum(1/(s-r)+1/r+1/(s-r.conjugate())+1/r.conjugate() for r in zs)
print("hadamard s=3",S,"actual",dlog(s))
# generating function: sum_n lam_n z^(n-1) = (1/(1-z)^2) xi'/xi(1/(1-z))
z=mpf('0.1')
lam=lambda n: sum(2*(1-(1-1/r)**n).real*1 + 2*(1-(1-1/r.conjugate())**n).real*0 for r in zs)
G=sum(lam(n)*z**(n-1) for n in range(1,25))
print("series",G,"lhs",dlog(1/(1-z))/(1-z)**2)
