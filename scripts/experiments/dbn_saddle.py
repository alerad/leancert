#!/usr/bin/env python3
"""DBN saddle diagnostics; NOT interval-certified and NOT a proof.

Requires sympy and mpmath. Integrates finite windows on positive-real-part
contours, using logarithmic Gamma ratios to avoid catastrophic scaling.
Window/precision/contour agreement checks numerical stability, not tail bounds.
Run from the repository root: python3 scripts/experiments/dbn_saddle.py
"""
import mpmath as mp
import sympy as sp


def symbolic_checks():
    a, s, u, ell, L = sp.symbols('a s u ell L', nonzero=True)
    phase = sp.expand(((a*ell-u)**2-(a*ell)**2)/(4*a)+ell*u/2)
    assert sp.simplify(phase-u**2/(4*a)) == 0
    A = 1/(4*a)+1/(4*s)
    assert sp.simplify(a-1/(4*A)-a*a/(s+a)) == 0
    # Stirling log-derivative of gamma(s)=s(s-1)pi^(-s/2)Gamma(s/2)/2.
    eps = sp.Symbol('eps')
    residual = 1/s+1/(s-1)-1/(2*s)-1/(6*s**2)
    print('Exact linear cancellation:', phase)
    print('Formal log-gamma derivative remainder:',
          sp.series(residual.subs(s,1/eps),eps,0,3))
    # Gaussian moments on u=2aL+2i sqrt(a) v with density exp(-v^2)/sqrt(pi).
    correction = sp.expand(sp.Rational(3,2)*(2*a*L)+(4*a*a*L*L-2*a)/4)
    print('Predicted coefficient of 1/s:', correction)


def log_prefactor(z):
    # Analytic logarithm on the upper half-plane; along integration contours
    # Re(z)>=2, the expression also stays well-defined below the real axis.
    return (mp.log(z)+mp.log(z-1)-mp.log(2)
            -z*mp.log(mp.pi)/2+mp.loggamma(z/2))


def term_ratio(a, x, y, L, width=10, shift=0):
    """Finite-window estimate of normalizedContourTerm / (exp(-aL²)n^-s).

    n is represented by L=log(n); real L>=0 is also allowed for diagnostics.
    The full infinite contour equals the coefficient after a right-half-plane
    contour shift; this script does not certify that shift or the omitted tail.
    """
    a, x, L = map(mp.mpf, (a, x, L))
    s = mp.mpc(x, y)
    c = 2*mp.sqrt(a)
    d = max(mp.mpf(2), x+2*a*L)+shift-x
    ell, base = mp.log(s/(2*mp.pi)), log_prefactor(s)

    def integrand(v):
        u = d+1j*c*v
        return mp.exp(log_prefactor(s+u)-base-ell*u/2
                      +u*u/(4*a)-u*L+a*L*L)

    return mp.quad(integrand, [-width,-4,0,4,width])/mp.sqrt(mp.pi)


def main():
    symbolic_checks()
    mp.mp.dps = 35
    print('\na     x    n    y      |R-1|        |s(R-1)-P|')
    for a,x,n in [('0.25',2,1),('0.25',2,10),('0.25',-2,10),('1',-2,100)]:
        a = mp.mpf(a)
        L = mp.log(n)
        P = a*a*L*L+3*a*L-a/2
        for y in [40,160,640]:
            R = term_ratio(a,x,y,L)
            print(str(a),x,n,y,mp.nstr(abs(R-1),7),
                  mp.nstr(abs(mp.mpc(x,y)*(R-1)-P),7))

    base = term_ratio('0.25',-2,160,mp.log(10))
    wider = term_ratio('0.25',-2,160,mp.log(10),width=12)
    shifted = term_ratio('0.25',-2,160,mp.log(10),shift=mp.mpf('0.5'))
    with mp.workdps(55):
        precise = term_ratio('0.25',-2,160,mp.log(10),width=12)
    discrepancies = [abs(base-wider),abs(base-shifted),abs(base-precise)]
    print('\nWindow, contour, precision discrepancies:',
          ', '.join(mp.nstr(v,6) for v in discrepancies))
    assert max(discrepancies) < mp.mpf('1e-25'), 'Numerical stability check failed'

    print('\nGrowing log(n)=sqrt(y)/a diagnostic (real L, not integer n):')
    print('y      |R-1|       |R-exp(-i)|')
    for y in [160,640,2560]:
        a = mp.mpf('0.25')
        R = term_ratio(a,2,y,mp.sqrt(y)/a)
        print(y,mp.nstr(abs(R-1),7),mp.nstr(abs(R-mp.exp(-1j)),7))
    print('\nAll numerical integrals are truncated and uncertified.')


if __name__ == '__main__':
    main()
