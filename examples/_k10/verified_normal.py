"""Arb validation of the two homogeneous normal-transfer ODEs."""
import math
from flint import arb, acb, arb_mat, arb_series, acb_series, ctx
from .verified_flow import integrate
from .dual import Dual


def _complex(re, im=None):
    if isinstance(re, Dual) or isinstance(im, Dual):
        template = re if isinstance(re, Dual) else im
        re = template._promote(re)
        im = template._promote(0 if im is None else im)
        # Promote constants to series before combining their coefficients.
        def series(x):
            return x if hasattr(x, 'prec') else arb_series([x], prec=template.value.prec)
        return Dual(_complex(series(re.value), series(im.value)),
                    [_complex(series(a), series(b)) for a, b in zip(re.gradient, im.gradient)])
    if im is None:
        return acb_series([acb(re[k]) for k in range(re.prec)], prec=re.prec)
    return acb_series([acb(re[k], im[k]) for k in range(re.prec)], prec=re.prec)


def _conjugate(z):
    if isinstance(z, Dual):
        return Dual(_conjugate(z.value), [_conjugate(x) for x in z.gradient])
    return acb_series([z[k].conjugate() for k in range(z.prec)], prec=z.prec)


def _parts(z):
    if isinstance(z, Dual):
        value = _parts(z.value)
        derivatives = [_parts(x) for x in z.gradient]
        return tuple(Dual(value[j], [x[j] for x in derivatives]) for j in (0, 1))
    return (arb_series([z[k].real for k in range(z.prec)], prec=z.prec),
            arb_series([z[k].imag for k in range(z.prec)], prec=z.prec))


def _norm2(z):
    if isinstance(z, Dual):
        return Dual(_norm2(z.value), [_complex(_parts(d*_conjugate(z.value)+z.value*_conjugate(d))[0])
                                     for d in z.gradient])
    re, im = _parts(z)
    squared = re*re+im*im
    # The polynomial backend can use generic products at coefficient zero;
    # use the real square range there, including boxes crossing zero.
    def square(x):
        if x.contains(0):
            bound = abs(x).upper()
            return arb(0).union(bound*bound)
        return x*x
    squared[0] = square(re[0])+square(im[0])
    return _complex(squared)


def _normal(z):
    f = sum(q*q*q for q in z)
    N = [3*_conjugate(q)*_conjugate(q)-3*_conjugate(f)*q for q in z]
    g = sum(_norm2(q) for q in N)
    return f, N, g


def horizontal_field(d):
    def field(t, state):
        z = [_complex(state[j], state[j+4]) for j in range(3)]
        w = _complex(state[3], state[7])
        t = _complex(t)
        _, N, g = _normal(z)
        w2 = _norm2(w)
        mass = 1+w2
        a, b = (1+(1-3*d)*w2)/mass, d/(mass*mass)
        denominator = g/a+t*t/b
        dz = [w*q/(a*denominator) for q in N]
        dz.append(-t*w/(b*denominator))
        parts = [_parts(q) for q in dz]
        return [q[0] for q in parts]+[q[1] for q in parts]
    field.jacobian = lambda t, state: _jacobian(t, state, d, horizontal=True)
    return field


def return_field(d):
    def field(t, state):
        z = [_complex(state[j], state[j+3]) for j in range(3)]
        t = _complex(t)
        f, N, g = _normal(z)
        f2 = _norm2(f)
        mass = 1+f2
        a, b = (1+(1-3*(1-t)*d)*f2)/mass, (1-t)*d/(mass*mass)
        dz = [d/2*f*q/(mass*(a+b*g)) for q in N]
        parts = [_parts(q) for q in dz]
        return [q[0] for q in parts]+[q[1] for q in parts]
    field.jacobian = lambda t, state: _jacobian(t, state, d, horizontal=False)
    return field


def _jacobian(t, state, d, horizontal):
    """Real Jacobian of the SAME rational extension, including off-sphere points."""
    size = 4 if horizontal else 3
    z = [acb(state[j], state[j+size]) for j in range(3)]
    f = sum(q*q*q for q in z)
    N = [3*q.conjugate()*q.conjugate()-3*f.conjugate()*q for q in z]
    g = sum(abs(q)*abs(q) for q in N)
    if horizontal:
        w = acb(state[3], state[7])
        w2 = abs(w)*abs(w)
        mass = 1+w2
        a, b = (1+(1-3*d)*w2)/mass, d/(mass*mass)
        den = g/a+t*t/b
        velocity = [w*q/(a*den) for q in N]+[-t*w/(b*den)]
    else:
        mass = 1+abs(f)*abs(f)
        s = 1-t
        a, b = (1+(1-3*s*d)*(mass-1))/mass, s*d/(mass*mass)
        den = a+b*g
        velocity = [d/2*f*q/(mass*den) for q in N]
    columns = []
    for j in range(2*size):
        dz = [acb(1 if j == k else 0, 1 if j == k+size else 0) for k in range(3)]
        df = sum(3*q*q*dq for q, dq in zip(z, dz))
        dN = [6*q.conjugate()*dq.conjugate()-3*df.conjugate()*q-3*f.conjugate()*dq
              for q, dq in zip(z, dz)]
        dg = 2*sum(q.conjugate()*dq for q, dq in zip(N, dN)).real
        if horizontal:
            dw = acb(1 if j == 3 else 0, 1 if j == 7 else 0)
            dm = 2*(w.conjugate()*dw).real
            da, db = -3*d*dm/(mass*mass), -2*d*dm/(mass*mass*mass)
            dden = dg/a-g*da/(a*a)-t*t*db/(b*b)
            dv = [(dw*q+w*dq)/(a*den)-v*(da/a+dden/den)
                  for q, dq, v in zip(N, dN, velocity[:3])]
            dv.append(-t*dw/(b*den)-velocity[3]*(db/b+dden/den))
        else:
            dm = 2*(f.conjugate()*df).real
            da, db = -3*s*d*dm/(mass*mass), -2*s*d*dm/(mass*mass*mass)
            dden = da+db*g+b*dg
            dv = [d/2*(df*q+f*dq)/(mass*den)-v*(dm/mass+dden/den)
                  for q, dq, v in zip(N, dN, velocity)]
        columns.append([q.real for q in dv]+[q.imag for q in dv])
    return arb_mat([[columns[j][i] for j in range(2*size)] for i in range(2*size)])


def normal_to_ball(initial, d, **options):
    bits = options.get('bits', 160)
    with ctx.workprec(bits):
        d = arb(d)
        initial = list(map(acb, initial))
        real = [z.real for z in initial]+[z.imag for z in initial]
        horizontal = integrate(horizontal_field(d), real, **options)
        graph = [acb(horizontal.endpoint[j], horizontal.endpoint[j+4]) for j in range(3)]
        norm = sum(abs(z)**2 for z in graph).sqrt()
        graph = [z/norm for z in graph]
        returned = integrate(return_field(d), [z.real for z in graph]+[z.imag for z in graph], **options)
        z = [acb(returned.endpoint[j], returned.endpoint[j+3]) for j in range(3)]
        norm = sum(abs(q)**2 for q in z).sqrt()
        if not abs(z[0]) > 0:
            raise ArithmeticError('the final ball chart denominator is not certified nonzero')
        q = [value*z[0].conjugate()/(norm*abs(z[0])*arb.pi().sqrt()) for value in z[1:]]
        return tuple([w.real for w in q]+[w.imag for w in q]), dict(
            accepted_steps=horizontal.accepted_steps+returned.accepted_steps,
            rejected_steps=horizontal.rejected_steps+returned.rejected_steps,
            maximum_coordinate_radius=math.nextafter(max(float(x.rad()) for x in [w.real for w in q]+[w.imag for w in q]), math.inf),
            bits=bits, order=options.get('order', 16), ode_error_validated=True)
