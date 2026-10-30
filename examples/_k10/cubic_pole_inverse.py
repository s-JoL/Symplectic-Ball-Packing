"""A validated projective inverse at the Weierstrass pole.

The wp chart is singular at the lattice origin. Use instead
x=Z0/(Z1-Z2), y=(Z1+Z2)/(Z1-Z2). The Fermat equation becomes
y^3+3y+4x^3=0, so two solutions with the same x and |y|<1/2
must coincide. A complex contraction certifies the local inverse x(z).
"""
from flint import arb,acb,ctx


def near_pole(Z):
    denominator=Z[1]-Z[2]
    return (not denominator.contains(0) and abs(Z[0]/denominator).upper()<arb('1e-4')
            and abs((Z[1]+Z[2])/denominator).upper()<arb(1)/2)


def local_coordinate(C,Z):
    with ctx.workprec(C.bits):
        denominator=Z[1]-Z[2]
        if denominator.contains(0):raise ArithmeticError('the pole inverse chart denominator is unresolved')
        target=Z[0]/denominator
        other=(Z[1]+Z[2])/denominator
        if not abs(other).upper()<arb(1)/2:raise ArithmeticError('point is outside the local pole branch')
        def data(z):
            raw,derivative=C._raw(z)
            D=raw[1]-raw[2];Dp=derivative[1]-derivative[2]
            return raw[0]/D,(derivative[0]*D-raw[0]*Dp)/(D*D),raw
        f0,derivative,_=data(acb(0));slope=derivative.mid()
        if slope.contains(0):raise ArithmeticError('pole coordinate has unresolved derivative')
        radius=arb('1/1024')
        box=acb(arb(0,radius),arb(0,radius))
        _,D,raw=data(box)
        kappa=abs(1-D/slope).upper()
        residual=abs((target-f0)/slope).upper()
        if not kappa<arb(1)/2 or not residual+kappa*radius<radius:
            raise ArithmeticError('pole inverse contraction was not certified')
        if not abs((raw[1]+raw[2])/(raw[1]-raw[2])).upper()<arb(1)/2:
            raise ArithmeticError('pole inverse does not isolate its Fermat branch')
        # Banach now proves the unique true inverse. Each subsequent
        # residual enclosure contracts that already established root.
        centre=acb(0);error=radius
        for _ in range(max(32,C.bits)):
            z=centre+acb(arb(0,error),arb(0,error))
            f,D,_=data(z)
            fcentre,_,_=data(centre)
            contraction=abs(1-D/slope).upper()
            if not contraction<1:raise ArithmeticError('pole inverse lost its derivative bound')
            correction=(target-fcentre)/slope
            newcentre=(centre+correction).mid()
            # Every true root obeys |z-c| <= residual/(1-kappa).
            newerror=(abs(correction).upper()/(1-contraction)).upper()
            if newerror<arb(2)**(-C.bits//2):
                return centre+acb(arb(0,newerror),arb(0,newerror))
            if newerror<error/2:
                # Recentring around the Newton candidate also retains
                # the old residual-to-root bound by the triangle law.
                shifted=(abs(centre-newcentre).upper()+newerror).upper()
                if shifted<error:centre,error=newcentre,shifted
                else:error=newerror
            else:
                # Standard interval Newton around its exact midpoint.
                residual=(target-fcentre)/slope
                radius_bound=(abs(residual).upper()/(1-contraction)).upper()
                if not radius_bound<error:break
                error=radius_bound
        z=centre+acb(arb(0,error),arb(0,error))
        if not z.is_finite():raise ArithmeticError('pole inverse enclosure is nonfinite')
        return z
