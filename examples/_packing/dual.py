"""First spatial differentials over Arb scalars or Arb time series.

Arithmetic encloses exact first derivatives. Branch decisions must inspect
the value enclosure, and every branch used must hold on that whole box.
"""
class Dual:
    def __init__(self, value, gradient):
        self.value, self.gradient = value, list(gradient)

    def _promote(self, other):
        return other if isinstance(other, Dual) else Dual(other, [self.value*0 for _ in self.gradient])

    def __add__(self, other):
        b = self._promote(other)
        return Dual(self.value+b.value, [x+y for x, y in zip(self.gradient, b.gradient)])
    __radd__ = __add__

    def __neg__(self):
        return Dual(-self.value, [-x for x in self.gradient])

    def __sub__(self, other):
        return self+-self._promote(other)

    def __rsub__(self, other):
        return self._promote(other)+-self

    def __mul__(self, other):
        b = self._promote(other)
        return Dual(self.value*b.value, [x*b.value+self.value*y for x, y in zip(self.gradient, b.gradient)])
    __rmul__ = __mul__

    def __truediv__(self, other):
        b = self._promote(other)
        return Dual(self.value/b.value, [(x*b.value-self.value*y)/(b.value*b.value)
                                        for x, y in zip(self.gradient, b.gradient)])

    def __rtruediv__(self, other):
        return self._promote(other)/self

    def __pow__(self, n):
        if not isinstance(n, int):
            raise TypeError('Dual powers require integers')
        if n < 0:
            return 1/(self**(-n))
        result, base = self*0+1, self
        while n:
            if n % 2:
                result = result*base
            base = base*base
            n //= 2
        return result

    def sin(self):
        return Dual(self.value.sin(), [self.value.cos()*x for x in self.gradient])

    def cos(self):
        return Dual(self.value.cos(), [-self.value.sin()*x for x in self.gradient])

    def exp(self):
        value = self.value.exp()
        return Dual(value, [value*x for x in self.gradient])

    def sqrt(self):
        value = self.value.sqrt()
        return Dual(value, [x/(2*value) for x in self.gradient])

    def atan(self):
        return Dual(self.value.atan(),[x/(1+self.value*self.value) for x in self.gradient])

    def conjugate(self):
        return Dual(self.value.conjugate(), [x.conjugate() for x in self.gradient])

    @property
    def real(self):
        return Dual(self.value.real, [x.real for x in self.gradient])

    @property
    def imag(self):
        return Dual(self.value.imag, [x.imag for x in self.gradient])

    @property
    def prec(self):
        return self.value.prec

    def __getitem__(self, key):
        return self.value[key]

    def mid(self): return self.value.mid()
    def lower(self): return self.value.lower()
    def upper(self): return self.value.upper()
    def is_zero(self): return self.value.is_zero()
    def union(self, other):
        b = self._promote(other)
        return Dual(self.value.union(b.value), [x.union(y) for x, y in zip(self.gradient, b.gradient)])


def primal(x):
    return x.value if isinstance(x, Dual) else x
