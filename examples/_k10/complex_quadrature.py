"""Keep Python callbacks on their owning thread during FLINT integration.

python-flint 0.9.0 callbacks reached from FLINT's gl_worker threads can
segfault in Python allocation. Native algebra can still use FLINT threads;
independent integrals run in the existing process pool.
"""
from contextlib import contextmanager
from flint import acb,ctx


@contextmanager
def callback_threads():
    previous=ctx.threads
    ctx.threads=1
    try:yield
    finally:ctx.threads=previous


def integrate(function,a,b,**options):
    with callback_threads():
        return acb.integral(function,a,b,**options)
