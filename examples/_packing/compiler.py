"""Run the current Lean total algorithm and interpret its finite output.

Every invocation builds the source-bound proof target. No historic audit flag,
precomputed geometric oracle, search timeout, or fixed precision cap is used.
"""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

from .polynomial import nat_unpair
from .real_names import NamedFiniteHamiltonian, lower_epsilon


REPOSITORY = Path(__file__).resolve().parents[2]


def source_hashes(repository=REPOSITORY):
    paths = [repository / name for name in
             ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'examples/Packing.lean')]
    for name in ('SymplecticPacking', 'verification', 'vendor'):
        paths.extend((repository / name).rglob('*.lean'))
    return {str(p.relative_to(repository)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}


def lake_command():
    lake = shutil.which('lake')
    if lake is None:
        fallback = Path.home() / '.elan/bin/lake'
        if fallback.is_file():
            lake = str(fallback)
    if lake is None:
        raise RuntimeError('Install Elan and the pinned Lean toolchain; lake was not found')
    return lake


class PackingHamiltonian(NamedFiniteHamiltonian):
    """The output of a successful execution of the proof-carrying Lean function.

    The JSON transcript is not itself a kernel proof. The packing guarantee
    comes from the checked `NativePacking.Output` type and this execution path.
    """
    def __init__(self, k, epsilon_lower, output, provenance):
        if (output.get('format') != 'native-packing-search-output-v1'
                or output.get('whole_closed_ball_certificate') is not True
                or output.get('coordinate_order') != 'q1,q2,p1,p2'
                or output.get('k') != k):
            raise ArithmeticError('incompatible output from the Lean compiler')
        radius = Fraction(output['radius_numerator'], output['radius_denominator'])
        if not radius > 0 or not 1 - epsilon_lower < Fraction(k) / radius**4:
            raise ArithmeticError('the output fails the original strict density requirement')
        stage = output['stage']
        fields = []
        for _ in range(5):
            field, stage = nat_unpair(stage)
            fields.append(field)
        if fields[1] != output['box']:
            raise ArithmeticError('the output cutoff differs from its candidate code')
        self.k, self.epsilon_lower, self.radius = k, epsilon_lower, radius
        self.output, self.provenance = output, provenance
        super().__init__(output['box'], output['program'])

    def description(self):
        return dict(k=self.k, epsilon_lower=str(self.epsilon_lower), radius=str(self.radius),
                    density=str(Fraction(self.k) / self.radius**4),
                    finite_hamiltonian=self.output, provenance=self.provenance)


def compile_packing(k, epsilon, *, run_directory=None, progress=None):
    """Compile for every k >= 10 and valid epsilon in (0,1), without a time cap.

    Exact rationals are accepted directly. A callable epsilon(p) must return
    a rational within 2**(-p) of one fixed real epsilon. All calls must finish.
    General dense-input search may take an astronomically long time.
    """
    if isinstance(k, bool) or not isinstance(k, int) or k < 10:
        raise ValueError('integer k at least ten required')
    lower, name_record = lower_epsilon(epsilon)
    if run_directory is None:
        run_directory = REPOSITORY / '.lake/packing' / str(time.time_ns())
    directory = Path(run_directory).resolve()
    directory.mkdir(parents=True, exist_ok=False)
    sources = source_hashes()
    lake = lake_command()
    if progress:
        progress(dict(stage='building current executable proof target'))
    with (directory / 'build.log').open('w') as log:
        subprocess.run([lake, 'build', 'verification.Executable'], cwd=REPOSITORY,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    arguments = [lake, 'env', 'lean', '--run', 'examples/Packing.lean', 'solve',
                 str(k), str(lower.numerator), str(lower.denominator)]
    outputs, messages = [], []
    started = time.monotonic()
    log_path = directory / 'native.log'
    with log_path.open('w') as log:
        process = subprocess.Popen(arguments, cwd=REPOSITORY, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True, bufsize=1)
        if progress:
            progress(dict(stage='running total certificate search', pid=process.pid, k=k))
        try:
            for line in process.stdout:
                log.write(line)
                log.flush()
                if line.startswith('{'):
                    outputs.append(json.loads(line))
                else:
                    messages.append(line.rstrip())
            code = process.wait()
        finally:
            if process.poll() is None:
                process.terminate()
                process.wait()
            process.stdout.close()
    if code != 0 or len(outputs) != 1:
        raise ArithmeticError(f'Lean compiler failed: exit={code}; see {log_path}')
    for name in ('solveRational', 'solveName'):
        expected = f"'NativePacking.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
        if expected not in messages:
            raise ArithmeticError('unexpected proof axiom dependencies; see the native log')
    if source_hashes() != sources:
        raise ArithmeticError('proof sources changed during compilation')
    provenance = dict(epsilon_input=name_record, proof_sources_sha256=sources,
                      native_log=str(log_path),
                      native_log_sha256=hashlib.sha256(log_path.read_bytes()).hexdigest(),
                      search_seconds=time.monotonic() - started)
    result = PackingHamiltonian(k, lower, outputs[0], provenance)
    (directory / 'output.json').write_text(json.dumps(result.description(), indent=2) + '\n')
    return result
