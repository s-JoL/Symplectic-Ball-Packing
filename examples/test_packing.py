"""Independent exact fixtures and closed-form flows for the uniform interpreter.

Set PACKING_NATIVE=1 to exercise actual Lean compilation and dense-seed rejection.
Finite tests do not substitute for the universal Lean return-type theorem.
"""
from fractions import Fraction
import json
import os
from pathlib import Path
import subprocess
import unittest
from unittest.mock import patch

from flint import arb, arb_series, ctx
from _packing.polynomial import (FinitePolynomialHamiltonian, nat_pair, nat_unpair,
                                polynomial, program_budget, rational_code, rational_value)
from _packing.real_names import (NamedFiniteHamiltonian, ScalarName, exact_fraction, lower_epsilon)
from _packing.rational import rational
from _packing.compiler import REPOSITORY, lake_command, compile_packing
from packing import serialize_enclosures


def variable(i):
    return [nat_pair(1, i)]


def constant(q):
    return [nat_pair(0, rational_code(q))]


def binary(tag, a, b):
    return [nat_pair(tag, 0), *a, *b]


def multiply(a, b):
    return binary(3, a, b)


def sqrt_name(n, *, scale=Fraction(1), offset=Fraction(0), calls=None):
    def name(p):
        if calls is not None:
            calls.append(p)
        extra = max(0, abs(scale.numerator).bit_length()-scale.denominator.bit_length())
        with ctx.workprec(p+extra+64):
            true = rational(offset)+rational(scale)*arb(n).sqrt()
            q = exact_fraction(true.mid())
            if not abs(rational(q)-true).upper() <= rational(Fraction(1, 1 << p)):
                raise ArithmeticError('independent name fixture failed its input contract')
            return q
    return name


class InterpreterTests(unittest.TestCase):
    def test_coding_matches_lean_examples_and_complete_natural_bijection(self):
        assert nat_pair(2, 4) == 18
        assert rational_value(nat_pair(nat_pair(3, 1), 3)) == Fraction(1, 2)
        for code in range(2000):
            assert nat_pair(*nat_unpair(code)) == code
        for q in [Fraction(0), Fraction(-7, 11), Fraction(22, 7)]:
            assert rational_value(rational_code(q)) == q

    def test_global_polynomial_gradient_field_and_unclipped_time(self):
        # P=t*q1*p1 + q2^2 + 3*p2; grouped q1,q2,p1,p2.
        first = binary(3, variable(0), binary(3, variable(1), variable(3)))
        P = binary(2, first, binary(2, binary(3, variable(2), variable(2)), binary(3, constant(3), variable(4))))
        H = FinitePolynomialHamiltonian(32, P)
        result = H.evaluate(arb(1)/2, [1, 2, 3, 4])
        assert result['value'].contains(arb('17.5'))
        assert all(x.contains(arb(q)) for x, q in zip(result['gradient'], ['1.5', '4', '.5', '3']))
        assert all(x.contains(arb(q)) for x, q in zip(result['vector_field'], ['.5', '3', '-1.5', '-4']))
        outside_time = FinitePolynomialHamiltonian(32, binary(3, variable(0), variable(3))).evaluate(2, [1, 0, 1, 0])
        assert outside_time['vector_field'][0].contains(2)

    def test_cutoff_transition_gradient_and_exact_flat_seams(self):
        H = FinitePolynomialHamiltonian(4, constant(1))
        with ctx.workprec(512):
            u = arb('0.45'); z = (-1/u+1/(1-u)).exp(); S = z/(1+z)
            slope = S*(1-S)*(1/u**2+1/(1-u)**2)
            positive = H.evaluate(0, [arb('2.5'), 0, 0, 0], bits=512)
            negative = H.evaluate(0, [arb('-2.5'), 0, 0, 0], bits=512)
            assert positive['value'].overlaps(1-S) and negative['value'].overlaps(1-S)
            assert positive['gradient'][0].overlaps(-slope)
            assert negative['gradient'][0].overlaps(slope)
            for x, expected in [(2, 1), (3, 0), (4, 0)]:
                result = H.evaluate(7, [x, 0, 0, 0])
                assert result['value'] == expected and all(v.is_zero() for v in result['gradient'])

    def test_full_time_jets_survive_global_gradient_composition(self):
        self.addCleanup(setattr, ctx, 'cap', ctx.cap)
        with ctx.workprec(512):
            ctx.cap = 32
            P = binary(3, variable(0), binary(3, variable(1), variable(3)))
            H = FinitePolynomialHamiltonian(32, P)
            result = H.jet(arb_series([arb(1)/2, 1], prec=3),
                           [arb_series([1, 1], prec=3), arb_series([0], prec=3),
                            arb_series([3], prec=3), arb_series([0], prec=3)])
            assert result['value'][1].contains(arb('4.5'))
            assert result['gradient'][0][1].contains(3)
            assert result['gradient'][2][1].contains(arb('1.5'))

    def test_prefix_underflow_out_of_range_and_budget_match_semantics(self):
        x = [arb(2)]*5
        assert polynomial([], x).is_zero()
        assert polynomial(variable(100), x).is_zero()
        assert polynomial([nat_pair(99, 123)], x).is_zero()
        assert program_budget(8, []) == 2
        assert program_budget(8, variable(3)) == 10
        assert program_budget(8, [nat_pair(2, 0)]) == 4

    def test_large_coefficients_refine_to_original_absolute_accuracy(self):
        q = Fraction(10**80, 3)
        H = FinitePolynomialHamiltonian(32, binary(3, constant(q), variable(1)))
        result = H.value_gradient(Fraction(1, 3), [1, 0, 0, 0], initial_bits=128)
        assert result['bits'] > 128
        assert all(v.rad() <= arb('1e-8') for v in [result['value'], *result['gradient']])
        from _packing.rational import rational
        with ctx.workprec(2048):
            assert result['value'].contains(rational(q))
            assert result['gradient'][0].contains(rational(q))

    def test_real_name_refinement_and_extremely_small_epsilon_are_unbounded(self):
        calls = []
        name = sqrt_name(2, scale=Fraction(1, 1 << 3000), calls=calls)
        q, record = lower_epsilon(name)
        assert record['precision'] == 4096 and calls == [128, 256, 512, 1024, 2048, 4096]
        with ctx.workprec(5000):
            assert 0 < rational(q) < arb(2).sqrt()/arb(2)**3000
        assert lower_epsilon(Fraction(1, 10))[0] == Fraction(1, 10)

    def test_exact_epsilon_has_no_hidden_python_decimal_digit_cap(self):
        q = Fraction(1, 10**5000)
        lower, record = lower_epsilon(q)
        assert lower == q and Fraction(record['epsilon']) == q

    def test_real_point_value_gradient_refines_inputs_as_well_as_arithmetic(self):
        calls = []
        coefficient = Fraction(10**80, 3)
        program = multiply([nat_pair(0, rational_code(coefficient))], variable(1))
        H = NamedFiniteHamiltonian(64, program)
        result = H.value_gradient(sqrt_name(3), [sqrt_name(2, calls=calls), 0, 0, 0], initial_bits=64)
        assert result['refinements'] > 0 and max(calls) >= 512
        with ctx.workprec(2048):
            assert result['value'].contains(rational(coefficient)*arb(2).sqrt())
            assert result['gradient'][0].contains(rational(coefficient))
            assert result['vector_field'][2].contains(-rational(coefficient))
            assert all(v.rad() <= arb('1e-8') for v in [result['value'], *result['gradient']])

    def test_irrational_point_boxes_crossing_a_flat_seam_keep_true_value_and_gradient(self):
        H = NamedFiniteHamiltonian(4, [nat_pair(0, rational_code(1))])
        # The valid name has nonzero-width boxes on both sides of the exact seam.
        result = H.value_gradient(sqrt_name(2), [lambda p: Fraction(2), 0, 0, 0], tolerance='1e-20', initial_bits=96)
        assert result['value'].contains(1)
        assert all(v.contains(0) and v.rad() <= arb('1e-20') for v in result['gradient'])

    def test_actual_nonzero_hamiltonian_flow_at_positive_and_negative_irrational_times(self):
        H = NamedFiniteHamiltonian(64, variable(3))  # H=p1, q1dot=1 on the plateau.
        for sign in [1, -1]:
            result = H.trajectory(sqrt_name(2, scale=Fraction(sign)), [sqrt_name(2), 0, 0, 0], initial_bits=160)
            with ctx.workprec(1024):
                expected = (1+sign)*arb(2).sqrt()
                assert result['endpoint'][0].contains(expected)
                assert all(v.contains(0) for v in result['endpoint'][1:])
                assert all(v.rad() <= arb('1e-8') for v in result['endpoint'])
            assert result['accepted_steps'] > 0

    def test_actual_linear_hamiltonian_flow_agrees_with_independent_exponentials(self):
        H = NamedFiniteHamiltonian(64, multiply(variable(1), variable(3)))
        result = H.trajectory(sqrt_name(2), [sqrt_name(2), Fraction(1, 3), sqrt_name(3), Fraction(-1, 5)],
                              initial_bits=160)
        with ctx.workprec(1024):
            expected = [arb(2).sqrt()*arb(2).sqrt().exp(), rational(Fraction(1, 3)),
                        arb(3).sqrt()*(-arb(2).sqrt()).exp(), rational(Fraction(-1, 5))]
            assert all(a.contains(b) for a, b in zip(result['endpoint'], expected))
            assert all(v.rad() <= arb('1e-8') for v in result['endpoint'])

    def test_intrinsic_width_and_inconsistent_names_are_rejected(self):
        with self.assertRaisesRegex(ValueError, 'point requires'):
            ScalarName(arb(1, '0.1'))
        name = ScalarName(lambda p: Fraction(0 if p < 100 else 1))
        name.bounds(64)
        with self.assertRaisesRegex(ValueError, 'disjoint'):
            name.bounds(128)
        with self.assertRaisesRegex(ValueError, 'epsilon'):
            lower_epsilon(Fraction(1))
        with self.assertRaisesRegex(ValueError, 'four'):
            NamedFiniteHamiltonian(4, []).trajectory(1, [0, 0, 0])

    def test_serialization_preserves_tiny_absolute_error_after_roundtrip(self):
        with ctx.workprec(512):
            original = [arb(1) / 3, -arb(2) / 7, arb(0)]
            encoded = serialize_enclosures(original, '1e-100', 512)
            self.assertTrue(all(arb(s).contains(v) and arb(s).rad() <= arb('1e-100')
                                for s, v in zip(encoded, original)))

    def test_rational_fallback_has_no_machine_word_precision_parameter(self):
        H = NamedFiniteHamiltonian(64, variable(3))
        for bits in (2**31, 2**63):
            result = H.value_gradient(0, [0]*4, initial_bits=bits)
            self.assertEqual(result['backend'], 'rational-interval')
            self.assertTrue(result['gradient'][2].contains(1))
        flow = H.trajectory(Fraction(1, 3), [0]*4, initial_bits=2**63)
        self.assertTrue(flow['endpoint'][0].contains(Fraction(1, 3)))
        encoded = serialize_enclosures(flow['endpoint'], '1e-8', flow['bits'])
        self.assertLessEqual(Fraction(encoded[0]['lower']), Fraction(1, 3))
        self.assertGreaterEqual(Fraction(encoded[0]['upper']), Fraction(1, 3))

    def test_arb_input_conversion_overflow_also_selects_the_rational_fallback(self):
        H = NamedFiniteHamiltonian(4, [])
        with patch('_packing.real_names.rational', side_effect=OverflowError('backend limit')):
            self.assertEqual(H.value_gradient(0, [0]*4)['backend'], 'rational-interval')
            self.assertEqual(H.trajectory(0, [0]*4)['backend'], 'rational-interval')

    def test_rational_exponential_and_cutoff_gradient_against_independent_arb(self):
        from _packing.exact import exp_negative
        with ctx.workprec(1024):
            for a in (Fraction(0), Fraction(1, 3), Fraction(1), Fraction(10), Fraction(100), Fraction(10000)):
                result = exp_negative(a, 160)
                true = (-rational(a)).exp()
                self.assertLessEqual(rational(result.lo), true)
                self.assertGreaterEqual(rational(result.hi), true)
        H = NamedFiniteHamiltonian(4, constant(1))
        for x in (Fraction(2), Fraction(5, 2), Fraction(3), 2+Fraction(1, 1 << 40)):
            actual = H.value_gradient(0, [x, 0, 0, 0], backend='rational', tolerance='1e-20')
            oracle = H.value_gradient(0, [x, 0, 0, 0], initial_bits=512, tolerance='1e-80')
            with ctx.workprec(1024):
                for v, q in zip([actual['value'], *actual['gradient']], [oracle['value'], *oracle['gradient']]):
                    self.assertLessEqual(rational(v.lo).lower(), q.upper())
                    self.assertGreaterEqual(rational(v.hi).upper(), q.lower())

    def test_rational_actual_flow_and_flat_seam_with_nonzero_field(self):
        H = NamedFiniteHamiltonian(4, constant(1))
        for x in (Fraction(5, 2), 2+Fraction(1, 1 << 40)):
            actual = H.trajectory(Fraction(1, 16), [x, 0, 0, 0], backend='rational')
            oracle = H.trajectory(Fraction(1, 16), [x, 0, 0, 0], initial_bits=256, tolerance='1e-30')
            with ctx.workprec(1024):
                for v, q in zip(actual['endpoint'], oracle['endpoint']):
                    self.assertLessEqual(rational(v.lo), q)
                    self.assertGreaterEqual(rational(v.hi), q)

    def test_rational_interval_euler_retries_until_independent_linear_flow_is_enclosed(self):
        H = NamedFiniteHamiltonian(64, multiply(variable(1), variable(3)))
        result = H.trajectory(Fraction(1, 16), [1, 0, 1, 0], tolerance='1e-4', backend='rational')
        self.assertGreater(result['refinements'], 0)
        with ctx.workprec(1024):
            for v, q in zip(result['endpoint'], [rational(Fraction(1, 16)).exp(), arb(0),
                                                (-rational(Fraction(1, 16))).exp(), arb(0)]):
                self.assertLessEqual(rational(v.lo), q)
                self.assertGreaterEqual(rational(v.hi), q)
                self.assertLessEqual(v.rad(), Fraction(1, 10000))

    def test_rational_actual_flow_accepts_named_negative_time_and_initial_point(self):
        H = NamedFiniteHamiltonian(64, variable(3))
        result = H.trajectory(sqrt_name(2, scale=Fraction(-1)),
                              [sqrt_name(2), 0, 0, 0], backend='rational', tolerance='1e-15')
        self.assertTrue(all(v.contains(0) and v.rad() <= Fraction(1, 10**15)
                            for v in result['endpoint']))


@unittest.skipUnless(os.environ.get('PACKING_NATIVE') == '1', 'set PACKING_NATIVE=1 for Lean execution')
class NativeExecutionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        lake = lake_command()
        subprocess.run([lake, 'build', 'verification.Executable'], cwd=REPOSITORY, check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        process = subprocess.run([lake, 'env', 'lean', '--run', 'examples/Packing.lean', 'batch'],
            cwd=REPOSITORY, input='fixture 10 1 10\nseed 10 1 10\n'
                'solve 10 9999999999999999 10000000000000000\n'
                'radius 1000000000000000000000000000003 1 ' + str(10**1000) + '\nquit\n',
            capture_output=True, text=True, check=True)
        cls.rows = [json.loads(line) for line in process.stdout.splitlines() if line.startswith('{')]
        if len(cls.rows) != 4:
            raise AssertionError(process.stdout)

    def test_native_nonzero_polynomial_and_gradient_match_exact_independent_formula(self):
        row = self.rows[0]
        H = FinitePolynomialHamiltonian(row['box'], row['program'])
        point = [Fraction(q['numerator'], q['denominator']) for q in row['point']]
        result = H.evaluate(point[0], point[1:])
        expected_value = point[0] * point[1] * point[3] + point[2]**2 + 3*point[4]
        expected_gradient = [point[0]*point[3], 2*point[2], point[0]*point[1], Fraction(3)]
        with ctx.workprec(512):
            self.assertTrue(result['value'].contains(rational(expected_value)))
            self.assertTrue(all(v.contains(rational(q)) for v, q in zip(result['gradient'], expected_gradient)))
            self.assertEqual(expected_value, Fraction(row['value']['numerator'], row['value']['denominator']))
            self.assertEqual(expected_gradient, [Fraction(q['numerator'], q['denominator']) for q in row['gradient']])

    def test_dense_identity_seed_is_rejected(self):
        self.assertFalse(self.rows[1]['passed'])

    def test_actual_compiled_output_contains_every_closed_source_ball(self):
        row = self.rows[2]
        self.assertTrue(row['whole_closed_ball_certificate'])
        self.assertEqual(row['program'], [])
        R = Fraction(row['radius_numerator'], row['radius_denominator'])
        self.assertGreater(R, 3*(row['k']-1)+1)
        self.assertGreater(Fraction(row['k'])/R**4, Fraction(1, 10**16))
        H = NamedFiniteHamiltonian(row['box'], row['program'])
        for i in range(row['k']):
            point = [3*i+1, 0, 0, 0]
            endpoint = H.trajectory(1, point)['endpoint']
            self.assertTrue(all(a.contains(b) for a, b in zip(endpoint, point)))

    def test_extreme_parameter_radius_obeys_both_exact_inequalities(self):
        row = self.rows[3]
        k, eps = 10**30+3, Fraction(1, 10**1000)
        R = Fraction(row['radius_numerator'], row['radius_denominator'])
        self.assertLess(Fraction(k)/(1-eps/2), R**4)
        self.assertLess(R**4, Fraction(k)/(1-eps))

    def test_general_python_adapter_compiles_an_irrational_epsilon_and_queries_same_field(self):
        epsilon = sqrt_name(2, scale=Fraction(-1, 10**20), offset=Fraction(1))
        H = compile_packing(12, epsilon)
        self.assertGreater(H.radius, 3*11+1)
        with ctx.workprec(1024):
            self.assertGreater(rational(Fraction(12)/H.radius**4), arb(2).sqrt()/rational(10**20))
        result = H.value_gradient(sqrt_name(2), [sqrt_name(3), 0, 0, 0])
        self.assertTrue(all(v.is_zero() for v in [result['value'], *result['gradient']]))
        endpoint = H.trajectory(sqrt_name(2), [sqrt_name(3), 0, 0, 0])
        with ctx.workprec(1024):
            self.assertTrue(endpoint['endpoint'][0].contains(arb(3).sqrt()))


if __name__ == '__main__':
    unittest.main()
