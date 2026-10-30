"""Fast regression checks; these do not establish packing or time-one flow."""
import json
from pathlib import Path
import subprocess
import sys
import unittest

from flint import arb,ctx
from k10 import K10,serialize_enclosures
from _k10.k10_hamiltonian_adapter import K10TailHamiltonian
from _k10.hamiltonian_core import identity,mv
from types import SimpleNamespace
from _k10.certified_cubic import CertifiedCubic
from _k10.direct_cubic_bridge import _QuadratureCubic


class SerializationTests(unittest.TestCase):
    def test_nondyadic_values_keep_requested_accuracy_after_decimal_roundtrip(self):
        with ctx.workprec(512):
            values=[arb(1)/3,-arb(2)/7,arb(0)]
            encoded=serialize_enclosures(values,'1e-100',512)
            for original,text in zip(values,encoded):
                restored=arb(text)
                self.assertTrue(restored.contains(original))
                self.assertTrue(restored.rad()<=arb('1e-100'))

    def test_a_wide_input_is_rejected(self):
        with ctx.workprec(512):
            with self.assertRaises(ArithmeticError):
                serialize_enclosures([arb(1,'1e-4')],'1e-8',512)

    def test_cli_reports_intervals_matching_its_accuracy_field(self):
        script=Path(__file__).with_name('k10.py')
        result=subprocess.run([sys.executable,str(script),'--time','0','--ball','0',
            '--point','1/3','0','0','0','--accuracy','1e-100'],check=True,capture_output=True,text=True)
        report=json.loads(result.stdout)
        with ctx.workprec(512):
            self.assertTrue(all(arb(x).rad()<=arb(report['accuracy']) for x in report['value']))


class MatchingLabelTests(unittest.TestCase):
    def test_cubic_connection_normalization_matches_independent_theta_values(self):
        with ctx.workprec(512):
            cubic=CertifiedCubic(512)
            for text in ('0','1/7','1/3','1/2','2/3','1'):
                y=arb(text)
                horizontal=cubic.evaluate(y,arb(0)).connection[0]
                self.assertTrue(horizontal.contains(0))
                self.assertTrue(horizontal.rad()<arb('1e-120'))
                a,b=cubic.evaluate(-y,y).connection
                residual=b-a+3*y+arb(1)/2
                self.assertTrue(residual.contains(0))
                self.assertTrue(residual.rad()<arb('1e-120'))

    def test_nonlinear_local_inverse_with_a_distinct_exact_symplectic_frame(self):
        # f(q,p)=(q,p+alpha*q1^2) has an independently known inverse.
        # A is a different symplectic shear, so simply returning u is wrong.
        with ctx.workprec(512):
            H=object.__new__(K10TailHamiltonian)
            H.bits=512;H.query_accuracy=arb('1e-8');H.retry_index=0
            H.tau=arb(1)/1024;H.r1=arb('20001/20000');H._largest_bound=arb(2)
            alpha=arb('1/100');beta=arb('1e-6');A=identity();A[2,0]=beta
            H.paths=[SimpleNamespace(A=A)]
            H.frame_variation=[2*alpha*H.tau*H.r1+beta]
            centre=list(map(arb,['1/4','-1/2','3/4','-1/4']))
            H._centre=lambda i,goal:centre
            calls=[]
            def forward(original,i,**options):
                calls.append(original)
                point=[a+b for a,b in zip(original,centre)]
                point[2]+=alpha*original[0]**2
                return point,{}
            H.engine=SimpleNamespace(forward=forward)
            for data in [('1/8','0','0','0'),('1','0','0','0'),('1/3','-1/4','1/5','-1/6')]:
                u=list(map(arb,data));label=H._label_point(u,0)
                expected=list(u);expected[2]+=beta*u[0]-alpha*H.tau*u[0]**2
                self.assertTrue(all(a.contains(b) for a,b in zip(label,expected)))
                self.assertTrue(max(x.rad() for x in label)<H._label_goal())
            self.assertGreaterEqual(len(calls),3)

    def test_fast_theta_boxes_enclose_independent_point_evaluations(self):
        with ctx.workprec(512):
            reference=CertifiedCubic(512);fast=_QuadratureCubic(512);radius=arb(2)**-60
            for a,b in [('1/3','1/2'),('0.94427998','0.52867887')]:
                u,v=arb(a),arb(b);box=fast.evaluate(arb(u,radius),arb(v,radius))
                for x in (-1,0,1):
                    for y in (-1,0,1):
                        sample=reference.evaluate(u+x*radius,v+y*radius)
                        self.assertTrue(box.density.contains(sample.density))
                        self.assertTrue(all(a.contains(b) for a,b in zip(box.connection,sample.connection)))


class FixedConstructionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.example=K10()

    def test_exact_density_and_initial_conditions_for_all_ten_balls(self):
        from fractions import Fraction
        self.assertGreater(10/self.example.radius**4,1-self.example.epsilon)
        with ctx.workprec(512):
            for i in range(10):
                point=self.example.trajectory('0',['1/3','0','0','0'],i)
                self.assertTrue(point[0].contains(arb(3*i)+arb(1)/3))
                self.assertTrue(all(x.is_zero() for x in point[1:]))
                self.assertTrue(self.example.H('0',point).is_zero())

    def test_gradient_of_actual_affine_H_equals_the_prescribed_velocity(self):
        H=self.example._evaluator.current
        with ctx.workprec(512):
            u=list(map(arb,['1/8','-1/16','1/32','1/64']));delta=arb('1e-12')
            for i in (0,9):
                for stage in range(6):
                    t=arb(2*stage+1)/16;y=H.isotopy(t,u,i)
                    gradient=[]
                    for j in range(4):
                        plus,minus=list(y),list(y);plus[j]+=delta;minus[j]-=delta
                        gradient.append((H.value(t,plus)-H.value(t,minus))/(2*delta))
                    field=[gradient[2],gradient[3],-gradient[0],-gradient[1]]
                    _,sigma,speed=H.clock(t)
                    if stage==5:
                        _,derivative=H.paths[i].evaluate(sigma);expected=[speed*x for x in mv(derivative,u)]
                    elif stage in (0,3):
                        expected=[speed*H.route_scale*i*x*(1 if stage==0 else -1) for x in H.dirQ]
                    elif stage in (1,4):
                        expected=[speed*H.route_scale*H.ranksP[i]*x*(1 if stage==1 else -1) for x in H.dirP]
                    else:expected=[speed*(a-b) for a,b in zip(H.far[i],H.sources[i])]
                    self.assertTrue(all(abs(a-b).upper()<arb('1e-8') for a,b in zip(field,expected)))

    def test_invalid_source_ball_is_rejected(self):
        with self.assertRaises(ValueError):self.example.trajectory('1',['1','1','0','0'],0)

    def test_decimal_coordinates_are_validated_and_evaluated_consistently(self):
        with ctx.workprec(512):
            point=self.example.trajectory('0',[0.6,0.8,0,0],0)
            self.assertTrue(point[0].contains(arb(3)/5))
            self.assertTrue(point[1].contains(arb(4)/5))

    def test_origin_is_excluded_from_the_actual_tail_charts(self):
        self.assertTrue(self.example.H('15/16',['0']*4).is_zero())

    def test_actual_tail_H_in_a_noncentral_local_chart_of_every_ball(self):
        H=self.example._evaluator.current
        with ctx.workprec(512):
            _,sigma,_=H.clock(arb(15)/16);v=H.tau+(1-H.tau)*sigma
            for centre in H.centres:
                point=[x/v for x in centre];point[0]+=arb(2)**-160
                value=H.value(arb(15)/16,point)
                self.assertTrue(value.is_finite())
                self.assertTrue(value.rad()<=arb(self.example.accuracy))


if __name__=='__main__':
    unittest.main()
