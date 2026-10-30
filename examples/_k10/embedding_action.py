"""Primitive of the complete actual K10 embedding, including phase winding."""
import math
from .arb_cache import floor_mid,nearest_mid,root_precision
from flint import arb,ctx
from .interval_chain import IntervalK10
from .primitive_flow import suspension_action,normal_to_ball_action
from .direct_cubic_bridge import DirectCubicBridge
from .developed_phase import landau_phase


class ActionK10(IntervalK10):
    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs)
        self._action_centres={}

    def raw_action(self,local,index,accuracy='1e-8',guard_bits=None,flow_order=None,local_moser=True):
        with ctx.workprec(self.bits):
            sigma=arb(self.numeric.sigma)
            source=[sigma*arb(x) for x in local]
            state,total=self.ball_layer(source,index,with_action=True)
            if self.progress:self.progress('ball_action',dict(action=total.str(30)))
            state,extra=self.layer_inverse(state,with_action=True);total+=extra
            moser_cell=floor_mid(state[0])
            if abs(state[0]-nearest_mid(state[0])).upper()<arb('.3'):
                # The suspension is identically zero on this whole
                # integer collar, hence its marked-row sheet correction
                # is exactly zero in either adjacent developed chart.
                moser_cell=0
            initial_strip=floor_mid(3*state[1])
            if moser_cell and not ((3*state[1]).lower()>initial_strip and (3*state[1]).upper()<initial_strip+1):
                raise ArithmeticError('refine the pre-Moser marked-row decision')
            options=dict(bits=self.bits,order=max(24,self.bits//16) if flow_order is None else flow_order,max_step='.0078125',
                         max_radius=accuracy,remainder_guard_bits=(128+max(0,(self.bits-384)//2)
                         if guard_bits is None else guard_bits),max_steps=max(100000,self.bits**3))
            if self.progress:options['progress']=lambda info:self.progress('primitive_flow',info)
            state,extra,stats=suspension_action(state,self.P,self.data,inverse=True,local_frame=local_moser,**options)
            total+=extra
            if self.progress:self.progress('moser_action',dict(action=total.str(30),steps=stats.accepted_steps))
            state,extra=self.base_inverse(state,with_action=True);total+=extra
            state=self.shear_inverse(state)
            bridge=DirectCubicBridge(bits=self.bits,root_bits=root_precision(self.bits,accuracy),workers=1)
            initial,info=bridge.old_normal_input(*state,arb(self.P.d))
            theta=landau_phase(bridge,*state[:2],old=(info['u'],info['v']),vertical_sheet=moser_cell)
            theta-=moser_cell*initial_strip
            total-=theta
            if self.progress:self.progress('initial_phase',dict(phase=theta.str(30)))
            point,extra,normal_stats=normal_to_ball_action(initial,arb(self.P.d),**options)
            total+=extra
            point=[x/sigma for x in point];total/=sigma*sigma
            if max([x.rad() for x in point]+[total.rad()])>arb(accuracy):
                raise ArithmeticError('full embedding primitive requires more precision')
            return point,total,dict(
                moser_steps=stats.accepted_steps,**normal_stats)

    def value_action(self,local,index,accuracy='1e-8'):
        with ctx.workprec(self.bits):
            goal=arb(accuracy)
            if not goal>0:raise ValueError('action accuracy must be positive')
            if index not in self._action_centres or max([x.rad() for x in self._action_centres[index][0]]+
                    [self._action_centres[index][1].rad()])>goal/4:
                self._action_centres[index]=self.raw_action([0]*4,index,goal/4)
            if all(arb(x).is_zero() for x in local):
                point,_,stats=self._action_centres[index]
                return point,arb(0),stats
            point,action,stats=self.raw_action(local,index,goal/4)
            action-=self._action_centres[index][1]
            if max([x.rad() for x in point]+[action.rad()])>goal:
                raise ArithmeticError('normalized embedding primitive requires more precision')
            return point,action,stats
