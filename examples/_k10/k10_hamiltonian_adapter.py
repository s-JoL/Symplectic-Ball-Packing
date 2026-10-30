"""Actual K10 oracles connected to the eight-stage common Hamiltonian.

Every accepted answer is an Arb enclosure. Unresolved precision or inverse
branches raise an error. Completing the full fixed-instance validation
requires all ten first jets, local bounds, and the time-one checks.
"""
from flint import arb,arb_mat,fmpq_mat,ctx
from .arb_cache import ball_key
from .embedding_action import ActionK10
from .inverse_chain import InverseK10
from .k10_instance import K10Instance
from .hamiltonian_core import CommonHamiltonian,ExactEmbedding,norm,mv
from .tail_matching import TailMatching
from .rational_symplectic import variation_bound
from .preimage_cover import CutoffImageCover


class _Engine(ActionK10,InverseK10):
    def raw_action(self,local,index,accuracy='1e-8',guard_bits=None):
        guard=16+64*getattr(self,'retry_index',0) if guard_bits is None else guard_bits
        return super().raw_action(local,index,accuracy,guard,
                                  flow_order=max(32,min(128,self.bits//8)))


class K10Hamiltonian(CommonHamiltonian):
    """Use the frozen local records for all ten balls of this fixed instance.

    Records contain centre enclosures, a first-jet matrix, a positive
    local radius, and its certified derivative norm bound.
    Precision failure is explicit and does not certify a zero value.
    """
    def __init__(self,records,*,bits=1024,accuracy='1e-8',progress=None,frozen=None,quad_workers=1):
        if len(records)!=10 or [r['ball'] for r in records]!=list(range(10)):
            raise ValueError('the fixed instance requires all ten ball records')
        self.records,self.progress=records,progress
        self.engine=_Engine(K10Instance(verified_normal=False),bits=bits,
            tolerance=arb(2)**(-bits+96),quad_workers=quad_workers,progress=progress)
        # Strip quadrature is an internal approximation, with a separate
        # final output-radius gate. Half the working precision avoids
        # oversolving its integrals by hundreds of unnecessary bits;
        # precision retries make this internal goal tend to zero.
        with ctx.workprec(bits):self.engine.strip.tolerance=arb(2)**(-max(128,bits//2))
        self._values={}
        with ctx.workprec(bits):
            self.query_accuracy=arb(accuracy)
            if not self.query_accuracy>0:raise ValueError('positive Hamiltonian accuracy is required')
            self._centre_boxes=[list(map(arb,r['centre'])) for r in records]
            matrices=[arb_mat([[arb(x) for x in row] for row in r['jacobian']]) for r in records]
            radius=min(arb(r['local_radius']).lower() for r in records)
            bounds=[arb(r['local_derivative_bound']) for r in records]
            if not radius>0 or not all(b>0 for b in bounds):
                raise ValueError('positive certified local radii and bounds are required')
            self._largest_bound=max(bounds)
            self.point_goal=self.action_goal=self.inverse_goal=self.query_accuracy/2**16
            self.retry_index=0
            oracles=[]
            for i in range(len(records)):
                oracles.append(ExactEmbedding(
                    lambda u,i=i:self._embedding_value(u,i),
                    lambda u,i=i:self._embedding_action(u,i),
                    lambda i=i:matrices[i],
                    lambda y,i=i:self._embedding_preimage(y,i)))
            super().__init__(oracles,bounds,radius,arb(73)/40,bits=bits,frozen=frozen)

    def _key(self,u,i):return i,tuple(ball_key(arb(x)) for x in u)

    def _replace_centre(self,i,point):
        old=self._centre_boxes[i]
        if not all(a.overlaps(b) for a,b in zip(old,point)):
            raise ArithmeticError('independent centre enclosures disagree')
        if max(x.rad() for x in point)<max(x.rad() for x in old):
            self._centre_boxes[i]=list(point)
            self.records[i]['centre']=[x.str(self.bits) for x in point]
            if hasattr(self,'centres'):
                self.centres[i]=list(point)
                self.far[i]=[x/self.tau for x in point]

    def _centre(self,i,goal):
        if max(x.rad() for x in self._centre_boxes[i])>goal:
            point,_=self.engine.forward([3*i,0,0,0],i,accuracy=goal,
                                        flow_order=max(32,min(128,self.bits//8)),guard_bits=16+64*self.retry_index,local_moser=True)
            self._replace_centre(i,point)
        return self._centre_boxes[i]

    def _embedding_value(self,u,i):
        u=list(map(arb,u))
        if all(x.is_zero() for x in u):return self._centre_boxes[i]
        key=self._key(u,i)
        if key in self._values and max(x.rad() for x in self._values[key])<=self.point_goal:
            return self._values[key]
        original=[x+(3*i if j==0 else 0) for j,x in enumerate(u)]
        point,_=self.engine.forward(original,i,accuracy=self.point_goal,neighbourhood=True,
                                    flow_order=24,guard_bits=16+64*self.retry_index,local_moser=True)
        self._values[key]=list(point)
        return point

    def _embedding_action(self,u,i):
        if all(arb(x).is_zero() for x in u):return arb(0)
        point,action,_=self.engine.value_action(u,i,accuracy=self.action_goal)
        self._values[self._key(u,i)]=list(point)
        self._replace_centre(i,self.engine._action_centres[i][0])
        return action

    def _embedding_preimage(self,y,i):
        source,_=self.engine.inverse(y,i,accuracy=self.inverse_goal,max_step='.001953125')
        return source

    def _budget(self,t):
        stage,sigma,speed=self.clock(t)
        coefficient=arb(1)
        if stage==6 and not speed.is_zero():
            rho=self.tau*sigma
            if rho.contains(0):raise ArithmeticError('increase clock precision near the shape-stage endpoint')
            coefficient=abs(2*self.tau*speed/(rho*rho*rho)).upper()
        elif stage==7 and not speed.is_zero():
            v=self.tau+(1-self.tau)*sigma
            coefficient=abs(2*(1-self.tau)*speed/(v*v*v)).upper()
        self.action_goal=self.query_accuracy/(2**16*(1+coefficient))
        self.point_goal=self.action_goal/(1+arb(73)/40)
        self.inverse_goal=self.action_goal/2**16
        return stage,sigma,speed

    def source_generator(self,t,u,i):
        with ctx.workprec(self.bits):
            stage,_,speed=self._budget(arb(t))
            if stage==6 and not speed.is_zero():
                self._centre(i,self.inverse_goal/(16*(1+self._largest_bound)))
            return super().source_generator(t,u,i)

    def value(self,t,y):
        with ctx.workprec(self.bits):
            t,y=arb(t),list(map(arb,y))
            stage,_,speed=self._budget(t)
            if stage is not None and stage<=5 and not speed.is_zero() and norm(y).lower()<=self.support_radius:
                factor=arb(1)
                if stage==5:
                    _,sigma,_=self.clock(t)
                    for path in self.paths:
                        M,Mdot=path.evaluate(sigma)
                        B=Mdot*M.inv()
                        factor=max(factor,sum(abs(B[a,b]).upper()**2 for a in range(4) for b in range(4)).sqrt().upper())
                goal=self.query_accuracy*self.tau/(2**24*(1+abs(speed).upper())*factor*
                    (1+self.support_radius+norm(y).upper())*arb(2)**(128*self.retry_index))
                for i in range(self.k):self._centre(i,goal)
            if stage==6 and not speed.is_zero():
                for i in range(self.k):
                    if norm([a-b for a,b in zip(y,self.far[i])]).lower()<=(self.derivative_bounds[i]*self.r2).upper():
                        self._centre(i,self.inverse_goal/(16*(1+self._largest_bound)))
            result=super().value(t,y)
            if result.rad()>self.query_accuracy:
                raise ArithmeticError('Hamiltonian enclosure requires finer oracle data or working precision')
            return result


class K10TailHamiltonian(TailMatching,K10Hamiltonian):
    """Fixed-instance H with an exact rational frame and no shape stage.

    The final embedding is f_i(nu_i(u)), not f_i(u). Certified near-frame
    bounds place every nu_i(B_1) inside the cutoff plateau B(r1).
    """
    def __init__(self,records,*,bits=1536,accuracy='1e-8',progress=None,frozen=None,quad_workers=1):
        with ctx.workprec(bits):
            converted=[];frames=[];bounds=[];metadata=[]
            for record in records:
                if 'local_jacobian' not in record:
                    raise ValueError('tail matching requires the full local differential enclosure')
                A=fmpq_mat(record['rational_frame']);info=dict(exact_symplectic=True)
                O=fmpq_mat([[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0]])
                residual=A.transpose()*O*A-O
                if any(residual[i,j] for i in range(4) for j in range(4)):
                    raise ValueError('the supplied rational frame is not symplectic')
                D=arb_mat([[arb(x) for x in row] for row in record['local_jacobian']])
                bound=sum(abs(D[a,b]).upper()**2 for a in range(4) for b in range(4)).sqrt().upper()
                if not bound<arb(record['local_derivative_bound']):
                    raise ValueError('the stored local derivative norm bound is too small')
                eta=variation_bound(A,D)
                if not eta<arb(1)/40002:
                    raise ValueError(f"ball {record['ball']} needs a finer local differential enclosure")
                r=dict(record);r['jacobian']=[[str(A[i,j]) for j in range(4)] for i in range(4)]
                r['rational_frame']=r['jacobian']
                converted.append(r);frames.append(A);bounds.append(eta);metadata.append(info)
            self.rational_frames,self.frame_metadata=frames,metadata
            super().__init__(converted,bits=bits,accuracy=accuracy,progress=progress,frozen=frozen,quad_workers=quad_workers)
            self.enable_tail_matching(bounds)

    def _label_goal(self):
        return min(self.query_accuracy/(64*(1+self._largest_bound)),
                   arb(2)**(-min(self.bits//8,64)-8*self.retry_index))

    def _label_point(self,u,i):
        # Solve G(w)=u in the tiny certified local chart. Inverting the
        # complete ambient map needlessly transports a 1/tau condition
        # number through every reverse chart. Banach's a posteriori bound
        # certifies the same exact label from forward evaluations instead.
        goal=self._label_goal()
        if hasattr(self,'records'):
            D=arb_mat([[arb(x) for x in row] for row in self.records[i]['local_jacobian']])
            candidate=mv(D.inv()*self.paths[i].A,u)
            if max(x.rad() for x in candidate)<goal:return candidate
        centre_goal=self.tau*goal/(64*(1+self._largest_bound))
        centre=self._centre(i,centre_goal)
        inverse=self.paths[i].A.inv()
        inverse_bound=sum(abs(inverse[a,b]).upper()**2 for a in range(4) for b in range(4)).sqrt().upper()
        eta=self.frame_variation[i]
        w=[arb(x).mid() for x in u]
        accuracy=self.tau*goal/(64*(1+inverse_bound))
        for _ in range(8):
            if not norm(w)<self.r1:
                raise ArithmeticError('local inverse iterate left its certified chart')
            original=[self.tau*x+(3*i if j==0 else 0) for j,x in enumerate(w)]
            value,_=self.engine.forward(original,i,accuracy=accuracy,neighbourhood=True,
                flow_order=48,guard_bits=64,local_moser=True)
            G=[x/self.tau for x in mv(inverse,[a-b for a,b in zip(value,centre)])]
            next_w=[x+a-b for x,a,b in zip(w,u,G)]
            error=(eta*norm([a-b for a,b in zip(next_w,w)]).upper()/(1-eta)).upper()
            label=[x+arb(0,error) for x in next_w]
            if max(x.rad() for x in label)<goal:return label
            w=[x.mid() for x in next_w]
        raise ArithmeticError('local tail-label contraction needs more precision')

    def _embedding_preimage(self,y,i):
        # A contraction enclosure around the affine inverse often settles
        # centre queries without any normal-transfer integration.
        with ctx.workprec(self.bits):
            for j in range(self.k):
                z=mv(self.paths[j].A.inv(),[arb(a)-b for a,b in zip(y,self.centres[j])])
                radius=norm(z).upper();local=arb(self.records[j]['local_radius'])
                eta=self.frame_variation[j]
                if radius<(1-eta)*local:
                    # Banach proves existence inside this local image.
                    # The verified r3 containers are pairwise disjoint.
                    if j!=i:return None
                    # f(x)-f(0)=(integral_0^1 Df(s*x) ds)*x. The local
                    # derivative box is convex and contains that average.
                    # Its interval inverse therefore encloses the inverse
                    # point, including uncertainty in the stored centre.
                    D=arb_mat([[arb(x) for x in row] for row in self.records[j]['local_jacobian']])
                    candidate=mv(D.inv(),[arb(a)-b for a,b in zip(y,self.centres[j])])
                    if self.retry_index==0 or max(x.rad() for x in candidate)<self.inverse_goal:
                        # A cheap initial enclosure may already suffice for
                        # the final output check. Retries require the finer
                        # inverse goal and retain the full reverse fallback.
                        return candidate
                    error=(eta*radius/(1-eta)).upper()
                    candidate=[x+arb(0,error) for x in z]
                    if max(x.rad() for x in candidate)<self.inverse_goal:return candidate
            if hasattr(self,'_active_source_radius'):
                r=self._active_source_radius
                if r<arb(self.records[i]['local_radius']):
                    if norm([arb(a)-b for a,b in zip(y,self.centres[i])]).lower()>(self.derivative_bounds[i]*r).upper():
                        return None
        try:return super()._embedding_preimage(y,i)
        except (ArithmeticError,ValueError,ZeroDivisionError):
            if not hasattr(self,'_outside_covers') or not hasattr(self,'_active_source_radius'):raise
            key=(self._cover_context,i)
            if key not in self._outside_covers:
                self._outside_covers[key]=CutoffImageCover(self.engine,y,i,radius=self._active_source_radius.upper())
            cover=self._outside_covers[key]
            cover.evaluator=self.engine
            cover.point=[a.intersection(arb(b)) for a,b in zip(cover.point,y)]
            cover.radius=min(cover.radius,self._active_source_radius.upper())
            if cover.advance(getattr(self,'_cover_budget',1)):return None
            raise ArithmeticError('reverse chart unresolved; certified cutoff-image cover remains incomplete')

    def _embedding_action(self,u,i):
        with ctx.workprec(self.bits):
            u=list(map(arb,u));r=norm(u).upper()
            if r<arb(self.records[i]['local_radius']):
                D=self.derivative_bounds[i]
                bound=((norm(self.centres[i]).upper()+D*r)*D*r/2).upper()
                if bound<self.action_goal:return arb(0,bound)
        return super()._embedding_action(u,i)

    def isotopy(self,t,u,i):
        with ctx.workprec(self.bits):
            t=arb(t)
            if t>=1:self.point_goal=self.query_accuracy/4
            elif t>0:
                stage,sigma,_=self.clock(t)
                if stage==7:
                    v=self.tau+(1-self.tau)*sigma
                    self.point_goal=self.query_accuracy*v.lower()/4
            result=super().isotopy(t,u,i)
            if max(x.rad() for x in result)>self.query_accuracy:
                raise ArithmeticError('trajectory enclosure needs finer source labels or working precision')
            return result

    def value(self,t,y):
        with ctx.workprec(self.bits):
            stage,sigma,_=self.clock(arb(t))
            if stage==7:self._active_source_radius=(self.tau+(1-self.tau)*sigma)*self.r2
            try:return super().value(t,y)
            finally:
                if hasattr(self,'_active_source_radius'):del self._active_source_radius


class AdaptiveK10Hamiltonian:
    """Refine intervals while preserving the exact same Hamiltonian.

    Every returned value is certified. A caller may bound max_bits to
    receive an explicit unresolved error. Without that bound retries
    continue; this scheduler itself is not a proof that all exceptional
    reverse-chart branches have a terminating implementation.
    """
    def __init__(self,records,*,bits=1536,accuracy='1e-8',progress=None,frozen=None,quad_workers=1):
        self.records,self.accuracy,self.progress=records,accuracy,progress
        self.quad_workers=quad_workers
        self.current=K10TailHamiltonian(records,bits=bits,accuracy=accuracy,progress=progress,frozen=frozen,quad_workers=quad_workers)
        self.frozen=self.current.configuration();self.covers={}

    def _refine(self,H,next_bits,attempt):
        refined=K10TailHamiltonian(H.records,bits=next_bits,accuracy=self.accuracy,
            progress=self.progress,frozen=self.frozen,quad_workers=self.quad_workers)
        refined.retry_index=refined.engine.retry_index=attempt
        with ctx.workprec(next_bits):
            goal=refined._label_goal()
            for (i,key,_),label in H._tail_labels.items():
                if max(x.rad() for x in label)<=goal:
                    # Equality of the exact dyadic input key is required.
                    # A non-dyadic input parsed at higher precision will
                    # miss this cache and be recomputed normally.
                    refined._tail_labels[i,key,next_bits]=label
        return refined

    def value(self,t,y,*,max_bits=None):
        with ctx.workprec(self.current.bits):
            if len(y)!=4 or not all(arb(x).is_finite() for x in [t,*y]):
                raise ValueError('a finite time and four finite coordinates are required')
            query=(ball_key(arb(t)),tuple(ball_key(arb(x)) for x in y))
        attempt=self.current.retry_index
        while True:
            H=self.current;H._outside_covers=self.covers;H._cover_context=query
            H._cover_budget=min(16,1+attempt)
            try:return H.value(t,y)
            except (ArithmeticError,ValueError,ZeroDivisionError) as error:
                if self.progress:self.progress('precision_retry',dict(bits=H.bits,error=str(error)))
                next_bits=H.bits+max(256,H.bits//2)
                if max_bits is not None and next_bits>max_bits:raise
                attempt+=1
                self.current=self._refine(H,next_bits,attempt)

    def trajectory(self,t,u,i,*,max_bits=None):
        attempt=self.current.retry_index
        while True:
            H=self.current
            try:return H.isotopy(t,u,i)
            except (ArithmeticError,ValueError,ZeroDivisionError) as error:
                if self.progress:self.progress('precision_retry',dict(bits=H.bits,error=str(error)))
                next_bits=H.bits+max(256,H.bits//2)
                if max_bits is not None and next_bits>max_bits:raise
                attempt+=1
                self.current=self._refine(H,next_bits,attempt)
