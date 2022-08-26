import std.conv: text;
import std.string: split;
import std.algorithm: map, any;
import std.array: array;
import std.range: iota;
import std.string: startsWith;
import util.tuple: q=tuple,Q=Tuple;
import util.io:writeln;
import std.exception: enforce;

import backend,options;
import distrib;
import sym.dexpr,util.hashtable,util;
import ast.expression,ast.declaration,ast.type,ast.error;
import ast.semantic_,ast.scope_,context;
import ast.reverse: knownLength;

import std.random, sample; // (for InferenceMethod.simulate)

class Bruteforce: Backend{
	this(string sourceFile){
		this.sourceFile=sourceFile;
	}
	override Distribution analyze(FunctionDef def,ErrorHandler err){
		DExpr[string] fields;
		foreach(i,a;def.params) fields[a.getName]=dVar(a.getName);
		DExpr init=dRecord(fields);
		auto interpreter=Interpreter(def,def.body_,init,false);
		auto ret=distInit();
		interpreter.runFun(ret);
		assert(!!def.ftype);
		bool isTuple = !!def.ftype.cod.isTupleTy;
		return ret.toDistribution(def.params.map!(p=>p.getName).array,def.isTuple,def.retNames,isTuple);
	}
private:
	string sourceFile;
}

auto distInit(){
	return Dist(MapX!(DExpr,DExpr).init,zero,SetX!string.init);
}
struct Dist{
	MapX!(DExpr,DExpr) state;
	DExpr error;
	SetX!string tmpVars;
	// @disable this();
	this(MapX!(DExpr,DExpr) state,DExpr error,SetX!string tmpVars){
		this.state=state;
		this.error=error;
		this.tmpVars=tmpVars;
	}
	Dist dup(){ return Dist(state.dup,error,tmpVars.dup); static assert(this.tupleof.length==3); }
	void addTmpVar(string var){ tmpVars.insert(var); }
	Dist marginalizeTemporaries(){
		if(!tmpVars.length) return this;
		auto r=distInit;
		r.error=error;
		foreach(k,v;state){
			auto rec=cast(DRecord)k;
			assert(!!rec,text(k));
			auto val=rec.values.dup;
			foreach(x;tmpVars) val.remove(x);
			r.add(dRecord(val),v);
		}
		tmpVars.clear();
		return r;
	}
	Dist marginalize(string[] vars){
		if(!vars.length) return this;
		auto r=distInit;
		r.error=error;
		r.tmpVars=tmpVars.dup;
		foreach(x;vars) r.tmpVars.remove(x);
		foreach(k,v;state){
			auto rec=cast(DRecord)k;
			assert(!!rec,text(k));
			auto val=rec.values.dup;
			foreach(x;vars) val.remove(x);
			r.add(dRecord(val),v);
		}
		return r;
	}
	void add(DExpr k,DExpr v){
		if(k in state) state[k]=(state[k]+v).simplify(one);
		else state[k]=v;
		if(state[k] == zero) state.remove(k);
	}
	void opOpAssign(string op:"+")(Dist r){
		foreach(k,v;r.state)
			add(k,v);
		error=(error+r.error).simplify(one);
		foreach(t;r.tmpVars) addTmpVar(t);
	}
	Dist map(DLambda lambda){
		if(opt.trace) writeln("particle-size: ",state.length);
		auto r=distInit;
		r.copyNonState(this);
		foreach(k,v;state) r.add(dApply(lambda,k).simplify(one),v);
		return r;
	}
	DExpr expectation(DLambda lambda,bool hasFrame){
		if(!hasFrame){
			DExpr r1=zero,r2=zero;
			foreach(k,v;state){
				r1=(r1+v*dApply(lambda,k)).simplify(one);
				r2=(r2+v).simplify(one);
			}
			return (r1/r2).simplify(one);
		}
		MapX!(DExpr,Q!(Q!(DExpr,DExpr)[],DExpr,DExpr)) byFrame;
		foreach(k,v;state){
			auto frame=dField(k,"`frame").simplify(one);
			auto entry=byFrame.get(frame,q((Q!(DExpr,DExpr)[]).init,zero,zero)); // (hash tables return their values by value)
			entry[0]~=q(k,v);
			byFrame[frame]=entry;
		}
		foreach(k,ref v;byFrame){
			foreach(x;v[0]){
				v[1]=(v[1]+x[1]*dApply(lambda,x[0])).simplify(one);
				v[2]=(v[2]+x[1]).simplify(one);
			}
		}
		auto r=distInit;
		r.copyNonState(this);
		static int unique=0;
		string tmp="`expectation"~lowNum(++unique);
		addTmpVar(tmp);
		foreach(k,v;byFrame){
			auto e=(v[1]/v[2]).simplify(one);
			foreach(x;v[0])
				r.add(dRUpdate(x[0],tmp,e).simplify(one),x[1]);
		}
		this=r;
		return dField(db1,tmp);
	}
	Dist pushFrame(){
		return map(dLambda(dRecord(["`frame":db1])));
	}
	Dist popFrame(string tmpVar){
		addTmpVar(tmpVar);
		return map(dLambda(dRUpdate(dField(db1,"`frame"),tmpVar,dField(db1,"`value"))));
	}
	Dist flatMap(DLambda[] lambdas){
		auto r=distInit;
		r.copyNonState(this);
		foreach(k,v;state){
			foreach(lambda;lambdas){
				auto app=dApply(lambda,k).simplify(one);
				auto val=app[0.dℚ].simplify(one),scale=app[1.dℚ].simplify(one);
				r.add(val,(v*scale).simplify(one));
			}
		}
		return r;
	}
	Dist assertTrue(DLambda lambda){
		if(opt.noCheck) return this;
		auto r=distInit;
		r.copyNonState(this);
		foreach(k,v;state){
			auto cond=dApply(lambda,k).simplify(one);
			if(cond == one || cond == zero){
				if(cond == zero){
					r.error = (r.error + v).simplify(one);
				}else{
					r.add(k,v);
				}
			}else{
				r.error = (r.error + v*dEqZ(cond)).simplify(one);
				r.add(k,(v*cond).simplify(one));
			}
		}
		return r;
	}
	Dist eraseErrors(){
		auto r=dup();
		r.error=zero;
		return r;
	}
	Dist observe(DLambda lambda){
		auto r=distInit;
		r.copyNonState(this);
		foreach(k,v;state){
			auto cond=dApply(lambda,k).simplify(one);
			if(cond == one || cond == zero){
				if(cond == one) r.add(k,v);
			}else{
				r.add(k,(v*cond).simplify(one));
			}
		}
		return r;
	}
	private Distribution toDistributionImpl(Distribution r,string[] names,bool isTuple){
		auto vars=names.map!(name=>r.declareVar(name)).array;
		r.distribution=zero;
		foreach(k,v;state){
			auto cur = v;
			foreach(i,var;vars){
				assert(!!var);
				auto val = dField(k,"`value");
				cur = cur*dDelta(isTuple?val[i.dℚ]:val,var);
			}
			r.distribution=r.distribution+cur;
		}
		r.error=error;
		r.simplify();
		r.orderFreeVars(vars,isTuple);
		return r;
	}
	Distribution toDistribution(string[] names,bool isTuple){
		auto r=new Distribution();
		return toDistributionImpl(r,names,isTuple);
	}
	Distribution toDistribution(string[] paramNames,bool argsIsTuple,string[] names,bool isTuple){
		auto r=new Distribution();
		auto args=paramNames.map!(name=>r.declareVar(name)).array;
		r.addArgs(args,argsIsTuple,null);
		return toDistributionImpl(r,names,isTuple);
	}
	/*DExpr flip(DExpr p){
		// TODO: check that p is in [0,1]
		static int unique=0;
		auto tmp="`flip"~lowNum(++unique);
		addTmpVar(tmp);
		this=flatMap(
			[dLambda(dTuple([dRUpdate(db1,tmp,zero),(one-p).simplify(one)])),
			 dLambda(dTuple([dRUpdate(db1,tmp,one),p]))]);
		if(opt.backend==InferenceMethod.simulate) pickOne();
		return dField(db1,tmp);
	}*/
	DExpr uniformInt(DExpr arg){
		// TODO: check constraints on arguments
		auto r=distInit;
		r.copyNonState(this);
		auto lambda=dLambda(arg);
		static int unique=0;
		auto tmp="`uniformInt"~lowNum(++unique);
		r.addTmpVar(tmp);
		if(opt.backend==InferenceMethod.simulate){
			long low,up;
			DExpr result=null;
			foreach(k,v;state){
				auto ab=dApply(lambda,k).simplify(one);
				auto a=ab[0.dℚ].simplify(one), b=ab[1.dℚ].simplify(one);
				static ℤ toNum(string what)(DExpr e){
					if(auto q=cast(Dℚ)e) return mixin(what~"div")(q.c.num,q.c.den);
					import std.format: format;
					import std.math: floor, ceil;
					if(auto f=cast(DFloat)e) return ℤ(format("%.0s",mixin(what)(f.c)));
					enforce(0,text("non-constant condition ",e));
					assert(0);
				}
				ℤ lowCand=toNum!"ceil"(a),upCand=toNum!"floor"(b);
				if(!result){
					import std.random;
					enforce(lowCand<=upCand);
					assert(long.min<=lowCand && upCand<=long.max);
					low=lowCand.toLong(), up=upCand.toLong();
					result=dℚ(uniform!"[]"(low,up));
				}else enforce(low==lowCand && up==upCand);
				r.add(dRUpdate(k,tmp,result).simplify(one),v);
			}
		}else{
			foreach(k,v;state){
				auto ab=dApply(lambda,k).simplify(one);
				auto a=ab[0.dℚ].simplify(one), b=ab[1.dℚ].simplify(one);
				auto az=a.isInteger(), bz=b.isInteger();
				assert(az&&bz,text("TODO: ",a," ",b));
				auto num=dℚ(bz.c.num-az.c.num+1);
				if(num.c>0){
					auto nv=(v/num).simplify(one);
					for(ℤ i=az.c.num;i<=bz.c.num;++i) r.add(dRUpdate(k,tmp,i.dℚ).simplify(one),nv);
				}else r.error = (r.error + v).simplify(one);
			}
		}
		this=r;
		//if(opt.backend==InferenceMethod.simulate) pickOne();
		return dField(db1,tmp);
	}
	DExpr categorical(DExpr arg){
		auto r=distInit;
		r.copyNonState(this);
		auto lambda=dLambda(arg);
		static int unique=0;
		auto tmp="`categorical"~lowNum(++unique);
		r.addTmpVar(tmp);
		if(opt.backend==InferenceMethod.simulate){
			DExpr[] p;
			DExpr result=null;
			foreach(k,v;state){
				auto arr=dApply(lambda,k).simplify(one);
				auto len=dField(arr,"length").simplify(one);
				auto qlen=cast(Dℚ)len;
				enforce(!!qlen && qlen.c.den==1);
				DExpr[] pCand;
				DExpr sum=zero;
				foreach(i;0..qlen.c.num.toLong()){
					auto cur=arr[i.dℚ].simplify(one);
					pCand~=cur;
					sum=(sum+cur).simplify(one);
				}
				enforce(cast(DFloat)sum||sum==one,"category probabilities must sum up to 1");
				if(!result){
					import std.random;
					p=pCand;
					real f=uniform(0.0L,1.0L);
					DExpr cur=zero;
					foreach(i,val;p){
						cur=(cur+val).simplify(one);
						auto r=dLe(dFloat(f),cur).simplify(one);
						enforce(r == zero || r == one);
						if(r==one){
							result = dℚ(i);
							break;
						}
					}
				}else enforce(p==pCand);
				r.add(dRUpdate(k,tmp,result).simplify(one),v);
			}
		}else{
			foreach(k,v;state){
				auto p=dApply(lambda,k).simplify(one);
				auto l=dField(p,"length").simplify(one);
				auto lz=l.isInteger();
				enforce(!!lz,"TODO");
				if(lz!=zero){
					// TODO: check other preconditions
					for(ℤ i=0.ℤ;i<lz.c.num;++i)
						r.add(dRUpdate(k,tmp,i.dℚ).simplify(one),(v*p[i.dℚ]).simplify(one));
				}else r.error = (r.error + v).simplify(one);
			}
		}
		this=r;
		//if(opt.backend==InferenceMethod.simulate) pickOne();
		return dField(db1,tmp);
	}
	void assignTo(DExpr lhs,DExpr rhs){
		void assignToImpl(DExpr lhs,DExpr rhs){
			if(auto id=cast(DNVar)lhs){
				auto lambda=dLambda(dRUpdate(db1,id.name,rhs));
				this=map(lambda);
			}else if(auto idx=cast(DIndex)lhs){
				assignTo(idx.e,dIUpdate(idx.e,idx.i,rhs));
			}else if(auto fe=cast(DField)lhs){
				if(fe.e == db1){
					assignTo(dVar(fe.f),rhs);
					return;
				}
				assignTo(fe.e,dRUpdate(fe.e,fe.f,rhs));
			}else if(auto tpl=cast(DTuple)lhs){
				if(!cast(DField)rhs){
					static int unique=0;
					auto tmp="`tpl"~lowNum(++unique);
					addTmpVar(tmp);
					assignTo(dField(db1,tmp),rhs);
					assignTo(lhs,dField(db1,tmp));
				}else{
					foreach(i;0..tpl.values.length)
						assignTo(tpl[i],rhs[i.dℚ].simplify(one));
				}
			}else if(cast(DPlus)lhs||cast(DMult)lhs){
				// TODO: this could be the case (if cond { a } else { b }) = c;
				// (this is also not handled in the symbolic backend at the moment)
			}else{
				assert(0,text("TODO: ",lhs," = ",rhs));
			}
		}
		assignToImpl(lhs,rhs);
	}
	DExpr call(FunctionDef fun,DExpr thisExp,DExpr arg,Scope sc){
		auto tmpVarsSave=tmpVars.dup; // (the temporaries of the caller are marginalized after the caller's statement)
		auto ncur=pushFrame();
		ncur.tmpVars=SetX!string.init;
		if(fun.isConstructor) ncur=ncur.map(dLambda(dRUpdate(db1,fun.thisVar.getName,dRecord())));
		if(thisExp) ncur=ncur.map(dLambda(dRUpdate(db1,fun.contextName,inFrame(thisExp))));
		else if(fun.isNested) ncur=ncur.map(dLambda(dRUpdate(db1,fun.contextName,inFrame(buildContextFor!readLocal(fun,sc)))));
		if(fun.isNested&&fun.isConstructor) ncur=ncur.map(dLambda(dRUpdate(db1,fun.thisVar.getName,dRecord([fun.contextName:dField(db1,fun.contextName)]))));
		if(fun.isTuple){
			DExpr updates=db1;
			foreach(i,prm;fun.params){
				updates=dRUpdate(updates,prm.getName,inFrame(arg[i.dℚ]));
			}
			if(updates != db1) ncur=ncur.map(dLambda(updates));
		}else{
			assert(fun.params.length==1);
			ncur=ncur.map(dLambda(dRUpdate(db1,fun.params[0].getName,inFrame(arg))));
		}
		auto intp=Interpreter(fun,fun.body_,ncur,true);
		auto nndist = distInit();
		intp.runFun(nndist);
		static uniq=0;
		string tmp="`call"~lowNum(++uniq);
		this=nndist.popFrame(tmp);
		foreach(v;tmpVarsSave) addTmpVar(v);
		if(thisExp&&!fun.isConstructor){
			assignTo(thisExp,dField(db1,tmp)[1.dℚ]);
			assignTo(dVar(tmp),dField(db1,tmp)[0.dℚ]);
		}
		return dField(db1,tmp);
	}
	private Dist callImpl(DExpr fun,DExpr arg){
		this=pushFrame();
		auto f=dLambda(inFrame(fun)), a=dLambda(inFrame(arg));
		auto r=distInit;
		r.copyNonState(this);
		MapX!(FunctionDef,MapX!(DExpr,DExpr)) byFun;
		foreach(k,v;state){
			auto cf=dApply(f,k).simplify(one);
			auto ca=dApply(a,k).simplify(one);
			FunctionDef fdc;
			DExpr ctx;
			if(auto bcf=cast(DDPContextFun)cf){
				fdc=bcf.def;
				ctx=bcf.ctx;
			}else if(auto bff=cast(DDPFun)cf) fdc=bff.def;
			else assert(0,text(cf," ",typeid(cf)));
			DExpr nk=k;
			if(fdc.isTuple){
				foreach(i,prm;fdc.params)
					nk=dRUpdate(nk,prm.getName,ca[i.dℚ]).simplify(one);
			}else{
				assert(fdc.params.length==1);
				nk=dRUpdate(nk,fdc.params[0].getName,ca).simplify(one);
			}
			assert(!!fdc.context==!!ctx,text(fdc.context," ",ctx," ",cf));
			if(ctx) nk=dRUpdate(nk,fdc.contextName,ctx).simplify(one);
			auto byNk=byFun.get(fdc,typeof(byFun[fdc]).init); // (hash tables return their values by value)
			byNk[nk]=v;
			byFun[fdc]=byNk;
		}
		foreach(fdc,kv;byFun){
			auto ncur=distInit;
			ncur.state=kv;
			ncur.copyNonState(this);
			ncur.tmpVars=SetX!string.init; // (the temporaries of the caller are marginalized after the caller's statement)
			auto intp=Interpreter(fdc,fdc.body_,ncur,true);
			auto nndist = distInit();
			intp.runFun(nndist);
			r+=nndist;
		}
		return r;
	}
	DExpr call(DExpr fun,DExpr arg){
		auto r=callImpl(fun,arg);
		static uniq=0;
		string tmp="`call'"~lowNum(++uniq);
		this=r.popFrame(tmp);
		return dField(db1,tmp);
	}
	Dist normalize(){
		auto r=distInit();
		r.copyNonState(this);
		DExpr tot=r.error;
		foreach(k,v;state) tot=(tot+v).simplify(one);
		if(!opt.noCheck && tot == zero) r.error=one;
		else if(cast(Dℚ)tot) foreach(k,v;state) r.add(k,(v/tot).simplify(one));
		else{
			if(!opt.noCheck) r.error=(dNeqZ(tot)*r.error+dEqZ(tot)).simplify(one);
			foreach(k,v;state) r.add(k,((v/tot)*dNeqZ(tot)).simplify(one));
		}
		return r;
	}
	DExpr infer(DExpr fun){
		assert(opt.backend != InferenceMethod.simulate,"TODO: higher-order inference in simulate backend");
		auto r=distInit;
		r.copyNonState(this);
		static uniq=0;
		string tmp="`infer"~lowNum(++uniq);
		addTmpVar(tmp);
		foreach(k,v;state){
			auto cur=distInit;
			cur.add(k,v);
			cur=cur.callImpl(fun,dTuple([])); // TODO: group calls that depend on identical information
			cur=cur.map(dLambda(dRecord(["`value":dField(db1,"`value")])));
			cur.tmpVars.clear();
			cur=cur.normalize();
			r.add(dRUpdate(k,tmp,dDPDist(cur)),v);
		}
		this=r;
		return dField(db1,tmp);
	}
	DExpr distSample(DExpr dist){
		auto r=distInit;
		r.copyNonState(this);
		auto d=dLambda(dist);
		static uniq=0;
		string tmp="`sample"~lowNum(++uniq);
		r.addTmpVar(tmp);
		if(opt.backend==InferenceMethod.simulate){
			DExpr theDist=null;
			DExpr result=null;
			foreach(k,v;state){
				auto dbf=cast(DDPDist)dApply(d,k).simplify(one);
				assert(!!dbf,text(dbf," ",d));
				if(!result){
					theDist=dbf;
					real f=uniform(0.0L,1.0L);
					DExpr cur=zero;
					DExpr sum=zero;
					foreach(dk,dv;dbf.dist.state)
						sum=(sum+dv).simplify(one);
					enforce(sum==one,"probabilities must sum up to 1");
					foreach(dk,dv;dbf.dist.state){
						cur=(cur+dv).simplify(one);
						auto r=dLe(dFloat(f),cur).simplify(one);
						enforce(r == zero || r == one);
						if(r==one){
							result = dField(dk,"`value").simplify(one);
							break;
						}
					}
				}else enforce(dbf==theDist);
				r.add(dRUpdate(k,tmp,result).simplify(one),v);
			}
		}else{
			foreach(k,v;state){
				auto dbf=cast(DDPDist)dApply(d,k).simplify(one);
				assert(!!dbf,text(dbf," ",d));
				foreach(dk,dv;dbf.dist.state) r.add(dRUpdate(k,tmp,dField(dk,"`value")).simplify(one),(v*dv).simplify(one));
				if(!opt.noCheck) r.error=(r.error+v*dbf.dist.error).simplify(one);
			}
		}
		this=r;
		// if(opt.backend==InferenceMethod.simulate) pickOne();
		return dField(db1,tmp);
	}
	DExpr distExpectation(DExpr dist){
		auto r=distInit;
		r.copyNonState(this);
		auto d=dLambda(dist);
		static uniq=0;
		string tmp="`expectation'"~lowNum(++uniq);
		r.addTmpVar(tmp);
		foreach(k,v;state){
			auto dbf=cast(DDPDist)dApply(d,k).simplify(one);
			assert(!!dbf,text(dbf," ",d));
			DExpr val1=zero,val2=zero;
			foreach(dk,dv;dbf.dist.state){
				val1=(val1+dv*dField(dk,"`value")).simplify(one);
				val2=(val2+dv).simplify(one);
			}
			if(!opt.noCheck&&val2==zero) r.error=(r.error+v).simplify(one);
			else if(cast(Dℚ)val2) r.add(dRUpdate(k,tmp,val1/val2).simplify(one),v);
			else{
				if(!opt.noCheck) r.error=(r.error+v*dEqZ(val2)).simplify(one);
				r.add(dRUpdate(k,tmp,val1/val2).simplify(one),(v*dNeqZ(val2)).simplify(one));
			}
		}
		this=r;
		return dField(db1,tmp);
	}
	DExpr distError(DExpr dist){
		if(opt.noCheck) return zero;
		auto r=distInit;
		r.copyNonState(this);
		auto d=dLambda(dist);
		static uniq=0;
		string tmp="`error'"~lowNum(++uniq);
		r.addTmpVar(tmp);
		foreach(k,v;state){
			auto dbf=cast(DDPDist)dApply(d,k).simplify(one);
			assert(!!dbf,text(dbf," ",d));
			DExpr error=dbf.dist.error;
			r.add(dRUpdate(k,tmp,error).simplify(one),v);
		}
		this=r;
		return dField(db1,tmp);
	}
	void copyNonState(ref Dist rhs){
		this.tupleof[1..$]=rhs.tupleof[1..$];
	}
	void pickOne()in{assert(opt.backend==InferenceMethod.simulate);}do{
		real f = uniform(0.0L,1.0L);
		DExpr cur=zero;
		foreach(k,v;state){
			cur=(cur+v).simplify(one);
			auto r=dLe(dFloat(f),cur).simplify(one);
			assert(r == zero || r == one);
			if(r == one){
				error = zero;
				state.clear();
				state[k]=one;
				return;
			}
		}
		cur = (cur+error).simplify(one);
		assert(cur == one);
		state.clear();
		error = one;
	}
	Dist simplify(DExpr facts){
		auto r=distInit;
		r.copyNonState(this);
		foreach(k,v;state)
			r.add(k.simplify(facts),v.simplify(facts));
		return r;
	}
	Dist substitute(DVar var,DExpr expr){
		auto r=distInit;
		r.copyNonState(this);
		foreach(k,v;state)
			r.add(k.substitute(var,expr),v.substitute(var,expr));
		return r;
	}
	Dist incDeBruijnVar(int di, int free){
		auto r=distInit;
		r.copyNonState(this);
		foreach(k,v;state)
			r.add(k.incDeBruijnVar(di,free),v.incDeBruijnVar(di,free));
		return r;
	}
	int freeVarsImpl(scope int delegate(DVar) dg,ref DExprSet visited){
		foreach(k,v;state){
			if(auto r=k.freeVarsImpl(dg,visited)) return r;
			if(auto r=v.freeVarsImpl(dg,visited)) return r;
		}
		return 0;
	}
}

DExpr inFrame(DExpr arg){
	return arg.substitute(db1,dField(db1,"`frame"));
}


class DDPFun: DExpr{
	FunctionDef def;
	alias subExprs=Seq!def;
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		return def.name.name;
	}
	mixin Constant;
}
mixin FactoryFunction!DDPFun;
class DDPContextFun: DExpr{
	FunctionDef def;
	DExpr ctx;
	alias subExprs=Seq!(def,ctx);
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		return text(def.name?def.name.name:text("(",def,")"),"@(",ctx.toStringImpl(formatting,Precedence.none,binders),")");
	}
	mixin Visitors;
	override DExpr simplifyImpl(DExpr facts){ return dDPContextFun(def,ctx.simplify(facts)); }

}
mixin FactoryFunction!DDPContextFun;
class DDPDist: DExpr{
	Dist dist;
	alias subExprs=Seq!dist;
	this(Dist dist)in{assert(!dist.tmpVars.length);}do{ this.dist=dist; }
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		auto d=dist.toDistribution(["r"],false);
		d.addArgs([],true,null);
		return dApply(d.toDExpr(),dTuple([])).simplify(one).toStringImpl(formatting,prec,binders);
	}
	override DExpr simplifyImpl(DExpr facts){ return dDPDist(dist.simplify(facts)); }
	mixin Visitors;
}
DDPDist dDPDist(Dist dist)in{assert(!dist.tmpVars.length);}do{
	static MapX!(Q!(MapX!(DExpr,DExpr),DExpr),DDPDist) uniq;
	auto t=q(dist.state,dist.error);
	if(t in uniq) return uniq[t];
	auto r=new DDPDist(dist);
	uniq[t]=r;
	return r;
}

import ast.lexer: Tok;
alias ODefExp=BinaryExp!(Tok!":=");
DExpr readLocal(string name){ return dField(db1,name); }
DExpr readFunction(Identifier id)in{ assert(id && id.scope_ && isFunctionDecl(id.meaning)); }do{
	auto fd=isFunctionDecl(id.meaning);
	assert(!!fd);
	if(!fd.isNested) return dDPFun(fd);
	return dDPContextFun(fd,buildContextFor!readLocal(fd,id.scope_));
}
struct Interpreter{
	FunctionDef functionDef;
	CompoundExp statements;
	Dist cur;
	bool hasFrame=false;
	this(FunctionDef functionDef,CompoundExp statements,DExpr init,bool hasFrame){
		auto cur=distInit;
		cur.state[init]=one;
		this(functionDef,statements,cur,hasFrame);
	}
	this(FunctionDef functionDef,CompoundExp statements,Dist cur,bool hasFrame){
		this.functionDef=functionDef;
		this.statements=statements;
		this.cur=cur;
		this.hasFrame=hasFrame;
	}
	// Forgotten variables are marginalized as soon as they no longer occur in values that are still needed.
	// Values that have been computed but not yet consumed are kept on the stack `pending` (see `runExp`).
	static final class Pending{ DExpr[] values; }
	Pending pending_;
	@property Pending pending(){
		if(!pending_) pending_=new Pending();
		return pending_;
	}
	void truncatePending(size_t length){
		if(pending.values.length<=length) return;
		pending.values.length=length;
		pending.values.assumeSafeAppend();
	}
	string[] deferredForgets; // forgotten variables that still occur in pending values
	Interpreter nested(CompoundExp statements,Dist ncur){ // (shares the pending values)
		auto r=Interpreter(functionDef,statements,ncur,hasFrame);
		r.pending_=pending;
		return r;
	}
	bool isReceiver(string name){ // (methods implicitly return their receiver)
		return functionDef&&functionDef.context&&functionDef.contextName.startsWith("this")&&name==functionDef.contextName;
	}
	void deferForget(Declaration decl){
		if(isVariableDecl(decl)&&!isReceiver(decl.getName))
			deferredForgets~=decl.getName;
		else if(isClosureDecl(decl)) deferredForgets~=closureName(decl); // (other functions are not stored in the state)
	}
	void deferForgets(Declaration[] decls){
		foreach(decl;decls) deferForget(decl);
	}
	void deferForgets(BlockScope blscope_){
		if(!blscope_) return;
		deferForgets(blscope_.forgottenVarsOnEntry);
		deferForgets(blscope_.forgottenVars);
	}
	void deferForgets(ForgetExp fe){
		void defer(Expression e){
			if(auto id=cast(Identifier)e){
				if(id.meaning) deferForget(id.meaning);
				else if(!isReceiver(id.name)) deferredForgets~=id.name;
			}else if(auto tpl=cast(TupleExp)e)
				foreach(x;tpl.e) defer(x);
		}
		defer(fe.var);
	}
	static ForgetExp[] forwardedForgets(LetExp le)in{ assert(!!le.isForward(true)); }do{
		return le.s.s[1..$].map!(s=>cast(ForgetExp)s).array;
	}
	static bool references(DExpr e,string name){ // (whether `e` may refer to field `name` of the state `db1`)
		bool visit(DExpr e,int depth){ // (`depth` may underestimate the number of enclosing binders)
			if(auto v=cast(DDeBruijnVar)e) return v.i>depth; // (refers to the entire state)
			if(auto f=cast(DField)e)
				if(auto v=cast(DDeBruijnVar)f.e)
					return v.i>depth&&f.f==name;
			if(auto l=cast(DLambda)e) return visit(l.expr,depth+1);
			if(auto l=cast(DDistLambda)e) return visit(l.expr,depth+1);
			if(auto i=cast(DInt)e) return visit(i.expr,depth+1);
			if(auto s=cast(DSum)e) return visit(s.expr,depth+1);
			if(auto l=cast(DLim)e) return visit(l.e,depth)||visit(l.x,depth);
			if(auto d=cast(DDiff)e) return visit(d.e,depth)||visit(d.x,depth);
			if(auto d=cast(DDeltaOld)e) return visit(d.var,depth);
			if(auto d=cast(DDelta)e) return visit(d.e,depth)||visit(d.var,depth);
			if(cast(DDPDist)e) return false; // (distributions of values)
			bool r=false;
			e.forEachSubExpr((DExpr x){ r=visit(x,depth); return r?1:0; });
			return r;
		}
		return visit(e,0);
	}
	bool isPending(string name){
		foreach(value;pending.values)
			if(references(value,name))
				return true;
		return false;
	}
	void flushForgets(){ // marginalize the forgotten variables that no longer occur in pending values
		if(!deferredForgets.length) return;
		string[] names,rest;
		foreach(name;deferredForgets){
			if(!name) continue;
			if(isPending(name)) rest~=name;
			else names~=name;
		}
		deferredForgets=rest;
		cur=cur.marginalize(names);
	}
	void forgetDecls(Declaration[] decls){
		deferForgets(decls);
		flushForgets();
	}
	void assignTo(DExpr lhs,DExpr rhs){ // (assignment to a variable within the current state)
		for(auto root=lhs;;){ // the variable is redefined by the current statement, so it is not forgotten at its end
			if(auto idx=cast(DIndex)root) root=idx.e;
			else if(auto fe=cast(DField)root){
				if(fe.e==db1){
					cur.tmpVars.remove(fe.f);
					foreach(ref name;deferredForgets) if(name==fe.f) name=null;
					break;
				}
				root=fe.e;
			}else break;
		}
		cur.assignTo(lhs,rhs);
	}
	// The value of each subexpression is pending until its parent expression is computed. If `consumed` is set, the
	// value of `e` is consumed right away, so variables that are forgotten after `e` are marginalized afterwards.
	DExpr runExp(Expression e,bool consumed=false){
		if(!cur.state.length) return zero;
		DExpr delegate(Expression) doIt; // (see `doItPending`)
		DExpr doItConsumed(Expression e){ // (the value of `e` is consumed right after it is computed)
			if(auto le=cast(LetExp)e){
				if(le.isForward(true)){ // (no need to store the value in a temporary)
					auto r=doItConsumed(le.isForward(true));
					foreach(fe;forwardedForgets(le)) deferForgets(fe);
					return r;
				}
			}
			return doIt(e);
		}
		// TODO: get rid of code duplication
		DExpr doItImpl(Expression e){
			if(e.type == typeTy) return dTuple([]); // TODO: get rid of this
			if(auto pl=cast(PlaceholderExp)e) return dVar(pl.ident.name);
			if(auto id=cast(Identifier)e){
				if(!id.meaning&&id.name=="π") return dΠ;
				if(auto init=id.getInitializer())
					return doIt(init);
				if(auto r=lookupMeaning!(readLocal,readFunction)(id)){
					if(isMove(id)) deferForget(id.meaning); // (marginalized once its value is consumed)
					return r;
				}
				assert(0,"unsupported");
			}
			if(auto fe=cast(FieldExp)e){
				if(isBuiltIn(fe)){
					if(fe.e.type.isTupleTy||cast(ArrayTy)fe.e.type||cast(VectorTy)fe.e.type){
						assert(fe.f.name=="length");
					}
				}
				return dField(doIt(fe.e),fe.f.name);
			}
			if(auto ae=cast(AddExp)e) return doIt(ae.e1)+doIt(ae.e2);
			if(auto me=cast(SubExp)e) return doIt(me.e1)-doIt(me.e2);
			if(auto me=cast(NSubExp)e){
				auto r = doIt(me.e1)-doIt(me.e2);
				cur.assertTrue(dLambda(dGeZ(r)));
				return r;
			}
			if(auto me=cast(MulExp)e) return doIt(me.e1)*doIt(me.e2);
			if(cast(DivExp)e||cast(IDivExp)e){
				auto de=cast(ABinaryExp)e;
				auto e1=doIt(de.e1);
				auto e2=doIt(de.e2);
				cur=cur.assertTrue(dLambda(dNeqZ(e2)));
				return cast(IDivExp)e?dFloor(e1/e2):e1/e2;
			}
			if(auto me=cast(ModExp)e) return doIt(me.e1)%doIt(me.e2);
			if(auto pe=cast(PowExp)e) return doIt(pe.e1)^^doIt(pe.e2);
			if(auto ce=cast(CatExp)e) return doIt(ce.e1)~doIt(ce.e2);
			if(auto ce=cast(BitOrExp)e) return dBitOr(doIt(ce.e1),doIt(ce.e2));
			if(auto ce=cast(BitXorExp)e) return dBitXor(doIt(ce.e1),doIt(ce.e2));
			if(auto ce=cast(BitAndExp)e) return dBitAnd(doIt(ce.e1),doIt(ce.e2));
			if(auto upe=cast(UPlusExp)e) return doIt(upe.e);
			if(auto ume=cast(UMinusExp)e) return -doIt(ume.e);
			if(auto ume=cast(UNotExp)e) return dEqZ(doIt(ume.e));
			if(auto ume=cast(UBitNotExp)e) return -doIt(ume.e)-1;
			if(auto le=cast(LambdaExp)e){
				if(le.fd.isNested){
					return dDPContextFun(le.fd,buildContextFor!readLocal(le.fd,le.fd.scope_));
				}
				return dDPFun(le.fd);
			}
			if(auto ce=cast(CallExp)e){
				auto id=cast(Identifier)ce.e;
				auto fe=cast(FieldExp)ce.e;
				DExpr thisExp=null;
				if(fe){
					id=fe.f;
					thisExp=doIt(fe.e);
				}
				if(id){
					if(auto fun=isFunctionDecl(id.meaning)){
						auto arg=doIt(ce.arg); // TODO: allow temporaries within arguments
						return cur.call(fun,thisExp,arg,id.scope_);
					}
					if(!fe && isBuiltIn(id)){
						switch(id.name){
							case "Marginal":
								enforce(0,"TODO");
								assert(0);
							case "sampleFrom":
								Expression[] args;
								if(auto tpl=cast(TupleExp)ce.arg) args=tpl.e;
								else args=[ce.arg];
								assert(args.length);
								auto getArg(){
									return args[1..$].length==1?doIt(args[1]):dTuple(args[1..$].map!doIt.array);
								}
								auto literal=cast(LiteralExp)args[0];
								assert(literal&&literal.lit.type==Tok!"``");
								auto str=literal.lit.str;
								import samplefrom;
								static real toFloat(DExpr e){
									if(auto q=cast(Dℚ)e) return toReal(q.c);
									if(auto f=cast(DFloat)e) return f.c;
									enforce(0,"parameters to sampling procedure must be constant");
									assert(0);
								}
								final switch(getToken(str)) with(Token){
									case exp:
										assert(args[1..$].length==1);
										return dE^^doIt(args[1]);
									case log:
										assert(args[1..$].length==1);
										return dLog(doIt(args[1]));
									case sin:
										assert(args[1..$].length==1);
										return dSin(doIt(args[1]));
									case cos:
										assert(args[1..$].length==1);
										return dCos(doIt(args[1]));
									case abs:
										assert(args[1..$].length==1);
										return dAbs(doIt(args[1]));
									case floor:
										assert(args[1..$].length==1);
										return dFloor(doIt(args[1]));
									case ceil:
										assert(args[1..$].length==1);
										return dCeil(doIt(args[1]));
									case array:
										assert(args[1..$].length==2);
										return dArray(doIt(args[1]),dLambda(doIt(args[2]).incDeBruijnVar(1,0)));
									case inferPrecondition:
										return one; // TODO
									case infer:
										return cur.infer(getArg());
									case errorPr:
										return cur.distError(getArg());
									case samplePrecondition:
										return one; // TODO
									case sample:
										if(opt.noCheck){
											assert(args[1..$].length==1);
											return cur.distSample(getArg());
										}else{
											assert(args[1..$].length==2);
											return cur.distSample(getArg()[0.dℚ].simplify(one));
										}
									case expectation:
										if(opt.noCheck){
											assert(args[1..$].length==1);
											return cur.distExpectation(getArg());
										}else{
											assert(args[1..$].length==2);
											return cur.distExpectation(getArg()[0.dℚ].simplify(one));
										}
									case uniformIntPrecondition: // (TODO: remove)
										return one; // TODO
									case uniformInt: // uniformInt
										return cur.uniformInt(getArg());
									case categoricalPrecondition:
										return one; // TODO?
									case categorical:
										return cur.categorical(getArg());
									case binomial:
										assert(args[1..$].length==2);
										DExpr arg=getArg();
										auto n_=arg[0.dℚ], p=arg[1.dℚ].incDeBruijnVar(1,0);
										auto n=n_.incDeBruijnVar(1,0);
										return cur.categorical(dArray(n_+1,dLambda(dNChooseK(n,db1)*p^^db1*(1-p)^^(n-db1))).simplify(one));
									case gauss:
										enforce(opt.backend==InferenceMethod.simulate,"cannot sample from Gaussian with --dp");
										auto arg=dLambda(getArg()).simplify(one);
										real μ,ν;
										bool hasResult;
										DExpr result;
										foreach(k,v;cur.state){
											auto gArgs=dApply(arg,k);
											auto μCand=toFloat(gArgs[0.dℚ].simplify(one)), νCand=toFloat(gArgs[1.dℚ].simplify(one));
											if(!hasResult){
												μ=μCand, ν=νCand;
												import std.math, std.mathspecial, std.random;
												result=dFloat(sampleGauss(μ,ν));
												hasResult=true;
											}else enforce(μ==μCand && ν==νCand);
										}
										assert(hasResult);
										return result;
									case uniform:
										enforce(opt.backend==InferenceMethod.simulate,"cannot sample from Uniform with --dp");
										auto arg=dLambda(getArg()).simplify(one);
										real a,b;
										bool hasResult;
										DExpr result;
										foreach(k,v;cur.state){
											auto uArgs=dApply(arg,k);
											auto aCand=toFloat(uArgs[0.dℚ].simplify(one)), bCand=toFloat(uArgs[1.dℚ].simplify(one));
											if(!hasResult){
												a=aCand, b=bCand;
												result=dFloat(sampleUniform(a,b));
												hasResult=true;
											}else enforce(a==aCand && b==bCand);
										}
										assert(hasResult);
										return result;
									case laplace:
										enforce(opt.backend==InferenceMethod.simulate,"cannot sample from Laplace with --dp");
										auto arg=dLambda(getArg()).simplify(one);
										real μ,b;
										bool hasResult;
										DExpr result;
										foreach(k,v;cur.state){
											auto lArgs=dApply(arg,k);
											auto μCand=toFloat(lArgs[0.dℚ].simplify(one)),bCand=toFloat(lArgs[1.dℚ].simplify(one));
											if(!hasResult){
												μ=μCand, b=bCand;
												import std.math: log;
												result=dFloat(sampleLaplace(μ,b));
												hasResult=true;
											}else enforce(μ==μCand && b==bCand);
										}
										assert(hasResult);
										return result;
									case rayleigh:
										enforce(opt.backend==InferenceMethod.simulate,"cannot sample from Rayleigh with --dp");
										auto arg=dLambda(getArg()).simplify(one);
										real ν;
										bool hasResult;
										DExpr result;
										foreach(k,v;cur.state){
											auto νCand=toFloat(dApply(arg,k).simplify(one));
											if(!hasResult){
												ν=νCand;
												import std.math: log, sqrt;
												result=dFloat(sampleRayleigh(ν));
												hasResult=true;
											}else enforce(ν==νCand);
										}
										assert(hasResult);
										return result;
									case pareto:
										enforce(opt.backend==InferenceMethod.simulate,"cannot sample from Pareto with --dp");
										auto arg=dLambda(getArg()).simplify(one);
										real a,b;
										bool hasResult;
										DExpr result;
										foreach(k,v;cur.state){
											auto pArgs=dApply(arg,k);
											auto aCand=toFloat(pArgs[0.dℚ].simplify(one)),bCand=toFloat(pArgs[1.dℚ].simplify(one));
											if(!hasResult){
												a=aCand, b=bCand;
												import std.math: log;
												result=dFloat(samplePareto(a,b));
												hasResult=true;
											}else enforce(a==aCand && b==bCand);
										}
										assert(hasResult);
										return result;
									case gamma:
										enforce(opt.backend==InferenceMethod.simulate,"cannot sample from Gamma with --dp");
										auto arg=dLambda(getArg()).simplify(one);
										real α,β;
										bool hasResult;
										DExpr result;
										foreach(k,v;cur.state){
											auto gArgs=dApply(arg,k);
											auto αCand=toFloat(gArgs[0.dℚ].simplify(one)),βCand=toFloat(gArgs[1.dℚ].simplify(one));
											if(!hasResult){
												α=αCand, β=βCand;
												import std.math: log;
												result=dFloat(sampleGamma(α,β));
												hasResult=true;
											}else enforce(α==αCand && β==βCand);
										}
										assert(hasResult);
										return result;
									case exponential:
										enforce(opt.backend==InferenceMethod.simulate,"cannot sample from Exponential with --dp");
										auto arg=dLambda(getArg()).simplify(one);
										real λ;
										bool hasResult;
										DExpr result;
										foreach(k,v;cur.state){
											auto λCand=toFloat(dApply(arg,k).simplify(one));
											if(!hasResult){
												λ=λCand;
												import std.math: log, sqrt;
												result=dFloat(sampleExponential(λ));
												hasResult=true;
											}else enforce(λ==λCand);
										}
										assert(hasResult);
										return result;
									case flip, none:
										static DDPDist[const(char)*] dists; // NOTE: it is actually important that identical strings with different addresses get different entries (parameters are substituted)
										if(str.ptr !in dists){
											auto dist=new Distribution();
											auto info=analyzeSampleFrom(ce,new SimpleErrorHandler(),dist);
											if(info.error) enforce(0,"TODO");
											auto retVars=info.retVars,paramVars=info.paramVars,newDist=info.newDist;
											foreach(i,pvar;paramVars){
												auto expr=doIt(args[1+i]);
												newDist=newDist.substitute(pvar,expr); // TODO: use substituteAll
											}
											dist.distribute(newDist);
											auto tmp=dist.declareVar("`tmp");
											dist.initialize(tmp,dTuple(cast(DExpr[])retVars.map!(v=>v.tmp).array),contextTy);
											foreach(v;info.retVars) dist.marginalize(v.tmp);
											dist.simplify();
											auto smpl=distInit();
											void gather(DExpr e,DExpr factor){
												enforce(!cast(DInt)e,text("TODO: ",ce.e));
												foreach(s;e.summands){
													foreach(f;s.factors){
														if(auto dd=cast(DDelta)f){
															assert(dd.var == tmp);
															smpl.add(dRecord(["`value":retVars.length==1?dd.e[0.dℚ].simplify(one):dd.e]),(factor*s.withoutFactor(f)).substitute(tmp,dd.e).simplify(one));
														}else if(auto sm=cast(DPlus)f){
															gather(sm,factor*s.withoutFactor(f));
														}
													}
												}
											}
											gather(dist.distribution,one);
											dists[str.ptr]=dDPDist(smpl);
										}
										return cur.distSample(dists[str.ptr]);
									}
							case "Expectation":
								auto arg=doItConsumed(ce.arg);
								return cur.expectation(dLambda(arg),hasFrame);
							default:
								assert(0, text("unsupported: ",id.name));
						}
					}
				}
				auto fun=doIt(ce.e), arg=doIt(ce.arg);
				return cur.call(fun,arg);
			}
			if(auto idx=cast(IndexExp)e) return dIndex(doIt(idx.e),doIt(idx.a)); // TODO: bounds checking
			if(auto sl=cast(SliceExp)e) return dSlice(doIt(sl.e),doIt(sl.l),doIt(sl.r)); // TODO: bounds checking
			if(auto le=cast(LiteralExp)e){
				if(le.lit.type==Tok!"0"){
					auto n=le.lit.str.split(".");
					if(n.length==1) n~="";
					return (dℚ((n[0]~n[1]).ℤ)/(ℤ(10)^^n[1].length)).simplify(one);
				}else if(le.lit.type==Tok!".0"){
					import std.conv: to;
					return dFloat(to!real(le.lit.str));
				}
			}
			if(auto vfe=cast(VectorForExp)e){
				enforce(vfe.fd&&cast(FunTy)typeForDecl(vfe.fd),"vector comprehension not analyzed");
				DExpr[] args;
				if(auto range=vfe.fe.aggr.isRange){
					auto l=doIt(range.left).simplify(one), r=doIt(range.right).simplify(one);
					auto s=range.step?doIt(range.step).simplify(one):one;
					auto lz=l.isInteger(),rz=r.isInteger(),sz=s.isInteger();
					enforce(lz&&rz&&sz,"TODO: vector comprehensions with non-constant bounds or steps");
					enforce(sz.c.num!=0,"vector comprehension step should be nonzero");
					auto iter=forRangeIteration(lz.c.num,sz.c.num,rz.c.num,range.leftExclusive,range.rightExclusive);
					for(ℤ j=iter.start;iter.inRange(j);j+=iter.step) args~=dℚ(j);
				}else if(auto cnt=vfe.fe.aggr.isContainer){
					auto c=doIt(cnt.e);
					DExpr len;
					if(auto tt=cnt.e.type.isTupleTy) len=dℚ(tt.length);
					else len=dField(c,"length").simplify(one);
					auto lenz=len.isInteger();
					enforce(!!lenz,"TODO: vector comprehensions over containers of non-constant length");
					for(ℤ k=0;k<lenz.c.num;k++) args~=c[dℚ(k)].simplify(one);
				}else assert(0);
				DExpr[] values;
				foreach(arg;args) values~=cur.call(vfe.fd,null,arg,vfe.fd.scope_);
				return dArray(values);
			}
			if(auto le=cast(LetExp)e){
				static uniq=0;
				if(auto fwd=le.isForward(true)){ // e.g., `let{ t := e; forget(x); } in t`, as inserted after last uses
					auto r=doIt(fwd);
					auto numDeferred=deferredForgets.length;
					foreach(fe;forwardedForgets(le)) deferForgets(fe);
					if(deferredForgets[numDeferred..$].any!(name=>references(r,name))){
						// store the value in a temporary, so that the forgotten variables can be marginalized now
						string tmp="`let"~lowNum(++uniq);
						cur.assignTo(dField(db1,tmp),r);
						r=dField(db1,tmp);
						assert(pending.values.length);
						pending.values[$-1]=r;
						deferredForgets~=tmp; // (marginalized once its value is consumed)
					}
					flushForgets();
					return r;
				}
				// the statements are executed as part of the enclosing statement
				auto tmpVarsSave=cur.tmpVars.dup;
				cur.tmpVars.clear();
				auto retDist=distInit;
				deferForgets(le.s.blscope_);
				flushForgets();
				foreach(s;le.s.s){
					if(auto fe=cast(ForgetExp)s){
						deferForgets(fe);
						flushForgets();
						continue;
					}
					runStm(s,retDist);
				}
				enforce(!retDist.state.length,"early returns from `let` expression not supported");
				auto r=doIt(le.e);
				// keep the result in a temporary, the variables local to the `let` expression are marginalized afterwards
				string tmp="`let"~lowNum(++uniq);
				cur.assignTo(dField(db1,tmp),r);
				foreach(v;tmpVarsSave) cur.addTmpVar(v);
				pending.values[$-1]=dField(db1,tmp);
				deferredForgets~=tmp;
				void markLocals(Expression e){
					e=unwrap(e);
					if(auto id=cast(Identifier)e) deferredForgets~=id.name;
					else if(auto tpl=cast(TupleExp)e) foreach(x;tpl.e) markLocals(x);
					else if(auto vec=cast(VectorExp)e) foreach(x;vec.e) markLocals(x);
					else if(auto ce=cast(CatExp)e){ markLocals(ce.e1); markLocals(ce.e2); }
				}
				foreach(s;le.s.s)
					if(auto de=cast(ODefExp)s)
						markLocals(de.e1);
				flushForgets();
				return dField(db1,tmp);
			}
			if(auto cmp=cast(CompoundExp)e){
				if(cmp.s.length==1)
					return doIt(cmp.s[0]);
			}else if(auto ite=cast(IteExp)e){
				auto numPending=pending.values.length;
				auto cond=runExp(ite.cond,true);
				auto curP=cur.eraseErrors();
				cur=cur.observe(dLambda(dNeqZ(cond).simplify(one)));
				curP=curP.observe(dLambda(dEqZ(cond).simplify(one)));
				truncatePending(numPending); // (the condition is consumed, the pending forgets are performed in the branches)
				auto forgets=deferredForgets;
				deferredForgets=[];
				static uniq=0;
				string tmp="`ite"~lowNum(++uniq);
				Dist runBranch(CompoundExp branch,Dist bcur){ // (the value of the branch is stored in a temporary)
					auto intp=nested(branch,bcur);
					intp.deferredForgets=forgets.dup;
					if(branch.blscope_) intp.forgetDecls(branch.blscope_.forgottenVarsOnEntry);
					auto r=intp.runExp(branch.s.length==1?branch.s[0]:branch);
					intp.cur.assignTo(dField(db1,tmp),r);
					truncatePending(numPending);
					if(branch.blscope_) intp.deferForgets(branch.blscope_.forgottenVars);
					intp.flushForgets();
					deferredForgets~=intp.deferredForgets;
					return intp.cur;
				}
				assert(!!ite.othw);
				cur=runBranch(ite.then,cur);
				cur+=runBranch(ite.othw,curP);
				deferredForgets~=tmp; // (marginalized once its value is consumed)
				return dField(db1,tmp);
			}else if(auto tpl=cast(TupleExp)e){
				auto dexprs=tpl.e.map!doIt.array;
				return dTuple(dexprs);
			}else if(auto arr=cast(VectorExp)e){
				auto dexprs=arr.e.map!doIt.array;
				return dArray(dexprs);
			}else if(auto ae=cast(AssertExp)e){
				if(auto c=runExp(ae.e)){
					cur=cur.assertTrue(dLambda(dNeqZ(c)));
					return dTuple([]);
				}
			}else if(auto tae=cast(TypeAnnotationExp)e){
				return doIt(tae.e);
			}else if(cast(Type)e)
				return dTuple([]); // 'erase' types
			else{
				enum common=q{
					auto e1=doIt(b.e1),e2=doIt(b.e2);
				};
				// TODO: short-circuit evaluation for `&&` and `||`
				if(auto le=cast(ALogicExp)e){
					deferForgets(le.blscope_);
					deferForgets(le.forgetScope);
				}
				if(cast(AndThenExp)e||cast(AndExp)e){
					auto b=cast(ABinaryExp)e;
					auto e1=doIt(b.e1), e2=doIt(b.e2);
					return e1*e2;
				}else if(cast(OrElseExp)e||cast(OrExp)e){
					DExprSet disjuncts;
					void collect(Expression e){
						if(cast(OrElseExp)e||cast(OrExp)e){
							auto or=cast(ABinaryExp)e;
							collect(or.e1);
							collect(or.e2);
						}else disjuncts.insert(doIt(e));
					}
					collect(e);
					return dNeqZ(dPlus(disjuncts));
				}else if(auto b=cast(XorExp)e){
					mixin(common);
					return dNeq(dNeqZ(e1),dNeqZ(e2));
				}else with(DIvr.Type)if(auto b=cast(LtExp)e){
					mixin(common);
					return dLt(e1,e2);
				}else if(auto b=cast(LeExp)e){
					mixin(common);
					return dLe(e1,e2);
				}else if(auto b=cast(GtExp)e){
					mixin(common);
					return dGt(e1,e2);
				}else if(auto b=cast(GeExp)e){
					mixin(common);
					return dGe(e1,e2);
				}else if(auto b=cast(EqExp)e){
					mixin(common);
					return dEq(e1,e2);
				}else if(auto b=cast(NeqExp)e){
					mixin(common);
					return dNeq(e1,e2);
				}
			}
			enforce(0,text("TODO: ",e));
			assert(0);
		}
		DExpr doItPending(Expression e){
			auto numPending=pending.values.length;
			auto r=doItImpl(e);
			truncatePending(numPending); // (the values of the subexpressions are consumed)
			pending.values~=r;
			flushForgets();
			return r;
		}
		doIt=&doItPending;
		return consumed?doItConsumed(e):doIt(e);
	}
	void runStm(Expression e,ref Dist retDist){
		if(!cur.state.length) return;
		if(opt.trace) writeln("statement: ",e);
		scope(success) flushForgets();
		auto numPending=pending.values.length;
		scope(exit) truncatePending(numPending); // (the values computed by the statement are consumed)
		if(auto de=cast(ODefExp)e){
			auto rhs=runExp(de.e2,true).simplify(one);
			void defineLhs(Expression lhs,DExpr rhs,Expression ty){
				if(!cur.state.length) return;
				if(auto tae=cast(TypeAnnotationExp)lhs) return defineLhs(tae.e,rhs,tae.type?tae.type:ty);
				if(cast(WildcardExp)lhs) return;
				DExpr bind(DExpr rhs){ // (avoids duplicate evaluation)
					if(cast(DField)rhs) return rhs;
					static int unique=0;
					auto tmp="`def"~lowNum(++unique);
					cur.addTmpVar(tmp);
					cur.assignTo(dField(db1,tmp),rhs);
					return dField(db1,tmp);
				}
				if(auto ce=cast(CatExp)lhs){ // split
					auto l1=knownLength(ce.e1,false), l2=knownLength(ce.e2,false);
					enforce(l1||l2,"split not supported");
					rhs=bind(rhs);
					DExpr len=dField(rhs,"length");
					if(auto tt=ty.isTupleTy) len=dℚ(tt.length);
					auto mid=l1?runExp(l1):len-runExp(l2);
					if(l1&&l2) cur=cur.assertTrue(dLambda(dEq(mid+runExp(l2),len)));
					else cur=cur.assertTrue(dLambda(dLe(mid,len)*dGeZ(mid)));
					defineLhs(ce.e1,dSlice(rhs,zero,mid).simplify(one),ce.e1.type);
					defineLhs(ce.e2,dSlice(rhs,mid,len).simplify(one),ce.e2.type);
					return;
				}
				Expression[] elements;
				if(auto tpl=cast(TupleExp)lhs) elements=tpl.e;
				else if(auto vec=cast(VectorExp)lhs) elements=vec.e;
				else return assignTo(runExp(lhs).simplify(one),rhs);
				rhs=bind(rhs);
				if(auto tt=ty.isTupleTy){
					enforce(tt.length==elements.length,"wrong number of elements to unpack");
					foreach(k,x;elements) defineLhs(x,rhs[k.dℚ].simplify(one),tt[k]);
				}else if(auto at=cast(ArrayTy)ty){
					cur=cur.assertTrue(dLambda(dEq(dField(rhs,"length"),dℚ(elements.length))));
					foreach(k,x;elements) defineLhs(x,rhs[k.dℚ].simplify(one),at.next);
				}else enforce(0,text("unsupported left hand side for definition: ",lhs));
			}
			defineLhs(de.e1,rhs,de.e2.type);
		}else if(auto ae=cast(AssignExp)e){
			auto lhs=runExp(ae.e1),rhs=runExp(ae.e2,true);
			assignTo(lhs,rhs);
		}else if(isOpAssignExp(e)){
			DExpr perform(DExpr a,DExpr b){
				if(cast(OrElseAssignExp)e||cast(OrAssignExp)e) return dNeqZ(dNeqZ(a)+dNeqZ(b)); // TODO: short-circuit evaluation for `||=`
				if(cast(AndThenAssignExp)e||cast(AndAssignExp)e) return dNeqZ(a)*dNeqZ(b); // TODO: short-circuit evaluation for `&&=`
				if(cast(XorAssignExp)e) return dNeq(dNeqZ(a),dNeqZ(b));
				if(cast(AddAssignExp)e) return a+b;
				if(cast(SubAssignExp)e) return a-b;
				if(cast(NSubAssignExp)e){
					cur=cur.assertTrue(dLambda(dGe(a,b)));
					return a-b;
				}
				if(cast(MulAssignExp)e) return a*b;
				if(cast(DivAssignExp)e||cast(IDivAssignExp)e){
					cur=cur.assertTrue(dLambda(dNeqZ(b)));
					return cast(IDivAssignExp)e?dFloor(a/b):a/b;
				}
				if(cast(ModAssignExp)e) return a%b;
				if(cast(PowAssignExp)e){
					// TODO: enforce constraints on domain
					return a^^b;
				}
				if(cast(CatAssignExp)e) return a~b;
				if(cast(BitOrAssignExp)e) return dBitOr(a,b);
				if(cast(BitXorAssignExp)e) return dBitXor(a,b);
				if(cast(BitAndAssignExp)e) return dBitAnd(a,b);
				assert(0);
			}
			auto be=cast(ABinaryExp)e;
			assert(!!be);
			auto lhs=runExp(be.e1); // TODO: keep lhs stable!
			auto rhs=runExp(be.e2,true);
			assignTo(lhs,perform(lhs,rhs));
		}else if(cast(CallExp)e||cast(TypeAnnotationExp)e){
			runExp(e,true);
		}else if(auto ce=cast(CompoundExp)e){
			if(ce.blscope_) forgetDecls(ce.blscope_.forgottenVarsOnEntry);
			foreach(s;ce.s) runStm(s,retDist);
			if(ce.blscope_) forgetDecls(ce.blscope_.forgottenVars);
		}else if(auto ite=cast(IteExp)e){
			auto cond=runExp(ite.cond,true);
			auto curP=cur.eraseErrors();
			cur=cur.observe(dLambda(dNeqZ(cond)));
			curP=curP.observe(dLambda(dEqZ(cond).simplify(one)));
			truncatePending(numPending); // (the condition is consumed, the pending forgets are performed in the branches)
			auto forgets=deferredForgets;
			deferredForgets=[];
			auto thenIntp=nested(ite.then,cur);
			thenIntp.deferredForgets=forgets.dup;
			thenIntp.flushForgets();
			thenIntp.run(retDist);
			cur=thenIntp.cur;
			deferredForgets~=thenIntp.deferredForgets;
			auto othwIntp=nested(ite.othw,curP);
			othwIntp.deferredForgets=forgets.dup;
			othwIntp.flushForgets();
			if(ite.othw) othwIntp.run(retDist);
			curP=othwIntp.cur;
			deferredForgets~=othwIntp.deferredForgets;
			cur+=curP;
		}else if(auto re=cast(RepeatExp)e){
			auto rep=runExp(re.num,true).simplify(one);
			truncatePending(numPending);
			flushForgets();
			if(auto z=rep.isInteger()){
				auto intp=nested(re.bdy,cur);
				scope(exit) deferredForgets~=intp.deferredForgets;
				foreach(x;0.ℤ..z.c.num){
					if(opt.trace) writeln("repetition: ",x+1);
					intp.run(retDist);
					// TODO: marginalize locals
				}
				cur=intp.cur;
			}else{
				auto bound=dFloor(rep);
				auto intp=nested(re.bdy,distInit());
				scope(exit) deferredForgets~=intp.deferredForgets;
				intp.cur.state = cur.state;
				cur.state=typeof(cur.state).init;
				for(ℤ x=0;;++x){
					cur += intp.cur.observe(dLambda(dLe(bound,x.dℚ)));
					intp.cur = intp.cur.observe(dLambda(dLt(x.dℚ,bound)));
					intp.cur.error = zero;
					if(!intp.cur.state.length) break;
					if(opt.trace) writeln("repetition: ",x+1);
					intp.run(retDist);
				}
			}
		}else if(auto fe=cast(ForExp)e){
			auto range=fe.aggr.isRange;
			enforce(!!range,"TODO: for loops over containers"); // (lowered to loops over ranges during semantic analysis)
			auto l=runExp(range.left,true).simplify(one), r=runExp(range.right,true).simplify(one);
			auto s=range.step?runExp(range.step,true).simplify(one):one;
			truncatePending(numPending);
			flushForgets();
			auto lz=l.isInteger(),rz=r.isInteger(),sz=s.isInteger();
			enforce(!sz||sz.c.num!=0,"for loop step should be nonzero");
			if(lz&&rz&&sz){
				auto intp=nested(fe.bdy,cur);
				scope(exit) deferredForgets~=intp.deferredForgets;
				auto iter=forRangeIteration(lz.c.num,sz.c.num,rz.c.num,range.leftExclusive,range.rightExclusive);
				for(ℤ j=iter.start;iter.inRange(j);j+=iter.step){
					if(opt.trace) writeln("loop-index: ",j);
					intp.cur.assignTo(dVar(fe.var.name),dℚ(j));
					intp.run(retDist);
					// TODO: marginalize locals
				}
				cur=intp.cur;
			}else{
				enforce(!range.step,"TODO: for loops with non-constant bounds and steps");
				static uniq=0;
				auto tmp="`loopIndex"~lowNum(++uniq);
				cur.assignTo(dVar(tmp),range.leftExclusive?dFloor(l)+1:dCeil(l));
				auto bound=range.rightExclusive?dCeil(r)-1:dFloor(r);
				auto intp=nested(fe.bdy,distInit());
				scope(exit) deferredForgets~=intp.deferredForgets;
				intp.cur.state = cur.state;
				cur.state=typeof(cur.state).init;
				auto cond = dLambda(dLe(dField(db1,tmp),bound).simplify(one));
				auto ncond = dLambda(dLt(bound,dField(db1,tmp)).simplify(one));
				auto upd = (dField(db1,tmp)+1).simplify(one);
				for(int x=0;;++x){
					cur += intp.cur.observe(ncond);
					intp.cur = intp.cur.observe(cond);
					intp.cur.error = zero;
					if(!intp.cur.state.length) break;
					intp.cur.assignTo(dVar(fe.var.name),dField(db1,tmp));
					if(opt.trace) writeln("repetition: ",x+1);
					intp.run(retDist);
					intp.cur.assignTo(dVar(tmp),upd);
					// TODO: marginalize locals
				}
			}
		}else if(auto we=cast(WhileExp)e){
			auto intp=nested(we.bdy,distInit());
			scope(exit) deferredForgets~=intp.deferredForgets;
			intp.cur.state=cur.state;
			cur.state=typeof(cur.state).init;
			while(intp.cur.state.length){
				auto rcond = intp.runExp(we.cond).simplify(one);
				auto cond = dLambda(dNeqZ(rcond).simplify(one));
				auto ncond = dLambda(dEqZ(rcond).simplify(one));
				cur += intp.cur.observe(ncond);
				intp.cur = intp.cur.observe(cond);
				intp.cur.error = zero;
				intp.run(retDist);
				// TODO: marginalize locals
			}
		}else if(auto re=cast(ReturnExp)e){
			auto forgets=deferredForgets.dup;
			scope(success) deferredForgets=forgets; // (the remaining code is unreachable)
			auto value = runExp(re.e,true);
			if(functionDef.context&&functionDef.contextName.startsWith("this"))
				value = dTuple([value,dField(db1,functionDef.contextName)]);
			auto rec=["`value":value];
			if(hasFrame) rec["`frame"]=dField(db1,"`frame");
			cur.tmpVars=SetX!string.init; // (the variables of the function are not part of the returned state)
			retDist += cur.map(dLambda(dRecord(rec)));
			cur=distInit;
			if(re.expected.length)
				expected.parse(re.expected,new SimpleErrorHandler(),re.loc);
		}else if(auto ae=cast(AssertExp)e){
			auto cond=dNeqZ(runExp(ae.e,true));
			cur=cur.assertTrue(dLambda(cond));
		}else if(auto oe=cast(ObserveExp)e){
			enforce(opt.backend != InferenceMethod.simulate,"TODO: observe with --simulate");
			auto cond=dNeqZ(runExp(oe.e,true));
			cur=cur.observe(dLambda(cond));
		}else if(auto fe=cast(ForgetExp)e){
			deferForgets(fe); // (marginalized at the end of the statement)
		}else if(auto ce=cast(CommaExp)e){
			runStm(ce.e1,retDist);
			runStm(ce.e2,retDist);
		}else if(auto decl=cast(Declaration)e){
			if(isClosureDecl(decl)) // nested functions and data types capture their context when they are defined
				cur.assignTo(dField(db1,closureName(decl)),captureContext!readLocal(decl,decl.scope_));
		}else{
			enforce(0,text("TODO: ",e));
		}
		cur=cur.marginalizeTemporaries();
	}
	void run(ref Dist retDist){
		if(statements.blscope_) forgetDecls(statements.blscope_.forgottenVarsOnEntry);
		foreach(s;statements.s){
			runStm(s,retDist);
			// writeln("cur: ",cur);
		}
		if(statements.blscope_) forgetDecls(statements.blscope_.forgottenVars);
	}
	void runFun(ref Dist retDist){
		run(retDist);
		retDist+=cur;
		cur=distInit();
	}
}
