// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.stdio, std.conv, std.format, std.string, std.range, std.algorithm;

import options, backend;
import ast.lexer, ast.expression, ast.declaration, ast.type, ast.semantic_, ast.error;
import ast.scope_: BlockScope;
import ast.reverse: knownLength;
import context: isFunctionDecl, isVariableDecl, isClosureDecl, closureName, captureContext, isMove;
import distrib, sym.dexpr, util;

class Symbolic: Backend{
	this(string sourceFile){
		this.sourceFile=sourceFile;
	}
	override Distribution analyze(FunctionDef def,ErrorHandler err){
		auto dist=new Distribution();
		DNVar[] args;
		foreach(i,a;def.params) args~=dist.declareVar(a.getName);
		DNVar ctx=null;
		if(def.context){
			assert(!!def.contextVal,text(def));
			ctx=dist.declareVar(def.contextVal.getName);
			if(def.contextName!=ctx.name)
				dist.initialize(dist.declareVar(def.contextName),ctx,def.context.vtype);
		}
		if(def.isConstructor){
			assert(!!def.thisVar);
			auto thisVar=dist.declareVar(def.thisVar.getName);
			auto dd=def.scope_.getDatDecl();
			assert(dd && dd.dtype);
			DExpr[string] fields;
			if(def.context) fields[def.contextName]=ctx;
			dist.initialize(thisVar,dRecord(fields),dd.dtype);
		}
		dist.addArgs(args,def.isTuple,ctx);
		return analyzeWith(def,dist,err);
	}

	Distribution analyzeWith(FunctionDef def,Distribution dist,ErrorHandler err){
		auto a=Analyzer(this,dist,err,null,null,def);
		Distribution retDist=null;
		a.analyze(def.body_,retDist,def);
		a.applyRetDist(def,retDist);
		a.dist.simplify();
		// dw(def," ",a.dist);
		return a.dist;
	}


	Distribution getSummary(FunctionDef fun,Location loc,ErrorHandler err){
		if(fun !in summaries){
			summaries[fun]=new Distribution();
			summaries[fun].distribute(mone);
			summaries[fun]=analyze(fun,err);
		}else if(summaries[fun].distribution == mone){
			// TODO: support special cases.
			err.error("recursive dependencies unsupported",loc);
			return null;
		}
		return summaries[fun];
	}
private:
	Distribution[FunctionDef] summaries;
	string sourceFile;
}


alias ODefExp=BinaryExp!(Tok!":=");

private struct Analyzer{
	Symbolic be;
	Distribution dist;
	ErrorHandler err;
	DExpr[][string] arrays;
	DExpr[DVar] deterministic;
	FunctionDef functionDef; // the function that is being analyzed

	// Forgotten variables are marginalized as soon as they no longer occur in values that are still needed.
	// Values that have been computed but not yet consumed are kept on the stack `pending` (see `transformExp`).
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
	int deferDepth=0; // (e.g., `if` expressions that are transformed twice)
	Analyzer nested(Distribution ndist,bool dupDeterministic=true){ // (shares the pending values)
		auto r=Analyzer(be,ndist,err,arrays.dup,dupDeterministic?deterministic.dup:deterministic,functionDef);
		r.pending_=pending;
		r.deferDepth=deferDepth;
		return r;
	}

	static class Unwind: Exception{ this(){ super(""); } }
	static void unwind(){ throw new Unwind(); }

	void forgetVars(string[] names){
		SetX!DNVar vars;
		foreach(name;names){
			if(name in arrays){ arrays.remove(name); continue; }
			auto var=dVar(name);
			if(dist.hasArg(var)) continue; // (the distribution is parameterized by its arguments)
			if(functionDef&&functionDef.context&&functionDef.contextName.startsWith("this")&&name==functionDef.contextName)
				continue; // (methods implicitly return their receiver)
			if(var in dist.freeVars) vars.insert(var);
		}
		foreach(var;dist.freeVars.dup){ // (marginalize in the same order as at the end of the function)
			if(var !in vars) continue;
			deterministic.remove(var);
			dist.marginalize(var);
		}
	}
	static string forgetName(Declaration decl){
		if(!decl) return null;
		if(isVariableDecl(decl)) return decl.getName;
		if(isClosureDecl(decl)) return closureName(decl);
		return null; // (other functions are not stored in the distribution)
	}
	void forgetDecls(Declaration[] decls){
		deferForgets(decls);
		flushForgets();
	}
	void deferForgets(Declaration[] decls){
		foreach(decl;decls)
			if(auto name=forgetName(decl))
				deferredForgets~=name;
	}
	void cancelDeferredForgets(string name){ // (the variable is redefined by the current statement)
		foreach(ref n;deferredForgets)
			if(n==name)
				n=null;
	}
	bool isPending(string name){
		if(name in arrays) return false; // (pending values refer to the elements)
		auto var=dVar(name);
		foreach(value;pending.values)
			if(value.hasFreeVar(var))
				return true;
		return false;
	}
	void flushForgets(){ // marginalize the forgotten variables that no longer occur in pending values
		if(deferDepth||!deferredForgets.length) return;
		string[] names,rest;
		foreach(name;deferredForgets){
			if(!name) continue;
			if(isPending(name)) rest~=name;
			else names~=name;
		}
		deferredForgets=rest;
		forgetVars(names);
	}
	DExpr readLocal(string name){
		auto v=dVar(name);
		if(v in dist.freeVars||dist.hasArg(v)) return v;
		return null;
	}
	void defineClosure(Declaration decl){ // nested functions and data types capture their context when they are defined
		DExpr readLocal(string name){ return this.readLocal(name); }
		auto ctx=captureContext!readLocal(decl,decl.scope_);
		auto var=dVar(closureName(decl));
		if(var in dist.freeVars) dist.marginalize(var);
		var=dist.declareVar(var.name);
		assert(!!var);
		dist.initialize(var,ctx,contextTy(true));
	}
	void mergeDeterministic(ref Analyzer athen,ref Analyzer aothw){
		// (variables may be forgotten on infeasible paths, e.g., ones that have returned early)
		bool thenFeasible=athen.dist.distribution!=zero, othwFeasible=aothw.dist.distribution!=zero;
		foreach(k,v;deterministic.dup){
			auto inThen=k in athen.deterministic, inOthw=k in aothw.deterministic;
			if(thenFeasible&&!othwFeasible&&inThen) deterministic[k]=*inThen;
			else if(othwFeasible&&!thenFeasible&&inOthw) deterministic[k]=*inOthw;
			else if(inThen&&inOthw&&*inThen==*inOthw) deterministic[k]=*inThen;
			else deterministic.remove(k);
		}
	}
	void deferForgets(ForgetExp fe){
		void defer(Expression e){
			if(auto id=cast(Identifier)e){
				if(id.meaning&&isClosureDecl(id.meaning)) deferredForgets~=closureName(id.meaning);
				else if(!id.meaning||isVariableDecl(id.meaning)) deferredForgets~=id.name; // (other functions are not stored in the distribution)
			}else if(auto tpl=cast(TupleExp)e)
				foreach(x;tpl.e) defer(x);
		}
		defer(fe.var);
	}
	static ForgetExp[] forwardedForgets(LetExp le)in{ assert(!!le.isForward(true)); }do{
		return le.s.s[1..$].map!(s=>cast(ForgetExp)s).array;
	}

	DExpr transformIte(Expression iteCond,CompoundExp iteThen,CompoundExp iteOthw,bool isConstr=false){
		auto numPending=pending.values.length;
		auto cond=transformConstr(iteCond);
		if(!cond) throw new Unwind();
		auto dthen=dist.dupNoErr();
		auto var=dthen.getTmpVar("__ite");
		dthen.initialize(var,dTuple([]),tupleTy([])); // TODO: get rid of this?
		dthen.distribution=dthen.distribution*dNeqZ(cond);
		auto dothw=dist.dupNoErr();
		auto ovar=dothw.getTmpVar("__ite");
		assert(var==ovar);
		dothw.initialize(var,dTuple([]),tupleTy([])); // TODO: get rid of this?
		dothw.distribution=dothw.distribution*dEqZ(cond);
		auto forgets=deferredForgets;
		if(!isConstr){ // (the condition is consumed, the pending forgets are performed in the branches)
			truncatePending(numPending);
			deferredForgets=[];
		}
		auto athen=nested(dthen), aothw=nested(dothw);
		if(!isConstr) athen.deferredForgets=forgets.dup, aothw.deferredForgets=forgets.dup;
		else athen.deferDepth++, aothw.deferDepth++; // (the branches may be transformed again in the current distribution, see below)
		DExpr transformBranch(ref Analyzer a,CompoundExp branch){
			if(branch.blscope_) a.forgetDecls(branch.blscope_.forgottenVarsOnEntry);
			auto r=isConstr?a.transformConstr(branch):a.transformExp(branch);
			if(r&&branch.blscope_) a.forgetDecls(branch.blscope_.forgottenVars);
			return r;
		}
		auto tprior=dthen.distribution;
		auto then=transformBranch(athen,iteThen);
		if(!then) unwind();
		if(!iteOthw) unwind();
		auto oprior=dothw.distribution;
		auto othw=transformBranch(aothw,iteOthw);
		if(!othw) unwind();
		if(isConstr && aothw.dist.distribution==oprior && aothw.dist.error==zero &&
		   athen.dist.distribution==tprior && athen.dist.error==zero){
			// (the branches are transformed again in the current distribution, their forgets are deferred until the result is computed)
			deferDepth++;
			auto e1=transformConstr(iteThen), e2=transformConstr(iteOthw);
			deferDepth--;
			if(iteThen.blscope_) deferForgets(iteThen.blscope_.forgottenVarsOnEntry~iteThen.blscope_.forgottenVars);
			if(iteOthw.blscope_) deferForgets(iteOthw.blscope_.forgottenVarsOnEntry~iteOthw.blscope_.forgottenVars);
			auto r=cond*e1+dEqZ(cond)*e2;
			truncatePending(numPending);
			pending.values~=r;
			flushForgets();
			return r;
		}
		if(isConstr){
			truncatePending(numPending); // (the condition is consumed)
			pending.values~=[then,othw];
			athen.deferDepth--, aothw.deferDepth--;
			athen.flushForgets(), aothw.flushForgets();
		}
		athen.dist.assign(var,then,iteThen.s[0].type);
		aothw.dist.assign(var,othw,iteOthw.s[0].type);
		truncatePending(numPending); // (the values of the branches are consumed)
		auto dvar=dist.getTmpVar("__ite");
		dist.initialize(dvar,dTuple([]),tupleTy([]));
		dist=athen.dist.join(dist,aothw.dist);
		mergeDeterministic(athen,aothw);
		deferredForgets~=athen.deferredForgets~aothw.deferredForgets; // (variables that are not defined on both paths are marginalized by `join`)
		pending.values~=var;
		flushForgets();
		return var;
	}
	// The value of each subexpression is pending until its parent expression is computed. If `consumed` is set, the
	// value of `e` is consumed right away, so variables that are forgotten after `e` are marginalized afterwards.
	DExpr transformExp(Exp e,bool consumed=false){
		import ast.scope_,context;
		DExpr readLocal(string name){ return this.readLocal(name); }
		DExpr readFunction(Identifier id)in{ assert(id && id.scope_ && isFunctionDecl(id.meaning)); }do{
			auto fd=isFunctionDecl(id.meaning);
			assert(!!fd);
			auto summary=be.getSummary(fd,id.loc,err);
			if(fd.isNested)
				return summary.toDExprWithContext(buildContextFor!readLocal(fd,id.scope_));
			return summary.toDExpr();
		}
		DExpr delegate(Exp) doIt; // (see `doItPending`)
		DExpr doItConsumed(Exp e){ // (the value of `e` is consumed right after it is computed)
			if(auto le=cast(LetExp)e){
				if(le.isForward(true)){ // (no need to store the value in a temporary)
					auto r=doItConsumed(le.isForward(true));
					foreach(fe;forwardedForgets(le)) deferForgets(fe);
					return r;
				}
			}
			return doIt(e);
		}
		DExpr doItImpl(Exp e){
			if(e.type == typeTy) return dTuple([]); // TODO: get rid of this
			if(cast(Declaration)e||cast(BinaryExp!(Tok!":="))e){
				err.error("definition must be at top level",e.loc);
				unwind();
			}
			if(auto pl=cast(PlaceholderExp)e)
				return dVar(pl.ident.name);
			if(auto id=cast(Identifier)e){
				if(!id.meaning&&id.name=="π") return dΠ;
				if(auto init=id.getInitializer())
					return doIt(init);
				if(id.name in arrays) return dArray(arrays[id.name]);
				if(auto r=lookupMeaning!(readLocal,readFunction)(id)){
					if(isMove(id)) deferredForgets~=forgetName(id.meaning); // (marginalized once its value is consumed)
					return r;
				}
				err.error("undefined variable '"~id.name~"'",id.loc);
				unwind();
			}
			if(auto fe=cast(FieldExp)e){
				if(auto id=cast(Identifier)fe.e){
					if(id.name in arrays && fe.f.name=="length")
						return ℤ(arrays[id.name].length).dℚ;
				}
				if(isBuiltIn(fe)){
					if(fe.e.type.isTupleTy||cast(ArrayTy)fe.e.type||cast(VectorTy)fe.e.type){
						assert(fe.f.name=="length");
					}else{ assert(0); }
				}else if(auto fd=cast(FunctionDef)fe.f.meaning){
					assert(fe.f.scope_&&fe.f.meaning.scope_);
					auto summary=be.getSummary(fd,fe.f.loc,err);
					return summary.toDExprWithContext(doIt(fe.e),true);
				}else assert(cast(VarDecl)fe.f.meaning&&fe.f.scope_&&fe.f.meaning.scope_);
				return dField(doIt(fe.e),fe.f.name);
			}
			if(auto ae=cast(AddExp)e) return doIt(ae.e1)+doIt(ae.e2);
			if(auto se=cast(SubExp)e) return doIt(se.e1)-doIt(se.e2);
			if(auto se=cast(NSubExp)e){
				auto a=doIt(se.e1), b=doIt(se.e2);
				dist.assertTrue(dGe(a,b),"result of sub is negative");
				return a-b;
			}
			if(auto me=cast(MulExp)e) return doIt(me.e1)*doIt(me.e2);
			if(cast(DivExp)e||cast(IDivExp)e){
				auto de=cast(ABinaryExp)e;
				auto e1=doIt(de.e1);
				auto e2=doIt(de.e2);
				dist.assertTrue(dNeqZ(e2),formatError("division by zero",e.loc));
				return cast(IDivExp)e?dFloor(e1/e2):e1/e2;
			}
			if(auto me=cast(ModExp)e) return doIt(me.e1)%doIt(me.e2);
			if(auto pe=cast(PowExp)e){
				auto e1=doIt(pe.e1), e2=doIt(pe.e2);
				// e1>=0 or e2∈ ℤ.
				auto c1=dNeqZ(dGeZ(e1)+dIsℤ(e2));
				// e1!=0 or e2>=0
				auto c2=dNeqZ(dNeqZ(e1)+dGeZ(e2));
				dist.assertTrue(c1*c2, "arguments outside domain of ^");
				return e1^^e2;
			}
			if(auto ce=cast(CatExp)e) return doIt(ce.e1)~doIt(ce.e2);
			if(auto ce=cast(BitOrExp)e) return dBitOr(doIt(ce.e1),doIt(ce.e2));
			if(auto ce=cast(BitXorExp)e) return dBitXor(doIt(ce.e1),doIt(ce.e2));
			if(auto ce=cast(BitAndExp)e) return dBitAnd(doIt(ce.e1),doIt(ce.e2));
			if(auto upe=cast(UPlusExp)e) return doIt(upe.e);
			if(auto ume=cast(UMinusExp)e) return -doIt(ume.e);
			if(auto ume=cast(UNotExp)e) return dEqZ(doIt(ume.e));
			if(auto ume=cast(UBitNotExp)e) return -doIt(ume.e)-1;
			if(auto le=cast(LambdaExp)e){
				auto summary=be.getSummary(le.fd,le.loc,err);
				if(le.fd.isNested)
					return summary.toDExprWithContext(buildContextFor!readLocal(le.fd,le.fd.scope_));
				return summary.toDExpr();
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
						auto summary=be.getSummary(fun,ce.loc,err);
						if(!summary) unwind();
						DExpr arg=doIt(ce.arg);
						if(!arg) unwind();
						auto funty=cast(FunTy)ce.e.type;
						assert(!!funty);
						auto argty=ce.arg.type;
						assert(isSubtype(argty,funty.dom),text(argty," ",funty.dom));
						if(thisExp){
							arg=dTuple([arg,thisExp]);
							argty=tupleTy([argty,fe.e.type]);
						}
						if(!thisExp)if(fun.isNested){ // nested function calls
							assert(id.scope_,text(id," ",id.loc));
							auto ctx=buildContextFor!readLocal(fun,id.scope_);
							assert(!!ctx);
							arg=dTuple([arg,ctx]);
							argty=tupleTy([argty,contextTy]);
						}
						auto r=dist.call(summary,arg,argty);
						if(thisExp&&!fun.isConstructor){
							auto thisr=r[1.dℚ];
							r=r[0.dℚ];
							assignTo(thisExp,thisr,fe.e.type,ce.loc);
						}
						return r;
					}
					if(isBuiltIn(id)) switch(id.name){
					case "readCSV":
						err.error(text("call to 'readCSV' only supported as the right hand side of an assignment"),ce.loc);
						unwind();
						assert(0);
					case "Marginal":
						auto arg=doItConsumed(ce.arg);
						auto idist=dist.dup();
						auto r=idist.getVar("`r");
						idist.hasArgs=false;
						idist.addArgs([],true,null);
						idist.initialize(r,arg,ce.arg.type);
						foreach(v;dist.freeVars)
							idist.marginalize(v);
						idist.orderFreeVars([r],false);
						idist.renormalize();
						return dApply(idist.toDExpr(),dTuple([]));
					case "sampleFrom":
						Expression[] args;
						if(auto tpl=cast(TupleExp)ce.arg) args=tpl.e;
						else args=[ce.arg];
						auto info=analyzeSampleFrom(ce,err,dist);
						if(info.error) unwind();
						auto retVars=info.retVars,paramVars=info.paramVars,newDist=info.newDist;
						foreach(i,pvar;paramVars){
							auto expr=doIt(args[1+i]);
							newDist=newDist.substitute(pvar,expr);
						}
						dist.distribute(newDist);
						return retVars.length==1?retVars[0].tmp:dTuple(cast(DExpr[])retVars.map!(v=>v.tmp).array);
					case "Expectation":
						auto arg=doItConsumed(ce.arg);
						auto total=dist.distribution;
						auto expct=dist.distribution*arg;
						foreach(v;dist.freeVars){ // TODO: handle non-convergence
							total=dInt(v,total);
							expct=dInt(v,expct);
						}
						// for obvious reasons, this will never fail:
						dist.assertTrue(dNeqZ(total),"expectation can be computed only in feasible path");
						auto tmp=dist.getTmpVar("__exp");
						dist.distribute(dDelta(expct/total,tmp,ℝ));
						return tmp;
					default: break;
					}
				}
				auto funty=cast(FunTy)ce.e.type;
				assert(!!funty);
				Expression[] resty;
				bool isTuple=true;
				if(auto tplres=funty.cod.isTupleTy) resty=iota(tplres.length).map!(i=>tplres[i]).array;
				else{ resty=[funty.cod]; isTuple=false; }
				auto fun=doIt(ce.e);
				DNVar[] results=iota(0,resty.length).map!(x=>dist.getTmpVar("__r")).array;
				auto summary=Distribution.fromDExpr(fun,1,false,results,isTuple,resty);
				foreach(r;results) dist.freeVars.remove(r), dist.tmpVars.remove(r);
				auto argty=funty.dom;
				assert(isSubtype(ce.arg.type, argty));
				auto r=dist.call(summary,doIt(ce.arg),argty);
				return r;
			}
			if(auto idx=cast(IndexExp)e){
				if(idx.e.type == arrayTy(ℝ)){
					if(auto id=cast(Identifier)idx.e) if(id.name in arrays){
						auto r=indexArray(idx);
						if(r) return r;
						unwind();
					}
				}
				auto de=doIt(idx.e);
				auto di=doIt(idx.a);
				if(!opt.noBoundsCheck) dist.assertTrue(dIsℤ(di)*dGeZ(di)*dLt(di,dField(de,"length")),formatError("array access out of bounds",idx.loc));
				return dIndex(de,di);
			}
			if(auto sl=cast(SliceExp)e){
				auto de=doIt(sl.e),dl=doIt(sl.l),dr=doIt(sl.r);
				if(!opt.noBoundsCheck){
					dist.assertTrue(dIsℤ(dl)*dGeZ(dl),formatError("slice lower bound out of bounds",sl.loc));
					dist.assertTrue(dLe(dl,dr),formatError("slice lower bound exceeds upper bound",sl.loc));
					dist.assertTrue(dIsℤ(dr)*dLe(dr,dField(de,"length")),formatError("slice upper bound out of bounds",sl.loc));
				}
				return dSlice(de,dl,dr);
			}
			if(auto le=cast(LiteralExp)e){
				if(le.lit.type==Tok!"0"||le.lit.type==Tok!".0"){
					auto x=le.lit.str.split("e");
					auto n=x[0].split(".");
					if(n.length==1) n~="";
					auto r=dℚ((n[0]~n[1]).ℤ)/(ℤ(10)^^n[1].length);
					if(x.length==2) r=x[1][0]=='-'?r/pow(ℤ(10),-ℤ(x[1])):r*pow(ℤ(10),ℤ(x[1]));
					return r;
				}
			}
			if(auto cmp=cast(CompoundExp)e){
				if(cmp.s.length==1)
					return doIt(cmp.s[0]);
			}else if(auto ite=cast(IteExp)e){
				return transformIte(ite.cond,ite.then,ite.othw);
			}else if(auto tpl=cast(TupleExp)e){
				auto dexprs=tpl.e.map!doIt.array;
				return dTuple(dexprs);
			}else if(auto arr=cast(VectorExp)e){
				auto dexprs=arr.e.map!doIt.array;
				return dArray(dexprs);
			}else if(auto ae=cast(AssertExp)e){
				if(auto c=transformConstr(ae.e)){
					dist.assertTrue(c,text("assertion '",ae.e,"' failed"));
					return dTuple([]);
				}
			}else if(auto tae=cast(TypeAnnotationExp)e){
				return doIt(tae.e);
			}else if(auto le=cast(LetExp)e){
				if(auto r=transformLet(le)) return r;
				unwind();
			}else if(auto vfe=cast(VectorForExp)e){
				auto fd=vfe.fd;
				auto ft=fd?cast(FunTy)typeForDecl(fd):null;
				if(!ft){ err.error("unsupported",vfe.loc); unwind(); }
				DExpr[] args;
				if(auto range=vfe.fe.aggr.isRange){
					auto lexp=doIt(range.left), rexp=doIt(range.right);
					auto sexp=range.step?doIt(range.step):one;
					auto l=isDeterministicInteger(lexp), r=isDeterministicInteger(rexp), s=isDeterministicInteger(sexp);
					if(!l||!r||!s){
						err.error(range.step?"vector comprehension bounds and step should be provably deterministic integers":"vector comprehension bounds should be provably deterministic integers",vfe.fe.aggr.loc);
						unwind();
					}
					assert(l.c.den==1 && r.c.den==1 && s.c.den==1);
					if(s.c.num==0){
						err.error("vector comprehension step should be nonzero",range.step.loc);
						unwind();
					}
					auto iter=forRangeIteration(l.c.num,s.c.num,r.c.num,range.leftExclusive,range.rightExclusive);
					for(ℤ j=iter.start;iter.inRange(j);j+=iter.step) args~=dℚ(j);
				}else if(auto cnt=vfe.fe.aggr.isContainer){
					auto c=doIt(cnt.e);
					Dℚ len=null;
					if(auto tt=cnt.e.type.isTupleTy) len=cast(Dℚ)dℚ(tt.length);
					else len=isDeterministicInteger(dField(c,"length"));
					if(!len){
						err.error("length of vector comprehension aggregate should be provably deterministic",cnt.loc);
						unwind();
					}
					for(ℤ k=0;k<len.c.num;k++) args~=c[dℚ(k)].simplify(one);
				}else assert(0);
				auto summary=be.getSummary(fd,vfe.loc,err);
				if(!summary) unwind();
				DExpr[] values;
				foreach(arg;args){
					Expression argty=ft.dom;
					if(fd.isNested){
						auto ctx=buildContextFor!readLocal(fd,fd.scope_);
						assert(!!ctx);
						arg=dTuple([arg,ctx]);
						argty=tupleTy([argty,contextTy]);
					}
					values~=dist.call(summary,arg,argty);
				}
				return dArray(values);
			}else if(cast(Type)e)
				return dTuple([]); // 'erase' types
			else if(isConstraint(e)){
				if(auto c=transformConstr(e))
					return c;
				unwind();
			}
			err.error("unsupported",e.loc);
			throw new Unwind();
		}
		DExpr doItPending(Exp e){
			auto numPending=pending.values.length;
			auto r=doItImpl(e);
			truncatePending(numPending); // (the values of the subexpressions are consumed)
			pending.values~=r;
			flushForgets();
			return r;
		}
		doIt=&doItPending;
		try return consumed?doItConsumed(e):doIt(e);
		catch(Unwind){ return null; }
	}

	DExpr transformLet(LetExp le){
		if(auto e=le.isForward(true)){ // e.g., `let{ t := e; forget(x); } in t`, as inserted after last uses
			auto r=transformExp(e);
			if(!r) return null;
			auto numDeferred=deferredForgets.length;
			foreach(fe;forwardedForgets(le)) deferForgets(fe);
			if(deferredForgets[numDeferred..$].any!(name=>r.hasFreeVar(dVar(name)))){
				// store the value in a temporary, so that the forgotten variables can be marginalized now
				auto tmp=dist.getTmpVar("__let");
				dist.initialize(tmp,r,le.type);
				r=tmp;
				assert(pending.values.length&&pending.values[$-1] !is null);
				pending.values[$-1]=tmp;
				deferredForgets~=tmp.name; // (marginalized once its value is consumed)
			}
			flushForgets();
			return r;
		}
		// the statements are analyzed as part of the enclosing statement
		auto tmpVarsSave=dist.tmpVars.dup;
		dist.tmpVars.clear();
		scope(exit){
			foreach(v;tmpVarsSave)
				if(v in dist.freeVars)
					dist.tmpVars.insert(v);
		}
		auto freeVarsBefore=dist.freeVars.dup;
		if(le.s.blscope_) deferForgets(le.s.blscope_.forgottenVarsOnEntry~le.s.blscope_.forgottenVars);
		Distribution retDist=null;
		foreach(s;le.s.s){
			if(auto fe=cast(ForgetExp)s){
				deferForgets(fe);
				flushForgets();
			}else analyzeStatement(s,retDist,null);
		}
		if(retDist){
			err.error("cannot return from within `let` expression",le.loc);
			return null;
		}
		auto r=transformExp(le.e);
		if(!r) return null;
		// marginalize the variables that are local to the `let` expression
		DNVar result=null;
		if(auto v=cast(DNVar)r) if(v in dist.freeVars&&v !in freeVarsBefore) result=v;
		if(!result){
			result=dist.getVar("__let");
			dist.initialize(result,r,le.type);
		}
		foreach(v;dist.freeVars.dup){
			if(v is result||v in freeVarsBefore) continue;
			deterministic.remove(v);
			dist.marginalize(v);
		}
		tmpVarsSave.insert(result);
		pending.values[$-1]=result;
		flushForgets();
		return result;
	}

	static bool isConstraint(Expression e){ // (expressions that are handled by `transformConstr`)
		return cast(ALogicExp)e||cast(AndExp)e||cast(OrExp)e||cast(XorExp)e||cast(IteExp)e
			||cast(LtExp)e||cast(LeExp)e||cast(GtExp)e||cast(GeExp)e||cast(EqExp)e||cast(NeqExp)e;
	}
	DExpr transformConstr(Exp e,bool consumed=false){ // (see `transformExp`)
		class Unwind: Exception{ this(){ super(""); } }
		void unwind(){ throw new Unwind(); }
		DExpr doItImpl(Exp e){
			enum common=q{
				auto e1=transformExp(b.e1),e2=transformExp(b.e2);
				if(!e1||!e2) unwind();
			};
			CompoundExp block(Expression e,BlockScope blscope_){
				auto r=new CompoundExp([e]);
				r.blscope_=blscope_;
				return r;
			}
			if(auto b=cast(AndThenExp)e){
				auto zeroExp=new LiteralExp(Token(Tok!"0","0"));
				zeroExp.type = ℝ;
				return transformIte(b.e1,block(b.e2,b.blscope_),block(zeroExp,b.forgetScope),true);
			}else if(auto b=cast(OrElseExp)e){
				auto oneExp=new LiteralExp(Token(Tok!"0","1"));
				oneExp.type = ℝ;
				return transformIte(b.e1,block(oneExp,b.forgetScope),block(b.e2,b.blscope_),true);
			}else if(auto b=cast(AndExp)e){ // (eager)
				mixin(common);
				return dNeqZ(e1)*dNeqZ(e2);
			}else if(auto b=cast(OrExp)e){ // (eager)
				mixin(common);
				return dNeqZ(dNeqZ(e1)+dNeqZ(e2));
			}else if(auto b=cast(XorExp)e){ // (eager)
				mixin(common);
				return dNeq(dNeqZ(e1),dNeqZ(e2));
			}else if(auto i=cast(IteExp)e){
				return transformIte(i.cond,i.then,i.othw,true);
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
			}else{
				auto cond=transformExp(e,consumed);
				if(!cond) unwind();
				return dNeqZ(cond);
			}
			err.error("unsupported",e.loc);
			throw new Unwind();
		}
		DExpr doIt(Exp e){
			auto numPending=pending.values.length;
			auto r=doItImpl(e);
			truncatePending(numPending);
			pending.values~=r;
			flushForgets();
			return r;
		}
		try return doIt(e);
		catch(Unwind){ return null; }
	}

	void trackDeterministic(DVar var,DExpr rhs,Expression ty){
		if(ty != ℝ) return;
		if(rhs){
			if(auto nrhs=isObviouslyDeterministic(rhs)){
				deterministic[var]=nrhs;
				return;
			}
		}
		deterministic.remove(var);
	}

	DExpr isObviouslyDeterministic(DExpr e){
		foreach(v;e.freeVars.setx){
			if(v in deterministic){
				e=e.substitute(v,deterministic[v]);
			}else return null;
		}
		return e.simplify(one);
	}

	DExpr isDeterministic(DExpr e,Expression ty){ // TODO: track deterministic values for more complex datatypes than 'ℝ"?
		if(ty != ℝ) return null;
		if(auto r=isObviouslyDeterministic(e))
			return r;
		// TODO: this is a glorious hack:
		auto ndist=dist.dup();
		auto tmp=ndist.getVar("tmp");
		ndist.initialize(tmp,e,ℝ);
		foreach(v;dist.freeVars) ndist.marginalize(v);
		DExpr deltaFactor=null;
		foreach(f;ndist.distribution.factors){
			if(auto d=cast(DDeltaOld)f)
				if(d.hasFreeVar(tmp))
					deltaFactor=d;
			if(auto d=cast(DDelta)f){
				if(d.var.hasFreeVar(tmp))
					deltaFactor=d;
				break;
			}
		}
		if(!deltaFactor) return null;
		auto r=dIntSmp(tmp,tmp*deltaFactor,one);
		if(r.hasAny!DInt) return null;
		return r;
	}

	Dℚ isDeterministicInteger(DExpr e){
		if(auto r=isDeterministic(e,ℝ))
			if(auto num=r.isInteger()) return num;
		return null;
	}

	DExpr indexArray(IndexExp idx){
		auto id=cast(Identifier)idx.e;
		if(!id){
			err.error("indexed expression should be identifier",idx.e.loc);
			return null;
		}
		if(id.name !in arrays){
			err.error("undefined variable '"~id.name~"'",id.loc);
			return null;
		}
		auto arr=arrays[id.name];
		if(auto index=transformExp(idx.a)){
			auto cidx=isDeterministicInteger(index);
			if(!cidx){
				err.error("index expression should be provably deterministic integer",idx.a.loc);
				return null;
			}
			if(!(0<=cidx.c&&cidx.c<arr.length)){
				err.error(text("index ",cidx.c," is outside array bounds [0..",arr.length,")"),idx.loc);
				return null;
			}
			assert(cidx.c.den==1);
			return arr[cast(size_t)cidx.c.num.toLong()];
		}else return null;
	}

	void evaluateArrayCall(Identifier id,CallExp call){
		if(!isSubtype(call.arg.type,ℝ)){
			err.error("expected one real argument to array",call.loc);
			return;
		}
		auto ae=transformExp(call.arg);
		if(!ae) return;
		auto num=isDeterministicInteger(ae);
		assert(num.c.den==1);
		if(!num){
			err.error("array length should be provably deterministic integer",call.loc);
			return;
		}
		if(num.c.num<0){
			err.error("array length should be non-negative",call.loc);
			return;
		}
		if(num.c.num>int.max){
			err.error("array length too high",call.loc);
			return;
		}
		if(id.name in arrays){
			err.error("array already exists",id.loc);
			return;
		}
		foreach(k;0..num.c.num.toLong()){
			auto var=dist.getVar(id.name);
			dist.initialize(var,zero,ℝ);
			arrays[id.name]~=var;
		}
	}

	void evaluateReadCSVCall(Identifier id,CallExp call){
		if(call.arg.type!=stringTy){
			err.error("expected one string argument (filename) to 'readCSV'",call.loc);
			return;
		}
		auto lit=cast(LiteralExp)call.arg;
		if(!lit||lit.lit.type != Tok!"``"){
			err.error("argument to 'readCSV' must be string constant",call.arg.loc);
			return;
		}
		auto filename=lit.lit.str;
		import std.path, std.file;
		auto path=buildPath(dirName(be.sourceFile),filename);
		File f;
		try{
			f=File(path,"r");
		}catch(Exception){
			err.error(text(`could not open file "`,path,`"`),call.loc);
			return;
		}
		try{
			static DExpr parseNum(string s){
				auto n=s.split(".");
				if(n.length==1) n~="";
				import std.exception;
				enforce(n.length==2);
				if(n[1].length) return dFloat((n[0]~"."~n[1]).to!real);
				return dℚ((n[0]~n[1]).ℤ)/(ℤ(10)^^n[1].length);
			}
			auto arr=f.readln().strip().split(",").map!strip.map!parseNum.array;
			//enforce(f.eof);
			arrays[id.name]=arr;
			// dw("len: ",arr.length);
		}catch(Exception e){
			err.error(text("not a comma-separated list of numbers: `",path,"`"),call.loc);
			return;
		}
	}

	void assignTo(DExpr lhs,DExpr rhs,Expression ty,Location loc){
		void assignVar(DNVar var,DExpr rhs,Expression ty){
			cancelDeferredForgets(var.name);
			if(var.name !in arrays){
				dist.assign(var,rhs,ty);
				trackDeterministic(var,rhs,ty);
			}else err.error("reassigning array unsupported",loc);
		}
		if(auto var=cast(DNVar)lhs){
			assignVar(var,rhs,ty);
		}else if(auto idx=cast(DIndex)lhs){
			if(auto id=cast(DNVar)idx.e){
				if(id.name in arrays){
					err.error("unsupported",loc);
					return;
				}
			}
			assignTo(idx.e,dIUpdate(idx.e,idx.i,rhs),unit,loc); // TODO: 'unit' ok?
		}else if(auto fe=cast(DField)lhs){
			assignTo(fe.e,dRUpdate(fe.e,fe.f,rhs),unit,loc); // TODO: 'unit' ok?
		}else{
			err.error("unsupported assignment",loc);
		}
	}

	void assignTo(Expression lhs,DExpr rhs,Expression ty,Location loc){
		if(!rhs) return;
		/+if(!cast(Identifier)lhs&&!cast(FieldExp)lhs){ // TODO
			auto tmp=dist.getTmpVar("tmp");
			dist.initialize(tmp,rhs,ty);
			rhs=tmp;
		}+/
		void assignToImpl(Expression lhs,DExpr rhs,Expression ty){
			void assignVar(Identifier id,DExpr rhs,Expression ty){
				cancelDeferredForgets(id.name);
				if(id.name !in arrays){
					auto v=dVar(id.name);
					dist.assign(v,rhs,ty);
					trackDeterministic(v,rhs,ty);
				}else err.error("reassigning array unsupported",lhs.loc);
			}
			if(auto id=cast(Identifier)lhs){
				assignVar(id,rhs,ty);
			}else if(auto idx=cast(IndexExp)lhs){
				if(auto id=cast(Identifier)idx.e){
					if(id.name in arrays){
						if(auto cidx=indexArray(idx)){
							if(auto v=cast(DNVar)cidx){
								dist.assign(v,rhs?rhs:zero,ty);
								trackDeterministic(v,rhs,ty);
							}else{
								err.error(text("array is not writeable"),lhs.loc);
							}
						}
						return;
					}
				}
				if(idx.e.type.isTupleTy||cast(ArrayTy)idx.e.type||cast(VectorTy)idx.e.type){
					auto old=transformExp(idx.e);
					auto index=transformExp(idx.a);
					if(old&&index&&rhs){
						if(!opt.noBoundsCheck) dist.assertTrue(dGeZ(index)*dLt(index,dField(old,"length")),"array access out of bounds"); // TODO: check that index is an integer.
						assignToImpl(idx.e,dIUpdate(old,index,rhs),idx.e.type);
					}
				}else{
					err.error(text("unsupported type '",idx.e.type,"' for index expression"),lhs.loc);
				}
			}else if(auto fe=cast(FieldExp)lhs){
				if(!(fe.e.type.isTupleTy||cast(ArrayTy)fe.e.type||cast(VectorTy)fe.e.type)){
					auto old=transformExp(fe.e);
					if(old) assignToImpl(fe.e,dRUpdate(old,fe.f.name,rhs),fe.e.type);
				}
			}else if(auto tpl=cast(TupleExp)lhs){
				if(!cast(DVar)rhs){
					auto tmp=dist.getTmpVar("__tpl");
					dist.initialize(tmp,rhs,ty);
					assignTo(lhs,tmp,ty,loc);
				}else{
					auto tt=ty.isTupleTy;
					assert(!!tt);
					assert(tpl.e.length==tt.length);
					foreach(k,exp;tpl.e) assignToImpl(exp,rhs[k.dℚ],tt[k]);
				}
			}else if(auto tae=cast(TypeAnnotationExp)lhs){
				assignToImpl(tae.e,rhs,ty);
			}else{
			LbadAssgnmLhs:
				err.error("invalid left hand side for assignment",lhs.loc);
			}
		}
		assignToImpl(lhs,rhs,ty);
	}

	private void analyzeStatement(Expression e,ref Distribution retDist,FunctionDef functionDef,bool deferForgetStatements=false)in{assert(!!e);}do{
		if(opt.trace) writeln("statement: ",e);
		scope(success) if(!deferForgetStatements) flushForgets();
		auto numPending=pending.values.length;
		scope(exit) truncatePending(numPending); // (the values computed by the statement are consumed)
		/+writeln("before: ",dist);
		 scope(success) writeln("after: ",dist);+/
		// TODO: visitor?
		void analyzeIte(Expression iteCond,CompoundExp iteThen,CompoundExp iteOthw){
			if(auto c=transformConstr(iteCond,true)){
				auto dthen=dist.dupNoErr();
				dthen.distribution=dthen.distribution*dNeqZ(c);
				auto dothw=dist.dupNoErr();
				dothw.distribution=dothw.distribution*dEqZ(c);
				truncatePending(numPending); // (the condition is consumed, the pending forgets are performed in the branches)
				auto forgets=deferredForgets;
				deferredForgets=[];
				auto athen=nested(dthen);
				athen.deferredForgets=forgets.dup;
				athen.flushForgets();
				dthen=athen.analyze(iteThen,retDist,functionDef);
				auto aothw=nested(dothw);
				aothw.deferredForgets=forgets.dup;
				aothw.flushForgets();
				if(iteOthw) dothw=aothw.analyze(iteOthw,retDist,functionDef);
				dist=dthen.join(dist,dothw);
				mergeDeterministic(athen,aothw);
				deferredForgets~=athen.deferredForgets~aothw.deferredForgets;
			}
		}
		if(auto de=cast(ODefExp)e){
			// TODO: no real need to repeat checks done by semantic
			scope(exit) dist.marginalizeTemporaries();
			void defineVar(Identifier id,DExpr rhs,Expression ty){
				cancelDeferredForgets(id.name);
				DVar var=null;
				if(id.name !in arrays) var=dist.declareVar(id.name);
				if(var){
					dist.distribute(dDelta(rhs?rhs:zero,var,rhs?ty:ℝ)); // TODO: zero is not a good default value for types other than ℝ.
					trackDeterministic(var,rhs,ty);
				}else err.error("variable already exists",id.loc);
			}
			if(auto id=cast(Identifier)de.e1){
				bool isSpecial=false;
				if(auto call=cast(CallExp)de.e2){
					if(auto cid=cast(Identifier)call.e){
						switch(cid.name){
							case "array":
								if(isSubtype(call.arg.type,ℝ)){
									isSpecial=true;
									evaluateArrayCall(id,call);
								}
								break;
							case "readCSV":
								isSpecial=true;
								evaluateReadCSVCall(id,call);
								break;
							default: break;
						}
					}
				}
				if(isSpecial) return;
			}
			auto rhs=transformExp(de.e2,true);
			if(!rhs){
				if(auto id=cast(Identifier)de.e1)
					defineVar(id,null,de.e2.type);
				return;
			}
			// variables that are defined again have been moved on the right-hand side
			// (the previous versions are marginalized after the definition)
			void renameMoved(Expression lhs){
				if(auto tae=cast(TypeAnnotationExp)lhs) return renameMoved(tae.e);
				if(auto id=cast(Identifier)lhs){
					auto var=dVar(id.name);
					if(var !in dist.freeVars||var in dist.tmpVars) return;
					auto nvar=dist.getTmpVar(id.name);
					dist.distribution=dist.distribution.substitute(var,nvar);
					rhs=rhs.substitute(var,nvar);
					dist.freeVars.remove(var);
					deterministic.remove(var);
				}else if(auto tpl=cast(TupleExp)lhs){
					foreach(x;tpl.e) renameMoved(x);
				}else if(auto vec=cast(VectorExp)lhs){
					foreach(x;vec.e) renameMoved(x);
				}else if(auto ce=cast(CatExp)lhs){
					renameMoved(ce.e1);
					renameMoved(ce.e2);
				}
			}
			renameMoved(de.e1);
			{
				bool defineLhs(Expression lhs,DExpr rhs,Expression ty){
					if(auto id=cast(Identifier)lhs){
						defineVar(id,rhs,ty);
						return true;
					}
					if(auto tae=cast(TypeAnnotationExp)lhs)
						return defineLhs(tae.e,rhs,tae.type?tae.type:ty);
					if(cast(WildcardExp)lhs) return true; // (value is discarded)
					Expression[] elements;
					if(auto tpl=cast(TupleExp)lhs) elements=tpl.e;
					else if(auto vec=cast(VectorExp)lhs) elements=vec.e;
					else if(auto ce=cast(CatExp)lhs){ // split
						DExpr length(Expression e,Expression lhsPart){
							if(auto l=knownLength(lhsPart,false))
								return transformExp(l);
							return null;
						}
						auto l1=length(ce.e1,ce.e1), l2=length(ce.e2,ce.e2);
						if(!l1&&!l2) return false;
						DExpr len=dField(rhs,"length");
						if(auto tt=ty.isTupleTy) len=dℚ(tt.length);
						auto mid=l1?l1:len-l2;
						if(!opt.noBoundsCheck){
							if(l1&&l2) dist.assertTrue(dEq(l1+l2,len),formatError("incompatible lengths for split",ce.loc));
							else dist.assertTrue(dLe(mid,len)*dGeZ(mid),formatError("not enough elements to split",ce.loc));
						}
						return defineLhs(ce.e1,dSlice(rhs,zero,mid),ce.e1.type)
							&& defineLhs(ce.e2,dSlice(rhs,mid,len),ce.e2.type);
					}else return false;
					if(auto tt=ty.isTupleTy){
						if(tt.length!=elements.length) return false;
						foreach(k,exp;elements)
							if(!defineLhs(exp,rhs[k.dℚ],tt[k]))
								return false;
						return true;
					}
					if(auto at=cast(ArrayTy)ty){
						if(!opt.noBoundsCheck)
							dist.assertTrue(dEq(dField(rhs,"length"),dℚ(elements.length)),formatError("wrong number of elements to unpack",lhs.loc));
						foreach(k,exp;elements)
							if(!defineLhs(exp,rhs[k.dℚ],at.next))
								return false;
						return true;
					}
					return false;
				}
				if(!defineLhs(de.e1,rhs,de.e2.type))
					err.error("unsupported left hand side for definition",de.e1.loc);
			}
		}else if(auto ae=cast(AssignExp)e){
			assignTo(ae.e1,transformExp(ae.e2,true),ae.e2.type,ae.loc);
			dist.marginalizeTemporaries();
		}else if(isOpAssignExp(e)){
			DExpr perform(DExpr a,DExpr b){
				if(cast(OrAssignExp)e) return dNeqZ(dNeqZ(a)+dNeqZ(b));
				if(cast(AndAssignExp)e) return dNeqZ(a)*dNeqZ(b);
				if(cast(XorAssignExp)e) return dNeq(dNeqZ(a),dNeqZ(b));
				if(cast(AddAssignExp)e) return a+b;
				if(cast(SubAssignExp)e) return a-b;
				if(cast(NSubAssignExp)e){
					dist.assertTrue(dGe(a,b),"result of sub is negative");
					return a-b;
				}
				if(cast(MulAssignExp)e) return a*b;
				if(cast(DivAssignExp)e||cast(IDivAssignExp)e){
					dist.assertTrue(dNeqZ(b),"division by zero");
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
			Expression setℝ(Expression e){
				e.type = ℝ;
				return e;
			}
			if(cast(AndThenAssignExp)be){
				auto zeroExp=setℝ(new LiteralExp(Token(Tok!"0","0")));
				analyzeIte(be.e1, new CompoundExp([new AssignExp(be.e1,setℝ(new NeqExp(be.e2,zeroExp)))]), new CompoundExp([new AssignExp(be.e1,setℝ(new NeqExp(be.e1,zeroExp)))]));
			}else if(cast(OrElseAssignExp)be){
				auto zeroExp=setℝ(new LiteralExp(Token(Tok!"0","0")));
				auto oneExp=setℝ(new LiteralExp(Token(Tok!"0","1")));
				analyzeIte(be.e1, new CompoundExp([new AssignExp(be.e1,oneExp)]), new CompoundExp([new AssignExp(be.e1,setℝ(new NeqExp(be.e2,zeroExp)))]));
			}else{
				auto lhs=transformExp(be.e1);
				auto rhs=transformExp(be.e2,true);
				assignTo(lhs,perform(lhs,rhs),be.e2.type,be.loc);
			}
			dist.marginalizeTemporaries();
		}else if(cast(CallExp)e||cast(TypeAnnotationExp)e){
			transformExp(e,true);
			dist.marginalizeTemporaries();
		}else if(auto ce=cast(CompoundExp)e){
			if(!ce.blscope_){ // (e.g., a statement followed by the variables it uses last, these are marginalized together)
				foreach(s;ce.s) analyzeStatement(s,retDist,functionDef,true);
			}else analyze(ce,retDist,functionDef);
		}else if(auto ite=cast(IteExp)e){
			analyzeIte(ite.cond,ite.then,ite.othw);
		}else if(auto re=cast(RepeatExp)e){
			if(auto exp=transformExp(re.num,true)){
				truncatePending(numPending);
				flushForgets();
				if(auto num=isDeterministicInteger(exp)){
					int nerrors=err.nerrors;
					for(ℤ j=0;j<num.c;j++){
						auto anext=nested(dist.dup(),false);
						auto dnext=anext.analyze(re.bdy,retDist,functionDef);
						dnext.marginalizeLocals(dist);
						dist=dnext;
						deterministic=anext.deterministic;
						if(err.nerrors>nerrors) break;
					}
				}else err.error("repeat expression should be provably deterministic integer",re.num.loc);
			}
		}else if(auto fe=cast(ForExp)e){
			auto range=fe.aggr.isRange;
			if(!range){ // (loops over containers are lowered to loops over ranges during semantic analysis)
				err.error("unsupported for loop",fe.loc);
				return;
			}
			auto lexp=transformExp(range.left,true), rexp=transformExp(range.right,true);
			auto sexp=range.step?transformExp(range.step,true):one;
			truncatePending(numPending);
			flushForgets();
			if(lexp&&rexp&&sexp){
				auto l=isDeterministicInteger(lexp), r=isDeterministicInteger(rexp), s=isDeterministicInteger(sexp);
				if(l&&r&&s){
					assert(l.c.den==1 && r.c.den==1 && s.c.den==1);
					if(s.c.num==0){
						err.error("for loop step should be nonzero",range.step.loc);
						return;
					}
					int nerrors=err.nerrors;
					auto iter=forRangeIteration(l.c.num,s.c.num,r.c.num,range.leftExclusive,range.rightExclusive);
					for(ℤ j=iter.start;iter.inRange(j);j+=iter.step){
						auto cdist=dist.dup();
						auto anext=nested(cdist,false);
						auto var=cdist.declareVar(fe.var.name);
						if(var){
							auto rhs=dℚ(j);
							cdist.initialize(var,rhs,ℝ);
							anext.trackDeterministic(var,rhs,ℝ);
						}else{
							err.error("variable already exists",fe.var.loc);
							break;
						}
						auto dnext=anext.analyze(fe.bdy,retDist,functionDef);
						dnext.marginalizeLocals(dist,(v){ anext.deterministic.remove(v); });
						dist=dnext;
						deterministic=anext.deterministic;
						deterministic.remove(var);
						if(err.nerrors>nerrors) break;
					}
				}else{
					auto loc=!l?range.left.loc:!r?range.right.loc:range.step.loc;
					err.error(range.step?"for bounds and step should be provably deterministic integers":"for bounds should be provably deterministic integers",loc);
				}
			}
		}else if(auto re=cast(ReturnExp)e){
			auto odist=dist.dup;
			odist.distribution=odist.error=zero; // code after return is unreachable
			auto forgets=deferredForgets.dup;
			auto exp = transformExp(re.e,true);
			auto tty=re.e.type.isTupleTy;
			DNVar[] orderedVars;
			bool isTuple=!!tty, needIndex=tty&&tty.length!=0;
			void keepOnly(SetX!DNVar keep){
				foreach(w;dist.freeVars.dup){
					if(w in keep) continue;
					dist.marginalize(w);
				}
			}
			if(!exp){ dist=odist; return; }
			if(functionDef.context&&functionDef.contextName.startsWith("this")){
				auto resv=dist.getVar("__r"),ctxv=dVar(functionDef.contextName);
				dist.initialize(resv,exp,re.e.type);
				orderedVars=[resv,ctxv];
				keepOnly(setx(orderedVars));
				isTuple=true;
			}else{
				foreach(n;functionDef.retNames){
					auto var=dVar(n);
					assert(!dist.hasArg(var));
					if(var in dist.freeVars){
						auto nvar=dist.getVar(var.name);
						dist.distribution=dist.distribution.substitute(var,nvar);
						exp=exp.substitute(var,nvar);
						dist.freeVars.remove(var);
						dist.freeVars.insert(nvar);
					}
				}
				orderedVars=functionDef.retNames.map!(n=>dist.declareVar(n)).array;
				foreach(i,var;orderedVars){
					assert(!!var);
					dist.initialize(var,needIndex?dIndex(exp,i.dℚ):exp,needIndex?tty[i]:re.e.type);
				}
				keepOnly(setx(orderedVars));
			}
			assert(isTuple||orderedVars.length==1);
			dist.orderFreeVars(orderedVars,isTuple);
			if(!retDist) retDist=dist;
			else retDist=dist.orderedJoin(retDist);
			dist=odist;
			deferredForgets=forgets; // (variables forgotten within the returned expression stay in the unreachable distribution)
			if(re.expected.length)
				expected.parse(re.expected,err,re.loc);
		}else if(auto ae=cast(AssertExp)e){
			if(auto c=transformConstr(ae.e,true))
				dist.assertTrue(c,text("assertion '",ae.e,"' failed"));
		}else if(auto oe=cast(ObserveExp)e){
			if(auto c=transformConstr(oe.e,true))
				dist.observe(c);
		}else if(auto co=cast(CObserveExp)e){ // TODO: fix
			if(auto var=transformExp(co.var)){
				if(auto ex=transformExp(co.val,true)){
					auto tmp=dist.getTmpVar("__cobs");
					dist.distribution=dDisintegrate(dist.distribution*dDelta(var,tmp)*dDelta(ex,tmp),dLebesgue(tmp));
				}
			}
		}else if(auto fe=cast(ForgetExp)e){
			deferForgets(fe); // (marginalized at the end of the statement)
		}else if(auto ce=cast(CommaExp)e){
			analyzeStatement(ce.e1,retDist,functionDef);
			analyzeStatement(ce.e2,retDist,functionDef);
		}else if(auto decl=cast(Declaration)e){
			if(isClosureDecl(decl)) defineClosure(decl);
		}else if(!cast(ErrorExp)e) err.error("unsupported ",e.loc);
	}

	Distribution analyze(CompoundExp ce,ref Distribution retDist,FunctionDef functionDef)in{assert(!!ce);}do{
		if(ce.blscope_) forgetDecls(ce.blscope_.forgottenVarsOnEntry);
		foreach(e;ce.s){
			analyzeStatement(e,retDist,functionDef);
		}
		if(ce.blscope_) forgetDecls(ce.blscope_.forgottenVars);
		return dist;
	}
	void applyRetDist(FunctionDef fd,Distribution retDist){
		if(retDist){
			dist.simplify();
			if(dist.distribution == zero){
				retDist.error=retDist.error+dist.error;
				dist=retDist;
			}else err.error("not all paths return",fd.loc); // TODO: check during semantic
		}
		if(!dist.freeVarsOrdered) dist.orderFreeVars(dist.freeVars.array,dist.freeVars.length!=1);
	}
}
