import std.conv;

import ast.expression, ast.declaration, ast.scope_;
import sym.dexpr;
// TODO: move this to semantic_, as a rewrite
DExpr readVariable(alias readLocal)(VarDecl var,Scope from){
	DExpr r=getContextFor!readLocal(var,from);
	if(r) return dField(r,var.getName);
	return readLocal(var.getName);
}
DExpr getContextFor(alias readLocal)(Declaration meaning,Scope sc)in{assert(meaning&&sc);}do{
	DExpr r=null;
	auto meaningScope=meaning.scope_;
	if(auto fd=cast(FunctionDef)meaning)
		meaningScope=fd.realScope;
	assert(sc&&sc.isNestedIn(meaningScope));
	for(auto csc=sc;csc !is meaningScope;){
		void add(string name){
			if(!r) r=readLocal(name);
			else r=dField(r,name);
			assert(!!cast(NestedScope)csc);
		}
		assert(cast(NestedScope)csc);
		if(!cast(NestedScope)(cast(NestedScope)csc).parent) break;
		if(auto fsc=cast(FunctionScope)csc){
			auto fd=fsc.getFunction();
			if(fd.isConstructor){
				if(meaning is fd.thisVar) break;
				add(fd.thisVar.getName);
			}else add(fd.contextName);
		}else if(cast(AggregateScope)csc) add(csc.getDatDecl().contextName);
		csc=(cast(NestedScope)csc).parent;
	}
	return r;
}
// Nested functions and data types capture the variables they use when they are defined.
// The record of captured values (their closure context) is then stored in a variable of
// the enclosing function (see `closureName`), which is read whenever the function or the
// constructor of the data type is referenced.
// (Anonymous functions capture when they are evaluated, see `captureContext`.)

// the declaration whose definition captures the context of `fd`, if any
Declaration closureDecl(FunctionDef fd){
	import ast.semantic_: isInDataScope;
	if(!fd||!fd.isNested||!fd.name) return null;
	if(fd.isConstructor){
		auto dsc=isInDataScope(fd.scope_);
		if(!dsc) return null;
		auto dat=dsc.decl;
		return isClosureDecl(dat)?dat:null;
	}
	if(isInDataScope(fd.scope_)) return null; // (methods access their context through `this`)
	if(!fd.scope_.getFunction()) return null;
	return fd;
}
// whether the declaration captures its context when it is defined
bool isClosureDecl(Declaration decl){
	decl=sourceDecl(decl);
	if(auto fd=cast(FunctionDef)decl) return closureDecl(fd) is fd;
	if(auto dat=cast(DatDecl)decl){
		import ast.semantic_: isInDataScope;
		return dat.isNested&&dat.scope_.getFunction()&&!isInDataScope(dat.scope_); // (not for members of data types)
	}
	return false;
}
// the name of the variable that stores the closure context of `decl`
string closureName(Declaration decl)in{assert(isClosureDecl(decl));}do{
	return "`closure·"~sourceDecl(decl).getName;
}
private bool isWithin(Scope sc,Declaration decl){
	if(auto fd=cast(FunctionDef)decl) return fd.fscope_&&sc.isNestedIn(fd.fscope_);
	if(auto dat=cast(DatDecl)decl) return dat.dscope_&&sc.isNestedIn(dat.dscope_);
	return false;
}
// read the stored closure context of `decl` from scope `sc`
DExpr readClosure(alias readLocal)(Declaration decl,Scope sc)in{assert(isClosureDecl(decl));}do{
	decl=sourceDecl(decl);
	DExpr r=getContextFor!readLocal(decl,sc);
	auto name=closureName(decl);
	return r?dField(r,name):readLocal(name);
}
// the context of a nested function `fd` that is referenced (e.g., called) in scope `sc`
DExpr buildContextFor(alias readLocal)(FunctionDef fd,Scope sc)in{assert(fd&&sc);}do{ // template, forward references 'doIt'
	if(auto decl=closureDecl(fd))
		if(!isWithin(sc,decl)) return readClosure!readLocal(decl,sc);
	// (recursive references use the context of the current call, anonymous functions capture when they are evaluated)
	if(auto ctx=getContextFor!readLocal(fd,sc)) return ctx;
	return captureContext!readLocal(fd,sc);
}
// build the record of the values captured by a nested function or data type that is defined in scope `sc`
DExpr captureContext(alias readLocal)(Declaration closure,Scope sc)in{assert(closure&&sc);}do{
	DExpr[string] record;
	Declaration[] capturedDecls;
	Scope msc;
	if(auto fd=cast(FunctionDef)closure){
		capturedDecls=fd.capturedDecls;
		msc=fd.realScope;
		if(fd.isConstructor){
			import ast.semantic_: isInDataScope;
			auto dsc=isInDataScope(fd.scope_);
			assert(!!dsc);
			capturedDecls=dsc.decl.capturedDecls;
		}
	}else if(auto dat=cast(DatDecl)closure){
		capturedDecls=dat.capturedDecls;
		msc=dat.scope_;
	}else assert(0);
	for(auto csc=msc;;csc=(cast(NestedScope)csc).parent){
		if(!cast(NestedScope)csc) break;
		foreach(decl;capturedDecls){ // TODO: this is a bit hacky
			if(!decl) continue;
			if(isClosureDecl(decl)){ // (captured functions and data types are captured with their closure contexts)
				auto src=sourceDecl(decl);
				if(src.scope_ is csc)
					record[closureName(src)]=readClosure!readLocal(src,sc);
				continue;
			}
			if(isFunctionDecl(decl)) continue;
			if(decl.scope_ is csc){
				if(auto vd=cast(VarDecl)decl)
					if(auto var=readVariable!readLocal(vd,sc))
						record[vd.getName]=var;
			}
		}
		if(!cast(NestedScope)(cast(NestedScope)csc).parent) break;
		if(auto dsc=cast(DataScope)csc){
			auto name=dsc.decl.contextName;
			record[name]=readLocal(name);
			break;
		}
		if(auto fsc=cast(FunctionScope)csc){
			auto cname=fsc.getFunction().contextName;
			record[cname]=readLocal(cname);
			break;
		}
	}
	return dRecord(record);
}
// the last-use analysis may split declarations into nested scopes (and merge them again afterwards)
// this returns the original declaration
Declaration sourceDecl(Declaration decl){
	if(!decl) return null;
	auto src=decl.canonicalSource;
	if(src.mergedFrom.length>1){
		auto r=sourceDecl(src.mergedFrom[0]);
		foreach(d;src.mergedFrom[1..$])
			if(sourceDecl(d) !is r) return src;
		return r;
	}
	return src;
}
// whether `id` moves the value of a local variable, i.e., the variable is not used afterwards (see ast.lastuse)
// (the backends marginalize moved variables at the end of the enclosing statement)
bool isMove(Identifier id){
	if(!id.meaning||id.constLookup||id.implicitDup||id.byRef) return false;
	auto decl=id.meaning;
	if(!isVariableDecl(decl)||!decl.scope_||decl.isToplevelDeclaration()) return false;
	if(!id.scope_||id.scope_.getFunction() !is decl.scope_.getFunction()) return false; // (captured variables are read from a context)
	return true;
}
FunctionDef isFunctionDecl(Declaration decl){
	return cast(FunctionDef)sourceDecl(decl);
}
bool isVariableDecl(Declaration decl){
	return !!cast(VarDecl)sourceDecl(decl);
}

DExpr lookupMeaning(alias readLocal,alias readFunction)(Identifier id)in{assert(id && id.scope_,text(id," ",id.loc));}do{
	if(!id.meaning||!id.scope_||!id.meaning.scope_)
		return readLocal(id.name);
	if(isFunctionDecl(id.meaning)) return readFunction(id);
	if(auto vd=cast(VarDecl)id.meaning){
		DExpr r=getContextFor!readLocal(id.meaning,id.scope_);
		return r?dField(r,id.name):readLocal(id.name);
	}
	return null;
}
