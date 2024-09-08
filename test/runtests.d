// (this is a little convoluted, as it is adapted from code that had more capabilities)
import std.stdio, std.file;
import std.process, std.string, std.array;
import std.algorithm, std.conv, std.range;
import std.datetime.stopwatch;
import std.typecons : Flag, Yes, No;

auto shell(string cmd){
	return executeShell(cmd).output;
}

enum TODOColor=CYAN;
enum passColor=GREEN;
enum failColor=RED;

bool fileStartsWithFlag(string source, string flag){
	auto code=readText(source);
	code=code.strip();
	if(code.startsWith("// -*-")||code.startsWith("//-*-")){
		while(code.length&&code.front!='\n') code.popFront();
		if(code.length) code.popFront();
	}
	immutable f1="//"~flag, f2="// "~flag;
	return code.startsWith(f1)||code.startsWith(f2);
}

alias to=std.conv.to;

auto to(string unit,T)(Duration d)if(unit=="seconds"||unit=="msecs"){
	static if(unit=="seconds") T factor=1e7;
	else static if(unit=="msecs") T factor=1e4;
	else static assert(0);
	return d.total!"hnsecs"/factor;
}

bool dashDashBad=false;
bool dashDashTodo=false;
int parseFlags(string[] flags){
	foreach(flag;flags){
		if(flag=="--bad") dashDashBad=true;
		else if(flag=="--todo") dashDashTodo=true;
		else{
			stderr.writeln("unrecognized flag: ",flag);
			return 1;
		}
	}
	return 0;
}

int main(string[] args){
	import std.algorithm:sort;
	args.sort!((a,b)=>a.startsWith("--")>b.startsWith("--"),SwapStrategy.stable);
	auto flags=args.until!(a=>!a.startsWith("--")).array;
	args=args[flags.length..$];
	bool writeLines=args.length!=1;
	if(auto r=parseFlags(flags)) return r;
	auto sources=args.length==1?shell("find . -name '*.psi' -type f").splitLines:args[1..$];
	Summary total;
	int skipped=0,passed=0;
	bool colorize=isATTy(stdout);
	Duration totalTime;
	foreach(source;sources){
		if(source.startsWith("./")) source=source[2..$];
		if(source.fileStartsWithFlag("skip")){
			if(!dashDashBad&&!dashDashTodo){
				if(colorize) writeln(TODOColor,BOLD,"skipped",RESET,"         ",source);
				else writeln("skipping ",source);
			}
			skipped++;
			continue;
		}else{
			if(colorize) write(CLEAR_LINE,BOLD,"running",RESET,"         ",source);
			else if(!dashDashBad&&!dashDashTodo) write("running"," ",source);
		}
		stdout.flush();
		auto results=source.getResults;
		auto summary=results.summarize;
		total+=summary;
		if(colorize) write("\r");
		else write(": ");
		if(summary.isInteresting){
			int regressions=summary.unexpectedErrors;
			if(summary.unexpectedErrors){
				if(colorize) write(failColor,BOLD,"failed ",RESET);
				else if(!dashDashBad&&!dashDashTodo) std.stdio.write("failed");
				else std.stdio.write("running ",source,": failed");
			}else if (summary.missingErrors) {
				if(colorize) write(failColor,BOLD,"invalid",RESET);
				else if(!dashDashBad&&!dashDashTodo) std.stdio.write("invalid",);
				else std.stdio.write("running ",source,": invalid");
			}else{
				if(summary.todos||!summary.obsoleteTodos){
					if(colorize) write(TODOColor,BOLD," TODO  ",RESET);
					else if(!dashDashTodo) write("TODO");
					else std.stdio.write("running ",source,": TODO");
				}else{
					if(colorize) write(passColor,"fixed  ",RESET);
					else if(!dashDashTodo) write("fixed");
					else std.stdio.write("running ",source,": fixed");
				}
			}
			//write(summary);
		}else passed++;
		if((!dashDashBad||summary.isBad)&&(!dashDashTodo||summary.isInteresting)){
			if(!summary.isInteresting){
				if(colorize) write(passColor,BOLD,"passed ",RESET);
				else std.stdio.write("passed");
			}
			if(colorize) writef(" % 5.0fms",results[0].time.to!("msecs",double));
			else writef(" in %.0fms",results[0].time.to!("msecs",double));
			if(colorize) writeln(" ",source,CLEAR_LINE);
			else writeln();
		}else if(colorize) std.stdio.write("\r",CLEAR_LINE);
		totalTime+=results[0].time;
	}
	writeln();
	if(colorize) writeln(BOLD,"TOTAL:",RESET," ",sources.length);
	else writeln("TOTAL: ",sources.length);
	if(colorize) writeln(passColor,BOLD,"passed:",RESET," ",passed);
	else writeln("passed: ",passed);
	if(colorize) writeln(failColor,"skipped:",RESET," ",skipped);
	else writeln("skipped: ",skipped);
	writeln(total.toString(colorize,true));
	if(colorize) writeln("total time: %.1fs".format(totalTime.to!("seconds",double)));
	return 0;
}

struct Summary{
	int unexpectedErrors;
	int expectedErrors;
	int missingErrors;
	int todos;
	int obsoleteTodos;
	int unspecified;

	auto combine(Summary rhs){
		Summary r;
		foreach(i,t;this.tupleof){
			r.tupleof[i]=t+rhs.tupleof[i];
		}
		return r;
	}
	string toString(bool colorize=false,bool showAll=false){
		int regressions=unexpectedErrors+missingErrors;
		return ((regressions||showAll?(colorize?failColor~BOLD:"")~"regressions:"~(colorize?RESET:"")~" "
				 ~regressions.to!string~"\n":"")~
				(todos||showAll?(colorize?TODOColor~BOLD:"")~"TODOs:"~(colorize?RESET:"")~" "
				 ~todos.to!string~"\n":"")~
				(obsoleteTodos||showAll?(colorize?passColor:"")~"fixed:"~(colorize?RESET:"")~" "
				 ~obsoleteTodos.to!string~"\n":"")~
				(unspecified||showAll?(colorize?failColor:"")~"unspecified:"~(colorize?RESET:"")~" "
				 ~unspecified.to!string~"\n":""))[0..$-1];
	}
	bool isInteresting(){
		foreach(i,x;this.tupleof) if(i!=1&&x) return true;
		return false;
	}
	bool isBad(){
		return unexpectedErrors||missingErrors;
	}
	void opOpAssign(string op:"+")(Summary rhs){
		foreach(i,ref x;this.tupleof) x+=rhs.tupleof[i];
	}
}

struct Info{
	int line;
	bool error;
	bool todo;
}


enum Status{
	expected,
	unexpected,
	missing,
	ok,
}
struct Comparison{
	Status status;
	Info info;
	Duration time;
}

Comparison[] getResults(string source){
	bool compilationError=source.fileStartsWithFlag("compilation error");
	bool foundCompilationError=false;
	auto fin=File(source,"r");
	string args;
	do{
		args=fin.readln().strip();
	}while(args==""||args.startsWith("//compilation error")||args.startsWith("// compilation error"));
	if(args.startsWith("// args: "))
		args=args["// args: ".length..$].strip()~" ";
	else args="";
	auto sw = StopWatch(Yes.autoStart);
	auto output = shell("../psi "~args~source~" 2>&1").splitLines;
	sw.stop();
	Comparison[] result;
	foreach(i,l;output){
		switch(l.strip){
		default: break;
		case "FIXED": result~=Comparison(Status.expected,Info(cast(int)i+1,true,true),sw.peek()); break;
		case "PASS": result~=Comparison(Status.ok,Info(cast(int)i+1,false,false),sw.peek()); break;
		case "TODO": result~=Comparison(Status.expected,Info(cast(int)i+1,false,true),sw.peek()); break;
		case "FAIL": result~=Comparison(Status.unexpected,Info(cast(int)i+1,true,false),sw.peek()); break;
		}
		auto isCompilationError=l.canFind("error: ");
		if(l.startsWith("core.exception.AssertError")||l.startsWith("Segmentation fault")||!compilationError&&!foundCompilationError&&isCompilationError)
			result~=Comparison(Status.unexpected,Info(cast(int)i+1,true,false),sw.peek());
		foundCompilationError|=isCompilationError;
	}
	if(compilationError){
		if(!foundCompilationError)
			result~=Comparison(Status.unexpected,Info(0,true,false),sw.peek());
		else
			result~=Comparison(Status.ok,Info(0,false,false),sw.peek());
	}else if(!result.length)
		result~=Comparison(Status.missing,Info(0,true,false),sw.peek());
	return result;
}

auto summarize(Comparison[] comp){
	Summary result;
	if(!comp.length) result.unspecified++;
	foreach(c;comp){
		final switch(c.status) with(Status){
			case expected:
				if(c.info.error){
					if(c.info.todo){
						result.obsoleteTodos++;
						//writeln("FIX AT LINE ",c.info.line);
					}else result.expectedErrors++;
				}else{
					if(c.info.todo) result.todos++;
					else{
						result.missingErrors++;
						//writeln("REGRESSION AT LINE ",c.info.line);
					}
				}
				break;
			case unexpected:
				assert(c.info.error);
				result.unexpectedErrors++;
				//writeln("REGRESSION AT LINE ",c.info.line);
				break;
			case missing:
				if(c.info.todo){
					if(c.info.error) result.todos++;
					else{
						result.obsoleteTodos++;
						//writeln("FIX AT LINE ",c.info.line);
					}
				}else{
					result.missingErrors++;
					//writeln("REGRESSION AT LINE ",c.info.line);
				}
				break;
			case ok:
				break;
		}
	}
	return result;
}

enum CLEAR_LINE=CSI~"0K";
// (copy of terminal.d)
enum CSI = "\033[";
enum RESET=CSI~"0m";
enum BOLD=CSI~"1m";
enum BLACK =CSI~"30m";
enum RED =CSI~"31m";
enum GREEN=CSI~"32m";
enum YELLOW=CSI~"33m";
enum BLUE=CSI~"34m";
enum MAGENTA=CSI~"35m";
enum CYAN=CSI~"36m";
enum WHITE=CSI~"37m";

version(Posix){
	private extern(C) size_t isatty(size_t desc);
	private extern(C) int fileno(shared(_iobuf)*);
	bool isATTy(ref File f){ // determine whether a given file is connected to a terminal
		if(environment.get("EMACS")) return false;
		if(environment.get("TERM")=="dumb") return false;
		return cast(bool)isatty(fileno(f.getFP()));
	}
	int getTabSize(){
		if(environment.get("EMACS")) return 4;
		if(environment.get("TERM")=="dumb") return 4;
		return 8;
	}
}else{
	bool isATTy(ref File){return false;}
}
