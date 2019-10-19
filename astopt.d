module astopt;
enum Language{
	psi,
	silq,
}
alias psi=Language.psi;
alias silq=Language.silq;
enum language=psi;

enum defaultExtension="psi";

@property string preludePath(){
	// TODO: use conditional compilation within prelude.psi instead
	import options;
	if(opt.noCheck) return "prelude-nocheck.psi";
	return "prelude.psi";		
}
