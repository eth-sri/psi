module astopt;
enum Language{
	psi,
	silq,
}
alias psi=Language.psi;
alias silq=Language.silq;
enum language=psi;

enum defaultExtension="psi";

immutable string[] preludePaths=["prelude-nocheck.psi","prelude.psi"];
int preludeIndex(){
	// TODO: use conditional compilation within prelude.psi instead
	import options;
	if(opt.noCheck) return 0;
	return 1;
}
