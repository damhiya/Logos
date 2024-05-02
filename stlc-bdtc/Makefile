all: stlc_hoas.lp stlc_subsys.lp

stlc_hoas.lpo: stlc_hoas.sig stlc_hoas.mod
	tjcc stlc_hoas

stlc_hoas.lp: stlc_hoas.lpo
	tjlink stlc_hoas

stlc_subsys.lpo: stlc_subsys.sig stlc_subsys.mod
	tjcc stlc_subsys

stlc_subsys.lp: stlc_subsys.lpo
	tjlink stlc_subsys

run_hoas: stlc_hoas.lp
	rlwrap tjsim stlc_hoas

run_subsys: stlc_subsys.lp
	rlwrap tjsim stlc_subsys

clean:
	rm -rf *.lp *.lpo
