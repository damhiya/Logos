all: stlc_hoas.lp

stlc_hoas.lpo: stlc_hoas.sig stlc_hoas.mod
	tjcc stlc_hoas

stlc_hoas.lp: stlc_hoas.lpo
	tjlink stlc_hoas

run: all
	rlwrap tjsim stlc_hoas

clean:
	rm -rf *.lp *.lpo
