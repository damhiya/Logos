all: stlc.lp

stlc.lpo: stlc.sig stlc.mod
	tjcc stlc

stlc.lp: stlc.lpo
	tjlink stlc

run: all
	rlwrap tjsim stlc

clean:
	rm -rf *.lp *.lpo
